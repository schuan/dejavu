//===- TimedExecution.cpp ------------------------------- -----------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/TE.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/BasicBlock.h"

#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#include "llvm/ADT/StringMap.h"

#include <vector>
#include <math.h>
#include <unistd.h>
#include <string.h>

#define MAINFILE "Enclave.c"


using namespace llvm;

struct bb_index
{
	int function;
	int bb;
};

struct training_info
{
	char *function_name = NULL;
	char *bb_name = NULL;
	unsigned long bb_time = -1;
	int bb_num = -1;
	int type1 = 0;
	int type2 = 0;
};

std::vector<struct training_info> info_list;

struct trace_info
{
	char *function_name = NULL;
	char *tail_type2_bb_name = NULL;
	char *context_type1_function_name = NULL;
	char *context_type1_bb_name = NULL;
	int context_type1_bb_num = -1;
	unsigned long bb_time = -1;
};

std::vector<struct trace_info> trace_list;


struct bb_num_s
{
	char *function_name = NULL;
	char *bb_name = NULL;
	unsigned long bb_num = -1;
	int type1 = -1;
	int type2 = -1;
};

std::vector<struct bb_num_s> bb_num_s_list;

//ecall function
char p_entry_function[40], p_entry_file[220], p_reference_function[40];

//page fault metrics
double page_fault_average = 1000000;
double page_fault_stdev = 0;
double tfactor = 0;



namespace {
  struct TimedExecution : public ModulePass {

	//config file full path including name
	char config_full[220];
	int mode;
	double threshold;


	static char ID; // Pass identification, replacement for typeid
	TimedExecution() : ModulePass(ID) {
		initializeTimedExecutionPass(*PassRegistry::getPassRegistry());
	}

	bool runOnModule(Module &M) override;

	void markBBNumType1Type2Info(char *function_name, char *bb_name, int bb_count, int type1, int type2);
	void printMark(Module &M);


	/**
		createStringArg Function
		--a helper function for creating string argument
	*/
	Constant *createStringArg(char *string, Function *F)
	{
		Module *M = F->getParent();
		LLVMContext &llvm_context = M->getContext();
		Constant *v_string = ConstantDataArray::getString(llvm_context, string, true);
		ArrayType *ArrayTy_0 = ArrayType::get(IntegerType::get(llvm_context, 8), (strlen(string) + 1));
		GlobalVariable *gvar_array = new GlobalVariable(*M, ArrayTy_0, true, GlobalValue::PrivateLinkage, 0, ".str");
		gvar_array->setInitializer(v_string);
		std::vector<Constant *> indices;
		ConstantInt *zero = ConstantInt::get(llvm_context, APInt(32, StringRef("0"), 10));
		indices.push_back(zero);
		indices.push_back(zero);
		return ConstantExpr::getGetElementPtr(gvar_array, indices);
	}
  };
} // end anonymous namespace

char TimedExecution::ID = 0;
INITIALIZE_PASS(TimedExecution, "timedexecution", "Timed Execution Pass", false, false)

// createTimedExecutionPass - This is the public interface to this file.
ModulePass *llvm::createTimedExecutionPass() {
	return new TimedExecution();
}

// runOnModule()
//
bool TimedExecution::runOnModule(Module &M) {

	//check the nearest config file recursively up the directory ladder
	char currentd[100], currentf[100], tcon[20];
	char *pch;
	strcpy(tcon, "/tconfig.txt");
	getcwd(currentd, sizeof(currentd));
	//printf("current directory: %s\n", currentd);
	strcpy(currentf, currentd);
	strcat(currentf, tcon);
	//printf("current file: %s\n", currentf);
	FILE *file;
	file = fopen(currentf, "r");
	while(!file && ((pch = strrchr(currentd, '/')) != NULL))
	{
		*pch = '\0';
		strcpy(currentf, currentd);
		strcat(currentf, tcon);
		//printf("current file: %s\n", currentf);
		file = fopen(currentf, "r");
	}

	if(file)
	{
		//printf("current directory: %s\n", currentd);
		char *line = NULL;
		size_t len = 0;
		ssize_t read;
		int count = 0;
		while ((read = getline(&line, &len, file)) != -1)
		{
			//leave out last character '\n'
			line[read-1] = '\0';

			//first line for mode
			if(count == 0)
			{
				//set mode
				mode = atoi(line);
			}
			else if(count == 1)
			{
				//set threshold
				threshold = atof(line);
			}
			else if(count == 2)
			{
				//set p_entry_function
				strcpy(p_entry_function, line);
			}
			else if(count == 3)
			{
				//set page_fault_average
				page_fault_average = atof(line);
			}
			else if(count == 4)
			{
				//set page_fault_stdev
				page_fault_stdev = atof(line);
			}
			else if(count == 5)
			{
				//set main source file
				strcpy(p_entry_file, line);
			}
			else if(count == 6)
			{
				//set reference function
				strcpy(p_reference_function, line);
			}
			else if(count == 7)
			{
				//set tfactor
				tfactor = atof(line);
			}


			//printf("%s", line);
			//printf("king\n");

			count++;
		}

		//printf("mode: %d, threshold: %f, p_entry_function: %s, page_fault_average: %f, page_fault_stdev: %f, p_entry_file: %s, p_reference_function: %s\n",
			 //mode, threshold, p_entry_function, page_fault_average, page_fault_stdev, p_entry_file, p_reference_function);
		fclose(file);

	}
	else
	{
		errs() << "Timed Execution Configration Error: We should have a config file.\n";
		exit(-1);
	}


	GlobalVariable *gv;
	LoadInst *load;
	LLVMContext &llvm_context = M.getContext();
	Type *I64Ty = Type::getInt64Ty(llvm_context);
	Type *I8PtrTy = Type::getInt8PtrTy(llvm_context);
	Type *VoidTy = Type::getVoidTy(llvm_context);
	Type *DoubleTy = Type::getDoubleTy(llvm_context);
	//Value *instru_print_f = M.getOrInsertFunction("te_printf", I64Ty, I8PtrTy, nullptr);
	//Value *instru_print_long_int_f = M.getOrInsertFunction("te_printf_long_int", I64Ty, I64Ty, nullptr);
	////Value *instru_print_f = M.getOrInsertFunction("instrument_function_print", I64Ty, I8PtrTy, nullptr);
	//Value *instru_print_int_f = M.getOrInsertFunction("instrument_function_print_int", I64Ty, I64Ty, nullptr);
	//Value *instru_print_long_int_f = M.getOrInsertFunction("instrument_function_print_long_int", I64Ty, I64Ty, nullptr);
	//Value *instru_print_bbid_and_time_f = M.getOrInsertFunction("instrument_function_print_bbid_and_time", I64Ty, I64Ty, I64Ty, nullptr);
	//Value *instru_print_information_f = M.getOrInsertFunction("instrument_function_print_information", I64Ty, I64Ty, I64Ty, I64Ty, nullptr);
	//Value *instru_gather_info_f = M.getOrInsertFunction("instrument_function_gather_info", I64Ty, I8PtrTy, I8PtrTy, I64Ty, nullptr);
	Value *instru_insert_record_f = M.getOrInsertFunction("instrument_function_insert_record", I64Ty, I8PtrTy, I8PtrTy, I64Ty, nullptr);
	Value *instru_dump_result_f = M.getOrInsertFunction("instrument_function_dump_result", I64Ty, I64Ty, nullptr);
	//Value *instru_insert_trace_record_f = M.getOrInsertFunction("instrument_function_insert_trace_record", I64Ty, I8PtrTy, I8PtrTy, I64Ty, nullptr);
	//Value *instru_dump_trace_result_f = M.getOrInsertFunction("instrument_function_dump_trace_result", I64Ty, I64Ty, nullptr);
	//Value *instru_print_int_to_debug_f = M.getOrInsertFunction("instrument_function_print_int_to_debug", I64Ty, I64Ty, nullptr);
	//Value *instru_print_long_long_int_to_debug_f = M.getOrInsertFunction("instrument_function_print_long_long_int_to_debug", I64Ty, I64Ty, nullptr);
	//Value *instru_print_to_debug_f = M.getOrInsertFunction("instrument_function_print_to_debug", I64Ty, I8PtrTy, nullptr);
	Value *instru_detect1_f = M.getOrInsertFunction("instrument_function_detect1", VoidTy, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I8PtrTy, I8PtrTy, nullptr);
	//Value *instru_detect1_f = M.getOrInsertFunction("instrument_function_detect1", VoidTy, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, DoubleTy, DoubleTy, I8PtrTy, I8PtrTy, nullptr);
	Value *instru_detect2_f = M.getOrInsertFunction("instrument_function_detect2", VoidTy, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I8PtrTy, I8PtrTy, nullptr);
	Value *instru_detect3_f = M.getOrInsertFunction("instrument_function_detect3", VoidTy, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I8PtrTy, I8PtrTy, nullptr);
	Value *instru_detect4_f = M.getOrInsertFunction("instrument_function_detect4", VoidTy, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I8PtrTy, I8PtrTy, nullptr);
	//Value *instru_detect3_f = M.getOrInsertFunction("instrument_function_detect3", VoidTy, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, I64Ty, nullptr);
	Value *instru_dump_detection_result_f = M.getOrInsertFunction("instrument_function_dump_detection_result", I64Ty, I64Ty, nullptr);
	Value *instru_get_time_f = M.getOrInsertFunction("instrument_function_get_time", I64Ty, I64Ty, nullptr);
	//Value *instru_clear_record_f = M.getOrInsertFunction("instrument_function_clear_record", I64Ty, I64Ty, nullptr);
	//Value *instru_init_f = M.getOrInsertFunction("instrument_function_init", VoidTy, I64Ty, nullptr);
	Value *instru_set_loop_false_f = M.getOrInsertFunction("set_infinite_loop_flag_false", VoidTy, I64Ty, nullptr);
	//Value *instru_print_time_f = M.getOrInsertFunction("instrument_function_print_time", VoidTy, I64Ty, nullptr);
	Value *instru_dump_rdtsc_result_f = M.getOrInsertFunction("instrument_function_dump_rdtsc_result", I64Ty, I64Ty, nullptr);

	Constant *initial_value_int_zero = ConstantInt::get(I64Ty, 0);
	Constant *initial_value_int_one = ConstantInt::get(I64Ty, 1);
	Constant *initial_value_int_minus_one = ConstantInt::get(I64Ty, -1);
	Constant *page_fault_average_value_int = ConstantInt::get(I64Ty, page_fault_average);
	Constant *page_fault_stdev_value_int = ConstantInt::get(I64Ty, page_fault_stdev);
	gv = new GlobalVariable(M, I64Ty, false, GlobalValue::InternalLinkage, 0, "last_inline_begin_time");
	gv->setInitializer(initial_value_int_zero);
	gv = new GlobalVariable(M, I64Ty, false, GlobalValue::AvailableExternallyLinkage, 0, "current_time");
	gv->setInitializer(initial_value_int_zero);
	gv = new GlobalVariable(M, I64Ty, false, GlobalValue::AvailableExternallyLinkage, 0, "previous_time");
	gv->setInitializer(initial_value_int_zero);
	gv = new GlobalVariable(M, I64Ty, false, GlobalValue::AvailableExternallyLinkage, 0, "int_flag");
	gv->setInitializer(initial_value_int_zero);
	gv = new GlobalVariable(M, I64Ty, false, GlobalValue::InternalLinkage, 0, "anormaly_total");
	gv->setInitializer(initial_value_int_zero);
	gv = new GlobalVariable(M, I64Ty, false, GlobalValue::AvailableExternallyLinkage, 0, "bb_run_count");
	gv->setInitializer(initial_value_int_zero);
	gv = new GlobalVariable(M, I64Ty, false, GlobalValue::AvailableExternallyLinkage, 0, "pre_bb_num");
	gv->setInitializer(initial_value_int_zero);

	






	//----------------------Mode -1 for dumping out the whole trace function names and basic block names ---------------------------//
	/**
		needs compile and run
		generate ./tgdata.txt, ./ttdata
		./tgdata.txt : each entry: function name, basic block name, 
				whether this basic block is type1, whether this basic block is type2
				yes: 1, no: -1
				generated when compiling

	*/

	if(mode ==-1)
	{
	//global bb num
	for(Module::iterator MI = M.begin(), ME = M.end(); MI != ME; MI++)
	{
		Function *F = MI;
		//errs() << F->getName() << "\n";

		for(Function::iterator FI = MI->begin(), FE = MI->end(); FI != FE; FI++)
		{	
			BasicBlock *BB = FI;
			int num_pred = 0;
			for(pred_iterator PI = pred_begin(BB), E = pred_end(BB); PI != E; PI++)
				num_pred++;
			int has_return_inst = 0;
			for(BasicBlock::iterator BI = FI->begin(), BE = FI->end(); BI != BE; BI++)
			{
				Instruction *II = BI;
				if(isa<ReturnInst>(II))
				{
					has_return_inst = 1;
				}
			}
			int type1 = -1, type2 = -1;

			if((num_pred > 1) || (strcmp(BB->getName().str().c_str(), "entry") == 0) || has_return_inst)
				type2 = 1;

			for(succ_iterator SI = succ_begin(BB), E = succ_end(BB); SI != E; SI++)
			{
				BasicBlock *BBB = *SI;
				int num_pred = 0;
				for(pred_iterator PI = pred_begin(BBB), E = pred_end(BBB); PI != E; PI++)
					num_pred++;
				int has_return_inst = 0;
				for(BasicBlock::iterator BI = SI->begin(), BE = SI->end(); BI != BE; BI++)
				{
					Instruction *II = BI;
					if(isa<ReturnInst>(II))
					{
						has_return_inst = 1;
					}
				}
				if((num_pred > 1) || (strcmp(BBB->getName().str().c_str(), "entry") == 0) || has_return_inst)
					type1 = 1;
			}
			FILE *file;
			char tgtemp[300];
			strcpy(tgtemp, currentd);
			strcat(tgtemp, "/tgdata.txt");
			file = fopen(tgtemp, "a");
			fprintf(file, "%s\n%s\n%d\n%d\n",F->getName().str().c_str(),BB->getName().str().c_str(),type1, type2);
			fclose(file);
		}
	}
	}


	//----------------------Mode 0 ---------------------------//
	/**
		needs compile and run
		generate: ./tdata.txt, ./tidata.txt
		./tdata.txt : 
				generated when running
		./ttdata.txt : program trace, each entry: function name, basic block name
				generated when running
		./tidata.txt : for debug, contains interrupt flag number
				generated when running
	*/

	if(mode ==0)
	{
	int f_count=0;

	for(Module::iterator MI = M.begin(), ME = M.end(); MI != ME; MI++)
	{
		Function *F = MI;
		//if(strstr((char *)F->getName().str().c_str(), "instrument_function") != NULL)errs() << F->getName() << "\n";

		int bb_count =0;
		for(Function::iterator FI = MI->begin(), FE = MI->end(); FI != FE; FI++)
		{	
			//get insert point: the end of the basic block
			BasicBlock *BB = FI;
			IRBuilder<> IRB(BB->getTerminator());
			//errs() << BB->getName() << "\n";
			int num_pred = 0;
			for(pred_iterator PI = pred_begin(BB), E = pred_end(BB); PI != E; PI++)
				num_pred++;

			int num_succ = 0;
			for(succ_iterator SI = succ_begin(BB), E = succ_end(BB); SI != E; SI++)
				num_succ++;
			int has_return_inst = 0;
			for(BasicBlock::iterator BI = FI->begin(), BE = FI->end(); BI != BE; BI++)
			{
				Instruction *II = BI;
				if(isa<ReturnInst>(II))
				{
					has_return_inst = 1;
				}
			}

			//type 2 nodes
			if((num_pred > 1) || (strcmp(BB->getName().str().c_str(), "entry") == 0) || has_return_inst)
			{
				//get time before our time consuming process
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB.CreateLoad(gv);
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				LoadInst *last_time_load = IRB.CreateLoad(gv);
				IRB.CreateStore(load, gv);

				Value *sub = IRB.CreateSub(load, last_time_load);

				Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
				Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);

				Value *args[] = {str_para1, str_para2, sub};
				//insert record
				IRB.CreateCall(instru_insert_record_f, args);

				//get time again after our time consuming process
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB.CreateLoad(gv);
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				IRB.CreateStore(load, gv);
			}

			else
			{
				//insert a -1 value
				Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
				Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
				Value *args[] = {str_para1, str_para2, initial_value_int_minus_one};
				IRB.CreateCall(instru_insert_record_f, args);
			}
			bb_count++;

		}

		if((strcmp(F->getName().str().c_str(), p_entry_function) == 0) && (M.getFunction(p_reference_function) != NULL))
		{
			//dump all timing infomation at the end of ecall
			//IRBuilder<> IRB1(F->back().getTerminator());
			//IRB1.CreateCall(instru_dump_result_f, initial_value_int_zero);
			BasicBlock *BB = &(F->back());
			BasicBlock::iterator BI, BE;
			for(BI = BB->begin(), BE = BB->end(); BI != BE; BI++)
			{
				Instruction *II = BI;
				if(isa<ReturnInst>(II)) break;// || isa<CallInst>(II)) break;
			}
			
			if(BI == BE)
			{
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "-----------found! ------------------------------------------1---------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";

				IRBuilder<> IRB1(F->back().getTerminator());
				IRB1.CreateCall(instru_dump_result_f, initial_value_int_zero);
				IRB1.CreateCall(instru_set_loop_false_f, initial_value_int_zero);

				//get time again after our time consuming process
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//IRB1.CreateStore(load, gv);



			}
			else
			{

			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "-----------found! ------------------------------------------2---------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";


				IRBuilder<> IRB1((Instruction *)BI);
				IRB1.CreateCall(instru_dump_result_f, initial_value_int_zero);
				IRB1.CreateCall(instru_set_loop_false_f, initial_value_int_zero);

				//get time again after our time consuming process
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//IRB1.CreateStore(load, gv);

			}




			//init timer thread at the beginning of ecall
			//clear earlier ecall records at the beginning of ecall
			//IRBuilder<> IRB(F->front().getFirstInsertionPt());
			//IRB.CreateCall(instru_init_f, initial_value_int_zero);
			//IRB.CreateCall(instru_clear_record_f, initial_value_int_zero);

			


		}

		f_count++;

	}
	}




	//----------------------Mode 1 for detection logic instrumentation---------------------------//
	if(mode == 1)
	{

	FILE *ttracefile;
	char ttracetemp[300];
	strcpy(ttracetemp, currentd);
	strcat(ttracetemp, "/tgdata.txt");

	//-------------------processing tgdata.txt-----------------//
	//map for quick access
	llvm::StringMap<struct bb_num_s*> bbmap;

	int longest_f = 0, longest_bb = 0;

	//get global bb_num, type1, type2
	FILE *gbfile;
	char tgtemp3[300];
	strcpy(tgtemp3, currentd);
	strcat(tgtemp3, "/tgdata.txt");
	gbfile = fopen(tgtemp3, "r");
	if(gbfile)
	{
		char *line = NULL;
		size_t len = 0;
		ssize_t read;
		int count = 0;
		struct bb_num_s *ti;
		while((read = getline(&line, &len, gbfile)) != -1)
		{
			//leave out last character '\n'
			line[read-1] = '\0';
			if(count % 4 == 0)
			{
				//function name
				ti = (struct bb_num_s*) malloc (sizeof(struct bb_num_s));
				ti->function_name = (char *) malloc(300);
				strcpy(ti->function_name, line);
			}
			else if(count % 4 == 1)
			{
				//bb name
				ti->bb_name = (char *) malloc(300);
				strcpy(ti->bb_name, line);			
			}
			else if(count % 4 == 2)
			{
				//type1
				ti->type1 = atoi(line);
			}
			else if(count % 4 == 3)
			{
				//type2 and bb global num
				ti->type2 = atoi(line);
				ti->bb_num = (count - 3) / 4;
				bb_num_s_list.push_back(*ti);
				char temp[300];
				strcpy(temp, ti->function_name);
				strcat(temp, ti->bb_name);
				//errs() << temp << "\n";
				std::string tempstr(temp);
				//errs() << tempstr << "\n";
				bbmap[tempstr] = ti;
				//errs() << "ti->function_name: " << ti->function_name << "length:" << strlen(ti->function_name) << "\n";
				//if(strlen(ti->function_name) > longest_f) longest_f = strlen(ti->function_name);
				//if(strlen(ti->bb_name) > longest_bb) longest_bb = strlen(ti->bb_name);
			}

			
			count++;
		}
		fclose(gbfile);
	}
	else
	{
		errs() << "Timed Execution Configration Error: We should have a global basic block file.\n";
		exit(-1);
	}

	/*errs() << "longest function name: " << longest_f << "\n";
	errs() << "longest bb name: " << longest_bb << "\n";

	if(M.getFunction("CRYPTO_num_locks") != NULL)
	{
	FILE *ttfile;
	char tgtemp[120];
	strcpy(tgtemp, currentd);
	strcat(tgtemp, "/my3.txt");
	ttfile = fopen(tgtemp, "a");
	fprintf(ttfile, "%d\n%d\n", longest_f, longest_bb);
	fclose(ttfile);
	}*/

	/*struct bb_num_s* mapt = bbmap["EVP_CIPHER_CTX_freeEVP_CIPHER_CTX_cleanup.exit"];
	if(mapt == NULL) errs() << "mapt == NULL\n";
	else errs() << "the data found in maps is: " << "function name: " << mapt->function_name << "bb name: " 
		<< mapt->bb_name << "bb num: " << mapt->bb_num << "type1 flag: " << mapt->type1 
		<< "type2 flag: " << mapt->type2 << "\n";*/

	/*if(M.getFunction("CRYPTO_num_locks") != NULL)
	{
	for(std::vector<struct bb_num_s>::iterator it = bb_num_s_list.begin() ; it != bb_num_s_list.end(); ++it)
	{
		FILE *file;
		char tgtemp[120];
		strcpy(tgtemp, currentd);
		strcat(tgtemp, "/my.txt");
		file = fopen(tgtemp, "a");
		//printf("%s\n",str);
		//fprintf(file, "%s\n%s\n%lu\n", function_name, bb_name, t);
		fprintf(file, "%s\n%s\n%d\n%d\n%d\n", it->function_name, it->bb_name, it->bb_num, it->type1, it->type2);
		fclose(file);
	}
	}
	bb_num_s_list.clear();*/




	//-------------------processing tdata.txt ttdata.txt-----------------//

	FILE *datafile, *tracefile;
	char tgtemp1[300];
	strcpy(tgtemp1, currentd);
	strcat(tgtemp1, "/tdata.txt");
	char tgtemp2[300];
	strcpy(tgtemp2, currentd);
	strcat(tgtemp2, "/ttdata.txt");
	datafile = fopen(tgtemp1,"r");
	tracefile = fopen(tgtemp2,"r");
	if(datafile)
	{
		if(tracefile)
		{
			char *line1 = NULL;
			size_t len1 = 0;
			ssize_t read1;
			int count1 = 0;
			char *line2 = NULL;
			size_t len2 = 0;
			ssize_t read2;
			int count2 = 0;
			char *line3= NULL;
			size_t len3 = 0;
			ssize_t read3;

			while (((read1 = getline(&line1, &len1, datafile)) != -1) 
				&& ((read2 = getline(&line2, &len2, tracefile)) != -1)
				&& ((read3 = getline(&line3, &len3, tracefile)) != -1))
			{
				//leave out last character '\n'
				line1[read1-1] = '\0';
				line2[read2-1] = '\0';
				line3[read3-1] = '\0';
				struct training_info *ti = (struct training_info*) malloc (sizeof(struct training_info));
				ti->bb_time = atoi(line1);
				ti->function_name = (char *) malloc(300);
				ti->bb_name = (char *) malloc(300);
				strcpy(ti->function_name, line2);
				strcpy(ti->bb_name, line3);
				char temp[300];
				strcpy(temp, ti->function_name);
				strcat(temp, ti->bb_name);
				struct bb_num_s* mapt = bbmap[temp];
				//if(mapt == NULL) errs() << "mapt == NULL\n";
				//else errs() << "the data found in maps is: " << "function name: " << mapt->function_name 
					//<< "bb name: " << mapt->bb_name << "bb num: " << mapt->bb_num << "type1 flag: " 
					//<< mapt->type1 << "type2 flag: " << mapt->type2 << "\n";
				if(mapt == NULL)
				{
					errs() << "--------------- mapt == NULL ----------------\n";
					FILE *file;
					char tgtemp[120];
					strcpy(tgtemp, currentd);
					strcat(tgtemp, "/my2.txt");
					file = fopen(tgtemp, "a");
					fprintf(file, "%s\n%s\n", ti->function_name, ti->bb_name);
					fclose(file);
					ti->bb_num = -1;
					ti->type1 = -1;
					ti->type2 = -1;
				}
				else
				{
					ti->bb_num = mapt->bb_num;
					ti->type1 = mapt->type1;
					ti->type2 = mapt->type2;
				}
				info_list.push_back(*ti);
			}
			fclose(datafile);
			fclose(tracefile);
		}
		else
		{
			errs() << "Timed Execution Configration Error: We should have a trace file.\n";
			exit(-1);
		}
	}
	else
	{
		errs() << "Timed Execution Configration Error: We should have a data file.\n";
		exit(-1);
	}
	bbmap.clear();
	bb_num_s_list.clear();


	/*if(M.getFunction("CRYPTO_num_locks") != NULL)
	{
	for(std::vector<struct training_info>::iterator trit = info_list.begin() ; trit != info_list.end(); ++trit)
	{
		FILE *file;
		char tgtemp[120];
		strcpy(tgtemp, currentd);
		strcat(tgtemp, "/my1.txt");
		file = fopen(tgtemp, "a");
		//printf("%s\n",str);
		//fprintf(file, "%s\n%s\n%lu\n", function_name, bb_name, t);
		fprintf(file, "%s\n%s\n%d\n%d\n%d\n%d\n", trit->function_name, trit->bb_name, trit->bb_time, trit->bb_num, trit->type1, trit->type2);
		fclose(file);

	}
	}*/
	//info_list.clear();




	/*obsolete
	//mark trace nodes type1 and type2
	//mark bb_num
	for(std::vector<struct bb_num_s>::iterator it = bb_num_s_list.begin() ; it != bb_num_s_list.end(); ++it)
	{
		markBBNumType1Type2Info(it->function_name, it->bb_name, it->bb_num, it->type1, it->type2);
	}

	if(M.getFunction("CRYPTO_num_locks") != NULL)
	{
	printMark(M);
	}*/


	//process trace
	//collect trace info from trainging info
	//backwards in training info list
	int need_type1_bb_num = 0;
	struct trace_info *ti;
	for(std::vector<struct training_info>::iterator it = info_list.end() - 1; it >= info_list.begin(); it--)
	{
		if(need_type1_bb_num)
		{
			ti->context_type1_function_name = (char *) malloc(60);
			strcpy(ti->context_type1_function_name, it->function_name);
			ti->context_type1_bb_name = (char *) malloc(60);
			strcpy(ti->context_type1_bb_name, it->bb_name);
			ti->context_type1_bb_num = it->bb_num;
			trace_list.push_back(*ti);
			need_type1_bb_num = 0;
		}
		if(it->type2 == 1)// && it != info_list.begin())
		{
			ti = (struct trace_info*) malloc (sizeof(struct trace_info));
			ti->function_name = (char *) malloc(60);
			strcpy(ti->function_name, it->function_name);
			ti->tail_type2_bb_name = (char *) malloc(60);
			strcpy(ti->tail_type2_bb_name, it->bb_name);
			ti->bb_time = it->bb_time;
			need_type1_bb_num = 1;
			//special handling for the entry of the ecall
			if(it == info_list.begin())
			{
				ti->context_type1_function_name = (char *) malloc(60);
				strcpy(ti->context_type1_function_name, " ");
				ti->context_type1_bb_name = (char *) malloc(60);
				strcpy(ti->context_type1_bb_name, " ");
				ti->context_type1_bb_num = -1;
				trace_list.push_back(*ti);
			}
		}
	}

	//print for debugging
	/*if(M.getFunction("CRYPTO_num_locks") != NULL)
	{
	for(std::vector<struct trace_info>::iterator it = trace_list.begin() ; it != trace_list.end(); it++)
	{
		FILE *file;
		char tgtemp[120];
		strcpy(tgtemp, currentd);
		strcat(tgtemp, "/my4.txt");
		file = fopen(tgtemp, "a");
		//fprintf(file, "%s\n%s\n%d\n%d\n%d\n%d\n", it->function_name, it->bb_name, it->bb_num, it->bb_time, it->type1, it->type2);
		
		//if(strcmp(M.getModuleIdentifier().c_str(), MAINFILE) == 0)
			fprintf(file, "%s\n%s\n%s\n%s\n%d\n%lu\n", 
				it->function_name, it->tail_type2_bb_name, it->context_type1_function_name, it->context_type1_bb_name, it->context_type1_bb_num, it->bb_time);
		
		fclose(file);
	}
	}

	//print for debugging
	int t2_count = 0;
	for(std::vector<struct training_info>::iterator it = info_list.end() - 1; it >= info_list.begin(); it--)
	{
		if(it->type2 == 1) t2_count++;
		//printf("%d\n", t2_count);
	}
	printf("t2_count: %d\n", t2_count);*/

	info_list.clear();




	//instrument type1 nodes
	//type1 nodes put its bb_num to global variable pre_bb_num
	//find every bb in this module first and then traverse trace_list

	int f_count=0;
	for(Module::iterator MI = M.begin(), ME = M.end(); MI != ME; MI++)
	{
		Function *F = MI;
		char* function_name = (char*)malloc(60);
		strcpy(function_name, F->getName().str().c_str());
		int bb_count =0;
		for(Function::iterator FI = MI->begin(), FE = MI->end(); FI != FE; FI++)
		{	
			BasicBlock *BB = FI;
			char* bb_name = (char*)malloc(180);
			strcpy(bb_name, BB->getName().str().c_str());
			IRBuilder<> IRB(BB->getTerminator());
			//errs() << function_name << " " << bb_name << "\n";
			int type1 = -1, type2 = -1;
			std::vector<int> bb_num_vector;
			std::vector<unsigned long> time_vector;
			std::vector<int> bb_num_vector1;
			std::vector<int> visited_vector1;
			std::vector<int> bb_num_vector2;
			std::vector<double> average_vector2;
			std::vector<double> stdev_vector2;
			std::vector<double> b_vector3;
			std::vector<double> c_vector3;
			int context_type1_bb_num = -1;

			//obsolete
			//handle the ecall entry and exit
			/*if((strcmp(function_name, p_entry_function) == 0) && (strcmp(bb_name, "entry") == 0))
			{
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//LoadInst *last_time_load = IRB.CreateLoad(gv);
				//IRB.CreateStore(initial_value_int_zero, gv);


				//IRBuilder<> IRB1(BB->getFirstInsertionPt());
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//IRB1.CreateCall(instru_print_long_long_int_to_debug_f, load);


				//print for debugging
				//IRB.CreateCall(instru_print_int_to_debug_f, last_time_load);
				//IRB.CreateCall(instru_print_int_to_debug_f, load);

				//init timer thread at the beginning of ecall
				//clear earlier ecall records at the beginning of ecall
				IRBuilder<> IRB1(F->front().getFirstInsertionPt());
				IRB1.CreateCall(instru_init_f, initial_value_int_zero);
				//IRB1.CreateCall(instru_clear_record_f, initial_value_int_zero);


			}*/

			for(std::vector<struct trace_info>::iterator it = trace_list.begin() ; it != trace_list.end(); it++)
			{
				//check if this one is type1
				if((strcmp(it->context_type1_function_name, function_name) == 0) && (strcmp(it->context_type1_bb_name, bb_name) == 0))
				{
					type1 = 1;
					context_type1_bb_num = it->context_type1_bb_num;
				}
				//check if any type2 nodes is this one
				if((strcmp(it->function_name, function_name) == 0) && (strcmp(it->tail_type2_bb_name, bb_name) == 0))
				{
					type2 = 1;
					bb_num_vector.push_back(it->context_type1_bb_num);
					time_vector.push_back(it->bb_time);
				}
			}
			//instrument type2 first
			if(type2 == 1)
			{
				errs() << function_name << " " << bb_name << "\n";
				errs() << "type2!\n";
				//errs() << "size of vector: " << bb_num_vector.size();
				//for(std::vector<int>::iterator it = bb_num_vector.begin() ; it != bb_num_vector.end(); it++)
					//for(std::vector<unsigned long>::iterator itt = time_vector.begin() ; itt != time_vector.end(); itt++)
						//errs() << *it << " " << *itt << ", ";
				//errs() << "\n";
				//get average and stdev
				//copy bb_num_vector to bb_num_vector1, bb_num_vector1 works as a temp vector with UNIQUE values
				for(std::vector<int>::iterator it = bb_num_vector.begin() ; it != bb_num_vector.end(); it++)
				{
					int in_it = 0;
					for(std::vector<int>::iterator itt = bb_num_vector1.begin() ; itt != bb_num_vector1.end(); itt++)
						if(*it == *itt) in_it = 1;
					if(in_it == 0)bb_num_vector1.push_back(*it);
				}
				errs() << "size of vector: " << bb_num_vector1.size() << "\n";
				//initialize visited_vector1 as all 0;
				for(std::vector<int>::iterator it = bb_num_vector.begin() ; it != bb_num_vector.end(); it++)
					visited_vector1.push_back(0);
				//check each value in bb_num_vector1
				for(std::vector<int>::iterator it = bb_num_vector1.begin() ; it != bb_num_vector1.end(); it++)
				{
					int count = 0;
					double average = -1.0;
					double stdev = -1.0;
					std::vector<unsigned long> specific_vector;
					//process everyone in bb_num_vector that has such value
					std::vector<int>::iterator itt = bb_num_vector.begin();
					std::vector<int>::iterator ittt = visited_vector1.begin();
					std::vector<unsigned long>::iterator itttt = time_vector.begin();
					while(itt != bb_num_vector.end() && ittt != visited_vector1.end() && itttt != time_vector.end())
					{
						//if it is visited before, do not bother that
						if(*itt == *it && *ittt == 0)
						{
							//mark as visited
							*ittt = 1;
							count++;
							specific_vector.push_back(*itttt);
						}
						itt++;ittt++;itttt++;
					}
					//calculate average
					average = 0;
					for(std::vector<unsigned long>::iterator myit = specific_vector.begin() ; myit != specific_vector.end(); myit++)
						average += *myit;
					average /= count;
					//calculate stdev
					stdev = 0;
					//errs() << "data:\n";
					for(std::vector<unsigned long>::iterator myit = specific_vector.begin() ; myit != specific_vector.end(); myit++)
					{
						//errs() << *myit << " ";
						stdev = stdev + (*myit - average) * (*myit - average);
					}
					//errs() << "\ncount: " << count << "\n";
					stdev /= count;
					stdev = sqrt(stdev);
					//errs() << "stdev: " << stdev << "\n";
					bb_num_vector2.push_back(*it);
					average_vector2.push_back(average);
					stdev_vector2.push_back(stdev);
				}
				std::vector<int>::iterator myit = bb_num_vector2.begin();
				std::vector<double>::iterator myit1 = average_vector2.begin();
				std::vector<double>::iterator myit2 = stdev_vector2.begin();

				//print for debugging
				while(myit != bb_num_vector2.end() && myit1 != average_vector2.end() && myit2 != stdev_vector2.end())
				{
					errs() << "prior bb num: " << *myit << " average: " << *myit1 << " stdev: " << *myit2 << "\n";
					myit++; myit1++; myit2++;
				}



				//---------------------untransformed code----------------------------
				//get times
				/*Constant *str_para = createStringArg(function_name, F);
				str_para = createStringArg(bb_name, F);
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB.CreateLoad(gv);
				Value *curr = load;
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				LoadInst *last_time_load = IRB.CreateLoad(gv);
				IRB.CreateStore(load, gv);
				Value *detect_result_sub_inst = IRB.CreateSub(load, last_time_load);



				int vector_size = bb_num_vector2.size();
				int my_i;
				myit1 = average_vector2.begin();
				myit2 = stdev_vector2.begin();
				for(my_i = 0; my_i < vector_size; my_i++)
				{
					b_vector3.push_back(*myit1 - *myit2);
					c_vector3.push_back(*myit1 + page_fault_average - *myit2 - page_fault_stdev);
					myit1++; myit2++;
				}
				//print for debugging, b_vector3 and c_vector3
				std::vector<double>::iterator mybit = b_vector3.begin();
				std::vector<double>::iterator mycit = c_vector3.begin();
				while((mybit != b_vector3.end()) && (mycit != c_vector3.end()))
				{
					errs() << "b: " << *mybit << " c: " << *mycit << "\n";
					mybit++;mycit++;
				}
				gv = M.getGlobalVariable(StringRef("pre_bb_num"), true);
				load = IRB.CreateLoad(gv);
				myit = bb_num_vector2.begin();
				mybit = b_vector3.begin();
				mycit = c_vector3.begin();
				errs() << "***************************\n";
				if(vector_size == 1)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mybit_value_int = ConstantInt::get(I64Ty, *mybit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);
					Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
					Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
					Value *args[] = {load, detect_result_sub_inst, last_time_load, curr, myit_value_int, mybit_value_int, mycit_value_int, str_para1, str_para2};
					IRB.CreateCall(instru_detect1_f, args);
				}
				else if(vector_size == 2)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mybit_value_int = ConstantInt::get(I64Ty, *mybit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);
					Constant *myit1_value_int = ConstantInt::get(I64Ty, *(myit+1));
					Constant *mybit1_value_int = ConstantInt::get(I64Ty, *(mybit+1));
					Constant *mycit1_value_int = ConstantInt::get(I64Ty, *(mycit+1));
					Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
					Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
					Value *args[] = {load, detect_result_sub_inst, last_time_load, curr, myit_value_int, mybit_value_int, mycit_value_int,
								myit1_value_int, mybit1_value_int, mycit1_value_int, str_para1, str_para2};
					IRB.CreateCall(instru_detect2_f, args);
				}*/
				/*else if(vector_size == 3)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mybit_value_int = ConstantInt::get(I64Ty, *mybit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);
					Constant *myit1_value_int = ConstantInt::get(I64Ty, *(myit+1));
					Constant *mybit1_value_int = ConstantInt::get(I64Ty, *(mybit+1));
					Constant *mycit1_value_int = ConstantInt::get(I64Ty, *(mycit+1));
					Constant *myit2_value_int = ConstantInt::get(I64Ty, *(myit+2));
					Constant *mybit2_value_int = ConstantInt::get(I64Ty, *(mybit+2));
					Constant *mycit2_value_int = ConstantInt::get(I64Ty, *(mycit+2));
					Value *args[] = {load, detect_result_sub_inst, myit_value_int, mybit_value_int, mycit_value_int,
								myit1_value_int, mybit1_value_int, mycit1_value_int,
								myit2_value_int, mybit2_value_int, mycit2_value_int};
					IRB.CreateCall(instru_detect3_f, args);
				}*/


				/*gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB.CreateLoad(gv);
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				IRB.CreateStore(load, gv);*/




				//-----------------------transformed code----------------------------
				/*
					---------		b1-->
					|	|		|
					|	|     =>	|	b2
					|	|		\/	|
					|	|			\/	
					---------		b3
				*/


				//transform

				//get times
				//in basic block b1
				Constant *str_para = createStringArg(function_name, F);
				str_para = createStringArg(bb_name, F);
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB.CreateLoad(gv);
				Value *curr = load;
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				LoadInst *last_time_load = IRB.CreateLoad(gv);
				IRB.CreateStore(load, gv);
				Value *detect_result_sub_inst = IRB.CreateSub(load, last_time_load);

				Value * cmpv = IRB.CreateICmpUGT(load, last_time_load);
				Value *mine_f = M.getOrInsertFunction("mine", VoidTy, I64Ty, nullptr);
			
				if(strcmp(function_name, "prog_init") == 0)
				{
					errs() << "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd\n";
					errs() << "F->getBasicBlockList().size(): " << F->getBasicBlockList().size() <<"\n";


				}

				/*if(//strcmp(function_name, "function_LHASH_COMP") != 0// && strcmp(function_name, "function_LHASH_HASH") != 0
					strcmp(function_name, "SortFnByName") != 0 && strcmp(function_name, "do_cmd") != 0
					&& BB->getInstList().size() >= 3)//&& strcmp(function_name, "lock_dbg_cb") != 0)// && strcmp(function_name, "main") != 0)*/
				/*if(BB->getInstList().size() >= 9 && strcmp(bb_name, "if.end1019") != 0 && strcmp(bb_name, "if.then25") != 0)//strcmp(function_name, "do_cmd") != 0)
				{*/
				Instruction *I1 = BB->getTerminator();
				//Instruction *nop = BinaryOperator::Create(Instruction::Add, initial_value_int_zero, initial_value_int_zero);
				CallInst * callv = CallInst::Create(mine_f, load);
				char name[100];
				strcpy(name, bb_name);
				strcat(name, "b3");
				BB->getInstList().insert(I1, callv);
				BasicBlock *newBB1 = BB->splitBasicBlock(callv, name);

				/*I1 = BB->getTerminator();
				nop = BinaryOperator::Create(Instruction::Add, initial_value_int_zero, initial_value_int_zero);
				BB->getInstList().insert(I1, nop);
				BasicBlock *newBB2 = BB->splitBasicBlock(nop, "newbasicblockb2");

				I1 = BB->getTerminator();
				BranchInst *bran1 = BranchInst::Create(newBB1, newBB2, cmpv);
				ReplaceInstWithInst(I1, bran1);*/
				//}
				





				



				/*int vector_size = bb_num_vector2.size();
				int my_i;
				myit1 = average_vector2.begin();
				myit2 = stdev_vector2.begin();
				for(my_i = 0; my_i < vector_size; my_i++)
				{
					b_vector3.push_back(*myit1 - *myit2);
					c_vector3.push_back(*myit1 + page_fault_average - *myit2 - page_fault_stdev);
					myit1++; myit2++;
				}
				//print for debugging, b_vector3 and c_vector3
				std::vector<double>::iterator mybit = b_vector3.begin();
				std::vector<double>::iterator mycit = c_vector3.begin();
				while((mybit != b_vector3.end()) && (mycit != c_vector3.end()))
				{
					errs() << "b: " << *mybit << " c: " << *mycit << "\n";
					mybit++;mycit++;
				}
				gv = M.getGlobalVariable(StringRef("pre_bb_num"), true);
				load = IRB.CreateLoad(gv);
				myit = bb_num_vector2.begin();
				mybit = b_vector3.begin();
				mycit = c_vector3.begin();
				errs() << "***************************\n";
				if(vector_size == 1)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mybit_value_int = ConstantInt::get(I64Ty, *mybit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);
					Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
					Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
					Value *args[] = {load, detect_result_sub_inst, last_time_load, curr, myit_value_int, mybit_value_int, mycit_value_int, str_para1, str_para2};
					IRBuilder<> IRB(BB->getTerminator());
					IRB.CreateCall(instru_detect1_f, args);
				}
				else if(vector_size == 2)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mybit_value_int = ConstantInt::get(I64Ty, *mybit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);
					Constant *myit1_value_int = ConstantInt::get(I64Ty, *(myit+1));
					Constant *mybit1_value_int = ConstantInt::get(I64Ty, *(mybit+1));
					Constant *mycit1_value_int = ConstantInt::get(I64Ty, *(mycit+1));
					Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
					Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
					Value *args[] = {load, detect_result_sub_inst, last_time_load, curr, myit_value_int, mybit_value_int, mycit_value_int,
								myit1_value_int, mybit1_value_int, mycit1_value_int, str_para1, str_para2};
					IRBuilder<> IRB(BB->getTerminator());
					IRB.CreateCall(instru_detect2_f, args);
				}*/
				/*else if(vector_size == 3)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mybit_value_int = ConstantInt::get(I64Ty, *mybit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);
					Constant *myit1_value_int = ConstantInt::get(I64Ty, *(myit+1));
					Constant *mybit1_value_int = ConstantInt::get(I64Ty, *(mybit+1));
					Constant *mycit1_value_int = ConstantInt::get(I64Ty, *(mycit+1));
					Constant *myit2_value_int = ConstantInt::get(I64Ty, *(myit+2));
					Constant *mybit2_value_int = ConstantInt::get(I64Ty, *(mybit+2));
					Constant *mycit2_value_int = ConstantInt::get(I64Ty, *(mycit+2));
					Value *args[] = {load, detect_result_sub_inst, myit_value_int, mybit_value_int, mycit_value_int,
								myit1_value_int, mybit1_value_int, mycit1_value_int,
								myit2_value_int, mybit2_value_int, mycit2_value_int};
					IRB.CreateCall(instru_detect3_f, args);
				}*/

				//in basic block b3
				/*IRBuilder<> IRB(newBB1->getTerminator());
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB.CreateLoad(gv);
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				IRB.CreateStore(load, gv);*/





			}
			if(type1 == 1)
			{
				//errs() << "type1!\n";
				//errs() << function_name << " " << bb_name << " " << context_type1_bb_num << "\n";
				Constant *bb_num_value = ConstantInt::get(I64Ty, context_type1_bb_num);
				gv = M.getGlobalVariable(StringRef("pre_bb_num"), true);
				IRB.CreateStore(bb_num_value, gv);//done.
			}

			//obsolete
			/*if((strcmp(function_name, p_entry_function) == 0) && (strcmp(bb_name, F->back().getName().str().c_str()) == 0))
			{
				//errs() << "F name: " << F->getName() << " " << "BB name: " << BB->getName() << "\n";
				IRB.CreateCall(instru_dump_detection_result_f, initial_value_int_one);
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB.CreateLoad(gv);
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				IRB.CreateStore(load, gv);
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB.CreateLoad(gv);
				//IRB.CreateCall(instru_print_long_long_int_to_debug_f, load);
			}*/

			free(bb_name);
			bb_num_vector.clear();
			time_vector.clear();
			bb_num_vector1.clear();
			visited_vector1.clear();
			bb_num_vector2.clear();
			average_vector2.clear();
			stdev_vector2.clear();
			b_vector3.clear();
			c_vector3.clear();
		}


		//handle ecall entry and exit
		if((strcmp(function_name, p_entry_function) == 0) && (M.getFunction(p_reference_function) != NULL))
		{
			//dump all detection timing infomation at the end of ecall
			BasicBlock *BB = &(F->back());
			BasicBlock::iterator BI, BE;
			for(BI = BB->begin(), BE = BB->end(); BI != BE; BI++)
			{
				Instruction *II = BI;
				if(isa<ReturnInst>(II) || isa<CallInst>(II)) break;
			}
			
			if(BI == BE)
			{
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "-----------found! ------------------------------------------1---------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";

				IRBuilder<> IRB1(F->back().getTerminator());
				//IRB1.CreateCall(instru_dump_detection_result_f, initial_value_int_zero);
				IRB1.CreateCall(instru_set_loop_false_f, initial_value_int_zero);

				//get time again after our time consuming process
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//IRB1.CreateStore(load, gv);



			}
			else
			{

			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "-----------found! ------------------------------------------2---------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";


				IRBuilder<> IRB1((Instruction *)BI);
				//IRB1.CreateCall(instru_dump_detection_result_f, initial_value_int_zero);
				IRB1.CreateCall(instru_set_loop_false_f, initial_value_int_zero);

				//get time again after our time consuming process
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//IRB1.CreateStore(load, gv);

			}




			//init timer thread at the beginning of ecall
			//clear earlier ecall records at the beginning of ecall
			IRBuilder<> IRB(F->front().getFirstInsertionPt());
			//IRB.CreateCall(instru_init_f, initial_value_int_zero);
			//IRB.CreateCall(instru_clear_record_f, initial_value_int_zero);
		}


		free(function_name);

	}
	
	trace_list.clear();







	}


	//----------------------Mode 2 ---------------------------//
	/**
		needs compile and run
		generate: ./tdata.txt, ./tidata.txt
		./tdata.txt : 
				generated when running
		./tidata.txt : for debug, contains interrupt flag number
				generated when running

		copy from Mode 1 and some changes
		for performance evaluation

	*/

	int mytemptemp = 0;
	if(mode ==2)
	{
	int f_count=0;

	for(Module::iterator MI = M.begin(), ME = M.end(); MI != ME; MI++)
	{
		Function *F = MI;
		//errs() << F->getName() << "\n";

		int bb_count =0;
		for(Function::iterator FI = MI->begin(), FE = MI->end(); FI != FE; FI++)
		{	
			//get insert point: the end of the basic block
			BasicBlock *BB = FI;
			IRBuilder<> IRB(BB->getTerminator());

			int num_pred = 0;
			for(pred_iterator PI = pred_begin(BB), E = pred_end(BB); PI != E; PI++)
				num_pred++;

			int num_succ = 0;
			for(succ_iterator SI = succ_begin(BB), E = succ_end(BB); SI != E; SI++)
				num_succ++;
			int has_return_inst = 0;
			for(BasicBlock::iterator BI = FI->begin(), BE = FI->end(); BI != BE; BI++)
			{
				Instruction *II = BI;
				if(isa<ReturnInst>(II))
				{
					has_return_inst = 1;
				}
			}

			//type 2 nodes
			if((num_pred > 1) || (strcmp(BB->getName().str().c_str(), "entry") == 0) || has_return_inst)
			{
				//get time before our time consuming process
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB.CreateLoad(gv);
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				LoadInst *last_time_load = IRB.CreateLoad(gv);
				IRB.CreateStore(load, gv);

				Value *sub = IRB.CreateSub(load, last_time_load);

				Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
				Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);

				Value *args[] = {str_para1, str_para2, sub};
				//insert record
				if(mytemptemp == 0)IRB.CreateCall(instru_insert_record_f, args);
				mytemptemp++;


				//get time again after our time consuming process
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB.CreateLoad(gv);
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				IRB.CreateStore(load, gv);
			}

			else
			{
				//insert a -1 value
				/*Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
				Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
				Value *args[] = {str_para1, str_para2, initial_value_int_minus_one};
				IRB.CreateCall(instru_insert_record_f, args);*/
			}
			bb_count++;

		}

		if((strcmp(F->getName().str().c_str(), p_entry_function) == 0) && (M.getFunction(p_reference_function) != NULL))
		{
			//dump all timing infomation at the end of ecall
			//IRBuilder<> IRB1(F->back().getTerminator());
			//IRB1.CreateCall(instru_dump_result_f, initial_value_int_zero);
			BasicBlock *BB = &(F->back());
			BasicBlock::iterator BI, BE;
			for(BI = BB->begin(), BE = BB->end(); BI != BE; BI++)
			{
				Instruction *II = BI;
				if(isa<ReturnInst>(II) || isa<CallInst>(II)) break;
			}
			
			if(BI == BE)
			{
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "-----------found! ------------------------------------------1---------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";

				IRBuilder<> IRB1(F->back().getTerminator());
				//IRB1.CreateCall(instru_print_time_f, initial_value_int_zero);
				//IRB1.CreateCall(instru_dump_result_f, initial_value_int_zero);
				//IRB1.CreateCall(instru_set_loop_false_f, initial_value_int_zero);
				//IRB1.CreateCall(instru_print_time_f, initial_value_int_zero);

				//get time again after our time consuming process
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//IRB1.CreateStore(load, gv);



			}
			else
			{

			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "-----------found! ------------------------------------------2---------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";


				IRBuilder<> IRB1((Instruction *)BI);
				//IRB1.CreateCall(instru_print_time_f, initial_value_int_zero);
				//IRB1.CreateCall(instru_dump_result_f, initial_value_int_zero);
				//IRB1.CreateCall(instru_set_loop_false_f, initial_value_int_zero);
				//IRB1.CreateCall(instru_print_time_f, initial_value_int_zero);

				//get time again after our time consuming process
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//IRB1.CreateStore(load, gv);

			}




			//init timer thread at the beginning of ecall
			//clear earlier ecall records at the beginning of ecall
			IRBuilder<> IRB(F->front().getFirstInsertionPt());
			//IRB.CreateCall(instru_print_time_f, initial_value_int_zero);
			//IRB.CreateCall(instru_init_f, initial_value_int_zero);
			//IRB.CreateCall(instru_clear_record_f, initial_value_int_zero);

			


		}

		f_count++;

	}
	}




	//----------------------Mode 3 ---------------------------//
	/**
		needs compile and run
		generate: ./tdata.txt, ./tidata.txt
		./tdata.txt : 
				generated when running
		./tidata.txt : for debug, contains interrupt flag number
				generated when running

		copy from Mode 1 and some changes
		for performance evaluation

	*/

	if(mode ==3)
	{
	int f_count=0;

	for(Module::iterator MI = M.begin(), ME = M.end(); MI != ME; MI++)
	{
		Function *F = MI;
		//errs() << F->getName() << "\n";

		if((strcmp(F->getName().str().c_str(), p_entry_function) == 0) && (M.getFunction(p_reference_function) != NULL))
		{
			//dump all timing infomation at the end of ecall
			//IRBuilder<> IRB1(F->back().getTerminator());
			//IRB1.CreateCall(instru_dump_result_f, initial_value_int_zero);
			BasicBlock *BB = &(F->back());
			BasicBlock::iterator BI, BE;
			for(BI = BB->begin(), BE = BB->end(); BI != BE; BI++)
			{
				Instruction *II = BI;
				if(isa<ReturnInst>(II) || isa<CallInst>(II)) break;
			}
			
			if(BI == BE)
			{
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "-----------found! ------------------------------------------1---------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";

				IRBuilder<> IRB1(F->back().getTerminator());
				//IRB1.CreateCall(instru_print_time_f, initial_value_int_zero);

				//get time again after our time consuming process
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//IRB1.CreateStore(load, gv);



			}
			else
			{

			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "-----------found! ------------------------------------------2---------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";


				IRBuilder<> IRB1((Instruction *)BI);
				//IRB1.CreateCall(instru_print_time_f, initial_value_int_zero);

				//get time again after our time consuming process
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//IRB1.CreateStore(load, gv);

			}




			//init timer thread at the beginning of ecall
			//clear earlier ecall records at the beginning of ecall
			IRBuilder<> IRB(F->front().getFirstInsertionPt());
			//IRB.CreateCall(instru_print_time_f, initial_value_int_zero);
			//IRB.CreateCall(instru_clear_record_f, initial_value_int_zero);

			


		}

		f_count++;

	}
	}


	//----------------------Mode 4 ---------------------------//
	/**
		needs compile and run
		generate: ./tdata.txt, ./tidata.txt
		./tdata.txt : 
				generated when running
		./tidata.txt : for debug, contains interrupt flag number
				generated when running


		copy from Mode 1 and some changes
		for basic block tranformation expriment

	*/


	//this mode is for new feature playing

	if(mode ==4)
	{
	int f_count=0;

	for(Module::iterator MI = M.begin(), ME = M.end(); MI != ME; MI++)
	{
		Function *F = MI;
		//errs() << F->getName() << "\n";

		if(strcmp(F->getName().str().c_str(), "main") == 0)
		{			

			BasicBlock *B1, *B2, *B3, *B4, *B5;
			for(Function::iterator FI = MI->begin(), FE = MI->end(); FI != FE; FI++)
			{	
				BasicBlock *BB = FI;
				errs() <<  BB->getName() << "\n";
				if(strcmp(BB->getName().str().c_str(), "while.body") == 0) B1 = BB;
				if(strcmp(BB->getName().str().c_str(), "if.then") == 0) B2 = BB;
				if(strcmp(BB->getName().str().c_str(), "while.end") == 0) B3 = BB;
				if(strcmp(BB->getName().str().c_str(), "if.end") == 0) B4 = BB;
				if(strcmp(BB->getName().str().c_str(), "if.else") == 0) B5 = BB;
			}
			//errs() <<  B1->getName() << "\n";
			//errs() <<  B2->getName() << "\n";
			//errs() <<  B3->getName() << "\n";

			//Instruction *I = B2->getTerminator();
			//I->print(errs());
			//if(isa<BranchInst>(I)) errs() << "yes....\n";

			Value *your_f = M.getOrInsertFunction("your", VoidTy, I64Ty, nullptr);
			

			//Instruction *nop = BinaryOperator::Create(Instruction::Add, initial_value_int_zero, initial_value_int_zero);
			//B2->getInstList().insert(I, nop);

			//BasicBlock *newBB = B2->splitBasicBlock(nop, "newbasicblock");

			TerminatorInst *I1 = B1->getTerminator();
			//gv = new GlobalVariable(M, I64Ty, false, GlobalValue::AvailableExternallyLinkage, ConstantInt::get(I64Ty, 4), "myglobal");
			Value *mine_f = M.getOrInsertFunction("mine", VoidTy, I64Ty, nullptr);
			//gv->setInitializer(initial_value_int_zero);
			IRBuilder<> builder(&(B1->back()));
			gv = M.getGlobalVariable(StringRef("i"), true);
			load = builder.CreateLoad(gv);
			gv = M.getGlobalVariable(StringRef("myglobal"), true);	
			LoadInst * lload = builder.CreateLoad(gv);	
			//Value *myv = builder.CreateAdd(initial_value_int_zero, load);
			builder.CreateCall(mine_f, load);
			//my->getType()->print(COUT);
			//errs() << "type: " << COUT.str() << "\n";
			Value * cmpv = builder.CreateICmpUGT(lload, load);
			//Value * cmpv = builder.CreateICmpUGT(load, initial_value_int_zero);
			//builder.CreateStore(cmpv, gv);


			
			//BasicBlock *bb1 = BasicBlock::Create(F->getContext(), "bb1");
			//bb1->getInstList().push_back(CallInst::Create(your_f, initial_value_int_zero));
			//bb1->getInstList().push_back(BranchInst::Create(B2));

			BranchInst *bran = BranchInst::Create(B2, B5, cmpv);
			ReplaceInstWithInst(I1, bran);


			//IRBuilder<> builder1(&(B1->back()));
			//Value *addv = builder1.CreateAdd(lload, load);

			I1 = B1->getTerminator();
			//Instruction *nop1 = BinaryOperator::Create(Instruction::Add, lload, load);
			CallInst * callv = CallInst::Create(mine_f, lload);
			B2->getInstList().insert(I1, callv);
			
			BasicBlock *newBB1 = B1->splitBasicBlock(callv, "newbasicblock1");
			I1 = B1->getTerminator();
			BranchInst *bran1 = BranchInst::Create(newBB1, B2, cmpv);
			ReplaceInstWithInst(I1, bran1);


			I1 = B4->getTerminator();
			callv = CallInst::Create(mine_f, lload);
			B4->getInstList().insert(I1, callv);
			newBB1 = B4->splitBasicBlock(callv, "newbasicblock2");

			I1 = B4->getTerminator();
			callv = CallInst::Create(mine_f, lload);
			B4->getInstList().insert(I1, callv);
			BasicBlock *newBB2 = B4->splitBasicBlock(callv, "newbasicblock3");

			I1 = B4->getTerminator();
			bran1 = BranchInst::Create(newBB1, newBB2, cmpv);
			ReplaceInstWithInst(I1, bran1);



			//Instruction *newBBI1 = newBB->getTerminator();
			//ReplaceInstWithInst(newBBI1, BranchInst::Create(B2));

			//I1 = B2->getTerminator();
			//ReplaceInstWithInst(I1, BranchInst::Create(B4));


			


			/*newBB->getInstList().insert(nop, CallInst::Create(your_f, initial_value_int_zero));


			Instruction *I1 = B2->getTerminator();
			Instruction *nop1 = BinaryOperator::Create(Instruction::Add, initial_value_int_zero, initial_value_int_zero);
			B2->getInstList().insert(I1, nop1);
			BasicBlock *newBB1 = B2->splitBasicBlock(nop1, "newbasicblock1");
			newBB1->getInstList().insert(nop1, CallInst::Create(your_f, initial_value_int_zero));

			Instruction *I2 = B2->getTerminator();
			I2->print(errs());*/

			/*BasicBlock *bb1 = BasicBlock::Create(F->getContext(), "bb1");
			bb1->getInstList().push_back(CallInst::Create(your_f, initial_value_int_zero));
			Instruction *i1 = bb1->getTerminator();
			ReplaceInstWithInst(i1, BranchInst::Create(B3));
			ReplaceInstWithInst(newBBI1, BranchInst::Create(bb1));*/

			//IRBuilder<> builder(I2);
			//gv = M.getGlobalVariable(StringRef("i"), true);
			//load = builder.CreateLoad(gv);
			//BranchInst *bran = BranchInst::Create(B2->getTerminator()->getSuccessor(0), B3, initial_value_int_zero);
			//ReplaceInstWithInst(I2, bran);



			





			//IRBuilder<> builder(I);
			//Instruction *nop = cast<Instruction>(builder.CreateAdd(initial_value_int_zero, initial_value_int_zero));

			//nop->print(errs());



			//ReplaceInstWithInst(I, BranchInst::Create(B3));



			/*BasicBlock *bb1 = BasicBlock::Create(F->getContext(), "bb1");
			BranchInst *bi;
			bi = BranchInst::Create(B3);
			bb1->getInstList().push_back(bi);
			//Value *your_f = M.getOrInsertFunction("your", VoidTy, I64Ty, nullptr);
			//bb1->getInstList().insert(bi, CallInst::Create(your_f, initial_value_int_zero));

			ReplaceInstWithInst(I, BranchInst::Create(bb1));*/
			





			//Instruction *nop = BinaryOperator::Create(Instruction::Add, );
			//Instruction *nop = cast<Instruction>(builder.CreateAdd(initial_value_int_zero, initial_value_int_zero));
			//builder.SetInsertPoint(nop);

			//nop->print(errs());

			


			//I->eraseFromParent();
			//B2->getInstList().push_back(BranchInst::Create(B1));



			/*Value *your_f = M.getOrInsertFunction("your", VoidTy, I64Ty, nullptr);
			BasicBlock *bb1 = BasicBlock::Create(F->getContext(), "bb1");
			IRBuilder<> builder(bb1);
			builder.CreateCall(your_f, initial_value_int_zero);
			builder.CreateRetVoid();

			int iv = 0;
			BasicBlock *B = &(F->front());
			BasicBlock *BB = &(F->back());
			BasicBlock::iterator BI, BE;
			Instruction *II;
			for(BI = BB->begin(), BE = BB->end(); BI != BE; BI++)
			{
				II = BI;
				iv++;
				if(iv == 2) break;
			}
			II->print(errs());
			builder.SetInsertPoint(BB);
			builder.CreateBr(B);*/



		}
		f_count++;

	}
	}


	//----------------------Mode 5 ---------------------------//
	/**
		needs compile and run
		generate: ./tdata.txt, ./tidata.txt
		./tdata.txt : 
				generated when running
		./tidata.txt : for debug, contains interrupt flag number
				generated when running
		traning for rdtsc
		copy from mode 0

	*/

	if(mode ==5)
	{
	int f_count=0;

	for(Module::iterator MI = M.begin(), ME = M.end(); MI != ME; MI++)
	{
		Function *F = MI;
		//errs() << F->getName() << "\n";

		int bb_count =0;
		for(Function::iterator FI = MI->begin(), FE = MI->end(); FI != FE; FI++)
		{	
			//get insert point: the end of the basic block
			BasicBlock *BB = FI;
			IRBuilder<> IRB(BB->getTerminator());

			int num_pred = 0;
			for(pred_iterator PI = pred_begin(BB), E = pred_end(BB); PI != E; PI++)
				num_pred++;

			int num_succ = 0;
			for(succ_iterator SI = succ_begin(BB), E = succ_end(BB); SI != E; SI++)
				num_succ++;
			int has_return_inst = 0;
			for(BasicBlock::iterator BI = FI->begin(), BE = FI->end(); BI != BE; BI++)
			{
				Instruction *II = BI;
				if(isa<ReturnInst>(II))
				{
					has_return_inst = 1;
				}
			}

			//type 2 nodes
			if((num_pred > 1) || (strcmp(BB->getName().str().c_str(), "entry") == 0) || has_return_inst)
			{
				Value *get_time_f = M.getOrInsertFunction("get_time", I64Ty, I64Ty, nullptr);
				Value *insert_real_time_f = M.getOrInsertFunction("insert_real_time", VoidTy, I64Ty, nullptr);

				//get time before our time consuming process
				CallInst * get = IRB.CreateCall(get_time_f, initial_value_int_zero);
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				LoadInst *last_time_load = IRB.CreateLoad(gv);
				IRB.CreateStore(get, gv);

				Value *sub = IRB.CreateSub(get, last_time_load);

				//print real time
				IRB.CreateCall(insert_real_time_f, sub);


				//get time again after our time consuming process
				get = IRB.CreateCall(get_time_f, initial_value_int_zero);
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				IRB.CreateStore(get, gv);
			}

			else
			{
				//insert a -1 value
				Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
				Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
				Value *args[] = {str_para1, str_para2, initial_value_int_minus_one};
				IRB.CreateCall(instru_insert_record_f, args);
			}
			bb_count++;

		}

		if((strcmp(F->getName().str().c_str(), p_entry_function) == 0) && (M.getFunction(p_reference_function) != NULL))
		{
			Value *print_real_time_f = M.getOrInsertFunction("print_real_time", VoidTy, I64Ty, nullptr);

			//dump all timing infomation at the end of ecall
			//IRBuilder<> IRB1(F->back().getTerminator());
			//IRB1.CreateCall(instru_dump_result_f, initial_value_int_zero);
			BasicBlock *BB = &(F->back());
			BasicBlock::iterator BI, BE;
			for(BI = BB->begin(), BE = BB->end(); BI != BE; BI++)
			{
				Instruction *II = BI;
				if(isa<ReturnInst>(II) || isa<CallInst>(II)) break;
			}
			
			if(BI == BE)
			{
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "-----------found! ------------------------------------------1---------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";

				IRBuilder<> IRB1(F->back().getTerminator());
				//IRB1.CreateCall(instru_dump_result_f, initial_value_int_zero);				
				IRB1.CreateCall(instru_set_loop_false_f, initial_value_int_zero);
				IRB1.CreateCall(print_real_time_f, initial_value_int_zero);

				//get time again after our time consuming process
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//IRB1.CreateStore(load, gv);



			}
			else
			{

			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "-----------found! ------------------------------------------2---------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";


				IRBuilder<> IRB1((Instruction *)BI);
				//IRB1.CreateCall(instru_dump_result_f, initial_value_int_zero);
				IRB1.CreateCall(instru_set_loop_false_f, initial_value_int_zero);
				IRB1.CreateCall(print_real_time_f, initial_value_int_zero);

				//get time again after our time consuming process
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//IRB1.CreateStore(load, gv);

			}




			//init timer thread at the beginning of ecall
			//clear earlier ecall records at the beginning of ecall
			IRBuilder<> IRB(F->front().getFirstInsertionPt());
			//IRB.CreateCall(instru_init_f, initial_value_int_zero);
			//IRB.CreateCall(instru_clear_record_f, initial_value_int_zero);

			


		}

		f_count++;

	}
	}





	//----------------------Mode 6 for detection logic instrumentation---------------------------//

	//optimized for performance, copied from mode 1

	if(mode == 6)
	{
	FILE *ttracefile;
	char ttracetemp[300];
	strcpy(ttracetemp, currentd);
	strcat(ttracetemp, "/ttracedata.txt");

	//if file does not exist
	if(access(ttracetemp, 0) == -1)
	{
	//-------------------processing tgdata.txt-----------------//
	//map for quick access
	llvm::StringMap<struct bb_num_s*> bbmap;

	int longest_f = 0, longest_bb = 0;

	//get global bb_num, type1, type2
	FILE *gbfile;
	char tgtemp3[300];
	strcpy(tgtemp3, currentd);
	strcat(tgtemp3, "/tgdata.txt");
	gbfile = fopen(tgtemp3, "r");
	if(gbfile)
	{
		char *line = NULL;
		size_t len = 0;
		ssize_t read;
		int count = 0;
		struct bb_num_s *ti;
		while((read = getline(&line, &len, gbfile)) != -1)
		{
			//leave out last character '\n'
			line[read-1] = '\0';
			if(count % 4 == 0)
			{
				//function name
				ti = (struct bb_num_s*) malloc (sizeof(struct bb_num_s));
				ti->function_name = (char *) malloc(300);
				strcpy(ti->function_name, line);
			}
			else if(count % 4 == 1)
			{
				//bb name
				ti->bb_name = (char *) malloc(300);
				strcpy(ti->bb_name, line);			
			}
			else if(count % 4 == 2)
			{
				//type1
				ti->type1 = atoi(line);
			}
			else if(count % 4 == 3)
			{
				//type2 and bb global num
				ti->type2 = atoi(line);
				ti->bb_num = (count - 3) / 4;
				bb_num_s_list.push_back(*ti);
				char temp[300];
				strcpy(temp, ti->function_name);
				strcat(temp, ti->bb_name);
				//errs() << temp << "\n";
				std::string tempstr(temp);
				//errs() << tempstr << "\n";
				bbmap[tempstr] = ti;
				//errs() << "ti->function_name: " << ti->function_name << "length:" << strlen(ti->function_name) << "\n";
				//if(strlen(ti->function_name) > longest_f) longest_f = strlen(ti->function_name);
				//if(strlen(ti->bb_name) > longest_bb) longest_bb = strlen(ti->bb_name);
			}

			
			count++;
		}
		fclose(gbfile);
	}
	else
	{
		errs() << "Timed Execution Configration Error: We should have a global basic block file.\n";
		exit(-1);
	}

	/*errs() << "longest function name: " << longest_f << "\n";
	errs() << "longest bb name: " << longest_bb << "\n";

	if(M.getFunction("CRYPTO_num_locks") != NULL)
	{
	FILE *ttfile;
	char tgtemp[120];
	strcpy(tgtemp, currentd);
	strcat(tgtemp, "/my3.txt");
	ttfile = fopen(tgtemp, "a");
	fprintf(ttfile, "%d\n%d\n", longest_f, longest_bb);
	fclose(ttfile);
	}*/

	/*struct bb_num_s* mapt = bbmap["EVP_CIPHER_CTX_freeEVP_CIPHER_CTX_cleanup.exit"];
	if(mapt == NULL) errs() << "mapt == NULL\n";
	else errs() << "the data found in maps is: " << "function name: " << mapt->function_name << "bb name: " 
		<< mapt->bb_name << "bb num: " << mapt->bb_num << "type1 flag: " << mapt->type1 
		<< "type2 flag: " << mapt->type2 << "\n";*/

	/*if(M.getFunction("CRYPTO_num_locks") != NULL)
	{
	for(std::vector<struct bb_num_s>::iterator it = bb_num_s_list.begin() ; it != bb_num_s_list.end(); ++it)
	{
		FILE *file;
		char tgtemp[120];
		strcpy(tgtemp, currentd);
		strcat(tgtemp, "/my.txt");
		file = fopen(tgtemp, "a");
		//printf("%s\n",str);
		//fprintf(file, "%s\n%s\n%lu\n", function_name, bb_name, t);
		fprintf(file, "%s\n%s\n%d\n%d\n%d\n", it->function_name, it->bb_name, it->bb_num, it->type1, it->type2);
		fclose(file);
	}
	}
	bb_num_s_list.clear();*/




	//-------------------processing tdata.txt ttdata.txt-----------------//

	FILE *datafile, *tracefile;
	char tgtemp1[300];
	strcpy(tgtemp1, currentd);
	strcat(tgtemp1, "/tdata.txt");
	char tgtemp2[300];
	strcpy(tgtemp2, currentd);
	strcat(tgtemp2, "/ttdata.txt");
	datafile = fopen(tgtemp1,"r");
	tracefile = fopen(tgtemp2,"r");
	if(datafile)
	{
		if(tracefile)
		{
			char *line1 = NULL;
			size_t len1 = 0;
			ssize_t read1;
			int count1 = 0;
			char *line2 = NULL;
			size_t len2 = 0;
			ssize_t read2;
			int count2 = 0;
			char *line3= NULL;
			size_t len3 = 0;
			ssize_t read3;

			while (((read1 = getline(&line1, &len1, datafile)) != -1) 
				&& ((read2 = getline(&line2, &len2, tracefile)) != -1)
				&& ((read3 = getline(&line3, &len3, tracefile)) != -1))
			{
				//leave out last character '\n'
				line1[read1-1] = '\0';
				line2[read2-1] = '\0';
				line3[read3-1] = '\0';
				struct training_info *ti = (struct training_info*) malloc (sizeof(struct training_info));
				ti->bb_time = atoi(line1);
				ti->function_name = (char *) malloc(300);
				ti->bb_name = (char *) malloc(300);
				strcpy(ti->function_name, line2);
				strcpy(ti->bb_name, line3);
				char temp[300];
				strcpy(temp, ti->function_name);
				strcat(temp, ti->bb_name);
				struct bb_num_s* mapt = bbmap[temp];
				//if(mapt == NULL) errs() << "mapt == NULL\n";
				//else errs() << "the data found in maps is: " << "function name: " << mapt->function_name 
					//<< "bb name: " << mapt->bb_name << "bb num: " << mapt->bb_num << "type1 flag: " 
					//<< mapt->type1 << "type2 flag: " << mapt->type2 << "\n";
				if(mapt == NULL)
				{
					errs() << "--------------- mapt == NULL ----------------\n";
					FILE *file;
					char tgtemp[120];
					strcpy(tgtemp, currentd);
					strcat(tgtemp, "/my2.txt");
					file = fopen(tgtemp, "a");
					fprintf(file, "%s\n%s\n", ti->function_name, ti->bb_name);
					fclose(file);
					ti->bb_num = -1;
					ti->type1 = -1;
					ti->type2 = -1;
				}
				else
				{
					ti->bb_num = mapt->bb_num;
					ti->type1 = mapt->type1;
					ti->type2 = mapt->type2;
				}
				info_list.push_back(*ti);
			}
			fclose(datafile);
			fclose(tracefile);
		}
		else
		{
			errs() << "Timed Execution Configration Error: We should have a trace file.\n";
			exit(-1);
		}
	}
	else
	{
		errs() << "Timed Execution Configration Error: We should have a data file.\n";
		exit(-1);
	}
	bbmap.clear();
	bb_num_s_list.clear();


	/*if(M.getFunction("CRYPTO_num_locks") != NULL)
	{
	for(std::vector<struct training_info>::iterator trit = info_list.begin() ; trit != info_list.end(); ++trit)
	{
		FILE *file;
		char tgtemp[120];
		strcpy(tgtemp, currentd);
		strcat(tgtemp, "/my1.txt");
		file = fopen(tgtemp, "a");
		//printf("%s\n",str);
		//fprintf(file, "%s\n%s\n%lu\n", function_name, bb_name, t);
		fprintf(file, "%s\n%s\n%d\n%d\n%d\n%d\n", trit->function_name, trit->bb_name, trit->bb_time, trit->bb_num, trit->type1, trit->type2);
		fclose(file);

	}
	}*/
	//info_list.clear();




	/*obsolete
	//mark trace nodes type1 and type2
	//mark bb_num
	for(std::vector<struct bb_num_s>::iterator it = bb_num_s_list.begin() ; it != bb_num_s_list.end(); ++it)
	{
		markBBNumType1Type2Info(it->function_name, it->bb_name, it->bb_num, it->type1, it->type2);
	}

	if(M.getFunction("CRYPTO_num_locks") != NULL)
	{
	printMark(M);
	}*/


	//process trace
	//collect trace info from trainging info
	//backwards in training info list
	int need_type1_bb_num = 0;
	struct trace_info *ti;
	for(std::vector<struct training_info>::iterator it = info_list.end() - 1; it >= info_list.begin(); it--)
	{
		if(need_type1_bb_num)
		{
			ti->context_type1_function_name = (char *) malloc(60);
			strcpy(ti->context_type1_function_name, it->function_name);
			ti->context_type1_bb_name = (char *) malloc(60);
			strcpy(ti->context_type1_bb_name, it->bb_name);
			ti->context_type1_bb_num = it->bb_num;
			trace_list.push_back(*ti);
			need_type1_bb_num = 0;
		}
		if(it->type2 == 1)// && it != info_list.begin())
		{
			ti = (struct trace_info*) malloc (sizeof(struct trace_info));
			ti->function_name = (char *) malloc(60);
			strcpy(ti->function_name, it->function_name);
			ti->tail_type2_bb_name = (char *) malloc(60);
			strcpy(ti->tail_type2_bb_name, it->bb_name);
			ti->bb_time = it->bb_time;
			need_type1_bb_num = 1;
			//special handling for the entry of the ecall
			if(it == info_list.begin())
			{
				ti->context_type1_function_name = (char *) malloc(60);
				strcpy(ti->context_type1_function_name, " ");
				ti->context_type1_bb_name = (char *) malloc(60);
				strcpy(ti->context_type1_bb_name, " ");
				ti->context_type1_bb_num = -1;
				trace_list.push_back(*ti);
			}
		}
	}

	//print for debugging
	/*if(M.getFunction("CRYPTO_num_locks") != NULL)
	{
	for(std::vector<struct trace_info>::iterator it = trace_list.begin() ; it != trace_list.end(); it++)
	{
		FILE *file;
		char tgtemp[120];
		strcpy(tgtemp, currentd);
		strcat(tgtemp, "/my4.txt");
		file = fopen(tgtemp, "a");
		//fprintf(file, "%s\n%s\n%d\n%d\n%d\n%d\n", it->function_name, it->bb_name, it->bb_num, it->bb_time, it->type1, it->type2);
		
		//if(strcmp(M.getModuleIdentifier().c_str(), MAINFILE) == 0)
			fprintf(file, "%s\n%s\n%s\n%s\n%d\n%lu\n", 
				it->function_name, it->tail_type2_bb_name, it->context_type1_function_name, it->context_type1_bb_name, it->context_type1_bb_num, it->bb_time);
		
		fclose(file);
	}
	}

	//print for debugging
	int t2_count = 0;
	for(std::vector<struct training_info>::iterator it = info_list.end() - 1; it >= info_list.begin(); it--)
	{
		if(it->type2 == 1) t2_count++;
		//printf("%d\n", t2_count);
	}
	printf("t2_count: %d\n", t2_count);*/

	info_list.clear();

	//save to file
	for(std::vector<struct trace_info>::iterator it = trace_list.begin() ; it != trace_list.end(); it++)
	{
		//errs() << "save to file\n";
		FILE *file;
		char tgtemp[120];
		strcpy(tgtemp, currentd);
		strcat(tgtemp, "/ttracedata.txt");
		file = fopen(tgtemp, "a");
			fprintf(file, "%s\n%s\n%s\n%s\n%d\n%lu\n", 
				it->function_name, it->tail_type2_bb_name, it->context_type1_function_name, it->context_type1_bb_name, it->context_type1_bb_num, it->bb_time);
		fclose(file);
	}
	}
	//file exists
	else
	{
	FILE *gbfile;
	char tgtemp3[300];
	strcpy(tgtemp3, currentd);
	strcat(tgtemp3, "/ttracedata.txt");
	gbfile = fopen(tgtemp3, "r");
	if(gbfile)
	{
		char *line = NULL;
		size_t len = 0;
		ssize_t read;
		int count = 0;
		struct trace_info *ti;
		while((read = getline(&line, &len, gbfile)) != -1)
		{
			//leave out last character '\n'
			line[read-1] = '\0';
			if(count % 4 == 0)
			{
				//function name
				ti = (struct trace_info*) malloc (sizeof(struct trace_info));
				ti->function_name = (char *) malloc(300);
				strcpy(ti->function_name, line);
			}
			else if(count % 4 == 1)
			{
				//type2 bb name
				ti->tail_type2_bb_name = (char *) malloc(300);
				strcpy(ti->tail_type2_bb_name, line);			
			}
			else if(count % 4 == 2)
			{
				//context type1 function name
				ti->context_type1_function_name = (char *) malloc(300);
				strcpy(ti->context_type1_function_name, line);			
			}
			else if(count % 4 == 3)
			{
				//context type1 bb name
				ti->context_type1_bb_name = (char *) malloc(300);
				strcpy(ti->context_type1_bb_name, line);			
			}
			else if(count % 4 == 4)
			{
				//context type1 bb num
				ti->context_type1_bb_num = atoi(line);
			}
			else if(count % 4 == 5)
			{
				//type2 and bb global num
				ti->bb_time = atoi(line);
				trace_list.push_back(*ti);
			}
			count++;
		}
		fclose(gbfile);
	}
	else
	{
		errs() << "Timed Execution Configration Error: We should have a processed trace file.\n";
		exit(-1);
	}

	}


	//instrument type1 nodes
	//type1 nodes put its bb_num to global variable pre_bb_num
	//find every bb in this module first and then traverse trace_list

	int f_count=0;
	for(Module::iterator MI = M.begin(), ME = M.end(); MI != ME; MI++)
	{
		Function *F = MI;
		char* function_name = (char*)malloc(60);
		strcpy(function_name, F->getName().str().c_str());
		int bb_count =0;
		for(Function::iterator FI = MI->begin(), FE = MI->end(); FI != FE; FI++)
		{	
			BasicBlock *BB = FI;
			char* bb_name = (char*)malloc(180);
			strcpy(bb_name, BB->getName().str().c_str());
			IRBuilder<> IRB(BB->getTerminator());
			//errs() << function_name << " " << bb_name << "\n";
			int type1 = -1, type2 = -1;
			std::vector<int> bb_num_vector;
			std::vector<unsigned long> time_vector;
			std::vector<int> bb_num_vector1;
			std::vector<int> visited_vector1;
			std::vector<int> bb_num_vector2;
			std::vector<double> average_vector2;
			std::vector<double> stdev_vector2;
			std::vector<double> b_vector3;
			std::vector<double> c_vector3;
			int context_type1_bb_num = -1;

			//obsolete
			//handle the ecall entry and exit
			/*if((strcmp(function_name, p_entry_function) == 0) && (strcmp(bb_name, "entry") == 0))
			{
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//LoadInst *last_time_load = IRB.CreateLoad(gv);
				//IRB.CreateStore(initial_value_int_zero, gv);


				//IRBuilder<> IRB1(BB->getFirstInsertionPt());
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//IRB1.CreateCall(instru_print_long_long_int_to_debug_f, load);


				//print for debugging
				//IRB.CreateCall(instru_print_int_to_debug_f, last_time_load);
				//IRB.CreateCall(instru_print_int_to_debug_f, load);

				//init timer thread at the beginning of ecall
				//clear earlier ecall records at the beginning of ecall
				IRBuilder<> IRB1(F->front().getFirstInsertionPt());
				IRB1.CreateCall(instru_init_f, initial_value_int_zero);
				//IRB1.CreateCall(instru_clear_record_f, initial_value_int_zero);


			}*/

			for(std::vector<struct trace_info>::iterator it = trace_list.begin() ; it != trace_list.end(); it++)
			{
				//check if this one is type1
				if((strcmp(it->context_type1_function_name, function_name) == 0) && (strcmp(it->context_type1_bb_name, bb_name) == 0))
				{
					type1 = 1;
					context_type1_bb_num = it->context_type1_bb_num;
				}
				//check if any type2 nodes is this one
				if((strcmp(it->function_name, function_name) == 0) && (strcmp(it->tail_type2_bb_name, bb_name) == 0))
				{
					type2 = 1;
					bb_num_vector.push_back(it->context_type1_bb_num);
					time_vector.push_back(it->bb_time);
				}
			}
			//instrument type2 first
			if(type2 == 1)
			{
				errs() << function_name << " " << bb_name << "\n";
				errs() << "type2!\n";
				//errs() << "size of vector: " << bb_num_vector.size();
				//for(std::vector<int>::iterator it = bb_num_vector.begin() ; it != bb_num_vector.end(); it++)
					//for(std::vector<unsigned long>::iterator itt = time_vector.begin() ; itt != time_vector.end(); itt++)
						//errs() << *it << " " << *itt << ", ";
				//errs() << "\n";
				//get average and stdev
				//copy bb_num_vector to bb_num_vector1, bb_num_vector1 works as a temp vector with UNIQUE values
				for(std::vector<int>::iterator it = bb_num_vector.begin() ; it != bb_num_vector.end(); it++)
				{
					int in_it = 0;
					for(std::vector<int>::iterator itt = bb_num_vector1.begin() ; itt != bb_num_vector1.end(); itt++)
						if(*it == *itt) in_it = 1;
					if(in_it == 0)bb_num_vector1.push_back(*it);
				}
				errs() << "size of vector: " << bb_num_vector1.size() << "\n";
				//initialize visited_vector1 as all 0;
				for(std::vector<int>::iterator it = bb_num_vector.begin() ; it != bb_num_vector.end(); it++)
					visited_vector1.push_back(0);
				//check each value in bb_num_vector1
				for(std::vector<int>::iterator it = bb_num_vector1.begin() ; it != bb_num_vector1.end(); it++)
				{
					int count = 0;
					double average = -1.0;
					double stdev = -1.0;
					std::vector<unsigned long> specific_vector;
					//process everyone in bb_num_vector that has such value
					std::vector<int>::iterator itt = bb_num_vector.begin();
					std::vector<int>::iterator ittt = visited_vector1.begin();
					std::vector<unsigned long>::iterator itttt = time_vector.begin();
					while(itt != bb_num_vector.end() && ittt != visited_vector1.end() && itttt != time_vector.end())
					{
						//if it is visited before, do not bother that
						if(*itt == *it && *ittt == 0)
						{
							//mark as visited
							*ittt = 1;
							count++;
							specific_vector.push_back(*itttt);
						}
						itt++;ittt++;itttt++;
					}
					//calculate average
					average = 0;
					for(std::vector<unsigned long>::iterator myit = specific_vector.begin() ; myit != specific_vector.end(); myit++)
						average += *myit;
					average /= count;
					//calculate stdev
					stdev = 0;
					//errs() << "data:\n";
					for(std::vector<unsigned long>::iterator myit = specific_vector.begin() ; myit != specific_vector.end(); myit++)
					{
						//errs() << *myit << " ";
						stdev = stdev + (*myit - average) * (*myit - average);
					}
					//errs() << "\ncount: " << count << "\n";
					stdev /= count;
					stdev = sqrt(stdev);
					//errs() << "stdev: " << stdev << "\n";
					bb_num_vector2.push_back(*it);
					average_vector2.push_back(average);
					stdev_vector2.push_back(stdev);
				}
				std::vector<int>::iterator myit = bb_num_vector2.begin();
				std::vector<double>::iterator myit1 = average_vector2.begin();
				std::vector<double>::iterator myit2 = stdev_vector2.begin();

				//print for debugging
				while(myit != bb_num_vector2.end() && myit1 != average_vector2.end() && myit2 != stdev_vector2.end())
				{
					errs() << "prior bb num: " << *myit << " average: " << *myit1 << " stdev: " << *myit2 << "\n";
					myit++; myit1++; myit2++;
				}



				//---------------------untransformed code----------------------------
				//get times
				Constant *str_para = createStringArg(function_name, F);
				str_para = createStringArg(bb_name, F);
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB.CreateLoad(gv);
				Value *curr = load;
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				LoadInst *last_time_load = IRB.CreateLoad(gv);
				IRB.CreateStore(load, gv);
				Value *detect_result_sub_inst = IRB.CreateSub(load, last_time_load);



				int vector_size = bb_num_vector2.size();
				int my_i;
				myit1 = average_vector2.begin();
				myit2 = stdev_vector2.begin();
				for(my_i = 0; my_i < vector_size; my_i++)
				{
					b_vector3.push_back(*myit1 - *myit2);
					c_vector3.push_back(*myit1 + page_fault_average - *myit2 - page_fault_stdev);
					myit1++; myit2++;
				}
				//print for debugging, b_vector3 and c_vector3
				std::vector<double>::iterator mybit = b_vector3.begin();
				std::vector<double>::iterator mycit = c_vector3.begin();
				while((mybit != b_vector3.end()) && (mycit != c_vector3.end()))
				{
					errs() << "b: " << *mybit << " c: " << *mycit << "\n";
					mybit++;mycit++;
				}
				gv = M.getGlobalVariable(StringRef("pre_bb_num"), true);
				load = IRB.CreateLoad(gv);
				myit = bb_num_vector2.begin();
				mybit = b_vector3.begin();
				mycit = c_vector3.begin();
				errs() << "***************************\n";
				if(vector_size == 1)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mybit_value_int = ConstantInt::get(I64Ty, *mybit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);
					Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
					Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
					Value *args[] = {load, detect_result_sub_inst, last_time_load, curr, myit_value_int, mybit_value_int, mycit_value_int, str_para1, str_para2};
					//IRB.CreateCall(instru_detect1_f, args);
				}
				else if(vector_size == 2)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mybit_value_int = ConstantInt::get(I64Ty, *mybit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);
					Constant *myit1_value_int = ConstantInt::get(I64Ty, *(myit+1));
					Constant *mybit1_value_int = ConstantInt::get(I64Ty, *(mybit+1));
					Constant *mycit1_value_int = ConstantInt::get(I64Ty, *(mycit+1));
					Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
					Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
					Value *args[] = {load, detect_result_sub_inst, last_time_load, curr, myit_value_int, mybit_value_int, mycit_value_int,
								myit1_value_int, mybit1_value_int, mycit1_value_int, str_para1, str_para2};
					//IRB.CreateCall(instru_detect2_f, args);
				}
				/*else if(vector_size == 3)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mybit_value_int = ConstantInt::get(I64Ty, *mybit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);
					Constant *myit1_value_int = ConstantInt::get(I64Ty, *(myit+1));
					Constant *mybit1_value_int = ConstantInt::get(I64Ty, *(mybit+1));
					Constant *mycit1_value_int = ConstantInt::get(I64Ty, *(mycit+1));
					Constant *myit2_value_int = ConstantInt::get(I64Ty, *(myit+2));
					Constant *mybit2_value_int = ConstantInt::get(I64Ty, *(mybit+2));
					Constant *mycit2_value_int = ConstantInt::get(I64Ty, *(mycit+2));
					Value *args[] = {load, detect_result_sub_inst, myit_value_int, mybit_value_int, mycit_value_int,
								myit1_value_int, mybit1_value_int, mycit1_value_int,
								myit2_value_int, mybit2_value_int, mycit2_value_int};
					IRB.CreateCall(instru_detect3_f, args);
				}*/


				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB.CreateLoad(gv);
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				IRB.CreateStore(load, gv);




				//-----------------------transformed code----------------------------
				/*
					---------		b1-->
					|	|		|
					|	|     =>	|	b2
					|	|		\/	|
					|	|			\/	
					---------		b3
				*/


				//transform

				//get times
				//in basic block b1
				/*Constant *str_para = createStringArg(function_name, F);
				str_para = createStringArg(bb_name, F);
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB.CreateLoad(gv);
				Value *curr = load;
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				LoadInst *last_time_load = IRB.CreateLoad(gv);
				IRB.CreateStore(load, gv);
				Value *detect_result_sub_inst = IRB.CreateSub(load, last_time_load);

				Value * cmpv = IRB.CreateICmpUGT(load, last_time_load);
				Value *mine_f = M.getOrInsertFunction("mine", VoidTy, I64Ty, nullptr);
			
				if(strcmp(function_name, "prog_init") == 0)
				{
					errs() << "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd\n";
					errs() << "F->getBasicBlockList().size(): " << F->getBasicBlockList().size() <<"\n";


				}*/

				/*if(//strcmp(function_name, "function_LHASH_COMP") != 0// && strcmp(function_name, "function_LHASH_HASH") != 0
					strcmp(function_name, "SortFnByName") != 0 && strcmp(function_name, "do_cmd") != 0
					&& BB->getInstList().size() >= 3)//&& strcmp(function_name, "lock_dbg_cb") != 0)// && strcmp(function_name, "main") != 0)*/
				/*if(BB->getInstList().size() >= 9 && strcmp(bb_name, "if.end1019") != 0 && strcmp(bb_name, "if.then25") != 0)//strcmp(function_name, "do_cmd") != 0)
				{
				Instruction *I1 = BB->getTerminator();
				//Instruction *nop = BinaryOperator::Create(Instruction::Add, initial_value_int_zero, initial_value_int_zero);
				CallInst * callv = CallInst::Create(mine_f, load);
				char name[100];
				strcpy(name, bb_name);
				strcat(name, "b3");
				BB->getInstList().insert(I1, callv);
				BasicBlock *newBB1 = BB->splitBasicBlock(callv, name);*/

				/*I1 = BB->getTerminator();
				nop = BinaryOperator::Create(Instruction::Add, initial_value_int_zero, initial_value_int_zero);
				BB->getInstList().insert(I1, nop);
				BasicBlock *newBB2 = BB->splitBasicBlock(nop, "newbasicblockb2");

				I1 = BB->getTerminator();
				BranchInst *bran1 = BranchInst::Create(newBB1, newBB2, cmpv);
				ReplaceInstWithInst(I1, bran1);*/
				//}
				





				



				/*int vector_size = bb_num_vector2.size();
				int my_i;
				myit1 = average_vector2.begin();
				myit2 = stdev_vector2.begin();
				for(my_i = 0; my_i < vector_size; my_i++)
				{
					b_vector3.push_back(*myit1 - *myit2);
					c_vector3.push_back(*myit1 + page_fault_average - *myit2 - page_fault_stdev);
					myit1++; myit2++;
				}
				//print for debugging, b_vector3 and c_vector3
				std::vector<double>::iterator mybit = b_vector3.begin();
				std::vector<double>::iterator mycit = c_vector3.begin();
				while((mybit != b_vector3.end()) && (mycit != c_vector3.end()))
				{
					errs() << "b: " << *mybit << " c: " << *mycit << "\n";
					mybit++;mycit++;
				}
				gv = M.getGlobalVariable(StringRef("pre_bb_num"), true);
				load = IRB.CreateLoad(gv);
				myit = bb_num_vector2.begin();
				mybit = b_vector3.begin();
				mycit = c_vector3.begin();
				errs() << "***************************\n";
				if(vector_size == 1)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mybit_value_int = ConstantInt::get(I64Ty, *mybit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);
					Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
					Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
					Value *args[] = {load, detect_result_sub_inst, last_time_load, curr, myit_value_int, mybit_value_int, mycit_value_int, str_para1, str_para2};
					IRBuilder<> IRB(BB->getTerminator());
					IRB.CreateCall(instru_detect1_f, args);
				}
				else if(vector_size == 2)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mybit_value_int = ConstantInt::get(I64Ty, *mybit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);
					Constant *myit1_value_int = ConstantInt::get(I64Ty, *(myit+1));
					Constant *mybit1_value_int = ConstantInt::get(I64Ty, *(mybit+1));
					Constant *mycit1_value_int = ConstantInt::get(I64Ty, *(mycit+1));
					Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
					Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
					Value *args[] = {load, detect_result_sub_inst, last_time_load, curr, myit_value_int, mybit_value_int, mycit_value_int,
								myit1_value_int, mybit1_value_int, mycit1_value_int, str_para1, str_para2};
					IRBuilder<> IRB(BB->getTerminator());
					IRB.CreateCall(instru_detect2_f, args);
				}*/
				/*else if(vector_size == 3)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mybit_value_int = ConstantInt::get(I64Ty, *mybit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);
					Constant *myit1_value_int = ConstantInt::get(I64Ty, *(myit+1));
					Constant *mybit1_value_int = ConstantInt::get(I64Ty, *(mybit+1));
					Constant *mycit1_value_int = ConstantInt::get(I64Ty, *(mycit+1));
					Constant *myit2_value_int = ConstantInt::get(I64Ty, *(myit+2));
					Constant *mybit2_value_int = ConstantInt::get(I64Ty, *(mybit+2));
					Constant *mycit2_value_int = ConstantInt::get(I64Ty, *(mycit+2));
					Value *args[] = {load, detect_result_sub_inst, myit_value_int, mybit_value_int, mycit_value_int,
								myit1_value_int, mybit1_value_int, mycit1_value_int,
								myit2_value_int, mybit2_value_int, mycit2_value_int};
					IRB.CreateCall(instru_detect3_f, args);
				}*/

				//in basic block b3
				/*IRBuilder<> IRB(newBB1->getTerminator());
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB.CreateLoad(gv);
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				IRB.CreateStore(load, gv);*/





			}
			if(type1 == 1)
			{
				//errs() << "type1!\n";
				//errs() << function_name << " " << bb_name << " " << context_type1_bb_num << "\n";
				Constant *bb_num_value = ConstantInt::get(I64Ty, context_type1_bb_num);
				gv = M.getGlobalVariable(StringRef("pre_bb_num"), true);
				IRB.CreateStore(bb_num_value, gv);//done.
			}

			//obsolete
			/*if((strcmp(function_name, p_entry_function) == 0) && (strcmp(bb_name, F->back().getName().str().c_str()) == 0))
			{
				//errs() << "F name: " << F->getName() << " " << "BB name: " << BB->getName() << "\n";
				IRB.CreateCall(instru_dump_detection_result_f, initial_value_int_one);
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB.CreateLoad(gv);
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				IRB.CreateStore(load, gv);
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB.CreateLoad(gv);
				//IRB.CreateCall(instru_print_long_long_int_to_debug_f, load);
			}*/

			free(bb_name);
			bb_num_vector.clear();
			time_vector.clear();
			bb_num_vector1.clear();
			visited_vector1.clear();
			bb_num_vector2.clear();
			average_vector2.clear();
			stdev_vector2.clear();
			b_vector3.clear();
			c_vector3.clear();
		}


		//handle ecall entry and exit
		if((strcmp(function_name, p_entry_function) == 0) && (M.getFunction(p_reference_function) != NULL))
		{
			//dump all detection timing infomation at the end of ecall
			BasicBlock *BB = &(F->back());
			BasicBlock::iterator BI, BE;
			for(BI = BB->begin(), BE = BB->end(); BI != BE; BI++)
			{
				Instruction *II = BI;
				if(isa<ReturnInst>(II) || isa<CallInst>(II)) break;
			}
			
			if(BI == BE)
			{
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "-----------found! ------------------------------------------1---------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";

				IRBuilder<> IRB1(F->back().getTerminator());
				//IRB1.CreateCall(instru_dump_detection_result_f, initial_value_int_zero);
				IRB1.CreateCall(instru_set_loop_false_f, initial_value_int_zero);

				//get time again after our time consuming process
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//IRB1.CreateStore(load, gv);



			}
			else
			{

			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "-----------found! ------------------------------------------2---------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";


				IRBuilder<> IRB1((Instruction *)BI);
				//IRB1.CreateCall(instru_dump_detection_result_f, initial_value_int_zero);
				IRB1.CreateCall(instru_set_loop_false_f, initial_value_int_zero);

				//get time again after our time consuming process
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//IRB1.CreateStore(load, gv);

			}




			//init timer thread at the beginning of ecall
			//clear earlier ecall records at the beginning of ecall
			IRBuilder<> IRB(F->front().getFirstInsertionPt());
			//IRB.CreateCall(instru_init_f, initial_value_int_zero);
			//IRB.CreateCall(instru_clear_record_f, initial_value_int_zero);
		}


		free(function_name);

	}
	
	trace_list.clear();







	}


	//----------------------Mode 7 for detection logic instrumentation---------------------------//

	//optimized for performance, copied from mode 6

	//optimized for performance, copied from mode 1

	if(mode == 7)
	{
	FILE *ttracefile;
	char ttracetemp[300];
	strcpy(ttracetemp, currentd);
	strcat(ttracetemp, "/ttracedata.txt");

	//if file does not exist
	if(access(ttracetemp, 0) == -1)
	{
	//-------------------processing tgdata.txt-----------------//
	//map for quick access
	llvm::StringMap<struct bb_num_s*> bbmap;

	int longest_f = 0, longest_bb = 0;

	//get global bb_num, type1, type2
	FILE *gbfile;
	char tgtemp3[300];
	strcpy(tgtemp3, currentd);
	strcat(tgtemp3, "/tgdata.txt");
	gbfile = fopen(tgtemp3, "r");
	if(gbfile)
	{
		char *line = NULL;
		size_t len = 0;
		ssize_t read;
		int count = 0;
		struct bb_num_s *ti;
		while((read = getline(&line, &len, gbfile)) != -1)
		{
			//leave out last character '\n'
			line[read-1] = '\0';
			if(count % 4 == 0)
			{
				//function name
				ti = (struct bb_num_s*) malloc (sizeof(struct bb_num_s));
				ti->function_name = (char *) malloc(300);
				strcpy(ti->function_name, line);
			}
			else if(count % 4 == 1)
			{
				//bb name
				ti->bb_name = (char *) malloc(300);
				strcpy(ti->bb_name, line);			
			}
			else if(count % 4 == 2)
			{
				//type1
				ti->type1 = atoi(line);
			}
			else if(count % 4 == 3)
			{
				//type2 and bb global num
				ti->type2 = atoi(line);
				ti->bb_num = (count - 3) / 4;
				bb_num_s_list.push_back(*ti);
				char temp[300];
				strcpy(temp, ti->function_name);
				strcat(temp, ti->bb_name);
				//errs() << temp << "\n";
				std::string tempstr(temp);
				//errs() << tempstr << "\n";
				bbmap[tempstr] = ti;
				//errs() << "ti->function_name: " << ti->function_name << "length:" << strlen(ti->function_name) << "\n";
				//if(strlen(ti->function_name) > longest_f) longest_f = strlen(ti->function_name);
				//if(strlen(ti->bb_name) > longest_bb) longest_bb = strlen(ti->bb_name);
			}

			
			count++;
		}
		fclose(gbfile);
	}
	else
	{
		errs() << "Timed Execution Configration Error: We should have a global basic block file.\n";
		exit(-1);
	}

	/*errs() << "longest function name: " << longest_f << "\n";
	errs() << "longest bb name: " << longest_bb << "\n";

	if(M.getFunction("CRYPTO_num_locks") != NULL)
	{
	FILE *ttfile;
	char tgtemp[120];
	strcpy(tgtemp, currentd);
	strcat(tgtemp, "/my3.txt");
	ttfile = fopen(tgtemp, "a");
	fprintf(ttfile, "%d\n%d\n", longest_f, longest_bb);
	fclose(ttfile);
	}*/

	/*struct bb_num_s* mapt = bbmap["EVP_CIPHER_CTX_freeEVP_CIPHER_CTX_cleanup.exit"];
	if(mapt == NULL) errs() << "mapt == NULL\n";
	else errs() << "the data found in maps is: " << "function name: " << mapt->function_name << "bb name: " 
		<< mapt->bb_name << "bb num: " << mapt->bb_num << "type1 flag: " << mapt->type1 
		<< "type2 flag: " << mapt->type2 << "\n";*/

	/*if(M.getFunction("ecall_DoNumSort") != NULL)
	{
	for(std::vector<struct bb_num_s>::iterator it = bb_num_s_list.begin() ; it != bb_num_s_list.end(); ++it)
	{
		FILE *file;
		char tgtemp[120];
		strcpy(tgtemp, currentd);
		strcat(tgtemp, "/my.txt");
		file = fopen(tgtemp, "a");
		//printf("%s\n",str);
		//fprintf(file, "%s\n%s\n%lu\n", function_name, bb_name, t);
		fprintf(file, "%s\n%s\n%d\n%d\n%d\n", it->function_name, it->bb_name, it->bb_num, it->type1, it->type2);
		fclose(file);
	}
	}
	bb_num_s_list.clear();*/




	//-------------------processing tdata.txt ttdata.txt-----------------//

	FILE *datafile, *tracefile;
	char tgtemp1[300];
	strcpy(tgtemp1, currentd);
	strcat(tgtemp1, "/tdata.txt");
	char tgtemp2[300];
	strcpy(tgtemp2, currentd);
	strcat(tgtemp2, "/ttdata.txt");
	datafile = fopen(tgtemp1,"r");
	tracefile = fopen(tgtemp2,"r");
	if(datafile)
	{
		if(tracefile)
		{
			char *line1 = NULL;
			size_t len1 = 0;
			ssize_t read1;
			int count1 = 0;
			char *line2 = NULL;
			size_t len2 = 0;
			ssize_t read2;
			int count2 = 0;
			char *line3= NULL;
			size_t len3 = 0;
			ssize_t read3;

			while (((read1 = getline(&line1, &len1, datafile)) != -1) 
				&& ((read2 = getline(&line2, &len2, tracefile)) != -1)
				&& ((read3 = getline(&line3, &len3, tracefile)) != -1))
			{
				//leave out last character '\n'
				line1[read1-1] = '\0';
				line2[read2-1] = '\0';
				line3[read3-1] = '\0';
				struct training_info *ti = (struct training_info*) malloc (sizeof(struct training_info));
				ti->bb_time = atoi(line1);
				ti->function_name = (char *) malloc(300);
				ti->bb_name = (char *) malloc(300);
				strcpy(ti->function_name, line2);
				strcpy(ti->bb_name, line3);
				char temp[300];
				strcpy(temp, ti->function_name);
				strcat(temp, ti->bb_name);
				struct bb_num_s* mapt = bbmap[temp];
				//if(mapt == NULL) errs() << "mapt == NULL\n";
				//else errs() << "the data found in maps is: " << "function name: " << mapt->function_name 
					//<< "bb name: " << mapt->bb_name << "bb num: " << mapt->bb_num << "type1 flag: " 
					//<< mapt->type1 << "type2 flag: " << mapt->type2 << "\n";
				if(mapt == NULL)
				{
					errs() << "--------------- mapt == NULL ----------------\n";
					FILE *file;
					char tgtemp[120];
					strcpy(tgtemp, currentd);
					strcat(tgtemp, "/my2.txt");
					file = fopen(tgtemp, "a");
					fprintf(file, "%s\n%s\n", ti->function_name, ti->bb_name);
					fclose(file);
					ti->bb_num = -1;
					ti->type1 = -1;
					ti->type2 = -1;
				}
				else
				{
					ti->bb_num = mapt->bb_num;
					ti->type1 = mapt->type1;
					ti->type2 = mapt->type2;
				}
				info_list.push_back(*ti);
			}
			fclose(datafile);
			fclose(tracefile);
		}
		else
		{
			errs() << "Timed Execution Configration Error: We should have a trace file.\n";
			exit(-1);
		}
	}
	else
	{
		errs() << "Timed Execution Configration Error: We should have a data file.\n";
		exit(-1);
	}
	bbmap.clear();
	bb_num_s_list.clear();


	/*if(M.getFunction("ecall_DoNumSort") != NULL)
	{
	for(std::vector<struct training_info>::iterator trit = info_list.begin() ; trit != info_list.end(); ++trit)
	{
		FILE *file;
		char tgtemp[120];
		strcpy(tgtemp, currentd);
		strcat(tgtemp, "/my1.txt");
		file = fopen(tgtemp, "a");
		//printf("%s\n",str);
		//fprintf(file, "%s\n%s\n%lu\n", function_name, bb_name, t);
		fprintf(file, "%s\n%s\n%d\n%d\n%d\n%d\n", trit->function_name, trit->bb_name, trit->bb_time, trit->bb_num, trit->type1, trit->type2);
		fclose(file);

	}
	}*/
	//info_list.clear();




	/*obsolete
	//mark trace nodes type1 and type2
	//mark bb_num
	for(std::vector<struct bb_num_s>::iterator it = bb_num_s_list.begin() ; it != bb_num_s_list.end(); ++it)
	{
		markBBNumType1Type2Info(it->function_name, it->bb_name, it->bb_num, it->type1, it->type2);
	}

	if(M.getFunction("CRYPTO_num_locks") != NULL)
	{
	printMark(M);
	}*/


	//process trace
	//collect trace info from trainging info
	//backwards in training info list
	int need_type1_bb_num = 0;
	struct trace_info *ti;
	for(std::vector<struct training_info>::iterator it = info_list.end() - 1; it >= info_list.begin(); it--)
	{
		if(need_type1_bb_num)
		{
			ti->context_type1_function_name = (char *) malloc(60);
			strcpy(ti->context_type1_function_name, it->function_name);
			ti->context_type1_bb_name = (char *) malloc(60);
			strcpy(ti->context_type1_bb_name, it->bb_name);
			ti->context_type1_bb_num = it->bb_num;
			trace_list.push_back(*ti);
			need_type1_bb_num = 0;
		}
		if(it->type2 == 1)// && it != info_list.begin())
		{
			ti = (struct trace_info*) malloc (sizeof(struct trace_info));
			ti->function_name = (char *) malloc(60);
			strcpy(ti->function_name, it->function_name);
			ti->tail_type2_bb_name = (char *) malloc(60);
			strcpy(ti->tail_type2_bb_name, it->bb_name);
			ti->bb_time = it->bb_time;
			need_type1_bb_num = 1;
			//special handling for the entry of the ecall
			if(it == info_list.begin())
			{
				ti->context_type1_function_name = (char *) malloc(60);
				strcpy(ti->context_type1_function_name, " ");
				ti->context_type1_bb_name = (char *) malloc(60);
				strcpy(ti->context_type1_bb_name, " ");
				ti->context_type1_bb_num = -1;
				trace_list.push_back(*ti);
			}
		}
	}

	//print for debugging
	/*if(M.getFunction("ecall_DoNumSort") != NULL)
	{
	for(std::vector<struct trace_info>::iterator it = trace_list.begin() ; it != trace_list.end(); it++)
	{
		FILE *file;
		char tgtemp[120];
		strcpy(tgtemp, currentd);
		strcat(tgtemp, "/my4.txt");
		file = fopen(tgtemp, "a");
		//fprintf(file, "%s\n%s\n%d\n%d\n%d\n%d\n", it->function_name, it->bb_name, it->bb_num, it->bb_time, it->type1, it->type2);
		
		//if(strcmp(M.getModuleIdentifier().c_str(), MAINFILE) == 0)
			fprintf(file, "%s\n%s\n%s\n%s\n%d\n%lu\n", 
				it->function_name, it->tail_type2_bb_name, it->context_type1_function_name, it->context_type1_bb_name, it->context_type1_bb_num, it->bb_time);
		
		fclose(file);
	}
	}

	//print for debugging
	int t2_count = 0;
	for(std::vector<struct training_info>::iterator it = info_list.end() - 1; it >= info_list.begin(); it--)
	{
		if(it->type2 == 1) t2_count++;
		//printf("%d\n", t2_count);
	}
	printf("t2_count: %d\n", t2_count);*/

	info_list.clear();

	//save to file
	for(std::vector<struct trace_info>::iterator it = trace_list.begin() ; it != trace_list.end(); it++)
	{
		//errs() << "save to file\n";
		FILE *file;
		char tgtemp[120];
		strcpy(tgtemp, currentd);
		strcat(tgtemp, "/ttracedata.txt");
		file = fopen(tgtemp, "a");
			fprintf(file, "%s\n%s\n%s\n%s\n%d\n%lu\n", 
				it->function_name, it->tail_type2_bb_name, it->context_type1_function_name, it->context_type1_bb_name, it->context_type1_bb_num, it->bb_time);
		fclose(file);
	}
	}
	//file exists
	else
	{
	//errs() << "ttracedata.txt exists.\n";
	FILE *gbfile;
	char tgtemp3[300];
	strcpy(tgtemp3, currentd);
	strcat(tgtemp3, "/ttracedata.txt");
	gbfile = fopen(tgtemp3, "r");
	if(gbfile)
	{
		char *line = NULL;
		size_t len = 0;
		ssize_t read;
		int count = 0;
		struct trace_info *ti;
		while((read = getline(&line, &len, gbfile)) != -1)
		{
			//leave out last character '\n'
			line[read-1] = '\0';
			//errs() << "line: " << line << "\n";
			if(count % 6 == 0)
			{
				//function name
				ti = (struct trace_info*) malloc (sizeof(struct trace_info));
				ti->function_name = (char *) malloc(300);
				strcpy(ti->function_name, line);
			}
			else if(count % 6 == 1)
			{
				//type2 bb name
				ti->tail_type2_bb_name = (char *) malloc(300);
				strcpy(ti->tail_type2_bb_name, line);			
			}
			else if(count % 6 == 2)
			{
				//context type1 function name
				ti->context_type1_function_name = (char *) malloc(300);
				strcpy(ti->context_type1_function_name, line);			
			}
			else if(count % 6 == 3)
			{
				//context type1 bb name
				ti->context_type1_bb_name = (char *) malloc(300);
				strcpy(ti->context_type1_bb_name, line);			
			}
			else if(count % 6 == 4)
			{
				//context type1 bb num
				ti->context_type1_bb_num = atoi(line);
			}
			else if(count % 6 == 5)
			{
				//type2 and bb global num
				ti->bb_time = atoi(line);

				//errs() << "ti->context_type1_function_name: " << ti->context_type1_function_name << "\n";
				//errs() << "ti->context_type1_bb_name: " << ti->context_type1_bb_name << "\n";

				trace_list.push_back(*ti);
			}
			count++;
		}
		fclose(gbfile);
	}
	else
	{
		errs() << "Timed Execution Configration Error: We should have a processed trace file.\n";
		exit(-1);
	}

	}


	//instrument type1 nodes
	//type1 nodes put its bb_num to global variable pre_bb_num
	//find every bb in this module first and then traverse trace_list

	int f_count=0;
	for(Module::iterator MI = M.begin(), ME = M.end(); MI != ME; MI++)
	{
		Function *F = MI;
		char* function_name = (char*)malloc(60);
		strcpy(function_name, F->getName().str().c_str());
		int bb_count =0;
		for(Function::iterator FI = MI->begin(), FE = MI->end(); FI != FE; FI++)
		{	
			BasicBlock *BB = FI;
			char* bb_name = (char*)malloc(180);
			strcpy(bb_name, BB->getName().str().c_str());
			IRBuilder<> IRB(BB->getTerminator());
			//errs() << function_name << " " << bb_name << "\n";
			int type1 = -1, type2 = -1;
			std::vector<int> bb_num_vector;
			std::vector<unsigned long> time_vector;
			std::vector<int> bb_num_vector1;
			std::vector<int> visited_vector1;
			std::vector<int> bb_num_vector2;
			std::vector<double> average_vector2;
			std::vector<double> stdev_vector2;
			std::vector<double> b_vector3;
			std::vector<double> c_vector3;
			int context_type1_bb_num = -1;

			//obsolete
			//handle the ecall entry and exit
			/*if((strcmp(function_name, p_entry_function) == 0) && (strcmp(bb_name, "entry") == 0))
			{
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//LoadInst *last_time_load = IRB.CreateLoad(gv);
				//IRB.CreateStore(initial_value_int_zero, gv);


				//IRBuilder<> IRB1(BB->getFirstInsertionPt());
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//IRB1.CreateCall(instru_print_long_long_int_to_debug_f, load);


				//print for debugging
				//IRB.CreateCall(instru_print_int_to_debug_f, last_time_load);
				//IRB.CreateCall(instru_print_int_to_debug_f, load);

				//init timer thread at the beginning of ecall
				//clear earlier ecall records at the beginning of ecall
				IRBuilder<> IRB1(F->front().getFirstInsertionPt());
				IRB1.CreateCall(instru_init_f, initial_value_int_zero);
				//IRB1.CreateCall(instru_clear_record_f, initial_value_int_zero);


			}*/

			//errs() << "trace_list.size(): " << trace_list.size() << "\n";
			for(std::vector<struct trace_info>::iterator it = trace_list.begin() ; it != trace_list.end(); it++)
			{
				//errs() << "it->context_type1_function_name: " << it->context_type1_function_name << "\n";
				//errs() << "it->context_type1_bb_name: " << it->context_type1_bb_name << "\n";
				//check if this one is type1
				if((strcmp(it->context_type1_function_name, function_name) == 0) && (strcmp(it->context_type1_bb_name, bb_name) == 0))
				{
					type1 = 1;
					context_type1_bb_num = it->context_type1_bb_num;
				}
				//check if any type2 nodes is this one
				if((strcmp(it->function_name, function_name) == 0) && (strcmp(it->tail_type2_bb_name, bb_name) == 0))
				{
					type2 = 1;
					//errs() << "type2: " << function_name << " " << bb_name << "\n";
					bb_num_vector.push_back(it->context_type1_bb_num);
					time_vector.push_back(it->bb_time);
				}
			}
			//instrument type2 first
			if(type2 == 1)
			{

				//errs() << function_name << " " << bb_name << "\n";
				errs() << "type2!\n";
				//errs() << "size of vector: " << bb_num_vector.size();
				//for(std::vector<int>::iterator it = bb_num_vector.begin() ; it != bb_num_vector.end(); it++)
					//for(std::vector<unsigned long>::iterator itt = time_vector.begin() ; itt != time_vector.end(); itt++)
						//errs() << *it << " " << *itt << ", ";
				//errs() << "\n";
				//get average and stdev
				//copy bb_num_vector to bb_num_vector1, bb_num_vector1 works as a temp vector with UNIQUE values
				for(std::vector<int>::iterator it = bb_num_vector.begin() ; it != bb_num_vector.end(); it++)
				{
					int in_it = 0;
					for(std::vector<int>::iterator itt = bb_num_vector1.begin() ; itt != bb_num_vector1.end(); itt++)
						if(*it == *itt) in_it = 1;
					if(in_it == 0)bb_num_vector1.push_back(*it);
				}
				errs() << "size of vector: " << bb_num_vector1.size() << "\n";
				//initialize visited_vector1 as all 0;
				for(std::vector<int>::iterator it = bb_num_vector.begin() ; it != bb_num_vector.end(); it++)
					visited_vector1.push_back(0);
				//check each value in bb_num_vector1
				for(std::vector<int>::iterator it = bb_num_vector1.begin() ; it != bb_num_vector1.end(); it++)
				{
					int count = 0;
					double average = -1.0;
					double stdev = -1.0;
					std::vector<unsigned long> specific_vector;
					//process everyone in bb_num_vector that has such value
					std::vector<int>::iterator itt = bb_num_vector.begin();
					std::vector<int>::iterator ittt = visited_vector1.begin();
					std::vector<unsigned long>::iterator itttt = time_vector.begin();
					while(itt != bb_num_vector.end() && ittt != visited_vector1.end() && itttt != time_vector.end())
					{
						//if it is visited before, do not bother that
						if(*itt == *it && *ittt == 0)
						{
							//mark as visited
							*ittt = 1;
							count++;
							specific_vector.push_back(*itttt);
						}
						itt++;ittt++;itttt++;
					}
					//calculate average
					average = 0;
					for(std::vector<unsigned long>::iterator myit = specific_vector.begin() ; myit != specific_vector.end(); myit++)
						average += *myit;
					average /= count;
					//calculate stdev
					stdev = 0;
					//errs() << "data:\n";
					for(std::vector<unsigned long>::iterator myit = specific_vector.begin() ; myit != specific_vector.end(); myit++)
					{
						//errs() << *myit << " ";
						stdev = stdev + (*myit - average) * (*myit - average);
					}
					//errs() << "\ncount: " << count << "\n";
					stdev /= count;
					stdev = sqrt(stdev);
					//errs() << "stdev: " << stdev << "\n";
					bb_num_vector2.push_back(*it);
					average_vector2.push_back(average);
					stdev_vector2.push_back(stdev);
				}
				std::vector<int>::iterator myit = bb_num_vector2.begin();
				std::vector<double>::iterator myit1 = average_vector2.begin();
				std::vector<double>::iterator myit2 = stdev_vector2.begin();

				//print for debugging
				while(myit != bb_num_vector2.end() && myit1 != average_vector2.end() && myit2 != stdev_vector2.end())
				{
					errs() << "prior bb num: " << *myit << " average: " << *myit1 << " stdev: " << *myit2 << "\n";
					myit++; myit1++; myit2++;
				}


				errs() << "**************************************************type2!\n";



				//transform structure
				/*//Value *mine_f = M.getOrInsertFunction("mine", VoidTy, I64Ty, nullptr);
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB.CreateLoad(gv);
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				LoadInst *lload = IRB.CreateLoad(gv);

				TerminatorInst *I1 = BB->getTerminator();
				Instruction *nop = BinaryOperator::Create(Instruction::Add, initial_value_int_zero, initial_value_int_zero);
				BB->getInstList().insert(I1, nop);
				BasicBlock *newBB1 = BB->splitBasicBlock(nop, "newbasicblock2");

				I1 = BB->getTerminator();
				nop = BinaryOperator::Create(Instruction::Add, initial_value_int_zero, initial_value_int_zero);
				//CallInst *callv = CallInst::Create(mine_f, initial_value_int_zero);
				BB->getInstList().insert(I1, nop);
				BasicBlock *newBB2 = BB->splitBasicBlock(nop, "newbasicblock3");

				I1 = BB->getTerminator();
				//Value * cmpv = IRB.CreateICmpUGT(lload, load);
				BranchInst *bran1 = BranchInst::Create(newBB1, newBB2, CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_EQ, lload, load, "compare", I1));
				ReplaceInstWithInst(I1, bran1);*///

				//add instructions
				//add to BB, that is, kind of front
				IRBuilder<> IRB1(BB->getTerminator());
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB1.CreateLoad(gv);
				Value *curr = load;
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				LoadInst *last_time_load = IRB1.CreateLoad(gv);
				IRB1.CreateStore(load, gv);
				Value *detect_result_sub_inst = IRB1.CreateSub(load, last_time_load);

				int vector_size = bb_num_vector2.size();
				int my_i;
				myit1 = average_vector2.begin();
				myit2 = stdev_vector2.begin();
				for(my_i = 0; my_i < vector_size; my_i++)
				{
					b_vector3.push_back(*myit1 - *myit2);
					c_vector3.push_back(*myit1 + page_fault_average - *myit2 - page_fault_stdev);
					myit1++; myit2++;
				}

				//errs() << "page_fault_average: " << page_fault_average << "page_fault_stdev: " << page_fault_stdev << "\n";

				//print for debugging, b_vector3 and c_vector3
				std::vector<double>::iterator mybit = b_vector3.begin();
				std::vector<double>::iterator mycit = c_vector3.begin();
				while((mybit != b_vector3.end()) && (mycit != c_vector3.end()))
				{
					errs() << "b: " << *mybit << " c: " << *mycit << "\n";
					mybit++;mycit++;
				}
				gv = M.getGlobalVariable(StringRef("pre_bb_num"), true);
				load = IRB1.CreateLoad(gv);
				myit = bb_num_vector2.begin();
				mybit = b_vector3.begin();
				mycit = c_vector3.begin();
				//if(*mycit < 3) printf("*mycit: %lf\n", *mycit);


				/*//if(vector_size == 1)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);

					//compare load and myit_value_int
					I1 = BB->getTerminator();
					CmpInst *cmp1 = CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_EQ, load, myit_value_int, "compare1", I1);
					CmpInst *cmp2 = CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_SGT, detect_result_sub_inst, mycit_value_int, "compare2", I1);

					//Instruction *myand = BinaryOperator::Create(Instruction::And, cmp1, cmp2);
					//CmpInst *cmp3 = CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_EQ, myand, initial_value_int_one, "compare3", I1);
					BranchInst *bran1 = BranchInst::Create(newBB2, newBB1, cmp2);
					ReplaceInstWithInst(I1, bran1);

				}
				else if(vector_size == 2)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);
					Constant *myit1_value_int = ConstantInt::get(I64Ty, *(myit+1));
					Constant *mycit1_value_int = ConstantInt::get(I64Ty, *(mycit+1));

					I1 = BB->getTerminator();
					CmpInst *cmp1 = CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_SGT, detect_result_sub_inst, mycit_value_int, "compare1", I1);
					CmpInst *cmp2 = CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_SGT, detect_result_sub_inst, mycit1_value_int, "compare2", I1);
					CmpInst *cmp3 = CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_EQ, cmp1, cmp2, "compare3", I1);
					CmpInst *cmp4 = CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_EQ, cmp1, cmp3, "compare4", I1);
					CmpInst *cmp5 = CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_EQ, cmp2, cmp4, "compare4", I1);

					BranchInst *bran1 = BranchInst::Create(newBB1, newBB2, cmp5);
					ReplaceInstWithInst(I1, bran1);

				}*///




				//add to newBB2, that is, the middle
				if(vector_size == 1)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, (int)*myit);
					Constant *mybit_value_int = ConstantInt::get(I64Ty, (int)*mybit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, (int)*mycit);


					//Constant *mybit_value_double = ConstantFP::get(DoubleTy, *mybit);
					//Constant *mycit_value_double = ConstantFP::get(DoubleTy, *mycit);



					//errs() << "*mycit: " << *mycit << "\n";
					Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
					Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
					Value *args[] = {load, detect_result_sub_inst, last_time_load, curr, myit_value_int, mybit_value_int, mycit_value_int, str_para1, str_para2};
					//Value *args[] = {load, detect_result_sub_inst, last_time_load, curr, myit_value_int, mybit_value_double, mycit_value_double, str_para1, str_para2};

					//IRBuilder<> IRB(newBB2->getTerminator());
					IRBuilder<> IRB(BB->getTerminator());
					IRB.CreateCall(instru_detect1_f, args);
				}
				else if(vector_size == 2)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mybit_value_int = ConstantInt::get(I64Ty, *mybit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);
					Constant *myit1_value_int = ConstantInt::get(I64Ty, *(myit+1));
					Constant *mybit1_value_int = ConstantInt::get(I64Ty, *(mybit+1));
					Constant *mycit1_value_int = ConstantInt::get(I64Ty, *(mycit+1));
					Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
					Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
					Value *args[] = {load, detect_result_sub_inst, last_time_load, curr, myit_value_int, mybit_value_int, mycit_value_int,
								myit1_value_int, mybit1_value_int, mycit1_value_int, str_para1, str_para2};
					//IRBuilder<> IRB(newBB2->getTerminator());
					IRBuilder<> IRB(BB->getTerminator());
					IRB.CreateCall(instru_detect2_f, args);
				}
				else if(vector_size == 3)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mybit_value_int = ConstantInt::get(I64Ty, *mybit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);
					Constant *myit1_value_int = ConstantInt::get(I64Ty, *(myit+1));
					Constant *mybit1_value_int = ConstantInt::get(I64Ty, *(mybit+1));
					Constant *mycit1_value_int = ConstantInt::get(I64Ty, *(mycit+1));
					Constant *myit2_value_int = ConstantInt::get(I64Ty, *(myit+2));
					Constant *mybit2_value_int = ConstantInt::get(I64Ty, *(mybit+2));
					Constant *mycit2_value_int = ConstantInt::get(I64Ty, *(mycit+2));
					Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
					Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
					Value *args[] = {load, detect_result_sub_inst, last_time_load, curr, myit_value_int, mybit_value_int, mycit_value_int,
								myit1_value_int, mybit1_value_int, mycit1_value_int,
								myit2_value_int, mybit2_value_int, mycit2_value_int, str_para1, str_para2};
					//IRBuilder<> IRB(newBB2->getTerminator());
					IRBuilder<> IRB(BB->getTerminator());
					IRB.CreateCall(instru_detect3_f, args);
				}
				else if(vector_size == 4)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mybit_value_int = ConstantInt::get(I64Ty, *mybit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);
					Constant *myit1_value_int = ConstantInt::get(I64Ty, *(myit+1));
					Constant *mybit1_value_int = ConstantInt::get(I64Ty, *(mybit+1));
					Constant *mycit1_value_int = ConstantInt::get(I64Ty, *(mycit+1));
					Constant *myit2_value_int = ConstantInt::get(I64Ty, *(myit+2));
					Constant *mybit2_value_int = ConstantInt::get(I64Ty, *(mybit+2));
					Constant *mycit2_value_int = ConstantInt::get(I64Ty, *(mycit+2));
					Constant *myit3_value_int = ConstantInt::get(I64Ty, *(myit+3));
					Constant *mybit3_value_int = ConstantInt::get(I64Ty, *(mybit+3));
					Constant *mycit3_value_int = ConstantInt::get(I64Ty, *(mycit+3));
					Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
					Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
					Value *args[] = {load, detect_result_sub_inst, last_time_load, curr, myit_value_int, mybit_value_int, mycit_value_int,
								myit1_value_int, mybit1_value_int, mycit1_value_int,
								myit2_value_int, mybit2_value_int, mycit2_value_int,
								myit3_value_int, mybit3_value_int, mycit3_value_int, str_para1, str_para2};
					//IRBuilder<> IRB(newBB2->getTerminator());
					IRBuilder<> IRB(BB->getTerminator());
					IRB.CreateCall(instru_detect4_f, args);
				}


				Constant *myit_value_int = ConstantInt::get(I64Ty, 1);
				Constant *mybit_value_int = ConstantInt::get(I64Ty, 2);
				Constant *mycit_value_int = ConstantInt::get(I64Ty, 3);
				Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
				Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
				Value *args[] = {myit_value_int, myit_value_int, myit_value_int, myit_value_int, myit_value_int, mybit_value_int, mycit_value_int, str_para1, str_para2};
				////IRBuilder<> IRB2(newBB2->getTerminator());
				//IRB2.CreateCall(instru_detect1_f, args);



				//add to newBB1, that is, the end
				////IRBuilder<> IRB3(newBB1->getTerminator());
				IRBuilder<> IRB3(BB->getTerminator());
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB3.CreateLoad(gv);
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				IRB3.CreateStore(load, gv);



			}


			if(type1 == 1)
			{
				//errs() << "type1!\n";
				//errs() << function_name << " " << bb_name << " " << context_type1_bb_num << "\n";
				Constant *bb_num_value = ConstantInt::get(I64Ty, context_type1_bb_num);
				gv = M.getGlobalVariable(StringRef("pre_bb_num"), true);
				IRBuilder<> IRB(BB->getTerminator());
				IRB.CreateStore(bb_num_value, gv);//done.
			}

			//obsolete
			/*if((strcmp(function_name, p_entry_function) == 0) && (strcmp(bb_name, F->back().getName().str().c_str()) == 0))
			{
				//errs() << "F name: " << F->getName() << " " << "BB name: " << BB->getName() << "\n";
				IRB.CreateCall(instru_dump_detection_result_f, initial_value_int_one);
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB.CreateLoad(gv);
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				IRB.CreateStore(load, gv);
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB.CreateLoad(gv);
				//IRB.CreateCall(instru_print_long_long_int_to_debug_f, load);
			}*/

			free(bb_name);
			bb_num_vector.clear();
			time_vector.clear();
			bb_num_vector1.clear();
			visited_vector1.clear();
			bb_num_vector2.clear();
			average_vector2.clear();
			stdev_vector2.clear();
			b_vector3.clear();
			c_vector3.clear();

		}

		//handle ecall entry and exit
		if((strcmp(function_name, p_entry_function) == 0) && (M.getFunction(p_reference_function) != NULL))
		{
			//dump all detection timing infomation at the end of ecall
			BasicBlock *BB = &(F->back());
			BasicBlock::iterator BI, BE;
			for(BI = BB->begin(), BE = BB->end(); BI != BE; BI++)
			{
				Instruction *II = BI;
				if(isa<ReturnInst>(II)) break; //|| isa<CallInst>(II)) break;
			}

			if(BI == BE)
			{
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "-----------found! ------------------------------------------1---------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";

				IRBuilder<> IRB1(F->back().getTerminator());


				//IRB1.CreateCall(instru_print_time_f, initial_value_int_zero);
				IRB1.CreateCall(instru_dump_detection_result_f, initial_value_int_zero);
				IRB1.CreateCall(instru_set_loop_false_f, initial_value_int_zero);

				//get time again after our time consuming process
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//IRB1.CreateStore(load, gv);



			}
			else
			{

			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "-----------found! ------------------------------------------2---------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";


				IRBuilder<> IRB1((Instruction *)BI);
				errs() << "2\n";
				//IRB1.CreateCall(instru_print_time_f, initial_value_int_zero);
				IRB1.CreateCall(instru_dump_detection_result_f, initial_value_int_zero);
				IRB1.CreateCall(instru_set_loop_false_f, initial_value_int_zero);

				//get time again after our time consuming process
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//IRB1.CreateStore(load, gv);

			}




			//init timer thread at the beginning of ecall
			//clear earlier ecall records at the beginning of ecall
			IRBuilder<> IRB(F->front().getFirstInsertionPt());
			//IRB.CreateCall(instru_init_f, initial_value_int_zero);
			//IRB.CreateCall(instru_print_time_f, initial_value_int_zero);
			//IRB.CreateCall(instru_clear_record_f, initial_value_int_zero);
		}



	}


	}


	//----------------------Mode 8 for detection logic instrumentation---------------------------//

	//for performance evaluation, clean clang, copied from mode 7


	if(mode == 8)
	{
		for(Module::iterator MI = M.begin(), ME = M.end(); MI != ME; MI++)
		{
		Function *F = MI;
		char* function_name = (char*)malloc(60);
		strcpy(function_name, F->getName().str().c_str());
		//handle ecall entry and exit
		if((strcmp(function_name, p_entry_function) == 0) && (M.getFunction(p_reference_function) != NULL))
		{
			//dump all detection timing infomation at the end of ecall
			BasicBlock *BB = &(F->back());
			BasicBlock::iterator BI, BE;
			for(BI = BB->begin(), BE = BB->end(); BI != BE; BI++)
			{
				Instruction *II = BI;
				if(isa<ReturnInst>(II) || isa<CallInst>(II)) break;
			}
			
			if(BI == BE)
			{
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "-----------found! ------------------------------------------1---------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";

				IRBuilder<> IRB1(F->back().getTerminator());
				//IRB1.CreateCall(instru_print_time_f, initial_value_int_zero);
				//IRB1.CreateCall(instru_dump_detection_result_f, initial_value_int_zero);
				//IRB1.CreateCall(instru_set_loop_false_f, initial_value_int_zero);

				//get time again after our time consuming process
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//IRB1.CreateStore(load, gv);



			}
			else
			{

			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "-----------found! ------------------------------------------2---------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";


				IRBuilder<> IRB1((Instruction *)BI);
				//IRB1.CreateCall(instru_print_time_f, initial_value_int_zero);
				//IRB1.CreateCall(instru_dump_detection_result_f, initial_value_int_zero);
				//IRB1.CreateCall(instru_set_loop_false_f, initial_value_int_zero);

				//get time again after our time consuming process
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//IRB1.CreateStore(load, gv);

			}




			//init timer thread at the beginning of ecall
			//clear earlier ecall records at the beginning of ecall
			IRBuilder<> IRB(F->front().getFirstInsertionPt());
			//IRB.CreateCall(instru_init_f, initial_value_int_zero);
			//IRB.CreateCall(instru_print_time_f, initial_value_int_zero);
			//IRB.CreateCall(instru_clear_record_f, initial_value_int_zero);
		}

		}

	}



	//----------------------Mode 9 for detection logic instrumentation with various factor---------------------------//

	//optimized for performance, copied from mode 7


	if(mode == 9)
	{
	errs() << "tfactor -----> " << tfactor << "\n";

	FILE *ttracefile;
	char ttracetemp[300];
	strcpy(ttracetemp, currentd);
	strcat(ttracetemp, "/ttracedata.txt");

	//if file does not exist
	if(access(ttracetemp, 0) == -1)
	{
	//-------------------processing tgdata.txt-----------------//
	//map for quick access
	llvm::StringMap<struct bb_num_s*> bbmap;

	int longest_f = 0, longest_bb = 0;

	//get global bb_num, type1, type2
	FILE *gbfile;
	char tgtemp3[300];
	strcpy(tgtemp3, currentd);
	strcat(tgtemp3, "/tgdata.txt");
	gbfile = fopen(tgtemp3, "r");
	if(gbfile)
	{
		char *line = NULL;
		size_t len = 0;
		ssize_t read;
		int count = 0;
		struct bb_num_s *ti;
		while((read = getline(&line, &len, gbfile)) != -1)
		{
			//leave out last character '\n'
			line[read-1] = '\0';
			if(count % 4 == 0)
			{
				//function name
				ti = (struct bb_num_s*) malloc (sizeof(struct bb_num_s));
				ti->function_name = (char *) malloc(300);
				strcpy(ti->function_name, line);
			}
			else if(count % 4 == 1)
			{
				//bb name
				ti->bb_name = (char *) malloc(300);
				strcpy(ti->bb_name, line);			
			}
			else if(count % 4 == 2)
			{
				//type1
				ti->type1 = atoi(line);
			}
			else if(count % 4 == 3)
			{
				//type2 and bb global num
				ti->type2 = atoi(line);
				ti->bb_num = (count - 3) / 4;
				bb_num_s_list.push_back(*ti);
				char temp[300];
				strcpy(temp, ti->function_name);
				strcat(temp, ti->bb_name);
				//errs() << temp << "\n";
				std::string tempstr(temp);
				//errs() << tempstr << "\n";
				bbmap[tempstr] = ti;
				//errs() << "ti->function_name: " << ti->function_name << "length:" << strlen(ti->function_name) << "\n";
				//if(strlen(ti->function_name) > longest_f) longest_f = strlen(ti->function_name);
				//if(strlen(ti->bb_name) > longest_bb) longest_bb = strlen(ti->bb_name);
			}

			
			count++;
		}
		fclose(gbfile);
	}
	else
	{
		errs() << "Timed Execution Configration Error: We should have a global basic block file.\n";
		exit(-1);
	}

	/*errs() << "longest function name: " << longest_f << "\n";
	errs() << "longest bb name: " << longest_bb << "\n";

	if(M.getFunction("CRYPTO_num_locks") != NULL)
	{
	FILE *ttfile;
	char tgtemp[120];
	strcpy(tgtemp, currentd);
	strcat(tgtemp, "/my3.txt");
	ttfile = fopen(tgtemp, "a");
	fprintf(ttfile, "%d\n%d\n", longest_f, longest_bb);
	fclose(ttfile);
	}*/

	/*struct bb_num_s* mapt = bbmap["EVP_CIPHER_CTX_freeEVP_CIPHER_CTX_cleanup.exit"];
	if(mapt == NULL) errs() << "mapt == NULL\n";
	else errs() << "the data found in maps is: " << "function name: " << mapt->function_name << "bb name: " 
		<< mapt->bb_name << "bb num: " << mapt->bb_num << "type1 flag: " << mapt->type1 
		<< "type2 flag: " << mapt->type2 << "\n";*/

	/*if(M.getFunction("CRYPTO_num_locks") != NULL)
	{
	for(std::vector<struct bb_num_s>::iterator it = bb_num_s_list.begin() ; it != bb_num_s_list.end(); ++it)
	{
		FILE *file;
		char tgtemp[120];
		strcpy(tgtemp, currentd);
		strcat(tgtemp, "/my.txt");
		file = fopen(tgtemp, "a");
		//printf("%s\n",str);
		//fprintf(file, "%s\n%s\n%lu\n", function_name, bb_name, t);
		fprintf(file, "%s\n%s\n%d\n%d\n%d\n", it->function_name, it->bb_name, it->bb_num, it->type1, it->type2);
		fclose(file);
	}
	}
	bb_num_s_list.clear();*/




	//-------------------processing tdata.txt ttdata.txt-----------------//

	FILE *datafile, *tracefile;
	char tgtemp1[300];
	strcpy(tgtemp1, currentd);
	strcat(tgtemp1, "/tdata.txt");
	char tgtemp2[300];
	strcpy(tgtemp2, currentd);
	strcat(tgtemp2, "/ttdata.txt");
	datafile = fopen(tgtemp1,"r");
	tracefile = fopen(tgtemp2,"r");
	if(datafile)
	{
		if(tracefile)
		{
			char *line1 = NULL;
			size_t len1 = 0;
			ssize_t read1;
			int count1 = 0;
			char *line2 = NULL;
			size_t len2 = 0;
			ssize_t read2;
			int count2 = 0;
			char *line3= NULL;
			size_t len3 = 0;
			ssize_t read3;

			while (((read1 = getline(&line1, &len1, datafile)) != -1) 
				&& ((read2 = getline(&line2, &len2, tracefile)) != -1)
				&& ((read3 = getline(&line3, &len3, tracefile)) != -1))
			{
				//leave out last character '\n'
				line1[read1-1] = '\0';
				line2[read2-1] = '\0';
				line3[read3-1] = '\0';
				struct training_info *ti = (struct training_info*) malloc (sizeof(struct training_info));
				ti->bb_time = atoi(line1);
				ti->function_name = (char *) malloc(300);
				ti->bb_name = (char *) malloc(300);
				strcpy(ti->function_name, line2);
				strcpy(ti->bb_name, line3);
				char temp[300];
				strcpy(temp, ti->function_name);
				strcat(temp, ti->bb_name);
				struct bb_num_s* mapt = bbmap[temp];
				//if(mapt == NULL) errs() << "mapt == NULL\n";
				//else errs() << "the data found in maps is: " << "function name: " << mapt->function_name 
					//<< "bb name: " << mapt->bb_name << "bb num: " << mapt->bb_num << "type1 flag: " 
					//<< mapt->type1 << "type2 flag: " << mapt->type2 << "\n";
				if(mapt == NULL)
				{
					errs() << "--------------- mapt == NULL ----------------\n";
					FILE *file;
					char tgtemp[120];
					strcpy(tgtemp, currentd);
					strcat(tgtemp, "/my2.txt");
					file = fopen(tgtemp, "a");
					fprintf(file, "%s\n%s\n", ti->function_name, ti->bb_name);
					fclose(file);
					ti->bb_num = -1;
					ti->type1 = -1;
					ti->type2 = -1;
				}
				else
				{
					ti->bb_num = mapt->bb_num;
					ti->type1 = mapt->type1;
					ti->type2 = mapt->type2;
				}
				info_list.push_back(*ti);
			}
			fclose(datafile);
			fclose(tracefile);
		}
		else
		{
			errs() << "Timed Execution Configration Error: We should have a trace file.\n";
			exit(-1);
		}
	}
	else
	{
		errs() << "Timed Execution Configration Error: We should have a data file.\n";
		exit(-1);
	}
	bbmap.clear();
	bb_num_s_list.clear();


	/*if(M.getFunction("CRYPTO_num_locks") != NULL)
	{
	for(std::vector<struct training_info>::iterator trit = info_list.begin() ; trit != info_list.end(); ++trit)
	{
		FILE *file;
		char tgtemp[120];
		strcpy(tgtemp, currentd);
		strcat(tgtemp, "/my1.txt");
		file = fopen(tgtemp, "a");
		//printf("%s\n",str);
		//fprintf(file, "%s\n%s\n%lu\n", function_name, bb_name, t);
		fprintf(file, "%s\n%s\n%d\n%d\n%d\n%d\n", trit->function_name, trit->bb_name, trit->bb_time, trit->bb_num, trit->type1, trit->type2);
		fclose(file);

	}
	}*/
	//info_list.clear();




	/*obsolete
	//mark trace nodes type1 and type2
	//mark bb_num
	for(std::vector<struct bb_num_s>::iterator it = bb_num_s_list.begin() ; it != bb_num_s_list.end(); ++it)
	{
		markBBNumType1Type2Info(it->function_name, it->bb_name, it->bb_num, it->type1, it->type2);
	}

	if(M.getFunction("CRYPTO_num_locks") != NULL)
	{
	printMark(M);
	}*/


	//process trace
	//collect trace info from trainging info
	//backwards in training info list
	int need_type1_bb_num = 0;
	struct trace_info *ti;
	for(std::vector<struct training_info>::iterator it = info_list.end() - 1; it >= info_list.begin(); it--)
	{
		if(need_type1_bb_num)
		{
			ti->context_type1_function_name = (char *) malloc(60);
			strcpy(ti->context_type1_function_name, it->function_name);
			ti->context_type1_bb_name = (char *) malloc(60);
			strcpy(ti->context_type1_bb_name, it->bb_name);
			ti->context_type1_bb_num = it->bb_num;
			trace_list.push_back(*ti);
			need_type1_bb_num = 0;
		}
		if(it->type2 == 1)// && it != info_list.begin())
		{
			ti = (struct trace_info*) malloc (sizeof(struct trace_info));
			ti->function_name = (char *) malloc(60);
			strcpy(ti->function_name, it->function_name);
			ti->tail_type2_bb_name = (char *) malloc(60);
			strcpy(ti->tail_type2_bb_name, it->bb_name);
			ti->bb_time = it->bb_time;
			need_type1_bb_num = 1;
			//special handling for the entry of the ecall
			if(it == info_list.begin())
			{
				ti->context_type1_function_name = (char *) malloc(60);
				strcpy(ti->context_type1_function_name, " ");
				ti->context_type1_bb_name = (char *) malloc(60);
				strcpy(ti->context_type1_bb_name, " ");
				ti->context_type1_bb_num = -1;
				trace_list.push_back(*ti);
			}
		}
	}

	//print for debugging
	/*if(M.getFunction("CRYPTO_num_locks") != NULL)
	{
	for(std::vector<struct trace_info>::iterator it = trace_list.begin() ; it != trace_list.end(); it++)
	{
		FILE *file;
		char tgtemp[120];
		strcpy(tgtemp, currentd);
		strcat(tgtemp, "/my4.txt");
		file = fopen(tgtemp, "a");
		//fprintf(file, "%s\n%s\n%d\n%d\n%d\n%d\n", it->function_name, it->bb_name, it->bb_num, it->bb_time, it->type1, it->type2);
		
		//if(strcmp(M.getModuleIdentifier().c_str(), MAINFILE) == 0)
			fprintf(file, "%s\n%s\n%s\n%s\n%d\n%lu\n", 
				it->function_name, it->tail_type2_bb_name, it->context_type1_function_name, it->context_type1_bb_name, it->context_type1_bb_num, it->bb_time);
		
		fclose(file);
	}
	}

	//print for debugging
	int t2_count = 0;
	for(std::vector<struct training_info>::iterator it = info_list.end() - 1; it >= info_list.begin(); it--)
	{
		if(it->type2 == 1) t2_count++;
		//printf("%d\n", t2_count);
	}
	printf("t2_count: %d\n", t2_count);*/

	info_list.clear();

	//save to file
	for(std::vector<struct trace_info>::iterator it = trace_list.begin() ; it != trace_list.end(); it++)
	{
		//errs() << "save to file\n";
		FILE *file;
		char tgtemp[120];
		strcpy(tgtemp, currentd);
		strcat(tgtemp, "/ttracedata.txt");
		file = fopen(tgtemp, "a");
			fprintf(file, "%s\n%s\n%s\n%s\n%d\n%lu\n", 
				it->function_name, it->tail_type2_bb_name, it->context_type1_function_name, it->context_type1_bb_name, it->context_type1_bb_num, it->bb_time);
		fclose(file);
	}
	}
	//file exists
	else
	{
	FILE *gbfile;
	char tgtemp3[300];
	strcpy(tgtemp3, currentd);
	strcat(tgtemp3, "/ttracedata.txt");
	gbfile = fopen(tgtemp3, "r");
	if(gbfile)
	{
		char *line = NULL;
		size_t len = 0;
		ssize_t read;
		int count = 0;
		struct trace_info *ti;
		while((read = getline(&line, &len, gbfile)) != -1)
		{
			//leave out last character '\n'
			line[read-1] = '\0';
			if(count % 4 == 0)
			{
				//function name
				ti = (struct trace_info*) malloc (sizeof(struct trace_info));
				ti->function_name = (char *) malloc(300);
				strcpy(ti->function_name, line);
			}
			else if(count % 4 == 1)
			{
				//type2 bb name
				ti->tail_type2_bb_name = (char *) malloc(300);
				strcpy(ti->tail_type2_bb_name, line);			
			}
			else if(count % 4 == 2)
			{
				//context type1 function name
				ti->context_type1_function_name = (char *) malloc(300);
				strcpy(ti->context_type1_function_name, line);			
			}
			else if(count % 4 == 3)
			{
				//context type1 bb name
				ti->context_type1_bb_name = (char *) malloc(300);
				strcpy(ti->context_type1_bb_name, line);			
			}
			else if(count % 4 == 4)
			{
				//context type1 bb num
				ti->context_type1_bb_num = atoi(line);
			}
			else if(count % 4 == 5)
			{
				//type2 and bb global num
				ti->bb_time = atoi(line);
				trace_list.push_back(*ti);
			}
			count++;
		}
		fclose(gbfile);
	}
	else
	{
		errs() << "Timed Execution Configration Error: We should have a processed trace file.\n";
		exit(-1);
	}

	}


	//instrument type1 nodes
	//type1 nodes put its bb_num to global variable pre_bb_num
	//find every bb in this module first and then traverse trace_list

	int f_count=0;
	for(Module::iterator MI = M.begin(), ME = M.end(); MI != ME; MI++)
	{
		Function *F = MI;
		char* function_name = (char*)malloc(60);
		strcpy(function_name, F->getName().str().c_str());
		int bb_count =0;
		for(Function::iterator FI = MI->begin(), FE = MI->end(); FI != FE; FI++)
		{	
			BasicBlock *BB = FI;
			char* bb_name = (char*)malloc(180);
			strcpy(bb_name, BB->getName().str().c_str());
			IRBuilder<> IRB(BB->getTerminator());
			//errs() << function_name << " " << bb_name << "\n";
			int type1 = -1, type2 = -1;
			std::vector<int> bb_num_vector;
			std::vector<unsigned long> time_vector;
			std::vector<int> bb_num_vector1;
			std::vector<int> visited_vector1;
			std::vector<int> bb_num_vector2;
			std::vector<double> average_vector2;
			std::vector<double> stdev_vector2;
			std::vector<double> b_vector3;
			std::vector<double> c_vector3;
			int context_type1_bb_num = -1;

			//obsolete
			//handle the ecall entry and exit
			/*if((strcmp(function_name, p_entry_function) == 0) && (strcmp(bb_name, "entry") == 0))
			{
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//LoadInst *last_time_load = IRB.CreateLoad(gv);
				//IRB.CreateStore(initial_value_int_zero, gv);


				//IRBuilder<> IRB1(BB->getFirstInsertionPt());
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//IRB1.CreateCall(instru_print_long_long_int_to_debug_f, load);


				//print for debugging
				//IRB.CreateCall(instru_print_int_to_debug_f, last_time_load);
				//IRB.CreateCall(instru_print_int_to_debug_f, load);

				//init timer thread at the beginning of ecall
				//clear earlier ecall records at the beginning of ecall
				IRBuilder<> IRB1(F->front().getFirstInsertionPt());
				IRB1.CreateCall(instru_init_f, initial_value_int_zero);
				//IRB1.CreateCall(instru_clear_record_f, initial_value_int_zero);


			}*/

			for(std::vector<struct trace_info>::iterator it = trace_list.begin() ; it != trace_list.end(); it++)
			{
				//check if this one is type1
				if((strcmp(it->context_type1_function_name, function_name) == 0) && (strcmp(it->context_type1_bb_name, bb_name) == 0))
				{
					type1 = 1;
					context_type1_bb_num = it->context_type1_bb_num;
				}
				//check if any type2 nodes is this one
				if((strcmp(it->function_name, function_name) == 0) && (strcmp(it->tail_type2_bb_name, bb_name) == 0))
				{
					type2 = 1;
					bb_num_vector.push_back(it->context_type1_bb_num);
					time_vector.push_back(it->bb_time);
				}
			}
			//instrument type2 first
			if(type2 == 1)
			{

				errs() << function_name << " " << bb_name << "\n";
				errs() << "type2!\n";
				//errs() << "size of vector: " << bb_num_vector.size();
				//for(std::vector<int>::iterator it = bb_num_vector.begin() ; it != bb_num_vector.end(); it++)
					//for(std::vector<unsigned long>::iterator itt = time_vector.begin() ; itt != time_vector.end(); itt++)
						//errs() << *it << " " << *itt << ", ";
				//errs() << "\n";
				//get average and stdev
				//copy bb_num_vector to bb_num_vector1, bb_num_vector1 works as a temp vector with UNIQUE values
				for(std::vector<int>::iterator it = bb_num_vector.begin() ; it != bb_num_vector.end(); it++)
				{
					int in_it = 0;
					for(std::vector<int>::iterator itt = bb_num_vector1.begin() ; itt != bb_num_vector1.end(); itt++)
						if(*it == *itt) in_it = 1;
					if(in_it == 0)bb_num_vector1.push_back(*it);
				}
				errs() << "size of vector: " << bb_num_vector1.size() << "\n";
				//initialize visited_vector1 as all 0;
				for(std::vector<int>::iterator it = bb_num_vector.begin() ; it != bb_num_vector.end(); it++)
					visited_vector1.push_back(0);
				//check each value in bb_num_vector1
				for(std::vector<int>::iterator it = bb_num_vector1.begin() ; it != bb_num_vector1.end(); it++)
				{
					int count = 0;
					double average = -1.0;
					double stdev = -1.0;
					std::vector<unsigned long> specific_vector;
					//process everyone in bb_num_vector that has such value
					std::vector<int>::iterator itt = bb_num_vector.begin();
					std::vector<int>::iterator ittt = visited_vector1.begin();
					std::vector<unsigned long>::iterator itttt = time_vector.begin();
					while(itt != bb_num_vector.end() && ittt != visited_vector1.end() && itttt != time_vector.end())
					{
						//if it is visited before, do not bother that
						if(*itt == *it && *ittt == 0)
						{
							//mark as visited
							*ittt = 1;
							count++;
							specific_vector.push_back(*itttt);
						}
						itt++;ittt++;itttt++;
					}
					//calculate average
					average = 0;
					for(std::vector<unsigned long>::iterator myit = specific_vector.begin() ; myit != specific_vector.end(); myit++)
						average += *myit;
					average /= count;
					//calculate stdev
					stdev = 0;
					//errs() << "data:\n";
					for(std::vector<unsigned long>::iterator myit = specific_vector.begin() ; myit != specific_vector.end(); myit++)
					{
						//errs() << *myit << " ";
						stdev = stdev + (*myit - average) * (*myit - average);
					}
					//errs() << "\ncount: " << count << "\n";
					stdev /= count;
					stdev = sqrt(stdev);
					//errs() << "stdev: " << stdev << "\n";
					bb_num_vector2.push_back(*it);
					average_vector2.push_back(average);
					stdev_vector2.push_back(stdev);
				}
				std::vector<int>::iterator myit = bb_num_vector2.begin();
				std::vector<double>::iterator myit1 = average_vector2.begin();
				std::vector<double>::iterator myit2 = stdev_vector2.begin();

				//print for debugging
				while(myit != bb_num_vector2.end() && myit1 != average_vector2.end() && myit2 != stdev_vector2.end())
				{
					errs() << "prior bb num: " << *myit << " average: " << *myit1 << " stdev: " << *myit2 << "\n";
					myit++; myit1++; myit2++;
				}


				errs() << "**************************************************type2!\n";
			
				//transform structure
				Value *mine_f = M.getOrInsertFunction("mine", VoidTy, I64Ty, nullptr);
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB.CreateLoad(gv);
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				LoadInst *lload = IRB.CreateLoad(gv);

				TerminatorInst *I1 = BB->getTerminator();
				Instruction *nop = BinaryOperator::Create(Instruction::Add, initial_value_int_zero, initial_value_int_zero);
				BB->getInstList().insert(I1, nop);
				BasicBlock *newBB1 = BB->splitBasicBlock(nop, "newbasicblock2");

				I1 = BB->getTerminator();
				nop = BinaryOperator::Create(Instruction::Add, initial_value_int_zero, initial_value_int_zero);
				//CallInst *callv = CallInst::Create(mine_f, initial_value_int_zero);
				BB->getInstList().insert(I1, nop);
				BasicBlock *newBB2 = BB->splitBasicBlock(nop, "newbasicblock3");

				I1 = BB->getTerminator();
				//Value * cmpv = IRB.CreateICmpUGT(lload, load);
				BranchInst *bran1 = BranchInst::Create(newBB1, newBB2, CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_EQ, lload, load, "compare", I1));
				ReplaceInstWithInst(I1, bran1);

				//add instructions
				//add to BB, that is, kind of front
				IRBuilder<> IRB1(BB->getTerminator());
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB1.CreateLoad(gv);
				Value *curr = load;
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				LoadInst *last_time_load = IRB1.CreateLoad(gv);
				IRB1.CreateStore(load, gv);
				Value *detect_result_sub_inst = IRB1.CreateSub(load, last_time_load);

				int vector_size = bb_num_vector2.size();
				int my_i;
				myit1 = average_vector2.begin();
				myit2 = stdev_vector2.begin();
				for(my_i = 0; my_i < vector_size; my_i++)
				{
					b_vector3.push_back(*myit1 - *myit2);
					c_vector3.push_back((*myit1 + page_fault_average - *myit2 - page_fault_stdev) * tfactor);
					myit1++; myit2++;
				}
				//print for debugging, b_vector3 and c_vector3
				std::vector<double>::iterator mybit = b_vector3.begin();
				std::vector<double>::iterator mycit = c_vector3.begin();
				while((mybit != b_vector3.end()) && (mycit != c_vector3.end()))
				{
					errs() << "b: " << *mybit << " c: " << *mycit << "\n";
					mybit++;mycit++;
				}
				gv = M.getGlobalVariable(StringRef("pre_bb_num"), true);
				load = IRB1.CreateLoad(gv);
				myit = bb_num_vector2.begin();
				mybit = b_vector3.begin();
				mycit = c_vector3.begin();


				if(vector_size == 1)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);

					//compare load and myit_value_int
					I1 = BB->getTerminator();
					CmpInst *cmp1 = CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_EQ, load, myit_value_int, "compare1", I1);
					CmpInst *cmp2 = CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_SGT, detect_result_sub_inst, mycit_value_int, "compare2", I1);

					//Instruction *myand = BinaryOperator::Create(Instruction::And, cmp1, cmp2);
					//CmpInst *cmp3 = CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_EQ, myand, initial_value_int_one, "compare3", I1);
					BranchInst *bran1 = BranchInst::Create(newBB2, newBB1, cmp2);
					ReplaceInstWithInst(I1, bran1);

				}
				else if(vector_size == 2)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);
					Constant *myit1_value_int = ConstantInt::get(I64Ty, *(myit+1));
					Constant *mycit1_value_int = ConstantInt::get(I64Ty, *(mycit+1));

					I1 = BB->getTerminator();
					CmpInst *cmp1 = CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_SGT, detect_result_sub_inst, mycit_value_int, "compare1", I1);
					CmpInst *cmp2 = CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_SGT, detect_result_sub_inst, mycit1_value_int, "compare2", I1);
					CmpInst *cmp3 = CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_EQ, cmp1, cmp2, "compare3", I1);
					CmpInst *cmp4 = CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_EQ, cmp1, cmp3, "compare4", I1);
					CmpInst *cmp5 = CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_EQ, cmp2, cmp4, "compare4", I1);

					BranchInst *bran1 = BranchInst::Create(newBB1, newBB2, cmp5);
					ReplaceInstWithInst(I1, bran1);

				}




				//add to newBB2, that is, the middle
				if(vector_size == 1)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mybit_value_int = ConstantInt::get(I64Ty, *mybit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);
					Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
					Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
					Value *args[] = {load, detect_result_sub_inst, last_time_load, curr, myit_value_int, mybit_value_int, mycit_value_int, str_para1, str_para2};
					IRBuilder<> IRB(newBB2->getTerminator());
					//IRB.CreateCall(instru_detect1_f, args);
				}
				else if(vector_size == 2)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mybit_value_int = ConstantInt::get(I64Ty, *mybit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);
					Constant *myit1_value_int = ConstantInt::get(I64Ty, *(myit+1));
					Constant *mybit1_value_int = ConstantInt::get(I64Ty, *(mybit+1));
					Constant *mycit1_value_int = ConstantInt::get(I64Ty, *(mycit+1));
					Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
					Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
					Value *args[] = {load, detect_result_sub_inst, last_time_load, curr, myit_value_int, mybit_value_int, mycit_value_int,
								myit1_value_int, mybit1_value_int, mycit1_value_int, str_para1, str_para2};
					IRBuilder<> IRB(newBB2->getTerminator());
					//IRB.CreateCall(instru_detect2_f, args);
				}




				Constant *myit_value_int = ConstantInt::get(I64Ty, 1);
				Constant *mybit_value_int = ConstantInt::get(I64Ty, 2);
				Constant *mycit_value_int = ConstantInt::get(I64Ty, 3);
				Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
				Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
				Value *args[] = {myit_value_int, myit_value_int, myit_value_int, myit_value_int, myit_value_int, mybit_value_int, mycit_value_int, str_para1, str_para2};
				IRBuilder<> IRB2(newBB2->getTerminator());
				//IRB2.CreateCall(instru_detect1_f, args);



				//add to newBB1, that is, the end
				IRBuilder<> IRB3(newBB1->getTerminator());
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB3.CreateLoad(gv);
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				IRB3.CreateStore(load, gv);



			}


			if(type1 == 1)
			{
				//errs() << "type1!\n";
				//errs() << function_name << " " << bb_name << " " << context_type1_bb_num << "\n";
				Constant *bb_num_value = ConstantInt::get(I64Ty, context_type1_bb_num);
				gv = M.getGlobalVariable(StringRef("pre_bb_num"), true);
				IRBuilder<> IRB(BB->getTerminator());
				IRB.CreateStore(bb_num_value, gv);//done.
			}

			//obsolete
			/*if((strcmp(function_name, p_entry_function) == 0) && (strcmp(bb_name, F->back().getName().str().c_str()) == 0))
			{
				//errs() << "F name: " << F->getName() << " " << "BB name: " << BB->getName() << "\n";
				IRB.CreateCall(instru_dump_detection_result_f, initial_value_int_one);
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB.CreateLoad(gv);
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				IRB.CreateStore(load, gv);
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB.CreateLoad(gv);
				//IRB.CreateCall(instru_print_long_long_int_to_debug_f, load);
			}*/

			free(bb_name);
			bb_num_vector.clear();
			time_vector.clear();
			bb_num_vector1.clear();
			visited_vector1.clear();
			bb_num_vector2.clear();
			average_vector2.clear();
			stdev_vector2.clear();
			b_vector3.clear();
			c_vector3.clear();

		}


		//handle ecall entry and exit
		if((strcmp(function_name, p_entry_function) == 0) && (M.getFunction(p_reference_function) != NULL))
		{
			//dump all detection timing infomation at the end of ecall
			BasicBlock *BB = &(F->back());
			BasicBlock::iterator BI, BE;
			for(BI = BB->begin(), BE = BB->end(); BI != BE; BI++)
			{
				Instruction *II = BI;
				if(isa<ReturnInst>(II) || isa<CallInst>(II)) break;
			}
			
			if(BI == BE)
			{
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "-----------found! ------------------------------------------1---------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";

				IRBuilder<> IRB1(F->back().getTerminator());
				//IRB1.CreateCall(instru_print_time_f, initial_value_int_zero);
				//IRB1.CreateCall(instru_dump_detection_result_f, initial_value_int_zero);
				IRB1.CreateCall(instru_set_loop_false_f, initial_value_int_zero);

				//get time again after our time consuming process
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//IRB1.CreateStore(load, gv);



			}
			else
			{

			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "-----------found! ------------------------------------------2---------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";


				IRBuilder<> IRB1((Instruction *)BI);
				//IRB1.CreateCall(instru_print_time_f, initial_value_int_zero);
				//IRB1.CreateCall(instru_dump_detection_result_f, initial_value_int_zero);
				IRB1.CreateCall(instru_set_loop_false_f, initial_value_int_zero);

				//get time again after our time consuming process
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//IRB1.CreateStore(load, gv);

			}




			//init timer thread at the beginning of ecall
			//clear earlier ecall records at the beginning of ecall
			IRBuilder<> IRB(F->front().getFirstInsertionPt());
			//IRB.CreateCall(instru_init_f, initial_value_int_zero);
			//IRB.CreateCall(instru_print_time_f, initial_value_int_zero);
			//IRB.CreateCall(instru_clear_record_f, initial_value_int_zero);
		}



	}


	}

	//----------------------Mode 10 for global type 1 and type 2 info ---------------------------//
	/**
		copied from type -1
		needs compile and run
		generate ./tgdata.txt, ./ttdata
		./tgdata.txt : each entry: function name, basic block name, 
				whether this basic block is type1, whether this basic block is type2
				yes: 1, no: -1
				generated when compiling
		./ttdata.txt : program trace, each entry: function name, basic block name
				generated when running
	*/

	if(mode ==10)
	{
	int f_count=0;
	int t1 = 0, t2 = 0, t0 = 0, t3 = 0, tb = 0;



	//global bb num
	for(Module::iterator MI = M.begin(), ME = M.end(); MI != ME; MI++)
	{
		Function *F = MI;
		//errs() << F->getName() << "\n";

		for(Function::iterator FI = MI->begin(), FE = MI->end(); FI != FE; FI++)
		{	
			BasicBlock *BB = FI;
			int num_pred = 0;
			for(pred_iterator PI = pred_begin(BB), E = pred_end(BB); PI != E; PI++)
				num_pred++;
			int has_return_inst = 0;
			for(BasicBlock::iterator BI = FI->begin(), BE = FI->end(); BI != BE; BI++)
			{
				Instruction *II = BI;
				if(isa<ReturnInst>(II))
				{
					has_return_inst = 1;
				}
			}
			int type1 = -1, type2 = -1;

			if((num_pred > 1) || (strcmp(BB->getName().str().c_str(), "entry") == 0) || has_return_inst)
			{
				type2 = 1;
				t2++;
			}

			for(succ_iterator SI = succ_begin(BB), E = succ_end(BB); SI != E; SI++)
			{
				BasicBlock *BBB = *SI;
				int num_pred = 0;
				for(pred_iterator PI = pred_begin(BBB), E = pred_end(BBB); PI != E; PI++)
					num_pred++;
				int has_return_inst = 0;
				for(BasicBlock::iterator BI = SI->begin(), BE = SI->end(); BI != BE; BI++)
				{
					Instruction *II = BI;
					if(isa<ReturnInst>(II))
					{
						has_return_inst = 1;
					}
				}
				if((num_pred > 1) || (strcmp(BBB->getName().str().c_str(), "entry") == 0) || has_return_inst)
				{
					type1 = 1;
					t1++;
				}
			}

			if(type1 == -1 && type2 == -1) t0++;
			else if(type1 == 1 && type2 == 1) t3++;


			tb++;


		}

	}



	FILE *file1;
	char tgtemp1[300];
	strcpy(tgtemp1, currentd);
	strcat(tgtemp1, "/tt1.txt");
	file1 = fopen(tgtemp1, "a");
	fprintf(file1, "%d\n",t1);
	fclose(file1);

	FILE *file2;
	char tgtemp2[300];
	strcpy(tgtemp2, currentd);
	strcat(tgtemp2, "/tt2.txt");
	file2 = fopen(tgtemp2, "a");
	fprintf(file2, "%d\n",t2);
	fclose(file2);

	FILE *file3;
	char tgtemp3[300];
	strcpy(tgtemp3, currentd);
	strcat(tgtemp3, "/tt3.txt");
	file3 = fopen(tgtemp3, "a");
	fprintf(file3, "%d\n",t3);
	fclose(file3);

	FILE *file0;
	char tgtemp0[300];
	strcpy(tgtemp0, currentd);
	strcat(tgtemp0, "/tt0.txt");
	file0 = fopen(tgtemp0, "a");
	fprintf(file0, "%d\n",t0);
	fclose(file0);


	FILE *fileb;
	char tgtempb[300];
	strcpy(tgtempb, currentd);
	strcat(tgtempb, "/ttb.txt");
	fileb = fopen(tgtempb, "a");
	fprintf(fileb, "%d\n",tb);
	fclose(fileb);


	}


	//----------------------Mode 11 for delta t ---------------------------//
	/**
		copied from Mode 0

		needs compile and run
		generate: ./tdata.txt, ./tidata.txt
		./tdata.txt : 
				generated when running
		./ttdata.txt : program trace, each entry: function name, basic block name
				generated when running
		./tidata.txt : for debug, contains interrupt flag number
				generated when running
	*/

	if(mode ==11)
	{
	int f_count=0;

	for(Module::iterator MI = M.begin(), ME = M.end(); MI != ME; MI++)
	{
		Function *F = MI;
		//if(strstr((char *)F->getName().str().c_str(), "instrument_function") != NULL)errs() << F->getName() << "\n";

		int bb_count =0;
		for(Function::iterator FI = MI->begin(), FE = MI->end(); FI != FE; FI++)
		{	
			//get insert point: the end of the basic block
			BasicBlock *BB = FI;
			IRBuilder<> IRB(BB->getTerminator());
			//errs() << BB->getName() << "\n";
			int num_pred = 0;
			for(pred_iterator PI = pred_begin(BB), E = pred_end(BB); PI != E; PI++)
				num_pred++;

			int num_succ = 0;
			for(succ_iterator SI = succ_begin(BB), E = succ_end(BB); SI != E; SI++)
				num_succ++;
			int has_return_inst = 0;
			for(BasicBlock::iterator BI = FI->begin(), BE = FI->end(); BI != BE; BI++)
			{
				Instruction *II = BI;
				if(isa<ReturnInst>(II))
				{
					has_return_inst = 1;
				}
			}

			//type 2 nodes
			if((num_pred > 1) || (strcmp(BB->getName().str().c_str(), "entry") == 0) || has_return_inst)
			{

				IRB.CreateCall(instru_get_time_f, initial_value_int_zero);

				//get time before our time consuming process
				/*gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB.CreateLoad(gv);
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				LoadInst *last_time_load = IRB.CreateLoad(gv);
				IRB.CreateStore(load, gv);

				Value *sub = IRB.CreateSub(load, last_time_load);

				Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
				Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);

				Value *args[] = {str_para1, str_para2, sub};
				//insert record
				//IRB.CreateCall(instru_insert_record_f, args);

				//get time again after our time consuming process
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB.CreateLoad(gv);
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				IRB.CreateStore(load, gv);*/
			}

			else
			{
				//insert a -1 value
				Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
				Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
				Value *args[] = {str_para1, str_para2, initial_value_int_minus_one};
				//IRB.CreateCall(instru_insert_record_f, args);
			}
			bb_count++;

		}

		if((strcmp(F->getName().str().c_str(), p_entry_function) == 0) && (M.getFunction(p_reference_function) != NULL))
		{
			//dump all timing infomation at the end of ecall
			//IRBuilder<> IRB1(F->back().getTerminator());
			//IRB1.CreateCall(instru_dump_result_f, initial_value_int_zero);
			BasicBlock *BB = &(F->back());
			BasicBlock::iterator BI, BE;
			for(BI = BB->begin(), BE = BB->end(); BI != BE; BI++)
			{
				Instruction *II = BI;
				if(isa<ReturnInst>(II)) break;// || isa<CallInst>(II)) break;
			}
			
			if(BI == BE)
			{
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "-----------found! ------------------------------------------1---------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";

				IRBuilder<> IRB1(F->back().getTerminator());
				//IRB1.CreateCall(instru_dump_result_f, initial_value_int_zero);
				IRB1.CreateCall(instru_dump_rdtsc_result_f, initial_value_int_zero);
				IRB1.CreateCall(instru_set_loop_false_f, initial_value_int_zero);

				//get time again after our time consuming process
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//IRB1.CreateStore(load, gv);



			}
			else
			{

			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "-----------found! ------------------------------------------2---------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";


				IRBuilder<> IRB1((Instruction *)BI);
				//IRB1.CreateCall(instru_dump_result_f, initial_value_int_zero);
				IRB1.CreateCall(instru_dump_rdtsc_result_f, initial_value_int_zero);
				IRB1.CreateCall(instru_set_loop_false_f, initial_value_int_zero);

				//get time again after our time consuming process
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//IRB1.CreateStore(load, gv);

			}




			//init timer thread at the beginning of ecall
			//clear earlier ecall records at the beginning of ecall
			//IRBuilder<> IRB(F->front().getFirstInsertionPt());
			//IRB.CreateCall(instru_init_f, initial_value_int_zero);
			//IRB.CreateCall(instru_clear_record_f, initial_value_int_zero);

			


		}

		f_count++;

	}
	}


	//----------------------Mode 12 for detection logic instrumentation---------------------------//

	//optimized for performance, copied from mode 7


	if(mode == 12)
	{
	FILE *ttracefile;
	char ttracetemp[300];
	strcpy(ttracetemp, currentd);
	strcat(ttracetemp, "/ttracedata.txt");

	//if file does not exist
	if(access(ttracetemp, 0) == -1)
	{
	//-------------------processing tgdata.txt-----------------//
	//map for quick access
	llvm::StringMap<struct bb_num_s*> bbmap;

	int longest_f = 0, longest_bb = 0;

	//get global bb_num, type1, type2
	FILE *gbfile;
	char tgtemp3[300];
	strcpy(tgtemp3, currentd);
	strcat(tgtemp3, "/tgdata.txt");
	gbfile = fopen(tgtemp3, "r");
	if(gbfile)
	{
		char *line = NULL;
		size_t len = 0;
		ssize_t read;
		int count = 0;
		struct bb_num_s *ti;
		while((read = getline(&line, &len, gbfile)) != -1)
		{
			//leave out last character '\n'
			line[read-1] = '\0';
			if(count % 4 == 0)
			{
				//function name
				ti = (struct bb_num_s*) malloc (sizeof(struct bb_num_s));
				ti->function_name = (char *) malloc(300);
				strcpy(ti->function_name, line);
			}
			else if(count % 4 == 1)
			{
				//bb name
				ti->bb_name = (char *) malloc(300);
				strcpy(ti->bb_name, line);			
			}
			else if(count % 4 == 2)
			{
				//type1
				ti->type1 = atoi(line);
			}
			else if(count % 4 == 3)
			{
				//type2 and bb global num
				ti->type2 = atoi(line);
				ti->bb_num = (count - 3) / 4;
				bb_num_s_list.push_back(*ti);
				char temp[300];
				strcpy(temp, ti->function_name);
				strcat(temp, ti->bb_name);
				//errs() << temp << "\n";
				std::string tempstr(temp);
				//errs() << tempstr << "\n";
				bbmap[tempstr] = ti;
				//errs() << "ti->function_name: " << ti->function_name << "length:" << strlen(ti->function_name) << "\n";
				//if(strlen(ti->function_name) > longest_f) longest_f = strlen(ti->function_name);
				//if(strlen(ti->bb_name) > longest_bb) longest_bb = strlen(ti->bb_name);
			}

			
			count++;
		}
		fclose(gbfile);
	}
	else
	{
		errs() << "Timed Execution Configration Error: We should have a global basic block file.\n";
		exit(-1);
	}

	/*errs() << "longest function name: " << longest_f << "\n";
	errs() << "longest bb name: " << longest_bb << "\n";

	if(M.getFunction("CRYPTO_num_locks") != NULL)
	{
	FILE *ttfile;
	char tgtemp[120];
	strcpy(tgtemp, currentd);
	strcat(tgtemp, "/my3.txt");
	ttfile = fopen(tgtemp, "a");
	fprintf(ttfile, "%d\n%d\n", longest_f, longest_bb);
	fclose(ttfile);
	}*/

	/*struct bb_num_s* mapt = bbmap["EVP_CIPHER_CTX_freeEVP_CIPHER_CTX_cleanup.exit"];
	if(mapt == NULL) errs() << "mapt == NULL\n";
	else errs() << "the data found in maps is: " << "function name: " << mapt->function_name << "bb name: " 
		<< mapt->bb_name << "bb num: " << mapt->bb_num << "type1 flag: " << mapt->type1 
		<< "type2 flag: " << mapt->type2 << "\n";*/

	/*if(M.getFunction("ecall_DoNumSort") != NULL)
	{
	for(std::vector<struct bb_num_s>::iterator it = bb_num_s_list.begin() ; it != bb_num_s_list.end(); ++it)
	{
		FILE *file;
		char tgtemp[120];
		strcpy(tgtemp, currentd);
		strcat(tgtemp, "/my.txt");
		file = fopen(tgtemp, "a");
		//printf("%s\n",str);
		//fprintf(file, "%s\n%s\n%lu\n", function_name, bb_name, t);
		fprintf(file, "%s\n%s\n%d\n%d\n%d\n", it->function_name, it->bb_name, it->bb_num, it->type1, it->type2);
		fclose(file);
	}
	}
	bb_num_s_list.clear();*/




	//-------------------processing tdata.txt ttdata.txt-----------------//

	FILE *datafile, *tracefile;
	char tgtemp1[300];
	strcpy(tgtemp1, currentd);
	strcat(tgtemp1, "/tdata.txt");
	char tgtemp2[300];
	strcpy(tgtemp2, currentd);
	strcat(tgtemp2, "/ttdata.txt");
	datafile = fopen(tgtemp1,"r");
	tracefile = fopen(tgtemp2,"r");
	if(datafile)
	{
		if(tracefile)
		{
			char *line1 = NULL;
			size_t len1 = 0;
			ssize_t read1;
			int count1 = 0;
			char *line2 = NULL;
			size_t len2 = 0;
			ssize_t read2;
			int count2 = 0;
			char *line3= NULL;
			size_t len3 = 0;
			ssize_t read3;

			while (((read1 = getline(&line1, &len1, datafile)) != -1) 
				&& ((read2 = getline(&line2, &len2, tracefile)) != -1)
				&& ((read3 = getline(&line3, &len3, tracefile)) != -1))
			{
				//leave out last character '\n'
				line1[read1-1] = '\0';
				line2[read2-1] = '\0';
				line3[read3-1] = '\0';
				struct training_info *ti = (struct training_info*) malloc (sizeof(struct training_info));
				ti->bb_time = atoi(line1);
				ti->function_name = (char *) malloc(300);
				ti->bb_name = (char *) malloc(300);
				strcpy(ti->function_name, line2);
				strcpy(ti->bb_name, line3);
				char temp[300];
				strcpy(temp, ti->function_name);
				strcat(temp, ti->bb_name);
				struct bb_num_s* mapt = bbmap[temp];
				//if(mapt == NULL) errs() << "mapt == NULL\n";
				//else errs() << "the data found in maps is: " << "function name: " << mapt->function_name 
					//<< "bb name: " << mapt->bb_name << "bb num: " << mapt->bb_num << "type1 flag: " 
					//<< mapt->type1 << "type2 flag: " << mapt->type2 << "\n";
				if(mapt == NULL)
				{
					errs() << "--------------- mapt == NULL ----------------\n";
					FILE *file;
					char tgtemp[120];
					strcpy(tgtemp, currentd);
					strcat(tgtemp, "/my2.txt");
					file = fopen(tgtemp, "a");
					fprintf(file, "%s\n%s\n", ti->function_name, ti->bb_name);
					fclose(file);
					ti->bb_num = -1;
					ti->type1 = -1;
					ti->type2 = -1;
				}
				else
				{
					ti->bb_num = mapt->bb_num;
					ti->type1 = mapt->type1;
					ti->type2 = mapt->type2;
				}
				info_list.push_back(*ti);
			}
			fclose(datafile);
			fclose(tracefile);
		}
		else
		{
			errs() << "Timed Execution Configration Error: We should have a trace file.\n";
			exit(-1);
		}
	}
	else
	{
		errs() << "Timed Execution Configration Error: We should have a data file.\n";
		exit(-1);
	}
	bbmap.clear();
	bb_num_s_list.clear();


	/*if(M.getFunction("ecall_DoNumSort") != NULL)
	{
	for(std::vector<struct training_info>::iterator trit = info_list.begin() ; trit != info_list.end(); ++trit)
	{
		FILE *file;
		char tgtemp[120];
		strcpy(tgtemp, currentd);
		strcat(tgtemp, "/my1.txt");
		file = fopen(tgtemp, "a");
		//printf("%s\n",str);
		//fprintf(file, "%s\n%s\n%lu\n", function_name, bb_name, t);
		fprintf(file, "%s\n%s\n%d\n%d\n%d\n%d\n", trit->function_name, trit->bb_name, trit->bb_time, trit->bb_num, trit->type1, trit->type2);
		fclose(file);

	}
	}*/
	//info_list.clear();




	/*obsolete
	//mark trace nodes type1 and type2
	//mark bb_num
	for(std::vector<struct bb_num_s>::iterator it = bb_num_s_list.begin() ; it != bb_num_s_list.end(); ++it)
	{
		markBBNumType1Type2Info(it->function_name, it->bb_name, it->bb_num, it->type1, it->type2);
	}

	if(M.getFunction("CRYPTO_num_locks") != NULL)
	{
	printMark(M);
	}*/


	//process trace
	//collect trace info from trainging info
	//backwards in training info list
	int need_type1_bb_num = 0;
	struct trace_info *ti;
	for(std::vector<struct training_info>::iterator it = info_list.end() - 1; it >= info_list.begin(); it--)
	{
		if(need_type1_bb_num)
		{
			ti->context_type1_function_name = (char *) malloc(60);
			strcpy(ti->context_type1_function_name, it->function_name);
			ti->context_type1_bb_name = (char *) malloc(60);
			strcpy(ti->context_type1_bb_name, it->bb_name);
			ti->context_type1_bb_num = it->bb_num;
			trace_list.push_back(*ti);
			need_type1_bb_num = 0;
		}
		if(it->type2 == 1)// && it != info_list.begin())
		{
			ti = (struct trace_info*) malloc (sizeof(struct trace_info));
			ti->function_name = (char *) malloc(60);
			strcpy(ti->function_name, it->function_name);
			ti->tail_type2_bb_name = (char *) malloc(60);
			strcpy(ti->tail_type2_bb_name, it->bb_name);
			ti->bb_time = it->bb_time;
			need_type1_bb_num = 1;
			//special handling for the entry of the ecall
			if(it == info_list.begin())
			{
				ti->context_type1_function_name = (char *) malloc(60);
				strcpy(ti->context_type1_function_name, " ");
				ti->context_type1_bb_name = (char *) malloc(60);
				strcpy(ti->context_type1_bb_name, " ");
				ti->context_type1_bb_num = -1;
				trace_list.push_back(*ti);
			}
		}
	}

	//print for debugging
	/*if(M.getFunction("ecall_DoNumSort") != NULL)
	{
	for(std::vector<struct trace_info>::iterator it = trace_list.begin() ; it != trace_list.end(); it++)
	{
		FILE *file;
		char tgtemp[120];
		strcpy(tgtemp, currentd);
		strcat(tgtemp, "/my4.txt");
		file = fopen(tgtemp, "a");
		//fprintf(file, "%s\n%s\n%d\n%d\n%d\n%d\n", it->function_name, it->bb_name, it->bb_num, it->bb_time, it->type1, it->type2);
		
		//if(strcmp(M.getModuleIdentifier().c_str(), MAINFILE) == 0)
			fprintf(file, "%s\n%s\n%s\n%s\n%d\n%lu\n", 
				it->function_name, it->tail_type2_bb_name, it->context_type1_function_name, it->context_type1_bb_name, it->context_type1_bb_num, it->bb_time);
		
		fclose(file);
	}
	}

	//print for debugging
	int t2_count = 0;
	for(std::vector<struct training_info>::iterator it = info_list.end() - 1; it >= info_list.begin(); it--)
	{
		if(it->type2 == 1) t2_count++;
		//printf("%d\n", t2_count);
	}
	printf("t2_count: %d\n", t2_count);*/

	info_list.clear();

	//save to file
	for(std::vector<struct trace_info>::iterator it = trace_list.begin() ; it != trace_list.end(); it++)
	{
		//errs() << "save to file\n";
		FILE *file;
		char tgtemp[120];
		strcpy(tgtemp, currentd);
		strcat(tgtemp, "/ttracedata.txt");
		file = fopen(tgtemp, "a");
			fprintf(file, "%s\n%s\n%s\n%s\n%d\n%lu\n", 
				it->function_name, it->tail_type2_bb_name, it->context_type1_function_name, it->context_type1_bb_name, it->context_type1_bb_num, it->bb_time);
		fclose(file);
	}
	}
	//file exists
	else
	{
	//errs() << "ttracedata.txt exists.\n";
	FILE *gbfile;
	char tgtemp3[300];
	strcpy(tgtemp3, currentd);
	strcat(tgtemp3, "/ttracedata.txt");
	gbfile = fopen(tgtemp3, "r");
	if(gbfile)
	{
		char *line = NULL;
		size_t len = 0;
		ssize_t read;
		int count = 0;
		struct trace_info *ti;
		while((read = getline(&line, &len, gbfile)) != -1)
		{
			//leave out last character '\n'
			line[read-1] = '\0';
			//errs() << "line: " << line << "\n";
			if(count % 6 == 0)
			{
				//function name
				ti = (struct trace_info*) malloc (sizeof(struct trace_info));
				ti->function_name = (char *) malloc(300);
				strcpy(ti->function_name, line);
			}
			else if(count % 6 == 1)
			{
				//type2 bb name
				ti->tail_type2_bb_name = (char *) malloc(300);
				strcpy(ti->tail_type2_bb_name, line);			
			}
			else if(count % 6 == 2)
			{
				//context type1 function name
				ti->context_type1_function_name = (char *) malloc(300);
				strcpy(ti->context_type1_function_name, line);			
			}
			else if(count % 6 == 3)
			{
				//context type1 bb name
				ti->context_type1_bb_name = (char *) malloc(300);
				strcpy(ti->context_type1_bb_name, line);			
			}
			else if(count % 6 == 4)
			{
				//context type1 bb num
				ti->context_type1_bb_num = atoi(line);
			}
			else if(count % 6 == 5)
			{
				//type2 and bb global num
				ti->bb_time = atoi(line);

				//errs() << "ti->context_type1_function_name: " << ti->context_type1_function_name << "\n";
				//errs() << "ti->context_type1_bb_name: " << ti->context_type1_bb_name << "\n";

				trace_list.push_back(*ti);
			}
			count++;
		}
		fclose(gbfile);
	}
	else
	{
		errs() << "Timed Execution Configration Error: We should have a processed trace file.\n";
		exit(-1);
	}

	}


	//instrument type1 nodes
	//type1 nodes put its bb_num to global variable pre_bb_num
	//find every bb in this module first and then traverse trace_list

	int f_count=0;
	for(Module::iterator MI = M.begin(), ME = M.end(); MI != ME; MI++)
	{
		Function *F = MI;
		char* function_name = (char*)malloc(60);
		strcpy(function_name, F->getName().str().c_str());
		int bb_count =0;
		for(Function::iterator FI = MI->begin(), FE = MI->end(); FI != FE; FI++)
		{	
			BasicBlock *BB = FI;
			char* bb_name = (char*)malloc(180);
			strcpy(bb_name, BB->getName().str().c_str());
			IRBuilder<> IRB(BB->getTerminator());
			//errs() << function_name << " " << bb_name << "\n";
			int type1 = -1, type2 = -1;
			std::vector<int> bb_num_vector;
			std::vector<unsigned long> time_vector;
			std::vector<int> bb_num_vector1;
			std::vector<int> visited_vector1;
			std::vector<int> bb_num_vector2;
			std::vector<double> average_vector2;
			std::vector<double> stdev_vector2;
			std::vector<double> b_vector3;
			std::vector<double> c_vector3;
			int context_type1_bb_num = -1;

			//obsolete
			//handle the ecall entry and exit
			/*if((strcmp(function_name, p_entry_function) == 0) && (strcmp(bb_name, "entry") == 0))
			{
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//LoadInst *last_time_load = IRB.CreateLoad(gv);
				//IRB.CreateStore(initial_value_int_zero, gv);


				//IRBuilder<> IRB1(BB->getFirstInsertionPt());
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//IRB1.CreateCall(instru_print_long_long_int_to_debug_f, load);


				//print for debugging
				//IRB.CreateCall(instru_print_int_to_debug_f, last_time_load);
				//IRB.CreateCall(instru_print_int_to_debug_f, load);

				//init timer thread at the beginning of ecall
				//clear earlier ecall records at the beginning of ecall
				IRBuilder<> IRB1(F->front().getFirstInsertionPt());
				IRB1.CreateCall(instru_init_f, initial_value_int_zero);
				//IRB1.CreateCall(instru_clear_record_f, initial_value_int_zero);


			}*/

			//errs() << "trace_list.size(): " << trace_list.size() << "\n";
			for(std::vector<struct trace_info>::iterator it = trace_list.begin() ; it != trace_list.end(); it++)
			{
				//errs() << "it->context_type1_function_name: " << it->context_type1_function_name << "\n";
				//errs() << "it->context_type1_bb_name: " << it->context_type1_bb_name << "\n";
				//check if this one is type1
				if((strcmp(it->context_type1_function_name, function_name) == 0) && (strcmp(it->context_type1_bb_name, bb_name) == 0))
				{
					type1 = 1;
					context_type1_bb_num = it->context_type1_bb_num;
				}
				//check if any type2 nodes is this one
				if((strcmp(it->function_name, function_name) == 0) && (strcmp(it->tail_type2_bb_name, bb_name) == 0))
				{
					type2 = 1;
					//errs() << "type2: " << function_name << " " << bb_name << "\n";
					bb_num_vector.push_back(it->context_type1_bb_num);
					time_vector.push_back(it->bb_time);
				}
			}
			//instrument type2 first
			if(type2 == 1)
			{

				//errs() << function_name << " " << bb_name << "\n";
				errs() << "type2!\n";
				//errs() << "size of vector: " << bb_num_vector.size();
				//for(std::vector<int>::iterator it = bb_num_vector.begin() ; it != bb_num_vector.end(); it++)
					//for(std::vector<unsigned long>::iterator itt = time_vector.begin() ; itt != time_vector.end(); itt++)
						//errs() << *it << " " << *itt << ", ";
				//errs() << "\n";
				//get average and stdev
				//copy bb_num_vector to bb_num_vector1, bb_num_vector1 works as a temp vector with UNIQUE values
				for(std::vector<int>::iterator it = bb_num_vector.begin() ; it != bb_num_vector.end(); it++)
				{
					int in_it = 0;
					for(std::vector<int>::iterator itt = bb_num_vector1.begin() ; itt != bb_num_vector1.end(); itt++)
						if(*it == *itt) in_it = 1;
					if(in_it == 0)bb_num_vector1.push_back(*it);
				}
				errs() << "size of vector: " << bb_num_vector1.size() << "\n";
				//initialize visited_vector1 as all 0;
				for(std::vector<int>::iterator it = bb_num_vector.begin() ; it != bb_num_vector.end(); it++)
					visited_vector1.push_back(0);
				//check each value in bb_num_vector1
				for(std::vector<int>::iterator it = bb_num_vector1.begin() ; it != bb_num_vector1.end(); it++)
				{
					int count = 0;
					double average = -1.0;
					double stdev = -1.0;
					std::vector<unsigned long> specific_vector;
					//process everyone in bb_num_vector that has such value
					std::vector<int>::iterator itt = bb_num_vector.begin();
					std::vector<int>::iterator ittt = visited_vector1.begin();
					std::vector<unsigned long>::iterator itttt = time_vector.begin();
					while(itt != bb_num_vector.end() && ittt != visited_vector1.end() && itttt != time_vector.end())
					{
						//if it is visited before, do not bother that
						if(*itt == *it && *ittt == 0)
						{
							//mark as visited
							*ittt = 1;
							count++;
							specific_vector.push_back(*itttt);
						}
						itt++;ittt++;itttt++;
					}
					//calculate average
					average = 0;
					for(std::vector<unsigned long>::iterator myit = specific_vector.begin() ; myit != specific_vector.end(); myit++)
						average += *myit;
					average /= count;
					//calculate stdev
					stdev = 0;
					//errs() << "data:\n";
					for(std::vector<unsigned long>::iterator myit = specific_vector.begin() ; myit != specific_vector.end(); myit++)
					{
						//errs() << *myit << " ";
						stdev = stdev + (*myit - average) * (*myit - average);
					}
					//errs() << "\ncount: " << count << "\n";
					stdev /= count;
					stdev = sqrt(stdev);
					//errs() << "stdev: " << stdev << "\n";
					bb_num_vector2.push_back(*it);
					average_vector2.push_back(average);
					stdev_vector2.push_back(stdev);
				}
				std::vector<int>::iterator myit = bb_num_vector2.begin();
				std::vector<double>::iterator myit1 = average_vector2.begin();
				std::vector<double>::iterator myit2 = stdev_vector2.begin();

				//print for debugging
				while(myit != bb_num_vector2.end() && myit1 != average_vector2.end() && myit2 != stdev_vector2.end())
				{
					errs() << "prior bb num: " << *myit << " average: " << *myit1 << " stdev: " << *myit2 << "\n";
					myit++; myit1++; myit2++;
				}


				errs() << "**************************************************type2!\n";



				//transform structure
				/*//Value *mine_f = M.getOrInsertFunction("mine", VoidTy, I64Ty, nullptr);
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB.CreateLoad(gv);
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				LoadInst *lload = IRB.CreateLoad(gv);

				TerminatorInst *I1 = BB->getTerminator();
				Instruction *nop = BinaryOperator::Create(Instruction::Add, initial_value_int_zero, initial_value_int_zero);
				BB->getInstList().insert(I1, nop);
				BasicBlock *newBB1 = BB->splitBasicBlock(nop, "newbasicblock2");

				I1 = BB->getTerminator();
				nop = BinaryOperator::Create(Instruction::Add, initial_value_int_zero, initial_value_int_zero);
				//CallInst *callv = CallInst::Create(mine_f, initial_value_int_zero);
				BB->getInstList().insert(I1, nop);
				BasicBlock *newBB2 = BB->splitBasicBlock(nop, "newbasicblock3");

				I1 = BB->getTerminator();
				//Value * cmpv = IRB.CreateICmpUGT(lload, load);
				BranchInst *bran1 = BranchInst::Create(newBB1, newBB2, CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_EQ, lload, load, "compare", I1));
				ReplaceInstWithInst(I1, bran1);*///

				//add instructions
				//add to BB, that is, kind of front
				IRBuilder<> IRB1(BB->getTerminator());
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB1.CreateLoad(gv);
				Value *curr = load;
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				LoadInst *last_time_load = IRB1.CreateLoad(gv);
				IRB1.CreateStore(load, gv);
				Value *detect_result_sub_inst = IRB1.CreateSub(load, last_time_load);

				int vector_size = bb_num_vector2.size();
				int my_i;
				myit1 = average_vector2.begin();
				myit2 = stdev_vector2.begin();
				for(my_i = 0; my_i < vector_size; my_i++)
				{
					b_vector3.push_back(*myit1 - *myit2);
					c_vector3.push_back(*myit1 + page_fault_average - *myit2 - page_fault_stdev);
					myit1++; myit2++;
				}

				//errs() << "page_fault_average: " << page_fault_average << "page_fault_stdev: " << page_fault_stdev << "\n";

				//print for debugging, b_vector3 and c_vector3
				std::vector<double>::iterator mybit = b_vector3.begin();
				std::vector<double>::iterator mycit = c_vector3.begin();
				while((mybit != b_vector3.end()) && (mycit != c_vector3.end()))
				{
					errs() << "b: " << *mybit << " c: " << *mycit << "\n";
					mybit++;mycit++;
				}
				gv = M.getGlobalVariable(StringRef("pre_bb_num"), true);
				load = IRB1.CreateLoad(gv);
				myit = bb_num_vector2.begin();
				mybit = b_vector3.begin();
				mycit = c_vector3.begin();
				//if(*mycit < 3) printf("*mycit: %lf\n", *mycit);


				/*//if(vector_size == 1)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);

					//compare load and myit_value_int
					I1 = BB->getTerminator();
					CmpInst *cmp1 = CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_EQ, load, myit_value_int, "compare1", I1);
					CmpInst *cmp2 = CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_SGT, detect_result_sub_inst, mycit_value_int, "compare2", I1);

					//Instruction *myand = BinaryOperator::Create(Instruction::And, cmp1, cmp2);
					//CmpInst *cmp3 = CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_EQ, myand, initial_value_int_one, "compare3", I1);
					BranchInst *bran1 = BranchInst::Create(newBB2, newBB1, cmp2);
					ReplaceInstWithInst(I1, bran1);

				}
				else if(vector_size == 2)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);
					Constant *myit1_value_int = ConstantInt::get(I64Ty, *(myit+1));
					Constant *mycit1_value_int = ConstantInt::get(I64Ty, *(mycit+1));

					I1 = BB->getTerminator();
					CmpInst *cmp1 = CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_SGT, detect_result_sub_inst, mycit_value_int, "compare1", I1);
					CmpInst *cmp2 = CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_SGT, detect_result_sub_inst, mycit1_value_int, "compare2", I1);
					CmpInst *cmp3 = CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_EQ, cmp1, cmp2, "compare3", I1);
					CmpInst *cmp4 = CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_EQ, cmp1, cmp3, "compare4", I1);
					CmpInst *cmp5 = CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_EQ, cmp2, cmp4, "compare4", I1);

					BranchInst *bran1 = BranchInst::Create(newBB1, newBB2, cmp5);
					ReplaceInstWithInst(I1, bran1);

				}*///




				//add to newBB2, that is, the middle
				if(vector_size == 1)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, (int)*myit);
					Constant *mybit_value_int = ConstantInt::get(I64Ty, (int)*mybit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, (int)*mycit);


					//Constant *mybit_value_double = ConstantFP::get(DoubleTy, *mybit);
					//Constant *mycit_value_double = ConstantFP::get(DoubleTy, *mycit);



					//errs() << "*mycit: " << *mycit << "\n";
					Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
					Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
					Value *args[] = {load, detect_result_sub_inst, last_time_load, curr, myit_value_int, mybit_value_int, mycit_value_int, str_para1, str_para2};
					//Value *args[] = {load, detect_result_sub_inst, last_time_load, curr, myit_value_int, mybit_value_double, mycit_value_double, str_para1, str_para2};

					//IRBuilder<> IRB(newBB2->getTerminator());
					IRBuilder<> IRB(BB->getTerminator());
					IRB.CreateCall(instru_detect1_f, args);
				}
				else if(vector_size == 2)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mybit_value_int = ConstantInt::get(I64Ty, *mybit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);
					Constant *myit1_value_int = ConstantInt::get(I64Ty, *(myit+1));
					Constant *mybit1_value_int = ConstantInt::get(I64Ty, *(mybit+1));
					Constant *mycit1_value_int = ConstantInt::get(I64Ty, *(mycit+1));
					Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
					Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
					Value *args[] = {load, detect_result_sub_inst, last_time_load, curr, myit_value_int, mybit_value_int, mycit_value_int,
								myit1_value_int, mybit1_value_int, mycit1_value_int, str_para1, str_para2};
					//IRBuilder<> IRB(newBB2->getTerminator());
					IRBuilder<> IRB(BB->getTerminator());
					IRB.CreateCall(instru_detect2_f, args);
				}
				else if(vector_size == 3)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mybit_value_int = ConstantInt::get(I64Ty, *mybit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);
					Constant *myit1_value_int = ConstantInt::get(I64Ty, *(myit+1));
					Constant *mybit1_value_int = ConstantInt::get(I64Ty, *(mybit+1));
					Constant *mycit1_value_int = ConstantInt::get(I64Ty, *(mycit+1));
					Constant *myit2_value_int = ConstantInt::get(I64Ty, *(myit+2));
					Constant *mybit2_value_int = ConstantInt::get(I64Ty, *(mybit+2));
					Constant *mycit2_value_int = ConstantInt::get(I64Ty, *(mycit+2));
					Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
					Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
					Value *args[] = {load, detect_result_sub_inst, last_time_load, curr, myit_value_int, mybit_value_int, mycit_value_int,
								myit1_value_int, mybit1_value_int, mycit1_value_int,
								myit2_value_int, mybit2_value_int, mycit2_value_int, str_para1, str_para2};
					//IRBuilder<> IRB(newBB2->getTerminator());
					IRBuilder<> IRB(BB->getTerminator());
					IRB.CreateCall(instru_detect3_f, args);
				}
				else if(vector_size == 4)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mybit_value_int = ConstantInt::get(I64Ty, *mybit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);
					Constant *myit1_value_int = ConstantInt::get(I64Ty, *(myit+1));
					Constant *mybit1_value_int = ConstantInt::get(I64Ty, *(mybit+1));
					Constant *mycit1_value_int = ConstantInt::get(I64Ty, *(mycit+1));
					Constant *myit2_value_int = ConstantInt::get(I64Ty, *(myit+2));
					Constant *mybit2_value_int = ConstantInt::get(I64Ty, *(mybit+2));
					Constant *mycit2_value_int = ConstantInt::get(I64Ty, *(mycit+2));
					Constant *myit3_value_int = ConstantInt::get(I64Ty, *(myit+3));
					Constant *mybit3_value_int = ConstantInt::get(I64Ty, *(mybit+3));
					Constant *mycit3_value_int = ConstantInt::get(I64Ty, *(mycit+3));
					Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
					Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
					Value *args[] = {load, detect_result_sub_inst, last_time_load, curr, myit_value_int, mybit_value_int, mycit_value_int,
								myit1_value_int, mybit1_value_int, mycit1_value_int,
								myit2_value_int, mybit2_value_int, mycit2_value_int,
								myit3_value_int, mybit3_value_int, mycit3_value_int, str_para1, str_para2};
					//IRBuilder<> IRB(newBB2->getTerminator());
					IRBuilder<> IRB(BB->getTerminator());
					IRB.CreateCall(instru_detect4_f, args);
				}


				Constant *myit_value_int = ConstantInt::get(I64Ty, 1);
				Constant *mybit_value_int = ConstantInt::get(I64Ty, 2);
				Constant *mycit_value_int = ConstantInt::get(I64Ty, 3);
				Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
				Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
				Value *args[] = {myit_value_int, myit_value_int, myit_value_int, myit_value_int, myit_value_int, mybit_value_int, mycit_value_int, str_para1, str_para2};
				////IRBuilder<> IRB2(newBB2->getTerminator());
				//IRB2.CreateCall(instru_detect1_f, args);



				//add to newBB1, that is, the end
				////IRBuilder<> IRB3(newBB1->getTerminator());
				IRBuilder<> IRB3(BB->getTerminator());
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB3.CreateLoad(gv);
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				IRB3.CreateStore(load, gv);



			}


			if(type1 == 1)
			{
				//errs() << "type1!\n";
				//errs() << function_name << " " << bb_name << " " << context_type1_bb_num << "\n";
				Constant *bb_num_value = ConstantInt::get(I64Ty, context_type1_bb_num);
				gv = M.getGlobalVariable(StringRef("pre_bb_num"), true);
				IRBuilder<> IRB(BB->getTerminator());
				IRB.CreateStore(bb_num_value, gv);//done.
			}

			//obsolete
			/*if((strcmp(function_name, p_entry_function) == 0) && (strcmp(bb_name, F->back().getName().str().c_str()) == 0))
			{
				//errs() << "F name: " << F->getName() << " " << "BB name: " << BB->getName() << "\n";
				IRB.CreateCall(instru_dump_detection_result_f, initial_value_int_one);
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB.CreateLoad(gv);
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				IRB.CreateStore(load, gv);
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB.CreateLoad(gv);
				//IRB.CreateCall(instru_print_long_long_int_to_debug_f, load);
			}*/

			free(bb_name);
			bb_num_vector.clear();
			time_vector.clear();
			bb_num_vector1.clear();
			visited_vector1.clear();
			bb_num_vector2.clear();
			average_vector2.clear();
			stdev_vector2.clear();
			b_vector3.clear();
			c_vector3.clear();

		}

		//handle ecall entry and exit
		if((strcmp(function_name, p_entry_function) == 0) && (M.getFunction(p_reference_function) != NULL))
		{
			//dump all detection timing infomation at the end of ecall
			BasicBlock *BB = &(F->back());
			BasicBlock::iterator BI, BE;
			for(BI = BB->begin(), BE = BB->end(); BI != BE; BI++)
			{
				Instruction *II = BI;
				if(isa<ReturnInst>(II)) break; //|| isa<CallInst>(II)) break;
			}

			if(BI == BE)
			{
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "-----------found! ------------------------------------------1---------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";

				IRBuilder<> IRB1(F->back().getTerminator());


				//IRB1.CreateCall(instru_print_time_f, initial_value_int_zero);
				IRB1.CreateCall(instru_dump_detection_result_f, initial_value_int_zero);
				////IRB1.CreateCall(instru_set_loop_false_f, initial_value_int_zero);

				//get time again after our time consuming process
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//IRB1.CreateStore(load, gv);



			}
			else
			{

			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "-----------found! ------------------------------------------2---------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";


				IRBuilder<> IRB1((Instruction *)BI);
				errs() << "2\n";
				//IRB1.CreateCall(instru_print_time_f, initial_value_int_zero);
				IRB1.CreateCall(instru_dump_detection_result_f, initial_value_int_zero);
				////IRB1.CreateCall(instru_set_loop_false_f, initial_value_int_zero);

				//get time again after our time consuming process
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//IRB1.CreateStore(load, gv);

			}




			//init timer thread at the beginning of ecall
			//clear earlier ecall records at the beginning of ecall
			IRBuilder<> IRB(F->front().getFirstInsertionPt());
			//IRB.CreateCall(instru_init_f, initial_value_int_zero);
			//IRB.CreateCall(instru_print_time_f, initial_value_int_zero);
			//IRB.CreateCall(instru_clear_record_f, initial_value_int_zero);
		}



	}


	}

	//----------------------Mode 13 for detection logic instrumentation---------------------------//

	//optimized for performance, copied from mode 12


	if(mode == 13)
	{
	FILE *ttracefile;
	char ttracetemp[300];
	strcpy(ttracetemp, currentd);
	strcat(ttracetemp, "/ttracedata.txt");

	//if file does not exist
	if(access(ttracetemp, 0) == -1)
	{
	//-------------------processing tgdata.txt-----------------//
	//map for quick access
	llvm::StringMap<struct bb_num_s*> bbmap;

	int longest_f = 0, longest_bb = 0;

	//get global bb_num, type1, type2
	FILE *gbfile;
	char tgtemp3[300];
	strcpy(tgtemp3, currentd);
	strcat(tgtemp3, "/tgdata.txt");
	gbfile = fopen(tgtemp3, "r");
	if(gbfile)
	{
		char *line = NULL;
		size_t len = 0;
		ssize_t read;
		int count = 0;
		struct bb_num_s *ti;
		while((read = getline(&line, &len, gbfile)) != -1)
		{
			//leave out last character '\n'
			line[read-1] = '\0';
			if(count % 4 == 0)
			{
				//function name
				ti = (struct bb_num_s*) malloc (sizeof(struct bb_num_s));
				ti->function_name = (char *) malloc(300);
				strcpy(ti->function_name, line);
			}
			else if(count % 4 == 1)
			{
				//bb name
				ti->bb_name = (char *) malloc(300);
				strcpy(ti->bb_name, line);			
			}
			else if(count % 4 == 2)
			{
				//type1
				ti->type1 = atoi(line);
			}
			else if(count % 4 == 3)
			{
				//type2 and bb global num
				ti->type2 = atoi(line);
				ti->bb_num = (count - 3) / 4;
				bb_num_s_list.push_back(*ti);
				char temp[300];
				strcpy(temp, ti->function_name);
				strcat(temp, ti->bb_name);
				//errs() << temp << "\n";
				std::string tempstr(temp);
				//errs() << tempstr << "\n";
				bbmap[tempstr] = ti;
				//errs() << "ti->function_name: " << ti->function_name << "length:" << strlen(ti->function_name) << "\n";
				//if(strlen(ti->function_name) > longest_f) longest_f = strlen(ti->function_name);
				//if(strlen(ti->bb_name) > longest_bb) longest_bb = strlen(ti->bb_name);
			}

			
			count++;
		}
		fclose(gbfile);
	}
	else
	{
		errs() << "Timed Execution Configration Error: We should have a global basic block file.\n";
		exit(-1);
	}

	/*errs() << "longest function name: " << longest_f << "\n";
	errs() << "longest bb name: " << longest_bb << "\n";

	if(M.getFunction("CRYPTO_num_locks") != NULL)
	{
	FILE *ttfile;
	char tgtemp[120];
	strcpy(tgtemp, currentd);
	strcat(tgtemp, "/my3.txt");
	ttfile = fopen(tgtemp, "a");
	fprintf(ttfile, "%d\n%d\n", longest_f, longest_bb);
	fclose(ttfile);
	}*/

	/*struct bb_num_s* mapt = bbmap["EVP_CIPHER_CTX_freeEVP_CIPHER_CTX_cleanup.exit"];
	if(mapt == NULL) errs() << "mapt == NULL\n";
	else errs() << "the data found in maps is: " << "function name: " << mapt->function_name << "bb name: " 
		<< mapt->bb_name << "bb num: " << mapt->bb_num << "type1 flag: " << mapt->type1 
		<< "type2 flag: " << mapt->type2 << "\n";*/

	/*if(M.getFunction("ecall_DoNumSort") != NULL)
	{
	for(std::vector<struct bb_num_s>::iterator it = bb_num_s_list.begin() ; it != bb_num_s_list.end(); ++it)
	{
		FILE *file;
		char tgtemp[120];
		strcpy(tgtemp, currentd);
		strcat(tgtemp, "/my.txt");
		file = fopen(tgtemp, "a");
		//printf("%s\n",str);
		//fprintf(file, "%s\n%s\n%lu\n", function_name, bb_name, t);
		fprintf(file, "%s\n%s\n%d\n%d\n%d\n", it->function_name, it->bb_name, it->bb_num, it->type1, it->type2);
		fclose(file);
	}
	}
	bb_num_s_list.clear();*/




	//-------------------processing tdata.txt ttdata.txt-----------------//

	FILE *datafile, *tracefile;
	char tgtemp1[300];
	strcpy(tgtemp1, currentd);
	strcat(tgtemp1, "/tdata.txt");
	char tgtemp2[300];
	strcpy(tgtemp2, currentd);
	strcat(tgtemp2, "/ttdata.txt");
	datafile = fopen(tgtemp1,"r");
	tracefile = fopen(tgtemp2,"r");
	if(datafile)
	{
		if(tracefile)
		{
			char *line1 = NULL;
			size_t len1 = 0;
			ssize_t read1;
			int count1 = 0;
			char *line2 = NULL;
			size_t len2 = 0;
			ssize_t read2;
			int count2 = 0;
			char *line3= NULL;
			size_t len3 = 0;
			ssize_t read3;

			while (((read1 = getline(&line1, &len1, datafile)) != -1) 
				&& ((read2 = getline(&line2, &len2, tracefile)) != -1)
				&& ((read3 = getline(&line3, &len3, tracefile)) != -1))
			{
				//leave out last character '\n'
				line1[read1-1] = '\0';
				line2[read2-1] = '\0';
				line3[read3-1] = '\0';
				struct training_info *ti = (struct training_info*) malloc (sizeof(struct training_info));
				ti->bb_time = atoi(line1);
				ti->function_name = (char *) malloc(300);
				ti->bb_name = (char *) malloc(300);
				strcpy(ti->function_name, line2);
				strcpy(ti->bb_name, line3);
				char temp[300];
				strcpy(temp, ti->function_name);
				strcat(temp, ti->bb_name);
				struct bb_num_s* mapt = bbmap[temp];
				//if(mapt == NULL) errs() << "mapt == NULL\n";
				//else errs() << "the data found in maps is: " << "function name: " << mapt->function_name 
					//<< "bb name: " << mapt->bb_name << "bb num: " << mapt->bb_num << "type1 flag: " 
					//<< mapt->type1 << "type2 flag: " << mapt->type2 << "\n";
				if(mapt == NULL)
				{
					errs() << "--------------- mapt == NULL ----------------\n";
					FILE *file;
					char tgtemp[120];
					strcpy(tgtemp, currentd);
					strcat(tgtemp, "/my2.txt");
					file = fopen(tgtemp, "a");
					fprintf(file, "%s\n%s\n", ti->function_name, ti->bb_name);
					fclose(file);
					ti->bb_num = -1;
					ti->type1 = -1;
					ti->type2 = -1;
				}
				else
				{
					ti->bb_num = mapt->bb_num;
					ti->type1 = mapt->type1;
					ti->type2 = mapt->type2;
				}
				info_list.push_back(*ti);
			}
			fclose(datafile);
			fclose(tracefile);
		}
		else
		{
			errs() << "Timed Execution Configration Error: We should have a trace file.\n";
			exit(-1);
		}
	}
	else
	{
		errs() << "Timed Execution Configration Error: We should have a data file.\n";
		exit(-1);
	}
	bbmap.clear();
	bb_num_s_list.clear();


	/*if(M.getFunction("ecall_DoNumSort") != NULL)
	{
	for(std::vector<struct training_info>::iterator trit = info_list.begin() ; trit != info_list.end(); ++trit)
	{
		FILE *file;
		char tgtemp[120];
		strcpy(tgtemp, currentd);
		strcat(tgtemp, "/my1.txt");
		file = fopen(tgtemp, "a");
		//printf("%s\n",str);
		//fprintf(file, "%s\n%s\n%lu\n", function_name, bb_name, t);
		fprintf(file, "%s\n%s\n%d\n%d\n%d\n%d\n", trit->function_name, trit->bb_name, trit->bb_time, trit->bb_num, trit->type1, trit->type2);
		fclose(file);

	}
	}*/
	//info_list.clear();




	/*obsolete
	//mark trace nodes type1 and type2
	//mark bb_num
	for(std::vector<struct bb_num_s>::iterator it = bb_num_s_list.begin() ; it != bb_num_s_list.end(); ++it)
	{
		markBBNumType1Type2Info(it->function_name, it->bb_name, it->bb_num, it->type1, it->type2);
	}

	if(M.getFunction("CRYPTO_num_locks") != NULL)
	{
	printMark(M);
	}*/


	//process trace
	//collect trace info from trainging info
	//backwards in training info list
	int need_type1_bb_num = 0;
	struct trace_info *ti;
	for(std::vector<struct training_info>::iterator it = info_list.end() - 1; it >= info_list.begin(); it--)
	{
		if(need_type1_bb_num)
		{
			ti->context_type1_function_name = (char *) malloc(60);
			strcpy(ti->context_type1_function_name, it->function_name);
			ti->context_type1_bb_name = (char *) malloc(60);
			strcpy(ti->context_type1_bb_name, it->bb_name);
			ti->context_type1_bb_num = it->bb_num;
			trace_list.push_back(*ti);
			need_type1_bb_num = 0;
		}
		if(it->type2 == 1)// && it != info_list.begin())
		{
			ti = (struct trace_info*) malloc (sizeof(struct trace_info));
			ti->function_name = (char *) malloc(60);
			strcpy(ti->function_name, it->function_name);
			ti->tail_type2_bb_name = (char *) malloc(60);
			strcpy(ti->tail_type2_bb_name, it->bb_name);
			ti->bb_time = it->bb_time;
			need_type1_bb_num = 1;
			//special handling for the entry of the ecall
			if(it == info_list.begin())
			{
				ti->context_type1_function_name = (char *) malloc(60);
				strcpy(ti->context_type1_function_name, " ");
				ti->context_type1_bb_name = (char *) malloc(60);
				strcpy(ti->context_type1_bb_name, " ");
				ti->context_type1_bb_num = -1;
				trace_list.push_back(*ti);
			}
		}
	}

	//print for debugging
	/*if(M.getFunction("ecall_DoNumSort") != NULL)
	{
	for(std::vector<struct trace_info>::iterator it = trace_list.begin() ; it != trace_list.end(); it++)
	{
		FILE *file;
		char tgtemp[120];
		strcpy(tgtemp, currentd);
		strcat(tgtemp, "/my4.txt");
		file = fopen(tgtemp, "a");
		//fprintf(file, "%s\n%s\n%d\n%d\n%d\n%d\n", it->function_name, it->bb_name, it->bb_num, it->bb_time, it->type1, it->type2);
		
		//if(strcmp(M.getModuleIdentifier().c_str(), MAINFILE) == 0)
			fprintf(file, "%s\n%s\n%s\n%s\n%d\n%lu\n", 
				it->function_name, it->tail_type2_bb_name, it->context_type1_function_name, it->context_type1_bb_name, it->context_type1_bb_num, it->bb_time);
		
		fclose(file);
	}
	}

	//print for debugging
	int t2_count = 0;
	for(std::vector<struct training_info>::iterator it = info_list.end() - 1; it >= info_list.begin(); it--)
	{
		if(it->type2 == 1) t2_count++;
		//printf("%d\n", t2_count);
	}
	printf("t2_count: %d\n", t2_count);*/

	info_list.clear();

	//save to file
	for(std::vector<struct trace_info>::iterator it = trace_list.begin() ; it != trace_list.end(); it++)
	{
		//errs() << "save to file\n";
		FILE *file;
		char tgtemp[120];
		strcpy(tgtemp, currentd);
		strcat(tgtemp, "/ttracedata.txt");
		file = fopen(tgtemp, "a");
			fprintf(file, "%s\n%s\n%s\n%s\n%d\n%lu\n", 
				it->function_name, it->tail_type2_bb_name, it->context_type1_function_name, it->context_type1_bb_name, it->context_type1_bb_num, it->bb_time);
		fclose(file);
	}
	}
	//file exists
	else
	{
	//errs() << "ttracedata.txt exists.\n";
	FILE *gbfile;
	char tgtemp3[300];
	strcpy(tgtemp3, currentd);
	strcat(tgtemp3, "/ttracedata.txt");
	gbfile = fopen(tgtemp3, "r");
	if(gbfile)
	{
		char *line = NULL;
		size_t len = 0;
		ssize_t read;
		int count = 0;
		struct trace_info *ti;
		while((read = getline(&line, &len, gbfile)) != -1)
		{
			//leave out last character '\n'
			line[read-1] = '\0';
			//errs() << "line: " << line << "\n";
			if(count % 6 == 0)
			{
				//function name
				ti = (struct trace_info*) malloc (sizeof(struct trace_info));
				ti->function_name = (char *) malloc(300);
				strcpy(ti->function_name, line);
			}
			else if(count % 6 == 1)
			{
				//type2 bb name
				ti->tail_type2_bb_name = (char *) malloc(300);
				strcpy(ti->tail_type2_bb_name, line);			
			}
			else if(count % 6 == 2)
			{
				//context type1 function name
				ti->context_type1_function_name = (char *) malloc(300);
				strcpy(ti->context_type1_function_name, line);			
			}
			else if(count % 6 == 3)
			{
				//context type1 bb name
				ti->context_type1_bb_name = (char *) malloc(300);
				strcpy(ti->context_type1_bb_name, line);			
			}
			else if(count % 6 == 4)
			{
				//context type1 bb num
				ti->context_type1_bb_num = atoi(line);
			}
			else if(count % 6 == 5)
			{
				//type2 and bb global num
				ti->bb_time = atoi(line);

				//errs() << "ti->context_type1_function_name: " << ti->context_type1_function_name << "\n";
				//errs() << "ti->context_type1_bb_name: " << ti->context_type1_bb_name << "\n";

				trace_list.push_back(*ti);
			}
			count++;
		}
		fclose(gbfile);
	}
	else
	{
		errs() << "Timed Execution Configration Error: We should have a processed trace file.\n";
		exit(-1);
	}

	}


	//instrument type1 nodes
	//type1 nodes put its bb_num to global variable pre_bb_num
	//find every bb in this module first and then traverse trace_list

	int f_count=0;
	for(Module::iterator MI = M.begin(), ME = M.end(); MI != ME; MI++)
	{
		Function *F = MI;
		char* function_name = (char*)malloc(60);
		strcpy(function_name, F->getName().str().c_str());
		int bb_count =0;
		for(Function::iterator FI = MI->begin(), FE = MI->end(); FI != FE; FI++)
		{	
			BasicBlock *BB = FI;
			char* bb_name = (char*)malloc(180);
			strcpy(bb_name, BB->getName().str().c_str());
			IRBuilder<> IRB(BB->getTerminator());
			//errs() << function_name << " " << bb_name << "\n";
			int type1 = -1, type2 = -1;
			std::vector<int> bb_num_vector;
			std::vector<unsigned long> time_vector;
			std::vector<int> bb_num_vector1;
			std::vector<int> visited_vector1;
			std::vector<int> bb_num_vector2;
			std::vector<double> average_vector2;
			std::vector<double> stdev_vector2;
			std::vector<double> b_vector3;
			std::vector<double> c_vector3;
			int context_type1_bb_num = -1;

			//obsolete
			//handle the ecall entry and exit
			/*if((strcmp(function_name, p_entry_function) == 0) && (strcmp(bb_name, "entry") == 0))
			{
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//LoadInst *last_time_load = IRB.CreateLoad(gv);
				//IRB.CreateStore(initial_value_int_zero, gv);


				//IRBuilder<> IRB1(BB->getFirstInsertionPt());
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//IRB1.CreateCall(instru_print_long_long_int_to_debug_f, load);


				//print for debugging
				//IRB.CreateCall(instru_print_int_to_debug_f, last_time_load);
				//IRB.CreateCall(instru_print_int_to_debug_f, load);

				//init timer thread at the beginning of ecall
				//clear earlier ecall records at the beginning of ecall
				IRBuilder<> IRB1(F->front().getFirstInsertionPt());
				IRB1.CreateCall(instru_init_f, initial_value_int_zero);
				//IRB1.CreateCall(instru_clear_record_f, initial_value_int_zero);


			}*/

			//errs() << "trace_list.size(): " << trace_list.size() << "\n";
			for(std::vector<struct trace_info>::iterator it = trace_list.begin() ; it != trace_list.end(); it++)
			{
				//errs() << "it->context_type1_function_name: " << it->context_type1_function_name << "\n";
				//errs() << "it->context_type1_bb_name: " << it->context_type1_bb_name << "\n";
				//check if this one is type1
				if((strcmp(it->context_type1_function_name, function_name) == 0) && (strcmp(it->context_type1_bb_name, bb_name) == 0))
				{
					type1 = 1;
					context_type1_bb_num = it->context_type1_bb_num;
				}
				//check if any type2 nodes is this one
				if((strcmp(it->function_name, function_name) == 0) && (strcmp(it->tail_type2_bb_name, bb_name) == 0))
				{
					type2 = 1;
					//errs() << "type2: " << function_name << " " << bb_name << "\n";
					bb_num_vector.push_back(it->context_type1_bb_num);
					time_vector.push_back(it->bb_time);
				}
			}
			//instrument type2 first
			if(type2 == 1)
			{

				//errs() << function_name << " " << bb_name << "\n";
				errs() << "type2!\n";
				//errs() << "size of vector: " << bb_num_vector.size();
				//for(std::vector<int>::iterator it = bb_num_vector.begin() ; it != bb_num_vector.end(); it++)
					//for(std::vector<unsigned long>::iterator itt = time_vector.begin() ; itt != time_vector.end(); itt++)
						//errs() << *it << " " << *itt << ", ";
				//errs() << "\n";
				//get average and stdev
				//copy bb_num_vector to bb_num_vector1, bb_num_vector1 works as a temp vector with UNIQUE values
				for(std::vector<int>::iterator it = bb_num_vector.begin() ; it != bb_num_vector.end(); it++)
				{
					int in_it = 0;
					for(std::vector<int>::iterator itt = bb_num_vector1.begin() ; itt != bb_num_vector1.end(); itt++)
						if(*it == *itt) in_it = 1;
					if(in_it == 0)bb_num_vector1.push_back(*it);
				}
				errs() << "size of vector: " << bb_num_vector1.size() << "\n";
				//initialize visited_vector1 as all 0;
				for(std::vector<int>::iterator it = bb_num_vector.begin() ; it != bb_num_vector.end(); it++)
					visited_vector1.push_back(0);
				//check each value in bb_num_vector1
				for(std::vector<int>::iterator it = bb_num_vector1.begin() ; it != bb_num_vector1.end(); it++)
				{
					int count = 0;
					double average = -1.0;
					double stdev = -1.0;
					std::vector<unsigned long> specific_vector;
					//process everyone in bb_num_vector that has such value
					std::vector<int>::iterator itt = bb_num_vector.begin();
					std::vector<int>::iterator ittt = visited_vector1.begin();
					std::vector<unsigned long>::iterator itttt = time_vector.begin();
					while(itt != bb_num_vector.end() && ittt != visited_vector1.end() && itttt != time_vector.end())
					{
						//if it is visited before, do not bother that
						if(*itt == *it && *ittt == 0)
						{
							//mark as visited
							*ittt = 1;
							count++;
							specific_vector.push_back(*itttt);
						}
						itt++;ittt++;itttt++;
					}
					//calculate average
					average = 0;
					for(std::vector<unsigned long>::iterator myit = specific_vector.begin() ; myit != specific_vector.end(); myit++)
						average += *myit;
					average /= count;
					//calculate stdev
					stdev = 0;
					//errs() << "data:\n";
					for(std::vector<unsigned long>::iterator myit = specific_vector.begin() ; myit != specific_vector.end(); myit++)
					{
						//errs() << *myit << " ";
						stdev = stdev + (*myit - average) * (*myit - average);
					}
					//errs() << "\ncount: " << count << "\n";
					stdev /= count;
					stdev = sqrt(stdev);
					//errs() << "stdev: " << stdev << "\n";
					bb_num_vector2.push_back(*it);
					average_vector2.push_back(average);
					stdev_vector2.push_back(stdev);
				}
				std::vector<int>::iterator myit = bb_num_vector2.begin();
				std::vector<double>::iterator myit1 = average_vector2.begin();
				std::vector<double>::iterator myit2 = stdev_vector2.begin();

				//print for debugging
				while(myit != bb_num_vector2.end() && myit1 != average_vector2.end() && myit2 != stdev_vector2.end())
				{
					errs() << "prior bb num: " << *myit << " average: " << *myit1 << " stdev: " << *myit2 << "\n";
					myit++; myit1++; myit2++;
				}


				errs() << "**************************************************type2!\n";



				//transform structure
				/*//Value *mine_f = M.getOrInsertFunction("mine", VoidTy, I64Ty, nullptr);
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB.CreateLoad(gv);
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				LoadInst *lload = IRB.CreateLoad(gv);

				TerminatorInst *I1 = BB->getTerminator();
				Instruction *nop = BinaryOperator::Create(Instruction::Add, initial_value_int_zero, initial_value_int_zero);
				BB->getInstList().insert(I1, nop);
				BasicBlock *newBB1 = BB->splitBasicBlock(nop, "newbasicblock2");

				I1 = BB->getTerminator();
				nop = BinaryOperator::Create(Instruction::Add, initial_value_int_zero, initial_value_int_zero);
				//CallInst *callv = CallInst::Create(mine_f, initial_value_int_zero);
				BB->getInstList().insert(I1, nop);
				BasicBlock *newBB2 = BB->splitBasicBlock(nop, "newbasicblock3");

				I1 = BB->getTerminator();
				//Value * cmpv = IRB.CreateICmpUGT(lload, load);
				BranchInst *bran1 = BranchInst::Create(newBB1, newBB2, CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_EQ, lload, load, "compare", I1));
				ReplaceInstWithInst(I1, bran1);*///

				//add instructions
				//add to BB, that is, kind of front
				IRBuilder<> IRB1(BB->getTerminator());
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB1.CreateLoad(gv);
				Value *curr = load;
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				LoadInst *last_time_load = IRB1.CreateLoad(gv);
				IRB1.CreateStore(load, gv);
				Value *detect_result_sub_inst = IRB1.CreateSub(load, last_time_load);

				int vector_size = bb_num_vector2.size();
				int my_i;
				myit1 = average_vector2.begin();
				myit2 = stdev_vector2.begin();
				for(my_i = 0; my_i < vector_size; my_i++)
				{
					b_vector3.push_back(*myit1 - *myit2);
					c_vector3.push_back(*myit1 + page_fault_average - *myit2 - page_fault_stdev);
					myit1++; myit2++;
				}

				//errs() << "page_fault_average: " << page_fault_average << "page_fault_stdev: " << page_fault_stdev << "\n";

				//print for debugging, b_vector3 and c_vector3
				std::vector<double>::iterator mybit = b_vector3.begin();
				std::vector<double>::iterator mycit = c_vector3.begin();
				while((mybit != b_vector3.end()) && (mycit != c_vector3.end()))
				{
					errs() << "b: " << *mybit << " c: " << *mycit << "\n";
					mybit++;mycit++;
				}
				gv = M.getGlobalVariable(StringRef("pre_bb_num"), true);
				load = IRB1.CreateLoad(gv);
				myit = bb_num_vector2.begin();
				mybit = b_vector3.begin();
				mycit = c_vector3.begin();
				//if(*mycit < 3) printf("*mycit: %lf\n", *mycit);






				/*if(vector_size == 1)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, (int)*myit);
					Constant *mybit_value_int = ConstantInt::get(I64Ty, (int)*mybit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, (int)*mycit);


					//Constant *mybit_value_double = ConstantFP::get(DoubleTy, *mybit);
					//Constant *mycit_value_double = ConstantFP::get(DoubleTy, *mycit);



					//errs() << "*mycit: " << *mycit << "\n";
					Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
					Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
					Value *args[] = {load, detect_result_sub_inst, last_time_load, curr, myit_value_int, mybit_value_int, mycit_value_int, str_para1, str_para2};
					//Value *args[] = {load, detect_result_sub_inst, last_time_load, curr, myit_value_int, mybit_value_double, mycit_value_double, str_para1, str_para2};

					//IRBuilder<> IRB(newBB2->getTerminator());
					IRBuilder<> IRB(BB->getTerminator());
					IRB.CreateCall(instru_detect1_f, args);
				}
				else if(vector_size == 2)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mybit_value_int = ConstantInt::get(I64Ty, *mybit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);
					Constant *myit1_value_int = ConstantInt::get(I64Ty, *(myit+1));
					Constant *mybit1_value_int = ConstantInt::get(I64Ty, *(mybit+1));
					Constant *mycit1_value_int = ConstantInt::get(I64Ty, *(mycit+1));
					Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
					Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
					Value *args[] = {load, detect_result_sub_inst, last_time_load, curr, myit_value_int, mybit_value_int, mycit_value_int,
								myit1_value_int, mybit1_value_int, mycit1_value_int, str_para1, str_para2};
					//IRBuilder<> IRB(newBB2->getTerminator());
					IRBuilder<> IRB(BB->getTerminator());
					IRB.CreateCall(instru_detect2_f, args);
				}
				else if(vector_size == 3)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mybit_value_int = ConstantInt::get(I64Ty, *mybit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);
					Constant *myit1_value_int = ConstantInt::get(I64Ty, *(myit+1));
					Constant *mybit1_value_int = ConstantInt::get(I64Ty, *(mybit+1));
					Constant *mycit1_value_int = ConstantInt::get(I64Ty, *(mycit+1));
					Constant *myit2_value_int = ConstantInt::get(I64Ty, *(myit+2));
					Constant *mybit2_value_int = ConstantInt::get(I64Ty, *(mybit+2));
					Constant *mycit2_value_int = ConstantInt::get(I64Ty, *(mycit+2));
					Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
					Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
					Value *args[] = {load, detect_result_sub_inst, last_time_load, curr, myit_value_int, mybit_value_int, mycit_value_int,
								myit1_value_int, mybit1_value_int, mycit1_value_int,
								myit2_value_int, mybit2_value_int, mycit2_value_int, str_para1, str_para2};
					//IRBuilder<> IRB(newBB2->getTerminator());
					IRBuilder<> IRB(BB->getTerminator());
					IRB.CreateCall(instru_detect3_f, args);
				}
				else if(vector_size == 4)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mybit_value_int = ConstantInt::get(I64Ty, *mybit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);
					Constant *myit1_value_int = ConstantInt::get(I64Ty, *(myit+1));
					Constant *mybit1_value_int = ConstantInt::get(I64Ty, *(mybit+1));
					Constant *mycit1_value_int = ConstantInt::get(I64Ty, *(mycit+1));
					Constant *myit2_value_int = ConstantInt::get(I64Ty, *(myit+2));
					Constant *mybit2_value_int = ConstantInt::get(I64Ty, *(mybit+2));
					Constant *mycit2_value_int = ConstantInt::get(I64Ty, *(mycit+2));
					Constant *myit3_value_int = ConstantInt::get(I64Ty, *(myit+3));
					Constant *mybit3_value_int = ConstantInt::get(I64Ty, *(mybit+3));
					Constant *mycit3_value_int = ConstantInt::get(I64Ty, *(mycit+3));
					Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
					Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
					Value *args[] = {load, detect_result_sub_inst, last_time_load, curr, myit_value_int, mybit_value_int, mycit_value_int,
								myit1_value_int, mybit1_value_int, mycit1_value_int,
								myit2_value_int, mybit2_value_int, mycit2_value_int,
								myit3_value_int, mybit3_value_int, mycit3_value_int, str_para1, str_para2};
					//IRBuilder<> IRB(newBB2->getTerminator());
					IRBuilder<> IRB(BB->getTerminator());
					IRB.CreateCall(instru_detect4_f, args);
				}*/


				Constant *myit_value_int = ConstantInt::get(I64Ty, 1);
				Constant *mybit_value_int = ConstantInt::get(I64Ty, 2);
				Constant *mycit_value_int = ConstantInt::get(I64Ty, 3);
				Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
				Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
				Value *args[] = {myit_value_int, myit_value_int, myit_value_int, myit_value_int, myit_value_int, mybit_value_int, mycit_value_int, str_para1, str_para2};
				////IRBuilder<> IRB2(newBB2->getTerminator());
				//IRB2.CreateCall(instru_detect1_f, args);



				//add to newBB1, that is, the end
				////IRBuilder<> IRB3(newBB1->getTerminator());
				IRBuilder<> IRB3(BB->getTerminator());
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB3.CreateLoad(gv);
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				IRB3.CreateStore(load, gv);



			}


			if(type1 == 1)
			{
				//errs() << "type1!\n";
				//errs() << function_name << " " << bb_name << " " << context_type1_bb_num << "\n";
				Constant *bb_num_value = ConstantInt::get(I64Ty, context_type1_bb_num);
				gv = M.getGlobalVariable(StringRef("pre_bb_num"), true);
				IRBuilder<> IRB(BB->getTerminator());
				IRB.CreateStore(bb_num_value, gv);//done.
			}

			//obsolete
			/*if((strcmp(function_name, p_entry_function) == 0) && (strcmp(bb_name, F->back().getName().str().c_str()) == 0))
			{
				//errs() << "F name: " << F->getName() << " " << "BB name: " << BB->getName() << "\n";
				IRB.CreateCall(instru_dump_detection_result_f, initial_value_int_one);
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB.CreateLoad(gv);
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				IRB.CreateStore(load, gv);
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB.CreateLoad(gv);
				//IRB.CreateCall(instru_print_long_long_int_to_debug_f, load);
			}*/

			free(bb_name);
			bb_num_vector.clear();
			time_vector.clear();
			bb_num_vector1.clear();
			visited_vector1.clear();
			bb_num_vector2.clear();
			average_vector2.clear();
			stdev_vector2.clear();
			b_vector3.clear();
			c_vector3.clear();

		}

		//handle ecall entry and exit
		if((strcmp(function_name, p_entry_function) == 0) && (M.getFunction(p_reference_function) != NULL))
		{
			//dump all detection timing infomation at the end of ecall
			BasicBlock *BB = &(F->back());
			BasicBlock::iterator BI, BE;
			for(BI = BB->begin(), BE = BB->end(); BI != BE; BI++)
			{
				Instruction *II = BI;
				if(isa<ReturnInst>(II)) break; //|| isa<CallInst>(II)) break;
			}

			if(BI == BE)
			{
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "-----------found! ------------------------------------------1---------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";

				IRBuilder<> IRB1(F->back().getTerminator());


				//IRB1.CreateCall(instru_print_time_f, initial_value_int_zero);
				IRB1.CreateCall(instru_dump_detection_result_f, initial_value_int_zero);
				////IRB1.CreateCall(instru_set_loop_false_f, initial_value_int_zero);

				//get time again after our time consuming process
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//IRB1.CreateStore(load, gv);



			}
			else
			{

			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "-----------found! ------------------------------------------2---------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";


				IRBuilder<> IRB1((Instruction *)BI);
				errs() << "2\n";
				//IRB1.CreateCall(instru_print_time_f, initial_value_int_zero);
				IRB1.CreateCall(instru_dump_detection_result_f, initial_value_int_zero);
				////IRB1.CreateCall(instru_set_loop_false_f, initial_value_int_zero);

				//get time again after our time consuming process
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//IRB1.CreateStore(load, gv);

			}




			//init timer thread at the beginning of ecall
			//clear earlier ecall records at the beginning of ecall
			IRBuilder<> IRB(F->front().getFirstInsertionPt());
			//IRB.CreateCall(instru_init_f, initial_value_int_zero);
			//IRB.CreateCall(instru_print_time_f, initial_value_int_zero);
			//IRB.CreateCall(instru_clear_record_f, initial_value_int_zero);
		}



	}


	}


	//----------------------Mode 14 for histogram---------------------------//

	//optimized for performance, copied from mode 13


	if(mode == 13)
	{
	FILE *ttracefile;
	char ttracetemp[300];
	strcpy(ttracetemp, currentd);
	strcat(ttracetemp, "/ttracedata.txt");

	//if file does not exist
	if(access(ttracetemp, 0) == -1)
	{
	//-------------------processing tgdata.txt-----------------//
	//map for quick access
	llvm::StringMap<struct bb_num_s*> bbmap;

	int longest_f = 0, longest_bb = 0;

	//get global bb_num, type1, type2
	FILE *gbfile;
	char tgtemp3[300];
	strcpy(tgtemp3, currentd);
	strcat(tgtemp3, "/tgdata.txt");
	gbfile = fopen(tgtemp3, "r");
	if(gbfile)
	{
		char *line = NULL;
		size_t len = 0;
		ssize_t read;
		int count = 0;
		struct bb_num_s *ti;
		while((read = getline(&line, &len, gbfile)) != -1)
		{
			//leave out last character '\n'
			line[read-1] = '\0';
			if(count % 4 == 0)
			{
				//function name
				ti = (struct bb_num_s*) malloc (sizeof(struct bb_num_s));
				ti->function_name = (char *) malloc(300);
				strcpy(ti->function_name, line);
			}
			else if(count % 4 == 1)
			{
				//bb name
				ti->bb_name = (char *) malloc(300);
				strcpy(ti->bb_name, line);			
			}
			else if(count % 4 == 2)
			{
				//type1
				ti->type1 = atoi(line);
			}
			else if(count % 4 == 3)
			{
				//type2 and bb global num
				ti->type2 = atoi(line);
				ti->bb_num = (count - 3) / 4;
				bb_num_s_list.push_back(*ti);
				char temp[300];
				strcpy(temp, ti->function_name);
				strcat(temp, ti->bb_name);
				//errs() << temp << "\n";
				std::string tempstr(temp);
				//errs() << tempstr << "\n";
				bbmap[tempstr] = ti;
				//errs() << "ti->function_name: " << ti->function_name << "length:" << strlen(ti->function_name) << "\n";
				//if(strlen(ti->function_name) > longest_f) longest_f = strlen(ti->function_name);
				//if(strlen(ti->bb_name) > longest_bb) longest_bb = strlen(ti->bb_name);
			}

			
			count++;
		}
		fclose(gbfile);
	}
	else
	{
		errs() << "Timed Execution Configration Error: We should have a global basic block file.\n";
		exit(-1);
	}

	/*errs() << "longest function name: " << longest_f << "\n";
	errs() << "longest bb name: " << longest_bb << "\n";

	if(M.getFunction("CRYPTO_num_locks") != NULL)
	{
	FILE *ttfile;
	char tgtemp[120];
	strcpy(tgtemp, currentd);
	strcat(tgtemp, "/my3.txt");
	ttfile = fopen(tgtemp, "a");
	fprintf(ttfile, "%d\n%d\n", longest_f, longest_bb);
	fclose(ttfile);
	}*/

	/*struct bb_num_s* mapt = bbmap["EVP_CIPHER_CTX_freeEVP_CIPHER_CTX_cleanup.exit"];
	if(mapt == NULL) errs() << "mapt == NULL\n";
	else errs() << "the data found in maps is: " << "function name: " << mapt->function_name << "bb name: " 
		<< mapt->bb_name << "bb num: " << mapt->bb_num << "type1 flag: " << mapt->type1 
		<< "type2 flag: " << mapt->type2 << "\n";*/

	/*if(M.getFunction("ecall_DoNumSort") != NULL)
	{
	for(std::vector<struct bb_num_s>::iterator it = bb_num_s_list.begin() ; it != bb_num_s_list.end(); ++it)
	{
		FILE *file;
		char tgtemp[120];
		strcpy(tgtemp, currentd);
		strcat(tgtemp, "/my.txt");
		file = fopen(tgtemp, "a");
		//printf("%s\n",str);
		//fprintf(file, "%s\n%s\n%lu\n", function_name, bb_name, t);
		fprintf(file, "%s\n%s\n%d\n%d\n%d\n", it->function_name, it->bb_name, it->bb_num, it->type1, it->type2);
		fclose(file);
	}
	}
	bb_num_s_list.clear();*/




	//-------------------processing tdata.txt ttdata.txt-----------------//

	FILE *datafile, *tracefile;
	char tgtemp1[300];
	strcpy(tgtemp1, currentd);
	strcat(tgtemp1, "/tdata.txt");
	char tgtemp2[300];
	strcpy(tgtemp2, currentd);
	strcat(tgtemp2, "/ttdata.txt");
	datafile = fopen(tgtemp1,"r");
	tracefile = fopen(tgtemp2,"r");
	if(datafile)
	{
		if(tracefile)
		{
			char *line1 = NULL;
			size_t len1 = 0;
			ssize_t read1;
			int count1 = 0;
			char *line2 = NULL;
			size_t len2 = 0;
			ssize_t read2;
			int count2 = 0;
			char *line3= NULL;
			size_t len3 = 0;
			ssize_t read3;

			while (((read1 = getline(&line1, &len1, datafile)) != -1) 
				&& ((read2 = getline(&line2, &len2, tracefile)) != -1)
				&& ((read3 = getline(&line3, &len3, tracefile)) != -1))
			{
				//leave out last character '\n'
				line1[read1-1] = '\0';
				line2[read2-1] = '\0';
				line3[read3-1] = '\0';
				struct training_info *ti = (struct training_info*) malloc (sizeof(struct training_info));
				ti->bb_time = atoi(line1);
				ti->function_name = (char *) malloc(300);
				ti->bb_name = (char *) malloc(300);
				strcpy(ti->function_name, line2);
				strcpy(ti->bb_name, line3);
				char temp[300];
				strcpy(temp, ti->function_name);
				strcat(temp, ti->bb_name);
				struct bb_num_s* mapt = bbmap[temp];
				//if(mapt == NULL) errs() << "mapt == NULL\n";
				//else errs() << "the data found in maps is: " << "function name: " << mapt->function_name 
					//<< "bb name: " << mapt->bb_name << "bb num: " << mapt->bb_num << "type1 flag: " 
					//<< mapt->type1 << "type2 flag: " << mapt->type2 << "\n";
				if(mapt == NULL)
				{
					errs() << "--------------- mapt == NULL ----------------\n";
					FILE *file;
					char tgtemp[120];
					strcpy(tgtemp, currentd);
					strcat(tgtemp, "/my2.txt");
					file = fopen(tgtemp, "a");
					fprintf(file, "%s\n%s\n", ti->function_name, ti->bb_name);
					fclose(file);
					ti->bb_num = -1;
					ti->type1 = -1;
					ti->type2 = -1;
				}
				else
				{
					ti->bb_num = mapt->bb_num;
					ti->type1 = mapt->type1;
					ti->type2 = mapt->type2;
				}
				info_list.push_back(*ti);
			}
			fclose(datafile);
			fclose(tracefile);
		}
		else
		{
			errs() << "Timed Execution Configration Error: We should have a trace file.\n";
			exit(-1);
		}
	}
	else
	{
		errs() << "Timed Execution Configration Error: We should have a data file.\n";
		exit(-1);
	}
	bbmap.clear();
	bb_num_s_list.clear();


	/*if(M.getFunction("ecall_DoNumSort") != NULL)
	{
	for(std::vector<struct training_info>::iterator trit = info_list.begin() ; trit != info_list.end(); ++trit)
	{
		FILE *file;
		char tgtemp[120];
		strcpy(tgtemp, currentd);
		strcat(tgtemp, "/my1.txt");
		file = fopen(tgtemp, "a");
		//printf("%s\n",str);
		//fprintf(file, "%s\n%s\n%lu\n", function_name, bb_name, t);
		fprintf(file, "%s\n%s\n%d\n%d\n%d\n%d\n", trit->function_name, trit->bb_name, trit->bb_time, trit->bb_num, trit->type1, trit->type2);
		fclose(file);

	}
	}*/
	//info_list.clear();




	/*obsolete
	//mark trace nodes type1 and type2
	//mark bb_num
	for(std::vector<struct bb_num_s>::iterator it = bb_num_s_list.begin() ; it != bb_num_s_list.end(); ++it)
	{
		markBBNumType1Type2Info(it->function_name, it->bb_name, it->bb_num, it->type1, it->type2);
	}

	if(M.getFunction("CRYPTO_num_locks") != NULL)
	{
	printMark(M);
	}*/


	//process trace
	//collect trace info from trainging info
	//backwards in training info list
	int need_type1_bb_num = 0;
	struct trace_info *ti;
	for(std::vector<struct training_info>::iterator it = info_list.end() - 1; it >= info_list.begin(); it--)
	{
		if(need_type1_bb_num)
		{
			ti->context_type1_function_name = (char *) malloc(60);
			strcpy(ti->context_type1_function_name, it->function_name);
			ti->context_type1_bb_name = (char *) malloc(60);
			strcpy(ti->context_type1_bb_name, it->bb_name);
			ti->context_type1_bb_num = it->bb_num;
			trace_list.push_back(*ti);
			need_type1_bb_num = 0;
		}
		if(it->type2 == 1)// && it != info_list.begin())
		{
			ti = (struct trace_info*) malloc (sizeof(struct trace_info));
			ti->function_name = (char *) malloc(60);
			strcpy(ti->function_name, it->function_name);
			ti->tail_type2_bb_name = (char *) malloc(60);
			strcpy(ti->tail_type2_bb_name, it->bb_name);
			ti->bb_time = it->bb_time;
			need_type1_bb_num = 1;
			//special handling for the entry of the ecall
			if(it == info_list.begin())
			{
				ti->context_type1_function_name = (char *) malloc(60);
				strcpy(ti->context_type1_function_name, " ");
				ti->context_type1_bb_name = (char *) malloc(60);
				strcpy(ti->context_type1_bb_name, " ");
				ti->context_type1_bb_num = -1;
				trace_list.push_back(*ti);
			}
		}
	}

	//print for debugging
	/*if(M.getFunction("ecall_DoNumSort") != NULL)
	{
	for(std::vector<struct trace_info>::iterator it = trace_list.begin() ; it != trace_list.end(); it++)
	{
		FILE *file;
		char tgtemp[120];
		strcpy(tgtemp, currentd);
		strcat(tgtemp, "/my4.txt");
		file = fopen(tgtemp, "a");
		//fprintf(file, "%s\n%s\n%d\n%d\n%d\n%d\n", it->function_name, it->bb_name, it->bb_num, it->bb_time, it->type1, it->type2);
		
		//if(strcmp(M.getModuleIdentifier().c_str(), MAINFILE) == 0)
			fprintf(file, "%s\n%s\n%s\n%s\n%d\n%lu\n", 
				it->function_name, it->tail_type2_bb_name, it->context_type1_function_name, it->context_type1_bb_name, it->context_type1_bb_num, it->bb_time);
		
		fclose(file);
	}
	}

	//print for debugging
	int t2_count = 0;
	for(std::vector<struct training_info>::iterator it = info_list.end() - 1; it >= info_list.begin(); it--)
	{
		if(it->type2 == 1) t2_count++;
		//printf("%d\n", t2_count);
	}
	printf("t2_count: %d\n", t2_count);*/

	info_list.clear();

	//save to file
	for(std::vector<struct trace_info>::iterator it = trace_list.begin() ; it != trace_list.end(); it++)
	{
		//errs() << "save to file\n";
		FILE *file;
		char tgtemp[120];
		strcpy(tgtemp, currentd);
		strcat(tgtemp, "/ttracedata.txt");
		file = fopen(tgtemp, "a");
			fprintf(file, "%s\n%s\n%s\n%s\n%d\n%lu\n", 
				it->function_name, it->tail_type2_bb_name, it->context_type1_function_name, it->context_type1_bb_name, it->context_type1_bb_num, it->bb_time);
		fclose(file);
	}
	}
	//file exists
	else
	{
	//errs() << "ttracedata.txt exists.\n";
	FILE *gbfile;
	char tgtemp3[300];
	strcpy(tgtemp3, currentd);
	strcat(tgtemp3, "/ttracedata.txt");
	gbfile = fopen(tgtemp3, "r");
	if(gbfile)
	{
		char *line = NULL;
		size_t len = 0;
		ssize_t read;
		int count = 0;
		struct trace_info *ti;
		while((read = getline(&line, &len, gbfile)) != -1)
		{
			//leave out last character '\n'
			line[read-1] = '\0';
			//errs() << "line: " << line << "\n";
			if(count % 6 == 0)
			{
				//function name
				ti = (struct trace_info*) malloc (sizeof(struct trace_info));
				ti->function_name = (char *) malloc(300);
				strcpy(ti->function_name, line);
			}
			else if(count % 6 == 1)
			{
				//type2 bb name
				ti->tail_type2_bb_name = (char *) malloc(300);
				strcpy(ti->tail_type2_bb_name, line);			
			}
			else if(count % 6 == 2)
			{
				//context type1 function name
				ti->context_type1_function_name = (char *) malloc(300);
				strcpy(ti->context_type1_function_name, line);			
			}
			else if(count % 6 == 3)
			{
				//context type1 bb name
				ti->context_type1_bb_name = (char *) malloc(300);
				strcpy(ti->context_type1_bb_name, line);			
			}
			else if(count % 6 == 4)
			{
				//context type1 bb num
				ti->context_type1_bb_num = atoi(line);
			}
			else if(count % 6 == 5)
			{
				//type2 and bb global num
				ti->bb_time = atoi(line);

				//errs() << "ti->context_type1_function_name: " << ti->context_type1_function_name << "\n";
				//errs() << "ti->context_type1_bb_name: " << ti->context_type1_bb_name << "\n";

				trace_list.push_back(*ti);
			}
			count++;
		}
		fclose(gbfile);
	}
	else
	{
		errs() << "Timed Execution Configration Error: We should have a processed trace file.\n";
		exit(-1);
	}

	}


	//instrument type1 nodes
	//type1 nodes put its bb_num to global variable pre_bb_num
	//find every bb in this module first and then traverse trace_list

	int f_count=0;
	for(Module::iterator MI = M.begin(), ME = M.end(); MI != ME; MI++)
	{
		Function *F = MI;
		char* function_name = (char*)malloc(60);
		strcpy(function_name, F->getName().str().c_str());
		int bb_count =0;
		for(Function::iterator FI = MI->begin(), FE = MI->end(); FI != FE; FI++)
		{	
			BasicBlock *BB = FI;
			char* bb_name = (char*)malloc(180);
			strcpy(bb_name, BB->getName().str().c_str());
			IRBuilder<> IRB(BB->getTerminator());
			//errs() << function_name << " " << bb_name << "\n";
			int type1 = -1, type2 = -1;
			std::vector<int> bb_num_vector;
			std::vector<unsigned long> time_vector;
			std::vector<int> bb_num_vector1;
			std::vector<int> visited_vector1;
			std::vector<int> bb_num_vector2;
			std::vector<double> average_vector2;
			std::vector<double> stdev_vector2;
			std::vector<double> b_vector3;
			std::vector<double> c_vector3;
			int context_type1_bb_num = -1;

			//obsolete
			//handle the ecall entry and exit
			/*if((strcmp(function_name, p_entry_function) == 0) && (strcmp(bb_name, "entry") == 0))
			{
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//LoadInst *last_time_load = IRB.CreateLoad(gv);
				//IRB.CreateStore(initial_value_int_zero, gv);


				//IRBuilder<> IRB1(BB->getFirstInsertionPt());
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//IRB1.CreateCall(instru_print_long_long_int_to_debug_f, load);


				//print for debugging
				//IRB.CreateCall(instru_print_int_to_debug_f, last_time_load);
				//IRB.CreateCall(instru_print_int_to_debug_f, load);

				//init timer thread at the beginning of ecall
				//clear earlier ecall records at the beginning of ecall
				IRBuilder<> IRB1(F->front().getFirstInsertionPt());
				IRB1.CreateCall(instru_init_f, initial_value_int_zero);
				//IRB1.CreateCall(instru_clear_record_f, initial_value_int_zero);


			}*/

			//errs() << "trace_list.size(): " << trace_list.size() << "\n";
			for(std::vector<struct trace_info>::iterator it = trace_list.begin() ; it != trace_list.end(); it++)
			{
				//errs() << "it->context_type1_function_name: " << it->context_type1_function_name << "\n";
				//errs() << "it->context_type1_bb_name: " << it->context_type1_bb_name << "\n";
				//check if this one is type1
				if((strcmp(it->context_type1_function_name, function_name) == 0) && (strcmp(it->context_type1_bb_name, bb_name) == 0))
				{
					type1 = 1;
					context_type1_bb_num = it->context_type1_bb_num;
				}
				//check if any type2 nodes is this one
				if((strcmp(it->function_name, function_name) == 0) && (strcmp(it->tail_type2_bb_name, bb_name) == 0))
				{
					type2 = 1;
					//errs() << "type2: " << function_name << " " << bb_name << "\n";
					bb_num_vector.push_back(it->context_type1_bb_num);
					time_vector.push_back(it->bb_time);
				}
			}
			//instrument type2 first
			if(type2 == 1)
			{

				//errs() << function_name << " " << bb_name << "\n";
				errs() << "type2!\n";
				//errs() << "size of vector: " << bb_num_vector.size();
				//for(std::vector<int>::iterator it = bb_num_vector.begin() ; it != bb_num_vector.end(); it++)
					//for(std::vector<unsigned long>::iterator itt = time_vector.begin() ; itt != time_vector.end(); itt++)
						//errs() << *it << " " << *itt << ", ";
				//errs() << "\n";
				//get average and stdev
				//copy bb_num_vector to bb_num_vector1, bb_num_vector1 works as a temp vector with UNIQUE values
				for(std::vector<int>::iterator it = bb_num_vector.begin() ; it != bb_num_vector.end(); it++)
				{
					int in_it = 0;
					for(std::vector<int>::iterator itt = bb_num_vector1.begin() ; itt != bb_num_vector1.end(); itt++)
						if(*it == *itt) in_it = 1;
					if(in_it == 0)bb_num_vector1.push_back(*it);
				}
				errs() << "size of vector: " << bb_num_vector1.size() << "\n";
				//initialize visited_vector1 as all 0;
				for(std::vector<int>::iterator it = bb_num_vector.begin() ; it != bb_num_vector.end(); it++)
					visited_vector1.push_back(0);
				//check each value in bb_num_vector1
				for(std::vector<int>::iterator it = bb_num_vector1.begin() ; it != bb_num_vector1.end(); it++)
				{
					int count = 0;
					double average = -1.0;
					double stdev = -1.0;
					std::vector<unsigned long> specific_vector;
					//process everyone in bb_num_vector that has such value
					std::vector<int>::iterator itt = bb_num_vector.begin();
					std::vector<int>::iterator ittt = visited_vector1.begin();
					std::vector<unsigned long>::iterator itttt = time_vector.begin();
					while(itt != bb_num_vector.end() && ittt != visited_vector1.end() && itttt != time_vector.end())
					{
						//if it is visited before, do not bother that
						if(*itt == *it && *ittt == 0)
						{
							//mark as visited
							*ittt = 1;
							count++;
							specific_vector.push_back(*itttt);
						}
						itt++;ittt++;itttt++;
					}
					//calculate average
					average = 0;
					for(std::vector<unsigned long>::iterator myit = specific_vector.begin() ; myit != specific_vector.end(); myit++)
						average += *myit;
					average /= count;
					//calculate stdev
					stdev = 0;
					//errs() << "data:\n";
					for(std::vector<unsigned long>::iterator myit = specific_vector.begin() ; myit != specific_vector.end(); myit++)
					{
						//errs() << *myit << " ";
						stdev = stdev + (*myit - average) * (*myit - average);
					}
					//errs() << "\ncount: " << count << "\n";
					stdev /= count;
					stdev = sqrt(stdev);
					//errs() << "stdev: " << stdev << "\n";
					bb_num_vector2.push_back(*it);
					average_vector2.push_back(average);
					stdev_vector2.push_back(stdev);
				}
				std::vector<int>::iterator myit = bb_num_vector2.begin();
				std::vector<double>::iterator myit1 = average_vector2.begin();
				std::vector<double>::iterator myit2 = stdev_vector2.begin();

				//print for debugging
				while(myit != bb_num_vector2.end() && myit1 != average_vector2.end() && myit2 != stdev_vector2.end())
				{
					errs() << "prior bb num: " << *myit << " average: " << *myit1 << " stdev: " << *myit2 << "\n";
					myit++; myit1++; myit2++;
				}


				errs() << "**************************************************type2!\n";



				//transform structure
				/*//Value *mine_f = M.getOrInsertFunction("mine", VoidTy, I64Ty, nullptr);
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB.CreateLoad(gv);
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				LoadInst *lload = IRB.CreateLoad(gv);

				TerminatorInst *I1 = BB->getTerminator();
				Instruction *nop = BinaryOperator::Create(Instruction::Add, initial_value_int_zero, initial_value_int_zero);
				BB->getInstList().insert(I1, nop);
				BasicBlock *newBB1 = BB->splitBasicBlock(nop, "newbasicblock2");

				I1 = BB->getTerminator();
				nop = BinaryOperator::Create(Instruction::Add, initial_value_int_zero, initial_value_int_zero);
				//CallInst *callv = CallInst::Create(mine_f, initial_value_int_zero);
				BB->getInstList().insert(I1, nop);
				BasicBlock *newBB2 = BB->splitBasicBlock(nop, "newbasicblock3");

				I1 = BB->getTerminator();
				//Value * cmpv = IRB.CreateICmpUGT(lload, load);
				BranchInst *bran1 = BranchInst::Create(newBB1, newBB2, CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_EQ, lload, load, "compare", I1));
				ReplaceInstWithInst(I1, bran1);*///

				//add instructions
				//add to BB, that is, kind of front
				IRBuilder<> IRB1(BB->getTerminator());
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB1.CreateLoad(gv);
				Value *curr = load;
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				LoadInst *last_time_load = IRB1.CreateLoad(gv);
				IRB1.CreateStore(load, gv);
				Value *detect_result_sub_inst = IRB1.CreateSub(load, last_time_load);

				int vector_size = bb_num_vector2.size();
				int my_i;
				myit1 = average_vector2.begin();
				myit2 = stdev_vector2.begin();
				for(my_i = 0; my_i < vector_size; my_i++)
				{
					b_vector3.push_back(*myit1 - *myit2);
					c_vector3.push_back(*myit1 + page_fault_average - *myit2 - page_fault_stdev);
					myit1++; myit2++;
				}

				//errs() << "page_fault_average: " << page_fault_average << "page_fault_stdev: " << page_fault_stdev << "\n";

				//print for debugging, b_vector3 and c_vector3
				std::vector<double>::iterator mybit = b_vector3.begin();
				std::vector<double>::iterator mycit = c_vector3.begin();
				while((mybit != b_vector3.end()) && (mycit != c_vector3.end()))
				{
					errs() << "b: " << *mybit << " c: " << *mycit << "\n";
					mybit++;mycit++;
				}
				gv = M.getGlobalVariable(StringRef("pre_bb_num"), true);
				load = IRB1.CreateLoad(gv);
				myit = bb_num_vector2.begin();
				mybit = b_vector3.begin();
				mycit = c_vector3.begin();
				//if(*mycit < 3) printf("*mycit: %lf\n", *mycit);






				/*if(vector_size == 1)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, (int)*myit);
					Constant *mybit_value_int = ConstantInt::get(I64Ty, (int)*mybit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, (int)*mycit);


					//Constant *mybit_value_double = ConstantFP::get(DoubleTy, *mybit);
					//Constant *mycit_value_double = ConstantFP::get(DoubleTy, *mycit);



					//errs() << "*mycit: " << *mycit << "\n";
					Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
					Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
					Value *args[] = {load, detect_result_sub_inst, last_time_load, curr, myit_value_int, mybit_value_int, mycit_value_int, str_para1, str_para2};
					//Value *args[] = {load, detect_result_sub_inst, last_time_load, curr, myit_value_int, mybit_value_double, mycit_value_double, str_para1, str_para2};

					//IRBuilder<> IRB(newBB2->getTerminator());
					IRBuilder<> IRB(BB->getTerminator());
					IRB.CreateCall(instru_detect1_f, args);
				}
				else if(vector_size == 2)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mybit_value_int = ConstantInt::get(I64Ty, *mybit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);
					Constant *myit1_value_int = ConstantInt::get(I64Ty, *(myit+1));
					Constant *mybit1_value_int = ConstantInt::get(I64Ty, *(mybit+1));
					Constant *mycit1_value_int = ConstantInt::get(I64Ty, *(mycit+1));
					Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
					Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
					Value *args[] = {load, detect_result_sub_inst, last_time_load, curr, myit_value_int, mybit_value_int, mycit_value_int,
								myit1_value_int, mybit1_value_int, mycit1_value_int, str_para1, str_para2};
					//IRBuilder<> IRB(newBB2->getTerminator());
					IRBuilder<> IRB(BB->getTerminator());
					IRB.CreateCall(instru_detect2_f, args);
				}
				else if(vector_size == 3)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mybit_value_int = ConstantInt::get(I64Ty, *mybit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);
					Constant *myit1_value_int = ConstantInt::get(I64Ty, *(myit+1));
					Constant *mybit1_value_int = ConstantInt::get(I64Ty, *(mybit+1));
					Constant *mycit1_value_int = ConstantInt::get(I64Ty, *(mycit+1));
					Constant *myit2_value_int = ConstantInt::get(I64Ty, *(myit+2));
					Constant *mybit2_value_int = ConstantInt::get(I64Ty, *(mybit+2));
					Constant *mycit2_value_int = ConstantInt::get(I64Ty, *(mycit+2));
					Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
					Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
					Value *args[] = {load, detect_result_sub_inst, last_time_load, curr, myit_value_int, mybit_value_int, mycit_value_int,
								myit1_value_int, mybit1_value_int, mycit1_value_int,
								myit2_value_int, mybit2_value_int, mycit2_value_int, str_para1, str_para2};
					//IRBuilder<> IRB(newBB2->getTerminator());
					IRBuilder<> IRB(BB->getTerminator());
					IRB.CreateCall(instru_detect3_f, args);
				}
				else if(vector_size == 4)
				{
					Constant *myit_value_int = ConstantInt::get(I64Ty, *myit);
					Constant *mybit_value_int = ConstantInt::get(I64Ty, *mybit);
					Constant *mycit_value_int = ConstantInt::get(I64Ty, *mycit);
					Constant *myit1_value_int = ConstantInt::get(I64Ty, *(myit+1));
					Constant *mybit1_value_int = ConstantInt::get(I64Ty, *(mybit+1));
					Constant *mycit1_value_int = ConstantInt::get(I64Ty, *(mycit+1));
					Constant *myit2_value_int = ConstantInt::get(I64Ty, *(myit+2));
					Constant *mybit2_value_int = ConstantInt::get(I64Ty, *(mybit+2));
					Constant *mycit2_value_int = ConstantInt::get(I64Ty, *(mycit+2));
					Constant *myit3_value_int = ConstantInt::get(I64Ty, *(myit+3));
					Constant *mybit3_value_int = ConstantInt::get(I64Ty, *(mybit+3));
					Constant *mycit3_value_int = ConstantInt::get(I64Ty, *(mycit+3));
					Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
					Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
					Value *args[] = {load, detect_result_sub_inst, last_time_load, curr, myit_value_int, mybit_value_int, mycit_value_int,
								myit1_value_int, mybit1_value_int, mycit1_value_int,
								myit2_value_int, mybit2_value_int, mycit2_value_int,
								myit3_value_int, mybit3_value_int, mycit3_value_int, str_para1, str_para2};
					//IRBuilder<> IRB(newBB2->getTerminator());
					IRBuilder<> IRB(BB->getTerminator());
					IRB.CreateCall(instru_detect4_f, args);
				}*/


				Constant *myit_value_int = ConstantInt::get(I64Ty, 1);
				Constant *mybit_value_int = ConstantInt::get(I64Ty, 2);
				Constant *mycit_value_int = ConstantInt::get(I64Ty, 3);
				Constant *str_para1 = createStringArg((char *)F->getName().str().c_str(), F);
				Constant *str_para2 = createStringArg((char *)BB->getName().str().c_str(), F);
				Value *args[] = {myit_value_int, myit_value_int, myit_value_int, myit_value_int, myit_value_int, mybit_value_int, mycit_value_int, str_para1, str_para2};
				////IRBuilder<> IRB2(newBB2->getTerminator());
				//IRB2.CreateCall(instru_detect1_f, args);



				//add to newBB1, that is, the end
				////IRBuilder<> IRB3(newBB1->getTerminator());
				IRBuilder<> IRB3(BB->getTerminator());
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB3.CreateLoad(gv);
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				IRB3.CreateStore(load, gv);



			}


			if(type1 == 1)
			{
				//errs() << "type1!\n";
				//errs() << function_name << " " << bb_name << " " << context_type1_bb_num << "\n";
				Constant *bb_num_value = ConstantInt::get(I64Ty, context_type1_bb_num);
				gv = M.getGlobalVariable(StringRef("pre_bb_num"), true);
				IRBuilder<> IRB(BB->getTerminator());
				IRB.CreateStore(bb_num_value, gv);//done.
			}

			//obsolete
			/*if((strcmp(function_name, p_entry_function) == 0) && (strcmp(bb_name, F->back().getName().str().c_str()) == 0))
			{
				//errs() << "F name: " << F->getName() << " " << "BB name: " << BB->getName() << "\n";
				IRB.CreateCall(instru_dump_detection_result_f, initial_value_int_one);
				gv = M.getGlobalVariable(StringRef("current_time"), true);
				load = IRB.CreateLoad(gv);
				gv = M.getGlobalVariable(StringRef("previous_time"), true);
				IRB.CreateStore(load, gv);
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB.CreateLoad(gv);
				//IRB.CreateCall(instru_print_long_long_int_to_debug_f, load);
			}*/

			free(bb_name);
			bb_num_vector.clear();
			time_vector.clear();
			bb_num_vector1.clear();
			visited_vector1.clear();
			bb_num_vector2.clear();
			average_vector2.clear();
			stdev_vector2.clear();
			b_vector3.clear();
			c_vector3.clear();

		}

		//handle ecall entry and exit
		if((strcmp(function_name, p_entry_function) == 0) && (M.getFunction(p_reference_function) != NULL))
		{
			//dump all detection timing infomation at the end of ecall
			BasicBlock *BB = &(F->back());
			BasicBlock::iterator BI, BE;
			for(BI = BB->begin(), BE = BB->end(); BI != BE; BI++)
			{
				Instruction *II = BI;
				if(isa<ReturnInst>(II)) break; //|| isa<CallInst>(II)) break;
			}

			if(BI == BE)
			{
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "-----------found! ------------------------------------------1---------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";

				IRBuilder<> IRB1(F->back().getTerminator());


				//IRB1.CreateCall(instru_print_time_f, initial_value_int_zero);
				IRB1.CreateCall(instru_dump_detection_result_f, initial_value_int_zero);
				////IRB1.CreateCall(instru_set_loop_false_f, initial_value_int_zero);

				//get time again after our time consuming process
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//IRB1.CreateStore(load, gv);



			}
			else
			{

			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "-----------found! ------------------------------------------2---------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";
			errs() << "----------------------------------------------------------------------------------\n";


				IRBuilder<> IRB1((Instruction *)BI);
				errs() << "2\n";
				//IRB1.CreateCall(instru_print_time_f, initial_value_int_zero);
				IRB1.CreateCall(instru_dump_detection_result_f, initial_value_int_zero);
				////IRB1.CreateCall(instru_set_loop_false_f, initial_value_int_zero);

				//get time again after our time consuming process
				//gv = M.getGlobalVariable(StringRef("current_time"), true);
				//load = IRB1.CreateLoad(gv);
				//gv = M.getGlobalVariable(StringRef("previous_time"), true);
				//IRB1.CreateStore(load, gv);

			}




			//init timer thread at the beginning of ecall
			//clear earlier ecall records at the beginning of ecall
			IRBuilder<> IRB(F->front().getFirstInsertionPt());
			//IRB.CreateCall(instru_init_f, initial_value_int_zero);
			//IRB.CreateCall(instru_print_time_f, initial_value_int_zero);
			//IRB.CreateCall(instru_clear_record_f, initial_value_int_zero);
		}



	}


	}

	return true;
}


//obsolete
/*void TimedExecution::markBBNumType1Type2Info(char *function_name, char *bb_name, int bb_count, int type1, int type2)
{
	int count = 0;
	for(std::vector<struct training_info>::iterator it = info_list.begin() ; it != info_list.end(); ++it)
	{
		if(strcmp(it->function_name,function_name) == 0 && strcmp(it->bb_name, bb_name) == 0)
		{
			it->bb_num = bb_count;
			it->type1 = type1;
			it->type2 = type2;
			//errs() << "bb_num " << count << ": " << it->function_name << " " << it->bb_name << " " << it->bb_num << "\n";
		}
		count++;
	}
}

char markfile[] = "/home/seclab/pro/graphene/LibOS/shim/test/apps/thread/openssl-1.0.2h/my2.txt";

void TimedExecution::printMark(Module &M)
{
	int count = 0;
	for(std::vector<struct training_info>::iterator it = info_list.begin() ; it != info_list.end(); ++it)
	{
		FILE *file;
		file = fopen(markfile, "a");
		fprintf(file, "%s\n%s\n%d\n%d\n%d\n%d\n", it->function_name, it->bb_name, it->bb_num, it->bb_time, it->type1, it->type2);
		//if(strcmp(M.getModuleIdentifier().c_str(), MAINFILE) == 0)fprintf(file, "%s\n%s\n%d\n%d\n%d\n%d\n", it->function_name, it->bb_name, it->bb_num, it->bb_time, it->type1, it->type2);
		fclose(file);
		count++;

		//if(it->type1 == 1 && it->type2 == 1)
		if(it->bb_num == -1)
		{
			//printf("%s, %s\n", it->function_name, it->bb_name);
			errs() << it->function_name << " " << it->bb_name << it->type1 << it->type2 << "\n";
			
		}	
	}
	//errs() << "count: " << count << "\n";
}*/



