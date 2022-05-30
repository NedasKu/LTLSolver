#include <iostream>
#include <cstring>
#include <assert.h>
#include <utility>
#include <vector>
#include <string.h>
#include <algorithm>
#include <stack>
#include <map>

// We need to have a
// > - implikacija
// v - unison sajunga
// ^ - sankirta
// ~ - neiginys
// ( - atsidarantis skliaustas
// ) - uzsidarantis skliaustas
// # - visada (always)
// @ - sekantis (next)
//
enum operands
{
    IMPLICATION = '>',
    UNISON = 'v',
    OVERLAP = '^',
    NEGATION = '~',
    ALWAYS = '@',
    NEXT = '$'
};

enum operations
{
    LHSA,
    RHSA,
    LHSO,
    RHSO,
    LHSN,
    RHSN,
    LHSI,
    RHSI,
    NXT,
    LHSAL,
    RHSAL,
    NAN,
    AXIOM
};
std::array<std::string, 13> opArray = {"LHSA",
                                       "RHSA",
                                       "LHSO",
                                       "RHSO",
                                       "LHSN",
                                       "RHSN",
                                       "LHSI",
                                       "RHSI",
                                       "NXT",
                                       "LHSAL",
                                       "RHSAL",
                                       "NAN",
                                       "AXIOM"
                                        };

enum BinaryNumber{
    zero = 0,
    one = 1,
    zeroB = 2,
    oneB = 3,
    star = 4,
};
std::array<std::string, 5> binaryArray = {
        "0",
        "1",
        "o",
        "i",
        "*"
};

class BinaryEncoding {
public:
    std::vector<BinaryNumber> antecedent;
    std::vector<BinaryNumber> succedent;
    BinaryEncoding() {
    }
};

enum brackets{
    OPENING_BRACKET = '(',
    CLOSING_BRACKET = ')',
};

char stringToChar(const std::string& str){
    if( str.length() > 1 ){
        assert(false);
    }
    return str.c_str()[0];
}

bool oneArgOperand(char operand){
    return operand == operands::NEGATION || operand == operands::ALWAYS || operand == operands::NEXT;
}

class FormulaNode {
public:
    std::string operand;
    bool sign;
    FormulaNode* formula_left;
    FormulaNode* formula_right;
    FormulaNode(){
        formula_left=nullptr;
        formula_right=nullptr;
    }
};

class State {
public:
    std::vector<FormulaNode*> antecedent;
    std::vector<FormulaNode*> succedent;
    State* previous;
    operations operation;
    BinaryEncoding encoding;

    State(){
        previous = nullptr;
        state_left= nullptr;
        state_right= nullptr;
        operation = NAN;
    }
    State* state_left;
    State* state_right;
};


bool isBranchingOperation (operations operation){
    return operation == operations::RHSA || operation == operations::LHSO
    || operation == operations::LHSI || operation == operations::RHSAL;
}




std::string printFormula(FormulaNode* f){
    if(f==nullptr){
        return "";
    }
    std::string signVal;
    if (f->formula_left != nullptr){
        if(f->sign) {
            signVal = "+";
        }else{
            signVal = "-";
        }
        if (oneArgOperand(f->operand.c_str()[0])){
            return "("+  f->operand + signVal + printFormula(f->formula_left)  + printFormula(f->formula_right)+")";
        }
        return "("+printFormula(f->formula_left) + f->operand + signVal + printFormula(f->formula_right)+")";
    }
    return f->operand;

}

std::string printFormulaUns(FormulaNode* f) {
    if (f == nullptr) {
        return "";
    }
    if (f->formula_left != nullptr) {

        if (oneArgOperand(f->operand.c_str()[0])) {
            return "(" + f->operand  + printFormulaUns(f->formula_left) + printFormulaUns(f->formula_right) + ")";
        }
        return "(" + printFormulaUns(f->formula_left) + f->operand  + printFormulaUns(f->formula_right) + ")";
    }
    return f->operand;
}
std::string printFormulaUnsNoBrackets(FormulaNode* f) {
    if (f == nullptr) {
        return "";
    }
    if (f->formula_left != nullptr) {

        if (oneArgOperand(f->operand.c_str()[0])) {
            return  f->operand  + printFormulaUnsNoBrackets(f->formula_left) + printFormulaUnsNoBrackets(f->formula_right);
        }
        return  printFormulaUnsNoBrackets(f->formula_left) + f->operand  + printFormulaUnsNoBrackets(f->formula_right);
    }
    return f->operand;
}

std::vector<FormulaNode*> getAllFormulas (std::vector<FormulaNode*> vector, operands operand){
    std::vector<FormulaNode*> result;
    for (const auto &item: vector) {
        if (stringToChar(item->operand) == operand){
            result.emplace_back(item);
        }
    }
    return result;
}

std::string splitFirstPart( const std::string& str, int sep){
    return str.substr(1,sep-1);
}
std::string splitOperand (const std::string& str, int sep){
    return str.substr(sep,1);
}
std::string splitSecondPart( const std::string& str, int sep){
    return str.substr(sep+1,str.length()-sep - 2);
}


bool validOperand(char operand){
    return operand == operands::NEGATION || operand == operands::ALWAYS
    || operand == operands::NEXT || operand == operands::IMPLICATION
    || operand == operands::OVERLAP || operand == operands::UNISON;
}

int findTopOperand (std::string formula){
    int count=0;
    int prevCount=0;
    std::string answer;

    for(int i = 0; i < formula.length(); i++){
        if(i==1){
            if(oneArgOperand(formula[i])){
                return i;
            }
        }
        prevCount = count;
        if (formula[i] == brackets::OPENING_BRACKET) {
            count++;
        } else if (formula[i] == brackets::CLOSING_BRACKET) {
            count--;
        }
        if (prevCount == 2 && count == 1){
            return i+1;
        }
    }
    return -1;
}

std::string stripLemmaBrackets(const std::string& lemma){
    return lemma.substr(1, lemma.length()-2);
}
// ( (AvB) -> ( ( ~C )^( ~(AvD) ) ) )
FormulaNode* parseAndFillFormula(FormulaNode &f, const std::string& formula) {
    int operandPos = findTopOperand(formula);
    f.formula_left = new FormulaNode();
    f.formula_right = new FormulaNode();

    if(operandPos<0){
        f.operand = stripLemmaBrackets(formula);
        return &f;
    }
    f.operand = splitOperand(formula,operandPos);
    assert(validOperand(stringToChar(f.operand)));
    if (operandPos > 0 && !oneArgOperand(stringToChar(f.operand))){
        parseAndFillFormula(*f.formula_left,splitFirstPart(formula, operandPos));
        parseAndFillFormula(*f.formula_right, splitSecondPart(formula,operandPos));
    }else if(oneArgOperand(stringToChar(f.operand)) && operandPos > 0){
        parseAndFillFormula(*f.formula_left, splitSecondPart(formula,operandPos));
    }
    return &f;
}

// Apply specified formula as an operation and emplace the new leaves in the given State vector
void applyFormula(State *baseState, operations operation, std::stack<State*> &leaves){
    State* newState = new State();
    State* newState2 = new State();
    FormulaNode* generatedFormula = new FormulaNode();
    newState->antecedent = baseState->antecedent;
    newState->succedent = baseState->succedent;
    newState->operation = operation;
    newState->previous = baseState;
    if(isBranchingOperation(operation)) {
        newState2->antecedent = baseState->antecedent;
        newState2->succedent = baseState->succedent;
        newState2->operation = operation;
        newState2->previous = baseState;
    }

    std::vector<FormulaNode*> nextAnte;
    std::vector<FormulaNode*> nextSucc;



    std::vector<FormulaNode*> formula;
    // Branching operations will need 2
    switch (operation) {
        case operations::RHSA:
            formula = getAllFormulas(newState->succedent, operands::OVERLAP);
            assert(!formula.empty());

            // Main Logic Code
            newState->succedent.emplace_back(formula[0]->formula_left);
            newState2->succedent.emplace_back(formula[0]->formula_right);
            newState->succedent.erase(std::remove(newState->succedent.begin(), newState->succedent.end(), formula[0]));
            newState2->succedent.erase(std::remove(newState2->succedent.begin(), newState2->succedent.end(), formula[0]));
            // Main Logic Code End

            leaves.push(newState);
            leaves.push(newState2);
            baseState->state_left = newState;
            baseState->state_right = newState2;
            break;
        case operations::LHSO:
            formula = getAllFormulas(newState->antecedent, operands::UNISON);
            assert(!formula.empty());

            // Main Logic Code
            newState->antecedent.emplace_back(formula[0]->formula_left);
            newState2->antecedent.emplace_back(formula[0]->formula_right);
            newState->antecedent.erase(std::remove(newState->antecedent.begin(), newState->antecedent.end(), formula[0]));
            newState2->antecedent.erase(std::remove(newState2->antecedent.begin(), newState2->antecedent.end(), formula[0]));
            // Main Logic Code End

            leaves.push(newState);
            leaves.push(newState2);
            baseState->state_left = newState;
            baseState->state_right = newState2;
            break;
        case operations::LHSI:
            formula = getAllFormulas(newState->antecedent, operands::IMPLICATION);
            assert(!formula.empty());

            // Main Logic Code
            newState->succedent.emplace_back(formula[0]->formula_left);
            newState2->antecedent.emplace_back(formula[0]->formula_right);
            newState->antecedent.erase(std::remove(newState->antecedent.begin(), newState->antecedent.end(), formula[0]));
            newState2->antecedent.erase(std::remove(newState2->antecedent.begin(), newState2->antecedent.end(), formula[0]));
            // Main Logic Code End

            leaves.push(newState);
            leaves.push(newState2);
            baseState->state_left = newState;
            baseState->state_right = newState2;
            break;
        case operations::RHSAL:
            formula = getAllFormulas(newState->succedent, operands::ALWAYS);
            assert(!formula.empty());

            // Main Logic Code
            newState->succedent.emplace_back(formula[0]->formula_left);

            generatedFormula->operand=operands::NEXT;
            generatedFormula->formula_left=formula[0];
            newState2->succedent.emplace_back(generatedFormula);


            newState->succedent.erase(std::remove(newState->succedent.begin(), newState->succedent.end(), formula[0]));
            newState2->succedent.erase(std::remove(newState2->succedent.begin(), newState2->succedent.end(), formula[0]));
            // Main Logic Code End

            leaves.push(newState);
            leaves.push(newState2);
            baseState->state_left = newState;
            baseState->state_right = newState2;
            break;
        case operations::LHSA:
            formula = getAllFormulas(newState->antecedent, operands::OVERLAP);
            assert(!formula.empty());

            // Main Logic Code
            newState->antecedent.emplace_back(formula[0]->formula_left);
            newState->antecedent.emplace_back(formula[0]->formula_right);
            newState->antecedent.erase(std::remove(newState->antecedent.begin(), newState->antecedent.end(), formula[0]));
            // Main Logic Code End

            leaves.push(newState);
            baseState->state_left = newState;
            break;
        case operations::RHSO:
            formula = getAllFormulas(newState->succedent, operands::UNISON);
            assert(!formula.empty());

            // Main Logic Code
            newState->succedent.emplace_back(formula[0]->formula_left);
            newState->succedent.emplace_back(formula[0]->formula_right);
            newState->succedent.erase(std::remove(newState->succedent.begin(), newState->succedent.end(), formula[0]));
            // Main Logic Code End

            leaves.push(newState);
            baseState->state_left = newState;
            break;
        case operations::LHSN:
            formula = getAllFormulas(newState->antecedent, operands::NEGATION);
            assert(!formula.empty());

            // Main Logic Code
            newState->succedent.emplace_back(formula[0]->formula_left);
            newState->antecedent.erase(std::remove(newState->antecedent.begin(), newState->antecedent.end(), formula[0]));
            // Main Logic Code End

            leaves.push(newState);
            baseState->state_left = newState;
            break;
        case operations::RHSN:
            formula = getAllFormulas(newState->succedent, operands::NEGATION);
            assert(!formula.empty());

            // Main Logic Code
            newState->antecedent.emplace_back(formula[0]->formula_left);
            newState->succedent.erase(std::remove(newState->succedent.begin(), newState->succedent.end(), formula[0]));
            // Main Logic Code End

            leaves.push(newState);
            baseState->state_left = newState;
            break;
        case operations::RHSI:
            formula = getAllFormulas(newState->succedent, operands::IMPLICATION);
            assert(!formula.empty());

            // Main Logic Code
            newState->antecedent.emplace_back(formula[0]->formula_left);
            newState->antecedent.emplace_back(formula[0]->formula_right);
            newState->succedent.erase(std::remove(newState->succedent.begin(), newState->succedent.end(), formula[0]));
            // Main Logic Code End

            leaves.push(newState);
            baseState->state_left = newState;
            break;
        case operations::NXT:
            formula = getAllFormulas(newState->antecedent, operands::NEXT);
            assert(!formula.empty());

            // Main Logic Code

            // Iterate through all formulas in both antecedent and succedent, leave only those that have
            // next as their operand and remove it.
            for (auto it : baseState->antecedent){
                if(it->operand.c_str()[0] == operands::NEXT){
                    nextAnte.emplace_back(it->formula_left);
                }
            }
            for (auto it : baseState->succedent){
                if(it->operand.c_str()[0] == operands::NEXT){
                    nextSucc.emplace_back(it->formula_left);
                }
            }
            newState->antecedent = nextAnte;
            newState->succedent = nextSucc;
            // Main Logic Code End

            leaves.push(newState);
            baseState->state_left = newState;
            break;
        case operations::LHSAL:
            formula = getAllFormulas(newState->antecedent, operands::ALWAYS);
            assert(!formula.empty());

            // Main Logic Code
            newState->antecedent.emplace_back(formula[0]->formula_left);

            generatedFormula->operand=operands::NEXT;
            generatedFormula->formula_left=formula[0];
            newState->antecedent.emplace_back(generatedFormula);
            newState->antecedent.erase(std::remove(newState->antecedent.begin(), newState->antecedent.end(), formula[0]));
            // Main Logic Code End

            leaves.push(newState);
            baseState->state_left = newState;
            break;
        default:
            assert(false);
    }
}

std::string operationToString(int operation){
    return opArray[operation];
}

std::string binaryNumberToString(int operation){
    return binaryArray[operation];
}

void printLeaves(std::stack<State*> leaves){
    while(!leaves.empty()) {
        State* leaf = leaves.top();
        for (auto it2: leaf->antecedent){
            std::cout<< printFormulaUns(it2)<< ", ";
        }
        std::cout<< "=> ";
        for (auto it2: leaf->succedent){
            std::cout<< printFormulaUns(it2)<< ", ";
        }
        leaves.pop();
        std::cout << operationToString(leaf->operation) << "|| ";
    }
    std::cout << std::endl;
}

void printLeavesNoBrackets(std::stack<State*> leaves){
    while(!leaves.empty()) {
        State* leaf = leaves.top();
        for (auto it2: leaf->antecedent){
            std::cout<< printFormulaUnsNoBrackets(it2)<< ", ";
        }
        std::cout<< "=> ";
        for (auto it2: leaf->succedent){
            std::cout<< printFormulaUnsNoBrackets(it2)<< ", ";
        }
        leaves.pop();
        std::cout << operationToString(leaf->operation) << "   ";
    }
    std::cout << std::endl;
}

void applySign(FormulaNode* formula, bool sign){
    if( formula == nullptr){
        return;
    }
    bool signImplication = sign;
    formula->sign = sign;
    if( formula->operand.c_str()[0] == operands::NEGATION) {
        sign = !sign;
        signImplication = !signImplication;
    }else if (formula->operand.c_str()[0] == operands::IMPLICATION){
        signImplication = !signImplication;
    }
    applySign(formula->formula_left, signImplication);
    applySign(formula->formula_right, sign);
}

bool formulaEquals(FormulaNode* formula1, FormulaNode* formula2){
    return strcmp(printFormulaUns(formula1).c_str(), printFormulaUns(formula2).c_str());
}

bool formulaExists(const std::vector<FormulaNode*>& source, FormulaNode* lookingFor){
    auto formula = printFormulaUns(lookingFor);

    for(auto it : source) {
        if(strcmp(printFormulaUns(it).c_str(), formula.c_str()) == 0){
            return true;
        }
    }
    return false;
}

bool formulaExistsSigned(const std::vector<FormulaNode*>& source, FormulaNode* lookingFor){
    auto formula = printFormula(lookingFor);

    for(auto it : source) {
        if(strcmp(printFormula(it).c_str(), formula.c_str()) == 0){
            return true;
        }
    }
    return false;
}

bool formulasNeedRevision(){
    return false;
}
std::vector<FormulaNode*> getAllPossibleFormulasFromState(std::vector<FormulaNode*> antecedent, std::vector<FormulaNode*> succedent){
    std::vector<FormulaNode*> allNodes;
    allNodes.insert(allNodes.end(), antecedent.begin(), antecedent.end());
    allNodes.insert(allNodes.end(), succedent.begin(), succedent.end());
    for(int i =0; i< allNodes.size(); i++){
        if(allNodes[i]->formula_left != nullptr && allNodes[i]->formula_left->formula_left != nullptr){
            allNodes.emplace_back(allNodes[i]->formula_left);
        }
        if(allNodes[i]->formula_right != nullptr && allNodes[i]->formula_right->formula_left != nullptr){
            allNodes.emplace_back(allNodes[i]->formula_right);
        }
    }
    return allNodes;
}
std::vector<FormulaNode*> getAllPossibleFormulasFromSingleState(std::vector<FormulaNode*> antecedent){
    std::vector<FormulaNode*> allNodes;
    allNodes.insert(allNodes.end(), antecedent.begin(), antecedent.end());
    for(int i =0; i< allNodes.size(); i++){
        if(allNodes[i]->formula_left != nullptr && allNodes[i]->formula_left->formula_left != nullptr){
            allNodes.emplace_back(allNodes[i]->formula_left);
        }
        if(allNodes[i]->formula_right != nullptr && allNodes[i]->formula_right->formula_left != nullptr){
            allNodes.emplace_back(allNodes[i]->formula_right);
        }
    }
    return allNodes;
}

std::vector<BinaryNumber> encodingFormula(std::vector<FormulaNode*> source, std::vector<bool> nonCyclicDomainIndex, const std::vector<FormulaNode*>& lookingFor, bool &needsChangingRootState, std::vector<FormulaNode*> rootState){
    std::vector<BinaryNumber> result;
    for(int i =0; i < source.size(); i++){
        if(formulaExists(lookingFor,source[i])){
            if(nonCyclicDomainIndex[i]){
                result.emplace_back(BinaryNumber::one);
            } else {
                result.emplace_back(BinaryNumber::oneB);
            }
        }else {
            if (formulaExistsSigned(rootState, source[i])){
                if(source[i]->operand.c_str()[0] == operands::NEXT && source[i]->formula_left != nullptr && source[i]->formula_left->operand.c_str()[0] == operands::ALWAYS){
                
                }else{
                    if(!formulaExists(getAllPossibleFormulasFromSingleState(lookingFor),source[i])){
                        result.emplace_back(BinaryNumber::star);
                        continue;
                    }
                }
            }
            if(nonCyclicDomainIndex[i]){
                result.emplace_back(BinaryNumber::zero);
            } else {
                result.emplace_back(BinaryNumber::zeroB);
            }
        }
    }
    return result;
}


std::vector<FormulaNode*> getAllSubformulas(std::vector<FormulaNode*> source){
    std::vector<FormulaNode*> subFormulas;
    subFormulas.emplace_back(source[0]);
    for(int i = 0; i< source.size(); i++){
        if(!formulaExistsSigned(subFormulas, source[i])){
            subFormulas.emplace_back(source[i]);
        }
        if(source[i]->formula_left != nullptr && source[i]->formula_left->formula_left != nullptr){
            source.emplace_back(source[i]->formula_left);
        }
        if(source[i]->formula_right != nullptr && source[i]->formula_right->formula_left != nullptr){
            source.emplace_back(source[i]->formula_right);
        }
    }
    return subFormulas;
}


void fillStateFormulas(std::vector<FormulaNode*> &antecedentOrSuccedent, std::vector<std::string> formulasInStringForm, bool sign) {
    for(auto it:formulasInStringForm){
        FormulaNode* node = new FormulaNode();
        auto result = parseAndFillFormula(*node, it);
        applySign(result, sign);
        antecedentOrSuccedent.emplace_back(result);
    }
}



std::vector<FormulaNode*> getLScb(std::vector<FormulaNode*> allNodes){
    std::vector<FormulaNode*> LScb;
    for(int i =0; i<allNodes.size(); i++) {
        if (!allNodes[i]->sign) {
            if (!formulaExists(LScb, allNodes[i])) {
                LScb.emplace_back(allNodes[i]);
            }
            if (allNodes[i]->operand.c_str()[0] == operands::ALWAYS) {
                FormulaNode *newF = new FormulaNode();
                newF->operand = operands::NEXT;
                newF->sign = false;
                newF->formula_left = allNodes[i];
                if (!formulaExists(LScb, newF)) {
                    LScb.emplace_back(newF);
                }
            }
        }
    }
    return LScb;
}



std::vector<FormulaNode*> getRScb(std::vector<FormulaNode*> allNodes){
    std::vector<FormulaNode*> RScb;
    for(int i =0; i<allNodes.size(); i++) {
        if (allNodes[i]->sign) {
            if(!formulaExists(RScb,allNodes[i])) {
                RScb.emplace_back(allNodes[i]);
            }
            if(allNodes[i]->operand.c_str()[0] == operands::ALWAYS){
                FormulaNode* newF =  new FormulaNode();
                newF->operand = operands::NEXT;
                newF->sign = true;
                newF->formula_left=allNodes[i];
                if(!formulaExists(RScb,newF)){
                    RScb.emplace_back(newF);
                }
            }
        }
    }
    return RScb;
}

// Return vector of FormulaNodes that encapsulate the formula domain.
std::vector<FormulaNode*> getAxiomDomain(std::vector<FormulaNode*> &LScb, std::vector<FormulaNode*> &RScb) {
    std::vector<FormulaNode*> axiomDomain;
    for(int i=0; i<LScb.size(); i++){
        for(int y = 0; y<RScb.size(); y++){
            if(formulaEquals(LScb[i], RScb[y])){
                axiomDomain.emplace_back(LScb[i]);
                LScb.insert(LScb.begin(), LScb[i]);
                RScb.insert(RScb.begin(), RScb[y]);
                LScb.erase(LScb.begin()+i+1);
                RScb.erase(RScb.begin()+y+1);
            }
        }
    }
    return axiomDomain;
}

// Obtained from LScb by dropping each formula, that formula- is not a sub-formula of any
std::vector<bool> getLSdl(std::vector<FormulaNode*> LScb) {
    std::vector<FormulaNode*> LSdlTest;
    for (auto it: LScb){
        if (it->operand.c_str()[0] == operands::ALWAYS) {
            applySign(it, false);
            FormulaNode* withNext = new FormulaNode();
            withNext->operand = operands::NEXT;
            withNext->sign = it->sign;
            withNext->formula_left = it;

            LSdlTest.emplace_back(it);
            LSdlTest.emplace_back(withNext);
        }
    }
    std::vector<FormulaNode*> LSdlTest2get = getAllSubformulas(LSdlTest);
    std::vector<bool> LSdl;
    for(int i=0;i<LScb.size(); i++){
        applySign(LScb[i], false);
        if(formulaExistsSigned(LSdlTest2get, LScb[i])){
            LSdl.emplace_back(true);
        }else{
            LSdl.emplace_back(false);
        }
    }
    return LSdl;
}
std::vector<bool> getRSdl(std::vector<FormulaNode*> LScb, std::vector<FormulaNode*> RScb){
    std::vector<FormulaNode*> RSdlTest;
    std::vector<bool> RSdl;
    for (auto it: LScb){
        if (it->operand.c_str()[0] == operands::ALWAYS) {
            applySign(it, false);
            RSdlTest.emplace_back(it);
        }
    }
    std::vector<FormulaNode*> RSdlTest2get = getAllSubformulas(RSdlTest);

    for(auto it: RScb){
        applySign(it, true);
        if(it->operand.c_str()[0] == operands::ALWAYS){
            RSdl.emplace_back(true);
        }else if (it->operand.c_str()[0] == operands::NEXT && it->formula_left->operand.c_str()[0] == operands::ALWAYS) {
            RSdl.emplace_back(true);
        }else if(formulaExistsSigned(RSdlTest2get, it)){
            RSdl.emplace_back(true);
        }else{
            RSdl.emplace_back(false);
        }
    }
    return RSdl;
}


void stateEncoding(State* rootState, State* encodedState){

    std::vector<FormulaNode*> allNodes = getAllPossibleFormulasFromState(rootState->antecedent, rootState->succedent);

    // Generating LScb and RScb
    std::vector<FormulaNode*> LScb = getLScb(allNodes);
    std::vector<FormulaNode*> RScb = getRScb(allNodes);

    // Searching for Axiom Domain of the given formulas
    std::vector<FormulaNode*> axiomDomain = getAxiomDomain(LScb, RScb);


    std::vector<bool> LSdl = getLSdl(LScb);
    std::vector<bool> RSdl = getRSdl(LScb, RScb);


    std::vector<FormulaNode*> allLScbNodes;
    std::vector<FormulaNode*> allRScbNodes;


    if (!(rootState->encoding.antecedent.empty() && rootState->encoding.succedent.empty())){
        std::vector<FormulaNode*> tempLS;
        for(int i = 0; i < rootState->encoding.antecedent.size(); i++){
            if(rootState->encoding.antecedent[i] == BinaryNumber::oneB || rootState->encoding.antecedent[i] == BinaryNumber::one){
                applySign(LScb[i], false);
                tempLS.emplace_back(LScb[i]);
            }
        }
        allLScbNodes = getAllPossibleFormulasFromSingleState(tempLS);

        std::vector<FormulaNode*> tempRS;
        for(int i = 0; i < rootState->encoding.succedent.size(); i++){
            if(rootState->encoding.succedent[i] == BinaryNumber::oneB || rootState->encoding.succedent[i] == BinaryNumber::one){
                applySign(RScb[i], true);
                tempRS.emplace_back(RScb[i]);
            }
        }
        allRScbNodes = getAllPossibleFormulasFromSingleState(tempRS);
    }



    bool needsChangingRootState = false;
    bool needsChangingRootState2 = false;
    // Checking Encodings
    BinaryEncoding code;
    code.antecedent = encodingFormula(LScb, LSdl, encodedState->antecedent, needsChangingRootState, allLScbNodes);
    code.succedent = encodingFormula(RScb, RSdl, encodedState->succedent, needsChangingRootState2, allRScbNodes);

    encodedState->encoding = code;

    if(encodedState->state_left != nullptr){
        if (needsChangingRootState || needsChangingRootState2){
            stateEncoding(encodedState, encodedState->state_left);
        }else{
            stateEncoding(rootState, encodedState->state_left);
        }
    }
    if(encodedState->state_right != nullptr) {
        if (needsChangingRootState || needsChangingRootState2) {
            stateEncoding(encodedState, encodedState->state_right);
        }else{
            stateEncoding(rootState, encodedState->state_right);
        }
    }

}



void printEncoding(BinaryEncoding encoding) {
    for (int i =0; i < encoding.antecedent.size(); i++){
        std::cout<< binaryNumberToString(encoding.antecedent[i]);
    }
    std::cout<< " => ";
    for (int i =0; i < encoding.succedent.size(); i++){
        std::cout<< binaryNumberToString(encoding.succedent[i]);
    }
    std::cout<<std::endl;
}

std::vector<operations> getAllAppliableFormulas(State* state){
    std::vector<operations> allOperations;
    for(auto i: state->antecedent){
        switch(i->operand.c_str()[0]){
            case operands::ALWAYS:
                allOperations.emplace_back(operations::LHSAL);
                break;
            case operands::NEXT:
                allOperations.emplace_back(operations::NXT);
                break;
            case operands::NEGATION:
                allOperations.emplace_back(operations::LHSN);
                break;
            case operands::IMPLICATION:
                allOperations.emplace_back(operations::LHSI);
                break;
            case operands::UNISON:
                allOperations.emplace_back(operations::LHSO);
                break;
            case operands::OVERLAP:
                allOperations.emplace_back(operations::LHSA);
                break;
            default:
                break;
        }
    }

    for(auto i: state->succedent){
        switch(i->operand.c_str()[0]){
            case operands::ALWAYS:
                allOperations.emplace_back(operations::RHSAL);
                break;
            case operands::NEXT:
                allOperations.emplace_back(operations::NXT);
                break;
            case operands::NEGATION:
                allOperations.emplace_back(operations::RHSN);
                break;
            case operands::IMPLICATION:
                allOperations.emplace_back(operations::RHSI);
                break;
            case operands::UNISON:
                allOperations.emplace_back(operations::RHSO);
                break;
            case operands::OVERLAP:
                allOperations.emplace_back(operations::RHSA);
                break;
            default:
                break;
        }
    }
    return allOperations;
}

void printTree(State* rootState) {
    std::stack<State*> layer;
    layer.push(rootState);
    std::stack<State*> nextLayer;
    while(!layer.empty()){
        printLeaves(layer);
        while(!layer.empty()){
            if(layer.top()->state_left!= nullptr){
                nextLayer.push(layer.top()->state_left);
            }
            if(layer.top()->state_right!= nullptr){
                nextLayer.push(layer.top()->state_right);
            }
            layer.pop();
        }
        layer = nextLayer;
        while(!nextLayer.empty()){
            nextLayer.pop();
        }
    }

}

void printTreeNoBrackets(State* rootState) {
    std::stack<State*> layer;
    layer.push(rootState);
    std::stack<State*> nextLayer;
    while(!layer.empty()){
        printLeavesNoBrackets(layer);
        while(!layer.empty()){
            auto temp = layer.top();
            layer.pop();
            if(temp->state_left!= nullptr){
                nextLayer.push(temp->state_left);
            }
            if(temp->state_right!= nullptr){
                nextLayer.push(temp->state_right);
            }
        }
        layer = nextLayer;
        while(!nextLayer.empty()){
            nextLayer.pop();
        }
    }

}

bool onlyNextLeft(std::vector<operations> operations){
    for(auto i: operations){
        if (i != operations::NXT){
            return false;
        }
    }
    return true;
}

bool isAxiom(State* state){
    for(int i=0; i<state->antecedent.size(); i++){
        if(formulaExists(state->succedent,state->antecedent[i])){
            return true;
        }
    }
    return false;
}

void printState(State* state){
    std::stack<State*> temp;
    temp.push(state);
    printLeavesNoBrackets(temp);
}


// https://stackoverflow.com/questions/36802354/print-binary-tree-in-a-pretty-way-using-c
void printBT(const std::string& prefix, State* node, bool isLeft)
{
    if( node != nullptr )
    {
        std::cout << prefix;

        std::cout << (isLeft ? "|--" : "L--" );

        // print the value of the node
        // Change between printing the encoding and the formulas themselves
        printEncoding(node->encoding);
        //printState(node);

        // enter the next tree level - left and right branch
        printBT( prefix + (isLeft ? "|   " : "    "), node->state_left, true);
        printBT( prefix + (isLeft ? "|   " : "    "), node->state_right, false);
    }
}

void printBT(State* node)
{
    printBT("", node, false);
}

// Loop checking functions
bool nonCyclicEncoding(BinaryEncoding encoding){
    for(int i = 0; i<encoding.succedent.size();i++){
        if(encoding.succedent[i] == BinaryNumber::oneB){
            return true;
        }
    }
    for(int i = 0; i<encoding.antecedent.size();i++){
        if(encoding.antecedent[i] == BinaryNumber::oneB){
            return true;
        }
    }
    return false;
}
std::string lazyPrintBinaryNumber(std::vector<BinaryNumber> first){
    std::string temp = "";
    for(int i = 0; i<first.size(); i++){
        if(first[i] == BinaryNumber::oneB || first[i] == BinaryNumber::one){
            temp += "1";
        }else if(first[i] == BinaryNumber::zero || first[i] == BinaryNumber::zeroB){
            temp += "0";
        }else if(first[i] == BinaryNumber::star){
            temp += "*";
        }
    }
    return temp;
}


bool binaryNumberEquals(std::string first, std::string second){
    return strcmp(first.c_str(), second.c_str());
}

std::string binaryMultiplication(std::vector<BinaryNumber> first, std::vector<BinaryNumber> second){
    std::string tempFirst = lazyPrintBinaryNumber(first);
    std::string tempSecond = lazyPrintBinaryNumber(second);
    std::string answer = "";
    for(int i =0; i<tempFirst.length(); i++){
        if(tempFirst[i] == '0'){
            answer+="0";
        }else if(tempFirst[i] == '*'){
            answer+="*";
        }else if(tempFirst[i] == tempSecond[i]){
            answer+="1";
        }else if(tempFirst[i] != tempSecond[i]){
            answer+="0";
        }
    }
    return answer;
}



bool loopCheck(BinaryEncoding first, BinaryEncoding second){
    if(nonCyclicEncoding(first)){
        return false;
    }
    if(nonCyclicEncoding(second)){
        return false;
    }
    if(binaryNumberEquals(lazyPrintBinaryNumber(first.antecedent), binaryMultiplication(first.antecedent, second.antecedent))){
        if(binaryNumberEquals(lazyPrintBinaryNumber(first.succedent), binaryMultiplication(first.succedent, second.succedent))){
            return true;
        }
    }
    return false;
}


int main() {
    // Simulating Getting initial formula from somewhere as two sets of std::vector<std::string>
    std::vector<std::string> antecedentFormulas2;
    std::vector<std::string> succedentFormulas2;

/*
    std::string set11 = "(((P)v(~((R)>(~(Q))))))>((~(Q))v(P)))";
    std::string set21 = "((P)v(((R)>(~(Q))))";
    antecedentFormulas2.emplace_back(set11);
    succedentFormulas2.emplace_back(set21);
*/



    std::string set11 = "(@(~(@((P)v(Q)))))";
    std::string set21 = "(@(~(@(P))))";
    antecedentFormulas2.emplace_back(set11);
    succedentFormulas2.emplace_back(set21);


    /*
    std::string form1 = "(P)";
    std::string form2 = "(Q)";
    std::string form3 = "(($(@(P)))v($(@(Q))))";
    std::string form4 = "($(@((P)v(Q))))";
    antecedentFormulas2.emplace_back(form1);
    antecedentFormulas2.emplace_back(form2);
    antecedentFormulas2.emplace_back(form3);
    succedentFormulas2.emplace_back(form4);

    */

    State* rootState2 = new State();
    fillStateFormulas(rootState2->antecedent, antecedentFormulas2, false);
    fillStateFormulas(rootState2->succedent, succedentFormulas2, true);

    // Generating LScb and RScb from Formula
    std::stack<State*> leaves;
    leaves.push(rootState2);
    std::stack<State*> nxtLeaves;

    bool finished = false;
    bool sequentDerivable = true;
    // Generation of a fully extended tree without the application of LTL formula next

    bool firstIteration = true;

    while(!finished){
        while(!leaves.empty()){
            State* state = leaves.top();
            leaves.pop();

            if(isAxiom(state)){
                state->operation = operations::AXIOM;
                continue;
            }

            auto formulas = getAllAppliableFormulas(state);

            // If there are no more formulas left to apply and the state is not an axiom
            // Then we can say that the sequent is not derivable in sequent calculus
            if (formulas.empty()){
                if(leaves.empty()){
                    sequentDerivable = false;
                    finished = true;
                    break;
                }else{
                    continue;
                }
            }

            if(onlyNextLeft(formulas)){
                nxtLeaves.push(state);
                continue;
            }
            for(auto it: formulas){
                if (it != operations::NXT){
                    applyFormula(state,it,leaves);
                    break;
                }
            }
            //printLeaves(leaves);
        }

        // If the sequentDerivable variable is set to false, then the sequent is not derivable,
        // if at this point the next formula leaves are empty, then the sequent is derivable
        // otherwise we have to do loop search and potentially apply the next rules.
        if (!sequentDerivable) {
            std::cout << "Sequent is not derivable" << std::endl;
            finished = true;
            break;
        }

        if (nxtLeaves.empty()){
            std::cout << "Sequent is derivable" << std::endl;
            finished = true;
            break;
        }

        // Here all of the states are encoded
        stateEncoding(rootState2, rootState2);


        std::cout << "Searching for derivation loops" << std::endl;
        while(!nxtLeaves.empty()){
            State* nodeToCheck = nxtLeaves.top();
            State* first = nodeToCheck;
            State* second = nodeToCheck->previous;
            State* temp = nodeToCheck;

            nxtLeaves.pop();
            bool loopFound = false;
            while(second!= nullptr && !loopFound){
                if (loopCheck(second->encoding, first->encoding)) {
                    loopFound = true;
                    // Loop Found Identifying Loop Type;
                }else{
                    if (second->previous!= nullptr){
                        second = second->previous;
                    }else{
                        if(first->previous != nullptr){
                            first = first->previous;
                            if(first-> previous!= nullptr){
                                second = first->previous;
                            }else{
                                // There are no more checks
                                break;
                            }
                        }else{
                            break;
                        }
                    }
                }
            }
            if (!loopFound){
                // If no loop is found we need to apply NXT operation
                applyFormula(temp, operations::NXT, leaves);
            }
        }
    }

    //std::cout << "Pretty Tree" << std::endl;
    printBT(rootState2);
}
