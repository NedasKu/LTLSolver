#include <iostream>
#include <cstring>
#include <assert.h>
#include <utility>
#include <vector>
#include <string.h>
#include <algorithm>
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
    ALWAYS = '#',
    NEXT = '@'
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
    NAN
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
    std::string signVal;
    if (f->formula_left != nullptr) {

        if (oneArgOperand(f->operand.c_str()[0])) {
            return "(" + f->operand  + printFormula(f->formula_left) + printFormula(f->formula_right) + ")";
        }
        return "(" + printFormula(f->formula_left) + f->operand  + printFormula(f->formula_right) + ")";
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
void applyFormula(State *baseState, operations operation, std::vector<State*> &leaves){
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

            leaves.emplace_back(newState);
            leaves.emplace_back(newState2);
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

            leaves.emplace_back(newState);
            leaves.emplace_back(newState2);
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

            leaves.emplace_back(newState);
            leaves.emplace_back(newState2);
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

            leaves.emplace_back(newState);
            leaves.emplace_back(newState2);
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

            leaves.emplace_back(newState);
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

            leaves.emplace_back(newState);
            baseState->state_left = newState;
            break;
        case operations::LHSN:
            formula = getAllFormulas(newState->antecedent, operands::NEGATION);
            assert(!formula.empty());

            // Main Logic Code
            newState->succedent.emplace_back(formula[0]->formula_left);
            newState->antecedent.erase(std::remove(newState->antecedent.begin(), newState->antecedent.end(), formula[0]));
            // Main Logic Code End

            leaves.emplace_back(newState);
            baseState->state_left = newState;
            break;
        case operations::RHSN:
            formula = getAllFormulas(newState->succedent, operands::NEGATION);
            assert(!formula.empty());

            // Main Logic Code
            newState->antecedent.emplace_back(formula[0]->formula_left);
            newState->succedent.erase(std::remove(newState->succedent.begin(), newState->succedent.end(), formula[0]));
            // Main Logic Code End

            leaves.emplace_back(newState);
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

            leaves.emplace_back(newState);
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

            leaves.emplace_back(newState);
            baseState->state_left = newState;
            break;
        case operations::LHSAL:
            formula = getAllFormulas(newState->antecedent, operands::ALWAYS);
            assert(!formula.empty());

            // Main Logic Code
            generatedFormula->operand=operands::ALWAYS;
            generatedFormula->formula_left=formula[0];
            newState->antecedent.emplace_back(generatedFormula);

            newState->antecedent.erase(std::remove(newState->antecedent.begin(), newState->antecedent.end(), formula[0]));
            // Main Logic Code End

            leaves.emplace_back(newState);
            baseState->state_left = newState;
            break;
        default:
            assert(false);
    }
}

void printLeaves(std::vector<State*> leaves){
    std::cout << "--------------------" << std::endl;
    for (auto it: leaves){
        std::cout << "@@@@@@@@@@@" << std::endl;
        std::cout<< "antecedent" << std::endl;
        for (auto it2: it->antecedent){
            std::cout<< printFormula(it2 )<< std::endl;
        }
        std::cout<< "succedent" << std::endl;
        for (auto it2: it->succedent){
            std::cout<< printFormula(it2 )<< std::endl;
        }
        std::cout << "@@@@@@@@@@@" << std::endl;
    }
    std::cout << "--------------------" << std::endl;
}

void applySign(FormulaNode* formula, bool sign){
    if( formula == nullptr){
        return;
    }
    formula->sign = sign;
    if( formula->operand.c_str()[0] == operands::NEGATION) {
        sign = !sign;
    }
    applySign(formula->formula_left, sign);
    applySign(formula->formula_right, sign);
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

int main() {
    std::string exampleFormula = "((A)v(D))";
    std::string exampleFormula2 = "(((A)v(B))>((~(C))^(D)))";
    std::string exampleFormula3 = "(@((A)v(B)))";

    std::string set1 = "(Q)";
    std::string set2 = "(~(#((~(@(P)))v(@(Q)))))";
    std::string set3 = "(~(#((P)v(~(~(Q))))))";

    auto* for1 = new FormulaNode();
    auto* for2 = new FormulaNode();
    auto* for3 = new FormulaNode();

    State *exState = new State();


    auto* ff1 = parseAndFillFormula(*for1, set1);
    auto* ff2 = parseAndFillFormula(*for2, set2);
    auto* ff3 = parseAndFillFormula(*for3, set3);

    applySign(ff1, false);
    applySign(ff2, false);
    applySign(ff3, true);

    exState->antecedent.emplace_back(ff1);
    exState->antecedent.emplace_back(ff2);
    exState->succedent.emplace_back(ff3);

    std::vector<State*> leaves2;

    std::cout << printFormula(exState->antecedent[0]) <<std::endl;
    std::cout << printFormula(exState->antecedent[1]) <<std::endl;
    std::cout << printFormula(exState->succedent[0]) <<std::endl;
    //applyFormula();

    std::vector<FormulaNode*> allNodes;
    allNodes.insert(allNodes.end(), exState->antecedent.begin(), exState->antecedent.end());
    allNodes.insert(allNodes.end(), exState->succedent.begin(), exState->succedent.end());


    // Generating LScb and RScb

    std::vector<FormulaNode*> LScb;
    std::vector<FormulaNode*> RScb;

    std::vector<FormulaNode*> newNodes;
    for( int i =0; i<allNodes.size(); i++){
        if(allNodes[i] == nullptr){
            break;
        }

        if(!allNodes[i]->sign){
            if(!formulaExists(LScb,allNodes[i])){
                LScb.emplace_back(allNodes[i]);
                std::cout << "LScb " << printFormula(allNodes[i]) << std::endl;
            }
            if(allNodes[i]->operand.c_str()[0] == operands::ALWAYS){
                FormulaNode* newF =  new FormulaNode();
                newF->operand = operands::NEXT;
                newF->sign = false;
                newF->formula_left=allNodes[i];
                if(!formulaExists(LScb,newF)){
                    LScb.emplace_back(newF);
                    std::cout << "LScb U - " << printFormula(newF) << std::endl;
                }

            }

        }else{
            if(!formulaExists(RScb,allNodes[i])){
                RScb.emplace_back(allNodes[i]);
                std::cout << "RScb " << printFormula(allNodes[i]) << std::endl;
            }
            if(allNodes[i]->operand.c_str()[0] == operands::ALWAYS){
                FormulaNode* newF =  new FormulaNode();
                newF->operand = operands::NEXT;
                newF->sign = true;
                newF->formula_left=allNodes[i];
                if(!formulaExists(RScb,allNodes[i])){
                    RScb.emplace_back(newF);
                    std::cout << "RScb U - " << printFormula(newF) << std::endl;
                }
            }
        }

        if(allNodes[i]->formula_left != nullptr && allNodes[i]->formula_left->formula_left != nullptr){
            allNodes.emplace_back(allNodes[i]->formula_left);
        }
        if(allNodes[i]->formula_right != nullptr && allNodes[i]->formula_right->formula_left != nullptr){
            allNodes.emplace_back(allNodes[i]->formula_right);
        }
    }


    printLeaves(leaves2);



    State *demoState = new State();
    auto* f1 = new FormulaNode();
    auto* f2 = new FormulaNode();
    auto* f3 = new FormulaNode();
    auto* f4 = new FormulaNode();
    auto form = parseAndFillFormula( *f1, exampleFormula2);
    applySign(form,true);
    std::cout<< printFormula(form) << std::endl;
    demoState->succedent.emplace_back(form);
    //demoState->succedent.emplace_back(parseAndFillFormula( *f3, exampleFormula3));
    demoState->antecedent.emplace_back(parseAndFillFormula( *f4, exampleFormula3));
    demoState->antecedent.emplace_back(parseAndFillFormula( *f2, exampleFormula2));
    FormulaNode* f = new FormulaNode();
    parseAndFillFormula(*f, exampleFormula2);
    auto b = getAllFormulas(demoState->antecedent, operands::IMPLICATION);
    std::vector<State*> leaves;
    applyFormula(demoState, operations::NXT, leaves);
    printLeaves(leaves);
    int i = 0;

}
