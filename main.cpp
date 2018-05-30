#pragma GCC diagnostic error "-std=c++11"           // 使用C++11标准编译
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <string>
#include <string.h>
#include <vector>
#include <algorithm>
#include <map>

using namespace std;

typedef map<char, vector<string>> AugmentedGrammar; // 拓广文法表
typedef map<string, int> GotoMap;                   // 状态转换表
typedef map<string, int> ReduceList;                // 递归式转换表
typedef vector<char> Terminator;                    // 终结符集
typedef vector<char> NonTerminator;                 // 非终结符集

ifstream fin("grammer.txt"); // 读入文法文件
bool isLR0 = true;           // 确认该文法可用LR0分析

// 结构体储存项目（拓广文法产生式）
struct AugmentedProduction
{
    char lhs;   // 产生式左部
    string rhs; // 产生式右部

    AugmentedProduction() {}

    // 单个状态项目构造函数
    AugmentedProduction(char _lhs, string _rhs) : lhs(_lhs), rhs(_rhs) {}
};

// LR(0)项目集类
class LR0Item
{
  private:
    // 项目集的项目列表（拓广文法产生式）
    vector<AugmentedProduction *> productions;

  public:
    // 每个项目集的导出边集合
    map<char, int> gotos;

    LR0Item() {}  // 默认构造函数
    ~LR0Item() {} // 默认析构函数

    // 在项目列表内添加新项目
    void Push(AugmentedProduction *p) { productions.push_back(p); }

    // 返回项目集内项目编号（返回目前项目列表内项目的数量）
    int Size() { return int(productions.size()); }

    // 检查当前项目集有无指定项目
    bool Contains(string production)
    {
        for (auto it = productions.begin(); it != productions.end(); it++)
        {

            // 按格式“‘产生式左部’->‘产生式右部’赋值给existing”
            string existing = string(&(*it)->lhs, 1) + "->" + (*it)->rhs;

            // 指定项目与现存项目匹配
            // C库函数无法读取string类，获得两个字符串指针再作出比较
            if (strcmp(production.c_str(), existing.c_str()) == 0)
            {
                return true;
            }
        }
        return false;
    }

    // 因为项目列表是私有对象
    // 重载下标运算符，用来获得具体项目指针
    AugmentedProduction *operator[](const int index)
    {
        return productions[index];
    }
};

// 生成项目集的过程中，根据拓广文法
// 假如下一个输入字符为非终结符，往项目集内添加项目
void add_closure(char lookahead, LR0Item &item, AugmentedGrammar &grammar, NonTerminator &globalVT, Terminator &globalVN)
{
    // 当lookahead为非终结符时才继续，否则跳出函数
    if (!isupper(lookahead))
    {
        // 添加终结符到VT集
        if (find(globalVT.begin(), globalVT.end(), lookahead) == globalVT.end())
        {
            if (lookahead != '\0')
                globalVT.push_back(lookahead);
        }
        return;
    }

    // 添加非终结符到VN集
    if (find(globalVN.begin(), globalVN.end(), lookahead) == globalVN.end())
    {
        if (lookahead != '\0')
            globalVN.push_back(lookahead);
    }

    //令新添加状态产生式的左部为下一个非终结符
    string lhs = string(&lookahead, 1);

    // 遍历拓广文法内的产生式，为产生式右部添加“小黑点”@
    for (int i = 0; i < grammar[lookahead].size(); i++)
    {
        string rhs = "@" + grammar[lookahead][i];

        // 若该项目集内不存在下一个符号的项目，将其添加至项目列表中
        if (!item.Contains(lhs + "->" + rhs))
        {
            item.Push(new AugmentedProduction(lookahead, rhs));
        }
    }
}

// 从给出的拓广文法生成DFA中的项目集
void get_LR0_items(vector<LR0Item> &lr0items, AugmentedGrammar &grammar, int &itemid, GotoMap &globalGoto, NonTerminator &globalVT, Terminator &globalVN)
{
    // 打印项目集状态号
    printf("I%d:\n", itemid);

    // 确保当前项目集为其包含的项目的完整闭包
    for (int i = 0; i < lr0items[itemid].Size(); i++)
    {

        // 获取项目列表中每个项目的产生式右部
        string rhs = lr0items[itemid][i]->rhs;

        // 获取产生式右部“圆点”的下一个符号
        char lookahead = rhs[rhs.find('@') + 1];

        // 检查是否需要添加新的项目
        add_closure(lookahead, lr0items[itemid], grammar, globalVT, globalVN);
    }

    char lookahead, lhs;
    string rhs;

    // 遍历当前项目集的所有项目
    for (int i = 0; i < lr0items[itemid].Size(); i++)
    {

        // 获取当前项目的产生式
        lhs = lr0items[itemid][i]->lhs;
        rhs = lr0items[itemid][i]->rhs;
        string production = string(&lhs, 1) + "->" + rhs;

        // 获取产生式右部“圆点”的下一个符号
        lookahead = rhs[rhs.find('@') + 1];

        // 如果没有下一个符号，输出当前产生式，跳过后续程序
        if (lookahead == '\0')
        {
            printf("\t%-20s\n", &production[0]);
            continue;
        }

        // 若该项目集没有为刚才获取的符号定义导出边，新建导出边
        if (lr0items[itemid].gotos.find(lookahead) == lr0items[itemid].gotos.end())
        {

            // 检查全局状态转换表中是否存在该产生式，若存在直接使用其状态转换结果
            if (globalGoto.find(production) == globalGoto.end())
            {

                // 全局状态转换表中不存在该产生式，即该项目集目前仍未生成
                // 新建一个项目集
                lr0items.push_back(LR0Item());

                // 新项目集的首个项目为原项目集的首个项目的“圆点”往右移动一位
                // 交换“圆点”与其后一位字符
                string newRhs = rhs;
                int atpos = newRhs.find('@');
                swap(newRhs[atpos], newRhs[atpos + 1]);

                // 添加新项目集
                // 添加当前项目集的新字符导出边及其导出结果
                // 全局状态转换表中记录该产生式的状态转换结果
                lr0items.back().Push(new AugmentedProduction(lhs, newRhs));
                lr0items[itemid].gotos[lookahead] = lr0items.size() - 1;
                globalGoto[production] = lr0items.size() - 1;
            }
            else
            {

                // 全局状态转换表中存在该产生式
                // 获取其导出状态项目集
                lr0items[itemid].gotos[lookahead] = globalGoto[production];
            }

            // 打印产生式及其转换结果
            printf("\t%-20s goto(%c)=I%d\n", &production[0], lookahead, globalGoto[production]);
        }
        else
        {

            // 若已存在导出边及其转换结果，为其添加当前的产生式
            // 原产生式的“圆点”右移一位，生成新的项目
            int at = rhs.find('@');
            swap(rhs[at], rhs[at + 1]);

            // 如果该符号导出边指定的项目集不存在上面新生成的项目
            // 就把该项目添加到项目集
            int nextItem = lr0items[itemid].gotos[lookahead];
            if (!lr0items[nextItem].Contains(string(&lhs, 1) + "->" + rhs))
            {
                lr0items[nextItem].Push(new AugmentedProduction(lhs, rhs));
            }

            // 将“圆点”位置还原（左移一位）
            swap(rhs[at], rhs[at + 1]);
            printf("\t%-20s\n", &production[0]);
        }
    }
}

// 对文件输入流进行LR(0)语法分析
void load_grammar(ReduceList &reduceList, AugmentedGrammar &grammar, vector<LR0Item> &lr0items)
{
    int reduce_counter = 0;
    string production;
    string lhs, rhs;
    string delim = "->";

    // 读入开始产生式
    getline(fin, lhs);

    // 受map容器局限，标识符号只能存入单个字符“'”，无法存入“E'”
    // 往拓广文法内加入产生式
    grammar['\''].push_back(lhs);

    // 往项目集I0中加入项目
    lr0items[0].Push(new AugmentedProduction('\'', "@" + lhs));

    // C语言没有string类，获得lhs指针打印产生式左部
    // 打印文法开始产生式
    printf("%d '->%s\n", reduce_counter, lhs.c_str());

    //往规约式列表中添加首规约式
    production = "\'->" + lhs + "@";
    reduceList[production] = reduce_counter;

    while (!fin.eof())
    {
        reduce_counter++;

        // 读取产生式
        getline(fin, production);

        // 读取完毕，跳出循环
        if (production.length() < 1)
            return;

        // 分开产生式左右部
        // 若“->”不位于产生式最末尾
        auto pos = production.find(delim);
        if (pos != string::npos)
        {
            lhs = production.substr(0, pos);
            rhs = production.substr(pos + delim.length(), std::string::npos);
        }

        // 往拓广文法内存入产生式
        grammar[lhs[0]].push_back(rhs);

        // C语言没有string类，获得lhs指针打印产生式左部
        // 打印该文法产生式
        printf("%d %s->%s\n", reduce_counter, lhs.c_str(), rhs.c_str());

        //往规约式列表中添加规约式
        production = lhs + "->" + rhs + "@";
        reduceList[production] = reduce_counter;

        // 往项目集I0中加入项目
        lr0items[0].Push(new AugmentedProduction(lhs[0], "@" + rhs));
    }
}

//打印LR(0)分析表
void print_LR0_items(vector<LR0Item> &lr0items, ReduceList &reduceList, int &itemid, NonTerminator &globalVT, Terminator &globalVN)
{
    //打印表头
    if (itemid == 0)
    {
        printf("\t");
        for (int i = 0; i < globalVT.size(); i++)
        {
            printf("%c\t", globalVT[i]);
        }

        printf("#\t");
        for (int i = 0; i < globalVN.size(); i++)
        {
            printf("%c\t", globalVN[i]);
        }
        printf("\n");
    }

    // 打印项目集状态号
    printf("%d\t", itemid);

    char lookahead, lhs;
    string rhs;

    // 若当前项目集只有一个项目且是规约式
    if (lr0items[itemid].Size() == 1)
    {
        // 获取当前项目的产生式
        lhs = lr0items[itemid][0]->lhs;
        rhs = lr0items[itemid][0]->rhs;
        string production = string(&lhs, 1) + "->" + rhs;

        // 查找该项目是否存在于规约式表中
        if (reduceList.find(production) != reduceList.end())
        {
            // 若为首规约式，输出acc
            if (reduceList[production] == 0)
            {
                for (int i = 0; i < globalVT.size(); i++)
                {
                    printf("\t");
                }
                printf("acc\t");
            }
            else
            {
                // 若非首规约式，输出转移状态号
                for (int i = 0; i < globalVT.size(); i++)
                {
                    printf("r%d\t", reduceList[production]);
                }
                printf("r%d\t", reduceList[production]);
            }
            printf("\n");
        }
    }
    else
    {
        // 非单项目情况下，输出终结符转移状态号
        for (int i = 0; i < globalVT.size(); i++)
        {
            if (lr0items[itemid].gotos.find(globalVT[i]) == lr0items[itemid].gotos.end())
            {
                printf("\t");
            }
            else
            {
                printf("s%d\t", lr0items[itemid].gotos[globalVT[i]]);
            }
        }
        printf("\t");

        // 非单项目情况下，输出非终结符转移状态号
        for (int i = 0; i < globalVN.size(); i++)
        {
            if (lr0items[itemid].gotos.find(globalVN[i]) == lr0items[itemid].gotos.end())
            {
                printf("\t");
            }
            else
            {
                printf("%d\t", lr0items[itemid].gotos[globalVN[i]]);
            }
        }
        printf("\n");

        // 非单项目情况下，若项目集内部含有规约项目
        // 则发生了“移进”-“规约”冲突
        if (isLR0)
        {
            for (int i = 0; i < lr0items[itemid].Size(); i++)
            {
                // 获取当前项目的产生式
                lhs = lr0items[itemid][i]->lhs;
                rhs = lr0items[itemid][i]->rhs;
                string production = string(&lhs, 1) + "->" + rhs;
                // 查找该项目是否存在于规约式表中
                if (reduceList.find(production) != reduceList.end())
                //发生冲突，则此文法不能用LR(0)分析
                    isLR0 = false;
            }
        }
    }
}
int main()
{
    // 初始化项目集号计数变量
    int itemid = -1;

    // 初始化拓广文法
    AugmentedGrammar grammar;

    // 在项目集列表中生成一个空的项目集
    vector<LR0Item> lr0items = {LR0Item()};

    // 初始化全局状态转换表
    GotoMap globalGoto;

    // 初始化归约式列表
    ReduceList reduceList;

    // 初始化全局终止符集
    Terminator globalVN;

    // 初始化全局非终止符集
    NonTerminator globalVT;

    printf("Augmented Grammar\n");
    printf("-----------------\n");

    // 对文件输入流进行LR(0)语法分析
    // 生成拓广文法以及项目集I0
    load_grammar(reduceList, grammar, lr0items);
    printf("\n");

    printf("Sets of LR(0) Items\n");
    printf("-------------------\n");
    while (++itemid < int(lr0items.size()))
    {
        get_LR0_items(lr0items, grammar, itemid, globalGoto, globalVT, globalVN);
    }
    printf("\n");

    // 重置项目集计数变量
    itemid = -1;

    // 打印LR(0)分析表
    printf("LR(0) Analyze Table\n");
    printf("-------------------\n");
    while (++itemid < int(lr0items.size()))
    {
        print_LR0_items(lr0items, reduceList, itemid, globalVT, globalVN);
    }

    // 打印文法不能用LR(0)分析
    if (!isLR0)
        printf("\n----------------------------------\nThis grammer can't analyze by LR(0)!\n");

    system("pause");
    return 0;
}
