#ifndef SEMANT_H_
#define SEMANT_H_

#include <assert.h>
#include <iostream>  
#include "cool-tree.h"
#include "stringtab.h"
#include "symtab.h"
#include "list.h"
#include <map>
#include <set>

#define TRUE 1
#define FALSE 0

class ClassTable;
typedef ClassTable *ClassTableP;

// This is a structure that may be used to contain the semantic
// information such as the inheritance graph.  You may use it or not as
// you like: it is only here to provide a container for the supplied
// methods.

class ClassTable {
  private:
    int semant_errors;
    void install_basic_classes();
    ostream& error_stream;

    std::set<Symbol> visited;

    void build_inheritance_graph(Classes classes);
    bool has_inheritance_cycle(Symbol c);
    void check_semantic_errors();
    Class_ current_class;

  public:
    ClassTable(Classes);
    int errors() { return semant_errors; }
    ostream& semant_error();
    ostream& semant_error(Class_ c);
    ostream& semant_error(Symbol filename, tree_node *t);
    std::map<Symbol, Class_> class_map;
    std::map<Symbol, Symbol> parent_map;
    bool conforms(Symbol child, Symbol parent);
    Symbol least_common_ancestor(Symbol a, Symbol b);
};


#endif

