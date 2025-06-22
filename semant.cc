

#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"


extern int semant_debug;
extern char *curr_filename;

//////////////////////////////////////////////////////////////////////
//
// Symbols
//
// For convenience, a large number of symbols are predefined here.
// These symbols include the primitive type and method names, as well
// as fixed names used by the runtime system.
//
//////////////////////////////////////////////////////////////////////
static Symbol 
    arg,
    arg2,
    Bool,
    concat,
    cool_abort,
    copy,
    Int,
    in_int,
    in_string,
    IO,
    length,
    Main,
    main_meth,
    No_class,
    No_type,
    Object,
    out_int,
    out_string,
    prim_slot,
    self,
    SELF_TYPE,
    Str,
    str_field,
    substr,
    type_name,
    val;
//
// Initializing the predefined symbols.
//
static void initialize_constants(void)
{
    arg         = idtable.add_string("arg");
    arg2        = idtable.add_string("arg2");
    Bool        = idtable.add_string("Bool");
    concat      = idtable.add_string("concat");
    cool_abort  = idtable.add_string("abort");
    copy        = idtable.add_string("copy");
    Int         = idtable.add_string("Int");
    in_int      = idtable.add_string("in_int");
    in_string   = idtable.add_string("in_string");
    IO          = idtable.add_string("IO");
    length      = idtable.add_string("length");
    Main        = idtable.add_string("Main");
    main_meth   = idtable.add_string("main");
    //   _no_class is a symbol that can't be the name of any 
    //   user-defined class.
    No_class    = idtable.add_string("_no_class");
    No_type     = idtable.add_string("_no_type");
    Object      = idtable.add_string("Object");
    out_int     = idtable.add_string("out_int");
    out_string  = idtable.add_string("out_string");
    prim_slot   = idtable.add_string("_prim_slot");
    self        = idtable.add_string("self");
    SELF_TYPE   = idtable.add_string("SELF_TYPE");
    Str         = idtable.add_string("String");
    str_field   = idtable.add_string("_str_field");
    substr      = idtable.add_string("substr");
    type_name   = idtable.add_string("type_name");
    val         = idtable.add_string("_val");
}



ClassTable::ClassTable(Classes classes) : semant_errors(0) , error_stream(cerr) {

    /* Fill this in */
    install_basic_classes();
    build_inheritance_graph(classes); 
    check_semantic_errors();
}

void ClassTable::install_basic_classes() {
    
    // The tree package uses these globals to annotate the classes built below.
   // curr_lineno  = 0;
    Symbol filename = stringtable.add_string("<basic class>");
    
    // The following demonstrates how to create dummy parse trees to
    // refer to basic Cool classes.  There's no need for method
    // bodies -- these are already built into the runtime system.
    
    // IMPORTANT: The results of the following expressions are
    // stored in local variables.  You will want to do something
    // with those variables at the end of this method to make this
    // code meaningful.

    // 
    // The Object class has no parent class. Its methods are
    //        abort() : Object    aborts the program
    //        type_name() : Str   returns a string representation of class name
    //        copy() : SELF_TYPE  returns a copy of the object
    //
    // There is no need for method bodies in the basic classes---these
    // are already built in to the runtime system.

    Class_ Object_class =
	class_(Object, 
	       No_class,
	       append_Features(
			       append_Features(
					       single_Features(method(cool_abort, nil_Formals(), Object, no_expr())),
					       single_Features(method(type_name, nil_Formals(), Str, no_expr()))),
			       single_Features(method(copy, nil_Formals(), SELF_TYPE, no_expr()))),
	       filename);

    // 
    // The IO class inherits from Object. Its methods are
    //        out_string(Str) : SELF_TYPE       writes a string to the output
    //        out_int(Int) : SELF_TYPE            "    an int    "  "     "
    //        in_string() : Str                 reads a string from the input
    //        in_int() : Int                      "   an int     "  "     "
    //
    Class_ IO_class = 
	class_(IO, 
	       Object,
	       append_Features(
			       append_Features(
					       append_Features(
							       single_Features(method(out_string, single_Formals(formal(arg, Str)),
										      SELF_TYPE, no_expr())),
							       single_Features(method(out_int, single_Formals(formal(arg, Int)),
										      SELF_TYPE, no_expr()))),
					       single_Features(method(in_string, nil_Formals(), Str, no_expr()))),
			       single_Features(method(in_int, nil_Formals(), Int, no_expr()))),
	       filename);  

    //
    // The Int class has no methods and only a single attribute, the
    // "val" for the integer. 
    //
    Class_ Int_class =
	class_(Int, 
	       Object,
	       single_Features(attr(val, prim_slot, no_expr())),
	       filename);

    //
    // Bool also has only the "val" slot.
    //
    Class_ Bool_class =
	class_(Bool, Object, single_Features(attr(val, prim_slot, no_expr())),filename);

    //
    // The class Str has a number of slots and operations:
    //       val                                  the length of the string
    //       str_field                            the string itself
    //       length() : Int                       returns length of the string
    //       concat(arg: Str) : Str               performs string concatenation
    //       substr(arg: Int, arg2: Int): Str     substring selection
    //       
    Class_ Str_class =
	class_(Str, 
	       Object,
	       append_Features(
			       append_Features(
					       append_Features(
							       append_Features(
									       single_Features(attr(val, Int, no_expr())),
									       single_Features(attr(str_field, prim_slot, no_expr()))),
							       single_Features(method(length, nil_Formals(), Int, no_expr()))),
					       single_Features(method(concat, 
								      single_Formals(formal(arg, Str)),
								      Str, 
								      no_expr()))),
			       single_Features(method(substr, 
						      append_Formals(single_Formals(formal(arg, Int)), 
								     single_Formals(formal(arg2, Int))),
						      Str, 
						      no_expr()))),
	       filename);

    class_map[Object_class->get_name()] = Object_class;
    parent_map[Object_class->get_name()] = No_class;

    class_map[IO_class->get_name()] = IO_class;
    parent_map[IO_class->get_name()] = Object;

    class_map[Int_class->get_name()] = Int_class;
    parent_map[Int_class->get_name()] = Object;

    class_map[Bool_class->get_name()] = Bool_class;
    parent_map[Bool_class->get_name()] = Object;

    class_map[Str_class->get_name()] = Str_class;
    parent_map[Str_class->get_name()] = Object;
}

void ClassTable::build_inheritance_graph(Classes classes) {
    for (int i = classes->first(); classes->more(i); i = classes->next(i)) {
        if (!classes->nth(i)) {
            std::cerr << "Null class at index " << i << std::endl;
            continue;
        }
        Class_ cls = classes->nth(i);
        Symbol name = cls->get_name();
        Symbol parent = cls->get_parent();

        if (class_map.count(name)) { //Class A was previously defined.
            semant_error(cls) << "Class " << name << " was previously defined." << std::endl;
            continue;
        }

        class_map[name] = cls;
        parent_map[name] = parent;
    }
}

void ClassTable::check_semantic_errors() {
    // Provjeri postoji li Main klasa
    if (!class_map.count(Main)) {
        semant_error() << "Class Main is not defined." << std::endl;
    }

    // Provjeri nedozvoljeno nasljeđivanje i cikluse
    for (const auto& [child, parent] : parent_map) {
        // Ako child nije u mapi, preskoči (sigurnosna provjera)
        if (!class_map.count(child)) continue;

        Class_ child_class = class_map[child];

        if (parent == Int || parent == Bool || parent == Str) {
            semant_error(child_class) << "Class " << child 
                << " cannot inherit from basic class " << parent << "." << std::endl;
        }

        if (!class_map.count(parent) && parent != Object && parent != No_class) {
            semant_error(child_class) << "Class " << child 
                << " inherits from undefined class " << parent << "." << std::endl;
        }

        if (has_inheritance_cycle(child)) {
            semant_error(child_class) << "Inheritance cycle detected at class " << child << "." << std::endl;
        }
    }

    for (const auto& [name, class_] : class_map) {
        if (name == Object || name == IO || name == Int || name == Bool || name == Str)
            continue;
        current_class = class_;
        SymbolTable<Symbol, Symbol> object_env;
        class_->walk_down(this, &object_env);
    }
}


bool ClassTable::has_inheritance_cycle(Symbol c) {
    std::set<Symbol> path;
    while (c != Object && c != No_class) {
        if (path.count(c)) return true;
        path.insert(c);
        c = parent_map[c];
    }
    return false;
}

bool ClassTable::conforms(Symbol child, Symbol parent) {
    if (child == parent) return true;
    if (child == SELF_TYPE) {
        if (parent == SELF_TYPE) return true;
        child = current_class->get_name(); // SELF_TYPE se ponaša kao trenutna klasa
    }
    if (parent == SELF_TYPE) return false;

    while (child != No_class) {
        if (child == parent) return true;
        if (parent_map.find(child) == parent_map.end()) break;
        child = parent_map[child];
    }

    return false;
}

Symbol ClassTable::least_common_ancestor(Symbol a, Symbol b) {
    if (a == SELF_TYPE) a = current_class->get_name();
    if (b == SELF_TYPE) b = current_class->get_name();

    std::set<Symbol> ancestors;

    while (a != No_class) {
        ancestors.insert(a);
        if (parent_map.find(a) == parent_map.end()) break;
        a = parent_map[a];
    }

    while (b != No_class) {
        if (ancestors.count(b)) return b;
        if (parent_map.find(b) == parent_map.end()) break;
        b = parent_map[b];
    }

    return Object; // fallback
}

bool ClassTable::is_attr_inherited(Symbol attr_name, Symbol class_name) {
    Symbol parent = parent_map[class_name];

    while (parent != No_class) {
        if (!class_map.count(parent)) break;

        Features features = class_map[parent]->get_features();
        for (int i = features->first(); features->more(i); i = features->next(i)) {
            Feature f = features->nth(i);
            attr_class* attr = dynamic_cast<attr_class*>(f);
            if (attr && attr->get_name() == attr_name) {
                return true;
            }
        }

        parent = parent_map[parent];
    }
    return false;
}


void class__class::walk_down(ClassTable* classtable, SymbolTable<Symbol, Symbol>* object_env) {
    object_env->enterscope();

    // 1. Dodaj atribute klase u objektni kontekst
    for (int i = features->first(); features->more(i); i = features->next(i)) {
        Feature f = features->nth(i);
        attr_class* attr = dynamic_cast<attr_class*>(f);
        if (attr) {
            Symbol name = attr->get_name();
            Symbol type = attr->get_type_decl();
            if (name == self) {
                classtable->semant_error(get_filename(), this)
                    << "'self' cannot be the name of an attribute.\n";
            } else {
                object_env->addid(name, new Symbol(type));
            }
        }
    }

    // 2. Pozovi walk_down na svaku metodu i atribut
    for (int i = features->first(); features->more(i); i = features->next(i)) {
        Feature f = features->nth(i);
        attr_class* attr = dynamic_cast<attr_class*>(f);

        if (attr) {
            Symbol attr_name = attr->get_name();

            if (classtable->is_attr_inherited(attr_name, name)) {
                classtable->semant_error(filename, this)
                    << "Attribute " << attr_name << " is an attribute of an inherited class.\n";
            }
        }

        f->walk_down(classtable, object_env, this);
    }

    object_env->exitscope();
}


void attr_class::walk_down(ClassTable* classtable, SymbolTable<Symbol, Symbol>* object_env, Class_ current_class) {
    if (init->get_type() == NULL) {
        init->walk_down(classtable, object_env, current_class);
    }

    Symbol init_type = init->get_type();

    // Ako nema inicijalizacije (tj. no_expr), ne radi se provjera tipa
    if (typeid(*init) != typeid(no_expr_class)) {
        if (!classtable->conforms(init_type, type_decl)) {
            classtable->semant_error(current_class->get_filename(), this)
                << "Type of initialization expression " << init_type
                << " does not conform to declared type " << type_decl
                << " of attribute " << name << ".\n";
        }
    }

    set_type(type_decl);
}



void object_class::walk_down(ClassTable* classtable, SymbolTable<Symbol, Symbol>* object_env, Class_ current_class) {
    if (name == self) {
        set_type(SELF_TYPE); // self je uvijek SELF_TYPE
        return;
    } 

    Symbol* type = object_env->lookup(name);
    if (type) {
        set_type(*type);
    } else {
        classtable->semant_error(current_class->get_filename(), this)
            << "Undeclared identifier " << name << ".\n";
        set_type(Object); // fallback
    }
}



void plus_class::walk_down(ClassTable* classtable, SymbolTable<Symbol, Symbol>* object_env, Class_ current_class) {
    e1->walk_down(classtable, object_env, current_class);
    e2->walk_down(classtable, object_env, current_class);

    if (e1->get_type() != Int || e2->get_type() != Int) {
        classtable->semant_error(current_class) << "Non-Int arguments: " << e1->get_type() << " + " << e2->get_type() << ".\n";
        set_type(Object);
    } else {
        set_type(Int);
    }
}

void no_expr_class::walk_down(ClassTable* classtable, SymbolTable<Symbol, Symbol>* object_env, Class_ current_class) {
    set_type(No_type);
}

void isvoid_class::walk_down(ClassTable* classtable, SymbolTable<Symbol, Symbol>* object_env, Class_ current_class) {
    e1->walk_down(classtable, object_env, current_class);
    set_type(Bool);
}

void new__class::walk_down(ClassTable* classtable, SymbolTable<Symbol, Symbol>* object_env, Class_ current_class) {
    set_type(type_name == SELF_TYPE ? SELF_TYPE : type_name);
}

void string_const_class::walk_down(ClassTable*, SymbolTable<Symbol, Symbol>*, Class_){
    set_type(Str);
}

void bool_const_class::walk_down(ClassTable*, SymbolTable<Symbol, Symbol>*, Class_){
    set_type(Bool);
}

void int_const_class::walk_down(ClassTable*, SymbolTable<Symbol, Symbol>*, Class_){
    set_type(Int);
}

void comp_class::walk_down(ClassTable* classtable, SymbolTable<Symbol, Symbol>* object_env, Class_ current_class) {
    e1->walk_down(classtable, object_env, current_class);
    set_type(Bool);
}

void leq_class::walk_down(ClassTable* classtable, SymbolTable<Symbol, Symbol>* object_env, Class_ current_class) {
    e1->walk_down(classtable, object_env, current_class);
    e2->walk_down(classtable, object_env, current_class);
    set_type(Bool);
}

void eq_class::walk_down(ClassTable* classtable, SymbolTable<Symbol, Symbol>* object_env, Class_ current_class) {
    e1->walk_down(classtable, object_env, current_class);
    e2->walk_down(classtable, object_env, current_class);

    Symbol t1 = e1->get_type();
    Symbol t2 = e2->get_type();

    if ((t1 == Int || t1 == Str || t1 == Bool || t2 == Int || t2 == Str || t2 == Bool) && t1 != t2) {
        classtable->semant_error(current_class->get_filename(), this)
            << "Illegal comparison with a basic type.\n";
    }

    set_type(Bool);
}


void lt_class::walk_down(ClassTable* classtable, SymbolTable<Symbol, Symbol>* object_env, Class_ current_class) {
    e1->walk_down(classtable, object_env, current_class);
    e2->walk_down(classtable, object_env, current_class);
    set_type(Bool);
}

void neg_class::walk_down(ClassTable* classtable, SymbolTable<Symbol, Symbol>* object_env, Class_ current_class) {
    e1->walk_down(classtable, object_env, current_class);
    set_type(Int);
}

void divide_class::walk_down(ClassTable* classtable, SymbolTable<Symbol, Symbol>* object_env, Class_ current_class) {
    e1->walk_down(classtable, object_env, current_class);
    e2->walk_down(classtable, object_env, current_class);
    set_type(Int);
}

void mul_class::walk_down(ClassTable* classtable, SymbolTable<Symbol, Symbol>* object_env, Class_ current_class) {
    e1->walk_down(classtable, object_env, current_class);
    e2->walk_down(classtable, object_env, current_class);
    set_type(Int);
}

void sub_class::walk_down(ClassTable* classtable, SymbolTable<Symbol, Symbol>* object_env, Class_ current_class) {
    e1->walk_down(classtable, object_env, current_class);
    e2->walk_down(classtable, object_env, current_class);
    set_type(Int);
}

void let_class::walk_down(ClassTable* classtable, SymbolTable<Symbol, Symbol>* object_env, Class_ current_class) {
    object_env->enterscope();

    if (identifier == self) {
        classtable->semant_error(current_class->get_filename(), this)
            << "'self' cannot be bound in a 'let' expression.\n";
    } else {
        object_env->addid(identifier, new Symbol(type_decl));
    }

    if (init) {
        init->walk_down(classtable, object_env, current_class);
        Symbol init_type = init->get_type();
        if (!classtable->conforms(init_type, type_decl)) {
            classtable->semant_error(current_class->get_filename(), this)
                << "Inferred type " << init_type << " of initialization does not conform to declared type "
                << type_decl << " of identifier " << identifier << ".\n";
        }
    }

    body->walk_down(classtable, object_env, current_class);
    set_type(body->get_type());

    object_env->exitscope();
}

void block_class::walk_down(ClassTable* classtable, SymbolTable<Symbol, Symbol>* object_env, Class_ current_class) {
    for (int i = 0; i < body->len(); ++i)
        body->nth(i)->walk_down(classtable, object_env, current_class);

    set_type(body->nth(body->len() - 1)->get_type());
}

/*
void typcase_class::walk_down(ClassTable*, SymbolTable<Symbol, Symbol>*, Class_) {
    set_type(Object); // puni kod dolazi kasnije
}
*/

void typcase_class::walk_down(ClassTable* classtable, SymbolTable<Symbol, Symbol>* object_env, Class_ current_class) {
    expr->walk_down(classtable, object_env, current_class);
    std::set<Symbol> seen;

    Symbol result_type = nullptr;

    for (int i = cases->first(); cases->more(i); i = cases->next(i)) {
        Case case_ = cases->nth(i);
        Symbol type = case_->get_type_decl();

        if (seen.count(type))
            classtable->semant_error(); // duplicate branch type
        seen.insert(type);

        object_env->enterscope();
        object_env->addid(case_->get_name(), new Symbol(type));
        case_->get_expr()->walk_down(classtable, object_env, current_class);
        object_env->exitscope();

        Symbol branch_type = case_->get_expr()->get_type();
        result_type = (i == 0) ? branch_type : classtable->least_common_ancestor(result_type, branch_type);
    }

    set_type(result_type);
}


void loop_class::walk_down(ClassTable* classtable, SymbolTable<Symbol, Symbol>* object_env, Class_ current_class) {
    pred->walk_down(classtable, object_env, current_class);
    body->walk_down(classtable, object_env, current_class);
    set_type(Object); // loop uvijek vraća Object
}

void cond_class::walk_down(ClassTable* classtable, SymbolTable<Symbol, Symbol>* object_env, Class_ current_class) {
    pred->walk_down(classtable, object_env, current_class);
    then_exp->walk_down(classtable, object_env, current_class);
    else_exp->walk_down(classtable, object_env, current_class);

    if (pred->get_type() != Bool)
        classtable->semant_error(); // condition not Bool

    set_type(classtable->least_common_ancestor(
        then_exp->get_type(), else_exp->get_type()));
}

void method_class::walk_down(ClassTable* classtable, SymbolTable<Symbol, Symbol>* object_env, Class_ current_class) {
    object_env->enterscope();
    object_env->addid(self, new Symbol(current_class->get_name())); // radi self
    // Dodaj formalne parametre u okruženje
    for (int i = formals->first(); formals->more(i); i = formals->next(i)) {
        Symbol name = formals->nth(i)->get_name();
        Symbol type = formals->nth(i)->get_type_decl();

        if (name == self) {
            classtable->semant_error(current_class->get_filename(), this)
                << "'self' cannot be used as a formal parameter name.\n";
        } else {
            object_env->addid(name, new Symbol(type));
        }
    }

    // Provjeri tijelo funkcije
    expr->walk_down(classtable, object_env, current_class);

    Symbol body_type = expr->get_type();
    Symbol declared_return = return_type;

    if (!classtable->conforms(body_type, declared_return)) {
        classtable->semant_error(current_class->get_filename(), this)
            << "Method " << name << " has body of type " << body_type
            << " but declared return type is " << declared_return << ".\n";
    }

    object_env->exitscope();
}


void dispatch_class::walk_down(ClassTable* classtable, SymbolTable<Symbol, Symbol>* object_env, Class_ current_class) {
    expr->walk_down(classtable, object_env, current_class);
    Symbol expr_type = expr->get_type();

    // Ako je SELF_TYPE, koristi ime trenutne klase
    if (expr_type == SELF_TYPE)
        expr_type = current_class->get_name();

    // Provjeri postoji li klasa
    if (!classtable->class_map.count(expr_type)) {
        classtable->semant_error(current_class->get_filename(), this)
            << "Dispatch on undefined class " << expr_type << ".\n";
        set_type(Object);
        return;
    }

    Class_ target_class = classtable->class_map[expr_type];
    bool method_found = false;
    method_class* method_ptr = nullptr;

    // Pronađi metodu u hijerarhiji
    while (target_class != nullptr && target_class->get_name() != No_class) {
        Features features = target_class->get_features();

        for (int i = features->first(); features->more(i); i = features->next(i)) {
            Feature f = features->nth(i);
            method_class* m = dynamic_cast<method_class*>(f);
            if (m && m->get_name() == name) {
                method_found = true;
                method_ptr = m;
                break;
            }
        }

        if (method_found) break;

        Symbol parent_name = classtable->parent_map[target_class->get_name()];
        if (!classtable->class_map.count(parent_name)) break;
        target_class = classtable->class_map[parent_name];
    }

    if (!method_found) {
        classtable->semant_error(current_class->get_filename(), this)
            << "Dispatch to undefined method " << name << ".\n";
        set_type(Object);
        return;
    }

    // Provjeri argumente
    Formals formals = method_ptr->get_formals();
    if (formals->len() != actual->len()) {
        classtable->semant_error(current_class->get_filename(), this)
            << "Method " << name << " called with wrong number of arguments.\n";
    } else {
        for (int i = 0; i < actual->len(); ++i) {
            Expression arg = actual->nth(i);
            arg->walk_down(classtable, object_env, current_class);

            Symbol arg_type = arg->get_type();
            Symbol param_type = formals->nth(i)->get_type_decl();

            if (!classtable->conforms(arg_type, param_type)) {
                classtable->semant_error(current_class->get_filename(), this)
                    << "Argument " << i + 1 << " of method " << name << " has type "
                    << arg_type << " but expected " << param_type << ".\n";
            }
        }
    }

    Symbol return_type = method_ptr->get_return_type();
    if (return_type == SELF_TYPE)
        set_type(expr->get_type()); // SELF_TYPE: rezultat je tip objekta
    else
        set_type(return_type);
}
/*
void static_dispatch_class::walk_down(ClassTable*, SymbolTable<Symbol, Symbol>*, Class_) {
    set_type(Object); // kasnije: provjeri eksplicitni tip
}
*/

void static_dispatch_class::walk_down(ClassTable* classtable, SymbolTable<Symbol, Symbol>* object_env, Class_ current_class) {
    expr->walk_down(classtable, object_env, current_class);
    Symbol expr_type = expr->get_type();

    if (expr_type == SELF_TYPE)
        expr_type = current_class->get_name();

    // statički tip mora postojati i biti nadtip
    if (!classtable->class_map.count(type_name))
        classtable->semant_error(); // static type does not exist
    else if (!classtable->conforms(expr_type, type_name))
        classtable->semant_error(); // expression type doesn't conform to static type

    // traži metodu
    Class_ target = classtable->class_map[type_name];
    method_class* method_ptr = nullptr;

    while (target && target->get_name() != No_class) {
        Features feats = target->get_features();

        for (int i = 0; i < feats->len(); ++i) {
            method_class* m = dynamic_cast<method_class*>(feats->nth(i));
            if (m && m->get_name() == name) {
                method_ptr = m;
                break;
            }
        }

        if (method_ptr) break;

        Symbol parent_name = classtable->parent_map[target->get_name()];
        if (!classtable->class_map.count(parent_name)) break;
        target = classtable->class_map[parent_name];
    }

    if (!method_ptr) {
        classtable->semant_error(); // undefined method
        set_type(Object);
        return;
    }

    // provjera argumenata
    if (method_ptr->get_formals()->len() != actual->len())
        classtable->semant_error(); // wrong number of args
    else {
        for (int i = 0; i < actual->len(); ++i) {
            actual->nth(i)->walk_down(classtable, object_env, current_class);

            Symbol arg_type = actual->nth(i)->get_type();
            Symbol expected = method_ptr->get_formals()->nth(i)->get_type_decl();

            if (!classtable->conforms(arg_type, expected))
                classtable->semant_error(); // type mismatch
        }
    }

    set_type(method_ptr->get_return_type() == SELF_TYPE ? expr->get_type() : method_ptr->get_return_type());
}

void assign_class::walk_down(ClassTable* classtable, SymbolTable<Symbol, Symbol>* object_env, Class_ current_class) {
    expr->walk_down(classtable, object_env, current_class);

    if (name == self) {
        classtable->semant_error(current_class->get_filename(), this)
            << "Cannot assign to 'self'.\n";
        set_type(Object);
        return;
    }

    Symbol* declared_type = object_env->lookup(name);
    if (!declared_type) {
        classtable->semant_error(current_class->get_filename(), this)
            << "Assignment to undeclared variable " << name << ".\n";
        set_type(Object);
        return;
    }

    Symbol expr_type = expr->get_type();
    if (!classtable->conforms(expr_type, *declared_type)) {
        classtable->semant_error(current_class->get_filename(), this)
            << "Type " << expr_type << " of assigned expression does not conform to declared type "
            << *declared_type << " of identifier " << name << ".\n";
        set_type(Object);
    } else {
        set_type(expr_type);
    }
}





////////////////////////////////////////////////////////////////////
//
// semant_error is an overloaded function for reporting errors
// during semantic analysis.  There are three versions:
//
//    ostream& ClassTable::semant_error()                
//
//    ostream& ClassTable::semant_error(Class_ c)
//       print line number and filename for `c'
//
//    ostream& ClassTable::semant_error(Symbol filename, tree_node *t)  
//       print a line number and filename
//
///////////////////////////////////////////////////////////////////

ostream& ClassTable::semant_error(Class_ c)
{                                                             
    return semant_error(c->get_filename(),c);
}    

ostream& ClassTable::semant_error(Symbol filename, tree_node *t)
{
    error_stream << filename << ":" << t->get_line_number() << ": ";
    return semant_error();
}

ostream& ClassTable::semant_error()                  
{                                                 
    semant_errors++;                            
    return error_stream;
} 



/*   This is the entry point to the semantic checker.

     Your checker should do the following two things:

     1) Check that the program is semantically correct
     2) Decorate the abstract syntax tree with type information
        by setting the `type' field in each Expression node.
        (see `tree.h')

     You are free to first do 1), make sure you catch all semantic
     errors. Part 2) can be done in a second stage, when you want
     to build mycoolc.
 */
void program_class::semant()
{
    initialize_constants();

    /* ClassTable constructor may do some semantic analysis */
    ClassTable *classtable = new ClassTable(classes);

    /* some semantic analysis code may go here */

    if (classtable->errors()) {
	cerr << "Compilation halted due to static semantic errors." << endl;
	exit(1);
    }
}


