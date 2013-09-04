/*********************                                                        */
/*! \file theory_strings.cpp
 ** \verbatim
 ** Original author: Tianyi Liang
 ** Major contributors: Tianyi Liang, Andrew Reynolds
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2013-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of the theory of strings.
 **
 ** Implementation of the theory of strings.
 **/


#include "theory/strings/theory_strings.h"
#include "theory/valuation.h"
#include "expr/kind.h"
#include "theory/rewriter.h"
#include "expr/command.h"
#include "theory/model.h"
#include "smt/logic_exception.h"


using namespace std;

namespace CVC4 {
namespace theory {
namespace strings {

TheoryStrings::TheoryStrings(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo, QuantifiersEngine* qe)
	: Theory(THEORY_STRINGS, c, u, out, valuation, logicInfo, qe),
	d_notify( *this ),
    d_equalityEngine(d_notify, c, "theory::strings::TheoryStrings"),
	d_conflict( c, false ),
    d_infer(c),
    d_infer_exp(c)
{
  // The kinds we are treating as function application in congruence
  d_equalityEngine.addFunctionKind(kind::STRING_IN_REGEXP);
  d_equalityEngine.addFunctionKind(kind::STRING_LENGTH);
  d_equalityEngine.addFunctionKind(kind::STRING_CONCAT);

	d_zero = NodeManager::currentNM()->mkConst( Rational( 0 ) );
	d_emptyString = NodeManager::currentNM()->mkConst( ::CVC4::String("") );
}

TheoryStrings::~TheoryStrings() {

}

void TheoryStrings::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  d_equalityEngine.setMasterEqualityEngine(eq);
}

void TheoryStrings::addSharedTerm(TNode t) {
  Debug("strings") << "TheoryStrings::addSharedTerm(): "
                     << t << " " << t.getType().isBoolean() << endl;
  d_equalityEngine.addTriggerTerm(t, THEORY_STRINGS);
  Debug("strings") << "TheoryStrings::addSharedTerm() finished" << std::endl;
}

void TheoryStrings::propagate(Effort e)
{
  // direct propagation now
}

bool TheoryStrings::propagate(TNode literal) {
  Debug("strings-propagate") << "TheoryStrings::propagate(" << literal  << ")" << std::endl;
  // If already in conflict, no more propagation
  if (d_conflict) {
    Debug("strings-propagate") << "TheoryStrings::propagate(" << literal << "): already in conflict" << std::endl;
    return false;
  }
  Trace("strings-prop") << "strPropagate " << literal << std::endl;
  // Propagate out
  bool ok = d_out->propagate(literal);
  if (!ok) {
    d_conflict = true;
  }
  return ok;
}

/** explain */
void TheoryStrings::explain(TNode literal, std::vector<TNode>& assumptions){
  Debug("strings-explain") << "Explain " << literal << std::endl;
  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];
  if (atom.getKind() == kind::EQUAL || atom.getKind() == kind::IFF) {
    d_equalityEngine.explainEquality(atom[0], atom[1], polarity, assumptions);
  } else {
    d_equalityEngine.explainPredicate(atom, polarity, assumptions);
  }
}

Node TheoryStrings::explain( TNode literal ){
  std::vector< TNode > assumptions;
  explain( literal, assumptions );
  if( assumptions.empty() ){
    return NodeManager::currentNM()->mkConst( true );
  }else if( assumptions.size()==1 ){
    return assumptions[0];
  }else{
    return NodeManager::currentNM()->mkNode( kind::AND, assumptions );
  }
}

/////////////////////////////////////////////////////////////////////////////
// MODEL GENERATION
/////////////////////////////////////////////////////////////////////////////


void TheoryStrings::collectModelInfo( TheoryModel* m, bool fullModel )
{
}

/////////////////////////////////////////////////////////////////////////////
// MAIN SOLVER
/////////////////////////////////////////////////////////////////////////////

void TheoryStrings::preRegisterTerm(TNode n) {
  Debug("strings-prereg") << "TheoryStrings::preRegisterTerm() " << n << endl;
  //collectTerms( n );
  switch (n.getKind()) {
  case kind::EQUAL:
    d_equalityEngine.addTriggerEquality(n);
    break;
  case kind::STRING_IN_REGEXP:
    d_equalityEngine.addTriggerPredicate(n);
    break;
  default:
	if(n.getKind() == kind::VARIABLE) {
	  Node n_len = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, n);
	  Node zero = NodeManager::currentNM()->mkConst( ::CVC4::Rational( 0 ) );
	  Node n_len_geq_zero = NodeManager::currentNM()->mkNode( kind::GEQ, n_len, zero);
	  Trace("strings-lemma") << "Strings: Add lemma " << n_len_geq_zero << std::endl;
	  d_out->lemma(n_len_geq_zero);
    }
    if (n.getType().isBoolean()) {
      // Get triggered for both equal and dis-equal
      d_equalityEngine.addTriggerPredicate(n);
    } else {
      // Function applications/predicates
      d_equalityEngine.addTerm(n);
    }
    break;
  }
}

void TheoryStrings::dealPositiveWordEquation(TNode n) {
  Trace("strings-pwe") << "Deal Positive Word Equation: " << n << endl;
  Node node = n;

  // length left = length right
  //Node n_left = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, n[0]);
  //Node n_right = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, n[1]);
  if(node[0].getKind() == kind::CONST_STRING) {
  } else if(node[0].getKind() == kind::STRING_CONCAT) {
  }
}

void TheoryStrings::check(Effort e) {
  bool polarity;
  TNode atom;

  while ( !done() && !d_conflict)
  {
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.assertion;

	Trace("strings-check") << "get assertion: " << fact << endl;

    polarity = fact.getKind() != kind::NOT;
    atom = polarity ? fact : fact[0];
    if (atom.getKind() == kind::EQUAL) {
	  //head
	  //if(atom[0].getKind() == kind::CONST_STRING) {
		  //if(atom[1].getKind() == kind::STRING_CONCAT) {
		  //}
	  //}
	  //tail
      d_equalityEngine.assertEquality(atom, polarity, fact);
    } else {
      d_equalityEngine.assertPredicate(atom, polarity, fact);
    }
	switch(atom.getKind()) {
		case kind::EQUAL:
			if(polarity) {
				//if(atom[0].isString() && atom[1].isString()) {
					//dealPositiveWordEquation(atom);
				//}
			} else {
				// TODO: Word Equation negaitive
			}
			break;
		case kind::STRING_IN_REGEXP:
			// TODO: membership
			break;
		default:
			//possibly error
			break;
	}
  }
  doPendingFacts();


  if( e == EFFORT_FULL && !d_conflict ) {
	  bool addedLemma = false;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
  while( !eqcs_i.isFinished() ){
	Node eqc = (*eqcs_i);
	//if eqc.getType is string
	if (eqc.getType().isString()) {
		//EqcInfo* ei = getOrMakeEqcInfo( eqc, true );
		//get the constant for the equivalence class
		//int c_len = ...;
		eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &d_equalityEngine );
		while( !eqc_i.isFinished() ){
		  Node n = (*eqc_i);

		  //if n is concat, and
		  //if n has not instantiatied the concat..length axiom
		  //then, add lemma
		  if( n.getKind() == kind::STRING_CONCAT || n.getKind() == kind::CONST_STRING ){
			if( d_length_inst.find(n)==d_length_inst.end() ){
				d_length_inst[n] = true;
				addedLemma = true;
				Trace("strings-debug") << "get n: " << n << endl;
				Node sk = NodeManager::currentNM()->mkSkolem( "lsym_$$", n.getType(), "created for concat lemma" );
				Node eq = NodeManager::currentNM()->mkNode( kind::EQUAL, sk, n );
				eq = Rewriter::rewrite(eq);
				Trace("strings-lemma") << "Strings: Add lemma " << eq << std::endl;
				d_out->lemma(eq);
				Node skl = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, sk );
				Node lsum;
				if( n.getKind() == kind::STRING_CONCAT ){
					//add lemma
					std::vector<Node> node_vec;
					for( unsigned i=0; i<n.getNumChildren(); i++ ) {
						Node lni = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, n[i] );
						node_vec.push_back(lni);
					}
					lsum = NodeManager::currentNM()->mkNode( kind::PLUS, node_vec );
				}else{
					//add lemma
					lsum = NodeManager::currentNM()->mkConst( ::CVC4::Rational( n.getConst<String>().size() ) );
				}
				Node ceq = NodeManager::currentNM()->mkNode( kind::EQUAL, skl, lsum );
				ceq = Rewriter::rewrite(ceq);
				Trace("strings-lemma") << "Strings: Add lemma " << ceq << std::endl;
				d_out->lemma(ceq);
			}
		  }
		  ++eqc_i;
		}
	}
	++eqcs_i;
  }
  if( !addedLemma ){
	//calculate normal forms for each equivalence class, possibly adding splitting lemmas
	d_normal_forms.clear();
	std::map< Node, Node > nf_to_eqc;
	std::map< Node, Node > eqc_to_exp;
	  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
	  while( !eqcs_i.isFinished() ){
		Node eqc = (*eqcs_i);
		//if eqc.getType is string
		if (eqc.getType().isString()) {
			std::vector< Node > visited;
			std::vector< Node > nf;
			std::vector< Node > nf_exp;
			normalizeEquivalenceClass(eqc, visited, nf, nf_exp);
			if( d_conflict ){
				return;
			}else{
				Node nf_term;
				if( nf.size()==0 ){
					nf_term = d_emptyString;
				}else if( nf.size()==1 ) {
					nf_term = nf[0];
				} else {
					nf_term = NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, nf );
				}
				nf_term = Rewriter::rewrite( nf_term );
				Node nf_term_exp = nf_exp.empty() ? NodeManager::currentNM()->mkConst(true) :
									nf_exp.size()==1 ? nf_exp[0] : NodeManager::currentNM()->mkNode( kind::AND, nf_exp );
				if( nf_to_eqc.find(nf_term)!=nf_to_eqc.end() ){
					//two equivalence classes have same normal form, merge
					Node eq_exp = NodeManager::currentNM()->mkNode( kind::AND, nf_term_exp, eqc_to_exp[nf_term] );
					Node eq = NodeManager::currentNM()->mkNode( kind::EQUAL, eqc, nf_to_eqc[nf_term] );
					Trace("strings-infer") << "Strings (by normal forms) : Infer " << eq << " from " << eq_exp << std::endl;
					d_equalityEngine.assertEquality( eq, true, eq_exp );
					d_infer.push_back(eq);
					d_infer_exp.push_back(eq_exp);
					if( d_conflict ){
						return;
					}
				}else{
					nf_to_eqc[nf_term] = eqc;
					eqc_to_exp[eqc] = nf_term_exp;
				}
			}
		}
		++eqcs_i;
	  }
  }
  }
}

TheoryStrings::EqcInfo::EqcInfo(  context::Context* c ) : d_length_term(c) {

}

TheoryStrings::EqcInfo * TheoryStrings::getOrMakeEqcInfo( Node eqc, bool doMake ) {
  std::map< Node, EqcInfo* >::iterator eqc_i = d_eqc_info.find( eqc );
  if( eqc_i==d_eqc_info.end() ){
    if( doMake ){
      EqcInfo* ei = new EqcInfo( getSatContext() );
      d_eqc_info[eqc] = ei;
      return ei;
    }else{
      return NULL;
    }
  }else{
    return (*eqc_i).second;
  }
}


/** Conflict when merging two constants */
void TheoryStrings::conflict(TNode a, TNode b){
  Node conflictNode;
  if (a.getKind() == kind::CONST_BOOLEAN) {
    conflictNode = explain( a.iffNode(b) );
  } else {
    conflictNode = explain( a.eqNode(b) );
  }
  Debug("strings-conflict") << "CONFLICT: Eq engine conflict : " << conflictNode << std::endl;
  d_out->conflict( conflictNode );
  d_conflict = true;
}

/** called when a new equivalance class is created */
void TheoryStrings::eqNotifyNewClass(TNode t){
  //if( t.getKind() == kind::CONST_STRING ){
  //  getOrMakeEqcInfo( t, true );
  //}
  if( t.getKind() == kind::STRING_LENGTH ){
	Trace("strings-debug") << "New length eqc : " << t << std::endl;
	Node r = d_equalityEngine.getRepresentative(t[0]);
	EqcInfo * ei = getOrMakeEqcInfo( r, true );
	ei->d_length_term = t[0];
  }
}

/** called when two equivalance classes will merge */
void TheoryStrings::eqNotifyPreMerge(TNode t1, TNode t2){
	EqcInfo * e2 = getOrMakeEqcInfo(t2, false);
	if( e2 ){
		EqcInfo * e1 = getOrMakeEqcInfo( t1 );
		//add information from e2 to e1
		if( !e2->d_length_term.get().isNull() ){
			e1->d_length_term.set( e2->d_length_term );
		}
	}
	if( hasTerm( d_zero ) ){
		Node leqc;
		if( areEqual(d_zero, t1) ){
			leqc = t2;
		}else if( areEqual(d_zero, t2) ){
			leqc = t1;
		}
		if( !leqc.isNull() ){
			//scan equivalence class to see if we apply
			eq::EqClassIterator eqc_i = eq::EqClassIterator( leqc, &d_equalityEngine );
			while( !eqc_i.isFinished() ){
			  Node n = (*eqc_i);
			  if( n.getKind()==kind::STRING_LENGTH ){
				if( !hasTerm( d_emptyString ) || !areEqual(n[0], d_emptyString ) ){
					Trace("strings-debug") << "Processing possible inference." << n << std::endl;
					//apply the rule length(n[0])==0 => n[0] == ""
					Node eq = NodeManager::currentNM()->mkNode( kind::EQUAL, n[0], d_emptyString );
					d_pending.push_back( eq );
					Node eq_exp = NodeManager::currentNM()->mkNode( kind::EQUAL, n, d_zero );
					d_pending_exp[eq] = eq_exp;
					Trace("strings-infer") << "Strings : Infer " << eq << " from " << eq_exp << std::endl;
					d_infer.push_back(eq);
					d_infer_exp.push_back(eq_exp);
				}
			  }
			  ++eqc_i;
			}
		}
	}
}

/** called when two equivalance classes have merged */
void TheoryStrings::eqNotifyPostMerge(TNode t1, TNode t2) {

}

/** called when two equivalance classes are disequal */
void TheoryStrings::eqNotifyDisequal(TNode t1, TNode t2, TNode reason) {

}

void TheoryStrings::computeCareGraph(){
  Theory::computeCareGraph();
}

void TheoryStrings::doPendingFacts() {
  int i=0;
  while( !d_conflict && i<(int)d_pending.size() ){
	Node fact = d_pending[i];
	Node exp = d_pending_exp[ fact ];
	  bool polarity = fact.getKind() != kind::NOT;
	  TNode atom = polarity ? fact : fact[0];
	  if (atom.getKind() == kind::EQUAL) {
		d_equalityEngine.assertEquality( atom, polarity, exp );
	  }else{
		d_equalityEngine.assertPredicate( atom, polarity, exp );
	  }
    i++;
  }
  d_pending.clear();
}

//nf_exp is conjunction
void TheoryStrings::normalizeEquivalenceClass( Node eqc, std::vector< Node > & visited, std::vector< Node > & nf, std::vector< Node > & nf_exp ) {
	if( std::find( visited.begin(), visited.end(), eqc )!=visited.end() ){
		nf.push_back( eqc );
	}else{
		visited.push_back( eqc );
		if(d_normal_forms.find(eqc)==d_normal_forms.end() ){
			eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &d_equalityEngine );
			std::vector< std::vector< Node > > normal_forms;
			std::vector< std::vector< Node > > normal_forms_exp;
			std::vector< Node > normal_form_src;
			Node n_const;
			while( !eqc_i.isFinished() ){
				Node n = (*eqc_i);
				if( n.getKind() == kind::CONST_STRING || n.getKind() == kind::STRING_CONCAT ){
					std::vector<Node> nf_n;
					std::vector<Node> nf_exp_n;
					if( n.getKind() == kind::CONST_STRING ){
						if( n!=d_emptyString ){
							nf_n.push_back( n );
						}
					}else if( n.getKind() == kind::STRING_CONCAT ){
						for( unsigned i=0; i<n.getNumChildren(); i++ ){
							Node nr = d_equalityEngine.getRepresentative( n[i] );
							std::vector< Node > nf_temp;
							std::vector< Node > nf_exp_temp;
							normalizeEquivalenceClass( nr, visited, nf_temp, nf_exp_temp );
							if( d_conflict ){
								return;
							}
							if( nf.size()!=1 || nf[0]!=d_emptyString ){
								nf_n.insert( nf_n.end(), nf_temp.begin(), nf_temp.end() );
							}
							nf_exp_n.insert( nf_exp_n.end(), nf_exp_temp.begin(), nf_exp_temp.end() );
							if( nr!=n[i] ){
								nf_exp_n.push_back( NodeManager::currentNM()->mkNode( kind::EQUAL, n[i], nr ) );
							}
						}
					}
					normal_forms.push_back(nf_n);
					normal_forms_exp.push_back(nf_exp_n);
					normal_form_src.push_back(n);
				}
				++eqc_i;
			}
			if( !normal_forms.empty() ){
				Trace("strings-solve") << "Normal forms for equivlance class " << eqc << " : " << std::endl;
				for( unsigned i=0; i<normal_forms.size(); i++ ){
					Trace("strings-solve") << "#" << i << " (from " << normal_form_src[i] << ") : ";
					for( unsigned j=0; j<normal_forms[i].size(); j++ ){
						if(j>0) Trace("strings-solve") << ", ";
						Trace("strings-solve") << normal_forms[i][j];
					}
					Trace("strings-solve") << std::endl;
					Trace("strings-solve") << "   Explanation is : ";
					if(normal_forms_exp[i].size() == 0) {
						Trace("strings-solve") << "NONE";
					} else {
						for( unsigned j=0; j<normal_forms_exp[i].size(); j++ ){
							if(j>0) Trace("strings-solve") << " AND ";
							Trace("strings-solve") << normal_forms_exp[i][j];
						}
					}
					Trace("strings-solve") << std::endl;
				}
			}
			unsigned i = 0;
			for( unsigned j=1; j<normal_forms.size(); j++ ){
				Trace("strings-solve") << "Process normal form #0 against #" << j << "..." << std::endl;
				//the current explanation for why the prefix is equal
				std::vector< Node > curr_exp;
				curr_exp.insert(curr_exp.end(), normal_forms_exp[i].begin(), normal_forms_exp[i].end() );
				curr_exp.insert(curr_exp.end(), normal_forms_exp[j].begin(), normal_forms_exp[j].end() );
				curr_exp.push_back( NodeManager::currentNM()->mkNode( kind::EQUAL, normal_form_src[i], normal_form_src[j] ) );
				//ensure that normal_forms[i] and normal_forms[j] are the same modulo equality
				unsigned index_i = 0;
				unsigned index_j = 0;
				bool success;
				do
				{
					success = false;
					if(index_i==normal_forms[i].size() || index_j==normal_forms[j].size() ) {
						if( index_i==normal_forms[i].size() && index_j==normal_forms[j].size() ){
							//we're done
						}else{
							//the remainder must be empty
							unsigned k = index_i==normal_forms[i].size() ? j : i;
							unsigned index_k = index_i==normal_forms[i].size() ? index_j : index_i;
							while(!d_conflict && index_k<normal_forms[k].size()) {
								//can infer that this string must be empty
								Node eq_exp;
								if( curr_exp.empty() ) {
									eq_exp = NodeManager::currentNM()->mkConst(true);
								} else if( curr_exp.size() == 1 ) {
									eq_exp = curr_exp[0];
								} else {
									eq_exp = NodeManager::currentNM()->mkNode( kind::AND, curr_exp );
								}
								Node eq = NodeManager::currentNM()->mkNode( kind::EQUAL, d_emptyString, normal_forms[k][index_k] );
								Trace("strings-infer") << "Strings : Infer " << eq << " from " << eq_exp << std::endl;
								d_equalityEngine.assertEquality( eq, true, eq_exp );
								d_infer.push_back(eq);
								d_infer_exp.push_back(eq_exp);
								Trace("strings-solve-debug") << "Add to explanation : " << eq << std::endl;
								curr_exp.push_back( eq );
								index_k++;
							}
						}
					}else {
						Trace("strings-solve-debug") << "Process " << normal_forms[i][index_i] << " ... " << normal_forms[j][index_j] << std::endl;
						if(areEqual(normal_forms[i][index_i],normal_forms[j][index_j])){
							if( normal_forms[i][index_i]!=normal_forms[j][index_j] ){
								Node eq = NodeManager::currentNM()->mkNode( kind::EQUAL,normal_forms[i][index_i],
																								 normal_forms[j][index_j]);
								Trace("strings-solve-debug") << "Add to explanation : " << eq << std::endl;
								curr_exp.push_back(eq);
							}
							index_j++;
							index_i++;
							success = true;
						}else{
							EqcInfo * ei = getOrMakeEqcInfo( normal_forms[i][index_i] );
							Node length_term_i = ei->d_length_term;
							if( length_term_i.isNull()) {
								//typically shouldnt be necessary
								length_term_i = normal_forms[i][index_i];
							}
							length_term_i = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, length_term_i );
							EqcInfo * ej = getOrMakeEqcInfo( normal_forms[j][index_j] );
							Node length_term_j = ej->d_length_term;
							if( length_term_j.isNull()) {
								length_term_j = normal_forms[j][index_j];
							}
							length_term_j = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, length_term_j );
							//check if length(normal_forms[i][index]) == length(normal_forms[j][index])
							if( areEqual(length_term_i, length_term_j)  ){
								//merge equivalence classes if not already done so
								Node eq = NodeManager::currentNM()->mkNode( kind::EQUAL, normal_forms[i][index_i], normal_forms[j][index_j] );
								std::vector< Node > temp_exp;
								temp_exp.insert(temp_exp.end(), curr_exp.begin(), curr_exp.end() );
								temp_exp.push_back(NodeManager::currentNM()->mkNode( kind::EQUAL, length_term_i, length_term_j ));
								Node eq_exp = temp_exp.empty() ? NodeManager::currentNM()->mkConst(true) :
												temp_exp.size() == 1 ? temp_exp[0] : NodeManager::currentNM()->mkNode( kind::AND, temp_exp );
								Trace("strings-infer") << "Strings : Infer " << eq << " from " << eq_exp << std::endl;
								d_equalityEngine.assertEquality( eq, true, eq_exp );
								d_infer.push_back(eq);
								d_infer_exp.push_back(eq_exp);
								Trace("strings-solve-debug") << "Add to explanation : " << eq << std::endl;
								curr_exp.push_back( eq );
								success = true;
							}else{
								bool sendLemma = false;
								Node conc;
								std::vector< Node > antec;
								std::vector< Node > antec_new_lits;
								if( normal_forms[i][index_i].getKind() == kind::CONST_STRING ||
								    normal_forms[j][index_j].getKind() == kind::CONST_STRING) {
									Node const_str = normal_forms[i][index_i].getKind() == kind::CONST_STRING ? normal_forms[i][index_i] : normal_forms[j][index_j];
									Node other_str = normal_forms[i][index_i].getKind() == kind::CONST_STRING ? normal_forms[j][index_j] : normal_forms[i][index_i];
									if( other_str.getKind() == kind::CONST_STRING ) {
										unsigned len_short = const_str.getConst<String>().size() <= other_str.getConst<String>().size() ? const_str.getConst<String>().size() : other_str.getConst<String>().size();
										if(strncmp(const_str.getConst<String>().c_str(), other_str.getConst<String>().c_str(), len_short) == 0) {
											//same prefix
											//k is the index of the string that is shorter
											int k = const_str.getConst<String>().size()<other_str.getConst<String>().size() ? i : j;
											int index_k = const_str.getConst<String>().size()<other_str.getConst<String>().size() ? index_i : index_j;
											int l = const_str.getConst<String>().size()<other_str.getConst<String>().size() ? j : i;
											int index_l = const_str.getConst<String>().size()<other_str.getConst<String>().size() ? index_j : index_i;
											Node remainderStr = NodeManager::currentNM()->mkConst( ::CVC4::String(const_str.getConst<String>().substr(len_short) ) );
											Trace("strings-solve-debug") << "Break normal form of " << normal_forms[l][index_l] << " into " << normal_forms[k][index_k] << ", " << remainderStr << std::endl;
											normal_forms[l].insert( normal_forms[l].begin()+index_l + 1, remainderStr );
											normal_forms[l][index_l] = normal_forms[k][index_k];
											success = true;
										} else {
											//curr_exp is conflict
											sendLemma = true;
											antec.insert(antec.end(), curr_exp.begin(), curr_exp.end() );
										}
									} else {
										Assert( other_str.getKind()!=kind::STRING_CONCAT ); 
										Node firstChar = const_str.getConst<String>().size() == 1 ? const_str :
											NodeManager::currentNM()->mkConst( ::CVC4::String(const_str.getConst<String>().substr(0, 1) ) );
										//split the string
										Node sk = NodeManager::currentNM()->mkSkolem( "ssym_$$", normal_forms[i][index_i].getType(), "created for split" );
										// |sk| >= 0
										Node sk_len = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, sk );
										Node zero = NodeManager::currentNM()->mkConst( ::CVC4::Rational( 0 ) );
	  									Node sk_len_geq_zero = NodeManager::currentNM()->mkNode( kind::GEQ, sk_len, zero);

										Node eq1 = NodeManager::currentNM()->mkNode( kind::EQUAL, other_str, d_emptyString );
										Node eq2_m = NodeManager::currentNM()->mkNode( kind::EQUAL, other_str, 
													NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, firstChar, sk ) );
										Node eq2 = NodeManager::currentNM()->mkNode( kind::AND, eq2_m, sk_len_geq_zero ); 
										conc = NodeManager::currentNM()->mkNode( kind::OR, eq1, eq2 );
										Trace("strings-solve-debug") << "Break normal form constant/variable " << std::endl;
										sendLemma = true;
									}
								}else{
									antec.insert(antec.end(), curr_exp.begin(), curr_exp.end() );
									Node ldeq = NodeManager::currentNM()->mkNode( kind::EQUAL, length_term_i, length_term_j ).negate();
									if( d_equalityEngine.areDisequal( length_term_i, length_term_j, false ) ){
										antec.push_back( ldeq );
									}else{
										antec_new_lits.push_back(ldeq);
									}
									Node sk = NodeManager::currentNM()->mkSkolem( "ssym_$$", normal_forms[i][index_i].getType(), "created for split" );
									Node eq1 = NodeManager::currentNM()->mkNode( kind::EQUAL, normal_forms[i][index_i], 
												NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, normal_forms[j][index_j], sk ) );
									Node eq2 = NodeManager::currentNM()->mkNode( kind::EQUAL, normal_forms[j][index_j], 
												NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, normal_forms[i][index_i], sk ) );
									conc = NodeManager::currentNM()->mkNode( kind::OR, eq1, eq2 );
									sendLemma = true;
									// |sk| > 0
									Node sk_len = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, sk );
									Node zero = NodeManager::currentNM()->mkConst( ::CVC4::Rational( 0 ) );
									Node sk_gt_zero = NodeManager::currentNM()->mkNode( kind::GT, sk_len, zero);
									Trace("strings-lemma") << "Strings lemma : " << sk_gt_zero << std::endl;
									d_out->lemma(sk_gt_zero);
									//success will be false
								}
								Trace("strings-solve-debug2") << "sendLemma/success : " << sendLemma << " " << success << std::endl;
								if( sendLemma ){
									std::vector< TNode > antec_exp;
									for( unsigned i=0; i<antec.size(); i++ ){
										Trace("strings-solve-debug") << "Ask for explanation of " << antec[i] << std::endl;
										//assert
										if(antec[i].getKind() == kind::EQUAL) {
											//assert( hasTerm(antec[i][0]) );
											//assert( hasTerm(antec[i][1]) );
											Assert( areEqual(antec[i][0], antec[i][1]) );
										} else if( antec[i].getKind()==kind::NOT && antec[i][0].getKind()==kind::EQUAL ){
											Assert( hasTerm(antec[i][0][0]) );
											Assert( hasTerm(antec[i][0][1]) );
											Assert( d_equalityEngine.areDisequal(antec[i][0][0], antec[i][0][1], false) );
										}
										explain(antec[i], antec_exp);
										Trace("strings-solve-debug") << "Done." << std::endl;
									}
									for( unsigned i=0; i<antec_new_lits.size(); i++ ){
										antec_exp.push_back(antec_new_lits[i]);
									}
									Node ant;
									if( antec_exp.empty() ) {
										ant = NodeManager::currentNM()->mkConst(true);
									} else if( antec_exp.size()==1 ) {
										ant = antec_exp[0];
									} else {
										ant = NodeManager::currentNM()->mkNode( kind::AND, antec_exp );
									}
									if( conc.isNull() ){
										d_out->conflict(ant);
										Trace("strings-conflict") << "Strings conflict : " << ant << std::endl;
										d_conflict = true;
									}else{
										Node lem = NodeManager::currentNM()->mkNode( kind::IMPLIES, ant, conc );
										Trace("strings-lemma") << "Strings split lemma : " << lem << std::endl;
										d_out->lemma(lem);
									}
								}
							}
						}
						if( d_conflict ){
							success = false;
						}
					}
				}while(success);
			}

			//construct the normal form
			if( normal_forms.empty() ){
				nf.push_back( eqc );
			}else{
				//just take the first normal form
				nf.insert( nf.end(), normal_forms[0].begin(), normal_forms[0].end() );
				nf_exp.insert( nf_exp.end(), normal_forms_exp[0].begin(), normal_forms_exp[0].end() );
				if( eqc!=normal_form_src[0] ){
					nf_exp.push_back( NodeManager::currentNM()->mkNode( kind::EQUAL, eqc, normal_form_src[0] ) );
				}
			}
			//if( visited.empty() ){
				//TODO : cache?
			//}
		}else{
			nf.insert( nf.end(), d_normal_forms[eqc].begin(), d_normal_forms[eqc].end() );
		}
		visited.pop_back();
	}
}
bool TheoryStrings::hasTerm( Node a ){
  return d_equalityEngine.hasTerm( a );
}

bool TheoryStrings::areEqual( Node a, Node b ){
  if( a==b ){
    return true;
  }else if( hasTerm( a ) && hasTerm( b ) ){
    return d_equalityEngine.areEqual( a, b );
  }else{
    return false;
  }
}

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
