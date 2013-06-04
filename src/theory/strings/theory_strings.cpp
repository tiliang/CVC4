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
	d_conflict( c, false )
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
  // register first

  // length left = length right
  //Node n_left = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, n[0]);
  //Node n_right = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, n[1]);
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
				//if(atom[0].getKind() == kind::STRING_CONCAT || atom[0].getKind() == kind::STRING_CONCAT
				//	|| (atom[0].getKind() == kind::VARIABLE && atom[0].getType() )) {
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
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
  while( !eqcs_i.isFinished() ){
	Node eqc = (*eqcs_i);
	//if eqc.getType is string
	if (eqc.getType().isString()) {
		EqcInfo* ei = getOrMakeEqcInfo( eqc, true );
		//get the constant for the equivalence class
		Node eqc_const = ei->d_constant;
		//get the length of eqc_const
		//int c_len = ...;
		eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &d_equalityEngine );
		while( !eqc_i.isFinished() ){
		  Node n = (*eqc_i);
		  //if n has a length l, and l != c_len, then report conflict
		  //d_equalityEngine.explainEquality(n,eqc_const,...);
		  // get explaination of length(n) == l
		  //d_out.conflict(...);

		  //if n is concat, and
		  //if n has not instantiatied the concat..length axiom
		  //then, add lemma
		  if( n.getKind() == kind::STRING_CONCAT || n.getKind() == kind::CONST_STRING ){
			if( d_length_inst.find(n)==d_length_inst.end() ){
				d_length_inst[n] = true;
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
					lsum = NodeManager::currentNM()->mkConst( ::CVC4::Rational( n.toString().size() ) );
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


  }
}

TheoryStrings::EqcInfo::EqcInfo(  context::Context* c ) : d_constant(c) {

}

TheoryStrings::EqcInfo * TheoryStrings::getOrMakeEqcInfo( Node eqc, bool doMake ) {
  std::map< Node, EqcInfo* >::iterator eqc_i = d_eqc_info.find( eqc );
  if( eqc_i==d_eqc_info.end() ){
    if( doMake ){
      EqcInfo* ei = new EqcInfo( getSatContext() );
      d_eqc_info[eqc] = ei;
      if( eqc.getKind() == kind::CONST_STRING ){
        ei->d_constant = eqc;
      }
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
  if( t.getKind() == kind::CONST_STRING ){
    getOrMakeEqcInfo( t, true );
  }
  if( t.getKind() == kind::STRING_LENGTH ){
	Trace("strings-debug") << "New length eqc : " << t << std::endl;
	Node r = d_equalityEngine.getRepresentative(t[0]);
	getOrMakeEqcInfo( r, true );
  }
}

/** called when two equivalance classes will merge */
void TheoryStrings::eqNotifyPreMerge(TNode t1, TNode t2){
	EqcInfo * e2 = getOrMakeEqcInfo(t2, false);
	if( e2 ){
		EqcInfo * e1 = getOrMakeEqcInfo( t1 );
		//add information from e2 to e1
		if( !e2->d_constant.get().isNull() ){
			Assert(e1->d_constant.get().isNull());
			e1->d_constant.set( e2->d_constant );
		}
	}
	if( d_equalityEngine.hasTerm( d_zero ) ){
		Node leqc;
		if( d_equalityEngine.areEqual(d_zero, t1) ){
			leqc = t2;
		}else if( d_equalityEngine.areEqual(d_zero, t2) ){
			leqc = t1;
		}
		if( !leqc.isNull() ){
			//scan equivalence class to see if we apply
			eq::EqClassIterator eqc_i = eq::EqClassIterator( leqc, &d_equalityEngine );
			while( !eqc_i.isFinished() ){
			  Node n = (*eqc_i);
			  if( n.getKind()==kind::STRING_LENGTH ){
				if( !d_equalityEngine.hasTerm( d_emptyString ) || !d_equalityEngine.areEqual(n[0], d_emptyString ) ){
					Trace("strings-debug") << "Processing possible inference." << n << std::endl;
					//apply the rule length(n[0])==0 => n[0] == ""
					Node eq = NodeManager::currentNM()->mkNode( kind::EQUAL, n[0], d_emptyString );
					d_pending.push_back( eq );
					Node eq_exp = NodeManager::currentNM()->mkNode( kind::EQUAL, n, d_zero );
					d_pending_exp[eq] = eq_exp;
					Trace("strings-infer") << "Strings : Infer " << eq << " from " << eq_exp << std::endl;
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



}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
