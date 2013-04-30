/*********************                                                        */
/*! \file rewrite_priority.h
 ** \verbatim
 ** Original author: Tianyi Liang
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_public.h"

#ifndef __CVC4__REWRITEPRIORITY_H
#define __CVC4__REWRITEPRIORITY_H

#include <iostream>
#include <string>
#include <cstdio>

namespace CVC4 {

class CVC4_PUBLIC RewritePriority {

private:
  int d_p;
 
public:  
  RewritePriority() {}

  RewritePriority(const int p)
	  : d_p(p) {}

  RewritePriority(const std::string &s)
	  : d_p( atoi( s.c_str() ) ) {}

  ~RewritePriority() {}

  RewritePriority& operator =(const RewritePriority& y) {
    if(this != &y) d_p = y.d_p;
    return *this;
  }

  bool operator ==(const RewritePriority& y) const {
    return d_p == y.d_p ;
  }

  bool operator !=(const RewritePriority& y) const {
    return d_p != y.d_p ;
  }

  bool operator <(const RewritePriority& y) const {
    return d_p < y.d_p; 
  }

  bool operator >(const RewritePriority& y) const {
    return d_p > y.d_p ;
  }

  bool operator <=(const RewritePriority& y) const {
    return d_p <= y.d_p; 
  }
  
  bool operator >=(const RewritePriority& y) const {
    return d_p >= y.d_p ;
  }
  
  /*
    Convenience functions
   */
  std::string toString() const {
	char cp[50];
	std::sprintf(cp, "%d", d_p);
	std::string s( cp );
    return s;
  }

  int getPriority() const {
    return d_p;
  }
};/* class RewritePriority */

struct RewritePriorityHashFunction {
  size_t operator()(const ::CVC4::RewritePriority& s) const {
    return __gnu_cxx::hash<const char*>()(s.toString().c_str());
  }
};/* struct RewritePriorityHashFunction */


inline std::ostream& operator <<(std::ostream& os, const RewritePriority& s) CVC4_PUBLIC;
inline std::ostream& operator <<(std::ostream& os, const RewritePriority& s) {
  return os << s.toString();
}

}/* CVC4 namespace */

#endif /* __CVC4__REWRITEPRIORITY_H */
