/*********************                                                        */
/*! \file emptyset.cpp
 ** \verbatim
 ** Original author: Kshitij Bansal
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "util/emptyset.h"
#include <iostream>

using namespace std;

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, const EmptySet& asa) {
  return out << "emptyset(" << asa.getType() << ')';
}

}/* CVC4 namespace */
