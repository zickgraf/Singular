/****************************************
*  Computer Algebra System SINGULAR     *
****************************************/
/***************************************************************
 *  File:    p_Mult_n__Template.cc
 *  Purpose: template for p_Mult_n
 *  Author:  obachman (Olaf Bachmann)
 *  Created: 8/00
 *******************************************************************/

/***************************************************************
 *
 *   Returns:  p*n
 *   Destroys: p
 *   Const:    n
 *
 ***************************************************************/
LINKAGE poly p_Mult_nn__T(poly p, const number n, const ring r)
{
  pAssume(!n_IsZero__T(n,r->cf));
  p_Test(p, r);

  poly q = p;
#ifdef HAVE_ZERODIVISORS
  poly old = NULL;
#endif
  //MYDEBUG while (p!=NULL && p_GetComp(p, r) <= 30)
  while (p!=NULL)
  {
#ifndef HAVE_ZERODIVISORS
    n_InpMult__T(pGetCoeff(p), n, r->cf);
    pIter(p);
#else
    number tmp = n_Mult__T(n, pGetCoeff(p), r->cf);
    if (!n_IsZero__T(tmp,r->cf))
    {
       number nc = pGetCoeff(p);
       p_SetCoeff0(p, tmp, r);
       n_Delete__T(&nc, r->cf);
       old = p;
       pIter(p);
    }
    else
    {
      n_Delete__T(&tmp, r->cf);
      if (old == NULL)
      {
        pIter(p);
        p_LmDelete(&q, r);
      }
      else
      {
        p_LmDelete(&p, r);
        pNext(old) = p;
      }
    }
#endif
  }
  p_Test(q, r);
  return q;
}
