/****************************************
*  Computer Algebra System SINGULAR     *
****************************************/
/*
*  ABSTRACT -  Routines for Spoly creation and reductions
*/

// #define PDEBUG 2



#include "kernel/mod2.h"
#include "misc/options.h"
#include "kernel/GBEngine/kutil.h"
#include "coeffs/numbers.h"
#include "polys/monomials/p_polys.h"
#include "polys/templates/p_Procs.h"
#include "polys/nc/nc.h"
#ifdef HAVE_RINGS
#include "kernel/polys.h"
#endif
#ifdef HAVE_SHIFTBBA
#include "polys/shiftop.h"
#endif

#ifdef KDEBUG
VAR int red_count = 0;
VAR int create_count = 0;
// define this if reductions are reported on TEST_OPT_DEBUG
#define TEST_OPT_DEBUG_RED
#endif

/***************************************************************
 *
 * Reduces PR with PW
 * Assumes PR != NULL, PW != NULL, Lm(PW) divides Lm(PR)
 *
 * returns 0: okay
 *         1: tailRing changed
 *         -1: cannot change tailRing
 *         2: cannot change tailRing: strat==NULL
 *
 ***************************************************************/
int ksReducePolyZ(LObject* PR,
                 TObject* PW,
                 poly spNoether,
                 number *coef,
                 kStrategy strat)
{
#ifdef KDEBUG
  red_count++;
#ifdef TEST_OPT_DEBUG_RED
//  if (TEST_OPT_DEBUG)
//  {
//    Print("Red %d:", red_count); PR->wrp(); Print(" with:");
//    PW->wrp();
//    //printf("\necart(PR)-ecart(PW): %i\n",PR->ecart-PW->ecart);
//    //pWrite(PR->p);
//  }
#endif
#endif
  int ret = 0;
  ring tailRing = PR->tailRing;
  kTest_L(PR,tailRing);
  kTest_T(PW);

  poly p1 = PR->GetLmTailRing();   // p2 | p1
  poly p2 = PW->GetLmTailRing();   // i.e. will reduce p1 with p2; lm = LT(p1) / LM(p2)
  poly t2 = pNext(p2), lm = p1;    // t2 = p2 - LT(p2); really compute P = LC(p2)*p1 - LT(p1)/LM(p2)*p2
  assume(p1 != NULL && p2 != NULL);// Attention, we have rings and there LC(p2) and LC(p1) are special
  p_CheckPolyRing(p1, tailRing);
  p_CheckPolyRing(p2, tailRing);

  pAssume1(p2 != NULL && p1 != NULL &&
           p_DivisibleBy(p2,  p1, tailRing));

  pAssume1(p_GetComp(p1, tailRing) == p_GetComp(p2, tailRing) ||
           (p_GetComp(p2, tailRing) == 0 &&
            p_MaxComp(pNext(p2),tailRing) == 0));

#ifdef HAVE_PLURAL
  if (rIsPluralRing(currRing))
  {
    // for the time being: we know currRing==strat->tailRing
    // no exp-bound checking needed
    // (only needed if exp-bound(tailring)<exp-b(currRing))
    if (PR->bucket!=NULL)  nc_kBucketPolyRed_Z(PR->bucket, p2,coef);
    else
    {
      poly _p = (PR->t_p != NULL ? PR->t_p : PR->p);
      assume(_p != NULL);
      nc_PolyPolyRed(_p, p2,coef, currRing);
      if (PR->t_p!=NULL) PR->t_p=_p; else PR->p=_p;
      PR->pLength=0; // usually not used, GetpLength re-computes it if needed
    }
    return 0;
  }
#endif

  if (t2==NULL)           // Divisor is just one term, therefore it will
  {                       // just cancel the leading term
    // adjust lead coefficient if needed
    if (! n_IsOne(pGetCoeff(p2), tailRing->cf))
    {
      number bn = pGetCoeff(lm);
      number an = pGetCoeff(p2);
      int ct = ksCheckCoeff(&an, &bn, tailRing->cf);    // Calculate special LC
      p_SetCoeff(lm, bn, tailRing);
      if ((ct == 0) || (ct == 2))
      PR->Tail_Mult_nn(an);
      if (coef != NULL) *coef = an;
      else n_Delete(&an, tailRing->cf);
    }
    PR->LmDeleteAndIter();
    if (coef != NULL) *coef = n_Init(1, tailRing->cf);
    return 0;
  }

  p_ExpVectorSub(lm, p2, tailRing); // Calculate the Monomial we must multiply to p2

  //if (tailRing != currRing)
  {
    // check that reduction does not violate exp bound
    while (PW->max_exp != NULL && !p_LmExpVectorAddIsOk(lm, PW->max_exp, tailRing))
    {
      // undo changes of lm
      p_ExpVectorAdd(lm, p2, tailRing);
      if (strat == NULL) return 2;
      if (! kStratChangeTailRing(strat, PR, PW)) return -1;
      tailRing = strat->tailRing;
      p1 = PR->GetLmTailRing();
      p2 = PW->GetLmTailRing();
      t2 = pNext(p2);
      lm = p1;
      p_ExpVectorSub(lm, p2, tailRing);
      ret = 1;
    }
  }

#ifdef HAVE_SHIFTBBA
  poly lmRight;
  if (tailRing->isLPring)
  {
    assume(PR->shift == 0);
    assume(PW->shift == si_max(p_mFirstVblock(PW->p, tailRing) - 1, 0));
    k_SplitFrame(lm, lmRight, PW->shift + 1, tailRing);
  }
#endif

  // take care of coef buisness
  if (! n_IsOne(pGetCoeff(p2), tailRing->cf))
  {
    number bn = pGetCoeff(lm);
    number an = pGetCoeff(p2);
    int ct = ksCheckCoeff(&an, &bn, tailRing->cf);    // Calculate special LC
    p_SetCoeff(lm, bn, tailRing);
#ifdef HAVE_SHIFTBBA
    if (tailRing->isLPring) pSetCoeff0(p1, bn); // lm doesn't point to p1 anymore, if the coef was a pointer, it has been deleted
#endif
    if ((ct == 0) || (ct == 2))
      PR->Tail_Mult_nn(an);
    if (coef != NULL) *coef = an;
    else n_Delete(&an, tailRing->cf);
  }
  else
  {
    if (coef != NULL) *coef = n_Init(1, tailRing->cf);
  }


  // and finally,
#ifdef HAVE_SHIFTBBA
  if (tailRing->isLPring)
  {
    PR->Tail_Minus_mm_Mult_qq(lm, tailRing->p_Procs->pp_Mult_mm(t2, lmRight, tailRing), pLength(t2), spNoether);
  }
  else
#endif
  {
    PR->Tail_Minus_mm_Mult_qq(lm, t2, pLength(t2) /*PW->GetpLength() - 1*/, spNoether);
  }
  assume(PW->GetpLength() == pLength(PW->p != NULL ? PW->p : PW->t_p));
  PR->LmDeleteAndIter();

  return ret;
}


poly mergepolys(poly p, poly q) {
	poly merged = pOne();
	poly tail = merged;
	
	while(p != NULL && q != NULL) {
		int comp_p = pGetComp(p);
		int comp_q = pGetComp(q);
		if(comp_p == comp_q) {
			printf("cannot merge polys with common components\n");
			exit(1);
		}
		if(comp_p < comp_q) {
			pNext(tail) = p;
			pIter(p);
			pIter(tail);
		}
		else {
			pNext(tail) = q;
			pIter(q);
			pIter(tail);
		}
	}

	if(p != NULL) {
		pNext(tail) = p;	
	}

	if(q != NULL) {
		pNext(tail) = q;	
	}

	return pNext(merged);
}

int ksReducePoly(LObject* PR,
                 TObject* PW,
                 poly spNoether,
                 number *coef,
                 kStrategy strat)
{
  //printf("entering ksReducePoly\n");
  
#if 1
	int dividend_additional_comp = 735;
	int divisor_additional_comp = 738;
	poly transformation_coeffs_dividend = NULL;
	int transformation_coeffs_dividend_bucket = -1;
	int transformation_coeffs_dividend_length = 0;
	poly transformation_coeffs_divisor = NULL;
	int transformation_coeffs_divisor_length = 0;
if(strat != NULL && strat->syzComp > 0) {

	//if(PR->transformation_coeffs == NULL) {
		// extract transformation coeffs of dividend and add one
	if(PR->bucket != NULL) {
		if(PR->p == NULL) {
			printf("PR->p is NULL, reducing a syzygy?\n");
			exit(1);
		}
		if(pGetComp(PR->p) > 30) {
			printf("pGetComp(PR->p) > 30, reducing a syzygy?\n");
			exit(1);
		}
		
		for(int myi = 1; myi <= PR->bucket->buckets_used; myi++) {
			if(PR->bucket->buckets[myi] != NULL) {
				
				poly asd = PR->bucket->buckets[myi];
				poly q = pOne();
				pSetComp(q, dividend_additional_comp);
				
				if(pGetComp(asd) > 30) {
					int new_transformation_coeffs_dividend_length = pLength(asd);

					//transformation_coeffs_dividend = mergepolys(transformation_coeffs_dividend, asd);
					transformation_coeffs_dividend = pAdd(transformation_coeffs_dividend, asd);

					if(pLength(transformation_coeffs_dividend) != transformation_coeffs_dividend_length + new_transformation_coeffs_dividend_length) {
						printf("Merge did not preserve length\n");	
						exit(1);
					}
					
					// replace tail by one or NULL
					PR->bucket->buckets_length[myi] -= new_transformation_coeffs_dividend_length;
					PR->pLength -= new_transformation_coeffs_dividend_length;

					if(PR->bucket->buckets_length[myi] != 0) {
						printf("assertion failed, bucket length is not 0\n");
						exit(1);	
					}
					
					if(transformation_coeffs_dividend_length == 0) {
						// first transformation coeffs found -> add one
						transformation_coeffs_dividend_bucket = myi;
						PR->bucket->buckets[myi] = q;

						PR->bucket->buckets_length[myi]++;
						PR->pLength++;
					}
					else {
						PR->bucket->buckets[myi] = NULL;
					}
							
					transformation_coeffs_dividend_length += new_transformation_coeffs_dividend_length;
				}
				else {
				
					while (pNext(asd) != NULL)
					{
						if(pGetComp(pNext(asd)) > 30) {
		
							int new_transformation_coeffs_dividend_length = pLength(pNext(asd));

							//transformation_coeffs_dividend = mergepolys(transformation_coeffs_dividend, pNext(asd));
							transformation_coeffs_dividend = pAdd(transformation_coeffs_dividend, pNext(asd));

							if(pLength(transformation_coeffs_dividend) != transformation_coeffs_dividend_length + new_transformation_coeffs_dividend_length) {
								printf("Merge did not preserve length\n");	
								exit(1);
							}
							
							// replace tail by one or NULL
							PR->bucket->buckets_length[myi] -= new_transformation_coeffs_dividend_length;
							PR->pLength -= new_transformation_coeffs_dividend_length;

							if(transformation_coeffs_dividend_length == 0) {
								// first transformation coeffs found -> add one
								transformation_coeffs_dividend_bucket = myi;
								pNext(asd) = q;

								PR->bucket->buckets_length[myi]++;
								PR->pLength++;
							}
							else {
								pNext(asd) = NULL;
							}
							
							transformation_coeffs_dividend_length += new_transformation_coeffs_dividend_length;
							
							break;
						}
						pIter(asd);
					}
				}
			}
		}
	}
	else {
		printf("bucket is NULL\n");
		exit(1);
	}
	if(transformation_coeffs_dividend == NULL && strat != NULL && strat->syzComp > 0) {
		printf("could not find transformation coeffs of dividend\n");
		exit(1);
	}

		PR->transformation_coeffs = transformation_coeffs_dividend;
	//}
	
	//if(PW->transformation_coeffs == NULL) {
	// extract transformation coeffs of divisor and add one
	if(PW->p != NULL) {
		
		poly asd = PW->p;
		//poly q = pOne();
		//pSetComp(q, divisor_additional_comp);
		
		while (pNext(asd) != NULL)
		{
			if(pGetComp(pNext(asd)) > 30) {
				transformation_coeffs_divisor = pNext(asd);
				//pNext(asd) = q;
				pNext(asd) = NULL;
				
				transformation_coeffs_divisor_length = pLength(transformation_coeffs_divisor);

				PW->pLength -= transformation_coeffs_divisor_length;
				//PW->pLength++;
				
				break;
			}
			pIter(asd);
		}
	}
	else {
		printf("PW->p is NULL, reducing by zero?\n");
		exit(1);
	}
	if(transformation_coeffs_divisor == NULL && strat != NULL && strat->syzComp > 0) {
		printf("could not find transformation coeffs of divisor\n");
		exit(1);
	}
	PW->transformation_coeffs = transformation_coeffs_divisor;
}
#endif
	
#ifdef KDEBUG
  red_count++;
#ifdef TEST_OPT_DEBUG_RED
//  if (TEST_OPT_DEBUG)
//  {
//    Print("Red %d:", red_count); PR->wrp(); Print(" with:");
//    PW->wrp();
//    //printf("\necart(PR)-ecart(PW): %i\n",PR->ecart-PW->ecart);
//    //pWrite(PR->p);
//  }
#endif
#endif

  
    //Print("Red %d:", red_count); PR->wrp(); Print(" with:");
    //PW->wrp();
	//pWrite(PR->p);
	//printf("\n");
    //pWrite(PW->p);
	//printf("\n");
  
	//{
	//	//p1.wrp();printf("\n");
	//	printf("PR components:\n");
	//	poly q = PR->p;
	//	while (q != NULL)
	//	{
	//		printf("%d\n", pGetComp(q));
	//		pIter(q);
	//	}
	//}
  
	//printf("################################\n");
  int ret = 0;
  ring tailRing = PR->tailRing;
  kTest_L(PR,tailRing);
  kTest_T(PW);

  poly p1 = PR->GetLmTailRing();   // p2 | p1
  poly p2 = PW->GetLmTailRing();   // i.e. will reduce p1 with p2; lm = LT(p1) / LM(p2)
  poly t2 = pNext(p2), lm = p1;    // t2 = p2 - LT(p2); really compute P = LC(p2)*p1 - LT(p1)/LM(p2)*p2
  assume(p1 != NULL && p2 != NULL);// Attention, we have rings and there LC(p2) and LC(p1) are special
  p_CheckPolyRing(p1, tailRing);
  p_CheckPolyRing(p2, tailRing);

  pAssume1(p2 != NULL && p1 != NULL &&
           p_DivisibleBy(p2,  p1, tailRing));

  pAssume1(p_GetComp(p1, tailRing) == p_GetComp(p2, tailRing) ||
           (p_GetComp(p2, tailRing) == 0 &&
            p_MaxComp(pNext(p2),tailRing) == 0));

#ifdef HAVE_PLURAL
  if (rIsPluralRing(currRing))
  {
    // for the time being: we know currRing==strat->tailRing
    // no exp-bound checking needed
    // (only needed if exp-bound(tailring)<exp-b(currRing))
    if (PR->bucket!=NULL)  nc_kBucketPolyRed_Z(PR->bucket, p2,coef);
    else
    {
      poly _p = (PR->t_p != NULL ? PR->t_p : PR->p);
      assume(_p != NULL);
      nc_PolyPolyRed(_p, p2,coef, currRing);
      if (PR->t_p!=NULL) PR->t_p=_p; else PR->p=_p;
      PR->pLength=0; // usually not used, GetpLength re-computes it if needed
    }
	printf("aaaaaaa1");
	exit(1);
    return 0;
  }
#endif

  if (t2==NULL && false)           // Divisor is just one term, therefore it will
  {                       // just cancel the leading term
    PR->LmDeleteAndIter();
    if (coef != NULL) *coef = n_Init(1, tailRing->cf);
	printf("unhandled case: divisor is only a single term\n");
	exit(1);
    return 0;
  }

  p_ExpVectorSub(lm, p2, tailRing); // Calculate the Monomial we must multiply to p2

  //printf("reduce result 0:\n");
  //PR->wrp();
  //printf("\n");
  //printf("lm 0:\n");
  //p_wrp(lm,currRing,tailRing);
  //printf("\n");

  //if (tailRing != currRing)
  {
    // check that reduction does not violate exp bound
    while (PW->max_exp != NULL && !p_LmExpVectorAddIsOk(lm, PW->max_exp, tailRing))
    {
      // undo changes of lm
      p_ExpVectorAdd(lm, p2, tailRing);
      if (strat == NULL) {
			printf("aaaaaaa3");
			exit(1);
		  return 2;
	  }
      if (! kStratChangeTailRing(strat, PR, PW)) {
			printf("aaaaaaa4");
			exit(1);
		  return -1;
	  }
      tailRing = strat->tailRing;
      p1 = PR->GetLmTailRing();
      p2 = PW->GetLmTailRing();
      t2 = pNext(p2);
      lm = p1;
      p_ExpVectorSub(lm, p2, tailRing);
      ret = 1;
    }
  }

  

  //printf("asd\n");
  

#ifdef HAVE_SHIFTBBA
  poly lmRight;
  if (tailRing->isLPring)
  {
    assume(PR->shift == 0);
    assume(PW->shift == si_max(p_mFirstVblock(PW->p, tailRing) - 1, 0));
    k_SplitFrame(lm, lmRight, PW->shift + 1, tailRing);
  }
#endif

  //printf("reduce result 1:\n");
  //PR->wrp();
  //printf("\n");
  //printf("lm 1:\n");
  //p_wrp(lm,currRing,tailRing);
  //printf("\n");

  // take care of coef buisness
  if (! n_IsOne(pGetCoeff(p2), tailRing->cf))
  {
    number bn = pGetCoeff(lm);
    number an = pGetCoeff(p2);
    int ct = ksCheckCoeff(&an, &bn, tailRing->cf);    // Calculate special LC
    p_SetCoeff(lm, bn, tailRing);
#ifdef HAVE_SHIFTBBA
    if (tailRing->isLPring) pSetCoeff0(p1, bn); // lm doesn't point to p1 anymore, if the coef was a pointer, it has been deleted
#endif

	//pWrite(ppMult_nn(pOne(), an));
	
    if ((ct == 0) || (ct == 2)) {
	  if(strat != NULL && strat->syzComp > 0) {
	      PR->transformation_coeffs = pMult_nn(PR->transformation_coeffs, an);
	  }
      PR->Tail_Mult_nn(an);
	}
    if (coef != NULL) *coef = an;
    else n_Delete(&an, tailRing->cf);
  }
  else
  {
    if (coef != NULL) *coef = n_Init(1, tailRing->cf);
  }

  //printf("reduce result 2:\n");
  //PR->wrp();
  //printf("\n");
  //printf("lm 2:\n");
  //p_wrp(lm,currRing,tailRing);
  //printf("\n");

  poly store = NULL;

  // and finally,
#ifdef HAVE_SHIFTBBA
  if (tailRing->isLPring)
  {
	printf("unhandled case\n");
    PR->Tail_Minus_mm_Mult_qq(lm, tailRing->p_Procs->pp_Mult_mm(t2, lmRight, tailRing), pLength(t2), spNoether);
  }
  else
#endif
  {


  
  
  
        
    // store additional component
    //if(t2 != NULL) {
    //  poly p = t2;
    //  while (pNext(p) != NULL)
    //  {
    //  	if (pGetComp(pNext(p)) > 30)
    //  	{
    //      store = pNext(p);
    //  	  p->next = NULL;
	//	  PW->pLength--;
    //  	  
    //  	  if (pNext(store) != NULL) {
    //  		  printf("assertion failed, pNext is not NULL, before reduce\n");
    //  		  exit(1);
    //  	  }

    //  	  break;
    //  	}
    //  	else
    //  	{
    //  	  pIter(p);
    //  	}
    //  }
    //}


    
    //Print("Red %d:", red_count); PR->wrp(); Print(" with:");
    //PW->wrp();
	//printf("Reduce lead monom?\n");
    //pWrite(PR->p);
  
	//for(int i=0;i<=PR->bucket->buckets_used;i++) {
	//	printf("bucket %d:\n", i);
	//		if(PR->bucket->buckets[i] != NULL) {
	//			pWrite(PR->bucket->buckets[i]);
	//		}
	//}

	//
    //Print("with:\n");
    //pWrite(t2);
	
    // remove additional components from divisor
    //if(PW->p != NULL) {
    //    
    //    poly asd = PW->p;
    //    
    //    while (pNext(asd) != NULL)
    //    {
    //        if(pGetComp(pNext(asd)) > 30) {
    //            poly tail = pNext(asd);
    //            asd->next = NULL;
    //            
    //            PW->pLength--;
    //            
    //            while (pNext(tail) != NULL) {
    //                PW->pLength--;
    //                pIter(tail);
    //            }
    //            break;
    //        }
    //        pIter(asd);
    //    }
    //}
	
  
	//printf("one ksReducePoly\n");
	//pWrite(lm);
	if(strat != NULL && strat->syzComp > 0) {
		PR->transformation_coeffs = pMinus_mm_Mult_qq(PR->transformation_coeffs, lm, PW->transformation_coeffs);
	}
    PR->Tail_Minus_mm_Mult_qq(lm, t2, pLength(t2) /*PW->GetpLength() - 1*/, spNoether);

	// correct bucket length
	//if(PR->bucket != NULL) {
	//	// leading monomial is not stored in bucket, right?
	//	int sum = 1;
	//	for(int myi = 1; myi <= PR->bucket->buckets_used; myi++) {

	//		if(PR->bucket->buckets[myi] != NULL) {
	//			
	//			poly asd = PR->bucket->buckets[myi];
	//			int cur_length = pLength(asd);
	//			PR->bucket->buckets_length[myi] = cur_length;
	//			sum += cur_length;
	//			
	//		}
	//	}
	//	PR->pLength = sum;
	//}
	//else {
	//	printf("bucket is NULL\n");	
	//}

	// remove additional components from dividend
	//if(PR->bucket != NULL) {
	//	for(int myi = 1; myi <= PR->bucket->buckets_used; myi++) {
	//		if(PR->bucket->buckets[myi] != NULL) {
	//			
	//			poly asd = PR->bucket->buckets[myi];
	//			
	//			if(pGetComp(asd) > 30) {
	//				int tail_length = pLength(asd);
	//				PR->bucket->buckets[myi] = NULL;
	//				
	//				PR->bucket->buckets_length[myi] -= tail_length;
	//				PR->pLength -= tail_length;
	//				
	//				if(PR->bucket->buckets_length[myi] != 0) {
	//					printf("assertion failed, bucket length is not 0\n");
	//					exit(1);	
	//				}
	//			}
	//			else {
	//			
	//				while (pNext(asd) != NULL)
	//				{
	//					if(pGetComp(pNext(asd)) > 30) {
	//						int tail_length = pLength(pNext(asd));
	//						asd->next = NULL;
	//						
	//						PR->bucket->buckets_length[myi] -= tail_length;
	//						PR->pLength -= tail_length;

	//						break;
	//					}
	//					pIter(asd);
	//				}
	//			}
	//		}
	//	}
	//}
	//else {
	//	printf("bucket is NULL\n");	
	//}
	  
	
    // remove additional components from divisor
    //if(PW->p != NULL) {
    //    
    //    poly asd = PW->p;
    //    
    //    while (pNext(asd) != NULL)
    //    {
    //        if(pGetComp(pNext(asd)) > 30) {
    //            poly tail = pNext(asd);
    //            asd->next = NULL;
    //            
    //            PW->pLength--;
    //            
    //            while (pNext(tail) != NULL) {
    //                PW->pLength--;
    //                pIter(tail);
    //            }
    //            break;
    //        }
    //        pIter(asd);
    //    }
    //}
	
  
    // restore store
	//if(store != NULL) {
	//  if (t2 == NULL) {
	//  	pNext(p2) = store;	
	//  }
	//  else {
	//  	poly asd = t2;
	//  	while (pNext(asd) != NULL)
	//  	{
	//  		pIter(asd);
	//  	}
	//  	pNext(asd) = store;
	//	PW->pLength++;
	//  }
	//}

  
	//printf("to:\n");
	//for(int i=0;i<=PR->bucket->buckets_used;i++) {
	//	printf("bucket %d:\n", i);
	//	pWrite(PR->bucket->buckets[i]);
	//}

	
  
  }

  
	
  
  assume(PW->GetpLength() == pLength(PW->p != NULL ? PW->p : PW->t_p));
  PR->LmDeleteAndIter();

  //{	
  //  LObject* h = PR;
  //  // add some additional components to dividend
  //  for(int ii=0;ii<100;ii++)
  //  {
  //  	if(h->bucket != NULL && h->bucket->buckets[h->bucket->buckets_used] != NULL) {
  //  		//int target_comp = pGetComp(store);
  //  		int target_comp = 730 + 1 + ii + 1;
  //  		
  //  		poly asd = h->bucket->buckets[h->bucket->buckets_used];
  //  		if (asd == NULL) {
  //  			printf("assertion failed, asd is NULL\n");
  //  			exit(1);
  //  		}
  //  		
  //  		while (pNext(asd) != NULL)
  //  		{
  //  			if(pGetComp(pNext(asd)) == target_comp) {
  //  				//printf("assertion failed, asd should not have a common component with store\n");
  //  				break;
  //  				//exit(1);
  //  			}
  //  			if(pGetComp(pNext(asd)) > target_comp) {
  //  				poly q = pOne();
  //  				pSetComp(q, target_comp);
  //  				pNext(q) = pNext(asd);
  //  				pNext(asd) = q;
  //  				h->bucket->buckets_length[h->bucket->buckets_used]++;
  //  				h->pLength++;
  //  				break;
  //  			}
  //  			pIter(asd);
  //  		}

  //  		if(pNext(asd) == NULL) {
  //  			poly q = pOne();
  //  			pSetComp(q, target_comp);
  //  			pNext(asd) = q;
  //  			h->bucket->buckets_length[h->bucket->buckets_used]++;
  //  			h->pLength++;
  //  		}
  //  	}
  //  }
  //}
	

	//{
	//	printf("PR components after reduce:\n");
	//	poly q = PR->p;
	//	while (q != NULL)
	//	{
	//		printf("%d\n", pGetComp(q));
	//		pIter(q);
	//	}
	//}
  

	
	
  //if( store != NULL)
  //	printf("%d\n", pGetComp(store));
  
  //// overwrite store
  ////if(t2 != NULL) {
  //  poly p = PR->p;
  //  while (pNext(p) != NULL)
  //  {
  //  	// delete monomial at component pGetComp(store)
  //  	if (pGetComp(pNext(p)) == pGetComp(store))
  //  	{
  //  	  printf("really delete\n");
  //  	  pNext(p) = pNext(pNext(p));
  //  	  break;
  //  	}
  //  	else
  //  	{
  //  	  pIter(p);
  //  	}
  //  }
  ////}
  
  //printf("reduce result 3:\n");
  //pWrite(PR->p);
  //printf("\n");
  //printf("lm 3:\n");
  //p_wrp(lm,currRing,tailRing);
  //printf("\n");
  //
  //
  
  
  
	// also add store to result
	//if(store != NULL) {
	//	poly asd = PR->bucket->buckets[PR->bucket->buckets_used];
    //  	if (asd == NULL) {
    //  	    printf("assertion failed, asd is NULL\n");
    //  	    exit(1);
    //  	}
	//	
	//	
	//  	while (pNext(asd) != NULL)
	//  	{
	//		if(pGetComp(pNext(asd)) == pGetComp(store)) {
	//			//printf("assertion failed, asd should not have a common component with store\n");
	//			break;
	//			//exit(1);
	//		}
	//		if(pGetComp(pNext(asd)) > pGetComp(store)) {
	//			poly q = pOne();
	//		    pSetComp(q, pGetComp(store));
	//			pNext(q) = pNext(asd);
	//			pNext(asd) = q;
	//			PR->bucket->buckets_length[PR->bucket->buckets_used]++;
	//			PR->pLength++;
	//			break;
	//		}
	//  		pIter(asd);
	//  	}

	//	if(pNext(asd) == NULL) {
	//		poly q = pOne();
	//		pSetComp(q, pGetComp(store));
	//		pNext(asd) = q;
	//		PR->bucket->buckets_length[PR->bucket->buckets_used]++;
	//		PR->pLength++;
	//	}
	//}
	//
	//
	
#if 1
  
    if(strat == NULL || strat->syzComp == 0) {
		return ret;	
	}

    // deal with the transformation coeffs
    // dividend
	// dividend_monom
	poly dividend_monom = NULL;
	if(PR->bucket != NULL) {
		poly qwe = PR->p;

		if(pGetComp(qwe) == dividend_additional_comp) {
			if(dividend_monom != NULL) {
				printf("a: multiple monomials with component 731 in dividend\n");
				exit(1);
			}
			dividend_monom = qwe;
			
			if(pNext(qwe) != NULL && pGetComp(pNext(qwe)) != divisor_additional_comp) {
				printf("there is a component which is different from 732 after 731\n");
				exit(1);
			}

			PR->pLength--;

			PR->p = pNext(qwe);
			pNext(dividend_monom) = NULL;
		}
		
		for(int myi = 1; myi <= PR->bucket->buckets_used; myi++) {
			if(PR->bucket->buckets[myi] != NULL) {
				
				poly asd = PR->bucket->buckets[myi];
				
				if(pGetComp(asd) == dividend_additional_comp) {
					if(dividend_monom != NULL) {
						printf("b: multiple monomials with component 731 in dividend\n");
						exit(1);
					}
					dividend_monom = asd;
					
					if(pNext(dividend_monom) != NULL && pGetComp(pNext(dividend_monom)) != divisor_additional_comp) {
						printf("there is a component which is different from 732 after 731\n");
						exit(1);
					}

					PR->bucket->buckets_length[myi]--;
					PR->pLength--;

					PR->bucket->buckets[myi] = pNext(dividend_monom);
					pNext(dividend_monom) = NULL;
				}
				else {
				
					while (pNext(asd) != NULL)
					{
						if(pGetComp(pNext(asd)) == dividend_additional_comp) {
							if(dividend_monom != NULL) {
								printf("c: multiple monomials with component 731 in dividend\n");
								exit(1);
							}
							dividend_monom = pNext(asd);
							
							if(pNext(dividend_monom) != NULL && pGetComp(pNext(dividend_monom)) != divisor_additional_comp) {
								printf("there is a component which is different from 732 after 731\n");
								exit(1);
							}

							PR->bucket->buckets_length[myi]--;
							PR->pLength--;

							pNext(asd) = pNext(pNext(asd));
							pNext(dividend_monom) = NULL;
							
							break;
						}
						pIter(asd);
					}
				}
			}
		}
	}
	else {
		printf("bucket is NULL\n");
		exit(1);
	}
	if(dividend_monom == NULL) {
		printf("could not find dividend_monom\n");
		exit(1);
	}
	//// divisor_monom
	//poly divisor_monom = NULL;
	//if(PR->bucket != NULL) {
	//	for(int myi = 1; myi <= PR->bucket->buckets_used; myi++) {
	//		if(PR->bucket->buckets[myi] != NULL) {
	//			
	//			poly asd = PR->bucket->buckets[myi];
	//			
	//			if(pGetComp(asd) == divisor_additional_comp) {
	//				if(divisor_monom != NULL) {
	//					printf("multiple monomials with component 732 in dividend\n");
	//					exit(1);
	//				}
	//				divisor_monom = asd;
	//				
	//				if(pNext(asd) != NULL) {
	//					printf("there is another component after 732\n");
	//					exit(1);
	//				}

	//				PR->bucket->buckets_length[myi]--;
	//				PR->pLength--;

	//				PR->bucket->buckets[myi] = pNext(asd);
	//				pNext(divisor_monom) = NULL;
	//			}
	//			else {
	//			
	//				while (pNext(asd) != NULL)
	//				{
	//					if(pGetComp(pNext(asd)) == divisor_additional_comp) {
	//						if(divisor_monom != NULL) {
	//							printf("multiple monomials with component 732 in dividend\n");
	//							exit(1);
	//						}
	//						divisor_monom = pNext(asd);
	//						
	//						if(pNext(pNext(asd)) != NULL) {
	//							printf("there is another component after 732\n");
	//							exit(1);
	//						}

	//						PR->bucket->buckets_length[myi]--;
	//						PR->pLength--;

	//						pNext(asd) = pNext(pNext(asd));
	//						pNext(divisor_monom) = NULL;
	//						
	//						break;
	//					}
	//					pIter(asd);
	//				}
	//			}
	//		}
	//	}
	//}
	//else {
	//	printf("bucket is NULL\n");
	//	exit(1);
	//}
	//if(divisor_monom == NULL) {
	//	printf("could not find divisor_monom\n");
	//	exit(1);
	//}

	//pSetComp(dividend_monom, 0);
	//pSetComp(divisor_monom, 0);

	//pWrite(dividend_monom);
	//pWrite(divisor_monom);
	
	// construct new transformaton_coeffs
	//poly transformation_coeffs_dividend_multi_coeff = pMult_mm(transformation_coeffs_dividend, dividend_monom);
	//poly transformation_coeffs_divisor_multi_coeff = ppMult_mm(transformation_coeffs_divisor, divisor_monom);
	//poly transformation_coeffs = pAdd(transformation_coeffs_dividend_multi_coeff, transformation_coeffs_divisor_multi_coeff);
	//poly transformation_coeffs = pPlus_mm_Mult_qq(transformation_coeffs_dividend_multi_coeff, divisor_monom, transformation_coeffs_divisor);
	
	poly transformation_coeffs = PR->transformation_coeffs;
	int transformation_coeffs_length = pLength(transformation_coeffs);
	// insert transformation_coeffs_dividend
	if(PR->bucket->buckets[transformation_coeffs_dividend_bucket] == NULL) {
		PR->bucket->buckets[transformation_coeffs_dividend_bucket] = transformation_coeffs;
		
		PR->bucket->buckets_length[transformation_coeffs_dividend_bucket] += transformation_coeffs_length;
		PR->pLength += transformation_coeffs_length;
	}
	else {
		poly asd = PR->bucket->buckets[transformation_coeffs_dividend_bucket];
		while(pNext(asd) != NULL) {
			pIter(asd);	
		}
		
		pNext(asd) = transformation_coeffs;

		PR->bucket->buckets_length[transformation_coeffs_dividend_bucket] += transformation_coeffs_length;
		PR->pLength += transformation_coeffs_length;
	}
  
    // divisor
    if (PW->p != NULL) {
        poly asd = PW->p;
        while (pNext(asd) != NULL) {
      	    pIter(asd);
        }

        pNext(asd) = transformation_coeffs_divisor;

        PW->pLength += transformation_coeffs_divisor_length;
    }
    else {
        printf("could not find additional component in divisor\n");
        exit(1);
    }
	
  
  
  
    // dividend simplified
	//int transformation_coeffs_dividend_bucket = PR->bucket->buckets_used;
	//int transformation_coeffs_length = pLength(PR->transformation_coeffs);
	//if(PR->bucket->buckets[transformation_coeffs_dividend_bucket] == NULL) {
	//	PR->bucket->buckets[transformation_coeffs_dividend_bucket] = PR->transformation_coeffs;
	//	
	//	PR->bucket->buckets_length[transformation_coeffs_dividend_bucket] += transformation_coeffs_length;
	//	PR->pLength += transformation_coeffs_length;
	//}
	//else {
	//	poly asd = PR->bucket->buckets[transformation_coeffs_dividend_bucket];
	//	while(pNext(asd) != NULL) {
	//		pIter(asd);	
	//	}
	//	
	//	pNext(asd) = PR->transformation_coeffs;

	//	PR->bucket->buckets_length[transformation_coeffs_dividend_bucket] += transformation_coeffs_length;
	//	PR->pLength += transformation_coeffs_length;
	//}
	//PR->transformation_coeffs = NULL;
	
    // divisor simplified
	
  
	  //{
	  //	  poly asd = PW->p;
	  //	  while(pNext(asd) != NULL) {
	  //	  	pIter(asd);
	  //	  }
	  //	  pNext(asd) = PW->transformation_coeffs;
	  //	  PW->pLength += pLength(PW->transformation_coeffs);
	  //    PW->transformation_coeffs = NULL;
	  //}
		
  
						//pWrite(PR->p); // MYDEBUG
						//for(int myii = 0; myii <= PR->bucket->buckets_used; myii++) {
						//	printf("bucket %d:\n", myii);
						//	pWrite(PR->bucket->buckets[myii]);
						//}
#endif
  
  return ret;
}

int ksReducePolyGCD(LObject* PR,
                 TObject* PW,
                 poly spNoether,
                 number *coef,
                 kStrategy strat)
{
#ifdef KDEBUG
  red_count++;
#ifdef TEST_OPT_DEBUG_RED
//  if (TEST_OPT_DEBUG)
//  {
//    Print("Red %d:", red_count); PR->wrp(); Print(" with:");
//    PW->wrp();
//    //printf("\necart(PR)-ecart(PW): %i\n",PR->ecart-PW->ecart);
//    //pWrite(PR->p);
//  }
#endif
#endif
  int ret = 0;
  ring tailRing = PR->tailRing;
  kTest_L(PR, tailRing);
  kTest_T(PW);

  poly p1 = PR->GetLmTailRing();
  poly p2 = PW->GetLmTailRing();
  poly t2 = pNext(p2), lm = pOne();
  assume(p1 != NULL && p2 != NULL);// Attention, we have rings and there LC(p2) and LC(p1) are special
  p_CheckPolyRing(p1, tailRing);
  p_CheckPolyRing(p2, tailRing);

  pAssume1(p2 != NULL && p1 != NULL &&
           p_DivisibleBy(p2,  p1, tailRing));

  pAssume1(p_GetComp(p1, tailRing) == p_GetComp(p2, tailRing) ||
           (p_GetComp(p2, tailRing) == 0 &&
            p_MaxComp(pNext(p2),tailRing) == 0));

#ifdef HAVE_PLURAL
  if (rIsPluralRing(currRing))
  {
    // for the time being: we know currRing==strat->tailRing
    // no exp-bound checking needed
    // (only needed if exp-bound(tailring)<exp-b(currRing))
    if (PR->bucket!=NULL)  nc_kBucketPolyRed_Z(PR->bucket, p2,coef);
    else
    {
      poly _p = (PR->t_p != NULL ? PR->t_p : PR->p);
      assume(_p != NULL);
      nc_PolyPolyRed(_p, p2,coef, currRing);
      if (PR->t_p!=NULL) PR->t_p=_p; else PR->p=_p;
      PR->pLength=0; // usually not used, GetpLength re-computes it if needed
    }
    return 0;
  }
#endif
  // check that reduction does not violate exp bound
  while (PW->max_exp != NULL && !p_LmExpVectorAddIsOk(lm, PW->max_exp, tailRing))
  {
    // undo changes of lm
    p_ExpVectorAdd(lm, p2, tailRing);
    if (strat == NULL) return 2;
    if (! kStratChangeTailRing(strat, PR, PW)) return -1;
    tailRing = strat->tailRing;
    p1 = PR->GetLmTailRing();
    p2 = PW->GetLmTailRing();
    t2 = pNext(p2);
    lm = p1;
    p_ExpVectorSub(lm, p2, tailRing);
    ret = 1;
  }

  number ct, an, bn;
  // take care of coef buisness
  if (! n_IsOne(pGetCoeff(p2), tailRing->cf))
  {
    ct = n_ExtGcd(pGetCoeff(p1), pGetCoeff(p2), &an, &bn, tailRing->cf);    // Calculate GCD
    /* negate bn since we subtract in Tail_Minus_mm_Mult_qq */
    bn  = n_InpNeg(bn, tailRing->cf);
    p_SetCoeff(lm, bn, tailRing);
    PR->Tail_Mult_nn(an);
  }
  else
  {
    if (coef != NULL) *coef = n_Init(1, tailRing->cf);
  }


  // and finally,
  PR->Tail_Minus_mm_Mult_qq(lm, t2, pLength(t2) /*PW->GetpLength() - 1*/, spNoether);
  assume(PW->GetpLength() == pLength(PW->p != NULL ? PW->p : PW->t_p));
  pSetCoeff(PR->p, ct);

  // the following is commented out: shrinking
#ifdef HAVE_SHIFTBBA_NONEXISTENT
  if ( (currRing->isLPring) && (!strat->homog) )
  {
    // assume? h->p in currRing
    PR->GetP();
    poly qq = p_Shrink(PR->p, currRing->isLPring, currRing);
    PR->Clear(); // does the right things
    PR->p = qq;
    PR->t_p = NULL;
    PR->SetShortExpVector();
  }
#endif

  return ret;
}

/* Computes a reduction of the lead coefficient only. We have already tested
 * that lm(PW) divides lm(PR), but lc(PW) does not divide lc(PR). We have
 * computed division with remainder on the lead coefficients, parameter
 * coef is the corresponding multiple for PW we need. The new lead
 * coefficient, i.e. the remainder of lc division has already been
 * set before calling this function. We do not drop the lead term at
 * the end, but keep the adjusted, correct lead term. */
int ksReducePolyLC(LObject* PR,
                 TObject* PW,
                 poly spNoether,
                 number *coef,
                 kStrategy strat)
{
#ifdef KDEBUG
  red_count++;
#ifdef TEST_OPT_DEBUG_RED
//  if (TEST_OPT_DEBUG)
//  {
//    Print("Red %d:", red_count); PR->wrp(); Print(" with:");
//    PW->wrp();
//    //printf("\necart(PR)-ecart(PW): %i\n",PR->ecart-PW->ecart);
//    //pWrite(PR->p);
//  }
#endif
#endif
  /* printf("PR->P: ");
   * p_Write(PR->p, currRing, PR->tailRing); */
  int ret = 0;
  ring tailRing = PR->tailRing;
  kTest_L(PR,tailRing);
  kTest_T(PW);

  poly p1 = PR->GetLmTailRing();   // p2 | p1
  poly p2 = PW->GetLmTailRing();   // i.e. will reduce p1 with p2; lm = LT(p1) / LM(p2)
  poly t2 = pNext(p2), lm = p1;    // t2 = p2 - LT(p2); really compute P = LC(p2)*p1 - LT(p1)/LM(p2)*p2
  assume(p1 != NULL && p2 != NULL);// Attention, we have rings and there LC(p2) and LC(p1) are special
  p_CheckPolyRing(p1, tailRing);
  p_CheckPolyRing(p2, tailRing);

  pAssume1(p2 != NULL && p1 != NULL &&
           p_DivisibleBy(p2,  p1, tailRing));

  pAssume1(p_GetComp(p1, tailRing) == p_GetComp(p2, tailRing) ||
           (p_GetComp(p2, tailRing) == 0 &&
            p_MaxComp(pNext(p2),tailRing) == 0));

#ifdef HAVE_PLURAL
  if (rIsPluralRing(currRing))
  {
    // for the time being: we know currRing==strat->tailRing
    // no exp-bound checking needed
    // (only needed if exp-bound(tailring)<exp-b(currRing))
    if (PR->bucket!=NULL)  nc_kBucketPolyRed_Z(PR->bucket, p2,coef);
    else
    {
      poly _p = (PR->t_p != NULL ? PR->t_p : PR->p);
      assume(_p != NULL);
      nc_PolyPolyRed(_p, p2,coef, currRing);
      if (PR->t_p!=NULL) PR->t_p=_p; else PR->p=_p;
      PR->pLength=0; // usually not used, GetpLength re-computes it if needed
    }
    return 0;
  }
#endif

  p_ExpVectorSub(lm, p2, tailRing); // Calculate the Monomial we must multiply to p2
  p_SetCoeff(lm, n_Init(1, tailRing), tailRing);
  while (PW->max_exp != NULL && !p_LmExpVectorAddIsOk(lm, PW->max_exp, tailRing))
  {
    // undo changes of lm
    p_ExpVectorAdd(lm, p2, tailRing);
    if (strat == NULL) return 2;
    /* if (! kStratChangeTailRing(strat, PR, PW)) return -1; */
    tailRing = strat->tailRing;
    p1 = PR->GetLmTailRing();
    p2 = PW->GetLmTailRing();
    t2 = pNext(p2);
    lm = p1;
    p_ExpVectorSub(lm, p2, tailRing);
    ret = 1;
  }

  // and finally,
  PR->Tail_Minus_mm_Mult_qq(lm, p2, pLength(p2) /*PW->GetpLength() - 1*/, spNoether);
  assume(PW->GetpLength() == pLength(PW->p != NULL ? PW->p : PW->t_p));

  PR->LmDeleteAndIter();
  p_SetCoeff(PR->p, *coef, currRing);


  // the following is commented out: shrinking
#ifdef HAVE_SHIFTBBA_NONEXISTENT
  if ( (currRing->isLPring) && (!strat->homog) )
  {
    // assume? h->p in currRing
    PR->GetP();
    poly qq = p_Shrink(PR->p, currRing->isLPring, currRing);
    PR->Clear(); // does the right things
    PR->p = qq;
    PR->t_p = NULL;
    PR->SetShortExpVector();
  }
#endif

#if defined(KDEBUG) && defined(TEST_OPT_DEBUG_RED)
  if (TEST_OPT_DEBUG)
  {
    Print(" to: "); PR->wrp(); Print("\n");
    //printf("\nt^%i ", PR->ecart);pWrite(pHead(PR->p));
  }
#endif
  return ret;
}

int ksReducePolyBound(LObject* PR,
                 TObject* PW,
                 int bound,
                 poly spNoether,
                 number *coef,
                 kStrategy strat)
{
#ifdef KDEBUG
  red_count++;
#ifdef TEST_OPT_DEBUG_RED
  if (TEST_OPT_DEBUG)
  {
    Print("Red %d:", red_count); PR->wrp(); Print(" with:");
    PW->wrp();
    //printf("\necart(PR)-ecart(PW): %i\n",PR->ecart-PW->ecart);
    //pWrite(PR->p);
  }
#endif
#endif
  int ret = 0;
  ring tailRing = PR->tailRing;
  kTest_L(PR,tailRing);
  kTest_T(PW);

  poly p1 = PR->GetLmTailRing();   // p2 | p1
  poly p2 = PW->GetLmTailRing();   // i.e. will reduce p1 with p2; lm = LT(p1) / LM(p2)
  poly t2 = pNext(p2), lm = p1;    // t2 = p2 - LT(p2); really compute P = LC(p2)*p1 - LT(p1)/LM(p2)*p2
  assume(p1 != NULL && p2 != NULL);// Attention, we have rings and there LC(p2) and LC(p1) are special
  p_CheckPolyRing(p1, tailRing);
  p_CheckPolyRing(p2, tailRing);

  pAssume1(p2 != NULL && p1 != NULL &&
           p_DivisibleBy(p2,  p1, tailRing));

  pAssume1(p_GetComp(p1, tailRing) == p_GetComp(p2, tailRing) ||
           (p_GetComp(p2, tailRing) == 0 &&
            p_MaxComp(pNext(p2),tailRing) == 0));

#ifdef HAVE_PLURAL
  if (rIsPluralRing(currRing))
  {
    // for the time being: we know currRing==strat->tailRing
    // no exp-bound checking needed
    // (only needed if exp-bound(tailring)<exp-b(currRing))
    if (PR->bucket!=NULL)  nc_kBucketPolyRed_Z(PR->bucket, p2,coef);
    else
    {
      poly _p = (PR->t_p != NULL ? PR->t_p : PR->p);
      assume(_p != NULL);
      nc_PolyPolyRed(_p, p2,coef, currRing);
      if (PR->t_p!=NULL) PR->t_p=_p; else PR->p=_p;
      PR->pLength=0; // usually not used, GetpLength re-computes it if needed
    }
    return 0;
  }
#endif

  if (t2==NULL)           // Divisor is just one term, therefore it will
  {                       // just cancel the leading term
    PR->LmDeleteAndIter();
    if (coef != NULL) *coef = n_Init(1, tailRing);
    return 0;
  }

  p_ExpVectorSub(lm, p2, tailRing); // Calculate the Monomial we must multiply to p2

  if (tailRing != currRing)
  {
    // check that reduction does not violate exp bound
    while (PW->max_exp != NULL && !p_LmExpVectorAddIsOk(lm, PW->max_exp, tailRing))
    {
      // undo changes of lm
      p_ExpVectorAdd(lm, p2, tailRing);
      if (strat == NULL) return 2;
      if (! kStratChangeTailRing(strat, PR, PW)) return -1;
      tailRing = strat->tailRing;
      p1 = PR->GetLmTailRing();
      p2 = PW->GetLmTailRing();
      t2 = pNext(p2);
      lm = p1;
      p_ExpVectorSub(lm, p2, tailRing);
      ret = 1;
    }
  }

#ifdef HAVE_SHIFTBBA
  poly lmRight;
  if (tailRing->isLPring)
  {
    assume(PR->shift == 0);
    assume(PW->shift == si_max(p_mFirstVblock(PW->p, tailRing) - 1, 0));
    k_SplitFrame(lm, lmRight, PW->shift + 1, tailRing);
  }
#endif

  // take care of coef buisness
  if (! n_IsOne(pGetCoeff(p2), tailRing))
  {
    number bn = pGetCoeff(lm);
    number an = pGetCoeff(p2);
    int ct = ksCheckCoeff(&an, &bn, tailRing->cf);    // Calculate special LC
    p_SetCoeff(lm, bn, tailRing);
#ifdef HAVE_SHIFTBBA
    if (tailRing->isLPring) pSetCoeff0(p1, bn); // lm doesn't point to p1 anymore, if the coef was a pointer, it has been deleted
#endif
    if ((ct == 0) || (ct == 2))
      PR->Tail_Mult_nn(an);
    if (coef != NULL) *coef = an;
    else n_Delete(&an, tailRing);
  }
  else
  {
    if (coef != NULL) *coef = n_Init(1, tailRing);
  }


  // and finally,
#ifdef HAVE_SHIFTBBA
  if (tailRing->isLPring)
  {
    PR->Tail_Minus_mm_Mult_qq(lm, tailRing->p_Procs->pp_Mult_mm(t2, lmRight, tailRing), pLength(t2), spNoether);
  }
  else
#endif
  {
    PR->Tail_Minus_mm_Mult_qq(lm, t2, pLength(t2) /*PW->GetpLength() - 1*/, spNoether);
  }
  assume(PW->GetpLength() == pLength(PW->p != NULL ? PW->p : PW->t_p));
  PR->LmDeleteAndIter();

#if defined(KDEBUG) && defined(TEST_OPT_DEBUG_RED)
  if (TEST_OPT_DEBUG)
  {
    Print(" to: "); PR->wrp(); Print("\n");
    //printf("\nt^%i ", PR->ecart);pWrite(pHead(PR->p));
  }
#endif
  return ret;
}

/***************************************************************
 *
 * Reduces PR with PW
 * Assumes PR != NULL, PW != NULL, Lm(PW) divides Lm(PR)
 *
 ***************************************************************/

int ksReducePolySig(LObject* PR,
                 TObject* PW,
                 long /*idx*/,
                 poly spNoether,
                 number *coef,
                 kStrategy strat)
{
#ifdef KDEBUG
  red_count++;
#ifdef TEST_OPT_DEBUG_RED
  if (TEST_OPT_DEBUG)
  {
    Print("Red %d:", red_count); PR->wrp(); Print(" with:");
    PW->wrp();
  }
#endif
#endif
  int ret = 0;
  ring tailRing = PR->tailRing;
  kTest_L(PR,tailRing);
  kTest_T(PW);

  // signature-based stuff:
  // checking for sig-safeness first
  // NOTE: This has to be done in the current ring
  //
  /**********************************************
   *
   * TODO:
   * --------------------------------------------
   * if strat->sbaOrder == 1
   * Since we are subdividing lower index and
   * current index reductions it is enough to
   * look at the polynomial part of the signature
   * for a check. This should speed-up checking
   * a lot!
   * if !strat->sbaOrder == 0
   * We are not subdividing lower and current index
   * due to the fact that we are using the induced
   * Schreyer order
   *
   * nevertheless, this different behaviour is
   * taken care of by is_sigsafe
   * => one reduction procedure can be used for
   * both, the incremental and the non-incremental
   * attempt!
   * --------------------------------------------
   *
   *********************************************/
  //printf("COMPARE IDX: %ld -- %ld\n",idx,strat->currIdx);
  if (!PW->is_sigsafe)
  {
    poly sigMult = pCopy(PW->sig);   // copy signature of reducer
//#if 1
#ifdef DEBUGF5
    printf("IN KSREDUCEPOLYSIG: \n");
    pWrite(pHead(f1));
    pWrite(pHead(f2));
    pWrite(sigMult);
    printf("--------------\n");
#endif
    p_ExpVectorAddSub(sigMult,PR->GetLmCurrRing(),PW->GetLmCurrRing(),currRing);
//#if 1
#ifdef DEBUGF5
    printf("------------------- IN KSREDUCEPOLYSIG: --------------------\n");
    pWrite(pHead(f1));
    pWrite(pHead(f2));
    pWrite(sigMult);
    pWrite(PR->sig);
    printf("--------------\n");
#endif
    int sigSafe = p_LmCmp(PR->sig,sigMult,currRing);
    // now we can delete the copied polynomial data used for checking for
    // sig-safeness of the reduction step
//#if 1
#ifdef DEBUGF5
    printf("%d -- %d sig\n",sigSafe,PW->is_sigsafe);

#endif
    //pDelete(&f1);
    pDelete(&sigMult);
    // go on with the computations only if the signature of p2 is greater than the
    // signature of fm*p1
    if(sigSafe != 1)
    {
      PR->is_redundant = TRUE;
      return 3;
    }
    //PW->is_sigsafe  = TRUE;
  }
  PR->is_redundant = FALSE;
  poly p1 = PR->GetLmTailRing();   // p2 | p1
  poly p2 = PW->GetLmTailRing();   // i.e. will reduce p1 with p2; lm = LT(p1) / LM(p2)
  poly t2 = pNext(p2), lm = p1;    // t2 = p2 - LT(p2); really compute P = LC(p2)*p1 - LT(p1)/LM(p2)*p2
  assume(p1 != NULL && p2 != NULL);// Attention, we have rings and there LC(p2) and LC(p1) are special
  p_CheckPolyRing(p1, tailRing);
  p_CheckPolyRing(p2, tailRing);

  pAssume1(p2 != NULL && p1 != NULL &&
      p_DivisibleBy(p2,  p1, tailRing));

  pAssume1(p_GetComp(p1, tailRing) == p_GetComp(p2, tailRing) ||
      (p_GetComp(p2, tailRing) == 0 &&
       p_MaxComp(pNext(p2),tailRing) == 0));

#ifdef HAVE_PLURAL
  if (rIsPluralRing(currRing))
  {
    // for the time being: we know currRing==strat->tailRing
    // no exp-bound checking needed
    // (only needed if exp-bound(tailring)<exp-b(currRing))
    if (PR->bucket!=NULL)  nc_kBucketPolyRed_Z(PR->bucket, p2,coef);
    else
    {
      poly _p = (PR->t_p != NULL ? PR->t_p : PR->p);
      assume(_p != NULL);
      nc_PolyPolyRed(_p, p2, coef, currRing);
      if (PR->t_p!=NULL) PR->t_p=_p; else PR->p=_p;
      PR->pLength=0; // usaully not used, GetpLength re-comoutes it if needed
    }
    return 0;
  }
#endif

  if (t2==NULL)           // Divisor is just one term, therefore it will
  {                       // just cancel the leading term
    PR->LmDeleteAndIter();
    if (coef != NULL) *coef = n_Init(1, tailRing->cf);
    return 0;
  }

  p_ExpVectorSub(lm, p2, tailRing); // Calculate the Monomial we must multiply to p2

  if (tailRing != currRing)
  {
    // check that reduction does not violate exp bound
    while (PW->max_exp != NULL && !p_LmExpVectorAddIsOk(lm, PW->max_exp, tailRing))
    {
      // undo changes of lm
      p_ExpVectorAdd(lm, p2, tailRing);
      if (strat == NULL) return 2;
      if (! kStratChangeTailRing(strat, PR, PW)) return -1;
      tailRing = strat->tailRing;
      p1 = PR->GetLmTailRing();
      p2 = PW->GetLmTailRing();
      t2 = pNext(p2);
      lm = p1;
      p_ExpVectorSub(lm, p2, tailRing);
      ret = 1;
    }
  }

#ifdef HAVE_SHIFTBBA
  poly lmRight;
  if (tailRing->isLPring)
  {
    assume(PR->shift == 0);
    assume(PW->shift == si_max(p_mFirstVblock(PW->p, tailRing) - 1, 0));
    k_SplitFrame(lm, lmRight, PW->shift + 1, tailRing);
  }
#endif

  // take care of coef buisness
  if (! n_IsOne(pGetCoeff(p2), tailRing->cf))
  {
    number bn = pGetCoeff(lm);
    number an = pGetCoeff(p2);
    int ct = ksCheckCoeff(&an, &bn, tailRing->cf);    // Calculate special LC
    p_SetCoeff(lm, bn, tailRing);
#ifdef HAVE_SHIFTBBA
    if (tailRing->isLPring) pSetCoeff0(p1, bn); // lm doesn't point to p1 anymore, if the coef was a pointer, it has been deleted
#endif
    if ((ct == 0) || (ct == 2))
      PR->Tail_Mult_nn(an);
    if (coef != NULL) *coef = an;
    else n_Delete(&an, tailRing->cf);
  }
  else
  {
    if (coef != NULL) *coef = n_Init(1, tailRing->cf);
  }


  // and finally,
#ifdef HAVE_SHIFTBBA
  if (tailRing->isLPring)
  {
    PR->Tail_Minus_mm_Mult_qq(lm, tailRing->p_Procs->pp_Mult_mm(t2, lmRight, tailRing), pLength(t2), spNoether);
  }
  else
#endif
  {
    PR->Tail_Minus_mm_Mult_qq(lm, t2, PW->GetpLength() - 1, spNoether);
  }
  assume(PW->GetpLength() == pLength(PW->p != NULL ? PW->p : PW->t_p));
  PR->LmDeleteAndIter();

#if defined(KDEBUG) && defined(TEST_OPT_DEBUG_RED)
  if (TEST_OPT_DEBUG)
  {
    Print(" to: "); PR->wrp(); Print("\n");
  }
#endif
  return ret;
}

int ksReducePolySigRing(LObject* PR,
                 TObject* PW,
                 long /*idx*/,
                 poly spNoether,
                 number *coef,
                 kStrategy strat)
{
#ifdef KDEBUG
  red_count++;
#ifdef TEST_OPT_DEBUG_RED
  if (TEST_OPT_DEBUG)
  {
    Print("Red %d:", red_count); PR->wrp(); Print(" with:");
    PW->wrp();
  }
#endif
#endif
  int ret = 0;
  ring tailRing = PR->tailRing;
  kTest_L(PR,tailRing);
  kTest_T(PW);

  // signature-based stuff:
  // checking for sig-safeness first
  // NOTE: This has to be done in the current ring
  //
  /**********************************************
   *
   * TODO:
   * --------------------------------------------
   * if strat->sbaOrder == 1
   * Since we are subdividing lower index and
   * current index reductions it is enough to
   * look at the polynomial part of the signature
   * for a check. This should speed-up checking
   * a lot!
   * if !strat->sbaOrder == 0
   * We are not subdividing lower and current index
   * due to the fact that we are using the induced
   * Schreyer order
   *
   * nevertheless, this different behaviour is
   * taken care of by is_sigsafe
   * => one reduction procedure can be used for
   * both, the incremental and the non-incremental
   * attempt!
   * --------------------------------------------
   *
   *********************************************/
  //printf("COMPARE IDX: %ld -- %ld\n",idx,strat->currIdx);
  if (!PW->is_sigsafe)
  {
    poly sigMult = pCopy(PW->sig);   // copy signature of reducer
//#if 1
#ifdef DEBUGF5
    printf("IN KSREDUCEPOLYSIG: \n");
    pWrite(pHead(f1));
    pWrite(pHead(f2));
    pWrite(sigMult);
    printf("--------------\n");
#endif
    p_ExpVectorAddSub(sigMult,PR->GetLmCurrRing(),PW->GetLmCurrRing(),currRing);
    //I have also to set the leading coeficient for sigMult (in the case of rings)
    if(rField_is_Ring(currRing))
    {
      pSetCoeff(sigMult,nMult(nDiv(pGetCoeff(PR->p),pGetCoeff(PW->p)), pGetCoeff(sigMult)));
      if(nIsZero(pGetCoeff(sigMult)))
      {
        sigMult = NULL;
      }
    }
//#if 1
#ifdef DEBUGF5
    printf("------------------- IN KSREDUCEPOLYSIG: --------------------\n");
    pWrite(pHead(f1));
    pWrite(pHead(f2));
    pWrite(sigMult);
    pWrite(PR->sig);
    printf("--------------\n");
#endif
    int sigSafe;
    if(!rField_is_Ring(currRing))
      sigSafe = p_LmCmp(PR->sig,sigMult,currRing);
    // now we can delete the copied polynomial data used for checking for
    // sig-safeness of the reduction step
//#if 1
#ifdef DEBUGF5
    printf("%d -- %d sig\n",sigSafe,PW->is_sigsafe);

#endif
    if(rField_is_Ring(currRing))
    {
      // Set the sig
      poly origsig = pCopy(PR->sig);
      if(sigMult != NULL)
        PR->sig = pHead(pSub(PR->sig, sigMult));
      //The sigs have the same lm, have to substract
      //It may happen that now the signature is 0 (drop)
      if(PR->sig == NULL)
      {
        strat->sigdrop=TRUE;
      }
      else
      {
        if(pLtCmp(PR->sig,origsig) == 1)
        {
          // do not allow this reduction - it will increase it's signature
          // and the partially standard basis is just till the old sig, not the new one
          PR->is_redundant = TRUE;
          pDelete(&PR->sig);
          PR->sig = origsig;
          strat->blockred++;
          return 3;
        }
        if(pLtCmp(PR->sig,origsig) == -1)
        {
          strat->sigdrop=TRUE;
        }
      }
      pDelete(&origsig);
    }
    //pDelete(&f1);
    // go on with the computations only if the signature of p2 is greater than the
    // signature of fm*p1
    if(sigSafe != 1 && !rField_is_Ring(currRing))
    {
      PR->is_redundant = TRUE;
      return 3;
    }
    //PW->is_sigsafe  = TRUE;
  }
  PR->is_redundant = FALSE;
  poly p1 = PR->GetLmTailRing();   // p2 | p1
  poly p2 = PW->GetLmTailRing();   // i.e. will reduce p1 with p2; lm = LT(p1) / LM(p2)
  poly t2 = pNext(p2), lm = p1;    // t2 = p2 - LT(p2); really compute P = LC(p2)*p1 - LT(p1)/LM(p2)*p2
  assume(p1 != NULL && p2 != NULL);// Attention, we have rings and there LC(p2) and LC(p1) are special
  p_CheckPolyRing(p1, tailRing);
  p_CheckPolyRing(p2, tailRing);

  pAssume1(p2 != NULL && p1 != NULL &&
      p_DivisibleBy(p2,  p1, tailRing));

  pAssume1(p_GetComp(p1, tailRing) == p_GetComp(p2, tailRing) ||
      (p_GetComp(p2, tailRing) == 0 &&
       p_MaxComp(pNext(p2),tailRing) == 0));

#ifdef HAVE_PLURAL
  if (rIsPluralRing(currRing))
  {
    // for the time being: we know currRing==strat->tailRing
    // no exp-bound checking needed
    // (only needed if exp-bound(tailring)<exp-b(currRing))
    if (PR->bucket!=NULL)  nc_kBucketPolyRed_Z(PR->bucket, p2,coef);
    else
    {
      poly _p = (PR->t_p != NULL ? PR->t_p : PR->p);
      assume(_p != NULL);
      nc_PolyPolyRed(_p, p2, coef, currRing);
      if (PR->t_p!=NULL) PR->t_p=_p; else PR->p=_p;
      PR->pLength=0; // usaully not used, GetpLength re-comoutes it if needed
    }
    return 0;
  }
#endif

  if (t2==NULL)           // Divisor is just one term, therefore it will
  {                       // just cancel the leading term
    PR->LmDeleteAndIter();
    if (coef != NULL) *coef = n_Init(1, tailRing->cf);
    return 0;
  }

  p_ExpVectorSub(lm, p2, tailRing); // Calculate the Monomial we must multiply to p2

  if (tailRing != currRing)
  {
    // check that reduction does not violate exp bound
    while (PW->max_exp != NULL && !p_LmExpVectorAddIsOk(lm, PW->max_exp, tailRing))
    {
      // undo changes of lm
      p_ExpVectorAdd(lm, p2, tailRing);
      if (strat == NULL) return 2;
      if (! kStratChangeTailRing(strat, PR, PW)) return -1;
      tailRing = strat->tailRing;
      p1 = PR->GetLmTailRing();
      p2 = PW->GetLmTailRing();
      t2 = pNext(p2);
      lm = p1;
      p_ExpVectorSub(lm, p2, tailRing);
      ret = 1;
    }
  }

#ifdef HAVE_SHIFTBBA
  poly lmRight;
  if (tailRing->isLPring)
  {
    assume(PR->shift == 0);
    assume(PW->shift == si_max(p_mFirstVblock(PW->p, tailRing) - 1, 0));
    k_SplitFrame(lm, lmRight, PW->shift + 1, tailRing);
  }
#endif

  // take care of coef buisness
  if(rField_is_Ring(currRing))
  {
    p_SetCoeff(lm, nDiv(pGetCoeff(lm),pGetCoeff(p2)), tailRing);
#ifdef HAVE_SHIFTBBA
    if (tailRing->isLPring) pSetCoeff0(p1, pGetCoeff(lm)); // lm doesn't point to p1 anymore, if the coef was a pointer, it has been deleted
#endif
    if (coef != NULL) *coef = n_Init(1, tailRing->cf);
  }
  else
  {
    if (! n_IsOne(pGetCoeff(p2), tailRing->cf))
    {
      number bn = pGetCoeff(lm);
      number an = pGetCoeff(p2);
      int ct = ksCheckCoeff(&an, &bn, tailRing->cf);    // Calculate special LC
      p_SetCoeff(lm, bn, tailRing);
#ifdef HAVE_SHIFTBBA
      if (tailRing->isLPring) pSetCoeff0(p1, bn); // lm doesn't point to p1 anymore, if the coef was a pointer, it has been deleted
#endif
      if (((ct == 0) || (ct == 2)))
        PR->Tail_Mult_nn(an);
      if (coef != NULL) *coef = an;
      else n_Delete(&an, tailRing->cf);
    }
    else
    {
      if (coef != NULL) *coef = n_Init(1, tailRing->cf);
    }
  }

  // and finally,
#ifdef HAVE_SHIFTBBA
  if (tailRing->isLPring)
  {
    PR->Tail_Minus_mm_Mult_qq(lm, tailRing->p_Procs->pp_Mult_mm(t2, lmRight, tailRing), pLength(t2), spNoether);
  }
  else
#endif
  {
    PR->Tail_Minus_mm_Mult_qq(lm, t2, PW->GetpLength() - 1, spNoether);
  }
  assume(PW->GetpLength() == pLength(PW->p != NULL ? PW->p : PW->t_p));
  PR->LmDeleteAndIter();

#if defined(KDEBUG) && defined(TEST_OPT_DEBUG_RED)
  if (TEST_OPT_DEBUG)
  {
    Print(" to: "); PR->wrp(); Print("\n");
  }
#endif
  return ret;
}

/***************************************************************
 *
 * Creates S-Poly of p1 and p2
 *
 *
 ***************************************************************/
void ksCreateSpoly(LObject* Pair,   poly spNoether,
                   int use_buckets, ring tailRing,
                   poly m1, poly m2, TObject** R)
{
#ifdef KDEBUG
  create_count++;
#endif
  kTest_L(Pair,tailRing);
  poly p1 = Pair->p1;
  poly p2 = Pair->p2;
  Pair->tailRing = tailRing;

  assume(p1 != NULL);
  assume(p2 != NULL);
  assume(tailRing != NULL);

  poly a1 = pNext(p1), a2 = pNext(p2);
  number lc1 = pGetCoeff(p1), lc2 = pGetCoeff(p2);
  int co=0/*, ct = ksCheckCoeff(&lc1, &lc2, currRing->cf)*/; // gcd and zero divisors
  (void) ksCheckCoeff(&lc1, &lc2, currRing->cf);

  int l1=0, l2=0;

  if (currRing->pCompIndex >= 0)
  {
    if (__p_GetComp(p1, currRing)!=__p_GetComp(p2, currRing))
    {
      if (__p_GetComp(p1, currRing)==0)
      {
        co=1;
        p_SetCompP(p1,__p_GetComp(p2, currRing), currRing, tailRing);
      }
      else
      {
        co=2;
        p_SetCompP(p2, __p_GetComp(p1, currRing), currRing, tailRing);
      }
    }
  }

  // get m1 = LCM(LM(p1), LM(p2))/LM(p1)
  //     m2 = LCM(LM(p1), LM(p2))/LM(p2)
  if (m1 == NULL)
    k_GetLeadTerms(p1, p2, currRing, m1, m2, tailRing);

#ifdef HAVE_SHIFTBBA
  poly m12, m22;
  if (tailRing->isLPring)
  {
    assume(si_max(p_mFirstVblock(p2, tailRing) - 1, 0) == 0);
    // note: because of how the pairs are created, p2 should never be shifted
    int split = p_mFirstVblock(p1, tailRing);
    k_SplitFrame(m1, m12, split, tailRing);
    k_SplitFrame(m2, m22, split, tailRing);
    // manually free the coeffs, because pSetCoeff0 is used in the next step
    n_Delete(&(m1->coef), tailRing->cf);
    n_Delete(&(m2->coef), tailRing->cf);
  }
#endif

  pSetCoeff0(m1, lc2);
  pSetCoeff0(m2, lc1);  // and now, m1 * LT(p1) == m2 * LT(p2)

  if (R != NULL)
  {
    if (Pair->i_r1 == -1)
    {
      l1 = pLength(p1) - 1;
    }
    else
    {
      l1 = (R[Pair->i_r1])->GetpLength() - 1;
    }
    if ((Pair->i_r2 == -1)||(R[Pair->i_r2]==NULL))
    {
      l2 = pLength(p2) - 1;
    }
    else
    {
      l2 = (R[Pair->i_r2])->GetpLength() - 1;
    }
  }

  // get m2 * a2
  if (spNoether != NULL)
  {
    l2 = -1;
    a2 = tailRing->p_Procs->pp_Mult_mm_Noether(a2, m2, spNoether, l2, tailRing);
    assume(l2 == pLength(a2));
  }
  else
#ifdef HAVE_SHIFTBBA
    if (tailRing->isLPring)
    {
      // m2*a2*m22
      a2 = tailRing->p_Procs->pp_Mult_mm(tailRing->p_Procs->pp_mm_Mult(a2, m2, tailRing), m22, tailRing);
    }
    else
#endif
    {
      a2 = tailRing->p_Procs->pp_Mult_mm(a2, m2, tailRing);
    }
#ifdef HAVE_RINGS
  if (!(rField_is_Domain(currRing))) l2 = pLength(a2);
#endif

  Pair->SetLmTail(m2, a2, l2, use_buckets, tailRing);

#ifdef HAVE_SHIFTBBA
  if (tailRing->isLPring)
  {
    // get m2*a2*m22 - m1*a1*m12
    Pair->Tail_Minus_mm_Mult_qq(m1, tailRing->p_Procs->pp_Mult_mm(a1, m12, tailRing), l1, spNoether);
  }
  else
#endif
  {
    // get m2*a2 - m1*a1
    Pair->Tail_Minus_mm_Mult_qq(m1, a1, l1, spNoether);
  }

  // Clean-up time
  Pair->LmDeleteAndIter();
  p_LmDelete(m1, tailRing);
#ifdef HAVE_SHIFTBBA
  if (tailRing->isLPring)
  {
    // just to be sure, check that the shift is correct
    assume(Pair->shift == 0);
    assume(si_max(p_mFirstVblock(Pair->p, tailRing) - 1, 0) == Pair->shift); // == 0

    p_LmDelete(m12, tailRing);
    p_LmDelete(m22, tailRing);
    // m2 is already deleted
  }
#endif

  if (co != 0)
  {
    if (co==1)
    {
      p_SetCompP(p1,0, currRing, tailRing);
    }
    else
    {
      p_SetCompP(p2,0, currRing, tailRing);
    }
  }
}

int ksReducePolyTail(LObject* PR, TObject* PW, poly Current, poly spNoether)
{
  BOOLEAN ret;
  number coef;
  poly Lp =     PR->GetLmCurrRing();
  poly Save =   PW->GetLmCurrRing();

  kTest_L(PR,PR->tailRing);
  kTest_T(PW);
  pAssume(pIsMonomOf(Lp, Current));

  assume(Lp != NULL && Current != NULL && pNext(Current) != NULL);
  assume(PR->bucket == NULL);

  LObject Red(pNext(Current), PR->tailRing);
  TObject With(PW, Lp == Save);

  pAssume(!pHaveCommonMonoms(Red.p, With.p));
  ret = ksReducePoly(&Red, &With, spNoether, &coef);

  if (!ret)
  {
    if (! n_IsOne(coef, currRing->cf))
    {
      pNext(Current) = NULL;
      if (Current == PR->p && PR->t_p != NULL)
        pNext(PR->t_p) = NULL;
      PR->Mult_nn(coef);
    }

    n_Delete(&coef, currRing->cf);
    pNext(Current) = Red.GetLmTailRing();
    if (Current == PR->p && PR->t_p != NULL)
      pNext(PR->t_p) = pNext(Current);
  }

  if (Lp == Save)
    With.Delete();

  return ret;
}

int ksReducePolyTailBound(LObject* PR, TObject* PW, int bound, poly Current, poly spNoether)
{
  BOOLEAN ret;
  number coef;
  poly Lp =     PR->GetLmCurrRing();
  poly Save =   PW->GetLmCurrRing();

  kTest_L(PR,PR->tailRing);
  kTest_T(PW);
  pAssume(pIsMonomOf(Lp, Current));

  assume(Lp != NULL && Current != NULL && pNext(Current) != NULL);
  assume(PR->bucket == NULL);

  LObject Red(pNext(Current), PR->tailRing);
  TObject With(PW, Lp == Save);

  pAssume(!pHaveCommonMonoms(Red.p, With.p));
  ret = ksReducePolyBound(&Red, &With,bound, spNoether, &coef);

  if (!ret)
  {
    if (! n_IsOne(coef, currRing))
    {
      pNext(Current) = NULL;
      if (Current == PR->p && PR->t_p != NULL)
        pNext(PR->t_p) = NULL;
      PR->Mult_nn(coef);
    }

    n_Delete(&coef, currRing);
    pNext(Current) = Red.GetLmTailRing();
    if (Current == PR->p && PR->t_p != NULL)
      pNext(PR->t_p) = pNext(Current);
  }

  if (Lp == Save)
    With.Delete();

  return ret;
}

/***************************************************************
 *
 * Auxillary Routines
 *
 *
 ***************************************************************/

/*2
* creates the leading term of the S-polynomial of p1 and p2
* do not destroy p1 and p2
* remarks:
*   1. the coefficient is 0 (p_Init)
*   1. a) in the case of coefficient ring, the coefficient is calculated
*   2. pNext is undefined
*/
//static void bbb() { int i=0; }
poly ksCreateShortSpoly(poly p1, poly p2, ring tailRing)
{
  poly a1 = pNext(p1), a2 = pNext(p2);
#ifdef HAVE_SHIFTBBA
  int shift1, shift2;
  if (tailRing->isLPring) {
    // assume: LM is shifted, tail unshifted
    assume(p_FirstVblock(a1, tailRing) <= 1);
    assume(p_FirstVblock(a2, tailRing) <= 1);
    // save the shift of the LM so we can shift the other monomials on demand
    shift1 = p_mFirstVblock(p1, tailRing) - 1;
    shift2 = p_mFirstVblock(p2, tailRing) - 1;
  }
#endif
  long c1=p_GetComp(p1, currRing),c2=p_GetComp(p2, currRing);
  long c;
  poly m1,m2;
  number t1 = NULL,t2 = NULL;
  int cm,i;
  BOOLEAN equal;

#ifdef HAVE_RINGS
  BOOLEAN is_Ring=rField_is_Ring(currRing);
  number lc1 = pGetCoeff(p1), lc2 = pGetCoeff(p2);
  if (is_Ring)
  {
    ksCheckCoeff(&lc1, &lc2, currRing->cf); // gcd and zero divisors
    if (a1 != NULL) t2 = nMult(pGetCoeff(a1),lc2);
    if (a2 != NULL) t1 = nMult(pGetCoeff(a2),lc1);
    while (a1 != NULL && nIsZero(t2))
    {
      pIter(a1);
      nDelete(&t2);
      if (a1 != NULL) t2 = nMult(pGetCoeff(a1),lc2);
    }
    while (a2 != NULL && nIsZero(t1))
    {
      pIter(a2);
      nDelete(&t1);
      if (a2 != NULL) t1 = nMult(pGetCoeff(a2),lc1);
    }
  }
#endif

#ifdef HAVE_SHIFTBBA
  // shift the next monomial on demand
  if (tailRing->isLPring)
  {
    a1 = p_LPCopyAndShiftLM(a1, shift1, tailRing);
    a2 = p_LPCopyAndShiftLM(a2, shift2, tailRing);
  }
#endif
  if (a1==NULL)
  {
    if(a2!=NULL)
    {
      m2=p_Init(currRing);
x2:
      for (i = (currRing->N); i; i--)
      {
        c = p_GetExpDiff(p1, p2,i, currRing);
        if (c>0)
        {
          p_SetExp(m2,i,(c+p_GetExp(a2,i,tailRing)),currRing);
        }
        else
        {
          p_SetExp(m2,i,p_GetExp(a2,i,tailRing),currRing);
        }
      }
      if ((c1==c2)||(c2!=0))
      {
        p_SetComp(m2,p_GetComp(a2,tailRing), currRing);
      }
      else
      {
        p_SetComp(m2,c1,currRing);
      }
      p_Setm(m2, currRing);
#ifdef HAVE_RINGS
      if (is_Ring)
      {
          nDelete(&lc1);
          nDelete(&lc2);
          nDelete(&t2);
          pSetCoeff0(m2, t1);
      }
#endif
      return m2;
    }
    else
    {
#ifdef HAVE_RINGS
      if (is_Ring)
      {
        nDelete(&lc1);
        nDelete(&lc2);
        nDelete(&t1);
        nDelete(&t2);
      }
#endif
      return NULL;
    }
  }
  if (a2==NULL)
  {
    m1=p_Init(currRing);
x1:
    for (i = (currRing->N); i; i--)
    {
      c = p_GetExpDiff(p2, p1,i,currRing);
      if (c>0)
      {
        p_SetExp(m1,i,(c+p_GetExp(a1,i, tailRing)),currRing);
      }
      else
      {
        p_SetExp(m1,i,p_GetExp(a1,i, tailRing), currRing);
      }
    }
    if ((c1==c2)||(c1!=0))
    {
      p_SetComp(m1,p_GetComp(a1,tailRing),currRing);
    }
    else
    {
      p_SetComp(m1,c2,currRing);
    }
    p_Setm(m1, currRing);
#ifdef HAVE_RINGS
    if (is_Ring)
    {
      pSetCoeff0(m1, t2);
      nDelete(&lc1);
      nDelete(&lc2);
      nDelete(&t1);
    }
#endif
    return m1;
  }
  m1 = p_Init(currRing);
  m2 = p_Init(currRing);
  loop
  {
    for (i = (currRing->N); i; i--)
    {
      c = p_GetExpDiff(p1, p2,i,currRing);
      if (c > 0)
      {
        p_SetExp(m2,i,(c+p_GetExp(a2,i,tailRing)), currRing);
        p_SetExp(m1,i,p_GetExp(a1,i, tailRing), currRing);
      }
      else
      {
        p_SetExp(m1,i,(p_GetExp(a1,i,tailRing)-c), currRing);
        p_SetExp(m2,i,p_GetExp(a2,i, tailRing), currRing);
      }
    }
    if(c1==c2)
    {
      p_SetComp(m1,p_GetComp(a1, tailRing), currRing);
      p_SetComp(m2,p_GetComp(a2, tailRing), currRing);
    }
    else
    {
      if(c1!=0)
      {
        p_SetComp(m1,p_GetComp(a1, tailRing), currRing);
        p_SetComp(m2,c1, currRing);
      }
      else
      {
        p_SetComp(m2,p_GetComp(a2, tailRing), currRing);
        p_SetComp(m1,c2, currRing);
      }
    }
    p_Setm(m1,currRing);
    p_Setm(m2,currRing);
    cm = p_LmCmp(m1, m2,currRing);
    if (cm!=0)
    {
      if(cm==1)
      {
        p_LmFree(m2,currRing);
#ifdef HAVE_RINGS
        if (is_Ring)
        {
          pSetCoeff0(m1, t2);
          nDelete(&lc1);
          nDelete(&lc2);
          nDelete(&t1);
        }
#endif
        return m1;
      }
      else
      {
        p_LmFree(m1,currRing);
#ifdef HAVE_RINGS
        if (is_Ring)
        {
          pSetCoeff0(m2, t1);
          nDelete(&lc1);
          nDelete(&lc2);
          nDelete(&t2);
        }
#endif
        return m2;
      }
    }
#ifdef HAVE_RINGS
    if (is_Ring)
    {
      equal = nEqual(t1,t2);
    }
    else
#endif
    {
      t1 = nMult(pGetCoeff(a2),pGetCoeff(p1));
      t2 = nMult(pGetCoeff(a1),pGetCoeff(p2));
      equal = nEqual(t1,t2);
      nDelete(&t2);
      nDelete(&t1);
    }
    if (!equal)
    {
      p_LmFree(m2,currRing);
#ifdef HAVE_RINGS
      if (is_Ring)
      {
          pSetCoeff0(m1, nSub(t1, t2));
          nDelete(&lc1);
          nDelete(&lc2);
          nDelete(&t1);
          nDelete(&t2);
      }
#endif
      return m1;
    }
    pIter(a1);
    pIter(a2);
#ifdef HAVE_RINGS
    if (is_Ring)
    {
      if (a2 != NULL)
      {
        nDelete(&t1);
        t1 = nMult(pGetCoeff(a2),lc1);
      }
      if (a1 != NULL)
      {
        nDelete(&t2);
        t2 = nMult(pGetCoeff(a1),lc2);
      }
      while ((a1 != NULL) && nIsZero(t2))
      {
        pIter(a1);
        if (a1 != NULL)
        {
          nDelete(&t2);
          t2 = nMult(pGetCoeff(a1),lc2);
        }
      }
      while ((a2 != NULL) && nIsZero(t1))
      {
        pIter(a2);
        if (a2 != NULL)
        {
          nDelete(&t1);
          t1 = nMult(pGetCoeff(a2),lc1);
        }
      }
    }
#endif
#ifdef HAVE_SHIFTBBA
    if (tailRing->isLPring)
    {
      a1 = p_LPCopyAndShiftLM(a1, shift1, tailRing);
      a2 = p_LPCopyAndShiftLM(a2, shift2, tailRing);
    }
#endif
    if (a2==NULL)
    {
      p_LmFree(m2,currRing);
      if (a1==NULL)
      {
#ifdef HAVE_RINGS
        if (is_Ring)
        {
          nDelete(&lc1);
          nDelete(&lc2);
          nDelete(&t1);
          nDelete(&t2);
        }
#endif
        p_LmFree(m1,currRing);
        return NULL;
      }
      goto x1;
    }
    if (a1==NULL)
    {
      p_LmFree(m1,currRing);
      goto x2;
    }
  }
}
