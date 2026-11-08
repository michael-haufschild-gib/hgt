import GaloisForLFunctions.ArithmeticEffectivityTheory.TheIntersectionOfTorsionOrbits
import GaloisForLFunctions.HTGeometry.IsogenyLattice
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Counts and heights of thickened arithmetic intersections

The residue ring `ℤ[X]/(P,Q)` is defined before its cardinality or height.
For monic `P`, bounded polynomial relations identify its additive group with
an integral Sylvester cokernel. A nonzero resultant gives finiteness and the
exact cardinality. Thickening both monic equations multiplies prime-local
order multiplicities and logarithmic height by the product of their
multiplicities. The prime factorization formula and the complex resultant
identify the finite-place and infinite-place values. Distinct cyclotomic
thickenings recover the torsion-orbit intersection with geometric multiplicity.
-/

noncomputable section
open Polynomial Finset
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

/-- The actual scheme-theoretic intersection ring of two integral polynomial divisors. -/
abbrev ArithmeticIntersectionRing (P Q : ℤ[X]) :=
  ℤ[X] ⧸ Ideal.span ({P,Q} : Set ℤ[X])

/-- Number of elements of the intersection ring; zero when it is infinite. -/
def arithmeticIntersectionCount (P Q : ℤ[X]) : ℕ :=
  Nat.card (ArithmeticIntersectionRing P Q)

/-- The finite coefficient lattice used for the integral relation presentation. -/
abbrev IntersectionLattice (P Q : ℤ[X]) := Polynomial.degreeLT ℤ (P.natDegree+Q.natDegree)

/-- Integral polynomial relations in coefficient coordinates. -/
def intersectionRelationMap (P Q : ℤ[X]) :
    IntersectionLattice P Q →ₗ[ℤ] IntersectionLattice P Q :=
  (Polynomial.sylvesterMap P Q le_rfl le_rfl).comp
    (Polynomial.degreeLT.addLinearEquiv ℤ P.natDegree Q.natDegree).toLinearMap

/-- Relation classes, defined independently of their determinant. -/
abbrev IntersectionRelationQuotient (P Q : ℤ[X]) :=
  IntersectionLattice P Q ⧸ LinearMap.range (intersectionRelationMap P Q)

/-- The coefficient presentation has exactly the classical resultant determinant. -/
theorem intersectionRelationMap_det (P Q : ℤ[X]) :
    LinearMap.det (intersectionRelationMap P Q) = P.resultant Q := by
  rw [← LinearMap.det_toMatrix (degreeLT.basis ℤ (P.natDegree+Q.natDegree))]
  have hm : LinearMap.toMatrix (degreeLT.basis ℤ (P.natDegree+Q.natDegree))
      (degreeLT.basis ℤ (P.natDegree+Q.natDegree)) (intersectionRelationMap P Q) =
      P.sylvester Q P.natDegree Q.natDegree := by
    rw [← toMatrix_sylvesterMap' P Q le_rfl le_rfl]
    ext i j
    simp only [LinearMap.toMatrix_apply, intersectionRelationMap, LinearMap.comp_apply,
      LinearEquiv.coe_coe, degreeLT.addLinearEquiv, Module.Basis.equiv_apply, Equiv.refl_apply]
    rfl
  rw [hm]
  rfl

/-- The coefficient relations count a finite integral cokernel at every proper intersection. -/
theorem card_intersectionRelationQuotient {P Q : ℤ[X]} (h : P.resultant Q ≠ 0) :
    Nat.card (IntersectionRelationQuotient P Q) = (P.resultant Q).natAbs := by
  rw [LinearMap.card_quotient_range_eq_natAbs_det
    (LinearMap.injective_of_det_ne_zero (by simpa only [intersectionRelationMap_det] using h)),
    intersectionRelationMap_det]

/-- Send a bounded polynomial to its class in the actual intersection ring. -/
def intersectionProjection (P Q : ℤ[X]) :
    IntersectionLattice P Q →ₗ[ℤ] ArithmeticIntersectionRing P Q :=
  (Ideal.Quotient.mkₐ ℤ (Ideal.span ({P,Q} : Set ℤ[X]))).toLinearMap.comp
    (Polynomial.degreeLT ℤ (P.natDegree+Q.natDegree)).subtype

@[simp] theorem intersectionProjection_apply (P Q : ℤ[X]) (r : IntersectionLattice P Q) :
    intersectionProjection P Q r = Ideal.Quotient.mk _ (r : ℤ[X]) := rfl

/-- Monic division supplies bounded representatives of every intersection class. -/
theorem intersectionProjection_surjective {P Q : ℤ[X]} (hP : P.Monic) :
    Function.Surjective (intersectionProjection P Q) := by
  intro z
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective z
  have hr : r %ₘ P ∈ Polynomial.degreeLT ℤ (P.natDegree+Q.natDegree) := by
    apply mem_degreeLT.mpr
    exact (degree_modByMonic_lt r hP).trans_le
      (degree_le_natDegree.trans (by exact_mod_cast Nat.le_add_right P.natDegree Q.natDegree))
  refine ⟨⟨r %ₘ P,hr⟩,?_⟩
  change Ideal.Quotient.mk (Ideal.span ({P,Q} : Set ℤ[X])) (r %ₘ P) =
    Ideal.Quotient.mk (Ideal.span ({P,Q} : Set ℤ[X])) r
  rw [modByMonic_eq_sub_mul_div,map_sub,map_mul]
  have hz : Ideal.Quotient.mk (Ideal.span ({P,Q} : Set ℤ[X])) P = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  rw [hz,zero_mul,sub_zero]

/-- Bounded relations are exactly the kernel of passage to the intersection ring. -/
theorem intersectionProjection_ker {P Q : ℤ[X]} (hP : P.Monic) :
    LinearMap.ker (intersectionProjection P Q) = LinearMap.range (intersectionRelationMap P Q) := by
  ext r
  rw [LinearMap.mem_ker,intersectionProjection_apply,Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro hr
    obtain ⟨a,b,hab⟩ := Ideal.mem_span_pair.mp hr
    let u := b %ₘ P
    let v := a + Q * (b /ₘ P)
    have hu : u ∈ Polynomial.degreeLT ℤ P.natDegree :=
      mem_degreeLT.mpr ((degree_modByMonic_lt b hP).trans_le degree_le_natDegree)
    have hid : P*v + Q*u = (r : ℤ[X]) := by
      dsimp [u,v]
      calc
        P * (a+Q*(b /ₘ P)) + Q*(b %ₘ P) = a*P + Q*(b %ₘ P+P*(b /ₘ P)) := by ring
        _ = a*P+b*Q := by rw [modByMonic_add_div]; ring
        _ = r := hab
    have hqu : Q*u ∈ Polynomial.degreeLT ℤ (P.natDegree+Q.natDegree) := by
      have hs := (sylvesterMap P Q le_rfl le_rfl (⟨u,hu⟩,0)).property
      simpa only [sylvesterMap_apply_coe,ZeroMemClass.coe_zero,mul_zero,zero_add] using hs
    have hpv : P*v ∈ Polynomial.degreeLT ℤ (P.natDegree+Q.natDegree) := by
      have hh := (Polynomial.degreeLT ℤ (P.natDegree+Q.natDegree)).sub_mem r.property hqu
      have he : (r : ℤ[X])-Q*u = P*v := by rw [←hid]; ring
      rwa [he] at hh
    have hv : v ∈ Polynomial.degreeLT ℤ Q.natDegree := by
      by_cases hv0 : v=0
      · rw [hv0]; exact Submodule.zero_mem _
      have hdeg := (natDegree_lt_iff_degree_lt (mul_ne_zero hP.ne_zero hv0)).mpr
        (mem_degreeLT.mp hpv)
      rw [natDegree_mul hP.ne_zero hv0] at hdeg
      exact mem_degreeLT.mpr ((natDegree_lt_iff_degree_lt hv0).mp (by omega))
    refine ⟨(degreeLT.addLinearEquiv ℤ P.natDegree Q.natDegree).symm (⟨u,hu⟩,⟨v,hv⟩),?_⟩
    apply Subtype.ext
    simpa only [intersectionRelationMap,LinearMap.comp_apply,LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply,sylvesterMap_apply_coe] using hid
  · rintro ⟨v,rfl⟩
    change P * _ + Q * _ ∈ Ideal.span ({P,Q} : Set ℤ[X])
    apply Ideal.mem_span_pair.mpr
    exact ⟨((degreeLT.addLinearEquiv ℤ P.natDegree Q.natDegree) v).2,
      ((degreeLT.addLinearEquiv ℤ P.natDegree Q.natDegree) v).1,by
        simp only [LinearEquiv.coe_coe,mul_comm]⟩

/-- The bounded integral relation quotient is the actual arithmetic intersection ring. -/
def intersectionRelationQuotientEquiv {P Q : ℤ[X]} (hP : P.Monic) :
    IntersectionRelationQuotient P Q ≃ₗ[ℤ] ArithmeticIntersectionRing P Q := by
  change (IntersectionLattice P Q ⧸ LinearMap.range (intersectionRelationMap P Q)) ≃ₗ[ℤ] _
  rw [←intersectionProjection_ker hP]
  exact (intersectionProjection P Q).quotKerEquivOfSurjective (intersectionProjection_surjective hP)

/-- Count the actual finite intersection ring by its integral presentation. -/
theorem arithmeticIntersectionCount_eq_resultant {P Q : ℤ[X]} (hP : P.Monic)
    (h : P.resultant Q ≠ 0) : arithmeticIntersectionCount P Q = (P.resultant Q).natAbs := by
  rw [arithmeticIntersectionCount,←Nat.card_congr (intersectionRelationQuotientEquiv hP).toEquiv]
  exact card_intersectionRelationQuotient h

#print axioms intersectionRelationQuotientEquiv
#print axioms arithmeticIntersectionCount_eq_resultant

/-- Proper intersections have finite residue rings, including the zero ring at unit resultant. -/
theorem arithmeticIntersectionRing_finite {P Q : ℤ[X]} (hP : P.Monic)
    (h : P.resultant Q ≠ 0) : Finite (ArithmeticIntersectionRing P Q) := by
  apply Nat.finite_of_card_ne_zero
  change arithmeticIntersectionCount P Q ≠ 0
  rw [arithmeticIntersectionCount_eq_resultant hP h]
  exact Int.natAbs_ne_zero.mpr h

/-- Thickening both equations multiplies the resultant exponent. -/
theorem resultant_thickening {P Q : ℤ[X]} (hP : P.Monic) (hQ : Q.Monic) (a b : ℕ) :
    (P^a).resultant (Q^b) = (P.resultant Q)^(a*b) := by
  rw [resultant_pow_left P (Q^b) a (Q^b).natDegree
    (by simp only [hP.leadingCoeff,one_pow,ne_eq,one_ne_zero,not_false_eq_true]) le_rfl,
    resultant_pow_right P Q P.natDegree b le_rfl
    (by simp only [hQ.leadingCoeff,one_pow,ne_eq,one_ne_zero,not_false_eq_true]),
    ←pow_mul,mul_comm b a]

/-- Two-divisor thickening counts actual residue classes; it is not a power by definition. -/
theorem arithmeticIntersectionCount_thickening {P Q : ℤ[X]} (hP : P.Monic) (hQ : Q.Monic)
    (h : P.resultant Q ≠ 0) (a b : ℕ) :
    arithmeticIntersectionCount (P^a) (Q^b) = arithmeticIntersectionCount P Q^(a*b) := by
  have hpow : (P^a).resultant (Q^b) ≠ 0 := by
    rw [resultant_thickening hP hQ]
    exact pow_ne_zero _ h
  rw [arithmeticIntersectionCount_eq_resultant (hP.pow a) hpow,
    resultant_thickening hP hQ,Int.natAbs_pow,arithmeticIntersectionCount_eq_resultant hP h]

/-- Arithmetic intersection height is the logarithm of the actual residue-ring count. -/
def arithmeticIntersectionHeight (P Q : ℤ[X]) : ℝ :=
  Real.log (arithmeticIntersectionCount P Q)

/-- Nonnegative height follows from nonemptiness and finiteness of the actual ring. -/
theorem arithmeticIntersectionHeight_nonneg {P Q : ℤ[X]} (hP : P.Monic)
    (h : P.resultant Q ≠ 0) : 0 ≤ arithmeticIntersectionHeight P Q := by
  have hc : arithmeticIntersectionCount P Q ≠ 0 := by
    rw [arithmeticIntersectionCount_eq_resultant hP h]
    exact Int.natAbs_ne_zero.mpr h
  exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hc)

/-- The infinite-place value is the ordinary absolute value of the integral resultant. -/
theorem arithmeticIntersectionHeight_archimedean {P Q : ℤ[X]} (hP : P.Monic)
    (h : P.resultant Q ≠ 0) :
    arithmeticIntersectionHeight P Q = Real.log |(P.resultant Q : ℝ)| := by
  simp only [arithmeticIntersectionHeight,arithmeticIntersectionCount_eq_resultant hP h,
    Nat.cast_natAbs,Int.cast_abs]

/-- The logarithmic count scales bilinearly in the two geometric multiplicities. -/
theorem arithmeticIntersectionHeight_thickening {P Q : ℤ[X]} (hP : P.Monic) (hQ : Q.Monic)
    (h : P.resultant Q ≠ 0) (a b : ℕ) :
    arithmeticIntersectionHeight (P^a) (Q^b) = (a:ℝ)*b*arithmeticIntersectionHeight P Q := by
  unfold arithmeticIntersectionHeight
  rw [arithmeticIntersectionCount_thickening hP hQ h,Nat.cast_pow,Real.log_pow,Nat.cast_mul]

/-- Equal thickening has an exact quadratic logarithmic count. -/
theorem arithmeticIntersectionHeight_quadratic {P Q : ℤ[X]} (hP : P.Monic) (hQ : Q.Monic)
    (h : P.resultant Q ≠ 0) (k : ℕ) :
    arithmeticIntersectionHeight (P^k) (Q^k) = (k:ℝ)^2*arithmeticIntersectionHeight P Q := by
  rw [arithmeticIntersectionHeight_thickening hP hQ h]
  ring

#print axioms arithmeticIntersectionRing_finite
#print axioms arithmeticIntersectionCount_thickening
#print axioms arithmeticIntersectionHeight_archimedean
#print axioms arithmeticIntersectionHeight_nonneg
#print axioms arithmeticIntersectionHeight_quadratic

/-- Distinct cyclotomic divisors have no common generic component over the integers. -/
theorem cyclotomic_resultant_ne_zero {n m : ℕ} (hnm : n ≠ m) :
    (cyclotomic n ℤ).resultant (cyclotomic m ℤ) ≠ 0 := by
  have hr := resultant_ne_zero (cyclotomic n ℚ) (cyclotomic m ℚ)
    (cyclotomic.isCoprime_rat hnm)
  intro hz
  apply hr
  have he := resultant_map_map (cyclotomic n ℤ) (cyclotomic m ℤ)
    (cyclotomic n ℤ).natDegree (cyclotomic m ℤ).natDegree (Int.castRingHom ℚ)
  rw [map_cyclotomic_int,map_cyclotomic_int,hz,map_zero] at he
  simpa only [natDegree_cyclotomic] using he

/-- All distinct cyclotomic thickenings are actual finite arithmetic intersections. -/
theorem cyclotomic_thickened_intersection_finite {n m : ℕ} (hnm : n ≠ m) (a b : ℕ) :
    Finite (ArithmeticIntersectionRing ((cyclotomic n ℤ)^a) ((cyclotomic m ℤ)^b)) := by
  apply arithmeticIntersectionRing_finite ((cyclotomic.monic n ℤ).pow a)
  rw [resultant_thickening (cyclotomic.monic n ℤ) (cyclotomic.monic m ℤ)]
  exact pow_ne_zero _ (cyclotomic_resultant_ne_zero hnm)

/-- Cyclotomic thickening raises the actual count to the product of the multiplicities. -/
theorem cyclotomic_intersection_count_thickening {n m : ℕ} (hnm : n ≠ m) (a b : ℕ) :
    arithmeticIntersectionCount ((cyclotomic n ℤ)^a) ((cyclotomic m ℤ)^b) =
      arithmeticIntersectionCount (cyclotomic n ℤ) (cyclotomic m ℤ)^(a*b) :=
  arithmeticIntersectionCount_thickening (cyclotomic.monic n ℤ) (cyclotomic.monic m ℤ)
    (cyclotomic_resultant_ne_zero hnm) a b

/-- Prime-local order multiplicity of the actual finite intersection ring. -/
def arithmeticIntersectionOrder (p : ℕ) (P Q : ℤ[X]) : ℕ :=
  (arithmeticIntersectionCount P Q).factorization p

/-- Each prime-local integer multiplicity scales bilinearly under geometric thickening. -/
theorem arithmeticIntersectionOrder_thickening {P Q : ℤ[X]} (hP : P.Monic) (hQ : Q.Monic)
    (h : P.resultant Q ≠ 0) (p a b : ℕ) :
    arithmeticIntersectionOrder p (P^a) (Q^b) = a*b*arithmeticIntersectionOrder p P Q := by
  simp only [arithmeticIntersectionOrder,arithmeticIntersectionCount_thickening hP hQ h,
    Nat.factorization_pow,Finsupp.smul_apply,smul_eq_mul]

/-- Equal thickening gives an integer-valued quadratic multiplicity at each prime. -/
theorem arithmeticIntersectionOrder_quadratic {P Q : ℤ[X]} (hP : P.Monic) (hQ : Q.Monic)
    (h : P.resultant Q ≠ 0) (p k : ℕ) :
    arithmeticIntersectionOrder p (P^k) (Q^k) = k^2*arithmeticIntersectionOrder p P Q := by
  rw [arithmeticIntersectionOrder_thickening hP hQ h]
  ring

#print axioms arithmeticIntersectionOrder_thickening
#print axioms arithmeticIntersectionOrder_quadratic

/-- The nonnegative logarithmic count decomposes into prime-local order multiplicities. -/
theorem arithmeticIntersectionHeight_prime_sum {P Q : ℤ[X]} (hP : P.Monic)
    (h : P.resultant Q ≠ 0) :
    0 < arithmeticIntersectionCount P Q ∧
    arithmeticIntersectionHeight P Q =
      (arithmeticIntersectionCount P Q).factorization.sum
        (fun p k => (k:ℝ)*Real.log p) := by
  refine ⟨?_,Real.log_nat_eq_sum_factorization _⟩
  rw [arithmeticIntersectionCount_eq_resultant hP h]
  exact Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr h)

#print axioms cyclotomic_thickened_intersection_finite
#print axioms cyclotomic_intersection_count_thickening
#print axioms arithmeticIntersectionHeight_prime_sum

/-- The complex resultant is the product of the differences between primitive torsion points. -/
theorem cyclotomic_resultant_complex_product {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    (((cyclotomic n ℤ).resultant (cyclotomic m ℤ) : ℤ) : ℂ) =
      ∏η∈primitiveRoots n ℂ,∏ξ∈primitiveRoots m ℂ,(η-ξ) := by
  letI : NeZero (n:ℂ) := ⟨by exact_mod_cast hn.ne'⟩
  have he := resultant_map_map (cyclotomic n ℤ) (cyclotomic m ℤ)
    (cyclotomic n ℤ).natDegree (cyclotomic m ℤ).natDegree (Int.castRingHom ℂ)
  rw [map_cyclotomic_int,map_cyclotomic_int] at he
  have hc : (((cyclotomic n ℤ).resultant (cyclotomic m ℤ) : ℤ) : ℂ) =
      (cyclotomic n ℂ).resultant (cyclotomic m ℂ) := by
    simpa only [natDegree_cyclotomic,Int.coe_castRingHom] using he.symm
  rw [hc,resultant_eq_prod_eval _ _ _ le_rfl (IsAlgClosed.splits _),
    (cyclotomic.monic n ℂ).leadingCoeff,one_pow,one_mul,
    cyclotomic.roots_eq_primitiveRoots_val]
  change (∏η∈primitiveRoots n ℂ,eval η (cyclotomic m ℂ)) = _
  apply prod_congr rfl
  intro η _
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots (Complex.isPrimitiveRoot_exp m hm.ne'),eval_prod]
  simp only [eval_sub,eval_X,eval_C]

/-- The independent finite-ring height recovers the torsion-orbit intersection. -/
theorem cyclotomic_intersectionHeight_eq_orbit {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hnm : n ≠ m) :
    arithmeticIntersectionHeight (cyclotomic n ℤ) (cyclotomic m ℤ) =
      ArithmeticEffectivityTheory.orbitIntersection n m := by
  rw [arithmeticIntersectionHeight_archimedean (cyclotomic.monic n ℤ)
    (cyclotomic_resultant_ne_zero hnm)]
  have hnorm : |(((cyclotomic n ℤ).resultant (cyclotomic m ℤ) : ℤ) : ℝ)| =
      ‖(((cyclotomic n ℤ).resultant (cyclotomic m ℤ) : ℤ) : ℂ)‖ := by
    rw [←Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs]
  rw [hnorm,cyclotomic_resultant_complex_product hn hm,norm_prod]
  simp_rw [norm_prod]
  have hne : ∀η∈primitiveRoots n ℂ,∀ξ∈primitiveRoots m ℂ,‖η-ξ‖≠0 := by
    intro η hη ξ hξ hzero
    have he : η=ξ := sub_eq_zero.mp (norm_eq_zero.mp hzero)
    subst ξ
    exact hnm (((mem_primitiveRoots hn).mp hη).unique ((mem_primitiveRoots hm).mp hξ))
  rw [Real.log_prod (fun η hη => Finset.prod_ne_zero_iff.mpr (hne η hη)),
    ArithmeticEffectivityTheory.orbitIntersection]
  apply sum_congr rfl
  intro η hη
  exact Real.log_prod (hne η hη)

/-- Thickened cyclotomic residue counts recover the same torsion height with geometric multiplicity. -/
theorem cyclotomic_intersectionHeight_thickening {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hnm : n ≠ m) (a b : ℕ) :
    arithmeticIntersectionHeight ((cyclotomic n ℤ)^a) ((cyclotomic m ℤ)^b) =
      (a:ℝ)*b*ArithmeticEffectivityTheory.orbitIntersection n m := by
  rw [arithmeticIntersectionHeight_thickening (cyclotomic.monic n ℤ) (cyclotomic.monic m ℤ)
    (cyclotomic_resultant_ne_zero hnm),cyclotomic_intersectionHeight_eq_orbit hn hm hnm]

#print axioms cyclotomic_intersectionHeight_eq_orbit
#print axioms cyclotomic_intersectionHeight_thickening

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
