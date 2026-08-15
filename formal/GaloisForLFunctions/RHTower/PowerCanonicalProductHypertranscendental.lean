import GaloisForLFunctions.RHTower.BarnesRemainderMeroTransfer
import GaloisForLFunctions.RHTower.PowerCanonicalProductHypertranscendence
import GaloisForLFunctions.HTGeometry.MvPolynomialLinearSubstitution

/-!
# Irrational-power canonical products are hypertranscendental

Assembling the chain.  A differentially algebraic `W_s` gives a differentially algebraic Barnes
remainder in the meromorphic field of the right half-plane, hence a pointwise relation among `z` and
the ordinary jets of the remainder.  Reversing the `z`-degrees turns `z = 1/t` into a polynomial
coefficient, and the unitriangular passage from ordinary to Euler jets turns the jets into the
functions whose Poincaré expansions are the Euler jets of the formal Barnes tail.  The two-sided
profile of that tail forbids the relation.
-/

open Complex Filter Set
open scoped Differential
open GaloisForLFunctions GaloisForLFunctions.HTGeometry Bottcher

namespace RHTower

noncomputable section

variable {s : ℝ}

local instance rhpDomain' : IsDomain (analyticSubring HTGeometry.rightHalfPlane) :=
  Bottcher.isDomain_analyticSubring _ HTGeometry.isOpen_rightHalfPlane
    HTGeometry.isPreconnected_rightHalfPlane HTGeometry.rightHalfPlane_nonempty

local instance rhpAlgebra' : Algebra (RatFunc ℂ) (meroField HTGeometry.rightHalfPlane) :=
  (ratfuncToMero _ HTGeometry.isOpen_rightHalfPlane HTGeometry.isPreconnected_rightHalfPlane
    HTGeometry.rightHalfPlane_nonempty HTGeometry.rightHalfPlane_infinite).toAlgebra

local instance rhpDifferential' : Differential (meroField HTGeometry.rightHalfPlane) :=
  meroFieldDifferential HTGeometry.isOpen_rightHalfPlane
    HTGeometry.isPreconnected_rightHalfPlane HTGeometry.rightHalfPlane_nonempty

local instance rhpCharZero' : CharZero (meroField HTGeometry.rightHalfPlane) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField HTGeometry.rightHalfPlane)).injective

local instance rhpRatFuncDifferential' : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance rhpDifferentialAlgebra' :
    DifferentialAlgebra (RatFunc ℂ) (meroField HTGeometry.rightHalfPlane) :=
  meroFieldRatFuncDifferentialAlgebra HTGeometry.isOpen_rightHalfPlane
    HTGeometry.isPreconnected_rightHalfPlane HTGeometry.rightHalfPlane_nonempty
    HTGeometry.rightHalfPlane_infinite

/-! ### The jet-change substitution -/

/-- The matrix writing the weighted ordinary jets through the Euler jets in the reciprocal
variable. -/
def jetChangeMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial ℂ) :=
  fun j k =>
    Polynomial.C (((eulerJetCoeff (j : ℕ) (k : ℕ) : ℤ) : ℂ) * (-1 : ℂ) ^ (k : ℕ))
      * Polynomial.X ^ (j : ℕ)

theorem jetChangeMatrix_lowerTriangular (n : ℕ) :
    ∀ j k : Fin (n + 1), j < k → jetChangeMatrix n j k = 0 := by
  intro j k hjk
  rw [jetChangeMatrix, eulerJetCoeff_eq_zero_of_lt hjk]
  simp

theorem isUnit_det_jetChangeMatrix_map (n : ℕ) :
    IsUnit (((jetChangeMatrix n).map
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) : Polynomial ℂ →+* RatFunc ℂ)).det) := by
  refine isUnit_det_of_lowerTriangular_units ?_ ?_
  · intro j k hjk
    rw [Matrix.map_apply, jetChangeMatrix_lowerTriangular n j k hjk, map_zero]
  · intro j
    rw [Matrix.map_apply, jetChangeMatrix, eulerJetCoeff_self]
    refine isUnit_iff_ne_zero.mpr ?_
    have hX : (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (Polynomial.X ^ (j : ℕ)) ≠ 0 := by
      refine (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℂ)).mpr ?_
      exact pow_ne_zero _ Polynomial.X_ne_zero
    have hC : (algebraMap (Polynomial ℂ) (RatFunc ℂ))
        (Polynomial.C (((1 : ℤ) : ℂ) * (-1 : ℂ) ^ (j : ℕ))) ≠ 0 := by
      refine (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℂ)).mpr ?_
      refine Polynomial.C_ne_zero.mpr ?_
      simp
    rw [map_mul]
    exact mul_ne_zero hC hX

theorem matrixSubst_jetChangeMatrix_injective (n : ℕ) :
    Function.Injective (matrixSubst (jetChangeMatrix n)) :=
  matrixSubst_injective_of_map _ (RatFunc.algebraMap_injective ℂ)
    (isUnit_det_jetChangeMatrix_map n)

/-! ### The reversal -/

/-- The relation with the `z`-degrees reversed, so that `z = 1/t` becomes a polynomial coefficient
in `t`. -/
def reversedRelation {n : ℕ} (P : MvPolynomial (Fin (n + 2)) ℂ) :
    MvPolynomial (Fin (n + 1)) (Polynomial ℂ) :=
  ∑ b ∈ Finset.range (((MvPolynomial.finSuccEquiv ℂ (n + 1)) P).reverse.natDegree + 1),
    MvPolynomial.C (Polynomial.monomial b (1 : ℂ)) *
      MvPolynomial.map (Polynomial.C : ℂ →+* Polynomial ℂ)
        (((MvPolynomial.finSuccEquiv ℂ (n + 1)) P).reverse.coeff b)

theorem coeff_reversedRelation {n : ℕ} (P : MvPolynomial (Fin (n + 2)) ℂ)
    (β : Fin (n + 1) →₀ ℕ) (b₀ : ℕ)
    (hb₀ : b₀ ≤ ((MvPolynomial.finSuccEquiv ℂ (n + 1)) P).reverse.natDegree) :
    (MvPolynomial.coeff β (reversedRelation P)).coeff b₀
      = MvPolynomial.coeff β (((MvPolynomial.finSuccEquiv ℂ (n + 1)) P).reverse.coeff b₀) := by
  classical
  have hmm : ∀ (b : ℕ) (c : ℂ), (Polynomial.monomial b (1 : ℂ)) * Polynomial.C c
      = Polynomial.monomial b c := by
    intro b c
    rw [mul_comm, Polynomial.C_mul_monomial, mul_one]
  rw [reversedRelation, MvPolynomial.coeff_sum, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single b₀]
  · rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, hmm, Polynomial.coeff_monomial,
      if_pos rfl]
  · intro b _ hb
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, hmm, Polynomial.coeff_monomial,
      if_neg hb]
  · intro hmem
    exact absurd (Finset.mem_range.mpr (by omega)) hmem

theorem reversedRelation_ne_zero {n : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ} (hP : P ≠ 0) :
    reversedRelation P ≠ 0 := by
  classical
  have hp0 : ((MvPolynomial.finSuccEquiv ℂ (n + 1)) P) ≠ 0 := by
    intro h
    exact hP ((MvPolynomial.finSuccEquiv ℂ (n + 1)).injective (by rw [h, map_zero]))
  have hq0 : ((MvPolynomial.finSuccEquiv ℂ (n + 1)) P).reverse ≠ 0 :=
    (Polynomial.reverse_eq_zero).not.mpr hp0
  obtain ⟨b₀, hb₀⟩ : ∃ b₀, ((MvPolynomial.finSuccEquiv ℂ (n + 1)) P).reverse.coeff b₀ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hq0 (Polynomial.ext hc)
  have hble : b₀ ≤ ((MvPolynomial.finSuccEquiv ℂ (n + 1)) P).reverse.natDegree :=
    Polynomial.le_natDegree_of_ne_zero hb₀
  obtain ⟨β, hβ⟩ : ∃ β,
      MvPolynomial.coeff β (((MvPolynomial.finSuccEquiv ℂ (n + 1)) P).reverse.coeff b₀) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hb₀ (MvPolynomial.ext _ _ (by simpa using hc))
  intro hzero
  apply hβ
  have h := coeff_reversedRelation P β b₀ hble
  rw [hzero] at h
  simpa using h.symm

/-! ### The evaluation identity -/

theorem eval₂_reversedRelation {n : ℕ} (P : MvPolynomial (Fin (n + 2)) ℂ) (c : ℂ)
    (Y : Fin (n + 1) → ℂ) :
    MvPolynomial.eval₂ (Polynomial.evalRingHom c) Y (reversedRelation P)
      = Polynomial.eval₂ (MvPolynomial.eval Y) c
          (((MvPolynomial.finSuccEquiv ℂ (n + 1)) P).reverse) := by
  classical
  set q := ((MvPolynomial.finSuccEquiv ℂ (n + 1)) P).reverse with hq
  rw [reversedRelation, MvPolynomial.eval₂_sum, Polynomial.eval₂_eq_sum_range]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_map]
  have hid : (Polynomial.evalRingHom c).comp (Polynomial.C : ℂ →+* Polynomial ℂ)
      = RingHom.id ℂ := by
    ext a
    simp
  rw [hid]
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_monomial]
  have hev : MvPolynomial.eval₂ (RingHom.id ℂ) Y (q.coeff b) = MvPolynomial.eval Y (q.coeff b) :=
    rfl
  rw [hev]
  ring


/-! ### The theorem -/

theorem jetChange_sum_eq (hs : 0 < s)
    (hne : ((HTGeometry.powerGenus s : ℕ) : ℝ) ≠ 1 / s) {n : ℕ} {t : ℝ} (ht : 0 < t)
    (i : Fin (n + 1)) :
    ∑ j : Fin (n + 1), (Polynomial.evalRingHom ((t : ℝ) : ℂ)) (jetChangeMatrix n i j)
        * barnesEulerJet s (j : ℕ) t
      = iteratedDeriv (i : ℕ) (barnesRemainderC s) (((1 / t : ℝ)) : ℂ) := by
  classical
  have hx : (0 : ℝ) < 1 / t := by positivity
  have htinv : 1 / (1 / t) = t := by field_simp
  have hval : ∀ j : Fin (n + 1),
      (Polynomial.evalRingHom ((t : ℝ) : ℂ)) (jetChangeMatrix n i j)
        = ((eulerJetCoeff (i : ℕ) (j : ℕ) : ℤ) : ℂ) * (-1 : ℂ) ^ (j : ℕ)
          * ((t : ℝ) : ℂ) ^ (i : ℕ) := by
    intro j
    rw [jetChangeMatrix]
    simp
  have hstep : ∑ j : Fin (n + 1), (Polynomial.evalRingHom ((t : ℝ) : ℂ)) (jetChangeMatrix n i j)
        * barnesEulerJet s (j : ℕ) t
      = ((t : ℝ) : ℂ) ^ (i : ℕ) * ∑ k ∈ Finset.range (n + 1),
          ((eulerJetCoeff (i : ℕ) k : ℤ) : ℂ) * ((-1 : ℂ) ^ k * barnesEulerJet s k t) := by
    rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range
      (fun k => ((t : ℝ) : ℂ) ^ (i : ℕ) *
        (((eulerJetCoeff (i : ℕ) k : ℤ) : ℂ) * ((-1 : ℂ) ^ k * barnesEulerJet s k t))) (n + 1)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hval j]
    ring
  have htrunc : ∑ k ∈ Finset.range (n + 1),
        ((eulerJetCoeff (i : ℕ) k : ℤ) : ℂ) * ((-1 : ℂ) ^ k * barnesEulerJet s k t)
      = ∑ k ∈ Finset.range ((i : ℕ) + 1),
          ((eulerJetCoeff (i : ℕ) k : ℤ) : ℂ) * ((-1 : ℂ) ^ k * barnesEulerJet s k t) := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro k hk
      have h1 : k < (i : ℕ) + 1 := Finset.mem_range.mp hk
      have h2 : (i : ℕ) < n + 1 := i.2
      exact Finset.mem_range.mpr (by omega)
    · intro k _ hk
      have hk' : ¬ k < (i : ℕ) + 1 := fun h => hk (Finset.mem_range.mpr h)
      rw [eulerJetCoeff_eq_zero_of_lt (by omega)]
      push_cast
      ring
  have hjet := weightedJet_barnesRemainderC hs hne (i : ℕ) hx
  rw [htinv] at hjet
  rw [hstep, htrunc, ← hjet, weightedJet]
  have hcast : ((t : ℝ) : ℂ) * (((1 / t : ℝ)) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, show t * (1 / t) = 1 from by field_simp, Complex.ofReal_one]
  calc ((t : ℝ) : ℂ) ^ (i : ℕ) * ((((1 / t : ℝ)) : ℂ) ^ (i : ℕ)
        * iteratedDeriv (i : ℕ) (barnesRemainderC s) (((1 / t : ℝ)) : ℂ))
      = (((t : ℝ) : ℂ) * (((1 / t : ℝ)) : ℂ)) ^ (i : ℕ)
          * iteratedDeriv (i : ℕ) (barnesRemainderC s) (((1 / t : ℝ)) : ℂ) := by
        rw [mul_pow]; ring
    _ = iteratedDeriv (i : ℕ) (barnesRemainderC s) (((1 / t : ℝ)) : ℂ) := by
        rw [hcast, one_pow, one_mul]

/-- **Irrational-power canonical products are hypertranscendental.** -/
theorem hypertranscendental_powerCanonicalProduct_irrational (hs : 0 < s) (hirr : Irrational s) :
    Hypertranscendental (HTGeometry.powerCanonicalProduct s) := by
  classical
  intro hDA
  have hne := powerGenus_ne_inv_of_irrational hs hirr
  have hW := analyticOnNhd_powerCanonicalProduct_rightHalfPlane hs
  obtain ⟨m, P₀, hP₀0, hP₀⟩ := hDA
  have hWm : DifferentialAlgebraicOver (RatFunc ℂ)
      (analyticMeroElement (HTGeometry.powerCanonicalProduct s) hW) :=
    differentialAlgebraicOver_analyticMeroElement_of_relation
      HTGeometry.isOpen_rightHalfPlane HTGeometry.isPreconnected_rightHalfPlane
      HTGeometry.rightHalfPlane_nonempty HTGeometry.rightHalfPlane_infinite hW hP₀0
      (fun z _ => hP₀ z)
  have hRm := differentialAlgebraicOver_barnesRemainderC hs hWm
  obtain ⟨n, P, hP0, hP⟩ :=
    exists_relation_of_differentialAlgebraicOver_analyticMeroElement
      HTGeometry.isOpen_rightHalfPlane HTGeometry.isPreconnected_rightHalfPlane
      HTGeometry.rightHalfPlane_nonempty HTGeometry.rightHalfPlane_infinite
      (analyticOnNhd_barnesRemainderC hs) hRm
  have hQ0 : matrixSubst (jetChangeMatrix n) (reversedRelation P) ≠ 0 := by
    intro h
    exact reversedRelation_ne_zero hP0
      (matrixSubst_jetChangeMatrix_injective n (by rw [h, map_zero]))
  refine not_polynomial_relation_barnesEulerJet hs hirr _ hQ0 ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : (0 : ℝ) < t := ht
  have hx : (0 : ℝ) < 1 / t := by positivity
  have hmem : (((1 / t : ℝ)) : ℂ) ∈ HTGeometry.rightHalfPlane :=
    HTGeometry.ofReal_mem_rightHalfPlane hx
  have hrel := hP _ hmem
  rw [MvPolynomial.eval_eq_eval_mv_eval', Polynomial.eval_map] at hrel
  have hzne : (((1 / t : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  letI : Invertible ((((1 / t : ℝ)) : ℂ)) := invertibleOfNonzero hzne
  have hinv : ⅟(((1 / t : ℝ)) : ℂ) = ((t : ℝ) : ℂ) :=
    invOf_eq_right_inv (by
      rw [← Complex.ofReal_mul, show (1 / t) * t = 1 from by field_simp, Complex.ofReal_one])
  have hrev : Polynomial.eval₂
      (MvPolynomial.eval fun j : Fin (n + 1) =>
        iteratedDeriv (j : ℕ) (barnesRemainderC s) (((1 / t : ℝ)) : ℂ))
      (⅟(((1 / t : ℝ)) : ℂ))
      ((MvPolynomial.finSuccEquiv ℂ (n + 1) P).reverse) = 0 :=
    (Polynomial.eval₂_reverse_eq_zero_iff _ _ _).mpr hrel
  rw [hinv] at hrev
  rw [eval₂_matrixSubst]
  have hfun : (fun i : Fin (n + 1) => ∑ j : Fin (n + 1),
      (Polynomial.evalRingHom ((t : ℝ) : ℂ)) (jetChangeMatrix n i j)
        * barnesEulerJet s (j : ℕ) t)
      = fun i : Fin (n + 1) =>
        iteratedDeriv (i : ℕ) (barnesRemainderC s) (((1 / t : ℝ)) : ℂ) := by
    funext i
    exact jetChange_sum_eq hs hne htpos i
  rw [hfun, eval₂_reversedRelation]
  exact hrev

end

end RHTower
