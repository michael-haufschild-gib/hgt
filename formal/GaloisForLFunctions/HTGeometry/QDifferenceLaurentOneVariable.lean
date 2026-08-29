import GaloisForLFunctions.HTGeometry.QDifferenceInhomogeneousHT
import GaloisForLFunctions.HTGeometry.SimplePoleEulerCombination

/-!
# The one-variable Laurent model of a `q`-difference field

When the multiplier of the homogeneous equation is a power of the dilation parameter, no second
coordinate is needed: the twisting element is already a monomial, and the additive primitive lives
in the same Laurent field.  The invariants of `k((w))` under `w ↦ βw` are the constants exactly
when `β` is not a root of unity, so the differential Ostrowski criterion applies directly.
-/

namespace GaloisForLFunctions.HTGeometry

open HahnSeries Multiplicative

open scoped RatFunc

noncomputable section

variable {k : Type*} [Field k]

theorem innerDilation_innerDilation_inv (β : k) (hβ : β ≠ 0) (f : LaurentSeries k) :
    innerDilation β⁻¹ (inv_ne_zero hβ) (innerDilation β hβ f) = f := by
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  rw [coeff_innerDilation, coeff_innerDilation, inv_zpow, ← zpow_neg,
    show β ^ (-n) * (β ^ n * f.coeff n) = (β ^ (-n) * β ^ n) * f.coeff n from by ring,
    ← zpow_add₀ hβ, neg_add_cancel, zpow_zero, one_mul]

theorem innerDilation_inv_innerDilation (β : k) (hβ : β ≠ 0) (f : LaurentSeries k) :
    innerDilation β hβ (innerDilation β⁻¹ (inv_ne_zero hβ) f) = f := by
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  rw [coeff_innerDilation, coeff_innerDilation, inv_zpow, ← zpow_neg,
    show β ^ n * (β ^ (-n) * f.coeff n) = (β ^ n * β ^ (-n)) * f.coeff n from by ring,
    ← zpow_add₀ hβ, add_neg_cancel, zpow_zero, one_mul]

/-- The dilation of `k((w))` as an automorphism. -/
def innerDilationEquiv (β : k) (hβ : β ≠ 0) : LaurentSeries k ≃+* LaurentSeries k where
  toFun := innerDilation β hβ
  invFun := innerDilation β⁻¹ (inv_ne_zero hβ)
  left_inv f := innerDilation_innerDilation_inv β hβ f
  right_inv f := innerDilation_inv_innerDilation β hβ f
  map_mul' := map_mul _
  map_add' := map_add _

/-- The dilation of `k(w)` as an automorphism. -/
def ratFuncScaleEquiv (β : k) (hβ : β ≠ 0) : RatFunc k ≃+* RatFunc k where
  toFun := ratFuncScale β hβ
  invFun := ratFuncScale β⁻¹ (inv_ne_zero hβ)
  left_inv f := ratFuncScale_scale_inv β hβ f
  right_inv f := by
    have h : ratFuncScale β hβ (ratFuncScale β⁻¹ (inv_ne_zero hβ) f) = f := by
      refine RatFunc.induction_on (P := fun f =>
        ratFuncScale β hβ (ratFuncScale β⁻¹ (inv_ne_zero hβ) f) = f) f ?_
      intro p s _
      rw [ratFuncScale_div, ratFuncScale_div, polyScale_polyScale, polyScale_polyScale,
        mul_inv_cancel₀ hβ, polyScale_one, polyScale_one]
    exact h
  map_mul' := map_mul _
  map_add' := map_add _

/-- **The invariants of a nonresonant dilation of `k((w))` are the constants.** -/
theorem exists_C_of_innerDilation_eq_self {β : k} (hβ : β ≠ 0)
    (hβtor : ∀ n : ℤ, n ≠ 0 → β ^ n ≠ 1) {f : LaurentSeries k}
    (hf : innerDilation β hβ f = f) : ∃ c : k, f = HahnSeries.C c := by
  refine ⟨f.coeff 0, ?_⟩
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  by_cases h : n = 0
  · subst h; simp [HahnSeries.C_apply]
  · have hcoeff := congrArg (fun x : LaurentSeries k => x.coeff n) hf
    simp only [coeff_innerDilation] at hcoeff
    have hzero : f.coeff n = 0 := by
      by_contra hne
      refine hβtor n h ?_
      have h1 : β ^ n * f.coeff n = 1 * f.coeff n := by rw [one_mul]; exact hcoeff
      exact mul_right_cancel₀ hne h1
    simp [hzero, HahnSeries.C_apply, h]

set_option maxHeartbeats 1000000 in
/-- **The differential Ostrowski criterion in the one-variable Laurent model.**  An additive
primitive of a rational increment for the dilation `w ↦ βw` is differentially transcendental over
`k(w)` as soon as no nonzero constant-coefficient differential character of the increment is a
dilation coboundary. -/
theorem differentialIndependent_of_oneVariable_primitive [CharZero k]
    (β : k) (hβ : β ≠ 0) (hβtor : ∀ n : ℤ, n ≠ 0 → β ^ n ≠ 1)
    (u : LaurentSeries k) (bb : RatFunc k)
    (hshift : innerDilation β hβ u = u + algebraMap (RatFunc k) (LaurentSeries k) bb)
    (hnot : letI := cylinderDifferential (1 : k)
      ∀ c : (Unit × ℕ) →₀ k, c ≠ 0 → ∀ y : RatFunc k,
        ratFuncScale β hβ y - y ≠
          Finsupp.linearCombination (RatFunc k)
            (fun p : Unit × ℕ => differentialJet p.2 bb)
            (Finsupp.mapRange (algebraMap k (RatFunc k)) (map_zero _) c)) :
    letI := cylinderDifferential (1 : k)
    letI := innerDifferential (k := k)
    DifferentialIndependent (RatFunc k) (fun _ : Unit => u) := by
  letI := cylinderDifferential (1 : k)
  letI := innerDifferential (k := k)
  haveI := IsScalarTower.of_algebraMap_eq (R := k) (S := RatFunc k) (A := LaurentSeries k)
    fun c => by
      rw [algebraMap_k_laurentSeries]
      exact (algebraMap_const_laurentSeries c).symm
  haveI : DifferentialAlgebra (RatFunc k) (LaurentSeries k) :=
    ⟨fun x => by
      rw [innerDifferential_deriv, cylinderDifferential_deriv, cylDeriv_one_eq_ratFuncEulerOp,
        algebraMap_ratFuncEulerOp]⟩
  refine automorphismFamily_differentialIndependent_of_no_constant_simultaneous_jet_telescoping
    (C := k) (K := RatFunc k) (L := LaurentSeries k)
    (fun _ : Unit => ratFuncScaleEquiv β hβ) (fun _ : Unit => innerDilationEquiv β hβ)
    (fun _ x => by exact (algebraMap_ratFuncScale β hβ x).symm)
    (fun _ x => by exact innerDilation_innerEuler β hβ x)
    (fun _ c => ?_) (fun z hz => ?_) (fun _ : Unit => u) (fun _ _ => bb) (fun _ _ => by exact hshift)
    (fun c hc y => ?_)
  · show innerDilation β hβ (algebraMap k (LaurentSeries k) c) = _
    rw [algebraMap_k_laurentSeries, innerDilation_C]
  · obtain ⟨c, hc⟩ := exists_C_of_innerDilation_eq_self hβ hβtor (hz ())
    exact ⟨c, by rw [hc, algebraMap_k_laurentSeries]⟩
  · exact ⟨(), hnot c hc y⟩

/-! ## The telescoping obstruction in one variable -/

/-- A nonzero constant-coefficient jet character is a nonzero Euler combination. -/
theorem exists_eulerCombination_of_jetCombination_oneVar (c : (Unit × ℕ) →₀ k) (hc : c ≠ 0)
    (w : RatFunc k) :
    letI := cylinderDifferential (1 : k)
    ∃ (α : ℕ → k) (N : ℕ), α N ≠ 0 ∧
      Finsupp.linearCombination (RatFunc k)
        (fun q : Unit × ℕ => differentialJet q.2 w)
        (Finsupp.mapRange (algebraMap k (RatFunc k)) (map_zero _) c)
        = eulerCombination α N w := by
  classical
  letI := cylinderDifferential (1 : k)
  have hsne : (c.support.image Prod.snd).Nonempty := by
    obtain ⟨q, hq⟩ := Finsupp.support_nonempty_iff.mpr hc
    exact ⟨q.2, Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩
  refine ⟨fun i => c ((), i), (c.support.image Prod.snd).max' hsne, ?_, ?_⟩
  · show c ((), (c.support.image Prod.snd).max' hsne) ≠ 0
    obtain ⟨q, hq, hq2⟩ := Finset.mem_image.mp (Finset.max'_mem _ hsne)
    have hqeq : ((), (c.support.image Prod.snd).max' hsne) = q :=
      Prod.ext (Subsingleton.elim _ _) hq2.symm
    rw [hqeq]
    exact Finsupp.mem_support_iff.mp hq
  · rw [Finsupp.linearCombination_apply, Finsupp.sum,
      Finsupp.support_mapRange_of_injective (map_zero _) c (algebraMap k (RatFunc k)).injective]
    simp only [Finsupp.mapRange_apply, smul_eq_mul]
    have hjet : ∀ n : ℕ, differentialJet n w = ratFuncEulerOp^[n] w := by
      intro n
      rw [differentialJet_cylinder]
      induction n with
      | zero => simp
      | succ m ih =>
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
            cylDeriv_one_eq_ratFuncEulerOp]
    have hmap : ∀ i : ℕ, algebraMap k (RatFunc k) (c ((), i)) * ratFuncEulerOp^[i] w
        = toRF (Polynomial.C (c ((), i))) * ratFuncEulerOp^[i] w := by
      intro i
      rw [algebraMap_eq_toRF_C]
    simp only [hjet, hmap]
    rw [sum_unitProd c.support (fun q : Unit × ℕ =>
      toRF (Polynomial.C (c q)) * ratFuncEulerOp^[q.2] w), eulerCombination]
    refine Finset.sum_subset ?_ ?_
    · intro n hn
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_max' _ n hn))
    · intro n _ hn
      have hzero : c ((), n) = 0 := by
        by_contra hne
        exact hn (Finset.mem_image.mpr ⟨((), n), Finsupp.mem_support_iff.mpr hne, rfl⟩)
      simp [hzero]

/-- Regularity of a simple-pole quotient away from its poles. -/
theorem regularAt_simplePoleQuotient (A S : Polynomial k) (p₀ w : k)
    (hden : (Polynomial.X - Polynomial.C p₀).eval w ≠ 0) (hS : S.eval w ≠ 0) :
    RegularAt (toRF A / (toRF (Polynomial.X - Polynomial.C p₀) * toRF S)) w :=
  ⟨A, (Polynomial.X - Polynomial.C p₀) * S, by
    rw [Polynomial.eval_mul]
    exact mul_ne_zero hden hS, by rw [map_mul]⟩

/-- **No constant-coefficient jet character of a simple-pole increment is a dilation
coboundary.** -/
theorem no_jetTelescoper_simplePole [CharZero k] (β : k) (hβ : β ≠ 0)
    (hβtor : ∀ n : ℤ, n ≠ 0 → β ^ n ≠ 1) (p₀ : k) (hp₀ : p₀ ≠ 0)
    (A S : Polynomial k) (hS : S.eval p₀ ≠ 0) (hA : A.eval p₀ ≠ 0)
    (hreg : ∀ n : ℤ, n ≠ 0 →
      RegularAt (toRF A / (toRF (Polynomial.X - Polynomial.C p₀) * toRF S)) (p₀ * β ^ n)) :
    letI := cylinderDifferential (1 : k)
    ∀ c : (Unit × ℕ) →₀ k, c ≠ 0 → ∀ y : RatFunc k,
      ratFuncScale β hβ y - y ≠
        Finsupp.linearCombination (RatFunc k)
          (fun q : Unit × ℕ => differentialJet q.2
            (toRF A / (toRF (Polynomial.X - Polynomial.C p₀) * toRF S)))
          (Finsupp.mapRange (algebraMap k (RatFunc k)) (map_zero _) c) := by
  letI := cylinderDifferential (1 : k)
  intro c hc y heq
  obtain ⟨α, N, hαN, hcomb⟩ := exists_eulerCombination_of_jetCombination_oneVar c hc
    (toRF A / (toRF (Polynomial.X - Polynomial.C p₀) * toRF S))
  rw [hcomb] at heq
  refine not_dilationTelescoped_of_unique_multOrbit_pole β p₀ hβ hp₀ hβtor _ ?_ ?_ ⟨y, heq.symm⟩
  · exact not_regularAt_eulerCombination_simplePole p₀ hp₀ A S hS hA α N hαN
  · intro n hn
    exact regularAt_eulerCombination α N (hreg n hn)

/-! ## Hypertranscendence for a monomial twist -/

theorem ratFuncScale_X_zpow (β : k) (hβ : β ≠ 0) (m : ℕ) :
    ratFuncScale β hβ ((RatFunc.X : RatFunc k) ^ m)
      = algebraMap k (RatFunc k) (β ^ m) * (RatFunc.X : RatFunc k) ^ m := by
  have hX : ratFuncScale β hβ (RatFunc.X : RatFunc k)
      = algebraMap k (RatFunc k) β * RatFunc.X := by
    rw [show (RatFunc.X : RatFunc k) = algebraMap (Polynomial k) (RatFunc k) Polynomial.X from
        RatFunc.algebraMap_X.symm,
      show algebraMap (Polynomial k) (RatFunc k) Polynomial.X
        = algebraMap (Polynomial k) (RatFunc k) Polynomial.X /
          algebraMap (Polynomial k) (RatFunc k) 1 from by rw [map_one, div_one],
      ratFuncScale_div, polyScale_X, map_one, map_one, div_one, div_one, map_mul]
    congr 1
  rw [map_pow, hX, mul_pow, map_pow]

set_option maxHeartbeats 1000000 in
/-- **Hypertranscendence for a monomial-twisted first-order equation.**  If the multiplier of the
homogeneous equation is a power of the dilation parameter and the twisted increment has a simple
pole at `1` with no other pole on the orbit of `1`, then every Laurent solution is differentially
transcendental over `k(w)`. -/
theorem hypertranscendentalOver_of_monomialTwist [CharZero k]
    (β : k) (hβ : β ≠ 0) (hβtor : ∀ n : ℤ, n ≠ 0 → β ^ n ≠ 1) (m : ℕ)
    (p₀ : k) (hp₀ : p₀ ≠ 0) (A S : Polynomial k) (hS : S.eval p₀ ≠ 0) (hA : A.eval p₀ ≠ 0)
    (hreg : ∀ n : ℤ, n ≠ 0 →
      RegularAt (toRF A / (toRF (Polynomial.X - Polynomial.C p₀) * toRF S)) (p₀ * β ^ n))
    (r : RatFunc k) (R : LaurentSeries k)
    (hR : R - algebraMap k (LaurentSeries k) (β ^ m) * innerDilation β hβ R
      = algebraMap (RatFunc k) (LaurentSeries k) r)
    (hbb : -(r * (RatFunc.X : RatFunc k) ^ m)
      = toRF A / (toRF (Polynomial.X - Polynomial.C p₀) * toRF S)) :
    letI := cylinderDifferential (1 : k)
    letI := innerDifferential (k := k)
    HypertranscendentalOver (RatFunc k) R := by
  letI := cylinderDifferential (1 : k)
  letI := innerDifferential (k := k)
  haveI := IsScalarTower.of_algebraMap_eq (R := k) (S := RatFunc k) (A := LaurentSeries k)
    fun c => by
      rw [algebraMap_k_laurentSeries]
      exact (algebraMap_const_laurentSeries c).symm
  haveI : DifferentialAlgebra (RatFunc k) (LaurentSeries k) :=
    ⟨fun x => by
      rw [innerDifferential_deriv, cylinderDifferential_deriv, cylDeriv_one_eq_ratFuncEulerOp,
        algebraMap_ratFuncEulerOp]⟩
  haveI : CharZero (LaurentSeries k) :=
    charZero_of_injective_algebraMap (algebraMap k (LaurentSeries k)).injective
  have hstep : algebraMap k (LaurentSeries k) (β ^ m) * innerDilation β hβ R
      = R - algebraMap (RatFunc k) (LaurentSeries k) r := by
    rw [← hR]; ring
  have hshift : innerDilation β hβ
      (R * algebraMap (RatFunc k) (LaurentSeries k) ((RatFunc.X : RatFunc k) ^ m))
      = R * algebraMap (RatFunc k) (LaurentSeries k) ((RatFunc.X : RatFunc k) ^ m)
        + algebraMap (RatFunc k) (LaurentSeries k) (-(r * (RatFunc.X : RatFunc k) ^ m)) := by
    rw [map_mul, ← algebraMap_ratFuncScale, ratFuncScale_X_zpow, map_mul,
      ← IsScalarTower.algebraMap_apply k (RatFunc k) (LaurentSeries k),
      show innerDilation β hβ R * (algebraMap k (LaurentSeries k) (β ^ m)
          * algebraMap (RatFunc k) (LaurentSeries k) ((RatFunc.X : RatFunc k) ^ m))
        = (algebraMap k (LaurentSeries k) (β ^ m) * innerDilation β hβ R)
          * algebraMap (RatFunc k) (LaurentSeries k) ((RatFunc.X : RatFunc k) ^ m) from by ring,
      hstep, map_neg, map_mul]
    ring
  have hu := differentialIndependent_of_oneVariable_primitive β hβ hβtor
    (R * algebraMap (RatFunc k) (LaurentSeries k) ((RatFunc.X : RatFunc k) ^ m))
    (-(r * (RatFunc.X : RatFunc k) ^ m)) hshift
    (by
      rw [hbb]
      exact no_jetTelescoper_simplePole β hβ hβtor p₀ hp₀ A S hS hA hreg)
  intro hDA
  have hmem : R * algebraMap (RatFunc k) (LaurentSeries k) ((RatFunc.X : RatFunc k) ^ m)
      ∈ differentialAdjoin (RatFunc k) ({R} : Set (LaurentSeries k)) :=
    mul_mem (subset_differentialAdjoin (RatFunc k) _ rfl)
      (IntermediateField.algebraMap_mem _ _)
  exact differentialAlgebraicOver_of_mem_differentialAdjoin_singleton hDA hmem hu

end

end GaloisForLFunctions.HTGeometry
