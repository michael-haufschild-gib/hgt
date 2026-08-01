import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Place-average residues on a number field

For a number field `K` and a finite place `v`, the logarithmic Kummer function
`α ↦ log ‖α‖` is constant on the fibre of places lying over `v`, so its place-average is the
measure of that fibre times the local logarithm.  Normalizing the fibre measure by the local
degree turns the average into the valuation residue.

* `deningerPlaceOrd v α` is the order of vanishing of `α` at `v`, and `deningerLog_adicAbv`
  computes the logarithm of the norm-normalized absolute value as `-ord_v(α) · log N v`.
* `deningerLogAbsQp p e n` is the logarithm of the `ℚ_p`-normalized absolute value, and
  `deningerLog_adicAbv_eq_localDegree_mul` is the local-degree specialization: the two
  normalizations differ exactly by the factor `e f`.
* `deningerPlaceAverage_eq` and `deningerPlaceAverage_setIntegral` are the place-average
  identity, and `deningerOrd_eq_of_placeAverage` inverts it into the residue formula.
* `deningerLog_prod_abs_eq_zero` and `deningerSum_placeAverage_eq_zero` are the additive form
  of the product formula: the place-averages of a nonzero element sum to zero.
* `deningerMixed_contraction` is the mixed `L¹/L²` step: an operator contracting two seminorms
  contracts their sum.
-/

namespace RHTower

open NumberField IsDedekindDomain Ideal MeasureTheory

section PlaceOrder

variable {K : Type*} [Field K] [NumberField K]

/-- The order of vanishing at a finite place: the `v`-adic valuation of `α` is
`exp (-ord_v α)`. -/
noncomputable def deningerPlaceOrd (v : HeightOneSpectrum (𝓞 K)) (α : K) : ℤ :=
  -WithZero.log (v.valuation K α)

/-- The additive coordinate of a nonzero element of `ℤᵐ⁰` is its logarithm. -/
theorem deningerToAdd_unzero {x : WithZero (Multiplicative ℤ)} (hx : x ≠ 0) :
    (WithZero.unzero hx).toAdd = WithZero.log x := by
  obtain ⟨a, rfl⟩ : ∃ a : ℤ, x = WithZero.exp a := ⟨WithZero.log x, (WithZero.exp_log hx).symm⟩
  rfl

/-- The valuation of a nonzero element is the exponential of minus its order. -/
theorem deningerValuation_eq_exp (v : HeightOneSpectrum (𝓞 K)) {α : K} (hα : α ≠ 0) :
    v.valuation K α = WithZero.exp (-(deningerPlaceOrd v α)) := by
  have hx : v.valuation K α ≠ 0 := (Valuation.ne_zero_iff _).mpr hα
  rw [deningerPlaceOrd, neg_neg, WithZero.exp_log hx]

/-- The `v`-adic absolute value is the ideal norm raised to minus the order. -/
theorem deningerAdicAbv_eq_zpow (v : HeightOneSpectrum (𝓞 K)) {α : K} (hα : α ≠ 0) :
    NumberField.HeightOneSpectrum.adicAbv K v α
      = (absNorm v.asIdeal : ℝ) ^ (-(deningerPlaceOrd v α)) := by
  have hx : v.valuation K α ≠ 0 := (Valuation.ne_zero_iff _).mpr hα
  have hlog : (WithZero.unzero hx).toAdd = -(deningerPlaceOrd v α) := by
    rw [deningerToAdd_unzero hx, deningerPlaceOrd, neg_neg]
  rw [NumberField.HeightOneSpectrum.adicAbv_def,
    WithZeroMulInt.toNNReal_neg_apply _ hx, hlog, NNReal.coe_zpow]
  norm_cast

/-- **Local residue formula.**  The logarithm of the norm-normalized absolute value at a finite
place is minus the order times the logarithm of the ideal norm. -/
theorem deningerLog_adicAbv (v : HeightOneSpectrum (𝓞 K)) {α : K} (hα : α ≠ 0) :
    Real.log (NumberField.HeightOneSpectrum.adicAbv K v α)
      = -(deningerPlaceOrd v α : ℝ) * Real.log (absNorm v.asIdeal) := by
  rw [deningerAdicAbv_eq_zpow v hα, Real.log_zpow]
  push_cast
  ring

end PlaceOrder

section LocalDegree

/-- The logarithm of the `ℚ_p`-normalized absolute value at a place of ramification index `e`
over the rational prime `p`, on an element of order `n`. -/
noncomputable def deningerLogAbsQp (p e : ℕ) (n : ℤ) : ℝ := -((n : ℝ) / e) * Real.log p

/-- **Local-degree specialization.**  The norm-normalized logarithm is the local degree `e f`
times the `ℚ_p`-normalized logarithm. -/
theorem deningerLog_absNorm_eq_localDegree_mul {p e f : ℕ} (he : e ≠ 0) (n : ℤ)
    {N : ℕ} (hN : N = p ^ f) :
    -(n : ℝ) * Real.log N = ((e : ℝ) * f) * deningerLogAbsQp p e n := by
  have he' : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr he
  rw [deningerLogAbsQp, hN]
  push_cast
  rw [Real.log_pow]
  field_simp

/-- The local-degree specialization at a finite place of a number field. -/
theorem deningerLog_adicAbv_eq_localDegree_mul {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) {α : K} (hα : α ≠ 0) {p e f : ℕ} (he : e ≠ 0)
    (hN : absNorm v.asIdeal = p ^ f) :
    Real.log (NumberField.HeightOneSpectrum.adicAbv K v α)
      = ((e : ℝ) * f) * deningerLogAbsQp p e (deningerPlaceOrd v α) := by
  rw [deningerLog_adicAbv v hα]
  exact deningerLog_absNorm_eq_localDegree_mul he _ hN

/-- The ideal norm of a prime lying over the rational prime `p` is `p` to the inertia degree. -/
theorem deningerAbsNorm_eq_pow_inertiaDeg {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) {p : ℕ} (hp : p.Prime)
    [v.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] :
    absNorm v.asIdeal = p ^ ((Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal) :=
  Ideal.absNorm_eq_pow_inertiaDeg' v.asIdeal hp

/-- **Local-degree specialization at a prime of a number field.**  With mathlib's ramification
index `e` and inertia degree `f` at a prime over the rational prime `p`, the norm-normalized
logarithm is `e f` times the `ℚ_p`-normalized one. -/
theorem deningerLog_adicAbv_eq_ramificationIdx_mul {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) {p : ℕ} (hp : p.Prime)
    [v.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] {α : K} (hα : α ≠ 0) :
    Real.log (NumberField.HeightOneSpectrum.adicAbv K v α)
      = (((Ideal.span {(p : ℤ)}).ramificationIdx' v.asIdeal : ℝ)
          * ((Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal))
        * deningerLogAbsQp p ((Ideal.span {(p : ℤ)}).ramificationIdx' v.asIdeal)
            (deningerPlaceOrd v α) := by
  have hpne : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simp [hp.ne_zero]
  have he : (Ideal.span {(p : ℤ)}).ramificationIdx' v.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver v.asIdeal hpne
  exact deningerLog_adicAbv_eq_localDegree_mul v hα he (deningerAbsNorm_eq_pow_inertiaDeg v hp)

end LocalDegree

section PlaceAverage

/-- **Place-average identity.**  With fibre measure `e f / d`, the average of the
`ℚ_p`-normalized logarithm is minus the order over the field degree times the logarithm of the
ideal norm. -/
theorem deningerPlaceAverage_eq {d p e f : ℕ} (hd : d ≠ 0) (he : e ≠ 0) (n : ℤ) {N : ℕ}
    (hN : N = p ^ f) :
    (((e : ℝ) * f) / d) * deningerLogAbsQp p e n = (-(n : ℝ) / d) * Real.log N := by
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have h := deningerLog_absNorm_eq_localDegree_mul (p := p) (f := f) he n hN
  rw [div_mul_eq_mul_div, ← h]
  ring

/-- The integral of a function constant on a set of prescribed finite measure. -/
theorem deningerPlaceAverage_setIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {Y : Set Ω} (hY : MeasurableSet Y) (g : Ω → ℝ) (c r : ℝ) (hg : Set.EqOn g (fun _ => c) Y)
    (hr : 0 ≤ r) (hμ : μ Y = ENNReal.ofReal r) :
    ∫ y in Y, g y ∂μ = r * c := by
  rw [MeasureTheory.setIntegral_congr_fun hY hg, MeasureTheory.setIntegral_const,
    MeasureTheory.measureReal_def, hμ, ENNReal.toReal_ofReal hr, smul_eq_mul]

/-- **Place-average residue.**  The place-average of the `ℚ_p`-normalized logarithm over a fibre
of measure `e f / d` is the normalized valuation residue. -/
theorem deningerPlaceAverage_setIntegral_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {Y : Set Ω} (hY : MeasurableSet Y) (g : Ω → ℝ) {d p e f : ℕ} (hd : d ≠ 0) (he : e ≠ 0)
    (n : ℤ) {N : ℕ} (hN : N = p ^ f) (hg : Set.EqOn g (fun _ => deningerLogAbsQp p e n) Y)
    (hμ : μ Y = ENNReal.ofReal (((e : ℝ) * f) / d)) :
    ∫ y in Y, g y ∂μ = (-(n : ℝ) / d) * Real.log N := by
  have hr : (0 : ℝ) ≤ ((e : ℝ) * f) / d := by positivity
  rw [deningerPlaceAverage_setIntegral μ hY g _ _ hg hr hμ]
  exact deningerPlaceAverage_eq hd he n hN

/-- **Residue recovery.**  The order at `v` is recovered from the place-average. -/
theorem deningerOrd_eq_of_placeAverage {d : ℕ} (hd : d ≠ 0) (n : ℤ) {N : ℕ} (hN : 1 < N)
    {A : ℝ} (hA : A = (-(n : ℝ) / d) * Real.log N) :
    (n : ℝ) = -((d : ℝ) / Real.log N) * A := by
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hlog : Real.log N ≠ 0 := by
    have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    exact (Real.log_pos this).ne'
  rw [hA]
  field_simp

end PlaceAverage

section ProductFormula

variable {K : Type*} [Field K] [NumberField K]

/-- **Additive product formula.**  The logarithms of all places of a nonzero element, weighted by
the local degrees, sum to zero. -/
theorem deningerLog_prod_abs_eq_zero {α : K} (hα : α ≠ 0) (s : Finset (FinitePlace K))
    (hs : Function.mulSupport (fun w : FinitePlace K => w α) ⊆ s) :
    (∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (w α))
      + ∑ w ∈ s, Real.log (w α) = 0 := by
  have hIpos : ∀ w : InfinitePlace K, 0 < w α := fun w => InfinitePlace.pos_iff.mpr hα
  have hFpos : ∀ w : FinitePlace K, 0 < w α := fun w => FinitePlace.pos_iff.mpr hα
  have hprod := NumberField.prod_abs_eq_one hα
  rw [finprod_eq_prod_of_mulSupport_subset _ hs] at hprod
  have hA : (∏ w : InfinitePlace K, (w α) ^ w.mult) ≠ 0 :=
    (Finset.prod_pos fun w _ => pow_pos (hIpos w) _).ne'
  have hB : (∏ w ∈ s, w α) ≠ 0 := (Finset.prod_pos fun w _ => hFpos w).ne'
  have h := congrArg Real.log hprod
  rw [Real.log_mul hA hB, Real.log_one,
    Real.log_prod (fun w _ => (pow_pos (hIpos w) _).ne'),
    Real.log_prod (fun w _ => (hFpos w).ne')] at h
  simpa only [Real.log_pow] using h

/-- **Place-average product formula.**  Normalized by the field degree, the place-averages of a
nonzero element sum to zero. -/
theorem deningerSum_placeAverage_eq_zero {α : K} (hα : α ≠ 0) (d : ℕ) (s : Finset (FinitePlace K))
    (hs : Function.mulSupport (fun w : FinitePlace K => w α) ⊆ s) :
    (∑ w : InfinitePlace K, ((w.mult : ℝ) / d) * Real.log (w α))
      + ∑ w ∈ s, (1 / (d : ℝ)) * Real.log (w α) = 0 := by
  have h := deningerLog_prod_abs_eq_zero hα s hs
  have hsplit : (∑ w : InfinitePlace K, ((w.mult : ℝ) / d) * Real.log (w α))
      + ∑ w ∈ s, (1 / (d : ℝ)) * Real.log (w α)
      = (1 / (d : ℝ)) * ((∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (w α))
          + ∑ w ∈ s, Real.log (w α)) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun w _ => by ring)
      (Finset.sum_congr rfl fun w _ => rfl)
  rw [hsplit, h, mul_zero]

/-- The finite places outside a fixed finite set contribute nothing. -/
theorem deningerMulSupport_subset_toFinset {α : K} (hα : α ≠ 0) :
    Function.mulSupport (fun w : FinitePlace K => w α)
      ⊆ (NumberField.FinitePlace.hasFiniteMulSupport hα).toFinset := by
  intro w hw
  exact (Set.Finite.mem_toFinset _).mpr hw

/-- **Additive product formula over all places.**  The unrestricted form of
`deningerLog_prod_abs_eq_zero`. -/
theorem deningerLog_prod_abs_eq_zero' {α : K} (hα : α ≠ 0) :
    (∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (w α))
      + ∑ᶠ w : FinitePlace K, Real.log (w α) = 0 := by
  classical
  have hs := deningerMulSupport_subset_toFinset hα
  have hsupp : Function.support (fun w : FinitePlace K => Real.log (w α))
      ⊆ ((NumberField.FinitePlace.hasFiniteMulSupport hα).toFinset :
          Set (FinitePlace K)) := by
    intro w hw
    refine hs ?_
    intro h1
    exact hw (by simp [h1])
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  exact deningerLog_prod_abs_eq_zero hα _ hs

/-- **Place-average product formula over all places.** -/
theorem deningerSum_placeAverage_eq_zero' {α : K} (hα : α ≠ 0) (d : ℕ) :
    (∑ w : InfinitePlace K, ((w.mult : ℝ) / d) * Real.log (w α))
      + ∑ᶠ w : FinitePlace K, (1 / (d : ℝ)) * Real.log (w α) = 0 := by
  classical
  have hs := deningerMulSupport_subset_toFinset hα
  have hsupp : Function.support (fun w : FinitePlace K => (1 / (d : ℝ)) * Real.log (w α))
      ⊆ ((NumberField.FinitePlace.hasFiniteMulSupport hα).toFinset :
          Set (FinitePlace K)) := by
    intro w hw
    refine hs ?_
    intro h1
    exact hw (by simp [h1])
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  exact deningerSum_placeAverage_eq_zero hα d _ hs

end ProductFormula

section MixedContraction

/-- **Mixed contraction.**  An operator contracting two seminorms contracts their sum; this is
the `L¹ + L²` step of the mixed Kummer completion. -/
theorem deningerMixed_contraction {E : Type*} (P : E → E) (n₁ n₂ : E → ℝ)
    (h₁ : ∀ f, n₁ (P f) ≤ n₁ f) (h₂ : ∀ f, n₂ (P f) ≤ n₂ f) (f : E) :
    n₁ (P f) + n₂ (P f) ≤ n₁ f + n₂ f :=
  add_le_add (h₁ f) (h₂ f)

end MixedContraction

end RHTower
