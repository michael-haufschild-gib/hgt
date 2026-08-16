import GaloisForLFunctions.RHTower.LayerCakeZeroCount

/-!
# Exponential layer cake for Route T zero packets

The density theorem counts zeros to the right of a moving abscissa, whereas the explicit formula
weights a zero of real part `β` by a real power `B ^ (β - 1)`.  This file proves the exact finite
identity connecting those two quantities.  In particular, it introduces no mesh or discretization
loss near the zero-free edge.
-/

open MeasureTheory intervalIntegral

namespace RHTower

/-- An exponential layer-cake summand is interval integrable. -/
theorem intervalIntegrable_exponential_indicator_lt
    {B m b σ₀ σ₁ : ℝ} (hB : 0 < B) :
    IntervalIntegrable
      (fun σ => if σ < b then Real.log B * B ^ (σ - 1) * m else 0)
      volume σ₀ σ₁ := by
  have hc : Continuous (fun σ : ℝ => Real.log B * B ^ (σ - 1) * m) := by
    exact (continuous_const.mul
      ((Real.continuous_const_rpow hB.ne').comp
        (continuous_id.sub continuous_const))).mul continuous_const
  have h := (intervalIntegrable_indicator_lt b σ₀ σ₁).mul_continuousOn hc.continuousOn
  simpa [ite_mul, mul_assoc] using h

/-- Exact integral of one exponential layer-cake summand. -/
theorem integral_exponential_indicator_lt
    {B m σ₀ σ₁ b : ℝ} (hB : 0 < B) (h₀ : σ₀ ≤ b) (h₁ : b ≤ σ₁) :
    (∫ σ in σ₀..σ₁,
        if σ < b then Real.log B * B ^ (σ - 1) * m else 0)
      = (B ^ (b - 1) - B ^ (σ₀ - 1)) * m := by
  let g : ℝ → ℝ := fun σ => Real.log B * B ^ (σ - 1) * m
  have hg_cont : Continuous g := by
    dsimp [g]
    exact (continuous_const.mul
      ((Real.continuous_const_rpow hB.ne').comp
        (continuous_id.sub continuous_const))).mul continuous_const
  have hg_int (a c : ℝ) : IntervalIntegrable g volume a c :=
    hg_cont.intervalIntegrable a c
  have hsplit :
      (∫ σ in σ₀..σ₁, if σ < b then g σ else 0)
        = (∫ σ in σ₀..b, if σ < b then g σ else 0)
          + ∫ σ in b..σ₁, if σ < b then g σ else 0 :=
    (integral_add_adjacent_intervals
      (intervalIntegrable_exponential_indicator_lt hB)
      (intervalIntegrable_exponential_indicator_lt hB)).symm
  have hleft : (∫ σ in σ₀..b, if σ < b then g σ else 0) = ∫ σ in σ₀..b, g σ := by
    refine intervalIntegral.integral_congr_ae ?_
    have hne : ∀ᵐ σ : ℝ, σ ≠ b := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hne] with σ hσ hmem
    rw [Set.uIoc_of_le h₀] at hmem
    have : σ < b := lt_of_le_of_ne hmem.2 hσ
    simp [this]
  have hright : (∫ σ in b..σ₁, if σ < b then g σ else 0) = 0 := by
    rw [integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro σ hσ
      rw [Set.uIcc_of_le h₁] at hσ
      have : ¬ σ < b := not_lt.mpr hσ.1
      simp [this]
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun σ : ℝ => B ^ (σ - 1) * m)
        (Real.log B * B ^ (x - 1) * m) x := by
    intro x
    simpa only [id_eq, one_mul, mul_one] using
      (((hasDerivAt_id x).sub_const 1).const_rpow hB).mul_const m
  have heval : (∫ σ in σ₀..b, g σ)
      = (B ^ (b - 1) - B ^ (σ₀ - 1)) * m := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun σ : ℝ => B ^ (σ - 1) * m)
      (f' := g) (a := σ₀) (b := b)
      (fun x _ => hderiv x) (hg_int σ₀ b)
    dsimp [g] at h
    linarith
  change (∫ σ in σ₀..σ₁, if σ < b then g σ else 0) = _
  rw [hsplit, hleft, hright, add_zero, heval]

/-- **Exact exponential layer cake for a finite weighted family.** -/
theorem sum_rpow_sub_eq_integral_weighted_count
    {ι : Type*} [DecidableEq ι] {B σ₀ σ₁ : ℝ}
    (Z : Finset ι) (β m : ι → ℝ) (hB : 0 < B)
    (hZ : ∀ z ∈ Z, σ₀ ≤ β z ∧ β z ≤ σ₁) :
    ∑ z ∈ Z, (B ^ (β z - 1) - B ^ (σ₀ - 1)) * m z
      = ∫ σ in σ₀..σ₁,
          Real.log B * B ^ (σ - 1) *
            ∑ z ∈ Z.filter (fun z => σ < β z), m z := by
  classical
  have hpoint : ∀ σ : ℝ,
      Real.log B * B ^ (σ - 1) *
          ∑ z ∈ Z.filter (fun z => σ < β z), m z
        = ∑ z ∈ Z,
            if σ < β z then Real.log B * B ^ (σ - 1) * m z else 0 := by
    intro σ
    rw [Finset.sum_filter]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    split_ifs <;> simp
  rw [intervalIntegral.integral_congr
    (g := fun σ => ∑ z ∈ Z,
      if σ < β z then Real.log B * B ^ (σ - 1) * m z else 0)
    (fun σ _ => hpoint σ)]
  rw [intervalIntegral.integral_finsetSum
    (fun z _ => intervalIntegrable_exponential_indicator_lt hB)]
  exact Finset.sum_congr rfl fun z hz =>
    (integral_exponential_indicator_lt hB (hZ z hz).1 (hZ z hz).2).symm

end RHTower
