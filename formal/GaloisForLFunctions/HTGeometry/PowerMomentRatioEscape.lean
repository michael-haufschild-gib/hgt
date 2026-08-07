import GaloisForLFunctions.HTGeometry.PowerMomentSupport

/-!
# Adjacent moment-ratio escape from unbounded support

Power moments of a finite nonnegative carrier have escaping adjacent ratios whenever the carrier
has positive mass above every threshold.  The proof compares the contribution below `2R` with
positive mass above `3R`; no quantitative tail estimate is required.
-/

open MeasureTheory Filter Set
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- Power moments of a finite nonnegative carrier with mass arbitrarily far to the right have
escaping adjacent ratios. -/
theorem tendsto_integral_pow_succ_div_integral_pow_atTop
    {α : Type*} [MeasurableSpace α] {mu : Measure α} [IsFiniteMeasure mu]
    {f : α → ℝ} (hf : Measurable f) (hfnn : ∀ x, 0 ≤ f x)
    (hint : ∀ n : ℕ, Integrable (fun x => f x ^ n) mu)
    (hunbounded : ∀ R : ℝ, mu {x | R ≤ f x} ≠ 0) :
    Tendsto (fun n : ℕ =>
      (∫ x, f x ^ (n + 1) ∂mu) / (∫ x, f x ^ n ∂mu)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro C
  let R : ℝ := max C 1 + 1
  have hR : 0 < R := by dsimp [R]; linarith [le_max_right C 1]
  have hCR : C < R := by dsimp [R]; linarith [le_max_left C 1]
  let S : Set α := {x | 2 * R ≤ f x}
  let B : Set α := {x | 3 * R ≤ f x}
  have hS : MeasurableSet S := measurableSet_le measurable_const hf
  have hB : MeasurableSet B := measurableSet_le measurable_const hf
  have hBmu : mu B ≠ 0 := hunbounded (3 * R)
  have hbpos : 0 < (mu B).toReal := ENNReal.toReal_pos hBmu (measure_ne_top mu B)
  have hpow : Tendsto (fun n : ℕ => (2 / 3 : ℝ) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num : (2 / 3 : ℝ) < 1)
  have hgeom : Tendsto (fun n : ℕ => (2 / 3 : ℝ) ^ n * (mu Set.univ).toReal)
      atTop (nhds 0) := by
    simpa using hpow.mul tendsto_const_nhds
  have hevent : ∀ᶠ n : ℕ in atTop,
      (2 / 3 : ℝ) ^ n * (mu Set.univ).toReal < (mu B).toReal :=
    (tendsto_order.1 hgeom).2 _ hbpos
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  refine ⟨N, fun n hn => ?_⟩
  have hgeomN : (2 / 3 : ℝ) ^ n * (mu Set.univ).toReal ≤ (mu B).toReal :=
    (hN n hn).le
  have hBsubS : B ⊆ S := by
    intro x hx
    dsimp [B] at hx
    dsimp [S]
    nlinarith
  have hpowint := hint n
  have hpowsuccint := hint (n + 1)
  have hlow :
      (∫ x in Sᶜ, f x ^ n ∂mu) ≤ (2 * R) ^ n * (mu Set.univ).toReal := by
    calc
      (∫ x in Sᶜ, f x ^ n ∂mu) ≤ ∫ _x in Sᶜ, (2 * R) ^ n ∂mu := by
        apply setIntegral_mono_on hpowint.integrableOn integrableOn_const hS.compl
        intro x hx
        have hxlt : f x < 2 * R := by
          simpa [S] using hx
        exact pow_le_pow_left₀ (hfnn x) hxlt.le n
      _ = (mu (Sᶜ)).toReal * (2 * R) ^ n := by
        rw [setIntegral_const, smul_eq_mul]
        simp [Measure.real]
      _ ≤ (mu Set.univ).toReal * (2 * R) ^ n := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by positivity) n)
        exact ENNReal.toReal_mono (measure_ne_top mu Set.univ)
          (measure_mono (Set.subset_univ _))
      _ = (2 * R) ^ n * (mu Set.univ).toReal := by ring
  have hscale :
      (2 * R) ^ n * (mu Set.univ).toReal ≤
        (3 * R) ^ n * (mu B).toReal := by
    calc
      (2 * R) ^ n * (mu Set.univ).toReal =
          (2 : ℝ) ^ n * R ^ n * (mu Set.univ).toReal := by rw [mul_pow]
      _ = ((3 : ℝ) ^ n * (2 / 3 : ℝ) ^ n) * R ^ n * (mu Set.univ).toReal := by
        have hnum : (3 : ℝ) ^ n * (2 / 3 : ℝ) ^ n = 2 ^ n := by
          rw [← mul_pow]
          norm_num
        rw [hnum]
      _ = (3 * R) ^ n * ((2 / 3 : ℝ) ^ n * (mu Set.univ).toReal) := by
        rw [mul_pow]
        ring
      _ ≤ (3 * R) ^ n * (mu B).toReal :=
        mul_le_mul_of_nonneg_left hgeomN (pow_nonneg (by positivity) n)
  have htailLower :
      (3 * R) ^ n * (mu B).toReal ≤ ∫ x in S, f x ^ n ∂mu := by
    calc
      (3 * R) ^ n * (mu B).toReal = ∫ _x in B, (3 * R) ^ n ∂mu := by
        rw [setIntegral_const, smul_eq_mul]
        simp [Measure.real]
        ring
      _ ≤ ∫ x in B, f x ^ n ∂mu := by
        apply setIntegral_mono_on integrableOn_const hpowint.integrableOn hB
        intro x hx
        exact pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 3 * R) hx n
      _ ≤ ∫ x in S, f x ^ n ∂mu := by
        apply setIntegral_mono_set hpowint.integrableOn
          (Filter.Eventually.of_forall fun x => pow_nonneg (hfnn x) n)
        exact Filter.Eventually.of_forall fun x hx => hBsubS hx
  have hlowTail : (∫ x in Sᶜ, f x ^ n ∂mu) ≤ ∫ x in S, f x ^ n ∂mu :=
    hlow.trans (hscale.trans htailLower)
  have htailpos : 0 < ∫ x in S, f x ^ n ∂mu := by
    have : 0 < (3 * R) ^ n * (mu B).toReal := mul_pos (pow_pos (by positivity) n) hbpos
    exact this.trans_le htailLower
  have hmomentSplit :
      (∫ x, f x ^ n ∂mu) =
        (∫ x in S, f x ^ n ∂mu) + (∫ x in Sᶜ, f x ^ n ∂mu) := by
    exact (integral_add_compl hS hpowint).symm
  have hmomentpos : 0 < ∫ x, f x ^ n ∂mu := by
    rw [hmomentSplit]
    have hlow0 : 0 ≤ ∫ x in Sᶜ, f x ^ n ∂mu :=
      setIntegral_nonneg hS.compl fun x _ => pow_nonneg (hfnn x) n
    linarith
  have hnextLower :
      2 * R * (∫ x in S, f x ^ n ∂mu) ≤ ∫ x, f x ^ (n + 1) ∂mu := by
    calc
      2 * R * (∫ x in S, f x ^ n ∂mu) =
          ∫ x in S, 2 * R * f x ^ n ∂mu := by
            rw [integral_const_mul]
      _ ≤ ∫ x in S, f x ^ (n + 1) ∂mu := by
        apply setIntegral_mono_on (hpowint.const_mul (2 * R)).integrableOn
          hpowsuccint.integrableOn hS
        intro x hx
        rw [pow_succ]
        nlinarith [mul_le_mul_of_nonneg_right hx (pow_nonneg (hfnn x) n)]
      _ ≤ ∫ x, f x ^ (n + 1) ∂mu :=
        setIntegral_le_integral hpowsuccint
          (Filter.Eventually.of_forall fun x => pow_nonneg (hfnn x) (n + 1))
  rw [le_div_iff₀ hmomentpos]
  by_cases hC : 0 ≤ C
  · calc
      C * (∫ x, f x ^ n ∂mu) =
          C * ((∫ x in S, f x ^ n ∂mu) + (∫ x in Sᶜ, f x ^ n ∂mu)) := by
        rw [hmomentSplit]
      _ ≤ C * (2 * ∫ x in S, f x ^ n ∂mu) := by
        gcongr
        linarith
      _ ≤ 2 * R * (∫ x in S, f x ^ n ∂mu) := by
        nlinarith [htailpos]
      _ ≤ ∫ x, f x ^ (n + 1) ∂mu := hnextLower
  · have hleft : C * (∫ x, f x ^ n ∂mu) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hC) hmomentpos.le
    exact hleft.trans (integral_nonneg fun x => pow_nonneg (hfnn x) (n + 1))

end GaloisForLFunctions.HTGeometry
