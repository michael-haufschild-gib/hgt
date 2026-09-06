import GaloisForLFunctions.RHTower.XiCTaylorThetaTailMomentLogConvex
import GaloisForLFunctions.RHTower.HedenmalmCenterMixedThreePoint

/-!
# Full theta moment growth obstructs the literal odd source Gram representation

Write `μ_j` for the normalized even moments of the complete theta density. The odd-monomial
Gram matrix is `D_ij = μ_(i+j+1) / ((2i+1)! (2j+1)!)`. Clearing the two Xi factors in the
logarithmic Hankel generating kernel gives a different coefficient matrix. In its sign-adjusted
row `i=1`, column `j=n+1`, the coefficient is the expression `thetaCuspClearedOddGramRow n`.

This file proves the exact difference of these two explicit source-moment expressions. It then
proves that the raw moment ratios tend to infinity, directly from positive source windows and
the corpus's moment log-convexity. Consequently the Gram entry strictly exceeds the cleared entry
eventually. Their literal all-order identification is false.

This is not a negative logarithmic Hankel witness or a no-go for other Gram representations.
No positivity or contractivity of the complete cleared coefficient matrix is asserted here.
-/

open MeasureTheory Set Filter Topology
namespace RHTower
noncomputable section

/-- Every positive source window gives a geometric lower bound valid at every moment order. -/
theorem thetaCuspRawEvenMoment_lower_window
    {A : ℝ} (hA : 0 ≤ A) (n : ℕ) :
    2 * thetaCuspFullSource (A + 1) * A ^ (2 * n) ≤ thetaCuspRawEvenMoment n := by
  let c := thetaCuspFullSource (A + 1) * A ^ (2 * n)
  have hsubset : Ioc A (A + 1) ⊆ Ioi (0 : ℝ) := by
    intro x hx
    exact lt_of_le_of_lt hA hx.1
  have hpoint : ∀ x ∈ Ioc A (A + 1),
      c ≤ x ^ (2 * n) * thetaCuspFullSource x := by
    intro x hx
    have hx0 : 0 ≤ x := (hA.trans hx.1.le)
    have hphi := (strictAntiOn_thetaCuspFullSource_mul_reflect 0).antitoneOn
      hx0 (by linarith : (0 : ℝ) ≤ A + 1) hx.2
    simp only [zero_add, zero_sub, thetaCuspFullSource_neg] at hphi
    have hpA := (thetaCuspFullSource_pos_all (A + 1)).le
    have hpx := (thetaCuspFullSource_pos_all x).le
    have hphile : thetaCuspFullSource (A + 1) ≤ thetaCuspFullSource x := by
      nlinarith
    have hpow := pow_le_pow_left₀ hA hx.1.le (2 * n)
    dsimp [c]
    calc
      thetaCuspFullSource (A + 1) * A ^ (2 * n) ≤
          thetaCuspFullSource x * x ^ (2 * n) :=
        mul_le_mul hphile hpow (pow_nonneg hA _) hpx
      _ = _ := by ring
  have hcint : IntegrableOn (fun _x : ℝ => c) (Ioc A (A + 1)) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    exact continuous_const.intervalIntegrable _ _
  have hfint := integrableOn_thetaCuspRawMoment (2 * n)
  have hloc := setIntegral_mono_on hcint (hfint.mono_set hsubset)
    measurableSet_Ioc hpoint
  have hc : (∫ _x in Ioc A (A + 1), c) = c := by
    rw [setIntegral_const]
    simp
  rw [hc] at hloc
  have hwhole : (∫ x in Ioc A (A + 1), x ^ (2 * n) * thetaCuspFullSource x) ≤
      ∫ x in Ioi 0, x ^ (2 * n) * thetaCuspFullSource x := by
    apply setIntegral_mono_set hfint
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_nonneg (pow_nonneg hx.le _) (thetaCuspFullSource_pos_of_pos hx).le
    · exact Filter.Eventually.of_forall hsubset
  unfold thetaCuspRawEvenMoment
  dsimp [c] at hloc
  linarith

/-- The actual raw theta moments admit no fixed geometric upper envelope. -/
theorem thetaCuspRawEvenMoment_no_geometric_upper_bound (C R : ℝ) (hR : 0 ≤ R) :
    ¬ ∀ n : ℕ, thetaCuspRawEvenMoment n ≤ C * R ^ n := by
  intro h
  let A := R + 2
  let c := 2 * thetaCuspFullSource (A + 1)
  have hA : 0 < A := by dsimp [A]; linarith
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos (by norm_num) (thetaCuspFullSource_pos_all _)
  have hAsq : 0 < A ^ 2 := pow_pos hA _
  have hRA : R < A ^ 2 := by
    dsimp [A]
    nlinarith [sq_nonneg R]
  have hq0 : 0 ≤ R / A ^ 2 := div_nonneg hR hAsq.le
  have hq1 : R / A ^ 2 < 1 := (div_lt_one hAsq).2 hRA
  have hlim : Tendsto (fun n : ℕ => C * (R / A ^ 2) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul C
  have hlow (n : ℕ) : c ≤ C * (R / A ^ 2) ^ n := by
    have hn := (thetaCuspRawEvenMoment_lower_window hA.le n).trans (h n)
    have hp : 0 < (A ^ 2) ^ n := pow_pos hAsq n
    have hn' : c * (A ^ 2) ^ n ≤ C * R ^ n := by
      simpa only [c, pow_mul] using hn
    calc
      c = (c * (A ^ 2) ^ n) / (A ^ 2) ^ n := by field_simp
      _ ≤ (C * R ^ n) / (A ^ 2) ^ n :=
        (div_le_div_iff_of_pos_right hp).2 hn'
      _ = C * (R / A ^ 2) ^ n := by rw [div_pow]; ring
  obtain ⟨n, hn⟩ := (hlim.eventually_lt_const hc).exists
  exact (not_lt_of_ge (hlow n)) hn

/-- Positive distant source windows and log-convexity force every fixed raw-moment ratio bound
to fail eventually. This holds for the complete source without any hypothesis about Xi zeros. -/
theorem tendsto_thetaCuspRawEvenMoment_ratio_atTop :
    Tendsto (fun n : ℕ => thetaCuspRawEvenMoment (n + 1) / thetaCuspRawEvenMoment n)
      atTop atTop := by
  apply tendsto_atTop_atTop_of_monotone
    (monotone_nat_of_le_succ thetaCuspRawEvenMoment_ratio_mono)
  intro b
  by_contra h
  push Not at h
  let R : ℝ := max b 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hstep (n : ℕ) : thetaCuspRawEvenMoment (n + 1) ≤ R * thetaCuspRawEvenMoment n := by
    apply (div_le_iff₀ (thetaCuspRawEvenMoment_pos n)).1
    exact (h n).le.trans (le_max_left _ _)
  apply thetaCuspRawEvenMoment_no_geometric_upper_bound (thetaCuspRawEvenMoment 0) R hR
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      thetaCuspRawEvenMoment (n + 1) ≤ R * thetaCuspRawEvenMoment n := hstep n
      _ ≤ R * (thetaCuspRawEvenMoment 0 * R ^ n) :=
        mul_le_mul_of_nonneg_left ih hR
      _ = thetaCuspRawEvenMoment 0 * R ^ (n + 1) := by rw [pow_succ]; ring

/-- Explicit raw-moment expression for sign-adjusted cleared row `1`, column `n+1`. -/
def thetaCuspClearedOddGramRow (n : ℕ) : ℝ :=
  thetaCuspNormalizedEvenMoment (n + 3) / (2 * n + 5).factorial +
    (n + 1) * thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment (n + 2) /
      (2 * n + 4).factorial

/-- Row `1`, column `n+1` of the literal odd-monomial source Gram matrix. -/
def thetaCuspOddRawGramRow (n : ℕ) : ℝ :=
  thetaCuspNormalizedEvenMoment (n + 3) / (6 * (2 * n + 3).factorial)

/-- Exact difference after clearing a strictly positive factorial denominator. -/
theorem thetaCuspOddRawGramRow_sub_cleared (n : ℕ) :
    3 * ((2 * n + 5).factorial : ℝ) *
        (thetaCuspOddRawGramRow n - thetaCuspClearedOddGramRow n) =
      (n + 1) * ((2 * n + 7) * thetaCuspNormalizedEvenMoment (n + 3) -
        3 * (2 * n + 5) * thetaCuspNormalizedEvenMoment 1 *
          thetaCuspNormalizedEvenMoment (n + 2)) := by
  have hf : (0 : ℝ) < (2 * n + 3).factorial := by exact_mod_cast Nat.factorial_pos _
  have hf4 : ((2 * n + 4).factorial : ℝ) =
      (2 * n + 4) * (2 * n + 3).factorial := by
    rw [show 2 * n + 4 = (2 * n + 3) + 1 by omega, Nat.factorial_succ]
    push_cast
    ring
  have hf5 : ((2 * n + 5).factorial : ℝ) =
      (2 * n + 5) * ((2 * n + 4) * (2 * n + 3).factorial) := by
    rw [show 2 * n + 5 = (2 * n + 4) + 1 by omega, Nat.factorial_succ]
    push_cast
    rw [hf4]
    ring
  unfold thetaCuspOddRawGramRow thetaCuspClearedOddGramRow
  rw [hf5, hf4]
  have h4 : (2 * (n : ℝ) + 4) ≠ 0 := by positivity
  have h5 : (2 * (n : ℝ) + 5) ≠ 0 := by positivity
  field_simp [hf.ne', h4, h5]
  ring

/-- The complete source gives a strictly positive row deficit at every sufficiently large
column. This is an entrywise assertion, not an inequality between quadratic forms. -/
theorem eventually_thetaCuspOddRawGramRow_gt_cleared :
    ∀ᶠ n : ℕ in atTop, thetaCuspClearedOddGramRow n < thetaCuspOddRawGramRow n := by
  have hlim := tendsto_thetaCuspRawEvenMoment_ratio_atTop.comp (tendsto_add_atTop_nat 2)
  have hm0 := thetaCuspRawEvenMoment_pos 0
  have hμ1 : 0 < thetaCuspNormalizedEvenMoment 1 :=
    div_pos (thetaCuspRawEvenMoment_pos 1) hm0
  have he := hlim.eventually (eventually_gt_atTop (3 * thetaCuspNormalizedEvenMoment 1))
  filter_upwards [he] with n hn
  change 3 * thetaCuspNormalizedEvenMoment 1 <
    thetaCuspRawEvenMoment (n + 2 + 1) / thetaCuspRawEvenMoment (n + 2) at hn
  have hμn : 0 < thetaCuspNormalizedEvenMoment (n + 2) :=
    div_pos (thetaCuspRawEvenMoment_pos _) hm0
  have hμs : 0 < thetaCuspNormalizedEvenMoment (n + 3) :=
    div_pos (thetaCuspRawEvenMoment_pos _) hm0
  have hrec : 3 * thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment (n + 2) <
      thetaCuspNormalizedEvenMoment (n + 3) := by
    have hp := (lt_div_iff₀ (thetaCuspRawEvenMoment_pos (n + 2))).1 hn
    have hd := (div_lt_div_iff_of_pos_right hm0).2 hp
    simpa only [thetaCuspNormalizedEvenMoment, Nat.add_assoc, mul_div_assoc] using hd
  have hnum : 0 < (2 * (n : ℝ) + 7) * thetaCuspNormalizedEvenMoment (n + 3) -
      3 * (2 * n + 5) * thetaCuspNormalizedEvenMoment 1 *
        thetaCuspNormalizedEvenMoment (n + 2) := by
    have hpos := mul_pos (by positivity : 0 < 2 * (n : ℝ) + 5) (sub_pos.mpr hrec)
    nlinarith
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have h := thetaCuspOddRawGramRow_sub_cleared n
  have hprod : 0 < 3 * ((2 * n + 5).factorial : ℝ) *
      (thetaCuspOddRawGramRow n - thetaCuspClearedOddGramRow n) := by
    rw [h]
    exact mul_pos hn1 hnum
  have hf : (0 : ℝ) < 3 * (2 * n + 5).factorial := by positivity
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hf).1 hprod)

/-- The literal odd source Gram row cannot be the cleared logarithmic-moment row in every
degree. Other Gram representations and the full Hankel sign remain open. -/
theorem not_thetaCuspClearedOddGramRow_eq_raw :
    ¬ ∀ n : ℕ, thetaCuspClearedOddGramRow n = thetaCuspOddRawGramRow n := by
  intro h
  obtain ⟨n, hn⟩ := eventually_thetaCuspOddRawGramRow_gt_cleared.exists
  exact (ne_of_lt hn) (h n)

end
end RHTower
