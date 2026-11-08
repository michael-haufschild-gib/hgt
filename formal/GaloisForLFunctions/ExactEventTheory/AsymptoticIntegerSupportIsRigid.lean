import GaloisForLFunctions.ArithmeticPositiveDuality.IntegrableDefectsAtUnitDensityAreRigid

/-!
# Asymptotic integer support is rigid

An integrable uncompleted Riemann functional-equation defect cannot coexist with a nontrivial
displacement of a positive spectrum that approaches the integer lattice. The finite initial
segment disappears in Abel averaging; the remaining phase error is arbitrarily small relative
to the Abel mass. Thus the unit atom fixes the pole residue, and unit-density rigidity applies.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.FreqHamburger
open GaloisForLFunctions.ArithmeticPositiveDuality RHTower.HamburgerStability

noncomputable section
namespace GaloisForLFunctions.ExactEventTheory

/-- A small phase defect beyond a finite index controls the full Abel gap. -/
theorem abelCos_gap_le_of_tail_phase {a lam : ℕ → ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (hlam : ∀ n, 1 ≤ lam n)
    (ha : Summable fun n => a n / lam n ^ 2)
    {δ : ℝ} (hδ : 0 ≤ δ) (M : ℕ)
    (hphase : ∀ n, M ≤ n → 1 - Real.cos (2 * Real.pi * lam n) ≤ δ)
    {ε : ℝ} (hε : 0 < ε) :
    abelCos a lam 0 ε - abelCos a lam 1 ε ≤
      2 * ε * (∑ n ∈ Finset.range M, a n) + δ * abelCos a lam 0 ε := by
  let w : ℕ → ℝ := fun n => a n * Real.exp (-(2 * Real.pi * lam n * ε))
  let b : ℕ → ℝ := fun n => 1 - Real.cos (2 * Real.pi * lam n)
  have hw : ∀ n, 0 ≤ w n := fun n => mul_nonneg (ha0 n) (Real.exp_pos _).le
  have hwa : ∀ n, w n ≤ a n := by
    intro n
    apply mul_le_of_le_one_right (ha0 n)
    apply Real.exp_le_one_iff.mpr
    have hl : 0 ≤ lam n := zero_le_one.trans (hlam n)
    positivity
  have hb2 : ∀ n, b n ≤ 2 := fun n => by
    dsimp only [b]
    linarith only [Real.neg_one_le_cos (2 * Real.pi * lam n)]
  have sw : Summable w := summable_abelWeight hlam ha0 ha hε
  have sb : Summable fun n => w n * b n := by
    simpa only [mul_one] using summable_abelGap hlam ha0 ha 1 hε
  have swt : Summable fun n => w (n + M) :=
    sw.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have sbt : Summable fun n => w (n + M) * b (n + M) :=
    sb.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have htail : (∑' n, w (n + M) * b (n + M)) ≤ δ * ∑' n, w (n + M) := by
    rw [← tsum_mul_left]
    exact sbt.tsum_le_tsum (fun n => by
      have hh := mul_le_mul_of_nonneg_left (hphase (n + M) (Nat.le_add_left M n)) (hw (n + M))
      simpa only [mul_comm] using hh) (swt.mul_left δ)
  have hmass : (∑' n, w (n + M)) ≤ ∑' n, w n := by
    have hh := sw.sum_add_tsum_nat_add M
    have hp : 0 ≤ ∑ n ∈ Finset.range M, w n := Finset.sum_nonneg fun n _ => hw n
    linarith only [hh, hp]
  have hhead : (∑ n ∈ Finset.range M, w n * b n) ≤ 2 * ∑ n ∈ Finset.range M, a n := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    calc w n * b n ≤ w n * 2 := mul_le_mul_of_nonneg_left (hb2 n) (hw n)
      _ ≤ 2 * a n := by nlinarith only [hwa n]
  have hsum : (∑' n, w n * b n) ≤ 2 * (∑ n ∈ Finset.range M, a n) + δ * ∑' n, w n := by
    have hh := sb.sum_add_tsum_nat_add M
    have ht := mul_le_mul_of_nonneg_left hmass hδ
    linarith only [hh, hhead, htail, ht]
  rw [abelCos_zero_sub hlam ha0 ha 1 hε]
  simp only [mul_one]
  have hC0 : abelCos a lam 0 ε = ε * ∑' n, w n := by
    simp only [abelCos, mul_zero, Real.cos_zero, mul_one, w]
  rw [hC0]
  change ε * (∑' n, w n * b n) ≤
    2 * ε * (∑ n ∈ Finset.range M, a n) + δ * (ε * ∑' n, w n)
  have hh := mul_le_mul_of_nonneg_left hsum hε.le
  nlinarith only [hh]

/-- Asymptotic alignment with the integer lattice bounds the pole residue by the first mass. -/
theorem pole_residue_le_of_asymptotic_integer_support {a lam : ℕ → ℝ}
    (hmono : StrictMono lam) (hlam0 : lam 0 = 1) (ha0 : ∀ n, 0 ≤ a n)
    (ha : Summable fun n => a n / lam n ^ 2)
    (hphase : Tendsto (fun n => Real.cos (2 * Real.pi * lam n)) atTop (𝓝 1))
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g)
    (hθ : ∀ x : ℝ, 0 < x → freqTheta (fun n => (a n : ℂ)) lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta (fun n => (a n : ℂ)) lam x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    2 * β ≤ a 0 := by
  have hlam : ∀ n, 1 ≤ lam n := fun n => hlam0 ▸ hmono.monotone (Nat.zero_le n)
  have hpos : ∀ n, 0 < lam n := fun n => zero_lt_one.trans_le (hlam n)
  have haC : Summable fun n => ‖(a n : ℂ)‖ / lam n ^ 2 :=
    ha.congr fun n => by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha0 n)]
  have hL := fun z hz => freqSeries_eq_of_theta_defect ha0 hlam ha hgm hgb hθ (z := z) hz
  obtain ⟨c, hc, hsep⟩ := exists_sep_of_strictMono hmono hpos 0
  have hres := tendsto_mul_freqSeries_atom (a := fun n => (a n : ℂ)) hlam haC rfl
    (hpos 0) hc hsep
  have hC1 := abel_limit_of_defective_series ha0 hlam ha hgm hgb hgi hL (hpos 0) hres
  have hre : ((a 0 : ℂ) / (2 * Real.pi)).re = a 0 / (2 * Real.pi) := by
    rw [show ((a 0 : ℂ) / (2 * Real.pi)) = ((a 0 / (2 * Real.pi) : ℝ) : ℂ) by
      push_cast; ring, Complex.ofReal_re]
  rw [hlam0, hre] at hC1
  have hC0 := tendsto_abelCos_zero_of_theta_defect ha0 hlam ha hgm hgb hgi hθ
  have hgap : ∀ δ : ℝ, 0 < δ → β / Real.pi - a 0 / (2 * Real.pi) ≤ δ * (β / Real.pi) := by
    intro δ hδ
    obtain ⟨M, hM⟩ := eventually_atTop.mp (hphase.eventually_const_lt (by linarith : 1 - δ < 1))
    have hb : ∀ n, M ≤ n → 1 - Real.cos (2 * Real.pi * lam n) ≤ δ := by
      intro n hn
      linarith only [hM n hn]
    have hhead : Tendsto (fun ε : ℝ => 2 * ε * (∑ n ∈ Finset.range M, a n))
        (𝓝[>] 0) (𝓝 0) := by
      simpa using ((by fun_prop : Continuous fun ε : ℝ =>
        2 * ε * (∑ n ∈ Finset.range M, a n)).tendsto 0).mono_left nhdsWithin_le_nhds
    have hright := hhead.add (hC0.const_mul δ)
    simp only [zero_add] at hright
    apply le_of_tendsto_of_tendsto (hC0.sub hC1) hright
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact abelCos_gap_le_of_tail_phase ha0 hlam ha hδ.le M hb hε
  have hzero : β / Real.pi - a 0 / (2 * Real.pi) ≤ 0 := by
    have hlim : Tendsto (fun δ : ℝ => δ * (β / Real.pi)) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((by fun_prop : Continuous fun δ : ℝ => δ * (β / Real.pi)).tendsto 0
        ).mono_left nhdsWithin_le_nhds
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hgap δ hδ
  have hdiv : β / Real.pi ≤ a 0 / (2 * Real.pi) := sub_nonpos.mp hzero
  rw [div_le_div_iff₀ Real.pi_pos (by positivity)] at hdiv
  have hh : (2 * β) * Real.pi ≤ a 0 * Real.pi := by nlinarith only [hdiv]
  exact (mul_le_mul_iff_left₀ Real.pi_pos).mp hh

/-- Vanishing displacement from the integer lattice is already exact rigidity in the integrable
FE-defect class; no displacement rate or defect-size bound is required. -/
theorem integer_spectrum_of_asymptotic_integer_support {a lam : ℕ → ℝ}
    (hmono : StrictMono lam) (hlam0 : lam 0 = 1) (ha1 : ∀ n, 1 ≤ a n) (haunit : a 0 = 1)
    (ha : Summable fun n => a n / lam n ^ 2)
    (hphase : Tendsto (fun n => Real.cos (2 * Real.pi * lam n)) atTop (𝓝 1))
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g)
    (hθ : ∀ x : ℝ, 0 < x → freqTheta (fun n => (a n : ℂ)) lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta (fun n => (a n : ℂ)) lam x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    β = 1 / 2 ∧ ∀ n, lam n = n + 1 ∧ a n = 1 := by
  have hb := pole_residue_le_of_asymptotic_integer_support hmono hlam0
    (fun n => zero_le_one.trans (ha1 n)) ha hphase hgm hgb hgi hθ
  rw [haunit] at hb
  exact integer_spectrum_of_integrable_theta_defect hmono hlam0 ha1 ha
    (by linarith only [hb]) hgm hgb hgi hθ

end GaloisForLFunctions.ExactEventTheory

#print axioms GaloisForLFunctions.ExactEventTheory.integer_spectrum_of_asymptotic_integer_support
