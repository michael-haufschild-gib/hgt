import GaloisForLFunctions.EulerFETransportTheory.FiniteEnergyDefectsHaveNoBoundaryResidues
import GaloisForLFunctions.ExactEventTheory.IntegerSupportForcesExactArithmetic

/-!
# Finite-energy defects preserve the atomic Abel residues

The actual Laplace identity transfers every atomic residue to its Abel cosine mean.
Integer support makes the means at zero and one identical. A unit first atom then
fixes the pole coefficient, and positivity forces every atomic mass to be one.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.FreqHamburger
open GaloisForLFunctions.ArithmeticPositiveDuality RHTower.HamburgerStability

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-- At a positive height, the actual Laplace identity preserves the atomic residue. -/
theorem abel_limit_of_finiteEnergy_series {a lam : ℕ → ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (hlam : ∀ n, 1 ≤ lam n)
    (ha : Summable fun n => a n / lam n ^ 2) {β : ℂ}
    {g : ℝ → ℂ} (hg : MemLp g 2 (volume : Measure ℝ))
    (hL : ∀ z : ℂ, 0 < z.re →
      freqSeries (fun n => (a n : ℂ)) lam z = freqDual (fun n => (a n : ℂ)) lam z +
        -β / (Real.pi * z) + β + defectLaplace g z)
    {y : ℝ} (hy : 0 < y) {w : ℂ}
    (hres : Tendsto (fun ε : ℝ => (ε : ℂ) * freqSeries (fun n => (a n : ℂ)) lam
      ((ε : ℂ) + (y : ℂ) * I)) (𝓝[>] 0) (𝓝 w)) :
    Tendsto (abelCos a lam y) (𝓝[>] 0) (𝓝 w.re) := by
  have hy0 : (y : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hy.ne') I_ne_zero
  have hcont : ContinuousAt (fun ε : ℝ => (ε : ℂ) * β /
      (Real.pi * ((ε : ℂ) + (y : ℂ) * I)) - (ε : ℂ) * β) 0 := by
    refine (ContinuousAt.div (by fun_prop) (by fun_prop) ?_).sub (by fun_prop)
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simpa using mul_ne_zero hp hy0
  have hlin : Tendsto (fun ε : ℝ => (ε : ℂ) * β /
      (Real.pi * ((ε : ℂ) + (y : ℂ) * I)) - (ε : ℂ) * β) (𝓝[>] 0) (𝓝 0) := by
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  apply tendsto_abelCos_of_tendsto hlam ha0 ha
  have hh := (hres.add hlin).sub (tendsto_mul_finiteEnergy_defectLaplace hg y)
  simp only [add_zero, sub_zero] at hh
  refine hh.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [hL _ (by simpa using hε)]
  ring

/-- The zero-height Abel residue is exactly the pole coefficient. -/
theorem tendsto_mul_freqDual_zero_of_finiteEnergy_theta_defect {a lam : ℕ → ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (hlam : ∀ n, 1 ≤ lam n)
    (ha : Summable fun n => a n / lam n ^ 2) {β : ℂ}
    {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hg : MemLp g 2 (volume : Measure ℝ))
    (hθ : ∀ x : ℝ, 0 < x → freqTheta (fun n => (a n : ℂ)) lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta (fun n => (a n : ℂ)) lam x⁻¹ +
        -β + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * freqDual (fun n => (a n : ℂ)) lam (ε : ℂ))
      (𝓝[>] 0) (𝓝 (β / Real.pi)) := by
  have haC : Summable fun n => ‖(a n : ℂ)‖ / lam n ^ 2 :=
    ha.congr fun n => by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha0 n)]
  have hL := fun z hz => freqSeries_eq_of_theta_defect ha0 hlam ha hgm hgb hθ (z := z) hz
  have hres := tendsto_mul_freqSeries_ofReal (a := fun n => (a n : ℂ)) hlam haC
  have hlin : Tendsto (fun ε : ℝ => β / Real.pi - (ε : ℂ) * β)
      (𝓝[>] 0) (𝓝 (β / Real.pi)) := by
    have hc : Continuous (fun ε : ℝ => β / Real.pi - (ε : ℂ) * β) := by fun_prop
    simpa using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hh := (hres.add hlin).sub (tendsto_mul_finiteEnergy_defectLaplace hg 0)
  simp only [zero_add, sub_zero, Complex.ofReal_zero, zero_mul, add_zero] at hh
  refine hh.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have he : (ε : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hε)
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hL _ (by simpa using hε)]
  field_simp
  ring

theorem tendsto_abelCos_zero_of_finiteEnergy_theta_defect {a lam : ℕ → ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (hlam : ∀ n, 1 ≤ lam n)
    (ha : Summable fun n => a n / lam n ^ 2) {β : ℝ}
    {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hg : MemLp g 2 (volume : Measure ℝ))
    (hθ : ∀ x : ℝ, 0 < x → freqTheta (fun n => (a n : ℂ)) lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta (fun n => (a n : ℂ)) lam x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    Tendsto (abelCos a lam 0) (𝓝[>] 0) (𝓝 (β / Real.pi)) := by
  have hF := tendsto_mul_freqDual_zero_of_finiteEnergy_theta_defect ha0 hlam ha hgm hgb hg hθ
  have hF' : Tendsto (fun ε : ℝ => (ε : ℂ) * freqDual (fun n => (a n : ℂ)) lam
      ((ε : ℂ) + ((0 : ℝ) : ℂ) * I)) (𝓝[>] 0) (𝓝 ((β : ℂ) / Real.pi)) := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using hF
  have hh := tendsto_abelCos_of_tendsto hlam ha0 ha hF'
  simpa only [Complex.div_ofReal_re, Complex.ofReal_re] using hh

/-- Integer support identifies the zero-height Abel density with the first atom. -/
theorem finiteEnergy_integer_support_pins_pole_residue {a lam : ℕ → ℝ}
    (hmono : StrictMono lam) (hlam0 : lam 0 = 1)
    (hint : ∀ n, ∃ k : ℕ, lam n = k) (ha0 : ∀ n, 0 ≤ a n)
    (ha : Summable fun n => a n / lam n ^ 2) {β : ℝ}
    {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hg : MemLp g 2 (volume : Measure ℝ))
    (hθ : ∀ x : ℝ, 0 < x → freqTheta (fun n => (a n : ℂ)) lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta (fun n => (a n : ℂ)) lam x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    2 * β = a 0 := by
  have hlam : ∀ n, 1 ≤ lam n := fun n => hlam0 ▸ hmono.monotone (Nat.zero_le n)
  have hpos : ∀ n, 0 < lam n := fun n => zero_lt_one.trans_le (hlam n)
  have haC : Summable fun n => ‖(a n : ℂ)‖ / lam n ^ 2 :=
    ha.congr fun n => by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha0 n)]
  have hL := fun z hz => freqSeries_eq_of_theta_defect ha0 hlam ha hgm hgb hθ (z := z) hz
  obtain ⟨c, hc, hsep⟩ := exists_sep_of_strictMono hmono hpos 0
  have hres := tendsto_mul_freqSeries_atom (a := fun n => (a n : ℂ)) hlam haC rfl
    (hpos 0) hc hsep
  have hC1 := abel_limit_of_finiteEnergy_series ha0 hlam ha hg hL (hpos 0) hres
  have hC0 := tendsto_abelCos_zero_of_finiteEnergy_theta_defect ha0 hlam ha hgm hgb hg hθ
  have hperiod : abelCos a lam (lam 0) = abelCos a lam 0 := by
    funext ε
    unfold abelCos
    congr 1
    apply tsum_congr
    intro n
    obtain ⟨k, hk⟩ := hint n
    have hcos : Real.cos (2 * Real.pi * lam n * lam 0) = 1 := by
      rw [hlam0, mul_one, hk, show 2 * Real.pi * (k : ℝ) = (k : ℝ) * (2 * Real.pi) by ring]
      exact Real.cos_nat_mul_two_pi k
    rw [hcos, mul_zero, Real.cos_zero]
  rw [hperiod] at hC1
  have he := tendsto_nhds_unique hC0 hC1
  have hre : ((a 0 : ℂ) / (2 * Real.pi)).re = a 0 / (2 * Real.pi) := by
    rw [show ((a 0 : ℂ) / (2 * Real.pi)) = ((a 0 / (2 * Real.pi) : ℝ) : ℂ) by
      push_cast; ring, Complex.ofReal_re]
  rw [hre, div_eq_div_iff Real.pi_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero)] at he
  nlinarith only [he, Real.pi_pos]

/-- The unit first atom fixes the pole; positivity then fixes every atomic multiplicity. -/
theorem finiteEnergy_integer_atom_masses_eq_one {a lam : ℕ → ℝ}
    (hmono : StrictMono lam) (hlam0 : lam 0 = 1)
    (hint : ∀ n, ∃ k : ℕ, lam n = k) (ha1 : ∀ n, 1 ≤ a n) (haunit : a 0 = 1)
    (ha : Summable fun n => a n / lam n ^ 2) {β : ℝ}
    {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hg : MemLp g 2 (volume : Measure ℝ))
    (hθ : ∀ x : ℝ, 0 < x → freqTheta (fun n => (a n : ℂ)) lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta (fun n => (a n : ℂ)) lam x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    β = 1 / 2 ∧ ∀ n, a n = 1 := by
  have ha0 : ∀ n, 0 ≤ a n := fun n => zero_le_one.trans (ha1 n)
  have hβ := finiteEnergy_integer_support_pins_pole_residue hmono hlam0 hint ha0 ha hgm hgb hg hθ
  rw [haunit] at hβ
  have hb : β = 1 / 2 := by linarith only [hβ]
  refine ⟨hb, fun m => ?_⟩
  have hlam : ∀ n, 1 ≤ lam n := fun n => hlam0 ▸ hmono.monotone (Nat.zero_le n)
  have hpos : ∀ n, 0 < lam n := fun n => zero_lt_one.trans_le (hlam n)
  have haC : Summable fun n => ‖(a n : ℂ)‖ / lam n ^ 2 :=
    ha.congr fun n => by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha0 n)]
  have hL := fun z hz => freqSeries_eq_of_theta_defect ha0 hlam ha hgm hgb hθ (z := z) hz
  obtain ⟨c, hc, hsep⟩ := exists_sep_of_strictMono hmono hpos m
  have hres := tendsto_mul_freqSeries_atom (a := fun n => (a n : ℂ)) hlam haC rfl
    (hpos m) hc hsep
  have hatom := abel_limit_of_finiteEnergy_series ha0 hlam ha hg hL (hpos m) hres
  have hC0 := tendsto_abelCos_zero_of_finiteEnergy_theta_defect ha0 hlam ha hgm hgb hg hθ
  have hre : ((a m : ℂ) / (2 * Real.pi)).re = a m / (2 * Real.pi) := by
    rw [show ((a m : ℂ) / (2 * Real.pi)) = ((a m / (2 * Real.pi) : ℝ) : ℂ) by
      push_cast; ring, Complex.ofReal_re]
  rw [hre] at hatom
  have hmass : a m / (2 * Real.pi) ≤ β / Real.pi := by
    apply le_of_tendsto_of_tendsto hatom hC0
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact abelCos_le_of_le hlam ha0 ha hε fun n => by simpa using Real.cos_le_one _
  have ham : a m ≤ 2 * β := by
    rw [div_le_div_iff₀ (by positivity) Real.pi_pos] at hmass
    nlinarith only [hmass, Real.pi_pos]
  linarith only [ham, hβ, ha1 m]

/-- Integer support and a unit first atom determine the full spectrum. At a missing
integer the zero atomic residue contradicts the positive periodic Abel density. -/
theorem integer_spectrum_of_integer_support_finiteEnergy_defect {a lam : ℕ → ℝ}
    (hmono : StrictMono lam) (hlam0 : lam 0 = 1)
    (hint : ∀ n, ∃ k : ℕ, lam n = k) (ha1 : ∀ n, 1 ≤ a n) (haunit : a 0 = 1)
    (ha : Summable fun n => a n / lam n ^ 2) {β : ℝ}
    {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hg : MemLp g 2 (volume : Measure ℝ))
    (hθ : ∀ x : ℝ, 0 < x → freqTheta (fun n => (a n : ℂ)) lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta (fun n => (a n : ℂ)) lam x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    β = 1 / 2 ∧ ∀ n, lam n = n + 1 ∧ a n = 1 := by
  obtain ⟨hb, hunit⟩ := finiteEnergy_integer_atom_masses_eq_one
    hmono hlam0 hint ha1 haunit ha hgm hgb hg hθ
  have ha0 : ∀ n, 0 ≤ a n := fun n => zero_le_one.trans (ha1 n)
  have hlam : ∀ n, 1 ≤ lam n := fun n => hlam0 ▸ hmono.monotone (Nat.zero_le n)
  have hpos : ∀ n, 0 < lam n := fun n => zero_lt_one.trans_le (hlam n)
  have haC : Summable fun n => ‖(a n : ℂ)‖ / lam n ^ 2 :=
    ha.congr fun n => by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha0 n)]
  have hL := fun z hz => freqSeries_eq_of_theta_defect ha0 hlam ha hgm hgb hθ (z := z) hz
  have hC0 := tendsto_abelCos_zero_of_finiteEnergy_theta_defect ha0 hlam ha hgm hgb hg hθ
  have hsurj : ∀ k : ℕ, 1 ≤ k → ∃ n, lam n = k := by
    intro k hk
    by_contra hnone
    push Not at hnone
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hsep : ∀ n, 1 / (2 * k) * lam n ≤ |lam n - k| := by
      intro n
      obtain ⟨K, hKn⟩ := hint n
      have hne : K ≠ k := fun h => hnone n (by rw [hKn, h])
      have hdist : 1 ≤ |lam n - k| := by
        rw [hKn]
        rcases lt_or_gt_of_ne hne with h | h
        · have hle : (K : ℝ) + 1 ≤ k := by exact_mod_cast h
          rw [abs_of_neg (by linarith only [hle])]
          linarith only [hle]
        · have hle : (k : ℝ) + 1 ≤ K := by exact_mod_cast h
          rw [abs_of_pos (by linarith only [hle])]
          linarith only [hle]
      rcases le_or_gt (lam n) (2 * k) with h | h
      · calc
          1 / (2 * k) * lam n ≤ 1 / (2 * k) * (2 * k) :=
            mul_le_mul_of_nonneg_left h (by positivity)
          _ = 1 := by field_simp
          _ ≤ |lam n - k| := hdist
      · rw [abs_of_pos (by linarith only [h, hk0])]
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
        have hc : 1 / (2 * (k : ℝ)) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith only [hk1]
        have hm := mul_le_mul_of_nonneg_right hc (hpos n).le
        linarith only [hm, h]
    have hres := tendsto_mul_freqSeries_gap (a := fun n => (a n : ℂ))
      hlam haC hk0.le (show 0 < 1 / (2 * (k : ℝ)) by positivity) hsep
    have hCk : Tendsto (abelCos a lam k) (𝓝[>] 0) (𝓝 0) := by
      simpa only [Complex.zero_re] using
        abel_limit_of_finiteEnergy_series ha0 hlam ha hg hL hk0 hres
    have heq : abelCos a lam k = abelCos a lam 0 := by
      funext ε
      unfold abelCos
      congr 1
      apply tsum_congr
      intro n
      obtain ⟨K, hKn⟩ := hint n
      have hc : Real.cos (2 * Real.pi * lam n * k) = 1 := by
        rw [hKn, show 2 * Real.pi * (K : ℝ) * k = ((K * k : ℕ) : ℝ) * (2 * Real.pi) by
          push_cast; ring]
        exact Real.cos_nat_mul_two_pi _
      rw [hc, mul_zero, Real.cos_zero]
    rw [heq] at hCk
    have he := tendsto_nhds_unique hC0 hCk
    have hp : 0 < β / Real.pi := by rw [hb]; positivity
    linarith only [he, hp]
  have hval : ∀ n, lam n = n + 1 := by
    intro n
    induction n with
    | zero => simpa using hlam0
    | succ n ih =>
      obtain ⟨K, hK⟩ := hint (n + 1)
      have hlt : lam n < lam (n + 1) := hmono (Nat.lt_succ_self n)
      have hKge : n + 2 ≤ K := by
        rw [ih, hK] at hlt
        have hNat : n + 1 < K := by exact_mod_cast hlt
        omega
      obtain ⟨m, hm⟩ := hsurj (n + 2) (by omega)
      have hmn : n + 1 ≤ m := by
        by_contra h
        have hle : lam m ≤ lam n := hmono.monotone (by omega)
        rw [hm, ih] at hle
        push_cast at hle
        linarith only [hle]
      have hle : lam (n + 1) ≤ lam m := hmono.monotone hmn
      rw [hK, hm] at hle
      have hKle : K ≤ n + 2 := by exact_mod_cast hle
      rw [hK]
      have he : K = n + 2 := le_antisymm hKle hKge
      rw [he]
      push_cast
      ring
  exact ⟨hb, fun n => ⟨hval n, hunit n⟩⟩

end GaloisForLFunctions.EulerFETransportTheory

#print axioms GaloisForLFunctions.EulerFETransportTheory.tendsto_mul_freqDual_zero_of_finiteEnergy_theta_defect
#print axioms GaloisForLFunctions.EulerFETransportTheory.finiteEnergy_integer_support_pins_pole_residue
#print axioms GaloisForLFunctions.EulerFETransportTheory.finiteEnergy_integer_atom_masses_eq_one
#print axioms GaloisForLFunctions.EulerFETransportTheory.integer_spectrum_of_integer_support_finiteEnergy_defect
