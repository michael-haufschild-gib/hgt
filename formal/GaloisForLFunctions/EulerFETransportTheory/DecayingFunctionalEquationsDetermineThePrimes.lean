import GaloisForLFunctions.EulerFETransportTheory.DecayingDefectsForceIntegerSupport
import GaloisForLFunctions.EulerFETransportTheory.IntegrableFunctionalEquationsDetermineThePrimes
import GaloisForLFunctions.RHTower.WeilFractionalMassPolynomialTailRigidity
import GaloisForLFunctions.EulerFETransportTheory.UnequalCoefficientsFloorTheAbelMass
import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.IntegerNormFakesHavePositiveDensity

/-!
# Decaying functional-equation defects determine the rational primes

**Theorem II.1** (`beurlingSystem_rigidity_of_decaying_defect`).  Let `B` be a countable Beurling
system with `Σ_x |x|^{-3/2} < ∞` whose zeta function lies in the Hamburger strip class with a
critical-line FE defect `‖g(t)‖ ≤ C (1 + |t|)^{-1/2 + ε₀}`, `ε₀ < 1/2`.  Then `β = 1/2`,
`ζ_B = ζ` on `Re s > 1`, and the generators of `B` are norm-equivalent to the rational primes.  In
particular no such system has a fake zero.

The defect need not be integrable or square integrable.  The pole coefficient is real
(`tendsto_mul_defectLaplace_zero`), the norms are integers (`beurling_intNorm_nat_of_decaying_theta_defect`),
and a decaying defect is Abel-sublinear, so it changes no radial residue
(`tendsto_mul_defectLaplace_of_decay`); the residue argument of the integrable case then fixes
every multiplicity at one.
-/

open Complex MeasureTheory Filter Topology Set Function
open RHTower.HamburgerStability
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.FreqHamburger
open GaloisForLFunctions.ExactEventTheory GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-! ## Radial residues of a decaying defect -/

theorem tendsto_mul_abelMass_of_decay {g : ℝ → ℂ} (hgm : Measurable g) {C a : ℝ} (ha : 0 < a)
    (hgd : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ (-a)) :
    Tendsto (fun δ => δ * abelMass g δ) (𝓝[>] 0) (𝓝 0) := by
  have hC := nonneg_of_decay hgd
  refine RHTower.FractionalMassPolynomialTailRigidity.tendsto_mul_abelMass_of_tendsto_zero
    (M := C) (fun t => by simpa using poly_of_decay ha.le hgd t) hgm.aestronglyMeasurable
    fun ε hε => ⟨(C / ε) ^ (1 / a), by positivity, fun t ht => ?_⟩
  refine (hgd t).trans ?_
  have hpos : 0 < 1 + |t| := by positivity
  have hle : (C / ε) ^ (1 / a) ≤ 1 + |t| := by linarith
  have hpow : C / ε ≤ (1 + |t|) ^ a := by
    calc C / ε = ((C / ε) ^ (1 / a)) ^ a := by
          rw [← Real.rpow_mul (by positivity), one_div_mul_cancel ha.ne', Real.rpow_one]
      _ ≤ (1 + |t|) ^ a := Real.rpow_le_rpow (by positivity) hle ha.le
  rw [Real.rpow_neg hpos.le, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ hε] at hpow
  linarith

/-- **A decaying defect changes no radial residue**: `ε J_g(ε + iy) → 0` for every real `y`. -/
theorem tendsto_mul_defectLaplace_of_decay {g : ℝ → ℂ} (hgm : Measurable g) {C a : ℝ}
    (ha : 0 < a) (hgd : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ (-a)) (y : ℝ) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * defectLaplace g ((ε : ℂ) + (y : ℂ) * I)) (𝓝[>] 0) (𝓝 0) := by
  have hgb := poly_of_decay ha.le hgd
  have hA := tendsto_mul_abelMass_of_decay hgm ha hgd
  rcases eq_or_ne y 0 with hy | hy
  · subst hy
    simpa using tendsto_mul_defectLaplace_radial hgm.aestronglyMeasurable hgb hA 0
  have hpi := Real.pi_pos
  have hy0 : 0 < |y| := abs_pos.mpr hy
  set κ : ℝ := |y| + 1 with hκ
  have hκ0 : 0 < κ := by positivity
  have hmap : Tendsto (fun ε : ℝ => 2 * ε / κ) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun ε hε =>
      div_pos (mul_pos two_pos hε) hκ0⟩
    simpa using (((continuous_const.mul continuous_id).div_const κ).tendsto (0 : ℝ)
      (f := fun ε : ℝ => 2 * ε / κ)).mono_left nhdsWithin_le_nhds
  have hA' := hA.comp hmap
  refine squeeze_zero_norm'
    (a := fun ε : ℝ => 3 / (2 * Real.pi) * |y| ^ (-(1 / 2 : ℝ)) * (κ / 2) *
      (2 * ε / κ * abelMass g (2 * ε / κ))) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with ε hε hε1
    have hε' : 0 < ε := hε
    set τ : ℂ := (ε : ℂ) + (y : ℂ) * I with hτ
    have hre : τ.re = ε := by simp [hτ]
    have hτre : 0 < τ.re := by rw [hre]; exact hε'
    have hb := norm_defectLaplace_le hgm.aestronglyMeasurable hgb hτre
    have hn1 : |y| ≤ ‖τ‖ := by
      have := Complex.abs_im_le_norm τ
      simpa [hτ] using this
    have hn2 : ‖τ‖ ≤ κ := by
      have h := norm_add_le (ε : ℂ) ((y : ℂ) * I)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε', norm_mul, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_I, mul_one] at h
      have := hε1.2
      rw [hκ]
      linarith
    have hτ0 : 0 < ‖τ‖ := lt_of_lt_of_le hy0 hn1
    have hpow : ‖τ‖ ^ (-(1 / 2 : ℝ)) ≤ |y| ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hy0 hn1 (by norm_num)
    have hmass : abelMass g (2 * (τ.re / ‖τ‖)) ≤ abelMass g (2 * ε / κ) := by
      refine abelMass_antitone hgm.aestronglyMeasurable hgb (by positivity) ?_
      rw [hre, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hε'.le hτ0 hn2) (by norm_num)
    have hmass0 : 0 ≤ abelMass g (2 * (τ.re / ‖τ‖)) :=
      integral_nonneg fun t => by positivity
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε']
    calc ε * ‖defectLaplace g τ‖
        ≤ ε * (3 / (2 * Real.pi) * |y| ^ (-(1 / 2 : ℝ)) * abelMass g (2 * ε / κ)) := by
          gcongr
          exact hb.trans (mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity)) hmass
            hmass0 (by positivity))
      _ = 3 / (2 * Real.pi) * |y| ^ (-(1 / 2 : ℝ)) * (κ / 2) *
            (2 * ε / κ * abelMass g (2 * ε / κ)) := by field_simp
  · have := hA'.const_mul (3 / (2 * Real.pi) * |y| ^ (-(1 / 2 : ℝ)) * (κ / 2))
    rw [mul_zero] at this
    exact this

/-! ## Residue-free defects fix the integer spectrum -/

section ResidueFree

variable {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ}

/-- At a positive height a residue-free defect leaves the atomic Abel residue unchanged. -/
theorem abel_limit_of_residueFree {a lam : ℕ → ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (hlam : ∀ n, 1 ≤ lam n)
    (ha : Summable fun n => a n / lam n ^ 2) {β : ℂ}
    (hres : ∀ y : ℝ, Tendsto (fun ε : ℝ => (ε : ℂ) * defectLaplace g ((ε : ℂ) + (y : ℂ) * I))
      (𝓝[>] 0) (𝓝 0))
    (hL : ∀ z : ℂ, 0 < z.re →
      freqSeries (fun n => (a n : ℂ)) lam z = freqDual (fun n => (a n : ℂ)) lam z +
        -β / (Real.pi * z) + β + defectLaplace g z)
    {y : ℝ} (hy : 0 < y) {w : ℂ}
    (hw : Tendsto (fun ε : ℝ => (ε : ℂ) * freqSeries (fun n => (a n : ℂ)) lam
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
  have hh := (hw.add hlin).sub (hres y)
  simp only [add_zero, sub_zero] at hh
  refine hh.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [hL _ (by simpa using hε)]
  ring

/-- The radial Abel limit recovers the pole coefficient. -/
theorem tendsto_mul_freqDual_of_residueFree {a lam : ℕ → ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (hlam : ∀ n, 1 ≤ lam n)
    (ha : Summable fun n => a n / lam n ^ 2) {β : ℂ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    (hres : ∀ y : ℝ, Tendsto (fun ε : ℝ => (ε : ℂ) * defectLaplace g ((ε : ℂ) + (y : ℂ) * I))
      (𝓝[>] 0) (𝓝 0))
    (hθ : ∀ x : ℝ, 0 < x → freqTheta (fun n => (a n : ℂ)) lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta (fun n => (a n : ℂ)) lam x⁻¹ +
        -β + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * freqDual (fun n => (a n : ℂ)) lam (ε : ℂ))
      (𝓝[>] 0) (𝓝 (β / Real.pi)) := by
  have haC : Summable fun n => ‖(a n : ℂ)‖ / lam n ^ 2 :=
    ha.congr fun n => by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha0 n)]
  have hL := fun z hz => freqSeries_eq_of_theta_defect ha0 hlam ha hgm hgb hθ (z := z) hz
  have hw := tendsto_mul_freqSeries_ofReal (a := fun n => (a n : ℂ)) hlam haC
  have hlin : Tendsto (fun ε : ℝ => β / Real.pi - (ε : ℂ) * β)
      (𝓝[>] 0) (𝓝 (β / Real.pi)) := by
    simpa using ((by fun_prop : Continuous fun ε : ℝ =>
      β / Real.pi - (ε : ℂ) * β).tendsto 0).mono_left nhdsWithin_le_nhds
  have hh := (hw.add hlin).sub (hres 0)
  simp only [zero_add, sub_zero, Complex.ofReal_zero, zero_mul, add_zero] at hh
  refine hh.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have he : (ε : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hε)
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hL _ (by simpa using hε)]
  field_simp
  ring

theorem tendsto_abelCos_zero_of_residueFree {a lam : ℕ → ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (hlam : ∀ n, 1 ≤ lam n)
    (ha : Summable fun n => a n / lam n ^ 2) {β : ℝ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    (hres : ∀ y : ℝ, Tendsto (fun ε : ℝ => (ε : ℂ) * defectLaplace g ((ε : ℂ) + (y : ℂ) * I))
      (𝓝[>] 0) (𝓝 0))
    (hθ : ∀ x : ℝ, 0 < x → freqTheta (fun n => (a n : ℂ)) lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta (fun n => (a n : ℂ)) lam x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    Tendsto (abelCos a lam 0) (𝓝[>] 0) (𝓝 (β / Real.pi)) := by
  have hF := tendsto_mul_freqDual_of_residueFree ha0 hlam ha hgm hgb hres hθ
  have hF' : Tendsto (fun ε : ℝ => (ε : ℂ) * freqDual (fun n => (a n : ℂ)) lam
      ((ε : ℂ) + ((0 : ℝ) : ℂ) * I)) (𝓝[>] 0) (𝓝 ((β : ℂ) / Real.pi)) := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using hF
  have hh := tendsto_abelCos_of_tendsto hlam ha0 ha hF'
  simpa only [Complex.div_ofReal_re, Complex.ofReal_re] using hh

/-- Unit atoms on integer frequencies with the Abel limits of the integers fill the lattice:
a missing integer `k` would see the full density `1/(2π)` and the gap limit `0` at once. -/
theorem integer_spectrum_of_unit_abel_limits_of_int {a lam : ℕ → ℝ}
    (hmono : StrictMono lam) (hlam0 : lam 0 = 1) (hint : ∀ n, ∃ k : ℕ, lam n = k)
    (hunit : ∀ n, a n = 1)
    (hC0 : Tendsto (abelCos a lam 0) (𝓝[>] 0) (𝓝 (1 / (2 * Real.pi))))
    (hgap : ∀ τ c : ℝ, 0 < τ → 0 < c → (∀ n, c * lam n ≤ |lam n - τ|) →
      Tendsto (abelCos a lam τ) (𝓝[>] 0) (𝓝 0)) :
    ∀ n, lam n = n + 1 ∧ a n = 1 := by
  have hlam : ∀ n, 1 ≤ lam n := fun n => hlam0 ▸ hmono.monotone (Nat.zero_le n)
  have hpos : ∀ n, 0 < lam n := fun n => lt_of_lt_of_le one_pos (hlam n)
  -- every positive integer is a frequency
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
        · have : (K : ℝ) + 1 ≤ k := by exact_mod_cast h
          rw [abs_of_neg (by linarith)]; linarith
        · have : (k : ℝ) + 1 ≤ K := by exact_mod_cast h
          rw [abs_of_pos (by linarith)]; linarith
      rcases le_or_gt (lam n) (2 * k) with h | h
      · calc 1 / (2 * k) * lam n ≤ 1 / (2 * k) * (2 * k) :=
              mul_le_mul_of_nonneg_left h (by positivity)
          _ = 1 := by field_simp
          _ ≤ |lam n - k| := hdist
      · rw [abs_of_pos (by linarith)]
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
        have : 1 / (2 * (k : ℝ)) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        nlinarith [hpos n]
    have hCk := hgap k (1 / (2 * k)) hk0 (by positivity) hsep
    have heq : ∀ ε, abelCos a lam k ε = abelCos a lam 0 ε := by
      intro ε
      unfold abelCos
      congr 1
      refine tsum_congr fun n => ?_
      obtain ⟨K, hKn⟩ := hint n
      have : Real.cos (2 * Real.pi * lam n * k) = 1 := by
        rw [hKn, show 2 * Real.pi * (K : ℝ) * k = ((K * k : ℕ) : ℝ) * (2 * Real.pi) by
          push_cast; ring]
        exact Real.cos_nat_mul_two_pi _
      rw [this]; simp
    have : Tendsto (abelCos a lam k) (𝓝[>] 0) (𝓝 (1 / (2 * Real.pi))) := by
      rw [show abelCos a lam k = abelCos a lam 0 from funext heq]; exact hC0
    have := tendsto_nhds_unique this hCk
    have hπ2 : 0 < 1 / (2 * Real.pi) := by positivity
    linarith
  -- strict monotonicity pins `λ_n = n + 1`
  have hval : ∀ n, lam n = n + 1 := by
    intro n
    induction n with
    | zero => simp [hlam0]
    | succ n ih =>
      obtain ⟨K, hK⟩ := hint (n + 1)
      have hlt : lam n < lam (n + 1) := hmono (Nat.lt_succ_self n)
      have hKge : n + 2 ≤ K := by
        rw [ih, hK] at hlt
        have : (n : ℝ) + 1 < K := by linarith
        exact_mod_cast (show n + 1 < K by exact_mod_cast this)
      obtain ⟨m, hm⟩ := hsurj (n + 2) (by omega)
      have hmn : n + 1 ≤ m := by
        by_contra h
        push Not at h
        have : lam m ≤ lam n := hmono.monotone (by omega)
        rw [hm, ih] at this
        push_cast at this
        linarith
      have hle : lam (n + 1) ≤ lam m := hmono.monotone hmn
      rw [hK, hm] at hle
      have hKle : K ≤ n + 2 := by exact_mod_cast hle
      rw [hK]
      push_cast
      have : K = n + 2 := le_antisymm hKle hKge
      rw [this]; push_cast; ring
  exact fun n => ⟨hval n, hunit n⟩

/-- A residue-free defect cannot deform an integer spectrum whose pole residue is at most one. -/
theorem integer_spectrum_of_residueFree {a lam : ℕ → ℝ}
    (hmono : StrictMono lam) (hlam0 : lam 0 = 1) (hint : ∀ n, ∃ k : ℕ, lam n = k)
    (ha1 : ∀ n, 1 ≤ a n)
    (ha : Summable fun n => a n / lam n ^ 2) {β : ℝ} (hβ : β ≤ 1 / 2) (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    (hres : ∀ y : ℝ, Tendsto (fun ε : ℝ => (ε : ℂ) * defectLaplace g ((ε : ℂ) + (y : ℂ) * I))
      (𝓝[>] 0) (𝓝 0))
    (hθ : ∀ x : ℝ, 0 < x → freqTheta (fun n => (a n : ℂ)) lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta (fun n => (a n : ℂ)) lam x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    β = 1 / 2 ∧ ∀ n, lam n = n + 1 ∧ a n = 1 := by
  have hlam : ∀ n, 1 ≤ lam n := fun n => hlam0 ▸ hmono.monotone (Nat.zero_le n)
  have hpos : ∀ n, 0 < lam n := fun n => lt_of_lt_of_le one_pos (hlam n)
  have ha0 : ∀ n, 0 ≤ a n := fun n => le_trans zero_le_one (ha1 n)
  have haC : Summable fun n => ‖(a n : ℂ)‖ / lam n ^ 2 :=
    ha.congr fun n => by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha0 n)]
  have hL := fun z hz => freqSeries_eq_of_theta_defect ha0 hlam ha hgm hgb hθ (z := z) hz
  have hC0 := tendsto_abelCos_zero_of_residueFree ha0 hlam ha hgm hgb hres hθ
  have hatom : ∀ m, Tendsto (abelCos a lam (lam m)) (𝓝[>] 0)
      (𝓝 (a m / (2 * Real.pi))) := by
    intro m
    obtain ⟨c, hc, hsep⟩ := exists_sep_of_strictMono hmono hpos m
    have hw := tendsto_mul_freqSeries_atom (a := fun n => (a n : ℂ)) hlam haC rfl
      (hpos m) hc hsep
    have hh := abel_limit_of_residueFree ha0 hlam ha hres hL (hpos m) hw
    have hre : ((a m : ℂ) / (2 * Real.pi)).re = a m / (2 * Real.pi) := by
      rw [show ((a m : ℂ) / (2 * Real.pi)) = ((a m / (2 * Real.pi) : ℝ) : ℂ) by
        push_cast; ring, Complex.ofReal_re]
    rwa [hre] at hh
  have hmass : ∀ m, a m ≤ 2 * β := by
    intro m
    have hh : a m / (2 * Real.pi) ≤ β / Real.pi := by
      refine le_of_tendsto_of_tendsto (hatom m) hC0 ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact abelCos_le_of_le hlam ha0 ha hε fun n => by simpa using Real.cos_le_one _
    have hp := Real.pi_pos
    rw [div_le_div_iff₀ (by positivity) hp] at hh
    nlinarith only [hh, hp]
  have hb : β = 1 / 2 := by linarith only [hmass 0, ha1 0, hβ]
  refine ⟨hb, integer_spectrum_of_unit_abel_limits_of_int hmono hlam0 hint
    (fun m => by linarith only [hmass m, ha1 m, hβ]) ?_ ?_⟩
  · have hratio : β / Real.pi = 1 / (2 * Real.pi) := by rw [hb]; ring
    rwa [hratio] at hC0
  · intro y c hy hc hsep
    have hw := tendsto_mul_freqSeries_gap (a := fun n => (a n : ℂ)) hlam haC hy.le hc hsep
    simpa using abel_limit_of_residueFree ha0 hlam ha hres hL hy hw

/-- The unit period of integer support identifies the Abel density with the first atom. -/
theorem integer_support_pins_pole_residue_of_residueFree {a lam : ℕ → ℝ}
    (hmono : StrictMono lam) (hlam0 : lam 0 = 1)
    (hint : ∀ n, ∃ k : ℕ, lam n = k) (ha0 : ∀ n, 0 ≤ a n)
    (ha : Summable fun n => a n / lam n ^ 2) {β : ℝ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    (hres : ∀ y : ℝ, Tendsto (fun ε : ℝ => (ε : ℂ) * defectLaplace g ((ε : ℂ) + (y : ℂ) * I))
      (𝓝[>] 0) (𝓝 0))
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
  have hw := tendsto_mul_freqSeries_atom (a := fun n => (a n : ℂ)) hlam haC rfl
    (hpos 0) hc hsep
  have hC1 := abel_limit_of_residueFree ha0 hlam ha hres hL (hpos 0) hw
  have hC0 := tendsto_abelCos_zero_of_residueFree ha0 hlam ha hgm hgb hres hθ
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

end ResidueFree

/-! ## Rigidity -/

/-- A decaying defect cannot carry an imaginary pole residue. -/
theorem measure_pole_real_of_decaying_theta_defect {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {β : ℂ} {g : ℝ → ℂ} (hgm : Measurable g) {C a : ℝ} (ha : 0 < a)
    (hgd : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ (-a))
    (hθ : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ +
        -β + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    (β.re : ℂ) = β := by
  have hgb := poly_of_decay ha.le hgd
  have hreal (ε : ℝ) : (measureSeries ν (ε : ℂ)).im = 0 ∧
      (measureDual ν (ε : ℂ)).im = 0 := by
    have hs := congrArg Complex.im (measureSeries_conj ν (ε : ℂ))
    have hd := congrArg Complex.im (measureDual_conj ν (ε : ℂ))
    simp only [Complex.conj_ofReal, Complex.conj_im] at hs hd
    constructor <;> linarith
  have hlim := (Complex.continuous_im.tendsto _).comp
    (tendsto_mul_defectLaplace_of_decay hgm ha hgd 0)
  simp only [Complex.ofReal_zero, zero_mul, add_zero, Complex.zero_im] at hlim
  change Tendsto (fun ε : ℝ => ((ε : ℂ) * defectLaplace g (ε : ℂ)).im)
    (𝓝[>] 0) (𝓝 0) at hlim
  simp only [Complex.im_ofReal_mul] at hlim
  have hid : ∀ ε : ℝ, 0 < ε →
      ε * (defectLaplace g (ε : ℂ)).im = β.im / Real.pi - ε * β.im := by
    intro ε hε
    have hh := congrArg Complex.im
      (measureSeries_eq_of_theta_defect hsupp hmom hgm hgb hθ
        (show 0 < (ε : ℂ).re from hε))
    rw [show (Real.pi : ℂ) * (ε : ℂ) = ((Real.pi * ε : ℝ) : ℂ) by push_cast; rfl] at hh
    simp only [Complex.add_im, Complex.div_ofReal_im, Complex.neg_im,
      (hreal ε).1, (hreal ε).2, zero_add] at hh
    field_simp [Real.pi_ne_zero, ne_of_gt hε] at hh ⊢
    nlinarith only [hh]
  have hother : Tendsto (fun ε : ℝ => β.im / Real.pi - ε * β.im)
      (𝓝[>] 0) (𝓝 (β.im / Real.pi)) := by
    simpa using ((by fun_prop : Continuous fun ε : ℝ =>
      β.im / Real.pi - ε * β.im).tendsto 0).mono_left nhdsWithin_le_nhds
  have hzero : Tendsto (fun ε : ℝ => β.im / Real.pi - ε * β.im) (𝓝[>] 0) (𝓝 0) := by
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hid ε hε
  have hi := (div_eq_zero_iff.mp (tendsto_nhds_unique hother hzero)).resolve_right Real.pi_ne_zero
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using hi.symm

/-- The unit atom alone cannot satisfy the theta law with a decaying defect. -/
theorem beurling_labels_nonempty_of_decaying_theta_defect
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    {β : ℝ} {g : ℝ → ℂ} (hgm : Measurable g) {C a : ℝ} (ha : 0 < a)
    (hgd : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ (-a))
    (hθ : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    Nonempty B.Label := by
  classical
  have hgb := poly_of_decay ha.le hgd
  have hres := tendsto_mul_defectLaplace_of_decay hgm ha hgd
  by_contra hempty
  have hx0 : ∀ x : B.Integer, x = 0 := by
    intro x
    induction x using Multiset.induction_on with
    | empty => rfl
    | cons l s ih => exact False.elim (hempty ⟨l⟩)
  let a : ℕ → ℝ := fun n => if n = 0 then 1 else 0
  let lam : ℕ → ℝ := fun n => (n : ℝ) + 1
  have ha0 : ∀ n, 0 ≤ a n := fun n => by simp only [a]; split_ifs <;> norm_num
  have hlam : ∀ n, 1 ≤ lam n := fun n => by
    dsimp only [lam]
    linarith only [Nat.cast_nonneg n (α := ℝ)]
  have hmono : StrictMono lam := by
    intro m n hmn
    change (m : ℝ) + 1 < (n : ℝ) + 1
    have hmnR : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
    linarith only [hmnR]
  have hsa : Summable fun n => a n / lam n ^ 2 := by
    apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [a, hn]
  have ht (x : ℝ) : measureTheta (beurlingSystemIntegerMeasure B) x =
      freqTheta (fun n => (a n : ℂ)) lam x := by
    rw [measureTheta_beurlingSystemIntegerMeasure]
    unfold beurlingTheta
    rw [tsum_eq_single (0 : B.Integer) (fun x hx => False.elim (hx (hx0 x)))]
    unfold freqTheta
    rw [tsum_eq_single 0 (fun n hn => by simp [a, hn])]
    simp [a, lam, B.intNorm_zero]
  have hθ' : ∀ x : ℝ, 0 < x → freqTheta (fun n => (a n : ℂ)) lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta (fun n => (a n : ℂ)) lam x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x := by
    intro x hx
    simpa only [ht] using hθ x hx
  have hpole := integer_support_pins_pole_residue_of_residueFree hmono (by simp [lam])
    (fun n => ⟨n + 1, by simp [lam]⟩) ha0 hsa hgm hgb hres hθ'
  have hF := tendsto_mul_freqDual_of_residueFree ha0 hlam hsa hgm hgb hres hθ'
  have hd (ε : ℝ) : freqDual (fun n => (a n : ℂ)) lam (ε : ℂ) =
      Complex.exp (-(2 * Real.pi * (ε : ℂ))) := by
    unfold freqDual
    rw [tsum_eq_single 0 (fun n hn => by simp [a, hn])]
    simp [a, lam]
  have hz : Tendsto (fun ε : ℝ => (ε : ℂ) *
      freqDual (fun n => (a n : ℂ)) lam (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simp only [hd]
    have hc : Continuous fun ε : ℝ => (ε : ℂ) * Complex.exp (-(2 * Real.pi * (ε : ℂ))) := by
      fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hb : (β : ℂ) = 0 := (div_eq_zero_iff.mp (tendsto_nhds_unique hF hz)).resolve_right
    (by exact_mod_cast Real.pi_ne_zero)
  have hb' : β = 0 := by exact_mod_cast hb
  simp [a, hb'] at hpole

/-- **Rigidity for decaying theta defects.** -/
theorem beurlingSystem_rigidity_of_decaying_theta_defect
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun i : B.Integer => B.intNorm i ^ (-(3 / 2 : ℝ)))
    {β : ℝ} {g : ℝ → ℂ} (hgm : Measurable g) {C a : ℝ} (ha : 0 < a)
    (hgd : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ (-a))
    (hθ : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    β = 1 / 2 ∧
      beurlingSystemIntegerMeasure B = beurlingIntegerMeasure riemannPrimeMeasure ∧
      (∀ x : B.Integer, ∃ m : ℕ, 1 ≤ m ∧ B.intNorm x = (m : ℝ)) ∧
      (∀ m : ℕ, 1 ≤ m → ∃! x : B.Integer, B.intNorm x = (m : ℝ)) ∧
      (∀ s : ℂ, 1 < s.re → beurlingZeta B s = riemannZeta s) ∧
      Nonempty {e : B.Label ≃ {p : ℕ // Nat.Prime p} //
        ∀ l : B.Label, B.labelNorm l = ((e l : ℕ) : ℝ)} := by
  classical
  have hgb := poly_of_decay ha.le hgd
  have hres := tendsto_mul_defectLaplace_of_decay hgm ha hgd
  haveI := beurling_labels_nonempty_of_decaying_theta_defect B hgm ha hgd hθ
  have hint := beurling_intNorm_nat_of_decaying_theta_defect B hBsum hgm ha hgd hθ
  obtain ⟨lam, index, hmono, hlam0, hsurj, hnorm, hfinite⟩ := exists_ordered_beurling_norms B hBsum
  let A : ℕ → ℕ := fun n => Nat.card {x : B.Integer // index x = n}
  have hA1 : ∀ n, 1 ≤ A n := by
    intro n
    letI : Fintype {x : B.Integer // index x = n} := (hfinite n).fintype
    obtain ⟨x, hx⟩ := hsurj n
    letI : Nonempty {x : B.Integer // index x = n} := ⟨⟨x, hx⟩⟩
    have hh : 0 < Fintype.card {x : B.Integer // index x = n} :=
      Fintype.card_pos_iff.mpr inferInstance
    simp only [A, Nat.card_eq_fintype_card]
    omega
  have hunit0 : A 0 = 1 := by
    have hindex0 : index 0 = 0 :=
      hmono.injective ((hnorm 0).trans B.intNorm_zero |>.trans hlam0.symm)
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨0, hindex0⟩, fun x => ?_⟩
    apply Subtype.ext
    exact (intNorm_eq_one_iff B x.val).mp (by rw [← hnorm x.val, x.property, hlam0])
  have hlamInt : ∀ n, ∃ k : ℕ, lam n = k := by
    intro n
    obtain ⟨x, hx⟩ := hsurj n
    obtain ⟨k, hk⟩ := hint x
    exact ⟨k, by rw [← hx, hnorm x, hk]⟩
  have hBsum2 := summable_beurling_inv_sq B hBsum
  have hsa : Summable fun n => (A n : ℝ) / lam n ^ 2 := by
    have hh := (sum_by_ordered_norm_fibers hnorm hfinite (fun u => 1 / u ^ 2) hBsum2).1
    simpa only [nsmul_eq_mul, mul_one_div, A] using hh
  have htheta : ∀ x : ℝ, 0 < x →
      measureTheta (beurlingSystemIntegerMeasure B) x =
        freqTheta (fun n => ((A n : ℝ) : ℂ)) lam x := by
    intro x hx
    rw [measureTheta_beurlingSystemIntegerMeasure]
    have hs : Summable fun y : B.Integer =>
        ((Real.exp (-Real.pi * B.intNorm y ^ 2 * x) : ℝ) : ℂ) := by
      refine Summable.of_norm_bounded (hBsum2.mul_left ((Real.pi * x)⁻¹)) fun y => ?_
      simpa only [one_mul, norm_one] using norm_thetaTerm_le
        (a := fun _ => (1 : ℂ)) (lam := fun _ => B.intNorm y) (fun _ => B.one_le_intNorm y) hx 0
    have hh := (sum_by_ordered_norm_fibers hnorm hfinite
      (fun u => ((Real.exp (-Real.pi * u ^ 2 * x) : ℝ) : ℂ)) hs).2
    simpa only [beurlingTheta, freqTheta, nsmul_eq_mul, Complex.ofReal_natCast, A] using hh
  have hθfreq : ∀ x : ℝ, 0 < x → freqTheta (fun n => ((A n : ℝ) : ℂ)) lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta (fun n => ((A n : ℝ) : ℂ)) lam x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x := by
    intro x hx
    simpa only [htheta x hx, htheta x⁻¹ (inv_pos.mpr hx)] using hθ x hx
  have hpole := integer_support_pins_pole_residue_of_residueFree hmono hlam0 hlamInt
    (fun n => Nat.cast_nonneg (A n)) hsa hgm hgb hres hθfreq
  rw [hunit0, Nat.cast_one] at hpole
  obtain ⟨hβ, hvals⟩ := integer_spectrum_of_residueFree hmono hlam0 hlamInt
    (fun n => by exact_mod_cast hA1 n) hsa (by linarith) hgm hgb hres hθfreq
  have hnormnat : ∀ x : B.Integer, B.intNorm x = (index x : ℝ) + 1 :=
    fun x => (hnorm x).symm.trans (hvals (index x)).1
  have hinj : Function.Injective index := by
    intro x y hxy
    letI : Fintype {z : B.Integer // index z = index x} := (hfinite (index x)).fintype
    have hc : Fintype.card {z : B.Integer // index z = index x} ≤ 1 := by
      rw [← Nat.card_eq_fintype_card]
      exact_mod_cast (hvals (index x)).2.le
    letI := Fintype.card_le_one_iff_subsingleton.mp hc
    exact congrArg Subtype.val (Subsingleton.elim
      (⟨x, rfl⟩ : {z : B.Integer // index z = index x}) ⟨y, hxy.symm⟩)
  let e : B.Integer ≃ ℕ := Equiv.ofBijective index ⟨hinj, hsurj⟩
  have hν : beurlingSystemIntegerMeasure B =
      Measure.sum (fun k : ℕ => Measure.dirac ((k : ℝ) + 1)) := by
    ext s hs
    rw [beurlingSystemIntegerMeasure, Measure.sum_apply _ hs, Measure.sum_apply _ hs]
    simp only [hnormnat]
    exact e.tsum_eq (fun n => Measure.dirac ((n : ℝ) + 1) s)
  exact ⟨hβ, beurlingSystem_rigidity_of_integer_measure_eq B hν⟩

/-- **Theorem II.1.**  A countable Beurling system with `Σ |x|^{-3/2} < ∞` in the Hamburger strip
class whose FE defect decays like `(1 + |t|)^{-1/2 + ε₀}`, `ε₀ < 1/2`, is the system of rational
primes: `β = 1/2`, `ζ_B = ζ` and the generators are norm-equivalent to the primes. -/
theorem beurlingSystem_rigidity_of_decaying_defect
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun x : B.Integer => B.intNorm x ^ (-(3 / 2 : ℝ)))
    {β : ℂ} {g : ℝ → ℂ} (hH : HamburgerStripDefect (beurlingZeta B) β g)
    {Cg ε₀ : ℝ} (hε₀ : ε₀ < 1 / 2) (hgd : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ (-(1 / 2 : ℝ) + ε₀)) :
    β = 1 / 2 ∧
      beurlingSystemIntegerMeasure B = beurlingIntegerMeasure riemannPrimeMeasure ∧
      (∀ x : B.Integer, ∃ m : ℕ, 1 ≤ m ∧ B.intNorm x = (m : ℝ)) ∧
      (∀ m : ℕ, 1 ≤ m → ∃! x : B.Integer, B.intNorm x = (m : ℝ)) ∧
      (∀ s : ℂ, 1 < s.re → beurlingZeta B s = riemannZeta s) ∧
      Nonempty {e : B.Label ≃ {p : ℕ // Nat.Prime p} //
        ∀ l : B.Label, B.labelNorm l = ((e l : ℕ) : ℝ)} := by
  obtain ⟨E, C, hEc, hEd, hdecay, hR, hC, hgm, Cg', Ng, hgb⟩ := hH
  have ha : 0 < 1 / 2 - ε₀ := by linarith
  have hgd' : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ (-(1 / 2 - ε₀)) := fun t => by
    rw [show -(1 / 2 - ε₀) = -(1 / 2 : ℝ) + ε₀ by ring]; exact hgd t
  have hsupp := beurlingSystemIntegerMeasure_Iio_one_eq_zero B
  have hmom := integrable_rpow_beurlingSystemIntegerMeasure B hBsum
  have hR' : ∀ s : ℂ, s.re = 3 / 2 →
      Complex.Gammaℝ s * measureDirichlet (beurlingSystemIntegerMeasure B) s =
        E s + β * Complex.Gammaℝ (s - 1) := by
    simpa only [measureDirichlet_beurlingSystemIntegerMeasure] using hR
  have hθ := measureTheta_defect_relation hsupp hmom hEc hEd hdecay hR' hC hgm hgb
  have hβ := measure_pole_real_of_decaying_theta_defect hsupp
    (integrable_inv_sq_of_integrable_rpow_neg_three_halves hsupp hmom) hgm ha hgd' hθ
  have hθreal : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β.re : ℂ) + (β.re : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x := by
    simpa only [hβ] using hθ
  obtain ⟨hb, hrest⟩ := beurlingSystem_rigidity_of_decaying_theta_defect B hBsum hgm ha hgd'
    hθreal
  refine ⟨?_, hrest⟩
  rw [← hβ, hb]
  norm_num

/-- **No fake zeros.**  Under the hypotheses of Theorem II.1, every holomorphic continuation of
`(s - 1) ζ_B(s)` to `Re s > 1/2` vanishes only at zeros of `ζ`. -/
theorem riemannZeta_eq_zero_of_decaying_defect
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun x : B.Integer => B.intNorm x ^ (-(3 / 2 : ℝ)))
    {β : ℂ} {g : ℝ → ℂ} (hH : HamburgerStripDefect (beurlingZeta B) β g)
    {Cg ε₀ : ℝ} (hε₀ : ε₀ < 1 / 2) (hgd : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ (-(1 / 2 : ℝ) + ε₀))
    {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGeq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * beurlingZeta B s)
    {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hρ1 : ρ ≠ 1) (hG0 : G ρ = 0) : riemannZeta ρ = 0 := by
  obtain ⟨-, -, -, -, hζ, -⟩ := beurlingSystem_rigidity_of_decaying_defect B hBsum hH hε₀ hgd
  have hne : ∀ {s : ℂ}, s ≠ 1 → RHTower.zetaResidueUnit s = (s - 1) * riemannZeta s :=
    fun hs => by simp [RHTower.zetaResidueUnit, Function.update_of_ne hs]
  have hid := SumProductArithmeticOfTheLogarithm.eqOn_re_gt_of_eq_on_re_gt_one
    (by norm_num : (1 / 2 : ℝ) < 1) hG
    (fun s _ => (RHTower.analyticAt_zetaResidueUnit s).differentiableAt.differentiableWithinAt)
    (fun s hs => by
      have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
      rw [hGeq s hs, hζ s hs, hne hs1]) hρ
  rw [hG0, hne hρ1] at hid
  exact (mul_eq_zero.mp hid.symm).resolve_left (sub_ne_zero.mpr hρ1)

end GaloisForLFunctions.EulerFETransportTheory
