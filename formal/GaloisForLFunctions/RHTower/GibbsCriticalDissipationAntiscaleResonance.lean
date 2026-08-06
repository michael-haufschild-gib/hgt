import GaloisForLFunctions.RHTower.GibbsSignedCovarianceAccumulation
import GaloisForLFunctions.RHTower.MobiusCriticalPrimeBlockResonance
import Mathlib.Analysis.MellinTransform

/-!
# Antiscale resonance of critical Gibbs dissipation

The same-sign dissipation vanishes exactly when normalized Gibbs current reverses sign across a
prime dilation. This module identifies that null direction with a concrete Mellin--Euler factor
and proves simultaneous normalized gain on the natural terminal prime window at the moving
frequency `pi / log y`.

The Mellin factorization is an identity for the actual finite Gibbs source, not an abstract
translation countermodel. No RH assumption, asymptotic prime theorem, or numerical computation is
used.
-/

open Complex Set MeasureTheory
open scoped BigOperators

namespace RHTower.GibbsGas

noncomputable section

/-- Same-sign dissipation has exactly one null direction: antiscale current coherence. -/
theorem gibbsSameSignDissipation_eq_zero_iff_antiscale
    (p : ℕ) (S : Finset ℕ) (x : ℝ) :
    gibbsSameSignDissipation p S x = 0 ↔
      normalizedGibbsCurrent S ((p : ℝ) * x) = -normalizedGibbsCurrent S x := by
  unfold gibbsSameSignDissipation
  have hZx : 0 < gibbsDiag S x 1 := gibbs_partition_pos S x
  have hZpx : 0 < gibbsDiag S ((p : ℝ) * x) 1 :=
    gibbs_partition_pos S ((p : ℝ) * x)
  have hcoeff :
      (gibbsDiag S x 1 * gibbsDiag S ((p : ℝ) * x) 1) /
          (gibbsDiag S x 1 + gibbsDiag S ((p : ℝ) * x) 1) ≠ 0 := by
    exact ne_of_gt (div_pos (mul_pos hZx hZpx) (add_pos hZx hZpx))
  rw [mul_eq_zero]
  simp only [hcoeff, false_or, sq_eq_zero_iff]
  constructor <;> intro h <;> linarith

/-- Mellin transform of a finite Gibbs activity section. -/
noncomputable def gibbsMellinTransform (S : Finset ℕ) (z : ℝ) (s : ℂ) : ℂ :=
  mellin (fun x : ℝ => (gibbsDiag S x z : ℂ)) s

/-- Every finite Gibbs section with positive dilation labels is Mellin-convergent in the open
right half-plane. -/
theorem mellinConvergent_gibbsDiag
    (S : Finset ℕ) (z : ℝ) {s : ℂ} (hs : 0 < s.re)
    (hS : ∀ p ∈ S, 0 < p) :
    MellinConvergent (fun x : ℝ => (gibbsDiag S x z : ℂ)) s := by
  induction S using Finset.induction_on with
  | empty =>
      simpa [MellinConvergent, gibbsDiag_empty, Complex.ofReal_exp, mul_comm] using
        Complex.GammaIntegral_convergent hs
  | @insert p S hp ih =>
      have hp0 : 0 < p := hS p (Finset.mem_insert_self p S)
      have hbase := ih (fun q hq => hS q (Finset.mem_insert_of_mem hq))
      have hscale : MellinConvergent
          (fun x : ℝ => (gibbsDiag S ((p : ℝ) * x) z : ℂ)) s :=
        (MellinConvergent.comp_mul_left (by exact_mod_cast hp0)).2 hbase
      have hz := hasMellin_const_smul hscale (z : ℂ)
      have hzconv : MellinConvergent
          (fun x : ℝ => (z : ℂ) * (gibbsDiag S ((p : ℝ) * x) z : ℂ)) s := by
        simpa only [smul_eq_mul] using hz.1
      have hadd := (hasMellin_add hbase hzconv).1
      refine hadd.congr_fun ?_ measurableSet_Ioi
      intro x hx
      simp only [smul_eq_mul]
      rw [gibbsDiag_insert p S hp]
      push_cast
      ring

/-- **Finite Gibbs Mellin--Euler factorization.** Every positive finite dilation alphabet has the
exact Euler product `Gamma(s) * product (1 + z * p^(-s))`. -/
theorem gibbsMellinTransform_eq_gamma_eulerProduct
    (S : Finset ℕ) (z : ℝ) {s : ℂ} (hs : 0 < s.re)
    (hS : ∀ p ∈ S, 0 < p) :
    gibbsMellinTransform S z s =
      Complex.Gamma s * ∏ p ∈ S, (1 + (z : ℂ) * (p : ℂ) ^ (-s)) := by
  induction S using Finset.induction_on with
  | empty =>
      rw [gibbsMellinTransform]
      simp_rw [gibbsDiag_empty]
      simp only [Finset.prod_empty, mul_one]
      rw [mellin]
      simpa [Complex.GammaIntegral, Complex.ofReal_exp, mul_comm] using
        (Complex.Gamma_eq_integral hs).symm
  | @insert p S hp ih =>
      have hp0 : 0 < p := hS p (Finset.mem_insert_self p S)
      have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
      have hsub : ∀ q ∈ S, 0 < q := fun q hq => hS q (Finset.mem_insert_of_mem hq)
      have hbase := mellinConvergent_gibbsDiag S z hs hsub
      have hscale : MellinConvergent
          (fun x : ℝ => (gibbsDiag S ((p : ℝ) * x) z : ℂ)) s :=
        (MellinConvergent.comp_mul_left hpR).2 hbase
      have hfun : (fun x : ℝ => (gibbsDiag (insert p S) x z : ℂ)) =
          fun x : ℝ => (gibbsDiag S x z : ℂ) +
            (z : ℂ) * (gibbsDiag S ((p : ℝ) * x) z : ℂ) := by
        funext x
        rw [gibbsDiag_insert p S hp]
        push_cast
        rfl
      rw [gibbsMellinTransform, hfun]
      have hz := hasMellin_const_smul hscale (z : ℂ)
      have hzconv : MellinConvergent
          (fun x : ℝ => (z : ℂ) * (gibbsDiag S ((p : ℝ) * x) z : ℂ)) s := by
        simpa only [smul_eq_mul] using hz.1
      have hzmellin :
          mellin (fun x : ℝ => (z : ℂ) * (gibbsDiag S ((p : ℝ) * x) z : ℂ)) s =
            (z : ℂ) * mellin (fun x : ℝ => (gibbsDiag S ((p : ℝ) * x) z : ℂ)) s := by
        simpa only [smul_eq_mul] using hz.2
      rw [(hasMellin_add hbase hzconv).2, hzmellin]
      rw [mellin_comp_mul_left (fun x : ℝ => (gibbsDiag S x z : ℂ)) s hpR]
      change gibbsMellinTransform S z s +
          (z : ℂ) * ((p : ℂ) ^ (-s) * gibbsMellinTransform S z s) = _
      rw [ih hsub, Finset.prod_insert hp]
      ring

/-- Radius of a prime factor on the real Mellin line `Re(s)=r`. -/
noncomputable def gibbsCriticalAntiscaleRadius (r : ℝ) (p : ℕ) : ℝ :=
  (p : ℝ) ^ (-r)

/-- Fourier multiplier of one parity-difference insertion at Mellin height `t`. -/
noncomputable def gibbsCriticalAntiscaleFactor (r t : ℝ) (p : ℕ) : ℂ :=
  1 - (gibbsCriticalAntiscaleRadius r p : ℂ) *
    Complex.exp (((-(t * Real.log p) : ℝ) : ℂ) * Complex.I)

theorem cpow_neg_mellinLine_eq_antiscaleRadius
    {p : ℕ} (hp : 0 < p) (r t : ℝ) :
    (p : ℂ) ^ (-(r + t * Complex.I)) =
      (gibbsCriticalAntiscaleRadius r p : ℂ) *
        Complex.exp (((-(t * Real.log p) : ℝ) : ℂ) * Complex.I) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  change ((p : ℝ) : ℂ) ^ (-(r + t * Complex.I)) = _
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpR.ne')]
  rw [← Complex.ofReal_log hpR.le]
  rw [gibbsCriticalAntiscaleRadius, Real.rpow_def_of_pos hpR, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem gibbsCriticalAntiscaleFactor_eq_cpow
    {p : ℕ} (hp : 0 < p) (r t : ℝ) :
    gibbsCriticalAntiscaleFactor r t p =
      1 - (p : ℂ) ^ (-(r + t * Complex.I)) := by
  rw [gibbsCriticalAntiscaleFactor, cpow_neg_mellinLine_eq_antiscaleRadius hp]

/-- The parity section's Mellin reporter is exactly Gamma times the finite antiscale block. -/
theorem gibbsParityMellinTransform_eq_gamma_antiscaleProduct
    (S : Finset ℕ) {r : ℝ} (hr : 0 < r) (t : ℝ)
    (hS : ∀ p ∈ S, 0 < p) :
    gibbsMellinTransform S (-1) (r + t * Complex.I) =
      Complex.Gamma (r + t * Complex.I) *
        ∏ p ∈ S, gibbsCriticalAntiscaleFactor r t p := by
  rw [gibbsMellinTransform_eq_gamma_eulerProduct S (-1) (by simpa using hr) hS]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  rw [gibbsCriticalAntiscaleFactor_eq_cpow (hS p hp)]
  push_cast
  ring

theorem normSq_finset_prod (S : Finset ℕ) (f : ℕ → ℂ) :
    Complex.normSq (∏ p ∈ S, f p) = ∏ p ∈ S, Complex.normSq (f p) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
      rw [Finset.prod_insert hp, Finset.prod_insert hp, Complex.normSq_mul, ih]

/-- Squared Mellin reporter is exactly Gamma mass times the product of local antiscale factors. -/
theorem normSq_gibbsParityMellinTransform_eq_gamma_mul_antiscaleProduct
    (S : Finset ℕ) {r : ℝ} (hr : 0 < r) (t : ℝ)
    (hS : ∀ p ∈ S, 0 < p) :
    Complex.normSq (gibbsMellinTransform S (-1) (r + t * Complex.I)) =
      Complex.normSq (Complex.Gamma (r + t * Complex.I)) *
        ∏ p ∈ S, Complex.normSq (gibbsCriticalAntiscaleFactor r t p) := by
  rw [gibbsParityMellinTransform_eq_gamma_antiscaleProduct S hr t hS,
    Complex.normSq_mul, normSq_finset_prod]

/-- Exact local norm-square law for a general positive Mellin exponent. -/
theorem normSq_gibbsCriticalAntiscaleFactor
    {p : ℕ} (hp : 0 < p) (r t : ℝ) :
    Complex.normSq (gibbsCriticalAntiscaleFactor r t p) =
      1 + gibbsCriticalAntiscaleRadius r p ^ 2 -
        2 * gibbsCriticalAntiscaleRadius r p * Real.cos (t * Real.log p) := by
  have hfac : gibbsCriticalAntiscaleFactor r t p =
      (gibbsCriticalAntiscaleRadius r p : ℂ) *
          (((gibbsCriticalAntiscaleRadius r p)⁻¹ : ℝ) -
            Complex.exp (((-(t * Real.log p) : ℝ) : ℂ) * Complex.I)) := by
    rw [gibbsCriticalAntiscaleFactor]
    have hradius : gibbsCriticalAntiscaleRadius r p ≠ 0 := by
      exact ne_of_gt (Real.rpow_pos_of_pos (by exact_mod_cast hp) _)
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hradius]
  rw [hfac, Complex.normSq_mul, Complex.normSq_ofReal,
    RHTower.normSq_real_sub_exp_I_mul, Real.cos_neg]
  have hradius : gibbsCriticalAntiscaleRadius r p ≠ 0 := by
    exact ne_of_gt (Real.rpow_pos_of_pos (by exact_mod_cast hp) _)
  field_simp [hradius]
  ring

/-- Euler-baseline-normalized local reporter factor. -/
noncomputable def gibbsCriticalNormalizedReporterFactor (r t : ℝ) (p : ℕ) : ℝ :=
  Complex.normSq (gibbsCriticalAntiscaleFactor r t p) /
    (1 + gibbsCriticalAntiscaleRadius r p)

/-- A phase with cosine at most `-2/3` gives a strict normalized gain of one sixth of the
Mellin radius. -/
theorem one_add_radius_div_six_le_gibbsCriticalNormalizedReporterFactor
    {p : ℕ} (hp : 0 < p) {r t : ℝ}
    (hcos : Real.cos (t * Real.log p) ≤ -(2 / 3 : ℝ)) :
    1 + gibbsCriticalAntiscaleRadius r p / 6 ≤
      gibbsCriticalNormalizedReporterFactor r t p := by
  have hu0 : 0 ≤ gibbsCriticalAntiscaleRadius r p :=
    (Real.rpow_pos_of_pos (by exact_mod_cast hp) _).le
  have hden : 0 < 1 + gibbsCriticalAntiscaleRadius r p := by positivity
  rw [gibbsCriticalNormalizedReporterFactor, le_div_iff₀ hden,
    normSq_gibbsCriticalAntiscaleFactor hp]
  nlinarith [sq_nonneg (gibbsCriticalAntiscaleRadius r p)]

/-- At every phase the normalized reporter is bounded below by its zero-phase contraction
factor. -/
theorem gibbsCriticalNormalizedReporterFactor_universal_lower
    {p : ℕ} (hp : 0 < p) (r t : ℝ) :
    (1 - gibbsCriticalAntiscaleRadius r p) ^ 2 /
        (1 + gibbsCriticalAntiscaleRadius r p) ≤
      gibbsCriticalNormalizedReporterFactor r t p := by
  have hu0 : 0 ≤ gibbsCriticalAntiscaleRadius r p :=
    (Real.rpow_pos_of_pos (by exact_mod_cast hp) _).le
  have hden : 0 < 1 + gibbsCriticalAntiscaleRadius r p := by positivity
  rw [gibbsCriticalNormalizedReporterFactor, div_le_div_iff_of_pos_right hden,
    normSq_gibbsCriticalAntiscaleFactor hp]
  have hcos := Real.cos_le_one (t * Real.log p)
  have htwoU : 0 ≤ 2 * gibbsCriticalAntiscaleRadius r p := mul_nonneg (by norm_num) hu0
  have hmul := mul_le_mul_of_nonneg_left hcos htwoU
  nlinarith

/-- The phase chamber `[3*pi/4,pi]` lies strictly beyond the neutral cosine `-1/2`. -/
theorem cos_le_neg_two_thirds_of_three_pi_div_four_le
    {θ : ℝ} (hlower : 3 * Real.pi / 4 ≤ θ) (hupper : θ ≤ Real.pi) :
    Real.cos θ ≤ -(2 / 3 : ℝ) := by
  have hthree0 : 0 ≤ 3 * Real.pi / 4 := by positivity
  have hthreePi : 3 * Real.pi / 4 ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hθ0 : 0 ≤ θ := hthree0.trans hlower
  have hanti := Real.antitoneOn_cos
    ⟨hthree0, hthreePi⟩ ⟨hθ0, hupper⟩ hlower
  have hcos : Real.cos (3 * Real.pi / 4) = -(Real.sqrt 2 / 2) := by
    rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_four]
  have hsqrtSq : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt0 : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  have hsqrt : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by nlinarith
  rw [hcos] at hanti
  linarith

/-- At `t=pi/log y`, every prime in `(y/3,y]` lies in the strict normalized-gain chamber once
`y>=81`. -/
theorem gibbsCriticalPrimeWindow_cos_le_neg_two_thirds
    {y : ℝ} (hy : 81 ≤ y) {p : ℕ}
    (hpmem : p ∈ RHTower.mobiusCriticalPrimeWindow y) :
    Real.cos ((Real.pi / Real.log y) * Real.log p) ≤ -(2 / 3 : ℝ) := by
  have hy0 : 0 < y := by linarith
  have hy1 : 1 < y := by linarith
  have hx0 : 0 ≤ y / 3 := by positivity
  obtain ⟨hpprime, hplower, hpupper⟩ :=
    (RHTower.mem_windowPrimes hx0 hy0.le).mp hpmem
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  have hlog81 : Real.log (81 : ℝ) ≤ Real.log y :=
    Real.log_le_log (by norm_num) hy
  have hlog81eq : Real.log (81 : ℝ) = 4 * Real.log 3 := by
    rw [show (81 : ℝ) = 3 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hlog3budget : 4 * Real.log 3 ≤ Real.log y := by
    rw [← hlog81eq]
    exact hlog81
  have hloglower : Real.log (y / 3) < Real.log p :=
    Real.log_lt_log (div_pos hy0 (by norm_num)) hplower
  rw [Real.log_div hy0.ne' (by norm_num : (3 : ℝ) ≠ 0)] at hloglower
  have hlogpLower : (3 / 4 : ℝ) * Real.log y ≤ Real.log p := by
    nlinarith
  have hlogpUpper : Real.log p ≤ Real.log y := Real.log_le_log hp0 hpupper
  have hthetaLower : 3 * Real.pi / 4 ≤
      (Real.pi / Real.log y) * Real.log p := by
    rw [show (Real.pi / Real.log y) * Real.log p =
      (Real.pi * Real.log p) / Real.log y by field_simp]
    rw [le_div_iff₀ hlogy]
    nlinarith [mul_le_mul_of_nonneg_left hlogpLower Real.pi_pos.le]
  have hthetaUpper : (Real.pi / Real.log y) * Real.log p ≤ Real.pi := by
    rw [show (Real.pi / Real.log y) * Real.log p =
      (Real.pi * Real.log p) / Real.log y by field_simp]
    apply (div_le_iff₀ hlogy).2
    nlinarith [mul_le_mul_of_nonneg_left hlogpUpper Real.pi_pos.le]
  exact cos_le_neg_two_thirds_of_three_pi_div_four_le hthetaLower hthetaUpper

/-- Product of Euler-normalized Gibbs reporter factors over the terminal prime window. -/
noncomputable def gibbsCriticalPrimeWindowNormalizedReporterProduct (r y : ℝ) : ℝ :=
  ∏ p ∈ RHTower.mobiusCriticalPrimeWindow y,
    gibbsCriticalNormalizedReporterFactor r (Real.pi / Real.log y) p

/-- **Terminal antiscale resonance.** The normalized reporter block gains one sixth of the common
endpoint Mellin radius at every prime in `(y/3,y]`. -/
theorem gibbsCriticalPrimeWindow_normalizedReporterProduct_lower
    {r y : ℝ} (hr : 0 < r) (hy : 81 ≤ y) :
    (1 + y ^ (-r) / 6) ^ (RHTower.mobiusCriticalPrimeWindow y).card ≤
      gibbsCriticalPrimeWindowNormalizedReporterProduct r y := by
  rw [gibbsCriticalPrimeWindowNormalizedReporterProduct, ← Finset.prod_const]
  apply Finset.prod_le_prod
  · intro p hp
    positivity
  · intro p hp
    have hy0 : 0 ≤ y := by linarith
    have hx0 : 0 ≤ y / 3 := by linarith
    obtain ⟨hpprime, _hplower, hpupper⟩ :=
      (RHTower.mem_windowPrimes hx0 hy0).mp hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
    have hyradius : y ^ (-r) ≤ gibbsCriticalAntiscaleRadius r p := by
      exact Real.rpow_le_rpow_of_nonpos hp0 hpupper (by linarith)
    have hlocal := one_add_radius_div_six_le_gibbsCriticalNormalizedReporterFactor
      (r := r) hpprime.pos (gibbsCriticalPrimeWindow_cos_le_neg_two_thirds hy hp)
    exact (by linarith :
      1 + y ^ (-r) / 6 ≤ 1 + gibbsCriticalAntiscaleRadius r p / 6).trans hlocal

end

end RHTower.GibbsGas
