import GaloisForLFunctions.RHTower.Deninger.DeningerCofinalPrimeMeyerEscape
import GaloisForLFunctions.RHTower.Deninger.DeningerTomographyNonstrict

/-!
# Literal damped paired source and original-prime circle contraction

The damped Euler defect and its actual weighted-reflection mate act on the
all-weight logarithmic source. Their entire Mellin multiplier is identified
exactly, as is their full periodization in the original smooth prime circle.
After normalization by an actual Xi evaluation, the residual is strictly
contractive throughout the open strip, including zero damping. The explicit
positive gap comes from the reverse triangle inequality and
`(1-q*x)*(1-q*y) - (1-q)*(1-q*x*y) = q*(1-x)*(1-y)`.

Repeated application to the original reflected Gaussian retains weighted
reflection and a nonzero Xi reading at every original prime depth. Its
normalized circle trace tends to zero in the actual smooth-circle topology,
while its literal original-source Xi reading remains one. The complete
original Gamma/flux discrepancy is nonzero at every normalized finite
stage. All source functions remain in the original all-weight class.

This does not assert convergence of the full source or vanishing of its
fixed Sonin image. A cofinal product must control its entire moving
normalized remainder, and the Green/BV-to-fixed-reader comparison remains
open. In particular, a scalar contraction is not a source-domain limit.
-/

open Complex Filter Topology SchwartzMap
namespace RHTower
noncomputable section

def deningerDampedPrimeWeight (L a : ℝ) : ℝ := Real.exp (-a * L)

def deningerDampedPairedMultiplier (L a : ℝ) (s : ℂ) : ℂ :=
  (1 - (deningerDampedPrimeWeight L a : ℂ) * Complex.exp ((-L : ℂ) * s)) *
    (1 - (deningerDampedPrimeWeight L a : ℂ) * Complex.exp ((-L : ℂ) * (1-s)))

def deningerDampedPairedResidual (L a : ℝ) : ℝ :=
  (1 - deningerDampedPrimeWeight L a) *
    (1 - deningerDampedPrimeWeight L a * Real.exp (-L))

def deningerDampedStrongLogDefect (L a : ℝ) :
    DeningerMeyerStrongLogTarget →ₗ[ℂ] DeningerMeyerStrongLogTarget :=
  LinearMap.id - (deningerDampedPrimeWeight L a : ℂ) • deningerMeyerStrongLogFlow (-L)

def deningerDampedPairedStrongLogDefect (L a : ℝ) :
    DeningerMeyerStrongLogTarget →ₗ[ℂ] DeningerMeyerStrongLogTarget :=
  (deningerDampedStrongLogDefect L a).comp
    (deningerMeyerStrongLogJ.comp ((deningerDampedStrongLogDefect L a).comp deningerMeyerStrongLogJ))

theorem deningerDampedStrongLogDefect_mellin (L a : ℝ)
    (g : DeningerMeyerStrongLogTarget) (s : ℂ) :
    deningerMeyerStrongLogMellin (deningerDampedStrongLogDefect L a g) s =
      (1 - (deningerDampedPrimeWeight L a : ℂ) * Complex.exp ((-L : ℂ) * s)) *
        deningerMeyerStrongLogMellin g s := by
  change deningerMeyerStrongLogMellinLM s
    (g - (deningerDampedPrimeWeight L a : ℂ) • deningerMeyerStrongLogFlow (-L) g) = _
  rw [map_sub, map_smul]
  change deningerMeyerStrongLogMellin g s - (deningerDampedPrimeWeight L a : ℂ) *
    deningerMeyerStrongLogMellin (deningerMeyerStrongLogFlow (-L) g) s = _
  rw [deningerMeyerStrongLogMellin_flow]
  push_cast
  rw [mul_comm s]
  ring

theorem deningerDampedPairedStrongLogDefect_mellin (L a : ℝ)
    (g : DeningerMeyerStrongLogTarget) (s : ℂ) :
    deningerMeyerStrongLogMellin (deningerDampedPairedStrongLogDefect L a g) s =
      deningerDampedPairedMultiplier L a s * deningerMeyerStrongLogMellin g s := by
  change deningerMeyerStrongLogMellin
    (deningerDampedStrongLogDefect L a (deningerMeyerStrongLogJ
      (deningerDampedStrongLogDefect L a (deningerMeyerStrongLogJ g)))) s = _
  rw [deningerDampedStrongLogDefect_mellin, deningerMeyerStrongLogMellin_J,
    deningerDampedStrongLogDefect_mellin, deningerMeyerStrongLogMellin_J]
  simp only [sub_sub_cancel, deningerDampedPairedMultiplier]
  ring

theorem deningerDampedStrongLogDefect_J_mate (L a : ℝ)
    (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerStrongLogJ (deningerDampedStrongLogDefect L a (deningerMeyerStrongLogJ g)) =
      g - ((deningerDampedPrimeWeight L a : ℂ) * (Real.exp (-L) : ℂ)) •
        deningerMeyerStrongLogFlow L g := by
  change deningerMeyerStrongLogJ
    (deningerMeyerStrongLogJ g - (deningerDampedPrimeWeight L a : ℂ) •
      deningerMeyerStrongLogFlow (-L) (deningerMeyerStrongLogJ g)) = _
  rw [map_sub, map_smul, deningerMeyerStrongLogJ_sq,
    deningerMeyerStrongLogJ_flow, deningerMeyerStrongLogJ_sq, neg_neg, smul_smul]

theorem deningerDampedPairedStrongLogDefect_J (L a : ℝ)
    (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerStrongLogJ (deningerDampedPairedStrongLogDefect L a g) =
      deningerDampedPairedStrongLogDefect L a (deningerMeyerStrongLogJ g) := by
  apply deningerMeyerStrongLogMellin_injective
  funext s
  dsimp only
  rw [deningerMeyerStrongLogMellin_J, deningerDampedPairedStrongLogDefect_mellin,
    deningerDampedPairedStrongLogDefect_mellin, deningerMeyerStrongLogMellin_J]
  simp only [deningerDampedPairedMultiplier, sub_sub_cancel]
  ring

def deningerDampedStrongLogOriginalSourceLM :
    DeningerMeyerStrongLogTarget →ₗ[ℂ] DeningerMeyerSource where
  toFun g := DeningerMeyerSource.toSource.symm
    (deningerExpSchwartzOfStrongLogDecay g.val g.property)
  map_add' g h := by
    apply DeningerMeyerSource.toSource.injective
    apply Subtype.ext
    ext t
    rfl
  map_smul' c g := by
    apply DeningerMeyerSource.toSource.injective
    apply Subtype.ext
    ext t
    rfl

theorem deningerDampedStrongLogOriginalSourceLM_mellin
    (g : DeningerMeyerStrongLogTarget) (s : ℂ) :
    deningerOriginalMeyerMellinCLM s (deningerDampedStrongLogOriginalSourceLM g) =
      deningerMeyerStrongLogMellin g s := by
  rw [deningerOriginalMeyerMellinCLM_apply]
  rfl

private theorem strongLogOriginal_per_flow (P : {x : ℝ // 0 < x})
    (g : DeningerMeyerStrongLogTarget) (c : ℝ) (hc : c = P.1 ∨ c = -P.1) :
    deningerPeriodizationLM P
      (deningerDampedStrongLogOriginalSourceLM (deningerMeyerStrongLogFlow c g)) =
    deningerPeriodizationLM P (deningerDampedStrongLogOriginalSourceLM g) := by
  apply (DeningerCircle.toPeriodic (P := P)).injective
  apply Subtype.ext
  funext t
  change deningerPeriodizationSum
    (deningerExpSchwartzOfStrongLogDecay (deningerMeyerStrongLogFlow c g).val
      (deningerMeyerStrongLogFlow c g).property : 𝓢(ℝ, ℂ)) P.1 t =
    deningerPeriodizationSum (deningerExpSchwartzOfStrongLogDecay g.val g.property) P.1 t
  have he : (deningerExpSchwartzOfStrongLogDecay (deningerMeyerStrongLogFlow c g).val
      (deningerMeyerStrongLogFlow c g).property : 𝓢(ℝ, ℂ)) =
    deningerExpShift (-c) (deningerExpSchwartzOfStrongLogDecay g.val g.property) := by
    ext u
    simp only [deningerExpSchwartzOfStrongLogDecay_apply,
      deningerMeyerStrongLogFlow_apply, deningerExpShift_apply, sub_eq_add_neg]
  rw [he, deningerPeriodizationSum_expShift]
  rcases hc with rfl | rfl
  · have hh := deningerPeriodizationSum_periodic
      (deningerExpSchwartzOfStrongLogDecay g.val g.property) P.1 (t - P.1)
    rw [sub_add_cancel] at hh
    simpa only [sub_eq_add_neg] using hh.symm
  · simpa only [neg_neg] using deningerPeriodizationSum_periodic
      (deningerExpSchwartzOfStrongLogDecay g.val g.property) P.1 t

theorem deningerDampedPairedStrongLogDefect_periodization
    (P : {x : ℝ // 0 < x}) (a : ℝ) (g : DeningerMeyerStrongLogTarget) :
    deningerPeriodizationLM P
      (deningerDampedStrongLogOriginalSourceLM (deningerDampedPairedStrongLogDefect P.1 a g)) =
    (deningerDampedPairedResidual P.1 a : ℂ) •
      deningerPeriodizationLM P (deningerDampedStrongLogOriginalSourceLM g) := by
  have hD (f : DeningerMeyerStrongLogTarget) :
      deningerPeriodizationLM P
        (deningerDampedStrongLogOriginalSourceLM (deningerDampedStrongLogDefect P.1 a f)) =
      (1 - (deningerDampedPrimeWeight P.1 a : ℂ)) •
        deningerPeriodizationLM P (deningerDampedStrongLogOriginalSourceLM f) := by
    change deningerPeriodizationLM P (deningerDampedStrongLogOriginalSourceLM
      (f - (deningerDampedPrimeWeight P.1 a : ℂ) • deningerMeyerStrongLogFlow (-P.1) f)) = _
    rw [map_sub, map_smul, map_sub, map_smul,
      strongLogOriginal_per_flow P f (-P.1) (Or.inr rfl), sub_smul, one_smul]
  change deningerPeriodizationLM P (deningerDampedStrongLogOriginalSourceLM
    (deningerDampedStrongLogDefect P.1 a (deningerMeyerStrongLogJ
      (deningerDampedStrongLogDefect P.1 a (deningerMeyerStrongLogJ g))))) = _
  rw [hD, deningerDampedStrongLogDefect_J_mate, map_sub, map_smul,
    map_sub, map_smul, strongLogOriginal_per_flow P g P.1 (Or.inl rfl)]
  simp only [deningerDampedPairedResidual, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_one, mul_smul, sub_smul, one_smul, smul_sub]

private theorem paired_residual_norm_gap (q x y : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hx : 0 < x) (hx1 : x < 1) (hy : 0 < y) (hy1 : y < 1)
    (z w : ℂ) (hz : ‖z‖ = q*x) (hw : ‖w‖ = q*y) :
    ‖(((1-q)*(1-q*x*y) : ℝ) : ℂ)‖ < ‖(1-z)*(1-w)‖ := by
  have hqx : q*x < 1 := (mul_le_mul_of_nonneg_right hq1 hx.le).trans_lt (by simpa using hx1)
  have hqy : q*y < 1 := (mul_le_mul_of_nonneg_right hq1 hy.le).trans_lt (by simpa using hy1)
  have hxy : x*y < 1 := (mul_lt_mul_of_pos_right hx1 hy).trans (by simpa using hy1)
  have hqxy : q*x*y < 1 := by
    calc q*x*y = q*(x*y) := by ring
         _ ≤ 1*(x*y) := mul_le_mul_of_nonneg_right hq1 (mul_pos hx hy).le
         _ < 1 := by simpa using hxy
  have hr : 0 ≤ (1-q)*(1-q*x*y) := mul_nonneg (sub_nonneg.mpr hq1) (sub_pos.mpr hqxy).le
  have hgap : (1-q)*(1-q*x*y) < (1-q*x)*(1-q*y) := by
    have hp := mul_pos (mul_pos hq (sub_pos.mpr hx1)) (sub_pos.mpr hy1)
    nlinarith
  have hz' : 1-q*x ≤ ‖1-z‖ := by
    simpa only [norm_one, hz] using norm_sub_norm_le (1 : ℂ) z
  have hw' : 1-q*y ≤ ‖1-w‖ := by
    simpa only [norm_one, hw] using norm_sub_norm_le (1 : ℂ) w
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr, norm_mul]
  exact hgap.trans_le (mul_le_mul hz' hw' (sub_pos.mpr hqy).le (norm_nonneg _))

/-- Strict contraction of the actual normalized residual throughout the open strip. -/
theorem deningerDampedPairedResidual_norm_lt_multiplier (L a : ℝ) (hL : 0 < L)
    (ha : 0 ≤ a) (s : ℂ) (hs : 0 < s.re ∧ s.re < 1) :
    ‖(deningerDampedPairedResidual L a : ℂ)‖ < ‖deningerDampedPairedMultiplier L a s‖ := by
  let q := deningerDampedPrimeWeight L a
  let x := Real.exp (-L*s.re)
  let y := Real.exp (-L*(1-s.re))
  have hq : 0 < q := Real.exp_pos _
  have hq1 : q ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) hL.le)
  have hx : 0 < x := Real.exp_pos _
  have hy : 0 < y := Real.exp_pos _
  have hx1 : x < 1 := Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos hL) hs.1)
  have hy1 : y < 1 := Real.exp_lt_one_iff.mpr
    (mul_neg_of_neg_of_pos (neg_neg_of_pos hL) (sub_pos.mpr hs.2))
  have hxy : x*y = Real.exp (-L) := by
    dsimp only [x, y]
    rw [← Real.exp_add]
    congr 1
    ring
  have hn (v : ℂ) :
      ‖(q : ℂ) * Complex.exp ((-L : ℂ)*v)‖ = q * Real.exp (-L*v.re) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq, Complex.norm_exp]
    congr 2
    simp
  have hh := paired_residual_norm_gap q x y hq hq1 hx hx1 hy hy1
    ((q : ℂ) * Complex.exp ((-L : ℂ)*s))
    ((q : ℂ) * Complex.exp ((-L : ℂ)*(1-s))) (hn s) (by simpa [y] using hn (1-s))
  have hr : (1-q)*(1-q*x*y) = deningerDampedPairedResidual L a := by
    rw [mul_assoc q x y, hxy]
    rfl
  simpa only [hr, deningerDampedPairedMultiplier] using hh

theorem deningerDampedPairedMultiplier_ne_zero (L a : ℝ) (hL : 0 < L)
    (ha : 0 ≤ a) (s : ℂ) (hs : 0 < s.re ∧ s.re < 1) :
    deningerDampedPairedMultiplier L a s ≠ 0 := by
  have hh := deningerDampedPairedResidual_norm_lt_multiplier L a hL ha s hs
  exact norm_pos_iff.mp ((norm_nonneg _).trans_lt hh)

theorem deningerDampedPairedNormalizedResidual_norm_lt_one (L a : ℝ) (hL : 0 < L)
    (ha : 0 ≤ a) (s : ℂ) (hs : 0 < s.re ∧ s.re < 1) :
    ‖(deningerDampedPairedResidual L a : ℂ) / deningerDampedPairedMultiplier L a s‖ < 1 := by
  rw [norm_div, div_lt_one (norm_pos_iff.mpr (deningerDampedPairedMultiplier_ne_zero L a hL ha s hs))]
  exact deningerDampedPairedResidual_norm_lt_multiplier L a hL ha s hs

/-- Repeated depletion at one original prime, retaining every depth. -/
def deningerDampedPrimeGaussianPower (p : Nat.Primes) (a : ℝ) :
    ℕ → DeningerMeyerStrongLogTarget
  | 0 => deningerMeyerReflectedLogGaussianSource
  | n+1 => deningerDampedPairedStrongLogDefect (Real.log (p : ℕ)) a
      (deningerDampedPrimeGaussianPower p a n)

theorem deningerDampedPrimeGaussianPower_mellin (p : Nat.Primes) (a : ℝ) (n : ℕ) (s : ℂ) :
    deningerMeyerStrongLogMellin (deningerDampedPrimeGaussianPower p a n) s =
      deningerDampedPairedMultiplier (Real.log (p : ℕ)) a s ^ n *
        deningerMeyerStrongLogMellin deningerMeyerReflectedLogGaussianSource s := by
  induction n with
  | zero => simp [deningerDampedPrimeGaussianPower]
  | succ n ih =>
    rw [deningerDampedPrimeGaussianPower, deningerDampedPairedStrongLogDefect_mellin, ih, pow_succ]
    ring

theorem deningerDampedPrimeGaussianPower_J_fixed (p : Nat.Primes) (a : ℝ) (n : ℕ) :
    deningerMeyerStrongLogJ (deningerDampedPrimeGaussianPower p a n) =
      deningerDampedPrimeGaussianPower p a n := by
  induction n with
  | zero => exact deningerMeyerReflectedLogGaussianSource_J_fixed
  | succ n ih =>
    rw [deningerDampedPrimeGaussianPower, deningerDampedPairedStrongLogDefect_J, ih]

theorem deningerDampedPrimeGaussianPower_periodization (p : Nat.Primes) (a : ℝ) (n : ℕ) :
    deningerPeriodizationLM
      ⟨Real.log (p : ℕ), Real.log_pos (by exact_mod_cast p.property.one_lt)⟩
      (deningerDampedStrongLogOriginalSourceLM (deningerDampedPrimeGaussianPower p a n)) =
    (deningerDampedPairedResidual (Real.log (p : ℕ)) a : ℂ) ^ n •
      deningerPeriodizationLM
        ⟨Real.log (p : ℕ), Real.log_pos (by exact_mod_cast p.property.one_lt)⟩
        (deningerDampedStrongLogOriginalSourceLM deningerMeyerReflectedLogGaussianSource) := by
  induction n with
  | zero => simp [deningerDampedPrimeGaussianPower]
  | succ n ih =>
    rw [deningerDampedPrimeGaussianPower, deningerDampedPairedStrongLogDefect_periodization, ih,
      ← mul_smul, pow_succ, mul_comm]

/-- Normalize by the literal Xi evaluation, before taking any source limit. -/
def deningerDampedPrimeGaussianNormalized (p : Nat.Primes) (a : ℝ)
    (rho : XiDivisorSupport) (n : ℕ) : DeningerMeyerSource :=
  (deningerMeyerStrongLogMellin (deningerDampedPrimeGaussianPower p a n) rho)⁻¹ •
    deningerDampedStrongLogOriginalSourceLM (deningerDampedPrimeGaussianPower p a n)

theorem deningerDampedPrimeGaussianPower_xi_ne_zero (p : Nat.Primes) (a : ℝ)
    (ha : 0 ≤ a) (rho : XiDivisorSupport) (n : ℕ) :
    deningerMeyerStrongLogMellin (deningerDampedPrimeGaussianPower p a n) rho ≠ 0 := by
  rw [deningerDampedPrimeGaussianPower_mellin]
  exact mul_ne_zero (pow_ne_zero n (deningerDampedPairedMultiplier_ne_zero _ _
    (Real.log_pos (by exact_mod_cast p.property.one_lt)) ha rho
    (xi_divisor_support_re_mem_open_unit rho)))
    (deningerMeyerReflectedLogGaussianSource_mellin_ne_zero rho)

theorem deningerDampedPrimeGaussianNormalized_reading (p : Nat.Primes) (a : ℝ)
    (ha : 0 ≤ a) (rho : XiDivisorSupport) (n : ℕ) :
    deningerOriginalMeyerMellinCLM rho (deningerDampedPrimeGaussianNormalized p a rho n) = 1 := by
  rw [deningerDampedPrimeGaussianNormalized, map_smul,
    deningerDampedStrongLogOriginalSourceLM_mellin, smul_eq_mul,
    inv_mul_cancel₀ (deningerDampedPrimeGaussianPower_xi_ne_zero p a ha rho n)]

theorem deningerDampedPrimeGaussianNormalized_periodization (p : Nat.Primes) (a : ℝ)
    (rho : XiDivisorSupport) (n : ℕ) :
    deningerPeriodizationLM
      ⟨Real.log (p : ℕ), Real.log_pos (by exact_mod_cast p.property.one_lt)⟩
      (deningerDampedPrimeGaussianNormalized p a rho n) =
    ((deningerDampedPairedResidual (Real.log (p : ℕ)) a : ℂ) /
      deningerDampedPairedMultiplier (Real.log (p : ℕ)) a rho) ^ n •
      deningerPeriodizationLM
        ⟨Real.log (p : ℕ), Real.log_pos (by exact_mod_cast p.property.one_lt)⟩
        (deningerDampedPrimeGaussianNormalized p a rho 0) := by
  rw [deningerDampedPrimeGaussianNormalized, map_smul,
    deningerDampedPrimeGaussianPower_periodization, deningerDampedPrimeGaussianPower_mellin]
  simp only [deningerDampedPrimeGaussianNormalized, deningerDampedPrimeGaussianPower,
    map_smul, ← mul_smul, mul_inv_rev, div_eq_mul_inv]
  congr 1
  ring

/-- Actual smooth prime-circle convergence, while the original Xi reading stays one. -/
theorem deningerDampedPrimeGaussianNormalized_circle_limit (p : Nat.Primes)
    (a : {x : ℝ // 0 ≤ x}) (rho : XiDivisorSupport) :
    Tendsto (fun n => deningerPeriodizationLM
      ⟨Real.log (p : ℕ), Real.log_pos (by exact_mod_cast p.property.one_lt)⟩
      (deningerDampedPrimeGaussianNormalized p a rho n)) atTop
      (nhds (0 : DeningerCircle
        ⟨Real.log (p : ℕ), Real.log_pos (by exact_mod_cast p.property.one_lt)⟩)) := by
  have hh := tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    (deningerDampedPairedNormalizedResidual_norm_lt_one (Real.log (p : ℕ)) a
      (Real.log_pos (by exact_mod_cast p.property.one_lt)) a.property rho
      (xi_divisor_support_re_mem_open_unit rho))
  have hlim := hh.smul_const (deningerPeriodizationLM
      ⟨Real.log (p : ℕ), Real.log_pos (by exact_mod_cast p.property.one_lt)⟩
      (deningerDampedPrimeGaussianNormalized p a rho 0))
  rw [zero_smul] at hlim
  apply hlim.congr'
  exact Filter.Eventually.of_forall fun n =>
    (deningerDampedPrimeGaussianNormalized_periodization p a rho n).symm

/-- Unconditional actual family: reflection is preserved, Xi is retained, and one circle vanishes. -/
theorem deningerDampedOriginalPrime_source_and_circle (p : Nat.Primes)
    (a : {x : ℝ // 0 ≤ x}) (rho : XiDivisorSupport) :
    (∀ n, deningerMeyerStrongLogJ (deningerDampedPrimeGaussianPower p a n) =
      deningerDampedPrimeGaussianPower p a n) ∧
    (∀ n, deningerOriginalMeyerMellinCLM rho
      (deningerDampedPrimeGaussianNormalized p a rho n) = 1) ∧
    Tendsto (fun n => deningerPeriodizationLM
      ⟨Real.log (p : ℕ), Real.log_pos (by exact_mod_cast p.property.one_lt)⟩
      (deningerDampedPrimeGaussianNormalized p a rho n)) atTop
      (nhds (0 : DeningerCircle
        ⟨Real.log (p : ℕ), Real.log_pos (by exact_mod_cast p.property.one_lt)⟩)) :=
  ⟨deningerDampedPrimeGaussianPower_J_fixed p a,
    deningerDampedPrimeGaussianNormalized_reading p a a.property rho,
    deningerDampedPrimeGaussianNormalized_circle_limit p a rho⟩

/-- Vanishing prime-circle traces do not remove the complete original Gamma/flux discrepancy. -/
theorem deningerDampedPrimeGaussianNormalized_gamma_ne_transgression (p : Nat.Primes)
    (a : {x : ℝ // 0 ≤ x}) (rho : XiDivisorSupport) (n : ℕ) :
    deningerAdiabaticGammaBoundary (deningerDampedPrimeGaussianNormalized p a rho n) ≠
      deningerAdiabaticGreenStokesTransgression (deningerDampedPrimeGaussianNormalized p a rho n) := by
  let g : DeningerMeyerStrongLogTarget :=
    (deningerMeyerStrongLogMellin (deningerDampedPrimeGaussianPower p a n) rho)⁻¹ •
      deningerDampedPrimeGaussianPower p a n
  have hsrc : deningerDampedStrongLogOriginalSourceLM g =
      deningerDampedPrimeGaussianNormalized p a rho n := by
    change deningerDampedStrongLogOriginalSourceLM
      ((deningerMeyerStrongLogMellin (deningerDampedPrimeGaussianPower p a n) rho)⁻¹ •
        deningerDampedPrimeGaussianPower p a n) = _
    rw [map_smul]
    rfl
  have hone : deningerMeyerStrongLogMellin g rho = 1 := by
    rw [← deningerDampedStrongLogOriginalSourceLM_mellin, hsrc]
    exact deningerDampedPrimeGaussianNormalized_reading p a a.property rho n
  rw [← hsrc]
  apply deningerFiniteXiJet_nonzero_gamma_ne_transgression {rho} g
  intro hz
  have he := congrFun hz
    (⟨⟨rho, by simp⟩, ⟨0, xiSupportMultiplicity_pos rho⟩⟩ : DeningerMeyerFiniteXiJetSlot {rho})
  change deningerMeyerXiSupportJetEvaluationLM rho ⟨0, xiSupportMultiplicity_pos rho⟩
    (Submodule.Quotient.mk g) = 0 at he
  rw [deningerMeyerXiSupportJetEvaluationLM_mk,
    deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv, iteratedDeriv_zero, hone] at he
  exact one_ne_zero he

end
end RHTower
