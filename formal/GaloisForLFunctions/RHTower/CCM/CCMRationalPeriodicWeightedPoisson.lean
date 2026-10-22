import GaloisForLFunctions.RHTower.CCM.CCMRationalArchimedeanSchwartzPoisson
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Periodic weighted Poisson summation for rational CCM traces

A compactly supported locally constant finite-adèlic factor restricts to a periodic weight on
the rational lattice once a common denominator and an open translation stabilizer are fixed.
This file isolates and proves the resulting analytic theorem.

For a period `M`, a weight `w : Fin M → ℂ`, and an archimedean Schwartz function `f`, the trace is

`Θ_{w,f}(a) = ∑' n : ℤ, w(n mod M) f(a n)`.

It is a finite sum of shifted lattices. Poisson summation transforms it into a dual lattice
weighted by the finite discrete Fourier coefficients of `w`. The physical zero mode is
`w 0 * f 0`; the dual zero mode is `(∑ r, w r) * (𝓕 f) 0`. When both vanish, explicit
arbitrary-power estimates hold at the two multiplicative ends.

No positivity, spectral assertion, numerical computation, or Riemann-hypothesis premise occurs.
The separate finite-adèlic topology theorem must still show that every Bruhat factor supplies such
a periodic weight.
-/

noncomputable section

open scoped SchwartzMap FourierTransform

namespace GaloisForLFunctions
namespace RHTower

def ccmRationalPeriodicResidue (M : ℕ) [NeZero M] (n : ℤ) : Fin M :=
  (Int.divModEquiv M n).2

def ccmRationalPeriodicWeightedTrace
    (M : ℕ) [NeZero M] (w : Fin M → ℂ)
    (f : CCMRationalArchimedeanSchwartz) (a : ℝ) : ℂ :=
  ∑' n : ℤ, w (ccmRationalPeriodicResidue M n) * f (a * (n : ℝ))

theorem ccmRationalPeriodicWeightedTrace_summable
    (M : ℕ) [NeZero M] (w : Fin M → ℂ)
    (f : CCMRationalArchimedeanSchwartz) {a : ℝ} (ha : a ≠ 0) :
    Summable
      (fun n : ℤ =>
        w (ccmRationalPeriodicResidue M n) * f (a * (n : ℝ))) := by
  let C : ℝ := ∑ r : Fin M, ‖w r‖
  have hbase :
      Summable (fun n : ℤ => ‖f (a * (n : ℝ))‖) :=
    ccmRationalArchimedeanSchwartz_lattice_summable f ha
  have hmajor :
      Summable (fun n : ℤ => C * ‖f (a * (n : ℝ))‖) :=
    hbase.mul_left C
  apply Summable.of_norm_bounded hmajor
  intro n
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_right
  · exact Finset.single_le_sum
      (fun i _ => norm_nonneg (w i)) (Finset.mem_univ _)
  · exact norm_nonneg _

set_option maxHeartbeats 800000 in
theorem ccmRationalPeriodicWeightedTrace_eq_sum_residues
    (M : ℕ) [NeZero M] (w : Fin M → ℂ)
    (f : CCMRationalArchimedeanSchwartz) {a : ℝ} (ha : a ≠ 0) :
    ccmRationalPeriodicWeightedTrace M w f a =
      ∑ r : Fin M, ∑' k : ℤ,
        w r * f (a * ((k : ℝ) * (M : ℝ) + (r : ℝ))) := by
  let F : ℤ → ℂ :=
    fun n => w (ccmRationalPeriodicResidue M n) * f (a * (n : ℝ))
  have hF : Summable F :=
    ccmRationalPeriodicWeightedTrace_summable M w f ha
  have hprod :
      Summable
        (fun p : ℤ × Fin M => F ((Int.divModEquiv M).symm p)) :=
    ((Int.divModEquiv M).symm.summable_iff).2 hF
  rw [ccmRationalPeriodicWeightedTrace]
  change (∑' n : ℤ, F n) = _
  rw [← (Int.divModEquiv M).symm.tsum_eq F]
  rw [hprod.tsum_prod, ← hprod.tsum_comm, tsum_fintype]
  apply Finset.sum_congr rfl
  intro r _
  apply tsum_congr
  intro k
  change
    w (ccmRationalPeriodicResidue M ((Int.divModEquiv M).symm (k, r))) *
        f (a * (((Int.divModEquiv M).symm (k, r) : ℤ) : ℝ)) =
      w r * f (a * ((k : ℝ) * (M : ℝ) + (r : ℝ)))
  rw [show ccmRationalPeriodicResidue M
      ((Int.divModEquiv M).symm (k, r)) = r by
    exact congrArg Prod.snd
      ((Int.divModEquiv M).apply_symm_apply (k, r))]
  rw [Int.divModEquiv_symm_apply]
  congr 2
  norm_cast

theorem ccmRationalArchimedeanShiftedLattice_poisson
    (f : CCMRationalArchimedeanSchwartz) (M : ℕ) [NeZero M]
    {a : ℝ} (ha : 0 < a) (r : Fin M) :
    (∑' k : ℤ, f (a * ((k : ℝ) * (M : ℝ) + (r : ℝ)))) =
      ∑' m : ℤ,
        (((a * (M : ℝ))⁻¹ : ℝ) : ℂ) *
          𝓕 f ((m : ℝ) / (a * (M : ℝ))) *
            fourier m (((r : ℝ) / (M : ℝ) : ℝ) : UnitAddCircle) := by
  have hM : 0 < (M : ℝ) := by
    exact_mod_cast Nat.pos_of_neZero M
  have hc : 0 < a * (M : ℝ) := mul_pos ha hM
  have h :=
    SchwartzMap.tsum_eq_tsum_fourier
      (ccmRationalArchimedeanDilation f (a * (M : ℝ)) hc.ne')
      ((r : ℝ) / (M : ℝ))
  simp_rw [ccmRationalArchimedeanDilation_apply,
    fourier_ccmRationalArchimedeanDilation f hc] at h
  convert h using 1 <;> apply tsum_congr <;> intro n
  · congr 1
    field_simp
    ring
  · norm_cast

def ccmRationalPeriodicFourierCoefficient
    (M : ℕ) [NeZero M] (w : Fin M → ℂ) (m : ℤ) : ℂ :=
  ∑ r : Fin M,
    w r * fourier m (((r : ℝ) / (M : ℝ) : ℝ) : UnitAddCircle)

def ccmRationalBoundedWeightedLatticeTrace
    (v : ℤ → ℂ) (f : CCMRationalArchimedeanSchwartz) (a : ℝ) : ℂ :=
  ∑' n : ℤ, v n * f (a * (n : ℝ))

theorem ccmRationalBoundedWeightedLatticeTrace_summable
    (v : ℤ → ℂ) (B : ℝ) (hv : ∀ n, ‖v n‖ ≤ B)
    (f : CCMRationalArchimedeanSchwartz) {a : ℝ} (ha : a ≠ 0) :
    Summable (fun n : ℤ => v n * f (a * (n : ℝ))) := by
  have hbase :
      Summable (fun n : ℤ => ‖f (a * (n : ℝ))‖) :=
    ccmRationalArchimedeanSchwartz_lattice_summable f ha
  have hmajor :
      Summable (fun n : ℤ => B * ‖f (a * (n : ℝ))‖) :=
    hbase.mul_left B
  apply Summable.of_norm_bounded hmajor
  intro n
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hv n) (norm_nonneg _)

set_option maxHeartbeats 500000 in
theorem ccmRationalBoundedWeightedLatticeTrace_norm_tsum_large_bound
    (v : ℤ → ℂ) (B : ℝ) (hv : ∀ n, ‖v n‖ ≤ B)
    (f : CCMRationalArchimedeanSchwartz) (hzero : v 0 * f 0 = 0)
    (N : ℕ) {a : ℝ} (ha : 0 < a) :
    (∑' n : ℤ, ‖v n * f (a * (n : ℝ))‖) ≤
      B * ccmRationalArchimedeanDecayConstant f N /
        a ^ ccmRationalArchimedeanDecayExponent N := by
  let p := ccmRationalArchimedeanDecayExponent N
  let S := SchwartzMap.seminorm ℂ p 0 f
  let C := S / a ^ p
  have hB : 0 ≤ B :=
    (norm_nonneg (v 0)).trans (hv 0)
  have hnorm :
      Summable (fun n : ℤ => ‖v n * f (a * (n : ℝ))‖) := by
    exact summable_norm_iff.mpr
      (ccmRationalBoundedWeightedLatticeTrace_summable v B hv f ha.ne')
  have hC : 0 ≤ C := div_nonneg (by positivity) (by positivity)
  have hmajor :
      Summable (fun n : ℤ =>
        (B * C) * ccmRationalArchimedeanPSeriesKernel N n) :=
    (ccmRationalArchimedeanPSeriesKernel_summable N).mul_left (B * C)
  have hfpoint (n : ℤ) (hn : n ≠ 0) :
      ‖f (a * (n : ℝ))‖ ≤
        C * ccmRationalArchimedeanPSeriesKernel N n := by
    have hnR : (n : ℝ) ≠ 0 := by
      exact_mod_cast hn
    have han : a * (n : ℝ) ≠ 0 := mul_ne_zero ha.ne' hnR
    have hx : 0 < ‖a * (n : ℝ)‖ ^ p :=
      pow_pos (norm_pos_iff.mpr han) _
    have hsem :=
      SchwartzMap.norm_pow_mul_le_seminorm ℂ f p
        (a * (n : ℝ))
    calc
      ‖f (a * (n : ℝ))‖ ≤
          S / ‖a * (n : ℝ)‖ ^ p := by
        apply (le_div_iff₀ hx).2
        simpa [S, mul_comm] using hsem
      _ = C * ccmRationalArchimedeanPSeriesKernel N n := by
        dsimp [C]
        rw [ccmRationalArchimedeanPSeriesKernel, if_neg hn,
          abs_mul, abs_of_pos ha]
        have hnabs : |(n : ℝ)| ≠ 0 := abs_ne_zero.mpr hnR
        rw [mul_pow]
        have habspow :
            |(n : ℝ)| ^ p = (n : ℝ) ^ p := by
          change |(n : ℝ)| ^ (2 * (N + 1)) =
            (n : ℝ) ^ (2 * (N + 1))
          rw [pow_mul, pow_mul, sq_abs]
        rw [habspow]
        field_simp
        rfl
  have hpoint (n : ℤ) :
      ‖v n * f (a * (n : ℝ))‖ ≤
        (B * C) * ccmRationalArchimedeanPSeriesKernel N n := by
    by_cases hn : n = 0
    · subst n
      simp [hzero, ccmRationalArchimedeanPSeriesKernel]
    · rw [norm_mul]
      calc
        ‖v n‖ * ‖f (a * (n : ℝ))‖ ≤
            B * ‖f (a * (n : ℝ))‖ :=
          mul_le_mul_of_nonneg_right (hv n) (norm_nonneg _)
        _ ≤ B * (C * ccmRationalArchimedeanPSeriesKernel N n) :=
          mul_le_mul_of_nonneg_left (hfpoint n hn) hB
        _ = (B * C) *
            ccmRationalArchimedeanPSeriesKernel N n := by ring
  calc
    (∑' n : ℤ, ‖v n * f (a * (n : ℝ))‖) ≤ ∑' n : ℤ,
        (B * C) * ccmRationalArchimedeanPSeriesKernel N n :=
      Summable.tsum_mono hnorm hmajor hpoint
    _ = B * ccmRationalArchimedeanDecayConstant f N /
        a ^ ccmRationalArchimedeanDecayExponent N := by
      rw [tsum_mul_left]
      simp only [C, S, p, ccmRationalArchimedeanDecayConstant]
      ring

theorem ccmRationalBoundedWeightedLatticeTrace_large_bound
    (v : ℤ → ℂ) (B : ℝ) (hv : ∀ n, ‖v n‖ ≤ B)
    (f : CCMRationalArchimedeanSchwartz) (hzero : v 0 * f 0 = 0)
    (N : ℕ) {a : ℝ} (ha : 0 < a) :
    ‖ccmRationalBoundedWeightedLatticeTrace v f a‖ ≤
      B * ccmRationalArchimedeanDecayConstant f N /
        a ^ ccmRationalArchimedeanDecayExponent N := by
  have hnorm :
      Summable (fun n : ℤ => ‖v n * f (a * (n : ℝ))‖) :=
    summable_norm_iff.mpr
      (ccmRationalBoundedWeightedLatticeTrace_summable v B hv f ha.ne')
  exact (norm_tsum_le_tsum_norm hnorm).trans
    (ccmRationalBoundedWeightedLatticeTrace_norm_tsum_large_bound
      v B hv f hzero N ha)

set_option maxHeartbeats 800000 in
theorem ccmRationalPeriodicWeightedTrace_poisson
    (M : ℕ) [NeZero M] (w : Fin M → ℂ)
    (f : CCMRationalArchimedeanSchwartz) {a : ℝ} (ha : 0 < a) :
    ccmRationalPeriodicWeightedTrace M w f a =
      ∑' m : ℤ,
        (((a * (M : ℝ))⁻¹ : ℝ) : ℂ) *
          𝓕 f ((m : ℝ) / (a * (M : ℝ))) *
            ccmRationalPeriodicFourierCoefficient M w m := by
  have hM : 0 < (M : ℝ) := by
    exact_mod_cast Nat.pos_of_neZero M
  have hc : 0 < a * (M : ℝ) := mul_pos ha hM
  let c : ℝ := a * (M : ℝ)
  let U : Fin M → ℤ → ℂ :=
    fun r m =>
      w r *
        (((c⁻¹ : ℝ) : ℂ) * 𝓕 f ((m : ℝ) / c) *
          fourier m (((r : ℝ) / (M : ℝ) : ℝ) : UnitAddCircle))
  have hFourier :
      Summable (fun m : ℤ => 𝓕 f ((m : ℝ) / c)) := by
    have h :=
      ccmRationalArchimedeanLatticeTrace_summable
        (𝓕 f) (inv_ne_zero hc.ne')
    apply h.congr
    intro m
    congr 1
    dsimp [c]
    field_simp
  have hFourierNorm :
      Summable (fun m : ℤ => ‖𝓕 f ((m : ℝ) / c)‖) :=
    summable_norm_iff.mpr hFourier
  have hU (r : Fin M) : Summable (U r) := by
    let D : ℝ := ‖w r‖ * c⁻¹
    apply Summable.of_norm_bounded (hFourierNorm.mul_left D)
    intro m
    dsimp [U, D]
    rw [norm_mul, norm_mul, norm_mul]
    simp only [Circle.norm_coe, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_inv]
    rw [abs_of_pos hc]
    dsimp [c]
    rw [mul_assoc]
  rw [ccmRationalPeriodicWeightedTrace_eq_sum_residues M w f ha.ne']
  calc
    (∑ r : Fin M, ∑' k : ℤ,
        w r * f (a * ((k : ℝ) * (M : ℝ) + (r : ℝ)))) =
        ∑ r : Fin M, w r *
          ∑' k : ℤ,
            f (a * ((k : ℝ) * (M : ℝ) + (r : ℝ))) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [tsum_mul_left]
    _ = ∑ r : Fin M, ∑' m : ℤ, U r m := by
      apply Finset.sum_congr rfl
      intro r _
      rw [ccmRationalArchimedeanShiftedLattice_poisson f M ha r]
      rw [← tsum_mul_left]
    _ = ∑' m : ℤ, ∑ r : Fin M, U r m := by
      rw [Summable.tsum_finsetSum]
      exact fun r _ => hU r
    _ = ∑' m : ℤ,
        (((a * (M : ℝ))⁻¹ : ℝ) : ℂ) *
          𝓕 f ((m : ℝ) / (a * (M : ℝ))) *
            ccmRationalPeriodicFourierCoefficient M w m := by
      apply tsum_congr
      intro m
      dsimp [U, c, ccmRationalPeriodicFourierCoefficient]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring

def ccmRationalPeriodicWeightNorm
    (M : ℕ) [NeZero M] (w : Fin M → ℂ) : ℝ :=
  ∑ r : Fin M, ‖w r‖

theorem ccmRationalPeriodicResidue_zero
    (M : ℕ) [NeZero M] :
    ccmRationalPeriodicResidue M 0 = 0 := by
  apply Fin.ext
  change (0 : ℤ).natMod (M : ℤ) = 0
  simp [Int.natMod]

theorem norm_ccmRationalPeriodicFourierCoefficient_le
    (M : ℕ) [NeZero M] (w : Fin M → ℂ) (m : ℤ) :
    ‖ccmRationalPeriodicFourierCoefficient M w m‖ ≤
      ccmRationalPeriodicWeightNorm M w := by
  rw [ccmRationalPeriodicFourierCoefficient, ccmRationalPeriodicWeightNorm]
  calc
    ‖∑ r : Fin M,
        w r * fourier m
          (((r : ℝ) / (M : ℝ) : ℝ) : UnitAddCircle)‖ ≤
        ∑ r : Fin M,
          ‖w r * fourier m
            (((r : ℝ) / (M : ℝ) : ℝ) : UnitAddCircle)‖ :=
      norm_sum_le Finset.univ _
    _ = ∑ r : Fin M, ‖w r‖ := by
      apply Finset.sum_congr rfl
      intro r _
      simp only [norm_mul, fourier_apply, Circle.norm_coe, mul_one]

theorem ccmRationalPeriodicFourierCoefficient_zero
    (M : ℕ) [NeZero M] (w : Fin M → ℂ) :
    ccmRationalPeriodicFourierCoefficient M w 0 = ∑ r : Fin M, w r := by
  rw [ccmRationalPeriodicFourierCoefficient]
  apply Finset.sum_congr rfl
  intro r _
  rw [fourier_zero, mul_one]

theorem ccmRationalPeriodicWeightedTrace_large_bound
    (M : ℕ) [NeZero M] (w : Fin M → ℂ)
    (f : CCMRationalArchimedeanSchwartz)
    (hphysical : w 0 * f 0 = 0)
    (N : ℕ) {a : ℝ} (ha : 0 < a) :
    ‖ccmRationalPeriodicWeightedTrace M w f a‖ ≤
      ccmRationalPeriodicWeightNorm M w *
        ccmRationalArchimedeanDecayConstant f N /
          a ^ ccmRationalArchimedeanDecayExponent N := by
  exact ccmRationalBoundedWeightedLatticeTrace_large_bound
    (fun n => w (ccmRationalPeriodicResidue M n))
    (ccmRationalPeriodicWeightNorm M w)
    (fun n => Finset.single_le_sum
      (fun r _ => norm_nonneg (w r)) (Finset.mem_univ _))
    f (by simpa [ccmRationalPeriodicResidue_zero M] using hphysical)
    N ha

theorem ccmRationalPeriodicWeightedTrace_poisson_as_boundedWeightedTrace
    (M : ℕ) [NeZero M] (w : Fin M → ℂ)
    (f : CCMRationalArchimedeanSchwartz) {a : ℝ} (ha : 0 < a) :
    ccmRationalPeriodicWeightedTrace M w f a =
      (((a * (M : ℝ))⁻¹ : ℝ) : ℂ) *
        ccmRationalBoundedWeightedLatticeTrace
          (ccmRationalPeriodicFourierCoefficient M w)
          (𝓕 f) (a * (M : ℝ))⁻¹ := by
  rw [ccmRationalPeriodicWeightedTrace_poisson M w f ha]
  rw [ccmRationalBoundedWeightedLatticeTrace, ← tsum_mul_left]
  congr 1
  funext m
  change
    (((a * (M : ℝ))⁻¹ : ℝ) : ℂ) *
        𝓕 f ((m : ℝ) / (a * (M : ℝ))) *
          ccmRationalPeriodicFourierCoefficient M w m =
      (((a * (M : ℝ))⁻¹ : ℝ) : ℂ) *
        (ccmRationalPeriodicFourierCoefficient M w m *
          𝓕 f ((a * (M : ℝ))⁻¹ * (m : ℝ)))
  have harg :
      (m : ℝ) / (a * (M : ℝ)) =
        (a * (M : ℝ))⁻¹ * (m : ℝ) := by
    ring
  rw [harg]
  ring

set_option maxHeartbeats 500000 in
theorem ccmRationalPeriodicWeightedTrace_small_bound
    (M : ℕ) [NeZero M] (w : Fin M → ℂ)
    (f : CCMRationalArchimedeanSchwartz)
    (hdual : (∑ r : Fin M, w r) * (𝓕 f) 0 = 0)
    (N : ℕ) {a : ℝ} (ha : 0 < a) :
    ‖ccmRationalPeriodicWeightedTrace M w f a‖ ≤
      ccmRationalPeriodicWeightNorm M w *
        ccmRationalArchimedeanDecayConstant (𝓕 f) N *
          (a * (M : ℝ)) ^
            (ccmRationalArchimedeanDecayExponent N - 1) := by
  have hM : 0 < (M : ℝ) := by
    exact_mod_cast Nat.pos_of_neZero M
  have hc : 0 < a * (M : ℝ) := mul_pos ha hM
  have hzero :
      ccmRationalPeriodicFourierCoefficient M w 0 * (𝓕 f) 0 = 0 := by
    rwa [ccmRationalPeriodicFourierCoefficient_zero]
  have hlarge :=
    ccmRationalBoundedWeightedLatticeTrace_large_bound
      (ccmRationalPeriodicFourierCoefficient M w)
      (ccmRationalPeriodicWeightNorm M w)
      (norm_ccmRationalPeriodicFourierCoefficient_le M w)
      (𝓕 f) hzero N (inv_pos.mpr hc)
  rw [ccmRationalPeriodicWeightedTrace_poisson_as_boundedWeightedTrace M w f ha,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
    abs_of_pos hc]
  calc
    (a * (M : ℝ))⁻¹ *
        ‖ccmRationalBoundedWeightedLatticeTrace
          (ccmRationalPeriodicFourierCoefficient M w)
          (𝓕 f) (a * (M : ℝ))⁻¹‖ ≤
        (a * (M : ℝ))⁻¹ *
          (ccmRationalPeriodicWeightNorm M w *
            ccmRationalArchimedeanDecayConstant (𝓕 f) N /
              ((a * (M : ℝ))⁻¹) ^
                ccmRationalArchimedeanDecayExponent N) := by
      gcongr
    _ = ccmRationalPeriodicWeightNorm M w *
        ccmRationalArchimedeanDecayConstant (𝓕 f) N *
          (a * (M : ℝ)) ^
            (ccmRationalArchimedeanDecayExponent N - 1) := by
      have hp : 1 ≤ ccmRationalArchimedeanDecayExponent N :=
        (ccmRationalArchimedeanDecayExponent_gt_one N).le
      rw [inv_pow, div_inv_eq_mul]
      have hpow :
          (a * (M : ℝ)) ^ ccmRationalArchimedeanDecayExponent N =
            (a * (M : ℝ)) ^
                (ccmRationalArchimedeanDecayExponent N - 1) *
              (a * (M : ℝ)) := by
        have hpEq : ccmRationalArchimedeanDecayExponent N =
            (ccmRationalArchimedeanDecayExponent N - 1) + 1 := by
          omega
        calc
          (a * (M : ℝ)) ^ ccmRationalArchimedeanDecayExponent N =
              (a * (M : ℝ)) ^
                ((ccmRationalArchimedeanDecayExponent N - 1) + 1) :=
            congrArg (fun q : ℕ => (a * (M : ℝ)) ^ q) hpEq
          _ = (a * (M : ℝ)) ^
                (ccmRationalArchimedeanDecayExponent N - 1) *
              (a * (M : ℝ)) := pow_succ _ _
      rw [hpow]
      field_simp

theorem ccmRationalPeriodicWeightedTrace_twoSidedDecay
    (M : ℕ) [NeZero M] (w : Fin M → ℂ)
    (f : CCMRationalArchimedeanSchwartz)
    (hphysical : w 0 * f 0 = 0)
    (hdual : (∑ r : Fin M, w r) * (∫ x : ℝ, f x) = 0)
    (N : ℕ) {a : ℝ} (ha : 0 < a) :
    ‖ccmRationalPeriodicWeightedTrace M w f a‖ ≤
        ccmRationalPeriodicWeightNorm M w *
          ccmRationalArchimedeanDecayConstant f N /
            a ^ ccmRationalArchimedeanDecayExponent N ∧
      ‖ccmRationalPeriodicWeightedTrace M w f a‖ ≤
        ccmRationalPeriodicWeightNorm M w *
          ccmRationalArchimedeanDecayConstant (𝓕 f) N *
            (a * (M : ℝ)) ^
              (ccmRationalArchimedeanDecayExponent N - 1) := by
  refine
    ⟨ccmRationalPeriodicWeightedTrace_large_bound M w f hphysical N ha, ?_⟩
  exact ccmRationalPeriodicWeightedTrace_small_bound M w f
    (by rw [fourier_ccmRationalArchimedean_zero_eq_integral, hdual])
    N ha

end RHTower
end GaloisForLFunctions
