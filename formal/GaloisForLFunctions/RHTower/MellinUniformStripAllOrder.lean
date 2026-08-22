import GaloisForLFunctions.RHTower.MellinQuinticStripDecay

/-!
# Uniform all-order Mellin decay on a bounded strip

The principal-character contour branch needs to absorb a polynomial vertical
zeta envelope whose degree is supplied existentially.  This module gives one
closed Mellin bound for every derivative order on `0 ≤ Re(s) ≤ 3`.
-/

open Complex MeasureTheory Filter Set Asymptotics
open scoped FourierTransform Topology BigOperators

namespace RHTower

noncomputable section

/-- A certified abscissa in the fixed strip for all-order Mellin bounds. -/
structure DeningerMeyerUniformStripAbscissa where
  value : ℝ
  nonneg : 0 ≤ value
  le_three : value ≤ 3

instance : Coe DeningerMeyerUniformStripAbscissa ℝ where
  coe sigma := sigma.value

/-- The exact binomial expansion of a conjugated Euler derivative. -/
theorem deningerMeyerWeightedEulerIterate_binomial
    (g : DeningerMeyerStrongLogTarget) (sigma : ℝ) (n : ℕ) :
    deningerMeyerWeightedEulerIterate sigma n (g : ℝ → ℂ) =
      fun t => ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℂ) * (sigma : ℂ) ^ (n - k) *
          iteratedDeriv k (g : ℝ → ℂ) t := by
  induction n with
  | zero =>
      funext t
      simp [deningerMeyerWeightedEulerIterate]
  | succ n ih =>
      have hd (k : ℕ) : Differentiable ℝ (iteratedDeriv k (g : ℝ → ℂ)) := by
        exact g.property.smooth.differentiable_iteratedDeriv k
          (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top k))
      have hderiv : deriv (fun t => ∑ k ∈ Finset.range (n + 1),
          (n.choose k : ℂ) * (sigma : ℂ) ^ (n - k) *
            iteratedDeriv k (g : ℝ → ℂ) t) =
          fun t => ∑ k ∈ Finset.range (n + 1),
            (n.choose k : ℂ) * (sigma : ℂ) ^ (n - k) *
              iteratedDeriv (k + 1) (g : ℝ → ℂ) t := by
        funext t
        have hsum :
            (fun u => ∑ k ∈ Finset.range (n + 1),
              (n.choose k : ℂ) * (sigma : ℂ) ^ (n - k) *
                iteratedDeriv k (g : ℝ → ℂ) u) =
              ∑ k ∈ Finset.range (n + 1), fun u =>
                (n.choose k : ℂ) * (sigma : ℂ) ^ (n - k) *
                  iteratedDeriv k (g : ℝ → ℂ) u := by
          funext u
          simp only [Finset.sum_apply]
        rw [hsum]
        simpa only [← iteratedDeriv_succ] using
          (HasDerivAt.sum (u := Finset.range (n + 1)) fun k _ =>
            ((hd k t).hasDerivAt.const_mul
              ((n.choose k : ℂ) * (sigma : ℂ) ^ (n - k)))).deriv
      rw [show deningerMeyerWeightedEulerIterate sigma n.succ (g : ℝ → ℂ) =
        deningerMeyerWeightedEuler sigma
          (deningerMeyerWeightedEulerIterate sigma n (g : ℝ → ℂ)) by rfl, ih]
      unfold deningerMeyerWeightedEuler
      rw [hderiv]
      funext t
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      rw [Finset.sum_range_succ']
      rw [Finset.sum_range_succ]
      conv_rhs =>
        rw [Finset.sum_range_succ']
        rw [Finset.sum_range_succ]
      have hmiddle :
          (∑ k ∈ Finset.range n,
              (sigma : ℂ) * ((n.choose (k + 1) : ℂ) *
                (sigma : ℂ) ^ (n - (k + 1)) *
                iteratedDeriv (k + 1) (g : ℝ → ℂ) t)) +
            ∑ k ∈ Finset.range n,
              (n.choose k : ℂ) * (sigma : ℂ) ^ (n - k) *
                iteratedDeriv (k + 1) (g : ℝ → ℂ) t =
          ∑ k ∈ Finset.range n,
            ((n + 1).choose (k + 1) : ℂ) * (sigma : ℂ) ^
                (n + 1 - (k + 1)) *
              iteratedDeriv (k + 1) (g : ℝ → ℂ) t := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        have hklt : k < n := Finset.mem_range.mp hk
        have hpow : n - k = n - (k + 1) + 1 := by omega
        simp only [Nat.succ_eq_add_one, Nat.succ_sub_succ_eq_sub,
          Nat.choose_succ_succ, Nat.cast_add]
        rw [hpow, pow_succ]
        ring
      calc
        _ =
            ((∑ k ∈ Finset.range n,
                (sigma : ℂ) * ((n.choose (k + 1) : ℂ) *
                  (sigma : ℂ) ^ (n - (k + 1)) *
                  iteratedDeriv (k + 1) (g : ℝ → ℂ) t)) +
              ∑ k ∈ Finset.range n,
                (n.choose k : ℂ) * (sigma : ℂ) ^ (n - k) *
                  iteratedDeriv (k + 1) (g : ℝ → ℂ) t) +
            ((sigma : ℂ) * ((n.choose 0 : ℂ) * (sigma : ℂ) ^ (n - 0) *
                iteratedDeriv 0 (g : ℝ → ℂ) t) +
              (n.choose n : ℂ) * (sigma : ℂ) ^ (n - n) *
                iteratedDeriv (n + 1) (g : ℝ → ℂ) t) := by
              abel
        _ =
            (∑ k ∈ Finset.range n,
              ((n + 1).choose (k + 1) : ℂ) * (sigma : ℂ) ^
                  (n + 1 - (k + 1)) *
                iteratedDeriv (k + 1) (g : ℝ → ℂ) t) +
            ((sigma : ℂ) * ((n.choose 0 : ℂ) * (sigma : ℂ) ^ (n - 0) *
                iteratedDeriv 0 (g : ℝ → ℂ) t) +
              (n.choose n : ℂ) * (sigma : ℂ) ^ (n - n) *
                iteratedDeriv (n + 1) (g : ℝ → ℂ) t) := by
              rw [hmiddle]
      simp only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one,
        Nat.sub_zero, Nat.sub_self, pow_zero, mul_one, one_mul]
      have hpow : (sigma : ℂ) ^ (n + 1) =
          (sigma : ℂ) * (sigma : ℂ) ^ n := by
        calc
          (sigma : ℂ) ^ (n + 1) = (sigma : ℂ) ^ n * (sigma : ℂ) := by
            exact pow_succ _ _
          _ = (sigma : ℂ) * (sigma : ℂ) ^ n := by ring
      rw [hpow]
      ring

private theorem deningerMeyerStrongLogDecay_iteratedDeriv
    {g : ℝ → ℂ} (hg : DeningerMeyerStrongLogDecay g) (n : ℕ) :
    DeningerMeyerStrongLogDecay (iteratedDeriv n g) := by
  induction n with
  | zero => simpa using hg
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

/-- One integrable majorant for all weighted Euler derivatives of order `n`
throughout `0 ≤ σ ≤ 3`. -/
def deningerMeyerUniformStripMajorant
    (g : DeningerMeyerStrongLogTarget) (n : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (n.choose k : ℝ) * 3 ^ (n - k) *
      (Real.exp (3 * |t|) * ‖iteratedDeriv k (g : ℝ → ℂ) t‖)

theorem integrable_deningerMeyerUniformStripMajorant
    (g : DeningerMeyerStrongLogTarget) (n : ℕ) :
    Integrable (deningerMeyerUniformStripMajorant g n) := by
  unfold deningerMeyerUniformStripMajorant
  have hsum : Integrable (∑ k ∈ Finset.range (n + 1), fun t : ℝ =>
      (n.choose k : ℝ) * 3 ^ (n - k) *
        (Real.exp (3 * |t|) * ‖iteratedDeriv k (g : ℝ → ℂ) t‖)) := by
    apply integrable_finsetSum'
    intro k _hk
    have hbase : Integrable (fun t : ℝ =>
        Real.exp (3 * |t|) * ‖iteratedDeriv k (g : ℝ → ℂ) t‖) := by
      convert integrable_deningerMeyerStrongLogAbsMoment
        (deningerMeyerStrongLogDecay_iteratedDeriv g.property k) 0 3 using 1
      funext t
      simp
    simpa only [mul_assoc] using
      hbase.const_mul ((n.choose k : ℝ) * 3 ^ (n - k))
  have heq :
      (fun t : ℝ => ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * 3 ^ (n - k) *
          (Real.exp (3 * |t|) * ‖iteratedDeriv k (g : ℝ → ℂ) t‖)) =
        ∑ k ∈ Finset.range (n + 1), fun t : ℝ =>
          (n.choose k : ℝ) * 3 ^ (n - k) *
            (Real.exp (3 * |t|) * ‖iteratedDeriv k (g : ℝ → ℂ) t‖) := by
    funext t
    simp only [Finset.sum_apply]
  rw [heq]
  exact hsum

private theorem norm_deningerMeyerWeightedEulerIterate_le_uniformMajorant
    (g : DeningerMeyerStrongLogTarget) (n : ℕ)
    (sigma : DeningerMeyerUniformStripAbscissa) (t : ℝ) :
    ‖deningerMeyerWeightedEulerIterate sigma.value n (g : ℝ → ℂ) t‖ ≤
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * 3 ^ (n - k) *
          ‖iteratedDeriv k (g : ℝ → ℂ) t‖ := by
  rw [deningerMeyerWeightedEulerIterate_binomial g sigma.value n]
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1),
        ‖(n.choose k : ℂ) * (sigma.value : ℂ) ^ (n - k) *
          iteratedDeriv k (g : ℝ → ℂ) t‖ :=
      norm_sum_le _ _
    _ = ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * sigma.value ^ (n - k) *
          ‖iteratedDeriv k (g : ℝ → ℂ) t‖ := by
      apply Finset.sum_congr rfl
      intro k _hk
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg sigma.nonneg, norm_natCast]
    _ ≤ ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * 3 ^ (n - k) *
          ‖iteratedDeriv k (g : ℝ → ℂ) t‖ := by
      apply Finset.sum_le_sum
      intro k _hk
      have hpow : sigma.value ^ (n - k) ≤ 3 ^ (n - k) := by
        exact pow_le_pow_left₀ sigma.nonneg sigma.le_three _
      gcongr

/-- Closed all-order uniform Mellin bound on the certified strip `0 ≤ Re(s) ≤ 3`. -/
theorem abs_im_pow_mul_norm_deningerMeyerStrongLogMellin_le_uniform
    (g : DeningerMeyerStrongLogTarget) (n : ℕ)
    (sigma : DeningerMeyerUniformStripAbscissa) (tau : ℝ) :
    |tau| ^ n * ‖deningerMeyerStrongLogMellin g
        ((sigma.value : ℂ) + (tau : ℂ) * I)‖ ≤
      ∫ t : ℝ, deningerMeyerUniformStripMajorant g n t := by
  have hbase :=
    abs_im_pow_mul_norm_deningerMeyerStrongLogMellin_le
      g n sigma.value tau
  have hinterior :=
    integrable_iteratedDeriv_deningerMeyerWeightedLogProfile
      g.property sigma.value n |>.norm
  apply hbase.trans
  apply integral_mono hinterior
    (integrable_deningerMeyerUniformStripMajorant g n)
  intro t
  rw [iteratedDeriv_deningerMeyerWeightedLogProfile g.property sigma.value n]
  simp only [deningerMeyerWeightedLogProfile]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have hst : sigma.value * t ≤ 3 * |t| := by
    calc
      sigma.value * t ≤ |sigma.value * t| := le_abs_self _
      _ = sigma.value * |t| := by
        rw [abs_mul, abs_of_nonneg sigma.nonneg]
      _ ≤ 3 * |t| :=
        mul_le_mul_of_nonneg_right sigma.le_three (abs_nonneg t)
  have hexp : Real.exp (sigma.value * t) ≤ Real.exp (3 * |t|) :=
    Real.exp_le_exp.mpr hst
  have hEuler := norm_deningerMeyerWeightedEulerIterate_le_uniformMajorant
    g n sigma t
  have hmajorant_nonneg : 0 ≤
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * 3 ^ (n - k) *
          ‖iteratedDeriv k (g : ℝ → ℂ) t‖ := by
    positivity
  calc
    Real.exp (sigma.value * t) *
        ‖deningerMeyerWeightedEulerIterate sigma.value n (g : ℝ → ℂ) t‖ ≤
      Real.exp (sigma.value * t) *
        ∑ k ∈ Finset.range (n + 1),
          (n.choose k : ℝ) * 3 ^ (n - k) *
            ‖iteratedDeriv k (g : ℝ → ℂ) t‖ :=
      mul_le_mul_of_nonneg_left hEuler (Real.exp_pos _).le
    _ ≤ Real.exp (3 * |t|) *
        ∑ k ∈ Finset.range (n + 1),
          (n.choose k : ℝ) * 3 ^ (n - k) *
            ‖iteratedDeriv k (g : ℝ → ℂ) t‖ :=
      mul_le_mul_of_nonneg_right hexp hmajorant_nonneg
    _ = deningerMeyerUniformStripMajorant g n t := by
      unfold deningerMeyerUniformStripMajorant
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      ring

end

end RHTower
