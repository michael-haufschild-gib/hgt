import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspSchwartz

/-!
# Exponential tilts of the theta-cusp Schwartz source

For every real aperture `a` with `|a| < 1`, multiplication of the theta-cusp source by
`exp (a x)` remains in Schwartz space.  The proof is quantitative: every derivative has the
residual exponential decay rate `1 - |a|`, and every Schwartz seminorm receives an explicit
factorial bound.

This is the physical source required to read Xi on a horizontally shifted spectral line.  The
Fourier identification with that shifted Xi line is deliberately separate from the present
source-space theorem.
-/

open Complex Real Set Filter Topology
open scoped SchwartzMap

noncomputable section

namespace RHTower

def thetaCuspTiltedSource (a x : ℝ) : ℝ :=
  Real.exp (a * x) * thetaCuspFullSource x

theorem contDiff_thetaCuspTiltedSource (a : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (thetaCuspTiltedSource a) := by
  unfold thetaCuspTiltedSource
  exact (Real.contDiff_exp.comp
    (contDiff_const.mul contDiff_id)).mul contDiff_thetaCuspFullSource

theorem iteratedDeriv_thetaCuspTiltedSource (a : ℝ) (m : ℕ) (x : ℝ) :
    iteratedDeriv m (thetaCuspTiltedSource a) x =
      ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * (a ^ i * Real.exp (a * x)) *
          iteratedDeriv (m - i) thetaCuspFullSource x := by
  have hm : ((m : ℕ∞) : WithTop ℕ∞) ≤
      ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤)
  have hexp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : ℝ => Real.exp (a * y)) :=
    Real.contDiff_exp.comp
      ((contDiff_const : ContDiff ℝ _ (fun _ : ℝ => a)).mul contDiff_id)
  have h := iteratedDeriv_mul
    (f := fun y : ℝ => Real.exp (a * y))
    (g := thetaCuspFullSource) (n := m) (x := x)
    (hexp.contDiffAt.of_le hm)
    (contDiff_thetaCuspFullSource.contDiffAt.of_le hm)
  change iteratedDeriv m
    ((fun y : ℝ => Real.exp (a * y)) * thetaCuspFullSource) x = _
  rw [h]
  apply Finset.sum_congr rfl
  intro i hi
  rw [congrFun (iteratedDeriv_exp_const_mul i a) x]

theorem abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg_abs
    (m : ℕ) (x : ℝ) :
    |iteratedDeriv m thetaCuspFullSource x| ≤
      thetaCuspDerivativeExpConstant m * Real.exp (-|x|) := by
  let y : ℝ := |x|
  have hy : 0 ≤ y := abs_nonneg x
  have hder : |iteratedDeriv m thetaCuspFullSource x| =
      |iteratedDeriv m thetaCuspFullSource y| := by
    rcases le_or_gt 0 x with hx | hx
    · simp [y, abs_of_nonneg hx]
    · have href := abs_iteratedDeriv_thetaCuspFullSource_neg m (-x)
      simpa [y, abs_of_neg hx] using href
  rw [hder]
  exact abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg m hy

def thetaCuspTiltedDerivativeConstant (a : ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1),
    (m.choose i : ℝ) * |a| ^ i * thetaCuspDerivativeExpConstant (m - i)

theorem thetaCuspTiltedDerivativeConstant_nonneg (a : ℝ) (m : ℕ) :
    0 ≤ thetaCuspTiltedDerivativeConstant a m := by
  unfold thetaCuspTiltedDerivativeConstant
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (abs_nonneg a) _))
    (thetaCuspDerivativeExpConstant_nonneg _)

theorem abs_iteratedDeriv_thetaCuspTiltedSource_le
    (a : ℝ) (m : ℕ) (x : ℝ) :
    |iteratedDeriv m (thetaCuspTiltedSource a) x| ≤
      thetaCuspTiltedDerivativeConstant a m *
        Real.exp (-(1 - |a|) * |x|) := by
  rw [iteratedDeriv_thetaCuspTiltedSource]
  calc
    |∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * (a ^ i * Real.exp (a * x)) *
          iteratedDeriv (m - i) thetaCuspFullSource x| ≤
        ∑ i ∈ Finset.range (m + 1),
          |(m.choose i : ℝ) * (a ^ i * Real.exp (a * x)) *
            iteratedDeriv (m - i) thetaCuspFullSource x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (m + 1),
        ((m.choose i : ℝ) * |a| ^ i *
          thetaCuspDerivativeExpConstant (m - i)) *
            Real.exp (-(1 - |a|) * |x|) := by
      apply Finset.sum_le_sum
      intro i hi
      have hsource :=
        abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg_abs (m - i) x
      have hax : a * x ≤ |a| * |x| := by
        calc
          a * x ≤ |a * x| := le_abs_self _
          _ = |a| * |x| := abs_mul a x
      have hexp : Real.exp (a * x) ≤ Real.exp (|a| * |x|) :=
        Real.exp_le_exp.mpr hax
      have hC := thetaCuspDerivativeExpConstant_nonneg (m - i)
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_mul, abs_pow,
        abs_of_pos (Real.exp_pos _)]
      calc
        (m.choose i : ℝ) * (|a| ^ i * Real.exp (a * x)) *
            |iteratedDeriv (m - i) thetaCuspFullSource x| ≤
          (m.choose i : ℝ) * (|a| ^ i * Real.exp (|a| * |x|)) *
            (thetaCuspDerivativeExpConstant (m - i) * Real.exp (-|x|)) := by
              gcongr
        _ = ((m.choose i : ℝ) * |a| ^ i *
              thetaCuspDerivativeExpConstant (m - i)) *
                Real.exp (-(1 - |a|) * |x|) := by
          have he : Real.exp (|a| * |x|) * Real.exp (-|x|) =
              Real.exp (-(1 - |a|) * |x|) := by
            rw [← Real.exp_add]
            congr 1
            ring
          rw [show (m.choose i : ℝ) * (|a| ^ i * Real.exp (|a| * |x|)) *
                (thetaCuspDerivativeExpConstant (m - i) * Real.exp (-|x|)) =
              ((m.choose i : ℝ) * |a| ^ i *
                thetaCuspDerivativeExpConstant (m - i)) *
                  (Real.exp (|a| * |x|) * Real.exp (-|x|)) by ring,
            he]
    _ = thetaCuspTiltedDerivativeConstant a m *
        Real.exp (-(1 - |a|) * |x|) := by
      rw [thetaCuspTiltedDerivativeConstant, Finset.sum_mul]

theorem pow_mul_exp_neg_mul_le_factorial_div
    (k : ℕ) {c y : ℝ} (hc : 0 < c) (hy : 0 ≤ y) :
    y ^ k * Real.exp (-c * y) ≤ (Nat.factorial k : ℝ) / c ^ k := by
  rw [le_div_iff₀ (pow_pos hc k)]
  have h := pow_mul_exp_neg_le_factorial k (mul_nonneg hc.le hy)
  calc
    y ^ k * Real.exp (-c * y) * c ^ k =
        (c * y) ^ k * Real.exp (-(c * y)) := by ring
    _ ≤ (Nat.factorial k : ℝ) := h

theorem weighted_iteratedDeriv_thetaCuspTiltedSource_le
    {a : ℝ} (ha : |a| < 1) (k m : ℕ) (x : ℝ) :
    ‖x‖ ^ k * ‖iteratedDeriv m (thetaCuspTiltedSource a) x‖ ≤
      thetaCuspTiltedDerivativeConstant a m *
        ((Nat.factorial k : ℝ) / (1 - |a|) ^ k) := by
  have hc : 0 < 1 - |a| := sub_pos.mpr ha
  have hder := abs_iteratedDeriv_thetaCuspTiltedSource_le a m x
  have hpow := pow_mul_exp_neg_mul_le_factorial_div k hc (abs_nonneg x)
  have hC := thetaCuspTiltedDerivativeConstant_nonneg a m
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  calc
    |x| ^ k * |iteratedDeriv m (thetaCuspTiltedSource a) x| ≤
        |x| ^ k * (thetaCuspTiltedDerivativeConstant a m *
          Real.exp (-(1 - |a|) * |x|)) := by gcongr
    _ = thetaCuspTiltedDerivativeConstant a m *
        (|x| ^ k * Real.exp (-(1 - |a|) * |x|)) := by ring
    _ ≤ thetaCuspTiltedDerivativeConstant a m *
        ((Nat.factorial k : ℝ) / (1 - |a|) ^ k) :=
      mul_le_mul_of_nonneg_left hpow hC

def thetaCuspTiltedSchwartzReal (a : ℝ) (ha : |a| < 1) : 𝓢(ℝ, ℝ) where
  toFun := thetaCuspTiltedSource a
  smooth' := contDiff_thetaCuspTiltedSource a
  decay' k m := by
    refine ⟨thetaCuspTiltedDerivativeConstant a m *
      ((Nat.factorial k : ℝ) / (1 - |a|) ^ k), ?_⟩
    intro x
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact weighted_iteratedDeriv_thetaCuspTiltedSource_le ha k m x

@[simp] theorem thetaCuspTiltedSchwartzReal_apply
    (a : ℝ) (ha : |a| < 1) (x : ℝ) :
    thetaCuspTiltedSchwartzReal a ha x = thetaCuspTiltedSource a x := rfl

def thetaCuspTiltedSchwartz (a : ℝ) (ha : |a| < 1) : 𝓢(ℝ, ℂ) :=
  (thetaCuspTiltedSchwartzReal a ha).postcompCLM Complex.ofRealCLM

@[simp] theorem thetaCuspTiltedSchwartz_apply
    (a : ℝ) (ha : |a| < 1) (x : ℝ) :
    thetaCuspTiltedSchwartz a ha x =
      (Real.exp (a * x) * thetaCuspFullSource x : ℝ) := rfl

end RHTower
