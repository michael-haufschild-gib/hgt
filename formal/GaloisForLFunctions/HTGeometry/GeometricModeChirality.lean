import GaloisForLFunctions.HTGeometry.PositiveJumpFormationChirality
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Chirality of one geometric formation mode

A geometric occupation mode with ratio `a ∈ (0,1)` and jump size `λ > 0` is exactly a
compound-Poisson formation with the discrete Lévy measure `∑_{k ≥ 1} (a^k / k) δ_{kλ}`: this is the
logarithmic series `−log(1−x) = ∑ x^k / k` read as a Laplace exponent.  Its directed information
commutator is therefore the kernel series

`χ(s,t) = ∑_{k ≥ 1} (a^k / k) e^{−s k λ} K((t−s) k λ)`,

which is strictly positive whenever `s < t`.
-/

open scoped Topology

namespace GaloisForLFunctions.HTGeometry

variable {a lam s t : ℝ}

/-- Occupation ratio of a geometric mode at Esscher parameter `t`. -/
noncomputable def modeRatio (a lam t : ℝ) : ℝ := a * Real.exp (-(lam * t))

theorem modeRatio_pos (ha : 0 < a) (lam t : ℝ) : 0 < modeRatio a lam t :=
  mul_pos ha (Real.exp_pos _)

theorem modeRatio_lt_one (ha0 : 0 < a) (ha1 : a < 1) (hlam : 0 < lam) (ht : 0 ≤ t) :
    modeRatio a lam t < 1 := by
  have hexp : Real.exp (-(lam * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  calc modeRatio a lam t = a * Real.exp (-(lam * t)) := rfl
    _ ≤ a * 1 := by
        exact mul_le_mul_of_nonneg_left hexp ha0.le
    _ < 1 := by simpa using ha1

/-- Log partition of a geometric mode. -/
noncomputable def modeLogPartition (a lam t : ℝ) : ℝ := -Real.log (1 - modeRatio a lam t)

/-- First response of a geometric mode. -/
noncomputable def modeFirstMoment (a lam t : ℝ) : ℝ :=
  lam * (modeRatio a lam t / (1 - modeRatio a lam t))

/-- Second response of a geometric mode. -/
noncomputable def modeSecondResponse (a lam t : ℝ) : ℝ :=
  lam ^ 2 * (modeRatio a lam t / (1 - modeRatio a lam t) ^ 2)

/-- Third response of a geometric mode. -/
noncomputable def modeThirdCumulant (a lam t : ℝ) : ℝ :=
  lam ^ 3 * (modeRatio a lam t * (1 + modeRatio a lam t) / (1 - modeRatio a lam t) ^ 3)

theorem hasDerivAt_modeRatio (a lam t : ℝ) :
    HasDerivAt (modeRatio a lam) (-(lam * modeRatio a lam t)) t := by
  have hin : HasDerivAt (fun x : ℝ => -(lam * x)) (-lam) t :=
    HasDerivAt.congr_deriv (((hasDerivAt_id t).const_mul lam).neg) (by ring)
  exact HasDerivAt.congr_deriv (hin.exp.const_mul a) (by simp only [modeRatio]; ring)

private theorem hasDerivAt_one_sub_modeRatio (a lam t : ℝ) :
    HasDerivAt (fun x : ℝ => 1 - modeRatio a lam x) (lam * modeRatio a lam t) t :=
  HasDerivAt.congr_deriv ((hasDerivAt_modeRatio a lam t).const_sub 1) (by ring)

/-- **(FCRM.21), first step.**  The mode log partition has derivative minus its first response. -/
theorem hasDerivAt_modeLogPartition (h1 : modeRatio a lam t < 1) :
    HasDerivAt (modeLogPartition a lam) (-(modeFirstMoment a lam t)) t := by
  have hne : 1 - modeRatio a lam t ≠ 0 := by linarith
  have hlog := (hasDerivAt_one_sub_modeRatio a lam t).log hne
  exact HasDerivAt.congr_deriv hlog.neg (by simp only [modeFirstMoment]; field_simp)

/-- **(FCRM.21), second step.**  The first response has derivative minus the second response. -/
theorem hasDerivAt_modeFirstMoment (h1 : modeRatio a lam t < 1) :
    HasDerivAt (modeFirstMoment a lam) (-(modeSecondResponse a lam t)) t := by
  have hne : 1 - modeRatio a lam t ≠ 0 := by linarith
  have hdiv := (hasDerivAt_modeRatio a lam t).div (hasDerivAt_one_sub_modeRatio a lam t) hne
  rw [Pi.div_def] at hdiv
  refine HasDerivAt.congr_deriv (hdiv.const_mul lam) ?_
  simp only [modeSecondResponse]
  field_simp
  ring

/-- **(FCRM.21), third step.**  The second response has derivative minus the third cumulant. -/
theorem hasDerivAt_modeSecondResponse (h1 : modeRatio a lam t < 1) :
    HasDerivAt (modeSecondResponse a lam) (-(modeThirdCumulant a lam t)) t := by
  have hne : 1 - modeRatio a lam t ≠ 0 := by linarith
  have hne2 : (1 - modeRatio a lam t) ^ 2 ≠ 0 := pow_ne_zero 2 hne
  have hsub := hasDerivAt_one_sub_modeRatio a lam t
  have hsq : HasDerivAt (fun x : ℝ => (1 - modeRatio a lam x) ^ 2)
      (2 * (1 - modeRatio a lam t) * (lam * modeRatio a lam t)) t := by
    have h := hsub.mul hsub
    rw [Pi.mul_def] at h
    have hfun : (fun x : ℝ => (1 - modeRatio a lam x) * (1 - modeRatio a lam x))
        = fun x : ℝ => (1 - modeRatio a lam x) ^ 2 := by
      funext x; ring
    rw [hfun] at h
    exact HasDerivAt.congr_deriv h (by ring)
  have hdiv := (hasDerivAt_modeRatio a lam t).div hsq hne2
  rw [Pi.div_def] at hdiv
  refine HasDerivAt.congr_deriv (hdiv.const_mul (lam ^ 2)) ?_
  simp only [modeThirdCumulant]
  field_simp
  ring

theorem modeSecondResponse_pos (hlam : 0 < lam)
    (h0 : 0 < modeRatio a lam t) (h1 : modeRatio a lam t < 1) :
    0 < modeSecondResponse a lam t := by
  have hden : 0 < (1 - modeRatio a lam t) ^ 2 := by positivity
  simp only [modeSecondResponse]
  positivity

/-- **(FCRM.14), (FCRM.18) mode form.**  The third response of a geometric mode is strictly
positive. -/
theorem modeThirdCumulant_pos (hlam : 0 < lam)
    (h0 : 0 < modeRatio a lam t) (h1 : modeRatio a lam t < 1) :
    0 < modeThirdCumulant a lam t := by
  have hden : 0 < (1 - modeRatio a lam t) ^ 3 := by positivity
  have hnum : 0 < modeRatio a lam t * (1 + modeRatio a lam t) := by nlinarith
  simp only [modeThirdCumulant]
  positivity

/-- Directed information commutator of a geometric mode. -/
noncomputable def modeChirality (a lam s t : ℝ) : ℝ :=
  2 * (modeLogPartition a lam t - modeLogPartition a lam s)
    + (t - s) * (modeFirstMoment a lam s + modeFirstMoment a lam t)

/-- The `k`-th power of the mode ratio is the Esscher weight of the `k`-th jump. -/
theorem modeRatio_pow (a lam t : ℝ) (k : ℕ) :
    modeRatio a lam t ^ (k + 1) = a ^ (k + 1) * Real.exp (-(t * (((k : ℝ) + 1) * lam))) := by
  rw [modeRatio, mul_pow, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- **The Lévy series of one geometric mode.**  Its log partition is the compound-Poisson Laplace
exponent of the measure `∑_{k ≥ 1} (a^k/k) δ_{kλ}`. -/
theorem hasSum_modeLogPartition (h0 : 0 < modeRatio a lam t) (h1 : modeRatio a lam t < 1) :
    HasSum (fun k : ℕ =>
        a ^ (k + 1) / ((k : ℝ) + 1) * Real.exp (-(t * (((k : ℝ) + 1) * lam))))
      (modeLogPartition a lam t) := by
  have habs : |modeRatio a lam t| < 1 := by rw [abs_of_pos h0]; exact h1
  refine (Real.hasSum_pow_div_log_of_abs_lt_one habs).congr_fun fun k => ?_
  rw [modeRatio_pow]
  ring

/-- **(FCRM.17)  The Lévy measure of one geometric mode.**  Its Laplace exponent relative to the
untilted mode is the compound-Poisson exponent of the discrete measure `∑_{k ≥ 1} (a^k/k) δ_{kλ}`. -/
theorem hasSum_modeLogPartition_sub (h0 : 0 < a) (h1 : a < 1)
    (ht0 : 0 < modeRatio a lam t) (ht1 : modeRatio a lam t < 1) :
    HasSum (fun k : ℕ =>
        a ^ (k + 1) / ((k : ℝ) + 1) * (Real.exp (-(t * (((k : ℝ) + 1) * lam))) - 1))
      (modeLogPartition a lam t - modeLogPartition a lam 0) := by
  have hz0 : modeRatio a lam 0 = a := by simp [modeRatio]
  have hzt := hasSum_modeLogPartition ht0 ht1
  have hz : HasSum (fun k : ℕ =>
      a ^ (k + 1) / ((k : ℝ) + 1) * Real.exp (-((0 : ℝ) * (((k : ℝ) + 1) * lam))))
      (modeLogPartition a lam 0) :=
    hasSum_modeLogPartition (by rw [hz0]; exact h0) (by rw [hz0]; exact h1)
  refine (hzt.sub hz).congr_fun fun k => ?_
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one]
  ring

/-- **The first response of one geometric mode is the Lévy first moment.** -/
theorem hasSum_modeFirstMoment (h0 : 0 < modeRatio a lam t) (h1 : modeRatio a lam t < 1) :
    HasSum (fun k : ℕ => a ^ (k + 1) / ((k : ℝ) + 1) * (((k : ℝ) + 1) * lam)
        * Real.exp (-(t * (((k : ℝ) + 1) * lam))))
      (modeFirstMoment a lam t) := by
  have hne : 1 - modeRatio a lam t ≠ 0 := by linarith
  have hgeo := (hasSum_geometric_of_lt_one h0.le h1).mul_left (modeRatio a lam t)
  have hrw : (fun n : ℕ => modeRatio a lam t * modeRatio a lam t ^ n)
      = fun n : ℕ => modeRatio a lam t ^ (n + 1) := by
    funext n; ring
  rw [hrw] at hgeo
  have hval : modeRatio a lam t * (1 - modeRatio a lam t)⁻¹
      = modeRatio a lam t / (1 - modeRatio a lam t) := by
    rw [div_eq_mul_inv]
  rw [hval] at hgeo
  have hmul := hgeo.mul_left lam
  rw [← modeFirstMoment] at hmul
  refine hmul.congr_fun fun k => ?_
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  rw [modeRatio_pow]
  field_simp

/-- **The exact chirality series of one geometric mode.** -/
theorem hasSum_modeChirality
    (hs0 : 0 < modeRatio a lam s) (hs1 : modeRatio a lam s < 1)
    (ht0 : 0 < modeRatio a lam t) (ht1 : modeRatio a lam t < 1) :
    HasSum (fun k : ℕ => a ^ (k + 1) / ((k : ℝ) + 1)
        * (Real.exp (-(s * (((k : ℝ) + 1) * lam)))
          * formationKernel ((t - s) * (((k : ℝ) + 1) * lam))))
      (modeChirality a lam s t) := by
  have hFt := hasSum_modeLogPartition ht0 ht1
  have hFs := hasSum_modeLogPartition hs0 hs1
  have hms := hasSum_modeFirstMoment hs0 hs1
  have hmt := hasSum_modeFirstMoment ht0 ht1
  have hcomb := ((hFt.sub hFs).mul_left 2).add ((hms.add hmt).mul_left (t - s))
  rw [← modeChirality] at hcomb
  refine hcomb.congr_fun fun k => ?_
  rw [← formationKernel_pointwise s t (((k : ℝ) + 1) * lam)]
  ring

/-- **Strict mode chirality.**  A geometric formation mode orients every ordered pair. -/
theorem modeChirality_pos (ha0 : 0 < a) (hlam : 0 < lam)
    (hs0 : 0 < modeRatio a lam s) (hs1 : modeRatio a lam s < 1)
    (ht0 : 0 < modeRatio a lam t) (ht1 : modeRatio a lam t < 1) (hst : s < t) :
    0 < modeChirality a lam s t := by
  have hsum := hasSum_modeChirality hs0 hs1 ht0 ht1
  have hpos : ∀ k : ℕ, 0 < a ^ (k + 1) / ((k : ℝ) + 1)
      * (Real.exp (-(s * (((k : ℝ) + 1) * lam)))
        * formationKernel ((t - s) * (((k : ℝ) + 1) * lam))) := by
    intro k
    have hx : (0 : ℝ) < ((k : ℝ) + 1) * lam := by positivity
    have hc : (0 : ℝ) < a ^ (k + 1) / ((k : ℝ) + 1) := by positivity
    exact mul_pos hc (mul_pos (Real.exp_pos _)
      (formationKernel_pos (mul_pos (sub_pos.mpr hst) hx)))
  rw [← hsum.tsum_eq]
  exact Summable.tsum_pos hsum.summable (fun k => (hpos k).le) 0 (hpos 0)

end GaloisForLFunctions.HTGeometry
