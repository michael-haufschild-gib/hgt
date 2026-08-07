import Mathlib

/-!
# The prime-only normal profile and its binomial resolvent

The differentiated prime-only physical boundary normal equation

`(2L − t) F'(L) + F(L) = 0`

has, in the spectral coordinate, the explicit solution `F_β(L) = β (L − t/2)^{−1/2}`, whose
half-log trace is `β` exactly.  Expanding the square root produces the central binomial
coefficients graded by `8^{-k}`, which is the card's resolvent expansion.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

/-- The prime-only normal profile with half-log trace `β`, in the scalar spectral coordinate. -/
noncomputable def primeNormalProfile (t β L : ℝ) : ℝ := β * (L - t / 2) ^ (-(1:ℝ)/2)

/-- **The profile solves the differentiated prime-only normal equation `(1)`.** -/
theorem hasDerivAt_primeNormalProfile {t β L : ℝ} (hL : t / 2 < L) :
    HasDerivAt (primeNormalProfile t β)
      (-(β / 2) * (L - t / 2) ^ (-(3:ℝ)/2)) L := by
  have hpos : (0:ℝ) < L - t / 2 := by linarith
  have hbase : HasDerivAt (fun x : ℝ => x - t / 2) 1 L := by
    simpa using (hasDerivAt_id L).sub_const (t / 2)
  have h := (Real.hasDerivAt_rpow_const (p := -(1:ℝ)/2) (Or.inl (ne_of_gt hpos))).comp L hbase
  have hval : (-(1:ℝ)/2 * (L - t/2) ^ (-(1:ℝ)/2 - 1)) * 1
      = -(1/2) * (L - t / 2) ^ (-(3:ℝ)/2) := by
    norm_num
  rw [hval] at h
  have hfin := h.const_mul β
  have hv : β * (-(1/2) * (L - t / 2) ^ (-(3:ℝ)/2))
      = -(β / 2) * (L - t / 2) ^ (-(3:ℝ)/2) := by ring
  rw [hv] at hfin
  exact hfin

/-- **The equation `(1)` holds:** `(2L − t) F' + F = 0`. -/
theorem primeNormalProfile_equation {t β L : ℝ} (hL : t / 2 < L) :
    (2 * L - t) * (-(β / 2) * (L - t / 2) ^ (-(3:ℝ)/2)) + primeNormalProfile t β L = 0 := by
  have hpos : (0:ℝ) < L - t / 2 := by linarith
  unfold primeNormalProfile
  have hrw : (L - t / 2) * (L - t / 2) ^ (-(3:ℝ)/2) = (L - t / 2) ^ (-(1:ℝ)/2) := by
    nth_rewrite 1 [← Real.rpow_one (L - t / 2)]
    rw [← Real.rpow_add hpos]
    norm_num
  rw [← hrw]
  ring

/-- **The half-log trace of the profile is `β`**, the card's `(3)`. -/
theorem tendsto_sqrt_mul_primeNormalProfile (t β : ℝ) :
    Tendsto (fun L => Real.sqrt L * primeNormalProfile t β L) atTop (nhds β) := by
  have hratio : Tendsto (fun L : ℝ => (L - t / 2) / L) atTop (nhds 1) := by
    have h : Tendsto (fun L : ℝ => 1 - (t / 2) / L) atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub (Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id)
    rw [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    field_simp
  have hsq : Tendsto (fun L : ℝ => Real.sqrt ((L - t / 2) / L)) atTop (nhds 1) := by
    have h := (Real.continuous_sqrt.tendsto 1).comp hratio
    rwa [Real.sqrt_one] at h
  have hinv : Tendsto (fun L : ℝ => (Real.sqrt ((L - t / 2) / L))⁻¹) atTop (nhds 1) := by
    have h := hsq.inv₀ (by norm_num)
    rwa [inv_one] at h
  have hfin := hinv.const_mul β
  rw [mul_one] at hfin
  refine hfin.congr' ?_
  filter_upwards [eventually_gt_atTop (max (0:ℝ) (t / 2))] with L hL
  have hL0 : (0:ℝ) < L := lt_of_le_of_lt (le_max_left _ _) hL
  have hLt : t / 2 < L := lt_of_le_of_lt (le_max_right _ _) hL
  have hpos : (0:ℝ) < L - t / 2 := by linarith
  unfold primeNormalProfile
  have hp : (L - t / 2) ^ (-(1:ℝ)/2) = (Real.sqrt (L - t / 2))⁻¹ := by
    rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, Real.rpow_neg hpos.le, Real.sqrt_eq_rpow]
  have hs : Real.sqrt ((L - t / 2) / L) = Real.sqrt (L - t / 2) / Real.sqrt L :=
    Real.sqrt_div hpos.le L
  have hsq1 : 0 < Real.sqrt (L - t / 2) := Real.sqrt_pos.mpr hpos
  have hsq2 : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  rw [hp, hs]
  field_simp


/-- The binomial expansion coefficient of the card's `(4)`. -/
noncomputable def primeNormalCoeff (k : ℕ) : ℝ := (Nat.centralBinom k : ℝ) / 8 ^ k

theorem primeNormalCoeff_zero : primeNormalCoeff 0 = 1 := by
  unfold primeNormalCoeff
  simp [Nat.centralBinom]

theorem primeNormalCoeff_pos (k : ℕ) : 0 < primeNormalCoeff k := by
  unfold primeNormalCoeff
  have h := Nat.centralBinom_pos k
  positivity

/-- The coefficients are `binom(2k,k)/4^k` scaled by `2^{-k}`, matching `(4)`'s `L^{-k}` grading. -/
theorem primeNormalCoeff_eq (k : ℕ) :
    primeNormalCoeff k = ((Nat.centralBinom k : ℝ) / 4 ^ k) * (1 / 2) ^ k := by
  unfold primeNormalCoeff
  rw [show (8:ℝ) = 4 * 2 by norm_num, mul_pow]
  field_simp
  rw [mul_assoc, ← mul_pow, show (2:ℝ) * (1/2) = 1 by norm_num, one_pow, mul_one]


end GaloisForLFunctions.HTGeometry
