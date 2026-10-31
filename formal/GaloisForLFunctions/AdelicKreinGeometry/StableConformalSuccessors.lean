import GaloisForLFunctions.AdelicKreinGeometry.TheSignatureOfASeparableAssembly
import GaloisForLFunctions.ArithmeticKreinLangerTheory.LocalConstituentsMeetOnlyAtTheIdentity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Stable conformal successors

The conformal successors of exponent `s` are the homogeneous kernels `c|b|^s`, on which the
dilation `x ↦ ux` acts with conformal factor `|u|^s` (`ConformalSymmetryNeedsANegativeSquare`
treats `s = 1`). For `0 < s < 1` this file proves that `−|m|^s` is a Pontryagin state with exactly
one negative square, by Poisson subordination.

* **Subordination** (`subordination`, `subordination_eq`): `I_s(t) = ∫_0^∞ (1 − e^{−rt}) r^{−1−s} dr`
  converges for `t ≥ 0` (`integrableOn_subordinand`) and is homogeneous, `I_s(t) = t^s I_s(1)`, with
  `I_s(1) > 0` (`subordination_one_pos`). So `|m|^s = I_s(|m|)/I_s(1)`.
* **Conditional positivity** (`hermQuad_gram_negPow_nonneg`). On coefficient vectors of total mass
  zero, `Σ c̄_a c_b (−|z_b − z_a|^s) = I_s(1)⁻¹ ∫_0^∞ P(r) r^{−1−s} dr` with
  `P(r) = Σ c̄_a c_b e^{−r|z_b − z_a|} ≥ 0`, the Gram form of the Poisson kernel `e^{−r|m|}`
  (`ArithmeticKreinLangerTheory.isPosDefKernel_poissonKernel`).
* **One negative square** (`negIndex_negPow`): `κ(−|m|^s) = 1` for `0 < s < 1`.

At `s = 1/2` the conformal factor of the dilation by `u` is `|u|^{1/2}`, the normalization that
turns Hecke translations into isometric boosts of the pole plane: the boost's scalar lives on the
additive side, carried by one negative square.
-/

open Complex Finset MeasureTheory Set Filter
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticKreinLangerTheory (isPosDefKernel_poissonKernel)

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

variable {s : ℝ}

/-- The subordinand `(1 − e^{−rt}) r^{−1−s}`. -/
def subordinand (s t r : ℝ) : ℝ := (1 - Real.exp (-(r * t))) * r ^ (-1 - s)

/-- The subordination integral `I_s(t) = ∫_0^∞ (1 − e^{−rt}) r^{−1−s} dr`. -/
def subordination (s t : ℝ) : ℝ := ∫ r in Ioi (0 : ℝ), subordinand s t r

theorem measurable_subordinand (s t : ℝ) : Measurable (subordinand s t) := by
  unfold subordinand; fun_prop

theorem subordinand_nonneg {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) : 0 ≤ subordinand s t r := by
  unfold subordinand
  have : Real.exp (-(r * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  exact mul_nonneg (by linarith) (Real.rpow_nonneg hr _)

theorem integrableOn_subordinand (hs0 : 0 < s) (hs1 : s < 1) {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (subordinand s t) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · -- near `0`: `(1 − e^{−rt}) r^{−1−s} ≤ t r^{−s}`
    have hint : IntegrableOn (fun r : ℝ => t * r ^ (-s)) (Ioc 0 1) := by
      have := (intervalIntegral.intervalIntegrable_rpow' (r := -s) (by linarith) (a := 0) (b := 1))
      rw [intervalIntegrable_iff, uIoc_of_le zero_le_one] at this
      exact this.const_mul t
    refine hint.mono' (measurable_subordinand s t).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun r hr => ?_)
    have hr0 : 0 < r := hr.1
    rw [Real.norm_of_nonneg (subordinand_nonneg ht hr0.le)]
    unfold subordinand
    have h1 : 1 - Real.exp (-(r * t)) ≤ r * t := by linarith [Real.add_one_le_exp (-(r * t))]
    have h2 : r * r ^ (-1 - s) = r ^ (-s) := by
      rw [← Real.rpow_one_add' hr0.le (by linarith)]; congr 1; ring
    calc (1 - Real.exp (-(r * t))) * r ^ (-1 - s) ≤ r * t * r ^ (-1 - s) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hr0.le _)
      _ = t * r ^ (-s) := by rw [← h2]; ring
  · -- near `∞`: `(1 − e^{−rt}) r^{−1−s} ≤ r^{−1−s}`
    refine (integrableOn_Ioi_rpow_of_lt (a := -1 - s) (by linarith) zero_lt_one).mono'
      (measurable_subordinand s t).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
    have hr0 : 0 < r := lt_trans zero_lt_one hr
    rw [Real.norm_of_nonneg (subordinand_nonneg ht hr0.le)]
    unfold subordinand
    have : 0 ≤ Real.exp (-(r * t)) := (Real.exp_pos _).le
    nlinarith [Real.rpow_nonneg hr0.le (-1 - s)]

/-- `I_s(1) > 0`. -/
theorem subordination_one_pos (hs0 : 0 < s) (hs1 : s < 1) : 0 < subordination s 1 := by
  unfold subordination
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · have hsupp : Ioi (0 : ℝ) ⊆ Function.support (subordinand s 1) := fun r hr => by
      have hr0 : 0 < r := hr
      unfold subordinand
      refine mul_ne_zero ?_ (Real.rpow_pos_of_pos hr0 _).ne'
      have : Real.exp (-(r * 1)) < 1 := by
        have h := Real.exp_lt_exp.mpr (show -(r * 1) < 0 by linarith)
        rwa [Real.exp_zero] at h
      linarith
    rw [inter_eq_right.mpr hsupp]
    simp
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun r hr => subordinand_nonneg zero_le_one (le_of_lt hr))
  · exact integrableOn_subordinand hs0 hs1 zero_le_one

/-- **Homogeneity of subordination**: `I_s(t) = t^s I_s(1)`. -/
theorem subordination_eq {t : ℝ} (ht : 0 < t) :
    subordination s t = t ^ s * subordination s 1 := by
  unfold subordination
  have hpt : ∀ r ∈ Ioi (0 : ℝ), subordinand s t r = t ^ (1 + s) * subordinand s 1 (t * r) := by
    intro r hr
    have hr0 : 0 < r := hr
    unfold subordinand
    rw [Real.mul_rpow ht.le hr0.le, mul_one, mul_comm t r]
    have : t ^ (1 + s) * t ^ (-1 - s) = 1 := by
      rw [← Real.rpow_add ht]; simp
    calc (1 - Real.exp (-(r * t))) * r ^ (-1 - s)
        = (t ^ (1 + s) * t ^ (-1 - s)) * ((1 - Real.exp (-(r * t))) * r ^ (-1 - s)) := by
          rw [this, one_mul]
      _ = _ := by ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    integral_comp_mul_left_Ioi (subordinand s 1) 0 ht, mul_zero, smul_eq_mul, ← mul_assoc]
  congr 1
  rw [← Real.rpow_neg_one, ← Real.rpow_add ht]
  congr 1; ring

/-- The kernel `m ↦ −|m|^s` on `ℤ`. -/
def negPowKernel (s : ℝ) (m : Multiplicative ℤ) : ℂ :=
  -(((|((Multiplicative.toAdd m : ℤ) : ℝ)|) ^ s : ℝ) : ℂ)

/-- `|m|^s = I_s(|m|)/I_s(1)`. -/
theorem abs_rpow_eq_subordination (hs0 : 0 < s) (hs1 : s < 1) (w : ℝ) :
    |w| ^ s = subordination s |w| / subordination s 1 := by
  have h1 := (subordination_one_pos hs0 hs1).ne'
  rcases (abs_nonneg w).eq_or_lt with h | h
  · rw [← h, Real.zero_rpow hs0.ne']
    have : subordination s 0 = 0 := by simp [subordination, subordinand]
    rw [this, zero_div]
  · rw [subordination_eq h, mul_div_assoc, div_self h1, mul_one]

/-- **`−|m|^s` is conditionally positive on `ℤ`** for `0 < s < 1`. -/
theorem hermQuad_gram_negPow_nonneg (hs0 : 0 < s) (hs1 : s < 1) {n : ℕ}
    (x : Fin n → Multiplicative ℤ) (c : Fin n → ℂ) (hc : ∑ a, c a = 0) :
    0 ≤ hermQuad (gram (negPowKernel s) x) c := by
  set w : Fin n → Fin n → ℝ := fun a b =>
    |((Multiplicative.toAdd (x b) - Multiplicative.toAdd (x a) : ℤ) : ℝ)|
  set ρ : Fin n → Fin n → ℝ := fun a b => (conj (c a) * c b).re
  have hI := subordination_one_pos hs0 hs1
  -- the form as a real double sum
  have hform : hermQuad (gram (negPowKernel s) x) c =
      -(subordination s 1)⁻¹ * ∑ a, ∑ b, ρ a b * subordination s (w a b) := by
    rw [hermQuad_gram, Complex.re_sum]
    simp_rw [Complex.re_sum, mul_sum]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    have hent : negPowKernel s ((x a)⁻¹ * x b) = -(((w a b) ^ s : ℝ) : ℂ) := by
      simp only [negPowKernel, w, toAdd_mul, toAdd_inv]; push_cast; ring_nf
    rw [hent, show conj (c a) * -(((w a b) ^ s : ℝ) : ℂ) * c b =
      ((-(w a b ^ s) : ℝ) : ℂ) * (conj (c a) * c b) by push_cast; ring, Complex.re_ofReal_mul]
    rw [show w a b = |w a b| from (abs_of_nonneg (abs_nonneg _)).symm,
      abs_rpow_eq_subordination hs0 hs1, abs_abs]
    simp only [ρ]
    field_simp
  -- the integrand is minus a Poisson Gram form
  have hint : ∀ a b, IntegrableOn (fun r => ρ a b * subordinand s (w a b) r) (Ioi 0) :=
    fun a b => (integrableOn_subordinand hs0 hs1 (abs_nonneg _)).const_mul _
  have hswap : ∑ a, ∑ b, ρ a b * subordination s (w a b) =
      ∫ r in Ioi (0 : ℝ), ∑ a, ∑ b, ρ a b * subordinand s (w a b) r := by
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hint a b]
    refine sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => hint a b]
    exact sum_congr rfl fun b _ => (integral_const_mul _ _).symm
  have hmass : ∑ a, ∑ b, ρ a b = 0 := by
    simp only [ρ, ← Complex.re_sum]
    rw [← sum_mul_sum, ← map_sum, hc, map_zero, zero_mul, Complex.zero_re]
  have hpt : ∀ r ∈ Ioi (0 : ℝ), ∑ a, ∑ b, ρ a b * subordinand s (w a b) r ≤ 0 := by
    intro r hr
    have hr0 : 0 < r := hr
    -- the Poisson Gram form at `e^{−r}`
    have hP := (isPosDefKernel_poissonKernel (Real.exp_pos (-r)).le
      (Real.exp_le_one_iff.mpr (by linarith))).hermQuad_nonneg x c
    rw [hermQuad_gram, Complex.re_sum] at hP
    simp_rw [Complex.re_sum] at hP
    have hPe : ∀ a b, (conj (c a) * ArithmeticKreinLangerTheory.poissonKernel (Real.exp (-r))
        ((x a)⁻¹ * x b) * c b).re =
        ρ a b * Real.exp (-(r * w a b)) := by
      intro a b
      simp only [ArithmeticKreinLangerTheory.poissonKernel, toAdd_mul, toAdd_inv, w, ρ]
      rw [show conj (c a) * ((Real.exp (-r) ^ (-Multiplicative.toAdd (x a) +
          Multiplicative.toAdd (x b)).natAbs : ℝ) : ℂ) * c b =
          ((Real.exp (-r) ^ (-Multiplicative.toAdd (x a) +
            Multiplicative.toAdd (x b)).natAbs : ℝ) : ℂ) * (conj (c a) * c b) by ring,
        Complex.re_ofReal_mul, ← Real.exp_nat_mul, mul_comm]
      refine congrArg₂ _ rfl (congrArg Real.exp ?_)
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      push_cast
      rw [show -((Multiplicative.toAdd (x a) : ℤ) : ℝ) + ((Multiplicative.toAdd (x b) : ℤ) : ℝ) =
        ((Multiplicative.toAdd (x b) : ℤ) : ℝ) - ((Multiplicative.toAdd (x a) : ℤ) : ℝ) by ring]
      ring
    simp_rw [hPe] at hP
    have e : ∑ a, ∑ b, ρ a b * subordinand s (w a b) r =
        r ^ (-1 - s) * (∑ a, ∑ b, ρ a b - ∑ a, ∑ b, ρ a b * Real.exp (-(r * w a b))) := by
      simp only [subordinand, mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
    rw [e, hmass, zero_sub]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hr0.le _) (by linarith)
  have hle : ∫ r in Ioi (0 : ℝ), ∑ a, ∑ b, ρ a b * subordinand s (w a b) r ≤ 0 :=
    setIntegral_nonpos measurableSet_Ioi hpt
  rw [hform, hswap]
  have : 0 ≤ (subordination s 1)⁻¹ := (inv_pos.mpr hI).le
  nlinarith

/-- **`−|m|^s` has exactly one negative square** for `0 < s < 1`. -/
theorem negIndex_negPow (hs0 : 0 < s) (hs1 : s < 1) : negIndex (negPowKernel s) = 1 := by
  refine le_antisymm ?_ ?_
  · have hpol : polarIndex (negPowKernel s) = 0 := by
      refine nonpos_iff_eq_zero.mp (iSup₂_le fun n x => ?_)
      rw [negIndexOn_eq_zero_of_nonneg fun c hc => hermQuad_gram_negPow_nonneg hs0 hs1 x c hc]
      rfl
    simpa [hpol] using negIndex_le_polarIndex_add_one (negPowKernel s)
  · have hneg : hermQuad (gram (negPowKernel s) ![1, Multiplicative.ofAdd 1]) ![1, 1] < 0 := by
      rw [hermQuad_gram]
      simp [Fin.sum_univ_two, negPowKernel, Real.zero_rpow hs0.ne']
    simpa using card_le_negIndex_of_orthogonal_translates (J := Fin 1) hneg (fun _ => 1)
      fun j j' h => absurd (Subsingleton.elim j j') h

/-- The dilations act on `−|m|^s` with conformal factor `|u|^s`. -/
theorem negPowKernel_conformal (u : ℤ) (m : ℤ) :
    negPowKernel s (Multiplicative.ofAdd (u * m)) =
      (((|(u : ℝ)|) ^ s : ℝ) : ℂ) * negPowKernel s (Multiplicative.ofAdd m) := by
  simp only [negPowKernel, toAdd_ofAdd]
  push_cast
  rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  push_cast
  ring

end GaloisForLFunctions.AdelicKreinGeometry
