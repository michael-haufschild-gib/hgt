import GaloisForLFunctions.AdelicKreinGeometry.Haar.PolynomialPerturbations
import GaloisForLFunctions.HeckeKreinToeplitz.Index.HyperbolicFeatures
import GaloisForLFunctions.HeckeKreinToeplitz.Index.RescalingInvariance
import Mathlib.Algebra.Ring.Parity

/-!
# Mixed affine powers attain every finite negative index above one

The kernels `γ(1-a⁻ᵈ)bᵈ`, with real phase in odd degree and imaginary phase in even
degree, vanish on both affine axes and have negative index `d+1`. Hyperbolic
features give the upper bound; the translation-degree law makes it sharp.
Positive-definite additions preserve this index by dilation rescaling, so adding
the Haar state preserves both axis readings at every index at least two.
-/

open Complex Finset Polynomial Filter Topology
open scoped ComplexConjugate
open GaloisForLFunctions.ArithmeticPositiveDuality GaloisForLFunctions.HeckeKreinToeplitz
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-- A homogeneous mixed affine kernel. Its phase determines Hermitian symmetry. -/
def mixedPowerKernel (d : ℕ) (γ : ℂ) (g : AffineGroupQ) : ℂ :=
  γ * (1 - (affSlope g : ℂ)⁻¹ ^ d) * (affShift g : ℂ) ^ d

theorem mixedPowerKernel_translation (d : ℕ) (γ : ℂ) (b : ℚ) :
    mixedPowerKernel d γ (translation b) = 0 := by
  simp only [mixedPowerKernel, affSlope_translation, Rat.cast_one, inv_one, one_pow,
    sub_self, mul_zero, zero_mul]

theorem mixedPowerKernel_dilation {d : ℕ} (hd : 0 < d) (γ : ℂ) (u : ℚˣ) :
    mixedPowerKernel d γ (dilation u) = 0 := by
  simp only [mixedPowerKernel, affShift_dilation, Rat.cast_zero,
    zero_pow (Nat.ne_of_gt hd), mul_zero]

private theorem mixedPowerKernel_quotient (d : ℕ) (γ : ℂ) (g h : AffineGroupQ) :
    mixedPowerKernel d γ (g⁻¹ * h) =
      γ * ((affSlope g : ℂ)⁻¹ ^ d - (affSlope h : ℂ)⁻¹ ^ d) *
        ((affShift h : ℂ) - (affShift g : ℂ)) ^ d := by
  have ha : (affSlope g : ℂ) ≠ 0 := by exact_mod_cast affSlope_ne_zero g
  have hs : (affShift (g⁻¹ * h) : ℂ) =
      (affSlope g : ℂ)⁻¹ * ((affShift h : ℂ) - (affShift g : ℂ)) := by
    simp only [affShift_mul, affSlope_inv, affShift_inv, Rat.cast_mul,
      Rat.cast_inv, Rat.cast_add, Rat.cast_div, Rat.cast_neg]
    ring
  rw [mixedPowerKernel, hs]
  simp only [affSlope_mul, affSlope_inv, Rat.cast_mul, Rat.cast_inv,
    mul_inv, inv_inv, mul_pow]
  have hcancel : (affSlope g : ℂ) ^ d * ((affSlope g : ℂ)⁻¹) ^ d = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ ha, one_pow]
  calc
    γ * (1 - (affSlope g : ℂ) ^ d * ((affSlope h : ℂ)⁻¹) ^ d) *
        (((affSlope g : ℂ)⁻¹) ^ d * ((affShift h : ℂ) - (affShift g : ℂ)) ^ d) =
      γ * (((affSlope g : ℂ)⁻¹) ^ d -
        ((affSlope h : ℂ)⁻¹) ^ d *
          ((affSlope g : ℂ) ^ d * ((affSlope g : ℂ)⁻¹) ^ d)) *
        ((affShift h : ℂ) - (affShift g : ℂ)) ^ d := by ring
    _ = _ := by rw [hcancel, mul_one]

private def mixedPowerF (d : ℕ) (j : Fin (d + 1)) (g : AffineGroupQ) : ℂ :=
  (affSlope g : ℂ)⁻¹ ^ d * (-(affShift g : ℂ)) ^ (d - j)

private def mixedPowerB (d : ℕ) (γ : ℂ) (j : Fin (d + 1)) (g : AffineGroupQ) : ℂ :=
  γ * (d.choose j : ℂ) * (affShift g : ℂ) ^ (j : ℕ)

private theorem mixedPower_forward (d : ℕ) (γ : ℂ) (g h : AffineGroupQ) :
    (∑ j, conj (mixedPowerF d j g) * mixedPowerB d γ j h) =
      γ * (affSlope g : ℂ)⁻¹ ^ d * ((affShift h : ℂ) - (affShift g : ℂ)) ^ d := by
  simp only [mixedPowerF, mixedPowerB, map_mul, map_pow, map_inv₀, map_ratCast, map_neg]
  rw [sub_eq_add_neg, add_pow, ← Fin.sum_univ_eq_sum_range]
  simp only [Finset.mul_sum]
  apply sum_congr rfl
  intro j _
  ring

private theorem mixedPower_pairing (d : ℕ) (γ : ℂ)
    (hγ : conj γ * (-1 : ℂ) ^ d = -γ) (g h : AffineGroupQ) :
    mixedPowerKernel d γ (g⁻¹ * h) =
      ∑ j, (conj (mixedPowerF d j g) * mixedPowerB d γ j h +
        conj (mixedPowerB d γ j g) * mixedPowerF d j h) := by
  rw [Finset.sum_add_distrib, mixedPower_forward]
  have hback : (∑ j, conj (mixedPowerB d γ j g) * mixedPowerF d j h) =
      conj (γ * (affSlope h : ℂ)⁻¹ ^ d *
        ((affShift g : ℂ) - (affShift h : ℂ)) ^ d) := by
    rw [← mixedPower_forward d γ h g, map_sum]
    apply sum_congr rfl
    intro j _
    rw [map_mul, conj_conj, mul_comm]
  rw [hback]
  simp only [map_mul, map_pow, map_inv₀, map_ratCast, map_sub]
  have hdiff : (affShift g : ℂ) - (affShift h : ℂ) =
      (-1 : ℂ) * ((affShift h : ℂ) - (affShift g : ℂ)) := by ring
  rw [hdiff, mul_pow]
  calc
    mixedPowerKernel d γ (g⁻¹ * h) =
        γ * ((affSlope g : ℂ)⁻¹ ^ d - (affSlope h : ℂ)⁻¹ ^ d) *
          ((affShift h : ℂ) - (affShift g : ℂ)) ^ d := mixedPowerKernel_quotient d γ g h
    _ = γ * (affSlope g : ℂ)⁻¹ ^ d * ((affShift h : ℂ) - (affShift g : ℂ)) ^ d +
        (conj γ * (-1 : ℂ) ^ d) * (affSlope h : ℂ)⁻¹ ^ d *
          ((affShift h : ℂ) - (affShift g : ℂ)) ^ d := by rw [hγ]; ring
    _ = _ := by ring

/-- A degree-`d` mixed power kernel needs at most `d+1` negative squares. -/
theorem negIndex_mixedPowerKernel_le (d : ℕ) (γ : ℂ)
    (hγ : conj γ * (-1 : ℂ) ^ d = -γ) :
    negIndex (mixedPowerKernel d γ) ≤ (d + 1 : ℕ) :=
  negIndex_le_of_hyperbolic_features (mixedPowerF d) (mixedPowerB d γ)
    (mixedPower_pairing d γ hγ)

theorem isHermKernel_mixedPowerKernel (d : ℕ) (γ : ℂ)
    (hγ : conj γ * (-1 : ℂ) ^ d = -γ) : IsHermKernel (mixedPowerKernel d γ) := by
  intro g
  have hleft := mixedPower_pairing d γ hγ g 1
  have hright := mixedPower_pairing d γ hγ 1 g
  simp only [mul_one, inv_one, one_mul] at hleft hright
  rw [hleft, hright, map_sum]
  apply sum_congr rfl
  intro j _
  simp only [map_add, map_mul, conj_conj]
  ring

private theorem mixedPowerKernel_fibre (d : ℕ) (γ : ℂ) (u : ℚˣ) (b : ℚ) :
    mixedPowerKernel d γ (translation b * dilation u) =
      γ * (1 - ((u : ℚ) : ℂ)⁻¹ ^ d) * (b : ℂ) ^ d := by
  simp only [mixedPowerKernel, affSlope_mul, affSlope_translation, affSlope_dilation,
    affShift_mul, affShift_translation, affShift_dilation, one_mul, mul_zero, zero_add]

private theorem mixedPowerCoefficient_ne_zero {d : ℕ} (hd : 0 < d) {γ : ℂ} (hγ : γ ≠ 0) :
    γ * (1 - (2 : ℂ)⁻¹ ^ d) ≠ 0 := by
  apply mul_ne_zero hγ
  intro he
  have hpow : (2 : ℂ)⁻¹ ^ d = 1 := (sub_eq_zero.mp he).symm
  have hc : (2 : ℂ) ^ d * (2 : ℂ)⁻¹ ^ d = 1 := by
    rw [← mul_pow]
    norm_num
  rw [hpow, mul_one] at hc
  have hgt : (1 : ℝ) < 2 ^ d := one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hd)
  have heq : (2 : ℝ) ^ d = 1 := by exact_mod_cast hc
  exact (ne_of_gt hgt) heq

private theorem mixedPowerKernel_ne_zero {d : ℕ} (hd : 0 < d) {γ : ℂ} (hγ : γ ≠ 0) :
    mixedPowerKernel d γ ≠ 0 := by
  intro he
  have hval := congrFun he (translation 1 * dilation (Units.mk0 2 two_ne_zero))
  simp only [mixedPowerKernel_fibre, Units.val_mk0, Rat.cast_ofNat, Rat.cast_one,
    one_pow, mul_one, Pi.zero_apply] at hval
  exact mixedPowerCoefficient_ne_zero hd hγ hval

/-- Translation degree attains the lower bound for the negative index. -/
theorem negIndex_mixedPowerKernel {d : ℕ} (hd : 0 < d) {γ : ℂ} (hγ0 : γ ≠ 0)
    (hγ : conj γ * (-1 : ℂ) ^ d = -γ) :
    negIndex (mixedPowerKernel d γ) = (d + 1 : ℕ) := by
  have hi := negIndex_mixedPowerKernel_le d γ hγ
  obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top (ENat.coe_ne_top (d + 1)) hi)
  have hir : negIndex (mixedPowerKernel d γ) ≤ r := hr.ge
  obtain ⟨P, hP, he⟩ := exists_polynomial_translation_fibre_lt_index
    (isHermKernel_mixedPowerKernel d γ hγ) (mixedPowerKernel_ne_zero hd hγ0)
    hir (mixedPowerKernel_translation d γ) (mixedPowerKernel_dilation hd γ)
    (Units.mk0 2 two_ne_zero)
  have hp : P = C (γ * (1 - (2 : ℂ)⁻¹ ^ d)) * X ^ d := by
    apply P.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective
      (Nat.cast_injective : Function.Injective (fun n : ℕ => (n : ℂ)))).mono
    rintro z ⟨n, rfl⟩
    simpa only [Set.mem_setOf_eq, eval_mul, eval_C, eval_pow, eval_X,
      mixedPowerKernel_fibre, Units.val_mk0, Rat.cast_ofNat, Rat.cast_natCast] using (he n).symm
  have hdeg : P.natDegree = d := by
    rw [hp, Polynomial.natDegree_C_mul (mixedPowerCoefficient_ne_zero hd hγ0),
      Polynomial.natDegree_X_pow]
  rw [hdeg] at hP
  apply le_antisymm hi
  rw [← hr]
  exact_mod_cast Nat.succ_le_of_lt hP

private theorem mixedPowerKernel_conjugate (d : ℕ) (γ : ℂ) (u : ℚˣ) (g : AffineGroupQ) :
    mixedPowerKernel d γ (dilation u * g * (dilation u)⁻¹) =
      ((u : ℚ) : ℂ) ^ d * mixedPowerKernel d γ g := by
  have hu : (u : ℚ) ≠ 0 := u.ne_zero
  have hs : affSlope (dilation u * g * (dilation u)⁻¹) = affSlope g := by
    simp only [affSlope_mul, affSlope_inv, affSlope_dilation]
    field_simp
  have hb : affShift (dilation u * g * (dilation u)⁻¹) = (u : ℚ) * affShift g := by
    simp only [affShift_mul, affSlope_mul, affSlope_dilation, affShift_inv,
      affShift_dilation, neg_zero, zero_div, mul_zero, zero_add, add_zero]
  rw [mixedPowerKernel, hs, hb, Rat.cast_mul, mul_pow]
  unfold mixedPowerKernel
  ring

/-- A positive-definite addition cannot remove any mixed polynomial negative direction. -/
theorem negIndex_posDef_add_mixedPowerKernel {d : ℕ} (hd : 0 < d) {γ : ℂ}
    (hγ0 : γ ≠ 0) (hγ : conj γ * (-1 : ℂ) ^ d = -γ)
    {p : AffineGroupQ → ℂ} (hp : IsPosDefKernel p) :
    negIndex (fun g => p g + mixedPowerKernel d γ g) = (d + 1 : ℕ) := by
  let u : ℕ → ℚˣ := fun N => Units.mk0 ((N : ℚ) + 1) (by positivity)
  let φ : ℕ → AffineGroupQ →* AffineGroupQ := fun N =>
    { toFun := fun g => dilation (u N) * g * (dilation (u N))⁻¹
      map_one' := by group
      map_mul' a b := by group }
  let s : ℕ → ℝ := fun N => (((N : ℝ) + 1)⁻¹) ^ d
  have hspos (N : ℕ) : 0 < s N := by dsimp only [s]; positivity
  have hs : Tendsto s atTop (𝓝 0) := by
    simpa only [s, one_div, zero_pow (Nat.ne_of_gt hd)] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow d
  have hscale (N : ℕ) (g : AffineGroupQ) :
      (s N : ℂ) * mixedPowerKernel d γ (φ N g) = mixedPowerKernel d γ g := by
    have h0 : (N : ℂ) + 1 ≠ 0 := by
      exact_mod_cast (show (N : ℝ) + 1 ≠ 0 by positivity)
    change (s N : ℂ) * mixedPowerKernel d γ
      (dilation (u N) * g * (dilation (u N))⁻¹) = _
    rw [mixedPowerKernel_conjugate, ← mul_assoc]
    have he : (s N : ℂ) * (((u N : ℚ) : ℂ) ^ d) = 1 := by
      simp only [s, u, Units.val_mk0, Complex.ofReal_pow, Complex.ofReal_inv,
        Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one, Rat.cast_add,
        Rat.cast_natCast, Rat.cast_one]
      rw [← mul_pow, inv_mul_cancel₀ h0, one_pow]
    rw [he, one_mul]
  rw [negIndex_posDef_add_of_rescaling (isHermKernel_mixedPowerKernel d γ hγ)
    hp φ s hspos hs hscale, negIndex_mixedPowerKernel hd hγ0 hγ]

/-- The real phase in odd degree and imaginary phase in even degree give Hermitian kernels. -/
def mixedPowerPhase (d : ℕ) : ℂ := if Even d then I else 1

theorem mixedPowerPhase_ne_zero (d : ℕ) : mixedPowerPhase d ≠ 0 := by
  unfold mixedPowerPhase
  split_ifs
  · exact I_ne_zero
  · exact one_ne_zero

theorem mixedPowerPhase_conj (d : ℕ) :
    conj (mixedPowerPhase d) * (-1 : ℂ) ^ d = -mixedPowerPhase d := by
  by_cases h : Even d
  · simp only [mixedPowerPhase, if_pos h, conj_I, h.neg_one_pow, mul_one]
  · have ho : Odd d := (Nat.even_or_odd d).resolve_left h
    simp only [mixedPowerPhase, if_neg h, map_one, ho.neg_one_pow, one_mul]

/-- Every positive degree occurs with the smallest index allowed by its translation degree. -/
theorem negIndex_posDef_add_canonicalMixedPower {d : ℕ} (hd : 0 < d)
    {p : AffineGroupQ → ℂ} (hp : IsPosDefKernel p) :
    negIndex (fun g => p g + mixedPowerKernel d (mixedPowerPhase d) g) = (d + 1 : ℕ) :=
  negIndex_posDef_add_mixedPowerKernel hd (mixedPowerPhase_ne_zero d) (mixedPowerPhase_conj d) hp

/-- The Haar state with a homogeneous perturbation invisible on both affine axes. -/
def haarMixedPowerState (d : ℕ) (g : AffineGroupQ) : ℂ :=
  haarState g + mixedPowerKernel d (mixedPowerPhase d) g

theorem haarMixedPowerState_translation (d : ℕ) (b : ℚ) :
    haarMixedPowerState d (translation b) = haarState (translation b) := by
  rw [haarMixedPowerState, mixedPowerKernel_translation, add_zero]

theorem haarMixedPowerState_hasIntegerSuccessor (d : ℕ) :
    HasIntegerSuccessor (haarMixedPowerState d) := by
  intro b
  rw [haarMixedPowerState_translation]
  exact haarState_hasIntegerSuccessor b

theorem haarMixedPowerState_dilation {d : ℕ} (hd : 0 < d) (u : ℚˣ) :
    haarMixedPowerState d (dilation u) = haarState (dilation u) := by
  rw [haarMixedPowerState, mixedPowerKernel_dilation hd, add_zero]

theorem isHermKernel_haarMixedPowerState (d : ℕ) : IsHermKernel (haarMixedPowerState d) := by
  intro g
  simp only [haarMixedPowerState, IsPosDefOnGroup.map_inv isPosDefOnGroup_haarState,
    isHermKernel_mixedPowerKernel d (mixedPowerPhase d) (mixedPowerPhase_conj d) g,
    map_add, Complex.star_def]

/-- Every index at least two is realized while preserving both Haar axis readings. -/
theorem negIndex_haarMixedPowerState {d : ℕ} (hd : 0 < d) :
    negIndex (haarMixedPowerState d) = (d + 1 : ℕ) :=
  negIndex_posDef_add_canonicalMixedPower hd
    (isPosDefKernel_iff_isPosDefOnGroup.mpr isPosDefOnGroup_haarState)

#print axioms negIndex_mixedPowerKernel_le
#print axioms negIndex_mixedPowerKernel
#print axioms negIndex_posDef_add_mixedPowerKernel
#print axioms negIndex_posDef_add_canonicalMixedPower
#print axioms haarMixedPowerState_hasIntegerSuccessor
#print axioms haarMixedPowerState_dilation
#print axioms isHermKernel_haarMixedPowerState
#print axioms negIndex_haarMixedPowerState
end GaloisForLFunctions.AdelicKreinGeometry
