import GaloisForLFunctions.RHTower.CHMDStage15ZeroSideSummabilityAndSechHalfOriginPositivity
import GaloisForLFunctions.RHTower.EvenLandauPairTest
import GaloisForLFunctions.RHTower.EvenSectorCriticalZeroCarrier

/-!
# CHMD Stage 16: Zero-Side Reflection Symmetries, Schwarz-Square Wave-Packet Decomposition, and Unconditional $\Xi$-Convolution Annihilation of `cosineShiftFn Λ sechHalf`

This module establishes **Stage 16** of the Causal Hyperbolic–Modular Duality (CHMD) route:

1. **Section 1 (Zero-Side Reflection/Negation Symmetries and Schwarz-Square Decomposition of Wave-Packet Summands):**
   - For every $\Phi : \mathbb{C} \to \mathbb{C}$ and $z \in \mathbb{C}$,
     `specSq Φ (conj z) = conj (specSq Φ z)` and `(specSq Φ (conj z)).re = (specSq Φ z).re`
     (`specSq_conj`, `re_specSq_conj`).
   - Under the reflection involution `zetaCarrierReflect` ($\rho \mapsto 1 - \bar{\rho}$,
     $\gamma_{1-\bar{\rho}} = \overline{\gamma_\rho}$), every zero-side summand satisfies
     `specSq Φ (gammaOf (zetaCarrierReflect ρ)) = conj (specSq Φ (gammaOf ρ))` and has identical
     real part (`specSq_gammaOf_reflect`, `re_specSq_gammaOf_reflect`,
     `re_rhoCosShift_gammaOf_reflect`).
   - Under `zetaCarrierOneSub` ($\rho \mapsto 1 - \rho$, $\gamma_{1-\rho} = -\gamma_\rho$), every
     even $\Phi$ satisfies `specSq Φ (gammaOf (zetaCarrierOneSub ρ)) = specSq Φ (gammaOf ρ)`
     (`specSq_gammaOf_oneSub`, `rhoCosShift_gammaOf_oneSub`).
   - Whenever $\Phi(\bar{z}) = \overline{\Phi(z)}$ (which holds on $|z.\text{im}| < \sqrt{2}$ for
     `sechHalf`, `cosComb t c sechHalf`, and `sinComb t c sechHalf`), `specSq Φ z = Φ z ^ 2` and
     `(specSq Φ z).re = (Φ z).re ^ 2 - (Φ z).im ^ 2` (`specSq_eq_sq_of_conj_symm`,
     `re_specSq_eq_re_sq_sub_im_sq_of_conj_symm`, `re_specSq_cosComb_add_sinComb_sechHalf_gammaOf`).

2. **Section 2 (Unconditional Zero-Side Vanishing of Every $\Xi$-Divisible `EvenStrip` Function and of `RHTower.XiC`):**
   - By `CHMDStage15`, for every `EvenStrip Φ` that vanishes at `gammaOf ρ` for all
     `ρ : zetaZeroConfig.carrier`, `evenWeilDensity Λ (specSq Φ) = 0`,
     `∀ y : ℝ, cosineShiftFn Λ Φ y = 0`, and every finite Toeplitz form of `cosineShiftFn Λ Φ`
     vanishes identically (`evenWeilDensity_specSq_vonMangoldt_eq_zero_of_gammaOf_eq_zero`,
     `cosineShiftFn_vonMangoldt_eq_zero_of_gammaOf_eq_zero`,
     `sum_sum_cosineShiftFn_vonMangoldt_eq_zero_of_gammaOf_eq_zero`).
   - We prove `evenStrip_XiC : EvenStrip RHTower.XiC` and
     `XiC_gammaOf_eq_zero : ∀ ρ : zetaZeroConfig.carrier, RHTower.XiC (gammaOf ρ) = 0`, deducing
     unconditionally that `cosineShiftFn Λ RHTower.XiC y = 0` for all $y \in \mathbb{R}$ and hence
     `evenPrimePart Λ (rhoCosShift y RHTower.XiC) = evenPolePart (rhoCosShift y RHTower.XiC) + (1 / (2 * π)) * evenArchPart (rhoCosShift y RHTower.XiC)`
     (`cosineShiftFn_XiC_vonMangoldt_eq_zero`, `evenPrimePart_rhoCosShift_XiC_vonMangoldt_eq`).

3. **Section 3 (Individual `xiShiftedGamma j` Annihilation, Global Convolution Annihilation of `cosineShiftFn Λ sechHalf`, and Global Nonnegativity of the $j = 0$ Ground-State Lift):**
   - For every individual $j \in \mathbb{N}$ (without summing over $j$),
     `evenWeilDensity Λ (specSq (xiShiftedGamma j)) = 0` and
     `∫ t : ℝ, sechKernel (xiShiftedGamma j) t * cosineShiftFn Λ sechHalf t = 0`
     (`evenWeilDensity_specSq_xiShiftedGamma_vonMangoldt_eq_zero`,
     `integral_sechKernel_xiShiftedGamma_mul_cosineShiftFn_sechHalf_vonMangoldt_eq_zero`).
   - Defining the multiplier `xiCoshHalf z = RHTower.XiC z * Complex.cosh (z / 2)` so that
     `sechHalf z * xiCoshHalf z = RHTower.XiC z` on `|z.im| ≤ 9 / 4`, we prove that the shifted
     convolution of `cosineShiftFn Λ sechHalf` against
     `stripTest (specSq (rhoLift xiCoshHalf))` vanishes identically at every shift $y \in \mathbb{R}$
     (`integral_cosShiftKernel_xiCoshHalf_mul_cosineShiftFn_sechHalf_vonMangoldt_eq_zero`).
   - Finally, we prove that the $j = 0$ ground-state weight
     `ρ ↦ (rhoLift (sechWeight (xiShiftedGamma 0)) ρ).re` is strictly positive on the entire
     sub-threshold segment `ρ ^ 2 ≤ 2` and nonnegative on all of `ℝ`
     (`re_rhoLift_sechWeight_xiShiftedGamma_zero_pos_of_sq_le_two`,
     `re_rhoLift_sechWeight_xiShiftedGamma_zero_nonneg`).
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped Real ComplexConjugate Nat

noncomputable section

namespace RHTower.CHMDStage16

open WeilOneSided WeilSpectral RHTower.EvenSector RHTower.WeilPolarMajorant
open RHTower.CHMDStage1 RHTower.CHMDStage2 RHTower.CHMDStage3 RHTower.CHMDStage4
open RHTower.CHMDStage11 RHTower.CHMDStage12 RHTower.CHMDStage13 RHTower.CHMDStage14
open RHTower.CHMDStage15
open GaloisForLFunctions.HTGeometry

/-! ## Section 1: Zero-Side Reflection Symmetries and Schwarz-Square Wave-Packet Decomposition -/

/-- For every $\Phi : \mathbb{C} \to \mathbb{C}$ and $z \in \mathbb{C}$,
`specSq Φ (conj z) = conj (specSq Φ z)`. -/
theorem specSq_conj (Φ : ℂ → ℂ) (z : ℂ) :
    specSq Φ (conj z) = conj (specSq Φ z) := by
  unfold specSq
  rw [Complex.conj_conj, map_mul, Complex.conj_conj, mul_comm]

/-- For every $\Phi : \mathbb{C} \to \mathbb{C}$ and $z \in \mathbb{C}$,
`(specSq Φ (conj z)).re = (specSq Φ z).re`. -/
theorem re_specSq_conj (Φ : ℂ → ℂ) (z : ℂ) :
    (specSq Φ (conj z)).re = (specSq Φ z).re := by
  rw [specSq_conj, Complex.conj_re]

/-- Under `zetaCarrierReflect` ($\rho \mapsto 1 - \bar{\rho}$),
`specSq Φ (gammaOf (zetaCarrierReflect ρ)) = conj (specSq Φ (gammaOf ρ))`. -/
theorem specSq_gammaOf_reflect (Φ : ℂ → ℂ) (ρ : zetaZeroConfig.carrier) :
    specSq Φ (Zeta23.gammaOf (zetaCarrierReflect ρ)) =
      conj (specSq Φ (Zeta23.gammaOf ρ)) := by
  simp only [zetaCarrierReflect, Equiv.coe_fn_mk, gammaOf_reflect', specSq_conj]

/-- Under `zetaCarrierReflect` ($\rho \mapsto 1 - \bar{\rho}$), the real part of `specSq Φ` at
`gammaOf` is invariant:
`(specSq Φ (gammaOf (zetaCarrierReflect ρ))).re = (specSq Φ (gammaOf ρ)).re`. -/
theorem re_specSq_gammaOf_reflect (Φ : ℂ → ℂ) (ρ : zetaZeroConfig.carrier) :
    (specSq Φ (Zeta23.gammaOf (zetaCarrierReflect ρ))).re =
      (specSq Φ (Zeta23.gammaOf ρ)).re := by
  rw [specSq_gammaOf_reflect, Complex.conj_re]

/-- On `|z.im| < √2`, `rhoCosShift y Φ (conj z) = conj (rhoCosShift y Φ z)`. -/
theorem rhoCosShift_conj (y : ℝ) (Φ : ℂ → ℂ) {z : ℂ} (hz : |z.im| < Real.sqrt 2) :
    rhoCosShift y Φ (conj z) = conj (rhoCosShift y Φ z) := by
  unfold rhoCosShift
  rw [map_mul, ← (conj_trig_rhoC_conj y hz).1, Complex.conj_conj, specSq_conj]

/-- Under `zetaCarrierReflect`, `rhoCosShift y Φ (gammaOf (zetaCarrierReflect ρ))` is the complex
conjugate of `rhoCosShift y Φ (gammaOf ρ)`. -/
theorem rhoCosShift_gammaOf_reflect (y : ℝ) (Φ : ℂ → ℂ) (ρ : zetaZeroConfig.carrier) :
    rhoCosShift y Φ (Zeta23.gammaOf (zetaCarrierReflect ρ)) =
      conj (rhoCosShift y Φ (Zeta23.gammaOf ρ)) := by
  have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hIm : |(Zeta23.gammaOf (ρ : ℂ)).im| < 1 / 2 :=
    WeilEF.abs_gammaOf_im_lt ⟨hmem.2.1, hmem.2.2⟩
  have h54 : |(Zeta23.gammaOf (ρ : ℂ)).im| ≤ 5 / 4 := by linarith
  simp only [zetaCarrierReflect, Equiv.coe_fn_mk, gammaOf_reflect']
  exact rhoCosShift_conj y Φ (abs_im_lt_sqrt_two h54)

/-- Under `zetaCarrierReflect`, `(rhoCosShift y Φ (gammaOf (zetaCarrierReflect ρ))).re` equals
`(rhoCosShift y Φ (gammaOf ρ)).re`. -/
theorem re_rhoCosShift_gammaOf_reflect (y : ℝ) (Φ : ℂ → ℂ) (ρ : zetaZeroConfig.carrier) :
    (rhoCosShift y Φ (Zeta23.gammaOf (zetaCarrierReflect ρ))).re =
      (rhoCosShift y Φ (Zeta23.gammaOf ρ)).re := by
  rw [rhoCosShift_gammaOf_reflect, Complex.conj_re]

/-- Under `zetaCarrierOneSub` ($\rho \mapsto 1 - \rho$), every even $\Phi$ satisfies
`specSq Φ (gammaOf (zetaCarrierOneSub ρ)) = specSq Φ (gammaOf ρ)`. -/
theorem specSq_gammaOf_oneSub {Φ : ℂ → ℂ} (heven : ∀ z, Φ (-z) = Φ z)
    (ρ : zetaZeroConfig.carrier) :
    specSq Φ (Zeta23.gammaOf (zetaCarrierOneSub ρ)) = specSq Φ (Zeta23.gammaOf ρ) := by
  simp only [zetaCarrierOneSub, Equiv.coe_fn_mk, gammaOf_one_sub, specSq_neg_of_even heven]

/-- Under `zetaCarrierOneSub` ($\rho \mapsto 1 - \rho$), every even $\Phi$ satisfies
`rhoCosShift y Φ (gammaOf (zetaCarrierOneSub ρ)) = rhoCosShift y Φ (gammaOf ρ)`. -/
theorem rhoCosShift_gammaOf_oneSub (y : ℝ) {Φ : ℂ → ℂ} (heven : ∀ z, Φ (-z) = Φ z)
    (ρ : zetaZeroConfig.carrier) :
    rhoCosShift y Φ (Zeta23.gammaOf (zetaCarrierOneSub ρ)) =
      rhoCosShift y Φ (Zeta23.gammaOf ρ) := by
  simp only [zetaCarrierOneSub, Equiv.coe_fn_mk, gammaOf_one_sub, rhoCosShift, rhoC_neg,
    specSq_neg_of_even heven]

/-- **Schwarz-Symmetric Square Reduction**:
if $\Phi(\bar{z}) = \overline{\Phi(z)}$ at $z \in \mathbb{C}$, then `specSq Φ z = Φ z ^ 2`. -/
theorem specSq_eq_sq_of_conj_symm {Φ : ℂ → ℂ} {z : ℂ} (hconj : Φ (conj z) = conj (Φ z)) :
    specSq Φ z = Φ z ^ 2 := by
  unfold specSq
  rw [hconj, Complex.conj_conj, sq]

/-- **Real Part of a Schwarz-Symmetric `specSq`**:
if $\Phi(\bar{z}) = \overline{\Phi(z)}$ at $z \in \mathbb{C}$, then
`(specSq Φ z).re = (Φ z).re ^ 2 - (Φ z).im ^ 2`. -/
theorem re_specSq_eq_re_sq_sub_im_sq_of_conj_symm {Φ : ℂ → ℂ} {z : ℂ}
    (hconj : Φ (conj z) = conj (Φ z)) :
    (specSq Φ z).re = (Φ z).re ^ 2 - (Φ z).im ^ 2 := by
  rw [specSq_eq_sq_of_conj_symm hconj, sq, Complex.mul_re, ← sq, ← sq]

/-- `sechHalf` is Schwarz reflection-symmetric on all of $\mathbb{C}$:
`sechHalf (conj z) = conj (sechHalf z)`. -/
theorem sechHalf_conj (z : ℂ) : sechHalf (conj z) = conj (sechHalf z) := by
  unfold sechHalf
  rw [show conj z / 2 = conj (z / 2) by rw [map_div₀, map_ofNat],
    Complex.cosh_conj, map_inv₀]

/-- On `|z.im| < √2`, `cosComb t c Φ` preserves Schwarz reflection symmetry. -/
theorem cosComb_conj {N : ℕ} (t c : Fin N → ℝ) {Φ : ℂ → ℂ} {z : ℂ}
    (hz : |z.im| < Real.sqrt 2) (hΦ : Φ (conj z) = conj (Φ z)) :
    cosComb t c Φ (conj z) = conj (cosComb t c Φ z) := by
  unfold cosComb
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, Complex.conj_ofReal, ← hΦ,
    ← Complex.cos_conj, map_mul, Complex.conj_ofReal, (rhoC_conj hz).symm]

/-- On `|z.im| < √2`, `sinComb t c Φ` preserves Schwarz reflection symmetry. -/
theorem sinComb_conj {N : ℕ} (t c : Fin N → ℝ) {Φ : ℂ → ℂ} {z : ℂ}
    (hz : |z.im| < Real.sqrt 2) (hΦ : Φ (conj z) = conj (Φ z)) :
    sinComb t c Φ (conj z) = conj (sinComb t c Φ z) := by
  unfold sinComb
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, Complex.conj_ofReal, ← hΦ,
    ← Complex.sin_conj, map_mul, Complex.conj_ofReal, (rhoC_conj hz).symm]

/-- On `|z.im| < √2`, `specSq (cosComb t c sechHalf) z = cosComb t c sechHalf z ^ 2`. -/
theorem specSq_cosComb_sechHalf_eq_sq {N : ℕ} (t c : Fin N → ℝ) {z : ℂ}
    (hz : |z.im| < Real.sqrt 2) :
    specSq (cosComb t c sechHalf) z = cosComb t c sechHalf z ^ 2 :=
  specSq_eq_sq_of_conj_symm (cosComb_conj t c hz (sechHalf_conj z))

/-- On `|z.im| < √2`, `specSq (sinComb t c sechHalf) z = sinComb t c sechHalf z ^ 2`. -/
theorem specSq_sinComb_sechHalf_eq_sq {N : ℕ} (t c : Fin N → ℝ) {z : ℂ}
    (hz : |z.im| < Real.sqrt 2) :
    specSq (sinComb t c sechHalf) z = sinComb t c sechHalf z ^ 2 :=
  specSq_eq_sq_of_conj_symm (sinComb_conj t c hz (sechHalf_conj z))

/-- **Exact Real-vs-Imaginary Square Decomposition of the Zero-Side Wave-Packet Summand**:
at every nontrivial zero `ρ : zetaZeroConfig.carrier`,
`(specSq (cosComb t c sechHalf) (gammaOf ρ) + specSq (sinComb t c sechHalf) (gammaOf ρ)).re`
equals the difference between the real-part squares and the imaginary-part squares of
`cosComb t c sechHalf (gammaOf ρ)` and `sinComb t c sechHalf (gammaOf ρ)`. -/
theorem re_specSq_cosComb_add_sinComb_sechHalf_gammaOf {N : ℕ} (t c : Fin N → ℝ)
    (ρ : zetaZeroConfig.carrier) :
    (specSq (cosComb t c sechHalf) (Zeta23.gammaOf ρ) +
        specSq (sinComb t c sechHalf) (Zeta23.gammaOf ρ)).re =
      ((cosComb t c sechHalf (Zeta23.gammaOf ρ)).re ^ 2 +
          (sinComb t c sechHalf (Zeta23.gammaOf ρ)).re ^ 2) -
        ((cosComb t c sechHalf (Zeta23.gammaOf ρ)).im ^ 2 +
          (sinComb t c sechHalf (Zeta23.gammaOf ρ)).im ^ 2) := by
  have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hIm : |(Zeta23.gammaOf (ρ : ℂ)).im| < 1 / 2 :=
    WeilEF.abs_gammaOf_im_lt ⟨hmem.2.1, hmem.2.2⟩
  have h54 : |(Zeta23.gammaOf (ρ : ℂ)).im| ≤ 5 / 4 := by linarith
  have hz := abs_im_lt_sqrt_two h54
  rw [Complex.add_re,
    re_specSq_eq_re_sq_sub_im_sq_of_conj_symm (cosComb_conj t c hz (sechHalf_conj _)),
    re_specSq_eq_re_sq_sub_im_sq_of_conj_symm (sinComb_conj t c hz (sechHalf_conj _))]
  ring

/-! ## Section 2: Unconditional Zero-Side Vanishing of $\Xi$-Divisible `EvenStrip` Functions and of `RHTower.XiC` -/

/-- **Unconditional Zero-Side Vanishing of `evenWeilDensity Λ (specSq Φ)`**:
for any `EvenStrip Φ` that vanishes at `gammaOf ρ` for every nontrivial zero `ρ` of $\zeta$,
`evenWeilDensity Λ (specSq Φ) = 0`. -/
theorem evenWeilDensity_specSq_vonMangoldt_eq_zero_of_gammaOf_eq_zero {Φ : ℂ → ℂ}
    (hΦ : EvenStrip Φ) (hzero : ∀ ρ : zetaZeroConfig.carrier, Φ (Zeta23.gammaOf ρ) = 0) :
    evenWeilDensity (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (specSq Φ) = 0 := by
  rw [evenWeilDensity_specSq_vonMangoldt_eq_tsum_re hΦ]
  refine (tsum_congr fun ρ => ?_).trans tsum_zero
  unfold specSq
  rw [hzero ρ, zero_mul, Complex.zero_re, mul_zero]

/-- **Unconditional Vanishing of `cosineShiftFn Λ Φ y` at Every Shift $y \in \mathbb{R}$**:
for any `EvenStrip Φ` that vanishes at `gammaOf ρ` for every nontrivial zero `ρ` of $\zeta$,
`cosineShiftFn Λ Φ y = 0` identically for all $y \in \mathbb{R}$. -/
theorem cosineShiftFn_vonMangoldt_eq_zero_of_gammaOf_eq_zero {Φ : ℂ → ℂ}
    (hΦ : EvenStrip Φ) (hzero : ∀ ρ : zetaZeroConfig.carrier, Φ (Zeta23.gammaOf ρ) = 0)
    (y : ℝ) :
    cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) Φ y = 0 := by
  rw [cosineShiftFn_vonMangoldt_eq_tsum_re hΦ y]
  refine (tsum_congr fun ρ => ?_).trans tsum_zero
  unfold rhoCosShift specSq
  rw [hzero ρ, zero_mul, mul_zero, Complex.zero_re, mul_zero]

/-- **Unconditional Vanishing of All Toeplitz Quadratic Forms of a $\Xi$-Divisible `EvenStrip` Function**:
if `EvenStrip Φ` and `∀ ρ, Φ (gammaOf ρ) = 0`, then every finite Toeplitz form of
`cosineShiftFn Λ Φ` vanishes identically. -/
theorem sum_sum_cosineShiftFn_vonMangoldt_eq_zero_of_gammaOf_eq_zero {Φ : ℂ → ℂ}
    (hΦ : EvenStrip Φ) (hzero : ∀ ρ : zetaZeroConfig.carrier, Φ (Zeta23.gammaOf ρ) = 0)
    {N : ℕ} (t c : Fin N → ℝ) :
    (∑ i, ∑ j, c i * c j *
        cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) Φ (t j - t i)) = 0 := by
  simp_rw [cosineShiftFn_vonMangoldt_eq_zero_of_gammaOf_eq_zero hΦ hzero, mul_zero,
    Finset.sum_const_zero]

/-- `RHTower.XiC` vanishes at `gammaOf ρ` for every nontrivial zero `ρ : zetaZeroConfig.carrier`
(on or off the critical line). -/
theorem XiC_gammaOf_eq_zero (ρ : zetaZeroConfig.carrier) :
    RHTower.XiC (Zeta23.gammaOf ρ) = 0 := by
  have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hpt : (1 / 2 : ℂ) + Zeta23.gammaOf (ρ : ℂ) * I = ρ := by
    unfold Zeta23.gammaOf
    field_simp
    ring
  have hne : (ρ : ℂ) ≠ 1 := by
    intro h
    have := hmem.2.2
    rw [h, Complex.one_re] at this
    exact lt_irrefl 1 this
  rw [RHTower.XiC, hpt]
  exact (RHTower.xi_eq_zero_iff hmem.2.1 hne).mpr hmem.1

/-- For every `j : ℕ`, `xiShiftedGamma j` vanishes at `gammaOf ρ` for every nontrivial zero `ρ`. -/
theorem xiShiftedGamma_gammaOf_eq_zero (j : ℕ) (ρ : zetaZeroConfig.carrier) :
    xiShiftedGamma j (Zeta23.gammaOf ρ) = 0 := by
  unfold xiShiftedGamma
  rw [XiC_gammaOf_eq_zero ρ, zero_mul]

/-- `xiShiftedGamma 0` is identically `RHTower.XiC`. -/
theorem xiShiftedGamma_zero_eq_XiC : xiShiftedGamma 0 = RHTower.XiC := by
  funext z
  simp [xiShiftedGamma, shiftedGammaPoly]

/-- `RHTower.XiC` is an `EvenStrip` function (`EvenStrip RHTower.XiC`). -/
theorem evenStrip_XiC : EvenStrip RHTower.XiC := by
  obtain ⟨C, _, hs⟩ := exists_stripDecay_xiShiftedGamma_wide
  have hs0 := hs 0
  rw [xiShiftedGamma_zero_eq_XiC] at hs0
  refine ⟨⟨xiShiftedGammaRate, C * ((0 ! : ℝ) * (3 / 2 : ℝ) ^ 0), xiShiftedGammaRate_pos, hs0⟩,
    RHTower.XiC_even, fun r => ?_⟩
  rw [RHTower.XiC_ofReal, Complex.ofReal_im]

/-- **Unconditional Vanishing of `evenWeilDensity Λ (specSq RHTower.XiC)`**:
with **zero hypotheses**, `evenWeilDensity Λ (specSq RHTower.XiC) = 0`. -/
theorem evenWeilDensity_specSq_XiC_vonMangoldt_eq_zero :
    evenWeilDensity (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (specSq RHTower.XiC) = 0 :=
  evenWeilDensity_specSq_vonMangoldt_eq_zero_of_gammaOf_eq_zero evenStrip_XiC XiC_gammaOf_eq_zero

/-- **Unconditional Vanishing of `cosineShiftFn Λ RHTower.XiC y` at Every Shift $y \in \mathbb{R}$**:
with **zero hypotheses**, `cosineShiftFn Λ RHTower.XiC y = 0` for all $y \in \mathbb{R}$. -/
theorem cosineShiftFn_XiC_vonMangoldt_eq_zero (y : ℝ) :
    cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) RHTower.XiC y = 0 :=
  cosineShiftFn_vonMangoldt_eq_zero_of_gammaOf_eq_zero evenStrip_XiC XiC_gammaOf_eq_zero y

/-- **Unconditional Exact Prime-to-Archimedean/Pole Identity for `rhoCosShift y RHTower.XiC`**:
for every $y \in \mathbb{R}$, the prime sum of `rhoCosShift y RHTower.XiC` against $\Lambda$ equals
its pole plus archimedean energy unconditionally:
`evenPrimePart Λ (rhoCosShift y RHTower.XiC) = evenPolePart (rhoCosShift y RHTower.XiC) + (1 / (2 * π)) * evenArchPart (rhoCosShift y RHTower.XiC)`. -/
theorem evenPrimePart_rhoCosShift_XiC_vonMangoldt_eq (y : ℝ) :
    evenPrimePart (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (rhoCosShift y RHTower.XiC) =
      evenPolePart (rhoCosShift y RHTower.XiC) +
        1 / (2 * Real.pi) * evenArchPart (rhoCosShift y RHTower.XiC) := by
  have h0 := cosineShiftFn_XiC_vonMangoldt_eq_zero y
  unfold cosineShiftFn evenWeilDensity at h0
  unfold evenPolePart evenArchPart evenPrimePart
  linarith

/-- For any `EvenStrip Φ` and any `Multiplier h`, `z ↦ Φ z * h z` is also an `EvenStrip`
function. -/
theorem evenStrip_mul_multiplier {Φ h : ℂ → ℂ} (hΦ : EvenStrip Φ) (hh : Multiplier h) :
    EvenStrip (fun z => Φ z * h z) := by
  obtain ⟨ε₁, C₁, hε₁, hs₁⟩ := hΦ.strip
  obtain ⟨ε₂, C₂, hε₂, hs₂⟩ := hh.strip
  have hC₁ := hs₁.const_nonneg (by norm_num)
  have hC₂ := hs₂.const_nonneg (by norm_num)
  refine ⟨⟨ε₁ + ε₂, C₁ * C₂, add_pos hε₁ hε₂, fun z hz => ?_, fun z hz => ?_⟩,
    fun z => ?_, fun r => ?_⟩
  · exact (hs₁.diff z hz).mul (hs₂.diff z (by linarith))
  · rw [norm_mul]
    calc ‖Φ z‖ * ‖h z‖
        ≤ (C₁ * Real.exp (-(ε₁ * |z.re|))) * (C₂ * Real.exp (-(ε₂ * |z.re|))) :=
          mul_le_mul (hs₁.bound z hz) (hs₂.bound z (by linarith)) (norm_nonneg _) (by positivity)
      _ = C₁ * C₂ * (Real.exp (-(ε₁ * |z.re|)) * Real.exp (-(ε₂ * |z.re|))) := by ring
      _ = C₁ * C₂ * Real.exp (-((ε₁ + ε₂) * |z.re|)) := by rw [← Real.exp_add]; ring_nf
  · rw [hΦ.even, hh.even]
  · have hhr : (h r).im = 0 := by
      have hc := hh.conj_symm r
      rw [Complex.conj_ofReal] at hc
      exact Complex.conj_eq_iff_im.mp hc.symm
    rw [Complex.mul_im, hΦ.real, hhr, mul_zero, zero_mul, add_zero]

/-- **Unconditional Vanishing of `cosineShiftFn Λ (RHTower.XiC * h) y` for Every Multiplier $h$**:
for every `Multiplier h` and every $y \in \mathbb{R}$,
`cosineShiftFn Λ (fun z => RHTower.XiC z * h z) y = 0`. -/
theorem cosineShiftFn_XiC_mul_multiplier_vonMangoldt_eq_zero {h : ℂ → ℂ} (hh : Multiplier h)
    (y : ℝ) :
    cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (fun z => RHTower.XiC z * h z) y = 0 :=
  cosineShiftFn_vonMangoldt_eq_zero_of_gammaOf_eq_zero (evenStrip_mul_multiplier evenStrip_XiC hh)
    (fun ρ => by rw [XiC_gammaOf_eq_zero ρ, zero_mul]) y

/-! ## Section 3: Individual `xiShiftedGamma j` Annihilation and Global Convolution Annihilation of `cosineShiftFn Λ sechHalf` -/

/-- Unconditional equality `atomPairing Λ (crossCorr (stripTest Φ) (stripTest Φ)) = abelPrimePairing Λ (stripTest Φ)`
for any `Φ` with `StripDecay Φ (5 / 4) ε C` (`0 < ε`), without requiring `Φ` to be even. -/
theorem atomPairing_stripTest_eq_abelPrimePairing_of_stripDecay {Φ : ℂ → ℂ} {ε C : ℝ}
    (hε : 0 < ε) (hs : StripDecay Φ (5 / 4) ε C) :
    atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (crossCorr (stripTest Φ) (stripTest Φ)) =
      abelPrimePairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (stripTest Φ) := by
  have hE : ExpDecayTest (stripTest Φ) := expDecayTest_stripTest (by norm_num) hε hs
  obtain ⟨_, hC', hdec⟩ := decayBound_stripTest (by norm_num : (1 / 2 : ℝ) < 5 / 4) hε hs
  have hlim1 :
      Tendsto
        (fun L : ℝ =>
          atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
            (crossCorr (truncTest (stripTest Φ) L) (truncTest (stripTest Φ) L)))
        atTop
        (𝓝 (atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (crossCorr (stripTest Φ) (stripTest Φ)))) := by
    refine tendsto_atomPairing_truncTest_of_growth
      abs_vonMangoldt_le_sqrt_mul_one_add_log hE (by norm_num : (1 : ℝ) < 5 / 4) hC' fun x => ?_
    have hx := (hdec x).1
    rwa [show (1 / 2 : ℝ) + (5 / 4 - 1 / 2) = 5 / 4 by ring] at hx
  have hlim2 :
      Tendsto
        (fun L : ℝ =>
          atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
            (crossCorr (truncTest (stripTest Φ) L) (truncTest (stripTest Φ) L)))
        atTop
        (𝓝 (abelPrimePairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (stripTest Φ))) :=
    tendsto_atomPairing_truncTest_abelPrimePairing hE (A := 7)
      (w := fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (fun N => abs_primeWeightPartialSum_vonMangoldt_le N)
  exact tendsto_nhds_unique hlim1 hlim2

/-- **Unconditional Vanishing of Each Individual `evenWeilDensity Λ (specSq (xiShiftedGamma j))`**:
for the actual von Mangoldt function $\Lambda$, each shifted-Gamma member `xiShiftedGamma j` has
`evenWeilDensity Λ (specSq (xiShiftedGamma j)) = 0` individually (without needing to sum over $j$
against twisted-arc weights). -/
theorem evenWeilDensity_specSq_xiShiftedGamma_vonMangoldt_eq_zero (j : ℕ) :
    evenWeilDensity (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (specSq (xiShiftedGamma j)) = 0 := by
  obtain ⟨C, _, hs⟩ := exists_stripDecay_xiShiftedGamma_wide
  rw [evenWeilDensity_specSq (by norm_num : (1 / 2 : ℝ) < 5 / 4) xiShiftedGammaRate_pos (hs j)
      (xiShiftedGamma_neg_ofReal j),
    atomPairing_stripTest_eq_abelPrimePairing_of_stripDecay xiShiftedGammaRate_pos (hs j),
    show stripTest (xiShiftedGamma j) = xiShiftedGammaTest j from rfl,
    archPoleEnergy_xiShiftedGammaTest_eq_abelPrimePairing j, sub_self]

/-- **Unconditional 1D Sech-Kernel Orthogonality of `cosineShiftFn Λ sechHalf` Against Every `xiShiftedGamma j`**:
for every $j \in \mathbb{N}$ individually,
`∫ t : ℝ, sechKernel (xiShiftedGamma j) t * cosineShiftFn Λ sechHalf t = 0`. -/
theorem integral_sechKernel_xiShiftedGamma_mul_cosineShiftFn_sechHalf_vonMangoldt_eq_zero
    (j : ℕ) :
    ∫ t : ℝ, sechKernel (xiShiftedGamma j) t *
      cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf t = 0 := by
  rw [← evenWeilDensity_xiShiftedGamma_eq_integral_sechKernel
    abs_vonMangoldt_le_sqrt_mul_one_add_log j]
  exact evenWeilDensity_specSq_xiShiftedGamma_vonMangoldt_eq_zero j

/-- The ground-state multiplier `xiCoshHalf z = RHTower.XiC z * Complex.cosh (z / 2)` bridging
`sechHalf` directly to `RHTower.XiC`. -/
def xiCoshHalf (z : ℂ) : ℂ := RHTower.XiC z * Complex.cosh (z / 2)

/-- `xiCoshHalf` is a `Multiplier` (`StripDecay xiCoshHalf (9 / 4) (1 / 4) C`, even, and
Schwarz reflection-symmetric). -/
theorem multiplier_xiCoshHalf : Multiplier xiCoshHalf := by
  have hpi : 2 * (3 / 4 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_d2]
  obtain ⟨CΞ, hCΞ, hΞ⟩ := RHTower.exists_norm_XiC_horizontal_le_wide (A := 9 / 4) (δ := 3 / 4)
    (by norm_num) (by norm_num) hpi
  refine ⟨⟨1 / 4, CΞ, by norm_num, fun z _ => ?_, fun z hz => ?_⟩, fun z => ?_, fun z => ?_⟩
  · unfold xiCoshHalf
    exact (RHTower.XiC_differentiable z).mul
      (Complex.differentiable_cosh.differentiableAt.comp z (differentiableAt_id.div_const 2))
  · unfold xiCoshHalf
    rw [norm_mul]
    have hz' : z = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im z).symm
    have hX : ‖RHTower.XiC z‖ ≤ CΞ * Real.exp (-(3 / 4 * |z.re|)) := by
      have := hΞ z.re z.im hz
      rwa [← hz'] at this
    have hc : ‖Complex.cosh (z / 2)‖ ≤ Real.exp (1 / 2 * |z.re|) := by
      have h1 := norm_cosh_le_real_cosh_re (z / 2)
      have hre : (z / 2).re = z.re / 2 := by simp
      rw [hre] at h1
      refine h1.trans ((real_cosh_le_exp_abs (z.re / 2)).trans (le_of_eq ?_))
      rw [abs_div, abs_two]; ring_nf
    calc ‖RHTower.XiC z‖ * ‖Complex.cosh (z / 2)‖
        ≤ (CΞ * Real.exp (-(3 / 4 * |z.re|))) * Real.exp (1 / 2 * |z.re|) :=
          mul_le_mul hX hc (norm_nonneg _) (by positivity)
      _ = CΞ * (Real.exp (-(3 / 4 * |z.re|)) * Real.exp (1 / 2 * |z.re|)) := by ring
      _ = CΞ * Real.exp (-(1 / 4 * |z.re|)) := by rw [← Real.exp_add]; ring_nf
  · unfold xiCoshHalf
    rw [RHTower.XiC_even, neg_div, Complex.cosh_neg]
  · unfold xiCoshHalf
    rw [map_mul, RHTower.XiC_conj,
      show conj z / 2 = conj (z / 2) by rw [map_div₀, map_ofNat], Complex.cosh_conj]

/-- On `|z.im| ≤ 9 / 4`, `sechHalf z * xiCoshHalf z = RHTower.XiC z`. -/
theorem sechHalf_mul_xiCoshHalf {z : ℂ} (hz : |z.im| ≤ 9 / 4) :
    sechHalf z * xiCoshHalf z = RHTower.XiC z := by
  unfold sechHalf xiCoshHalf
  have hne := cosh_half_ne_zero hz
  field_simp

/-- At every shift $y \in \mathbb{R}$, `cosineShiftFn lam (sechHalf * xiCoshHalf) y` equals
`cosineShiftFn lam RHTower.XiC y`. -/
theorem cosineShiftFn_sechHalf_mul_xiCoshHalf_eq (lam : ℕ → ℝ) (y : ℝ) :
    cosineShiftFn lam (fun z => sechHalf z * xiCoshHalf z) y =
      cosineShiftFn lam RHTower.XiC y := by
  have heq : ∀ z : ℂ, |z.im| ≤ 5 / 4 →
      rhoCosShift y (fun w => sechHalf w * xiCoshHalf w) z = rhoCosShift y RHTower.XiC z := by
    intro z hz
    unfold rhoCosShift specSq
    dsimp only
    have hz1 : |z.im| ≤ 9 / 4 := by linarith
    have hz2 : |(conj z).im| ≤ 9 / 4 := by rw [Complex.conj_im, abs_neg]; linarith
    rw [sechHalf_mul_xiCoshHalf hz1, sechHalf_mul_xiCoshHalf hz2]
  exact evenWeilDensity_congr (heq _ (by norm_num [abs_of_pos]))
    (heq _ (by norm_num [abs_of_pos])) (fun r => heq _ (by simp; norm_num))

/-- **Unconditional Global Convolution Annihilation of `cosineShiftFn Λ sechHalf`**:
for every shift $y \in \mathbb{R}$, the shifted-cosine convolution of `cosineShiftFn Λ sechHalf`
against `stripTest (specSq (rhoLift xiCoshHalf))` vanishes identically:
`∫ t : ℝ, cosShiftKernel (stripTest (specSq (rhoLift xiCoshHalf))) y t * cosineShiftFn Λ sechHalf t = 0`. -/
theorem integral_cosShiftKernel_xiCoshHalf_mul_cosineShiftFn_sechHalf_vonMangoldt_eq_zero
    (y : ℝ) :
    ∫ t : ℝ, cosShiftKernel (stripTest (specSq (rhoLift xiCoshHalf))) y t *
      cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf t = 0 := by
  rw [← cosineShiftFn_mul_eq_integral_cosShiftKernel_unconditional
      abs_vonMangoldt_le_sqrt_mul_one_add_log evenStrip_sechHalf multiplier_xiCoshHalf y,
    cosineShiftFn_sechHalf_mul_xiCoshHalf_eq, cosineShiftFn_XiC_vonMangoldt_eq_zero]

/-- **Strict Positivity of the $j = 0$ Ground-State Lift on the Sub-Threshold Segment `ρ ^ 2 ≤ 2`**:
for every $\rho \in \mathbb{R}$ with $\rho^2 \le 2$,
`0 < (rhoLift (sechWeight (xiShiftedGamma 0)) ρ).re`. -/
theorem re_rhoLift_sechWeight_xiShiftedGamma_zero_pos_of_sq_le_two {ρ : ℝ} (hρ : ρ ^ 2 ≤ 2) :
    0 < (rhoLift (sechWeight (xiShiftedGamma 0)) ρ).re := by
  rw [rhoLift_of_sq_le_two (multiplier_sechWeight_xiShiftedGamma 0).even hρ,
    sechWeight_xiShiftedGamma_I_mul, Complex.ofReal_re, shiftedGammaLaplaceFactor_zero, mul_one]
  have hy : |Real.sqrt (2 - ρ ^ 2)| ≤ 9 / 4 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    have h1 : Real.sqrt (2 - ρ ^ 2) ≤ Real.sqrt 2 :=
      Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ρ])
    have h2 : Real.sqrt 2 ≤ 9 / 4 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    linarith
  have hθ := thetaSourceLaplace_pos (Real.sqrt (2 - ρ ^ 2))
  have hc := cos_half_pos hy
  positivity

/-- **Global Nonnegativity of the $j = 0$ Ground-State Lift on All of $\mathbb{R}$**:
for every $\rho \in \mathbb{R}$ (both $\rho^2 \le 2$ and $\rho^2 \ge 2$),
`0 ≤ (rhoLift (sechWeight (xiShiftedGamma 0)) ρ).re`. -/
theorem re_rhoLift_sechWeight_xiShiftedGamma_zero_nonneg (ρ : ℝ) :
    0 ≤ (rhoLift (sechWeight (xiShiftedGamma 0)) ρ).re := by
  rcases le_or_gt (ρ ^ 2) 2 with hρ | hρ
  · exact (re_rhoLift_sechWeight_xiShiftedGamma_zero_pos_of_sq_le_two hρ).le
  · exact re_rhoLift_sechWeight_nonneg (xiShiftedGamma 0) hρ.le

end RHTower.CHMDStage16

end
