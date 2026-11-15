import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.PhaseExtraction.TheNonprincipalRowRetainsTheTarget
import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.ShortColumnsOfTheEisensteinLatticeAreIncoherent

/-!
# Signed extraction over smooth arithmetic rows

After the reciprocal target is subtracted, the character-weighted completed
row is exactly a linear combination of the sextic and cubic residue characters.
Both have mean zero. Their finite Fourier coefficients have square-root size,
so lattice Poisson summation bounds the signed extraction error to every order
when the row scale exceeds the conductor. All parameters in the bound are
explicit; the reciprocal target is retained before taking norms.
-/

noncomputable section
open scoped BigOperators Classical FourierTransform

namespace GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies
open HTGeometry HTGeometry.IntegerLatticePoisson MetaplecticMobiusDescent
  MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.Eisenstein.Coordinates
  FamilyContinuationTheory

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "Z" => Fin 2 → ℤ

private theorem norm_character_fourier_le {F : Type*} [Field F] [Fintype F]
    {χ : MulChar F ℂ} (hχ : χ ≠ 1) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (h : F) :
    ‖∑ d : F, χ d * ψ (-(h * d))‖ ≤ Real.sqrt (Fintype.card F) := by
  by_cases hh : h = 0
  · simp only [hh, zero_mul, neg_zero, AddChar.map_zero_eq_one, mul_one,
      MulChar.sum_eq_zero_of_ne_one hχ, norm_zero]
    exact Real.sqrt_nonneg _
  · let u : Fˣ := Units.mk0 (-h) (neg_ne_zero.mpr hh)
    have he : (∑ d : F, χ d * ψ (-(h * d))) = gaussSum χ (ψ.mulShift u) := by
      simp only [gaussSum, AddChar.mulShift_apply, u, Units.val_mk0, neg_mul]
    rw [he, gaussSum_mulShift_eq, norm_mul,
      Complex.norm_eq_one_of_mem_rootsOfUnity ((χ⁻¹).apply_mem_rootsOfUnity u),
      one_mul, ArithmeticEffectivityTheory.norm_gaussSum_eq_sqrt_card hχ hψ]

/-- The constant mode of the corrected local row. -/
def rowTargetConstant (Q R η X Y V : ℂ) : ℂ :=
  (1 - R * Q⁻¹ - η * (Q - 1) * X * Y * V) * (1 - V)⁻¹

variable (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P)

/-- Signed discrepancy from the reciprocal target on the actual residue field.
The principal character retains the restriction to nonzero residue classes. -/
def rowTargetResidual (Q R η X Y V : ℂ) (d : O ⧸ P) : ℂ :=
  complexSexticChar P hg d *
      rowTargetPolynomial Q R η X Y V (complexSexticChar P hg d) +
    η * X * (1 : MulChar (O ⧸ P) ℂ) d

/-- Target subtraction leaves two nonprincipal arithmetic modes, including at zero residue. -/
theorem rowTargetResidual_eq (Q R η X Y V : ℂ) (d : O ⧸ P) :
    rowTargetResidual P hg Q R η X Y V d =
      rowTargetConstant Q R η X Y V * complexSexticChar P hg d +
        (R * Y) * complexCubicChar P hg d := by
  have hi : complexSexticChar P hg d * (complexSexticChar P hg d)⁻¹ =
      (1 : MulChar (O ⧸ P) ℂ) d := by
    rw [← MulChar.inv_apply_eq_inv', ← MulChar.mul_apply, mul_inv_cancel]
  have hs : complexSexticChar P hg d ^ 2 = complexCubicChar P hg d := by
    rw [← MulChar.pow_apply' _ (by norm_num : (2 : ℕ) ≠ 0),
      (complexSexticChar_powers P hg).1]
  unfold rowTargetResidual rowTargetPolynomial rowTargetConstant
  rw [← hi, ← hs]
  ring

theorem sum_rowTargetResidual_eq_zero (Q R η X Y V : ℂ) :
    ∑ d, rowTargetResidual P hg Q R η X Y V d = 0 := by
  simp_rw [rowTargetResidual_eq]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    MulChar.sum_eq_zero_of_ne_one (complexSexticChar_ne_one P hg),
    MulChar.sum_eq_zero_of_ne_one (complexCubicChar_ne_one P hg),
    mul_zero, mul_zero, add_zero]

/-- Gauss cancellation controls every Fourier coefficient of the signed extraction error. -/
theorem norm_rowTargetResidual_fourier_le (Q R η X Y V : ℂ)
    {ψ : AddChar (O ⧸ P) ℂ} (hψ : ψ.IsPrimitive) (h : O ⧸ P) :
    ‖∑ d, rowTargetResidual P hg Q R η X Y V d * ψ (-(h * d))‖ ≤
      Real.sqrt (Fintype.card (O ⧸ P)) * (‖rowTargetConstant Q R η X Y V‖ + ‖R * Y‖) := by
  simp_rw [rowTargetResidual_eq, add_mul, mul_assoc]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  calc
    _ ≤ ‖rowTargetConstant Q R η X Y V *
          ∑ d, complexSexticChar P hg d * ψ (-(h * d))‖ +
        ‖(R * Y) * ∑ d, complexCubicChar P hg d * ψ (-(h * d))‖ := norm_add_le _ _
    _ ≤ ‖rowTargetConstant Q R η X Y V‖ * Real.sqrt (Fintype.card (O ⧸ P)) +
        ‖R * Y‖ * Real.sqrt (Fintype.card (O ⧸ P)) := by
      rw [norm_mul, norm_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (norm_character_fourier_le (complexSexticChar_ne_one P hg) hψ h) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left
          (norm_character_fourier_le (complexCubicChar_ne_one P hg) hψ h) (norm_nonneg _))
    _ = _ := by ring

/-- The normalized Fourier mass has no loss beyond square-root conductor size. -/
theorem mean_norm_rowTargetResidual_fourier_le (Q R η X Y V : ℂ)
    {ψ : AddChar (O ⧸ P) ℂ} (hψ : ψ.IsPrimitive) :
    (Fintype.card (O ⧸ P) : ℝ)⁻¹ *
        ∑ h : O ⧸ P, ‖∑ d, rowTargetResidual P hg Q R η X Y V d * ψ (-(h * d))‖ ≤
      Real.sqrt (Fintype.card (O ⧸ P)) * (‖rowTargetConstant Q R η X Y V‖ + ‖R * Y‖) := by
  have hc : (Fintype.card (O ⧸ P) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    _ ≤ (Fintype.card (O ⧸ P) : ℝ)⁻¹ *
        ∑ _h : O ⧸ P, Real.sqrt (Fintype.card (O ⧸ P)) *
          (‖rowTargetConstant Q R η X Y V‖ + ‖R * Y‖) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      exact Finset.sum_le_sum fun h _ => norm_rowTargetResidual_fourier_le P hg Q R η X Y V hψ h
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- Explicit geometric decay from the separation of nonzero dual Eisenstein residues. -/
def eisensteinRowDecay (f : SchwartzMap E ℂ) (M : ℕ) (B : E ≃L[ℝ] E)
    (μ : ℝ) (a b : ℤ) : ℝ :=
  latticeScale B * ((SchwartzMap.seminorm ℝ M 0 (𝓕 f) * 9 ^ M *
    ∑' m : Z, latticeBracket m ^ (-(M : ℝ))) *
      (μ * Real.sqrt (2 / (3 * (eisNormZ a b : ℝ)))) ^ (-(M : ℝ)))

/-- A positive lower bound for the expansion of the inverse adjoint, determined by `B`. -/
def eisensteinDualScale (B : E ≃L[ℝ] E) : ℝ :=
  (‖(inverseAdjointEquiv B).symm.toContinuousLinearMap‖ + 1)⁻¹

theorem eisensteinDualScale_pos (B : E ≃L[ℝ] E) : 0 < eisensteinDualScale B := by
  unfold eisensteinDualScale
  positivity

theorem eisensteinDualScale_mul_norm_le (B : E ≃L[ℝ] E) (v : E) :
    eisensteinDualScale B * ‖v‖ ≤ ‖inverseAdjoint B v‖ := by
  have hn := (inverseAdjointEquiv B).symm.toContinuousLinearMap.le_opNorm
    ((inverseAdjointEquiv B) v)
  change ‖(inverseAdjointEquiv B).symm ((inverseAdjointEquiv B) v)‖ ≤
    ‖(inverseAdjointEquiv B).symm.toContinuousLinearMap‖ * ‖inverseAdjoint B v‖ at hn
  rw [ContinuousLinearEquiv.symm_apply_apply] at hn
  have hp : 0 < ‖(inverseAdjointEquiv B).symm.toContinuousLinearMap‖ + 1 := by positivity
  rw [eisensteinDualScale, inv_mul_eq_div]
  apply (div_le_iff₀ hp).mpr
  exact hn.trans (by nlinarith only [norm_nonneg (inverseAdjoint B v)])

/-- Signed extraction on the lattice: the reciprocal target is removed before the norm,
and the remaining actual arithmetic modes satisfy an explicit Poisson bound. -/
theorem norm_tsum_rowTargetResidual_le (f : SchwartzMap E ℂ) {M : ℕ} (hM : (2 : ℝ) < M)
    (B : E ≃L[ℝ] E) {μ : ℝ} (hμ : 0 < μ)
    (hT : ∀ v, μ * ‖v‖ ≤ ‖inverseAdjoint B v‖)
    (a b : ℤ) [hc : NeZero (eval a b)] [(Ideal.span {eval a b}).IsMaximal]
    (hg : lambda ∉ Ideal.span {eval a b}) (Q R η X Y V : ℂ) :
    ‖∑' n : Z, rowTargetResidual (Ideal.span {eval a b}) hg Q R η X Y V
          (Ideal.Quotient.mk _ (eval (n 0) (n 1))) * f (B (euclideanIntegerPoint n))‖ ≤
      eisensteinRowDecay f M B μ a b * Real.sqrt (Fintype.card (O ⧸ Ideal.span {eval a b})) *
        (‖rowTargetConstant Q R η X Y V‖ + ‖R * Y‖) := by
  have h := norm_tsum_eisensteinColumn_le f hM B hμ hT a b
    (rowTargetResidual (Ideal.span {eval a b}) hg Q R η X Y V)
    (sum_rowTargetResidual_eq_zero (Ideal.span {eval a b}) hg Q R η X Y V)
  change _ ≤ eisensteinRowDecay f M B μ a b * _ at h
  have hd : 0 ≤ eisensteinRowDecay f M B μ a b := by
    have hB := (latticeScale_pos B).le
    have hs := (SchwartzMap.seminorm ℝ M 0 (𝓕 f)).coe_nonneg
    unfold eisensteinRowDecay
    positivity
  refine h.trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (mean_norm_rowTargetResidual_fourier_le (Ideal.span {eval a b}) hg Q R η X Y V
      (principalTraceChar_primitive _ hc.ne)) hd

/-- Pointwise matching with the literal local series. At zero residue the character
annihilates the row; elsewhere its convergence is supplied by the local Poisson identity. -/
theorem rowTargetResidual_localTerm (π : O) [NeZero π]
    [(Ideal.span {π}).IsMaximal] (hlam : lambda ∉ Ideal.span {π})
    (h2 : (2 : O) ∉ Ideal.span {π}) (hprim : lambda ^ 2 ∣ π - 1)
    (η X Y V : ℂ) (hV : ‖V‖ < 1) (hY : ‖Y‖ < 1)
    (hR : ‖primeR π η X V‖ < 1) (u : O) :
    let d := Ideal.Quotient.mk (Ideal.span {π}) u
    complexSexticChar (Ideal.span {π}) hlam d * (1 - primeR π η X V) *
        ((∑' v, localTerm π η X Y V u 0 v) -
          complexSexticChar (Ideal.span {π}) hlam d * Y *
            (1 - complexSexticChar (Ideal.span {π}) hlam d * Y)⁻¹) +
      η * X * (1 : MulChar (O ⧸ Ideal.span {π}) ℂ) d =
        rowTargetResidual (Ideal.span {π}) hlam (primeQ π) (primeR π η X V) η X Y V d := by
  dsimp only
  by_cases hu : u ∈ Ideal.span {π}
  · have hd : Ideal.Quotient.mk (Ideal.span {π}) u = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hu
    simp only [hd, rowTargetResidual, MulChar.map_zero, zero_mul, mul_zero, add_zero]
  · have hd : Ideal.Quotient.mk (Ideal.span {π}) u ≠ 0 := by
      intro he
      exact hu (Ideal.Quotient.eq_zero_iff_mem.mp he)
    have hW : ‖complexSexticChar (Ideal.span {π}) hlam
        (Ideal.Quotient.mk _ u) * Y‖ < 1 := by
      rw [norm_mul, norm_sexticChar_eq_indicator, if_neg hd, one_mul]
      exact hY
    have hR0 : 1 - primeR π η X V ≠ 0 := by
      intro he
      rw [← sub_eq_zero.mp he, norm_one] at hR
      exact (lt_irrefl _) hR
    rw [(hasSum_localTerm_rowLocalSum π hlam h2 hprim η X Y V hu hV hW hR).tsum_eq,
      mul_assoc, rowLocalSum_remove_completion _ _ _ _ _ _ _ hR0]
    rfl

/-- The same signed estimate for the actual Poisson coefficient series, on its
convergence domain. The main term is exactly the reciprocal target times the
coprimality indicator, rather than an absolute-value replacement. -/
theorem norm_tsum_localTerm_target_error_le (f : SchwartzMap E ℂ) {M : ℕ}
    (hM : (2 : ℝ) < M) (B : E ≃L[ℝ] E)
    (a b : ℤ) [NeZero (eval a b)] [(Ideal.span {eval a b}).IsMaximal]
    (hlam : lambda ∉ Ideal.span {eval a b}) (h2 : (2 : O) ∉ Ideal.span {eval a b})
    (hprim : lambda ^ 2 ∣ eval a b - 1) (η X Y V : ℂ)
    (hV : ‖V‖ < 1) (hY : ‖Y‖ < 1) (hR : ‖primeR (eval a b) η X V‖ < 1) :
    ‖∑' n : Z,
      (let d := Ideal.Quotient.mk (Ideal.span {eval a b}) (eval (n 0) (n 1))
       complexSexticChar (Ideal.span {eval a b}) hlam d * (1 - primeR (eval a b) η X V) *
           ((∑' v, localTerm (eval a b) η X Y V (eval (n 0) (n 1)) 0 v) -
             complexSexticChar (Ideal.span {eval a b}) hlam d * Y *
               (1 - complexSexticChar (Ideal.span {eval a b}) hlam d * Y)⁻¹) +
         η * X * (1 : MulChar (O ⧸ Ideal.span {eval a b}) ℂ) d) *
           f (B (euclideanIntegerPoint n))‖ ≤
      eisensteinRowDecay f M B (eisensteinDualScale B) a b *
        Real.sqrt (Fintype.card (O ⧸ Ideal.span {eval a b})) *
        (‖rowTargetConstant (primeQ (eval a b)) (primeR (eval a b) η X V) η X Y V‖ +
          ‖primeR (eval a b) η X V * Y‖) := by
  simp_rw [rowTargetResidual_localTerm (eval a b) hlam h2 hprim η X Y V hV hY hR]
  exact norm_tsum_rowTargetResidual_le f hM B (eisensteinDualScale_pos B)
    (eisensteinDualScale_mul_norm_le B) a b hlam _ _ η X Y V

end GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies
