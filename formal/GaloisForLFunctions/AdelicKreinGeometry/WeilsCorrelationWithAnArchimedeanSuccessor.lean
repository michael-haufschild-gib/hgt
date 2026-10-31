import GaloisForLFunctions.AdelicKreinGeometry.ThePontryaginExtensionsOfWeilsCorrelation
import GaloisForLFunctions.AdelicKreinGeometry.TheHeckeBoostAndTheConformalSuccessorAreOneState
import GaloisForLFunctions.HeckeKreinToeplitz.FiniteIndexIsPositiveMinusFiniteRank
import GaloisForLFunctions.ArithmeticPositiveDuality.AMautnerPhenomenonForTheAffineGroupOfQ

/-!
# Weil's correlation with an archimedean successor

Weil's dilation data and the integer successor meet only at infinite index. The archimedean
successor carries no such cost. The **archimedean Weil state**

  `φ_c(x ↦ ax + b) = ratCorr(|a|) − c|a|^{−1/2}|b|`,  `c > 0`,

the blind extension of Weil's correlation plus the conformal induction of `−c|b|`, has

* dilation reading Weil's correlation (`weilArchState_dilation`);
* translation reading `ratCorr(1) − c|b|`, a nonconstant successor, conformal of exponent one up to
  the constant (`weilArchState_translation`);
* index `max(1, κ(K_ζ)) ≤ κ(φ_c) ≤ κ(K_ζ) + 1` (`negIndex_weilArchState_le`,
  `le_negIndex_weilArchState`, `one_le_negIndex_weilArchState`).

So Weil's dilation data has carriers of finite index with a nonconstant successor exactly when
`κ(K_ζ)` is finite (`negIndex_weilArchState_lt_top_iff`), and when `κ(K_ζ) = 0` the index is one
(`negIndex_weilArchState_eq_one_of_zero`). The no-go for the integer successor is a statement about
the integer successor, not about successors.
-/

open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

variable {K : Type*} [Field K] {v : AbsoluteValue K ℝ} {s : ℝ}

/-- Conformal induction of a Hermitian successor is Hermitian. -/
theorem isHermKernel_conformalInduction {ψ : Multiplicative K → ℂ} (hψ : IsConformal v s ψ)
    (hk : IsHermKernel ψ) : IsHermKernel (conformalInduction v s ψ) := fun g => by
  have h := conformalInduction_inv_mul hψ g 1
  rw [mul_one] at h
  rw [h, slopePow_one, shiftOf_one, zero_sub, ofAdd_neg, hk, conformalInduction, map_mul,
    Complex.conj_ofReal, mul_one]

/-- **The archimedean Weil state** `ratCorr(|a|) − c|a|^{−1/2}|b|`. -/
def weilArchState (c : ℝ) (g : AffineGroupQ) : ℂ :=
  blindWeilState g +
    conformalInduction Rat.AbsoluteValue.real 1 (fun m => (c : ℂ) * negAbsRat m) g

theorem weilArchState_dilation (c : ℝ) (u : posUnits) :
    weilArchState c (dilation u) = ratCorr u := by
  have h0 : shiftOf (dilation (u : ℚˣ)) = 0 := affShift_dilation _
  simp [weilArchState, blindWeilState_dilation, conformalInduction, h0, negAbsRat, absRat]

theorem weilArchState_translation (c : ℝ) (b : ℚ) :
    weilArchState c (translation b) = splineCorr 0 - (c : ℂ) * ((|b| : ℚ) : ℂ) := by
  have h1 : slopePow Rat.AbsoluteValue.real 1 (translation b) = 1 := slopePow_translation _ _ b
  have h2 : shiftOf (translation b) = b := affShift_translation b
  simp only [weilArchState, blindWeilState_translation, conformalInduction, h1, h2, inv_one,
    Complex.ofReal_one, one_mul, negAbsRat, absRat, toAdd_ofAdd]
  ring

theorem isHermKernel_blindWeilState : IsHermKernel blindWeilState :=
  isHermKernel_ratCorr.comp _

theorem isHermKernel_mul_negAbsRat (c : ℝ) : IsHermKernel fun m => (c : ℂ) * negAbsRat m :=
  fun m => by
    show (c : ℂ) * negAbsRat m⁻¹ = conj ((c : ℂ) * negAbsRat m)
    rw [isHermKernel_negAbsRat m, map_mul, Complex.conj_ofReal]

/-- **Upper bound**: `κ(φ_c) ≤ κ(K_ζ) + 1`. -/
theorem negIndex_weilArchState_le {c : ℝ} (hc : 0 < c) :
    negIndex (weilArchState c) ≤ negIndex zetaKernel + 1 := by
  have hψ := isConformal_negAbsRat c
  have h := negIndex_add_le isHermKernel_blindWeilState
    (isHermKernel_conformalInduction hψ (isHermKernel_mul_negAbsRat c))
  rw [negIndex_blindWeilState, negIndex_conformalInduction hψ, negIndex_ofReal_mul _ hc,
    negIndex_negAbsRat] at h
  exact h

/-- **Lower bound**: `κ(K_ζ) ≤ κ(φ_c)`. -/
theorem le_negIndex_weilArchState (c : ℝ) : negIndex zetaKernel ≤ negIndex (weilArchState c) :=
  negIndex_le_of_weil_extension (weilArchState_dilation c)

/-- The translations of `Aff(ℚ)` as a homomorphism. -/
def translationHomQ : Multiplicative ℚ →* AffineGroupQ where
  toFun b := translation (Multiplicative.toAdd b)
  map_one' := translation_zero
  map_mul' b b' := by rw [toAdd_mul, translation_add]

/-- The successor `ratCorr(1) − c|b|` already costs one square. -/
theorem one_le_negIndex_weilArchState {c : ℝ} (hc : 0 < c) : 1 ≤ negIndex (weilArchState c) := by
  obtain ⟨L, hL⟩ := exists_nat_gt (2 * |(splineCorr 0).re| / c)
  have hL0 : (0 : ℝ) ≤ L := by positivity
  have hk : ∀ p q : ℚ, (weilArchState c ∘ translationHomQ)
      ((Multiplicative.ofAdd p)⁻¹ * Multiplicative.ofAdd q) =
        splineCorr 0 - (c : ℂ) * ((|q - p| : ℚ) : ℂ) := fun p q => by
    rw [ofAdd_inv_mul_ofAdd]
    show weilArchState c (translation (q - p)) = _
    exact weilArchState_translation c _
  have hneg : hermQuad (gram (weilArchState c ∘ translationHomQ)
      ![Multiplicative.ofAdd 0, Multiplicative.ofAdd (L : ℚ)]) ![1, 1] < 0 := by
    rw [hermQuad_gram]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hk, sub_self,
      sub_zero, zero_sub, abs_zero, abs_neg, map_one, one_mul, mul_one]
    rw [abs_of_nonneg (by positivity : (0 : ℚ) ≤ L)]
    push_cast
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero]
    have hre : (splineCorr 0).re ≤ |(splineCorr 0).re| := le_abs_self _
    have : 2 * |(splineCorr 0).re| < c * L := by
      rw [div_lt_iff₀ hc] at hL; linarith
    nlinarith
  have h := card_le_negIndex_of_orthogonal_translates (J := Fin 1) hneg (fun _ => 1)
    fun j j' h => absurd (Subsingleton.elim j j') h
  simp only [Fintype.card_fin, Nat.cast_one] at h
  exact h.trans (negIndex_comp_le _ translationHomQ)

/-- If `K_ζ` has no negative squares, the archimedean Weil state has exactly one. -/
theorem negIndex_weilArchState_eq_one_of_zero {c : ℝ} (hc : 0 < c)
    (h0 : negIndex zetaKernel = 0) : negIndex (weilArchState c) = 1 :=
  le_antisymm (by simpa [h0] using negIndex_weilArchState_le hc) (one_le_negIndex_weilArchState hc)

/-- The archimedean Weil state has finite index exactly when `K_ζ` does. -/
theorem negIndex_weilArchState_lt_top_iff {c : ℝ} (hc : 0 < c) :
    negIndex (weilArchState c) < ⊤ ↔ negIndex zetaKernel < ⊤ := by
  constructor
  · exact fun h => (le_negIndex_weilArchState c).trans_lt h
  · intro h
    refine (negIndex_weilArchState_le hc).trans_lt ?_
    exact ENat.add_lt_top.mpr ⟨h, ENat.coe_lt_top 1⟩

end GaloisForLFunctions.AdelicKreinGeometry
