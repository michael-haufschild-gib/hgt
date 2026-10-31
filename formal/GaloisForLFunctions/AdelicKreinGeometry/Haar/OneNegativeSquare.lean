import GaloisForLFunctions.AdelicKreinGeometry.HeckeSupportedStatesHaveIndexZeroOrInfinity
import GaloisForLFunctions.ArithmeticPositiveDuality.AMautnerPhenomenonForTheAffineGroupOfQ

/-!
# A Haar successor with exactly one negative square

Subtracting four times the squared logarithmic slope from the Haar state preserves its
translation reading. One outer product completes every Gram matrix to a sum of positive
forms, while dilation by two rules out index zero. The resulting state leaves Hecke support
and has no dilation reading continuous at one.
-/

open Complex Finset Matrix
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-- The logarithm of the absolute slope, normalized at dilation by two. -/
def affineLogTwo (g : AffineGroupQ) : ℝ :=
  Real.log |(affSlope g : ℝ)| / Real.log 2

lemma affineLogTwo_mul (g h : AffineGroupQ) :
    affineLogTwo (g * h) = affineLogTwo g + affineLogTwo h := by
  have hg : (affSlope g : ℝ) ≠ 0 := by exact_mod_cast affSlope_ne_zero g
  have hh : (affSlope h : ℝ) ≠ 0 := by exact_mod_cast affSlope_ne_zero h
  simp only [affineLogTwo, affSlope_mul, Rat.cast_mul, abs_mul,
    Real.log_mul (abs_ne_zero.mpr hg) (abs_ne_zero.mpr hh), add_div]

lemma affineLogTwo_inv (g : AffineGroupQ) : affineLogTwo g⁻¹ = -affineLogTwo g := by
  simp only [affineLogTwo, affSlope_inv, Rat.cast_inv, abs_inv, Real.log_inv, neg_div]

lemma affineLogTwo_translation (b : ℚ) : affineLogTwo (translation b) = 0 := by
  simp only [affineLogTwo, affSlope_translation, Rat.cast_one, abs_one, Real.log_one, zero_div]

/-- The Haar state minus four times the squared logarithmic slope. -/
def haarOneNegativeSquare (g : AffineGroupQ) : ℂ :=
  haarState g - (4 * affineLogTwo g ^ 2 : ℝ)

/-- The logarithmic perturbation vanishes on every translation. -/
theorem haarOneNegativeSquare_hasIntegerSuccessor : HasIntegerSuccessor haarOneNegativeSquare := by
  intro b
  simpa only [haarOneNegativeSquare, affineLogTwo_translation, zero_pow (by decide : 2 ≠ 0),
    mul_zero, Complex.ofReal_zero, sub_zero] using haarState_hasIntegerSuccessor b

lemma haarOneNegativeSquare_one : haarOneNegativeSquare 1 = 1 :=
  hasIntegerSuccessor_one haarOneNegativeSquare_hasIntegerSuccessor

lemma isHermKernel_haarOneNegativeSquare : IsHermKernel haarOneNegativeSquare := by
  intro g
  simp only [haarOneNegativeSquare, affineLogTwo_inv, neg_sq,
    IsPosDefOnGroup.map_inv isPosDefOnGroup_haarState, map_sub, Complex.conj_ofReal,
    Complex.star_def]

private def rankOneGram {ι : Type*} (z : ι → ℂ) : Matrix ι ι ℂ :=
  fun a b => conj (z a) * z b

private lemma hermQuad_outer {ι : Type*} [Fintype ι] (z c : ι → ℂ) :
    hermQuad (rankOneGram z) c = normSq (∑ a, c a * z a) := by
  have he : (normSq (∑ a, c a * z a) : ℂ) =
      ∑ a, ∑ b, conj (c a) * (conj (z a) * z b * c b) := by
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [map_sum, Finset.sum_mul_sum, map_mul]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  simp only [hermQuad, rankOneGram, dotProduct, mulVec, Pi.star_apply,
    Finset.mul_sum, Complex.star_def]
  rw [← he, Complex.ofReal_re]

/-- One square completes the form to the Haar form and four explicit feature squares. -/
theorem haarOneNegativeSquare_completion {n : ℕ} (x : Fin n → AffineGroupQ) (c : Fin n → ℂ) :
    hermQuad (gram haarOneNegativeSquare x) c +
        normSq (∑ a, c a * (2 * (1 + affineLogTwo (x a) ^ 2) : ℝ)) =
      hermQuad (gram haarState x) c + normSq (∑ a, c a * 2) +
        normSq (∑ a, c a * (2 * affineLogTwo (x a) : ℝ)) +
        normSq (∑ a, c a * (2 * affineLogTwo (x a) : ℝ)) +
        normSq (∑ a, c a * (2 * affineLogTwo (x a) ^ 2 : ℝ)) := by
  let F : Fin n → ℂ := fun a => (2 * (1 + affineLogTwo (x a) ^ 2) : ℝ)
  let A : Fin n → ℂ := fun _ => 2
  let B : Fin n → ℂ := fun a => (2 * affineLogTwo (x a) : ℝ)
  let C : Fin n → ℂ := fun a => (2 * affineLogTwo (x a) ^ 2 : ℝ)
  -- The completion is `-4(y-x)² + 4(1+x²)(1+y²) = 4 + 8xy + 4x²y²`.
  have he : gram haarOneNegativeSquare x + rankOneGram F =
      gram haarState x + rankOneGram A + rankOneGram B + rankOneGram B + rankOneGram C := by
    ext a b
    simp only [Matrix.add_apply, rankOneGram, HeckeKreinToeplitz.gram,
      haarOneNegativeSquare, affineLogTwo_mul,
      affineLogTwo_inv, F, A, B, C, Complex.conj_ofReal, map_ofNat]
    push_cast
    ring
  have h := congrArg (fun M => hermQuad M c) he
  simpa only [HeckeKreinToeplitz.hermQuad_add, hermQuad_outer, F, A, B, C] using h

/-- The explicit completion costs at most one negative square. -/
theorem negIndex_haarOneNegativeSquare_le_one : negIndex haarOneNegativeSquare ≤ 1 := by
  refine negIndex_le_of_rank (m := 1)
    (fun _ g => (2 * (1 + affineLogTwo g ^ 2) : ℝ)) fun n x c => ?_
  simp only [Fin.sum_univ_one]
  rw [haarOneNegativeSquare_completion]
  have h := (isPosDefKernel_iff_isPosDefOnGroup.mpr isPosDefOnGroup_haarState).2 n x c
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg h (normSq_nonneg _))
    (normSq_nonneg _)) (normSq_nonneg _)) (normSq_nonneg _)

/-- Dilation by two violates the normalized positive-definite bound, so the index is one. -/
theorem negIndex_haarOneNegativeSquare : negIndex haarOneNegativeSquare = 1 := by
  have hle := negIndex_haarOneNegativeSquare_le_one
  have hne : negIndex haarOneNegativeSquare ≠ 0 := by
    intro hz
    let g := dilation (Units.mk0 (2 : ℚ) two_ne_zero)
    have hlog : affineLogTwo g = 1 := by
      have h2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
      simp only [g, affineLogTwo, affSlope_dilation, Units.val_mk0, Rat.cast_ofNat,
        abs_of_pos (by norm_num : (0 : ℝ) < 2), div_self h2]
    have hH := (isPosDefKernel_iff_isPosDefOnGroup.mpr isPosDefOnGroup_haarState).norm_le g
    rw [hasIntegerSuccessor_one haarState_hasIntegerSuccessor, Complex.one_re] at hH
    have hP := (isPosDefKernel_iff isHermKernel_haarOneNegativeSquare).mpr hz
    have hb := hP.norm_le g
    rw [haarOneNegativeSquare_one, Complex.one_re] at hb
    have hre : (haarOneNegativeSquare g).re = (haarState g).re - 4 := by
      simp only [haarOneNegativeSquare, hlog, one_pow, mul_one, Complex.sub_re, Complex.ofReal_re]
    have hreal := Complex.re_le_norm (haarState g)
    have hlower := Complex.re_le_norm (-haarOneNegativeSquare g)
    simp only [Complex.neg_re, norm_neg] at hlower
    rw [hre] at hlower
    linarith only [hH, hb, hreal, hlower]
  exact le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne)

/-- A finite nonzero index forces the state outside Hecke support. -/
theorem not_isHeckeSupported_haarOneNegativeSquare : ¬ IsHeckeSupported haarOneNegativeSquare := by
  intro hs
  have h := negIndex_eq_zero_or_top_of_isHeckeSupported isHermKernel_haarOneNegativeSquare hs
  rw [negIndex_haarOneNegativeSquare] at h
  norm_num at h

/-- A continuous dilation reading would also make the Haar reading continuous, contradicting
positive Mautner rigidity for its nonconstant integer successor. -/
theorem haarOneNegativeSquare_dilation_discontinuous :
    ¬ ∃ f : ℝ → ℂ, ContinuousAt f 1 ∧
      ∀ u : ℚˣ, 0 < (u : ℚ) → haarOneNegativeSquare (dilation u) = f (u : ℚ) := by
  rintro ⟨f, hf, hread⟩
  let F : ℝ → ℂ := fun r => f r + (4 * (Real.log |r| / Real.log 2) ^ 2 : ℝ)
  have hF : ContinuousAt F 1 := by
    apply hf.add
    fun_prop (disch := norm_num)
  have hmatch : ∀ u : ℚˣ, 0 < (u : ℚ) → haarState (dilation u) = F (u : ℚ) := by
    intro u hu
    dsimp only [F]
    rw [← hread u hu, haarOneNegativeSquare, affineLogTwo, affSlope_dilation]
    ring
  have he := translation_eq_of_continuousAt_dilation isPosDefOnGroup_haarState
    (hasIntegerSuccessor_int haarState_hasIntegerSuccessor) hF hmatch (1 / 2)
  rw [haarState_hasIntegerSuccessor, hasIntegerSuccessor_one haarState_hasIntegerSuccessor] at he
  norm_num at he

#print axioms haarOneNegativeSquare_hasIntegerSuccessor
#print axioms haarOneNegativeSquare_completion
#print axioms negIndex_haarOneNegativeSquare
#print axioms not_isHeckeSupported_haarOneNegativeSquare
#print axioms haarOneNegativeSquare_dilation_discontinuous
end GaloisForLFunctions.AdelicKreinGeometry
