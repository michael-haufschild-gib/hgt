import GaloisForLFunctions.AdelicKreinGeometry.ThePontryaginExtensionsOfWeilsCorrelation
import GaloisForLFunctions.HeckeKreinToeplitz.FiniteIndexIsPositiveMinusFiniteRank
import GaloisForLFunctions.HeckeKreinToeplitz.BoundedIndexIsClosedUnderPointwiseLimits

/-!
# A mixed polynomial perturbation invisible on both affine axes

The Hermitian kernel `K(a,b) = i(1-a⁻²)b²` vanishes on translations and dilations, but has
exactly three negative squares. Three explicit feature squares complete it to a positive form;
a six-point Gram matrix supplies a negative three-dimensional subspace.

Adding `K` to the Haar state preserves both axis readings and its three negative squares.
Dilation conjugation amplifies `K` quadratically while the Haar contribution stays bounded.
The resulting mixed coefficients are unbounded on a fixed slope, excluding a decomposition
as a positive-definite affine kernel plus a kernel depending only on slope.
-/

open Complex Finset Matrix Filter Topology
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-- A quadratic mixed affine kernel with zero translation and dilation readings. -/
def mixedQuadraticKernel (g : AffineGroupQ) : ℂ :=
  I * (1 - (affSlope g : ℂ)⁻¹ ^ 2) * (affShift g : ℂ) ^ 2

/-- The perturbation vanishes on the translation subgroup. -/
theorem mixedQuadraticKernel_translation (b : ℚ) :
    mixedQuadraticKernel (translation b) = 0 := by
  simp only [mixedQuadraticKernel, affSlope_translation, Rat.cast_one, inv_one, one_pow,
    sub_self, mul_zero, zero_mul]

/-- The perturbation vanishes on the dilation subgroup. -/
theorem mixedQuadraticKernel_dilation (u : ℚˣ) :
    mixedQuadraticKernel (dilation u) = 0 := by
  simp only [mixedQuadraticKernel, affShift_dilation, Rat.cast_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero]

/-- Inversion changes the sign of the purely imaginary perturbation. -/
theorem isHermKernel_mixedQuadraticKernel : IsHermKernel mixedQuadraticKernel := by
  intro g
  have ha : (affSlope g : ℂ) ≠ 0 := by exact_mod_cast affSlope_ne_zero g
  simp only [mixedQuadraticKernel, affSlope_inv, affShift_inv, Rat.cast_inv, Rat.cast_div,
    Rat.cast_neg, inv_inv, map_mul, map_sub, map_one, map_pow, map_inv₀, map_ratCast,
    Complex.conj_I]
  field_simp
  ring

private theorem mixedQuadraticKernel_quotient (g h : AffineGroupQ) :
    mixedQuadraticKernel (g⁻¹ * h) =
      I * ((affSlope g : ℂ)⁻¹ ^ 2 - (affSlope h : ℂ)⁻¹ ^ 2) *
        ((affShift h : ℂ) - (affShift g : ℂ)) ^ 2 := by
  have ha : (affSlope g : ℂ) ≠ 0 := by exact_mod_cast affSlope_ne_zero g
  have hb : (affSlope h : ℂ) ≠ 0 := by exact_mod_cast affSlope_ne_zero h
  simp only [mixedQuadraticKernel, affSlope_mul, affSlope_inv, affShift_mul, affShift_inv,
    Rat.cast_mul, Rat.cast_inv, Rat.cast_add, Rat.cast_div, Rat.cast_neg]
  field_simp
  ring

private def mixedA (g : AffineGroupQ) : Fin 3 → ℂ :=
  ![(affSlope g : ℂ)⁻¹ ^ 2,
    (affSlope g : ℂ)⁻¹ ^ 2 * (affShift g : ℂ) ^ 2,
    -2 * (affSlope g : ℂ)⁻¹ ^ 2 * (affShift g : ℂ)]

private def mixedB (g : AffineGroupQ) : Fin 3 → ℂ :=
  ![(affShift g : ℂ) ^ 2, 1, (affShift g : ℂ)]

private def outerGram {ι : Type*} (z : ι → ℂ) : Matrix ι ι ℂ :=
  fun a b => conj (z a) * z b

private theorem hermQuad_outerGram {ι : Type*} [Fintype ι] (z c : ι → ℂ) :
    hermQuad (outerGram z) c = normSq (∑ a, c a * z a) := by
  have he : (normSq (∑ a, c a * z a) : ℂ) =
      ∑ a, ∑ b, conj (c a) * (conj (z a) * z b * c b) := by
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [map_sum, Finset.sum_mul_sum, map_mul]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  simp only [hermQuad, outerGram, dotProduct, mulVec, Pi.star_apply,
    Finset.mul_sum, Complex.star_def]
  rw [← he, Complex.ofReal_re]

private theorem hermQuad_sum_mixed {ι J : Type*} [Fintype ι] [Fintype J]
    (M : J → Matrix ι ι ℂ) (c : ι → ℂ) :
    hermQuad (∑ j, M j) c = ∑ j, hermQuad (M j) c := by
  simp only [hermQuad, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]

/-- Three added squares leave six positive feature squares. -/
private theorem mixedQuadraticKernel_completion {ι : Type*} [Fintype ι]
    (x : ι → AffineGroupQ) (c : ι → ℂ) :
    hermQuad (HeckeKreinToeplitz.gram mixedQuadraticKernel x) c +
      ∑ j, normSq (∑ a, c a * (mixedA (x a) j - I * mixedB (x a) j)) =
        ∑ j, (normSq (∑ a, c a * mixedA (x a) j) +
          normSq (∑ a, c a * mixedB (x a) j)) := by
  have hm : HeckeKreinToeplitz.gram mixedQuadraticKernel x +
      ∑ j, outerGram (fun a => mixedA (x a) j - I * mixedB (x a) j) =
        ∑ j, (outerGram (fun a => mixedA (x a) j) + outerGram (fun a => mixedB (x a) j)) := by
    ext a b
    simp only [Matrix.add_apply, Matrix.sum_apply, outerGram, HeckeKreinToeplitz.gram,
      mixedQuadraticKernel_quotient, mixedA, mixedB, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, map_sub, map_mul, map_pow, map_inv₀,
      map_ratCast, Complex.conj_I, map_one, map_neg, map_ofNat]
    simp only [Matrix.zero_apply, add_zero]
    ring_nf
    simp only [I_sq]
    ring
  have h := congrArg (fun M => hermQuad M c) hm
  simpa only [HeckeKreinToeplitz.hermQuad_add, hermQuad_sum_mixed, hermQuad_outerGram] using h

/-- The explicit completion bounds the negative index by three. -/
theorem negIndex_mixedQuadraticKernel_le_three : negIndex mixedQuadraticKernel ≤ 3 := by
  refine negIndex_le_of_rank (m := 3)
    (fun j g => mixedA g j - I * mixedB g j) fun n x c => ?_
  rw [mixedQuadraticKernel_completion]
  exact sum_nonneg fun j _ => add_nonneg (normSq_nonneg _) (normSq_nonneg _)

private def mixedTestPoints : Fin 3 ⊕ Fin 3 → AffineGroupQ :=
  Sum.elim (fun j => translation (j : ℚ))
    (fun j => translation (j : ℚ) * dilation (Units.mk0 2 two_ne_zero))

private def mixedNegativeMatrix : Matrix (Fin 3 ⊕ Fin 3) (Fin 3) ℂ :=
  Matrix.fromRows
    ((8 : ℂ)⁻¹ • !![-1, 4, 1; 4, -16, 4; 1, 4, -1])
    (I • (1 : Matrix (Fin 3) (Fin 3) ℂ))

/-- On two slopes and three translations, the displayed coefficient map is negative definite. -/
private theorem mixedNegativeMatrix_congruence :
    mixedNegativeMatrixᴴ * HeckeKreinToeplitz.gram mixedQuadraticKernel mixedTestPoints *
      mixedNegativeMatrix = Matrix.diagonal (fun _ : Fin 3 => (-3 / 2 : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [mixedNegativeMatrix, mixedTestPoints, HeckeKreinToeplitz.gram,
      mixedQuadraticKernel_quotient, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_succ, Matrix.conjTranspose_apply, Matrix.fromRows,
      affSlope_translation, affShift_translation, affSlope_mul, affShift_mul,
      affSlope_dilation, affShift_dilation, Matrix.diagonal_apply, Matrix.one_apply,
      Complex.star_def, map_mul, map_inv₀, map_neg, map_ofNat, map_one, map_zero,
      Complex.conj_I, I_sq] <;>
    ring_nf <;> norm_num [I_sq, Fin.ext_iff]

private theorem three_le_mixed_test_index :
    3 ≤ hermNegIndex (HeckeKreinToeplitz.gram mixedQuadraticKernel mixedTestPoints) := by
  have h := hermNegIndex_le_of_hermQuad_eq
    (Matrix.diagonal (fun _ : Fin 3 => (-3 / 2 : ℂ)))
    (HeckeKreinToeplitz.gram mixedQuadraticKernel mixedTestPoints)
    mixedNegativeMatrix.mulVecLin (fun c => by
      rw [Matrix.mulVecLin_apply, ← hermQuad_rect_conjugate, mixedNegativeMatrix_congruence])
  have hd : hermNegIndex (Matrix.diagonal (fun _ : Fin 3 => (-3 / 2 : ℂ))) = 3 := by
    convert negIndex_diagonal (fun _ : Fin 3 => (-3 / 2 : ℝ)) using 1 <;> norm_num
  rwa [hd] at h

/-- The mixed quadratic kernel has exactly three negative squares. -/
theorem negIndex_mixedQuadraticKernel : negIndex mixedQuadraticKernel = 3 := by
  refine le_antisymm negIndex_mixedQuadraticKernel_le_three ?_
  exact (Nat.cast_le.mpr three_le_mixed_test_index).trans
    (hermNegIndex_gram_le_negIndex mixedQuadraticKernel mixedTestPoints)

/-- The Haar state with a mixed quadratic perturbation. -/
def haarMixedQuadraticState (g : AffineGroupQ) : ℂ :=
  haarState g + mixedQuadraticKernel g

/-- The translation reading remains the Haar reading. -/
theorem haarMixedQuadraticState_translation (b : ℚ) :
    haarMixedQuadraticState (translation b) = haarState (translation b) := by
  rw [haarMixedQuadraticState, mixedQuadraticKernel_translation, add_zero]

/-- The mixed perturbation preserves the integer successor exactly. -/
theorem haarMixedQuadraticState_hasIntegerSuccessor : HasIntegerSuccessor haarMixedQuadraticState := by
  intro b
  rw [haarMixedQuadraticState_translation]
  exact haarState_hasIntegerSuccessor b

/-- The dilation reading remains the Haar reading. -/
theorem haarMixedQuadraticState_dilation (u : ℚˣ) :
    haarMixedQuadraticState (dilation u) = haarState (dilation u) := by
  rw [haarMixedQuadraticState, mixedQuadraticKernel_dilation, add_zero]

/-- The perturbed Haar state is Hermitian. -/
theorem isHermKernel_haarMixedQuadraticState : IsHermKernel haarMixedQuadraticState := by
  intro g
  simp only [haarMixedQuadraticState, IsPosDefOnGroup.map_inv isPosDefOnGroup_haarState,
    isHermKernel_mixedQuadraticKernel g, map_add, Complex.star_def]

/-- Adding the positive Haar state cannot increase the negative index. -/
theorem negIndex_haarMixedQuadraticState_le_three : negIndex haarMixedQuadraticState ≤ 3 :=
  (negIndex_add_posDef_le (k := mixedQuadraticKernel)
    (isPosDefKernel_iff_isPosDefOnGroup.mpr isPosDefOnGroup_haarState)).trans
      negIndex_mixedQuadraticKernel_le_three

/-- Dilation conjugation scales the mixed kernel by the square of the dilation. -/
private theorem mixedQuadraticKernel_conjugate (u : ℚˣ) (g : AffineGroupQ) :
    mixedQuadraticKernel (dilation u * g * (dilation u)⁻¹) =
      ((u : ℚ) : ℂ) ^ 2 * mixedQuadraticKernel g := by
  have hu : ((u : ℚ) : ℂ) ≠ 0 := by exact_mod_cast u.ne_zero
  have hg : (affSlope g : ℂ) ≠ 0 := by exact_mod_cast affSlope_ne_zero g
  simp only [mixedQuadraticKernel, affSlope_mul, affSlope_inv, affSlope_dilation,
    affShift_mul, affShift_inv, affShift_dilation, Rat.cast_mul, Rat.cast_add,
    Rat.cast_inv, Rat.cast_div, Rat.cast_zero, add_zero, neg_zero]
  field_simp
  ring

/-- Rescaled dilation conjugates retain all three negative directions after Haar addition. -/
theorem negIndex_haarMixedQuadraticState : negIndex haarMixedQuadraticState = 3 := by
  apply le_antisymm negIndex_haarMixedQuadraticState_le_three
  let u : ℕ → ℚˣ := fun N => Units.mk0 ((N : ℚ) + 1) (by positivity)
  let y : ℕ → Fin 3 ⊕ Fin 3 → AffineGroupQ := fun N a =>
    dilation (u N) * mixedTestPoints a * (dilation (u N))⁻¹
  let s : ℕ → ℝ := fun N => (((N : ℝ) + 1)⁻¹) ^ 2
  let P : ℕ → Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℂ := fun N =>
    (s N : ℂ) • HeckeKreinToeplitz.gram haarState (y N)
  let M : ℕ → Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℂ := fun N =>
    (s N : ℂ) • HeckeKreinToeplitz.gram haarMixedQuadraticState (y N)
  have hspos (N : ℕ) : 0 < s N := by dsimp only [s]; positivity
  have he (N : ℕ) : (s N : ℂ) * (((u N : ℚ) : ℂ) ^ 2) = 1 := by
    have h0 : (N : ℂ) + 1 ≠ 0 := by
      exact_mod_cast (show (N : ℝ) + 1 ≠ 0 by positivity)
    simp only [s, u, Units.val_mk0, Complex.ofReal_pow, Complex.ofReal_inv,
      Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one, Rat.cast_add,
      Rat.cast_natCast, Rat.cast_one]
    field_simp
  have hM (N : ℕ) : M N = HeckeKreinToeplitz.gram mixedQuadraticKernel mixedTestPoints + P N := by
    ext a b
    change (s N : ℂ) * (haarState ((y N a)⁻¹ * y N b) +
      mixedQuadraticKernel ((y N a)⁻¹ * y N b)) =
        mixedQuadraticKernel ((mixedTestPoints a)⁻¹ * mixedTestPoints b) +
          (s N : ℂ) * haarState ((y N a)⁻¹ * y N b)
    have hq : (y N a)⁻¹ * y N b = dilation (u N) *
        ((mixedTestPoints a)⁻¹ * mixedTestPoints b) * (dilation (u N))⁻¹ := by
      dsimp only [y]
      group
    rw [hq, mixedQuadraticKernel_conjugate, mul_add]
    rw [show (s N : ℂ) * (((u N : ℚ) : ℂ) ^ 2 *
        mixedQuadraticKernel ((mixedTestPoints a)⁻¹ * mixedTestPoints b)) =
          mixedQuadraticKernel ((mixedTestPoints a)⁻¹ * mixedTestPoints b) by
      rw [← mul_assoc, he, one_mul], add_comm]
  have hnorm (g : AffineGroupQ) : ‖haarState g‖ ≤ 1 := by
    simpa only [hasIntegerSuccessor_one haarState_hasIntegerSuccessor, Complex.one_re] using
      (isPosDefKernel_iff_isPosDefOnGroup.mpr isPosDefOnGroup_haarState).norm_le g
  have hP (N : ℕ) (a b : Fin 3 ⊕ Fin 3) : ‖P N a b‖ ≤ s N := by
    change ‖(s N : ℂ) * haarState ((y N a)⁻¹ * y N b)‖ ≤ s N
    rw [norm_mul, Complex.norm_of_nonneg (hspos N).le]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hnorm _) (hspos N).le
  have hs : Tendsto s atTop (𝓝 0) := by
    simpa only [s, one_div, zero_pow (by decide : 2 ≠ 0)] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
  have hPlim (a b : Fin 3 ⊕ Fin 3) : Tendsto (fun N => P N a b) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hs.eventually (gt_mem_nhds hε)] with N hN
    simpa only [dist_zero_right] using (hP N a b).trans_lt hN
  have hconv (a b : Fin 3 ⊕ Fin 3) : Tendsto (fun N => M N a b) atTop
      (𝓝 ((HeckeKreinToeplitz.gram mixedQuadraticKernel mixedTestPoints) a b)) := by
    simp only [hM, Matrix.add_apply]
    simpa only [add_zero] using tendsto_const_nhds.add (hPlim a b)
  obtain ⟨N, hN⟩ := (eventually_le_hermNegIndex
    (gram_isHermitian isHermKernel_mixedQuadraticKernel mixedTestPoints) hconv).exists
  have hMN : hermNegIndex (M N) =
      hermNegIndex (HeckeKreinToeplitz.gram haarMixedQuadraticState (y N)) :=
    ArithmeticCastelnuovoSeveri.hermNegIndex_ofReal_smul (hspos N) _
  rw [hMN] at hN
  exact (Nat.cast_le.mpr (three_le_mixed_test_index.trans hN)).trans
    (hermNegIndex_gram_le_negIndex haarMixedQuadraticState (y N))

private theorem haarMixedQuadraticState_im (b : ℚ) :
    (haarMixedQuadraticState (translation b * dilation (Units.mk0 2 two_ne_zero))).im =
      (3 / 4 : ℝ) * (b : ℝ) ^ 2 := by
  norm_num [haarMixedQuadraticState, haarState, mixedQuadraticKernel, affSlope_mul,
    affShift_mul, affSlope_translation, affShift_translation, affSlope_dilation,
    affShift_dilation, Complex.mul_re, Complex.mul_im, pow_two]

/-- At slope two the imaginary part grows quadratically in the translation coordinate. -/
theorem haarMixedQuadraticState_unbounded_on_fixed_slope (C : ℝ) :
    ∃ b : ℚ, C < ‖haarMixedQuadraticState
      (translation b * dilation (Units.mk0 2 two_ne_zero))‖ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max C 2)
  have hNC : C < (N : ℝ) := (le_max_left _ _).trans_lt hN
  have hN2 : (2 : ℝ) < N := (le_max_right _ _).trans_lt hN
  refine ⟨N, ?_⟩
  have h := Complex.im_le_norm (haarMixedQuadraticState
    (translation (N : ℚ) * dilation (Units.mk0 2 two_ne_zero)))
  rw [haarMixedQuadraticState_im, Rat.cast_natCast] at h
  nlinarith only [hNC, hN2, h]

/-- This finite-index Haar carrier is not a positive affine kernel plus a slope kernel. -/
theorem haarMixedQuadraticState_not_positive_add_slope :
    ¬ ∃ (p : AffineGroupQ → ℂ) (ψ : ℚˣ → ℂ), IsPosDefKernel p ∧
      ∀ g, haarMixedQuadraticState g = p g + ψ (slopeUnit g) := by
  rintro ⟨p, ψ, hp, he⟩
  obtain ⟨b, hb⟩ := haarMixedQuadraticState_unbounded_on_fixed_slope
    ((p 1).re + ‖ψ (Units.mk0 2 two_ne_zero)‖)
  let g := translation b * dilation (Units.mk0 2 two_ne_zero)
  have hs : slopeUnit g = Units.mk0 2 two_ne_zero := by
    apply Units.ext
    simp only [g, slopeUnit, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0,
      affSlope_mul, affSlope_translation, affSlope_dilation, one_mul]
  have h : ‖haarMixedQuadraticState g‖ ≤ (p 1).re + ‖ψ (Units.mk0 2 two_ne_zero)‖ := by
    rw [he, hs]
    exact (norm_add_le _ _).trans (add_le_add (hp.norm_le g) le_rfl)
  exact (not_lt_of_ge h) hb

#print axioms haarMixedQuadraticState_hasIntegerSuccessor
#print axioms haarMixedQuadraticState_dilation
#print axioms negIndex_haarMixedQuadraticState
#print axioms haarMixedQuadraticState_not_positive_add_slope
#print axioms negIndex_mixedQuadraticKernel
#print axioms isHermKernel_mixedQuadraticKernel
#print axioms negIndex_mixedQuadraticKernel_le_three
end GaloisForLFunctions.AdelicKreinGeometry
