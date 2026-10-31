import GaloisForLFunctions.AdelicKreinGeometry.WeilsArchimedeanStateCountsTheZeros

/-!
# The gluing square is sharp, and the glue is blind to the pole

Gluing dilation data `K` on `ℚ_{>0}` to the archimedean successor, `K(|a|) − c|a|^{−1/2}|b|`, costs at
most one square: `κ(K) ≤ κ(glued) ≤ κ(K) + 1` (`negIndex_archGlue_eq_or`). Both values occur.

* **Weil's correlation pays the square**: `κ = κ(K_ζ) + 1` (`negIndex_weilArchState_eq_add_one`).
* **The pole pair does not** (`negIndex_archGlue_polePair`): glued to `−c|b|`, the pole pair
  `u^{1/2} + u^{−1/2}` is the pole–successor state, of index `1 = κ(polePair)`. Its form at slopes
  `u_i` is `2 Re(ℓ̄m)` with `ℓ = Σ w_i u_i^{−1/2}` and `m = Σ w_i u_i^{1/2}`, which vanishes on the
  boost hyperplane `ℓ = 0` (`hermQuad_gram_polePair_of_boostMass`).

Hence the glued index is **blind to the pole terms**: adding the pole pair at any real strength
leaves `κ^{(½)}` and the glued index unchanged (`boostPolarIndex_add_polePair`,
`negIndex_archGlue_add_polePair`). For Weil's zero correlation, `κ(K_ζ + t·polePair glued) =
κ(K_ζ) + 1` for every `t ∈ ℝ` (`negIndex_archGlue_ratCorr_add_polePair`): the count of the zeros
right of the line does not depend on how the poles are weighted.
-/

open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

/-! ### The gluing square is at most one -/

theorem archGlue_dilation (K : posUnits → ℂ) (c : ℝ) (u : posUnits) :
    archGlue K c (dilation u) = K u := by
  have h0 : shiftOf (dilation (u : ℚˣ)) = 0 := affShift_dilation _
  simp [archGlue, slopeAbs_dilation, conformalInduction, h0, negAbsRat, absRat]

/-- The dilation reading of the glued state is `K`, so gluing never loses a square. -/
theorem negIndex_le_negIndex_archGlue (K : posUnits → ℂ) (c : ℝ) :
    negIndex K ≤ negIndex (archGlue K c) := by
  have e : archGlue K c ∘ (dilation.comp posUnits.subtype) = K :=
    funext fun u => archGlue_dilation K c u
  simpa [e] using negIndex_comp_le (archGlue K c) (dilation.comp posUnits.subtype)

/-- **The gluing square is at most one**: `κ(K) ≤ κ(K(|a|) − c|a|^{−1/2}|b|) ≤ κ(K) + 1`. -/
theorem negIndex_archGlue_eq_or (K : posUnits → ℂ) {c : ℝ} (hc : 0 ≤ c) :
    negIndex (archGlue K c) = negIndex K ∨ negIndex (archGlue K c) = negIndex K + 1 := by
  have h1 := negIndex_le_negIndex_archGlue K c
  have h2 := (negIndex_archGlue_le K hc).trans (add_le_add (boostPolarIndex_le_negIndex K) le_rfl)
  generalize negIndex (archGlue K c) = x at h1 h2 ⊢
  generalize negIndex K = y at h1 h2 ⊢
  induction y using ENat.recTopCoe with
  | top => exact Or.inl (top_le_iff.mp h1)
  | coe m =>
    induction x using ENat.recTopCoe with
    | top => exact absurd (top_le_iff.mp h2) (by exact_mod_cast ENat.coe_ne_top (m + 1))
    | coe n =>
      have h1' : m ≤ n := by exact_mod_cast h1
      have h2' : n ≤ m + 1 := by exact_mod_cast h2
      rcases (show n = m ∨ n = m + 1 by omega) with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rw [h]; push_cast; rfl)

/-! ### The pole pair -/

/-- The pole pair `u^{1/2} + u^{−1/2}` on `ℚ_{>0}`. -/
def polePair (u : posUnits) : ℂ :=
  (((((u : ℚˣ) : ℚ) : ℝ) ^ (1 / 2 : ℝ) + ((((u : ℚˣ) : ℚ) : ℝ) ^ (1 / 2 : ℝ))⁻¹ : ℝ) : ℂ)

/-- Glued to the archimedean successor, the pole pair is the pole–successor state. -/
theorem archGlue_polePair (c : ℝ) :
    archGlue polePair c = poleSuccessor Rat.AbsoluteValue.real 1 fun m => (c : ℂ) * negAbsRat m := by
  funext g
  simp only [archGlue, poleSuccessor, polePair, slopePow_real_eq]

theorem polePair_inv (u : posUnits) : polePair u⁻¹ = polePair u := by
  simp only [polePair, InvMemClass.coe_inv, Units.val_inv_eq_inv_val, Rat.cast_inv]
  rw [Real.inv_rpow (posUnits_val_pos u).le, inv_inv, add_comm]

theorem isHermKernel_polePair : IsHermKernel polePair := fun u => by
  rw [polePair_inv, polePair, Complex.conj_ofReal]

/-- The form of the pole pair is `2 Re(ℓ̄m)`; it vanishes on the boost hyperplane `ℓ = 0`. -/
theorem hermQuad_gram_polePair_of_boostMass {n : ℕ} (u : Fin n → posUnits) {w : Fin n → ℂ}
    (hw : boostMassU u w = 0) : hermQuad (gram polePair u) w = 0 := by
  set D : Fin n → AffineGroupQ := fun a => dilation (u a : ℚˣ)
  have hD : (fun a => slopeAbs (D a)) = u := funext fun a => slopeAbs_dilation (u a)
  have e : gram polePair u = gram (fun x => ((slopePow Rat.AbsoluteValue.real 1 x +
      (slopePow Rat.AbsoluteValue.real 1 x)⁻¹ : ℝ) : ℂ)) D := by
    rw [← hD, ← gram_comp_slopeAbs]
    simp only [polePair, slopePow_real_eq]
  have hmass : ∑ a, boostWeights Rat.AbsoluteValue.real 1 D w a = 0 := by
    rw [sum_boostWeights_eq, hD]; exact hw
  rw [e, hermQuad_gram_boostPair, hmass]
  simp

private def four : posUnits := ⟨Units.mk0 4 (by norm_num), show (0 : ℚ) < 4 by norm_num⟩

private theorem polePair_four : polePair four = ((5 / 2 : ℝ) : ℂ) := by
  have h : (((four : ℚˣ) : ℚ) : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by
    rw [Real.rpow_two]; norm_num [four]
  rw [polePair, h, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- The pole pair has one negative square. -/
theorem negIndex_polePair : negIndex polePair = 1 := by
  refine le_antisymm ?_ ?_
  · have h := negIndex_le_negIndex_archGlue polePair 1
    rwa [archGlue_polePair, negIndex_poleSuccessorState zero_le_one] at h
  · -- slopes `1, 4` with weights `1, −1`: `2 + 2 − 5/2 − 5/2 < 0`
    have hneg : hermQuad (gram polePair ![1, four]) ![1, -1] < 0 := by
      rw [hermQuad_gram]
      simp [Fin.sum_univ_two, polePair_inv, polePair_four, polePair]
      norm_num
    have h1 := one_le_negIndexOn (V := ⊤) Submodule.mem_top hneg
    exact le_trans (by exact_mod_cast h1.trans (negIndexOn_le_hermNegIndex _ ⊤))
      (hermNegIndex_gram_le_negIndex polePair _)

/-- **The pole pair keeps its square when glued**: `κ(polePair glued) = κ(polePair) = 1`. -/
theorem negIndex_archGlue_polePair {c : ℝ} (hc : 0 ≤ c) :
    negIndex (archGlue polePair c) = negIndex polePair := by
  rw [archGlue_polePair, negIndex_poleSuccessorState hc, negIndex_polePair]

/-! ### The glue is blind to the pole -/

/-- **Pole blindness of the boost-polar index**: `κ^{(½)}(K + t·polePair) = κ^{(½)}(K)`. -/
theorem boostPolarIndex_add_polePair (K : posUnits → ℂ) (t : ℝ) :
    boostPolarIndex (fun u => K u + t * polePair u) = boostPolarIndex K := by
  have key : ∀ {n : ℕ} (u : Fin n → posUnits), ∀ w ∈ LinearMap.ker (boostMassU u),
      hermQuad (gram (fun v => K v + t * polePair v) u) w = hermQuad (gram K u) w :=
    fun u w hw => by
      have e : gram (fun v => (t : ℂ) * polePair v) u = (t : ℂ) • gram polePair u := by
        ext a b; simp [gram]
      rw [hermQuad_gram_add, e, hermQuad_smul,
        hermQuad_gram_polePair_of_boostMass u (LinearMap.mem_ker.mp hw), mul_zero, add_zero]
  simp only [boostPolarIndex]
  refine iSup_congr fun n => iSup_congr fun u => ?_
  exact congrArg _ (le_antisymm (negIndexOn_le_of_hermQuad_le fun w hw => (key u w hw).ge)
    (negIndexOn_le_of_hermQuad_le fun w hw => (key u w hw).le))

theorem isHermKernel_add_polePair {K : posUnits → ℂ} (hK : IsHermKernel K) (t : ℝ) :
    IsHermKernel fun u => K u + t * polePair u := fun u => by
  rw [hK u, isHermKernel_polePair u, map_add, map_mul, Complex.conj_ofReal]

/-- **The glued index is blind to the pole terms.** -/
theorem negIndex_archGlue_add_polePair {K : posUnits → ℂ} (hK : IsHermKernel K) (t : ℝ) {c : ℝ}
    (hc : 0 < c) :
    negIndex (archGlue (fun u => K u + t * polePair u) c) = negIndex (archGlue K c) := by
  rw [negIndex_archGlue_eq (isHermKernel_add_polePair hK t) hc, negIndex_archGlue_eq hK hc,
    boostPolarIndex_add_polePair]

/-- Weil's zero correlation with the pole pair at any strength, glued at `∞`, still counts the zeros:
`κ = κ(K_ζ) + 1`. -/
theorem negIndex_archGlue_ratCorr_add_polePair (t : ℝ) {c : ℝ} (hc : 0 < c) :
    negIndex (archGlue (fun u => ratCorr u + t * polePair u) c) = negIndex zetaKernel + 1 := by
  rw [negIndex_archGlue_add_polePair isHermKernel_ratCorr t hc, ← weilArchState_eq_archGlue,
    negIndex_weilArchState_eq_add_one hc]

end GaloisForLFunctions.AdelicKreinGeometry
