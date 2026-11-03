import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspEvenFourFixedGlobal
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspEvenCompensationCoefficient
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspAllRankNativeTail

/-!
# Two-entry repair of the fifth even theta source

The fourth native even block is indefinite at the origin, so a correction
confined to the new diagonal cannot repair the fifth block. Retaining its
fixed zero-flux correction leaves one scalar Schur coordinate. A coefficient
selected from that coordinate repairs the origin and a neighborhood of it.
Gaussian balancing preserves the positive tail. The corresponding weighted
flux derivatives integrate to zero in every corrected entry.
-/

noncomputable section
open Matrix Filter Topology MeasureTheory Set
open RHTower RHTower.ThetaCuspGaussianLimit
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ThetaCuspSections

/-- Native fifth even block with independent corrections on its last two diagonals. -/
def evenFiveRepair (C D x : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  nativeShiftedMatrix 5 0 x + diagonal (fun i : Fin 5 =>
    if i.val = 3 then C * thetaCuspCenterCompensationSource x
    else if i.val = 4 then D * thetaCuspCenterCompensationSource x else 0)

private def head (x : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  thetaCuspNativeEvenFourCompensated 1000000000000 x

private def border (x : ℝ) : Matrix (Fin 4) (Fin 1) ℝ :=
  fun (i : Fin 4) (_ : Fin 1) =>
    (-1 : ℝ) ^ (i.val + 4) * thetaCuspNativeReflectionJet (2 * (i.val + 4)) x

/-- The fifth coordinate after retaining the fixed repair of the fourth block. -/
def evenFiveSchur (x : ℝ) : ℝ :=
  thetaCuspNativeReflectionJet 16 x - ((border x)ᴴ * (head x)⁻¹ * border x) 0 0

/-- An aperture-independent coefficient selected from the actual source at zero. -/
def evenFiveRepairCoefficient : ℝ :=
  (|evenFiveSchur 0| + thetaCuspFullSource 0 ^ 2) / thetaCuspFullSource 0 ^ 2

private theorem repair_hermitian (C D x : ℝ) : (evenFiveRepair C D x).IsHermitian := by
  apply Matrix.IsHermitian.add
  · rw [Matrix.IsHermitian]
    ext i j
    simp [nativeShiftedMatrix, add_comm]
  · exact Matrix.isHermitian_diagonal _

private theorem repair_head (C D x : ℝ) :
    (evenFiveRepair C D x).submatrix Fin.castSucc Fin.castSucc =
      thetaCuspNativeEvenFourCompensated C x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [evenFiveRepair, nativeShiftedMatrix, thetaCuspNativeEvenFourCompensated,
      Matrix.diagonal]

/-- The negative fourth native determinant obstructs every correction confined
 to the new fifth diagonal. -/
theorem evenFiveRepair_top_only_not_posSemidef (D : ℝ) :
    ¬ (evenFiveRepair 0 D 0).PosSemidef := by
  intro h
  have hh := h.submatrix Fin.castSucc
  rw [repair_head] at hh
  exact (not_lt_of_ge hh.det_nonneg) thetaCuspNativeEvenFourDet_zero_neg

/-- A positive fifth Schur coordinate completes the already repaired fourth block. -/
theorem evenFiveRepair_posDef_of_schur {D x : ℝ} (hx : 0 ≤ x)
    (hs : 0 < evenFiveSchur x + D * thetaCuspCenterCompensationSource x) :
    (evenFiveRepair 1000000000000 D x).PosDef := by
  let A : Matrix (Fin 4) (Fin 4) ℝ := head x
  let B : Matrix (Fin 4) (Fin 1) ℝ := border x
  let T : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ =>
    thetaCuspNativeReflectionJet 16 x + D * thetaCuspCenterCompensationSource x
  let e : Fin 4 ⊕ Fin 1 ≃ Fin 5 := finSumFinEquiv
  let M : Matrix (Fin 4 ⊕ Fin 1) (Fin 4 ⊕ Fin 1) ℝ :=
    (evenFiveRepair 1000000000000 D x).submatrix e e
  have hA : A.PosDef := thetaCuspNativeEvenFourFixed_posDef hx
  letI : Invertible A := hA.isUnit.invertible
  have hblock : M = fromBlocks A B Bᴴ T := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · exact congrFun (congrFun (repair_head 1000000000000 D x) i) j
    · fin_cases i <;> fin_cases j <;>
        norm_num [M, e, evenFiveRepair, nativeShiftedMatrix, border, B, diagonal]
    · fin_cases i <;> fin_cases j <;>
        norm_num [M, e, evenFiveRepair, nativeShiftedMatrix, border, B, diagonal]
    · fin_cases i <;> fin_cases j <;>
        norm_num [M, e, evenFiveRepair, nativeShiftedMatrix, T, diagonal]
  let S : Matrix (Fin 1) (Fin 1) ℝ := T - Bᴴ * A⁻¹ * B
  have hS : S.PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · rw [Matrix.IsHermitian]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · intro v
      have hval : S 0 0 = evenFiveSchur x + D * thetaCuspCenterCompensationSource x := by
        dsimp only [S, T, A, B, Matrix.sub_apply, evenFiveSchur]
        ring
      simp only [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_one, hval]
      nlinarith only [mul_nonneg hs.le (sq_nonneg (v 0))]
  have hM : M.PosSemidef := by
    rw [hblock]
    exact (Matrix.PosDef.fromBlocks₁₁ B T hA).mpr hS
  have hdet : M.det ≠ 0 := by
    rw [hblock, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv, Matrix.det_fin_one]
    apply mul_ne_zero hA.det_pos.ne'
    have he : (T - Bᴴ * A⁻¹ * B) 0 0 =
        evenFiveSchur x + D * thetaCuspCenterCompensationSource x := by
      dsimp only [T, A, B, Matrix.sub_apply, evenFiveSchur]
      ring
    rw [he]
    exact hs.ne'
  have hfull := (hM.posDef_iff_det_ne_zero.mpr hdet).submatrix e.symm.injective
  convert hfull using 1
  ext i j
  simp [M]

/-- The actual source selects a strictly positive repair coefficient. -/
theorem evenFiveRepairCoefficient_pos : 0 < evenFiveRepairCoefficient := by
  unfold evenFiveRepairCoefficient
  have hp := sq_pos_of_pos (thetaCuspFullSource_pos_all 0)
  exact div_pos (add_pos_of_nonneg_of_pos (abs_nonneg _) hp) hp

/-- Both repaired diagonal entries are sufficient at the literal theta origin. -/
theorem evenFiveRepair_zero_posDef :
    (evenFiveRepair 1000000000000 evenFiveRepairCoefficient 0).PosDef := by
  apply evenFiveRepair_posDef_of_schur le_rfl
  have hp := sq_pos_of_pos (thetaCuspFullSource_pos_all 0)
  have he : evenFiveRepairCoefficient * thetaCuspCenterCompensationSource 0 =
      3 * |evenFiveSchur 0| + 3 * thetaCuspFullSource 0 ^ 2 := by
    unfold evenFiveRepairCoefficient thetaCuspCenterCompensationSource
    simp only [mul_zero, zero_mul, add_zero]
    field_simp [(thetaCuspFullSource_pos_all 0).ne']
  rw [he]
  linarith only [neg_le_abs (evenFiveSchur 0), abs_nonneg (evenFiveSchur 0), hp]

private theorem repair_continuous (C D : ℝ) : Continuous (evenFiveRepair C D) := by
  have hΦ : Continuous thetaCuspFullSource := thetaCuspSchwartzReal.continuous
  have hd : Continuous (deriv thetaCuspFullSource) :=
    (SchwartzMap.derivCLM ℝ ℝ thetaCuspSchwartzReal).continuous
  have hj := continuous_thetaCuspNativeReflectionJet
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold evenFiveRepair nativeShiftedMatrix thetaCuspCenterCompensationSource
  simp only [Matrix.add_apply, Matrix.diagonal_apply]
  split_ifs <;> fun_prop

/-- The repaired fifth even source is strict on a nontrivial interval at zero. -/
theorem evenFiveRepair_posDef_near_zero :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x| < δ →
      (evenFiveRepair 1000000000000 evenFiveRepairCoefficient x).PosDef := by
  have ht (i j : Fin 5) : Tendsto
      (fun x => evenFiveRepair 1000000000000 evenFiveRepairCoefficient x i j)
      (𝓝 0) (𝓝 (evenFiveRepair 1000000000000 evenFiveRepairCoefficient 0 i j)) := by
    have hc := repair_continuous 1000000000000 evenFiveRepairCoefficient
    exact ((continuous_apply j).comp ((continuous_apply i).comp hc)).continuousAt.tendsto
  have hp := posDef_eventually_of_tendsto evenFiveRepair_zero_posDef
    (Filter.Eventually.of_forall (repair_hermitian 1000000000000 evenFiveRepairCoefficient)) ht
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp hp
  exact ⟨δ, hδ, fun x hx => hb (by simpa [Real.dist_eq] using hx)⟩

private def gaussianFive : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j : Fin 5 => gaussianMoment (i.val + j.val)

private theorem gaussianFive_posDef : gaussianFive.PosDef := by
  let A : Matrix (Fin 5) (Fin 5) ℝ :=
    _root_.HTGeometry.momentHankelMatrix (gammaShapeMoment (1/2)) 5
  let D : Matrix (Fin 5) (Fin 5) ℝ := diagonal (fun i : Fin 5 => (16 : ℝ)^i.val)
  have hA : A.PosDef := gammaShapeMoment_momentHankelMatrix_posDef (by norm_num) 5
  have hD : Function.Injective D.mulVec := by
    intro v w h
    funext i
    have hi := congrFun h i
    simp only [D, Matrix.mulVec_diagonal] at hi
    exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (16 : ℝ) ≠ 0)) hi
  have he : gaussianFive = Dᴴ * A * D := by
    ext i j
    simp only [gaussianFive, gaussianMoment, D, A, diagonal_conjTranspose,
      star_trivial, diagonal_mul, mul_diagonal, _root_.HTGeometry.momentHankelMatrix,
      pow_add]
    ring
  rw [he]
  exact hA.conjTranspose_mul_mul_same hD

private def balancedRepair (C D x : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  (fun i j : Fin 5 => thetaCuspNativeScaledEvenJet (i.val + j.val) x) +
    diagonal (fun i : Fin 5 =>
      (if i.val = 3 then C * thetaCuspCenterCompensationSource x
      else if i.val = 4 then D * thetaCuspCenterCompensationSource x else 0) /
        (thetaCuspSourceTerm x 1 ^ 2 * thetaCuspSingleAtomReflectionScale 1 x ^ (2 * i.val)))

private theorem compensation_sixteen_limit :
    Tendsto (fun x : ℝ => thetaCuspCenterCompensationSource x /
      (thetaCuspSourceTerm x 1 ^ 2 * thetaCuspSingleAtomReflectionScale 1 x ^ 8))
      atTop (𝓝 0) := by
  have h := thetaCuspCenterCompensationSource_twelfth_scaled_tendsto_zero.mul
    (thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero.pow 2)
  apply (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hq : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hf : thetaCuspSourceTerm x 1 ≠ 0 :=
    (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)).ne'
  field_simp [hq, hf]
  ring

private theorem balancedRepair_limit (C D : ℝ) (i j : Fin 5) :
    Tendsto (fun x => balancedRepair C D x i j) atTop (𝓝 (gaussianFive i j)) := by
  have hn := native_scaled_jet_tendsto (i.val + j.val)
  rw [profile_signed_even_jet] at hn
  have hd : Tendsto (fun x => (diagonal (fun k : Fin 5 =>
      (if k.val = 3 then C * thetaCuspCenterCompensationSource x
      else if k.val = 4 then D * thetaCuspCenterCompensationSource x else 0) /
        (thetaCuspSourceTerm x 1 ^ 2 * thetaCuspSingleAtomReflectionScale 1 x ^ (2 * k.val)))) i j)
      atTop (𝓝 0) := by
    by_cases hij : i = j
    · subst j
      simp only [diagonal_apply_eq]
      fin_cases i
      · simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))
      · simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))
      · simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))
      · simpa [mul_div_assoc] using
          thetaCuspCenterCompensationSource_twelfth_scaled_tendsto_zero.const_mul C
      · simpa [mul_div_assoc] using compensation_sixteen_limit.const_mul D
    · simp only [diagonal_apply_ne _ hij]
      exact tendsto_const_nhds
  simpa only [balancedRepair, Matrix.add_apply, gaussianFive, add_zero] using hn.add hd

/-- Every pair of fixed diagonal corrections retains the positive Gaussian tail. -/
theorem evenFiveRepair_posDef_eventually (C D : ℝ) :
    ∀ᶠ x : ℝ in atTop, (evenFiveRepair C D x).PosDef := by
  have hh (x : ℝ) : (balancedRepair C D x).IsHermitian := by
    apply Matrix.IsHermitian.add
    · rw [Matrix.IsHermitian]
      ext i j
      simp [add_comm]
    · exact Matrix.isHermitian_diagonal _
  have hp := posDef_eventually_of_tendsto gaussianFive_posDef
    (Filter.Eventually.of_forall hh) (balancedRepair_limit C D)
  filter_upwards [hp, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let T : Matrix (Fin 5) (Fin 5) ℝ := diagonal (fun i : Fin 5 => f * q ^ i.val)
  have hq : q ≠ 0 := by dsimp [q, thetaCuspSingleAtomReflectionScale]; positivity
  have hf : f ≠ 0 := (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx0 (by norm_num)).ne'
  have hT : Function.Injective T.mulVec := by
    intro v w h
    funext i
    have hi := congrFun h i
    simp only [T, Matrix.mulVec_diagonal] at hi
    exact mul_left_cancel₀ (mul_ne_zero hf (pow_ne_zero _ hq)) hi
  have he : evenFiveRepair C D x = Tᴴ * balancedRepair C D x * T := by
    ext i j
    simp only [T, diagonal_conjTranspose, star_trivial, diagonal_mul, mul_diagonal,
      evenFiveRepair, balancedRepair, Matrix.add_apply, nativeShiftedMatrix,
      thetaCuspNativeScaledEvenJet, add_zero]
    change (-1 : ℝ) ^ (i.val + j.val) * thetaCuspNativeReflectionJet (2 * (i.val + j.val)) x +
      (diagonal (fun k : Fin 5 => if k.val = 3 then C * thetaCuspCenterCompensationSource x
        else if k.val = 4 then D * thetaCuspCenterCompensationSource x else 0)) i j =
      (f * q ^ i.val) *
        (((-1 : ℝ) ^ (i.val + j.val) * thetaCuspNativeReflectionJet (2 * (i.val + j.val)) x) /
          (f ^ 2 * q ^ (i.val + j.val)) +
        (diagonal (fun k : Fin 5 => (if k.val = 3 then C * thetaCuspCenterCompensationSource x
          else if k.val = 4 then D * thetaCuspCenterCompensationSource x else 0) /
          (f ^ 2 * q ^ (2 * k.val)))) i j) * (f * q ^ j.val)
    by_cases hij : i = j
    · subst j
      simp only [diagonal_apply_eq, show 2 * i.val = i.val + i.val by omega, pow_add]
      field_simp [hf, hq]
      ring
    · simp only [diagonal_apply_ne _ hij, add_zero, pow_add]
      field_simp [hf, hq]
      ring
  rw [he]
  exact hx.conjTranspose_mul_mul_same hT

/-- One source-selected pair of corrections repairs the origin and a cofinal
ray. The unproved source comparison is confined to a compact interval. -/
theorem evenFiveRepair_compact_gap :
    ∃ δ R : ℝ, 0 < δ ∧ δ ≤ R ∧ ∀ x : ℝ, 0 ≤ x → (x < δ ∨ R ≤ x) →
      (evenFiveRepair 1000000000000 evenFiveRepairCoefficient x).PosDef := by
  obtain ⟨δ, hδ, hnear⟩ := evenFiveRepair_posDef_near_zero
  obtain ⟨R, htail⟩ := Filter.eventually_atTop.mp
    (evenFiveRepair_posDef_eventually 1000000000000 evenFiveRepairCoefficient)
  refine ⟨δ, max R δ, hδ, le_max_right _ _, fun x hx h => ?_⟩
  rcases h with h | h
  · exact hnear x (by simpa [abs_of_nonneg hx] using h)
  · exact htail x ((le_max_left _ _).trans h)

/-- Literal weighted matrix with the derivative of the same zero-boundary flux
on the last two diagonal entries. -/
def centerEvenFiveRepair (a C D r : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j : Fin 5 => (-1 : ℝ)^(i.val + j.val) *
    (r * Real.sinh (a*r) * thetaCuspNativeReflectionJet (2*(i.val+j.val)) (r/2)) +
    (diagonal (fun k : Fin 5 => if k.val = 3 then C * deriv (thetaCuspCenterCompensationFlux a) r
      else if k.val = 4 then D * deriv (thetaCuspCenterCompensationFlux a) r else 0)) i j

/-- Both corrected entries are integrable, with every other native entry retained. -/
theorem centerEvenFiveRepair_integrable {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2)
    (C D : ℝ) (i j : Fin 5) :
    IntegrableOn (fun r => centerEvenFiveRepair a C D r i j) (Ioi 0) := by
  have hi := (integrableOn_thetaCuspWeightedNativeReflectionJet ha0 ha
    (2*(i.val+j.val))).const_mul ((-1 : ℝ)^(i.val+j.val))
  have habs : |a| < 1 := by rw [abs_of_nonneg ha0]; linarith only [ha]
  have hf := integrableOn_deriv_thetaCuspCenterCompensationFlux habs
  unfold centerEvenFiveRepair
  simp only [diagonal_apply]
  split_ifs
  · exact hi.add (hf.const_mul C)
  · exact hi.add (hf.const_mul D)
  · simpa using hi
  · simpa using hi

/-- The two corrections integrate to zero: the complete literal mixed even
five-dimensional block is preserved entry by entry. -/
theorem centerEvenFiveRepair_integral {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2)
    (C D : ℝ) (i j : Fin 5) :
    (∫ r in Ioi 0, centerEvenFiveRepair a C D r i j) =
      thetaCuspCenterMixedSignedJet a (2*(i.val+j.val)) := by
  have hi := (integrableOn_thetaCuspWeightedNativeReflectionJet ha0 ha
    (2*(i.val+j.val))).const_mul ((-1 : ℝ)^(i.val+j.val))
  have habs : |a| < 1 := by rw [abs_of_nonneg ha0]; linarith only [ha]
  have hf := integrableOn_deriv_thetaCuspCenterCompensationFlux habs
  have hbase : (∫ r in Ioi 0, (-1 : ℝ)^(i.val+j.val) *
      (r * Real.sinh (a*r) * thetaCuspNativeReflectionJet (2*(i.val+j.val)) (r/2))) =
      thetaCuspCenterMixedSignedJet a (2*(i.val+j.val)) := by
    rw [integral_const_mul, thetaCuspCenterMixedSignedJet_even,
      iteratedDeriv_thetaCuspCenterMixedDensity_eq_integral_nativeJet ha0 ha]
  unfold centerEvenFiveRepair
  simp only [diagonal_apply]
  split_ifs
  · rw [integral_add hi (hf.const_mul C), integral_const_mul,
      integral_deriv_thetaCuspCenterCompensationFlux habs, mul_zero, add_zero]
    exact hbase
  · rw [integral_add hi (hf.const_mul D), integral_const_mul,
      integral_deriv_thetaCuspCenterCompensationFlux habs, mul_zero, add_zero]
    exact hbase
  · simpa using hbase
  · simpa using hbase

/-- Aperture weighting adds a positive diagonal reserve to each nonnegative
source correction. -/
theorem centerEvenFiveRepair_posDef_of_source {a C D r : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C) (hD : 0 ≤ D) (hr : 0 < r)
    (hs : (evenFiveRepair C D (r/2)).PosDef) :
    (centerEvenFiveRepair a C D r).PosDef := by
  let w := r * Real.sinh (a*r)
  let d := deriv (thetaCuspCenterCompensationFlux a) r -
    w * thetaCuspCenterCompensationSource (r/2)
  have hw : 0 < w := mul_pos hr (Real.sinh_pos_iff.mpr (mul_pos ha hr))
  have hd : 0 ≤ d := by
    apply sub_nonneg.mpr
    convert deriv_thetaCuspCenterCompensationFlux_lower ha.le hr.le using 1
    unfold w thetaCuspCenterCompensationSource
    ring
  let P : Matrix (Fin 5) (Fin 5) ℝ := diagonal (fun i : Fin 5 =>
    if i.val = 3 then C*d else if i.val = 4 then D*d else 0)
  have hP : P.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    split_ifs
    · exact mul_nonneg hC hd
    · exact mul_nonneg hD hd
    · exact le_rfl
  have he : centerEvenFiveRepair a C D r = w • evenFiveRepair C D (r/2) + P := by
    ext i j
    simp only [centerEvenFiveRepair, evenFiveRepair, nativeShiftedMatrix,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_zero, P, diagonal_apply]
    split_ifs <;> dsimp only [d, w] <;> ring
  rw [he]
  exact (hs.smul hw).add_posSemidef hP

/-- The single fixed source correction yields positive weighted matrices near
zero and past a common tail, simultaneously for every positive aperture. -/
theorem centerEvenFiveRepair_compact_gap :
    ∃ δ R : ℝ, 0 < δ ∧ δ ≤ R ∧ ∀ a r : ℝ, 0 < a → 0 < r →
      (r < δ ∨ R ≤ r) →
      (centerEvenFiveRepair a 1000000000000 evenFiveRepairCoefficient r).PosDef := by
  obtain ⟨δ, R, hδ, hR, hs⟩ := evenFiveRepair_compact_gap
  refine ⟨2*δ, 2*R, by positivity, by linarith only [hR], fun a r ha hr h => ?_⟩
  apply centerEvenFiveRepair_posDef_of_source ha (by norm_num)
    evenFiveRepairCoefficient_pos.le hr
  apply hs (r/2) (by positivity)
  rcases h with h | h
  · exact Or.inl (by linarith only [h])
  · exact Or.inr (by linarith only [h])

end GaloisForLFunctions.ThetaCuspSections
