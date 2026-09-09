import GaloisForLFunctions.RHTower.FokasLenellsCauchyLinfty

/-!
# Full matrix multiplier norms survive boundary Cauchy compression

Simultaneous modulation on the two existing boundary coordinates preserves
their product norm. Moving both coordinates into the selected Fourier ray
recovers the norm of every output. Hence the Cauchy projection cannot reduce
the operator norm of any matrix of bounded measurable multipliers.
-/

open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open GaloisForLFunctions.HTGeometry
namespace RHTower.FokasLenells
noncomputable section

/-- Product of two ordinary L-infinity symbols, using the existing Holder construction. -/
def lineLinftyProduct (g h : Lp ℂ ∞ (volume : Measure ℝ)) : Lp ℂ ∞ (volume : Measure ℝ) :=
  (ContinuousLinearMap.lsmul ℂ ℂ).holder ∞ g h

/-- The Holder product is the pointwise product of representatives almost everywhere. -/
theorem lineLinftyProduct_ae (g h : Lp ℂ ∞ (volume : Measure ℝ)) :
    (lineLinftyProduct g h : ℝ → ℂ) =ᵐ[volume] fun z => g z * h z :=
  (ContinuousLinearMap.lsmul ℂ ℂ).coeFn_holder g h

/-- Operator composition agrees exactly with multiplication of the L-infinity symbols. -/
theorem lineLinftyMultiplier_comp (g h : Lp ℂ ∞ (volume : Measure ℝ)) :
    (lineLinftyMultiplier g).comp (lineLinftyMultiplier h) =
      lineLinftyMultiplier (lineLinftyProduct g h) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [lineLinftyMultiplier_ae g (lineLinftyMultiplier h u),
    lineLinftyMultiplier_ae h u, lineLinftyMultiplier_ae (lineLinftyProduct g h) u,
    lineLinftyProduct_ae g h] with z h0 h1 h2 h3
  change lineLinftyMultiplier g (lineLinftyMultiplier h u) z = _
  rw [h0, h1, h2, h3, mul_assoc]

/-- Every bounded measurable multiplier commutes with the Fourier modulation probe. -/
theorem lineLinftyMultiplier_commutes_modulation (g : Lp ℂ ∞ (volume : Measure ℝ))
    (a : ℝ) (u : SoninL2) :
    lineLinftyMultiplier g (modulationMul a u) = modulationMul a (lineLinftyMultiplier g u) := by
  apply Lp.ext
  filter_upwards [lineLinftyMultiplier_ae g (modulationMul a u), coeFn_modulationMul a u,
    coeFn_modulationMul a (lineLinftyMultiplier g u), lineLinftyMultiplier_ae g u]
    with z h0 h1 h2 h3
  rw [h0, h1, h2, h3]
  ring

/-- The same modulation is applied to both boundary coordinates. -/
def boundaryModulation (a : ℝ) : Boundary →L[ℂ] Boundary :=
  (modulationMul a).prodMap (modulationMul a)

/-- Simultaneous modulation is an isometry for the actual product boundary norm. -/
theorem norm_boundaryModulation (a : ℝ) (u : Boundary) : ‖boundaryModulation a u‖ = ‖u‖ := by
  change max ‖modulationMul a u.1‖ ‖modulationMul a u.2‖ = max ‖u.1‖ ‖u.2‖
  rw [norm_modulationMul_eq, norm_modulationMul_eq]

/-- One modulation direction asymptotically recovers the full norm of both Cauchy coordinates. -/
theorem boundaryCauchy_modulation_norm_tendsto (u : Boundary) :
    Tendsto (fun a => ‖boundaryCauchy (boundaryModulation a u)‖) atBot (𝓝 ‖u‖) := by
  change Tendsto (fun a => max ‖negativeCauchy (modulationMul a u.1)‖
    ‖negativeCauchy (modulationMul a u.2)‖) atBot (𝓝 (max ‖u.1‖ ‖u.2‖))
  exact (negativeCauchy_modulation_norm_tendsto u.1).max (negativeCauchy_modulation_norm_tendsto u.2)

private def rawBoundaryLinftyMatrix (A : Matrix (Fin 2) (Fin 2) (Lp ℂ ∞ (volume : Measure ℝ))) :
    Boundary →L[ℂ] Boundary :=
  (((lineLinftyMultiplier (A 0 0)).comp (ContinuousLinearMap.fst ℂ SoninL2 SoninL2)) +
    ((lineLinftyMultiplier (A 0 1)).comp (ContinuousLinearMap.snd ℂ SoninL2 SoninL2))).prod
  (((lineLinftyMultiplier (A 1 0)).comp (ContinuousLinearMap.fst ℂ SoninL2 SoninL2)) +
    ((lineLinftyMultiplier (A 1 1)).comp (ContinuousLinearMap.snd ℂ SoninL2 SoninL2)))

private theorem rawBoundaryLinftyMatrix_apply
    (A : Matrix (Fin 2) (Fin 2) (Lp ℂ ∞ (volume : Measure ℝ))) (u : Boundary) :
    rawBoundaryLinftyMatrix A u =
      (lineLinftyMultiplier (A 0 0) u.1 + lineLinftyMultiplier (A 0 1) u.2,
       lineLinftyMultiplier (A 1 0) u.1 + lineLinftyMultiplier (A 1 1) u.2) := rfl

/-- The full matrix representation uses ordinary L-infinity entries, with no supplied hypotheses. -/
def boundaryLinftyMatrix : Matrix (Fin 2) (Fin 2) (Lp ℂ ∞ (volume : Measure ℝ)) →ₗ[ℂ]
    (Boundary →L[ℂ] Boundary) where
  toFun := rawBoundaryLinftyMatrix
  map_add' A B := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [_root_.add_apply, rawBoundaryLinftyMatrix_apply, Prod.mk_add_mk]
    apply Prod.ext <;> dsimp <;> simp only [map_add, _root_.add_apply] <;> abel
  map_smul' c A := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [_root_.smul_apply, rawBoundaryLinftyMatrix_apply, RingHom.id_apply, Prod.smul_mk]
    apply Prod.ext <;> dsimp <;> simp only [map_smul, _root_.smul_apply, smul_add]

/-- Matrix representation acts on both actual L2 coordinates. -/
theorem boundaryLinftyMatrix_apply
    (A : Matrix (Fin 2) (Fin 2) (Lp ℂ ∞ (volume : Measure ℝ))) (u : Boundary) :
    boundaryLinftyMatrix A u =
      (lineLinftyMultiplier (A 0 0) u.1 + lineLinftyMultiplier (A 0 1) u.2,
       lineLinftyMultiplier (A 1 0) u.1 + lineLinftyMultiplier (A 1 1) u.2) := rfl

/-- Scalar modulation commutes with the complete matrix action, including off-diagonal coupling. -/
theorem boundaryLinftyMatrix_commutes_modulation
    (A : Matrix (Fin 2) (Fin 2) (Lp ℂ ∞ (volume : Measure ℝ))) (a : ℝ) (u : Boundary) :
    boundaryLinftyMatrix A (boundaryModulation a u) = boundaryModulation a (boundaryLinftyMatrix A u) := by
  change (lineLinftyMultiplier (A 0 0) (modulationMul a u.1) +
      lineLinftyMultiplier (A 0 1) (modulationMul a u.2),
    lineLinftyMultiplier (A 1 0) (modulationMul a u.1) +
      lineLinftyMultiplier (A 1 1) (modulationMul a u.2)) =
    (modulationMul a (lineLinftyMultiplier (A 0 0) u.1 + lineLinftyMultiplier (A 0 1) u.2),
      modulationMul a (lineLinftyMultiplier (A 1 0) u.1 + lineLinftyMultiplier (A 1 1) u.2))
  simp only [map_add, lineLinftyMultiplier_commutes_modulation]

/-- Signed boundary Cauchy compression preserves the entire matrix multiplier operator norm. -/
theorem norm_boundaryCauchy_comp_boundaryLinftyMatrix
    (A : Matrix (Fin 2) (Fin 2) (Lp ℂ ∞ (volume : Measure ℝ))) :
    ‖boundaryCauchy.comp (boundaryLinftyMatrix A)‖ = ‖boundaryLinftyMatrix A‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro u
    exact (boundaryCauchy_bound _).trans ((boundaryLinftyMatrix A).le_opNorm u)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro u
    apply le_of_tendsto (boundaryCauchy_modulation_norm_tendsto (boundaryLinftyMatrix A u))
    apply Eventually.of_forall
    intro a
    have h := (boundaryCauchy.comp (boundaryLinftyMatrix A)).le_opNorm (boundaryModulation a u)
    change ‖boundaryCauchy (boundaryLinftyMatrix A (boundaryModulation a u))‖ ≤ _ at h
    rw [boundaryLinftyMatrix_commutes_modulation, norm_boundaryModulation] at h
    exact h

/-- Distances between full matrix multiplier operators survive Cauchy compression exactly. -/
theorem dist_boundaryCauchy_comp_boundaryLinftyMatrix
    (A B : Matrix (Fin 2) (Fin 2) (Lp ℂ ∞ (volume : Measure ℝ))) :
    dist (boundaryCauchy.comp (boundaryLinftyMatrix A)) (boundaryCauchy.comp (boundaryLinftyMatrix B)) =
      dist (boundaryLinftyMatrix A) (boundaryLinftyMatrix B) := by
  simp only [dist_eq_norm, ← ContinuousLinearMap.comp_sub, ← map_sub]
  exact norm_boundaryCauchy_comp_boundaryLinftyMatrix (A-B)

/-- The full boundary operator determines all four L-infinity entries. -/
theorem boundaryLinftyMatrix_injective : Function.Injective boundaryLinftyMatrix := by
  intro A B h
  have h00 : lineLinftyMultiplier (A 0 0) = lineLinftyMultiplier (B 0 0) := by
    apply ContinuousLinearMap.ext
    intro u
    have he := congrArg (fun T : Boundary →L[ℂ] Boundary => (T (u,0)).1) h
    simpa only [boundaryLinftyMatrix_apply, map_zero, add_zero] using he
  have h01 : lineLinftyMultiplier (A 0 1) = lineLinftyMultiplier (B 0 1) := by
    apply ContinuousLinearMap.ext
    intro u
    have he := congrArg (fun T : Boundary →L[ℂ] Boundary => (T (0,u)).1) h
    simpa only [boundaryLinftyMatrix_apply, map_zero, zero_add] using he
  have h10 : lineLinftyMultiplier (A 1 0) = lineLinftyMultiplier (B 1 0) := by
    apply ContinuousLinearMap.ext
    intro u
    have he := congrArg (fun T : Boundary →L[ℂ] Boundary => (T (u,0)).2) h
    simpa only [boundaryLinftyMatrix_apply, map_zero, add_zero] using he
  have h11 : lineLinftyMultiplier (A 1 1) = lineLinftyMultiplier (B 1 1) := by
    apply ContinuousLinearMap.ext
    intro u
    have he := congrArg (fun T : Boundary →L[ℂ] Boundary => (T (0,u)).2) h
    simpa only [boundaryLinftyMatrix_apply, map_zero, zero_add] using he
  funext i j
  fin_cases i <;> fin_cases j
  · exact lineLinftyMultiplier_injective h00
  · exact lineLinftyMultiplier_injective h01
  · exact lineLinftyMultiplier_injective h10
  · exact lineLinftyMultiplier_injective h11

/-- Signed Cauchy compression still determines every entry of a bounded matrix symbol. -/
theorem boundaryCauchy_comp_boundaryLinftyMatrix_injective :
    Function.Injective (fun A => boundaryCauchy.comp (boundaryLinftyMatrix A)) := by
  intro A B h
  change boundaryCauchy.comp (boundaryLinftyMatrix A) =
    boundaryCauchy.comp (boundaryLinftyMatrix B) at h
  apply boundaryLinftyMatrix_injective
  apply eq_of_dist_eq_zero
  rw [← dist_boundaryCauchy_comp_boundaryLinftyMatrix, h, dist_self]

/-- The off-diagonal symbol shape shared by all existing first and mixed jump derivatives. -/
def offDiagonalLinftyMatrix (a b : Lp ℂ ∞ (volume : Measure ℝ)) :
    Matrix (Fin 2) (Fin 2) (Lp ℂ ∞ (volume : Measure ℝ)) := !![0, -a; b, 0]

/-- The off-diagonal matrix acts by the two existing multiplier channels. -/
theorem boundaryLinftyMatrix_offDiagonal_apply (a b : Lp ℂ ∞ (volume : Measure ℝ)) (u : Boundary) :
    boundaryLinftyMatrix (offDiagonalLinftyMatrix a b) u =
      (-lineLinftyMultiplier a u.2, lineLinftyMultiplier b u.1) := by
  change (lineLinftyMultiplier 0 u.1 + lineLinftyMultiplier (-a) u.2,
    lineLinftyMultiplier b u.1 + lineLinftyMultiplier 0 u.2) = _
  simp only [map_zero, map_neg, _root_.zero_apply, _root_.neg_apply, zero_add, add_zero]

/-- The full regularized jump shape includes its genuine nonlinear diagonal entry. -/
def regularizedLinftyJumpMatrix (a b : Lp ℂ ∞ (volume : Measure ℝ)) :
    Matrix (Fin 2) (Fin 2) (Lp ℂ ∞ (volume : Measure ℝ)) := !![0, -a; b, -lineLinftyProduct a b]

/-- The matrix representation retains the exact nonlinear product on the diagonal. -/
theorem boundaryLinftyMatrix_regularizedJump_apply (a b : Lp ℂ ∞ (volume : Measure ℝ)) (u : Boundary) :
    boundaryLinftyMatrix (regularizedLinftyJumpMatrix a b) u =
      (-lineLinftyMultiplier a u.2,
        lineLinftyMultiplier b u.1 - lineLinftyMultiplier a (lineLinftyMultiplier b u.2)) := by
  change (lineLinftyMultiplier 0 u.1 + lineLinftyMultiplier (-a) u.2,
    lineLinftyMultiplier b u.1 + lineLinftyMultiplier (-lineLinftyProduct a b) u.2) = _
  simp only [map_zero, map_neg, _root_.zero_apply, _root_.neg_apply, zero_add]
  rw [← lineLinftyMultiplier_comp]
  rfl

/-- The off-diagonal generator has the exact maximum of the two essential-supremum norms. -/
theorem norm_boundaryLinftyMatrix_offDiagonal (a b : Lp ℂ ∞ (volume : Measure ℝ)) :
    ‖boundaryLinftyMatrix (offDiagonalLinftyMatrix a b)‖ = max ‖a‖ ‖b‖ := by
  let T := boundaryLinftyMatrix (offDiagonalLinftyMatrix a b)
  have h0 : 0 ≤ max ‖a‖ ‖b‖ := (norm_nonneg a).trans (le_max_left _ _)
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ h0
    intro u
    rw [boundaryLinftyMatrix_offDiagonal_apply]
    change max ‖-lineLinftyMultiplier a u.2‖ ‖lineLinftyMultiplier b u.1‖ ≤ _
    rw [norm_neg, max_le_iff]
    have ha := (lineLinftyMultiplier a).le_opNorm u.2
    have hb := (lineLinftyMultiplier b).le_opNorm u.1
    rw [norm_lineLinftyMultiplier] at ha hb
    exact ⟨ha.trans (mul_le_mul (le_max_left _ _) (norm_snd_le u) (norm_nonneg _) h0),
      hb.trans (mul_le_mul (le_max_right _ _) (norm_fst_le u) (norm_nonneg _) h0)⟩
  · apply max_le
    · rw [← norm_lineLinftyMultiplier]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro u
      have h := norm_fst_le (T (0,u))
      dsimp only [T] at h
      rw [boundaryLinftyMatrix_offDiagonal_apply] at h
      simp only [norm_neg] at h
      have ht := T.le_opNorm (0,u)
      dsimp only [T] at ht
      rw [boundaryLinftyMatrix_offDiagonal_apply] at ht
      have hh := h.trans ht
      simpa only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg u)] using hh
    · rw [← norm_lineLinftyMultiplier]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro u
      have h := norm_snd_le (T (u,0))
      dsimp only [T] at h
      rw [boundaryLinftyMatrix_offDiagonal_apply] at h
      have ht := T.le_opNorm (u,0)
      dsimp only [T] at ht
      rw [boundaryLinftyMatrix_offDiagonal_apply] at ht
      have hh := h.trans ht
      simpa only [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg u)] using hh

end
end RHTower.FokasLenells
