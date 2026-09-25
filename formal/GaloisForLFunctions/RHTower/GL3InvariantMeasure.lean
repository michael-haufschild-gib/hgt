import GaloisForLFunctions.RHTower.GL3IwasawaHaar
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.Compact


/-!
# `dx dy / (y₁y₂)³` is the `GL₃(ℝ)`-invariant measure on `h³`

The orbit map `SL₃(ℝ) → h³`, `g ↦ g • 1 = ofMat (g gᵀ)`, is continuous, equivariant
(`toGL_smul_orbit`) and proper (`isCompact_orbit_preimage`): on a compact `K ⊆ h³` the quantity
`y₁²y₂` is bounded below and `tr gram` above, and `g gᵀ = (g gᵀ)₂₂ · gram z` with
`(g gᵀ)₂₂³ (y₁²y₂)² = 1` bounds the entries of `g`.

So the image of Haar measure of `SL₃(ℝ)` is locally finite, nonzero, and invariant under every
`g ∈ GL₃(ℝ)`, because `g` is a nonzero scalar times an element of `SL₃(ℝ)` (`exists_sl_smul`, odd
dimension) and scalars act trivially. It is in particular left invariant under the Iwasawa group
`h³`, whose Haar measure is `dx dy / (y₁y₂)³` (`GL3IwasawaHaar`). Uniqueness of Haar measure makes
the two proportional with a nonzero factor, so `dx dy / (y₁y₂)³` is `GL₃(ℝ)`-invariant, hence also
`SL₃(ℤ)`-invariant. No Jacobian of a non-triangular element is computed.
-/

open Matrix Topology MeasureTheory
open scoped NNReal ENNReal

namespace GaloisForLFunctions.RHTower.GL3

/-- `SL₃(ℝ)` with its matrix topology and Borel structure. -/
abbrev SL3R := Matrix.SpecialLinearGroup (Fin 3) ℝ

instance : LocallyCompactSpace SL3R := by
  haveI : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 3 → Fin 3 → ℝ))
  exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace

instance : SecondCountableTopology SL3R := by
  haveI : SecondCountableTopology (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → ℝ))
  exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.secondCountableTopology

instance : MeasurableSpace SL3R := borel SL3R

instance : BorelSpace SL3R := ⟨rfl⟩

namespace H3

theorem posDef_mul_transpose {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : IsUnit A) : (A * Aᵀ).PosDef := by
  have h := (PosDef.one (n := Fin 3) (R := ℝ)).mul_mul_conjTranspose_same
    (vecMul_injective_of_isUnit hA)
  simpa [conjTranspose_eq_transpose_of_trivial] using h

theorem isUnit_sl (g : SL3R) : IsUnit (g : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [Matrix.isUnit_iff_isUnit_det, g.2]; exact isUnit_one

/-- The orbit map of the base point `1 = (0,0,0,1,1)`: `g ↦ g • 1 = ofMat (g gᵀ)`. -/
noncomputable def orbit (g : SL3R) : H3 :=
  ofMat ((g : Matrix (Fin 3) (Fin 3) ℝ) * (g : Matrix (Fin 3) (Fin 3) ℝ)ᵀ)

theorem continuous_orbit : Continuous orbit := by
  have hS : Continuous fun g : SL3R =>
      (g : Matrix (Fin 3) (Fin 3) ℝ) * (g : Matrix (Fin 3) (Fin 3) ℝ)ᵀ :=
    continuous_subtype_val.matrix_mul continuous_subtype_val.matrix_transpose
  have e : orbit = fun g => ofPD _ (posDef_mul_transpose (isUnit_sl g)) :=
    funext fun g => ofMat_eq _
  rw [e]
  exact continuous_ofPD hS _

/-- `g • ofMat (A Aᵀ) = ofMat ((gA)(gA)ᵀ)` for invertible `A`. -/
theorem smul_ofMat_mul_transpose (g : GL (Fin 3) ℝ) {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : IsUnit A) :
    g • ofMat (A * Aᵀ) =
      ofMat (((g : Matrix (Fin 3) (Fin 3) ℝ) * A) * ((g : Matrix (Fin 3) (Fin 3) ℝ) * A)ᵀ) := by
  have hP := posDef_mul_transpose hA
  have hgA : IsUnit ((g : Matrix (Fin 3) (Fin 3) ℝ) * A) := (Units.isUnit g).mul hA
  have e : (g : Matrix (Fin 3) (Fin 3) ℝ) * (A * Aᵀ) * (g : Matrix (Fin 3) (Fin 3) ℝ)ᵀ =
      ((g : Matrix (Fin 3) (Fin 3) ℝ) * A) * ((g : Matrix (Fin 3) (Fin 3) ℝ) * A)ᵀ := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [smul_def, gram_ofMat_of_posDef hP, Matrix.mul_smul, Matrix.smul_mul, e,
    ofMat_smul (posDef_mul_transpose hgA) (inv_pos.2 hP.diag_pos)]

/-- **Equivariance of the orbit map.** -/
theorem toGL_smul_orbit (g h : SL3R) :
    Matrix.SpecialLinearGroup.toGL g • orbit h = orbit (g * h) := by
  rw [orbit, smul_ofMat_mul_transpose _ (isUnit_sl h)]
  rfl

/-- Nonzero scalar multiples act identically on `h³`. -/
theorem smul_eq_of_val_eq_smul {g g' : GL (Fin 3) ℝ} {r : ℝ} (hr : r ≠ 0)
    (h : (g' : Matrix (Fin 3) (Fin 3) ℝ) = r • (g : Matrix (Fin 3) (Fin 3) ℝ)) (w : H3) :
    g' • w = g • w := by
  have e : r • (g : Matrix (Fin 3) (Fin 3) ℝ) * w.gram * (r • (g : Matrix (Fin 3) (Fin 3) ℝ))ᵀ =
      (r * r) • ((g : Matrix (Fin 3) (Fin 3) ℝ) * w.gram * (g : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) := by
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [smul_def, smul_def, h, e, ofMat_smul (posDef_conj g w) (mul_self_pos.2 hr)]

/-- Every real number has a real cube root. -/
theorem exists_cube_root (d : ℝ) : ∃ r : ℝ, r ^ 3 = d := by
  rcases le_or_gt 0 d with hd | hd
  · refine ⟨d ^ (1 / 3 : ℝ), ?_⟩
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd]; norm_num
  · refine ⟨-((-d) ^ (1 / 3 : ℝ)), ?_⟩
    have h3 : ((-d) ^ (1 / 3 : ℝ)) ^ 3 = -d := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
    rw [neg_pow, h3]; ring

/-- **Every invertible matrix is a scalar multiple of an element of `SL₃(ℝ)`** (odd dimension). -/
theorem exists_sl_smul (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.det ≠ 0) :
    ∃ r : ℝ, r ≠ 0 ∧ ∃ g : SL3R, A = r • (g : Matrix (Fin 3) (Fin 3) ℝ) := by
  obtain ⟨r, hr⟩ := exists_cube_root A.det
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr; exact hA hr.symm
  refine ⟨r, hr0, ⟨r⁻¹ • A, ?_⟩, ?_⟩
  · rw [Matrix.det_smul, Fintype.card_fin, inv_pow, hr, inv_mul_cancel₀ hA]
  · show A = r • (r⁻¹ • A)
    rw [smul_smul, mul_inv_cancel₀ hr0, one_smul]

/-! ### Properness of the orbit map -/

theorem det_gram (z : H3) : z.gram.det = (z.y1 ^ 2 * z.y2) ^ 2 := by
  rw [gram, Matrix.det_mul, Matrix.det_transpose, det_mat]; ring

/-- **The orbit map is proper.** On a compact set `K ⊆ h³`, `y₁²y₂` is bounded below and the
diagonal of `gram` above; since `g gᵀ = (g gᵀ)₂₂ · gram z` with `(g gᵀ)₂₂³ (y₁²y₂)² = 1`, the entries
of `g` are bounded, and `SL₃(ℝ)` is closed in the matrices. -/
theorem isCompact_orbit_preimage {K : Set H3} (hK : IsCompact K) : IsCompact (orbit ⁻¹' K) := by
  -- a lower bound for `y₁²y₂` on `K`
  have hf : Continuous fun z : H3 => z.y1 ^ 2 * z.y2 := by fun_prop
  obtain ⟨δ, hδ, hδK⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, δ ≤ z.y1 ^ 2 * z.y2 := by
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact ⟨1, one_pos, fun z hz => hz.elim⟩
    · obtain ⟨z0, hz0, hmin⟩ := hK.exists_isMinOn hne hf.continuousOn
      exact ⟨_, mul_pos (pow_pos z0.y1_pos 2) z0.y2_pos, fun z hz => hmin hz⟩
  -- an upper bound for the trace of `gram` on `K`
  have htr : Continuous fun z : H3 => z.gram 0 0 + z.gram 1 1 + z.gram 2 2 := by
    have := continuous_gram
    fun_prop
  obtain ⟨M, hM⟩ := (hK.image_of_continuousOn htr.continuousOn).isBounded.bddAbove
  set C : ℝ := max 1 (δ ^ 2)⁻¹
  set B : ℝ := C * M + 1
  have hbound : ∀ g : SL3R, orbit g ∈ K → ∀ i j, (g : Matrix (Fin 3) (Fin 3) ℝ) i j ∈ Set.Icc (-B) B := by
    intro g hg i j
    set P := (g : Matrix (Fin 3) (Fin 3) ℝ) * (g : Matrix (Fin 3) (Fin 3) ℝ)ᵀ with hPdef
    have hP : P.PosDef := posDef_mul_transpose (isUnit_sl g)
    set z := orbit g
    have hgram : z.gram = (P 2 2)⁻¹ • P := gram_ofMat_of_posDef hP
    have hp22 := hP.diag_pos (i := 2)
    have hdetP : P.det = 1 := by
      rw [hPdef, Matrix.det_mul, Matrix.det_transpose, g.2, one_mul]
    -- `(P₂₂)³ · (y₁²y₂)² = 1`
    have hcube : P 2 2 ^ 3 * (z.y1 ^ 2 * z.y2) ^ 2 = 1 := by
      have := congrArg Matrix.det hgram
      rw [det_gram, Matrix.det_smul, Fintype.card_fin, hdetP, mul_one] at this
      rw [this, inv_pow, mul_inv_cancel₀ (pow_pos hp22 3).ne']
    have hzK : δ ≤ z.y1 ^ 2 * z.y2 := hδK z hg
    have hP22 : P 2 2 ≤ C := by
      rcases le_or_gt (P 2 2) 1 with h | h
      · exact h.trans (le_max_left _ _)
      · refine le_trans ?_ (le_max_right _ _)
        have h2 : P 2 2 ^ 3 * δ ^ 2 ≤ 1 := by
          rw [← hcube]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ.le hzK 2) (pow_pos hp22 3).le
        have h3 : P 2 2 * δ ^ 2 ≤ 1 := by
          have : P 2 2 * δ ^ 2 ≤ P 2 2 ^ 3 * δ ^ 2 :=
            mul_le_mul_of_nonneg_right (by
              have := mul_pos (mul_pos hp22 (sub_pos.2 h)) (by linarith : (0 : ℝ) < P 2 2 + 1)
              nlinarith) (by positivity)
          linarith
        calc P 2 2 = (P 2 2 * δ ^ 2) * (δ ^ 2)⁻¹ := by field_simp
          _ ≤ 1 * (δ ^ 2)⁻¹ := by gcongr
          _ = (δ ^ 2)⁻¹ := one_mul _
    have hPii : P i i = P 2 2 * z.gram i i := by
      rw [hgram, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hp22.ne', one_mul]
    have hgii : ∀ k, 0 ≤ z.gram k k := fun k => (z.posDef_gram.diag_pos (i := k)).le
    have htrace : z.gram i i ≤ M := by
      have hmem : z.gram 0 0 + z.gram 1 1 + z.gram 2 2 ≤ M := hM ⟨z, hg, rfl⟩
      fin_cases i <;> simp <;> linarith [hgii 0, hgii 1, hgii 2]
    have hsq : (g : Matrix (Fin 3) (Fin 3) ℝ) i j ^ 2 ≤ P i i := by
      have : P i i = ∑ k, (g : Matrix (Fin 3) (Fin 3) ℝ) i k ^ 2 := by
        simp [hPdef, Matrix.mul_apply, sq]
      rw [this]
      exact Finset.single_le_sum (f := fun k => (g : Matrix (Fin 3) (Fin 3) ℝ) i k ^ 2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ j)
    have hCM : (g : Matrix (Fin 3) (Fin 3) ℝ) i j ^ 2 ≤ C * M := by
      calc _ ≤ P i i := hsq
        _ = P 2 2 * z.gram i i := hPii
        _ ≤ C * M := mul_le_mul hP22 htrace (hgii i) ((le_max_left _ _).trans' zero_le_one)
    constructor <;> nlinarith [sq_nonneg ((g : Matrix (Fin 3) (Fin 3) ℝ) i j - 1),
      sq_nonneg ((g : Matrix (Fin 3) (Fin 3) ℝ) i j + 1)]
  have hbox : Subtype.val '' (orbit ⁻¹' K) ⊆
      (Set.univ.pi fun _ : Fin 3 => Set.univ.pi fun _ : Fin 3 => Set.Icc (-B) B :
        Set (Fin 3 → Fin 3 → ℝ)) := by
    rintro _ ⟨g, hg, rfl⟩
    exact fun i _ j _ => hbound g hg i j
  have hclosed : IsClosed (Subtype.val '' (orbit ⁻¹' K) : Set (Matrix (Fin 3) (Fin 3) ℝ)) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.isClosedMap _
      (hK.isClosed.preimage continuous_orbit)
  have hcpt : IsCompact (Subtype.val '' (orbit ⁻¹' K) : Set (Matrix (Fin 3) (Fin 3) ℝ)) :=
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset
      hclosed hbox
  have := Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage hcpt
  rwa [Set.preimage_image_eq _ Subtype.val_injective] at this

/-! ### The pushforward of Haar measure on `SL₃(ℝ)` -/

/-- The image of Haar measure of `SL₃(ℝ)` under the orbit map. -/
noncomputable def orbitMeasure : Measure H3 := Measure.map orbit (Measure.haar : Measure SL3R)

instance : IsFiniteMeasureOnCompacts orbitMeasure :=
  ⟨fun K hK => by
    rw [orbitMeasure, Measure.map_apply continuous_orbit.measurable hK.measurableSet]
    exact (isCompact_orbit_preimage hK).measure_lt_top⟩

/-- `h ↦ g • orbit h` is the orbit map precomposed with left multiplication by the `SL₃(ℝ)`
representative of `g`. -/
theorem smul_orbit_eq {g : GL (Fin 3) ℝ} {r : ℝ} (hr : r ≠ 0) {g₀ : SL3R}
    (h : (g : Matrix (Fin 3) (Fin 3) ℝ) = r • (g₀ : Matrix (Fin 3) (Fin 3) ℝ)) (x : SL3R) :
    g • orbit x = orbit (g₀ * x) := by
  rw [smul_eq_of_val_eq_smul (g := Matrix.SpecialLinearGroup.toGL g₀) hr h, toGL_smul_orbit]

/-- The orbit measure transforms like Haar measure under every `g ∈ GL₃(ℝ)`. -/
theorem orbitMeasure_preimage_smul (g : GL (Fin 3) ℝ) {s : Set H3} (hs : MeasurableSet s) :
    orbitMeasure ((fun w => g • w) ⁻¹' s) = orbitMeasure s := by
  obtain ⟨r, hr, g₀, hg₀⟩ := exists_sl_smul (g : Matrix (Fin 3) (Fin 3) ℝ)
    (Matrix.isUnit_iff_isUnit_det _ |>.1 (Units.isUnit g)).ne_zero
  have hms : MeasurableSet ((fun w => g • w) ⁻¹' s) :=
    (continuous_const_smul g).measurable hs
  rw [orbitMeasure, Measure.map_apply continuous_orbit.measurable hms,
    Measure.map_apply continuous_orbit.measurable hs]
  have e : orbit ⁻¹' ((fun w => g • w) ⁻¹' s) = (fun x => g₀ * x) ⁻¹' (orbit ⁻¹' s) := by
    ext x
    simp only [Set.mem_preimage, smul_orbit_eq hr hg₀]
  rw [e, measure_preimage_mul]

instance : orbitMeasure.IsMulLeftInvariant :=
  ⟨fun z => by
    ext A hA
    rw [Measure.map_apply (measurable_const_mul z) hA]
    have e : (fun w => z * w) ⁻¹' A = (fun w => toGL z • w) ⁻¹' A := by
      ext w; simp only [Set.mem_preimage, toGL_smul]
    rw [e, orbitMeasure_preimage_smul _ hA]⟩

theorem orbitMeasure_ne_zero : orbitMeasure ≠ 0 := by
  intro h
  have := congrArg (fun μ : Measure H3 => μ Set.univ) h
  simp only [orbitMeasure, Measure.map_apply continuous_orbit.measurable MeasurableSet.univ,
    Set.preimage_univ, Measure.coe_zero, Pi.zero_apply] at this
  exact (Measure.measure_univ_pos.2 (NeZero.ne (Measure.haar : Measure SL3R))).ne' this

/-- **Haar uniqueness.** The orbit measure is a positive multiple of `dx dy / (y₁y₂)³`. -/
theorem orbitMeasure_eq :
    orbitMeasure = orbitMeasure.haarScalarFactor volume • (volume : Measure H3) :=
  Measure.isMulLeftInvariant_eq_smul orbitMeasure volume

theorem haarScalarFactor_ne_zero : orbitMeasure.haarScalarFactor (volume : Measure H3) ≠ 0 := by
  intro h
  apply orbitMeasure_ne_zero
  rw [orbitMeasure_eq, h, zero_smul]

/-- **`dx dy / (y₁y₂)³` is `GL₃(ℝ)`-invariant.** -/
instance : SMulInvariantMeasure (GL (Fin 3) ℝ) H3 volume :=
  ⟨fun g s hs => by
    have h := orbitMeasure_preimage_smul g hs
    rw [orbitMeasure_eq, Measure.smul_apply, Measure.smul_apply] at h
    simp only [ENNReal.smul_def, smul_eq_mul] at h
    exact (ENNReal.mul_right_inj (by exact_mod_cast haarScalarFactor_ne_zero)
      ENNReal.coe_ne_top).1 h⟩

/-- Every `g ∈ GL₃(ℝ)` preserves `dx dy / (y₁y₂)³`. -/
theorem measurePreserving_smul_GL (g : GL (Fin 3) ℝ) :
    MeasurePreserving (fun w : H3 => g • w) volume volume :=
  measurePreserving_smul g volume

/-- **`dx dy / (y₁y₂)³` is `SL₃(ℤ)`-invariant.** -/
instance : SMulInvariantMeasure (Matrix.SpecialLinearGroup (Fin 3) ℤ) H3 volume :=
  ⟨fun γ _ hs => SMulInvariantMeasure.measure_preimage_smul (slToGL γ) hs⟩

end H3
end GaloisForLFunctions.RHTower.GL3
