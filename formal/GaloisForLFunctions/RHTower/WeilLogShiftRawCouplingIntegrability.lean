import GaloisForLFunctions.RHTower.WeilLogShiftRawLipschitzComparison

/-! Finite raw marginals discharge every integrability premise in transport weak duality. -/

open MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

def finiteWeilCanonicalRawCouplingSpace (r k : ℕ) :=
  {π : Measure (ℝ × ℝ) // IsCoupling (finiteWeilCanonicalRawIndexLaw r k : Measure ℝ)
    (finiteWeilCanonicalRawCorrectionLaw r k : Measure ℝ) π}

theorem finiteWeilCanonicalRawCoupling_fst_integrable (r k : ℕ)
    (π : finiteWeilCanonicalRawCouplingSpace r k) (f : {f : ℝ → ℝ // Continuous f}) :
    Integrable (fun p : ℝ × ℝ => f.val p.1) π.val := by
  have h : Integrable f.val (π.val.map Prod.fst) := by
    rw [π.property.1, finiteWeilCanonicalRawIndexLaw]
    exact finiteWeilCanonicalObservableLaw_integrable r k _ _
  exact (integrable_map_measure f.property.aestronglyMeasurable measurable_fst.aemeasurable).mp h

theorem finiteWeilCanonicalRawCoupling_snd_integrable (r k : ℕ)
    (π : finiteWeilCanonicalRawCouplingSpace r k) (f : {f : ℝ → ℝ // Continuous f}) :
    Integrable (fun p : ℝ × ℝ => f.val p.2) π.val := by
  have h : Integrable f.val (π.val.map Prod.snd) := by
    rw [π.property.2, finiteWeilCanonicalRawCorrectionLaw]
    exact finiteWeilCanonicalObservableLaw_integrable r k _ _
  exact (integrable_map_measure f.property.aestronglyMeasurable measurable_snd.aemeasurable).mp h

theorem finiteWeilCanonicalRawCoupling_cost_integrable (r k : ℕ)
    (π : finiteWeilCanonicalRawCouplingSpace r k) :
    Integrable (fun p : ℝ × ℝ => dist p.1 p.2) π.val := by
  have h1 := finiteWeilCanonicalRawCoupling_fst_integrable r k π ⟨id, continuous_id⟩
  have h2 := finiteWeilCanonicalRawCoupling_snd_integrable r k π ⟨id, continuous_id⟩
  have h : Integrable (fun p : ℝ × ℝ => |p.1 - p.2|) π.val := (h1.sub h2).abs
  simpa only [Real.dist_eq] using h

theorem finiteWeilCanonicalRawLipschitz_le_coupling_cost (r k : ℕ)
    (π : finiteWeilCanonicalRawCouplingSpace r k) (f : {f : ℝ → ℝ // LipschitzWith 1 f}) :
    (∫ x, f.val x ∂(finiteWeilCanonicalRawIndexLaw r k : Measure ℝ)) -
      (∫ x, f.val x ∂(finiteWeilCanonicalRawCorrectionLaw r k : Measure ℝ)) ≤
        ∫ p, dist p.1 p.2 ∂π.val := by
  have h1 := finiteWeilCanonicalRawCoupling_fst_integrable r k π ⟨f.val, f.property.continuous⟩
  have h2 := finiteWeilCanonicalRawCoupling_snd_integrable r k π ⟨f.val, f.property.continuous⟩
  rw [← π.property.integral_fst f.property.continuous,
    ← π.property.integral_snd f.property.continuous, ← integral_sub h1 h2]
  apply integral_mono (h1.sub h2) (finiteWeilCanonicalRawCoupling_cost_integrable r k π)
  intro p
  have h := f.property.dist_le_mul p.1 p.2
  rw [NNReal.coe_one, one_mul, Real.dist_eq] at h
  exact (le_abs_self _).trans h

theorem finiteWeilCanonicalRawLipschitzDual_le_coupling_cost (r k : ℕ)
    (π : finiteWeilCanonicalRawCouplingSpace r k) :
    finiteWeilCanonicalRawLipschitzDual r k ≤ ∫ p, dist p.1 p.2 ∂π.val := by
  letI : Nonempty {f : ℝ → ℝ // LipschitzWith 1 f} :=
    ⟨⟨fun _ => 0, (LipschitzWith.const 0).weaken zero_le_one⟩⟩
  unfold finiteWeilCanonicalRawLipschitzDual lipschitzDual
  exact ciSup_le fun f => finiteWeilCanonicalRawLipschitz_le_coupling_cost r k π f

theorem finiteWeilCanonicalRawLipschitzDual_le_wasserstein (r k : ℕ) :
    finiteWeilCanonicalRawLipschitzDual r k ≤ finiteWeilCanonicalRawWasserstein r k := by
  letI : Nonempty (finiteWeilCanonicalRawCouplingSpace r k) :=
    ⟨⟨(finiteWeilCanonicalRawCoupling r k : Measure (ℝ × ℝ)),
      finiteWeilCanonicalRawCoupling_isCoupling r k⟩⟩
  change finiteWeilCanonicalRawLipschitzDual r k ≤
    ⨅ π : finiteWeilCanonicalRawCouplingSpace r k, ∫ p, dist p.1 p.2 ∂π.val
  exact le_ciInf fun π => finiteWeilCanonicalRawLipschitzDual_le_coupling_cost r k π

end RHTower
