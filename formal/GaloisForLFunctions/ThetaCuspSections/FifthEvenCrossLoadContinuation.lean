import GaloisForLFunctions.ThetaCuspSections.FifthEvenCoupledEndpointGap
import GaloisForLFunctions.ThetaCuspSections.FifthEvenCoherentRepair
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterCompensationSign

/-!
# Positive neighborhoods and tail of the fifth cross-load

Continuity extends the two strict endpoint forms to neighborhoods. The trace
complement of a positive two-dimensional matrix is positive, so the scalar
coupled-load tail bounds the same explicit cross-load from below.
-/

noncomputable section
open Matrix Filter Topology MeasureTheory Set RHTower RHTower.ThetaCuspGaussianLimit
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.ThetaCuspSections.EvenFiveEndpoint

/-- The complete fifth source with the explicit positive cross-load. -/
def crossRepair (x : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  nativeShiftedMatrix 5 0 x+thetaCuspCenterCompensationSource x • crossLoad paidSevenSchur

private theorem crossRepair_hermitian (x : ℝ) : (crossRepair x).IsHermitian := by
  apply Matrix.IsHermitian.add
  · rw [Matrix.IsHermitian]
    ext i j
    simp [nativeShiftedMatrix,add_comm]
  · exact (crossCoefficient_posDef.posSemidef.conjTranspose_mul_mul_same loadMap).isHermitian.smul (by rfl)

private theorem crossRepair_continuous : Continuous crossRepair := by
  have hΦ : Continuous thetaCuspFullSource := thetaCuspSchwartzReal.continuous
  have hd : Continuous (deriv thetaCuspFullSource) :=
    (SchwartzMap.derivCLM ℝ ℝ thetaCuspSchwartzReal).continuous
  have hj := continuous_thetaCuspNativeReflectionJet
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold crossRepair nativeShiftedMatrix thetaCuspCenterCompensationSource
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  fun_prop

private theorem crossRepair_near {y : ℝ} (hy : (crossRepair y).PosDef) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x-y| < δ → (crossRepair x).PosDef := by
  have ht (i j : Fin 5) : Tendsto (fun x => crossRepair x i j)
      (𝓝 y) (𝓝 (crossRepair y i j)) :=
    ((continuous_apply j).comp ((continuous_apply i).comp crossRepair_continuous)).continuousAt.tendsto
  have hp := posDef_eventually_of_tendsto hy
    (Filter.Eventually.of_forall crossRepair_hermitian) ht
  obtain ⟨δ,hδ,hb⟩ := Metric.eventually_nhds_iff.mp hp
  exact ⟨δ,hδ,fun x hx => hb (by simpa [Real.dist_eq] using hx)⟩

/-- One fixed cross-load is positive on neighborhoods of both complete-source endpoints. -/
theorem crossRepair_endpoint_neighborhoods :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ,
      (|x| < δ ∨ |x-EvenFiveBoundary.witnessCenter| < δ) → (crossRepair x).PosDef := by
  obtain ⟨δ₀,hδ₀,hzero⟩ := crossRepair_near origin_cross_load_posDef
  obtain ⟨δ₇,hδ₇,hseven⟩ := crossRepair_near scaleSeven_cross_load_posDef
  refine ⟨min δ₀ δ₇,lt_min hδ₀ hδ₇,fun x hx => ?_⟩
  rcases hx with hx | hx
  · exact hzero x (by simpa only [sub_zero] using hx.trans_le (min_le_left _ _))
  · exact hseven x (hx.trans_le (min_le_right _ _))

private def traceCoefficient : ℝ := paidSevenSchur 0 0+paidSevenSchur 1 1

/-- In two dimensions the trace complement is a rotation of the positive form. -/
private theorem traceComplement_posSemidef :
    (traceCoefficient • (1 : Matrix (Fin 2) (Fin 2) ℝ)-paidSevenSchur).PosSemidef := by
  let J : Matrix (Fin 2) (Fin 2) ℝ := !![0,-1;1,0]
  have hs : paidSevenSchur 1 0=paidSevenSchur 0 1 := by
    have h := congrFun (congrFun paidSevenSchur_hermitian 0) 1
    simpa only [Matrix.conjTranspose_apply,star_trivial] using h
  have he : traceCoefficient • (1 : Matrix (Fin 2) (Fin 2) ℝ)-paidSevenSchur =
      Jᴴ*paidSevenSchur*J := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [J,traceCoefficient,Matrix.mul_apply,Matrix.conjTranspose_apply,
        Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply,Fin.sum_univ_two,hs]
  rw [he]
  exact crossCoefficient_posDef.posSemidef.conjTranspose_mul_mul_same J

private theorem crossLoad_traceComplement :
    crossLoad (traceCoefficient • (1 : Matrix (Fin 2) (Fin 2) ℝ)-paidSevenSchur) =
      traceCoefficient • EvenFiveCoherent.load-crossLoad paidSevenSchur := by
  simp only [crossLoad,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,
    Matrix.smul_mul,Matrix.mul_one,EvenFiveCoherent.load,loadMap,EvenFiveCoherent.loadRows]

/-- The explicit cross-load preserves positivity on a cofinal source ray. -/
theorem crossRepair_posDef_eventually : ∀ᶠ x : ℝ in atTop, (crossRepair x).PosDef := by
  obtain ⟨τ,hτ,hs⟩ := exists_thetaCuspCenterCompensationSource_transition
  have hload : (crossLoad (traceCoefficient • 1-paidSevenSchur)).PosSemidef :=
    traceComplement_posSemidef.conjTranspose_mul_mul_same loadMap
  filter_upwards [EvenFiveCoherent.repair_posDef_eventually traceCoefficient,
    eventually_gt_atTop τ] with x hx hxτ
  have hg := (hs x (hτ.le.trans hxτ.le)).2.2.mpr hxτ
  have h := hx.add_posSemidef (hload.smul (neg_nonneg.mpr hg.le))
  have he : EvenFiveCoherent.repair traceCoefficient x+
      (-thetaCuspCenterCompensationSource x) •
        crossLoad (traceCoefficient • (1 : Matrix (Fin 2) (Fin 2) ℝ)-paidSevenSchur) =
      crossRepair x := by
    rw [crossLoad_traceComplement]
    ext i j
    simp only [crossRepair,EvenFiveCoherent.repair,Matrix.add_apply,Matrix.sub_apply,
      Matrix.smul_apply,smul_eq_mul]
    ring
  rwa [he] at h

/-- Only a compact set away from both positive endpoint neighborhoods remains. -/
theorem crossRepair_compact_gap :
    ∃ δ R : ℝ, 0 < δ ∧ δ ≤ R ∧ ∀ x : ℝ, 0 ≤ x →
      (x < δ ∨ |x-EvenFiveBoundary.witnessCenter| < δ ∨ R ≤ x) →
      (crossRepair x).PosDef := by
  obtain ⟨δ,hδ,hloc⟩ := crossRepair_endpoint_neighborhoods
  obtain ⟨R,htail⟩ := Filter.eventually_atTop.mp crossRepair_posDef_eventually
  refine ⟨δ,max R δ,hδ,le_max_right _ _,fun x hx h => ?_⟩
  rcases h with h | h | h
  · exact hloc x (Or.inl (by simpa only [abs_of_nonneg hx] using h))
  · exact hloc x (Or.inr h)
  · exact htail x ((le_max_left _ _).trans h)

end GaloisForLFunctions.ThetaCuspSections.EvenFiveEndpoint
