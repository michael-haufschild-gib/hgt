import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.JointHaar
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ZeroGateExactOccupation

/-! # Simultaneous empty-circuit returns after perturbing one boundary field -/
open Filter Topology MeasureTheory Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
noncomputable section
private abbrev Register (n : ℕ) := Matrix (Fin n→Bool) (Fin n→Bool) ℂ
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩

/-- Joint Haar phases give the product of the exact empty-circuit occupations
at any pair of tolerances and from every observation origin. -/
theorem empty_return_product {n : ℕ} (H K : selfAdjoint (Register n))
    (r s : Icc (0:ℝ) 1) (a : ℝ)
    (h : ∀ i j, let f := Sum.elim (projectiveFrequency (fun z => -H.2.isHermitian.eigenvalues z) i)
                  (projectiveFrequency (fun z => -K.2.isHermitian.eigenvalues z) j)
                Tendsto (clockPhaseWindowLaw f) atTop (𝓝 (finiteTorusHaarProbabilityMeasure _))) :
    Tendsto (fun T => volume.real ((zeroGateReturnSet H r ∩ zeroGateReturnSet K s) ∩ Icc a T)/(T-a))
      atTop (𝓝 (zeroGateArcOccupationPolynomial (2^n) r * zeroGateArcOccupationPolynomial (2^n) s)) := by
  classical
  let i : Fin n→Bool := fun _ => false
  let I := {j : Fin n→Bool // j≠i}
  letI : Fintype I := inferInstanceAs (Fintype {j : Fin n→Bool // j≠i})
  let split := MeasurableEquiv.sumPiEquivProdPi (fun _ : I⊕I => UnitAddCircle)
  have hc : Continuous split := (Homeomorph.sumPiEquivProdPi I I (fun _ => UnitAddCircle)).continuous
  have hp : MeasurePreserving split volume volume := volume_measurePreserving_sumPiEquivProdPi _
  let X := relativeEnclosingUnitArc i (r:ℝ)
  let Y := relativeEnclosingUnitArc i (s:ℝ)
  let V := split ⁻¹' (X ×ˢ Y)
  have hXY : MeasurableSet (X ×ˢ Y) := (isClosed_relativeEnclosingUnitArc i r).measurableSet.prod
    (isClosed_relativeEnclosingUnitArc i s).measurableSet
  let f := Sum.elim (projectiveFrequency (fun z => -H.2.isHermitian.eigenvalues z) i)
    (projectiveFrequency (fun z => -K.2.isHermitian.eigenvalues z) i)
  have hset : zeroGateReturnSet H r ∩ zeroGateReturnSet K s=finiteClockPhasePoint f ⁻¹' V := by
    rw [zeroGateReturnSet_eq_preimage_full H i r,zeroGateReturnSet_eq_preimage_full K i s]
    rfl
  have hV : MeasurableSet V := hXY.preimage split.measurable
  have hx : volume (frontier X)=0 := volume_frontier_relativeEnclosingUnitArc i r
  have hy : volume (frontier Y)=0 := volume_frontier_relativeEnclosingUnitArc i s
  have hfront : MeasurableSet (frontier (X ×ˢ Y)) := by
    rw [frontier_prod_eq]
    exact (isClosed_closure.measurableSet.prod isClosed_frontier.measurableSet).union
      (isClosed_frontier.measurableSet.prod isClosed_closure.measurableSet)
  have hbd : volume (frontier V)=0 := by
    apply measure_mono_null (hc.frontier_preimage_subset _)
    rw [hp.measure_preimage hfront.nullMeasurableSet,frontier_prod_eq]
    apply measure_union_null
    · rw [Measure.volume_eq_prod,Measure.prod_prod,hy,mul_zero]
    · rw [Measure.volume_eq_prod,Measure.prod_prod,hx,zero_mul]
  have hmass : volume.real V=zeroGateArcOccupationPolynomial (2^n) r * zeroGateArcOccupationPolynomial (2^n) s := by
    change (volume (split ⁻¹' (X ×ˢ Y))).toReal=_
    rw [hp.measure_preimage hXY.nullMeasurableSet,Measure.volume_eq_prod,Measure.prod_prod,ENNReal.toReal_mul]
    exact congrArg₂ (·*·) (zeroGateFullArcMass_eq_exactPolynomial n r) (zeroGateFullArcMass_eq_exactPolynomial n s)
  have hnull : (finiteTorusHaarProbabilityMeasure (I⊕I) : Measure _) (frontier V)=0 := by
    rwa [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume]
  have he := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' (h i i) hnull
  rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume] at he
  have hav := (ENNReal.tendsto_toReal (measure_ne_top _ V)).comp he
  change Tendsto (fun T => (clockPhaseWindowLaw f T : Measure _).real V) atTop (𝓝 (volume.real V)) at hav
  rw [hmass] at hav
  apply tendsto_occupation_from_start _ (by rw [hset]; exact hV.preimage (finiteClockPhasePoint_continuous f).measurable)
  apply hav.congr
  intro T
  rw [clockPhaseWindowLaw,Measure.real,ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (finiteClockPhasePoint_continuous f).measurable hV,←hset]
  rfl

/-- For each prefix of one chain and all but countably many changes in a
single boundary field, the simultaneous return fraction factors exactly. -/
theorem gaussian_boundary_joint_empty_returns :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∃ B : Set ℝ, B.Countable ∧ ∀ t ∉ B,
      let H : selfAdjoint (Register (k+3)) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let K : selfAdjoint (Register (k+3)) := ⟨boundaryHamiltonian ω k t,(boundaryHermitian ω k t).isSelfAdjoint⟩
      ∀ (r s : Icc (0:ℝ) 1) (a : ℝ),
        Tendsto (fun T => volume.real ((zeroGateReturnSet H r ∩ zeroGateReturnSet K s) ∩ Icc a T)/(T-a))
          atTop (𝓝 (zeroGateArcOccupationPolynomial (2^(k+3)) r * zeroGateArcOccupationPolynomial (2^(k+3)) s)) := by
  filter_upwards [gaussian_boundary_joint_haar] with ω hω
  intro k
  obtain ⟨B,hB,hs⟩ := hω k
  exact ⟨B,hB,fun t ht r s a => empty_return_product _ _ r s a (hs t ht)⟩

/-- Among the reference orbit's empty-circuit times, the fraction also
empty for the perturbed orbit is exactly D x^(D−1), for every normalized
arc length 0<x≤1/2 and every observation origin. -/
theorem gaussian_boundary_conditional_empty_returns :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∃ B : Set ℝ, B.Countable ∧ ∀ t ∉ B,
      let H : selfAdjoint (Register (k+3)) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let K : selfAdjoint (Register (k+3)) := ⟨boundaryHamiltonian ω k t,(boundaryHermitian ω k t).isSelfAdjoint⟩
      ∀ (x : Icc (0:ℝ) (1/2)) (a : ℝ), 0<(x:ℝ) →
        Tendsto (fun T => volume.real ((zeroGateReturnSet H x ∩ zeroGateReturnSet K x) ∩ Icc a T)/
          volume.real (zeroGateReturnSet H x ∩ Icc a T)) atTop (𝓝 (zeroGateArcDensity (2^(k+3)) x)) := by
  filter_upwards [gaussian_boundary_joint_empty_returns,gaussian_path_all_prefixes_maximally_projective] with ω hω hm
  intro k
  obtain ⟨B,hB,hs⟩ := hω k
  refine ⟨B,hB,?_⟩
  intro t ht H K x a hx
  let r : Icc (0:ℝ) 1 := ⟨x,x.property.1,x.property.2.trans (by norm_num)⟩
  let i : Fin (k+3)→Bool := fun _ => false
  have hp : zeroGateArcOccupationPolynomial (2^(k+3)) r=zeroGateArcDensity (2^(k+3)) x := by
    rw [←zeroGateFullArcMass_eq_exactPolynomial]
    simpa only [zeroGateFullArcMass,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,r,i] using
      relativeUnitArcMass_eq_power i x
  have hn : zeroGateArcDensity (2^(k+3)) x≠0 :=
    mul_ne_zero (by positivity) (pow_ne_zero _ hx.ne')
  have hj := hs t ht r r a
  rw [hp] at hj
  have h := hj.div (maximallyProjective_zeroGateOccupation_from_start H (hm k) x a) hn
  rw [mul_div_cancel_right₀ _ hn] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop a] with T hT
  exact div_div_div_cancel_right₀ (sub_ne_zero.mpr hT.ne') _ _

#print axioms gaussian_boundary_joint_empty_returns
#print axioms gaussian_boundary_conditional_empty_returns
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
