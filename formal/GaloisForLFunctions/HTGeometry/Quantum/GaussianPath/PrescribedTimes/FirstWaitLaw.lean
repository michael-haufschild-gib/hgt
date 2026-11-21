import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.CrossingOrigin
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.GaussianDilation
import GaloisForLFunctions.HTGeometry.GaussianAngularPolarDisintegrationLaw

/-! # Joint law of the first robust crossing and its subsequent circuit return -/
open MeasureTheory ProbabilityTheory Set Matrix Metric
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes
noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- The self-adjoint prefix generator in its independent coefficient coordinates. -/
def prefixGenerator (n : ℕ) (x : PrefixIndex n → ℝ) : selfAdjoint (Reg (n+2)) :=
  ⟨numberedGenerator n x,by
    let u : PathShell n := WithLp.toLp 2 (fun l => x ((pathCoeffEquiv n).symm l))
    have he : numberedGenerator n x = pathHamiltonian u := by
      simpa only [u,WithLp.ofLp_toLp,Equiv.symm_apply_apply] using numberedGenerator_shell u
    rw [he]
    exact isSelfAdjoint_pathHamiltonian u⟩

/-- Elapsed time from the first j-gate crossing at distance 9/80
to the first s-gate approximation at error 1/10. -/
def crossingWait (n j s : ℕ) (x : PrefixIndex n → ℝ) : ℝ :=
  let σ := crossingOrigin n j (9/80) x
  firstCircuitVisit (prefixGenerator n x) s σ - σ

theorem crossingWait_le_iff (n j s : ℕ) (x : PrefixIndex n → ℝ) (b : ℝ) :
    crossingWait n j s x ≤ b ↔
      ∃ t ∈ Icc (crossingOrigin n j (9/80) x) (crossingOrigin n j (9/80) x+b),
        pathGateDistance n s x t ≤ 1/10 := by
  let σ := crossingOrigin n j (9/80) x
  let H := prefixGenerator n x
  have he : firstCircuitVisit H s σ ≤ σ+b ↔ σ ∈ circuitWindowHits H.val s b := by
    rw [circuitWindowHits_eq_firstVisit]
    rfl
  change firstCircuitVisit H s σ-σ ≤ b ↔ _
  rw [sub_le_iff_le_add',he]
  change (∃ t ∈ Icc σ (σ+b), HasProjectiveCircuitApproximation (n+2) (1/10:ℝ) s (unitaryEvolution H.val t)) ↔ _
  simp only [hasProjectiveCircuitApproximation_iff_infDist]
  rfl

/-- Enlarging the return budget can only shorten the actual waiting time. -/
theorem crossingWait_antitone {n j s r : ℕ} (hs : s ≤ r) (x : PrefixIndex n → ℝ) :
    crossingWait n j r x ≤ crossingWait n j s x := by
  apply (crossingWait_le_iff _ _ _ _ _).mpr
  obtain ⟨t,ht,hd⟩ := (crossingWait_le_iff n j s x _).mp le_rfl
  obtain ⟨z,hz,C,hC,he⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ s _).mpr hd
  exact ⟨t,ht,(hasProjectiveCircuitApproximation_iff_infDist _ r _).mp ⟨z,hz,C,hC.trans hs,he⟩⟩

theorem measurable_crossingWait (n j s : ℕ) : Measurable (crossingWait n j s) := by
  apply measurable_of_Iic
  intro b
  have he : crossingWait n j s ⁻¹' Iic b =
      {x | ∃ t ∈ Icc (crossingOrigin n j (9/80) x) (crossingOrigin n j (9/80) x+b),
        pathGateDistance n s x t ≤ 1/10} := Set.ext fun x => crossingWait_le_iff n j s x b
  rw [he]
  simpa only [add_zero] using measurable_shifted_window n s _ (measurable_crossingOrigin n j (9/80)) 0 b

theorem smul_crossingWait (n j s : ℕ) {a : ℝ} (ha : 0 < a) (x : PrefixIndex n → ℝ) :
    a*crossingWait n j s (a • x) = crossingWait n j s x := by
  have scale (b : ℝ) : crossingWait n j s (a • x) ≤ b ↔ crossingWait n j s x ≤ a*b := by
    rw [crossingWait_le_iff,crossingWait_le_iff]
    simpa only [mul_zero,add_zero] using crossing_window_dilate n j s (9/80) (1/10) 0 b ha x
  have h := (scale (crossingWait n j s x/a)).mpr
    (by rw [mul_comm a,div_mul_cancel₀ _ ha.ne'])
  exact le_antisymm ((mul_comm a _).trans_le ((le_div_iff₀ ha).mp h))
    ((scale _).mp le_rfl)

/-- Exact joint distribution. On the unit coefficient sphere retain the
first crossing and the actual first wait. Divide both by the same independent
chi radius to recover their Gaussian-prefix law. -/
theorem gaussian_joint_first_passage_polar (n j s : ℕ) (f : ℝ → ℝ → ℝ) :
    let m := Fintype.card (ChainLabel (n+2))
    let σ := crossingOrigin n j (9/80)
    let Δ := crossingWait n j s
    (∫ x, f (σ x) (Δ x) ∂Measure.pi (fun _ : PrefixIndex n => gaussianReal 0 1)) =
      ∫ p : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 × Ioi (0:ℝ),
        f (σ p.1.val.ofLp/p.2.val) (Δ p.1.val.ofLp/p.2.val)
        ∂((gaussianAngularMeasure m).prod (gaussianRadiusMeasure m)) := by
  intro m σ Δ
  have hi := ((pathCoeffEquiv n).symm (Sum.inl (0,0))).isLt
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) hi
  let F (z : EuclideanSpace ℝ (Fin m)) := f (σ z.ofLp) (Δ z.ofLp)
  have he : (∫ x, f (σ x) (Δ x) ∂Measure.pi (fun _ : PrefixIndex n => gaussianReal 0 1)) =
      ∫ z, F z ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
    rw [←map_pi_eq_stdGaussian,←MeasurableEquiv.coe_toLp,integral_map_equiv]
    rfl
  rw [he,integral_stdGaussian_independent_polar hm F]
  apply integral_congr_ae
  filter_upwards with p
  let r := p.2.val
  let x := p.1.val.ofLp
  have hσ := smul_crossingOrigin n j (9/80) p.2.property x
  have hΔ := smul_crossingWait n j s p.2.property x
  change f (σ (r • x)) (Δ (r • x)) = _
  congr 1
  · exact (eq_div_iff p.2.property.ne').mpr ((mul_comm _ r).trans hσ)
  · exact (eq_div_iff p.2.property.ne').mpr ((mul_comm _ r).trans hΔ)

/-- For simultaneous early onset and late return the chi radius must clear
the onset threshold and stay below the return threshold on the same angular
sample. An empty interval of permitted radii contributes zero mass. -/
theorem gaussian_early_onset_late_return_probability (n j s : ℕ) (A B : ℝ) :
    let m := Fintype.card (ChainLabel (n+2))
    let σ := crossingOrigin n j (9/80)
    let Δ := crossingWait n j s
    let μ := Measure.pi (fun _ : PrefixIndex n => gaussianReal 0 1)
    μ.real {x | σ x ≤ A ∧ B ≤ Δ x} =
      ((gaussianAngularMeasure m).prod (gaussianRadiusMeasure m)).real
        {p : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 × Ioi (0:ℝ) |
          σ p.1.val.ofLp ≤ A*p.2.val ∧ B*p.2.val ≤ Δ p.1.val.ofLp} := by
  classical
  intro m σ Δ μ
  let Ω := sphere (0 : EuclideanSpace ℝ (Fin m)) 1 × Ioi (0:ℝ)
  let x := fun (p : Ω) => p.1.val.ofLp
  let r := fun (p : Ω) => p.2.val
  have hx : Measurable x :=
    (MeasurableEquiv.toLp 2 (Fin m → ℝ)).symm.measurable.comp (measurable_subtype_coe.comp measurable_fst)
  have hr : Measurable r := measurable_subtype_coe.comp measurable_snd
  have hσ := measurable_crossingOrigin n j (9/80)
  have hΔ := measurable_crossingWait n j s
  have hS : MeasurableSet {p : Ω | σ (x p) ≤ A*r p ∧ B*r p ≤ Δ (x p)} :=
    (measurableSet_le (hσ.comp hx) (hr.const_mul A)).inter
      (measurableSet_le (hr.const_mul B) (hΔ.comp hx))
  have hE : MeasurableSet {y | σ y ≤ A ∧ B ≤ Δ y} :=
    (measurableSet_le hσ measurable_const).inter (measurableSet_le measurable_const hΔ)
  rw [←integral_indicator_one hE,←integral_indicator_one hS]
  let f (u v : ℝ) := if u ≤ A ∧ B ≤ v then (1:ℝ) else 0
  have he : {y | σ y ≤ A ∧ B ≤ Δ y}.indicator (1 : (PrefixIndex n → ℝ) → ℝ) =
      fun y => f (σ y) (Δ y) := by
    funext y
    by_cases hy : σ y ≤ A ∧ B ≤ Δ y <;> simp [f,hy]
  rw [he]
  rw [gaussian_joint_first_passage_polar n j s f]
  apply integral_congr_ae
  filter_upwards with p
  have hp : 0 < r p := p.2.property
  change f (σ (x p)/r p) (Δ (x p)/r p) = _
  by_cases hy : σ (x p) ≤ A*r p ∧ B*r p ≤ Δ (x p)
    <;> simp [f,div_le_iff₀ hp,le_div_iff₀ hp,hy]

/-- A common dilation gives a finite-dimensional lower tail bound at *every*
time scale. It applies jointly to the two stopping times, including elapsed
time from the distinguished first crossing. -/
theorem gaussian_joint_first_passage_tail (n j s : ℕ) (u t : ℝ) {a : ℝ} (ha : 1 ≤ a) :
    let μ := Measure.pi (fun _ : PrefixIndex n => gaussianReal 0 1)
    let σ := crossingOrigin n j (9/80)
    let Δ := crossingWait n j s
    μ.real {x | u < σ x ∧ t < Δ x} ≤ a^(Fintype.card (ChainLabel (n+2))) *
      μ.real {x | a*u < σ x ∧ a*t < Δ x} := by
  intro μ σ Δ
  let E := {x | u < σ x ∧ t < Δ x}
  have hm : MeasurableSet E := (measurableSet_lt measurable_const (measurable_crossingOrigin _ _ _)).inter
    (measurableSet_lt measurable_const (measurable_crossingWait _ _ _))
  have h := gaussian_dilation_comparison ha E hm
  have hp := zero_lt_one.trans_le ha
  have he : (fun x : PrefixIndex n → ℝ => a • x) ⁻¹' E = {x | a*u < σ x ∧ a*t < Δ x} := by
    ext x
    change (u < σ (a • x) ∧ t < Δ (a • x)) ↔ (a*u < crossingOrigin n j (9/80) x ∧ a*t < crossingWait n j s x)
    rw [←smul_crossingOrigin n j (9/80) hp x,←smul_crossingWait n j s hp x]
    exact and_congr (mul_lt_mul_iff_right₀ hp).symm (mul_lt_mul_iff_right₀ hp).symm
  simpa only [he,Fintype.card_fin] using h

#print axioms gaussian_joint_first_passage_polar
#print axioms gaussian_early_onset_late_return_probability
#print axioms gaussian_joint_first_passage_tail
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes
