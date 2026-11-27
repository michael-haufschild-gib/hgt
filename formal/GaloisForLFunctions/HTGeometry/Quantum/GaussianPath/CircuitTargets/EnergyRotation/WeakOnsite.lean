import GaloisForLFunctions.HTGeometry.Quantum.GaussianPathCoefficientMass
import GaloisForLFunctions.HTGeometry.AtomlessProbabilityLaws

/-! # Few sites have an arbitrarily weak onsite coordinate -/
open MeasureTheory ProbabilityTheory Filter Finset Metric
open scoped ENNReal Topology
namespace GaloisForLFunctions.HTGeometry.EnergyRotation
noncomputable section
open private gaussian_direction_slln from GaloisForLFunctions.HTGeometry.Quantum.GaussianPathCoefficientMass

/-- At any prescribed density, there is a deterministic positive field
threshold such that every sufficiently long prefix has fewer weak sites.
At the other sites all three Cartesian components exceed the threshold. -/
theorem weak_onsite_density {η : ℝ} (hη : 0 < η) :
    ∃ r>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let u := pathPauliDisorderShell ω n
      ((univ.filter fun i : Fin (n+2) => ∃ a : Fin 3, |u (.inl (i,a))| ≤ r).card:ℝ) ≤ η*(n+2:ℕ) := by
  classical
  let ν := gaussianReal 0 1
  let μ : ProbabilityMeasure ℝ := ⟨ν,inferInstance⟩
  have hsmall : 0 < ENNReal.ofReal (η/4) := ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨r,hr,hμ⟩ := atomless_exists_small_closedBall μ (nullSingletonClass_gaussianReal one_ne_zero) 0 hsmall
  let B := closedBall (0:ℝ) r
  have hB : MeasurableSet B := isClosed_closedBall.measurableSet
  have hm : ν.real B < η/4 := by
    simpa only [Measure.real,ENNReal.toReal_ofReal (by positivity : 0 ≤ η/4)] using
      (ENNReal.toReal_lt_toReal (measure_ne_top ν B) ENNReal.ofReal_ne_top).mpr hμ
  let f : ℝ → ℝ := B.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hB
  have hfi : Integrable f ν := (integrable_const 1).indicator hB
  have hmean : (∫ x, f x ∂ν)=ν.real B := by
    rw [show f=B.indicator (fun _ => (1:ℝ)) from rfl,integral_indicator hB,
      setIntegral_const,smul_eq_mul,mul_one]
  have hall (a : Fin 3) := gaussian_direction_slln (.inl a) f hf hfi
  refine ⟨r,hr,?_⟩
  filter_upwards [ae_all_iff.mpr hall] with ω hw
  have hev (a : Fin 3) := (hw a).eventually_lt_const (hmean.trans_lt hm)
  have hN := (tendsto_add_atTop_nat 2).eventually (Filter.eventually_all.mpr hev)
  filter_upwards [hN] with n hn
  intro u
  let S := univ.filter fun i : Fin (n+2) => ∃ a : Fin 3, |u (.inl (i,a))| ≤ r
  have hpos : (0:ℝ)<(n+2:ℕ) := by positivity
  have hcount : (S.card:ℝ) ≤ ∑ i : Fin (n+2), ∑ a : Fin 3, f (u (.inl (i,a))) := by
    have hval (i : Fin (n+2)) (hi : i ∈ S) : (1:ℝ) ≤ ∑ a : Fin 3, f (u (.inl (i,a))) := by
      obtain ⟨a,ha⟩ := (mem_filter.mp hi).2
      have hm' : u (.inl (i,a)) ∈ B := by simpa only [B,mem_closedBall,Real.dist_eq,sub_zero] using ha
      have h := single_le_sum (f:=fun j : Fin 3 => f (u (.inl (i,j))))
        (fun j _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _) (mem_univ a)
      simpa only [f,Set.indicator_of_mem hm'] using h
    simpa only [sum_const,nsmul_eq_mul,mul_one] using
      (sum_le_sum hval).trans (sum_le_sum_of_subset_of_nonneg (subset_univ S)
        (fun _ _ _ => sum_nonneg fun _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _))
  apply hcount.trans
  rw [sum_comm]
  have hsum (a : Fin 3) : (∑ i : Fin (n+2), f (u (.inl (i,a)))) ≤ (η/4)*(n+2:ℕ) := by
    change (∑ i : Fin (n+2), f (ω (i.val,.inl a))) ≤ _
    rw [Fin.sum_univ_eq_sum_range (fun i => f (ω (i,.inl a))) (n+2)]
    exact ((div_lt_iff₀ hpos).mp (hn a)).le
  have h := sum_le_sum (s:=univ) fun a _ => hsum a
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at h
  linarith only [h,mul_nonneg hη.le hpos.le]

#print axioms weak_onsite_density
end
end GaloisForLFunctions.HTGeometry.EnergyRotation
