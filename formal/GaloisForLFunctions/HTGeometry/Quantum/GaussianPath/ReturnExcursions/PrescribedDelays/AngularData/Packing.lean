import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.IsolatedDilations

/-! # Disjoint Gaussian dilations with the direction held fixed -/

open Set MeasureTheory ProbabilityTheory Real Finset
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.PrescribedDelays
open PrescribedTimes ShortWindows
noncomputable section

/-- A measurable event on directions localizes the entire packing
bound. Choosing separate observations on disjoint angular events thus
charges each event only in proportion to its Gaussian mass. -/
theorem angular_isolated_mass {ι : Type*} [Fintype ι] {m : ℕ} (a : Fin m → ℝ)
    (E D : Set (ι → ℝ)) (hE : MeasurableSet E) (hD : MeasurableSet D)
    (hdir : ∀ x (u : ℝ), 0<u → u • x ∈ D → x ∈ D)
    (ha : ∀ i, 1 ≤ a i) (hd : ∀ i, (Fintype.card ι:ℝ)*(a i-1) ≤ 1) :
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    (m:ℝ)*μ.real (isolated a E ∩ D) ≤ exp 1*μ.real D := by
  classical
  intro μ
  let Z := isolated a E ∩ D
  let V (i : Fin m) := (fun x : ι → ℝ => a i • x) ⁻¹' Z
  have hZ : MeasurableSet Z := (measurable_isolated a hE).inter hD
  have hV (i : Fin m) : MeasurableSet (V i) := hZ.preimage (measurable_id.const_smul (a i))
  have hp (i : Fin m) := zero_lt_one.trans_le (ha i)
  have hdis : Pairwise (fun i j => Disjoint (V i) (V j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hi : a i • x ∈ isolated a E := hx.1
    have hj : a j • x ∈ isolated a E := hy.1
    have hno := mem_iInter.mp (mem_iInter.mp hi.2 i) (⟨j,hij.symm⟩ : {v : Fin m // v≠i})
    change (a j/a i) • (a i • x) ∉ E at hno
    rw [smul_smul,div_mul_cancel₀ _ (hp i).ne'] at hno
    exact hno hj.1
  have hcover : (⋃ i, V i) ⊆ D := by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact hdir x _ (hp i) hi.2
  have he (i : Fin m) : μ.real Z ≤ exp 1*μ.real (V i) := by
    apply (gaussian_dilation_comparison (ha i) Z hZ).trans
    apply mul_le_mul_of_nonneg_right _ measureReal_nonneg
    have hu := Real.add_one_le_exp (a i-1)
    rw [sub_add_cancel] at hu
    apply (pow_le_pow_left₀ (hp i).le hu _).trans
    rw [←Real.exp_nat_mul]
    exact exp_le_exp.mpr (hd i)
  have h := sum_le_sum (s:=univ) fun i _ => he i
  rw [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,←mul_sum,
    ←measureReal_iUnion_fintype hdis hV (fun _ => measure_ne_top _ _)] at h
  exact h.trans (mul_le_mul_of_nonneg_left (measureReal_mono hcover) (exp_pos _).le)

#print axioms angular_isolated_mass
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.PrescribedDelays
