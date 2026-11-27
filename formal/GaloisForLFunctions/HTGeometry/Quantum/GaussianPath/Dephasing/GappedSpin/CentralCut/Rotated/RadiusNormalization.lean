import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Rotated.JointSurvival
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.FixedRadius

/-! # First-excursion survival after fixing the root-mean-square coupling -/

open Set Filter MeasureTheory ProbabilityTheory Real Finset
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
open PrescribedTimes WeakBonds AccuracyScales.TenthPlateau
noncomputable section

/-- If all physical coefficients have magnitude at least one hundredth,
setting the root-mean-square coefficient to one speeds the Hamiltonian
up by at most one hundred. -/
private theorem rms_le_hundred_norm {n : ℕ} {x : PrefixIndex n → ℝ}
    (hx : x ∈ allCoordStrongEvent n (1/100)) :
    sqrt (Fintype.card (PrefixIndex n) : ℝ) ≤ 100*coefficientNorm x := by
  have hb : (Fintype.card (PrefixIndex n):ℝ)*(1/100:ℝ)^2 ≤ coefficientNorm x^2 := by
    change _ ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (PrefixIndex n))‖^2
    rw [EuclideanSpace.norm_sq_eq]
    have h := sum_le_sum (s:=Finset.univ) (fun (i : PrefixIndex n) _ =>
      pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/100) (hx i) 2)
    simpa only [sum_const,card_univ,nsmul_eq_mul,Real.norm_eq_abs] using h
  have hn : 0 ≤ coefficientNorm x := norm_nonneg _
  apply (sq_le_sq₀ (sqrt_nonneg _) (mul_nonneg (by norm_num) hn)).mp
  rw [sq_sqrt (Nat.cast_nonneg _)]
  nlinarith only [hb]

/-- On the same draw, simultaneously for every fixed radius through
unit root-mean-square strength, the onset and every half-budget wait
retain the uniform seventh-power lower tail. -/
theorem rms_first_excursion :
    ∃ C > (0:ℝ), ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let K := n+2
      let P := nearHilbertContinuousCircuitBudget K
      let μ := Measure.pi (fun _ : PrefixIndex n => gaussianReal 0 1)
      let J := fun (x : PrefixIndex n → ℝ) (T : ℝ) =>
        T < crossingOrigin n P (9/80) x ∧ ∀ s ≤ P/2, T < crossingWait n P s x
      ∀ T ≥ (1:ℝ), ∃ E : Set (PrefixIndex n → ℝ), MeasurableSet E ∧
        exp (-C*(K:ℝ)^2) ≤ (100*T)^7*μ.real E ∧
        ∀ x ∈ E, x ∈ allCoordStrongEvent n (1/100) ∧ J x T ∧
          ∀ r ∈ Ioc (0:ℝ) (sqrt (Fintype.card (PrefixIndex n):ℝ)), J (atRadius r x) T := by
  obtain ⟨C,hC,hfloor⟩ := all_strong_first_excursion
  refine ⟨C,hC,?_⟩
  filter_upwards [hfloor] with k hb
  intro n K P μ J T hT
  have hbig : 1 ≤ 100*T := by linarith only [hT]
  let E := {x | x ∈ allCoordStrongEvent n (1/100) ∧ J x (100*T)}
  have hstrong : MeasurableSet (allCoordStrongEvent n (1/100)) := by
    simp only [allCoordStrongEvent,setOf_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le measurable_const (measurable_pi_apply i).abs
  have hwait : MeasurableSet {x | ∀ s ≤ P/2, 100*T < crossingWait n P s x} := by
    simp only [setOf_forall]
    exact MeasurableSet.iInter fun s => MeasurableSet.iInter fun _ =>
      measurableSet_lt measurable_const (measurable_crossingWait n P s)
  refine ⟨E,hstrong.inter ((measurableSet_lt measurable_const (measurable_crossingOrigin ..)).inter hwait),
    hb (100*T) hbig,?_⟩
  intro x hx
  have hxS : x ∈ allCoordStrongEvent n (1/100) := hx.1
  have hT' : T ≤ 100*T := by linarith only [hT]
  refine ⟨hxS,⟨hT'.trans_lt hx.2.1,fun j hj => hT'.trans_lt (hx.2.2 j hj)⟩,?_⟩
  intro r hr
  have hrnorm := hr.2.trans (rms_le_hundred_norm hxS)
  have hn : 0 < coefficientNorm x := by linarith only [hr.1,hrnorm]
  let q := r/coefficientNorm x
  have hq : 0 < q := div_pos hr.1 hn
  have hq' : q ≤ 100 := (div_le_iff₀ hn).mpr hrnorm
  have hqT := mul_le_mul_of_nonneg_right hq' (zero_le_one.trans hT)
  constructor
  · apply (mul_lt_mul_iff_right₀ hq).mp
    rw [show atRadius r x=q • x from rfl,smul_crossingOrigin _ _ _ hq]
    exact hqT.trans_lt hx.2.1
  · intro s hs
    apply (mul_lt_mul_iff_right₀ hq).mp
    rw [show atRadius r x=q • x from rfl,smul_crossingWait _ _ _ hq]
    exact hqT.trans_lt (hx.2.2 s hs)

#print axioms rms_first_excursion
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
