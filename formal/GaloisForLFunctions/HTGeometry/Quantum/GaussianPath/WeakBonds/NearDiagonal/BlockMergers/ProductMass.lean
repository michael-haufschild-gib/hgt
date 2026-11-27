import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.GaussianSections

/-! # Probability of a separated tensor sum for two independent blocks -/
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
noncomputable section
variable {X ι I J : Type*} [MeasurableSpace X] [Fintype ι] [Fintype I] [Fintype J]

/-- Integrate the right-block section bound with the left sample fixed.
The favorable grid scale is allowed to change with both inputs. -/
theorem product_gap_mass (μ : Measure X) [IsProbabilityMeasure μ]
    (a : X→I→ℝ) (b : (ι→ℝ)→J→ℝ) (ha : ∀ i, Measurable fun x => a x i)
    (hb : ∀ i, Measurable fun x => b x i)
    (hf : ∀ c : ℝ, 0<c → ∀ x j, b (c • x) j=c*b x j) {g : ℝ} (hg : 0<g) :
    let N := Fintype.card ((I×J)×(I×J))+1
    let ν := Measure.pi fun _ : ι => gaussianReal 0 1
    let A := {x | ∀ i j, i≠j → g≤|a x i-a x j|}
    let B := {y | ∀ i j, i≠j → g≤|b y i-b y j|}
    let F := {p : X×(ι→ℝ) | ∀ u v : I×J, u≠v →
      g/(8*(N:ℝ)) ≤ |(a p.1 u.1+b p.2 u.2)-(a p.1 v.1+b p.2 v.2)|}
    μ.real A*ν.real B ≤ (N:ℝ)*2^(Fintype.card ι)*(μ.prod ν).real F := by
  intro N ν A B F
  let c : ℝ := N*2^(Fintype.card ι)
  have hc : 0≤c := by dsimp only [c]; positivity
  have hF : MeasurableSet F := by
    let M (u : I×J) := fun p : X×(ι→ℝ) => a p.1 u.1+b p.2 u.2
    have hm u : Measurable (M u) := ((ha _).comp measurable_fst).add ((hb _).comp measurable_snd)
    simp only [F,setOf_forall]
    exact MeasurableSet.iInter fun u => MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ =>
      measurableSet_le measurable_const (((hm u).sub (hm v)).abs)
  have hslice (x : X) (hx : x∈A) : ν B ≤ ENNReal.ofReal c*ν (Prod.mk x ⁻¹' F) := by
    have h := spectral_section_mass (a x) b hf B hg hx (fun _ hy => hy) hb
    change ν.real B ≤ c*ν.real (Prod.mk x ⁻¹' F) at h
    have h' := ENNReal.ofReal_le_ofReal h
    simpa only [measureReal_def,ENNReal.ofReal_mul hc,ENNReal.ofReal_toReal (measure_ne_top _ _)] using h'
  have hprod : μ A*ν B ≤ ENNReal.ofReal c*(μ.prod ν) F := calc
    _ = ∫⁻ _ in A, ν B ∂μ := by rw [setLIntegral_const,mul_comm]
    _ ≤ ∫⁻ x in A, ENNReal.ofReal c*ν (Prod.mk x ⁻¹' F) ∂μ :=
      setLIntegral_mono ((measurable_measure_prodMk_left hF).const_mul _) hslice
    _ ≤ ∫⁻ x, ENNReal.ofReal c*ν (Prod.mk x ⁻¹' F) ∂μ := lintegral_mono' Measure.restrict_le_self le_rfl
    _ = _ := by rw [lintegral_const_mul _ (measurable_measure_prodMk_left hF),Measure.prod_apply hF]
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hprod
  simpa only [measureReal_def,ENNReal.toReal_mul,ENNReal.toReal_ofReal hc,c] using h

#print axioms product_gap_mass
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
