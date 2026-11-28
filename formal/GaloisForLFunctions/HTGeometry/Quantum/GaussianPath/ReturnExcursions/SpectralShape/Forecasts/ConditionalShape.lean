import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.Forecasts.LocalDirections
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.Forecasts.Sections
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.Forecasts.PolynomialLine

/-! # Predicting the cubic shape after observing all but three physical couplings -/

open MeasureTheory ProbabilityTheory Set WithLp
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
open Dephasing.PairedFields
noncomputable section

theorem measurable_outside {n : ℕ} (e : Fin (n+1)) : Measurable (outside e) :=
  measurable_pi_lambda _ fun i =>
    (measurable_pi_apply i.val).comp (MeasurableEquiv.toLp 2 (Coeff n)).symm.measurable

private theorem outside_line {n : ℕ} (e : Fin (n+1)) {v : PathShell n} (hv : outside e v=0)
    (y : PathShell n) (t : ℝ) : outside e (y+t • v)=outside e y := by
  funext i
  have hi : v i.val=0 := congrFun hv i
  change y i.val+t*v i.val=y i.val
  rw [hi,mul_zero,add_zero]

/-- Measurability of the physical discrepancy for an exterior-field forecast. -/
theorem measurable_forecast_discrepancy {n : ℕ} (e : Fin (n+1)) (f : (Exterior e→ℝ) → ℝ)
    (hf : Measurable f) : Measurable (fun h => skewConstraint (f (outside e h)) h) := by
  have hH : Continuous (fun h : PathShell n => pathHamiltonian h) :=
    (pathHamiltonianLM n).continuous_of_finiteDimensional
  have hM : Continuous (thirdMoment (n:=n)) := by unfold thirdMoment Matrix.trace; fun_prop
  exact (hM.measurable.pow_const 2).sub
    ((hf.comp (measurable_outside e)).mul ((continuous_norm.measurable.pow_const 2).pow_const 3))

/-- The forecast and the conditioning event may read every coupling except
three on the chosen bond. The constant is independent of the observed fields,
the event probability and the position of the bond. -/
theorem conditional_shape_price {n : ℕ} (e : Fin (n+1)) (f : (Exterior e→ℝ) → ℝ)
    (hf : Measurable f) (D : Set (Exterior e→ℝ)) (hD : MeasurableSet D) {r : ℝ} (hr : 0<r) :
    let S := {h : PathShell n | |skewConstraint (f (outside e h)) h|<(2/3)*r^6}
    let O := outside e ⁻¹' D
    stdGaussian (PathShell n) (S ∩ O) ≤ ENNReal.ofReal (12*r)*stdGaussian (PathShell n) O := by
  intro S O
  let μ := stdGaussian (PathShell n)
  let a := ENNReal.ofReal (12*r)
  let A := {h : PathShell n | 2/3≤|f (outside e h)|}
  have hmeas := hf.comp (measurable_outside e)
  have hA : MeasurableSet A := measurableSet_le measurable_const hmeas.abs
  have hO : MeasurableSet O := hD.preimage (measurable_outside e)
  have hS : MeasurableSet S := measurableSet_lt (measurable_forecast_discrepancy e f hf).abs measurable_const
  obtain ⟨u,v,hu,hv,h₀,h₄,hou,hov⟩ := local_directions e
  have branch (w : PathShell n) (hw : ‖w‖=1) (how : outside e w=0)
      (B : Set (PathShell n)) (hB : MeasurableSet B)
      (hinv : ∀ (y : PathShell n) (t : ℝ), y+t • w∈B ↔ y∈B)
      (hcoeff : ∀ y∈B, 2/3≤|skewConstraint (f (outside e y)) w|) :
      μ (S ∩ B) ≤ a*μ B := by
    apply conditional_line_bound (.inl (0,0) : PathLabel n) w hw S B hS hB a ENNReal.ofReal_ne_top hinv
    intro y hy
    have heq : {t : ℝ | y+t • w∈S} =
        {t : ℝ | |skewConstraint (f (outside e y)) (y+t • w)|<(2/3)*r^6} := by
      ext t
      change |skewConstraint (f (outside e (y+t • w))) (y+t • w)|<_ ↔ _
      rw [outside_line e how]
      rfl
    rw [heq]
    exact line_sublevel _ y w hr (hcoeff y hy)
  have h₁ : μ (S ∩ (O ∩ A)) ≤ a*μ (O ∩ A) := by
    apply branch u hu hou _ (hO.inter hA)
    · intro y t
      change (outside e (y+t • u)∈D ∧ 2/3≤|f (outside e (y+t • u))|) ↔ _
      rw [outside_line e hou]
      rfl
    · intro y hy
      simpa [skewConstraint,hu,h₀] using (show 2/3≤|f (outside e y)| from hy.2)
  have h₂ : μ (S ∩ (O \ A)) ≤ a*μ (O \ A) := by
    apply branch v hv hov _ (hO.diff hA)
    · intro y t
      change (outside e (y+t • v)∈D ∧ ¬2/3≤|f (outside e (y+t • v))|) ↔ _
      rw [outside_line e hov]
      rfl
    · intro y hy
      have hc : |f (outside e y)|<2/3 := lt_of_not_ge hy.2
      simp only [skewConstraint,h₄,hv,one_pow,mul_one]
      exact (by linarith only [hc,le_abs_self (f (outside e y))] : (2:ℝ)/3≤4/3-f (outside e y)).trans
        (le_abs_self _)
  calc
    μ (S ∩ O) = μ ((S ∩ O) ∩ A)+μ ((S ∩ O) \ A) := (measure_inter_add_sdiff _ hA).symm
    _ = μ (S ∩ (O ∩ A))+μ (S ∩ (O \ A)) := by
      congr 1
      · rw [inter_assoc]
      · congr 1
        ext y
        exact and_assoc
    _ ≤ a*μ (O ∩ A)+a*μ (O \ A) := add_le_add h₁ h₂
    _ = a*μ O := by rw [←mul_add,measure_inter_add_sdiff _ hA]

#print axioms conditional_shape_price
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
