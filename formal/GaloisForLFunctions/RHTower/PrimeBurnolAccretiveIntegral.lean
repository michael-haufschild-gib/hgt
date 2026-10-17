import GaloisForLFunctions.RHTower.PrimeBurnolAccretiveEvolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # The integrated resolvent identity on the full Burnol Hilbert space -/

open Complex Set Filter Topology MeasureTheory
open scoped NNReal
noncomputable section
namespace RHTower.BurnolAccretiveSymbol
open GaloisForLFunctions.HTGeometry _root_.HTGeometry
variable (ψ : BurnolAccretiveSymbol)

theorem continuous_clipped_evolution (u : BurnolHalfLineL2) :
    Continuous (fun s : ℝ => ψ.evolution s.toNNReal u) :=
  (ψ.continuous_evolution u).comp continuous_real_toNNReal

def orbitPrimitive (r : ℝ) (u : BurnolHalfLineL2) : BurnolHalfLineL2 :=
  ∫ s in (0 : ℝ)..r, ψ.evolution s.toNNReal u

private def orbitIntegralLinear (t : ℝ≥0) : BurnolHalfLineL2 →ₗ[ℂ] BurnolHalfLineL2 where
  toFun := ψ.orbitPrimitive t
  map_add' u v := by
    unfold orbitPrimitive
    simp only [map_add]
    exact intervalIntegral.integral_add ((ψ.continuous_clipped_evolution u).intervalIntegrable _ _)
      ((ψ.continuous_clipped_evolution v).intervalIntegrable _ _)
  map_smul' c u := by
    unfold orbitPrimitive
    simp only [map_smul]
    exact intervalIntegral.integral_smul c _

private theorem primitive_bound (t : ℝ≥0) (u : BurnolHalfLineL2) :
    ‖ψ.orbitPrimitive t u‖ ≤ (t : ℝ)*‖u‖ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := (t : ℝ)) (fun s _ => ψ.evolution_norm_le s.toNNReal u)
  have ht : |(t : ℝ)| = (t : ℝ) := abs_of_nonneg t.property
  simpa only [orbitPrimitive, sub_zero, ht, mul_comm] using h

def orbitIntegral (t : ℝ≥0) : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2 :=
  (ψ.orbitIntegralLinear t).mkContinuous (t : ℝ) (ψ.primitive_bound t)

theorem orbitIntegral_apply (t : ℝ≥0) (u : BurnolHalfLineL2) :
    ψ.orbitIntegral t u = ψ.orbitPrimitive t u := rfl

theorem orbitPrimitive_hasDerivAt (r : ℝ) (u : BurnolHalfLineL2) :
    HasDerivAt (fun x => ψ.orbitPrimitive x u) (ψ.evolution r.toNNReal u) r :=
  intervalIntegral.integral_hasDerivAt_right
    ((ψ.continuous_clipped_evolution u).intervalIntegrable 0 r)
    ((ψ.continuous_clipped_evolution u).stronglyMeasurableAtFilter volume (𝓝 r))
    (ψ.continuous_clipped_evolution u).continuousAt

theorem orbitPrimitive_zero (u : BurnolHalfLineL2) : ψ.orbitPrimitive 0 u = 0 := by
  simp only [orbitPrimitive, intervalIntegral.integral_same]

theorem orbitPrimitive_hasDerivAt_zero (u : BurnolHalfLineL2) :
    HasDerivAt (fun x => ψ.orbitPrimitive x u) u 0 := by
  simpa only [Real.toNNReal_zero, ψ.evolution_zero, one_apply_eq_self] using
    ψ.orbitPrimitive_hasDerivAt 0 u

private theorem scalar_orbit_derivative (a c : ℂ) (u : BurnolHalfLineL2) (s : ℝ) :
    HasDerivAt (fun x : ℝ => (Complex.exp (-(x : ℂ)*a)*c) • u)
      ((Complex.exp (-(s : ℂ)*a)*(-a*c)) • u) s := by
  have hlin : HasDerivAt (fun x : ℝ => -(x : ℂ)*a) (-a) s := by
    have h := (Complex.ofRealCLM.hasDerivAt (x := s)).neg.mul_const a
    change HasDerivAt (fun x : ℝ => -(x : ℂ)*a) (-(1 : ℂ)*a) s at h
    simpa only [neg_mul, one_mul] using h
  have he := (Complex.hasDerivAt_exp (-(s : ℂ)*a)).scomp s hlin
  have hd := (he.mul_const c).smul_const u
  simpa only [Function.comp_def, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using hd

private theorem scalar_orbit_integral (a c : ℂ) (u : BurnolHalfLineL2) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, (Complex.exp (-(s : ℂ)*a)*(-a*c)) • u) =
      (Complex.exp (-(t : ℂ)*a)*c) • u - c • u := by
  have hc : Continuous (fun s : ℝ => (Complex.exp (-(s : ℂ)*a)*(-a*c)) • u) := by fun_prop
  simpa only [Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, one_mul] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => scalar_orbit_derivative a c u s) (hc.intervalIntegrable 0 t)

/-- The resolvent identity is proved on prime eigenvectors and extends by boundedness. -/
theorem evolution_resolvent_integral (t : ℝ≥0) :
    (ψ.evolution t).comp ψ.resolvent - ψ.resolvent =
      (ψ.orbitIntegral t).comp (ψ.resolvent-1) := by
  apply primeBurnol_operator_ext
  intro p
  let a := ψ (Real.log (p : ℝ))
  let c := ψ.resolventFn (Real.log (p : ℝ))
  let u := primeLogCriticalLaplaceFeatureL2 p
  have he : c-1 = -a*c := by
    have hm : (1+a)*c = 1 := mul_inv_cancel₀
      (ψ.one_add_ne_zero (Real.log_pos (by exact_mod_cast p.property.one_lt)))
    linear_combination hm
  change ψ.evolution t (ψ.resolvent u)-ψ.resolvent u =
    ψ.orbitPrimitive t (ψ.resolvent u-u)
  have hr : ψ.resolvent u = c • u := ψ.resolvent_prime p
  rw [hr, map_smul]
  have ht : ψ.evolution t u = ψ.evolutionFn t (Real.log (p : ℝ)) • u := ψ.evolution_prime t p
  rw [ht, smul_smul]
  change (c*Complex.exp (-((t : ℝ) : ℂ)*a)) • u - c • u = _
  rw [mul_comm c]
  rw [← scalar_orbit_integral a c u (t : ℝ)]
  unfold orbitPrimitive
  apply intervalIntegral.integral_congr
  intro s hs
  have hs0 : 0 ≤ s := (Set.uIcc_of_le t.property ▸ hs).1
  change (Complex.exp (-(s : ℂ)*a)*(-a*c)) • u = ψ.evolution s.toNNReal (c • u-u)
  rw [map_sub, map_smul]
  have hsu : ψ.evolution s.toNNReal u = Complex.exp (-(s : ℂ)*a) • u := by
    simpa only [evolutionFn, Real.coe_toNNReal s hs0] using ψ.evolution_prime s.toNNReal p
  rw [hsu, smul_smul]
  calc
    (Complex.exp (-(s : ℂ)*a)*(-a*c)) • u =
        ((c-1)*Complex.exp (-(s : ℂ)*a)) • u := by rw [he, mul_comm]
    _ = (c*Complex.exp (-(s : ℂ)*a)) • u - Complex.exp (-(s : ℂ)*a) • u := by
      rw [sub_mul, one_mul, sub_smul]

theorem graph_orbit_integral {u v : BurnolHalfLineL2} (h : (u,v) ∈ ψ.graph) (t : ℝ≥0) :
    ψ.evolution t u-u = ψ.orbitPrimitive t v := by
  obtain ⟨w,rfl,rfl⟩ := (ψ.graph_mem_iff_param u v).mp h
  exact congrArg (fun A : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2 => A w)
    (ψ.evolution_resolvent_integral t)

end RHTower.BurnolAccretiveSymbol
