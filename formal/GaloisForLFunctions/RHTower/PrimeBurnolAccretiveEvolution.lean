import GaloisForLFunctions.RHTower.PrimeBurnolAccretiveGraph
import GaloisForLFunctions.HTGeometry.StrongConvergenceDense
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Strong contraction evolution from every accretive Burnol symbol -/

open Complex Set Filter Topology
open scoped NNReal
noncomputable section
namespace RHTower.BurnolAccretiveSymbol
open GaloisForLFunctions.HTGeometry _root_.HTGeometry
variable (ψ : BurnolAccretiveSymbol)

def evolutionFn (t : ℝ≥0) (z : ℂ) : ℂ := Complex.exp (-((t : ℝ) : ℂ)*ψ z)

theorem analytic_evolutionFn (t : ℝ≥0) :
    AnalyticOnNhd ℂ (ψ.evolutionFn t) PrimeBlindCarlson.rightHalf := by
  intro z hz
  exact (analyticAt_const.mul (ψ.analytic z hz)).cexp

theorem norm_evolutionFn_le (t : ℝ≥0) {z : ℂ} (hz : 0 < z.re) :
    ‖ψ.evolutionFn t z‖ ≤ 1 := by
  rw [evolutionFn, Complex.norm_exp, Real.exp_le_one_iff]
  simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  exact neg_nonpos.mpr (mul_nonneg t.property (ψ.nonneg z hz))

private theorem exists_evolution (t : ℝ≥0) :
    ∃! T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2,
      ‖T‖ ≤ 1 ∧ ∀ (z : ℂ) (hz : 0 < z.re),
        T (burnolComplexFeature z hz) = ψ.evolutionFn t z • burnolComplexFeature z hz :=
  existsUnique_burnol_operator_of_holomorphic (ψ.analytic_evolutionFn t) zero_le_one
    (fun _ hz => ψ.norm_evolutionFn_le t hz)

def evolution (t : ℝ≥0) : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2 :=
  (ψ.exists_evolution t).choose

theorem norm_evolution_le (t : ℝ≥0) : ‖ψ.evolution t‖ ≤ 1 :=
  (ψ.exists_evolution t).choose_spec.1.1

theorem evolution_norm_le (t : ℝ≥0) (u : BurnolHalfLineL2) : ‖ψ.evolution t u‖ ≤ ‖u‖ := by
  simpa only [one_mul] using (ψ.evolution t).le_opNorm u |>.trans
    (mul_le_mul_of_nonneg_right (ψ.norm_evolution_le t) (norm_nonneg u))

theorem evolution_feature (t : ℝ≥0) (z : ℂ) (hz : 0 < z.re) :
    ψ.evolution t (burnolComplexFeature z hz) = ψ.evolutionFn t z • burnolComplexFeature z hz :=
  (ψ.exists_evolution t).choose_spec.1.2 z hz

theorem evolution_prime (t : ℝ≥0) (p : Nat.Primes) :
    ψ.evolution t (primeLogCriticalLaplaceFeatureL2 p) =
      ψ.evolutionFn t (Real.log (p : ℝ)) • primeLogCriticalLaplaceFeatureL2 p :=
  (primeBurnol_eigenvalue_iff (ψ.evolution t) p _).mpr (ψ.evolution_feature t _ _)

theorem evolution_zero : ψ.evolution 0 = 1 := by
  apply primeBurnol_operator_ext
  intro p
  rw [ψ.evolution_prime]
  simp [evolutionFn]

theorem evolution_add (s t : ℝ≥0) :
    ψ.evolution (s+t) = (ψ.evolution s).comp (ψ.evolution t) := by
  apply primeBurnol_operator_ext
  intro p
  change ψ.evolution (s+t) (primeLogCriticalLaplaceFeatureL2 p) =
    ψ.evolution s (ψ.evolution t (primeLogCriticalLaplaceFeatureL2 p))
  rw [ψ.evolution_prime, ψ.evolution_prime, map_smul, ψ.evolution_prime, smul_smul]
  congr 1
  simp only [evolutionFn, NNReal.coe_add, Complex.ofReal_add, neg_add, add_mul, Complex.exp_add]
  exact mul_comm _ _

theorem evolution_resolvent (t : ℝ≥0) :
    (ψ.evolution t).comp ψ.resolvent = ψ.resolvent.comp (ψ.evolution t) := by
  apply primeBurnol_operator_ext
  intro p
  change ψ.evolution t (ψ.resolvent (primeLogCriticalLaplaceFeatureL2 p)) =
    ψ.resolvent (ψ.evolution t (primeLogCriticalLaplaceFeatureL2 p))
  rw [ψ.resolvent_prime, map_smul, ψ.evolution_prime, map_smul,
    ψ.resolvent_prime, smul_smul, smul_smul, mul_comm]

theorem continuous_evolution (u : BurnolHalfLineL2) :
    Continuous (fun t : ℝ≥0 => ψ.evolution t u) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  apply tendsto_of_dense_of_uniform_bound (C := 1) zero_le_one
    (Eventually.of_forall ψ.norm_evolution_le) (ψ.norm_evolution_le t₀)
    dense_primeLogCriticalLaplaceFeature_span
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨p,rfl⟩ := hv
    have hc : Continuous (fun t : ℝ≥0 => ψ.evolutionFn t (Real.log (p : ℝ))) := by
      unfold evolutionFn
      fun_prop
    simpa only [ψ.evolution_prime] using
      (hc.tendsto t₀).smul (tendsto_const_nhds (x := primeLogCriticalLaplaceFeatureL2 p))
  | zero => simpa only [map_zero] using (tendsto_const_nhds (x := (0 : BurnolHalfLineL2)))
  | add x y hx hy ihx ihy => simpa only [map_add] using ihx.add ihy
  | smul c x hx ih => simpa only [map_smul] using (tendsto_const_nhds (x := c)).smul ih

end RHTower.BurnolAccretiveSymbol
