import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.CurvePhases
import GaloisForLFunctions.HTGeometry.MeromorphicGermField
import GaloisForLFunctions.HTGeometry.AlgebraicClosureDerivationClosed
import GaloisForLFunctions.HTGeometry.HyperexponentialPrimitive
import Mathlib.RingTheory.Localization.Integral

/-! # Exponential sums of algebraic spectral actions on a complex line -/

open Filter Topology Polynomial
open scoped Differential
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves
noncomputable section

/-- Germs algebraic over the rational functions in the line parameter. -/
abbrev curveField := (algebraicClosure (RatFunc ℂ) MeroGerm).restrictScalars ℂ

private theorem dimension_one : Algebra.trdeg ℂ curveField=1 := by
  letI : Algebra.IsAlgebraic (Polynomial ℂ) (RatFunc ℂ) :=
    (IsFractionRing.isAlgebraic_iff' (Polynomial ℂ) (Polynomial ℂ) (RatFunc ℂ)).mp inferInstance
  have hr := trdeg_add_eq ℂ (Polynomial ℂ) (A:=RatFunc ℂ)
  rw [Polynomial.trdeg_of_isDomain,trdeg_eq_zero (R:=Polynomial ℂ) (A:=RatFunc ℂ),add_zero] at hr
  letI : Algebra (RatFunc ℂ) curveField :=
    inferInstanceAs (Algebra (RatFunc ℂ) (algebraicClosure (RatFunc ℂ) MeroGerm))
  letI : IsScalarTower ℂ (RatFunc ℂ) curveField := IsScalarTower.of_algebraMap_eq fun x =>
    Subtype.ext (IsScalarTower.algebraMap_apply ℂ (RatFunc ℂ) MeroGerm x)
  letI : Algebra.IsAlgebraic (RatFunc ℂ) curveField :=
    inferInstanceAs (Algebra.IsAlgebraic (RatFunc ℂ) (algebraicClosure (RatFunc ℂ) MeroGerm))
  have hh := trdeg_add_eq ℂ (RatFunc ℂ) (A:=curveField)
  rw [trdeg_eq_zero (R:=RatFunc ℂ) (A:=curveField),add_zero,←hr] at hh
  exact hh.symm

private theorem tangent_const (c : ℂ) : meroDeriv (algebraMap ℂ MeroGerm c)=0 := by
  rw [algebraMap_complex_meroGerm,meroDeriv_ofMero,ofMero_eq_zero_iff]
  exact .of_forall fun z => deriv_const z c

/-- Differentiation in the complex coordinate of a meromorphic germ. -/
private def tangent : Derivation ℂ MeroGerm MeroGerm where
  toFun := meroDeriv
  map_add' := meroDeriv_add
  map_smul' c a := by
    rw [Algebra.smul_def,Algebra.smul_def,meroDeriv_mul,tangent_const,mul_zero,add_zero,RingHom.id_apply]
  map_one_eq_zero' := by
    change meroDeriv 1=0
    simpa only [map_one] using tangent_const (1:ℂ)
  leibniz' a b := by
    change meroDeriv (a*b)=a*meroDeriv b+b*meroDeriv a
    exact meroDeriv_mul a b

private theorem tangent_closed (y : MeroGerm) (hy : y ∈ curveField) : tangent y ∈ curveField := by
  letI : CharZero MeroGerm := charZero_of_injective_algebraMap (algebraMap ℂ MeroGerm).injective
  apply deriv_mem_algebraicClosure (E:=RatFunc ℂ) _ hy
  intro x hx
  obtain ⟨p,rfl⟩ := IntermediateField.mem_bot.mp hx
  rw [meroGerm_deriv_apply,meroDeriv_algebraMap]
  exact IntermediateField.algebraMap_mem _ _

private abbrev lineDeriv := restrictDerivation tangent curveField tangent_closed

private def coordinate : curveField := ⟨algebraMap (RatFunc ℂ) MeroGerm RatFunc.X,
  IntermediateField.algebraMap_mem (algebraicClosure (RatFunc ℂ) MeroGerm) _⟩

private theorem coordinate_changes : lineDeriv coordinate≠0 := by
  intro h
  have hc := congrArg Subtype.val h
  change meroDeriv (algebraMap (RatFunc ℂ) MeroGerm RatFunc.X)=0 at hc
  rw [algebraMap_X_meroGerm,zGerm,meroDeriv_ofMero,ofMero_eq_zero_iff] at hc
  obtain ⟨z,hz⟩ := hc.exists
  simp at hz

private theorem exp_germ_derivative {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    meroDeriv (ofMero (fun z => Complex.exp (f z)) hf.cexp.meromorphicAt)=
      meroDeriv (ofMero f hf.meromorphicAt)*ofMero (fun z => Complex.exp (f z)) hf.cexp.meromorphicAt := by
  rw [meroDeriv_ofMero,meroDeriv_ofMero,ofMero_mul,ofMero_eq_iff]
  filter_upwards [hf.eventually_analyticAt.filter_mono nhdsWithin_le_nhds] with z hz
  simpa only [Pi.mul_apply,mul_comm] using hz.differentiableAt.hasDerivAt.cexp.deriv

/-- Along an algebraic spectral curve, exponentials of analytic actions
with pairwise nonconstant differences are linearly independent even over
the algebraic functions of the curve parameter. -/
theorem algebraic_action_exponentials {ι : Type*} [Fintype ι] (f : ι → ℂ → ℂ)
    (hf : ∀ i, AnalyticAt ℂ (f i) 0)
    (ha : ∀ i, IsAlgebraic (RatFunc ℂ) (ofMero (f i) (hf i).meromorphicAt))
    (hd : ∀ i j, i≠j → ∀ c : ℂ, ¬ ((fun z => f i z-f j z) =ᶠ[𝓝[≠] 0] fun _ => c))
    (a : ι → curveField)
    (hz : ∑ i, (a i:MeroGerm)*ofMero (fun z => Complex.exp (f i z)) (hf i).cexp.meromorphicAt=0) :
    ∀ i, a i=0 := by
  let u (i : ι) : curveField := ⟨ofMero (f i) (hf i).meromorphicAt,mem_algebraicClosure_iff.mpr (ha i)⟩
  let v (i : ι) := ofMero (fun z => Complex.exp (f i z)) (hf i).cexp.meromorphicAt
  apply exponential_sum_on_curve curveField dimension_one lineDeriv tangent (fun _ => rfl)
    coordinate_changes u v _ (fun i => exp_germ_derivative (hf i)) _ a hz
  · intro i h
    obtain ⟨z,hz⟩ := ((ofMero_eq_zero_iff _).mp h).exists
    exact Complex.exp_ne_zero _ hz
  · intro i j hij h
    let B := algebraicClosure ℂ curveField
    have hb : u i-u j ∈ B := mem_algebraicClosure_iff.mpr h
    rw [show B=⊥ from IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic B] at hb
    obtain ⟨c,hc⟩ := IntermediateField.mem_bot.mp hb
    apply hd i j hij c
    have hfun := congrArg Subtype.val hc.symm
    change ofMero (f i) (hf i).meromorphicAt-ofMero (f j) (hf j).meromorphicAt=algebraMap ℂ MeroGerm c at hfun
    rwa [ofMero_sub,algebraMap_complex_meroGerm,ofMero_eq_iff] at hfun

#print axioms algebraic_action_exponentials
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves
