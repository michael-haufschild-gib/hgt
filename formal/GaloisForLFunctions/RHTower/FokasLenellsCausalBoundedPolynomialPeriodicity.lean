import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedPolynomialEigenmodes
import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedPolynomialFlowGroup
import GaloisForLFunctions.HTGeometry.ExpPolynomialRational

/-! Actual entire polynomial evolution on the genuine bounded Cauchy derivative space. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance causalPolynomialPeriodLowerComplete : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance causalPolynomialPeriodChainComplete : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance causalPolynomialPeriodChainNormedGroup : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance causalPolynomialPeriodChainNormedSpace : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
local instance causalPolynomialPeriodEndNormedRing : NormedRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedRing
local instance causalPolynomialPeriodEndTopology : TopologicalSpace (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  (inferInstance : NormedAddCommGroup
    (causalBoundedChain →L[ℂ] causalBoundedChain)).toUniformSpace.toTopologicalSpace
local instance causalPolynomialPeriodEndTopologicalRing : IsTopologicalRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

local instance causalPolynomialPeriodEndNormedAlgebra : NormedAlgebra ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedAlgebra
local instance causalPolynomialPeriodEndNormOne : NormOneClass (causalBoundedChain →L[ℂ] causalBoundedChain) := ⟨by
  have he := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => ‖A‖)
    causalBoundedChainExponential_zero
  exact he.symm.trans (norm_causalBoundedChainExponential_real (0 : ℝ≥0))⟩


open Polynomial

/-- The actual constant-polynomial flow is scalar multiplication by the scalar exponential. -/
theorem causalBoundedPolynomialExponential_constant (c z : ℂ) :
    causalBoundedPolynomialExponential (C c) z =
      algebraMap ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) (Complex.exp (z*c)) := by
  have hc : causalBoundedPolynomialOperator (C c) =
      algebraMap ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) c :=
    Polynomial.aeval_C causalBoundedChainShift c
  have hs := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => z • A) hc
  have hm : z • algebraMap ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) c =
      algebraMap ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) (z*c) :=
    (Algebra.smul_def z _).trans (((algebraMap ℂ _).map_mul z c).symm)
  have he := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => NormedSpace.exp A) (hs.trans hm)
  have ha : NormedSpace.exp (algebraMap ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) (z*c)) =
      algebraMap ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) (Complex.exp (z*c)) := by
    simpa only [Complex.exp_eq_exp_ℂ] using
      (NormedSpace.algebraMap_exp_comm (𝕂 := ℂ) (𝔸 := causalBoundedChain →L[ℂ] causalBoundedChain) (z*c)).symm
  exact he.trans ha

private theorem identity_scalar_character (p : ℂ[X])
    (hp : causalBoundedPolynomialExponential p 1 = 1) (q : causalBoundedDiskRate) :
    Complex.exp (p.eval q.val) = 1 := by
  let u := causalBoundedDiskEigenchain q
  have he : causalBoundedPolynomialExponential p 1 u = Complex.exp (p.eval q.val) • u := by
    simpa only [one_mul] using causalBoundedPolynomialExponential_diskEigenchain p 1 q
  have hi : causalBoundedPolynomialExponential p 1 u = u :=
    congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => A u) hp
  have hx : Complex.exp (p.eval q.val) • u = (1 : ℂ) • u :=
    he.symm.trans (hi.trans (one_smul ℂ u).symm)
  have hz : (Complex.exp (p.eval q.val)-1) • u = 0 :=
    (sub_smul (Complex.exp (p.eval q.val)) 1 u).trans
      ((congrArg (fun v : causalBoundedChain => v - (1 : ℂ) • u) hx).trans (sub_self _))
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right (causalBoundedDiskEigenchain_ne_zero q))

private theorem identity_entire_character (p : ℂ[X])
    (hp : causalBoundedPolynomialExponential p 1 = 1) :
    ∀ z : ℂ, Complex.exp (p.eval z) = 1 := by
  have hopen : IsOpen {z : ℂ | z.re < 0 ∧ ‖z‖ < 1} :=
    (isOpen_lt Complex.continuous_re continuous_const).inter (isOpen_lt continuous_norm continuous_const)
  have hmem : (-1/2 : ℂ) ∈ {z : ℂ | z.re < 0 ∧ ‖z‖ < 1} := by
    constructor <;> norm_num
  have hnear : ∀ᶠ z : ℂ in 𝓝 (-1/2 : ℂ), z.re < 0 ∧ ‖z‖ < 1 := hopen.mem_nhds hmem
  have hlocal : (fun z : ℂ => Complex.exp (p.eval z)) =ᶠ[𝓝 (-1/2 : ℂ)] (fun _ => 1) :=
    hnear.mono (fun z hz => identity_scalar_character p hp ⟨z, hz.1, hz.2.le⟩)
  have hf : AnalyticOnNhd ℂ (fun z : ℂ => Complex.exp (p.eval z)) Set.univ :=
    fun z _ => (Complex.differentiable_exp.comp p.differentiable).analyticAt z
  have hg : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) Set.univ := fun _ _ => analyticAt_const
  exact congrFun (hf.eq_of_eventuallyEq hg hlocal)

/-- Only integer constant exponential periods make every genuine chain return after unit time. -/
theorem causalBoundedPolynomialExponential_one_eq_one_iff (p : ℂ[X]) :
    causalBoundedPolynomialExponential p 1 = 1 ↔
      ∃ n : ℤ, p = C ((n : ℂ)*(2*Real.pi*Complex.I)) := by
  constructor
  · intro hp
    have hchar := identity_entire_character p hp
    have hd : p.derivative = 0 := derivative_eq_zero_of_expPolynomial_eq_ratio
      (G := (1 : ℂ[X])) (Q := (1 : ℂ[X])) (T := p) one_ne_zero one_ne_zero
      (by intro z; simpa only [Polynomial.eval_one, one_mul] using hchar z)
    have hc := Polynomial.eq_C_of_derivative_eq_zero hd
    have he : Complex.exp (p.coeff 0) = 1 := by
      exact (congrArg Complex.exp (Polynomial.coeff_zero_eq_eval_zero p)).trans (hchar 0)
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp he
    exact ⟨n, hc.trans (congrArg Polynomial.C hn)⟩
  · rintro ⟨n, rfl⟩
    have he : Complex.exp ((n : ℂ)*(2*Real.pi*Complex.I)) = 1 :=
      Complex.exp_eq_one_iff.mpr ⟨n, rfl⟩
    have h := causalBoundedPolynomialExponential_constant ((n : ℂ)*(2*Real.pi*Complex.I)) 1
    have hs := congrArg (fun c : ℂ => algebraMap ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) c)
      ((congrArg Complex.exp (one_mul ((n : ℂ)*(2*Real.pi*Complex.I)))).trans he)
    exact h.trans (hs.trans (map_one _))

/-- Two unit-time polynomial flows agree exactly when their exponents differ by a constant integer period. -/
theorem causalBoundedPolynomialExponential_one_eq_iff (p q : ℂ[X]) :
    causalBoundedPolynomialExponential p 1 = causalBoundedPolynomialExponential q 1 ↔
      ∃ n : ℤ, p-q = C ((n : ℂ)*(2*Real.pi*Complex.I)) := by
  have hr : p-q = (1 : ℂ) • p + (-1 : ℂ) • q := by
    simp only [one_smul, neg_one_smul, sub_eq_add_neg]
  have he : causalBoundedPolynomialExponential (p-q) 1 =
      causalBoundedPolynomialExponential p 1 * causalBoundedPolynomialExponential q (-1) :=
    (congrArg (fun r : ℂ[X] => causalBoundedPolynomialExponential r 1) hr).trans
      (causalBoundedPolynomialExponential_mix p q 1 (-1))
  have hiff : causalBoundedPolynomialExponential p 1 = causalBoundedPolynomialExponential q 1 ↔
      causalBoundedPolynomialExponential (p-q) 1 = 1 := by
    constructor
    · intro hpq
      have hm := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain =>
        A * causalBoundedPolynomialExponential q (-1)) hpq
      have hq : causalBoundedPolynomialExponential q 1 * causalBoundedPolynomialExponential q (-1) = 1 :=
        (causalBoundedPolynomialExponential_add q 1 (-1)).symm.trans
          ((congrArg (causalBoundedPolynomialExponential q) (add_neg_cancel (1 : ℂ))).trans
            (causalBoundedPolynomialExponential_zero q))
      exact he.trans (hm.trans hq)
    · intro hpq
      apply ContinuousLinearMap.ext
      intro u
      have h := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain =>
        A (causalBoundedPolynomialExponential q 1 u)) (he.symm.trans hpq)
      have hi := congrArg (fun v : causalBoundedChain => causalBoundedPolynomialExponential p 1 v)
        (causalBoundedPolynomialExponential_neg_apply q 1 u)
      exact hi.symm.trans h
  exact hiff.trans (causalBoundedPolynomialExponential_one_eq_one_iff (p-q))

/-- At any complex time, the full return condition is exactly a constant integer period in the scaled polynomial. -/
theorem causalBoundedPolynomialExponential_eq_one_iff (p : ℂ[X]) (z : ℂ) :
    causalBoundedPolynomialExponential p z = 1 ↔
      ∃ n : ℤ, z • p = C ((n : ℂ)*(2*Real.pi*Complex.I)) := by
  have hp : causalBoundedPolynomialOperator (z • p) = z • causalBoundedPolynomialOperator p :=
    (Polynomial.aeval causalBoundedChainShift).toLinearMap.map_smul z p
  have hs : (1 : ℂ) • causalBoundedPolynomialOperator (z • p) = z • causalBoundedPolynomialOperator p :=
    (one_smul ℂ _).trans hp
  have he : causalBoundedPolynomialExponential (z • p) 1 = causalBoundedPolynomialExponential p z :=
    congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => NormedSpace.exp A) hs
  exact (congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => A = 1) he).symm.to_iff.trans
    (causalBoundedPolynomialExponential_one_eq_one_iff (z • p))

/-- Complete equality classification for arbitrary complex-time polynomial flows. -/
theorem causalBoundedPolynomialExponential_eq_iff (p q : ℂ[X]) (z w : ℂ) :
    causalBoundedPolynomialExponential p z = causalBoundedPolynomialExponential q w ↔
      ∃ n : ℤ, z • p - w • q = C ((n : ℂ)*(2*Real.pi*Complex.I)) := by
  have hscale (r : ℂ[X]) (t : ℂ) :
      causalBoundedPolynomialExponential (t • r) 1 = causalBoundedPolynomialExponential r t := by
    have hr : causalBoundedPolynomialOperator (t • r) = t • causalBoundedPolynomialOperator r :=
      (Polynomial.aeval causalBoundedChainShift).toLinearMap.map_smul t r
    have hs : (1 : ℂ) • causalBoundedPolynomialOperator (t • r) = t • causalBoundedPolynomialOperator r :=
      (one_smul ℂ _).trans hr
    exact congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => NormedSpace.exp A) hs
  have he := congrArg₂ (fun A B : causalBoundedChain →L[ℂ] causalBoundedChain => A=B)
    (hscale p z) (hscale q w)
  exact he.symm.to_iff.trans (causalBoundedPolynomialExponential_one_eq_iff (z • p) (w • q))

end
end RHTower.FokasLenells
