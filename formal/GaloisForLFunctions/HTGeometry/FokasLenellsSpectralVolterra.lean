import GaloisForLFunctions.HTGeometry.FokasLenellsUniformization
import GaloisForLFunctions.HTGeometry.VolterraLinearIntegralEquation
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Normed.Operator.Prod
import GaloisForLFunctions.RHTower.L2FourierConjugation
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Fokas–Lenells spectral Volterra evolution

The factorial Picard mechanism in Section 2 of Yan–Zhang–Zhu,
arXiv:2607.19649v1, is applied to the corpus's Banach-space Volterra solver.
The coefficient operator is exactly `i z σ₃ + Q̂`, with Schwartz coefficient
profiles. Bounded continuous functions provide all global coefficient bounds.

The resulting initial-value eigenfunction exists uniquely, has a factorially
convergent Picard expansion, obeys an exponential bound and solves the actual
spectral ODE. The final specialization uses a Schwartz initial potential,
its first and second derivatives, and the correctly signed reflected derivative.
No smallness hypothesis is used. This is normalization at zero, not a Jost
normalization at either infinite endpoint.
-/

open Complex Matrix MeasureTheory
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section


abbrev SpectralVector := ℂ × ℂ

def pairOperator (a b c d : ℂ) : SpectralVector →L[ℝ] SpectralVector :=
  (a • ContinuousLinearMap.fst ℝ ℂ ℂ + b • ContinuousLinearMap.snd ℝ ℂ ℂ).prod
    (c • ContinuousLinearMap.fst ℝ ℂ ℂ + d • ContinuousLinearMap.snd ℝ ℂ ℂ)

theorem pairOperator_bound (a b c d : ℂ) :
    ‖pairOperator a b c d‖ ≤ ‖a‖+‖b‖+‖c‖+‖d‖ := by
  unfold pairOperator
  rw [ContinuousLinearMap.opNorm_prod, Prod.norm_def]
  apply max_le
  · have h := norm_add_le (a • ContinuousLinearMap.fst ℝ ℂ ℂ)
      (b • ContinuousLinearMap.snd ℝ ℂ ℂ)
    simp only [norm_smul, ContinuousLinearMap.norm_fst, ContinuousLinearMap.norm_snd,
      mul_one] at h
    linarith [norm_nonneg c,norm_nonneg d]
  · have h := norm_add_le (c • ContinuousLinearMap.fst ℝ ℂ ℂ)
      (d • ContinuousLinearMap.snd ℝ ℂ ℂ)
    simp only [norm_smul, ContinuousLinearMap.norm_fst, ContinuousLinearMap.norm_snd,
      mul_one] at h
    linarith [norm_nonneg a,norm_nonneg b]

def spectralEntries (f g h : SchwartzMap ℝ ℂ) (z : ℂ) :
    Matrix (Fin 2) (Fin 2) (BoundedContinuousFunction ℝ ℂ) :=
  let U := f.toBoundedContinuousFunction
  let V := g.toBoundedContinuousFunction
  let W := h.toBoundedContinuousFunction
  !![BoundedContinuousFunction.const ℝ (I*z) + (I/2) • (U*V), (-I/2) • V;
    W + (I/2) • (U^(2 : ℕ)*V), BoundedContinuousFunction.const ℝ (-I*z) + (-I/2) • (U*V)]

theorem spectralEntries_apply (f g h : SchwartzMap ℝ ℂ) (z : ℂ) (x : ℝ) :
    (spectralEntries f g h z).map (fun e => e x) =
      uniformizedLax (f x) (g x) (h x) z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spectralEntries, uniformizedLax, effectivePotential] <;> ring

def spectralMass (f g h : SchwartzMap ℝ ℂ) (z : ℂ) : ℝ :=
  ‖spectralEntries f g h z 0 0‖ + ‖spectralEntries f g h z 0 1‖ +
    ‖spectralEntries f g h z 1 0‖ + ‖spectralEntries f g h z 1 1‖

def spectralKernel (f g h : SchwartzMap ℝ ℂ) (z : ℂ) (_t s : ℝ) :
    SpectralVector →L[ℝ] SpectralVector :=
  pairOperator (spectralEntries f g h z 0 0 s) (spectralEntries f g h z 0 1 s)
    (spectralEntries f g h z 1 0 s) (spectralEntries f g h z 1 1 s)

theorem spectralMass_nonneg (f g h : SchwartzMap ℝ ℂ) (z : ℂ) :
    0 ≤ spectralMass f g h z := by unfold spectralMass; positivity

theorem continuous_spectralKernel (f g h : SchwartzMap ℝ ℂ) (z : ℂ) :
    Continuous (fun p : ℝ × ℝ => spectralKernel f g h z p.1 p.2) := by
  let U : ℝ × ℝ → SpectralVector →L[ℝ] ℂ := fun p =>
    spectralEntries f g h z 0 0 p.2 • ContinuousLinearMap.fst ℝ ℂ ℂ +
      spectralEntries f g h z 0 1 p.2 • ContinuousLinearMap.snd ℝ ℂ ℂ
  let V : ℝ × ℝ → SpectralVector →L[ℝ] ℂ := fun p =>
    spectralEntries f g h z 1 0 p.2 • ContinuousLinearMap.fst ℝ ℂ ℂ +
      spectralEntries f g h z 1 1 p.2 • ContinuousLinearMap.snd ℝ ℂ ℂ
  have hU : Continuous U := by fun_prop
  have hV : Continuous V := by fun_prop
  exact (ContinuousLinearMap.prodₗᵢ (𝕜 := ℝ) (E := SpectralVector)
    (F := ℂ) (G := ℂ) ℝ).continuous.comp (hU.prodMk hV)

theorem spectralKernel_bound (f g h : SchwartzMap ℝ ℂ) (z : ℂ) (t s : ℝ) :
    ‖spectralKernel f g h z t s‖ ≤ spectralMass f g h z := by
  refine (pairOperator_bound _ _ _ _).trans ?_
  exact add_le_add (add_le_add (add_le_add
    ((spectralEntries f g h z 0 0).norm_coe_le_norm s)
    ((spectralEntries f g h z 0 1).norm_coe_le_norm s))
    ((spectralEntries f g h z 1 0).norm_coe_le_norm s))
    ((spectralEntries f g h z 1 1).norm_coe_le_norm s)

/-- The eigenfunction solution constructed from the convergent Picard series. -/
def spectralSolution (f g h : SchwartzMap ℝ ℂ) (z : ℂ) (v : SpectralVector) :
    ℝ → SpectralVector :=
  volterraSolution (fun _ => v) (spectralKernel f g h z)

theorem continuous_spectralSolution (f g h : SchwartzMap ℝ ℂ) (z : ℂ)
    (v : SpectralVector) : Continuous (spectralSolution f g h z v) :=
  continuous_volterraSolution continuous_const (continuous_spectralKernel f g h z)
    (spectralMass_nonneg f g h z) (norm_nonneg v) (spectralKernel_bound f g h z)
    (fun _ => le_rfl)

theorem spectralSolution_equation (f g h : SchwartzMap ℝ ℂ) (z : ℂ)
    (v : SpectralVector) (x : ℝ) :
    spectralSolution f g h z v x = v + ∫ s in (0:ℝ)..x,
      spectralKernel f g h z x s (spectralSolution f g h z v s) :=
  volterraSolution_eq continuous_const (continuous_spectralKernel f g h z)
    (spectralMass_nonneg f g h z) (norm_nonneg v) (spectralKernel_bound f g h z)
    (fun _ => le_rfl) x

theorem spectralSolution_initial (f g h : SchwartzMap ℝ ℂ) (z : ℂ)
    (v : SpectralVector) : spectralSolution f g h z v 0 = v := by
  rw [spectralSolution_equation]
  simp

/-- Factorial convergence, without a small-potential condition. -/
theorem spectral_picard_increment (f g h : SchwartzMap ℝ ℂ) (z : ℂ)
    (v : SpectralVector) (n : ℕ) (x : ℝ) :
    ‖volterraIterate (fun _ => v) (spectralKernel f g h z) (n+1) x -
      volterraIterate (fun _ => v) (spectralKernel f g h z) n x‖ ≤
      ‖v‖ * spectralMass f g h z ^ (n+1) * |x|^(n+1) / (n+1).factorial :=
  norm_volterraIterate_succ_sub_le continuous_const (continuous_spectralKernel f g h z)
    (spectralMass_nonneg f g h z) (norm_nonneg v) (spectralKernel_bound f g h z)
    (fun _ => le_rfl) n x

theorem spectralSolution_bound (f g h : SchwartzMap ℝ ℂ) (z : ℂ)
    (v : SpectralVector) (x : ℝ) :
    ‖spectralSolution f g h z v x‖ ≤ ‖v‖ * Real.exp (spectralMass f g h z * |x|) :=
  norm_volterraSolution_le continuous_const (continuous_spectralKernel f g h z)
    (spectralMass_nonneg f g h z) (norm_nonneg v) (spectralKernel_bound f g h z)
    (fun _ => le_rfl) x

theorem spectralSolution_existsUnique (f g h : SchwartzMap ℝ ℂ) (z : ℂ)
    (v : SpectralVector) :
    ∃! u : ℝ → SpectralVector, Continuous u ∧
      ∀ x, u x = v + ∫ s in (0:ℝ)..x, spectralKernel f g h z x s (u s) := by
  refine ⟨spectralSolution f g h z v,
    ⟨continuous_spectralSolution f g h z v, spectralSolution_equation f g h z v⟩, ?_⟩
  intro u hu
  exact volterra_eq_of_eq_of_eq (continuous_spectralKernel f g h z)
    (spectralMass_nonneg f g h z) (spectralKernel_bound f g h z)
    hu.1 (continuous_spectralSolution f g h z v) hu.2 (spectralSolution_equation f g h z v)

/-- Differentiating the convergent integral equation produces the actual spectral ODE. -/
theorem spectralSolution_hasDerivAt (f g h : SchwartzMap ℝ ℂ) (z : ℂ)
    (v : SpectralVector) (x : ℝ) :
    HasDerivAt (spectralSolution f g h z v)
      (spectralKernel f g h z x x (spectralSolution f g h z v x)) x := by
  have hK : Continuous (fun s : ℝ => spectralKernel f g h z 0 s) :=
    (continuous_spectralKernel f g h z).comp (f := fun s : ℝ => ((0:ℝ), s))
      ((continuous_const : Continuous (fun _ : ℝ => (0:ℝ))).prodMk continuous_id)
  have hc := hK.clm_apply (continuous_spectralSolution f g h z v)
  have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).const_add v
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun y => spectralSolution_equation f g h z v y))

/-- The operator used in the Picard construction is exactly the paper's matrix action. -/
theorem spectralKernel_eq_matrix (f g h : SchwartzMap ℝ ℂ) (z : ℂ)
    (t s : ℝ) (v : SpectralVector) :
    spectralKernel f g h z t s v =
      ((uniformizedLax (f s) (g s) (h s) z *ᵥ ![v.1,v.2]) 0,
       (uniformizedLax (f s) (g s) (h s) z *ᵥ ![v.1,v.2]) 1) := by
  have he (i j : Fin 2) := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i j)
    (spectralEntries_apply f g h z s)
  simp only [Matrix.map_apply] at he
  change (spectralEntries f g h z 0 0 s * v.1 + spectralEntries f g h z 0 1 s * v.2,
    spectralEntries f g h z 1 0 s * v.1 + spectralEntries f g h z 1 1 s * v.2) = _
  rw [he 0 0, he 0 1, he 1 0, he 1 1]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The reflected derivative has the sign dictated by simultaneous reversal,
with no complex conjugation. -/
def reflectedDerivative (q : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  -(RHTower.negSchwartz' (SchwartzMap.derivCLM ℂ ℂ q))

theorem reflectedDerivative_apply (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    reflectedDerivative q x = deriv (fun y : ℝ => q (-y)) x := by
  simp [reflectedDerivative, RHTower.negSchwartz'_apply,
    SchwartzMap.derivCLM_apply, deriv_comp_neg]

/-- The eigenfunction for the actual initial-data potential in equation (2.8). -/
def initialSpectralSolution (q : SchwartzMap ℝ ℂ) (z : ℂ) (v : SpectralVector) :
    ℝ → SpectralVector :=
  spectralSolution (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
    (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q)) z v

/-- Global spectral-ODE existence for every Schwartz initial potential. -/
theorem initialSpectralSolution_hasDerivAt (q : SchwartzMap ℝ ℂ) (z : ℂ)
    (v : SpectralVector) (x : ℝ) :
    HasDerivAt (initialSpectralSolution q z v)
      (let A := uniformizedLax (deriv q x) (deriv (fun y : ℝ => q (-y)) x)
          (deriv (deriv q) x) z
       let u := initialSpectralSolution q z v x
       ((A *ᵥ ![u.1,u.2]) 0, (A *ᵥ ![u.1,u.2]) 1)) x := by
  refine (spectralSolution_hasDerivAt (SchwartzMap.derivCLM ℂ ℂ q)
    (reflectedDerivative q) (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q))
    z v x).congr_deriv ?_
  rw [spectralKernel_eq_matrix]
  simp only [SchwartzMap.derivCLM_apply, reflectedDerivative_apply]
  rfl

theorem initialSpectralSolution_initial (q : SchwartzMap ℝ ℂ) (z : ℂ)
    (v : SpectralVector) : initialSpectralSolution q z v 0 = v :=
  spectralSolution_initial _ _ _ _ _

end
end GaloisForLFunctions.HTGeometry.FokasLenells
