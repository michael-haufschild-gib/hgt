import GaloisForLFunctions.HTGeometry.LagrangeSpectralProjector
import GaloisForLFunctions.HTGeometry.ObserverInvisibleRayPreservation
import GaloisForLFunctions.HTGeometry.EternityOperatorReturnCorollary

/-! # Comparing four phase evolutions in one fixed energy basis -/

open Finset Matrix Real Filter Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds.Products
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Attach arbitrary complex weights to the spectral lines with the given labeling. -/
def weightedLines (H : Matrix I I ℂ) (E : I→ℝ) (z : I→ℂ) :=
  ∑ j, z j • lagrangeSpectralProjector E j H

private theorem action {H : Matrix I I ℂ} {E : I→ℝ} {e : I→I→ℂ}
    (he : IsOrthoEigenBasis H e E) (hi : Function.Injective E) (z : I→ℂ) (k : I) :
    weightedLines H E z *ᵥ e k=z k • e k := by
  rw [weightedLines,Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec,lagrangeSpectralProjector_mulVec_eigen he hi]
  rw [sum_eq_single k]
  · simp
  · intro l _ hl
    simp [Ne.symm hl]
  · simp

private theorem ext_lines {H A B : Matrix I I ℂ} {E : I→ℝ} {e : I→I→ℂ}
    (he : IsOrthoEigenBasis H e E) (h : ∀ j, A *ᵥ e j=B *ᵥ e j) : A=B := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  conv_lhs => rw [←he.complete v]
  conv_rhs => rw [←he.complete v]
  simp only [Matrix.mulVec_sum,Matrix.mulVec_smul,h]

theorem weightedLines_mul {H : Matrix I I ℂ} {E : I→ℝ} {e : I→I→ℂ}
    (he : IsOrthoEigenBasis H e E) (hi : Function.Injective E) (z w : I→ℂ) :
    weightedLines H E z*weightedLines H E w=weightedLines H E (fun i => z i*w i) := by
  apply ext_lines he
  intro i
  rw [←Matrix.mulVec_mulVec,action he hi,Matrix.mulVec_smul,action he hi,action he hi,smul_smul,mul_comm]

private def phase (θ t : ℝ) : ℂ := Complex.exp (-(Complex.I*((t:ℂ)*(θ:ℂ))))

private theorem phase_norm (θ t : ℝ) : ‖phase θ t‖=1 := by
  rw [phase,Complex.norm_exp]
  simp

/-- Evaluate a spectrum F in the fixed spectral lines of (H,E). -/
def frozenEvolution (H : Matrix I I ℂ) (E F : I→ℝ) (t : ℝ) :=
  weightedLines H E (fun i => phase (F i) t)

/-- The matrix reconstructed from the instantaneous phases in its own
eigenspaces is exactly the physical evolution. -/
theorem evolution_lines {H : Matrix I I ℂ} {E : I→ℝ} {e : I→I→ℂ}
    (he : IsOrthoEigenBasis H e E) (hi : Function.Injective E) (t : ℝ) :
    unitaryEvolution H t=frozenEvolution H E E t := by
  unfold frozenEvolution
  apply ext_lines he
  intro i
  rw [QuantumAlg.unitaryEvolution_mulVec_of_eigenvector (he.eigen i),action he hi]
  rfl

theorem frozen_add {H : Matrix I I ℂ} {E : I→ℝ} {e : I→I→ℂ}
    (he : IsOrthoEigenBasis H e E) (hi : Function.Injective E) (F G : I→ℝ) (t : ℝ) :
    frozenEvolution H E F t*frozenEvolution H E G t=frozenEvolution H E (F+G) t := by
  unfold frozenEvolution
  rw [weightedLines_mul he hi]
  congr 1
  funext i
  simp only [phase,←Complex.exp_add,Pi.add_apply,Complex.ofReal_add]
  congr 1
  ring

/-- Perturbing the energy eigenspaces costs a fixed amount uniformly
over all times and all choices of the energy phases. -/
theorem uniform_freezing {X : Type*} [TopologicalSpace X] {x : X}
    {H : X→Matrix I I ℂ} {E : X→I→ℝ} (hH : Continuous H) (hE : Continuous E)
    (hx : Function.Injective (E x)) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ y in 𝓝 x, ∀ t : ℝ, ‖frozenEvolution (H y) (E y) (E y) t-
      frozenEvolution (H x) (E x) (E y) t‖<δ := by
  let P (y : X) (j : I) := lagrangeSpectralProjector (E y) j (H y)
  have hc : ContinuousAt (fun y => ∑ j, ‖P y j-P x j‖) x :=
    continuousAt_finsetSum _ fun j _ => ((continuousAt_lagrangeSpectralProjector hE hH j hx).sub continuousAt_const).norm
  have h₀ : (∑ j, ‖P x j-P x j‖)=0 := by simp
  filter_upwards [hc.tendsto.eventually_lt_const (h₀.trans_lt hδ)] with y hy
  intro t
  simp only [frozenEvolution,weightedLines,←sum_sub_distrib]
  simp_rw [←smul_sub]
  apply (norm_sum_le _ _).trans_lt
  simpa only [norm_smul,phase_norm,one_mul] using hy

private theorem phase_chord (a b t : ℝ) :
    ‖phase a t-phase b t‖≤|t|*|a-b| := by
  rw [phase,phase,norm_exp_neg_I_mul_sub_exp_neg_I_mul,Real.norm_eq_abs,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have h := Real.abs_sin_le_abs (t*(a-b)/2)
  rw [abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at h
  linarith only [h]

def projectorMass (H : Matrix I I ℂ) (E : I→ℝ) := ∑ i, ‖lagrangeSpectralProjector E i H‖

theorem frozen_norm (H : Matrix I I ℂ) (E F : I→ℝ) (t : ℝ) :
    ‖frozenEvolution H E F t‖≤projectorMass H E := by
  unfold frozenEvolution weightedLines projectorMass
  simpa only [norm_smul,phase_norm,one_mul] using
    norm_sum_le univ (fun i => phase (F i) t • lagrangeSpectralProjector E i H)

/-- Phase errors accumulate linearly in time in the fixed eigenbasis. -/
theorem frozen_change (H : Matrix I I ℂ) (E F G : I→ℝ) (t : ℝ) {r : ℝ}
    (hr : ∀ i, |F i-G i|≤r) :
    ‖frozenEvolution H E F t-frozenEvolution H E G t‖≤|t|*r*projectorMass H E := by
  simp only [frozenEvolution,weightedLines,←sum_sub_distrib]
  simp_rw [←sub_smul]
  rw [projectorMass,mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro i _
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right ((phase_chord ..).trans
    (mul_le_mul_of_nonneg_left (hr i) (abs_nonneg _))) (norm_nonneg _)

theorem frozen_neg (H : Matrix I I ℂ) (E F : I→ℝ) (t : ℝ) :
    frozenEvolution H E F (-t)=frozenEvolution H E (-F) t := by
  apply congrArg (weightedLines H E)
  funext i
  simp [phase]

#print axioms uniform_freezing
end
end GaloisForLFunctions.HTGeometry.WeakBonds.Products
