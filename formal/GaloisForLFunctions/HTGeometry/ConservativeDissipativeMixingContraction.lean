import GaloisForLFunctions.HTGeometry.ConservativeDissipativeImplicitEntropy
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

/-!
# Uniform contraction of implicit complete mixing

The positive implicit transport induced by the Schaffer–Exl energy mechanism
(arXiv:2609.04530) contracts coordinate oscillation quantitatively. Raw edge
coefficients `1 + a i j ^ 2` construct conductances at least two, and raw
step parameters construct steps `1 + u ^ 2`. The contraction factor is
`W / (W + 2)` for total positive reference mass `W`, uniformly over all
unrestricted raw coefficients and step parameters.
-/
open scoped BigOperators NNReal
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The largest coordinate of a finite density. -/
def transportMax (p : ι → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty p

/-- The smallest coordinate of a finite density. -/
def transportMin (p : ι → ℝ) : ℝ := Finset.univ.inf' Finset.univ_nonempty p

/-- Coordinate oscillation of a finite density. -/
def transportOscillation (p : ι → ℝ) : ℝ := transportMax p - transportMin p

theorem le_transportMax (p : ι → ℝ) (i : ι) : p i ≤ transportMax p :=
  Finset.le_sup' p (Finset.mem_univ i)

theorem transportMin_le (p : ι → ℝ) (i : ι) : transportMin p ≤ p i :=
  Finset.inf'_le p (Finset.mem_univ i)

theorem transportOscillation_nonneg (p : ι → ℝ) : 0 ≤ transportOscillation p := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact sub_nonneg.mpr ((transportMin_le p i).trans (le_transportMax p i))

/-- Complete mixing coefficients with a lower edge-conductance bound constructed algebraically. -/
def mixingCoefficients (a : ι → ι → ℝ) (i j : ι) : ℝ := 1 + a i j ^ 2

omit [Fintype ι] [Nonempty ι] in
theorem mixingConductance_lower (a : ι → ι → ℝ) (i j : ι) :
    2 ≤ entropyConductance (mixingCoefficients a) i j := by
  unfold entropyConductance mixingCoefficients
  nlinarith [sq_nonneg (a i j), sq_nonneg (a j i), sq_nonneg (a i j ^ 2), sq_nonneg (a j i ^ 2)]

/-- Nonnegative time steps with a constructed lower bound of one. -/
def mixingStep (u : ℝ) : ℝ≥0 := ⟨1 + u ^ 2, by positivity⟩

/-- Total mass of the positive reference density. -/
def transportReferenceMass (r : ι → ℝ) : ℝ := ∑ i, Real.exp (r i)

theorem transportReferenceMass_pos (r : ι → ℝ) : 0 < transportReferenceMass r := by
  exact Finset.sum_pos (fun i _ => Real.exp_pos (r i)) Finset.univ_nonempty

omit [Nonempty ι] in
theorem exp_le_transportReferenceMass (r : ι → ℝ) (i : ι) :
    Real.exp (r i) ≤ transportReferenceMass r :=
  Finset.single_le_sum (fun j _ => (Real.exp_pos (r j)).le) (Finset.mem_univ i)

/-- A common contraction factor, independent of all raw network coefficients and step parameters. -/
def transportContraction (r : ι → ℝ) : ℝ :=
  transportReferenceMass r / (transportReferenceMass r + 2)

theorem transportContraction_nonneg (r : ι → ℝ) : 0 ≤ transportContraction r := by
  unfold transportContraction
  positivity [transportReferenceMass_pos r]

theorem transportContraction_lt_one (r : ι → ℝ) : transportContraction r < 1 := by
  unfold transportContraction
  have h := transportReferenceMass_pos r
  exact (div_lt_one (by linarith)).mpr (by linarith)

/-- The maximum principle confines every inverse density coordinate to the input interval. -/
theorem densityImplicitStep_interval (a : ι → ι → ℝ) (r p : ι → ℝ) (t : ℝ≥0) (i : ι) :
    transportMin p ≤ densityImplicitStep a r t p i ∧
      densityImplicitStep a r t p i ≤ transportMax p := by
  obtain ⟨j, k, hj, hk⟩ := densityImplicitStep_extrema a r p t i
  exact ⟨(transportMin_le p j).trans hj, hk.trans (le_transportMax p k)⟩

/-- Uniform contraction of density oscillation for arbitrary complete mixing and arbitrary raw time. -/
theorem densityImplicitStep_oscillation_contract (a : ι → ι → ℝ) (r p : ι → ℝ) (u : ℝ) :
    transportOscillation (densityImplicitStep (mixingCoefficients a) r (mixingStep u) p) ≤
      transportContraction r * transportOscillation p := by
  classical
  let y := densityImplicitStep (mixingCoefficients a) r (mixingStep u) p
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty y
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty y
  have hyj : transportMax y = y j := hj
  have hyk : transportMin y = y k := hk
  have hdelta : 0 ≤ y j - y k := by
    have h := transportOscillation_nonneg y
    simpa only [transportOscillation, hyj, hyk] using h
  let d := ∑ l, entropyConductance (mixingCoefficients a) j l * (y j - y l)
  have hterms : ∀ l, 0 ≤ entropyConductance (mixingCoefficients a) j l * (y j - y l) := by
    intro l
    exact mul_nonneg (entropyConductance_nonneg _ _ _)
      (sub_nonneg.mpr (by simpa only [hyj] using le_transportMax y l))
  have hd : 2 * (y j - y k) ≤ d := by
    exact (mul_le_mul_of_nonneg_right (mixingConductance_lower a j k) hdelta).trans
      (Finset.single_le_sum (fun l _ => hterms l) (Finset.mem_univ k))
  have he := congrFun (densityShift_implicitStep (mixingCoefficients a) r p (mixingStep u)) j
  change y j - (mixingStep u : ℝ) * (Real.exp (-(r j)) *
    ∑ l, entropyConductance (mixingCoefficients a) j l * (y l - y j)) = p j at he
  have hneg : (∑ l, entropyConductance (mixingCoefficients a) j l * (y l - y j)) = -d := by
    simp only [d, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hneg] at he
  have hmul := congrArg (fun z : ℝ => Real.exp (r j) * z) he
  simp only [mul_sub, mul_left_comm (Real.exp (r j)) (mixingStep u : ℝ), ← mul_assoc,
    ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at hmul
  have ht : (1 : ℝ) ≤ mixingStep u := by change 1 ≤ 1 + u ^ 2; nlinarith [sq_nonneg u]
  have hd0 : 0 ≤ d := le_trans (mul_nonneg (by positivity) hdelta) hd
  have htd := mul_le_mul_of_nonneg_right ht hd0
  have hpower : 2 * (y j - y k) ≤ Real.exp (r j) * (p j - y j) := by nlinarith [hmul]
  have hp : 0 ≤ p j - y j := by nlinarith [Real.exp_pos (r j)]
  have hweight := mul_le_mul_of_nonneg_right (exp_le_transportReferenceMass r j) hp
  have hlow : transportMin p ≤ y k := (densityImplicitStep_interval _ r p _ k).1
  have hhigh := le_transportMax p j
  have hmax : p j - y j ≤ transportOscillation p - (y j - y k) := by
    unfold transportOscillation
    linarith
  have hmass := transportReferenceMass_pos r
  have hbound := mul_le_mul_of_nonneg_left hmax hmass.le
  change transportOscillation y ≤ transportContraction r * transportOscillation p
  rw [transportOscillation, hyj, hyk, transportContraction, div_mul_eq_mul_div]
  apply (le_div_iff₀ (by linarith : 0 < transportReferenceMass r + 2)).mpr
  nlinarith

end
end GaloisForLFunctions.HTGeometry.SchafferExl
