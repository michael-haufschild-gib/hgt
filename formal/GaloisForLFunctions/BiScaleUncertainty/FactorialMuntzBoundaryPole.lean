import GaloisForLFunctions.BiScaleUncertainty.ClampedRampLatticeSum
import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzCompletion

/-! The exact negative-end boundary coefficient of the actual Müntz completion.
Zero mean cancels the reciprocal sampling scale, but its endpoint half survives. -/

open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open GaloisForLFunctions.RHTower
noncomputable section
set_option autoImplicit false

theorem factorialMuntzSum_eq_clampedLattice (n : ℕ) {t : ℝ} (ht : 0 < t) :
    factorialMuntzSum n t =
      clampedLatticeSum (sourceFactorialCollar (n+1)) (4*((n+1 : ℕ) : ℝ)) t-
      4*clampedLatticeSum (sourceFactorialCollar (n+1)) (2*((n+1 : ℕ) : ℝ)) t+
      4*clampedLatticeSum (sourceFactorialCollar (n+1)) ((n+1 : ℕ) : ℝ) t := by
  have hε := sourceFactorialCollar_pos (N := n+1) (by omega)
  have h4 := summable_clampedRamp_dilate hε
    (show 0 < 4*((n+1 : ℕ) : ℝ) by positivity) ht
  have h2 := summable_clampedRamp_dilate hε
    (show 0 < 2*((n+1 : ℕ) : ℝ) by positivity) ht
  have h1 := summable_clampedRamp_dilate hε
    (show 0 < ((n+1 : ℕ) : ℝ) by positivity) ht
  calc
    _ = ∑' k : ℕ,
        (clampedRamp (sourceFactorialCollar (n+1)) (((k : ℝ)+1)*t/(4*((n+1 : ℕ) : ℝ)))-
        4*clampedRamp (sourceFactorialCollar (n+1)) (((k : ℝ)+1)*t/(2*((n+1 : ℕ) : ℝ)))+
        4*clampedRamp (sourceFactorialCollar (n+1)) (((k : ℝ)+1)*t/((n+1 : ℕ) : ℝ))) := by
      unfold factorialMuntzSum arithmeticSum
      apply tsum_congr
      intro k
      exact factorialMuntzSeed_of_pos n (by positivity)
    _ = _ := by
      unfold clampedLatticeSum
      rw [(h4.sub (h2.mul_left 4)).tsum_add (h1.mul_left 4),
        h4.tsum_sub (h2.mul_left 4), tsum_mul_left, tsum_mul_left]

/-- Quantitative endpoint asymptotic of the literal arithmetic sum, with every
integer sampling endpoint included exactly. -/
theorem factorialMuntzSum_boundary_error (n : ℕ) {t : ℝ} (ht : 0 < t) :
    |factorialMuntzSum n t+1/2| ≤
      25*t/(32*((n+1 : ℕ) : ℝ)*sourceFactorialCollar (n+1)) := by
  let N : ℝ := ((n+1 : ℕ) : ℝ)
  let ε := sourceFactorialCollar (n+1)
  have hN : 0 < N := by dsimp [N]; positivity
  have hε : 0 < ε := sourceFactorialCollar_pos (N := n+1) (by omega)
  let e : ℝ → ℝ := fun a => clampedLatticeSum ε a t-(a*(1+ε/2)/t-1/2)
  have h4 : |e (4*N)| ≤ t/(8*(4*N)*ε) :=
    clampedLatticeSum_error_le hε (by positivity) ht
  have h2 : |e (2*N)| ≤ t/(8*(2*N)*ε) :=
    clampedLatticeSum_error_le hε (by positivity) ht
  have h1 : |e N| ≤ t/(8*N*ε) := clampedLatticeSum_error_le hε hN ht
  have he : factorialMuntzSum n t+1/2 = e (4*N)-4*e (2*N)+4*e N := by
    rw [factorialMuntzSum_eq_clampedLattice n ht]
    dsimp [e, N, ε]
    ring
  rw [he]
  calc
    _ ≤ |e (4*N)-4*e (2*N)|+|4*e N| := _root_.abs_add_le _ _
    _ ≤ (|e (4*N)|+|4*e (2*N)|)+|4*e N| := by
      linarith only [abs_sub (e (4*N)) (4*e (2*N))]
    _ = |e (4*N)|+4*|e (2*N)|+4*|e N| := by rw [abs_mul, abs_mul]; norm_num
    _ ≤ t/(8*(4*N)*ε)+4*(t/(8*(2*N)*ε))+4*(t/(8*N*ε)) := by
      linarith only [h4, h2, h1]
    _ = 25*t/(32*N*ε) := by field_simp <;> ring

def factorialMuntzBoundaryCoefficient (n : ℕ) : ℝ :=
  1/(2*Real.sqrt ((n+1 : ℕ) : ℝ))

def factorialMuntzBoundaryError (n : ℕ) : ℝ :=
  25/(32*((n+1 : ℕ) : ℝ)*sourceFactorialCollar (n+1)*Real.sqrt ((n+1 : ℕ) : ℝ))

theorem factorialMuntzBoundaryCoefficient_pos (n : ℕ) :
    0 < factorialMuntzBoundaryCoefficient n := by
  unfold factorialMuntzBoundaryCoefficient
  positivity

theorem factorialMuntzBoundaryError_pos (n : ℕ) : 0 < factorialMuntzBoundaryError n := by
  have hε := sourceFactorialCollar_pos (N := n+1) (by omega)
  unfold factorialMuntzBoundaryError
  positivity

theorem factorialMuntzCompletion_boundary_error (n : ℕ) (x : ℝ) :
    |Real.exp (-x/2)*factorialMuntzCompletion n x+factorialMuntzBoundaryCoefficient n| ≤
      factorialMuntzBoundaryError n*Real.exp x := by
  have hs : 0 < Real.sqrt ((n+1 : ℕ) : ℝ) := by positivity
  have hε := sourceFactorialCollar_pos (N := n+1) (by omega)
  have he : Real.exp (-x/2)*factorialMuntzCompletion n x+factorialMuntzBoundaryCoefficient n =
      (factorialMuntzSum n (Real.exp x)+1/2)/Real.sqrt ((n+1 : ℕ) : ℝ) := by
    unfold factorialMuntzCompletion factorialMuntzBoundaryCoefficient
    rw [← mul_div_assoc, ← mul_assoc, ← Real.exp_add,
      show -x/2+x/2 = 0 by ring, Real.exp_zero, one_mul]
    field_simp
  rw [he, abs_div, abs_of_pos hs]
  calc
    _ ≤ (25*Real.exp x/(32*((n+1 : ℕ) : ℝ)*sourceFactorialCollar (n+1)))/
        Real.sqrt ((n+1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right (factorialMuntzSum_boundary_error n (Real.exp_pos x)) hs.le
    _ = _ := by unfold factorialMuntzBoundaryError; field_simp

/-- The actual completion retains a nonzero negative-end polar coefficient. -/
theorem factorialMuntzCompletion_boundary_tendsto (n : ℕ) :
    Tendsto (fun x : ℝ => Real.exp (-x/2)*factorialMuntzCompletion n x) atBot
      (𝓝 (-factorialMuntzBoundaryCoefficient n)) := by
  have hz : Tendsto (fun x : ℝ =>
      Real.exp (-x/2)*factorialMuntzCompletion n x+factorialMuntzBoundaryCoefficient n)
      atBot (𝓝 0) := by
    have hb : Tendsto (fun x : ℝ => factorialMuntzBoundaryError n*Real.exp x)
        atBot (𝓝 0) := by
      simpa using Real.tendsto_exp_atBot.const_mul (factorialMuntzBoundaryError n)
    exact squeeze_zero_norm (a := fun x : ℝ => factorialMuntzBoundaryError n*Real.exp x)
      (fun x => by simpa only [Real.norm_eq_abs] using factorialMuntzCompletion_boundary_error n x) hb
  have hc : Tendsto (fun _ : ℝ => factorialMuntzBoundaryCoefficient n) atBot
      (𝓝 (factorialMuntzBoundaryCoefficient n)) := tendsto_const_nhds
  simpa using hz.sub hc

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
