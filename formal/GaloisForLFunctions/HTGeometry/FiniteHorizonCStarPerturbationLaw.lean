import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Finite-horizon perturbation law in a C⋆-algebra

This module proves an operator-norm Duhamel bound without finite-dimensional,
matrix, spectral, or commutativity assumptions.  Two skew-adjoint generators
whose norm distance is `δ` produce unitary evolutions at distance at most
`|t| δ`.  Conjugating an arbitrary observable costs at most the sharp
two-sided factor `2`.

Consequently, detecting a fixed observable separation between two
self-adjoint Hamiltonians requires observation time inversely proportional
to their norm distance.  This is the finite-horizon half of the singular
recurrence programme: exact long-time recurrent geometry may change at
arbitrarily weak coupling, while every bounded-time operator-norm
observation remains continuous in that coupling.
-/

open NormedSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [CStarAlgebra A]

/-- **C⋆ Duhamel perturbation bound.** Exponentiation is `|t|`-Lipschitz on
skew-adjoint generators.  No finite-dimensional or spectral hypothesis is
used. -/
theorem exp_skewAdjoint_sub_exp_skewAdjoint_norm_le
    (x y : A) (hx : x ∈ skewAdjoint A) (hy : y ∈ skewAdjoint A) (t : ℝ) :
    ‖exp (t • x) - exp (t • y)‖ ≤ |t| * ‖x - y‖ := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  let f : ℝ → A :=
    fun s => exp (t • x) * exp (s • (-x)) * exp (s • y)
  let f' : ℝ → A :=
    fun s => exp (t • x) * exp (s • (-x)) * (y - x) * exp (s • y)
  have hf (s : ℝ) : HasDerivAt f (f' s) s := by
    dsimp only [f, f']
    have h :=
      (hasDerivAt_exp_smul_const (-x) s).const_mul
        (exp (t • x)) |>.mul
          (hasDerivAt_exp_smul_const' y s)
    convert h using 1
    · funext r
      simp only [Pi.mul_apply, smul_neg]
    · noncomm_ring
  have hf_deriv : deriv f = f' := by
    funext s
    exact (hf s).deriv
  have hf'_continuous : Continuous f' := by
    dsimp only [f']
    fun_prop
  have h_integral :
      (∫ s : ℝ in 0..t, f' s) = exp (t • y) - exp (t • x) := by
    have hftc :=
      intervalIntegral.integral_deriv_eq_sub' (a := 0) (b := t) f hf_deriv
        (fun s _ => (hf s).differentiableAt) hf'_continuous.continuousOn
    have hf_zero : f 0 = exp (t • x) := by
      simp [f]
    have hf_t : f t = exp (t • y) := by
      dsimp only [f]
      have hcancel : exp (t • x) * exp (t • (-x)) = (1 : A) := by
        rw [smul_neg, ← NormedSpace.exp_add_of_commute (Commute.refl (t • x)).neg_right]
        simp
      rw [hcancel, one_mul]
    simpa only [hf_t, hf_zero] using hftc
  have hf'_norm (s : ℝ) : ‖f' s‖ = ‖y - x‖ := by
    dsimp only [f']
    have hutx : exp (t • x) ∈ unitary A :=
      NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem t hx)
    have husx : exp (s • (-x)) ∈ unitary A :=
      NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
        (by simpa [smul_neg, neg_smul] using skewAdjoint.smul_mem (-s) hx)
    have husy : exp (s • y) ∈ unitary A :=
      NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem s hy)
    simp only [mul_assoc]
    rw [CStarRing.norm_mem_unitary_mul _ hutx,
      CStarRing.norm_mem_unitary_mul _ husx,
      CStarRing.norm_mul_mem_unitary _ husy]
  calc
    ‖exp (t • x) - exp (t • y)‖ =
        ‖exp (t • y) - exp (t • x)‖ := norm_sub_rev _ _
    _ = ‖∫ s : ℝ in 0..t, f' s‖ := by rw [h_integral]
    _ ≤ ‖y - x‖ * |t - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (fun s _ => (hf'_norm s).le)
    _ = |t| * ‖x - y‖ := by rw [sub_zero, norm_sub_rev, mul_comm]

/-- Self-adjoint Hamiltonian form of the C⋆ Duhamel bound. -/
theorem selfAdjoint_unitaryEvolution_norm_sub_le
    (H K : A) (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K) (t : ℝ) :
    ‖exp (t • ((-Complex.I) • H)) - exp (t • ((-Complex.I) • K))‖
      ≤ |t| * ‖H - K‖ := by
  have hx : (-Complex.I) • H ∈ skewAdjoint A := by
    rw [skewAdjoint.mem_iff, star_smul, hH.star_eq]
    simp
  have hy : (-Complex.I) • K ∈ skewAdjoint A := by
    rw [skewAdjoint.mem_iff, star_smul, hK.star_eq]
    simp
  have hnorm : ‖(-Complex.I) • H - (-Complex.I) • K‖ = ‖H - K‖ := by
    rw [← smul_sub, norm_smul]
    simp
  simpa only [hnorm] using
    exp_skewAdjoint_sub_exp_skewAdjoint_norm_le
      ((-Complex.I) • H) ((-Complex.I) • K) hx hy t

/-- Operator-normalized conjugation bound for two arbitrary unitary
elements.  It avoids Hilbert--Schmidt normalization and dimension factors. -/
theorem unitary_conjugation_norm_sub_le
    (U V O : A) (hU : U ∈ unitary A) (hV : V ∈ unitary A) :
    ‖U * O * star U - V * O * star V‖ ≤ 2 * ‖U - V‖ * ‖O‖ := by
  have hsplit :
      U * O * star U - V * O * star V =
        (U - V) * O * star U + V * O * (star U - star V) := by
    noncomm_ring
  rw [hsplit]
  calc
    ‖(U - V) * O * star U + V * O * (star U - star V)‖
        ≤ ‖(U - V) * O * star U‖ +
          ‖V * O * (star U - star V)‖ := norm_add_le _ _
    _ = ‖(U - V) * O‖ + ‖O * (star U - star V)‖ := by
      rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hU),
        mul_assoc, CStarRing.norm_mem_unitary_mul _ hV]
    _ ≤ ‖U - V‖ * ‖O‖ + ‖O‖ * ‖star U - star V‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖U - V‖ * ‖O‖ := by
      rw [← star_sub, norm_star]
      ring

/-- **Finite-horizon observable stability law.** Every operator-norm
observable is uniformly stable under a Hamiltonian perturbation.  The bound
is independent of Hilbert-space dimension and therefore applies directly in
arbitrary unital C⋆-algebras. -/
theorem selfAdjoint_heisenbergEvolution_norm_sub_le
    (H K O : A) (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K) (t : ℝ) :
    ‖exp (t • ((-Complex.I) • H)) * O *
          star (exp (t • ((-Complex.I) • H))) -
        exp (t • ((-Complex.I) • K)) * O *
          star (exp (t • ((-Complex.I) • K)))‖
      ≤ 2 * |t| * ‖H - K‖ * ‖O‖ := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  let U : A := exp (t • ((-Complex.I) • H))
  let V : A := exp (t • ((-Complex.I) • K))
  have hx : (-Complex.I) • H ∈ skewAdjoint A := by
    rw [skewAdjoint.mem_iff, star_smul, hH.star_eq]
    simp
  have hy : (-Complex.I) • K ∈ skewAdjoint A := by
    rw [skewAdjoint.mem_iff, star_smul, hK.star_eq]
    simp
  have hU : U ∈ unitary A := by
    dsimp only [U]
    exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
      (skewAdjoint.smul_mem t hx)
  have hV : V ∈ unitary A := by
    dsimp only [V]
    exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
      (skewAdjoint.smul_mem t hy)
  have hevolution : ‖U - V‖ ≤ |t| * ‖H - K‖ := by
    simpa only [U, V] using
      selfAdjoint_unitaryEvolution_norm_sub_le H K hH hK t
  change ‖U * O * star U - V * O * star V‖ ≤
    2 * |t| * ‖H - K‖ * ‖O‖
  calc
    ‖U * O * star U - V * O * star V‖
        ≤ 2 * ‖U - V‖ * ‖O‖ :=
      unitary_conjugation_norm_sub_le U V O hU hV
    _ ≤ 2 * (|t| * ‖H - K‖) * ‖O‖ := by
      gcongr
    _ = 2 * |t| * ‖H - K‖ * ‖O‖ := by ring

/-- **Distinguishability-time lower bound.** If an observable separates two
Hamiltonian evolutions by at least `ε`, then the observation time must be at
least `ε / (2 ‖H-K‖ ‖O‖)`. -/
theorem selfAdjoint_distinguishability_time_lowerBound
    (H K O : A) (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K)
    (t ε : ℝ) (hHK : 0 < ‖H - K‖) (hO : 0 < ‖O‖)
    (hdetect :
      ε ≤
        ‖exp (t • ((-Complex.I) • H)) * O *
              star (exp (t • ((-Complex.I) • H))) -
            exp (t • ((-Complex.I) • K)) * O *
              star (exp (t • ((-Complex.I) • K)))‖) :
    ε / (2 * ‖H - K‖ * ‖O‖) ≤ |t| := by
  have hupper :=
    selfAdjoint_heisenbergEvolution_norm_sub_le H K O hH hK t
  have hε : ε ≤ 2 * |t| * ‖H - K‖ * ‖O‖ :=
    hdetect.trans hupper
  have hden : 0 < 2 * ‖H - K‖ * ‖O‖ := by positivity
  rw [div_le_iff₀ hden]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hε

end

end GaloisForLFunctions.HTGeometry
