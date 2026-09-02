import GaloisForLFunctions.RHTower.DirichletUniformAbel
import GaloisForLFunctions.RHTower.MobiusEvenIndexPositiveRecurrence

/-!
# Convergence of the Möbius series forces a zero-free half-plane

If the ordinary Dirichlet series `∑ μ(n) n^{−s}` converges at one point `s₀`, it converges
locally uniformly on `Re s > Re s₀`, so its sum `F` is holomorphic there.  On `Re s > 1` the sum
is `1/ζ`, hence `F(s)·(s − 1)ζ(s) = s − 1`; both sides are analytic on the connected half-plane
`Re s > Re s₀`, so they agree on all of it.  At a zero of `ζ` the left side vanishes, which forces
`s = 1`.  Consequently `ζ` has no zeros in `Re s > Re s₀`, and the abscissa of convergence of the
Möbius series is at least the real part of every nontrivial zero.

This is the precise sense in which the convergent Möbius series inside the critical strip — the
multiplicative completion of `1/ζ` there — already contains the zero-free statement it might be
asked to produce.
-/

open Filter Topology Complex
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- The Möbius coefficients indexed from `1`: the `n`-th coefficient of the ordinary Dirichlet
series `∑ μ(n+1) (n+1)^{−s}`. -/
def moebiusShift (n : ℕ) : ℂ := moebiusCoeffC (n + 1)

/-- Each partial sum of the Möbius Dirichlet series is an entire function of `s`. -/
theorem differentiable_dirichletPartialSum_moebiusShift (N : ℕ) :
    Differentiable ℂ (fun s : ℂ => dirichletPartialSum moebiusShift N s) := by
  have hterm : ∀ n : ℕ,
      Differentiable ℂ (fun s : ℂ => moebiusShift n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) := by
    intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hne : ((((n : ℝ) + 1 : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hpos)
    exact (differentiable_const _).mul (differentiable_neg.const_cpow (Or.inl hne))
  unfold dirichletPartialSum
  exact Differentiable.fun_sum (𝕜 := ℂ) fun n _ => hterm n

/-- On the half-plane of absolute convergence the sum of the shifted series is `1/ζ`. -/
theorem dirichletSum_moebiusShift_mul_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    dirichletSum moebiusShift s * riemannZeta s = 1 := by
  have hsum : LSeriesSummable moebiusCoeffC s :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => norm_moebiusCoeff_le_one n) hs
  have hhas : HasSum (LSeries.term moebiusCoeffC s) (LSeries moebiusCoeffC s) :=
    hsum.LSeriesHasSum
  have hhas' : HasSum (fun n => LSeries.term moebiusCoeffC s (n + 1))
      (LSeries moebiusCoeffC s) := by
    have := (hasSum_nat_add_iff' 1).mpr hhas
    simpa [LSeries.term_zero] using this
  have hterm : ∀ n : ℕ, LSeries.term moebiusCoeffC s (n + 1)
      = moebiusShift n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) := by
    intro n
    have h1 : (n + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero n
    rw [LSeries.term_of_ne_zero h1, moebiusShift, Complex.cpow_neg, div_eq_mul_inv]
    congr 2
    push_cast
    try ring
  have htend : Tendsto (fun N => dirichletPartialSum moebiusShift N s) atTop
      (𝓝 (LSeries moebiusCoeffC s)) := by
    refine hhas'.tendsto_sum_nat.congr fun N => ?_
    unfold dirichletPartialSum
    exact Finset.sum_congr rfl fun n _ => hterm n
  have hconv : DirichletConvergesAt moebiusShift s := ⟨_, htend⟩
  have heq : dirichletSum moebiusShift s = LSeries moebiusCoeffC s :=
    tendsto_nhds_unique (tendsto_dirichletSum hconv) htend
  rw [heq]
  exact LSeries_moebiusCoeff_mul_riemannZeta hs

/-- **Convergence of the Möbius series at one point forces a zero-free half-plane to its
right.** -/
theorem riemannZeta_ne_zero_of_moebius_convergesAt {s₀ : ℂ}
    (h₀ : DirichletConvergesAt moebiusShift s₀) {s : ℂ} (hs : s₀.re < s.re) (hs1 : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  set U : Set ℂ := {z : ℂ | s₀.re < z.re} with hUdef
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected U := (convex_decayHalfPlane s₀.re).isPreconnected
  have hF : DifferentiableOn ℂ (dirichletSum moebiusShift) U := by
    refine (tendstoLocallyUniformlyOn_dirichletPartialSum h₀).differentiableOn ?_ hUopen
    exact Eventually.of_forall fun N =>
      (differentiable_dirichletPartialSum_moebiusShift N).differentiableOn
  have hF1 : AnalyticOnNhd ℂ (fun z : ℂ => dirichletSum moebiusShift z * zetaEntire z) U :=
    (hF.mul differentiable_zetaEntire.differentiableOn).analyticOnNhd hUopen
  have hF2 : AnalyticOnNhd ℂ (fun z : ℂ => z - 1) U :=
    ((differentiable_id.sub_const (1 : ℂ)).differentiableOn).analyticOnNhd hUopen
  set x₁ : ℝ := max 2 (s₀.re + 1) with hx₁
  have hx₁U : (x₁ : ℂ) ∈ U := by
    show s₀.re < (x₁ : ℂ).re
    rw [Complex.ofReal_re, hx₁]
    exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hagree : (fun z : ℂ => dirichletSum moebiusShift z * zetaEntire z)
      =ᶠ[𝓝 (x₁ : ℂ)] fun z : ℂ => z - 1 := by
    have hV : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hx₁V : (x₁ : ℂ) ∈ {z : ℂ | 1 < z.re} := by
      show 1 < (x₁ : ℂ).re
      rw [Complex.ofReal_re, hx₁]
      exact lt_of_lt_of_le one_lt_two (le_max_left _ _)
    filter_upwards [hV.mem_nhds hx₁V] with z hz
    have hz1 : 1 < z.re := hz
    have hzne : z ≠ 1 := by
      intro h
      rw [h] at hz1
      simp at hz1
    rw [zetaEntire_eq hzne]
    have := dirichletSum_moebiusShift_mul_riemannZeta hz1
    linear_combination (z - 1) * this
  have heq := hF1.eqOn_of_preconnected_of_eventuallyEq hF2 hUconn hx₁U hagree
  intro hzero
  have hval := heq (show s ∈ U from hs)
  simp only at hval
  rw [zetaEntire_eq hs1, hzero, mul_zero, mul_zero] at hval
  exact hs1 (by linear_combination -hval)

/-- **The abscissa of convergence of the Möbius series is at least the real part of every
zero of `ζ`.** -/
theorem re_le_abscissaOfConv_moebiusShift {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hρ1 : ρ ≠ 1) :
    (ρ.re : EReal) ≤ abscissaOfConv moebiusShift := by
  unfold abscissaOfConv
  refine le_sInf ?_
  rintro _ ⟨x, hx, rfl⟩
  by_contra hlt
  push Not at hlt
  have hxr : x < ρ.re := by exact_mod_cast hlt
  exact riemannZeta_ne_zero_of_moebius_convergesAt hx (by simpa using hxr) hρ1 hρ

end

end RHTower
