import GaloisForLFunctions.HTGeometry.HermiteOscillatorContinuity

/-!
# The Hermite polynomials span, and the vanishing of Gaussian moments

Each step of the Hermite recursion multiplies by `2X` and subtracts a multiple of the derivative,
which has strictly smaller degree.  So the `n`-th Hermite polynomial has degree `n` and leading
coefficient `2ⁿ`, and a triangular argument shows that the Hermite polynomials span the polynomial
ring.

Consequently a Schwartz function orthogonal to every Hermite function is orthogonal to every
polynomial multiple of the Gaussian: all of its Gaussian moments vanish.  That is the first step
of the completeness of the Hermite system.

* `hermitePoly_degree`, `hermitePoly_leadingCoeff` : degree `n`, leading coefficient `2ⁿ`.
* `hermitePoly_span_eq_top` : **the Hermite polynomials span the polynomial ring.**
* `schwartzPair_polyGauss_eq_zero` : **orthogonal to every Hermite function means every Gaussian
  moment vanishes.**
-/

open scoped Real SchwartzMap
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

/-! ## Degree and leading coefficient -/

theorem hermitePoly_degree_leadingCoeff (n : ℕ) :
    (hermitePoly n).degree = (n : WithBot ℕ) ∧ (hermitePoly n).leadingCoeff = 2 ^ n := by
  induction n with
  | zero => exact ⟨by simp, by simp⟩
  | succ n ih =>
    obtain ⟨hdeg, hlc⟩ := ih
    have hne : hermitePoly n ≠ 0 := by
      intro h
      rw [h, Polynomial.leadingCoeff_zero] at hlc
      exact (pow_ne_zero n (two_ne_zero : (2 : ℝ) ≠ 0)) hlc.symm
    have hXdeg : (2 * Polynomial.X * hermitePoly n).degree = (n : WithBot ℕ) + 1 := by
      have h2c : (2 : Polynomial ℝ) = Polynomial.C 2 := (map_ofNat Polynomial.C 2).symm
      have h2 : ((2 : Polynomial ℝ) * Polynomial.X).degree = 1 := by
        rw [h2c, Polynomial.degree_C_mul (two_ne_zero : (2 : ℝ) ≠ 0), Polynomial.degree_X]
      rw [Polynomial.degree_mul, h2, hdeg, add_comm]
    have hDderiv : (Polynomial.C (1 / (2 * π)) * (hermitePoly n).derivative).degree
        < (n : WithBot ℕ) + 1 := by
      refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
      refine lt_of_le_of_lt (add_le_add (Polynomial.degree_C_le)
        (le_of_lt (Polynomial.degree_derivative_lt hne))) ?_
      rw [hdeg, zero_add]
      have hcast : ((n : WithBot ℕ) + 1) = ((n + 1 : ℕ) : WithBot ℕ) := by push_cast; ring
      rw [hcast]
      exact_mod_cast Nat.lt_succ_self n
    have hsub : (hermitePoly (n + 1)).degree = (n : WithBot ℕ) + 1 := by
      rw [hermitePoly_succ, hermiteStep,
        Polynomial.degree_sub_eq_left_of_degree_lt (by rw [hXdeg]; exact hDderiv), hXdeg]
    refine ⟨by rw [hsub]; push_cast; ring, ?_⟩
    have hlead : (hermitePoly (n + 1)).leadingCoeff
        = (2 * Polynomial.X * hermitePoly n).leadingCoeff := by
      rw [hermitePoly_succ, hermiteStep, sub_eq_add_neg,
        Polynomial.leadingCoeff_add_of_degree_lt']
      rw [Polynomial.degree_neg, hXdeg]
      exact hDderiv
    rw [hlead, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul, hlc,
      Polynomial.leadingCoeff_X]
    have h2lc : (2 : Polynomial ℝ).leadingCoeff = 2 := by
      rw [show (2 : Polynomial ℝ) = Polynomial.C 2 from (map_ofNat Polynomial.C 2).symm,
        Polynomial.leadingCoeff_C]
    rw [h2lc, pow_succ]
    ring

theorem hermitePoly_degree (n : ℕ) : (hermitePoly n).degree = (n : WithBot ℕ) :=
  (hermitePoly_degree_leadingCoeff n).1

theorem hermitePoly_leadingCoeff (n : ℕ) : (hermitePoly n).leadingCoeff = 2 ^ n :=
  (hermitePoly_degree_leadingCoeff n).2

theorem hermitePoly_coeff_self (n : ℕ) : (hermitePoly n).coeff n = 2 ^ n := by
  have hnat : (hermitePoly n).natDegree = n :=
    Polynomial.natDegree_eq_of_degree_eq_some (hermitePoly_degree n)
  have := hermitePoly_leadingCoeff n
  rwa [Polynomial.leadingCoeff, hnat] at this

theorem hermitePoly_coeff_eq_zero {n m : ℕ} (h : n < m) : (hermitePoly n).coeff m = 0 := by
  refine Polynomial.coeff_eq_zero_of_degree_lt ?_
  rw [hermitePoly_degree]
  exact_mod_cast h

/-! ## The spanning property -/

theorem hermitePoly_mem_span (n : ℕ) :
    hermitePoly n ∈ Submodule.span ℝ (Set.range hermitePoly) :=
  Submodule.subset_span ⟨n, rfl⟩

/-- Every polynomial of degree below `n` lies in the span of the Hermite polynomials, by descending
on the top coefficient. -/
theorem mem_span_hermitePoly_of_degree_lt :
    ∀ (n : ℕ) (p : Polynomial ℝ), p.degree < (n : WithBot ℕ) →
      p ∈ Submodule.span ℝ (Set.range hermitePoly)
  | 0, p, hp => by
    have hp' : p.degree < ((0 : ℕ) : WithBot ℕ) := hp
    rw [Polynomial.degree_lt_iff_coeff_zero] at hp'
    have hzero : p = 0 := by
      refine Polynomial.ext fun m => ?_
      rw [Polynomial.coeff_zero]
      exact hp' m (by exact_mod_cast Nat.zero_le m)
    rw [hzero]
    exact Submodule.zero_mem _
  | (n + 1), p, hp => by
    set c : ℝ := p.coeff n / 2 ^ n with hc
    set q : Polynomial ℝ := p - c • hermitePoly n with hq
    have hdegq : q.degree < (n : WithBot ℕ) := by
      rw [Polynomial.degree_lt_iff_coeff_zero]
      intro m hm
      have hmn : n ≤ m := by exact_mod_cast hm
      rcases eq_or_lt_of_le hmn with rfl | hlt
      · rw [hq, Polynomial.coeff_sub, Polynomial.coeff_smul, hermitePoly_coeff_self, hc,
          smul_eq_mul, div_mul_cancel₀]
        · exact sub_self _
        · exact pow_ne_zero n (two_ne_zero : (2 : ℝ) ≠ 0)
      · have hp1 : p.coeff m = 0 := by
          refine Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hp ?_)
          exact_mod_cast Nat.succ_le_of_lt hlt
        rw [hq, Polynomial.coeff_sub, Polynomial.coeff_smul, hp1,
          hermitePoly_coeff_eq_zero hlt, smul_zero, sub_zero]
    have hqmem := mem_span_hermitePoly_of_degree_lt n q hdegq
    have hp' : p = q + c • hermitePoly n := by
      rw [hq]
      abel
    rw [hp']
    exact Submodule.add_mem _ hqmem (Submodule.smul_mem _ c (hermitePoly_mem_span n))

/-- **The Hermite polynomials span the polynomial ring.** -/
theorem hermitePoly_span_eq_top :
    Submodule.span ℝ (Set.range hermitePoly) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun p => ?_
  refine mem_span_hermitePoly_of_degree_lt (p.natDegree + 1) p ?_
  refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
  exact_mod_cast Nat.lt_succ_self _

/-! ## Vanishing of the Gaussian moments -/

theorem polyGaussSchwartz_add (p q : Polynomial ℝ) :
    polyGaussSchwartz (p + q) = polyGaussSchwartz p + polyGaussSchwartz q := by
  apply SchwartzMap.ext
  intro x
  show (((p + q).eval x * gaussReal x : ℝ) : ℂ)
    = ((p.eval x * gaussReal x : ℝ) : ℂ) + ((q.eval x * gaussReal x : ℝ) : ℂ)
  push_cast
  rw [Polynomial.eval_add]
  push_cast
  ring

theorem polyGaussSchwartz_smul (c : ℝ) (p : Polynomial ℝ) :
    polyGaussSchwartz (c • p) = c • polyGaussSchwartz p := by
  apply SchwartzMap.ext
  intro x
  show (((c • p).eval x * gaussReal x : ℝ) : ℂ) = c • ((p.eval x * gaussReal x : ℝ) : ℂ)
  have hev : (c • p).eval x = c * p.eval x := by simp
  rw [hev, ← Complex.coe_smul]
  push_cast
  ring

/-- The Gaussian multiples of polynomials, as a linear map. -/
def polyGaussLM : Polynomial ℝ →ₗ[ℝ] 𝓢(ℝ, ℂ) where
  toFun := polyGaussSchwartz
  map_add' := polyGaussSchwartz_add
  map_smul' := polyGaussSchwartz_smul

/-- **A Schwartz function orthogonal to every Hermite function has vanishing Gaussian moments**:
its pairing against every polynomial multiple of the Gaussian is zero. -/
theorem schwartzPair_polyGauss_eq_zero {f : 𝓢(ℝ, ℂ)}
    (hf : ∀ n : ℕ, schwartzPair f (hermiteSchwartz n) = 0) (p : Polynomial ℝ) :
    schwartzPair f (polyGaussSchwartz p) = 0 := by
  have hmem : p ∈ Submodule.span ℝ (Set.range hermitePoly) := by
    rw [hermitePoly_span_eq_top]
    exact Submodule.mem_top
  induction hmem using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨n, rfl⟩ := hq
    exact hf n
  | zero =>
    have hzero : polyGaussSchwartz (0 : Polynomial ℝ) = 0 := by
      apply SchwartzMap.ext
      intro x
      show (((0 : Polynomial ℝ).eval x * gaussReal x : ℝ) : ℂ) = 0
      simp
    rw [hzero, schwartzPair_zero_right]
  | add q r _ _ hq hr =>
    rw [polyGaussSchwartz_add, schwartzPair_add_right, hq, hr, add_zero]
  | smul c q _ hq =>
    rw [polyGaussSchwartz_smul, ← Complex.coe_smul, schwartzPair_smul_right, hq, mul_zero]

end GaloisForLFunctions

end
