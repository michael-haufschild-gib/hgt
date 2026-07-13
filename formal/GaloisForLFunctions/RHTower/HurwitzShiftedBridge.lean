import GaloisForLFunctions.RHTower.LogIndependence
import GaloisForLFunctions.RHTower.ShiftedMultIndependence
import GaloisForLFunctions.HTGeometry.Hypertranscendence
import Mathlib.NumberTheory.LSeries.HurwitzZeta

/-!
# The Hurwitz zeta function as a field of ℚ-independent shifted exponential monomials

Mathlib's `hasSum_hurwitzZeta_of_one_lt_re` expresses the Hurwitz zeta `ζ(a, s)` as the Dirichlet
series `∑ₙ 1/(n+a)^s` on `Re s > 1`.  Each coefficient `1/(n+a)^s` is a **shifted exponential
monomial** `exp(−s · log(n+a))` with frequency `log(n+a)`.  For a transcendental shift `a`, those
frequencies are `ℚ`-linearly independent (`LogIndependence.log_shifts_independent`).  So the actual
Hurwitz L-function is a superposition of exponential monomials whose frequencies carry no rational
relation — the value-theoretic genericity that underlies its universality, tied to the concrete
mathlib object.
-/

open Complex HurwitzZeta

namespace RHTower

/-- **The Hurwitz-zeta coefficient is a shifted exponential monomial.**  For `a > 0`, the `n`-th
Dirichlet coefficient `1/(n+a)^s` of the Hurwitz zeta equals `exp(−s · log(n+a))`: an exponential
monomial with frequency `log(n+a)`. -/
theorem hurwitzZeta_summand_eq_shifted_exp {a : ℝ} (h0 : 0 < a) (n : ℕ) (s : ℂ) :
    1 / ((n : ℂ) + a) ^ s = Complex.exp (-s * (Real.log ((n : ℝ) + a) : ℂ)) := by
  have hpos : (0 : ℝ) < (n : ℝ) + a := by positivity
  have hne : ((n : ℂ) + a) ≠ 0 := by
    have : ((n : ℂ) + a) = (((n : ℝ) + a : ℝ) : ℂ) := by push_cast; ring
    rw [this]; exact_mod_cast ne_of_gt hpos
  rw [one_div, ← Complex.cpow_neg, Complex.cpow_def_of_ne_zero hne]
  congr 1
  rw [show ((n : ℂ) + a) = (((n : ℝ) + a : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_log hpos.le]
  ring

/-- **The Hurwitz zeta is a sum of shifted exponential monomials.**  On `Re s > 1`, for a shift
`a ∈ (0,1]`, `ζ(a, s) = ∑ₙ exp(−s · log(n+a))`: the Hurwitz L-function is the superposition of the
exponential monomials with frequencies `log(n+a)`. -/
theorem hasSum_hurwitzZeta_shifted_exp {a : ℝ} (h0 : 0 < a) (ha1 : a ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => Complex.exp (-s * (Real.log ((n : ℝ) + a) : ℂ)))
      (hurwitzZeta (a : UnitAddCircle) s) := by
  have hm := hasSum_hurwitzZeta_of_one_lt_re (Set.mem_Icc.mpr ⟨h0.le, ha1⟩) hs
  refine hm.congr_fun (fun n => ?_)
  exact (hurwitzZeta_summand_eq_shifted_exp h0 n s).symm

/-- **The Hurwitz-zeta frequencies are `ℚ`-independent for a transcendental shift.**  The frequencies
`log(n+a)` of the Hurwitz-zeta Dirichlet series (`hasSum_hurwitzZeta_shifted_exp`) admit no nontrivial
integer linear relation when `a > 0` is transcendental: `∑ kₙ log(n+a) = 0 ⟹ kₙ = 0`.  The exponential
monomials composing `ζ(a, ·)` have rationally independent frequencies. -/
theorem hurwitzZeta_frequencies_ratIndependent {a : ℝ} (h0 : 0 < a) (ha : Transcendental ℚ a)
    (s : Finset ℕ) (k : ℕ → ℤ) (hrel : ∑ n ∈ s, (k n : ℝ) * Real.log ((n : ℝ) + a) = 0) :
    ∀ n ∈ s, k n = 0 :=
  log_shifts_independent h0 ha s k hrel

open Filter Topology in
/-- **Mean square of the Hurwitz-zeta truncation (Parseval).**  For `a > 0`, on the vertical line
`Re s = σ`, the Cesàro time average of `|ζ_N(a, σ+it)|²` (the modulus square of the `N`-term truncation
`∑_{n∈s} (n+a)^{−σ−it}`) converges to `∑_{n∈s} (n+a)^{−2σ}` — the diagonal, since the shifted
frequencies `log(n+a)` are distinct.  Parseval's identity for the actual Hurwitz L-function's partial
sums. -/
theorem hurwitzZeta_truncation_meanSquare {a : ℝ} (h0 : 0 < a) (σ : ℝ) (s : Finset ℕ) :
    Tendsto (fun T : ℝ => (↑T)⁻¹ * ∫ t in (0 : ℝ)..T,
        ((Complex.normSq (∑ n ∈ s,
            Complex.exp (-((σ : ℂ) + (t : ℂ) * Complex.I) * (Real.log ((n : ℝ) + a) : ℂ))) : ℝ) : ℂ))
      atTop
      (𝓝 (∑ n ∈ s,
        ((Complex.normSq (Complex.exp (-(σ : ℂ) * (Real.log ((n : ℝ) + a) : ℂ))) : ℝ) : ℂ))) := by
  have key := shifted_dirichlet_meanValue h0 s
    (fun n => Complex.exp (-(σ : ℂ) * (Real.log ((n : ℝ) + a) : ℂ)))
  have hint : ∀ t : ℝ,
      ((Complex.normSq (∑ n ∈ s,
          Complex.exp (-((σ : ℂ) + (t : ℂ) * Complex.I) * (Real.log ((n : ℝ) + a) : ℂ))) : ℝ) : ℂ)
      = ∑ p ∈ s ×ˢ s,
          (Complex.exp (-(σ : ℂ) * (Real.log ((p.1 : ℝ) + a) : ℂ))
            * (starRingEnd ℂ) (Complex.exp (-(σ : ℂ) * (Real.log ((p.2 : ℝ) + a) : ℂ))))
          * Complex.exp (((Real.log ((p.2 : ℝ) + a) - Real.log ((p.1 : ℝ) + a) : ℝ) : ℂ)
              * Complex.I * ↑t) := by
    intro t
    rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_congr rfl (fun p _ => ?_)
    simp only [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, map_neg, map_add, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  simp_rw [hint]
  exact key

open Filter Topology in
/-- **The Hurwitz-zeta truncation has zero vertical mean.**  For `a > 0` with `a ≠ 1`, the Cesàro time
average of the truncation `ζ_N(a, σ+it) = ∑_{n∈s} (n+a)^{−σ−it}` converges to `0`: every frequency
`log(n+a)` is nonzero (as `n+a ≠ 1`), so no term contributes a mean.  Together with
`hurwitzZeta_truncation_meanSquare` this gives the variance of the truncation's vertical fluctuation. -/
theorem hurwitzZeta_truncation_mean_zero {a : ℝ} (h0 : 0 < a) (ha1 : a ≠ 1) (σ : ℝ) (s : Finset ℕ) :
    Tendsto (fun T : ℝ => (↑T)⁻¹ * ∫ t in (0 : ℝ)..T,
        ∑ n ∈ s, Complex.exp (-((σ : ℂ) + (t : ℂ) * Complex.I) * (Real.log ((n : ℝ) + a) : ℂ)))
      atTop (𝓝 0) := by
  have key := Weyl.trig_time_average s (fun n => -Real.log ((n : ℝ) + a))
    (fun n => Complex.exp (-(σ : ℂ) * (Real.log ((n : ℝ) + a) : ℂ)))
  have hfilter : s.filter (fun n : ℕ => -Real.log ((n : ℝ) + a) = 0) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro n _ hlog
    have hpos : (0 : ℝ) < (n : ℝ) + a := by positivity
    have hne1 : (n : ℝ) + a ≠ 1 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simpa using ha1
      · have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
        linarith
    have hl : Real.log ((n : ℝ) + a) = 0 := by linarith
    have hexp := Real.exp_log hpos
    rw [hl, Real.exp_zero] at hexp
    exact hne1 hexp.symm
  rw [hfilter, Finset.sum_empty] at key
  have hint : ∀ t : ℝ,
      (∑ n ∈ s, Complex.exp (-((σ : ℂ) + (t : ℂ) * Complex.I) * (Real.log ((n : ℝ) + a) : ℂ)))
      = ∑ n ∈ s, Complex.exp (-(σ : ℂ) * (Real.log ((n : ℝ) + a) : ℂ))
          * Complex.exp (((-Real.log ((n : ℝ) + a) : ℝ) : ℂ) * Complex.I * ↑t) := by
    intro t
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [← Complex.exp_add]
    congr 1
    push_cast; ring
  simp_rw [hint]
  exact key

/-- **Each Hurwitz monomial is differentially algebraic.**  The `n`-th coefficient function
`s ↦ exp(−s·log(n+a)) = (n+a)^{−s}` satisfies the linear ODE `y' + log(n+a)·y = 0`, so it is
differentially algebraic (`GaloisForLFunctions.differentiallyAlgebraic_cexp_linear`).  Hence, by
`hasSum_hurwitzZeta_shifted_exp`, the Hurwitz zeta `ζ(a, ·)` is an infinite superposition of
differentially algebraic monomials.  Whether that infinite sum leaves the differentially-algebraic
class — i.e. whether `ζ(a, ·)` is hypertranscendental — is the frontier the notion sets up: a field
constant (`log(n+a)`) per term, no generative rule for the whole. -/
theorem differentiallyAlgebraic_hurwitzMonomial {a : ℝ} (n : ℕ) :
    GaloisForLFunctions.DifferentiallyAlgebraic
      (fun s => Complex.exp (-s * (Real.log ((n : ℝ) + a) : ℂ))) := by
  have h := GaloisForLFunctions.differentiallyAlgebraic_cexp_linear
    (-(Real.log ((n : ℝ) + a) : ℂ))
  have heq : (fun s => Complex.exp (-s * (Real.log ((n : ℝ) + a) : ℂ)))
      = (fun s : ℂ => Complex.exp (-(Real.log ((n : ℝ) + a) : ℂ) * s)) := by
    funext s; congr 1; ring
  rw [heq]; exact h

end RHTower
