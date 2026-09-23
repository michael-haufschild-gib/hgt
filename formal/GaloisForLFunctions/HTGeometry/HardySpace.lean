import GaloisForLFunctions.HTGeometry.RieszBrothersRieszFischer
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Analytic.Basic
open MeasureTheory Complex
open scoped Real ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

/-- **Analytic-polynomial density in the Hardy subspace.**  If an `L²(circleLebesgue)` function `f`
is *analytic* — its negative Fourier coefficients (under the additive-circle identification) all
vanish — then the analytic-monomial partial sums `∑_{n≤N} f̂(n) zⁿ` converge to `f` in `L²`.  This is
the basic `H²` density statement underlying the Szegő and F.&M. Riesz constructions. -/
theorem analyticPoly_hasSum_of_hardy {f : Lp ℂ 2 circleLebesgue}
    (hf : ∀ n : ℤ, n < 0 →
      fourierCoeff (↑↑(circleLpAddCircleLinearIsometryEquiv f)) n = 0) :
    HasSum (fun n : ℕ =>
        fourierCoeff (↑↑(circleLpAddCircleLinearIsometryEquiv f)) (n : ℤ)
          • circleMonomialLp circleLebesgue n) f := by
  set U := circleLpAddCircleLinearIsometryEquiv with hU
  -- L² Fourier series of `U f` on the additive circle
  have h2 := hasSum_fourier_series_L2 (U f)
  -- pull the series back through the isometry `U.symm`
  have h3 : HasSum
      (fun i : ℤ => fourierCoeff (↑↑(U f)) i • U.symm (fourierLp 2 i)) f := by
    have hmap := h2.mapL (U.symm.toContinuousLinearEquiv.toContinuousLinearMap)
    simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      map_smul, LinearIsometryEquiv.symm_apply_apply] at hmap
    exact hmap
  -- reindex `ℤ → ℕ`, discarding the (vanishing) negative modes
  have hreindex : HasSum
      (fun n : ℕ => fourierCoeff (↑↑(U f)) (n : ℤ) • U.symm (fourierLp 2 (n : ℤ))) f := by
    refine (Function.Injective.hasSum_iff (f := fun i : ℤ =>
      fourierCoeff (↑↑(U f)) i • U.symm (fourierLp 2 i))
      (g := (Nat.cast : ℕ → ℤ)) Nat.cast_injective ?_).mpr h3
    intro i hi
    have hneg : i < 0 := by
      rcases lt_trichotomy i 0 with h | h | h
      · exact h
      · exact absurd ⟨i.toNat, by simp [h]⟩ hi
      · exact absurd ⟨i.toNat, by simp [Int.toNat_of_nonneg h.le]⟩ hi
    show fourierCoeff (↑↑(U f)) i • U.symm (fourierLp 2 i) = 0
    rw [hf i hneg, zero_smul]
  -- identify `U.symm (fourierLp 2 n)` with the multiplicative monomial
  have hsummand : ∀ n : ℕ,
      U.symm (fourierLp 2 (n : ℤ)) = circleMonomialLp circleLebesgue n := fun n => by
    apply U.injective
    rw [U.apply_symm_apply]
    exact (circleLpToAddCircleLinearIsometry_circleMonomial n).symm
  have hfun : (fun n : ℕ =>
        fourierCoeff (↑↑(U f)) (n : ℤ) • U.symm (fourierLp 2 (n : ℤ)))
      = fun n : ℕ =>
        fourierCoeff (↑↑(U f)) (n : ℤ) • circleMonomialLp circleLebesgue n := by
    funext n; rw [hsummand n]
  rw [hfun] at hreindex
  exact hreindex

/-- **Parseval for the Riesz–Fischer reconstruction.**  The `L²(circleLebesgue)` norm of the analytic
function reconstructed from a square-summable coefficient sequence equals the `ℓ²` norm of its
coefficients (extended by zero to the negative modes).  This realises an `ℓ²` Taylor sequence as a
boundary `L²` (`H²`) function isometrically — the identity behind `1/D ∈ H²`. -/
theorem norm_circleRieszFischerOfNat (c : ℕ → ℂ) (hc : Memℓp c 2) :
    ‖circleRieszFischerOfNat c hc‖
      = ‖(⟨nonnegativeIntExtension c, nonnegativeIntExtension_memℓp_two c hc⟩ :
          lp (fun _ : ℤ => ℂ) 2)‖ := by
  rw [circleRieszFischerOfNat, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]


/-- **Monomial orthogonality on the circle.**  `∫₀²π e^{i n θ} dθ = 2π` if `n = 0`, else `0`.
The reusable core of every Parseval/Gutzmer identity. -/
theorem integral_exp_int_mul_I (n : ℤ) :
    (∫ θ in (0:ℝ)..(2 * π), Complex.exp ((n : ℂ) * θ * Complex.I)) = if n = 0 then 2 * π else 0 := by
  by_cases hn : n = 0
  · subst hn; simp
  · have hc : (n : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hn) Complex.I_ne_zero
    have hrw : (∫ θ in (0:ℝ)..(2 * π), Complex.exp ((n : ℂ) * θ * Complex.I))
        = ∫ θ in (0:ℝ)..(2 * π), Complex.exp ((n * Complex.I : ℂ) * θ) :=
      intervalIntegral.integral_congr (fun θ _ => by congr 1; ring)
    rw [hrw, integral_exp_mul_complex hc, if_neg hn]
    have h1 : Complex.exp ((↑n * Complex.I : ℂ) * ↑(2 * π)) = 1 := by
      rw [show ((↑n * Complex.I : ℂ) * ↑(2 * π)) = (↑n : ℂ) * (2 * ↑π * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I n
    rw [h1, Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_self, zero_div]


/-- `(circleMap 0 r θ)^k = r^k · e^{i k θ}` as a complex number. -/
theorem circleMap_pow (r : ℝ) (k : ℕ) (θ : ℝ) :
    (circleMap 0 r θ) ^ k = (r : ℂ) ^ k * Complex.exp ((k : ℂ) * θ * Complex.I) := by
  rw [circleMap, zero_add, mul_pow, ← Complex.exp_nat_mul]
  congr 2
  ring

/-- **Monomial orthogonality on the circle of radius `r`.**  `∫₀²π zᵏ · conj(zʲ) dθ` (with
`z = r e^{iθ}`) is `r^{2k}·2π` if `k = j`, else `0`. -/
theorem integral_circleMap_pow_conj (r : ℝ) (j k : ℕ) :
    (∫ θ in (0:ℝ)..(2 * π),
        (circleMap 0 r θ) ^ k * conj ((circleMap 0 r θ) ^ j))
      = if k = j then (r : ℂ) ^ (2 * k) * (2 * π) else 0 := by
  have hconj : ∀ θ : ℝ, conj ((circleMap 0 r θ) ^ j)
      = (r : ℂ) ^ j * Complex.exp (-((j : ℂ) * θ * Complex.I)) := by
    intro θ
    rw [circleMap_pow, map_mul, map_pow, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    simp only [map_mul, map_natCast, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  set n : ℤ := (k : ℤ) - (j : ℤ) with hn
  have hint : (∫ θ in (0:ℝ)..(2 * π),
        (circleMap 0 r θ) ^ k * conj ((circleMap 0 r θ) ^ j))
      = ∫ θ in (0:ℝ)..(2 * π),
          (r : ℂ) ^ (k + j) * Complex.exp ((n : ℂ) * θ * Complex.I) := by
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    rw [circleMap_pow r k θ, hconj θ, mul_mul_mul_comm, ← pow_add, ← Complex.exp_add]
    congr 2
    rw [hn]; push_cast; ring
  rw [hint, intervalIntegral.integral_const_mul, integral_exp_int_mul_I n, hn]
  rcases eq_or_ne k j with h | h
  · subst h; simp [two_mul]
  · have hd : (k : ℤ) - (j : ℤ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
    simp [hd, h]

/-- **Polynomial Parseval on the circle of radius `r`.**  The circle average of `‖p‖²` for a
polynomial `p(z) = ∑ cₖ zᵏ` is `∑ ‖cₖ‖² r^{2k}`.  Gutzmer's identity for polynomials — the finite
core of the `H²` Parseval used to bound the reciprocal outer function's Taylor coefficients. -/
theorem circleAverage_normSq_poly (r : ℝ) (M : ℕ) (c : ℕ → ℂ) :
    (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π),
        ‖∑ k ∈ Finset.range M, c k * (circleMap 0 r θ) ^ k‖ ^ (2 : ℕ)
      = ∑ k ∈ Finset.range M, ‖c k‖ ^ (2 : ℕ) * r ^ (2 * k) := by
  have hπ : (0:ℝ) < 2 * π := by positivity
  set z : ℝ → ℂ := fun θ => circleMap 0 r θ with hz
  -- pointwise expansion of ↑‖S‖²
  have hpt : ∀ θ : ℝ,
      ((‖∑ k ∈ Finset.range M, c k * (z θ) ^ k‖ ^ (2 : ℕ) : ℝ) : ℂ)
      = ∑ k ∈ Finset.range M, ∑ j ∈ Finset.range M,
          c k * conj (c j) * ((z θ) ^ k * conj ((z θ) ^ j)) := by
    intro θ
    have h1 : ((‖∑ k ∈ Finset.range M, c k * (z θ) ^ k‖ ^ (2 : ℕ) : ℝ) : ℂ)
        = (∑ k ∈ Finset.range M, c k * (z θ) ^ k)
            * conj (∑ k ∈ Finset.range M, c k * (z θ) ^ k) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [h1, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [map_mul]; ring
  -- integrate and swap ∫ with the finite double sum
  have hcont : ∀ k j : ℕ, Continuous
      (fun θ : ℝ => c k * conj (c j) * ((z θ) ^ k * conj ((z θ) ^ j))) := by
    intro k j
    refine continuous_const.mul (Continuous.mul ?_ ?_)
    · exact (continuous_circleMap 0 r).pow k
    · exact Complex.continuous_conj.comp ((continuous_circleMap 0 r).pow j)
  have hInt : (∫ θ in (0:ℝ)..(2 * π),
        ((‖∑ k ∈ Finset.range M, c k * (z θ) ^ k‖ ^ (2 : ℕ) : ℝ) : ℂ))
      = ∑ k ∈ Finset.range M, ∑ j ∈ Finset.range M,
          c k * conj (c j) * (∫ θ in (0:ℝ)..(2 * π), (z θ) ^ k * conj ((z θ) ^ j)) := by
    rw [intervalIntegral.integral_congr (fun θ _ => hpt θ),
      intervalIntegral.integral_finsetSum
        (fun k _ => (continuous_finsetSum _ (fun j _ => hcont k j)).intervalIntegrable _ _)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [intervalIntegral.integral_finsetSum
      (fun j _ => (hcont k j).intervalIntegrable _ _)]
    exact Finset.sum_congr rfl (fun j _ => intervalIntegral.integral_const_mul _ _)
  -- orthogonality collapses to the diagonal
  simp only [hz, integral_circleMap_pow_conj] at hInt
  have hdiag : ∀ k ∈ Finset.range M,
      (∑ j ∈ Finset.range M,
        c k * conj (c j) * (if k = j then (r : ℂ) ^ (2 * k) * (2 * π) else 0))
      = ((‖c k‖ ^ (2 : ℕ) * r ^ (2 * k) * (2 * π) : ℝ) : ℂ) := by
    intro k hk
    rw [Finset.sum_eq_single_of_mem k hk
      (fun j _ hjk => by rw [if_neg (fun h => hjk h.symm), mul_zero])]
    rw [if_pos rfl, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [Finset.sum_congr rfl hdiag, ← Complex.ofReal_sum,
    intervalIntegral.integral_ofReal] at hInt
  have hreal : (∫ θ in (0:ℝ)..(2 * π),
        (‖∑ k ∈ Finset.range M, c k * (z θ) ^ k‖ ^ (2 : ℕ) : ℝ))
      = ∑ k ∈ Finset.range M, ‖c k‖ ^ (2 : ℕ) * r ^ (2 * k) * (2 * π) :=
    Complex.ofReal_injective hInt
  rw [hreal, ← Finset.sum_mul]
  have h2 : (2 * π) ≠ 0 := hπ.ne'
  field_simp

/-- **Partial-sum Parseval.**  The circle average of `‖Sₙ‖²` for the `N`-th partial sum of a power
series with coefficients `bₖ` is `∑_{k<N} ‖bₖ‖² r^{2k}`.  Bridges a power series to polynomial
Parseval. -/
theorem circleAverage_normSq_partialSum (p : FormalMultilinearSeries ℂ ℂ ℂ) (r : ℝ) (N : ℕ) :
    (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ‖p.partialSum N (circleMap 0 r θ)‖ ^ (2 : ℕ)
      = ∑ k ∈ Finset.range N, ‖p.coeff k‖ ^ (2 : ℕ) * r ^ (2 * k) := by
  have h : ∀ θ : ℝ, p.partialSum N (circleMap 0 r θ)
      = ∑ k ∈ Finset.range N, p.coeff k * (circleMap 0 r θ) ^ k := by
    intro θ
    rw [FormalMultilinearSeries.partialSum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [p.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm]
  simp_rw [h]
  exact circleAverage_normSq_poly r N p.coeff


end GaloisForLFunctions.HTGeometry
