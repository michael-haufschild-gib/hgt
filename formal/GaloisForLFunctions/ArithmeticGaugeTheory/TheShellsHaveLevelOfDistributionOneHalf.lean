import GaloisForLFunctions.ArithmeticGaugeTheory.TheShellDecomposition
import GaloisForLFunctions.ArithmeticGaugeTheory.TheFiniteGaugePointsSampleHaar
import GaloisForLFunctions.ArithmeticGaugeTheory.TheDirichletPointsCancelThroughPeriodicity

/-!
# The shells have level of distribution one half

The prime pair form `P(a, x) = Σ a(k) x(m) x̄(n) G(log n − log m − log k)` splits into a gauge-invariant
ratio part and the shells, which are gauge charge (`TheShellDecomposition`). This file measures the
shells at the special locus, on average over conductors, for kernels with a finite Fourier expansion
`G(u) = Σ_j g_j e^{i t_j u}` (`fourierKernel`).

* **Factorization** (`primePairForm_fourierKernel`). Each frequency factors the form:
  `P = Σ_j g_j A_j X_j X̄_j`, with `A_j = Σ_k a(k) k^{−it_j}` and `X_j = Σ_n x(n) n^{−it_j}`. The form is a
  combination of squared twisted sums of `x`, weighted by twisted sums of `a`.
* **The large sieve for the prime pair form** (`largeSieve_primePairForm`). For a source `x` rough to
  conductor `Q`, summing `|P|` over the primitive Dirichlet points of conductor at most `Q` (weights
  `q/φ(q)`) gives at most `‖g‖₁ ‖a‖₁ (N + Q²) ‖x‖₂²`. At a single point the trivial bound is
  `‖g‖₁ ‖a‖₁ N ‖x‖₂²`; there are about `Q²` special points, so for `Q² ≍ N` the form is on average
  smaller than trivial by the factor `N`, the scale of its Haar mean.
* **The shells** (`largeSieve_shellPart`). Since the ratio part is gauge invariant, the same bound
  holds for `shell + ratio` at every special point: on average over conductors up to `√N` the shells
  cancel the ratio part to within the Haar scale. This is the level-of-distribution `1/2` statement for
  the shells, in large-sieve form.

What it leaves at `0`: the trivial point is the single term `q = 1`. The large sieve bounds it only by
the total, the trivial bound; level of distribution says nothing about one point. The input that
Bombieri–Vinogradov adds to the large sieve, Siegel–Walfisz for small conductors, is a zero-free region
for each `L(s, χ)`, i.e. information about individual special points.
-/

open Finset
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

/-- The archimedean phase `n^{−it} = e^{−it log n}`. -/
def archPhase (t : ℝ) (n : ℕ) : ℂ := Complex.exp (((-(t * Real.log n)) : ℝ) * Complex.I)

theorem norm_archPhase (t : ℝ) (n : ℕ) : ‖archPhase t n‖ = 1 := Complex.norm_exp_ofReal_mul_I _

/-- A kernel with finite Fourier expansion `G(u) = Σ_j g_j e^{i t_j u}`. -/
def fourierKernel {ι : Type*} (J : Finset ι) (g : ι → ℂ) (t : ι → ℝ) (u : ℝ) : ℂ :=
  ∑ j ∈ J, g j * Complex.exp (((t j * u : ℝ)) * Complex.I)

/-- The phase of a lag factors: `e^{it(log n − log m − log k)} = k^{−it} m^{−it} conj(n^{−it})`. -/
theorem exp_lag (t : ℝ) (k m n : ℕ) :
    Complex.exp (((t * (Real.log n - Real.log m - Real.log k)) : ℝ) * Complex.I) =
      archPhase t k * archPhase t m * conj (archPhase t n) := by
  simp only [archPhase, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

variable (K N : ℕ) (a x : ℕ → ℂ) {ι : Type*} (J : Finset ι) (g : ι → ℂ) (t : ι → ℝ)

/-- **Factorization of the prime pair form** over the frequencies of the kernel. -/
theorem primePairForm_fourierKernel :
    primePairForm K N a x (fourierKernel J g t) =
      ∑ j ∈ J, g j * (∑ k ∈ Icc 1 K, a k * archPhase (t j) k) *
        ((∑ m ∈ Icc 1 N, x m * archPhase (t j) m) *
          conj (∑ n ∈ Icc 1 N, x n * archPhase (t j) n)) := by
  -- Expand both sides into sums over `(j, k, m, n)`.
  have hrhs : ∀ j ∈ J, g j * (∑ k ∈ Icc 1 K, a k * archPhase (t j) k) *
      ((∑ m ∈ Icc 1 N, x m * archPhase (t j) m) *
        conj (∑ n ∈ Icc 1 N, x n * archPhase (t j) n)) =
      ∑ k ∈ Icc 1 K, ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        a k * x m * conj (x n) * (g j * (archPhase (t j) k * archPhase (t j) m *
          conj (archPhase (t j) n))) := by
    intro j _
    rw [map_sum, sum_mul_sum, mul_sum (Icc 1 K), sum_mul]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [map_mul]
    ring
  rw [sum_congr rfl hrhs, primePairForm]
  symm
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun m _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun n _ => ?_
  rw [fourierKernel, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [exp_lag]

/-- **The form at one point** is bounded by the squared twisted sums of `x`. -/
theorem norm_primePairForm_fourierKernel_le :
    ‖primePairForm K N a x (fourierKernel J g t)‖ ≤
      ∑ j ∈ J, ‖g j‖ * (∑ k ∈ Icc 1 K, ‖a k‖) *
        ‖∑ n ∈ Icc 1 N, x n * archPhase (t j) n‖ ^ 2 := by
  rw [primePairForm_fourierKernel]
  refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_mul, Complex.mul_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    (by positivity)
  refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun k _ => ?_))
  rw [norm_mul, norm_archPhase, mul_one]

/-- The twisted sum of a gauge-transformed source at a Dirichlet point, as a sum over `range`. -/
theorem sum_gaugeTransform_archPhase (y : GaugeTorus) {x : ℕ → ℂ} (hx0 : x 0 = 0) (s : ℝ) :
    ∑ n ∈ Icc 1 N, gaugeTransform y x n * archPhase s n =
      ∑ n ∈ range (N + 1), (x n * archPhase s n) * twist y n := by
  rw [sum_range_succ_eq_add_Icc, hx0, zero_mul, zero_mul, zero_add]
  refine sum_congr rfl fun n _ => ?_
  rw [gaugeTransform]
  ring

open Classical in
/-- **The large sieve for the prime pair form.** For `x` rough to conductor `Q ≥ 2`,
`Σ_{q ≤ Q} (q/φ(q)) Σ_{χ primitive} |P(aχ, xχ)| ≤ ‖g‖₁ ‖a‖₁ (N + Q²) ‖x‖₂²`. -/
theorem largeSieve_primePairForm (Q : ℕ) (hQ : 2 ≤ Q) {x : ℕ → ℂ} (hx : RoughSource Q x) :
    ∑ r ∈ range Q, ((r + 1 : ℕ) : ℝ) / (r + 1).totient *
        ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ (r + 1))).filter (fun ψ => ψ.IsPrimitive),
          ‖primePairForm K N (gaugeTransform (dirichletGauge ψ) a)
            (gaugeTransform (dirichletGauge ψ) x) (fourierKernel J g t)‖ ≤
      (∑ j ∈ J, ‖g j‖) * (∑ k ∈ Icc 1 K, ‖a k‖) * ((N : ℝ) + Q ^ 2) *
        ∑ n ∈ Icc 1 N, ‖x n‖ ^ 2 := by
  have hx0 : x 0 = 0 := by
    by_contra h
    exact (hx 0 h).1 rfl
  set A : ℝ := ∑ k ∈ Icc 1 K, ‖a k‖
  have hA : 0 ≤ A := sum_nonneg fun _ _ => norm_nonneg _
  -- The gauge transform does not change the norms of `a`.
  have hnorma : ∀ y : GaugeTorus, ∑ k ∈ Icc 1 K, ‖gaugeTransform y a k‖ = A := fun y =>
    sum_congr rfl fun k _ => by rw [gaugeTransform, norm_mul, norm_twist, mul_one]
  -- The large sieve, one frequency at a time.
  have hsieve : ∀ j ∈ J, ∑ r ∈ range Q, ((r + 1 : ℕ) : ℝ) / (r + 1).totient *
      ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ (r + 1))).filter (fun ψ => ψ.IsPrimitive),
        ‖∑ n ∈ Icc 1 N, gaugeTransform (dirichletGauge ψ) x n * archPhase (t j) n‖ ^ 2 ≤
      ((N : ℝ) + Q ^ 2) * ∑ n ∈ Icc 1 N, ‖x n‖ ^ 2 := by
    intro j _
    have hc : RoughSource Q (fun n => x n * archPhase (t j) n) := fun n hn =>
      hx n (left_ne_zero_of_mul hn)
    have h := dirichletGauge_largeSieve (N + 1) Q hQ hc
    simp_rw [sum_gaugeTransform_archPhase N _ hx0]
    refine h.trans (le_of_eq ?_)
    have hsum : ∑ n ∈ range (N + 1), ‖x n * archPhase (t j) n‖ ^ 2 =
        ∑ n ∈ Icc 1 N, ‖x n‖ ^ 2 := by
      rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (Nat.succ_pos N), hx0, zero_mul, norm_zero,
        zero_pow two_ne_zero, zero_add, Nat.succ_eq_add_one, Finset.Ico_add_one_right_eq_Icc]
      exact sum_congr rfl fun n _ => by rw [norm_mul, norm_archPhase, mul_one]
    rw [hsum]
    push_cast
    ring
  calc ∑ r ∈ range Q, ((r + 1 : ℕ) : ℝ) / (r + 1).totient *
        ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ (r + 1))).filter (fun ψ => ψ.IsPrimitive),
          ‖primePairForm K N (gaugeTransform (dirichletGauge ψ) a)
            (gaugeTransform (dirichletGauge ψ) x) (fourierKernel J g t)‖
      ≤ ∑ r ∈ range Q, ((r + 1 : ℕ) : ℝ) / (r + 1).totient *
          ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ (r + 1))).filter (fun ψ => ψ.IsPrimitive),
            ∑ j ∈ J, ‖g j‖ * A *
              ‖∑ n ∈ Icc 1 N, gaugeTransform (dirichletGauge ψ) x n * archPhase (t j) n‖ ^ 2 := by
        refine sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (sum_le_sum fun ψ _ => ?_)
          (by positivity)
        have h := norm_primePairForm_fourierKernel_le K N (gaugeTransform (dirichletGauge ψ) a)
          (gaugeTransform (dirichletGauge ψ) x) J g t
        rwa [hnorma] at h
    _ = ∑ j ∈ J, ‖g j‖ * A * ∑ r ∈ range Q, ((r + 1 : ℕ) : ℝ) / (r + 1).totient *
          ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ (r + 1))).filter (fun ψ => ψ.IsPrimitive),
            ‖∑ n ∈ Icc 1 N, gaugeTransform (dirichletGauge ψ) x n * archPhase (t j) n‖ ^ 2 := by
        simp_rw [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun r _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun ψ _ => ?_
        refine sum_congr rfl fun j _ => ?_
        ring
    _ ≤ ∑ j ∈ J, ‖g j‖ * A * (((N : ℝ) + Q ^ 2) * ∑ n ∈ Icc 1 N, ‖x n‖ ^ 2) :=
        sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hsieve j hj) (by positivity)
    _ = _ := by
        rw [← sum_mul, ← sum_mul]
        ring

open Classical in
/-- **The shells have level of distribution one half.** On average over the primitive Dirichlet
points of conductor at most `Q`, the shells cancel the gauge-invariant ratio part to within
`‖g‖₁ ‖a‖₁ (N + Q²) ‖x‖₂²`. -/
theorem largeSieve_shellPart (Q : ℕ) (hQ : 2 ≤ Q) {x : ℕ → ℂ} (hx : RoughSource Q x) :
    ∑ r ∈ range Q, ((r + 1 : ℕ) : ℝ) / (r + 1).totient *
        ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ (r + 1))).filter (fun ψ => ψ.IsPrimitive),
          ‖shellPart K N (gaugeTransform (dirichletGauge ψ) a)
              (gaugeTransform (dirichletGauge ψ) x) (fourierKernel J g t) +
            ratioPart K N a x (fourierKernel J g t)‖ ≤
      (∑ j ∈ J, ‖g j‖) * (∑ k ∈ Icc 1 K, ‖a k‖) * ((N : ℝ) + Q ^ 2) *
        ∑ n ∈ Icc 1 N, ‖x n‖ ^ 2 := by
  refine le_of_eq_of_le ?_ (largeSieve_primePairForm K N a J g t Q hQ hx)
  refine sum_congr rfl fun r _ => congrArg _ (sum_congr rfl fun ψ _ => ?_)
  rw [primePairForm_eq_ratioPart_add_shellPart, ratioPart_gaugeTransform, add_comm]

end GaloisForLFunctions.ArithmeticGaugeTheory
