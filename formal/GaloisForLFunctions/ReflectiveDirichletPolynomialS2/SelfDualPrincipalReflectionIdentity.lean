import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalGuthMaynardForm
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardSTwoReductionDiagonal

/-!
# Signed Principal Reflection Factorization and Self-Dual Scale Law in the $S_2$ Tower

This module formalizes the first leg of **Mechanism 5 (Self-Dual Reflective Dirichlet-Polynomial
Closure in the Guth–Maynard / Chen–Gupta–Li $S_2$ Tower)**:

1. **Exact Signed Positive- and Negative-Frequency Reflection Identities
   (`sum_fourier_pos_eq_mellin_headPoly_integral`,
   `sum_fourier_neg_eq_conj_mellin_headPoly_integral`):**
   For any smooth bump `w : CGLRealSmoothBump`, scale `N > 0`, time `t : ℝ`, and cutoff `M : ℕ`,
   the positive-frequency Poisson sum $\sum_{m=1}^M \hat{h}_t(mN)$ factorizes inside the Mellin
   vertical line integral into the unweighted Dirichlet head polynomial
   $D_M(t - y) = \sum_{m=1}^M m^{-i(t-y)}$ (`cglGMHeadPoly M (t - y)`) times the stationary-phase
   factor $K(t - y; \log N, \log(2MN))$:
   $$\sum_{m=1}^M \hat{h}_t(mN) = \frac{1}{2\pi} \int_{\mathbb{R}} H(1+iy)\,
     e^{-i(t-y)\log N}\, D_M(t-y)\, K(t-y; \log N, \log(2MN))\,dy,$$
   and the negative-frequency sum $\sum_{m=1}^M \hat{h}_t(-mN)$ equals the complex conjugate of the
   reflected integral at $-t$.
2. **Two-Sided Self-Dual Scale Product & Self-Dual Length Equalization
   (`selfDual_reflection_scale_product`, `selfDual_ceiling_length_bounds`):**
   For $N > 0$ and $|t| > 0$, the reflected cutoff $M = \lceil |t|^{1+\epsilon}/N \rceil$ satisfies
   $|t|^{1+\epsilon} \le N \cdot M < |t|^{1+\epsilon} + N$. At the self-dual scale
   $N = |t|^{(1+\epsilon)/2}$, the quotient $|t|^{1+\epsilon}/N$ equals $N$, so the reflected length
   $M = \lceil N \rceil$ satisfies $N \le M < N + 1$.
3. **Conjugation Symmetry of `gmNonzero` & Explicit Lemma 6.2 Reflection Bound
   (`gmNonzero_conj_symm_and_lemma62_bound`):**
   Combines the exact conjugation symmetry $A(-\tau) = \overline{A(\tau)}$ of the punctured Poisson
   mode sum `gmNonzero w N τ`, the norm reflection symmetry $\|D_M(-\tau)\| = \|D_M(\tau)\|$, and
   the unconditional Guth–Maynard Lemma 6.2 estimate `cglGM_lemma62_zeta`.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Finset
open scoped FourierTransform ComplexConjugate
open RHTower RHTower.GuthMaynard

noncomputable section

namespace GaloisForLFunctions.ReflectiveDirichletPolynomialS2

/-! ### 1. Exact Signed Positive- and Negative-Frequency Reflection Identities -/

/-- **Signed Positive-Frequency Principal Reflection Identity:**
For `N > 0` and `M : ℕ`, the positive-frequency Poisson sum $\sum_{m=1}^M \hat{h}_t(mN)$ equals the
Mellin-line integral of $H(1+iy)\, e^{-i(t-y)\log N}\, D_M(t-y)\, K(t-y; \log N, \log(2MN))$, where
$D_M(\tau) = \text{cglGMHeadPoly } M \, \tau = \sum_{m=1}^M m^{-i\tau}$. -/
theorem sum_fourier_pos_eq_mellin_headPoly_integral (w : CGLRealSmoothBump) (t N : ℝ)
    (hN : 0 < N) (M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, 𝓕 (cglSmoothBumpHt w.toCGLSmoothBump t : ℝ → ℂ) ((m : ℝ) * N) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ y : ℝ, cglGMMellinLine w y *
          ((Complex.exp (((-((t - y) * Real.log N) : ℝ) : ℂ) * I) *
            cglGMHeadPoly M (t - y)) *
            cglGMReflectionPhaseIntegral (t - y) (Real.log N) (Real.log (2 * M * N))) := by
  rw [cglGM_sum_fourier_eq_reflected w t N hN M]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun y =>
    sum_cglGMReflectedTerm_eq w t N hN M y)

/-- **Signed Negative-Frequency Principal Reflection Identity:**
For `N > 0` and `M : ℕ`, the negative-frequency Poisson sum $\sum_{m=1}^M \hat{h}_t(-mN)$ equals
the complex conjugate of the Mellin-line reflected integral evaluated at $-t$. -/
theorem sum_fourier_neg_eq_conj_mellin_headPoly_integral (w : CGLRealSmoothBump) (t N : ℝ)
    (hN : 0 < N) (M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, 𝓕 (cglSmoothBumpHt w.toCGLSmoothBump t : ℝ → ℂ) (-((m : ℝ) * N)) =
      conj (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ y : ℝ, cglGMMellinLine w y *
          ((Complex.exp (((-((-t - y) * Real.log N) : ℝ) : ℂ) * I) *
            cglGMHeadPoly M (-t - y)) *
            cglGMReflectionPhaseIntegral (-t - y) (Real.log N) (Real.log (2 * M * N)))) := by
  simp_rw [cglGM_fourier_neg_eq_conj w t, ← map_sum]
  rw [sum_fourier_pos_eq_mellin_headPoly_integral w (-t) N hN M]

/-! ### 2. Self-Dual Scale Product and Length Equalization -/

/-- **Two-Sided Scale Product Law for the Reflected Length:**
For any $|t| > 0$, $N > 0$, and $\epsilon \in \mathbb{R}$, the reflected Dirichlet polynomial length
$M = \lceil |t|^{1+\epsilon} / N \rceil$ satisfies $1 \le M$ and
$$|t|^{1+\epsilon} \le N \cdot M < |t|^{1+\epsilon} + N.$$ -/
theorem selfDual_reflection_scale_product {t ε N : ℝ} (ht : 0 < |t|) (hN : 0 < N) :
    1 ≤ ⌈|t| ^ (1 + ε) / N⌉₊ ∧
      |t| ^ (1 + ε) ≤ N * (⌈|t| ^ (1 + ε) / N⌉₊ : ℝ) ∧
      N * (⌈|t| ^ (1 + ε) / N⌉₊ : ℝ) < |t| ^ (1 + ε) + N := by
  have hx0 : 0 < |t| ^ (1 + ε) / N := div_pos (Real.rpow_pos_of_pos ht _) hN
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr hx0)), ?_, ?_⟩
  · have h1 : |t| ^ (1 + ε) / N ≤ (⌈|t| ^ (1 + ε) / N⌉₊ : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hN] at h1
    linarith
  · have h2 : (⌈|t| ^ (1 + ε) / N⌉₊ : ℝ) < |t| ^ (1 + ε) / N + 1 := Nat.ceil_lt_add_one hx0.le
    have h3 := mul_lt_mul_of_pos_left h2 hN
    have h4 : N * (|t| ^ (1 + ε) / N + 1) = |t| ^ (1 + ε) + N := by field_simp
    linarith

/-- **Self-Dual Length Equalization (`N = |t|^{(1+ε)/2}`):**
At the self-dual scale $N = |t|^{(1+\epsilon)/2}$ (`|t| > 0`), the reflected quotient
$|t|^{1+\epsilon} / N$ equals $N$, so the reflected length $M = \lceil |t|^{1+\epsilon} / N \rceil$
coincides with $\lceil N \rceil$ and satisfies $N \le M < N + 1$. -/
theorem selfDual_ceiling_length_bounds {t ε : ℝ} (ht : 0 < |t|) :
    let N := |t| ^ ((1 + ε) / 2)
    ⌈|t| ^ (1 + ε) / N⌉₊ = ⌈N⌉₊ ∧
      N ≤ (⌈|t| ^ (1 + ε) / N⌉₊ : ℝ) ∧
      (⌈|t| ^ (1 + ε) / N⌉₊ : ℝ) < N + 1 := by
  dsimp only
  have hdiv : |t| ^ (1 + ε) / |t| ^ ((1 + ε) / 2) = |t| ^ ((1 + ε) / 2) := by
    rw [← Real.rpow_sub ht, show 1 + ε - (1 + ε) / 2 = (1 + ε) / 2 by ring]
  have hpos : 0 ≤ |t| ^ ((1 + ε) / 2) := Real.rpow_nonneg (abs_nonneg t) _
  rw [hdiv]
  exact ⟨rfl, Nat.le_ceil _, Nat.ceil_lt_add_one hpos⟩

/-! ### 3. Conjugation Symmetry and Explicit Lemma 6.2 Reflection Bound -/

/-- **Conjugation Symmetry of `gmNonzero` and Guth–Maynard Lemma 6.2 Reflection Bound:**
For every smooth bump `w : CGLRealSmoothBump` and $\epsilon \in (0, 1]$:
1. the punctured Poisson mode sum $A(\tau) = \text{gmNonzero } w \, N \, \tau$ is conjugation-symmetric
   under $\tau \mapsto -\tau$: $A(-\tau) = \overline{A(\tau)}$,
2. the unweighted Dirichlet head polynomial $D_M(\tau) = \text{cglGMHeadPoly } M \, \tau$ has
   even norm: $\|D_M(-\tau)\| = \|D_M(\tau)\|$, and
3. there exists $C \ge 0$ such that for all $T \ge 1$, $N \ge 1$, and $T^\epsilon \le |t| \le T$,
   $$\|A(t)\| \le C |t|^{-1/2} \int_{-T^\epsilon/2}^{T^\epsilon/2}
     \|D_{\lceil |t|^{1+\epsilon}/N \rceil}(t + u)\|\,du + C T^{-100}.$$ -/
theorem gmNonzero_conj_symm_and_lemma62_bound (w : CGLRealSmoothBump) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∀ N τ : ℝ, gmNonzero w N (-τ) = conj (gmNonzero w N τ)) ∧
    (∀ (M : ℕ) (τ : ℝ), ‖cglGMHeadPoly M (-τ)‖ = ‖cglGMHeadPoly M τ‖) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ (T t : ℝ) (N : ℕ), 1 ≤ T → 1 ≤ N → T ^ ε ≤ |t| → |t| ≤ T →
      ‖gmNonzero w N t‖ ≤
        C * |t| ^ (-(1 / 2 : ℝ)) *
            (∫ u in (-(T ^ ε / 2))..(T ^ ε / 2),
              ‖cglGMHeadPoly ⌈|t| ^ (1 + ε) / N⌉₊ (t + u)‖) +
          C * T ^ (-100 : ℝ)) :=
  ⟨gmNonzero_neg w, norm_cglGMHeadPoly_neg, cglGM_lemma62_zeta w hε hε1⟩

end GaloisForLFunctions.ReflectiveDirichletPolynomialS2
