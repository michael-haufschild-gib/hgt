import GaloisForLFunctions.ReflectiveDirichletPolynomialS2.SelfDualPrincipalReflectionIdentity
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardSTwoReductionSingleBlock
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardKeyPropFrequencySplit

/-!
# Exact $q = 1$ Cubic Trace $S_2$ Plane-Diagonal Decomposition and Single-Block Reflection Reduction

This module formalizes the second leg of **Mechanism 5 (Self-Dual Reflective Dirichlet-Polynomial
Closure in the Guth–Maynard / Chen–Gupta–Li $S_2$ Tower)**:

1. **Exact $q = 1$ Plane-Diagonal Decomposition of the Chen–Gupta–Li Cubic Trace $S_2$
   (`cglTraceS2_modulusOne_eq_diag_add_offDiag`):**
   For any packet of $R$ rows at modulus $q = 1$ with distinct row times forming
   $W = \text{image}(\text{time})$, the two-nonzero-frequency component $S_2$ of the Chen–Gupta–Li
   cubic Gram trace decomposes identically into the diagonal quadratic form in the punctured
   Poisson mode sum $A(\tau) = \text{gmNonzero } w \, N \, \tau$ plus the off-diagonal triple sum:
   $$\sum_{m \in S_2} \text{cglLemma45TraceFrequencyTerm}(m) =
     3 N^3 \Biggl(\hat{h}_0(0) \sum_{x, y \in W} \|A(x - y)\|^2 +
       \sum_{x \in W} \sum_{y \in W} \sum_{z \in W \setminus \{x\}}
         A(x - y) A(y - z) \hat{h}_{z - x}(0)\Biggr).$$
2. **Single-Dyadic-Block Reflection Reduction for the $q = 1$ CGL Cubic Trace $S_2$
   (`cglTraceS2_modulusOne_le_single_dyadic_block`):**
   For every $\epsilon \in (0, 1]$, there exists $C \ge 0$ such that for any $T \ge 1$, length $N$,
   and packet of $R$ rows with $T^\epsilon$-separated times in $[0, T]$, there exist an admissible
   reflected length $1 \le M \le (2T)^{1+\epsilon}/N + 1$ and a dyadic block $2^j \le M$ such that
   $$\left\|\sum_{m \in S_2} \text{cglLemma45TraceFrequencyTerm}(m)\right\| \le
     C (T^\epsilon)^6 \frac{N^2}{2^j}
       \sum_{t_1, t_2 \in W} \left|\sum_{m \in \text{block}_j(M)} m^{i(t_1 - t_2)}\right|^2.$$
3. **Full Off-Diagonal Nonzero Frequency Split at $q = 1$
   (`cglOffDiagonalNonzero_modulusOne_split_and_bound`):**
   Combines the exact three-carrier frequency split $S_1' + (S_2(W) - R S_2(\{0\})) +
   (S_3(W) - R S_3(\{0\}))$ (`nonzeroFrequencySum_modulusOne`) with the uniform triangle bound
   `norm_nonzeroFrequencySum_modulusOne_le`.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Finset
open scoped FourierTransform
open RHTower RHTower.GuthMaynard

noncomputable section

namespace GaloisForLFunctions.ReflectiveDirichletPolynomialS2

/-! ### 1. Exact `q = 1` Plane-Diagonal Decomposition of the Chen–Gupta–Li Cubic Trace `S₂` -/

/-- **Exact `q = 1` Plane-Diagonal Decomposition of the CGL Cubic Trace `S₂`:**
For a packet of `R` rows at modulus `q = 1` with injective row times forming
`W = Finset.univ.image (fun r => (rows r).time)`, the `S₂` component of the Chen–Gupta–Li cubic
Gram trace equals `3 N³ (ĥ₀(0) ∑_{x,y∈W} ‖A(x−y)‖² + ∑_{x∈W} ∑_{y∈W} ∑_{z∈W.erase x} F(x,y,z))`. -/
theorem cglTraceS2_modulusOne_eq_diag_add_offDiag (w : CGLRealSmoothBump)
    (N : CGLPositiveLength) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData modulusOne.value)
    (hinj : Function.Injective fun r => (rows r).time) :
    ∑' m : {m : (ℤ × ℤ) × ℤ // gmS2Frequency m},
        cglLemma45TraceFrequencyTerm w N modulusOne R rows m =
      3 * ((N.value : ℂ) ^ 3 *
        (gmHat w 0 0 *
          (gmS2Diagonal w N.value (Finset.univ.image fun r => (rows r).time) : ℂ) +
          ∑ x ∈ Finset.univ.image (fun r => (rows r).time),
            ∑ y ∈ Finset.univ.image (fun r => (rows r).time),
              ∑ z ∈ (Finset.univ.image (fun r => (rows r).time)).erase x,
                gmS2Kernel w N.value x y z)) := by
  have hN : (0 : ℝ) < N.value := by exact_mod_cast N.positive
  rw [cglTraceS2_modulusOne_eq_gmS2 w N R rows hinj,
    gmS2_eq_three_mul w hN, sum_gmS2Kernel_eq_diag_add]
  push_cast
  rfl

/-! ### 2. Single-Dyadic-Block Reflection Reduction for the `q = 1` CGL Cubic Trace `S₂` -/

/-- **Single-Dyadic-Block Reflection Bound for the `q = 1` Chen–Gupta–Li Cubic Trace `S₂`:**
For every `ε ∈ (0, 1]`, there exists `C ≥ 0` such that for all `T ≥ 1`, length `N`, and packet of
`R` rows with `T^ε`-separated times in `[0, T]`, there exist `M ≥ 1` and a dyadic block `j`
(`2^j ≤ M ≤ (2T)^{1+ε}/N + 1`) such that the `S₂` component of the `q = 1` Chen–Gupta–Li cubic
trace is bounded by `C (T^ε)^6 (N² / 2^j) hbPairSum W (dyadicSegmentBlock M j) 1`. -/
theorem cglTraceS2_modulusOne_le_single_dyadic_block (w : CGLRealSmoothBump) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ) (N : CGLPositiveLength) (R : ℕ)
      (rows : Fin R → CGLCharacterDyadicRowData modulusOne.value), 1 ≤ T →
      (∀ r s, r ≠ s → T ^ ε ≤ |(rows r).time - (rows s).time|) →
      (∀ r, 0 ≤ (rows r).time ∧ (rows r).time ≤ T) →
      ∃ M j : ℕ, 1 ≤ M ∧ 2 ^ j ≤ M ∧ (M : ℝ) ≤ (2 * T) ^ (1 + ε) / N.value + 1 ∧
        ‖∑' m : {m : (ℤ × ℤ) × ℤ // gmS2Frequency m},
            cglLemma45TraceFrequencyTerm w N modulusOne R rows m‖ ≤
          C * (T ^ ε) ^ 6 *
            ((N.value : ℝ) ^ 2 / 2 ^ j *
              Sieve.hbPairSum (Finset.univ.image fun r => (rows r).time)
                (Sieve.dyadicSegmentBlock M j) (fun _ => ((1 : ℝ) : ℂ))) := by
  classical
  obtain ⟨C, hC0, hC⟩ := gmS2_le_sixOne_single w hε hε1
  refine ⟨C, hC0, fun T N R rows hT hsep hrange => ?_⟩
  have hTe : 0 < T ^ ε := Real.rpow_pos_of_pos (by linarith) ε
  have hinj : Function.Injective fun r => (rows r).time := by
    intro r s hrs
    by_contra hne
    have := hsep r s hne
    simp only at hrs
    rw [hrs, sub_self, abs_zero] at this
    linarith
  have hN : (1 : ℝ) ≤ N.value := by exact_mod_cast N.positive
  set W := Finset.univ.image fun r => (rows r).time
  have hWsep : IsSeparated (T ^ ε) W := by
    intro t ht t' ht' hne
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp ht'
    exact hsep r s (fun h => hne (by rw [h]))
  have hWrange : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T := by
    intro t ht
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp ht
    exact hrange r
  rw [cglTraceS2_modulusOne_eq_gmS2 w N R rows hinj]
  exact hC T N.value W hT hN hWsep hWrange

/-! ### 3. Full Off-Diagonal Nonzero Frequency Split at `q = 1` -/

/-- **Full Off-Diagonal Nonzero Frequency Split and Bound at `q = 1`:**
For any smooth bump `w : CGLRealSmoothBump`, the nonzero-frequency sum of the off-diagonal
Chen–Gupta–Li cubic trace at `q = 1` decomposes into `S₁' + (S₂(W) − R S₂({0})) + (S₃(W) − R S₃({0}))`
and is bounded in norm by `‖S₁'‖ + ‖S₂(W)‖ + ‖S₃(W)‖ + c R`. -/
theorem cglOffDiagonalNonzero_modulusOne_split_and_bound (w : CGLRealSmoothBump) :
    (∀ (N : CGLPositiveLength) (R : ℕ)
      (rows : Fin R → CGLCharacterDyadicRowData modulusOne.value),
      Function.Injective (fun r => (rows r).time) →
      ∑' m : {m : (ℤ × ℤ) × ℤ // m ∉ ({0} : Finset ((ℤ × ℤ) × ℤ))},
          cglLemma45OffDiagonalNonzeroFrequencyTerm w N modulusOne R rows m =
        cglProposition51S1 w N modulusOne R rows +
          (gmS2 w N.value (Finset.univ.image fun r => (rows r).time) -
            (R : ℂ) * gmS2 w N.value {0}) +
          (allNonzeroCubicSum w.toCGLSmoothBump
              (Finset.univ.image fun r => (rows r).time) N.value -
            (R : ℂ) * allNonzeroCubicSum w.toCGLSmoothBump {0} N.value)) ∧
    (∃ c, 0 ≤ c ∧ ∀ (N : CGLPositiveLength) (R : ℕ)
      (rows : Fin R → CGLCharacterDyadicRowData modulusOne.value),
      Function.Injective (fun r => (rows r).time) →
      ‖∑' m : {m : (ℤ × ℤ) × ℤ // m ∉ ({0} : Finset ((ℤ × ℤ) × ℤ))},
          cglLemma45OffDiagonalNonzeroFrequencyTerm w N modulusOne R rows m‖ ≤
        ‖cglProposition51S1 w N modulusOne R rows‖ +
          ‖gmS2 w N.value (Finset.univ.image fun r => (rows r).time)‖ +
          ‖allNonzeroCubicSum w.toCGLSmoothBump
            (Finset.univ.image fun r => (rows r).time) N.value‖ +
          c * R) :=
  ⟨nonzeroFrequencySum_modulusOne w, norm_nonzeroFrequencySum_modulusOne_le w⟩

end GaloisForLFunctions.ReflectiveDirichletPolynomialS2
