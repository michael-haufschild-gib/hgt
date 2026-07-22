import GaloisForLFunctions.RHTower.ArithmeticSchurFirstTraceNonclosability
import GaloisForLFunctions.HilbertMetric.DenseClosedScalarRigidity
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Exact-norm riggings cannot close the arithmetic-Schur clock

The explicit actual-prime graph-null packet is not an artifact of the Hardy realization.  This
module proves a transport law across arbitrary source and target Banach completions: if both
realizations preserve, on every finite packet, the source norm and the response norm of a model
with a nonzero graph-null limit, the transported operator is again nonclosable.

Applied to the arithmetic-Schur prime family, every complete Hilbert/Banach rigging that preserves
the exact coherent source norm and exact first-trace clock norm remains nonclosable.  More strongly,
nonclosability survives when the new source norm is merely bounded above by the arithmetic-Schur
norm and the new response norm is uniformly equivalent to the original clock norm.  The source
and target spaces may differ; no ambient unitary, coordinate model, finite rank, or bounded
postprocessor is assumed.  Therefore a pre-Hardy CCM rigging can close the logarithmic clock only
through unbounded source distortion or asymptotic loss of response observability.

No Xi zero, RH assumption, numerical computation, or nonstandard axiom is used.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Sequential closability for an algebraic operator whose source and target completions may be
different normed spaces. -/
def IsSequentiallyClosableBetween
    {D E K : Type*} [AddCommGroup D] [Module ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (T : D →ₗ[ℝ] K) (j : D →ₗ[ℝ] E) : Prop :=
  ∀ u : ℕ → D,
    Tendsto (fun n => j (u n)) atTop (nhds 0) →
    ∀ y : K, Tendsto (fun n => T (u n)) atTop (nhds y) → y = 0

/-- **Forced response collapse.** Suppose the new source norm is bounded by a model source norm,
the new response norm is bounded by the model response norm, and the new graph is closable.  Every
model graph-null sequence with a convergent response is then sent strongly to zero. -/
theorem tendsto_zero_of_closableBetween_of_source_response_upper
    {D E K H₁ H₂ : Type*} [AddCommGroup D] [Module ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]
    [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    (T : D →ₗ[ℝ] K) (j : D →ₗ[ℝ] E)
    (A : D →ₗ[ℝ] H₂) (i : D →ₗ[ℝ] H₁)
    (Cj Ct : ℝ) (hCt : 0 ≤ Ct)
    (hj : ∀ d, ‖j d‖ ≤ Cj * ‖i d‖)
    (hTupper : ∀ d, ‖T d‖ ≤ Ct * ‖A d‖)
    (hclose : IsSequentiallyClosableBetween T j)
    (u : ℕ → D) (y : H₂)
    (hiu : Tendsto (fun n => i (u n)) atTop (nhds 0))
    (hAu : Tendsto (fun n => A (u n)) atTop (nhds y)) :
    Tendsto (fun n => T (u n)) atTop (nhds 0) := by
  have hCjiu : Tendsto (fun n => Cj * ‖i (u n)‖) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hiu.norm
  have hjuNorm : Tendsto (fun n => ‖j (u n)‖) atTop (nhds 0) :=
    squeeze_zero (fun n => norm_nonneg _) (fun n => hj _) hCjiu
  have hju : Tendsto (fun n => j (u n)) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2 hjuNorm
  have hTcauchy : CauchySeq (fun n => T (u n)) := by
    have hAcauchy : CauchySeq (fun n => A (u n)) := hAu.cauchySeq
    rw [Metric.cauchySeq_iff] at hAcauchy ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hAcauchy (ε / (Ct + 1)) (div_pos hε (by linarith))
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hsmall := hN m hm n hn
    have hbound : dist (T (u m)) (T (u n)) ≤
        Ct * dist (A (u m)) (A (u n)) := by
      simpa only [dist_eq_norm, ← map_sub] using hTupper (u m - u n)
    calc
      dist (T (u m)) (T (u n)) ≤
          Ct * dist (A (u m)) (A (u n)) := hbound
      _ < ε := by
        by_cases hCt0 : Ct = 0
        · simp [hCt0, hε]
        · have hCtpos : 0 < Ct := lt_of_le_of_ne hCt (Ne.symm hCt0)
          calc
            Ct * dist (A (u m)) (A (u n)) < Ct * (ε / (Ct + 1)) :=
              mul_lt_mul_of_pos_left hsmall hCtpos
            _ < ε := by
              rw [show Ct * (ε / (Ct + 1)) = (Ct * ε) / (Ct + 1) by ring]
              apply (div_lt_iff₀ (by linarith : 0 < Ct + 1)).2
              nlinarith
  obtain ⟨z, hTu⟩ := cauchySeq_tendsto_of_complete hTcauchy
  have hz : z = 0 := hclose u hju z hTu
  simpa [hz] using hTu

/-- **Uniform graph-null transport.** A graph-null obstruction survives whenever the new source
norm is bounded above by the model source norm and the new response norm is uniformly equivalent
to the model response norm.  Thus a closable realization must have unbounded source distortion,
lose uniform response observability, or abandon an upper response bound. -/
theorem not_isSequentiallyClosableBetween_of_uniform_graphNull
    {D E K H₁ H₂ : Type*} [AddCommGroup D] [Module ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]
    [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    (T : D →ₗ[ℝ] K) (j : D →ₗ[ℝ] E)
    (A : D →ₗ[ℝ] H₂) (i : D →ₗ[ℝ] H₁)
    (Cj Ct c : ℝ) (hCt : 0 ≤ Ct) (hc : 0 < c)
    (hj : ∀ d, ‖j d‖ ≤ Cj * ‖i d‖)
    (hTupper : ∀ d, ‖T d‖ ≤ Ct * ‖A d‖)
    (hTlower : ∀ d, c * ‖A d‖ ≤ ‖T d‖)
    (u : ℕ → D) (y : H₂)
    (hiu : Tendsto (fun n => i (u n)) atTop (nhds 0))
    (hAu : Tendsto (fun n => A (u n)) atTop (nhds y)) (hy : y ≠ 0) :
    ¬ IsSequentiallyClosableBetween T j := by
  intro hclose
  have hTuZero := tendsto_zero_of_closableBetween_of_source_response_upper
    T j A i Cj Ct hCt hj hTupper hclose u y hiu hAu
  have hTnormZero : Tendsto (fun n => ‖T (u n)‖) atTop (nhds 0) := by
    simpa using hTuZero.norm
  have hquot : Tendsto (fun n => ‖T (u n)‖ / c) atTop (nhds 0) := by
    simpa using hTnormZero.div_const c
  have hAnormZero : Tendsto (fun n => ‖A (u n)‖) atTop (nhds 0) := by
    apply squeeze_zero (fun n => norm_nonneg _) _ hquot
    intro n
    exact (le_div_iff₀ hc).2 (by simpa [mul_comm] using hTlower (u n))
  have hAzero : Tendsto (fun n => A (u n)) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2 hAnormZero
  exact hy (tendsto_nhds_unique hAu hAzero)

/-- **Exact-norm graph-null transport.** A graph-null obstruction survives every pair of complete
source/target realizations that preserve the source and response norms on the algebraic core.
No common ambient Hilbert space or chosen unitary is required. -/
theorem not_isSequentiallyClosableBetween_of_exact_norm_graphNull
    {D E K H₁ H₂ : Type*} [AddCommGroup D] [Module ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]
    [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    (T : D →ₗ[ℝ] K) (j : D →ₗ[ℝ] E)
    (A : D →ₗ[ℝ] H₂) (i : D →ₗ[ℝ] H₁)
    (hjnorm : ∀ d, ‖j d‖ = ‖i d‖) (hTnorm : ∀ d, ‖T d‖ = ‖A d‖)
    (u : ℕ → D) (y : H₂)
    (hiu : Tendsto (fun n => i (u n)) atTop (nhds 0))
    (hAu : Tendsto (fun n => A (u n)) atTop (nhds y)) (hy : y ≠ 0) :
    ¬ IsSequentiallyClosableBetween T j := by
  apply not_isSequentiallyClosableBetween_of_uniform_graphNull
    T j A i 1 1 1 (by norm_num) (by norm_num)
  · intro d
    simp [hjnorm d]
  · intro d
    simp [hTnorm d]
  · intro d
    simp [hTnorm d]
  · exact hiu
  · exact hAu
  · exact hy

/-- **Arithmetic-Schur exact-rigging obstruction.** The actual-prime first-trace clock remains
nonclosable in every pair of complete Hilbert/Banach realizations preserving its exact source and
clock norms on all finite packets. -/
theorem arithmeticSchurExactNormRigging_not_closable
    {E K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]
    (j : (Nat.Primes →₀ ℝ) →ₗ[ℝ] E)
    (T : (Nat.Primes →₀ ℝ) →ₗ[ℝ] K)
    (hsource : ∀ d, ‖j d‖ = ‖primeHardyKernelMap d‖)
    (hclock : ∀ d, ‖T d‖ = ‖primeFirstTraceClock d‖) :
    ¬ IsSequentiallyClosableBetween T j := by
  exact not_isSequentiallyClosableBetween_of_exact_norm_graphNull
    T j primeFirstTraceClock primeHardyKernelMap hsource hclock
    primeFirstTraceNullSequence (lp.single 2 1 1)
    tendsto_primeHardyKernelMap_nullSequence
    tendsto_primeFirstTraceClock_nullSequence primeHardy_basisOne_ne_zero

/-- **Arithmetic-Schur uniform-rigging obstruction.** More generally, the actual-prime clock
remains nonclosable if the new source norm is bounded above by the arithmetic-Schur norm and the
new clock norm is uniformly equivalent to the Hardy first-trace norm.  Consequently every
closable pre-Hardy realization must exhibit unbounded source distortion or asymptotic loss of
clock observability. -/
theorem arithmeticSchurUniformRigging_not_closable
    {E K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]
    (j : (Nat.Primes →₀ ℝ) →ₗ[ℝ] E)
    (T : (Nat.Primes →₀ ℝ) →ₗ[ℝ] K)
    (Cj Ct c : ℝ) (hCt : 0 ≤ Ct) (hc : 0 < c)
    (hsource : ∀ d, ‖j d‖ ≤ Cj * ‖primeHardyKernelMap d‖)
    (hclockUpper : ∀ d, ‖T d‖ ≤ Ct * ‖primeFirstTraceClock d‖)
    (hclockLower : ∀ d, c * ‖primeFirstTraceClock d‖ ≤ ‖T d‖) :
    ¬ IsSequentiallyClosableBetween T j := by
  exact not_isSequentiallyClosableBetween_of_uniform_graphNull
    T j primeFirstTraceClock primeHardyKernelMap Cj Ct c hCt hc
    hsource hclockUpper hclockLower
    primeFirstTraceNullSequence (lp.single 2 1 1)
    tendsto_primeHardyKernelMap_nullSequence
    tendsto_primeFirstTraceClock_nullSequence primeHardy_basisOne_ne_zero

/-- **Arithmetic-Schur forced-collapse law.** If a source-controlled, response-bounded pre-Hardy
realization is closable, it must send the explicit actual-prime packet carrying the nonzero first
valuation limit strongly to zero. -/
theorem tendsto_arithmeticSchurRigging_nullSequence_zero_of_closable
    {E K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]
    (j : (Nat.Primes →₀ ℝ) →ₗ[ℝ] E)
    (T : (Nat.Primes →₀ ℝ) →ₗ[ℝ] K)
    (Cj Ct : ℝ) (hCt : 0 ≤ Ct)
    (hsource : ∀ d, ‖j d‖ ≤ Cj * ‖primeHardyKernelMap d‖)
    (hclockUpper : ∀ d, ‖T d‖ ≤ Ct * ‖primeFirstTraceClock d‖)
    (hclose : IsSequentiallyClosableBetween T j) :
    Tendsto (fun n => T (primeFirstTraceNullSequence n)) atTop (nhds 0) := by
  exact tendsto_zero_of_closableBetween_of_source_response_upper
    T j primeFirstTraceClock primeHardyKernelMap Cj Ct hCt
    hsource hclockUpper hclose primeFirstTraceNullSequence (lp.single 2 1 1)
    tendsto_primeHardyKernelMap_nullSequence
    tendsto_primeFirstTraceClock_nullSequence

/-- A closable source-controlled rigging cannot retain the first valuation response through any
bounded scalar marker.  The model marker is its inner product with the first Hardy basis vector,
whose value on the explicit graph-null response tends to one. -/
theorem arithmeticSchurRigging_no_bounded_firstValuationMarker_of_closable
    {E K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]
    (j : (Nat.Primes →₀ ℝ) →ₗ[ℝ] E)
    (T : (Nat.Primes →₀ ℝ) →ₗ[ℝ] K)
    (Cj Ct : ℝ) (hCt : 0 ≤ Ct)
    (hsource : ∀ d, ‖j d‖ ≤ Cj * ‖primeHardyKernelMap d‖)
    (hclockUpper : ∀ d, ‖T d‖ ≤ Ct * ‖primeFirstTraceClock d‖)
    (hclose : IsSequentiallyClosableBetween T j)
    (φ : K →L[ℝ] ℝ)
    (hmark : ∀ d, φ (T d) =
      inner ℝ (primeFirstTraceClock d) (lp.single 2 1 1)) : False := by
  let e₁ : PrimeHardy := lp.single 2 1 1
  have hTzero := tendsto_arithmeticSchurRigging_nullSequence_zero_of_closable
    j T Cj Ct hCt hsource hclockUpper hclose
  have hφzero : Tendsto
      (fun n => φ (T (primeFirstTraceNullSequence n))) atTop (nhds 0) := by
    have h := φ.continuous.continuousAt.tendsto.comp hTzero
    simpa using h
  have hmodel : Tendsto
      (fun n => inner ℝ (primeFirstTraceClock (primeFirstTraceNullSequence n)) e₁)
      atTop (nhds (inner ℝ e₁ e₁)) := by
    exact Filter.Tendsto.inner (𝕜 := ℝ)
      tendsto_primeFirstTraceClock_nullSequence tendsto_const_nhds
  have heq : (fun n => φ (T (primeFirstTraceNullSequence n))) =
      fun n => inner ℝ (primeFirstTraceClock (primeFirstTraceNullSequence n)) e₁ := by
    funext n
    exact hmark _
  rw [heq] at hφzero
  have hinner : inner ℝ e₁ e₁ = 0 :=
    tendsto_nhds_unique hmodel hφzero
  exact (inner_self_ne_zero.mpr primeHardy_basisOne_ne_zero) hinner

/-- By the closed graph theorem, the same obstruction excludes every everywhere-defined closed
linear first-valuation marker.  A surviving closed scalarization must therefore have a proper
unbounded domain; calling an everywhere-defined relation "closed" cannot evade the bounded-marker
obstruction. -/
theorem arithmeticSchurRigging_no_closed_fullDomain_firstValuationMarker
    {E K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]
    (j : (Nat.Primes →₀ ℝ) →ₗ[ℝ] E)
    (T : (Nat.Primes →₀ ℝ) →ₗ[ℝ] K)
    (Cj Ct : ℝ) (hCt : 0 ≤ Ct)
    (hsource : ∀ d, ‖j d‖ ≤ Cj * ‖primeHardyKernelMap d‖)
    (hclockUpper : ∀ d, ‖T d‖ ≤ Ct * ‖primeFirstTraceClock d‖)
    (hclose : IsSequentiallyClosableBetween T j)
    (φ : K →ₗ[ℝ] ℝ) (hφclosed : IsClosed (φ.graph : Set (K × ℝ)))
    (hmark : ∀ d, φ (T d) =
      inner ℝ (primeFirstTraceClock d) (lp.single 2 1 1)) : False := by
  let φc : K →L[ℝ] ℝ := ContinuousLinearMap.ofIsClosedGraph hφclosed
  apply arithmeticSchurRigging_no_bounded_firstValuationMarker_of_closable
    j T Cj Ct hCt hsource hclockUpper hclose φc
  intro d
  exact hmark d

/-- **No closed densely defined scalar escape.** A source-controlled closable rigging cannot retain
the first valuation response through any single-valued closed densely defined scalar relation.
Dense closed scalar rigidity first extends the partial marker to a bounded full-domain functional,
where the forced-collapse contradiction applies. -/
theorem arithmeticSchurRigging_no_closed_dense_firstValuationMarker
    {E K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]
    (j : (Nat.Primes →₀ ℝ) →ₗ[ℝ] E)
    (T : (Nat.Primes →₀ ℝ) →ₗ[ℝ] K)
    (Cj Ct : ℝ) (hCt : 0 ≤ Ct)
    (hsource : ∀ d, ‖j d‖ ≤ Cj * ‖primeHardyKernelMap d‖)
    (hclockUpper : ∀ d, ‖T d‖ ≤ Ct * ‖primeFirstTraceClock d‖)
    (hclose : IsSequentiallyClosableBetween T j)
    (φ : K →ₗ.[ℝ] ℝ) (hφclosed : φ.IsClosed)
    (hφdense : Dense (φ.domain : Set K))
    (hTdomain : ∀ d, T d ∈ φ.domain)
    (hmark : ∀ d, φ ⟨T d, hTdomain d⟩ =
      inner ℝ (primeFirstTraceClock d) (lp.single 2 1 1)) : False := by
  obtain ⟨φc, hφc⟩ :=
    GaloisForLFunctions.HilbertMetric.dense_closed_scalarLinearPMap_exists_continuous_extension
      φ hφclosed hφdense
  apply arithmeticSchurRigging_no_bounded_firstValuationMarker_of_closable
    j T Cj Ct hCt hsource hclockUpper hclose φc
  intro d
  rw [hφc ⟨T d, hTdomain d⟩]
  exact hmark d

/-- The same conclusion holds if the densely defined scalar marker is merely closable: its closure
would be a closed dense scalar relation and hence a bounded full-domain extension. -/
theorem arithmeticSchurRigging_no_closable_dense_firstValuationMarker
    {E K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]
    (j : (Nat.Primes →₀ ℝ) →ₗ[ℝ] E)
    (T : (Nat.Primes →₀ ℝ) →ₗ[ℝ] K)
    (Cj Ct : ℝ) (hCt : 0 ≤ Ct)
    (hsource : ∀ d, ‖j d‖ ≤ Cj * ‖primeHardyKernelMap d‖)
    (hclockUpper : ∀ d, ‖T d‖ ≤ Ct * ‖primeFirstTraceClock d‖)
    (hclose : IsSequentiallyClosableBetween T j)
    (φ : K →ₗ.[ℝ] ℝ) (hφclosable : φ.IsClosable)
    (hφdense : Dense (φ.domain : Set K))
    (hTdomain : ∀ d, T d ∈ φ.domain)
    (hmark : ∀ d, φ ⟨T d, hTdomain d⟩ =
      inner ℝ (primeFirstTraceClock d) (lp.single 2 1 1)) : False := by
  obtain ⟨φc, hφc⟩ :=
    GaloisForLFunctions.HilbertMetric.dense_closable_scalarLinearPMap_exists_continuous_extension
      φ hφclosable hφdense
  apply arithmeticSchurRigging_no_bounded_firstValuationMarker_of_closable
    j T Cj Ct hCt hsource hclockUpper hclose φc
  intro d
  rw [hφc ⟨T d, hTdomain d⟩]
  exact hmark d

end

end RHTower
