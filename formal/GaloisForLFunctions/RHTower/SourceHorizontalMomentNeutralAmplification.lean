import GaloisForLFunctions.RHTower.SourceZeroHorizontalCarrier
import GaloisForLFunctions.RHTower.PrimeGammaCofinalBocksteinCStarShilovBlindness

/-!
# Source-horizontal moment-neutral amplification

An off-line source-horizontal Xi copy is nonzero at every ordinary-prime label, but its signed
coefficients tend to zero along the cofinite prime filter. Consequently it already admits
arbitrarily large packets of distinct labelled hyperbolic blocks with arbitrarily small average
Frobenius-square cost. Reflection negates every coefficient and preserves that cost exactly.

This is the precise moment-neutral amplification requested by the finite rank--trace route. It is
not an RH producer: raw hyperbolic inertia is scale-free, while any fixed spectral threshold forces
linear Frobenius-square cost. The rank--trace inequality must price every nonzero positive-index
unit even when its eigenvalue is arbitrarily small. Thus second moments control only thresholded
inertia, not raw inertia.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Real `2 x 2` hyperbolic block attached to one source coefficient. -/
def sourceHorizontalHyperbolicBlock (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, a; a, 0]

/-- Frobenius-square cost of the real hyperbolic block with eigenvalues `+|a|,-|a|`. -/
def sourceHorizontalHyperbolicFrobSq (a : ℝ) : ℝ := 2 * a ^ (2 : ℕ)

@[simp] theorem sourceHorizontalHyperbolicBlock_trace (a : ℝ) :
    Matrix.trace (sourceHorizontalHyperbolicBlock a) = 0 := by
  simp [sourceHorizontalHyperbolicBlock, Matrix.trace]

theorem sourceHorizontalHyperbolicBlock_entrySq_sum (a : ℝ) :
    (∑ i, ∑ j, (sourceHorizontalHyperbolicBlock a i j) ^ (2 : ℕ)) =
      sourceHorizontalHyperbolicFrobSq a := by
  simp [sourceHorizontalHyperbolicBlock, sourceHorizontalHyperbolicFrobSq]
  ring

@[simp] theorem sourceHorizontalHyperbolicFrobSq_neg (a : ℝ) :
    sourceHorizontalHyperbolicFrobSq (-a) =
      sourceHorizontalHyperbolicFrobSq a := by
  simp [sourceHorizontalHyperbolicFrobSq]

theorem sourceHorizontalHyperbolicFrobSq_nonneg (a : ℝ) :
    0 ≤ sourceHorizontalHyperbolicFrobSq a := by
  unfold sourceHorizontalHyperbolicFrobSq
  positivity

/-- Fixed spectral size forces linear Frobenius-square cost. This is the exact thresholded-index
wall: sublinear second moment can amplify only blocks whose eigenvalues collapse to zero. -/
theorem sourceHorizontalHyperbolicFrobSq_sum_ge
    {ι : Type*} [DecidableEq ι] (K : Finset ι) (a : ι → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hvisible : ∀ i ∈ K, δ ≤ |a i|) :
    2 * δ ^ (2 : ℕ) * (K.card : ℝ) ≤
      ∑ i ∈ K, sourceHorizontalHyperbolicFrobSq (a i) := by
  calc
    2 * δ ^ (2 : ℕ) * (K.card : ℝ) =
        ∑ i ∈ K, 2 * δ ^ (2 : ℕ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
    _ ≤ ∑ i ∈ K, sourceHorizontalHyperbolicFrobSq (a i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hsquare : δ ^ (2 : ℕ) ≤ |a i| ^ (2 : ℕ) :=
        (sq_le_sq₀ hδ (abs_nonneg (a i))).2 (hvisible i hi)
      rw [sq_abs] at hsquare
      unfold sourceHorizontalHyperbolicFrobSq
      linarith

/-- Every off-line multiplicity copy has arbitrarily large distinct-prime hyperbolic packets whose
average Frobenius-square cost is arbitrarily small. Prime labels, the multiplicity copy, and
nonvanishing of every block are retained. -/
theorem exists_sourceZeroHorizontalMomentNeutralPacket
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) (m : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Finset Nat.Primes,
      K.card = m ∧
      (∀ p ∈ K,
        sourceZeroHorizontalPrimeCarrier q p ≠ 0 ∧
          |sourceZeroHorizontalPrimeCarrier q p| < ε) ∧
      (∑ p ∈ K,
          sourceHorizontalHyperbolicFrobSq
            (sourceZeroHorizontalPrimeCarrier q p)) ≤
        2 * ε ^ (2 : ℕ) * (m : ℝ) := by
  have ht : |primeDepthBVWoldXiCenteredRate q.1| < 1 :=
    xiCenteredPrimeIdealRate_abs_lt_one q.1
  have hlim : Tendsto (sourceZeroHorizontalPrimeCarrier q)
      cofinite (nhds 0) := by
    change Tendsto
      (primeGammaCofinalBocksteinCoefficient
        (primeDepthBVWoldXiCenteredRate q.1)) cofinite (nhds 0)
    exact primeGammaCofinalBocksteinCoefficient_tendsto_cofinite_zero ht
  have hevent : ∀ᶠ p : Nat.Primes in cofinite,
      |sourceZeroHorizontalPrimeCarrier q p| < ε := by
    have hball : ∀ᶠ p : Nat.Primes in cofinite,
        sourceZeroHorizontalPrimeCarrier q p ∈ Metric.ball (0 : ℝ) ε :=
      hlim (Metric.ball_mem_nhds (0 : ℝ) hε)
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hball
  let S : Set Nat.Primes :=
    {p | |sourceZeroHorizontalPrimeCarrier q p| < ε}
  have hfinite : Sᶜ.Finite := by
    simpa only [S, Set.compl_setOf] using
      (Filter.eventually_cofinite.mp hevent)
  have hinfinite : S.Infinite := by
    simpa only [compl_compl] using Set.Finite.infinite_compl hfinite
  obtain ⟨K, hKS, hKcard⟩ := hinfinite.exists_subset_card_eq m
  refine ⟨K, hKcard, ?_, ?_⟩
  · intro p hp
    exact ⟨(not_congr (sourceZeroHorizontalPrimeCarrier_eq_zero_iff q p)).mpr hoff,
      hKS hp⟩
  · calc
      (∑ p ∈ K,
          sourceHorizontalHyperbolicFrobSq
            (sourceZeroHorizontalPrimeCarrier q p)) ≤
          ∑ p ∈ K, 2 * ε ^ (2 : ℕ) := by
            apply Finset.sum_le_sum
            intro p hp
            have hsmall : |sourceZeroHorizontalPrimeCarrier q p| < ε := hKS hp
            have hsquare :
                |sourceZeroHorizontalPrimeCarrier q p| ^ (2 : ℕ) ≤ ε ^ (2 : ℕ) :=
              (sq_le_sq₀ (abs_nonneg _) hε.le).2 hsmall.le
            rw [sq_abs] at hsquare
            unfold sourceHorizontalHyperbolicFrobSq
            linarith
      _ = 2 * ε ^ (2 : ℕ) * (m : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, hKcard]
        ring

/-- Reflection retains the same labelled packet and exactly the same Frobenius-square budget. -/
theorem sourceZeroHorizontalMomentNeutralPacket_reflection_energy
    (q : XiZeroCopy) (K : Finset Nat.Primes) :
    (∑ p ∈ K,
        sourceHorizontalHyperbolicFrobSq
          (sourceZeroHorizontalPrimeCarrier (xiZeroCopyLineConjEquiv q) p)) =
      ∑ p ∈ K,
        sourceHorizontalHyperbolicFrobSq
          (sourceZeroHorizontalPrimeCarrier q p) := by
  apply Finset.sum_congr rfl
  intro p hp
  rw [sourceZeroHorizontalPrimeCarrier_reflection,
    sourceHorizontalHyperbolicFrobSq_neg]

end

end RHTower
