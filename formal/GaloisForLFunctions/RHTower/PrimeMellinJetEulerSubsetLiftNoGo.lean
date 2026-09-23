import GaloisForLFunctions.RHTower.PrimeMellinJetDiagonalEnergyNoGo

/-!
# Euler-subset positive-lift no-go for prime Mellin jets

An off-diagonal incidence can evade the resolved-channel commutant only by mixing prime outputs.
This file classifies such mixing under the source-functorial requirement that every finite Euler
subproduct have its exact additive energy.  Four finite subsets force distinct prime packets to
have zero real covariance, even when an arbitrary fixed Gamma/polar boundary vector is included
before the norm.  More strongly, any nonnegative nonsummable local energy makes the completed
finite-packet norms unbounded.  Thus arbitrary channel mixing cannot repair the positive-log
Mellin divergence while retaining Euler-subset positivity.

No zero data, RH-equivalent positivity, limiting computation, or target moment is used.
-/

namespace RHTower

noncomputable section

/-- Exact positive energy law for every finite source subset.  `base` may contain arbitrary fixed
Gamma and polar boundary modes; `packet i` may live anywhere in the ambient normed space. -/
def EulerSubsetNormSqExact
    {ι E : Type*} [NormedAddCommGroup E]
    (base : E) (packet : ι → E) (energy : ι → ℝ) (baseline : ℝ) : Prop :=
  ∀ F : Finset ι,
    ‖base + ∑ i ∈ F, packet i‖ ^ (2 : ℕ) = baseline + ∑ i ∈ F, energy i

/-- Lower-bound form of the Euler-subset positive energy law.  Exactness is unnecessary for the
unboundedness obstruction. -/
def EulerSubsetNormSqLower
    {ι E : Type*} [NormedAddCommGroup E]
    (base : E) (packet : ι → E) (energy : ι → ℝ) (baseline : ℝ) : Prop :=
  ∀ F : Finset ι,
    baseline + ∑ i ∈ F, energy i ≤ ‖base + ∑ i ∈ F, packet i‖ ^ (2 : ℕ)

/-- The empty Euler subset fixes the scalar baseline to the squared boundary norm. -/
theorem eulerSubsetNormSqExact_baseline_eq_normSq
    {ι E : Type*} [NormedAddCommGroup E]
    (base : E) (packet : ι → E) (energy : ι → ℝ) (baseline : ℝ)
    (h : EulerSubsetNormSqExact base packet energy baseline) :
    baseline = ‖base‖ ^ (2 : ℕ) := by
  simpa only [Finset.sum_empty, add_zero] using (h ∅).symm

/-- Exact finite-subset energy implies its lower-bound version. -/
theorem EulerSubsetNormSqExact.toLower
    {ι E : Type*} [NormedAddCommGroup E]
    {base : E} {packet : ι → E} {energy : ι → ℝ} {baseline : ℝ}
    (h : EulerSubsetNormSqExact base packet energy baseline) :
    EulerSubsetNormSqLower base packet energy baseline := by
  intro F
  exact (h F).ge

/-- **Four-subset rigidity.**  Exact additivity on the empty, two singleton, and pair subsets
annihilates the real covariance of two distinct packets.  In a complex Hilbert space an imaginary
inner product may remain, but it is invisible to every norm square and cannot cancel energy. -/
theorem eulerSubsetNormSqExact_pairwise_re_inner_zero
    {ι 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (base : E) (packet : ι → E) (energy : ι → ℝ) (baseline : ℝ)
    (h : EulerSubsetNormSqExact base packet energy baseline)
    {i j : ι} (hij : i ≠ j) :
    RCLike.re (inner 𝕜 (packet i) (packet j)) = 0 := by
  classical
  have h0 := h ∅
  have hi := h {i}
  have hj := h {j}
  have hp := h {i, j}
  simp only [Finset.sum_empty, add_zero] at h0
  simp only [Finset.sum_singleton] at hi hj
  simp only [Finset.sum_pair hij] at hp
  have hbi := norm_add_sq (𝕜 := 𝕜) base (packet i)
  have hbj := norm_add_sq (𝕜 := 𝕜) base (packet j)
  have hbij := norm_add_sq (𝕜 := 𝕜) base (packet i + packet j)
  have hij' := norm_add_sq (𝕜 := 𝕜) (packet i) (packet j)
  simp only [inner_add_right, map_add] at hbij
  nlinarith

/-- **Abstract positive-subset obstruction.**  A lower Euler-subset norm law with nonnegative,
nonsummable local energy cannot have uniformly bounded finite packets.  No linearity, channel
preservation, fixed-boundary premise, or inner-product expansion is needed for this part. -/
theorem not_exists_bounded_eulerSubsetNormSqLower_of_not_summable
    {ι E : Type*} [NormedAddCommGroup E]
    (base : E) (packet : ι → E) (energy : ι → ℝ) (baseline : ℝ)
    (hnonneg : ∀ i, 0 ≤ energy i) (hnot : ¬ Summable energy)
    (h : EulerSubsetNormSqLower base packet energy baseline) :
    ¬ ∃ C : ℝ, ∀ F : Finset ι,
      ‖base + ∑ i ∈ F, packet i‖ ^ (2 : ℕ) ≤ C := by
  rintro ⟨C, hC⟩
  apply hnot
  apply summable_of_sum_le (c := C - baseline) hnonneg
  intro F
  have hlower := h F
  have hupper := hC F
  nlinarith

/-- Exact Euler-subset energies with nonsummable nonnegative local mass are unbounded. -/
theorem not_exists_bounded_eulerSubsetNormSqExact_of_not_summable
    {ι E : Type*} [NormedAddCommGroup E]
    (base : E) (packet : ι → E) (energy : ι → ℝ) (baseline : ℝ)
    (hnonneg : ∀ i, 0 ≤ energy i) (hnot : ¬ Summable energy)
    (h : EulerSubsetNormSqExact base packet energy baseline) :
    ¬ ∃ C : ℝ, ∀ F : Finset ι,
      ‖base + ∑ i ∈ F, packet i‖ ^ (2 : ℕ) ≤ C :=
  not_exists_bounded_eulerSubsetNormSqLower_of_not_summable
    base packet energy baseline hnonneg hnot h.toLower

/-- Quantitative logical form: every proposed bound is exceeded by one finite source subset. -/
theorem exists_finset_normSq_gt_of_eulerSubsetNormSqLower_of_not_summable
    {ι E : Type*} [NormedAddCommGroup E]
    (base : E) (packet : ι → E) (energy : ι → ℝ) (baseline : ℝ)
    (hnonneg : ∀ i, 0 ≤ energy i) (hnot : ¬ Summable energy)
    (h : EulerSubsetNormSqLower base packet energy baseline) (C : ℝ) :
    ∃ F : Finset ι, C < ‖base + ∑ i ∈ F, packet i‖ ^ (2 : ℕ) := by
  by_contra hbound
  push Not at hbound
  exact (not_exists_bounded_eulerSubsetNormSqLower_of_not_summable
    base packet energy baseline hnonneg hnot h) ⟨C, hbound⟩

/-- Every local positive-log prime Mellin energy is nonnegative. -/
theorem primeMellinJetDiagonalEnergy_nonneg (r : ℕ) (p : Nat.Primes) :
    0 ≤ primeMellinJetDiagonalEnergy r p := by
  rw [primeMellinJetDiagonalEnergy, finiteVonMangoldtRealWeight,
    ArithmeticFunction.vonMangoldt_apply_prime p.prop]
  positivity

/-- **Prime-Mellin Euler-subset no-go.**  No exact positive lift of a positive-log Mellin jet has
uniformly bounded finite Euler packets, even with an arbitrary boundary vector and arbitrary
off-diagonal output locations. -/
theorem no_bounded_primeMellinJet_eulerSubsetPositiveLift
    {E : Type*} [NormedAddCommGroup E]
    (r : ℕ) (base : E) (packet : Nat.Primes → E) (baseline : ℝ)
    (h : EulerSubsetNormSqExact base packet (primeMellinJetDiagonalEnergy r) baseline) :
    ¬ ∃ C : ℝ, ∀ F : Finset Nat.Primes,
      ‖base + ∑ p ∈ F, packet p‖ ^ (2 : ℕ) ≤ C :=
  not_exists_bounded_eulerSubsetNormSqExact_of_not_summable
    base packet (primeMellinJetDiagonalEnergy r) baseline
    (primeMellinJetDiagonalEnergy_nonneg r)
    (not_summable_primeMellinJetDiagonalEnergy r) h

/-- **Off-diagonal mixing classification.**  Any Hilbert realization of the exact finite-Euler
source law has pairwise zero real prime covariance, yet its finite completed packets are
unbounded.  Hence mixing is only a real-orthogonal re-embedding and cannot cure the energy wall. -/
theorem primeMellinJet_eulerSubsetPositiveLift_classification
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (r : ℕ) (base : E) (packet : Nat.Primes → E) (baseline : ℝ)
    (h : EulerSubsetNormSqExact base packet (primeMellinJetDiagonalEnergy r) baseline) :
    (∀ {p q : Nat.Primes}, p ≠ q →
      RCLike.re (inner 𝕜 (packet p) (packet q)) = 0) ∧
      ¬ ∃ C : ℝ, ∀ F : Finset Nat.Primes,
        ‖base + ∑ p ∈ F, packet p‖ ^ (2 : ℕ) ≤ C := by
  constructor
  · intro p q hpq
    exact eulerSubsetNormSqExact_pairwise_re_inner_zero
      base packet (primeMellinJetDiagonalEnergy r) baseline h hpq
  · exact no_bounded_primeMellinJet_eulerSubsetPositiveLift r base packet baseline h

end

end RHTower
