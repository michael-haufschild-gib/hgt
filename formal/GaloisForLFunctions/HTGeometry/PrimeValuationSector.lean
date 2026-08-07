import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Geometric
import GaloisForLFunctions.HTGeometry.PrimeSieveDensityTelescope
import GaloisForLFunctions.HTGeometry.ConditioningTotalVariation

/-!
# The prime-valuation product sector

At a prime `p` the valuation of a random integer is geometric with success probability `1 - 1/p`:
the local law is `μ_p(k) = (1 - 1/p) p^{-k}`.  Taking the product over all primes gives a
probability measure on `∏_p ℕ`, and the event that every prime in a finite set `P` has valuation
zero is a cylinder whose mass is exactly the sieve density `∏_{p ∈ P} (1 - 1/p)`.

This identifies the finite-variation sieve density layer with a genuine product probability sector,
so the conditioning contrast — normalized states move by the mass *ratio*, unnormalized restrictions
by the mass *difference* — applies to it verbatim.
-/

open MeasureTheory ProbabilityTheory Set

namespace GaloisForLFunctions.HTGeometry

/-! ## The local valuation law -/

/-- Success probability of the valuation law at `p`. -/
noncomputable def primeValuationParam (p : Nat.Primes) : unitInterval := by
  refine ⟨1 - (((p : ℕ) : ℝ))⁻¹, ?_, ?_⟩
  · have h1 := one_lt_prime_cast p
    have h2 : (((p : ℕ) : ℝ))⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      exact Or.inr h1.le
    linarith
  · have h : (0 : ℝ) < (((p : ℕ) : ℝ))⁻¹ := by
      have := one_lt_prime_cast p
      positivity
    linarith

@[simp] theorem primeValuationParam_coe (p : Nat.Primes) :
    ((primeValuationParam p : unitInterval) : ℝ) = 1 - (((p : ℕ) : ℝ))⁻¹ := rfl

theorem primeValuationParam_ne_zero (p : Nat.Primes) :
    primeValuationParam p ≠ 0 := by
  intro h
  have hcoe : ((primeValuationParam p : unitInterval) : ℝ) = 0 := by
    rw [h]; rfl
  rw [primeValuationParam_coe] at hcoe
  have h1 := one_lt_prime_cast p
  have h2 : (((p : ℕ) : ℝ))⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    exact Or.inr h1
  linarith

/-- Local valuation law at `p`: the valuation is geometric with success
probability `1 - 1/p`. -/
noncomputable def primeValuationLaw (p : Nat.Primes) : Measure ℕ :=
  geometricMeasure (primeValuationParam p)

instance instIsProbabilityMeasurePrimeValuationLaw (p : Nat.Primes) :
    IsProbabilityMeasure (primeValuationLaw p) :=
  isProbabilityMeasure_geometricMeasure

/-- The local law gives valuation zero exactly the sieve factor `1 - 1/p`. -/
theorem primeValuationLaw_zero (p : Nat.Primes) :
    primeValuationLaw p {0} = ENNReal.ofReal (1 - (((p : ℕ) : ℝ))⁻¹) := by
  rw [primeValuationLaw,
    geometricMeasure_singleton (primeValuationParam_ne_zero p) 0]
  simp

/-! ## The product sector -/

/-- The prime-valuation sector: the product of the local laws over all primes. -/
noncomputable def primeValuationMeasure : Measure (∀ _ : Nat.Primes, ℕ) :=
  Measure.infinitePi primeValuationLaw

instance : IsProbabilityMeasure primeValuationMeasure := by
  rw [primeValuationMeasure]
  infer_instance

/-- The event that every prime in `P` has valuation zero. -/
def primeValuationCylinder (P : Finset Nat.Primes) :
    Set (∀ _ : Nat.Primes, ℕ) :=
  Set.pi (↑P) fun _ => {0}

theorem measurableSet_primeValuationCylinder (P : Finset Nat.Primes) :
    MeasurableSet (primeValuationCylinder P) :=
  MeasurableSet.pi P.countable_toSet fun _ _ => measurableSet_singleton 0

theorem primeValuationCylinder_antitone {P Q : Finset Nat.Primes}
    (hPQ : P ⊆ Q) : primeValuationCylinder Q ⊆ primeValuationCylinder P := by
  intro k hk p hp
  exact hk p (hPQ hp)

/-- **The cylinder mass is the sieve density.**  This identifies the corpus's
finite-variation sieve layer with a product probability sector. -/
theorem primeValuationMeasure_cylinder (P : Finset Nat.Primes) :
    primeValuationMeasure (primeValuationCylinder P) =
      ENNReal.ofReal (sieveDensity P) := by
  have hpi := Measure.infinitePi_pi (μ := primeValuationLaw) (s := P)
    (t := fun _ : Nat.Primes => ({0} : Set ℕ))
    (fun p _ => measurableSet_singleton 0)
  rw [primeValuationMeasure, primeValuationCylinder, hpi, sieveDensity,
    ENNReal.ofReal_prod_of_nonneg]
  · exact Finset.prod_congr rfl fun p _ => primeValuationLaw_zero p
  · intro p _
    have h1 := one_lt_prime_cast p
    have h2 : (((p : ℕ) : ℝ))⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      exact Or.inr h1.le
    linarith

theorem primeValuationMeasure_cylinder_ne_zero (P : Finset Nat.Primes) :
    primeValuationMeasure (primeValuationCylinder P) ≠ 0 := by
  rw [primeValuationMeasure_cylinder, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact sieveDensity_pos P

theorem toReal_primeValuationMeasure_cylinder (P : Finset Nat.Primes) :
    (primeValuationMeasure (primeValuationCylinder P)).toReal = sieveDensity P := by
  rw [primeValuationMeasure_cylinder,
    ENNReal.toReal_ofReal (sieveDensity_pos P).le]

/-! ## The amplification contrast on the sector -/

/-- **Normalized sieve states move by the density ratio.**  Conditioning from the
`P`-cylinder down to the `Q`-cylinder displaces the state by exactly
`1 - sieveDensity Q / sieveDensity P`, uniformly over test sets. -/
theorem abs_toReal_cond_primeValuation_le {P Q : Finset Nat.Primes}
    (hPQ : P ⊆ Q) (A : Set (∀ _ : Nat.Primes, ℕ)) :
    |((ProbabilityTheory.cond primeValuationMeasure
          (primeValuationCylinder Q)) A).toReal -
        ((ProbabilityTheory.cond primeValuationMeasure
          (primeValuationCylinder P)) A).toReal| ≤
      1 - sieveDensity Q / sieveDensity P := by
  have h := abs_toReal_cond_sub_cond_le primeValuationMeasure
    (measurableSet_primeValuationCylinder P)
    (measurableSet_primeValuationCylinder Q)
    (primeValuationCylinder_antitone hPQ)
    (primeValuationMeasure_cylinder_ne_zero P)
    (primeValuationMeasure_cylinder_ne_zero Q) A
  rwa [toReal_primeValuationMeasure_cylinder,
    toReal_primeValuationMeasure_cylinder] at h

/-- Adjoining one prime displaces the normalized state by exactly `1 / p`. -/
theorem abs_toReal_cond_primeValuation_insert_le {p : Nat.Primes}
    {P : Finset Nat.Primes} (hp : p ∉ P)
    (A : Set (∀ _ : Nat.Primes, ℕ)) :
    |((ProbabilityTheory.cond primeValuationMeasure
          (primeValuationCylinder (insert p P))) A).toReal -
        ((ProbabilityTheory.cond primeValuationMeasure
          (primeValuationCylinder P)) A).toReal| ≤ (((p : ℕ) : ℝ))⁻¹ := by
  have h := abs_toReal_cond_primeValuation_le (Finset.subset_insert p P) A
  rw [sieveDensity_insert hp] at h
  have hpos := sieveDensity_pos P
  rw [mul_comm, mul_div_assoc, div_self hpos.ne'] at h
  simpa using h

/-- **Unnormalized restrictions move only by the density difference**, which is
the quantity that telescopes. -/
theorem toReal_restrict_primeValuation_le {P Q : Finset Nat.Primes}
    (hPQ : P ⊆ Q) (A : Set (∀ _ : Nat.Primes, ℕ)) :
    (primeValuationMeasure.restrict (primeValuationCylinder P) A).toReal -
        (primeValuationMeasure.restrict (primeValuationCylinder Q) A).toReal ≤
      sieveDensity P - sieveDensity Q := by
  have h := toReal_restrict_sub_restrict_le primeValuationMeasure
    (measurableSet_primeValuationCylinder P)
    (measurableSet_primeValuationCylinder Q)
    (primeValuationCylinder_antitone hPQ) A
  rwa [toReal_primeValuationMeasure_cylinder,
    toReal_primeValuationMeasure_cylinder] at h


/-! ## The atomic weak limit is maximally far in strong variation -/

/-- The all-zero valuation point: no prime divides. -/
def zeroValuation : ∀ _ : Nat.Primes, ℕ := fun _ => 0

theorem zeroValuation_mem_cylinder (P : Finset Nat.Primes) :
    zeroValuation ∈ primeValuationCylinder P := fun _ _ => rfl

/-- **The sector is atomless at the all-zero valuation.**  The point lies in every
cylinder, and the sieve densities squeeze its mass to zero along any prime
enumeration. -/
theorem primeValuationMeasure_zeroValuation (e : ℕ ≃ Nat.Primes) :
    primeValuationMeasure {zeroValuation} = 0 := by
  have hle : ∀ n : ℕ,
      (primeValuationMeasure {zeroValuation}).toReal ≤
        sieveDensity (sievePrefix e n) := by
    intro n
    rw [← toReal_primeValuationMeasure_cylinder (sievePrefix e n)]
    refine ENNReal.toReal_mono
      (by rw [primeValuationMeasure_cylinder]; exact ENNReal.ofReal_ne_top) ?_
    exact measure_mono (by
      rintro k rfl
      exact zeroValuation_mem_cylinder _)
  have hzero : (primeValuationMeasure {zeroValuation}).toReal ≤ 0 :=
    ge_of_tendsto (tendsto_sieveDensity_sievePrefix e)
      (Filter.Eventually.of_forall hle)
  have hnn : 0 ≤ (primeValuationMeasure {zeroValuation}).toReal :=
    ENNReal.toReal_nonneg
  have hfin : primeValuationMeasure {zeroValuation} ≠ ⊤ :=
    measure_ne_top _ _
  have htr : (primeValuationMeasure {zeroValuation}).toReal = 0 :=
    le_antisymm hzero hnn
  rcases (ENNReal.toReal_eq_zero_iff _).mp htr with h | h
  · exact h
  · exact absurd h hfin

/-- Every normalized sieve state gives the all-zero valuation mass zero. -/
theorem cond_primeValuation_zeroValuation (e : ℕ ≃ Nat.Primes)
    (P : Finset Nat.Primes) :
    (ProbabilityTheory.cond primeValuationMeasure
      (primeValuationCylinder P)) {zeroValuation} = 0 := by
  rw [ProbabilityTheory.cond_apply (measurableSet_primeValuationCylinder P)]
  have hsub : primeValuationCylinder P ∩ {zeroValuation} ⊆ {zeroValuation} :=
    inter_subset_right
  have hzero : primeValuationMeasure
      (primeValuationCylinder P ∩ {zeroValuation}) = 0 :=
    nonpos_iff_eq_zero.mp (le_trans (measure_mono hsub)
      (le_of_eq (primeValuationMeasure_zeroValuation e)))
  rw [hzero, mul_zero]

/-- **Maximal strong separation from the weak limit.**  The normalized states put
no mass on the all-zero valuation, while the atomic weak limit puts all of it
there, so they are at total-variation distance one — the maximum — at every
finite stage. -/
theorem abs_toReal_cond_sub_dirac_zeroValuation (e : ℕ ≃ Nat.Primes)
    (P : Finset Nat.Primes) :
    |((ProbabilityTheory.cond primeValuationMeasure
          (primeValuationCylinder P)) {zeroValuation}).toReal -
        ((Measure.dirac zeroValuation) {zeroValuation}).toReal| = 1 := by
  rw [cond_primeValuation_zeroValuation e P,
    MeasureTheory.Measure.dirac_apply_of_mem (mem_singleton zeroValuation)]
  norm_num

/-! ## The sieve weights are event probabilities of the sector -/

/-- The local law gives a positive valuation exactly probability `1 / p`: this is
the second factor of the restarted Euler sieve weight. -/
theorem primeValuationLaw_compl_zero (p : Nat.Primes) :
    primeValuationLaw p {0}ᶜ = ENNReal.ofReal ((((p : ℕ) : ℝ))⁻¹) := by
  have hnn : (0 : ℝ) ≤ 1 - (((p : ℕ) : ℝ))⁻¹ := by
    have h1 : (((p : ℕ) : ℝ))⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      exact Or.inr (one_lt_prime_cast p).le
    linarith
  rw [prob_compl_eq_one_sub (measurableSet_singleton 0), primeValuationLaw_zero,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hnn]
  congr 1
  ring

/-- Along a full enumeration the cylinders shrink exactly to the all-zero
valuation. -/
theorem iInter_primeValuationCylinder (e : ℕ ≃ Nat.Primes) :
    ⋂ n, primeValuationCylinder (sievePrefix e n) = {zeroValuation} := by
  ext k
  constructor
  · intro hk
    funext p
    have hmem := Set.mem_iInter.mp hk (e.symm p + 1)
    have hp : p ∈ sievePrefix e (e.symm p + 1) := by
      simp only [sievePrefix, Finset.mem_image, Finset.mem_range]
      exact ⟨e.symm p, Nat.lt_succ_self _, e.apply_symm_apply p⟩
    exact hmem p hp
  · rintro rfl
    exact Set.mem_iInter.mpr fun n => zeroValuation_mem_cylinder _

/-- **Almost surely some prime divides.**  This is the probabilistic content of
the sieve's unit total variation: the surviving set of the full sieve is null. -/
theorem ae_exists_valuation_ne_zero (e : ℕ ≃ Nat.Primes) :
    ∀ᵐ k ∂primeValuationMeasure, ∃ p : Nat.Primes, k p ≠ 0 := by
  have hnull : primeValuationMeasure {zeroValuation} = 0 :=
    primeValuationMeasure_zeroValuation e
  refine MeasureTheory.measure_mono_null (fun k hk => ?_) hnull
  have hall : ∀ p : Nat.Primes, k p = 0 := by
    intro p
    by_contra hp
    exact hk ⟨p, hp⟩
  exact Set.mem_singleton_iff.mpr (funext hall)

/-! ## The sector is the independent-valuations model -/

/-- Reading off the valuation at one prime pushes the sector forward to that
prime's local law. -/
theorem measurePreserving_eval_primeValuation (p : Nat.Primes) :
    MeasurePreserving (Function.eval p) primeValuationMeasure
      (primeValuationLaw p) :=
  measurePreserving_eval_infinitePi primeValuationLaw p

/-- **A prime divides with probability exactly `1 / p`.**  The probabilistic form
of the local sieve factor. -/
theorem primeValuationMeasure_divides (p : Nat.Primes) :
    primeValuationMeasure {k | k p ≠ 0} =
      ENNReal.ofReal ((((p : ℕ) : ℝ))⁻¹) := by
  have hpre : Function.eval p ⁻¹' ({0}ᶜ) = {k : ∀ _ : Nat.Primes, ℕ | k p ≠ 0} := by
    ext k
    simp [Function.eval]
  have hmap := (measurePreserving_eval_primeValuation p).measure_preimage
    ((measurableSet_singleton 0).compl).nullMeasurableSet
  rw [hpre] at hmap
  rw [hmap, primeValuationLaw_compl_zero]

/-- Complementarily, a prime fails to divide with probability `1 - 1/p`. -/
theorem primeValuationMeasure_not_divides (p : Nat.Primes) :
    primeValuationMeasure {k | k p = 0} =
      ENNReal.ofReal (1 - (((p : ℕ) : ℝ))⁻¹) := by
  have hpre : Function.eval p ⁻¹' ({0} : Set ℕ) =
      {k : ∀ _ : Nat.Primes, ℕ | k p = 0} := by
    ext k
    simp [Function.eval]
  have hmap := (measurePreserving_eval_primeValuation p).measure_preimage
    (measurableSet_singleton 0).nullMeasurableSet
  rw [hpre] at hmap
  rw [hmap, primeValuationLaw_zero]

/-- **The valuations at distinct primes are independent.**  This is the
probabilistic content of the Euler product, and it is what makes the cylinder mass
a product of local factors. -/
theorem iIndepFun_primeValuation :
    ProbabilityTheory.iIndepFun
      (fun (p : Nat.Primes) (k : ∀ _ : Nat.Primes, ℕ) => k p)
      primeValuationMeasure :=
  ProbabilityTheory.iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id

/-- The event that every prime in `P` divides. -/
def primeValuationDividedCylinder (P : Finset Nat.Primes) :
    Set (∀ _ : Nat.Primes, ℕ) :=
  Set.pi (↑P) fun _ => {0}ᶜ

/-- **Every prime in `P` divides with probability `∏_{p ∈ P} 1 / p`.**  The
reciprocal of the product of the primes: the density of the multiples of their
product. -/
theorem primeValuationMeasure_dividedCylinder (P : Finset Nat.Primes) :
    primeValuationMeasure (primeValuationDividedCylinder P) =
      ENNReal.ofReal (∏ p ∈ P, (((p : ℕ) : ℝ))⁻¹) := by
  have hpi := Measure.infinitePi_pi (μ := primeValuationLaw) (s := P)
    (t := fun _ : Nat.Primes => ({0}ᶜ : Set ℕ))
    (fun p _ => (measurableSet_singleton 0).compl)
  rw [primeValuationMeasure, primeValuationDividedCylinder, hpi,
    ENNReal.ofReal_prod_of_nonneg]
  · exact Finset.prod_congr rfl fun p _ => primeValuationLaw_compl_zero p
  · intro p _
    have := one_lt_prime_cast p
    positivity

end GaloisForLFunctions.HTGeometry
