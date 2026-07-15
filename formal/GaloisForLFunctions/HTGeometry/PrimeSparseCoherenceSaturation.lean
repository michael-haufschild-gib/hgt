import GaloisForLFunctions.HTGeometry.SparseCoherenceSelection
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Prime sparse coherence saturation

Positive prime power weights are cofinally small: outside every finite set of
primes one can find a fresh prime with arbitrarily small squared weight.  This
discharges the remaining arithmetic selection hypothesis in the finite-rank
coherence-local differential-saturation theorem.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

noncomputable section

/-- The horizontal prime coherence weight `p^(-sigma)`. -/
def primeCoherenceWeight (sigma : ℝ) (p : Nat.Primes) : ℝ :=
  ((p : ℕ) : ℝ) ^ (-sigma)

/-- For every positive exponent, arbitrarily small squared prime weights remain
outside every prescribed finite set of primes. -/
theorem primeCoherenceWeight_cofinally_small (sigma : ℝ) (hsigma : 0 < sigma) :
    ∀ (F : Finset Nat.Primes) (d : ℝ), 0 < d →
      ∃ p, p ∉ F ∧ 4 * primeCoherenceWeight sigma p ^ 2 < d := by
  intro F d hd
  have ht : Tendsto (fun x : ℝ => 4 * (x ^ (-sigma)) ^ 2) atTop (nhds 0) := by
    simpa using (tendsto_rpow_neg_atTop hsigma).pow 2 |>.const_mul 4
  have hev : ∀ᶠ x in atTop, 4 * (x ^ (-sigma)) ^ 2 < d := by
    filter_upwards [ht.eventually (gt_mem_nhds hd)] with x hx
    simpa using hx
  obtain ⟨X, hX⟩ := eventually_atTop.1 hev
  let N := max ((F.sup fun p => (p : ℕ)) + 1) (Nat.ceil X)
  obtain ⟨q, hNq, hqprime⟩ := Nat.exists_infinite_primes N
  let p : Nat.Primes := ⟨q, hqprime⟩
  refine ⟨p, ?_, ?_⟩
  · intro hpF
    have hp_le : (p : ℕ) ≤ F.sup fun z => (z : ℕ) :=
      Finset.le_sup (f := fun z : Nat.Primes => (z : ℕ)) hpF
    have hsup : F.sup (fun z : Nat.Primes => (z : ℕ)) + 1 ≤ N := by
      simp [N]
    have hp_ge : F.sup (fun z : Nat.Primes => (z : ℕ)) + 1 ≤ (p : ℕ) := by
      exact hsup.trans hNq
    omega
  · have hNX : Nat.ceil X ≤ N := by simp [N]
    have hXp : X ≤ ((p : ℕ) : ℝ) := by
      exact (Nat.le_ceil X).trans (by exact_mod_cast hNX.trans hNq)
    exact hX _ hXp

/-- **Prime finite-rank local differential saturation.**  At every positive
horizontal exponent and every positive coherence radius, an arbitrary finite
injective Boolean-sequence family embeds around any base prime orientation.
Every finite translated palette is differentially independent, and all base
and pairwise squared distances are below the requested radius squared. -/
theorem exists_primeCoherenceLocalDifferentialIndependentFamily
    {I A : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (sigma eta : ℝ) (hsigma : 0 < sigma) (heta : 0 < eta)
    (base : Nat.Primes → Bool) (x : I → ℕ → Bool)
    (hx : Function.Injective x) (alpha : A → ℂ)
    (halpha : Function.Injective (fun a => (alpha a).re)) :
    ∃ e : PrefixFunctionCoordinate ↪ Nat.Primes,
      GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
        (fun ia : I × A => signedPrimeShiftCarrier
          (basedSparsePrefixOrientation base e (x ia.1)) (alpha ia.2)) ∧
      (∀ i, weightedOrientationDistanceSq (primeCoherenceWeight sigma)
        (basedSparsePrefixOrientation base e (x i)) base < eta ^ 2) ∧
      ∀ i j, weightedOrientationDistanceSq (primeCoherenceWeight sigma)
        (basedSparsePrefixOrientation base e (x i))
        (basedSparsePrefixOrientation base e (x j)) < eta ^ 2 := by
  have hB : 0 < eta ^ 2 := sq_pos_of_pos heta
  obtain ⟨e, htail, hbase, hpair⟩ :=
    exists_coherenceLocalTailIndependentFamily_of_cofinally_small
      (primeCoherenceWeight sigma) (eta ^ 2) hB
      (primeCoherenceWeight_cofinally_small sigma hsigma) base x hx
  refine ⟨e, ?_, hbase, hpair⟩
  exact (signedPrimeShiftPalette_differentialIndependent_iff
    (fun i => basedSparsePrefixOrientation base e (x i)) alpha halpha).2 htail

end

end GaloisForLFunctions.HTGeometry
