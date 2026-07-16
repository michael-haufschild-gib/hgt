import GaloisForLFunctions.HTGeometry.PolynomialADEPhaseIdentity
import GaloisForLFunctions.HTGeometry.PolynomialPatternWeight
import GaloisForLFunctions.HTGeometry.TorsionFaceExactification

/-!
# Torsion-language-universal Taylor phases

This module gives the phase recurrence used by geometric-magnitude exactification a literal Lean
definition.  It extracts cofinal exact occurrences of every finite torsion word and identifies the
normalized phase of each translated bounded ADE pattern with the corresponding finite character.
-/

namespace GaloisForLFunctions

open Filter Finset PowerSeries Topology

noncomputable section

/-- Every finite word in every positive-order complex torsion alphabet occurs arbitrarily far out
in the phase sequence. -/
def TorsionLanguageUniversal (u : ℕ → ℂ) : Prop :=
  ∀ (m M N : ℕ), 0 < m → ∀ s : Fin M → ℂ,
    (∀ r, s r ^ m = 1) →
      ∃ q, N ≤ q ∧ ∀ r : Fin M, u (q + (r : ℕ)) = s r

/-- Arbitrarily late occurrences of one torsion word contain a strictly increasing cofinal
subsequence of exact occurrences. -/
theorem TorsionLanguageUniversal.exists_strictMono_occurrences
    {u : ℕ → ℂ} (hu : TorsionLanguageUniversal u)
    {m M : ℕ} (hm : 0 < m) (s : Fin M → ℂ)
    (hs : ∀ r, s r ^ m = 1) :
    ∃ q : ℕ → ℕ, StrictMono q ∧ Tendsto q atTop atTop ∧
      ∀ k (r : Fin M), u (q k + (r : ℕ)) = s r := by
  let P : ℕ → Prop := fun q => ∀ r : Fin M, u (q + (r : ℕ)) = s r
  have hP : ∀ N, ∃ q > N, P q := by
    intro N
    obtain ⟨q, hq, hword⟩ := hu m M (N + 1) hm s hs
    exact ⟨q, by omega, hword⟩
  obtain ⟨q, hqmono, hqP⟩ := Nat.exists_strictMono_subsequence hP
  exact ⟨q, hqmono, hqmono.tendsto_atTop, hqP⟩

/-- A translated bounded multiplicity pattern evaluates as its finite phase character. -/
theorem prod_shiftedAtomPatternKey
    {M D : ℕ} (u : ℕ → ℂ) (q K : ℕ)
    (p : Fin M → Fin (D + 1)) :
    (shiftedAtomPatternKey q K p).prod (fun i k => u i ^ k) =
      ∏ r : Fin M, u (windowShift q K (r : ℕ)) ^ (p r : ℕ) := by
  classical
  rw [shiftedAtomPatternKey_eq_sum]
  change (∑ r ∈ (Finset.univ : Finset (Fin M)),
      Finsupp.single (windowShift q K (r : ℕ)) (p r : ℕ)).prod
        (fun i k => u i ^ k) =
    ∏ r ∈ (Finset.univ : Finset (Fin M)),
      u (windowShift q K (r : ℕ)) ^ (p r : ℕ)
  rw [← Finsupp.prod_finsetSum_index]
  · simp
  · intro i
    simp
  · intro i a b
    exact pow_add _ _ _

/-- The product of coefficient-magnitude factors is the exponential of the negative atom
valuation. -/
theorem prod_exp_neg_eq_exp_neg_atomValuation
    (b : ℕ → ℝ) (ν : ℕ →₀ ℕ) :
    ν.prod (fun i k => ((Real.exp (-b i) : ℝ) : ℂ) ^ k) =
      ((Real.exp (-atomValuation b ν) : ℝ) : ℂ) := by
  classical
  change (∏ i ∈ ν.support, ((Real.exp (-b i) : ℝ) : ℂ) ^ ν i) = _
  simp_rw [Complex.ofReal_exp, ← Complex.exp_nat_mul]
  rw [← Complex.exp_sum]
  congr 1
  rw [atomValuation]
  rw [Finsupp.sum]
  push_cast
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- If each Taylor coefficient is its prescribed magnitude times `u i`, the intrinsic normalized
atom phase is exactly the multiplicative phase monomial. -/
theorem normalizedAtomPhase_eq_phaseProd
    (F : PowerSeries ℂ) (b : ℕ → ℝ) (u : ℕ → ℂ)
    (hcoeff : ∀ i, PowerSeries.coeff i F =
      ((Real.exp (-b i) : ℝ) : ℂ) * u i)
    (ν : ℕ →₀ ℕ) :
    normalizedAtomPhase F b ν = ν.prod (fun i k => u i ^ k) := by
  classical
  rw [normalizedAtomPhase]
  simp_rw [hcoeff, mul_pow]
  rw [Finsupp.prod_mul, prod_exp_neg_eq_exp_neg_atomValuation]
  push_cast
  rw [← mul_assoc, ← Complex.exp_add]
  simp

/-- The normalized phase of a shifted bounded ADE atom is its finite torsion character. -/
theorem normalizedAtomPhase_shiftedAtomPatternKey_eq
    (F : PowerSeries ℂ) (b : ℕ → ℝ) (u : ℕ → ℂ)
    (hcoeff : ∀ i, PowerSeries.coeff i F =
      ((Real.exp (-b i) : ℝ) : ℂ) * u i)
    {M D : ℕ} (q K : ℕ) (p : Fin M → Fin (D + 1)) :
    normalizedAtomPhase F b (shiftedAtomPatternKey q K p) =
      ∏ r : Fin M, u (windowShift q K (r : ℕ)) ^ (p r : ℕ) := by
  rw [normalizedAtomPhase_eq_phaseProd F b u hcoeff]
  exact prod_shiftedAtomPatternKey u q K p

end

end GaloisForLFunctions
