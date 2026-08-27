import GaloisForLFunctions.RHTower.XiPhysicalPrimeEndpointActiveApertureWidthEnergy
import GaloisForLFunctions.RHTower.CreaseBudgetPrimeMass

/-!
# Mertens control of active physical endpoint energy

Activity forces every selected prime below `exp k`.  Elementary Mertens first upper bound then
removes packet-dependent endpoint weight from the physical ultraviolet estimate, leaving the
explicit moving-scale factor `N (k-m) (k+log 4)^2`.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- A nonempty active physical packet has total endpoint weight at most `k + log 4`. -/
theorem xiPhysicalPrimeLogEndpointTotalWeight_le_k_add_log_four_of_active
    (P : Finset Nat.Primes) {A m k : ℝ} (hP : P.Nonempty)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p) :
    xiPhysicalPrimeLogEndpointTotalWeight P ≤ k + Real.log 4 := by
  let n : ℕ := ⌊Real.exp k⌋₊
  let Q : Finset ℕ := P.image Subtype.val
  have hlog (p : Nat.Primes) (hp : p ∈ P) : Real.log (p : ℝ) < k := by
    have hlen := hactive p hp
    have hstart := xiPhysicalPrimeLogApertureStart_nonneg m p
    have hdiff : xiPhysicalPrimeLogApertureStart m p <
        xiPhysicalPrimeLogApertureEnd A k p := by
      have : 0 < xiPhysicalPrimeLogApertureEnd A k p -
          xiPhysicalPrimeLogApertureStart m p := by
        simpa [xiPhysicalPrimeLogApertureLength] using hlen
      linarith
    have hendpos : 0 < xiPhysicalPrimeLogApertureEnd A k p :=
      lt_of_le_of_lt hstart hdiff
    have hendle : xiPhysicalPrimeLogApertureEnd A k p ≤ k - Real.log (p : ℝ) :=
      min_le_right _ _
    linarith
  have hp_le_n (p : Nat.Primes) (hp : p ∈ P) : (p : ℕ) ≤ n := by
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
    have hpExp : (p : ℝ) < Real.exp k := by
      rw [← Real.exp_log hp0]
      exact Real.exp_lt_exp.mpr (hlog p hp)
    exact Nat.le_floor hpExp.le
  have hQsub : Q ⊆ Nat.primesBelow (n + 1) := by
    intro q hq
    change q ∈ P.image Subtype.val at hq
    rw [Finset.mem_image] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    have hple := hp_le_n p hp
    exact Nat.mem_primesBelow.mpr ⟨by omega, p.prop⟩
  have hn : 1 ≤ n := by
    obtain ⟨p, hp⟩ := hP
    have hp2 := p.prop.two_le
    have hple := hp_le_n p hp
    omega
  have hsumEq : xiPhysicalPrimeLogEndpointTotalWeight P =
      ∑ q ∈ Q, Real.log q / (q : ℝ) := by
    rw [xiPhysicalPrimeLogEndpointTotalWeight]
    calc
      ∑ p ∈ P, physicalPrimeEndpointWeight p =
          ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [physicalPrimeEndpointWeight]
      _ = ∑ q ∈ Q, Real.log q / (q : ℝ) := by
        change (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) =
          ∑ q ∈ P.image Subtype.val, Real.log q / (q : ℝ)
        exact (Finset.sum_image (f := fun q : ℕ => Real.log q / (q : ℝ))
          Subtype.val_injective.injOn).symm
  have hnonneg : ∀ q ∈ Nat.primesBelow (n + 1), q ∉ Q →
      0 ≤ Real.log q / (q : ℝ) := by
    intro q hq hqQ
    have hprime := (Nat.mem_primesBelow.mp hq).2
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)) (by positivity)
  have hsubsum : (∑ q ∈ Q, Real.log q / (q : ℝ)) ≤
      ∑ q ∈ Nat.primesBelow (n + 1), Real.log q / (q : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hQsub hnonneg
  have hmert := mertens_first_upper hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hnExp : (n : ℝ) ≤ Real.exp k := Nat.floor_le (Real.exp_pos k).le
  have hlogn : Real.log (n : ℝ) ≤ k := by
    calc
      Real.log (n : ℝ) ≤ Real.log (Real.exp k) := Real.log_le_log hnR hnExp
      _ = k := Real.log_exp k
  rw [hsumEq]
  linarith

/-- Fully explicit active-packet raw ultraviolet bound.  Finite-set weight has disappeared; only
aperture location `k`, width `k-m`, and frequency cutoff `N` remain. -/
theorem natCast_mul_tsum_normSq_xiPhysicalPrimeLogCharacterAmplitude_le_mertensApertureWidth
    (P : Finset Nat.Primes) {A m k : ℝ} (hA : 0 < A) (hmk : m ≤ k)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p)
    (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) * ∑' r : ℕ,
        Complex.normSq (xiPhysicalPrimeLogCharacterAmplitude P A
          ((N + 1 + r : ℕ) : ℤ) m k) ≤
      (2 * A / Real.pi) * (N : ℝ) * (k - m) * (k + Real.log 4) ^ 2 := by
  by_cases hPempty : P = ∅
  · subst P
    simp [xiPhysicalPrimeLogCharacterAmplitude]
    positivity
  have hP : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr hPempty
  have hW := xiPhysicalPrimeLogEndpointTotalWeight_le_k_add_log_four_of_active
    P hP hactive
  have hW0 := xiPhysicalPrimeLogEndpointTotalWeight_nonneg P
  have hklog4 : 0 ≤ k + Real.log 4 := hW0.trans hW
  have hsq : xiPhysicalPrimeLogEndpointTotalWeight P ^ 2 ≤ (k + Real.log 4) ^ 2 :=
    (sq_le_sq₀ hW0 hklog4).2 hW
  have hwidth : 0 ≤ k - m := sub_nonneg.mpr hmk
  have hsource :=
    natCast_mul_tsum_normSq_xiPhysicalPrimeLogCharacterAmplitude_le_apertureWidth
      P hA hactive N hN
  calc
    _ ≤ (2 * A / Real.pi) * (N : ℝ) * (k - m) *
        xiPhysicalPrimeLogEndpointTotalWeight P ^ 2 := hsource
    _ ≤ (2 * A / Real.pi) * (N : ℝ) * (k - m) * (k + Real.log 4) ^ 2 := by
      gcongr

end

end RHTower
