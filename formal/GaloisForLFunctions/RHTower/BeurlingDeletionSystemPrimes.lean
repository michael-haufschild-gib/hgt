import GaloisForLFunctions.RHTower.BeurlingDeletionSystemCount
import GaloisForLFunctions.RHTower.VonKochChebyshevBound

/-!
# The Chebyshev function of the deletion system

For a Beurling system, `ψ_B(X) = Σ_{N(p)^k ≤ X, k ≥ 1} log N(p) = Σ_p ⌊log X/log N(p)⌋ log N(p)`
(`BeurlingSystem.chebyshevPsi`).  For the deletion system `(ℙ ∖ S) ∪ ℙ^{1/β}`

`ψ_B(X) = ψ(X) − ψ_S(X) + β^{−1} ψ(X^β)`,   `ψ_S(X) = Σ_{p ≤ X, p ∈ S} ⌊log X/log p⌋ log p`

(`chebyshevPsi_deletionSystem`), and `log 2 · π_S(X) ≤ ψ_S(X) ≤ π_S(X) log X`
(`primePowerSum_bounds`).
-/

open Finset Real

noncomputable section

namespace RHTower

namespace BeurlingSystem

/-- The Chebyshev function of a Beurling system,
`ψ_B(X) = Σ_{N(p)^k ≤ X, k ≥ 1} log N(p) = Σ_p ⌊log X / log N(p)⌋ log N(p)`. -/
def chebyshevPsi (B : BeurlingSystem) (X : ℝ) : ℝ :=
  ∑' p : B.Label, (⌊Real.log X / Real.log (B.labelNorm p)⌋₊ : ℝ) * Real.log (B.labelNorm p)

end BeurlingSystem

namespace BeurlingDeletion

/-- `#{k ≥ 1 : p^k ≤ Y} = ⌊log Y / log p⌋`. -/
theorem nat_log_floor_eq {p : ℕ} (hp : 2 ≤ p) {Y : ℝ} (hY : 1 ≤ Y) :
    Nat.log p ⌊Y⌋₊ = ⌊Real.log Y / Real.log p⌋₊ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  have hY0 : ⌊Y⌋₊ ≠ 0 := by
    have := Nat.le_floor (n := 1) (by exact_mod_cast hY); omega
  have key : ∀ k : ℕ, k ≤ Nat.log p ⌊Y⌋₊ ↔ k ≤ ⌊Real.log Y / Real.log p⌋₊ := by
    intro k
    rw [Nat.le_floor_iff (div_nonneg (Real.log_nonneg hY) hlogp.le), le_div_iff₀ hlogp,
      Nat.le_log_iff_pow_le (by omega) hY0, Nat.le_floor_iff (by linarith),
      ← Real.log_le_log_iff (by positivity) (by linarith), Nat.cast_pow, Real.log_pow]
  exact le_antisymm ((key _).mp le_rfl) ((key _).mpr le_rfl)

/-- `ψ(Y) = Σ_{p ≤ Y} ⌊log Y/log p⌋ log p`. -/
theorem psi_eq_sum_floor {Y : ℝ} (hY : 1 ≤ Y) :
    Chebyshev.psi Y = ∑ p ∈ Nat.primesLE ⌊Y⌋₊,
      (⌊Real.log Y / Real.log p⌋₊ : ℝ) * Real.log p := by
  rw [Chebyshev.psi_eq_psi_coe_floor, Chebyshev.psi_eq_sum_mul_log_prime]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [nat_log_floor_eq (Nat.two_le_of_mem_primesLE hp) hY]

/-- The prime-power sum over the deleted primes, `ψ_S(X) = Σ_{p ≤ X, p ∈ S} ⌊log X/log p⌋ log p`. -/
def primePowerSum (S : Set ℕ) (X : ℝ) : ℝ := by
  classical
  exact ∑ p ∈ (Nat.primesLE ⌊X⌋₊).filter (· ∈ S), (⌊Real.log X / Real.log p⌋₊ : ℝ) * Real.log p

/-- The number of deleted primes up to `X`. -/
def deletedCount (S : Set ℕ) (X : ℝ) : ℝ := by
  classical
  exact (((Nat.primesLE ⌊X⌋₊).filter (· ∈ S)).card : ℝ)

theorem floor_log_div_eq_zero {p : ℕ} (hp : 2 ≤ p) {X : ℝ} (hX : 1 ≤ X) (hpX : X < p) :
    ⌊Real.log X / Real.log p⌋₊ = 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  rw [Nat.floor_eq_zero, div_lt_one hlogp]
  exact Real.log_lt_log (by linarith) hpX

/-- **The Chebyshev function of the deletion system.** -/
theorem chebyshevPsi_deletionSystem (S : Set ℕ) {β : ℝ} (hβ : 0 < β) {X : ℝ} (hX : 1 ≤ X) :
    (deletionSystem S β hβ).chebyshevPsi X =
      Chebyshev.psi X - primePowerSum S X + β⁻¹ * Chebyshev.psi (X ^ β) := by
  classical
  have hX0 : 0 < X := by linarith
  have hXβ : 1 ≤ X ^ β := Real.one_le_rpow hX hβ.le
  set f : KeptPrime S ⊕ Nat.Primes → ℝ := fun p =>
    (⌊Real.log X / Real.log ((deletionSystem S β hβ).labelNorm p)⌋₊ : ℝ) *
      Real.log ((deletionSystem S β hβ).labelNorm p) with hf
  set gA : ℕ → ℝ := fun n => (⌊Real.log X / Real.log (n : ℝ)⌋₊ : ℝ) * Real.log (n : ℝ) with hgA
  set gB : ℕ → ℝ := fun n => (⌊Real.log (X ^ β) / Real.log (n : ℝ)⌋₊ : ℝ) * Real.log (n : ℝ)
    with hgB
  have hfA : ∀ p : KeptPrime S, f (Sum.inl p) = gA p.1 := fun p => rfl
  have hlogq : ∀ q : Nat.Primes, Real.log (((q : ℕ) : ℝ) ^ (1 / β)) = β⁻¹ * Real.log (q : ℕ) := by
    intro q; rw [Real.log_rpow (by exact_mod_cast q.2.pos), one_div]
  have hfB : ∀ q : Nat.Primes, f (Sum.inr q) = β⁻¹ * gB (q : ℕ) := by
    intro q
    show (⌊Real.log X / Real.log (((q : ℕ) : ℝ) ^ (1 / β))⌋₊ : ℝ) *
      Real.log (((q : ℕ) : ℝ) ^ (1 / β)) = _
    rw [hlogq]
    show _ = β⁻¹ * ((⌊Real.log (X ^ β) / Real.log ((q : ℕ) : ℝ)⌋₊ : ℝ) * Real.log ((q : ℕ) : ℝ))
    rw [Real.log_rpow hX0]
    have : Real.log X / (β⁻¹ * Real.log (q : ℕ)) = β * Real.log X / Real.log (q : ℕ) := by
      field_simp
    rw [this]; ring
  -- the finite supports
  set tA : Finset ℕ := (Nat.primesLE ⌊X⌋₊).filter (· ∉ S) with htA
  set tB : Finset ℕ := Nat.primesLE ⌊X ^ β⌋₊ with htB
  set sA : Finset (KeptPrime S) := tA.preimage (fun p : KeptPrime S => p.1)
    (Subtype.val_injective.injOn) with hsA
  set sB : Finset Nat.Primes := tB.preimage (fun q : Nat.Primes => (q : ℕ))
    (Subtype.val_injective.injOn) with hsB
  have hA0 : ∀ p ∉ sA, f (Sum.inl p) = 0 := by
    intro p hp
    have hpX : X < p.1 := by
      by_contra h
      push Not at h
      apply hp
      rw [hsA, Finset.mem_preimage, htA, Finset.mem_filter, Nat.mem_primesLE]
      exact ⟨⟨Nat.le_floor h, p.2.1⟩, p.2.2⟩
    rw [hfA, hgA]
    simp only
    rw [floor_log_div_eq_zero p.2.1.two_le hX hpX]; simp
  have hB0 : ∀ q ∉ sB, f (Sum.inr q) = 0 := by
    intro q hq
    have hqX : X ^ β < (q : ℕ) := by
      by_contra h
      push Not at h
      apply hq
      rw [hsB, Finset.mem_preimage, htB, Nat.mem_primesLE]
      exact ⟨Nat.le_floor h, q.2⟩
    rw [hfB, hgB]
    simp only
    rw [floor_log_div_eq_zero q.2.two_le hXβ hqX]; simp
  have hsumA : Summable (f ∘ Sum.inl) := summable_of_ne_finset_zero (s := sA) hA0
  have hsumB : Summable (f ∘ Sum.inr) := summable_of_ne_finset_zero (s := sB) hB0
  unfold BeurlingSystem.chebyshevPsi
  change ∑' p, f p = _
  rw [Summable.tsum_sum hsumA hsumB, tsum_eq_sum (s := sA) hA0, tsum_eq_sum (s := sB) hB0]
  simp_rw [hfA, hfB]
  rw [← Finset.mul_sum]
  have hpartA : ∑ p ∈ sA, gA p.1 = ∑ n ∈ tA, gA n :=
    Finset.sum_preimage (fun p : KeptPrime S => p.1) tA _ gA fun n hn hnr => by
      exfalso; apply hnr
      have hn' := Finset.mem_filter.mp hn
      exact ⟨⟨n, Nat.prime_of_mem_primesLE hn'.1, hn'.2⟩, rfl⟩
  have hpartB : ∑ q ∈ sB, gB (q : ℕ) = ∑ n ∈ tB, gB n :=
    Finset.sum_preimage (fun q : Nat.Primes => (q : ℕ)) tB _ gB fun n hn hnr => by
      exfalso; apply hnr
      exact ⟨⟨n, Nat.prime_of_mem_primesLE hn⟩, rfl⟩
  rw [hpartA, hpartB, htB, ← psi_eq_sum_floor hXβ, htA, psi_eq_sum_floor hX, primePowerSum,
    ← Finset.sum_filter_add_sum_filter_not (Nat.primesLE ⌊X⌋₊) (· ∈ S)]
  ring

/-- `log 2 · π_S(X) ≤ ψ_S(X) ≤ π_S(X) log X`. -/
theorem primePowerSum_bounds (S : Set ℕ) {X : ℝ} (hX : 1 ≤ X) :
    Real.log 2 * deletedCount S X ≤ primePowerSum S X ∧
      primePowerSum S X ≤ deletedCount S X * Real.log X := by
  classical
  unfold primePowerSum deletedCount
  constructor
  · rw [show Real.log 2 * (((Nat.primesLE ⌊X⌋₊).filter (· ∈ S)).card : ℝ) =
        ∑ _p ∈ (Nat.primesLE ⌊X⌋₊).filter (· ∈ S), Real.log 2 by
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm]]
    refine Finset.sum_le_sum fun p hp => ?_
    have hp' := (Finset.mem_filter.mp hp).1
    have hp2 : 2 ≤ p := Nat.two_le_of_mem_primesLE hp'
    have hpX : (p : ℝ) ≤ X := by
      have := (Nat.mem_primesLE.mp hp').1
      exact (Nat.le_floor_iff (by linarith)).mp this
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp2
    have hlogp : 0 < Real.log p := Real.log_pos hp1
    have hfl : 1 ≤ ⌊Real.log X / Real.log p⌋₊ := by
      rw [Nat.one_le_floor_iff, one_le_div hlogp]
      exact Real.log_le_log (by linarith) hpX
    have hl2 : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) (by exact_mod_cast hp2)
    calc Real.log 2 ≤ 1 * Real.log p := by linarith
      _ ≤ (⌊Real.log X / Real.log p⌋₊ : ℝ) * Real.log p := by
          gcongr; exact_mod_cast hfl
  · rw [show (((Nat.primesLE ⌊X⌋₊).filter (· ∈ S)).card : ℝ) * Real.log X =
        ∑ _p ∈ (Nat.primesLE ⌊X⌋₊).filter (· ∈ S), Real.log X by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun p hp => ?_
    have hp' := (Finset.mem_filter.mp hp).1
    have hp2 : 2 ≤ p := Nat.two_le_of_mem_primesLE hp'
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp2
    have hlogp : 0 < Real.log p := Real.log_pos hp1
    calc (⌊Real.log X / Real.log p⌋₊ : ℝ) * Real.log p ≤ (Real.log X / Real.log p) * Real.log p := by
          gcongr; exact Nat.floor_le (div_nonneg (Real.log_nonneg hX) hlogp.le)
      _ = Real.log X := by field_simp

end BeurlingDeletion

end RHTower
