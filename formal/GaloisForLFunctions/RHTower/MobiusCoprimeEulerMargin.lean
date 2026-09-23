import GaloisForLFunctions.RHTower.Sieve.StartShift

/-!
# The coprime Euler margin

The shared-prime sectors of a balanced squarefree pair have total density `D² · A` with

`A = ∑_p (p+1)^{-2}`,

so the coprime pairs survive with density `D²(1/2 - A)`.  That margin is positive, and the proof is
purely structural: the prime `2` contributes `1/9`, and for odd primes the values `p+1` are
*distinct even integers at least four*, so they inject into `{2, 3, 4, …}` after halving.  Hence

`A ≤ 1/9 + (1/4) ∑_{k ≥ 2} k^{-2} ≤ 1/9 + 1/4 = 13/36 < 1/2`,

with the inner sum bounded by the telescoping inverse-square tail.  No numerical evaluation of `A`
or of `ζ(2)` is used — only that `∑_{k ≥ 2} k^{-2} ≤ 1`.
-/

namespace RHTower

open Finset

/-- A finite set of integers at least two has inverse-square sum at most one. -/
theorem sum_inv_sq_ge_two_le_one (U : Finset ℕ) (hU : ∀ k ∈ U, 2 ≤ k) :
    ∑ k ∈ U, (1 : ℝ) / (k : ℝ) ^ (2 : ℕ) ≤ 1 := by
  classical
  set N : ℕ := U.sup id with hN
  have hsub : U ⊆ Finset.Icc 2 N := by
    intro k hk
    exact Finset.mem_Icc.2 ⟨hU k hk, Finset.le_sup (f := id) hk⟩
  have hmono : ∑ k ∈ U, (1 : ℝ) / (k : ℝ) ^ (2 : ℕ) ≤ ∑ k ∈ Finset.Icc 2 N, (1 : ℝ) / (k : ℝ) ^ (2 : ℕ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
  refine le_trans hmono ?_
  have hIcc : Finset.Icc 2 N = Finset.Ico 2 (N + 1) := by
    ext x
    simp
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  have hidx : N + 1 - 2 = N - 1 := by omega
  rw [hidx]
  have hcong : ∀ i ∈ Finset.range (N - 1),
      (1 : ℝ) / ((2 + i : ℕ) : ℝ) ^ (2 : ℕ) = (1 : ℝ) / ((i : ℝ) + 1 + 1) ^ (2 : ℕ) := by
    intro i _
    congr 2
    push_cast
    ring
  rw [Finset.sum_congr rfl hcong]
  have hbase := Sieve.sum_range_inv_sq_shift_le 1 (N - 1) (le_refl 1)
  push_cast at hbase
  have hinv : (0 : ℝ) < 1 / (((N - 1 : ℕ) : ℝ) + 1) := by positivity
  linarith

/-- The shared-prime weight of the coprimality sieve. -/
noncomputable def primeSuccInvSq (p : ℕ) : ℝ := if p.Prime then (1 : ℝ) / ((p : ℝ) + 1) ^ (2 : ℕ) else 0

theorem primeSuccInvSq_nonneg (p : ℕ) : 0 ≤ primeSuccInvSq p := by
  unfold primeSuccInvSq
  split
  · positivity
  · exact le_refl 0

/-- **The Euler margin, finite form.**  Every partial sum of the shared-prime weights is at most
`13/36`. -/
theorem sum_primeSuccInvSq_le (S : Finset ℕ) : ∑ p ∈ S, primeSuccInvSq p ≤ 13 / 36 := by
  classical
  set T : Finset ℕ := {p ∈ S | p.Prime} with hT
  have hfilter : ∑ p ∈ S, primeSuccInvSq p = ∑ p ∈ T, (1 : ℝ) / ((p : ℝ) + 1) ^ (2 : ℕ) := by
    rw [hT, Finset.sum_filter]
    exact Finset.sum_congr rfl fun p _ => rfl
  rw [hfilter]
  set Todd : Finset ℕ := {p ∈ T | p ≠ 2} with hTodd
  have hsplit : ∑ p ∈ T, (1 : ℝ) / ((p : ℝ) + 1) ^ (2 : ℕ)
      = ∑ p ∈ {p ∈ T | p = 2}, (1 : ℝ) / ((p : ℝ) + 1) ^ (2 : ℕ)
        + ∑ p ∈ Todd, (1 : ℝ) / ((p : ℝ) + 1) ^ (2 : ℕ) := by
    rw [hTodd]
    exact (Finset.sum_filter_add_sum_filter_not T (fun p => p = 2) _).symm
  have htwo : ∑ p ∈ {p ∈ T | p = 2}, (1 : ℝ) / ((p : ℝ) + 1) ^ (2 : ℕ) ≤ 1 / 9 := by
    have hsub : {p ∈ T | p = 2} ⊆ ({2} : Finset ℕ) := by
      intro p hp
      exact Finset.mem_singleton.2 (Finset.mem_filter.1 hp).2
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)) ?_
    rw [Finset.sum_singleton]
    norm_num
  have hoddprime : ∀ p ∈ Todd, p % 2 = 1 := by
    intro p hp
    obtain ⟨hpT, hp2⟩ := Finset.mem_filter.1 hp
    have hprime : p.Prime := (Finset.mem_filter.1 hpT).2
    rcases hprime.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have hinj : ∀ p ∈ Todd, ∀ q ∈ Todd, (p + 1) / 2 = (q + 1) / 2 → p = q := by
    intro p hp q hq hpq
    have h1 := hoddprime p hp
    have h2 := hoddprime q hq
    omega
  have hval : ∀ p ∈ Todd,
      (1 : ℝ) / ((p : ℝ) + 1) ^ (2 : ℕ) = (1 / 4) * ((1 : ℝ) / (((p + 1) / 2 : ℕ) : ℝ) ^ (2 : ℕ)) := by
    intro p hp
    have hmod := hoddprime p hp
    have hcast : ((p : ℝ) + 1) = 2 * ((((p + 1) / 2 : ℕ)) : ℝ) := by
      have hnat : p + 1 = 2 * ((p + 1) / 2) := by omega
      have := congrArg (fun k : ℕ => (k : ℝ)) hnat
      push_cast at this
      linarith
    rw [hcast]
    have hk : ((((p + 1) / 2 : ℕ)) : ℝ) ≠ 0 := by
      have : 0 < (p + 1) / 2 := by omega
      positivity
    field_simp
    ring
  have hodd : ∑ p ∈ Todd, (1 : ℝ) / ((p : ℝ) + 1) ^ (2 : ℕ) ≤ 1 / 4 := by
    rw [Finset.sum_congr rfl hval, ← Finset.mul_sum]
    set V : Finset ℕ := Todd.image (fun p => (p + 1) / 2) with hV
    have himg : ∑ k ∈ V, (1 : ℝ) / (k : ℝ) ^ (2 : ℕ)
        = ∑ p ∈ Todd, (1 : ℝ) / (((p + 1) / 2 : ℕ) : ℝ) ^ (2 : ℕ) := by
      rw [hV]
      exact Finset.sum_image hinj
    rw [← himg]
    have hge : ∀ k ∈ V, 2 ≤ k := by
      rw [hV]
      intro k hk
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hk
      obtain ⟨hpT, hp2⟩ := Finset.mem_filter.1 hp
      have hprime : p.Prime := (Finset.mem_filter.1 hpT).2
      have := hprime.two_le
      omega
    have := sum_inv_sq_ge_two_le_one _ hge
    linarith
  rw [hsplit]
  linarith

/-- The shared-prime weights are summable. -/
theorem summable_primeSuccInvSq : Summable primeSuccInvSq := by
  refine Summable.of_nonneg_of_le primeSuccInvSq_nonneg (fun p => ?_)
    (Sieve.summable_inv_sq_shift 0)
  unfold primeSuccInvSq
  have hcast : ((p : ℝ) + ((0 : ℕ) : ℝ) + 1) = (p : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  split
  · exact le_refl _
  · positivity

/-- `A = ∑_p (p+1)^{-2}`, the total shared-prime density. -/
noncomputable def coprimeSharedPrimeDensity : ℝ := ∑' p : ℕ, primeSuccInvSq p

/-- **The Euler margin is positive.**  `A ≤ 13/36 < 1/2`, with no numerical estimation. -/
theorem coprimeSharedPrimeDensity_le : coprimeSharedPrimeDensity ≤ 13 / 36 :=
  summable_primeSuccInvSq.tsum_le_of_sum_le sum_primeSuccInvSq_le

theorem coprimeSharedPrimeDensity_lt_half : coprimeSharedPrimeDensity < 1 / 2 := by
  have := coprimeSharedPrimeDensity_le
  linarith

/-- **Card equation (13).**  The surviving coprime margin is strictly positive. -/
theorem coprimeMargin_pos : 0 < 1 / 2 - coprimeSharedPrimeDensity := by
  have := coprimeSharedPrimeDensity_lt_half
  linarith

/-- **Card equation (8).**  Excluding one prime rescales the squarefree Euler density by
`p/(p+1)`. -/
theorem euler_exclusion_factor {p : ℝ} (hp : 2 ≤ p) :
    (1 - 1 / p) / (1 - 1 / p ^ (2 : ℕ)) = p / (p + 1) := by
  have hp0 : p ≠ 0 := by intro h; rw [h] at hp; linarith
  have hp1 : p + 1 ≠ 0 := by intro h; linarith
  have hpm1 : p - 1 ≠ 0 := by intro h; linarith
  have hden : 1 - 1 / p ^ (2 : ℕ) = (p - 1) * (p + 1) / p ^ (2 : ℕ) := by
    field_simp
    ring
  rw [hden]
  field_simp

/-- **Card equation (9).**  The shared-prime sector density in the original normalisation. -/
theorem sharedPrimeSector_density {D p : ℝ} (hp : 2 ≤ p) :
    (1 / p ^ (2 : ℕ)) * (D * (p / (p + 1))) ^ (2 : ℕ) * ((p + 1) / p) ^ (2 : ℕ) * p ^ (2 : ℕ)
      = D ^ (2 : ℕ) := by
  have hp0 : p ≠ 0 := by intro h; rw [h] at hp; linarith
  have hp1 : p + 1 ≠ 0 := by intro h; linarith
  field_simp

end RHTower
