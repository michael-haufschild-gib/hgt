import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Compact-support stabilization of the prime-power orbit sum

The orbit side of Deninger's finite-stage Lefschetz identities is
`Σ_{p ∈ P_a} Σ_{k ≥ 1} (log p) · c_{p,k} · φ(k log p)`.  For a test function `φ` supported in
`(-∞, B]`, a nonzero summand forces `p^k ≤ e^B`, and by unique factorization only finitely
many prime powers satisfy that bound.  Hence the stage sums are **eventually constant** along
any directed exhaustion of the primes: infinite-dimensional `H¹` creates no orbit-side
convergence problem on compact test support.

* `primePow_injOn` — `(p, k) ↦ p^(k+1)` is injective (unique factorization);
* `primePowBall_finite` — only finitely many prime powers lie below any bound;
* `orbitTerm_eq_zero_of_notMem_ball` — outside the ball the orbit term vanishes;
* `orbitSum_stabilizes` — **any two stages containing the ball have equal orbit sums**: the
  compact-support stabilization half of the card's trace-limit theorem, unconditional.

No trace-norm, spectral, or zeta input occurs; this is the arithmetic half of the limit
theorem, leaving all analytic work in the trace-norm convergence hypothesis where the card
places it.
-/

namespace GaloisForLFunctions

noncomputable section

open Real

/-- The prime-power ball: pairs `(p, k)` with `p^(k+1)` below the bound. -/
def primePowBall (N : ℝ) : Set (Nat.Primes × ℕ) :=
  {q | (((q.1 : ℕ) : ℝ)) ^ (q.2 + 1) ≤ N}

/-- Unique factorization: `(p, k) ↦ p^(k+1)` is injective. -/
theorem primePow_injOn :
    Function.Injective (fun q : Nat.Primes × ℕ => ((q.1 : ℕ)) ^ (q.2 + 1)) := by
  rintro ⟨p, k⟩ ⟨p', k'⟩ h
  simp only at h
  have hdvd : (p : ℕ) ∣ ((p' : ℕ)) ^ (k' + 1) := by
    rw [← h]
    exact dvd_pow_self _ (Nat.succ_ne_zero k)
  have hpp' : (p : ℕ) = (p' : ℕ) :=
    (Nat.prime_dvd_prime_iff_eq p.2 p'.2).mp (p.2.dvd_of_dvd_pow hdvd)
  have hk : k + 1 = k' + 1 := by
    apply Nat.pow_right_injective p.2.two_le
    show (p : ℕ) ^ (k + 1) = (p : ℕ) ^ (k' + 1)
    rw [h, hpp']
  ext
  · exact Subtype.ext hpp'
  · omega

/-- Only finitely many prime powers lie below any real bound. -/
theorem primePowBall_finite (N : ℝ) : (primePowBall N).Finite := by
  apply Set.Finite.of_finite_image _ primePow_injOn.injOn
  apply Set.Finite.subset (Set.finite_Iic (Nat.floor N))
  rintro m ⟨⟨p, k⟩, hq, rfl⟩
  simp only [Set.mem_Iic]
  apply Nat.le_floor
  calc ((((p : ℕ)) ^ (k + 1) : ℕ) : ℝ)
      = (((p : ℕ) : ℝ)) ^ (k + 1) := by push_cast; rfl
    _ ≤ N := hq

/-- The orbit term of the finite-stage Lefschetz identity at the prime power `p^(k+1)`. -/
def orbitTerm (φ : ℝ → ℂ) (c : Nat.Primes × ℕ → ℂ) (q : Nat.Primes × ℕ) : ℂ :=
  (Real.log ((q.1 : ℕ)) : ℂ) * c q *
    φ ((((q.2 + 1 : ℕ)) : ℝ) * Real.log ((q.1 : ℕ)))

/-- Outside the prime-power ball of radius `e^B`, a test function supported in `(-∞, B]`
kills the orbit term. -/
theorem orbitTerm_eq_zero_of_notMem_ball {B : ℝ} {φ : ℝ → ℂ}
    (hsupp : ∀ x : ℝ, B < x → φ x = 0) (c : Nat.Primes × ℕ → ℂ)
    {q : Nat.Primes × ℕ} (hq : q ∉ primePowBall (Real.exp B)) :
    orbitTerm φ c q = 0 := by
  obtain ⟨p, k⟩ := q
  rw [primePowBall, Set.mem_setOf_eq, not_le] at hq
  have hp1 : (1 : ℝ) < ((p : ℕ) : ℝ) := by
    exact_mod_cast p.2.one_lt
  have hlog : B < (((k + 1 : ℕ)) : ℝ) * Real.log ((p : ℕ)) := by
    have h1 := Real.log_lt_log (Real.exp_pos B) hq
    rwa [Real.log_exp, Real.log_pow] at h1
  rw [orbitTerm, hsupp _ hlog, mul_zero]

/-- **Compact-support stabilization**: any two stages containing the prime-power ball have
equal orbit sums.  Along a directed exhaustion of the primes the finite-stage orbit sums are
eventually constant, so the finite-stage Lefschetz identities pass to the infinite arithmetic
distributional trace identity with no orbit-side convergence problem. -/
theorem orbitSum_stabilizes {B : ℝ} {φ : ℝ → ℂ}
    (hsupp : ∀ x : ℝ, B < x → φ x = 0) (c : Nat.Primes × ℕ → ℂ)
    {s t : Finset (Nat.Primes × ℕ)}
    (hs : (primePowBall_finite (Real.exp B)).toFinset ⊆ s)
    (ht : (primePowBall_finite (Real.exp B)).toFinset ⊆ t) :
    ∑ q ∈ s, orbitTerm φ c q = ∑ q ∈ t, orbitTerm φ c q := by
  have hvanish : ∀ (u : Finset (Nat.Primes × ℕ)),
      (primePowBall_finite (Real.exp B)).toFinset ⊆ u →
      ∑ q ∈ u, orbitTerm φ c q =
        ∑ q ∈ (primePowBall_finite (Real.exp B)).toFinset,
          orbitTerm φ c q := by
    intro u hu
    rw [Finset.sum_subset hu]
    intro q _ hqnot
    apply orbitTerm_eq_zero_of_notMem_ball hsupp
    rwa [Set.Finite.mem_toFinset] at hqnot
  rw [hvanish s hs, hvanish t ht]

end

end GaloisForLFunctions
