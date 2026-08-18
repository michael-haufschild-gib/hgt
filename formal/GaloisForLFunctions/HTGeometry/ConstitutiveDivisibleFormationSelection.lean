import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Group.Pi.Basic

/-!
# Divisible formation selection

Formation roots turn composition depth into divisibility of an integer-valued charge.  Roots at
unbounded depths annihilate every finite charge.  Applied to pointwise meromorphic order, the same
mechanism kills the complete divisor without assuming RH or any route-specific endpoint theorem.
-/

open Complex Filter

namespace GaloisForLFunctions.HTGeometry

/-- An integer divisible by natural numbers of unbounded size is zero. -/
theorem int_eq_zero_of_unbounded_natCast_dvd (q : ℤ)
    (h : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ (n : ℤ) ∣ q) : q = 0 := by
  by_contra hq
  obtain ⟨n, hn, hdvd⟩ := h (q.natAbs + 1)
  have hle : n ≤ q.natAbs := by
    have habs := Int.natAbs_le_of_dvd_ne_zero hdvd hq
    simpa using habs
  omega

/-- Universal formation-root selection law.  If an integer-valued charge is additive under powers,
then roots of one carrier at unbounded formation depths force its charge to vanish. -/
theorem charge_eq_zero_of_unbounded_formationRoots
    {M : Type*} [Monoid M] (charge : M → ℤ)
    (hpow : ∀ (x : M) (n : ℕ), charge (x ^ n) = (n : ℤ) * charge x)
    (R : M)
    (hroot : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ G : M, G ^ n = R) :
    charge R = 0 := by
  apply int_eq_zero_of_unbounded_natCast_dvd
  intro N
  obtain ⟨n, hn, G, hG⟩ := hroot N
  refine ⟨n, hn, ?_⟩
  refine ⟨charge G, ?_⟩
  rw [← hpow, hG]

/-- Pointwise analytic selection law.  Meromorphic roots at unbounded depths force every finite
meromorphic order to vanish. -/
theorem meromorphicOrderAt_eq_zero_of_unbounded_roots
    (R : ℂ → ℂ) (z : ℂ)
    (hfinite : meromorphicOrderAt R z ≠ ⊤)
    (hroot : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ G : ℂ → ℂ, MeromorphicAt G z ∧ G ^ n = R) :
    meromorphicOrderAt R z = 0 := by
  have hRfinite := hfinite
  lift meromorphicOrderAt R z to ℤ using hfinite with q hq
  have hq0 : q = 0 := by
    apply int_eq_zero_of_unbounded_natCast_dvd
    intro N
    obtain ⟨n, hn, G, hGmero, hGpow⟩ := hroot (max N 1)
    have hnN : N ≤ n := le_trans (le_max_left N 1) hn
    have hn0 : n ≠ 0 := by omega
    have horder : meromorphicOrderAt R z = n * meromorphicOrderAt G z := by
      rw [← hGpow]
      exact meromorphicOrderAt_pow hGmero
    have hGfinite : meromorphicOrderAt G z ≠ ⊤ := by
      intro htop
      rw [htop] at horder
      simp [hn0] at horder
      exact hRfinite (hq.trans horder)
    lift meromorphicOrderAt G z to ℤ using hGfinite with p hp
    refine ⟨n, hnN, ⟨p, ?_⟩⟩
    have hcast : (q : WithTop ℤ) = (((n : ℤ) * p : ℤ) : WithTop ℤ) := by
      calc
        (q : WithTop ℤ) = meromorphicOrderAt R z := hq
        _ = (n : WithTop ℤ) * (p : WithTop ℤ) := horder
        _ = (((n : ℤ) * p : ℤ) : WithTop ℤ) := by norm_cast
    exact_mod_cast hcast
  exact_mod_cast hq0

/-- Global divisor annihilation.  A single unbounded root family that is meromorphic everywhere
kills every finite pointwise order of the carrier. -/
theorem meromorphicDivisor_eq_zero_of_unbounded_roots
    (R : ℂ → ℂ) (hfinite : ∀ z, meromorphicOrderAt R z ≠ ⊤)
    (hroot : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ G : ℂ → ℂ, (∀ z, MeromorphicAt G z) ∧ G ^ n = R) :
    ∀ z, meromorphicOrderAt R z = 0 := by
  intro z
  apply meromorphicOrderAt_eq_zero_of_unbounded_roots R z (hfinite z)
  intro N
  obtain ⟨n, hn, G, hG, hpow⟩ := hroot N
  exact ⟨n, hn, G, hG z, hpow⟩

/-- Closed capstone: abstract integer-charge selection and global meromorphic divisor selection are
the same unbounded formation-root mechanism. -/
theorem divisibleFormationSelection_capstone
    {M : Type*} [Monoid M] (charge : M → ℤ)
    (hpow : ∀ (x : M) (n : ℕ), charge (x ^ n) = (n : ℤ) * charge x)
    (R : M) (hroot : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ G : M, G ^ n = R) :
    charge R = 0 :=
  charge_eq_zero_of_unbounded_formationRoots charge hpow R hroot

end GaloisForLFunctions.HTGeometry
