import Mathlib

/-!
# Primes obey no eventual affine recurrence

Let `(p n)` be a sequence of primes, eventually strictly increasing, that eventually follows an
affine recurrence `p (n + 1) = a · p n + m` with `a ≥ 1`. Choose a member `ℓ = p M` larger than `a`.
Modulo `ℓ` the recurrence is the map `x ↦ a x + m`, a permutation of `ZMod ℓ` because `a` is a unit.
A permutation of a finite set returns every point, so the residue `p M ≡ 0` recurs: `ℓ` divides a
later, larger member, which is then not prime (`not_eventually_affine_recurrence`).

The same holds when the defect `p (n + 1) − a · p n` is only eventually periodic: along a residue
class of indices the `d`-step recurrence is affine with slope `a ^ d`
(`not_eventually_periodic_defect`).

In a realization of the primes by a dynamical system, `p n = e^{S(u^n v)}` along a cycle family and
the defect is the conformal defect of the family; these theorems exclude conformal defects that
stabilize or cycle.
-/

namespace GaloisForLFunctions.ArithmeticResonanceTheory

/-- A sequence that increases from index `N` on is strictly monotone there. -/
theorem lt_of_increasing_from {p : ℕ → ℕ} {N : ℕ} (hmono : ∀ n, N ≤ n → p n < p (n + 1))
    {i j : ℕ} (hi : N ≤ i) (hij : i < j) : p i < p j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
    · exact (ih h).trans (hmono j (hi.trans h.le))
    · subst h; exact hmono i hi

/-- **Returning residues.** If from index `M` on the residues of `p` modulo `ℓ = p M` follow an
injective self-map of `ZMod ℓ`, then `ℓ` divides `p (M + j)` for some `j ≥ 1`. -/
theorem exists_dvd_of_injective_step {p : ℕ → ℕ} {M : ℕ} [NeZero (p M)]
    (f : ZMod (p M) → ZMod (p M)) (hf : Function.Injective f)
    (hstep : ∀ n, M ≤ n → ((p (n + 1) : ℕ) : ZMod (p M)) = f (p n)) :
    ∃ j, 0 < j ∧ p M ∣ p (M + j) := by
  classical
  -- `f` is a permutation of the finite set `ZMod (p M)`; its order returns every residue
  let σ : Equiv.Perm (ZMod (p M)) := Equiv.ofBijective f hf.bijective_of_finite
  have hiter : ∀ j, ((p (M + j) : ℕ) : ZMod (p M)) = (σ ^ j) (p M) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [← Nat.add_assoc, hstep _ (Nat.le_add_right _ _), ih, pow_succ', Equiv.Perm.mul_apply]
      rfl
  refine ⟨orderOf σ, orderOf_pos σ, ?_⟩
  have h := hiter (orderOf σ)
  rw [pow_orderOf_eq_one, Equiv.Perm.one_apply, ZMod.natCast_self] at h
  exact (ZMod.natCast_eq_zero_iff _ _).mp h

/-- **Primes obey no eventual affine recurrence.** A sequence of primes that increases from some
index on cannot satisfy `p (n + 1) = a · p n + m` for all large `n`, whatever `a ≥ 1` and `m ∈ ℤ`. -/
theorem not_eventually_affine_recurrence {p : ℕ → ℕ} {a : ℕ} (ha : 1 ≤ a) (m : ℤ) {N : ℕ}
    (hprime : ∀ n, N ≤ n → (p n).Prime) (hmono : ∀ n, N ≤ n → p n < p (n + 1))
    (hrec : ∀ n, N ≤ n → (p (n + 1) : ℤ) = a * p n + m) : False := by
  -- a member `ℓ = p M` larger than `a`
  set M := N + a + 1 with hM
  have hgrow : ∀ j, p N + j ≤ p (N + j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have := hmono (N + j) (Nat.le_add_right _ _)
      rw [show N + (j + 1) = N + j + 1 by omega]; omega
  have haM : a < p M := by have := hgrow (a + 1); rw [hM, Nat.add_assoc]; omega
  have hℓ : (p M).Prime := hprime M (by omega)
  haveI : Fact (p M).Prime := ⟨hℓ⟩
  -- `a` is a unit modulo `ℓ`, so `x ↦ a x + m` is injective
  have ha0 : ((a : ℕ) : ZMod (p M)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun hdvd => absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)
  let f : ZMod (p M) → ZMod (p M) := fun x => (a : ZMod (p M)) * x + (m : ZMod (p M))
  have hf : Function.Injective f := fun x y hxy => by
    have h : (a : ZMod (p M)) * x = (a : ZMod (p M)) * y := by simpa [f] using hxy
    exact mul_left_cancel₀ ha0 h
  have hstep : ∀ n, M ≤ n → ((p (n + 1) : ℕ) : ZMod (p M)) = f (p n) := by
    intro n hn
    have h := congrArg (fun z : ℤ => (z : ZMod (p M))) (hrec n (by omega))
    simpa [f] using h
  obtain ⟨j, hj, hdvd⟩ := exists_dvd_of_injective_step f hf hstep
  -- the later member `p (M + j)` is a prime with a proper prime divisor
  have hlt : p M < p (M + j) := lt_of_increasing_from hmono (by omega) (by omega)
  rcases (Nat.dvd_prime (hprime (M + j) (by omega))).mp hdvd with h1 | h1
  · exact hℓ.one_lt.ne' h1
  · exact hlt.ne h1

/-- Along an eventually periodic defect, `d` steps of the recurrence are affine with slope `a ^ d`
and an intercept independent of the starting block. -/
theorem exists_block_intercept {p : ℕ → ℕ} {a : ℕ} (m : ℕ → ℤ) {d N : ℕ}
    (hrec : ∀ n, N ≤ n → (p (n + 1) : ℤ) = a * p n + m n)
    (hper : ∀ n, N ≤ n → m (n + d) = m n) (e : ℕ) :
    ∃ c : ℤ, ∀ j, (p (N + j * d + e) : ℤ) = (a : ℤ) ^ e * p (N + j * d) + c := by
  -- the defect at `N + j d + e` is the defect at `N + e`
  have hshift : ∀ j e, m (N + j * d + e) = m (N + e) := by
    intro j e
    induction j with
    | zero => simp
    | succ j ih =>
      have h := hper (N + j * d + e) (by omega)
      rw [show N + j * d + e + d = N + (j + 1) * d + e by ring] at h
      rw [h, ih]
  induction e with
  | zero => exact ⟨0, fun j => by simp⟩
  | succ e ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨a * c + m (N + e), fun j => ?_⟩
    rw [← Nat.add_assoc, hrec _ (by omega), hc j, hshift j e]
    ring

/-- **Primes admit no eventually periodic conformal defect.** If `p (n + 1) − a · p n` is
eventually periodic, the primes `p n` cannot increase from some index on. -/
theorem not_eventually_periodic_defect {p : ℕ → ℕ} {a : ℕ} (ha : 1 ≤ a) (m : ℕ → ℤ) {d N : ℕ}
    (hd : 0 < d) (hprime : ∀ n, N ≤ n → (p n).Prime) (hmono : ∀ n, N ≤ n → p n < p (n + 1))
    (hrec : ∀ n, N ≤ n → (p (n + 1) : ℤ) = a * p n + m n)
    (hper : ∀ n, N ≤ n → m (n + d) = m n) : False := by
  obtain ⟨c, hc⟩ := exists_block_intercept m hrec hper d
  -- the block sequence `q j = p (N + j d)` follows an affine recurrence with slope `a ^ d`
  set q : ℕ → ℕ := fun j => p (N + j * d) with hq
  have hqrec : ∀ j, 0 ≤ j → (q (j + 1) : ℤ) = ((a ^ d : ℕ) : ℤ) * q j + c := by
    intro j _
    have h := hc j
    rw [show N + j * d + d = N + (j + 1) * d by ring] at h
    simpa [hq] using h
  refine not_eventually_affine_recurrence (p := q) (Nat.one_le_pow _ _ ha) c (N := 0)
    (fun j _ => hprime _ (Nat.le_add_right _ _)) (fun j _ => ?_) hqrec
  exact lt_of_increasing_from hmono (Nat.le_add_right _ _) (by nlinarith)

end GaloisForLFunctions.ArithmeticResonanceTheory
