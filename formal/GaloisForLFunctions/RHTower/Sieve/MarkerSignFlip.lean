import GaloisForLFunctions.RHTower.Sieve.ShortWindowMatching

/-!
# The marker flips the sign

A marker is a prime larger than every cofactor of its cell, so it never divides the cofactor and the
Möbius function is multiplicative across the product:

`μ(a·p) = μ(a)·μ(p) = −μ(a)`.

Every target of a marker block therefore carries the sign of its cofactor, reversed.  This is the
step that turns a count of block targets into a count of integers of prescribed Möbius sign; what it
leaves open is the distribution of `μ` over the cofactors themselves.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- **A marker reverses the Möbius sign of its cofactor.** -/
theorem moebius_marker_mul {a p : ℕ} (hp : p.Prime) (ha : 0 < a) (hap : a < p) :
    moebius (a * p) = -moebius a := by
  have hdvd : ¬ p ∣ a := Nat.not_dvd_of_pos_of_lt ha hap
  have hcop : Nat.Coprime a p := (Nat.Prime.coprime_iff_not_dvd hp).2 hdvd |>.symm
  rw [isMultiplicative_moebius.map_mul_of_coprime hcop, moebius_apply_prime hp]
  ring

/-- **Every target of a marker block carries the reversed sign of its cofactor.** -/
theorem moebius_of_mem_markerBlockTargets {P : Finset ℕ} {C : ℕ → Finset ℕ}
    (hprime : ∀ p ∈ P, p.Prime)
    (hpos : ∀ p ∈ P, ∀ a ∈ C p, 0 < a)
    (hsmall : ∀ p ∈ P, ∀ a ∈ C p, ∀ r ∈ P, a < r)
    {n : ℕ} (hn : n ∈ RHTower.markerBlockTargets P C) :
    ∃ p ∈ P, ∃ a ∈ C p, n = a * p ∧ moebius n = -moebius a := by
  classical
  rw [RHTower.markerBlockTargets, Finset.mem_image] at hn
  obtain ⟨x, hx, rfl⟩ := hn
  rw [Finset.mem_sigma] at hx
  obtain ⟨hp, ha⟩ := hx
  refine ⟨x.1, hp, x.2, ha, rfl, ?_⟩
  exact moebius_marker_mul (hprime x.1 hp) (hpos x.1 hp x.2 ha) (hsmall x.1 hp x.2 ha x.1 hp)

/-- The block of the sign-restricted cells is the sign-restricted block. -/
theorem markerBlockTargets_filter_moebius {P : Finset ℕ} {C : ℕ → Finset ℕ} {ε : ℤ}
    (hprime : ∀ p ∈ P, p.Prime)
    (hpos : ∀ p ∈ P, ∀ a ∈ C p, 0 < a)
    (hsmall : ∀ p ∈ P, ∀ a ∈ C p, ∀ r ∈ P, a < r) :
    RHTower.markerBlockTargets P (fun p => (C p).filter (fun a => moebius a = -ε))
      = {n ∈ RHTower.markerBlockTargets P C | moebius n = ε} := by
  classical
  ext n
  simp only [RHTower.markerBlockTargets, Finset.mem_image, Finset.mem_sigma, Finset.mem_filter]
  constructor
  · rintro ⟨x, ⟨hp, ha⟩, rfl⟩
    refine ⟨⟨x, ⟨hp, ha.1⟩, rfl⟩, ?_⟩
    rw [moebius_marker_mul (hprime x.1 hp) (hpos x.1 hp x.2 ha.1)
      (hsmall x.1 hp x.2 ha.1 x.1 hp), ha.2]
    ring
  · rintro ⟨⟨x, ⟨hp, ha⟩, rfl⟩, hsign⟩
    refine ⟨x, ⟨hp, ?_⟩, rfl⟩
    refine ⟨ha, ?_⟩
    have hflip := moebius_marker_mul (hprime x.1 hp) (hpos x.1 hp x.2 ha)
      (hsmall x.1 hp x.2 ha x.1 hp)
    rw [hflip] at hsign
    omega

/-- **The sign-count of a block is the sign-count of its cofactors.**  Every difficulty about the
Möbius function of the targets is a difficulty about the cofactors. -/
theorem card_markerBlockTargets_moebius {P : Finset ℕ} {C : ℕ → Finset ℕ} {ε : ℤ}
    (hprime : ∀ p ∈ P, p.Prime)
    (hpos : ∀ p ∈ P, ∀ a ∈ C p, 0 < a)
    (hsmall : ∀ p ∈ P, ∀ a ∈ C p, ∀ r ∈ P, a < r) :
    ({n ∈ RHTower.markerBlockTargets P C | moebius n = ε}).card
      = ∑ p ∈ P, ((C p).filter (fun a => moebius a = -ε)).card := by
  classical
  rw [← markerBlockTargets_filter_moebius hprime hpos hsmall]
  refine RHTower.card_markerBlockTargets P _ hprime ?_ ?_
  · intro p hp a ha
    rw [Finset.mem_filter] at ha
    exact hpos p hp a ha.1
  · intro p hp a ha r hr
    rw [Finset.mem_filter] at ha
    exact hsmall p hp a ha.1 r hr

end RHTower.Sieve
