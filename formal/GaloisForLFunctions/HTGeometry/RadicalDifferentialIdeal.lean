import GaloisForLFunctions.HTGeometry.DeltaStructureLinearOde
import Mathlib.RingTheory.Ideal.Operations

/-!
# Radical differential ideals

Two foundational facts of differential algebra, neither of which mathlib has.

The first is Ritt's lemma: in a radical differential ideal, `a b ∈ I` already forces `a δb ∈ I`.
Squaring turns the Leibniz expansion of `δ(ab)` into a membership statement, and radicality removes
the square.

The second is that over a `ℚ`-algebra the radical of a differential ideal is again differential: if
`x ^ (m+1) ∈ I` then `(δx) ^ (2m+1) ∈ I`, by a descent that trades one power of `x` for two powers
of `δx` at each step.  This is the characteristic-zero case of Keigher's condition, and it is what
makes the Kolchin topology behave.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem deriv_pow' {R : Type*} [CommRing R] [Differential R] (x : R) (n : ℕ) :
    Differential.deriv (x ^ n) = (n : R) * x ^ (n - 1) * Differential.deriv x := by
  simp [nsmul_eq_mul, smul_eq_mul, mul_assoc]

theorem isUnit_natCast_of_ratAlgebra {R : Type*} [CommRing R] [Algebra ℚ R] {n : ℕ}
    (hn : n ≠ 0) : IsUnit ((n : R)) := by
  have h : ((n : R)) = algebraMap ℚ R (n : ℚ) := by push_cast; ring
  rw [h]
  exact (isUnit_iff_ne_zero.mpr (by exact_mod_cast hn)).map (algebraMap ℚ R)

theorem mem_of_natCast_mul_mem {R : Type*} [CommRing R] [Algebra ℚ R] {I : Ideal R} {n : ℕ}
    (hn : n ≠ 0) {u : R} (h : (n : R) * u ∈ I) : u ∈ I := by
  obtain ⟨v, hv⟩ : ∃ v : R, (n : R) * v = 1 := by
    refine ⟨algebraMap ℚ R ((n : ℚ))⁻¹, ?_⟩
    rw [show ((n : R)) = algebraMap ℚ R (n : ℚ) by push_cast; ring, ← map_mul,
      mul_inv_cancel₀ (by exact_mod_cast hn : (n : ℚ) ≠ 0), map_one]
  have hu : u = v * ((n : R) * u) := by rw [← mul_assoc, mul_comm v, hv, one_mul]
  rw [hu]
  exact I.mul_mem_left _ h

/-- **Ritt's lemma.**  In a radical differential ideal, a product membership forces the membership
of the product with the derivative of either factor. -/
theorem mul_deriv_mem_of_mul_mem {R : Type*} [CommRing R] [Differential R]
    {I : Ideal R} (hrad : I.IsRadical) (hδ : ∀ x ∈ I, Differential.deriv x ∈ I)
    {a b : R} (hab : a * b ∈ I) : a * Differential.deriv b ∈ I := by
  have h1 : a * Differential.deriv b + b * Differential.deriv a ∈ I := by
    have := hδ _ hab
    rwa [deriv_mul'] at this
  have h2 : a * (a * Differential.deriv b + b * Differential.deriv a) ∈ I := I.mul_mem_left _ h1
  have h3 : a * b * Differential.deriv a ∈ I := I.mul_mem_right _ hab
  have h4 : a * a * Differential.deriv b ∈ I := by
    have hrw : a * a * Differential.deriv b
        = a * (a * Differential.deriv b + b * Differential.deriv a)
          - a * b * Differential.deriv a := by ring
    rw [hrw]
    exact I.sub_mem h2 h3
  refine hrad ⟨2, ?_⟩
  have hrw : (a * Differential.deriv b) ^ 2
      = (a * a * Differential.deriv b) * Differential.deriv b := by ring
  rw [hrw]
  exact I.mul_mem_right _ h4

/-- One descent step: a power of `x` is traded for two powers of `δx`. -/
theorem pow_deriv_descent {R : Type*} [CommRing R] [Differential R] [Algebra ℚ R]
    {I : Ideal R} (hδ : ∀ y ∈ I, Differential.deriv y ∈ I) {x : R} (a j : ℕ)
    (h : x ^ (a + 1) * Differential.deriv x ^ (2 * j + 1) ∈ I) :
    x ^ a * Differential.deriv x ^ (2 * j + 3) ∈ I := by
  set d := Differential.deriv x with hd
  have hderiv : Differential.deriv (x ^ (a + 1) * d ^ (2 * j + 1))
      = ((a : R) + 1) * x ^ a * d ^ (2 * j + 2)
        + ((2 * j : R) + 1) * x ^ (a + 1) * d ^ (2 * j) * Differential.deriv d := by
    rw [deriv_mul', deriv_pow', deriv_pow', ← hd]
    have h0 : a + 1 - 1 = a := by omega
    have h1 : 2 * j + 1 - 1 = 2 * j := by omega
    rw [h0, h1]
    push_cast
    have h2 : d ^ (2 * j + 2) = d ^ (2 * j + 1) * d := by ring
    rw [h2]
    ring
  have hd1 : Differential.deriv (x ^ (a + 1) * d ^ (2 * j + 1)) ∈ I := hδ _ h
  have hmul : d * Differential.deriv (x ^ (a + 1) * d ^ (2 * j + 1)) ∈ I := I.mul_mem_left _ hd1
  have hterm : ((2 * j : R) + 1) * Differential.deriv d * (x ^ (a + 1) * d ^ (2 * j + 1)) ∈ I :=
    I.mul_mem_left _ h
  have hkey : ((a : R) + 1) * (x ^ a * d ^ (2 * j + 3)) ∈ I := by
    have hrw : ((a : R) + 1) * (x ^ a * d ^ (2 * j + 3))
        = d * Differential.deriv (x ^ (a + 1) * d ^ (2 * j + 1))
          - ((2 * j : R) + 1) * Differential.deriv d * (x ^ (a + 1) * d ^ (2 * j + 1)) := by
      rw [hderiv]
      have h3 : d ^ (2 * j + 3) = d * d ^ (2 * j + 2) := by ring
      have h4 : d ^ (2 * j + 1) = d ^ (2 * j) * d := by ring
      rw [h3, h4]
      ring
    rw [hrw]
    exact I.sub_mem hmul hterm
  refine mem_of_natCast_mul_mem (n := a + 1) (by omega) ?_
  push_cast
  exact hkey

/-- The descent, iterated: all powers of `x` are traded away. -/
theorem pow_deriv_descent_chain {R : Type*} [CommRing R] [Differential R] [Algebra ℚ R]
    {I : Ideal R} (hδ : ∀ y ∈ I, Differential.deriv y ∈ I) {x : R} :
    ∀ a j : ℕ, x ^ a * Differential.deriv x ^ (2 * j + 1) ∈ I →
      Differential.deriv x ^ (2 * (j + a) + 1) ∈ I := by
  intro a
  induction a with
  | zero => intro j h; simpa using h
  | succ a ih =>
      intro j h
      have hstep := pow_deriv_descent hδ a j h
      have : x ^ a * Differential.deriv x ^ (2 * (j + 1) + 1) ∈ I := by
        have hrw : 2 * (j + 1) + 1 = 2 * j + 3 := by omega
        rw [hrw]
        exact hstep
      have := ih (j + 1) this
      have hrw2 : j + 1 + a = j + (a + 1) := by omega
      rwa [hrw2] at this

/-- **The radical of a differential ideal over a `ℚ`-algebra is differential.** -/
theorem deriv_mem_radical {R : Type*} [CommRing R] [Differential R] [Algebra ℚ R]
    {I : Ideal R} (hδ : ∀ y ∈ I, Differential.deriv y ∈ I)
    {x : R} (hx : x ∈ I.radical) : Differential.deriv x ∈ I.radical := by
  obtain ⟨n, hn⟩ := hx
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · refine ⟨1, ?_⟩
    have htop : I = ⊤ := Ideal.eq_top_iff_one I |>.mpr (by simpa using hn)
    rw [htop]
    trivial
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hbase : x ^ m * Differential.deriv x ^ (2 * 0 + 1) ∈ I := by
      have h1 : Differential.deriv (x ^ (m + 1)) ∈ I := hδ _ hn
      rw [deriv_pow'] at h1
      simp only [Nat.add_sub_cancel] at h1
      refine mem_of_natCast_mul_mem (n := m + 1) (by omega) ?_
      push_cast
      simpa [mul_assoc] using h1
    have := pow_deriv_descent_chain hδ m 0 hbase
    exact ⟨2 * (0 + m) + 1, this⟩

end

end GaloisForLFunctions.HTGeometry
