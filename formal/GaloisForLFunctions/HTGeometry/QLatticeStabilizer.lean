import GaloisForLFunctions.HTGeometry.SimplePoleUnit
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The additive lattice behind a multiplicative `q`-orbit

For `q = exp(2πiτ)` with `τ` off the real axis, the multiplier is not a root of unity and the
preimage of the orbit `q^ℤ` under `h ↦ exp(2πih)` is exactly the rank-two lattice `ℤ + τℤ`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

noncomputable section

/-- The multiplier attached to a period. -/
def periodMultiplier (τ : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * τ)

theorem periodMultiplier_ne_zero (τ : ℂ) : periodMultiplier τ ≠ 0 :=
  Complex.exp_ne_zero _

theorem periodMultiplier_zpow (τ : ℂ) (n : ℤ) :
    (periodMultiplier τ) ^ n = Complex.exp (2 * Real.pi * Complex.I * (n * τ)) := by
  rw [periodMultiplier, ← Complex.exp_int_mul]
  congr 1
  ring

/-- **A period off the real axis gives a non-torsion multiplier.** -/
theorem periodMultiplier_zpow_ne_one {τ : ℂ} (hτ : τ.im ≠ 0) {n : ℤ} (hn : n ≠ 0) :
    (periodMultiplier τ) ^ n ≠ 1 := by
  intro hcon
  rw [periodMultiplier_zpow, Complex.exp_eq_one_iff] at hcon
  obtain ⟨k, hk⟩ := hcon
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hnτ : (n : ℂ) * τ = (k : ℂ) := by
    field_simp at hk
    exact hk
  have him : ((n : ℂ) * τ).im = 0 := by
    rw [hnτ]
    simp
  rw [Complex.mul_im] at him
  simp only [Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero] at him
  rcases mul_eq_zero.1 him with h | h
  · exact hn (by exact_mod_cast h)
  · exact hτ h

/-- **The additive lattice of a multiplicative orbit.**  The preimage of `q^ℤ` under
`h ↦ exp(2πih)` is the rank-two lattice `ℤ + τℤ`. -/
theorem exp_mem_zpow_iff_lattice {τ : ℂ} (h : ℂ) :
    (∃ n : ℤ, Complex.exp (2 * Real.pi * Complex.I * h) = (periodMultiplier τ) ^ n)
      ↔ ∃ m k : ℤ, h = (m : ℂ) * τ + (k : ℂ) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : (2 : ℂ) * Real.pi * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
  constructor
  · rintro ⟨n, hn⟩
    rw [periodMultiplier_zpow, Complex.exp_eq_exp_iff_exists_int] at hn
    obtain ⟨k, hk⟩ := hn
    refine ⟨n, k, ?_⟩
    have hmul : (2 * Real.pi * Complex.I) * h
        = (2 * Real.pi * Complex.I) * ((n : ℂ) * τ + (k : ℂ)) := by
      rw [hk]
      ring
    exact mul_left_cancel₀ h2 hmul
  · rintro ⟨m, k, rfl⟩
    refine ⟨m, ?_⟩
    rw [periodMultiplier_zpow, Complex.exp_eq_exp_iff_exists_int]
    exact ⟨k, by ring⟩


theorem mem_orbitUnion_one_iff {q : ℂ} (hq : q ≠ 0) (γ : ℂ) :
    γ ∈ orbitUnion q ({1} : Finset ℂ) ↔ γ ≠ 0 ∧ ∃ n : ℤ, γ = q ^ n := by
  constructor
  · rintro ⟨hγ, n, hn⟩
    refine ⟨hγ, -n, ?_⟩
    rw [Finset.mem_singleton] at hn
    rw [zpow_neg]
    have hqn : q ^ n ≠ 0 := zpow_ne_zero n hq
    field_simp
    exact hn
  · rintro ⟨hγ, n, rfl⟩
    refine ⟨hγ, -n, ?_⟩
    rw [Finset.mem_singleton, ← zpow_add₀ hq]
    simp
  
theorem orbitUnion_one_div_closed {q : ℂ} (hq : q ≠ 0) :
    ∀ x ∈ orbitUnion q ({1} : Finset ℂ), ∀ y ∈ orbitUnion q ({1} : Finset ℂ),
      x / y ∈ orbitUnion q ({1} : Finset ℂ) := by
  intro x hx y hy
  obtain ⟨hx0, n, rfl⟩ := (mem_orbitUnion_one_iff hq x).1 hx
  obtain ⟨hy0, m, rfl⟩ := (mem_orbitUnion_one_iff hq y).1 hy
  refine (mem_orbitUnion_one_iff hq _).2 ⟨div_ne_zero hx0 hy0, n - m, ?_⟩
  rw [zpow_sub₀ hq]

/-- **Every rank-two lattice is an exact summability stabilizer.**  For the one-point residue class
`r = x/(x−1)` the scaling stabilizer is exactly the multiplicative orbit `q^ℤ`, whose additive
pullback under `h ↦ exp(2πih)` is the lattice `ℤ + τℤ`. -/
theorem qSummable_simplePoleUnit_one_iff_lattice {τ : ℂ} (hτ : τ.im ≠ 0) (h : ℂ) :
    QSummable (periodMultiplier τ) (periodMultiplier_ne_zero τ)
        (ratFuncScale (Complex.exp (2 * Real.pi * Complex.I * h)) (Complex.exp_ne_zero _)
            (simplePoleSum ({1} : Finset ℂ)) - simplePoleSum ({1} : Finset ℂ))
      ↔ ∃ m k : ℤ, h = (m : ℂ) * τ + (k : ℂ) := by
  set q : ℂ := periodMultiplier τ with hqdef
  have hq : q ≠ 0 := periodMultiplier_ne_zero τ
  have hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1 := fun n hn => periodMultiplier_zpow_ne_one hτ hn
  have hS0 : ∀ α ∈ ({1} : Finset ℂ), α ≠ 0 := by
    intro α hα
    rw [Finset.mem_singleton] at hα
    rw [hα]
    exact one_ne_zero
  have hSorb : ∀ α ∈ ({1} : Finset ℂ), ∀ β ∈ ({1} : Finset ℂ), ∀ n : ℤ, α = β * q ^ n → n = 0 := by
    intro α hα β hβ n hn
    rw [Finset.mem_singleton] at hα hβ
    rw [hα, hβ, one_mul] at hn
    by_contra hcon
    exact hqtor n hcon hn.symm
  rw [qSummable_ratFuncScale_simplePoleSum_sub_iff hq hqtor hS0 hSorb ⟨1, Finset.mem_singleton_self 1⟩
    (orbitUnion_one_div_closed hq) (Complex.exp_ne_zero _)]
  rw [mem_orbitUnion_one_iff hq]
  constructor
  · rintro ⟨-, n, hn⟩
    exact (exp_mem_zpow_iff_lattice h).1 ⟨n, hn⟩
  · intro hlat
    obtain ⟨n, hn⟩ := (exp_mem_zpow_iff_lattice h).2 hlat
    exact ⟨Complex.exp_ne_zero _, n, hn⟩

end

end GaloisForLFunctions.HTGeometry
