import GaloisForLFunctions.WorldsOfTheZeroConfiguration.InfinitelyManyStrictFakeZerosOnALine
import GaloisForLFunctions.FloorFreeArithmetic.TheFloorOfAMechanism
import GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws.TheAbscissaLawIsNotAsymptotic

/-!
# The floor of prime edits with a count rate

In the floor calculus a mechanism is a property of zero configurations, and its floor is the
least depth beyond which it excludes zeros.  This module puts the structures of a two-sided edit
into that calculus.

`PrimeEditDivisor Z`: the zeros of `Z` right of the critical line are the zeros there of the
continuation of `(s − 1) ζ_B(s)`, where `B` is a two-sided edit of the rational primes — an Euler
product over the rational primes with multiplicities `0, 1, 2` and integer norms — with a count
`A x + O(x^β)`, `β < 1`.

* `primeEditDivisor_zetaZeroConfig`: the zeros of `ζ` have the property (the empty edit).
* `hasModelAt_primeEditDivisor`: the property has a model at every depth `0 < δ < 13/30`: the
  zeros of `ζ` together with a pair `ρ, ρ̄` at depth `δ` where `ζ` does not vanish, and their
  reflections; the edit is the greedy edit at `ρ`.
* `le_floor_primeEditDivisor`: the floor is at least `13/30`.

So a mechanism that uses the Euler product over the rational primes with multiplicities
`0, 1, 2`, integrality of the norms and a power saving in the count excludes no zero of depth
below `13/30`, and proves purity of nothing.
-/

open Complex Filter Topology Set
open Zeta23
open RHTower RHTower.BeurlingDeletion GaloisForLFunctions.RigidArithmeticOfCuts
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration

open PrimeEdits TwoSidedEdits
open GaloisForLFunctions.FloorFreeArithmetic
open GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa

/-- The zeros of the configuration right of the critical line are the zeros there of the
continuation of `(s − 1) ζ_B(s)`, for a two-sided edit `B` of the rational primes with a count
`A x + O(x^β)`, `β < 1`. -/
def PrimeEditDivisor (Z : ZeroConfig) : Prop :=
  ∃ e : ℕ → ℤ, IsEdit e ∧
    (∃ A C β : ℝ, 0 ≤ A ∧ β < 1 ∧
      ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β) ∧
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s) ∧
      ∀ s : ℂ, 1 / 2 < s.re → (G s = 0 ↔ s ∈ Z.carrier)

/-- Right of the line the zeros of `(s − 1) ζ(s)` are the nontrivial zeros of `ζ`. -/
theorem zetaResidueUnit_eq_zero_iff {s : ℂ} (hs : 1 / 2 < s.re) :
    zetaResidueUnit s = 0 ↔ s ∈ zetaZeroConfig.carrier := by
  constructor
  · intro hz
    have h1 : s ≠ 1 := fun h => by
      rw [h, zetaResidueUnit_one] at hz
      exact one_ne_zero hz
    rw [zetaResidueUnit_of_ne h1, mul_eq_zero, or_iff_right (sub_ne_zero.mpr h1)] at hz
    refine ⟨hz, by linarith, ?_⟩
    by_contra hge
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hz
  · intro h
    have h1 : s ≠ 1 := fun h1 => by
      have h2 := h.2.2
      rw [h1, Complex.one_re] at h2
      exact lt_irrefl _ h2
    rw [zetaResidueUnit_of_ne h1, h.1, mul_zero]

/-- **The zeros of `ζ` are a prime edit divisor**: of the empty edit. -/
theorem primeEditDivisor_zetaZeroConfig : PrimeEditDivisor zetaZeroConfig := by
  have he : IsEdit (fun _ : ℕ => (0 : ℤ)) := ⟨fun _ _ => rfl, fun _ => Or.inr (Or.inr rfl)⟩
  have hS : Summable fun k : ℕ => |(((0 : ℤ) : ℝ))| * (k : ℝ) ^ (-(1 / 2 : ℝ)) :=
    summable_zero.congr fun k => by simp
  obtain ⟨A, C, hA, hcount⟩ := editSystem_count (e := fun _ : ℕ => (0 : ℤ)) (β := 1 / 2)
    (by norm_num) (by norm_num) hS
  refine ⟨fun _ => 0, he, ⟨A, C, 1 / 2, hA, by norm_num, hcount⟩, zetaResidueUnit,
    differentiable_zetaResidueUnit.differentiableOn, fun s hs => ?_,
    fun s hs => zetaResidueUnit_eq_zero_iff hs⟩
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
  have hfun : (fun k : ℕ => (((0 : ℤ)) : ℂ)) = 0 := by
    funext k
    simp
  have hL0 : LSeries (fun k : ℕ => (((0 : ℤ)) : ℂ)) s = 0 := by
    rw [hfun]; simp
  have hR0 : editRem (fun _ : ℕ => (0 : ℤ)) s = 0 := by simp [editRem]
  rw [editSystem_zetaSeriesC he hs, hL0, hR0, add_zero, Complex.exp_zero, mul_one,
    zetaResidueUnit_of_ne hs1]

/-- **A model at every depth below `13/30`.**  The zeros of `ζ` together with a pair `ρ, ρ̄` at
depth `δ` and its reflections are the zero configuration of the greedy edit at `ρ`. -/
theorem hasModelAt_primeEditDivisor {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 13 / 30) :
    HasModelAt PrimeEditDivisor δ := by
  classical
  -- a point of depth `δ` at which `ζ` does not vanish
  obtain ⟨t, ht1, -, hζ⟩ := exists_riemannZeta_ne_zero_on_segment (σ := 1 / 2 + δ)
    (by intro h; linarith) (a := 1) (b := 2) (by norm_num)
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℂ, ρ = ⟨1 / 2 + δ, t⟩ := ⟨_, rfl⟩
  have hre : ρ.re = 1 / 2 + δ := by rw [hρdef]
  have him : ρ.im = t := by rw [hρdef]
  rw [← hρdef] at hζ
  have hρ12 : 1 / 2 < ρ.re := by rw [hre]; linarith
  have hρ1 : ρ.re < 14 / 15 := by rw [hre]; linarith
  have hcre : ((starRingEnd ℂ) ρ).re = 1 / 2 + δ := by rw [Complex.conj_re, hre]
  have hcim : ((starRingEnd ℂ) ρ).im = -t := by rw [Complex.conj_im, him]
  have hrr : ∀ z : ℂ, Zeta23.reflect (Zeta23.reflect z) = z := fun z => by
    simp [Zeta23.reflect]
  have hrre : ∀ z : ℂ, (Zeta23.reflect z).re = 1 - z.re := fun z => by
    simp [Zeta23.reflect]
  have hrim : ∀ z : ℂ, (Zeta23.reflect z).im = z.im := fun z => by
    simp [Zeta23.reflect]
  -- neither `ρ`, `ρ̄` nor their reflections are zeros of `ζ`
  have hρZ : ρ ∉ zetaZeroConfig.carrier := fun h => hζ h.1
  have hρZ' : Zeta23.reflect ρ ∉ zetaZeroConfig.carrier := fun h => by
    have h2 := zetaZeroConfig.reflect_mem _ h
    rw [hrr] at h2
    exact hρZ h2
  have hcZ : (starRingEnd ℂ) ρ ∉ zetaZeroConfig.carrier := fun h => by
    have h2 : riemannZeta ((starRingEnd ℂ) ρ) = 0 := h.1
    rw [riemannZeta_conj] at h2
    exact hζ ((map_eq_zero (starRingEnd ℂ)).mp h2)
  have hcZ' : Zeta23.reflect ((starRingEnd ℂ) ρ) ∉
      zetaZeroConfig.carrier := fun h => by
    have h2 := zetaZeroConfig.reflect_mem _ h
    rw [hrr] at h2
    exact hcZ h2
  -- the configuration: the zeros of `ζ`, the pair and its reflections
  have h1mem : (starRingEnd ℂ) ρ ∉
      (addPair zetaZeroConfig ρ (by linarith) (by linarith) hρZ hρZ').carrier := by
    rintro (h | h | h)
    · exact hcZ h
    · have h' := congrArg Complex.im (show (starRingEnd ℂ) ρ = ρ from h)
      rw [hcim, him] at h'
      linarith
    · have h' := congrArg Complex.re (show (starRingEnd ℂ) ρ = Zeta23.reflect ρ from h)
      rw [hcre, hrre, hre] at h'
      linarith
  have h2mem : Zeta23.reflect ((starRingEnd ℂ) ρ) ∉
      (addPair zetaZeroConfig ρ (by linarith) (by linarith) hρZ hρZ').carrier := by
    rintro (h | h | h)
    · exact hcZ' h
    · have h' := congrArg Complex.re
        (show Zeta23.reflect ((starRingEnd ℂ) ρ) = ρ from h)
      rw [hrre, hcre, hre] at h'
      linarith
    · have h' := congrArg Complex.im
        (show Zeta23.reflect ((starRingEnd ℂ) ρ) = Zeta23.reflect ρ from h)
      rw [hrim, hrim, hcim, him] at h'
      linarith
  -- the greedy edit at `ρ`
  obtain ⟨C, H, hC, hdiff, hfac⟩ := (isPairTwin_editSystem hρ12 hρ1).exists_continuation
  obtain ⟨A, Cc, hA, hcount⟩ := editSystem_count (e := edit ρ) (β := (ρ.re + 1) / 2)
    (by linarith) (by linarith)
    (summable_abs_edit_rpow (by linarith) (by linarith) (by linarith))
  refine ⟨addPair (addPair zetaZeroConfig ρ (by linarith) (by linarith) hρZ hρZ')
    ((starRingEnd ℂ) ρ) (by rw [hcre]; linarith) (by rw [hcre]; linarith) h1mem h2mem,
    ⟨edit ρ, isEdit_edit ρ, ⟨A, Cc, (ρ.re + 1) / 2, hA, by linarith, hcount⟩, _, hdiff,
      fun s hs => (hfac s hs).symm, fun s hs => ?_⟩,
    ρ, Or.inl (Or.inr (Set.mem_insert _ _)), hre⟩
  -- the zeros of the continuation right of the line
  have hG0 :
      zetaResidueUnit s * (C * (s - ρ) * (s - (starRingEnd ℂ) ρ) * Complex.exp (H s)) = 0 ↔
        (s ∈ zetaZeroConfig.carrier ∨ s = ρ ∨ s = (starRingEnd ℂ) ρ) := by
    rw [mul_eq_zero, zetaResidueUnit_eq_zero_iff hs, mul_eq_zero, mul_eq_zero, mul_eq_zero]
    constructor
    · rintro (h | ((h | h) | h) | h)
      · exact Or.inl h
      · exact absurd h hC
      · exact Or.inr (Or.inl (sub_eq_zero.mp h))
      · exact Or.inr (Or.inr (sub_eq_zero.mp h))
      · exact absurd h (Complex.exp_ne_zero _)
    · rintro (h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl (Or.inl (Or.inr (sub_eq_zero.mpr h))))
      · exact Or.inr (Or.inl (Or.inr (sub_eq_zero.mpr h)))
  refine hG0.trans ?_
  show _ ↔ s ∈ (zetaZeroConfig.carrier ∪ {ρ, Zeta23.reflect ρ}) ∪
    {(starRingEnd ℂ) ρ, Zeta23.reflect ((starRingEnd ℂ) ρ)}
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
  · rintro ((h | h | h) | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exfalso
      have h' := congrArg Complex.re h
      rw [hrre, hre] at h'
      linarith
    · exact Or.inr (Or.inr h)
    · exfalso
      have h' := congrArg Complex.re h
      rw [hrre, hcre] at h'
      linarith

/-- **The floor of prime edits with a count rate is at least `13/30`.** -/
theorem le_floor_primeEditDivisor : 13 / 30 ≤ FloorFreeArithmetic.floor PrimeEditDivisor := by
  by_contra h
  have h' : FloorFreeArithmetic.floor PrimeEditDivisor < 13 / 30 := not_le.mp h
  have hnn := floor_nonneg PrimeEditDivisor
  have hmodel := hasModelAt_primeEditDivisor
    (δ := (FloorFreeArithmetic.floor PrimeEditDivisor + 13 / 30) / 2) (by linarith) (by linarith)
  have hle := le_floor_of_hasModelAt hmodel
  linarith

end GaloisForLFunctions.WorldsOfTheZeroConfiguration
