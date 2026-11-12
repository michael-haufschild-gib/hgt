import GaloisForLFunctions.WorldsOfTheZeroConfiguration.InfinitelyManyStrictFakeZerosOnALine
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TwinsContinuePastTheLine
import GaloisForLFunctions.FloorFreeArithmetic.TheFloorOfAMechanism
import GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws.TheAbscissaLawIsNotAsymptotic

/-!
# The floor of prime edits with a count rate

In the floor calculus a mechanism is a property of zero configurations, and its floor is the
least depth beyond which it excludes zeros.  This module puts the structures of a two-sided edit
into that calculus.

`PrimeEditDivisorOn c Z`: the zeros of `Z` in the half-plane `Re s > c` are the zeros there of
the continuation of `(s − 1) ζ_B(s)`, where `B` is a two-sided edit of the rational primes — an
Euler product over the rational primes with multiplicities `0, 1, 2` and integer norms — with a
count `A x + O(x^β)`, `β < 1`.  For `c = 1/2` (`PrimeEditDivisor`) the property reads the zeros
right of the critical line; for `c < 1/2` it reads the strip `c < Re s < 1 − c` too, on which a
zero configuration is symmetric about the line.

* `exists_isEdit_zeros_zeta_and_quartet`: for `δ + 1/15 < c` and `1/4 + δ/2 < c ≤ 1/2` there are
  a point `ρ` of depth `δ` with `ζ(ρ) ≠ 0` and an edit whose continuation to `Re s > c` vanishes
  exactly at the zeros of `ζ` and at the points of the quartet `ρ, ρ̄, 1 − ρ̄, 1 − ρ` in the
  half-plane.  The edit is the greedy edit of the layer `{ρ, 1 − ρ̄}` if `1 − ρ̄` lies in the
  half-plane, and of `{ρ}` otherwise.
* `exists_isEdit_zeros_symmetric_in_a_strip`: if moreover `c < 1/2 − δ` (for instance `c = 1/3`
  and `δ < 1/6`), the zeros of the continuation in the strip `c < Re s < 1 − c` are symmetric
  about the critical line, and `ρ` is one of them.
* `hasModelAt_primeEditDivisorOn`, `le_floor_primeEditDivisorOn`: the property has a model at
  every such depth, so its floor is at least `min(c − 1/15, 2c − 1/2)`: `13/30` for `c = 1/2`
  (`le_floor_primeEditDivisor`) and `1/6` for `c = 1/3` (`le_floor_primeEditDivisorOn_third`).

So a mechanism that uses the Euler product over the rational primes with multiplicities
`0, 1, 2`, integrality of the norms, a power saving in the count and the symmetry of the zeros
in a strip about the line excludes no zero of depth below these bounds.  The symmetry of the
zeros in a strip is not the functional equation.
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

/-- The zeros of the configuration in `Re s > c` are the zeros there of the continuation of
`(s − 1) ζ_B(s)`, for a two-sided edit `B` of the rational primes with a count `A x + O(x^β)`,
`β < 1`. -/
def PrimeEditDivisorOn (c : ℝ) (Z : ZeroConfig) : Prop :=
  ∃ e : ℕ → ℤ, IsEdit e ∧
    (∃ A C β : ℝ, 0 ≤ A ∧ β < 1 ∧
      ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β) ∧
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | c < s.re} ∧
      (∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s) ∧
      ∀ s : ℂ, c < s.re → (G s = 0 ↔ s ∈ Z.carrier)

/-- The property read right of the critical line. -/
abbrev PrimeEditDivisor : ZeroConfig → Prop := PrimeEditDivisorOn (1 / 2)

/-- Right of the imaginary axis the zeros of `(s − 1) ζ(s)` are the nontrivial zeros of `ζ`. -/
theorem zetaResidueUnit_eq_zero_iff {s : ℂ} (hs : 0 < s.re) :
    zetaResidueUnit s = 0 ↔ s ∈ zetaZeroConfig.carrier := by
  constructor
  · intro hz
    have h1 : s ≠ 1 := fun h => by
      rw [h, zetaResidueUnit_one] at hz
      exact one_ne_zero hz
    rw [zetaResidueUnit_of_ne h1, mul_eq_zero, or_iff_right (sub_ne_zero.mpr h1)] at hz
    refine ⟨hz, hs, ?_⟩
    by_contra hge
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hz
  · intro h
    have h1 : s ≠ 1 := fun h1 => by
      have h2 := h.2.2
      rw [h1, Complex.one_re] at h2
      exact lt_irrefl _ h2
    rw [zetaResidueUnit_of_ne h1, h.1, mul_zero]

/-- **The zeros of `ζ` are a prime edit divisor**: of the empty edit. -/
theorem primeEditDivisorOn_zetaZeroConfig {c : ℝ} (hc : 0 ≤ c) :
    PrimeEditDivisorOn c zetaZeroConfig := by
  have he : IsEdit (fun _ : ℕ => (0 : ℤ)) := ⟨fun _ _ => rfl, fun _ => Or.inr (Or.inr rfl)⟩
  have hS : Summable fun k : ℕ => |(((0 : ℤ) : ℝ))| * (k : ℝ) ^ (-(1 / 2 : ℝ)) :=
    summable_zero.congr fun k => by simp
  obtain ⟨A, C, hA, hcount⟩ := editSystem_count (e := fun _ : ℕ => (0 : ℤ)) (β := 1 / 2)
    (by norm_num) (by norm_num) hS
  refine ⟨fun _ => 0, he, ⟨A, C, 1 / 2, hA, by norm_num, hcount⟩, zetaResidueUnit,
    differentiable_zetaResidueUnit.differentiableOn, fun s hs => ?_,
    fun s hs => zetaResidueUnit_eq_zero_iff (lt_of_le_of_lt hc hs)⟩
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
  have hfun : (fun k : ℕ => (((0 : ℤ)) : ℂ)) = 0 := by
    funext k
    simp
  have hL0 : LSeries (fun k : ℕ => (((0 : ℤ)) : ℂ)) s = 0 := by
    rw [hfun]; simp
  have hR0 : editRem (fun _ : ℕ => (0 : ℤ)) s = 0 := by simp [editRem]
  rw [editSystem_zetaSeriesC he hs, hL0, hR0, add_zero, Complex.exp_zero, mul_one,
    zetaResidueUnit_of_ne hs1]

theorem primeEditDivisor_zetaZeroConfig : PrimeEditDivisor zetaZeroConfig :=
  primeEditDivisorOn_zetaZeroConfig (by norm_num)

/-- **The zeros of `ζ` and one more quartet.**  For `δ + 1/15 < c` and `1/4 + δ/2 < c ≤ 1/2`
there are a point `ρ` of depth `δ` at which `ζ` does not vanish and a two-sided edit of the
rational primes with a count rate whose continuation to `Re s > c` vanishes exactly at the
zeros of `ζ` and at the points of the quartet `ρ, ρ̄, 1 − ρ̄, 1 − ρ` in the half-plane. -/
theorem exists_isEdit_zeros_zeta_and_quartet {c δ : ℝ} (hc : c ≤ 1 / 2) (hδ : 0 < δ)
    (h1 : δ + 1 / 15 < c) (h2 : 1 / 4 + δ / 2 < c) :
    ∃ (ρ : ℂ) (e : ℕ → ℤ) (G : ℂ → ℂ), ρ.re = 1 / 2 + δ ∧ 1 ≤ ρ.im ∧ riemannZeta ρ ≠ 0 ∧
      IsEdit e ∧
      (∃ A C β : ℝ, 0 ≤ A ∧ β < 1 ∧
        ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β) ∧
      DifferentiableOn ℂ G {s : ℂ | c < s.re} ∧
      (∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s) ∧
      ∀ s : ℂ, c < s.re → (G s = 0 ↔ (s ∈ zetaZeroConfig.carrier ∨ s = ρ ∨
        s = (starRingEnd ℂ) ρ ∨ s = Zeta23.reflect ρ ∨
        s = Zeta23.reflect ((starRingEnd ℂ) ρ))) := by
  classical
  -- a point of depth `δ` at which `ζ` does not vanish
  obtain ⟨t, ht1, -, hζ⟩ := exists_riemannZeta_ne_zero_on_segment (σ := 1 / 2 + δ)
    (by intro h; linarith) (a := 1) (b := 2) (by norm_num)
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℂ, ρ = ⟨1 / 2 + δ, t⟩ := ⟨_, rfl⟩
  have hre : ρ.re = 1 / 2 + δ := by rw [hρdef]
  have him : ρ.im = t := by rw [hρdef]
  rw [← hρdef] at hζ
  have hcre : ((starRingEnd ℂ) ρ).re = 1 / 2 + δ := by rw [Complex.conj_re, hre]
  have hrre : ∀ z : ℂ, (Zeta23.reflect z).re = 1 - z.re := fun z => by simp [Zeta23.reflect]
  have hrc : ∀ z : ℂ,
      (starRingEnd ℂ) (Zeta23.reflect z) = Zeta23.reflect ((starRingEnd ℂ) z) :=
    fun z => by simp [Zeta23.reflect]
  -- the layer: the pair, and its reflection if it lies in the half-plane
  obtain ⟨J, hJρ, hJsub, hJr⟩ : ∃ J : Finset ℂ, ρ ∈ J ∧
      (∀ j ∈ J, j = ρ ∨ j = Zeta23.reflect ρ) ∧ (Zeta23.reflect ρ ∈ J ∨ 1 / 2 - δ ≤ c) := by
    by_cases hq : c < 1 / 2 - δ
    · exact ⟨{ρ, Zeta23.reflect ρ}, by simp, fun j hj => by simpa using hj, Or.inl (by simp)⟩
    · exact ⟨{ρ}, by simp, fun j hj => Or.inl (by simpa using hj), Or.inr (not_lt.mp hq)⟩
  have hJre : ∀ j ∈ J, j.re ≤ 1 / 2 + δ := fun j hj => by
    rcases hJsub j hj with h | h
    · rw [h, hre]
    · rw [h, hrre, hre]; linarith
  obtain ⟨e, he, ⟨A, Cc, hA, hcount⟩, C, H, hC, hH, hfac⟩ :=
    exists_isEdit_layerTwinOn J (fun z : ℂ => z) (b := 1 / 2 + δ) (c := c)
      (β := (3 / 2 + δ) / 2) (by linarith) (by linarith) hJre (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith)
  refine ⟨ρ, e,
    fun s => zetaResidueUnit s * (C * layerFactor J (fun z : ℂ => z) s * Complex.exp (H s)),
    hre, by rw [him]; exact ht1, hζ, he, ⟨A, Cc, (3 / 2 + δ) / 2, hA, by linarith, hcount⟩,
    differentiable_zetaResidueUnit.differentiableOn.mul
      (((differentiableOn_const C).mul
        (differentiable_layerFactor J _).differentiableOn).mul hH.cexp),
    fun s hs => (hfac s hs).symm, fun s hs => ?_⟩
  have hs0 : 0 < s.re := by linarith
  show zetaResidueUnit s * (C * layerFactor J (fun z : ℂ => z) s * Complex.exp (H s)) = 0 ↔ _
  rw [mul_eq_zero, zetaResidueUnit_eq_zero_iff hs0, mul_eq_zero, mul_eq_zero,
    layerFactor_eq_zero_iff]
  constructor
  · rintro (h | (h | ⟨j, hj, h⟩) | h)
    · exact Or.inl h
    · exact absurd h hC
    · rcases hJsub j hj with hj' | hj'
      · rw [hj'] at h
        rcases h with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
      · rw [hj'] at h
        rcases h with h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (h.trans (hrc ρ)))))
    · exact absurd h (Complex.exp_ne_zero _)
  · rintro (h | h | h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl (Or.inr ⟨ρ, hJρ, Or.inl h⟩))
    · exact Or.inr (Or.inl (Or.inr ⟨ρ, hJρ, Or.inr h⟩))
    · -- the reflection lies in the layer, or left of the half-plane
      rcases hJr with hmem | hle
      · exact Or.inr (Or.inl (Or.inr ⟨_, hmem, Or.inl h⟩))
      · exfalso
        have h' := congrArg Complex.re h
        rw [hrre, hre] at h'
        linarith
    · rcases hJr with hmem | hle
      · exact Or.inr (Or.inl (Or.inr ⟨_, hmem, Or.inr (h.trans (hrc ρ).symm)⟩))
      · exfalso
        have h' := congrArg Complex.re h
        rw [hrre, hcre] at h'
        linarith

/-- **Symmetric zeros in a strip.**  For `δ + 1/15 < c` and `1/4 + δ/2 < c < 1/2 − δ` there
are a point `ρ` of depth `δ` at which `ζ` does not vanish and a two-sided edit of the rational
primes with a count rate whose continuation `G` to `Re s > c` vanishes at `ρ` and has zeros
symmetric about the critical line in the strip `c < Re s < 1 − c`. -/
theorem exists_isEdit_zeros_symmetric_in_a_strip {c δ : ℝ} (hδ : 0 < δ)
    (h1 : δ + 1 / 15 < c) (h2 : 1 / 4 + δ / 2 < c) (h3 : c < 1 / 2 - δ) :
    ∃ (ρ : ℂ) (e : ℕ → ℤ) (G : ℂ → ℂ), ρ.re = 1 / 2 + δ ∧ riemannZeta ρ ≠ 0 ∧ IsEdit e ∧
      (∃ A C β : ℝ, 0 ≤ A ∧ β < 1 ∧
        ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β) ∧
      DifferentiableOn ℂ G {s : ℂ | c < s.re} ∧
      (∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s) ∧ G ρ = 0 ∧
      ∀ s : ℂ, c < s.re → s.re < 1 - c → (G s = 0 ↔ G (1 - (starRingEnd ℂ) s) = 0) := by
  obtain ⟨ρ, e, G, hre, -, hζ, he, hcount, hG, hGeq, hzero⟩ :=
    exists_isEdit_zeros_zeta_and_quartet (by linarith) hδ h1 h2
  have hrr : ∀ z : ℂ, Zeta23.reflect (Zeta23.reflect z) = z := fun z => by
    simp [Zeta23.reflect]
  -- the zeros of `ζ` and the quartet are closed under the reflection
  have key : ∀ z : ℂ, (z ∈ zetaZeroConfig.carrier ∨ z = ρ ∨ z = (starRingEnd ℂ) ρ ∨
      z = Zeta23.reflect ρ ∨ z = Zeta23.reflect ((starRingEnd ℂ) ρ)) →
      (Zeta23.reflect z ∈ zetaZeroConfig.carrier ∨ Zeta23.reflect z = ρ ∨
        Zeta23.reflect z = (starRingEnd ℂ) ρ ∨ Zeta23.reflect z = Zeta23.reflect ρ ∨
        Zeta23.reflect z = Zeta23.reflect ((starRingEnd ℂ) ρ)) := by
    rintro z (h | h | h | h | h)
    · exact Or.inl (zetaZeroConfig.reflect_mem z h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl (congrArg Zeta23.reflect h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (congrArg Zeta23.reflect h))))
    · exact Or.inr (Or.inl ((congrArg Zeta23.reflect h).trans (hrr ρ)))
    · exact Or.inr (Or.inr (Or.inl ((congrArg Zeta23.reflect h).trans (hrr _))))
  refine ⟨ρ, e, G, hre, hζ, he, hcount, hG, hGeq,
    (hzero ρ (by rw [hre]; linarith)).mpr (Or.inr (Or.inl rfl)), fun s hs hs1 => ?_⟩
  have hrs : c < (Zeta23.reflect s).re := by
    have hr : (Zeta23.reflect s).re = 1 - s.re := by simp [Zeta23.reflect]
    rw [hr]; linarith
  show G s = 0 ↔ G (Zeta23.reflect s) = 0
  rw [hzero s hs, hzero _ hrs]
  refine ⟨key s, fun h => ?_⟩
  have h' := key _ h
  rwa [hrr] at h'

/-- **A model at every depth below `min(c − 1/15, 2c − 1/2)`.**  The zeros of `ζ` together with
a pair `ρ, ρ̄` at depth `δ` and its reflections are, in `Re s > c`, the zeros of the greedy edit
of the part of the quartet in the half-plane. -/
theorem hasModelAt_primeEditDivisorOn {c δ : ℝ} (hc : c ≤ 1 / 2) (hδ : 0 < δ)
    (h1 : δ + 1 / 15 < c) (h2 : 1 / 4 + δ / 2 < c) : HasModelAt (PrimeEditDivisorOn c) δ := by
  classical
  obtain ⟨ρ, e, G, hre, him, hζ, he, hcount, hG, hGeq, hzero⟩ :=
    exists_isEdit_zeros_zeta_and_quartet hc hδ h1 h2
  have hρ0 : 0 ≤ ρ.re := by rw [hre]; linarith
  have hρ1 : ρ.re ≤ 1 := by rw [hre]; linarith
  have hcre : ((starRingEnd ℂ) ρ).re = 1 / 2 + δ := by rw [Complex.conj_re, hre]
  have hcim : ((starRingEnd ℂ) ρ).im = -ρ.im := Complex.conj_im ρ
  have hrr : ∀ z : ℂ, Zeta23.reflect (Zeta23.reflect z) = z := fun z => by
    simp [Zeta23.reflect]
  have hrre : ∀ z : ℂ, (Zeta23.reflect z).re = 1 - z.re := fun z => by simp [Zeta23.reflect]
  have hrim : ∀ z : ℂ, (Zeta23.reflect z).im = z.im := fun z => by simp [Zeta23.reflect]
  -- neither `ρ`, `ρ̄` nor their reflections are zeros of `ζ`
  have hρZ : ρ ∉ zetaZeroConfig.carrier := fun h => hζ h.1
  have hρZ' : Zeta23.reflect ρ ∉ zetaZeroConfig.carrier := fun h => by
    have h2 := zetaZeroConfig.reflect_mem _ h
    rw [hrr] at h2
    exact hρZ h2
  have hcZ : (starRingEnd ℂ) ρ ∉ zetaZeroConfig.carrier := fun h => by
    have h2 : riemannZeta ((starRingEnd ℂ) ρ) = 0 := h.1
    rw [_root_.riemannZeta_conj] at h2
    exact hζ ((map_eq_zero (starRingEnd ℂ)).mp h2)
  have hcZ' : Zeta23.reflect ((starRingEnd ℂ) ρ) ∉ zetaZeroConfig.carrier := fun h => by
    have h2 := zetaZeroConfig.reflect_mem _ h
    rw [hrr] at h2
    exact hcZ h2
  -- the configuration: the zeros of `ζ`, the pair and its reflections
  have h1mem : (starRingEnd ℂ) ρ ∉ (addPair zetaZeroConfig ρ hρ0 hρ1 hρZ hρZ').carrier := by
    rintro (h | h | h)
    · exact hcZ h
    · have h' := congrArg Complex.im (show (starRingEnd ℂ) ρ = ρ from h)
      rw [hcim] at h'
      linarith
    · have h' := congrArg Complex.re (show (starRingEnd ℂ) ρ = Zeta23.reflect ρ from h)
      rw [hcre, hrre, hre] at h'
      linarith
  have h2mem : Zeta23.reflect ((starRingEnd ℂ) ρ) ∉
      (addPair zetaZeroConfig ρ hρ0 hρ1 hρZ hρZ').carrier := by
    rintro (h | h | h)
    · exact hcZ' h
    · have h' := congrArg Complex.re
        (show Zeta23.reflect ((starRingEnd ℂ) ρ) = ρ from h)
      rw [hrre, hcre, hre] at h'
      linarith
    · have h' := congrArg Complex.im
        (show Zeta23.reflect ((starRingEnd ℂ) ρ) = Zeta23.reflect ρ from h)
      rw [hrim, hrim, hcim] at h'
      linarith
  refine ⟨addPair (addPair zetaZeroConfig ρ hρ0 hρ1 hρZ hρZ') ((starRingEnd ℂ) ρ)
      (by rw [hcre]; linarith) (by rw [hcre]; linarith) h1mem h2mem,
    ⟨e, he, hcount, G, hG, hGeq, fun s hs => (hzero s hs).trans ?_⟩,
    ρ, Or.inl (Or.inr (Set.mem_insert _ _)), hre⟩
  show _ ↔ s ∈ (zetaZeroConfig.carrier ∪ {ρ, Zeta23.reflect ρ}) ∪
    {(starRingEnd ℂ) ρ, Zeta23.reflect ((starRingEnd ℂ) ρ)}
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- **The floor of prime edits read on `Re s > c`** is at least `min(c − 1/15, 2c − 1/2)`. -/
theorem le_floor_primeEditDivisorOn {c : ℝ} (hc : c ≤ 1 / 2) :
    min (c - 1 / 15) (2 * c - 1 / 2) ≤ FloorFreeArithmetic.floor (PrimeEditDivisorOn c) := by
  by_contra h
  have h' := not_le.mp h
  have hnn := floor_nonneg (PrimeEditDivisorOn c)
  have hμ1 : min (c - 1 / 15) (2 * c - 1 / 2) ≤ c - 1 / 15 := min_le_left _ _
  have hμ2 : min (c - 1 / 15) (2 * c - 1 / 2) ≤ 2 * c - 1 / 2 := min_le_right _ _
  have hmodel := hasModelAt_primeEditDivisorOn (c := c)
    (δ := (FloorFreeArithmetic.floor (PrimeEditDivisorOn c) +
      min (c - 1 / 15) (2 * c - 1 / 2)) / 2) hc (by linarith) (by linarith) (by linarith)
  have hle := le_floor_of_hasModelAt hmodel
  linarith

/-- A model right of the critical line at every depth below `13/30`. -/
theorem hasModelAt_primeEditDivisor {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 13 / 30) :
    HasModelAt PrimeEditDivisor δ :=
  hasModelAt_primeEditDivisorOn le_rfl hδ (by linarith) (by linarith)

/-- **The floor of prime edits with a count rate is at least `13/30`.** -/
theorem le_floor_primeEditDivisor : 13 / 30 ≤ FloorFreeArithmetic.floor PrimeEditDivisor := by
  have h := le_floor_primeEditDivisorOn (c := 1 / 2) le_rfl
  have h' : (13 : ℝ) / 30 ≤ min (1 / 2 - 1 / 15) (2 * (1 / 2) - 1 / 2) :=
    le_min (by norm_num) (by norm_num)
  exact h'.trans h

/-- **Read on the strip `1/3 < Re s < 2/3`, where the zeros are symmetric, the floor is at
least `1/6`.** -/
theorem le_floor_primeEditDivisorOn_third :
    1 / 6 ≤ FloorFreeArithmetic.floor (PrimeEditDivisorOn (1 / 3)) := by
  have h := le_floor_primeEditDivisorOn (c := 1 / 3) (by norm_num)
  have h' : (1 : ℝ) / 6 ≤ min (1 / 3 - 1 / 15) (2 * (1 / 3) - 1 / 2) :=
    le_min (by norm_num) (by norm_num)
  exact h'.trans h

end GaloisForLFunctions.WorldsOfTheZeroConfiguration
