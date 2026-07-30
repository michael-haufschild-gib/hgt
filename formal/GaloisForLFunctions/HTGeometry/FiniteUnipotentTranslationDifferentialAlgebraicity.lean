import GaloisForLFunctions.HTGeometry.MeroFieldShiftStableSpace
import GaloisForLFunctions.HTGeometry.EllipticCompositumRationalBase

/-!
# Finite unipotent translation orbits are differentially algebraic

A unit-periodic meromorphic germ whose iterated defect under one upper-half-plane translation
vanishes has a finite-dimensional span of translation defects.  This span is stable under both
translations `1` and `β`.  The shift-stable-space theorem therefore makes the original germ
differentially algebraic over `ℂ(z)`.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra

/-- The `n`-fold forward difference for translation by `β`. -/
def iteratedMeroTranslationDefect (β : ℂ) :
    ℕ → meroField (Set.univ : Set ℂ) → meroField (Set.univ : Set ℂ)
  | 0, x => x
  | n + 1, x =>
      addTranslationMeroEquiv β (iteratedMeroTranslationDefect β n x) -
        iteratedMeroTranslationDefect β n x

@[simp]
theorem iteratedMeroTranslationDefect_zero (β : ℂ)
    (x : meroField (Set.univ : Set ℂ)) :
    iteratedMeroTranslationDefect β 0 x = x := rfl

@[simp]
theorem iteratedMeroTranslationDefect_succ (β : ℂ) (n : ℕ)
    (x : meroField (Set.univ : Set ℂ)) :
    iteratedMeroTranslationDefect β (n + 1) x =
      addTranslationMeroEquiv β (iteratedMeroTranslationDefect β n x) -
        iteratedMeroTranslationDefect β n x := rfl

theorem addTranslationMeroEquiv_iteratedMeroTranslationDefect_self
    (β : ℂ) (n : ℕ) (x : meroField (Set.univ : Set ℂ)) :
    addTranslationMeroEquiv β (iteratedMeroTranslationDefect β n x) =
      iteratedMeroTranslationDefect β n x +
        iteratedMeroTranslationDefect β (n + 1) x := by
  rw [iteratedMeroTranslationDefect_succ]
  ring

theorem addTranslationMeroEquiv_iteratedMeroTranslationDefect_comm
    (α β : ℂ) (n : ℕ) (x : meroField (Set.univ : Set ℂ)) :
    addTranslationMeroEquiv α (iteratedMeroTranslationDefect β n x) =
      iteratedMeroTranslationDefect β n (addTranslationMeroEquiv α x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedMeroTranslationDefect_succ,
        iteratedMeroTranslationDefect_succ, map_sub, ih,
        addTranslationMeroEquiv_comm α β]
      rw [ih]

theorem addTranslationMeroEquiv_iteratedMeroTranslationDefect_of_fixed
    {α β : ℂ} {x : meroField (Set.univ : Set ℂ)}
    (hα : addTranslationMeroEquiv α x = x) (n : ℕ) :
    addTranslationMeroEquiv α (iteratedMeroTranslationDefect β n x) =
      iteratedMeroTranslationDefect β n x := by
  rw [addTranslationMeroEquiv_iteratedMeroTranslationDefect_comm, hα]

theorem iteratedMeroTranslationDefect_eq_zero_of_ge
    {β : ℂ} {x : meroField (Set.univ : Set ℂ)} {N : ℕ}
    (hN : iteratedMeroTranslationDefect β N x = 0) :
    ∀ n, N ≤ n → iteratedMeroTranslationDefect β n x = 0 := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction k with
  | zero => simpa using hN
  | succ k ih =>
      rw [Nat.add_succ, iteratedMeroTranslationDefect_succ, ih, map_zero, sub_zero]

/-- **Finite-unipotent two-shift law.** A unit-periodic meromorphic germ killed by a finite
iterate of the defect for an upper-half-plane step is differentially algebraic over `ℂ(z)`. -/
theorem differentialAlgebraicOver_of_iteratedMeroTranslationDefect_eq_zero
    {β : ℂ} (hβ : 0 < β.im)
    {x : meroField (Set.univ : Set ℂ)}
    (hone : addTranslationMeroEquiv 1 x = x)
    {N : ℕ} (hN : iteratedMeroTranslationDefect β N x = 0) :
    DifferentialAlgebraicOver (RatFunc ℂ) x := by
  have hindepR : LinearIndependent ℝ ![(1 : ℂ), β] :=
    linearIndependent_one_of_im_pos hβ
  have hcast : Function.Injective (fun q : ℚ => q • (1 : ℝ)) := by
    intro a b hab
    exact Rat.cast_injective (by simpa using! hab)
  have hindepQ : LinearIndependent ℚ ![(1 : ℂ), β] :=
    hindepR.restrict_scalars hcast
  let v : Fin (N + 1) → meroField (Set.univ : Set ℂ) :=
    fun k => iteratedMeroTranslationDefect β k x
  let W : Submodule ℂ (meroField (Set.univ : Set ℂ)) :=
    Submodule.span ℂ (Set.range v)
  haveI hfd : FiniteDimensional ℂ W :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
  have hfinrank : Module.finrank ℂ W ≤ N + 1 := by
    simpa [W] using! finrank_range_le_card (R := ℂ) v
  have hxW : x ∈ W := by
    apply Submodule.subset_span
    exact ⟨0, rfl⟩
  have honeW : ∀ u ∈ W, addTranslationMeroEquiv 1 u ∈ W := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨k, rfl⟩ := hy
        rw [addTranslationMeroEquiv_iteratedMeroTranslationDefect_of_fixed hone k]
        exact Submodule.subset_span ⟨k, rfl⟩
    | zero => simp
    | add a b _ _ ha hb =>
        rw [map_add]
        exact W.add_mem ha hb
    | smul c y _ hy =>
        rw [Algebra.smul_def, map_mul,
          HTGeometry.addTranslationMeroEquiv_algebraMap_complex_self,
          ← Algebra.smul_def]
        exact W.smul_mem c hy
  have hβW : ∀ u ∈ W, addTranslationMeroEquiv β u ∈ W := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨k, rfl⟩ := hy
        rw [addTranslationMeroEquiv_iteratedMeroTranslationDefect_self]
        apply W.add_mem
        · exact Submodule.subset_span ⟨k, rfl⟩
        · by_cases hk : (k : ℕ) < N
          · exact Submodule.subset_span
              ⟨⟨(k : ℕ) + 1, by omega⟩, rfl⟩
          · have hkN : N ≤ (k : ℕ) := by omega
            rw [iteratedMeroTranslationDefect_eq_zero_of_ge hN ((k : ℕ) + 1)
              (by omega)]
            exact W.zero_mem
    | zero => simp
    | add a b _ _ ha hb =>
        rw [map_add]
        exact W.add_mem ha hb
    | smul c y _ hy =>
        rw [Algebra.smul_def, map_mul,
          HTGeometry.addTranslationMeroEquiv_algebraMap_complex_self,
          ← Algebra.smul_def]
        exact W.smul_mem c hy
  exact differentialAlgebraicOver_of_mem_shiftStable hindepQ
    (N + 1) W hfd hfinrank honeW hβW x hxW

end

end GaloisForLFunctions
