import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Ramification from nontrivial relative differentials

Over a local base with a discrete valuation ring upstairs and separable residue extension, the
extended maximal ideal is the maximal ideal exactly when the relative differentials vanish
(`Algebra.FormallyUnramified.of_map_maximalIdeal`).  Since a nonzero ideal of a discrete valuation
ring that is not the maximal ideal lies in its square, nonvanishing differentials give ramification
index at least two:

```text
map_maximalIdeal_le_sq_of_not_subsingleton :
    ¬ Subsingleton Ω[B⁄A]  →  (maximalIdeal A).map (algebraMap A B) ≤ (maximalIdeal B) ^ 2
```

`isUnit_det_of_span_eq_top` is the companion linear-algebra step: a family of `N` vectors spanning
a free module of rank `N` has unit determinant in any basis.  Its contrapositive detects
nonvanishing differentials from a determinant lying in the maximal ideal.
-/

namespace GaloisForLFunctions.HTGeometry

open IsLocalRing Matrix

/-- **A spanning family of the right size has unit determinant.**  Writing each basis vector in
terms of the family produces a left inverse of the coordinate matrix. -/
theorem isUnit_det_of_span_eq_top {B M : Type*} [CommRing B] [AddCommGroup M] [Module B M]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι B M) (v : ι → M)
    (hspan : Submodule.span B (Set.range v) = ⊤) :
    IsUnit (Matrix.of (fun i j => b.repr (v j) i)).det := by
  classical
  set Mx : Matrix ι ι B := Matrix.of (fun i j => b.repr (v j) i) with hMx
  have hcoef : ∀ i : ι, ∃ c : ι → B, ∑ j, c j • v j = b i := by
    intro i
    have : b i ∈ Submodule.span B (Set.range v) := by rw [hspan]; trivial
    exact (Submodule.mem_span_range_iff_exists_fun B).mp this
  choose c hc using hcoef
  set C : Matrix ι ι B := Matrix.of (fun i j => c i j) with hC
  have hCM : C * Mx.transpose = 1 := by
    ext i k
    have := congrArg (fun x => b.repr x k) (hc i)
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Module.Basis.repr_self] at this
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [hC, hMx, Matrix.transpose_apply, Finsupp.single_apply, eq_comm] using this
  have hdet := congrArg Matrix.det hCM
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hdet
  exact isUnit_iff_exists_inv.mpr ⟨C.det, by rw [mul_comm]; exact hdet⟩

/-- In a discrete valuation ring a nonzero ideal different from the maximal ideal lies in its
square. -/
theorem le_maximalIdeal_sq_of_ne {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {I : Ideal B} (hle : I ≤ maximalIdeal B) (hne : I ≠ maximalIdeal B) (hbot : I ≠ ⊥) :
    I ≤ (maximalIdeal B) ^ 2 := by
  classical
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal I).principal
  have haI : I = Ideal.span {a} := ha
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hbot (by rw [haI, Ideal.span_singleton_eq_bot.mpr rfl])
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hπ
  have hassoc : Associated a (π ^ n) :=
    ⟨u⁻¹, by rw [hu, mul_comm (u : B) (π ^ n), mul_assoc]; simp⟩
  have hspan : I = Ideal.span {π ^ n} := by
    rw [haI, Ideal.span_singleton_eq_span_singleton.mpr hassoc]
  have hmax : maximalIdeal B = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hn1 : n ≠ 1 := by
    rintro rfl
    exact hne (by rw [hspan, hmax, pow_one])
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [hspan, pow_zero, Ideal.span_singleton_one] at hle
    exact (maximalIdeal.isMaximal B).ne_top (top_le_iff.mp hle)
  rw [hspan, hmax, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton]
  exact pow_dvd_pow π (by omega)

/-- **Nontrivial relative differentials force ramification index at least two.** -/
theorem map_maximalIdeal_le_sq_of_not_subsingleton {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [IsLocalRing A] [IsDomain B] [IsDiscreteValuationRing B]
    [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    (h : ¬ Subsingleton Ω[B⁄A])
    (hbot : (maximalIdeal A).map (algebraMap A B) ≠ ⊥) :
    (maximalIdeal A).map (algebraMap A B) ≤ (maximalIdeal B) ^ 2 := by
  refine le_maximalIdeal_sq_of_ne ?_ ?_ hbot
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    simp only [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    exact fun hu => hx (isUnit_of_map_unit (algebraMap A B) x hu)
  · intro H
    exact h (Algebra.FormallyUnramified.of_map_maximalIdeal H).subsingleton_kaehlerDifferential

end GaloisForLFunctions.HTGeometry
