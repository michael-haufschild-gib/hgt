import Mathlib.Data.Finsupp.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic

/-!
# No equivariant Hilbert lift of an infinite orbit quotient

Pair-face residues are finite-support functions on an orbit quotient `G ⧸ H`. To turn such a
charge into a potential in a representation where the period subgroup `H` still acts, one would
need to lift the quotient basis vector. This file proves the obstruction used to close the
polarized pair-face/Sonin bridge:

* an infinite subgroup has no nonzero invariant vector in the finite-support regular module;
* therefore orbit pushforward has no translation-equivariant linear section;
* the same obstruction holds for square-summable regular vectors.

The result is carrier-free. In the prime specialization, `H` is the infinite period subgroup and
the regular action is the algebraic or Hilbert precursor of the nontrivial Mellin-dilation action.
-/

namespace GaloisForLFunctions

noncomputable section

/-- Left translation on the finite-support regular module. -/
def leftTranslateFinsupp {G R : Type*} [Group G] [AddCommMonoid R]
    (g : G) (f : G →₀ R) : G →₀ R :=
  Finsupp.mapDomain (fun x => g * x) f

@[simp]
theorem leftTranslateFinsupp_apply {G R : Type*} [Group G] [AddCommMonoid R]
    (g x : G) (f : G →₀ R) :
    leftTranslateFinsupp g f (g * x) = f x := by
  exact Finsupp.mapDomain_apply (fun _ _ h => mul_left_cancel h) f x

/-- A finite-support vector invariant under an infinite subgroup is zero. -/
theorem eq_zero_of_infinite_subgroup_leftInvariant
    {G R : Type*} [Group G] [AddCommMonoid R]
    (H : Subgroup G) [Infinite H] (f : G →₀ R)
    (hinv : ∀ h : H, leftTranslateFinsupp h.1 f = f) : f = 0 := by
  by_contra hf
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    simpa [Finsupp.ext_iff] using hf
  let emb : H → f.support := fun h => ⟨h.1 * x, by
    rw [Finsupp.mem_support_iff]
    rw [← hinv h]
    simpa using hx⟩
  have hemb : Function.Injective emb := by
    intro h k heq
    apply Subtype.ext
    apply mul_right_cancel (b := x)
    exact congrArg Subtype.val heq
  haveI : Finite H := Finite.of_injective emb hemb
  exact not_finite H

/-- Push finite-support coefficients from the regular module to the orbit quotient. -/
def orbitPushforward {G R : Type*} [CommGroup G] [Semiring R]
    (H : Subgroup G) : (G →₀ R) →ₗ[R] ((G ⧸ H) →₀ R) :=
  Finsupp.lmapDomain R R (QuotientGroup.mk' H)

/-- Left translation on the orbit-quotient module. -/
def leftTranslateOrbitFinsupp {G R : Type*} [CommGroup G] [AddCommMonoid R]
    (H : Subgroup G) (g : G) (f : (G ⧸ H) →₀ R) : (G ⧸ H) →₀ R :=
  Finsupp.mapDomain (fun x => QuotientGroup.mk' H g * x) f

@[simp]
theorem leftTranslateOrbitFinsupp_single {G R : Type*} [CommGroup G] [AddCommMonoid R]
    (H : Subgroup G) (g : G) (x : G ⧸ H) (r : R) :
    leftTranslateOrbitFinsupp H g (Finsupp.single x r) =
      Finsupp.single (QuotientGroup.mk' H g * x) r := by
  exact Finsupp.mapDomain_single

/-- **Algebraic orbit-lift no-go.** For an infinite subgroup, orbit pushforward admits no linear
section which intertwines all left translations. -/
theorem no_equivariant_orbitPushforward_section
    {G R : Type*} [CommGroup G] [CommSemiring R] [Nontrivial R]
    (H : Subgroup G) [Infinite H]
    (s : ((G ⧸ H) →₀ R) →ₗ[R] (G →₀ R))
    (hsection : (orbitPushforward H).comp s = LinearMap.id)
    (hequiv : ∀ g v, leftTranslateFinsupp g (s v) =
      s (leftTranslateOrbitFinsupp H g v)) : False := by
  let e : (G ⧸ H) →₀ R := Finsupp.single (QuotientGroup.mk' H 1) 1
  have he_ne : e ≠ 0 := by
    change Finsupp.single (QuotientGroup.mk' H 1) (1 : R) ≠ 0
    exact (Finsupp.single_ne_zero (a := QuotientGroup.mk' H 1) (b := (1 : R))).mpr
      one_ne_zero
  have hinv : ∀ h : H, leftTranslateFinsupp h.1 (s e) = s e := by
    intro h
    rw [hequiv]
    congr 1
    have hh : QuotientGroup.mk' H h.1 = 1 := (QuotientGroup.eq_one_iff _).mpr h.2
    simp [e, leftTranslateOrbitFinsupp, hh]
  have hzero : s e = 0 := eq_zero_of_infinite_subgroup_leftInvariant H (s e) hinv
  have hback := LinearMap.congr_fun hsection e
  simp only [LinearMap.comp_apply, LinearMap.id_apply, hzero, map_zero] at hback
  exact he_ne hback.symm

/-- **Hilbert orbit-lift no-go.** A square-summable regular vector invariant under an infinite
subgroup is zero. This is the coefficient-function form of the statement that `ℓ²(G)` has no
nonzero `H`-fixed orbit vector. -/
theorem eq_zero_of_infinite_subgroup_leftInvariant_summable_normSq
    {G E : Type*} [Group G] [NormedAddCommGroup E]
    (H : Subgroup G) [Infinite H] (f : G → E)
    (hsum : Summable (fun g => ‖f g‖ ^ (2 : ℕ)))
    (hinv : ∀ h : H, ∀ x, f (h.1 * x) = f x) : f = 0 := by
  funext x
  by_contra hx
  have hpos : 0 < ‖f x‖ ^ (2 : ℕ) := sq_pos_of_pos (norm_pos_iff.mpr hx)
  let emb : H → G := fun h => h.1 * x
  have hemb : Function.Injective emb := by
    intro h k heq
    apply Subtype.ext
    exact mul_right_cancel heq
  have hconst : Summable (fun _ : H => ‖f x‖ ^ (2 : ℕ)) := by
    have hcomp := hsum.comp_injective hemb
    apply hcomp.congr
    intro h
    change ‖f (h.1 * x)‖ ^ (2 : ℕ) = ‖f x‖ ^ (2 : ℕ)
    rw [hinv h x]
  haveI : Finite H := Finite.of_summable_const hpos hconst
  exact not_finite H

/-- Pair differences annihilate the common-potential mode. -/
@[simp]
theorem pairDifference_const
    {ι V : Type*} [AddCommGroup V] (a : V) (i j : ι) :
    (fun _ : ι => a) i - (fun _ : ι => a) j = 0 := by
  simp

end

end GaloisForLFunctions
