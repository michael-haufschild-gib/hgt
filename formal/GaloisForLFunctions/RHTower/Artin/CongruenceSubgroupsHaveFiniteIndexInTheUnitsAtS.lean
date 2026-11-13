import GaloisForLFunctions.RHTower.Artin.CongruenceUnitsOfNormOneAreQuotientsOfConjugates
import GaloisForLFunctions.RHTower.Artin.InvariantDivisorsDescendOutsideALargeSetOfPrimes
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient

/-!
# Congruence subgroups have finite index in the units at `S`

Let `L/K` be a Galois extension of number fields with group `G`, `S` a finite `G`-stable set of
primes of `L`, and `W_k` the congruence subgroups of the normal basis lattices `Λ_j`.

* **Levels lie in lattices** (`exists_level_le_lattice`): `level (j + c) ⊂ Λ_j`. The coordinate
  of `y` at `τθ` is the trace `Tr(y d_τ)` against the dual basis for the trace form, and a trace
  is a sum of conjugates, which have the level of `y d_τ`.
* **Approximation** (`exists_sub_algebraMap_mem_level`): an element `x` of `L` integral at `S`
  is congruent to an integer of `L` modulo any level `J`. Choose an integer `y ≡ 1` modulo
  `w^J` for `w ∈ S` and divisible by the denominator of `x`; then `xy` is an integer and
  `x − xy = x(1 − y)`.
* **Finite index** (`relIndex_congruenceSubgroup_ker_divMap_ne_zero`): `W_k` has finite index
  in the group of elements of `L^×` with exponent zero on `S`. Two such elements with
  approximations congruent modulo `w^J` for all `w ∈ S` differ by a factor in
  `1 + level J ⊂ 1 + Λ`, and `𝓞_L / w^J` is finite.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain HeightOneSpectrum

noncomputable section

namespace GaloisForLFunctions

section Index

/-- `W` has finite index in `U` if a map to a finite set separates the cosets of `W` in `U`. -/
theorem relIndex_ne_zero_of_forall_sub_mem {A F : Type*} [AddCommGroup A] [Finite F]
    {W U : AddSubgroup A} (ψ : A → F)
    (h : ∀ x ∈ U, ∀ x' ∈ U, ψ x = ψ x' → x - x' ∈ W) : W.relIndex U ≠ 0 := by
  haveI : Finite (U ⧸ W.addSubgroupOf U) :=
    Finite.of_injective (fun q : U ⧸ W.addSubgroupOf U => ψ (q.out : U)) fun q q' hq => by
      have h1 : (q.out : A) - (q'.out : A) ∈ W := h _ q.out.2 _ q'.out.2 hq
      rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q']
      exact QuotientAddGroup.eq_iff_sub_mem.mpr (AddSubgroup.mem_addSubgroupOf.mpr h1)
  exact AddSubgroup.index_ne_zero_of_finite

end Index

section Trace

variable (K L : Type*) [Field K] [Field L] [Algebra K L] (G : Type*) [Group G] [Fintype G]
  [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- The trace is the sum of the conjugates. -/
theorem algebraMap_trace_eq_sum_smul (x : L) :
    algebraMap K L (Algebra.trace K L x) = ∑ τ : G, τ • x := by
  haveI := IsGaloisGroup.isGalois G K L
  haveI := IsGaloisGroup.finiteDimensional G K L
  rw [trace_eq_sum_automorphisms]
  exact (Fintype.sum_equiv (IsGaloisGroup.mulEquivAlgEquiv G K L).toEquiv _ _ fun τ => rfl).symm

/-- The basis dual to the normal basis for the trace form. -/
def galoisDualBasis : Module.Basis G K L :=
  haveI := IsGaloisGroup.isGalois G K L
  haveI := IsGaloisGroup.finiteDimensional G K L
  (Algebra.traceForm K L).dualBasis (traceForm_nondegenerate K L) (galoisNormalBasis K L G)

/-- The coordinates in the normal basis are traces: `a_τ(y) = Tr(y d_τ)`. -/
theorem repr_galoisNormalBasis_eq_trace (y : L) (τ : G) :
    (galoisNormalBasis K L G).repr y τ = Algebra.trace K L (y * galoisDualBasis K L G τ) := by
  haveI := IsGaloisGroup.isGalois G K L
  haveI := IsGaloisGroup.finiteDimensional G K L
  have h := LinearMap.BilinForm.dualBasis_repr_apply (traceForm_nondegenerate K L)
    ((Algebra.traceForm K L).dualBasis (traceForm_nondegenerate K L) (galoisNormalBasis K L G))
    y τ
  rw [LinearMap.BilinForm.dualBasis_dualBasis _ (Algebra.traceForm_isSymm K)] at h
  exact h

end Trace

section Level

variable {K : Type*} {L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L] {G : Type*}
  [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

attribute [local instance] primeMulAction

variable {S : SubMulAction G (HeightOneSpectrum (𝓞 L))}

/-- The trace of an element of level `j` has level `j`. -/
theorem algebraMap_trace_mem_level {j : ℤ} {z : L} (hz : z ∈ level L G S j) :
    algebraMap K L (Algebra.trace K L z) ∈ level L G S j := by
  rw [algebraMap_trace_eq_sum_smul K L G]
  exact sum_mem fun τ _ => smul_mem_level τ hz

variable [Fintype S]

/-- **Levels lie in lattices**: `level (j + c) ⊂ Λ_j`. -/
theorem exists_level_le_lattice : ∃ c : ℕ, ∀ j : ℤ, level L G S (j + c) ≤ lattice K S j := by
  obtain ⟨c, hc⟩ := exists_forall_mem_level (S := S) fun τ : G => galoisDualBasis K L G τ
  refine ⟨c, fun j y hy τ => ?_⟩
  rw [repr_galoisNormalBasis_eq_trace]
  have h := mul_mem_level hy (hc τ)
  rw [add_neg_cancel_right] at h
  exact algebraMap_trace_mem_level h

end Level

section Approximation

variable {L : Type*} [Field L] [NumberField L] {G : Type*} [Group G] [MulSemiringAction G L]

attribute [local instance] primeMulAction

variable {S : SubMulAction G (HeightOneSpectrum (𝓞 L))}

/-- An integer lying in `w^J` for all `w ∈ S` has level `J`. -/
theorem algebraMap_mem_level_of_mem_pow {J : ℕ} {r : 𝓞 L} (hr : ∀ w ∈ S, r ∈ w.asIdeal ^ J) :
    algebraMap (𝓞 L) L r ∈ level L G S (J : ℤ) := fun w hw => by
  rw [valuation_of_algebraMap]
  exact (w.intValuation_le_pow_iff_mem r J).mpr (hr w hw)

variable [Fintype S]

/-- **Approximation**: an element integral at `S` is congruent to an integer modulo any
level. -/
theorem exists_sub_algebraMap_mem_level {x : L} (hx : x ∈ level L G S 0) (J : ℕ) :
    ∃ r : 𝓞 L, x - algebraMap (𝓞 L) L r ∈ level L G S (J : ℤ) := by
  by_cases hx0 : x = 0
  · exact ⟨0, by rw [hx0, map_zero, sub_zero]; exact zero_mem _⟩
  obtain ⟨u, rfl⟩ : ∃ u : Lˣ, (u : L) = x := ⟨Units.mk0 x hx0, rfl⟩
  -- an integer `y ≡ 1` modulo `w^J` on `S`, divisible by the denominator of `x`
  have hfin := finite_ordAt_ne_zero L u
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
    (s := (Finset.univ : Finset S).image Subtype.val ∪ hfin.toFinset) (fun v => v.asIdeal)
    (fun v => if v ∈ S then J else (ordAt L v (Additive.ofMul u)).natAbs) (fun v _ => v.prime)
    (fun v _ v' _ hne h => hne (HeightOneSpectrum.ext h))
    (fun v => if v.1 ∈ S then 1 else 0)
  have hS : ∀ w ∈ S, y - 1 ∈ w.asIdeal ^ J := fun w hw => by
    have h := hy w (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨⟨w, hw⟩, Finset.mem_univ _, rfl⟩))
    simpa only [if_pos hw] using h
  have hT : ∀ v, v ∉ S → ordAt L v (Additive.ofMul u) ≠ 0 →
      y ∈ v.asIdeal ^ (ordAt L v (Additive.ofMul u)).natAbs := fun v hv hne => by
    have h := hy v (Finset.mem_union_right _ (hfin.mem_toFinset.mpr hne))
    simpa only [if_neg hv, sub_zero] using h
  -- `x y` is an integer
  have hint : (u : L) * algebraMap (𝓞 L) L y ∈ (algebraMap (𝓞 L) L).range := by
    refine mem_integers_of_valuation_le_one (K := L) _ fun v => ?_
    rw [map_mul, valuation_of_algebraMap]
    by_cases hv : v ∈ S
    · have h1 := hx v hv
      rw [neg_zero, WithZero.exp_zero] at h1
      exact mul_le_one' h1 (v.intValuation_le_one y)
    · by_cases hne : ordAt L v (Additive.ofMul u) = 0
      · rw [(ordAt_eq_zero_iff L v u).mp hne, one_mul]
        exact v.intValuation_le_one y
      · have h2 := (v.intValuation_le_pow_iff_mem y _).mpr (hT v hv hne)
        rw [valuation_eq_exp_neg_ordAt]
        calc WithZero.exp (-(ordAt L v (Additive.ofMul u))) * v.intValuation y
            ≤ WithZero.exp (-(ordAt L v (Additive.ofMul u))) *
                WithZero.exp (-((ordAt L v (Additive.ofMul u)).natAbs : ℤ)) :=
              mul_le_mul' le_rfl h2
          _ ≤ WithZero.exp (0 : ℤ) := by
              rw [← WithZero.exp_add, WithZero.exp_le_exp]
              omega
          _ = 1 := WithZero.exp_zero
  obtain ⟨r, hr⟩ := hint
  refine ⟨r, ?_⟩
  have e : (u : L) - algebraMap (𝓞 L) L r = (u : L) * algebraMap (𝓞 L) L (1 - y) := by
    rw [hr, map_sub, map_one]
    ring
  rw [e]
  have h := mul_mem_level hx
    (algebraMap_mem_level_of_mem_pow (S := S) (r := 1 - y) fun w hw => by
      rw [← neg_sub]
      exact neg_mem (hS w hw))
  rwa [zero_add] at h

end Approximation

section FiniteIndex

variable {K : Type*} {L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L] {G : Type*}
  [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

attribute [local instance] primeMulAction

variable {S : SubMulAction G (HeightOneSpectrum (𝓞 L))} [Fintype S]

/-- **Finite index**: the congruence subgroup `W_k` has finite index in the group of elements
of `L^×` with exponent zero on `S`. -/
theorem relIndex_congruenceSubgroup_ker_divMap_ne_zero (k : ℕ) :
    (congruenceSubgroup K S k).relIndex (divMap L G S).ker ≠ 0 := by
  obtain ⟨c, hc⟩ := exists_level_le_lattice (K := K) (S := S)
  -- integral approximations modulo the level `J`
  have key : ∀ x : L, ∃ r : 𝓞 L, x ∈ level L G S 0 →
      x - algebraMap (𝓞 L) L r ∈ level L G S ((congruenceBase K S + k + c : ℕ) : ℤ) :=
    fun x => by
      by_cases h : x ∈ level L G S 0
      · exact (exists_sub_algebraMap_mem_level h _).imp fun r hr _ => hr
      · exact ⟨0, fun h' => (h h').elim⟩
  choose r hr using key
  haveI : ∀ w : S, Finite (𝓞 L ⧸ w.1.asIdeal ^ (congruenceBase K S + k + c)) := fun w =>
    Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ w.1.ne_bot)
  -- the elements with exponent zero on `S` have valuation one on `S`
  have hval : ∀ x ∈ (divMap L G S).ker, ∀ w ∈ S,
      w.valuation L ((Additive.toMul x : Lˣ) : L) = 1 := fun x hx w hw =>
    (ordAt_eq_zero_iff L w (Additive.toMul x)).mp (congrFun (AddMonoidHom.mem_ker.mp hx) ⟨w, hw⟩)
  have hlev : ∀ x ∈ (divMap L G S).ker, ((Additive.toMul x : Lˣ) : L) ∈ level L G S 0 :=
    fun x hx w hw => by rw [hval x hx w hw, neg_zero, WithZero.exp_zero]
  refine relIndex_ne_zero_of_forall_sub_mem
    (F := (w : S) → 𝓞 L ⧸ w.1.asIdeal ^ (congruenceBase K S + k + c))
    (fun x w => Ideal.Quotient.mk _ (r ((Additive.toMul x : Lˣ) : L))) fun x hx x' hx' hψ => ?_
  -- equal residues: the difference has level `J`
  have h1 : ((Additive.toMul x : Lˣ) : L) - ((Additive.toMul x' : Lˣ) : L) ∈
      level L G S ((congruenceBase K S + k + c : ℕ) : ℤ) := by
    have hrr : algebraMap (𝓞 L) L
        (r ((Additive.toMul x : Lˣ) : L) - r ((Additive.toMul x' : Lˣ) : L)) ∈
        level L G S ((congruenceBase K S + k + c : ℕ) : ℤ) :=
      algebraMap_mem_level_of_mem_pow fun w hw => Ideal.Quotient.eq.mp (congrFun hψ ⟨w, hw⟩)
    have e : ((Additive.toMul x : Lˣ) : L) - ((Additive.toMul x' : Lˣ) : L) =
        (((Additive.toMul x : Lˣ) : L) - algebraMap (𝓞 L) L (r ((Additive.toMul x : Lˣ) : L))) -
          (((Additive.toMul x' : Lˣ) : L) -
            algebraMap (𝓞 L) L (r ((Additive.toMul x' : Lˣ) : L))) +
          algebraMap (𝓞 L) L
            (r ((Additive.toMul x : Lˣ) : L) - r ((Additive.toMul x' : Lˣ) : L)) := by
      rw [map_sub]
      ring
    rw [e]
    exact add_mem (sub_mem (hr _ (hlev x hx)) (hr _ (hlev x' hx'))) hrr
  have hinv : (((Additive.toMul x' : Lˣ) : L))⁻¹ ∈ level L G S 0 := fun w hw => by
    rw [map_inv₀, hval x' hx' w hw, inv_one, neg_zero, WithZero.exp_zero]
  -- the quotient is `1 + (x − x') x'⁻¹`
  refine mem_congruenceSubgroup.mpr (hc _ ?_)
  show ((Additive.toMul x / Additive.toMul x' : Lˣ) : L) - 1 ∈
    level L G S (((congruenceBase K S + k : ℕ) : ℤ) + c)
  have e : ((Additive.toMul x / Additive.toMul x' : Lˣ) : L) - 1 =
      (((Additive.toMul x : Lˣ) : L) - ((Additive.toMul x' : Lˣ) : L)) *
        (((Additive.toMul x' : Lˣ) : L))⁻¹ := by
    rw [Units.val_div_eq_div_val, sub_mul, div_eq_mul_inv,
      mul_inv_cancel₀ (Additive.toMul x').ne_zero]
  rw [e]
  have h2 := mul_mem_level h1 hinv
  rwa [add_zero, Nat.cast_add] at h2

end FiniteIndex

end GaloisForLFunctions
