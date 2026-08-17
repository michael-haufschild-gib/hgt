import GaloisForLFunctions.HTGeometry.SiegelTorusTranscendence
import GaloisForLFunctions.HTGeometry.SeveralVariableTranslation
import GaloisForLFunctions.HTGeometry.PencilDifferentialIndependence

/-!
# Algebraic dependence in the several-variable meromorphic field

Siegel's bound, transported into the corpus's own meromorphic field `meroFieldGen (Set.univ)`: any
`n + 2` elements whose period groups all contain a subgroup with compact quotient are algebraically
dependent over `ℂ`.

The transport is the fraction-field presentation.  Each element is a quotient of two analytic germs;
the germs have entire representatives; the period condition cross-multiplies to the pointwise
identity the analytic theorem consumes; and the denominator-cleared combination the theorem produces
vanishes identically, hence is the zero germ, hence gives the relation after dividing by the
product of the denominators — which is invertible in the field.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher Filter Set

/-- The ring of entire germs of `ℂ^{n+1}`. -/
noncomputable abbrev entireGermRing (n : ℕ) := analyticSubringGen (Set.univ : Set (Fin (n + 1) → ℂ))

/-- The meromorphic field of `ℂ^{n+1}`. -/
noncomputable abbrev meroFieldCn (n : ℕ) := meroFieldGen (Set.univ : Set (Fin (n + 1) → ℂ))

variable {n : ℕ}

/-- **Siegel's bound in the meromorphic field.**  Any `n + 2` elements of the several-variable
meromorphic field of `ℂ^{n+1}` whose period groups all contain a subgroup with compact quotient
satisfy a nonzero polynomial relation over `ℂ`. -/
theorem exists_ne_zero_poly_aeval_of_compactSpace_quotient
    {P : AddSubgroup (Fin (n + 1) → ℂ)} (hP : CompactSpace ((Fin (n + 1) → ℂ) ⧸ P))
    (x : Fin (n + 2) → meroFieldCn n)
    (hper : ∀ k, ∀ p ∈ P, p ∈ meroPeriodSubgroupGen (E := Fin (n + 1) → ℂ) (x k)) :
    ∃ Q : MvPolynomial (Fin (n + 2)) ℂ, Q ≠ 0 ∧ MvPolynomial.aeval x Q = 0 := by
  classical
  -- present every element as a quotient of two analytic germs
  have hpres : ∀ k, ∃ (uu vv : entireGermRing n), vv ≠ 0 ∧
      x k = algebraMap (entireGermRing n) (meroFieldCn n) uu
        / algebraMap (entireGermRing n) (meroFieldCn n) vv := by
    intro k
    obtain ⟨uu, vv, hvv, huv⟩ :=
      IsFractionRing.div_surjective (A := entireGermRing n) (K := meroFieldCn n) (x k)
    exact ⟨uu, vv, nonZeroDivisors.ne_zero hvv, huv.symm⟩
  choose u v hv hx using hpres
  -- entire representatives
  have hreps : ∀ k, ∃ f : (Fin (n + 1) → ℂ) → ℂ,
      AnalyticOnNhd ℂ f Set.univ ∧ Germ.coeRingHom (𝓟 (Set.univ : Set (Fin (n + 1) → ℂ))) f
        = (u k : Germ (𝓟 (Set.univ : Set (Fin (n + 1) → ℂ))) ℂ) := fun k => (u k).2
  choose A hAan hAg using hreps
  have hrepsB : ∀ k, ∃ f : (Fin (n + 1) → ℂ) → ℂ,
      AnalyticOnNhd ℂ f Set.univ ∧ Germ.coeRingHom (𝓟 (Set.univ : Set (Fin (n + 1) → ℂ))) f
        = (v k : Germ (𝓟 (Set.univ : Set (Fin (n + 1) → ℂ))) ℂ) := fun k => (v k).2
  choose B hBan hBg using hrepsB
  have hAdiff : ∀ k, Differentiable ℂ (A k) := fun k z => (hAan k z (mem_univ z)).differentiableAt
  have hBdiff : ∀ k, Differentiable ℂ (B k) := fun k z => (hBan k z (mem_univ z)).differentiableAt
  have hB0 : ∀ k, ∃ z, B k z ≠ 0 := by
    intro k
    by_contra hcon
    push Not at hcon
    refine hv k ?_
    refine Subtype.ext ?_
    rw [ZeroMemClass.coe_zero, ← hBg k]
    have hz : B k = 0 := funext fun z => hcon z
    rw [hz, map_zero]
  -- the period condition, cross-multiplied
  have hcross : ∀ k, ∀ p ∈ P, ∀ z, A k (z + p) * B k z = A k z * B k (z + p) := by
    intro k p hp z
    have hmem := hper k p hp
    rw [hx k] at hmem
    exact (mem_meroPeriodSubgroupGen_iff (hv k) (hAg k) (hBg k) p).mp hmem z
  -- the analytic theorem
  obtain ⟨m, a, ha0, hzero⟩ :=
    exists_ne_zero_siegelHomCombination_of_periodic_meromorphic hP hAdiff hBdiff hB0 hcross
  refine ⟨siegelPoly a, siegelPoly_ne_zero ha0, ?_⟩
  -- the cleared relation, as an element of the germ ring
  have hfun : (siegelHomCombination A B m a : (Fin (n + 1) → ℂ) → ℂ)
      = ∑ β : Fin (n + 2) → Fin (m + 1),
        (Function.const (Fin (n + 1) → ℂ) (a β))
          * ∏ k, (A k) ^ (β k : ℕ) * (B k) ^ (m - (β k : ℕ)) := by
    funext z
    simp [siegelHomCombination, Finset.sum_apply, Finset.prod_apply]
  have hXzero : (∑ β : Fin (n + 2) → Fin (m + 1),
      constToAnalyticGen (Set.univ : Set (Fin (n + 1) → ℂ)) (a β)
        * ∏ k, (u k) ^ (β k : ℕ) * (v k) ^ (m - (β k : ℕ)) : entireGermRing n) = 0 := by
    refine Subtype.ext ?_
    rw [ZeroMemClass.coe_zero]
    have hsum : ((∑ β : Fin (n + 2) → Fin (m + 1),
        constToAnalyticGen (Set.univ : Set (Fin (n + 1) → ℂ)) (a β)
          * ∏ k, (u k) ^ (β k : ℕ) * (v k) ^ (m - (β k : ℕ)) : entireGermRing n) :
          Germ (𝓟 (Set.univ : Set (Fin (n + 1) → ℂ))) ℂ)
        = Germ.coeRingHom (𝓟 (Set.univ : Set (Fin (n + 1) → ℂ)))
            (siegelHomCombination A B m a) := by
      rw [hfun]
      simp only [map_sum, map_mul, map_prod, map_pow, ← hAg, ← hBg,
        AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, SubmonoidClass.coe_finset_prod,
        SubmonoidClass.coe_pow]
      rfl
    rw [hsum]
    have hz : siegelHomCombination A B m a = 0 := funext hzero
    rw [hz, map_zero]
  -- pass to the field and cancel the denominators
  have hden : ∀ k, algebraMap (entireGermRing n) (meroFieldCn n) (v k) ≠ 0 := by
    intro k hk
    exact hv k (IsFractionRing.injective (entireGermRing n) (meroFieldCn n)
      (by rw [hk, map_zero]))
  have hxv : ∀ k, x k * algebraMap (entireGermRing n) (meroFieldCn n) (v k)
      = algebraMap (entireGermRing n) (meroFieldCn n) (u k) := by
    intro k
    rw [hx k, div_mul_cancel₀ _ (hden k)]
  have hkey : MvPolynomial.aeval x (siegelPoly a)
      * ∏ k, (algebraMap (entireGermRing n) (meroFieldCn n) (v k)) ^ m = 0 := by
    have hmapzero : algebraMap (entireGermRing n) (meroFieldCn n)
        (∑ β : Fin (n + 2) → Fin (m + 1),
          constToAnalyticGen (Set.univ : Set (Fin (n + 1) → ℂ)) (a β)
            * ∏ k, (u k) ^ (β k : ℕ) * (v k) ^ (m - (β k : ℕ))) = 0 := by
      rw [hXzero, map_zero]
    rw [aeval_siegelPoly, Finset.sum_mul, ← hmapzero, map_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [map_mul, map_prod]
    have hconst : algebraMap (entireGermRing n) (meroFieldCn n)
        (constToAnalyticGen (Set.univ : Set (Fin (n + 1) → ℂ)) (a β))
        = algebraMap ℂ (meroFieldCn n) (a β) := by
      rw [IsScalarTower.algebraMap_apply ℂ (entireGermRing n) (meroFieldCn n)]
      rfl
    rw [hconst, mul_assoc]
    congr 1
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_mul, map_pow, map_pow, ← hxv k, mul_pow]
    have hsplit : (algebraMap (entireGermRing n) (meroFieldCn n) (v k)) ^ m
        = (algebraMap (entireGermRing n) (meroFieldCn n) (v k)) ^ (β k : ℕ)
          * (algebraMap (entireGermRing n) (meroFieldCn n) (v k)) ^ (m - (β k : ℕ)) := by
      rw [← pow_add]
      congr 1
      have hle : (β k : ℕ) ≤ m := Nat.lt_succ_iff.mp (β k).2
      omega
    rw [hsplit]
    ring
  have hprodne : (∏ k, (algebraMap (entireGermRing n) (meroFieldCn n) (v k)) ^ m) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hden k)
  exact (mul_eq_zero.mp hkey).resolve_right hprodne

end GaloisForLFunctions.HTGeometry
