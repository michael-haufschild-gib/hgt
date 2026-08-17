import GaloisForLFunctions.HTGeometry.SiegelTorusTranscendence
import GaloisForLFunctions.HTGeometry.ComplexTorusVelocityTail

/-!
# The noncompact period-quotient law in every dimension

Siegel's bound, read in the entire fraction field: if a subgroup `P` of `ℂ^{n+1}` fixes `n + 2`
elements of that field and the quotient by `P` is compact, the elements are algebraically dependent
over `ℂ`.

Applied to the jets of a single element it becomes the period-escape law.  A constant directional
derivation commutes with every translation, so all the jets of a `P`-invariant element are again
`P`-invariant; if the quotient were compact, `n + 2` of those jets would satisfy a nonzero
polynomial relation, i.e. the element would be differentially algebraic over `ℂ`.  Contrapositive:
a hypertranscendental element has a noncompact period quotient — in every dimension, not only in
one variable.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Set

variable {n : ℕ}

/-! ## The cross-multiplied invariance criterion -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem fieldTranslateEquiv_div (t : V) (a b : entireSubring V) :
    fieldTranslateEquiv t
        (algebraMap (entireSubring V) (EntireField V) a
          / algebraMap (entireSubring V) (EntireField V) b)
      = algebraMap (entireSubring V) (EntireField V) (entireTranslate t a)
        / algebraMap (entireSubring V) (EntireField V) (entireTranslate t b) := by
  rw [map_div₀, fieldTranslateEquiv_algebraMap, fieldTranslateEquiv_algebraMap]

/-- **A translation fixes a fraction of entire functions exactly when it fixes it after
cross-multiplication.** -/
theorem fieldTranslateEquiv_fix_iff {a b : entireSubring V} (hb : b ≠ 0) (t : V) :
    fieldTranslateEquiv t
        (algebraMap (entireSubring V) (EntireField V) a
          / algebraMap (entireSubring V) (EntireField V) b)
        = algebraMap (entireSubring V) (EntireField V) a
          / algebraMap (entireSubring V) (EntireField V) b
      ↔ ∀ z : V, (a : V → ℂ) (z + t) * (b : V → ℂ) z
          = (a : V → ℂ) z * (b : V → ℂ) (z + t) := by
  have hinj : Function.Injective (algebraMap (entireSubring V) (EntireField V)) :=
    IsFractionRing.injective (entireSubring V) (EntireField V)
  have hb0 : algebraMap (entireSubring V) (EntireField V) b ≠ 0 := by
    intro h
    exact hb (hinj (by rw [h, map_zero]))
  have htb : entireTranslate t b ≠ 0 := by
    intro h
    refine hb (Subtype.ext (funext fun z => ?_))
    have := congrArg (fun c : entireSubring V => (c : V → ℂ) (z - t)) h
    simpa using this
  have htb0 : algebraMap (entireSubring V) (EntireField V) (entireTranslate t b) ≠ 0 := by
    intro h
    exact htb (hinj (by rw [h, map_zero]))
  rw [fieldTranslateEquiv_div, div_eq_div_iff htb0 hb0, ← map_mul, ← map_mul]
  constructor
  · intro h z
    have hring : entireTranslate t a * b = a * entireTranslate t b := hinj h
    have := congrArg (fun c : entireSubring V => (c : V → ℂ) z) hring
    simpa using this
  · intro h
    congr 1
    refine Subtype.ext (funext fun z => ?_)
    have hz := h z
    simpa using hz

/-! ## Siegel's bound in the entire fraction field -/

/-- **Siegel's bound in the entire fraction field.** -/
theorem exists_ne_zero_poly_aeval_entire_of_compactSpace_quotient
    {P : AddSubgroup (Fin (n + 1) → ℂ)} (hP : CompactSpace ((Fin (n + 1) → ℂ) ⧸ P))
    (x : Fin (n + 2) → EntireField (Fin (n + 1) → ℂ))
    (hfix : ∀ k, ∀ p ∈ P, fieldTranslateEquiv p (x k) = x k) :
    ∃ Q : MvPolynomial (Fin (n + 2)) ℂ, Q ≠ 0 ∧ MvPolynomial.aeval x Q = 0 := by
  classical
  set W := Fin (n + 1) → ℂ
  have hpres : ∀ k, ∃ uu vv : entireSubring W, vv ≠ 0 ∧
      x k = algebraMap (entireSubring W) (EntireField W) uu
        / algebraMap (entireSubring W) (EntireField W) vv := by
    intro k
    obtain ⟨uu, vv, hvv, huv⟩ :=
      IsFractionRing.div_surjective (A := entireSubring W) (K := EntireField W) (x k)
    exact ⟨uu, vv, nonZeroDivisors.ne_zero hvv, huv.symm⟩
  choose u v hv hx using hpres
  set A : Fin (n + 2) → W → ℂ := fun k => ((u k : entireSubring W) : W → ℂ) with hAdef
  set B : Fin (n + 2) → W → ℂ := fun k => ((v k : entireSubring W) : W → ℂ) with hBdef
  have hAdiff : ∀ k, Differentiable ℂ (A k) := fun k =>
    differentiable_of_analyticOnNhd (u k).2
  have hBdiff : ∀ k, Differentiable ℂ (B k) := fun k =>
    differentiable_of_analyticOnNhd (v k).2
  have hB0 : ∀ k, ∃ z, B k z ≠ 0 := by
    intro k
    by_contra hcon
    push Not at hcon
    exact hv k (Subtype.ext (funext fun z => hcon z))
  have hper : ∀ k, ∀ p ∈ P, ∀ z, A k (z + p) * B k z = A k z * B k (z + p) := by
    intro k p hp z
    have hfixk := hfix k p hp
    rw [hx k] at hfixk
    exact (fieldTranslateEquiv_fix_iff (hv k) p).mp hfixk z
  obtain ⟨m, a, ha0, hzero⟩ :=
    exists_ne_zero_siegelHomCombination_of_periodic_meromorphic hP hAdiff hBdiff hB0 hper
  refine ⟨siegelPoly a, siegelPoly_ne_zero ha0, ?_⟩
  -- the cleared relation is the zero entire function
  have hXzero : (∑ β : Fin (n + 2) → Fin (m + 1),
      constEntireRing W (a β) * ∏ k, (u k) ^ (β k : ℕ) * (v k) ^ (m - (β k : ℕ))
        : entireSubring W) = 0 := by
    refine Subtype.ext (funext fun z => ?_)
    have hval : ((∑ β : Fin (n + 2) → Fin (m + 1),
        constEntireRing W (a β) * ∏ k, (u k) ^ (β k : ℕ) * (v k) ^ (m - (β k : ℕ))
          : entireSubring W) : W → ℂ) z
        = siegelHomCombination A B m a z := by
      simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul,
        SubmonoidClass.coe_finset_prod, SubmonoidClass.coe_pow, Finset.sum_apply,
        Finset.prod_apply, Pi.mul_apply, Pi.pow_apply, siegelHomCombination, hAdef, hBdef]
      rfl
    rw [hval, hzero z]
    rfl
  -- pass to the field and cancel the denominators
  have hinj : Function.Injective (algebraMap (entireSubring W) (EntireField W)) :=
    IsFractionRing.injective (entireSubring W) (EntireField W)
  have hden : ∀ k, algebraMap (entireSubring W) (EntireField W) (v k) ≠ 0 := by
    intro k hk
    exact hv k (hinj (by rw [hk, map_zero]))
  have hxv : ∀ k, x k * algebraMap (entireSubring W) (EntireField W) (v k)
      = algebraMap (entireSubring W) (EntireField W) (u k) := by
    intro k
    rw [hx k, div_mul_cancel₀ _ (hden k)]
  have hkey : MvPolynomial.aeval x (siegelPoly a)
      * ∏ k, (algebraMap (entireSubring W) (EntireField W) (v k)) ^ m = 0 := by
    have hmapzero : algebraMap (entireSubring W) (EntireField W)
        (∑ β : Fin (n + 2) → Fin (m + 1),
          constEntireRing W (a β) * ∏ k, (u k) ^ (β k : ℕ) * (v k) ^ (m - (β k : ℕ))) = 0 := by
      rw [hXzero, map_zero]
    rw [aeval_siegelPoly, Finset.sum_mul, ← hmapzero, map_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [map_mul, map_prod]
    have hconst : algebraMap (entireSubring W) (EntireField W) (constEntireRing W (a β))
        = algebraMap ℂ (EntireField W) (a β) := rfl
    rw [hconst, mul_assoc]
    congr 1
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_mul, map_pow, map_pow, ← hxv k, mul_pow]
    have hsplit : (algebraMap (entireSubring W) (EntireField W) (v k)) ^ m
        = (algebraMap (entireSubring W) (EntireField W) (v k)) ^ (β k : ℕ)
          * (algebraMap (entireSubring W) (EntireField W) (v k)) ^ (m - (β k : ℕ)) := by
      rw [← pow_add]
      congr 1
      have hle : (β k : ℕ) ≤ m := Nat.lt_succ_iff.mp (β k).2
      omega
    rw [hsplit]
    ring
  have hprodne : (∏ k, (algebraMap (entireSubring W) (EntireField W) (v k)) ^ m) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hden k)
  exact (mul_eq_zero.mp hkey).resolve_right hprodne

end GaloisForLFunctions.HTGeometry
