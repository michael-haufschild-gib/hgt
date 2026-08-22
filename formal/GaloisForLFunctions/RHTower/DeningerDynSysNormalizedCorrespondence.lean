/-
Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 1.3
(`t26n`), the correspondence of normalized irreducibles.

"The irreducible polynomials `α ∈ κ₀[t]` with `α(0) = 1` correspond bijectively to the irreducible
polynomials `α̃ ∈ κ₀^perf[t]` with `α̃(0) = 1` via `α = α̃ ^ d`, where `d` is the degree of
inseparability of any zero of `α`."  Both directions are proved here, for an arbitrary purely
inseparable extension `L / F` and an algebraically closed extension `E`:

* reversal turns a normalized irreducible into a monic irreducible
  (`DeningerDynSysNormalizedIrreducible`);
* a monic irreducible is the minimal polynomial of one of its roots `x`, and `x ≠ 0` because the
  polynomial has nonzero constant coefficient;
* `(minpoly F x).map = (minpoly L x) ^ d` (`DeningerDynSysMinpolyPurelyInseparable`);
* reversing back — reversal is multiplicative, hence commutes with powers — gives
  `α.map = β ^ d` with `α = (minpoly F x).reverse` and `β = (minpoly L x).reverse` normalized
  irreducible.

Choosing `x` from a normalized irreducible over `F` gives the forward map, choosing it from one
over `L` gives surjectivity.
-/
import GaloisForLFunctions.RHTower.DeningerDynSysMinpolyPurelyInseparable
import GaloisForLFunctions.RHTower.DeningerDynSysNormalizedIrreducible

namespace RHTower

open Polynomial

variable {F : Type*} [Field F]

theorem deningerReverse_pow (p : Polynomial F) (k : ℕ) :
    (p ^ k).reverse = p.reverse ^ k := by
  induction k with
  | zero => simp [Polynomial.reverse]
  | succ k ih => rw [pow_succ, pow_succ, Polynomial.reverse_mul_of_domain, ih]

/-- The minimal polynomial of a nonzero algebraic element has nonzero constant coefficient. -/
theorem deningerMinpoly_coeff_zero_ne_zero {K M : Type*} [Field K] [Field M] [Algebra K M]
    {x : M} (hx : IsIntegral K x) (hxne : x ≠ 0) : (minpoly K x).coeff 0 ≠ 0 := by
  intro h0
  have hdvd : Polynomial.X ∣ minpoly K x := Polynomial.X_dvd_iff.2 h0
  have hassoc : Associated (Polynomial.X : Polynomial K) (minpoly K x) :=
    Polynomial.irreducible_X.associated_of_dvd (minpoly.irreducible hx) hdvd
  have hXeq : (Polynomial.X : Polynomial K) = minpoly K x :=
    Polynomial.eq_of_monic_of_associated Polynomial.monic_X (minpoly.monic hx) hassoc
  have hev := minpoly.aeval K x
  rw [← hXeq] at hev
  exact hxne (by simpa using hev)

/-- **Deninger, Proposition 1.3 (`t26n`), the correspondence of normalized irreducibles.**  Let
`L / F` be purely inseparable and `E` an algebraically closed extension.  Every irreducible
polynomial `α` over `F` with `α(0) = 1` becomes, over `L`, the `d`-th power of an irreducible
polynomial `β` over `L` with `β(0) = 1`. -/
theorem deningerNormalizedIrreducible_map_eq_pow {L E : Type*} [Field L] [Field E]
    [Algebra F L] [Algebra F E] [Algebra L E] [IsScalarTower F L E]
    [IsPurelyInseparable F L] [IsAlgClosed E] (q : ℕ) [ExpChar F q]
    {α : Polynomial F} (hα0 : α.coeff 0 = 1) (hαirr : Irreducible α) :
    ∃ (d : ℕ) (β : Polynomial L), 0 < d ∧ β.coeff 0 = 1 ∧ Irreducible β ∧
      α.map (algebraMap F L) = β ^ d := by
  have hα0' : α.coeff 0 ≠ 0 := by rw [hα0]; exact one_ne_zero
  have hαne : α ≠ 0 := fun h => hα0' (by rw [h, Polynomial.coeff_zero])
  have hrevmonic : α.reverse.Monic := deningerReverse_monic hα0
  have hrevirr : Irreducible α.reverse := deningerIrreducible_reverse hα0' hαirr
  have hrev0 : α.reverse.coeff 0 ≠ 0 := by
    rw [deningerReverse_coeff_zero]
    exact Polynomial.leadingCoeff_ne_zero.2 hαne
  obtain ⟨x, hx⟩ := deningerExists_minpoly_eq (E := E) hrevmonic hrevirr
  have haeval : (Polynomial.aeval x) α.reverse = 0 := by
    rw [← hx]
    exact minpoly.aeval F x
  have hint : IsIntegral F x := ⟨α.reverse, hrevmonic, haeval⟩
  have hxne : x ≠ 0 := by
    intro h0
    apply hrev0
    rw [← hx, h0, minpoly.zero]
    simp
  have hxL : IsIntegral L x := hint.tower_top
  have hminL0 : (minpoly L x).coeff 0 ≠ 0 := by
    intro h0
    have hdvd : Polynomial.X ∣ minpoly L x := Polynomial.X_dvd_iff.2 h0
    have hassoc : Associated (Polynomial.X : Polynomial L) (minpoly L x) :=
      (Polynomial.irreducible_X).associated_of_dvd (minpoly.irreducible hxL) hdvd
    have hXeq : (Polynomial.X : Polynomial L) = minpoly L x :=
      Polynomial.eq_of_monic_of_associated Polynomial.monic_X (minpoly.monic hxL) hassoc
    have hx0 : x = 0 := by
      have hev := minpoly.aeval L x
      rw [← hXeq] at hev
      simpa using hev
    exact hxne hx0
  obtain ⟨k, hk, heq⟩ := deningerMinpoly_map_eq_pow (F := F) (L := L) (E := E) q x hint
  rw [hx] at heq
  refine ⟨k, (minpoly L x).reverse, hk, ?_, ?_, ?_⟩
  · rw [deningerReverse_coeff_zero]
    exact minpoly.monic hxL
  · exact deningerIrreducible_reverse hminL0 (minpoly.irreducible hxL)
  · have h1 := congrArg Polynomial.reverse heq
    rw [deningerReverse_map (algebraMap F L) (algebraMap F L).injective α.reverse,
      deningerReverse_reverse hα0', deningerReverse_pow] at h1
    exact h1

/-- The correspondence attached to a nonzero algebraic element: the normalized minimal polynomials
over `F` and over `L` are irreducible and related by `α = β ^ d`. -/
theorem deningerNormalizedPair {L E : Type*} [Field L] [Field E]
    [Algebra F L] [Algebra F E] [Algebra L E] [IsScalarTower F L E]
    [IsPurelyInseparable F L] (q : ℕ) [ExpChar F q] {x : E} (hx : IsIntegral F x) (hxne : x ≠ 0) :
    ∃ d : ℕ, 0 < d ∧
      ((minpoly F x).reverse).coeff 0 = 1 ∧ Irreducible ((minpoly F x).reverse) ∧
      ((minpoly L x).reverse).coeff 0 = 1 ∧ Irreducible ((minpoly L x).reverse) ∧
      ((minpoly F x).reverse).map (algebraMap F L) = ((minpoly L x).reverse) ^ d := by
  have hxL : IsIntegral L x := hx.tower_top
  have hF0 : (minpoly F x).coeff 0 ≠ 0 := deningerMinpoly_coeff_zero_ne_zero hx hxne
  have hL0 : (minpoly L x).coeff 0 ≠ 0 := deningerMinpoly_coeff_zero_ne_zero hxL hxne
  obtain ⟨k, hk, heq⟩ := deningerMinpoly_map_eq_pow (F := F) (L := L) (E := E) q x hx
  refine ⟨k, hk, ?_, ?_, ?_, ?_, ?_⟩
  · rw [deningerReverse_coeff_zero]; exact minpoly.monic hx
  · exact deningerIrreducible_reverse hF0 (minpoly.irreducible hx)
  · rw [deningerReverse_coeff_zero]; exact minpoly.monic hxL
  · exact deningerIrreducible_reverse hL0 (minpoly.irreducible hxL)
  · have h1 := congrArg Polynomial.reverse heq
    rw [deningerReverse_map (algebraMap F L) (algebraMap F L).injective (minpoly F x),
      deningerReverse_pow] at h1
    exact h1

/-- **Deninger, Proposition 1.3 (`t26n`), surjectivity of the correspondence.**  Every irreducible
polynomial `β` over `L` with `β(0) = 1` arises from an irreducible polynomial `α` over `F` with
`α(0) = 1` via `α = β ^ d`. -/
theorem deningerNormalizedIrreducible_exists_preimage {L E : Type*} [Field L] [Field E]
    [Algebra F L] [Algebra F E] [Algebra L E] [IsScalarTower F L E]
    [IsPurelyInseparable F L] [IsAlgClosed E] (q : ℕ) [ExpChar F q]
    {β : Polynomial L} (hβ0 : β.coeff 0 = 1) (hβirr : Irreducible β) :
    ∃ (d : ℕ) (α : Polynomial F), 0 < d ∧ α.coeff 0 = 1 ∧ Irreducible α ∧
      α.map (algebraMap F L) = β ^ d := by
  have hβ0' : β.coeff 0 ≠ 0 := by rw [hβ0]; exact one_ne_zero
  have hβne : β ≠ 0 := fun h => hβ0' (by rw [h, Polynomial.coeff_zero])
  have hrevmonic : β.reverse.Monic := deningerReverse_monic hβ0
  have hrevirr : Irreducible β.reverse := deningerIrreducible_reverse hβ0' hβirr
  obtain ⟨x, hx⟩ := deningerExists_minpoly_eq (E := E) hrevmonic hrevirr
  have haeval : (Polynomial.aeval x) β.reverse = 0 := by
    rw [← hx]; exact minpoly.aeval L x
  have hxL : IsIntegral L x := ⟨β.reverse, hrevmonic, haeval⟩
  haveI : Algebra.IsIntegral F L := by
    haveI : Algebra.IsAlgebraic F L := IsPurelyInseparable.isAlgebraic F L
    exact Algebra.IsAlgebraic.isIntegral
  have hxF : IsIntegral F x := isIntegral_trans x hxL
  have hxne : x ≠ 0 := by
    intro h0
    have : β.reverse = Polynomial.X := by rw [← hx, h0, minpoly.zero]
    have hβeq : β = (Polynomial.X : Polynomial L).reverse := by
      rw [← this, deningerReverse_reverse hβ0']
    rw [hβeq] at hβirr
    simp [Polynomial.reverse] at hβirr
  obtain ⟨d, hd, hα0, hαirr, -, -, hmap⟩ := deningerNormalizedPair (L := L) q hxF hxne
  refine ⟨d, (minpoly F x).reverse, hd, hα0, hαirr, ?_⟩
  rw [hmap, hx, deningerReverse_reverse hβ0']

end RHTower
