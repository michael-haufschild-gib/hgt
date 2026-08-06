import GaloisForLFunctions.HTGeometry.DilatedCotModelOrbitObstruction

/-!
# A constant character of a separated orbit family is not a coboundary

The differential character of a family of translates of a source is, in the cylinder coordinate, a
finite constant combination of cylinder jets of dilated cotangent models.  Grouping the combination
by translate turns it into a sum of dilated Euler-operator combinations, one per translate, and the
top jet index of the whole character singles out a translate whose combination has a nonzero
leading coefficient.

When the translates lie in distinct classes — that is, when their dilation factors lie on distinct
multiplicative orbits — the separated obstruction applies to that translate, so no nonzero constant
character of the family is a `q`-difference.

This is the character form of the defect-coset mechanism: it is what the arbitrary-family
differential criterion consumes.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K]

noncomputable section

/-! ### Constants, dilations and iterated cylinder derivations -/

theorem ratFuncScale_algebraMap_base (q : K) (hq : q ≠ 0) (x : K) :
    ratFuncScale q hq (algebraMap K (RatFunc K) x) = algebraMap K (RatFunc K) x := by
  rw [algebraMap_ratFunc_eq_polynomialC, ratFuncScale_algebraMap, polyScale_eq_comp,
    Polynomial.C_comp]

theorem ratFuncEulerOp_const_mul (x : K) (y : RatFunc K) :
    ratFuncEulerOp (algebraMap K (RatFunc K) x * y)
      = algebraMap K (RatFunc K) x * ratFuncEulerOp y := by
  have hD : ratFuncDerivative K (algebraMap K (RatFunc K) x * y)
      = algebraMap K (RatFunc K) x * ratFuncDerivative K y := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, Derivation.map_algebraMap]
    ring
  rw [ratFuncEulerOp, ratFuncEulerOp, hD]
  ring

theorem cylDeriv_iterate_eq (lam : K) (n : ℕ) (y : RatFunc K) :
    (cylDeriv lam)^[n] y
      = algebraMap K (RatFunc K) (lam ^ n) * ratFuncEulerOp^[n] y := by
  induction n generalizing y with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, cylDeriv,
        ratFuncEulerOp_const_mul, map_pow, map_pow]
      ring

/-! ### The grouped character -/

/-- **A nonzero constant character of a separated family of dilated cotangent models is not a
`q`-difference.**  Grouping the character by translate exhibits it as a sum of dilated
Euler-operator combinations; the translate carrying the top jet index has a nonzero leading
coefficient, and its pole orbit is disjoint from the others. -/
theorem not_dilationTelescoped_constantCharacter_separated [CharZero K]
    (q : K) (hq : q ≠ 0) (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1)
    {lam c₀ : K} (hlam : lam ≠ 0) (hc₀ : c₀ ≠ 0)
    {κ : Type*} [DecidableEq κ] (σ : κ → K) (hσ : ∀ i, σ i ≠ 0)
    (hsep : ∀ i j : κ, i ≠ j → ∀ n : ℤ, (σ i)⁻¹ * q ^ n ≠ (σ j)⁻¹)
    (γ : (κ × ℕ) →₀ K) (hγ : γ ≠ 0) (k : RatFunc K) :
    ratFuncScale q hq k - k
      ≠ ∑ p ∈ γ.support, algebraMap K (RatFunc K) (γ p) *
          ratFuncScale (σ p.1) (hσ p.1) ((cylDeriv lam)^[p.2] (cotModel c₀)) := by
  classical
  obtain ⟨p₀, hp₀mem, hp₀max⟩ :=
    γ.support.exists_max_image (fun p => p.2) (Finsupp.support_nonempty_iff.mpr hγ)
  set r : ℕ := p₀.2 with hrdef
  set a : κ → ℕ → K := fun i n => γ (i, n) * lam ^ n with hadef
  set t : Finset κ := γ.support.image Prod.fst with htdef
  have hmem : ∀ p ∈ γ.support, p ∈ t ×ˢ Finset.range (r + 1) := by
    intro p hp
    refine Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hp₀max p hp))
  -- the character, term by term
  have hterm : ∀ p : κ × ℕ,
      algebraMap K (RatFunc K) (γ p) *
          ratFuncScale (σ p.1) (hσ p.1) ((cylDeriv lam)^[p.2] (cotModel c₀))
        = algebraMap K (RatFunc K) (a p.1 p.2) *
          ratFuncScale (σ p.1) (hσ p.1) (ratFuncEulerOp^[p.2] (cotModel c₀)) := by
    intro p
    rw [cylDeriv_iterate_eq, map_mul, ratFuncScale_algebraMap_base, hadef, map_mul]
    ring
  -- the grouped form
  have hgroup : ∑ p ∈ γ.support, algebraMap K (RatFunc K) (γ p) *
        ratFuncScale (σ p.1) (hσ p.1) ((cylDeriv lam)^[p.2] (cotModel c₀))
      = ∑ i ∈ t, ratFuncScale (σ i) (hσ i)
          (eulerCombination (a i) r (cotModel c₀)) := by
    have hsum1 : ∑ p ∈ γ.support, algebraMap K (RatFunc K) (γ p) *
          ratFuncScale (σ p.1) (hσ p.1) ((cylDeriv lam)^[p.2] (cotModel c₀))
        = ∑ p ∈ t ×ˢ Finset.range (r + 1), algebraMap K (RatFunc K) (a p.1 p.2) *
            ratFuncScale (σ p.1) (hσ p.1) (ratFuncEulerOp^[p.2] (cotModel c₀)) := by
      rw [Finset.sum_congr rfl fun p _ => hterm p]
      refine Finset.sum_subset hmem ?_
      intro p _ hnot
      have hzero : γ p = 0 := Finsupp.notMem_support_iff.mp hnot
      rw [hadef]
      simp [hzero]
    rw [hsum1, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [eulerCombination, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    show algebraMap K (RatFunc K) (a i n) *
        ratFuncScale (σ i) (hσ i) (ratFuncEulerOp^[n] (cotModel c₀))
      = ratFuncScale (σ i) (hσ i)
        (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (a i n)) *
          ratFuncEulerOp^[n] (cotModel c₀))
    have hC : ratFuncScale (σ i) (hσ i)
        (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (a i n)))
        = algebraMap K (RatFunc K) (a i n) := by
      rw [← algebraMap_ratFunc_eq_polynomialC, ratFuncScale_algebraMap_base]
    rw [map_mul (ratFuncScale (σ i) (hσ i))
      (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (a i n)))
      (ratFuncEulerOp^[n] (cotModel c₀)), hC]
  rw [hgroup]
  intro hcon
  have hi₀ : p₀.1 ∈ t := Finset.mem_image.mpr ⟨p₀, hp₀mem, rfl⟩
  have har : a p₀.1 r ≠ 0 := by
    rw [hadef]
    refine mul_ne_zero ?_ (pow_ne_zero _ hlam)
    have : γ p₀ ≠ 0 := Finsupp.mem_support_iff.mp hp₀mem
    simpa [hrdef] using this
  refine not_dilationTelescoped_separated_family q hq hqtor t σ hσ a (fun _ => r)
    (fun _ => c₀) hi₀ hc₀ har ?_ ⟨k, hcon.symm⟩
  intro j hj hne n
  exact hsep p₀.1 j (Ne.symm hne) n

end

end GaloisForLFunctions.HTGeometry
