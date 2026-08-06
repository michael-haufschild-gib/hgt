import GaloisForLFunctions.HTGeometry.MultipleSineNormalizedSource

/-!
# The exact double-sine difference equation

For a two-period frame the multiple-sine source, corrected by an explicit rational function,
satisfies the double-sine functional equation exactly:

```text
(T_1 - 1) M = -(π/ω_2) cot(π z/ω_2),
(T_2 - 1) M = -(π/ω_1) cot(π z/ω_1) + b,
```

with `b` a constant.  The rational correction is `ρ + p`, where `ρ = 1/z - 1/(z - (ω_1 + ω_2))`
cancels every pole of the accumulated ladder defect and `p` is a polynomial produced by discrete
integration of the remaining polynomial defect in the first direction.

In the second direction the remaining defect is a polynomial killed by the first shift difference,
because the two translations commute and the cotangent of a period is invariant under that period;
hence it is a constant.  A constant increment is exactly what the cotangent-model character
obstruction tolerates, so this is the hypothesis of the double-sine atomic theorem.
-/

open Filter Set Topology Complex Polynomial
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem erase_eq_singleton_of_card_two {S : Finset ι} {k j : ι} (hk : k ∈ S) (hj : j ∈ S)
    (hkj : k ≠ j) (hcard : S.card = 2) : S.erase k = ({j} : Finset ι) := by
  have hcard' : (S.erase k).card = 1 := by
    rw [Finset.card_erase_of_mem hk, hcard]
  have hjmem : j ∈ S.erase k := Finset.mem_erase.mpr ⟨hkj.symm, hj⟩
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hjmem, fun x hx => ?_⟩
  exact Finset.card_le_one.mp (le_of_eq hcard') x hx j hjmem

theorem ratMero_injective : Function.Injective (ratMero : RatFunc ℂ → meroField (Set.univ : Set ℂ)) :=
  RingHom.injective _

/-- The shift difference of an embedded polynomial. -/
theorem shiftDiff_ratMero_polynomial (a : ℂ) (p : Polynomial ℂ) :
    addTranslationMeroEquiv a (ratMero (algebraMap (Polynomial ℂ) (RatFunc ℂ) p))
        - ratMero (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
      = ratMero (algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (p.comp (Polynomial.X + Polynomial.C a) - p)) := by
  rw [addTranslationMeroEquiv_ratfuncToMero_by, ratShiftBy_algebraMap, ← map_sub, ← map_sub]

/-- **The exact double-sine difference equation.**  For a two-period frame there is a rational
correction after which the multiple-sine source satisfies the double-sine functional equation with
cotangent right-hand sides, exactly in the first direction and up to a constant in the second. -/
theorem exists_exact_doubleSine_source (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im)
    (S : Finset ι) (k j : ι) (hk : k ∈ S) (hj : j ∈ S) (hkj : k ≠ j) (hcard : S.card = 2)
    (hS : S.Nonempty) :
    ∃ (r : RatFunc ℂ) (b : ℂ),
      addTranslationMeroEquiv (ω k) (frameSourceMero ω hω S hS + ratMero r)
          - (frameSourceMero ω hω S hS + ratMero r) = -periodCotMero (ω j) ∧
      addTranslationMeroEquiv (ω j) (frameSourceMero ω hω S hS + ratMero r)
          - (frameSourceMero ω hω S hS + ratMero r)
        = -periodCotMero (ω k) + ratMero (RatFunc.C b) := by
  classical
  have hωk : ω k ≠ 0 := by
    intro hcon
    have := hω k
    rw [hcon] at this
    simp at this
  have hωj : ω j ≠ 0 := by
    intro hcon
    have := hω j
    rw [hcon] at this
    simp at this
  have herase_k : S.erase k = ({j} : Finset ι) :=
    erase_eq_singleton_of_card_two hk hj hkj hcard
  have herase_j : S.erase j = ({k} : Finset ι) :=
    erase_eq_singleton_of_card_two hj hk (Ne.symm hkj) hcard
  set Qk : Polynomial ℂ := normalizedRemainder ω S k j hk with hQk
  set Qj : Polynomial ℂ := normalizedRemainder ω S j k hj with hQj
  obtain ⟨p, hp⟩ := exists_shiftDiff_eq hωk (-Qk)
  set ρ : RatFunc ℂ := normalizationRat (ω k + ω j) with hρ
  set r : RatFunc ℂ := ρ + algebraMap (Polynomial ℂ) (RatFunc ℂ) p with hr
  set M : meroField (Set.univ : Set ℂ) := frameSourceMero ω hω S hS + ratMero r with hM
  -- the two normalized shift differences
  have hstepk := normalizedSource_shiftDiff ω hω S k j hk herase_k hcard hS
  have hstepj := normalizedSource_shiftDiff ω hω S j k hj herase_j hcard hS
  rw [show ω j + ω k = ω k + ω j from add_comm _ _] at hstepj
  rw [← hρ, ← hQk] at hstepk
  rw [← hρ, ← hQj] at hstepj
  -- the polynomial part
  have hpolyk := shiftDiff_ratMero_polynomial (ω k) p
  have hpolyj := shiftDiff_ratMero_polynomial (ω j) p
  rw [hp] at hpolyk
  -- the first direction is exact
  have hdirk : addTranslationMeroEquiv (ω k) M - M = -periodCotMero (ω j) := by
    rw [hM, hr]
    have hsplit : frameSourceMero ω hω S hS + ratMero (ρ + algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
        = (frameSourceMero ω hω S hS + ratMero ρ)
          + ratMero (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) := by
      rw [map_add]
      ring
    rw [hsplit, map_add]
    have hzero : ratMero (algebraMap (Polynomial ℂ) (RatFunc ℂ) Qk)
        + ratMero (algebraMap (Polynomial ℂ) (RatFunc ℂ) (-Qk)) = 0 := by
      rw [← map_add, ← map_add, add_neg_cancel, map_zero, map_zero]
    linear_combination hstepk + hpolyk + hzero
  -- the second direction has a polynomial defect
  set B : Polynomial ℂ := Qj + (p.comp (Polynomial.X + Polynomial.C (ω j)) - p) with hB
  have hdirj : addTranslationMeroEquiv (ω j) M - M
      = -periodCotMero (ω k) + ratMero (algebraMap (Polynomial ℂ) (RatFunc ℂ) B) := by
    have hsplitM : M = (frameSourceMero ω hω S hS + ratMero ρ)
        + ratMero (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) := by
      rw [hM, hr, map_add]
      ring
    have hBsplit : ratMero (algebraMap (Polynomial ℂ) (RatFunc ℂ) B)
        = ratMero (algebraMap (Polynomial ℂ) (RatFunc ℂ) Qj)
          + ratMero (algebraMap (Polynomial ℂ) (RatFunc ℂ)
              (p.comp (Polynomial.X + Polynomial.C (ω j)) - p)) := by
      rw [hB, map_add, map_add]
    rw [hsplitM, map_add, hBsplit]
    linear_combination hstepj + hpolyj
  -- the polynomial defect is constant
  have hcomm : addTranslationMeroEquiv (ω k) (addTranslationMeroEquiv (ω j) M)
      = addTranslationMeroEquiv (ω j) (addTranslationMeroEquiv (ω k) M) :=
    addTranslationMeroEquiv_comm _ _ _
  have hcock : addTranslationMeroEquiv (ω j) (addTranslationMeroEquiv (ω k) M - M)
      - (addTranslationMeroEquiv (ω k) M - M) = 0 := by
    rw [hdirk, map_neg, addTranslationMeroEquiv_periodCotMero hωj]
    ring
  have hcocj : addTranslationMeroEquiv (ω k) (addTranslationMeroEquiv (ω j) M - M)
      - (addTranslationMeroEquiv (ω j) M - M)
      = ratMero (algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (B.comp (Polynomial.X + Polynomial.C (ω k)) - B)) := by
    rw [hdirj, map_add, map_neg, addTranslationMeroEquiv_periodCotMero hωk,
      ← shiftDiff_ratMero_polynomial (ω k) B]
    ring
  have hequal : addTranslationMeroEquiv (ω k) (addTranslationMeroEquiv (ω j) M - M)
      - (addTranslationMeroEquiv (ω j) M - M)
      = addTranslationMeroEquiv (ω j) (addTranslationMeroEquiv (ω k) M - M)
        - (addTranslationMeroEquiv (ω k) M - M) := by
    rw [map_sub, map_sub, hcomm]
    ring
  have hBzero : B.comp (Polynomial.X + Polynomial.C (ω k)) - B = 0 := by
    refine RatFunc.algebraMap_injective ℂ ?_
    refine ratMero_injective ?_
    rw [← hcocj, hequal, hcock, map_zero, map_zero]
  have hBconst : B = Polynomial.C (B.eval 0) := by
    refine eq_C_of_shiftDiff_eq_zero hωk ?_
    exact sub_eq_zero.mp hBzero
  have hBrat : algebraMap (Polynomial ℂ) (RatFunc ℂ) B = RatFunc.C (B.eval 0) := by
    conv_lhs => rw [hBconst]
    exact RatFunc.algebraMap_C _
  refine ⟨r, B.eval 0, hdirk, ?_⟩
  rw [hdirj, hBrat]

end

end GaloisForLFunctions.HTGeometry
