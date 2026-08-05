import GaloisForLFunctions.RHTower.FieldOneFiniteStageClassSpace
import GaloisForLFunctions.RHTower.FieldOneFiniteAdeleDiagonalReciprocity

/-!
# Restriction maps of the semilocal sheaf and their Weyl multipliers

For finite sets `S ⊆ T` of finite places the semilocal sheaf restricts sections over the
complement of `S` to sections over the complement of `T`.  On adelic test functions the
restriction extends a function on `A_S` by the indicator of the integral part at the places of
`T` outside `S`.

This module constructs those restriction maps, proves that they compose as a presheaf, and proves
that the Weyl multiplier representation commutes with every one of them: a rational whose
denominator only involves places of `S` is integral at each place of `T` outside `S`, and the
standard local character is trivial on the integers there, so the extra places contribute nothing
to the character.

All statements are unconditional.  No zero of a zeta function, positivity premise, or
Riemann-hypothesis statement enters.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain

attribute [local instance] Classical.propDecidable

variable {S T U : Finset (HeightOneSpectrum ℤ)}

/-- Character contribution of a stage adele at an ambient finite place, zero off the stage. -/
def fieldOneFiniteStageLocalTerm (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageAdele S) (v : HeightOneSpectrum ℤ) : UnitAddCircle :=
  if h : v ∈ S then fieldOneFiniteAdeleLocalUnitCharacter v (x.2 ⟨v, h⟩) else 0

theorem fieldOneFiniteStageLocalTerm_add (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageAdele S) (v : HeightOneSpectrum ℤ) :
    fieldOneFiniteStageLocalTerm S (x + y) v =
      fieldOneFiniteStageLocalTerm S x v + fieldOneFiniteStageLocalTerm S y v := by
  by_cases h : v ∈ S
  · simp only [fieldOneFiniteStageLocalTerm, dif_pos h]
    exact map_add _ _ _
  · simp only [fieldOneFiniteStageLocalTerm, dif_neg h, add_zero]

/-- Additive-circle character of the stage adele ring `A_S`, with the archimedean sign matching
the semilocal convention. -/
def fieldOneFiniteStageUnitCharacter (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageAdele S →+ UnitAddCircle where
  toFun x :=
    -((x.1 : ℝ) : UnitAddCircle) + ∑ v ∈ S, fieldOneFiniteStageLocalTerm S x v
  map_zero' := by
    have hterm : ∀ v ∈ S,
        fieldOneFiniteStageLocalTerm S (0 : FieldOneFiniteStageAdele S) v = 0 := by
      intro v _
      by_cases h : v ∈ S
      · simp only [fieldOneFiniteStageLocalTerm, dif_pos h]
        exact map_zero _
      · simp only [fieldOneFiniteStageLocalTerm, dif_neg h]
    simp [Finset.sum_congr rfl hterm]
  map_add' x y := by
    show -(((x + y).1 : ℝ) : UnitAddCircle) +
        ∑ v ∈ S, fieldOneFiniteStageLocalTerm S (x + y) v =
      (-((x.1 : ℝ) : UnitAddCircle) + ∑ v ∈ S, fieldOneFiniteStageLocalTerm S x v) +
        (-((y.1 : ℝ) : UnitAddCircle) + ∑ v ∈ S, fieldOneFiniteStageLocalTerm S y v)
    rw [Finset.sum_congr rfl (fun v _ => fieldOneFiniteStageLocalTerm_add S x y v),
      Finset.sum_add_distrib,
      show (((x + y).1 : ℝ) : UnitAddCircle) =
        ((x.1 : ℝ) : UnitAddCircle) + ((y.1 : ℝ) : UnitAddCircle) from rfl]
    abel

/-- Coordinate projection `A_T → A_S` attached to an inclusion `S ⊆ T` of stages. -/
def fieldOneFiniteStageProjection (h : S ⊆ T) (x : FieldOneFiniteStageAdele T) :
    FieldOneFiniteStageAdele S :=
  (x.1, fun v => x.2 ⟨v.1, h v.2⟩)

theorem fieldOneFiniteStageProjection_comp (hST : S ⊆ T) (hTU : T ⊆ U)
    (x : FieldOneFiniteStageAdele U) :
    fieldOneFiniteStageProjection hST (fieldOneFiniteStageProjection hTU x) =
      fieldOneFiniteStageProjection (hST.trans hTU) x :=
  rfl

theorem fieldOneFiniteStageLocalTerm_projection (h : S ⊆ T)
    (x : FieldOneFiniteStageAdele T) {v : HeightOneSpectrum ℤ} (hv : v ∈ S) :
    fieldOneFiniteStageLocalTerm S (fieldOneFiniteStageProjection h x) v =
      fieldOneFiniteStageLocalTerm T x v := by
  simp only [fieldOneFiniteStageLocalTerm, dif_pos hv, dif_pos (h hv)]
  rfl

theorem fieldOneFiniteStageUnitCharacter_projection (h : S ⊆ T)
    {x : FieldOneFiniteStageAdele T}
    (hvanish : ∀ v ∈ T, v ∉ S → fieldOneFiniteStageLocalTerm T x v = 0) :
    fieldOneFiniteStageUnitCharacter S (fieldOneFiniteStageProjection h x) =
      fieldOneFiniteStageUnitCharacter T x := by
  show -((x.1 : ℝ) : UnitAddCircle) +
      ∑ v ∈ S, fieldOneFiniteStageLocalTerm S (fieldOneFiniteStageProjection h x) v =
    -((x.1 : ℝ) : UnitAddCircle) + ∑ v ∈ T, fieldOneFiniteStageLocalTerm T x v
  congr 1
  rw [Finset.sum_congr rfl (fun v hv => fieldOneFiniteStageLocalTerm_projection h x hv)]
  exact Finset.sum_subset h hvanish

/-- Diagonal rational scaling of a stage adele. -/
def fieldOneFiniteStageSMul (S : Finset (HeightOneSpectrum ℤ)) (a : ℚ)
    (x : FieldOneFiniteStageAdele S) : FieldOneFiniteStageAdele S :=
  ((a : ℝ) * x.1, fun v => algebraMap ℚ (v.1.adicCompletion ℚ) a * x.2 v)

theorem fieldOneFiniteStageSMul_projection (h : S ⊆ T) (a : ℚ)
    (x : FieldOneFiniteStageAdele T) :
    fieldOneFiniteStageSMul S a (fieldOneFiniteStageProjection h x) =
      fieldOneFiniteStageProjection h (fieldOneFiniteStageSMul T a x) :=
  rfl

theorem fieldOneFiniteStageSMul_add (S : Finset (HeightOneSpectrum ℤ)) (a b : ℚ)
    (x : FieldOneFiniteStageAdele S) :
    fieldOneFiniteStageSMul S (a + b) x =
      fieldOneFiniteStageSMul S a x + fieldOneFiniteStageSMul S b x := by
  refine Prod.ext ?_ ?_
  · show ((a + b : ℚ) : ℝ) * x.1 = (a : ℝ) * x.1 + (b : ℝ) * x.1
    push_cast
    ring
  · funext v
    show algebraMap ℚ (v.1.adicCompletion ℚ) (a + b) * x.2 v =
      algebraMap ℚ (v.1.adicCompletion ℚ) a * x.2 v +
        algebraMap ℚ (v.1.adicCompletion ℚ) b * x.2 v
    rw [map_add]
    ring

theorem fieldOneFiniteStageSMul_zero (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageAdele S) :
    fieldOneFiniteStageSMul S 0 x = 0 := by
  refine Prod.ext ?_ ?_
  · show ((0 : ℚ) : ℝ) * x.1 = 0
    simp
  · funext v
    show algebraMap ℚ (v.1.adicCompletion ℚ) 0 * x.2 v = 0
    simp

/-- Weyl multiplier at a stage: multiplication by the character of the diagonal rational
scaling. -/
def fieldOneFiniteStageWeyl (S : Finset (HeightOneSpectrum ℤ)) (a : ℚ)
    (f : FieldOneFiniteStageAdele S → ℂ) : FieldOneFiniteStageAdele S → ℂ :=
  fun x =>
    (AddCircle.toCircle
      (fieldOneFiniteStageUnitCharacter S (fieldOneFiniteStageSMul S a x)) : ℂ) * f x

theorem fieldOneFiniteStageWeyl_zero (S : Finset (HeightOneSpectrum ℤ))
    (f : FieldOneFiniteStageAdele S → ℂ) :
    fieldOneFiniteStageWeyl S 0 f = f := by
  funext x
  show (AddCircle.toCircle
    (fieldOneFiniteStageUnitCharacter S (fieldOneFiniteStageSMul S 0 x)) : ℂ) * f x = f x
  rw [fieldOneFiniteStageSMul_zero, map_zero, AddCircle.toCircle_zero]
  simp

theorem fieldOneFiniteStageWeyl_add (S : Finset (HeightOneSpectrum ℤ)) (a b : ℚ)
    (f : FieldOneFiniteStageAdele S → ℂ) :
    fieldOneFiniteStageWeyl S a (fieldOneFiniteStageWeyl S b f) =
      fieldOneFiniteStageWeyl S (a + b) f := by
  funext x
  show (AddCircle.toCircle
      (fieldOneFiniteStageUnitCharacter S (fieldOneFiniteStageSMul S a x)) : ℂ) *
      ((AddCircle.toCircle
        (fieldOneFiniteStageUnitCharacter S (fieldOneFiniteStageSMul S b x)) : ℂ) * f x) =
    (AddCircle.toCircle
      (fieldOneFiniteStageUnitCharacter S (fieldOneFiniteStageSMul S (a + b) x)) : ℂ) * f x
  rw [fieldOneFiniteStageSMul_add, map_add, AddCircle.toCircle_add]
  push_cast
  ring

/-- Locus in `A_T` that is integral at every place of `T` outside `S`. -/
def fieldOneFiniteStageOuterIntegral (_h : S ⊆ T) : Set (FieldOneFiniteStageAdele T) :=
  {x | ∀ v : ↥T, v.1 ∉ S → x.2 v ∈ v.1.adicCompletionIntegers ℚ}

/-- Restriction of a section of the semilocal sheaf along `S ⊆ T`: extend by the indicator of the
integral part at the places of `T` outside `S`. -/
def fieldOneFiniteStageRestrict (h : S ⊆ T) (f : FieldOneFiniteStageAdele S → ℂ) :
    FieldOneFiniteStageAdele T → ℂ :=
  fun x =>
    if x ∈ fieldOneFiniteStageOuterIntegral h then f (fieldOneFiniteStageProjection h x) else 0

theorem fieldOneFiniteStageRestrict_self (f : FieldOneFiniteStageAdele S → ℂ) :
    fieldOneFiniteStageRestrict (le_refl S) f = f := by
  classical
  funext x
  have hx : x ∈ fieldOneFiniteStageOuterIntegral (le_refl S) := by
    intro v hv
    exact absurd v.2 hv
  simp only [fieldOneFiniteStageRestrict, if_pos hx]
  rfl

theorem fieldOneFiniteStageOuterIntegral_comp (hST : S ⊆ T) (hTU : T ⊆ U)
    (x : FieldOneFiniteStageAdele U) :
    (x ∈ fieldOneFiniteStageOuterIntegral (hST.trans hTU) ↔
      x ∈ fieldOneFiniteStageOuterIntegral hTU ∧
        fieldOneFiniteStageProjection hTU x ∈ fieldOneFiniteStageOuterIntegral hST) := by
  constructor
  · intro hx
    refine ⟨fun v hv => hx v (fun hvS => hv (hST hvS)), fun v hv => ?_⟩
    exact hx ⟨v.1, hTU v.2⟩ hv
  · rintro ⟨h1, h2⟩ v hv
    by_cases hvT : v.1 ∈ T
    · exact h2 ⟨v.1, hvT⟩ hv
    · exact h1 v hvT

theorem fieldOneFiniteStageRestrict_comp (hST : S ⊆ T) (hTU : T ⊆ U)
    (f : FieldOneFiniteStageAdele S → ℂ) :
    fieldOneFiniteStageRestrict hTU (fieldOneFiniteStageRestrict hST f) =
      fieldOneFiniteStageRestrict (hST.trans hTU) f := by
  classical
  funext x
  by_cases hx : x ∈ fieldOneFiniteStageOuterIntegral (hST.trans hTU)
  · obtain ⟨h1, h2⟩ := (fieldOneFiniteStageOuterIntegral_comp hST hTU x).mp hx
    simp only [fieldOneFiniteStageRestrict, if_pos hx, if_pos h1, if_pos h2]
    rw [fieldOneFiniteStageProjection_comp]
  · have hnot : ¬ (x ∈ fieldOneFiniteStageOuterIntegral hTU ∧
        fieldOneFiniteStageProjection hTU x ∈ fieldOneFiniteStageOuterIntegral hST) :=
      fun hc => hx ((fieldOneFiniteStageOuterIntegral_comp hST hTU x).mpr hc)
    simp only [fieldOneFiniteStageRestrict, if_neg hx]
    by_cases h1 : x ∈ fieldOneFiniteStageOuterIntegral hTU
    · have h2 : ¬ fieldOneFiniteStageProjection hTU x ∈
          fieldOneFiniteStageOuterIntegral hST := fun hc => hnot ⟨h1, hc⟩
      simp only [if_pos h1, if_neg h2]
    · simp only [if_neg h1]

/-- **Restriction compatibility of the Weyl multiplier representation.** If the diagonal rational
`a` is integral at every place of `T` outside `S`, then the Weyl multiplier at stage `S` and the
Weyl multiplier at stage `T` agree through the restriction map. -/
theorem fieldOneFiniteStageRestrict_weyl (h : S ⊆ T) (a : ℚ)
    (hint : ∀ v : HeightOneSpectrum ℤ, v ∈ T → v ∉ S →
      algebraMap ℚ (v.adicCompletion ℚ) a ∈ v.adicCompletionIntegers ℚ)
    (f : FieldOneFiniteStageAdele S → ℂ) :
    fieldOneFiniteStageRestrict h (fieldOneFiniteStageWeyl S a f) =
      fieldOneFiniteStageWeyl T a (fieldOneFiniteStageRestrict h f) := by
  classical
  funext x
  by_cases hx : x ∈ fieldOneFiniteStageOuterIntegral h
  · have hchar :
        fieldOneFiniteStageUnitCharacter S
            (fieldOneFiniteStageSMul S a (fieldOneFiniteStageProjection h x)) =
          fieldOneFiniteStageUnitCharacter T (fieldOneFiniteStageSMul T a x) := by
      rw [fieldOneFiniteStageSMul_projection]
      refine fieldOneFiniteStageUnitCharacter_projection h ?_
      intro v hvT hvS
      simp only [fieldOneFiniteStageLocalTerm, dif_pos hvT]
      refine fieldOneFiniteAdeleLocalUnitCharacter_vanishes_on_integers v ?_
      exact Subring.mul_mem _ (hint v hvT hvS) (hx ⟨v, hvT⟩ hvS)
    simp only [fieldOneFiniteStageRestrict, if_pos hx, fieldOneFiniteStageWeyl, hchar]
  · simp only [fieldOneFiniteStageRestrict, if_neg hx, fieldOneFiniteStageWeyl, mul_zero]

/-- **The sheaf hypothesis of the card holds for every rational with denominator inside the
stage.** A rational `m / p^n` whose prime `p` is a place of `S` is integral at every place of `T`
outside `S`, so its Weyl multiplier commutes with the restriction map. -/
theorem fieldOneFiniteStageRestrict_weyl_int_div_pow (h : S ⊆ T)
    {v₀ : HeightOneSpectrum ℤ} (hv₀ : v₀ ∈ S) (m : ℤ) (n : ℕ)
    (f : FieldOneFiniteStageAdele S → ℂ) :
    fieldOneFiniteStageRestrict h
        (fieldOneFiniteStageWeyl S
          ((m : ℚ) / (Rat.HeightOneSpectrum.primesEquiv v₀ : ℚ) ^ n) f) =
      fieldOneFiniteStageWeyl T
        ((m : ℚ) / (Rat.HeightOneSpectrum.primesEquiv v₀ : ℚ) ^ n)
        (fieldOneFiniteStageRestrict h f) := by
  refine fieldOneFiniteStageRestrict_weyl h _ ?_ f
  intro v _ hvS
  refine fieldOneFiniteAdele_algebraMap_int_div_pow_mem_integers_of_ne ?_ m n
  intro hvv
  exact hvS (hvv ▸ hv₀)

end

end GaloisForLFunctions.RHTower
