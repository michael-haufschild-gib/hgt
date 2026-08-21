import GaloisForLFunctions.HTGeometry.ABHN.RestrictedInvariantSum

/-!
# Direct-sum form of the raw ABHN invariant target

Choosing one place splits the finite-support invariant-sum map.  A local invariant profile is
uniquely the sum of a zero-sum profile and a profile concentrated at the chosen place carrying its
total invariant.  This is target-side infrastructure: it does not assert that the zero-sum part
comes from a global Brauer class.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u

noncomputable section

/-- Put one invariant value at a fixed place. -/
noncomputable def finsuppRatModIntSingleAddHom {ι : Type u} (i : ι) :
    RatModInt →+ (ι →₀ RatModInt) where
  toFun q := Finsupp.single i q
  map_zero' := Finsupp.single_zero i
  map_add' q r := Finsupp.single_add i q r

/-- The global invariant sum of a one-place profile is its assigned value. -/
theorem finsuppRatModIntSum_single {ι : Type u} (i : ι) (q : RatModInt) :
    finsuppRatModIntSumAddHom ι (Finsupp.single i q) = q := by
  change (Finsupp.single i q).sum (fun _ q ↦ q) = q
  exact Finsupp.sum_single_index rfl

/-- The global invariant sum of the additive one-place section is its input. -/
theorem finsuppRatModIntSum_singleAddHom {ι : Type u} (i : ι) (q : RatModInt) :
    finsuppRatModIntSumAddHom ι (finsuppRatModIntSingleAddHom i q) = q :=
  finsuppRatModIntSum_single i q

/-- Separate a finite-support profile into its zero-sum part and its total invariant. -/
noncomputable def finsuppRatModIntSplitToProd {ι : Type u} (i : ι) :
    (ι →₀ RatModInt) →+
      (finsuppRatModIntSumAddHom ι).ker × RatModInt where
  toFun f :=
    (⟨f - finsuppRatModIntSingleAddHom i (finsuppRatModIntSumAddHom ι f), by
        change finsuppRatModIntSumAddHom ι
          (f - finsuppRatModIntSingleAddHom i (finsuppRatModIntSumAddHom ι f)) = 0
        rw [map_sub, finsuppRatModIntSum_singleAddHom]
        exact sub_self _⟩,
      finsuppRatModIntSumAddHom ι f)
  map_zero' := by
    apply Prod.ext
    · apply Subtype.ext
      change 0 - finsuppRatModIntSingleAddHom i (finsuppRatModIntSumAddHom ι 0) = 0
      rw [map_zero, (finsuppRatModIntSingleAddHom i).map_zero]
      exact sub_zero 0
    · exact map_zero _
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      change x + y - finsuppRatModIntSingleAddHom i
          (finsuppRatModIntSumAddHom ι (x + y)) =
        (x - finsuppRatModIntSingleAddHom i (finsuppRatModIntSumAddHom ι x)) +
          (y - finsuppRatModIntSingleAddHom i (finsuppRatModIntSumAddHom ι y))
      rw [map_add, (finsuppRatModIntSingleAddHom i).map_add]
      abel
    · exact map_add _ x y

/-- Reassemble a profile from its zero-sum component and total invariant. -/
noncomputable def finsuppRatModIntSplitFromProd {ι : Type u} (i : ι) :
    (finsuppRatModIntSumAddHom ι).ker × RatModInt →+ (ι →₀ RatModInt) where
  toFun p := p.1 + finsuppRatModIntSingleAddHom i p.2
  map_zero' := by
    change 0 + finsuppRatModIntSingleAddHom i 0 = 0
    rw [(finsuppRatModIntSingleAddHom i).map_zero]
    exact zero_add 0
  map_add' p q := by
    change ↑(p.1 + q.1) + finsuppRatModIntSingleAddHom i (p.2 + q.2) =
      (↑p.1 + finsuppRatModIntSingleAddHom i p.2) +
        (↑q.1 + finsuppRatModIntSingleAddHom i q.2)
    rw [AddSubgroup.coe_add, (finsuppRatModIntSingleAddHom i).map_add]
    abel

/-- **Raw ABHN target splitting.** A finite-support local invariant profile is its zero-sum part
together with its total invariant. -/
noncomputable def finsuppRatModIntSplitEquiv {ι : Type u} (i : ι) :
    (ι →₀ RatModInt) ≃+ (finsuppRatModIntSumAddHom ι).ker × RatModInt :=
  { finsuppRatModIntSplitToProd i with
    invFun := finsuppRatModIntSplitFromProd i
    left_inv := by
      intro f
      change (f - finsuppRatModIntSingleAddHom i (finsuppRatModIntSumAddHom ι f)) +
        finsuppRatModIntSingleAddHom i (finsuppRatModIntSumAddHom ι f) = f
      abel
    right_inv := by
      rintro ⟨f, q⟩
      apply Prod.ext
      · apply Subtype.ext
        change ↑f + finsuppRatModIntSingleAddHom i q -
          finsuppRatModIntSingleAddHom i
            (finsuppRatModIntSumAddHom ι (↑f + finsuppRatModIntSingleAddHom i q)) = ↑f
        rw [map_add, f.property, finsuppRatModIntSum_singleAddHom]
        abel_nf
      · change finsuppRatModIntSumAddHom ι
          (↑f + finsuppRatModIntSingleAddHom i q) = q
        rw [map_add, f.property, finsuppRatModIntSum_singleAddHom]
        exact zero_add q }

/-- The number-field raw invariant target splits at a fixed archimedean witness place. -/
noncomputable def numberFieldFinsuppRatModIntSplitEquiv
    (K : Type u) [Field K] [NumberField K] :
    (NumberFieldPlace K →₀ RatModInt) ≃+
      (finsuppRatModIntSumAddHom (NumberFieldPlace K)).ker × RatModInt :=
  finsuppRatModIntSplitEquiv (witnessPlace K)

/-- The rational-function-field raw invariant target splits at infinity. -/
noncomputable def rationalFunctionFinsuppRatModIntSplitEquiv
    (F : Type u) [Field F] [Finite F] :
    (RationalFunctionPlace F →₀ RatModInt) ≃+
      (finsuppRatModIntSumAddHom (RationalFunctionPlace F)).ker × RatModInt :=
  finsuppRatModIntSplitEquiv RationalFunctionPlace.infinite

end

end GaloisForLFunctions.HTGeometry.ABHN
