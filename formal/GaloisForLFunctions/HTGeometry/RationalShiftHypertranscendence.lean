import GaloisForLFunctions.HTGeometry.RationalIncrementHolderElimination

/-!
# Hypertranscendence from a rational translation increment

This is the field-level Adamczewski--Dreyfus--Hardouin/Hölder bridge needed by the signed Gamma
orbit-charge law.  An element whose complete jet translates by rational increments is
hypertranscendental once no nonzero constant linear combination of those increments is a rational
shift coboundary.
-/

open scoped Differential

namespace GaloisForLFunctions

noncomputable section

open MvPolynomial

theorem eval₂_jetTranslateWith
    {L : Type*} [Field L] [Algebra (RatFunc ℂ) L]
    (sigma : L ≃+* L)
    (hbase : ∀ r : RatFunc ℂ,
      sigma (algebraMap (RatFunc ℂ) L r) =
        algebraMap (RatFunc ℂ) L (ratShift r))
    {m : ℕ} (rj : ℕ → RatFunc ℂ) (xj : Fin m → L)
    (hjet : ∀ j : Fin m,
      sigma (xj j) = xj j + algebraMap (RatFunc ℂ) L (rj (j : ℕ)))
    (P : MvPolynomial (Fin m) (RatFunc ℂ)) :
    MvPolynomial.eval₂ (algebraMap (RatFunc ℂ) L) xj
        (RationalIncrementHolder.jetTranslateWith rj m P) =
      sigma (MvPolynomial.eval₂ (algebraMap (RatFunc ℂ) L) xj P) := by
  let lhs : MvPolynomial (Fin m) (RatFunc ℂ) →+* L :=
    (MvPolynomial.eval₂Hom (algebraMap (RatFunc ℂ) L) xj).comp
      (RationalIncrementHolder.jetTranslateWith rj m)
  let rhs : MvPolynomial (Fin m) (RatFunc ℂ) →+* L :=
    sigma.toRingHom.comp (MvPolynomial.eval₂Hom (algebraMap (RatFunc ℂ) L) xj)
  have heq : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lhs, rhs, RationalIncrementHolder.jetTranslate_CWith, hbase]
    · intro j
      simp [lhs, rhs, RationalIncrementHolder.jetTranslate_XWith, hjet]
  exact RingHom.congr_fun heq P

/-- Every finite initial jet packet is algebraically independent over `ℂ(X)`. -/
theorem algebraicIndependent_rationalShiftJet_prefix
    {L : Type*} [Field L] [Algebra (RatFunc ℂ) L]
    [Differential L]
    (sigma : L ≃+* L)
    (hbase : ∀ r : RatFunc ℂ,
      sigma (algebraMap (RatFunc ℂ) L r) =
        algebraMap (RatFunc ℂ) L (ratShift r))
    (x : L) (rj : ℕ → RatFunc ℂ)
    (hjet : ∀ j : ℕ,
      sigma (differentialJet j x) =
        differentialJet j x + algebraMap (RatFunc ℂ) L (rj j))
    (Hres : ∀ {m : ℕ} {w : RatFunc ℂ} {delta : Fin m → ℂ},
      ratShift w - w =
          ∑ j : Fin m,
            algebraMap ℂ (RatFunc ℂ) (delta j) * rj (j : ℕ) →
      ∀ j, delta j = 0)
    (m : ℕ) :
    AlgebraicIndependent (RatFunc ℂ)
      (fun j : Fin m => differentialJet (j : ℕ) x) := by
  rw [algebraicIndependent_iff_injective_aeval]
  intro P Q hPQ
  have hPQ' : MvPolynomial.eval₂ (algebraMap (RatFunc ℂ) L)
      (fun j : Fin m => differentialJet (j : ℕ) x) P =
      MvPolynomial.eval₂ (algebraMap (RatFunc ℂ) L)
        (fun j : Fin m => differentialJet (j : ℕ) x) Q := by
    simpa [MvPolynomial.aeval_def] using hPQ
  apply sub_eq_zero.mp
  by_contra hne
  let I : Set (MvPolynomial (Fin m) (RatFunc ℂ)) :=
    {G | MvPolynomial.eval₂ (algebraMap (RatFunc ℂ) L)
      (fun j : Fin m => differentialJet (j : ℕ) x) G = 0}
  have hsub : ∀ G H, G ∈ I → H ∈ I → G - H ∈ I := by
    intro G H hG hH
    change MvPolynomial.eval₂ _ _ G = 0 at hG
    change MvPolynomial.eval₂ _ _ H = 0 at hH
    change MvPolynomial.eval₂ _ _ (G - H) = 0
    simpa only [MvPolynomial.eval₂_sub, hG, hH, sub_zero]
  have hsmul : ∀ (k : RatFunc ℂ) G, G ∈ I → MvPolynomial.C k * G ∈ I := by
    intro k G hG
    change MvPolynomial.eval₂ _ _ G = 0 at hG
    change MvPolynomial.eval₂ _ _ (MvPolynomial.C k * G) = 0
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, hG, mul_zero]
  have hshift : ∀ G, G ∈ I →
      RationalIncrementHolder.jetTranslateWith rj m G ∈ I := by
    intro G hG
    change MvPolynomial.eval₂ _ _
      (RationalIncrementHolder.jetTranslateWith rj m G) = 0
    rw [eval₂_jetTranslateWith sigma hbase rj
      (fun j : Fin m => differentialJet (j : ℕ) x)
      (fun j => hjet (j : ℕ)) G, hG, map_zero]
  have hconst : ∀ k : RatFunc ℂ, MvPolynomial.C k ∈ I → k = 0 := by
    intro k hk
    change MvPolynomial.eval₂ _ _ (MvPolynomial.C k) = 0 at hk
    simp only [MvPolynomial.eval₂_C] at hk
    exact (algebraMap (RatFunc ℂ) L).injective (hk.trans (map_zero _).symm)
  have hrel : P - Q ∈ I := by
    change MvPolynomial.eval₂ _ _ (P - Q) = 0
    rw [MvPolynomial.eval₂_sub]
    exact sub_eq_zero.mpr hPQ'
  exact RationalIncrementHolder.no_shift_stable_annihilatorWith rj I
    hsub hsmul hshift hconst Hres ⟨P - Q, hrel, hne⟩

/-- **Rational-shift hypertranscendence criterion.**  Complete rational increment separation
forces the element to be hypertranscendental over `ℂ(X)`. -/
theorem hypertranscendentalOver_of_rationalShiftJets
    {L : Type*} [Field L] [Algebra (RatFunc ℂ) L]
    [Differential L]
    (sigma : L ≃+* L)
    (hbase : ∀ r : RatFunc ℂ,
      sigma (algebraMap (RatFunc ℂ) L r) =
        algebraMap (RatFunc ℂ) L (ratShift r))
    (x : L) (rj : ℕ → RatFunc ℂ)
    (hjet : ∀ j : ℕ,
      sigma (differentialJet j x) =
        differentialJet j x + algebraMap (RatFunc ℂ) L (rj j))
    (Hres : ∀ {m : ℕ} {w : RatFunc ℂ} {delta : Fin m → ℂ},
      ratShift w - w =
          ∑ j : Fin m,
            algebraMap ℂ (RatFunc ℂ) (delta j) * rj (j : ℕ) →
      ∀ j, delta j = 0) :
    HypertranscendentalOver (RatFunc ℂ) x := by
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
  unfold DifferentialIndependent
  apply algebraicIndependent_of_finite_type
  intro t ht
  obtain ⟨N, hN⟩ := ht.bddAbove
  let e : t → Fin (N.2 + 1) := fun p =>
    ⟨p.1.2, Nat.lt_succ_of_le (hN p.2).2⟩
  have he : Function.Injective e := by
    intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · exact Fin.ext_iff.mp hpq
  have hprefix := algebraicIndependent_rationalShiftJet_prefix
    sigma hbase x rj hjet Hres (N.2 + 1)
  have hcomp := hprefix.comp e he
  simpa [e, Function.comp_def] using hcomp

end

end GaloisForLFunctions
