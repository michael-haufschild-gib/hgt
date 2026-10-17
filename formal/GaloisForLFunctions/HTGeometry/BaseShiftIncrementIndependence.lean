import GaloisForLFunctions.HTGeometry.ShiftEliminationEngine

/-!
# Independence from additive increments over a difference field

The fixed-field assumption belongs to the coefficient field. The ambient field may contain
nonconstant periodic elements. A nonzero constant charge on the increments must fail to be a
coefficient-field coboundary; this suffices for algebraic independence of the primitives.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial GenericShiftHolder

noncomputable section

theorem eval₂_jetTranslate_baseShift
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (tau : K →+* K) (sigma : L ≃+* L)
    (hbase : ∀ a : K, sigma (algebraMap K L a) = algebraMap K L (tau a))
    {m : ℕ} (rj : ℕ → K) (xj : Fin m → L)
    (hjet : ∀ j, sigma (xj j) = xj j + algebraMap K L (rj (j : ℕ)))
    (P : MvPolynomial (Fin m) K) :
    MvPolynomial.eval₂ (algebraMap K L) xj (jetTranslateGen tau rj m P) =
      sigma (MvPolynomial.eval₂ (algebraMap K L) xj P) := by
  let lhs : MvPolynomial (Fin m) K →+* L :=
    (MvPolynomial.eval₂Hom (algebraMap K L) xj).comp (jetTranslateGen tau rj m)
  let rhs : MvPolynomial (Fin m) K →+* L :=
    sigma.toRingHom.comp (MvPolynomial.eval₂Hom (algebraMap K L) xj)
  have heq : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lhs, rhs, jetTranslate_CGen, hbase]
    · intro j
      simp [lhs, rhs, jetTranslate_XGen, hjet]
  exact RingHom.congr_fun heq P

/-- A finite primitive family is algebraically independent when its increments have no nonzero
constant charge which is a coboundary in the coefficient field. -/
theorem algebraicIndependent_of_baseShiftIncrements
    {K L : Type*} [Field K] [Field L] [Algebra ℂ K] [Algebra K L]
    (tau : K →+* K) (sigma : L ≃+* L)
    (htau : Function.Injective tau)
    (hconst : ∀ c : ℂ, tau (algebraMap ℂ K c) = algebraMap ℂ K c)
    (hfixed : ∀ w : K, tau w = w → ∃ c : ℂ, w = algebraMap ℂ K c)
    (hbase : ∀ a : K, sigma (algebraMap K L a) = algebraMap K L (tau a))
    {m : ℕ} (xj : Fin m → L) (rj : ℕ → K)
    (hjet : ∀ j, sigma (xj j) = xj j + algebraMap K L (rj (j : ℕ)))
    (hcharge : ∀ (w : K) (delta : Fin m → ℂ),
      tau w - w = ∑ j : Fin m, algebraMap ℂ K (delta j) * rj (j : ℕ) →
        ∀ j, delta j = 0) :
    AlgebraicIndependent K xj := by
  rw [algebraicIndependent_iff_injective_aeval]
  intro P Q hPQ
  have hPQ' : MvPolynomial.eval₂ (algebraMap K L) xj P =
      MvPolynomial.eval₂ (algebraMap K L) xj Q := by
    simpa [MvPolynomial.aeval_def] using hPQ
  apply sub_eq_zero.mp
  by_contra hne
  let I : Set (MvPolynomial (Fin m) K) :=
    {G | MvPolynomial.eval₂ (algebraMap K L) xj G = 0}
  have hsub : ∀ G H, G ∈ I → H ∈ I → G - H ∈ I := by
    intro G H hG hH
    change MvPolynomial.eval₂ _ _ G = 0 at hG
    change MvPolynomial.eval₂ _ _ H = 0 at hH
    change MvPolynomial.eval₂ _ _ (G - H) = 0
    simp only [MvPolynomial.eval₂_sub, hG, hH, sub_zero]
  have hsmul : ∀ (k : K) G, G ∈ I → MvPolynomial.C k * G ∈ I := by
    intro k G hG
    change MvPolynomial.eval₂ _ _ G = 0 at hG
    change MvPolynomial.eval₂ _ _ (MvPolynomial.C k * G) = 0
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, hG, mul_zero]
  have hshift : ∀ G, G ∈ I → jetTranslateGen tau rj m G ∈ I := by
    intro G hG
    change MvPolynomial.eval₂ _ _ (jetTranslateGen tau rj m G) = 0
    rw [eval₂_jetTranslate_baseShift tau sigma hbase rj xj hjet G, hG, map_zero]
  have hconstant : ∀ k : K, MvPolynomial.C k ∈ I → k = 0 := by
    intro k hk
    change MvPolynomial.eval₂ _ _ (MvPolynomial.C k) = 0 at hk
    simp only [MvPolynomial.eval₂_C] at hk
    exact (algebraMap K L).injective (hk.trans (map_zero _).symm)
  have hrel : P - Q ∈ I := by
    change MvPolynomial.eval₂ _ _ (P - Q) = 0
    rw [MvPolynomial.eval₂_sub]
    exact sub_eq_zero.mpr hPQ'
  exact no_shift_stable_annihilatorGen tau rj htau hconst (fun hw => hfixed _ hw)
    I hsub hsmul hshift hconstant (fun h => hcharge _ _ h) ⟨P - Q, hrel, hne⟩

end

end GaloisForLFunctions.HTGeometry
