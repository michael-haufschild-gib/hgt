import GaloisForLFunctions.HTGeometry.TailQuotientSeparationLaw

/-!
# Anti-Hasse laws for tail quotients

Quotients insensitive to finite modifications exhibit the opposite of finite local-global
separation.  Whenever such a quotient is nontrivial, every erased support, finite coordinate set,
or finite horizon admits two locally identical records representing different global classes.
-/

namespace GaloisForLFunctions.HTGeometry

/-- If a support-saturated quotient is nontrivial, agreement on that local support cannot separate
its global classes. -/
theorem coordinateSupport_hasse_separation_fails
    {I A : Type*} (r : Setoid (I → A)) (E : Set I)
    [DecidablePred (· ∈ E)] (hr : ModificationSaturatedOn r E)
    [Nontrivial (Quotient r)] :
    ∃ u v : I → A,
      CoordinatesAgreeOn E u v ∧ Quotient.mk r u ≠ Quotient.mk r v := by
  obtain ⟨q₁, q₂, hq⟩ := exists_pair_ne (Quotient r)
  obtain ⟨u, rfl⟩ := Quotient.exists_rep q₁
  obtain ⟨v, hvE, hv⟩ :=
    coordinateSupportCylinder_surjective_quotient r E hr u q₂
  refine ⟨u, v, fun i hi => (hvE i hi).symm, ?_⟩
  intro huv
  exact hq (huv.trans hv)

/-- If a finite-modification quotient is nontrivial, agreement on any finite coordinate set cannot
separate its global classes. -/
theorem finiteCoordinate_hasse_separation_fails
    {I A : Type*} [DecidableEq I]
    (r : Setoid (I → A)) (hr : FiniteModificationSaturated r)
    [Nontrivial (Quotient r)] (s : Finset I) :
    ∃ u v : I → A,
      FiniteCoordinatesAgree s u v ∧ Quotient.mk r u ≠ Quotient.mk r v := by
  obtain ⟨q₁, q₂, hq⟩ := exists_pair_ne (Quotient r)
  obtain ⟨u, rfl⟩ := Quotient.exists_rep q₁
  obtain ⟨v, hvs, hv⟩ :=
    finiteCoordinateCylinder_surjective_quotient r hr s u q₂
  refine ⟨u, v, fun i hi => (hvs i hi).symm, ?_⟩
  intro huv
  exact hq (huv.trans hv)

/-- If a tail quotient is nontrivial, agreement through any finite horizon cannot separate its
global classes. -/
theorem finiteHorizon_hasse_separation_fails
    {A : Type*} (r : Setoid (ℕ → A)) (hr : TailSaturated r)
    [Nontrivial (Quotient r)] (N : ℕ) :
    ∃ u v : ℕ → A,
      FinitePrefixAgree N u v ∧ Quotient.mk r u ≠ Quotient.mk r v := by
  obtain ⟨q₁, q₂, hq⟩ := exists_pair_ne (Quotient r)
  obtain ⟨u, rfl⟩ := Quotient.exists_rep q₁
  obtain ⟨v, hvN, hv⟩ := finiteCylinder_surjective_tailQuotient r hr N u q₂
  refine ⟨u, v, fun n hn => (hvN n hn).symm, ?_⟩
  intro huv
  exact hq (huv.trans hv)

end GaloisForLFunctions.HTGeometry
