import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsConePureBlindness

/-! # Sharp recovery from total source mass and two Fisher observations -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The total source mass together with the two successive normalized readouts. -/
def egbFixedChargeAGibbsConeMassFisherObservation (x y : NNReal) : ℝ × ℝ × ℝ :=
  ((x : ℝ) + y, egbFixedChargeAGibbsCollisionFisherShape x y,
    egbFixedChargeAGibbsCollisionFisherShape ((4 / 9 : ℝ) * x) ((1 / 36 : ℝ) * y))

/-- The classified mass/Fisher record is exactly the normalized mass and two readings of an actual full-support Gibbs realization. -/
theorem egbFixedChargeAGibbsCone_mass_fisher_observation (n k m : ℕ) (x y : NNReal) :
    (hausdorffMoment (egbFixedChargeAGibbsConeSource x y) 0,
      egbFixedChargeAGibbsCollisionFisherValue n m 1 (egbFixedChargeAGibbsConeEnergy n k m x y),
      egbFixedChargeAGibbsCollisionFisherValue n (m + 1) 1 (egbFixedChargeAGibbsConeEnergy n k m x y)) =
        egbFixedChargeAGibbsConeMassFisherObservation x y := by
  rw [egbFixedChargeAGibbsConeSource_moment, egbFixedChargeAGibbsCone_fisher_formula,
    egbFixedChargeAGibbsCone_fisher_history]
  simp only [pow_zero, pow_one, mul_one]
  rfl

/-- Equal mass and two Fisher readings force equality, except for exchanging the two pure sources of that mass. -/
theorem egbFixedChargeAGibbsCone_mass_fisher_fibers (x y u v : NNReal) :
    egbFixedChargeAGibbsConeMassFisherObservation x y = egbFixedChargeAGibbsConeMassFisherObservation u v ↔
      (x = u ∧ y = v) ∨ (x * y = 0 ∧ x = v ∧ y = u) := by
  unfold egbFixedChargeAGibbsConeMassFisherObservation
  rw [Prod.mk.injEq, Prod.mk.injEq]
  constructor
  · intro h
    rcases (egbFixedChargeAGibbsCollisionFisherShape_nonnegative_pair_fibers x y u v).1 h.2 with hz | hm
    · have hxy := hz.1
      have hxyn : x * y = 0 := Subtype.ext hxy
      rcases mul_eq_zero.mp hxy with hx | hy
      · rcases mul_eq_zero.mp hz.2 with hu | hv
        · exact Or.inl ⟨Subtype.ext (show (x : ℝ) = (u : ℝ) by linarith),
            Subtype.ext (show (y : ℝ) = (v : ℝ) by linarith [h.1])⟩
        · exact Or.inr ⟨hxyn, Subtype.ext (show (x : ℝ) = (v : ℝ) by linarith),
            Subtype.ext (show (y : ℝ) = (u : ℝ) by linarith [h.1])⟩
      · rcases mul_eq_zero.mp hz.2 with hu | hv
        · exact Or.inr ⟨hxyn, Subtype.ext (show (x : ℝ) = (v : ℝ) by linarith [h.1]),
            Subtype.ext (show (y : ℝ) = (u : ℝ) by linarith)⟩
        · exact Or.inl ⟨Subtype.ext (show (x : ℝ) = (u : ℝ) by linarith [h.1]),
            Subtype.ext (show (y : ℝ) = (v : ℝ) by linarith)⟩
    · have hs : 0 < (x : ℝ) + y := by
        by_contra! hn
        have hx : (x : ℝ) = 0 := by linarith [x.property, y.property]
        exact hm.1 (by rw [hx, zero_mul])
      have hp := congrArg (fun z : ℝ => (x : ℝ) * z) h.1
      have hd : ((x : ℝ) - u) * ((x : ℝ) + y) = 0 := by nlinarith [hm.2.2]
      have he : (x : ℝ) = u := by
        rcases mul_eq_zero.mp hd with hd | hd
        · linarith
        · exact False.elim (hs.ne' hd)
      exact Or.inl ⟨Subtype.ext he, Subtype.ext (show (y : ℝ) = (v : ℝ) by linarith [h.1])⟩
  · rintro (⟨rfl, rfl⟩ | ⟨hxy, hxv, hyu⟩)
    · exact ⟨rfl, rfl, rfl⟩
    · subst v
      subst u
      refine ⟨by ring, (egbFixedChargeAGibbsCollisionFisherShape_nonnegative_pair_fibers x y y x).2 ?_⟩
      have hz : (x : ℝ) * y = 0 := congrArg (fun z : NNReal => (z : ℝ)) hxy
      exact Or.inl ⟨hz, by nlinarith⟩

/-- One first source moment removes the only residual ambiguity, including both pure rays and the cone vertex. -/
theorem egbFixedChargeAGibbsCone_mass_fisher_first_moment_complete (x y u v : NNReal) :
    (egbFixedChargeAGibbsConeMassFisherObservation x y = egbFixedChargeAGibbsConeMassFisherObservation u v ∧
      hausdorffMoment (egbFixedChargeAGibbsConeSource x y) 1 =
        hausdorffMoment (egbFixedChargeAGibbsConeSource u v) 1) ↔
      egbFixedChargeAGibbsConeSource x y = egbFixedChargeAGibbsConeSource u v := by
  constructor
  · intro h
    have hmass := congrArg (fun z : ℝ × ℝ × ℝ => z.1) h.1
    change (x : ℝ) + y = (u : ℝ) + v at hmass
    have hmoment := h.2
    rw [egbFixedChargeAGibbsConeSource_moment, egbFixedChargeAGibbsConeSource_moment] at hmoment
    norm_num at hmoment
    have hx : (x : ℝ) = (u : ℝ) := by linarith
    have hy : (y : ℝ) = (v : ℝ) := by linarith
    exact (egbFixedChargeAGibbsConeSource_eq_iff x y u v).2 ⟨Subtype.ext hx, Subtype.ext hy⟩
  · intro h
    obtain ⟨rfl, rfl⟩ := (egbFixedChargeAGibbsConeSource_eq_iff x y u v).1 h
    exact ⟨rfl, rfl⟩

end
end GaloisForLFunctions.HTGeometry
