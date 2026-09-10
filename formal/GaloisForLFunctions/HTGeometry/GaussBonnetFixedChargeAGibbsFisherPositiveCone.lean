import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsFisherCurveFibers

/-! # Fisher fibers on the complete nonnegative two-atom cone
This includes both pure rays and the zero measure, which the positive-slow
chart alone cannot classify. Mixed sources are identified up to positive scale. -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

private theorem shape_zero (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    egbFixedChargeAGibbsCollisionFisherShape x y = 0 ↔ x * y = 0 := by
  unfold egbFixedChargeAGibbsCollisionFisherShape
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · nlinarith
    · have hs : x + y = 0 := by nlinarith [sq_nonneg (x + y)]
      have hz : x = 0 := by linarith
      rw [hz, zero_mul]
  · intro h
    exact Or.inl (by nlinarith)

private theorem positive_coordinates (x y : NNReal) (h : (x : ℝ) * (y : ℝ) ≠ 0) :
    0 < (x : ℝ) ∧ 0 < (y : ℝ) := by
  constructor
  · by_contra! hn
    have hz : (x : ℝ) = 0 := by linarith [x.property]
    exact h (by rw [hz, zero_mul])
  · by_contra! hn
    have hz : (y : ℝ) = 0 := by linarith [y.property]
    exact h (by rw [hz, mul_zero])

private theorem positive_shape_fibers (x y u v : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hu : 0 < u) (hv : 0 < v) :
    egbFixedChargeAGibbsCollisionFisherShape x y = egbFixedChargeAGibbsCollisionFisherShape u v ↔
      x * v = y * u ∨ x * u = y * v := by
  have hxy : (x + y) ^ 2 ≠ 0 := by positivity
  have huv : (u + v) ^ 2 ≠ 0 := by positivity
  unfold egbFixedChargeAGibbsCollisionFisherShape
  rw [div_eq_div_iff hxy huv]
  have hid : x * y * (u + v) ^ 2 - u * v * (x + y) ^ 2 =
      -(x * v - y * u) * (x * u - y * v) := by ring
  constructor
  · intro h
    have hz : (x * v - y * u) * (x * u - y * v) = 0 := by nlinarith [hid]
    rcases mul_eq_zero.mp hz with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · have hz : x * v - y * u = 0 := by linarith
      rw [hz] at hid
      nlinarith [hid]
    · have hz : x * u - y * v = 0 := by linarith
      rw [hz] at hid
      nlinarith [hid]

private theorem positive_pair_fibers (x y u v : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hu : 0 < u) (hv : 0 < v) :
    (egbFixedChargeAGibbsCollisionFisherShape x y = egbFixedChargeAGibbsCollisionFisherShape u v ∧
      egbFixedChargeAGibbsCollisionFisherShape ((4 / 9 : ℝ) * x) ((1 / 36 : ℝ) * y) =
        egbFixedChargeAGibbsCollisionFisherShape ((4 / 9 : ℝ) * u) ((1 / 36 : ℝ) * v)) ↔
      x * v = y * u := by
  rw [positive_shape_fibers x y u v hx hy hu hv,
    positive_shape_fibers _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity)]
  constructor
  · rintro ⟨h, hn⟩
    rcases h with h | h
    · exact h
    · rcases hn with hn | hn
      · nlinarith
      · have hp : 0 < x * u := mul_pos hx hu
        nlinarith
  · intro h
    exact ⟨Or.inl h, Or.inl (by nlinarith)⟩

/-- On the full positive cone, zero Fisher value means at most one atom is occupied. -/
theorem egbFixedChargeAGibbsCollisionFisherShape_nonnegative_zero_iff (x y : NNReal) :
    egbFixedChargeAGibbsCollisionFisherShape x y = 0 ↔ (x : ℝ) * (y : ℝ) = 0 :=
  shape_zero x y x.property y.property

/-- One readout identifies a mixed ray only up to exchanging the relative atom masses; all pure rays coalesce at zero. -/
theorem egbFixedChargeAGibbsCollisionFisherShape_nonnegative_fibers (x y u v : NNReal) :
    egbFixedChargeAGibbsCollisionFisherShape x y = egbFixedChargeAGibbsCollisionFisherShape u v ↔
      ((x : ℝ) * (y : ℝ) = 0 ∧ (u : ℝ) * (v : ℝ) = 0) ∨
      ((x : ℝ) * (y : ℝ) ≠ 0 ∧ (u : ℝ) * (v : ℝ) ≠ 0 ∧
        ((x : ℝ) * (v : ℝ) = (y : ℝ) * (u : ℝ) ∨ (x : ℝ) * (u : ℝ) = (y : ℝ) * (v : ℝ))) := by
  constructor
  · intro h
    by_cases hxy : (x : ℝ) * (y : ℝ) = 0
    · exact Or.inl ⟨hxy, (shape_zero u v u.property v.property).1
        (h.symm.trans ((shape_zero x y x.property y.property).2 hxy))⟩
    · have huv : (u : ℝ) * (v : ℝ) ≠ 0 := by
        intro hz
        exact hxy ((shape_zero x y x.property y.property).1
          (h.trans ((shape_zero u v u.property v.property).2 hz)))
      obtain ⟨hx, hy⟩ := positive_coordinates x y hxy
      obtain ⟨hu, hv⟩ := positive_coordinates u v huv
      exact Or.inr ⟨hxy, huv, (positive_shape_fibers x y u v hx hy hu hv).1 h⟩
  · rintro (⟨hxy, huv⟩ | ⟨hxy, huv, h⟩)
    · rw [(shape_zero x y x.property y.property).2 hxy,
        (shape_zero u v u.property v.property).2 huv]
    · obtain ⟨hx, hy⟩ := positive_coordinates x y hxy
      obtain ⟨hu, hv⟩ := positive_coordinates u v huv
      exact (positive_shape_fibers x y u v hx hy hu hv).2 h

/-- Two successive readouts classify every mixed positive ray exactly; pure rays and the zero source remain one explicit stratum. -/
theorem egbFixedChargeAGibbsCollisionFisherShape_nonnegative_pair_fibers (x y u v : NNReal) :
    (egbFixedChargeAGibbsCollisionFisherShape x y = egbFixedChargeAGibbsCollisionFisherShape u v ∧
      egbFixedChargeAGibbsCollisionFisherShape ((4 / 9 : ℝ) * x) ((1 / 36 : ℝ) * y) =
        egbFixedChargeAGibbsCollisionFisherShape ((4 / 9 : ℝ) * u) ((1 / 36 : ℝ) * v)) ↔
      ((x : ℝ) * (y : ℝ) = 0 ∧ (u : ℝ) * (v : ℝ) = 0) ∨
      ((x : ℝ) * (y : ℝ) ≠ 0 ∧ (u : ℝ) * (v : ℝ) ≠ 0 ∧
        (x : ℝ) * (v : ℝ) = (y : ℝ) * (u : ℝ)) := by
  constructor
  · intro h
    rcases (egbFixedChargeAGibbsCollisionFisherShape_nonnegative_fibers x y u v).1 h.1 with hzero | hmix
    · exact Or.inl hzero
    · obtain ⟨hx, hy⟩ := positive_coordinates x y hmix.1
      obtain ⟨hu, hv⟩ := positive_coordinates u v hmix.2.1
      exact Or.inr ⟨hmix.1, hmix.2.1, (positive_pair_fibers x y u v hx hy hu hv).1 h⟩
  · rintro (⟨hxy, huv⟩ | ⟨hxy, huv, h⟩)
    · constructor
      · rw [(shape_zero x y x.property y.property).2 hxy,
          (shape_zero u v u.property v.property).2 huv]
      · have hxy' : ((4 / 9 : ℝ) * x) * ((1 / 36 : ℝ) * y) = 0 := by nlinarith
        have huv' : ((4 / 9 : ℝ) * u) * ((1 / 36 : ℝ) * v) = 0 := by nlinarith
        rw [(shape_zero _ _ (by positivity) (by positivity)).2 hxy',
          (shape_zero _ _ (by positivity) (by positivity)).2 huv']
    · obtain ⟨hx, hy⟩ := positive_coordinates x y hxy
      obtain ⟨hu, hv⟩ := positive_coordinates u v huv
      exact (positive_pair_fibers x y u v hx hy hu hv).2 h

end
end GaloisForLFunctions.HTGeometry
