import GaloisForLFunctions.BiarithmeticGeometry.Affine.UnipotentProjectiveClock

/-!
# Moving destinations of the split Cartan flow

The rank-one destination phenomenon in Cano et al., arXiv:2611.17510,
Proposition 1.1, occurs in the corpus's split diagonal and projective clock.
Sources converging to the repelling line can reach every projective
direction. Explicit nonzero rescalings witness the projective limits.
-/

open Filter Topology Matrix
namespace GaloisForLFunctions.BiarithmeticGeometry
noncomputable section

/-- Projective convergence witnessed in homogeneous coordinates by nonzero rescalings. -/
def IsSplitCartanDestination (source target : Fin 2 → ℝ) : Prop :=
  source ≠ 0 ∧ target ≠ 0 ∧
    ∃ (v w : ℝ → Fin 2 → ℝ) (r : ℝ → ℝ),
      Tendsto v atTop (𝓝 source) ∧ Tendsto w atTop (𝓝 target) ∧
      (∀ t, r t ≠ 0) ∧ (∀ t, v t ≠ 0) ∧
      ∀ t, w t = r t • (splitDiagonal t).mulVec (v t)

private theorem exp_neg_limit :
    Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot

theorem splitDiagonal_mulVec (t a b : ℝ) :
    (splitDiagonal t).mulVec ![a, b] = ![Real.exp t * a, Real.exp (-t) * b] := by
  ext i
  fin_cases i <;> simp [splitDiagonal, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Every finite chart target is reached exactly by a source approaching the repeller. -/
theorem splitCartan_finite_destination (s : ℝ) :
    IsSplitCartanDestination ![0, 1] ![s, 1] := by
  refine ⟨?_, ?_, (fun t => ![s * Real.exp (-t) ^ 2, 1]),
    (fun _ => ![s, 1]), Real.exp, ?_, tendsto_const_nhds,
    Real.exp_ne_zero, ?_, ?_⟩
  · intro h
    have := congrFun h 1
    norm_num at this
  · intro h
    have := congrFun h 1
    norm_num at this
  · apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · change Tendsto (fun t : ℝ => s * Real.exp (-t) ^ 2) atTop (𝓝 0)
      simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero] using
        (exp_neg_limit.pow 2).const_mul s
    · exact tendsto_const_nhds
  · intro t h
    have := congrFun h 1
    norm_num at this
  · intro t
    rw [splitDiagonal_mulVec]
    ext i
    fin_cases i
    · change s = Real.exp t * (Real.exp t * (s * Real.exp (-t) ^ 2))
      rw [Real.exp_neg]
      field_simp [Real.exp_ne_zero]
    · change 1 = Real.exp t * (Real.exp (-t) * 1)
      rw [Real.exp_neg, mul_one, mul_inv_cancel₀ (Real.exp_ne_zero t)]

/-- A slower approach to the repeller reaches the missing infinite chart point. -/
theorem splitCartan_infinite_destination :
    IsSplitCartanDestination ![0, 1] ![1, 0] := by
  refine ⟨?_, ?_, (fun t => ![Real.exp (-t), 1]),
    (fun t => ![1, Real.exp (-t)]), (fun _ => 1), ?_, ?_,
    (fun _ => one_ne_zero), ?_, ?_⟩
  · intro h
    have := congrFun h 1
    norm_num at this
  · intro h
    have := congrFun h 0
    norm_num at this
  · apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · exact exp_neg_limit
    · exact tendsto_const_nhds
  · apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · exact tendsto_const_nhds
    · exact exp_neg_limit
  · intro t h
    have := congrFun h 1
    norm_num at this
  · intro t
    rw [splitDiagonal_mulVec, one_smul]
    simp only [Real.exp_neg, mul_inv_cancel₀ (Real.exp_ne_zero t), mul_one]

/-- Scaling a target preserves its destination whenever the scale is nonzero. -/
theorem splitCartan_destination_scale (source target : Fin 2 → ℝ) (a : ℝ) :
    a = 0 ∨ (IsSplitCartanDestination source target →
      IsSplitCartanDestination source (a • target)) := by
  by_cases ha : a = 0
  · exact Or.inl ha
  right
  rintro ⟨hs, ht, v, w, r, hv, hw, hr, hn, he⟩
  refine ⟨hs, ?_, v, (fun t => a • w t), (fun t => a * r t), hv,
    tendsto_const_nhds.smul hw, (fun t => mul_ne_zero ha (hr t)), hn, ?_⟩
  · exact fun h => ht ((smul_eq_zero.mp h).resolve_left ha)
  · intro t
    change a • w t = (a * r t) • (splitDiagonal t).mulVec (v t)
    rw [he t, mul_smul]

/-- Every nonzero homogeneous target occurs; the zero vector is the sole excluded representative. -/
theorem splitCartan_all_destinations (a b : ℝ) :
    (a = 0 ∧ b = 0) ∨ IsSplitCartanDestination ![0, 1] ![a, b] := by
  by_cases hb : b = 0
  · by_cases ha : a = 0
    · exact Or.inl ⟨ha, hb⟩
    right
    have h := (splitCartan_destination_scale ![0, 1] ![1, 0] a).resolve_left ha
      splitCartan_infinite_destination
    have he : a • (![1, 0] : Fin 2 → ℝ) = ![a, b] := by
      ext i
      fin_cases i <;> simp [hb]
    rw [he] at h
    exact h
  · right
    have h := (splitCartan_destination_scale ![0, 1] ![a / b, 1] b).resolve_left hb
      (splitCartan_finite_destination (a / b))
    have he : b • (![a / b, 1] : Fin 2 → ℝ) = ![a, b] := by
      ext i
      fin_cases i
      · change b * (a / b) = a
        field_simp [hb]
      · simp
    rw [he] at h
    exact h

/-- The same moving source produces the prescribed value in the existing Gauss clock. -/
theorem crossingClock_moving_target (s t : ℝ) :
    crossingClock 0 t (s * Real.exp (-t) ^ 2) = s := by
  simp only [crossingClock, crossingDenominator, zero_mul, sub_zero, Real.exp_neg]
  field_simp [Real.exp_ne_zero]

/-- Vanishing inputs can retain any fixed projective-clock output. -/
theorem crossingClock_vanishing_source (s : ℝ) :
    ∃ u : ℝ → ℝ, Tendsto u atTop (𝓝 0) ∧ ∀ t, crossingClock 0 t (u t) = s := by
  refine ⟨fun t => s * Real.exp (-t) ^ 2, ?_, crossingClock_moving_target s⟩
  simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero] using
    (exp_neg_limit.pow 2).const_mul s

#print axioms splitCartan_all_destinations
#print axioms crossingClock_vanishing_source

end
end GaloisForLFunctions.BiarithmeticGeometry
