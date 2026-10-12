import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticLikelihoodLimit

/-! All-order likelihood rigidity and the universally subcritical interpolation interval. -/

open MeasureTheory ProbabilityTheory Set Filter Topology
local notation "E" => EuclideanSpace ℝ (Fin 2)

namespace RHTower

theorem finiteWeilQuadraticLikelihoodFiniteLimit_self
    (s : {s : ℝ // s < 2}) (θ : ℝ) :
    finiteWeilQuadraticLikelihoodFiniteLimit s s θ = 1 := by
  unfold finiteWeilQuadraticLikelihoodFiniteLimit
  simp only [sub_self, mul_zero, add_zero, Real.exp_zero, one_mul]
  rw [div_self (sub_pos.mpr s.property).ne', Real.sqrt_one]

theorem forall_bddAbove_finiteWeilCanonicalQuadraticLikelihood_iff
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2})
    (A B : ℝ) (D : {D : ℝ // A + 2 * B + D < 2}) :
    (∀ θ : ℝ, BddAbove (range (fun r => finiteWeilCanonicalQuadraticLikelihoodMoment
      r (2 * (r + 1) ^ 2 + t r) a b d.val A B D.val θ))) ↔
        a + 2 * b + d.val = A + 2 * B + D.val := by
  constructor
  · intro h
    by_contra hne
    let s := a + 2 * b + d.val
    let S := A + 2 * B + D.val
    have hgap : s - S ≠ 0 := sub_ne_zero.mpr hne
    have hc := (bddAbove_finiteWeilCanonicalQuadraticLikelihood_iff
      t a b d A B D ((2 - s) / (s - S))).mp (h ((2 - s) / (s - S)))
    change s + ((2 - s) / (s - S)) * (s - S) < 2 at hc
    have hcancel : ((2 - s) / (s - S)) * (s - S) = 2 - s := by field_simp [hgap]
    rw [hcancel] at hc
    linarith
  · intro h θ
    apply (bddAbove_finiteWeilCanonicalQuadraticLikelihood_iff t a b d A B D θ).mpr
    rw [h, sub_self, mul_zero, add_zero]
    exact D.property

theorem forall_tendsto_finiteWeilCanonicalQuadraticLikelihood_one_iff
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2})
    (A B : ℝ) (D : {D : ℝ // A + 2 * B + D < 2}) :
    (∀ θ : ℝ, Tendsto (fun r => finiteWeilCanonicalQuadraticLikelihoodMoment
      r (2 * (r + 1) ^ 2 + t r) a b d.val A B D.val θ) atTop (𝓝 1)) ↔
        a + 2 * b + d.val = A + 2 * B + D.val := by
  constructor
  · intro h
    apply (forall_bddAbove_finiteWeilCanonicalQuadraticLikelihood_iff t a b d A B D).mp
    exact fun θ => (h θ).isBoundedUnder_le.bddAbove_range
  · intro h θ
    have hc : (a + 2 * b + d.val) +
        θ * ((a + 2 * b + d.val) - (A + 2 * B + D.val)) < 2 := by
      rw [h, sub_self, mul_zero, add_zero]
      exact D.property
    have hlim := tendsto_finiteWeilCanonicalQuadraticLikelihood_subcritical t a b d A B D ⟨θ, hc⟩
    have hp : (⟨a + 2 * b + d.val, d.property⟩ : {s : ℝ // s < 2}) =
        ⟨A + 2 * B + D.val, D.property⟩ := Subtype.ext h
    have hv : finiteWeilQuadraticLikelihoodFiniteLimit
        ⟨a + 2 * b + d.val, d.property⟩ ⟨A + 2 * B + D.val, D.property⟩ θ = 1 := by
      rw [hp]
      exact finiteWeilQuadraticLikelihoodFiniteLimit_self _ _
    simpa only [hv] using hlim

theorem finiteWeilQuadraticLikelihood_interval_subcritical
    (s S : {s : ℝ // s < 2}) (θ : {θ : ℝ // -1 ≤ θ ∧ θ ≤ 0}) :
    s.val + θ.val * (s.val - S.val) < 2 := by
  by_cases hθ : θ.val = -1
  · rw [hθ]
    nlinarith [S.property]
  · have hp : 0 < 1 + θ.val := by
      by_contra hp
      have he : θ.val = -1 := by linarith [θ.property.1]
      exact hθ he
    have hpos := mul_pos hp (sub_pos.mpr s.property)
    have hnonneg := mul_nonneg (neg_nonneg.mpr θ.property.2) (sub_pos.mpr S.property).le
    nlinarith

theorem tendsto_finiteWeilCanonicalQuadraticLikelihood_interval
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2})
    (A B : ℝ) (D : {D : ℝ // A + 2 * B + D < 2})
    (θ : {θ : ℝ // -1 ≤ θ ∧ θ ≤ 0}) :
    Tendsto (fun r => finiteWeilCanonicalQuadraticLikelihoodMoment
      r (2 * (r + 1) ^ 2 + t r) a b d.val A B D.val θ.val) atTop
      (𝓝 (finiteWeilQuadraticLikelihoodFiniteLimit
        ⟨a + 2 * b + d.val, d.property⟩ ⟨A + 2 * B + D.val, D.property⟩ θ.val)) :=
  tendsto_finiteWeilCanonicalQuadraticLikelihood_subcritical t a b d A B D
    ⟨θ.val, finiteWeilQuadraticLikelihood_interval_subcritical
      ⟨a + 2 * b + d.val, d.property⟩ ⟨A + 2 * B + D.val, D.property⟩ θ⟩

theorem tendsto_finiteWeilCanonicalQuadraticLikelihood_overlap
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2})
    (A B : ℝ) (D : {D : ℝ // A + 2 * B + D < 2}) :
    Tendsto (fun r => ∫ z, Real.sqrt
      (((finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) A B D.val : Measure E).rnDeriv
        (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E) z).toReal)
          ∂(finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E))
      atTop (𝓝 (finiteWeilQuadraticLikelihoodFiniteLimit
        ⟨a + 2 * b + d.val, d.property⟩ ⟨A + 2 * B + D.val, D.property⟩ (-1 / 2))) := by
  have h := tendsto_finiteWeilCanonicalQuadraticLikelihood_interval t a b d A B D
    ⟨-1 / 2, by constructor <;> norm_num⟩
  exact h.congr fun r => finiteWeilCanonicalQuadraticLikelihoodMoment_half_eq_overlap
    r (2 * (r + 1) ^ 2 + t r) a b d.val A B D.val

end RHTower
