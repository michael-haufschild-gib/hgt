import GaloisForLFunctions.HTGeometry.OscillatorLadderIdentity

/-!
# The ladder boundary term vanishes for a square-integrable solution

The boundary term of the ladder identity is `B = v v′ + ξ v²`.  For a nontrivial square-integrable
solution of `v″ = (ξ² − μ)v` both summands tend to zero: the product because it is nondecreasing and
negative, the moment because nonnegative energy bounds `(ξ² − μ)v²` by `v′²`, which tends to zero.

The potential is even, so the reflected function solves the same equation and the statement at
`−∞` follows by reflection, with `B` picking up a sign.
-/

open Set MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **The boundary term vanishes at `+∞`.** -/
theorem tendsto_oscBoundary_atTop_zero {mu : ℝ} {v v' : ℝ → ℝ} {a : ℝ}
    (ha : 0 < a) (hmu : mu < a ^ 2)
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((x ^ 2 - mu) * v x) x)
    (hnt : ∀ y, v y ≠ 0 ∨ v' y ≠ 0)
    (hint : Integrable (fun x => v x ^ 2)) :
    Tendsto (oscBoundary v v') atTop (𝓝 0) := by
  have hintI : IntegrableOn (fun x => v x ^ 2) (Ici a) volume := hint.integrableOn
  have hneg : ∀ x ∈ Ici a, oscProduct v v' x < 0 :=
    oscProduct_neg_of_integrableOn ha hmu.le hv hv' hnt hintI
  have hE : ∀ x ∈ Ici a, 0 ≤ oscEnergy mu v v' x :=
    oscEnergy_nonneg_of_integrableOn ha hmu hv hv' hintI
  have hP : Tendsto (oscProduct v v') atTop (𝓝 0) :=
    tendsto_oscProduct_zero ha hmu.le le_rfl hv hv' hneg
  have hnz : ∀ x ∈ Ici a, v x ≠ 0 := by
    intro x hx hzero
    have := hneg x hx
    rw [oscProduct, hzero] at this
    simp at this
  have hcv : Continuous v := continuous_of_hasDerivAt hv
  have hv'0 : Tendsto v' atTop (𝓝 0) := by
    rcases sign_const_of_ne_zero hcv hnz with hpos | hnegv
    · exact tendsto_deriv_zero_of_pos ha hmu.le hv hv' hpos hneg
    · have hvv : ∀ x, HasDerivAt (fun y => -v y) ((fun y => -v' y) x) x := fun x => (hv x).neg
      have hvv' : ∀ x, HasDerivAt (fun y => -v' y) ((x ^ 2 - mu) * (fun y => -v y) x) x := by
        intro x
        refine ((hv' x).neg).congr_deriv ?_
        ring
      have hposn : ∀ x ∈ Ici a, 0 < (fun y => -v y) x := by
        intro x hx
        simpa using hnegv x hx
      have hnegn : ∀ x ∈ Ici a, oscProduct (fun y => -v y) (fun y => -v' y) x < 0 := by
        intro x hx
        have := hneg x hx
        rw [oscProduct] at this ⊢
        simpa using this
      have := tendsto_deriv_zero_of_pos ha hmu.le hvv hvv' hposn hnegn
      have hneg0 : Tendsto (fun x => -(-v' x)) atTop (𝓝 (-0)) := this.neg
      simpa using hneg0
  have hmuIci : ∀ x ∈ Ici a, mu ≤ x ^ 2 := by
    intro x hx
    have hax : a ≤ x := Set.mem_Ici.1 hx
    nlinarith
  have hw := tendsto_weighted_sq_zero hE hmuIci hv'0
  have hm := tendsto_mul_sq_zero hw
  have hsum := hP.add hm
  rw [add_zero] at hsum
  exact hsum

/-- The reflected solution's data. -/
theorem oscBoundary_reflect {v v' : ℝ → ℝ} (R : ℝ) :
    oscBoundary (fun t => v (-t)) (fun t => -v' (-t)) R = -oscBoundary v v' (-R) := by
  rw [oscBoundary, oscBoundary, oscProduct, oscProduct]
  ring

/-- **The boundary term vanishes at `−∞`.** -/
theorem tendsto_oscBoundary_atBot_zero {mu : ℝ} {v v' : ℝ → ℝ} {a : ℝ}
    (ha : 0 < a) (hmu : mu < a ^ 2)
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((x ^ 2 - mu) * v x) x)
    (hnt : ∀ y, v y ≠ 0 ∨ v' y ≠ 0)
    (hint : Integrable (fun x => v x ^ 2)) :
    Tendsto (fun R : ℝ => oscBoundary v v' (-R)) atTop (𝓝 0) := by
  obtain ⟨hw, hw'⟩ := hasDerivAt_reflect hv hv'
  have hntw : ∀ y, (fun t => v (-t)) y ≠ 0 ∨ (fun t => -v' (-t)) y ≠ 0 := by
    intro y
    rcases hnt (-y) with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa using h)
  have hintw : Integrable (fun x => (fun t => v (-t)) x ^ 2) := by
    have := hint.comp_neg
    simpa using this
  have hlim := tendsto_oscBoundary_atTop_zero (mu := mu) (a := a) ha hmu hw hw' hntw hintw
  have hlim2 : Tendsto (fun R : ℝ => -oscBoundary v v' (-R)) atTop (𝓝 0) :=
    Filter.Tendsto.congr (fun R => oscBoundary_reflect (v := v) (v' := v') R) hlim
  have := hlim2.neg
  simpa using this

end GaloisForLFunctions.HTGeometry
