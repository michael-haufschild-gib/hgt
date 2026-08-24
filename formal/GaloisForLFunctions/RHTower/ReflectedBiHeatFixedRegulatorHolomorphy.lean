import GaloisForLFunctions.RHTower.ReflectedBiHeatThetaResidue
import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy

/-!
# Fixed-regulator holomorphy of the reflected bi-heat sum

At fixed positive real regulator, the complementary orders have constant total real part
`1 + delta`.  The sharp triangular majorant is consequently uniform in the reflection parameter.
Cauchy's estimate upgrades that locally normal convergence to holomorphy on the full reflected
strip.
-/

open Complex Filter Set Topology

namespace RHTower

noncomputable section

/-- Positive real regulator and aperture for a horizontal reflected slice. -/
structure ReflectedBiHeatPositiveSlice where
  delta : ℝ
  x : ℝ
  delta_pos : 0 < delta
  delta_lt_one : delta < 1
  x_pos : 0 < x

def ReflectedBiHeatPositiveSlice.leftOrder
    (Q : ReflectedBiHeatPositiveSlice) (z : ℂ) : ℂ :=
  z + (Q.delta : ℂ) / 2

def ReflectedBiHeatPositiveSlice.rightOrder
    (Q : ReflectedBiHeatPositiveSlice) (z : ℂ) : ℂ :=
  1 - z + (Q.delta : ℂ) / 2

/-- Strip on which both shifted orders remain inside the open unit strip. -/
def ReflectedBiHeatPositiveSlice.domain
    (Q : ReflectedBiHeatPositiveSlice) : Set ℂ :=
  {z | Q.delta / 2 < z.re ∧ z.re < 1 - Q.delta / 2}

/-- Triangularly reindexed summand on a fixed positive-regulator slice. -/
def reflectedBiHeatFixedRegulatorRowTerm
    (Q : ReflectedBiHeatPositiveSlice) (z : ℂ)
    (q : (ℕ × ℕ) ⊕ (ℕ × ℕ)) : ℂ :=
  asymmetricHeatPairTerm (Q.leftOrder z) (Q.rightOrder z) Q.x
    (upperLowerNatPairEquiv q)

/-- The fixed-regulator reflected double sum in triangular coordinates. -/
def reflectedBiHeatFixedRegulatorSum
    (Q : ReflectedBiHeatPositiveSlice) (z : ℂ) : ℂ :=
  ∑' q, reflectedBiHeatFixedRegulatorRowTerm Q z q

theorem ReflectedBiHeatPositiveSlice.leftOrder_add_rightOrder
    (Q : ReflectedBiHeatPositiveSlice) (z : ℂ) :
    Q.leftOrder z + Q.rightOrder z = 1 + Q.delta := by
  simp [ReflectedBiHeatPositiveSlice.leftOrder, ReflectedBiHeatPositiveSlice.rightOrder]
  ring

theorem differentiable_reflectedBiHeatFixedRegulatorRowTerm
    (Q : ReflectedBiHeatPositiveSlice) (q : (ℕ × ℕ) ⊕ (ℕ × ℕ)) :
    Differentiable ℂ (fun z => reflectedBiHeatFixedRegulatorRowTerm Q z q) := by
  have hm : (((((upperLowerNatPairEquiv q).1 : ℝ) + 1 : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  have hn : (((((upperLowerNatPairEquiv q).2 : ℝ) + 1 : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  have hleft : Differentiable ℂ (fun z : ℂ =>
      (((((upperLowerNatPairEquiv q).1 : ℝ) + 1 : ℝ) : ℂ)) ^
        (-(z + (Q.delta : ℂ) / 2))) :=
    (by fun_prop : Differentiable ℂ (fun z : ℂ => -(z + (Q.delta : ℂ) / 2))).const_cpow
      (Or.inl hm)
  have hright : Differentiable ℂ (fun z : ℂ =>
      (((((upperLowerNatPairEquiv q).2 : ℝ) + 1 : ℝ) : ℂ)) ^
        (-(1 - z + (Q.delta : ℂ) / 2))) :=
    (by fun_prop : Differentiable ℂ (fun z : ℂ => -(1 - z + (Q.delta : ℂ) / 2))).const_cpow
      (Or.inl hn)
  intro z
  simpa [reflectedBiHeatFixedRegulatorRowTerm, asymmetricHeatPairTerm,
    ReflectedBiHeatPositiveSlice.leftOrder, ReflectedBiHeatPositiveSlice.rightOrder] using
      ((hleft z).mul (hright z)).mul_const
        (((heatCoeff Q.x (((upperLowerNatPairEquiv q).1 : ℤ) -
          ((upperLowerNatPairEquiv q).2 : ℤ)) : ℝ) : ℂ))

/-- The fixed-regulator double sum is holomorphic at every point of the reflected strip. -/
theorem differentiableAt_reflectedBiHeatFixedRegulatorSum
    (Q : ReflectedBiHeatPositiveSlice) {z₀ : ℂ} (hz₀ : z₀ ∈ Q.domain) :
    DifferentiableAt ℂ (reflectedBiHeatFixedRegulatorSum Q) z₀ := by
  let R : ℝ := min (z₀.re - Q.delta / 2) (1 - Q.delta / 2 - z₀.re)
  have hR : 0 < R := by
    change 0 < min (z₀.re - Q.delta / 2) (1 - Q.delta / 2 - z₀.re)
    exact lt_min (sub_pos.mpr hz₀.1) (sub_pos.mpr hz₀.2)
  let M : (ℕ × ℕ) ⊕ (ℕ × ℕ) → ℝ :=
    asymmetricHeatPairMajorant (Q.leftOrder z₀) (Q.rightOrder z₀) Q.x
  have horders : ∀ z ∈ Metric.ball z₀ R,
      0 ≤ (Q.leftOrder z).re ∧ 0 ≤ (Q.rightOrder z).re := by
    intro z hz
    have hdist : ‖z - z₀‖ < R := by
      simpa [Complex.dist_eq] using hz
    have hre : |z.re - z₀.re| ≤ ‖z - z₀‖ := by
      simpa using Complex.abs_re_le_norm (z - z₀)
    have habs : |z.re - z₀.re| < R := lt_of_le_of_lt hre hdist
    have hRleft : R ≤ z₀.re - Q.delta / 2 := min_le_left _ _
    have hRright : R ≤ 1 - Q.delta / 2 - z₀.re := min_le_right _ _
    constructor
    · rw [ReflectedBiHeatPositiveSlice.leftOrder]
      norm_num [Complex.add_re, Complex.div_re]
      linarith [(abs_lt.mp habs).1, Q.delta_pos]
    · rw [ReflectedBiHeatPositiveSlice.rightOrder]
      norm_num [Complex.add_re, Complex.sub_re, Complex.div_re]
      linarith [(abs_lt.mp habs).2, Q.delta_pos]
  have hMsum : Summable M := by
    apply summable_asymmetricHeatPairMajorant
    · have hsum := congrArg Complex.re (Q.leftOrder_add_rightOrder z₀)
      norm_num at hsum ⊢
      linarith [Q.delta_pos]
    · exact Q.x_pos
  have hbound : ∀ q, ∀ z ∈ Metric.ball z₀ R,
      ‖reflectedBiHeatFixedRegulatorRowTerm Q z q‖ ≤ M q := by
    intro q z hz
    have hle := norm_asymmetricHeatPairTerm_comp_equiv_le
      (horders z hz).1 (horders z hz).2 Q.x q
    refine hle.trans_eq ?_
    rcases q with ⟨k, n⟩ | ⟨k, n⟩ <;>
      simp only [M, asymmetricHeatPairMajorant]
    · congr 3
      have hzsum := congrArg Complex.re (Q.leftOrder_add_rightOrder z)
      have h0sum := congrArg Complex.re (Q.leftOrder_add_rightOrder z₀)
      norm_num at hzsum h0sum
      linarith
    · congr 3
      have hzsum := congrArg Complex.re (Q.leftOrder_add_rightOrder z)
      have h0sum := congrArg Complex.re (Q.leftOrder_add_rightOrder z₀)
      norm_num at hzsum h0sum
      linarith
  exact GaloisForLFunctions.HTGeometry.differentiableAt_tsum_of_cauchy_dominated
    hR (fun q => (differentiable_reflectedBiHeatFixedRegulatorRowTerm Q q).differentiableOn)
    hbound hMsum

theorem differentiableOn_reflectedBiHeatFixedRegulatorSum
    (Q : ReflectedBiHeatPositiveSlice) :
    DifferentiableOn ℂ (reflectedBiHeatFixedRegulatorSum Q) Q.domain := by
  intro z hz
  exact (differentiableAt_reflectedBiHeatFixedRegulatorSum Q hz).differentiableWithinAt

end

end RHTower
