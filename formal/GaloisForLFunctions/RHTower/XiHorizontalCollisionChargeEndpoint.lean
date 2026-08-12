import GaloisForLFunctions.RHTower.XiHorizontalMultiplicityOneUniversalityLaw
import GaloisForLFunctions.RHTower.WindowLadder

/-!
# Horizontal collision charge and the exact two-unit RH endpoint

For a finite positive-height Xi strip window, attach to each zero `rho` its local multiplicity
`m_rho` and the total multiplicity `H_rho` of the exact horizontal fibre through `rho`.  The
collision charge

`sum_rho m_rho * (H_rho - m_rho)`

is nonnegative and dominates the complete off-line divisor mass.  The reason is literal: an
off-line point has a distinct critical-line reflection at the same ordinate with equal positive
multiplicity.

The existing window identity says that the off-line mass is twice the right-half mass.  Therefore
any off-line zero forces collision charge at least two.  This yields an unconditional endpoint:
a strict charge bound below two on every natural-height window is equivalent to RH.

This module proves the quantized endpoint.  It does not prove the missing source estimate below
two; in particular, a merely sublinear charge estimate would only imply density one and is not
enough for RH.
-/

open Complex Set Metric

namespace RHTower

noncomputable section

/-- Total off-critical Xi order in the positive-height strip window. -/
def xiStripWindowOffLineOrder (T : ℝ) : ℕ :=
  ∑ rho ∈ (stripZeros_finite T).toFinset.filter (fun rho => rho.re ≠ 1 / 2),
    (analyticOrderAt xi rho).toNat

/-- Total Xi order strictly right of the critical line in the positive-height strip window. -/
def xiStripWindowRightOrder (T : ℝ) : ℕ :=
  ∑ rho ∈ (stripZeros_finite T).toFinset.filter (fun rho => 1 / 2 < rho.re),
    (analyticOrderAt xi rho).toNat

/-- Horizontal collision charge of a finite positive-height Xi strip window. -/
def xiHorizontalCollisionCharge (T : ℝ) : ℕ :=
  ∑ rho ∈ (stripZeros_finite T).toFinset,
    (analyticOrderAt xi rho).toNat *
      (xiHorizontalMultiplicity rho.im - (analyticOrderAt xi rho).toNat)

/-- Every strip-window zero belongs to its complete exact-height Xi fibre. -/
theorem mem_stripHeightFinset_of_mem_stripZeros {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ (stripZeros_finite T).toFinset) :
    rho ∈ stripHeightFinset rho.im := by
  rw [Set.Finite.mem_toFinset] at hrho
  exact mem_stripHeightFinset.mpr
    ⟨hrho.1.1, hrho.1.2.1, rfl, hrho.2⟩

/-- The local multiplicity is bounded by the total multiplicity of its horizontal fibre. -/
theorem xi_order_le_horizontalMultiplicity_of_mem_stripZeros
    {T : ℝ} {rho : ℂ} (hrho : rho ∈ (stripZeros_finite T).toFinset) :
    (analyticOrderAt xi rho).toNat ≤ xiHorizontalMultiplicity rho.im := by
  rw [xiHorizontalMultiplicity]
  exact Finset.single_le_sum
    (s := stripHeightFinset rho.im)
    (f := fun z => (analyticOrderAt xi z).toNat)
    (fun z _ => Nat.zero_le _) (mem_stripHeightFinset_of_mem_stripZeros hrho)

/-- At an off-line strip zero, the complete horizontal fibre contains two disjoint copies of its
local order: the point and its critical-line reflection. -/
theorem two_mul_xi_order_le_horizontalMultiplicity_of_offLine
    {T : ℝ} {rho : ℂ} (hrho : rho ∈ (stripZeros_finite T).toFinset)
    (hoff : rho.re ≠ 1 / 2) :
    2 * (analyticOrderAt xi rho).toNat ≤ xiHorizontalMultiplicity rho.im := by
  classical
  have hheight : rho ∈ stripHeightFinset rho.im :=
    mem_stripHeightFinset_of_mem_stripZeros hrho
  have hreflect : lineReflect rho ∈ stripHeightFinset rho.im :=
    lineReflect_mem_stripHeightFinset hheight
  have hne : rho ≠ lineReflect rho := by
    intro h
    apply hoff
    have hre := congrArg Complex.re h
    rw [lineReflect_re] at hre
    linarith
  have hpair : ({rho, lineReflect rho} : Finset ℂ) ⊆ stripHeightFinset rho.im := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hheight
    · exact hreflect
  have hsum :
      (analyticOrderAt xi rho).toNat +
          (analyticOrderAt xi (lineReflect rho)).toNat ≤
        xiHorizontalMultiplicity rho.im := by
    rw [xiHorizontalMultiplicity]
    simpa only [Finset.sum_pair hne] using
      (Finset.sum_le_sum_of_subset hpair
        (f := fun z => (analyticOrderAt xi z).toNat))
  rw [xi_orderAt_lineReflect] at hsum
  omega

/-- One off-line zero copy pays at least its full multiplicity into collision charge. -/
theorem xi_order_le_horizontalCollisionTerm_of_offLine
    {T : ℝ} {rho : ℂ} (hrho : rho ∈ (stripZeros_finite T).toFinset)
    (hoff : rho.re ≠ 1 / 2) :
    (analyticOrderAt xi rho).toNat ≤
      (analyticOrderAt xi rho).toNat *
        (xiHorizontalMultiplicity rho.im - (analyticOrderAt xi rho).toNat) := by
  let m := (analyticOrderAt xi rho).toNat
  let H := xiHorizontalMultiplicity rho.im
  have hm : 1 ≤ m := by
    apply Nat.one_le_iff_ne_zero.mpr
    exact xi_order_toNat_ne_zero ((Set.Finite.mem_toFinset _).mp hrho).2
  have hpair : 2 * m ≤ H := by
    exact two_mul_xi_order_le_horizontalMultiplicity_of_offLine hrho hoff
  have hgap : 1 ≤ H - m := by omega
  calc
    m = m * 1 := by omega
    _ ≤ m * (H - m) := Nat.mul_le_mul_left m hgap

/-- **Deficit domination.** Complete off-line divisor multiplicity is bounded by horizontal
collision charge in the same window. -/
theorem xiStripWindowOffLineOrder_le_horizontalCollisionCharge (T : ℝ) :
    xiStripWindowOffLineOrder T ≤ xiHorizontalCollisionCharge T := by
  classical
  let S := (stripZeros_finite T).toFinset
  let m : ℂ → ℕ := fun rho => (analyticOrderAt xi rho).toNat
  let c : ℂ → ℕ := fun rho => m rho * (xiHorizontalMultiplicity rho.im - m rho)
  have hfiltered :
      (∑ rho ∈ S.filter (fun rho => rho.re ≠ 1 / 2), m rho) ≤
        ∑ rho ∈ S.filter (fun rho => rho.re ≠ 1 / 2), c rho := by
    apply Finset.sum_le_sum
    intro rho hrho
    have hdata := Finset.mem_filter.mp hrho
    exact xi_order_le_horizontalCollisionTerm_of_offLine hdata.1 hdata.2
  have hpart :
      (∑ rho ∈ S.filter (fun rho => rho.re ≠ 1 / 2), c rho) ≤
        ∑ rho ∈ S, c rho := by
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  exact hfiltered.trans hpart

/-- The off-line window mass is exactly twice the right-half window mass. -/
theorem xiStripWindowOffLineOrder_eq_two_mul_rightOrder (T : ℝ) :
    xiStripWindowOffLineOrder T = 2 * xiStripWindowRightOrder T := by
  classical
  let S := (stripZeros_finite T).toFinset
  let m : ℂ → ℕ := fun rho => (analyticOrderAt xi rho).toNat
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not S (fun rho => rho.re = 1 / 2) m
  have hwindow := stripWindow_order_identity T
  change
    (∑ rho ∈ S.filter (fun rho => rho.re ≠ 1 / 2), m rho) =
      2 * ∑ rho ∈ S.filter (fun rho => 1 / 2 < rho.re), m rho
  change
    (∑ rho ∈ S, m rho) =
      (∑ rho ∈ S.filter (fun rho => rho.re = 1 / 2), m rho) +
        2 * ∑ rho ∈ S.filter (fun rho => 1 / 2 < rho.re), m rho at hwindow
  have hsplit' :
      (∑ rho ∈ S.filter (fun rho => rho.re = 1 / 2), m rho) +
        (∑ rho ∈ S.filter (fun rho => rho.re ≠ 1 / 2), m rho) = ∑ rho ∈ S, m rho := hsplit
  omega

/-- A charge strictly below the reflected-pair quantum forces the right-half window empty. -/
theorem boxZeros_eq_empty_of_horizontalCollisionCharge_lt_two
    {T : ℝ} (hcharge : xiHorizontalCollisionCharge T < 2) :
    boxZeros T = ∅ := by
  have hoff := xiStripWindowOffLineOrder_le_horizontalCollisionCharge T
  have hsplit := xiStripWindowOffLineOrder_eq_two_mul_rightOrder T
  have hright : xiStripWindowRightOrder T = 0 := by omega
  rw [Set.eq_empty_iff_forall_notMem]
  intro rho hrho
  have hmemStrip : rho ∈ (stripZeros_finite T).toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact boxZeros_subset_stripZeros T hrho
  have hmemRight :
      rho ∈ (stripZeros_finite T).toFinset.filter (fun z => 1 / 2 < z.re) :=
    Finset.mem_filter.mpr ⟨hmemStrip, hrho.1.1⟩
  have hpositive : 1 ≤ (analyticOrderAt xi rho).toNat :=
    Nat.one_le_iff_ne_zero.mpr (xi_order_toNat_ne_zero hrho.2)
  have hle : (analyticOrderAt xi rho).toNat ≤ xiStripWindowRightOrder T := by
    rw [xiStripWindowRightOrder]
    exact Finset.single_le_sum
      (fun z _ => Nat.zero_le ((analyticOrderAt xi z).toNat)) hmemRight
  rw [hright] at hle
  omega

/-- Under RH every horizontal fibre contains only its generating critical-line zero, so collision
charge vanishes pointwise. -/
theorem xiHorizontalCollisionCharge_eq_zero_of_riemannHypothesis
    (hRH : RiemannHypothesis) (T : ℝ) :
    xiHorizontalCollisionCharge T = 0 := by
  classical
  rw [xiHorizontalCollisionCharge, Finset.sum_eq_zero]
  intro rho hrho
  have hzero : xi rho = 0 := ((Set.Finite.mem_toFinset _).mp hrho).2
  rw [xiHorizontalMultiplicity_eq_order_of_RH hRH hzero, Nat.sub_self, mul_zero]

/-- **Exact quantized collision endpoint.** RH is equivalent to a strict two-unit collision bound
on every real-height window. -/
theorem riemannHypothesis_iff_forall_horizontalCollisionCharge_lt_two :
    RiemannHypothesis ↔ ∀ T : ℝ, xiHorizontalCollisionCharge T < 2 := by
  constructor
  · intro hRH T
    rw [xiHorizontalCollisionCharge_eq_zero_of_riemannHypothesis hRH T]
    omega
  · intro hcharge
    rw [rh_iff_forall_boxZeros_empty]
    exact fun T => boxZeros_eq_empty_of_horizontalCollisionCharge_lt_two (hcharge T)

/-- Vanishing collision charge is an equivalent, slightly stronger-looking presentation of the
same endpoint. -/
theorem riemannHypothesis_iff_forall_horizontalCollisionCharge_eq_zero :
    RiemannHypothesis ↔ ∀ T : ℝ, xiHorizontalCollisionCharge T = 0 := by
  constructor
  · exact xiHorizontalCollisionCharge_eq_zero_of_riemannHypothesis
  · intro hzero
    exact riemannHypothesis_iff_forall_horizontalCollisionCharge_lt_two.mpr
      (fun T => by rw [hzero T]; omega)

/-- Natural-height windows are already cofinal.  Thus a source estimate below two is needed only
at integer cutoffs; no asymptotic limiting argument is required. -/
theorem riemannHypothesis_of_forall_nat_horizontalCollisionCharge_lt_two
    (hcharge : ∀ n : ℕ, xiHorizontalCollisionCharge n < 2) :
    RiemannHypothesis := by
  rw [rh_iff_forall_boxZeros_empty]
  intro T
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt T
  have hnempty : boxZeros (n : ℝ) = ∅ :=
    boxZeros_eq_empty_of_horizontalCollisionCharge_lt_two (hcharge n)
  rw [Set.eq_empty_iff_forall_notMem]
  intro rho hrho
  have hrhoN : rho ∈ boxZeros (n : ℝ) := by
    exact ⟨⟨hrho.1.1, hrho.1.2.1, hrho.1.2.2.1,
      hrho.1.2.2.2.trans hn⟩, hrho.2⟩
  rw [hnempty] at hrhoN
  exact Set.notMem_empty rho hrhoN

end

end RHTower
