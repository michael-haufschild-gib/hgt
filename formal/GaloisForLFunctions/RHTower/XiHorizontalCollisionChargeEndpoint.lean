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

open Complex Set Metric Filter

namespace RHTower

noncomputable section

/-- Total Xi divisor order in the positive-height strip window. -/
def xiStripWindowTotalOrder (T : ℝ) : ℕ :=
  ∑ rho ∈ (stripZeros_finite T).toFinset, (analyticOrderAt xi rho).toNat

/-- Total critical-line Xi order in the positive-height strip window. -/
def xiStripWindowLineOrder (T : ℝ) : ℕ :=
  ∑ rho ∈ (stripZeros_finite T).toFinset.filter (fun rho => rho.re = 1 / 2),
    (analyticOrderAt xi rho).toNat

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

/-- Ordered distinct pairs of Xi zeros lying in the same horizontal window fibre. -/
def xiHorizontalCollisionPairs (T : ℝ) : Finset (ℂ × ℂ) :=
  (((stripZeros_finite T).toFinset ×ˢ (stripZeros_finite T).toFinset).filter
    (fun p => p.1.im = p.2.im ∧ p.1 ≠ p.2))

/-- Sum of squared total horizontal-fibre multiplicities over the ordinates occurring in a strip
window. -/
def xiStripWindowHorizontalSquareSum (T : ℝ) : ℕ :=
  ∑ gamma ∈ (stripZeros_finite T).toFinset.image Complex.im,
    (xiHorizontalMultiplicity gamma) ^ 2

/-- Sum of squared local Xi multiplicities over a strip window. -/
def xiStripWindowLocalSquareSum (T : ℝ) : ℕ :=
  ∑ rho ∈ (stripZeros_finite T).toFinset,
    ((analyticOrderAt xi rho).toNat) ^ 2

/-- Strip-zero finsets grow with the height cutoff. -/
theorem stripZeros_toFinset_mono {T U : ℝ} (hTU : T ≤ U) :
    (stripZeros_finite T).toFinset ⊆ (stripZeros_finite U).toFinset := by
  intro rho hrho
  rw [Set.Finite.mem_toFinset] at hrho ⊢
  exact ⟨⟨hrho.1.1, hrho.1.2.1, hrho.1.2.2.1,
    hrho.1.2.2.2.trans_le hTU⟩, hrho.2⟩

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

/-- Inside a strip window, the full exact-height fibre through a member is precisely the window
slice at that ordinate.  The height bounds transfer from the chosen member because all points in
the fibre have the same imaginary part. -/
theorem stripHeightFinset_eq_stripZeros_filter_im
    {T : ℝ} {rho : ℂ} (hrho : rho ∈ (stripZeros_finite T).toFinset) :
    stripHeightFinset rho.im =
      (stripZeros_finite T).toFinset.filter (fun z => z.im = rho.im) := by
  ext z
  rw [mem_stripHeightFinset, Finset.mem_filter, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨hzre0, hzre1, hzim, hzero⟩
    have hrhoData := (stripZeros_finite T).mem_toFinset.mp hrho
    refine ⟨⟨⟨hzre0, hzre1, ?_, ?_⟩, hzero⟩, hzim⟩
    · rw [hzim]
      exact hrhoData.1.2.2.1
    · rw [hzim]
      exact hrhoData.1.2.2.2
  · rintro ⟨hz, hzim⟩
    exact ⟨hz.1.1, hz.1.2.1, hzim, hz.2⟩

/-- At every ordinate represented in the window, the horizontal multiplicity is exactly the
local-order sum over the corresponding window fibre. -/
theorem horizontalMultiplicity_eq_sum_stripZeros_filter_im
    {T gamma : ℝ}
    (hgamma : gamma ∈ (stripZeros_finite T).toFinset.image Complex.im) :
    xiHorizontalMultiplicity gamma =
      ∑ rho ∈ (stripZeros_finite T).toFinset.filter (fun z => z.im = gamma),
        (analyticOrderAt xi rho).toNat := by
  obtain ⟨rho, hrho, hrhoIm⟩ := Finset.mem_image.mp hgamma
  subst gamma
  rw [xiHorizontalMultiplicity,
    stripHeightFinset_eq_stripZeros_filter_im hrho]

/-- Removing the local order from its horizontal multiplicity leaves exactly the sum over the
other points in the same window fibre. -/
theorem horizontalMultiplicity_sub_order_eq_sum_same_im_erase
    {T : ℝ} {rho : ℂ} (hrho : rho ∈ (stripZeros_finite T).toFinset) :
    xiHorizontalMultiplicity rho.im - (analyticOrderAt xi rho).toNat =
      ∑ z ∈ ((stripZeros_finite T).toFinset.filter
        (fun z => z.im = rho.im)).erase rho,
          (analyticOrderAt xi z).toNat := by
  let F := (stripZeros_finite T).toFinset.filter (fun z => z.im = rho.im)
  have hrhoF : rho ∈ F := Finset.mem_filter.mpr ⟨hrho, rfl⟩
  have hsum := Finset.sum_erase_add F
    (fun z => (analyticOrderAt xi z).toNat) hrhoF
  rw [xiHorizontalMultiplicity,
    stripHeightFinset_eq_stripZeros_filter_im hrho]
  change
    (∑ z ∈ F, (analyticOrderAt xi z).toNat) -
        (analyticOrderAt xi rho).toNat =
      ∑ z ∈ F.erase rho, (analyticOrderAt xi z).toNat
  omega

/-- **Ordered-pair normal form.** Collision charge is the multiplicity-weighted mass of all
ordered distinct pairs in common horizontal fibres. -/
theorem xiHorizontalCollisionCharge_eq_sum_pairs (T : ℝ) :
    xiHorizontalCollisionCharge T =
      ∑ p ∈ xiHorizontalCollisionPairs T,
        (analyticOrderAt xi p.1).toNat * (analyticOrderAt xi p.2).toNat := by
  classical
  let S := (stripZeros_finite T).toFinset
  let m : ℂ → ℕ := fun rho => (analyticOrderAt xi rho).toNat
  rw [xiHorizontalCollisionCharge]
  change ∑ rho ∈ S, m rho * (xiHorizontalMultiplicity rho.im - m rho) = _
  calc
    (∑ rho ∈ S, m rho * (xiHorizontalMultiplicity rho.im - m rho)) =
        ∑ rho ∈ S, ∑ z ∈ (S.filter (fun z => z.im = rho.im)).erase rho,
          m rho * m z := by
      apply Finset.sum_congr rfl
      intro rho hrho
      rw [horizontalMultiplicity_sub_order_eq_sum_same_im_erase hrho,
        Finset.mul_sum]
    _ = ∑ rho ∈ S, ∑ z ∈ S.filter (fun z => z.im = rho.im ∧ z ≠ rho),
          m rho * m z := by
      apply Finset.sum_congr rfl
      intro rho _
      apply Finset.sum_congr
      · ext z
        simp only [Finset.mem_erase, Finset.mem_filter]
        tauto
      · intro z _
        rfl
    _ = ∑ p ∈ xiHorizontalCollisionPairs T, m p.1 * m p.2 := by
      rw [xiHorizontalCollisionPairs, Finset.sum_filter, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro rho _
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro z _
      simp [eq_comm]

/-- Ordered horizontal-collision pairs persist when the height cutoff increases. -/
theorem xiHorizontalCollisionPairs_mono {T U : ℝ} (hTU : T ≤ U) :
    xiHorizontalCollisionPairs T ⊆ xiHorizontalCollisionPairs U := by
  intro p hp
  rw [xiHorizontalCollisionPairs, Finset.mem_filter, Finset.mem_product] at hp ⊢
  exact ⟨⟨stripZeros_toFinset_mono hTU hp.1.1,
    stripZeros_toFinset_mono hTU hp.1.2⟩, hp.2⟩

/-- Horizontal collision charge is monotone in the height cutoff. -/
theorem xiHorizontalCollisionCharge_mono : Monotone xiHorizontalCollisionCharge := by
  intro T U hTU
  rw [xiHorizontalCollisionCharge_eq_sum_pairs,
    xiHorizontalCollisionCharge_eq_sum_pairs]
  exact Finset.sum_le_sum_of_subset (xiHorizontalCollisionPairs_mono hTU)

/-- **Quadratic census identity.** The horizontal square census is the local square census plus
collision charge.  Equivalently, collision charge is
`sum_gamma H_gamma^2 - sum_rho m_rho^2`. -/
theorem xiStripWindowHorizontalSquareSum_eq_localSquare_add_collisionCharge
    (T : ℝ) :
    xiStripWindowHorizontalSquareSum T =
      xiStripWindowLocalSquareSum T + xiHorizontalCollisionCharge T := by
  classical
  let S := (stripZeros_finite T).toFinset
  let G := S.image Complex.im
  let m : ℂ → ℕ := fun rho => (analyticOrderAt xi rho).toNat
  let H : ℝ → ℕ := xiHorizontalMultiplicity
  have hgroup :
      (∑ gamma ∈ G, H gamma ^ 2) = ∑ rho ∈ S, m rho * H rho.im := by
    calc
      (∑ gamma ∈ G, H gamma ^ 2) =
          ∑ gamma ∈ G,
            ∑ rho ∈ S.filter (fun z => z.im = gamma), m rho * H gamma := by
        apply Finset.sum_congr rfl
        intro gamma hgamma
        rw [← Finset.sum_mul]
        have hmass := horizontalMultiplicity_eq_sum_stripZeros_filter_im hgamma
        change H gamma = ∑ rho ∈ S.filter (fun z => z.im = gamma), m rho at hmass
        rw [← hmass]
        ring
      _ = ∑ gamma ∈ G,
          ∑ rho ∈ S.filter (fun z => z.im = gamma), m rho * H rho.im := by
        apply Finset.sum_congr rfl
        intro gamma _
        apply Finset.sum_congr rfl
        intro rho hrho
        have him := (Finset.mem_filter.mp hrho).2
        rw [him]
      _ = ∑ rho ∈ S, m rho * H rho.im := by
        exact Finset.sum_fiberwise_of_maps_to
          (fun rho hrho => Finset.mem_image.mpr ⟨rho, hrho, rfl⟩)
          (fun rho => m rho * H rho.im)
  have hpoint : ∀ rho ∈ S,
      m rho * H rho.im = m rho ^ 2 + m rho * (H rho.im - m rho) := by
    intro rho hrho
    have hle : m rho ≤ H rho.im :=
      xi_order_le_horizontalMultiplicity_of_mem_stripZeros hrho
    calc
      m rho * H rho.im = m rho * (m rho + (H rho.im - m rho)) := by
        rw [Nat.add_sub_of_le hle]
      _ = m rho ^ 2 + m rho * (H rho.im - m rho) := by ring
  rw [xiStripWindowHorizontalSquareSum, xiStripWindowLocalSquareSum,
    xiHorizontalCollisionCharge]
  change (∑ gamma ∈ G, H gamma ^ 2) =
    (∑ rho ∈ S, m rho ^ 2) + ∑ rho ∈ S, m rho * (H rho.im - m rho)
  rw [hgroup, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl hpoint

/-- User-facing difference form of the same quadratic identity. -/
theorem xiHorizontalCollisionCharge_eq_horizontalSquare_sub_localSquare (T : ℝ) :
    xiHorizontalCollisionCharge T =
      xiStripWindowHorizontalSquareSum T - xiStripWindowLocalSquareSum T := by
  have h := xiStripWindowHorizontalSquareSum_eq_localSquare_add_collisionCharge T
  omega

/-- Collision charge is even: swapping an ordered pair is a fixed-point-free involution and keeps
its multiplicity product unchanged. -/
theorem xiHorizontalCollisionCharge_even (T : ℝ) :
    Even (xiHorizontalCollisionCharge T) := by
  classical
  rw [xiHorizontalCollisionCharge_eq_sum_pairs, even_iff_two_dvd,
    ← ZMod.natCast_eq_zero_iff
      (∑ p ∈ xiHorizontalCollisionPairs T,
        (analyticOrderAt xi p.1).toNat * (analyticOrderAt xi p.2).toNat) 2]
  push_cast
  refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
  · intro p _
    rw [mul_comm]
    exact CharTwo.add_self_eq_zero _
  · intro p hp _ hfix
    have hpne := (Finset.mem_filter.mp hp).2.2
    apply hpne
    exact congrArg Prod.fst hfix.symm
  · intro p hp
    rw [xiHorizontalCollisionPairs, Finset.mem_filter,
      Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2.1.symm, fun h => hp.2.2 h.symm⟩
  · intro p _
    rfl

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
    exact xi_order_toNat_ne_zero ((stripZeros_finite T).mem_toFinset.mp hrho).2
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

/-- The strip divisor splits exactly into its critical-line and off-line parts. -/
theorem xiStripWindowTotalOrder_eq_line_add_offLine (T : ℝ) :
    xiStripWindowTotalOrder T =
      xiStripWindowLineOrder T + xiStripWindowOffLineOrder T := by
  classical
  let S := (stripZeros_finite T).toFinset
  let m : ℂ → ℕ := fun rho => (analyticOrderAt xi rho).toNat
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not S (fun rho => rho.re = 1 / 2) m
  change
    (∑ rho ∈ S, m rho) =
      (∑ rho ∈ S.filter (fun rho => rho.re = 1 / 2), m rho) +
        ∑ rho ∈ S.filter (fun rho => rho.re ≠ 1 / 2), m rho
  exact hsplit.symm

/-- **User-facing deficit inequality.** The critical-line order is at least total order minus
horizontal collision charge: `N₀(T) ≥ N(T) - O(T)`. -/
theorem xiStripWindowTotalOrder_sub_collisionCharge_le_lineOrder (T : ℝ) :
    xiStripWindowTotalOrder T - xiHorizontalCollisionCharge T ≤
      xiStripWindowLineOrder T := by
  have hsplit := xiStripWindowTotalOrder_eq_line_add_offLine T
  have hoff := xiStripWindowOffLineOrder_le_horizontalCollisionCharge T
  omega

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
  have hzero : xi rho = 0 := ((stripZeros_finite T).mem_toFinset.mp hrho).2
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

/-- A strict two-unit estimate on any cofinal family of height windows proves RH.  This is the
precise form needed from a source estimate: it need not control every cutoff. -/
theorem riemannHypothesis_of_cofinal_horizontalCollisionCharge_lt_two
    (hcharge : ∀ T : ℝ, ∃ U : ℝ,
      T ≤ U ∧ xiHorizontalCollisionCharge U < 2) :
    RiemannHypothesis := by
  rw [rh_iff_forall_boxZeros_empty]
  intro T
  obtain ⟨U, hTU, hU⟩ := hcharge T
  have hUempty : boxZeros U = ∅ :=
    boxZeros_eq_empty_of_horizontalCollisionCharge_lt_two hU
  rw [Set.eq_empty_iff_forall_notMem]
  intro rho hrho
  have hrhoU : rho ∈ boxZeros U := boxZeros_mono hTU hrho
  rw [hUempty] at hrhoU
  exact hrhoU

/-- An eventual source estimate below the indivisible collision quantum is enough.  In contrast,
an estimate only after division by the total zero count is not enough. -/
theorem riemannHypothesis_of_eventually_horizontalCollisionCharge_lt_two
    (hcharge : ∀ᶠ T : ℝ in atTop, xiHorizontalCollisionCharge T < 2) :
    RiemannHypothesis := by
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 hcharge
  apply riemannHypothesis_of_cofinal_horizontalCollisionCharge_lt_two
  intro T
  exact ⟨max T T₀, le_max_left T T₀, hT₀ _ (le_max_right T T₀)⟩

end

end RHTower
