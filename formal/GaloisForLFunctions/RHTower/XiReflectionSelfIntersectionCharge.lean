import GaloisForLFunctions.RHTower.XiHorizontalCollisionChargeEndpoint
import GaloisForLFunctions.RHTower.XiWeilCauchyCoreMultiplicity
import GaloisForLFunctions.RHTower.XiCriticalLineIntegrality
import GaloisForLFunctions.RHTower.SourceZeroHorizontalCarrier

/-!
# Canonical reflection self-intersection charge

The full horizontal collision charge counts every ordered pair of distinct Xi zeros at one
ordinate.  This module separates its canonical part: the two oriented incidences between each
right-half zero and its critical-line reflection.  If the local divisor order is `m`, this forced
contribution is `2 * m^(2 : ℕ)`.

The resulting reflection charge is bounded by the full collision charge and has the same exact
two-unit RH endpoint.  Unlike the full charge, every local square is the literal cardinality of a
Cartesian product of multiplicity-copy fibres.  No synthetic replication, simplicity assumption,
zero-location hypothesis, or source estimate is used.
-/

open Complex Set Metric Filter
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Sum of squared Xi orders at off-critical points in a positive-height strip window. -/
def xiStripWindowOffLineSquareOrder (T : ℝ) : ℕ :=
  ∑ rho ∈ (stripZeros_finite T).toFinset.filter (fun rho => rho.re ≠ 1 / 2),
    ((analyticOrderAt xi rho).toNat) ^ (2 : ℕ)

/-- Sum of squared Xi orders strictly right of the critical line in a positive-height window. -/
def xiStripWindowRightSquareOrder (T : ℝ) : ℕ :=
  ∑ rho ∈ (stripZeros_finite T).toFinset.filter (fun rho => 1 / 2 < rho.re),
    ((analyticOrderAt xi rho).toNat) ^ (2 : ℕ)

/-- Canonical two-oriented self-intersection charge forced by critical-line reflection. -/
def xiReflectionSelfIntersectionCharge (T : ℝ) : ℕ :=
  2 * xiStripWindowRightSquareOrder T

/-- Noncanonical remainder of horizontal collision charge after forced reflection incidences. -/
def xiHorizontalAccidentalCollisionCharge (T : ℝ) : ℕ :=
  xiHorizontalCollisionCharge T - xiReflectionSelfIntersectionCharge T

/-- Squared off-line divisor order is exactly twice squared right-half divisor order. -/
theorem xiStripWindowOffLineSquareOrder_eq_two_mul_rightSquareOrder (T : ℝ) :
    xiStripWindowOffLineSquareOrder T = 2 * xiStripWindowRightSquareOrder T := by
  classical
  let S := (stripZeros_finite T).toFinset
  let m : ℂ → ℕ := fun rho => (analyticOrderAt xi rho).toNat
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not S (fun rho => rho.re = 1 / 2)
      (fun rho => m rho ^ (2 : ℕ))
  have hwindow :
      (∑ rho ∈ S, m rho ^ (2 : ℕ)) =
        (∑ rho ∈ S.filter (fun rho => rho.re = 1 / 2), m rho ^ (2 : ℕ)) +
          2 * ∑ rho ∈ S.filter (fun rho => 1 / 2 < rho.re), m rho ^ (2 : ℕ) := by
    refine window_identity (m := fun rho => m rho ^ (2 : ℕ)) ?_ ?_
    · intro rho hrho
      rw [Set.Finite.mem_toFinset] at hrho ⊢
      exact lineReflect_mem_stripZeros hrho
    · intro rho _
      dsimp only [m]
      rw [xi_orderAt_lineReflect]
  change
    (∑ rho ∈ S.filter (fun rho => rho.re ≠ 1 / 2), m rho ^ (2 : ℕ)) =
      2 * ∑ rho ∈ S.filter (fun rho => 1 / 2 < rho.re), m rho ^ (2 : ℕ)
  have hsplit' :
      (∑ rho ∈ S.filter (fun rho => rho.re = 1 / 2), m rho ^ (2 : ℕ)) +
          (∑ rho ∈ S.filter (fun rho => rho.re ≠ 1 / 2), m rho ^ (2 : ℕ)) =
        ∑ rho ∈ S, m rho ^ (2 : ℕ) := hsplit
  omega

/-- At an off-line zero, its local square is paid by the horizontal collision summand. -/
theorem xi_order_sq_le_horizontalCollisionTerm_of_offLine
    {T : ℝ} {rho : ℂ} (hrho : rho ∈ (stripZeros_finite T).toFinset)
    (hoff : rho.re ≠ 1 / 2) :
    ((analyticOrderAt xi rho).toNat) ^ (2 : ℕ) ≤
      (analyticOrderAt xi rho).toNat *
        (xiHorizontalMultiplicity rho.im - (analyticOrderAt xi rho).toNat) := by
  let m := (analyticOrderAt xi rho).toNat
  let H := xiHorizontalMultiplicity rho.im
  have hpair : 2 * m ≤ H :=
    two_mul_xi_order_le_horizontalMultiplicity_of_offLine hrho hoff
  have hgap : m ≤ H - m := by omega
  simpa only [pow_two] using Nat.mul_le_mul_left m hgap

/-- Full off-line squared order is bounded by full horizontal collision charge. -/
theorem xiStripWindowOffLineSquareOrder_le_horizontalCollisionCharge (T : ℝ) :
    xiStripWindowOffLineSquareOrder T ≤ xiHorizontalCollisionCharge T := by
  classical
  let S := (stripZeros_finite T).toFinset
  let m : ℂ → ℕ := fun rho => (analyticOrderAt xi rho).toNat
  let c : ℂ → ℕ := fun rho =>
    m rho * (xiHorizontalMultiplicity rho.im - m rho)
  have hfiltered :
      (∑ rho ∈ S.filter (fun rho => rho.re ≠ 1 / 2), m rho ^ (2 : ℕ)) ≤
        ∑ rho ∈ S.filter (fun rho => rho.re ≠ 1 / 2), c rho := by
    apply Finset.sum_le_sum
    intro rho hrho
    have hdata := Finset.mem_filter.mp hrho
    exact xi_order_sq_le_horizontalCollisionTerm_of_offLine hdata.1 hdata.2
  have hpart :
      (∑ rho ∈ S.filter (fun rho => rho.re ≠ 1 / 2), c rho) ≤
        ∑ rho ∈ S, c rho :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  exact hfiltered.trans hpart

/-- Reflection charge is exactly squared off-line divisor order. -/
theorem xiReflectionSelfIntersectionCharge_eq_offLineSquareOrder (T : ℝ) :
    xiReflectionSelfIntersectionCharge T = xiStripWindowOffLineSquareOrder T := by
  rw [xiReflectionSelfIntersectionCharge,
    xiStripWindowOffLineSquareOrder_eq_two_mul_rightSquareOrder]

/-- Canonical reflection charge is a lower bound for full horizontal collision charge. -/
theorem xiReflectionSelfIntersectionCharge_le_horizontalCollisionCharge (T : ℝ) :
    xiReflectionSelfIntersectionCharge T ≤ xiHorizontalCollisionCharge T := by
  rw [xiReflectionSelfIntersectionCharge_eq_offLineSquareOrder]
  exact xiStripWindowOffLineSquareOrder_le_horizontalCollisionCharge T

/-- Exact decomposition into forced reflection self-intersection and accidental collision excess. -/
theorem xiHorizontalCollisionCharge_eq_reflection_add_accidental (T : ℝ) :
    xiHorizontalCollisionCharge T =
      xiReflectionSelfIntersectionCharge T + xiHorizontalAccidentalCollisionCharge T := by
  rw [xiHorizontalAccidentalCollisionCharge]
  exact (Nat.add_sub_of_le
    (xiReflectionSelfIntersectionCharge_le_horizontalCollisionCharge T)).symm

/-- Reflection charge is even because it records both orientations. -/
theorem xiReflectionSelfIntersectionCharge_even (T : ℝ) :
    Even (xiReflectionSelfIntersectionCharge T) := by
  refine ⟨xiStripWindowRightSquareOrder T, ?_⟩
  rw [xiReflectionSelfIntersectionCharge]
  omega

/-- Reflection charge grows monotonically with window height. -/
theorem xiReflectionSelfIntersectionCharge_mono :
    Monotone xiReflectionSelfIntersectionCharge := by
  intro T U hTU
  rw [xiReflectionSelfIntersectionCharge, xiReflectionSelfIntersectionCharge]
  apply Nat.mul_le_mul_left
  rw [xiStripWindowRightSquareOrder, xiStripWindowRightSquareOrder]
  apply Finset.sum_le_sum_of_subset
  intro rho hrho
  have hdata := Finset.mem_filter.mp hrho
  exact Finset.mem_filter.mpr
    ⟨stripZeros_toFinset_mono hTU hdata.1, hdata.2⟩

/-- A reflection charge below its indivisible two-unit quantum empties the right-half box. -/
theorem boxZeros_eq_empty_of_reflectionSelfIntersectionCharge_lt_two
    {T : ℝ} (hcharge : xiReflectionSelfIntersectionCharge T < 2) :
    boxZeros T = ∅ := by
  have hright : xiStripWindowRightSquareOrder T = 0 := by
    rw [xiReflectionSelfIntersectionCharge] at hcharge
    omega
  rw [Set.eq_empty_iff_forall_notMem]
  intro rho hrho
  have hmemStrip : rho ∈ (stripZeros_finite T).toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact boxZeros_subset_stripZeros T hrho
  have hmemRight :
      rho ∈ (stripZeros_finite T).toFinset.filter (fun z => 1 / 2 < z.re) :=
    Finset.mem_filter.mpr ⟨hmemStrip, hrho.1.1⟩
  have hle : ((analyticOrderAt xi rho).toNat) ^ (2 : ℕ) ≤
      xiStripWindowRightSquareOrder T := by
    rw [xiStripWindowRightSquareOrder]
    exact Finset.single_le_sum
      (fun z _ => Nat.zero_le ((analyticOrderAt xi z).toNat ^ (2 : ℕ))) hmemRight
  rw [hright] at hle
  have hsquare : ((analyticOrderAt xi rho).toNat) ^ (2 : ℕ) = 0 :=
    Nat.eq_zero_of_le_zero hle
  have horder : (analyticOrderAt xi rho).toNat = 0 := by
    by_contra hne
    have hpos : 0 < ((analyticOrderAt xi rho).toNat) ^ (2 : ℕ) :=
      Nat.pow_pos (Nat.pos_of_ne_zero hne)
    omega
  exact (xi_order_toNat_ne_zero hrho.2) horder

/-- Under RH the canonical reflection self-intersection charge vanishes. -/
theorem xiReflectionSelfIntersectionCharge_eq_zero_of_riemannHypothesis
    (hRH : RiemannHypothesis) (T : ℝ) :
    xiReflectionSelfIntersectionCharge T = 0 := by
  have hle := xiReflectionSelfIntersectionCharge_le_horizontalCollisionCharge T
  rw [xiHorizontalCollisionCharge_eq_zero_of_riemannHypothesis hRH T] at hle
  omega

/-- Exact strict-two endpoint for canonical reflection self-intersection charge. -/
theorem riemannHypothesis_iff_forall_reflectionSelfIntersectionCharge_lt_two :
    RiemannHypothesis ↔ ∀ T : ℝ, xiReflectionSelfIntersectionCharge T < 2 := by
  constructor
  · intro hRH T
    rw [xiReflectionSelfIntersectionCharge_eq_zero_of_riemannHypothesis hRH T]
    omega
  · intro hcharge
    rw [rh_iff_forall_boxZeros_empty]
    exact fun T =>
      boxZeros_eq_empty_of_reflectionSelfIntersectionCharge_lt_two (hcharge T)

/-- Vanishing canonical reflection charge is equivalent to RH. -/
theorem riemannHypothesis_iff_forall_reflectionSelfIntersectionCharge_eq_zero :
    RiemannHypothesis ↔ ∀ T : ℝ, xiReflectionSelfIntersectionCharge T = 0 := by
  constructor
  · exact xiReflectionSelfIntersectionCharge_eq_zero_of_riemannHypothesis
  · intro hzero
    exact riemannHypothesis_iff_forall_reflectionSelfIntersectionCharge_lt_two.mpr
      (fun T => by rw [hzero T]; omega)

/-- Natural-height strict-two estimates for canonical reflection charge prove RH. -/
theorem riemannHypothesis_of_forall_nat_reflectionSelfIntersectionCharge_lt_two
    (hcharge : ∀ n : ℕ, xiReflectionSelfIntersectionCharge n < 2) :
    RiemannHypothesis := by
  rw [rh_iff_forall_boxZeros_empty]
  intro T
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt T
  have hnempty : boxZeros (n : ℝ) = ∅ :=
    boxZeros_eq_empty_of_reflectionSelfIntersectionCharge_lt_two (hcharge n)
  rw [Set.eq_empty_iff_forall_notMem]
  intro rho hrho
  have hrhoN : rho ∈ boxZeros (n : ℝ) := by
    exact ⟨⟨hrho.1.1, hrho.1.2.1, hrho.1.2.2.1,
      hrho.1.2.2.2.trans hn⟩, hrho.2⟩
  rw [hnempty] at hrhoN
  exact Set.notMem_empty rho hrhoN

/-- Strict-two estimates on any cofinal family of reflection-charge windows prove RH. -/
theorem riemannHypothesis_of_cofinal_reflectionSelfIntersectionCharge_lt_two
    (hcharge : ∀ T : ℝ, ∃ U : ℝ,
      T ≤ U ∧ xiReflectionSelfIntersectionCharge U < 2) :
    RiemannHypothesis := by
  rw [rh_iff_forall_boxZeros_empty]
  intro T
  obtain ⟨U, hTU, hU⟩ := hcharge T
  have hUempty : boxZeros U = ∅ :=
    boxZeros_eq_empty_of_reflectionSelfIntersectionCharge_lt_two hU
  rw [Set.eq_empty_iff_forall_notMem]
  intro rho hrho
  have hrhoU : rho ∈ boxZeros U := boxZeros_mono hTU hrho
  rw [hUempty] at hrhoU
  exact hrhoU

/-- An eventual strict-two reflection-charge estimate proves RH. -/
theorem riemannHypothesis_of_eventually_reflectionSelfIntersectionCharge_lt_two
    (hcharge : ∀ᶠ T : ℝ in atTop, xiReflectionSelfIntersectionCharge T < 2) :
    RiemannHypothesis := by
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 hcharge
  apply riemannHypothesis_of_cofinal_reflectionSelfIntersectionCharge_lt_two
  intro T
  exact ⟨max T T₀, le_max_left T T₀, hT₀ _ (le_max_right T T₀)⟩

/-! ## Multiplicity-copy incidence realization -/

/-- Literal oriented incidence set between a Xi multiplicity fibre and its line-reflected fibre. -/
def xiZeroCopyLineReflectionIncidence (rho : XiDivisorSupport) :
    Finset (XiZeroCopy × XiZeroCopy) :=
  xiZeroCopyFiber rho ×ˢ xiZeroCopyFiber (xiZeroLineConjEquiv rho)

/-- Fibre cardinality rewritten as analytic Xi order. -/
theorem card_xiZeroCopyFiber_eq_order_toNat (rho : XiDivisorSupport) :
    (xiZeroCopyFiber rho).card = (analyticOrderAt xi (rho : ℂ)).toNat := by
  rw [card_xiZeroCopyFiber, MeromorphicOn.AnalyticOnNhd.divisor_apply
    xi_analyticOnNhd_univ (Set.mem_univ _)]
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (xi_order_ne_top (rho : ℂ))
  rw [← hm]
  simp

/-- Support projection of copy-level critical-line reflection. -/
theorem xiZeroCopyLineConjEquiv_fst (q : XiZeroCopy) :
    (xiZeroCopyLineConjEquiv q).1 = xiZeroLineConjEquiv q.1 := rfl

/-- Copy-level reflection transports a fibre onto its support-level reflected fibre. -/
theorem xiZeroCopyLineConjEquiv_mem_reflectedFiber
    {rho : XiDivisorSupport} {q : XiZeroCopy}
    (hq : q ∈ xiZeroCopyFiber rho) :
    xiZeroCopyLineConjEquiv q ∈ xiZeroCopyFiber (xiZeroLineConjEquiv rho) := by
  rw [mem_xiZeroCopyFiber] at hq ⊢
  rw [xiZeroCopyLineConjEquiv_fst, hq]

/-- Analytic Xi order is preserved by support-level critical-line reflection. -/
theorem xi_orderAt_xiZeroLineConjEquiv (rho : XiDivisorSupport) :
    analyticOrderAt xi ((xiZeroLineConjEquiv rho : XiDivisorSupport) : ℂ) =
      analyticOrderAt xi (rho : ℂ) := by
  rw [xiZeroLineConjEquiv_apply]
  change analyticOrderAt xi (lineReflect (rho : ℂ)) = analyticOrderAt xi (rho : ℂ)
  exact xi_orderAt_lineReflect (rho : ℂ)

/-- **Coefficient-faithful local square law.** Reflection incidence has exactly `m_rho^(2 : ℕ)`
elements, one for each ordered pair of actual divisor-multiplicity copies. -/
theorem card_xiZeroCopyLineReflectionIncidence (rho : XiDivisorSupport) :
    (xiZeroCopyLineReflectionIncidence rho).card =
      ((analyticOrderAt xi (rho : ℂ)).toNat) ^ (2 : ℕ) := by
  rw [xiZeroCopyLineReflectionIncidence, Finset.card_product,
    card_xiZeroCopyFiber_eq_order_toNat, card_xiZeroCopyFiber_eq_order_toNat,
    xi_orderAt_xiZeroLineConjEquiv, pow_two]

/-- Every Xi support point carries a nonempty reflection-copy incidence. -/
theorem xiZeroCopyLineReflectionIncidence_nonempty (rho : XiDivisorSupport) :
    (xiZeroCopyLineReflectionIncidence rho).Nonempty := by
  rw [← Finset.card_pos, card_xiZeroCopyLineReflectionIncidence]
  exact Nat.pow_pos (Nat.pos_of_ne_zero
    (xi_order_toNat_ne_zero (xi_eq_zero_of_mem_divisor_support rho)))

/-- **Incidence endpoint.** RH says precisely that no right-half divisor support point can carry
its necessarily nonempty, coefficient-faithful line-reflection incidence. -/
theorem riemannHypothesis_iff_no_right_reflectionCopyIncidence :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport, 1 / 2 < (rho : ℂ).re →
        xiZeroCopyLineReflectionIncidence rho = ∅ := by
  constructor
  · intro hRH rho hright
    have hfix := (riemannHypothesis_iff_xiZeroLineConj_fixed.mp hRH) rho
    have hre := congrArg (fun tau : XiDivisorSupport => (tau : ℂ).re) hfix
    rw [xiZeroLineConjEquiv_apply] at hre
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hre
    exfalso
    linarith
  · intro hempty
    apply riemannHypothesis_iff_xiZeroLineConj_fixed.mpr
    intro rho
    by_contra hne
    have hre : (rho : ℂ).re ≠ 1 / 2 := by
      intro hre
      apply hne
      apply Subtype.ext
      rw [xiZeroLineConjEquiv_apply]
      exact lineReflect_eq_self_iff.mpr hre
    rcases lt_or_gt_of_ne hre with hleft | hright
    · let tau := xiZeroLineConjEquiv rho
      have htauRight : 1 / 2 < (tau : ℂ).re := by
        dsimp only [tau]
        rw [xiZeroLineConjEquiv_apply]
        simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
        linarith
      exact (Finset.nonempty_iff_ne_empty.mp
        (xiZeroCopyLineReflectionIncidence_nonempty tau))
          (hempty tau htauRight)
    · exact (Finset.nonempty_iff_ne_empty.mp
        (xiZeroCopyLineReflectionIncidence_nonempty rho))
          (hempty rho hright)

/-- Local canonical reflection charge is twice literal reflection-incidence cardinality. -/
theorem two_mul_card_xiZeroCopyLineReflectionIncidence (rho : XiDivisorSupport) :
    2 * (xiZeroCopyLineReflectionIncidence rho).card =
      2 * ((analyticOrderAt xi (rho : ℂ)).toNat) ^ (2 : ℕ) := by
  rw [card_xiZeroCopyLineReflectionIncidence]

/-! ## Prime-labelled source energy on reflection incidence -/

/-- Prime-labelled source coefficient before choosing a multiplicity copy. -/
def sourceZeroHorizontalPrimeCarrierAtSupport
    (rho : XiDivisorSupport) (p : Nat.Primes) : ℝ :=
  primeGammaCofinalBocksteinCoefficient
    (primeDepthBVWoldXiCenteredRate rho) p

/-- Copy-level carrier is constant on each exact multiplicity fibre. -/
theorem sourceZeroHorizontalPrimeCarrier_eq_support
    {rho : XiDivisorSupport} {q : XiZeroCopy}
    (hq : q ∈ xiZeroCopyFiber rho) (p : Nat.Primes) :
    sourceZeroHorizontalPrimeCarrier q p =
      sourceZeroHorizontalPrimeCarrierAtSupport rho p := by
  have hsupport : q.1 = rho := mem_xiZeroCopyFiber.mp hq
  rw [sourceZeroHorizontalPrimeCarrier,
    sourceZeroHorizontalPrimeCarrierAtSupport, hsupport]

/-- Support-level prime coefficient has exactly critical-line radical. -/
theorem sourceZeroHorizontalPrimeCarrierAtSupport_eq_zero_iff
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    sourceZeroHorizontalPrimeCarrierAtSupport rho p = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [sourceZeroHorizontalPrimeCarrierAtSupport,
    primeGammaCofinalBocksteinCoefficient_eq_zero_iff,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- Support-level line reflection reverses every retained prime coefficient. -/
@[simp] theorem sourceZeroHorizontalPrimeCarrierAtSupport_reflection
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    sourceZeroHorizontalPrimeCarrierAtSupport (xiZeroLineConjEquiv rho) p =
      -sourceZeroHorizontalPrimeCarrierAtSupport rho p := by
  rw [sourceZeroHorizontalPrimeCarrierAtSupport,
    sourceZeroHorizontalPrimeCarrierAtSupport,
    primeDepthBVWoldXiCenteredRate_reflection,
    primeGammaCofinalBocksteinCoefficient_neg]

/-- Every literal line-reflection incidence reverses the prime-labelled source coefficient. -/
theorem sourceZeroHorizontalPrimeCarrier_neg_on_lineReflectionIncidence
    {rho : XiDivisorSupport} {q r : XiZeroCopy}
    (hq : q ∈ xiZeroCopyFiber rho)
    (hr : r ∈ xiZeroCopyFiber (xiZeroLineConjEquiv rho))
    (p : Nat.Primes) :
    sourceZeroHorizontalPrimeCarrier r p =
      -sourceZeroHorizontalPrimeCarrier q p := by
  have hqSupport : q.1 = rho := mem_xiZeroCopyFiber.mp hq
  have hrSupport : r.1 = xiZeroLineConjEquiv rho := mem_xiZeroCopyFiber.mp hr
  have hreflectSupport :
      r.1 = (xiZeroCopyLineConjEquiv q).1 := by
    rw [hrSupport, xiZeroCopyLineConjEquiv_fst, hqSupport]
  have hsame :
      sourceZeroHorizontalPrimeCarrier r p =
        sourceZeroHorizontalPrimeCarrier (xiZeroCopyLineConjEquiv q) p := by
    rw [sourceZeroHorizontalPrimeCarrier,
      sourceZeroHorizontalPrimeCarrier, hreflectSupport]
  rw [hsame, sourceZeroHorizontalPrimeCarrier_reflection]

/-- Linear source coefficients cancel on every literal reflection incidence. -/
theorem sourceZeroHorizontalPrimeCarrier_add_eq_zero_on_lineReflectionIncidence
    {rho : XiDivisorSupport} {q r : XiZeroCopy}
    (hq : q ∈ xiZeroCopyFiber rho)
    (hr : r ∈ xiZeroCopyFiber (xiZeroLineConjEquiv rho))
    (p : Nat.Primes) :
    sourceZeroHorizontalPrimeCarrier q p +
        sourceZeroHorizontalPrimeCarrier r p = 0 := by
  rw [sourceZeroHorizontalPrimeCarrier_neg_on_lineReflectionIncidence hq hr p]
  ring

/-- Linear trace of prime coefficients across the literal reflection-incidence fibre. -/
def xiZeroCopyLineReflectionPrimeIncidenceTrace
    (rho : XiDivisorSupport) (p : Nat.Primes) : ℝ :=
  ∑ qr ∈ xiZeroCopyLineReflectionIncidence rho,
    (sourceZeroHorizontalPrimeCarrier qr.1 p +
      sourceZeroHorizontalPrimeCarrier qr.2 p)

/-- **Linear-blindness law.** Reflection-incidence trace vanishes for every divisor point,
including every off-line point carrying a nonempty incidence fibre. -/
theorem xiZeroCopyLineReflectionPrimeIncidenceTrace_eq_zero
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    xiZeroCopyLineReflectionPrimeIncidenceTrace rho p = 0 := by
  classical
  rw [xiZeroCopyLineReflectionPrimeIncidenceTrace, Finset.sum_eq_zero]
  intro qr hqr
  have hmem := Finset.mem_product.mp hqr
  exact sourceZeroHorizontalPrimeCarrier_add_eq_zero_on_lineReflectionIncidence
    hmem.1 hmem.2 p

/-- Coefficient-faithful source energy of one reflected multiplicity-copy incidence fibre.
The minus sign converts the product of the two opposite orientations into a positive square. -/
def xiZeroCopyLineReflectionPrimeIncidenceEnergy
    (rho : XiDivisorSupport) (p : Nat.Primes) : ℝ :=
  ∑ qr ∈ xiZeroCopyLineReflectionIncidence rho,
    -(sourceZeroHorizontalPrimeCarrier qr.1 p *
      sourceZeroHorizontalPrimeCarrier qr.2 p)

/-- **Quadratic source-incidence law.** Unconditional linear reflection cancellation becomes one
positive source square for every literal pair of divisor-multiplicity copies. -/
theorem xiZeroCopyLineReflectionPrimeIncidenceEnergy_eq
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    xiZeroCopyLineReflectionPrimeIncidenceEnergy rho p =
      (((analyticOrderAt xi (rho : ℂ)).toNat : ℝ) ^ (2 : ℕ)) *
        sourceZeroHorizontalPrimeCarrierAtSupport rho p ^ (2 : ℕ) := by
  classical
  rw [xiZeroCopyLineReflectionPrimeIncidenceEnergy]
  calc
    (∑ qr ∈ xiZeroCopyLineReflectionIncidence rho,
        -(sourceZeroHorizontalPrimeCarrier qr.1 p *
          sourceZeroHorizontalPrimeCarrier qr.2 p)) =
        ∑ _qr ∈ xiZeroCopyLineReflectionIncidence rho,
          sourceZeroHorizontalPrimeCarrierAtSupport rho p ^ (2 : ℕ) := by
      apply Finset.sum_congr rfl
      intro qr hqr
      have hmem := Finset.mem_product.mp hqr
      have hq := sourceZeroHorizontalPrimeCarrier_eq_support hmem.1 p
      have hreflect :=
        sourceZeroHorizontalPrimeCarrier_neg_on_lineReflectionIncidence
          hmem.1 hmem.2 p
      rw [hq, hreflect, hq]
      ring
    _ = ((xiZeroCopyLineReflectionIncidence rho).card : ℝ) *
          sourceZeroHorizontalPrimeCarrierAtSupport rho p ^ (2 : ℕ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = (((analyticOrderAt xi (rho : ℂ)).toNat : ℝ) ^ (2 : ℕ)) *
          sourceZeroHorizontalPrimeCarrierAtSupport rho p ^ (2 : ℕ) := by
      rw [card_xiZeroCopyLineReflectionIncidence]
      norm_cast

/-- Quadratic incidence energy is reflection invariant although every linear coefficient is odd. -/
@[simp] theorem xiZeroCopyLineReflectionPrimeIncidenceEnergy_reflection
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    xiZeroCopyLineReflectionPrimeIncidenceEnergy (xiZeroLineConjEquiv rho) p =
      xiZeroCopyLineReflectionPrimeIncidenceEnergy rho p := by
  rw [xiZeroCopyLineReflectionPrimeIncidenceEnergy_eq,
    xiZeroCopyLineReflectionPrimeIncidenceEnergy_eq,
    xi_orderAt_xiZeroLineConjEquiv,
    sourceZeroHorizontalPrimeCarrierAtSupport_reflection]
  ring

/-- Source incidence energy is nonnegative at every support point. -/
theorem xiZeroCopyLineReflectionPrimeIncidenceEnergy_nonneg
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    0 ≤ xiZeroCopyLineReflectionPrimeIncidenceEnergy rho p := by
  rw [xiZeroCopyLineReflectionPrimeIncidenceEnergy_eq]
  positivity

/-- Source incidence energy vanishes exactly on the critical line. -/
theorem xiZeroCopyLineReflectionPrimeIncidenceEnergy_eq_zero_iff
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    xiZeroCopyLineReflectionPrimeIncidenceEnergy rho p = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [xiZeroCopyLineReflectionPrimeIncidenceEnergy_eq, mul_eq_zero]
  have horder : ((analyticOrderAt xi (rho : ℂ)).toNat : ℝ) ^ (2 : ℕ) ≠ 0 := by
    exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr
      (xi_order_toNat_ne_zero (xi_eq_zero_of_mem_divisor_support rho)))
  simp only [horder, false_or, sq_eq_zero_iff]
  exact sourceZeroHorizontalPrimeCarrierAtSupport_eq_zero_iff rho p

/-- Off-line source incidence energy is strictly positive at every retained prime label. -/
theorem xiZeroCopyLineReflectionPrimeIncidenceEnergy_pos_of_offLine
    (rho : XiDivisorSupport) (p : Nat.Primes)
    (hoff : (rho : ℂ).re ≠ 1 / 2) :
    0 < xiZeroCopyLineReflectionPrimeIncidenceEnergy rho p := by
  exact lt_of_le_of_ne
    (xiZeroCopyLineReflectionPrimeIncidenceEnergy_nonneg rho p)
    (Ne.symm ((not_congr
      (xiZeroCopyLineReflectionPrimeIncidenceEnergy_eq_zero_iff rho p)).mpr hoff))

/-- **Normalized source reconstruction.** Away from the critical line, dividing by the retained
prime coefficient square recovers literal reflection-incidence cardinality, hence exact `m^(2 : ℕ)`.
This normalization is coefficient-faithful but singular at the desired critical radical. -/
theorem xiZeroCopyLineReflectionPrimeIncidenceEnergy_div_sq
    (rho : XiDivisorSupport) (p : Nat.Primes)
    (hoff : (rho : ℂ).re ≠ 1 / 2) :
    xiZeroCopyLineReflectionPrimeIncidenceEnergy rho p /
        sourceZeroHorizontalPrimeCarrierAtSupport rho p ^ (2 : ℕ) =
      ((analyticOrderAt xi (rho : ℂ)).toNat : ℝ) ^ (2 : ℕ) := by
  have hcoeff : sourceZeroHorizontalPrimeCarrierAtSupport rho p ≠ 0 :=
    (not_congr
      (sourceZeroHorizontalPrimeCarrierAtSupport_eq_zero_iff rho p)).mpr hoff
  rw [xiZeroCopyLineReflectionPrimeIncidenceEnergy_eq]
  field_simp

/-- The normalized prime-incidence energy is exactly the real cardinality of the literal
reflection-copy incidence set. -/
theorem xiZeroCopyLineReflectionPrimeIncidenceEnergy_div_sq_eq_card
    (rho : XiDivisorSupport) (p : Nat.Primes)
    (hoff : (rho : ℂ).re ≠ 1 / 2) :
    xiZeroCopyLineReflectionPrimeIncidenceEnergy rho p /
        sourceZeroHorizontalPrimeCarrierAtSupport rho p ^ (2 : ℕ) =
      (xiZeroCopyLineReflectionIncidence rho).card := by
  rw [xiZeroCopyLineReflectionPrimeIncidenceEnergy_div_sq rho p hoff,
    card_xiZeroCopyLineReflectionIncidence]
  norm_cast

/-- **One-prime source-energy endpoint.** At any fixed retained ordinary prime, global vanishing
of coefficient-faithful reflection-incidence energy is exactly RH. -/
theorem riemannHypothesis_iff_forall_reflectionPrimeIncidenceEnergy_eq_zero
    (p : Nat.Primes) :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        xiZeroCopyLineReflectionPrimeIncidenceEnergy rho p = 0 := by
  constructor
  · intro hRH rho
    exact (xiZeroCopyLineReflectionPrimeIncidenceEnergy_eq_zero_iff rho p).2
      (xi_divisor_support_re_eq_half_of_rh hRH rho)
  · intro henergy
    rw [riemannHypothesis_iff_xi_zero_re_eq_half]
    intro rho hzero
    let support : XiDivisorSupport :=
      ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
    exact (xiZeroCopyLineReflectionPrimeIncidenceEnergy_eq_zero_iff support p).1
      (henergy support)

end

end RHTower
