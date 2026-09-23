import GaloisForLFunctions.RHTower.CCMRestrictedWeilPoleParityWallClosure

/-!
# Literal common-clock envelope for finite completed parity heads

The homogeneous parity-wall transgression has an exact Volterra primitive.  For every fixed
literal finite arithmetic head, its relative-clock channel is recovered from its common-age
channel without a residual polar, Gamma, or arithmetic forcing:

`R(s) + cosh(s) P(s) - 2 ∫_r^s sinh(t) P(t) dt = R(r) + cosh(r) P(r)`.

This closes the fixed-head common-clock envelope.  It is an equality only: the remaining
RH-bearing task is a lower bound for the actual moving finite head, not an omitted completion
term.
-/

open Set MeasureTheory Filter
open scoped Topology

noncomputable section

namespace RHTower

/-- **Finite literal common-clock envelope.**  Once the completed polar--Gamma wall is
normalized, every fixed finite head obeys an exact Volterra transport law between positive
apertures.  The statement retains the literal common-age channel under the integral. -/
theorem ccmWeilParityHead_commonClockEnvelope
    (S : Finset ℕ) (r s : SuzukiPositiveAperture) (hrs : r.1 ≤ s.1) :
    ccmWeilParityClockHead S s.1 +
        Real.cosh s.1 * ccmWeilParityAgeHead S s.1 -
          2 * ∫ t in r.1..s.1,
            Real.sinh t * ccmWeilParityAgeHead S t =
      ccmWeilParityClockHead S r.1 +
        Real.cosh r.1 * ccmWeilParityAgeHead S r.1 := by
  let P : ℝ → ℝ := ccmWeilParityAgeHead S
  let R : ℝ → ℝ := ccmWeilParityClockHead S
  have hpos : ∀ t ∈ uIcc r.1 s.1, 0 < t := by
    intro t ht
    rw [uIcc_of_le hrs] at ht
    exact lt_of_lt_of_le r.2 ht.1
  have hPderiv : ∀ t ∈ uIcc r.1 s.1,
      HasDerivAt P (deriv P t) t := by
    intro t ht
    have h := hasDerivAt_ccmWeilParityAgeHead S ⟨t, hpos t ht⟩
    change HasDerivAt P (deriv P t) t
    rw [h.deriv]
    exact h
  have hderiv : ∀ t ∈ uIcc r.1 s.1,
      HasDerivAt (fun x => R x + Real.cosh x * P x)
        (2 * Real.sinh t * P t) t := by
    intro t ht
    let a : SuzukiPositiveAperture := ⟨t, hpos t ht⟩
    let dR : ℝ := -4 * ccmWeilPoleCrossSmoothSlope a.1 +
      ∑ n ∈ S, criticalMellinAtomWeight n * (16 * Real.cosh (Real.log n / 2))
    let dP : ℝ := 4 * ccmWeilPoleDiagonalSmoothSlope a.1 +
      ∑ n ∈ S, criticalMellinAtomWeight n *
        (-16 * Real.cosh (a.1 - Real.log n / 2))
    have hR : HasDerivAt (ccmWeilParityClockHead S) dR t := by
      simpa only [a, dR] using hasDerivAt_ccmWeilParityClockHead S a
    have hP : HasDerivAt (ccmWeilParityAgeHead S) dP t := by
      simpa only [a, dP] using hasDerivAt_ccmWeilParityAgeHead S a
    have hzero := ccmWeilParityHeadTransgression_zero S a
    have hsum := hR.add ((Real.hasDerivAt_cosh t).mul hP)
    have hzero' : dR + Real.cosh t * dP -
        Real.sinh t * ccmWeilParityAgeHead S t = 0 := by
      rw [← hR.deriv, ← hP.deriv]
      simpa only [a] using hzero
    have hscalar : dR +
        (Real.sinh t * ccmWeilParityAgeHead S t + Real.cosh t * dP) =
          2 * Real.sinh t * ccmWeilParityAgeHead S t := by
      linarith
    change HasDerivAt (ccmWeilParityClockHead S +
        Real.cosh * ccmWeilParityAgeHead S)
      (2 * Real.sinh t * ccmWeilParityAgeHead S t) t
    exact hsum.congr_deriv hscalar
  have hPcont : ContinuousOn P (uIcc r.1 s.1) := by
    intro t ht
    exact (hPderiv t ht).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (fun t => 2 * Real.sinh t * P t)
      volume r.1 s.1 := by
    apply ContinuousOn.intervalIntegrable
    exact (continuousOn_const.mul Real.continuous_sinh.continuousOn).mul hPcont
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hscale : (∫ t in r.1..s.1, 2 * Real.sinh t * P t) =
      2 * ∫ t in r.1..s.1, Real.sinh t * P t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  rw [hscale] at hftc
  change R s.1 + Real.cosh s.1 * P s.1 -
      2 * ∫ t in r.1..s.1, Real.sinh t * P t =
    R r.1 + Real.cosh r.1 * P r.1
  linarith

/-- A literal common-age atom is born with zero value at its physical clock. -/
theorem ccmWeilWallAgeMode_entry (n : ℕ) :
    ccmWeilWallAgeMode n (Real.log n / 2) = 0 := by
  unfold ccmWeilWallAgeMode
  ring_nf
  simp

/-- A literal relative-clock atom is born with zero value at its physical clock. -/
theorem ccmWeilWallClockMode_entry (n : ℕ) :
    ccmWeilWallClockMode n (Real.log n / 2) = 0 := by
  unfold ccmWeilWallClockMode
  ring_nf

/-- Adding a newly admitted atom creates no common-age value jump. -/
theorem ccmWeilParityAgeHead_insert_entry
    (S : Finset ℕ) (n : ℕ) (hn : n ∉ S) :
    ccmWeilParityAgeHead (insert n S) (Real.log n / 2) =
      ccmWeilParityAgeHead S (Real.log n / 2) := by
  unfold ccmWeilParityAgeHead
  rw [Finset.sum_insert hn, ccmWeilWallAgeMode_entry]
  ring

/-- Adding a newly admitted atom creates no relative-clock value jump. -/
theorem ccmWeilParityClockHead_insert_entry
    (S : Finset ℕ) (n : ℕ) (hn : n ∉ S) :
    ccmWeilParityClockHead (insert n S) (Real.log n / 2) =
      ccmWeilParityClockHead S (Real.log n / 2) := by
  unfold ccmWeilParityClockHead
  rw [Finset.sum_insert hn, ccmWeilWallClockMode_entry]
  ring

/-- **Covariant entry neutrality.**  At every genuine arithmetic entry, the ordinary slopes can
jump, but their literal common-clock covariant combination does not.  This is the exact gluing
condition needed to concatenate fixed-head envelopes across moving cutoffs. -/
theorem ccmWeilParityHead_insert_covariantSlope_entry
    (S : Finset ℕ) (n : ℕ) (hn : n ∉ S) (hnone : 1 < n) :
    deriv (ccmWeilParityClockHead (insert n S)) (Real.log n / 2) -
        deriv (ccmWeilParityClockHead S) (Real.log n / 2) +
      Real.cosh (Real.log n / 2) *
        (deriv (ccmWeilParityAgeHead (insert n S)) (Real.log n / 2) -
          deriv (ccmWeilParityAgeHead S) (Real.log n / 2)) = 0 := by
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hnone
  let a : SuzukiPositiveAperture :=
    ⟨Real.log n / 2, div_pos (Real.log_pos hnreal) (by norm_num)⟩
  have hnew := ccmWeilParityHeadTransgression_zero (insert n S) a
  have hold := ccmWeilParityHeadTransgression_zero S a
  have hvalue := ccmWeilParityAgeHead_insert_entry S n hn
  change deriv (ccmWeilParityClockHead (insert n S)) a.1 -
        deriv (ccmWeilParityClockHead S) a.1 +
      Real.cosh a.1 *
        (deriv (ccmWeilParityAgeHead (insert n S)) a.1 -
          deriv (ccmWeilParityAgeHead S) a.1) = 0
  rw [hvalue] at hnew
  linarith

/-- The individual literal wall modes have the same exact common-clock Volterra primitive. -/
theorem ccmWeilWallMode_commonClockEnvelope
    (n : ℕ) (r s : ℝ) (_hrs : r ≤ s) :
    ccmWeilWallClockMode n s + Real.cosh s * ccmWeilWallAgeMode n s -
        2 * ∫ t in r..s, Real.sinh t * ccmWeilWallAgeMode n t =
      ccmWeilWallClockMode n r + Real.cosh r * ccmWeilWallAgeMode n r := by
  have hPderiv : ∀ t ∈ uIcc r s,
      HasDerivAt (ccmWeilWallAgeMode n) (deriv (ccmWeilWallAgeMode n) t) t := by
    intro t ht
    have h := hasDerivAt_ccmWeilWallAgeMode n t
    rw [h.deriv]
    exact h
  have hderiv : ∀ t ∈ uIcc r s,
      HasDerivAt (ccmWeilWallClockMode n + Real.cosh * ccmWeilWallAgeMode n)
        (2 * Real.sinh t * ccmWeilWallAgeMode n t) t := by
    intro t ht
    let dR : ℝ := 16 * Real.cosh (Real.log n / 2)
    let dP : ℝ := -16 * Real.cosh (t - Real.log n / 2)
    have hR : HasDerivAt (ccmWeilWallClockMode n) dR t := by
      simpa only [dR] using hasDerivAt_ccmWeilWallClockMode n t
    have hP : HasDerivAt (ccmWeilWallAgeMode n) dP t := by
      simpa only [dP] using hasDerivAt_ccmWeilWallAgeMode n t
    have hzero := ccmWeilWallModeTransgression_atom n t
    have hsum := hR.add ((Real.hasDerivAt_cosh t).mul hP)
    have hzero' : dR + Real.cosh t * dP -
        Real.sinh t * ccmWeilWallAgeMode n t = 0 := by
      rw [← hR.deriv, ← hP.deriv]
      exact hzero
    have hscalar : dR +
        (Real.sinh t * ccmWeilWallAgeMode n t + Real.cosh t * dP) =
          2 * Real.sinh t * ccmWeilWallAgeMode n t := by
      linarith
    exact hsum.congr_deriv hscalar
  have hPcont : ContinuousOn (ccmWeilWallAgeMode n) (uIcc r s) := by
    intro t ht
    exact (hPderiv t ht).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (fun t => 2 * Real.sinh t * ccmWeilWallAgeMode n t)
      volume r s := by
    apply ContinuousOn.intervalIntegrable
    exact (continuousOn_const.mul Real.continuous_sinh.continuousOn).mul hPcont
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hscale : (∫ t in r..s, 2 * Real.sinh t * ccmWeilWallAgeMode n t) =
      2 * ∫ t in r..s, Real.sinh t * ccmWeilWallAgeMode n t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  rw [hscale] at hftc
  change 2 * ∫ t in r..s, Real.sinh t * ccmWeilWallAgeMode n t =
      (ccmWeilWallClockMode n s + Real.cosh s * ccmWeilWallAgeMode n s) -
        (ccmWeilWallClockMode n r + Real.cosh r * ccmWeilWallAgeMode n r) at hftc
  linarith

/-- A wall mode's full future transport starts exactly at its zero-valued entry clock. -/
theorem ccmWeilWallMode_commonClock_from_entry
    (n : ℕ) (s : ℝ) (hs : Real.log n / 2 ≤ s) :
    ccmWeilWallClockMode n s + Real.cosh s * ccmWeilWallAgeMode n s =
      2 * ∫ t in (Real.log n / 2)..s,
        Real.sinh t * ccmWeilWallAgeMode n t := by
  have h := ccmWeilWallMode_commonClockEnvelope n (Real.log n / 2) s hs
  rw [ccmWeilWallAgeMode_entry, ccmWeilWallClockMode_entry] at h
  linarith

/-- A genuinely admitted wall atom contributes a nonpositive amount to the common-clock
primitive.  Thus moving the literal cutoff cannot manufacture common-age coercivity from entry
terms alone. -/
theorem ccmWeilWallMode_commonClock_from_entry_nonpos
    (n : ℕ) (hn : 1 < n) (s : ℝ) (hs : Real.log n / 2 ≤ s) :
    ccmWeilWallClockMode n s + Real.cosh s * ccmWeilWallAgeMode n s ≤ 0 := by
  rw [ccmWeilWallMode_commonClock_from_entry n s hs]
  have hepos : 0 < Real.log n / 2 := by
    have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
    exact div_pos (Real.log_pos hnreal) (by norm_num)
  have hint : (∫ t in (Real.log n / 2)..s,
      Real.sinh t * ccmWeilWallAgeMode n t) ≤ 0 := by
    rw [intervalIntegral.integral_of_le hs]
    apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htpos : 0 ≤ t := hepos.le.trans ht.1.le
    have htsinh : 0 ≤ Real.sinh t := Real.sinh_nonneg_iff.mpr htpos
    have hagemode : ccmWeilWallAgeMode n t ≤ 0 := by
      unfold ccmWeilWallAgeMode
      have harg : 0 ≤ t - Real.log n / 2 := sub_nonneg.mpr ht.1.le
      have hsinh : 0 ≤ Real.sinh (t - Real.log n / 2) :=
        Real.sinh_nonneg_iff.mpr harg
      nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos htsinh hagemode
  linarith

/-- The literal coefficient-weighted entry transport is nonpositive. -/
theorem ccmWeilWallMode_weightedEntryTransport_nonpos
    (n : ℕ) (hn : 1 < n) (s : ℝ) (hs : Real.log n / 2 ≤ s) :
    2 * criticalMellinAtomWeight n *
      (∫ t in (Real.log n / 2)..s,
        Real.sinh t * ccmWeilWallAgeMode n t) ≤ 0 := by
  have hmode := ccmWeilWallMode_commonClock_from_entry_nonpos n hn s hs
  rw [ccmWeilWallMode_commonClock_from_entry n s hs] at hmode
  have hint : (∫ t in (Real.log n / 2)..s,
      Real.sinh t * ccmWeilWallAgeMode n t) ≤ 0 := by
    linarith
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (by norm_num) (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer n)) hint

/-- A finite entering collar is nonpositive before any source term is estimated. -/
theorem ccmWeilParityHead_union_commonClock_collar_nonpos
    (T : Finset ℕ) (s : SuzukiPositiveAperture)
    (hT : ∀ n ∈ T, 1 < n) (hentry : ∀ n ∈ T, Real.log n / 2 ≤ s.1) :
    2 * ∑ n ∈ T, criticalMellinAtomWeight n *
      ∫ t in (Real.log n / 2)..s.1,
        Real.sinh t * ccmWeilWallAgeMode n t ≤ 0 := by
  rw [Finset.mul_sum]
  apply Finset.sum_nonpos
  intro n hn
  have h := ccmWeilWallMode_weightedEntryTransport_nonpos n
    (hT n hn) s.1 (hentry n hn)
  nlinarith

/-- **Finite moving-head envelope.**  Extending a literal head by any disjoint finite family is
exactly the old fixed-head Volterra transport plus each new atom transported from its own zero
clock.  This is the finite concatenation identity needed for the actual moving cutoff. -/
theorem ccmWeilParityHead_union_commonClockEnvelope
    (S T : Finset ℕ) (hdisj : Disjoint S T)
    (r s : SuzukiPositiveAperture) (hrs : r.1 ≤ s.1)
    (hentry : ∀ n ∈ T, Real.log n / 2 ≤ s.1) :
    ccmWeilParityClockHead (S ∪ T) s.1 +
        Real.cosh s.1 * ccmWeilParityAgeHead (S ∪ T) s.1 =
      ccmWeilParityClockHead S r.1 +
        Real.cosh r.1 * ccmWeilParityAgeHead S r.1 +
          (2 * ∫ t in r.1..s.1, Real.sinh t * ccmWeilParityAgeHead S t) +
            (2 * ∑ n ∈ T, criticalMellinAtomWeight n *
              ∫ t in (Real.log n / 2)..s.1,
                Real.sinh t * ccmWeilWallAgeMode n t) := by
  have hfixed := ccmWeilParityHead_commonClockEnvelope S r s hrs
  have hclock : ccmWeilParityClockHead (S ∪ T) s.1 =
      ccmWeilParityClockHead S s.1 +
        ∑ n ∈ T, criticalMellinAtomWeight n * ccmWeilWallClockMode n s.1 := by
    unfold ccmWeilParityClockHead
    rw [Finset.sum_union hdisj]
    ring
  have hage : ccmWeilParityAgeHead (S ∪ T) s.1 =
      ccmWeilParityAgeHead S s.1 +
        ∑ n ∈ T, criticalMellinAtomWeight n * ccmWeilWallAgeMode n s.1 := by
    unfold ccmWeilParityAgeHead
    rw [Finset.sum_union hdisj]
    ring
  have hnew :
      (∑ n ∈ T, criticalMellinAtomWeight n * ccmWeilWallClockMode n s.1) +
        Real.cosh s.1 *
          (∑ n ∈ T, criticalMellinAtomWeight n * ccmWeilWallAgeMode n s.1) =
        2 * ∑ n ∈ T, criticalMellinAtomWeight n *
          ∫ t in (Real.log n / 2)..s.1,
            Real.sinh t * ccmWeilWallAgeMode n t := by
    calc
      (∑ n ∈ T, criticalMellinAtomWeight n * ccmWeilWallClockMode n s.1) +
          Real.cosh s.1 *
            (∑ n ∈ T, criticalMellinAtomWeight n * ccmWeilWallAgeMode n s.1) =
        T.sum (fun x => criticalMellinAtomWeight x * ccmWeilWallClockMode x s.1 +
          Real.cosh s.1 * criticalMellinAtomWeight x * ccmWeilWallAgeMode x s.1) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro x hx
          ring
      _ = T.sum (fun x => criticalMellinAtomWeight x *
          (ccmWeilWallClockMode x s.1 +
            Real.cosh s.1 * ccmWeilWallAgeMode x s.1)) := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
      _ = T.sum (fun x => criticalMellinAtomWeight x *
          (2 * ∫ t in (Real.log x / 2)..s.1,
            Real.sinh t * ccmWeilWallAgeMode x t)) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [ccmWeilWallMode_commonClock_from_entry x s.1 (hentry x hx)]
      _ = 2 * ∑ x ∈ T, criticalMellinAtomWeight x *
          ∫ t in (Real.log x / 2)..s.1,
            Real.sinh t * ccmWeilWallAgeMode x t := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          ring
  have hbase : ccmWeilParityClockHead S s.1 +
      Real.cosh s.1 * ccmWeilParityAgeHead S s.1 =
    ccmWeilParityClockHead S r.1 +
      Real.cosh r.1 * ccmWeilParityAgeHead S r.1 +
        2 * ∫ t in r.1..s.1, Real.sinh t * ccmWeilParityAgeHead S t := by
    linarith [hfixed]
  rw [hclock, hage]
  calc
    ccmWeilParityClockHead S s.1 +
        ∑ n ∈ T, criticalMellinAtomWeight n * ccmWeilWallClockMode n s.1 +
      Real.cosh s.1 *
        (ccmWeilParityAgeHead S s.1 +
          ∑ n ∈ T, criticalMellinAtomWeight n * ccmWeilWallAgeMode n s.1) =
      (ccmWeilParityClockHead S s.1 +
        Real.cosh s.1 * ccmWeilParityAgeHead S s.1) +
      ((∑ n ∈ T, criticalMellinAtomWeight n * ccmWeilWallClockMode n s.1) +
        Real.cosh s.1 *
          (∑ n ∈ T, criticalMellinAtomWeight n * ccmWeilWallAgeMode n s.1)) := by ring
    _ = (ccmWeilParityClockHead S s.1 +
        Real.cosh s.1 * ccmWeilParityAgeHead S s.1) +
      2 * ∑ n ∈ T, criticalMellinAtomWeight n *
          ∫ t in (Real.log n / 2)..s.1,
            Real.sinh t * ccmWeilWallAgeMode n t := by rw [hnew]
    _ = _ := by rw [hbase]

/-- Canonical arithmetic cutoffs are monotone, split into an old head and a disjoint entering
collar, and every collar atom has entered by the later aperture. -/
private theorem ccmWeilParityCutoff_set_facts
    (r s : SuzukiPositiveAperture) (hrs : r.1 ≤ s.1) :
    let Sr : Finset ℕ := Finset.Icc 2 (Nat.floor (Real.exp (2 * r.1)))
    let Ss : Finset ℕ := Finset.Icc 2 (Nat.floor (Real.exp (2 * s.1)))
    Sr ⊆ Ss ∧ Disjoint Sr (Ss \ Sr) ∧ Sr ∪ (Ss \ Sr) = Ss ∧
      (∀ n ∈ Ss \ Sr, Real.log n / 2 ≤ s.1) := by
  dsimp
  have hfloor : Nat.floor (Real.exp (2 * r.1)) ≤
      Nat.floor (Real.exp (2 * s.1)) := by
    apply Nat.floor_mono
    exact Real.exp_le_exp.mpr (by linarith)
  have hsubset : Finset.Icc 2 (Nat.floor (Real.exp (2 * r.1))) ⊆
      Finset.Icc 2 (Nat.floor (Real.exp (2 * s.1))) := by
    exact Finset.Icc_subset_Icc le_rfl hfloor
  refine ⟨hsubset, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro n hnS hnnew
    simp only [Finset.mem_sdiff] at hnnew
    exact hnnew.2 hnS
  · exact Finset.union_sdiff_of_subset hsubset
  · intro n hn
    simp only [Finset.mem_sdiff, Finset.mem_Icc] at hn
    have hn2 : 2 ≤ n := hn.1.1
    have hnupper : n ≤ Nat.floor (Real.exp (2 * s.1)) := hn.1.2
    have hnupperReal : (n : ℝ) ≤ (Nat.floor (Real.exp (2 * s.1)) : ℝ) := by
      exact_mod_cast hnupper
    have hfloorReal : (Nat.floor (Real.exp (2 * s.1)) : ℝ) ≤ Real.exp (2 * s.1) :=
      Nat.floor_le (Real.exp_pos _).le
    have hnexp : (n : ℝ) ≤ Real.exp (2 * s.1) :=
      hnupperReal.trans hfloorReal
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (show 0 < n by omega)
    have hlog : Real.log (n : ℝ) ≤ 2 * s.1 := by
      rw [Real.log_le_iff_le_exp hnpos]
      exact hnexp
    linarith

/-- **Literal moving-cutoff common-clock envelope.**  The canonical finite head at aperture
`s` is exactly the older head at `r`, its Volterra transport, and the individual transports of
the newly admitted arithmetic collar.  No asymptotic replacement, completion remainder, or
coefficient is discarded. -/
theorem ccmWeilParityCutoff_commonClockEnvelope
    (r s : SuzukiPositiveAperture) (hrs : r.1 ≤ s.1) :
    let Sr : Finset ℕ := Finset.Icc 2 (Nat.floor (Real.exp (2 * r.1)))
    let Ss : Finset ℕ := Finset.Icc 2 (Nat.floor (Real.exp (2 * s.1)))
    ccmWeilParityClockHead Ss s.1 + Real.cosh s.1 * ccmWeilParityAgeHead Ss s.1 =
      ccmWeilParityClockHead Sr r.1 + Real.cosh r.1 * ccmWeilParityAgeHead Sr r.1 +
        (2 * ∫ t in r.1..s.1, Real.sinh t * ccmWeilParityAgeHead Sr t) +
          (2 * ∑ n ∈ Ss \ Sr, criticalMellinAtomWeight n *
            ∫ t in (Real.log n / 2)..s.1,
              Real.sinh t * ccmWeilWallAgeMode n t) := by
  dsimp
  obtain ⟨hsubset, hdisj, hcover, hentry⟩ := ccmWeilParityCutoff_set_facts r s hrs
  simpa only [hcover] using
    ccmWeilParityHead_union_commonClockEnvelope
      (Finset.Icc 2 (Nat.floor (Real.exp (2 * r.1))))
      (Finset.Icc 2 (Nat.floor (Real.exp (2 * s.1))) \
        Finset.Icc 2 (Nat.floor (Real.exp (2 * r.1))))
      hdisj r s hrs hentry

/-- On canonical literal cutoffs, the whole entering collar has nonpositive common-clock
charge.  The only possible positive lower-bound mechanism is therefore the already-admitted,
source-faithful joint block; it cannot be supplied by counting new prime entries. -/
theorem ccmWeilParityCutoff_commonClock_collar_nonpos
    (r s : SuzukiPositiveAperture) (hrs : r.1 ≤ s.1) :
    let Sr : Finset ℕ := Finset.Icc 2 (Nat.floor (Real.exp (2 * r.1)))
    let Ss : Finset ℕ := Finset.Icc 2 (Nat.floor (Real.exp (2 * s.1)))
    2 * ∑ n ∈ Ss \ Sr, criticalMellinAtomWeight n *
      ∫ t in (Real.log n / 2)..s.1,
        Real.sinh t * ccmWeilWallAgeMode n t ≤ 0 := by
  dsimp
  obtain ⟨hsubset, hdisj, hcover, hentry⟩ := ccmWeilParityCutoff_set_facts r s hrs
  apply ccmWeilParityHead_union_commonClock_collar_nonpos
  · intro n hn
    simp only [Finset.mem_sdiff, Finset.mem_Icc] at hn
    omega
  · exact hentry

/-- **Literal arithmetic cannot supply common-clock coercivity.**  At every canonical cutoff,
the entire prime-power contribution to the common-clock charge is nonpositive.  Hence the full
literal charge is bounded above by the completed polar--Gamma smooth channel alone.  This is an
operator-specific obstruction: it does not transfer to the distinct actual Gamma--Slepian heads. -/
theorem ccmWeilParityCutoff_commonClock_le_smooth
    (s : SuzukiPositiveAperture) :
    let S : Finset ℕ := Finset.Icc 2 (Nat.floor (Real.exp (2 * s.1)))
    ccmWeilParityClockHead S s.1 + Real.cosh s.1 * ccmWeilParityAgeHead S s.1 ≤
      -4 * ccmWeilPoleCrossSmooth s.1 +
        Real.cosh s.1 * (4 * ccmWeilPoleDiagonalSmooth s.1) := by
  dsimp
  let S : Finset ℕ := Finset.Icc 2 (Nat.floor (Real.exp (2 * s.1)))
  have hsum : ∑ n ∈ S, criticalMellinAtomWeight n *
      (ccmWeilWallClockMode n s.1 +
        Real.cosh s.1 * ccmWeilWallAgeMode n s.1) ≤ 0 := by
    apply Finset.sum_nonpos
    intro n hn
    have hnmem : n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * s.1))) := by
      simpa only [S] using hn
    simp only [Finset.mem_Icc] at hnmem
    have hn2 : 1 < n := by omega
    have hnupper : n ≤ Nat.floor (Real.exp (2 * s.1)) := hnmem.2
    have hnupperReal : (n : ℝ) ≤ (Nat.floor (Real.exp (2 * s.1)) : ℝ) := by
      exact_mod_cast hnupper
    have hfloorReal : (Nat.floor (Real.exp (2 * s.1)) : ℝ) ≤ Real.exp (2 * s.1) :=
      Nat.floor_le (Real.exp_pos _).le
    have hnexp : (n : ℝ) ≤ Real.exp (2 * s.1) := hnupperReal.trans hfloorReal
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hentry : Real.log n / 2 ≤ s.1 := by
      have hlog : Real.log (n : ℝ) ≤ 2 * s.1 := by
        rw [Real.log_le_iff_le_exp hnpos]
        exact hnexp
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer n)
      (ccmWeilWallMode_commonClock_from_entry_nonpos n hn2 s.1 hentry)
  change (-4 * ccmWeilPoleCrossSmooth s.1 +
      ∑ n ∈ S, criticalMellinAtomWeight n * ccmWeilWallClockMode n s.1) +
      Real.cosh s.1 *
        (4 * ccmWeilPoleDiagonalSmooth s.1 +
          ∑ n ∈ S, criticalMellinAtomWeight n * ccmWeilWallAgeMode n s.1) ≤ _
  calc
    (-4 * ccmWeilPoleCrossSmooth s.1 +
        ∑ n ∈ S, criticalMellinAtomWeight n * ccmWeilWallClockMode n s.1) +
        Real.cosh s.1 *
          (4 * ccmWeilPoleDiagonalSmooth s.1 +
            ∑ n ∈ S, criticalMellinAtomWeight n * ccmWeilWallAgeMode n s.1) =
      (-4 * ccmWeilPoleCrossSmooth s.1 +
        Real.cosh s.1 * (4 * ccmWeilPoleDiagonalSmooth s.1)) +
          ∑ n ∈ S, criticalMellinAtomWeight n *
            (ccmWeilWallClockMode n s.1 +
              Real.cosh s.1 * ccmWeilWallAgeMode n s.1) := by
        calc
          _ = (-4 * ccmWeilPoleCrossSmooth s.1 +
              Real.cosh s.1 * (4 * ccmWeilPoleDiagonalSmooth s.1)) +
              ((∑ n ∈ S, criticalMellinAtomWeight n * ccmWeilWallClockMode n s.1) +
                ∑ n ∈ S, Real.cosh s.1 * criticalMellinAtomWeight n *
                  ccmWeilWallAgeMode n s.1) := by
            rw [mul_add, Finset.mul_sum]
            ring
          _ = (-4 * ccmWeilPoleCrossSmooth s.1 +
              Real.cosh s.1 * (4 * ccmWeilPoleDiagonalSmooth s.1)) +
              ∑ n ∈ S, (criticalMellinAtomWeight n * ccmWeilWallClockMode n s.1 +
                Real.cosh s.1 * criticalMellinAtomWeight n *
                  ccmWeilWallAgeMode n s.1) := by
            rw [← Finset.sum_add_distrib]
          _ = _ := by
            congr 2
            funext n
            ring
    _ ≤ _ := by linarith

/-- **One-sided literal cutoff transport.**  Canonical cutoff enlargement has no positive entry
impulse: after subtracting the fixed-head Volterra transport, the later common-clock charge is
at most the earlier charge.  This is a structural inequality, not the missing source coercivity. -/
theorem ccmWeilParityCutoff_commonClockEnvelope_le
    (r s : SuzukiPositiveAperture) (hrs : r.1 ≤ s.1) :
    let Sr : Finset ℕ := Finset.Icc 2 (Nat.floor (Real.exp (2 * r.1)))
    let Ss : Finset ℕ := Finset.Icc 2 (Nat.floor (Real.exp (2 * s.1)))
    ccmWeilParityClockHead Ss s.1 + Real.cosh s.1 * ccmWeilParityAgeHead Ss s.1 ≤
      ccmWeilParityClockHead Sr r.1 + Real.cosh r.1 * ccmWeilParityAgeHead Sr r.1 +
        2 * ∫ t in r.1..s.1, Real.sinh t * ccmWeilParityAgeHead Sr t := by
  dsimp
  have htransport := ccmWeilParityCutoff_commonClockEnvelope r s hrs
  have hcollar := ccmWeilParityCutoff_commonClock_collar_nonpos r s hrs
  dsimp only at htransport hcollar
  linarith

end RHTower
