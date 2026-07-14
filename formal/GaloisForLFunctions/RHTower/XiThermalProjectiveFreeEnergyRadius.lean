import GaloisForLFunctions.RHTower.XiThermalProjectiveCofinalSection

/-!
# Exact free-energy rate of the Xi projective thermal system

The faithful projective cold partition is a positive weighted exponential sum of the horizontal
Xi displacements.  Its zero-temperature free-energy density therefore recovers the exact support
radius.  The statement remains true along every simultaneous cofinal finite-volume and cooling
schedule: a fixed near-extremal divisor atom is eventually present, while the full partition gives
the matching upper bound.
-/

open Filter Topology Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Every full projective cold-partition value is strictly positive. -/
theorem xiThermalProjectiveColdPartition_pos (k : ℕ) :
    0 < xiThermalProjectiveColdPartition k := by
  let q : XiZeroCopy := xiThermalEnumeration 0
  have hterm : 0 < xiThermalNode q *
      Real.exp ((k : ℝ) * xiEndpointProjectiveReflectionDisplacement q) :=
    mul_pos (xiThermalNode_pos q) (Real.exp_pos _)
  have hle := (summable_xiThermalProjectiveColdPartition k).le_tsum q
    (fun r _ => mul_nonneg (xiThermalNode_pos r).le (Real.exp_pos _).le)
  rw [← xiThermalProjectiveColdPartition] at hle
  exact hterm.trans_le hle

/-- A nonempty finite projective cold system has strictly positive partition value. -/
theorem xiThermalProjectiveColdTruncation_pos
    {N k : ℕ} (hN : 0 < N) :
    0 < xiThermalProjectiveColdTruncation N k := by
  let term : ℕ → ℝ := fun j =>
    xiThermalNode (xiThermalEnumeration j) *
      Real.exp ((k : ℝ) *
        xiEndpointProjectiveReflectionDisplacement (xiThermalEnumeration j))
  have hsingle : term 0 ≤ ∑ j ∈ Finset.range N, term j :=
    Finset.single_le_sum
      (f := term)
      (fun j _ => mul_nonneg (xiThermalNode_pos _).le (Real.exp_pos _).le)
      (Finset.mem_range.mpr hN)
  have hterm : 0 < term 0 :=
    mul_pos (xiThermalNode_pos _) (Real.exp_pos _)
  rw [xiThermalProjectiveColdTruncation]
  exact hterm.trans_le (by simpa only [term] using hsingle)

/-- Every strict lower bound for the projective support radius is exceeded by an actual
multiplicity copy of a Xi zero.  When the right divisor is empty the radius is zero and any
critical-line copy supplies the assertion. -/
theorem exists_xiZeroCopy_projectiveDisplacement_gt_of_lt_radius
    {a : ℝ} (ha : a < xiProjectiveReflectionRadius) :
    ∃ q : XiZeroCopy,
      a < xiEndpointProjectiveReflectionDisplacement q := by
  by_cases hne : Nonempty XiRightZeroCopy
  · letI : Nonempty XiRightZeroCopy := hne
    obtain ⟨x, ⟨q, rfl⟩, hax⟩ :=
      exists_lt_of_lt_csSup (Set.range_nonempty _)
        (by simpa only [xiProjectiveReflectionRadius] using ha)
    exact ⟨q.1, hax⟩
  · letI : IsEmpty XiRightZeroCopy := ⟨fun q => hne ⟨q⟩⟩
    have hradius : xiProjectiveReflectionRadius = 0 := by
      rw [xiProjectiveReflectionRadius]
      have hrange : Set.range (fun q : XiRightZeroCopy =>
          xiEndpointProjectiveReflectionDisplacement q.1) = ∅ :=
        Set.range_eq_empty_iff.mpr inferInstance
      rw [hrange, Real.sSup_empty]
    let q : XiZeroCopy := xiThermalEnumeration 0
    refine ⟨q, ?_⟩
    rw [hradius] at ha
    exact ha.trans_le (xiEndpointProjectiveReflectionDisplacement_nonneg q)

/-- **Cofinal finite-volume free-energy radius law.**  Along every schedule for which both the
finite Xi system and the integer inverse temperature tend to infinity, the logarithmic partition
value divided by inverse temperature converges to the exact projective reflection radius. -/
theorem tendsto_xiThermalProjectiveColdTruncation_log_div_cold
    (size cold : ℕ → ℕ)
    (hsize : Tendsto size atTop atTop)
    (hcold : Tendsto cold atTop atTop) :
    Tendsto
      (fun j : ℕ =>
        Real.log (xiThermalProjectiveColdTruncation (size j) (cold j)) /
          (cold j : ℝ))
      atTop (nhds xiProjectiveReflectionRadius) := by
  have hcoldReal : Tendsto (fun j : ℕ => (cold j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcold
  have hmassPos : 0 < normalizedPrimeArchMoment 0 := by
    rw [← xiThermalProjectiveColdPartition_zero_eq_source]
    exact xiThermalProjectiveColdPartition_pos 0
  have hzeros : XiZeroHalfPlaneBound xiProjectiveReflectionRadius :=
    (xiZeroHalfPlaneBound_iff_projectiveReflectionRadius_le
      xiProjectiveReflectionRadius_nonneg).2 le_rfl
  rw [tendsto_order]
  constructor
  · intro a ha
    obtain ⟨q, hqa⟩ :=
      exists_xiZeroCopy_projectiveDisplacement_gt_of_lt_radius ha
    obtain ⟨m, hm⟩ := xiThermalEnumeration_bijective.2 q
    let w : ℝ := xiThermalNode q
    let d : ℝ := xiEndpointProjectiveReflectionDisplacement q
    have hw : 0 < w := by simpa only [w] using xiThermalNode_pos q
    have hfixed : Tendsto (fun j : ℕ => Real.log w / (cold j : ℝ))
        atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hcoldReal
    have hsmall : ∀ᶠ j : ℕ in atTop,
        a < d + Real.log w / (cold j : ℝ) := by
      have hgap : a - d < 0 := by simpa only [d] using sub_neg.mpr hqa
      filter_upwards [(tendsto_order.1 hfixed).1 (a - d) hgap] with j hj
      linarith
    have hsizeM : ∀ᶠ j : ℕ in atTop, m + 1 ≤ size j :=
      hsize.eventually_ge_atTop (m + 1)
    have hcoldOne : ∀ᶠ j : ℕ in atTop, 1 ≤ cold j :=
      hcold.eventually_ge_atTop 1
    filter_upwards [hsmall, hsizeM, hcoldOne] with j hj hsj hkj
    have hkmem : m ∈ Finset.range (size j) :=
      Finset.mem_range.mpr (by omega)
    have htermle : w * Real.exp ((cold j : ℝ) * d) ≤
        xiThermalProjectiveColdTruncation (size j) (cold j) := by
      rw [xiThermalProjectiveColdTruncation]
      have hsingle := Finset.single_le_sum
        (f := fun n => xiThermalNode (xiThermalEnumeration n) *
          Real.exp ((cold j : ℝ) *
            xiEndpointProjectiveReflectionDisplacement (xiThermalEnumeration n)))
        (fun n _ => mul_nonneg (xiThermalNode_pos _).le (Real.exp_pos _).le)
        hkmem
      simpa only [hm, w, d] using hsingle
    have htermPos : 0 < w * Real.exp ((cold j : ℝ) * d) :=
      mul_pos hw (Real.exp_pos _)
    have hlogle := Real.log_le_log htermPos htermle
    have hkpos : 0 < (cold j : ℝ) := by exact_mod_cast hkj
    have hnormalized :
        d + Real.log w / (cold j : ℝ) ≤
          Real.log (xiThermalProjectiveColdTruncation (size j) (cold j)) /
            (cold j : ℝ) := by
      rw [Real.log_mul hw.ne' (Real.exp_ne_zero _), Real.log_exp] at hlogle
      rw [le_div_iff₀ hkpos]
      calc
        (d + Real.log w / (cold j : ℝ)) * (cold j : ℝ) =
            Real.log w + (cold j : ℝ) * d := by field_simp; ring
        _ ≤ Real.log (xiThermalProjectiveColdTruncation (size j) (cold j)) :=
          hlogle
    exact hj.trans_le hnormalized
  · intro b hb
    have hfixed : Tendsto
        (fun j : ℕ => Real.log (normalizedPrimeArchMoment 0) / (cold j : ℝ))
        atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hcoldReal
    have hsmall : ∀ᶠ j : ℕ in atTop,
        Real.log (normalizedPrimeArchMoment 0) / (cold j : ℝ) <
          b - xiProjectiveReflectionRadius :=
      (tendsto_order.1 hfixed).2 _ (sub_pos.mpr hb)
    have hsizeOne : ∀ᶠ j : ℕ in atTop, 1 ≤ size j :=
      hsize.eventually_ge_atTop 1
    have hcoldOne : ∀ᶠ j : ℕ in atTop, 1 ≤ cold j :=
      hcold.eventually_ge_atTop 1
    filter_upwards [hsmall, hsizeOne, hcoldOne] with j hj hsj hkj
    have hfinitePos :
        0 < xiThermalProjectiveColdTruncation (size j) (cold j) :=
      xiThermalProjectiveColdTruncation_pos (by omega)
    have hupper :
        xiThermalProjectiveColdTruncation (size j) (cold j) ≤
          normalizedPrimeArchMoment 0 *
            Real.exp ((cold j : ℝ) * xiProjectiveReflectionRadius) :=
      (xiThermalProjectiveColdTruncation_le_partition (size j) (cold j)).trans
        (xiThermalProjectiveColdPartition_le_source_exp_of_halfPlaneBound
          xiProjectiveReflectionRadius_nonneg hzeros (cold j))
    have hlogle := Real.log_le_log hfinitePos hupper
    have hkpos : 0 < (cold j : ℝ) := by exact_mod_cast hkj
    have hnormalized :
        Real.log (xiThermalProjectiveColdTruncation (size j) (cold j)) /
            (cold j : ℝ) ≤
          xiProjectiveReflectionRadius +
            Real.log (normalizedPrimeArchMoment 0) / (cold j : ℝ) := by
      rw [Real.log_mul hmassPos.ne' (Real.exp_ne_zero _), Real.log_exp] at hlogle
      rw [div_le_iff₀ hkpos]
      calc
        Real.log (xiThermalProjectiveColdTruncation (size j) (cold j)) ≤
            Real.log (normalizedPrimeArchMoment 0) +
              (cold j : ℝ) * xiProjectiveReflectionRadius := hlogle
        _ = (xiProjectiveReflectionRadius +
              Real.log (normalizedPrimeArchMoment 0) / (cold j : ℝ)) *
                (cold j : ℝ) := by field_simp; ring
    exact hnormalized.trans_lt (by linarith)

/-- The diagonal finite-volume/cooling section has free-energy density equal to the exact
horizontal Xi support radius. -/
theorem tendsto_xiThermalProjectiveColdDiagonal_log_div :
    Tendsto
      (fun j : ℕ =>
        Real.log (xiThermalProjectiveColdTruncation j j) / (j : ℝ))
      atTop (nhds xiProjectiveReflectionRadius) :=
  tendsto_xiThermalProjectiveColdTruncation_log_div_cold
    id id tendsto_id tendsto_id

/-- **Free-energy RH criterion along every cofinal section.**  Once a cofinal size/cooling
schedule is fixed, vanishing of its exact zero-temperature free-energy density is equivalent to
RH. -/
theorem riemannHypothesis_iff_tendsto_thermalProjectiveCofinalFreeEnergy_zero
    (size cold : ℕ → ℕ)
    (hsize : Tendsto size atTop atTop)
    (hcold : Tendsto cold atTop atTop) :
    RiemannHypothesis ↔
      Tendsto
        (fun j : ℕ =>
          Real.log (xiThermalProjectiveColdTruncation (size j) (cold j)) /
            (cold j : ℝ))
        atTop (nhds 0) := by
  let F : ℕ → ℝ := fun j =>
    Real.log (xiThermalProjectiveColdTruncation (size j) (cold j)) /
      (cold j : ℝ)
  have hF : Tendsto F atTop (nhds xiProjectiveReflectionRadius) :=
    tendsto_xiThermalProjectiveColdTruncation_log_div_cold size cold hsize hcold
  constructor
  · intro hRH
    have hradius := xiProjectiveReflectionRadius_eq_zero_iff_rh.mpr hRH
    simpa only [F, hradius] using hF
  · intro hzero
    have hradius : xiProjectiveReflectionRadius = 0 :=
      tendsto_nhds_unique hF (by simpa only [F] using hzero)
    exact xiProjectiveReflectionRadius_eq_zero_iff_rh.mp hradius

/-- **Subexponential cofinal thermal criterion.**  Uniform boundedness is unnecessary.  Along
any simultaneous finite-volume and cooling schedule, RH is equivalent to growth slower than
`exp (epsilon * beta)` for every positive exponential rate. -/
theorem riemannHypothesis_iff_thermalProjectiveCofinalSubexponential
    (size cold : ℕ → ℕ)
    (hsize : Tendsto size atTop atTop)
    (hcold : Tendsto cold atTop atTop) :
    RiemannHypothesis ↔
      ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ j : ℕ in atTop,
        xiThermalProjectiveColdTruncation (size j) (cold j) ≤
          Real.exp (epsilon * (cold j : ℝ)) := by
  let F : ℕ → ℝ := fun j =>
    Real.log (xiThermalProjectiveColdTruncation (size j) (cold j)) /
      (cold j : ℝ)
  have hF : Tendsto F atTop (nhds xiProjectiveReflectionRadius) :=
    tendsto_xiThermalProjectiveColdTruncation_log_div_cold size cold hsize hcold
  constructor
  · intro hRH epsilon hepsilon
    have hradius : xiProjectiveReflectionRadius = 0 :=
      xiProjectiveReflectionRadius_eq_zero_iff_rh.mpr hRH
    have hFzero : Tendsto F atTop (nhds 0) := by
      simpa only [hradius] using hF
    have hsmall : ∀ᶠ j : ℕ in atTop, F j < epsilon :=
      (tendsto_order.1 hFzero).2 epsilon hepsilon
    have hsizeOne : ∀ᶠ j : ℕ in atTop, 1 ≤ size j :=
      hsize.eventually_ge_atTop 1
    have hcoldOne : ∀ᶠ j : ℕ in atTop, 1 ≤ cold j :=
      hcold.eventually_ge_atTop 1
    filter_upwards [hsmall, hsizeOne, hcoldOne] with j hj hsj hkj
    have hZ : 0 < xiThermalProjectiveColdTruncation (size j) (cold j) :=
      xiThermalProjectiveColdTruncation_pos (by omega)
    have hbeta : 0 < (cold j : ℝ) := by exact_mod_cast hkj
    have hlog :
        Real.log (xiThermalProjectiveColdTruncation (size j) (cold j)) <
          epsilon * (cold j : ℝ) := by
      have := (div_lt_iff₀ hbeta).mp hj
      simpa only [F] using this
    rw [← Real.exp_log hZ]
    exact Real.exp_le_exp.mpr hlog.le
  · intro hsub
    have hradius : xiProjectiveReflectionRadius = 0 := by
      by_contra hne
      have hradiusPos : 0 < xiProjectiveReflectionRadius :=
        lt_of_le_of_ne xiProjectiveReflectionRadius_nonneg (Ne.symm hne)
      let epsilon : ℝ := xiProjectiveReflectionRadius / 2
      have hepsilon : 0 < epsilon := by
        dsimp only [epsilon]
        linarith
      have hepsilonRadius : epsilon < xiProjectiveReflectionRadius := by
        dsimp only [epsilon]
        linarith
      have hupperZ := hsub epsilon hepsilon
      have hlowerF : ∀ᶠ j : ℕ in atTop, epsilon < F j :=
        (tendsto_order.1 hF).1 epsilon hepsilonRadius
      have hsizeOne : ∀ᶠ j : ℕ in atTop, 1 ≤ size j :=
        hsize.eventually_ge_atTop 1
      have hcoldOne : ∀ᶠ j : ℕ in atTop, 1 ≤ cold j :=
        hcold.eventually_ge_atTop 1
      obtain ⟨j, hjupper, hjlower, hsj, hkj⟩ :=
        (hupperZ.and (hlowerF.and (hsizeOne.and hcoldOne))).exists
      have hZ : 0 < xiThermalProjectiveColdTruncation (size j) (cold j) :=
        xiThermalProjectiveColdTruncation_pos (by omega)
      have hbeta : 0 < (cold j : ℝ) := by exact_mod_cast hkj
      have hlog := Real.log_le_log hZ hjupper
      rw [Real.log_exp] at hlog
      have hFupper : F j ≤ epsilon := by
        rw [show F j =
          Real.log (xiThermalProjectiveColdTruncation (size j) (cold j)) /
            (cold j : ℝ) by rfl]
        exact (div_le_iff₀ hbeta).2 hlog
      exact (not_lt_of_ge hFupper) hjlower
    exact xiProjectiveReflectionRadius_eq_zero_iff_rh.mp hradius

/-- The exact diagonal free-energy rate vanishes exactly under RH. -/
theorem riemannHypothesis_iff_tendsto_thermalProjectiveDiagonalFreeEnergy_zero :
    RiemannHypothesis ↔
      Tendsto
        (fun j : ℕ =>
          Real.log (xiThermalProjectiveColdTruncation j j) / (j : ℝ))
        atTop (nhds 0) :=
  riemannHypothesis_iff_tendsto_thermalProjectiveCofinalFreeEnergy_zero
    id id tendsto_id tendsto_id

end

end RHTower
