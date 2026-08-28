import GaloisForLFunctions.RHTower.ThetaCuspCenterMixedFourPointOddParityCusp

/-!
# Far-tail positivity for the center-mixed four-point theta packet

Both reflection-parity determinant walls converge to the square of the central density.  Since
that density is strictly positive on every physical aperture, all sufficiently separated
equispaced four-node packets are positive definite.  Together with the coalescing result, this
localizes any rank-four obstruction to an intermediate separation.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-- The reflection-even four-point wall converges to the squared central density. -/
theorem tendsto_thetaCuspCenterMixedEvenParityWall_atTop
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    Tendsto (thetaCuspCenterMixedEvenParityWall a) atTop
      (𝓝 (thetaCuspCenterMixedDensity a 0 ^ 2)) := by
  let f : ℝ → ℝ := thetaCuspCenterMixedDensity a
  have hconst : Tendsto (fun _ : ℝ => f 0) atTop (𝓝 (f 0)) := tendsto_const_nhds
  have hf : Tendsto f atTop (𝓝 0) := by
    simpa only [f] using thetaCuspCenterMixedDensity_tendsto_zero ha0.le ha
  have hf2 : Tendsto (fun t : ℝ => f (2 * t)) atTop (𝓝 0) := by
    exact hf.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hf3 : Tendsto (fun t : ℝ => f (3 * t)) atTop (𝓝 0) := by
    exact hf.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 3))
  change Tendsto
    (fun t : ℝ => (f 0 + f (3 * t)) * (f 0 + f t) - (f t + f (2 * t)) ^ 2)
    atTop (𝓝 (f 0 ^ 2))
  simpa [pow_two] using
    ((hconst.add hf3).mul (hconst.add hf)).sub
      ((hf.add hf2).pow 2)

/-- The reflection-odd four-point wall converges to the squared central density. -/
theorem tendsto_thetaCuspCenterMixedOddParityWall_atTop
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    Tendsto (thetaCuspCenterMixedOddParityWall a) atTop
      (𝓝 (thetaCuspCenterMixedDensity a 0 ^ 2)) := by
  let f : ℝ → ℝ := thetaCuspCenterMixedDensity a
  have hconst : Tendsto (fun _ : ℝ => f 0) atTop (𝓝 (f 0)) := tendsto_const_nhds
  have hf : Tendsto f atTop (𝓝 0) := by
    simpa only [f] using thetaCuspCenterMixedDensity_tendsto_zero ha0.le ha
  have hf2 : Tendsto (fun t : ℝ => f (2 * t)) atTop (𝓝 0) := by
    exact hf.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hf3 : Tendsto (fun t : ℝ => f (3 * t)) atTop (𝓝 0) := by
    exact hf.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 3))
  change Tendsto
    (fun t : ℝ => (f 0 - f (3 * t)) * (f 0 - f t) - (f t - f (2 * t)) ^ 2)
    atTop (𝓝 (f 0 ^ 2))
  simpa [pow_two] using
    ((hconst.sub hf3).mul (hconst.sub hf)).sub
      ((hf.sub hf2).pow 2)

/-- Every physical center-mixed theta packet on four equispaced nodes is positive definite at
sufficiently large separation. -/
theorem eventually_thetaCuspCenterMixedGramFourEquispaced_posDef_atTop
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    ∀ᶠ t : ℝ in atTop,
      Matrix.PosDef (thetaCuspCenterMixedGramFourEquispaced a t) := by
  have hA2 : 0 < thetaCuspCenterMixedDensity a 0 ^ 2 :=
    sq_pos_of_pos (thetaCuspCenterMixedDensity_pos ha0 ha 0)
  have hEven := tendsto_thetaCuspCenterMixedEvenParityWall_atTop ha0 ha
  have hOdd := tendsto_thetaCuspCenterMixedOddParityWall_atTop ha0 ha
  filter_upwards [hEven.eventually (Ioi_mem_nhds hA2),
    hOdd.eventually (Ioi_mem_nhds hA2), eventually_gt_atTop (0 : ℝ)] with t he ho ht
  have hpsd : Matrix.PosSemidef (thetaCuspCenterMixedGramFourEquispaced a t) :=
    (thetaCuspCenterMixedGramFourEquispaced_posSemidef_iff_parityWalls ha0 ha ht).2
      ⟨he.le, ho.le⟩
  apply hpsd.posDef_iff_det_ne_zero.mpr
  unfold thetaCuspCenterMixedGramFourEquispaced
  rw [det_toeplitzFour_eq_parityWalls]
  exact mul_ne_zero
    (by simpa [thetaCuspCenterMixedEvenParityWall] using he.ne')
    (by simpa [thetaCuspCenterMixedOddParityWall] using ho.ne')

/-- Exact first derivative of the reflection-even four-point wall. -/
theorem hasDerivAt_thetaCuspCenterMixedEvenParityWall
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (t : ℝ) :
    HasDerivAt (thetaCuspCenterMixedEvenParityWall a)
      (3 * thetaCuspCenterMixedDensityFirstJet a (3 * t) *
          (thetaCuspCenterMixedDensity a 0 + thetaCuspCenterMixedDensity a t) +
        thetaCuspCenterMixedDensityFirstJet a t *
          (thetaCuspCenterMixedDensity a 0 + thetaCuspCenterMixedDensity a (3 * t)) -
        2 * (thetaCuspCenterMixedDensity a t + thetaCuspCenterMixedDensity a (2 * t)) *
          (thetaCuspCenterMixedDensityFirstJet a t +
            2 * thetaCuspCenterMixedDensityFirstJet a (2 * t))) t := by
  let f : ℝ → ℝ := thetaCuspCenterMixedDensity a
  let p : ℝ → ℝ := thetaCuspCenterMixedDensityFirstJet a
  have h0 : HasDerivAt (fun _ : ℝ => f 0) 0 t := hasDerivAt_const t (f 0)
  have h1 : HasDerivAt f (p t) t := by
    simpa only [f, p] using hasDerivAt_thetaCuspCenterMixedDensity ha0 ha t
  have h2 : HasDerivAt (fun s : ℝ => f (2 * s)) (2 * p (2 * t)) t := by
    have h := (hasDerivAt_thetaCuspCenterMixedDensity ha0 ha (2 * t)).comp t
      ((hasDerivAt_id t).const_mul 2)
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    dsimp only [p]
    ring
  have h3 : HasDerivAt (fun s : ℝ => f (3 * s)) (3 * p (3 * t)) t := by
    have h := (hasDerivAt_thetaCuspCenterMixedDensity ha0 ha (3 * t)).comp t
      ((hasDerivAt_id t).const_mul 3)
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    dsimp only [p]
    ring
  change HasDerivAt
    (fun s : ℝ => (f 0 + f (3 * s)) * (f 0 + f s) - (f s + f (2 * s)) ^ 2) _ t
  have hraw := ((h0.add h3).mul (h0.add h1)).sub ((h1.add h2).pow 2)
  refine (hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  dsimp only [f, p]
  simp only [Pi.add_apply, Nat.cast_ofNat, Nat.reduceSubDiff, zero_add]
  ring

/-- Exact first derivative of the reflection-odd four-point wall. -/
theorem hasDerivAt_thetaCuspCenterMixedOddParityWall
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (t : ℝ) :
    HasDerivAt (thetaCuspCenterMixedOddParityWall a)
      (-3 * thetaCuspCenterMixedDensityFirstJet a (3 * t) *
          (thetaCuspCenterMixedDensity a 0 - thetaCuspCenterMixedDensity a t) -
        thetaCuspCenterMixedDensityFirstJet a t *
          (thetaCuspCenterMixedDensity a 0 - thetaCuspCenterMixedDensity a (3 * t)) -
        2 * (thetaCuspCenterMixedDensity a t - thetaCuspCenterMixedDensity a (2 * t)) *
          (thetaCuspCenterMixedDensityFirstJet a t -
            2 * thetaCuspCenterMixedDensityFirstJet a (2 * t))) t := by
  let f : ℝ → ℝ := thetaCuspCenterMixedDensity a
  let p : ℝ → ℝ := thetaCuspCenterMixedDensityFirstJet a
  have h0 : HasDerivAt (fun _ : ℝ => f 0) 0 t := hasDerivAt_const t (f 0)
  have h1 : HasDerivAt f (p t) t := by
    simpa only [f, p] using hasDerivAt_thetaCuspCenterMixedDensity ha0 ha t
  have h2 : HasDerivAt (fun s : ℝ => f (2 * s)) (2 * p (2 * t)) t := by
    have h := (hasDerivAt_thetaCuspCenterMixedDensity ha0 ha (2 * t)).comp t
      ((hasDerivAt_id t).const_mul 2)
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    dsimp only [p]
    ring
  have h3 : HasDerivAt (fun s : ℝ => f (3 * s)) (3 * p (3 * t)) t := by
    have h := (hasDerivAt_thetaCuspCenterMixedDensity ha0 ha (3 * t)).comp t
      ((hasDerivAt_id t).const_mul 3)
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    dsimp only [p]
    ring
  change HasDerivAt
    (fun s : ℝ => (f 0 - f (3 * s)) * (f 0 - f s) - (f s - f (2 * s)) ^ 2) _ t
  have hraw := ((h0.sub h3).mul (h0.sub h1)).sub ((h1.sub h2).pow 2)
  refine (hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  dsimp only [f, p]
  simp only [Pi.sub_apply, Nat.cast_ofNat, Nat.reduceSubDiff]
  ring

/-- A negative even-parity wall cannot occur as an asymptotic accident: it forces a strictly
interior negative stationary wall with an exact theta-jet equation. -/
theorem exists_thetaCuspCenterMixedEvenParityWall_stationary_neg_of_neg
    {a t₀ : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (ht₀ : 0 < t₀)
    (hneg : thetaCuspCenterMixedEvenParityWall a t₀ < 0) :
    ∃ t : ℝ, 0 < t ∧ thetaCuspCenterMixedEvenParityWall a t < 0 ∧
      3 * thetaCuspCenterMixedDensityFirstJet a (3 * t) *
          (thetaCuspCenterMixedDensity a 0 + thetaCuspCenterMixedDensity a t) +
        thetaCuspCenterMixedDensityFirstJet a t *
          (thetaCuspCenterMixedDensity a 0 + thetaCuspCenterMixedDensity a (3 * t)) -
        2 * (thetaCuspCenterMixedDensity a t + thetaCuspCenterMixedDensity a (2 * t)) *
          (thetaCuspCenterMixedDensityFirstJet a t +
            2 * thetaCuspCenterMixedDensityFirstJet a (2 * t)) = 0 := by
  have hA2 : 0 < thetaCuspCenterMixedDensity a 0 ^ 2 :=
    sq_pos_of_pos (thetaCuspCenterMixedDensity_pos ha0 ha 0)
  have hposEventually : ∀ᶠ t : ℝ in atTop,
      0 < thetaCuspCenterMixedEvenParityWall a t :=
    (tendsto_thetaCuspCenterMixedEvenParityWall_atTop ha0 ha).eventually
      (Ioi_mem_nhds hA2)
  obtain ⟨R, hR⟩ := eventually_atTop.mp hposEventually
  let T : ℝ := max R (t₀ + 1)
  have hRT : R ≤ T := le_max_left _ _
  have ht₀T : t₀ < T := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hTpos : 0 < thetaCuspCenterMixedEvenParityWall a T := hR T hRT
  have hf : Continuous (thetaCuspCenterMixedDensity a) :=
    continuous_thetaCuspCenterMixedDensity ha0.le ha
  have hcont : Continuous (thetaCuspCenterMixedEvenParityWall a) := by
    unfold thetaCuspCenterMixedEvenParityWall toeplitzFourEvenParityWall
    fun_prop
  have ht₀mem : t₀ ∈ Icc (0 : ℝ) T := ⟨ht₀.le, ht₀T.le⟩
  obtain ⟨t, htmem, hmin⟩ := isCompact_Icc.exists_isMinOn
    ⟨t₀, ht₀mem⟩ hcont.continuousOn
  have htneg : thetaCuspCenterMixedEvenParityWall a t < 0 :=
    lt_of_le_of_lt (hmin ht₀mem) hneg
  have htpos : 0 < t := by
    by_contra hnot
    have htzero : t = 0 := le_antisymm (le_of_not_gt hnot) htmem.1
    subst t
    simp [thetaCuspCenterMixedEvenParityWall, toeplitzFourEvenParityWall, pow_two] at htneg
  have htT : t < T := by
    by_contra hnot
    have hteq : t = T := le_antisymm htmem.2 (le_of_not_gt hnot)
    subst t
    exact (not_lt_of_ge hTpos.le) htneg
  have hlocal : IsLocalMin (thetaCuspCenterMixedEvenParityWall a) t :=
    hmin.isLocalMin (Icc_mem_nhds htpos htT)
  have hstationary := hlocal.hasDerivAt_eq_zero
    (hasDerivAt_thetaCuspCenterMixedEvenParityWall ha0.le ha t)
  exact ⟨t, htpos, htneg, hstationary⟩

/-- A negative odd-parity wall forces a strictly interior negative stationary wall with its exact
theta-jet equation.  This is the global obstruction shape left after coalescing and tail
positivity. -/
theorem exists_thetaCuspCenterMixedOddParityWall_stationary_neg_of_neg
    {a t₀ : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (ht₀ : 0 < t₀)
    (hneg : thetaCuspCenterMixedOddParityWall a t₀ < 0) :
    ∃ t : ℝ, 0 < t ∧ thetaCuspCenterMixedOddParityWall a t < 0 ∧
      -3 * thetaCuspCenterMixedDensityFirstJet a (3 * t) *
          (thetaCuspCenterMixedDensity a 0 - thetaCuspCenterMixedDensity a t) -
        thetaCuspCenterMixedDensityFirstJet a t *
          (thetaCuspCenterMixedDensity a 0 - thetaCuspCenterMixedDensity a (3 * t)) -
        2 * (thetaCuspCenterMixedDensity a t - thetaCuspCenterMixedDensity a (2 * t)) *
          (thetaCuspCenterMixedDensityFirstJet a t -
            2 * thetaCuspCenterMixedDensityFirstJet a (2 * t)) = 0 := by
  have hA2 : 0 < thetaCuspCenterMixedDensity a 0 ^ 2 :=
    sq_pos_of_pos (thetaCuspCenterMixedDensity_pos ha0 ha 0)
  have hposEventually : ∀ᶠ t : ℝ in atTop,
      0 < thetaCuspCenterMixedOddParityWall a t :=
    (tendsto_thetaCuspCenterMixedOddParityWall_atTop ha0 ha).eventually
      (Ioi_mem_nhds hA2)
  obtain ⟨R, hR⟩ := eventually_atTop.mp hposEventually
  let T : ℝ := max R (t₀ + 1)
  have hRT : R ≤ T := le_max_left _ _
  have ht₀T : t₀ < T := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hTpos : 0 < thetaCuspCenterMixedOddParityWall a T := hR T hRT
  have hf : Continuous (thetaCuspCenterMixedDensity a) :=
    continuous_thetaCuspCenterMixedDensity ha0.le ha
  have hcont : Continuous (thetaCuspCenterMixedOddParityWall a) := by
    unfold thetaCuspCenterMixedOddParityWall toeplitzFourOddParityWall
    fun_prop
  have ht₀mem : t₀ ∈ Icc (0 : ℝ) T := ⟨ht₀.le, ht₀T.le⟩
  obtain ⟨t, htmem, hmin⟩ := isCompact_Icc.exists_isMinOn
    ⟨t₀, ht₀mem⟩ hcont.continuousOn
  have htneg : thetaCuspCenterMixedOddParityWall a t < 0 :=
    lt_of_le_of_lt (hmin ht₀mem) hneg
  have htpos : 0 < t := by
    by_contra hnot
    have htzero : t = 0 := le_antisymm (le_of_not_gt hnot) htmem.1
    subst t
    simp [thetaCuspCenterMixedOddParityWall, toeplitzFourOddParityWall, pow_two] at htneg
  have htT : t < T := by
    by_contra hnot
    have hteq : t = T := le_antisymm htmem.2 (le_of_not_gt hnot)
    subst t
    exact (not_lt_of_ge hTpos.le) htneg
  have hlocal : IsLocalMin (thetaCuspCenterMixedOddParityWall a) t :=
    hmin.isLocalMin (Icc_mem_nhds htpos htT)
  have hstationary := hlocal.hasDerivAt_eq_zero
    (hasDerivAt_thetaCuspCenterMixedOddParityWall ha0.le ha t)
  exact ⟨t, htpos, htneg, hstationary⟩

/-- Nonpositive parity walls on the nonnegative separation ray. -/
def thetaCuspCenterMixedFourPointObstructionSet (a : ℝ) : Set ℝ :=
  {t | 0 ≤ t ∧
    (thetaCuspCenterMixedEvenParityWall a t ≤ 0 ∨
      thetaCuspCenterMixedOddParityWall a t ≤ 0)}

theorem continuous_thetaCuspCenterMixedEvenParityWall
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    Continuous (thetaCuspCenterMixedEvenParityWall a) := by
  have hf : Continuous (thetaCuspCenterMixedDensity a) :=
    continuous_thetaCuspCenterMixedDensity ha0 ha
  unfold thetaCuspCenterMixedEvenParityWall toeplitzFourEvenParityWall
  fun_prop

theorem continuous_thetaCuspCenterMixedOddParityWall
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    Continuous (thetaCuspCenterMixedOddParityWall a) := by
  have hf : Continuous (thetaCuspCenterMixedDensity a) :=
    continuous_thetaCuspCenterMixedDensity ha0 ha
  unfold thetaCuspCenterMixedOddParityWall toeplitzFourOddParityWall
  fun_prop

/-- Any failure of a rank-four parity wall lies in a compact subset of the nonnegative
separation ray. -/
theorem isCompact_thetaCuspCenterMixedFourPointObstructionSet
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    IsCompact (thetaCuspCenterMixedFourPointObstructionSet a) := by
  have hEvenCont := continuous_thetaCuspCenterMixedEvenParityWall ha0.le ha
  have hOddCont := continuous_thetaCuspCenterMixedOddParityWall ha0.le ha
  have hclosed : IsClosed (thetaCuspCenterMixedFourPointObstructionSet a) := by
    unfold thetaCuspCenterMixedFourPointObstructionSet
    exact isClosed_Ici.inter
      ((isClosed_le hEvenCont continuous_const).union
        (isClosed_le hOddCont continuous_const))
  have hA2 : 0 < thetaCuspCenterMixedDensity a 0 ^ 2 :=
    sq_pos_of_pos (thetaCuspCenterMixedDensity_pos ha0 ha 0)
  have hEvenPos : ∀ᶠ t : ℝ in atTop, 0 < thetaCuspCenterMixedEvenParityWall a t :=
    (tendsto_thetaCuspCenterMixedEvenParityWall_atTop ha0 ha).eventually
      (Ioi_mem_nhds hA2)
  have hOddPos : ∀ᶠ t : ℝ in atTop, 0 < thetaCuspCenterMixedOddParityWall a t :=
    (tendsto_thetaCuspCenterMixedOddParityWall_atTop ha0 ha).eventually
      (Ioi_mem_nhds hA2)
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hEvenPos.and hOddPos)
  apply (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).of_isClosed_subset hclosed
  intro t ht
  refine ⟨ht.1, ?_⟩
  by_contra hnot
  have hpos := hT t (lt_of_not_ge hnot).le
  rcases ht.2 with he | ho
  · exact (not_lt_of_ge he) hpos.1
  · exact (not_lt_of_ge ho) hpos.2

end

end RHTower
