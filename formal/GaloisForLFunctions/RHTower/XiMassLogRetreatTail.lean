import GaloisForLFunctions.RHTower.XiMassCausticPenetration

/-!
# The raw exterior tail at a logarithmic retreat

The exterior tail constant is antitone in the cone slope, so the slope may be allowed to move with
the height: for `H ≥ κ₀ u` the tail past `e^H` is at most

`C(κ₀) u^{-1/2} e^{g_u(H)}`,  `g_u(H) = H/2 − a√(H²−u²)`.

Retreating from the balance slope by `q log u` costs the action only `m_B q log u + o(1)`, so the
raw exterior tail past `κ_B u − q log u` is `O(u^{m_B q − 1/2})`.  It vanishes below the
coefficient `q_raw = 1/(2 m_B)` and stays bounded at it: the caustic has a coefficient-sharp
logarithmic boundary layer, not merely a sharp linear slope.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-! ## The moving cone slope -/

/-- The cone exponent at the slope realized by a height. -/
theorem xiMassBesselConeExponent_movingSlope {a u H : ℝ} (hu : 0 < u) (huH : u ≤ H) :
    xiMassBesselConeExponent a (H / u) * u = a * Real.sqrt (H ^ 2 - u ^ 2) - H / 2 := by
  have hgap : (0 : ℝ) ≤ H ^ 2 - u ^ 2 := by nlinarith
  have hval : (H / u) ^ 2 - 1 = (H ^ 2 - u ^ 2) / u ^ 2 := by field_simp
  have hroot : Real.sqrt ((H ^ 2 - u ^ 2) / u ^ 2) = Real.sqrt (H ^ 2 - u ^ 2) / u := by
    rw [Real.sqrt_div hgap, Real.sqrt_sq hu.le]
  rw [xiMassBesselConeExponent, hval, hroot]
  field_simp

/-- The exterior envelope constant is antitone in the slope. -/
theorem xiMassBesselExteriorSqrtConstant_antitone {a sigma kappa kappa' : ℝ} (ha : 0 < a)
    (hkappa : 1 < kappa) (hkk : kappa ≤ kappa') :
    xiMassBesselExteriorSqrtConstant a sigma kappa'
      ≤ xiMassBesselExteriorSqrtConstant a sigma kappa := by
  have hkappa' : 1 < kappa' := lt_of_lt_of_le hkappa hkk
  have hk1 : (0 : ℝ) < kappa - 1 := by linarith
  have hk1' : (0 : ℝ) < kappa' - 1 := by linarith
  have hk2 : (0 : ℝ) < kappa ^ 2 - 1 := by nlinarith
  have hk2' : (0 : ℝ) < kappa' ^ 2 - 1 := by nlinarith
  have hs : (0 : ℝ) < Real.sqrt (kappa ^ 2 - 1) := Real.sqrt_pos.2 hk2
  have hs' : (0 : ℝ) < Real.sqrt (kappa' ^ 2 - 1) := Real.sqrt_pos.2 hk2'
  have hratio : (kappa' + 1) / (kappa' - 1) ≤ (kappa + 1) / (kappa - 1) := by
    rw [div_le_div_iff₀ hk1' hk1]
    nlinarith
  have hroot : Real.sqrt (kappa ^ 2 - 1) ≤ Real.sqrt (kappa' ^ 2 - 1) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hsq : Real.sqrt (2 * Real.pi / (a * Real.sqrt (kappa' ^ 2 - 1)))
      ≤ Real.sqrt (2 * Real.pi / (a * Real.sqrt (kappa ^ 2 - 1))) := by
    refine Real.sqrt_le_sqrt ?_
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    nlinarith
  rw [xiMassBesselExteriorSqrtConstant, xiMassBesselExteriorSqrtConstant]
  have hfirst : 2 * a * ((kappa' + 1) / (kappa' - 1)) * Real.exp (1 / (2 * (a * sigma)))
      ≤ 2 * a * ((kappa + 1) / (kappa - 1)) * Real.exp (1 / (2 * (a * sigma))) := by
    have := mul_le_mul_of_nonneg_left hratio (by positivity : (0 : ℝ) ≤ 2 * a)
    exact mul_le_mul_of_nonneg_right this (Real.exp_nonneg _)
  exact mul_le_mul hfirst hsq (Real.sqrt_nonneg _) (by positivity)

theorem xiMassBesselExteriorSqrtTailConstant_antitone {a sigma kappa kappa' : ℝ} (ha : 1 / 2 < a)
    (hkappa : 1 < kappa) (hkk : kappa ≤ kappa') :
    xiMassBesselExteriorSqrtTailConstant a sigma kappa'
      ≤ xiMassBesselExteriorSqrtTailConstant a sigma kappa := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hδ : (0 : ℝ) < a - 1 / 2 := by linarith
  have hbase := xiMassBesselExteriorSqrtConstant_antitone (sigma := sigma) ha0 hkappa hkk
  have hfac : (0 : ℝ) ≤ (2 : ℝ) ^ (a - 1 / 2) * primeLogRpowTailConstant (a - 1 / 2) := by
    have h1 : (0 : ℝ) < (2 : ℝ) ^ (a - 1 / 2) := Real.rpow_pos_of_pos (by norm_num) _
    have h2 : 0 ≤ primeLogRpowTailConstant (a - 1 / 2) := primeLogRpowTailConstant_nonneg hδ
    exact mul_nonneg h1.le h2
  rw [xiMassBesselExteriorSqrtTailConstant, xiMassBesselExteriorSqrtTailConstant]
  exact mul_le_mul_of_nonneg_right hbase hfac

/-- **The exterior tail at a moving slope.** -/
theorem sum_norm_exteriorTail_movingSlope_le {a sigma kappa0 u H : ℝ} (ha : 1 / 2 < a)
    (hsigma : 0 < sigma) (hkappa0 : 1 < kappa0) (hu : 0 < u) (hcone : kappa0 * u ≤ H) (N : ℕ) :
    ∑ p ∈ (Nat.primesBelow (N + 1)).filter (fun p : ℕ => Real.exp H < (p : ℝ)),
        ‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) p‖
      ≤ xiMassBesselExteriorSqrtTailConstant a sigma kappa0 / Real.sqrt u
        * Real.exp (H / 2 - a * Real.sqrt (H ^ 2 - u ^ 2)) := by
  have hslope : kappa0 ≤ H / u := (le_div_iff₀ hu).2 hcone
  have hone : 1 < H / u := lt_of_lt_of_le hkappa0 hslope
  have huH : u ≤ H := by
    have h1 : (1 : ℝ) * u ≤ H := le_trans (by nlinarith) hcone
    linarith
  have hmul : H / u * u = H := div_mul_cancel₀ H hu.ne'
  have hbase := sum_norm_xiMassCenteredPrimeAtom_exteriorSqrt_le (a := a) (sigma := sigma)
    (kappa := H / u) (u := u) (L := 0) ha hsigma hone hu le_rfl N
  rw [hmul, add_zero] at hbase
  refine hbase.trans ?_
  have hexp : Real.exp (-(xiMassBesselConeExponent a (H / u) * u))
      = Real.exp (H / 2 - a * Real.sqrt (H ^ 2 - u ^ 2)) := by
    rw [xiMassBesselConeExponent_movingSlope hu huH]
    congr 1
    ring
  rw [hexp, mul_zero, neg_zero, Real.exp_zero, mul_one]
  have hCT : xiMassBesselExteriorSqrtTailConstant a sigma (H / u)
      ≤ xiMassBesselExteriorSqrtTailConstant a sigma kappa0 :=
    xiMassBesselExteriorSqrtTailConstant_antitone ha hkappa0 hslope
  have hroot : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.2 hu
  have hstep : xiMassBesselExteriorSqrtTailConstant a sigma (H / u) / Real.sqrt u
      ≤ xiMassBesselExteriorSqrtTailConstant a sigma kappa0 / Real.sqrt u :=
    div_le_div_of_nonneg_right hCT hroot.le
  exact mul_le_mul_of_nonneg_right hstep (Real.exp_nonneg _)

/-! ## The logarithmic retreat -/

theorem log_le_four_mul_rpow {u : ℝ} (hu : 0 < u) : Real.log u ≤ 4 * u ^ ((1 : ℝ) / 4) := by
  have h1 : (0 : ℝ) < u ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hu _
  have h2 := Real.log_le_sub_one_of_pos h1
  rw [Real.log_rpow hu] at h2
  linarith

/-- **(21.2)--(21.3) The raw exterior tail at a logarithmic retreat.** -/
theorem exists_norm_logRetreatTail_le {a sigma q : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma)
    (hq : 0 < q) :
    ∃ C u₀ : ℝ, 0 ≤ C ∧ 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u → ∀ N : ℕ,
      (∑ p ∈ (Nat.primesBelow (N + 1)).filter (fun p : ℕ =>
          Real.exp (xiMassSpacelikeSharpSlope a * u - q * Real.log u) < (p : ℝ)),
          ‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) p‖)
        ≤ C * u ^ ((2 * a ^ 2 - 1 / 2) * q - 1 / 2) := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hkap : 0 < xiMassSpacelikeSharpSlope a := sharpSlope_pos ha
  have hkone : 1 < xiMassSpacelikeSharpSlope a := one_lt_xiMassSpacelikeSharpSlope ha
  have hk2 : (0 : ℝ) < xiMassSpacelikeSharpSlope a ^ 2 - 1 := by nlinarith
  obtain ⟨k0, hk0def⟩ : ∃ k0 : ℝ, (1 + xiMassSpacelikeSharpSlope a) / 2 = k0 := ⟨_, rfl⟩
  have hk0one : 1 < k0 := by rw [← hk0def]; linarith
  have hgapk : (0 : ℝ) < xiMassSpacelikeSharpSlope a - k0 := by rw [← hk0def]; linarith
  have hCT : 0 ≤ xiMassBesselExteriorSqrtTailConstant a sigma k0 := by
    rw [xiMassBesselExteriorSqrtTailConstant]
    have h1 : 0 ≤ xiMassBesselExteriorSqrtConstant a sigma k0 :=
      xiMassBesselExteriorSqrtConstant_nonneg ha0 hk0one
    have h2 : 0 ≤ primeLogRpowTailConstant (a - 1 / 2) :=
      primeLogRpowTailConstant_nonneg (by linarith)
    have h3 : (0 : ℝ) < (2 : ℝ) ^ (a - 1 / 2) := Real.rpow_pos_of_pos (by norm_num) _
    exact mul_nonneg h1 (mul_nonneg h3.le h2)
  obtain ⟨D, hD⟩ : ∃ D : ℝ, 8 * a ^ 2 * xiMassSpacelikeSharpSlope a * q ^ 2
      / (xiMassSpacelikeSharpSlope a ^ 2 - 1) = D := ⟨_, rfl⟩
  have hDnn : (0 : ℝ) ≤ D := by rw [← hD]; positivity
  have hgrow : Tendsto (fun u : ℝ => u ^ ((3 : ℝ) / 4)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hgrow2 : Tendsto (fun u : ℝ => u ^ ((1 : ℝ) / 2)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  obtain ⟨u₁, hu₁⟩ :=
    ((((hgrow.eventually_ge_atTop (4 * q / (xiMassSpacelikeSharpSlope a - k0))).and
      (hgrow.eventually_ge_atTop (16 * xiMassSpacelikeSharpSlope a * q
        / (xiMassSpacelikeSharpSlope a ^ 2 - 1)))).and
      (hgrow2.eventually_ge_atTop (16 * D))).and
      (eventually_ge_atTop (2 : ℝ))).exists_forall_of_atTop
  refine ⟨Real.exp 1 * xiMassBesselExteriorSqrtTailConstant a sigma k0, max u₁ 2,
    by positivity, lt_of_lt_of_le (by norm_num) (le_max_right _ _), fun u hu N => ?_⟩
  have hu2 : (2 : ℝ) ≤ u := le_trans (le_max_right _ _) hu
  have hu1 : (1 : ℝ) ≤ u := by linarith
  have hupos : (0 : ℝ) < u := by linarith
  obtain ⟨⟨⟨hA, hB⟩, hC⟩, _⟩ := hu₁ u (le_trans (le_max_left _ _) hu)
  have hlogpos : 0 < Real.log u := Real.log_pos (by linarith)
  have hlog0 : 0 ≤ Real.log u := hlogpos.le
  have hlog4 : Real.log u ≤ 4 * u ^ ((1 : ℝ) / 4) := log_le_four_mul_rpow hupos
  have hrpos : (0 : ℝ) < q * Real.log u := mul_pos hq hlogpos
  have hsplit34 : u ^ ((1 : ℝ) / 4) * u ^ ((3 : ℝ) / 4) = u := by
    rw [← Real.rpow_add hupos]
    norm_num
  have hpow4 : (0 : ℝ) < u ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hupos _
  have hpow2 : (0 : ℝ) < u ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hupos _
  -- the retreat stays inside a fixed inner cone
  have hcone : k0 * u ≤ xiMassSpacelikeSharpSlope a * u - q * Real.log u := by
    have h1 : 4 * q ≤ (xiMassSpacelikeSharpSlope a - k0) * u ^ ((3 : ℝ) / 4) := by
      rw [div_le_iff₀ hgapk] at hA
      linarith
    have h2 : 4 * q * u ^ ((1 : ℝ) / 4)
        ≤ (xiMassSpacelikeSharpSlope a - k0) * u ^ ((3 : ℝ) / 4) * u ^ ((1 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right h1 hpow4.le
    have h3 : (xiMassSpacelikeSharpSlope a - k0) * u ^ ((3 : ℝ) / 4) * u ^ ((1 : ℝ) / 4)
        = (xiMassSpacelikeSharpSlope a - k0) * u := by
      rw [mul_assoc, mul_comm (u ^ ((3 : ℝ) / 4)), hsplit34]
    rw [h3] at h2
    nlinarith [mul_le_mul_of_nonneg_left hlog4 hq.le, h2]
  -- the relative retreat is small
  have hx : 2 * xiMassSpacelikeSharpSlope a * (q * Real.log u)
      ≤ (1 / 2) * (u * (xiMassSpacelikeSharpSlope a ^ 2 - 1)) := by
    have h1 : 16 * xiMassSpacelikeSharpSlope a * q
        ≤ (xiMassSpacelikeSharpSlope a ^ 2 - 1) * u ^ ((3 : ℝ) / 4) := by
      rw [div_le_iff₀ hk2] at hB
      linarith
    have h2 : 16 * xiMassSpacelikeSharpSlope a * q * u ^ ((1 : ℝ) / 4)
        ≤ (xiMassSpacelikeSharpSlope a ^ 2 - 1) * u ^ ((3 : ℝ) / 4) * u ^ ((1 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right h1 hpow4.le
    have h3 : (xiMassSpacelikeSharpSlope a ^ 2 - 1) * u ^ ((3 : ℝ) / 4) * u ^ ((1 : ℝ) / 4)
        = (xiMassSpacelikeSharpSlope a ^ 2 - 1) * u := by
      rw [mul_assoc, mul_comm (u ^ ((3 : ℝ) / 4)), hsplit34]
    rw [h3] at h2
    nlinarith [mul_le_mul_of_nonneg_left hlog4 (by positivity :
      (0 : ℝ) ≤ 2 * xiMassSpacelikeSharpSlope a * q), h2]
  -- the curvature correction is at most one
  have hcurv : 4 * a ^ 2 * (q * Real.log u)
      * (2 * xiMassSpacelikeSharpSlope a * (q * Real.log u)
        / (u * (xiMassSpacelikeSharpSlope a ^ 2 - 1))) ≤ 1 := by
    have hval : 4 * a ^ 2 * (q * Real.log u)
        * (2 * xiMassSpacelikeSharpSlope a * (q * Real.log u)
          / (u * (xiMassSpacelikeSharpSlope a ^ 2 - 1)))
        = D * (Real.log u * Real.log u / u) := by
      rw [← hD]
      field_simp
      ring
    rw [hval]
    have hlogsq : Real.log u * Real.log u / u ≤ 16 * u ^ (-((1 : ℝ) / 2)) := by
      have hsq : Real.log u * Real.log u ≤ 16 * (u ^ ((1 : ℝ) / 4) * u ^ ((1 : ℝ) / 4)) := by
        nlinarith [hlog4, hlog0, hpow4]
      have hid : u ^ ((1 : ℝ) / 4) * u ^ ((1 : ℝ) / 4) = u ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_add hupos]
        norm_num
      rw [hid] at hsq
      rw [div_le_iff₀ hupos]
      have hneg : u ^ (-((1 : ℝ) / 2)) * u = u ^ ((1 : ℝ) / 2) := by
        nth_rewrite 2 [show u = u ^ (1 : ℝ) from (Real.rpow_one u).symm]
        rw [← Real.rpow_add hupos]
        norm_num
      rw [mul_assoc, hneg]
      linarith
    have hDsmall : D * (16 * u ^ (-((1 : ℝ) / 2))) ≤ 1 := by
      have hinv : u ^ (-((1 : ℝ) / 2)) * u ^ ((1 : ℝ) / 2) = 1 := by
        rw [← Real.rpow_add hupos]
        norm_num
      have hstep : D * (16 * u ^ (-((1 : ℝ) / 2))) * u ^ ((1 : ℝ) / 2) = 16 * D := by
        calc D * (16 * u ^ (-((1 : ℝ) / 2))) * u ^ ((1 : ℝ) / 2)
            = 16 * D * (u ^ (-((1 : ℝ) / 2)) * u ^ ((1 : ℝ) / 2)) := by ring
          _ = 16 * D := by rw [hinv]; ring
      have hCle : 16 * D ≤ u ^ ((1 : ℝ) / 2) := hC
      have hfin : D * (16 * u ^ (-((1 : ℝ) / 2))) * u ^ ((1 : ℝ) / 2)
          ≤ 1 * u ^ ((1 : ℝ) / 2) := by
        rw [hstep, one_mul]
        exact hCle
      exact le_of_mul_le_mul_right hfin hpow2
    nlinarith [mul_le_mul_of_nonneg_left hlogsq hDnn, hDsmall]
  -- the tail bound
  have htail := sum_norm_exteriorTail_movingSlope_le (a := a) (sigma := sigma) (kappa0 := k0)
    (u := u) (H := xiMassSpacelikeSharpSlope a * u - q * Real.log u) ha hsigma hk0one hupos
    hcone N
  refine htail.trans ?_
  have haction := xiMassAction_penetration_le (a := a) (u := u) (r := q * Real.log u)
    ha hupos hrpos hx
  have hgu : (xiMassSpacelikeSharpSlope a * u - q * Real.log u) / 2
      - a * Real.sqrt ((xiMassSpacelikeSharpSlope a * u - q * Real.log u) ^ 2 - u ^ 2)
      ≤ (2 * a ^ 2 - 1 / 2) * (q * Real.log u) + 1 := by
    refine haction.trans ?_
    linarith [hcurv]
  have hCTnn : (0 : ℝ) ≤ xiMassBesselExteriorSqrtTailConstant a sigma k0 / Real.sqrt u := by
    have : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.2 hupos
    positivity
  refine (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hgu) hCTnn).trans (le_of_eq ?_)
  have hpowid : Real.exp ((2 * a ^ 2 - 1 / 2) * (q * Real.log u))
      = u ^ ((2 * a ^ 2 - 1 / 2) * q) := by
    rw [Real.rpow_def_of_pos hupos]
    congr 1
    ring
  have hsub : u ^ ((2 * a ^ 2 - 1 / 2) * q - 1 / 2)
      = u ^ ((2 * a ^ 2 - 1 / 2) * q) / u ^ ((1 : ℝ) / 2) := Real.rpow_sub hupos _ _
  rw [Real.exp_add, hpowid, hsub, Real.sqrt_eq_rpow]
  field_simp

/-- **(21.3) At the sharp logarithmic coefficient the raw exterior tail stays bounded.** -/
theorem exists_norm_logRetreatTail_bounded {a sigma : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma) :
    ∃ C u₀ : ℝ, 0 ≤ C ∧ 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u → ∀ N : ℕ,
      (∑ p ∈ (Nat.primesBelow (N + 1)).filter (fun p : ℕ =>
          Real.exp (xiMassSpacelikeSharpSlope a * u
            - (1 / (2 * (2 * a ^ 2 - 1 / 2))) * Real.log u) < (p : ℝ)),
          ‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) p‖) ≤ C := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hmB : (0 : ℝ) < 2 * a ^ 2 - 1 / 2 := by nlinarith
  have hq : (0 : ℝ) < 1 / (2 * (2 * a ^ 2 - 1 / 2)) := by positivity
  obtain ⟨C, u₀, hC, hu₀, hbd⟩ := exists_norm_logRetreatTail_le ha hsigma hq
  refine ⟨C, u₀, hC, hu₀, fun u hu N => ?_⟩
  have hzero : (2 * a ^ 2 - 1 / 2) * (1 / (2 * (2 * a ^ 2 - 1 / 2))) - 1 / 2 = 0 := by
    have hne2 : (2 : ℝ) * (2 * a ^ 2 - 1 / 2) ≠ 0 := mul_ne_zero two_ne_zero (ne_of_gt hmB)
    rw [sub_eq_zero, mul_one_div, div_eq_iff hne2]
    ring
  have hres := hbd u hu N
  rw [hzero, Real.rpow_zero, mul_one] at hres
  exact hres

end

end RHTower
