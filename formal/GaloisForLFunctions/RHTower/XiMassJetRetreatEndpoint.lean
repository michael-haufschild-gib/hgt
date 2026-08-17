import GaloisForLFunctions.RHTower.XiMassJetLogRetreat
import GaloisForLFunctions.RHTower.XiMassJetPrimeTail

/-!
# The endpoint of the jet-modified logarithmic retreat

The jet of order `n` gains a factor `u^{-(n+1)/2}` inside the caustic window and nothing at all past
the balance slope, where the exterior action already vanishes.  Retreating the cut from the balance
slope by `q log u` costs the action `m_B q log u + O(1)`, `m_B = 2a² − 1/2`, so the two gains balance
exactly at

`q_n = (n+1)/(2 m_B)`.

At that coefficient the whole exterior prime tail past `κ_B u − q_n log u` is bounded by a constant
depending only on `a`, `σ` and `n` — uniformly in the height `u` and in the truncation.  The tail is
cut in two at the balance ray: inside the retreat interval the window envelope applies, past it the
far-field envelope does, and the exterior action at the balance slope is zero.
-/

open Complex Filter Finset

namespace RHTower

noncomputable section

/-- The endpoint retreat coefficient of the jet of order `n`, `q_n = (n+1)/(2 m_B)`. -/
def xiMassJetRetreatCoeff (a : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) / (2 * (2 * a ^ 2 - 1 / 2))

theorem xiMassJetRetreatCoeff_pos {a : ℝ} (ha : 1 / 2 < a) (n : ℕ) :
    0 < xiMassJetRetreatCoeff a n := by
  have hm : (0 : ℝ) < 2 * a ^ 2 - 1 / 2 := by nlinarith
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [xiMassJetRetreatCoeff]
  exact div_pos hn (by linarith)

/-- The defining balance: the action cost of the endpoint retreat is exactly the jet gain. -/
theorem xiMassJetRetreatCoeff_mul {a : ℝ} (ha : 1 / 2 < a) (n : ℕ) :
    (2 * a ^ 2 - 1 / 2) * xiMassJetRetreatCoeff a n = ((n : ℝ) + 1) / 2 := by
  have hm : (0 : ℝ) < 2 * a ^ 2 - 1 / 2 := by nlinarith
  rw [xiMassJetRetreatCoeff]
  field_simp
  exact div_self (ne_of_gt (by nlinarith : (0 : ℝ) < 2 ^ 2 * a ^ 2 - 1))

set_option maxHeartbeats 1000000 in
/-- **The jet-modified exterior tail at the endpoint retreat is uniformly bounded.**  For every jet
order `n` the exterior prime tail past `κ_B u − q_n log u` is `O(1)` in the height, uniformly in the
truncation.  The window gain `u^{-(n+1)/2}` and the retreat cost `u^{m_B q_n}` cancel exactly, and
the far tail past the balance ray needs no gain because the exterior action vanishes there. -/
theorem exists_bound_xiMassJetPrimeTail_endpoint {a sigma : ℝ} (ha : 1 / 2 < a)
    (hsigma : 0 < sigma) (n : ℕ) :
    ∃ C u₀ : ℝ, 0 < C ∧ 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u → ∀ M : ℕ,
      ∑ p ∈ (Nat.primesBelow (M + 1)).filter (fun p : ℕ =>
          Real.exp (xiMassSpacelikeSharpSlope a * u
            - xiMassJetRetreatCoeff a n * Real.log u) < (p : ℝ)),
        ‖xiMassJetPrimeAtom a ((sigma : ℂ) + (u : ℂ) * Complex.I) n p‖ ≤ C := by
  classical
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hδ : (0 : ℝ) < a - 1 / 2 := by linarith
  have hm : (0 : ℝ) < 2 * a ^ 2 - 1 / 2 := by nlinarith
  set Cp : ℝ := (2 : ℝ) ^ (a - 1 / 2) * primeLogRpowTailConstant (a - 1 / 2) with hCpdef
  have hCp0 : (0 : ℝ) ≤ Cp := by
    rw [hCpdef]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (primeLogRpowTailConstant_nonneg hδ)
  set κ : ℝ := xiMassSpacelikeSharpSlope a with hκdef
  have hκ1 : 1 < κ := by rw [hκdef]; exact one_lt_xiMassSpacelikeSharpSlope ha
  set q : ℝ := xiMassJetRetreatCoeff a n with hqdef
  have hq0 : 0 < q := by rw [hqdef]; exact xiMassJetRetreatCoeff_pos ha n
  have hqm : (2 * a ^ 2 - 1 / 2) * q = ((n : ℝ) + 1) / 2 := by
    rw [hqdef]; exact xiMassJetRetreatCoeff_mul ha n
  obtain ⟨Cw, uw, hCw, huw0, hwin⟩ := exists_norm_xiMassJetIterate_window_le' ha hsigma n
  obtain ⟨Cf, uf, hCf, huf0, hfar⟩ := exists_norm_xiMassJetIterate_far_le ha hsigma n
  obtain ⟨ua, hua0, hact⟩ := exists_logRetreat_data ha hq0
  have hgrow4 : Tendsto (fun u : ℝ => u ^ ((1 : ℝ) / 4)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  obtain ⟨ub, hub⟩ := (hgrow4.eventually_ge_atTop (8 * q)).exists_forall_of_atTop
  refine ⟨|Cw * Cp * Real.exp 1| + |Cf * Cp| + 1,
    max uw (max uf (max ua (max ub (max 1 (xiMassFarThreshold a))))), by positivity,
    lt_of_lt_of_le one_pos (by simp), ?_⟩
  intro u hu M
  have huw : uw ≤ u := le_trans (le_max_left _ _) hu
  have huf : uf ≤ u := le_trans (by simp) hu
  have hua : ua ≤ u := le_trans (by simp) hu
  have hub' : ub ≤ u := le_trans (by simp) hu
  have hu1 : (1 : ℝ) ≤ u := le_trans (by simp) hu
  have hfth : xiMassFarThreshold a ≤ u := le_trans (by simp) hu
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu1
  have hlog0 : (0 : ℝ) ≤ Real.log u := Real.log_nonneg hu1
  obtain ⟨hcone, haction⟩ := hact u hua
  rw [← hκdef] at hcone haction
  set H : ℝ := κ * u - q * Real.log u with hHdef
  have hHu : u < H := by nlinarith [hcone]
  have hHpos : (0 : ℝ) < H := lt_trans hu0 hHu
  -- the caustic window is wide enough to contain the retreat
  have hsq : Real.sqrt u = u ^ ((1 : ℝ) / 4) * u ^ ((1 : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hu0]
    norm_num
  have hp4 : (0 : ℝ) < u ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hu0 _
  have hwidth : q * Real.log u ≤ Real.sqrt u / 2 := by
    have h4 := log_le_four_mul_rpow hu0
    have h8 := hub u hub'
    rw [hsq]
    nlinarith [mul_le_mul_of_nonneg_left h4 hq0.le, mul_le_mul_of_nonneg_right h8 hp4.le]
  have hS : (0 : ℝ) < Real.sqrt u ^ (n + 1) := pow_pos (Real.sqrt_pos.2 hu0) _
  have hSne : Real.sqrt u ^ (n + 1) ≠ 0 := ne_of_gt hS
  have hpow : Real.exp (((n : ℝ) + 1) / 2 * Real.log u) = Real.sqrt u ^ (n + 1) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (u ^ ((1 : ℝ) / 2)) (n + 1),
      ← Real.rpow_mul hu0.le, Real.rpow_def_of_pos hu0]
    congr 1
    push_cast
    ring
  set T : Finset ℕ := (Nat.primesBelow (M + 1)).filter
    (fun p : ℕ => Real.exp H < (p : ℝ)) with hTdef
  -- the retreat interval: the caustic window envelope
  have hboundA : ∑ p ∈ T.filter (fun p : ℕ => (p : ℝ) ≤ Real.exp (κ * u)),
      ‖xiMassJetPrimeAtom a ((sigma : ℂ) + (u : ℂ) * Complex.I) n p‖
      ≤ Cw / Real.sqrt u ^ (n + 1) * Cp
        * Real.exp (-(xiMassBesselConeExponent a (H / u) * u)) := by
    have hkapA : 1 < H / u := (one_lt_div hu0).2 hHu
    refine sum_norm_xiMassJetPrimeAtom_subset_le (a := a) (sigma := sigma) (kappa := H / u)
      (u := u) (B := Cw / Real.sqrt u ^ (n + 1)) (n := n) (M := M) ha hkapA hu0
      (by positivity) _ ?_ ?_
    · intro p hp
      have hpT := (Finset.mem_filter.mp hp).1
      rw [hTdef] at hpT
      refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hpT).1, ?_⟩
      rw [div_mul_cancel₀ H hu0.ne']
      exact (Finset.mem_filter.mp hpT).2
    · intro p hp
      obtain ⟨hpT0, hple⟩ := Finset.mem_filter.mp hp
      have hpT := hpT0
      rw [hTdef] at hpT
      obtain ⟨hpmem, hgt⟩ := Finset.mem_filter.mp hpT
      have hpp := (Nat.mem_primesBelow.mp hpmem).2
      have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
      have hplow : H < Real.log p := by
        have h := Real.log_lt_log (Real.exp_pos H) hgt
        rwa [Real.log_exp] at h
      have hplow' : κ * u - q * Real.log u < Real.log p := by rw [← hHdef]; exact hplow
      have hphigh : Real.log p ≤ κ * u := (Real.log_le_iff_le_exp hppos).2 hple
      set t : ℝ := Real.log p - κ * u with htdef
      have habs : |t| ≤ Real.sqrt u / 2 := by
        rw [abs_le]
        refine ⟨?_, ?_⟩
        · rw [htdef]; linarith
        · rw [htdef]; linarith [Real.sqrt_nonneg u]
      have hb := hwin u huw t habs
      have hteq : xiMassSpacelikeSharpSlope a * u + t = Real.log p := by
        rw [← hκdef, htdef]; ring
      rw [hteq] at hb
      exact hb
  -- past the balance ray: the far-field envelope, at zero exterior action
  have hboundB : ∑ p ∈ T.filter (fun p : ℕ => ¬ ((p : ℝ) ≤ Real.exp (κ * u))),
      ‖xiMassJetPrimeAtom a ((sigma : ℂ) + (u : ℂ) * Complex.I) n p‖
      ≤ Cf * Cp * Real.exp (-(xiMassBesselConeExponent a κ * u)) := by
    refine sum_norm_xiMassJetPrimeAtom_subset_le (a := a) (sigma := sigma) (kappa := κ)
      (u := u) (B := Cf) (n := n) (M := M) ha hκ1 hu0 hCf.le _ ?_ ?_
    · intro p hp
      obtain ⟨hpT0, hgt⟩ := Finset.mem_filter.mp hp
      have hpT := hpT0
      rw [hTdef] at hpT
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hpT).1, not_le.mp hgt⟩
    · intro p hp
      obtain ⟨hpT0, hgt⟩ := Finset.mem_filter.mp hp
      have hpT := hpT0
      rw [hTdef] at hpT
      have hplow : κ * u < Real.log p := by
        have h := Real.log_lt_log (Real.exp_pos (κ * u)) (not_le.mp hgt)
        rwa [Real.log_exp] at h
      have hku : u ≤ κ * u := by nlinarith
      exact hfar u huf (Real.log p) (by rw [← hκdef]; linarith) (by linarith)
  -- the exponent bookkeeping
  have hAexp : Real.exp (-(xiMassBesselConeExponent a (H / u) * u))
      ≤ Real.exp 1 * Real.sqrt u ^ (n + 1) := by
    have hmov := xiMassBesselConeExponent_movingSlope (a := a) (u := u) (H := H) hu0 hHu.le
    rw [hmov]
    have heq : -(a * Real.sqrt (H ^ 2 - u ^ 2) - H / 2)
        = H / 2 - a * Real.sqrt (H ^ 2 - u ^ 2) := by ring
    rw [heq]
    have hact2 : H / 2 - a * Real.sqrt (H ^ 2 - u ^ 2)
        ≤ ((n : ℝ) + 1) / 2 * Real.log u + 1 := by
      refine haction.trans ?_
      have hid : (2 * a ^ 2 - 1 / 2) * (q * Real.log u) = ((n : ℝ) + 1) / 2 * Real.log u := by
        rw [← hqm]; ring
      linarith [hid]
    calc Real.exp (H / 2 - a * Real.sqrt (H ^ 2 - u ^ 2))
        ≤ Real.exp (((n : ℝ) + 1) / 2 * Real.log u + 1) := Real.exp_le_exp.2 hact2
      _ = Real.exp (((n : ℝ) + 1) / 2 * Real.log u) * Real.exp 1 := Real.exp_add _ _
      _ = Real.sqrt u ^ (n + 1) * Real.exp 1 := by rw [hpow]
      _ = Real.exp 1 * Real.sqrt u ^ (n + 1) := by ring
  have hBexp : Real.exp (-(xiMassBesselConeExponent a κ * u)) = 1 := by
    rw [hκdef, xiMassBesselConeExponent_sharpSlope_eq_zero ha]
    simp
  calc ∑ p ∈ T, ‖xiMassJetPrimeAtom a ((sigma : ℂ) + (u : ℂ) * Complex.I) n p‖
      = ∑ p ∈ T.filter (fun p : ℕ => (p : ℝ) ≤ Real.exp (κ * u)),
            ‖xiMassJetPrimeAtom a ((sigma : ℂ) + (u : ℂ) * Complex.I) n p‖
          + ∑ p ∈ T.filter (fun p : ℕ => ¬ ((p : ℝ) ≤ Real.exp (κ * u))),
            ‖xiMassJetPrimeAtom a ((sigma : ℂ) + (u : ℂ) * Complex.I) n p‖ :=
        (Finset.sum_filter_add_sum_filter_not T _ _).symm
    _ ≤ Cw / Real.sqrt u ^ (n + 1) * Cp * (Real.exp 1 * Real.sqrt u ^ (n + 1))
          + Cf * Cp * 1 := by
        refine add_le_add (hboundA.trans ?_) (hboundB.trans ?_)
        · exact mul_le_mul_of_nonneg_left hAexp
            (mul_nonneg (div_nonneg hCw.le hS.le) hCp0)
        · rw [hBexp]
    _ = Cw * Cp * Real.exp 1 + Cf * Cp := by field_simp
    _ ≤ |Cw * Cp * Real.exp 1| + |Cf * Cp| + 1 := by
        linarith [le_abs_self (Cw * Cp * Real.exp 1), le_abs_self (Cf * Cp)]

end

end RHTower
