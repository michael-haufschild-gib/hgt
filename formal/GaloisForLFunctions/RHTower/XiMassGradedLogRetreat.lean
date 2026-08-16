import GaloisForLFunctions.RHTower.XiMassLogRetreatTail
import GaloisForLFunctions.RHTower.XiMassGradedConeSharpness

/-!
# The logarithmic layer of the graded cone

At the graded slope `κ_{a,λ}` the exterior action equals `λ u`, and its penetration rate is

`m_{a,λ} = a κ_{a,λ}/√(κ_{a,λ}² − 1) − 1/2 > 0`.

Two-point convexity plus the quantitative slope estimate give

`g_u(κ_{a,λ} u − q log u) ≤ λ u + m_{a,λ} q log u + O((log u)²/u)`,

so the exterior true-prime tail past the moving boundary
`κ_{a,λ} u − (log u)/(2 m_{a,λ})` is still `O(e^{λ u})`.  Every grade therefore carries the same
coefficient-sharp logarithmic refinement, with the balance slope as the member `λ = 0`.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The logarithmic penetration rate of a slope. -/
def xiMassGradedPenetrationRate (a kappa : ℝ) : ℝ :=
  a * kappa / Real.sqrt (kappa ^ 2 - 1) - 1 / 2

theorem xiMassGradedPenetrationRate_pos {a kappa : ℝ} (ha : 1 / 2 < a) (hkappa : 1 < kappa) :
    0 < xiMassGradedPenetrationRate a kappa := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hk2 : (0 : ℝ) < kappa ^ 2 - 1 := by nlinarith
  have hq : (0 : ℝ) < Real.sqrt (kappa ^ 2 - 1) := Real.sqrt_pos.2 hk2
  have hqsq : Real.sqrt (kappa ^ 2 - 1) ^ 2 = kappa ^ 2 - 1 := Real.sq_sqrt hk2.le
  have hqk : Real.sqrt (kappa ^ 2 - 1) < kappa := by nlinarith
  rw [xiMassGradedPenetrationRate, sub_pos, lt_div_iff₀ hq]
  nlinarith [hqk, ha, hq]

/-- **The quantitative retreat cost at a general slope.** -/
theorem xiMassAction_penetration_general_le {a kappa u r : ℝ} (ha : 1 / 2 < a) (hkappa : 1 < kappa)
    (hu : 0 < u) (hr : 0 < r)
    (hx : 2 * kappa * r ≤ (1 / 2) * (u * (kappa ^ 2 - 1))) :
    (kappa * u - r) / 2 - a * Real.sqrt ((kappa * u - r) ^ 2 - u ^ 2)
      ≤ (kappa / 2 - a * Real.sqrt (kappa ^ 2 - 1)) * u
        + xiMassGradedPenetrationRate a kappa * r
        + 2 * a * (kappa / Real.sqrt (kappa ^ 2 - 1)) * r
          * (2 * kappa * r / (u * (kappa ^ 2 - 1))) := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  have hk2 : (0 : ℝ) < kappa ^ 2 - 1 := by nlinarith
  have hq : (0 : ℝ) < Real.sqrt (kappa ^ 2 - 1) := Real.sqrt_pos.2 hk2
  have hq2 : Real.sqrt (kappa ^ 2 - 1) ^ 2 = kappa ^ 2 - 1 := Real.sq_sqrt hk2.le
  obtain ⟨x, hxdefe⟩ : ∃ x : ℝ, 2 * kappa * r / (u * (kappa ^ 2 - 1)) = x := ⟨_, rfl⟩
  have hxmul : x * (u * Real.sqrt (kappa ^ 2 - 1) ^ 2) = 2 * kappa * r := by
    rw [hq2, ← hxdefe]
    field_simp
  have hx0 : 0 ≤ x := by
    rw [← hxdefe]
    positivity
  have hxhalf : x ≤ 1 / 2 := by
    rw [← hxdefe, div_le_iff₀ (by positivity : (0 : ℝ) < u * (kappa ^ 2 - 1))]
    linarith
  obtain ⟨H, hH⟩ : ∃ H : ℝ, kappa * u - r = H := ⟨_, rfl⟩
  have hratio := height_ratio_le (kappa := kappa) (q := Real.sqrt (kappa ^ 2 - 1)) (u := u)
    (r := r) (x := x) (H := H) hkappa hq hq2 hu hr hxmul hx0 hxhalf hH.symm
  -- the outer height
  have hKgap : Real.sqrt ((kappa * u) ^ 2 - u ^ 2) = u * Real.sqrt (kappa ^ 2 - 1) := by
    have hfac : (kappa * u) ^ 2 - u ^ 2 = u ^ 2 * (kappa ^ 2 - 1) := by ring
    rw [hfac, Real.sqrt_mul (by positivity), Real.sqrt_sq hu.le]
  -- the inner height is outside the light cone
  have hHu : u < H := by
    have hr' : 2 * kappa * r ≤ (1 / 2) * (u * (kappa ^ 2 - 1)) := hx
    rw [← hH]
    nlinarith [hr', hu, hkappa0, hkappa, mul_pos hkappa0 hu]
  have hHK : H ≤ kappa * u := by rw [← hH]; linarith
  have hconv := xiMassAction_le_slope_general (a := a) (u := u) (H := H) (K := kappa * u)
    ha0 hu hHu hHK
  rw [hKgap] at hconv
  have hrr : kappa * u - H = r := by rw [← hH]; ring
  rw [hrr] at hconv
  have hslope : a * H / Real.sqrt (H ^ 2 - u ^ 2) - 1 / 2
      ≤ xiMassGradedPenetrationRate a kappa
        + 2 * a * (kappa / Real.sqrt (kappa ^ 2 - 1)) * x := by
    have hmul : a * H / Real.sqrt (H ^ 2 - u ^ 2) = a * (H / Real.sqrt (H ^ 2 - u ^ 2)) := by
      ring
    rw [hmul, xiMassGradedPenetrationRate]
    have hstep := mul_le_mul_of_nonneg_left hratio ha0.le
    have hval : a * (kappa / Real.sqrt (kappa ^ 2 - 1) * (1 + 2 * x))
        = a * kappa / Real.sqrt (kappa ^ 2 - 1)
          + 2 * a * (kappa / Real.sqrt (kappa ^ 2 - 1)) * x := by
      field_simp
    rw [hval] at hstep
    linarith
  have hfinal : r * (a * H / Real.sqrt (H ^ 2 - u ^ 2) - 1 / 2)
      ≤ r * (xiMassGradedPenetrationRate a kappa
        + 2 * a * (kappa / Real.sqrt (kappa ^ 2 - 1)) * x) :=
    mul_le_mul_of_nonneg_left hslope hr.le
  rw [hH, hxdefe]
  nlinarith [hconv, hfinal]

/-! ## The graded logarithmic tail -/

set_option maxHeartbeats 1200000 in
/-- **(21.16)--(21.17) The graded exterior tail at a logarithmic retreat.** -/
theorem exists_norm_gradedLogRetreatTail_le {a sigma lam q : ℝ} (ha : 1 / 2 < a)
    (hsigma : 0 < sigma) (hlam : 0 ≤ lam) (hlamhalf : lam < 1 / 2) (hq : 0 < q)
    (hqcap : xiMassGradedPenetrationRate a (xiMassGradedConeSlope a lam) * q ≤ 1 / 2) :
    ∃ C u₀ : ℝ, 0 ≤ C ∧ 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u → ∀ N : ℕ,
      (∑ p ∈ (Nat.primesBelow (N + 1)).filter (fun p : ℕ =>
          Real.exp (xiMassGradedConeSlope a lam * u - q * Real.log u) < (p : ℝ)),
          ‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) p‖)
        ≤ C * Real.exp (lam * u) := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  obtain ⟨kap, hkapdef⟩ : ∃ k : ℝ, xiMassGradedConeSlope a lam = k := ⟨_, rfl⟩
  rw [hkapdef] at hqcap
  have hkone : 1 < kap := by
    rw [← hkapdef]
    exact one_lt_xiMassGradedConeSlope ha hlam hlamhalf
  have hkap0 : (0 : ℝ) < kap := lt_trans zero_lt_one hkone
  have hk2 : (0 : ℝ) < kap ^ 2 - 1 := by nlinarith
  have hqq : (0 : ℝ) < Real.sqrt (kap ^ 2 - 1) := Real.sqrt_pos.2 hk2
  have hmpos : 0 < xiMassGradedPenetrationRate a kap :=
    xiMassGradedPenetrationRate_pos ha hkone
  have hgrade : kap / 2 - a * Real.sqrt (kap ^ 2 - 1) = lam := by
    have hval := xiMassBesselConeExponent_gradedConeSlope ha hlam hlamhalf.le
    rw [hkapdef, xiMassBesselConeExponent] at hval
    linarith
  obtain ⟨k0, hk0def⟩ : ∃ k0 : ℝ, (1 + kap) / 2 = k0 := ⟨_, rfl⟩
  have hk0one : 1 < k0 := by rw [← hk0def]; linarith
  have hgapk : (0 : ℝ) < kap - k0 := by rw [← hk0def]; linarith
  have hCT : 0 ≤ xiMassBesselExteriorSqrtTailConstant a sigma k0 := by
    rw [xiMassBesselExteriorSqrtTailConstant]
    have h1 : 0 ≤ xiMassBesselExteriorSqrtConstant a sigma k0 :=
      xiMassBesselExteriorSqrtConstant_nonneg ha0 hk0one
    have h2 : 0 ≤ primeLogRpowTailConstant (a - 1 / 2) :=
      primeLogRpowTailConstant_nonneg (by linarith)
    have h3 : (0 : ℝ) < (2 : ℝ) ^ (a - 1 / 2) := Real.rpow_pos_of_pos (by norm_num) _
    exact mul_nonneg h1 (mul_nonneg h3.le h2)
  obtain ⟨D, hD⟩ : ∃ D : ℝ,
      4 * a * (kap / Real.sqrt (kap ^ 2 - 1)) * kap * q ^ 2 / (kap ^ 2 - 1) = D := ⟨_, rfl⟩
  have hDnn : (0 : ℝ) ≤ D := by rw [← hD]; positivity
  have hgrow : Tendsto (fun u : ℝ => u ^ ((3 : ℝ) / 4)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hgrow2 : Tendsto (fun u : ℝ => u ^ ((1 : ℝ) / 2)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  obtain ⟨u₁, hu₁⟩ :=
    ((((hgrow.eventually_ge_atTop (4 * q / (kap - k0))).and
      (hgrow.eventually_ge_atTop (16 * kap * q / (kap ^ 2 - 1)))).and
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
  have hcone : k0 * u ≤ kap * u - q * Real.log u := by
    have h1 : 4 * q ≤ (kap - k0) * u ^ ((3 : ℝ) / 4) := by
      rw [div_le_iff₀ hgapk] at hA
      linarith
    have h2 : 4 * q * u ^ ((1 : ℝ) / 4)
        ≤ (kap - k0) * u ^ ((3 : ℝ) / 4) * u ^ ((1 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right h1 hpow4.le
    have h3 : (kap - k0) * u ^ ((3 : ℝ) / 4) * u ^ ((1 : ℝ) / 4) = (kap - k0) * u := by
      rw [mul_assoc, mul_comm (u ^ ((3 : ℝ) / 4)), hsplit34]
    rw [h3] at h2
    nlinarith [mul_le_mul_of_nonneg_left hlog4 hq.le, h2]
  have hx : 2 * kap * (q * Real.log u) ≤ (1 / 2) * (u * (kap ^ 2 - 1)) := by
    have h1 : 16 * kap * q ≤ (kap ^ 2 - 1) * u ^ ((3 : ℝ) / 4) := by
      rw [div_le_iff₀ hk2] at hB
      linarith
    have h2 : 16 * kap * q * u ^ ((1 : ℝ) / 4)
        ≤ (kap ^ 2 - 1) * u ^ ((3 : ℝ) / 4) * u ^ ((1 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right h1 hpow4.le
    have h3 : (kap ^ 2 - 1) * u ^ ((3 : ℝ) / 4) * u ^ ((1 : ℝ) / 4) = (kap ^ 2 - 1) * u := by
      rw [mul_assoc, mul_comm (u ^ ((3 : ℝ) / 4)), hsplit34]
    rw [h3] at h2
    nlinarith [mul_le_mul_of_nonneg_left hlog4 (by positivity : (0 : ℝ) ≤ 2 * kap * q), h2]
  have hcurv : 2 * a * (kap / Real.sqrt (kap ^ 2 - 1)) * (q * Real.log u)
      * (2 * kap * (q * Real.log u) / (u * (kap ^ 2 - 1))) ≤ 1 := by
    have hval : 2 * a * (kap / Real.sqrt (kap ^ 2 - 1)) * (q * Real.log u)
        * (2 * kap * (q * Real.log u) / (u * (kap ^ 2 - 1)))
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
      have hfin : D * (16 * u ^ (-((1 : ℝ) / 2))) * u ^ ((1 : ℝ) / 2)
          ≤ 1 * u ^ ((1 : ℝ) / 2) := by
        rw [hstep, one_mul]
        exact hC
      exact le_of_mul_le_mul_right hfin hpow2
    nlinarith [mul_le_mul_of_nonneg_left hlogsq hDnn, hDsmall]
  have htail := sum_norm_exteriorTail_movingSlope_le (a := a) (sigma := sigma) (kappa0 := k0)
    (u := u) (H := kap * u - q * Real.log u) ha hsigma hk0one hupos hcone N
  rw [hkapdef]
  refine htail.trans ?_
  have haction := xiMassAction_penetration_general_le (a := a) (kappa := kap) (u := u)
    (r := q * Real.log u) ha hkone hupos hrpos hx
  rw [hgrade] at haction
  have hgu : (kap * u - q * Real.log u) / 2
      - a * Real.sqrt ((kap * u - q * Real.log u) ^ 2 - u ^ 2)
      ≤ lam * u + xiMassGradedPenetrationRate a kap * (q * Real.log u) + 1 := by
    refine haction.trans ?_
    linarith [hcurv]
  have hCTnn : (0 : ℝ) ≤ xiMassBesselExteriorSqrtTailConstant a sigma k0 / Real.sqrt u := by
    have : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.2 hupos
    positivity
  refine (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hgu) hCTnn).trans ?_
  -- collect the powers
  have hpowid : Real.exp (xiMassGradedPenetrationRate a kap * (q * Real.log u))
      = u ^ (xiMassGradedPenetrationRate a kap * q) := by
    rw [Real.rpow_def_of_pos hupos]
    congr 1
    ring
  have hsqrtid : Real.sqrt u = u ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow u
  have hquot : u ^ (xiMassGradedPenetrationRate a kap * q) / Real.sqrt u ≤ 1 := by
    rw [hsqrtid, div_le_one hpow2]
    exact Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
  have hCTnn' : (0 : ℝ) ≤ xiMassBesselExteriorSqrtTailConstant a sigma k0 := hCT
  calc xiMassBesselExteriorSqrtTailConstant a sigma k0 / Real.sqrt u
        * Real.exp (lam * u + xiMassGradedPenetrationRate a kap * (q * Real.log u) + 1)
      = Real.exp 1 * xiMassBesselExteriorSqrtTailConstant a sigma k0 * Real.exp (lam * u)
        * (u ^ (xiMassGradedPenetrationRate a kap * q) / Real.sqrt u) := by
        rw [Real.exp_add, Real.exp_add, hpowid]
        field_simp
    _ ≤ Real.exp 1 * xiMassBesselExteriorSqrtTailConstant a sigma k0 * Real.exp (lam * u) * 1 := by
        refine mul_le_mul_of_nonneg_left hquot ?_
        positivity
    _ = Real.exp 1 * xiMassBesselExteriorSqrtTailConstant a sigma k0 * Real.exp (lam * u) := by
        ring

end

end RHTower
