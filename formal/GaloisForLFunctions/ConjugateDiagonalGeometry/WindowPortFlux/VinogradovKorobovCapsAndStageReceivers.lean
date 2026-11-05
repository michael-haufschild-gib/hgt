import GaloisForLFunctions.ConjugateDiagonalGeometry.WindowPortFlux.InnerCapSourceIdentityAndStageCancellation
import GaloisForLFunctions.SquareRootThreshold.ZetaLagFamilyVinogradovKorobovEnvelope

/-!
# Vinogradov–Korobov caps at square-root theta prefixes

The arithmetic zero-free width moves the outer contour farther into the
critical strip. Polynomial-stage zero transfer retains the square-root
prefix schedule and identifies the old and new inner-cap readings exactly.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.WindowPortFlux
open GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision
open GaloisForLFunctions.SquareRootThreshold

/-- The VK cap retains half the zero-free width for approximation error. -/
def vkWindowCapAbscissa (m : ℕ) : ℝ :=
  1 - vkZeroFreeWidth ((m + 5 : ℕ) : ℝ) / 2

private theorem vkWidth_bounds {G : ℝ} (hG : Real.exp (Real.exp 30) ≤ G) :
    0 < vkZeroFreeWidth G ∧ vkZeroFreeWidth G ≤ 1 / 10 ^ 8 := by
  have hG0 : 0 < G := (Real.exp_pos _).trans_le hG
  have hL : Real.exp 30 ≤ Real.log G := (Real.le_log_iff_exp_le hG0).mpr hG
  have hL1 : 1 ≤ Real.log G := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < Real.log G := zero_lt_one.trans_le hL1
  have hl : 30 ≤ Real.log (Real.log G) := by
    rw [← Real.log_exp 30]
    exact Real.log_le_log (Real.exp_pos _) hL
  have hl1 : 1 ≤ Real.log (Real.log G) := by linarith only [hl]
  have hl0 : 0 < Real.log (Real.log G) := zero_lt_one.trans_le hl1
  unfold vkZeroFreeWidth
  constructor
  · positivity
  · have h1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num : -(2 : ℝ) / 3 ≤ 0)
    have h2 := Real.rpow_le_one_of_one_le_of_nonpos hl1 (by norm_num : -(5 : ℝ) / 3 ≤ 0)
    have hp := mul_le_mul h1 h2 (Real.rpow_nonneg hl0.le _) zero_le_one
    simpa only [one_mul] using div_le_div_of_nonneg_right hp (by norm_num : (0 : ℝ) ≤ 10 ^ 8)

/-- The VK width eventually exceeds the reciprocal logarithm. -/
theorem eventually_inv_log_le_vkWidth :
    ∀ᶠ G : ℝ in atTop, 1 / Real.log G ≤ vkZeroFreeWidth G := by
  have hsmall := Real.tendsto_log_atTop.eventually
    (eventually_log_sq_le_rpow (r := 1 / 3) (by norm_num))
  filter_upwards [hsmall, eventually_ge_atTop (Real.exp (Real.exp 30))] with G hsmall hG
  have hG0 : 0 < G := (Real.exp_pos _).trans_le hG
  have hL : Real.exp 30 ≤ Real.log G := (Real.le_log_iff_exp_le hG0).mpr hG
  have hL1 : 1 ≤ Real.log G := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < Real.log G := zero_lt_one.trans_le hL1
  have hl : 30 ≤ Real.log (Real.log G) := by
    rw [← Real.log_exp 30]
    exact Real.log_le_log (Real.exp_pos _) hL
  have hl1 : 1 ≤ Real.log (Real.log G) := by linarith only [hl]
  have hl0 : 0 < Real.log (Real.log G) := zero_lt_one.trans_le hl1
  have hp : Real.log (Real.log G) ^ ((5 : ℝ) / 3) ≤ Real.log (Real.log G) ^ 2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le hl1 (by norm_num : (5 : ℝ) / 3 ≤ 2)
  have hden : 10 ^ 8 * (Real.log G ^ ((2 : ℝ) / 3) *
      Real.log (Real.log G) ^ ((5 : ℝ) / 3)) ≤ Real.log G := by
    calc 10 ^ 8 * (Real.log G ^ ((2 : ℝ) / 3) *
          Real.log (Real.log G) ^ ((5 : ℝ) / 3))
        ≤ Real.log G ^ ((2 : ℝ) / 3) * (10 ^ 8 * Real.log (Real.log G) ^ 2) := by
          nlinarith only [mul_le_mul_of_nonneg_left hp
            (show 0 ≤ 10 ^ 8 * Real.log G ^ ((2 : ℝ) / 3) by positivity)]
      _ ≤ Real.log G ^ ((2 : ℝ) / 3) * Real.log G ^ ((1 : ℝ) / 3) :=
        mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hL0.le _)
      _ = Real.log G := by rw [← Real.rpow_add hL0]; norm_num
  unfold vkZeroFreeWidth
  rw [show -(2 : ℝ) / 3 = -((2 : ℝ) / 3) by ring,
    show -(5 : ℝ) / 3 = -((5 : ℝ) / 3) by ring,
    Real.rpow_neg hL0.le, Real.rpow_neg hl0.le]
  calc 1 / Real.log G
      ≤ 1 / (10 ^ 8 * (Real.log G ^ ((2 : ℝ) / 3) *
          Real.log (Real.log G) ^ ((5 : ℝ) / 3))) :=
        div_le_div_of_nonneg_left zero_le_one (by positivity) hden
    _ = (Real.log G ^ ((2 : ℝ) / 3))⁻¹ *
        (Real.log (Real.log G) ^ ((5 : ℝ) / 3))⁻¹ / 10 ^ 8 := by ring

/-- A square-root prefix locates every window zero within `1/(16(m+6))`
of an actual xi zero in the same Burnol window. -/
theorem exists_xiZero_near_thetaZero_polyPrefix (m : ℕ) {N : ℕ}
    (hN : polySqrtPrefix 1 m ≤ N) {z : ℂ}
    (hz : -1 / 2 < z.re ∧ z.re < 3 / 2 ∧
      burnolUnitLower m < z.im ∧ z.im < burnolUnitUpper m)
    (hzero : _root_.RHTower.finiteThetaAmplitude N z = 0) :
    ∃ w ∈ burnolUnitXiZeros m, ‖z - w‖ ≤ 1 / (16 * ((m + 6 : ℕ) : ℝ)) := by
  have hb := (besselUnitPrefix_le_polySqrtPrefix_of_le 1 m (S := m + 6) (by simp)).trans hN
  have hsq := sq_nonneg
    (((∑ w ∈ burnolUnitXiZeros m, (analyticOrderAt _root_.RHTower.xi w).toNat : ℕ) : ℝ))
  have ht := unitStage_tail_lt m (m + 6) (n := m + 6) (by omega)
    (by linarith only [hsq]) hb
  exact exists_xiZero_near_thetaZero m N (by positivity) ht hz hzero

/-- Above a fixed height, the VK cap is strictly inside the classical cap
and the theta prefix is nonvanishing on the entire outer rectangle. -/
theorem exists_vkWindowCap_zeroFree :
    ∃ m₀ : ℕ, ∀ m ≥ m₀,
      3 / 4 < vkWindowCapAbscissa m ∧
      vkWindowCapAbscissa m < burnolCapAbscissa m ∧
      burnolCapAbscissa m < 1 ∧
      ∀ N ≥ polySqrtPrefix 1 m,
        ∀ z ∈ Icc (vkWindowCapAbscissa m) (3 / 2) ×ℂ
          Icc (burnolUnitLower m) (burnolUnitUpper m),
          _root_.RHTower.finiteThetaAmplitude N z ≠ 0 := by
  obtain ⟨γ₀, hγ₀, hvk⟩ := exists_re_le_of_mem_zetaCarrier_vk
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp eventually_inv_log_le_vkWidth
  refine ⟨Nat.ceil (max γ₀ T) + 12, fun m hm => ?_⟩
  have hmR : max γ₀ T + 12 ≤ (m : ℝ) := by
    have hmR' : (Nat.ceil (max γ₀ T) : ℝ) + 12 ≤ (m : ℝ) := by exact_mod_cast hm
    linarith only [hmR', Nat.le_ceil (max γ₀ T)]
  have hmγ : γ₀ + 12 ≤ (m : ℝ) := by linarith only [hmR, le_max_left γ₀ T]
  have hmT : T + 12 ≤ (m : ℝ) := by linarith only [hmR, le_max_right γ₀ T]
  set G : ℝ := ((m + 5 : ℕ) : ℝ) with hGdef
  have hG : Real.exp (Real.exp 30) ≤ G := by
    rw [hGdef]; push_cast; linarith only [hmγ, hγ₀]
  have hG0 : 0 < G := (Real.exp_pos _).trans_le hG
  have hlogG : 0 < Real.log G := by
    exact (Real.exp_pos 30).trans_le ((Real.le_log_iff_exp_le hG0).mpr hG)
  have hw := vkWidth_bounds hG
  have hlogWidth : 1 / Real.log G ≤ vkZeroFreeWidth G := hT G (by
    rw [hGdef]; push_cast; linarith only [hmT])
  have hσ0 : 3 / 4 < vkWindowCapAbscissa m := by
    change 3 / 4 < 1 - vkZeroFreeWidth G / 2
    linarith only [hw.2]
  have hσold : vkWindowCapAbscissa m < burnolCapAbscissa m := by
    change 1 - vkZeroFreeWidth G / 2 < 1 - 1 / (116 * Real.log G)
    have hpos : 0 < 1 / Real.log G := by positivity
    have he : 1 / (116 * Real.log G) = (1 / Real.log G) / 116 := by ring
    rw [he]
    linarith only [hlogWidth, hpos]
  refine ⟨hσ0, hσold, (burnolCapAbscissa_mem_Ioo m).2, fun N hN z hz hzero => ?_⟩
  obtain ⟨⟨hxlo, hxhi⟩, ⟨hylo, hyhi⟩⟩ := hz
  have hbdry := burnolUnit_bdry_regular m
    ((burnolPrefix_le_capCancelSqrtPrefix m).trans
      ((capCancelSqrtPrefix_le_polySqrtPrefix 1 m).trans hN))
  by_cases hedge : z.re = 3 / 2 ∨ z.im = burnolUnitLower m ∨ z.im = burnolUnitUpper m
  · exact edge_ne_zero_of_bdry_regular (burnolUnitLower_le_upper m) hbdry
      ⟨by linarith only [hσ0, hxlo], hxhi⟩ ⟨hylo, hyhi⟩ (Or.inr hedge) hzero
  · push Not at hedge
    have hzopen : -1 / 2 < z.re ∧ z.re < 3 / 2 ∧
        burnolUnitLower m < z.im ∧ z.im < burnolUnitUpper m :=
      ⟨by linarith only [hσ0, hxlo], lt_of_le_of_ne hxhi hedge.1,
        lt_of_le_of_ne hylo hedge.2.1.symm, lt_of_le_of_ne hyhi hedge.2.2⟩
    obtain ⟨w, hwmem, hdist⟩ := exists_xiZero_near_thetaZero_polyPrefix m hN hzopen hzero
    obtain ⟨⟨hw0, hw1, hwylo, hwyhi⟩, hwxi⟩ := (mem_burnolUnitXiZeros_iff m w).mp hwmem
    obtain ⟨hy₁, _, _, hy₂, _⟩ := burnolUnit_coords m
    have hwimlo : γ₀ ≤ |w.im| := by
      have hlow : (m : ℝ) - 3 ≤ w.im := by
        have hc := burnolUnit_coords m
        linarith only [hc.2.2.1, hc.2.2.2.2, hwylo]
      exact (by linarith only [hmγ, hlow] : γ₀ ≤ w.im).trans (le_abs_self _)
    have hwimhi : |w.im| ≤ G := by
      rw [abs_le, hGdef]
      constructor <;> (push_cast; linarith only
        [hy₁, hy₂, hwylo, hwyhi, (Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))])
    have hwne1 : w ≠ 1 := fun he => by rw [he] at hw1; simp at hw1
    have hwzeta := (_root_.RHTower.xi_eq_zero_iff hw0 hwne1).mp hwxi
    have hcarrier : w ∈ _root_.Zeta23.zetaZeroConfig.carrier := ⟨hwzeta, hw0, hw1⟩
    have hwre := hvk w hcarrier hwimlo
    have hwide := vkZeroFreeWidth_antitone (hγ₀.trans hwimlo) hwimhi
    have hre : z.re - w.re ≤ 1 / (16 * ((m + 6 : ℕ) : ℝ)) :=
      (le_abs_self _).trans ((Complex.abs_re_le_norm (z - w)).trans hdist)
    have hlogle : Real.log G ≤ ((m + 6 : ℕ) : ℝ) := by
      have hb := Real.log_le_sub_one_of_pos hG0
      rw [hGdef] at hb ⊢
      push_cast at hb ⊢
      linarith only [hb]
    have hr : 1 / (16 * ((m + 6 : ℕ) : ℝ)) ≤ vkZeroFreeWidth G / 16 := by
      calc 1 / (16 * ((m + 6 : ℕ) : ℝ)) = (1 / ((m + 6 : ℕ) : ℝ)) / 16 := by ring
        _ ≤ (1 / Real.log G) / 16 :=
          div_le_div_of_nonneg_right (one_div_le_one_div_of_le hlogG hlogle) (by norm_num)
        _ ≤ vkZeroFreeWidth G / 16 := div_le_div_of_nonneg_right hlogWidth (by norm_num)
    change 1 - vkZeroFreeWidth G / 2 ≤ z.re at hxlo
    linarith only [hxlo, hwre, hwide, hre, hr, hw.1]

/-- Cauchy cancellation and the inner-cap reading at VK strength. -/
theorem exists_vkWindowCap_cancellation :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ N ≥ polySqrtPrefix 1 m,
      (∀ t : ℝ, rightEdgeFlux (burnolUnitLower m) (burnolUnitUpper m) N t +
          horizCapFlux (vkWindowCapAbscissa m) (3 / 2)
            (burnolUnitLower m) (burnolUnitUpper m) N t =
          vertFlux (vkWindowCapAbscissa m) (burnolUnitLower m) (burnolUnitUpper m) N t) ∧
      (∀ t : ℝ, rightHalfPort (burnolUnitLower m) (burnolUnitUpper m) N t =
          vertFlux (vkWindowCapAbscissa m) (burnolUnitLower m) (burnolUnitUpper m) N t +
            horizCapFlux (1 / 2) (vkWindowCapAbscissa m)
              (burnolUnitLower m) (burnolUnitUpper m) N t) ∧
      ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ,
        ‖vertFlux (vkWindowCapAbscissa m) (burnolUnitLower m) (burnolUnitUpper m) N t‖ ≤
          M * Real.exp ((1 / 2 - vkZeroFreeWidth ((m + 5 : ℕ) : ℝ) / 2) * t) := by
  obtain ⟨m₀, hcap⟩ := exists_vkWindowCap_zeroFree
  refine ⟨m₀, fun m hm N hN => ?_⟩
  obtain ⟨hlo, hmid, hhi, hnz⟩ := hcap m hm
  have hσhi : vkWindowCapAbscissa m ≤ 3 / 2 := by linarith only [hmid, hhi]
  have hσlo : 1 / 2 ≤ vkWindowCapAbscissa m := by linarith only [hlo]
  have hreg := burnolUnit_bdry_regular m
    ((burnolPrefix_le_capCancelSqrtPrefix m).trans
      ((capCancelSqrtPrefix_le_polySqrtPrefix 1 m).trans hN))
  have hrect := hnz N hN
  refine ⟨fun t => rightEdgeFlux_add_horizCapFlux_eq_vertFlux hσhi
      (burnolUnitLower_le_upper m) N hrect t,
    fun t => rightHalfPort_eq_vertFlux_add_innerCapFlux hσlo hσhi
      (burnolUnitLower_le_upper m) N hreg hrect t, ?_⟩
  obtain ⟨M, hM, hbound⟩ := exists_norm_vertFlux_le_exp
    (σ := vkWindowCapAbscissa m) (burnolUnitLower_le_upper m) N
    (fun y hy => hrect ((vkWindowCapAbscissa m : ℂ) + (y : ℂ) * I)
      ⟨⟨by simp, by simpa using hσhi⟩, by simpa using hy⟩)
  refine ⟨M, hM, fun t => ?_⟩
  have hexp : vkWindowCapAbscissa m - 1 / 2 =
      1 / 2 - vkZeroFreeWidth ((m + 5 : ℕ) : ℝ) / 2 := by
    unfold vkWindowCapAbscissa
    ring
  simpa only [hexp] using hbound t

/-- The height from which the explicit VK cap is valid. -/
def vkWindowCapCutoff : ℕ := Classical.choose exists_vkWindowCap_zeroFree

theorem vkWindowCapCutoff_spec (m : ℕ) (hm : vkWindowCapCutoff ≤ m) :
    3 / 4 < vkWindowCapAbscissa m ∧
    vkWindowCapAbscissa m < burnolCapAbscissa m ∧
    burnolCapAbscissa m < 1 ∧
    ∀ N ≥ polySqrtPrefix 1 m,
      ∀ z ∈ Icc (vkWindowCapAbscissa m) (3 / 2) ×ℂ
        Icc (burnolUnitLower m) (burnolUnitUpper m),
        _root_.RHTower.finiteThetaAmplitude N z ≠ 0 :=
  Classical.choose_spec exists_vkWindowCap_zeroFree m hm

/-- The VK cap above its height threshold, with the classical cap on the
finitely many lower windows. -/
def globalVkWindowCap (m : ℕ) : ℝ :=
  if vkWindowCapCutoff ≤ m then vkWindowCapAbscissa m else burnolCapAbscissa m

theorem globalVkWindowCap_bounds (m : ℕ) : 3 / 4 < globalVkWindowCap m ∧ globalVkWindowCap m < 1 := by
  by_cases hm : vkWindowCapCutoff ≤ m
  · rw [globalVkWindowCap, if_pos hm]
    obtain ⟨hlo, hmid, hhi, _⟩ := vkWindowCapCutoff_spec m hm
    exact ⟨hlo, hmid.trans hhi⟩
  · rw [globalVkWindowCap, if_neg hm]
    exact burnolCapAbscissa_mem_Ioo m

theorem globalVkWindowCap_zeroFree (m : ℕ) {N : ℕ} (hN : polySqrtPrefix 1 m ≤ N) :
    ∀ z ∈ Icc (globalVkWindowCap m) (3 / 2) ×ℂ
      Icc (burnolUnitLower m) (burnolUnitUpper m),
      _root_.RHTower.finiteThetaAmplitude N z ≠ 0 := by
  by_cases hm : vkWindowCapCutoff ≤ m
  · rw [globalVkWindowCap, if_pos hm]
    exact (vkWindowCapCutoff_spec m hm).2.2.2 N hN
  · rw [globalVkWindowCap, if_neg hm]
    exact (exists_burnol_subHalfExp_cap_cancellation m
      ((capCancelSqrtPrefix_le_polySqrtPrefix 1 m).trans hN)).2.2.2.1

/-- The reduced right-port reading along the VK cap and its inner horizontal edges. -/
def vkInnerCapFlux (m N : ℕ) (t : ℝ) : ℂ :=
  vertFlux (globalVkWindowCap m) (burnolUnitLower m) (burnolUnitUpper m) N t +
    horizCapFlux (1 / 2) (globalVkWindowCap m) (burnolUnitLower m) (burnolUnitUpper m) N t

/-- Contour deformation preserves the complete right-port reading exactly. -/
theorem vkInnerCapFlux_eq_rightHalfPort (m : ℕ) {N : ℕ} (hN : polySqrtPrefix 1 m ≤ N) :
    vkInnerCapFlux m N = rightHalfPort (burnolUnitLower m) (burnolUnitUpper m) N := by
  obtain ⟨hlo, hhi⟩ := globalVkWindowCap_bounds m
  have hbdry := burnolUnit_bdry_regular m
    ((burnolPrefix_le_capCancelSqrtPrefix m).trans
      ((capCancelSqrtPrefix_le_polySqrtPrefix 1 m).trans hN))
  funext t
  exact (rightHalfPort_eq_vertFlux_add_innerCapFlux
    (by linarith only [hlo]) (by linarith only [hhi]) (burnolUnitLower_le_upper m)
    N hbdry (globalVkWindowCap_zeroFree m hN) t).symm

/-- The VK cap retains the same off-line source and bounded remainder. -/
theorem vk_innerCap_source_identity (m : ℕ) {N : ℕ} (hN : polySqrtPrefix 1 m ≤ N) (t : ℝ) :
    vkInnerCapFlux m N t =
      burnolInnerOffLineSource m N ((capCancelSqrtPrefix_le_polySqrtPrefix 1 m).trans hN) t +
        burnolInnerBoundedSource m N ((capCancelSqrtPrefix_le_polySqrtPrefix 1 m).trans hN) t -
          leftHalfPort (burnolUnitLower m) (burnolUnitUpper m) N t := by
  rw [vkInnerCapFlux_eq_rightHalfPort m hN,
    (burnol_rightHalfPort_eq_vertFlux_add_innerCapFlux m
      ((capCancelSqrtPrefix_le_polySqrtPrefix 1 m).trans hN)).2.2.1 t]
  exact burnol_innerCap_source_identity m _ t

theorem vk_integrable_innerCap_iff_offLineSource (m : ℕ) {N : ℕ}
    (hN : polySqrtPrefix 1 m ≤ N) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => Real.exp (-(x * t)) * ‖vkInnerCapFlux m N t‖ ^ 2) (Ioi 0) ↔
      IntegrableOn (fun t : ℝ => Real.exp (-(x * t)) *
        ‖burnolInnerOffLineSource m N ((capCancelSqrtPrefix_le_polySqrtPrefix 1 m).trans hN) t‖ ^ 2)
        (Ioi 0) := by
  have hcap := (capCancelSqrtPrefix_le_polySqrtPrefix 1 m).trans hN
  have hid := (burnol_rightHalfPort_eq_vertFlux_add_innerCapFlux m hcap).2.2.1
  rw [vkInnerCapFlux_eq_rightHalfPort m hN]
  simp_rw [hid]
  exact integrableOn_innerCapFlux_iff_offLineSource m hcap hx

/-- The arithmetic index at a stabilized stage is independent of the prefix.
An integrable port at any later stabilized prefix therefore kills the index
at every stabilized prefix. -/
theorem unitStage_index_zero_of_port_integrable (m S N N' : ℕ)
    (hN : doorUnitPrefix m S ≤ N) (hN' : doorUnitPrefix m S ≤ N')
    (hint : IntegrableOn
      (fun t : ℝ => Real.exp (-((1 / (2 * (doorUnitStage m S : ℝ))) * t)) *
        ‖rightHalfPort (burnolUnitLower m) (burnolUnitUpper m) N' t‖ ^ 2) (Ioi 0)) :
    (∀ u : HTGeometry.UnitCircle,
      centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m)
        (doorUnitStage m S) N u ≠ 0) ∧
    HTGeometry.fredholmIndex
      (centeredThetaCollisionOperator (burnolUnitLower m) (burnolUnitUpper m)
        (doorUnitStage m S) N) = 0 := by
  obtain ⟨hstage, hspec⟩ := doorUnitStage_spec m S
  obtain ⟨hnz, hindex⟩ := hspec N hN
  have hindex' := (hspec N' hN').2
  have hn6 : 6 ≤ doorUnitStage m S := (le_max_right S 6).trans (Finset.mem_Icc.mp hstage).1
  have hnpos : (0 : ℝ) < (doorUnitStage m S : ℝ) := by exact_mod_cast (show 0 < doorUnitStage m S by omega)
  have hbdry := burnolUnit_bdry_regular m ((burnolPrefix_le_doorUnitPrefix m S).trans hN')
  have hzint := (integrableOn_windowEnergy_iff_rightHalfPort
    (burnolUnitLower_le_upper m) N' hbdry (by positivity : (0 : ℝ) ≤ 1 / (2 * (doorUnitStage m S : ℝ)))).mpr hint
  let W := centeredThetaWindow (burnolUnitLower_le_upper m) N' hbdry
  have hgap : 1 / 2 - zhukovskyMajorAxis (doorUnitStage m S) = 1 / (2 * (doorUnitStage m S : ℝ)) := by
    rw [zhukovskyMajorAxis_of_six_le hn6]
    ring
  have hW : IntegrableOn
      (fun t : ℝ => Real.exp (-((1 / 2 - zhukovskyMajorAxis (doorUnitStage m S)) * t)) *
        ‖W.expSum t‖ ^ 2) (Ioi 0) := by
    simpa only [W, hgap, centeredThetaWindow_expSum] using hzint
  have hzero := W.fredholmIndex_eq_zero_of_integrableOn_energy
    (eval_centeredThetaDifferencePoly_eq_window (burnolUnitLower_le_upper m) N' hbdry) hW
  refine ⟨hnz, ?_⟩
  exact hindex.trans (hindex'.symm.trans hzero)

/-- Increasing every prefix threshold by an arbitrary amount preserves the
all-polynomial-stage RH receiver. -/
theorem polynomialStage_cofinal_prefix_iff (P : ℕ → ℕ → ℕ) :
    RiemannHypothesis ↔ ∀ k m : ℕ, ∀ N ≥ max (polySqrtPrefix k m) (P k m),
      IntegrableOn
        (fun t : ℝ => Real.exp (-((1 / (2 * (doorUnitStage m ((m + 6) ^ k) : ℝ))) * t)) *
          ‖rightHalfPort (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2) (Ioi 0) := by
  constructor
  · intro hRH k m N hN
    have hport := (riemannHypothesis_polynomialStage_tfae.out 0 3).mp hRH
    exact hport k m N ((le_max_left _ _).trans hN)
  · intro h
    apply (riemannHypothesis_polynomialStage_tfae.out 5 0).mp
    intro k m N hN
    have hd := (doorUnitPrefix_le_besselUnitPrefix m ((m + 6) ^ k)).trans
      ((besselUnitPrefix_le_polySqrtPrefix_of_le k m le_rfl).trans hN)
    exact unitStage_index_zero_of_port_integrable m ((m + 6) ^ k) N (max N (P k m))
      hd (hd.trans (le_max_left _ _))
      (h k m _ (max_le (hN.trans (le_max_left _ _)) (le_max_right _ _)))

/-- The same prefix invariance holds for each fixed-degree corridor. -/
theorem fixedDegree_cofinal_prefix_iff {k : ℕ} (hk : 1 ≤ k) (P : ℕ → ℕ) :
    (∃ T₁ C : ℝ, 2 ≤ T₁ ∧ 0 < C ∧ ∀ ρ : ℂ,
      _root_.RHTower.xi ρ = 0 → T₁ ≤ |ρ.im| → |ρ.re - 1 / 2| ≤ C / |ρ.im| ^ k) ↔
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀,
      ∀ N ≥ max (polySqrtPrefix k m) (P m), IntegrableOn
        (fun t : ℝ => Real.exp (-((1 / (2 * (fixedPolyDoorStage k c m : ℝ))) * t)) *
          ‖rightHalfPort (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2) (Ioi 0) := by
  constructor
  · intro hcorr
    obtain ⟨c, hc, hc1, m₀, h⟩ := (invPoly_corridor_iff_fixedDegree_polynomialStage hk).out 0 1 |>.mp hcorr
    exact ⟨c, hc, hc1, m₀, fun m hm N hN => (h m hm N ((le_max_left _ _).trans hN)).2⟩
  · rintro ⟨c, hc, hc1, m₀, h⟩
    apply ((invPoly_corridor_iff_fixedDegree_polynomialStage hk).out 3 0).mp
    refine ⟨c, hc, hc1, m₀, fun m hm N hN => ?_⟩
    have hS : Nat.ceil (c * ((m + 6 : ℕ) : ℝ) ^ k) ≤ (m + 6) ^ k :=
      Nat.ceil_le.mpr (by push_cast; exact mul_le_of_le_one_left (by positivity) hc1)
    have hd := (doorUnitPrefix_le_besselUnitPrefix m _).trans
      ((besselUnitPrefix_le_polySqrtPrefix_of_le k m hS).trans hN)
    exact unitStage_index_zero_of_port_integrable m _ N (max N (P m))
      hd (hd.trans (le_max_left _ _))
      (h m hm _ (max_le (hN.trans (le_max_left _ _)) (le_max_right _ _)))

/-- The enlarged schedule is still a constant multiple of `√m+1` at each degree. -/
def vkPolynomialPrefix (k m : ℕ) : ℕ := max (polySqrtPrefix k m) (polySqrtPrefix 1 m)

theorem vkPolynomialPrefix_eq (k m : ℕ) :
    vkPolynomialPrefix k m = max (polySqrtConst k) (polySqrtConst 1) * (Nat.sqrt m + 1) := by
  unfold vkPolynomialPrefix polySqrtPrefix
  rcases le_total (polySqrtConst k) (polySqrtConst 1) with h | h
  · rw [max_eq_right h, max_eq_right (Nat.mul_le_mul_right _ h)]
  · rw [max_eq_left h, max_eq_left (Nat.mul_le_mul_right _ h)]

/-- The all-stage receiver is unchanged by the VK contour and prefix enlargement. -/
theorem vk_innerCap_allPolynomialStages_iff_riemannHypothesis :
    RiemannHypothesis ↔ ∀ k m : ℕ, ∀ N ≥ vkPolynomialPrefix k m,
      IntegrableOn
        (fun t : ℝ => Real.exp (-((1 / (2 * (doorUnitStage m ((m + 6) ^ k) : ℝ))) * t)) *
          ‖vkInnerCapFlux m N t‖ ^ 2) (Ioi 0) := by
  have heq := polynomialStage_cofinal_prefix_iff (fun _ m => polySqrtPrefix 1 m)
  constructor
  · intro hRH k m N hN
    rw [vkInnerCapFlux_eq_rightHalfPort m ((le_max_right _ _).trans hN)]
    exact heq.mp hRH k m N hN
  · intro h
    apply heq.mpr
    intro k m N hN
    have hh := h k m N hN
    rwa [vkInnerCapFlux_eq_rightHalfPort m ((le_max_right _ _).trans hN)] at hh

/-- At fixed degree the VK receiver is exactly the inverse-polynomial corridor. -/
theorem vk_innerCap_fixedDegree_iff_invPoly_corridor {k : ℕ} (hk : 1 ≤ k) :
    (∃ T₁ C : ℝ, 2 ≤ T₁ ∧ 0 < C ∧ ∀ ρ : ℂ,
      _root_.RHTower.xi ρ = 0 → T₁ ≤ |ρ.im| → |ρ.re - 1 / 2| ≤ C / |ρ.im| ^ k) ↔
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀,
      ∀ N ≥ vkPolynomialPrefix k m, IntegrableOn
        (fun t : ℝ => Real.exp (-((1 / (2 * (fixedPolyDoorStage k c m : ℝ))) * t)) *
          ‖vkInnerCapFlux m N t‖ ^ 2) (Ioi 0) := by
  have heq := fixedDegree_cofinal_prefix_iff hk (fun m => polySqrtPrefix 1 m)
  constructor
  · intro hcorr
    obtain ⟨c, hc, hc1, m₀, h⟩ := heq.mp hcorr
    refine ⟨c, hc, hc1, m₀, fun m hm N hN => ?_⟩
    rw [vkInnerCapFlux_eq_rightHalfPort m ((le_max_right _ _).trans hN)]
    exact h m hm N hN
  · rintro ⟨c, hc, hc1, m₀, h⟩
    apply heq.mpr
    refine ⟨c, hc, hc1, m₀, fun m hm N hN => ?_⟩
    have hh := h m hm N hN
    rwa [vkInnerCapFlux_eq_rightHalfPort m ((le_max_right _ _).trans hN)] at hh

#print axioms exists_vkWindowCap_zeroFree
#print axioms exists_vkWindowCap_cancellation

#print axioms vk_innerCap_source_identity
#print axioms polynomialStage_cofinal_prefix_iff
#print axioms vk_innerCap_allPolynomialStages_iff_riemannHypothesis
#print axioms vk_innerCap_fixedDegree_iff_invPoly_corridor

end GaloisForLFunctions.ConjugateDiagonalGeometry.WindowPortFlux
