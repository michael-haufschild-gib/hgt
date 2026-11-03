import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheTopCollarHasADyadicSeventhPowerReserve
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TelescopedConductorSplitAndOneNinthWeilPositivity
import GaloisForLFunctions.CompletedArithmeticForms.ConductorPrefixLeakage

/-!
# The critical far complement retains its weighted collar

Conductor orthogonality converts the prefix defect into a logarithmic gap.
Its terminal leakage is paid from the dyadic collar reserve. The conductor
exponent may shrink like `(1 + log log N)^(-5)`, permitting the band–far
cross payment at critical overlap.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset Filter Topology
open scoped Classical BigOperators RealInnerProductSpace Matrix

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis ArithmeticLorentzianGeometry
  RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  CriticalScaleArithmeticRigidity ArithmeticElectrostatics ArithmeticEffectivityTheory

/-- The conductor cutoff lies inside the retained prefix and keeps its logarithmic gap. -/
theorem critical_prefix_cutoff_geometry {θ c : ℝ} {N : ℕ} (hθ : 0 < θ) (hθ36 : θ ≤ 1 / 36)
    (hc1 : 1 ≤ c) (hcL : c ≤ Real.log N) (hL2000 : 2000 ≤ Real.log N)
    (hHL : 256 * Real.exp 2 + 4 ≤ Real.log N)
    (hL2θ : 2 / θ ≤ Real.log N)
    (hL4Dθ : 4 * explicitConductorCutoffConstant / θ ≤ Real.log N)
    (hLX : Real.log N ≤ (N : ℝ) ^ (1 / 36 : ℝ)) (hNθ4 : 4 ≤ (N : ℝ) ^ θ) :
    2 ≤ ⌊(N : ℝ) ^ θ⌋₊ ∧ linearDefectCutoff c ≤ N ∧
      ⌊(N : ℝ) ^ θ⌋₊ * ⌊(N : ℝ) ^ θ⌋₊ ≤ N / linearDefectCutoff c ∧
      2 ≤ N / linearDefectCutoff c ∧
      Real.log N / 2 ≤ Real.log ((N / linearDefectCutoff c : ℕ) : ℝ) ∧
      18 * (1 + Real.log ⌊(N : ℝ) ^ θ⌋₊) ≤ Real.log ((N / linearDefectCutoff c : ℕ) : ℝ) ∧
      (θ / (4 * explicitConductorCutoffConstant)) * Real.log N ≤
        Real.log ⌊(N : ℝ) ^ θ⌋₊ / explicitConductorCutoffConstant - 1 ∧
      Real.log ⌊(N : ℝ) ^ θ⌋₊ ≤ θ * Real.log N := by
  obtain ⟨R, hR⟩ : ∃ R, R = ⌊(N : ℝ) ^ θ⌋₊ := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, T = linearDefectCutoff c := ⟨_, rfl⟩
  rw [← hR, ← hT]
  have hD := explicitConductorCutoffConstant_pos
  have hL1 : 1 ≤ Real.log N := by linarith only [hL2000]
  have hL0 : 0 < Real.log N := by linarith only [hL2000]
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have hN1 : 1 ≤ N := by
    by_contra h
    have : N = 0 := by omega
    subst this; simp at hL0
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN1R
  obtain ⟨hT3, -, -, hTup⟩ := linearDefectCutoff_bounds hc1
  rw [← hT] at hT3 hTup
  have hT1 : 1 ≤ T := by omega
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT1
  obtain ⟨X, hXdef⟩ : ∃ X, X = (N : ℝ) ^ (1 / 36 : ℝ) := ⟨_, rfl⟩
  rw [← hXdef] at hLX
  have hX1 : 1 ≤ X := hL1.trans hLX
  have hX0 : 0 < X := lt_of_lt_of_le one_pos hX1
  have hX36 : X ^ (36 : ℕ) = (N : ℝ) := by
    rw [hXdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hlogX : Real.log X = (1 / 36 : ℝ) * Real.log N := by rw [hXdef, Real.log_rpow hN0]
  have hR2 : 2 ≤ R := by
    rw [hR]; exact Nat.le_floor (by push_cast; linarith only [hNθ4])
  have hRX : (R : ℝ) ≤ X := by
    rw [hR, hXdef]
    exact (Nat.floor_le (by positivity)).trans (Real.rpow_le_rpow_of_exponent_le hN1R hθ36)
  have hTX : (T : ℝ) ≤ X ^ 2 := by
    calc (T : ℝ) ≤ (256 * Real.exp 2 + 4) * c := hTup
      _ ≤ X * X := mul_le_mul (hHL.trans hLX) (hcL.trans hLX) hc0.le hX0.le
      _ = X ^ 2 := by ring
  have hRRT : R * R * T ≤ N := by
    have hh : (R : ℝ) ^ 2 * T ≤ (N : ℝ) := by
      calc (R : ℝ) ^ 2 * T ≤ X ^ 2 * X ^ 2 :=
            mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg R) hRX 2) hTX hT0.le (by positivity)
        _ = X ^ 4 := by ring
        _ ≤ (N : ℝ) := (pow_le_pow_right₀ hX1 (by norm_num : 4 ≤ 36)).trans_eq hX36
    have hhNat : R ^ 2 * T ≤ N := by exact_mod_cast hh
    simpa only [pow_two] using hhNat
  have hRM : R * R ≤ N / T := (Nat.le_div_iff_mul_le (by omega : 0 < T)).mpr hRRT
  have hTN : T ≤ N := by
    have hR1 : 1 ≤ R * R := Nat.mul_pos (by omega) (by omega)
    exact (by simpa only [one_mul] using Nat.mul_le_mul_right T hR1 : T ≤ R * R * T).trans hRRT
  have hM2 : 2 ≤ N / T := (by norm_num : 2 ≤ 2 * 2).trans ((Nat.mul_le_mul hR2 hR2).trans hRM)
  obtain ⟨M, hM⟩ : ∃ M, M = N / T := ⟨_, rfl⟩
  rw [← hM] at hRM hM2 ⊢
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hfloor : (N : ℝ) < ((M : ℝ) + 1) * T := by
    have hh : N < (M + 1) * T := by
      rw [hM]; simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ N (show 0 < T by omega)
    exact_mod_cast hh
  have hratio : Real.log N - Real.log M ≤ Real.log (2 * (T : ℝ)) := by
    rw [← Real.log_div hN0.ne' hM0.ne']
    apply Real.log_le_log (div_pos hN0 hM0)
    apply (div_le_iff₀ hM0).mpr
    nlinarith only [hfloor, mul_nonneg (sub_nonneg.mpr hM1) hT0.le]
  have hlog2T : Real.log (2 * (T : ℝ)) ≤ Real.log N / 4 + 1 := by
    have hh := Real.log_le_log (by positivity : 0 < 2 * (T : ℝ))
      (mul_le_mul_of_nonneg_left hTX zero_le_two)
    rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hX0.ne'), Real.log_pow, hlogX] at hh
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    push_cast at hh
    linarith only [hh, h2, hL0]
  have hhalf_M : Real.log N / 2 ≤ Real.log M := by linarith only [hratio, hlog2T, hL2000]
  have hlogR_le36 : Real.log R ≤ (1 / 36 : ℝ) * Real.log N := by
    have hh := Real.log_le_log (by exact_mod_cast (show 0 < R by omega)) hRX
    rwa [hlogX] at hh
  have hlogM_cond : 18 * (1 + Real.log R) ≤ Real.log M := by
    linarith only [hlogR_le36, hratio, hlog2T, hL2000]
  have hlogR_le : Real.log R ≤ θ * Real.log N := by
    have hh := Real.log_le_log (by exact_mod_cast (show 0 < R by omega))
      (show (R : ℝ) ≤ (N : ℝ) ^ θ by rw [hR]; exact Nat.floor_le (by positivity))
    rwa [Real.log_rpow hN0] at hh
  have hR_half : (1 / 2 : ℝ) * (N : ℝ) ^ θ ≤ (R : ℝ) := by
    have hgt : (N : ℝ) ^ θ - 1 < (R : ℝ) := by
      rw [hR]; exact sub_lt_iff_lt_add.mpr (Nat.lt_floor_add_one _)
    linarith only [hNθ4, hgt]
  have hlogR_lb : (θ / 2) * Real.log N ≤ Real.log R := by
    have hlog2 : Real.log 2 ≤ 1 := by
      linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hpos : 0 < (N : ℝ) ^ θ := by linarith only [hNθ4]
    have h1 := Real.log_le_log (by positivity) hR_half
    rw [Real.log_mul (by norm_num) hpos.ne', one_div, Real.log_inv, Real.log_rpow hN0] at h1
    have h2 : 2 ≤ θ * Real.log N := by
      have h := (div_le_iff₀ hθ).mp hL2θ; linarith only [h]
    linarith only [h1, hlog2, h2]
  have hgap : (θ / (4 * explicitConductorCutoffConstant)) * Real.log N ≤
      Real.log R / explicitConductorCutoffConstant - 1 := by
    have hdiv := div_le_div_of_nonneg_right hlogR_lb hD.le
    have h1 : (θ / 2) * Real.log N / explicitConductorCutoffConstant =
        2 * ((θ / (4 * explicitConductorCutoffConstant)) * Real.log N) := by
      field_simp; ring
    have h4D : 4 * explicitConductorCutoffConstant ≤ θ * Real.log N := by
      have h := (div_le_iff₀ hθ).mp hL4Dθ; linarith only [h]
    have h2 : 1 ≤ (θ / (4 * explicitConductorCutoffConstant)) * Real.log N := by
      rw [div_mul_eq_mul_div, one_le_div (by positivity)]
      linarith only [h4D]
    linarith only [hdiv, h1, h2]
  exact ⟨hR2, hTN, hRM, hM2, hhalf_M, hlogM_cond, hgap, hlogR_le⟩

/-- Prefix coercivity and the weighted collar survive simultaneously at a
small critical multiple, uniformly down to an almost-polynomial conductor cutoff. -/
theorem exists_critical_multiple_weighted_far_complement :
    ∃ K : ℝ, 0 < K ∧ 2 * K ≤ 1 ∧
      ∀ᶠ N : ℕ in atTop, ∀ c θ : ℝ,
        1 ≤ c → c ≤ 2 * K * Real.log (N : ℝ) ^ (1 / 8 : ℝ) →
        1 / (1 + Real.log (Real.log (N : ℝ))) ^ 5 ≤ θ → θ ≤ 1 / 4096 →
        ∀ z ∈ (conductorSubspace ⌊(N : ℝ) ^ θ⌋₊ N)ᗮ,
          (θ * Real.log N / (8 * explicitConductorCutoffConstant)) *
              (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension z n ^ 2) +
            (dyadicTopMassConstant * Real.log N / (16 * c ^ 7)) *
              topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension z) ≤
            completeWeilEnergy tiltedUnitSpline c N z := by
  obtain ⟨Kfar, hKfar, hKfar1, hfar⟩ := exists_critical_multiple_far_reserve
  let D := explicitConductorCutoffConstant
  let g := dyadicTopMassConstant
  let H := 256 * Real.exp 2 + 4
  let C := 7 * (5 + Real.log (2 * H)) / (2 * D)
  have hD : 0 < D := explicitConductorCutoffConstant_pos
  have hg : 0 < g := dyadicTopMassConstant_pos
  have hH1 : 1 ≤ H := by
    dsimp only [H]
    linarith only [Real.exp_pos 2]
  have hlogH : 0 ≤ Real.log (2 * H) := Real.log_nonneg (by linarith only [hH1])
  have hC : 0 < C := by dsimp only [C]; positivity
  let K := min Kfar (min (1 / 2) (g / (64 * (C + 1))))
  have hK : 0 < K := by dsimp only [K]; positivity
  have hKfar' : K ≤ Kfar := min_le_left _ _
  have hKhalf : K ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hKC : K ≤ g / (64 * (C + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have h2K : 2 * K ≤ 1 := by linarith only [hKhalf]
  refine ⟨K, hK, h2K, ?_⟩
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hfar 5 (show 0 < 1 / (16 * D) by positivity),
    eventually_log_nat_le_rpow_36_one_ninth,
    hLlim.eventually_ge_atTop (2000 + H),
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 5
      (by norm_num : (0 : ℝ) < 1) (4 * D + 4))]
    with N hfarN hLX hlarge hpoly
  intro c θ hc1 hc hθlo hθhi z hz
  let L := Real.log (N : ℝ)
  let T := linearDefectCutoff c
  let M := N / T
  let R := ⌊(N : ℝ) ^ θ⌋₊
  have hL2000 : 2000 ≤ L := by linarith only [hlarge, hH1]
  have hL1 : 1 ≤ L := by linarith only [hL2000]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have ht : 0 < (1 + Real.log L) ^ 5 := by
    have := Real.log_nonneg hL1
    positivity
  have hθ : 0 < θ := (one_div_pos.mpr ht).trans_le hθlo
  have hθ36 : θ ≤ 1 / 36 := hθhi.trans (by norm_num)
  have hθ1 : θ ≤ 1 := hθhi.trans (by norm_num)
  have hθL : 4 * D + 4 ≤ θ * L := by
    have hpoly' : (4 * D + 4) * (1 + Real.log L) ^ 5 ≤ L := by
      simpa only [Real.rpow_one] using hpoly
    have h₁ := (le_div_iff₀ ht).mpr hpoly'
    have h₂ := mul_le_mul_of_nonneg_right hθlo hL0.le
    change 1 / (1 + Real.log L) ^ 5 * L ≤ θ * L at h₂
    calc
      _ ≤ L / (1 + Real.log L) ^ 5 := h₁
      _ ≤ θ * L := (by ring : L / (1 + Real.log L) ^ 5 =
        1 / (1 + Real.log L) ^ 5 * L).trans_le h₂
  have h2θ : 2 / θ ≤ L := by
    rw [div_le_iff₀ hθ]
    linarith only [hθL, hD]
  have h4Dθ : 4 * D / θ ≤ L := by
    rw [div_le_iff₀ hθ]
    linarith only [hθL]
  have hN1 : 1 ≤ N := by
    by_contra hn
    have : N = 0 := by omega
    subst this
    simp [L] at hL0
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNθ4 : 4 ≤ (N : ℝ) ^ θ := by
    rw [Real.rpow_def_of_pos hN0]
    have h := Real.add_one_le_exp (L * θ)
    change 4 ≤ Real.exp (L * θ)
    linarith only [h, hθL, hD]
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hcroot : c ≤ L ^ (1 / 8 : ℝ) := hc.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right h2K
      (Real.rpow_nonneg hL0.le (1 / 8 : ℝ)))
  have hcL : c ≤ L := hcroot.trans ((Real.rpow_le_rpow_of_exponent_le hL1
    (by norm_num : (1 / 8 : ℝ) ≤ 1)).trans_eq (Real.rpow_one L))
  obtain ⟨hR2, hTN, hRM, hM2, hhalf, hlogM, hgap, hlogR⟩ :=
    critical_prefix_cutoff_geometry hθ hθ36 hc1 hcL hL2000
      (by linarith only [hlarge]) h2θ h4Dθ hLX hNθ4
  change Real.log (R : ℝ) ≤ θ * L at hlogR
  have hlogM0 : 0 < Real.log (M : ℝ) := (by positivity : 0 < L / 2).trans_le hhalf
  have hk : 0 < Real.log (R : ℝ) / D - 1 := (by positivity : 0 < θ / (4 * D) * L).trans_le hgap
  have hscale : D ≤ Real.log (R : ℝ) := by
    have h := (lt_div_iff₀ hD).mp (show 1 < Real.log (R : ℝ) / D by linarith only [hk])
    linarith only [h]
  have hpre := poleDefect_prefix_ge_of_conductor_orthogonal hR2 hM2
    (Nat.div_le_self N T) hRM hlogM hscale hz
  have hz1 : z ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hz v (conductorSubspace_mono (by omega : 1 ≤ R) N hv)
  have hcFar : c ≤ 2 * Kfar * L ^ (1 / 8 : ℝ) := hc.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKfar' (by norm_num)) (by positivity))
  have hf := hfarN c hc1 hcFar hz1
  obtain ⟨hT3, -, -, hTup⟩ := linearDefectCutoff_bounds hc1
  have hTB := terminalPacketCost_nat_div_le (Q := R) (by omega) hTN hRM
  have hlog2T : Real.log (2 * (T : ℝ)) ≤ Real.log (2 * H) + c := by
    have hTpos : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
    have h := Real.log_le_log (show 0 < 2 * (T : ℝ) by positivity)
      (mul_le_mul_of_nonneg_left hTup zero_le_two)
    rw [show 2 * (H * c) = (2 * H) * c by ring,
      Real.log_mul (by positivity) hc0.ne'] at h
    linarith only [h, Real.log_le_sub_one_of_pos hc0]
  let B := terminalPacketCost R M N / Real.log (M : ℝ)
  let k := Real.log (R : ℝ) / D - 1
  have hB0 : 0 ≤ B := div_nonneg (terminalPacketCost_nonneg R (Nat.div_le_self N T)) hlogM0.le
  have hB : B ≤ 2 * (4 + Real.log (2 * H) + c) / L := by
    apply (div_le_div_iff₀ hlogM0 hL0).mpr
    have hcost : terminalPacketCost R M N ≤ 4 + Real.log (2 * H) + c := by
      linarith only [hTB, hlog2T]
    have hnum : 0 ≤ 4 + Real.log (2 * H) + c := by positivity
    change L / 2 ≤ Real.log (M : ℝ) at hhalf
    have h₁ := mul_le_mul_of_nonneg_right hcost hL0.le
    have h₂ := mul_le_mul_of_nonneg_left hhalf hnum
    nlinarith only [h₁, h₂]
  have hkL : k ≤ L / D := by
    have h₁ := div_le_div_of_nonneg_right hlogR hD.le
    have h₂ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hθ1 hL0.le) hD.le
    simp only [one_mul] at h₂
    exact (sub_le_self _ zero_le_one).trans (h₁.trans h₂)
  have hleak : (7 / 4 : ℝ) * k * B ≤ g * L / (16 * c ^ 7) := by
    have hbound : (7 / 4 : ℝ) * k * B ≤ C * c := by
      calc
        _ ≤ (7 / 4 : ℝ) * (L / D) * (2 * (4 + Real.log (2 * H) + c) / L) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hkL (by norm_num)) hB hB0 (by positivity)
        _ = 7 * (4 + Real.log (2 * H) + c) / (2 * D) := by field_simp; ring
        _ ≤ C * c := by
          have h := mul_nonneg (show 0 ≤ 4 + Real.log (2 * H) by positivity) (sub_nonneg.mpr hc1)
          have hnum : 7 * (4 + Real.log (2 * H) + c) ≤
              7 * (5 + Real.log (2 * H)) * c := by nlinarith only [h]
          exact (div_le_div_of_nonneg_right hnum (show 0 ≤ 2 * D by positivity)).trans_eq
            (by dsimp only [C]; ring)
    have h2K8 : (2 * K) ^ 8 ≤ 2 * K := by
      have h7 := pow_le_one₀ (show 0 ≤ 2 * K by positivity) h2K (n := 7)
      calc
        _ = (2 * K) * (2 * K) ^ 7 := by ring
        _ ≤ (2 * K) * 1 := mul_le_mul_of_nonneg_left h7 (by positivity)
        _ = _ := mul_one _
    have hc8 : c ^ 8 ≤ 2 * K * L := by
      calc
        _ ≤ (2 * K * L ^ (1 / 8 : ℝ)) ^ 8 := pow_le_pow_left₀ hc0.le hc 8
        _ = (2 * K) ^ 8 * L := by
          rw [mul_pow, ← Real.rpow_natCast (L ^ (1 / 8 : ℝ)), ← Real.rpow_mul hL0.le]; norm_num
        _ ≤ _ := mul_le_mul_of_nonneg_right h2K8 hL0.le
    have hCK : 32 * C * K ≤ g := by
      have h := (le_div_iff₀ (show 0 < 64 * (C + 1) by positivity)).mp hKC
      have hCK0 : 0 ≤ C * K := mul_nonneg hC.le hK.le
      nlinarith only [h, hCK0, hK]
    apply hbound.trans
    apply (le_div_iff₀ (show 0 < 16 * c ^ 7 by positivity)).mpr
    have h₁ := mul_le_mul_of_nonneg_left hc8 (show 0 ≤ 16 * C by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hCK hL0.le
    nlinarith only [h₁, h₂, show C * c * (16 * c ^ 7) = 16 * C * c ^ 8 by ring]
  let P := ∑ n ∈ Icc 1 M, primeHorizonExtension z n ^ 2
  let S := ∑ n ∈ Ioc M N, primeHorizonExtension z n ^ 2
  let S7 := topCollarSeventhMass M N (primeHorizonExtension z)
  have hP : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hS : 0 ≤ S := sum_nonneg fun _ _ => sq_nonneg _
  have hS7 : S ≤ S7 := sum_sq_Ioc_le_topCollarSeventhMass M N _
  have hleakS : (7 / 4 : ℝ) * k * B * S ≤ (g * L / (16 * c ^ 7)) * S7 :=
    (mul_le_mul_of_nonneg_right hleak hS).trans
      (mul_le_mul_of_nonneg_left hS7 (by positivity))
  have hprefixCost : (1 / (16 * D) * L / (1 + Real.log L) ^ 5) * P ≤
      (θ * L / (16 * D)) * P := by
    apply mul_le_mul_of_nonneg_right _ hP
    have h := mul_le_mul_of_nonneg_right hθlo (show 0 ≤ L / (16 * D) by positivity)
    convert h using 1 <;> ring
  have hgapP := mul_le_mul_of_nonneg_right hgap hP
  change θ / (4 * D) * L * P ≤ k * P at hgapP
  let A := θ * L / D * P
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hgapA : A / 4 ≤ k * P := by
    convert hgapP using 1 <;> dsimp only [A] <;> ring
  have hcostA : (1 / (16 * D) * L / (1 + Real.log L) ^ 5) * P ≤ A / 16 :=
    hprefixCost.trans_eq (by dsimp only [A]; ring)
  simp only [mul_div_assoc] at hpre
  change k * ((15 / 16 : ℝ) * P - 2 * B * S) ≤ poleDefect M (primeHorizonExtension z) at hpre
  change (7 / 8 : ℝ) * poleDefect M (primeHorizonExtension z) +
    (g / (8 * c ^ 7)) * L * S7 -
    (1 / (16 * D) * L / (1 + Real.log L) ^ 5) * P ≤ _ at hf
  change (θ * L / (8 * D)) * P + (g * L / (16 * c ^ 7)) * S7 ≤ _
  have hid : (g / (8 * c ^ 7)) * L = 2 * (g * L / (16 * c ^ 7)) := by ring
  rw [hid] at hf
  rw [show θ * L / (8 * D) * P = A / 8 by dsimp only [A]; ring]
  nlinarith only [hpre, hf, hleakS, hcostA, hgapA, hA]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_critical_multiple_weighted_far_complement
