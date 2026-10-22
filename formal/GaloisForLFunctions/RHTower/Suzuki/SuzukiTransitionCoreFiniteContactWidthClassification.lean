import GaloisForLFunctions.RHTower.Suzuki.SuzukiTransitionCoreQuadraticContactWidthLoss

/-!
# Finite-contact width classification for Suzuki transition-core compensation

For every fixed contact order `m ≥ 1`, this module studies the totalized residual

`P_m(N) = E_N^m / C_N^(m-1)`,

where `C_N` is the positive Suzuki transition core and `E_N` is its aligned
Gamma-completed energy. Eventual boundedness of `P_m` forces the completed Green amplitude to
grow no faster than `N^((m-1)/(2m))`. Exact outgoing-charge and logarithmic-lattice identities
transfer that rate to the CCM resolvent, whose quantitative continuation excludes Xi zeros beyond
the same width.

Order one is exactly the RH endpoint. Every fixed order at least two has strictly positive width,
so the full higher finite-contact family loses the endpoint through this compensation/CCM-abscissa
mechanism. All capstones are unconditional closed propositions; residual boundedness occurs inside
their implications.
-/

open Set MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

def suzukiTransitionCoreFiniteContactResidual (m N : ℕ) : ℝ :=
  if _hC : suzukiNaturalApertureTransitionCoreCauchyEnergy N = 0 then 0
  else suzukiTransitionCoreAlignedGammaCompletedEnergy N ^ m /
    suzukiNaturalApertureTransitionCoreCauchyEnergy N ^ (m - 1)

def suzukiFiniteContactWidth (m : ℕ) : ℝ :=
  ((m : ℝ) - 1) / (2 * (m : ℝ))

theorem suzukiTransitionCoreFiniteContactResidual_two_eq_quadratic (N : ℕ) :
    suzukiTransitionCoreFiniteContactResidual 2 N =
      suzukiTransitionCoreQuadraticContactResidual N := by
  unfold suzukiTransitionCoreFiniteContactResidual
  unfold suzukiTransitionCoreQuadraticContactResidual
  split_ifs
  · rfl
  · norm_num

theorem suzukiFiniteContactWidth_two :
    suzukiFiniteContactWidth 2 = 1 / 4 := by
  norm_num [suzukiFiniteContactWidth]

/-- Algebraic information used by finite-contact compensation at one aperture: positive core,
nonnegative aligned energy, the completed-Green square bound, and unit-bounded order-`m`
residual. -/
def SuzukiFiniteContactAlgebraicPacket (m : ℕ) (C E G : ℝ) : Prop :=
  0 < C ∧ 0 ≤ E ∧ G ^ (2 : ℕ) ≤ E ∧ E ^ m / C ^ (m - 1) ≤ 1

private theorem le_pow_two_mul_add_one {x : ℝ} (hx : 0 ≤ x) {m : ℕ} (hm : 1 ≤ m) :
    x ≤ x ^ (2 * m) + 1 := by
  by_cases hx1 : x ≤ 1
  · have hnonneg : 0 ≤ x ^ (2 * m) := by positivity
    linarith
  · have h1x : 1 ≤ x := le_of_not_ge hx1
    have hp : x ^ (1 : ℕ) ≤ x ^ (2 * m) :=
      pow_le_pow_right₀ h1x (by omega)
    have hxpow : x ≤ x ^ (2 * m) := by simpa using hp
    linarith

theorem eventually_abs_completedLowerHardyAmplitude_le_finiteContactWidth_of_bound
    {m : ℕ} (hm : 1 ≤ m) {B : ℝ} (hB0 : 0 ≤ B)
    (hbound : ∀ᶠ N : ℕ in atTop, suzukiTransitionCoreFiniteContactResidual m N ≤ B) :
    ∀ᶠ N : ℕ in atTop,
      |suzukiNaturalApertureCompletedLowerHardyAmplitude N| ≤
        (B * suzukiTransitionCoreLinearEnvelope ^ (m - 1) + 1) *
          Real.exp (suzukiFiniteContactWidth m * Real.log N) := by
  filter_upwards [hbound,
    eventually_suzukiNaturalApertureTransitionCoreCauchyEnergy_ne_zero,
    eventually_completedAnchor_sq_le_suzukiTransitionCoreAlignedEnergy,
    eventually_ge_atTop (2 : ℕ)] with N hres hC hG hN
  have hC0 : 0 < suzukiNaturalApertureTransitionCoreCauchyEnergy N :=
    lt_of_le_of_ne (suzukiNaturalApertureTransitionCoreCauchyEnergy_nonneg N)
      (Ne.symm hC)
  have hCpow0 : 0 < suzukiNaturalApertureTransitionCoreCauchyEnergy N ^ (m - 1) :=
    pow_pos hC0 _
  have hEm : suzukiTransitionCoreAlignedGammaCompletedEnergy N ^ m ≤
      B * suzukiNaturalApertureTransitionCoreCauchyEnergy N ^ (m - 1) := by
    rw [suzukiTransitionCoreFiniteContactResidual, dif_neg hC] at hres
    exact (div_le_iff₀ hCpow0).mp hres
  have hCupper := suzukiNaturalApertureTransitionCoreCauchyEnergy_le_linear N
  have hGpowE :
      |suzukiNaturalApertureCompletedLowerHardyAmplitude N| ^ (2 * m) ≤
        suzukiTransitionCoreAlignedGammaCompletedEnergy N ^ m := by
    rw [pow_mul, sq_abs]
    exact pow_le_pow_left₀ (sq_nonneg _ ) hG m
  have hGpow :
      |suzukiNaturalApertureCompletedLowerHardyAmplitude N| ^ (2 * m) ≤
        (B * suzukiTransitionCoreLinearEnvelope ^ (m - 1)) *
          (N : ℝ) ^ (m - 1) := by
    calc
      _ ≤ suzukiTransitionCoreAlignedGammaCompletedEnergy N ^ m := hGpowE
      _ ≤ B * suzukiNaturalApertureTransitionCoreCauchyEnergy N ^ (m - 1) := hEm
      _ ≤ B * (suzukiTransitionCoreLinearEnvelope * (N : ℝ)) ^ (m - 1) := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀
            (suzukiNaturalApertureTransitionCoreCauchyEnergy_nonneg N)
            (by simpa [suzukiTransitionCoreLinearEnvelope] using hCupper) (m - 1)) hB0
      _ = (B * suzukiTransitionCoreLinearEnvelope ^ (m - 1)) *
          (N : ℝ) ^ (m - 1) := by rw [mul_pow]; ring
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN)
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  let y : ℝ := Real.exp (suzukiFiniteContactWidth m * Real.log N)
  have hy : 0 < y := Real.exp_pos _
  have hyPow : y ^ (2 * m) = (N : ℝ) ^ (m - 1) := by
    dsimp only [y]
    calc
      Real.exp (suzukiFiniteContactWidth m * Real.log N) ^ (2 * m) =
          Real.exp (((2 * m : ℕ) : ℝ) * (suzukiFiniteContactWidth m * Real.log N)) := by
            exact (Real.exp_nat_mul _ _).symm
      _ = Real.exp (((m - 1 : ℕ) : ℝ) * Real.log N) := by
        congr 1
        rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hm]
        unfold suzukiFiniteContactWidth
        field_simp
        ring
      _ = Real.exp (Real.log N) ^ (m - 1) := Real.exp_nat_mul _ _
      _ = (N : ℝ) ^ (m - 1) := by rw [Real.exp_log hNR]
  let z : ℝ := |suzukiNaturalApertureCompletedLowerHardyAmplitude N| / y
  have hz0 : 0 ≤ z := div_nonneg (abs_nonneg _) hy.le
  have hzPow : z ^ (2 * m) ≤ B * suzukiTransitionCoreLinearEnvelope ^ (m - 1) := by
    rw [show z ^ (2 * m) =
      |suzukiNaturalApertureCompletedLowerHardyAmplitude N| ^ (2 * m) /
        y ^ (2 * m) by
      dsimp only [z]
      exact div_pow _ _ (2 * m)]
    rw [hyPow]
    exact (div_le_iff₀ (pow_pos hNR _)).2 (by simpa [mul_assoc] using hGpow)
  have hz := le_pow_two_mul_add_one hz0 hm
  have hzle : z ≤ B * suzukiTransitionCoreLinearEnvelope ^ (m - 1) + 1 :=
    hz.trans (by simpa [add_comm] using add_le_add_right hzPow 1)
  have hrecover :
      |suzukiNaturalApertureCompletedLowerHardyAmplitude N| = z * y := by
    dsimp only [z]
    field_simp [hy.ne']
  rw [hrecover]
  exact mul_le_mul_of_nonneg_right hzle hy.le

theorem suzukiFiniteContactWidth_nonneg {m : ℕ} (hm : 1 ≤ m) :
    0 ≤ suzukiFiniteContactWidth m := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  unfold suzukiFiniteContactWidth
  positivity

theorem suzukiFiniteContactWidth_lt_half {m : ℕ} (hm : 1 ≤ m) :
    suzukiFiniteContactWidth m < 1 / 2 := by
  have hmR : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  unfold suzukiFiniteContactWidth
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ))]
  nlinarith

theorem suzukiFiniteContactWidth_pos {m : ℕ} (hm : 2 ≤ m) :
    0 < suzukiFiniteContactWidth m := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  unfold suzukiFiniteContactWidth
  exact div_pos (by linarith) (by positivity)

/-- **Sharp algebraic endpoint obstruction.** At every fixed contact order `m ≥ 2`, packets with
unit-bounded residual have unbounded Green amplitude. Thus the finite-contact inequalities alone
cannot manufacture the uniform Green/resolvent bound required at the RH endpoint. -/
theorem suzukiFiniteContact_algebraicEndpointNoGo :
    ∀ m : ℕ, 2 ≤ m →
      ¬ ∃ K : ℝ, 0 ≤ K ∧ ∀ C E G : ℝ,
        SuzukiFiniteContactAlgebraicPacket m C E G → |G| ≤ K := by
  intro m hm
  rintro ⟨K, hK0, hK⟩
  let R : ℝ := K + 1
  let C : ℝ := R ^ (2 * m)
  let E : ℝ := R ^ (2 * (m - 1))
  let G : ℝ := R ^ (m - 1)
  have hR1 : 1 ≤ R := by dsimp only [R]; linarith
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hC0 : 0 < C := by dsimp only [C]; positivity
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hG0 : 0 ≤ G := by dsimp only [G]; positivity
  have hGsq : G ^ (2 : ℕ) = E := by
    dsimp only [G, E]
    rw [← pow_mul]
    congr 1
    ac_rfl
  have hEm : E ^ m = C ^ (m - 1) := by
    dsimp only [E, C]
    rw [← pow_mul, ← pow_mul]
    congr 1
    ac_rfl
  have hpacket : SuzukiFiniteContactAlgebraicPacket m C E G := by
    refine ⟨hC0, hE0, hGsq.le, ?_⟩
    rw [hEm, div_self (ne_of_gt (pow_pos hC0 _))]
  have hbound := hK C E G hpacket
  have hmone : 1 ≤ m - 1 := by omega
  have hRG : R ≤ G := by
    have hp : R ^ (1 : ℕ) ≤ R ^ (m - 1) := pow_le_pow_right₀ hR1 hmone
    simpa only [pow_one, G] using hp
  rw [abs_of_nonneg hG0] at hbound
  dsimp only [R] at hRG
  linarith

theorem exists_abs_completedLowerHardyAmplitude_le_finiteContactWidth_of_bound
    {m : ℕ} (hm : 1 ≤ m) {B : ℝ} (hB0 : 0 ≤ B)
    (hbound : ∀ᶠ N : ℕ in atTop, suzukiTransitionCoreFiniteContactResidual m N ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N →
      |suzukiNaturalApertureCompletedLowerHardyAmplitude N| ≤
        K * Real.exp (suzukiFiniteContactWidth m * Real.log N) := by
  have hevent := eventually_abs_completedLowerHardyAmplitude_le_finiteContactWidth_of_bound hm hB0 hbound
  rw [eventually_atTop] at hevent
  obtain ⟨N₀, hN₀⟩ := hevent
  let K₀ : ℝ := B * suzukiTransitionCoreLinearEnvelope ^ (m - 1) + 1
  let K : ℝ := K₀ + ∑ N ∈ Finset.range N₀,
    |suzukiNaturalApertureCompletedLowerHardyAmplitude N|
  have hK₀ : 0 ≤ K₀ := by
    dsimp only [K₀]
    exact add_nonneg
      (mul_nonneg hB0 (pow_nonneg suzukiTransitionCoreLinearEnvelope_nonneg _))
      (by norm_num)
  have hsum0 : 0 ≤ ∑ N ∈ Finset.range N₀,
      |suzukiNaturalApertureCompletedLowerHardyAmplitude N| := by positivity
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro N hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ N by omega))
  have hexp1 : 1 ≤ Real.exp (suzukiFiniteContactWidth m * Real.log N) := by
    rw [Real.one_le_exp_iff]
    exact mul_nonneg (suzukiFiniteContactWidth_nonneg hm) hlog
  by_cases hlarge : N₀ ≤ N
  · have hmain := hN₀ N hlarge
    exact hmain.trans (mul_le_mul_of_nonneg_right
      (show K₀ ≤ K by
        dsimp only [K]
        linarith) (Real.exp_pos _).le)
  · have hmem : N ∈ Finset.range N₀ := Finset.mem_range.mpr (lt_of_not_ge hlarge)
    have hterm : |suzukiNaturalApertureCompletedLowerHardyAmplitude N| ≤
        ∑ n ∈ Finset.range N₀,
          |suzukiNaturalApertureCompletedLowerHardyAmplitude n| := by
      exact Finset.single_le_sum
        (fun i _ => abs_nonneg (suzukiNaturalApertureCompletedLowerHardyAmplitude i)) hmem
    calc
      _ ≤ ∑ n ∈ Finset.range N₀,
          |suzukiNaturalApertureCompletedLowerHardyAmplitude n| := hterm
      _ ≤ K := by
        dsimp only [K]
        linarith
      _ ≤ K * Real.exp (suzukiFiniteContactWidth m * Real.log N) := by
        nlinarith [show 0 ≤ K by dsimp only [K]; positivity]

theorem exists_log_nat_bound_criticalMellinChebyshevResolventSource_finiteContactWidth
    {m : ℕ} (hm : 1 ≤ m) {B : ℝ} (hB0 : 0 ≤ B)
    (hbound : ∀ᶠ N : ℕ in atTop, suzukiTransitionCoreFiniteContactResidual m N ≤ B) :
    ∃ KQ : ℝ, 0 ≤ KQ ∧ ∀ N : ℕ, 2 ≤ N →
      |criticalMellinChebyshevResolventSource (Real.log N)| ≤
        KQ * Real.exp (suzukiFiniteContactWidth m * Real.log N) := by
  obtain ⟨K, hK0, hK⟩ := exists_abs_completedLowerHardyAmplitude_le_finiteContactWidth_of_bound hm hB0 hbound
  let J : ℝ := unitRieszSuzukiPolarUniformBound + unitRieszSuzukiArchUniformBound
  let KQ : ℝ := 2 * (K + J)
  have hPolar0 : 0 ≤ unitRieszSuzukiPolarUniformBound := by
    unfold unitRieszSuzukiPolarUniformBound
    positivity
  have hArch0 : 0 ≤ unitRieszSuzukiArchUniformBound := by
    unfold unitRieszSuzukiArchUniformBound
    exact div_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
      unitRieszSuzukiArchDenominator_pos.le
  have hJ0 : 0 ≤ J := by dsimp only [J]; positivity
  refine ⟨KQ, by dsimp only [KQ]; positivity, ?_⟩
  intro N hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN)
  have hH : unitRieszSuzukiBase ≤ Real.log N := by
    exact (unitRieszSuzukiBase_lt_log_two.trans_le
      (Real.strictMonoOn_log.monotoneOn (by norm_num) hNR
        (by exact_mod_cast hN))).le
  have hGreen : suzukiNaturalApertureCompletedLowerHardyAmplitude N =
      unitRieszSuzukiGreen (Real.log N) := by
    have h := suzukiNaturalApertureCompletedLowerHardyAmplitude_add_two_eq_green (N - 2)
    simpa [Nat.sub_add_cancel hN] using h
  have hP := abs_unitRieszSuzukiPolarCorrection_le hH
  have hA := abs_unitRieszSuzukiArchCorrection_le hH
  have hout := unitRieszSuzuki_outgoing_eq_green hN
  have hcharge := unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half hN
  have hG := hK N hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ N by omega))
  have hexp1 : 1 ≤ Real.exp (suzukiFiniteContactWidth m * Real.log N) := by
    rw [Real.one_le_exp_iff]
    exact mul_nonneg (suzukiFiniteContactWidth_nonneg hm) hlog
  have houtAbs : |unitRieszCoherentCompletedOutgoingCharge N| ≤
      (K + J) * Real.exp (suzukiFiniteContactWidth m * Real.log N) := by
    rw [hout]
    calc
      |unitRieszSuzukiGreen (Real.log N) + unitRieszSuzukiPolarCorrection (Real.log N) -
          unitRieszSuzukiArchCorrection (Real.log N)| ≤
          |unitRieszSuzukiGreen (Real.log N)| +
            |unitRieszSuzukiPolarCorrection (Real.log N)| +
              |unitRieszSuzukiArchCorrection (Real.log N)| := by
        have hs := abs_sub
          (unitRieszSuzukiGreen (Real.log N) + unitRieszSuzukiPolarCorrection (Real.log N))
          (unitRieszSuzukiArchCorrection (Real.log N))
        have ha := abs_add_le (unitRieszSuzukiGreen (Real.log N))
          (unitRieszSuzukiPolarCorrection (Real.log N))
        linarith
      _ ≤ K * Real.exp (suzukiFiniteContactWidth m * Real.log N) + J := by
        rw [← hGreen]
        dsimp only [J]
        linarith
      _ ≤ (K + J) * Real.exp (suzukiFiniteContactWidth m * Real.log N) := by
        nlinarith
  have hres : criticalMellinChebyshevResolventSource (Real.log N) =
      2 * unitRieszCoherentCompletedOutgoingCharge N := by
    linarith
  rw [hres, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  simpa only [KQ, mul_assoc] using
    mul_le_mul_of_nonneg_left houtAbs (by norm_num : (0 : ℝ) ≤ 2)

theorem exists_global_exponential_bound_criticalMellinChebyshevResolventSource_of_log_nat_exponentialBound
    {alpha K : ℝ} (halpha : 0 ≤ alpha) (hK0 : 0 ≤ K)
    (hlog : ∀ N : ℕ, 2 ≤ N →
      |criticalMellinChebyshevResolventSource (Real.log N)| ≤
        K * Real.exp (alpha * Real.log N)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 ≤ t →
      |criticalMellinChebyshevResolventSource t| ≤
        B * Real.exp (alpha * t) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image
    continuous_criticalMellinChebyshevResolventRayRepresentative.norm.continuousOn
  let T : ℝ := K + (Real.log 4 + 5)
  let B : ℝ := max |C| T
  have hT0 : 0 ≤ T := by dsimp only [T]; positivity
  have hB0 : 0 ≤ B := (abs_nonneg C).trans (le_max_left _ _)
  refine ⟨B, hB0, ?_⟩
  intro t ht
  by_cases hhead : t ≤ Real.log 2
  · have hcompact := hC (mem_image_of_mem
        (fun u : ℝ => ‖criticalMellinChebyshevResolventRayRepresentative u‖)
        (show t ∈ Icc (0 : ℝ) (Real.log 2) from ⟨ht, hhead⟩))
    have hrep := criticalMellinChebyshevResolventRayRepresentative_eq ht
    rw [Real.norm_eq_abs, hrep] at hcompact
    have hexp1 : 1 ≤ Real.exp (alpha * t) := by
      rw [Real.one_le_exp_iff]
      positivity
    have hCB : C ≤ B := (le_abs_self C).trans (le_max_left _ _)
    nlinarith
  · have htail : Real.log 2 ≤ t := le_of_not_ge hhead
    let X : ℝ := Real.exp t
    let N : ℕ := ⌊X⌋₊
    have hX2 : (2 : ℝ) ≤ X := by
      rw [show (2 : ℝ) = Real.exp (Real.log 2) by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]]
      exact Real.exp_le_exp.mpr htail
    have hX0 : 0 ≤ X := (Real.exp_pos t).le
    have hN : 2 ≤ N := Nat.le_floor hX2
    have hNX : (N : ℝ) ≤ X := Nat.floor_le hX0
    have hXN : X ≤ (N : ℝ) + 1 := (Nat.lt_floor_add_one X).le
    have hcell := abs_criticalMellinChebyshevResolventSource_log_le_nat_add hN hNX hXN
    have hlogX : Real.log X = t := by
      dsimp only [X]
      exact Real.log_exp t
    rw [hlogX] at hcell
    have hlogNle : Real.log (N : ℝ) ≤ t := by
      rw [← hlogX]
      exact Real.strictMonoOn_log.monotoneOn
        (show (N : ℝ) ∈ Ioi 0 by
          show 0 < (N : ℝ)
          exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN))
        (show X ∈ Ioi 0 by exact Real.exp_pos t) hNX
    have hexpN : Real.exp (alpha * Real.log N) ≤ Real.exp (alpha * t) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hlogNle halpha
    have hexp1 : 1 ≤ Real.exp (alpha * t) := by
      rw [Real.one_le_exp_iff]
      positivity
    have hsample := hlog N hN
    have htailBound :
        |criticalMellinChebyshevResolventSource t| ≤
          T * Real.exp (alpha * t) := by
      calc
        _ ≤ |criticalMellinChebyshevResolventSource (Real.log N)| +
            (Real.log 4 + 5) := hcell
        _ ≤ K * Real.exp (alpha * Real.log N) + (Real.log 4 + 5) := by linarith
        _ ≤ K * Real.exp (alpha * t) +
            (Real.log 4 + 5) * Real.exp (alpha * t) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hexpN hK0)
            (by
              have hC0 : 0 ≤ Real.log 4 + 5 := by positivity
              simpa only [mul_one] using
                mul_le_mul_of_nonneg_left hexp1 hC0)
        _ = T * Real.exp (alpha * t) := by
          dsimp only [T]
          ring
    exact htailBound.trans (mul_le_mul_of_nonneg_right
      (le_max_right |C| T) (Real.exp_pos _).le)

def SuzukiTransitionCoreFiniteContactResidualEventuallyBounded (m : ℕ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop, suzukiTransitionCoreFiniteContactResidual m N ≤ B

theorem suzukiTransitionCoreFiniteContactResidualEventuallyBounded_two_iff_quadratic :
    SuzukiTransitionCoreFiniteContactResidualEventuallyBounded 2 ↔
      SuzukiTransitionCoreQuadraticContactResidualEventuallyBounded := by
  unfold SuzukiTransitionCoreFiniteContactResidualEventuallyBounded
  unfold SuzukiTransitionCoreQuadraticContactResidualEventuallyBounded
  simp only [suzukiTransitionCoreFiniteContactResidual_two_eq_quadratic]

theorem xiZeroHalfPlaneBound_suzukiFiniteContactWidth_of_finiteContactResidualEventuallyBounded {m : ℕ} (hm : 1 ≤ m)
    (hcontact : SuzukiTransitionCoreFiniteContactResidualEventuallyBounded m) :
    XiZeroHalfPlaneBound (suzukiFiniteContactWidth m) := by
  obtain ⟨B, hB0, hbound⟩ := hcontact
  obtain ⟨K, hK0, hlog⟩ := exists_log_nat_bound_criticalMellinChebyshevResolventSource_finiteContactWidth hm hB0 hbound
  obtain ⟨BQ, hBQ0, hglobal⟩ :=
    exists_global_exponential_bound_criticalMellinChebyshevResolventSource_of_log_nat_exponentialBound (suzukiFiniteContactWidth_nonneg hm) hK0 hlog
  exact xiZeroHalfPlaneBound_of_criticalMellinChebyshevResolventSource_exponentialBound
    (suzukiFiniteContactWidth_nonneg hm) (suzukiFiniteContactWidth_lt_half hm) hBQ0 hglobal

theorem eventually_suzukiTransitionCoreFiniteContactResidual_one_eq_alignedEnergy :
    ∀ᶠ N : ℕ in atTop,
      suzukiTransitionCoreFiniteContactResidual 1 N = suzukiTransitionCoreAlignedGammaCompletedEnergy N := by
  filter_upwards [eventually_suzukiNaturalApertureTransitionCoreCauchyEnergy_ne_zero]
    with N hC
  rw [suzukiTransitionCoreFiniteContactResidual, dif_neg hC]
  norm_num

theorem suzukiTransitionCoreFiniteContactResidualEventuallyBounded_one_iff_alignedEnergy :
    SuzukiTransitionCoreFiniteContactResidualEventuallyBounded 1 ↔
      SuzukiTransitionCoreAlignedGammaCompletedEnergyEventuallyBounded := by
  unfold SuzukiTransitionCoreFiniteContactResidualEventuallyBounded
  unfold SuzukiTransitionCoreAlignedGammaCompletedEnergyEventuallyBounded
  constructor
  · rintro ⟨B, hB0, hB⟩
    refine ⟨B, ?_⟩
    filter_upwards [hB, eventually_suzukiTransitionCoreFiniteContactResidual_one_eq_alignedEnergy] with N hbound heq
    rwa [← heq]
  · rintro ⟨B, hB⟩
    refine ⟨max B 0, le_max_right _ _, ?_⟩
    filter_upwards [hB, eventually_suzukiTransitionCoreFiniteContactResidual_one_eq_alignedEnergy] with N hbound heq
    rw [heq]
    exact hbound.trans (le_max_left _ _)

theorem suzukiTransitionCore_finiteContact_widthClassification :
    (RiemannHypothesis ↔ SuzukiTransitionCoreFiniteContactResidualEventuallyBounded 1) ∧
    (∀ m : ℕ, 2 ≤ m → SuzukiTransitionCoreFiniteContactResidualEventuallyBounded m →
      XiZeroHalfPlaneBound (suzukiFiniteContactWidth m) ∧
        0 < suzukiFiniteContactWidth m ∧ suzukiFiniteContactWidth m < 1 / 2) := by
  constructor
  · exact riemannHypothesis_iff_suzukiTransitionCoreAlignedGammaCompletedEnergyEventuallyBounded.trans
      suzukiTransitionCoreFiniteContactResidualEventuallyBounded_one_iff_alignedEnergy.symm
  · intro m hm hcontact
    exact ⟨xiZeroHalfPlaneBound_suzukiFiniteContactWidth_of_finiteContactResidualEventuallyBounded (by omega) hcontact,
      suzukiFiniteContactWidth_pos hm, suzukiFiniteContactWidth_lt_half (by omega)⟩

end GaloisForLFunctions.RHTower
