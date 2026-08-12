import GaloisForLFunctions.RHTower.Sieve.RouteTMoebiusPowerSaving
import GaloisForLFunctions.RHTower.Sieve.MaynardEndpointZetaLogDeficit
import GaloisForLFunctions.RHTower.Sieve.MaynardMobiusAllShort

/-!
# Route-T cancellation for endpoint-long Möbius atoms

The contour displacement vanishes, but endpoint-long atoms still have logarithmic length
comparable to `log T`.  The spare tenth-power in the Route-T receiver therefore absorbs every
fixed contour constant and leaves a uniform (height-dependent) Maynard amplitude deficit.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Filter Topology

/-- The actual Route-T contour shift is antitone once the zero-free monotonicity range begins. -/
theorem routeTContourShift_antitone
    {A delta s t : ℝ} (hs : 8 * Real.pi ≤ s) (hst : s ≤ t) :
    routeTContourShift A delta t ≤ routeTContourShift A delta s := by
  have hD : routeTInverseDelta A t ≤ routeTInverseDelta A s := by
    unfold routeTInverseDelta routeTInverseHeight
    exact routeTZeroFreeDelta_antitone (by linarith) (by linarith)
  unfold routeTContourShift
  exact min_le_min (div_le_div_of_nonneg_right hD (by norm_num)) le_rfl

/-- Common Möbius deficit across the full endpoint ordinate interval. -/
def routeTEndpointMoebiusDeficit (A delta T : ℝ) : ℝ :=
  routeTContourShift A delta (3 * T) / 6

theorem routeTEndpointMoebiusDeficit_pos
    {A delta T : ℝ} (hdelta : 0 < delta) :
    0 < routeTEndpointMoebiusDeficit A delta T := by
  unfold routeTEndpointMoebiusDeficit
  exact div_pos (routeTContourShift_pos (A := A) (T := 3 * T) hdelta) (by norm_num)

theorem one_le_routeTContourEdgeLogEnvelope
    (A : ℝ) {S : ℝ} (hS : 0 ≤ S) :
    1 ≤ routeTContourEdgeLogEnvelope A S := by
  have hB : 2 ≤ routeTZeroFreeBudgetEnvelopeConstant A + 2 := by
    linarith [routeTZeroFreeBudgetEnvelopeConstant_pos A]
  have hBsq : 4 ≤ (routeTZeroFreeBudgetEnvelopeConstant A + 2) ^ (2 : ℕ) := by
    nlinarith
  have hZ : 1 ≤ routeTLogHeightEnvelope (4 * (S + 1)) :=
    routeTLogHeightEnvelope_one_le (by positivity)
  have hL : 1 ≤ 1 + Real.log (routeTLogHeightEnvelope (4 * (S + 1))) := by
    linarith [Real.log_nonneg hZ]
  have hLsq : 1 ≤
      (1 + Real.log (routeTLogHeightEnvelope (4 * (S + 1)))) ^ (2 : ℕ) := by
    nlinarith
  unfold routeTContourEdgeLogEnvelope
  calc
    (1 : ℝ) ≤ 400 * 4 * 1 := by norm_num
    _ ≤ 400 * (routeTZeroFreeBudgetEnvelopeConstant A + 2) ^ (2 : ℕ) *
        (1 + Real.log (routeTLogHeightEnvelope (4 * (S + 1)))) ^ (2 : ℕ) := by
      gcongr

/-- Logarithmic cost of the literal contour coefficient is one fixed multiple of the edge
envelope. -/
theorem log_routeTMoebiusPowerCoefficient_le
    {A C C' S : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C') (hS : 8 * Real.pi ≤ S) :
    Real.log (2 * routeTMoebiusPowerConstant C C' * routeTContourEdgeBound A S) ≤
      (1 + |Real.log (2 * routeTMoebiusPowerConstant C C')|) *
        routeTContourEdgeLogEnvelope A S := by
  let F : ℝ := 2 * routeTMoebiusPowerConstant C C'
  let M : ℝ := routeTContourEdgeBound A S
  let E : ℝ := routeTContourEdgeLogEnvelope A S
  have hF : 0 < F := by
    dsimp only [F]
    positivity [routeTMoebiusPowerConstant_pos hC hC']
  have hM : 0 < M := by
    dsimp only [M, routeTContourEdgeBound]
    positivity
  have hE : 1 ≤ E := by
    dsimp only [E]
    exact one_le_routeTContourEdgeLogEnvelope A (by linarith [Real.pi_pos])
  have hlogM : Real.log M ≤ E := by
    have hbound := routeTContourEdgeBound_logHeight_upper (A := A) hS
    have hlog := Real.log_le_log hM hbound
    simpa only [M, E, Real.log_exp] using hlog
  have habs : 0 ≤ |Real.log F| := abs_nonneg _
  have hmul : |Real.log F| ≤ |Real.log F| * E := by
    nlinarith [mul_nonneg habs (sub_nonneg.mpr hE)]
  calc
    Real.log (2 * routeTMoebiusPowerConstant C C' * routeTContourEdgeBound A S) =
        Real.log F + Real.log M := by
      dsimp only [F, M]
      rw [Real.log_mul hF.ne' hM.ne']
    _ ≤ |Real.log F| + E := add_le_add (le_abs_self _) hlogM
    _ ≤ E + |Real.log F| * E := by linarith
    _ = (1 + |Real.log F|) * E := by ring
    _ = (1 + |Real.log (2 * routeTMoebiusPowerConstant C C')|) *
        routeTContourEdgeLogEnvelope A S := by rfl

/-- Every literal Möbius coordinate has represented dyadic length at most its truncation cutoff. -/
theorem HeathBrownBoxChoice.moebius_factor_pow_le_cutoff
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k) (hL : 1 ≤ L)
    (j : HeathBrownBoxFactorIndex k box.m)
    (hkind : heathBrownBoxFactorKind k box.m j = .moebius) :
    2 ^ heathBrownBoxFactorExponent box.a box.b box.q j ≤ L := by
  rcases j with j | j
  · exact (Nat.pow_le_pow_right (by norm_num : 0 < 2)
      (dyadicChoice_le_log box.2.2.2.2 j)).trans
        (Nat.pow_log_le_self 2 (by omega))
  · rcases j with j | j <;> simp [heathBrownBoxFactorKind] at hkind

/-- Exponent-zero atoms contribute zero logarithmic mass, so positive-length trimming preserves
the exact box exponent. -/
theorem sum_positive_dyadicLogExponent_eq_heathBrownBoxTotalExponent
    {L X k : ℕ} {T : ℝ} (box : HeathBrownBoxChoice L X k) :
    (∑ i : PositiveHeathBrownBoxFactorIndex box,
      dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q i)) =
      heathBrownBoxTotalExponent L X k T box := by
  classical
  let q : HeathBrownBoxFactorIndex k box.m → ℕ :=
    heathBrownBoxFactorExponent box.a box.b box.q
  let u : Finset (HeathBrownBoxFactorIndex k box.m) :=
    Finset.univ.filter fun i => 1 ≤ q i
  have hu (i : HeathBrownBoxFactorIndex k box.m) : i ∈ u ↔ 1 ≤ q i := by
    simp [u]
  have hreindex := Finset.sum_subtype
    (F := Subtype.fintype fun i : HeathBrownBoxFactorIndex k box.m => 1 ≤ q i)
    u hu (fun i => dyadicLogExponent T (q i))
  calc
    (∑ i : PositiveHeathBrownBoxFactorIndex box,
        dyadicLogExponent T
          (heathBrownBoxFactorExponent box.a box.b box.q i)) =
        ∑ i ∈ u, dyadicLogExponent T (q i) := by
      simpa [PositiveHeathBrownBoxFactorIndex, q] using hreindex.symm
    _ = ∑ i : HeathBrownBoxFactorIndex k box.m, dyadicLogExponent T (q i) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _hi hiu
      have hqi : q i = 0 := by
        have : ¬ 1 ≤ q i := by simpa [u] using hiu
        omega
      simp [hqi, dyadicLogExponent]
    _ = heathBrownBoxTotalExponent L X k T box := by
      rfl

/-- The canonical cutoff is so short that every fourth power of a dyadic Möbius length fits below
half the endpoint height.  The coarse exponent `1/8` deliberately avoids any fragile decimal
arithmetic: `mu/60 <= 19/540 < 1/8`. -/
theorem fourth_power_le_half_height_of_maynard_cutoff
    {T mu N : ℝ} (hT : 4 ≤ T) (hmu : mu ≤ 19 / 9)
    (hN : 0 ≤ N) (hcut : N ≤ T ^ (mu / 60)) :
    N ^ (4 : ℕ) ≤ T / 2 := by
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hexp : mu / 60 ≤ 1 / 8 := by linarith
  have hroot : N ≤ T ^ (1 / 8 : ℝ) :=
    hcut.trans (Real.rpow_le_rpow_of_exponent_le hT1 hexp)
  have hpow : N ^ (4 : ℕ) ≤ (T ^ (1 / 8 : ℝ)) ^ (4 : ℕ) :=
    pow_le_pow_left₀ hN hroot 4
  have hcollapse : (T ^ (1 / 8 : ℝ)) ^ (4 : ℕ) = T ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
    norm_num
  rw [hcollapse] at hpow
  have hroot2 : 2 ≤ Real.sqrt T := Real.le_sqrt_of_sq_le (by nlinarith)
  have hsqrtSq : (Real.sqrt T) ^ (2 : ℕ) = T := Real.sq_sqrt hT0.le
  have hsqrtHalf : Real.sqrt T ≤ T / 2 := by nlinarith
  rw [← Real.sqrt_eq_rpow] at hpow
  exact hpow.trans hsqrtHalf

/-- Pointwise Route-T saving becomes a common endpoint amplitude deficit after coefficient
absorption. -/
theorem maynard_moebius_amplitude_le_routeTEndpointDeficit
    {A C C' delta T S : ℝ} {L q : ℕ} {c y U : ℝ}
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hdelta : 0 < delta)
    (hq : 1 ≤ q) (hNL : 2 ^ q ≤ L) (hc : 0 ≤ c)
    (hU : (((2 ^ q : ℕ) : ℝ)) ^ (4 : ℕ) ≤ U)
    (hsep : routeTInverseBaseHeight + U ≤ |y|)
    (hS : S = |y| + U)
    (hsize : 2 * Real.log
        (2 * routeTMoebiusPowerConstant C C' * routeTContourEdgeBound A S) ≤
      (routeTContourShift A delta S / 3) *
        Real.log (((2 ^ q : ℕ) : ℝ)))
    (hcommon : routeTContourShift A delta (3 * T) ≤
      routeTContourShift A delta S)
    (hV : 0 < ‖LSeries
      (complexCoeff (arithmeticDyadicBlock (truncatedMoebius L) q))
        ((c : ℂ) + (y : ℝ) * Complex.I)‖)
    (hmain : ‖LSeries
      (complexCoeff (arithmeticDyadicBlock (truncatedMoebius L) q))
        ((c : ℂ) + (y : ℝ) * Complex.I)‖ ≤
      2 * routeTMoebiusPowerConstant C C' *
        routeTContourEdgeBound A (|y| + U) *
        (((2 ^ q : ℕ) : ℝ)) ^
          (1 - c - routeTContourShift A delta (|y| + U) / 3)) :
    maynardAmplitude c (((2 ^ q : ℕ) : ℝ))
        ‖LSeries (complexCoeff
          (arithmeticDyadicBlock (truncatedMoebius L) q))
            ((c : ℂ) + (y : ℝ) * Complex.I)‖ ≤
      1 - routeTEndpointMoebiusDeficit A delta T := by
  let N : ℝ := (((2 ^ q : ℕ) : ℝ))
  let shift : ℝ := routeTContourShift A delta S
  let coeff : ℝ :=
    2 * routeTMoebiusPowerConstant C C' * routeTContourEdgeBound A S
  have hN : 1 < N := by
    dsimp only [N]
    exact_mod_cast (show 1 < 2 ^ q by
      exact pow_lt_pow_right₀ (by norm_num) hq)
  have hN0 : 0 < N := lt_trans zero_lt_one hN
  have hP : 1000 ≤ routeTMoebiusPowerConstant C C' := by
    unfold routeTMoebiusPowerConstant
    linarith
  have hM : 1 ≤ routeTContourEdgeBound A S := by
    unfold routeTContourEdgeBound
    exact Real.one_le_exp (by positivity)
  have hcoeff : 1 ≤ coeff := by
    dsimp only [coeff]
    calc
      (1 : ℝ) ≤ 2 * 1000 * 1 := by norm_num
      _ ≤ 2 * routeTMoebiusPowerConstant C C' * routeTContourEdgeBound A S := by
        gcongr
  have hpow : N ^ (1 - c - shift / 3) =
      N ^ (1 - c) * N ^ (-(shift / 3)) := by
    rw [← Real.rpow_add hN0]
    ring
  have hupper :
      ‖LSeries (complexCoeff (arithmeticDyadicBlock (truncatedMoebius L) q))
          ((c : ℂ) + (y : ℝ) * Complex.I)‖ ≤
        coeff * N ^ (1 - c) * N ^ (-(shift / 3)) := by
    calc
      ‖LSeries (complexCoeff (arithmeticDyadicBlock (truncatedMoebius L) q))
          ((c : ℂ) + (y : ℝ) * Complex.I)‖ ≤
          coeff * N ^ (1 - c - shift / 3) := by
        simpa only [coeff, N, shift, hS] using hmain
      _ = coeff * N ^ (1 - c) * N ^ (-(shift / 3)) := by rw [hpow]; ring
  have hamp := maynardAmplitude_le_one_sub_half_of_pointwise_power_saving
    (c := c) (N := N) (C := coeff) (Delta := shift / 3)
      hN hV hcoeff (by simpa only [coeff, N, shift] using hsize) hupper
  have hdef : routeTEndpointMoebiusDeficit A delta T ≤ shift / 6 := by
    dsimp only [routeTEndpointMoebiusDeficit, shift]
    linarith
  dsimp only [N] at hamp ⊢
  linarith

/-- Uniform endpoint absorption of the complete Route-T contour coefficient.  This is the exact
place where the spare receiver tenth-power is spent. -/
theorem eventually_routeT_endpoint_moebius_coefficient_ready
    (A C C' delta : ℝ) (hC : 0 ≤ C) (hC' : 0 ≤ C') (hdelta : 0 < delta) :
    ∀ᶠ T : ℝ in atTop,
      ∀ y : ℝ, T ≤ y → y ≤ 2 * T →
        let U := |y| / 2
        let S := |y| + U
        2 * Real.log
            (2 * routeTMoebiusPowerConstant C C' * routeTContourEdgeBound A S) ≤
          (routeTContourShift A delta S / 3) * (Real.log T / 216000) ∧
        routeTContourShift A delta (3 * T) ≤ routeTContourShift A delta S ∧
        routeTInverseBaseHeight + U ≤ |y| := by
  let D : ℝ := 1 + |Real.log (2 * routeTMoebiusPowerConstant C C')|
  let K : ℝ := 12 * 216000 * D
  have hD : 1 ≤ D := by
    dsimp only [D]
    linarith [abs_nonneg (Real.log (2 * routeTMoebiusPowerConstant C C'))]
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  obtain ⟨a, ha⟩ := eventually_atTop.1
    (eventually_const_mul_routeTContourEdgeLogEnvelope_le_shiftGain A K hK)
  obtain ⟨b, hb⟩ := eventually_atTop.1
    (eventually_routeTContourShiftEnvelope_le (A := A) hdelta)
  filter_upwards [eventually_ge_atTop a, eventually_ge_atTop b,
    eventually_ge_atTop (8 * Real.pi), eventually_ge_atTop 3,
    eventually_ge_atTop (2 * routeTInverseBaseHeight)]
      with T hTa hTb hTpi hT3 hTbase
  intro y hylo hyhi
  let U : ℝ := |y| / 2
  let S : ℝ := |y| + U
  have hT0 : 0 < T := by linarith [Real.pi_pos]
  have hy0 : 0 < y := hT0.trans_le hylo
  have habsy : |y| = y := abs_of_pos hy0
  have hU : U = y / 2 := by simp only [U, habsy]
  have hS : S = 3 * y / 2 := by
    dsimp only [S]
    rw [hU, habsy]
    ring
  have hTS : T ≤ S := by rw [hS]; linarith
  have hS3T : S ≤ 3 * T := by rw [hS]; linarith
  have hS0 : 0 < S := hT0.trans_le hTS
  have hS8 : 8 * Real.pi ≤ S := hTpi.trans hTS
  have hcost := ha S (hTa.trans hTS)
  have henv := hb S (hTb.trans hTS)
  have hcommon : routeTContourShift A delta (3 * T) ≤
      routeTContourShift A delta S :=
    routeTContourShift_antitone hS8 hS3T
  have hsep : routeTInverseBaseHeight + U ≤ |y| := by
    rw [hU, habsy]
    linarith
  have hSTsq : S ≤ T ^ (2 : ℕ) := by
    have h3T : 3 * T ≤ T ^ (2 : ℕ) := by nlinarith
    exact hS3T.trans h3T
  have hlogS : Real.log S ≤ 2 * Real.log T := by
    have hlog := Real.log_le_log hS0 hSTsq
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    exact hlog
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hE0 : 0 ≤ routeTContourEdgeLogEnvelope A S :=
    (one_le_routeTContourEdgeLogEnvelope A hS0.le).trans' zero_le_one
  have henv0 : 0 ≤ routeTContourShiftEnvelope A S :=
    (routeTContourShiftEnvelope_pos A hS0.le).le
  have hshift0 : 0 ≤ routeTContourShift A delta S :=
    (routeTContourShift_pos hdelta).le
  have hlogCoeff := log_routeTMoebiusPowerCoefficient_le (A := A) hC hC' hS8
  have hcostScaled :
      2 * D * routeTContourEdgeLogEnvelope A S ≤
        routeTContourShiftEnvelope A S * Real.log S / (6 * 216000) := by
    dsimp only [K] at hcost
    nlinarith
  have hlogCost :
      2 * Real.log
          (2 * routeTMoebiusPowerConstant C C' * routeTContourEdgeBound A S) ≤
        2 * D * routeTContourEdgeLogEnvelope A S := by
    dsimp only [D]
    linarith
  have hlogTransfer :
      routeTContourShiftEnvelope A S * Real.log S ≤
        2 * routeTContourShift A delta S * Real.log T := by
    calc
      routeTContourShiftEnvelope A S * Real.log S ≤
          routeTContourShiftEnvelope A S * (2 * Real.log T) :=
        mul_le_mul_of_nonneg_left hlogS henv0
      _ ≤ routeTContourShift A delta S * (2 * Real.log T) :=
        mul_le_mul_of_nonneg_right henv (by positivity)
      _ = 2 * routeTContourShift A delta S * Real.log T := by ring
  have hready :
      2 * Real.log
          (2 * routeTMoebiusPowerConstant C C' * routeTContourEdgeBound A S) ≤
        (routeTContourShift A delta S / 3) * (Real.log T / 216000) := by
    calc
      2 * Real.log
          (2 * routeTMoebiusPowerConstant C C' * routeTContourEdgeBound A S) ≤
          2 * D * routeTContourEdgeLogEnvelope A S := hlogCost
      _ ≤ routeTContourShiftEnvelope A S * Real.log S / (6 * 216000) :=
        hcostScaled
      _ ≤ (2 * routeTContourShift A delta S * Real.log T) / (6 * 216000) :=
        div_le_div_of_nonneg_right hlogTransfer (by norm_num)
      _ = (routeTContourShift A delta S / 3) * (Real.log T / 216000) := by
        ring
  simpa only [U, S] using (And.intro hready (And.intro hcommon hsep))

end RHTower.Sieve
