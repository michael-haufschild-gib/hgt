import GaloisForLFunctions.RHTower.XiMassCriticalDiscreteRemainderCells

/-!
# Finite centered-atom cone criterion for the critical Xi mass current

The finite mass cone can be rounded up to its next logarithmic arithmetic cell at uniformly
bounded cost.  Exact cell atomization then identifies the remaining source problem with a canonical
finite sum of centered von Mangoldt atoms.  Both the rounding overflow and terminal remainder are
bounded unconditionally, so uniform boundedness of this finite atom sum is equivalent to the cone
current criterion, hence to RH.

Every integral below is a genuine Bochner integral.  No finite computation or remainder hypothesis
is used.
-/

open Complex Filter MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- Absolute version of the superluminal tail estimate.  This supports arbitrary measurable
subintervals of the tail, not only the signed tail current. -/
theorem integral_norm_xiMassCriticalDiscreteRemainder_superluminalTail_le
    {a sigma d u : ℝ}
    (hdhalf : 1 / 2 < d) (hda : d < a) (hsigma : 0 < sigma) (hu : 0 ≤ u) :
    (∫ h in Ioi (d * u / (d - 1 / 2)),
      ‖xiMassCriticalDiscreteRemainderDensity a sigma u h‖) ≤
      8 * xiMassCriticalOutgoingDeepShiftBound sigma d / (d - 1 / 2) := by
  let H : ℝ := d * u / (d - 1 / 2)
  let J : ℝ := xiMassCriticalOutgoingDeepShiftBound sigma d
  let b : ℝ := 1 / 2 - d
  have hden : 0 < d - 1 / 2 := by linarith
  have hb : b < 0 := by dsimp [b]; linarith
  have hJ : 0 ≤ J := xiMassCriticalOutgoingDeepShiftBound_nonneg (by linarith)
  have hleft : IntegrableOn
      (fun h => ‖xiMassCriticalDiscreteRemainderDensity a sigma u h‖) (Ioi H) := by
    have hfull := integrableOn_xiMassCriticalDiscreteRemainderDensity
      (a := a) (sigma := sigma) (lt_trans hdhalf hda) hsigma u
    have hH : 0 ≤ H := by dsimp [H]; positivity
    exact (hfull.mono_set (Ioi_subset_Ioi hH)).norm
  have hright : IntegrableOn
      (fun h : ℝ => (8 * J * Real.exp (d * u)) * Real.exp (b * h)) (Ioi H) :=
    (integrableOn_exp_mul_Ioi hb H).const_mul _
  have hmono :
      (∫ h in Ioi H, ‖xiMassCriticalDiscreteRemainderDensity a sigma u h‖) ≤
        ∫ h in Ioi H, (8 * J * Real.exp (d * u)) * Real.exp (b * h) := by
    apply integral_mono_ae hleft hright
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    have hdensity := norm_xiMassCriticalDiscreteRemainderDensity_le_deepShift
      hdhalf hda hsigma hu (h := h)
    calc
      ‖xiMassCriticalDiscreteRemainderDensity a sigma u h‖ ≤
          8 * J * Real.exp (d * u + b * h) := by
        simpa only [J, b] using hdensity
      _ = (8 * J * Real.exp (d * u)) * Real.exp (b * h) := by
        rw [Real.exp_add]
        ring_nf
  calc
    (∫ h in Ioi (d * u / (d - 1 / 2)),
        ‖xiMassCriticalDiscreteRemainderDensity a sigma u h‖) =
      ∫ h in Ioi H, ‖xiMassCriticalDiscreteRemainderDensity a sigma u h‖ := by rfl
    _ ≤ ∫ h in Ioi H, (8 * J * Real.exp (d * u)) * Real.exp (b * h) := hmono
    _ = (8 * J * Real.exp (d * u)) * (-Real.exp (b * H) / b) := by
      rw [integral_const_mul, integral_exp_mul_Ioi hb H]
    _ = 8 * xiMassCriticalOutgoingDeepShiftBound sigma d / (d - 1 / 2) := by
      have hdenne : d - 1 / 2 ≠ 0 := by linarith
      have hbident : b = -(d - 1 / 2) := by dsimp [b]; ring_nf
      have hexp : d * u + b * H = 0 := by
        rw [hbident]
        dsimp [H]
        calc
          d * u + -(d - 1 / 2) * (d * u / (d - 1 / 2)) =
              d * u - (d * u / (d - 1 / 2)) * (d - 1 / 2) := by ring_nf
          _ = d * u - d * u := by rw [div_mul_cancel₀ _ hdenne]
          _ = 0 := sub_self _
      have hexpprod : Real.exp (d * u) * Real.exp (b * H) = 1 := by
        rw [← Real.exp_add, hexp, Real.exp_zero]
      rw [show (8 * J * Real.exp (d * u)) * (-Real.exp (b * H) / b) =
        8 * J * (-(Real.exp (d * u) * Real.exp (b * H)) / b) by ring_nf,
        hexpprod, hbident]
      field_simp [hdenne]
      rfl

/-- The terminal Abel-summation remainder at the cell just beyond the mass cone is uniformly
bounded.  Exponential Fourier decay cancels the unconditional linear remainder estimate. -/
theorem norm_xiMassCriticalDiscreteRemainder_terminalFlux_le
    {a sigma d u : ℝ}
    (hdhalf : 1 / 2 < d) (hda : d < a) (hsigma : 0 < sigma) (hu : 0 ≤ u) :
    let H := d * u / (d - 1 / 2)
    let M := ⌊Real.exp H⌋₊
    ‖(psiRemainder M : ℂ) *
      xiMassCriticalDampedFourierProfile a sigma u (Real.log ((M : ℝ) + 1))‖ ≤
      8 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) := by
  dsimp only
  let H : ℝ := d * u / (d - 1 / 2)
  let M : ℕ := ⌊Real.exp H⌋₊
  let w : ℝ := Real.log ((M : ℝ) + 1)
  let J : ℝ := ∫ x : ℝ, Real.exp (-(sigma * |x|))
  change ‖(psiRemainder M : ℂ) *
      xiMassCriticalDampedFourierProfile a sigma u w‖ ≤ 8 * J
  have hden : 0 < d - 1 / 2 := by linarith
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hMone : 1 ≤ M := by
    apply Nat.le_floor
    simpa only [Nat.cast_one, ← Real.exp_zero] using Real.exp_le_exp.mpr hH
  have hMle : (M : ℝ) ≤ Real.exp H := Nat.floor_le (Real.exp_pos H).le
  have hupper : Real.exp H < (M : ℝ) + 1 := Nat.lt_floor_add_one _
  have hwgt : H < w := by
    have hlog := Real.log_lt_log (Real.exp_pos H) hupper
    simpa only [Real.log_exp, w] using hlog
  have hR := abs_psiRemainder_le M
  have hF := norm_stripFourier_xiMass_deepShift_le
    (a := a) (σ := sigma) (d := d) (by linarith) hda hsigma u w
  rw [abs_of_nonneg hu] at hF
  have hwpos : 0 < (M : ℝ) + 1 := by positivity
  have hexpw : Real.exp w = (M : ℝ) + 1 := by
    dsimp [w]
    rw [Real.exp_log hwpos]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    xiMassCriticalDampedFourierProfile, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    |psiRemainder M| *
        (Real.exp (-w / 2) *
          ‖stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + ↑u * I)) ↑w‖) ≤
      (8 * (M : ℝ)) *
        (Real.exp (-w / 2) * (Real.exp (u * d - w * d) * J)) :=
      mul_le_mul hR
        (mul_le_mul_of_nonneg_left (by simpa only [J] using hF) (Real.exp_nonneg _))
        (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _)) (by positivity)
    _ ≤ (8 * Real.exp H) *
        (Real.exp (-w / 2) * (Real.exp (u * d - w * d) * J)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hMle (by norm_num)) (by positivity)
    _ = 8 * J * Real.exp (d * u + H - (d + 1 / 2) * w) := by
      rw [show (8 * Real.exp H) *
          (Real.exp (-w / 2) * (Real.exp (u * d - w * d) * J)) =
        8 * J * (Real.exp H *
          (Real.exp (-w / 2) * Real.exp (u * d - w * d))) by ring_nf,
        ← Real.exp_add, ← Real.exp_add]
      ring_nf
    _ ≤ 8 * J * Real.exp (d * u + (1 / 2 - d) * H) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      have hdpos : 0 < d + 1 / 2 := by linarith
      nlinarith
    _ = 8 * J := by
      have hcancel : d * u + (1 / 2 - d) * H = 0 := by
        have hdenne : d - 1 / 2 ≠ 0 := by linarith
        have hb : 1 / 2 - d = -(d - 1 / 2) := by ring_nf
        rw [hb]
        dsimp [H]
        calc
          d * u + -(d - 1 / 2) * (d * u / (d - 1 / 2)) =
              d * u - (d * u / (d - 1 / 2)) * (d - 1 / 2) := by ring_nf
          _ = d * u - d * u := by rw [div_mul_cancel₀ _ hdenne]
          _ = 0 := sub_self _
      rw [hcancel, Real.exp_zero, mul_one]
    _ = 8 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) := by rfl

/-- Short interval between the geometric cone edge and the next logarithmic arithmetic cell. -/
noncomputable def xiMassCriticalDiscreteRemainderConeOverflow
    (a sigma d u : ℝ) : ℂ :=
  let H := d * u / (d - 1 / 2)
  let M := ⌊Real.exp H⌋₊
  ∫ h in H..Real.log ((M : ℝ) + 1),
    xiMassCriticalDiscreteRemainderDensity a sigma u h

/-- Rounding a mass cone up to its next complete arithmetic cell has uniformly bounded cost. -/
theorem norm_xiMassCriticalDiscreteRemainderConeOverflow_le
    {a sigma d u : ℝ}
    (hdhalf : 1 / 2 < d) (hda : d < a) (hsigma : 0 < sigma) (hu : 0 ≤ u) :
    ‖xiMassCriticalDiscreteRemainderConeOverflow a sigma d u‖ ≤
      8 * xiMassCriticalOutgoingDeepShiftBound sigma d / (d - 1 / 2) := by
  let H : ℝ := d * u / (d - 1 / 2)
  let M : ℕ := ⌊Real.exp H⌋₊
  let w : ℝ := Real.log ((M : ℝ) + 1)
  have hden : 0 < d - 1 / 2 := by linarith
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hupper : Real.exp H < (M : ℝ) + 1 := Nat.lt_floor_add_one _
  have hHw : H ≤ w := by
    have hlog := Real.log_lt_log (Real.exp_pos H) hupper
    have hlt : H < w := by
      simpa only [Real.log_exp, w] using hlog
    exact hlt.le
  have htailInt : IntegrableOn
      (fun h => ‖xiMassCriticalDiscreteRemainderDensity a sigma u h‖) (Ioi H) := by
    have hfull := integrableOn_xiMassCriticalDiscreteRemainderDensity
      (a := a) (sigma := sigma) (lt_trans hdhalf hda) hsigma u
    exact (hfull.mono_set (Ioi_subset_Ioi hH)).norm
  have hmono :
      (∫ h in Ioc H w, ‖xiMassCriticalDiscreteRemainderDensity a sigma u h‖) ≤
        ∫ h in Ioi H, ‖xiMassCriticalDiscreteRemainderDensity a sigma u h‖ := by
    apply setIntegral_mono_set htailInt
    · exact Filter.Eventually.of_forall fun h => norm_nonneg _
    · exact Filter.Eventually.of_forall fun h hh => hh.1
  rw [xiMassCriticalDiscreteRemainderConeOverflow]
  change ‖∫ h in H..w, xiMassCriticalDiscreteRemainderDensity a sigma u h‖ ≤ _
  calc
    ‖∫ h in H..w, xiMassCriticalDiscreteRemainderDensity a sigma u h‖ ≤
        ∫ h in H..w, ‖xiMassCriticalDiscreteRemainderDensity a sigma u h‖ :=
      intervalIntegral.norm_integral_le_integral_norm hHw
    _ = ∫ h in Ioc H w, ‖xiMassCriticalDiscreteRemainderDensity a sigma u h‖ := by
      rw [intervalIntegral.integral_of_le hHw]
    _ ≤ ∫ h in Ioi H, ‖xiMassCriticalDiscreteRemainderDensity a sigma u h‖ := hmono
    _ ≤ 8 * xiMassCriticalOutgoingDeepShiftBound sigma d / (d - 1 / 2) := by
      simpa only [H] using
        integral_norm_xiMassCriticalDiscreteRemainder_superluminalTail_le
          hdhalf hda hsigma hu

/-- Canonical finite centered von Mangoldt atom sum inside the rounded critical mass cone. -/
noncomputable def xiMassCriticalCenteredAtomConeSum (a sigma d u : ℝ) : ℂ :=
  let H := d * u / (d - 1 / 2)
  let M := ⌊Real.exp H⌋₊
  ∑ k ∈ Finset.range (M - 1),
    ((ArithmeticFunction.vonMangoldt (k + 2) - 1 : ℝ) : ℂ) *
      xiMassCriticalDampedFourierProfile a sigma u (Real.log ((k : ℝ) + 2))

/-- Exact finite-cell identity at the mass-cone edge.  Overflow completes the last arithmetic cell;
finite Abel summation leaves the centered atom sum and one explicit terminal remainder. -/
theorem xiMassCriticalDiscreteRemainderConeFlux_add_overflow_eq_centeredAtomConeSum
    {a sigma d u : ℝ}
    (hdhalf : 1 / 2 < d) (hda : d < a) (hsigma : 0 < sigma) (hu : 0 ≤ u) :
    let H := d * u / (d - 1 / 2)
    let M := ⌊Real.exp H⌋₊
    xiMassCriticalDiscreteRemainderConeFlux a sigma d u +
        xiMassCriticalDiscreteRemainderConeOverflow a sigma d u =
      -xiMassCriticalDampedFourierProfile a sigma u 0 +
        xiMassCriticalCenteredAtomConeSum a sigma d u -
        (psiRemainder M : ℂ) *
          xiMassCriticalDampedFourierProfile a sigma u (Real.log ((M : ℝ) + 1)) := by
  dsimp only
  let H : ℝ := d * u / (d - 1 / 2)
  let M : ℕ := ⌊Real.exp H⌋₊
  let w : ℝ := Real.log ((M : ℝ) + 1)
  have hden : 0 < d - 1 / 2 := by linarith
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hMone : 1 ≤ M := by
    apply Nat.le_floor
    simpa only [Nat.cast_one, ← Real.exp_zero] using Real.exp_le_exp.mpr hH
  have hupper : Real.exp H < (M : ℝ) + 1 := Nat.lt_floor_add_one _
  have hHw : H ≤ w := by
    have hlog := Real.log_lt_log (Real.exp_pos H) hupper
    have hlt : H < w := by
      simpa only [Real.log_exp, w] using hlog
    exact hlt.le
  have hfull := integrableOn_xiMassCriticalDiscreteRemainderDensity
    (a := a) (sigma := sigma) (lt_trans hdhalf hda) hsigma u
  have h0H : IntervalIntegrable
      (xiMassCriticalDiscreteRemainderDensity a sigma u) volume 0 H := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hH]
    exact hfull.mono_set (fun _ hh => hh.1)
  have hHwInt : IntervalIntegrable
      (xiMassCriticalDiscreteRemainderDensity a sigma u) volume H w := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hHw]
    exact hfull.mono_set (fun h hh => hH.trans_lt hh.1)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals h0H hHwInt
  have hprefix := integral_xiMassCriticalDiscreteRemainderDensity_eq_centeredAtoms
    (a := a) (sigma := sigma) (u := u) (M - 1) (lt_trans hdhalf hda) hsigma
  have hMsub : M - 1 + 1 = M := by omega
  have hcast : (((M - 1 : ℕ) : ℝ) + 2) = (M : ℝ) + 1 := by
    rw [Nat.cast_sub hMone]
    push_cast
    ring_nf
  rw [hcast, hMsub] at hprefix
  rw [xiMassCriticalDiscreteRemainderConeFlux,
    xiMassCriticalDiscreteRemainderConeOverflow,
    xiMassCriticalCenteredAtomConeSum]
  change (∫ h in Ioc (0 : ℝ) H,
      xiMassCriticalDiscreteRemainderDensity a sigma u h) +
      (∫ h in H..w, xiMassCriticalDiscreteRemainderDensity a sigma u h) = _
  rw [← intervalIntegral.integral_of_le hH] at ⊢
  rw [hsplit, hprefix]

/-- Uniform line bound for the canonical finite centered-atom cone sums. -/
def XiMassCriticalCenteredAtomConeLineBound (a sigma d : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
    ‖xiMassCriticalCenteredAtomConeSum a sigma d u‖ ≤ C

/-- Uniform bound for the fixed left endpoint of the finite Abel identity. -/
theorem norm_xiMassCriticalDampedFourierProfile_zero_le
    {a sigma u : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) :
    ‖xiMassCriticalDampedFourierProfile a sigma u 0‖ ≤
      ∫ x : ℝ, Real.exp (-(sigma * |x|)) := by
  rw [xiMassCriticalDampedFourierProfile]
  norm_num
  exact norm_stripFourier_xiMassAnalyticTest_vertical_le ha hsigma u 0

/-- The integral finite-cone condition and the finite centered-atom condition differ only by three
uniformly bounded explicit terms: left endpoint, rounding overflow, and terminal remainder. -/
theorem xiMassCriticalDiscreteRemainderConeFluxLineBound_iff_centeredAtomCone
    {a sigma d : ℝ} (hdhalf : 1 / 2 < d) (hda : d < a) (hsigma : 0 < sigma) :
    XiMassCriticalDiscreteRemainderConeFluxLineBound a sigma d ↔
      XiMassCriticalCenteredAtomConeLineBound a sigma d := by
  let J : ℝ := ∫ x : ℝ, Real.exp (-(sigma * |x|))
  let BO : ℝ := 8 * xiMassCriticalOutgoingDeepShiftBound sigma d / (d - 1 / 2)
  let BT : ℝ := 8 * J
  have ha : 0 < a := lt_trans (by norm_num) (lt_trans hdhalf hda)
  have hO : ∀ u : ℝ, 0 ≤ u →
      ‖xiMassCriticalDiscreteRemainderConeOverflow a sigma d u‖ ≤ BO :=
    fun u hu => by
      simpa only [BO] using
        norm_xiMassCriticalDiscreteRemainderConeOverflow_le hdhalf hda hsigma hu
  have hK : ∀ u : ℝ, ‖xiMassCriticalDampedFourierProfile a sigma u 0‖ ≤ J :=
    fun u => by
      simpa only [J] using
        norm_xiMassCriticalDampedFourierProfile_zero_le ha hsigma (u := u)
  have hT : ∀ u : ℝ, 0 ≤ u →
      let H := d * u / (d - 1 / 2)
      let M := ⌊Real.exp H⌋₊
      ‖(psiRemainder M : ℂ) *
        xiMassCriticalDampedFourierProfile a sigma u (Real.log ((M : ℝ) + 1))‖ ≤ BT :=
    fun u hu => by
      simpa only [BT, J] using
        norm_xiMassCriticalDiscreteRemainder_terminalFlux_le hdhalf hda hsigma hu
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + BO + J + BT, fun u hu => ?_⟩
    let H : ℝ := d * u / (d - 1 / 2)
    let M : ℕ := ⌊Real.exp H⌋₊
    let K : ℂ := xiMassCriticalDampedFourierProfile a sigma u 0
    let T : ℂ := (psiRemainder M : ℂ) *
      xiMassCriticalDampedFourierProfile a sigma u (Real.log ((M : ℝ) + 1))
    have hrel :=
      xiMassCriticalDiscreteRemainderConeFlux_add_overflow_eq_centeredAtomConeSum
        hdhalf hda hsigma hu
    dsimp only at hrel
    have hA : xiMassCriticalCenteredAtomConeSum a sigma d u =
        xiMassCriticalDiscreteRemainderConeFlux a sigma d u +
          xiMassCriticalDiscreteRemainderConeOverflow a sigma d u + K + T := by
      dsimp only [K, T, H, M]
      linear_combination -hrel
    rw [hA]
    calc
      ‖xiMassCriticalDiscreteRemainderConeFlux a sigma d u +
          xiMassCriticalDiscreteRemainderConeOverflow a sigma d u + K + T‖ ≤
          (‖xiMassCriticalDiscreteRemainderConeFlux a sigma d u‖ +
            ‖xiMassCriticalDiscreteRemainderConeOverflow a sigma d u‖ + ‖K‖) +
            ‖T‖ := by
        calc
          _ ≤ ‖xiMassCriticalDiscreteRemainderConeFlux a sigma d u +
                xiMassCriticalDiscreteRemainderConeOverflow a sigma d u + K‖ +
              ‖T‖ := norm_add_le _ _
          _ ≤ (‖xiMassCriticalDiscreteRemainderConeFlux a sigma d u +
                xiMassCriticalDiscreteRemainderConeOverflow a sigma d u‖ + ‖K‖) +
              ‖T‖ := by
            gcongr
            exact norm_add_le _ _
          _ ≤ (‖xiMassCriticalDiscreteRemainderConeFlux a sigma d u‖ +
                ‖xiMassCriticalDiscreteRemainderConeOverflow a sigma d u‖ + ‖K‖) +
              ‖T‖ := by
            gcongr
            exact norm_add_le _ _
      _ ≤ (C + BO + J) + BT := by
        exact add_le_add
          (add_le_add (add_le_add (hC u hu) (hO u hu)) (hK u))
          (by simpa only [T, H, M] using hT u hu)
      _ = C + BO + J + BT := rfl
  · rintro ⟨C, hC⟩
    refine ⟨J + C + BT + BO, fun u hu => ?_⟩
    let H : ℝ := d * u / (d - 1 / 2)
    let M : ℕ := ⌊Real.exp H⌋₊
    let K : ℂ := xiMassCriticalDampedFourierProfile a sigma u 0
    let T : ℂ := (psiRemainder M : ℂ) *
      xiMassCriticalDampedFourierProfile a sigma u (Real.log ((M : ℝ) + 1))
    have hrel :=
      xiMassCriticalDiscreteRemainderConeFlux_add_overflow_eq_centeredAtomConeSum
        hdhalf hda hsigma hu
    dsimp only at hrel
    have hcone : xiMassCriticalDiscreteRemainderConeFlux a sigma d u =
        -K + xiMassCriticalCenteredAtomConeSum a sigma d u - T -
          xiMassCriticalDiscreteRemainderConeOverflow a sigma d u := by
      dsimp only [K, T, H, M]
      linear_combination hrel
    rw [hcone]
    calc
      ‖-K + xiMassCriticalCenteredAtomConeSum a sigma d u - T -
          xiMassCriticalDiscreteRemainderConeOverflow a sigma d u‖ ≤
          (‖K‖ + ‖xiMassCriticalCenteredAtomConeSum a sigma d u‖ + ‖T‖) +
            ‖xiMassCriticalDiscreteRemainderConeOverflow a sigma d u‖ := by
        calc
          _ ≤ ‖-K + xiMassCriticalCenteredAtomConeSum a sigma d u - T‖ +
              ‖xiMassCriticalDiscreteRemainderConeOverflow a sigma d u‖ :=
            norm_sub_le _ _
          _ ≤ (‖-K + xiMassCriticalCenteredAtomConeSum a sigma d u‖ + ‖T‖) +
              ‖xiMassCriticalDiscreteRemainderConeOverflow a sigma d u‖ := by
            gcongr
            exact norm_sub_le _ _
          _ ≤ (‖K‖ + ‖xiMassCriticalCenteredAtomConeSum a sigma d u‖ + ‖T‖) +
              ‖xiMassCriticalDiscreteRemainderConeOverflow a sigma d u‖ := by
            gcongr
            simpa only [norm_neg] using
              norm_add_le (-K) (xiMassCriticalCenteredAtomConeSum a sigma d u)
      _ ≤ (J + C + BT) + BO := by
        exact add_le_add
          (add_le_add (add_le_add (hK u) (hC u hu))
            (by simpa only [T, H, M] using hT u hu))
          (hO u hu)
      _ = J + C + BT + BO := rfl

/-- **Finite centered-atom exact open core.**  RH is equivalent to uniform boundedness, along one
nonnegative vertical line, of a canonical finite centered von Mangoldt sum whose cutoff is the
rounded mass-cone edge. -/
theorem riemannHypothesis_iff_xiMassCriticalCenteredAtomConeLineBound
    {a c sigma d : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hsigma : 0 < sigma) (hdhalf : 1 / 2 < d) (hda : d < a) :
    RiemannHypothesis ↔ XiMassCriticalCenteredAtomConeLineBound a sigma d := by
  exact (riemannHypothesis_iff_xiMassCriticalDiscreteRemainderConeFluxLineBound
    hhalf hca hsigma hdhalf hda).trans
      (xiMassCriticalDiscreteRemainderConeFluxLineBound_iff_centeredAtomCone
        hdhalf hda hsigma)

end

end RHTower
