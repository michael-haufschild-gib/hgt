import GaloisForLFunctions.RHTower.Deninger.DeningerAdiabaticGreenStokes

/-!
# The strict Gamma endpoint of the adiabatic Möbius path

The ordinary-integer series has a genuine second boundary.  As the adiabatic parameter tends to
infinity, every dilation except `n = 1` dies.  The proof is in full-line `L¹`: on the cofinal wall
`a ≥ 1`, every term is dominated by the fixed summable majorant `C / n²`.  Thus the endpoint is
the undeformed even logarithmic pullback, and continuity transports it to tempered distributions
and the two-collar boundary.
-/

namespace RHTower

open Filter Topology MeasureTheory SchwartzMap FourierTransform ArithmeticFunction

noncomputable section

/-- The surviving `n = 1` Gamma collar in full-line `L¹`. -/
def deningerAdiabaticGammaLp (h : DeningerMeyerSource) :
    Lp ℂ (1 : ENNReal) (volume : Measure ℝ) :=
  deningerAdiabaticEvenLogPullDilationLp h 1 (by omega)

/-- The `n = 1` term is independent of the adiabatic parameter. -/
@[simp]
theorem deningerAdiabaticMobiusTermLp_one
    (h : DeningerMeyerSource) (a : ℝ) :
    deningerAdiabaticMobiusTermLp h 1 a = deningerAdiabaticGammaLp h := by
  simp [deningerAdiabaticMobiusTermLp, deningerAdiabaticGammaLp,
    deningerAdiabaticMobiusScalar, deningerAdiabaticMobiusCoefficient]

/-- Fixed `n⁻²` majorant on the cofinal adiabatic wall `a ≥ 1`. -/
def deningerAdiabaticGammaMajorant
    (h : DeningerMeyerSource) (n : ℕ) : ℝ :=
  (2 * deningerAdiabaticLogPullNormMass h) * (n : ℝ) ^ (-(2 : ℝ))

theorem summable_deningerAdiabaticGammaMajorant
    (h : DeningerMeyerSource) :
    Summable (deningerAdiabaticGammaMajorant h) := by
  have hpow : Summable (fun n : ℕ => (n : ℝ) ^ (-(2 : ℝ))) := by
    rw [Real.summable_nat_rpow]
    norm_num
  exact hpow.mul_left _

theorem norm_deningerAdiabaticMobiusTermLp_le_gammaMajorant
    (h : DeningerMeyerSource) {a : ℝ} (ha : 1 ≤ a) (n : ℕ) :
    ‖deningerAdiabaticMobiusTermLp h n a‖ ≤
      deningerAdiabaticGammaMajorant h n := by
  by_cases hn : 0 < n
  · rw [deningerAdiabaticMobiusTermLp, dif_pos hn, norm_smul,
      norm_deningerAdiabaticEvenLogPullDilationLp h hn]
    have hmass := deningerAdiabaticLogPullNormMass_nonneg h
    calc
      ‖deningerAdiabaticMobiusScalar n a‖ *
          (2 * (n : ℝ)⁻¹ * deningerAdiabaticLogPullNormMass h) ≤
        deningerAdiabaticMobiusCoefficient a n *
          (2 * (n : ℝ)⁻¹ * deningerAdiabaticLogPullNormMass h) := by
            gcongr
            exact norm_deningerAdiabaticMobiusScalar_le (by linarith) n
      _ ≤ deningerAdiabaticMobiusCoefficient 1 n *
          (2 * (n : ℝ)⁻¹ * deningerAdiabaticLogPullNormMass h) := by
            gcongr
            exact deningerAdiabaticMobiusCoefficient_anti zero_le_one ha hn
      _ = deningerAdiabaticGammaMajorant h n := by
        rw [deningerAdiabaticGammaMajorant]
        calc
          deningerAdiabaticMobiusCoefficient 1 n *
              (2 * (n : ℝ)⁻¹ * deningerAdiabaticLogPullNormMass h) =
            (2 * deningerAdiabaticLogPullNormMass h) *
              (deningerAdiabaticMobiusCoefficient 1 n * (n : ℝ)⁻¹) := by ring
          _ = (2 * deningerAdiabaticLogPullNormMass h) *
              (n : ℝ) ^ (-(1 + 1 : ℝ)) := by
            rw [deningerAdiabaticMobiusCoefficient_mul_inv 1 hn]
          _ = (2 * deningerAdiabaticLogPullNormMass h) *
              (n : ℝ) ^ (-(2 : ℝ)) := by norm_num
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    rw [deningerAdiabaticMobiusTermLp, dif_neg (by omega), norm_zero]
    exact mul_nonneg (mul_nonneg zero_le_two
      (deningerAdiabaticLogPullNormMass_nonneg h)) (Real.rpow_nonneg (by norm_num) _)

/-- Every individual ordinary-integer term converges to the isolated Gamma term. -/
theorem tendsto_deningerAdiabaticMobiusTermLp_atTop
    (h : DeningerMeyerSource) (n : ℕ) :
    Tendsto (fun a : ℝ => deningerAdiabaticMobiusTermLp h n a) atTop
      (𝓝 (if n = 1 then deningerAdiabaticGammaLp h else 0)) := by
  by_cases hn1 : n = 1
  · subst n
    simpa using tendsto_const_nhds
  · by_cases hn0 : n = 0
    · subst n
      simp [deningerAdiabaticMobiusTermLp]
    · have hn : 0 < n := Nat.pos_of_ne_zero hn0
      have hn2 : 2 ≤ n := by omega
      have hlog : 0 < Real.log (n : ℝ) := by
        apply Real.log_pos
        exact_mod_cast (show 1 < n by omega)
      have hmul : Tendsto (fun a : ℝ => a * Real.log (n : ℝ)) atTop atTop :=
        tendsto_id.atTop_mul_const hlog
      have hneg : Tendsto (fun a : ℝ => -a * Real.log (n : ℝ)) atTop atBot := by
        convert tendsto_neg_atTop_atBot.comp hmul using 1
        funext a
        simp only [Function.comp_apply]
        ring
      have hexp : Tendsto (fun a : ℝ => Real.exp (-a * Real.log (n : ℝ))) atTop
          (𝓝 0) :=
        Real.tendsto_exp_atBot.comp hneg
      have hscalar : Tendsto (deningerAdiabaticMobiusScalar n) atTop (𝓝 0) := by
        have hreal := hexp.const_mul (((moebius n : ℤ) : ℝ))
        have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
        convert hcomplex using 1
        · funext a
          rfl
        · simp
      have hterm := hscalar.smul_const
        (deningerAdiabaticEvenLogPullDilationLp h n hn)
      simpa [deningerAdiabaticMobiusTermLp, hn, hn1] using hterm

/-- **Strict Gamma endpoint in full-line `L¹`.** -/
theorem tendsto_deningerAdiabaticEvenPreimageLp_atTop
    (h : DeningerMeyerSource) :
    Tendsto (fun a : ℝ => deningerAdiabaticEvenPreimageLpExt a h) atTop
      (𝓝 (deningerAdiabaticGammaLp h)) := by
  have hsum : Tendsto
      (fun a : ℝ => ∑' n : ℕ, deningerAdiabaticMobiusTermLp h n a) atTop
      (𝓝 (∑' n : ℕ, if n = 1 then deningerAdiabaticGammaLp h else 0)) :=
    tendsto_tsum_of_dominated_convergence
      (summable_deningerAdiabaticGammaMajorant h)
      (tendsto_deningerAdiabaticMobiusTermLp_atTop h)
      (by
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
        exact fun n => norm_deningerAdiabaticMobiusTermLp_le_gammaMajorant h ha n)
  have hsum' : Tendsto
      (fun a : ℝ => ∑' n : ℕ, deningerAdiabaticMobiusTermLp h n a) atTop
      (𝓝 (deningerAdiabaticGammaLp h)) := by
    simpa only [tsum_ite_eq] using hsum
  apply hsum'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  rw [tsum_deningerAdiabaticMobiusTermLp_eq ha h,
    deningerAdiabaticEvenPreimageLpExt, dif_pos ha.le]

/-- Gamma endpoint as a tempered distribution. -/
def deningerAdiabaticGammaDistribution (h : DeningerMeyerSource) : 𝓢'(ℝ, ℂ) :=
  MeasureTheory.Lp.toTemperedDistribution (deningerAdiabaticGammaLp h)

/-- **Strict Gamma endpoint in tempered distributions.** -/
theorem tendsto_deningerAdiabaticPreimageDistributionExt_atTop
    (h : DeningerMeyerSource) :
    Tendsto (fun a : ℝ => deningerAdiabaticPreimageDistributionExt a h) atTop
      (𝓝 (deningerAdiabaticGammaDistribution h)) := by
  exact (MeasureTheory.Lp.toTemperedDistributionCLM ℂ volume 1).continuous.continuousAt.tendsto.comp
    (tendsto_deningerAdiabaticEvenPreimageLp_atTop h)

/-- The two-collar Gamma boundary. -/
def deningerAdiabaticGammaBoundary (h : DeningerMeyerSource) : 𝓢'(ℝ, ℂ) :=
  𝓕 (deningerAdiabaticGammaDistribution h) -
    deningerAdiabaticGammaDistribution (deningerMeyerCollarExchange h)

/-- **Strict Gamma endpoint of the unsquared two-collar boundary.** -/
theorem tendsto_deningerAdiabaticMobiusBoundaryExt_atTop
    (h : DeningerMeyerSource) :
    Tendsto (fun a : ℝ => deningerAdiabaticMobiusBoundaryExt a h) atTop
      (𝓝 (deningerAdiabaticGammaBoundary h)) := by
  have hfirst : Tendsto
      (fun a : ℝ => 𝓕 (deningerAdiabaticPreimageDistributionExt a h)) atTop
      (𝓝 (𝓕 (deningerAdiabaticGammaDistribution h))) := by
    have hraw := continuous_fourier.continuousAt.tendsto.comp
      (tendsto_deningerAdiabaticPreimageDistributionExt_atTop h)
    convert hraw using 1
    funext a
    rfl
  have hsecond := tendsto_deningerAdiabaticPreimageDistributionExt_atTop
    (deningerMeyerCollarExchange h)
  simpa only [deningerAdiabaticMobiusBoundaryExt,
    deningerAdiabaticCollarLiftExt, deningerAdiabaticGammaBoundary] using
      hfirst.sub hsecond

/-- **Strict critical endpoint of the same boundary.**  The limit is the literal pre-existing
Möbius--Fourier commutator, not a newly postulated boundary value. -/
theorem tendsto_deningerAdiabaticMobiusBoundaryExt_atBot
    (h : DeningerMeyerSource) :
    Tendsto
      (fun a : Set.Ioi (0 : ℝ) => deningerAdiabaticMobiusBoundaryExt a h)
      atBot (𝓝 (deningerMobiusCommutator (DeningerMeyerSource.toSource h))) := by
  have hfirst : Tendsto
      (fun a : Set.Ioi (0 : ℝ) =>
        𝓕 (deningerAdiabaticPreimageDistribution a.property.le h)) atBot
      (𝓝 (𝓕 (deningerPreimageDistribution (DeningerMeyerSource.toSource h)))) := by
    have hraw := continuous_fourier.continuousAt.tendsto.comp
      (tendsto_deningerAdiabaticPreimageDistribution_zero h)
    convert hraw using 1
    funext a
    rfl
  have hsecond := tendsto_deningerAdiabaticPreimageDistribution_zero
    (deningerMeyerCollarExchange h)
  have hboundary := hfirst.sub hsecond
  have hboundary' : Tendsto
      (fun a : Set.Ioi (0 : ℝ) =>
        𝓕 (deningerAdiabaticPreimageDistribution a.property.le h) -
          deningerAdiabaticPreimageDistribution a.property.le
            (deningerMeyerCollarExchange h))
      atBot (𝓝 (deningerMobiusCommutator (DeningerMeyerSource.toSource h))) := by
    simpa only [deningerMeyerCollarExchange_toSource,
      deningerMobiusCommutator] using hboundary
  apply hboundary'.congr'
  filter_upwards with a
  rw [deningerAdiabaticMobiusBoundaryExt, deningerAdiabaticCollarLiftExt,
    deningerAdiabaticPreimageDistributionExt_eq a.property,
    deningerAdiabaticPreimageDistributionExt_eq a.property]

end

end RHTower
