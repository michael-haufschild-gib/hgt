import GaloisForLFunctions.RHTower.JointAncestryHaarSingularCertificate
import GaloisForLFunctions.RHTower.JointAncestryUndressedPositivity
import GaloisForLFunctions.RHTower.WeilLagFunctionOneSided
import GaloisForLFunctions.RHTower.WeilLagFunctionInteger
import GaloisForLFunctions.RHTower.WeilPaperTorusSpectralClassification

/-!
# Height mixtures of prime-Poisson laws are exactly RH

The natural ansatz for a JAS certificate is a superposition of prime-Poisson laws over heights:
a finite positive measure `m` on `ℝ` with

`A_σ(n) = e^{−σ‖n‖} ∫ e^{−it(log u − log v)} dm(t)`   for every character `n = u/v`,

i.e. the certificate `∫ μ_{σ,−t} dm(t)`.  **Theorem** (`riemannHypothesis_iff_exists_jasHeightMixture`):
for every real `σ`, such an `m` exists iff RH holds.  So at every dressing level, even where JAS
positivity is unconditional (`σ ≥ 2`), the height-mixture form of the certificate is equivalent to
RH: off RH the certificate at `σ = 2` exists but is not a mixture over heights.

**Proof.**  On the integer characters the mixture identity reads `Φ(log n) = ∫ e^{−it log n} dm(t)`,
so `|Φ(log n)| ≤ m(ℝ)`; the integer lags then bound the lag function everywhere, and a bounded lag
function is RH.  Conversely, under RH the zero measure `Σ_ρ w_ρ δ_{γ_ρ}` is such a mixture.

**Rigidity** (`jasHeightMixture_eq_jasZeroHeightMeasure`): the mixing measure is unique and equals the
zero measure.  On the characters `a/b` the mixture identity says that the characteristic function of
`m` agrees with `Φ` at `log b − log a`; these points are dense and both sides are continuous, so the
characteristic functions of `m` and of the zero measure coincide.
-/

open Complex MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- A height mixture at dressing `σ`: a finite positive measure on the heights whose prime-Poisson
superposition has the dressed aggregate as its moments. -/
def JasHeightMixture (σ : ℝ) (m : Measure ℝ) : Prop :=
  IsFiniteMeasure m ∧ ∀ n : Nat.Primes →₀ ℤ, jasDressedLagAggregate σ n =
    (Real.exp (-σ * jasLogSize n) : ℂ) *
      ∫ t, cexp (-(t : ℂ) * I * ((jasLogPos n - jasLogNeg n : ℝ) : ℂ)) ∂m

/-- **A height mixture forces RH.** -/
theorem riemannHypothesis_of_jasHeightMixture {σ : ℝ} {m : Measure ℝ}
    (h : JasHeightMixture σ m) : RiemannHypothesis := by
  obtain ⟨hfin, hm⟩ := h
  refine riemannHypothesis_iff_weilLagFunctionReal_bddAbove.mpr
    ⟨_, weilLagFunctionReal_le_of_integerLag_le (M := (m Set.univ).toReal) fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  have h1 := hm (jasNatChar n)
  rw [jasDressedLagAggregate_jasNatChar σ hn0, jasLogPos_jasNatChar hn0, jasLogNeg_jasNatChar,
    sub_zero, jasLogSize, jasLogPos_jasNatChar hn0, jasLogNeg_jasNatChar, add_zero] at h1
  have hne : (Real.exp (-σ * Real.log n) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have h2 := mul_left_cancel₀ hne h1
  have hbound : ‖weilLagFunction (Real.log n)‖ ≤ (m Set.univ).toReal := by
    rw [h2]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    have : ∀ t : ℝ, ‖cexp (-(t : ℂ) * I * ((Real.log n : ℝ) : ℂ))‖ = 1 := fun t => by
      rw [show -(t : ℂ) * I * ((Real.log n : ℝ) : ℂ) = ((-t * Real.log n : ℝ) : ℂ) * I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I]
    simp only [this, integral_const, smul_eq_mul, mul_one, measureReal_def]
  have h3 : integerLag n ≤ ‖weilLagFunction (Real.log n)‖ := by
    rw [integerLag, weilLagFunction_eq_ofReal, Complex.norm_real, Real.norm_eq_abs]
    exact le_abs_self _
  exact h3.trans hbound

/-- Under RH the zero measure `Σ_ρ w_ρ δ_{γ_ρ}` (with `w_ρ = 1/(ρ(1 − ρ)) > 0`). -/
def jasZeroHeightMeasure : Measure ℝ :=
  Measure.sum fun q : XiZeroCopy => ENNReal.ofReal (lagWeight q).re • Measure.dirac (q.1 : ℂ).im

instance : IsFiniteMeasure jasZeroHeightMeasure := by
  refine ⟨?_⟩
  rw [jasZeroHeightMeasure, Measure.sum_apply _ MeasurableSet.univ]
  have h : ∀ q : XiZeroCopy, (ENNReal.ofReal (lagWeight q).re • Measure.dirac (q.1 : ℂ).im)
      Set.univ = ENNReal.ofReal (lagWeight q).re :=
    fun q => by rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  simp_rw [h]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun q => (lagWeight_re_pos q).le) summable_lagWeight_re]
  exact ENNReal.ofReal_lt_top

/-- **Under RH the zero measure is a height mixture at every dressing.** -/
theorem jasHeightMixture_of_riemannHypothesis (hRH : RiemannHypothesis) (σ : ℝ) :
    JasHeightMixture σ jasZeroHeightMeasure := by
  refine ⟨inferInstance, fun n => ?_⟩
  have hint : Integrable (fun t : ℝ => cexp (-(t : ℂ) * I * ((jasLogPos n - jasLogNeg n : ℝ) : ℂ)))
      jasZeroHeightMeasure := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop : Continuous _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    rw [show -(t : ℂ) * I * ((jasLogPos n - jasLogNeg n : ℝ) : ℂ) =
      ((-t * (jasLogPos n - jasLogNeg n) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  unfold jasZeroHeightMeasure at hint ⊢
  rw [jasDressedLagAggregate, integral_sum_measure hint, weilLagFunction]
  congr 1
  refine tsum_congr fun q => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (lagWeight_re_pos q).le,
    Complex.real_smul]
  have hre : (q.1 : ℂ).re = 1 / 2 :=
    xi_zero_re_eq_half_of_RH hRH (xi_xiZeroCopy_eq_zero q)
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = (q.1 : ℂ).im := ⟨_, rfl⟩
  have hq : (q.1 : ℂ) = 1 / 2 + (γ : ℂ) * I := by
    apply Complex.ext <;> simp [hre, hγ]
  have hreal : (q.1 : ℂ) * (1 - (q.1 : ℂ)) = ((1 / 4 + γ ^ 2 : ℝ) : ℂ) := by
    rw [hq]; push_cast; linear_combination (-(γ : ℂ) ^ 2) * Complex.I_sq
  have hw : lagWeight q = ((lagWeight q).re : ℂ) := by
    unfold lagWeight
    rw [hreal, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [← hw, lagWeight, ← hγ, div_eq_mul_one_div, mul_comm (cexp _)]
  congr 1
  congr 1
  rw [show (q.1 : ℂ) - 1 / 2 = (γ : ℂ) * I by rw [hq]; ring]
  push_cast
  ring

/-- **Height mixtures are exactly RH, at every dressing level.** -/
theorem riemannHypothesis_iff_exists_jasHeightMixture (σ : ℝ) :
    RiemannHypothesis ↔ ∃ m : Measure ℝ, JasHeightMixture σ m :=
  ⟨fun h => ⟨_, jasHeightMixture_of_riemannHypothesis h σ⟩,
    fun ⟨_, h⟩ => riemannHypothesis_of_jasHeightMixture h⟩

/-- **Off RH the unconditional certificate is not a height mixture.**  At `σ = 2` the dressed
aggregate is positive semidefinite without hypothesis, but if RH fails no finite positive measure on
the heights reproduces it. -/
theorem jasDressedPSD_two_and_not_heightMixture_of_not_rh (h : ¬ RiemannHypothesis) :
    JasDressedPSD 2 ∧ ∀ m : Measure ℝ, ¬ JasHeightMixture 2 m :=
  ⟨jasDressedPSD_two, fun _ hm => h (riemannHypothesis_of_jasHeightMixture hm)⟩

theorem jasLogPos_sub_jasLogNeg_natChar_sub {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    jasLogPos (jasNatChar a - jasNatChar b) - jasLogNeg (jasNatChar a - jasNatChar b) =
      Real.log a - Real.log b := by
  have hL : ∀ m : Nat.Primes →₀ ℤ,
      jasLogPos m - jasLogNeg m = m.sum fun p k => (k : ℝ) * Real.log p :=
    fun m => by linarith [jasLogNeg_sub_jasLogPos m]
  have hnat : ∀ c : ℕ, c ≠ 0 → ((jasNatChar c).sum fun p k => (k : ℝ) * Real.log p) = Real.log c :=
    fun c hc => by rw [← hL, jasLogPos_jasNatChar hc, jasLogNeg_jasNatChar, sub_zero]
  rw [hL, Finsupp.sum_sub_index (fun p k₁ k₂ => by push_cast; ring), hnat a ha, hnat b hb]

/-- On the character `a/b` the mixture identity is an identity of characteristic functions. -/
theorem charFun_neg_eq_of_jasHeightMixture {σ : ℝ} {m : Measure ℝ} (h : JasHeightMixture σ m)
    {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    charFun m (-(Real.log a - Real.log b)) = weilLagFunction (Real.log b - Real.log a) := by
  have h1 := h.2 (jasNatChar a - jasNatChar b)
  rw [jasDressedLagAggregate] at h1
  have hne : (Real.exp (-σ * jasLogSize (jasNatChar a - jasNatChar b)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have h2 := mul_left_cancel₀ hne h1
  have hpn := jasLogPos_sub_jasLogNeg_natChar_sub ha hb
  rw [show jasLogNeg (jasNatChar a - jasNatChar b) - jasLogPos (jasNatChar a - jasNatChar b) =
    Real.log b - Real.log a by linarith, hpn] at h2
  rw [h2, charFun_apply_real]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show cexp (((-(Real.log a - Real.log b) : ℝ) : ℂ) * (t : ℂ) * I) =
    cexp (-(t : ℂ) * I * ((Real.log a - Real.log b : ℝ) : ℂ))
  congr 1
  push_cast
  ring

/-- **Rigidity: the mixing measure is the zero measure `Σ_ρ w_ρ δ_{γ_ρ}`.** -/
theorem jasHeightMixture_eq_jasZeroHeightMeasure {σ : ℝ} {m : Measure ℝ}
    (h : JasHeightMixture σ m) : m = jasZeroHeightMeasure := by
  have hZ := jasHeightMixture_of_riemannHypothesis (riemannHypothesis_of_jasHeightMixture h) σ
  haveI := h.1
  have hcont : ∀ (ν : Measure ℝ) [IsFiniteMeasure ν], Continuous fun y : ℝ => charFun ν (-y) :=
    fun ν _ => continuous_charFun.comp continuous_neg
  refine Measure.ext_of_charFun ?_
  have hext := Continuous.ext_on WeilWorkPBAP.dense_log_nat_ratios (hcont m)
    (hcont jasZeroHeightMeasure) ?_
  · funext x
    simpa using congrFun hext (-x)
  · rintro y ⟨a, b, ha, hb, rfl⟩
    show charFun m (-(Real.log a - Real.log b)) =
      charFun jasZeroHeightMeasure (-(Real.log a - Real.log b))
    rw [charFun_neg_eq_of_jasHeightMixture h ha hb, charFun_neg_eq_of_jasHeightMixture hZ ha hb]

end

end RHTower
