import GaloisForLFunctions.RHTower.LiClockThetaSignedGammaCoupling
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockPrimitiveNegative

/-!
# Positive-jump compound Poisson criterion for the actual Gamma mixture

For `p > 1` the actual Gamma mixture `μ_p` has log-Laplace transform `∫ (e^{-st} - 1) σ_p(t) dt`
with signed jump density `σ_p(t) = e^{-pt} P(t)/t` on `t > 0`.  The following are equivalent:

* `μ_p` is a compound Poisson law `CP(λ, Q)` with `λ ≥ 0` and jump law `Q` carried by `(0, ∞)`;
* `σ_p ≥ 0` almost everywhere;
* `P(t) ≥ 0` for every `t > 0`;
* the Riemann hypothesis.

Forward: the Gamma jump coupling `μ_p ⋆ CP(G⁻) = CP(G⁺)` and `μ_p = CP(λ, Q)` give
`λ L_Q + L_{G⁻} = L_{G⁺} + c`; adding the atom `|c| δ₀` to the deficient side, Laplace uniqueness of
finite half-line measures and the absence of atoms at the origin force `c = 0` and
`G⁺ = λ Q + G⁻`, so `σ_p dt = G⁺ - G⁻ ≥ 0`.  Converse: a nonnegative `σ_p` of mass `H(p)` is itself
the jump measure.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace RHTower

noncomputable section

local notation "Lap" => GaloisForLFunctions.HTGeometry.laplace
local notation "CP" => GaloisForLFunctions.HTGeometry.compoundPoisson
local notation "P" => liEvenCrossActualClockPrimitive
local notation "σ" => liClockThetaSignedGammaDensity

private theorem laplace_le_mass (ν : Measure ℝ) (hν : ∀ᵐ t ∂ν, 0 ≤ t) {s : ℝ} (hs : 0 ≤ s) :
    Lap ν s ≤ ν univ := by
  unfold GaloisForLFunctions.HTGeometry.laplace
  calc ∫⁻ t, ENNReal.ofReal (Real.exp (-(s * t))) ∂ν ≤ ∫⁻ _, 1 ∂ν := by
        refine lintegral_mono_ae (hν.mono fun t ht => ?_)
        rw [ENNReal.ofReal_le_one]
        exact Real.exp_le_one_iff.2 (by nlinarith)
    _ = ν univ := by simp

private theorem laplace_ne_top (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ∀ᵐ t ∂ν, 0 ≤ t) {s : ℝ}
    (hs : 0 ≤ s) : Lap ν s ≠ ∞ :=
  ne_top_of_le_ne_top (measure_ne_top ν univ) (laplace_le_mass ν hν hs)

private theorem laplace_add (μ ν : Measure ℝ) (s : ℝ) : Lap (μ + ν) s = Lap μ s + Lap ν s := by
  unfold GaloisForLFunctions.HTGeometry.laplace
  rw [lintegral_add_measure]

private theorem laplace_smul (c : ℝ≥0∞) (ν : Measure ℝ) (s : ℝ) :
    Lap (c • ν) s = c * Lap ν s := by
  unfold GaloisForLFunctions.HTGeometry.laplace
  rw [lintegral_smul_measure, smul_eq_mul]

private theorem laplace_at_zero (ν : Measure ℝ) : Lap ν 0 = ν univ := by
  simp [GaloisForLFunctions.HTGeometry.laplace]

private theorem isFiniteMeasure_ofReal_smul (a : ℝ) (ν : Measure ℝ) [IsFiniteMeasure ν] :
    IsFiniteMeasure (ENNReal.ofReal a • ν) := by
  refine ⟨?_⟩
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ν univ)

private theorem singleton_zero_eq_zero (ν : Measure ℝ) (hν : ∀ᵐ t ∂ν, 0 < t) : ν {0} = 0 := by
  refine measure_mono_null ?_ (ae_iff.1 hν)
  intro t ht
  simp only [mem_singleton_iff] at ht
  simp [ht]

private theorem ae_nonneg_smul_dirac (a : ℝ≥0∞) :
    ∀ᵐ t ∂(a • Measure.dirac (0 : ℝ)), 0 ≤ t :=
  Measure.ae_smul_measure ((ae_dirac_iff measurableSet_Ici).2 le_rfl) a

/-- **Forward direction.**  If `μ_p = CP(λ, Q)` with jumps carried by `(0, ∞)`, then the signed
Gamma jump density is nonnegative almost everywhere. -/
theorem ae_nonneg_liClockThetaSignedGammaDensity_of_eq_compoundPoisson {p : ℝ} (hp : 1 < p)
    {lam : ℝ} {Q : Measure ℝ} [IsProbabilityMeasure Q] (hlam : 0 ≤ lam) (hQ : ∀ᵐ t ∂Q, 0 < t)
    (hμ : liClockThetaGammaMixture p = CP lam Q) : 0 ≤ᵐ[volume] σ p := by
  obtain ⟨-, hdata⟩ := liClockThetaJumpMeasure_admission hp
  obtain ⟨hmP, -, hGPfin, -, hGPuniv, -, hGPsupp⟩ := hdata true
  obtain ⟨hmM, -, hGMfin, -, hGMuniv, -, hGMsupp⟩ := hdata false
  set Gp := liClockThetaGammaJumpMeasure p true
  set Gm := liClockThetaGammaJumpMeasure p false
  set mp := liClockThetaJumpMass p true
  set mm := liClockThetaJumpMass p false
  haveI := hGPfin
  haveI := hGMfin
  have hQ0 : ∀ᵐ t ∂Q, 0 ≤ t := hQ.mono fun _ ht => ht.le
  have hGP0 : ∀ᵐ t ∂Gp, 0 ≤ t := hGPsupp.mono fun _ ht => ht.le
  have hGM0 : ∀ᵐ t ∂Gm, 0 ≤ t := hGMsupp.mono fun _ ht => ht.le
  haveI : IsProbabilityMeasure ((ENNReal.ofReal (liClockThetaJumpMass p false))⁻¹ •
      liClockThetaGammaJumpMeasure p false) := isProbabilityMeasure_inv_ofReal_smul _ hmM hGMuniv
  haveI := GaloisForLFunctions.HTGeometry.isProbabilityMeasure_compoundPoisson
    (liClockThetaJumpMass p false) hmM.le
    ((ENNReal.ofReal (liClockThetaJumpMass p false))⁻¹ • liClockThetaGammaJumpMeasure p false)
  have hcoup := liClockThetaGammaMixture_poisson_coupling hp
  unfold liClockThetaGammaJumpPoisson at hcoup
  simp only [one_mul] at hcoup
  rw [hμ] at hcoup
  set c := lam + mm - mp with hcdef
  have hbal : ∀ s : ℝ, 0 ≤ s →
      lam * (Lap Q s).toReal + (Lap Gm s).toReal = (Lap Gp s).toReal + c := by
    intro s hs
    have h := congrArg (fun ν => Lap ν s) hcoup
    have hLM := laplace_normalized_compoundPoisson Gm hmM hGMuniv hGM0 (time := 1) zero_le_one hs
    have hLP := laplace_normalized_compoundPoisson Gp hmP hGPuniv hGP0 (time := 1) zero_le_one hs
    simp only [one_mul] at hLM hLP
    rw [GaloisForLFunctions.HTGeometry.laplace_conv,
      GaloisForLFunctions.HTGeometry.laplace_compoundPoisson lam hlam Q s
        (ne_top_of_le_ne_top ENNReal.one_ne_top
          (GaloisForLFunctions.HTGeometry.laplace_le_one Q hs hQ0)),
      hLM, hLP, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add,
      ENNReal.ofReal_eq_ofReal_iff (Real.exp_nonneg _) (Real.exp_nonneg _), Real.exp_eq_exp] at h
    rw [hcdef]
    linarith
  set ν₁ := ENNReal.ofReal lam • Q + Gm + ENNReal.ofReal (max (-c) 0) • Measure.dirac (0 : ℝ)
  set ν₂ := Gp + ENNReal.ofReal (max c 0) • Measure.dirac (0 : ℝ)
  haveI := isFiniteMeasure_ofReal_smul lam Q
  haveI := isFiniteMeasure_ofReal_smul (max (-c) 0) (Measure.dirac (0 : ℝ))
  haveI := isFiniteMeasure_ofReal_smul (max c 0) (Measure.dirac (0 : ℝ))
  have hsupp₁ : ∀ᵐ t ∂ν₁, 0 ≤ t := by
    rw [ae_add_measure_iff, ae_add_measure_iff]
    exact ⟨⟨Measure.ae_smul_measure hQ0 _, hGM0⟩, ae_nonneg_smul_dirac _⟩
  have hsupp₂ : ∀ᵐ t ∂ν₂, 0 ≤ t := by
    rw [ae_add_measure_iff]
    exact ⟨hGP0, ae_nonneg_smul_dirac _⟩
  have hlap : ∀ s : ℝ, 0 ≤ s → Lap ν₁ s = Lap ν₂ s := by
    intro s hs
    have hQf : Lap Q s ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top
      (GaloisForLFunctions.HTGeometry.laplace_le_one Q hs hQ0)
    have hMf := laplace_ne_top Gm hGM0 hs
    have hPf := laplace_ne_top Gp hGP0 hs
    simp only [ν₁, ν₂, laplace_add, laplace_smul,
      GaloisForLFunctions.HTGeometry.laplace_dirac_zero, mul_one]
    have hL0 : 0 ≤ lam * (Lap Q s).toReal := mul_nonneg hlam ENNReal.toReal_nonneg
    have e₁ : ENNReal.ofReal lam * Lap Q s + Lap Gm s + ENNReal.ofReal (max (-c) 0) =
        ENNReal.ofReal (lam * (Lap Q s).toReal + (Lap Gm s).toReal + max (-c) 0) := by
      rw [ENNReal.ofReal_add (add_nonneg hL0 ENNReal.toReal_nonneg) (le_max_right _ _),
        ENNReal.ofReal_add hL0 ENNReal.toReal_nonneg, ENNReal.ofReal_mul hlam,
        ENNReal.ofReal_toReal hQf, ENNReal.ofReal_toReal hMf]
    have e₂ : Lap Gp s + ENNReal.ofReal (max c 0) =
        ENNReal.ofReal ((Lap Gp s).toReal + max c 0) := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (le_max_right _ _), ENNReal.ofReal_toReal hPf]
    rw [e₁, e₂]
    congr 1
    have := hbal s hs
    rcases le_total c 0 with hc | hc
    · rw [max_eq_left (by linarith : (0 : ℝ) ≤ -c), max_eq_right hc]; linarith
    · rw [max_eq_right (by linarith : -c ≤ 0), max_eq_left hc]; linarith
  have heq := finite_halfLine_laplace_ext ν₁ ν₂ hsupp₁ hsupp₂ hlap
  have h0 := congrArg (fun ν : Measure ℝ => ν {0}) heq
  simp only [ν₁, ν₂, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply_of_mem (mem_singleton (0 : ℝ)), mul_one, singleton_zero_eq_zero Q hQ,
    singleton_zero_eq_zero Gm hGMsupp, singleton_zero_eq_zero Gp hGPsupp, mul_zero,
    zero_add] at h0
  have hc : c = 0 := by
    rw [ENNReal.ofReal_eq_ofReal_iff (le_max_right _ _) (le_max_right _ _)] at h0
    rcases lt_trichotomy c 0 with h | h | h
    · rw [max_eq_left (by linarith), max_eq_right h.le] at h0; linarith
    · exact h
    · rw [max_eq_right (by linarith), max_eq_left h.le] at h0; linarith
  have heq' : ENNReal.ofReal lam • Q + Gm = Gp := by
    simpa [ν₁, ν₂, hc] using heq
  have hsigned := liClockThetaSignedGammaMeasure_admission hp
  have hint : Integrable (σ p) volume := by
    have := (hsigned.2 (fun _ => 1) measurable_const ⟨1, fun _ => by simp⟩).1
    simpa using this
  refine ae_nonneg_of_forall_setIntegral_nonneg hint fun A hA _ => ?_
  have h1 := hsigned.1 A hA
  rw [liClockThetaSignedGammaMeasure, withDensityᵥ_apply hint hA] at h1
  have heq'' : ENNReal.ofReal lam • Q + Gm = liClockThetaGammaJumpMeasure p true := heq'
  rw [h1, ← heq'', Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top Q A))
      (measure_ne_top Gm A), add_sub_cancel_right]
  exact ENNReal.toReal_nonneg

/-- An almost-everywhere nonnegative signed Gamma jump density forces `P ≥ 0` on `(0, ∞)`. -/
theorem liEvenCrossActualClockPrimitive_nonneg_of_ae_nonneg_signedGammaDensity {p : ℝ}
    (hp : 1 < p) (h : 0 ≤ᵐ[volume] σ p) {t : ℝ} (ht : 0 < t) : 0 ≤ P t := by
  by_contra hneg
  rw [not_le] at hneg
  have hU : IsOpen (Ioi (0 : ℝ) ∩ {s | P s < 0}) :=
    isOpen_Ioi.inter (isOpen_lt contDiff_liEvenCrossActualClockPrimitive.continuous continuous_const)
  refine hU.measure_ne_zero volume ⟨t, ht, hneg⟩ (measure_mono_null (fun s hs => ?_) (ae_iff.1 h))
  simp only [mem_setOf_eq, Pi.zero_apply, not_le]
  rw [liClockThetaSignedGammaDensity_eq_primitive hp, indicator_of_mem hs.1]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (Real.exp_pos _) hs.2) hs.1

theorem liClockThetaSignedGammaDensity_nonneg_of_primitive_nonneg {p : ℝ} (hp : 1 < p)
    (hP : ∀ t, 0 < t → 0 ≤ P t) (t : ℝ) : 0 ≤ σ p t := by
  rw [liClockThetaSignedGammaDensity_eq_primitive hp]
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem ht]
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le (hP t ht)) (le_of_lt ht)
  · rw [indicator_of_notMem ht]

/-- **Converse.**  If `P ≥ 0` on `(0, ∞)`, then `μ_p = CP(H(p), Q)` with
`Q = σ_p dt / H(p)` carried by `(0, ∞)`. -/
theorem liClockThetaGammaMixture_eq_compoundPoisson_of_nonneg {p : ℝ} (hp : 1 < p)
    (hP : ∀ t, 0 < t → 0 ≤ P t) :
    ∃ lam : ℝ, ∃ Q : Measure ℝ, 0 < lam ∧ IsProbabilityMeasure Q ∧ (∀ᵐ t ∂Q, 0 < t) ∧
      liClockThetaGammaMixture p = CP lam Q := by
  have hp0 : 0 < p := by linarith
  have hσ0 := liClockThetaSignedGammaDensity_nonneg_of_primitive_nonneg hp hP
  have hσm : Measurable (σ p) := by
    have e : σ p = (Ioi (0 : ℝ)).indicator (fun t =>
        Real.exp (-(p * t)) * liEvenCrossActualClockPrimitive t / t) :=
      funext (liClockThetaSignedGammaDensity_eq_primitive hp)
    rw [e]
    have := contDiff_liEvenCrossActualClockPrimitive.continuous.measurable
    exact Measurable.indicator (by fun_prop) measurableSet_Ioi
  set lam := liClockThetaReciprocalLog p
  have hlam : 0 < lam := Real.log_pos (liClockThetaGammaNormalizer_source hp0).2.2
  set τ := volume.withDensity (fun t => ENNReal.ofReal (σ p t))
  have hτ : ∀ s : ℝ, 0 ≤ s → Lap τ s = ENNReal.ofReal (liClockThetaReciprocalLog (p + s)) := by
    intro s hs
    obtain ⟨hi, hval, -, -⟩ := liClockThetaSignedGammaDensity_laplace hp hs
    unfold GaloisForLFunctions.HTGeometry.laplace
    rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop), ← hval,
      ofReal_integral_eq_lintegral_ofReal hi
        (Eventually.of_forall fun t => mul_nonneg (Real.exp_pos _).le (hσ0 t))]
    refine lintegral_congr fun t => ?_
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (hσ0 t), mul_comm]
  have hτuniv : τ univ = ENNReal.ofReal lam := by
    rw [← laplace_at_zero, hτ 0 le_rfl, add_zero]
  haveI : IsFiniteMeasure τ := ⟨by rw [hτuniv]; exact ENNReal.ofReal_lt_top⟩
  have hτsupp : ∀ᵐ t ∂τ, 0 < t := by
    rw [ae_iff]
    have e : {t : ℝ | ¬0 < t} = Iic 0 := by ext t; simp
    rw [e, withDensity_apply _ measurableSet_Iic]
    refine (setLIntegral_congr_fun measurableSet_Iic fun t (ht : t ≤ 0) => ?_).trans
      (lintegral_zero)
    show ENNReal.ofReal (σ p t) = 0
    rw [liClockThetaSignedGammaDensity_eq_primitive hp,
      indicator_of_notMem (by simpa using ht), ENNReal.ofReal_zero]
  set Q := (ENNReal.ofReal lam)⁻¹ • τ
  haveI hQprob : IsProbabilityMeasure Q := isProbabilityMeasure_inv_ofReal_smul τ hlam hτuniv
  have hQsupp : ∀ᵐ t ∂Q, 0 < t := Measure.ae_smul_measure hτsupp _
  refine ⟨lam, Q, hlam, hQprob, hQsupp, ?_⟩
  have hadm := liClockThetaGammaMixture_admission hp0
  haveI := hadm.1
  haveI := GaloisForLFunctions.HTGeometry.isProbabilityMeasure_compoundPoisson lam hlam.le Q
  refine finite_halfLine_laplace_ext _ _ hadm.2.1
    (compoundPoisson_ae_nonneg Q (hQsupp.mono fun _ ht => ht.le) lam) fun s hs => ?_
  have hQf : Lap Q s ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top
    (GaloisForLFunctions.HTGeometry.laplace_le_one Q hs (hQsupp.mono fun _ ht => ht.le))
  rw [liClockThetaGammaMixture_laplace hp0 hs,
    GaloisForLFunctions.HTGeometry.laplace_compoundPoisson lam hlam.le Q s hQf]
  congr 1
  have hQs : (Lap Q s).toReal = lam⁻¹ * liClockThetaReciprocalLog (p + s) := by
    simp only [Q, laplace_smul, hτ s hs, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal hlam.le]
    rw [ENNReal.toReal_ofReal]
    exact (Real.log_pos (liClockThetaGammaNormalizer_source (by linarith : 0 < p + s)).2.2).le
  rw [hQs]
  have hN := (liClockThetaGammaNormalizer_source hp0).2.2
  have hNs := (liClockThetaGammaNormalizer_source (by linarith : 0 < p + s)).2.2
  have e : lam * (lam⁻¹ * liClockThetaReciprocalLog (p + s) - 1) =
      liClockThetaReciprocalLog (p + s) - lam := by
    field_simp
  rw [e, Real.exp_sub, show lam = liClockThetaReciprocalLog p from rfl]
  unfold liClockThetaReciprocalLog
  rw [Real.exp_log (by linarith), Real.exp_log (by linarith)]

/-- **Positive-jump compound Poisson criterion.**  For `p > 1`:
`μ_p = CP(λ, Q)` with jumps on `(0, ∞)` ⟺ `σ_p ≥ 0` a.e. ⟺ `P ≥ 0` on `(0, ∞)` ⟺ RH. -/
theorem liClockThetaGammaMixture_positiveJumpCompoundPoisson_iff {p : ℝ} (hp : 1 < p) :
    ((∃ lam : ℝ, ∃ Q : Measure ℝ, 0 ≤ lam ∧ IsProbabilityMeasure Q ∧ (∀ᵐ t ∂Q, 0 < t) ∧
        liClockThetaGammaMixture p = CP lam Q) ↔ 0 ≤ᵐ[volume] σ p) ∧
    (0 ≤ᵐ[volume] σ p ↔ ∀ t, 0 < t → 0 ≤ P t) ∧
    ((∀ t, 0 < t → 0 ≤ P t) ↔ RiemannHypothesis) := by
  have hPσ : (∀ t, 0 < t → 0 ≤ P t) → 0 ≤ᵐ[volume] σ p := fun hP =>
    Eventually.of_forall (liClockThetaSignedGammaDensity_nonneg_of_primitive_nonneg hp hP)
  have hσP : 0 ≤ᵐ[volume] σ p → ∀ t, 0 < t → 0 ≤ P t := fun h _ ht =>
    liEvenCrossActualClockPrimitive_nonneg_of_ae_nonneg_signedGammaDensity hp h ht
  refine ⟨⟨fun ⟨lam, Q, hlam, hQ, hsupp, hμ⟩ => ?_, fun h => ?_⟩, ⟨hσP, hPσ⟩, ?_⟩
  · haveI := hQ
    exact ae_nonneg_liClockThetaSignedGammaDensity_of_eq_compoundPoisson hp hlam hsupp hμ
  · obtain ⟨lam, Q, hlam, hQ, hsupp, hμ⟩ :=
      liClockThetaGammaMixture_eq_compoundPoisson_of_nonneg hp (hσP h)
    exact ⟨lam, Q, hlam.le, hQ, hsupp, hμ⟩
  · rw [(liEvenCrossActualClockPrimitive_rh_criteria).1]
    constructor
    · intro h t ht
      rcases ht.eq_or_lt with rfl | ht
      · simp [liEvenCrossActualClockPrimitive]
      · exact h t ht
    · exact fun h t ht => h t ht.le

end

end RHTower
