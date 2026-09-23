import GaloisForLFunctions.HTGeometry.MeasurementJetBridge
import GaloisForLFunctions.HTGeometry.SignedAmplitudeSquareDifference
import GaloisForLFunctions.HTGeometry.ErlangWignerSmithPacket
import GaloisForLFunctions.HTGeometry.BumpMollifierFamily
import GaloisForLFunctions.HTGeometry.FiniteEvaluationPacket
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

open Complex Filter Function MeasureTheory Real Set Topology
open scoped Convolution ContDiff Filter
open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def compactPacketBump (ε : ℝ) : ContDiffBump (0 : ℝ) :=
  if hε : 0 < ε then widthBump hε else widthBump (by norm_num : (0 : ℝ) < 1)

theorem compactPacketBump_eq_widthBump {ε : ℝ} (hε : 0 < ε) :
    compactPacketBump ε = widthBump hε := by
  simp [compactPacketBump, hε]

theorem compactPacketBump_rOut {ε : ℝ} (hε : 0 < ε) :
    (compactPacketBump ε).rOut = ε := by
  simp [compactPacketBump, hε, widthBump]

theorem tendsto_compactPacketBump_rOut :
    Tendsto (fun ε : ℝ => (compactPacketBump ε).rOut) (𝓝[>] 0) (𝓝 0) := by
  have heq : (fun ε : ℝ => (compactPacketBump ε).rOut) =ᶠ[𝓝[>] 0] id := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact compactPacketBump_rOut hε
  exact ((tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0)).mono_left
    nhdsWithin_le_nhds).congr' heq.symm

def compactPacketRawMass (ε : ℝ) : ℝ :=
  ∫ t : ℝ, (compactPacketBump ε t) ^ 2

theorem compactPacketRawMass_pos (ε : ℝ) : 0 < compactPacketRawMass ε := by
  unfold compactPacketRawMass
  let φ := compactPacketBump ε
  have hc : HasCompactSupport (fun t : ℝ => (φ t) ^ 2) := by
    have hc' : HasCompactSupport (fun t : ℝ => φ t * φ t) :=
      φ.hasCompactSupport.mul_right
    simpa [pow_two] using hc'
  have hi : Integrable (fun t : ℝ => (φ t) ^ 2) :=
    (φ.continuous.pow 2).integrable_of_hasCompactSupport hc
  rw [integral_pos_iff_support_of_nonneg (fun t => sq_nonneg (φ t)) hi]
  have hsupp : Function.support (fun t : ℝ => (φ t) ^ 2) = Function.support φ := by
    ext t
    simp [Function.mem_support]
  rw [hsupp, φ.support_eq]
  exact Metric.measure_ball_pos volume 0 φ.rOut_pos

def compactPacketAmplitude (ε t : ℝ) : ℝ :=
  compactPacketBump ε t / Real.sqrt (compactPacketRawMass ε)

def compactPacketDensity (ε t : ℝ) : ℝ :=
  compactPacketAmplitude ε t ^ 2

theorem compactPacketDensity_eq (ε t : ℝ) :
    compactPacketDensity ε t =
      (compactPacketBump ε t) ^ 2 / compactPacketRawMass ε := by
  rw [compactPacketDensity, compactPacketAmplitude, div_pow]
  rw [Real.sq_sqrt (compactPacketRawMass_pos ε).le]

theorem compactPacketDensity_nonneg (ε t : ℝ) : 0 ≤ compactPacketDensity ε t :=
  sq_nonneg _

theorem integral_compactPacketDensity (ε : ℝ) :
    (∫ t : ℝ, compactPacketDensity ε t) = 1 := by
  simp_rw [compactPacketDensity_eq, div_eq_mul_inv]
  rw [MeasureTheory.integral_mul_const]
  exact div_self (compactPacketRawMass_pos ε).ne'

theorem support_compactPacketDensity (ε : ℝ) :
    Function.support (compactPacketDensity ε) = Metric.ball 0 (compactPacketBump ε).rOut := by
  change Function.support (fun t => compactPacketDensity ε t) = _
  simp_rw [compactPacketDensity_eq]
  ext t
  simp only [Function.mem_support, ne_eq, div_eq_zero_iff]
  have hb : compactPacketBump ε t ≠ 0 ↔
      t ∈ Metric.ball 0 (compactPacketBump ε).rOut := by
    change t ∈ Function.support (compactPacketBump ε) ↔ _
    rw [(compactPacketBump ε).support_eq]
  simpa [compactPacketRawMass_pos ε |>.ne'] using hb

theorem continuous_compactPacketDensity (ε : ℝ) : Continuous (compactPacketDensity ε) := by
  unfold compactPacketDensity compactPacketAmplitude
  exact ((compactPacketBump ε).continuous.div_const _).pow 2

theorem contDiff_compactPacketDensity (ε : ℝ) :
    ContDiff ℝ ∞ (compactPacketDensity ε) := by
  unfold compactPacketDensity compactPacketAmplitude
  exact ((compactPacketBump ε).contDiff.div_const _).pow 2

theorem hasCompactSupport_compactPacketDensity (ε : ℝ) :
    HasCompactSupport (compactPacketDensity ε) := by
  have hc := (compactPacketBump ε).hasCompactSupport
  rw [HasCompactSupport, tsupport] at hc ⊢
  rw [(compactPacketBump ε).support_eq] at hc
  rw [support_compactPacketDensity]
  exact hc

theorem integrable_compactPacketDensity (ε : ℝ) : Integrable (compactPacketDensity ε) := by
  exact (continuous_compactPacketDensity ε).integrable_of_hasCompactSupport
    (hasCompactSupport_compactPacketDensity ε)

theorem contDiff_compactPacketAmplitude (ε : ℝ) :
    ContDiff ℝ ∞ (compactPacketAmplitude ε) := by
  unfold compactPacketAmplitude
  exact (compactPacketBump ε).contDiff.div_const _

theorem hasCompactSupport_compactPacketAmplitude (ε : ℝ) :
    HasCompactSupport (compactPacketAmplitude ε) := by
  have hsqrt : Real.sqrt (compactPacketRawMass ε) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (compactPacketRawMass_pos ε))
  have hsupp : Function.support (compactPacketAmplitude ε) =
      Function.support (compactPacketBump ε) := by
    ext t
    simp [compactPacketAmplitude, Function.mem_support, hsqrt]
  have hc := (compactPacketBump ε).hasCompactSupport
  rw [HasCompactSupport, tsupport] at hc ⊢
  rw [hsupp]
  exact hc

theorem integrable_sq_deriv_compactPacketAmplitude (ε : ℝ) :
    Integrable (fun t : ℝ => deriv (compactPacketAmplitude ε) t ^ 2) := by
  have hC1 : ContDiff ℝ 1 (compactPacketAmplitude ε) :=
    (contDiff_compactPacketAmplitude ε).of_le (by exact_mod_cast le_top)
  have hcont : Continuous (deriv (compactPacketAmplitude ε)) :=
    hC1.continuous_deriv le_rfl
  have hcderiv : HasCompactSupport (deriv (compactPacketAmplitude ε)) :=
    (hasCompactSupport_compactPacketAmplitude ε).deriv
  have hcsq : HasCompactSupport (fun t : ℝ => deriv (compactPacketAmplitude ε) t ^ 2) := by
    have hcmul : HasCompactSupport
        (fun t : ℝ => deriv (compactPacketAmplitude ε) t *
          deriv (compactPacketAmplitude ε) t) := hcderiv.mul_right
    simpa [pow_two] using hcmul
  exact (hcont.pow 2).integrable_of_hasCompactSupport hcsq

structure CompactPacketFirstDerivativeData (ε : ℝ) : Prop where
  smooth : ContDiff ℝ ∞ (compactPacketAmplitude ε)
  compactSupport : HasCompactSupport (compactPacketAmplitude ε)
  amplitude_sq_integrable : Integrable (fun t : ℝ => compactPacketAmplitude ε t ^ 2)
  normalized : (∫ t : ℝ, compactPacketAmplitude ε t ^ 2) = 1
  derivative_sq_integrable :
    Integrable (fun t : ℝ => deriv (compactPacketAmplitude ε) t ^ 2)

theorem compactPacket_firstDerivativeData (ε : ℝ) :
    CompactPacketFirstDerivativeData ε where
  smooth := contDiff_compactPacketAmplitude ε
  compactSupport := hasCompactSupport_compactPacketAmplitude ε
  amplitude_sq_integrable := by
    change Integrable (compactPacketDensity ε)
    exact integrable_compactPacketDensity ε
  normalized := by
    change (∫ t : ℝ, compactPacketDensity ε t) = 1
    exact integral_compactPacketDensity ε
  derivative_sq_integrable := integrable_sq_deriv_compactPacketAmplitude ε

theorem tendsto_support_compactPacketDensity_smallSets :
    Tendsto (fun ε : ℝ => Function.support (compactPacketDensity ε))
      (𝓝[>] 0) (𝓝 (0 : ℝ)).smallSets := by
  rw [tendsto_smallSets_iff]
  intro s hs
  rw [Metric.mem_nhds_iff] at hs
  obtain ⟨δ, hδ, hball⟩ := hs
  filter_upwards [(tendsto_compactPacketBump_rOut.eventually
    (Metric.ball_mem_nhds 0 hδ))] with ε hε
  rw [support_compactPacketDensity]
  have hr : (compactPacketBump ε).rOut < δ := by
    simpa [Real.dist_eq, abs_of_nonneg (compactPacketBump ε).rOut_pos.le] using hε
  exact (Metric.ball_subset_ball hr.le).trans hball

def compactPacketAverage (ε : ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  compactPacketDensity ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u

theorem compactPacketAverage_tendsto {u : ℝ → ℝ} (hu : Continuous u) (x : ℝ) :
    Tendsto (fun ε : ℝ => compactPacketAverage ε u x) (𝓝[>] 0) (𝓝 (u x)) := by
  exact MeasureTheory.convolution_tendsto_right
    (φ := fun ε : ℝ => compactPacketDensity ε) (g := fun _ => u) (k := fun _ => x)
    (Eventually.of_forall (compactPacketDensity_nonneg · ·))
    (Eventually.of_forall integral_compactPacketDensity)
    tendsto_support_compactPacketDensity_smallSets
    (Eventually.of_forall fun _ => hu.aestronglyMeasurable)
    ((hu.tendsto x).comp tendsto_snd) tendsto_const_nhds

theorem hasCompactSupport_iteratedDeriv_real_wignerSmithFiniteResolutionLawEscape {u : ℝ → ℝ}
    (hu : HasCompactSupport u) (k : ℕ) : HasCompactSupport (iteratedDeriv k u) := by
  induction k with
  | zero => simpa [iteratedDeriv_zero] using hu
  | succ k ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

theorem contDiff_one_iteratedDeriv_real {u : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (k : ℕ) : ContDiff ℝ 1 (iteratedDeriv k u) := by
  have hk : ContDiff ℝ (k + 1 : ℕ) u := hu.of_le (by exact_mod_cast le_top)
  exact (contDiff_nat_succ_iff_contDiff_one_iteratedDeriv.mp hk).2

theorem deriv_compactPacketAverage (ε : ℝ) {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) :
    deriv (compactPacketAverage ε u) = compactPacketAverage ε (deriv u) := by
  funext x
  have hρC1 : ContDiff ℝ 1 (compactPacketDensity ε) :=
    (contDiff_compactPacketDensity ε).of_le (by exact_mod_cast le_top)
  have hρderiv : ∀ t, HasDerivAt (compactPacketDensity ε)
      (deriv (compactPacketDensity ε) t) t := fun t =>
    (hρC1.differentiable (by norm_num) t).hasDerivAt
  have hushift : ∀ t, HasDerivAt (fun s : ℝ => u (x - s))
      (-deriv u (x - t)) t := by
    intro t
    have hut : HasDerivAt u (deriv u (x - t)) (x - t) :=
      (hu.differentiable (by norm_num) (x - t)).hasDerivAt
    exact hut.comp_const_sub x t
  have hρcont : Continuous (compactPacketDensity ε) := hρC1.continuous
  have hρdcont : Continuous (deriv (compactPacketDensity ε)) :=
    hρC1.continuous_deriv le_rfl
  have hucont : Continuous u := hu.continuous
  have hudcont : Continuous (deriv u) := hu.continuous_deriv le_rfl
  have hρv' : Integrable
      (fun t => compactPacketDensity ε t * (-deriv u (x - t))) := by
    have hcont : Continuous
        (fun t => compactPacketDensity ε t * (-deriv u (x - t))) :=
      hρcont.mul ((hudcont.comp (continuous_const.sub continuous_id)).neg)
    have hc : HasCompactSupport
        (fun t => compactPacketDensity ε t * (-deriv u (x - t))) :=
      (hasCompactSupport_compactPacketDensity ε).mul_right
    exact hcont.integrable_of_hasCompactSupport hc
  have hρ'v : Integrable
      (fun t => deriv (compactPacketDensity ε) t * u (x - t)) := by
    have hcont : Continuous
        (fun t => deriv (compactPacketDensity ε) t * u (x - t)) :=
      hρdcont.mul (hucont.comp (continuous_const.sub continuous_id))
    have hcderiv : HasCompactSupport (deriv (compactPacketDensity ε)) :=
      (hasCompactSupport_compactPacketDensity ε).deriv
    have hc : HasCompactSupport
        (fun t => deriv (compactPacketDensity ε) t * u (x - t)) := hcderiv.mul_right
    exact hcont.integrable_of_hasCompactSupport hc
  have hρv : Integrable
      (fun t => compactPacketDensity ε t * u (x - t)) := by
    have hcont : Continuous
        (fun t => compactPacketDensity ε t * u (x - t)) :=
      hρcont.mul (hucont.comp (continuous_const.sub continuous_id))
    have hc : HasCompactSupport
        (fun t => compactPacketDensity ε t * u (x - t)) :=
      (hasCompactSupport_compactPacketDensity ε).mul_right
    exact hcont.integrable_of_hasCompactSupport hc
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun t _ => hρderiv t) (fun t _ => hushift t) hρv' hρ'v hρv
  have heq :
      (∫ t : ℝ, deriv (compactPacketDensity ε) t * u (x - t)) =
        ∫ t : ℝ, compactPacketDensity ε t * deriv u (x - t) := by
    have hneg :
        (∫ t : ℝ, compactPacketDensity ε t * (-deriv u (x - t))) =
          -(∫ t : ℝ, compactPacketDensity ε t * deriv u (x - t)) := by
      rw [show (fun t : ℝ => compactPacketDensity ε t * (-deriv u (x - t))) =
          fun t => -(compactPacketDensity ε t * deriv u (x - t)) by
        funext t
        ring,
        integral_neg]
    rw [hneg] at hibp
    linarith
  have hconv :
      ((deriv (compactPacketDensity ε)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x =
        (compactPacketDensity ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] deriv u) x := by
    simpa only [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply,
      smul_eq_mul] using heq
  have hleft := (hasCompactSupport_compactPacketDensity ε).hasDerivAt_convolution_left
    (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ) hρC1 hu.continuous.locallyIntegrable x
  change deriv
      (compactPacketDensity ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x =
    (compactPacketDensity ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] deriv u) x
  rw [hleft.deriv]
  exact hconv

theorem iteratedDeriv_compactPacketAverage (ε : ℝ) {u : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (k : ℕ) :
    iteratedDeriv k (compactPacketAverage ε u) =
      compactPacketAverage ε (iteratedDeriv k u) := by
  induction k with
  | zero => simp [iteratedDeriv_zero]
  | succ k ih =>
      rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
      exact deriv_compactPacketAverage ε (contDiff_one_iteratedDeriv_real hu k)

theorem iteratedDeriv_compactPacketAverage_tendsto {u : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (k : ℕ) (x : ℝ) :
    Tendsto (fun ε : ℝ => iteratedDeriv k (compactPacketAverage ε u) x)
      (𝓝[>] 0) (𝓝 (iteratedDeriv k u x)) := by
  have h := compactPacketAverage_tendsto
    (hu.continuous_iteratedDeriv k (by exact_mod_cast le_top)) x
  simpa only [iteratedDeriv_compactPacketAverage _ hu k] using h

def compactPacketSampledJet {n m : ℕ} (u : ℝ → ℝ) (E : Fin m → ℝ) (ε : ℝ) :
    Fin m → Fin n → ℝ :=
  fun j i => iteratedDeriv (i : ℕ) (compactPacketAverage ε u) (E j)

def trueSampledJet {n m : ℕ} (u : ℝ → ℝ) (E : Fin m → ℝ) :
    Fin m → Fin n → ℝ :=
  fun j i => iteratedDeriv (i : ℕ) u (E j)

theorem compactPacketSampledJet_tendsto {n m : ℕ} {u : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (E : Fin m → ℝ) :
    Tendsto (compactPacketSampledJet (n := n) u E) (𝓝[>] 0)
      (𝓝 (trueSampledJet (n := n) u E)) := by
  rw [tendsto_pi_nhds]
  intro j
  rw [tendsto_pi_nhds]
  intro i
  exact iteratedDeriv_compactPacketAverage_tendsto hu i (E j)

theorem compactPacket_eventually_injMod_pos {n m N : ℕ} [Nonempty (Fin N)]
    (e : Fin N → (Fin n → ℕ)) {u : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (E : Fin m → ℝ)
    (hinj : Function.Injective (measCLM e (trueSampledJet (n := n) u E))) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < injMod (measCLM e (compactPacketSampledJet (n := n) u E ε)) :=
  measCLM_eventually_injMod_pos e hinj (compactPacketSampledJet_tendsto hu E)

theorem span_realEvaluationVectors_eq_top
    {ι X : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → X → ℝ) (hf : LinearIndependent ℝ f) :
    Submodule.span ℝ (Set.range fun x : X => fun i => f i x) = ⊤ := by
  let K : Submodule ℝ (ι → ℝ) :=
    Submodule.span ℝ (Set.range fun x : X => fun i => f i x)
  change K = ⊤
  rw [← Submodule.dualAnnihilator_eq_bot_iff]
  rw [Submodule.eq_bot_iff]
  intro φ hφ
  have hvanish : ∀ x : X, φ (fun i => f i x) = 0 := by
    intro x
    exact (Submodule.mem_dualAnnihilator φ).mp hφ _
      (Submodule.subset_span (Set.mem_range_self x))
  let c : ι → ℝ := fun i => φ (fun j => if i = j then 1 else 0)
  have hcomb : ∑ i, c i • f i = 0 := by
    funext x
    have hsum := LinearMap.pi_apply_eq_sum_univ φ (fun i => f i x)
    rw [hvanish x] at hsum
    simpa [c, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using hsum.symm
  have hc : ∀ i, c i = 0 :=
    (Fintype.linearIndependent_iff.mp hf) c hcomb
  apply LinearMap.ext
  intro v
  rw [LinearMap.pi_apply_eq_sum_univ φ v]
  have hφbasis : ∀ i, φ (fun j => if i = j then 1 else 0) = 0 := by
    simpa [c] using hc
  simp [hφbasis]

theorem exists_fullRank_real_evaluation_packet
    {ι X : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → X → ℝ) (hf : LinearIndependent ℝ f) :
    ∃ points : ι → X,
      IsUnit (Matrix.of fun a i => f i (points a) : Matrix ι ι ℝ) := by
  have hspan := span_realEvaluationVectors_eq_top f hf
  obtain ⟨v, hv_range, hv_span, hv_indep⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ
      (Set.range fun x : X => fun i : ι => f i x)
  have hfinrank : Module.finrank ℝ
      (Submodule.span ℝ (Set.range fun x : X => fun i : ι => f i x)) = Fintype.card ι := by
    rw [hspan, finrank_top, Module.finrank_pi]
  let eqv : Fin (Module.finrank ℝ
      (Submodule.span ℝ (Set.range fun x : X => fun i : ι => f i x))) ≃ ι :=
    (finCongr hfinrank).trans (Fintype.equivFin ι).symm
  let v' : ι → (ι → ℝ) := v ∘ eqv.symm
  have hv'_range : ∀ i, v' i ∈ Set.range fun x : X => fun j : ι => f j x := by
    intro i
    exact hv_range (eqv.symm i)
  have hv'_indep : LinearIndependent ℝ v' :=
    hv_indep.comp _ eqv.symm.injective
  choose points hpoints using hv'_range
  refine ⟨points, ?_⟩
  rw [← Matrix.linearIndependent_rows_iff_isUnit]
  have hrow :
      (Matrix.of fun a i => f i (points a) : Matrix ι ι ℝ).row = v' := by
    funext a i
    simpa using congrFun (hpoints a) i
  rw [hrow]
  exact hv'_indep

def lawMonomial {n N : ℕ} (e : Fin N → (Fin n → ℕ))
    (g : Fin n → (ℝ → ℝ)) (k : Fin N) (x : ℝ) : ℝ :=
  ∏ i, (g i x) ^ (e k i)

theorem measCLM_eq_lawMonomial_mulVec {n N : ℕ}
    (e : Fin N → (Fin n → ℕ)) (g : Fin n → (ℝ → ℝ)) (E : Fin N → ℝ)
    (c : Fin N → ℝ) :
    measCLM e (fun j i => g i (E j)) c =
      (Matrix.of fun j k => lawMonomial e g k (E j)).mulVec c := by
  ext j
  simp [measCLM, Matrix.mulVec, dotProduct, lawMonomial, mul_comm]

theorem exists_sample_injective_measCLM_of_linearIndependent {n N : ℕ}
    (e : Fin N → (Fin n → ℕ)) (g : Fin n → (ℝ → ℝ))
    (hlin : LinearIndependent ℝ (lawMonomial e g)) :
    ∃ E : Fin N → ℝ, Function.Injective (measCLM e (fun j i => g i (E j))) := by
  obtain ⟨E, hunit⟩ := exists_fullRank_real_evaluation_packet (lawMonomial e g) hlin
  refine ⟨E, fun c d hcd => ?_⟩
  have hmul :
      (Matrix.of fun j k => lawMonomial e g k (E j)).mulVec c =
        (Matrix.of fun j k => lawMonomial e g k (E j)).mulVec d := by
    simpa only [← measCLM_eq_lawMonomial_mulVec] using hcd
  exact (Matrix.mulVec_injective_iff_isUnit.mpr hunit) hmul

theorem lawEmbed_injective_of_injective {n N : ℕ}
    {e : Fin N → (Fin n →₀ ℕ)} (he : Function.Injective e) :
    Function.Injective (lawEmbed e) := by
  intro c d hcd
  have hc : lawEmbed e (c - d) = 0 := by
    rw [map_sub, hcd, sub_self]
  funext k
  have hcoeff := congrArg (MvPolynomial.coeff (e k)) hc
  simp only [lawEmbed, LinearMap.coe_mk, AddHom.coe_mk, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial, mul_boole,
    MvPolynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single k] at hcoeff
  · exact sub_eq_zero.mp (by simpa using hcoeff)
  · intro j _ hj
    simp [he.ne hj]
  · simp

def lawMonomialFinsupp {n N : ℕ} (e : Fin N → (Fin n →₀ ℕ))
    (g : Fin n → (ℝ → ℝ)) (k : Fin N) (x : ℝ) : ℝ :=
  ∏ i, (g i x) ^ (e k i)

theorem linearIndependent_lawMonomialFinsupp_of_jetEval_injective {n N : ℕ}
    {e : Fin N → (Fin n →₀ ℕ)} (he : Function.Injective e)
    {g : Fin n → (ℝ → ℝ)} (hg : Function.Injective (jetEval g)) :
    LinearIndependent ℝ (lawMonomialFinsupp e g) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hembed : lawEmbed e c = 0 := by
    apply hg
    funext x
    have hx := congrFun hc x
    simp only [jetEval_apply, lawEmbed, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
      map_mul, eval_C, eval_monomial, one_mul, map_zero]
    simpa [lawMonomialFinsupp, Finset.sum_apply, Finsupp.prod_fintype] using hx
  have hzero := (lawEmbed_injective_of_injective he)
    (show lawEmbed e c = lawEmbed e 0 by simpa using hembed)
  exact fun i => congrFun hzero i

theorem exists_sample_injective_measCLM_of_jetEval_injective {n N : ℕ}
    {e : Fin N → (Fin n →₀ ℕ)} (he : Function.Injective e)
    {g : Fin n → (ℝ → ℝ)} (hg : Function.Injective (jetEval g)) :
    ∃ E : Fin N → ℝ,
      Function.Injective (measCLM (fun k i => e k i) (fun j i => g i (E j))) := by
  have hlin : LinearIndependent ℝ (lawMonomial (fun k i => e k i) g) := by
    change LinearIndependent ℝ (lawMonomialFinsupp e g)
    exact linearIndependent_lawMonomialFinsupp_of_jetEval_injective he hg
  exact exists_sample_injective_measCLM_of_linearIndependent _ _ hlin

def wignerSmithFiniteJet (r : ℕ) (u : ℝ → ℝ) : Fin (r + 2) → (ℝ → ℝ) :=
  fun i => Fin.cases (fun x : ℝ => x)
    (fun j x => iteratedDeriv (j : ℕ) u x) i

def compactPacketWignerSmithFiniteJet (r : ℕ) (u : ℝ → ℝ) (ε : ℝ) :
    Fin (r + 2) → (ℝ → ℝ) :=
  fun i => Fin.cases (fun x : ℝ => x)
    (fun j x => iteratedDeriv (j : ℕ) (compactPacketAverage ε u) x) i

theorem compactPacketWignerSmithFiniteJet_sample_tendsto {r m : ℕ} {u : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (E : Fin m → ℝ) :
    Tendsto
      (fun ε j i => compactPacketWignerSmithFiniteJet r u ε i (E j))
      (𝓝[>] (0 : ℝ))
      (𝓝 (fun j i => wignerSmithFiniteJet r u i (E j))) := by
  rw [tendsto_pi_nhds]
  intro j
  rw [tendsto_pi_nhds]
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · exact tendsto_const_nhds
  · exact iteratedDeriv_compactPacketAverage_tendsto hu k (E j)

/-- Every fixed finite monomial law window admits finitely many center energies at which the
normalized squared-bump packet measurements eventually have a positive deterministic noise margin.
The convergence is derived from the concrete packet, not assumed. -/
theorem exists_compactPacket_finiteResolution_lawEscape {r N : ℕ} [Nonempty (Fin N)]
    {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    {e : Fin N → (Fin (r + 2) →₀ ℕ)} (he : Function.Injective e)
    (hHT : Function.Injective (jetEval (wignerSmithFiniteJet r u))) :
    ∃ E : Fin N → ℝ,
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        let A := measCLM (fun k i => e k i)
          (fun j i => compactPacketWignerSmithFiniteJet r u ε i (E j))
        0 < injMod A ∧ ∀ c : Fin N → ℝ, injMod A * ‖c‖ ≤ ‖A c‖ := by
  obtain ⟨E, hinj⟩ := exists_sample_injective_measCLM_of_jetEval_injective he hHT
  refine ⟨E, ?_⟩
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < injMod (measCLM (fun k i => e k i)
        (fun j i => compactPacketWignerSmithFiniteJet r u ε i (E j))) :=
    measCLM_eventually_injMod_pos (fun k i => e k i) hinj
      (compactPacketWignerSmithFiniteJet_sample_tendsto hu E)
  filter_upwards [hpos] with ε hε
  exact ⟨hε, fun c => injMod_mul_norm_le _ c⟩

def compactPacketComplexAmplitude (ε t : ℝ) : ℂ :=
  compactPacketAmplitude ε t

def compactPacketComplexEnergyDerivative (ε t : ℝ) : ℂ :=
  -deriv (compactPacketAmplitude ε) t

theorem continuous_compactPacketComplexAmplitude (ε : ℝ) :
    Continuous (compactPacketComplexAmplitude ε) := by
  exact Complex.ofRealCLM.continuous.comp (contDiff_compactPacketAmplitude ε).continuous

theorem continuous_compactPacketComplexEnergyDerivative (ε : ℝ) :
    Continuous (compactPacketComplexEnergyDerivative ε) := by
  have hC1 : ContDiff ℝ 1 (compactPacketAmplitude ε) :=
    (contDiff_compactPacketAmplitude ε).of_le (by exact_mod_cast le_top)
  exact (Complex.ofRealCLM.continuous.comp (hC1.continuous_deriv le_rfl)).neg

theorem hasCompactSupport_compactPacketComplexAmplitude (ε : ℝ) :
    HasCompactSupport (compactPacketComplexAmplitude ε) := by
  have h := (hasCompactSupport_compactPacketAmplitude ε).comp_left
    (g := fun r : ℝ => (r : ℂ)) rfl
  change HasCompactSupport (fun t : ℝ => (compactPacketAmplitude ε t : ℂ))
  exact h

theorem hasDerivAt_compactPacketComplexAmplitude (ε t : ℝ) :
    HasDerivAt (compactPacketComplexAmplitude ε)
      (-compactPacketComplexEnergyDerivative ε t) t := by
  have hC1 : ContDiff ℝ 1 (compactPacketAmplitude ε) :=
    (contDiff_compactPacketAmplitude ε).of_le (by exact_mod_cast le_top)
  have hreal : HasDerivAt (compactPacketAmplitude ε)
      (deriv (compactPacketAmplitude ε) t) t :=
    (hC1.differentiable (by norm_num) t).hasDerivAt
  simpa only [compactPacketComplexAmplitude, compactPacketComplexEnergyDerivative,
    Function.comp_def, Complex.ofRealCLM_apply, neg_neg] using!
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hreal

theorem integrable_scalarTimePairing_of_continuous_of_compact
    {ψ ψ' : ℝ → ℂ} (hψ : Continuous ψ) (hψ' : Continuous ψ')
    (hψc : HasCompactSupport ψ) :
    Integrable (scalarTimePairingIntegrand ψ ψ') := by
  have hcont : Continuous (scalarTimePairingIntegrand ψ ψ') := by
    unfold scalarTimePairingIntegrand
    fun_prop
  have hcstar : HasCompactSupport (fun t => star (ψ t)) := by
    have h := hψc.comp_left (g := fun z : ℂ => star z) (star_zero ℂ)
    simpa [Function.comp_def] using h
  have hc : HasCompactSupport (scalarTimePairingIntegrand ψ ψ') := by
    unfold scalarTimePairingIntegrand
    exact hcstar.mul_right
  exact hcont.integrable_of_hasCompactSupport hc

def compactPacketCenteredAmplitude (ε x E : ℝ) : ℂ :=
  compactPacketComplexAmplitude ε (x - E)

def compactPacketCenteredAmplitudeDerivative (ε x E : ℝ) : ℂ :=
  compactPacketComplexEnergyDerivative ε (x - E)

theorem hasDerivAt_compactPacketCenteredAmplitude (ε x E : ℝ) :
    HasDerivAt (compactPacketCenteredAmplitude ε x)
      (compactPacketCenteredAmplitudeDerivative ε x E) E := by
  change HasDerivAt (fun y : ℝ => compactPacketComplexAmplitude ε (x - y))
    (compactPacketComplexEnergyDerivative ε (x - E)) E
  simpa only [neg_neg] using
    (hasDerivAt_compactPacketComplexAmplitude ε (x - E)).comp_const_sub x E

theorem hasCompactSupport_compactPacketCenteredAmplitude (ε x : ℝ) :
    HasCompactSupport (compactPacketCenteredAmplitude ε x) := by
  have hisom : Isometry (fun E : ℝ => x - E) := by
    apply Isometry.of_dist_eq
    intro a b
    rw [Real.dist_eq, Real.dist_eq, show (x - a) - (x - b) = b - a by ring,
      abs_sub_comm]
  have h := (hasCompactSupport_compactPacketComplexAmplitude ε).comp_isClosedEmbedding
    hisom.isClosedEmbedding
  change HasCompactSupport (fun E : ℝ => compactPacketComplexAmplitude ε (x - E))
  exact h

theorem hasDerivAt_compactPacketScatteredAmplitude
    (ε x : ℝ) {S S' : ℝ → ℂ} (hSderiv : ∀ E, HasDerivAt S (S' E) E) (E : ℝ) :
    HasDerivAt
      (fun y => S y * compactPacketCenteredAmplitude ε x y)
      (S' E * compactPacketCenteredAmplitude ε x E +
        S E * compactPacketCenteredAmplitudeDerivative ε x E) E :=
  (hSderiv E).mul (hasDerivAt_compactPacketCenteredAmplitude ε x E)

/-- Exact compact-packet Wigner--Smith reporter. The first conjunct certifies that the displayed
scattered derivative is the actual energy derivative; the second identifies its time-pairing
difference with the concrete squared-bump convolution of the delay. -/
theorem compactPacket_timePairing_eq_average
    (ε x : ℝ) {S S' : ℝ → ℂ} {Q : ℝ → ℝ}
    (hS : Continuous S) (hS' : Continuous S')
    (hSderiv : ∀ E, HasDerivAt S (S' E) E)
    (hunit : ∀ E : ℝ, star (S E) * S E = 1)
    (hQ : ∀ E : ℝ, scalarWignerSmithDelay S S' E = Q E) :
    (∀ E, HasDerivAt
      (fun y => S y * compactPacketCenteredAmplitude ε x y)
      (S' E * compactPacketCenteredAmplitude ε x E +
        S E * compactPacketCenteredAmplitudeDerivative ε x E) E) ∧
    ((∫ E : ℝ, scalarTimePairingIntegrand
        (fun y => S y * compactPacketCenteredAmplitude ε x y)
        (fun y => S' y * compactPacketCenteredAmplitude ε x y +
          S y * compactPacketCenteredAmplitudeDerivative ε x y) E) -
      ∫ E : ℝ, scalarTimePairingIntegrand
        (compactPacketCenteredAmplitude ε x)
        (compactPacketCenteredAmplitudeDerivative ε x) E =
      (compactPacketAverage ε Q x : ℂ)) := by
  refine ⟨hasDerivAt_compactPacketScatteredAmplitude ε x hSderiv, ?_⟩
  have hcenter : Continuous (compactPacketCenteredAmplitude ε x) :=
    (continuous_compactPacketComplexAmplitude ε).comp
      (continuous_const.sub continuous_id)
  have hcenter' : Continuous (compactPacketCenteredAmplitudeDerivative ε x) :=
    (continuous_compactPacketComplexEnergyDerivative ε).comp
      (continuous_const.sub continuous_id)
  have hψ : Continuous
      (fun E => S E * compactPacketCenteredAmplitude ε x E) := hS.mul hcenter
  have hψ' : Continuous
      (fun E => S' E * compactPacketCenteredAmplitude ε x E +
        S E * compactPacketCenteredAmplitudeDerivative ε x E) :=
    (hS'.mul hcenter).add (hS.mul hcenter')
  have hψc : HasCompactSupport
      (fun E => S E * compactPacketCenteredAmplitude ε x E) :=
    (hasCompactSupport_compactPacketCenteredAmplitude ε x).mul_left
  have hscattered := integrable_scalarTimePairing_of_continuous_of_compact hψ hψ' hψc
  have hfree := integrable_scalarTimePairing_of_continuous_of_compact hcenter hcenter'
    (hasCompactSupport_compactPacketCenteredAmplitude ε x)
  have hpair := scalarWignerSmith_timePairing_integral MeasurableSet.univ
    (fun E _ => hunit E) hscattered.integrableOn hfree.integrableOn
  simp only [Measure.restrict_univ] at hpair
  rw [hpair]
  calc
    (∫ E : ℝ, star (compactPacketCenteredAmplitude ε x E) *
        compactPacketCenteredAmplitude ε x E * scalarWignerSmithDelay S S' E) =
        ∫ E : ℝ, ((compactPacketDensity ε (x - E) * Q E : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with E
      rw [hQ]
      simp only [compactPacketCenteredAmplitude, compactPacketComplexAmplitude,
        Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]
      norm_cast
      simp [compactPacketDensity, pow_two]
    _ = ((∫ E : ℝ, compactPacketDensity ε (x - E) * Q E : ℝ) : ℂ) :=
      _root_.integral_ofReal
    _ = (compactPacketAverage ε Q x : ℂ) := by
      rw [compactPacketAverage, MeasureTheory.convolution_lsmul_swap]
      rfl

end

end GaloisForLFunctions.HTGeometry
