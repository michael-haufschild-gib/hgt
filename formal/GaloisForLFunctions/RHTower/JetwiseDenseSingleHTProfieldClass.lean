import GaloisForLFunctions.RHTower.CenteredRealEvenNonzeroJetDensity
import GaloisForLFunctions.RHTower.DeBrangesExplicitGammaGauge
import GaloisForLFunctions.RHTower.EnvelopeJetAgreement
import GaloisForLFunctions.HTGeometry.TranslationPowerProfield
import GaloisForLFunctions.HTGeometry.FiniteOrderZeroFreeDifferentialAlgebraic
import GaloisForLFunctions.HTGeometry.MulPolynomialInvariance

/-!
# Jetwise density of one symmetric hypertranscendental profield class

This module centers the explicit reciprocal-gamma gauge at the critical point,
proves that its nonzero real-even polynomial orbit is hypertranscendental and
has one exact translation-power profield, and proves compact-open density of
that orbit inside every compatible finite-jet fiber. Consequently every
continuous selector determined by the complete profield is constant.
-/

open Complex Filter Set Topology Polynomial Function
open scoped BigOperators

namespace GaloisForLFunctions.RHTower

open HTGeometry

noncomputable section

def centeredReciprocalGammaGauge (w : ℂ) : ℂ :=
  deBrangesReciprocalGammaGauge (w + (1 / 2 : ℂ))

theorem deBrangesReciprocalGammaGauge_one_sub (z : ℂ) :
    deBrangesReciprocalGammaGauge (1 - z) = deBrangesReciprocalGammaGauge z := by
  simp [deBrangesReciprocalGammaGauge, deBrangesReciprocalGammaExponent]
  ring_nf

theorem differentiable_centeredReciprocalGammaGauge :
    Differentiable ℂ centeredReciprocalGammaGauge := by
  unfold centeredReciprocalGammaGauge
  exact (analyticOnNhd_univ_iff_differentiable.mp
    analyticOnNhd_deBrangesReciprocalGammaGauge).comp (by fun_prop)

theorem analyticOnNhd_centeredReciprocalGammaGauge :
    AnalyticOnNhd ℂ centeredReciprocalGammaGauge Set.univ :=
  analyticOnNhd_univ_iff_differentiable.mpr differentiable_centeredReciprocalGammaGauge

theorem zeroFree_centeredReciprocalGammaGauge (w : ℂ) :
    centeredReciprocalGammaGauge w ≠ 0 :=
  zeroFree_deBrangesReciprocalGammaGauge _

theorem centeredReciprocalGammaGauge_even (w : ℂ) :
    centeredReciprocalGammaGauge (-w) = centeredReciprocalGammaGauge w := by
  rw [centeredReciprocalGammaGauge, centeredReciprocalGammaGauge]
  rw [show -w + (1 / 2 : ℂ) = 1 - (w + 1 / 2) by ring,
    deBrangesReciprocalGammaGauge_one_sub]

theorem deBrangesReciprocalGammaGauge_conj (z : ℂ) :
    deBrangesReciprocalGammaGauge ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (deBrangesReciprocalGammaGauge z) := by
  simpa [suzukiEntireSharp] using
    (schwarzReal_deBrangesReciprocalGammaGauge ((starRingEnd ℂ) z)).symm

theorem centeredReciprocalGammaGauge_conj (w : ℂ) :
    centeredReciprocalGammaGauge ((starRingEnd ℂ) w) =
      (starRingEnd ℂ) (centeredReciprocalGammaGauge w) := by
  rw [centeredReciprocalGammaGauge, centeredReciprocalGammaGauge]
  rw [show (starRingEnd ℂ) w + (1 / 2 : ℂ) =
    (starRingEnd ℂ) (w + 1 / 2) by
      rw [map_add, map_div₀]
      rw [map_one]
      have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := map_natCast (starRingEnd ℂ) 2
      rw [htwo],
    deBrangesReciprocalGammaGauge_conj]

theorem hypertranscendental_centeredReciprocalGammaGauge :
    Hypertranscendental centeredReciprocalGammaGauge := by
  exact (hypertranscendental_comp_add_const_iff (1 / 2 : ℂ)).mpr
    hypertranscendental_deBrangesReciprocalGammaGauge

theorem not_finiteOrderEnvelope_centeredReciprocalGammaGauge :
    ¬ FiniteOrderEnvelope centeredReciprocalGammaGauge :=
  not_finiteOrderEnvelope_of_zeroFree_of_hypertranscendental
    differentiable_centeredReciprocalGammaGauge
    zeroFree_centeredReciprocalGammaGauge
    hypertranscendental_centeredReciprocalGammaGauge

def centeredGaugePolynomial (P : Polynomial ℂ) (z : ℂ) : ℂ :=
  P.eval z * centeredReciprocalGammaGauge z

theorem differentiable_centeredGaugePolynomial (P : Polynomial ℂ) :
    Differentiable ℂ (centeredGaugePolynomial P) :=
  (Polynomial.differentiable P).mul differentiable_centeredReciprocalGammaGauge

theorem analyticOnNhd_centeredGaugePolynomial (P : Polynomial ℂ) :
    AnalyticOnNhd ℂ (centeredGaugePolynomial P) Set.univ :=
  analyticOnNhd_univ_iff_differentiable.mpr (differentiable_centeredGaugePolynomial P)

theorem hypertranscendental_centeredGaugePolynomial {P : Polynomial ℂ} (hP : P ≠ 0) :
    Hypertranscendental (centeredGaugePolynomial P) := by
  exact hypertranscendental_mul_polynomial
    differentiable_centeredReciprocalGammaGauge.contDiff hP
    hypertranscendental_centeredReciprocalGammaGauge

theorem translationPowerProfield_centeredGaugePolynomial
    {P : Polynomial ℂ} (hP : P ≠ 0) (r : ℕ) :
    translationPowerProfield (centeredGaugePolynomial P)
        (analyticOnNhd_centeredGaugePolynomial P) r =
      translationPowerProfield centeredReciprocalGammaGauge
        analyticOnNhd_centeredReciprocalGammaGauge r := by
  exact translationPowerProfield_mul_polynomial
    analyticOnNhd_centeredReciprocalGammaGauge
    (analyticOnNhd_centeredGaugePolynomial P) hP (fun z => rfl) r

/-- Compact-open centered real-even, Schwarz-real entire-function space. -/
abbrev CenteredRealEvenEntire :=
  {F : _root_.RHTower.DeningerCompactOpenEntire //
    (∀ z, F (-z) = F z) ∧
    (∀ z, F ((starRingEnd ℂ) z) = (starRingEnd ℂ) (F z))}

instance centeredRealEvenEntireCoeFun :
    CoeFun CenteredRealEvenEntire (fun _ => ℂ → ℂ) :=
  ⟨fun F => F.1⟩

def centeredGaugePolynomialEntire (P : Polynomial ℂ) :
    _root_.RHTower.DeningerCompactOpenEntire :=
  _root_.RHTower.deningerCompactOpenOfEntire
    (centeredGaugePolynomial P) (differentiable_centeredGaugePolynomial P)

def centeredGaugeQuotient (F : CenteredRealEvenEntire) (z : ℂ) : ℂ :=
  F z / centeredReciprocalGammaGauge z

theorem differentiable_centeredGaugeQuotient (F : CenteredRealEvenEntire) :
    Differentiable ℂ (centeredGaugeQuotient F) :=
  F.1.2.div differentiable_centeredReciprocalGammaGauge
    zeroFree_centeredReciprocalGammaGauge

theorem centeredGaugeQuotient_even (F : CenteredRealEvenEntire) (z : ℂ) :
    centeredGaugeQuotient F (-z) = centeredGaugeQuotient F z := by
  rw [centeredGaugeQuotient, centeredGaugeQuotient, F.2.1,
    centeredReciprocalGammaGauge_even]

theorem centeredGaugeQuotient_conj (F : CenteredRealEvenEntire) (z : ℂ) :
    centeredGaugeQuotient F ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (centeredGaugeQuotient F z) := by
  rw [centeredGaugeQuotient, centeredGaugeQuotient, F.2.2,
    centeredReciprocalGammaGauge_conj, map_div₀]

theorem tendstoLocallyUniformly_const_function (f : ℂ → ℂ) :
    TendstoLocallyUniformly (fun _ : ℕ => f) f atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  exact Filter.Eventually.of_forall (fun n z hz => by simpa using hepsilon)

/-- Sequence form of jetwise orbit density. Every approximant uses a nonzero real-even polynomial. -/
theorem exists_centeredGaugePolynomial_jetwise_approximation
    {ι : Type*} [Fintype ι]
    (negIdx conjIdx : ι ≃ ι) (a : ι → ℂ) (ha : Function.Injective a)
    (m : ι → ℕ)
    (haneg : ∀ i, a (negIdx i) = -a i)
    (haconj : ∀ i, a (conjIdx i) = (starRingEnd ℂ) (a i))
    (hmneg : ∀ i, m (negIdx i) = m i)
    (hmconj : ∀ i, m (conjIdx i) = m i)
    (F : CenteredRealEvenEntire) :
    ∃ P : ℕ → Polynomial ℂ,
      (∀ n, P n ≠ 0) ∧
      (∀ n z, (P n).eval (-z) = (P n).eval z) ∧
      (∀ n z, (P n).eval ((starRingEnd ℂ) z) =
        (starRingEnd ℂ) ((P n).eval z)) ∧
      (∀ n i k, k < m i →
        iteratedDeriv k (centeredGaugePolynomial (P n)) (a i) =
          iteratedDeriv k (F : ℂ → ℂ) (a i)) ∧
      TendstoLocallyUniformly
        (fun n => centeredGaugePolynomial (P n)) F atTop := by
  let g := centeredGaugeQuotient F
  obtain ⟨P, hPeven, hPconj, hPjets, hPconv⟩ :=
    _root_.RHTower.exists_realEvenPolynomial_compactOpen_approximation_with_finiteJets
      negIdx conjIdx a ha m haneg haconj hmneg hmconj
      (differentiable_centeredGaugeQuotient F)
      (centeredGaugeQuotient_even F) (centeredGaugeQuotient_conj F)
  obtain ⟨Q, hQne, hQeven, hQconj, hQjets, hQconv⟩ :=
    _root_.RHTower.exists_nonzero_realEvenPolynomial_compactOpen_approximation_with_finiteJets
      a m hPeven hPconj hPjets hPconv
  refine ⟨Q, hQne, hQeven, hQconj, ?_, ?_⟩
  · intro n i k hk
    have hpoly : AnalyticAt ℂ (fun z => (Q n).eval z) (a i) :=
      (Polynomial.differentiable (Q n)).analyticAt (a i)
    have hg : AnalyticAt ℂ g (a i) :=
      (differentiable_centeredGaugeQuotient F).analyticAt (a i)
    have hmul := _root_.RHTower.iteratedDeriv_mul_congr
      (analyticOnNhd_centeredReciprocalGammaGauge (a i) (Set.mem_univ _))
      hpoly hg (N := k) (fun j hj => ?_)
    · have hcancel :
          (centeredReciprocalGammaGauge * g) = (F : ℂ → ℂ) := by
        funext z
        simp only [Pi.mul_apply, g, centeredGaugeQuotient]
        exact mul_div_cancel₀ (F z) (zeroFree_centeredReciprocalGammaGauge z)
      rw [hcancel] at hmul
      have hcomm :
          (centeredReciprocalGammaGauge * fun z => (Q n).eval z) =
            centeredGaugePolynomial (Q n) := by
        funext z
        simp [centeredGaugePolynomial, mul_comm]
      rw [hcomm] at hmul
      exact hmul k le_rfl
    · rw [_root_.RHTower.iteratedDeriv_deningerPolynomial_eval]
      exact hQjets n i j (lt_of_le_of_lt hj hk)
  · have hU := tendstoLocallyUniformly_const_function centeredReciprocalGammaGauge
    have hmul := tendstoLocallyUniformly_mul hQconv hU
      (differentiable_centeredGaugeQuotient F).continuous
      differentiable_centeredReciprocalGammaGauge.continuous
    convert hmul using 1
    · funext n z
      rfl
    · funext z
      simp only [centeredGaugeQuotient]
      exact (div_mul_cancel₀ (F z) (zeroFree_centeredReciprocalGammaGauge z)).symm

def centeredGaugePolynomialCentered (P : Polynomial ℂ)
    (heven : ∀ z, P.eval (-z) = P.eval z)
    (hconj : ∀ z, P.eval ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (P.eval z)) : CenteredRealEvenEntire := by
  refine ⟨centeredGaugePolynomialEntire P, ?_, ?_⟩
  · intro z
    change centeredGaugePolynomial P (-z) = centeredGaugePolynomial P z
    rw [centeredGaugePolynomial, centeredGaugePolynomial, heven,
      centeredReciprocalGammaGauge_even]
  · intro z
    change centeredGaugePolynomial P ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (centeredGaugePolynomial P z)
    rw [centeredGaugePolynomial, centeredGaugePolynomial, hconj,
      centeredReciprocalGammaGauge_conj, map_mul]

/-- Symmetric polynomial orbit of the explicit centered gauge. -/
def centeredReciprocalGammaProfieldOrbit : Set CenteredRealEvenEntire :=
  {F | ∃ (P : Polynomial ℂ)
      (heven : ∀ z, P.eval (-z) = P.eval z)
      (hconj : ∀ z, P.eval ((starRingEnd ℂ) z) =
        (starRingEnd ℂ) (P.eval z)),
    P ≠ 0 ∧ F = centeredGaugePolynomialCentered P heven hconj}

theorem deningerCompactOpenOfEntire_tendsto_of_locallyUniform
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hf : ∀ n, Differentiable ℂ (f n)) (hg : Differentiable ℂ g)
    (h : TendstoLocallyUniformly f g atTop) :
    Tendsto (fun n => _root_.RHTower.deningerCompactOpenOfEntire (f n) (hf n)) atTop
      (𝓝 (_root_.RHTower.deningerCompactOpenOfEntire g hg)) := by
  rw [tendsto_subtype_rng]
  apply ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr
  simpa [_root_.RHTower.deningerCompactOpenOfEntire] using h

theorem exists_centeredReciprocalGammaProfieldOrbit_tendsto
    (F : CenteredRealEvenEntire) :
    ∃ u : ℕ → CenteredRealEvenEntire,
      (∀ n, u n ∈ centeredReciprocalGammaProfieldOrbit) ∧
      Tendsto u atTop (𝓝 F) := by
  let a : Fin 0 → ℂ := Fin.elim0
  let m : Fin 0 → ℕ := Fin.elim0
  obtain ⟨P, hPne, hPeven, hPconj, hPjets, hPconv⟩ :=
    exists_centeredGaugePolynomial_jetwise_approximation
      (Equiv.refl (Fin 0)) (Equiv.refl (Fin 0)) a (fun i => Fin.elim0 i) m
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) F
  let u : ℕ → CenteredRealEvenEntire := fun n =>
    centeredGaugePolynomialCentered (P n) (hPeven n) (hPconj n)
  have hsource := deningerCompactOpenOfEntire_tendsto_of_locallyUniform
    (fun n => differentiable_centeredGaugePolynomial (P n)) F.1.2 hPconv
  have hu : Tendsto u atTop (𝓝 F) := by
    rw [tendsto_subtype_rng]
    exact hsource
  refine ⟨u, ?_, hu⟩
  intro n
  exact ⟨P n, hPeven n, hPconj n, hPne n, rfl⟩

/-- The single exact profield orbit is dense in the full centered symmetric Fréchet space. -/
theorem centeredReciprocalGammaProfieldOrbit_dense :
    Dense centeredReciprocalGammaProfieldOrbit := by
  apply dense_iff_closure_eq.mpr
  apply Set.eq_univ_of_forall
  intro F
  obtain ⟨u, huMem, hu⟩ := exists_centeredReciprocalGammaProfieldOrbit_tendsto F
  exact mem_closure_iff_seq_limit.mpr ⟨u, huMem, hu⟩

theorem analyticOnNhd_centeredRealEvenEntire (F : CenteredRealEvenEntire) :
    AnalyticOnNhd ℂ (F : ℂ → ℂ) Set.univ :=
  analyticOnNhd_univ_iff_differentiable.mpr F.1.2

def centeredTranslationPowerProfield (F : CenteredRealEvenEntire) (r : ℕ) :=
  translationPowerProfield (F : ℂ → ℂ) (analyticOnNhd_centeredRealEvenEntire F) r

theorem centeredReciprocalGammaProfieldOrbit_hypertranscendental
    {F : CenteredRealEvenEntire} (hF : F ∈ centeredReciprocalGammaProfieldOrbit) :
    Hypertranscendental (F : ℂ → ℂ) := by
  obtain ⟨P, heven, hconj, hP, rfl⟩ := hF
  exact hypertranscendental_centeredGaugePolynomial hP

theorem centeredReciprocalGammaProfieldOrbit_profield
    {F : CenteredRealEvenEntire} (hF : F ∈ centeredReciprocalGammaProfieldOrbit)
    (r : ℕ) :
    centeredTranslationPowerProfield F r =
      translationPowerProfield centeredReciprocalGammaGauge
        analyticOnNhd_centeredReciprocalGammaGauge r := by
  obtain ⟨P, heven, hconj, hP, rfl⟩ := hF
  simpa [centeredTranslationPowerProfield, centeredGaugePolynomialCentered,
    centeredGaugePolynomialEntire, _root_.RHTower.deningerCompactOpenOfEntire] using
      translationPowerProfield_centeredGaugePolynomial hP r

/-- Compatible finite-jet realization fiber inside the centered symmetric space. -/
abbrev CenteredRealEvenJetFiber {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (m : ι → ℕ)
    (c : _root_.RHTower.FiniteEntireJetCoordinate m → ℂ) :=
  {F : CenteredRealEvenEntire //
    ∀ i (k : Fin (m i)), iteratedDeriv k.1 (F : ℂ → ℂ) (a i) = c ⟨i, k⟩}

def centeredReciprocalGammaProfieldOrbitInJetFiber
    {ι : Type*} [Fintype ι] (a : ι → ℂ) (m : ι → ℕ)
    (c : _root_.RHTower.FiniteEntireJetCoordinate m → ℂ) :
    Set (CenteredRealEvenJetFiber a m c) :=
  {F | F.1 ∈ centeredReciprocalGammaProfieldOrbit}

/-- The same orbit remains dense after any compatible finite jet passport is fixed. -/
theorem centeredReciprocalGammaProfieldOrbitInJetFiber_dense
    {ι : Type*} [Fintype ι]
    (negIdx conjIdx : ι ≃ ι) (a : ι → ℂ) (ha : Function.Injective a)
    (m : ι → ℕ)
    (haneg : ∀ i, a (negIdx i) = -a i)
    (haconj : ∀ i, a (conjIdx i) = (starRingEnd ℂ) (a i))
    (hmneg : ∀ i, m (negIdx i) = m i)
    (hmconj : ∀ i, m (conjIdx i) = m i)
    (c : _root_.RHTower.FiniteEntireJetCoordinate m → ℂ) :
    Dense (centeredReciprocalGammaProfieldOrbitInJetFiber a m c) := by
  apply dense_iff_closure_eq.mpr
  apply Set.eq_univ_of_forall
  intro F
  obtain ⟨P, hPne, hPeven, hPconj, hPjets, hPconv⟩ :=
    exists_centeredGaugePolynomial_jetwise_approximation
      negIdx conjIdx a ha m haneg haconj hmneg hmconj F.1
  let u : ℕ → CenteredRealEvenJetFiber a m c := fun n =>
    ⟨centeredGaugePolynomialCentered (P n) (hPeven n) (hPconj n),
      fun i k => (hPjets n i k.1 k.2).trans (F.2 i k)⟩
  have hsource := deningerCompactOpenOfEntire_tendsto_of_locallyUniform
    (fun n => differentiable_centeredGaugePolynomial (P n)) F.1.1.2 hPconv
  have hcentered : Tendsto (fun n => (u n).1) atTop (𝓝 F.1) := by
    rw [tendsto_subtype_rng]
    exact hsource
  have hu : Tendsto u atTop (𝓝 F) := by
    rw [tendsto_subtype_rng]
    exact hcentered
  apply mem_closure_iff_seq_limit.mpr
  refine ⟨u, ?_, hu⟩
  intro n
  exact ⟨P n, hPeven n, hPconj n, hPne n, rfl⟩

/-- Every compact-open continuous complete-profield selector is constant on a finite jet fiber. -/
theorem continuous_centeredProfieldSelector_constant_on_jetFiber
    {ι : Type*} [Fintype ι]
    (negIdx conjIdx : ι ≃ ι) (a : ι → ℂ) (ha : Function.Injective a)
    (m : ι → ℕ)
    (haneg : ∀ i, a (negIdx i) = -a i)
    (haconj : ∀ i, a (conjIdx i) = (starRingEnd ℂ) (a i))
    (hmneg : ∀ i, m (negIdx i) = m i)
    (hmconj : ∀ i, m (conjIdx i) = m i)
    (c : _root_.RHTower.FiniteEntireJetCoordinate m → ℂ)
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (Phi : CenteredRealEvenJetFiber a m c → Y) (hPhi : Continuous Phi)
    (hprofield : ∀ F G,
      (∀ r, 1 ≤ r →
        centeredTranslationPowerProfield F.1 r =
          centeredTranslationPowerProfield G.1 r) →
      Phi F = Phi G) :
    ∀ F G, Phi F = Phi G := by
  have hdense := centeredReciprocalGammaProfieldOrbitInJetFiber_dense
    negIdx conjIdx a ha m haneg haconj hmneg hmconj c
  intro F G
  letI : Nonempty (CenteredRealEvenJetFiber a m c) := ⟨F⟩
  obtain ⟨O, hO⟩ := hdense.nonempty
  have hEqOn : Set.EqOn Phi (fun _ => Phi O)
      (centeredReciprocalGammaProfieldOrbitInJetFiber a m c) := by
    intro H hH
    apply hprofield H O
    intro r hr
    calc
      centeredTranslationPowerProfield H.1 r =
          translationPowerProfield centeredReciprocalGammaGauge
            analyticOnNhd_centeredReciprocalGammaGauge r :=
        centeredReciprocalGammaProfieldOrbit_profield hH r
      _ = centeredTranslationPowerProfield O.1 r :=
        (centeredReciprocalGammaProfieldOrbit_profield hO r).symm
  have hconst : Phi = fun _ => Phi O := hPhi.ext_on hdense continuous_const hEqOn
  rw [congrFun hconst F, congrFun hconst G]

/-- No-passport specialization: a continuous complete-profield selector is constant on all `X`. -/
theorem continuous_centeredProfieldSelector_constant
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (Phi : CenteredRealEvenEntire → Y) (hPhi : Continuous Phi)
    (hprofield : ∀ F G,
      (∀ r, 1 ≤ r →
        centeredTranslationPowerProfield F r =
          centeredTranslationPowerProfield G r) →
      Phi F = Phi G) :
    ∀ F G, Phi F = Phi G := by
  intro F G
  letI : Nonempty CenteredRealEvenEntire := ⟨F⟩
  obtain ⟨O, hO⟩ := centeredReciprocalGammaProfieldOrbit_dense.nonempty
  have hEqOn : Set.EqOn Phi (fun _ => Phi O) centeredReciprocalGammaProfieldOrbit := by
    intro H hH
    apply hprofield H O
    intro r hr
    calc
      centeredTranslationPowerProfield H r =
          translationPowerProfield centeredReciprocalGammaGauge
            analyticOnNhd_centeredReciprocalGammaGauge r :=
        centeredReciprocalGammaProfieldOrbit_profield hH r
      _ = centeredTranslationPowerProfield O r :=
        (centeredReciprocalGammaProfieldOrbit_profield hO r).symm
  have hconst : Phi = fun _ => Phi O := hPhi.ext_on
    centeredReciprocalGammaProfieldOrbit_dense continuous_const hEqOn
  rw [congrFun hconst F, congrFun hconst G]

end

end GaloisForLFunctions.RHTower
