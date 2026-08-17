import GaloisForLFunctions.RHTower.ProlateIndexedOscillatorUpper
import GaloisForLFunctions.RHTower.ProlateWindowMassLocalBounds
import GaloisForLFunctions.RHTower.ProlateGroundTotalMass
import GaloisForLFunctions.HTGeometry.UltrafilterFamilyLimit
import GaloisForLFunctions.HTGeometry.CompactOperatorDiscreteSpectrum

open Set Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

abbrev ProlatePositiveAperture := {a : ℝ // 0 < a}

def indexedOscillatorBandwidth (a : ProlatePositiveAperture) : ℝ :=
  signedModeRadialBandwidth (a : ℝ)

def indexedOscillatorSeparation (n : ℕ) (a : ProlatePositiveAperture) : ℝ :=
  indexedOscillatorBandwidth a * (signedModeRadialData (a : ℝ) n).s

def indexedOscillatorProfile (n : ℕ) (a : ProlatePositiveAperture) : ℝ → ℝ :=
  normalizedProlateProfile (indexedOscillatorBandwidth a)
    (signedModeRadialData (a : ℝ) n).R

def indexedOscillatorProfileDeriv (n : ℕ) (a : ProlatePositiveAperture) : ℝ → ℝ :=
  normalizedProlateDeriv (indexedOscillatorBandwidth a)
    (signedModeRadialData (a : ℝ) n).R

def indexedOscillatorProfileDeriv2 (n : ℕ) (a : ProlatePositiveAperture) : ℝ → ℝ :=
  normalizedProlateDeriv2 (indexedOscillatorBandwidth a)
    (signedModeRadialData (a : ℝ) n).R

theorem indexedOscillatorBandwidth_pos (a : ProlatePositiveAperture) :
    0 < indexedOscillatorBandwidth a := by
  dsimp [indexedOscillatorBandwidth, signedModeRadialBandwidth]
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (sq_pos_of_pos a.property)

theorem tendsto_prolatePositiveAperture_val_atTop :
    Tendsto (fun a : ProlatePositiveAperture => (a : ℝ)) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  let a₀ : ProlatePositiveAperture := ⟨max (b + 1) 1, by positivity⟩
  filter_upwards [eventually_ge_atTop a₀] with a ha
  change b ≤ (a : ℝ)
  have hbase : b ≤ (a₀ : ℝ) := by
    dsimp [a₀]
    exact le_trans (le_add_of_nonneg_right zero_le_one) (le_max_left _ _)
  exact hbase.trans ha

theorem tendsto_indexedOscillatorBandwidth_atTop :
    Tendsto indexedOscillatorBandwidth atTop atTop :=
  tendsto_signedModeRadialBandwidth_atTop.comp tendsto_prolatePositiveAperture_val_atTop

theorem indexedOscillatorProfile_hasDerivAt (n : ℕ) (a : ProlatePositiveAperture) (x : ℝ) :
    HasDerivAt (indexedOscillatorProfile n a) (indexedOscillatorProfileDeriv n a x) x := by
  exact hasDerivAt_normalizedProlateProfile
    (signedModeRadialData_isExact_of_pos a.property n).2.2.2.2.2.1 x

theorem indexedOscillatorProfileDeriv_hasDerivAt
    (n : ℕ) (a : ProlatePositiveAperture) (x : ℝ) :
    HasDerivAt (indexedOscillatorProfileDeriv n a)
      (indexedOscillatorProfileDeriv2 n a x) x := by
  exact hasDerivAt_normalizedProlateDeriv
    (signedModeRadialData_isExact_of_pos a.property n).2.2.2.2.2.1 x

theorem indexedOscillatorProfile_even (n : ℕ) (a : ProlatePositiveAperture) :
    Function.Even (indexedOscillatorProfile n a) :=
  even_normalizedProlateProfile
    (signedModeRadialData_isExact_of_pos a.property n).2.2.2.2.2.2.1

theorem signedModeRadialData_R_band
    {a : ℝ} (ha : 0 < a) (n : ℕ) : ∀ x : ℝ,
    bandTransform (signedModeRadialBandwidth a) (signedModeRadialData a n).R x =
      evenProlateSignedValue a n ^ 2 * (signedModeRadialData a n).R x := by
  have h := signedModeRadialData_isExact_of_pos ha n
  rw [h.2.2.2.2.1]
  exact bandTransform_endpointNormalize_eigen h.2.2.2.2.2.2.2.2.1

theorem indexedOscillatorProfile_window_package
    (n : ℕ) (a : ProlatePositiveAperture) {K : ℝ} (hK : 0 < K)
    (hcK : 2 * K ^ 2 ≤ indexedOscillatorBandwidth a) :
    (∀ x ∈ Icc (0 : ℝ) K,
      indexedOscillatorProfileDeriv2 n a x =
        rescaledProlateP (indexedOscillatorBandwidth a) (indexedOscillatorSeparation n a) x *
            indexedOscillatorProfile n a x +
          rescaledProlateQ (indexedOscillatorBandwidth a) x *
            indexedOscillatorProfileDeriv n a x) ∧
      indexedOscillatorProfile n a 0 = 1 ∧
      indexedOscillatorProfileDeriv n a 0 = 0 := by
  have hD := signedModeRadialData_isExact_of_pos a.property n
  have hRne : (signedModeRadialData (a : ℝ) n).R ≠ 0 := by
    intro hzero
    have hz := congrFun hzero 1
    rw [hD.2.2.2.2.2.2.2.1] at hz
    exact one_ne_zero hz
  have hpack := normalizedProlate_window_package hK hcK
    hD.2.2.2.2.2.1 hRne hD.2.2.2.2.2.2.1
    (pow_ne_zero 2 (evenProlateSignedValue_ne_zero a.property n))
    (signedModeRadialData_R_band a.property n) hD.2.2.2.2.2.2.2.2.2.1
  simpa [indexedOscillatorProfile, indexedOscillatorProfileDeriv,
    indexedOscillatorProfileDeriv2, indexedOscillatorSeparation,
    indexedOscillatorBandwidth,
    hD.2.2.2.2.2.2.2.2.2.2.1] using hpack.2.2

def indexedOscillatorWindowBound (M K : ℝ) : ℝ :=
  Real.exp (max 1 (hermiteWindowBound K 0 + 2 * (M + 2) + 2) * K)

theorem indexedOscillatorWindowBound_nonneg (M K : ℝ) :
    0 ≤ indexedOscillatorWindowBound M K :=
  (Real.exp_pos _).le

theorem eventually_indexedOscillatorProfile_windowBound
    {L : Filter ProlatePositiveAperture} {M m : ℝ} (hM : 0 ≤ M)
    (n : ℕ) (hmu : Tendsto (indexedOscillatorSeparation n) L (𝓝 m))
    (hm : m ≤ M) (hc : Tendsto indexedOscillatorBandwidth L atTop)
    {K : ℝ} (hK : 0 < K) :
    ∀ᶠ a in L, 0 < indexedOscillatorBandwidth a ∧
      2 * K ^ 2 ≤ indexedOscillatorBandwidth a ∧
      (∀ x ∈ Icc (0 : ℝ) K,
        indexedOscillatorProfileDeriv2 n a x =
          rescaledProlateP (indexedOscillatorBandwidth a)
              (indexedOscillatorSeparation n a) x * indexedOscillatorProfile n a x +
            rescaledProlateQ (indexedOscillatorBandwidth a) x *
              indexedOscillatorProfileDeriv n a x) ∧
      (∀ x ∈ Icc (0 : ℝ) K,
        max |indexedOscillatorProfile n a x| |indexedOscillatorProfileDeriv n a x| ≤
          indexedOscillatorWindowBound M K) ∧
      indexedOscillatorProfile n a 0 = 1 ∧ indexedOscillatorProfileDeriv n a 0 = 0 := by
  have hmUpper : m < M + 1 := by linarith
  have hmuUpper : ∀ᶠ a in L, indexedOscillatorSeparation n a < M + 1 :=
    hmu.eventually (Iio_mem_nhds hmUpper)
  let A : ℝ := max (2 * K ^ 2)
    (max (2 * (K ^ 2 * (K ^ 2 + 1))) (4 * K))
  have hcLarge : ∀ᶠ a in L, A ≤ indexedOscillatorBandwidth a :=
    hc.eventually (eventually_ge_atTop A)
  filter_upwards [hmuUpper, hcLarge] with a hmuA hcA
  have hcpos := indexedOscillatorBandwidth_pos a
  have hcK : 2 * K ^ 2 ≤ indexedOscillatorBandwidth a :=
    (le_max_left _ _).trans hcA
  obtain ⟨hode, hzero, hzero'⟩ := indexedOscillatorProfile_window_package n a hK hcK
  have hmuNonneg : 0 ≤ indexedOscillatorSeparation n a := by
    exact mul_nonneg (indexedOscillatorBandwidth_pos a).le
      (signedModeRadialData_isExact_of_pos a.property n).2.2.2.2.2.2.2.2.2.2.2.1
  have habs : |indexedOscillatorSeparation n a - 1| ≤ M + 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hnum : 2 * (K ^ 2 * (K ^ 2 + 1)) ≤ indexedOscillatorBandwidth a :=
    calc
      2 * (K ^ 2 * (K ^ 2 + 1)) ≤
          max (2 * (K ^ 2 * (K ^ 2 + 1))) (4 * K) := le_max_left _ _
      _ ≤ A := le_max_right _ _
      _ ≤ indexedOscillatorBandwidth a := hcA
  have hfrac : 2 * (K ^ 2 * (K ^ 2 + 1)) / indexedOscillatorBandwidth a ≤ 1 := by
    rw [div_le_one hcpos]
    exact hnum
  have hepsP : prolateWindowEpsP (indexedOscillatorBandwidth a)
      (indexedOscillatorSeparation n a) K 0 ≤ 2 * (M + 2) + 1 := by
    rw [prolateWindowEpsP]
    norm_num
    linarith
  have hfour : 4 * K ≤ indexedOscillatorBandwidth a :=
    calc
      4 * K ≤ max (2 * (K ^ 2 * (K ^ 2 + 1))) (4 * K) := le_max_right _ _
      _ ≤ A := le_max_right _ _
      _ ≤ indexedOscillatorBandwidth a := hcA
  have hepsQ : prolateWindowEpsQ (indexedOscillatorBandwidth a) K ≤ 1 := by
    rw [prolateWindowEpsQ, div_le_one hcpos]
    exact hfour
  have hphase := prolateProfile_window_phase_le (n := 0) hK hcK
    (indexedOscillatorProfile_hasDerivAt n a)
    (indexedOscillatorProfileDeriv_hasDerivAt n a) hode
  refine ⟨hcpos, hcK, hode, ?_, hzero, hzero'⟩
  intro x hx
  have hbase := hphase x hx
  simp only [hzero, hzero', abs_one, abs_zero, max_eq_left zero_le_one,
    one_mul, sub_zero] at hbase
  refine hbase.trans ?_
  rw [indexedOscillatorWindowBound]
  apply Real.exp_le_exp.mpr
  have hrate : max 1 ((hermiteWindowBound K 0 +
      prolateWindowEpsP (indexedOscillatorBandwidth a)
        (indexedOscillatorSeparation n a) K 0) +
      prolateWindowEpsQ (indexedOscillatorBandwidth a) K) ≤
      max 1 (hermiteWindowBound K 0 + 2 * (M + 2) + 2) := by
    apply max_le_max le_rfl
    linarith
  have hboundRateNonneg : 0 ≤ max 1 (hermiteWindowBound K 0 + 2 * (M + 2) + 2) :=
    le_trans zero_le_one (le_max_left _ _)
  exact mul_le_mul hrate hx.2 hx.1 hboundRateNonneg

theorem normalizedProlate_total_mass_le_of_windowPhase
    {c mu chi K B : ℝ} {Phi : ℝ → ℝ}
    (hc : 0 < c) (hK : 0 < K) (hcK : 2 * K ^ 2 ≤ c)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (heven : Function.Even Phi)
    (heig : ∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x)
    (hmuval : mu = c * radialSeparationRatio c chi)
    (hB : ∀ x ∈ Icc (0 : ℝ) K,
      max |normalizedProlateProfile c Phi x| |normalizedProlateDeriv c Phi x| ≤ B) :
    (∫ x in (-Real.sqrt c)..(Real.sqrt c), (normalizedProlateProfile c Phi x) ^ 2) *
        (1 - mu / K ^ 2) ≤ 2 * K * B ^ 2 := by
  have hprofileEven : Function.Even (normalizedProlateProfile c Phi) :=
    even_normalizedProlateProfile heven
  have hBfull : ∀ x ∈ Icc (-K) K, |normalizedProlateProfile c Phi x| ≤ B :=
    abs_le_of_even_window hprofileEven
      (fun x hx => le_trans (le_max_left _ _) (hB x hx))
  have hKS : K ≤ Real.sqrt c := by
    calc
      K = Real.sqrt (K ^ 2) := (Real.sqrt_sq hK.le).symm
      _ ≤ Real.sqrt c := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg K])
  have hmom : (∫ x in (-Real.sqrt c)..(Real.sqrt c),
      x ^ 2 * (normalizedProlateProfile c Phi x) ^ 2) ≤
      mu * ∫ x in (-Real.sqrt c)..(Real.sqrt c),
        (normalizedProlateProfile c Phi x) ^ 2 := by
    rw [hmuval]
    exact normalizedProlate_secondMoment_le hc hsm (fun x _ => heig x)
  exact total_mass_le_of_window_bound hK hKS
    (continuous_normalizedProlateProfile hsm) hBfull hmom

theorem integral_signedModeRadialData_R_mul_eq_zero_of_ne
    {a : ℝ} (ha : 0 < a) {m n : ℕ} (hmn : m ≠ n) :
    (∫ x in (-1 : ℝ)..1,
      (signedModeRadialData a m).R x * (signedModeRadialData a n).R x) = 0 := by
  let fm := bandClass (signedModeRadialData a m).R
    (signedModeRadialData_isExact_of_pos ha m).2.2.2.2.2.1.continuous
  let fn := bandClass (signedModeRadialData a n).R
    (signedModeRadialData_isExact_of_pos ha n).2.2.2.2.2.1.continuous
  have hfmNe : fm ≠ 0 := bandClass_ne_zero_of_global_band_eigen
    (signedModeRadialData_isExact_of_pos ha m).2.2.2.2.2.1.continuous
    (pow_ne_zero 2 (evenProlateSignedValue_ne_zero ha m))
    (by
      intro hzero
      have hz := congrFun hzero 1
      rw [(signedModeRadialData_isExact_of_pos ha m).2.2.2.2.2.2.2.1] at hz
      exact one_ne_zero hz)
    (signedModeRadialData_R_band ha m)
  have hfnNe : fn ≠ 0 := bandClass_ne_zero_of_global_band_eigen
    (signedModeRadialData_isExact_of_pos ha n).2.2.2.2.2.1.continuous
    (pow_ne_zero 2 (evenProlateSignedValue_ne_zero ha n))
    (by
      intro hzero
      have hz := congrFun hzero 1
      rw [(signedModeRadialData_isExact_of_pos ha n).2.2.2.2.2.2.2.1] at hz
      exact one_ne_zero hz)
    (signedModeRadialData_R_band ha n)
  have hfmEig : bandOperatorL2 (signedModeRadialBandwidth a) fm =
      evenProlateSignedValue a m ^ 2 • fm :=
    bandOperatorL2_bandClass_eq_smul_of_global_band_eigen
      (signedModeRadialData_isExact_of_pos ha m).2.2.2.2.2.1.continuous
      (signedModeRadialData_R_band ha m)
  have hfnEig : bandOperatorL2 (signedModeRadialBandwidth a) fn =
      evenProlateSignedValue a n ^ 2 • fn :=
    bandOperatorL2_bandClass_eq_smul_of_global_band_eigen
      (signedModeRadialData_isExact_of_pos ha n).2.2.2.2.2.1.continuous
      (signedModeRadialData_R_band ha n)
  have hvalNe : evenProlateSignedValue a m ^ 2 ≠ evenProlateSignedValue a n ^ 2 :=
    fun h => hmn (evenProlateSignedValue_sq_injective ha h)
  have horth := inner_eq_zero_of_hasEigenvector_of_ne
    (_root_.RHTower.isSymmetric_bandOperatorL2 (signedModeRadialBandwidth a))
    ⟨Module.End.mem_eigenspace_iff.mpr hfmEig, hfmNe⟩
    ⟨Module.End.mem_eigenspace_iff.mpr hfnEig, hfnNe⟩ hvalNe
  rw [show fm = bandClass (signedModeRadialData a m).R
      (signedModeRadialData_isExact_of_pos ha m).2.2.2.2.2.1.continuous from rfl,
    show fn = bandClass (signedModeRadialData a n).R
      (signedModeRadialData_isExact_of_pos ha n).2.2.2.2.2.1.continuous from rfl,
    inner_bandClass_eq] at horth
  exact horth

def indexedOscillatorTotalMass (n : ℕ) (a : ProlatePositiveAperture) : ℝ :=
  ∫ x in (-Real.sqrt (indexedOscillatorBandwidth a))..
      (Real.sqrt (indexedOscillatorBandwidth a)), (indexedOscillatorProfile n a x) ^ 2

def indexedOscillatorSecondMoment (n : ℕ) (a : ProlatePositiveAperture) : ℝ :=
  ∫ x in (-Real.sqrt (indexedOscillatorBandwidth a))..
      (Real.sqrt (indexedOscillatorBandwidth a)),
    x ^ 2 * (indexedOscillatorProfile n a x) ^ 2

theorem indexedOscillatorTotalMass_nonneg (n : ℕ) (a : ProlatePositiveAperture) :
    0 ≤ indexedOscillatorTotalMass n a := by
  rw [indexedOscillatorTotalMass]
  exact intervalIntegral.integral_nonneg
    (neg_le_self (Real.sqrt_nonneg _)) (fun x _ => sq_nonneg _)

theorem indexedOscillatorSecondMoment_le (n : ℕ) (a : ProlatePositiveAperture) :
    indexedOscillatorSecondMoment n a ≤
      indexedOscillatorSeparation n a * indexedOscillatorTotalMass n a := by
  have hD := signedModeRadialData_isExact_of_pos a.property n
  have h := normalizedProlate_secondMoment_le (indexedOscillatorBandwidth_pos a)
    hD.2.2.2.2.2.1 (fun x _ => hD.2.2.2.2.2.2.2.2.2.1 x)
  simpa [indexedOscillatorSecondMoment, indexedOscillatorTotalMass,
    indexedOscillatorProfile, indexedOscillatorSeparation,
    indexedOscillatorBandwidth,
    hD.2.2.2.2.2.2.2.2.2.2.1] using h

theorem integral_indexedOscillatorProfile_mul_eq_zero_of_ne
    (a : ProlatePositiveAperture) {m n : ℕ} (hmn : m ≠ n) :
    (∫ x in (-Real.sqrt (indexedOscillatorBandwidth a))..
        (Real.sqrt (indexedOscillatorBandwidth a)),
      indexedOscillatorProfile m a x * indexedOscillatorProfile n a x) = 0 := by
  exact integral_normalizedProlate_mul_eq_zero (indexedOscillatorBandwidth_pos a)
    (integral_signedModeRadialData_R_mul_eq_zero_of_ne a.property hmn)

theorem false_of_canonicalIndexedProlate_limits_below
    {j : ℕ} {L : Filter ProlatePositiveAperture} [L.NeBot]
    {m : Fin (j + 1) → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hmu : ∀ k : Fin (j + 1),
      Tendsto (indexedOscillatorSeparation (k : ℕ)) L (𝓝 (m k)))
    (hmle : ∀ k, m k ≤ M)
    (hc : Tendsto indexedOscillatorBandwidth L atTop)
    (hbelow : ∀ k, m k < 4 * (j : ℝ) + 1) : False := by
  let B : ℝ → ℝ := indexedOscillatorWindowBound M
  let K₀ : ℝ := M + 2
  let B₀ : ℝ := B K₀
  let N : ℝ := 4 * K₀ * B₀ ^ 2
  let C : ℝ := (M + 1) * N
  have hK₀ : 0 < K₀ := by dsimp [K₀]; linarith
  have hB : ∀ K, 0 < K → 0 ≤ B K := by
    intro K hK
    exact indexedOscillatorWindowBound_nonneg M K
  have hev : ∀ (k : Fin (j + 1)) (K : ℝ), 0 < K → ∀ᶠ a in L,
      0 < indexedOscillatorBandwidth a ∧ 2 * K ^ 2 ≤ indexedOscillatorBandwidth a ∧
      (∀ x ∈ Icc (0 : ℝ) K,
        indexedOscillatorProfileDeriv2 (k : ℕ) a x =
          rescaledProlateP (indexedOscillatorBandwidth a)
              (indexedOscillatorSeparation (k : ℕ) a) x *
              indexedOscillatorProfile (k : ℕ) a x +
            rescaledProlateQ (indexedOscillatorBandwidth a) x *
              indexedOscillatorProfileDeriv (k : ℕ) a x) ∧
      (∀ x ∈ Icc (0 : ℝ) K,
        max |indexedOscillatorProfile (k : ℕ) a x|
            |indexedOscillatorProfileDeriv (k : ℕ) a x| ≤ B K) ∧
      indexedOscillatorProfile (k : ℕ) a 0 = 1 ∧
      indexedOscillatorProfileDeriv (k : ℕ) a 0 = 0 := by
    intro k K hK
    simpa [B] using eventually_indexedOscillatorProfile_windowBound hM
      (k : ℕ) (hmu k) (hmle k) hc hK
  have htotal : ∀ k : Fin (j + 1), ∀ᶠ a in L,
      indexedOscillatorTotalMass (k : ℕ) a ≤ N := by
    intro k
    have hwin := hev k K₀ hK₀
    have hmUpper : m k < M + 1 := by linarith [hmle k]
    have hmuUpper : ∀ᶠ a in L,
        indexedOscillatorSeparation (k : ℕ) a < M + 1 :=
      (hmu k).eventually (Iio_mem_nhds hmUpper)
    filter_upwards [hwin, hmuUpper] with a hwa hmua
    have hD := signedModeRadialData_isExact_of_pos a.property (k : ℕ)
    have hmassIneq := normalizedProlate_total_mass_le_of_windowPhase
      (c := indexedOscillatorBandwidth a)
      (mu := indexedOscillatorSeparation (k : ℕ) a)
      (chi := (signedModeRadialData (a : ℝ) (k : ℕ)).chi)
      (Phi := (signedModeRadialData (a : ℝ) (k : ℕ)).R)
      (indexedOscillatorBandwidth_pos a) hK₀ hwa.2.1 hD.2.2.2.2.2.1
      hD.2.2.2.2.2.2.1 hD.2.2.2.2.2.2.2.2.2.1
      (by
        have hs := hD.2.2.2.2.2.2.2.2.2.2.1
        simpa [indexedOscillatorSeparation, indexedOscillatorBandwidth] using
          (congrArg (fun s => indexedOscillatorBandwidth a * s) hs))
      hwa.2.2.2.1
    have hmuNonneg : 0 ≤ indexedOscillatorSeparation (k : ℕ) a := by
      exact mul_nonneg (indexedOscillatorBandwidth_pos a).le hD.2.2.2.2.2.2.2.2.2.2.2.1
    have hratio : indexedOscillatorSeparation (k : ℕ) a / K₀ ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ (sq_pos_of_pos hK₀)]
      dsimp [K₀]
      nlinarith [sq_nonneg M]
    have hfactor : 1 / 2 ≤ 1 - indexedOscillatorSeparation (k : ℕ) a / K₀ ^ 2 := by
      linarith
    have hmassNonneg := indexedOscillatorTotalMass_nonneg (k : ℕ) a
    have hmassIneq' : indexedOscillatorTotalMass (k : ℕ) a *
        (1 - indexedOscillatorSeparation (k : ℕ) a / K₀ ^ 2) ≤
          2 * K₀ * B₀ ^ 2 := by
      simpa [indexedOscillatorTotalMass, indexedOscillatorProfile, B₀, B]
        using hmassIneq
    dsimp [N]
    nlinarith [mul_le_mul_of_nonneg_left hfactor hmassNonneg]
  have hmass : ∀ (k : Fin (j + 1)) (K : ℝ), 0 < K → ∀ᶠ a in L,
      (∫ x in (-K)..K,
        indexedOscillatorProfile (k : ℕ) a x *
          indexedOscillatorProfile (k : ℕ) a x) ≤ N := by
    intro k K hK
    have hcK : ∀ᶠ a in L, K ^ 2 ≤ indexedOscillatorBandwidth a :=
      hc.eventually (eventually_ge_atTop (K ^ 2))
    filter_upwards [htotal k, hcK] with a htot hca
    have hKsqrt : K ≤ Real.sqrt (indexedOscillatorBandwidth a) := by
      rw [← Real.sqrt_sq hK.le]
      exact Real.sqrt_le_sqrt hca
    have hcont : Continuous (indexedOscillatorProfile (k : ℕ) a) := by
      exact continuous_normalizedProlateProfile
        (signedModeRadialData_isExact_of_pos a.property (k : ℕ)).2.2.2.2.2.1
    have hle := window_le_total (f := indexedOscillatorProfile (k : ℕ) a)
      hKsqrt hcont
    simpa [indexedOscillatorTotalMass, indexedOscillatorProfile, pow_two] using hle.trans htot
  have hpair : ∀ k l : Fin (j + 1), k ≠ l → ∀ K : ℝ, 0 < K → ∀ᶠ a in L,
      |∫ x in (-K)..K,
        indexedOscillatorProfile (k : ℕ) a x * indexedOscillatorProfile (l : ℕ) a x| ≤
          C / K ^ 2 := by
    intro k l hkl K hK
    have hcK : ∀ᶠ a in L, K ^ 2 ≤ indexedOscillatorBandwidth a :=
      hc.eventually (eventually_ge_atTop (K ^ 2))
    have hmkUpper : ∀ᶠ a in L, indexedOscillatorSeparation (k : ℕ) a ≤ M + 1 :=
      (hmu k).eventually (Iic_mem_nhds (by linarith [hmle k]))
    have hmlUpper : ∀ᶠ a in L, indexedOscillatorSeparation (l : ℕ) a ≤ M + 1 :=
      (hmu l).eventually (Iic_mem_nhds (by linarith [hmle l]))
    filter_upwards [htotal k, htotal l, hcK, hmkUpper, hmlUpper]
      with a hmassK hmassL hca hmuK hmuL
    have hKsqrt : K ≤ Real.sqrt (indexedOscillatorBandwidth a) := by
      rw [← Real.sqrt_sq hK.le]
      exact Real.sqrt_le_sqrt hca
    have hcontK : Continuous (indexedOscillatorProfile (k : ℕ) a) := by
      exact continuous_normalizedProlateProfile
        (signedModeRadialData_isExact_of_pos a.property (k : ℕ)).2.2.2.2.2.1
    have hcontL : Continuous (indexedOscillatorProfile (l : ℕ) a) := by
      exact continuous_normalizedProlateProfile
        (signedModeRadialData_isExact_of_pos a.property (l : ℕ)).2.2.2.2.2.1
    have htail := abs_window_pairing_sub_le_of_secondMoment hK hKsqrt hcontK hcontL
    have hmassK0 := indexedOscillatorTotalMass_nonneg (k : ℕ) a
    have hmassL0 := indexedOscillatorTotalMass_nonneg (l : ℕ) a
    have hmuK0 : 0 ≤ indexedOscillatorSeparation (k : ℕ) a := by
      exact mul_nonneg (indexedOscillatorBandwidth_pos a).le
        (signedModeRadialData_isExact_of_pos a.property (k : ℕ)).2.2.2.2.2.2.2.2.2.2.2.1
    have hmuL0 : 0 ≤ indexedOscillatorSeparation (l : ℕ) a := by
      exact mul_nonneg (indexedOscillatorBandwidth_pos a).le
        (signedModeRadialData_isExact_of_pos a.property (l : ℕ)).2.2.2.2.2.2.2.2.2.2.2.1
    have hmomK : indexedOscillatorSecondMoment (k : ℕ) a ≤ (M + 1) * N :=
      (indexedOscillatorSecondMoment_le (k : ℕ) a).trans
        (mul_le_mul hmuK hmassK hmassK0 (by linarith))
    have hmomL : indexedOscillatorSecondMoment (l : ℕ) a ≤ (M + 1) * N :=
      (indexedOscillatorSecondMoment_le (l : ℕ) a).trans
        (mul_le_mul hmuL hmassL hmassL0 (by linarith))
    have hklNat : (k : ℕ) ≠ (l : ℕ) := by
      intro h
      exact hkl (Fin.ext h)
    have horth := integral_indexedOscillatorProfile_mul_eq_zero_of_ne
      (m := (k : ℕ)) (n := (l : ℕ)) a hklNat
    rw [horth, zero_sub, abs_neg] at htail
    have htail' : |∫ x in (-K)..K,
        indexedOscillatorProfile (k : ℕ) a x * indexedOscillatorProfile (l : ℕ) a x| ≤
        (1 / (2 * K ^ 2)) *
          (indexedOscillatorSecondMoment (k : ℕ) a +
            indexedOscillatorSecondMoment (l : ℕ) a) := by
      simpa [indexedOscillatorSecondMoment, indexedOscillatorProfile] using htail
    have hKsq : 0 < K ^ 2 := sq_pos_of_pos hK
    calc
      |∫ x in (-K)..K,
          indexedOscillatorProfile (k : ℕ) a x * indexedOscillatorProfile (l : ℕ) a x|
          ≤ (1 / (2 * K ^ 2)) *
            (indexedOscillatorSecondMoment (k : ℕ) a +
              indexedOscillatorSecondMoment (l : ℕ) a) := htail'
      _ ≤ (1 / (2 * K ^ 2)) * (2 * ((M + 1) * N)) := by
        gcongr
        linarith
      _ = C / K ^ 2 := by
        dsimp [C]
        field_simp
  exact false_of_orthogonal_prolateFamily_below_windowBound
    (B := B) (N := N) (C := C) hB
    (fun k => indexedOscillatorProfile_hasDerivAt (k : ℕ))
    (fun k => indexedOscillatorProfileDeriv_hasDerivAt (k : ℕ))
    (fun k => indexedOscillatorProfile_even (k : ℕ))
    hev hmass hpair hmu hc hbelow

/-- At every positive aperture, multiplication by the positive bandwidth preserves the global
ordering of the canonical separation ratios. -/
theorem indexedOscillatorSeparation_monotone (a : ProlatePositiveAperture) :
    Monotone fun n : ℕ => indexedOscillatorSeparation n a := by
  intro m n hmn
  rcases hmn.eq_or_lt with rfl | hmn
  · exact le_rfl
  · exact mul_le_mul_of_nonneg_left
      (signedModeRadialData_s_strictMono a.property hmn).le
      (indexedOscillatorBandwidth_pos a).le

/-- The sharp indexed oscillator upper bound, restricted to the cofinal positive-aperture type. -/
theorem eventually_indexedOscillatorSeparation_lt_evenOscillatorRung_add
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : ProlatePositiveAperture in atTop,
      indexedOscillatorSeparation n a < 4 * (n : ℝ) + 1 + ε := by
  exact tendsto_prolatePositiveAperture_val_atTop.eventually
    (eventually_signedModeRadialBandwidth_mul_s_lt_evenOscillatorRung n hε)

/-- **Sharp indexed lower half of the oscillator law.**  A frequently low canonical index would
refine to an ultrafilter on which all preceding indices have simultaneous bounded limits.  Exact
orthogonality and local window compactness then force `n + 1` distinct even oscillator rungs below
the `n`th rung, which is impossible. -/
theorem eventually_evenOscillatorRung_sub_lt_indexedOscillatorSeparation
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : ProlatePositiveAperture in atTop,
      4 * (n : ℝ) + 1 - ε < indexedOscillatorSeparation n a := by
  by_contra hnot
  have hfreq : ∃ᶠ a : ProlatePositiveAperture in atTop,
      indexedOscillatorSeparation n a ≤ 4 * (n : ℝ) + 1 - ε := by
    simpa only [not_lt] using (Filter.not_eventually.mp hnot)
  let S : Set ProlatePositiveAperture :=
    {a | indexedOscillatorSeparation n a ≤ 4 * (n : ℝ) + 1 - ε}
  let L : Filter ProlatePositiveAperture := atTop ⊓ Filter.principal S
  have hLne : L.NeBot := by
    change (atTop ⊓ Filter.principal S).NeBot
    rw [Filter.inf_principal_neBot_iff]
    intro U hU
    obtain ⟨a, haU, haBad⟩ := Filter.frequently_iff.mp hfreq hU
    exact ⟨a, haU, by simpa [S] using haBad⟩
  letI : L.NeBot := hLne
  have hLatTop : L ≤ (atTop : Filter ProlatePositiveAperture) := by
    dsimp [L]
    exact inf_le_left
  let M : ℝ := 4 * (n : ℝ) + 2
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hbounded : ∀ k : Fin (n + 1), ∀ᶠ a in L,
      indexedOscillatorSeparation (k : ℕ) a ∈ Icc 0 M := by
    intro k
    have hkUpperAtTop :=
      eventually_indexedOscillatorSeparation_lt_evenOscillatorRung_add
        (k : ℕ) (ε := 1) zero_lt_one
    have hkUpper := hkUpperAtTop.filter_mono hLatTop
    filter_upwards [hkUpper] with a hka
    have hknNat : (k : ℕ) ≤ n := Nat.le_of_lt_succ k.isLt
    have hkn : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hknNat
    constructor
    · exact mul_nonneg (indexedOscillatorBandwidth_pos a).le
        (signedModeRadialData_isExact_of_pos a.property (k : ℕ)).2.2.2.2.2.2.2.2.2.2.2.1
    · dsimp [M]
      linarith
  obtain ⟨U, hUL, m, hmIcc, hmu⟩ :=
    exists_ultrafilter_tendsto_of_eventually_bounded
      (fun k : Fin (n + 1) => indexedOscillatorSeparation (k : ℕ)) hbounded
  have hUatTop : (U : Filter ProlatePositiveAperture) ≤ atTop := hUL.trans hLatTop
  have hcU : Tendsto indexedOscillatorBandwidth (U : Filter ProlatePositiveAperture) atTop :=
    tendsto_indexedOscillatorBandwidth_atTop.mono_left hUatTop
  have hbadL : ∀ᶠ a in L,
      indexedOscillatorSeparation n a ≤ 4 * (n : ℝ) + 1 - ε := by
    change ∀ᶠ a in atTop ⊓ Filter.principal S,
      indexedOscillatorSeparation n a ≤ 4 * (n : ℝ) + 1 - ε
    rw [Filter.eventually_inf_principal]
    exact Filter.Eventually.of_forall fun a ha => by simpa [S] using ha
  have hbadU : ∀ᶠ a in (U : Filter ProlatePositiveAperture),
      indexedOscillatorSeparation n a ≤ 4 * (n : ℝ) + 1 - ε :=
    hbadL.filter_mono hUL
  have hbelow : ∀ k : Fin (n + 1), m k < 4 * (n : ℝ) + 1 := by
    intro k
    have hkBad : ∀ᶠ a in (U : Filter ProlatePositiveAperture),
        indexedOscillatorSeparation (k : ℕ) a ≤ 4 * (n : ℝ) + 1 - ε := by
      filter_upwards [hbadU] with a ha
      exact (indexedOscillatorSeparation_monotone a
        (Nat.le_of_lt_succ k.isLt)).trans ha
    have hmBad : m k ≤ 4 * (n : ℝ) + 1 - ε := le_of_tendsto (hmu k) hkBad
    linarith
  exact false_of_canonicalIndexedProlate_limits_below
    (j := n) (L := (U : Filter ProlatePositiveAperture)) (M := M)
    hM hmu (fun k => (hmIcc k).2) hcU hbelow

/-- Canonical separation mode `n` converges to exactly the `n`th even oscillator rung on the
positive-aperture cofinal type. -/
theorem tendsto_indexedOscillatorSeparation_atTop (n : ℕ) :
    Tendsto (indexedOscillatorSeparation n) atTop (𝓝 (4 * (n : ℝ) + 1)) := by
  rw [tendsto_order]
  constructor
  · intro b hb
    have hε : 0 < (4 * (n : ℝ) + 1) - b := sub_pos.mpr hb
    have hlow := eventually_evenOscillatorRung_sub_lt_indexedOscillatorSeparation n hε
    filter_upwards [hlow] with a ha
    linarith
  · intro b hb
    have hε : 0 < b - (4 * (n : ℝ) + 1) := sub_pos.mpr hb
    have hupp := eventually_indexedOscillatorSeparation_lt_evenOscillatorRung_add n hε
    filter_upwards [hupp] with a ha
    linarith

/-- The sharp indexed lower bound on the original real aperture axis. -/
theorem eventually_evenOscillatorRung_sub_lt_signedModeRadialBandwidth_mul_s
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop,
      4 * (n : ℝ) + 1 - ε <
        signedModeRadialBandwidth a * (signedModeRadialData a n).s := by
  obtain ⟨a₀, ha₀⟩ := Filter.eventually_atTop.mp
    (eventually_evenOscillatorRung_sub_lt_indexedOscillatorSeparation n hε)
  apply Filter.eventually_atTop.mpr
  refine ⟨(a₀ : ℝ), fun a haa => ?_⟩
  have haPos : 0 < a := lt_of_lt_of_le a₀.property haa
  let aPos : ProlatePositiveAperture := ⟨a, haPos⟩
  have ha₀a : a₀ ≤ aPos := haa
  simpa [indexedOscillatorSeparation, indexedOscillatorBandwidth, aPos] using ha₀ aPos ha₀a

/-- **Exact indexed large-aperture oscillator law.**  Every fixed canonical prolate separation
mode retains its index in the Hermite limit; no subsequence can collapse onto a lower rung. -/
theorem tendsto_signedModeRadialBandwidth_mul_s_atTop (n : ℕ) :
    Tendsto
      (fun a : ℝ => signedModeRadialBandwidth a * (signedModeRadialData a n).s)
      atTop (𝓝 (4 * (n : ℝ) + 1)) := by
  rw [tendsto_order]
  constructor
  · intro b hb
    have hε : 0 < (4 * (n : ℝ) + 1) - b := sub_pos.mpr hb
    have hlow :=
      eventually_evenOscillatorRung_sub_lt_signedModeRadialBandwidth_mul_s n hε
    filter_upwards [hlow] with a ha
    linarith
  · intro b hb
    have hε : 0 < b - (4 * (n : ℝ) + 1) := sub_pos.mpr hb
    have hupp :=
      eventually_signedModeRadialBandwidth_mul_s_lt_evenOscillatorRung n hε
    filter_upwards [hupp] with a ha
    linarith


end GaloisForLFunctions.RHTower
