import GaloisForLFunctions.BiScaleUncertainty.FiniteSourceEnergyScalarization
import GaloisForLFunctions.RHTower.GammaHardyPhaseRateLevyKhintchine

/-!
# Finite spectral envelopes with exact local data and uniform energy error

Cosine/sine modulation realizes a cosine times an actual compact autocorrelation. The energy
error relative to the pure-frequency cost is bounded by the envelope energy, uniformly in the
frequency. Finite nonnegative mixtures can then be scalarized and made polar while preserving
all prescribed bounded-window normalized correlations exactly.
-/

open MeasureTheory Set Filter Topology
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-- The archimedean cost of a unit cosine frequency. -/
def archFrequencyCost (ω : ℝ) : ℝ :=
  ∫ x in Ioi 0, (1 - Real.cos (ω * x)) * archLevySinhWeight x

theorem integrableOn_archFrequencyIntegrand (ω : ℝ) :
    IntegrableOn (fun x => (1 - Real.cos (ω * x)) * archLevySinhWeight x) (Ioi 0) := by
  refine ((RHTower.integrableOn_archLevyDensity_mul_one_sub_cos ω).const_mul 2).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [archLevySinhWeight, exp_half_div_sinh_eq hx]
  ring

/-- The frequency cost is exactly the centered archimedean symbol, with no approximation. -/
theorem archFrequencyCost_eq_gammaBracket_sub_zero (ω : ℝ) :
    archFrequencyCost ω = Zeta23.EF.gammaBracket ω - Zeta23.EF.gammaBracket 0 := by
  rw [RHTower.WeilLevyPole.gammaBracket_eq_two_mul_gammaHardyPhaseRate,
    RHTower.WeilLevyPole.gammaBracket_eq_two_mul_gammaHardyPhaseRate, ← mul_sub,
    RHTower.gammaHardyPhaseRate_sub_zero_eq_integral, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only [archLevySinhWeight]
  rw [exp_half_div_sinh_eq hx]
  ring

def cosineSource (f : ℝ → ℝ) (ω u : ℝ) : ℝ := f u * Real.cos (ω * u)
def sineSource (f : ℝ → ℝ) (ω u : ℝ) : ℝ := f u * Real.sin (ω * u)

theorem contDiff_cosineSource {f : ℝ → ℝ} {r : WithTop ℕ∞} (hf : ContDiff ℝ r f) (ω : ℝ) :
    ContDiff ℝ r (cosineSource f ω) :=
  hf.mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))

theorem contDiff_sineSource {f : ℝ → ℝ} {r : WithTop ℕ∞} (hf : ContDiff ℝ r f) (ω : ℝ) :
    ContDiff ℝ r (sineSource f ω) :=
  hf.mul (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id))

/-- A real cosine/sine pair realizes the full modulated autocorrelation exactly. -/
theorem autocorr_cosineSource_add_sineSource {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (ω x : ℝ) :
    autocorr (cosineSource f ω) x + autocorr (sineSource f ω) x =
      autocorr f x * Real.cos (ω * x) := by
  have hc : Continuous (cosineSource f ω) := hf.mul (by fun_prop)
  have hs : Continuous (sineSource f ω) := hf.mul (by fun_prop)
  unfold autocorr
  rw [← integral_add (integrable_mul_shift hc hfc.mul_right x)
    (integrable_mul_shift hs hfc.mul_right x), ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with u
  have ht : Real.cos (ω * u) * Real.cos (ω * (u + x)) +
      Real.sin (ω * u) * Real.sin (ω * (u + x)) = Real.cos (ω * x) := by
    rw [← Real.cos_sub, show ω * u - ω * (u + x) = -(ω * x) by ring, Real.cos_neg]
  dsimp only [cosineSource, sineSource]
  linear_combination (f u * f (u + x)) * ht

/-- The oscillatory error in the modulated energy. -/
def archEnvelopeError (f : ℝ → ℝ) (ω : ℝ) : ℝ :=
  ∫ x in Ioi 0, ((autocorr f 0 - autocorr f x) * archLevySinhWeight x) * Real.cos (ω * x)

theorem integrableOn_archEnvelopeError {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (ω : ℝ) :
    IntegrableOn (fun x => ((autocorr f 0 - autocorr f x) * archLevySinhWeight x) *
      Real.cos (ω * x)) (Ioi 0) := by
  have hi := integrableOn_biScaleLevyIntegrand hf hfc
  refine hi.mono' (hi.aestronglyMeasurable.mul (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg
    (mul_nonneg (autocorr_sub_nonneg hfc hf.continuous x) (archLevySinhWeight_pos hx).le)]
  exact mul_le_of_le_one_right
    (mul_nonneg (autocorr_sub_nonneg hfc hf.continuous x) (archLevySinhWeight_pos hx).le)
    (Real.abs_cos_le_one _)

/-- Uniform in frequency: the envelope contributes at most its own energy in absolute value. -/
theorem abs_archEnvelopeError_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (ω : ℝ) :
    |archEnvelopeError f ω| ≤ biScaleLevyEnergy f := by
  unfold archEnvelopeError biScaleLevyEnergy
  calc
    _ ≤ ∫ x in Ioi 0, |((autocorr f 0 - autocorr f x) * archLevySinhWeight x) * Real.cos (ω * x)| :=
      abs_integral_le_integral_abs
    _ ≤ _ := by
      refine integral_mono_ae (integrableOn_archEnvelopeError hf hfc ω).abs
        (integrableOn_biScaleLevyIntegrand hf hfc) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [abs_mul, abs_of_nonneg
        (mul_nonneg (autocorr_sub_nonneg hfc hf.continuous x) (archLevySinhWeight_pos hx).le)]
      exact mul_le_of_le_one_right
        (mul_nonneg (autocorr_sub_nonneg hfc hf.continuous x) (archLevySinhWeight_pos hx).le)
        (Real.abs_cos_le_one _)

/-- Exact energy decomposition of the two real modulated components. -/
theorem biScaleLevyEnergy_cosine_sine_eq {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (ω : ℝ) :
    biScaleLevyEnergy (cosineSource f ω) + biScaleLevyEnergy (sineSource f ω) =
      autocorr f 0 * archFrequencyCost ω + archEnvelopeError f ω := by
  have hc := integrableOn_biScaleLevyIntegrand (contDiff_cosineSource hf ω) hfc.mul_right
  have hs := integrableOn_biScaleLevyIntegrand (contDiff_sineSource hf ω) hfc.mul_right
  unfold biScaleLevyEnergy archFrequencyCost archEnvelopeError
  rw [← integral_add hc hs, ← integral_const_mul,
    ← integral_add ((integrableOn_archFrequencyIntegrand ω).const_mul (autocorr f 0))
      (integrableOn_archEnvelopeError hf hfc ω)]
  apply integral_congr_ae
  filter_upwards [] with x
  have h0 := autocorr_cosineSource_add_sineSource hf.continuous hfc ω 0
  simp only [mul_zero, Real.cos_zero, mul_one] at h0
  have hx := autocorr_cosineSource_add_sineSource hf.continuous hfc ω x
  linear_combination (archLevySinhWeight x) * h0 - (archLevySinhWeight x) * hx

/-- Actual scalar realization of one frequency with explicit envelope-energy error. -/
theorem exists_scalar_cosine_envelope {f : ℝ → ℝ} {r : WithTop ℕ∞} (hr : 2 ≤ r)
    (hf : ContDiff ℝ r f) (hfc : HasCompactSupport f) (ω A : ℝ) :
    ∃ k : ℝ → ℝ, ContDiff ℝ r k ∧ HasCompactSupport k ∧
      (∀ x, |x| ≤ A → autocorr k x = autocorr f x * Real.cos (ω * x)) ∧
      biScaleLevyEnergy k ≤ autocorr f 0 * archFrequencyCost ω + biScaleLevyEnergy f := by
  obtain ⟨k, hk, hkc, hlocal, hE⟩ := exists_scalar_pair_local_energy_le hr
    (contDiff_cosineSource hf ω) (contDiff_sineSource hf ω) hfc.mul_right hfc.mul_right A
  refine ⟨k, hk, hkc, ?_, ?_⟩
  · intro x hx
    exact (hlocal x hx).trans (autocorr_cosineSource_add_sineSource hf.continuous hfc ω x)
  · rw [biScaleLevyEnergy_cosine_sine_eq (hf.of_le hr) hfc] at hE
    exact hE.trans (add_le_add le_rfl ((le_abs_self _).trans
      (abs_archEnvelopeError_le (hf.of_le hr) hfc ω)))

/-- A finite cosine mixture with its nonnegative weights recorded explicitly. -/
def cosineMixture (atoms : List (ℝ × ℝ)) (x : ℝ) : ℝ :=
  (atoms.map (fun p => p.1 * Real.cos (p.2 * x))).sum

def spectralMixtureCost (atoms : List (ℝ × ℝ)) : ℝ :=
  (atoms.map (fun p => p.1 * archFrequencyCost p.2)).sum

def spectralMixtureMass (atoms : List (ℝ × ℝ)) : ℝ := (atoms.map Prod.fst).sum

/-- The total energy of the actual cosine/sine vector source components. -/
def spectralEnvelopeEnergy (f : ℝ → ℝ) (atoms : List (ℝ × ℝ)) : ℝ :=
  (atoms.map (fun p => p.1 * (biScaleLevyEnergy (cosineSource f p.2) +
    biScaleLevyEnergy (sineSource f p.2)))).sum

/-- Uniform absolute error for the finite vector envelope, including zero weights. -/
theorem abs_spectralEnvelopeEnergy_sub_cost_le (atoms : List (ℝ × ℝ)) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hw : ∀ p ∈ atoms, 0 ≤ p.1) :
    |spectralEnvelopeEnergy f atoms - autocorr f 0 * spectralMixtureCost atoms| ≤
      biScaleLevyEnergy f * spectralMixtureMass atoms := by
  induction atoms with
  | nil => simp [spectralEnvelopeEnergy, spectralMixtureCost, spectralMixtureMass]
  | cons p atoms ih =>
      have hp := hw p (List.mem_cons_self ..)
      have ht := ih (fun q hq => hw q (List.mem_cons_of_mem _ hq))
      have he : |p.1 * archEnvelopeError f p.2| ≤ p.1 * biScaleLevyEnergy f := by
        rw [abs_mul, abs_of_nonneg hp]
        exact mul_le_mul_of_nonneg_left (abs_archEnvelopeError_le hf hfc p.2) hp
      have hid : spectralEnvelopeEnergy f (p :: atoms) -
          autocorr f 0 * spectralMixtureCost (p :: atoms) =
          p.1 * archEnvelopeError f p.2 +
            (spectralEnvelopeEnergy f atoms - autocorr f 0 * spectralMixtureCost atoms) := by
        simp only [spectralEnvelopeEnergy, spectralMixtureCost, List.map_cons, List.sum_cons,
          biScaleLevyEnergy_cosine_sine_eq hf hfc]
        ring
      rw [hid]
      have hab := abs_add_le (p.1 * archEnvelopeError f p.2)
        (spectralEnvelopeEnergy f atoms - autocorr f 0 * spectralMixtureCost atoms)
      simp only [spectralMixtureMass, List.map_cons, List.sum_cons] at ht ⊢
      linarith

/-- Every finite nonnegative spectral mixture has an actual real scalar envelope realization.
The energy allowance uses only spectral cost, total weight, and the envelope energy. -/
theorem exists_scalar_spectral_envelope (atoms : List (ℝ × ℝ)) {f : ℝ → ℝ}
    {r : WithTop ℕ∞} (hr : 2 ≤ r) (hf : ContDiff ℝ r f) (hfc : HasCompactSupport f)
    (hw : ∀ p ∈ atoms, 0 ≤ p.1) (A : ℝ) :
    ∃ k : ℝ → ℝ, ContDiff ℝ r k ∧ HasCompactSupport k ∧
      (∀ x, |x| ≤ A → autocorr k x = autocorr f x * cosineMixture atoms x) ∧
      biScaleLevyEnergy k ≤ autocorr f 0 * spectralMixtureCost atoms +
        biScaleLevyEnergy f * spectralMixtureMass atoms := by
  induction atoms with
  | nil =>
      refine ⟨fun _ => 0, contDiff_const, HasCompactSupport.zero, ?_, ?_⟩
      · intro x _; simp [autocorr, cosineMixture]
      · simp [biScaleLevyEnergy, autocorr, spectralMixtureCost, spectralMixtureMass]
  | cons p atoms ih =>
      have hp := hw p (List.mem_cons_self ..)
      obtain ⟨g, hg, hgc, hlocalg, hEg⟩ := ih (fun q hq => hw q (List.mem_cons_of_mem _ hq))
      obtain ⟨h, hh, hhc, hlocalh, hEh⟩ := exists_scalar_cosine_envelope hr hf hfc p.2 A
      obtain ⟨k, hk, hkc, hlocalk, hEk⟩ :=
        exists_scalar_weighted_pair_local_energy_le hr hh hg hhc hgc hp zero_le_one A
      refine ⟨k, hk, hkc, ?_, ?_⟩
      · intro x hx
        rw [hlocalk x hx, hlocalh x hx, hlocalg x hx]
        simp only [cosineMixture, List.map_cons, List.sum_cons]
        ring
      · have hweighted := mul_le_mul_of_nonneg_left hEh hp
        simp only [one_mul] at hEk
        simp only [spectralMixtureCost, spectralMixtureMass, List.map_cons, List.sum_cons]
        dsimp only [spectralMixtureCost, spectralMixtureMass] at hEg
        nlinarith

/-- Unit-mass finite spectral data have actual polar scalar envelopes with arbitrary additional
energy tolerance and exactly the prescribed normalized local correlations. -/
theorem exists_polar_spectral_envelope (atoms : List (ℝ × ℝ)) {f : ℝ → ℝ}
    {r : WithTop ℕ∞} (hr : 2 ≤ r) (hf : ContDiff ℝ r f) (hfc : HasCompactSupport f)
    (hR : 0 < autocorr f 0) (hw : ∀ p ∈ atoms, 0 ≤ p.1)
    (hmass : spectralMixtureMass atoms = 1) (A : ℝ) (hA : 0 ≤ A) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ r g ∧ HasCompactSupport g ∧ 0 < autocorr g 0 ∧
      (∫ x in Ioi 0, autocorr g x * Real.cosh (x / 2)) = 0 ∧
      (∀ x, |x| ≤ A → autocorr g x / autocorr g 0 =
        autocorr f x / autocorr f 0 * cosineMixture atoms x) ∧
      normalizedArchEnergy g < spectralMixtureCost atoms + normalizedArchEnergy f + ε := by
  obtain ⟨k, hk, hkc, hlocal, hE⟩ := exists_scalar_spectral_envelope atoms hr hf hfc hw A
  have hzero : cosineMixture atoms 0 = 1 := by
    simpa only [cosineMixture, spectralMixtureMass, mul_zero, Real.cos_zero, mul_one] using hmass
  have hkR : autocorr k 0 = autocorr f 0 := by
    simpa only [hzero, mul_one] using hlocal 0 (by simpa using hA)
  have hkpos : 0 < autocorr k 0 := by rwa [hkR]
  have hkE : normalizedArchEnergy k ≤ spectralMixtureCost atoms + normalizedArchEnergy f := by
    rw [hmass, mul_one] at hE
    unfold normalizedArchEnergy
    rw [hkR]
    calc
      _ ≤ (autocorr f 0 * spectralMixtureCost atoms + biScaleLevyEnergy f) / autocorr f 0 :=
        div_le_div_of_nonneg_right hE hR.le
      _ = _ := by field_simp
  obtain ⟨g, hg, hgc, hgR, hpolar, hlocalg, herr⟩ :=
    exists_polar_source_local_energy_close hr hk hkc hkpos A hA hε
  refine ⟨g, hg, hgc, hgR, hpolar, ?_, ?_⟩
  · intro x hx
    rw [hlocalg x hx, hlocal x hx, hkR]
    ring
  · have := (le_abs_self (normalizedArchEnergy g - normalizedArchEnergy k)).trans_lt herr
    linarith

/-- Every finite spectral probability satisfying the logarithmic cosine constraints gives an
actual polar grid source, with spectral cost plus explicit envelope error and arbitrary tolerance. -/
theorem exists_polar_log_grid_source_of_spectral_mixture (atoms : List (ℝ × ℝ))
    {f : ℝ → ℝ} {r : WithTop ℕ∞} (hr : 2 ≤ r) (hf : ContDiff ℝ r f)
    (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    (hw : ∀ p ∈ atoms, 0 ≤ p.1) (hmass : spectralMixtureMass atoms = 1) (N : ℕ)
    (hgrid : ∀ n ∈ Finset.Icc 2 N, cosineMixture atoms (Real.log (n : ℝ)) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ r g ∧ HasCompactSupport g ∧ 0 < autocorr g 0 ∧
      (∫ x in Ioi 0, autocorr g x * Real.cosh (x / 2)) = 0 ∧
      (∀ n ∈ Finset.Icc 2 N, autocorr g (Real.log (n : ℝ)) = 0) ∧
      normalizedArchEnergy g < spectralMixtureCost atoms + normalizedArchEnergy f + ε := by
  let A := max (Real.log (N : ℝ)) 0
  obtain ⟨g, hg, hgc, hgR, hpolar, hlocal, hE⟩ :=
    exists_polar_spectral_envelope atoms hr hf hfc hR hw hmass A (le_max_right _ _) hε
  refine ⟨g, hg, hgc, hgR, hpolar, ?_, hE⟩
  intro n hn
  have hnrange := Finset.mem_Icc.mp hn
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hbound : |Real.log (n : ℝ)| ≤ A := by
    rw [abs_of_nonneg hln]
    exact (Real.log_le_log hnp (by exact_mod_cast hnrange.2)).trans (le_max_left _ _)
  have hz := hlocal (Real.log (n : ℝ)) hbound
  rw [hgrid n hn, mul_zero] at hz
  exact (div_eq_zero_iff.mp hz).resolve_right hgR.ne'

end
end GaloisForLFunctions.BiScaleUncertainty
