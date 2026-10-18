import GaloisForLFunctions.RHTower.CHMDArithmeticThetaOrder
import GaloisForLFunctions.RHTower.CHMDThetaHarmonicIdentity

/-!
# Signed arithmetic recovery from the complete Euler–Poisson source

The theta, archimedean, and polar terms of the one-sided source equation uniquely
determine all arithmetic coefficients. The coefficients may have arbitrary signs;
no coefficientwise comparison with von Mangoldt weights is required. Integer
samples, even after deleting an arbitrary finite prefix, suffice.

The actual von Mangoldt data are admitted using the already proved complete prime
source summability. Thus the uniqueness and coefficient-recovery theorems have no
Riemann-hypothesis, positivity, or additional analytic premise.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators
noncomputable section

namespace RHTower.CHMDArithmeticTheta
open HedenmalmThetaSource CHMDPolar ThetaSourceWard

/-- Undo the cusp normalization to read the original arithmetic coefficient. -/
def coefficient (a : Data) (n : ℕ) : ℝ :=
  a n / thetaEnvelope (Real.log (site n))

theorem wave_eq_arithmetic_series (a : Data) (x : ℝ) :
    wave a x = ∑' n, coefficient a n * riemannKernelReal (x + Real.log (site n)) := by
  apply tsum_congr
  intro n
  dsimp [atom, coefficient]
  ring

/-- Admissibility is exactly absolute convergence of the original arithmetic
source at zero; it imposes no polynomial growth bound on the coefficients. -/
theorem summable_weighted_envelope_iff (c : ℕ → ℝ) :
    (Summable fun n => |c n| * thetaEnvelope (Real.log (site n))) ↔
      Summable (fun n => c n * riemannKernelReal (Real.log (site n))) := by
  constructor
  · intro hs
    apply Summable.of_norm_bounded (hs.mul_left thetaEnvelopeUpper)
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (riemannKernelReal_pos _)]
    have hu := thetaCuspFullSource_le_envelope (log_site_pos n).le
    rw [thetaCuspFullSource_eq_riemannKernelReal] at hu
    calc
      _ ≤ |c n| * (thetaEnvelopeUpper * thetaEnvelope (Real.log (site n))) :=
        mul_le_mul_of_nonneg_left hu (abs_nonneg _)
      _ = _ := by ring
  · intro hs
    have hn : Summable fun n => |c n| * riemannKernelReal (Real.log (site n)) := by
      simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (riemannKernelReal_pos _)] using hs.norm
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg (abs_nonneg _) (thetaEnvelope_pos _).le)
      (fun n => ?_) (hn.mul_left (1 / thetaEnvelopeLower))
    have hl := thetaCuspFullSource_ge_envelope (log_site_pos n)
    rw [thetaCuspFullSource_eq_riemannKernelReal] at hl
    have hb : thetaEnvelope (Real.log (site n)) ≤
        riemannKernelReal (Real.log (site n)) / thetaEnvelopeLower :=
      (le_div_iff₀ thetaEnvelopeLower_pos).mpr (by nlinarith)
    calc
      _ ≤ |c n| * (riemannKernelReal (Real.log (site n)) / thetaEnvelopeLower) :=
        mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ = _ := by ring

/-- Every signed coefficient sequence with an absolutely convergent zero sample
belongs to the recovery class. -/
def sourceData (c : ℕ → ℝ)
    (hc : Summable fun n => c n * riemannKernelReal (Real.log (site n))) : Data :=
  ⟨fun n => c n * thetaEnvelope (Real.log (site n)), by
    apply memℓp_gen
    simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs, abs_mul,
      abs_of_pos (thetaEnvelope_pos _)] using (summable_weighted_envelope_iff c).mpr hc⟩

theorem coefficient_sourceData (c : ℕ → ℝ)
    (hc : Summable fun n => c n * riemannKernelReal (Real.log (site n))) (n : ℕ) :
    coefficient (sourceData c hc) n = c n := by
  dsimp [coefficient, sourceData]
  exact mul_div_cancel_right₀ _ (thetaEnvelope_pos _).ne'

theorem wave_sourceData (c : ℕ → ℝ)
    (hc : Summable fun n => c n * riemannKernelReal (Real.log (site n))) (x : ℝ) :
    wave (sourceData c hc) x = ∑' n, c n * riemannKernelReal (x + Real.log (site n)) := by
  rw [wave_eq_arithmetic_series]
  simp_rw [coefficient_sourceData]

theorem summable_mangoldt_data : Summable fun n : ℕ =>
    vonMangoldtAtom (n + 2) * thetaEnvelope (Real.log (site n)) := by
  have hs : Summable fun n : ℕ =>
      vonMangoldtAtom (n + 2) * riemannKernelReal (Real.log (site n)) := by
    simpa only [zero_add, site, Nat.cast_add, Nat.cast_ofNat] using
      (summable_nat_add_iff 2).mpr (summable_primeShift_right 0)
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (vonMangoldtAtom_nonneg _) (thetaEnvelope_pos _).le)
    (fun n => ?_) (hs.mul_left (1 / thetaEnvelopeLower))
  have hl := thetaCuspFullSource_ge_envelope (log_site_pos n)
  rw [thetaCuspFullSource_eq_riemannKernelReal] at hl
  have hb : thetaEnvelope (Real.log (site n)) ≤
      riemannKernelReal (Real.log (site n)) / thetaEnvelopeLower :=
    (le_div_iff₀ thetaEnvelopeLower_pos).mpr (by nlinarith)
  calc
    _ ≤ vonMangoldtAtom (n + 2) *
        (riemannKernelReal (Real.log (site n)) / thetaEnvelopeLower) :=
      mul_le_mul_of_nonneg_left hb (vonMangoldtAtom_nonneg _)
    _ = _ := by ring

/-- The original arithmetic source as an element of the signed coefficient space. -/
def mangoldtData : Data :=
  ⟨fun n => vonMangoldtAtom (n + 2) * thetaEnvelope (Real.log (site n)), by
    apply memℓp_gen
    simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (vonMangoldtAtom_nonneg _) (thetaEnvelope_pos _).le)] using
      summable_mangoldt_data⟩

theorem coefficient_mangoldtData (n : ℕ) :
    coefficient mangoldtData n = vonMangoldtAtom (n + 2) := by
  dsimp [coefficient, mangoldtData]
  exact mul_div_cancel_right₀ _ (thetaEnvelope_pos _).ne'

theorem wave_mangoldtData (x : ℝ) :
    wave mangoldtData x =
      ∑' n : ℕ, vonMangoldtAtom n * riemannKernelReal (x + Real.log n) := by
  rw [wave_eq_arithmetic_series]
  simp_rw [coefficient_mangoldtData]
  have h := (summable_primeShift_right x).sum_add_tsum_nat_add 2
  simpa [Finset.sum_range_succ, vonMangoldtAtom, site, Nat.cast_add] using h

/-- The complete one-sided source with arithmetic coefficients removed. -/
def sourceReadout (x : ℝ) : ℝ :=
  -archConstantReal * riemannKernelReal x +
    (∫ u in Ioi (0 : ℝ), gammaSourceTerm x u) +
    (∫ u in Ioi (0 : ℝ), 2 * Real.cosh (u / 2) * riemannKernelReal (x + u)) -
    x * riemannKernelReal x

theorem wave_mangoldtData_eq_sourceReadout (x : ℝ) :
    wave mangoldtData x = sourceReadout x := by
  rw [wave_mangoldtData]
  have h := oneSided_source_equation x
  dsimp [sourceReadout]
  linarith

/-- The fixed theta–Gamma–pole source has exactly one admissible signed arithmetic realization. -/
theorem unique_signed_arithmetic_source :
    ∃! a : Data, ∀ N : ℕ, wave a N = sourceReadout N := by
  refine ⟨mangoldtData, fun N => wave_mangoldtData_eq_sourceReadout N, ?_⟩
  intro a ha
  apply integer_samples_injective
  funext N
  change wave a N = wave mangoldtData N
  rw [ha N, wave_mangoldtData_eq_sourceReadout]

/-- Even an arbitrary finite set of early observations is unnecessary for arithmetic uniqueness. -/
theorem unique_eventual_signed_arithmetic_source :
    ∃! a : Data, ∀ᶠ N : ℕ in atTop, wave a N = sourceReadout N := by
  refine ⟨mangoldtData, Eventually.of_forall fun N => wave_mangoldtData_eq_sourceReadout N, ?_⟩
  intro a ha
  apply eq_of_eventually_wave_eq
  filter_upwards [ha] with N hN
  rw [hN, wave_mangoldtData_eq_sourceReadout]

/-- Agreement on any unbounded set of integer observations forces the actual
arithmetic data, even for arbitrary signed coefficient sequences. -/
theorem unique_frequently_signed_arithmetic_source :
    ∃! a : Data, ∃ᶠ N : ℕ in atTop, wave a N = sourceReadout N := by
  refine ⟨mangoldtData, (Eventually.of_forall
    (fun N : ℕ => wave_mangoldtData_eq_sourceReadout N)).frequently, ?_⟩
  intro a ha
  apply eq_of_frequently_wave_eq
  exact ha.mono fun N hN => hN.trans (wave_mangoldtData_eq_sourceReadout N).symm

/-- Direct coefficient form of signed source rigidity. Convergence at zero is
the entire admissibility requirement; no coefficientwise comparison is used. -/
theorem signed_arithmetic_source_rigidity (c : ℕ → ℝ)
    (hc : Summable fun n => c n * riemannKernelReal (Real.log (site n)))
    (hsource : ∃ᶠ N : ℕ in atTop,
      (∑' n, c n * riemannKernelReal ((N : ℝ) + Real.log (site n))) = sourceReadout N) :
    c = fun n => vonMangoldtAtom (n + 2) := by
  have hdata : sourceData c hc = mangoldtData := by
    apply eq_of_frequently_wave_eq
    refine hsource.mono fun N hN => ?_
    rw [wave_sourceData, hN, wave_mangoldtData_eq_sourceReadout]
  funext n
  have h := congrArg (fun a : Data => coefficient a n) hdata
  simpa only [coefficient_sourceData, coefficient_mangoldtData] using h

/-- Exact recursive recovery of the original `Λ(n)/sqrt(n)` coefficients from the
theta, Gamma, and pole source alone. -/
theorem recover_vonMangoldtAtom (m : ℕ) :
    Tendsto (fun N : ℕ =>
      (sourceReadout N - ∑ n ∈ Finset.range m,
        vonMangoldtAtom (n + 2) * riemannKernelReal ((N : ℝ) + Real.log (site n))) /
      riemannKernelReal ((N : ℝ) + Real.log (site m))) atTop
      (𝓝 (vonMangoldtAtom (m + 2))) := by
  have h := (recover_from_wave mangoldtData m).div_const (thetaEnvelope (Real.log (site m)))
  have hc : mangoldtData m / thetaEnvelope (Real.log (site m)) = vonMangoldtAtom (m + 2) :=
    coefficient_mangoldtData m
  rw [hc] at h
  convert h using 1
  funext N
  rw [wave_mangoldtData_eq_sourceReadout]
  have hh : (∑ n ∈ Finset.range m, mangoldtData n * atom n N) =
      ∑ n ∈ Finset.range m,
        vonMangoldtAtom (n + 2) * riemannKernelReal ((N : ℝ) + Real.log (site n)) := by
    apply Finset.sum_congr rfl
    intro n _
    dsimp [mangoldtData, atom]
    field_simp [(thetaEnvelope_pos _).ne']
  rw [hh]
  dsimp [atom]
  field_simp [(thetaEnvelope_pos _).ne', (riemannKernelReal_pos _).ne']

end RHTower.CHMDArithmeticTheta
