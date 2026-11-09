import GaloisForLFunctions.HyperbolicArakelovTheory.TheGreenDampingOnSmoothProbes
import GaloisForLFunctions.ArithmeticIntersectionTheory.TheHeckeCocycleOfRenormalization
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.WeilsFormIsContinuousInTheLevyNorm
import GaloisForLFunctions.RHTower.MarkovOddSectorFarkasAndOneSidedPBAP
import GaloisForLFunctions.BiScaleUncertainty.KreinIncrementAndChordCascade

/-!
# Smoothing retains the torsion discriminant

Place a compact C² profile at the integer logarithms below their spacing. Its
prime energy is exactly the torsion prime form times the profile mass. Coupling
the raw Abel torsion energy to the smooth Green energy therefore has a definite
meaning on these probes, without assuming an extension to arbitrary profiles.

One scalar locking cancels the logarithmic divergences. Its finite part is Weil's
form minus the profile mass times the discriminant diagonal. Changing the scalar
normalization adds only a multiple of total mass; it cannot remove that diagonal.
-/

open MeasureTheory Filter Topology Set Finset

noncomputable section

namespace GaloisForLFunctions.HyperbolicArakelovTheory

open SurfaceOfSpecZ ArithmeticEffectivityTheory ArithmeticIntersectionTheory
open ArithmeticElectrostatics SpacingScaleHarmonicAnalysis _root_.RHTower
open _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.ArchimedeanExactForm

/-- The raw torsion lift of a smooth packet, with an arbitrary common radius. -/
def smoothTorsionPacket (ρ : ℝ → ℝ) (r : ℝ) (N : ℕ) (x : ℕ → ℝ)
    (g : ℝ → ℝ) : ℝ :=
  let f := atomicTest N x g
  (2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2) - smoothGreenEnergy r f +
    (∫ u, g u ^ 2) * torsionForm (ρ r) (Icc 1 N) x

private theorem compact_atomicTest {g : ℝ → ℝ} (hgc : HasCompactSupport g)
    (N : ℕ) (x : ℕ → ℝ) : HasCompactSupport (atomicTest N x g) := by
  unfold atomicTest
  induction (Icc 1 N : Finset ℕ) using Finset.induction_on with
  | empty => simpa using (HasCompactSupport.zero : HasCompactSupport (0 : ℝ → ℝ))
  | insert n S hn ih =>
    simp only [Finset.sum_insert hn]
    exact ((hgc.comp_homeomorph (Homeomorph.subRight (Real.log n))).mul_left).add ih

/-- Before imposing separation, the two divergent coefficients are different quadratic forms:
the torsion coefficient is the discrete mass; the Green coefficient is the packet's L² mass. -/
theorem tendsto_smoothTorsionPacket_renormalized {ρ : ℝ → ℝ}
    (hρ : Tendsto ρ (𝓝[<] 1) (𝓝 1)) {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (N : ℕ) (x : ℕ → ℝ) :
    Tendsto (fun r => smoothTorsionPacket ρ r N x g +
        Real.log |1 - ρ r| * ((∫ u, g u ^ 2) * ∑ n ∈ Icc 1 N, x n ^ 2) +
        (∫ u, atomicTest N x g u ^ 2) * selfEnergy r) (𝓝[<] 1)
      (𝓝 ((2 * coshHalfMoment (atomicTest N x g) ^ 2 -
        2 * sinhHalfMoment (atomicTest N x g) ^ 2) + levyEnergy (atomicTest N x g) +
        (∫ u, g u ^ 2) * renormalizedTorsionForm (Icc 1 N) x)) := by
  have hT := ((tendsto_torsionForm
    (S := Icc 1 N) (fun n hn => (Finset.mem_Icc.mp hn).1) x).comp hρ).const_mul
      (∫ u, g u ^ 2)
  have hA := tendsto_smoothGreenEnergy_sub_mass (atomicTest N x g)
    (contDiff_atomicTest hg N x) (compact_atomicTest hgc N x)
  have h := (hT.sub hA).add_const
    (2 * coshHalfMoment (atomicTest N x g) ^ 2 - 2 * sinhHalfMoment (atomicTest N x g) ^ 2)
  convert h.congr (fun r => show _ = smoothTorsionPacket ρ r N x g +
      Real.log |1 - ρ r| * ((∫ u, g u ^ 2) * ∑ n ∈ Icc 1 N, x n ^ 2) +
      (∫ u, atomicTest N x g u ^ 2) * selfEnergy r by
    dsimp only [Function.comp_def, smoothTorsionPacket]; ring) using 1 <;> congr 1 <;> ring

/-- A scalar locking with an adjustable finite mass normalization. -/
def smoothLockingRadius (c r : ℝ) : ℝ := 1 - Real.exp (-selfEnergy r - c)

theorem log_smoothLockingRadius (c r : ℝ) :
    Real.log |1 - smoothLockingRadius c r| = -selfEnergy r - c := by
  rw [smoothLockingRadius, sub_sub_cancel, abs_of_pos (Real.exp_pos _), Real.log_exp]

theorem tendsto_smoothLockingRadius (c : ℝ) :
    Tendsto (smoothLockingRadius c) (𝓝[<] 1) (𝓝 1) := by
  have hz : Tendsto (fun r => -selfEnergy r - c) (𝓝[<] 1) atBot := by
    refine tendsto_atBot.2 fun b => ?_
    filter_upwards [tendsto_selfEnergy_atTop.eventually_ge_atTop (-b - c)] with r hr
    linarith
  have he := Real.tendsto_exp_atBot.comp hz
  simpa only [smoothLockingRadius, sub_zero] using he.const_sub 1

theorem eventually_smoothLockingRadius_mem (c : ℝ) :
    ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 < smoothLockingRadius c r ∧ smoothLockingRadius c r < 1 := by
  filter_upwards [tendsto_selfEnergy_atTop.eventually_gt_atTop (-c)] with r hr
  constructor
  · have h := Real.exp_lt_one_iff.mpr (show -selfEnergy r - c < 0 by linarith)
    dsimp only [smoothLockingRadius]
    linarith
  · dsimp only [smoothLockingRadius]
    linarith [Real.exp_pos (-selfEnergy r - c)]

/-- Pole minus smooth Green energy plus the actual Abel torsion energy of a packet. -/
def smoothLockedPacket (c r : ℝ) (N : ℕ) (x : ℕ → ℝ) (g : ℝ → ℝ) : ℝ :=
  let f := atomicTest N x g
  (2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2) - smoothGreenEnergy r f +
    (∫ u, g u ^ 2) * torsionForm (smoothLockingRadius c r) (Icc 1 N) x

/-- The exact discriminant defect for separated smooth packets. -/
theorem tendsto_smoothLockedPacket {g : ℝ → ℝ} {w : ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ}
    (hw : w < atomSpacing N) (x : ℕ → ℝ) (c : ℝ) :
    Tendsto (fun r => smoothLockedPacket c r N x g) (𝓝[<] 1)
      (𝓝 (weilQuad (atomicTest N x g) +
        (c - 2 * gammaHardyPhaseRate 0) * (∫ u, atomicTest N x g u ^ 2) -
        (∫ u, g u ^ 2) * ∑ n ∈ Icc 1 N, x n ^ 2 * selfIntersection n)) := by
  let f := atomicTest N x g
  have hf : ContDiff ℝ 2 f := contDiff_atomicTest hg N x
  have hfc : HasCompactSupport f := hasCompactSupport_atomicTest hsupp N x
  have hmass : (∫ u, f u ^ 2) = (∑ n ∈ Icc 1 N, x n ^ 2) * ∫ u, g u ^ 2 :=
    integral_atomicTest_sq hg hgc hsupp hw x
  have hprime : primeSum f = (∫ u, g u ^ 2) * atomicWeilForm N x :=
    primeSum_atomicTest hg hgc hsupp hw x
  have hT := ((tendsto_torsionForm
    (S := Icc 1 N) (fun n hn => (Finset.mem_Icc.mp hn).1) x).comp
      (tendsto_smoothLockingRadius c)).const_mul (∫ u, g u ^ 2)
  have hA := tendsto_smoothGreenEnergy_sub_mass f hf hfc
  have h := ((hT.sub hA).add_const (c * ∫ u, f u ^ 2)).add_const
    (2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2)
  have hval :
      ((∫ u, g u ^ 2) * renormalizedTorsionForm (Icc 1 N) x - -levyEnergy f +
        c * (∫ u, f u ^ 2)) + (2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2) =
      weilQuad f + (c - 2 * gammaHardyPhaseRate 0) * (∫ u, f u ^ 2) -
        (∫ u, g u ^ 2) * ∑ n ∈ Icc 1 N, x n ^ 2 * selfIntersection n := by
    rw [weilQuad_eq hf hfc, hprime]
    unfold renormalizedTorsionForm atomicWeilForm
    ring
  rw [hval] at h
  refine h.congr (fun r => ?_)
  simp only [Function.comp_def, log_smoothLockingRadius]
  rw [hmass]
  change _ = smoothLockedPacket c r N x g
  dsimp only [smoothLockedPacket, f]
  ring

/-- Normalization at degree one leaves precisely the negative discriminant energy. -/
theorem tendsto_smoothLockedPacket_weil_normalization {g : ℝ → ℝ} {w : ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ}
    (hw : w < atomSpacing N) (x : ℕ → ℝ) :
    Tendsto (fun r => smoothLockedPacket (2 * gammaHardyPhaseRate 0) r N x g) (𝓝[<] 1)
      (𝓝 (weilQuad (atomicTest N x g) -
        (∫ u, g u ^ 2) * ∑ n ∈ Icc 1 N, x n ^ 2 * selfIntersection n)) := by
  simpa only [sub_self, zero_mul, add_zero] using
    tendsto_smoothLockedPacket hg hgc hsupp hw x (2 * gammaHardyPhaseRate 0)

/-- The locked diagonal for one translated profile at a torsion orbit.
Both continuum terms are translation invariant. -/
def smoothLockedOrbit (ρ : ℝ → ℝ) (r : ℝ) (n : ℕ) (g : ℝ → ℝ) : ℝ :=
  (2 * coshHalfMoment g ^ 2 - 2 * sinhHalfMoment g ^ 2) - smoothGreenEnergy r g +
    (∫ u, g u ^ 2) * twistedEnergy (ρ r) n n

/-- Every scalar locking retains the same discriminant difference between smooth orbits. -/
theorem tendsto_smoothLockedOrbit_sub_one {ρ : ℝ → ℝ}
    (hρ : Tendsto ρ (𝓝[<] 1) (𝓝 1)) (g : ℝ → ℝ) {n : ℕ} (hn : 0 < n) :
    Tendsto (fun r => smoothLockedOrbit ρ r n g - smoothLockedOrbit ρ r 1 g) (𝓝[<] 1)
      (𝓝 (-(∫ u, g u ^ 2) * selfIntersection n)) := by
  have h := ((tendsto_twistedEnergy_self_add_log hn).sub
    (tendsto_twistedEnergy_self_add_log one_pos)).comp hρ
  change Tendsto _ _ (𝓝 (-selfIntersection n - -selfIntersection 1)) at h
  have h1 : selfIntersection 1 = 0 := by rw [selfIntersection_eq one_pos]; simp [tameDifferent]
  rw [h1, neg_zero, sub_zero] at h
  have h' := h.const_mul (∫ u, g u ^ 2)
  have hv : (∫ u, g u ^ 2) * -selfIntersection n =
      -(∫ u, g u ^ 2) * selfIntersection n := by ring
  rw [hv] at h'
  refine h'.congr (fun r => ?_)
  dsimp only [Function.comp_def, smoothLockedOrbit]
  ring

/-- Calibrating one orbit fixes every diagonal, including its arithmetic defect. -/
theorem tendsto_smoothLockedOrbit_of_one {ρ : ℝ → ℝ}
    (hρ : Tendsto ρ (𝓝[<] 1) (𝓝 1)) (g : ℝ → ℝ) {B : ℝ}
    (hB : Tendsto (fun r => smoothLockedOrbit ρ r 1 g) (𝓝[<] 1) (𝓝 B))
    {n : ℕ} (hn : 0 < n) :
    Tendsto (fun r => smoothLockedOrbit ρ r n g) (𝓝[<] 1)
      (𝓝 (B - (∫ u, g u ^ 2) * selfIntersection n)) := by
  have h := hB.add (tendsto_smoothLockedOrbit_sub_one hρ g hn)
  have hv : B + -(∫ u, g u ^ 2) * selfIntersection n =
      B - (∫ u, g u ^ 2) * selfIntersection n := by ring
  rw [hv] at h
  exact h.congr (fun r => by ring)

/-- No scalar locking gives Weil's energy on every translated nonzero smooth orbit.
Degrees one and four already contradict translation invariance. -/
theorem not_exists_scalar_locking_weil_orbits (g : ℝ → ℝ)
    (hM : 0 < ∫ u, g u ^ 2) :
    ¬ ∃ ρ : ℝ → ℝ, Tendsto ρ (𝓝[<] 1) (𝓝 1) ∧
      ∀ n : ℕ, 0 < n →
        Tendsto (fun r => smoothLockedOrbit ρ r n g) (𝓝[<] 1)
          (𝓝 (weilQuad (fun u => g (u - Real.log n)))) := by
  rintro ⟨ρ, hρ, hlim⟩
  have h1 := hlim 1 one_pos
  have h4 := hlim 4 (by norm_num)
  rw [weilQuad_comp_sub] at h1 h4
  have h4' := tendsto_smoothLockedOrbit_of_one hρ g h1 (by norm_num : 0 < (4 : ℕ))
  have hdiscr : selfIntersection 4 = Real.log 2 := by
    have h := selfIntersection_two_pow (k := 2) (by norm_num)
    norm_num at h
    exact h
  rw [hdiscr] at h4'
  have heq := tendsto_nhds_unique h4 h4'
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith [mul_pos hM hlog]

/-- The failure occurs among actual nonzero compact C² probes. -/
theorem not_exists_scalar_locking_all_smooth_orbits :
    ¬ ∃ ρ : ℝ → ℝ, Tendsto ρ (𝓝[<] 1) (𝓝 1) ∧
      ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
        ∀ n : ℕ, 0 < n →
          Tendsto (fun r => smoothLockedOrbit ρ r n g) (𝓝[<] 1)
            (𝓝 (weilQuad (fun u => g (u - Real.log n)))) := by
  rintro ⟨ρ, hρ, hlim⟩
  exact not_exists_scalar_locking_weil_orbits (evenNarrowBump 0)
    (integral_evenNarrowBump_sq_pos 0)
    ⟨ρ, hρ, hlim _ (contDiff_evenNarrowBump 0) (hasCompactSupport_evenNarrowBump 0)⟩

private theorem atomicTest_one (g : ℝ → ℝ) : atomicTest 1 (fun _ => 1) g = g := by
  funext u
  simp [atomicTest]

private theorem atomicTest_two (g : ℝ → ℝ) :
    atomicTest 2 (fun _ => 1) g = fun u => g u + g (u - Real.log 2) := by
  funext u
  norm_num [atomicTest, show (Icc 1 2 : Finset ℕ) = {1, 2} by decide]

private theorem positive_mass_excess :
    ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      0 < (∫ u, atomicTest 2 (fun _ => 1) g u ^ 2) - 2 * ∫ u, g u ^ 2 := by
  let b := evenNarrowBump 0
  let g : ℝ → ℝ := fun u => b u + b (u - Real.log 2)
  have hb : ContDiff ℝ 2 b := contDiff_evenNarrowBump 0
  have hbc : HasCompactSupport b := hasCompactSupport_evenNarrowBump 0
  have hb0 (u : ℝ) : 0 ≤ b u := by
    dsimp [b, evenNarrowBump, evenPartReal]
    exact div_nonneg (add_nonneg (narrowBump 0).nonneg (narrowBump 0).nonneg) (by norm_num)
  have hg : ContDiff ℝ 2 g := hb.add (hb.comp (contDiff_id.sub contDiff_const))
  have hgc : HasCompactSupport g :=
    hbc.add (hbc.comp_homeomorph (Homeomorph.subRight (Real.log 2)))
  have hbi : Integrable (fun u => b u ^ 2) :=
    hb.continuous.pow 2 |>.integrable_of_hasCompactSupport
      (hbc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num))
  have hgi : Integrable (fun u => g u * g (u + Real.log 2)) :=
    (hg.continuous.mul (hg.continuous.comp (continuous_add_const _))).integrable_of_hasCompactSupport
      hgc.mul_right
  have hcorr : 0 < autocorr g (Real.log 2) := by
    have hle : (∫ u, b u ^ 2) ≤ autocorr g (Real.log 2) := by
      apply integral_mono hbi hgi
      intro u
      dsimp only [g]
      rw [add_sub_cancel_right]
      have h := mul_le_mul (show b u ≤ b u + b (u - Real.log 2) by linarith [hb0 (u - Real.log 2)])
        (show b u ≤ b (u + Real.log 2) + b u by linarith [hb0 (u + Real.log 2)])
        (hb0 u) (add_nonneg (hb0 u) (hb0 (u - Real.log 2)))
      simpa only [pow_two] using h
    exact (integral_evenNarrowBump_sq_pos 0).trans_le hle
  refine ⟨g, hg, hgc, ?_⟩
  rw [atomicTest_two]
  simp_rw [sub_eq_add_neg]
  rw [BiScaleUncertainty.integral_add_shift_sq hgc hg.continuous,
    autocorr_neg, ← BiScaleUncertainty.integral_sq_eq_autocorr_zero]
  linarith only [hcorr]

private theorem not_tendsto_positive_selfEnergy {a : ℝ} (ha : 0 < a) (B : ℝ) :
    ¬ Tendsto (fun r => a * selfEnergy r) (𝓝[<] 1) (𝓝 B) := by
  intro h
  obtain ⟨r, hr, hB⟩ := ((tendsto_selfEnergy_atTop.eventually_gt_atTop ((B + 1) / a)).and
    (h.eventually_lt_const (show B < B + 1 by linarith))).exists
  have := (div_lt_iff₀ ha).mp hr
  linarith

/-- Overlap prevents a common radius from giving finite limits on all compact C² packets.
The contradiction uses just the same profile at one orbit and at the two orders `1,2`:
their discrete masses are in ratio two, while their L² masses have a positive overlap term. -/
theorem not_exists_scalar_locking_all_smooth_packets :
    ¬ ∃ ρ : ℝ → ℝ, Tendsto ρ (𝓝[<] 1) (𝓝 1) ∧
      ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
        ∀ (N : ℕ) (x : ℕ → ℝ), ∃ B : ℝ,
          Tendsto (fun r => smoothTorsionPacket ρ r N x g) (𝓝[<] 1) (𝓝 B) := by
  rintro ⟨ρ, hρ, hlim⟩
  obtain ⟨g, hg, hgc, hexcess⟩ := positive_mass_excess
  obtain ⟨B₁, h₁⟩ := hlim g hg hgc 1 (fun _ => 1)
  obtain ⟨B₂, h₂⟩ := hlim g hg hgc 2 (fun _ => 1)
  have hR₁ := tendsto_smoothTorsionPacket_renormalized hρ hg hgc 1 (fun _ => 1)
  have hR₂ := tendsto_smoothTorsionPacket_renormalized hρ hg hgc 2 (fun _ => 1)
  have hs₁ : (∑ _n ∈ (Icc 1 1 : Finset ℕ), (1 : ℝ) ^ 2) = 1 := by norm_num
  have hs₂ : (∑ _n ∈ (Icc 1 2 : Finset ℕ), (1 : ℝ) ^ 2) = 2 := by
    norm_num [show (Icc 1 2 : Finset ℕ) = {1, 2} by decide]
  simp only [hs₁, mul_one, atomicTest_one] at hR₁
  simp only [hs₂] at hR₂
  have h := (hR₂.sub (hR₁.const_mul 2)).sub (h₂.sub (h₁.const_mul 2))
  apply not_tendsto_positive_selfEnergy hexcess _
  exact h.congr (fun r => by ring)

end GaloisForLFunctions.HyperbolicArakelovTheory

#print axioms GaloisForLFunctions.HyperbolicArakelovTheory.tendsto_smoothLockedPacket_weil_normalization
#print axioms GaloisForLFunctions.HyperbolicArakelovTheory.not_exists_scalar_locking_weil_orbits
#print axioms GaloisForLFunctions.HyperbolicArakelovTheory.not_exists_scalar_locking_all_smooth_orbits
#print axioms GaloisForLFunctions.HyperbolicArakelovTheory.not_exists_scalar_locking_all_smooth_packets
