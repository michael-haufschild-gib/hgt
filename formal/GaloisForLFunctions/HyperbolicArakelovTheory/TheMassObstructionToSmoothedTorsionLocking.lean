import GaloisForLFunctions.HyperbolicArakelovTheory.TheGreenDampingOnSmoothProbes
import GaloisForLFunctions.ArithmeticIntersectionTheory.TheHeckeCocycleOfRenormalization
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.WeilsFormIsContinuousInTheLevyNorm
import GaloisForLFunctions.RHTower.MarkovOddSectorFarkasAndOneSidedPBAP
import GaloisForLFunctions.BiScaleUncertainty.KreinIncrementAndChordCascade

/-!
# The mass obstruction to smoothed torsion locking

Place a compact C² profile at the integer logarithms below their spacing. Its
prime energy is exactly the torsion prime form times the profile mass. Coupling
the raw Abel torsion energy to the smooth Green energy therefore has a definite
meaning on these probes, without assuming an extension to arbitrary profiles.

For arbitrary packets the divergent coefficients are discrete mass and actual L²
mass. The exponential locking has a finite limit exactly when those masses agree. An
explicit overlapping profile proves that no common radius gives finite limits
on all packets. Below the atom spacing the masses agree, and the finite part is
Weil's form minus the profile mass times the discriminant diagonal.
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
  | empty =>
    convert (HasCompactSupport.zero : HasCompactSupport (0 : ℝ → ℝ)) using 1
    funext u
    exact Finset.sum_empty _
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
  have hv : (∫ u, g u ^ 2) * renormalizedTorsionForm (Icc 1 N) x -
      -levyEnergy (atomicTest N x g) +
      (2 * coshHalfMoment (atomicTest N x g) ^ 2 - 2 * sinhHalfMoment (atomicTest N x g) ^ 2) =
      (2 * coshHalfMoment (atomicTest N x g) ^ 2 - 2 * sinhHalfMoment (atomicTest N x g) ^ 2) +
      levyEnergy (atomicTest N x g) + (∫ u, g u ^ 2) * renormalizedTorsionForm (Icc 1 N) x := by ring
  rw [hv] at h
  exact h.congr (fun r => show _ = smoothTorsionPacket ρ r N x g +
      Real.log |1 - ρ r| * ((∫ u, g u ^ 2) * ∑ n ∈ Icc 1 N, x n ^ 2) +
      (∫ u, atomicTest N x g u ^ 2) * selfEnergy r by
    dsimp only [Function.comp_def, smoothTorsionPacket]; ring)

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
  change Tendsto (fun r => 1 - Real.exp (-selfEnergy r - c)) (𝓝[<] 1) (𝓝 1)
  simpa only [Function.comp_def, sub_zero] using he.const_sub 1

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

/-- The finite defect after removing the mass divergence: the prime discrepancy,
the scalar normalization, and the torsion discriminant. -/
def smoothPacketWeilDefect (c : ℝ) (N : ℕ) (x : ℕ → ℝ) (g : ℝ → ℝ) : ℝ :=
  let f := atomicTest N x g
  primeSum f - (∫ u, g u ^ 2) * atomicWeilForm N x +
    c * ((∫ u, g u ^ 2) * ∑ n ∈ Icc 1 N, x n ^ 2) -
    2 * gammaHardyPhaseRate 0 * (∫ u, f u ^ 2) -
    (∫ u, g u ^ 2) * ∑ n ∈ Icc 1 N, x n ^ 2 * selfIntersection n

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

private theorem atomicTest_one (g : ℝ → ℝ) : atomicTest 1 (fun _ => 1) g = g := by
  funext u
  simp [atomicTest]

private theorem atomicTest_two (g : ℝ → ℝ) :
    atomicTest 2 (fun _ => 1) g = fun u => g u + g (u - Real.log 2) := by
  funext u
  norm_num [atomicTest, show (Icc 1 2 : Finset ℕ) = {1, 2} by decide]

private theorem overlap_mass_excess {b : ℝ → ℝ} (hb : ContDiff ℝ 2 b)
    (hbc : HasCompactSupport b) (hb0 : ∀ u, 0 ≤ b u) (hM : 0 < ∫ u, b u ^ 2) :
    0 < (∫ u, atomicTest 2 (fun _ => 1) (fun v => b v + b (v - Real.log 2)) u ^ 2) -
      2 * ∫ u, (b u + b (u - Real.log 2)) ^ 2 := by
  let g : ℝ → ℝ := fun u => b u + b (u - Real.log 2)
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
    exact hM.trans_le hle
  change 0 < (∫ u, atomicTest 2 (fun _ => 1) g u ^ 2) - 2 * ∫ u, g u ^ 2
  rw [atomicTest_two]
  simp_rw [sub_eq_add_neg]
  rw [BiScaleUncertainty.integral_add_shift_sq hgc hg.continuous,
    autocorr_neg, ← BiScaleUncertainty.integral_sq_eq_autocorr_zero]
  linarith only [hcorr]

private theorem positive_mass_excess :
    ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      0 < (∫ u, atomicTest 2 (fun _ => 1) g u ^ 2) - 2 * ∫ u, g u ^ 2 := by
  have hb := contDiff_evenNarrowBump 0
  have hbc := hasCompactSupport_evenNarrowBump 0
  have hb0 (u : ℝ) : 0 ≤ evenNarrowBump 0 u := by
    unfold evenNarrowBump evenPartReal
    exact div_nonneg
      (add_nonneg (WeilOneSided.narrowBump 0).nonneg (WeilOneSided.narrowBump 0).nonneg)
      (by norm_num)
  exact ⟨fun u => evenNarrowBump 0 u + evenNarrowBump 0 (u - Real.log 2),
    hb.add (hb.comp (contDiff_id.sub contDiff_const)),
    hbc.add (hbc.comp_homeomorph (Homeomorph.subRight (Real.log 2))),
    overlap_mass_excess hb hbc hb0 (integral_evenNarrowBump_sq_pos 0)⟩

private theorem not_tendsto_positive_selfEnergy {a : ℝ} (ha : 0 < a) (B : ℝ) :
    ¬ Tendsto (fun r => a * selfEnergy r) (𝓝[<] 1) (𝓝 B) := by
  intro h
  obtain ⟨r, hr, hB⟩ := ((tendsto_selfEnergy_atTop.eventually_gt_atTop ((B + 1) / a)).and
    (h.eventually_lt_const (show B < B + 1 by linarith))).exists
  have := (div_lt_iff₀ ha).mp hr
  linarith

private theorem eq_zero_of_tendsto_mul_selfEnergy {a B : ℝ}
    (h : Tendsto (fun r => a * selfEnergy r) (𝓝[<] 1) (𝓝 B)) : a = 0 := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · have h' : Tendsto (fun r => (-a) * selfEnergy r) (𝓝[<] 1) (𝓝 (-B)) := by
      simpa only [neg_mul] using h.neg
    exact False.elim (not_tendsto_positive_selfEnergy (neg_pos.mpr ha) _ h')
  · exact ha
  · exact False.elim (not_tendsto_positive_selfEnergy ha _ h)

/-- The exact asymptotic on every smooth packet, including overlapping packets.
Its divergence is precisely discrete mass minus continuum mass. -/
theorem tendsto_smoothLockedPacket_sub_mass_defect {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (N : ℕ) (x : ℕ → ℝ) (c : ℝ) :
    Tendsto (fun r => smoothLockedPacket c r N x g -
        ((∫ u, g u ^ 2) * (∑ n ∈ Icc 1 N, x n ^ 2) -
          (∫ u, atomicTest N x g u ^ 2)) * selfEnergy r)
      (𝓝[<] 1)
      (𝓝 (weilQuad (atomicTest N x g) + smoothPacketWeilDefect c N x g)) := by
  have h := (tendsto_smoothTorsionPacket_renormalized (tendsto_smoothLockingRadius c)
    hg hgc N x).add_const (c * ((∫ u, g u ^ 2) * ∑ n ∈ Icc 1 N, x n ^ 2))
  have hv : (2 * coshHalfMoment (atomicTest N x g) ^ 2 -
      2 * sinhHalfMoment (atomicTest N x g) ^ 2) + levyEnergy (atomicTest N x g) +
      (∫ u, g u ^ 2) * renormalizedTorsionForm (Icc 1 N) x +
      c * ((∫ u, g u ^ 2) * ∑ n ∈ Icc 1 N, x n ^ 2) =
      weilQuad (atomicTest N x g) + smoothPacketWeilDefect c N x g := by
    rw [weilQuad_eq (contDiff_atomicTest hg N x) (compact_atomicTest hgc N x)]
    unfold smoothPacketWeilDefect renormalizedTorsionForm atomicWeilForm
    ring
  rw [hv] at h
  refine h.congr (fun r => ?_)
  simp only [log_smoothLockingRadius, smoothTorsionPacket, smoothLockedPacket]
  ring

/-- A packet has a finite scalar-locked limit exactly when smoothing preserves its discrete mass.
Separation is sufficient, but the exact boundary is the vanishing total overlap. -/
theorem finite_smoothLockedPacket_iff_mass_balance {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (N : ℕ) (x : ℕ → ℝ) (c : ℝ) :
    (∃ B : ℝ, Tendsto (fun r => smoothLockedPacket c r N x g) (𝓝[<] 1) (𝓝 B)) ↔
      (∫ u, atomicTest N x g u ^ 2) = (∫ u, g u ^ 2) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  have hR := tendsto_smoothLockedPacket_sub_mass_defect hg hgc N x c
  constructor
  · rintro ⟨B, hB⟩
    have h := hR.sub hB
    have hz := eq_zero_of_tendsto_mul_selfEnergy (a :=
      (∫ u, atomicTest N x g u ^ 2) - (∫ u, g u ^ 2) * ∑ n ∈ Icc 1 N, x n ^ 2)
      (h.congr (fun r => by ring))
    exact sub_eq_zero.mp hz
  · intro hm
    simp only [hm, sub_self, zero_mul, sub_zero] at hR
    exact ⟨_, hR⟩

/-- One compact C² profile already prevents every radius from giving finite limits at both
the one-orbit packet and the two orders `1,2`. Their discrete masses are in ratio two,
while their L² masses have a strictly positive overlap term. -/
theorem exists_smooth_profile_without_scalar_locking :
    ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      ∀ ρ : ℝ → ℝ, Tendsto ρ (𝓝[<] 1) (𝓝 1) →
        ¬ ((∃ B : ℝ, Tendsto (fun r => smoothTorsionPacket ρ r 1 (fun _ => 1) g)
              (𝓝[<] 1) (𝓝 B)) ∧
          (∃ B : ℝ, Tendsto (fun r => smoothTorsionPacket ρ r 2 (fun _ => 1) g)
              (𝓝[<] 1) (𝓝 B))) := by
  obtain ⟨g, hg, hgc, hexcess⟩ := positive_mass_excess
  refine ⟨g, hg, hgc, ?_⟩
  rintro ρ hρ ⟨⟨B₁, h₁⟩, ⟨B₂, h₂⟩⟩
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
#print axioms GaloisForLFunctions.HyperbolicArakelovTheory.exists_smooth_profile_without_scalar_locking
#print axioms GaloisForLFunctions.HyperbolicArakelovTheory.finite_smoothLockedPacket_iff_mass_balance
