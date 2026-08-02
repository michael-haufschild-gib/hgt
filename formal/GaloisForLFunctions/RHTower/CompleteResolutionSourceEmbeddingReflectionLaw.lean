import GaloisForLFunctions.RHTower.CompleteResolutionBoundedBanachFusionLaw
import GaloisForLFunctions.RHTower.HighExponentShellPrimeSpectrum

/-!
# The complete Riemann source embeds the spectral half-plane

The complete high-exponent resolution defines an injective map from the open right half-plane
into one affine hyperplane of `ℓ¹`.  Its norm-one codiagonal is constantly one, so every spectral
coordinate is carried by the closed zero-mass radical.  Injectivity is not a formal property of
partitions of unity: it follows from the prime-two and prime-three asymptotic atoms of the same
shell tail.

Functional-equation reflection therefore has a canonical unsquared source displacement inside
that radical.  It vanishes exactly on the critical line, and the relative size of the two
prime-two tail characters gives its one-sided orientation.
-/

open Complex Filter Topology
open GaloisForLFunctions
open scoped ENNReal

namespace RHTower

noncomputable section

/-- Spectral points at which the complete source vector is absolutely summable. -/
abbrev CompleteResolutionRightHalfPlane := {s : ℂ // 0 < s.re}

/-- The complete high-exponent source as one map into a fixed `ℓ¹` space. -/
def completeResolutionSourceEmbedding (K : ℕ) :
    CompleteResolutionRightHalfPlane → CompleteResolutionSourceSpace :=
  fun s => completeResolutionSourceVector K s.1 s.2

/-- Every point of the source embedding has scalar mass one. -/
@[simp] theorem sourceFusionCodiagonal_completeResolutionSourceEmbedding
    (K : ℕ) (s : CompleteResolutionRightHalfPlane) :
    sourceFusionCodiagonal (completeResolutionSourceEmbedding K s) = 1 := by
  rw [completeResolutionSourceEmbedding, sourceFusionCodiagonal,
    lp.tsumCLM_apply]
  simpa only [completeResolutionSourceVector_apply] using
    (hasSum_completeResolutionMultiplier_one K s.2).tsum_eq

/-- Equality of complete source vectors forces equality of the prime-two tail character. -/
theorem two_cpow_neg_eq_of_completeResolutionSourceVector_eq
    (K : ℕ) {s t : ℂ} (hs : 0 < s.re) (ht : 0 < t.re)
    (hvector :
      completeResolutionSourceVector K s hs =
        completeResolutionSourceVector K t ht) :
    (2 : ℂ) ^ (-s) = (2 : ℂ) ^ (-t) := by
  have hshell :
      ∀ n : ℕ,
        shellMultiplier (K + n) s =
          shellMultiplier (K + n) t := by
    intro n
    have hcoord := congrArg
      (fun x : CompleteResolutionSourceSpace => x (n + 1)) hvector
    simpa [completeResolutionMultiplier, Nat.add_assoc] using hcoord
  have hadjacent :
      ∀ n : ℕ,
        shellAdjacentTransfer (K + n) s =
          shellAdjacentTransfer (K + n) t := by
    intro n
    simp only [shellAdjacentTransfer]
    rw [hshell n]
    have hsucc := hshell (n + 1)
    rw [show K + n + 1 = K + (n + 1) by omega, hsucc]
  have hshift :
      Tendsto (fun n : ℕ => K + n) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat K
  exact tendsto_nhds_unique_of_eventuallyEq
    ((tendsto_shellAdjacentTransfer hs).comp hshift)
    ((tendsto_shellAdjacentTransfer ht).comp hshift)
    (Filter.Eventually.of_forall hadjacent)

/-- Equality of complete source vectors also forces equality of the prime-three tail character
after exact removal of the common prime-two atom. -/
theorem three_cpow_neg_eq_of_completeResolutionSourceVector_eq
    (K : ℕ) {s t : ℂ} (hs : 0 < s.re) (ht : 0 < t.re)
    (hvector :
      completeResolutionSourceVector K s hs =
        completeResolutionSourceVector K t ht) :
    (3 : ℂ) ^ (-s) = (3 : ℂ) ^ (-t) := by
  have hshell :
      ∀ n : ℕ,
        shellMultiplier (K + n) s =
          shellMultiplier (K + n) t := by
    intro n
    have hcoord := congrArg
      (fun x : CompleteResolutionSourceSpace => x (n + 1)) hvector
    simpa [completeResolutionMultiplier, Nat.add_assoc] using hcoord
  have htwo :
      (2 : ℂ) ^ (-s) = (2 : ℂ) ^ (-t) :=
    two_cpow_neg_eq_of_completeResolutionSourceVector_eq
      K hs ht hvector
  have htwoPower (n : ℕ) :
      (2 : ℂ) ^ (-((n : ℂ) * s)) =
        (2 : ℂ) ^ (-((n : ℂ) * t)) := by
    calc
      (2 : ℂ) ^ (-((n : ℂ) * s)) =
          (2 : ℂ) ^ ((n : ℂ) * (-s)) := by congr 2; ring
      _ = ((2 : ℂ) ^ (-s)) ^ n := by
        simpa using Complex.cpow_nat_mul (2 : ℂ) n (-s)
      _ = ((2 : ℂ) ^ (-t)) ^ n := by rw [htwo]
      _ = (2 : ℂ) ^ ((n : ℂ) * (-t)) := by
        symm
        simpa using Complex.cpow_nat_mul (2 : ℂ) n (-t)
      _ = (2 : ℂ) ^ (-((n : ℂ) * t)) := by congr 2; ring
  have hresidual :
      ∀ n : ℕ,
        shellSecondAtomResidual (K + n) s =
          shellSecondAtomResidual (K + n) t := by
    intro n
    rw [shellSecondAtomResidual, shellSecondAtomResidual, hshell n,
      htwoPower (K + n), htwo]
  have hadjacent :
      ∀ n : ℕ,
        shellSecondAtomAdjacentTransfer (K + n) s =
          shellSecondAtomAdjacentTransfer (K + n) t := by
    intro n
    simp only [shellSecondAtomAdjacentTransfer]
    rw [hresidual n]
    have hsucc := hresidual (n + 1)
    rw [show K + n + 1 = K + (n + 1) by omega, hsucc]
  have hshift :
      Tendsto (fun n : ℕ => K + n) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat K
  exact tendsto_nhds_unique_of_eventuallyEq
    ((tendsto_shellSecondAtomAdjacentTransfer hs).comp hshift)
    ((tendsto_shellSecondAtomAdjacentTransfer ht).comp hshift)
    (Filter.Eventually.of_forall hadjacent)

/-- **Spectral source embedding.**  The complete `ℓ¹` source vector determines the entire complex
spectral coordinate on the open right half-plane.  Prime two determines the real part and one
phase class; prime three removes the remaining phase alias. -/
theorem completeResolutionSourceEmbedding_injective (K : ℕ) :
    Function.Injective (completeResolutionSourceEmbedding K) := by
  intro s t hvector
  have htwo :
      (2 : ℂ) ^ (-s.1) = (2 : ℂ) ^ (-t.1) :=
    two_cpow_neg_eq_of_completeResolutionSourceVector_eq
      K s.2 t.2 hvector
  have hthree :
      (3 : ℂ) ^ (-s.1) = (3 : ℂ) ^ (-t.1) :=
    three_cpow_neg_eq_of_completeResolutionSourceVector_eq
      K s.2 t.2 hvector
  have hcharacterTwo :
      GaloisForLFunctions.HTGeometry.leastAtomTransferCharacter
          2 1 s.1 =
        GaloisForLFunctions.HTGeometry.leastAtomTransferCharacter
          2 1 t.1 := by
    have htwoReal :
        ((2 : ℝ) : ℂ) ^ (-s.1) =
          ((2 : ℝ) : ℂ) ^ (-t.1) := by
      simpa using htwo
    rw [GaloisForLFunctions.HTGeometry.leastAtomTransferCharacter,
      GaloisForLFunctions.HTGeometry.leastAtomTransferCharacter,
      show ((((1 : ℝ) / 2 : ℝ) : ℂ) - s.1) =
          (1 / 2 : ℂ) + (-s.1) by norm_num; ring,
      show ((((1 : ℝ) / 2 : ℝ) : ℂ) - t.1) =
          (1 / 2 : ℂ) + (-t.1) by norm_num; ring,
      Complex.cpow_add _ _ (by norm_num),
      Complex.cpow_add _ _ (by norm_num), htwoReal]
  have hcharacterThree :
      GaloisForLFunctions.HTGeometry.leastAtomTransferCharacter
          3 1 s.1 =
        GaloisForLFunctions.HTGeometry.leastAtomTransferCharacter
          3 1 t.1 := by
    have hthreeReal :
        ((3 : ℝ) : ℂ) ^ (-s.1) =
          ((3 : ℝ) : ℂ) ^ (-t.1) := by
      simpa using hthree
    rw [GaloisForLFunctions.HTGeometry.leastAtomTransferCharacter,
      GaloisForLFunctions.HTGeometry.leastAtomTransferCharacter,
      show ((((1 : ℝ) / 2 : ℝ) : ℂ) - s.1) =
          (1 / 2 : ℂ) + (-s.1) by norm_num; ring,
      show ((((1 : ℝ) / 2 : ℝ) : ℂ) - t.1) =
          (1 / 2 : ℂ) + (-t.1) by norm_num; ring,
      Complex.cpow_add _ _ (by norm_num),
      Complex.cpow_add _ _ (by norm_num), hthreeReal]
  apply Subtype.ext
  exact twoPrimeShellTransferSpectrum_injective
    (Prod.ext hcharacterTwo hcharacterThree)

/-- Zero-free domain on which every reciprocal-zeta coordinate of the resolution is an ordinary
holomorphic reciprocal rather than merely a pointwise field inverse. -/
abbrev CompleteResolutionSafeHalfPlane (K : ℕ) :=
  {s : ℂ // 1 < (K : ℝ) * s.re}

/-- Restriction of the source embedding to its ordinary reciprocal-zeta domain. -/
def completeResolutionSafeSourceEmbedding
    (K : ℕ) (hK : 1 ≤ K) :
    CompleteResolutionSafeHalfPlane K → CompleteResolutionSourceSpace :=
  fun s =>
    completeResolutionSourceVector K s.1 (by
      have hKnonneg : (0 : ℝ) ≤ K := by positivity
      nlinarith [s.2])

/-- The source embedding remains injective on the zero-free holomorphic domain used in the
ordinary complex-analytic statement. -/
theorem completeResolutionSafeSourceEmbedding_injective
    (K : ℕ) (hK : 1 ≤ K) :
    Function.Injective (completeResolutionSafeSourceEmbedding K hK) := by
  intro s t hvector
  let sRight : CompleteResolutionRightHalfPlane :=
    ⟨s.1, by
      have hKnonneg : (0 : ℝ) ≤ K := by positivity
      nlinarith [s.2]⟩
  let tRight : CompleteResolutionRightHalfPlane :=
    ⟨t.1, by
      have hKnonneg : (0 : ℝ) ≤ K := by positivity
      nlinarith [t.2]⟩
  have hright :
      completeResolutionSourceEmbedding K sRight =
        completeResolutionSourceEmbedding K tRight := by
    exact hvector
  have heq :=
    completeResolutionSourceEmbedding_injective K hright
  apply Subtype.ext
  exact congrArg
    (fun u : CompleteResolutionRightHalfPlane => u.1) heq

/-- Adjacent cofinal coordinate ratio read directly from the complete source vector. -/
def completeResolutionSourceAdjacentTailRatio
    (K n : ℕ) (s : CompleteResolutionRightHalfPlane) : ℂ :=
  completeResolutionSourceEmbedding K s (n + 2) /
    completeResolutionSourceEmbedding K s (n + 1)

/-- The source-vector tail ratio is exactly the shifted high-shell transfer. -/
theorem completeResolutionSourceAdjacentTailRatio_eq
    (K n : ℕ) (s : CompleteResolutionRightHalfPlane) :
    completeResolutionSourceAdjacentTailRatio K n s =
      shellAdjacentTransfer (K + n) s.1 := by
  simp [completeResolutionSourceAdjacentTailRatio,
    completeResolutionSourceEmbedding, completeResolutionMultiplier,
    shellAdjacentTransfer, Nat.add_assoc]

/-- Prime-two tail character recovered from the complete source vector itself. -/
theorem tendsto_completeResolutionSourceAdjacentTailRatio
    (K : ℕ) (s : CompleteResolutionRightHalfPlane) :
    Tendsto
      (fun n : ℕ => completeResolutionSourceAdjacentTailRatio K n s)
      atTop (nhds ((2 : ℂ) ^ (-s.1))) := by
  have hshift :
      Tendsto (fun n : ℕ => K + n) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat K
  have hlimit :=
    (tendsto_shellAdjacentTransfer s.2).comp hshift
  change Tendsto
    (fun n : ℕ => shellAdjacentTransfer (K + n) s.1)
    atTop (nhds ((2 : ℂ) ^ (-s.1))) at hlimit
  simpa only [completeResolutionSourceAdjacentTailRatio_eq] using hlimit

/-- Half-density normalization of the source tail. -/
def completeResolutionNormalizedSourceTailRatio
    (K n : ℕ) (s : CompleteResolutionRightHalfPlane) : ℂ :=
  (Real.sqrt 2 : ℂ) *
    completeResolutionSourceAdjacentTailRatio K n s

/-- **Canonical source-tail orientation.**  The normalized ratios of the actual `ℓ¹` source
converge to the shell character whose logarithmic modulus is exactly the signed horizontal
distance from the critical line. -/
theorem completeResolutionNormalizedSourceTailRatio_orientation
    (K : ℕ) (s : CompleteResolutionRightHalfPlane) :
    Tendsto
        (fun n : ℕ =>
          completeResolutionNormalizedSourceTailRatio K n s)
        atTop (nhds (shellTransferCharacter s.1)) ∧
      Real.log ‖shellTransferCharacter s.1‖ =
        (1 / 2 - s.1.re) * Real.log 2 := by
  have hlimit :=
    (tendsto_completeResolutionSourceAdjacentTailRatio K s).const_mul
      (Real.sqrt 2 : ℂ)
  have hsqrt :
      (Real.sqrt 2 : ℂ) = (2 : ℂ) ^ (1 / 2 : ℂ) := by
    have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    have hbase : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
    rw [hhalf, hbase,
      ← Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.sqrt_eq_rpow]
  have hproduct :
      (Real.sqrt 2 : ℂ) * (2 : ℂ) ^ (-s.1) =
        shellTransferCharacter s.1 := by
    rw [shellTransferCharacter, hsqrt,
      ← Complex.cpow_add _ _ (by norm_num)]
    congr 2
  exact ⟨by
    simpa only [completeResolutionNormalizedSourceTailRatio,
      hproduct] using hlimit,
    log_norm_shellTransferCharacter s.1⟩

/-- Canonical closed-radical coordinate of the complete source. -/
def completeResolutionSourceRadicalEmbedding (K : ℕ) :
    CompleteResolutionRightHalfPlane → CompleteResolutionSourceSpace :=
  fun s =>
    completeResolutionSourceEmbedding K s -
      sourceFusionPointSection 1

/-- The radical coordinate has exactly zero scalar mass. -/
@[simp] theorem sourceFusionCodiagonal_completeResolutionSourceRadicalEmbedding
    (K : ℕ) (s : CompleteResolutionRightHalfPlane) :
    sourceFusionCodiagonal
        (completeResolutionSourceRadicalEmbedding K s) = 0 := by
  rw [completeResolutionSourceRadicalEmbedding, map_sub,
    sourceFusionCodiagonal_completeResolutionSourceEmbedding,
    sourceFusionCodiagonal_pointSection, sub_self]

/-- **All spectral information is transverse.**  Translation into the closed zero-mass radical
does not lose any point of the open right half-plane. -/
theorem completeResolutionSourceRadicalEmbedding_injective (K : ℕ) :
    Function.Injective (completeResolutionSourceRadicalEmbedding K) := by
  intro s t h
  apply completeResolutionSourceEmbedding_injective K
  exact sub_left_injective h

/-- Points for which functional-equation reflection remains in the source half-plane. -/
abbrev CompleteResolutionOpenCriticalStrip :=
  {s : ℂ // 0 < s.re ∧ s.re < 1}

/-- Canonical unsquared displacement between a source and its functional-equation reflection. -/
def completeResolutionReflectionSourceDisplacement
    (K : ℕ) (s : CompleteResolutionOpenCriticalStrip) :
    CompleteResolutionSourceSpace :=
  completeResolutionSourceEmbedding K ⟨s.1, s.2.1⟩ -
    completeResolutionSourceEmbedding K
      ⟨1 - star s.1, by
        have hstarRe : (star s.1).re = s.1.re := by simp
        simp only [sub_re, one_re]
        rw [hstarRe]
        linarith [s.2.2]⟩

/-- Reflection displacement is invisible to scalar fusion: it lies in the closed source radical. -/
@[simp] theorem sourceFusionCodiagonal_completeResolutionReflectionSourceDisplacement
    (K : ℕ) (s : CompleteResolutionOpenCriticalStrip) :
    sourceFusionCodiagonal
        (completeResolutionReflectionSourceDisplacement K s) = 0 := by
  rw [completeResolutionReflectionSourceDisplacement, map_sub,
    sourceFusionCodiagonal_completeResolutionSourceEmbedding,
    sourceFusionCodiagonal_completeResolutionSourceEmbedding, sub_self]

/-- **Source reflection fixed-point law.**  The canonical unsquared source displacement vanishes
exactly on the critical line. -/
theorem completeResolutionReflectionSourceDisplacement_eq_zero_iff
    (K : ℕ) (s : CompleteResolutionOpenCriticalStrip) :
    completeResolutionReflectionSourceDisplacement K s = 0 ↔
      s.1.re = 1 / 2 := by
  constructor
  · intro hzero
    have hembedding :
        completeResolutionSourceEmbedding K ⟨s.1, s.2.1⟩ =
          completeResolutionSourceEmbedding K
            ⟨1 - star s.1, by
              have hstarRe : (star s.1).re = s.1.re := by simp
              simp only [sub_re, one_re]
              rw [hstarRe]
              linarith [s.2.2]⟩ :=
      sub_eq_zero.mp hzero
    have hpoint :=
      congrArg Subtype.val
        (completeResolutionSourceEmbedding_injective K hembedding)
    have hre := congrArg Complex.re hpoint
    have hstarRe : (star s.1).re = s.1.re := by simp
    simp only [sub_re, one_re] at hre
    rw [hstarRe] at hre
    linarith
  · intro hre
    apply sub_eq_zero.mpr
    apply congrArg (completeResolutionSourceEmbedding K)
    apply Subtype.ext
    apply Complex.ext
    · have hstarRe : (star s.1).re = s.1.re := by simp
      simp only [sub_re, one_re]
      rw [hstarRe, hre]
      norm_num
    · simp

/-- The displacement norm is a strict, unsquared detector of departure from the critical line. -/
theorem norm_completeResolutionReflectionSourceDisplacement_ne_zero_iff
    (K : ℕ) (s : CompleteResolutionOpenCriticalStrip) :
    ‖completeResolutionReflectionSourceDisplacement K s‖ ≠ 0 ↔
      s.1.re ≠ 1 / 2 := by
  rw [norm_ne_zero_iff,
    ne_eq, completeResolutionReflectionSourceDisplacement_eq_zero_iff]

/-- Prime-two cofinal tails orient the two sides before scalar fusion. -/
theorem completeResolution_reflectionTailNorm_lt_iff
    (rho : ℂ) :
    ‖(2 : ℂ) ^ (-rho)‖ <
        ‖(2 : ℂ) ^ (-(1 - star rho))‖ ↔
      1 / 2 < rho.re := by
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2),
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hstarRe : (star rho).re = rho.re := by simp
  simp only [neg_re, sub_re, one_re]
  rw [hstarRe,
    (Real.strictMono_rpow_of_base_gt_one
      (by norm_num : (1 : ℝ) < 2)).lt_iff_lt]
  constructor <;> intro h <;> linarith

end

end RHTower
