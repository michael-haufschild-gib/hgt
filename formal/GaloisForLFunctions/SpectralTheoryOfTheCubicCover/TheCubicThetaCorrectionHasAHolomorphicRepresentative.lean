import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheThetaCorrectionHasOnlyTheCubicPole
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheEisensteinPairingContinuesAcrossFourThirds
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# A holomorphic representative of the Eisenstein correction

The meromorphic normal form fills removable real values of the actual
`[2,3]` correction. It is holomorphic on `Re s>1` away from `4/3`, agrees
with the correction off the real axis, and preserves its punctured germ
at `4/3`. Thus contour integrals use the analytic extension even when the
totalized operator inverse has a different value at a removable point.
-/

noncomputable section
open Filter Topology
namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover
open MetaplecticMobiusDescent.CubicEisenstein

private theorem eisensteinCorrection_local_representative (s : ℂ) (hs : 1 < s.re)
    (hp : s ≠ 4 / 3) :
    ∃ C : ℂ → KernelQuotientL2, AnalyticAt ℂ C s ∧
      C =ᶠ[𝓝[≠] s] eisensteinCorrection := by
  by_cases hi : s.im = 0
  · have he : (s.re : ℂ) = s := by
      apply Complex.ext
      · simp
      · simp [hi]
    have hp' : s.re ≠ 4 / 3 := by
      intro h
      apply hp
      rw [← he, h]
      norm_num
    obtain ⟨C, hC, hEq⟩ := kernelEisensteinCorrection_removable 2 3 (by norm_num)
      (by norm_num) s.re hs hp'
    rw [he] at hC hEq
    exact ⟨C, hC, hEq⟩
  · exact ⟨eisensteinCorrection,
      kernelEisensteinL2Correction_analyticAt_nonreal 2 3 (by norm_num) (by norm_num) s
        (by linarith) hi, Filter.EventuallyEq.rfl⟩

theorem eisensteinCorrection_meromorphicOn_right :
    MeromorphicOn eisensteinCorrection {s : ℂ | 1 < s.re} := by
  intro s hs
  by_cases hp : s = 4 / 3
  · rw [hp]
    exact kernelEisensteinL2Correction_meromorphicAt 2 3 (by norm_num) (by norm_num)
  · obtain ⟨C, hC, hEq⟩ := eisensteinCorrection_local_representative s hs hp
    exact hC.meromorphicAt.congr hEq

/-- The correction with removable real values filled in by its meromorphic normal form. -/
def regularizedEisensteinCorrection : ℂ → KernelQuotientL2 :=
  toMeromorphicNFOn eisensteinCorrection {s : ℂ | 1 < s.re}

/-- The filled correction is holomorphic on `Re s>1` except for the cubic pole. -/
theorem regularizedEisensteinCorrection_analyticAt (s : ℂ) (hs : 1 < s.re)
    (hp : s ≠ 4 / 3) : AnalyticAt ℂ regularizedEisensteinCorrection s := by
  obtain ⟨C, hC, hEq⟩ := eisensteinCorrection_local_representative s hs hp
  have hNF := meromorphicNFOn_toMeromorphicNFOn eisensteinCorrection {s : ℂ | 1 < s.re} hs
  apply hNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [meromorphicOrderAt_toMeromorphicNFOn eisensteinCorrection_meromorphicOn_right hs,
    ← meromorphicOrderAt_congr hEq]
  exact hC.meromorphicOrderAt_nonneg

/-- Filling removable real values preserves the actual correction off the real axis. -/
theorem regularizedEisensteinCorrection_eq_nonreal (s : ℂ) (hs : 1 < s.re)
    (hi : s.im ≠ 0) : regularizedEisensteinCorrection s = eisensteinCorrection s := by
  have hA := kernelEisensteinL2Correction_analyticAt_nonreal 2 3 (by norm_num) (by norm_num)
    s (by linarith) hi
  rw [regularizedEisensteinCorrection,
    toMeromorphicNFOn_eq_toMeromorphicNFAt eisensteinCorrection_meromorphicOn_right hs,
    toMeromorphicNFAt_eq_self.mpr hA.meromorphicNFAt]

/-- The filled correction has exactly the original punctured germ at the cubic pole. -/
theorem regularizedEisensteinCorrection_eventually_eq_center :
    regularizedEisensteinCorrection =ᶠ[𝓝[≠] (4 / 3 : ℂ)] eisensteinCorrection :=
  eisensteinCorrection_meromorphicOn_right.toMeromorphicNFOn_eq_self_on_nhdsNE (by norm_num)

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
