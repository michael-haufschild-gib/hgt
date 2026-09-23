import GaloisForLFunctions.RHTower.HarmonicQuotientToeplitz
import GaloisForLFunctions.RHTower.Sieve.CoprimeLogMoebiusOneLimit
import GaloisForLFunctions.RHTower.Sieve.CoprimeLogMoebiusUniformBound

open Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

/-- Principal harmonic model of the Barban--Vehov two-variable Euler kernel. -/
def selbergPrincipalHarmonicModel (N : ℕ) : ℝ :=
  harmonicQuotientMean
    (fun m : ℕ => (coprimeLogMoebius 1 (m : ℝ)) ^ (2 : ℕ)) N

/-- The principal Barban--Vehov Euler factor has logarithmic residue one. -/
theorem tendsto_selbergPrincipalHarmonicModel_div_log_one :
    Tendsto (fun N : ℕ => selbergPrincipalHarmonicModel N / Real.log N)
      atTop (𝓝 1) := by
  have hone : Tendsto (fun m : ℕ => coprimeLogMoebius 1 (m : ℝ)) atTop (𝓝 1) :=
    tendsto_coprimeLogMoebius_one.comp tendsto_natCast_atTop_atTop
  have hsq : Tendsto (fun m : ℕ => (coprimeLogMoebius 1 (m : ℝ)) ^ (2 : ℕ))
      atTop (𝓝 1) := by simpa using hone.pow 2
  have hbound : ∀ m : ℕ, |(coprimeLogMoebius 1 (m : ℝ)) ^ (2 : ℕ)| ≤
      coprimeLogMoebiusConst ^ (2 : ℕ) := by
    intro m
    have h := abs_coprimeLogMoebius_le 1 (by simp) (m : ℝ)
    norm_num at h
    rw [abs_pow]
    nlinarith [abs_nonneg (coprimeLogMoebius 1 (m : ℝ)),
      coprimeLogMoebiusConst_nonneg]
  simpa only [selbergPrincipalHarmonicModel] using
    tendsto_harmonicQuotientMean_div_log
      (fun m : ℕ => (coprimeLogMoebius 1 (m : ℝ)) ^ (2 : ℕ))
      1 (coprimeLogMoebiusConst ^ (2 : ℕ)) hsq hbound

end

end RHTower.Sieve

