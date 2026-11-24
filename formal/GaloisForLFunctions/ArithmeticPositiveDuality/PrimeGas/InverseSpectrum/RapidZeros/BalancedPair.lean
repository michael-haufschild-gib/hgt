import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RapidZeros.ClockReadout
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RapidZeros.Transport

/-! # Destructive interference of a law and its inserted copy -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

/-- Mixing an exterior probability equally with any probability retains infinite mean label. -/
def midpointExterior (ρ : ExteriorLaw) (μ : ℕ+ → ℝ) (hμ : ∀ n, 0 ≤ μ n) (hsμ : HasSum μ 1) : ExteriorLaw := by
  let ν := fun n => (ρ.val n+μ n)/2
  have hp (n : ℕ+) : 0 ≤ ν n :=
    div_nonneg (add_nonneg (ρ.property.1 n) (hμ n)) (by norm_num)
  have hs : HasSum ρ.val 1 := Equiv.pnatEquivNat.symm.hasSum_iff.mp ρ.property.2.1
  have hν : HasSum ν 1 := by
    have h := (hs.add hsμ).div_const 2
    norm_num at h
    exact h
  have hd (n : ℕ+) : (1/2:ℝ)*ρ.val n ≤ ν n := by
    dsimp only [ν]
    linarith only [hμ n]
  exact ⟨ν,hp,Equiv.pnatEquivNat.symm.hasSum_iff.mpr hν,
    fun h => exterior_mean_of_dominates ρ (by norm_num : (0:ℝ) < 1/2) hd ((labelMean_summable_iff ν).mpr h)⟩

/-- Equal mixture of an exterior law and its translate by one inserted block. -/
def pairedExterior (a : ℕ+) (ρ : ExteriorLaw) := midpointExterior ρ (insertedMass a ρ.val)
  (insertedMass_nonneg a ρ.property.1) (insertedMass_hasSum a (Equiv.pnatEquivNat.symm.hasSum_iff.mp ρ.property.2.1))

def pairedWave (a : ℕ+) (v : MissingWave) := lawOmission (pairedExterior a (exteriorLaw v))

theorem paired_probability (a : ℕ+) (v : MissingWave) (n : ℕ+) :
    occupationProbability (pairedWave a v) n = (occupationProbability v n+insertedMass a (occupationProbability v) n)/2 :=
  congrFun (lawOmission_probability _) n

/-- At critical time, block insertion multiplies the two preparations by relative phase uₐ(t). -/
theorem paired_response (a : ℕ+) (v : MissingWave) (t : ℝ) :
    compositionResponse (pairedWave a v) (criticalTime t) =
      (1+splitPhase t a)*compositionResponse v (criticalTime t)/2 := by
  have h := ((criticalTerms_hasSum v t).add (criticalTerms_hasSum (insertedWave a v) t)).div_const 2
  have hs : HasSum (fun n => (occupationProbability (pairedWave a v) n:ℂ)*splitPhase t n)
      ((compositionResponse v (criticalTime t)+compositionResponse (insertedWave a v) (criticalTime t))/2) := by
    apply h.congr_fun
    intro n
    rw [paired_probability,insertedWave_probability,Complex.ofReal_div,Complex.ofReal_add]
    push_cast
    ring
  have he := (criticalTerms_hasSum (pairedWave a v) t).unique hs
  rw [he,inserted_response]
  change (_+splitPhase t a*_)/2 = _
  ring

#print axioms paired_probability
#print axioms paired_response

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
