import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RapidZeros.Insertion
import GaloisForLFunctions.U0.U0NaturalBoundary

/-! # Effect of occupation insertion on convergence and continuation -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology U0NaturalBoundary

def insertedWave (a : ℕ+) (v : MissingWave) := lawOmission (insertedExterior a (exteriorLaw v))

theorem insertedWave_probability (a : ℕ+) (v : MissingWave) :
    occupationProbability (insertedWave a v) = insertedMass a (occupationProbability v) :=
  lawOmission_probability _

private theorem inserted_terms (a : ℕ+) (v : MissingWave) (s b : ℂ) :
    HasSum (fun n => (occupationProbability (insertedWave a v) n:ℂ)*heat (2*s-1) n) b ↔
      HasSum (fun n => heat (2*s-1) a*((occupationProbability v n:ℂ)*heat (2*s-1) n)) b := by
  rw [insertedWave_probability]
  have h := inserted_hasSum_iff a (occupationProbability v) (fun n x => (x:ℂ)*heat (2*s-1) n)
    (fun n => by simp only [Complex.ofReal_zero,zero_mul]) b
  refine h.trans ?_
  have he (n : ℕ+) : (occupationProbability v n:ℂ)*heat (2*s-1) (a*n) =
      heat (2*s-1) a*((occupationProbability v n:ℂ)*heat (2*s-1) n) := by rw [heat_mul,mul_left_comm]
  exact (congrArg (fun f : ℕ+ → ℂ => HasSum f b) (funext he)).to_iff

theorem inserted_response (a : ℕ+) (v : MissingWave) (s : ℂ) :
    compositionResponse (insertedWave a v) s = heat (2*s-1) a*compositionResponse v s := by
  unfold compositionResponse
  rw [← tsum_mul_left]
  exact tsum_eq_tsum_of_hasSum_iff_hasSum (inserted_terms a v s _)

theorem inserted_finiteSplit_iff (a : ℕ+) (v : MissingWave) (s : ℂ) :
    finiteSplit (insertedWave a v) s ↔ finiteSplit v s := by
  rw [← response_absolute_iff,← response_absolute_iff,summable_norm_iff,summable_norm_iff]
  exact (exists_congr (inserted_terms a v s)).trans (summable_mul_left_iff (Complex.exp_ne_zero _))

/-- Reversible analytic transport by the entire, nowhere-zero heat of the inserted block. -/
theorem inserted_continues_iff (a : ℕ+) (v : MissingWave) (D : Set ℂ) (s : ℂ) :
    ContinuesAcross (compositionResponse (insertedWave a v)) D s ↔ ContinuesAcross (compositionResponse v) D s := by
  have ha : AnalyticAt ℂ (fun z => heat (2*z-1) a) s := by unfold heat; fun_prop
  have hn (z : ℂ) : heat (2*z-1) a ≠ 0 := Complex.exp_ne_zero _
  constructor
  · rintro ⟨g,hg,he⟩
    refine ⟨fun z => g z/heat (2*z-1) a,hg.div ha (hn s),?_⟩
    filter_upwards [he] with z hz
    rw [hz,inserted_response]
    exact mul_div_cancel_left₀ _ (hn z)
  · rintro ⟨g,hg,he⟩
    refine ⟨fun z => heat (2*z-1) a*g z,ha.mul hg,?_⟩
    filter_upwards [he] with z hz
    rw [hz,inserted_response]

#print axioms insertedWave_probability
#print axioms inserted_response
#print axioms inserted_finiteSplit_iff
#print axioms inserted_continues_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
