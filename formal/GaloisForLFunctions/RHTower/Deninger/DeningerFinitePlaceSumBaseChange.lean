import GaloisForLFunctions.RHTower.Deninger.DeningerFinitePlaceBaseChange
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# Fibrewise summation over the primes above a place

Summing a homogeneous function of the adic absolute value over all primes of `L` above a prime `v`
of `K` multiplies it by `[L : K]`: each term contributes the local degree `e·f` by the scaling
law, and the local degrees add up to the global degree by the fundamental identity.

Together with the archimedean base-change law this is the compatibility that lets the place models
of a tower of number fields glue: every place sum built from a homogeneous `F` — the logarithmic
height with `F = log⁺`, the Kummer norm with `F = |log ·|` — scales by exactly `[L : K]`.

* `deningerSpectrumOfMem` : a prime above `v` as a point of the height-one spectrum.
* `deningerFinitePlaceSum_baseChange` : the fibrewise sum law.
* `deningerFinitePlaceSum_posLog`, `deningerFinitePlaceSum_absLog` : the two instances used by the
  height and by the Kummer norm.
-/

namespace RHTower

open NumberField IsDedekindDomain Module

section FibrewiseSum

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- A prime of `𝓞 L` lying over `v`, viewed as a point of the height-one spectrum. -/
noncomputable def deningerSpectrumOfMem {v : HeightOneSpectrum (𝓞 K)} {P : Ideal (𝓞 L)}
    (hP : P ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 L)) : HeightOneSpectrum (𝓞 L) where
  asIdeal := P
  isPrime := by
    haveI : v.asIdeal.IsMaximal := v.isMaximal
    exact ((IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot (𝓞 L)).mp hP).1
  ne_bot := by
    haveI : v.asIdeal.IsMaximal := v.isMaximal
    exact Ideal.ne_bot_of_mem_primesOver v.ne_bot
      ((IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot (𝓞 L)).mp hP)

@[simp] theorem deningerSpectrumOfMem_asIdeal {v : HeightOneSpectrum (𝓞 K)} {P : Ideal (𝓞 L)}
    (hP : P ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 L)) :
    (deningerSpectrumOfMem hP).asIdeal = P := rfl

/-- A prime in the fibre over `v` does lie over `v`. -/
theorem deningerSpectrumOfMem_liesOver {v : HeightOneSpectrum (𝓞 K)} {P : Ideal (𝓞 L)}
    (hP : P ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 L)) :
    (deningerSpectrumOfMem hP).asIdeal.LiesOver v.asIdeal := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  exact ((IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot (𝓞 L)).mp hP).2

/-- **The fibrewise base-change law at a finite place.**  For a function `F` homogeneous under
powers, the sum over all primes of `L` above `v` of `F` applied to the adic absolute value of an
element of `K` is `[L : K]` times its value at `v`.  Each term contributes the local degree by
`deningerAdicAbv_liesOver`, and the local degrees sum to the global degree by
`Ideal.sum_ramification_inertia`. -/
theorem deningerFinitePlaceSum_baseChange (F : ℝ → ℝ)
    (hF : ∀ (n : ℕ) (t : ℝ), F (t ^ n) = n * F t) (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    ∑ P ∈ (IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 L)).attach,
        F (HeightOneSpectrum.adicAbv L (deningerSpectrumOfMem P.2) (algebraMap K L x))
      = (finrank K L : ℝ) * F (HeightOneSpectrum.adicAbv K v x) := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  have hterm : ∀ P ∈ (IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 L)).attach,
      F (HeightOneSpectrum.adicAbv L (deningerSpectrumOfMem P.2) (algebraMap K L x))
        = ((v.asIdeal.ramificationIdx' P.1 * v.asIdeal.inertiaDeg' P.1 : ℕ) : ℝ)
            * F (HeightOneSpectrum.adicAbv K v x) := by
    intro P _
    haveI := deningerSpectrumOfMem_liesOver P.2
    rw [deningerAdicAbv_liesOver v (deningerSpectrumOfMem P.2) x, hF]
    rfl
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  congr 1
  rw [← Nat.cast_sum, Finset.sum_attach _
    (fun P => v.asIdeal.ramificationIdx' P * v.asIdeal.inertiaDeg' P),
    Ideal.sum_ramification_inertia (𝓞 L) K L v.ne_bot]

/-- The instance used by the logarithmic height. -/
theorem deningerFinitePlaceSum_posLog (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    ∑ P ∈ (IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 L)).attach,
        Real.posLog (HeightOneSpectrum.adicAbv L (deningerSpectrumOfMem P.2) (algebraMap K L x))
      = (finrank K L : ℝ) * Real.posLog (HeightOneSpectrum.adicAbv K v x) :=
  deningerFinitePlaceSum_baseChange Real.posLog (fun n t => Real.posLog_pow n t) v x

/-- The instance used by the Kummer norm. -/
theorem deningerFinitePlaceSum_absLog (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    ∑ P ∈ (IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 L)).attach,
        |Real.log (HeightOneSpectrum.adicAbv L (deningerSpectrumOfMem P.2) (algebraMap K L x))|
      = (finrank K L : ℝ) * |Real.log (HeightOneSpectrum.adicAbv K v x)| := by
  refine deningerFinitePlaceSum_baseChange (fun t => |Real.log t|) (fun n t => ?_) v x
  rw [Real.log_pow, abs_mul, Nat.abs_cast]

end FibrewiseSum

end RHTower
