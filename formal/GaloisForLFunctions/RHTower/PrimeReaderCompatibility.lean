import GaloisForLFunctions.RHTower.MertensPrimeMeanReader
import GaloisForLFunctions.RHTower.HarmonicResidueAbscissaReader

/-!
# The Mertens mean and the prime-harmonic residue agree

Two readers have been built on prime coefficient fields: the Mertens mean, weighted by `log p / p`
and normalised by `log X`, and the prime-harmonic residue, weighted by `1 / p` and read either by
cofinal averaging or at the Dirichlet abscissa.  They act on different objects — the first on `b_p`,
the second on a field asymptotic to `c / p` — and they annihilate different ideals.

They are nevertheless compatible.  Since `log p ≥ log 2` on the primes, critical summability is
stronger than plain harmonic summability, so a field `b` lying critically summably near a constant
`c` produces a rescaled field `p ↦ b_p / p` whose prime-harmonic residue is that same `c`.  Both
devices then report the same number.
-/

open Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## Transport from the natural-number index to the primes -/

theorem primeCoe_injective : Function.Injective (fun p : Nat.Primes => (p : ℕ)) :=
  fun _ _ h => Subtype.ext h

theorem notMem_range_primeCoe {n : ℕ}
    (hn : n ∉ Set.range fun p : Nat.Primes => (p : ℕ)) : ¬ n.Prime :=
  fun hp => hn ⟨⟨n, hp⟩, rfl⟩

/-- Critical summability, transported to an index over the primes themselves. -/
theorem summable_primes_of_memCriticalSummableLayer {b : ℕ → ℝ}
    (hb : MemCriticalSummableLayer b) :
    Summable fun p : Nat.Primes =>
      Real.log (p : ℕ) / (p : ℕ) * |b (p : ℕ)| := by
  have hvanish : ∀ n ∉ Set.range fun p : Nat.Primes => (p : ℕ),
      ({q : ℕ | q.Prime}.indicator fun m => Real.log m / m * |b m|) n = 0 := by
    intro n hn
    exact Set.indicator_of_notMem (notMem_range_primeCoe hn) _
  refine ((primeCoe_injective.summable_iff hvanish).mpr hb).congr fun p => ?_
  exact Set.indicator_of_mem (show (p : ℕ) ∈ {q : ℕ | q.Prime} from p.2) _

/-- **Critical summability is stronger than harmonic summability.**  On the
primes `log p ≥ log 2`, so the extra logarithmic weight can be divided out. -/
theorem summable_primeHarmonic_of_memCriticalSummableLayer {b : ℕ → ℝ}
    (hb : MemCriticalSummableLayer b) :
    Summable fun p : Nat.Primes => |b (p : ℕ)| * primeHarmonicWeight p := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
    ((summable_primes_of_memCriticalSummableLayer hb).mul_left (Real.log 2)⁻¹)
  · exact mul_nonneg (abs_nonneg _) (primeHarmonicWeight_nonneg p)
  · have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
    have hlogp : Real.log 2 ≤ Real.log (p : ℕ) := Real.log_le_log (by norm_num) hp2
    rw [primeHarmonicWeight]
    rw [show (Real.log 2)⁻¹ *
          (Real.log (p : ℕ) / ((p : ℕ) : ℝ) * |b (p : ℕ)|) =
        (Real.log (p : ℕ) / Real.log 2) * (|b (p : ℕ)| * ((p : ℕ) : ℝ)⁻¹) by
      field_simp]
    have hone : (1 : ℝ) ≤ Real.log (p : ℕ) / Real.log 2 := by
      rw [le_div_iff₀ hlog2]
      linarith
    have hnn : (0 : ℝ) ≤ |b (p : ℕ)| * ((p : ℕ) : ℝ)⁻¹ := by positivity
    nlinarith [hone, hnn]

/-! ## The rescaled field has the constant as its harmonic residue -/

/-- The rescaled prime field `p ↦ b_p / p`, as a complex prime field. -/
def rescaledPrimeField (b : ℕ → ℝ) : Nat.Primes → ℂ :=
  fun p => ((b (p : ℕ) / (p : ℕ) : ℝ) : ℂ)

theorem hasReferenceResidue_rescaledPrimeField {b : ℕ → ℝ} {c : ℝ}
    (hb : MemCriticalSummableLayer fun n => b n - c) :
    HasReferenceResidue primeHarmonicWeight (rescaledPrimeField b) (c : ℂ) := by
  have hsum := summable_primeHarmonic_of_memCriticalSummableLayer hb
  refine Summable.of_norm (hsum.congr fun p => ?_)
  have hEq : rescaledPrimeField b p -
      (c : ℂ) * ((((((p : ℕ) : ℝ))⁻¹ : ℝ)) : ℂ) =
      (((b (p : ℕ) - c) * ((p : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [rescaledPrimeField]
    push_cast
    ring
  rw [primeHarmonicWeight, hEq, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (show (0 : ℝ) < ((p : ℕ) : ℝ)⁻¹ by
      have : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
      positivity)]

/-! ## The two readers report the same constant -/

/-- **Compatibility of the two readers.**  A field lying critically summably near
a constant is read as that constant by the Mertens mean, and its rescaled prime
field is read as the same constant by the prime-harmonic abscissa reader. -/
theorem mertensPrimeMean_and_abscissaReader_agree {b : ℕ → ℝ} {c : ℝ}
    (hb : MemCriticalSummableLayer fun n => b n - c) :
    Tendsto (mertensPrimeMean b) atTop (nhds c) ∧
      Tendsto (fun s => primeAbscissaSeries (rescaledPrimeField b) s /
          ((abscissaLog s : ℝ) : ℂ))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (c : ℂ)) :=
  ⟨tendsto_mertensPrimeMean hb,
    tendsto_primeAbscissaSeries_div_abscissaLog
      (hasReferenceResidue_rescaledPrimeField hb)⟩

/-- The same compatibility against the combinatorial reader: every bounded
cofinal unit profile reports the constant too. -/
theorem tendsto_profileAverage_rescaledPrimeField
    {mu : ℕ → Nat.Primes → ℝ}
    (hmu : IsCofinalUnitProfile primeHarmonicWeight mu) {b : ℕ → ℝ} {c : ℝ}
    (hb : MemCriticalSummableLayer fun n => b n - c) :
    Tendsto (fun N => profileAverage mu N (rescaledPrimeField b)) atTop
      (nhds (c : ℂ)) :=
  tendsto_profileAverage hmu (hasReferenceResidue_rescaledPrimeField hb)

end

end RHTower
