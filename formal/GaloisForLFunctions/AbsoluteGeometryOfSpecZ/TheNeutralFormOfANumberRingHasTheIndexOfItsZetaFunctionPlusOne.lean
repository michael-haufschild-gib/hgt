import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheNeutralPartIsWeilsFormOfTheZerosMinusThePoles
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheSquareOfANumberRingThroughItsIdealsHasTheIndexOfItsDedekindZetaFunction

/-!
# The neutral form of a number ring has the index of its zeta function plus one

Let `K` be a number field. Weil's form of its ring of integers is the form of the zeros of the
completed Dedekind zeta function; without the product of the two charges, the form of the two
poles `s = 0, 1`, it is the form of the divisor of the completed zeta function.

* The completed Dedekind zeta function with its poles cleared does not vanish at `s = 1`
  (`heckeXi_trivialModulus_one_ne_zero`): its value there is the discriminant factor, the
  Gamma factor and the residue of the class number formula, none of which vanishes.
* So the neutral form of the ring has `n` negative squares on some family of tests iff `n` is
  at most one plus the number of zeros right of the line
  (`exists_le_negIndex_dedekind_sub_poleConfig_iff`), and it has at most one negative square on
  every family iff all zeros of the Dedekind zeta function are on the critical line
  (`forall_negIndex_dedekind_sub_poleConfig_le_one_iff`).
-/

noncomputable section

open Filter Topology NumberField
open Zeta23
open scoped Classical

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HeckeLFunctions ArtinMertens HTGeometry

variable (K : Type*) [Field K] [NumberField K]

/-- **The completed Dedekind zeta function with its poles cleared does not vanish at
`s = 1`.** -/
theorem heckeXi_trivialModulus_one_ne_zero : heckeXi (trivialModulus K) 1 (1 : ℂ) ≠ 0 := by
  rw [← Complex.ofReal_one]
  have hcoe : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝 ((1 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
  -- the value at `1` is the limit from the right
  have hξ : Tendsto (fun s : ℝ => heckeXi (trivialModulus K) 1 (s : ℂ)) (𝓝[>] 1)
      (𝓝 (heckeXi (trivialModulus K) 1 ((1 : ℝ) : ℂ))) :=
    ((differentiable_heckeXi (trivialModulus K) 1).continuous.tendsto _).comp hcoe
  have hFt : Tendsto (fun s : ℝ => heckeCompletionFactor (trivialModulus K) (s : ℂ)) (𝓝[>] 1)
      (𝓝 (heckeCompletionFactor (trivialModulus K) ((1 : ℝ) : ℂ))) :=
    ((differentiable_heckeCompletionFactor (trivialModulus K)).continuous.tendsto _).comp hcoe
  have hG1 : heckeGammaFactor (trivialModulus K) 1 ((1 : ℝ) : ℂ) ≠ 0 :=
    heckeGammaFactor_ne_zero _ 1 (by simp)
  have hGc : ContinuousAt (fun s : ℂ => ((heckeGammaFactor (trivialModulus K) 1 s)⁻¹)⁻¹)
      ((1 : ℝ) : ℂ) :=
    ((differentiable_heckeGammaFactor_inv (trivialModulus K) 1).continuous.continuousAt).inv₀
      (inv_ne_zero hG1)
  have hGt : Tendsto (fun s : ℝ => heckeGammaFactor (trivialModulus K) 1 (s : ℂ)) (𝓝[>] 1)
      (𝓝 (heckeGammaFactor (trivialModulus K) 1 ((1 : ℝ) : ℂ))) := by
    have h := hGc.tendsto.comp hcoe
    simpa only [Function.comp_def, inv_inv] using h
  have hprod := ((hcoe.mul hFt).mul hGt).mul (tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
  -- right of `1` the function is its Euler product with the pole cleared
  have heq : (fun s : ℝ => heckeXi (trivialModulus K) 1 (s : ℂ)) =ᶠ[𝓝[>] 1] fun s : ℝ =>
      (s : ℂ) * heckeCompletionFactor (trivialModulus K) (s : ℂ) *
        heckeGammaFactor (trivialModulus K) 1 (s : ℂ) * (((s : ℂ) - 1) * dedekindZeta K s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [heckeXi_trivialModulus_one K (by simpa using hs)]
    ring
  rw [tendsto_nhds_unique (hξ.congr' heq) hprod]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (heckeCompletionFactor_ne_zero _ _)) hG1) ?_
  · simp
  · exact_mod_cast dedekindZeta_residue_ne_zero K

/-- The point `1` is not a zero of the completed Dedekind zeta function. -/
theorem one_notMem_dedekindZeros : (1 : ℂ) ∉ (dedekindZeros K).carrier :=
  fun h => heckeXi_trivialModulus_one_ne_zero K h

/-- **The index law of the neutral form of a number ring.** The form of the zeros of the
Dedekind zeta function minus the form of the poles has `n` negative squares on some family of
`n` tests iff `n` is at most one plus the number of zeros right of the line. -/
theorem exists_le_negIndex_dedekind_sub_poleConfig_iff (n : ℕ) :
    (∃ f : Fin n → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
        n ≤ hermNegIndex (ArithmeticCastelnuovoSeveri.zeroGram (dedekindZeros K) f -
          ArithmeticCastelnuovoSeveri.zeroGram poleConfig f)) ↔
      (n : ℕ∞) ≤ (ArithmeticCastelnuovoSeveri.rightZeros (dedekindZeros K)).encard + 1 :=
  exists_le_negIndex_sub_poleConfig_iff (dedekindZeros K) (temperedConfig_classZeros K 1)
    (one_notMem_dedekindZeros K) n

/-- **The Riemann hypothesis of a number ring is the signature of its neutral form**: the zeros
of the Dedekind zeta function are on the critical line iff the form of the zeros minus the
poles has at most one negative square on every family of tests. -/
theorem forall_negIndex_dedekind_sub_poleConfig_le_one_iff :
    (∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) →
        (∀ i, HasCompactSupport (f i)) →
        hermNegIndex (ArithmeticCastelnuovoSeveri.zeroGram (dedekindZeros K) f -
          ArithmeticCastelnuovoSeveri.zeroGram poleConfig f) ≤ 1) ↔
      ∀ ρ : ℂ, heckeXi (trivialModulus K) 1 ρ = 0 → ρ.re = 1 / 2 := by
  rw [← rightZeros_heckeZeros_eq_empty_iff (trivialModulus K) 1
    (heckeFiniteConductor_trivialModulus K 1)]
  exact (rightZeros_eq_empty_iff_forall_negIndex_sub_poleConfig_le_one (dedekindZeros K)
    (temperedConfig_classZeros K 1) (one_notMem_dedekindZeros K)).symm

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
