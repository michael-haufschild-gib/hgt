import GaloisForLFunctions.RHTower.Sieve.GuthMaynardSTwoReductionAssembly
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardCubicTermCGL
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma45FrequencySplit

/-!
# Guth–Maynard (6.1) for the Chen–Gupta–Li cubic trace at `q = 1`

The Chen–Gupta–Li tower expands the weighted cubic Gram trace of a character packet into the
frequency coefficients `cglLemma45TraceFrequencyTerm` (`cglLemma45_cubicTrace_eq_tsum_frequencyTerm`).
For the modulus `q = 1` (the Riemann zeta function) every residue class, character value and
additive character is trivial (corpus `cglLemma45CharacterPairFourierTerm_modulusOne`), and the
coefficient is exactly Guth–Maynard's

`I_m = N³ Σ_{t₁,t₂,t₃∈W} ĥ_{t₁−t₂}(m₁N) ĥ_{t₂−t₃}(m₂N) ĥ_{t₃−t₁}(m₃N)`

on the set `W` of row times (`cglLemma45TraceFrequencyTerm_modulusOne`).  Hence the `S₂` component
of the actual Chen–Gupta–Li cubic trace (exactly two nonzero frequencies) is `gmS2`, and (6.1)
holds for it (`cglTraceS2_modulusOne_le_sixOne`).
-/

set_option autoImplicit false

open Complex Finset
open scoped FourierTransform

noncomputable section

namespace RHTower.GuthMaynard

/-- **The Chen–Gupta–Li trace coefficient at `q = 1` is Guth–Maynard's `I_m`** on the set of row
times (rows with distinct times). -/
theorem cglLemma45TraceFrequencyTerm_modulusOne (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (R : ℕ) (rows : Fin R → CGLCharacterDyadicRowData modulusOne.value)
    (hinj : Function.Injective fun r => (rows r).time) (m : (ℤ × ℤ) × ℤ) :
    cglLemma45TraceFrequencyTerm w N modulusOne R rows m =
      gmIm w N.value (Finset.univ.image fun r => (rows r).time) m := by
  classical
  haveI : Unique (ZMod modulusOne.value) := (inferInstance : Unique (ZMod 1))
  have hinj' : Set.InjOn (fun r => (rows r).time) ↑(Finset.univ : Finset (Fin R)) :=
    hinj.injOn
  unfold cglLemma45TraceFrequencyTerm cglLemma45FrequencyIndex cglCharacterDyadicGramCubicIndexSet
  simp only [gmIm, cubicTerm, Finset.sum_product, Finset.univ_unique, Finset.sum_singleton,
    cglLemma45TripleFrequencyTerm, cglLemma45CharacterPairFourierTerm_modulusOne,
    Finset.sum_image hinj', Finset.mul_sum, Complex.ofReal_natCast]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ =>
    Finset.sum_congr rfl fun u _ => ?_
  ring

/-- The `S₂` component of the Chen–Gupta–Li cubic trace at `q = 1` is `gmS2`. -/
theorem cglTraceS2_modulusOne_eq_gmS2 (w : CGLRealSmoothBump) (N : CGLPositiveLength) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData modulusOne.value)
    (hinj : Function.Injective fun r => (rows r).time) :
    ∑' m : {m : (ℤ × ℤ) × ℤ // gmS2Frequency m},
        cglLemma45TraceFrequencyTerm w N modulusOne R rows m =
      gmS2 w N.value (Finset.univ.image fun r => (rows r).time) :=
  tsum_congr fun m => cglLemma45TraceFrequencyTerm_modulusOne w N R rows hinj m

/-- **Guth–Maynard (6.1) for the Chen–Gupta–Li cubic trace at `q = 1`.**  For every `ε ∈ (0,1]`
there is `C ≥ 0` such that for every packet of `R` rows with `T^ε`-separated times in `[0,T]`
(`T ≥ 1`) and every length `N`, the `S₂` component of the cubic trace satisfies
`‖S₂‖ ≤ C (T^ε)^4 R₆.₁ + C N² R²` with `R₆.₁ = gmSixOneSum ε N T W` the right side of (6.1). -/
theorem cglTraceS2_modulusOne_le_sixOne (w : CGLRealSmoothBump) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ) (N : CGLPositiveLength) (R : ℕ)
      (rows : Fin R → CGLCharacterDyadicRowData modulusOne.value), 1 ≤ T →
      (∀ r s, r ≠ s → T ^ ε ≤ |(rows r).time - (rows s).time|) →
      (∀ r, 0 ≤ (rows r).time ∧ (rows r).time ≤ T) →
      ‖∑' m : {m : (ℤ × ℤ) × ℤ // gmS2Frequency m},
          cglLemma45TraceFrequencyTerm w N modulusOne R rows m‖ ≤
        C * ((T ^ ε) ^ 4 * gmSixOneSum ε N.value T (Finset.univ.image fun r => (rows r).time)) +
          C * ((N.value : ℝ) ^ 2 * (R : ℝ) ^ 2) := by
  classical
  obtain ⟨C, hC0, hC⟩ := gmS2_le_sixOne w hε hε1
  refine ⟨C, hC0, fun T N R rows hT hsep hrange => ?_⟩
  have hTe : 0 < T ^ ε := Real.rpow_pos_of_pos (by linarith) ε
  have hinj : Function.Injective fun r => (rows r).time := by
    intro r s hrs
    by_contra hne
    have := hsep r s hne
    simp only at hrs
    rw [hrs, sub_self, abs_zero] at this
    linarith
  have hN : (1 : ℝ) ≤ N.value := by exact_mod_cast N.positive
  set W := Finset.univ.image fun r => (rows r).time with hW
  have hWsep : IsSeparated (T ^ ε) W := by
    intro t ht t' ht' hne
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp ht'
    exact hsep r s (fun h => hne (by rw [h]))
  have hWrange : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T := by
    intro t ht
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp ht
    exact hrange r
  have hcard : (W.card : ℝ) = R := by
    rw [hW, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  rw [cglTraceS2_modulusOne_eq_gmS2 w N R rows hinj, ← hcard]
  exact hC T N.value W hT hN hWsep hWrange

end RHTower.GuthMaynard
