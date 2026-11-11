import GaloisForLFunctions.SelectiveArithmetic.CancellationInTheContactsBuysTheLadder
import GaloisForLFunctions.RHTower.PsiRemainderSignChange
import GaloisForLFunctions.RHTower.QuasiRHQuotientHeadAndFiniteContactAbscissaLaw
import GaloisForLFunctions.RHTower.JointAncestryLargePrimeAbscissa
import GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit.AZeroFreeRegionBoundsTheHeavyReturns

/-!
# The half-plane map for three scales

A zero half-plane `Θ≤b` gives bounded-shape positivity for centred prime contacts
at every rung `(2b−1)κ<1`, dressed positivity on large primes above level `b+1/2`,
and absence of heavy prime-orbit returns with `log t<c y^(1−b)`.
The centred contacts are `Λ(n)−1`; the main term of the raw prime sum is retained
in the other two statements.
-/

open Complex Filter Topology Set MeasureTheory
open Zeta23
open _root_.RHTower
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.SelectiveArithmetic

open TranscendenceTheoryOfThePrimeOrbit

/-- Centring the prime contacts removes exactly their linear main term. -/
theorem partialSum_centred_vonMangoldt {n : ℕ} (hn : 1 ≤ n) :
    partialSum (fun k => (Λ k : ℝ) - 1) n = psiRemainder n + 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hzero : n = 0
    · subst n
      norm_num [partialSum, psiRemainder, chebyshevPsi, ArithmeticFunction.vonMangoldt]
    · have hn' : 1 ≤ n := by omega
      rw [partialSum_succ _ (by omega), ih hn', ← psiRemainder_succ_sub n]
      ring

/-- The zero abscissa supplies cancellation for the centred prime contacts. -/
theorem exists_centred_prime_cancellation {γ : ℝ} (hγ : zetaZeroAbscissa - 1 / 2 < γ) :
    ∃ C : ℝ, 0 ≤ C ∧ HasCancellation (fun n => (Λ n : ℝ) - 1) C γ := by
  let ε := 1 / 2 + γ - zetaZeroAbscissa
  have hε : 0 < ε := by dsimp [ε]; linarith only [hγ]
  obtain ⟨C, hC, hb⟩ := exists_psiRemainder_le_rpow_zetaZeroAbscissa ε hε
  have hg0 : 0 < γ := by linarith only [hγ, half_le_zetaZeroAbscissa]
  refine ⟨C + 1, by linarith only [hC], fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hpow : 1 ≤ (n : ℝ) ^ (1 / 2 + γ) := Real.one_le_rpow hn1 (by linarith only [hg0])
  have hR := hb n hn
  rw [show zetaZeroAbscissa + ε = 1 / 2 + γ by dsimp [ε]; ring] at hR
  have htri := abs_add_le (psiRemainder n) 1
  rw [abs_one] at htri
  rw [partialSum_centred_vonMangoldt hn, Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add hn0]
  nlinarith only [htri, hR, hpow]

/-- A strict rung below `1/(2b−1)` is positive on bounded shapes for centred contacts. -/
theorem centred_prime_rung_of_halfPlane {b κ : ℝ} (hb : zetaZeroAbscissa ≤ b)
    (hκ : 0 < κ) (hrung : (2 * b - 1) * κ < 1) :
    ∃ M : ℝ, ∀ q : ℝ, M ≤ Real.log q → ∀ a : ℝ,
      0 ≤ a → a ≤ κ * Real.log (Real.log q) → ∀ f : ℝ → ℝ,
      ContDiff ℝ 3 f → (∀ u, a ≤ |u| → f u = 0) →
      (∫ u, deriv f u ^ 2) ≤ (∫ u, f u ^ 2) →
      0 ≤ systemForm (fun n => (Λ n : ℝ) - 1) q a (fun u => (f u : ℂ)) := by
  have hb0 : 1 / 2 ≤ b := half_le_zetaZeroAbscissa.trans hb
  have hgap : b - 1 / 2 < 1 / (2 * κ) := by
    apply (lt_div_iff₀ (by positivity : 0 < 2 * κ)).mpr
    nlinarith only [hrung]
  obtain ⟨γ, hγlo, hγhi⟩ := exists_between hgap
  have hγ : 0 ≤ γ := by linarith only [hb0, hγlo]
  have hγκ : 2 * γ * κ < 1 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 2 * κ)).mp hγhi
    nlinarith only [hh]
  obtain ⟨C, hC, hcancel⟩ := exists_centred_prime_cancellation (γ := γ)
    (by linarith only [hb, hγlo])
  obtain ⟨M, hM⟩ := exists_cancellation_margin hC hγ hκ.le hγκ
  refine ⟨max M 0, fun q hq a ha har f hf hs hshape => ?_⟩
  have hq0 : 0 ≤ Real.log q := (le_max_right _ _).trans hq
  exact (mul_nonneg (div_nonneg hq0 zero_le_two) (sub_nonneg.mpr hshape)).trans
    (hM q ((le_max_left _ _).trans hq) a ha har hcancel hf hs)

/-- Every level strictly above `b+1/2` is positive on sufficiently large primes. -/
theorem large_prime_level_of_halfPlane {b ε : ℝ} (hb : zetaZeroAbscissa ≤ b)
    (hε : 0 < ε) : ∃ X : ℕ, JasDressedPSDAbove X (b + 1 / 2 + ε) := by
  let e := min ε 1
  let α := b - 1 / 2 + (ε - e)
  have he0 : 0 < e := lt_min hε zero_lt_one
  have he1 : e ≤ 1 := min_le_right _ _
  have heε : e ≤ ε := min_le_left _ _
  have hb0 : 1 / 2 ≤ b := half_le_zetaZeroAbscissa.trans hb
  have hα : 0 ≤ α := by dsimp [α]; linarith only [hb0, heε]
  have hXi : XiZeroHalfPlaneBound α := by
    intro ρ hρ
    have hh := (xi_zero_re_le_zetaZeroAbscissa hρ).trans hb
    dsimp [α]
    linarith only [hh, heε]
  let X := ⌈Real.exp (1 / e + 1)⌉₊ + 2
  have hX : 2 ≤ X := by dsimp [X]; omega
  have hlog : 1 / e + 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (by exact_mod_cast (by omega : 0 < X))]
    dsimp [X]
    push_cast
    linarith only [Nat.le_ceil (Real.exp (1 / e + 1))]
  refine ⟨X, ?_⟩
  have h := jasDressedPSDAbove_of_xiZeroHalfPlaneBound hα hXi he0 he1 hX hlog
  rwa [show 1 + α + e = b + 1 / 2 + ε by dsimp [α]; ring] at h

/-- Under `Θ≤b`, a heavy return requires `log t≥c y^(1−b)`. -/
theorem heavy_return_bound_of_halfPlane {b : ℝ} (hb : zetaZeroAbscissa ≤ b) :
    ∃ c : ℝ, 0 < c ∧ ∃ T₁ : ℝ, ∀ᶠ y : ℕ in atTop,
      ∀ H : Finset ℕ, IsHeavy y (1 / 1000) H → ∀ δ t : ℝ,
        0 ≤ δ → δ ≤ 1 / 20 → T₁ ≤ t →
        IsDeltaReturn H (fun p : ℕ => Real.log p) δ t →
          c * (y : ℝ) ^ (1 - b) ≤ Real.log t := by
  have hh : 0 ≤ b - 1 / 2 := by linarith only [half_le_zetaZeroAbscissa.trans hb]
  have hstrip : ∀ ρ ∈ zetaZeroConfig.carrier, (0 : ℝ) ≤ |ρ.im| →
      |ρ.re - 1 / 2| ≤ b - 1 / 2 := by
    intro ρ hρ _
    have hxi := (_root_.RHTower.CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp hρ).1
    obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
    have hq := xiZeroCopy_abs_re_sub_half_le_zetaZeroAbscissa q
    linarith only [hq, hb]
  simpa only [show 1 / 2 - (b - 1 / 2) = 1 - b by ring] using
    log_ge_of_heavy_return_of_strip hh hstrip

end GaloisForLFunctions.SelectiveArithmetic
