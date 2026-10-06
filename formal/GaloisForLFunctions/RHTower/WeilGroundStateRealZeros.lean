import GaloisForLFunctions.RHTower.WeilPositivityPrimeBlindDuality
import GaloisForLFunctions.HTGeometry.FourierZeroDivisionGroundStates

/-!
# Simple ground states of the restricted Weil form have real Fourier zeros

For weights `lam`, atoms `2 ≤ n ≤ N` and a pole-constrained `C²` test `f` supported in `[-a, a]`
(`IsPolarTest a f`), the restricted Weil energy is the Fourier multiplier
`∫ |f̂(τ)|² weilAtomSymbol lam N (τ/2π) dτ`; it depends only on `|f̂|` on the real line.

**Theorem** (`im_eq_zero_of_simple_weil_groundState`).  If `f₀ ≠ 0` spans the only eigenline of
its Rayleigh value among such tests (every polar test with the same ratio
`∫ |f̂|² S / ∫ |f̂|²` is a multiple of `f₀`), then every zero of `f̂₀` other than the forced zeros
`±i/2` is real.

**Proof.**  The polar constraint is `f̂(±i/2) = 0`.  A zero flip at any other zero `z₀` stays a
polar `C²` test supported in `[-a, a]` and has the same Fourier modulus on `ℝ`
(`FourierZeroFlip.im_eq_zero_of_simple_rayleigh_contDiff`), so rigidity forces `z₀` real.  Taking
`lam = Λ` gives the Connes–van Suijlekom statement for the Weil quadratic form: a simple polar
ground state has a Fourier transform whose zeros, apart from `±i/2`, all lie on the real line.

**Without simplicity** (`card_lt_of_weil_groundState`, `exists_real_rooted_weil_groundState`).  If
no `d + 1` polar ground states at level `μ` are linearly independent, every ground state has fewer
than `d` distinct non-real Fourier zeros other than `±i/2`, and some nonzero ground state has only
real zeros apart from `±i/2`.  These hold in the comparison class of `Cⁿ` functions supported in
`[-a, a]` with `f̂(±i/2) = 0` for every `n`, including the continuous class `n = 0`; for `n = 2`
it is the polar test class (`inClass_iff_isPolarTest`).  The restricted Weil symbol is continuous
(`continuous_weilAtomSymbol`).
-/

noncomputable section
open Complex MeasureTheory Set Filter Zeta23

namespace RHTower.WeilGroundStateRealZeros

open GaloisForLFunctions.HTGeometry.FourierZeroFlip

theorem supportedIn_of_tsupport {a : ℝ} {f : ℝ → ℂ} (h : tsupport f ⊆ Icc (-a) a) :
    SupportedIn a f :=
  fun _ hx => image_eq_zero_of_notMem_tsupport fun hm => hx (h hm)

theorem tsupport_subset_of_supportedIn {a : ℝ} {f : ℝ → ℂ} (h : SupportedIn a f) :
    tsupport f ⊆ Icc (-a) a :=
  closure_minimal (fun x hx => by
    by_contra hc
    exact hx (h x hc)) isClosed_Icc

/-- **Simple polar ground states are real-rooted.** -/
theorem im_eq_zero_of_simple_weil_groundState {a : ℝ} (lam : ℕ → ℝ) (N : ℕ) {f₀ : ℝ → ℂ}
    (hf₀ : IsPolarTest a f₀) (hne : f₀ ≠ 0)
    (hsimple : ∀ f : ℝ → ℂ, IsPolarTest a f →
      (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam N (τ / (2 * Real.pi))) *
          (∫ τ : ℝ, ‖paperFT f₀ τ‖ ^ 2) =
        (∫ τ : ℝ, ‖paperFT f₀ τ‖ ^ 2 * weilAtomSymbol lam N (τ / (2 * Real.pi))) *
          (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2) →
      ∃ c : ℂ, f = c • f₀)
    {z₀ : ℂ} (hz : paperFT f₀ z₀ = 0) (hp : z₀ ≠ I / 2) (hm : z₀ ≠ -(I / 2)) : z₀.im = 0 := by
  obtain ⟨ha, hc2, hts, hpp, hpm⟩ := hf₀
  have e : ∀ g : ℝ → ℂ, (∫ τ : ℝ, ‖paperFT g τ‖ ^ 2 * weilAtomSymbol lam N (τ / (2 * Real.pi))) =
      ∫ t : ℝ, weilAtomSymbol lam N (t / (2 * Real.pi)) * ‖paperFT g t‖ ^ 2 :=
    fun g => integral_congr_ae (Eventually.of_forall fun t => mul_comm _ _)
  refine im_eq_zero_of_simple_rayleigh_contDiff ha
    (fun t => weilAtomSymbol lam N (t / (2 * Real.pi))) (n := 2) hc2
    (supportedIn_of_tsupport hts) hne (E := {I / 2, -(I / 2)}) ?_ ?_ hz ?_
  · rintro w (rfl | rfl)
    · exact hpp
    · exact hpm
  · intro f hf hfs hfE hq
    refine hsimple f ⟨ha, hf, tsupport_subset_of_supportedIn hfs, hfE _ (by simp),
      hfE _ (by simp)⟩ ?_
    rw [e, e]
    exact hq
  · rintro (h | h)
    · exact hp h
    · exact hm h

theorem continuous_weilAtomSymbol (lam : ℕ → ℝ) (N : ℕ) : Continuous (weilAtomSymbol lam N) := by
  unfold weilAtomSymbol archimedeanWeilSymbol
  refine (continuous_const.mul
    (continuous_gammaHardyPhaseRate.comp (continuous_const.mul continuous_id))).sub ?_
  exact continuous_finsetSum _ fun n _ => continuous_const.mul (by fun_prop)

/-- The restricted Weil symbol in the frequency variable of `paperFT`. -/
def weilRaySymbol (lam : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ := weilAtomSymbol lam N (t / (2 * Real.pi))

theorem measurable_weilRaySymbol (lam : ℕ → ℝ) (N : ℕ) : Measurable (weilRaySymbol lam N) :=
  ((continuous_weilAtomSymbol lam N).comp (continuous_id.div_const _)).measurable

/-- The polar test class is the comparison class with `n = 2` and `E = {±i/2}`. -/
theorem inClass_iff_isPolarTest {a : ℝ} (ha : 0 ≤ a) (f : ℝ → ℂ) :
    InClass a 2 {I / 2, -(I / 2)} f ↔ IsPolarTest a f := by
  constructor
  · rintro ⟨hc, hs, hE⟩
    exact ⟨ha, hc, tsupport_subset_of_supportedIn hs, hE _ (by simp), hE _ (by simp)⟩
  · rintro ⟨_, hc, hts, hp, hm⟩
    refine ⟨hc, supportedIn_of_tsupport hts, ?_⟩
    rintro w (rfl | rfl)
    · exact hp
    · exact hm

/-- **Multiplicity bound for polar Weil ground states**, in the comparison class of `Cⁿ` functions
supported in `[-a, a]` with `f̂(±i/2) = 0`; `n = 0` is the class of continuous functions. -/
theorem card_lt_of_weil_groundState {a : ℝ} (ha : 0 ≤ a) (lam : ℕ → ℝ) (N : ℕ) {n : ℕ} {μ : ℝ}
    (hlev : IsGroundLevel a n {I / 2, -(I / 2)} (weilRaySymbol lam N) μ) {d : ℕ}
    (hdim : ∀ g : Fin (d + 1) → ℝ → ℂ,
      (∀ i, IsGround a n {I / 2, -(I / 2)} (weilRaySymbol lam N) μ (g i)) →
        ¬ LinearIndependent ℂ g)
    {f₀ : ℝ → ℂ} (hf₀ : IsGround a n {I / 2, -(I / 2)} (weilRaySymbol lam N) μ f₀)
    (hne : f₀ ≠ 0) (Z : Finset ℂ)
    (hZ : ∀ z ∈ Z, paperFT f₀ z = 0 ∧ z.im ≠ 0 ∧ z ≠ I / 2 ∧ z ≠ -(I / 2)) : Z.card < d :=
  card_lt_of_isGround ha (measurable_weilRaySymbol lam N) hlev hdim hf₀ hne Z fun z hz => by
    obtain ⟨h1, h2, h3, h4⟩ := hZ z hz
    refine ⟨h1, h2, ?_⟩
    rintro (h | h)
    · exact h3 h
    · exact h4 h

/-- **Real-rooted polar Weil ground states exist without simplicity**, in the `Cⁿ` comparison class
(`n = 0`: continuous functions). -/
theorem exists_real_rooted_weil_groundState {a : ℝ} (ha : 0 ≤ a) (lam : ℕ → ℝ) (N : ℕ) {n : ℕ}
    {μ : ℝ} (hlev : IsGroundLevel a n {I / 2, -(I / 2)} (weilRaySymbol lam N) μ) {d : ℕ}
    (hdim : ∀ g : Fin (d + 1) → ℝ → ℂ,
      (∀ i, IsGround a n {I / 2, -(I / 2)} (weilRaySymbol lam N) μ (g i)) →
        ¬ LinearIndependent ℂ g)
    {f₀ : ℝ → ℂ} (hf₀ : IsGround a n {I / 2, -(I / 2)} (weilRaySymbol lam N) μ f₀)
    (hne : f₀ ≠ 0) :
    ∃ g : ℝ → ℂ, IsGround a n {I / 2, -(I / 2)} (weilRaySymbol lam N) μ g ∧ g ≠ 0 ∧
      ∀ z : ℂ, paperFT g z = 0 → z ≠ I / 2 → z ≠ -(I / 2) → z.im = 0 := by
  obtain ⟨g, hg, hgne, hreal⟩ :=
    exists_isGround_real_zeros ha (measurable_weilRaySymbol lam N) hlev hdim hf₀ hne
  refine ⟨g, hg, hgne, fun z hz hp hm => hreal z hz ?_⟩
  rintro (h | h)
  · exact hp h
  · exact hm h

end RHTower.WeilGroundStateRealZeros
