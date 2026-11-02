import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheWindowIndexCountsTheRightZeros
import GaloisForLFunctions.RHTower.WeilNyquistInertia
import GaloisForLFunctions.SquareRootThreshold.ZetaSmallApertureHeightWindowPositivity

/-!
# The window index resolves the zeros of its length
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23 Matrix
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticCastelnuovoSeveri HTGeometry

variable {φ : ℝ → ℝ}

local notation "Λw" => (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ))

/-! ### Real parts of a negative family -/

/-- The coefficients that rewrite `Σ x̄_i f_i` in the real and imaginary parts of the `f_i`. -/
def reImCoeff {n : ℕ} (x : Fin n → ℂ) : Fin n ⊕ Fin n → ℂ
  | Sum.inl i => x i
  | Sum.inr i => -Complex.I * x i

/-- The linear map `x ↦ (x, −ix)`. -/
def reImMap (n : ℕ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n ⊕ Fin n → ℂ) where
  toFun := reImCoeff
  map_add' x y := by funext j; cases j <;> simp [reImCoeff]; ring
  map_smul' c x := by funext j; cases j <;> simp [reImCoeff]; ring

theorem reImMap_injective (n : ℕ) : Function.Injective (reImMap n) := fun x y hxy => by
  funext i
  have := congrFun hxy (Sum.inl i)
  simpa [reImMap, reImCoeff] using this

/-- The real and imaginary parts of complex tests. -/
def reImTests {n : ℕ} (f : Fin n → ℝ → ℂ) : Fin n ⊕ Fin n → ℝ → ℝ
  | Sum.inl i => fun u => (f i u).re
  | Sum.inr i => fun u => (f i u).im

theorem sum_reImTests {n : ℕ} (f : Fin n → ℝ → ℂ) (x : Fin n → ℂ) :
    ∑ j, conj (reImCoeff x j) • cx (reImTests f j) = ∑ i, conj (x i) • f i := by
  rw [Fintype.sum_sum_type]
  rw [← Finset.sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  funext u
  simp only [reImCoeff, reImTests, cx, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_mul,
    map_neg, Complex.conj_I]
  conv_rhs => rw [← Complex.re_add_im (f i u)]
  ring

/-- **A negative family of complex tests gives a negative family of real tests**: if Weil's form is
negative on every nonzero combination `Σ x̄_i f_i` of `n` complex `C²` tests, the `2n` real and
imaginary parts have Weil index at least `n`. -/
theorem le_hermNegIndex_reIm {n : ℕ} (f : Fin n → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i))
    (hneg : ∀ x : Fin n → ℂ, x ≠ 0 →
      (zetaZeroConfig.W (∑ i, conj (x i) • f i) (∑ i, conj (x i) • f i)).re < 0) :
    n ≤ hermNegIndex (weilGram Λw fun j => cx (reImTests f j)) := by
  have hr : ∀ j, ContDiff ℝ 2 (cx (reImTests f j)) := by
    intro j
    rcases j with i | i
    · exact Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp (hf i))
    · exact Complex.ofRealCLM.contDiff.comp (Complex.imCLM.contDiff.comp (hf i))
  have hrc : ∀ j, HasCompactSupport (cx (reImTests f j)) := by
    intro j
    rcases j with i | i
    · have h1 : HasCompactSupport (fun u => (f i u).re) :=
        (hfc i).comp_left (g := Complex.re) Complex.zero_re
      exact h1.comp_left Complex.ofReal_zero
    · have h1 : HasCompactSupport (fun u => (f i u).im) :=
        (hfc i).comp_left (g := Complex.im) Complex.zero_im
      exact h1.comp_left Complex.ofReal_zero
  rw [weilGram_eq_zeroGram _ hr hrc]
  set W : Submodule ℂ (Fin n ⊕ Fin n → ℂ) := LinearMap.range (reImMap n) with hW
  have hWdim : Module.finrank ℂ W = n := by
    rw [hW, LinearMap.finrank_range_of_inj (reImMap_injective n), Module.finrank_fin_fun]
  have hpos : IsPosDefOn (-(zeroGram zetaZeroConfig fun j => cx (reImTests f j))) W := by
    rintro y ⟨x, rfl⟩ hy
    have hx : x ≠ 0 := fun h0 => hy (by rw [h0, map_zero])
    rw [hermQuad_neg, hermQuad_zeroGram_of_tempered _ SquareRootThreshold.temperedConfig_zetaZeroConfig _ hr hrc]
    have e : (reImMap n x) = reImCoeff x := rfl
    rw [e, sum_reImTests]
    linarith [hneg x hx]
  have := finrank_le_posIndex hpos
  rw [hWdim] at this
  exact this

/-! ### Windows from tests -/

/-- A test `r` on `[−a, a]` as a window on `[−2a, 0]`: `h(y) = e^{−y/2} r(y + a)`, so that
`H = e^{y/2} h = r(· + a)`. -/
def windowOfTest (a : ℝ) (r : ℝ → ℝ) (y : ℝ) : ℝ := Real.exp (-(y / 2)) * r (y + a)

theorem halfWeight_windowOfTest (a : ℝ) (r : ℝ → ℝ) :
    halfWeight (windowOfTest a r) = fun u => r (u - -a) := by
  funext u
  simp only [halfWeight, windowOfTest]
  rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul, sub_neg_eq_add]

theorem weilGram_windowOfTest {ι : Type*} [Fintype ι] (a : ℝ) (r : ι → ℝ → ℝ)
    (hr : ∀ i, ContDiff ℝ 2 (r i)) (hrc : ∀ i, HasCompactSupport (r i)) :
    weilGram Λw (fun i => cx (halfWeight (windowOfTest a (r i)))) = weilGram Λw (fun i => cx (r i)) := by
  simp_rw [halfWeight_windowOfTest]
  exact EffectiveArithmeticHodgeTheory.weilGram_cx_common_translate r hr hrc (-a)

/-- **Windows of length `2a` carry the finite-level index of `ζ` at level `a`.** For every `ε ≥ 0`
there is a family of windows on `[−2a, 0]` whose window index is eventually at least the
`ε`-negative index of the level-`a` Weil form of `ζ`. -/
theorem exists_windows_le_weilNegIndex (hφ0 : ∫ u, φ u ≠ 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {β J : ℝ}
    (hβJ : 0 ≤ β * J) {a ε : ℝ} (hε : 0 ≤ ε) :
    ∃ (n : ℕ) (h : Fin n ⊕ Fin n → ℝ → ℝ), (∀ i, ContDiff ℝ 2 (h i)) ∧
      (∀ i y, y ∉ Set.Icc (-(2 * a)) 0 → h i y = 0) ∧
        ∀ᶠ K in atTop, RHTower.weilNegIndex zetaZeroConfig a ε ≤
          hermNegIndex (pencilGram φ β J K h) := by
  by_cases h0 : RHTower.weilNegIndex zetaZeroConfig a ε = 0
  · refine ⟨0, fun _ _ => 0, fun _ => contDiff_const, fun _ _ _ => rfl, ?_⟩
    exact Eventually.of_forall fun K => by rw [h0]; exact Nat.zero_le _
  -- a witnessing subspace of maximal dimension
  set S : Set ℕ := {n : ℕ | ∃ V : Submodule ℂ (ℝ → ℂ), FiniteDimensional ℂ V ∧
    Module.finrank ℂ V = n ∧ (∀ f ∈ V, ContDiff ℝ 2 f ∧ tsupport f ⊆ Set.Icc (-a) a ∧
      paperFT f (Complex.I / 2) = 0 ∧ paperFT f (-(Complex.I / 2)) = 0) ∧
    ∀ f ∈ V, f ≠ 0 → (zetaZeroConfig.W f f).re < -(ε * ∫ u, ‖f u‖ ^ 2)} with hS
  have hdef : RHTower.weilNegIndex zetaZeroConfig a ε = sSup S := rfl
  have hne : S.Nonempty := by
    by_contra hem
    rw [Set.not_nonempty_iff_eq_empty] at hem
    exact h0 (by rw [hdef, hem, Nat.sSup_empty])
  have hbdd : BddAbove S := by
    by_contra hnb
    exact h0 (by rw [hdef, Nat.sSup_of_not_bddAbove hnb])
  obtain ⟨V, hVfin, hVdim, hVprop, hVneg⟩ := Nat.sSup_mem hne hbdd
  rw [← hdef] at hVdim
  set n := RHTower.weilNegIndex zetaZeroConfig a ε with hn
  let b := Module.finBasisOfFinrankEq ℂ V hVdim
  set f : Fin n → ℝ → ℂ := fun i => (b i : ℝ → ℂ) with hf
  have hfV : ∀ i, f i ∈ V := fun i => (b i).2
  have hfC : ∀ i, ContDiff ℝ 2 (f i) := fun i => (hVprop _ (hfV i)).1
  have hfS : ∀ i, tsupport (f i) ⊆ Set.Icc (-a) a := fun i => (hVprop _ (hfV i)).2.1
  have hfc : ∀ i, HasCompactSupport (f i) := fun i =>
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (hfS i)
  have hneg : ∀ x : Fin n → ℂ, x ≠ 0 →
      (zetaZeroConfig.W (∑ i, conj (x i) • f i) (∑ i, conj (x i) • f i)).re < 0 := by
    intro x hx
    set g : V := ∑ i, conj (x i) • b i with hg
    have hgf : (g : ℝ → ℂ) = ∑ i, conj (x i) • f i := by
      rw [hg, Submodule.coe_sum]
      exact sum_congr rfl fun i _ => by rw [Submodule.coe_smul]
    have hg0 : g ≠ 0 := by
      intro hg0
      apply hx
      funext i
      have := Fintype.linearIndependent_iff.mp b.linearIndependent (fun i => conj (x i))
        (by rw [← hg]; exact hg0) i
      simpa using this
    have hgne : (g : ℝ → ℂ) ≠ 0 := fun h' => hg0 (Subtype.ext h')
    have := hVneg _ g.2 hgne
    have hint : 0 ≤ ε * ∫ u, ‖(g : ℝ → ℂ) u‖ ^ 2 :=
      mul_nonneg hε (integral_nonneg fun u => sq_nonneg _)
    rw [← hgf]
    linarith
  have hidx := le_hermNegIndex_reIm f hfC hfc hneg
  -- the real tests and their windows
  have hrC : ∀ j, ContDiff ℝ 2 (reImTests f j) := by
    intro j
    rcases j with i | i
    · exact Complex.reCLM.contDiff.comp (hfC i)
    · exact Complex.imCLM.contDiff.comp (hfC i)
  have hrc : ∀ j, HasCompactSupport (reImTests f j) := by
    intro j
    rcases j with i | i
    · exact (hfc i).comp_left (g := Complex.re) Complex.zero_re
    · exact (hfc i).comp_left (g := Complex.im) Complex.zero_im
  have hr0 : ∀ j t, t ∉ Set.Icc (-a) a → reImTests f j t = 0 := by
    intro j t ht
    have hft : ∀ i, f i t = 0 := fun i => image_eq_zero_of_notMem_tsupport fun hm => ht (hfS i hm)
    rcases j with i | i
    · show (f i t).re = 0; rw [hft i, Complex.zero_re]
    · show (f i t).im = 0; rw [hft i, Complex.zero_im]
  set h : Fin n ⊕ Fin n → ℝ → ℝ := fun j => windowOfTest a (reImTests f j) with hh
  have hhC : ∀ j, ContDiff ℝ 2 (h j) := fun j =>
    (Real.contDiff_exp.comp (contDiff_id.div_const 2).neg).mul
      ((hrC j).comp (contDiff_id.add contDiff_const))
  have hhS : ∀ j y, y ∉ Set.Icc (-(2 * a)) 0 → h j y = 0 := fun j y hy => by
    simp only [hh, windowOfTest]
    rw [hr0 j (y + a) fun hm => hy ⟨by linarith [hm.1], by linarith [hm.2]⟩, mul_zero]
  refine ⟨n, h, hhC, hhS, ?_⟩
  filter_upwards [eventually_hermNegIndex_pencilGram_eq hφ0 hφ2 hhC hhS hβJ] with K hK
  rw [hK, show (fun j => cx (halfWeight (h j))) =
    (fun j => cx (halfWeight (windowOfTest a (reImTests f j)))) from rfl,
    weilGram_windowOfTest a _ hrC hrc]
  exact hidx

/-- **Windows resolve the right zeros of their length.** There are constants `K₀, K₁ > 0` such that
for every level `a ≥ 1` and every set `T` of right zeros of `ζ` resolved at level `a` (height at
least `101`, below the Nyquist height `πe^{2a−3/4}`, pairwise `3/2` apart, with the Nyquist size and
tail conditions of `weilNegIndex_ge_card_offline_zeros`), some family of windows of length `2a`
has window index eventually at least `|T|`. Together with the Shannon bound
(`hermNegIndex_pencilGram_le_shannon`) the window index of windows of length `A` lies between the
number of right zeros they resolve and `1 + 2A T(A/2)/π`. -/
theorem exists_windows_resolving_rightZeros (hφ0 : ∫ u, φ u ≠ 0) (hφ2 : 0 < ∫ u, φ u ^ 2)
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    ∃ K₀ K₁ : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ ∀ {a Λ τ : ℝ} (T : Finset ℂ), 1 ≤ a →
      (∀ ρ ∈ T, ρ ∈ zetaZeroConfig.carrier ∧ 1 / 2 < ρ.re ∧ 101 ≤ ρ.im ∧
        1 / 2 + 3 * (RHTower.windowCount ρ.im : ℝ) + 11 / 2 ≤
          2 * Real.pi * Real.exp (2 * (a - 3 / 8)) ∧
        RHTower.nyquistSize ρ ≤ Λ ∧ RHTower.nyquistTail a ρ ≤ τ) →
      (∀ ρ ∈ T, ∀ σ ∈ T, ρ ≠ σ → 3 / 2 ≤ |ρ.im - σ.im|) →
      K₀ * T.card * Real.exp (a / 2) * Λ ^ 2 * τ ≤ 1 →
      ∃ (n : ℕ) (h : Fin n ⊕ Fin n → ℝ → ℝ), (∀ i, ContDiff ℝ 2 (h i)) ∧
        (∀ i y, y ∉ Set.Icc (-(2 * a)) 0 → h i y = 0) ∧
          ∀ᶠ K in atTop, T.card ≤ hermNegIndex (pencilGram φ β J K h) := by
  obtain ⟨K₀, K₁, hK₀, hK₁, hb⟩ := RHTower.weilNegIndex_ge_card_offline_zeros
  refine ⟨K₀, K₁, hK₀, hK₁, fun {a Λ τ} T ha hT hsep hsize => ?_⟩
  have hcard := hb T ha hT hsep hsize
  have hε : 0 ≤ 1 / (K₁ * a * T.card * Λ ^ 2) := by
    apply one_div_nonneg.mpr
    have : 0 ≤ a := by linarith
    positivity
  obtain ⟨n, h, hhC, hhS, hev⟩ := exists_windows_le_weilNegIndex hφ0 hφ2 hβJ (a := a) hε
  exact ⟨n, h, hhC, hhS, hev.mono fun K hK => hcard.trans hK⟩

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
