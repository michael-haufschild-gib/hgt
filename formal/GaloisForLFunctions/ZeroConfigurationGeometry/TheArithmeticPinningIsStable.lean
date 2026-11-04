import GaloisForLFunctions.ZeroConfigurationGeometry.TheInverseWindowsAreStable
import GaloisForLFunctions.RHTower.WeilMarkovOddSectorTrivialZeroSquares

/-!
# The arithmetic pinning is stable

`ThePrimesPinEveryFinitePieceOfZeta` fixes every finite piece of the zeros of `ζ` by exact prime
data below `e^{2r}`. Here the prime data may be wrong, and the precision of the inverse windows of
`TheInverseWindowsAreStable` converts the prime-side error into a statement about positions.

* **Prime discrepancy** (`norm_weilFullFunctional_sub_le`). Two arithmetic data `λ, λ'` give
  arithmetic images of a kernel `k` supported in `[−2r, 2r]` that differ by at most
  `2 D_r(λ, λ') sup|k|`, `D_r = Σ_{n ≤ e^{2r}} |λ(n) − λ'(n)|/√n` (`primeDiscrepancy`); the pole
  and archimedean terms cancel.
* **Stable pinning at height `T`** (`norm_multDiff_mul_gaps_le_of_arithmetic`). Let a tempered
  configuration `Z` differ from the zeros of `ζ` on a finite set `S`, and let its image on the
  windows of aperture `r` be the arithmetic image of data `λ`. Then for every `z₀ ∈ S` and every
  height `T`,
  `|c(z₀)| ∏_{z ≠ z₀} |γ_{z₀} − γ_z| ≤ 2 D_r(λ, Λ) · annihilatorBound(γ − T) · sup|g|`.
* **Approximate primes pin separated points** (`multDiff_eq_zero_of_arithmetic_precision`). If the
  right-hand side is smaller than the gap product, `Z` and `ζ` have the same multiplicity at `z₀`.

So a configuration produced by approximate prime data can differ from the zeros of `ζ` only at
points whose gaps to the rest of the modification are small compared with the prime discrepancy:
near-collisions are the only places where prime-side error can hide a change of configuration.
-/

open MeasureTheory Complex Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 SquareRootThreshold

/-- The prime weight `λ(n)/√n`, `n ≥ 2`, of the explicit formula. -/
def primeWeight (lam : ℕ → ℝ) (n : ℕ) : ℝ := if 2 ≤ n then lam n / Real.sqrt n else 0

/-- The prime range of aperture `r`: the integers `n ≤ e^{2r}`. -/
def primeRange (r : ℝ) : Finset ℕ := Finset.range (⌊Real.exp (2 * r)⌋₊ + 1)

/-- The **prime discrepancy** `Σ_{n ≤ e^{2r}} |λ(n) − λ'(n)|/√n` of two arithmetic data. -/
def primeDiscrepancy (lam lam' : ℕ → ℝ) (r : ℝ) : ℝ :=
  ∑ n ∈ primeRange r, |primeWeight lam n - primeWeight lam' n|

theorem primeDiscrepancy_nonneg (lam lam' : ℕ → ℝ) (r : ℝ) : 0 ≤ primeDiscrepancy lam lam' r :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Outside the prime range the logarithms exceed `2r`. -/
theorem two_mul_lt_log_of_not_mem_primeRange {r : ℝ} {n : ℕ} (hn : n ∉ primeRange r) :
    2 * r < |Real.log n| := by
  rw [primeRange, Finset.mem_range, not_lt] at hn
  have h1 : Real.exp (2 * r) < n := by
    have := Nat.lt_floor_add_one (Real.exp (2 * r))
    have h2 : ((⌊Real.exp (2 * r)⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2; linarith
  have hpos : (0 : ℝ) < n := (Real.exp_pos _).trans h1
  exact (Real.lt_log_iff_exp_lt hpos).mpr h1 |>.trans_le (le_abs_self _)

theorem weilTest_eq_zero_of_lt {f g : ℝ → ℂ} {r : ℝ} (hf : tsupport f ⊆ Icc (-r) r)
    (hg : tsupport g ⊆ Icc (-r) r) {s : ℝ} (hs : 2 * r < |s|) : EF.weilTest f g s = 0 := by
  rw [_root_.RHTower.weilTest_apply]
  have hz : ∀ t, f t * conj (g (t - s)) = 0 := by
    intro t
    by_cases hft : f t = 0
    · simp [hft]
    · have ht := hf (subset_tsupport _ hft)
      have hgt : g (t - s) = 0 := by
        by_contra h
        have hts := hg (subset_tsupport _ h)
        have h1 : |t| ≤ r := abs_le.mpr ⟨ht.1, ht.2⟩
        have h2 : |t - s| ≤ r := abs_le.mpr ⟨hts.1, hts.2⟩
        have : |s| ≤ 2 * r := by
          calc |s| = |t - (t - s)| := by ring_nf
            _ ≤ |t| + |t - s| := abs_sub _ _
            _ ≤ 2 * r := by linarith
        linarith
      simp [hgt]
  simp [hz]

theorem norm_weilTest_le {f g : ℝ → ℂ} (hf : Integrable f) {M : ℝ} (hg : ∀ u, ‖g u‖ ≤ M)
    (s : ℝ) : ‖EF.weilTest f g s‖ ≤ (∫ u, ‖f u‖) * M := by
  rw [_root_.RHTower.weilTest_apply, ← integral_mul_const]
  refine norm_integral_le_of_norm_le (hf.norm.mul_const M) (Filter.Eventually.of_forall fun t => ?_)
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul_of_nonneg_left (hg _) (norm_nonneg _)

/-- Arithmetic images of two data differ only through the primes in range. -/
theorem weilFullFunctional_sub (lam lam' : ℕ → ℝ) {k : ℝ → ℂ} {r : ℝ}
    (hk : ∀ s, 2 * r < |s| → k s = 0) :
    _root_.RHTower.weilFullFunctional lam k - _root_.RHTower.weilFullFunctional lam' k =
      -∑ n ∈ primeRange r, ((primeWeight lam n - primeWeight lam' n : ℝ) : ℂ) *
        (k (Real.log n) + k (-Real.log n)) := by
  have hzero : ∀ n ∉ primeRange r, k (Real.log n) + k (-Real.log n) = 0 := fun n hn => by
    have h := two_mul_lt_log_of_not_mem_primeRange hn
    rw [hk _ h, hk _ (by rwa [abs_neg]), add_zero]
  have hsum : ∀ μ : ℕ → ℝ, (∑' n : ℕ, ((if 2 ≤ n then μ n / Real.sqrt n else 0 : ℝ) : ℂ) *
      (k (Real.log n) + k (-Real.log n))) =
        ∑ n ∈ primeRange r, ((primeWeight μ n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n)) :=
    fun μ => tsum_eq_sum fun n hn => by rw [hzero n hn, mul_zero]
  simp only [_root_.RHTower.weilFullFunctional]
  rw [hsum lam, hsum lam']
  simp only [Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib]
  ring

/-- **The prime discrepancy bounds the difference of arithmetic images.** -/
theorem norm_weilFullFunctional_sub_le (lam lam' : ℕ → ℝ) {k : ℝ → ℂ} {r K : ℝ}
    (hk : ∀ s, 2 * r < |s| → k s = 0) (hK : ∀ s, ‖k s‖ ≤ K) :
    ‖_root_.RHTower.weilFullFunctional lam k - _root_.RHTower.weilFullFunctional lam' k‖ ≤
      2 * primeDiscrepancy lam lam' r * K := by
  rw [weilFullFunctional_sub lam lam' hk, norm_neg, primeDiscrepancy,
    show 2 * (∑ n ∈ primeRange r, |primeWeight lam n - primeWeight lam' n|) * K =
      ∑ n ∈ primeRange r, 2 * |primeWeight lam n - primeWeight lam' n| * K by
        rw [Finset.mul_sum, Finset.sum_mul]]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h2 : ‖k (Real.log n) + k (-Real.log n)‖ ≤ 2 * K :=
    (norm_add_le _ _).trans (by linarith [hK (Real.log n), hK (-Real.log n)])
  nlinarith [abs_nonneg (primeWeight lam n - primeWeight lam' n)]

/-- **Stable pinning at height `T`.** -/
theorem norm_multDiff_mul_gaps_le_of_arithmetic {Z : ZeroConfig} (hZ : TemperedConfig Z)
    {S : Finset ℂ} (hS : ∀ z ∉ S, multDiff Z zetaZeroConfig z = 0) {z₀ : ℂ} (hz₀ : z₀ ∈ S)
    {r : ℝ} (T : ℝ) {b : ℝ → ℂ} (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbc : HasCompactSupport b)
    (hbs : tsupport b ⊆ Icc (-r) r) (hb1 : paperFT b (gammaOf z₀ - T) = 1)
    {g : ℝ → ℂ} (hg : ApertureWindow r g) (hg1 : paperFT g (conj (gammaOf z₀)) = 1)
    {M : ℝ} (hM : ∀ u, ‖g u‖ ≤ M) {lam : ℕ → ℝ}
    (hW : ∀ f h, ApertureWindow r f → ApertureWindow r h →
      Z.W f h = _root_.RHTower.weilFullFunctional lam (EF.weilTest f h)) :
    ‖multDiff Z zetaZeroConfig z₀‖ * ∏ z ∈ S.erase z₀, ‖gammaOf z₀ - gammaOf z‖ ≤
      2 * primeDiscrepancy lam (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) r *
        annihilatorBound ((S.erase z₀).image fun z => gammaOf z - T) b 0 * M := by
  obtain ⟨f, hfwin, hf0, hfw⟩ := exists_inverse_window_at_height S z₀ T hb hbc hbs
  have hb1' : paperFT (modulate T b) (gammaOf z₀) = 1 := by rw [paperFT_modulate, hb1]
  have hid := W_sub_W_eq_of_annihilating hZ temperedConfig_zetaZeroConfig hS hz₀ hb1' hfw
    hfwin hg hg1
  have hnorm : ‖Z.W f g - zetaZeroConfig.W f g‖ =
      ‖multDiff Z zetaZeroConfig z₀‖ * ∏ z ∈ S.erase z₀, ‖gammaOf z₀ - gammaOf z‖ := by
    rw [hid, norm_mul, norm_prod]
    congr 1
    refine Finset.prod_congr rfl fun z _ => ?_
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hfi : Integrable f := hfwin.1.continuous.integrable_of_hasCompactSupport
    hfwin.hasCompactSupport
  rw [← hnorm, hW f g hfwin hg, _root_.RHTower.zetaZeroConfig_W_eq_weilFullFunctional_bilinear
    hfwin.1 hfwin.hasCompactSupport hg.1 hg.hasCompactSupport]
  have hk := norm_weilFullFunctional_sub_le lam (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    (k := EF.weilTest f g) (r := r) (fun s hs => weilTest_eq_zero_of_lt hfwin.2 hg.2 hs)
    (norm_weilTest_le hfi hM)
  refine hk.trans ?_
  have hD := primeDiscrepancy_nonneg lam (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) r
  have := mul_le_mul_of_nonneg_right hf0 hM0
  nlinarith

/-- **Approximate primes pin separated points.** -/
theorem multDiff_eq_zero_of_arithmetic_precision {Z : ZeroConfig} (hZ : TemperedConfig Z)
    {S : Finset ℂ} (hS : ∀ z ∉ S, multDiff Z zetaZeroConfig z = 0) {z₀ : ℂ} (hz₀ : z₀ ∈ S)
    {r : ℝ} (T : ℝ) {b : ℝ → ℂ} (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbc : HasCompactSupport b)
    (hbs : tsupport b ⊆ Icc (-r) r) (hb1 : paperFT b (gammaOf z₀ - T) = 1)
    {g : ℝ → ℂ} (hg : ApertureWindow r g) (hg1 : paperFT g (conj (gammaOf z₀)) = 1)
    {M : ℝ} (hM : ∀ u, ‖g u‖ ≤ M) {lam : ℕ → ℝ}
    (hW : ∀ f h, ApertureWindow r f → ApertureWindow r h →
      Z.W f h = _root_.RHTower.weilFullFunctional lam (EF.weilTest f h))
    (hprec : 2 * primeDiscrepancy lam (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) r *
        annihilatorBound ((S.erase z₀).image fun z => gammaOf z - T) b 0 * M <
      ∏ z ∈ S.erase z₀, ‖gammaOf z₀ - gammaOf z‖) :
    multDiff Z zetaZeroConfig z₀ = 0 := by
  by_contra hne
  have hle := norm_multDiff_mul_gaps_le_of_arithmetic hZ hS hz₀ T hb hbc hbs hb1 hg hg1 hM hW
  obtain ⟨m, hm⟩ := exists_int_multDiff Z zetaZeroConfig z₀
  have hm0 : m ≠ 0 := fun h => hne (by rw [hm, h, Int.cast_zero])
  have h1 : (1 : ℝ) ≤ ‖multDiff Z zetaZeroConfig z₀‖ := by
    rw [hm, Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hm0
  have hP : 0 ≤ ∏ z ∈ S.erase z₀, ‖gammaOf z₀ - gammaOf z‖ :=
    Finset.prod_nonneg fun _ _ => norm_nonneg _
  nlinarith

end GaloisForLFunctions.ZeroConfigurationGeometry
