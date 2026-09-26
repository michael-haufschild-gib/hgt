import GaloisForLFunctions.RHTower.CCMRestrictedWeilPrimePolarArithmeticAction
import GaloisForLFunctions.RHTower.MertensFirst
import GaloisForLFunctions.RHTower.ChebyshevPsiScaling
import GaloisForLFunctions.RHTower.CCMConnesConsaniHilbertOne
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarConstrainedRightContinuity

open MeasureTheory Set Filter
open scoped ENNReal InnerProduct

/-!
# The prime-transport horizon law

The literal level-`a` prime part of the restricted Weil form (Connes--Consani's `Σ Λ(n) T(n)`,
compressed to the logarithmic aperture `[-a,a]`),

`T_a = Σ_{2 ≤ n ≤ e^{2a}} Λ(n) n^{-1/2} (τ_{log n} + τ_{-log n})`,

has operator norm `(1 + o(1)) e^a`.  The triangle-inequality bound `2 Σ Λ(n)/√n ≈ 4 e^a` and the
corpus's outer-shell bound `21 (e^a + e^{a/2})` both overstate it.

**Mechanism.** The weighted Schur test for a nonnegative translation kernel is run with the
*pole profile* `w(y) = e^{y/2} + e^{-y/2}`, the sum of the two rulings.  The corpus's exact ruling
action makes the Schur row sum a Chebyshev/Mertens combination:

`Σ_n Λ(n)n^{-1/2}(w(y-log n)1_I + w(y+log n)1_I) =
   e^{y/2}(ψ(e^{a-y}) + S₁(e^{a+y})) + e^{-y/2}(ψ(e^{a+y}) + S₁(e^{a-y}))`

(`primePoleRow_eq`).  A Chebyshev bound `ψ(X) ≤ RX + B√X + D` and a Mertens bound
`S₁(X) ≤ log X + c` then give `‖T_a‖ ≤ Re^a + Be^{a/2} + D + 2a + c`
(`norm_ccmFinitePrimeOperator_le_chebyshevMertens`).  The Rayleigh quotient of the pole vector
gives the matching lower bound from `ψ(X) ≥ (1-ε)X - K`.

**Main results.**
* `norm_ccmFinitePrimeOperator_le_log4`: `‖T_a‖ ≤ log 4 · e^a + 4a e^{a/2} + 2a + log 4 + 4` for
  every aperture.  This is unconditional, elementary, and has no PNT input.
* `primeTransport_horizon_law`: for every `ε ∈ (0,1)`, `(1-ε)e^a ≤ ‖T_a‖ ≤ (1+ε)e^a` for all large
  `a`, by the prime number theorem.  The pole profile is an asymptotic Perron vector.
* `ccmRestrictedWeilSourceQuadratic_ge_of_primeBound`: on pole-constrained vectors, the restricted
  Weil quadratic is at least the archimedean energy minus `(‖T_a‖ + |2γ₀-1|)` times the aperture
  mass.  So the level-`a` arithmetic Hodge index can fail only through spectral mass where the
  archimedean weight is below `(1+o(1))e^a`.

**Interpretation (route HF).** In Weil's proof for curves over `𝔽_q`, the Frobenius graph meets
the two rulings in degrees `(1, q)`.  Here the prime transport exchanges the two rulings `e^{±y/2}`
with coefficient `e^a·ψ(x)/x` and scales each by the Mertens sum (`primePoleRow_eq`).  PNT says this
exchange degree is `e^a(1+o(1))`, and the horizon of the level-`a` Hodge index sits at archimedean
height `≈ e^a`.  Negativity below that horizon requires a *shadow pole*: a height `t` where the
phases `n^{-it}`, `n ≤ e^{2a}`, align well enough to push the twisted Perron value near `‖T_a‖`.
Any argument that does not use the height (an operator bound independent of `t`) cannot place the
horizon lower, because `‖T_a‖ ≥ (1-ε)e^a`.

No RH input, no numerical computation, no axioms beyond the standard three.
-/

noncomputable section
namespace RHTower


/-- Weighted AM-GM for one translated pair, with the two endpoint cutoffs built into the
weights.  `F` vanishes outside `I`. -/
theorem translate_pair_pointwise (I : Set ℝ) (w : ℝ → ℝ) (hw : ∀ x, 0 < w x)
    (F : ℝ → ℝ) (_hF0 : ∀ x, 0 ≤ F x) (hFI : ∀ x, x ∉ I → F x = 0) (x h : ℝ) :
    F (x + h) * F x ≤
      (1/2) * (I.indicator w x / w (x + h)) * F (x + h) ^ 2 +
        (1/2) * (I.indicator w (x + h) / w x) * F x ^ 2 := by
  by_cases hx : x ∈ I
  · by_cases hxh : x + h ∈ I
    · rw [indicator_of_mem hx, indicator_of_mem hxh]
      have h1 := hw x
      have h2 := hw (x + h)
      have hid : (1/2) * (w x / w (x + h)) * F (x + h) ^ 2 +
          (1/2) * (w (x + h) / w x) * F x ^ 2 - F (x + h) * F x =
          (w x * F (x + h) - w (x + h) * F x) ^ 2 / (2 * w x * w (x + h)) := by
        field_simp
        ring
      have hnn : 0 ≤ (w x * F (x + h) - w (x + h) * F x) ^ 2 / (2 * w x * w (x + h)) := by
        positivity
      linarith
    · rw [hFI _ hxh]
      have : 0 ≤ (1/2) * (I.indicator w x / w (x + h)) * 0 ^ 2 +
          (1/2) * (I.indicator w (x + h) / w x) * F x ^ 2 := by
        rw [indicator_of_notMem hxh]; simp
      simpa using this
  · rw [hFI _ hx]
    have hnn : 0 ≤ (1/2) * (I.indicator w x / w (x + h)) * F (x + h) ^ 2 +
        (1/2) * (I.indicator w (x + h) / w x) * 0 ^ 2 := by
      rw [indicator_of_notMem hx]; simp
    simpa using hnn



theorem lintegral_translate_pair_le (I : Set ℝ) (hI : MeasurableSet I) (w : ℝ → ℝ)
    (hw : ∀ x, 0 < w x) (hwm : Measurable w)
    (F : ℝ → ℝ) (hF0 : ∀ x, 0 ≤ F x) (hFI : ∀ x, x ∉ I → F x = 0) (hFm : Measurable F)
    (h : ℝ) :
    ∫⁻ x, ENNReal.ofReal ((F (x + h) + F (x - h)) * F x) ≤
      ∫⁻ z, ENNReal.ofReal
        (F z ^ 2 * ((I.indicator w (z - h) + I.indicator w (z + h)) / w z)) := by
  set P : ℝ → ℝ := fun z => (1/2) * (I.indicator w (z - h) / w z) * F z ^ 2 with hP
  set Q : ℝ → ℝ := fun z => (1/2) * (I.indicator w (z + h) / w z) * F z ^ 2 with hQ
  have hind0 : ∀ y, 0 ≤ I.indicator w y := fun y => by
    by_cases hy : y ∈ I
    · rw [indicator_of_mem hy]; exact (hw y).le
    · rw [indicator_of_notMem hy]
  have hP0 : ∀ z, 0 ≤ P z := fun z => by
    have := hw z; have := hind0 (z - h); positivity
  have hQ0 : ∀ z, 0 ≤ Q z := fun z => by
    have := hw z; have := hind0 (z + h); positivity
  have hindm : Measurable (I.indicator w) := hwm.indicator hI
  have hPm : Measurable P := by
    apply Measurable.mul
    · apply Measurable.mul measurable_const
      exact (hindm.comp (measurable_id.sub_const h)).div hwm
    · exact hFm.pow_const 2
  have hQm : Measurable Q := by
    apply Measurable.mul
    · apply Measurable.mul measurable_const
      exact (hindm.comp (measurable_id.add_const h)).div hwm
    · exact hFm.pow_const 2
  have hpt : ∀ x, (F (x + h) + F (x - h)) * F x ≤ P (x + h) + Q x + Q (x - h) + P x := by
    intro x
    have h1 := translate_pair_pointwise I w hw F hF0 hFI x h
    have h2 := translate_pair_pointwise I w hw F hF0 hFI x (-h)
    have e1 : P (x + h) = (1/2) * (I.indicator w x / w (x + h)) * F (x + h) ^ 2 := by
      simp [hP]
    have e2 : Q (x - h) = (1/2) * (I.indicator w x / w (x + -h)) * F (x + -h) ^ 2 := by
      simp [hQ, sub_eq_add_neg]
    have e3 : P x = (1/2) * (I.indicator w (x + -h) / w x) * F x ^ 2 := by
      simp [hP, sub_eq_add_neg]
    have e4 : Q x = (1/2) * (I.indicator w (x + h) / w x) * F x ^ 2 := by simp [hQ]
    rw [e1, e2, e3, e4, ← sub_eq_add_neg] at *
    rw [sub_eq_add_neg] at h2 ⊢
    nlinarith [h1, h2]
  have mP : Measurable fun x => ENNReal.ofReal (P x) := hPm.ennreal_ofReal
  have mQ : Measurable fun x => ENNReal.ofReal (Q x) := hQm.ennreal_ofReal
  have mQs : Measurable fun x => ENNReal.ofReal (Q (x - h)) :=
    (hQm.comp (measurable_id.sub_const h)).ennreal_ofReal
  calc
    ∫⁻ x, ENNReal.ofReal ((F (x + h) + F (x - h)) * F x)
        ≤ ∫⁻ x, (ENNReal.ofReal (P (x + h)) + ENNReal.ofReal (Q x) +
            ENNReal.ofReal (Q (x - h)) + ENNReal.ofReal (P x)) := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [← ENNReal.ofReal_add (hP0 _) (hQ0 _), ← ENNReal.ofReal_add (by linarith [hP0 (x+h), hQ0 x]) (hQ0 _),
        ← ENNReal.ofReal_add (by linarith [hP0 (x+h), hQ0 x, hQ0 (x - h)]) (hP0 _)]
      exact ENNReal.ofReal_le_ofReal (hpt x)
    _ = (∫⁻ x, ENNReal.ofReal (P (x + h))) + (∫⁻ x, ENNReal.ofReal (Q x)) +
          (∫⁻ x, ENNReal.ofReal (Q (x - h))) + (∫⁻ x, ENNReal.ofReal (P x)) := by
      rw [lintegral_add_right _ mP, lintegral_add_right _ mQs, lintegral_add_right _ mQ]
    _ = (∫⁻ x, ENNReal.ofReal (P x)) + (∫⁻ x, ENNReal.ofReal (Q x)) +
          (∫⁻ x, ENNReal.ofReal (Q x)) + (∫⁻ x, ENNReal.ofReal (P x)) := by
      rw [lintegral_add_right_eq_self (fun z => ENNReal.ofReal (P z)) h]
      rw [show (fun x => ENNReal.ofReal (Q (x - h))) = fun x => (fun z => ENNReal.ofReal (Q z)) (x + -h)
        by funext x; simp [sub_eq_add_neg]]
      rw [lintegral_add_right_eq_self (fun z => ENNReal.ofReal (Q z)) (-h)]
    _ = ∫⁻ z, ENNReal.ofReal
        (F z ^ 2 * ((I.indicator w (z - h) + I.indicator w (z + h)) / w z)) := by
      rw [← lintegral_add_right _ mQ, ← lintegral_add_right _ mQ, ← lintegral_add_right _ mP]
      apply lintegral_congr
      intro z
      rw [← ENNReal.ofReal_add (hP0 _) (hQ0 _), ← ENNReal.ofReal_add (by linarith [hP0 z, hQ0 z]) (hQ0 _),
        ← ENNReal.ofReal_add (by linarith [hP0 z, hQ0 z]) (hP0 _)]
      congr 1
      simp only [hP, hQ]
      have := hw z
      field_simp
      ring



/-- The weighted Schur test for a finite family of symmetric translations with nonnegative
weights. -/
theorem lintegral_translation_sum_le (I : Set ℝ) (hI : MeasurableSet I) (w : ℝ → ℝ)
    (hw : ∀ x, 0 < w x) (hwm : Measurable w)
    (F : ℝ → ℝ) (hF0 : ∀ x, 0 ≤ F x) (hFI : ∀ x, x ∉ I → F x = 0) (hFm : Measurable F)
    (s : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (h : ℕ → ℝ) (L : ℝ)
    (hrow : ∀ z ∈ I, ∑ n ∈ s, c n * (I.indicator w (z - h n) + I.indicator w (z + h n))
      ≤ L * w z) :
    ∫⁻ x, ENNReal.ofReal (∑ n ∈ s, c n * ((F (x + h n) + F (x - h n)) * F x)) ≤
      ENNReal.ofReal L * ∫⁻ z, ENNReal.ofReal (F z ^ 2) := by
  have hind0 : ∀ y, 0 ≤ I.indicator w y := fun y => by
    by_cases hy : y ∈ I
    · rw [indicator_of_mem hy]; exact (hw y).le
    · rw [indicator_of_notMem hy]
  have hterm0 : ∀ n x, 0 ≤ c n * ((F (x + h n) + F (x - h n)) * F x) := fun n x => by
    have := hF0 (x + h n); have := hF0 (x - h n); have := hF0 x; have := hc n; positivity
  have hmeas : ∀ n, Measurable fun x => ENNReal.ofReal ((F (x + h n) + F (x - h n)) * F x) :=
    fun n => (((hFm.comp (measurable_id.add_const _)).add
      (hFm.comp (measurable_id.sub_const _))).mul hFm).ennreal_ofReal
  calc
    ∫⁻ x, ENNReal.ofReal (∑ n ∈ s, c n * ((F (x + h n) + F (x - h n)) * F x))
        = ∫⁻ x, ∑ n ∈ s, ENNReal.ofReal (c n) *
            ENNReal.ofReal ((F (x + h n) + F (x - h n)) * F x) := by
      apply lintegral_congr
      intro x
      rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => hterm0 n x)]
      apply Finset.sum_congr rfl
      intro n _
      rw [ENNReal.ofReal_mul (hc n)]
    _ = ∑ n ∈ s, ∫⁻ x, ENNReal.ofReal (c n) *
            ENNReal.ofReal ((F (x + h n) + F (x - h n)) * F x) :=
      lintegral_finsetSum _ (fun n _ => (hmeas n).const_mul _)
    _ = ∑ n ∈ s, ENNReal.ofReal (c n) *
            ∫⁻ x, ENNReal.ofReal ((F (x + h n) + F (x - h n)) * F x) := by
      apply Finset.sum_congr rfl
      intro n _
      exact lintegral_const_mul _ (hmeas n)
    _ ≤ ∑ n ∈ s, ENNReal.ofReal (c n) * ∫⁻ z, ENNReal.ofReal
          (F z ^ 2 * ((I.indicator w (z - h n) + I.indicator w (z + h n)) / w z)) := by
      apply Finset.sum_le_sum
      intro n _
      exact mul_le_mul_right (lintegral_translate_pair_le I hI w hw hwm F hF0 hFI hFm (h n)) _
    _ = ∫⁻ z, ENNReal.ofReal (F z ^ 2 *
          ((∑ n ∈ s, c n * (I.indicator w (z - h n) + I.indicator w (z + h n))) / w z)) := by
      have hindm : Measurable (I.indicator w) := hwm.indicator hI
      have hm2 : ∀ n, Measurable fun z => ENNReal.ofReal
          (F z ^ 2 * ((I.indicator w (z - h n) + I.indicator w (z + h n)) / w z)) := fun n =>
        ((hFm.pow_const 2).mul (((hindm.comp (measurable_id.sub_const _)).add
          (hindm.comp (measurable_id.add_const _))).div hwm)).ennreal_ofReal
      calc
        _ = ∑ n ∈ s, ∫⁻ z, ENNReal.ofReal (c n) * ENNReal.ofReal
            (F z ^ 2 * ((I.indicator w (z - h n) + I.indicator w (z + h n)) / w z)) := by
          apply Finset.sum_congr rfl
          intro n _
          exact (lintegral_const_mul _ (hm2 n)).symm
        _ = ∫⁻ z, ∑ n ∈ s, ENNReal.ofReal (c n) * ENNReal.ofReal
            (F z ^ 2 * ((I.indicator w (z - h n) + I.indicator w (z + h n)) / w z)) :=
          (lintegral_finsetSum _ (fun n _ => (hm2 n).const_mul _)).symm
        _ = _ := by
          apply lintegral_congr
          intro z
          have hwz := hw z
          rw [Finset.sum_div, Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
          · apply Finset.sum_congr rfl
            intro n _
            rw [← ENNReal.ofReal_mul (hc n)]
            congr 1
            ring
          · intro n _
            have := hind0 (z - h n); have := hind0 (z + h n); have := hc n
            positivity
    _ ≤ ∫⁻ z, ENNReal.ofReal L * ENNReal.ofReal (F z ^ 2) := by
      apply lintegral_mono
      intro z
      dsimp only
      rw [← ENNReal.ofReal_mul' (sq_nonneg _), mul_comm L]
      apply ENNReal.ofReal_le_ofReal
      by_cases hz : z ∈ I
      · apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        rw [div_le_iff₀ (hw z)]
        exact hrow z hz
      · rw [hFI z hz]; simp
    _ = ENNReal.ofReal L * ∫⁻ z, ENNReal.ofReal (F z ^ 2) := by
      rw [lintegral_const_mul]
      exact (hFm.pow_const 2).ennreal_ofReal


/-- Pointwise formula for the literal finite-prime operator on an arbitrary aperture vector. -/
theorem ccmFinitePrimeOperator_coeFn_translation (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) :
    ((ccmFinitePrimeOperator a f : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
        ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
          (centralInterval a.1).indicator
            (fun y => f.1 (y + Real.log n) + f.1 (y - Real.log n)) x := by
  classical
  let s := Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊
  let v : ℕ → SoninL2 := fun n =>
    (ArithmeticFunction.vonMangoldt n : ℂ) • (ccmPrimeTransportOperator a n f : SoninL2)
  have hval : (ccmFinitePrimeOperator a f : SoninL2) = ∑ n ∈ s, v n := by
    simp [ccmFinitePrimeOperator, s, v]
    apply Finset.sum_congr rfl
    intro n hn
    rfl
  have hatoms (n : ℕ) : ∀ᵐ x : ℝ, v n x =
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (centralInterval a.1).indicator
          (fun y => f.1 (y + Real.log n) + f.1 (y - Real.log n)) x := by
    have htr : (ccmPrimeTransportOperator a n f : SoninL2) =
        ((1 / Real.sqrt n : ℝ) : ℂ) •
          (ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log n)) f : SoninL2) := by
      rfl
    filter_upwards [Lp.coeFn_smul (ArithmeticFunction.vonMangoldt n : ℂ)
        (ccmPrimeTransportOperator a n f : SoninL2),
      Lp.coeFn_smul ((1 / Real.sqrt n : ℝ) : ℂ)
        (ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log n)) f : SoninL2),
      ccmApertureSymmetricTranslation_coeFn a (Real.log n) f] with x h1 h2 h3
    change ((ArithmeticFunction.vonMangoldt n : ℂ) •
      (ccmPrimeTransportOperator a n f : SoninL2)) x = _ 
    rw [h1]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [htr, h2]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h3]
    push_cast
    ring
  rw [hval]
  filter_upwards [Lp.coeFn_fun_finsetSum s v, ae_all_iff.mpr hatoms] with x hs ha
  rw [hs]
  exact Finset.sum_congr rfl fun n _ => ha n


/-- The pole profile `e^{y/2} + e^{-y/2}`, the sum of the two rulings. -/
def primePoleProfile (y : ℝ) : ℝ := Real.exp (y / 2) + Real.exp (-y / 2)

theorem primePoleProfile_pos (y : ℝ) : 0 < primePoleProfile y := by
  unfold primePoleProfile; positivity

theorem measurable_primePoleProfile : Measurable primePoleProfile := by
  unfold primePoleProfile
  fun_prop

/-- The weighted Schur quadratic bound for the literal finite-prime operator. -/
theorem norm_inner_ccmFinitePrimeOperator_le_of_poleRow (a : SuzukiPositiveAperture)
    (L : ℝ) (hL : 0 ≤ L)
    (hrow : ∀ z ∈ centralInterval a.1, ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
      (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        ((centralInterval a.1).indicator primePoleProfile (z - Real.log n) +
          (centralInterval a.1).indicator primePoleProfile (z + Real.log n)) ≤
        L * primePoleProfile z)
    (f : suzukiApertureHilbert a) :
    ‖inner ℂ (ccmFinitePrimeOperator a f) f‖ ≤ L * ‖f‖ ^ 2 := by
  classical
  set I := centralInterval a.1 with hIdef
  have hI : MeasurableSet I := measurableSet_centralInterval a.1
  set s := Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊ with hs
  set c : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n / Real.sqrt n with hc
  have hc0 : ∀ n, 0 ≤ c n := fun n =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  set F : ℝ → ℝ := I.indicator (fun x => ‖f.1 x‖) with hF
  have hF0 : ∀ x, 0 ≤ F x := fun x => by
    by_cases hx : x ∈ I
    · rw [hF, indicator_of_mem hx]; exact norm_nonneg _
    · rw [hF, indicator_of_notMem hx]
  have hFI : ∀ x, x ∉ I → F x = 0 := fun x hx => by rw [hF, indicator_of_notMem hx]
  have hFm : Measurable F :=
    ((Lp.stronglyMeasurable f.1).measurable.norm).indicator hI
  -- the aperture vector vanishes off the aperture
  have hzero : ∀ᵐ y, ‖f.1 y‖ = F y := by
    have hc := indicatorCutoff_ae I hI f.1
    rw [indicatorCutoff_suzukiApertureHilbert] at hc
    filter_upwards [hc] with y hy
    by_cases hyI : y ∈ I
    · rw [hF, indicator_of_mem hyI]
    · rw [hF, indicator_of_notMem hyI, hy, indicator_of_notMem hyI, norm_zero]
  have hshift : ∀ h : ℝ, ∀ᵐ x, ‖f.1 (x + h)‖ = F (x + h) := fun h =>
    (measurePreserving_add_right volume h).quasiMeasurePreserving.ae hzero
  have hshifts : ∀ᵐ x, ∀ n : ℕ, ‖f.1 (x + Real.log n)‖ = F (x + Real.log n) ∧
      ‖f.1 (x - Real.log n)‖ = F (x - Real.log n) := by
    rw [ae_all_iff]
    intro n
    filter_upwards [hshift (Real.log n), hshift (-Real.log n)] with x h1 h2
    exact ⟨h1, by rw [sub_eq_add_neg]; exact h2⟩
  -- pointwise domination of the Rayleigh integrand
  have hpt : ∀ᵐ x, ENNReal.ofReal ‖inner ℂ ((ccmFinitePrimeOperator a f : SoninL2) x) (f.1 x)‖ ≤
      ENNReal.ofReal (∑ n ∈ s, c n * ((F (x + Real.log n) + F (x - Real.log n)) * F x)) := by
    filter_upwards [ccmFinitePrimeOperator_coeFn_translation a f, hshifts, hzero] with x hT hsh hz
    apply ENNReal.ofReal_le_ofReal
    have hRnn : 0 ≤ ∑ n ∈ s, c n * ((F (x + Real.log n) + F (x - Real.log n)) * F x) :=
      Finset.sum_nonneg fun n _ => by
        have := hF0 (x + Real.log n); have := hF0 (x - Real.log n); have := hF0 x
        have := hc0 n; positivity
    by_cases hx : x ∈ I
    · calc
        ‖inner ℂ ((ccmFinitePrimeOperator a f : SoninL2) x) (f.1 x)‖
            ≤ ‖(ccmFinitePrimeOperator a f : SoninL2) x‖ * ‖f.1 x‖ := norm_inner_le_norm _ _
        _ ≤ (∑ n ∈ s, c n * (F (x + Real.log n) + F (x - Real.log n))) * F x := by
          rw [hz]
          apply mul_le_mul_of_nonneg_right _ (hF0 x)
          rw [hT]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
          rw [indicator_of_mem hx, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (hc0 n)]
          apply mul_le_mul_of_nonneg_left _ (hc0 n)
          rw [← (hsh n).1, ← (hsh n).2]
          exact norm_add_le _ _
        _ = ∑ n ∈ s, c n * ((F (x + Real.log n) + F (x - Real.log n)) * F x) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun n _ => by ring
    · have h0 : (ccmFinitePrimeOperator a f : SoninL2) x = 0 := by
        rw [hT]
        exact Finset.sum_eq_zero fun n _ => by rw [indicator_of_notMem hx, mul_zero]
      rw [h0, inner_zero_left, norm_zero]
      exact hRnn
  -- the Schur test
  have hrow' : ∀ z ∈ I, ∑ n ∈ s, c n * (I.indicator primePoleProfile (z - Real.log n) +
      I.indicator primePoleProfile (z + Real.log n)) ≤ L * primePoleProfile z := hrow
  have hschur := lintegral_translation_sum_le I hI primePoleProfile primePoleProfile_pos
    measurable_primePoleProfile F hF0 hFI hFm s c hc0 (fun n => Real.log n) L hrow'
  -- the energy
  set X : ℝ≥0∞ := ∫⁻ z, ENNReal.ofReal (‖f.1 z‖ ^ 2) with hX
  have hFX : ∫⁻ z, ENNReal.ofReal (F z ^ 2) ≤ X := by
    apply lintegral_mono
    intro z
    apply ENNReal.ofReal_le_ofReal
    by_cases hz : z ∈ I
    · rw [hF, indicator_of_mem hz]
    · rw [hF, indicator_of_notMem hz]
      nlinarith [norm_nonneg (f.1 z)]
  have hint : Integrable (fun z => ‖f.1 z‖ ^ 2) :=
    (MeasureTheory.Lp.memLp f.1).integrable_norm_pow (by norm_num)
  have hXfin : X ≠ ∞ := by
    have hfi := hint.2
    rw [hX]
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) hfi)
    apply lintegral_congr
    intro z
    rw [Real.enorm_eq_ofReal (by positivity)]
  have hnormsq : ‖f‖ ^ 2 = X.toReal := by
    have hL2 : ‖f.1‖ ^ 2 = ∫ x : ℝ, ‖(f.1 : ℝ → ℂ) x‖ ^ 2 := by
      have h2 := MeasureTheory.L2.inner_def (𝕜 := ℂ) f.1 f.1
      rw [inner_self_eq_norm_sq_to_K] at h2
      have h3 : ∀ x : ℝ, inner ℂ ((f.1 : ℝ → ℂ) x) ((f.1 : ℝ → ℂ) x)
          = ((‖(f.1 : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
        intro x
        rw [inner_self_eq_norm_sq_to_K]
        norm_cast
      simp_rw [h3] at h2
      rw [integral_complex_ofReal] at h2
      apply Complex.ofReal_injective
      rw [← h2]
      push_cast
      rfl
    rw [show ‖f‖ = ‖f.1‖ from rfl, hL2, hX,
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z => by positivity)
        hint.aestronglyMeasurable]
  -- assemble
  calc
    ‖inner ℂ (ccmFinitePrimeOperator a f) f‖
        = ‖∫ x, inner ℂ ((ccmFinitePrimeOperator a f : SoninL2) x) (f.1 x)‖ := by
      rw [Submodule.coe_inner, MeasureTheory.L2.inner_def]
    _ ≤ (∫⁻ x, ENNReal.ofReal
          ‖inner ℂ ((ccmFinitePrimeOperator a f : SoninL2) x) (f.1 x)‖).toReal :=
      norm_integral_le_lintegral_norm _
    _ ≤ (ENNReal.ofReal L * X).toReal := by
      apply ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hXfin)
      exact (lintegral_mono_ae hpt).trans (hschur.trans (mul_le_mul_right hFX _))
    _ = L * ‖f‖ ^ 2 := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hL, hnormsq]

/-- Operator-norm form of the weighted Schur test. -/
theorem norm_ccmFinitePrimeOperator_le_of_poleRow (a : SuzukiPositiveAperture)
    (L : ℝ) (hL : 0 ≤ L)
    (hrow : ∀ z ∈ centralInterval a.1, ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
      (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        ((centralInterval a.1).indicator primePoleProfile (z - Real.log n) +
          (centralInterval a.1).indicator primePoleProfile (z + Real.log n)) ≤
        L * primePoleProfile z) :
    ‖ccmFinitePrimeOperator a‖ ≤ L := by
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _
    (ccmFinitePrimeOperator_isSelfAdjoint a).isSymmetric]
  apply ciSup_le
  intro f
  by_cases hf : f = 0
  · subst hf; simp [hL]
  have hpos : 0 < ‖f‖ ^ 2 := by positivity
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  exact (RCLike.abs_re_le_norm _).trans
    (norm_inner_ccmFinitePrimeOperator_le_of_poleRow a L hL hrow f)

private theorem sum_log_cutoff' (a : ℝ) (f : ℕ → ℝ) {y : ℝ} (hy : y ≤ 2 * a) :
    (∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, if Real.log n ≤ y then f n else 0) =
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp y⌋₊, f n := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc]
  by_cases hn : 2 ≤ n
  · have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have heq : Real.log n ≤ y ↔ n ≤ ⌊Real.exp y⌋₊ :=
      (Real.log_le_iff_le_exp hnR).trans (Nat.le_floor_iff (Real.exp_pos y).le).symm
    have hfloor := Nat.floor_mono (Real.exp_le_exp.mpr hy)
    rw [heq]
    omega
  · simp [hn]

private theorem psi_eq_sum_from_two' (X : ℝ) :
    Chebyshev.psi X = ∑ n ∈ Finset.Icc 2 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n := by
  rw [Chebyshev.psi_eq_sum_Icc]
  symm
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    exact ⟨Nat.zero_le _, hn.2⟩
  · intro n hn hnot
    simp only [Finset.mem_Icc] at hn hnot
    have hsmall : n = 0 ∨ n = 1 := by omega
    rcases hsmall with rfl | rfl <;> simp

/-- **Exact ruling row sum.**  On the aperture, the weighted row sum of the literal
prime transport against the pole profile is a Chebyshev/Mertens combination. -/
theorem primePoleRow_eq (a : SuzukiPositiveAperture) {z : ℝ} (hz : z ∈ centralInterval a.1) :
    ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
      (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        ((centralInterval a.1).indicator primePoleProfile (z - Real.log n) +
          (centralInterval a.1).indicator primePoleProfile (z + Real.log n)) =
      Real.exp (z / 2) * (Chebyshev.psi (Real.exp (a.1 - z)) +
          ccmReciprocalMangoldtCumulative (Real.exp (a.1 + z))) +
        Real.exp (-z / 2) * (Chebyshev.psi (Real.exp (a.1 + z)) +
          ccmReciprocalMangoldtCumulative (Real.exp (a.1 - z))) := by
  classical
  have hz' : -a.1 ≤ z ∧ z ≤ a.1 := hz
  -- termwise evaluation
  have hterm : ∀ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
      (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        ((centralInterval a.1).indicator primePoleProfile (z - Real.log n) +
          (centralInterval a.1).indicator primePoleProfile (z + Real.log n)) =
      (if Real.log n ≤ a.1 + z then
          Real.exp (z / 2) * (ArithmeticFunction.vonMangoldt n / n) +
            Real.exp (-z / 2) * ArithmeticFunction.vonMangoldt n else 0) +
      (if Real.log n ≤ a.1 - z then
          Real.exp (z / 2) * ArithmeticFunction.vonMangoldt n +
            Real.exp (-z / 2) * (ArithmeticFunction.vonMangoldt n / n) else 0) := by
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlogpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hsq : Real.sqrt n ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hnR)
    have hsq2 : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hnR.le
    have hexp_half : Real.exp (Real.log n / 2) = Real.sqrt n := by
      rw [← Real.log_sqrt hnR.le, Real.exp_log (Real.sqrt_pos.mpr hnR)]
    have hminus : (z - Real.log n ∈ centralInterval a.1) ↔ Real.log n ≤ a.1 + z := by
      constructor
      · intro h; have := h.1; linarith
      · intro h; exact ⟨by linarith, by linarith⟩
    have hplus : (z + Real.log n ∈ centralInterval a.1) ↔ Real.log n ≤ a.1 - z := by
      constructor
      · intro h; have := h.2; linarith
      · intro h; exact ⟨by linarith, by linarith⟩
    have e1 : (1 / Real.sqrt n) * primePoleProfile (z - Real.log n) =
        Real.exp (z / 2) / n + Real.exp (-z / 2) := by
      unfold primePoleProfile
      rw [show (z - Real.log n) / 2 = z / 2 + -(Real.log n / 2) by ring,
        show -(z - Real.log n) / 2 = -z / 2 + Real.log n / 2 by ring,
        Real.exp_add, Real.exp_add, Real.exp_neg, hexp_half]
      field_simp
      rw [hsq2]
      ring
    have e2 : (1 / Real.sqrt n) * primePoleProfile (z + Real.log n) =
        Real.exp (z / 2) + Real.exp (-z / 2) / n := by
      unfold primePoleProfile
      rw [show (z + Real.log n) / 2 = z / 2 + Real.log n / 2 by ring,
        show -(z + Real.log n) / 2 = -z / 2 + -(Real.log n / 2) by ring,
        Real.exp_add, Real.exp_add, Real.exp_neg, hexp_half]
      field_simp
      rw [hsq2]
      ring
    rw [mul_add]
    congr 1
    · by_cases h : Real.log n ≤ a.1 + z
      · rw [if_pos h, indicator_of_mem (hminus.mpr h), div_eq_mul_one_div,
          mul_assoc, e1]
        ring
      · rw [if_neg h, indicator_of_notMem (mt hminus.mp h), mul_zero]
    · by_cases h : Real.log n ≤ a.1 - z
      · rw [if_pos h, indicator_of_mem (hplus.mpr h), div_eq_mul_one_div,
          mul_assoc, e2]
        ring
      · rw [if_neg h, indicator_of_notMem (mt hplus.mp h), mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  have hA := sum_log_cutoff' a.1 (fun n => Real.exp (z / 2) * (ArithmeticFunction.vonMangoldt n / n) +
      Real.exp (-z / 2) * ArithmeticFunction.vonMangoldt n) (y := a.1 + z) (by linarith [hz'.2])
  have hB := sum_log_cutoff' a.1 (fun n => Real.exp (z / 2) * ArithmeticFunction.vonMangoldt n +
      Real.exp (-z / 2) * (ArithmeticFunction.vonMangoldt n / n)) (y := a.1 - z) (by linarith [hz'.1])
  rw [hA, hB, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, psi_eq_sum_from_two', psi_eq_sum_from_two',
    ccmReciprocalMangoldtCumulative, ccmReciprocalMangoldtCumulative]
  ring


theorem two_le_primePoleProfile (y : ℝ) : 2 ≤ primePoleProfile y := by
  unfold primePoleProfile
  have h1 := Real.add_one_le_exp (y / 2)
  have h2 := Real.add_one_le_exp (-y / 2)
  have hmul : Real.exp (y / 2) * Real.exp (-y / 2) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  nlinarith [Real.exp_pos (y / 2), Real.exp_pos (-y / 2),
    sq_nonneg (Real.exp (y / 2) - Real.exp (-y / 2))]

/-- **Pole-row Chebyshev–Mertens bound.**  Any affine-plus-square-root Chebyshev bound and any
Mertens bound on `[1, e^{2a}]` turn into a Schur row bound for the literal prime transport. -/
theorem primePoleRow_le (a : SuzukiPositiveAperture) (R B D c : ℝ) (hB : 0 ≤ B)
    (hψ : ∀ X : ℝ, 1 ≤ X → X ≤ Real.exp (2 * a.1) →
      Chebyshev.psi X ≤ R * X + B * Real.sqrt X + D)
    (hS : ∀ X : ℝ, 1 ≤ X → X ≤ Real.exp (2 * a.1) →
      ccmReciprocalMangoldtCumulative X ≤ Real.log X + c)
    {z : ℝ} (hz : z ∈ centralInterval a.1) :
    ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
      (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        ((centralInterval a.1).indicator primePoleProfile (z - Real.log n) +
          (centralInterval a.1).indicator primePoleProfile (z + Real.log n)) ≤
      (R * Real.exp a.1 + B * Real.exp (a.1 / 2) + D + 2 * a.1 + c) * primePoleProfile z := by
  have hz' : -a.1 ≤ z ∧ z ≤ a.1 := hz
  rw [primePoleRow_eq a hz]
  set E1 := Real.exp (z / 2) with hE1
  set E2 := Real.exp (-z / 2) with hE2
  have hE1p : 0 < E1 := Real.exp_pos _
  have hE2p : 0 < E2 := Real.exp_pos _
  have hX1 : 1 ≤ Real.exp (a.1 - z) := Real.one_le_exp (by linarith)
  have hX2 : 1 ≤ Real.exp (a.1 + z) := Real.one_le_exp (by linarith)
  have hX1' : Real.exp (a.1 - z) ≤ Real.exp (2 * a.1) := Real.exp_le_exp.mpr (by linarith)
  have hX2' : Real.exp (a.1 + z) ≤ Real.exp (2 * a.1) := Real.exp_le_exp.mpr (by linarith)
  have hp1 := hψ _ hX1 hX1'
  have hp2 := hψ _ hX2 hX2'
  have hs1 := hS _ hX1 hX1'
  have hs2 := hS _ hX2 hX2'
  rw [Real.log_exp] at hs1 hs2
  have hsq1 : Real.sqrt (Real.exp (a.1 - z)) = Real.exp ((a.1 - z) / 2) := by
    rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
    ring_nf
  have hsq2 : Real.sqrt (Real.exp (a.1 + z)) = Real.exp ((a.1 + z) / 2) := by
    rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
    ring_nf
  rw [hsq1] at hp1
  rw [hsq2] at hp2
  -- exponential bookkeeping
  have k1 : E1 * Real.exp (a.1 - z) = Real.exp a.1 * E2 := by
    rw [hE1, hE2, ← Real.exp_add, ← Real.exp_add]; ring_nf
  have k2 : E2 * Real.exp (a.1 + z) = Real.exp a.1 * E1 := by
    rw [hE1, hE2, ← Real.exp_add, ← Real.exp_add]; ring_nf
  have k3 : E1 * Real.exp ((a.1 - z) / 2) = Real.exp (a.1 / 2) := by
    rw [hE1, ← Real.exp_add]; ring_nf
  have k4 : E2 * Real.exp ((a.1 + z) / 2) = Real.exp (a.1 / 2) := by
    rw [hE2, ← Real.exp_add]; ring_nf
  have hw : primePoleProfile z = E1 + E2 := rfl
  have hw2 : 2 ≤ E1 + E2 := hw ▸ two_le_primePoleProfile z
  have hB2 : 2 * (B * Real.exp (a.1 / 2)) ≤ B * Real.exp (a.1 / 2) * (E1 + E2) := by
    have := Real.exp_pos (a.1 / 2)
    nlinarith [mul_nonneg hB this.le]
  have hzr : z * (E1 - E2) ≤ a.1 * (E1 + E2) := by nlinarith
  rw [hw]
  calc
    E1 * (Chebyshev.psi (Real.exp (a.1 - z)) + ccmReciprocalMangoldtCumulative (Real.exp (a.1 + z))) +
        E2 * (Chebyshev.psi (Real.exp (a.1 + z)) + ccmReciprocalMangoldtCumulative (Real.exp (a.1 - z)))
        ≤ E1 * ((R * Real.exp (a.1 - z) + B * Real.exp ((a.1 - z) / 2) + D) + (a.1 + z + c)) +
          E2 * ((R * Real.exp (a.1 + z) + B * Real.exp ((a.1 + z) / 2) + D) + (a.1 - z + c)) := by
      gcongr
    _ = R * Real.exp a.1 * (E1 + E2) + 2 * (B * Real.exp (a.1 / 2)) + D * (E1 + E2) +
          (a.1 + c) * (E1 + E2) + z * (E1 - E2) := by
      linear_combination R * k1 + R * k2 + B * k3 + B * k4
    _ ≤ (R * Real.exp a.1 + B * Real.exp (a.1 / 2) + D + 2 * a.1 + c) * (E1 + E2) := by
      nlinarith [hB2, hzr]

/-- **Pole-profile Schur bound for the literal prime transport.** -/
theorem norm_ccmFinitePrimeOperator_le_chebyshevMertens (a : SuzukiPositiveAperture)
    (R B D c : ℝ) (hB : 0 ≤ B)
    (hψ : ∀ X : ℝ, 1 ≤ X → X ≤ Real.exp (2 * a.1) →
      Chebyshev.psi X ≤ R * X + B * Real.sqrt X + D)
    (hS : ∀ X : ℝ, 1 ≤ X → X ≤ Real.exp (2 * a.1) →
      ccmReciprocalMangoldtCumulative X ≤ Real.log X + c) :
    ‖ccmFinitePrimeOperator a‖ ≤ R * Real.exp a.1 + B * Real.exp (a.1 / 2) + D + 2 * a.1 + c := by
  set L := R * Real.exp a.1 + B * Real.exp (a.1 / 2) + D + 2 * a.1 + c
  have hrow := fun z (hz : z ∈ centralInterval a.1) => primePoleRow_le a R B D c hB hψ hS hz
  have hL : 0 ≤ L := by
    have h0 : (0 : ℝ) ∈ centralInterval a.1 := ⟨by linarith [a.property], a.property.le⟩
    have hr := hrow 0 h0
    have hnn : 0 ≤ ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          ((centralInterval a.1).indicator primePoleProfile (0 - Real.log n) +
            (centralInterval a.1).indicator primePoleProfile (0 + Real.log n)) := by
      apply Finset.sum_nonneg
      intro n _
      apply mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
      apply add_nonneg
      · by_cases h : (0 - Real.log n) ∈ centralInterval a.1
        · rw [indicator_of_mem h]; exact (primePoleProfile_pos _).le
        · rw [indicator_of_notMem h]
      · by_cases h : (0 + Real.log n) ∈ centralInterval a.1
        · rw [indicator_of_mem h]; exact (primePoleProfile_pos _).le
        · rw [indicator_of_notMem h]
    have := primePoleProfile_pos 0
    by_contra hneg
    have hneg' : L < 0 := lt_of_not_ge hneg
    nlinarith
  exact norm_ccmFinitePrimeOperator_le_of_poleRow a L hL hrow

/-- The Mertens cumulative on reals, from the corpus's integer Mertens theorem. -/
theorem ccmReciprocalMangoldtCumulative_le_log_add (X : ℝ) (hX : 1 ≤ X) :
    ccmReciprocalMangoldtCumulative X ≤ Real.log X + (Real.log 4 + 4) := by
  have hN : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
  have hm := Mertens.mertens_first ⌊X⌋₊ hN
  have hsum : ccmReciprocalMangoldtCumulative X =
      ∑ d ∈ Finset.Icc 1 ⌊X⌋₊, ArithmeticFunction.vonMangoldt d / d := by
    unfold ccmReciprocalMangoldtCumulative
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_Icc] at hn ⊢
      omega
    · intro n hn hnot
      simp only [Finset.mem_Icc] at hn hnot
      have h1 : n = 1 := by omega
      subst h1
      simp
  have hfl : Real.log (⌊X⌋₊ : ℝ) ≤ Real.log X :=
    Real.log_le_log (by exact_mod_cast (show 0 < ⌊X⌋₊ by omega)) (Nat.floor_le (by linarith))
  rw [hsum]
  have := (abs_le.mp hm).2
  linarith

/-- **Explicit pole-Schur bound.**  `‖T_a‖ ≤ log 4 · e^a + 4a e^{a/2} + 2a + log 4 + 4`. -/
theorem norm_ccmFinitePrimeOperator_le_log4 (a : SuzukiPositiveAperture) :
    ‖ccmFinitePrimeOperator a‖ ≤
      Real.log 4 * Real.exp a.1 + 4 * a.1 * Real.exp (a.1 / 2) + 2 * a.1 + (Real.log 4 + 4) := by
  have ha := a.property
  have h := norm_ccmFinitePrimeOperator_le_chebyshevMertens a (Real.log 4) (4 * a.1) 0
    (Real.log 4 + 4) (by linarith)
    (fun X hX hXa => by
      have hp := Chebyshev.psi_le hX
      have hlog : Real.log X ≤ 2 * a.1 := by
        rw [← Real.log_exp (2 * a.1)]; exact Real.log_le_log (by linarith) hXa
      have hsq := Real.sqrt_nonneg X
      nlinarith [Real.log_nonneg hX])
    (fun X hX _ => ccmReciprocalMangoldtCumulative_le_log_add X hX)
  linarith

/-- **Sharp asymptotic upper bound.**  By the prime number theorem, for every `ε > 0` the literal
prime transport satisfies `‖T_a‖ ≤ (1+ε) e^a` for all large apertures. -/
theorem exists_norm_ccmFinitePrimeOperator_le_one_add (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, ∀ a : SuzukiPositiveAperture, A ≤ a.1 →
      ‖ccmFinitePrimeOperator a‖ ≤ (1 + ε) * Real.exp a.1 := by
  have hpnt := tendsto_chebyshevPsiReal_div
  have hev : ∀ᶠ x : ℝ in Filter.atTop, chebyshevPsiReal x / x < 1 + ε / 2 :=
    hpnt (Iio_mem_nhds (by linarith))
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp hev
  set x₀ := max x₁ 1 with hx₀
  have hx₀1 : 1 ≤ x₀ := le_max_right _ _
  set D := Chebyshev.psi x₀ with hD
  have hD0 : 0 ≤ D := Chebyshev.psi_nonneg _
  set K := Real.log 4 + 4 with hK
  have hK0 : 0 ≤ K := by
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4); linarith
  have hψ : ∀ X : ℝ, 1 ≤ X → Chebyshev.psi X ≤ (1 + ε / 2) * X + 0 * Real.sqrt X + D := by
    intro X hX
    by_cases hXx : x₀ ≤ X
    · have h1 := hx₁ X (le_trans (le_max_left _ _) hXx)
      have hident : chebyshevPsiReal X = Chebyshev.psi X := by
        rw [chebyshevPsiReal_eq_sum_range, Chebyshev.psi_eq_sum_Icc]
        congr 1
        ext n
        simp
      rw [hident, div_lt_iff₀ (by linarith)] at h1
      nlinarith
    · have hmono := Chebyshev.psi_mono (le_of_lt (lt_of_not_ge hXx))
      nlinarith
  refine ⟨16 / ε + 8 * (D + K) / ε + 1, fun a haA => ?_⟩
  have ha1 : 1 ≤ a.1 := by
    have : 0 ≤ 16 / ε + 8 * (D + K) / ε := by positivity
    linarith
  have hbound := norm_ccmFinitePrimeOperator_le_chebyshevMertens a (1 + ε / 2) 0 D K le_rfl
    (fun X hX _ => hψ X hX) (fun X hX _ => ccmReciprocalMangoldtCumulative_le_log_add X hX)
  have hquad := Real.quadratic_le_exp_of_nonneg (show 0 ≤ a.1 by linarith)
  have hA1 : 16 / ε ≤ a.1 := by
    have : 0 ≤ 8 * (D + K) / ε := by positivity
    linarith
  have hA2 : 8 * (D + K) / ε ≤ a.1 := by
    have : 0 ≤ 16 / ε := by positivity
    linarith
  have h1 : 16 ≤ ε * a.1 := by
    rw [div_le_iff₀ hε] at hA1
    linarith
  have h2 : 8 * (D + K) ≤ ε * a.1 := by
    rw [div_le_iff₀ hε] at hA2
    linarith
  have hkey : 2 * a.1 + D + K ≤ ε / 2 * Real.exp a.1 := by
    nlinarith [mul_le_mul_of_nonneg_left ha1 hε.le]
  nlinarith [hbound]

/-- `L²` norm squared as an integral (inlined from the corpus's Gaussian carrier). -/
private theorem soninL2_norm_sq_eq_integral (f : SoninL2) :
    ‖f‖ ^ 2 = ∫ x : ℝ, ‖(f : ℝ → ℂ) x‖ ^ 2 := by
  have h2 := MeasureTheory.L2.inner_def (𝕜 := ℂ) f f
  rw [inner_self_eq_norm_sq_to_K] at h2
  have h3 : ∀ x : ℝ, inner ℂ ((f : ℝ → ℂ) x) ((f : ℝ → ℂ) x)
      = ((‖(f : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  simp_rw [h3] at h2
  rw [integral_complex_ofReal] at h2
  apply Complex.ofReal_injective
  rw [← h2]
  push_cast
  rfl

/-- The pole vector `h₊ + h₋ = 1_{[-a,a]} (e^{x/2} + e^{-x/2})`. -/
def primePoleApertureVector (a : SuzukiPositiveAperture) : suzukiApertureHilbert a :=
  ccmPolarApertureVector a (1 / 2) + ccmPolarApertureVector a (-1 / 2)

theorem primePoleApertureVector_coeFn (a : SuzukiPositiveAperture) :
    ((primePoleApertureVector a : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => (((centralInterval a.1).indicator primePoleProfile x : ℝ) : ℂ) := by
  filter_upwards [Lp.coeFn_add (ccmPolarApertureVector a (1 / 2) : SoninL2)
      (ccmPolarApertureVector a (-1 / 2) : SoninL2),
    ccmPolarL2Vector_coeFn a (1 / 2), ccmPolarL2Vector_coeFn a (-1 / 2)] with x hadd hp hm
  change ((ccmPolarApertureVector a (1 / 2) : SoninL2) +
    (ccmPolarApertureVector a (-1 / 2) : SoninL2)) x = _
  rw [hadd, Pi.add_apply]
  change (ccmPolarL2Vector a (1 / 2)) x + (ccmPolarL2Vector a (-1 / 2)) x = _
  rw [hp, hm]
  by_cases hx : x ∈ centralInterval a.1
  · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx]
    simp only [ccmPolarProfile, primePoleProfile]
    push_cast
    ring_nf
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, indicator_of_notMem hx]
    simp

/-- Exact action of the literal prime transport on the pole vector. -/
theorem ccmFinitePrimeOperator_primePole_coeFn (a : SuzukiPositiveAperture) :
    ((ccmFinitePrimeOperator a (primePoleApertureVector a) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => (((centralInterval a.1).indicator (fun z =>
        Real.exp (z / 2) * (Chebyshev.psi (Real.exp (a.1 - z)) +
            ccmReciprocalMangoldtCumulative (Real.exp (a.1 + z))) +
          Real.exp (-z / 2) * (Chebyshev.psi (Real.exp (a.1 + z)) +
            ccmReciprocalMangoldtCumulative (Real.exp (a.1 - z)))) x : ℝ) : ℂ) := by
  have hmap : (ccmFinitePrimeOperator a (primePoleApertureVector a) : SoninL2) =
      (ccmFinitePrimeOperator a (ccmPolarApertureVector a (1 / 2)) : SoninL2) +
        (ccmFinitePrimeOperator a (ccmPolarApertureVector a (-1 / 2)) : SoninL2) := by
    rw [primePoleApertureVector, map_add]; rfl
  rw [hmap]
  filter_upwards [Lp.coeFn_add
      (ccmFinitePrimeOperator a (ccmPolarApertureVector a (1 / 2)) : SoninL2)
      (ccmFinitePrimeOperator a (ccmPolarApertureVector a (-1 / 2)) : SoninL2),
    ccmFinitePrimeOperator_polarPlus_coeFn a, ccmFinitePrimeOperator_polarMinus_coeFn a]
    with x hadd hp hm
  rw [hadd, Pi.add_apply, hp, hm]
  by_cases hx : x ∈ centralInterval a.1
  · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx]
    push_cast
    ring
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, indicator_of_notMem hx]
    simp

/-- **Rayleigh lower bound.**  If on the aperture the pole row sum dominates `λ · w` with
`λ ≥ 0`, then `‖T_a‖ ≥ λ`. -/
theorem le_norm_ccmFinitePrimeOperator_of_poleRow_ge (a : SuzukiPositiveAperture)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hrow : ∀ z ∈ centralInterval a.1, lam * primePoleProfile z ≤
      Real.exp (z / 2) * (Chebyshev.psi (Real.exp (a.1 - z)) +
          ccmReciprocalMangoldtCumulative (Real.exp (a.1 + z))) +
        Real.exp (-z / 2) * (Chebyshev.psi (Real.exp (a.1 + z)) +
          ccmReciprocalMangoldtCumulative (Real.exp (a.1 - z)))) :
    lam ≤ ‖ccmFinitePrimeOperator a‖ := by
  set p := primePoleApertureVector a with hp
  set T := ccmFinitePrimeOperator a with hT
  have hpt : ∀ᵐ x, lam ^ 2 * ‖(p : SoninL2) x‖ ^ 2 ≤ ‖(T p : SoninL2) x‖ ^ 2 := by
    filter_upwards [primePoleApertureVector_coeFn a, ccmFinitePrimeOperator_primePole_coeFn a]
      with x hpx hTx
    rw [hpx, hTx, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      sq_abs, sq_abs]
    by_cases hx : x ∈ centralInterval a.1
    · rw [indicator_of_mem hx, indicator_of_mem hx]
      have h1 := hrow x hx
      have h0 : 0 ≤ lam * primePoleProfile x := mul_nonneg hlam (primePoleProfile_pos x).le
      nlinarith
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
      simp
  have hint1 : Integrable (fun x => ‖(T p : SoninL2) x‖ ^ 2) :=
    (MeasureTheory.Lp.memLp (T p : SoninL2)).integrable_norm_pow (by norm_num)
  have hint2 : Integrable (fun x => lam ^ 2 * ‖(p : SoninL2) x‖ ^ 2) :=
    ((MeasureTheory.Lp.memLp (p : SoninL2)).integrable_norm_pow (by norm_num)).const_mul _
  have hsq : lam ^ 2 * ‖p‖ ^ 2 ≤ ‖T p‖ ^ 2 := by
    rw [show ‖p‖ = ‖(p : SoninL2)‖ from rfl, show ‖T p‖ = ‖(T p : SoninL2)‖ from rfl,
      soninL2_norm_sq_eq_integral, soninL2_norm_sq_eq_integral, ← integral_const_mul]
    exact integral_mono_ae hint2 hint1 hpt
  -- `p ≠ 0`
  have hpos : 0 < ‖p‖ := by
    rw [norm_pos_iff]
    intro h0
    have hz : ∀ᵐ x, (((centralInterval a.1).indicator primePoleProfile x : ℝ) : ℂ) = 0 := by
      filter_upwards [primePoleApertureVector_coeFn a,
        (show ((p : SoninL2) : ℝ → ℂ) =ᵐ[volume] 0 by rw [h0]; exact Lp.coeFn_zero _ _ _)]
        with x h1 h2
      rw [← h1, h2]; rfl
    have hmeas : volume (centralInterval a.1) ≠ 0 := by
      rw [centralInterval, Real.volume_Icc]
      have := a.property
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      linarith
    have hae : ∀ᵐ x ∂(volume.restrict (centralInterval a.1)), False := by
      filter_upwards [ae_restrict_of_ae hz, ae_restrict_mem (measurableSet_centralInterval a.1)]
        with x hx hxI
      rw [indicator_of_mem hxI] at hx
      exact (primePoleProfile_pos x).ne' (by exact_mod_cast hx)
    have := (ae_iff.mp hae)
    simp only [not_false_eq_true, setOf_true] at this
    rw [Measure.restrict_apply_univ] at this
    exact hmeas this
  have hTp : ‖T p‖ ≤ ‖T‖ * ‖p‖ := T.le_opNorm p
  have h2 : lam * ‖p‖ ≤ ‖T p‖ :=
    (sq_le_sq₀ (mul_nonneg hlam hpos.le) (norm_nonneg _)).mp (by rw [mul_pow]; linarith [hsq])
  exact le_of_mul_le_mul_right (h2.trans hTp) hpos

theorem ccmReciprocalMangoldtCumulative_nonneg (X : ℝ) : 0 ≤ ccmReciprocalMangoldtCumulative X :=
  Finset.sum_nonneg fun _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)

/-- **Sharp asymptotic lower bound.**  By the prime number theorem, the Rayleigh quotient of the
pole vector gives `‖T_a‖ ≥ (1-ε) e^a` for all large apertures. -/
theorem exists_one_sub_le_norm_ccmFinitePrimeOperator (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ A : ℝ, ∀ a : SuzukiPositiveAperture, A ≤ a.1 →
      (1 - ε) * Real.exp a.1 ≤ ‖ccmFinitePrimeOperator a‖ := by
  have hpnt := tendsto_chebyshevPsiReal_div
  have hev : ∀ᶠ x : ℝ in Filter.atTop, 1 - ε / 2 < chebyshevPsiReal x / x :=
    hpnt (Ioi_mem_nhds (by linarith))
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp hev
  set x₀ := max x₁ 1 with hx₀
  have hx₀1 : 1 ≤ x₀ := le_max_right _ _
  set K := (1 - ε / 2) * x₀ with hK
  have hK0 : 0 ≤ K := by have : 0 ≤ 1 - ε / 2 := by linarith
                         positivity
  have hψ : ∀ X : ℝ, 1 ≤ X → (1 - ε / 2) * X - K ≤ Chebyshev.psi X := by
    intro X hX
    by_cases hXx : x₀ ≤ X
    · have h1 := hx₁ X (le_trans (le_max_left _ _) hXx)
      have hident : chebyshevPsiReal X = Chebyshev.psi X := by
        rw [chebyshevPsiReal_eq_sum_range, Chebyshev.psi_eq_sum_Icc]
        congr 1
        ext n
        simp
      rw [hident, lt_div_iff₀ (by linarith)] at h1
      nlinarith
    · have h0 := Chebyshev.psi_nonneg X
      have : X < x₀ := lt_of_not_ge hXx
      have : 0 ≤ 1 - ε / 2 := by linarith
      nlinarith
  refine ⟨2 * K / ε + 1, fun a haA => ?_⟩
  have hKa : K ≤ ε / 2 * Real.exp a.1 := by
    have h1 : 2 * K / ε ≤ a.1 := by linarith
    rw [div_le_iff₀ hε] at h1
    have h2 := Real.add_one_le_exp a.1
    nlinarith
  set lam := (1 - ε / 2) * Real.exp a.1 - K with hlam
  have hlam0 : 0 ≤ lam := by
    have := Real.exp_pos a.1
    nlinarith
  have hrow : ∀ z ∈ centralInterval a.1, lam * primePoleProfile z ≤
      Real.exp (z / 2) * (Chebyshev.psi (Real.exp (a.1 - z)) +
          ccmReciprocalMangoldtCumulative (Real.exp (a.1 + z))) +
        Real.exp (-z / 2) * (Chebyshev.psi (Real.exp (a.1 + z)) +
          ccmReciprocalMangoldtCumulative (Real.exp (a.1 - z))) := by
    intro z hz
    have hz' : -a.1 ≤ z ∧ z ≤ a.1 := hz
    have hX1 : 1 ≤ Real.exp (a.1 - z) := Real.one_le_exp (by linarith)
    have hX2 : 1 ≤ Real.exp (a.1 + z) := Real.one_le_exp (by linarith)
    have hp1 := hψ _ hX1
    have hp2 := hψ _ hX2
    have hs1 := ccmReciprocalMangoldtCumulative_nonneg (Real.exp (a.1 - z))
    have hs2 := ccmReciprocalMangoldtCumulative_nonneg (Real.exp (a.1 + z))
    have hE1 := Real.exp_pos (z / 2)
    have hE2 := Real.exp_pos (-z / 2)
    have k1 : Real.exp (z / 2) * Real.exp (a.1 - z) = Real.exp a.1 * Real.exp (-z / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    have k2 : Real.exp (-z / 2) * Real.exp (a.1 + z) = Real.exp a.1 * Real.exp (z / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    have hw : primePoleProfile z = Real.exp (z / 2) + Real.exp (-z / 2) := rfl
    rw [hw, hlam]
    have e : ((1 - ε / 2) * Real.exp a.1 - K) * (Real.exp (z / 2) + Real.exp (-z / 2)) =
        Real.exp (z / 2) * ((1 - ε / 2) * Real.exp (a.1 - z) - K) +
          Real.exp (-z / 2) * ((1 - ε / 2) * Real.exp (a.1 + z) - K) := by
      linear_combination (-(1 - ε / 2)) * k1 + (-(1 - ε / 2)) * k2
    rw [e]
    have t1 : Real.exp (z / 2) * ((1 - ε / 2) * Real.exp (a.1 - z) - K) ≤
        Real.exp (z / 2) * (Chebyshev.psi (Real.exp (a.1 - z)) +
          ccmReciprocalMangoldtCumulative (Real.exp (a.1 + z))) :=
      mul_le_mul_of_nonneg_left (by linarith) hE1.le
    have t2 : Real.exp (-z / 2) * ((1 - ε / 2) * Real.exp (a.1 + z) - K) ≤
        Real.exp (-z / 2) * (Chebyshev.psi (Real.exp (a.1 + z)) +
          ccmReciprocalMangoldtCumulative (Real.exp (a.1 - z))) :=
      mul_le_mul_of_nonneg_left (by linarith) hE2.le
    linarith
  have hmain := le_norm_ccmFinitePrimeOperator_of_poleRow_ge a lam hlam0 hrow
  nlinarith

/-- **The prime-transport horizon law.**  The literal level-`a` prime transport of the restricted
Weil form has norm `(1 + o(1)) e^a`: for every `ε ∈ (0,1)` there is `A` with
`(1-ε)e^a ≤ ‖T_a‖ ≤ (1+ε)e^a` for all apertures `a ≥ A`. -/
theorem primeTransport_horizon_law (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ A : ℝ, ∀ a : SuzukiPositiveAperture, A ≤ a.1 →
      (1 - ε) * Real.exp a.1 ≤ ‖ccmFinitePrimeOperator a‖ ∧
        ‖ccmFinitePrimeOperator a‖ ≤ (1 + ε) * Real.exp a.1 := by
  obtain ⟨A₁, h₁⟩ := exists_one_sub_le_norm_ccmFinitePrimeOperator ε hε hε1
  obtain ⟨A₂, h₂⟩ := exists_norm_ccmFinitePrimeOperator_le_one_add ε hε
  exact ⟨max A₁ A₂, fun a ha =>
    ⟨h₁ a (le_trans (le_max_left _ _) ha), h₂ a (le_trans (le_max_right _ _) ha)⟩⟩

/-- **Hodge-index horizon on the primitive sector.**  On pole-constrained form-domain vectors the
restricted Weil quadratic is at least the archimedean energy minus `(L + |2γ₀ - 1|)` times the
aperture mass, for any bound `L` on the prime transport. -/
theorem ccmRestrictedWeilSourceQuadratic_ge_of_primeBound (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (hu : IsPolarConstrained a u) (L : ℝ)
    (hT : ‖ccmFinitePrimeOperator a‖ ≤ L) :
    ‖u.1‖ ^ 2 - (L + |2 * gammaHardyPhaseRate 0 - 1|) * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a u := by
  set f := ccmArchimedeanFormToAperture a u with hf
  rw [ccmRestrictedWeilSourceQuadratic_eq_formNorm_sq_add_boundedDiagonal]
  unfold ccmRestrictedWeilBoundedDiagonal
  rw [inner_ccmRestrictedWeilBoundedRemainder, Complex.sub_re, Complex.add_re]
  have hpolar : (inner ℂ (ccmPolarOperator a f) f).re = 0 := by
    rw [inner_ccmPolarOperator, hu.1, hu.2]
    simp
  have hself : (ccmArchimedeanRemainderScalar * inner ℂ f f).re =
      (2 * gammaHardyPhaseRate 0 - 1) * ‖f‖ ^ 2 := by
    have hff : inner ℂ f f = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) f]
      norm_cast
    unfold ccmArchimedeanRemainderScalar
    rw [hff, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hprime : (inner ℂ (ccmFinitePrimeOperator a f) f).re ≤ L * ‖f‖ ^ 2 := by
    calc (inner ℂ (ccmFinitePrimeOperator a f) f).re
        ≤ ‖inner ℂ (ccmFinitePrimeOperator a f) f‖ := Complex.re_le_norm _
      _ ≤ ‖ccmFinitePrimeOperator a f‖ * ‖f‖ := by
        convert norm_inner_le_norm (𝕜 := ℂ) (ccmFinitePrimeOperator a f) f using 1
      _ ≤ ‖ccmFinitePrimeOperator a‖ * ‖f‖ * ‖f‖ :=
        mul_le_mul_of_nonneg_right ((ccmFinitePrimeOperator a).le_opNorm f) (norm_nonneg _)
      _ ≤ L * ‖f‖ ^ 2 := by nlinarith [norm_nonneg f, norm_nonneg (ccmFinitePrimeOperator a)]
  rw [hpolar, hself]
  have habs := neg_abs_le (2 * gammaHardyPhaseRate 0 - 1)
  nlinarith [sq_nonneg ‖f‖]

/-- Explicit primitive-sector horizon. -/
theorem ccmRestrictedWeilSourceQuadratic_ge_log4Horizon (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (hu : IsPolarConstrained a u) :
    ‖u.1‖ ^ 2 - (Real.log 4 * Real.exp a.1 + 4 * a.1 * Real.exp (a.1 / 2) + 2 * a.1 +
        (Real.log 4 + 4) + |2 * gammaHardyPhaseRate 0 - 1|) *
        ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a u :=
  ccmRestrictedWeilSourceQuadratic_ge_of_primeBound a u hu _ (norm_ccmFinitePrimeOperator_le_log4 a)

end RHTower
