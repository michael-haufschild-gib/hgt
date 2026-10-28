import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheHodgeIndexHoldsAtAFixedFractionOfTheSpacing
import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheAtomicMetzlerPropertyIsSelective
import Mathlib.NumberTheory.ArithmeticFunction.Liouville

/-!
# Hyperbolicity is blind, the sign is not

A twin of `ζ` replaces the prime place by `Σ_k ω(k)Λ_k`, keeping the archimedean place and the pole.
For a completely multiplicative sign twin `ω` the twin's atomic intersection Gram
(`twinAtomicIntersectionGram`) has the same pole plane and pole row as `ζ`'s, and the twin's
Markov form obeys the same stability law at the spacing scale (SpacingScaleHarmonicAnalysis).

* **The twin's polar defect is the twin's Weil form** (`polarDefect_twin`): the twisted Markov
  pairing is symmetric and bilinear on compactly supported `C²` tests (`twinMarkovPair_sum_right`),
  so the polar defect of the twin's Gram is `M_ω(f) + 2AB`, with `M_ω(f) = archForm f − Σ_k ω(k)…`.
* **Hyperbolicity is blind** (`twinAtomicIntersectionGram_isHyperbolic`): at every width
  `w ≤ c★δ_N` every completely multiplicative sign twin has an atomic intersection Gram with one
  positive square — the tilted margin of the stability law pays the pole for all of them alike.
* **The sign is not** (`liouville_isHyperbolic_and_not_metzler`): for the Liouville twin
  `λ(n) = (−1)^{Ω(n)}`, whose Dirichlet series `ζ(2s)/ζ(s)` has a pole on the critical line, the
  Gram is hyperbolic at the same widths, yet for `N ≥ 2` admits no unimodular gauge with
  nonnegative off-diagonal entries; `ζ`'s Gram is Metzler there.

So at the scales where the Hodge index of the atomic family is a theorem, it carries no
arithmetic: it holds at the Liouville point. The Lorentzian sign hypothesis is the part of the
structure that sees the Euler point.
-/

noncomputable section

open MeasureTheory Set Finset Matrix RHTower Complex
open scoped Real ComplexConjugate ComplexOrder

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics

variable {g : ℝ → ℝ} {w : ℝ}

/-! ### Bilinearity of the twisted pairing -/

theorem twinPrimePair_comm (ω : ℕ → ℝ) (f d : ℝ → ℝ) :
    twinPrimePair ω f d = twinPrimePair ω d f := by
  unfold twinPrimePair
  refine tsum_congr fun k => ?_
  congr 1
  have e1 : ∫ t, f t * d (t - Real.log k) = ∫ t, d t * f (t + Real.log k) := by
    rw [← integral_add_right_eq_self (fun t => f t * d (t - Real.log k)) (Real.log k)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by
      simp only [add_sub_cancel_right]; ring)
  have e2 : ∫ t, f t * d (t + Real.log k) = ∫ t, d t * f (t - Real.log k) := by
    rw [← integral_sub_right_eq_self (fun t => f t * d (t + Real.log k)) (Real.log k)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by
      simp only [sub_add_cancel]; ring)
  rw [e1, e2, add_comm]

/-- On tests supported in `[−R, R]` the twisted prime pairing is a finite sum. -/
theorem twinPrimePair_eq_sum_of_supportedIn (ω : ℕ → ℝ) {R : ℝ} {f d : ℝ → ℝ}
    (hf : SupportedIn R f) (hd : SupportedIn R d) :
    twinPrimePair ω f d = ∑ k ∈ Finset.range (lagRange R), ω k * vonMangoldtAtom k *
      ((∫ t, f t * d (t - Real.log k)) + ∫ t, f t * d (t + Real.log k)) := by
  rw [twinPrimePair]
  refine tsum_eq_sum fun k hk => ?_
  have hk' : lagRange R ≤ k := by simpa using hk
  have hl := two_mul_lt_abs_log_of_lagRange_le hk'
  have e1 : ∀ t, f t * d (t - Real.log k) = 0 := fun t => by
    rw [sub_eq_add_neg]
    exact mul_shift_eq_zero_of_supportedIn hf hd (by rwa [abs_neg]) t
  have e2 : ∀ t, f t * d (t + Real.log k) = 0 := fun t => mul_shift_eq_zero_of_supportedIn hf hd hl t
  simp [e1, e2]

/-- **Linearity of the twisted prime pairing** in its second argument over finite sums. -/
theorem twinPrimePair_sum_right (ω : ℕ → ℝ) {ι : Type*} (s : Finset ι) {R : ℝ} {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfR : SupportedIn R f) {d : ι → ℝ → ℝ}
    (hd : ∀ i, Continuous (d i)) (hdR : ∀ i, SupportedIn R (d i)) (x : ι → ℝ) :
    twinPrimePair ω f (fun u => ∑ i ∈ s, x i * d i u) = ∑ i ∈ s, x i * twinPrimePair ω f (d i) := by
  rw [twinPrimePair_eq_sum_of_supportedIn ω hfR (supportedIn_sum s hdR x)]
  simp_rw [twinPrimePair_eq_sum_of_supportedIn ω hfR (hdR _)]
  have e : ∀ c : ℝ, ∫ t, f t * ∑ i ∈ s, x i * d i (t + c) =
      ∑ i ∈ s, x i * ∫ t, f t * d i (t + c) := fun c => by
    simp_rw [mul_sum]
    rw [integral_finsetSum _ fun i _ => by
      simpa [mul_left_comm] using (integrable_mul_shift hf hfc (hd i) c).const_mul (x i)]
    refine sum_congr rfl fun i _ => ?_
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => by ring)
  simp_rw [sub_eq_add_neg, e, mul_sum, ← sum_add_distrib, mul_sum]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun k _ => by ring

theorem primePair_eq_twinPrimePair_one (f d : ℝ → ℝ) :
    primePair f d = twinPrimePair (fun _ => 1) f d := by
  simp [primePair, twinPrimePair]

theorem twinMarkovPair_eq (ω : ℕ → ℝ) (f d : ℝ → ℝ) :
    twinMarkovPair ω f d = markovPair f d + twinPrimePair (fun _ => 1) f d - twinPrimePair ω f d := by
  unfold twinMarkovPair markovPair
  rw [primePair_eq_twinPrimePair_one]
  ring

theorem twinMarkovPair_comm (ω : ℕ → ℝ) (f d : ℝ → ℝ) :
    twinMarkovPair ω f d = twinMarkovPair ω d f := by
  rw [twinMarkovPair_eq, twinMarkovPair_eq, markovPair_comm, twinPrimePair_comm ω f d,
    twinPrimePair_comm (fun _ => (1 : ℝ)) f d]

/-- **Linearity of the twisted Markov pairing** over finite sums of `C²` tests in `[−R, R]`. -/
theorem twinMarkovPair_sum_right (ω : ℕ → ℝ) {ι : Type*} (s : Finset ι) {R : ℝ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hfR : SupportedIn R f) {d : ι → ℝ → ℝ}
    (hd : ∀ i, ContDiff ℝ 2 (d i)) (hdc : ∀ i, HasCompactSupport (d i))
    (hdR : ∀ i, SupportedIn R (d i)) (x : ι → ℝ) :
    twinMarkovPair ω f (fun u => ∑ i ∈ s, x i * d i u) =
      ∑ i ∈ s, x i * twinMarkovPair ω f (d i) := by
  simp_rw [twinMarkovPair_eq]
  rw [markovPair_sum_right s hf hfc hfR hd hdc hdR x,
    twinPrimePair_sum_right _ s hf.continuous hfc hfR (fun i => (hd i).continuous) hdR x,
    twinPrimePair_sum_right ω s hf.continuous hfc hfR (fun i => (hd i).continuous) hdR x,
    ← sum_add_distrib, ← sum_sub_distrib]
  exact sum_congr rfl fun i _ => by ring

/-- The twisted Markov form of a finite combination is the quadratic form of its Gram. -/
theorem twinMarkovPair_sum_eq (ω : ℕ → ℝ) {ι : Type*} (s : Finset ι) {R : ℝ} {e : ι → ℝ → ℝ}
    (he : ∀ i, ContDiff ℝ 2 (e i)) (hec : ∀ i, HasCompactSupport (e i))
    (heR : ∀ i, SupportedIn R (e i)) (x : ι → ℝ) :
    twinMarkovPair ω (fun u => ∑ i ∈ s, x i * e i u) (fun u => ∑ i ∈ s, x i * e i u) =
      ∑ i ∈ s, ∑ j ∈ s, x i * x j * twinMarkovPair ω (e i) (e j) := by
  have hF : ContDiff ℝ 2 fun u => ∑ i ∈ s, x i * e i u :=
    ContDiff.sum fun i _ => contDiff_const.mul (he i)
  have hFc : HasCompactSupport fun u => ∑ i ∈ s, x i * e i u :=
    HasCompactSupport.intro (K := Set.Icc (-R) R) isCompact_Icc fun u hu =>
      supportedIn_sum s heR x u (by
        by_contra h; push Not at h; exact hu (abs_le.mp h))
  rw [twinMarkovPair_sum_right ω s hF hFc (supportedIn_sum s heR x) he hec heR]
  refine sum_congr rfl fun i _ => ?_
  rw [twinMarkovPair_comm, twinMarkovPair_sum_right ω s (he i) (hec i) (heR i) he hec heR, mul_sum]
  exact sum_congr rfl fun j _ => by rw [twinMarkovPair_comm]; ring

/-- The twin's Markov form: `M_ω(f) = archForm f − Σ_k ω(k) Λ_k (…)`. -/
theorem twinMarkovPair_self (ω : ArithmeticFunction ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    twinMarkovPair ω f f = archForm f - twistedPrimeSum ω f := by
  have h1 : markovPair f f = archForm f - primeSum f := by
    rw [markovPair_self, levyMarkovForm, archForm_eq_levyEnergy hf hfc]
  have h2 : twinPrimePair (fun _ => 1) f f = primeSum f := by
    rw [← primePair_eq_twinPrimePair_one]
    unfold primePair primeSum
    rfl
  rw [twinMarkovPair_eq, h1, h2]
  unfold twinPrimePair twistedPrimeSum
  ring

/-! ### The twin's polar defect -/

theorem twinMarkovGram_isSymm (ω : ℕ → ℝ) (g : ℝ → ℝ) (N : ℕ) : (twinMarkovGram ω g N).IsSymm :=
  Matrix.IsSymm.ext fun i j => by simp only [twinMarkovGram, Matrix.of_apply, twinMarkovPair_comm]

/-- **The polar defect of the twin's Gram is the twin's Weil form**: `M_ω(f) + 2AB`. -/
theorem polarDefect_twin (ω : ℕ → ℝ) (hg : ContDiff ℝ 2 g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw0 : 0 ≤ w) (N : ℕ) (d : Fin N → ℝ) :
    polarDefect (atomPoleRow g N) (-twinMarkovGram ω g N) d =
      twinMarkovPair ω (finAtomicTest g N d) (finAtomicTest g N d) +
        2 * (∫ u, finAtomicTest g N d u * Real.exp (-(u / 2))) *
          ∫ u, finAtomicTest g N d u * Real.exp (u / 2) := by
  set f := finAtomicTest g N d
  have hB0 : (atomPoleRow g N *ᵥ d) 0 = ∫ u, f u * Real.exp (-(u / 2)) := by
    rw [integral_finAtomicTest_mul (φ := fun u => Real.exp (-(u / 2))) (by fun_prop)
      hg.continuous hgsupp]
    simp only [mulVec, dotProduct, atomPoleRow, Matrix.of_apply, if_true]
    exact sum_congr rfl fun j _ => mul_comm _ _
  have hB1 : (atomPoleRow g N *ᵥ d) 1 = ∫ u, f u * Real.exp (u / 2) := by
    rw [integral_finAtomicTest_mul (φ := fun u => Real.exp (u / 2)) (by fun_prop)
      hg.continuous hgsupp]
    simp only [mulVec, dotProduct, atomPoleRow, Matrix.of_apply, one_ne_zero, if_false]
    exact sum_congr rfl fun j _ => mul_comm _ _
  have hM : qf (-twinMarkovGram ω g N) d = -twinMarkovPair ω f f := by
    rw [show f = fun u => ∑ j, d j * atom g ((j : ℕ) + 1) u from rfl,
      twinMarkovPair_sum_eq ω _ (fun j => contDiff_atom hg _)
        (fun j => hasCompactSupport_atom hgsupp _)
        (fun j => supportedIn_atom hgsupp hw0 (mem_Icc_succ j)), qf_eq_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun j _ => ?_
    simp only [Matrix.neg_apply, twinMarkovGram, Matrix.of_apply]
    ring
  rw [polarDefect, hB0, hB1, hM]
  ring

/-! ### Hyperbolicity is blind -/

/-- **Hyperbolicity is blind.** At every width `0 < w ≤ c★δ_N`, the atomic intersection Gram of
every completely multiplicative sign twin has one positive square. -/
theorem twinAtomicIntersectionGram_isHyperbolic {ω : ArithmeticFunction ℝ}
    (hω : ∀ a b, ω (a * b) = ω a * ω b) (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w) (hw : w ≤ fixedWidthRatio * atomSpacing N) :
    IsHyperbolic (twinAtomicIntersectionGram ω g N) := by
  have hL : (-twinMarkovGram ω g N).IsSymm := by
    unfold Matrix.IsSymm; rw [transpose_neg, (twinMarkovGram_isSymm ω g N).eq]
  rw [twinAtomicIntersectionGram, isHyperbolic_fromBlocks_iff _ hL]
  intro d
  rw [polarDefect_twin ω hg hgsupp hw0.le N d, finAtomicTest_eq_atomicTest,
    twinMarkovPair_self ω (contDiff_atomicTest hg N _) (hasCompactSupport_atomicTest hgsupp N _)]
  exact twin_markov_add_pole_nonneg hω hsign hg hgc hgsupp hN hw0 hw _

/-! ### The sign is not -/

/-- The Liouville twin `λ(n) = (−1)^{Ω(n)}`. -/
def liouvilleTwin : ArithmeticFunction ℝ :=
  ⟨fun n => (ArithmeticFunction.liouville n : ℝ), by simp⟩

theorem liouvilleTwin_apply (n : ℕ) :
    liouvilleTwin n = (ArithmeticFunction.liouville n : ℝ) := rfl

theorem liouvilleTwin_mul (a b : ℕ) : liouvilleTwin (a * b) = liouvilleTwin a * liouvilleTwin b := by
  simp only [liouvilleTwin_apply, ArithmeticFunction.liouville_apply_mul, Int.cast_mul]

theorem liouvilleTwin_sign (n : ℕ) (hn : 0 < n) : liouvilleTwin n = 1 ∨ liouvilleTwin n = -1 := by
  rw [liouvilleTwin_apply, ArithmeticFunction.liouville_apply hn.ne']
  rcases neg_one_pow_eq_or ℤ (ArithmeticFunction.cardFactors n) with h | h <;> rw [h] <;> simp

theorem liouvilleTwin_two : liouvilleTwin 2 = -1 := by
  rw [liouvilleTwin_apply, ArithmeticFunction.liouville_apply two_ne_zero,
    ArithmeticFunction.cardFactors_apply_prime Nat.prime_two]
  simp

theorem archLevyDensity_half_le_two : archLevyDensity (1 / 2) ≤ 2 := by
  unfold archLevyDensity
  have h1 : Real.exp (-(1 / 2) / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have h2 : Real.exp (-2 * (1 / 2)) ≤ 1 / 2 := by
    rw [show -2 * (1 / 2 : ℝ) = -1 by norm_num, Real.exp_neg, inv_le_comm₀ (Real.exp_pos _)
      (by norm_num)]
    linarith [Real.add_one_le_exp (1 : ℝ)]
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- **Hyperbolicity is blind, the sign is not.** For a nonnegative nonzero `C²` bump and
`0 < w ≤ c★δ_N`, `N ≥ 2`: the Liouville twin's atomic intersection Gram has one positive
square, like `ζ`'s, yet admits no unimodular gauge with nonnegative off-diagonal entries, while
`ζ`'s Gram is Metzler. -/
theorem liouville_isHyperbolic_and_not_metzler (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hg0 : ∀ u, 0 ≤ g u) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {u₀ : ℝ} (hu₀ : 0 < g u₀)
    {N : ℕ} (hN : 2 ≤ N) (hw0 : 0 < w) (hw : w ≤ fixedWidthRatio * atomSpacing N) :
    IsHyperbolic (twinAtomicIntersectionGram liouvilleTwin g N) ∧
      IsHyperbolic (atomicIntersectionGram g N) ∧ IsMetzler (atomicIntersectionGram g N) ∧
      ¬ ∃ γ : Fin 2 ⊕ Fin N → ℂ, (∀ i, ‖γ i‖ = 1) ∧ ∀ i j, i ≠ j →
        0 ≤ conj (γ i) * γ j * ((twinAtomicIntersectionGram liouvilleTwin g N i j : ℝ) : ℂ) := by
  obtain ⟨-, hw2, -⟩ := one_add_le_atomMargin (by omega : 1 ≤ N) hw0 hw
  have hwδ : w < atomSpacing N := by linarith [atomSpacing_pos (N := N) (by omega)]
  refine ⟨twinAtomicIntersectionGram_isHyperbolic liouvilleTwin_mul liouvilleTwin_sign hg hgc hgsupp
    (by omega) hw0 hw, atomicIntersectionGram_isHyperbolic hg hgc hgsupp (by omega) hw0 hw,
    atomicIntersectionGram_isMetzler hg0 hgsupp hwδ, ?_⟩
  -- the window condition at `p = 2`: `2w ω(log 2 − w) < log 2/√2`
  have hδ1 : atomSpacing N ≤ 1 / 2 := by
    have h := atomSpacing_le_inv (N := N) (by omega)
    have : (1 : ℝ) / N ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hN)
    linarith
  have hw100 : w ≤ 1 / 100 := by
    have hc := fixedWidthRatio_le
    have hR : spacingRatio ≤ 1 / 32 := by
      unfold spacingRatio
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [Real.one_le_exp (show (0 : ℝ) ≤ 5 / 2 by norm_num)]
    have := fixedWidthRatio_pos
    have := atomSpacing_pos (N := N) (by omega)
    nlinarith
  have hl2 := Real.log_two_gt_d9
  have hdens : archLevyDensity (Real.log 2 - w) ≤ 2 :=
    (archLevyDensity_antitone (by norm_num) (by linarith)).trans archLevyDensity_half_le_two
  have hatom : vonMangoldtAtom 2 = Real.log 2 / Real.sqrt 2 := by
    unfold vonMangoldtAtom
    rw [if_pos le_rfl, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    push_cast; rfl
  have hwin : 2 * w * archLevyDensity (Real.log ((2 : ℕ) : ℝ) - w) < vonMangoldtAtom 2 := by
    rw [hatom]
    have hs2 : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have : Real.log 2 / 2 ≤ Real.log 2 / Real.sqrt 2 :=
      div_le_div_of_nonneg_left (by linarith) (by positivity) hs2
    push_cast
    nlinarith [archLevyDensity_pos (show 0 < Real.log 2 - w by linarith)]
  exact not_exists_nonneg_gauge_twinAtomicIntersectionGram liouvilleTwin hg hgc hg0 hgsupp hu₀
    hw0.le Nat.prime_two hN hwδ liouvilleTwin_two hwin

end GaloisForLFunctions.ArithmeticLorentzianGeometry
