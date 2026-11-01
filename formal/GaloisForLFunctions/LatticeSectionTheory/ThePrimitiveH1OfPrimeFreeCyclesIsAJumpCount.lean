import GaloisForLFunctions.LatticeSectionTheory.BidegreeCountsSeeNoPrimitiveClass
import GaloisForLFunctions.LatticeSectionTheory.HeckeCorrespondencesAreSimilitudesOfThePrimitiveH1
import GaloisForLFunctions.BiScaleUncertainty.AllParityWeilPoleWeightFunctionalAndChebyshevSynthesis
import GaloisForLFunctions.BiScaleUncertainty.KreinIncrementAndChordCascade
import GaloisForLFunctions.RHTower.WeilLevyOsculatingPotentialFloor

/-!
# The primitive `h¹` of a prime-free cycle is a jump count

Q1 of the programme asks for the prime-free Weil positivity to come out of a count, not out of an
estimate of a quadratic form. On a test `f` supported in `[−a, a]` with `2a < log 2` no prime
power is seen, and the primitive `h¹ = ½ W(f, f)` of the Künneth count is the sum of three terms
(`weilPair_eq_jumpCount_of_primeFree`):

    W(f, f) = Ω(0) ‖f‖² + J(f) + 2 ∫_0^c 2 cosh(x/2) A_f(x) dx,

with `A_f` the autocorrelation, `Ω(0) = −(log π + 3 log 2 + γ + π/2)` the archimedean constant, and
the **jump count**

    J(f) = ∫_0^∞ (A_f(0) − A_f(x)) e^{x/2}/sinh x dx = ½ ∫_0^∞ ∫ (f(u) − f(u + x))² du · w(x) dx ≥ 0,

the Lévy–Khintchine form of the Gamma factor: every jump of `f` across a gap `x` is counted with the
weight `w(x) = e^{x/2}/sinh x`.

* **Exterior jumps** (`jumpCount_ge`). A test supported in `[−a, a]` jumps to `0` across every gap
  `x > 2a`, so `J(f) ≥ ‖f‖² ∫_{2a}^1 (1/x − 1/2) dx = ‖f‖² (log(1/2a) − (1 − 2a)/2)`, from
  `w(x) ≥ e^{−x/2}/x ≥ 1/x − 1/2`.
* **The pole term** (`abs_poleCross_le`) is at most `4a cosh a ‖f‖²`.
* **Positivity from the count** (`jumpCount_derivation_of_primeFree_positivity`). For
  `a ≤ 1/2000` the exterior jumps alone pay the archimedean constant `|Ω(0)| < 5.373` and the pole
  term: `W(f, f) ≥ ‖f‖²/4`. The primitive `h¹` on these prime-free cycles is nonnegative because a
  count of jumps dominates it (`primitiveH1_ge_of_jumpCount`).

The window is small; on the whole prime-free window `(−½ log 2, ½ log 2)` the exterior jumps
(`≈ 3.9 ‖f‖²` at `a = ½ log 2`) no longer pay `|Ω(0)| ≈ 5.37`, and the interior jumps and the pole
term must be counted as well. That is the remaining part of Q1.
-/

noncomputable section

open Real MeasureTheory Set

namespace GaloisForLFunctions.LatticeSectionTheory

open ArithmeticCastelnuovoSeveri ArithmeticEffectivityTheory BiScaleUncertainty
open RHTower.ArchimedeanAnomaly Zeta23

/-! ### The real Weil test of a real test -/

/-- A real test as a real Weil test function. -/
def toRealWeilTestFn {f : ℝ → ℝ} (hf : f ∈ realTests) : RealWeilTestFn :=
  ⟨⟨cx f, cx_contDiff hf.1, cx_hasCompactSupport hf.2⟩, fun u => by simp [cx]⟩

theorem toRealWeilTestFn_source {f : ℝ → ℝ} (hf : f ∈ realTests) :
    (toRealWeilTestFn hf).source = f := by
  funext u; simp [RealWeilTestFn.source, toRealWeilTestFn, cx]

/-- The **jump count** of a test: the Lévy form of the Gamma factor. -/
def jumpCount (f : ℝ → ℝ) : ℝ := biScaleLevyEnergy f

/-- The **pole cross term** `∫_0^c 2 cosh(x/2) A_f(x) dx` at the cutoff `c = log(N + 2)`. -/
def poleCross (N : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∫ x in Icc 0 (SignedPrimePolar.cutoff N), SignedPrimePolar.polarDensity x * autocorr f x

/-- The autocorrelation of a test supported in `[−a, a]` vanishes beyond `2a`. -/
theorem autocorr_eq_zero_of_support {f : ℝ → ℝ} {a : ℝ} (hs : tsupport f ⊆ Icc (-a) a) {x : ℝ}
    (hx : 2 * a < x) : autocorr f x = 0 := by
  unfold autocorr
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun u => ?_)
  by_cases hu : f u = 0
  · simp [hu]
  · have hu' := hs (subset_tsupport f hu)
    have hux : f (u + x) = 0 := by
      refine image_eq_zero_of_notMem_tsupport fun h => ?_
      have := (hs h).2
      linarith [hu'.1]
    simp [hux]

theorem autocorr_zero_eq (f : ℝ → ℝ) : autocorr f 0 = ∫ u, f u ^ 2 := by
  unfold autocorr; simp [sq]

/-! ### The jump-count identity -/

/-- **The primitive `h¹` of a prime-free cycle is a jump count.** For a test supported in
`[−a, a]` with `2a < log 2`: `W(f, f) = Ω(0)‖f‖² + J(f) + 2 · poleCross`. -/
theorem weilPair_eq_jumpCount_of_primeFree {f : ℝ → ℝ} (hf : f ∈ realTests) {a : ℝ}
    (hs : tsupport f ⊆ Icc (-a) a) (ha : 2 * a < Real.log 2) :
    weilPair f f = EF.gammaBracket 0 * (∫ u, f u ^ 2) + jumpCount f +
      2 * poleCross (toRealWeilTestFn hf).supportScale f := by
  have hid := (toRealWeilTestFn hf).re_weilFullFunctional_vonMangoldt_eq_of_supportScale_le
    (le_refl (toRealWeilTestFn hf).supportScale)
  have hW : weilPair f f = (RHTower.weilFullFunctional
      (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest (toRealWeilTestFn hf).1.1 (toRealWeilTestFn hf).1.1)).re := rfl
  rw [hW, hid, ← (toRealWeilTestFn hf).autocorr_eq 0, toRealWeilTestFn_source, autocorr_zero_eq]
  -- no prime power is seen: the prime part of the signed pairing vanishes
  have hprime : ∑ n ∈ Finset.Icc 1 ((toRealWeilTestFn hf).supportScale + 2),
      SignedPrimePolar.primeWeight n * autocorr f (Real.log n) = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    rcases (Finset.mem_Icc.mp hn).1.lt_or_eq with h | h
    · have hlog : Real.log 2 ≤ Real.log n :=
        Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ n by omega))
      rw [autocorr_eq_zero_of_support hs (by linarith), mul_zero]
    · subst h
      simp [SignedPrimePolar.primeWeight]
  unfold SignedPrimePolar.pairing jumpCount poleCross
  rw [hprime]
  ring

/-! ### Exterior jumps -/

/-- The Lévy weight dominates `1/x − 1/2`: `e^{x/2}/sinh x ≥ e^{−x/2}/x ≥ 1/x − 1/2`. -/
theorem archLevySinhWeight_ge {x : ℝ} (hx : 0 < x) : 1 / x - 1 / 2 ≤ archLevySinhWeight x := by
  unfold archLevySinhWeight
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  -- `sinh x ≤ x e^x`, from `1 − e^{−2x} ≤ 2x`
  have hsinh : Real.sinh x ≤ x * Real.exp x := by
    rw [Real.sinh_eq]
    have h1 := Real.add_one_le_exp (-(2 * x))
    have h2 : Real.exp (-x) = Real.exp x * Real.exp (-(2 * x)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h2]
    nlinarith [Real.exp_pos x]
  have hlow : Real.exp (-(x / 2)) / x ≤ Real.exp (x / 2) / Real.sinh x := by
    rw [div_le_div_iff₀ hx hs]
    have : Real.exp (-(x / 2)) * (x * Real.exp x) = Real.exp (x / 2) * x := by
      rw [show x * Real.exp x = Real.exp x * x by ring, ← mul_assoc, ← Real.exp_add]
      congr 2; ring
    nlinarith [Real.exp_pos (-(x / 2))]
  have he : 1 - x / 2 ≤ Real.exp (-(x / 2)) := by
    have := Real.add_one_le_exp (-(x / 2)); linarith
  have : 1 / x - 1 / 2 = (1 - x / 2) / x := by field_simp
  rw [this]
  exact (div_le_div_of_nonneg_right he hx.le).trans hlow

/-- **Exterior jumps.** A test supported in `[−a, a]`, `0 < 2a ≤ 1`, has
`J(f) ≥ ‖f‖² (log(1/2a) − (1 − 2a)/2)`. -/
theorem jumpCount_ge {f : ℝ → ℝ} (hf : f ∈ realTests) {a : ℝ} (hs : tsupport f ⊆ Icc (-a) a)
    (ha0 : 0 < a) (ha1 : 2 * a ≤ 1) :
    (∫ u, f u ^ 2) * (Real.log (1 / (2 * a)) - (1 - 2 * a) / 2) ≤ jumpCount f := by
  set A0 := autocorr f 0
  have hA0 : A0 = ∫ u, f u ^ 2 := autocorr_zero_eq f
  have hA0nn : 0 ≤ A0 := by rw [hA0]; exact integral_nonneg fun u => sq_nonneg _
  have hint := integrableOn_biScaleLevyIntegrand hf.1 hf.2
  have hnn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ (autocorr f 0 - autocorr f x) * archLevySinhWeight x := by
    intro x hx
    have h1 := abs_autocorr_le_zero hf.2 hf.1.continuous x
    have h2 := le_abs_self (autocorr f x)
    exact mul_nonneg (by linarith) (archLevySinhWeight_pos hx).le
  have hsub : Ioc (2 * a) 1 ⊆ Ioi (0 : ℝ) := fun x hx => Set.mem_Ioi.mpr (by linarith [hx.1])
  have h1 : ∫ x in Ioc (2 * a) 1, (autocorr f 0 - autocorr f x) * archLevySinhWeight x ≤
      jumpCount f :=
    setIntegral_mono_set hint ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall hnn)) (Filter.Eventually.of_forall hsub)
  have hcont : ContinuousOn (fun x : ℝ => A0 * (1 / x - 1 / 2)) (Icc (2 * a) 1) :=
    continuousOn_const.mul ((continuousOn_const.div continuousOn_id fun x hx =>
      (show (0 : ℝ) < x by linarith [hx.1]).ne').sub continuousOn_const)
  have h2 : ∫ x in Ioc (2 * a) 1, A0 * (1 / x - 1 / 2) ≤
      ∫ x in Ioc (2 * a) 1, (autocorr f 0 - autocorr f x) * archLevySinhWeight x := by
    refine setIntegral_mono_on (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (hint.mono_set hsub) measurableSet_Ioc fun x hx => ?_
    rw [autocorr_eq_zero_of_support hs hx.1, sub_zero]
    exact mul_le_mul_of_nonneg_left (archLevySinhWeight_ge (by linarith [hx.1])) hA0nn
  have hinv : IntervalIntegrable (fun x : ℝ => x⁻¹) volume (2 * a) 1 :=
    intervalIntegral.intervalIntegrable_inv (fun x hx => (show (0 : ℝ) < x by
      rcases Set.mem_uIcc.mp hx with h | h <;> linarith [h.1, h.2]).ne') continuousOn_id
  have h3 : ∫ x in Ioc (2 * a) 1, A0 * (1 / x - 1 / 2) =
      A0 * (Real.log (1 / (2 * a)) - (1 - 2 * a) / 2) := by
    rw [← intervalIntegral.integral_of_le ha1, intervalIntegral.integral_const_mul]
    simp only [one_div]
    rw [intervalIntegral.integral_sub hinv intervalIntegrable_const,
      integral_inv_of_pos (by linarith) one_pos, intervalIntegral.integral_const, smul_eq_mul]
    simp only [one_div]
    ring
  rw [← hA0]
  linarith

/-! ### The pole term -/

theorem abs_poleCross_le {f : ℝ → ℝ} (hf : f ∈ realTests) {a : ℝ} (hs : tsupport f ⊆ Icc (-a) a)
    (ha0 : 0 ≤ a) (ha : 2 * a < Real.log 2) (N : ℕ) :
    |poleCross N f| ≤ 2 * Real.cosh a * (∫ u, f u ^ 2) * (2 * a) := by
  have hc : 2 * a ≤ SignedPrimePolar.cutoff N := by
    unfold SignedPrimePolar.cutoff
    have : Real.log 2 ≤ Real.log ((N + 2 : ℕ) : ℝ) :=
      Real.log_le_log (by norm_num) (by push_cast; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
    linarith
  set g := fun x : ℝ => SignedPrimePolar.polarDensity x * autocorr f x
  have hA0 := autocorr_zero_eq f
  -- beyond `2a` the integrand vanishes
  have hgc : Continuous g := SignedPrimePolar.continuous_polarDensity.mul
    (RHTower.ArchimedeanExactForm.continuous_autocorr hf.1 hf.2)
  have hsplit : poleCross N f = ∫ x in Icc 0 (2 * a), g x := by
    unfold poleCross
    rw [← Icc_union_Ioc_eq_Icc (by linarith) hc, setIntegral_union
      (Set.disjoint_left.mpr fun x h1 h2 => by linarith [h1.2, h2.1]) measurableSet_Ioc
      hgc.integrableOn_Icc (hgc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)]
    have hz : ∫ x in Ioc (2 * a) (SignedPrimePolar.cutoff N), g x = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun x hx => by
        show SignedPrimePolar.polarDensity x * autocorr f x = 0
        rw [autocorr_eq_zero_of_support hs hx.1, mul_zero]
    rw [hz, add_zero]
  rw [hsplit]
  have hbound : ∀ x ∈ Icc (0 : ℝ) (2 * a), ‖g x‖ ≤ 2 * Real.cosh a * ∫ u, f u ^ 2 := by
    intro x hx
    rw [Real.norm_eq_abs, abs_mul, ← hA0]
    have h1 : |SignedPrimePolar.polarDensity x| ≤ 2 * Real.cosh a := by
      rw [abs_of_nonneg (SignedPrimePolar.polarDensity_nonneg x), SignedPrimePolar.polarDensity]
      have : |x / 2| ≤ |a| := by
        rw [abs_of_nonneg (by linarith [hx.1]), abs_of_nonneg ha0]; linarith [hx.2]
      have := Real.cosh_le_cosh.mpr this
      linarith
    exact mul_le_mul h1 (abs_autocorr_le_zero hf.2 hf.1.continuous x) (abs_nonneg _)
      (by positivity)
  have := norm_setIntegral_le_of_norm_le_const (s := Icc (0 : ℝ) (2 * a))
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top) hbound
  rw [Real.norm_eq_abs, Real.volume_real_Icc_of_le (by linarith)] at this
  linarith

/-! ### Positivity from the count -/

/-- **Prime-free positivity from the jump count.** For a test supported in `[−a, a]`,
`0 < a ≤ 1/2000`: `W(f, f) ≥ ‖f‖²/4`. The exterior jumps pay the archimedean constant and the
pole term; no estimate of the Weil form is used. -/
theorem jumpCount_derivation_of_primeFree_positivity {f : ℝ → ℝ} (hf : f ∈ realTests) {a : ℝ}
    (hs : tsupport f ⊆ Icc (-a) a) (ha0 : 0 < a) (ha : a ≤ 1 / 2000) :
    (∫ u, f u ^ 2) / 4 ≤ weilPair f f := by
  have hlog2 : 2 * a < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hid := weilPair_eq_jumpCount_of_primeFree hf hs hlog2
  have hJ := jumpCount_ge hf hs ha0 (by linarith)
  have hP := abs_poleCross_le hf hs ha0.le hlog2 (toRealWeilTestFn hf).supportScale
  have hΩ := RHTower.WeilLevyOsculatingFloor.neg_gammaBracket_zero_lt_5373_over_1000
  set M := ∫ u, f u ^ 2
  have hM : 0 ≤ M := integral_nonneg fun u => sq_nonneg _
  -- `log(1/2a) ≥ log 512 = 9 log 2 > 6.2`
  have hlog : 62 / 10 ≤ Real.log (1 / (2 * a)) := by
    have h1 : (512 : ℝ) ≤ 1 / (2 * a) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith
    have h2 : Real.log 512 = 9 * Real.log 2 := by
      rw [show (512 : ℝ) = 2 ^ 9 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_log (by norm_num) h1
    linarith [Real.log_two_gt_d9]
  have hcosh : Real.cosh a ≤ 2 := by
    have := Real.cosh_le_cosh.mpr (show |a| ≤ |1| by
      rw [abs_of_pos ha0, abs_one]; linarith)
    have hc1 : Real.cosh 1 ≤ 2 := by
      rw [Real.cosh_eq]
      have := Real.exp_one_lt_d9
      have : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
      linarith
    linarith
  have hpole : -(16 * a * M) ≤ 2 * poleCross (toRealWeilTestFn hf).supportScale f := by
    have h := (abs_le.mp hP).1
    have : 2 * Real.cosh a * M * (2 * a) ≤ 8 * a * M := by
      have := mul_le_mul_of_nonneg_right hcosh (show 0 ≤ M * a by positivity)
      nlinarith
    linarith
  have hJ' : M * (62 / 10 - 1 / 2) ≤ jumpCount f := by
    have : M * (62 / 10 - 1 / 2) ≤ M * (Real.log (1 / (2 * a)) - (1 - 2 * a) / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hM
    linarith
  have h16a : 16 * a * M ≤ M / 100 := by nlinarith
  rw [hid]
  nlinarith

/-- **The primitive `h¹` of a prime-free cycle is controlled by its jump count**: on the scaling
subsurface of tests supported in `[−a, a]`, `0 < a ≤ 1/2000`, `h¹_prim(x) ≥ ‖f‖²/8`. -/
theorem primitiveH1_ge_of_jumpCount {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2000)
    (x : ℝ × ℝ × realTestsAt a) :
    (∫ u, (x.2.2.1.1 u) ^ 2) / 8 ≤ primitiveH1 (scalingSubsurface (realTestsAt a)) x := by
  rw [primitiveH1_eq, scalingSubsurface_defect_self]
  have h := jumpCount_derivation_of_primeFree_positivity x.2.2.1.2 x.2.2.2 ha0 ha
  linarith

end GaloisForLFunctions.LatticeSectionTheory
