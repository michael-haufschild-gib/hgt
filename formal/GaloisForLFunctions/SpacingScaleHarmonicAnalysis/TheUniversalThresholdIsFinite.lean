import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheGaugeBecomesVisibleAtTheCriticalExponent
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheSpacingScaleLawIsUniversal
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheMarkovFormFailsInsideTheSeparatedRegime
import GaloisForLFunctions.RHTower.WeilMarkovArchimedeanWideTestNegativity

/-!
# The universal threshold is finite

The **universal threshold** `K_univ` is the largest overlap ratio at which
`Re W_ω + 2S² ≥ 0` holds for every real twist `|ω| ≤ 1` on every atomic family, uniformly in `N`.
It is at least `c₀`: at width `≤ c₀ δ_N` every twist satisfies the stability law
(`TheSpacingScaleLawIsUniversal`). This file shows that it is finite.

* **Weil's form of a twist in Markov form** (`weilQuadTw_eq_markov`):
  `Re W_ω(f) = archForm f − twistedPrimeSum ω f + 2C(f)² − 2S(f)²`, so
  `Re W_ω + 2S² = M_ω + 2C²`.
* **Wide tests have negative archimedean form** (`archForm_le_of_wide`): for an `L`-Lipschitz test
  supported in an interval of length `D`, `levyEnergy f ≤ 36 D L² + 4 A(D) ‖f‖²` with the Lévy tail
  `A(D) = ∫_D^∞ ω → 0`, while `2θ′(0) < −5`.
* **The dipole** (`universalThreshold_finite`): two wide bumps at `log 1` and `log 2`,
  `f = g − t g(· − log 2)`, with `t = C(g)/C(g(· − log 2)) ≤ 1/cosh(log 2 / 2)` killing the cosh
  moment. Against the sign twist `ω(k) = sign` of the `k`-th lag correlation the twisted prime sum is
  `Σ Λ_k |pairing_k| ≥ 0`, so `Re W_ω + 2S² = M_ω ≤ archForm f < 0` once the bumps are wide.

So `c₀ ≤ K_univ < ∞` (`universalThreshold_bracket`): the failing family has `N = 2` and overlap
ratio `W/log(3/2)`. The extremal twist is the sign of the lag correlations, as on every
`|·|`-closed family the twists dominate `ζ`; the threshold is decided on signed families.
-/

noncomputable section

open MeasureTheory Finset Filter Topology RHTower Zeta23
open scoped Real

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open ArithmeticElectrostatics

/-! ### Weil's form of a twist in Markov form -/

theorem twistCoeff_mul_vonMangoldt (ω : ArithmeticFunction ℝ) (n : ℕ) :
    twistCoeff (fun n => ω n * ArithmeticFunction.vonMangoldt n) n = ω n * vonMangoldtAtom n := by
  unfold twistCoeff vonMangoldtAtom
  split_ifs <;> ring

variable {f : ℝ → ℝ} {R : ℝ}

theorem primeSum_eq_sum_pairing (hfR : SupportedIn R f) :
    primeSum f = ∑ n ∈ Finset.range (lagRange R), vonMangoldtAtom n * pairing f n := by
  unfold primeSum
  exact tsum_eq_sum fun n hn => by rw [show (∫ t, f t * f (t - Real.log n)) +
    ∫ t, f t * f (t + Real.log n) = pairing f n from rfl, pairing_eq_zero hfR hn, mul_zero]

theorem twistedPrimeSum_eq_sum_pairing (ω : ArithmeticFunction ℝ) (hfR : SupportedIn R f) :
    twistedPrimeSum ω f =
      ∑ n ∈ Finset.range (lagRange R), ω n * vonMangoldtAtom n * pairing f n := by
  unfold twistedPrimeSum
  exact tsum_eq_sum fun n hn => by rw [show (∫ t, f t * f (t - Real.log n)) +
    ∫ t, f t * f (t + Real.log n) = pairing f n from rfl, pairing_eq_zero hfR hn, mul_zero]

/-- **Weil's form of a twist in Markov form**:
`Re W_ω(f) = archForm f − twistedPrimeSum ω f + 2C(f)² − 2S(f)²`. -/
theorem weilQuadTw_eq_markov (ω : ArithmeticFunction ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hfR : SupportedIn R f) :
    weilQuadTw (fun n => ω n * ArithmeticFunction.vonMangoldt n) f =
      archForm f - twistedPrimeSum ω f +
        (2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2) := by
  rw [weilQuadTw_eq _ hfR, weilQuad_eq hf hfc, archForm_eq_levyEnergy hf hfc,
    primeSum_eq_sum_pairing hfR, twistedPrimeSum_eq_sum_pairing ω hfR]
  simp_rw [twistCoeff_mul_vonMangoldt]
  have : ∑ n ∈ Finset.range (lagRange R), (vonMangoldtAtom n - ω n * vonMangoldtAtom n) *
      pairing f n = ∑ n ∈ Finset.range (lagRange R), vonMangoldtAtom n * pairing f n -
        ∑ n ∈ Finset.range (lagRange R), ω n * vonMangoldtAtom n * pairing f n := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [this]
  ring

/-! ### Wide tests -/

/-- An `L`-Lipschitz test supported in `[a, b]` moves by `L y` on a support of length `b − a + y`. -/
theorem integral_sub_shift_sq_le_of_supp (hf : Continuous f) (hfc : HasCompactSupport f) {L a b : ℝ}
    (hL : ∀ u v, |f u - f v| ≤ L * |u - v|) (hsupp : ∀ u, u ∉ Set.Icc a b → f u = 0) (hab : a ≤ b)
    {y : ℝ} (hy : 0 ≤ y) : ∫ u, (f u - f (u + y)) ^ 2 ≤ L ^ 2 * y ^ 2 * (b - a + y) := by
  have hzero : ∀ u, u ∉ Set.Icc (a - y) b → (f u - f (u + y)) ^ 2 = 0 := fun u hu => by
    simp only [Set.mem_Icc, not_and_or, not_le] at hu
    rcases hu with hu | hu
    · rw [hsupp u fun h => by linarith [h.1], hsupp (u + y) fun h => by linarith [h.1]]; ring
    · rw [hsupp u fun h => by linarith [h.2], hsupp (u + y) fun h => by linarith [h.2]]; ring
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hint : IntegrableOn (fun u => (f u - f (u + y)) ^ 2) (Set.Icc (a - y) b) :=
    ((hf.sub (hf.comp (continuous_add_const y))).pow 2).integrableOn_Icc
  have hc : IntegrableOn (fun _ : ℝ => L ^ 2 * y ^ 2) (Set.Icc (a - y) b) :=
    continuous_const.integrableOn_Icc
  refine (setIntegral_mono_on hint hc measurableSet_Icc fun u _ => ?_).trans (le_of_eq ?_)
  · have h := hL u (u + y)
    rw [show u - (u + y) = -y by ring, abs_neg, abs_of_nonneg hy] at h
    have h0 : 0 ≤ L * y := (abs_nonneg _).trans h
    calc (f u - f (u + y)) ^ 2 = |f u - f (u + y)| ^ 2 := (sq_abs _).symm
      _ ≤ (L * y) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = L ^ 2 * y ^ 2 := by ring
  · rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
    ring

/-- **The Lévy energy of a wide test**: for an `L`-Lipschitz test supported in `[0, D]`,
`levyEnergy f ≤ 36 D L² + 4 A(D) ‖f‖²`, `A(D) = ∫_D^∞ ω`. -/
theorem levyEnergy_le_of_wide (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {L D : ℝ}
    (hL : ∀ u v, |f u - f v| ≤ L * |u - v|) (hsupp : ∀ u, u ∉ Set.Icc 0 D → f u = 0)
    (hD : 0 < D) :
    levyEnergy f ≤ 36 * D * L ^ 2 +
      4 * WeilLevyPoleGauss.archLevyAntideriv D * ∫ u, f u ^ 2 := by
  set Q : ℝ → ℝ := fun y => ∫ u, (f u - f (u + y)) ^ 2
  set M := ∫ u, f u ^ 2
  have hM : 0 ≤ M := integral_nonneg fun u => sq_nonneg _
  have hI := integrableOn_levyIntegrand hf hfc
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 D ∪ Set.Ioi D := (Set.Ioc_union_Ioi_eq_Ioi hD.le).symm
  unfold levyEnergy
  rw [hsplit, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hI.mono_set fun y hy => hy.1) (hI.mono_set fun y hy => lt_trans hD hy)]
  -- near: `Q(y) ≤ 2D L² y²`
  have hnear : ∫ y in Set.Ioc 0 D, archLevyDensity y * Q y ≤ 2 * D * L ^ 2 * levySecondMoment := by
    have hm2 : IntegrableOn (fun y : ℝ => y ^ 2 * archLevyDensity y) (Set.Ioc 0 D) :=
      integrableOn_sq_mul_archLevyDensity.mono_set fun y hy => hy.1
    have h1 := setIntegral_mono_on (hI.mono_set fun y hy => hy.1) (hm2.const_mul (2 * D * L ^ 2))
      measurableSet_Ioc fun y hy => by
        have hQ := integral_sub_shift_sq_le_of_supp hf.continuous hfc hL hsupp hD.le hy.1.le
        have hω := (archLevyDensity_pos hy.1).le
        calc archLevyDensity y * Q y ≤ archLevyDensity y * (L ^ 2 * y ^ 2 * (D - 0 + y)) :=
              mul_le_mul_of_nonneg_left hQ hω
          _ ≤ archLevyDensity y * (L ^ 2 * y ^ 2 * (2 * D)) := by
              refine mul_le_mul_of_nonneg_left ?_ hω
              have := hy.2
              nlinarith [sq_nonneg (L * y)]
          _ = 2 * D * L ^ 2 * (y ^ 2 * archLevyDensity y) := by ring
    refine h1.trans ?_
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left (setIntegral_mono_set integrableOn_sq_mul_archLevyDensity
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy =>
        mul_nonneg (sq_nonneg y) (archLevyDensity_pos hy).le))
      (Filter.Eventually.of_forall fun y hy => hy.1)) (by positivity)
  -- far: `Q(y) ≤ 4 ‖f‖²`
  have hfar : ∫ y in Set.Ioi D, archLevyDensity y * Q y ≤
      4 * M * WeilLevyPoleGauss.archLevyAntideriv D := by
    have hω := WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi hD
    have h1 := setIntegral_mono_on (s := Set.Ioi D) (hI.mono_set fun y hy => lt_trans hD hy)
      (hω.const_mul (4 * M)) measurableSet_Ioi fun y hy => by
        have hQ := integral_sub_shift_sq_le_four hf.continuous hfc y
        have hω0 := (archLevyDensity_pos (lt_trans hD hy)).le
        calc archLevyDensity y * Q y ≤ archLevyDensity y * (4 * M) := mul_le_mul_of_nonneg_left hQ hω0
          _ = 4 * M * archLevyDensity y := by ring
    rw [integral_const_mul, WeilLevyCoshCrossover.integral_archLevyDensity_Ioi hD] at h1
    exact h1
  have hm2 := levySecondMoment_le
  have hDL : 0 ≤ 2 * D * L ^ 2 := by positivity
  nlinarith

/-- `2θ′(0) < −5`. -/
theorem two_gammaHardyPhaseRate_zero_lt : 2 * gammaHardyPhaseRate 0 < -5 := by
  rw [gammaHardyPhaseRate_zero_closed]
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hlog2 := Real.log_two_gt_d9
  have hpi := Real.pi_gt_d2
  have hlogpi : 1 < Real.log π := by
    rw [Real.lt_log_iff_exp_lt Real.pi_pos]
    linarith [Real.exp_one_lt_d9]
  linarith

/-! ### The dipole -/

/-- The cosh moment of a translate: `C(g(· − a)) = cosh(a/2) C(g) + sinh(a/2) S(g)`. -/
theorem coshHalfMoment_comp_sub (g : ℝ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (a : ℝ) : coshHalfMoment (fun u => g (u - a)) =
      Real.cosh (a / 2) * coshHalfMoment g + Real.sinh (a / 2) * sinhHalfMoment g := by
  unfold coshHalfMoment sinhHalfMoment
  have h := integral_sub_right_eq_self (μ := volume) (fun v => g v * Real.cosh ((v + a) / 2)) a
  simp only [sub_add_cancel] at h
  rw [h, ← integral_const_mul, ← integral_const_mul, ← integral_add]
  · congr 1
    funext v
    rw [show (v + a) / 2 = v / 2 + a / 2 by ring, Real.cosh_add]
    ring
  · exact ((hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right).const_mul _
  · exact ((hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right).const_mul _

/-- The dipole weights `x_1 = 1`, `x_2 = −t`. -/
def dipoleWeights (t : ℝ) (n : ℕ) : ℝ := if n = 1 then 1 else if n = 2 then -t else 0

theorem atomicTest_dipole (g : ℝ → ℝ) (t : ℝ) :
    atomicTest 2 (dipoleWeights t) g = fun u => g u - t * g (u - Real.log 2) := by
  funext u
  have h : Finset.Icc 1 2 = {1, 2} := by decide
  simp only [atomicTest, h, Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2} : Finset ℕ)),
    Finset.sum_singleton, dipoleWeights, if_pos rfl, if_neg (by decide : (2 : ℕ) ≠ 1),
    Nat.cast_one, Real.log_one, sub_zero]
  push_cast
  ring

/-- The sign twist aligned with the lag correlations of `f`: `ω(k) = sign pairing_k(f)`. -/
def alignedTwist (f : ℝ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun k => if k = 0 then 0 else if 0 ≤ pairing f k then 1 else -1, by simp⟩

theorem abs_alignedTwist_le (f : ℝ → ℝ) (k : ℕ) : |alignedTwist f k| ≤ 1 := by
  show |(if k = 0 then 0 else if 0 ≤ pairing f k then 1 else -1 : ℝ)| ≤ 1
  split_ifs <;> simp

/-- Against the aligned twist the twisted prime sum is `Σ Λ_k |pairing_k| ≥ 0`. -/
theorem twistedPrimeSum_alignedTwist_nonneg (f : ℝ → ℝ) :
    0 ≤ twistedPrimeSum (alignedTwist f) f := by
  unfold twistedPrimeSum
  refine tsum_nonneg fun k => ?_
  rw [show (∫ t, f t * f (t - Real.log k)) + ∫ t, f t * f (t + Real.log k) = pairing f k from rfl,
    mul_comm (alignedTwist f k), mul_assoc]
  refine mul_nonneg (vonMangoldtAtom_nonneg' k) ?_
  show 0 ≤ (if k = 0 then 0 else if 0 ≤ pairing f k then 1 else -1 : ℝ) * pairing f k
  split_ifs with h0 h1
  · simp
  · linarith
  · nlinarith

theorem integral_sub_shift_neg_sq (g : ℝ → ℝ) (a : ℝ) :
    ∫ u, (g u - g (u - a)) ^ 2 = ∫ u, (g u - g (u + a)) ^ 2 := by
  have h := integral_sub_right_eq_self (μ := volume) (fun v => (g v - g (v + a)) ^ 2) a
  simp only [sub_add_cancel] at h
  rw [← h]
  congr 1
  funext u
  ring

section Dipole

variable {g : ℝ → ℝ} {W K t a : ℝ}

/-- The dipole `g − t g(· − a)` of a bump supported in `[0, W]` lives in `[0, W + a]`. -/
theorem dipole_supp (hgsupp : ∀ u, u ∉ Set.Icc 0 W → g u = 0) (ha : 0 ≤ a) (u : ℝ)
    (hu : u ∉ Set.Icc 0 (W + a)) : g u - t * g (u - a) = 0 := by
  simp only [Set.mem_Icc, not_and_or, not_le] at hu
  rcases hu with hu | hu
  · rw [hgsupp u fun h => by linarith [h.1], hgsupp (u - a) fun h => by linarith [h.1]]; ring
  · rw [hgsupp u fun h => by linarith [h.2], hgsupp (u - a) fun h => by linarith [h.2]]; ring

/-- The dipole of a `(K/W)`-Lipschitz bump with `0 ≤ t ≤ 1` is `(2K/W)`-Lipschitz. -/
theorem dipole_lipschitz (hgL : ∀ u v, |g u - g v| ≤ K / W * |u - v|) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (u v : ℝ) :
    |g u - t * g (u - a) - (g v - t * g (v - a))| ≤ 2 * K / W * |u - v| := by
  have h1 := hgL u v
  have h2 := hgL (u - a) (v - a)
  rw [show u - a - (v - a) = u - v by ring] at h2
  have hKW : 0 ≤ K / W * |u - v| := (abs_nonneg _).trans h1
  calc |g u - t * g (u - a) - (g v - t * g (v - a))|
      = |(g u - g v) - t * (g (u - a) - g (v - a))| := by ring_nf
    _ ≤ |g u - g v| + t * |g (u - a) - g (v - a)| := by
        refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
        rw [abs_mul, abs_of_nonneg ht0]
    _ ≤ K / W * |u - v| + 1 * (K / W * |u - v|) :=
        add_le_add h1 (mul_le_mul ht1 h2 (abs_nonneg _) zero_le_one)
    _ = 2 * K / W * |u - v| := by ring

/-- The cosh moment of the dipole vanishes for `t = C(g)/C(g(· − a))`. -/
theorem coshHalfMoment_dipole (hg : Continuous g) (hgc : HasCompactSupport g)
    (hC : coshHalfMoment (fun u => g (u - a)) ≠ 0) :
    coshHalfMoment (fun u => g u - coshHalfMoment g / coshHalfMoment (fun u => g (u - a)) *
      g (u - a)) = 0 := by
  set c := coshHalfMoment g / coshHalfMoment (fun u => g (u - a))
  have i1 : Integrable fun u => g u * Real.cosh (u / 2) :=
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right
  have i2 : Integrable fun u => g (u - a) * Real.cosh (u / 2) :=
    ((hg.comp (continuous_sub_right a)).mul (by fun_prop)).integrable_of_hasCompactSupport
      (hgc.comp_homeomorph (Homeomorph.subRight a)).mul_right
  have e : coshHalfMoment (fun u => g u - c * g (u - a)) =
      coshHalfMoment g - c * coshHalfMoment (fun u => g (u - a)) := by
    unfold coshHalfMoment
    rw [← integral_const_mul, ← integral_sub i1 (i2.const_mul c)]
    congr 1
    funext u
    ring
  rw [e]
  simp only [c]
  field_simp
  ring

/-- **The mass of the dipole**: `‖g − t g(· − a)‖² ≥ (τ²/2)‖g‖² − ‖g − g(· − a)‖²` for
`τ ≤ 1 − t`, `0 ≤ t ≤ 1`. -/
theorem integral_dipole_sq_ge (hg : Continuous g) (hgc : HasCompactSupport g) {τ : ℝ} (hτ : 0 ≤ τ)
    (hτt : τ ≤ 1 - t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    τ ^ 2 / 2 * (∫ u, g u ^ 2) - ∫ u, (g u - g (u - a)) ^ 2 ≤
      ∫ u, (g u - t * g (u - a)) ^ 2 := by
  have hga : Continuous fun u => g (u - a) := hg.comp (continuous_sub_right a)
  have hgac : HasCompactSupport fun u => g (u - a) := hgc.comp_homeomorph (Homeomorph.subRight a)
  have i1 : Integrable fun u => g u ^ 2 := integrable_sq_of_continuous hg hgc
  have i2 : Integrable fun u => (g u - g (u - a)) ^ 2 :=
    integrable_sq_of_continuous (hg.sub hga) (hgc.sub hgac)
  have i3 : Integrable fun u => (g u - t * g (u - a)) ^ 2 :=
    integrable_sq_of_continuous (hg.sub (continuous_const.mul hga)) (hgc.sub hgac.mul_left)
  have hpt : ∀ u, τ ^ 2 / 2 * g u ^ 2 - (g u - g (u - a)) ^ 2 ≤ (g u - t * g (u - a)) ^ 2 := by
    intro u
    have hp : τ ^ 2 * g u ^ 2 ≤ (1 - t) ^ 2 * g u ^ 2 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hτ hτt 2) (sq_nonneg _)
    have hq : t ^ 2 * (g u - g (u - a)) ^ 2 ≤ (g u - g (u - a)) ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg _) (by nlinarith)
    have e : g u - t * g (u - a) = (1 - t) * g u + t * (g u - g (u - a)) := by ring
    rw [e]
    nlinarith [sq_nonneg ((1 - t) * g u + 2 * (t * (g u - g (u - a))))]
  have i4 : Integrable fun u => τ ^ 2 / 2 * g u ^ 2 - (g u - g (u - a)) ^ 2 :=
    (i1.const_mul _).sub i2
  have := integral_mono i4 i3 hpt
  rwa [integral_sub (i1.const_mul _) i2, integral_const_mul] at this

end Dipole

/-- The final inequality: a negative mass term beats the Lipschitz terms of a wide bump. -/
theorem dipole_arch_neg {τ W K a A F G : ℝ} (hτ : 0 < τ) (hW : 1 ≤ W) (haW : a ≤ W) (ha : 0 ≤ a)
    (hK : 0 ≤ K) (hθ : 2 * gammaHardyPhaseRate 0 < -5) (hA0 : 0 ≤ A) (hA : A ≤ 1)
    (hF0 : 0 ≤ F) (hG : W / 2 ≤ G)
    (hmass : τ ^ 2 / 2 * G - (K / W) ^ 2 * a ^ 2 * (W + a) ≤ F)
    (hbig : 2 * (K ^ 2 * a ^ 2 + 144 * K ^ 2) < τ ^ 2 / 4 * W ^ 2) :
    2 * gammaHardyPhaseRate 0 * F + (36 * (W + a) * (2 * K / W) ^ 2 + 4 * A * F) < 0 := by
  have hW0 : 0 < W := by linarith
  have h1 : 2 * gammaHardyPhaseRate 0 * F + 4 * A * F ≤ -F := by nlinarith
  have hlip : 36 * (W + a) * (2 * K / W) ^ 2 + (K / W) ^ 2 * a ^ 2 * (W + a) ≤
      2 * (K ^ 2 * a ^ 2 + 144 * K ^ 2) / W := by
    have e : 36 * (W + a) * (2 * K / W) ^ 2 + (K / W) ^ 2 * a ^ 2 * (W + a) =
        (W + a) * (144 * K ^ 2 + K ^ 2 * a ^ 2) / W ^ 2 := by
      field_simp; ring
    rw [e, div_le_div_iff₀ (by positivity) hW0]
    have : (W + a) * W ≤ 2 * W ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right this (show 0 ≤ 144 * K ^ 2 + K ^ 2 * a ^ 2 by positivity)]
  have hdiv : 2 * (K ^ 2 * a ^ 2 + 144 * K ^ 2) / W < τ ^ 2 / 4 * W := by
    rw [div_lt_iff₀ hW0]; nlinarith
  have hG' : τ ^ 2 / 4 * W ≤ τ ^ 2 / 2 * G := by nlinarith [sq_nonneg τ]
  linarith

/-- **The universal threshold is finite**: there is a width `W` and a nonnegative `C²` bump
supported in `[0, W]` such that on the atomic family of level `2` — overlap ratio `W/log(3/2)` —
some test with vanishing cosh moment has `Re W_ω + 2S² < 0` for a sign twist `|ω| ≤ 1`. -/
theorem universalThreshold_finite :
    ∃ W : ℝ, 0 < W ∧ ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ (∀ u, u ∉ Set.Icc 0 W → g u = 0) ∧
      (∀ u, 0 ≤ g u) ∧ ∃ (x : ℕ → ℝ) (ω : ArithmeticFunction ℝ), (∀ k, |ω k| ≤ 1) ∧
        coshHalfMoment (atomicTest 2 x g) = 0 ∧
        weilQuadTw (fun n => ω n * ArithmeticFunction.vonMangoldt n) (atomicTest 2 x g) +
          2 * sinhHalfMoment (atomicTest 2 x g) ^ 2 < 0 := by
  -- the profile: a plateau on `[0, 1]`
  obtain ⟨Cs, -, hCs⟩ := exists_lipschitz_smoothTransition
  have hη : (0 : ℝ) < 1 / 4 := by norm_num
  have hφ2 : 1 / 2 ≤ ∫ u, plateau (1 / 4) u ^ 2 := by
    have := integral_plateau_sq_ge hη (by norm_num); linarith
  set K := 2 * Cs / (1 / 4)
  have hK : ∀ u v, |plateau (1 / 4) u - plateau (1 / 4) v| ≤ K * |u - v| := abs_plateau_sub_le hCs hη
  have hK0 : 0 ≤ K := (abs_nonneg _).trans ((hK 1 0).trans (by simp))
  set a := Real.log 2
  have ha : 0 < a := Real.log_pos one_lt_two
  have hcosh : 1 < Real.cosh (a / 2) := Real.one_lt_cosh.mpr (by positivity)
  set τ := 1 - 1 / Real.cosh (a / 2)
  have hτ : 0 < τ := by
    have : 1 / Real.cosh (a / 2) < 1 := by rw [div_lt_one (by linarith)]; exact hcosh
    simp only [τ]; linarith
  -- choose the width
  have hev : ∀ᶠ W : ℝ in atTop, WeilLevyPoleGauss.archLevyAntideriv (W + a) ≤ 1 ∧ 1 ≤ W ∧ a ≤ W ∧
      2 * (K ^ 2 * a ^ 2 + 144 * K ^ 2) < τ ^ 2 / 4 * W ^ 2 := by
    have h1 := (WeilLevyCoshCrossover.tendsto_archLevyAntideriv_atTop.comp
      (tendsto_atTop_add_const_right _ a tendsto_id)).eventually
      (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    have h4 := ((tendsto_pow_atTop two_ne_zero).const_mul_atTop
      (show (0 : ℝ) < τ ^ 2 / 4 by positivity)).eventually_gt_atTop (2 * (K ^ 2 * a ^ 2 + 144 * K ^ 2))
    filter_upwards [h1, eventually_ge_atTop 1, eventually_ge_atTop a, h4] with W h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨W, hAW, hW1, haW, hBW⟩ := hev.exists
  have hW0 : 0 < W := by linarith
  -- the bump `g = φ(·/W)`
  set g : ℝ → ℝ := atomDilate (plateau (1 / 4)) W
  have hg : ContDiff ℝ 2 g := (contDiff_plateau _).comp (contDiff_id.div_const W)
  have hgsupp : ∀ u, u ∉ Set.Icc 0 W → g u = 0 := fun u hu => plateau_eq_zero hη fun h => hu
    ⟨by have := h.1; rwa [le_div_iff₀ hW0, zero_mul] at this,
      by have := h.2; rwa [div_le_iff₀ hW0, one_mul] at this⟩
  have hgc : HasCompactSupport g := HasCompactSupport.intro isCompact_Icc fun u hu => hgsupp u hu
  have hg0 : ∀ u, 0 ≤ g u := fun u => plateau_nonneg _
  have hg1 : ∀ u, g u ≤ 1 := fun u => plateau_le_one _
  have hgL : ∀ u v, |g u - g v| ≤ K / W * |u - v| := fun u v => by
    have := hK (u / W) (v / W)
    rw [← sub_div, abs_div, abs_of_pos hW0] at this
    calc |g u - g v| ≤ K * (|u - v| / W) := this
      _ = K / W * |u - v| := by ring
  have hg2 : W / 2 ≤ ∫ u, g u ^ 2 := by
    rw [integral_atomDilate_sq hW0]; nlinarith
  -- the moments and the weight `t`
  have hCg : ∫ u, g u ^ 2 ≤ coshHalfMoment g := by
    unfold coshHalfMoment
    refine integral_mono (integrable_sq_of_continuous hg.continuous hgc)
      ((hg.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right) fun u => ?_
    have h1 := Real.one_le_cosh (u / 2)
    nlinarith [hg0 u, hg1 u]
  have hCg0 : 0 < coshHalfMoment g := lt_of_lt_of_le (by linarith) hCg
  have hSg0 : 0 ≤ sinhHalfMoment g := by
    unfold sinhHalfMoment
    refine integral_nonneg fun u => ?_
    rcases le_or_gt 0 u with hu | hu
    · exact mul_nonneg (hg0 u) (Real.sinh_nonneg_iff.mpr (by linarith))
    · simp [hgsupp u fun h => by linarith [h.1]]
  have hCa : Real.cosh (a / 2) * coshHalfMoment g ≤ coshHalfMoment (fun u => g (u - a)) := by
    rw [coshHalfMoment_comp_sub g hg.continuous hgc a]
    nlinarith [Real.sinh_nonneg_iff.mpr (show (0 : ℝ) ≤ a / 2 by positivity)]
  have hCapos : 0 < coshHalfMoment (fun u => g (u - a)) := lt_of_lt_of_le (by nlinarith) hCa
  set t := coshHalfMoment g / coshHalfMoment (fun u => g (u - a))
  have ht0 : 0 ≤ t := div_nonneg hCg0.le hCapos.le
  have htτ : τ ≤ 1 - t := by
    have : t ≤ 1 / Real.cosh (a / 2) := by
      rw [div_le_div_iff₀ hCapos (by linarith), one_mul]; nlinarith
    simp only [τ]; linarith
  have ht1 : t ≤ 1 := by linarith
  -- the dipole
  set f := atomicTest 2 (dipoleWeights t) g
  have hfeq : f = fun u => g u - t * g (u - a) := atomicTest_dipole g t
  have hf : ContDiff ℝ 2 f := contDiff_atomicTest hg 2 _
  have hfc : HasCompactSupport f := hasCompactSupport_atomicTest hgsupp 2 _
  have hfsupp : ∀ u, u ∉ Set.Icc 0 (W + a) → f u = 0 := fun u hu => by
    rw [hfeq]; exact dipole_supp hgsupp ha.le u hu
  have hfL : ∀ u v, |f u - f v| ≤ 2 * K / W * |u - v| := fun u v => by
    rw [hfeq]; exact dipole_lipschitz hgL ht0 ht1 u v
  have hCf : coshHalfMoment f = 0 := by
    rw [hfeq]; exact coshHalfMoment_dipole hg.continuous hgc hCapos.ne'
  -- the archimedean form is negative
  have hshift : ∫ u, (g u - g (u - a)) ^ 2 ≤ (K / W) ^ 2 * a ^ 2 * (W + a) := by
    rw [integral_sub_shift_neg_sq]
    have := integral_sub_shift_sq_le_of_supp hg.continuous hgc hgL hgsupp hW0.le ha.le
    linarith
  have hmass : τ ^ 2 / 2 * (∫ u, g u ^ 2) - (K / W) ^ 2 * a ^ 2 * (W + a) ≤ ∫ u, f u ^ 2 := by
    rw [hfeq]
    have := integral_dipole_sq_ge hg.continuous hgc hτ.le htτ ht0 ht1 (a := a)
    linarith
  have hlevy := levyEnergy_le_of_wide hf hfc hfL hfsupp (by linarith)
  have hAW0 : 0 ≤ WeilLevyPoleGauss.archLevyAntideriv (W + a) := by
    rw [← WeilLevyCoshCrossover.integral_archLevyDensity_Ioi (by linarith)]
    exact setIntegral_nonneg measurableSet_Ioi fun y hy =>
      (archLevyDensity_pos (lt_trans (by linarith) hy)).le
  have hneg : archForm f < 0 := by
    rw [archForm_eq_levyEnergy hf hfc]
    have := dipole_arch_neg hτ hW1 haW ha.le hK0 two_gammaHardyPhaseRate_zero_lt hAW0 hAW
      (integral_nonneg fun u => sq_nonneg (f u)) hg2 hmass hBW
    linarith
  -- assemble
  refine ⟨W, hW0, g, hg, hgsupp, hg0, dipoleWeights t, alignedTwist f, abs_alignedTwist_le f,
    hCf, ?_⟩
  have hfR : SupportedIn (W + a) f := fun u hu => hfsupp u fun h => by
    have h1 := h.1
    have h2 := h.2
    rcases le_or_gt 0 u with hu0 | hu0
    · rw [abs_of_nonneg hu0] at hu; linarith
    · linarith
  rw [weilQuadTw_eq_markov (alignedTwist f) hf hfc hfR, hCf]
  have := twistedPrimeSum_alignedTwist_nonneg f
  nlinarith

/-- **The universal threshold is bracketed**: every real twist `|ω| ≤ 1` satisfies
`Re W_ω + 2S² = M_ω + 2C² ≥ 0` on every atomic family of width `≤ c₀ δ_N`, for every `N`
(`TheSpacingScaleLawIsUniversal`); and some sign twist violates it on the dipole of level `2` at a
finite overlap ratio (`universalThreshold_finite`). So `c₀ ≤ K_univ < ∞`. -/
theorem universalThreshold_bracket :
    (∀ {ω : ArithmeticFunction ℝ} {g : ℝ → ℝ} {w : ℝ} {N : ℕ}, (∀ k, |ω k| ≤ 1) →
      ContDiff ℝ 2 g → HasCompactSupport g → (∀ u, u ∉ Set.Icc 0 w → g u = 0) → 1 ≤ N → 0 < w →
      w ≤ spacingWidthRatio * atomSpacing N → ∀ x : ℕ → ℝ,
        0 ≤ weilQuadTw (fun n => ω n * ArithmeticFunction.vonMangoldt n) (atomicTest N x g) +
          2 * sinhHalfMoment (atomicTest N x g) ^ 2) ∧
    ∃ W : ℝ, 0 < W ∧ ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ (∀ u, u ∉ Set.Icc 0 W → g u = 0) ∧
      ∃ (x : ℕ → ℝ) (ω : ArithmeticFunction ℝ), (∀ k, |ω k| ≤ 1) ∧
        weilQuadTw (fun n => ω n * ArithmeticFunction.vonMangoldt n) (atomicTest 2 x g) +
          2 * sinhHalfMoment (atomicTest 2 x g) ^ 2 < 0 := by
  refine ⟨fun {ω g w N} hω hg hgc hgsupp hN hw0 hw x => ?_, ?_⟩
  · have hf := contDiff_atomicTest hg N x
    have hfc := hasCompactSupport_atomicTest hgsupp N x
    obtain ⟨R, -, -, -, hR, -, -⟩ := exists_test_constants hf hfc
    rw [weilQuadTw_eq_markov ω hf hfc hR]
    have := twistedMarkov_atomicTest_nonneg_spacing_of_abs_le hω hg hgc hgsupp hN hw0 hw x
    nlinarith [sq_nonneg (coshHalfMoment (atomicTest N x g))]
  · obtain ⟨W, hW, g, hg, hgs, -, x, ω, hω, -, hneg⟩ := universalThreshold_finite
    exact ⟨W, hW, g, hg, hgs, x, ω, hω, hneg⟩

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
