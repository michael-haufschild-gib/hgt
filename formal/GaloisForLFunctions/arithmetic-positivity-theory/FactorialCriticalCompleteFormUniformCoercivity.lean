import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalCompleteFormDivergence
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeFiniteScaleNegativity

/-!
# Uniform coercivity of the complete critical form

On a finite translated support `S` every translated autocorrelation is the quadratic form of the
symmetric correlation matrix of single-scale critical sources. Polarizing the rational dilation
law gives its entrywise limit: `e^{-t/2}` times the polarized dilation limit at ratio `e^t`,
which is the critical mass matrix at `t = 0` and vanishes whenever `e^t` is irrational.

The decorrelation defect `d_n(x)` — distance of the zero-shift matrix from the mass matrix plus
the size of the shift-`x` matrix — therefore tends to `0` almost everywhere, and with the mass
floor `Σ b_j²/(12π⁴)` it bounds every jump from below:
`ac(0) - ac(x) ≥ (1/(12π⁴) - d_n(x)) Σ b_j²`. Integrating against the Lévy weight gives a
floor common to all coefficient vectors, which diverges by Fatou's lemma. Together with the
uniform bounds on the mass and polar channels and the eventual negativity of the prime channel,
the complete critical form is eventually coercive on every finite support with arbitrarily
large constant, in particular eventually positive definite.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-- Symmetrized cross correlation of the translated single-scale sources at offsets `i, j`. -/
def criticalTranslatedSymmetricCorrelation (n i j : ℕ) (t : ℝ) : ℝ :=
  (criticalScaleCrossCorrelation (n+i) (n+j) t + criticalScaleCrossCorrelation (n+j) (n+i) t) / 2

/-- The symmetric correlation matrix is symmetric. -/
theorem criticalTranslatedSymmetricCorrelation_symm (n i j : ℕ) (t : ℝ) :
    criticalTranslatedSymmetricCorrelation n i j t = criticalTranslatedSymmetricCorrelation n j i t := by
  unfold criticalTranslatedSymmetricCorrelation; ring

/-- Polarization of the dilation limit: the limiting symmetric correlation matrix at ratio `ρ`. -/
def factorialCriticalDilationPolarization (i j : ℕ) (ρ : ℝ) : ℝ :=
  if i = j then factorialCriticalDilationLimit {i} (fun _ => 1) ρ else
    (factorialCriticalDilationLimit {i, j} (fun _ => 1) ρ - factorialCriticalDilationLimit {i} (fun _ => 1) ρ -
      factorialCriticalDilationLimit {j} (fun _ => 1) ρ) / 2

private theorem sum_sum_symmetrize (S : Finset ℕ) (b : ℕ → ℝ) (X : ℕ → ℕ → ℝ) :
    ∑ i ∈ S, ∑ j ∈ S, b i * b j * X i j = ∑ i ∈ S, ∑ j ∈ S, b i * b j * ((X i j + X j i) / 2) := by
  have hswap : ∑ i ∈ S, ∑ j ∈ S, b i * b j * X j i = ∑ i ∈ S, ∑ j ∈ S, b i * b j * X i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have : ∑ i ∈ S, ∑ j ∈ S, b i * b j * ((X i j + X j i) / 2) =
      (∑ i ∈ S, ∑ j ∈ S, b i * b j * X i j + ∑ i ∈ S, ∑ j ∈ S, b i * b j * X j i) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [this, hswap]; ring

/-- The translated autocorrelation is the quadratic form of the symmetric correlation matrix. -/
theorem criticalTranslatedAutocorrelation_eq_symmetric (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    criticalTranslatedAutocorrelation S b n t =
      ∑ i ∈ S, ∑ j ∈ S, b i * b j * criticalTranslatedSymmetricCorrelation n i j t := by
  unfold criticalTranslatedAutocorrelation criticalTranslatedSource
  rw [criticalFactorialSource_translated_correlation_eq_sum S b n ht, sum_sum_symmetrize]
  rfl

private theorem autocorr_singleton (n i : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    criticalTranslatedAutocorrelation {i} (fun _ => 1) n t = criticalTranslatedSymmetricCorrelation n i i t := by
  rw [criticalTranslatedAutocorrelation_eq_symmetric _ _ _ ht]; simp

private theorem autocorr_pair (n : ℕ) {i j : ℕ} (hij : i ≠ j) {t : ℝ} (ht : 0 ≤ t) :
    criticalTranslatedAutocorrelation {i, j} (fun _ => 1) n t =
      criticalTranslatedSymmetricCorrelation n i i t + criticalTranslatedSymmetricCorrelation n j j t +
        2 * criticalTranslatedSymmetricCorrelation n i j t := by
  rw [criticalTranslatedAutocorrelation_eq_symmetric _ _ _ ht]
  simp only [Finset.sum_pair hij, one_mul]
  rw [criticalTranslatedSymmetricCorrelation_symm n j i]; ring

/-- **Entrywise dilation law.** Each symmetric cross correlation of translated single-scale
sources converges to `e^{-t/2}` times the polarized dilation limit at ratio `e^t`. -/
theorem tendsto_criticalTranslatedSymmetricCorrelation (i j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => criticalTranslatedSymmetricCorrelation n i j t) atTop
      (𝓝 (Real.exp (-(t / 2)) * factorialCriticalDilationPolarization i j (Real.exp t))) := by
  have hA (T : Finset ℕ) : Tendsto (fun n => criticalTranslatedAutocorrelation T (fun _ => 1) n t) atTop
      (𝓝 (Real.exp (-(t / 2)) * factorialCriticalDilationLimit T (fun _ => 1) (Real.exp t))) :=
    criticalFactorialSource_translated_autocorrelation_tendsto T (fun _ => 1) ht
  unfold factorialCriticalDilationPolarization
  rcases eq_or_ne i j with rfl | hij
  · rw [if_pos rfl]
    exact (hA {i}).congr fun n => autocorr_singleton n i ht
  · rw [if_neg hij]
    have h := ((hA {i, j}).sub ((hA {i}).add (hA {j}))).div_const 2
    refine (h.congr fun n => ?_).trans (le_of_eq (by congr 1; ring))
    rw [autocorr_pair n hij ht, autocorr_singleton n i ht, autocorr_singleton n j ht]; ring

/-- At an irrational dilation ratio the polarized limit vanishes. -/
theorem factorialCriticalDilationPolarization_eq_zero_of_irrational (i j : ℕ) {ρ : ℝ}
    (hρ : Irrational ρ) : factorialCriticalDilationPolarization i j ρ = 0 := by
  unfold factorialCriticalDilationPolarization
  simp only [factorialCriticalDilationLimit_eq_zero_of_irrational _ _ hρ]; simp

/-- The limiting mass matrix represents the critical mass of every pattern. -/
theorem factorialCriticalDilationLimit_one_eq_polarization (S : Finset ℕ) (b : ℕ → ℝ) :
    factorialCriticalDilationLimit S b 1 =
      ∑ i ∈ S, ∑ j ∈ S, b i * b j * factorialCriticalDilationPolarization i j 1 := by
  have h1 : Tendsto (fun n => criticalTranslatedAutocorrelation S b n 0) atTop
      (𝓝 (factorialCriticalDilationLimit S b 1)) := by
    have h := criticalFactorialSource_translated_autocorrelation_tendsto S b (le_refl (0 : ℝ))
    simp only [zero_div, neg_zero, Real.exp_zero, one_mul] at h
    exact h
  have h2 : Tendsto (fun n => criticalTranslatedAutocorrelation S b n 0) atTop
      (𝓝 (∑ i ∈ S, ∑ j ∈ S, b i * b j * factorialCriticalDilationPolarization i j 1)) := by
    refine (tendsto_finsetSum S fun i _ => tendsto_finsetSum S fun j _ =>
      (tendsto_criticalTranslatedSymmetricCorrelation i j le_rfl).const_mul (b i * b j)).congr' ?_ |>.trans
      (le_of_eq (by simp))
    exact Eventually.of_forall fun n => (criticalTranslatedAutocorrelation_eq_symmetric S b n le_rfl).symm
  exact tendsto_nhds_unique h1 h2

/-- Decorrelation defect of the translated support `S` at shift `x`: distance of the zero-shift
correlation matrix from the limiting mass matrix plus the size of the shift-`x` matrix. -/
def criticalTranslatedDecorrelationDefect (S : Finset ℕ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S, (|criticalTranslatedSymmetricCorrelation n i j 0 -
    factorialCriticalDilationPolarization i j 1| + |criticalTranslatedSymmetricCorrelation n i j x|)

private theorem abs_mul_le_sum_sq {S : Finset ℕ} (b : ℕ → ℝ) {i j : ℕ} (hi : i ∈ S) (hj : j ∈ S) :
    |b i * b j| ≤ ∑ k ∈ S, b k ^ 2 := by
  have h1 := Finset.single_le_sum (fun k _ => sq_nonneg (b k)) hi
  have h2 := Finset.single_le_sum (fun k _ => sq_nonneg (b k)) hj
  rw [abs_mul]
  nlinarith [sq_nonneg (|b i| - |b j|), sq_abs (b i), sq_abs (b j)]

private theorem abs_quadratic_le (S : Finset ℕ) (b : ℕ → ℝ) (a : ℕ → ℕ → ℝ) :
    |∑ i ∈ S, ∑ j ∈ S, b i * b j * a i j| ≤ (∑ k ∈ S, b k ^ 2) * ∑ i ∈ S, ∑ j ∈ S, |a i j| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_mul_le_sum_sq b hi hj) (abs_nonneg _)

/-- **Pointwise jump floor.** At every nonnegative shift the jump `ac(0) - ac(x)` of every
translated pattern dominates `(1/(12π⁴) - defect(x)) Σ b_j²`. -/
theorem criticalTranslatedAutocorrelation_jump_ge (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) {x : ℝ}
    (hx : 0 ≤ x) :
    (1 / (12 * Real.pi ^ 4) - criticalTranslatedDecorrelationDefect S n x) * ∑ j ∈ S, b j ^ 2 ≤
      criticalTranslatedAutocorrelation S b n 0 - criticalTranslatedAutocorrelation S b n x := by
  set E := ∑ j ∈ S, b j ^ 2
  set K := fun i j => factorialCriticalDilationPolarization i j 1
  set Y := fun t i j => criticalTranslatedSymmetricCorrelation n i j t
  have hsplit : criticalTranslatedAutocorrelation S b n 0 - criticalTranslatedAutocorrelation S b n x =
      factorialCriticalDilationLimit S b 1 +
        ∑ i ∈ S, ∑ j ∈ S, b i * b j * ((Y 0 i j - K i j) - Y x i j) := by
    rw [criticalTranslatedAutocorrelation_eq_symmetric S b n le_rfl,
      criticalTranslatedAutocorrelation_eq_symmetric S b n hx,
      factorialCriticalDilationLimit_one_eq_polarization, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by simp only [Y, K]; ring
  have herr := abs_quadratic_le S b fun i j => (Y 0 i j - K i j) - Y x i j
  have hdef : ∑ i ∈ S, ∑ j ∈ S, |(Y 0 i j - K i j) - Y x i j| ≤ criticalTranslatedDecorrelationDefect S n x :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => abs_sub _ _
  have hE : 0 ≤ E := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hm := factorialCriticalDilationLimit_one_ge S b
  rw [hsplit]
  have h3 := neg_abs_le (∑ i ∈ S, ∑ j ∈ S, b i * b j * ((Y 0 i j - K i j) - Y x i j))
  have h4 := mul_le_mul_of_nonneg_left hdef hE
  have h5 : E / (12 * Real.pi ^ 4) = 1 / (12 * Real.pi ^ 4) * E := by ring
  nlinarith

/-- Cross correlations of single-scale sources are measurable in the shift. -/
theorem measurable_criticalScaleCrossCorrelation (p q : ℕ) :
    Measurable (criticalScaleCrossCorrelation p q) := by
  have hm : StronglyMeasurable fun z : ℝ × ℝ =>
      criticalScaleSource p z.2 * criticalScaleSource q (z.2 - z.1) :=
    (((measurable_criticalScaleSource p).comp measurable_snd).mul
      ((measurable_criticalScaleSource q).comp (measurable_snd.sub measurable_fst))).stronglyMeasurable
  exact (hm.integral_prod_right' (ν := volume)).measurable

/-- Decorrelation defects are measurable in the shift. -/
theorem measurable_criticalTranslatedDecorrelationDefect (S : Finset ℕ) (n : ℕ) :
    Measurable (criticalTranslatedDecorrelationDefect S n) := by
  unfold criticalTranslatedDecorrelationDefect criticalTranslatedSymmetricCorrelation
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact measurable_const.add ((((measurable_criticalScaleCrossCorrelation _ _).add
    (measurable_criticalScaleCrossCorrelation _ _)).div_const 2).abs)

/-- Decorrelation defects vanish in the translated limit at every shift with irrational
exponential. -/
theorem tendsto_criticalTranslatedDecorrelationDefect (S : Finset ℕ) {x : ℝ} (hx : 0 ≤ x)
    (hirr : Irrational (Real.exp x)) :
    Tendsto (fun n => criticalTranslatedDecorrelationDefect S n x) atTop (𝓝 0) := by
  have h := tendsto_finsetSum S fun i _ => tendsto_finsetSum S fun j _ =>
    (((tendsto_criticalTranslatedSymmetricCorrelation i j (le_refl (0 : ℝ))).sub_const
      (factorialCriticalDilationPolarization i j 1)).abs).add
    ((tendsto_criticalTranslatedSymmetricCorrelation i j hx).abs)
  simp only [zero_div, neg_zero, Real.exp_zero, one_mul, sub_self, abs_zero, zero_add,
    factorialCriticalDilationPolarization_eq_zero_of_irrational _ _ hirr, mul_zero,
    Finset.sum_const_zero] at h
  exact h

/-- The common Lévy floor of the translated support `S`. -/
def criticalTranslatedLevyFloor (S : Finset ℕ) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ x in Ioi 0, ENNReal.ofReal ((1 / (12 * Real.pi ^ 4) - criticalTranslatedDecorrelationDefect S n x) *
    BiScaleUncertainty.archLevySinhWeight x)

/-- The Lévy energy of every pattern on `S` dominates `Σ b_j²` times the common floor. -/
theorem criticalTranslatedLevyEnergy_ge_floor (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) :
    ENNReal.ofReal (∑ j ∈ S, b j ^ 2) * criticalTranslatedLevyFloor S n ≤
      criticalTranslatedLevyEnergy S b n := by
  unfold criticalTranslatedLevyFloor criticalTranslatedLevyEnergy
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Ioi fun x hx => ?_
  have hE : 0 ≤ ∑ j ∈ S, b j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [← ENNReal.ofReal_mul hE]
  apply ENNReal.ofReal_le_ofReal
  have hω := (BiScaleUncertainty.archLevySinhWeight_pos hx).le
  have := mul_le_mul_of_nonneg_right
    (criticalTranslatedAutocorrelation_jump_ge S b n (le_of_lt hx)) hω
  linarith [this]

/-- **Uniform archimedean divergence.** The common Lévy floor of every finite translated support
tends to `+∞`. -/
theorem tendsto_criticalTranslatedLevyFloor_top (S : Finset ℕ) :
    Tendsto (criticalTranslatedLevyFloor S) atTop (𝓝 ⊤) := by
  set c : ℝ := 1 / (12 * Real.pi ^ 4)
  have hc : 0 < c := by positivity
  set ω := BiScaleUncertainty.archLevySinhWeight
  set f : ℕ → ℝ → ℝ≥0∞ := fun n x =>
    ENNReal.ofReal ((c - criticalTranslatedDecorrelationDefect S n x) * ω x)
  have hmeas (n : ℕ) : AEMeasurable (f n) (volume.restrict (Ioi 0)) :=
    (ENNReal.measurable_ofReal.comp ((measurable_const.sub
      (measurable_criticalTranslatedDecorrelationDefect S n)).mul
      BiScaleUncertainty.measurable_archLevySinhWeight)).aemeasurable
  have hlim : ∀ᵐ x ∂(volume.restrict (Ioi 0)), Tendsto (fun n => f n x) atTop
      (𝓝 (ENNReal.ofReal (c * ω x))) := by
    filter_upwards [ae_restrict_of_ae ae_irrational_exp, ae_restrict_mem measurableSet_Ioi] with x hirr hx
    have h := ((tendsto_criticalTranslatedDecorrelationDefect S (le_of_lt hx) hirr).const_sub c).mul_const (ω x)
    rw [sub_zero] at h
    exact (ENNReal.continuous_ofReal.tendsto _).comp h
  have hfatou := lintegral_liminf_le' (μ := volume.restrict (Ioi 0)) (u := atTop) hmeas
  rw [lintegral_congr_ae (hlim.mono fun x hx => hx.liminf_eq),
    lintegral_ofReal_mul_archLevySinhWeight_eq_top hc] at hfatou
  apply ENNReal.tendsto_nhds_top
  intro k
  exact Filter.eventually_lt_of_lt_liminf (lt_of_lt_of_le (ENNReal.natCast_lt_top k) hfatou)

open _root_.Zeta23 in
/-- **Uniform coercivity of the complete critical form.** On every finite translated support and
for every constant `M`, beyond a threshold scale the complete critical energy dominates
`M Σ b_j²` simultaneously for all coefficient vectors: the Lévy floor diverges uniformly, the
mass and polar channels are bounded by multiples of `Σ b_j²`, and the prime channel is
eventually negative definite. -/
theorem eventually_criticalTranslatedCompleteEnergy_coercive (S : Finset ℕ) (M : ℝ) :
    ∀ᶠ n in atTop, ∀ b : ℕ → ℝ,
      ((M * ∑ j ∈ S, b j ^ 2 : ℝ) : EReal) ≤ criticalTranslatedCompleteEnergy S b n := by
  set K := fun i j => factorialCriticalDilationPolarization i j 1
  set B₁ : ℝ := ∑ i ∈ S, ∑ j ∈ S, (|K i j| + 1)
  set B : ℝ := |EF.gammaBracket 0| * B₁ + 1152 * S.card
  have hB₁ : 0 ≤ B₁ := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  have hB : 0 ≤ B := by positivity
  have hmass : ∀ᶠ n in atTop, ∀ i ∈ S, ∀ j ∈ S,
      |criticalTranslatedSymmetricCorrelation n i j 0 - K i j| < 1 := by
    rw [Filter.eventually_all_finset]; intro i _
    rw [Filter.eventually_all_finset]; intro j _
    have h := tendsto_criticalTranslatedSymmetricCorrelation i j (le_refl (0 : ℝ))
    simp only [zero_div, neg_zero, Real.exp_zero, one_mul] at h
    exact Metric.tendsto_nhds.mp h 1 one_pos
  have hfloor := (ENNReal.tendsto_nhds_top_iff_nnreal.mp (tendsto_criticalTranslatedLevyFloor_top S))
    (Real.toNNReal (|M| + B))
  filter_upwards [hmass, hfloor, eventually_factorialCriticalTranslatedPrimeEnergy_le S]
    with n hn hfl hpr b
  set E := ∑ j ∈ S, b j ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hlev : ((E * (|M| + B) : ℝ) : EReal) ≤ (criticalTranslatedLevyEnergy S b n : EReal) := by
    have h1 : ENNReal.ofReal (E * (|M| + B)) ≤ criticalTranslatedLevyEnergy S b n := by
      rw [ENNReal.ofReal_mul hE]
      refine le_trans ?_ (criticalTranslatedLevyEnergy_ge_floor S b n)
      gcongr
      exact hfl.le
    have h2 := EReal.coe_ennreal_le_coe_ennreal_iff.mpr h1
    rwa [EReal.coe_ennreal_ofReal, max_eq_left (by positivity)] at h2
  have hac0 : |criticalTranslatedAutocorrelation S b n 0| ≤ E * B₁ := by
    rw [criticalTranslatedAutocorrelation_eq_symmetric S b n le_rfl]
    refine (abs_quadratic_le S b _).trans (mul_le_mul_of_nonneg_left ?_ hE)
    refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
    have h1 := hn i hi j hj
    have h2 := abs_add_le (K i j) (criticalTranslatedSymmetricCorrelation n i j 0 - K i j)
    rw [add_sub_cancel] at h2
    linarith
  have hpol : |criticalTranslatedPolarProduct S b n| ≤ 576 * S.card * E := by
    have hn1 : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    have hcs : (∑ j ∈ S, |b j|) ^ 2 ≤ S.card * E := by
      simpa only [sq_abs] using (sq_sum_le_card_mul_sum_sq (s := S) (f := fun i => |b i|))
    calc _ ≤ (24 * ∑ j ∈ S, |b j|) ^ 2 / ((n+1 : ℕ) : ℝ) := abs_criticalTranslatedPolarProduct_le S b n
      _ ≤ (24 * ∑ j ∈ S, |b j|) ^ 2 := div_le_self (sq_nonneg _) hn1
      _ = 576 * (∑ j ∈ S, |b j|) ^ 2 := by ring
      _ ≤ 576 * (S.card * E) := by gcongr
      _ = 576 * S.card * E := by ring
  have hprime : factorialCriticalTranslatedPrimeEnergy S b n ≤ 0 := by
    have := hpr b
    have : 0 ≤ (2 / (7000 * Real.pi ^ 4)) * E := by positivity
    linarith
  have hch : -(B * E) ≤ criticalTranslatedArithmeticChannels S b n := by
    unfold criticalTranslatedArithmeticChannels
    have h1 := neg_abs_le (EF.gammaBracket 0 * criticalTranslatedAutocorrelation S b n 0)
    rw [abs_mul] at h1
    have h1' := mul_le_mul_of_nonneg_left hac0 (abs_nonneg (EF.gammaBracket 0))
    have h2 := neg_abs_le (criticalTranslatedPolarProduct S b n)
    have hBE : B * E = |EF.gammaBracket 0| * (E * B₁) + 2 * (576 * S.card * E) := by simp only [B]; ring
    linarith
  unfold criticalTranslatedCompleteEnergy
  have hME : M * E ≤ |M| * E := mul_le_mul_of_nonneg_right (le_abs_self M) hE
  calc ((M * E : ℝ) : EReal) ≤ ((E * (|M| + B) + criticalTranslatedArithmeticChannels S b n : ℝ) : EReal) := by
        rw [EReal.coe_le_coe_iff]
        have : E * (|M| + B) = |M| * E + B * E := by ring
        linarith
    _ = ((E * (|M| + B) : ℝ) : EReal) + (criticalTranslatedArithmeticChannels S b n : EReal) :=
        EReal.coe_add _ _
    _ ≤ _ := add_le_add hlev le_rfl

/-- **Eventual positive definiteness of the complete critical form** on every finite translated
support: beyond a threshold scale the complete critical energy is positive for every pattern
that is nonzero on the support. -/
theorem eventually_criticalTranslatedCompleteEnergy_pos (S : Finset ℕ) :
    ∀ᶠ n in atTop, ∀ b : ℕ → ℝ, (∃ j ∈ S, b j ≠ 0) → 0 < criticalTranslatedCompleteEnergy S b n := by
  filter_upwards [eventually_criticalTranslatedCompleteEnergy_coercive S 1] with n hn b hb
  obtain ⟨j, hj, hbj⟩ := hb
  have hE : 0 < ∑ i ∈ S, b i ^ 2 :=
    lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun i _ => sq_nonneg (b i)) hj)
  refine lt_of_lt_of_le ?_ (hn b)
  rw [one_mul]
  exact_mod_cast hE

end GaloisForLFunctions.ArithmeticPositivityTheory
