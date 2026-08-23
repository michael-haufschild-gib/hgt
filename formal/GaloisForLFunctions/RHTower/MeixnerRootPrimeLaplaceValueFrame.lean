import GaloisForLFunctions.RHTower.PrimeLaplaceGammaJetIncidence
import GaloisForLFunctions.RHTower.XiWeilCauchyCoreMultiplicity
import GaloisForLFunctions.RHTower.GammaMeixnerRootSeamScale
import GaloisForLFunctions.RHTower.GammaDampedPrimeLogCauchyDomain
import GaloisForLFunctions.RHTower.SquarefreeCarlemanLogExpansion
import GaloisForLFunctions.HTGeometry.MinimalCompleteSystem

/-!
# Common Gamma--Meixner prime-Laplace value frame

This module realizes the countable common prime-exponential core for all nonnegative
Gamma--Meixner times.  It identifies its Gram kernel and reflected seam values by absolutely
convergent weighted prime Dirichlet series, proves the exact finite Gram/Riesz interpolation
criterion and its sharp least constant, and packages the resulting countable criterion as an
equivalence with the Riemann hypothesis.  The final section proves the sharp obstruction to
reusing finite regular-Cauchy packets below time one.

All Hilbert spaces are represented unitarily in unweighted `lp` by multiplying coordinates by the
square root of the Meixner weight.  No assumption on Xi-zero location enters any construction.
-/

open Complex Filter Topology Set
open scoped InnerProductSpace BigOperators

noncomputable section

namespace RHTower

abbrev MeixnerPrimeHilbert := lp (fun _ : Nat.Primes => ℂ) 2

def meixnerPrimeLaplaceFeatureRaw (theta x : ℝ) (p : Nat.Primes) : ℂ :=
  (Real.sqrt (meixnerPrimeWeight theta (p : ℕ)) : ℂ) *
    ((((p : ℕ) : ℝ) ^ (-x) : ℝ) : ℂ)

theorem norm_sq_meixnerPrimeLaplaceFeatureRaw (theta x : ℝ) (p : Nat.Primes) :
    ‖meixnerPrimeLaplaceFeatureRaw theta x p‖ ^ 2 =
      meixnerPrimeWeight theta (p : ℕ) * (((p : ℕ) : ℝ) ^ (-2 * x)) := by
  rw [meixnerPrimeLaplaceFeatureRaw, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_pos (Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _), mul_pow,
    Real.sq_sqrt (meixnerPrimeWeight_pos theta _).le]
  rw [← Real.rpow_natCast ((((p : ℕ) : ℝ) ^ (-x))) 2,
    ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ ((p : ℕ) : ℝ))]
  congr 2
  push_cast
  ring

theorem summable_norm_sq_meixnerPrimeLaplaceFeatureRaw
    {theta x : ℝ} (htheta : 0 ≤ theta) (hx : 1 / 2 < x) :
    Summable (fun p : Nat.Primes => ‖meixnerPrimeLaplaceFeatureRaw theta x p‖ ^ 2) := by
  have hpow : Summable (fun p : Nat.Primes => (((p : ℕ) : ℝ) ^ (-theta - 2 * x))) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  refine Summable.of_nonneg_of_le (fun p => sq_nonneg _) (fun p => ?_)
    (hpow.mul_left (2 ^ (theta / 2)))
  rw [norm_sq_meixnerPrimeLaplaceFeatureRaw]
  have hw := meixnerPrimeWeight_le theta htheta (n := (p : ℕ)) p.2.one_lt.le
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have hsplit : ((p : ℕ) : ℝ) ^ (-theta) * ((p : ℕ) : ℝ) ^ (-2 * x) =
      ((p : ℕ) : ℝ) ^ (-theta - 2 * x) := by
    rw [← Real.rpow_add hp0]
    congr 1
    ring
  calc
    meixnerPrimeWeight theta (p : ℕ) * ((p : ℕ) : ℝ) ^ (-2 * x) ≤
        (2 ^ (theta / 2) * ((p : ℕ) : ℝ) ^ (-theta)) *
          ((p : ℕ) : ℝ) ^ (-2 * x) :=
      mul_le_mul_of_nonneg_right hw (Real.rpow_nonneg hp0.le _)
    _ = 2 ^ (theta / 2) * ((p : ℕ) : ℝ) ^ (-theta - 2 * x) := by
      rw [← hsplit]
      ring

noncomputable def meixnerPrimeLaplaceFeature
    (theta x : ℝ) (htheta : 0 ≤ theta) (hx : 1 / 2 < x) : MeixnerPrimeHilbert :=
  ⟨meixnerPrimeLaplaceFeatureRaw theta x,
    HilbertSchmidt.memℓp_of_sq
      (summable_norm_sq_meixnerPrimeLaplaceFeatureRaw htheta hx)⟩

@[simp] theorem meixnerPrimeLaplaceFeature_apply
    (theta x : ℝ) (htheta : 0 ≤ theta) (hx : 1 / 2 < x) (p : Nat.Primes) :
    meixnerPrimeLaplaceFeature theta x htheta hx p =
      meixnerPrimeLaplaceFeatureRaw theta x p := rfl

theorem LSeries_primeLaplaceCoeff_eq_tsum_primes
    (theta : ℝ) (a : Nat.Primes → ℂ) (s : ℂ) :
    LSeries (primeLaplaceCoeff theta a) s =
      ∑' p : Nat.Primes, a p * (Real.sqrt (meixnerPrimeWeight theta (p : ℕ)) : ℂ) /
        ((p : ℕ) : ℂ) ^ s := by
  classical
  have hsupp : Function.support (LSeries.term (primeLaplaceCoeff theta a) s) ⊆
      Set.range (fun p : Nat.Primes => (p : ℕ)) := by
    intro n hn
    by_contra hmem
    have hnp : ¬ n.Prime := fun hp => hmem ⟨⟨n, hp⟩, rfl⟩
    apply hn
    rcases eq_or_ne n 0 with rfl | h0
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero h0, primeLaplaceCoeff, dif_neg hnp, zero_div]
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := Subtype.coe_injective
  rw [LSeries, ← hinj.tsum_eq hsupp]
  apply tsum_congr
  intro p
  rw [LSeries.term_of_ne_zero p.2.ne_zero, primeLaplaceCoeff_prime]

theorem inner_meixnerPrimeLaplaceFeature_eq_LSeries
    {theta x : ℝ} (htheta : 0 ≤ theta) (hx : 1 / 2 < x)
    (a : MeixnerPrimeHilbert) :
    inner ℂ (meixnerPrimeLaplaceFeature theta x htheta hx) a =
      LSeries (primeLaplaceCoeff theta a) x := by
  rw [lp.inner_eq_tsum, LSeries_primeLaplaceCoeff_eq_tsum_primes]
  apply tsum_congr
  intro p
  rw [meixnerPrimeLaplaceFeature_apply, meixnerPrimeLaplaceFeatureRaw,
    RCLike.inner_apply, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have hpow : ((((p : ℕ) : ℝ) ^ (-x) : ℝ) : ℂ) =
      (((p : ℕ) : ℂ) ^ (x : ℂ))⁻¹ := by
    rw [Real.rpow_neg hp0.le, Complex.ofReal_inv,
      Complex.ofReal_cpow hp0.le]
    congr 1
  rw [hpow, inv_eq_one_div]
  ring

def meixnerPrimeLaplaceNode (n : ℕ) : ℝ := 1 + 1 / ((n : ℝ) + 1)

theorem meixnerPrimeLaplaceNode_gt_one (n : ℕ) : 1 < meixnerPrimeLaplaceNode n := by
  dsimp [meixnerPrimeLaplaceNode]
  have hpos : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
  linarith

theorem tendsto_meixnerPrimeLaplaceNode :
    Tendsto meixnerPrimeLaplaceNode atTop (nhds 1) := by
  unfold meixnerPrimeLaplaceNode
  simpa only [one_div, add_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem tendsto_meixnerPrimeLaplaceNode_complex :
    Tendsto (fun n : ℕ => (meixnerPrimeLaplaceNode n : ℂ)) atTop
      (𝓝[≠] (1 : ℂ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨(Complex.continuous_ofReal.tendsto 1).comp
    tendsto_meixnerPrimeLaplaceNode, ?_⟩
  refine Filter.Eventually.of_forall fun n hn => ?_
  have hne : meixnerPrimeLaplaceNode n ≠ 1 :=
    (meixnerPrimeLaplaceNode_gt_one n).ne'
  exact hne (ofReal_injective hn)

theorem meixnerPrimeLaplaceNode_gt_half (n : ℕ) :
    1 / 2 < meixnerPrimeLaplaceNode n :=
  lt_trans (by norm_num) (meixnerPrimeLaplaceNode_gt_one n)

noncomputable def meixnerPrimeLaplaceFrame
    (theta : ℝ) (htheta : 0 ≤ theta) : ℕ → MeixnerPrimeHilbert :=
  fun n => meixnerPrimeLaplaceFeature theta (meixnerPrimeLaplaceNode n) htheta
    (meixnerPrimeLaplaceNode_gt_half n)

theorem isCompleteSystem_meixnerPrimeLaplaceFrame
    {theta : ℝ} (htheta : 0 ≤ theta) :
    GaloisForLFunctions.HTGeometry.IsCompleteSystem ℂ
      (meixnerPrimeLaplaceFrame theta htheta) := by
  rw [GaloisForLFunctions.HTGeometry.isCompleteSystem_iff_forall_inner_eq_zero]
  intro a hann
  classical
  have ha : Summable (fun p : Nat.Primes => ‖a p‖ ^ 2) := summable_sq_lp a
  set f := primeLaplaceCoeff theta a with hf
  have habs : LSeries.abscissaOfAbsConv f ≤ (((1 - theta) / 2 : ℝ) : EReal) := by
    rw [hf]
    exact abscissaOfAbsConv_primeLaplaceCoeff_le htheta ha
  set U : Set ℂ := {s : ℂ | LSeries.abscissaOfAbsConv f < (s.re : EReal)} with hU
  set V : Set ℂ := {s : ℂ | (1 - theta) / 2 < s.re} with hV
  have hVU : V ⊆ U := by
    intro s hs
    have hlt : LSeries.abscissaOfAbsConv f < ((s.re : ℝ) : EReal) :=
      lt_of_le_of_lt habs (by exact_mod_cast hs)
    simpa [hU] using hlt
  have hana : AnalyticOnNhd ℂ (LSeries f) V :=
    (LSeries_analyticOnNhd f).mono hVU
  have hone : (1 : ℂ) ∈ V := by
    simp only [hV, mem_setOf_eq, Complex.one_re]
    linarith
  have hzeroNode : ∀ n : ℕ,
      LSeries f (meixnerPrimeLaplaceNode n : ℂ) = 0 := by
    intro n
    have hn := hann n
    rw [meixnerPrimeLaplaceFrame,
      inner_meixnerPrimeLaplaceFeature_eq_LSeries] at hn
    simpa [hf] using hn
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), LSeries f z = 0 :=
    tendsto_meixnerPrimeLaplaceNode_complex.frequently
      (Filter.Frequently.of_forall hzeroNode)
  have hzero : Set.EqOn (LSeries f) 0 V :=
    hana.eqOn_zero_of_preconnected_of_frequently_eq_zero
      (convex_halfSpace_re_gt ((1 - theta) / 2)).isPreconnected hone hfreq
  have hatTop : (fun x : ℝ => LSeries f (x : ℂ)) =ᶠ[Filter.atTop] 0 := by
    filter_upwards [Filter.eventually_gt_atTop ((1 - theta) / 2)] with y hy
    exact hzero (by simpa [hV] using hy)
  have hcoeff : ∀ n : ℕ, n ≠ 0 → f n = 0 := by
    rcases LSeries_eventually_eq_zero_iff'.mp hatTop with hzeroc | htop
    · exact hzeroc
    · exact absurd htop (by
        intro hcon
        rw [hcon] at habs
        exact absurd habs (by simp))
  apply lp.ext
  funext p
  have hp := hcoeff (p : ℕ) p.2.ne_zero
  rw [hf, primeLaplaceCoeff_prime] at hp
  have hw : ((Real.sqrt (meixnerPrimeWeight theta (p : ℕ)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (meixnerPrimeWeight_pos theta _)))
  simpa [hw] using (mul_eq_zero.mp hp)

/-! ### Exact weighted prime-zeta Gram kernel -/

def meixnerWeightedPrimeZeta (theta : ℝ) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, (meixnerPrimeWeight theta (p : ℕ) : ℂ) *
    ((p : ℕ) : ℂ) ^ (-s)

theorem inner_meixnerPrimeLaplaceFeature_eq_weightedPrimeZeta
    {theta x y : ℝ} (htheta : 0 ≤ theta) (hx : 1 / 2 < x) (hy : 1 / 2 < y) :
    inner ℂ (meixnerPrimeLaplaceFeature theta x htheta hx)
        (meixnerPrimeLaplaceFeature theta y htheta hy) =
      meixnerWeightedPrimeZeta theta (x + y) := by
  rw [lp.inner_eq_tsum, meixnerWeightedPrimeZeta]
  apply tsum_congr
  intro p
  rw [meixnerPrimeLaplaceFeature_apply, meixnerPrimeLaplaceFeature_apply,
    meixnerPrimeLaplaceFeatureRaw, meixnerPrimeLaplaceFeatureRaw,
    RCLike.inner_apply, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have hsq : ((Real.sqrt (meixnerPrimeWeight theta (p : ℕ)) : ℝ) : ℂ) ^ 2 =
      (meixnerPrimeWeight theta (p : ℕ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (meixnerPrimeWeight_pos theta _).le]
  have hxpow : ((((p : ℕ) : ℝ) ^ (-x) : ℝ) : ℂ) =
      ((p : ℕ) : ℂ) ^ (-(x : ℂ)) := by
    rw [Complex.ofReal_cpow hp0.le]
    norm_num
  have hypow : ((((p : ℕ) : ℝ) ^ (-y) : ℝ) : ℂ) =
      ((p : ℕ) : ℂ) ^ (-(y : ℂ)) := by
    rw [Complex.ofReal_cpow hp0.le]
    norm_num
  rw [hxpow, hypow]
  have hpne : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.2.ne_zero
  calc
    ((Real.sqrt (meixnerPrimeWeight theta (p : ℕ)) : ℝ) : ℂ) *
          ((p : ℕ) : ℂ) ^ (-(y : ℂ)) *
        (((Real.sqrt (meixnerPrimeWeight theta (p : ℕ)) : ℝ) : ℂ) *
          ((p : ℕ) : ℂ) ^ (-(x : ℂ))) =
        ((Real.sqrt (meixnerPrimeWeight theta (p : ℕ)) : ℝ) : ℂ) ^ 2 *
          (((p : ℕ) : ℂ) ^ (-(y : ℂ)) * ((p : ℕ) : ℂ) ^ (-(x : ℂ))) := by ring
    _ = (meixnerPrimeWeight theta (p : ℕ) : ℂ) *
          (((p : ℕ) : ℂ) ^ (-(y : ℂ)) * ((p : ℕ) : ℂ) ^ (-(x : ℂ))) := by rw [hsq]
    _ = (meixnerPrimeWeight theta (p : ℕ) : ℂ) *
          ((p : ℕ) : ℂ) ^ (-(y : ℂ) + -(x : ℂ)) := by
          rw [Complex.cpow_add _ _ hpne]
    _ = (meixnerPrimeWeight theta (p : ℕ) : ℂ) *
          ((p : ℕ) : ℂ) ^ (-((x : ℂ) + (y : ℂ))) := by
          congr 2
          ring

theorem inner_meixnerPrimeLaplaceFrame_eq_weightedPrimeZeta
    {theta : ℝ} (htheta : 0 ≤ theta) (m n : ℕ) :
    inner ℂ (meixnerPrimeLaplaceFrame theta htheta m)
        (meixnerPrimeLaplaceFrame theta htheta n) =
      meixnerWeightedPrimeZeta theta
        (meixnerPrimeLaplaceNode m + meixnerPrimeLaplaceNode n) := by
  exact inner_meixnerPrimeLaplaceFeature_eq_weightedPrimeZeta htheta
    (meixnerPrimeLaplaceNode_gt_half m) (meixnerPrimeLaplaceNode_gt_half n)

/-! ### Ordinary prime-zeta binomial expansion

The positive coefficient below is `(theta / 2)_k / k!`. The signed binomial series is
absolutely summable at every prime because `p⁻⁴ ≤ 1/16`. This uniform majorant supplies the
Tonelli interchange behind exact ordinary-prime-zeta and prime-zeta-derivative expansions.
-/

def meixnerPrimeBinomialCoeff (theta : ℝ) (k : ℕ) : ℝ :=
  Ring.choose (theta / 2 + k - 1) k

theorem meixnerPrimeBinomialCoeff_pos {theta : ℝ} (htheta : 0 < theta) (k : ℕ) :
    0 < meixnerPrimeBinomialCoeff theta k := by
  rw [meixnerPrimeBinomialCoeff, Ring.choose_eq_smul, smul_eq_mul,
    Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval]
  exact mul_pos (inv_pos.mpr (by positivity))
    (ascPochhammer_pos k _ (by
      linarith))

theorem meixnerPrimeBinomialCoeff_eq_pochhammer (theta : ℝ) (k : ℕ) :
    meixnerPrimeBinomialCoeff theta k =
      (ascPochhammer ℝ k).eval (theta / 2) / (k.factorial : ℝ) := by
  rw [meixnerPrimeBinomialCoeff, Ring.choose_eq_smul, smul_eq_mul,
    Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval]
  have harg : theta / 2 + (k : ℝ) - 1 - k + 1 = theta / 2 := by
    ring
  rw [harg]
  rw [div_eq_mul_inv]
  ring

theorem hasSum_meixnerPrimeBinomial (theta : ℝ) {x : ℝ}
    (hx : |x| < 1) :
    HasSum (fun k : ℕ => (-1 : ℝ) ^ k * meixnerPrimeBinomialCoeff theta k * x ^ k)
      ((1 + x) ^ (-theta / 2)) := by
  have hball := Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := -theta / 2)
  have hmem : x ∈ Metric.eball (0 : ℝ) 1 := by
    show edist x (0 : ℝ) < 1
    rw [edist_dist, Real.dist_eq, sub_zero]
    exact ENNReal.ofReal_lt_one.mpr hx
  have hs := hball.hasSum hmem
  simpa only [zero_add] using hs.congr_fun (fun k => by
    rw [binomialSeries_apply]
    have hp : (List.ofFn (fun _ : Fin k => x)).prod = x ^ k := by simp
    rw [hp, smul_eq_mul]
    change (-1 : ℝ) ^ k * Ring.choose (theta / 2 + k - 1) k * x ^ k =
      Ring.choose (-theta / 2) k * x ^ k
    rw [show -theta / 2 = -(theta / 2) by ring, Ring.choose_neg]
    rw [@Units.smul_def ℤ ℝ _ _, ← Int.cast_smul_eq_zsmul ℝ, smul_eq_mul,
      Int.coe_negOnePow]
    simp)

theorem hasSum_meixnerPrimeBinomial_abs (theta : ℝ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun k : ℕ => meixnerPrimeBinomialCoeff theta k * q ^ k)
      ((1 - q) ^ (-theta / 2)) := by
  have hs := hasSum_meixnerPrimeBinomial theta (x := -q) (by simpa [abs_of_nonneg hq0] using hq1)
  rw [show (1 : ℝ) + -q = 1 - q by ring] at hs
  exact hs.congr_fun (fun k => by
    have hsign : (-1 : ℝ) ^ k * (-1) ^ k = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    calc
      meixnerPrimeBinomialCoeff theta k * q ^ k =
          ((-1 : ℝ) ^ k * (-1) ^ k) *
            (meixnerPrimeBinomialCoeff theta k * q ^ k) := by rw [hsign, one_mul]
      _ = (-1 : ℝ) ^ k * meixnerPrimeBinomialCoeff theta k * (-q) ^ k := by
        rw [neg_pow]
        ring)

def meixnerPrimeZetaDoubleTerm (theta : ℝ) (s : ℂ) (q : Nat.Primes × ℕ) : ℂ :=
  ((2 ^ (theta / 2) : ℝ) : ℂ) *
    (((-1 : ℝ) ^ q.2 * meixnerPrimeBinomialCoeff theta q.2 : ℝ) : ℂ) *
      coronaPrimeEigenvalue (s + (theta : ℂ)) q.1 *
        (((((q.1 : ℕ) : ℝ) ^ (-(4 : ℝ))) ^ q.2 : ℝ) : ℂ)

theorem norm_meixnerPrimeZetaDoubleTerm_le {theta : ℝ} (htheta : 0 < theta) (s : ℂ)
    (q : Nat.Primes × ℕ) :
    ‖meixnerPrimeZetaDoubleTerm theta s q‖ ≤
      2 ^ (theta / 2) *
        (((q.1 : ℕ) : ℝ) ^ (-(s.re + theta)) *
          (meixnerPrimeBinomialCoeff theta q.2 * (1 / 16 : ℝ) ^ q.2)) := by
  rcases q with ⟨p, k⟩
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
  have hcpos := meixnerPrimeBinomialCoeff_pos htheta k
  rw [meixnerPrimeZetaDoubleTerm, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _),
    abs_mul, abs_pow, abs_neg, abs_of_pos hcpos,
    Real.norm_eq_abs, abs_of_pos (by positivity),
    norm_coronaPrimeEigenvalue]
  simp only [one_pow, one_mul,
    Complex.add_re, Complex.ofReal_re]
  rw [abs_of_nonneg (by positivity : 0 ≤ (((p : ℕ) : ℝ) ^ (-(4 : ℝ))) ^ k)]
  have hquart : ((p : ℕ) : ℝ) ^ (-(4 : ℝ)) ≤ (1 / 16 : ℝ) := by
    have h := Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num : (-(4 : ℝ)) ≤ 0)
    have htwo : (2 : ℝ) ^ (-(4 : ℝ)) = 1 / 16 := by
      rw [show (-(4 : ℝ)) = ((-4 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
      norm_num
    rwa [htwo] at h
  calc
    2 ^ (theta / 2) * meixnerPrimeBinomialCoeff theta k *
        ((p : ℕ) : ℝ) ^ (-(s.re + theta)) *
          (((p : ℕ) : ℝ) ^ (-(4 : ℝ))) ^ k =
      2 ^ (theta / 2) * (((p : ℕ) : ℝ) ^ (-(s.re + theta)) *
        (meixnerPrimeBinomialCoeff theta k *
          (((p : ℕ) : ℝ) ^ (-(4 : ℝ))) ^ k)) := by ring
    _ ≤ 2 ^ (theta / 2) * (((p : ℕ) : ℝ) ^ (-(s.re + theta)) *
        (meixnerPrimeBinomialCoeff theta k * (1 / 16 : ℝ) ^ k)) := by
      gcongr

theorem summable_meixnerPrimeZetaDoubleTerm {theta : ℝ} (htheta : 0 < theta) {s : ℂ}
    (hs : 1 < theta + s.re) : Summable (meixnerPrimeZetaDoubleTerm theta s) := by
  have hp : Summable (fun p : Nat.Primes =>
      ((p : ℕ) : ℝ) ^ (-(s.re + theta))) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  have hg : Summable (fun k : ℕ =>
      meixnerPrimeBinomialCoeff theta k * (1 / 16 : ℝ) ^ k) :=
    (hasSum_meixnerPrimeBinomial_abs theta (q := 1 / 16) (by norm_num) (by norm_num)).summable
  have hprod : Summable (fun q : Nat.Primes × ℕ =>
      ((q.1 : ℕ) : ℝ) ^ (-(s.re + theta)) *
        (meixnerPrimeBinomialCoeff theta q.2 * (1 / 16 : ℝ) ^ q.2)) :=
    Summable.mul_of_nonneg hp hg
      (fun _ => Real.rpow_nonneg (by positivity) _)
      (fun k => mul_nonneg (meixnerPrimeBinomialCoeff_pos htheta k).le (by positivity))
  exact Summable.of_norm_bounded (hprod.mul_left (2 ^ (theta / 2)))
    (norm_meixnerPrimeZetaDoubleTerm_le htheta s)

theorem testDouble_hasSum_column (theta : ℝ) (s : ℂ) (p : Nat.Primes) :
    HasSum (fun k : ℕ => meixnerPrimeZetaDoubleTerm theta s (p, k))
      ((meixnerPrimeWeight theta (p : ℕ) : ℂ) * coronaPrimeEigenvalue s p) := by
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
  let q : ℝ := ((p : ℕ) : ℝ) ^ (-(4 : ℝ))
  have hq0 : 0 < q := Real.rpow_pos_of_pos hp0 _
  have hq16 : q ≤ (1 / 16 : ℝ) := by
    have h := Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num : (-(4 : ℝ)) ≤ 0)
    have htwo : (2 : ℝ) ^ (-(4 : ℝ)) = 1 / 16 := by
      rw [show (-(4 : ℝ)) = ((-4 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
      norm_num
    rwa [htwo] at h
  have hsreal := hasSum_meixnerPrimeBinomial theta (x := q) (by
    rw [abs_of_pos hq0]
    linarith)
  have hscomplex : HasSum
      (fun k : ℕ => ((((-1 : ℝ) ^ k * meixnerPrimeBinomialCoeff theta k * q ^ k) : ℝ) : ℂ))
      ((((1 + q) ^ (-theta / 2) : ℝ) : ℂ)) :=
    Complex.hasSum_ofReal.mpr hsreal
  have hmul := hscomplex.mul_left
    (((2 ^ (theta / 2) : ℝ) : ℂ) *
      coronaPrimeEigenvalue (s + (theta : ℂ)) p)
  have hpC : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hshift : coronaPrimeEigenvalue (s + (theta : ℂ)) p =
      ((((p : ℕ) : ℝ) ^ (-theta) : ℝ) : ℂ) * coronaPrimeEigenvalue s p := by
    unfold coronaPrimeEigenvalue
    rw [
      show -(s + (theta : ℂ)) = (-theta : ℂ) + -s by ring,
      Complex.cpow_add _ _ hpC, Complex.ofReal_cpow hp0.le]
    push_cast
    rfl
  have hvalue :
      (((2 ^ (theta / 2) : ℝ) : ℂ) *
          coronaPrimeEigenvalue (s + (theta : ℂ)) p) *
            ((((1 + q) ^ (-theta / 2) : ℝ) : ℂ)) =
        (meixnerPrimeWeight theta (p : ℕ) : ℂ) * coronaPrimeEigenvalue s p := by
    rw [meixnerPrimeWeight_eq p.2.one_lt.le, hshift]
    dsimp only [q]
    push_cast
    ring
  rw [← hvalue]
  exact hmul.congr_fun (fun k => by
    dsimp [meixnerPrimeZetaDoubleTerm, q]
    push_cast
    ring)

theorem testDouble_hasSum_row {theta : ℝ} {s : ℂ}
    (hs : 1 < theta + s.re) (k : ℕ) :
    HasSum (fun p : Nat.Primes => meixnerPrimeZetaDoubleTerm theta s (p, k))
      ((((2 ^ (theta / 2) : ℝ) * (-1 : ℝ) ^ k *
          meixnerPrimeBinomialCoeff theta k : ℝ) : ℂ) *
        coronaPrimeZeta
          (s + (theta : ℂ) + ((4 * k : ℕ) : ℂ))) := by
  have harg : 1 < (s + (theta : ℂ) + ((4 * k : ℕ) : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.natCast_re]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hsum := (summable_coronaPrimeEigenvalue harg).hasSum.mul_left
    ((((2 ^ (theta / 2) : ℝ) * (-1 : ℝ) ^ k *
      meixnerPrimeBinomialCoeff theta k : ℝ) : ℂ))
  rw [coronaPrimeZeta]
  exact hsum.congr_fun (fun p => by
    have hpC : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    change ((2 ^ (theta / 2) : ℝ) : ℂ) *
        (((-1 : ℝ) ^ k * meixnerPrimeBinomialCoeff theta k : ℝ) : ℂ) *
          coronaPrimeEigenvalue (s + (theta : ℂ)) p *
            (((((p : ℕ) : ℝ) ^ (-(4 : ℝ))) ^ k : ℝ) : ℂ) =
      (((2 ^ (theta / 2) : ℝ) * (-1 : ℝ) ^ k *
          meixnerPrimeBinomialCoeff theta k : ℝ) : ℂ) *
        coronaPrimeEigenvalue
          (s + (theta : ℂ) + ((4 * k : ℕ) : ℂ)) p
    unfold coronaPrimeEigenvalue
    rw [
      show -(s + (theta : ℂ) + ((4 * k : ℕ) : ℂ)) =
        -(s + (theta : ℂ)) + (-((4 * k : ℕ) : ℂ)) by ring,
      Complex.cpow_add _ _ hpC]
    have hfour : ((p : ℕ) : ℂ) ^ (-((4 * k : ℕ) : ℂ)) =
        (((((p : ℕ) : ℝ) ^ (-(4 : ℝ))) ^ k : ℝ) : ℂ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le,
        Complex.ofReal_cpow hp0.le]
      congr 2
      push_cast
      ring
    rw [hfour]
    push_cast
    ring)

theorem meixnerWeightedPrimeZeta_eq_binomialPrimeZeta
    {theta : ℝ} (htheta : 0 < theta) {s : ℂ} (hs : 1 < theta + s.re) :
    meixnerWeightedPrimeZeta theta s =
      ((2 ^ (theta / 2) : ℝ) : ℂ) *
        ∑' k : ℕ, (((-1 : ℝ) ^ k * meixnerPrimeBinomialCoeff theta k : ℝ) : ℂ) *
          coronaPrimeZeta (s + (theta : ℂ) + ((4 * k : ℕ) : ℂ)) := by
  have hdouble := summable_meixnerPrimeZetaDoubleTerm htheta hs
  have hdouble' : Summable (Function.uncurry
      (fun p : Nat.Primes => fun k : ℕ => meixnerPrimeZetaDoubleTerm theta s (p, k))) := by
    exact hdouble.congr (fun q => by
      rcases q with ⟨p, k⟩
      rfl)
  calc
    meixnerWeightedPrimeZeta theta s =
        ∑' p : Nat.Primes, ∑' k : ℕ, meixnerPrimeZetaDoubleTerm theta s (p, k) := by
      unfold meixnerWeightedPrimeZeta
      apply tsum_congr
      intro p
      exact (testDouble_hasSum_column theta s p).tsum_eq.symm
    _ = ∑' k : ℕ, ∑' p : Nat.Primes, meixnerPrimeZetaDoubleTerm theta s (p, k) := by
      exact (Summable.tsum_comm hdouble').symm
    _ = ∑' k : ℕ, ((((2 ^ (theta / 2) : ℝ) * (-1 : ℝ) ^ k *
          meixnerPrimeBinomialCoeff theta k : ℝ) : ℂ) *
        coronaPrimeZeta (s + (theta : ℂ) + ((4 * k : ℕ) : ℂ))) := by
      apply tsum_congr
      intro k
      exact (testDouble_hasSum_row hs k).tsum_eq
    _ = ((2 ^ (theta / 2) : ℝ) : ℂ) *
        ∑' k : ℕ, (((-1 : ℝ) ^ k * meixnerPrimeBinomialCoeff theta k : ℝ) : ℂ) *
          coronaPrimeZeta (s + (theta : ℂ) + ((4 * k : ℕ) : ℂ)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      push_cast
      ring

def meixnerPrimeZetaLogDoubleTerm (theta : ℝ) (s : ℂ) (q : Nat.Primes × ℕ) : ℂ :=
  (Real.log ((q.1 : ℕ) : ℝ) : ℂ) * meixnerPrimeZetaDoubleTerm theta s q

theorem summable_meixnerPrimeZetaLogDoubleTerm {theta : ℝ} (htheta : 0 < theta) {s : ℂ}
    (hs : 1 < theta + s.re) : Summable (meixnerPrimeZetaLogDoubleTerm theta s) := by
  have hp : Summable (fun p : Nat.Primes =>
      |Real.log ((p : ℕ) : ℝ)| * ((p : ℕ) : ℝ) ^ (-(s.re + theta))) := by
    have h := (summable_abs_log_natCast_pow_mul_rpow_neg
      1 (s.re + theta) (by linarith)).comp_injective
        (i := fun p : Nat.Primes => (p : ℕ)) Subtype.coe_injective
    exact h.congr (fun p => by simp only [Function.comp_apply, pow_one])
  have hg : Summable (fun k : ℕ =>
      meixnerPrimeBinomialCoeff theta k * (1 / 16 : ℝ) ^ k) :=
    (hasSum_meixnerPrimeBinomial_abs theta (q := 1 / 16) (by norm_num) (by norm_num)).summable
  have hprod : Summable (fun q : Nat.Primes × ℕ =>
      (|Real.log ((q.1 : ℕ) : ℝ)| * ((q.1 : ℕ) : ℝ) ^ (-(s.re + theta))) *
        (meixnerPrimeBinomialCoeff theta q.2 * (1 / 16 : ℝ) ^ q.2)) :=
    Summable.mul_of_nonneg hp hg
      (fun p => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (by positivity) _))
      (fun k => mul_nonneg (meixnerPrimeBinomialCoeff_pos htheta k).le (by positivity))
  apply Summable.of_norm_bounded (hprod.mul_left (2 ^ (theta / 2)))
  rintro ⟨p, k⟩
  rw [meixnerPrimeZetaLogDoubleTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |Real.log ((p : ℕ) : ℝ)| * ‖meixnerPrimeZetaDoubleTerm theta s (p, k)‖ ≤
        |Real.log ((p : ℕ) : ℝ)| *
          (2 ^ (theta / 2) * (((p : ℕ) : ℝ) ^ (-(s.re + theta)) *
            (meixnerPrimeBinomialCoeff theta k * (1 / 16 : ℝ) ^ k))) :=
      mul_le_mul_of_nonneg_left (norm_meixnerPrimeZetaDoubleTerm_le htheta s (p, k)) (abs_nonneg _)
    _ = 2 ^ (theta / 2) *
        ((|Real.log ((p : ℕ) : ℝ)| * ((p : ℕ) : ℝ) ^ (-(s.re + theta))) *
          (meixnerPrimeBinomialCoeff theta k * (1 / 16 : ℝ) ^ k)) := by ring

theorem testLogDouble_hasSum_column (theta : ℝ) (s : ℂ) (p : Nat.Primes) :
    HasSum (fun k : ℕ => meixnerPrimeZetaLogDoubleTerm theta s (p, k))
      ((meixnerPrimeWeight theta (p : ℕ) : ℂ) *
        (Real.log ((p : ℕ) : ℝ) : ℂ) * coronaPrimeEigenvalue s p) := by
  have h := (testDouble_hasSum_column theta s p).mul_left
    (Real.log ((p : ℕ) : ℝ) : ℂ)
  rw [show (meixnerPrimeWeight theta (p : ℕ) : ℂ) *
      (Real.log ((p : ℕ) : ℝ) : ℂ) * coronaPrimeEigenvalue s p =
    (Real.log ((p : ℕ) : ℝ) : ℂ) *
      ((meixnerPrimeWeight theta (p : ℕ) : ℂ) * coronaPrimeEigenvalue s p) by ring]
  simpa only [meixnerPrimeZetaLogDoubleTerm] using h

theorem testLogDouble_hasSum_row {theta : ℝ} {s : ℂ}
    (hs : 1 < theta + s.re) (k : ℕ) :
    HasSum (fun p : Nat.Primes => meixnerPrimeZetaLogDoubleTerm theta s (p, k))
      ((((2 ^ (theta / 2) : ℝ) * (-1 : ℝ) ^ k *
          meixnerPrimeBinomialCoeff theta k : ℝ) : ℂ) *
        (-deriv coronaPrimeZeta
          (s + (theta : ℂ) + ((4 * k : ℕ) : ℂ)))) := by
  have harg : 1 < (s + (theta : ℂ) + ((4 * k : ℕ) : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.natCast_re]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hsum := (hasSum_neg_deriv_coronaPrimeZeta harg).mul_left
    ((((2 ^ (theta / 2) : ℝ) * (-1 : ℝ) ^ k *
      meixnerPrimeBinomialCoeff theta k : ℝ) : ℂ))
  exact hsum.congr_fun (fun p => by
    have hpC : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    change (Real.log ((p : ℕ) : ℝ) : ℂ) *
        (((2 ^ (theta / 2) : ℝ) : ℂ) *
          (((-1 : ℝ) ^ k * meixnerPrimeBinomialCoeff theta k : ℝ) : ℂ) *
            coronaPrimeEigenvalue (s + (theta : ℂ)) p *
              (((((p : ℕ) : ℝ) ^ (-(4 : ℝ))) ^ k : ℝ) : ℂ)) =
      (((2 ^ (theta / 2) : ℝ) * (-1 : ℝ) ^ k *
          meixnerPrimeBinomialCoeff theta k : ℝ) : ℂ) *
        ((Real.log ((p : ℕ) : ℝ) : ℂ) *
          coronaPrimeEigenvalue
            (s + (theta : ℂ) + ((4 * k : ℕ) : ℂ)) p)
    unfold coronaPrimeEigenvalue
    rw [show -(s + (theta : ℂ) + ((4 * k : ℕ) : ℂ)) =
        -(s + (theta : ℂ)) + (-((4 * k : ℕ) : ℂ)) by ring,
      Complex.cpow_add _ _ hpC]
    have hfour : ((p : ℕ) : ℂ) ^ (-((4 * k : ℕ) : ℂ)) =
        (((((p : ℕ) : ℝ) ^ (-(4 : ℝ))) ^ k : ℝ) : ℂ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le,
        Complex.ofReal_cpow hp0.le]
      congr 2
      push_cast
      ring
    rw [hfour]
    push_cast
    ring)

theorem primeSeamTransform_eq_binomialPrimeZetaDeriv
    {theta : ℝ} (htheta : 0 < theta) {s : ℂ} (hs : 1 < theta + s.re) :
    primeSeamTransform theta s =
      ((2 ^ (theta / 2) : ℝ) : ℂ) *
        ∑' k : ℕ, (((-1 : ℝ) ^ k * meixnerPrimeBinomialCoeff theta k : ℝ) : ℂ) *
          (-deriv coronaPrimeZeta
            (s + (theta : ℂ) + ((4 * k : ℕ) : ℂ))) := by
  have hdouble := summable_meixnerPrimeZetaLogDoubleTerm htheta hs
  have hdouble' : Summable (Function.uncurry
      (fun p : Nat.Primes => fun k : ℕ => meixnerPrimeZetaLogDoubleTerm theta s (p, k))) := by
    exact hdouble.congr (fun q => by
      rcases q with ⟨p, k⟩
      rfl)
  calc
    primeSeamTransform theta s =
        ∑' p : Nat.Primes, ∑' k : ℕ, meixnerPrimeZetaLogDoubleTerm theta s (p, k) := by
      unfold primeSeamTransform
      apply tsum_congr
      intro p
      exact (testLogDouble_hasSum_column theta s p).tsum_eq.symm
    _ = ∑' k : ℕ, ∑' p : Nat.Primes, meixnerPrimeZetaLogDoubleTerm theta s (p, k) := by
      exact (Summable.tsum_comm hdouble').symm
    _ = ∑' k : ℕ, ((((2 ^ (theta / 2) : ℝ) * (-1 : ℝ) ^ k *
          meixnerPrimeBinomialCoeff theta k : ℝ) : ℂ) *
        (-deriv coronaPrimeZeta
          (s + (theta : ℂ) + ((4 * k : ℕ) : ℂ)))) := by
      apply tsum_congr
      intro k
      exact (testLogDouble_hasSum_row hs k).tsum_eq
    _ = ((2 ^ (theta / 2) : ℝ) : ℂ) *
        ∑' k : ℕ, (((-1 : ℝ) ^ k * meixnerPrimeBinomialCoeff theta k : ℝ) : ℂ) *
          (-deriv coronaPrimeZeta
            (s + (theta : ℂ) + ((4 * k : ℕ) : ℂ))) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      push_cast
      ring

/-! ### Exact reflected seam values -/

def meixnerPrimeSeamSummand (theta : ℝ) (w : ℂ) (p : Nat.Primes) : ℂ :=
  (meixnerPrimeWeight theta (p : ℕ) : ℂ) *
    (Real.log ((p : ℕ) : ℝ) : ℂ) * ((p : ℕ) : ℂ) ^ (-w)

theorem summable_meixnerPrimeSeamSummand {theta : ℝ} (htheta : 0 ≤ theta)
    {w : ℂ} (hw : 1 < theta + w.re) :
    Summable (meixnerPrimeSeamSummand theta w) := by
  have hbase : Summable (fun p : Nat.Primes =>
      |Real.log ((p : ℕ) : ℝ)| * ((p : ℕ) : ℝ) ^ (-(theta + w.re))) :=
    by
      have h :=
        (summable_abs_log_natCast_pow_mul_rpow_neg 1 (theta + w.re) hw).comp_injective
          (i := fun p : Nat.Primes => (p : ℕ)) Subtype.coe_injective
      exact h.congr (fun p => by simp only [Function.comp_apply, pow_one])
  refine Summable.of_norm_bounded (hbase.mul_left (2 ^ (theta / 2))) fun p => ?_
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have hwgt := meixnerPrimeWeight_le theta htheta
    (n := (p : ℕ)) p.2.one_lt.le
  rw [meixnerPrimeSeamSummand, norm_mul, norm_mul, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (meixnerPrimeWeight_pos theta _),
    Complex.norm_natCast_cpow_of_pos p.2.pos]
  have hsplit : ((p : ℕ) : ℝ) ^ (-theta) * ((p : ℕ) : ℝ) ^ (-w.re) =
      ((p : ℕ) : ℝ) ^ (-(theta + w.re)) := by
    rw [← Real.rpow_add hp0]
    congr 1
    ring
  calc
    meixnerPrimeWeight theta (p : ℕ) * |Real.log ((p : ℕ) : ℝ)| *
        ((p : ℕ) : ℝ) ^ (-w.re) ≤
      (2 ^ (theta / 2) * ((p : ℕ) : ℝ) ^ (-theta)) *
        |Real.log ((p : ℕ) : ℝ)| * ((p : ℕ) : ℝ) ^ (-w.re) := by
          gcongr
    _ = 2 ^ (theta / 2) *
        (|Real.log ((p : ℕ) : ℝ)| * ((p : ℕ) : ℝ) ^ (-(theta + w.re))) := by
          rw [← hsplit]
          ring

def meixnerPrimeSeamCoeff (theta : ℝ) (rho : ℂ) (n : ℕ) : ℂ :=
  if _h : n.Prime then
    (meixnerPrimeWeight theta n : ℂ) *
      (starRingEnd ℂ) (orbitwiseNatPrimeSeamCharge n rho)
  else 0

@[simp] theorem meixnerPrimeSeamCoeff_zero (theta : ℝ) (rho : ℂ) :
    meixnerPrimeSeamCoeff theta rho 0 = 0 := by
  simp [meixnerPrimeSeamCoeff, Nat.not_prime_zero]

theorem meixnerPrimeSeamCoeff_prime (theta : ℝ) (rho : ℂ) (p : Nat.Primes) :
    meixnerPrimeSeamCoeff theta rho (p : ℕ) =
      (meixnerPrimeWeight theta (p : ℕ) : ℂ) *
        (starRingEnd ℂ) (orbitwiseNatPrimeSeamCharge (p : ℕ) rho) := by
  rw [meixnerPrimeSeamCoeff, dif_pos p.2]

theorem LSeries_meixnerPrimeSeamCoeff_eq_tsum_primes
    (theta : ℝ) (rho z : ℂ) :
    LSeries (meixnerPrimeSeamCoeff theta rho) z =
      ∑' p : Nat.Primes, meixnerPrimeSeamCoeff theta rho (p : ℕ) /
        ((p : ℕ) : ℂ) ^ z := by
  classical
  have hsupp : Function.support (LSeries.term (meixnerPrimeSeamCoeff theta rho) z) ⊆
      Set.range (fun p : Nat.Primes => (p : ℕ)) := by
    intro n hn
    by_contra hmem
    have hnp : ¬ n.Prime := fun hp => hmem ⟨⟨n, hp⟩, rfl⟩
    apply hn
    rcases eq_or_ne n 0 with rfl | h0
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero h0, meixnerPrimeSeamCoeff, dif_neg hnp, zero_div]
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := Subtype.coe_injective
  rw [LSeries, ← hinj.tsum_eq hsupp]
  apply tsum_congr
  intro p
  rw [LSeries.term_of_ne_zero p.2.ne_zero]

def meixnerPrimeSeamValue (theta : ℝ) (rho z : ℂ) : ℂ :=
  LSeries (meixnerPrimeSeamCoeff theta rho) z

theorem star_natPrime_cpow_neg (p : Nat.Primes) (w : ℂ) :
    (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-w)) =
      ((p : ℕ) : ℂ) ^ (-((starRingEnd ℂ) w)) := by
  have harg : (((p : ℕ) : ℂ)).arg ≠ Real.pi := by
    rw [show ((p : ℕ) : ℂ) = ((((p : ℕ) : ℝ)) : ℂ) by norm_num,
      Complex.arg_ofReal_of_nonneg (by positivity)]
    exact ne_of_lt Real.pi_pos
  have h := Complex.cpow_conj (((p : ℕ) : ℂ)) (-w) harg
  rw [show (starRingEnd ℂ) (((p : ℕ) : ℂ)) = ((p : ℕ) : ℂ) by simp] at h
  rw [← h, map_neg]

theorem star_orbitwiseNatPrimeSeamCharge (p : Nat.Primes) (rho : ℂ) :
    (starRingEnd ℂ) (orbitwiseNatPrimeSeamCharge (p : ℕ) rho) =
      (Real.log ((p : ℕ) : ℝ) : ℂ) *
        (((p : ℕ) : ℂ) ^ (-rho) -
          ((p : ℕ) : ℂ) ^ (-(1 - (starRingEnd ℂ) rho))) := by
  rw [orbitwiseNatPrimeSeamCharge, orbitwiseScaleSeamCharge,
    show ((((p : ℕ) : ℝ)) : ℂ) = ((p : ℕ) : ℂ) by norm_num,
    map_mul, Complex.conj_ofReal, map_sub,
    star_natPrime_cpow_neg, star_natPrime_cpow_neg]
  simp

theorem LSeries_term_meixnerPrimeSeamCoeff_prime
    (theta : ℝ) (rho z : ℂ) (p : Nat.Primes) :
    LSeries.term (meixnerPrimeSeamCoeff theta rho) z (p : ℕ) =
      meixnerPrimeSeamSummand theta (z + rho) p -
        meixnerPrimeSeamSummand theta (z + 1 - (starRingEnd ℂ) rho) p := by
  rw [LSeries.term_of_ne_zero p.2.ne_zero, meixnerPrimeSeamCoeff_prime,
    star_orbitwiseNatPrimeSeamCharge]
  dsimp [meixnerPrimeSeamSummand]
  have hpne : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.2.ne_zero
  calc
    (meixnerPrimeWeight theta (p : ℕ) : ℂ) *
          ((Real.log ((p : ℕ) : ℝ) : ℂ) *
            (((p : ℕ) : ℂ) ^ (-rho) -
              ((p : ℕ) : ℂ) ^ (-(1 - (starRingEnd ℂ) rho)))) /
        ((p : ℕ) : ℂ) ^ z =
      (meixnerPrimeWeight theta (p : ℕ) : ℂ) *
          (Real.log ((p : ℕ) : ℝ) : ℂ) *
            (((p : ℕ) : ℂ) ^ (-rho) / ((p : ℕ) : ℂ) ^ z) -
        (meixnerPrimeWeight theta (p : ℕ) : ℂ) *
          (Real.log ((p : ℕ) : ℝ) : ℂ) *
            (((p : ℕ) : ℂ) ^ (-(1 - (starRingEnd ℂ) rho)) /
              ((p : ℕ) : ℂ) ^ z) := by ring
    _ = (meixnerPrimeWeight theta (p : ℕ) : ℂ) *
          (Real.log ((p : ℕ) : ℝ) : ℂ) * ((p : ℕ) : ℂ) ^ (-rho - z) -
        (meixnerPrimeWeight theta (p : ℕ) : ℂ) *
          (Real.log ((p : ℕ) : ℝ) : ℂ) *
            ((p : ℕ) : ℂ) ^ (-(1 - (starRingEnd ℂ) rho) - z) := by
          rw [Complex.cpow_sub _ _ hpne, Complex.cpow_sub _ _ hpne]
    _ = (meixnerPrimeWeight theta (p : ℕ) : ℂ) *
          (Real.log ((p : ℕ) : ℝ) : ℂ) * ((p : ℕ) : ℂ) ^ (-(z + rho)) -
        (meixnerPrimeWeight theta (p : ℕ) : ℂ) *
          (Real.log ((p : ℕ) : ℝ) : ℂ) *
            ((p : ℕ) : ℂ) ^ (-(z + 1 - (starRingEnd ℂ) rho)) := by
          congr 2
          all_goals ring

theorem lSeriesSummable_meixnerPrimeSeamCoeff
    {theta : ℝ} (htheta : 0 ≤ theta) {rho z : ℂ}
    (hleft : 1 < theta + (z + rho).re)
    (hright : 1 < theta + (z + 1 - (starRingEnd ℂ) rho).re) :
    LSeriesSummable (meixnerPrimeSeamCoeff theta rho) z := by
  have hs1 := summable_meixnerPrimeSeamSummand htheta hleft
  have hs2 := summable_meixnerPrimeSeamSummand htheta hright
  have hprime : Summable (fun p : Nat.Primes =>
      LSeries.term (meixnerPrimeSeamCoeff theta rho) z (p : ℕ)) :=
    (hs1.sub hs2).congr (fun p =>
      (LSeries_term_meixnerPrimeSeamCoeff_prime theta rho z p).symm)
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := Subtype.coe_injective
  have hzero : ∀ n : ℕ, n ∉ Set.range (fun p : Nat.Primes => (p : ℕ)) →
      LSeries.term (meixnerPrimeSeamCoeff theta rho) z n = 0 := by
    intro n hn
    have hnp : ¬ n.Prime := fun hp => hn ⟨⟨n, hp⟩, rfl⟩
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hn0, meixnerPrimeSeamCoeff, dif_neg hnp, zero_div]
  exact (hinj.summable_iff hzero).mp hprime

theorem abscissaOfAbsConv_meixnerPrimeSeamCoeff_lt_one
    {theta : ℝ} (htheta : 0 < theta) {rho : ℂ}
    (hrho : 0 < rho.re ∧ rho.re < 1) :
    LSeries.abscissaOfAbsConv (meixnerPrimeSeamCoeff theta rho) < (1 : EReal) := by
  let delta : ℝ := min (theta + rho.re) (theta + 1 - rho.re)
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min (by linarith) (by linarith)
  let c : ℝ := 1 - delta / 2
  have hc : c < 1 := by dsimp [c]; linarith
  have hsum : LSeriesSummable (meixnerPrimeSeamCoeff theta rho) (c : ℂ) := by
    apply lSeriesSummable_meixnerPrimeSeamCoeff htheta.le
    · simp only [Complex.add_re, Complex.ofReal_re]
      have hle := min_le_left (theta + rho.re) (theta + 1 - rho.re)
      dsimp [c, delta]
      dsimp [delta] at hle hdelta
      linarith
    · have hcre : ((starRingEnd ℂ) rho).re = rho.re := Complex.conj_re rho
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
        Complex.one_re, hcre]
      have hle := min_le_right (theta + rho.re) (theta + 1 - rho.re)
      dsimp [c, delta]
      dsimp [delta] at hle hdelta
      linarith
  exact lt_of_le_of_lt hsum.abscissaOfAbsConv_le (by exact_mod_cast hc)

def meixnerPrimeSeamAbscissaWitness (theta : ℝ) (rho : ℂ) : ℝ :=
  1 - min (theta + rho.re) (theta + 1 - rho.re) / 2

theorem meixnerPrimeSeamAbscissaWitness_lt_one
    {theta : ℝ} (htheta : 0 < theta) {rho : ℂ}
    (hrho : 0 < rho.re ∧ rho.re < 1) :
    meixnerPrimeSeamAbscissaWitness theta rho < 1 := by
  rw [meixnerPrimeSeamAbscissaWitness]
  have : 0 < min (theta + rho.re) (theta + 1 - rho.re) :=
    lt_min (by linarith) (by linarith)
  linarith

theorem abscissaOfAbsConv_meixnerPrimeSeamCoeff_le_witness
    {theta : ℝ} (htheta : 0 < theta) {rho : ℂ}
    (hrho : 0 < rho.re ∧ rho.re < 1) :
    LSeries.abscissaOfAbsConv (meixnerPrimeSeamCoeff theta rho) ≤
      (meixnerPrimeSeamAbscissaWitness theta rho : EReal) := by
  have hs : LSeriesSummable (meixnerPrimeSeamCoeff theta rho)
      (meixnerPrimeSeamAbscissaWitness theta rho : ℂ) := by
    apply lSeriesSummable_meixnerPrimeSeamCoeff htheta.le
    · simp only [Complex.add_re, Complex.ofReal_re]
      rw [meixnerPrimeSeamAbscissaWitness]
      have hdelta : 0 < min (theta + rho.re) (theta + 1 - rho.re) :=
        lt_min (by linarith) (by linarith)
      have hle := min_le_left (theta + rho.re) (theta + 1 - rho.re)
      linarith
    · have hcre : ((starRingEnd ℂ) rho).re = rho.re := Complex.conj_re rho
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
        Complex.one_re, hcre]
      rw [meixnerPrimeSeamAbscissaWitness]
      have hdelta : 0 < min (theta + rho.re) (theta + 1 - rho.re) :=
        lt_min (by linarith) (by linarith)
      have hle := min_le_right (theta + rho.re) (theta + 1 - rho.re)
      linarith
  simpa using hs.abscissaOfAbsConv_le

theorem meixnerPrimeSeamValue_eq_reflected_transform
    {theta : ℝ} (htheta : 0 < theta) {rho : ℂ}
    (hrho : 0 < rho.re ∧ rho.re < 1) {x : ℝ} (hx : 1 < x) :
    meixnerPrimeSeamValue theta rho x =
      primeSeamTransform theta ((x : ℂ) + rho) -
        primeSeamTransform theta ((x : ℂ) + 1 - (starRingEnd ℂ) rho) := by
  have hsum1 : Summable (meixnerPrimeSeamSummand theta ((x : ℂ) + rho)) :=
    summable_meixnerPrimeSeamSummand htheta.le (by
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith)
  have hsum2 : Summable
      (meixnerPrimeSeamSummand theta ((x : ℂ) + 1 - (starRingEnd ℂ) rho)) :=
    summable_meixnerPrimeSeamSummand htheta.le (by
      have hcre : ((starRingEnd ℂ) rho).re = rho.re := Complex.conj_re rho
      rw [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.one_re, hcre]
      linarith)
  rw [meixnerPrimeSeamValue, LSeries_meixnerPrimeSeamCoeff_eq_tsum_primes,
    primeSeamTransform, primeSeamTransform]
  change (∑' p : Nat.Primes, meixnerPrimeSeamCoeff theta rho (p : ℕ) /
      ((p : ℕ) : ℂ) ^ (x : ℂ)) =
    (∑' p : Nat.Primes, meixnerPrimeSeamSummand theta ((x : ℂ) + rho) p) -
      ∑' p : Nat.Primes,
        meixnerPrimeSeamSummand theta ((x : ℂ) + 1 - (starRingEnd ℂ) rho) p
  rw [← hsum1.tsum_sub hsum2]
  apply tsum_congr
  intro p
  rw [meixnerPrimeSeamCoeff_prime, star_orbitwiseNatPrimeSeamCharge]
  dsimp [meixnerPrimeSeamSummand]
  have hpne : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.2.ne_zero
  calc
    (meixnerPrimeWeight theta (p : ℕ) : ℂ) *
          ((Real.log ((p : ℕ) : ℝ) : ℂ) *
            (((p : ℕ) : ℂ) ^ (-rho) -
              ((p : ℕ) : ℂ) ^ (-(1 - (starRingEnd ℂ) rho)))) /
        ((p : ℕ) : ℂ) ^ (x : ℂ) =
      (meixnerPrimeWeight theta (p : ℕ) : ℂ) *
          (Real.log ((p : ℕ) : ℝ) : ℂ) *
            (((p : ℕ) : ℂ) ^ (-rho) / ((p : ℕ) : ℂ) ^ (x : ℂ)) -
        (meixnerPrimeWeight theta (p : ℕ) : ℂ) *
          (Real.log ((p : ℕ) : ℝ) : ℂ) *
            (((p : ℕ) : ℂ) ^ (-(1 - (starRingEnd ℂ) rho)) /
              ((p : ℕ) : ℂ) ^ (x : ℂ)) := by ring
    _ = (meixnerPrimeWeight theta (p : ℕ) : ℂ) *
          (Real.log ((p : ℕ) : ℝ) : ℂ) *
            ((p : ℕ) : ℂ) ^ (-rho - (x : ℂ)) -
        (meixnerPrimeWeight theta (p : ℕ) : ℂ) *
          (Real.log ((p : ℕ) : ℝ) : ℂ) *
            ((p : ℕ) : ℂ) ^ (-(1 - (starRingEnd ℂ) rho) - (x : ℂ)) := by
          rw [Complex.cpow_sub _ _ hpne, Complex.cpow_sub _ _ hpne]
    _ = (meixnerPrimeWeight theta (p : ℕ) : ℂ) *
          (Real.log ((p : ℕ) : ℝ) : ℂ) *
            ((p : ℕ) : ℂ) ^ (-((x : ℂ) + rho)) -
        (meixnerPrimeWeight theta (p : ℕ) : ℂ) *
          (Real.log ((p : ℕ) : ℝ) : ℂ) *
            ((p : ℕ) : ℂ) ^ (-((x : ℂ) + 1 - (starRingEnd ℂ) rho)) := by
          congr 2
          all_goals ring

def meixnerPrimeSeamRaw (theta : ℝ) (rho : ℂ) (p : Nat.Primes) : ℂ :=
  (Real.sqrt (meixnerPrimeWeight theta (p : ℕ)) : ℂ) *
    orbitwiseNatPrimeSeamCharge (p : ℕ) rho

theorem norm_sq_meixnerPrimeSeamRaw (theta : ℝ) (rho : ℂ) (p : Nat.Primes) :
    ‖meixnerPrimeSeamRaw theta rho p‖ ^ 2 = meixnerSeamEnergy theta rho p := by
  rw [meixnerPrimeSeamRaw, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (meixnerPrimeWeight_pos theta _).le, meixnerSeamEnergy]

theorem summable_norm_sq_meixnerPrimeSeamRaw_iff
    {theta : ℝ} (htheta : 0 < theta) (rho : ℂ) :
    Summable (fun p : Nat.Primes => ‖meixnerPrimeSeamRaw theta rho p‖ ^ 2) ↔
      rho.re = 1 / 2 ∨ |2 * rho.re - 1| < theta := by
  simpa only [norm_sq_meixnerPrimeSeamRaw] using summable_meixnerSeamEnergy_iff htheta rho

noncomputable def meixnerPrimeSeam
    (theta : ℝ) (rho : ℂ) (hmem : Summable (meixnerSeamEnergy theta rho)) :
    MeixnerPrimeHilbert :=
  ⟨meixnerPrimeSeamRaw theta rho,
    HilbertSchmidt.memℓp_of_sq
      (hmem.congr (fun p => (norm_sq_meixnerPrimeSeamRaw theta rho p).symm))⟩

@[simp] theorem meixnerPrimeSeam_apply
    (theta : ℝ) (rho : ℂ) (hmem : Summable (meixnerSeamEnergy theta rho))
    (p : Nat.Primes) :
    meixnerPrimeSeam theta rho hmem p = meixnerPrimeSeamRaw theta rho p := rfl

theorem norm_sq_meixnerPrimeSeam
    (theta : ℝ) (rho : ℂ) (hmem : Summable (meixnerSeamEnergy theta rho)) :
    ‖meixnerPrimeSeam theta rho hmem‖ ^ 2 = ∑' p, meixnerSeamEnergy theta rho p := by
  rw [HilbertSchmidt.lp_norm_sq_eq]
  apply tsum_congr
  exact norm_sq_meixnerPrimeSeamRaw theta rho

theorem inner_lp_meixnerPrimeLaplaceFeature_eq_LSeries_star
    {theta x : ℝ} (htheta : 0 ≤ theta) (hx : 1 / 2 < x)
    (a : MeixnerPrimeHilbert) :
    inner ℂ a (meixnerPrimeLaplaceFeature theta x htheta hx) =
      LSeries (primeLaplaceCoeff theta (fun p => (starRingEnd ℂ) (a p))) x := by
  rw [lp.inner_eq_tsum, LSeries_primeLaplaceCoeff_eq_tsum_primes]
  apply tsum_congr
  intro p
  rw [meixnerPrimeLaplaceFeature_apply, meixnerPrimeLaplaceFeatureRaw,
    RCLike.inner_apply]
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have hpow : ((((p : ℕ) : ℝ) ^ (-x) : ℝ) : ℂ) =
      (((p : ℕ) : ℂ) ^ (x : ℂ))⁻¹ := by
    rw [Real.rpow_neg hp0.le, Complex.ofReal_inv, Complex.ofReal_cpow hp0.le]
    congr 1
  rw [hpow, inv_eq_one_div]
  ring

theorem primeLaplaceCoeff_star_meixnerPrimeSeamRaw
    (theta : ℝ) (rho : ℂ) :
    primeLaplaceCoeff theta (fun p => (starRingEnd ℂ) (meixnerPrimeSeamRaw theta rho p)) =
      meixnerPrimeSeamCoeff theta rho := by
  funext n
  rw [primeLaplaceCoeff, meixnerPrimeSeamCoeff]
  by_cases hn : n.Prime
  · rw [dif_pos hn, dif_pos hn, meixnerPrimeSeamRaw, map_mul, Complex.conj_ofReal]
    change ((Real.sqrt (meixnerPrimeWeight theta n) : ℝ) : ℂ) *
        (starRingEnd ℂ) (orbitwiseNatPrimeSeamCharge n rho) *
          ((Real.sqrt (meixnerPrimeWeight theta n) : ℝ) : ℂ) =
        (meixnerPrimeWeight theta n : ℂ) *
          (starRingEnd ℂ) (orbitwiseNatPrimeSeamCharge n rho)
    have hsq : ((Real.sqrt (meixnerPrimeWeight theta n) : ℝ) : ℂ) ^ 2 =
        (meixnerPrimeWeight theta n : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (meixnerPrimeWeight_pos theta _).le]
    calc
      ((Real.sqrt (meixnerPrimeWeight theta n) : ℝ) : ℂ) *
          (starRingEnd ℂ) (orbitwiseNatPrimeSeamCharge n rho) *
            ((Real.sqrt (meixnerPrimeWeight theta n) : ℝ) : ℂ) =
        ((Real.sqrt (meixnerPrimeWeight theta n) : ℝ) : ℂ) ^ 2 *
          (starRingEnd ℂ) (orbitwiseNatPrimeSeamCharge n rho) := by ring
      _ = (meixnerPrimeWeight theta n : ℂ) *
          (starRingEnd ℂ) (orbitwiseNatPrimeSeamCharge n rho) := by rw [hsq]
  · rw [dif_neg hn, dif_neg hn]

theorem inner_meixnerPrimeSeam_meixnerPrimeLaplaceFeature
    {theta : ℝ} (htheta : 0 < theta) (rho : ℂ)
    (hmem : Summable (meixnerSeamEnergy theta rho)) {x : ℝ} (hx : 1 / 2 < x) :
    inner ℂ (meixnerPrimeSeam theta rho hmem)
        (meixnerPrimeLaplaceFeature theta x htheta.le hx) =
      meixnerPrimeSeamValue theta rho x := by
  rw [inner_lp_meixnerPrimeLaplaceFeature_eq_LSeries_star,
    meixnerPrimeSeamValue]
  apply LSeries_congr
  intro n hn
  exact congrFun (primeLaplaceCoeff_star_meixnerPrimeSeamRaw theta rho) n

theorem inner_meixnerPrimeSeam_meixnerPrimeLaplaceFrame
    {theta : ℝ} (htheta : 0 < theta) (rho : ℂ)
    (hmem : Summable (meixnerSeamEnergy theta rho)) (n : ℕ) :
    inner ℂ (meixnerPrimeSeam theta rho hmem)
        (meixnerPrimeLaplaceFrame theta htheta.le n) =
      meixnerPrimeSeamValue theta rho (meixnerPrimeLaplaceNode n) := by
  exact inner_meixnerPrimeSeam_meixnerPrimeLaplaceFeature htheta rho hmem
    (meixnerPrimeLaplaceNode_gt_half n)

theorem eq_meixnerPrimeSeamRaw_of_frame_values
    {theta : ℝ} (htheta : 0 < theta) {rho : ℂ}
    (hrho : 0 < rho.re ∧ rho.re < 1) (a : MeixnerPrimeHilbert)
    (hvalues : ∀ n : ℕ,
      inner ℂ a (meixnerPrimeLaplaceFrame theta htheta.le n) =
        meixnerPrimeSeamValue theta rho (meixnerPrimeLaplaceNode n)) :
    ∀ p : Nat.Primes, a p = meixnerPrimeSeamRaw theta rho p := by
  classical
  let f : ℕ → ℂ := primeLaplaceCoeff theta (fun p => (starRingEnd ℂ) (a p))
  let g : ℕ → ℂ := meixnerPrimeSeamCoeff theta rho
  have hasq : Summable (fun p : Nat.Primes =>
      ‖(starRingEnd ℂ) (a p)‖ ^ 2) := by
    simpa only [RCLike.norm_conj] using summable_sq_lp a
  have habsf : LSeries.abscissaOfAbsConv f ≤ (((1 - theta) / 2 : ℝ) : EReal) := by
    dsimp [f]
    exact abscissaOfAbsConv_primeLaplaceCoeff_le htheta.le hasq
  have habsg : LSeries.abscissaOfAbsConv g ≤
      (meixnerPrimeSeamAbscissaWitness theta rho : EReal) := by
    dsimp [g]
    exact abscissaOfAbsConv_meixnerPrimeSeamCoeff_le_witness htheta hrho
  let C : ℝ := max ((1 - theta) / 2) (meixnerPrimeSeamAbscissaWitness theta rho)
  have hC : C < 1 := by
    rw [max_lt_iff]
    exact ⟨by linarith, meixnerPrimeSeamAbscissaWitness_lt_one htheta hrho⟩
  let V : Set ℂ := {z : ℂ | C < z.re}
  have hVf : V ⊆ {z : ℂ | LSeries.abscissaOfAbsConv f < (z.re : EReal)} := by
    intro z hz
    have hreal : (1 - theta) / 2 < z.re :=
      lt_of_le_of_lt (le_max_left _ _) hz
    exact lt_of_le_of_lt habsf (by exact_mod_cast hreal)
  have hVg : V ⊆ {z : ℂ | LSeries.abscissaOfAbsConv g < (z.re : EReal)} := by
    intro z hz
    have hreal : meixnerPrimeSeamAbscissaWitness theta rho < z.re :=
      lt_of_le_of_lt (le_max_right _ _) hz
    exact lt_of_le_of_lt habsg (by exact_mod_cast hreal)
  have hanaf : AnalyticOnNhd ℂ (LSeries f) V := (LSeries_analyticOnNhd f).mono hVf
  have hanag : AnalyticOnNhd ℂ (LSeries g) V := (LSeries_analyticOnNhd g).mono hVg
  have hone : (1 : ℂ) ∈ V := by
    simpa [V] using hC
  have hnode : ∀ n : ℕ,
      LSeries f (meixnerPrimeLaplaceNode n : ℂ) =
        LSeries g (meixnerPrimeLaplaceNode n : ℂ) := by
    intro n
    have hv := hvalues n
    change inner ℂ a
        (meixnerPrimeLaplaceFeature theta (meixnerPrimeLaplaceNode n) htheta.le
          (meixnerPrimeLaplaceNode_gt_half n)) =
      meixnerPrimeSeamValue theta rho (meixnerPrimeLaplaceNode n) at hv
    rw [inner_lp_meixnerPrimeLaplaceFeature_eq_LSeries_star] at hv
    simpa [f, g, meixnerPrimeSeamValue, meixnerPrimeLaplaceFrame] using hv
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), LSeries f z - LSeries g z = 0 :=
    tendsto_meixnerPrimeLaplaceNode_complex.frequently
      (Filter.Frequently.of_forall fun n => sub_eq_zero.mpr (hnode n))
  have hzero : Set.EqOn (fun z => LSeries f z - LSeries g z) 0 V :=
    (hanaf.sub hanag).eqOn_zero_of_preconnected_of_frequently_eq_zero
      (convex_halfSpace_re_gt C).isPreconnected hone hfreq
  have hevent : (fun x : ℝ => LSeries f (x : ℂ)) =ᶠ[Filter.atTop]
      (fun x : ℝ => LSeries g (x : ℂ)) := by
    filter_upwards [Filter.eventually_gt_atTop C] with x hx
    exact sub_eq_zero.mp (hzero (by simpa [V] using hx))
  have habsfTop : LSeries.abscissaOfAbsConv f < ⊤ :=
    lt_of_le_of_lt habsf (EReal.coe_lt_top _)
  have habsgTop : LSeries.abscissaOfAbsConv g < ⊤ :=
    lt_of_le_of_lt habsg (EReal.coe_lt_top _)
  intro p
  have hcoeff : f (p : ℕ) = g (p : ℕ) :=
    LSeries.eq_of_LSeries_eventually_eq habsfTop habsgTop hevent p.2.ne_zero
  have hrawCoeff := congrFun (primeLaplaceCoeff_star_meixnerPrimeSeamRaw theta rho) (p : ℕ)
  have hcoeff' :
      primeLaplaceCoeff theta (fun q => (starRingEnd ℂ) (a q)) (p : ℕ) =
        primeLaplaceCoeff theta
          (fun q => (starRingEnd ℂ) (meixnerPrimeSeamRaw theta rho q)) (p : ℕ) := by
    exact hcoeff.trans hrawCoeff.symm
  rw [primeLaplaceCoeff_prime, primeLaplaceCoeff_prime] at hcoeff'
  have hsqrt : ((Real.sqrt (meixnerPrimeWeight theta (p : ℕ)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (meixnerPrimeWeight_pos theta _)))
  have hstar : (starRingEnd ℂ) (a p) =
      (starRingEnd ℂ) (meixnerPrimeSeamRaw theta rho p) :=
    mul_right_cancel₀ hsqrt hcoeff'
  exact (starRingEnd ℂ).injective hstar

/-! ### Finite Gram/Riesz consumer -/

section FiniteValueGram

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def FiniteValueGramBoundSq (u : ι → E) (v : ι → ℂ) (B : ℝ) : Prop :=
  0 ≤ B ∧ ∀ c : ι →₀ ℂ,
    ‖Finsupp.linearCombination ℂ v c‖ ^ 2 ≤
      B * ‖Finsupp.linearCombination ℂ u c‖ ^ 2

noncomputable def complexRangePreim (T : (ι →₀ ℂ) →ₗ[ℂ] E)
    (y : LinearMap.range T) : ι →₀ ℂ :=
  Classical.choose (LinearMap.mem_range.mp y.2)

theorem complexRangePreim_spec (T : (ι →₀ ℂ) →ₗ[ℂ] E)
    (y : LinearMap.range T) :
    T (complexRangePreim T y) = (y : E) :=
  Classical.choose_spec (LinearMap.mem_range.mp y.2)

noncomputable def complexFactorRange
    (T : (ι →₀ ℂ) →ₗ[ℂ] E) (L : (ι →₀ ℂ) →ₗ[ℂ] ℂ)
    (hker : ∀ c, T c = 0 → L c = 0) : LinearMap.range T →ₗ[ℂ] ℂ where
  toFun y := L (complexRangePreim T y)
  map_add' y z := by
    have h : T (complexRangePreim T (y + z) -
        (complexRangePreim T y + complexRangePreim T z)) = 0 := by
      rw [map_sub, map_add, complexRangePreim_spec, complexRangePreim_spec,
        complexRangePreim_spec]
      simp
    have hzero := hker _ h
    rw [map_sub, map_add, sub_eq_zero] at hzero
    exact hzero
  map_smul' a y := by
    have h : T (complexRangePreim T (a • y) - a • complexRangePreim T y) = 0 := by
      rw [map_sub, map_smul, complexRangePreim_spec, complexRangePreim_spec]
      simp
    have hzero := hker _ h
    rw [map_sub, map_smul, sub_eq_zero] at hzero
    exact hzero

theorem complexFactorRange_apply_of_eq
    (T : (ι →₀ ℂ) →ₗ[ℂ] E) (L : (ι →₀ ℂ) →ₗ[ℂ] ℂ)
    (hker : ∀ c, T c = 0 → L c = 0) {c : ι →₀ ℂ}
    {y : LinearMap.range T} (hc : T c = (y : E)) :
    complexFactorRange T L hker y = L c := by
  have h : T (complexRangePreim T y - c) = 0 := by
    rw [map_sub, complexRangePreim_spec, hc, sub_self]
  have hzero := hker _ h
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

theorem finiteValueGramBoundSq_iff_exists_riesz [CompleteSpace E]
    (u : ι → E) (v : ι → ℂ) (B : ℝ) :
    FiniteValueGramBoundSq u v B ↔
      ∃ h : E, (∀ i, inner ℂ h (u i) = v i) ∧ ‖h‖ ^ 2 ≤ B := by
  classical
  let T : (ι →₀ ℂ) →ₗ[ℂ] E := Finsupp.linearCombination ℂ u
  let L : (ι →₀ ℂ) →ₗ[ℂ] ℂ := Finsupp.linearCombination ℂ v
  constructor
  · rintro ⟨hB, hbound⟩
    have hker : ∀ c, T c = 0 → L c = 0 := by
      intro c hc
      have hb := hbound c
      change ‖L c‖ ^ 2 ≤ B * ‖T c‖ ^ 2 at hb
      rw [hc, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero] at hb
      exact norm_eq_zero.mp (by nlinarith [sq_nonneg ‖L c‖])
    have hlinear : ∀ c, ‖L c‖ ≤ Real.sqrt B * ‖T c‖ := by
      intro c
      have hb := hbound c
      change ‖L c‖ ^ 2 ≤ B * ‖T c‖ ^ 2 at hb
      have hsqrt := Real.sq_sqrt hB
      have hright : (Real.sqrt B * ‖T c‖) ^ 2 = B * ‖T c‖ ^ 2 := by
        rw [mul_pow, hsqrt]
      rw [← hright] at hb
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg B)
        (norm_nonneg _))).mp hb
    let phi0 : LinearMap.range T →ₗ[ℂ] ℂ := complexFactorRange T L hker
    have hphi0 : ∀ y : LinearMap.range T, ‖phi0 y‖ ≤ Real.sqrt B * ‖y‖ := by
      intro y
      have h := hlinear (complexRangePreim T y)
      rw [complexRangePreim_spec] at h
      exact h
    let phi : LinearMap.range T →L[ℂ] ℂ := phi0.mkContinuous (Real.sqrt B) hphi0
    obtain ⟨psi, hpsi, hpsiNorm⟩ := exists_extension_norm_eq (LinearMap.range T) phi
    let h : E := (InnerProductSpace.toDual ℂ E).symm psi
    refine ⟨h, ?_, ?_⟩
    · intro i
      have hmem : T (Finsupp.single i 1) ∈ LinearMap.range T :=
        ⟨Finsupp.single i 1, rfl⟩
      have hrep : inner ℂ h (u i) = psi (u i) := by
        have heq := (InnerProductSpace.toDual ℂ E).apply_symm_apply psi
        exact congrArg (fun q : StrongDual ℂ E => q (u i)) heq
      rw [hrep]
      have hTi : T (Finsupp.single i 1) = u i := by simp [T]
      calc
        psi (u i) = psi (T (Finsupp.single i 1)) := by rw [hTi]
        _ = phi ⟨T (Finsupp.single i 1), hmem⟩ :=
          hpsi ⟨T (Finsupp.single i 1), hmem⟩
        _ = phi0 ⟨T (Finsupp.single i 1), hmem⟩ := rfl
        _ = L (Finsupp.single i 1) :=
          complexFactorRange_apply_of_eq T L hker rfl
        _ = v i := by simp [L]
    · have hphiNorm : ‖phi‖ ≤ Real.sqrt B :=
        phi.opNorm_le_bound (Real.sqrt_nonneg B) hphi0
      have hhNorm : ‖h‖ = ‖psi‖ := by
        exact (InnerProductSpace.toDual ℂ E).symm.norm_map psi
      rw [hhNorm, hpsiNorm]
      nlinarith [Real.sq_sqrt hB, norm_nonneg phi]
  · rintro ⟨h, hv, hh⟩
    refine ⟨le_trans (sq_nonneg ‖h‖) hh, fun c => ?_⟩
    have hsum : Finsupp.linearCombination ℂ v c =
        inner ℂ h (Finsupp.linearCombination ℂ u c) := by
      induction c using Finsupp.induction with
      | zero => simp
      | single_add i b c hi hb ih =>
          rw [map_add, Finsupp.linearCombination_single, map_add,
            Finsupp.linearCombination_single, inner_add_right, ih,
            inner_smul_right, hv i]
          rfl
    rw [hsum]
    have hinner : ‖inner ℂ h (Finsupp.linearCombination ℂ u c)‖ ≤
        ‖h‖ * ‖Finsupp.linearCombination ℂ u c‖ :=
      norm_inner_le_norm h (Finsupp.linearCombination ℂ u c)
    have hsq : ‖inner ℂ h (Finsupp.linearCombination ℂ u c)‖ ^ 2 ≤
        ‖h‖ ^ 2 * ‖Finsupp.linearCombination ℂ u c‖ ^ 2 := by
      rw [← mul_pow]
      exact (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hinner
    exact hsq.trans (mul_le_mul_of_nonneg_right hh (sq_nonneg _))

theorem isLeast_finiteValueGramBoundSq [CompleteSpace E]
    (u : ι → E) (hu : GaloisForLFunctions.HTGeometry.IsCompleteSystem ℂ u)
    (g : E) :
    IsLeast {B : ℝ | FiniteValueGramBoundSq u (fun i => inner ℂ g (u i)) B}
      (‖g‖ ^ 2) := by
  constructor
  · exact (finiteValueGramBoundSq_iff_exists_riesz u (fun i => inner ℂ g (u i))
      (‖g‖ ^ 2)).2 ⟨g, fun _ => rfl, le_rfl⟩
  · intro B hB
    obtain ⟨h, hhval, hhB⟩ :=
      (finiteValueGramBoundSq_iff_exists_riesz u (fun i => inner ℂ g (u i)) B).1 hB
    have heq : h = g := by
      have hzero : h - g = 0 :=
        (GaloisForLFunctions.HTGeometry.isCompleteSystem_iff_forall_inner_eq_zero u).1 hu
          (h - g) (fun i => by
            have hv : inner ℂ (h - g) (u i) = 0 := by
              rw [inner_sub_left, hhval i, sub_self]
            have hc := congrArg (starRingEnd ℂ) hv
            rw [inner_sub_right]
            simpa [inner_conj_symm] using hc)
      exact sub_eq_zero.mp hzero
    rwa [heq] at hhB

end FiniteValueGram

/-! ### Exact Meixner seam interpolation criterion -/

def meixnerPrimeSeamFiniteGramBound
    (theta : ℝ) (htheta : 0 ≤ theta) (rho : ℂ) (B : ℝ) : Prop :=
  FiniteValueGramBoundSq
    (meixnerPrimeLaplaceFrame theta htheta)
    (fun n => meixnerPrimeSeamValue theta rho (meixnerPrimeLaplaceNode n)) B

theorem summable_meixnerSeamEnergy_iff_exists_finiteGramBound
    {theta : ℝ} (htheta : 0 < theta) {rho : ℂ}
    (hrho : 0 < rho.re ∧ rho.re < 1) :
    Summable (meixnerSeamEnergy theta rho) ↔
      ∃ B : ℝ, meixnerPrimeSeamFiniteGramBound theta htheta.le rho B := by
  constructor
  · intro hmem
    refine ⟨‖meixnerPrimeSeam theta rho hmem‖ ^ 2, ?_⟩
    exact (finiteValueGramBoundSq_iff_exists_riesz
      (meixnerPrimeLaplaceFrame theta htheta.le)
      (fun n => meixnerPrimeSeamValue theta rho (meixnerPrimeLaplaceNode n))
      (‖meixnerPrimeSeam theta rho hmem‖ ^ 2)).2
        ⟨meixnerPrimeSeam theta rho hmem,
          inner_meixnerPrimeSeam_meixnerPrimeLaplaceFrame htheta rho hmem, le_rfl⟩
  · rintro ⟨B, hB⟩
    obtain ⟨a, hvalues, _⟩ := (finiteValueGramBoundSq_iff_exists_riesz
      (meixnerPrimeLaplaceFrame theta htheta.le)
      (fun n => meixnerPrimeSeamValue theta rho (meixnerPrimeLaplaceNode n)) B).1 hB
    have heq := eq_meixnerPrimeSeamRaw_of_frame_values htheta hrho a hvalues
    have hraw : Summable (fun p : Nat.Primes =>
        ‖meixnerPrimeSeamRaw theta rho p‖ ^ 2) :=
      (summable_sq_lp a).congr (fun p => congrArg (fun z : ℂ => ‖z‖ ^ 2) (heq p))
    exact hraw.congr (norm_sq_meixnerPrimeSeamRaw theta rho)

theorem exists_finiteGramBound_iff_meixnerRootThreshold
    {theta : ℝ} (htheta : 0 < theta) {rho : ℂ}
    (hrho : 0 < rho.re ∧ rho.re < 1) :
    (∃ B : ℝ, meixnerPrimeSeamFiniteGramBound theta htheta.le rho B) ↔
      rho.re = 1 / 2 ∨ |2 * rho.re - 1| < theta := by
  rw [← summable_meixnerSeamEnergy_iff htheta rho]
  exact (summable_meixnerSeamEnergy_iff_exists_finiteGramBound htheta hrho).symm

theorem isLeast_meixnerPrimeSeamFiniteGramBound
    {theta : ℝ} (htheta : 0 < theta) (rho : ℂ)
    (hmem : Summable (meixnerSeamEnergy theta rho)) :
    IsLeast
      {B : ℝ | meixnerPrimeSeamFiniteGramBound theta htheta.le rho B}
      (∑' p, meixnerSeamEnergy theta rho p) := by
  let g := meixnerPrimeSeam theta rho hmem
  have hleast := isLeast_finiteValueGramBoundSq
    (meixnerPrimeLaplaceFrame theta htheta.le)
    (isCompleteSystem_meixnerPrimeLaplaceFrame htheta.le) g
  have hvalues : (fun n => inner ℂ g (meixnerPrimeLaplaceFrame theta htheta.le n)) =
      (fun n => meixnerPrimeSeamValue theta rho (meixnerPrimeLaplaceNode n)) := by
    funext n
    exact inner_meixnerPrimeSeam_meixnerPrimeLaplaceFrame htheta rho hmem n
  rw [hvalues, norm_sq_meixnerPrimeSeam theta rho hmem] at hleast
  exact hleast

theorem riemannHypothesis_iff_meixnerPrimeSeamFiniteGramBounds :
    RiemannHypothesis ↔
      ∀ (m : ℕ), 0 < m → ∀ rho : ℂ, xi rho = 0 →
        ∃ B : ℝ, meixnerPrimeSeamFiniteGramBound
          (1 / (m : ℝ)) (by positivity) rho B := by
  rw [riemannHypothesis_iff_meixnerRootDomain]
  constructor
  · intro hroot m hm rho hzero
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    exact (summable_meixnerSeamEnergy_iff_exists_finiteGramBound
      (one_div_pos.mpr hmR) (xi_zero_re_mem_open_unit hzero)).mp
        (hroot m hm rho hzero)
  · intro hgram m hm rho hzero
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    exact (summable_meixnerSeamEnergy_iff_exists_finiteGramBound
      (one_div_pos.mpr hmR) (xi_zero_re_mem_open_unit hzero)).mpr
        (hgram m hm rho hzero)

/-! ### Sharp regular-Cauchy phase transition -/

def meixnerPrimeLogCauchyPacketEnergy {n : ℕ}
    (theta : ℝ) (z c : Fin n → ℂ) (p : Nat.Primes) : ℝ :=
  meixnerPrimeWeight theta (p : ℕ) * Complex.normSq
    (∑ j, c j * (z j - (GaloisForLFunctions.HTGeometry.primeLogSupport p : ℂ))⁻¹)

theorem meixnerPrimeLogCauchyPacketEnergy_nonneg {n : ℕ}
    (theta : ℝ) (z c : Fin n → ℂ) (p : Nat.Primes) :
    0 ≤ meixnerPrimeLogCauchyPacketEnergy theta z c p :=
  mul_nonneg (meixnerPrimeWeight_pos theta _).le (Complex.normSq_nonneg _)

theorem summable_meixnerPrimeLogCauchyPacketEnergy_iff_of_lt_one {n : ℕ}
    {theta : ℝ} (htheta0 : 0 ≤ theta) (htheta1 : theta < 1)
    (z c : Fin n → ℂ) (hz : Function.Injective z) (hzUpper : ∀ j, 0 < (z j).im) :
    Summable (meixnerPrimeLogCauchyPacketEnergy theta z c) ↔ c = 0 := by
  constructor
  · intro hsum
    have hb : 0 < (1 - theta) / 2 := by linarith
    have htransport : Summable
        (GaloisForLFunctions.HTGeometry.primeLogCauchyPacketTransportEnergy
          z c ((1 - theta) / 2)) := by
      refine Summable.of_nonneg_of_le (fun p => by
          exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
            (Complex.normSq_nonneg _)) (fun p => ?_) hsum
      have hw := meixnerPrimeWeight_ge theta htheta0
        (n := (p : ℕ)) p.2.one_lt.le
      rw [GaloisForLFunctions.HTGeometry.primeLogCauchyPacketTransportEnergy,
        meixnerPrimeLogCauchyPacketEnergy]
      have hexp : 2 * ((1 - theta) / 2) - 1 = -theta := by ring
      rw [hexp]
      exact mul_le_mul_of_nonneg_right hw (Complex.normSq_nonneg _)
    exact (GaloisForLFunctions.HTGeometry.summable_primeLogCauchyPacketTransportEnergy_iff
      z c hz hzUpper hb).mp htransport
  · rintro rfl
    convert (summable_zero : Summable (fun _ : Nat.Primes => (0 : ℝ))) using 1
    funext p
    simp [meixnerPrimeLogCauchyPacketEnergy]

theorem summable_meixnerPrimeLogCauchyPacketEnergy_one {n : ℕ}
    (z c : Fin n → ℂ) :
    Summable (meixnerPrimeLogCauchyPacketEnergy 1 z c) := by
  apply (summable_gammaDampedPrimeLogCauchyPacketEnergy z c).congr
  intro p
  simp only [meixnerPrimeLogCauchyPacketEnergy,
    gammaDampedPrimeLogCauchyPacketEnergy]
  congr 1

theorem meixnerPrimeLogCauchyPacket_sharp_phaseTransition {n : ℕ}
    {theta : ℝ} (htheta0 : 0 ≤ theta) (htheta1 : theta < 1)
    (z c : Fin n → ℂ) (hz : Function.Injective z) (hzUpper : ∀ j, 0 < (z j).im) :
    (Summable (meixnerPrimeLogCauchyPacketEnergy theta z c) ↔ c = 0) ∧
      Summable (meixnerPrimeLogCauchyPacketEnergy 1 z c) :=
  ⟨summable_meixnerPrimeLogCauchyPacketEnergy_iff_of_lt_one
      htheta0 htheta1 z c hz hzUpper,
    summable_meixnerPrimeLogCauchyPacketEnergy_one z c⟩

end RHTower
