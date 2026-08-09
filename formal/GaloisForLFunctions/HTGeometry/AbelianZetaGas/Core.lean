import GaloisForLFunctions.HTGeometry.ProductOccupancyDichotomy
import GaloisForLFunctions.HTGeometry.GeometricTailMass
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.PNat.Equiv
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# Abelian zeta gas: exact mode measure and condensation core

This file constructs the countable prime-depth product measure used by the abelian zeta gas.
Depths are stored with a zero-based coordinate, so `(p, n)` represents the cyclic factor
`Z / p^(n+1) Z`.  It proves the exact geometric atom law, identifies canonical finite abelian
group classes with finitely supported mode configurations, and proves both halves of every sharp
depth-condensation wall.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- A prime-depth mode.  The natural coordinate `n` represents positive depth `n + 1`. -/
abbrev AbelianZetaMode := Nat.Primes × ℕ

namespace AbelianZetaMode

/-- Positive cyclic depth represented by a zero-based mode coordinate. -/
def depth (m : AbelianZetaMode) : ℕ := m.2 + 1

@[simp] theorem depth_mk (p : Nat.Primes) (n : ℕ) : depth (p, n) = n + 1 := rfl

theorem depth_pos (m : AbelianZetaMode) : 0 < depth m := by
  simp [depth]

end AbelianZetaMode

/-- Unconditional parameter domain of the two-observable mode gas. -/
structure AbelianZetaParameters where
  sigma : ℝ
  tau : ℝ
  sigma_pos : 0 < sigma
  tau_nonneg : 0 ≤ tau

/-- Absolute-convergence chamber in which the whole group is finite almost surely. -/
structure AbelianZetaConvergentParameters extends AbelianZetaParameters where
  firstDepth : 1 < sigma + tau

namespace AbelianZetaParameters

/-- Exponent attached to a prime-depth mode. -/
def exponent (θ : AbelianZetaParameters) (m : AbelianZetaMode) : ℝ :=
  AbelianZetaMode.depth m * θ.sigma + θ.tau

/-- Failure ratio of the geometric occupation law at a mode. -/
def ratio (θ : AbelianZetaParameters) (m : AbelianZetaMode) : ℝ :=
  (m.1 : ℝ) ^ (-θ.exponent m)

theorem exponent_pos (θ : AbelianZetaParameters) (m : AbelianZetaMode) :
    0 < θ.exponent m := by
  dsimp [exponent]
  have hd : 0 < (AbelianZetaMode.depth m : ℝ) := by
    exact_mod_cast AbelianZetaMode.depth_pos m
  exact add_pos_of_pos_of_nonneg (mul_pos hd θ.sigma_pos) θ.tau_nonneg

theorem ratio_pos (θ : AbelianZetaParameters) (m : AbelianZetaMode) :
    0 < θ.ratio m := by
  exact Real.rpow_pos_of_pos (by exact_mod_cast m.1.prop.pos) _

theorem ratio_lt_one (θ : AbelianZetaParameters) (m : AbelianZetaMode) :
    θ.ratio m < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast m.1.prop.one_lt) (neg_neg_of_pos (θ.exponent_pos m))

theorem ratio_nonneg (θ : AbelianZetaParameters) (m : AbelianZetaMode) :
    0 ≤ θ.ratio m := (θ.ratio_pos m).le

theorem ratio_le_one (θ : AbelianZetaParameters) (m : AbelianZetaMode) :
    θ.ratio m ≤ 1 := (θ.ratio_lt_one m).le

/-- Success parameter of `geometricMeasure`; its failure probability is the gas ratio. -/
def success (θ : AbelianZetaParameters) (m : AbelianZetaMode) : unitInterval :=
  ⟨1 - θ.ratio m, sub_nonneg.mpr (θ.ratio_le_one m), by linarith [θ.ratio_nonneg m]⟩

theorem success_pos (θ : AbelianZetaParameters) (m : AbelianZetaMode) :
    0 < (θ.success m : ℝ) := by
  simpa [success] using sub_pos.mpr (θ.ratio_lt_one m)

theorem success_ne_zero (θ : AbelianZetaParameters) (m : AbelianZetaMode) :
    θ.success m ≠ 0 := by
  intro h
  have hv := congrArg Subtype.val h
  exact (ne_of_gt (θ.success_pos m)) hv

@[simp] theorem one_sub_success (θ : AbelianZetaParameters) (m : AbelianZetaMode) :
    1 - (θ.success m : ℝ) = θ.ratio m := by
  simp [success]

/-- Independent geometric occupation law of one prime-depth mode. -/
def modeLaw (θ : AbelianZetaParameters) (m : AbelianZetaMode) : Measure ℕ :=
  geometricMeasure (θ.success m)

instance modeLaw_isProbability (θ : AbelianZetaParameters) (m : AbelianZetaMode) :
    IsProbabilityMeasure (θ.modeLaw m) := by
  dsimp [modeLaw]
  infer_instance

theorem modeLaw_singleton (θ : AbelianZetaParameters) (m : AbelianZetaMode) (n : ℕ) :
    θ.modeLaw m {n} = ENNReal.ofReal ((θ.ratio m) ^ n * (1 - θ.ratio m)) := by
  rw [modeLaw, geometricMeasure_singleton (θ.success_ne_zero m)]
  simp only [one_sub_success]
  simp [success]

theorem modeLaw_zero (θ : AbelianZetaParameters) (m : AbelianZetaMode) :
    θ.modeLaw m {0} = ENNReal.ofReal (1 - θ.ratio m) := by
  simpa using θ.modeLaw_singleton m 0

theorem modeLaw_occupied (θ : AbelianZetaParameters) (m : AbelianZetaMode) :
    θ.modeLaw m {0}ᶜ = ENNReal.ofReal (θ.ratio m) := by
  rw [modeLaw]
  rw [show ({0}ᶜ : Set ℕ) = {n : ℕ | 1 ≤ n} by
    ext n
    simp only [mem_compl_iff, mem_singleton_iff, mem_setOf_eq]
    omega]
  rw [geometricMeasure_Ici (θ.success_ne_zero m) 1]
  simp

/-- Full independent prime-depth occupation measure. -/
def gasMeasure (θ : AbelianZetaParameters) : Measure (AbelianZetaMode → ℕ) :=
  Measure.infinitePi θ.modeLaw

instance gasMeasure_isProbability (θ : AbelianZetaParameters) :
    IsProbabilityMeasure θ.gasMeasure := by
  dsimp [gasMeasure]
  infer_instance

/-- Canonical enumeration used by Borel--Cantelli theorems. -/
def modeEquivNat : ℕ ≃ AbelianZetaMode :=
  Classical.choice nonempty_equiv_of_countable

end AbelianZetaParameters

/-! ## Exact summability of reindexed depth tails -/

/-- Ratio of the mode at prime `p` and actual depth `g + n`. -/
def abelianZetaTailRatio (σ τ : ℝ) (g : ℕ) (m : AbelianZetaMode) : ℝ :=
  (m.1 : ℝ) ^ (-(((g + m.2 : ℕ) : ℝ) * σ + τ))

theorem abelianZetaTailRatio_nonneg (σ τ : ℝ) (g : ℕ) (m : AbelianZetaMode) :
    0 ≤ abelianZetaTailRatio σ τ g m := by
  exact (Real.rpow_pos_of_pos (by exact_mod_cast m.1.prop.pos) _).le

private theorem abelianZetaTailRatio_factor
    (σ τ : ℝ) (g : ℕ) (p : Nat.Primes) (n : ℕ) :
    abelianZetaTailRatio σ τ g (p, n) =
      (p : ℝ) ^ (-((g : ℝ) * σ + τ)) * (((p : ℝ) ^ (-σ)) ^ n) := by
  rw [abelianZetaTailRatio]
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  rw [show -(((g + n : ℕ) : ℝ) * σ + τ) =
      (-((g : ℝ) * σ + τ)) + (-σ) * (n : ℝ) by push_cast; ring]
  rw [Real.rpow_add hp, Real.rpow_mul hp.le, Real.rpow_natCast]

private theorem prime_ratio_le_two_ratio (σ : ℝ) (hσ : 0 < σ) (p : Nat.Primes) :
    (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) := by
  rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
  apply (inv_le_inv₀ (Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _)
    (Real.rpow_pos_of_pos (by positivity) _)).2
  exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast p.prop.two_le) hσ.le

/-- If the first retained depth exponent exceeds one, all retained occupation ratios are summable.
This is the analytic core of finite activity above every depth wall. -/
theorem summable_abelianZetaTailRatio
    {σ τ : ℝ} (hσ : 0 < σ) {g : ℕ} (hg : 1 < (g : ℝ) * σ + τ) :
    Summable (abelianZetaTailRatio σ τ g) := by
  let base : Nat.Primes → ℝ := fun p => (p : ℝ) ^ (-((g : ℝ) * σ + τ))
  let r : ℝ := (2 : ℝ) ^ (-σ)
  have hbase : Summable base := by
    rw [Nat.Primes.summable_rpow]
    linarith
  have hrpos : 0 < r := Real.rpow_pos_of_pos (by positivity) _
  have hrlt : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hσ)
  have hgeo : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_norm_lt_one (by simpa [abs_of_pos hrpos] using hrlt)
  have hprod : Summable (fun m : AbelianZetaMode => base m.1 * r ^ m.2) :=
    Summable.mul_of_nonneg hbase hgeo
      (fun p => (Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _).le)
      (fun _ => pow_nonneg hrpos.le _)
  refine Summable.of_nonneg_of_le (abelianZetaTailRatio_nonneg σ τ g) ?_ hprod
  rintro ⟨p, n⟩
  rw [abelianZetaTailRatio_factor]
  dsimp [base, r]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _).le
      (prime_ratio_le_two_ratio σ hσ p) n)
    (Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _).le

/-- Equivalence between zero-based modes and modes of actual depth at least `g`. -/
def abelianZetaTailModeEquiv (g : ℕ) (hg : 1 ≤ g) :
    AbelianZetaMode ≃ {m : AbelianZetaMode // g ≤ AbelianZetaMode.depth m} where
  toFun m := ⟨(m.1, m.2 + (g - 1)), by simp [AbelianZetaMode.depth]; omega⟩
  invFun m := (m.1.1, m.1.2 - (g - 1))
  left_inv m := by
    ext <;> simp
  right_inv m := by
    apply Subtype.ext
    ext
    · rfl
    · simp [AbelianZetaMode.depth] at m ⊢
      omega

theorem abelianZetaTailModeEquiv_depth
    (g : ℕ) (hg : 1 ≤ g) (m : AbelianZetaMode) :
    AbelianZetaMode.depth ((abelianZetaTailModeEquiv g hg m :
      {m : AbelianZetaMode // g ≤ AbelianZetaMode.depth m}) : AbelianZetaMode) = g + m.2 := by
  change m.2 + (g - 1) + 1 = g + m.2
  omega

theorem summable_abelianZetaRatio_indicator_depth
    (θ : AbelianZetaParameters) {g : ℕ} (hg : 1 ≤ g)
    (hwall : 1 < (g : ℝ) * θ.sigma + θ.tau) :
    Summable ({m : AbelianZetaMode | g ≤ AbelianZetaMode.depth m}.indicator θ.ratio) := by
  rw [← summable_subtype_iff_indicator]
  apply ((abelianZetaTailModeEquiv g hg).summable_iff).mp
  have hs := summable_abelianZetaTailRatio θ.sigma_pos hwall
  refine hs.congr fun m => ?_
  simp only [Function.comp_apply]
  rw [AbelianZetaParameters.ratio, AbelianZetaParameters.exponent,
    abelianZetaTailRatio, abelianZetaTailModeEquiv_depth g hg m]
  simp [abelianZetaTailModeEquiv]

/-! ## Exact prime-slice divergence -/

theorem not_summable_prime_rpow_of_exponent_le_one
    {a : ℝ} (_ha0 : 0 < a) (ha1 : a ≤ 1) :
    ¬ Summable (fun p : Nat.Primes => (p : ℝ) ^ (-a)) := by
  intro hs
  have hdiv : Summable (fun p : Nat.Primes => 1 / (p : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun p => ?_) hs
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.prop.one_lt.le) (by linarith)
  exact Nat.Primes.not_summable_one_div hdiv

theorem tsum_coe_prime_rpow_eq_top_of_exponent_le_one
    {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    (∑' p : Nat.Primes, ENNReal.ofReal ((p : ℝ) ^ (-a))) = ∞ := by
  let f : Nat.Primes → ℝ≥0 := fun p =>
    ⟨(p : ℝ) ^ (-a), (Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _).le⟩
  have heq : (fun p : Nat.Primes => ENNReal.ofReal ((p : ℝ) ^ (-a))) =
      fun p => (f p : ℝ≥0∞) := by
    funext p
    rw [ENNReal.ofReal_eq_coe_nnreal
      (Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _).le]
    rfl
  rw [heq]
  rw [ENNReal.tsum_coe_eq_top_iff_not_summable_coe]
  exact not_summable_prime_rpow_of_exponent_le_one ha0 ha1

/-! ## Sharp almost-sure condensation laws -/

namespace AbelianZetaParameters

/-- Local event selecting occupied modes whose actual depth is at least `g`. -/
def depthTailEvent (_θ : AbelianZetaParameters) (g : ℕ) (m : AbelianZetaMode) : Set ℕ :=
  if g ≤ AbelianZetaMode.depth m then {0}ᶜ else ∅

/-- Local event selecting occupied modes of actual depth exactly `g`. -/
def exactDepthEvent (_θ : AbelianZetaParameters) (g : ℕ) (m : AbelianZetaMode) : Set ℕ :=
  if AbelianZetaMode.depth m = g then {0}ᶜ else ∅

theorem modeLaw_depthTailEvent (θ : AbelianZetaParameters) (g : ℕ) (m : AbelianZetaMode) :
    θ.modeLaw m (θ.depthTailEvent g m) =
      ENNReal.ofReal (({m : AbelianZetaMode | g ≤ AbelianZetaMode.depth m}.indicator θ.ratio) m) := by
  by_cases h : g ≤ AbelianZetaMode.depth m
  · simp [depthTailEvent, h, θ.modeLaw_occupied]
  · simp [depthTailEvent, h]

theorem modeLaw_exactDepthEvent (θ : AbelianZetaParameters) (g : ℕ) (m : AbelianZetaMode) :
    θ.modeLaw m (θ.exactDepthEvent g m) =
      ENNReal.ofReal (({m : AbelianZetaMode | AbelianZetaMode.depth m = g}.indicator θ.ratio) m) := by
  by_cases h : AbelianZetaMode.depth m = g
  · simp [exactDepthEvent, h, θ.modeLaw_occupied]
  · simp [exactDepthEvent, h]

theorem tsum_depthTailEvent_ne_top
    (θ : AbelianZetaParameters) {g : ℕ} (hg : 1 ≤ g)
    (hwall : 1 < (g : ℝ) * θ.sigma + θ.tau) :
    (∑' m : AbelianZetaMode, θ.modeLaw m (θ.depthTailEvent g m)) ≠ ∞ := by
  simp_rw [θ.modeLaw_depthTailEvent]
  have hs := summable_abelianZetaRatio_indicator_depth θ hg hwall
  exact hs.tsum_ofReal_ne_top

/-- Above the exact wall, only finitely many depth-at-least-`g` modes are active almost surely. -/
theorem measure_finite_depthTail_eq_one
    (θ : AbelianZetaParameters) {g : ℕ} (hg : 1 ≤ g)
    (hwall : 1 < (g : ℝ) * θ.sigma + θ.tau) :
    θ.gasMeasure {k | (localHitSet (θ.depthTailEvent g) k).Finite} = 1 := by
  exact measure_finiteHit_eq_one θ.modeLaw (θ.depthTailEvent g) modeEquivNat
    (θ.tsum_depthTailEvent_ne_top hg hwall)

theorem tsum_exactDepthEvent_eq_top
    (θ : AbelianZetaParameters) {g : ℕ} (hg : 1 ≤ g)
    (hwall : (g : ℝ) * θ.sigma + θ.tau ≤ 1) :
    (∑' m : AbelianZetaMode, θ.modeLaw m (θ.exactDepthEvent g m)) = ∞ := by
  have hgpos : 0 < (g : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hg)
  have hexp0 : 0 < (g : ℝ) * θ.sigma + θ.tau :=
    add_pos_of_pos_of_nonneg (mul_pos hgpos θ.sigma_pos) θ.tau_nonneg
  have hprime := tsum_coe_prime_rpow_eq_top_of_exponent_le_one hexp0 hwall
  let emb : Nat.Primes → AbelianZetaMode := fun p => (p, g - 1)
  have hemb : Function.Injective emb := fun p q h => by simpa [emb] using congrArg Prod.fst h
  rw [← top_le_iff]
  calc
    ∞ = ∑' p : Nat.Primes, ENNReal.ofReal ((p : ℝ) ^ (-((g : ℝ) * θ.sigma + θ.tau))) := hprime.symm
    _ = ∑' p : Nat.Primes, θ.modeLaw (emb p) (θ.exactDepthEvent g (emb p)) := by
      apply tsum_congr
      intro p
      rw [θ.modeLaw_exactDepthEvent]
      simp only [emb]
      rw [Set.indicator_of_mem]
      · have hdepth : AbelianZetaMode.depth (p, g - 1) = g := by
          simp [AbelianZetaMode.depth]
          omega
        rw [AbelianZetaParameters.ratio, AbelianZetaParameters.exponent, hdepth]
      · simp [AbelianZetaMode.depth]
        omega
    _ ≤ ∑' m : AbelianZetaMode, θ.modeLaw m (θ.exactDepthEvent g m) :=
      ENNReal.tsum_comp_le_tsum_of_injective hemb _

/-- At or below the exact wall, infinitely many depth-exactly-`g` modes are active almost surely. -/
theorem measure_infinite_exactDepth_eq_one
    (θ : AbelianZetaParameters) {g : ℕ} (hg : 1 ≤ g)
    (hwall : (g : ℝ) * θ.sigma + θ.tau ≤ 1) :
    θ.gasMeasure {k | (localHitSet (θ.exactDepthEvent g) k).Infinite} = 1 := by
  exact measure_infiniteHit_eq_one θ.modeLaw (θ.exactDepthEvent g) modeEquivNat
    (θ.tsum_exactDepthEvent_eq_top hg hwall)

/-- The theorem-5.1 chamber at `tau = 0`, stated without route hypotheses. -/
def temperatureParameters (σ : ℝ) (hσ : 0 < σ) : AbelianZetaParameters :=
  ⟨σ, 0, hσ, le_rfl⟩

theorem temperature_finite_depthTail_eq_one
    {σ : ℝ} (hσ : 0 < σ) {g : ℕ} (hg : 1 ≤ g) (hwall : 1 / (g : ℝ) < σ) :
    (temperatureParameters σ hσ).gasMeasure
      {k | (localHitSet ((temperatureParameters σ hσ).depthTailEvent g) k).Finite} = 1 := by
  apply measure_finite_depthTail_eq_one _ hg
  have hgpos : (0 : ℝ) < g := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hg)
  field_simp at hwall
  simpa [temperatureParameters] using hwall

theorem temperature_infinite_exactDepth_eq_one
    {σ : ℝ} (hσ : 0 < σ) {g : ℕ} (hg : 1 ≤ g) (hwall : σ ≤ 1 / (g : ℝ)) :
    (temperatureParameters σ hσ).gasMeasure
      {k | (localHitSet ((temperatureParameters σ hσ).exactDepthEvent g) k).Infinite} = 1 := by
  apply measure_infinite_exactDepth_eq_one _ hg
  have hgpos : (0 : ℝ) < g := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hg)
  field_simp at hwall
  simpa [temperatureParameters, mul_comm] using hwall

end AbelianZetaParameters

/-! ## Canonical finite abelian group classes and observables -/

/-- Isomorphism classes of finite abelian groups in elementary-divisor normal form. -/
abbrev AbelianZetaGroupClass := AbelianZetaMode →₀ ℕ

noncomputable instance : Countable AbelianZetaGroupClass :=
  Countable.of_equiv (Multiset AbelianZetaMode) Multiset.toFinsupp.toEquiv

/-- Embed a finitely supported group class into the full occupation configuration. -/
def AbelianZetaGroupClass.configuration (A : AbelianZetaGroupClass) : AbelianZetaMode → ℕ := A

theorem AbelianZetaGroupClass.occupiedSet_configuration (A : AbelianZetaGroupClass) :
    occupiedSet A.configuration = (A.support : Set AbelianZetaMode) := by
  ext m
  simp [occupiedSet, AbelianZetaGroupClass.configuration]

theorem AbelianZetaGroupClass.finite_occupiedSet (A : AbelianZetaGroupClass) :
    (occupiedSet A.configuration).Finite := by
  rw [A.occupiedSet_configuration]
  exact A.support.finite_toSet

/-- Every finitely occupied full configuration has a unique canonical group class. -/
theorem existsUnique_groupClass_of_finite_occupiedSet
    (k : AbelianZetaMode → ℕ) (hk : (occupiedSet k).Finite) :
    ∃! A : AbelianZetaGroupClass, A.configuration = k := by
  have hsupp : (Function.support k).Finite := by
    simpa [occupiedSet, Function.support] using hk
  refine ⟨Finsupp.ofSupportFinite k hsupp, ?_, ?_⟩
  · exact Finsupp.ofSupportFinite_coe
  · intro A hA
    ext m
    exact congrFun hA m

/-- Group order observable from the elementary-divisor normal form. -/
def AbelianZetaGroupClass.order (A : AbelianZetaGroupClass) : ℕ :=
  A.prod fun m n => (m.1 : ℕ) ^ (AbelianZetaMode.depth m * n)

/-- Socle order observable: one prime factor for every cyclic factor. -/
def AbelianZetaGroupClass.socleOrder (A : AbelianZetaGroupClass) : ℕ :=
  A.prod fun m n => (m.1 : ℕ) ^ n

theorem AbelianZetaGroupClass.order_eq_mode_product (A : AbelianZetaGroupClass) :
    A.order = A.prod fun m n => (m.1 : ℕ) ^ (AbelianZetaMode.depth m * n) := rfl

theorem AbelianZetaGroupClass.socleOrder_eq_mode_product (A : AbelianZetaGroupClass) :
    A.socleOrder = A.prod fun m n => (m.1 : ℕ) ^ n := rfl

theorem AbelianZetaGroupClass.order_pos (A : AbelianZetaGroupClass) : 0 < A.order := by
  classical
  simp only [AbelianZetaGroupClass.order, Finsupp.prod]
  exact Finset.prod_pos fun m _ => pow_pos m.1.prop.pos _

theorem AbelianZetaGroupClass.socleOrder_pos (A : AbelianZetaGroupClass) :
    0 < A.socleOrder := by
  classical
  simp only [AbelianZetaGroupClass.socleOrder, Finsupp.prod]
  exact Finset.prod_pos fun m _ => pow_pos m.1.prop.pos _

/-- Exact unnormalized two-observable Gibbs weight expressed by group observables. -/
def abelianZetaTwoObservableWeight (θ : AbelianZetaParameters) (A : AbelianZetaGroupClass) : ℝ :=
  (A.order : ℝ) ^ (-θ.sigma) * (A.socleOrder : ℝ) ^ (-θ.tau)

/-- Exact unnormalized Gibbs weight in the independent prime-depth factorization. -/
def abelianZetaModeWeight (θ : AbelianZetaParameters) (A : AbelianZetaGroupClass) : ℝ :=
  A.prod fun m n => (θ.ratio m) ^ n

end GaloisForLFunctions.HTGeometry
