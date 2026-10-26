import GaloisForLFunctions.ArithmeticCorrelationGeometry.SuccessorCorrelationsArePureGaugeCharge

/-!
# The threshold is the price of the archimedean line

The vertical shifts `n^{2πiξ}` are the twists along one line of the gauge torus, the phase flow
with frequencies `log p` (`expSum_eq_twistSum`). Mean values over heights are averages along that
line; gauge mean values are averages over the whole torus. This file compares the two exactly.

* **Archimedean = gauge + near-incidence** (`windowed_eq_gauge_add_nearIncidence`). The windowed
  mean square of a Dirichlet polynomial is `‖η‖²` times its gauge mean square plus the
  **near-incidence form** `Σ_{j ≠ k} c_j c̄_k k_η(log j − log k)`, which reads only the pairs with
  `|log(j/k)|` inside the window support. The same holds for every product order
  (`windowed_pow_eq_gauge_add_nearIncidence`), with the near-incidence form of `c^{*k}`.
* **Below the threshold the line sees the whole torus** (`windowed_pow_eq_gauge_of_threshold`). If
  `2rX^k ≤ 1` the near-incidence form vanishes and the windowed `2k`-th moment equals `‖η‖²` times
  the gauge `2k`-th moment. The gauge torus has no threshold; the archimedean line has one because
  it cannot separate products closer than its window.
* **Near-incidence is pure gauge charge** (`integral_nearIncidence_twisted`,
  `integral_nearIncidence_pow_twisted`). Over the gauge orbit of the coefficients its mean is
  zero, at every order and every length. So the gauge-orbit mean of every windowed moment is
  exactly its diagonal (`integral_windowed_twisted`): beyond the threshold, all excess over the
  diagonal is a property of the particular gauge point.
* **Nonnegative sources are the worst case of their orbit** (`norm_nearIncidence_twisted_le`). For
  nonnegative coefficients and a window with nonnegative autocorrelation, the untwisted
  near-incidence form is real, nonnegative, and dominates the modulus of every twist. A bound on
  the near-incidence of the primes obtained through positive kernels is a bound for the whole gauge
  orbit; it cannot see the negative (repulsive) values a signed kernel can.
-/

open MeasureTheory Complex Finset
open scoped Real ComplexConjugate ComplexOrder

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrelationGeometry

open HTGeometry ArithmeticKunnethTheory Zeta23 SquareRootThreshold _root_.RHTower
  _root_.RHTower.WeilRegular

/-! ### The archimedean line in the gauge torus -/

/-- The point of the archimedean line at height `ξ`: the twist `n ↦ n^{2πiξ}`. -/
def archPoint (ξ : ℝ) : GaugeTorus := clockPhasePoint (fun p => Real.log p) (2 * π * ξ)

theorem twist_archPoint (ξ : ℝ) (n : ℕ) :
    twist (archPoint ξ) n = cexp (2 * π * I * ξ * logFreq n) := by
  rw [archPoint, twist_clockPhasePoint, logFreq]
  congr 1
  push_cast
  ring

/-- Dirichlet polynomials at height `ξ` are twisted polynomials at the archimedean point. -/
theorem expSum_eq_twistSum (s : Finset ℕ) (c : ℕ → ℂ) (ξ : ℝ) :
    expSum s c logFreq ξ = twistSum s c (archPoint ξ) := by
  rw [expSum, twistSum]
  simp_rw [twist_archPoint]

/-! ### Near-incidence forms -/

/-- The near-incidence form `Σ_{j ≠ k} c_j c̄_k k_η(log j − log k)`. -/
def nearIncidence (η : ℝ → ℂ) (s : Finset ℕ) (c : ℕ → ℂ) : ℂ :=
  ∑ j ∈ s, ∑ k ∈ s.erase j, c j * conj (c k) * EF.weilTest η η (logFreq j - logFreq k)

/-- **Archimedean = gauge + near-incidence.** -/
theorem windowed_eq_gauge_add_nearIncidence {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η)
    (hηc : HasCompactSupport η) {s : Finset ℕ} (hs : ∀ n ∈ s, n ≠ 0) (c : ℕ → ℂ) :
    ∫ ξ : ℝ, pairTransform η ξ * (expSum s c logFreq ξ * conj (expSum s c logFreq ξ)) =
      ((∫ t, ‖η t‖ ^ 2 : ℝ) : ℂ) * ((∫ x, ‖twistSum s c x‖ ^ 2 ∂gaugeHaar : ℝ) : ℂ) +
        nearIncidence η s c := by
  rw [integral_pairTransform_mul_normSq_expSum_eq_diag_add hη hηc, integral_normSq_twistSum hs,
    nearIncidence]
  push_cast
  rfl

/-- The coefficients of a power of a twisted polynomial are twisted coefficients. -/
theorem powCoeff_twisted {s : Finset ℕ} (hs : ∀ n ∈ s, n ≠ 0) (y : GaugeTorus) (c : ℕ → ℂ)
    (k N : ℕ) : powCoeff s (twisted y c) k N = twist y N * powCoeff s c k N := by
  rw [powCoeff, powCoeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  obtain ⟨ht, hN⟩ := Finset.mem_filter.mp ht
  rw [Fintype.mem_piFinset] at ht
  simp only [twisted, Finset.prod_mul_distrib]
  rw [← twist_prod y _ t fun i _ => hs _ (ht i), hN]

/-- **Archimedean = gauge + near-incidence, at every product order.** -/
theorem windowed_pow_eq_gauge_add_nearIncidence {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η)
    (hηc : HasCompactSupport η) {s : Finset ℕ} (hs : ∀ n ∈ s, n ≠ 0) (c : ℕ → ℂ) (k : ℕ) :
    ∫ ξ : ℝ, pairTransform η ξ * (expSum s c logFreq ξ * conj (expSum s c logFreq ξ)) ^ k =
      ((∫ t, ‖η t‖ ^ 2 : ℝ) : ℂ) * ((∫ x, ‖twistSum s c x‖ ^ (2 * k) ∂gaugeHaar : ℝ) : ℂ) +
        nearIncidence η (ArithmeticKunnethTheory.powSupport s k) (powCoeff s c k) := by
  have hs1 : ∀ n ∈ s, 1 ≤ n := fun n hn => Nat.one_le_iff_ne_zero.mpr (hs n hn)
  have hpow : ∀ ξ : ℝ, (expSum s c logFreq ξ * conj (expSum s c logFreq ξ)) ^ k =
      expSum (ArithmeticKunnethTheory.powSupport s k) (powCoeff s c k) logFreq ξ *
        conj (expSum (ArithmeticKunnethTheory.powSupport s k) (powCoeff s c k) logFreq ξ) := by
    intro ξ
    rw [mul_pow, ← map_pow, expSum_pow_eq_powSum hs1]
  simp_rw [hpow]
  rw [windowed_eq_gauge_add_nearIncidence hη hηc (fun N hN => ne_zero_of_mem_powSupport hs hN),
    integral_normSq_twistSum_pow hs, integral_normSq_twistSum
      (fun N hN => ne_zero_of_mem_powSupport hs hN)]

/-- **Below the threshold the archimedean line sees the whole gauge torus.** -/
theorem windowed_pow_eq_gauge_of_threshold {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η) {r : ℝ}
    (hηs : tsupport η ⊆ Set.Icc (-r) r) {s : Finset ℕ} {X : ℕ} (hs : ∀ n ∈ s, 1 ≤ n ∧ n ≤ X)
    (c : ℕ → ℂ) {k : ℕ} (hthr : 2 * r * ((X : ℝ) ^ k) ≤ 1) :
    ∫ ξ : ℝ, pairTransform η ξ * (expSum s c logFreq ξ * conj (expSum s c logFreq ξ)) ^ k =
      ((∫ t, ‖η t‖ ^ 2 : ℝ) : ℂ) * ((∫ x, ‖twistSum s c x‖ ^ (2 * k) ∂gaugeHaar : ℝ) : ℂ) := by
  rw [integral_pairTransform_mul_normSq_pow_eq_diag hη hηs hs c hthr,
    integral_normSq_twistSum_pow (fun n hn => by have := (hs n hn).1; omega)]
  push_cast
  rfl

/-! ### Near-incidence is gauge charge -/

/-- The near-incidence form of the twisted source, written against the gauge characters. -/
theorem nearIncidence_twisted (η : ℝ → ℂ) (s : Finset ℕ) (c : ℕ → ℂ) (y : GaugeTorus) :
    nearIncidence η s (twisted y c) =
      ∑ j ∈ s, ∑ k ∈ s.erase j, c j * conj (c k) * EF.weilTest η η (logFreq j - logFreq k) *
        (twist y j * conj (twist y k)) := by
  rw [nearIncidence]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [twisted, map_mul]
  ring

theorem continuous_nearIncidence_twisted (η : ℝ → ℂ) (s : Finset ℕ) (c : ℕ → ℂ) :
    Continuous fun y => nearIncidence η s (twisted y c) := by
  simp_rw [nearIncidence_twisted]
  exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ =>
    continuous_const.mul ((continuous_twist j).mul (Complex.continuous_conj.comp (continuous_twist k)))

/-- **Near-incidence has gauge mean zero.** -/
theorem integral_nearIncidence_twisted (η : ℝ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, n ≠ 0)
    (c : ℕ → ℂ) : ∫ y, nearIncidence η s (twisted y c) ∂gaugeHaar = 0 := by
  simp_rw [nearIncidence_twisted]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
    (integrable_twist_mul_conj _ _).const_mul _]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [integral_finsetSum _ fun k _ => (integrable_twist_mul_conj _ _).const_mul _]
  refine Finset.sum_eq_zero fun k hk => ?_
  obtain ⟨hkj, hk⟩ := Finset.mem_erase.mp hk
  rw [integral_const_mul, integral_twist_mul_conj (hs j hj) (hs k hk), if_neg (Ne.symm hkj),
    mul_zero]

/-- **Near-incidence of every product order has gauge mean zero.** -/
theorem integral_nearIncidence_pow_twisted (η : ℝ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, n ≠ 0)
    (c : ℕ → ℂ) (k : ℕ) :
    ∫ y, nearIncidence η (ArithmeticKunnethTheory.powSupport s k) (powCoeff s (twisted y c) k) ∂gaugeHaar = 0 := by
  have h : ∀ y, powCoeff s (twisted y c) k = twisted y (powCoeff s c k) := fun y =>
    funext fun N => powCoeff_twisted hs y c k N
  simp_rw [h]
  exact integral_nearIncidence_twisted η (fun N hN => ne_zero_of_mem_powSupport hs hN) _

/-- **The gauge-orbit mean of a windowed mean square is its diagonal**, at every length. -/
theorem integral_windowed_twisted {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η)
    {s : Finset ℕ} (hs : ∀ n ∈ s, n ≠ 0) (c : ℕ → ℂ) :
    ∫ y, (∫ ξ : ℝ, pairTransform η ξ *
        (expSum s (twisted y c) logFreq ξ * conj (expSum s (twisted y c) logFreq ξ))) ∂gaugeHaar =
      ((∫ t, ‖η t‖ ^ 2 : ℝ) : ℂ) * ∑ n ∈ s, ((‖c n‖ ^ 2 : ℝ) : ℂ) := by
  have hpt : ∀ y, (∫ ξ : ℝ, pairTransform η ξ *
      (expSum s (twisted y c) logFreq ξ * conj (expSum s (twisted y c) logFreq ξ))) =
        ((∫ t, ‖η t‖ ^ 2 : ℝ) : ℂ) * ∑ n ∈ s, ((‖c n‖ ^ 2 : ℝ) : ℂ) +
          nearIncidence η s (twisted y c) := by
    intro y
    rw [windowed_eq_gauge_add_nearIncidence hη hηc hs, integral_normSq_twistSum hs]
    simp_rw [norm_twisted]
    push_cast
    rfl
  simp_rw [hpt]
  rw [integral_add (integrable_const _)
    ((continuous_nearIncidence_twisted η s c).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)),
    integral_nearIncidence_twisted η hs, integral_const, probReal_univ, one_smul, add_zero]

/-! ### Nonnegative sources maximize near-incidence on their orbit -/

/-- A sum of unimodular characters against nonnegative weights is dominated by the weight total. -/
theorem norm_sum_mul_unimodular_le {ι : Type*} (S : Finset ι) (W u : ι → ℂ) (hW : ∀ i ∈ S, 0 ≤ W i)
    (hu : ∀ i ∈ S, ‖u i‖ = 1) : ‖∑ i ∈ S, W i * u i‖ ≤ (∑ i ∈ S, W i).re := by
  calc ‖∑ i ∈ S, W i * u i‖ ≤ ∑ i ∈ S, ‖W i * u i‖ := norm_sum_le _ _
    _ = ∑ i ∈ S, (W i).re := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [norm_mul, hu i hi, mul_one]
      obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp (hW i hi)
      rw [← Complex.re_add_im (W i), ← him]
      simp [abs_of_nonneg hre]
    _ = (∑ i ∈ S, W i).re := (Complex.re_sum _ _).symm

/-- **Nonnegative sources are the worst case of their gauge orbit.** For nonnegative coefficients
and nonnegative kernel values, every twist has near-incidence of modulus at most the (real,
nonnegative) near-incidence of the source itself. -/
theorem norm_nearIncidence_twisted_le {η : ℝ → ℂ} (hK : ∀ v, 0 ≤ EF.weilTest η η v)
    (s : Finset ℕ) {c : ℕ → ℂ} (hc : ∀ n, 0 ≤ c n) (y : GaugeTorus) :
    0 ≤ nearIncidence η s c ∧ ‖nearIncidence η s (twisted y c)‖ ≤ (nearIncidence η s c).re := by
  have hW : ∀ j k, 0 ≤ c j * conj (c k) * EF.weilTest η η (logFreq j - logFreq k) := by
    intro j k
    have hck : conj (c k) = c k := Complex.conj_eq_iff_re.mpr
      (by rw [← Complex.re_add_im (c k), (Complex.nonneg_iff.mp (hc k)).2.symm]; simp)
    rw [hck]
    exact mul_nonneg (mul_nonneg (hc j) (hc k)) (hK _)
  refine ⟨Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => hW j k, ?_⟩
  rw [nearIncidence_twisted, nearIncidence]
  calc _ ≤ ∑ j ∈ s, ‖∑ k ∈ s.erase j, c j * conj (c k) * EF.weilTest η η (logFreq j - logFreq k) *
        (twist y j * conj (twist y k))‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ s, (∑ k ∈ s.erase j, c j * conj (c k) *
        EF.weilTest η η (logFreq j - logFreq k)).re := by
      refine Finset.sum_le_sum fun j _ => norm_sum_mul_unimodular_le _ _ _ (fun k _ => hW j k)
        fun k _ => ?_
      rw [norm_mul, RCLike.norm_conj, norm_twist, norm_twist, one_mul]
    _ = _ := (Complex.re_sum _ _).symm

end GaloisForLFunctions.ArithmeticCorrelationGeometry
