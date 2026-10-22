import GaloisForLFunctions.RHTower.ThetaPrimeDeletionMellin
import GaloisForLFunctions.RHTower.ThetaTailFirstMomentKreinTransform
import GaloisForLFunctions.RHTower.ThetaEulerAtomMellin
import GaloisForLFunctions.RHTower.ThetaEulerCriticalAtomMoment
import GaloisForLFunctions.RHTower.PrimeArchThetaWardLaplaceHalfDensity
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspKernelLogConcavity
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaAllShiftedTails

/-!
# Prime deletion preserves the Xi divisor while its boundary spectrum escapes

Let `k` be the completed theta source, `h = a_1` its first Gaussian atom and
`k_S = ∏_{p∈S} (1 - p^{-1/2} T_{log p}) k` a finite literal prime deletion.

* `k_S` is the sum of the atoms with labels coprime to `S`, positive on `x ≥ 0`, and
  `L_w k_S = XiC(i w) ∏_{p∈S} (1 - p^{-1/2-w})` for every complex `w`; to the right of
  `Re w = -1/2` its zero orders equal those of `XiC(i w)`.
* Along every exhaustion of the primes `k_{S_j} → h` uniformly on compact sets, whereas
  `L_w h = G(w)` has no zero in the Xi strip; every real Mellin charge with
  `-1/2 < w ≤ 1/2` of `k_{S_j}` tends to `0`, and the residual `k_{S_j} - h` carries the limiting
  ordinary mass `Γ(5/4) π^{-1/4} / 2` entirely at the negative cusp.
* The reflected deletion keeps the interior Xi factor, kills both critical charges, has positive
  mass and therefore changes sign.
* A compactly supported positive symmetric probability translation gauge preserves both mass and
  half-charge only when it is `δ₀`; the two-point gauge shows mass alone is not rigid.
-/

open MeasureTheory Set Filter Topology Complex

namespace RHTower

/-! ## Complex Laplace transform of the deleted source -/

theorem integrable_cexp_mul_thetaCuspFullSource (w : ℂ) :
    Integrable (fun x : ℝ => Complex.exp (w * x) * (thetaCuspFullSource x : ℂ)) :=
  (integrable_thetaBilateralLaplace w).congr
    (Eventually.of_forall fun x => by simp only; ring)

theorem integral_cexp_mul_thetaCuspFullSource (w : ℂ) :
    (∫ x : ℝ, Complex.exp (w * x) * (thetaCuspFullSource x : ℂ)) = XiC (I * w) := by
  rw [← thetaBilateralLaplace_eq_XiC, thetaBilateralLaplace_eq_integral]
  apply integral_congr_ae
  filter_upwards with x
  ring

/-- **Deleted-source Xi factorization.**  For every finite set of positive integers `S` and every
complex `w`, `L_w (D_S k) = XiC(i w) ∏_{p∈S} (1 - p^{-1/2-w})`. -/
theorem integral_cexp_mul_thetaPrimeDeletion_thetaCuspFullSource (S : Finset ℕ)
    (hS : ∀ p ∈ S, 0 < p) (w : ℂ) :
    (∫ x : ℝ, Complex.exp (w * x) * (thetaPrimeDeletion S thetaCuspFullSource x : ℂ)) =
      XiC (I * w) * ∏ p ∈ S, (1 - (p : ℂ) ^ (-(1 / 2 : ℂ) - w)) := by
  rw [(integral_cexp_mul_thetaPrimeDeletion S hS thetaCuspFullSource w
    (integrable_cexp_mul_thetaCuspFullSource w)).2, integral_cexp_mul_thetaCuspFullSource,
    mul_comm]

theorem integrable_cexp_mul_thetaPrimeDeletion_thetaCuspFullSource (S : Finset ℕ)
    (hS : ∀ p ∈ S, 0 < p) (w : ℂ) :
    Integrable (fun x : ℝ =>
      Complex.exp (w * x) * (thetaPrimeDeletion S thetaCuspFullSource x : ℂ)) :=
  (integral_cexp_mul_thetaPrimeDeletion S hS thetaCuspFullSource w
    (integrable_cexp_mul_thetaCuspFullSource w)).1

/-- Every finite Euler factor is zero-free to the right of `Re w = -1/2`. -/
theorem one_sub_natCast_cpow_ne_zero {p : ℕ} (hp : 2 ≤ p) {w : ℂ} (hw : -(1 / 2) < w.re) :
    1 - (p : ℂ) ^ (-(1 / 2 : ℂ) - w) ≠ 0 := by
  intro h
  have h1 : (p : ℂ) ^ (-(1 / 2 : ℂ) - w) = 1 := by linear_combination -h
  have hnorm := congrArg norm h1
  rw [Complex.norm_natCast_cpow_of_pos (by omega), norm_one] at hnorm
  have hre : (-(1 / 2 : ℂ) - w).re < 0 := by simp; linarith
  have hpR : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have := Real.rpow_lt_one_of_one_lt_of_neg hpR hre
  linarith

theorem differentiable_natCast_cpow_neg_half_sub {p : ℕ} (hp : 0 < p) :
    Differentiable ℂ (fun w : ℂ => (p : ℂ) ^ (-(1 / 2 : ℂ) - w)) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  intro w
  exact ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl hp')

/-- **Divisor fidelity with multiplicity.**  To the right of `Re w = -1/2` (in particular in the
whole open Xi strip), every finite literal prime deletion has exactly the analytic zero order of
`w ↦ XiC(i w)`. -/
theorem analyticOrderAt_thetaPrimeDeletion_laplace (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {w₀ : ℂ} (hw₀ : -(1 / 2) < w₀.re) :
    analyticOrderAt (fun w : ℂ => ∫ x : ℝ,
        Complex.exp (w * x) * (thetaPrimeDeletion S thetaCuspFullSource x : ℂ)) w₀ =
      analyticOrderAt (fun w : ℂ => XiC (I * w)) w₀ := by
  have hpos : ∀ p ∈ S, 0 < p := fun p hp => (hS p hp).pos
  have hfun : (fun w : ℂ => ∫ x : ℝ,
      Complex.exp (w * x) * (thetaPrimeDeletion S thetaCuspFullSource x : ℂ)) =
      (fun w : ℂ => XiC (I * w)) * fun w => ∏ p ∈ S, (1 - (p : ℂ) ^ (-(1 / 2 : ℂ) - w)) := by
    funext w
    exact integral_cexp_mul_thetaPrimeDeletion_thetaCuspFullSource S hpos w
  have hXi : AnalyticAt ℂ (fun w : ℂ => XiC (I * w)) w₀ :=
    (XiC_differentiable.comp (differentiable_id.const_mul I)).analyticAt w₀
  have hE : AnalyticAt ℂ (fun w => ∏ p ∈ S, (1 - (p : ℂ) ^ (-(1 / 2 : ℂ) - w))) w₀ := by
    apply Differentiable.analyticAt
    intro w
    have : (fun w => ∏ p ∈ S, (1 - (p : ℂ) ^ (-(1 / 2 : ℂ) - w))) =
        ∏ p ∈ S, fun w => (1 - (p : ℂ) ^ (-(1 / 2 : ℂ) - w)) := by
      funext w
      simp [Finset.prod_apply]
    rw [this]
    apply DifferentiableAt.finsetProd
    intro p hp
    exact (differentiableAt_const _).sub (differentiable_natCast_cpow_neg_half_sub (hpos p hp) w)
  have hE0 : analyticOrderAt (fun w => ∏ p ∈ S, (1 - (p : ℂ) ^ (-(1 / 2 : ℂ) - w))) w₀ = 0 := by
    rw [analyticOrderAt_eq_zero]
    right
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    exact one_sub_natCast_cpow_ne_zero (hS p hp).two_le hw₀
  rw [hfun, analyticOrderAt_mul hXi hE, hE0, add_zero]

/-! ## Positivity of every deleted source on the positive ray -/

private theorem thetaCuspSourceTerm_pos_of_nonneg {x : ℝ} (hx : 0 ≤ x) {m : ℕ} (hm : 0 < m) :
    0 < thetaCuspSourceTerm x m := by
  unfold thetaCuspSourceTerm
  apply mul_pos (Real.exp_pos _)
  apply thetaCuspSeed_pos
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have he : (1 : ℝ) ≤ Real.exp x := Real.one_le_exp hx
  have hprod : (1 : ℝ) ≤ m * Real.exp x := by nlinarith
  have hsq : (1 : ℝ) ≤ (m * Real.exp x) ^ 2 := by nlinarith
  nlinarith [Real.pi_gt_three]

theorem thetaCuspSourceTerm_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) (m : ℕ) :
    0 ≤ thetaCuspSourceTerm x m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [thetaCuspSourceTerm, thetaCuspSeed]
  · exact (thetaCuspSourceTerm_pos_of_nonneg hx hm).le

/-- On the positive ray every finite deletion is a positive sum of actual Gaussian atoms, bounded
between the first atom and the completed source. -/
theorem thetaCuspSourceTerm_one_le_thetaPrimeDeletion (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspSourceTerm x 1 ≤ thetaPrimeDeletion S thetaCuspFullSource x ∧
      thetaPrimeDeletion S thetaCuspFullSource x ≤ thetaCuspFullSource x := by
  rw [thetaPrimeDeletion_thetaCuspFullSource_eq_tsum S hS]
  have hsum := summable_thetaCuspSourceTerm x
  have hnn : ∀ m, 0 ≤ {m : ℕ | ∀ p ∈ S, ¬ p ∣ m}.indicator (thetaCuspSourceTerm x) m :=
    fun m => Set.indicator_nonneg (fun m _ => thetaCuspSourceTerm_nonneg_of_nonneg hx m) m
  constructor
  · have h1 : {m : ℕ | ∀ p ∈ S, ¬ p ∣ m}.indicator (thetaCuspSourceTerm x) 1 =
        thetaCuspSourceTerm x 1 := by
      apply Set.indicator_of_mem
      intro p hp hdiv
      exact (hS p hp).one_lt.ne' (Nat.dvd_one.mp hdiv)
    rw [← h1]
    exact (hsum.indicator _).le_tsum 1 (fun m _ => hnn m)
  · rw [thetaCuspFullSource]
    exact (hsum.indicator _).tsum_le_tsum
      (fun m => Set.indicator_le_self' (fun m _ => thetaCuspSourceTerm_nonneg_of_nonneg hx m) m)
      hsum

theorem thetaPrimeDeletion_pos_of_nonneg (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {x : ℝ} (hx : 0 ≤ x) : 0 < thetaPrimeDeletion S thetaCuspFullSource x :=
  (thetaCuspSourceTerm_pos_of_nonneg hx one_pos).trans_le
    (thetaCuspSourceTerm_one_le_thetaPrimeDeletion S hS hx).1


/-! ## Cofinal deletion converges to the seed on compact sets -/

/-- A sequence of finite prime sets exhausting all primes. -/
structure PrimeExhaustion (S : ℕ → Finset ℕ) : Prop where
  prime : ∀ j, ∀ p ∈ S j, p.Prime
  eventually_mem : ∀ p, p.Prime → ∀ᶠ j in atTop, p ∈ S j

theorem PrimeExhaustion.eventually_not_coprime {S : ℕ → Finset ℕ} (hS : PrimeExhaustion S)
    {m : ℕ} (hm : 2 ≤ m) : ∀ᶠ j in atTop, ¬ ∀ p ∈ S j, ¬ p ∣ m := by
  filter_upwards [hS.eventually_mem (Nat.minFac m) (Nat.minFac_prime (by omega))] with j hj
  intro h
  exact h _ hj (Nat.minFac_dvd m)

/-- The indicator weight of `D_S k - h` on the atom `m`. -/
private theorem thetaPrimeDeletion_sub_seed_eq_tsum (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (x : ℝ) :
    thetaPrimeDeletion S thetaCuspFullSource x - thetaCuspSourceTerm x 1 =
      ∑' m : ℕ, {m : ℕ | 2 ≤ m ∧ ∀ p ∈ S, ¬ p ∣ m}.indicator (thetaCuspSourceTerm x) m := by
  classical
  have hsum := summable_thetaCuspSourceTerm x
  rw [thetaPrimeDeletion_thetaCuspFullSource_eq_tsum S hS]
  have hone : thetaCuspSourceTerm x 1 =
      ∑' m : ℕ, ({1} : Set ℕ).indicator (thetaCuspSourceTerm x) m := by
    rw [tsum_eq_single 1]
    · simp
    · intro m hm
      simp [hm]
  rw [hone, ← (hsum.indicator _).tsum_sub (hsum.indicator _)]
  apply tsum_congr
  intro m
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · simp [thetaCuspSourceTerm, thetaCuspSeed]
    · have h1 : (1 : ℕ) ∈ {m : ℕ | ∀ p ∈ S, ¬ p ∣ m} := by
        intro p hp hdiv
        exact (hS p hp).one_lt.ne' (Nat.dvd_one.mp hdiv)
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem (Set.mem_singleton 1),
        Set.indicator_of_notMem (by simp)]
      ring
  · have hm1 : m ∉ ({1} : Set ℕ) := by simp; omega
    rw [Set.indicator_of_notMem hm1, sub_zero]
    by_cases hc : ∀ p ∈ S, ¬ p ∣ m
    · rw [Set.indicator_of_mem (show m ∈ {m : ℕ | ∀ p ∈ S, ¬ p ∣ m} from hc),
        Set.indicator_of_mem (show m ∈ {m : ℕ | 2 ≤ m ∧ ∀ p ∈ S, ¬ p ∣ m} from ⟨hm, hc⟩)]
    · rw [Set.indicator_of_notMem (show m ∉ {m : ℕ | ∀ p ∈ S, ¬ p ∣ m} from hc),
        Set.indicator_of_notMem (show m ∉ {m : ℕ | 2 ≤ m ∧ ∀ p ∈ S, ¬ p ∣ m} from
          fun h => hc h.2)]

/-- **Compact-local convergence.**  Along every exhaustion of the primes, the literal deleted
sources converge to the first Gaussian atom uniformly on every compact interval. -/
theorem PrimeExhaustion.tendstoUniformlyOn_thetaPrimeDeletion {S : ℕ → Finset ℕ}
    (hS : PrimeExhaustion S) (R : ℝ) :
    TendstoUniformlyOn (fun j => thetaPrimeDeletion (S j) thetaCuspFullSource)
      (fun x => thetaCuspSourceTerm x 1) atTop (Set.Icc (-R) R) := by
  classical
  let B : ℕ → ℕ → ℝ := fun j m =>
    {m : ℕ | 2 ≤ m ∧ ∀ p ∈ S j, ¬ p ∣ m}.indicator (thetaCuspSourceMajorant R) m
  have hB : Tendsto (fun j => ∑' m, B j m) atTop (𝓝 (∑' _m : ℕ, (0 : ℝ))) := by
    apply tendsto_tsum_of_dominated_convergence (summable_thetaCuspSourceMajorant R)
    · intro m
      rcases Nat.lt_or_ge m 2 with hm | hm
      · apply tendsto_const_nhds.congr
        intro j
        simp only [B]
        rw [Set.indicator_of_notMem (fun h => by have := h.1; omega)]
      · apply tendsto_const_nhds.congr'
        filter_upwards [hS.eventually_not_coprime hm] with j hj
        simp only [B]
        rw [Set.indicator_of_notMem (fun h => hj h.2)]
    · filter_upwards with j m
      rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun m _ => thetaCuspSourceMajorant_nonneg R m) m)]
      exact Set.indicator_le_self' (fun m _ => thetaCuspSourceMajorant_nonneg R m) m
  rw [tsum_zero] at hB
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(hB.eventually (gt_mem_nhds hε))] with j hj x hx
  rw [Real.dist_eq, abs_sub_comm, thetaPrimeDeletion_sub_seed_eq_tsum (S j) (hS.prime j)]
  have hsum := summable_thetaCuspSourceTerm x
  calc
    |∑' m : ℕ, {m : ℕ | 2 ≤ m ∧ ∀ p ∈ S j, ¬ p ∣ m}.indicator (thetaCuspSourceTerm x) m| ≤
        ∑' m : ℕ, |{m : ℕ | 2 ≤ m ∧ ∀ p ∈ S j, ¬ p ∣ m}.indicator (thetaCuspSourceTerm x) m| :=
      norm_tsum_le_tsum_norm ((hsum.indicator _).norm)
    _ ≤ ∑' m, B j m := by
      apply ((hsum.indicator _).norm).tsum_le_tsum _
        ((summable_thetaCuspSourceMajorant R).indicator _)
      intro m
      by_cases hmem : m ∈ {m : ℕ | 2 ≤ m ∧ ∀ p ∈ S j, ¬ p ∣ m}
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
        exact abs_thetaCuspSourceTerm_le_majorant hx m
      · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, norm_zero]
    _ < ε := hj

theorem PrimeExhaustion.tendsto_thetaPrimeDeletion {S : ℕ → Finset ℕ}
    (hS : PrimeExhaustion S) (x : ℝ) :
    Tendsto (fun j => thetaPrimeDeletion (S j) thetaCuspFullSource x) atTop
      (𝓝 (thetaCuspSourceTerm x 1)) :=
  (hS.tendstoUniformlyOn_thetaPrimeDeletion |x|).tendsto_at
    ⟨by linarith [neg_abs_le x], le_abs_self x⟩


/-! ## Real Mellin charges of the deleted sources -/

theorem integral_cexp_mul_ofReal_eq_ofReal_integral (w : ℝ) (f : ℝ → ℝ) :
    (∫ x : ℝ, Complex.exp ((w : ℂ) * x) * (f x : ℂ)) =
      ((∫ x : ℝ, Real.exp (w * x) * f x : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with x
  push_cast
  ring

theorem integrable_exp_mul_of_integrable_cexp_mul (w : ℝ) {f : ℝ → ℝ}
    (h : Integrable (fun x : ℝ => Complex.exp ((w : ℂ) * x) * (f x : ℂ))) :
    Integrable (fun x : ℝ => Real.exp (w * x) * f x) := by
  refine h.re.congr (Eventually.of_forall fun x => ?_)
  simp only [RCLike.re_to_complex]
  rw [show Complex.exp ((w : ℂ) * x) * (f x : ℂ) = ((Real.exp (w * x) * f x : ℝ) : ℂ) by
    push_cast; ring, Complex.ofReal_re]

theorem integrable_exp_mul_thetaPrimeDeletion (S : Finset ℕ) (hS : ∀ p ∈ S, 0 < p) (w : ℝ) :
    Integrable (fun x : ℝ => Real.exp (w * x) * thetaPrimeDeletion S thetaCuspFullSource x) :=
  integrable_exp_mul_of_integrable_cexp_mul w
    (integrable_cexp_mul_thetaPrimeDeletion_thetaCuspFullSource S hS w)

/-- Real form of the deletion Mellin law. -/
theorem integral_exp_mul_thetaPrimeDeletion (S : Finset ℕ) (hS : ∀ p ∈ S, 0 < p) (w : ℝ) :
    (∫ x : ℝ, Real.exp (w * x) * thetaPrimeDeletion S thetaCuspFullSource x) =
      (∏ p ∈ S, (1 - (p : ℝ) ^ (-(1 / 2 : ℝ) - w))) *
        ∫ x : ℝ, Real.exp (w * x) * thetaCuspFullSource x := by
  have h := (integral_cexp_mul_thetaPrimeDeletion S hS thetaCuspFullSource (w : ℂ)
    (integrable_cexp_mul_thetaCuspFullSource w)).2
  rw [integral_cexp_mul_ofReal_eq_ofReal_integral, integral_cexp_mul_ofReal_eq_ofReal_integral] at h
  apply Complex.ofReal_injective
  rw [h]
  push_cast
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  rw [Complex.ofReal_cpow (by positivity)]
  push_cast
  rfl

/-- If the prime weights `0 ≤ a_p ≤ 1` have divergent sum, every finite Euler product
`∏_{p∈S_j} (1 - a_p)` along an exhaustion of the primes tends to zero. -/
theorem PrimeExhaustion.tendsto_prod_one_sub {S : ℕ → Finset ℕ} (hS : PrimeExhaustion S)
    {a : ℕ → ℝ} (ha0 : ∀ p, p.Prime → 0 ≤ a p) (ha1 : ∀ p, p.Prime → a p ≤ 1)
    (hdiv : ¬ Summable ({p : ℕ | p.Prime}.indicator a)) :
    Tendsto (fun j => ∏ p ∈ S j, (1 - a p)) atTop (𝓝 0) := by
  classical
  set f := {p : ℕ | p.Prime}.indicator a with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => Set.indicator_nonneg (fun p hp => ha0 p hp) n
  have hpart := (not_summable_iff_tendsto_nat_atTop_of_nonneg hf0).mp hdiv
  have hsumS : Tendsto (fun j => ∑ p ∈ S j, a p) atTop atTop := by
    rw [tendsto_atTop]
    intro M
    obtain ⟨N, hN⟩ := (tendsto_atTop.mp hpart M).exists
    have hev : ∀ᶠ j in atTop, ∀ p ∈ (Finset.range N).filter Nat.Prime, p ∈ S j := by
      rw [Filter.eventually_all_finset]
      intro p hp
      exact hS.eventually_mem p (Finset.mem_filter.mp hp).2
    filter_upwards [hev] with j hj
    calc
      M ≤ ∑ i ∈ Finset.range N, f i := hN
      _ = ∑ p ∈ (Finset.range N).filter Nat.Prime, a p := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        rw [hf, Set.indicator_apply]
        rfl
      _ ≤ ∑ p ∈ S j, a p :=
        Finset.sum_le_sum_of_subset_of_nonneg hj
          (fun p hp _ => ha0 p (hS.prime j p hp))
  have hexp : Tendsto (fun j => Real.exp (-∑ p ∈ S j, a p)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hsumS)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hexp
  · intro j
    exact Finset.prod_nonneg fun p hp => by linarith [ha1 p (hS.prime j p hp)]
  · intro j
    simp only
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp
      linarith [ha1 p (hS.prime j p hp)]
    · intro p _
      linarith [Real.add_one_le_exp (-a p)]

theorem PrimeExhaustion.tendsto_prod_one_sub_rpow {S : ℕ → Finset ℕ} (hS : PrimeExhaustion S)
    {w : ℝ} (hw : -(1 / 2) < w) (hw' : w ≤ 1 / 2) :
    Tendsto (fun j => ∏ p ∈ S j, (1 - (p : ℝ) ^ (-(1 / 2 : ℝ) - w))) atTop (𝓝 0) := by
  apply hS.tendsto_prod_one_sub (a := fun p => (p : ℝ) ^ (-(1 / 2 : ℝ) - w))
  · intro p _
    positivity
  · intro p hp
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp.one_lt.le) (by linarith)
  · intro hsum
    apply not_summable_one_div_on_primes
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hsum
    · exact Set.indicator_nonneg (fun p _ => by positivity) n
    · by_cases hn : n ∈ {p : ℕ | p.Prime}
      · rw [Set.indicator_of_mem hn, Set.indicator_of_mem hn]
        have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (show Nat.Prime n from hn).one_lt.le
        calc
          1 / (n : ℝ) = (n : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, one_div]
          _ ≤ (n : ℝ) ^ (-(1 / 2 : ℝ) - w) :=
            Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
      · rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hn]

/-- **Escaping Mellin charges.**  For `-1/2 < w ≤ 1/2`, every real Mellin observation of the
deleted sources tends to zero along an exhaustion of the primes. -/
theorem PrimeExhaustion.tendsto_integral_exp_mul_thetaPrimeDeletion {S : ℕ → Finset ℕ}
    (hS : PrimeExhaustion S) {w : ℝ} (hw : -(1 / 2) < w) (hw' : w ≤ 1 / 2) :
    Tendsto (fun j => ∫ x : ℝ, Real.exp (w * x) * thetaPrimeDeletion (S j) thetaCuspFullSource x)
      atTop (𝓝 0) := by
  have h := (hS.tendsto_prod_one_sub_rpow hw hw').mul_const
    (∫ x : ℝ, Real.exp (w * x) * thetaCuspFullSource x)
  rw [zero_mul] at h
  refine h.congr (fun j => ?_)
  rw [integral_exp_mul_thetaPrimeDeletion (S j) (fun p hp => (hS.prime j p hp).pos)]

/-- Exact real Mellin transform of the seed `h = a_1`. -/
theorem integral_exp_mul_thetaSeedAtom (w : ℝ) (hw : -(5 / 2) < w) :
    (∫ x : ℝ, Real.exp (w * x) * thetaCuspSourceTerm x 1) =
      (w - 1 / 2) * Real.Gamma (w / 2 + 5 / 4) * Real.pi ^ (-(w / 2 + 1 / 4)) := by
  rw [integral_exp_mul_thetaCuspSourceTerm w hw 1 one_pos]
  simp

/-- The seed has no zero of its real Mellin transform in the Xi strip and is strictly negative
there. -/
theorem integral_exp_mul_thetaSeedAtom_neg {w : ℝ} (hw : -(5 / 2) < w) (hw' : w < 1 / 2) :
    (∫ x : ℝ, Real.exp (w * x) * thetaCuspSourceTerm x 1) < 0 := by
  rw [integral_exp_mul_thetaSeedAtom w hw]
  have hΓ : 0 < Real.Gamma (w / 2 + 5 / 4) := Real.Gamma_pos_of_pos (by linarith)
  have hπ : 0 < Real.pi ^ (-(w / 2 + 1 / 4)) := Real.rpow_pos_of_pos Real.pi_pos _
  have : w - 1 / 2 < 0 := by linarith
  nlinarith [mul_pos hΓ hπ]

/-- **Critical half-charge.**  `L_{1/2} k_S = (1/2) ∏_{p∈S} (1 - 1/p)`. -/
theorem integral_exp_half_mul_thetaPrimeDeletion (S : Finset ℕ) (hS : ∀ p ∈ S, 0 < p) :
    (∫ x : ℝ, Real.exp ((1 / 2 : ℝ) * x) * thetaPrimeDeletion S thetaCuspFullSource x) =
      (1 / 2) * ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
  rw [integral_exp_mul_thetaPrimeDeletion S hS, integral_exp_half_mul_thetaCuspFullSource_eq_half,
    mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro p _
  rw [show -(1 / 2 : ℝ) - 1 / 2 = -1 by norm_num, Real.rpow_neg_one, one_div]

theorem integral_exp_half_mul_thetaSeedAtom :
    (∫ x : ℝ, Real.exp ((1 / 2 : ℝ) * x) * thetaCuspSourceTerm x 1) = 0 := by
  rw [integral_exp_mul_thetaSeedAtom _ (by norm_num)]
  ring

theorem integral_thetaCuspFullSource_pos : 0 < ∫ x : ℝ, thetaCuspFullSource x := by
  have hint : Integrable thetaCuspFullSource := by
    simpa using HedenmalmThetaSource.integrable_exp_mul_thetaCuspFullSource 0
  rw [integral_pos_iff_support_of_nonneg (fun x => (thetaCuspFullSource_pos_all x).le) hint]
  have : Function.support thetaCuspFullSource = Set.univ :=
    Set.eq_univ_of_forall fun x => (thetaCuspFullSource_pos_all x).ne'
  rw [this, Real.volume_univ]
  exact ENNReal.zero_lt_top

/-- **Positive ordinary mass at every finite stage.** -/
theorem integral_thetaPrimeDeletion_pos (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    0 < ∫ x : ℝ, thetaPrimeDeletion S thetaCuspFullSource x := by
  have h := integral_exp_mul_thetaPrimeDeletion S (fun p hp => (hS p hp).pos) 0
  simp only [zero_mul, Real.exp_zero, one_mul, sub_zero] at h
  rw [h]
  apply mul_pos _ integral_thetaCuspFullSource_pos
  apply Finset.prod_pos
  intro p hp
  have h1 : (1 : ℝ) < p := by exact_mod_cast (hS p hp).one_lt
  have := Real.rpow_lt_one_of_one_lt_of_neg h1 (by norm_num : -(1 / 2 : ℝ) < 0)
  linarith


/-! ## The escaped residual mass lives at the negative cusp -/

theorem continuous_thetaCuspSourceTerm (n : ℕ) :
    Continuous (fun x : ℝ => thetaCuspSourceTerm x n) := by
  unfold thetaCuspSourceTerm thetaCuspSeed
  fun_prop

theorem continuous_thetaCuspFullSource : Continuous thetaCuspFullSource :=
  contDiff_thetaCuspFullSource.continuous

theorem continuous_thetaPrimeDeletion (S : Finset ℕ) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (thetaPrimeDeletion S f) := by
  unfold thetaPrimeDeletion
  fun_prop

private theorem integrable_thetaCuspFullSource : Integrable thetaCuspFullSource := by
  simpa using HedenmalmThetaSource.integrable_exp_mul_thetaCuspFullSource 0

theorem integrable_thetaCuspSourceTerm_one : Integrable (fun x : ℝ => thetaCuspSourceTerm x 1) := by
  have h := integrable_exp_mul_of_integrable_cexp_mul 0
    (integrable_cexp_mul_thetaCuspSourceTerm ((0 : ℝ) : ℂ) (by simp) 1 one_pos)
  simpa using h

theorem integrable_thetaPrimeDeletion (S : Finset ℕ) (hS : ∀ p ∈ S, 0 < p) :
    Integrable (thetaPrimeDeletion S thetaCuspFullSource) := by
  simpa using integrable_exp_mul_thetaPrimeDeletion S hS 0

/-- A deletion-uniform compact bound for the residual `D_S k - h`. -/
theorem abs_thetaPrimeDeletion_sub_seed_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {R x : ℝ}
    (hx : x ∈ Set.Icc (-R) R) :
    |thetaPrimeDeletion S thetaCuspFullSource x - thetaCuspSourceTerm x 1| ≤
      ∑' m, thetaCuspSourceMajorant R m := by
  rw [thetaPrimeDeletion_sub_seed_eq_tsum S hS]
  have hsum := summable_thetaCuspSourceTerm x
  calc
    |∑' m : ℕ, {m : ℕ | 2 ≤ m ∧ ∀ p ∈ S, ¬ p ∣ m}.indicator (thetaCuspSourceTerm x) m| ≤
        ∑' m : ℕ, |{m : ℕ | 2 ≤ m ∧ ∀ p ∈ S, ¬ p ∣ m}.indicator (thetaCuspSourceTerm x) m| :=
      norm_tsum_le_tsum_norm ((hsum.indicator _).norm)
    _ ≤ ∑' m, thetaCuspSourceMajorant R m := by
      apply ((hsum.indicator _).norm).tsum_le_tsum _ (summable_thetaCuspSourceMajorant R)
      intro m
      by_cases hmem : m ∈ {m : ℕ | 2 ≤ m ∧ ∀ p ∈ S, ¬ p ∣ m}
      · rw [Set.indicator_of_mem hmem]
        exact abs_thetaCuspSourceTerm_le_majorant hx m
      · rw [Set.indicator_of_notMem hmem, norm_zero]
        exact thetaCuspSourceMajorant_nonneg R m

/-- **No escaped mass on any right-closed ray.**  For every fixed `R`, the residual integral of
`k_{S_j} - h` over `[-R, ∞)` tends to zero. -/
theorem PrimeExhaustion.tendsto_setIntegral_Ici_thetaPrimeDeletion_sub_seed
    {S : ℕ → Finset ℕ} (hS : PrimeExhaustion S) (R : ℝ) :
    Tendsto (fun j => ∫ x in Set.Ici (-R),
        (thetaPrimeDeletion (S j) thetaCuspFullSource x - thetaCuspSourceTerm x 1))
      atTop (𝓝 0) := by
  set R' := |R|
  set C := ∑' m, thetaCuspSourceMajorant R' m
  have hC : 0 ≤ C := tsum_nonneg fun m => thetaCuspSourceMajorant_nonneg R' m
  let bound : ℝ → ℝ := fun x => (Set.Icc (-R') 0).indicator (fun _ => C) x +
    (thetaCuspFullSource x + |thetaCuspSourceTerm x 1|)
  have hbound : Integrable bound (volume.restrict (Set.Ici (-R))) := by
    apply Integrable.integrableOn
    apply Integrable.add
    · exact (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
    · exact integrable_thetaCuspFullSource.add integrable_thetaCuspSourceTerm_one.abs
  have hlim : (∫ _x in Set.Ici (-R), (0 : ℝ)) = 0 := integral_zero _ _
  rw [← hlim]
  apply tendsto_integral_of_dominated_convergence bound
  · intro j
    exact ((continuous_thetaPrimeDeletion (S j) continuous_thetaCuspFullSource).sub
      (continuous_thetaCuspSourceTerm 1)).aestronglyMeasurable
  · exact hbound
  · intro j
    rw [ae_restrict_iff' measurableSet_Ici]
    filter_upwards with x hx
    rw [Real.norm_eq_abs]
    have hkpos := (thetaCuspFullSource_pos_all x).le
    by_cases hx0 : x ≤ 0
    · have hmem : x ∈ Set.Icc (-R') 0 :=
        ⟨le_trans (neg_le_neg (le_abs_self R)) (Set.mem_Ici.mp hx), hx0⟩
      have hmem' : x ∈ Set.Icc (-R') R' := ⟨hmem.1, hx0.trans (abs_nonneg R)⟩
      simp only [bound, Set.indicator_of_mem hmem]
      have := abs_thetaPrimeDeletion_sub_seed_le (S j) (hS.prime j) hmem'
      have habs := abs_nonneg (thetaCuspSourceTerm x 1)
      linarith
    · have hx0' : 0 ≤ x := le_of_lt (not_le.mp hx0)
      have hmem : x ∉ Set.Icc (-R') 0 := fun h => hx0 h.2
      simp only [bound, Set.indicator_of_notMem hmem, zero_add]
      obtain ⟨h1, h2⟩ := thetaCuspSourceTerm_one_le_thetaPrimeDeletion (S j) (hS.prime j) hx0'
      have hD := (thetaPrimeDeletion_pos_of_nonneg (S j) (hS.prime j) hx0').le
      calc
        |thetaPrimeDeletion (S j) thetaCuspFullSource x - thetaCuspSourceTerm x 1| ≤
            |thetaPrimeDeletion (S j) thetaCuspFullSource x| + |thetaCuspSourceTerm x 1| :=
          abs_sub _ _
        _ ≤ thetaCuspFullSource x + |thetaCuspSourceTerm x 1| := by
          rw [abs_of_nonneg hD]
          linarith
  · filter_upwards with x
    have h := (hS.tendsto_thetaPrimeDeletion x).sub_const (thetaCuspSourceTerm x 1)
    rwa [sub_self] at h

/-- **The escaped half-seed mass.**  The full ordinary residual integral tends to
`Γ(5/4) π^{-1/4} / 2 > 0`; by the previous theorem it is carried by the negative cusp. -/
theorem PrimeExhaustion.tendsto_integral_thetaPrimeDeletion_sub_seed
    {S : ℕ → Finset ℕ} (hS : PrimeExhaustion S) :
    Tendsto (fun j => ∫ x : ℝ,
        (thetaPrimeDeletion (S j) thetaCuspFullSource x - thetaCuspSourceTerm x 1))
      atTop (𝓝 (Real.Gamma (5 / 4) * Real.pi ^ (-(1 / 4 : ℝ)) / 2)) := by
  have hseed := integral_exp_mul_thetaSeedAtom 0 (by norm_num)
  simp only [zero_mul, Real.exp_zero, one_mul, zero_div, zero_add] at hseed
  have hmass := hS.tendsto_integral_exp_mul_thetaPrimeDeletion (w := 0) (by norm_num)
    (by norm_num)
  simp only [zero_mul, Real.exp_zero, one_mul] at hmass
  have h := hmass.sub_const (∫ x : ℝ, thetaCuspSourceTerm x 1)
  rw [hseed] at h
  convert h using 1
  · funext j
    rw [integral_sub (integrable_thetaPrimeDeletion (S j) fun p hp => (hS.prime j p hp).pos)
      integrable_thetaCuspSourceTerm_one, hseed]
  · ring_nf

/-! ## Reflected single-prime deletion -/

/-- The reflected deletion `(1 - p^{-1/2} T_{log p})(1 - p^{-1/2} T_{-log p})`. -/
noncomputable def thetaSymmetricPrimeDeletion (p : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 + 1 / (p : ℝ)) * f x -
    (p : ℝ) ^ (-(1 / 2 : ℝ)) * (f (x + Real.log p) + f (x - Real.log p))

theorem thetaSymmetricPrimeDeletion_eq_comp {p : ℕ} (hp : 0 < p) (f : ℝ → ℝ) (x : ℝ) :
    thetaSymmetricPrimeDeletion p f x =
      thetaPrimeDeletion {p} f x -
        (p : ℝ) ^ (-(1 / 2 : ℝ)) * thetaPrimeDeletion {p} f (x - Real.log p) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have h1 : thetaPrimeDeletion {p} f = fun y => f y - (p : ℝ) ^ (-(1 / 2 : ℝ)) * f (y + Real.log p) := by
    funext y
    rw [show ({p} : Finset ℕ) = insert p ∅ by rfl,
      thetaPrimeDeletion_insert hp (by simp) (by simp), thetaPrimeDeletion_empty]
  rw [h1, thetaSymmetricPrimeDeletion]
  simp only
  rw [sub_add_cancel]
  have hsq : (p : ℝ) ^ (-(1 / 2 : ℝ)) * (p : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / (p : ℝ) := by
    rw [← Real.rpow_add hpR]
    norm_num [Real.rpow_neg_one]
  linear_combination (-(f x)) * hsq

theorem thetaSymmetricPrimeDeletion_neg (p : ℕ) (x : ℝ) :
    thetaSymmetricPrimeDeletion p thetaCuspFullSource (-x) =
      thetaSymmetricPrimeDeletion p thetaCuspFullSource x := by
  unfold thetaSymmetricPrimeDeletion
  rw [thetaCuspFullSource_neg, show -x + Real.log p = -(x - Real.log p) by ring,
    show -x - Real.log p = -(x + Real.log p) by ring, thetaCuspFullSource_neg,
    thetaCuspFullSource_neg]
  ring

private theorem natCast_cpow_eq_cexp' {n : ℕ} (hn : 0 < n) (z : ℂ) :
    (n : ℂ) ^ z = Complex.exp (z * (Real.log n : ℂ)) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Complex.cpow_def_of_ne_zero hn', mul_comm]
  congr 2
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_cast, ← Complex.ofReal_log (by positivity)]

private theorem symmetric_factor_identity (L w : ℂ) :
    (1 + Complex.exp (-L)) - Complex.exp (-(1 / 2) * L) *
        (Complex.exp (-(w * L)) + Complex.exp (-(w * -L))) =
      (1 - Complex.exp ((-(1 / 2) - w) * L)) * (1 - Complex.exp ((-(1 / 2) + w) * L)) := by
  have e1 : Complex.exp (-L) = Complex.exp (-(1 / 2) * L) * Complex.exp (-(1 / 2) * L) := by
    rw [← Complex.exp_add]; ring_nf
  have e2 : Complex.exp ((-(1 / 2) - w) * L) =
      Complex.exp (-(1 / 2) * L) * Complex.exp (-(w * L)) := by
    rw [← Complex.exp_add]; ring_nf
  have e3 : Complex.exp ((-(1 / 2) + w) * L) =
      Complex.exp (-(1 / 2) * L) * Complex.exp (-(w * -L)) := by
    rw [← Complex.exp_add]; ring_nf
  have e4 : Complex.exp (-(w * L)) * Complex.exp (-(w * -L)) = 1 := by
    rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
  rw [e1, e2, e3]
  linear_combination (-(Complex.exp (-(1 / 2) * L)) ^ 2) * e4

private theorem cexp_mul_thetaSymmetricPrimeDeletion_eq (p : ℕ) (w : ℂ) :
    (fun x : ℝ => Complex.exp (w * x) *
      (thetaSymmetricPrimeDeletion p thetaCuspFullSource x : ℂ)) =
      fun x : ℝ => ((1 + 1 / (p : ℝ) : ℝ) : ℂ) *
          (Complex.exp (w * x) * (thetaCuspFullSource x : ℂ)) -
        (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          (Complex.exp (w * x) * (thetaCuspFullSource (x + Real.log p) : ℂ) +
            Complex.exp (w * x) * (thetaCuspFullSource (x + -Real.log p) : ℂ)) := by
  funext x
  unfold thetaSymmetricPrimeDeletion
  rw [← sub_eq_add_neg]
  push_cast
  ring

theorem integrable_cexp_mul_thetaSymmetricPrimeDeletion (p : ℕ) (w : ℂ) :
    Integrable (fun x : ℝ => Complex.exp (w * x) *
      (thetaSymmetricPrimeDeletion p thetaCuspFullSource x : ℂ)) := by
  have hk := integrable_cexp_mul_thetaCuspFullSource w
  have hplus := integrable_cexp_mul_comp_add (Real.log p)
    (G := fun y => (thetaCuspFullSource y : ℂ)) hk
  have hminus := integrable_cexp_mul_comp_add (-Real.log p)
    (G := fun y => (thetaCuspFullSource y : ℂ)) hk
  have hsum : Integrable (fun x : ℝ =>
      Complex.exp (w * x) * (thetaCuspFullSource (x + Real.log p) : ℂ) +
        Complex.exp (w * x) * (thetaCuspFullSource (x + -Real.log p) : ℂ)) := hplus.add hminus
  rw [cexp_mul_thetaSymmetricPrimeDeletion_eq]
  exact (hk.const_mul _).sub (hsum.const_mul _)

/-- **Reflected deletion keeps the interior Xi factor and kills both endpoint charges.** -/
theorem integral_cexp_mul_thetaSymmetricPrimeDeletion {p : ℕ} (hp : 0 < p) (w : ℂ) :
    (∫ x : ℝ, Complex.exp (w * x) *
        (thetaSymmetricPrimeDeletion p thetaCuspFullSource x : ℂ)) =
      XiC (I * w) * ((1 - (p : ℂ) ^ (-(1 / 2 : ℂ) - w)) *
        (1 - (p : ℂ) ^ (-(1 / 2 : ℂ) + w))) := by
  have hk := integrable_cexp_mul_thetaCuspFullSource w
  have hplus := integrable_cexp_mul_comp_add (Real.log p)
    (G := fun y => (thetaCuspFullSource y : ℂ)) hk
  have hminus := integrable_cexp_mul_comp_add (-Real.log p)
    (G := fun y => (thetaCuspFullSource y : ℂ)) hk
  have hfun : (fun x : ℝ => Complex.exp (w * x) *
      (thetaSymmetricPrimeDeletion p thetaCuspFullSource x : ℂ)) =
      fun x : ℝ => ((1 + 1 / (p : ℝ) : ℝ) : ℂ) *
          (Complex.exp (w * x) * (thetaCuspFullSource x : ℂ)) -
        (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          (Complex.exp (w * x) * (thetaCuspFullSource (x + Real.log p) : ℂ) +
            Complex.exp (w * x) * (thetaCuspFullSource (x + -Real.log p) : ℂ)) := by
    funext x
    unfold thetaSymmetricPrimeDeletion
    rw [← sub_eq_add_neg]
    push_cast
    ring
  have hsum : Integrable (fun x : ℝ =>
      Complex.exp (w * x) * (thetaCuspFullSource (x + Real.log p) : ℂ) +
        Complex.exp (w * x) * (thetaCuspFullSource (x + -Real.log p) : ℂ)) := hplus.add hminus
  rw [hfun, integral_sub (hk.const_mul _) (hsum.const_mul _), integral_const_mul,
    integral_const_mul, integral_add hplus hminus,
    integral_cexp_mul_comp_add w (Real.log p) (fun y => (thetaCuspFullSource y : ℂ)),
    integral_cexp_mul_comp_add w (-Real.log p) (fun y => (thetaCuspFullSource y : ℂ)),
    integral_cexp_mul_thetaCuspFullSource]
  have hpC : (p : ℂ) = Complex.exp (Real.log p : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log (by exact_mod_cast hp), Complex.ofReal_natCast]
  have hconst : ((1 + 1 / (p : ℝ) : ℝ) : ℂ) = 1 + Complex.exp (-(Real.log p : ℂ)) := by
    rw [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_natCast, hpC, Complex.exp_neg, one_div]
  have hhalf : (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
      Complex.exp (-(1 / 2) * (Real.log p : ℂ)) := by
    rw [Complex.ofReal_cpow (by positivity), Complex.ofReal_natCast, natCast_cpow_eq_cexp' hp]
    congr 1
    simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [hconst, hhalf, natCast_cpow_eq_cexp' hp, natCast_cpow_eq_cexp' hp, Complex.ofReal_neg,
    ← symmetric_factor_identity (Real.log p : ℂ) w]
  ring


theorem integral_exp_mul_thetaSymmetricPrimeDeletion {p : ℕ} (hp : 0 < p) (w : ℝ) :
    (∫ x : ℝ, Real.exp (w * x) * thetaSymmetricPrimeDeletion p thetaCuspFullSource x) =
      ((1 - (p : ℝ) ^ (-(1 / 2 : ℝ) - w)) * (1 - (p : ℝ) ^ (-(1 / 2 : ℝ) + w))) *
        ∫ x : ℝ, Real.exp (w * x) * thetaCuspFullSource x := by
  have h := integral_cexp_mul_thetaSymmetricPrimeDeletion hp (w : ℂ)
  rw [integral_cexp_mul_ofReal_eq_ofReal_integral, ← integral_cexp_mul_thetaCuspFullSource,
    integral_cexp_mul_ofReal_eq_ofReal_integral] at h
  apply Complex.ofReal_injective
  rw [h]
  push_cast
  rw [Complex.ofReal_cpow (by positivity), Complex.ofReal_cpow (by positivity)]
  push_cast
  ring

/-- Both reflected Euler factors are zero-free on the open Xi strip. -/
theorem thetaSymmetricPrimeDeletion_factor_ne_zero {p : ℕ} (hp : 2 ≤ p) {w : ℂ}
    (hw : |w.re| < 1 / 2) :
    (1 - (p : ℂ) ^ (-(1 / 2 : ℂ) - w)) * (1 - (p : ℂ) ^ (-(1 / 2 : ℂ) + w)) ≠ 0 := by
  have h1 := one_sub_natCast_cpow_ne_zero hp (w := w) (by linarith [neg_abs_le w.re])
  have h2 := one_sub_natCast_cpow_ne_zero hp (w := -w)
    (by simp; linarith [le_abs_self w.re])
  rw [show -(1 / 2 : ℂ) - -w = -(1 / 2 : ℂ) + w by ring] at h2
  exact mul_ne_zero h1 h2

/-- Both critical endpoint charges of the reflected deletion vanish. -/
theorem thetaSymmetricPrimeDeletion_charges_zero {p : ℕ} (hp : 0 < p) :
    (∫ x : ℝ, Real.exp ((1 / 2 : ℝ) * x) *
        thetaSymmetricPrimeDeletion p thetaCuspFullSource x) = 0 ∧
      (∫ x : ℝ, Real.exp ((-(1 / 2) : ℝ) * x) *
        thetaSymmetricPrimeDeletion p thetaCuspFullSource x) = 0 := by
  constructor
  · rw [integral_exp_mul_thetaSymmetricPrimeDeletion hp,
      show -(1 / 2 : ℝ) + 1 / 2 = 0 by norm_num, Real.rpow_zero]
    ring
  · rw [integral_exp_mul_thetaSymmetricPrimeDeletion hp,
      show -(1 / 2 : ℝ) - -(1 / 2) = 0 by norm_num, Real.rpow_zero]
    ring

/-- The reflected deletion has strictly positive ordinary mass `(1 - p^{-1/2})² ∫ k`. -/
theorem integral_thetaSymmetricPrimeDeletion {p : ℕ} (hp : 0 < p) :
    (∫ x : ℝ, thetaSymmetricPrimeDeletion p thetaCuspFullSource x) =
      (1 - (p : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 * ∫ x : ℝ, thetaCuspFullSource x := by
  have h := integral_exp_mul_thetaSymmetricPrimeDeletion hp 0
  simp only [zero_mul, Real.exp_zero, one_mul, sub_zero, add_zero] at h
  rw [h]
  ring

theorem integral_thetaSymmetricPrimeDeletion_pos {p : ℕ} (hp : 2 ≤ p) :
    0 < ∫ x : ℝ, thetaSymmetricPrimeDeletion p thetaCuspFullSource x := by
  rw [integral_thetaSymmetricPrimeDeletion (by omega)]
  have h1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hlt := Real.rpow_lt_one_of_one_lt_of_neg h1 (by norm_num : -(1 / 2 : ℝ) < 0)
  have hne : 1 - (p : ℝ) ^ (-(1 / 2 : ℝ)) ≠ 0 := by linarith
  exact mul_pos (pow_pos (by linarith) 2) integral_thetaCuspFullSource_pos

theorem continuous_thetaSymmetricPrimeDeletion (p : ℕ) :
    Continuous (thetaSymmetricPrimeDeletion p thetaCuspFullSource) := by
  unfold thetaSymmetricPrimeDeletion
  have := continuous_thetaCuspFullSource
  fun_prop

/-- **Reflection plus divisor fidelity forces a sign change.**  The reflected deletion takes a
strictly negative value somewhere. -/
theorem exists_thetaSymmetricPrimeDeletion_neg {p : ℕ} (hp : 2 ≤ p) :
    ∃ x : ℝ, thetaSymmetricPrimeDeletion p thetaCuspFullSource x < 0 := by
  by_contra hcon
  push Not at hcon
  have hp0 : 0 < p := by omega
  set f := thetaSymmetricPrimeDeletion p thetaCuspFullSource
  have hcont : Continuous fun x : ℝ => Real.exp ((1 / 2 : ℝ) * x) * f x :=
    (by fun_prop : Continuous fun x : ℝ => Real.exp ((1 / 2 : ℝ) * x)).mul
      (continuous_thetaSymmetricPrimeDeletion p)
  have hint : Integrable fun x : ℝ => Real.exp ((1 / 2 : ℝ) * x) * f x :=
    integrable_exp_mul_of_integrable_cexp_mul (1 / 2) (integrable_cexp_mul_thetaSymmetricPrimeDeletion p _)
  have hnn : 0 ≤ fun x : ℝ => Real.exp ((1 / 2 : ℝ) * x) * f x :=
    fun x => mul_nonneg (Real.exp_pos _).le (hcon x)
  have hzero := (integral_eq_zero_iff_of_nonneg hnn hint).mp
    (thetaSymmetricPrimeDeletion_charges_zero hp0).1
  have hzero' := (Continuous.ae_eq_iff_eq volume hcont continuous_const).mp hzero
  have hf0 : ∀ x, f x = 0 := fun x => by
    have := congrFun hzero' x
    exact (mul_eq_zero.mp this).resolve_left (Real.exp_pos _).ne'
  have hpos : 0 < ∫ x : ℝ, f x := integral_thetaSymmetricPrimeDeletion_pos hp
  have hint0 : (∫ x : ℝ, f x) = 0 := by simp [hf0]
  linarith


/-! ## Mass and half-charge rigidify positive symmetric translation gauges -/

/-- The translation mixture `(μ * k)(x) = ∫ k(x - t) dμ(t)`. -/
noncomputable def thetaTranslationMixture (μ : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ t, thetaCuspFullSource (x - t) ∂μ

theorem integral_exp_mul_comp_sub (w c : ℝ) (f : ℝ → ℝ) :
    (∫ x : ℝ, Real.exp (w * x) * f (x - c)) = Real.exp (w * c) * ∫ y : ℝ, Real.exp (w * y) * f y := by
  have h := integral_sub_right_eq_self (μ := volume) (fun y : ℝ => Real.exp (w * y) * f y) c
  rw [← h, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [← mul_assoc, ← Real.exp_add]
  ring_nf

theorem integrable_exp_mul_thetaCuspFullSource_real (w : ℝ) :
    Integrable (fun x : ℝ => Real.exp (w * x) * thetaCuspFullSource x) :=
  HedenmalmThetaSource.integrable_exp_mul_thetaCuspFullSource w

private theorem ae_mem_Icc_of_compl_zero {μ : Measure ℝ} {A : ℝ} (hA : μ (Set.Icc (-A) A)ᶜ = 0) :
    ∀ᵐ t ∂μ, t ∈ Set.Icc (-A) A := by
  rw [ae_iff]
  exact hA

private theorem integrable_exp_of_compact {μ : Measure ℝ} [IsFiniteMeasure μ] {A : ℝ}
    (hA : μ (Set.Icc (-A) A)ᶜ = 0) (w : ℝ) :
    Integrable (fun t : ℝ => Real.exp (w * t)) μ := by
  apply Integrable.mono' (integrable_const (Real.exp (|w| * A)))
    (by fun_prop : Continuous fun t : ℝ => Real.exp (w * t)).aestronglyMeasurable
  filter_upwards [ae_mem_Icc_of_compl_zero hA] with t ht
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have : |t| ≤ A := abs_le.mpr ⟨ht.1, ht.2⟩
  calc w * t ≤ |w * t| := le_abs_self _
    _ = |w| * |t| := abs_mul _ _
    _ ≤ |w| * A := mul_le_mul_of_nonneg_left this (abs_nonneg w)

/-- Translation mixtures multiply every real Mellin charge by the measure's Laplace value. -/
theorem integral_exp_mul_thetaTranslationMixture {μ : Measure ℝ} [IsFiniteMeasure μ] {A : ℝ}
    (hA : μ (Set.Icc (-A) A)ᶜ = 0) (w : ℝ) :
    (∫ x : ℝ, Real.exp (w * x) * thetaTranslationMixture μ x) =
      (∫ t, Real.exp (w * t) ∂μ) * ∫ x : ℝ, Real.exp (w * x) * thetaCuspFullSource x := by
  set L := ∫ x : ℝ, Real.exp (w * x) * thetaCuspFullSource x
  let F : ℝ → ℝ → ℝ := fun x t => Real.exp (w * x) * thetaCuspFullSource (x - t)
  have hinner : ∀ t, (∫ x : ℝ, F x t) = Real.exp (w * t) * L := fun t =>
    integral_exp_mul_comp_sub w t thetaCuspFullSource
  have hFint : Integrable (Function.uncurry F) (volume.prod μ) := by
    have hcont : Continuous (Function.uncurry F) := by
      have := continuous_thetaCuspFullSource
      simp only [F, Function.uncurry_def]
      fun_prop
    rw [integrable_prod_iff' hcont.aestronglyMeasurable]
    constructor
    · filter_upwards with t
      simp only [Function.uncurry_apply_pair, F]
      have h := ((integrable_exp_mul_thetaCuspFullSource_real w).comp_sub_right t).const_mul
        (Real.exp (w * t))
      refine h.congr (Eventually.of_forall fun x => ?_)
      simp only
      rw [← mul_assoc, ← Real.exp_add]
      ring_nf
    · have hnorm : ∀ t, (∫ x : ℝ, ‖Function.uncurry F (x, t)‖) = Real.exp (w * t) * L := by
        intro t
        rw [← hinner t]
        apply integral_congr_ae
        filter_upwards with x
        simp only [Function.uncurry_apply_pair, F, Real.norm_eq_abs]
        exact abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (thetaCuspFullSource_pos_all _).le)
      simp_rw [hnorm]
      exact (integrable_exp_of_compact hA w).mul_const L
  calc
    (∫ x : ℝ, Real.exp (w * x) * thetaTranslationMixture μ x) = ∫ x : ℝ, ∫ t, F x t ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [thetaTranslationMixture, ← integral_const_mul]
    _ = ∫ t, (∫ x : ℝ, F x t) ∂μ := integral_integral_swap hFint
    _ = ∫ t, Real.exp (w * t) * L ∂μ := by simp_rw [hinner]
    _ = (∫ t, Real.exp (w * t) ∂μ) * L := integral_mul_const L _

/-- Symmetry turns the half-density Laplace value into the `cosh` average. -/
theorem integral_exp_half_eq_integral_cosh {μ : Measure ℝ} [IsFiniteMeasure μ] {A : ℝ}
    (hA : μ (Set.Icc (-A) A)ᶜ = 0) (hsymm : μ.map Neg.neg = μ) :
    (∫ t, Real.exp ((1 / 2 : ℝ) * t) ∂μ) = ∫ t, Real.cosh (t / 2) ∂μ := by
  have hneg : (∫ t, Real.exp ((-(1 / 2) : ℝ) * t) ∂μ) = ∫ t, Real.exp ((1 / 2 : ℝ) * t) ∂μ := by
    conv_rhs => rw [← hsymm]
    rw [integral_map measurable_neg.aemeasurable
      (by fun_prop : Continuous fun t : ℝ => Real.exp ((1 / 2 : ℝ) * t)).aestronglyMeasurable]
    congr 1
    funext t
    ring_nf
  have hcosh : (fun t : ℝ => Real.cosh (t / 2)) = fun t =>
      (1 / 2 : ℝ) * (Real.exp ((1 / 2 : ℝ) * t) + Real.exp ((-(1 / 2) : ℝ) * t)) := by
    funext t
    rw [Real.cosh_eq]
    ring_nf
  rw [hcosh, integral_const_mul, integral_add (integrable_exp_of_compact hA _)
    (integrable_exp_of_compact hA _), hneg]
  ring

theorem measure_eq_dirac_zero_of_ae {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : ∀ᵐ t ∂μ, t = 0) : μ = Measure.dirac 0 := by
  have hset : ({0} : Set ℝ)ᶜ = {a : ℝ | ¬ a = 0} := by
    ext a
    simp
  have hc : μ ({0} : Set ℝ)ᶜ = 0 := by
    rw [hset, ← ae_iff]
    exact h
  ext s hs
  rw [Measure.dirac_apply' _ hs]
  by_cases h0 : (0 : ℝ) ∈ s
  · rw [Set.indicator_of_mem h0, Pi.one_apply]
    have hsub : sᶜ ⊆ ({0} : Set ℝ)ᶜ := fun t ht htz => ht (by
      rw [Set.mem_singleton_iff] at htz
      rw [htz]
      exact h0)
    exact (prob_compl_eq_zero_iff hs).mp (measure_mono_null hsub hc)
  · rw [Set.indicator_of_notMem h0]
    have hsub : s ⊆ ({0} : Set ℝ)ᶜ := fun t ht htz => h0 (by
      rw [Set.mem_singleton_iff] at htz
      rw [htz] at ht
      exact ht)
    exact measure_mono_null hsub hc

/-- **Positive-convolution rigidity.**  A compactly supported positive symmetric probability
translation gauge of the completed theta source keeps its ordinary mass automatically, multiplies
its critical half-charge by `∫ cosh(t/2) dμ ≥ 1`, and preserves that half-charge only for
`μ = δ₀`. -/
theorem thetaTranslationMixture_rigidity {μ : Measure ℝ} [IsProbabilityMeasure μ] {A : ℝ}
    (hA : μ (Set.Icc (-A) A)ᶜ = 0) (hsymm : μ.map Neg.neg = μ) :
    (∫ x : ℝ, thetaTranslationMixture μ x) = (∫ x : ℝ, thetaCuspFullSource x) ∧
      (∫ x : ℝ, Real.exp ((1 / 2 : ℝ) * x) * thetaTranslationMixture μ x) =
        (∫ t, Real.cosh (t / 2) ∂μ) * (1 / 2) ∧
      1 ≤ ∫ t, Real.cosh (t / 2) ∂μ ∧
      ((∫ x : ℝ, Real.exp ((1 / 2 : ℝ) * x) * thetaTranslationMixture μ x) =
          ∫ x : ℝ, Real.exp ((1 / 2 : ℝ) * x) * thetaCuspFullSource x →
        μ = Measure.dirac 0 ∧ thetaTranslationMixture μ = thetaCuspFullSource) := by
  have hmass := integral_exp_mul_thetaTranslationMixture hA 0
  simp only [zero_mul, Real.exp_zero, one_mul, integral_const, probReal_univ,
    smul_eq_mul] at hmass
  have hhalf := integral_exp_mul_thetaTranslationMixture hA (1 / 2)
  rw [integral_exp_half_eq_integral_cosh hA hsymm,
    integral_exp_half_mul_thetaCuspFullSource_eq_half] at hhalf
  have hcint : Integrable (fun t : ℝ => Real.cosh (t / 2)) μ := by
    have h := ((integrable_exp_of_compact hA (1 / 2)).add
      (integrable_exp_of_compact hA (-(1 / 2)))).const_mul (1 / 2 : ℝ)
    refine h.congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply]
    rw [Real.cosh_eq]
    ring_nf
  have hge : 1 ≤ ∫ t, Real.cosh (t / 2) ∂μ := by
    have h1 : (∫ _t, (1 : ℝ) ∂μ) = 1 := by simp
    rw [← h1]
    exact integral_mono (integrable_const 1) hcint fun t => Real.one_le_cosh _
  refine ⟨by simpa using hmass, hhalf, hge, fun heq => ?_⟩
  rw [hhalf, integral_exp_half_mul_thetaCuspFullSource_eq_half] at heq
  have hcosh1 : (∫ t, Real.cosh (t / 2) ∂μ) = 1 := by linarith
  have hzero : (∫ t, (Real.cosh (t / 2) - 1) ∂μ) = 0 := by
    rw [integral_sub hcint (integrable_const 1), hcosh1]
    simp
  have hnn : 0 ≤ fun t : ℝ => Real.cosh (t / 2) - 1 := fun t => by
    simp only [Pi.zero_apply]
    linarith [Real.one_le_cosh (t / 2)]
  have hae := (integral_eq_zero_iff_of_nonneg hnn (hcint.sub (integrable_const 1))).mp hzero
  have ht0 : ∀ᵐ t ∂μ, t = 0 := by
    filter_upwards [hae] with t ht
    simp only [Pi.zero_apply] at ht
    by_contra hne
    have := Real.one_lt_cosh.mpr (div_ne_zero hne two_ne_zero)
    linarith
  have hdirac := measure_eq_dirac_zero_of_ae ht0
  refine ⟨hdirac, ?_⟩
  funext x
  rw [thetaTranslationMixture, hdirac, integral_dirac, sub_zero]


/-! ## The seed transform has no zero in the Xi strip -/

theorem integral_cexp_mul_thetaSeedAtom (w : ℂ) (hw : -(5 / 2) < w.re) :
    (∫ x : ℝ, Complex.exp (w * x) * (thetaCuspSourceTerm x 1 : ℂ)) = thetaAtomMellinFactor w := by
  rw [integral_cexp_mul_thetaCuspSourceTerm w hw 1 one_pos]
  simp

theorem thetaAtomMellinFactor_ne_zero {w : ℂ} (hw : -(5 / 2) < w.re) (hw1 : w ≠ 1 / 2) :
    thetaAtomMellinFactor w ≠ 0 := by
  unfold thetaAtomMellinFactor
  have hΓ : Complex.Gamma (w / 2 + 5 / 4) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hm
    have := congrArg Complex.re hm
    simp at this
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hpi : (1 / (Real.pi : ℂ)) ^ (w / 2 + 1 / 4) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    push Not
    intro h
    exact absurd h (one_div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hw1) hΓ) hpi

/-- **Divisor discontinuity.**  At every Xi zero `w₀` of the open strip, every finite literal
deletion keeps the zero, while the compact-local cofinal limit `h` has nonzero transform. -/
theorem thetaPrimeDeletion_keeps_zero_seed_loses_it (S : Finset ℕ) (hS : ∀ p ∈ S, 0 < p)
    {w₀ : ℂ} (hw₀ : |w₀.re| < 1 / 2) (hzero : XiC (I * w₀) = 0) :
    (∫ x : ℝ, Complex.exp (w₀ * x) * (thetaPrimeDeletion S thetaCuspFullSource x : ℂ)) = 0 ∧
      (∫ x : ℝ, Complex.exp (w₀ * x) * (thetaCuspSourceTerm x 1 : ℂ)) ≠ 0 := by
  refine ⟨by rw [integral_cexp_mul_thetaPrimeDeletion_thetaCuspFullSource S hS, hzero,
    zero_mul], ?_⟩
  have hre := abs_lt.mp hw₀
  rw [integral_cexp_mul_thetaSeedAtom w₀ (by linarith)]
  apply thetaAtomMellinFactor_ne_zero (by linarith)
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

/-! ## A normalized two-point gauge that changes the critical charge -/

/-- The positive even two-point gauge `(1-ε) k + (ε/2)(k(· - L) + k(· + L))`. -/
noncomputable def thetaTwoPointGauge (ε L : ℝ) (x : ℝ) : ℝ :=
  (1 - ε) * thetaCuspFullSource x +
    ε / 2 * (thetaCuspFullSource (x - L) + thetaCuspFullSource (x + L))

theorem thetaTwoPointGauge_pos {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (L x : ℝ) :
    0 < thetaTwoPointGauge ε L x := by
  unfold thetaTwoPointGauge
  have h1 := thetaCuspFullSource_pos_all x
  have h2 := thetaCuspFullSource_pos_all (x - L)
  have h3 := thetaCuspFullSource_pos_all (x + L)
  rcases eq_or_lt_of_le hε1 with rfl | hlt
  · simp only [sub_self, zero_mul, zero_add]
    positivity
  · have : 0 < 1 - ε := by linarith
    positivity

theorem thetaTwoPointGauge_neg (ε L x : ℝ) :
    thetaTwoPointGauge ε L (-x) = thetaTwoPointGauge ε L x := by
  unfold thetaTwoPointGauge
  rw [thetaCuspFullSource_neg, show -x - L = -(x + L) by ring,
    show -x + L = -(x - L) by ring, thetaCuspFullSource_neg, thetaCuspFullSource_neg]
  ring

theorem integral_cexp_mul_thetaTwoPointGauge (ε L : ℝ) (w : ℂ) :
    (∫ x : ℝ, Complex.exp (w * x) * (thetaTwoPointGauge ε L x : ℂ)) =
      XiC (I * w) * (1 - ε + ε * Complex.cosh (w * L)) := by
  have hk := integrable_cexp_mul_thetaCuspFullSource w
  have hm := integrable_cexp_mul_comp_add (-L) (G := fun y => (thetaCuspFullSource y : ℂ)) hk
  have hp := integrable_cexp_mul_comp_add L (G := fun y => (thetaCuspFullSource y : ℂ)) hk
  have hsum : Integrable (fun x : ℝ =>
      Complex.exp (w * x) * (thetaCuspFullSource (x + -L) : ℂ) +
        Complex.exp (w * x) * (thetaCuspFullSource (x + L) : ℂ)) := hm.add hp
  have hfun : (fun x : ℝ => Complex.exp (w * x) * (thetaTwoPointGauge ε L x : ℂ)) =
      fun x : ℝ => ((1 - ε : ℝ) : ℂ) * (Complex.exp (w * x) * (thetaCuspFullSource x : ℂ)) +
        ((ε / 2 : ℝ) : ℂ) * (Complex.exp (w * x) * (thetaCuspFullSource (x + -L) : ℂ) +
          Complex.exp (w * x) * (thetaCuspFullSource (x + L) : ℂ)) := by
    funext x
    unfold thetaTwoPointGauge
    rw [← sub_eq_add_neg]
    push_cast
    ring
  rw [hfun, integral_add (hk.const_mul _) (hsum.const_mul _), integral_const_mul,
    integral_const_mul, integral_add hm hp,
    integral_cexp_mul_comp_add w (-L) (fun y => (thetaCuspFullSource y : ℂ)),
    integral_cexp_mul_comp_add w L (fun y => (thetaCuspFullSource y : ℂ)),
    integral_cexp_mul_thetaCuspFullSource]
  have hcosh : 2 * Complex.cosh (w * L) = Complex.exp (w * L) + Complex.exp (-(w * L)) :=
    Complex.two_cosh _
  push_cast
  rw [mul_neg, neg_neg]
  linear_combination (-(XiC (I * w) * (ε / 2))) * hcosh

theorem norm_cosh_le_cosh_re (z : ℂ) : ‖Complex.cosh z‖ ≤ Real.cosh z.re := by
  have h := Complex.two_cosh z
  have hn : ‖2 * Complex.cosh z‖ ≤ Real.exp z.re + Real.exp (-z.re) := by
    rw [h]
    calc ‖Complex.exp z + Complex.exp (-z)‖ ≤ ‖Complex.exp z‖ + ‖Complex.exp (-z)‖ :=
          norm_add_le _ _
      _ = Real.exp z.re + Real.exp (-z.re) := by
          rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re]
  rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by simp] at hn
  rw [Real.cosh_eq]
  linarith

/-- For `0 < ε < 1/(1 + cosh(L/2))` the two-point multiplier has no zero in the open Xi strip. -/
theorem thetaTwoPointGauge_multiplier_ne_zero {ε L : ℝ} (hε : 0 < ε)
    (hsmall : ε * (1 + Real.cosh (L / 2)) < 1) {w : ℂ} (hw : |w.re| < 1 / 2) :
    (1 - ε + ε * Complex.cosh (w * L)) ≠ 0 := by
  intro h
  have h1ε : 0 ≤ 1 - ε := by nlinarith [Real.one_le_cosh (L / 2)]
  have hc : ‖(ε : ℂ) * Complex.cosh (w * L)‖ = 1 - ε := by
    have : (ε : ℂ) * Complex.cosh (w * L) = -(((1 - ε : ℝ) : ℂ)) := by
      push_cast
      linear_combination h
    rw [this, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1ε]
  have hle : ‖Complex.cosh (w * L)‖ ≤ Real.cosh (L / 2) := by
    refine (norm_cosh_le_cosh_re _).trans ?_
    rw [Real.cosh_le_cosh]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [abs_mul, abs_div, abs_two]
    have := abs_nonneg L
    nlinarith [hw]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε] at hc
  have : 1 - ε ≤ ε * Real.cosh (L / 2) := by
    rw [← hc]
    exact mul_le_mul_of_nonneg_left hle hε.le
  nlinarith

/-- The two-point gauge preserves ordinary mass but changes the critical half-charge whenever
`ε ≠ 0` and `L ≠ 0`. -/
theorem thetaTwoPointGauge_mass_and_charge (ε L : ℝ) :
    (∫ x : ℝ, thetaTwoPointGauge ε L x) = ∫ x : ℝ, thetaCuspFullSource x ∧
      (∫ x : ℝ, Real.exp ((1 / 2 : ℝ) * x) * thetaTwoPointGauge ε L x) =
        (1 - ε + ε * Real.cosh (L / 2)) * (1 / 2) := by
  have hmain (w : ℝ) : (∫ x : ℝ, Real.exp (w * x) * thetaTwoPointGauge ε L x) =
      (1 - ε + ε * Real.cosh (w * L)) * ∫ x : ℝ, Real.exp (w * x) * thetaCuspFullSource x := by
    have h := integral_cexp_mul_thetaTwoPointGauge ε L (w : ℂ)
    rw [integral_cexp_mul_ofReal_eq_ofReal_integral, ← integral_cexp_mul_thetaCuspFullSource,
      integral_cexp_mul_ofReal_eq_ofReal_integral] at h
    apply Complex.ofReal_injective
    rw [h]
    push_cast
    ring
  constructor
  · have h := hmain 0
    simp only [zero_mul, Real.exp_zero, one_mul, Real.cosh_zero] at h
    rw [h]
    ring
  · rw [hmain, integral_exp_half_mul_thetaCuspFullSource_eq_half]
    ring_nf

theorem thetaTwoPointGauge_charge_ne {ε L : ℝ} (hε : ε ≠ 0) (hL : L ≠ 0) :
    (∫ x : ℝ, Real.exp ((1 / 2 : ℝ) * x) * thetaTwoPointGauge ε L x) ≠
      ∫ x : ℝ, Real.exp ((1 / 2 : ℝ) * x) * thetaCuspFullSource x := by
  rw [(thetaTwoPointGauge_mass_and_charge ε L).2, integral_exp_half_mul_thetaCuspFullSource_eq_half]
  have hc : 1 < Real.cosh (L / 2) := Real.one_lt_cosh.mpr (div_ne_zero hL two_ne_zero)
  intro h
  have : ε * (Real.cosh (L / 2) - 1) = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · exact hε h1
  · linarith


/-- The two-point gauge is the translation mixture of the positive symmetric probability measure
`(1-ε) δ₀ + (ε/2)(δ_L + δ_{-L})`. -/
theorem thetaTranslationMixture_twoPoint {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (L : ℝ) :
    thetaTranslationMixture (ENNReal.ofReal (1 - ε) • Measure.dirac (0 : ℝ) +
        ENNReal.ofReal (ε / 2) • (Measure.dirac L + Measure.dirac (-L))) =
      thetaTwoPointGauge ε L := by
  funext x
  set f : ℝ → ℝ := fun t => thetaCuspFullSource (x - t)
  have hd : ∀ a : ℝ, Integrable f (Measure.dirac a) := fun a => integrable_dirac enorm_lt_top
  have h0 := hd 0
  have hL := hd L
  have hmL := hd (-L)
  unfold thetaTranslationMixture
  change ∫ t, f t ∂(ENNReal.ofReal (1 - ε) • Measure.dirac (0 : ℝ) +
      ENNReal.ofReal (ε / 2) • (Measure.dirac L + Measure.dirac (-L))) = _
  rw [integral_add_measure (h0.smul_measure ENNReal.ofReal_ne_top)
      ((hL.add_measure hmL).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_add_measure hL hmL,
    integral_dirac, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
  simp only [f, smul_eq_mul, sub_zero, sub_neg_eq_add, thetaTwoPointGauge]

end RHTower
