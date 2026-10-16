import GaloisForLFunctions.RHTower.MobiusDivisorPrimeClusterSynthesis

/-!
# Simultaneous phase selection by actual prime clusters

A negative prescribed cosine forces a strict amplitude gap for the common
cluster exponential. A positive neighborhood of the aligned phase then
dominates all negative contributions, simultaneously for finitely many
integrable signed tests. The final selector is a finite set of actual primes.
-/

noncomputable section
open Finset Set Filter Topology MeasureTheory
namespace RHTower
open PrimePreparation

private def badRate (R : Finset ℕ) : ℝ := (R.card : ℝ) - 2 + Real.sqrt 2

private lemma badRate_lt_card (R : Finset ℕ) : badRate R < R.card := by
  have h : Real.sqrt (2 : ℝ) < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  dsimp [badRate]
  linarith

private lemma cosine_sum_lower (R : Finset ℕ) (frequency t : ℝ) :
    -(R.card : ℝ) ≤ ∑ r ∈ R, Real.cos ((frequency + Real.log r) * t) := by
  simpa only [sum_const, nsmul_eq_mul, mul_neg, mul_one] using
    Finset.sum_le_sum (fun r (_ : r ∈ R) => Real.neg_one_le_cos ((frequency + Real.log r) * t))

private lemma cosine_sum_bad (R : Finset ℕ) (h1 : 1 ∈ R)
    {q : ℕ} (hq : q ∈ R) (hq1 : q ≠ 1) (frequency t : ℝ)
    (hbad : Real.cos (Real.log q * t) ≤ 0) :
    -badRate R ≤ ∑ r ∈ R, Real.cos ((frequency + Real.log r) * t) := by
  let F : ℕ → ℝ := fun r => Real.cos ((frequency + Real.log r) * t)
  let U := (R.erase 1).erase q
  have hqe : q ∈ R.erase 1 := mem_erase.mpr ⟨hq1, hq⟩
  have hsplit1 := Finset.sum_erase_add R F h1
  have hsplit2 := Finset.sum_erase_add (R.erase 1) F hqe
  have hc1 := Finset.card_erase_add_one h1
  have hc2 := Finset.card_erase_add_one hqe
  have hc : (U.card : ℝ) + 2 = R.card := by
    have hn : U.card + 2 = R.card := by dsimp [U]; omega
    exact_mod_cast hn
  have hrest : -(U.card : ℝ) ≤ ∑ r ∈ U, F r := cosine_sum_lower U frequency t
  have hpair : -Real.sqrt (2 : ℝ) ≤ F 1 + F q := by
    have h := clusterCos_negative_region (by norm_num : (0 : ℝ) ≤ 1)
      (θ := frequency * t) hbad
    simpa only [F, clusterCos, one_pow, one_mul, Nat.cast_one, Real.log_one,
      zero_mul, add_zero, show (1 : ℝ) + 1 = 2 by norm_num, add_mul] using h
  change -badRate R ≤ ∑ r ∈ R, F r
  dsimp only [badRate]
  change -(U.card : ℝ) ≤ ∑ r ∈ (R.erase 1).erase q, F r at hrest
  linarith

private lemma model_bound (R : Finset ℕ) {s : ℝ} (hs : 0 ≤ s)
    (frequency t : ℝ) :
    primeClusterModel R s frequency t ≤ Real.exp (2 * s * R.card) := by
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (cosine_sum_lower R frequency t) (show 0 ≤ 2 * s by positivity)
  nlinarith only [h]

private lemma model_bad (R : Finset ℕ) (h1 : 1 ∈ R)
    {q : ℕ} (hq : q ∈ R) (hq1 : q ≠ 1) {s : ℝ} (hs : 0 ≤ s)
    (frequency t : ℝ) (hbad : Real.cos (Real.log q * t) ≤ 0) :
    primeClusterModel R s frequency t ≤ Real.exp (2 * s * badRate R) := by
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (cosine_sum_bad R h1 hq hq1 frequency t hbad)
    (show 0 ≤ 2 * s by positivity)
  nlinarith only [h]

private lemma model_gate (R : Finset ℕ) {s c b : ℝ}
    (hs : 0 ≤ s) (hc : 0 ≤ c) (frequency t : ℝ)
    (hgap : b ≤ (R.card : ℝ) * c - ∑ r ∈ R, |Real.log r * t|) :
    Real.exp (2 * s * b) * clusterGate c (frequency * t) ≤
      primeClusterModel R s frequency t := by
  by_cases hg : 0 < clusterGate c (frequency * t)
  · have hcos : Real.cos (frequency * t) < -c := by
      have h := (lt_max_iff.mp hg).resolve_left (lt_irrefl (0 : ℝ))
      linarith
    have hterm (r : ℕ) : Real.cos ((frequency + Real.log r) * t) ≤
        Real.cos (frequency * t) + |Real.log r * t| := by
      have h := Real.abs_cos_sub_cos_le ((frequency + Real.log r) * t) (frequency * t)
      rw [show (frequency + Real.log r) * t - frequency * t = Real.log r * t by ring] at h
      have hh := (le_abs_self _).trans h
      linarith
    have hsum := Finset.sum_le_sum (fun r (_ : r ∈ R) => hterm r)
    rw [sum_add_distrib, sum_const, nsmul_eq_mul] at hsum
    have hm := mul_le_mul_of_nonneg_left hcos.le (Nat.cast_nonneg R.card : (0 : ℝ) ≤ R.card)
    have hsmall : (∑ r ∈ R, Real.cos ((frequency + Real.log r) * t)) ≤ -b := by linarith
    have hscale := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 2 * s by positivity)
    have he : Real.exp (2 * s * b) ≤ primeClusterModel R s frequency t := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hscale]
    exact (mul_le_of_le_one_right (Real.exp_pos _).le (clusterGate_bounds hc _).2).trans he
  · have hz : clusterGate c (frequency * t) = 0 := le_antisymm (le_of_not_gt hg) (clusterGate_bounds hc _).1
    rw [hz, mul_zero]
    exact (Real.exp_pos _).le

private lemma model_integrable (R : Finset ℕ) {s : ℝ} (hs : 0 ≤ s)
    (frequency : ℝ) (f : ℝ → ℝ) (hf : Integrable f) :
    Integrable (fun t => f t * primeClusterModel R s frequency t) := by
  have hc : Continuous (primeClusterModel R s frequency) := by unfold primeClusterModel; fun_prop
  apply hf.mul_bdd hc.aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs, abs_of_pos (show 0 < primeClusterModel R s frequency t from Real.exp_pos _)]
  exact model_bound R hs frequency t

private lemma model_integral_lower (R : Finset ℕ) (h1 : 1 ∈ R)
    {s c b m d : ℝ} (hs : 0 ≤ s) (hc : 0 ≤ c) (hm : 0 < m) (hd : 0 < d)
    (f : ℝ → ℝ) (hfi : Integrable f)
    (hbad : ∀ t, f t < 0 → ∃ q ∈ R, q ≠ 1 ∧ Real.cos (Real.log q * t) ≤ 0)
    (hlocal : ∀ t ∈ Icc (0 : ℝ) d,
      m ≤ f t ∧ b ≤ (R.card : ℝ) * c - ∑ r ∈ R, |Real.log r * t|)
    {n : ℕ} (hn : 0 < n) :
    m * Real.exp (2 * s * b) *
        (d / (2 * Real.pi) * ∫ θ in (0 : ℝ)..2 * Real.pi, clusterGate c θ) -
      (∫ t, |f t|) * Real.exp (2 * s * badRate R) ≤
      ∫ t, f t * primeClusterModel R s (2 * Real.pi * n / d) t := by
  let freq := 2 * Real.pi * n / d
  let G := (Ioc (0 : ℝ) d).indicator (fun t => clusterGate c (freq * t))
  have hgcont : Continuous (fun t => clusterGate c (freq * t)) :=
    (clusterGate_continuous c).comp (continuous_const.mul continuous_id)
  have hgi : Integrable G := (integrable_indicator_iff measurableSet_Ioc).mpr
    (hgcont.intervalIntegrable 0 d).1
  have hai : Integrable (fun t => |f t|) := by simpa only [Real.norm_eq_abs] using hfi.norm
  have hglobal (t : ℝ) : -|f t| * Real.exp (2 * s * badRate R) ≤
      f t * primeClusterModel R s freq t := by
    by_cases ht : 0 ≤ f t
    · exact le_trans
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (abs_nonneg _)) (Real.exp_pos _).le)
        (mul_nonneg ht (Real.exp_pos _).le)
    · have hneg : f t < 0 := lt_of_not_ge ht
      obtain ⟨q, hq, hq1, hcos⟩ := hbad t hneg
      rw [abs_of_neg hneg, neg_neg]
      exact mul_le_mul_of_nonpos_left (model_bad R h1 hq hq1 hs freq t hcos) hneg.le
  have hpoint (t : ℝ) : m * Real.exp (2 * s * b) * G t -
      |f t| * Real.exp (2 * s * badRate R) ≤ f t * primeClusterModel R s freq t := by
    by_cases ht : t ∈ Ioc (0 : ℝ) d
    · have hl := hlocal t ⟨ht.1.le, ht.2⟩
      have hg := model_gate R hs hc freq t hl.2
      have hpos : m * Real.exp (2 * s * b) * G t ≤ f t * primeClusterModel R s freq t := by
        rw [show G t = clusterGate c (freq * t) from Set.indicator_of_mem ht _]
        calc
          _ = m * (Real.exp (2 * s * b) * clusterGate c (freq * t)) := by ring
          _ ≤ m * primeClusterModel R s freq t := mul_le_mul_of_nonneg_left hg hm.le
          _ ≤ _ := mul_le_mul_of_nonneg_right hl.1 (Real.exp_pos _).le
      exact (sub_le_self _ (by positivity)).trans hpos
    · rw [show G t = 0 from Set.indicator_of_notMem ht _, mul_zero, zero_sub, ← neg_mul]
      exact hglobal t
  have hleft := (hgi.const_mul (m * Real.exp (2 * s * b))).sub
    (hai.mul_const (Real.exp (2 * s * badRate R)))
  have hi := integral_mono hleft (model_integrable R hs freq f hfi) hpoint
  simp only [Pi.sub_apply] at hi
  rw [integral_sub (hgi.const_mul _) (hai.mul_const _), integral_const_mul,
    integral_mul_const] at hi
  have hG : (∫ t, G t) = d / (2 * Real.pi) *
      ∫ θ in (0 : ℝ)..2 * Real.pi, clusterGate c θ := by
    rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hd.le]
    exact clusterGate_integer_periods c hd hn
  rwa [hG] at hi

private lemma exists_positive_model {ι : Type*} (J : Finset ι)
    (R : Finset ℕ) (h1 : 1 ∈ R) (f : ι → ℝ → ℝ)
    (hfc : ∀ j ∈ J, Continuous (f j)) (hfi : ∀ j ∈ J, Integrable (f j))
    (hf0 : ∀ j ∈ J, 0 < f j 0)
    (hbad : ∀ j ∈ J, ∀ t, f j t < 0 → ∃ q ∈ R, q ≠ 1 ∧ Real.cos (Real.log q * t) ≤ 0) :
    ∃ s d : ℝ, ∃ g : ι → ℝ, 0 < s ∧ 0 < d ∧ ∀ j ∈ J,
      0 < g j ∧ ∀ n : ℕ, 0 < n →
        g j ≤ ∫ t, f j t * primeClusterModel R s (2 * Real.pi * n / d) t := by
  let k : ℝ := R.card
  let a : ℝ := badRate R
  let b : ℝ := (a + k) / 2
  have hk : 0 < k := by
    dsimp [k]
    exact_mod_cast Finset.card_pos.mpr ⟨1, h1⟩
  have hak : a < k := badRate_lt_card R
  have ha : 0 ≤ a := by
    have hk1 : (1 : ℝ) ≤ R.card := by exact_mod_cast Finset.card_pos.mpr ⟨1, h1⟩
    have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
    dsimp [a, badRate]
    linarith
  have hab : a < b := by dsimp [b]; linarith
  have hbk : b < k := by dsimp [b]; linarith
  have hb : 0 < b := ha.trans_lt hab
  let c : ℝ := (b + k) / (2 * k)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hc1 : c < 1 := by
    apply (div_lt_one (show 0 < 2 * k by positivity)).mpr
    linarith
  have hkc : k * c = (b + k) / 2 := by dsimp [c]; field_simp
  have hgap : b < k * c := by rw [hkc]; linarith
  have hphase : Continuous (fun t : ℝ => k * c - ∑ r ∈ R, |Real.log r * t|) := by fun_prop
  have hfnear : ∀ᶠ t : ℝ in 𝓝 0, ∀ j ∈ J, f j 0 / 2 < f j t := by
    apply (Filter.eventually_all_finset J).mpr
    intro j hj
    exact (hfc j hj).continuousAt.eventually (eventually_gt_nhds (by linarith [hf0 j hj]))
  have hpnear := hphase.continuousAt.eventually
    (eventually_gt_nhds (show b < k * c - ∑ r ∈ R, |Real.log r * (0 : ℝ)| by simpa using hgap))
  obtain ⟨e, he, hnear⟩ := Metric.eventually_nhds_iff.mp (hfnear.and hpnear)
  let d := e / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hlocal (t : ℝ) (ht : t ∈ Icc (0 : ℝ) d) :
      (∀ j ∈ J, f j 0 / 2 ≤ f j t) ∧
      b ≤ k * c - ∑ r ∈ R, |Real.log r * t| := by
    have hdist : dist t 0 < e := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      dsimp [d] at ht
      linarith [ht.2]
    exact ⟨fun j hj => ((hnear hdist).1 j hj).le, (hnear hdist).2.le⟩
  let C : ι → ℝ := fun j => (f j 0 / 2) *
    (d / (2 * Real.pi) * ∫ θ in (0 : ℝ)..2 * Real.pi, clusterGate c θ)
  let W : ι → ℝ := fun j => ∫ t, |f j t|
  have hC (j : ι) (hj : j ∈ J) : 0 < C j := by
    have hg := clusterGate_mean_pos hc1
    have hf := hf0 j hj
    dsimp [C]
    positivity
  have hlarge : ∀ᶠ s : ℝ in atTop, ∀ j ∈ J,
      W j < C j * Real.exp (2 * (b - a) * s) := by
    apply (Filter.eventually_all_finset J).mpr
    intro j hj
    exact (((Real.tendsto_exp_atTop.comp
      (tendsto_id.const_mul_atTop (show 0 < 2 * (b - a) by linarith))).const_mul_atTop
        (hC j hj)).eventually (eventually_gt_atTop (W j)))
  obtain ⟨s, hs, hslarge⟩ := ((eventually_gt_atTop (0 : ℝ)).and hlarge).exists
  let g : ι → ℝ := fun j => C j * Real.exp (2 * s * b) - W j * Real.exp (2 * s * a)
  refine ⟨s, d, g, hs, hd, ?_⟩
  intro j hj
  have hg : 0 < g j := by
    have hp := mul_pos (sub_pos.mpr (hslarge j hj)) (Real.exp_pos (2 * s * a))
    have hexp : Real.exp (2 * s * b) = Real.exp (2 * (b - a) * s) * Real.exp (2 * s * a) := by
      rw [← Real.exp_add]
      congr 1
      ring
    dsimp [g]
    rw [hexp]
    nlinarith only [hp]
  refine ⟨hg, fun n hn => ?_⟩
  have h := model_integral_lower R h1 hs.le hc (by linarith [hf0 j hj]) hd (f j)
    (hfi j hj) (hbad j hj) (fun t ht => ⟨(hlocal t ht).1 j hj, (hlocal t ht).2⟩) hn
  convert h using 1
  dsimp [g, C, W, a]
  ring

/-- One actual prime set makes every test in a finite compatible family
strictly positive. The same inverse-square-root budget works beyond every
prescribed lower bound on the helper primes. -/
theorem exists_primeCluster_positive_tests {ι : Type*} (J : Finset ι)
    (R : Finset ℕ) (h1 : 1 ∈ R) (hR : ∀ r ∈ R, 0 < r)
    (f : ι → ℝ → ℝ) (hfc : ∀ j ∈ J, Continuous (f j))
    (hfi : ∀ j ∈ J, Integrable (f j)) (hf0 : ∀ j ∈ J, 0 < f j 0)
    (hbad : ∀ j ∈ J, ∀ t, f j t < 0 → ∃ q ∈ R, q ≠ 1 ∧ Real.cos (Real.log q * t) ≤ 0) :
    ∃ W : ℝ, 0 < W ∧ ∀ L : ℝ, ∃ S : Finset ℕ,
      (∀ p ∈ S, p.Prime ∧ L < (p : ℝ)) ∧
      (∑ p ∈ S, (Real.sqrt p)⁻¹) ≤ W ∧
      ∀ j ∈ J, 0 < ∫ t : ℝ, f j t *
        ‖divisorCoreMellinEuler S (1 + (t : ℂ) * Complex.I)‖ ^ 2 := by
  obtain ⟨s, d, g, hs, hd, hmodel⟩ := exists_positive_model J R h1 f hfc hfi hf0 hbad
  obtain ⟨N, S, C, W, hC, hW, hN, hmass, hprime, hprod, hexp, hlim⟩ :=
    exists_primeCluster_synthesis R ⟨1, h1⟩ hR hs hd
  let D : ι → ℕ → ℝ → ℝ := fun j n t => f j t *
    (‖divisorCoreMellinEuler (S n) (1 + (t : ℂ) * Complex.I)‖ ^ 2 -
      primeClusterModel R s (2 * Real.pi * N n / d) t)
  have hdiff (n : ℕ) (t : ℝ) :
      |‖divisorCoreMellinEuler (S n) (1 + (t : ℂ) * Complex.I)‖ ^ 2 -
        primeClusterModel R s (2 * Real.pi * N n / d) t| ≤ 2 * C ^ 2 := by
    rw [← norm_exp_primeClusterExponent_sq]
    apply abs_sub_le_iff.mpr
    have hp0 := norm_nonneg (divisorCoreMellinEuler (S n) (1 + (t : ℂ) * Complex.I))
    have he0 := norm_nonneg (Complex.exp (primeClusterExponent R s (2 * Real.pi * N n / d) t))
    constructor <;> nlinarith [hprod n t, hexp n t, sq_nonneg C]
  have hai (j : ι) (hj : j ∈ J) : Integrable (fun t => |f j t|) := by
    simpa only [Real.norm_eq_abs] using (hfi j hj).norm
  have hint (j : ι) (hj : j ∈ J) :
      Tendsto (fun n => ∫ t, D j n t) atTop (𝓝 (0 : ℝ)) := by
    have hmeas (n : ℕ) : AEStronglyMeasurable (D j n) volume := by
      apply Continuous.aestronglyMeasurable
      have hm : Continuous (primeClusterModel R s (2 * Real.pi * N n / d)) := by
        unfold primeClusterModel
        fun_prop
      exact (hfc j hj).mul (((cluster_euler_continuous (S n)).norm.pow 2).sub hm)
    have hbound (n : ℕ) : ∀ᵐ t : ℝ, ‖D j n t‖ ≤ |f j t| * (2 * C ^ 2) := by
      apply Eventually.of_forall
      intro t
      dsimp [D]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hdiff n t) (abs_nonneg _)
    have hzero : ∀ᵐ t : ℝ, Tendsto (fun n => D j n t) atTop (𝓝 (0 : ℝ)) := by
      apply Eventually.of_forall
      intro t
      simpa only [D, mul_zero] using (hlim t).const_mul (f j t)
    simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
      (fun t => |f j t| * (2 * C ^ 2)) hmeas ((hai j hj).mul_const _) hbound hzero
  have hactual (j : ι) (hj : j ∈ J) (n : ℕ) :
      Integrable (fun t => f j t *
        ‖divisorCoreMellinEuler (S n) (1 + (t : ℂ) * Complex.I)‖ ^ 2) := by
    apply (hfi j hj).mul_bdd ((cluster_euler_continuous (S n)).norm.pow 2).aestronglyMeasurable
      (c := C ^ 2)
    apply Eventually.of_forall
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change ‖divisorCoreMellinEuler (S n) (1 + (t : ℂ) * Complex.I)‖ ^ 2 ≤ C ^ 2
    have hnon := norm_nonneg (divisorCoreMellinEuler (S n) (1 + (t : ℂ) * Complex.I))
    nlinarith [hprod n t]
  have heventual : ∀ᶠ n : ℕ in atTop, ∀ j ∈ J, 0 < ∫ t : ℝ, f j t *
      ‖divisorCoreMellinEuler (S n) (1 + (t : ℂ) * Complex.I)‖ ^ 2 := by
    apply (Filter.eventually_all_finset J).mpr
    intro j hj
    have he := (hint j hj).eventually
      (eventually_gt_nhds (show -(g j) / 2 < (0 : ℝ) by linarith [(hmodel j hj).1]))
    filter_upwards [he] with n hn
    have hpositive := (hmodel j hj).2 (N n) (lt_of_lt_of_le (Nat.zero_lt_succ n) (hN n))
    have heq : (∫ t, D j n t) =
        (∫ t : ℝ, f j t * ‖divisorCoreMellinEuler (S n) (1 + (t : ℂ) * Complex.I)‖ ^ 2) -
        ∫ t, f j t * primeClusterModel R s (2 * Real.pi * N n / d) t := by
      rw [← integral_sub (hactual j hj n) (model_integrable R hs.le _ (f j) (hfi j hj))]
      apply integral_congr_ae
      exact Eventually.of_forall (fun t => by dsimp [D]; ring)
    rw [heq] at hn
    linarith [(hmodel j hj).1]
  have hscale : Tendsto (fun n => clusterScale d (N n)) atTop atTop :=
    (clusterScale_tendsto hd).comp
      (tendsto_atTop_mono (fun n => (Nat.le_succ n).trans (hN n)) tendsto_id)
  refine ⟨W, hW, fun L => ?_⟩
  obtain ⟨n, hn, hlarge⟩ := (heventual.and (hscale.eventually (eventually_gt_atTop L))).exists
  exact ⟨S n, fun p hp => ⟨(hprime n p hp).1, hlarge.trans (hprime n p hp).2⟩, hmass n, hn⟩

end RHTower
