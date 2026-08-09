import GaloisForLFunctions.HTGeometry.InfiniteMultipleEllipticGammaExhaustion
import GaloisForLFunctions.HTGeometry.InfiniteMultipleEllipticGammaSharpness
import GaloisForLFunctions.HTGeometry.InfiniteMultipleEllipticGammaValues

/-!
# Forward collapse and parity normalization

Power summability of an infinite nome family forces the product of any finite nome set to be small,
because one factor already is.  The finite sections are uniformly close to one near the origin —
uniformly in the nome set, since their centred factors are dominated by one fixed summable family —
so the forward half of every finite section collapses to one along the net of finite nome sets.

The backward half converges to the infinite-order product.  Hence the parity-normalized finite
sections converge to it as well, while the raw sections carry the reciprocal of the parity twist.
-/

namespace HTGeometry

open Filter Topology
open scoped BigOperators

/-- Infinite-product form of the finite estimate `‖∏(1+f) - 1‖ ≤ exp(∑‖f‖) - 1`. -/
theorem norm_tprod_one_add_sub_one_le {ι : Type*} {f : ι → ℂ}
    (hf : Summable fun i => ‖f i‖) :
    ‖(∏' i, (1 + f i)) - 1‖ ≤ Real.exp (∑' i, ‖f i‖) - 1 := by
  have hmul : Multipliable fun i => 1 + f i := multipliable_one_add_of_summable hf
  have hlim : Tendsto (fun s : Finset ι => ∏ i ∈ s, (1 + f i)) atTop
      (𝓝 (∏' i, (1 + f i))) := hmul.hasProd
  have hnorm : Tendsto (fun s : Finset ι => ‖(∏ i ∈ s, (1 + f i)) - 1‖) atTop
      (𝓝 (‖(∏' i, (1 + f i)) - 1‖)) := (hlim.sub_const 1).norm
  refine le_of_tendsto hnorm ?_
  filter_upwards with s
  refine (Finset.norm_prod_one_add_sub_one_le s f).trans ?_
  have hle := hf.sum_le_tsum s (fun i _ => norm_nonneg _)
  gcongr

/-- Total occupation mass at the given genus. -/
noncomputable def occupationMassPow {ι : Type*} (g : ℕ) (p : ι → ℂ) : ℝ :=
  ∑' ν : ι →₀ ℕ, ‖nomeMonomial p ν‖ ^ (g + 1)

theorem occupationMassPow_nonneg {ι : Type*} (g : ℕ) (p : ι → ℂ) :
    0 ≤ occupationMassPow g p :=
  tsum_nonneg fun _ => by positivity

/-- **Uniform smallness of the finite sections near the origin.**  The bound does not depend on the
nome set, because the centred factors of every section are dominated by one fixed summable family. -/
theorem norm_finiteNomeSection_sub_one_le {ι : Type*} (g : ℕ) (p : ι → ℂ)
    (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ (g + 1)))
    (S : Finset ι) {t : ℂ} (ht : ‖t‖ ≤ 1) :
    ‖finiteNomeSection g p S t - 1‖
      ≤ Real.exp (Real.exp g * ‖t‖ ^ (g + 1) * occupationMassPow g p) - 1 := by
  classical
  have hq_sum : Summable (fun ν : ι →₀ ℕ => ‖nomeMonomial p ν‖ ^ (g + 1)) :=
    (summable_nomeMonomial_pow_iff g p hp_lt).2 hsum
  set F : (ι →₀ ℕ) → ℂ := fun ν =>
    (if ν.support ⊆ S then primaryFactor g (t * nomeMonomial p ν) else 1) - 1 with hF
  have hFbound : ∀ ν, ‖F ν‖
      ≤ Real.exp g * ‖t‖ ^ (g + 1) * ‖nomeMonomial p ν‖ ^ (g + 1) := by
    intro ν
    by_cases hν : ν.support ⊆ S
    · have hqle : ‖nomeMonomial p ν‖ ≤ 1 := norm_nomeMonomial_le_one p hp_lt ν
      have hz : ‖t * nomeMonomial p ν‖ ≤ 1 := by
        rw [norm_mul]
        nlinarith [norm_nonneg t, norm_nonneg (nomeMonomial p ν)]
      have hb := primaryFactor_sub_one_norm_le g hz
      rw [norm_mul, mul_pow] at hb
      simp only [hF, hν, if_true]
      calc ‖primaryFactor g (t * nomeMonomial p ν) - 1‖
          ≤ Real.exp g * (‖t‖ ^ (g + 1) * ‖nomeMonomial p ν‖ ^ (g + 1)) := hb
        _ = Real.exp g * ‖t‖ ^ (g + 1) * ‖nomeMonomial p ν‖ ^ (g + 1) := by ring
    · simp only [hF, hν, if_false, sub_self, norm_zero]
      positivity
  have hFsum : Summable (fun ν => ‖F ν‖) :=
    Summable.of_nonneg_of_le (fun ν => norm_nonneg _) hFbound (hq_sum.mul_left _)
  have hrewrite : finiteNomeSection g p S t = ∏' ν : ι →₀ ℕ, (1 + F ν) := by
    rw [finiteNomeSection]
    refine tprod_congr fun ν => ?_
    rw [hF]
    ring
  rw [hrewrite]
  refine (norm_tprod_one_add_sub_one_le hFsum).trans ?_
  have hmass : ∑' ν : ι →₀ ℕ, ‖F ν‖
      ≤ Real.exp g * ‖t‖ ^ (g + 1) * occupationMassPow g p := by
    calc ∑' ν : ι →₀ ℕ, ‖F ν‖
        ≤ ∑' ν : ι →₀ ℕ, Real.exp g * ‖t‖ ^ (g + 1) * ‖nomeMonomial p ν‖ ^ (g + 1) :=
          Summable.tsum_le_tsum hFbound hFsum (hq_sum.mul_left _)
      _ = Real.exp g * ‖t‖ ^ (g + 1) * occupationMassPow g p := by
          rw [occupationMassPow, tsum_mul_left]
  gcongr

/-- **The nome product collapses.**  Over an infinite index set, power summability makes some single
nome arbitrarily small, and every larger finite product is smaller still. -/
theorem tendsto_nomeProduct_atTop_zero {ι : Type*} [Infinite ι] (g : ℕ) (p : ι → ℂ)
    (hp_lt : ∀ a, ‖p a‖ < 1) (hsum : Summable (fun a => ‖p a‖ ^ (g + 1))) :
    Tendsto (fun S : Finset ι => ∏ a ∈ S, p a) atTop (𝓝 0) := by
  classical
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ι, ‖p a₀‖ < ε := by
    by_contra hcon
    have hcon' : ∀ a : ι, ε ≤ ‖p a‖ := fun a => not_lt.mp (fun h => hcon ⟨a, h⟩)
    have hfin : {a : ι | ¬ (‖p a‖ ^ (g + 1) ∈ Metric.ball (0 : ℝ) (ε ^ (g + 1)))}.Finite :=
      Filter.eventually_cofinite.mp (hsum.tendsto_cofinite_zero
        (Metric.ball_mem_nhds 0 (by positivity)))
    have huniv : (Set.univ : Set ι) ⊆
        {a : ι | ¬ (‖p a‖ ^ (g + 1) ∈ Metric.ball (0 : ℝ) (ε ^ (g + 1)))} := by
      intro a _
      simp only [Set.mem_setOf_eq, Metric.mem_ball, Real.dist_eq, sub_zero, not_lt]
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (le_of_lt hε) (hcon' a) _
    exact absurd (hfin.subset huniv) Set.infinite_univ
  filter_upwards [eventually_ge_atTop ({a₀} : Finset ι)] with S hS
  have hsub : ({a₀} : Finset ι) ⊆ S := hS
  calc ‖∏ a ∈ S, p a‖ = ∏ a ∈ S, ‖p a‖ := norm_prod _ _
    _ ≤ ∏ a ∈ ({a₀} : Finset ι), ‖p a‖ :=
        Finset.prod_le_prod_of_subset_of_le_one hsub (fun i _ => norm_nonneg _)
          (fun i _ _ => le_of_lt (hp_lt i))
    _ = ‖p a₀‖ := by simp
    _ < ε := ha₀

/-- The forward half of a finite section, evaluated at the collapsing coordinate. -/
noncomputable def forwardNomeFactor {ι : Type*} (g : ℕ) (p : ι → ℂ) (S : Finset ι) (x : ℂ) : ℂ :=
  finiteNomeSection g p S ((∏ a ∈ S, p a) / x)

/-- **The forward half collapses to one.** -/
theorem tendsto_forwardNomeFactor_one {ι : Type*} [Infinite ι] (g : ℕ) (p : ι → ℂ)
    (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ (g + 1))) (x : ℂ) :
    Tendsto (fun S : Finset ι => forwardNomeFactor g p S x) atTop (𝓝 1) := by
  classical
  have hQ := tendsto_nomeProduct_atTop_zero g p hp_lt hsum
  have ht0 : Tendsto (fun S : Finset ι => (∏ a ∈ S, p a) / x) atTop (𝓝 0) := by
    simpa using hQ.div_const x
  have hn0 : Tendsto (fun S : Finset ι => ‖(∏ a ∈ S, p a) / x‖) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp ht0
  have hmaj : Tendsto (fun S : Finset ι =>
      Real.exp (Real.exp g * ‖(∏ a ∈ S, p a) / x‖ ^ (g + 1) * occupationMassPow g p) - 1)
      atTop (𝓝 0) := by
    have hcomp : Tendsto (fun S : Finset ι =>
        Real.exp g * ‖(∏ a ∈ S, p a) / x‖ ^ (g + 1) * occupationMassPow g p)
        atTop (𝓝 0) := by
      have := (hn0.pow (g + 1)).const_mul (Real.exp g)
      simpa using this.mul_const (occupationMassPow g p)
    have := (Real.continuous_exp.tendsto 0).comp hcomp
    simpa using this.sub_const 1
  have hev : ∀ᶠ S : Finset ι in atTop, ‖(∏ a ∈ S, p a) / x‖ ≤ 1 := by
    have hb := hn0.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hb] with S hS
    exact hS
  have hkey : Tendsto (fun S : Finset ι => forwardNomeFactor g p S x - 1) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun S => norm_nonneg _) ?_ hmaj
    filter_upwards [hev] with S hS
    exact norm_finiteNomeSection_sub_one_le g p hp_lt hsum S hS
  simpa using hkey.add_const 1

/-- The parity-normalized finite section: the raw section raised to `(-1)^(|S|+1)`. -/
noncomputable def parityNormalizedSection {ι : Type*} (g : ℕ) (p : ι → ℂ)
    (S : Finset ι) (x : ℂ) : ℂ :=
  if Even S.card then finiteNomeSection g p S x / forwardNomeFactor g p S x
  else finiteNomeSection g p S x * forwardNomeFactor g p S x

/-- **The parity-normalized sections converge to the infinite-order product.**  Both parity branches
have the same limit precisely because the forward half collapses to one. -/
theorem tendsto_parityNormalizedSection {ι : Type*} [Infinite ι] (g : ℕ) (p : ι → ℂ)
    (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ (g + 1))) (x : ℂ) :
    Tendsto (fun S : Finset ι => parityNormalizedSection g p S x) atTop
      (𝓝 (infiniteMultipleEllipticGamma g p x)) := by
  classical
  have hB := tendsto_finiteNomeSection g p hp_ne hp_lt hsum x
  have hF := tendsto_forwardNomeFactor_one g p hp_lt hsum x
  have hdiv : Tendsto (fun S : Finset ι =>
      finiteNomeSection g p S x / forwardNomeFactor g p S x) atTop
      (𝓝 (infiniteMultipleEllipticGamma g p x)) := by
    have h := hB.div hF one_ne_zero
    rw [div_one] at h
    exact h
  have hmul : Tendsto (fun S : Finset ι =>
      finiteNomeSection g p S x * forwardNomeFactor g p S x) atTop
      (𝓝 (infiniteMultipleEllipticGamma g p x)) := by
    have h := hB.mul hF
    rw [mul_one] at h
    exact h
  rw [Metric.tendsto_nhds] at hdiv hmul ⊢
  intro ε hε
  filter_upwards [hdiv ε hε, hmul ε hε] with S h1 h2
  rw [parityNormalizedSection]
  by_cases hp : Even S.card
  · simpa [hp] using h1
  · simpa [hp] using h2


/-! ## The parity obstruction -/

/-- The raw finite section, before parity normalization. -/
noncomputable def rawSection {ι : Type*} (g : ℕ) (p : ι → ℂ) (S : Finset ι) (x : ℂ) : ℂ :=
  if Even S.card then forwardNomeFactor g p S x / finiteNomeSection g p S x
  else forwardNomeFactor g p S x * finiteNomeSection g p S x

theorem rawSection_eq_inv_of_even {ι : Type*} (g : ℕ) (p : ι → ℂ) {S : Finset ι}
    (hS : Even S.card) (x : ℂ) :
    rawSection g p S x = (parityNormalizedSection g p S x)⁻¹ := by
  rw [rawSection, parityNormalizedSection, if_pos hS, if_pos hS, inv_div]

theorem rawSection_eq_of_odd {ι : Type*} (g : ℕ) (p : ι → ℂ) {S : Finset ι}
    (hS : ¬ Even S.card) (x : ℂ) :
    rawSection g p S x = parityNormalizedSection g p S x := by
  rw [rawSection, parityNormalizedSection, if_neg hS, if_neg hS, mul_comm]

/-- Both parity subposets of the finite nome sets are cofinal, so both parity subnets are genuine
subnets: a fresh index can always be adjoined. -/
instance evenCard_neBot {ι : Type*} [Infinite ι] :
    (atTop ⊓ 𝓟 {S : Finset ι | Even S.card}).NeBot := by
  classical
  rw [inf_principal_neBot_iff]
  intro U hU
  obtain ⟨S₀, hS₀⟩ := Filter.mem_atTop_sets.mp hU
  by_cases hpar : Even S₀.card
  · exact ⟨S₀, hS₀ S₀ le_rfl, hpar⟩
  · obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset S₀
    refine ⟨insert a S₀, hS₀ _ (Finset.subset_insert a S₀), ?_⟩
    simp only [Set.mem_setOf_eq, Finset.card_insert_of_notMem ha, Nat.even_add_one]
    exact hpar

instance oddCard_neBot {ι : Type*} [Infinite ι] :
    (atTop ⊓ 𝓟 {S : Finset ι | ¬ Even S.card}).NeBot := by
  classical
  rw [inf_principal_neBot_iff]
  intro U hU
  obtain ⟨S₀, hS₀⟩ := Filter.mem_atTop_sets.mp hU
  by_cases hpar : Even S₀.card
  · obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset S₀
    refine ⟨insert a S₀, hS₀ _ (Finset.subset_insert a S₀), ?_⟩
    simp only [Set.mem_setOf_eq, Finset.card_insert_of_notMem ha, Nat.even_add_one, not_not]
    exact hpar
  · exact ⟨S₀, hS₀ S₀ le_rfl, hpar⟩

/-- Along odd nome sets the raw section tends to the infinite-order product. -/
theorem tendsto_rawSection_odd {ι : Type*} [Infinite ι] (g : ℕ) (p : ι → ℂ)
    (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ (g + 1))) (x : ℂ) :
    Tendsto (fun S : Finset ι => rawSection g p S x)
      (atTop ⊓ 𝓟 {S : Finset ι | ¬ Even S.card})
      (𝓝 (infiniteMultipleEllipticGamma g p x)) := by
  have h : Tendsto (fun S : Finset ι => parityNormalizedSection g p S x)
      (atTop ⊓ 𝓟 {S : Finset ι | ¬ Even S.card})
      (𝓝 (infiniteMultipleEllipticGamma g p x)) :=
    (tendsto_parityNormalizedSection g p hp_ne hp_lt hsum x).mono_left inf_le_left
  refine h.congr' (Filter.eventually_inf_principal.mpr ?_)
  filter_upwards with S hS
  exact (rawSection_eq_of_odd g p hS x).symm

/-- Along even nome sets the raw section tends to the reciprocal of the infinite-order product. -/
theorem tendsto_rawSection_even {ι : Type*} [Infinite ι] (g : ℕ) (p : ι → ℂ)
    (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ (g + 1))) {x : ℂ}
    (hG : infiniteMultipleEllipticGamma g p x ≠ 0) :
    Tendsto (fun S : Finset ι => rawSection g p S x)
      (atTop ⊓ 𝓟 {S : Finset ι | Even S.card})
      (𝓝 (infiniteMultipleEllipticGamma g p x)⁻¹) := by
  have h0 : Tendsto (fun S : Finset ι => parityNormalizedSection g p S x)
      (atTop ⊓ 𝓟 {S : Finset ι | Even S.card})
      (𝓝 (infiniteMultipleEllipticGamma g p x)) :=
    (tendsto_parityNormalizedSection g p hp_ne hp_lt hsum x).mono_left inf_le_left
  have h := h0.inv₀ hG
  refine h.congr' (Filter.eventually_inf_principal.mpr ?_)
  filter_upwards with S hS
  exact (rawSection_eq_inv_of_even g p hS x).symm

/-- **The two parity cluster values are reciprocal.**  If the raw net converged at a point where the
infinite-order product does not vanish, the limit would have to equal both the product and its
reciprocal. -/
theorem sq_eq_one_of_tendsto_rawSection {ι : Type*} [Infinite ι] (g : ℕ) (p : ι → ℂ)
    (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ (g + 1))) {x : ℂ}
    (hG : infiniteMultipleEllipticGamma g p x ≠ 0) {L : ℂ}
    (hL : Tendsto (fun S : Finset ι => rawSection g p S x) atTop (𝓝 L)) :
    infiniteMultipleEllipticGamma g p x ^ 2 = 1 := by
  have hLe : Tendsto (fun S : Finset ι => rawSection g p S x)
      (atTop ⊓ 𝓟 {S : Finset ι | Even S.card}) (𝓝 L) := hL.mono_left inf_le_left
  have hLo : Tendsto (fun S : Finset ι => rawSection g p S x)
      (atTop ⊓ 𝓟 {S : Finset ι | ¬ Even S.card}) (𝓝 L) := hL.mono_left inf_le_left
  have h1 : L = (infiniteMultipleEllipticGamma g p x)⁻¹ :=
    tendsto_nhds_unique hLe (tendsto_rawSection_even g p hp_ne hp_lt hsum hG)
  have h2 : L = infiniteMultipleEllipticGamma g p x :=
    tendsto_nhds_unique hLo (tendsto_rawSection_odd g p hp_ne hp_lt hsum x)
  have h3 : infiniteMultipleEllipticGamma g p x =
      (infiniteMultipleEllipticGamma g p x)⁻¹ := h2.symm.trans h1
  rw [sq]
  nth_rewrite 1 [h3]
  exact inv_mul_cancel₀ hG

/-- A point where the infinite-order product is neither zero nor a square root of one: the real part
of the product runs continuously from one to zero, so it takes the value one half. -/
theorem exists_point_of_half {ι : Type*} (g : ℕ) (p : ι → ℂ)
    (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ (g + 1))) :
    ∃ x : ℂ, infiniteMultipleEllipticGamma g p x ≠ 0 ∧
      infiniteMultipleEllipticGamma g p x ^ 2 ≠ 1 := by
  have hcont : Continuous (infiniteMultipleEllipticGamma g p) := by
    have h := infiniteMultipleEllipticGamma_analytic g p hp_ne hp_lt hsum
    rw [← continuousOn_univ]
    exact h.continuousOn
  set F : ℝ → ℝ := fun t => (infiniteMultipleEllipticGamma g p (t : ℂ)).re with hF
  have hFcont : ContinuousOn F (Set.Icc 0 1) := by
    refine Continuous.continuousOn ?_
    exact Complex.continuous_re.comp (hcont.comp Complex.continuous_ofReal)
  have hF0 : F 0 = 1 := by
    simp [hF, infiniteMultipleEllipticGamma_at_zero]
  have hF1 : F 1 = 0 := by
    simp [hF, infiniteMultipleEllipticGamma_at_one g p hp_ne hp_lt hsum]
  have hmem : (1 / 2 : ℝ) ∈ Set.Icc (F 1) (F 0) := by
    rw [hF0, hF1]
    constructor <;> norm_num
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hFcont hmem
  have ht' : (infiniteMultipleEllipticGamma g p (t : ℂ)).re = 1 / 2 := ht
  refine ⟨(t : ℂ), ?_, ?_⟩
  · intro hzero
    rw [hzero] at ht'
    norm_num at ht'
  · intro hsq
    have hcases : infiniteMultipleEllipticGamma g p (t : ℂ) = 1 ∨
        infiniteMultipleEllipticGamma g p (t : ℂ) = -1 := by
      have hfac : (infiniteMultipleEllipticGamma g p (t : ℂ) - 1) *
          (infiniteMultipleEllipticGamma g p (t : ℂ) + 1) = 0 := by linear_combination hsq
      rcases mul_eq_zero.mp hfac with h | h
      · exact Or.inl (by linear_combination h)
      · exact Or.inr (by linear_combination h)
    rcases hcases with h | h <;> rw [h] at ht' <;> norm_num at ht'

/-- **Parity normalization is necessary.**  At some point the raw net of finite sections has no
limit at all: its two parity subnets cluster at reciprocal values that cannot coincide there. -/
theorem exists_rawSection_not_convergent {ι : Type*} [Infinite ι] (g : ℕ) (p : ι → ℂ)
    (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ (g + 1))) :
    ∃ x : ℂ, ¬ ∃ L : ℂ,
      Tendsto (fun S : Finset ι => rawSection g p S x) atTop (𝓝 L) := by
  obtain ⟨x, hx0, hxsq⟩ := exists_point_of_half g p hp_ne hp_lt hsum
  refine ⟨x, ?_⟩
  rintro ⟨L, hL⟩
  exact hxsq (sq_eq_one_of_tendsto_rawSection g p hp_ne hp_lt hsum hx0 hL)

end HTGeometry
