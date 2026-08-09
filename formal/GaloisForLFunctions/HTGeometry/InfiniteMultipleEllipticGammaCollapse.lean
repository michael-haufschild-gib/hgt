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

end HTGeometry
