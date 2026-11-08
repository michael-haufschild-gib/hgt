import GaloisForLFunctions.HTGeometry.PolynomialRootSumSemicontinuity
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Continuity of weighted polynomial root sums

Locally uniform convergence and fixed root cardinality imply convergence of
all continuous nonnegative root sums, with multiplicity. A bounded cutoff
rules out escaping copies; applying lower semicontinuity to complementary
weights then supplies the upper bound. Constant perturbations preserve the
cardinality and hence every nonnegative power of root depth.
-/

open Polynomial Complex Filter Topology Set
namespace GaloisForLFunctions.HTGeometry


private theorem eventually_lt_root_weight_sum {f : ℂ[X]} (hf : f ≠ 0)
    {F : ℕ → ℂ[X]}
    (hconv : TendstoLocallyUniformly (fun n z => (F n).eval z) f.eval atTop)
    {Ψ : ℂ → ℝ} (hΨ : Continuous Ψ) (hΨ0 : ∀ z, 0 ≤ Ψ z)
    {a : ℝ} (ha : a < (f.roots.map Ψ).sum) :
    ∀ᶠ n in atTop, a < ((F n).roots.map Ψ).sum := by
  by_contra h
  have hfreq : ∃ᶠ n in atTop, ((F n).roots.map Ψ).sum ≤ a := by
    simpa only [Filter.Frequently, not_le] using h
  obtain ⟨φ, hφ, hbound⟩ := Filter.extraction_of_frequently_atTop hfreq
  have hsub : TendstoLocallyUniformly (fun n z => (F (φ n)).eval z) f.eval atTop := by
    intro U hU z
    obtain ⟨V, hV, he⟩ := hconv U hU z
    exact ⟨V, hV, hφ.tendsto_atTop.eventually he⟩
  exact (not_le_of_gt ha) (sum_roots_le_of_tendstoLocallyUniformly hf hsub hΨ hΨ0
    (Filter.Eventually.of_forall hbound))

private theorem tendsto_root_weight_sum_of_bounded {f : ℂ[X]} (hf : f ≠ 0)
    {F : ℕ → ℂ[X]}
    (hconv : TendstoLocallyUniformly (fun n z => (F n).eval z) f.eval atTop)
    (hcard : ∀ᶠ n in atTop, (F n).roots.card = f.roots.card)
    {Ψ : ℂ → ℝ} (hΨ : Continuous Ψ) (hΨ0 : ∀ z, 0 ≤ Ψ z)
    {M : ℝ} (hfM : ∀ z ∈ f.roots, Ψ z ≤ M)
    (hFM : ∀ᶠ n in atTop, ∀ z ∈ (F n).roots, Ψ z ≤ M) :
    Tendsto (fun n => ((F n).roots.map Ψ).sum) atTop (𝓝 (f.roots.map Ψ).sum) := by
  let Φ : ℂ → ℝ := fun z => max 0 (M - Ψ z)
  have hΦ : Continuous Φ := continuous_const.max (continuous_const.sub hΨ)
  have hΦ0 (z : ℂ) : 0 ≤ Φ z := le_max_left _ _
  have hsplit (S : Multiset ℂ) (hS : ∀ z ∈ S, Ψ z ≤ M) :
      (S.map Ψ).sum + (S.map Φ).sum = (S.card : ℝ) * M := by
    rw [← Multiset.sum_map_add]
    have he : S.map (fun z => Ψ z + Φ z) = S.map (fun _ => M) := by
      apply Multiset.map_congr rfl
      intro z hz
      dsimp only [Φ]
      rw [max_eq_right (sub_nonneg.mpr (hS z hz))]
      ring
    rw [he, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul]
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact eventually_lt_root_weight_sum hf hconv hΨ hΨ0 ha
  · intro b hb
    have hb' : (f.roots.card : ℝ) * M - b < (f.roots.map Φ).sum := by
      linarith only [hsplit f.roots hfM, hb]
    filter_upwards [eventually_lt_root_weight_sum hf hconv hΦ hΦ0 hb', hcard, hFM]
      with n hn hc hM
    have hs := hsplit (F n).roots hM
    rw [hc] at hs
    linarith only [hs, hn]


/-- Fixed total multiplicity prevents loss of any continuous nonnegative
root weight under locally uniform polynomial convergence. -/
theorem tendsto_sum_roots_of_fixed_card {f : ℂ[X]} (hf : f ≠ 0)
    {F : ℕ → ℂ[X]}
    (hconv : TendstoLocallyUniformly (fun n z => (F n).eval z) f.eval atTop)
    (hcard : ∀ᶠ n in atTop, (F n).roots.card = f.roots.card)
    {Ψ : ℂ → ℝ} (hΨ : Continuous Ψ) (hΨ0 : ∀ z, 0 ≤ Ψ z) :
    Tendsto (fun n => ((F n).roots.map Ψ).sum) atTop (𝓝 (f.roots.map Ψ).sum) := by
  let M := (f.roots.map Ψ).sum
  have hfM (z : ℂ) (hz : z ∈ f.roots) : Ψ z ≤ M :=
    Multiset.single_le_sum (fun x hx => by
      obtain ⟨w, _, rfl⟩ := Multiset.mem_map.mp hx
      exact hΨ0 w) (Ψ z) (Multiset.mem_map.mpr ⟨z, hz, rfl⟩)
  -- A copy above the cutoff loses one unit of the conserved root count.
  let χ : ℂ → ℝ := fun z => max 0 (1 - max 0 (Ψ z - M))
  have hχ : Continuous χ := continuous_const.max
    (continuous_const.sub (continuous_const.max (hΨ.sub continuous_const)))
  have hχ0 (z : ℂ) : 0 ≤ χ z := le_max_left _ _
  have hχ1 (z : ℂ) : χ z ≤ 1 :=
    max_le zero_le_one (sub_le_self _ (le_max_left _ _))
  have hχf : (f.roots.map χ).sum = (f.roots.card : ℝ) := by
    have he : f.roots.map χ = f.roots.map (fun _ => (1 : ℝ)) := by
      apply Multiset.map_congr rfl
      intro z hz
      dsimp only [χ]
      rw [max_eq_left (sub_nonpos.mpr (hfM z hz)), sub_zero, max_eq_right zero_le_one]
    rw [he, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_one]
  have hlow : ∀ᶠ n in atTop,
      (f.roots.card : ℝ) - 1 < ((F n).roots.map χ).sum :=
    eventually_lt_root_weight_sum hf hconv hχ hχ0 (by rw [hχf]; linarith)
  have hFM : ∀ᶠ n in atTop, ∀ z ∈ (F n).roots, Ψ z ≤ M + 1 := by
    filter_upwards [hlow, hcard] with n hn hc z hz
    by_contra h
    have hχz : χ z = 0 := by
      dsimp only [χ]
      rw [max_eq_right (by linarith : 0 ≤ Ψ z - M),
        max_eq_left (by linarith : 1 - (Ψ z - M) ≤ 0)]
    have hgap : 1 ≤ (((F n).roots.map (fun w => 1 - χ w)).sum) := by
      have h := Multiset.single_le_sum (s := (F n).roots.map (fun w => 1 - χ w))
        (fun x hx => by
          obtain ⟨w, _, rfl⟩ := Multiset.mem_map.mp hx
          exact sub_nonneg.mpr (hχ1 w))
        (1 - χ z)
        (Multiset.mem_map.mpr ⟨z, hz, rfl⟩)
      simpa only [hχz, sub_zero] using h
    have htotal : ((F n).roots.map χ).sum +
        ((F n).roots.map (fun w => 1 - χ w)).sum = (f.roots.card : ℝ) := by
      rw [← Multiset.sum_map_add]
      have he : (F n).roots.map (fun w => χ w + (1 - χ w)) =
          (F n).roots.map (fun _ => (1 : ℝ)) := by
        apply Multiset.map_congr rfl
        intro z _
        ring
      rw [he, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_one, hc]
    linarith only [hn, hgap, htotal]
  exact tendsto_root_weight_sum_of_bounded hf hconv hcard hΨ hΨ0
    (fun z hz => (hfM z hz).trans (le_add_of_nonneg_right zero_le_one)) hFM


/-- Continuous nonnegative root sums survive arbitrary small constant
perturbations, including at multiple roots. -/
theorem tendsto_sum_roots_add_C {p : ℂ[X]} (hp : p ≠ 0)
    {a : ℕ → ℂ} (ha : Tendsto a atTop (𝓝 0))
    {Ψ : ℂ → ℝ} (hΨ : Continuous Ψ) (hΨ0 : ∀ z, 0 ≤ Ψ z) :
    Tendsto (fun n => ((p + C (a n)).roots.map Ψ).sum) atTop
      (𝓝 (p.roots.map Ψ).sum) := by
  have hu : TendstoUniformly (fun n z => (p + C (a n)).eval z) p.eval atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [ha.eventually (Metric.ball_mem_nhds (0 : ℂ) hε)] with n hn z
    rw [eval_add, eval_C, dist_eq_norm, sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg]
    simpa only [Metric.mem_ball, dist_zero_right] using hn
  apply tendsto_sum_roots_of_fixed_card hp hu.tendstoLocallyUniformly _ hΨ hΨ0
  exact Filter.Eventually.of_forall fun n => by
    rw [IsAlgClosed.card_roots_eq_natDegree, IsAlgClosed.card_roots_eq_natDegree,
      natDegree_add_C]

/-- Every nonnegative power of squared depth plus a nonnegative offset is
continuous under vanishing constant perturbations. -/
theorem tendsto_sum_root_depth_powers_add_C {p : ℂ[X]} (hp : p ≠ 0)
    {a : ℕ → ℂ} (ha : Tendsto a atTop (𝓝 0))
    {q c : ℝ} (hq : 0 ≤ q) (hc : 0 ≤ c) :
    Tendsto (fun n => ((p + C (a n)).roots.map (fun z => (z.im ^ 2 + c) ^ q)).sum)
      atTop (𝓝 (p.roots.map (fun z => (z.im ^ 2 + c) ^ q)).sum) := by
  exact tendsto_sum_roots_add_C hp ha
    (((Complex.continuous_im.pow 2).add continuous_const).rpow_const
      (fun _ => Or.inr hq))
    (fun z => Real.rpow_nonneg (add_nonneg (sq_nonneg z.im) hc) q)

#print axioms tendsto_sum_roots_of_fixed_card
#print axioms tendsto_sum_roots_add_C
#print axioms tendsto_sum_root_depth_powers_add_C

end GaloisForLFunctions.HTGeometry

