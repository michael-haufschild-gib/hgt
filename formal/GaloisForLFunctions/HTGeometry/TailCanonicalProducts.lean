import GaloisForLFunctions.HTGeometry.CanonicalProductPredicateSplit
import GaloisForLFunctions.HTGeometry.CanonicalProductGrowth
import GaloisForLFunctions.HTGeometry.CanonicalProductE1Divisor

/-!
# Tails of genus-one canonical products

For nonzero points `a i` with `∑ ‖a i‖⁻² < ∞` and a finite index set `T`, the tail
`P_T(z) = ∏'_{i ∉ T} E₁(z / a i)` is the factor that remains after the finitely many factors
indexed by `T` are removed. It is entire and:

* vanishes at `w ≠ 0` to at least the number of indices `i ∉ T` with `a i = w`
  (`le_analyticOrderAt_canonicalProductE1Tail`);
* obeys a Gaussian bound uniform in `T`: for every `δ > 0`, `‖P_T(z)‖ ≤ C e^{δ‖z‖²}`
  (`exists_norm_canonicalProductE1Tail_le`), because the minimal-growth majorant
  `∑ min(2r/‖a i‖, 2r²/‖a i‖²)` is `o(r²)`;
* tends to `1` pointwise as `T` exhausts the index type
  (`tendsto_canonicalProductE1Tail_one`), since `‖P_T(z) − 1‖ ≤ exp(∑_{i ∉ T} ‖E₁(z/a i) − 1‖) − 1`.

These are the three properties a tail must have to serve as an approximate identity that kills
all but finitely many prescribed zeros.
-/

open Complex Filter Topology Set Asymptotics
open GaloisForLFunctions.CountableDivisor

namespace RHTower

noncomputable section

variable {ι : Type*}

/-- The tail of the genus-one canonical product outside the finite index set `T`. -/
def canonicalProductE1Tail (a : ι → ℂ) (T : Finset ι) : ℂ → ℂ :=
  canonicalProductE1IndexedComplement a (· ∈ T)

theorem canonicalProductE1Tail_analytic (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ (2 : ℕ))) (T : Finset ι) :
    AnalyticOnNhd ℂ (canonicalProductE1Tail a T) Set.univ :=
  canonicalProductE1IndexedComplement_analytic a _ ha hsum

theorem canonicalProductE1Tail_differentiable (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ (2 : ℕ))) (T : Finset ι) :
    Differentiable ℂ (canonicalProductE1Tail a T) := fun z =>
  (canonicalProductE1Tail_analytic a ha hsum T z (Set.mem_univ z)).differentiableAt

/-- Square-summable reciprocal norms force finitely many points in every ball. -/
theorem locallyFiniteDivisor_of_summable_inv_sq {a : ι → ℂ} (ha : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ (2 : ℕ))) : LocallyFiniteDivisor a := by
  intro r
  rcases le_or_gt r 0 with hr | hr
  · refine Set.finite_empty.subset fun i hi => ?_
    have : 0 < ‖a i‖ := norm_pos_iff.mpr (ha i)
    exact absurd (lt_of_lt_of_le this (le_trans hi hr)) (lt_irrefl 0)
  · have hev : ∀ᶠ i in cofinite, 1 / ‖a i‖ ^ (2 : ℕ) < 1 / r ^ (2 : ℕ) :=
      hsum.tendsto_cofinite_zero.eventually_lt_const (by positivity)
    refine (Filter.eventually_cofinite.mp hev).subset fun i hi => ?_
    have hpos : 0 < ‖a i‖ := norm_pos_iff.mpr (ha i)
    simp only [Set.mem_setOf_eq, not_lt] at hi ⊢
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hpos.le hi 2)

/-! ### Divisor of the tail -/

/-- The tail vanishes at `w ≠ 0` to at least the number of indices outside `T` that sit at `w`. -/
theorem le_analyticOrderAt_canonicalProductE1Tail (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ (2 : ℕ))) (T : Finset ι) {w : ℂ} (hw : w ≠ 0)
    (F : Finset ι) (hF : ∀ i ∈ F, a i = w ∧ i ∉ T) :
    (F.card : ℕ∞) ≤ analyticOrderAt (canonicalProductE1Tail a T) w := by
  classical
  let b : {i // ¬ i ∈ T} → ℂ := fun i => a i.1
  have hb : ∀ i, b i ≠ 0 := fun i => ha i.1
  have hbsum : Summable (fun i => 1 / ‖b i‖ ^ (2 : ℕ)) :=
    canonicalProductE1IndexedComplement_inv_sq_summable a _ hsum
  have hbloc : LocallyFiniteDivisor b := locallyFiniteDivisor_of_summable_inv_sq hb hbsum
  change (F.card : ℕ∞) ≤ analyticOrderAt (canonicalProductE1Indexed b) w
  rw [analyticOrderAt_canonicalProductE1Indexed hb hbloc hbsum hw]
  have hcard : (F.subtype (fun i => ¬ i ∈ T)).card = F.card := by
    rw [Finset.card_subtype, Finset.filter_true_of_mem fun i hi => (hF i hi).2]
  have hsub : ((F.subtype (fun i => ¬ i ∈ T) : Finset {i // ¬ i ∈ T}) : Set _) ⊆
      {i | b i = w} := by
    intro i hi
    exact (hF i.1 (Finset.mem_subtype.mp hi)).1
  have hle := Set.ncard_le_ncard hsub (finite_fiber hbloc w)
  rw [Set.ncard_coe_finset, hcard] at hle
  exact_mod_cast hle

/-! ### Uniform Gaussian bound -/

/-- The minimal-growth majorant of a square-summable divisor is below `δ r² + C`. -/
theorem exists_minGrowth_le (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ (2 : ℕ))) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r →
      ∑' i, min (2 * r / ‖a i‖) (2 * r ^ (2 : ℕ) / ‖a i‖ ^ (2 : ℕ)) ≤ δ * r ^ (2 : ℕ) + C := by
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp
    ((canonicalProduct_minGrowth_isLittleO_sq a ha hsum).bound hδ)
  set S : ℝ := ∑' i, 1 / ‖a i‖ ^ (2 : ℕ)
  have hS : 0 ≤ S := tsum_nonneg fun i => by positivity
  refine ⟨2 * max R 0 ^ (2 : ℕ) * S, by positivity, fun r hr => ?_⟩
  have hmin_nonneg : ∀ i, 0 ≤ min (2 * r / ‖a i‖) (2 * r ^ (2 : ℕ) / ‖a i‖ ^ (2 : ℕ)) :=
    fun i => le_min (by positivity) (by positivity)
  rcases le_or_gt R r with hRr | hrR
  · have h := hR r hRr
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hr,
      abs_of_nonneg (tsum_nonneg hmin_nonneg), abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 2)]
      at h
    have : 0 ≤ 2 * max R 0 ^ (2 : ℕ) * S := by positivity
    linarith
  · have hle : ∀ i, min (2 * r / ‖a i‖) (2 * r ^ (2 : ℕ) / ‖a i‖ ^ (2 : ℕ)) ≤
        2 * max R 0 ^ (2 : ℕ) * (1 / ‖a i‖ ^ (2 : ℕ)) := by
      intro i
      refine (min_le_right _ _).trans ?_
      rw [div_eq_mul_one_div]
      have hr2 : r ^ (2 : ℕ) ≤ max R 0 ^ (2 : ℕ) :=
        pow_le_pow_left₀ hr (hrR.le.trans (le_max_left R 0)) 2
      gcongr
    have hsum' : Summable (fun i => 2 * max R 0 ^ (2 : ℕ) * (1 / ‖a i‖ ^ (2 : ℕ))) :=
      hsum.mul_left _
    have htsum := Summable.tsum_le_tsum hle (hsum'.of_nonneg_of_le hmin_nonneg hle) hsum'
    rw [tsum_mul_left] at htsum
    have : 0 ≤ δ * r ^ (2 : ℕ) := by positivity
    linarith

/-- **Uniform Gaussian bound.** For every `δ > 0` one constant bounds every tail:
`‖P_T(z)‖ ≤ C e^{δ ‖z‖²}` for all finite `T` and all `z`. -/
theorem exists_norm_canonicalProductE1Tail_le (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ (2 : ℕ))) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Finset ι) (z : ℂ),
      ‖canonicalProductE1Tail a T z‖ ≤ C * Real.exp (δ * ‖z‖ ^ (2 : ℕ)) := by
  obtain ⟨C, hC, hmaj⟩ := exists_minGrowth_le a ha hsum hδ
  refine ⟨Real.exp C, Real.exp_pos C, fun T z => ?_⟩
  let m : ι → ℝ := fun i => min (2 * ‖z‖ / ‖a i‖) (2 * ‖z‖ ^ (2 : ℕ) / ‖a i‖ ^ (2 : ℕ))
  have hm_nonneg : ∀ i, 0 ≤ m i := fun i => le_min (by positivity) (by positivity)
  have hm_sum : Summable m :=
    ((hsum.mul_left (2 * ‖z‖ ^ (2 : ℕ))).of_nonneg_of_le hm_nonneg fun i => by
      refine (min_le_right _ _).trans_eq ?_
      ring)
  have hb := canonicalProductE1Indexed_norm_le_exp_min (fun i : {i // ¬ i ∈ T} => a i.1)
    (fun i => ha i.1) (canonicalProductE1IndexedComplement_inv_sq_summable a _ hsum) z
  have hsub : ∑' i : {i // ¬ i ∈ T}, m i.1 ≤ ∑' i, m i :=
    Summable.tsum_subtype_le m {i | ¬ i ∈ T} hm_nonneg hm_sum
  calc ‖canonicalProductE1Tail a T z‖
      ≤ Real.exp (∑' i : {i // ¬ i ∈ T}, m i.1) := hb
    _ ≤ Real.exp (δ * ‖z‖ ^ (2 : ℕ) + C) :=
        Real.exp_le_exp.mpr (hsub.trans (hmaj ‖z‖ (norm_nonneg z)))
    _ = Real.exp C * Real.exp (δ * ‖z‖ ^ (2 : ℕ)) := by rw [Real.exp_add, mul_comm]

/-! ### Exhaustion -/

/-- The distance of a tail from `1` is controlled by its centered factors:
`‖P_T(z) − 1‖ ≤ exp(∑_{i ∉ T} ‖E₁(z/a i) − 1‖) − 1`. -/
theorem norm_canonicalProductE1Tail_sub_one_le (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ (2 : ℕ))) (T : Finset ι) (z : ℂ) :
    ‖canonicalProductE1Tail a T z - 1‖ ≤
      Real.exp (∑' i : {i // i ∉ T}, ‖weierstrassE1 (z / a i) - 1‖) - 1 := by
  let u : {i // ¬ i ∈ T} → ℂ := fun i => weierstrassE1 (z / a i.1) - 1
  have hu : Summable (fun i => ‖u i‖) :=
    canonicalProductE1Indexed_sub_one_norm_summable (fun i : {i // ¬ i ∈ T} => a i.1)
      (fun i => ha i.1) (canonicalProductE1IndexedComplement_inv_sq_summable a _ hsum) z
  have hprod : HasProd (fun i => 1 + u i) (canonicalProductE1Tail a T z) := by
    have h := (multipliable_one_add_of_summable hu).hasProd
    convert h using 1
    change ∏' i : {i // ¬ i ∈ T}, weierstrassE1 (z / a i.1) = _
    exact tprod_congr fun i => by simp only [u]; ring
  refine le_of_tendsto ((continuous_norm.comp (continuous_sub_right 1)).continuousAt.tendsto.comp
    hprod) (Eventually.of_forall fun s => ?_)
  refine (s.norm_prod_one_add_sub_one_le u).trans ?_
  gcongr
  exact hu.sum_le_tsum s fun i _ => norm_nonneg _

/-- **Exhaustion.** As `T` exhausts the index type, the tail tends to `1` at every point. -/
theorem tendsto_canonicalProductE1Tail_one (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ (2 : ℕ))) (z : ℂ) :
    Tendsto (fun T : Finset ι => canonicalProductE1Tail a T z) atTop (𝓝 1) := by
  have htail := tendsto_tsum_compl_atTop_zero (fun i => ‖weierstrassE1 (z / a i) - 1‖)
  have hexp : Tendsto (fun T : Finset ι =>
      Real.exp (∑' i : {i // i ∉ T}, ‖weierstrassE1 (z / a i) - 1‖) - 1) atTop (𝓝 0) := by
    simpa using ((Real.continuous_exp.tendsto 0).comp htail).sub_const 1
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun T => norm_canonicalProductE1Tail_sub_one_le a ha hsum T z) hexp

end

end RHTower
