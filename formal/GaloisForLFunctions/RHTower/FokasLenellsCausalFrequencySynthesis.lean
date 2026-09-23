import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyTotality
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Algebra.Order.Field
open Complex Set Filter Topology
noncomputable section
namespace RHTower.FokasLenells
set_option backward.isDefEq.respectTransparency false
section GenericSynthesis
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
local instance frequencySynthesisGenericEndRing : NormedRing (E →L[ℂ] E) :=
  ContinuousLinearMap.toNormedRing

private def rotatedMean (T : E →L[ℂ] E) (z : ℂ) (N : ℕ) : E →L[ℂ] E :=
  ((N : ℝ)⁻¹ : ℂ) • ∑ n ∈ Finset.range N, (z⁻¹) ^ n • T ^ n

private def obsCorr (T : E →L[ℂ] E) (ℓ : E →L[ℂ] ℂ) (N : ℕ) (u v : E) : ℂ :=
  ((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N, ℓ ((T ^ n) u) * star (ℓ ((T ^ n) v))

private theorem unit_star (z : ℂ) (hz : ‖z‖ = 1) : star z = z⁻¹ :=
  (Circle.coe_inv_eq_conj ⟨z, mem_sphere_zero_iff_norm.mpr hz⟩).symm

private theorem mean_observe (T : E →L[ℂ] E) (ℓ : E →L[ℂ] ℂ) (z : ℂ) (N : ℕ) (u : E) :
    ℓ (rotatedMean T z N u) =
      ((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N, (z⁻¹) ^ n * ℓ ((T ^ n) u) := by
  simp only [rotatedMean, smul_apply, sum_apply, map_smul, map_sum, smul_eq_mul]

private theorem corr_eigen (T : E →L[ℂ] E) (ℓ : E →L[ℂ] ℂ) (u v : E)
    (z : ℂ) (hz : ‖z‖ = 1) (he : ∀ n : ℕ, (T ^ n) v = z ^ n • v) (N : ℕ) :
    obsCorr T ℓ N u v = star (ℓ v) * ℓ (rotatedMean T z N u) := by
  rw [mean_observe]
  unfold obsCorr
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [he n, map_smul, smul_eq_mul, star_mul, star_pow, unit_star z hz]
  ring

private theorem corr_zero (T : E →L[ℂ] E) (ℓ : E →L[ℂ] ℂ) (N : ℕ) (u : E) :
    obsCorr T ℓ N u 0 = 0 := by
  simp only [obsCorr, map_zero, star_zero, mul_zero, Finset.sum_const_zero]

private theorem corr_add (T : E →L[ℂ] E) (ℓ : E →L[ℂ] ℂ) (N : ℕ) (u v w : E) :
    obsCorr T ℓ N u (v + w) = obsCorr T ℓ N u v + obsCorr T ℓ N u w := by
  simp only [obsCorr, map_add, star_add, mul_add, Finset.sum_add_distrib]

private theorem corr_smul (T : E →L[ℂ] E) (ℓ : E →L[ℂ] ℂ) (N : ℕ)
    (u v : E) (c : ℂ) : obsCorr T ℓ N u (c • v) = star c * obsCorr T ℓ N u v := by
  simp only [obsCorr, map_smul, smul_eq_mul, star_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

private theorem core_corr_tendsto (T : E →L[ℂ] E) (ℓ : E →L[ℂ] ℂ) (u : E)
    (v : I → E) (z : I → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (he : ∀ i n, (T ^ n) (v i) = (z i) ^ n • v i)
    (hm : ∀ i, Tendsto (fun N : ℕ => ℓ (rotatedMean T (z i) N u)) atTop (𝓝 0))
    {w : E} (hw : w ∈ Submodule.span ℂ (Set.range v)) :
    Tendsto (fun N : ℕ => obsCorr T ℓ N u w) atTop (𝓝 0) := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    have hc : Tendsto (fun N : ℕ => star (ℓ (v i)) * ℓ (rotatedMean T (z i) N u))
        atTop (𝓝 (star (ℓ (v i)) * 0)) := tendsto_const_nhds.mul (hm i)
    simpa only [corr_eigen T ℓ u (v i) (z i) (hz i) (he i), mul_zero] using hc
  | zero =>
    simpa only [corr_zero] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  | add a b ha hb ia ib =>
    simpa only [corr_add, add_zero] using ia.add ib
  | smul c a ha ih =>
    have hc : Tendsto (fun N : ℕ => star c * obsCorr T ℓ N u a)
        atTop (𝓝 (star c * 0)) := tendsto_const_nhds.mul ih
    simpa only [corr_smul, mul_zero] using hc

private theorem norm_scalar_cesaro_le (f : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ n, ‖f n‖ ≤ C) (N : ℕ) :
    ‖((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N, f n‖ ≤ C := by
  by_cases hN : N = 0
  · subst N
    simpa only [Finset.range_zero, Finset.sum_empty, mul_zero, norm_zero] using hC
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hi : 0 ≤ (N : ℝ)⁻¹ := by positivity
  calc
    ‖((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N, f n‖ =
        (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.range N, f n‖ := by
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Nat.cast_nonneg N)]
    _ ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖f n‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hi
    _ ≤ (N : ℝ)⁻¹ * ∑ _n ∈ Finset.range N, C :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun n hn => hf n)) hi
    _ = C := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ hn, one_mul]

private theorem corr_gap (T : E →L[ℂ] E) (ℓ : E →L[ℂ] ℂ) (N : ℕ) (u v : E) :
    obsCorr T ℓ N u u - obsCorr T ℓ N u v =
      ((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N,
        ℓ ((T ^ n) u) * star (ℓ ((T ^ n) (u - v))) := by
  simp only [obsCorr, map_sub, star_sub, mul_sub, Finset.sum_sub_distrib]

private theorem norm_corr_gap_le (T : E →L[ℂ] E)
    (ht : ∀ n u, ‖(T ^ n) u‖ ≤ ‖u‖) (ℓ : E →L[ℂ] ℂ) (N : ℕ) (u v : E) :
    ‖obsCorr T ℓ N u u - obsCorr T ℓ N u v‖ ≤ ‖ℓ‖ ^ (2 : ℕ) * ‖u‖ * ‖u - v‖ := by
  rw [corr_gap]
  apply norm_scalar_cesaro_le _ _ (by positivity)
  intro n
  have ha : ‖ℓ ((T ^ n) u)‖ ≤ ‖ℓ‖ * ‖u‖ :=
    (ℓ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (ht n u) (norm_nonneg ℓ))
  have hb : ‖ℓ ((T ^ n) (u - v))‖ ≤ ‖ℓ‖ * ‖u - v‖ :=
    (ℓ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (ht n (u - v)) (norm_nonneg ℓ))
  calc
    ‖ℓ ((T ^ n) u) * star (ℓ ((T ^ n) (u - v)))‖ =
        ‖ℓ ((T ^ n) u)‖ * ‖ℓ ((T ^ n) (u - v))‖ := by rw [norm_mul, norm_star]
    _ ≤ (‖ℓ‖ * ‖u‖) * (‖ℓ‖ * ‖u - v‖) := mul_le_mul ha hb (norm_nonneg _) (by positivity)
    _ = ‖ℓ‖ ^ (2 : ℕ) * ‖u‖ * ‖u - v‖ := by ring

private theorem self_corr_tendsto_zero (T : E →L[ℂ] E)
    (ht : ∀ n u, ‖(T ^ n) u‖ ≤ ‖u‖) (ℓ : E →L[ℂ] ℂ) (u : E) (A : Set E)
    (ha : ∀ v ∈ A, Tendsto (fun N : ℕ => obsCorr T ℓ N u v) atTop (𝓝 0))
    (hu : u ∈ closure A) : Tendsto (fun N : ℕ => obsCorr T ℓ N u u) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let C : ℝ := ‖ℓ‖ ^ (2 : ℕ) * ‖u‖
  have hC : 0 ≤ C := by positivity
  obtain ⟨v, hv, huv⟩ := Metric.mem_closure_iff.mp hu (ε / (2 * (C + 1))) (by positivity)
  have hvn : ‖u - v‖ < ε / (2 * (C + 1)) := by simpa only [dist_eq_norm] using huv
  have hsmall : C * ‖u - v‖ < ε / 2 := by
    have hd := (lt_div_iff₀ (show 0 < 2 * (C + 1) by positivity)).mp hvn
    nlinarith [norm_nonneg (u - v)]
  have hevent := Metric.tendsto_nhds.mp (ha v hv) (ε / 2) (by linarith)
  filter_upwards [hevent] with N hN
  have hg := norm_corr_gap_le T ht ℓ N u v
  change ‖obsCorr T ℓ N u u - obsCorr T ℓ N u v‖ ≤ C * ‖u - v‖ at hg
  have htri := norm_add_le (obsCorr T ℓ N u u - obsCorr T ℓ N u v) (obsCorr T ℓ N u v)
  rw [sub_add_cancel] at htri
  simp only [dist_zero_right] at hN ⊢
  linarith

private theorem complex_self_square (z : ℂ) : z * star z = ((‖z‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  change z * (starRingEnd ℂ) z = _
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

private theorem corr_self_re (T : E →L[ℂ] E) (ℓ : E →L[ℂ] ℂ) (N : ℕ) (u : E) :
    (obsCorr T ℓ N u u).re = (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖ℓ ((T ^ n) u)‖ ^ (2 : ℕ) := by
  have h : obsCorr T ℓ N u u =
      (((N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖ℓ ((T ^ n) u)‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    simp only [obsCorr, complex_self_square, ← Complex.ofReal_sum]
    rw [Complex.ofReal_mul, Complex.ofReal_inv]
  rw [h, Complex.ofReal_re]

private theorem mean_square_zero_of_modes (T : E →L[ℂ] E)
    (ht : ∀ n u, ‖(T ^ n) u‖ ≤ ‖u‖) (ℓ : E →L[ℂ] ℂ) (u : E)
    (v : I → E) (z : I → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (he : ∀ i n, (T ^ n) (v i) = (z i) ^ n • v i)
    (hm : ∀ i, Tendsto (fun N : ℕ => ℓ (rotatedMean T (z i) N u)) atTop (𝓝 0))
    (hu : u ∈ closure (Submodule.span ℂ (Set.range v) : Set E)) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖ℓ ((T ^ n) u)‖ ^ (2 : ℕ))
      atTop (𝓝 0) := by
  have hc := self_corr_tendsto_zero T ht ℓ u (Submodule.span ℂ (Set.range v))
    (fun w hw => core_corr_tendsto T ℓ u v z hz he hm hw) hu
  have hr := (Complex.continuous_re.tendsto 0).comp hc
  simpa only [Function.comp_def, corr_self_re, Complex.zero_re] using! hr

private theorem compact_finite_norming (K : Set E) (hK : IsCompact K) (δ : ℝ)
    (hδ : 0 < δ) (hlow : ∀ v ∈ K, δ ≤ ‖v‖) :
    ∃ s : Finset (E →L[ℂ] ℂ), (∀ ℓ ∈ s, ‖ℓ‖ ≤ 1) ∧
      ∀ v ∈ K, δ ^ (2 : ℕ) / 4 ≤ ∑ ℓ ∈ s, ‖ℓ v‖ ^ (2 : ℕ) := by
  classical
  let J := {ℓ : E →L[ℂ] ℂ // ‖ℓ‖ ≤ 1}
  let U : J → Set E := fun ℓ => {v | δ / 2 < ‖ℓ.val v‖}
  have hU : ∀ ℓ : J, IsOpen (U ℓ) :=
    fun ℓ => isOpen_lt continuous_const ℓ.val.continuous.norm
  have hcover : K ⊆ ⋃ ℓ : J, U ℓ := by
    intro v hv
    obtain ⟨ℓ, hℓ, hval⟩ := exists_dual_vector'' ℂ v
    refine Set.mem_iUnion.mpr ⟨⟨ℓ, hℓ⟩, ?_⟩
    change δ / 2 < ‖ℓ v‖
    simp only [hval, norm_algebraMap', norm_norm]
    linarith [hlow v hv]
  obtain ⟨t, hcover'⟩ := hK.elim_finite_subcover U hU hcover
  refine ⟨t.image (fun ℓ : J => ℓ.val), ?_, ?_⟩
  · intro ℓ hℓ
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hℓ
    exact f.property
  · intro v hv
    have hmem := hcover' hv
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨ℓ, hℓ, hobs⟩ := hmem
    have hobs' : δ / 2 < ‖ℓ.val v‖ := hobs
    have hsq : δ ^ (2 : ℕ) / 4 ≤ ‖ℓ.val v‖ ^ (2 : ℕ) := by
      have hp : 0 ≤ (‖ℓ.val v‖ - δ / 2) * (‖ℓ.val v‖ + δ / 2) :=
        mul_nonneg (by linarith) (by positivity)
      nlinarith
    exact hsq.trans (Finset.single_le_sum (fun (f : E →L[ℂ] ℂ) _ => sq_nonneg ‖f v‖)
      (Finset.mem_image.mpr ⟨ℓ, hℓ, rfl⟩))

private theorem le_cesaro_of_pointwise (f : ℕ → ℝ) (r : ℝ) (hf : ∀ n, r ≤ f n)
    (N : ℕ) (hN : 0 < N) : r ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f n := by
  have hs : (∑ _n ∈ Finset.range N, r) ≤ ∑ n ∈ Finset.range N, f n :=
    Finset.sum_le_sum (fun n hn => hf n)
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ (N : ℝ)⁻¹ by positivity)
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hn, one_mul] using hm

private theorem sum_observation_means (s : Finset (E →L[ℂ] ℂ)) (x : ℕ → E) (N : ℕ) :
    (∑ ℓ ∈ s, (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖ℓ (x n)‖ ^ (2 : ℕ)) =
      (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ∑ ℓ ∈ s, ‖ℓ (x n)‖ ^ (2 : ℕ) := by
  rw [← Finset.mul_sum, Finset.sum_comm]

private theorem finite_mean_square_floor (s : Finset (E →L[ℂ] ℂ)) (x : ℕ → E) (r : ℝ)
    (hf : ∀ n, r ≤ ∑ ℓ ∈ s, ‖ℓ (x n)‖ ^ (2 : ℕ))
    (hm : ∀ ℓ ∈ s, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
      ∑ n ∈ Finset.range N, ‖ℓ (x n)‖ ^ (2 : ℕ)) atTop (𝓝 0)) : r ≤ 0 := by
  have hsum : Tendsto (fun N : ℕ => ∑ ℓ ∈ s, (N : ℝ)⁻¹ *
      ∑ n ∈ Finset.range N, ‖ℓ (x n)‖ ^ (2 : ℕ)) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum s hm
  apply ge_of_tendsto hsum
  apply Filter.eventually_atTop.mpr
  refine ⟨1, ?_⟩
  intro N hN
  exact (le_cesaro_of_pointwise (fun n => ∑ ℓ ∈ s, ‖ℓ (x n)‖ ^ (2 : ℕ))
    r hf N (by omega)).trans_eq (sum_observation_means s x N).symm

private theorem eigen_span_invariant (T : E →L[ℂ] E) (v : I → E) (z : I → ℂ)
    (he : ∀ i, T (v i) = z i • v i) :
    ∀ u ∈ Submodule.span ℂ (Set.range v), T u ∈ Submodule.span ℂ (Set.range v) := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b ha hb ia ib => rw [map_add]; exact Submodule.add_mem _ ia ib
  | smul c a ha ih => rw [map_smul]; exact Submodule.smul_mem _ c ih

private theorem closure_invariant (T : E →L[ℂ] E) (A : Submodule ℂ E)
    (ha : ∀ u ∈ A, T u ∈ A) :
    ∀ u ∈ A.topologicalClosure, T u ∈ A.topologicalClosure := by
  have hc : IsClosed {u : E | T u ∈ A.topologicalClosure} :=
    A.isClosed_topologicalClosure.preimage T.continuous
  exact hc.closure_subset_iff.mpr (fun u hu => A.le_topologicalClosure (ha u hu))

private theorem quotient_map_norm_le (D : Submodule ℂ E) (F : E →L[ℂ] E)
    (hf : ∀ v, ‖F v‖ ≤ ‖v‖) (hd : ∀ v ∈ D, F v ∈ D) (u : E) :
    ‖D.mkQL (F u)‖ ≤ ‖D.mkQL u‖ := by
  apply (QuotientAddGroup.le_norm_iff (S := D.toAddSubgroup)).mpr
  intro m hm
  have hm' : (Submodule.Quotient.mk m : E ⧸ D) = Submodule.Quotient.mk u := hm
  have he : F m - F u ∈ D := by
    rw [← map_sub]
    exact hd (m - u) ((Submodule.Quotient.eq D).mp hm')
  have heq : (Submodule.Quotient.mk (F m) : E ⧸ D) = Submodule.Quotient.mk (F u) :=
    (Submodule.Quotient.eq D).mpr he
  change ‖(Submodule.Quotient.mk (F u) : E ⧸ D)‖ ≤ ‖m‖
  rw [← heq]
  exact (Submodule.Quotient.norm_mk_le D (F m)).trans (hf m)

private theorem quotient_recurrent_power_norm (D : Submodule ℂ E) (T : E →L[ℂ] E)
    (ht : ∀ n v, ‖(T ^ n) v‖ ≤ ‖v‖)
    (hd : ∀ n v, v ∈ D → (T ^ n) v ∈ D) (u : E)
    (hu : MapClusterPt u atTop (fun n : ℕ => (T ^ n) u)) (n : ℕ) :
    ‖D.mkQL ((T ^ n) u)‖ = ‖D.mkQL u‖ := by
  apply le_antisymm
  · exact quotient_map_norm_le D (T ^ n) (ht n) (hd n) u
  · have hc : IsClosed {v : E | ‖D.mkQL v‖ ≤ ‖D.mkQL ((T ^ n) u)‖} :=
      isClosed_le (continuous_norm.comp D.mkQL.continuous) continuous_const
    apply hc.mem_of_mapClusterPt hu
    apply Filter.eventually_atTop.mpr
    refine ⟨n, ?_⟩
    intro k hk
    have hp : k = (k - n) + n := by omega
    change ‖D.mkQL ((T ^ k) u)‖ ≤ ‖D.mkQL ((T ^ n) u)‖
    rw [hp, pow_add, mul_apply_eq_comp]
    exact quotient_map_norm_le D (T ^ (k - n)) (ht (k - n)) (hd (k - n)) ((T ^ n) u)

private theorem compact_observation_zero (x : ℕ → E) (u : E) (K : Set E)
    (hK : IsCompact K) (hx : ∀ n, x n ∈ K) (hk : ∀ v ∈ K, ‖v‖ = ‖u‖)
    (hm : ∀ ℓ : E →L[ℂ] ℂ,
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖ℓ (x n)‖ ^ (2 : ℕ))
        atTop (𝓝 0)) : u = 0 := by
  by_contra hu
  have hp : 0 < ‖u‖ := norm_pos_iff.mpr hu
  obtain ⟨s, hs, hfloor⟩ := compact_finite_norming K hK ‖u‖ hp
    (fun v hv => (hk v hv).ge)
  have hle := finite_mean_square_floor s x (‖u‖ ^ (2 : ℕ) / 4)
    (fun n => hfloor (x n) (hx n)) (fun ℓ hℓ => hm ℓ)
  nlinarith [sq_pos_of_pos hp]

private theorem quotient_zero_of_observed_means (D : Submodule ℂ E)
    [IsClosed (D : Set E)] (T : E →L[ℂ] E)
    (ht : ∀ n v, ‖(T ^ n) v‖ ≤ ‖v‖)
    (hd : ∀ n v, v ∈ D → (T ^ n) v ∈ D) (u : E)
    (hu : MapClusterPt u atTop (fun n : ℕ => (T ^ n) u))
    (hc : IsCompact (closure (Set.range (fun n : ℕ => (T ^ n) u))))
    (hm : ∀ ℓ : (E ⧸ D) →L[ℂ] ℂ,
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
        ‖ℓ (D.mkQL ((T ^ n) u))‖ ^ (2 : ℕ)) atTop (𝓝 0)) : D.mkQL u = 0 := by
  let K : Set (E ⧸ D) := D.mkQL '' closure (Set.range (fun n : ℕ => (T ^ n) u))
  have hK : IsCompact K := hc.image D.mkQL.continuous
  have hx : ∀ n : ℕ, D.mkQL ((T ^ n) u) ∈ K := fun n =>
    ⟨(T ^ n) u, subset_closure (Set.mem_range_self n), rfl⟩
  have hk : ∀ v ∈ K, ‖v‖ = ‖D.mkQL u‖ := by
    rintro _ ⟨v, hv, rfl⟩
    have hclosed : IsClosed {v : E | ‖D.mkQL v‖ = ‖D.mkQL u‖} :=
      isClosed_eq (continuous_norm.comp D.mkQL.continuous) continuous_const
    apply hclosed.closure_subset_iff.mpr ?_ hv
    rintro _ ⟨n, rfl⟩
    exact quotient_recurrent_power_norm D T ht hd u hu n
  exact compact_observation_zero _ (D.mkQL u) K hK hx hk hm

private theorem synthesis_mem_closed_subspace (D : Submodule ℂ E)
    [IsClosed (D : Set E)] (T : E →L[ℂ] E)
    (ht : ∀ n w, ‖(T ^ n) w‖ ≤ ‖w‖)
    (hd : ∀ n w, w ∈ D → (T ^ n) w ∈ D)
    (v : I → E) (z : I → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (he : ∀ i n, (T ^ n) (v i) = (z i) ^ n • v i) (u : E)
    (hu : u ∈ closure (Submodule.span ℂ (Set.range v) : Set E))
    (hr : MapClusterPt u atTop (fun n : ℕ => (T ^ n) u))
    (hc : IsCompact (closure (Set.range (fun n : ℕ => (T ^ n) u))))
    (hm : ∀ i, Tendsto (fun N : ℕ => D.mkQL (rotatedMean T (z i) N u)) atTop (𝓝 0)) :
    u ∈ D := by
  apply (Submodule.Quotient.mk_eq_zero D).mp
  apply quotient_zero_of_observed_means D T ht hd u hr hc
  intro ℓ
  apply mean_square_zero_of_modes T ht (ℓ.comp D.mkQL) u v z hz he ?_ hu
  intro i
  have hh := (ℓ.continuous.tendsto 0).comp (hm i)
  simpa only [Function.comp_def, map_zero, ContinuousLinearMap.comp_apply] using! hh
private theorem reconstruction_mem (D : Submodule ℂ E) (a : ℂ) (v w : E)
    (he : a • v = w) (hm : a ≠ 0 → v ∈ D) : w ∈ D := by
  rw [← he]
  by_cases ha : a = 0
  · rw [ha, zero_smul]
    exact D.zero_mem
  · exact D.smul_mem a (hm ha)

private theorem mode_mem_of_scalar (D : Submodule ℂ E) (a : ℂ) (ha : a ≠ 0)
    (v : E) (hv : a • v ∈ D) : v ∈ D := by
  have hs := D.smul_mem a⁻¹ hv
  simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul] using hs

private theorem closed_span_le_of_modes (v : I → E) (D : Submodule ℂ E)
    (hD : IsClosed (D : Set E)) (hv : ∀ i, v i ∈ D) :
    (Submodule.span ℂ (Set.range v)).topologicalClosure ≤ D := by
  apply hD.closure_subset_iff.mpr
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact hv i

private theorem rotatedMean_mem_cyclic (T : E →L[ℂ] E) (u : E) (z : ℂ) (N : ℕ) :
    rotatedMean T z N u ∈ Submodule.span ℂ (Set.range (fun n : ℕ => (T ^ n) u)) := by
  simp only [rotatedMean, smul_apply, sum_apply]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro n hn
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self n))
end GenericSynthesis
local instance frequencySynthesisActualEndRing : NormedRing
    (causalBoundedChain →L[ℂ] causalBoundedChain) := ContinuousLinearMap.toNormedRing

/-- The actual closed bounded-chain span of the frequencies in a specified set. -/
def causalFrequencySynthesisSpace (b : ℝ) (A : Set ℝ) : Submodule ℂ causalBoundedChain :=
  (Submodule.span ℂ (Set.range (fun ω : A => causalBoundedUnitEigenchain b ω.val))).topologicalClosure

private theorem synthesis_power_invariant (b : ℝ) (A : Set ℝ) (n : ℕ) :
    ∀ w ∈ causalFrequencySynthesisSpace b A,
      (causalBoundedChainShift ^ n) w ∈ causalFrequencySynthesisSpace b A :=
  closure_invariant (causalBoundedChainShift ^ n)
    (Submodule.span ℂ (Set.range (fun ω : A => causalBoundedUnitEigenchain b ω.val)))
    (eigen_span_invariant (causalBoundedChainShift ^ n)
      (fun ω : A => causalBoundedUnitEigenchain b ω.val)
      (fun ω : A => (causalUnitBoundaryRate b ω.val).val ^ n)
      (fun ω => causalBoundedChainShift_pow_unitEigenchain b ω.val n))

private theorem projection_mem_active_span (b : ℝ) (u : causalFrequencySpace b) (ω : ℝ) :
    (causalFrequencyProjection b ω u).val ∈ causalFrequencySynthesisSpace b
      (Function.support (fun η : ℝ => causalFrequencyCoefficient b η u)) := by
  let A := Function.support (fun η : ℝ => causalFrequencyCoefficient b η u)
  let D := causalFrequencySynthesisSpace b A
  have he : causalFrequencyCoefficient b ω u • causalBoundedUnitEigenchain b ω =
      (causalFrequencyProjection b ω u).val :=
    congrArg (fun w : causalFrequencySpace b => w.val) (causalFrequencyCoefficient_smul_mode b ω u)
  apply reconstruction_mem D (causalFrequencyCoefficient b ω u)
    (causalBoundedUnitEigenchain b ω) (causalFrequencyProjection b ω u).val he
  intro hω
  exact (Submodule.span ℂ (Set.range (fun η : A => causalBoundedUnitEigenchain b η.val))).le_topologicalClosure
    (Submodule.subset_span ⟨⟨ω, hω⟩, rfl⟩)

private theorem active_quotient_mean_zero (b : ℝ) (u : causalFrequencySpace b) (ω : ℝ) :
    Tendsto (fun N : ℕ =>
      (causalFrequencySynthesisSpace b
        (Function.support (fun η : ℝ => causalFrequencyCoefficient b η u))).mkQL
          (rotatedMean causalBoundedChainShift (causalUnitBoundaryRate b ω).val N u.val))
      atTop (𝓝 0) := by
  let D := causalFrequencySynthesisSpace b
    (Function.support (fun η : ℝ => causalFrequencyCoefficient b η u))
  have hp : D.mkQL (causalFrequencyProjection b ω u).val = 0 :=
    (Submodule.Quotient.mk_eq_zero D).mpr (projection_mem_active_span b u ω)
  have hh := (D.mkQL.continuous.tendsto (causalFrequencyProjection b ω u).val).comp
    (causalFrequencyProjection_tendsto b ω u)
  simpa only [Function.comp_def, hp, causalBoundedFrequencyMean, rotatedMean] using! hh

/-- Every actual completed-frequency vector belongs to the closed span of its
own nonzero amplitudes. No convergence of unweighted partial sums is assumed. -/
theorem causalFrequencySpace_mem_closed_span_support (b : ℝ) (u : causalFrequencySpace b) :
    u.val ∈ causalFrequencySynthesisSpace b
      (Function.support (fun ω : ℝ => causalFrequencyCoefficient b ω u)) := by
  let A := Function.support (fun ω : ℝ => causalFrequencyCoefficient b ω u)
  let D := causalFrequencySynthesisSpace b A
  letI : IsClosed (D : Set causalBoundedChain) :=
    (Submodule.span ℂ (Set.range (fun ω : A => causalBoundedUnitEigenchain b ω.val))).isClosed_topologicalClosure
  exact synthesis_mem_closed_subspace D causalBoundedChainShift
    causalBoundedChainShift_pow_norm_le (synthesis_power_invariant b A)
    (causalBoundedUnitEigenchain b) (fun ω => (causalUnitBoundaryRate b ω).val)
    (norm_causalUnitBoundaryRate b) (fun ω n => causalBoundedChainShift_pow_unitEigenchain b ω n)
    u.val u.property (causalFrequencySpace_recurrent b u) (causalFrequencySpace_compact_orbit b u)
    (active_quotient_mean_zero b u)

private theorem projection_mem_cyclic (b : ℝ) (u : causalFrequencySpace b) (ω : ℝ) :
    (causalFrequencyProjection b ω u).val ∈
      (Submodule.span ℂ (Set.range (fun n : ℕ => (causalBoundedChainShift ^ n) u.val))).topologicalClosure := by
  apply (Submodule.span ℂ (Set.range (fun n : ℕ =>
    (causalBoundedChainShift ^ n) u.val))).isClosed_topologicalClosure.mem_of_tendsto
    (causalFrequencyProjection_tendsto b ω u)
  apply Filter.Eventually.of_forall
  intro N
  apply (Submodule.span ℂ (Set.range (fun n : ℕ =>
    (causalBoundedChainShift ^ n) u.val))).le_topologicalClosure
  exact rotatedMean_mem_cyclic causalBoundedChainShift u.val (causalUnitBoundaryRate b ω).val N

/-- The closed forward-shift cyclic space is exactly the closed span of the
vector's nonzero actual frequencies. Thus orbit generation and active spectral
support give the same completed bounded-chain subspace. -/
theorem causalFrequencyCyclicSpace_eq_support (b : ℝ) (u : causalFrequencySpace b) :
    (Submodule.span ℂ (Set.range (fun n : ℕ => (causalBoundedChainShift ^ n) u.val))).topologicalClosure =
      causalFrequencySynthesisSpace b
        (Function.support (fun ω : ℝ => causalFrequencyCoefficient b ω u)) := by
  let A := Function.support (fun ω : ℝ => causalFrequencyCoefficient b ω u)
  let C := (Submodule.span ℂ (Set.range (fun n : ℕ =>
    (causalBoundedChainShift ^ n) u.val))).topologicalClosure
  apply le_antisymm
  · apply closed_span_le_of_modes
      (fun n : ℕ => (causalBoundedChainShift ^ n) u.val)
      (causalFrequencySynthesisSpace b A)
      (Submodule.span ℂ (Set.range (fun ω : A => causalBoundedUnitEigenchain b ω.val))).isClosed_topologicalClosure
    intro n
    exact synthesis_power_invariant b A n u.val (causalFrequencySpace_mem_closed_span_support b u)
  · apply closed_span_le_of_modes (fun ω : A => causalBoundedUnitEigenchain b ω.val) C
      (Submodule.span ℂ (Set.range (fun n : ℕ =>
        (causalBoundedChainShift ^ n) u.val))).isClosed_topologicalClosure
    intro ω
    have he : causalFrequencyCoefficient b ω.val u • causalBoundedUnitEigenchain b ω.val =
        (causalFrequencyProjection b ω.val u).val :=
      congrArg (fun w : causalFrequencySpace b => w.val)
        (causalFrequencyCoefficient_smul_mode b ω.val u)
    apply mode_mem_of_scalar C (causalFrequencyCoefficient b ω.val u) ω.property
      (causalBoundedUnitEigenchain b ω.val)
    exact he.symm ▸ projection_mem_cyclic b u ω.val

end RHTower.FokasLenells
