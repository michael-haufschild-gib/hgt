import GaloisForLFunctions.RHTower.MobiusDivisorInheritedPrimeInsertionProducer

/-!
# Distinct-prime realization of finite positive vector mixtures

Square-root-many primes in shrinking proportional windows realize any finite
positive mixture of a continuous vector-valued source. One common scale and
unit prime multiplicities suffice. The quadratic sum of the individual
normalized vectors tends to zero along the same realizations.
-/

noncomputable section
open Finset Set Filter Topology

namespace RHTower.PrimePreparation

private lemma source_windows {ι E : Type*} [DecidableEq ι]
    [NormedAddCommGroup E] (J : Finset ι) (r : ι → ℝ) (H : ℝ → E)
    {b δ : ℝ} (hδ : 0 < δ)
    (hr : ∀ i ∈ J, 0 < r i ∧ r i < b)
    (hH : ∀ i ∈ J, ContinuousAt H (r i)) :
    ∃ η : ℝ, 0 < η ∧
      (∀ i ∈ J, (1 + η) * r i < b ∧
        ∀ x : ℝ, r i ≤ x → x ≤ (1 + η) * r i → ‖H x - H (r i)‖ < δ) ∧
      ∀ i ∈ J, ∀ j ∈ J, r i < r j → (1 + η) * r i < r j := by
  have hnear : ∀ᶠ η : ℝ in 𝓝 0, ∀ i ∈ J,
      (1 + η) * r i < b ∧
        ∀ x : ℝ, r i ≤ x → x ≤ (1 + η) * r i → ‖H x - H (r i)‖ < δ := by
    apply (Filter.eventually_all_finset J).mpr
    intro i hi
    obtain ⟨d, hd, hdist⟩ := (Metric.continuousAt_iff.mp (hH i hi)) δ hδ
    have hb : ∀ᶠ η : ℝ in 𝓝 0, (1 + η) * r i < b :=
      (show ContinuousAt (fun η : ℝ => (1 + η) * r i) 0 by fun_prop).eventually
        (eventually_lt_nhds (by simpa using (hr i hi).2))
    have he : ∀ᶠ η : ℝ in 𝓝 0, η * r i < d :=
      (show ContinuousAt (fun η : ℝ => η * r i) 0 by fun_prop).eventually
        (eventually_lt_nhds (by simpa using hd))
    filter_upwards [hb, he] with η hb he
    refine ⟨hb, fun x hx hx' => ?_⟩
    have hxδ : dist x (r i) < d := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx)]
      nlinarith only [hx', he]
    simpa only [dist_eq_norm] using hdist hxδ
  have hsep : ∀ᶠ η : ℝ in 𝓝 0,
      ∀ i ∈ J, ∀ j ∈ J, r i < r j → (1 + η) * r i < r j := by
    apply (Filter.eventually_all_finset J).mpr
    intro i hi
    apply (Filter.eventually_all_finset J).mpr
    intro j hj
    by_cases hij : r i < r j
    · have he : ∀ᶠ η : ℝ in 𝓝 0, (1 + η) * r i < r j :=
        (show ContinuousAt (fun η : ℝ => (1 + η) * r i) 0 by fun_prop).eventually
          (eventually_lt_nhds (by simpa using hij))
      exact he.mono fun _ h _ => h
    · exact Filter.Eventually.of_forall fun _ h => (hij h).elim
  have hpos : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η := self_mem_nhdsWithin
  have he : ∀ᶠ η : ℝ in 𝓝[>] 0,
      0 < η ∧ (∀ i ∈ J, (1 + η) * r i < b ∧
        ∀ x : ℝ, r i ≤ x → x ≤ (1 + η) * r i → ‖H x - H (r i)‖ < δ) ∧
      ∀ i ∈ J, ∀ j ∈ J, r i < r j → (1 + η) * r i < r j :=
    hpos.and ((hnear.and hsep).filter_mono nhdsWithin_le_nhds)
  exact he.exists

private lemma normalized_ceiling_tendsto {w : ℝ} (hw : 0 ≤ w) :
    Tendsto (fun N : ℕ => (⌈w * Real.sqrt N⌉₊ : ℝ) / Real.sqrt N)
      atTop (𝓝 w) :=
  (tendsto_nat_ceil_mul_div_atTop hw).comp
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

private lemma window_capacity_scaled {r w η : ℝ}
    (hr : 0 < r) (hw : 0 ≤ w) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      ⌈w * Real.sqrt N⌉₊ ≤ (clusterWindow η (r * N)).card := by
  have he := ((tendsto_natCast_atTop_atTop :
      Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).const_mul_atTop hr).eventually
    (cluster_capacity (s := w / Real.sqrt r) hη (by positivity))
  filter_upwards [he] with N hN
  convert hN using 1
  rw [Real.sqrt_mul hr.le]
  congr 1
  field_simp [(Real.sqrt_pos.mpr hr).ne']

private lemma window_above_sqrt {r : ℝ} (hr : 0 < r) :
    ∀ᶠ N : ℕ in atTop, Real.sqrt N < r * N := by
  have he : ∀ᶠ N : ℕ in atTop, 1 / r < Real.sqrt N :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop _
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with N hN hN0
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN0)
  have hh := (div_lt_iff₀ hr).mp hN
  calc
    _ = 1 * Real.sqrt (N : ℝ) := (one_mul _).symm
    _ < (Real.sqrt N * r) * Real.sqrt N := mul_lt_mul_of_pos_right hh hs
    _ = r * (Real.sqrt N) ^ 2 := by ring
    _ = r * N := by rw [Real.sq_sqrt (Nat.cast_nonneg N)]

/-- A finite positive mixture is realized, at every sufficiently large common
integer scale, by distinct actual primes with unit multiplicities. The same
realization has arbitrarily small quadratic diagonal cost. -/
theorem eventually_exists_prime_vector_synthesis {ι E : Type*} [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : Finset ι) (r w : ι → ℝ) (H : ℝ → E) {b ε : ℝ} (hε : 0 < ε)
    (hr : ∀ i ∈ J, 0 < r i ∧ r i < b)
    (hw : ∀ i ∈ J, 0 ≤ w i) (hinj : Set.InjOn r J)
    (hH : ∀ i ∈ J, ContinuousAt H (r i)) :
    ∀ᶠ N : ℕ in atTop, ∃ S : Finset ℕ,
      (∀ p ∈ S, p.Prime ∧ Real.sqrt N < p ∧ (p : ℝ) / N < b) ∧
      ‖(∑ p ∈ S, (Real.sqrt N)⁻¹ • H ((p : ℝ) / N)) -
        ∑ i ∈ J, w i • H (r i)‖ < ε ∧
      (∑ p ∈ S, ‖(Real.sqrt N)⁻¹ • H ((p : ℝ) / N)‖ ^ 2) < ε := by
  classical
  let W : ℝ := ∑ i ∈ J, w i
  have hW : 0 ≤ W := Finset.sum_nonneg hw
  let δ : ℝ := ε / (2 * (W + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨η, hη, hnear, hsep⟩ := source_windows J r H hδ hr hH
  let m (i : ι) (N : ℕ) : ℕ := ⌈w i * Real.sqrt N⌉₊
  let v (N : ℕ) : E := ∑ i ∈ J, ((m i N : ℝ) / Real.sqrt N) • H (r i)
  let C (i : ι) : ℝ := ‖H (r i)‖ + δ
  have hm (i : ι) (hi : i ∈ J) :
      Tendsto (fun N : ℕ => (m i N : ℝ) / Real.sqrt N) atTop (𝓝 (w i)) :=
    normalized_ceiling_tendsto (hw i hi)
  have hmass : Tendsto (fun N : ℕ => ∑ i ∈ J, (m i N : ℝ) / Real.sqrt N)
      atTop (𝓝 W) := tendsto_finsetSum J hm
  have hv : Tendsto v atTop (𝓝 (∑ i ∈ J, w i • H (r i))) :=
    tendsto_finsetSum J (fun i hi => (hm i hi).smul tendsto_const_nhds)
  have hi : Tendsto (fun N : ℕ => (Real.sqrt N)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hdiag : Tendsto (fun N : ℕ =>
      ∑ i ∈ J, ((m i N : ℝ) / Real.sqrt N) * (Real.sqrt N)⁻¹ * C i ^ 2)
      atTop (𝓝 0) := by
    have hh := tendsto_finsetSum J (fun i hi' => ((hm i hi').mul hi).mul_const (C i ^ 2))
    simpa only [mul_zero, zero_mul, sum_const_zero] using hh
  have hcap : ∀ᶠ N : ℕ in atTop, ∀ i ∈ J,
      m i N ≤ (clusterWindow η (r i * N)).card :=
    (Filter.eventually_all_finset J).mpr fun i hi =>
      window_capacity_scaled (hr i hi).1 (hw i hi) hη
  have hsqrt : ∀ᶠ N : ℕ in atTop, ∀ i ∈ J, Real.sqrt N < r i * N :=
    (Filter.eventually_all_finset J).mpr fun i hi => window_above_sqrt (hr i hi).1
  have hvclose : ∀ᶠ N : ℕ in atTop,
      ‖v N - ∑ i ∈ J, w i • H (r i)‖ < ε / 2 := by
    have hh : Tendsto (fun N => ‖v N - ∑ i ∈ J, w i • H (r i)‖)
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [sub_self, norm_zero] using
        (hv.sub (tendsto_const_nhds (x := ∑ i ∈ J, w i • H (r i)))).norm
    exact hh.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < ε / 2))
  filter_upwards [hcap, hsqrt, hmass.eventually (eventually_lt_nhds (lt_add_one W)),
    hvclose, hdiag.eventually (eventually_lt_nhds hε), eventually_gt_atTop (0 : ℕ)]
    with N hcap hsqrt hmass hvclose hdiag hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hroot : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  have hchoose (i : ι) : ∃ A : Finset ℕ, i ∈ J →
      A ⊆ clusterWindow η (r i * N) ∧ A.card = m i N := by
    by_cases hi' : i ∈ J
    · obtain ⟨A, hA, hc⟩ := Finset.exists_subset_card_eq (hcap i hi')
      exact ⟨A, fun _ => ⟨hA, hc⟩⟩
    · exact ⟨∅, fun h => (hi' h).elim⟩
  choose A hA using hchoose
  have hmem (i : ι) (hi' : i ∈ J) (p : ℕ) (hp : p ∈ A i) :
      p.Prime ∧ r i * N < p ∧ (p : ℝ) ≤ (1 + η) * (r i * N) :=
    cluster_members hη.le (mul_nonneg (hr i hi').1.le hN0.le) ((hA i hi').1 hp)
  have hratio (i : ι) (hi' : i ∈ J) (p : ℕ) (hp : p ∈ A i) :
      r i ≤ (p : ℝ) / N ∧ (p : ℝ) / N ≤ (1 + η) * r i := by
    exact ⟨(le_div_iff₀ hN0).mpr (hmem i hi' p hp).2.1.le,
      (div_le_iff₀ hN0).mpr (by simpa only [mul_assoc] using (hmem i hi' p hp).2.2)⟩
  have hdj : Set.PairwiseDisjoint (↑J) A := by
    intro i hi' j hj hij
    apply Finset.disjoint_left.mpr
    intro p hp hp'
    have hne : r i ≠ r j := fun he => hij (hinj hi' hj he)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hh := mul_lt_mul_of_pos_right (hsep i hi' j hj hlt) hN0
      have hpi := (hmem i hi' p hp).2.2
      have hpj := (hmem j hj p hp').2.1
      nlinarith only [hh, hpi, hpj]
    · have hh := mul_lt_mul_of_pos_right (hsep j hj i hi' hgt) hN0
      have hpj := (hmem j hj p hp').2.2
      have hpi := (hmem i hi' p hp).2.1
      nlinarith only [hh, hpj, hpi]
  let S := J.biUnion A
  have hlocal (i : ι) (hi' : i ∈ J) :
      ‖(∑ p ∈ A i, (Real.sqrt N)⁻¹ • H ((p : ℝ) / N)) -
        ((m i N : ℝ) / Real.sqrt N) • H (r i)‖ ≤
      ((m i N : ℝ) / Real.sqrt N) * δ := by
    have hc : (∑ _p ∈ A i, (Real.sqrt N)⁻¹ • H (r i)) =
        ((m i N : ℝ) / Real.sqrt N) • H (r i) := by
      rw [← Finset.sum_smul]
      simp only [sum_const, nsmul_eq_mul, (hA i hi').2, div_eq_mul_inv]
    rw [← hc, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ p ∈ A i, ‖(Real.sqrt N)⁻¹ • (H ((p : ℝ) / N) - H (r i))‖ := by
        simpa only [smul_sub] using norm_sum_le (A i)
          (fun p => (Real.sqrt N)⁻¹ • H ((p : ℝ) / N) - (Real.sqrt N)⁻¹ • H (r i))
      _ ≤ ∑ _p ∈ A i, (Real.sqrt N)⁻¹ * δ := by
        apply Finset.sum_le_sum
        intro p hp
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hroot)]
        exact mul_le_mul_of_nonneg_left
          ((hnear i hi').2 _ (hratio i hi' p hp).1 (hratio i hi' p hp).2).le
          (inv_nonneg.mpr hroot.le)
      _ = _ := by simp [sum_const, (hA i hi').2, div_eq_mul_inv, mul_assoc]
  have htotal : ‖(∑ p ∈ S, (Real.sqrt N)⁻¹ • H ((p : ℝ) / N)) - v N‖ < ε / 2 := by
    rw [show S = J.biUnion A from rfl, Finset.sum_biUnion hdj]
    change ‖(∑ i ∈ J, ∑ p ∈ A i, (Real.sqrt N)⁻¹ • H ((p : ℝ) / N)) -
      (∑ i ∈ J, ((m i N : ℝ) / Real.sqrt N) • H (r i))‖ < ε / 2
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i ∈ J, ‖(∑ p ∈ A i, (Real.sqrt N)⁻¹ • H ((p : ℝ) / N)) -
          ((m i N : ℝ) / Real.sqrt N) • H (r i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ J, ((m i N : ℝ) / Real.sqrt N) * δ := Finset.sum_le_sum hlocal
      _ = (∑ i ∈ J, (m i N : ℝ) / Real.sqrt N) * δ := (Finset.sum_mul ..).symm
      _ < (W + 1) * δ := mul_lt_mul_of_pos_right hmass hδ
      _ = ε / 2 := by
        have hW1 : W + 1 ≠ 0 := by positivity
        dsimp [δ]
        field_simp
  refine ⟨S, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨i, hi', hp⟩ := Finset.mem_biUnion.mp hp
    exact ⟨(hmem i hi' p hp).1, (hsqrt i hi').trans (hmem i hi' p hp).2.1,
      (hratio i hi' p hp).2.trans_lt (hnear i hi').1⟩
  · calc
      _ = ‖((∑ p ∈ S, (Real.sqrt N)⁻¹ • H ((p : ℝ) / N)) - v N) +
          (v N - ∑ i ∈ J, w i • H (r i))‖ := by congr 1; abel
      _ ≤ ‖(∑ p ∈ S, (Real.sqrt N)⁻¹ • H ((p : ℝ) / N)) - v N‖ +
          ‖v N - ∑ i ∈ J, w i • H (r i)‖ := norm_add_le _ _
      _ < ε := (add_lt_add htotal hvclose).trans_eq (by ring)
  · apply lt_of_le_of_lt _ hdiag
    rw [show S = J.biUnion A from rfl, Finset.sum_biUnion hdj]
    apply Finset.sum_le_sum
    intro i hi'
    calc
      _ ≤ ∑ _p ∈ A i, ((Real.sqrt N)⁻¹ * C i) ^ 2 := by
        apply Finset.sum_le_sum
        intro p hp
        apply pow_le_pow_left₀ (norm_nonneg _) _ 2
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hroot)]
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hroot.le)
        have hh := (hnear i hi').2 _ (hratio i hi' p hp).1 (hratio i hi' p hp).2
        exact (norm_le_norm_sub_add _ _).trans
          (by simpa only [C, add_comm] using add_le_add_right hh.le ‖H (r i)‖)
      _ = _ := by simp only [sum_const, nsmul_eq_mul, (hA i hi').2]; dsimp [C]; ring

end RHTower.PrimePreparation
