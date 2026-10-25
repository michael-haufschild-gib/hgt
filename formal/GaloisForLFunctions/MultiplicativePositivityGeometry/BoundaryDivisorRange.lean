import GaloisForLFunctions.MultiplicativePositivityGeometry.BoundaryPositivity
import GaloisForLFunctions.ArithmeticPositiveDuality.IntegerPositiveDefiniteFunctionsAreSignCharacters

/-!
# The range of the boundary divisor map

A positive cosine polynomial is `u ↦ Σ_{i<N} c_i cos(λ_i u)` with `c_i ≥ 0` (`IsPosCosPoly`).

* **Range** (`isBoundaryDivisor_iff_tendsto_posCosPoly`). A function `D` is the boundary divisor of
  some family of nonnegative weights iff it is the pointwise limit of a sequence of positive cosine
  polynomials. (⇒) At damping `x = 1/(n+1)` truncate the trace to a finite set carrying all but
  mass `1` of the weights; the error is at most `x`, uniformly in `u`. (⇐) At damping `x` use the
  `⌊1/x⌋`-th polynomial with weights `c_i/x`.
* **Not every positive-definite function is a boundary divisor**
  (`rationalIndicator_not_boundaryDivisor`). The indicator of `ℚ` is positive definite on the discrete
  group `ℝ` (a subgroup indicator). A pointwise limit of continuous functions is, by Baire's theorem,
  within `1/4` of one of them on a nonempty open set, while `1_ℚ` jumps by `1` in every interval.

So on the boundary multiplicative positivity permits exactly the sequential pointwise closure of the
positive cosine polynomials: positive definiteness alone does not suffice, and the obstruction is a
regularity (first Baire class) condition, not a positivity condition.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

/-- `f` is a cosine polynomial with nonnegative coefficients. -/
def IsPosCosPoly (f : ℝ → ℝ) : Prop :=
  ∃ (N : ℕ) (c lam : ℕ → ℝ), (∀ i, 0 ≤ c i) ∧ ∀ u, f u = ∑ i ∈ range N, c i * Real.cos (lam i * u)

theorem IsPosCosPoly.continuous {f : ℝ → ℝ} (hf : IsPosCosPoly f) : Continuous f := by
  obtain ⟨N, c, lam, -, hf⟩ := hf
  rw [show f = fun u => ∑ i ∈ range N, c i * Real.cos (lam i * u) from funext hf]
  exact continuous_finsetSum _ fun i _ =>
    continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))

/-- A finite nonnegative combination of cosines is a positive cosine polynomial. -/
theorem isPosCosPoly_finset_sum {ι : Type*} (s : Finset ι) (c lam : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) : IsPosCosPoly fun u => ∑ i ∈ s, c i * Real.cos (lam i * u) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun _ => 0, fun _ => 0, fun _ => le_rfl, fun u => by simp⟩
  | insert a s ha ih =>
    obtain ⟨N, c', lam', hc', hrep⟩ := ih fun i hi => hc i (Finset.mem_insert_of_mem hi)
    refine ⟨N + 1, fun j => if j = N then c a else c' j, fun j => if j = N then lam a else lam' j,
      fun j => ?_, fun u => ?_⟩
    · beta_reduce
      split_ifs
      · exact hc a (Finset.mem_insert_self a s)
      · exact hc' j
    · beta_reduce
      have hr := hrep u
      beta_reduce at hr
      rw [Finset.sum_insert ha, hr, Finset.sum_range_succ, if_pos rfl, if_pos rfl, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      have : j ≠ N := (Finset.mem_range.mp hj).ne
      rw [if_neg this, if_neg this]

/-- **(⇒)** Every boundary divisor is a pointwise limit of positive cosine polynomials. -/
theorem exists_posCosPoly_of_isBoundaryDivisor {ι : Type*} {lam : ι → ℝ} {w : ℝ → ι → ℝ}
    {D : ℝ → ℝ} (hD : IsBoundaryDivisor lam w D) :
    ∃ P : ℕ → ℝ → ℝ, (∀ n, IsPosCosPoly (P n)) ∧
      ∀ u, Tendsto (fun n => P n u) atTop (𝓝 (D u)) := by
  classical
  set x : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hx : ∀ n, 0 < x n := fun n => by positivity
  -- A finite set carrying all but mass `1` of the weights at damping `x n`.
  have hfin : ∀ n, ∃ s : Finset ι, ∑' i, w (x n) i - ∑ i ∈ s, w (x n) i < 1 := by
    intro n
    have h2 := ((hD.summable (x n) (hx n)).hasSum).eventually
      (Ioo_mem_nhds (show ∑' i, w (x n) i - 1 < ∑' i, w (x n) i by linarith)
        (show ∑' i, w (x n) i < ∑' i, w (x n) i + 1 by linarith))
    obtain ⟨s, hs⟩ := h2.exists
    exact ⟨s, by linarith [hs.1]⟩
  choose s hs using hfin
  refine ⟨fun n u => ∑ i ∈ s n, x n * w (x n) i * Real.cos (lam i * u), fun n =>
    isPosCosPoly_finset_sum _ _ _ fun i _ => mul_nonneg (hx n).le
      (hD.nonneg _ (hx n) i), fun u => ?_⟩
  -- The truncation error is at most `x n`, uniformly in `u`.
  have herr : ∀ n, |x n * cosineTrace (w (x n)) lam u -
      ∑ i ∈ s n, x n * w (x n) i * Real.cos (lam i * u)| ≤ x n := by
    intro n
    have hnn := hD.nonneg _ (hx n)
    have hsum := hD.summable _ (hx n)
    have hcos := summable_cosineTrace_terms hnn hsum lam u
    have hsplit := (hcos.sum_add_tsum_compl (s := s n))
    have hsplit' := (hsum.sum_add_tsum_compl (s := s n))
    have htail : |∑' i : ↥((s n : Set ι)ᶜ), w (x n) i * Real.cos (lam i * u)| ≤
        ∑' i : ↥((s n : Set ι)ᶜ), w (x n) i := by
      have hs1 : Summable fun i : ↥((s n : Set ι)ᶜ) => w (x n) i := hsum.subtype _
      have hs2 : Summable fun i : ↥((s n : Set ι)ᶜ) => w (x n) i * Real.cos (lam i * u) :=
        hcos.subtype _
      rw [abs_le]
      constructor
      · rw [← tsum_neg]
        exact Summable.tsum_le_tsum (fun i => by
          nlinarith [Real.neg_one_le_cos (lam i * u), hnn i]) hs1.neg hs2
      · exact Summable.tsum_le_tsum (fun i => mul_le_of_le_one_right (hnn i)
          (Real.cos_le_one _)) hs2 hs1
    have hfs : ∑ i ∈ s n, x n * w (x n) i * Real.cos (lam i * u) =
        x n * ∑ i ∈ s n, w (x n) i * Real.cos (lam i * u) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    unfold cosineTrace
    rw [hfs, ← hsplit, mul_add, add_sub_cancel_left, abs_mul, abs_of_pos (hx n)]
    have := hs n
    rw [← hsplit'] at this
    have h1 : ∑' i : ↥((s n : Set ι)ᶜ), w (x n) i < 1 := by linarith
    nlinarith [hx n, abs_nonneg (∑' i : ↥((s n : Set ι)ᶜ), w (x n) i * Real.cos (lam i * u))]
  -- `x n → 0⁺`, so the traces converge to `D u`.
  have hxlim : Tendsto x atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall hx⟩
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have htr := (hD.tendsto u).comp hxlim
  have hxz : Tendsto x atTop (𝓝 0) := tendsto_nhdsWithin_iff.mp hxlim |>.1
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  have hdiff : Tendsto (fun n => x n * cosineTrace (w (x n)) lam u - D u) atTop (𝓝 0) := by
    simpa using htr.sub_const (D u)
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by
    simpa using (hdiff.norm.add hxz))
  try simp only [Real.norm_eq_abs]
  show |∑ i ∈ s n, x n * w (x n) i * Real.cos (lam i * u) - D u| ≤ _
  rw [show ∑ i ∈ s n, x n * w (x n) i * Real.cos (lam i * u) - D u =
      (x n * cosineTrace (w (x n)) lam u - D u) -
        (x n * cosineTrace (w (x n)) lam u - ∑ i ∈ s n, x n * w (x n) i * Real.cos (lam i * u))
      by ring]
  exact (abs_sub _ _).trans (by linarith [herr n])

/-- **(⇐)** Every pointwise limit of positive cosine polynomials is a boundary divisor. -/
theorem isBoundaryDivisor_of_tendsto_posCosPoly {P : ℕ → ℝ → ℝ} {D : ℝ → ℝ}
    (hP : ∀ n, IsPosCosPoly (P n)) (hlim : ∀ u, Tendsto (fun n => P n u) atTop (𝓝 (D u))) :
    ∃ (lam : ℕ × ℕ → ℝ) (w : ℝ → ℕ × ℕ → ℝ), IsBoundaryDivisor lam w D := by
  classical
  choose N c lam hc hrep using hP
  set n₀ : ℝ → ℕ := fun x => ⌊1 / x⌋₊
  set w : ℝ → ℕ × ℕ → ℝ := fun x p =>
    if p.1 = n₀ x ∧ p.2 < N p.1 then c p.1 p.2 / x else 0
  have hsupp : ∀ x, ∀ p ∉ ({n₀ x} : Finset ℕ) ×ˢ range (N (n₀ x)), w x p = 0 := by
    intro x p hp
    simp only [w]
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hp (Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr h1,
      Finset.mem_range.mpr (h1 ▸ h2)⟩)
  have htrace : ∀ x, 0 < x → ∀ u, x * cosineTrace (w x) (fun p => lam p.1 p.2) u =
      P (n₀ x) u := by
    intro x hx u
    unfold cosineTrace
    rw [tsum_eq_sum (s := ({n₀ x} : Finset ℕ) ×ˢ range (N (n₀ x))) fun p hp => by
      rw [hsupp x p hp, zero_mul], Finset.sum_product, Finset.sum_singleton, hrep, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [w, if_pos (And.intro rfl (Finset.mem_range.mp hi))]
    field_simp
  refine ⟨fun p => lam p.1 p.2, w, ⟨fun x hx p => ?_, fun x _ => ?_, fun u => ?_⟩⟩
  · simp only [w]
    split_ifs
    · exact div_nonneg (hc _ _) hx.le
    · exact le_rfl
  · exact summable_of_ne_finset_zero (hsupp x)
  · have h1 : Tendsto (fun x : ℝ => 1 / x) (𝓝[>] 0) atTop := by
      simpa only [one_div] using tendsto_inv_nhdsGT_zero (𝕜 := ℝ)
    have hn : Tendsto n₀ (𝓝[>] 0) atTop := tendsto_nat_floor_atTop.comp h1
    refine ((hlim u).comp hn).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (htrace x hx u).symm

/-- **The range of the boundary divisor map.** `D` is a boundary divisor iff it is a pointwise limit
of a sequence of positive cosine polynomials. -/
theorem isBoundaryDivisor_iff_tendsto_posCosPoly (D : ℝ → ℝ) :
    (∃ (ι : Type) (lam : ι → ℝ) (w : ℝ → ι → ℝ), IsBoundaryDivisor lam w D) ↔
      ∃ P : ℕ → ℝ → ℝ, (∀ n, IsPosCosPoly (P n)) ∧
        ∀ u, Tendsto (fun n => P n u) atTop (𝓝 (D u)) :=
  ⟨fun ⟨_, _, _, hD⟩ => exists_posCosPoly_of_isBoundaryDivisor hD,
    fun ⟨_, hP, hlim⟩ => let ⟨lam, w, hw⟩ := isBoundaryDivisor_of_tendsto_posCosPoly hP hlim
      ⟨_, lam, w, hw⟩⟩

/-! ### The indicator of `ℚ` -/

/-- The subgroup `ℚ ⊂ ℝ`. -/
noncomputable def ratSubgroup : AddSubgroup ℝ := (Rat.castHom ℝ).toAddMonoidHom.range

/-- The indicator of `ℚ` in `ℝ`. -/
noncomputable def rationalIndicator (u : ℝ) : ℝ :=
  ArithmeticPositiveDuality.extendByZero ratSubgroup (fun _ => 1) u

/-- `1_ℚ` is positive definite on the discrete group `ℝ`. -/
theorem rationalIndicator_isEvenPosDef : IsEvenPosDef rationalIndicator :=
  ArithmeticPositiveDuality.signCharacter_isEvenPosDef (H := ratSubgroup) (χ := fun _ => 1)
    ⟨fun _ _ => by ring, fun _ => by ring⟩

theorem rationalIndicator_rat (q : ℚ) : rationalIndicator q = 1 := by
  unfold rationalIndicator ArithmeticPositiveDuality.extendByZero
  rw [dif_pos ⟨q, rfl⟩]

theorem rationalIndicator_irrational {v : ℝ} (hv : Irrational v) : rationalIndicator v = 0 := by
  unfold rationalIndicator ArithmeticPositiveDuality.extendByZero
  rw [dif_neg]
  rintro ⟨q, hq⟩
  exact hv ⟨q, hq⟩

/-- **Baire obstruction.** `1_ℚ` is not a pointwise limit of continuous functions. -/
theorem not_tendsto_continuous_rationalIndicator {f : ℕ → ℝ → ℝ} (hf : ∀ n, Continuous (f n))
    (hlim : ∀ u, Tendsto (fun n => f n u) atTop (𝓝 (rationalIndicator u))) : False := by
  set A : ℕ → Set ℝ := fun N => ⋂ n ≥ N, {u | |f n u - f N u| ≤ 1 / 4}
  have hA : ∀ N, IsClosed (A N) := fun N =>
    isClosed_biInter fun n _ => isClosed_le ((hf n).sub (hf N)).abs continuous_const
  have hU : ⋃ N, A N = Set.univ := by
    refine Set.eq_univ_of_forall fun u => Set.mem_iUnion.mpr ?_
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hlim u) (1 / 8) (by norm_num)
    refine ⟨N, Set.mem_iInter₂.mpr fun n hn => ?_⟩
    have h1 := hN n hn
    have h2 := hN N le_rfl
    rw [Real.dist_eq] at h1 h2
    show |f n u - f N u| ≤ 1 / 4
    calc |f n u - f N u| = |(f n u - rationalIndicator u) - (f N u - rationalIndicator u)| := by
          ring_nf
      _ ≤ |f n u - rationalIndicator u| + |f N u - rationalIndicator u| := abs_sub _ _
      _ ≤ 1 / 4 := by linarith
  obtain ⟨N, hint⟩ := nonempty_interior_of_iUnion_of_closed hA hU
  set U := interior (A N)
  -- On `U` the `N`-th function is within `1/4` of `1_ℚ`.
  have hclose : ∀ u ∈ U, |rationalIndicator u - f N u| ≤ 1 / 4 := by
    intro u hu
    have hmem : u ∈ A N := interior_subset hu
    have hev : ∀ᶠ n in atTop, |f n u - f N u| ≤ 1 / 4 :=
      eventually_atTop.mpr ⟨N, fun n hn => Set.mem_iInter₂.mp hmem n hn⟩
    exact le_of_tendsto (((hlim u).sub_const (f N u)).abs) hev
  -- A rational point of `U` and an irrational point nearby.
  obtain ⟨q, hqU⟩ := Rat.denseRange_cast.exists_mem_open isOpen_interior hint
  have hq := hclose q hqU
  rw [rationalIndicator_rat] at hq
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuous_iff.mp (hf N) q (1 / 4) (by norm_num)
  have hopen : IsOpen (U ∩ Metric.ball (q : ℝ) δ) := isOpen_interior.inter Metric.isOpen_ball
  obtain ⟨v, hv, hvU⟩ := dense_irrational.exists_mem_open hopen ⟨q, hqU, Metric.mem_ball_self hδ⟩
  have hv1 := hclose v hvU.1
  rw [rationalIndicator_irrational hv] at hv1
  have hv2 := hδc v hvU.2
  rw [Real.dist_eq] at hv2
  rw [abs_le] at hq hv1
  rw [abs_lt] at hv2
  linarith [hq.1, hv1.1, hv2.1, hq.2, hv1.2, hv2.2]

/-- **`1_ℚ` is positive definite but not a boundary divisor.** -/
theorem rationalIndicator_not_boundaryDivisor :
    IsEvenPosDef rationalIndicator ∧
      ¬ ∃ (ι : Type) (lam : ι → ℝ) (w : ℝ → ι → ℝ), IsBoundaryDivisor lam w rationalIndicator := by
  refine ⟨rationalIndicator_isEvenPosDef, fun h => ?_⟩
  obtain ⟨P, hP, hlim⟩ := (isBoundaryDivisor_iff_tendsto_posCosPoly _).mp h
  exact not_tendsto_continuous_rationalIndicator (fun n => (hP n).continuous) hlim

end GaloisForLFunctions.MultiplicativePositivityGeometry
