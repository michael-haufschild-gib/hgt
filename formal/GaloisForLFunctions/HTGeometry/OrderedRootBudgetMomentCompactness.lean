import GaloisForLFunctions.HTGeometry.OrderedPositiveMomentDetermination

/-!
# Bounded ordered root budgets and cofinal moments

Standard positive-sequence compactness and dominated convergence. No arithmetic selector
or scientific novelty is asserted. A bounded root budget has a still-summable subsequential
receiver for every even moment; absent such a receiver, budgets escape to infinity and
each fixed budget already has a finite moment/error obstruction.

Literature parent: Collins--Hasebe--Sakuma (2018), Proposition 2.8, spectral moment
convergence. The application to exact completed Xi moments is in the importing RH leaf.
-/

open Filter Topology Set
open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.HTGeometry

theorem nonneg_antitone_le_budget_div_succ {a : ℕ → ℝ} {C : ℝ}
    (ha : Summable a) (ha0 : ∀ k, 0 ≤ a k) (haa : Antitone a)
    (hC : (∑' k, a k) ≤ C) (k : ℕ) : a k ≤ C / ((k : ℝ) + 1) := by
  have hp : 0 < (k : ℝ) + 1 := by positivity
  apply (le_div_iff₀ hp).2
  calc
    a k * ((k : ℝ) + 1) = ∑ j ∈ Finset.range (k + 1), a k := by simp; ring
    _ ≤ ∑ j ∈ Finset.range (k + 1), a j := by
      exact Finset.sum_le_sum fun j hj => haa (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    _ ≤ ∑' j, a j := ha.sum_le_tsum _ (fun j _ => ha0 j)
    _ ≤ C := hC

theorem tendsto_squarePowerSums_of_bounded_rootBudget
    {a : ℕ → ℕ → ℝ} {b : ℕ → ℝ} {C : ℝ}
    (ha : ∀ N, Summable (a N)) (ha0 : ∀ N k, 0 ≤ a N k)
    (haa : ∀ N, Antitone (a N)) (hC : ∀ N, (∑' k, a N k) ≤ C)
    (hlim : ∀ k, Tendsto (fun N => a N k) atTop (nhds (b k))) (r : ℕ) :
    Tendsto (fun N => ∑' k, (a N k ^ 2) ^ (r + 1)) atTop
      (nhds (∑' k, (b k ^ 2) ^ (r + 1))) := by
  have hC0 : 0 ≤ C := (tsum_nonneg (ha0 0)).trans (hC 0)
  have hsum : Summable (fun k : ℕ => C ^ (2 * r) * (C / ((k : ℝ) + 1)) ^ 2) := by
    have hs := (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num : (1 : ℝ) < 2)
    have hs' : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
      simpa [Real.rpow_two, sq_abs] using hs
    exact (hs'.mul_left (C ^ (2 * r) * C ^ 2)).congr fun k => by
      simp only [div_pow]
      ring
  refine tendsto_tsum_of_dominated_convergence hsum (fun k => ((hlim k).pow 2).pow _) ?_
  apply Eventually.of_forall
  intro N k
  have hk := nonneg_antitone_le_budget_div_succ (ha N) (ha0 N) (haa N) (hC N) k
  have hkC : a N k ≤ C := ((ha N).le_tsum k (fun j _ => ha0 N j)).trans (hC N)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sq_nonneg _) _)]
  calc
    (a N k ^ 2) ^ (r + 1) = a N k ^ (2 * r) * a N k ^ 2 := by rw [pow_succ, pow_mul]
    _ ≤ C ^ (2 * r) * (C / ((k : ℝ) + 1)) ^ 2 :=
      mul_le_mul (pow_le_pow_left₀ (ha0 N k) hkC _) (pow_le_pow_left₀ (ha0 N k) hk 2)
        (sq_nonneg _) (pow_nonneg hC0 _)

/-- A bounded ordered root budget has a subsequential, still summable moment receiver.
This is standard compactness, not an arithmetic positivity theorem. -/
theorem exists_summable_squareMoment_limit_of_bounded_rootBudget
    {a : ℕ → ℕ → ℝ} {M : ℕ → ℝ} {C : ℝ}
    (ha : ∀ N, Summable (a N)) (ha0 : ∀ N k, 0 ≤ a N k)
    (haa : ∀ N, Antitone (a N)) (hC : ∀ N, (∑' k, a N k) ≤ C)
    (hm : ∀ r, Tendsto (fun N => ∑' k, (a N k ^ 2) ^ (r + 1)) atTop (nhds (M r))) :
    ∃ b : ℕ → ℝ, Summable b ∧ (∀ k, 0 ≤ b k) ∧ Antitone b ∧
      (∑' k, b k) ≤ C ∧ ∀ r, (∑' k, (b k ^ 2) ^ (r + 1)) = M r := by
  let K : Set (ℕ → ℝ) := Set.univ.pi (fun _ => Set.Icc (0 : ℝ) C)
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  have hmem : ∀ N, a N ∈ K := by
    intro N k _
    exact ⟨ha0 N k, ((ha N).le_tsum k (fun j _ => ha0 N j)).trans (hC N)⟩
  obtain ⟨b, hbK, φ, hφ, hconv⟩ := hK.tendsto_subseq hmem
  have hcoord : ∀ k, Tendsto (fun N => a (φ N) k) atTop (nhds (b k)) :=
    fun k => ((continuous_apply k).tendsto b).comp hconv
  have hb0 : ∀ k, 0 ≤ b k := fun k => (hbK k (Set.mem_univ k)).1
  have hba : Antitone b := fun i j hij =>
    le_of_tendsto_of_tendsto' (hcoord j) (hcoord i) (fun N => haa (φ N) hij)
  have hfin (n : ℕ) : ∑ k ∈ Finset.range n, b k ≤ C := by
    have hcont : Continuous (fun x : ℕ → ℝ => ∑ k ∈ Finset.range n, x k) :=
      continuous_finsetSum _ fun k _ => continuous_apply k
    exact le_of_tendsto ((hcont.tendsto b).comp hconv) (Eventually.of_forall fun N =>
      ((ha (φ N)).sum_le_tsum _ (fun k _ => ha0 (φ N) k)).trans (hC (φ N)))
  have hb : Summable b := summable_of_sum_range_le hb0 hfin
  refine ⟨b, hb, hb0, hba, hb.tsum_le_of_sum_range_le hfin, fun r => ?_⟩
  exact tendsto_nhds_unique
    (tendsto_squarePowerSums_of_bounded_rootBudget (fun N => ha (φ N))
      (fun N => ha0 (φ N)) (fun N => haa (φ N)) (fun N => hC (φ N)) hcoord r)
    ((hm r).comp hφ.tendsto_atTop)

/-- If the limiting moments have no summable ordered root realization, every sequence
realizing them asymptotically must have root mass tending to infinity. -/
theorem tendsto_rootBudget_atTop_of_no_summable_squareMoment_realization
    {a : ℕ → ℕ → ℝ} {M : ℕ → ℝ}
    (ha : ∀ N, Summable (a N)) (ha0 : ∀ N k, 0 ≤ a N k)
    (haa : ∀ N, Antitone (a N))
    (hM : ¬ ∃ b : ℕ → ℝ, Summable b ∧ (∀ k, 0 ≤ b k) ∧ Antitone b ∧
      ∀ r, (∑' k, (b k ^ 2) ^ (r + 1)) = M r)
    (hm : ∀ r, Tendsto (fun N => ∑' k, (a N k ^ 2) ^ (r + 1)) atTop (nhds (M r))) :
    Tendsto (fun N => ∑' k, a N k) atTop atTop := by
  rw [tendsto_atTop]
  intro C
  by_contra hn
  have hf : ∃ᶠ N in atTop, (∑' k, a N k) < C := by
    rw [frequently_atTop]
    simpa using hn
  obtain ⟨φ, hφ, hbound⟩ := extraction_of_frequently_atTop hf
  obtain ⟨b, hb, hb0, hba, _, hbm⟩ :=
    exists_summable_squareMoment_limit_of_bounded_rootBudget
      (fun N => ha (φ N)) (fun N => ha0 (φ N)) (fun N => haa (φ N))
      (fun N => (hbound N).le) (fun r => (hm r).comp hφ.tendsto_atTop)
  exact hM ⟨b, hb, hb0, hba, hbm⟩

/-- A bounded root budget is separated from a forbidden full moment landing by
finitely many moments and a positive error. The certificate is existential, not numerical. -/
theorem exists_finite_squareMoment_gap_of_no_summable_realization
    {M : ℕ → ℝ}
    (hM : ¬ ∃ b : ℕ → ℝ, Summable b ∧ (∀ k, 0 ≤ b k) ∧ Antitone b ∧
      ∀ r, (∑' k, (b k ^ 2) ^ (r + 1)) = M r) (C : ℝ) :
    ∃ n : ℕ, ∀ a : ℕ → ℝ, Summable a → (∀ k, 0 ≤ a k) → Antitone a →
      (∑' k, a k) ≤ C → ∃ r ≤ n,
        1 / ((n : ℝ) + 1) ≤ |(∑' k, (a k ^ 2) ^ (r + 1)) - M r| := by
  by_contra hn
  push Not at hn
  choose a ha ha0 haa hC hclose using hn
  have hm (r : ℕ) : Tendsto (fun N => ∑' k, (a N k ^ 2) ^ (r + 1)) atTop
      (nhds (M r)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hsmall : ∀ᶠ N : ℕ in atTop, 1 / ((N : ℝ) + 1) < ε :=
      (tendsto_order.1 (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (nhds 0))).2 ε hε
    filter_upwards [hsmall, eventually_ge_atTop r] with N hN hr
    rw [Real.dist_eq]
    exact (hclose N r hr).trans hN
  obtain ⟨b, hb, hb0, hba, _, hbm⟩ :=
    exists_summable_squareMoment_limit_of_bounded_rootBudget ha ha0 haa hC hm
  exact hM ⟨b, hb, hb0, hba, hbm⟩

end GaloisForLFunctions.HTGeometry
