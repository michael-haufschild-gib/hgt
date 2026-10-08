import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Ordinary harmonic convolution and inverse at a fixed endpoint

Finite hyperbola reindexing and dominated convergence preserve an ordinary
harmonic limit when convolved with an absolutely summable harmonic sequence.
A strict harmonic norm bound on the nonconstant part gives an inverse with
absolute harmonic summability at the same endpoint, by a finite-sum contraction.
No conditional series is replaced by unordered summability.
-/

open Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic

/-- Conditional summatory limits survive convolution with an absolutely
summable coefficient sequence, in the exact floor-cutoff ordering. -/
theorem tendsto_sum_mul_floor_div {a S : ℕ → ℂ} {H : ℂ}
    (ha0 : a 0 = 0) (hS0 : S 0 = 0) (ha : Summable (fun n => ‖a n‖))
    (hS : Tendsto S atTop (𝓝 H)) :
    Tendsto (fun N => ∑ m ∈ Finset.Icc 1 N, a m * S (N / m))
      atTop (𝓝 ((∑' m, a m) * H)) := by
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto S hS)
  have hSn (n : ℕ) : ‖S n‖ ≤ B := hB _ (Set.mem_range_self n)
  have ht := tendsto_tsum_of_dominated_convergence (ha.mul_right B)
    (f := fun N m => a m * S (N / m)) (g := fun m => a m * H) (by
      intro m
      by_cases hm : m = 0
      · subst m
        simpa only [ha0, zero_mul] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
      · have hdiv : Tendsto (fun N : ℕ => N / m) atTop atTop := by
          refine tendsto_atTop.2 fun k => Filter.eventually_atTop.2 ⟨k * m, ?_⟩
          intro N hN
          exact (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hm)).2 hN
        exact (hS.comp hdiv).const_mul (a m))
    (Filter.Eventually.of_forall fun N m => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hSn _) (norm_nonneg _))
  rw [tsum_mul_right] at ht
  refine ht.congr fun N => ?_
  apply tsum_eq_sum
  intro m hm
  by_cases hm0 : m = 0
  · simp [hm0, ha0]
  · have hNm : N < m := by
      simp only [Finset.mem_Icc, not_and_or] at hm
      omega
    rw [Nat.div_eq_of_lt hNm, hS0, mul_zero]

/-- Exact hyperbola reindexing, without any infinite rearrangement. -/
theorem sum_divisors_hyperbola {R : Type*} [AddCommMonoid R]
    (G : ℕ × ℕ → R) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal, G p) =
      ∑ m ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 (N / m), G (m, k) := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij (fun p _ => ⟨p.2.1, p.2.2⟩) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hn, hp⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    have hm0 : 0 < p.2.1 := Nat.pos_of_ne_zero (fun h => hn0 (by rw [← hprod, h, zero_mul]))
    have hk0 : 0 < p.2.2 := Nat.pos_of_ne_zero (fun h => hn0 (by rw [← hprod, h, mul_zero]))
    have hprodN : p.2.1 * p.2.2 ≤ N := hprod.trans_le (Finset.mem_Icc.mp hn).2
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hm0,
      le_trans (Nat.le_mul_of_pos_right _ hk0) hprodN⟩,
      Finset.mem_Icc.mpr ⟨hk0, (Nat.le_div_iff_mul_le hm0).2 (by simpa only [Nat.mul_comm] using hprodN)⟩⟩
  · intro p hp q hq he
    have hp' := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hp).2).1
    have hq' := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hq).2).1
    have hfst : p.2.1 = q.2.1 := congrArg Sigma.fst he
    have hsnd : p.2.2 = q.2.2 := by injection he
    have hpq : p.2 = q.2 := Prod.ext hfst hsnd
    have hpq1 : p.1 = q.1 := hp'.symm.trans ((congrArg (fun z : ℕ × ℕ => z.1 * z.2) hpq).trans hq')
    exact Sigma.ext hpq1 (heq_of_eq hpq)
  · intro p hp
    obtain ⟨hm, hk⟩ := Finset.mem_sigma.mp hp
    have hm0 : 0 < p.1 := (Finset.mem_Icc.mp hm).1
    have hk0 : 0 < p.2 := (Finset.mem_Icc.mp hk).1
    refine ⟨⟨p.1 * p.2, (p.1, p.2)⟩, ?_, rfl⟩
    apply Finset.mem_sigma.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hm0 hk0,
      by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hm0).1 (Finset.mem_Icc.mp hk).2⟩,
      Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, Nat.ne_of_gt (Nat.mul_pos hm0 hk0)⟩⟩
  · intro p hp
    rfl

/-- Harmonic partial sums of Dirichlet convolution retain their finite cutoff. -/
theorem harmonic_sum_mul (a b : ArithmeticFunction ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (a * b) n / (n : ℂ)) =
      ∑ m ∈ Finset.Icc 1 N, (a m / (m : ℂ)) *
        (∑ k ∈ Finset.Icc 1 (N / m), b k / (k : ℂ)) := by
  calc
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal,
        (a p.1 / (p.1 : ℂ)) * (b p.2 / (p.2 : ℂ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [ArithmeticFunction.mul_apply, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p hp
      have hn : (n : ℂ) = (p.1 : ℂ) * (p.2 : ℂ) := by
        exact_mod_cast (Nat.mem_divisorsAntidiagonal.mp hp).1.symm
      rw [hn, div_mul_div_comm]
    _ = ∑ m ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 (N / m),
        (a m / (m : ℂ)) * (b k / (k : ℂ)) := sum_divisors_hyperbola _ N
    _ = _ := by simp only [Finset.mul_sum]

/-- One ordinary harmonic limit and one absolute harmonic sum suffice.
No unordered summability hypothesis is imposed on the second factor. -/
theorem tendsto_harmonic_mul_of_summable {a b : ArithmeticFunction ℂ} {H : ℂ}
    (ha : Summable (fun n => ‖a n / (n : ℂ)‖))
    (hb : Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, b n / (n : ℂ)) atTop (𝓝 H)) :
    Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, (a * b) n / (n : ℂ))
      atTop (𝓝 ((∑' n, a n / (n : ℂ)) * H)) := by
  have h := tendsto_sum_mul_floor_div (a := fun n => a n / (n : ℂ))
    (S := fun N => ∑ n ∈ Finset.Icc 1 N, b n / (n : ℂ))
    (by simp) (by simp) ha hb
  exact h.congr fun N => (harmonic_sum_mul a b N).symm

private def harmonicNormMass (a : ArithmeticFunction ℂ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ‖a n / (n : ℂ)‖

private theorem harmonicNormMass_mul_le (a b : ArithmeticFunction ℂ)
    (ha : Summable (fun n => ‖a n / (n : ℂ)‖)) (N : ℕ) :
    harmonicNormMass (a * b) N ≤ (∑' n, ‖a n / (n : ℂ)‖) * harmonicNormMass b N := by
  have hpoint (n : ℕ) : ‖(a * b) n / (n : ℂ)‖ ≤
      ∑ p ∈ n.divisorsAntidiagonal, ‖a p.1 / (p.1 : ℂ)‖ * ‖b p.2 / (p.2 : ℂ)‖ := by
    rw [ArithmeticFunction.mul_apply, Finset.sum_div]
    refine (norm_sum_le _ _).trans_eq ?_
    apply Finset.sum_congr rfl
    intro p hp
    have hn : (n : ℂ) = (p.1 : ℂ) * (p.2 : ℂ) := by
      exact_mod_cast (Nat.mem_divisorsAntidiagonal.mp hp).1.symm
    rw [hn, ← div_mul_div_comm, norm_mul]
  have hb0 : 0 ≤ harmonicNormMass b N := Finset.sum_nonneg fun n _ => norm_nonneg _
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal,
        ‖a p.1 / (p.1 : ℂ)‖ * ‖b p.2 / (p.2 : ℂ)‖ :=
      Finset.sum_le_sum fun n _ => hpoint n
    _ = ∑ m ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 (N / m),
        ‖a m / (m : ℂ)‖ * ‖b k / (k : ℂ)‖ := sum_divisors_hyperbola _ N
    _ ≤ ∑ m ∈ Finset.Icc 1 N, ‖a m / (m : ℂ)‖ * harmonicNormMass b N := by
      apply Finset.sum_le_sum
      intro m hm
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc le_rfl (Nat.div_le_self N m)) (fun _ _ _ => norm_nonneg _)
    _ = (∑ m ∈ Finset.Icc 1 N, ‖a m / (m : ℂ)‖) * harmonicNormMass b N :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (ha.sum_le_tsum _ (fun _ _ => norm_nonneg _)) hb0

/-- A strict harmonic l1 contraction has an inverse at the same endpoint.
This is stronger than merely giving its inverse some finite abscissa. -/
theorem exists_harmonicSummable_inverse (a : ArithmeticFunction ℂ) (ha1 : a 1 = 1)
    (ha : Summable (fun n => ‖(a - 1) n / (n : ℂ)‖))
    (hq : (∑' n, ‖(a - 1) n / (n : ℂ)‖) < 1) :
    ∃ g : ArithmeticFunction ℂ, a * g = 1 ∧ Summable (fun n => ‖g n / (n : ℂ)‖) := by
  let hi : Invertible (a 1) := ⟨1, by rw [ha1, one_mul], by rw [ha1, one_mul]⟩
  let g := ArithmeticFunction.dirichletInverse a hi
  have hag : a * g = 1 := ArithmeticFunction.self_mul_dirichletInverse a hi
  have he : g = 1 - (a - 1) * g := by rw [sub_mul, one_mul, hag]; ring
  let q := ∑' n, ‖(a - 1) n / (n : ℂ)‖
  have hq0 : 0 < 1 - q := sub_pos.mpr hq
  have hone (N : ℕ) : harmonicNormMass (1 : ArithmeticFunction ℂ) N ≤ 1 := by
    have ht (n : ℕ) : ‖(1 : ArithmeticFunction ℂ) n / (n : ℂ)‖ =
        if n = 1 then 1 else 0 := by
      by_cases hn : n = 1
      · subst n; simp
      · simp [hn]
    simp only [harmonicNormMass, ht]
    by_cases hN : 1 ≤ N <;> simp [hN]
  have hpartial (N : ℕ) : harmonicNormMass g N ≤ 1 + q * harmonicNormMass g N := by
    calc
      _ ≤ harmonicNormMass (1 : ArithmeticFunction ℂ) N +
          harmonicNormMass ((a - 1) * g) N := by
        rw [harmonicNormMass, harmonicNormMass, harmonicNormMass, ← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro n hn
        have hgn : g n = (1 : ArithmeticFunction ℂ) n - ((a - 1) * g) n :=
          congrArg (fun f : ArithmeticFunction ℂ => f n) he
        rw [hgn, sub_div]
        exact norm_sub_le _ _
      _ ≤ _ := add_le_add (hone N) (harmonicNormMass_mul_le (a - 1) g ha N)
  have hbound (N : ℕ) : harmonicNormMass g N ≤ 1 / (1 - q) := by
    apply (le_div_iff₀ hq0).2
    nlinarith [hpartial N]
  refine ⟨g, hag, summable_of_sum_range_le (c := 1 / (1 - q)) (fun n => norm_nonneg _) ?_⟩
  intro N
  have hz : ‖g 0 / ((0 : ℕ) : ℂ)‖ = 0 := by simp
  calc
    _ = ∑ n ∈ (Finset.range N).erase 0, ‖g n / (n : ℂ)‖ :=
      (Finset.sum_erase (Finset.range N) hz).symm
    _ ≤ harmonicNormMass g N := by
      apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => norm_nonneg _)
      intro n hn
      obtain ⟨hn0, hn⟩ := Finset.mem_erase.mp hn
      exact Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hn0, (Finset.mem_range.mp hn).le⟩
    _ ≤ _ := hbound N

private theorem tendsto_sum_Icc_of_summable {f : ℕ → ℂ}
    (hf0 : f 0 = 0) (hf : Summable f) :
    Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, f n) atTop (𝓝 (∑' n, f n)) := by
  have h := hf.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  refine h.congr fun N => ?_
  have he : (Finset.range (N + 1)).erase 0 = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]
    omega
  simpa only [Function.comp_apply, he] using (Finset.sum_erase (Finset.range (N + 1)) hf0).symm

/-- Endpoint evaluation preserves an absolutely summable Dirichlet inverse. -/
theorem harmonic_inverse_product {a b : ArithmeticFunction ℂ}
    (hab : a * b = 1)
    (ha : Summable (fun n => ‖a n / (n : ℂ)‖))
    (hb : Summable (fun n => ‖b n / (n : ℂ)‖)) :
    (∑' n, a n / (n : ℂ)) * (∑' n, b n / (n : ℂ)) = 1 := by
  have h := tendsto_harmonic_mul_of_summable ha
    (tendsto_sum_Icc_of_summable (by simp) hb.of_norm)
  apply tendsto_nhds_unique h
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.eventually_atTop.2 ⟨1, fun N hN => hN⟩] with N hN
  have ht (n : ℕ) : (1 : ArithmeticFunction ℂ) n / (n : ℂ) =
      if n = 1 then 1 else 0 := by
    by_cases hn : n = 1
    · subst n; simp
    · simp [hn]
  rw [hab]
  simp only [ht]
  simp [hN]

end RHTower.WeilSingularArithmetic
