import GaloisForLFunctions.ArithmeticProduction.AFaithfulInputNeedNotDecide

/-!
# No finite system of linear laws decides

A linear law pins the limit of `Σ_{n ≤ N} a(n) w(n) − ℓ(N)`.  The Mertens law is one, with `w(n) = 1/n`.  It is precision-faithful and it fails the stabilizer test.  This is not an accident of `w`.

**Theorem** (`exists_stabilizer_outside_sqrtClass`).  Let `L₁, …, L_k` be linear laws whose weights are summable against `n^{−t}` for `¼ ≤ t < ½`.  Then a perturbation `δ ∉ 𝒬`
preserves every one of them, at every weight.

The proof is a dimension count: the `k + 1` power weights `n^{−t_j}` have vectors of pairings in `ℝ^k`, so a nontrivial combination has pairing zero with every `w_i`.  The smallest exponent in the combination dominates its
partial sums, so it lies outside `𝒬`.

Consequently (`finite_linear_system_cannot_decide`) a finite system of such laws that holds at `Λ` cannot imply the count.  A deciding statement of linear type has to pin infinitely many functionals, or functionals such as `w = 1` that do not converge against `n^{−t}`: the count itself is of this second kind.
-/

noncomputable section

open Filter Topology Asymptotics Finset

namespace GaloisForLFunctions.ArithmeticProduction

open ArithmeticOfSquareRootPrecision

/-- A linear law: the limit of `Σ_{n ≤ N} a(n) w(n) − ℓ(N)` is `c`. -/
structure LinearLaw where
  /-- The weight. -/
  w : ℕ → ℝ
  /-- The main term. -/
  ℓ : ℕ → ℝ
  /-- The constant. -/
  c : ℝ

/-- The law holds at the weight `a`. -/
def LinearLaw.Holds (L : LinearLaw) (a : ℕ → ℝ) : Prop :=
  Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, a n * L.w n - L.ℓ N) atTop (𝓝 L.c)

/-- The weight of the law converges against every power below square root. -/
def LinearLaw.Convergent (L : LinearLaw) : Prop :=
  ∀ t : ℝ, 1 / 4 ≤ t → t < 1 / 2 → Summable fun n : ℕ => powerWeight t n * L.w n

/-- Partial sums over `[1, N]` of a sequence vanishing at `0`. -/
private theorem tendsto_sum_Icc {f : ℕ → ℝ} (hf : Summable f) (h0 : f 0 = 0) :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, f n) atTop (𝓝 (∑' n, f n)) := by
  have h := (tendsto_add_atTop_iff_nat 1).mpr hf.hasSum.tendsto_sum_nat
  refine h.congr fun N => ?_
  refine (sum_subset (fun n hn => ?_) fun n hn hnot => ?_).symm
  · obtain ⟨-, h2⟩ := mem_Icc.mp hn
    exact mem_range.mpr (by omega)
  · have hn0 : n = 0 := by
      by_contra hne
      exact hnot (mem_Icc.mpr ⟨Nat.pos_of_ne_zero hne, by have := mem_range.mp hn; omega⟩)
    rw [hn0, h0]

private theorem powerWeight_zero_of_pos {t : ℝ} (ht : 0 < t) : powerWeight t 0 = 0 := by
  unfold powerWeight
  rw [Nat.cast_zero, Real.zero_rpow (by linarith)]

private theorem partialSum_powerWeight_isBigO {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    partialSum (powerWeight t) =O[atTop] fun x : ℝ => x ^ (1 - t) := by
  have hpos : 0 < 1 - t := by linarith
  refine IsBigO.of_bound (1 + 1 / (1 - t)) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have h1 := partialSum_powerWeight_le_rpow ht0 ht1 hx
  have h2 : (1 : ℝ) ≤ x ^ (1 - t) := Real.one_le_rpow hx hpos.le
  rw [Real.norm_of_nonneg (partialSum_nonneg (powerWeight_nonneg t) x),
    Real.norm_of_nonneg (by positivity)]
  have h3 : x ^ (1 - t) / (1 - t) = 1 / (1 - t) * x ^ (1 - t) := by ring
  rw [h3] at h1
  linarith

/-- A nontrivial combination of powers below square root is outside `𝒬`: its smallest exponent dominates. -/
theorem sum_powerWeight_not_mem_sqrtClass {ι : Type*} [Fintype ι] [LinearOrder ι] {t : ι → ℝ} {g : ι → ℝ}
    (ht0 : ∀ j, 0 ≤ t j) (ht1 : ∀ j, t j < 1 / 2) (hmono : ∀ j j', j < j' → t j < t j')
    (hg : ∃ j, g j ≠ 0) :
    (fun n => ∑ j, g j * powerWeight (t j) n) ∉ sqrtClass := by
  classical
  obtain ⟨j₁, hj₁⟩ := hg
  have hne : (univ.filter fun j => g j ≠ 0).Nonempty := ⟨j₁, by simp [hj₁]⟩
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, j₀ = (univ.filter fun j => g j ≠ 0).min' hne := ⟨_, rfl⟩
  have hj₀mem : g j₀ ≠ 0 := by
    have h1 : j₀ ∈ univ.filter fun j => g j ≠ 0 := by
      rw [hj₀]
      exact min'_mem _ hne
    exact (mem_filter.mp h1).2
  have hj₀min : ∀ j, g j ≠ 0 → j₀ ≤ j := by
    intro j hj
    rw [hj₀]
    exact min'_le _ _ (by simp [hj])
  have hpart : ∀ x : ℝ, partialSum (fun n => ∑ j, g j * powerWeight (t j) n) x =
      g j₀ * partialSum (powerWeight (t j₀)) x +
        ∑ j ∈ univ.erase j₀, g j * partialSum (powerWeight (t j)) x := by
    intro x
    rw [show g j₀ * partialSum (powerWeight (t j₀)) x +
        ∑ j ∈ univ.erase j₀, g j * partialSum (powerWeight (t j)) x =
          ∑ j, g j * partialSum (powerWeight (t j)) x from
      Finset.add_sum_erase univ (fun j => g j * partialSum (powerWeight (t j)) x) (mem_univ j₀)]
    unfold partialSum
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum]
  have hR : (fun x : ℝ => ∑ j ∈ univ.erase j₀, g j * partialSum (powerWeight (t j)) x) =o[atTop]
      fun x : ℝ => x ^ (1 - t j₀) := by
    refine IsLittleO.sum fun j hj => ?_
    by_cases hgj : g j = 0
    · simp only [hgj, zero_mul]
      exact isLittleO_zero _ _
    · have hlt : j₀ < j := lt_of_le_of_ne (hj₀min j hgj) (Ne.symm (ne_of_mem_erase hj))
      have h1 := partialSum_powerWeight_isBigO (ht0 j) (by linarith [ht1 j])
      have h2 := rpow_isLittleO_rpow (r := 1 - t j) (s := 1 - t j₀) (by linarith [hmono _ _ hlt])
      exact (h1.trans_isLittleO h2).const_mul_left _
  have hc : 0 < |g j₀| / 4 := by
    have := abs_pos.mpr hj₀mem
    positivity
  refine not_mem_precisionClass_of_lower_bound (sqrtScale_isLittleO_rpow (ht1 j₀)) hc ?_ ?_
  · filter_upwards [hR.def hc, eventually_ge_atTop (1 : ℝ)] with x hx1 hx
    have hx0 : 0 ≤ x ^ (1 - t j₀) := Real.rpow_nonneg (by linarith) _
    rw [Real.norm_of_nonneg hx0] at hx1 ⊢
    rw [hpart]
    have h2 := partialSum_powerWeight_ge (ht0 j₀) hx
    have h3 : |g j₀| * (x ^ (1 - t j₀) / 2) ≤ ‖g j₀ * partialSum (powerWeight (t j₀)) x‖ := by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (h2.trans (le_abs_self _)) (abs_nonneg _)
    have h4 := norm_sub_le_norm_add (g j₀ * partialSum (powerWeight (t j₀)) x)
      (∑ j ∈ univ.erase j₀, g j * partialSum (powerWeight (t j)) x)
    have h5 : |g j₀| * (x ^ (1 - t j₀) / 2) = 2 * (|g j₀| / 4 * x ^ (1 - t j₀)) := by ring
    linarith
  · refine (eventually_gt_atTop (0 : ℝ)).frequently.mono fun x hx => ?_
    exact (Real.rpow_pos_of_pos hx _).ne'

/-- **Every finite system of convergent linear laws has a stabilizer outside `𝒬`.** -/
theorem exists_stabilizer_outside_sqrtClass {k : ℕ} (L : Fin k → LinearLaw) (hL : ∀ i, (L i).Convergent) :
    ∃ δ : ℕ → ℝ, δ ∉ sqrtClass ∧ ∀ a : ℕ → ℝ, (∀ i, (L i).Holds a) → ∀ i, (L i).Holds (a + δ) := by
  obtain ⟨t, ht⟩ : ∃ t : Fin (k + 1) → ℝ,
      t = fun j : Fin (k + 1) => 1 / 4 + ((j : ℕ) : ℝ) / (8 * ((k : ℝ) + 1)) := ⟨_, rfl⟩
  have hk : (0 : ℝ) < 8 * ((k : ℝ) + 1) := by positivity
  have ht0 : ∀ j, 1 / 4 ≤ t j := by
    intro j
    rw [ht]
    have : (0 : ℝ) ≤ ((j : ℕ) : ℝ) / (8 * ((k : ℝ) + 1)) := by positivity
    show (1 : ℝ) / 4 ≤ 1 / 4 + ((j : ℕ) : ℝ) / (8 * ((k : ℝ) + 1))
    linarith
  have ht1 : ∀ j, t j < 1 / 2 := by
    intro j
    rw [ht]
    have hj : ((j : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.mp j.isLt
    have h1 : ((j : ℕ) : ℝ) / (8 * ((k : ℝ) + 1)) ≤ 1 / 8 := by
      rw [div_le_iff₀ hk]
      linarith
    show (1 : ℝ) / 4 + ((j : ℕ) : ℝ) / (8 * ((k : ℝ) + 1)) < 1 / 2
    linarith
  have hmono : ∀ j j' : Fin (k + 1), j < j' → t j < t j' := by
    intro j j' hjj
    rw [ht]
    have h1 : ((j : ℕ) : ℝ) < ((j' : ℕ) : ℝ) := by exact_mod_cast hjj
    show (1 : ℝ) / 4 + ((j : ℕ) : ℝ) / (8 * ((k : ℝ) + 1)) < 1 / 4 + ((j' : ℕ) : ℝ) / (8 * ((k : ℝ) + 1))
    have h2 := div_lt_div_of_pos_right h1 hk
    linarith
  -- the vectors of pairings are dependent
  obtain ⟨τ, hτ⟩ : ∃ τ : Fin (k + 1) → Fin k → ℝ,
      τ = fun j i => ∑' n : ℕ, powerWeight (t j) n * (L i).w n := ⟨_, rfl⟩
  have hdep : ¬ LinearIndependent ℝ τ := by
    intro h
    have h1 := h.fintype_card_le_finrank
    simp at h1
  obtain ⟨g, hg0, hgne⟩ := Fintype.not_linearIndependent_iff.mp hdep
  refine ⟨fun n => ∑ j, g j * powerWeight (t j) n,
    sum_powerWeight_not_mem_sqrtClass (fun j => by linarith [ht0 j]) ht1 hmono hgne, ?_⟩
  intro a ha i
  have hpos : ∀ j, 0 < t j := fun j => by linarith [ht0 j]
  have hzero : Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, (∑ j, g j * powerWeight (t j) n) * (L i).w n)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => ∑ j, g j * ∑ n ∈ Icc 1 N, powerWeight (t j) n * (L i).w n) atTop
        (𝓝 (∑ j, g j * τ j i)) := by
      refine tendsto_finsetSum _ fun j _ => ?_
      have h4 : τ j i = ∑' n : ℕ, powerWeight (t j) n * (L i).w n := by rw [hτ]
      rw [h4]
      refine (tendsto_sum_Icc (hL i _ (ht0 j) (ht1 j)) ?_).const_mul _
      rw [powerWeight_zero_of_pos (hpos j), zero_mul]
    have h2 : ∑ j, g j * τ j i = 0 := by
      have h3 := congrFun hg0 i
      simpa [Finset.sum_apply] using h3
    rw [h2] at h1
    refine h1.congr fun N => ?_
    simp_rw [sum_mul, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun n _ => sum_congr rfl fun j _ => ?_
    ring
  have hadd := (ha i).add hzero
  rw [add_zero] at hadd
  refine hadd.congr fun N => ?_
  simp only [Pi.add_apply, add_mul]
  rw [sum_add_distrib]
  ring

/-- **A finite system of convergent linear laws cannot decide.** -/
theorem finite_linear_system_cannot_decide {k : ℕ} (L : Fin k → LinearLaw) (hL : ∀ i, (L i).Convergent)
    (hΛ : ∀ i, (L i).Holds vonMangoldtWeight) : ¬ ∀ a : ℕ → ℝ, (∀ i, (L i).Holds a) → Count a := by
  intro h
  obtain ⟨δ, hδ, hst⟩ := exists_stabilizer_outside_sqrtClass L hL
  exact hδ ((count_add_iff_mem_sqrtClass (h _ hΛ) δ).mp (h _ (hst _ hΛ)))

/-- The Mertens law as a linear law. -/
def mertensLinearLaw : LinearLaw := ⟨fun n => 1 / (n : ℝ), fun N => Real.log N, -Real.eulerMascheroniConstant⟩

theorem mertensLinearLaw_holds_iff (a : ℕ → ℝ) : mertensLinearLaw.Holds a ↔ MertensLaw a := by
  unfold LinearLaw.Holds MertensLaw mertensLinearLaw harmonicSum
  simp only [mul_one_div]

theorem mertensLinearLaw_convergent : mertensLinearLaw.Convergent := by
  intro t ht _
  have h := Real.summable_nat_rpow_inv.mpr (by linarith : (1 : ℝ) < t + 1)
  refine h.congr fun n => ?_
  unfold mertensLinearLaw powerWeight
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hne : t + 1 ≠ 0 := (by linarith : (0 : ℝ) < t + 1).ne'
    simp [Real.zero_rpow hne]
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  simp only
  rw [Real.rpow_add hpos, Real.rpow_one, mul_inv, Real.rpow_neg hpos.le, one_div]

end GaloisForLFunctions.ArithmeticProduction
