import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TowerGridCapacitiesAdd

/-!
# Two towers add exactly on boxes

A two-tower train carries its amplitudes on a support `S` of the exponent lattice inside the box
`[0, M] × [0, N]`.  On the full box the joint first-power charge of the two primes is at most
`(w_p cos(π/(M+2)) + w_q cos(π/(N+2)))` times the mass, attained by the product sine (mechanism 21).
**The capacities add only on the box**: if `S` misses one point of its box, then for all positive
weights the joint charge of every amplitude carried by `S` is bounded by a constant strictly below
that sum (`exists_joint_capacity_lt_of_not_box`); conversely a full box admits no such constant
(`joint_capacity_lt_iff_not_box`).  When `S` contains the two axes, each tower alone still attains
its box capacity on `S` (`axisRowSine_capacity`, `axisColSine_capacity`), so the gap is a
cross-prime saving forced by the support.

**Proof.**  The slack `cap · mass − (w_p · row + w_q · column)` is the positive combination of the
slacks of all rows and all columns, each a single uniform train
(`cos_mul_gridMass_sub_gridRowCharge`, `cos_mul_gridMass_sub_gridColCharge`).  At equality every
row and every column is extremal.  An extremal train is a multiple of the sine, which has no zero on
the train (`uniformTrain_eq_zero_of_capacity_eq`, from the ground-state transform of the chain).
So a zero at a missing point empties its row, every column through that row, and the box
(`grid_eq_zero_of_capacity_eq`).  Compactness of the normalized amplitudes carried by `S` turns the
pointwise strict inequality into a uniform gap.

**Smooth numbers.**  The train on `p^j q^k ≤ e^X` lives on `j log p + k log q ≤ X`.  As soon as
both towers have length at least two, this support misses the corner of its box
(`slanted_corner_not_mem`), so for every `X ≥ max(log p, log q)` and every pair of positive weights
— in particular `Λ(p) p^{−½}, Λ(q) q^{−½}` — the towers do not add (`slanted_capacities_do_not_add`).
-/

open Finset Real Filter Topology

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-! ### The extremal train has no zero -/

/-- **An extremal uniform train with one zero vanishes.**  If
`2 Σ_{k<n} f_k f_{k+1} = 2 cos(π/(n+2)) Σ_{k≤n} f_k²` and `f_m = 0` for some `m ≤ n`, then `f`
vanishes on `[0, n]`: in the sine gauge `f = s g` the energy is `Σ_k s_k s_{k+1} (g_k − g_{k+1})²`,
so `g` is constant, and `s > 0`. -/
theorem uniformTrain_eq_zero_of_capacity_eq (n : ℕ) (f : ℕ → ℝ)
    (heq : 2 * ∑ k ∈ range n, f k * f (k + 1) =
      2 * Real.cos (π / (n + 2)) * ∑ k ∈ range (n + 1), f k ^ 2)
    {m : ℕ} (hm : m ≤ n) (hfm : f m = 0) {k : ℕ} (hk : k ≤ n) : f k = 0 := by
  have hv0 : ∀ i : Fin (n + 1), 0 < trainSine n i := fun i => trainSine_pos n i.isLt
  have hsym := chainCoupling_isSymmetric (n + 1) (fun _ => 2 * Real.cos (π / (n + 2)))
    fun _ => (-1 : ℝ)
  -- the energy of `f` vanishes
  have hE0 : incidenceEnergy (chainCoupling (n + 1) (fun _ => 2 * Real.cos (π / (n + 2)))
      fun _ => (-1 : ℝ)) (fun i : Fin (n + 1) => f i) = 0 := by
    rw [incidenceEnergy_chainCoupling]
    have e1 : ∑ k ∈ range (n + 1), 2 * Real.cos (π / (n + 2)) * f k ^ 2 =
        2 * Real.cos (π / (n + 2)) * ∑ k ∈ range (n + 1), f k ^ 2 := by rw [mul_sum]
    have e2 : ∑ k ∈ range n, -1 * f k * f (k + 1) = -∑ k ∈ range n, f k * f (k + 1) := by
      rw [← sum_neg_distrib]; exact sum_congr rfl fun k _ => by ring
    rw [e1, e2]
    linarith
  -- the ground-state transform in the sine gauge
  have hfg : (fun i : Fin (n + 1) => f i) =
      fun i : Fin (n + 1) => trainSine n i * (f i / trainSine n i) :=
    funext fun i => (mul_div_cancel₀ (f i) (hv0 i).ne').symm
  have hmul := incidenceEnergy_mul_eq hsym (fun i : Fin (n + 1) => trainSine n i)
    (fun i => f i / trainSine n i)
  rw [← hfg, hE0] at hmul
  simp only [couplingAction_uniformTrain_trainSine, mul_zero, zero_mul, sum_const_zero,
    zero_sub] at hmul
  have hnp : ∀ i j : Fin (n + 1),
      chainCoupling (n + 1) (fun _ => 2 * Real.cos (π / (n + 2))) (fun _ => (-1 : ℝ)) i j *
        trainSine n i * trainSine n j * (f i / trainSine n i - f j / trainSine n j) ^ 2 ≤ 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp
    · have hc : chainCoupling (n + 1) (fun _ => 2 * Real.cos (π / (n + 2)))
          (fun _ => (-1 : ℝ)) i j ≤ 0 := by
        have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
        simp only [chainCoupling, chainEntry, hij', if_false]
        split_ifs <;> norm_num
      have hpos : 0 ≤ trainSine n i * trainSine n j *
          (f i / trainSine n i - f j / trainSine n j) ^ 2 :=
        mul_nonneg (mul_pos (hv0 i) (hv0 j)).le (sq_nonneg _)
      calc _ = chainCoupling (n + 1) (fun _ => 2 * Real.cos (π / (n + 2))) (fun _ => (-1 : ℝ))
              i j * (trainSine n i * trainSine n j *
                (f i / trainSine n i - f j / trainSine n j) ^ 2) := by ring
        _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hpos
  have hsum : ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
      chainCoupling (n + 1) (fun _ => 2 * Real.cos (π / (n + 2))) (fun _ => (-1 : ℝ)) i j *
        trainSine n i * trainSine n j * (f i / trainSine n i - f j / trainSine n j) ^ 2 = 0 := by
    linarith
  have hzero : ∀ i j : Fin (n + 1),
      chainCoupling (n + 1) (fun _ => 2 * Real.cos (π / (n + 2))) (fun _ => (-1 : ℝ)) i j *
        trainSine n i * trainSine n j * (f i / trainSine n i - f j / trainSine n j) ^ 2 = 0 := by
    intro i j
    have h1 := (sum_eq_zero_iff_of_nonpos fun i _ => sum_nonpos fun j _ => hnp i j).mp hsum i
      (mem_univ _)
    exact (sum_eq_zero_iff_of_nonpos fun j _ => hnp i j).mp h1 j (mem_univ _)
  -- consecutive ratios agree
  have hstep : ∀ i : ℕ, i < n → f i / trainSine n i = f (i + 1) / trainSine n (i + 1) := by
    intro i hi
    have h := hzero ⟨i, by omega⟩ ⟨i + 1, by omega⟩
    have hce : chainCoupling (n + 1) (fun _ => 2 * Real.cos (π / (n + 2))) (fun _ => (-1 : ℝ))
        ⟨i, by omega⟩ ⟨i + 1, by omega⟩ = -1 := by
      simp [chainCoupling, chainEntry]
    rw [hce] at h
    simp only at h
    have h' : (trainSine n i * trainSine n (i + 1)) *
        (f i / trainSine n i - f (i + 1) / trainSine n (i + 1)) ^ 2 = 0 := by
      rw [← neg_eq_zero, ← h]; ring
    rcases mul_eq_zero.mp h' with h0 | h0
    · exact absurd h0 (mul_pos (trainSine_pos n (by omega)) (trainSine_pos n (by omega))).ne'
    · exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)
  have hconst : ∀ i : ℕ, i ≤ n → f i / trainSine n i = f 0 / trainSine n 0 := by
    intro i hi
    induction i with
    | zero => rfl
    | succ i ih => rw [← hstep i (by omega), ih (by omega)]
  have hg0 : f 0 / trainSine n 0 = 0 := by rw [← hconst m hm, hfm, zero_div]
  have hk' := hconst k hk
  rw [hg0, div_eq_zero_iff] at hk'
  exact hk'.resolve_right (trainSine_pos n (by omega)).ne'

/-! ### Row and column slacks -/

/-- The first-tower slack is the sum of the row slacks. -/
theorem cos_mul_gridMass_sub_gridRowCharge (M N : ℕ) (f : ℕ → ℕ → ℝ) :
    Real.cos (π / (M + 2)) * gridMass M N f - gridRowCharge M N f =
      ∑ k ∈ range (N + 1), (Real.cos (π / (M + 2)) * ∑ j ∈ range (M + 1), f j k ^ 2 -
        ∑ j ∈ range M, f j k * f (j + 1) k) := by
  unfold gridMass gridRowCharge
  rw [sum_comm (s := range (M + 1)), mul_sum, ← sum_sub_distrib]

/-- The second-tower slack is the sum of the column slacks. -/
theorem cos_mul_gridMass_sub_gridColCharge (M N : ℕ) (f : ℕ → ℕ → ℝ) :
    Real.cos (π / (N + 2)) * gridMass M N f - gridColCharge M N f =
      ∑ j ∈ range (M + 1), (Real.cos (π / (N + 2)) * ∑ k ∈ range (N + 1), f j k ^ 2 -
        ∑ k ∈ range N, f j k * f j (k + 1)) := by
  unfold gridMass gridColCharge
  rw [mul_sum, ← sum_sub_distrib]

/-- **At joint equality one zero empties the box.**  For positive weights, an amplitude attaining
the joint capacity of the box with a zero at a box point vanishes on the whole box. -/
theorem grid_eq_zero_of_capacity_eq (M N : ℕ) {wp wq : ℝ} (hp : 0 < wp) (hq : 0 < wq)
    (f : ℕ → ℕ → ℝ)
    (heq : wp * gridRowCharge M N f + wq * gridColCharge M N f =
      (wp * Real.cos (π / (M + 2)) + wq * Real.cos (π / (N + 2))) * gridMass M N f)
    {j₀ k₀ : ℕ} (hj₀ : j₀ ≤ M) (hk₀ : k₀ ≤ N) (hf₀ : f j₀ k₀ = 0) :
    ∀ j ≤ M, ∀ k ≤ N, f j k = 0 := by
  have hrs : ∀ k, 0 ≤ Real.cos (π / (M + 2)) * ∑ j ∈ range (M + 1), f j k ^ 2 -
      ∑ j ∈ range M, f j k * f (j + 1) k := fun k => by
    have := uniformTrain_capacity M (fun j => f j k); linarith
  have hcs : ∀ j, 0 ≤ Real.cos (π / (N + 2)) * ∑ k ∈ range (N + 1), f j k ^ 2 -
      ∑ k ∈ range N, f j k * f j (k + 1) := fun j => by
    have := uniformTrain_capacity N (fun k => f j k); linarith
  have hR := cos_mul_gridMass_sub_gridRowCharge M N f
  have hC := cos_mul_gridMass_sub_gridColCharge M N f
  have hR0 : 0 ≤ Real.cos (π / (M + 2)) * gridMass M N f - gridRowCharge M N f := by
    rw [hR]; exact sum_nonneg fun k _ => hrs k
  have hC0 : 0 ≤ Real.cos (π / (N + 2)) * gridMass M N f - gridColCharge M N f := by
    rw [hC]; exact sum_nonneg fun j _ => hcs j
  have hRz : Real.cos (π / (M + 2)) * gridMass M N f - gridRowCharge M N f = 0 := by
    nlinarith [mul_nonneg hp.le hR0, mul_nonneg hq.le hC0]
  have hCz : Real.cos (π / (N + 2)) * gridMass M N f - gridColCharge M N f = 0 := by
    nlinarith [mul_nonneg hp.le hR0, mul_nonneg hq.le hC0]
  rw [hR] at hRz
  rw [hC] at hCz
  have hrow := (sum_eq_zero_iff_of_nonneg fun k _ => hrs k).mp hRz
  have hcol := (sum_eq_zero_iff_of_nonneg fun j _ => hcs j).mp hCz
  -- the row through the zero vanishes
  have hrow₀ : ∀ j ≤ M, f j k₀ = 0 := fun j hj =>
    uniformTrain_eq_zero_of_capacity_eq M (fun j => f j k₀)
      (by have := hrow k₀ (mem_range.mpr (by omega)); linarith) hj₀ hf₀ hj
  -- and then every column
  intro j hj k hk
  exact uniformTrain_eq_zero_of_capacity_eq N (fun k => f j k)
    (by have := hcol j (mem_range.mpr (by omega)); linarith) hk₀ (hrow₀ j hj) hk

/-! ### Amplitudes carried by a support -/

/-- An amplitude carried by the support `S`. -/
def CarriedBy (S : Set (ℕ × ℕ)) (f : ℕ → ℕ → ℝ) : Prop := ∀ j k, (j, k) ∉ S → f j k = 0

/-- The box quantities depend only on the values in the box. -/
theorem grid_congr {M N : ℕ} {f g : ℕ → ℕ → ℝ} (h : ∀ j ≤ M, ∀ k ≤ N, f j k = g j k) :
    gridMass M N f = gridMass M N g ∧ gridRowCharge M N f = gridRowCharge M N g ∧
      gridColCharge M N f = gridColCharge M N g := by
  refine ⟨?_, ?_, ?_⟩
  · unfold gridMass
    refine sum_congr rfl fun j hj => sum_congr rfl fun k hk => ?_
    rw [h j (by simp at hj; omega) k (by simp at hk; omega)]
  · unfold gridRowCharge
    refine sum_congr rfl fun k hk => sum_congr rfl fun j hj => ?_
    simp only [mem_range] at hj hk
    rw [h j (by omega) k (by omega), h (j + 1) (by omega) k (by omega)]
  · unfold gridColCharge
    refine sum_congr rfl fun j hj => sum_congr rfl fun k hk => ?_
    simp only [mem_range] at hj hk
    rw [h j (by omega) k (by omega), h j (by omega) (k + 1) (by omega)]

theorem eq_zero_of_gridMass_eq_zero {M N : ℕ} {f : ℕ → ℕ → ℝ} (h : gridMass M N f = 0) :
    ∀ j ≤ M, ∀ k ≤ N, f j k = 0 := by
  intro j hj k hk
  have h1 := (sum_eq_zero_iff_of_nonneg fun j _ => sum_nonneg fun k _ => sq_nonneg (f j k)).mp h
    j (mem_range.mpr (by omega))
  have h2 := (sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg (f j k)).mp h1 k
    (mem_range.mpr (by omega))
  exact pow_eq_zero_iff two_ne_zero |>.mp h2

theorem gridMass_nonneg (M N : ℕ) (f : ℕ → ℕ → ℝ) : 0 ≤ gridMass M N f :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _

theorem sq_le_gridMass {M N : ℕ} (f : ℕ → ℕ → ℝ) {j k : ℕ} (hj : j ≤ M) (hk : k ≤ N) :
    f j k ^ 2 ≤ gridMass M N f := by
  unfold gridMass
  refine le_trans ?_ (single_le_sum (fun j _ => sum_nonneg fun k _ => sq_nonneg (f j k))
    (mem_range.mpr (show j < M + 1 by omega)))
  exact single_le_sum (fun k _ => sq_nonneg (f j k)) (mem_range.mpr (show k < N + 1 by omega))

/-- Rescaling divides the box quantities by the square of the scale. -/
theorem grid_div (M N : ℕ) (f : ℕ → ℕ → ℝ) (s : ℝ) :
    gridMass M N (fun j k => f j k / s) = gridMass M N f / s ^ 2 ∧
      gridRowCharge M N (fun j k => f j k / s) = gridRowCharge M N f / s ^ 2 ∧
      gridColCharge M N (fun j k => f j k / s) = gridColCharge M N f / s ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold gridMass
    rw [sum_div]
    exact sum_congr rfl fun j _ => by rw [sum_div]; exact sum_congr rfl fun k _ => by rw [div_pow]
  · unfold gridRowCharge
    rw [sum_div]
    exact sum_congr rfl fun k _ => by
      rw [sum_div]; exact sum_congr rfl fun j _ => by rw [div_mul_div_comm, sq]
  · unfold gridColCharge
    rw [sum_div]
    exact sum_congr rfl fun j _ => by
      rw [sum_div]; exact sum_congr rfl fun k _ => by rw [div_mul_div_comm, sq]

theorem continuous_gridQuantities (M N : ℕ) :
    Continuous (fun f : ℕ → ℕ → ℝ => gridMass M N f) ∧
      Continuous (fun f : ℕ → ℕ → ℝ => gridRowCharge M N f) ∧
      Continuous (fun f : ℕ → ℕ → ℝ => gridColCharge M N f) := by
  have hev : ∀ j k : ℕ, Continuous fun f : ℕ → ℕ → ℝ => f j k := fun j k =>
    (continuous_apply k).comp (continuous_apply j)
  refine ⟨?_, ?_, ?_⟩
  · unfold gridMass
    exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ => (hev j k).pow 2
  · unfold gridRowCharge
    exact continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun j _ =>
      (hev j k).mul (hev (j + 1) k)
  · unfold gridColCharge
    exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ =>
      (hev j k).mul (hev j (k + 1))

/-! ### The capacities add only on boxes -/

/-- **Strict pointwise inequality off the box.** -/
theorem joint_charge_lt_of_not_box {S : Set (ℕ × ℕ)} {M N : ℕ} {j₀ k₀ : ℕ} (hj₀ : j₀ ≤ M)
    (hk₀ : k₀ ≤ N) (hmiss : (j₀, k₀) ∉ S) {wp wq : ℝ} (hp : 0 < wp) (hq : 0 < wq)
    {f : ℕ → ℕ → ℝ} (hf : CarriedBy S f) (hmass : 0 < gridMass M N f) :
    wp * gridRowCharge M N f + wq * gridColCharge M N f <
      (wp * Real.cos (π / (M + 2)) + wq * Real.cos (π / (N + 2))) * gridMass M N f := by
  refine lt_of_le_of_ne (grid_joint_capacity M N hp.le hq.le f) fun heq => ?_
  have hz := grid_eq_zero_of_capacity_eq M N hp hq f heq hj₀ hk₀ (hf j₀ k₀ hmiss)
  have hm0 : gridMass M N f = 0 := by
    unfold gridMass
    exact sum_eq_zero fun j hj => sum_eq_zero fun k hk => by
      rw [hz j (by simp at hj; omega) k (by simp at hk; omega)]; ring
  exact hmass.ne' hm0

/-- **Two towers do not add off the box.**  If the support `S ⊆ [0, M] × [0, N]` misses a point of
the box, then for all positive weights there is `c < w_p cos(π/(M+2)) + w_q cos(π/(N+2))` with
`w_p · row + w_q · column ≤ c · mass` for every amplitude carried by `S`. -/
theorem exists_joint_capacity_lt_of_not_box {S : Set (ℕ × ℕ)} {M N : ℕ}
    (hS : ∀ p ∈ S, p.1 ≤ M ∧ p.2 ≤ N) {j₀ k₀ : ℕ} (hj₀ : j₀ ≤ M) (hk₀ : k₀ ≤ N)
    (hmiss : (j₀, k₀) ∉ S) {wp wq : ℝ} (hp : 0 < wp) (hq : 0 < wq) :
    ∃ c < wp * Real.cos (π / (M + 2)) + wq * Real.cos (π / (N + 2)), ∀ f : ℕ → ℕ → ℝ,
      CarriedBy S f → wp * gridRowCharge M N f + wq * gridColCharge M N f ≤ c * gridMass M N f := by
  obtain ⟨hmc, hrc, hcc⟩ := continuous_gridQuantities M N
  have hjc : Continuous fun f : ℕ → ℕ → ℝ => wp * gridRowCharge M N f + wq * gridColCharge M N f :=
    (continuous_const.mul hrc).add (continuous_const.mul hcc)
  -- the normalized amplitudes carried by `S`
  set K : Set (ℕ → ℕ → ℝ) :=
    (Set.univ.pi fun _ : ℕ => Set.univ.pi fun _ : ℕ => Set.Icc (-1 : ℝ) 1) ∩
      ({f | CarriedBy S f} ∩ {f | gridMass M N f = 1}) with hK
  have hcarried : IsClosed {f : ℕ → ℕ → ℝ | CarriedBy S f} := by
    have e : {f : ℕ → ℕ → ℝ | CarriedBy S f} =
        ⋂ j : ℕ, ⋂ k : ℕ, {f : ℕ → ℕ → ℝ | (j, k) ∉ S → f j k = 0} := by
      ext f; simp [CarriedBy]
    rw [e]
    refine isClosed_iInter fun j => isClosed_iInter fun k => ?_
    by_cases hjk : (j, k) ∈ S
    · simp [hjk]
    · simp only [hjk, not_false_eq_true, forall_const]
      exact isClosed_eq ((continuous_apply k).comp (continuous_apply j)) continuous_const
  have hKc : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc).inter_right
      (hcarried.inter (isClosed_eq hmc continuous_const))
  -- normalization into `K`
  have hnorm : ∀ f : ℕ → ℕ → ℝ, CarriedBy S f → 0 < gridMass M N f →
      (fun j k => f j k / Real.sqrt (gridMass M N f)) ∈ K := by
    intro f hf hm
    have hs : Real.sqrt (gridMass M N f) ^ 2 = gridMass M N f := Real.sq_sqrt hm.le
    obtain ⟨hgm, -, -⟩ := grid_div M N f (Real.sqrt (gridMass M N f))
    have hg1 : gridMass M N (fun j k => f j k / Real.sqrt (gridMass M N f)) = 1 := by
      rw [hgm, hs, div_self hm.ne']
    refine ⟨Set.mem_univ_pi.mpr fun j => Set.mem_univ_pi.mpr fun k => ?_,
      fun j k hjk => by simp only [hf j k hjk, zero_div], hg1⟩
    by_cases hjk : (j, k) ∈ S
    · obtain ⟨hj, hk⟩ := hS _ hjk
      have hsq := sq_le_gridMass (fun j k => f j k / Real.sqrt (gridMass M N f)) hj hk
      rw [hg1] at hsq
      exact ⟨by nlinarith, by nlinarith⟩
    · simp only [hf j k hjk, zero_div]
      exact ⟨by norm_num, by norm_num⟩
  -- an amplitude carried by `S` with zero mass carries no charge
  have hzero : ∀ f : ℕ → ℕ → ℝ, gridMass M N f = 0 →
      wp * gridRowCharge M N f + wq * gridColCharge M N f = 0 := by
    intro f hm
    obtain ⟨-, hr, hc⟩ := grid_congr (g := fun _ _ => (0 : ℝ)) (eq_zero_of_gridMass_eq_zero hm)
    rw [hr, hc]
    simp [gridRowCharge, gridColCharge]
  -- homogeneity
  have hscale : ∀ f : ℕ → ℕ → ℝ, 0 < gridMass M N f →
      wp * gridRowCharge M N f + wq * gridColCharge M N f =
        (wp * gridRowCharge M N (fun j k => f j k / Real.sqrt (gridMass M N f)) +
          wq * gridColCharge M N (fun j k => f j k / Real.sqrt (gridMass M N f))) *
            gridMass M N f := by
    intro f hm
    obtain ⟨-, hr, hc⟩ := grid_div M N f (Real.sqrt (gridMass M N f))
    rw [hr, hc, Real.sq_sqrt hm.le]
    field_simp
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · -- no amplitude carried by `S` has positive mass
    refine ⟨wp * Real.cos (π / (M + 2)) + wq * Real.cos (π / (N + 2)) - 1, by linarith,
      fun f hf => ?_⟩
    have hm0 : gridMass M N f = 0 := by
      rcases (gridMass_nonneg M N f).lt_or_eq with hm | hm
      · exact absurd (hnorm f hf hm) (by rw [hKe]; exact Set.notMem_empty _)
      · exact hm.symm
    rw [hzero f hm0, hm0, mul_zero]
  · obtain ⟨f₀, hf₀K, hmax⟩ := hKc.exists_isMaxOn hKne hjc.continuousOn
    obtain ⟨-, hf₀S, hf₀m⟩ := hf₀K
    have hf₀m' : gridMass M N f₀ = 1 := hf₀m
    refine ⟨wp * gridRowCharge M N f₀ + wq * gridColCharge M N f₀, ?_, fun f hf => ?_⟩
    · have := joint_charge_lt_of_not_box hj₀ hk₀ hmiss hp hq hf₀S (by rw [hf₀m']; norm_num)
      rwa [hf₀m', mul_one] at this
    · rcases (gridMass_nonneg M N f).lt_or_eq with hm | hm
      · rw [hscale f hm]
        exact mul_le_mul_of_nonneg_right (hmax (hnorm f hf hm)) hm.le
      · rw [hzero f hm.symm, ← hm, mul_zero]

/-- The product sine truncated to the box. -/
def boxSine (M N : ℕ) (j k : ℕ) : ℝ := if j ≤ M ∧ k ≤ N then productSine M N j k else 0

/-- **The capacities add exactly on boxes.**  For `S ⊆ [0, M] × [0, N]` and positive weights, a
constant below the sum of the box capacities bounds the joint charge of all amplitudes carried by
`S` iff `S` misses a point of the box. -/
theorem joint_capacity_lt_iff_not_box {S : Set (ℕ × ℕ)} {M N : ℕ}
    (hS : ∀ p ∈ S, p.1 ≤ M ∧ p.2 ≤ N) {wp wq : ℝ} (hp : 0 < wp) (hq : 0 < wq) :
    (∃ c < wp * Real.cos (π / (M + 2)) + wq * Real.cos (π / (N + 2)), ∀ f : ℕ → ℕ → ℝ,
      CarriedBy S f → wp * gridRowCharge M N f + wq * gridColCharge M N f ≤ c * gridMass M N f) ↔
      ∃ j ≤ M, ∃ k ≤ N, (j, k) ∉ S := by
  constructor
  · rintro ⟨c, hc, hle⟩
    by_contra hfull
    push Not at hfull
    have hcar : CarriedBy S (boxSine M N) := fun j k hjk => by
      unfold boxSine
      split_ifs with h
      · exact absurd (hfull j h.1 k h.2) hjk
      · rfl
    obtain ⟨hm, hr, hcl⟩ := grid_congr (M := M) (N := N) (f := boxSine M N)
      (g := productSine M N) fun j hj k hk => by simp [boxSine, hj, hk]
    have h1 := hle _ hcar
    rw [hm, hr, hcl, grid_joint_capacity_attained] at h1
    exact absurd h1 (not_le.mpr (mul_lt_mul_of_pos_right hc (gridMass_productSine_pos M N)))
  · rintro ⟨j, hj, k, hk, hmiss⟩
    exact exists_joint_capacity_lt_of_not_box hS hj hk hmiss hp hq

/-! ### Each tower alone keeps its box capacity -/

/-- The sine train on the first axis. -/
def axisRowSine (M : ℕ) (j k : ℕ) : ℝ := if k = 0 ∧ j ≤ M then trainSine M j else 0

/-- The sine train on the second axis. -/
def axisColSine (N : ℕ) (j k : ℕ) : ℝ := if j = 0 ∧ k ≤ N then trainSine N k else 0

/-- **The first tower attains its box capacity on the first axis**, carrying no second-tower
charge. -/
theorem axisRowSine_capacity (M N : ℕ) :
    gridRowCharge M N (axisRowSine M) = Real.cos (π / (M + 2)) * gridMass M N (axisRowSine M) ∧
      gridColCharge M N (axisRowSine M) = 0 ∧ 0 < gridMass M N (axisRowSine M) := by
  have hmassk : ∀ k, ∑ j ∈ range (M + 1), axisRowSine M j k ^ 2 =
      if k = 0 then ∑ j ∈ range (M + 1), trainSine M j ^ 2 else 0 := by
    intro k
    split_ifs with hk
    · subst hk
      exact sum_congr rfl fun j hj => by
        simp [axisRowSine, show j ≤ M by simp at hj; omega]
    · exact sum_eq_zero fun j _ => by simp [axisRowSine, hk]
  have hrowk : ∀ k, ∑ j ∈ range M, axisRowSine M j k * axisRowSine M (j + 1) k =
      if k = 0 then ∑ j ∈ range M, trainSine M j * trainSine M (j + 1) else 0 := by
    intro k
    split_ifs with hk
    · subst hk
      exact sum_congr rfl fun j hj => by
        simp [axisRowSine, show j ≤ M by simp at hj; omega, show j + 1 ≤ M by simp at hj; omega]
    · exact sum_eq_zero fun j _ => by simp [axisRowSine, hk]
  have hmass : gridMass M N (axisRowSine M) = ∑ j ∈ range (M + 1), trainSine M j ^ 2 := by
    unfold gridMass
    rw [sum_comm, sum_congr rfl fun k _ => hmassk k, sum_ite_eq' (range (N + 1)) 0]
    simp
  have hrow : gridRowCharge M N (axisRowSine M) =
      ∑ j ∈ range M, trainSine M j * trainSine M (j + 1) := by
    unfold gridRowCharge
    rw [sum_congr rfl fun k _ => hrowk k, sum_ite_eq' (range (N + 1)) 0]
    simp
  have hatt := uniformTrain_capacity_attained M
  refine ⟨by rw [hrow, hmass]; linarith, ?_, ?_⟩
  · unfold gridColCharge
    exact sum_eq_zero fun j _ => sum_eq_zero fun k _ => by simp [axisRowSine]
  · rw [hmass]
    exact sum_pos (fun j hj => pow_pos (trainSine_pos M (mem_range.mp hj)) 2) ⟨0, by simp⟩

/-- **The second tower attains its box capacity on the second axis**, carrying no first-tower
charge. -/
theorem axisColSine_capacity (M N : ℕ) :
    gridColCharge M N (axisColSine N) = Real.cos (π / (N + 2)) * gridMass M N (axisColSine N) ∧
      gridRowCharge M N (axisColSine N) = 0 ∧ 0 < gridMass M N (axisColSine N) := by
  have hmassj : ∀ j, ∑ k ∈ range (N + 1), axisColSine N j k ^ 2 =
      if j = 0 then ∑ k ∈ range (N + 1), trainSine N k ^ 2 else 0 := by
    intro j
    split_ifs with hj
    · subst hj
      exact sum_congr rfl fun k hk => by
        simp [axisColSine, show k ≤ N by simp at hk; omega]
    · exact sum_eq_zero fun k _ => by simp [axisColSine, hj]
  have hcolj : ∀ j, ∑ k ∈ range N, axisColSine N j k * axisColSine N j (k + 1) =
      if j = 0 then ∑ k ∈ range N, trainSine N k * trainSine N (k + 1) else 0 := by
    intro j
    split_ifs with hj
    · subst hj
      exact sum_congr rfl fun k hk => by
        simp [axisColSine, show k ≤ N by simp at hk; omega, show k + 1 ≤ N by simp at hk; omega]
    · exact sum_eq_zero fun k _ => by simp [axisColSine, hj]
  have hmass : gridMass M N (axisColSine N) = ∑ k ∈ range (N + 1), trainSine N k ^ 2 := by
    unfold gridMass
    rw [sum_congr rfl fun j _ => hmassj j, sum_ite_eq' (range (M + 1)) 0]
    simp
  have hcol : gridColCharge M N (axisColSine N) =
      ∑ k ∈ range N, trainSine N k * trainSine N (k + 1) := by
    unfold gridColCharge
    rw [sum_congr rfl fun j _ => hcolj j, sum_ite_eq' (range (M + 1)) 0]
    simp
  have hatt := uniformTrain_capacity_attained N
  refine ⟨by rw [hcol, hmass]; linarith, ?_, ?_⟩
  · unfold gridRowCharge
    exact sum_eq_zero fun k _ => sum_eq_zero fun j _ => by simp [axisColSine]
  · rw [hmass]
    exact sum_pos (fun k hk => pow_pos (trainSine_pos N (mem_range.mp hk)) 2) ⟨0, by simp⟩

/-! ### Smooth numbers -/

/-- The exponent support `j a + k b ≤ X` of the smooth numbers `p^j q^k ≤ e^X`, `a = log p`,
`b = log q`. -/
def slantedSupport (a b X : ℝ) : Set (ℕ × ℕ) := {p | (p.1 : ℝ) * a + p.2 * b ≤ X}

theorem slantedSupport_subset_box {a b X : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∀ p ∈ slantedSupport a b X, p.1 ≤ ⌊X / a⌋₊ ∧ p.2 ≤ ⌊X / b⌋₊ := by
  rintro ⟨j, k⟩ hp
  simp only [slantedSupport, Set.mem_setOf_eq] at hp
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine ⟨Nat.le_floor ?_, Nat.le_floor ?_⟩
  · rw [le_div_iff₀ ha]; nlinarith
  · rw [le_div_iff₀ hb]; nlinarith

/-- **The slanted support misses the corner of its box** once both towers have length `≥ 2`. -/
theorem slanted_corner_not_mem {a b X : ℝ} (ha : 0 < a) (hb : 0 < b) (hM : 1 ≤ ⌊X / a⌋₊)
    (hN : 1 ≤ ⌊X / b⌋₊) : (⌊X / a⌋₊, ⌊X / b⌋₊) ∉ slantedSupport a b X := by
  simp only [slantedSupport, Set.mem_setOf_eq, not_le]
  have h1 : X < ((⌊X / a⌋₊ : ℝ) + 1) * a := by
    have := Nat.lt_floor_add_one (X / a)
    rwa [div_lt_iff₀ ha] at this
  have h2 : X < ((⌊X / b⌋₊ : ℝ) + 1) * b := by
    have := Nat.lt_floor_add_one (X / b)
    rwa [div_lt_iff₀ hb] at this
  have hM' : (1 : ℝ) ≤ ⌊X / a⌋₊ := by exact_mod_cast hM
  have hN' : (1 : ℝ) ≤ ⌊X / b⌋₊ := by exact_mod_cast hN
  -- either `X ≥ a + b` and the corner lies beyond `2X − a − b ≥ X`, or `(1, 1)` already does
  rcases le_or_gt (a + b) X with hab | hab
  · nlinarith
  · nlinarith

/-- **On the smooth numbers two towers never add.**  For `a, b > 0` (the logarithms of two primes)
and `X` with both towers of length `≥ 2`, every pair of positive weights — in particular
`Λ(p) p^{−½}, Λ(q) q^{−½}` — leaves a constant strictly below the sum of the single capacities that
bounds the joint charge of every amplitude carried by `j a + k b ≤ X`.  Each single capacity is
attained on the support (`axisRowSine_capacity`, `axisColSine_capacity`). -/
theorem slanted_capacities_do_not_add {a b X : ℝ} (ha : 0 < a) (hb : 0 < b) (hM : 1 ≤ ⌊X / a⌋₊)
    (hN : 1 ≤ ⌊X / b⌋₊) {wp wq : ℝ} (hp : 0 < wp) (hq : 0 < wq) :
    ∃ c < wp * Real.cos (π / (⌊X / a⌋₊ + 2)) + wq * Real.cos (π / (⌊X / b⌋₊ + 2)),
      ∀ f : ℕ → ℕ → ℝ, CarriedBy (slantedSupport a b X) f →
        wp * gridRowCharge ⌊X / a⌋₊ ⌊X / b⌋₊ f + wq * gridColCharge ⌊X / a⌋₊ ⌊X / b⌋₊ f ≤
          c * gridMass ⌊X / a⌋₊ ⌊X / b⌋₊ f :=
  exists_joint_capacity_lt_of_not_box (slantedSupport_subset_box ha hb) le_rfl le_rfl
    (slanted_corner_not_mem ha hb hM hN) hp hq

/-- The axes lie in the slanted support: each tower attains its capacity there. -/
theorem axes_carriedBy_slantedSupport {a b X : ℝ} (ha : 0 < a) (hb : 0 < b) (hM : 1 ≤ ⌊X / a⌋₊)
    (hN : 1 ≤ ⌊X / b⌋₊) :
    CarriedBy (slantedSupport a b X) (axisRowSine ⌊X / a⌋₊) ∧
      CarriedBy (slantedSupport a b X) (axisColSine ⌊X / b⌋₊) := by
  have hXa : 0 ≤ X / a := by linarith [Nat.floor_pos.mp (show 0 < ⌊X / a⌋₊ by omega)]
  have hXb : 0 ≤ X / b := by linarith [Nat.floor_pos.mp (show 0 < ⌊X / b⌋₊ by omega)]
  constructor
  · intro j k hjk
    unfold axisRowSine
    split_ifs with h
    · refine absurd ?_ hjk
      have hj : (j : ℝ) ≤ X / a := (Nat.cast_le.mpr h.2).trans (Nat.floor_le hXa)
      show (j : ℝ) * a + (k : ℝ) * b ≤ X
      rw [h.1, Nat.cast_zero, zero_mul, add_zero]
      rwa [le_div_iff₀ ha] at hj
    · rfl
  · intro j k hjk
    unfold axisColSine
    split_ifs with h
    · refine absurd ?_ hjk
      have hk : (k : ℝ) ≤ X / b := (Nat.cast_le.mpr h.2).trans (Nat.floor_le hXb)
      show (j : ℝ) * a + (k : ℝ) * b ≤ X
      rw [h.1, Nat.cast_zero, zero_mul, zero_add]
      rwa [le_div_iff₀ hb] at hk
    · rfl

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
