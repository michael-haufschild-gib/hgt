import GaloisForLFunctions.HTGeometry.ReciprocalWorkFusionRigidity
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.PSeries
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Complexity-weighted reciprocal work: global fusion and the sharp compactness threshold

For weights `a_j ≥ 1` the extended work of a real sequence is
`𝒲_a(x) = ∑_j a_j² ω(x_j) ∈ [0, ∞]`, with `ω` the reciprocal work.

* **Theorem 3.1, `(RFT.10)`–`(RFT.13)`**: the finite-work sequences form an additive subgroup
  closed under reversal, and `𝒲(x + y) + 𝒲(x - y) = ℐ(x, y) + 2𝒲(x) + 2𝒲(y)` with
  `ℐ(x, y) ≤ 𝒲(x)𝒲(y)`; every term is finite.
* **`(RFT.15)`**: `∑ x_j² ≤ ∑ a_j² x_j² ≤ 𝒲(x)`.
* **Theorem 5.1, `(RFT.22)`–`(RFT.27)`**: the sublevels `{x ∈ ℓ¹ : 𝒲(x) ≤ C}` are all compact,
  iff one positive sublevel is bounded, iff `∑ a_j⁻² < ∞`; then `∑_{j ≥ N} |x_j| ≤
  𝒲(x)^{1/2} (∑_{j ≥ N} a_j⁻²)^{1/2}`.  Necessity uses the finite-support sequences
  `x_j = δ a_j⁻² S_N^{-1/2}` of bounded work and `ℓ¹` norm `δ S_N^{1/2} → ∞`.
* **Theorem 6.1, `(RFT.28)`**: for `d > 1`, `sup_n 𝒲(dⁿx) < ∞` iff `x = 0`.
-/

open scoped ENNReal
open Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry.ReciprocalFusion

variable (a : ℕ → ℝ)

/-- The summand `a_j² ω(x_j)` of the work. -/
def workTerm (x : ℕ → ℝ) (j : ℕ) : ℝ := a j ^ 2 * reciprocalWork (x j)

theorem workTerm_nonneg (x : ℕ → ℝ) (j : ℕ) : 0 ≤ workTerm a x j :=
  mul_nonneg (sq_nonneg _) (reciprocalWork_nonneg _)

/-- **`(RFT.9)`** the extended work `𝒲_a(x) = ∑_j a_j² ω(x_j) ∈ [0, ∞]`. -/
def extendedWork (x : ℕ → ℝ) : ℝ≥0∞ := ∑' j, ENNReal.ofReal (workTerm a x j)

/-- The real work of a finite-work sequence. -/
def work (x : ℕ → ℝ) : ℝ := ∑' j, workTerm a x j

/-- **`(RFT.11)`** the fusion interaction `ℐ_a(x, y) = ∑_j a_j² ω(x_j) ω(y_j)`. -/
def interactionTerm (x y : ℕ → ℝ) (j : ℕ) : ℝ :=
  a j ^ 2 * reciprocalWork (x j) * reciprocalWork (y j)

/-- **`(RFT.11)`** the fusion interaction. -/
def interaction (x y : ℕ → ℝ) : ℝ := ∑' j, interactionTerm a x y j

theorem extendedWork_ne_top_iff (x : ℕ → ℝ) :
    extendedWork a x ≠ ⊤ ↔ Summable (workTerm a x) := by
  have h : ∀ j, ENNReal.ofReal (workTerm a x j) = ((workTerm a x j).toNNReal : ℝ≥0∞) :=
    fun j => rfl
  rw [extendedWork, tsum_congr h, ENNReal.tsum_coe_ne_top_iff_summable]
  constructor
  · intro hs
    refine (NNReal.summable_coe.2 hs).congr fun j => ?_
    exact Real.coe_toNNReal _ (workTerm_nonneg a x j)
  · exact fun hs => hs.toNNReal

theorem extendedWork_lt_top_iff (x : ℕ → ℝ) :
    extendedWork a x < ⊤ ↔ Summable (workTerm a x) := by
  rw [lt_top_iff_ne_top, extendedWork_ne_top_iff]

theorem extendedWork_eq_ofReal {x : ℕ → ℝ} (hx : Summable (workTerm a x)) :
    extendedWork a x = ENNReal.ofReal (work a x) :=
  (ENNReal.ofReal_tsum_of_nonneg (workTerm_nonneg a x) hx).symm

theorem work_nonneg (x : ℕ → ℝ) : 0 ≤ work a x := tsum_nonneg (workTerm_nonneg a x)

/-! ### Theorem 3.1: global fusion and group closure -/

section Fusion

variable {a}

theorem reciprocalWork_le_workTerm (ha : ∀ j, 1 ≤ a j) (x : ℕ → ℝ) (j : ℕ) :
    reciprocalWork (x j) ≤ workTerm a x j := by
  have h1 : 1 ≤ a j ^ 2 := one_le_pow₀ (ha j)
  have h0 := reciprocalWork_nonneg (x j)
  unfold workTerm
  nlinarith

theorem workTerm_le_work {x : ℕ → ℝ} (hx : Summable (workTerm a x)) (j : ℕ) :
    workTerm a x j ≤ work a x :=
  hx.le_tsum j fun k _ => workTerm_nonneg a x k

/-- **Theorem 3.1, `(RFT.12)`–`(RFT.13)`**: global fusion of two finite-work sequences. -/
theorem global_fusion (ha : ∀ j, 1 ≤ a j) {x y : ℕ → ℝ} (hx : Summable (workTerm a x))
    (hy : Summable (workTerm a y)) :
    Summable (interactionTerm a x y) ∧ Summable (workTerm a (x + y)) ∧
      Summable (workTerm a (x - y)) ∧
      work a (x + y) + work a (x - y) = interaction a x y + 2 * work a x + 2 * work a y ∧
      interaction a x y ≤ work a x * work a y := by
  have hI : ∀ j, interactionTerm a x y j ≤ workTerm a x j * work a y := fun j => by
    have h := (reciprocalWork_le_workTerm ha y j).trans (workTerm_le_work hy j)
    have hx0 := workTerm_nonneg a x j
    unfold interactionTerm
    unfold workTerm at hx0 ⊢
    exact mul_le_mul_of_nonneg_left h hx0
  have hI0 : ∀ j, 0 ≤ interactionTerm a x y j := fun j =>
    mul_nonneg (mul_nonneg (sq_nonneg _) (reciprocalWork_nonneg _)) (reciprocalWork_nonneg _)
  have hIs : Summable (interactionTerm a x y) :=
    Summable.of_nonneg_of_le hI0 hI (hx.mul_right _)
  have hterm : ∀ j, workTerm a (x + y) j + workTerm a (x - y) j =
      interactionTerm a x y j + 2 * workTerm a x j + 2 * workTerm a y j := fun j => by
    simp only [workTerm, interactionTerm, Pi.add_apply, Pi.sub_apply]
    have := reciprocalWork_fusion (x j) (y j)
    linear_combination a j ^ 2 * this
  have hR : Summable fun j => interactionTerm a x y j + 2 * workTerm a x j + 2 * workTerm a y j :=
    (hIs.add (hx.mul_left 2)).add (hy.mul_left 2)
  have hplus : Summable (workTerm a (x + y)) :=
    Summable.of_nonneg_of_le (workTerm_nonneg a _) (fun j => by
      have := workTerm_nonneg a (x - y) j; linarith [hterm j]) hR
  have hminus : Summable (workTerm a (x - y)) :=
    Summable.of_nonneg_of_le (workTerm_nonneg a _) (fun j => by
      have := workTerm_nonneg a (x + y) j; linarith [hterm j]) hR
  refine ⟨hIs, hplus, hminus, ?_, ?_⟩
  · rw [work, work, ← hplus.tsum_add hminus, tsum_congr hterm, (hIs.add (hx.mul_left 2)).tsum_add
      (hy.mul_left 2), hIs.tsum_add (hx.mul_left 2), tsum_mul_left, tsum_mul_left]
    rfl
  · calc interaction a x y ≤ ∑' j, workTerm a x j * work a y :=
          hIs.tsum_le_tsum hI (hx.mul_right _)
      _ = work a x * work a y := by rw [tsum_mul_right]; rfl

theorem workTerm_neg (x : ℕ → ℝ) : workTerm a (-x) = workTerm a x := by
  funext j
  simp [workTerm, reciprocalWork_neg]

/-- **Theorem 3.1, `(RFT.10)`**: the finite-work sequences form an additive group, closed under
reversal `x ↦ -x`. -/
def admissible (ha : ∀ j, 1 ≤ a j) : AddSubgroup (ℕ → ℝ) where
  carrier := {x | Summable (workTerm a x)}
  zero_mem' := by
    show Summable (workTerm a 0)
    have : workTerm a 0 = 0 := by funext j; simp [workTerm, reciprocalWork_zero]
    rw [this]
    exact summable_zero
  add_mem' hx hy := (global_fusion ha hx hy).2.1
  neg_mem' {x} hx := by
    show Summable (workTerm a (-x))
    rw [workTerm_neg]
    exact hx

theorem mem_admissible_iff (ha : ∀ j, 1 ≤ a j) (x : ℕ → ℝ) :
    x ∈ admissible ha ↔ extendedWork a x < ⊤ :=
  (extendedWork_lt_top_iff a x).symm

/-- **`(RFT.14)`–`(RFT.15)`**: `∑ x_j² ≤ ∑ a_j² x_j² ≤ 𝒲(x)`; in particular `|x_j| ≤ 𝒲(x)^{1/2}`. -/
theorem sq_summable_and_le (ha : ∀ j, 1 ≤ a j) {x : ℕ → ℝ} (hx : Summable (workTerm a x)) :
    Summable (fun j => x j ^ 2) ∧ Summable (fun j => a j ^ 2 * x j ^ 2) ∧
      ∑' j, x j ^ 2 ≤ ∑' j, a j ^ 2 * x j ^ 2 ∧ ∑' j, a j ^ 2 * x j ^ 2 ≤ work a x ∧
      ∀ j, |x j| ≤ Real.sqrt (work a x) := by
  have h1 : ∀ j, x j ^ 2 ≤ a j ^ 2 * x j ^ 2 := fun j => by
    have : 1 ≤ a j ^ 2 := one_le_pow₀ (ha j)
    nlinarith [sq_nonneg (x j)]
  have h2 : ∀ j, a j ^ 2 * x j ^ 2 ≤ workTerm a x j := fun j =>
    mul_le_mul_of_nonneg_left (sq_le_reciprocalWork _) (sq_nonneg _)
  have hs2 : Summable (fun j => a j ^ 2 * x j ^ 2) :=
    Summable.of_nonneg_of_le (fun j => by positivity) h2 hx
  have hs1 : Summable (fun j => x j ^ 2) :=
    Summable.of_nonneg_of_le (fun j => by positivity) h1 hs2
  refine ⟨hs1, hs2, hs1.tsum_le_tsum h1 hs2, hs2.tsum_le_tsum h2 hx, fun j => ?_⟩
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt ((h1 j).trans ((h2 j).trans (workTerm_le_work hx j)))

end Fusion

/-! ### Theorem 6.1: bounded amplified work selects zero -/

/-- **Theorem 6.1, `(RFT.28)`**: for `d > 1`, the amplified works `𝒲(dⁿx)` are bounded iff
`x = 0`. -/
theorem bounded_amplified_work_iff (ha : ∀ j, 1 ≤ a j) {d : ℝ} (hd : 1 < d) (x : ℕ → ℝ) :
    (⨆ n : ℕ, extendedWork a (fun j => d ^ n * x j)) < ⊤ ↔ x = 0 := by
  constructor
  · intro hb
    by_contra hx
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
      by_contra! h
      exact hx (funext h)
    set B := (⨆ n : ℕ, extendedWork a (fun j => d ^ n * x j)).toReal
    have hbound : ∀ n : ℕ, (d ^ n * x j) ^ 2 ≤ B := fun n => by
      have h1 : ENNReal.ofReal (workTerm a (fun j => d ^ n * x j) j) ≤
          extendedWork a (fun j => d ^ n * x j) :=
        ENNReal.le_tsum (f := fun k => ENNReal.ofReal (workTerm a (fun j => d ^ n * x j) k)) j
      have h2 := h1.trans (le_iSup (fun n : ℕ => extendedWork a (fun j => d ^ n * x j)) n)
      have h3 := (ENNReal.ofReal_le_iff_le_toReal hb.ne).1 h2
      have h4 : (d ^ n * x j) ^ 2 ≤ workTerm a (fun j => d ^ n * x j) j := by
        have : 1 ≤ a j ^ 2 := one_le_pow₀ (ha j)
        have h5 := sq_le_reciprocalWork (d ^ n * x j)
        unfold workTerm
        nlinarith [sq_nonneg (d ^ n * x j)]
      exact h4.trans h3
    have htend : Tendsto (fun n : ℕ => (d ^ n * x j) ^ 2) atTop atTop := by
      have hpow := tendsto_pow_atTop_atTop_of_one_lt hd
      have hx2 : 0 < x j ^ 2 := by positivity
      have : (fun n : ℕ => (d ^ n * x j) ^ 2) = fun n => (d ^ n) ^ 2 * x j ^ 2 := by
        funext n; ring
      rw [this]
      exact ((tendsto_pow_atTop (two_ne_zero)).comp hpow).atTop_mul_const hx2
    obtain ⟨n, hn⟩ := (htend.eventually_gt_atTop B).exists
    exact absurd (hbound n) (not_le.2 hn)
  · rintro rfl
    have h0 : extendedWork a (fun _ => 0) = 0 := by
      simp [extendedWork, workTerm, reciprocalWork_zero]
    simp [h0]

/-! ### Theorem 5.1: the sharp compactness threshold in `ℓ¹` -/

/-- The ambient space `ℓ¹(ℕ; ℝ)`. -/
abbrev L1 := lp (fun _ : ℕ => ℝ) 1

/-- **`(RFT.22)`** the work sublevel `K_C(a) = {x ∈ ℓ¹ : 𝒲_a(x) ≤ C}`. -/
def sublevel (C : ℝ) : Set L1 := {x | extendedWork a x ≤ ENNReal.ofReal C}

theorem L1_summable (x : L1) : Summable fun j => |(x : ℕ → ℝ) j| := by
  have h := (memℓp_gen_iff (by norm_num : (0 : ℝ) < (1 : ℝ≥0∞).toReal)).1 (lp.memℓp x)
  simpa [Real.norm_eq_abs] using h

theorem L1_norm_eq (x : L1) : ‖x‖ = ∑' j, |(x : ℕ → ℝ) j| := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (1 : ℝ≥0∞).toReal)]
  simp [Real.norm_eq_abs]

theorem continuous_L1_apply (j : ℕ) : Continuous fun x : L1 => (x : ℕ → ℝ) j := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun x y => ?_).continuous
  rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
  have := lp.norm_apply_le_norm (by norm_num : (1 : ℝ≥0∞) ≠ 0) (x - y) j
  simpa [Real.norm_eq_abs] using this

theorem continuous_reciprocalWork : Continuous reciprocalWork := by
  unfold reciprocalWork
  fun_prop

theorem isClosed_sublevel (C : ℝ) : IsClosed (sublevel a C) := by
  have hset : sublevel a C = ⋂ N : ℕ, {x : L1 | ∑ j ∈ Finset.range N,
      ENNReal.ofReal (workTerm a x j) ≤ ENNReal.ofReal C} := by
    ext x
    simp only [sublevel, extendedWork, Set.mem_setOf_eq, Set.mem_iInter,
      ENNReal.tsum_eq_iSup_nat, iSup_le_iff]
  rw [hset]
  refine isClosed_iInter fun N => isClosed_le ?_ continuous_const
  refine continuous_finsetSum _ fun j _ => ENNReal.continuous_ofReal.comp ?_
  exact continuous_const.mul (continuous_reciprocalWork.comp (continuous_L1_apply j))

/-- Cauchy–Schwarz for nonnegative series. -/
theorem tsum_mul_le_sqrt_mul_sqrt {f g : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j) (hg : ∀ j, 0 ≤ g j)
    (hf2 : Summable fun j => f j ^ 2) (hg2 : Summable fun j => g j ^ 2) :
    Summable (fun j => f j * g j) ∧
      ∑' j, f j * g j ≤ Real.sqrt (∑' j, f j ^ 2) * Real.sqrt (∑' j, g j ^ 2) := by
  have hsum : Summable (fun j => f j * g j) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (hf j) (hg j))
      (fun j => by nlinarith [sq_nonneg (f j - g j)]) ((hf2.add hg2).div_const 2)
  refine ⟨hsum, ?_⟩
  have h := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two hf hg
    (by simpa [Real.rpow_two] using hf2) (by simpa [Real.rpow_two] using hg2)
  simp only [Real.rpow_two] at h
  rwa [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

section Threshold

variable {a}

/-- **Theorem 5.1, `(RFT.24)`**: under `∑ a_j⁻² < ∞`, a finite-work sequence is summable and
`∑_{j ≥ N} |x_j| ≤ 𝒲(x)^{1/2} (∑_{j ≥ N} a_j⁻²)^{1/2}`. -/
theorem tail_bound (ha : ∀ j, 1 ≤ a j) (hsum : Summable fun j => (a j ^ 2)⁻¹) {x : ℕ → ℝ}
    (hx : Summable (workTerm a x)) (N : ℕ) :
    Summable (fun j => |x j|) ∧
      ∑' j, |x (j + N)| ≤ Real.sqrt (work a x) * Real.sqrt (∑' j, (a (j + N) ^ 2)⁻¹) := by
  have hapos : ∀ j, 0 < a j := fun j => lt_of_lt_of_le one_pos (ha j)
  obtain ⟨-, hs2, -, hle, -⟩ := sq_summable_and_le ha hx
  -- `|x_j| = (a_j |x_j|) · a_j⁻¹`
  have hfac : ∀ j, |x j| = (a j * |x j|) * (a j)⁻¹ := fun j => by
    field_simp [(hapos j).ne']
  have hf2 : ∀ j, (a j * |x j|) ^ 2 = a j ^ 2 * x j ^ 2 := fun j => by
    rw [mul_pow, sq_abs]
  have hg2 : ∀ j, ((a j)⁻¹) ^ 2 = (a j ^ 2)⁻¹ := fun j => by rw [inv_pow]
  have hCS := tsum_mul_le_sqrt_mul_sqrt (f := fun j => a j * |x j|) (g := fun j => (a j)⁻¹)
    (fun j => mul_nonneg (hapos j).le (abs_nonneg _)) (fun j => inv_nonneg.2 (hapos j).le)
    (by simpa only [hf2] using hs2) (by simpa only [hg2] using hsum)
  have hsx : Summable (fun j => |x j|) := hCS.1.congr fun j => (hfac j).symm
  refine ⟨hsx, ?_⟩
  have hs2N : Summable fun j => a (j + N) ^ 2 * x (j + N) ^ 2 := (summable_nat_add_iff N).2 hs2
  have hsumN : Summable fun j => (a (j + N) ^ 2)⁻¹ := (summable_nat_add_iff N).2 hsum
  have hCSN := tsum_mul_le_sqrt_mul_sqrt (f := fun j => a (j + N) * |x (j + N)|)
    (g := fun j => (a (j + N))⁻¹)
    (fun j => mul_nonneg (hapos _).le (abs_nonneg _)) (fun j => inv_nonneg.2 (hapos _).le)
    (by simpa only [hf2] using hs2N) (by simpa only [hg2] using hsumN)
  have htailWork : ∑' j, a (j + N) ^ 2 * x (j + N) ^ 2 ≤ work a x := by
    have hsplit := hs2.sum_add_tsum_nat_add N
    have hhead : 0 ≤ ∑ i ∈ Finset.range N, a i ^ 2 * x i ^ 2 :=
      Finset.sum_nonneg fun i _ => by positivity
    linarith
  calc ∑' j, |x (j + N)| = ∑' j, a (j + N) * |x (j + N)| * (a (j + N))⁻¹ :=
        tsum_congr fun j => hfac (j + N)
    _ ≤ Real.sqrt (∑' j, (a (j + N) * |x (j + N)|) ^ 2) *
          Real.sqrt (∑' j, ((a (j + N))⁻¹) ^ 2) := hCSN.2
    _ = Real.sqrt (∑' j, a (j + N) ^ 2 * x (j + N) ^ 2) *
          Real.sqrt (∑' j, (a (j + N) ^ 2)⁻¹) := by
        simp only [hf2, hg2]
    _ ≤ Real.sqrt (work a x) * Real.sqrt (∑' j, (a (j + N) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt htailWork) (Real.sqrt_nonneg _)

theorem work_le_of_mem_sublevel {C : ℝ} {x : L1} (hx : x ∈ sublevel a C) :
    Summable (workTerm a x) ∧ work a x ≤ max C 0 := by
  have hfin : extendedWork a x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx
  have hs := (extendedWork_ne_top_iff a x).1 hfin
  refine ⟨hs, ?_⟩
  have hx : extendedWork a x ≤ ENNReal.ofReal C := hx
  rw [extendedWork_eq_ofReal a hs] at hx
  have := (ENNReal.ofReal_le_ofReal_iff (le_max_right C 0)).1
    (hx.trans (ENNReal.ofReal_le_ofReal (le_max_left C 0)))
  exact this

/-- Truncation of an `ℓ¹` sequence to its first `N` coordinates. -/
def truncation (N : ℕ) (x : L1) : L1 := ∑ j ∈ Finset.range N, lp.single 1 j ((x : ℕ → ℝ) j)

/-- Synthesis of an `N`-coordinate head. -/
def head (N : ℕ) (v : Fin N → ℝ) : L1 := ∑ i : Fin N, lp.single 1 (i : ℕ) (v i)

theorem continuous_head (N : ℕ) : Continuous (head N) := by
  unfold head
  refine continuous_finsetSum _ fun i _ => ?_
  exact (lp.singleContinuousLinearMap ℝ (fun _ : ℕ => ℝ) 1 (i : ℕ)).continuous.comp
    (continuous_apply i)

theorem head_eq_truncation (N : ℕ) (x : L1) :
    head N (fun i => (x : ℕ → ℝ) i) = truncation N x :=
  Fin.sum_univ_eq_sum_range (fun n => lp.single 1 n ((x : ℕ → ℝ) n)) N

theorem norm_sub_truncation (N : ℕ) (x : L1) :
    ‖x - truncation N x‖ = ∑' j, |(x : ℕ → ℝ) (j + N)| := by
  have hcompl := lp.norm_compl_sum_single
    (by norm_num : (0 : ℝ) < (1 : ℝ≥0∞).toReal) x (Finset.range N)
  simp only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] at hcompl
  rw [truncation, hcompl, L1_norm_eq]
  have hsplit := (L1_summable x).sum_add_tsum_nat_add N
  linarith

/-- **Theorem 5.1, sufficiency**: under `∑ a_j⁻² < ∞` every sublevel is totally bounded. -/
theorem totallyBounded_sublevel (ha : ∀ j, 1 ≤ a j) (hsum : Summable fun j => (a j ^ 2)⁻¹)
    (C : ℝ) : TotallyBounded (sublevel a C) := by
  set C' := max C 0
  have hC' : 0 ≤ C' := le_max_right C 0
  rw [Metric.totallyBounded_iff]
  intro ε hε
  -- a tail index `N` with `√C' √(∑_{j ≥ N} a_j⁻²) < ε/2`
  have htail : Tendsto (fun N => Real.sqrt C' * Real.sqrt (∑' j, (a (j + N) ^ 2)⁻¹)) atTop
      (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp (tendsto_sum_nat_add fun j => (a j ^ 2)⁻¹)
    rw [Real.sqrt_zero] at h
    simpa using h.const_mul (Real.sqrt C')
  obtain ⟨N, hN⟩ := (htail.eventually (gt_mem_nhds (half_pos hε))).exists
  let K : Set L1 := head N '' Metric.closedBall (0 : Fin N → ℝ) (Real.sqrt C')
  have hKcompact : IsCompact K :=
    (isCompact_closedBall (0 : Fin N → ℝ) _).image (continuous_head N)
  obtain ⟨centers, hfin, hcover⟩ :=
    Metric.totallyBounded_iff.mp hKcompact.totallyBounded (ε / 2) (half_pos hε)
  refine ⟨centers, hfin, fun x hx => ?_⟩
  obtain ⟨hs, hW⟩ := work_le_of_mem_sublevel hx
  have hcoord := (sq_summable_and_le ha hs).2.2.2.2
  have hvball : (fun i : Fin N => (x : ℕ → ℝ) i) ∈ Metric.closedBall (0 : Fin N → ℝ)
      (Real.sqrt C') := by
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    rw [Real.norm_eq_abs]
    exact (hcoord i).trans (Real.sqrt_le_sqrt hW)
  have htruncK : truncation N x ∈ K := ⟨_, hvball, head_eq_truncation N x⟩
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp (hcover htruncK)
  obtain ⟨hcCenter, htruncBall⟩ := Set.mem_iUnion.mp hc
  refine Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hcCenter, ?_⟩⟩
  rw [Metric.mem_ball] at htruncBall ⊢
  have htailx := (tail_bound ha hsum hs N).2
  have hdist : dist x (truncation N x) < ε / 2 := by
    rw [dist_eq_norm, norm_sub_truncation]
    calc ∑' j, |(x : ℕ → ℝ) (j + N)|
        ≤ Real.sqrt (work a x) * Real.sqrt (∑' j, (a (j + N) ^ 2)⁻¹) := htailx
      _ ≤ Real.sqrt C' * Real.sqrt (∑' j, (a (j + N) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hW) (Real.sqrt_nonneg _)
      _ < ε / 2 := hN
  exact (dist_triangle x (truncation N x) c).trans_lt (by linarith)

/-- **Theorem 5.1, sufficiency**: every sublevel is compact in `ℓ¹`. -/
theorem isCompact_sublevel (ha : ∀ j, 1 ≤ a j) (hsum : Summable fun j => (a j ^ 2)⁻¹)
    (C : ℝ) : IsCompact (sublevel a C) :=
  (totallyBounded_sublevel ha hsum C).isCompact_of_isClosed (isClosed_sublevel a C)

theorem coe_sum_single (N : ℕ) (c : ℕ → ℝ) (j : ℕ) :
    ((∑ i ∈ Finset.range N, lp.single 1 i (c i) : L1) : ℕ → ℝ) j =
      if j < N then c j else 0 := by
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.coeFn_single]
  split_ifs with h
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro hj; exact absurd (Finset.mem_range.2 h) hj
  · refine Finset.sum_eq_zero fun i hi => ?_
    have : j ≠ i := fun h' => h (h' ▸ Finset.mem_range.1 hi)
    simp [this]

/-- **Theorem 5.1, necessity, `(RFT.25)`–`(RFT.27)`**: if one positive sublevel is bounded in
`ℓ¹`, then `∑ a_j⁻² < ∞`. -/
theorem summable_of_isBounded_sublevel (ha : ∀ j, 1 ≤ a j) {C : ℝ} (hC : 0 < C)
    (hb : Bornology.IsBounded (sublevel a C)) : Summable fun j => (a j ^ 2)⁻¹ := by
  by_contra hns
  have hpos : ∀ j, 0 < a j ^ 2 := fun j => by have := ha j; positivity
  have hinv_le : ∀ j, (a j ^ 2)⁻¹ ≤ 1 := fun j => inv_le_one_of_one_le₀ (one_le_pow₀ (ha j))
  set S : ℕ → ℝ := fun N => ∑ j ∈ Finset.range N, (a j ^ 2)⁻¹
  have hS : Tendsto S atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg fun j => (inv_pos.2 (hpos j)).le).1 hns
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : L1)).1 hb
  set δ : ℝ := min 1 (Real.sqrt C / 2)
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδC : δ ^ 2 ≤ C / 4 := by
    have h := min_le_right 1 (Real.sqrt C / 2)
    have hsq : (Real.sqrt C / 2) ^ 2 = C / 4 := by
      rw [div_pow, Real.sq_sqrt hC.le]; norm_num
    calc δ ^ 2 ≤ (Real.sqrt C / 2) ^ 2 := pow_le_pow_left₀ hδpos.le h 2
      _ = C / 4 := hsq
  have hsqrtS : Tendsto (fun N => δ * Real.sqrt (S N)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp hS).const_mul_atTop hδpos
  obtain ⟨N, hN1, hNR⟩ := ((hS.eventually_ge_atTop 1).and
    (hsqrtS.eventually_gt_atTop R)).exists
  have hSpos : 0 < S N := lt_of_lt_of_le one_pos hN1
  have hsqrtpos : 0 < Real.sqrt (S N) := Real.sqrt_pos.2 hSpos
  set c : ℕ → ℝ := fun j => δ * (a j ^ 2)⁻¹ / Real.sqrt (S N)
  set v : L1 := ∑ i ∈ Finset.range N, lp.single 1 i (c i)
  have hv : ∀ j, (v : ℕ → ℝ) j = if j < N then c j else 0 := coe_sum_single N c
  have hc0 : ∀ j, 0 ≤ c j := fun j => by have := hpos j; positivity
  have hc1 : ∀ j, |c j| ≤ 1 := fun j => by
    rw [abs_of_nonneg (hc0 j)]
    have hsq1 : 1 ≤ Real.sqrt (S N) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hN1
    have h1 : δ * (a j ^ 2)⁻¹ ≤ 1 := by
      have := hinv_le j
      have := inv_pos.2 (hpos j)
      nlinarith
    have h2 : c j ≤ δ * (a j ^ 2)⁻¹ :=
      div_le_self (by have := hpos j; positivity) hsq1
    linarith
  -- the work of `v` is at most `cosh(1) δ² ≤ C`
  have hwork : extendedWork a v ≤ ENNReal.ofReal C := by
    have hsupp : ∀ j ∉ Finset.range N, ENNReal.ofReal (workTerm a v j) = 0 := fun j hj => by
      have hvj := hv j
      rw [if_neg (fun h => hj (Finset.mem_range.2 h))] at hvj
      simp only [workTerm, hvj, reciprocalWork_zero, mul_zero, ENNReal.ofReal_zero]
    rw [extendedWork, tsum_eq_sum hsupp, ← ENNReal.ofReal_sum_of_nonneg
      (fun j _ => workTerm_nonneg a v j)]
    apply ENNReal.ofReal_le_ofReal
    have hterm : ∀ j ∈ Finset.range N,
        workTerm a v j ≤ Real.cosh 1 * (δ ^ 2 * (a j ^ 2)⁻¹ / S N) := fun j hj => by
      have hjN := Finset.mem_range.1 hj
      rw [workTerm, hv, if_pos hjN]
      have h1 := reciprocalWork_le_cosh_one_mul_sq (hc1 j)
      have hcj : a j ^ 2 * c j ^ 2 = δ ^ 2 * (a j ^ 2)⁻¹ / S N := by
        simp only [c]
        rw [div_pow, mul_pow, Real.sq_sqrt hSpos.le]
        field_simp [(hpos j).ne']
      calc a j ^ 2 * reciprocalWork (c j) ≤ a j ^ 2 * (Real.cosh 1 * c j ^ 2) :=
            mul_le_mul_of_nonneg_left h1 (hpos j).le
        _ = Real.cosh 1 * (a j ^ 2 * c j ^ 2) := by ring
        _ = Real.cosh 1 * (δ ^ 2 * (a j ^ 2)⁻¹ / S N) := by rw [hcj]
    calc ∑ j ∈ Finset.range N, workTerm a v j
        ≤ ∑ j ∈ Finset.range N, Real.cosh 1 * (δ ^ 2 * (a j ^ 2)⁻¹ / S N) :=
          Finset.sum_le_sum hterm
      _ = Real.cosh 1 * (δ ^ 2 * S N / S N) := by
          rw [← Finset.mul_sum, ← Finset.sum_div, ← Finset.mul_sum]
      _ = Real.cosh 1 * δ ^ 2 := by rw [mul_div_assoc, div_self hSpos.ne', mul_one]
      _ ≤ 2 * (C / 4) := by
          gcongr
          · exact cosh_one_le_two
      _ ≤ C := by linarith
  -- but its `ℓ¹` norm is `δ √S_N > R`
  have hnorm : ‖v‖ = δ * Real.sqrt (S N) := by
    rw [L1_norm_eq]
    have hsupp : ∀ j ∉ Finset.range N, |(v : ℕ → ℝ) j| = 0 := fun j hj => by
      rw [hv, if_neg (fun h => hj (Finset.mem_range.2 h)), abs_zero]
    rw [tsum_eq_sum hsupp]
    have : ∀ j ∈ Finset.range N, |(v : ℕ → ℝ) j| = δ * (a j ^ 2)⁻¹ / Real.sqrt (S N) :=
      fun j hj => by rw [hv, if_pos (Finset.mem_range.1 hj), abs_of_nonneg (hc0 j)]
    rw [Finset.sum_congr rfl this, ← Finset.sum_div, ← Finset.mul_sum]
    change δ * S N / Real.sqrt (S N) = δ * Real.sqrt (S N)
    rw [div_eq_iff hsqrtpos.ne', mul_assoc, Real.mul_self_sqrt hSpos.le]
  have hvmem : v ∈ Metric.closedBall (0 : L1) R := hR hwork
  rw [Metric.mem_closedBall, dist_zero_right, hnorm] at hvmem
  linarith

/-- **Theorem 5.1, `(RFT.23)`**: the three properness conditions are equivalent. -/
theorem compactness_tfae (ha : ∀ j, 1 ≤ a j) :
    List.TFAE [∀ C : ℝ, 0 ≤ C → IsCompact (sublevel a C),
      ∃ C : ℝ, 0 < C ∧ Bornology.IsBounded (sublevel a C),
      Summable fun j => (a j ^ 2)⁻¹] := by
  tfae_have 1 → 2 := fun h => ⟨1, one_pos, (h 1 zero_le_one).isBounded⟩
  tfae_have 2 → 3 := fun ⟨C, hC, hb⟩ => summable_of_isBounded_sublevel ha hC hb
  tfae_have 3 → 1 := fun hsum C _ => isCompact_sublevel ha hsum C
  tfae_finish

/-- **Theorem 5.1, depth weights**: for `a_j = j + 1` every sublevel is compact. -/
theorem isCompact_sublevel_depth (C : ℝ) :
    IsCompact (sublevel (fun j => (j : ℝ) + 1) C) := by
  refine isCompact_sublevel (fun j => by have : (0 : ℝ) ≤ j := j.cast_nonneg; linarith) ?_ C
  have h := (summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 (by norm_num : 1 < 2))
  refine h.congr fun j => ?_
  push_cast
  ring

end Threshold

/-- **Loop C**: without complexity weights the translates `t eₙ` all have work `ω(t)` but are
pairwise at `ℓ¹` distance `2|t|`; for `t ≠ 0` no subsequence is Cauchy. -/
theorem unweighted_translates (t : ℝ) :
    (∀ n, extendedWork (fun _ => 1) (lp.single 1 n t : L1) = ENNReal.ofReal (reciprocalWork t)) ∧
      (∀ n m, n ≠ m → dist (lp.single 1 n t : L1) (lp.single 1 m t) = 2 * |t|) ∧
      (t ≠ 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
        ¬ CauchySeq fun k => (lp.single 1 (φ k) t : L1)) := by
  have hdist : ∀ n m, n ≠ m → dist (lp.single 1 n t : L1) (lp.single 1 m t) = 2 * |t| := by
    intro n m hnm
    rw [dist_eq_norm, L1_norm_eq]
    have hsupp : ∀ j ∉ ({n, m} : Finset ℕ),
        |((lp.single 1 n t - lp.single 1 m t : L1) : ℕ → ℝ) j| = 0 := fun j hj => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      simp [hj.1, hj.2]
    rw [tsum_eq_sum hsupp, Finset.sum_pair hnm]
    simp [hnm, Ne.symm hnm]
    ring
  refine ⟨fun n => ?_, hdist, fun ht φ hφ hC => ?_⟩
  · rw [extendedWork, tsum_eq_single n]
    · simp [workTerm]
    · intro j hj
      simp [workTerm, hj, reciprocalWork_zero]
  · obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hC (2 * |t|) (by positivity)
    have h := hN (N + 1) (Nat.le_succ N)
    rw [hdist _ _ (hφ.injective.ne (Nat.succ_ne_self N))] at h
    exact lt_irrefl _ h

end GaloisForLFunctions.HTGeometry.ReciprocalFusion
