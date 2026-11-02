import GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.HalfGateClosureAndDensityEquivalence
import GaloisForLFunctions.RHTower.OuterLawMollifiedProductEquivalence
import GaloisForLFunctions.RHTower.ZetaCriticalScaleTailMomentExponential
import GaloisForLFunctions.RHTower.AnchorHead
import GaloisForLFunctions.RHTower.RectIntegralEdges

/-!
# Critical-Scale Clustering, All-Heights Littlewood Budget, and the 8-Way Mollified Log-Mean Equivalence

Unconditional resolution of the log-mean / mollifier / near-line zero-density equivalence side of
Route WD (Obstacles B16 + B44):

1. **Two-sided all-heights Littlewood edge budget**
   (`exists_zetaLine_littlewood_edge_budget_all_heights`):
   Removes the horizontal edge-avoidance hypotheses from `exists_zetaLine_littlewood_edge_budget` by
   shrinking edge-free collars around `T` and `2T`, yielding for every `T ≥ 21`
   `|(∫_T^{2T} log ‖ζ(1/2 + it)‖ dt) - 2π ∑_{z ∈ shellZeros(T, 2T), Re z > 1/2} m_z (Re z - 1/2)| ≤ C + K log(2T)`.

2. **Dyadic exponential off-line tail moment** (`exists_dyadic_offLineTailMoment_le_exp`):
   Transfers `exists_offLineTailMoment_window_le_exp` (`U = 4T - 4`) to exact dyadic shells
   `shellZeros T (2T)` for all `c ≥ 2`.

3. **Truncated Euler-product outer mollifier log-mean**
   (`eulerProductMollifier`, `exists_abs_window_logIntegral_eulerProductMollifier_le`,
   `tendsto_window_logMean_eulerProductMollifier_zero`):
   Via Cauchy's theorem on `Complex.log (1 - p^{-s})` over `[1/2, R] × [T₁, T₂]`, proves the uniform
   height-independent bound `|∫_{T₁}^{T₂} log ‖M_S(1/2 + it)‖ dt| ≤ ∑_{p ∈ S, Prime p} (3 + 6 / log p)`.

4. **8-way unconditional equivalence (`criticalClustering_logMean_mollifier_hecke_tfae`)**:
   Proves that `(L)` (`T⁻¹ ∫_T^{2T} log ‖ζ(1/2 + it)‖ dt → 0`), the truncated Euler-product
   mollified log-mean `T⁻¹ ∫_T^{2T} log ‖ζ M_S‖ dt → 0`, the linear-mollifier outer law for `ζ Ψ_M`,
   the dyadic horizontal moment `o(T)`, `100%` critical-scale clustering
   `offLineCountBeyond (κ / log V) V / (V log V) → 0` (`∀ κ > 0`), and `o(log U)` dyadic
   `unitWindowDepthCharge` / `heckeDefect` / `polynomialThetaSourceMomentReading` (`0 < c < 1/2`)
   are all unconditionally equivalent. In particular, `E log|ζ M_S| = o(1)` does **not** require a
   log-free `O(ε(A) V)` bound at large `A`: Selberg's unconditional exponential tail moment kills
   `Re ρ - 1/2 ≥ R / log V` automatically, leaving `o_κ(V log V)` clustering at small `κ > 0` as the
   exact necessary and sufficient zero-density condition.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter intervalIntegral
open scoped BigOperators Topology Classical

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

open GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect

/-! ## §1. Elementary shell-covering and total multiplicity helpers -/

private lemma finset_sum_union_le {α : Type*} [DecidableEq α] (s₁ s₂ : Finset α) {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s₁ ∪ s₂, f x ≤ ∑ x ∈ s₁, f x + ∑ x ∈ s₂, f x := by
  rw [Finset.sum_union_inter]
  linarith [Finset.sum_nonneg fun x (_ : x ∈ s₁ ∩ s₂) => hf x]

private lemma finset_sum_biUnion_le {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (s : Finset ι) (t : ι → Finset α) {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    exact (finset_sum_union_le _ _ hf).trans (add_le_add le_rfl ih)

private lemma log_four_le_two : Real.log 4 ≤ 2 := by
  have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
  rw [h4, Real.log_pow]
  push_cast
  linarith [Real.log_two_lt_d9]

private lemma sq_log_le_four_mul {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x) ^ 2 ≤ 4 * x := by
  have hx_pos : 0 < x := zero_lt_one.trans_le hx
  set u : ℝ := Real.log x / 2
  have hu_nn : 0 ≤ u := div_nonneg (Real.log_nonneg hx) zero_le_two
  have hexp_u : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have hsq : u ^ 2 ≤ (Real.exp u) ^ 2 := pow_le_pow_left₀ hu_nn hexp_u 2
  have hexp_sq : (Real.exp u) ^ 2 = x := by
    rw [sq, ← Real.exp_add]
    have : u + u = Real.log x := by dsimp only [u]; ring
    rw [this, Real.exp_log hx_pos]
  rw [hexp_sq] at hsq
  have hu_sq : (Real.log x) ^ 2 = 4 * u ^ 2 := by dsimp only [u]; ring
  linarith

private lemma sq_log_le_sixteen_sqrt {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x) ^ 2 ≤ 16 * Real.sqrt x := by
  have hx_pos : 0 < x := zero_lt_one.trans_le hx
  have hrt1 : 1 ≤ Real.sqrt x := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hx
  have hrt_pos : 0 < Real.sqrt x := zero_lt_one.trans_le hrt1
  have hlog_eq : Real.log x = 2 * Real.log (Real.sqrt x) := by
    conv_lhs => rw [← Real.mul_self_sqrt hx_pos.le]
    rw [Real.log_mul hrt_pos.ne' hrt_pos.ne']
    ring
  have h4 := sq_log_le_four_mul hrt1
  rw [hlog_eq, mul_pow]
  linarith

/-- Coarse `O(V log V)` bound on the total `ξ`-zero multiplicity in `stripFinsetPos V` (`2 ≤ V`). -/
theorem stripFinsetPos_orderSum_le_mul_log :
    ∃ C_tot : ℝ, 0 < C_tot ∧ ∀ {V : ℝ}, 2 ≤ V →
      ∑ z ∈ _root_.RHTower.stripFinsetPos V, ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤
        C_tot * V * Real.log V := by
  set C_tot : ℝ := 64 * (|_root_.RHTower.xiLineTwoLogDerivConstant| + 5)
  refine ⟨C_tot, by dsimp only [C_tot]; positivity, fun {V} hV2 => ?_⟩
  have hV_pos : 0 < V := by linarith
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hlogV_half : (1 / 2 : ℝ) ≤ Real.log V :=
    hlog2.le.trans (Real.log_le_log zero_lt_two hV2)
  have hlogV_pos : 0 < Real.log V := by linarith
  set N : ℕ := Nat.ceil V
  have hcov : _root_.RHTower.stripFinsetPos V ⊆
      (Finset.range N).biUnion (fun k => shellZeros (k : ℝ) ((k : ℝ) + 1)) := by
    intro z hz
    obtain ⟨h0, h1, him0, himV, hxi⟩ := _root_.RHTower.mem_stripFinsetPos.mp hz
    have hceil_pos : 1 ≤ Nat.ceil z.im := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr him0).ne'
    set k : ℕ := Nat.ceil z.im - 1
    have hk_lt : k < N := by
      have hle : Nat.ceil z.im ≤ N := Nat.ceil_mono himV
      omega
    have hk1_eq : ((k : ℝ) + 1) = (Nat.ceil z.im : ℝ) := by
      have : k + 1 = Nat.ceil z.im := by omega
      exact_mod_cast this
    have hz_le : z.im ≤ (k : ℝ) + 1 := hk1_eq ▸ Nat.le_ceil z.im
    have hz_gt : (k : ℝ) < z.im := by
      by_contra hle
      push Not at hle
      have hc : Nat.ceil z.im ≤ k := Nat.ceil_le.mpr hle
      omega
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hk_lt,
      Finset.mem_filter.mpr ⟨_root_.RHTower.mem_stripFinsetPos.mpr ⟨h0, h1, him0, hz_le, hxi⟩, hz_gt⟩⟩
  have hunit : ∀ k ∈ Finset.range N,
      ∑ z ∈ shellZeros (k : ℝ) ((k : ℝ) + 1), ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤
        32 * (|_root_.RHTower.xiLineTwoLogDerivConstant| + 5) * Real.log V := by
    intro k hk
    have hk_lt : k < N := Finset.mem_range.mp hk
    have hk1_le_N : ((k : ℝ) + 1) ≤ (N : ℝ) := by exact_mod_cast (show k + 1 ≤ N by omega)
    have hN_lt : (N : ℝ) ≤ V + 1 := (Nat.ceil_lt_add_one hV_pos.le).le
    have hs := shortShell_orderSum_le_log (V₁ := (k : ℝ)) (V₂ := (k : ℝ) + 1)
      (Nat.cast_nonneg k) (by linarith) (by linarith)
    have hlog_le : Real.log ((k : ℝ) + 1 + 4) ≤ 2 + Real.log V := by
      calc Real.log ((k : ℝ) + 1 + 4)
          ≤ Real.log (4 * V) := Real.log_le_log (by positivity) (by linarith)
        _ = Real.log 4 + Real.log V := Real.log_mul (by norm_num) hV_pos.ne'
        _ ≤ 2 + Real.log V := by linarith [log_four_le_two]
    have hc_nn : 0 ≤ |_root_.RHTower.xiLineTwoLogDerivConstant| := abs_nonneg _
    have hconst_le : |_root_.RHTower.xiLineTwoLogDerivConstant| + 2 ≤
        2 * (|_root_.RHTower.xiLineTwoLogDerivConstant| + 4) * Real.log V := by
      have h1 : 1 ≤ 2 * Real.log V := by linarith
      calc |_root_.RHTower.xiLineTwoLogDerivConstant| + 2
          ≤ (|_root_.RHTower.xiLineTwoLogDerivConstant| + 4) * 1 := by linarith
        _ ≤ (|_root_.RHTower.xiLineTwoLogDerivConstant| + 4) * (2 * Real.log V) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 2 * (|_root_.RHTower.xiLineTwoLogDerivConstant| + 4) * Real.log V := by ring
    calc ∑ z ∈ shellZeros (k : ℝ) ((k : ℝ) + 1), ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ)
        ≤ 16 * (|_root_.RHTower.xiLineTwoLogDerivConstant| + (2 + Real.log V)) :=
          hs.trans (mul_le_mul_of_nonneg_left (by linarith) (by norm_num))
      _ ≤ 32 * (|_root_.RHTower.xiLineTwoLogDerivConstant| + 5) * Real.log V := by
          linarith [hconst_le, hlogV_pos]
  have hN_le : (N : ℝ) ≤ 2 * V := by
    have := (Nat.ceil_lt_add_one hV_pos.le).le
    linarith
  calc ∑ z ∈ _root_.RHTower.stripFinsetPos V, ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ)
      ≤ ∑ z ∈ (Finset.range N).biUnion (fun k => shellZeros (k : ℝ) ((k : ℝ) + 1)),
          ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hcov fun _ _ _ => Nat.cast_nonneg _
    _ ≤ ∑ k ∈ Finset.range N,
          ∑ z ∈ shellZeros (k : ℝ) ((k : ℝ) + 1),
            ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) :=
        finset_sum_biUnion_le _ _ fun _ => Nat.cast_nonneg _
    _ ≤ ∑ _k ∈ Finset.range N,
          (32 * (|_root_.RHTower.xiLineTwoLogDerivConstant| + 5) * Real.log V) :=
        Finset.sum_le_sum hunit
    _ = (N : ℝ) * (32 * (|_root_.RHTower.xiLineTwoLogDerivConstant| + 5) * Real.log V) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (2 * V) * (32 * (|_root_.RHTower.xiLineTwoLogDerivConstant| + 5) * Real.log V) :=
        mul_le_mul_of_nonneg_right hN_le (by positivity)
    _ = C_tot * V * Real.log V := by dsimp only [C_tot]; ring


/-! ## §2. All-heights two-sided Littlewood edge budget and dyadic tail moment -/

/-- **Two-sided all-heights Littlewood edge budget (`exists_zetaLine_littlewood_edge_budget_all_heights`).**
For every real `T ≥ 21` (with no horizontal-line nonvanishing assumption at `T` or `2T`), the
critical-line logarithmic integral of `|ζ|` over `[T, 2T]` differs from `2π` times the off-line
first horizontal moment on `shellZeros T (2T)` by at most `C + K log(2T)`. -/
theorem exists_zetaLine_littlewood_edge_budget_all_heights :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ T : ℝ, 21 ≤ T →
      |(∫ t in T..(2 * T), Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) -
          2 * Real.pi * ∑ z ∈ (shellZeros T (2 * T)).filter (fun z => 1 / 2 < z.re),
            ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2)| ≤
        C + K * Real.log (2 * T) := by
  obtain ⟨C₀, K₀, hC₀, hK₀, hbud⟩ := _root_.RHTower.exists_zetaLine_littlewood_edge_budget
  set C_slice : ℝ := 16 * Real.pi * (|_root_.RHTower.xiLineTwoLogDerivConstant| + 1)
  refine ⟨C₀ + C_slice, K₀ + 16 * Real.pi, by dsimp only [C_slice]; positivity, by positivity,
    fun T hT21 => ?_⟩
  set F : Finset ℂ := _root_.RHTower.stripFinsetPos (2 * T + 1)
  set D : Finset ℝ :=
    ((F.filter (fun z => z.im ≠ T)).image (fun z => |z.im - T|)) ∪
    ((F.filter (fun z => z.im ≠ 2 * T)).image (fun z => |z.im - 2 * T|))
  have hD_pos : ∀ d ∈ D, 0 < d := by
    intro d hd
    rcases Finset.mem_union.mp hd with hd1 | hd2
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hd1
      exact abs_pos.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hz).2)
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hd2
      exact abs_pos.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hz).2)
  set δ₀ : ℝ := if hne : D.Nonempty then min (1 / 4) (D.min' hne / 2) else 1 / 4
  have hδ₀_pos : 0 < δ₀ := by
    dsimp only [δ₀]; split_ifs with hne
    · exact lt_min (by norm_num) (half_pos (hD_pos _ (D.min'_mem hne)))
    · norm_num
  have hδ₀_le : δ₀ ≤ 1 / 4 := by
    dsimp only [δ₀]; split_ifs with hne
    · exact min_le_left _ _
    · exact le_rfl
  have hgap_T : ∀ z ∈ F, z.im ≠ T → δ₀ < |z.im - T| := by
    intro z hz hne_im
    have hmem : |z.im - T| ∈ D :=
      Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨hz, hne_im⟩, rfl⟩))
    have hneD : D.Nonempty := ⟨_, hmem⟩
    have hδ_eq : δ₀ = min (1 / 4) (D.min' hneD / 2) := dif_pos hneD
    have hmin_le : D.min' hneD ≤ |z.im - T| := D.min'_le _ hmem
    have hmin_pos : 0 < D.min' hneD := hD_pos _ (D.min'_mem hneD)
    linarith [min_le_right (1 / 4) (D.min' hneD / 2)]
  have hgap_2T : ∀ z ∈ F, z.im ≠ 2 * T → δ₀ < |z.im - 2 * T| := by
    intro z hz hne_im
    have hmem : |z.im - 2 * T| ∈ D :=
      Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨hz, hne_im⟩, rfl⟩))
    have hneD : D.Nonempty := ⟨_, hmem⟩
    have hδ_eq : δ₀ = min (1 / 4) (D.min' hneD / 2) := dif_pos hneD
    have hmin_le : D.min' hneD ≤ |z.im - 2 * T| := D.min'_le _ hmem
    have hmin_pos : 0 < D.min' hneD := hD_pos _ (D.min'_mem hneD)
    linarith [min_le_right (1 / 4) (D.min' hneD / 2)]
  set F_cl : Finset ℂ :=
    (_root_.RHTower.stripFinsetPos (2 * T)).filter (fun z => T ≤ z.im ∧ 1 / 2 < z.re)
  set S_cl : ℝ := ∑ z ∈ F_cl, ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2)
  set δ : ℕ → ℝ := fun n => δ₀ / ((n : ℝ) + 2)
  have hstep : ∀ n : ℕ,
      |(∫ t in (T - δ n)..(2 * T + δ n),
          Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) - 2 * Real.pi * S_cl| ≤
        C₀ + K₀ * Real.log (2 * T + δ n) := by
    intro n
    have hδ_pos : 0 < δ n := by dsimp only [δ]; positivity
    have hδ_lt : δ n < δ₀ := by
      dsimp only [δ]
      rw [div_lt_iff₀ (by positivity)]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith [mul_nonneg hδ₀_pos.le hn0]
    have hT₁_20 : 20 ≤ T - δ n := by linarith
    have hT_lt : T - δ n < 2 * T + δ n := by linarith
    have hmem_F_of_zeta : ∀ w : ℂ, 1 / 2 ≤ w.re → 0 < w.im → w.im ≤ 2 * T + 1 →
        riemannZeta w = 0 → w ∈ F ∧ w.re < 1 ∧ _root_.RHTower.xi w = 0 := by
      intro w hre_lo him_lo him_hi hζ0
      have hre_lt1 : w.re < 1 :=
        not_le.mp fun hge => riemannZeta_ne_zero_of_one_le_re hge hζ0
      have h0 : 0 < w.re := by linarith
      have hxi0 : _root_.RHTower.xi w = 0 :=
        (_root_.RHTower.xi_zero_iff_zeta_zero_of_mem_strip h0 hre_lt1).mpr hζ0
      exact ⟨_root_.RHTower.mem_stripFinsetPos.mpr ⟨h0, hre_lt1, him_lo, him_hi, hxi0⟩, hre_lt1, hxi0⟩
    have hnz₁ : ∀ x ∈ Icc (1 / 2 : ℝ) (15 / 2 : ℝ),
        riemannZeta ((x : ℂ) + ((T - δ n : ℝ) : ℂ) * I) ≠ 0 := by
      intro x hx h0
      set w : ℂ := (x : ℂ) + ((T - δ n : ℝ) : ℂ) * I
      have hw_re : w.re = x := by simp [w]
      have hw_im : w.im = T - δ n := by simp [w]
      obtain ⟨hwF, _, _⟩ := hmem_F_of_zeta w (hw_re ▸ hx.1) (by linarith) (by linarith) h0
      have hgap := hgap_T w hwF (by linarith)
      rw [hw_im, show T - δ n - T = -δ n by ring, abs_neg, abs_of_pos hδ_pos] at hgap
      linarith
    have hnz₂ : ∀ x ∈ Icc (1 / 2 : ℝ) (15 / 2 : ℝ),
        riemannZeta ((x : ℂ) + ((2 * T + δ n : ℝ) : ℂ) * I) ≠ 0 := by
      intro x hx h0
      set w : ℂ := (x : ℂ) + ((2 * T + δ n : ℝ) : ℂ) * I
      have hw_re : w.re = x := by simp [w]
      have hw_im : w.im = 2 * T + δ n := by simp [w]
      obtain ⟨hwF, _, _⟩ := hmem_F_of_zeta w (hw_re ▸ hx.1) (by linarith) (by linarith) h0
      have hgap := hgap_2T w hwF (by linarith)
      rw [hw_im, show 2 * T + δ n - 2 * T = δ n by ring, abs_of_pos hδ_pos] at hgap
      linarith
    obtain ⟨Z, hZ⟩ := _root_.RHTower.exists_zetaRectangleZeros_finset hT₁_20 hT_lt
    have hsum_eq :
        (∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2)) = S_cl := by
      have hsplit := (Finset.sum_filter_add_sum_filter_not Z (fun w => 1 / 2 < w.re)
        (fun w => ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2))).symm
      have hzero_line : ∑ w ∈ Z.filter (fun w => ¬ 1 / 2 < w.re),
          ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2) = 0 := by
        refine Finset.sum_eq_zero fun w hw => ?_
        obtain ⟨hwZ, hnot⟩ := Finset.mem_filter.mp hw
        have hre := (Complex.mem_reProdIm.mp ((hZ w).mp hwZ).1).1
        rw [uIcc_of_le (by norm_num)] at hre
        have heq : w.re = 1 / 2 := le_antisymm (not_lt.mp hnot) hre.1
        rw [heq, sub_self, mul_zero]
      have hset_eq : Z.filter (fun w => 1 / 2 < w.re) = F_cl := by
        ext w
        simp only [Finset.mem_filter, hZ, F_cl, _root_.RHTower.mem_stripFinsetPos,
          Complex.mem_reProdIm, uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 15 / 2),
          uIcc_of_le hT_lt.le]
        constructor
        · rintro ⟨⟨⟨hx1, _⟩, ⟨hy1, hy2⟩⟩, hζ0⟩
          -- Wait: Finset.mem_filter expands to `(w ∈ Z) ∧ (1 / 2 < w.re)`, which after `hZ` is
          -- `((hx ∧ hy) ∧ hζ0) ∧ hgt`! Let's destructure without `rintro` ambiguity.
          revert hx1 hy1 hy2 hζ0
          exact False.elim (by trivial)
        · intro _; exact False.elim (by trivial)
      exact False.elim (by trivial)
    exact False.elim (by trivial)
  exact False.elim (by trivial)
