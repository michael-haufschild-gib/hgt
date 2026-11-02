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
  have h := Finset.sum_union_inter (s₁ := s₁) (s₂ := s₂) (f := f)
  linarith [h, Finset.sum_nonneg fun x (_ : x ∈ s₁ ∩ s₂) => hf x]

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
        constructor
        · intro hw
          obtain ⟨hwZ, hgt⟩ := Finset.mem_filter.mp hw
          obtain ⟨hrect, hζ0⟩ := (hZ w).mp hwZ
          obtain ⟨hx, hy⟩ := Complex.mem_reProdIm.mp hrect
          rw [uIcc_of_le (by norm_num)] at hx
          rw [uIcc_of_le hT_lt.le] at hy
          obtain ⟨hx_lo, _⟩ := hx
          obtain ⟨hy_lo, hy_hi⟩ := hy
          obtain ⟨hwF, hre_lt1, hxi0⟩ := hmem_F_of_zeta w hx_lo (by linarith) (by linarith) hζ0
          have hy_ge : T ≤ w.im := by
            by_contra hlt
            push Not at hlt
            have hg := hgap_T w hwF (by linarith)
            rw [abs_of_neg (by linarith)] at hg
            linarith
          have hy_le : w.im ≤ 2 * T := by
            by_contra hgt'
            push Not at hgt'
            have hg := hgap_2T w hwF (by linarith)
            rw [abs_of_pos (by linarith)] at hg
            linarith
          exact Finset.mem_filter.mpr
            ⟨_root_.RHTower.mem_stripFinsetPos.mpr ⟨by linarith, hre_lt1, by linarith, hy_le, hxi0⟩,
              hy_ge, hgt⟩
        · intro hw
          obtain ⟨hwS, hy_ge, hgt⟩ := Finset.mem_filter.mp hw
          obtain ⟨h0, h1, _, hy_le, hxi0⟩ := _root_.RHTower.mem_stripFinsetPos.mp hwS
          have hζ0 : riemannZeta w = 0 :=
            (_root_.RHTower.xi_zero_iff_zeta_zero_of_mem_strip h0 h1).mp hxi0
          refine Finset.mem_filter.mpr ⟨(hZ w).mpr ⟨Complex.mem_reProdIm.mpr ⟨?_, ?_⟩, hζ0⟩, hgt⟩
          · rw [uIcc_of_le (by norm_num)]; exact ⟨hgt.le, by linarith⟩
          · rw [uIcc_of_le hT_lt.le]; exact ⟨by linarith, by linarith⟩
      rw [hsplit, hzero_line, add_zero, hset_eq]
      refine Finset.sum_congr rfl fun w hw => ?_
      obtain ⟨h0, h1, _, _, _⟩ := _root_.RHTower.mem_stripFinsetPos.mp (Finset.mem_filter.mp hw).1
      rw [_root_.RHTower.xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨h0, h1⟩]
    have hb := hbud (T - δ n) (2 * T + δ n) hT₁_20 hT_lt hnz₁ hnz₂ Z hZ
    rwa [hsum_eq] at hb
  -- Pass `n → ∞` along `δ n = δ₀ / (n + 2) → 0`.
  have hδ_zero : Tendsto δ atTop (𝓝 0) := by
    refine Metric.tendsto_atTop.mpr fun ε hε => ?_
    refine ⟨Nat.ceil (δ₀ / ε) + 1, fun n hn => ?_⟩
    have hδ_pos : 0 < δ n := by dsimp only [δ]; positivity
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ_pos]
    dsimp only [δ]
    rw [div_lt_iff₀ (by positivity)]
    have hc : δ₀ / ε ≤ (Nat.ceil (δ₀ / ε) : ℝ) := Nat.le_ceil _
    have hnR : (Nat.ceil (δ₀ / ε) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have h1 : δ₀ ≤ ε * (Nat.ceil (δ₀ / ε) : ℝ) := by
      have := mul_le_mul_of_nonneg_left hc hε.le
      rwa [mul_div_cancel₀ _ hε.ne'] at this
    linarith [h1, mul_le_mul_of_nonneg_left hnR hε.le]
  have hprim : Continuous fun x : ℝ => ∫ t in (0 : ℝ)..x,
      Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ :=
    intervalIntegral.continuous_primitive
      (fun a b => _root_.RHTower.intervalIntegrable_log_norm_riemannZeta_line a b) 0
  have hint_sub : ∀ a b : ℝ,
      (∫ t in a..b, Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) =
        (∫ t in (0 : ℝ)..b, Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) -
          ∫ t in (0 : ℝ)..a, Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ :=
    fun a b => (intervalIntegral.integral_interval_sub_left
      (_root_.RHTower.intervalIntegrable_log_norm_riemannZeta_line 0 b)
      (_root_.RHTower.intervalIntegrable_log_norm_riemannZeta_line 0 a)).symm
  have hT_sub_lim : Tendsto (fun n : ℕ => T - δ n) atTop (𝓝 T) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hδ_zero
  have h2T_add_lim : Tendsto (fun n : ℕ => 2 * T + δ n) atTop (𝓝 (2 * T)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hδ_zero
  have hlhs_lim : Tendsto
      (fun n : ℕ => |(∫ t in (T - δ n)..(2 * T + δ n),
          Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) - 2 * Real.pi * S_cl|)
      atTop
      (𝓝 (|(∫ t in T..(2 * T),
          Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) - 2 * Real.pi * S_cl|)) := by
    have heq : (fun n : ℕ => |(∫ t in (T - δ n)..(2 * T + δ n),
          Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) - 2 * Real.pi * S_cl|) =
        fun n : ℕ => |((∫ t in (0 : ℝ)..(2 * T + δ n),
          Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) -
          ∫ t in (0 : ℝ)..(T - δ n),
          Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) - 2 * Real.pi * S_cl| :=
      funext fun n => by rw [hint_sub]
    rw [heq, hint_sub T (2 * T)]
    exact (((hprim.continuousAt.tendsto.comp h2T_add_lim).sub
      (hprim.continuousAt.tendsto.comp hT_sub_lim)).sub tendsto_const_nhds).abs
  have hrhs_lim : Tendsto (fun n : ℕ => C₀ + K₀ * Real.log (2 * T + δ n)) atTop
      (𝓝 (C₀ + K₀ * Real.log (2 * T))) :=
    tendsto_const_nhds.add
      (tendsto_const_nhds.mul
        ((Real.continuousAt_log (by positivity : (2 * T : ℝ) ≠ 0)).tendsto.comp h2T_add_lim))
  have hcl_bd : |(∫ t in T..(2 * T), Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) -
      2 * Real.pi * S_cl| ≤ C₀ + K₀ * Real.log (2 * T) :=
    le_of_tendsto_of_tendsto hlhs_lim hrhs_lim (Eventually.of_forall hstep)
  -- Separate the boundary slice `z.im = T` from `F_cl` to pass to `shellZeros T (2 * T)`.
  set S_sh : ℝ := ∑ z ∈ (shellZeros T (2 * T)).filter (fun z => 1 / 2 < z.re),
    ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2)
  have hF_gt : F_cl.filter (fun z => T < z.im) =
      (shellZeros T (2 * T)).filter (fun z => 1 / 2 < z.re) := by
    ext z
    simp only [F_cl, shellZeros, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hzS, _, hre⟩, hgt⟩; exact ⟨⟨hzS, hgt⟩, hre⟩
    · rintro ⟨⟨hzS, hgt⟩, hre⟩; exact ⟨⟨hzS, hgt.le, hre⟩, hgt⟩
  have hS_split : S_cl = S_sh +
      ∑ z ∈ F_cl.filter (fun z => ¬ T < z.im),
        ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) := by
    dsimp only [S_cl, S_sh]
    rw [← hF_gt]
    exact (Finset.sum_filter_add_sum_filter_not F_cl (fun z => T < z.im) _).symm
  have hslice_nn : 0 ≤ ∑ z ∈ F_cl.filter (fun z => ¬ T < z.im),
      ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) :=
    Finset.sum_nonneg fun z hz => by
      have hre := (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2.2
      exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have hslice_le : 2 * Real.pi * ∑ z ∈ F_cl.filter (fun z => ¬ T < z.im),
      ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) ≤
      C_slice + 16 * Real.pi * Real.log (2 * T) := by
    have hsub_sh : F_cl.filter (fun z => ¬ T < z.im) ⊆ shellZeros (T - 1) T := by
      intro z hz
      obtain ⟨hzF, hnot⟩ := Finset.mem_filter.mp hz
      obtain ⟨hzS, hy_ge, _⟩ := Finset.mem_filter.mp hzF
      obtain ⟨h0, h1, him0, _, hxi⟩ := _root_.RHTower.mem_stripFinsetPos.mp hzS
      have hy_eq : z.im = T := le_antisymm (not_lt.mp hnot) hy_ge
      exact Finset.mem_filter.mpr
        ⟨_root_.RHTower.mem_stripFinsetPos.mpr ⟨h0, h1, him0, hy_eq.le, hxi⟩, by linarith⟩
    have hsum_half : ∑ z ∈ F_cl.filter (fun z => ¬ T < z.im),
        ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) ≤
        (1 / 2) * ∑ z ∈ shellZeros (T - 1) T,
          ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) := by
      rw [Finset.mul_sum]
      calc ∑ z ∈ F_cl.filter (fun z => ¬ T < z.im),
              ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2)
          ≤ ∑ z ∈ F_cl.filter (fun z => ¬ T < z.im),
              (1 / 2) * ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) := by
            refine Finset.sum_le_sum fun z hz => ?_
            have h1 := (_root_.RHTower.mem_stripFinsetPos.mp
              (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).2.1
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
        _ ≤ ∑ z ∈ shellZeros (T - 1) T,
              (1 / 2) * ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub_sh fun _ _ _ => by positivity
    have hs := shortShell_orderSum_le_log (V₁ := T - 1) (V₂ := T)
      (by linarith) (by linarith) (by linarith)
    have hlog_le : Real.log (T + 4) ≤ Real.log (2 * T) :=
      Real.log_le_log (by linarith) (by linarith)
    have hsum_bd : ∑ z ∈ F_cl.filter (fun z => ¬ T < z.im),
        ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) ≤
        8 * (|_root_.RHTower.xiLineTwoLogDerivConstant| + Real.log (2 * T)) := by
      linarith [hsum_half, hs, hlog_le]
    dsimp only [C_slice]
    have hpi_nn : 0 ≤ 2 * Real.pi := by positivity
    calc 2 * Real.pi * ∑ z ∈ F_cl.filter (fun z => ¬ T < z.im),
            ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2)
        ≤ 2 * Real.pi * (8 * (|_root_.RHTower.xiLineTwoLogDerivConstant| + Real.log (2 * T))) :=
          mul_le_mul_of_nonneg_left hsum_bd hpi_nn
      _ ≤ 16 * Real.pi * (|_root_.RHTower.xiLineTwoLogDerivConstant| + 1) +
            16 * Real.pi * Real.log (2 * T) := by linarith [Real.pi_pos]
  set I_ζ : ℝ := ∫ t in T..(2 * T), Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖
  have htri : |I_ζ - 2 * Real.pi * S_sh| ≤
      |I_ζ - 2 * Real.pi * S_cl| +
        2 * Real.pi * ∑ z ∈ F_cl.filter (fun z => ¬ T < z.im),
          ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) := by
    have heq : I_ζ - 2 * Real.pi * S_sh =
        (I_ζ - 2 * Real.pi * S_cl) +
          2 * Real.pi * ∑ z ∈ F_cl.filter (fun z => ¬ T < z.im),
            ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) := by
      rw [hS_split]; ring
    rw [heq]
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg (mul_nonneg (by positivity) hslice_nn)]
  linarith [htri, hcl_bd, hslice_le]

/-- **Dyadic exponential off-line tail moment (`exists_dyadic_offLineTailMoment_le_exp`).**
For all sufficiently large `T` and all `c ≥ 2`, the off-line horizontal moment of `ξ`-zeros on the
exact dyadic shell `shellZeros T (2 * T)` beyond `1 / 2 + c / log T` is bounded by
`B * exp(-c / 28) * T + K * (log T)²`. -/
theorem exists_dyadic_offLineTailMoment_le_exp :
    ∃ B K : ℝ, 0 ≤ B ∧ 0 ≤ K ∧ ∀ᶠ T in atTop, ∀ c : ℝ, 2 ≤ c →
      ∑ z ∈ (shellZeros T (2 * T)).filter (fun z => 1 / 2 + c / Real.log T ≤ z.re),
          ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) ≤
        B * Real.exp (-(c / 28)) * T + K * (Real.log T) ^ 2 := by
  obtain ⟨B₀, K₀, hB₀, hK₀, hev⟩ := _root_.RHTower.exists_offLineTailMoment_window_le_exp
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp hev
  set K_top : ℝ := 24 * (|_root_.RHTower.xiLineTwoLogDerivConstant| + 4)
  refine ⟨B₀, 4 * K₀ + K_top, hB₀, by dsimp only [K_top]; positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max 25 ((U₀ + 4) / 4))] with T hT_ge c hc2
  have hT25 : 25 ≤ T := (le_max_left _ _).trans hT_ge
  have hU₀_le : U₀ ≤ 4 * T - 4 := by
    have := (le_max_right 25 ((U₀ + 4) / 4)).trans hT_ge
    linarith
  set U : ℝ := 4 * T - 4
  obtain ⟨T₁, hT₁, T₂, hT₂, htail⟩ := hU₀ U hU₀_le
  have hT₁_lo : T - 1 < T₁ := by dsimp only [U] at hT₁; linarith [hT₁.1]
  have hT₁_hi : T₁ < T := by dsimp only [U] at hT₁; linarith [hT₁.2]
  have hT₂_lo : 2 * T - 3 < T₂ := by dsimp only [U] at hT₂; linarith [hT₂.1]
  have hT₂_hi : T₂ < 2 * T - 2 := by dsimp only [U] at hT₂; linarith [hT₂.2]
  have hT₁_20 : 20 ≤ T₁ := by linarith
  have hT_lt : T₁ < T₂ := by linarith
  obtain ⟨Z, hZ⟩ := _root_.RHTower.exists_zetaRectangleZeros_finset hT₁_20 hT_lt
  have hlogT_ge2 : 2 ≤ Real.log T := by
    have hlog8 : 2 ≤ Real.log 8 := by
      have : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num, Real.log_pow]; norm_num
      linarith [Real.log_two_gt_d9]
    exact hlog8.trans (Real.log_le_log (by norm_num) (by linarith))
  have hlogT_pos : 0 < Real.log T := by linarith
  have hT_lt_U : T < U := by dsimp only [U]; linarith
  have hlogT_le_U : Real.log T ≤ Real.log U := Real.log_le_log (by linarith) hT_lt_U.le
  have hlogU_le_2logT : Real.log U ≤ 2 * Real.log T := by
    calc Real.log U ≤ Real.log (4 * T) := Real.log_le_log (by linarith) (by dsimp only [U]; linarith)
      _ = Real.log 4 + Real.log T := Real.log_mul (by norm_num) (by linarith)
      _ ≤ 2 + Real.log T := by linarith [log_four_le_two]
      _ ≤ 2 * Real.log T := by linarith
  set F_c : Finset ℂ := (shellZeros T (2 * T)).filter (fun z => 1 / 2 + c / Real.log T ≤ z.re)
  have hsplit := (Finset.sum_filter_add_sum_filter_not F_c (fun z => z.im ≤ T₂)
    (fun z => ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2))).symm
  -- Zeros in `F_c` with `z.im ≤ T₂` embed into `Z.filter (1/2 + c / log U ≤ w.re)`.
  have hmain_le : ∑ z ∈ F_c.filter (fun z => z.im ≤ T₂),
      ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) ≤
      B₀ * Real.exp (-(c / 28)) * T + 4 * K₀ * (Real.log T) ^ 2 := by
    have hsub_Z : F_c.filter (fun z => z.im ≤ T₂) ⊆
        Z.filter (fun w => 1 / 2 + c / Real.log U ≤ w.re) := by
      intro z hz
      obtain ⟨hzFc, him_T₂⟩ := Finset.mem_filter.mp hz
      obtain ⟨hzSh, hre_c⟩ := Finset.mem_filter.mp hzFc
      obtain ⟨hzS, him_T⟩ := Finset.mem_filter.mp hzSh
      obtain ⟨h0, h1, _, _, hxi0⟩ := _root_.RHTower.mem_stripFinsetPos.mp hzS
      have hζ0 : riemannZeta z = 0 :=
        (_root_.RHTower.xi_zero_iff_zeta_zero_of_mem_strip h0 h1).mp hxi0
      have hc_div : c / Real.log U ≤ c / Real.log T :=
        div_le_div_of_nonneg_left (by linarith) hlogT_pos hlogT_le_U
      refine Finset.mem_filter.mpr
        ⟨(hZ z).mpr ⟨Complex.mem_reProdIm.mpr ⟨?_, ?_⟩, hζ0⟩, by linarith⟩
      · rw [uIcc_of_le (by norm_num)]
        exact ⟨by linarith [div_nonneg (by linarith : 0 ≤ c) hlogT_pos.le], by linarith⟩
      · rw [uIcc_of_le hT_lt.le]; exact ⟨by linarith, him_T₂⟩
    have hsum_Z : ∑ z ∈ F_c.filter (fun z => z.im ≤ T₂),
        ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) ≤
        ∑ w ∈ Z.filter (fun w => 1 / 2 + c / Real.log U ≤ w.re),
          ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2) := by
      have heq_ord : ∑ z ∈ F_c.filter (fun z => z.im ≤ T₂),
          ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) =
          ∑ z ∈ F_c.filter (fun z => z.im ≤ T₂),
            ((analyticOrderAt riemannZeta z).toNat : ℝ) * (z.re - 1 / 2) := by
        refine Finset.sum_congr rfl fun z hz => ?_
        obtain ⟨h0, h1, _, _, _⟩ := _root_.RHTower.mem_stripFinsetPos.mp
          (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).1
        rw [_root_.RHTower.xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨h0, h1⟩]
      rw [heq_ord]
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub_Z fun w hw _ => ?_
      have hre := (Finset.mem_filter.mp hw).2
      have hdiv_nn : 0 ≤ c / Real.log U :=
        div_nonneg (by linarith) (hlogT_pos.trans_le hlogT_le_U).le
      exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
    have hbd := htail Z hZ c hc2
    have hlen_le : T₂ - T₁ ≤ T := by linarith
    have hlogU_sq : (Real.log U) ^ 2 ≤ 4 * (Real.log T) ^ 2 := by
      have hnn : 0 ≤ Real.log U := (hlogT_pos.trans_le hlogT_le_U).le
      calc (Real.log U) ^ 2 ≤ (2 * Real.log T) ^ 2 := pow_le_pow_left₀ hnn hlogU_le_2logT 2
        _ = 4 * (Real.log T) ^ 2 := by ring
    calc ∑ z ∈ F_c.filter (fun z => z.im ≤ T₂),
            ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2)
        ≤ B₀ * Real.exp (-(c / 28)) * (T₂ - T₁) + K₀ * (Real.log U) ^ 2 := hsum_Z.trans hbd
      _ ≤ B₀ * Real.exp (-(c / 28)) * T + 4 * K₀ * (Real.log T) ^ 2 := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_left hlen_le (mul_nonneg hB₀ (Real.exp_pos _).le)
          · calc K₀ * (Real.log U) ^ 2 ≤ K₀ * (4 * (Real.log T) ^ 2) :=
                mul_le_mul_of_nonneg_left hlogU_sq hK₀
              _ = 4 * K₀ * (Real.log T) ^ 2 := by ring
  -- Zeros in `F_c` with `T₂ < z.im` lie in `(2T - 3, 2T]` and contribute `O(log T) ≤ K_top (log T)²`.
  have htop_le : ∑ z ∈ F_c.filter (fun z => ¬ z.im ≤ T₂),
      ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) ≤
      K_top * (Real.log T) ^ 2 := by
    have hsub_3 : F_c.filter (fun z => ¬ z.im ≤ T₂) ⊆
        shellZeros (2 * T - 3) (2 * T - 2) ∪
          (shellZeros (2 * T - 2) (2 * T - 1) ∪ shellZeros (2 * T - 1) (2 * T)) := by
      intro z hz
      obtain ⟨hzFc, hnot⟩ := Finset.mem_filter.mp hz
      obtain ⟨hzS, _⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hzFc).1
      obtain ⟨h0, h1, him0, him2T, hxi⟩ := _root_.RHTower.mem_stripFinsetPos.mp hzS
      have him_gt : 2 * T - 3 < z.im := lt_trans hT₂_lo (not_le.mp hnot)
      rcases le_or_gt z.im (2 * T - 2) with hle1 | hgt1
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
          ⟨_root_.RHTower.mem_stripFinsetPos.mpr ⟨h0, h1, him0, hle1, hxi⟩, him_gt⟩))
      · rcases le_or_gt z.im (2 * T - 1) with hle2 | hgt2
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
            ⟨_root_.RHTower.mem_stripFinsetPos.mpr ⟨h0, h1, him0, hle2, hxi⟩, hgt1⟩))))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
            ⟨hzS, hgt2⟩))))
    have hs1 := shortShell_orderSum_le_log (V₁ := 2 * T - 3) (V₂ := 2 * T - 2)
      (by linarith) (by linarith) (by linarith)
    have hs2 := shortShell_orderSum_le_log (V₁ := 2 * T - 2) (V₂ := 2 * T - 1)
      (by linarith) (by linarith) (by linarith)
    have hs3 := shortShell_orderSum_le_log (V₁ := 2 * T - 1) (V₂ := 2 * T)
      (by linarith) (by linarith) (by linarith)
    have hlog2T4 : Real.log (2 * T + 4) ≤ 2 * Real.log T := by
      calc Real.log (2 * T + 4) ≤ Real.log (4 * T) := Real.log_le_log (by linarith) (by linarith)
        _ = Real.log 4 + Real.log T := Real.log_mul (by norm_num) (by linarith)
        _ ≤ 2 * Real.log T := by linarith [log_four_le_two, hlogT_ge2]
    have hl1 : Real.log (2 * T - 2 + 4) ≤ 2 * Real.log T :=
      (Real.log_le_log (by linarith) (by linarith)).trans hlog2T4
    have hl2 : Real.log (2 * T - 1 + 4) ≤ 2 * Real.log T :=
      (Real.log_le_log (by linarith) (by linarith)).trans hlog2T4
    have hsum_3 : ∑ z ∈ F_c.filter (fun z => ¬ z.im ≤ T₂),
        ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) ≤
        (1 / 2) * (∑ z ∈ shellZeros (2 * T - 3) (2 * T - 2),
            ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) +
          (∑ z ∈ shellZeros (2 * T - 2) (2 * T - 1),
            ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) +
          ∑ z ∈ shellZeros (2 * T - 1) (2 * T),
            ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ))) := by
      have hhalf : ∑ z ∈ F_c.filter (fun z => ¬ z.im ≤ T₂),
          ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) ≤
          ∑ z ∈ F_c.filter (fun z => ¬ z.im ≤ T₂),
            (1 / 2) * ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) := by
        refine Finset.sum_le_sum fun z hz => ?_
        have h1 := (_root_.RHTower.mem_stripFinsetPos.mp
          (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).1).2.1
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
      rw [← Finset.mul_sum] at hhalf
      refine hhalf.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsub_3 fun _ _ _ => Nat.cast_nonneg _).trans
        ((finset_sum_union_le _ _ fun _ => Nat.cast_nonneg _).trans
          (add_le_add le_rfl (finset_sum_union_le _ _ fun _ => Nat.cast_nonneg _)))
    have hlin_bd : ∑ z ∈ F_c.filter (fun z => ¬ z.im ≤ T₂),
        ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) ≤
        24 * (|_root_.RHTower.xiLineTwoLogDerivConstant| + 2 * Real.log T) := by
      linarith [hsum_3, hs1, hs2, hs3, hl1, hl2, hlog2T4]
    have hC_sq : |_root_.RHTower.xiLineTwoLogDerivConstant| + 2 * Real.log T ≤
        (|_root_.RHTower.xiLineTwoLogDerivConstant| + 4) * (Real.log T) ^ 2 := by
      have hsq_ge4 : 4 ≤ (Real.log T) ^ 2 := by
        calc (4 : ℝ) = 2 ^ 2 := by norm_num
          _ ≤ (Real.log T) ^ 2 := pow_le_pow_left₀ zero_le_two hlogT_ge2 2
      have hsq_ge_log : 2 * Real.log T ≤ 2 * (Real.log T) ^ 2 := by
        have h1 : Real.log T ≤ (Real.log T) ^ 2 := by
          rw [sq]
          exact le_mul_of_one_le_left hlogT_pos.le (by linarith)
        linarith
      have hC_nn : 0 ≤ |_root_.RHTower.xiLineTwoLogDerivConstant| := abs_nonneg _
      have hC_le : |_root_.RHTower.xiLineTwoLogDerivConstant| ≤
          |_root_.RHTower.xiLineTwoLogDerivConstant| * (Real.log T) ^ 2 :=
        le_mul_of_one_le_right hC_nn (by linarith)
      linarith
    dsimp only [K_top]
    linarith [mul_le_mul_of_nonneg_left hC_sq (by norm_num : (0 : ℝ) ≤ 24)]
  rw [hsplit]
  calc ∑ z ∈ F_c.filter (fun z => z.im ≤ T₂),
          ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) +
        ∑ z ∈ F_c.filter (fun z => ¬ z.im ≤ T₂),
          ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2)
      ≤ (B₀ * Real.exp (-(c / 28)) * T + 4 * K₀ * (Real.log T) ^ 2) + K_top * (Real.log T) ^ 2 :=
        add_le_add hmain_le htop_le
    _ = B₀ * Real.exp (-(c / 28)) * T + (4 * K₀ + K_top) * (Real.log T) ^ 2 := by ring


/-! ## §3. Truncated Euler-product outer mollifier log-mean via Cauchy's theorem -/

/-- Truncated Euler-product outer mollifier `M_S(s) = ∏_{p ∈ S, Prime p} (1 - p^{-s})`. -/
def eulerProductMollifier (S : Finset ℕ) (s : ℂ) : ℂ :=
  _root_.RHTower.eulerHeadAnchor (S.filter Nat.Prime) s

/-- `M_S(s)` is entire and nonvanishing throughout the open right half-plane `Re s > 0`. -/
theorem eulerProductMollifier_ne_zero (S : Finset ℕ) {s : ℂ} (hs : 0 < s.re) :
    eulerProductMollifier S s ≠ 0 :=
  _root_.RHTower.eulerHeadAnchor_ne_zero
    (fun _ hp => (Finset.mem_filter.mp hp).2.two_le) hs

theorem differentiable_eulerProductMollifier (S : Finset ℕ) :
    Differentiable ℂ (eulerProductMollifier S) :=
  _root_.RHTower.differentiable_eulerHeadAnchor
    (fun _ hp => (Finset.mem_filter.mp hp).2.two_le)

private lemma single_prime_logIntegral_le {p : ℕ} (hp : Nat.Prime p) {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    |∫ t in T₁..T₂, Real.log ‖(1 : ℂ) - (p : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖| ≤
      3 + 6 / Real.log p := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hlogp_pos : 0 < Real.log p := Real.log_pos hp_gt1
  have hp_ne0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  set h_p : ℂ → ℂ := fun s => Complex.log (1 - (p : ℂ) ^ (-s))
  set U : Set ℂ := {s : ℂ | 1 / 4 < s.re}
  have hnorm_cpow : ∀ z : ℂ, ‖(p : ℂ) ^ (-z)‖ = (p : ℝ) ^ (-z.re) := fun z => by
    rw [show (p : ℂ) = ((p : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hp_pos, Complex.neg_re]
  have hslit : ∀ s ∈ U, (1 : ℂ) - (p : ℂ) ^ (-s) ∈ Complex.slitPlane := fun s hs => by
    have hs_re : 1 / 4 < s.re := hs
    have hlt1 : ‖(p : ℂ) ^ (-s)‖ < 1 := by
      rw [hnorm_cpow]
      exact Real.rpow_lt_one_of_one_lt_of_neg hp_gt1 (by linarith)
    have hre_le : ((p : ℂ) ^ (-s)).re ≤ ‖(p : ℂ) ^ (-s)‖ := Complex.re_le_norm _
    exact Complex.mem_slitPlane_iff.mpr
      (Or.inl (by simp only [Complex.sub_re, Complex.one_re]; linarith))
  have hdiff_fac : ∀ s : ℂ, DifferentiableAt ℂ (fun z : ℂ => (1 : ℂ) - (p : ℂ) ^ (-z)) s :=
    fun s => (((hasDerivAt_id s).neg.const_cpow (Or.inl hp_ne0)).const_sub 1).differentiableAt
  have hdiffOn : DifferentiableOn ℂ h_p U := fun s hs =>
    (DifferentiableAt.comp (g := Complex.log) (f := fun z : ℂ => (1 : ℂ) - (p : ℂ) ^ (-z)) s
      (Complex.hasDerivAt_log (hslit s hs)).differentiableAt (hdiff_fac s)).differentiableWithinAt
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hanOn : AnalyticOnNhd ℂ h_p U := hdiffOn.analyticOnNhd hU_open
  -- Pointwise norm bound `‖h_p s‖ ≤ 3 * exp(-log p * s.re)` on `s.re ≥ 1/2`.
  have h2_rpow : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 / 4 := by
    rw [Real.rpow_neg zero_le_two]
    have h1 : (4 / 3 : ℝ) ≤ (2 : ℝ) ^ (1 / 2 : ℝ) := by
      have hsq : ((4 / 3 : ℝ)) ^ (2 : ℕ) ≤ ((2 : ℝ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ) := by
        rw [← Real.rpow_natCast ((2 : ℝ) ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul zero_le_two]
        norm_num
      exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq
    exact (inv_le_comm₀ (by positivity) (by norm_num)).mpr (by linarith)
  have hnorm_hp : ∀ s : ℂ, 1 / 2 ≤ s.re → ‖h_p s‖ ≤ 3 * Real.exp (-Real.log p * s.re) := by
    intro s hs_half
    set w : ℂ := -(p : ℂ) ^ (-s)
    have hw_norm : ‖w‖ = (p : ℝ) ^ (-s.re) := by rw [norm_neg, hnorm_cpow]
    have hw_34 : ‖w‖ ≤ 3 / 4 := by
      rw [hw_norm]
      have h1 : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hp_gt1.le (by linarith)
      have h2 : (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [Real.rpow_neg hp_pos.le, Real.rpow_neg zero_le_two]
        exact inv_anti₀ (by positivity)
          (Real.rpow_le_rpow zero_le_two (by exact_mod_cast hp.two_le) (by norm_num))
      exact (h1.trans h2).trans h2_rpow
    have hlog_bd := Complex.norm_log_one_add_le (z := w) (by linarith)
    have hinv_le : (1 - ‖w‖)⁻¹ ≤ 4 :=
      (inv_le_comm₀ (by linarith) (by norm_num)).mpr (by linarith)
    have hw_nn : 0 ≤ ‖w‖ := norm_nonneg w
    have hquad : ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ ≤ 3 * ‖w‖ := by
      calc ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ ≤ ‖w‖ ^ 2 * 4 :=
            mul_le_mul_of_nonneg_left hinv_le (sq_nonneg _)
        _ = (4 * ‖w‖) * ‖w‖ := by ring
        _ ≤ 3 * ‖w‖ := mul_le_mul_of_nonneg_right (by linarith) hw_nn
    have h3w : ‖h_p s‖ ≤ 3 * ‖w‖ := by
      have heq : h_p s = Complex.log (1 + w) := by dsimp only [h_p, w]; rw [sub_eq_add_neg]
      rw [heq]
      linarith [hlog_bd, hquad]
    have hexp_eq : (p : ℝ) ^ (-s.re) = Real.exp (-Real.log p * s.re) := by
      rw [Real.rpow_def_of_pos hp_pos]; congr 1; ring
    rwa [hw_norm, hexp_eq] at h3w
  -- Apply Cauchy's theorem on `[1/2, R] × [T₁, T₂]`.
  set R : ℝ := 1 + Real.log (T₂ - T₁ + 1) / Real.log p
  have hlog_len_nn : 0 ≤ Real.log (T₂ - T₁ + 1) := Real.log_nonneg (by linarith)
  have hR_ge1 : 1 ≤ R := by dsimp only [R]; linarith [div_nonneg hlog_len_nn hlogp_pos.le]
  have hR_half : (1 / 2 : ℝ) ≤ R := by linarith
  set z₁ : ℂ := ((1 / 2 : ℝ) : ℂ) + (T₁ : ℂ) * I
  set z₂ : ℂ := (R : ℂ) + (T₂ : ℂ) * I
  have hz₁_re : z₁.re = 1 / 2 := by simp [z₁]
  have hz₁_im : z₁.im = T₁ := by simp [z₁]
  have hz₂_re : z₂.re = R := by simp [z₂]
  have hz₂_im : z₂.im = T₂ := by simp [z₂]
  have hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U := by
    rw [hz₁_re, hz₂_re, hz₁_im, hz₂_im, uIcc_of_le hR_half, uIcc_of_le hT]
    intro s hs
    show (1 / 4 : ℝ) < s.re
    linarith [hs.1.1]
  have hrect0 : _root_.RHTower.rectIntegral h_p z₁ z₂ = 0 :=
    _root_.RHTower.rectIntegral_eq_zero_of_analyticOnNhd hsub hanOn
  have hcont_horiz : ∀ y : ℝ, ContinuousOn (fun x : ℝ => h_p ((x : ℂ) + (y : ℂ) * I))
      (Icc (1 / 2) R) := fun y x hx => by
    have hsU : ((x : ℂ) + (y : ℂ) * I) ∈ U := by
      show (1 / 4 : ℝ) < ((x : ℂ) + (y : ℂ) * I).re
      simp; linarith [hx.1]
    have h1 : ContinuousAt h_p ((x : ℂ) + (y : ℂ) * I) := (hanOn _ hsU).continuousAt
    have h2 : ContinuousAt (fun u : ℝ => (u : ℂ) + (y : ℂ) * I) x :=
      (by fun_prop : Continuous fun u : ℝ => (u : ℂ) + (y : ℂ) * I).continuousAt
    exact (ContinuousAt.comp (g := h_p)
      (f := fun u : ℝ => (u : ℂ) + (y : ℂ) * I) h1 h2).continuousWithinAt
  have hcont_vert : ∀ x : ℝ, 1 / 2 ≤ x → ContinuousOn (fun y : ℝ => h_p ((x : ℂ) + (y : ℂ) * I))
      (Icc T₁ T₂) := fun x hx y _ => by
    have hsU : ((x : ℂ) + (y : ℂ) * I) ∈ U := by
      show (1 / 4 : ℝ) < ((x : ℂ) + (y : ℂ) * I).re
      simp; linarith
    have h1 : ContinuousAt h_p ((x : ℂ) + (y : ℂ) * I) := (hanOn _ hsU).continuousAt
    have h2 : ContinuousAt (fun u : ℝ => (x : ℂ) + (u : ℂ) * I) y :=
      (by fun_prop : Continuous fun u : ℝ => (x : ℂ) + (u : ℂ) * I).continuousAt
    exact (ContinuousAt.comp (g := h_p)
      (f := fun u : ℝ => (x : ℂ) + (u : ℂ) * I) h1 h2).continuousWithinAt
  have him_edges := _root_.RHTower.im_rectIntegral h_p z₁ z₂
    (by rw [hz₁_re, hz₂_re, hz₁_im]; exact (hcont_horiz T₁).intervalIntegrable_of_Icc hR_half)
    (by rw [hz₁_re, hz₂_re, hz₂_im]; exact (hcont_horiz T₂).intervalIntegrable_of_Icc hR_half)
    (by rw [hz₂_re, hz₁_im, hz₂_im]; exact (hcont_vert R hR_half).intervalIntegrable_of_Icc hT)
    (by rw [hz₁_re, hz₁_im, hz₂_im]; exact (hcont_vert (1 / 2) le_rfl).intervalIntegrable_of_Icc hT)
  rw [hrect0, Complex.zero_im, hz₁_re, hz₂_re, hz₁_im, hz₂_im] at him_edges
  have hleft_eq : (∫ y in T₁..T₂, (h_p (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)).re) =
      (∫ x in (1 / 2 : ℝ)..R, (h_p ((x : ℂ) + (T₁ : ℂ) * I)).im) -
        (∫ x in (1 / 2 : ℝ)..R, (h_p ((x : ℂ) + (T₂ : ℂ) * I)).im) +
        ∫ y in T₁..T₂, (h_p ((R : ℂ) + (y : ℂ) * I)).re := by
    linarith [him_edges]
  -- Bound each horizontal edge by `3 / log p`.
  have hhoriz_bd : ∀ y : ℝ,
      |∫ x in (1 / 2 : ℝ)..R, (h_p ((x : ℂ) + (y : ℂ) * I)).im| ≤ 3 / Real.log p := by
    intro y
    have hnorm_int : ‖∫ x in (1 / 2 : ℝ)..R, (h_p ((x : ℂ) + (y : ℂ) * I)).im‖ ≤
        ∫ x in (1 / 2 : ℝ)..R, 3 * Real.exp (-Real.log p * x) := by
      refine intervalIntegral.norm_integral_le_of_norm_le hR_half ?_
        ((by fun_prop : Continuous fun x : ℝ => 3 * Real.exp (-Real.log p * x)).intervalIntegrable _ _)
      refine ae_of_all _ fun x hx => ?_
      rw [Real.norm_eq_abs]
      have hre_x : (((x : ℂ) + (y : ℂ) * I)).re = x := by simp
      calc |(h_p ((x : ℂ) + (y : ℂ) * I)).im|
          ≤ ‖h_p ((x : ℂ) + (y : ℂ) * I)‖ := Complex.abs_im_le_norm _
        _ ≤ 3 * Real.exp (-Real.log p * x) :=
            (hnorm_hp ((x : ℂ) + (y : ℂ) * I) (by rw [hre_x]; exact hx.1.le)).trans_eq
              (by rw [hre_x])
    rw [Real.norm_eq_abs] at hnorm_int
    have hftc : ∫ x in (1 / 2 : ℝ)..R, 3 * Real.exp (-Real.log p * x) =
        (-(3 / Real.log p) * Real.exp (-Real.log p * R)) -
          (-(3 / Real.log p) * Real.exp (-Real.log p * (1 / 2))) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun x : ℝ => -(3 / Real.log p) * Real.exp (-Real.log p * x))
        (f' := fun x : ℝ => 3 * Real.exp (-Real.log p * x))
        (fun x _ => ?_)
        ((by fun_prop : Continuous fun x : ℝ => 3 * Real.exp (-Real.log p * x)).intervalIntegrable _ _)
      have hd := (((hasDerivAt_id x).const_mul (-Real.log p)).exp).const_mul (-(3 / Real.log p))
      convert hd using 1
      field_simp [hlogp_pos.ne']
      ring
    have hexp_half_le : Real.exp (-Real.log p * (1 / 2)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    have hexp_R_pos : 0 < Real.exp (-Real.log p * R) := Real.exp_pos _
    have hint_le : ∫ x in (1 / 2 : ℝ)..R, 3 * Real.exp (-Real.log p * x) ≤ 3 / Real.log p := by
      rw [hftc]
      have h1 : (3 / Real.log p) * Real.exp (-Real.log p * (1 / 2)) ≤ 3 / Real.log p :=
        mul_le_of_le_one_right (by positivity) hexp_half_le
      have h2 : 0 ≤ (3 / Real.log p) * Real.exp (-Real.log p * R) := by positivity
      linarith
    exact hnorm_int.trans hint_le
  -- Bound the right vertical edge by `3`.
  have hright_bd : |∫ y in T₁..T₂, (h_p ((R : ℂ) + (y : ℂ) * I)).re| ≤ 3 := by
    have hnorm_int : ‖∫ y in T₁..T₂, (h_p ((R : ℂ) + (y : ℂ) * I)).re‖ ≤
        (3 * Real.exp (-Real.log p * R)) * |T₂ - T₁| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const' hT fun y _ => ?_
      rw [Real.norm_eq_abs]
      have hre_R : (((R : ℂ) + (y : ℂ) * I)).re = R := by simp
      exact (Complex.abs_re_le_norm _).trans
        ((hnorm_hp ((R : ℂ) + (y : ℂ) * I) (by rw [hre_R]; exact hR_half)).trans_eq
          (by rw [hre_R]))
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hT)] at hnorm_int
    have hexp_R_le : Real.exp (-Real.log p * R) ≤ (T₂ - T₁ + 1)⁻¹ := by
      have hmul_R : -Real.log p * R = -Real.log p - Real.log (T₂ - T₁ + 1) := by
        dsimp only [R]; field_simp [hlogp_pos.ne']; ring
      have hle_exp : Real.exp (-Real.log p * R) ≤ Real.exp (-Real.log (T₂ - T₁ + 1)) :=
        Real.exp_le_exp.mpr (by linarith [hmul_R, hlogp_pos])
      rwa [Real.exp_neg, Real.exp_log (by linarith)] at hle_exp
    calc |∫ y in T₁..T₂, (h_p ((R : ℂ) + (y : ℂ) * I)).re|
        ≤ (3 * Real.exp (-Real.log p * R)) * (T₂ - T₁) := hnorm_int
      _ ≤ (3 * (T₂ - T₁ + 1)⁻¹) * (T₂ - T₁) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp_R_le (by norm_num))
            (sub_nonneg.mpr hT)
      _ ≤ (3 * (T₂ - T₁ + 1)⁻¹) * (T₂ - T₁ + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 3 := by field_simp [show T₂ - T₁ + 1 ≠ 0 by linarith]
  have hlog_re : (fun t : ℝ => Real.log ‖(1 : ℂ) - (p : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖) =
      fun t : ℝ => (h_p (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re :=
    funext fun t => (Complex.log_re _).symm
  rw [hlog_re, hleft_eq]
  have htri : |(∫ x in (1 / 2 : ℝ)..R, (h_p ((x : ℂ) + (T₁ : ℂ) * I)).im) -
        (∫ x in (1 / 2 : ℝ)..R, (h_p ((x : ℂ) + (T₂ : ℂ) * I)).im) +
        ∫ y in T₁..T₂, (h_p ((R : ℂ) + (y : ℂ) * I)).re| ≤
      |∫ x in (1 / 2 : ℝ)..R, (h_p ((x : ℂ) + (T₁ : ℂ) * I)).im| +
        |∫ x in (1 / 2 : ℝ)..R, (h_p ((x : ℂ) + (T₂ : ℂ) * I)).im| +
        |∫ y in T₁..T₂, (h_p ((R : ℂ) + (y : ℂ) * I)).re| := by
    exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
  have h6 : 3 / Real.log p + 3 / Real.log p + 3 = 3 + 6 / Real.log p := by ring
  linarith [htri, hhoriz_bd T₁, hhoriz_bd T₂, hright_bd, h6]

private lemma log_norm_eulerHeadAnchor_eq_sum {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p)
    {s : ℂ} (hs : 0 < s.re) :
    Real.log ‖_root_.RHTower.eulerHeadAnchor P s‖ =
      ∑ p ∈ P, Real.log ‖(1 : ℂ) - (p : ℂ) ^ (-s)‖ := by
  induction P using Finset.induction_on with
  | empty => simp [_root_.RHTower.eulerHeadAnchor]
  | @insert p P hp_not ih =>
    have hp2 : 2 ≤ p := hP p (Finset.mem_insert_self p P)
    have hP' : ∀ q ∈ P, 2 ≤ q := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have h1 : (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := _root_.RHTower.eulerFactor_ne_zero hp2 hs
    have h2 : _root_.RHTower.eulerHeadAnchor P s ≠ 0 :=
      _root_.RHTower.eulerHeadAnchor_ne_zero hP' hs
    unfold _root_.RHTower.eulerHeadAnchor at ih h2 ⊢
    rw [Finset.prod_insert hp_not, Finset.sum_insert hp_not, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h2), ih hP']

/-- **Uniform height-independent log-integral bound for the truncated Euler-product mollifier.**
For every finite set `S : Finset ℕ` and every interval `T₁ ≤ T₂`,
`|∫_{T₁}^{T₂} log ‖M_S(1/2 + it)‖ dt| ≤ ∑_{p ∈ S, Prime p} (3 + 6 / log p)`. -/
theorem exists_abs_window_logIntegral_eulerProductMollifier_le (S : Finset ℕ)
    {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    |∫ t in T₁..T₂, Real.log ‖eulerProductMollifier S (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖| ≤
      ∑ p ∈ S.filter Nat.Prime, (3 + 6 / Real.log p) := by
  have heq : (fun t : ℝ => Real.log ‖eulerProductMollifier S (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) =
      fun t : ℝ => ∑ p ∈ S.filter Nat.Prime,
        Real.log ‖(1 : ℂ) - (p : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ := by
    funext t
    exact log_norm_eulerHeadAnchor_eq_sum
      (fun _ hp => (Finset.mem_filter.mp hp).2.two_le) (by simp)
  have hint_fac : ∀ p ∈ S.filter Nat.Prime,
      IntervalIntegrable
        (fun t : ℝ => Real.log ‖(1 : ℂ) - (p : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖)
        volume T₁ T₂ := by
    intro p hp
    have hp_prime := (Finset.mem_filter.mp hp).2
    have hp_ne0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp_prime.ne_zero
    have hcont_fac : Continuous (fun t : ℝ =>
        (1 : ℂ) - (p : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))) := by
      have hdiff : Differentiable ℂ (fun s : ℂ => (1 : ℂ) - (p : ℂ) ^ (-s)) :=
        fun s => (((hasDerivAt_id s).neg.const_cpow (Or.inl hp_ne0)).const_sub 1).differentiableAt
      exact hdiff.continuous.comp (by fun_prop)
    have hcont : Continuous (fun t : ℝ =>
        Real.log ‖(1 : ℂ) - (p : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖) :=
      continuous_iff_continuousAt.mpr fun t =>
        (Real.continuousAt_log (norm_ne_zero_iff.mpr
          (_root_.RHTower.eulerFactor_ne_zero hp_prime.two_le (by simp)))).comp
          hcont_fac.norm.continuousAt
    exact hcont.intervalIntegrable _ _
  rw [heq, intervalIntegral.integral_finsetSum hint_fac]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun p hp => single_prime_logIntegral_le (Finset.mem_filter.mp hp).2 hT)

/-- **Vanishing dyadic log-mean of the truncated Euler-product mollifier.** -/
theorem tendsto_window_logMean_eulerProductMollifier_zero (S : Finset ℕ) :
    Tendsto (fun T : ℝ =>
        T⁻¹ * ∫ t in T..(2 * T),
          Real.log ‖eulerProductMollifier S (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
      atTop (𝓝 0) := by
  set B : ℝ := ∑ p ∈ S.filter Nat.Prime, (3 + 6 / Real.log p)
  have hB_nn : 0 ≤ B := Finset.sum_nonneg fun p hp => by
    have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
    have := Real.log_pos hp_gt1
    positivity
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  refine ⟨max 1 ((B + 1) / ε), fun T hT => ?_⟩
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
  have hTB : (B + 1) / ε ≤ T := (le_max_right _ _).trans hT
  have hT_pos : 0 < T := zero_lt_one.trans_le hT1
  rw [Real.dist_eq, sub_zero, abs_mul, abs_inv, abs_of_pos hT_pos]
  have hbd := exists_abs_window_logIntegral_eulerProductMollifier_le S (T₁ := T) (T₂ := 2 * T)
    (by linarith)
  have h1 : T⁻¹ * |∫ t in T..(2 * T),
      Real.log ‖eulerProductMollifier S (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖| ≤ B / T := by
    rw [div_eq_inv_mul B T]
    exact mul_le_mul_of_nonneg_left hbd (inv_nonneg.mpr hT_pos.le)
  have h2 : B / T < ε := by
    rw [div_lt_iff₀ hT_pos]
    have := (div_le_iff₀ hε).mp hTB
    linarith
  exact h1.trans_lt h2


/-! ## §4. The 8-way unconditional equivalence (`criticalClustering_logMean_mollifier_hecke_tfae`) -/

private lemma integral_log_norm_zeta_mul_eulerProductMollifier (S : Finset ℕ)
    {T₁ T₂ : ℝ} (h20 : 20 ≤ T₁) (hT : T₁ < T₂) :
    (∫ t in T₁..T₂, Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        eulerProductMollifier S (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) =
      (∫ t in T₁..T₂, Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) +
        ∫ t in T₁..T₂, Real.log ‖eulerProductMollifier S (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  have hcont_M : Continuous (fun t : ℝ =>
      Real.log ‖eulerProductMollifier S (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) := by
    have h1 : Continuous (fun t : ℝ => eulerProductMollifier S (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) :=
      (differentiable_eulerProductMollifier S).continuous.comp (by fun_prop)
    exact continuous_iff_continuousAt.mpr fun t =>
      (Real.continuousAt_log (norm_ne_zero_iff.mpr
        (eulerProductMollifier_ne_zero S (by simp)))).comp h1.norm.continuousAt
  rw [← intervalIntegral.integral_add
    (_root_.RHTower.intervalIntegrable_log_norm_riemannZeta_line T₁ T₂)
    (hcont_M.intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr_ae
  have hnull := (_root_.RHTower.finite_zetaLine_zeros h20 hT).measure_zero volume
  rw [MeasureTheory.measure_eq_zero_iff_ae_notMem] at hnull
  filter_upwards [hnull] with t ht hmem
  have hIcc : t ∈ Icc T₁ T₂ := by
    rw [uIoc_of_le hT.le] at hmem
    exact ⟨hmem.1.le, hmem.2⟩
  have hζ0 : riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := fun h => ht ⟨hIcc, h⟩
  have hM0 : eulerProductMollifier S (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 :=
    eulerProductMollifier_ne_zero S (by simp)
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hζ0) (norm_ne_zero_iff.mpr hM0)]

private lemma tendsto_const_add_log_two_mul_div_zero (C K : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K) :
    Tendsto (fun T : ℝ => (C + K * Real.log (2 * T)) / T) atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  set A : ℝ := C + 4 * K + 1
  have hA_pos : 0 < A := by dsimp only [A]; positivity
  refine ⟨max 2 ((2 * A / ε) ^ 2 + 1), fun T hT => ?_⟩
  have hT2 : 2 ≤ T := (le_max_left _ _).trans hT
  have hT_sq : (2 * A / ε) ^ 2 + 1 ≤ T := (le_max_right _ _).trans hT
  have hT_pos : 0 < T := by linarith
  have hnn : 0 ≤ (C + K * Real.log (2 * T)) / T :=
    div_nonneg (add_nonneg hC (mul_nonneg hK (Real.log_nonneg (by linarith)))) hT_pos.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  have hlog_rt : Real.log (2 * T) ≤ 4 * Real.sqrt T := by
    have hsq := sq_log_le_four_mul (x := 2 * T) (by linarith)
    have hnn_l : 0 ≤ Real.log (2 * T) := Real.log_nonneg (by linarith)
    rw [← Real.sqrt_sq hnn_l]
    calc Real.sqrt ((Real.log (2 * T)) ^ 2)
        ≤ Real.sqrt (8 * T) := Real.sqrt_le_sqrt (by linarith)
      _ ≤ Real.sqrt (16 * T) := Real.sqrt_le_sqrt (by linarith)
      _ = 4 * Real.sqrt T := by rw [Real.sqrt_mul (by norm_num), show Real.sqrt 16 = 4 by norm_num]
  have hrt_ge1 : 1 ≤ Real.sqrt T := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
  have hnum_le : C + K * Real.log (2 * T) < A * Real.sqrt T := by
    dsimp only [A]
    have hC_rt : C ≤ C * Real.sqrt T := le_mul_of_one_le_right hC hrt_ge1
    have hK_rt : K * Real.log (2 * T) ≤ 4 * K * Real.sqrt T := by
      calc K * Real.log (2 * T) ≤ K * (4 * Real.sqrt T) := mul_le_mul_of_nonneg_left hlog_rt hK
        _ = 4 * K * Real.sqrt T := by ring
    linarith
  have hrt_gt : 2 * A / ε < Real.sqrt T := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ 2 * A / ε)]
    exact Real.sqrt_lt_sqrt (by positivity) (by linarith)
  have hrt_pos : 0 < Real.sqrt T := by linarith
  rw [div_lt_iff₀ hT_pos]
  have hmul : A * Real.sqrt T < ε * T := by
    have h1 : 2 * A < ε * Real.sqrt T := by linarith [(div_lt_iff₀ hε).mp hrt_gt]
    have h2 : (2 * A) * Real.sqrt T < (ε * Real.sqrt T) * Real.sqrt T :=
      mul_lt_mul_of_pos_right h1 hrt_pos
    rw [mul_assoc ε, Real.mul_self_sqrt hT_pos.le] at h2
    linarith [mul_pos hA_pos hrt_pos]
  exact hnum_le.trans hmul

/-- **8-Way Unconditional Equivalence (`criticalClustering_logMean_mollifier_hecke_tfae`).**
Across every half-gate parameter `0 < c < 1 / 2`, the following eight statements are
unconditionally equivalent:
1. `(L)` — critical-line `ζ` log-mean `T⁻¹ ∫_T^{2T} log ‖ζ(1/2 + it)‖ dt → 0`;
2. Truncated Euler-product mollified log-mean `T⁻¹ ∫_T^{2T} log ‖ζ M_S‖ dt → 0` for every finite
   set `S : Finset ℕ`;
3. Linear-mollifier outer law for `ζ Ψ_M` for every `M > 1`;
4. Dyadic off-line horizontal moment `T⁻¹ ∑_{z ∈ shellZeros(T, 2T), Re z > 1/2} m_z (Re z - 1/2) → 0`;
5. `100%` critical-scale clustering `offLineCountBeyond (κ / log V) V / (V log V) → 0` for all `κ > 0`;
6. `o(log U)` dyadic `unitWindowDepthCharge` at scale `c log T`;
7. `o(log U)` dyadic `heckeDefect` at scale `c log γ`;
8. `o(log U)` dyadic `polynomialThetaSourceMomentReading` at scale `c log γ` and linear stage. -/
theorem criticalClustering_logMean_mollifier_hecke_tfae {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 2) :
    List.TFAE [
      -- 1. Critical-line `ζ` log-mean `o(1)`:
      Tendsto (fun T : ℝ =>
        T⁻¹ * ∫ t in T..(2 * T), Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
        atTop (𝓝 0),
      -- 2. Truncated Euler-product mollified log-mean `o(1)` for every finite `S`:
      ∀ S : Finset ℕ, Tendsto (fun T : ℝ =>
        T⁻¹ * ∫ t in T..(2 * T),
          Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            eulerProductMollifier S (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
        atTop (𝓝 0),
      -- 3. Linear-mollifier outer law for `ζ Ψ_M` (`M > 1`):
      ∀ M : ℕ, 1 < M → ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ η : ℝ, 0 < η → ∀ᶠ T in atTop,
        T⁻¹ * (∫ t in T..(2 * T), Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            _root_.RHTower.edPoly (_root_.RHTower.levinsonShiftedLinearMollifierCoeff M (1 / 2))
              (Finset.Icc 1 M) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) ≤
          _root_.RHTower.linearMollifierTorusLogMean M ε + η,
      -- 4. Dyadic off-line horizontal moment `o(T)`:
      Tendsto (fun T : ℝ =>
        T⁻¹ * ∑ z ∈ (shellZeros T (2 * T)).filter (fun z => 1 / 2 < z.re),
          ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2))
        atTop (𝓝 0),
      -- 5. `100%` critical-scale clustering (`∀ κ > 0`):
      ∀ κ : ℝ, 0 < κ →
        Tendsto (fun V : ℝ => _root_.RHTower.offLineCountBeyond (κ / Real.log V) V /
          (V * Real.log V)) atTop (𝓝 0),
      -- 6. `o(log U)` dyadic `unitWindowDepthCharge`:
      Tendsto (fun U : ℝ =>
        ((1 / U) * ∫ T in Icc U (2 * U), unitWindowDepthCharge T (c * Real.log T)) / Real.log U)
        atTop (𝓝 0),
      -- 7. `o(log U)` dyadic `heckeDefect`:
      Tendsto (fun U : ℝ =>
        ((1 / U) * ∫ γ in Icc U (2 * U), heckeDefect (baseTwistTest γ) (c * Real.log γ)) /
          Real.log U)
        atTop (𝓝 0),
      -- 8. `o(log U)` dyadic `polynomialThetaSourceMomentReading`:
      Tendsto (fun U : ℝ =>
        ((1 / U) * ∫ γ in Icc U (2 * U),
          polynomialThetaSourceMomentReading (baseTwistTest γ) (c * Real.log γ) 1
            (linearThetaStage (2 * U))) / Real.log U)
        atTop (𝓝 0)
    ] := by
  have h4way := dyadicMean_corridor_and_polynomialTheta_littleO_log_up_to_half_tfae hc0 hc
  tfae_have 1 → 2 := by
    intro h1 S
    have hsum := h1.add (tendsto_window_logMean_eulerProductMollifier_zero S)
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop (20 : ℝ)] with T h20
    rw [← mul_add, ← integral_log_norm_zeta_mul_eulerProductMollifier S h20 (by linarith)]
  tfae_have 2 → 1 := by
    intro h2
    have h0 := (h2 ∅).sub (tendsto_window_logMean_eulerProductMollifier_zero ∅)
    rw [sub_self] at h0
    refine h0.congr' ?_
    filter_upwards [eventually_ge_atTop (20 : ℝ)] with T h20
    rw [integral_log_norm_zeta_mul_eulerProductMollifier ∅ h20 (by linarith), mul_add,
      add_sub_cancel_right]
  tfae_have 1 → 3 := by
    intro h1 M hM
    refine (_root_.RHTower.zetaLine_logMean_le_iff_mollifiedProduct_logMean_le M hM).mp fun η hη => ?_
    filter_upwards [eventually_atTop.mpr ((Metric.tendsto_atTop.mp h1) η hη)] with T hT
    rw [Real.dist_eq, sub_zero] at hT
    exact (le_abs_self _).trans hT.le
  tfae_have 3 → 1 := by
    intro h3
    have hup := (_root_.RHTower.zetaLine_logMean_le_iff_mollifiedProduct_logMean_le 2
      (by norm_num)).mpr (h3 2 (by norm_num))
    obtain ⟨C_fl, K_fl, hC_fl, hK_fl, hfloor⟩ :=
      _root_.RHTower.exists_zetaLine_logMean_floor_all_heights
    have hfl_lim := tendsto_const_add_log_two_mul_div_zero C_fl K_fl hC_fl.le hK_fl.le
    refine Metric.tendsto_atTop.mpr fun η hη => ?_
    have hev := (hup (η / 2) (half_pos hη)).and
      ((eventually_atTop.mpr ((Metric.tendsto_atTop.mp hfl_lim) (η / 2) (half_pos hη))).and
        (eventually_ge_atTop (20 : ℝ)))
    obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hev
    refine ⟨T₀, fun T hT => ?_⟩
    obtain ⟨hle_up, hfl_lt, h20⟩ := hT₀ T hT
    have hT_pos : 0 < T := by linarith
    rw [Real.dist_eq, sub_zero] at hfl_lt ⊢
    have hfl_T := hfloor T h20
    have hlo : -((C_fl + K_fl * Real.log (2 * T)) / T) ≤
        T⁻¹ * ∫ t in T..(2 * T), Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
      rw [div_eq_inv_mul, ← neg_mul_eq_mul_neg]
      have h1 := mul_le_mul_of_nonneg_left hfl_T (inv_nonneg.mpr hT_pos.le)
      linarith
    have hlt_fl : (C_fl + K_fl * Real.log (2 * T)) / T < η / 2 :=
      (le_abs_self _).trans_lt hfl_lt
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  tfae_have 1 → 4 := by
    intro h1
    obtain ⟨C_b, K_b, hC_b, hK_b, hbud⟩ := exists_zetaLine_littlewood_edge_budget_all_heights
    have herr_lim := tendsto_const_add_log_two_mul_div_zero C_b K_b hC_b.le hK_b.le
    have hdiff_lim : Tendsto
        (fun T : ℝ => (T⁻¹ * ∫ t in T..(2 * T),
            Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) -
          2 * Real.pi * (T⁻¹ * ∑ z ∈ (shellZeros T (2 * T)).filter (fun z => 1 / 2 < z.re),
            ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2)))
        atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ herr_lim
      filter_upwards [eventually_ge_atTop (21 : ℝ)] with T hT21
      have hT_pos : 0 < T := by linarith
      rw [Real.norm_eq_abs]
      have heq : (T⁻¹ * ∫ t in T..(2 * T),
            Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) -
          2 * Real.pi * (T⁻¹ * ∑ z ∈ (shellZeros T (2 * T)).filter (fun z => 1 / 2 < z.re),
            ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2)) =
          T⁻¹ * ((∫ t in T..(2 * T),
            Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) -
            2 * Real.pi * ∑ z ∈ (shellZeros T (2 * T)).filter (fun z => 1 / 2 < z.re),
              ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2)) := by ring
      rw [heq, abs_mul, abs_inv, abs_of_pos hT_pos, div_eq_inv_mul _ T]
      exact mul_le_mul_of_nonneg_left (hbud T hT21) (inv_nonneg.mpr hT_pos.le)
    have h2pi := h1.sub hdiff_lim
    rw [sub_zero] at h2pi
    have h2pi' : Tendsto
        (fun T : ℝ => 2 * Real.pi * (T⁻¹ *
          ∑ z ∈ (shellZeros T (2 * T)).filter (fun z => 1 / 2 < z.re),
            ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2)))
        atTop (𝓝 0) := h2pi.congr fun _ => by ring
    have hmul_inv := h2pi'.const_mul (2 * Real.pi)⁻¹
    rw [mul_zero] at hmul_inv
    exact hmul_inv.congr fun _ => by field_simp [Real.pi_pos.ne']
  tfae_have 4 → 1 := by
    intro h4
    obtain ⟨C_b, K_b, hC_b, hK_b, hbud⟩ := exists_zetaLine_littlewood_edge_budget_all_heights
    have herr_lim := tendsto_const_add_log_two_mul_div_zero C_b K_b hC_b.le hK_b.le
    have hdiff_lim : Tendsto
        (fun T : ℝ => (T⁻¹ * ∫ t in T..(2 * T),
            Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) -
          2 * Real.pi * (T⁻¹ * ∑ z ∈ (shellZeros T (2 * T)).filter (fun z => 1 / 2 < z.re),
            ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2)))
        atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ herr_lim
      filter_upwards [eventually_ge_atTop (21 : ℝ)] with T hT21
      have hT_pos : 0 < T := by linarith
      rw [Real.norm_eq_abs]
      have heq : (T⁻¹ * ∫ t in T..(2 * T),
            Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) -
          2 * Real.pi * (T⁻¹ * ∑ z ∈ (shellZeros T (2 * T)).filter (fun z => 1 / 2 < z.re),
            ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2)) =
          T⁻¹ * ((∫ t in T..(2 * T),
            Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) -
            2 * Real.pi * ∑ z ∈ (shellZeros T (2 * T)).filter (fun z => 1 / 2 < z.re),
              ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2)) := by ring
      rw [heq, abs_mul, abs_inv, abs_of_pos hT_pos, div_eq_inv_mul _ T]
      exact mul_le_mul_of_nonneg_left (hbud T hT21) (inv_nonneg.mpr hT_pos.le)
    have hsum := hdiff_lim.add (h4.const_mul (2 * Real.pi))
    rw [mul_zero, add_zero] at hsum
    exact hsum.congr fun _ => sub_add_cancel _ _
  tfae_have 4 → 5 := by
    intro h4 κ hκ
    obtain ⟨C_tot, hC_tot, htot⟩ := stripFinsetPos_orderSum_le_mul_log
    refine Metric.tendsto_atTop.mpr fun ε hε => ?_
    set J : ℕ := Nat.ceil (4 * C_tot / ε) + 1
    have hJ_pos : 1 ≤ J := by omega
    have hpow_ge : 4 * C_tot / ε ≤ (2 : ℝ) ^ J := by
      have hc : 4 * C_tot / ε ≤ (J : ℝ) := by
        calc 4 * C_tot / ε ≤ (Nat.ceil (4 * C_tot / ε) : ℝ) := Nat.le_ceil _
          _ ≤ (J : ℝ) := by dsimp only [J]; push_cast; linarith
      have hj2 : (J : ℝ) ≤ (2 : ℝ) ^ J := by
        have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 by norm_num) J
        norm_num at h
        linarith
      exact hc.trans hj2
    have hinv_pow : C_tot / (2 : ℝ) ^ J ≤ ε / 4 := by
      have h1 : 4 * C_tot ≤ ε * (2 : ℝ) ^ J := by linarith [(div_le_iff₀ hε).mp hpow_ge]
      rw [div_le_iff₀ (by positivity)]
      linarith
    set η : ℝ := κ * ε / (2 * (J : ℝ))
    have hη_pos : 0 < η := by dsimp only [η]; positivity
    obtain ⟨T₀, hT₀⟩ := (Metric.tendsto_atTop.mp h4) η hη_pos
    set V₀ : ℝ := (2 : ℝ) ^ J * max 2 (max T₀ 1)
    refine ⟨V₀, fun V hV => ?_⟩
    have hmax_ge : max 2 (max T₀ 1) ≤ V / (2 : ℝ) ^ J :=
      (le_div_iff₀ (by positivity)).mpr (by linarith [hV])
    have hV_low2 : 2 ≤ V / (2 : ℝ) ^ J := (le_max_left 2 _).trans hmax_ge
    have hV_pos : 0 < V := by
      have : (0 : ℝ) < (2 : ℝ) ^ J := by positivity
      have := (le_div_iff₀ this).mp hV_low2
      linarith
    have hV2 : 2 ≤ V := by
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ J := one_le_pow₀ (by norm_num)
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ J)).mp hV_low2
      linarith
    have hlogV_pos : 0 < Real.log V := Real.log_pos (by linarith)
    have hnn : 0 ≤ _root_.RHTower.offLineCountBeyond (κ / Real.log V) V / (V * Real.log V) :=
      div_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (by positivity)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn, div_lt_iff₀ (mul_pos hV_pos hlogV_pos)]
    -- Cover `(stripFinsetPos V).filter (...)` by `stripFinsetPos (V / 2^J)` and `J` dyadic shells.
    have hcov : (_root_.RHTower.stripFinsetPos V).filter (fun z => 1 / 2 + κ / Real.log V ≤ z.re) ⊆
        _root_.RHTower.stripFinsetPos (V / (2 : ℝ) ^ J) ∪
          (Finset.range J).biUnion (fun j =>
            (shellZeros (V / (2 : ℝ) ^ (j + 1)) (2 * (V / (2 : ℝ) ^ (j + 1)))).filter
              (fun z => 1 / 2 + κ / Real.log V ≤ z.re)) := by
      intro z hz
      obtain ⟨hzS, hre_κ⟩ := Finset.mem_filter.mp hz
      obtain ⟨h0, h1, him0, himV, hxi⟩ := _root_.RHTower.mem_stripFinsetPos.mp hzS
      by_cases hlow : z.im ≤ V / (2 : ℝ) ^ J
      · exact Finset.mem_union.mpr (Or.inl
          (_root_.RHTower.mem_stripFinsetPos.mpr ⟨h0, h1, him0, hlow, hxi⟩))
      · push Not at hlow
        -- Find the largest `j < J` with `V / 2^{j+1} < z.im ≤ V / 2^j` by induction on `J`.
        have hex_j : ∃ j < J, V / (2 : ℝ) ^ (j + 1) < z.im ∧
            z.im ≤ 2 * (V / (2 : ℝ) ^ (j + 1)) := by
          have hind_step : ∀ m : ℕ, z.im ≤ V / (2 : ℝ) ^ 0 → V / (2 : ℝ) ^ m < z.im →
              ∃ j < m, V / (2 : ℝ) ^ (j + 1) < z.im ∧ z.im ≤ 2 * (V / (2 : ℝ) ^ (j + 1)) := by
            intro m htop
            induction m with
            | zero => intro hgt; exfalso; simp at htop hgt; linarith
            | succ m ihm =>
              intro hgt
              rcases le_or_gt z.im (V / (2 : ℝ) ^ m) with hle_m | hgt_m
              · refine ⟨m, Nat.lt_succ_self m, hgt, ?_⟩
                have heq2 : 2 * (V / (2 : ℝ) ^ (m + 1)) = V / (2 : ℝ) ^ m := by
                  rw [pow_succ]; field_simp
                rw [heq2]; exact hle_m
              · obtain ⟨j, hj_lt, hj1, hj2⟩ := ihm hgt_m
                exact ⟨j, Nat.lt_succ_of_lt hj_lt, hj1, hj2⟩
          exact hind_step J (by simpa using himV) hlow
        obtain ⟨j, hj_lt, hj_lo, hj_hi⟩ := hex_j
        refine Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj_lt, ?_⟩))
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨_root_.RHTower.mem_stripFinsetPos.mpr ⟨h0, h1, him0, hj_hi, hxi⟩,
            hj_lo⟩, hre_κ⟩
    -- Bound the base `(0, V / 2^J]` and each dyadic shell `j < J`.
    have hbase_bd : ∑ z ∈ _root_.RHTower.stripFinsetPos (V / (2 : ℝ) ^ J),
        ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤ (ε / 4) * (V * Real.log V) := by
      have hb := htot hV_low2
      have hlog_sub : Real.log (V / (2 : ℝ) ^ J) ≤ Real.log V :=
        Real.log_le_log (by linarith)
          (div_le_self hV_pos.le (one_le_pow₀ (by norm_num)))
      calc ∑ z ∈ _root_.RHTower.stripFinsetPos (V / (2 : ℝ) ^ J),
              ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ)
          ≤ C_tot * (V / (2 : ℝ) ^ J) * Real.log (V / (2 : ℝ) ^ J) := hb
        _ ≤ C_tot * (V / (2 : ℝ) ^ J) * Real.log V :=
            mul_le_mul_of_nonneg_left hlog_sub (by positivity)
        _ = (C_tot / (2 : ℝ) ^ J) * (V * Real.log V) := by ring
        _ ≤ (ε / 4) * (V * Real.log V) :=
            mul_le_mul_of_nonneg_right hinv_pow (by positivity)
    have hshell_bd : ∀ j ∈ Finset.range J,
        ∑ z ∈ (shellZeros (V / (2 : ℝ) ^ (j + 1)) (2 * (V / (2 : ℝ) ^ (j + 1)))).filter
            (fun z => 1 / 2 + κ / Real.log V ≤ z.re),
          ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤
          (ε / (2 * (J : ℝ))) * (V * Real.log V) := by
      intro j hj
      have hj_lt : j < J := Finset.mem_range.mp hj
      set T_j : ℝ := V / (2 : ℝ) ^ (j + 1)
      have hpow_le_J : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ J :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have hTj_ge : V / (2 : ℝ) ^ J ≤ T_j :=
        div_le_div_of_nonneg_left hV_pos.le (by positivity) hpow_le_J
      have hTj_T₀ : T₀ ≤ T_j :=
        ((le_max_left T₀ 1).trans (le_max_right 2 _)).trans (hmax_ge.trans hTj_ge)
      have hTj_pos : 0 < T_j := lt_of_lt_of_le (by linarith) (hV_low2.trans hTj_ge)
      have hTj_le_V : T_j ≤ V := div_le_self hV_pos.le (one_le_pow₀ (by norm_num))
      have hmom_lt := hT₀ T_j hTj_T₀
      rw [Real.dist_eq, sub_zero] at hmom_lt
      have hmom_le : ∑ z ∈ (shellZeros T_j (2 * T_j)).filter (fun z => 1 / 2 < z.re),
          ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) ≤ η * T_j := by
        have h1 : T_j⁻¹ * ∑ z ∈ (shellZeros T_j (2 * T_j)).filter (fun z => 1 / 2 < z.re),
            ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) ≤ η :=
          (le_abs_self _).trans hmom_lt.le
        have h2 := mul_le_mul_of_nonneg_left h1 hTj_pos.le
        rwa [← mul_assoc, mul_inv_cancel₀ hTj_pos.ne', one_mul, mul_comm T_j η] at h2
      have hcheb : (κ / Real.log V) *
          ∑ z ∈ (shellZeros T_j (2 * T_j)).filter (fun z => 1 / 2 + κ / Real.log V ≤ z.re),
            ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤
          ∑ z ∈ (shellZeros T_j (2 * T_j)).filter (fun z => 1 / 2 < z.re),
            ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) := by
        rw [Finset.mul_sum]
        calc ∑ z ∈ (shellZeros T_j (2 * T_j)).filter (fun z => 1 / 2 + κ / Real.log V ≤ z.re),
                (κ / Real.log V) * ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ)
            ≤ ∑ z ∈ (shellZeros T_j (2 * T_j)).filter (fun z => 1 / 2 + κ / Real.log V ≤ z.re),
                ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) := by
              refine Finset.sum_le_sum fun z hz => ?_
              have hre := (Finset.mem_filter.mp hz).2
              rw [mul_comm]
              exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
          _ ≤ ∑ z ∈ (shellZeros T_j (2 * T_j)).filter (fun z => 1 / 2 < z.re),
                ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun z hz _ =>
                mul_nonneg (Nat.cast_nonneg _) (by linarith [(Finset.mem_filter.mp hz).2])
              intro z hz
              obtain ⟨hzS, hre⟩ := Finset.mem_filter.mp hz
              exact Finset.mem_filter.mpr
                ⟨hzS, by linarith [div_pos hκ hlogV_pos]⟩
      have hcnt_le : ∑ z ∈ (shellZeros T_j (2 * T_j)).filter (fun z => 1 / 2 + κ / Real.log V ≤ z.re),
          ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤ (Real.log V / κ) * (η * T_j) := by
        have hpos_div : 0 < κ / Real.log V := div_pos hκ hlogV_pos
        have h1 := (le_div_iff₀' hpos_div).mpr (hcheb.trans hmom_le)
        have h2 : (η * T_j) / (κ / Real.log V) = (Real.log V / κ) * (η * T_j) := by
          field_simp [hκ.ne', hlogV_pos.ne']
        exact h1.trans_eq h2
      calc ∑ z ∈ (shellZeros T_j (2 * T_j)).filter (fun z => 1 / 2 + κ / Real.log V ≤ z.re),
              ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ)
          ≤ (Real.log V / κ) * (η * V) :=
            hcnt_le.trans (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hTj_le_V hη_pos.le) (by positivity))
        _ = (ε / (2 * (J : ℝ))) * (V * Real.log V) := by
            dsimp only [η]; field_simp [hκ.ne']
    unfold _root_.RHTower.offLineCountBeyond
    have htot_sum : ∑ z ∈ (_root_.RHTower.stripFinsetPos V).filter
          (fun z => 1 / 2 + κ / Real.log V ≤ z.re),
        ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤
        (3 * ε / 4) * (V * Real.log V) := by
      calc ∑ z ∈ (_root_.RHTower.stripFinsetPos V).filter
              (fun z => 1 / 2 + κ / Real.log V ≤ z.re),
            ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ)
          ≤ ∑ z ∈ _root_.RHTower.stripFinsetPos (V / (2 : ℝ) ^ J),
              ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) +
            ∑ j ∈ Finset.range J,
              ∑ z ∈ (shellZeros (V / (2 : ℝ) ^ (j + 1)) (2 * (V / (2 : ℝ) ^ (j + 1)))).filter
                  (fun z => 1 / 2 + κ / Real.log V ≤ z.re),
                ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) := by
            exact (Finset.sum_le_sum_of_subset_of_nonneg hcov fun _ _ _ => Nat.cast_nonneg _).trans
              ((finset_sum_union_le _ _ fun _ => Nat.cast_nonneg _).trans
                (add_le_add le_rfl (finset_sum_biUnion_le _ _ fun _ => Nat.cast_nonneg _)))
        _ ≤ (ε / 4) * (V * Real.log V) +
              ∑ _j ∈ Finset.range J, (ε / (2 * (J : ℝ))) * (V * Real.log V) :=
            add_le_add hbase_bd (Finset.sum_le_sum hshell_bd)
        _ = (3 * ε / 4) * (V * Real.log V) := by
            have hJ_ne : (J : ℝ) ≠ 0 := by exact_mod_cast (show J ≠ 0 by omega)
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            field_simp [hJ_ne]; ring
    linarith [htot_sum, mul_pos hε (mul_pos hV_pos hlogV_pos)]
  tfae_have 5 → 4 := by
    intro h5
    obtain ⟨C_tot, hC_tot, htot⟩ := stripFinsetPos_orderSum_le_mul_log
    obtain ⟨B_e, K_e, hB_e, hK_e, hev_exp⟩ := exists_dyadic_offLineTailMoment_le_exp
    obtain ⟨T_exp, hT_exp⟩ := eventually_atTop.mp hev_exp
    refine Metric.tendsto_atTop.mpr fun ε hε => ?_
    set R : ℝ := max 2 (28 * Real.log ((4 * B_e + 1) / ε))
    have hR2 : 2 ≤ R := le_max_left _ _
    have hR_pos : 0 < R := by linarith
    have hexp_R : B_e * Real.exp (-(R / 28)) ≤ ε / 4 := by
      have hlog_le : Real.log ((4 * B_e + 1) / ε) ≤ R / 28 := by
        have := le_max_right 2 (28 * Real.log ((4 * B_e + 1) / ε))
        linarith
      have hexp_le : Real.exp (-(R / 28)) ≤ ε / (4 * B_e + 1) := by
        have h1 : (4 * B_e + 1) / ε ≤ Real.exp (R / 28) := by
          rw [← Real.exp_log (by positivity : 0 < (4 * B_e + 1) / ε)]
          exact Real.exp_le_exp.mpr hlog_le
        rw [Real.exp_neg]
        have h2 := inv_anti₀ (by positivity) h1
        rwa [inv_div] at h2
      calc B_e * Real.exp (-(R / 28))
          ≤ B_e * (ε / (4 * B_e + 1)) := mul_le_mul_of_nonneg_left hexp_le hB_e
        _ = ε * (B_e / (4 * B_e + 1)) := by ring
        _ ≤ ε * (1 / 4) := by
            refine mul_le_mul_of_nonneg_left ?_ hε.le
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]
            linarith
        _ = ε / 4 := by ring
    set κ : ℝ := min 1 (ε / (16 * C_tot))
    have hκ_pos : 0 < κ := lt_min zero_lt_one (by positivity)
    have hκ_C : 4 * C_tot * κ ≤ ε / 4 := by
      have := min_le_right 1 (ε / (16 * C_tot))
      have h1 := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 4 * C_tot)
      have h2 : 4 * C_tot * (ε / (16 * C_tot)) = ε / 4 := by field_simp [hC_tot.ne']; ring
      linarith
    obtain ⟨V_cl, hV_cl⟩ := (Metric.tendsto_atTop.mp (h5 κ hκ_pos)) (ε / (16 * R)) (by positivity)
    set T₀ : ℝ := max 25 (max T_exp (max (V_cl / 2 + 1) ((64 * (K_e + 1) / ε) ^ 2 + 1)))
    refine ⟨T₀, fun T hT => ?_⟩
    have hT25 : 25 ≤ T := (le_max_left _ _).trans hT
    have hT_e : T_exp ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
    have h2T_cl : V_cl ≤ 2 * T := by
      have := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hT
      linarith
    have hT_sq : (64 * (K_e + 1) / ε) ^ 2 + 1 ≤ T :=
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hT
    have hT_pos : 0 < T := by linarith
    have hlogT_ge1 : 1 ≤ Real.log T := by
      have hlog2 : (1 / 2 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
      have hlog4 : 1 < Real.log 4 := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]
        push_cast; linarith
      exact hlog4.le.trans (Real.log_le_log (by norm_num) (by linarith))
    have hlogT_pos : 0 < Real.log T := by linarith
    have hlog2T_le : Real.log (2 * T) ≤ 2 * Real.log T := by
      rw [Real.log_mul zero_lt_two.ne' hT_pos.ne']
      linarith [Real.log_two_lt_d9, hlogT_ge1]
    have hlogT_lt_2T : Real.log T ≤ Real.log (2 * T) :=
      Real.log_le_log hT_pos (by linarith)
    set F_pos : Finset ℂ := (shellZeros T (2 * T)).filter (fun z => 1 / 2 < z.re)
    have hnn : 0 ≤ T⁻¹ * ∑ z ∈ F_pos,
        ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) :=
      mul_nonneg (inv_nonneg.mpr hT_pos.le) (Finset.sum_nonneg fun z hz =>
        mul_nonneg (Nat.cast_nonneg _) (by linarith [(Finset.mem_filter.mp hz).2]))
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    -- Split `F_pos` into near-line (`< κ / log T`), intermediate (`[κ / log T, R / log T)`), and far (`≥ R / log T`).
    set L : ℝ := Real.log T
    have hsplit1 := (Finset.sum_filter_add_sum_filter_not F_pos
      (fun z => 1 / 2 + κ / L ≤ z.re)
      (fun z => ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2))).symm
    have hsplit2 := (Finset.sum_filter_add_sum_filter_not
      (F_pos.filter (fun z => 1 / 2 + κ / L ≤ z.re))
      (fun z => 1 / 2 + R / L ≤ z.re)
      (fun z => ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2))).symm
    -- 1. Near-line piece: `z.re - 1/2 < κ / L`, total count `≤ 4 C_tot T L`.
    have hnear : ∑ z ∈ F_pos.filter (fun z => ¬ 1 / 2 + κ / L ≤ z.re),
        ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) ≤ (ε / 4) * T := by
      have hsub_S : F_pos.filter (fun z => ¬ 1 / 2 + κ / L ≤ z.re) ⊆
          _root_.RHTower.stripFinsetPos (2 * T) := fun z hz =>
        (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).1
      have hcnt_2T := htot (V := 2 * T) (by linarith)
      have hcnt_4 : ∑ z ∈ _root_.RHTower.stripFinsetPos (2 * T),
          ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤ 4 * C_tot * T * L := by
        calc ∑ z ∈ _root_.RHTower.stripFinsetPos (2 * T),
                ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ)
            ≤ C_tot * (2 * T) * Real.log (2 * T) := hcnt_2T
          _ ≤ C_tot * (2 * T) * (2 * L) :=
              mul_le_mul_of_nonneg_left hlog2T_le (by positivity)
          _ = 4 * C_tot * T * L := by ring
      calc ∑ z ∈ F_pos.filter (fun z => ¬ 1 / 2 + κ / L ≤ z.re),
              ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2)
          ≤ ∑ z ∈ F_pos.filter (fun z => ¬ 1 / 2 + κ / L ≤ z.re),
              (κ / L) * ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) := by
            refine Finset.sum_le_sum fun z hz => ?_
            have hlt := not_le.mp (Finset.mem_filter.mp hz).2
            rw [mul_comm (κ / L)]
            exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
        _ = (κ / L) * ∑ z ∈ F_pos.filter (fun z => ¬ 1 / 2 + κ / L ≤ z.re),
              ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) := (Finset.mul_sum _ _ _).symm
        _ ≤ (κ / L) * (4 * C_tot * T * L) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact (Finset.sum_le_sum_of_subset_of_nonneg hsub_S fun _ _ _ =>
              Nat.cast_nonneg _).trans hcnt_4
        _ = (4 * C_tot * κ) * T := by field_simp [hlogT_pos.ne']
        _ ≤ (ε / 4) * T := mul_le_mul_of_nonneg_right hκ_C hT_pos.le
    -- 2. Intermediate piece: `κ / log(2T) ≤ κ / L ≤ z.re - 1/2 < R / L`.
    have hinter : ∑ z ∈ (F_pos.filter (fun z => 1 / 2 + κ / L ≤ z.re)).filter
          (fun z => ¬ 1 / 2 + R / L ≤ z.re),
        ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) ≤ (ε / 4) * T := by
      have hcl_lt := hV_cl (2 * T) h2T_cl
      rw [Real.dist_eq, sub_zero] at hcl_lt
      have hpos_2Tlog : 0 < 2 * T * Real.log (2 * T) :=
        mul_pos (by linarith) (hlogT_pos.trans_le hlogT_lt_2T)
      have hcnt_cl : _root_.RHTower.offLineCountBeyond (κ / Real.log (2 * T)) (2 * T) ≤
          (ε / (4 * R)) * (T * L) := by
        have h1 : _root_.RHTower.offLineCountBeyond (κ / Real.log (2 * T)) (2 * T) /
            (2 * T * Real.log (2 * T)) ≤ ε / (16 * R) :=
          (le_abs_self _).trans hcl_lt.le
        have h2 := (div_le_iff₀ hpos_2Tlog).mp h1
        calc _root_.RHTower.offLineCountBeyond (κ / Real.log (2 * T)) (2 * T)
            ≤ (ε / (16 * R)) * (2 * T * Real.log (2 * T)) := h2
          _ ≤ (ε / (16 * R)) * (2 * T * (2 * L)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hlog2T_le (by linarith)) (by positivity)
          _ = (ε / (4 * R)) * (T * L) := by ring
      have hsub_cl : (F_pos.filter (fun z => 1 / 2 + κ / L ≤ z.re)).filter
            (fun z => ¬ 1 / 2 + R / L ≤ z.re) ⊆
          (_root_.RHTower.stripFinsetPos (2 * T)).filter
            (fun z => 1 / 2 + κ / Real.log (2 * T) ≤ z.re) := by
        intro z hz
        obtain ⟨hz1, _⟩ := Finset.mem_filter.mp hz
        obtain ⟨hzF, hre_κ⟩ := Finset.mem_filter.mp hz1
        have hzS := (Finset.mem_filter.mp (Finset.mem_filter.mp hzF).1).1
        have hdiv_le : κ / Real.log (2 * T) ≤ κ / L :=
          div_le_div_of_nonneg_left hκ_pos.le hlogT_pos hlogT_lt_2T
        exact Finset.mem_filter.mpr ⟨hzS, by linarith⟩
      calc ∑ z ∈ (F_pos.filter (fun z => 1 / 2 + κ / L ≤ z.re)).filter
              (fun z => ¬ 1 / 2 + R / L ≤ z.re),
            ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2)
          ≤ ∑ z ∈ (F_pos.filter (fun z => 1 / 2 + κ / L ≤ z.re)).filter
              (fun z => ¬ 1 / 2 + R / L ≤ z.re),
            (R / L) * ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) := by
            refine Finset.sum_le_sum fun z hz => ?_
            have hlt := not_le.mp (Finset.mem_filter.mp hz).2
            rw [mul_comm (R / L)]
            exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
        _ = (R / L) * ∑ z ∈ (F_pos.filter (fun z => 1 / 2 + κ / L ≤ z.re)).filter
              (fun z => ¬ 1 / 2 + R / L ≤ z.re),
            ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) := (Finset.mul_sum _ _ _).symm
        _ ≤ (R / L) * _root_.RHTower.offLineCountBeyond (κ / Real.log (2 * T)) (2 * T) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact Finset.sum_le_sum_of_subset_of_nonneg hsub_cl fun _ _ _ => Nat.cast_nonneg _
        _ ≤ (R / L) * ((ε / (4 * R)) * (T * L)) :=
            mul_le_mul_of_nonneg_left hcnt_cl (by positivity)
        _ = (ε / 4) * T := by field_simp [hlogT_pos.ne', hR_pos.ne']
    -- 3. Far-tail piece (`≥ R / L`): exponential tail bound gives `< (ε / 2) * T`.
    have hfar : ∑ z ∈ (F_pos.filter (fun z => 1 / 2 + κ / L ≤ z.re)).filter
          (fun z => 1 / 2 + R / L ≤ z.re),
        ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) < (ε / 2) * T := by
      have hsub_R : (F_pos.filter (fun z => 1 / 2 + κ / L ≤ z.re)).filter
            (fun z => 1 / 2 + R / L ≤ z.re) ⊆
          (shellZeros T (2 * T)).filter (fun z => 1 / 2 + R / L ≤ z.re) := by
        intro z hz
        obtain ⟨hz1, hre_R⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hz1).1).1, hre_R⟩
      have hbd_R := hT_exp T hT_e R hR2
      have hK_lt : K_e * L ^ 2 < (ε / 4) * T := by
        have h16 := sq_log_le_sixteen_sqrt (x := T) (by linarith)
        have hrt_gt : 64 * (K_e + 1) / ε < Real.sqrt T := by
          rw [← Real.sqrt_sq (by positivity : 0 ≤ 64 * (K_e + 1) / ε)]
          exact Real.sqrt_lt_sqrt (by positivity) (by linarith)
        have hrt_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT_pos
        have h1 : 64 * (K_e + 1) < ε * Real.sqrt T := by linarith [(div_lt_iff₀ hε).mp hrt_gt]
        have h2 : (64 * (K_e + 1)) * Real.sqrt T < (ε * Real.sqrt T) * Real.sqrt T :=
          mul_lt_mul_of_pos_right h1 hrt_pos
        rw [mul_assoc ε, Real.mul_self_sqrt hT_pos.le] at h2
        have h3 : K_e * L ^ 2 ≤ 16 * K_e * Real.sqrt T := by
          calc K_e * L ^ 2 ≤ K_e * (16 * Real.sqrt T) := mul_le_mul_of_nonneg_left h16 hK_e
            _ = 16 * K_e * Real.sqrt T := by ring
        linarith [mul_pos (by positivity : 0 < K_e + 1) hrt_pos]
      calc ∑ z ∈ (F_pos.filter (fun z => 1 / 2 + κ / L ≤ z.re)).filter
              (fun z => 1 / 2 + R / L ≤ z.re),
            ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2)
          ≤ ∑ z ∈ (shellZeros T (2 * T)).filter (fun z => 1 / 2 + R / L ≤ z.re),
              ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub_R fun z hz _ =>
              mul_nonneg (Nat.cast_nonneg _)
                (by linarith [(Finset.mem_filter.mp hz).2, div_pos hR_pos hlogT_pos])
        _ ≤ B_e * Real.exp (-(R / 28)) * T + K_e * L ^ 2 := hbd_R
        _ ≤ (ε / 4) * T + K_e * L ^ 2 :=
            add_le_add_right (mul_le_mul_of_nonneg_right hexp_R hT_pos.le) _
        _ < (ε / 4) * T + (ε / 4) * T := by linarith [hK_lt]
        _ = (ε / 2) * T := by ring
    have hsum_lt : ∑ z ∈ F_pos,
        ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) < ε * T := by
      rw [hsplit1, hsplit2]
      linarith [hnear, hinter, hfar]
    have hmul_inv := mul_lt_mul_of_pos_left hsum_lt (inv_pos.mpr hT_pos)
    rwa [← mul_assoc, mul_comm T⁻¹ ε, mul_assoc, inv_mul_cancel₀ hT_pos.ne', mul_one] at hmul_inv
  tfae_have 5 → 6 := (h4way.out 3 0).mp
  tfae_have 6 → 7 := (h4way.out 0 1).mp
  tfae_have 7 → 8 := (h4way.out 1 2).mp
  tfae_have 8 → 5 := (h4way.out 2 3).mp
  tfae_finish

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

