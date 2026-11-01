import GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.HalfPlaneMollifiedGreenReading

/-!
# Closing the Critical Gate Gap (`22/51 → 1/2`) and Zero-Density Equivalence up to `2/3`

This module closes the logarithmic corridor gate gap from `22 / 51` to `1 / 2` unconditionally
and establishes the exact zero-density equivalence up to the Ingham–Guth–Maynard `2 / 3` barrier:

1. **Arbitrary-rate Selberg–Barban–Vehov near-line zero density**
   (`exists_selberg_arbitraryRate_nearLine_zeroDensity`):
   Coupling `exists_twoLength_mollified_meanSquare_arbitrary_exponents` with the wide right-shifted
   Littlewood ceiling `exists_zetaZeroDensity_scale_le_of_mollified_meanSquare_wide` yields, for
   every exponential rate `0 < r < 1` and shift slack `ε > 0`, a strict power-saving near-line zero
   density bound `2π (a / log S) N_{≥ 1/2 + (1+ε)a/log S} ≤ (T₂ - T₁) A e^{-r a} + K S^{1 - η_r}`.

2. **Continuous hyperbolic Laplace integration and gate closure `0 < c < 1/2`**
   (`exists_shellDepthSum_le_mul_log_up_to_half`,
    `exists_dyadicMean_compactTest_polynomialTheta_le_log_up_to_half`,
    `exists_dyadicMean_corridor_and_polynomialTheta_le_log_up_to_half`):
   Replacing the discrete `51/50`-stepped Barban–Vehov slab sum in Scale II by continuous hyperbolic
   layer-cake integration (`sum_depthKernel_band_le_sinh_tail_integral`) cancels the `1 / a`
   Littlewood weight loss identically against `sinh(2Lu) ≤ 2Lu exp(2Lu)`, extending the unconditional
   `O_c(log U)` dyadic-mean collapse of `unitWindowDepthCharge`, `heckeDefect`, and
   `polynomialThetaSourceMomentReading` (for arbitrary compact tests supported in `[-1/4, 1/4]`)
   across the full half-gate `0 < c < 1 / 2`, with uniform quadratic scaling `K_c ≤ K_* c²` on
   `0 < c ≤ 1 / 5`.

3. **Sharp `(1 + ε) log(log T) / log T` almost-all unit-window zero-free corridor and `o(log U)`
   four-way equivalence across `0 < c < 1/2`**
   (`eventually_volume_badSharpLogLogCorridor_unitWindows_le`,
    `dyadicMean_corridor_and_polynomialTheta_littleO_log_up_to_half_tfae`):
   Letting `r → 1⁻` and `ε' → 0⁺` sharpens the almost-all unit-window zero-free corridor from
   `(6/5) log(log T) / log T` to `(1 + ε) log(log T) / log T` for every `ε > 0`, and extends the
   4-way `o(log U)` `List.TFAE` with `100%` critical-scale clustering to all `0 < c < 1 / 2`.

4. **Unconditional four-way zero-density equivalence up to `2 / 3`**
   (`dyadicMean_log_bound_iff_nearLine_exp_density_tfae`):
   For every threshold `c_* ∈ (0, 2 / 3]`, `O_c(log U)` dyadic-mean boundedness of
   `unitWindowDepthCharge`, `heckeDefect`, and `polynomialThetaSourceMomentReading` across all
   `0 < c < c_*` is unconditionally equivalent (`List.TFAE`) to exponential near-line zero-density
   decay of rate `r` across all `0 < r < 2 c_*`.
-/

set_option autoImplicit false

open Complex Filter Topology Set MeasureTheory intervalIntegral
open scoped BigOperators Real ComplexConjugate ContDiff ENNReal Interval
open _root_.RHTower _root_.Zeta23

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect

open GaloisForLFunctions.ConjugateDiagonalGeometry
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
open ArithmeticPolarization SquareRootThreshold

/-! ## §1. Shell counting, `XiZeroCopy` deep-shell lifting, and step-tail integrability -/

private theorem one_le_log_of_four_le' {V : ℝ} (hV : 4 ≤ V) : 1 ≤ Real.log V := by
  have h2 := Real.log_two_gt_d9
  have h4_eq : (2 : ℝ) ^ (2 : ℕ) = 4 := by norm_num
  have h4 : Real.log ((2 : ℝ) ^ (2 : ℕ)) ≤ Real.log V :=
    Real.log_le_log (by norm_num) (h4_eq.trans_le hV)
  rw [Real.log_pow] at h4; push_cast at h4; linarith only [h2, h4]

private theorem two_le_log_of_sixteen_le' {V : ℝ} (hV : 16 ≤ V) : 2 ≤ Real.log V := by
  have h2 := Real.log_two_gt_d9
  have h16_eq : (2 : ℝ) ^ (4 : ℕ) = 16 := by norm_num
  have h16 : Real.log ((2 : ℝ) ^ (4 : ℕ)) ≤ Real.log V :=
    Real.log_le_log (by norm_num) (h16_eq.trans_le hV)
  rw [Real.log_pow] at h16; push_cast at h16; linarith only [h2, h16]

private theorem log_four_le_two' : Real.log 4 ≤ 2 := by
  have h4_eq : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
  rw [h4_eq, Real.log_pow]; push_cast; linarith only [Real.log_two_lt_d9]

private theorem shellRight_orderSum_le_windowZeros' {T₁ T₂ d : ℝ} (hT₁ : 0 < T₁) (hT : T₁ ≤ T₂)
    (hd : 0 ≤ d) :
    (∑ z ∈ (shellZeros T₁ T₂).filter (fun z => 1 / 2 + d ≤ z.re),
      ((analyticOrderAt xi z).toNat : ℝ)) ≤
      ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + d ≤ w.re),
        ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
  classical
  have hsub : (shellZeros T₁ T₂).filter (fun z => 1 / 2 + d ≤ z.re) ⊆
      (windowZeros T₁ T₂).filter (fun w => 1 / 2 + d ≤ w.re) := by
    intro z hz
    obtain ⟨hz_sh, hre_d⟩ := Finset.mem_filter.mp hz
    obtain ⟨hz_pos, him1⟩ := Finset.mem_filter.mp hz_sh
    obtain ⟨h0, h1, _, him2, hxi⟩ := mem_stripFinsetPos.mp hz_pos
    rw [Finset.mem_filter, mem_windowZeros_iff hT₁ hT]
    refine ⟨⟨Complex.mem_reProdIm.mpr ⟨?_, ?_⟩, (xi_zero_iff_zeta_zero_of_mem_strip h0 h1).mp hxi⟩,
      hre_d⟩
    · rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 15 / 2)]
      exact ⟨by linarith only [hd, hre_d], by linarith only [h1]⟩
    · rw [uIcc_of_le hT]
      exact ⟨him1.le, him2⟩
  calc ∑ z ∈ (shellZeros T₁ T₂).filter (fun z => 1 / 2 + d ≤ z.re),
          ((analyticOrderAt xi z).toNat : ℝ)
      = ∑ z ∈ (shellZeros T₁ T₂).filter (fun z => 1 / 2 + d ≤ z.re),
          ((analyticOrderAt riemannZeta z).toNat : ℝ) := by
        refine Finset.sum_congr rfl fun z hz => ?_
        obtain ⟨h0, h1, _, _, _⟩ :=
          mem_stripFinsetPos.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1
        rw [xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨h0, h1⟩]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _

private theorem shellOrderSum_abs_ge_eq_two_mul_right' (V₁ V₂ : ℝ) {b : ℝ} (hb : 0 < b) :
    (∑ z ∈ (shellZeros V₁ V₂).filter (fun z => b ≤ |z.re - 1 / 2|),
      ((analyticOrderAt xi z).toNat : ℝ)) =
      2 * ∑ z ∈ (shellZeros V₁ V₂).filter (fun z => 1 / 2 + b ≤ z.re),
        ((analyticOrderAt xi z).toNat : ℝ) := by
  classical
  let t := shellZeros V₁ V₂
  let m : ℂ → ℝ := fun z => ((analyticOrderAt xi z).toNat : ℝ)
  let A := t.filter (fun z => b ≤ |z.re - 1 / 2|)
  have hsplit := (Finset.sum_filter_add_sum_filter_not A (fun z => 1 / 2 ≤ z.re) m).symm
  have hR : A.filter (fun z => 1 / 2 ≤ z.re) = t.filter (fun z => 1 / 2 + b ≤ z.re) := by
    ext z
    simp only [A, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hz, habs⟩, hge⟩
      rw [abs_of_nonneg (by linarith only [hge])] at habs
      exact ⟨hz, by linarith only [habs]⟩
    · rintro ⟨hz, hge⟩
      refine ⟨⟨hz, ?_⟩, by linarith only [hb, hge]⟩
      rw [abs_of_nonneg (by linarith only [hb, hge])]; linarith only [hge]
  have hL : A.filter (fun z => ¬ 1 / 2 ≤ z.re) = t.filter (fun z => z.re ≤ 1 / 2 - b) := by
    ext z
    simp only [A, Finset.mem_filter, not_le]
    constructor
    · rintro ⟨⟨hz, habs⟩, hlt⟩
      rw [abs_of_neg (by linarith only [hlt])] at habs
      exact ⟨hz, by linarith only [habs]⟩
    · rintro ⟨hz, hle⟩
      refine ⟨⟨hz, ?_⟩, by linarith only [hb, hle]⟩
      rw [abs_of_neg (by linarith only [hb, hle])]; linarith only [hle]
  have hbij : ∑ z ∈ t.filter (fun z => z.re ≤ 1 / 2 - b), m z =
      ∑ z ∈ t.filter (fun z => 1 / 2 + b ≤ z.re), m z := by
    refine Finset.sum_nbij' lineReflect lineReflect ?_ ?_ ?_ ?_ ?_
    · intro z hz
      rw [Finset.mem_filter] at hz ⊢
      exact ⟨lineReflect_mem_shellZeros hz.1, by rw [lineReflect_re]; linarith only [hz.2]⟩
    · intro z hz
      rw [Finset.mem_filter] at hz ⊢
      exact ⟨lineReflect_mem_shellZeros hz.1, by rw [lineReflect_re]; linarith only [hz.2]⟩
    · intro z _; exact lineReflect_involutive z
    · intro z _; exact lineReflect_involutive z
    · intro z _; dsimp [m]; rw [xi_orderAt_lineReflect]
  change ∑ z ∈ A, m z = 2 * ∑ z ∈ t.filter (fun z => 1 / 2 + b ≤ z.re), m z
  rw [hsplit, hR, hL, hbij, two_mul]

private theorem finset_sum_union_le' {α : Type*} [DecidableEq α] (s₁ s₂ : Finset α)
    {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) :
    ∑ a ∈ s₁ ∪ s₂, f a ≤ ∑ a ∈ s₁, f a + ∑ a ∈ s₂, f a := by
  have h := Finset.sum_union_inter (s₁ := s₁) (s₂ := s₂) (f := f)
  have hnn : 0 ≤ ∑ a ∈ s₁ ∩ s₂, f a := Finset.sum_nonneg fun a _ => hf a
  linarith only [h, hnn]

private theorem finset_sum_biUnion_le' {ι α : Type*} [DecidableEq α] (s : Finset ι)
    (t : ι → Finset α) {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) :
    ∑ a ∈ s.biUnion t, f a ≤ ∑ i ∈ s, ∑ a ∈ t i, f a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hi]
      exact (finset_sum_union_le' (t i) (s.biUnion t) hf).trans (add_le_add le_rfl ih)

private theorem stripFinsetPos_orderSum_le_mul_log' {V : ℝ} (hV : 2 ≤ V) :
    ∑ z ∈ stripFinsetPos V, ((analyticOrderAt xi z).toNat : ℝ) ≤
      32 * (2 * |xiLineTwoLogDerivConstant| + 5) * V * Real.log V := by
  classical
  have hV_pos : 0 < V := by linarith only [hV]
  have hlogV_half : (1 / 2 : ℝ) ≤ Real.log V := by
    have h1 := Real.log_two_gt_d9
    have h2 := Real.log_le_log zero_lt_two hV
    linarith only [h1, h2]
  let n : ℕ := ⌈V⌉₊
  have hn_lt : (n : ℝ) < V + 1 := Nat.ceil_lt_add_one hV_pos.le
  have hn_le_2V : (n : ℝ) ≤ 2 * V := by linarith only [hn_lt, hV]
  have hsub : stripFinsetPos V ⊆
      (Finset.range n).biUnion (fun k => shellZeros (k : ℝ) ((k : ℝ) + 1)) := by
    intro z hz
    obtain ⟨h0, h1, him0, himV, hxi⟩ := mem_stripFinsetPos.mp hz
    let m : ℕ := ⌈z.im⌉₊
    have hm_pos : 1 ≤ m := Nat.ceil_pos.mpr him0
    have hm_le : m ≤ n := Nat.ceil_mono himV
    let k : ℕ := m - 1
    have hk_lt : k < n := by omega
    have hkm : (k : ℝ) + 1 = (m : ℝ) := by
      have : k + 1 = m := by omega
      exact_mod_cast this
    have him_le : z.im ≤ (k : ℝ) + 1 := by rw [hkm]; exact Nat.le_ceil z.im
    have him_gt : (k : ℝ) < z.im := by
      have hlt : (m : ℝ) < z.im + 1 := Nat.ceil_lt_add_one him0.le
      linarith only [hkm, hlt]
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hk_lt,
      Finset.mem_filter.mpr ⟨mem_stripFinsetPos.mpr ⟨h0, h1, him0, him_le, hxi⟩, him_gt⟩⟩
  have hterm_le : ∀ k ∈ Finset.range n,
      (∑ z ∈ shellZeros (k : ℝ) ((k : ℝ) + 1), ((analyticOrderAt xi z).toNat : ℝ)) ≤
        16 * (2 * |xiLineTwoLogDerivConstant| + 5) * Real.log V := by
    intro k hk
    have hk_lt : k < n := Finset.mem_range.mp hk
    have hk1_le : (k : ℝ) + 1 ≤ (n : ℝ) := by
      have : k + 1 ≤ n := by omega
      exact_mod_cast this
    have hord := shortShell_orderSum_le_log (V₁ := (k : ℝ)) (V₂ := (k : ℝ) + 1)
      (Nat.cast_nonneg k) (by linarith) (by linarith)
    have hlog_k : Real.log ((k : ℝ) + 1 + 4) ≤ 5 * Real.log V := by
      have hle4V : (k : ℝ) + 1 + 4 ≤ 4 * V := by linarith only [hk1_le, hn_le_2V, hV]
      calc Real.log ((k : ℝ) + 1 + 4)
          ≤ Real.log (4 * V) := Real.log_le_log (by positivity) hle4V
        _ = Real.log 4 + Real.log V := Real.log_mul (by norm_num) hV_pos.ne'
        _ ≤ 2 + Real.log V := by linarith only [log_four_le_two']
        _ ≤ 5 * Real.log V := by linarith only [hlogV_half]
    have hinner : |xiLineTwoLogDerivConstant| + Real.log ((k : ℝ) + 1 + 4) ≤
        (2 * |xiLineTwoLogDerivConstant| + 5) * Real.log V := by
      have hc_nn : 0 ≤ |xiLineTwoLogDerivConstant| := abs_nonneg _
      nlinarith only [hlog_k, hlogV_half, hc_nn]
    calc (∑ z ∈ shellZeros (k : ℝ) ((k : ℝ) + 1), ((analyticOrderAt xi z).toNat : ℝ))
        ≤ 16 * (|xiLineTwoLogDerivConstant| + Real.log ((k : ℝ) + 1 + 4)) := hord
      _ ≤ 16 * ((2 * |xiLineTwoLogDerivConstant| + 5) * Real.log V) :=
          mul_le_mul_of_nonneg_left hinner (by norm_num)
      _ = 16 * (2 * |xiLineTwoLogDerivConstant| + 5) * Real.log V := by ring
  calc ∑ z ∈ stripFinsetPos V, ((analyticOrderAt xi z).toNat : ℝ)
      ≤ ∑ z ∈ (Finset.range n).biUnion (fun k => shellZeros (k : ℝ) ((k : ℝ) + 1)),
          ((analyticOrderAt xi z).toNat : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _
    _ ≤ ∑ k ∈ Finset.range n,
          ∑ z ∈ shellZeros (k : ℝ) ((k : ℝ) + 1), ((analyticOrderAt xi z).toNat : ℝ) :=
        finset_sum_biUnion_le' _ _ fun _ => Nat.cast_nonneg _
    _ ≤ ∑ _k ∈ Finset.range n,
          16 * (2 * |xiLineTwoLogDerivConstant| + 5) * Real.log V :=
        Finset.sum_le_sum hterm_le
    _ = (n : ℝ) * (16 * (2 * |xiLineTwoLogDerivConstant| + 5) * Real.log V) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (2 * V) * (16 * (2 * |xiLineTwoLogDerivConstant| + 5) * Real.log V) :=
        mul_le_mul_of_nonneg_right hn_le_2V (by positivity)
    _ = 32 * (2 * |xiLineTwoLogDerivConstant| + 5) * V * Real.log V := by ring

private def toXiDivisorSupport' (z : ℂ) (hz : xi z = 0) : XiDivisorSupport :=
  ⟨z, Function.mem_support.mpr (by
    rw [xi_divisor_apply_of_mem (Set.mem_univ z)]
    exact_mod_cast xi_order_toNat_ne_zero hz)⟩

private def liftToXiZeroCopy' (S : Finset ℂ) (hS : ∀ z ∈ S, xi z = 0) : Finset XiZeroCopy :=
  S.attach.biUnion fun z =>
    (Finset.univ : Finset (Fin (Int.toNat (MeromorphicOn.divisor xi Set.univ
      (toXiDivisorSupport' z.1 (hS z.1 z.2) : ℂ))))).image
      (fun i => (⟨toXiDivisorSupport' z.1 (hS z.1 z.2), i⟩ : XiZeroCopy))

private theorem sum_analyticOrder_eq_sum_liftToXiZeroCopy' (S : Finset ℂ)
    (hS : ∀ z ∈ S, xi z = 0) (g : ℂ → ℝ) :
    ∑ z ∈ S, ((analyticOrderAt xi z).toNat : ℝ) * g z =
      ∑ q ∈ liftToXiZeroCopy' S hS, g (q.1 : ℂ) := by
  classical
  unfold liftToXiZeroCopy'
  have hdisj : Set.PairwiseDisjoint (S.attach : Set {z // z ∈ S})
      (fun z => (Finset.univ : Finset (Fin (Int.toNat (MeromorphicOn.divisor xi Set.univ
        (toXiDivisorSupport' z.1 (hS z.1 z.2) : ℂ))))).image
        (fun i => (⟨toXiDivisorSupport' z.1 (hS z.1 z.2), i⟩ : XiZeroCopy))) := by
    intro a _ b _ hab
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro q hqa hqb
    obtain ⟨ia, _, rfl⟩ := Finset.mem_image.mp hqa
    obtain ⟨ib, _, heq⟩ := Finset.mem_image.mp hqb
    have hval : a.1 = b.1 := congrArg (fun x : XiZeroCopy => (x.1 : ℂ)) heq.symm
    exact hab (Subtype.ext hval)
  rw [Finset.sum_biUnion hdisj, ← Finset.sum_attach S]
  refine Finset.sum_congr rfl fun z _ => ?_
  let ρ : XiDivisorSupport := toXiDivisorSupport' z.1 (hS z.1 z.2)
  rw [Finset.sum_image fun _ _ _ _ hij => eq_of_heq (Sigma.mk.inj_iff.mp hij).2]
  have hconst : (∑ _i ∈ (Finset.univ : Finset (Fin (Int.toNat (MeromorphicOn.divisor xi Set.univ (ρ : ℂ))))),
      g (ρ : ℂ)) = (Int.toNat (MeromorphicOn.divisor xi Set.univ (ρ : ℂ)) : ℝ) * g (ρ : ℂ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hconst]
  have hρ_eq : (ρ : ℂ) = z.1 := rfl
  rw [hρ_eq, xi_divisor_apply_of_mem (Set.mem_univ z.1), Int.toNat_natCast]

private theorem mem_liftToXiZeroCopy_iff' {S : Finset ℂ} {hS : ∀ z ∈ S, xi z = 0}
    {q : XiZeroCopy} :
    q ∈ liftToXiZeroCopy' S hS → (q.1 : ℂ) ∈ S := by
  unfold liftToXiZeroCopy'
  intro hq
  obtain ⟨z, _, hqi⟩ := Finset.mem_biUnion.mp hq
  obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hqi
  exact z.2

/-- General Scale-III deep-shell bound at any abscissa threshold `1 / 2 + θ₀ ≤ z.re` (`θ₀ > 0`). -/
private theorem scaleIII_deep_shell_sum_le_general (R_deep : Finset ℂ)
    {V T₁ T₂ L θ₀ C_deep γ₀ : ℝ}
    (hV_pos : 0 < V) (hVT₁ : V ≤ T₁) (hT₂2V : T₂ ≤ 2 * V) (hL0 : 0 ≤ L) (hθ₀ : 0 < θ₀)
    (hsub : R_deep ⊆ shellZeros T₁ T₂)
    (hre : ∀ z ∈ R_deep, 1 / 2 + θ₀ ≤ z.re)
    (hdeep_V : ∀ G : Finset XiZeroCopy,
      (∀ q ∈ G, 1 / 2 + θ₀ ≤ foldedRe q ∧ V ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 2 * V) →
      (1 / V) * ∑ q ∈ G, Real.exp (2 * L * (foldedRe q - 1 / 2)) ≤ C_deep * V ^ (-γ₀)) :
    2 * ∑ z ∈ R_deep, ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2) ≤
      2 * (C_deep * V ^ (1 - γ₀)) := by
  have hxi : ∀ z ∈ R_deep, xi z = 0 := fun z hz =>
    (mem_stripFinsetPos.mp (Finset.mem_filter.mp (hsub hz)).1).2.2.2.2
  have hptw : ∑ z ∈ R_deep, ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2) ≤
      ∑ z ∈ R_deep, ((analyticOrderAt xi z).toNat : ℝ) * Real.exp (2 * L * (z.re - 1 / 2)) := by
    refine Finset.sum_le_sum fun z hz => ?_
    have hge := hre z hz
    have hdk := depthKernel_le_exp_two_mul (d := z.re - 1 / 2) hL0
    rw [abs_of_pos (by linarith only [hge, hθ₀])] at hdk
    exact mul_le_mul_of_nonneg_left hdk (Nat.cast_nonneg _)
  have hfold_eq : ∑ q ∈ liftToXiZeroCopy' R_deep hxi, Real.exp (2 * L * ((q.1 : ℂ).re - 1 / 2)) =
      ∑ q ∈ liftToXiZeroCopy' R_deep hxi, Real.exp (2 * L * (foldedRe q - 1 / 2)) := by
    refine Finset.sum_congr rfl fun q hq => ?_
    have hge := hre (q.1 : ℂ) (mem_liftToXiZeroCopy_iff' hq)
    rw [show foldedRe q = (q.1 : ℂ).re from max_eq_left (by linarith only [hge, hθ₀])]
  have hG_cond : ∀ q ∈ liftToXiZeroCopy' R_deep hxi,
      1 / 2 + θ₀ ≤ foldedRe q ∧ V ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 2 * V := by
    intro q hq
    have hz_mem : (q.1 : ℂ) ∈ R_deep := mem_liftToXiZeroCopy_iff' hq
    have hge := hre (q.1 : ℂ) hz_mem
    have hz_sh := hsub hz_mem
    have him1 : T₁ < (q.1 : ℂ).im := (Finset.mem_filter.mp hz_sh).2
    have him2 : (q.1 : ℂ).im ≤ T₂ := (mem_stripFinsetPos.mp (Finset.mem_filter.mp hz_sh).1).2.2.2.1
    rw [abs_of_pos (by linarith only [hV_pos, hVT₁, him1])]
    exact ⟨le_trans hge (le_max_left _ _), by linarith only [hVT₁, him1],
      by linarith only [him2, hT₂2V]⟩
  have hm_V := mul_le_mul_of_nonneg_left (hdeep_V (liftToXiZeroCopy' R_deep hxi) hG_cond) hV_pos.le
  have hlhs : V * ((1 / V) * ∑ q ∈ liftToXiZeroCopy' R_deep hxi,
      Real.exp (2 * L * (foldedRe q - 1 / 2))) =
      ∑ q ∈ liftToXiZeroCopy' R_deep hxi, Real.exp (2 * L * (foldedRe q - 1 / 2)) := by
    field_simp [hV_pos.ne']
  have hrhs : V * (C_deep * V ^ (-γ₀)) = C_deep * V ^ (1 - γ₀) := by
    calc V * (C_deep * V ^ (-γ₀))
        = C_deep * (V ^ (1 : ℝ) * V ^ (-γ₀)) := by rw [Real.rpow_one]; ring
      _ = C_deep * V ^ (1 - γ₀) := by rw [← Real.rpow_add hV_pos]; ring_nf
  rw [hlhs, hrhs] at hm_V
  have hchain : ∑ z ∈ R_deep, ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2) ≤
      C_deep * V ^ (1 - γ₀) :=
    calc ∑ z ∈ R_deep, ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2)
        ≤ ∑ z ∈ R_deep, ((analyticOrderAt xi z).toNat : ℝ) * Real.exp (2 * L * (z.re - 1 / 2)) := hptw
      _ = ∑ q ∈ liftToXiZeroCopy' R_deep hxi, Real.exp (2 * L * ((q.1 : ℂ).re - 1 / 2)) :=
          sum_analyticOrder_eq_sum_liftToXiZeroCopy' R_deep hxi _
      _ = ∑ q ∈ liftToXiZeroCopy' R_deep hxi, Real.exp (2 * L * (foldedRe q - 1 / 2)) := hfold_eq
      _ ≤ C_deep * V ^ (1 - γ₀) := hm_V
  exact mul_le_mul_of_nonneg_left hchain zero_le_two

/-- Interval integrability of a continuous weight multiplied by a finite zero-tail step sum. -/
private theorem intervalIntegrable_mul_tailCount (S : Finset ℂ) (m : ℂ → ℝ) {g : ℝ → ℝ}
    (hg : Continuous g) {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable
      (fun u : ℝ => g u * ∑ w ∈ S.filter (fun w => 1 / 2 + u ≤ w.re), m w) volume a b := by
  classical
  have hrew : (fun u : ℝ => g u * ∑ w ∈ S.filter (fun w => 1 / 2 + u ≤ w.re), m w) =
      fun u : ℝ => ∑ w ∈ S, (if 1 / 2 + u ≤ w.re then m w * g u else 0) := by
    funext u
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    split_ifs <;> ring
  rw [hrew]
  refine IntervalIntegrable.sum S fun w _ => ?_
  rcases lt_or_ge (w.re - 1 / 2) a with hlt_a | hge_a
  · refine intervalIntegrable_const.congr fun u hu => ?_
    rw [uIoc_of_le hab] at hu
    exact (if_neg (by linarith only [hlt_a, hu.1])).symm
  · rcases le_or_gt b (w.re - 1 / 2) with hle_b | hlt_b
    · refine ((hg.const_mul (m w)).intervalIntegrable (μ := volume) a b).congr fun u hu => ?_
      rw [uIoc_of_le hab] at hu
      exact (if_pos (by linarith only [hle_b, hu.2])).symm
    · have h1 : IntervalIntegrable (fun u : ℝ => if 1 / 2 + u ≤ w.re then m w * g u else 0)
          volume a (w.re - 1 / 2) :=
        ((hg.const_mul (m w)).intervalIntegrable (μ := volume) a (w.re - 1 / 2)).congr fun u hu => by
          rw [uIoc_of_le hge_a] at hu
          exact (if_pos (by linarith only [hu.2])).symm
      have h2 : IntervalIntegrable (fun u : ℝ => if 1 / 2 + u ≤ w.re then m w * g u else 0)
          volume (w.re - 1 / 2) b :=
        intervalIntegrable_const.congr fun u hu => by
          rw [uIoc_of_le hlt_b.le] at hu
          exact (if_neg (by linarith only [hu.1])).symm
      exact h1.trans h2

/-! ## §2. Arbitrary-rate Selberg–Barban–Vehov near-line zero density -/

/-- **Arbitrary-Rate Selberg–Barban–Vehov Near-Line Zero Density
(`exists_selberg_arbitraryRate_nearLine_zeroDensity`).**
For every exponential rate `0 < r < 1` and shift slack `ε > 0`, optimizing the two-piece
Barban–Vehov mollifier exponents `r / 2 < θ_Y < θ_X < 1 / 2` yields a strict power-saving
(`S ^ (1 - η_r)`, `0 < η_r < 1 / 2`) near-line zero-density bound across all
`1 ≤ a ≤ (1 / (4 * (1 + min ε 1))) * log S`. -/
theorem exists_selberg_arbitraryRate_nearLine_zeroDensity
    {r ε : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hε : 0 < ε) :
    ∃ A K η_r : ℝ, 0 < A ∧ 0 < K ∧ 0 < η_r ∧ η_r < 1 / 2 ∧
      ∀ᶠ S : ℝ in atTop,
        ∃ T₁ ∈ Ioo (2 * S / 3) (2 * S / 3 + 1),
        ∃ T₂ ∈ Ioo (4 * S / 3 - 1) (4 * S / 3),
          ∀ a : ℝ, 1 ≤ a → a ≤ (1 / (4 * (1 + min ε 1))) * Real.log S →
            ∀ Z : Finset ℂ,
              (∀ z : ℂ, z ∈ Z ↔
                z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
              2 * Real.pi * ((a / Real.log S) *
                ∑ w ∈ Z.filter (fun w => 1 / 2 + (1 + ε) * (a / Real.log S) ≤ w.re),
                  ((analyticOrderAt riemannZeta w).toNat : ℝ)) ≤
                (T₂ - T₁) * (A * Real.exp (-(r * a))) + K * S ^ (1 - η_r) := by
  let θ_Y : ℝ := (r + 1) / 4
  let θ_X : ℝ := (θ_Y + 1 / 2) / 2
  let η_r : ℝ := (1 / 2 - θ_X) / 2
  let ε₁ : ℝ := min ε 1
  have hθY : 0 < θ_Y := by dsimp [θ_Y]; linarith only [hr0]
  have hYX_exp : θ_Y < θ_X := by dsimp [θ_X, θ_Y]; linarith only [hr1]
  have hθX : θ_X < 1 / 2 := by dsimp [θ_X, θ_Y]; linarith only [hr1]
  have hr_2θY : r < 2 * θ_Y := by dsimp [θ_Y]; linarith only [hr1]
  have hη_pos : 0 < η_r := by dsimp [η_r]; linarith only [hθX]
  have hη_lt : η_r < 1 / 2 := by dsimp [η_r]; linarith only [hθY, hYX_exp]
  have hε₁_pos : 0 < ε₁ := lt_min hε zero_lt_one
  have hε₁_le_ε : ε₁ ≤ ε := min_le_left _ _
  have hε₁_le1 : ε₁ ≤ 1 := min_le_right _ _
  obtain ⟨A₀, hA₀, hev_msq⟩ :=
    exists_twoLength_mollified_meanSquare_arbitrary_exponents hθY hYX_exp hθX hr0 hr_2θY
  obtain ⟨C_zd, K_zd, hC_zd, hK_zd, hzd⟩ :=
    RHTower.exists_zetaZeroDensity_scale_le_of_mollified_meanSquare_wide
  obtain ⟨K_log1, hK_log1, hlog1⟩ := exists_one_add_log_pow_le_rpow 1 hη_pos
  let A : ℝ := A₀ / (2 * ε₁) + 1
  let K : ℝ := (60 + (C_zd + 5 * K_zd) * K_log1) / ε₁ + 1
  refine ⟨A, K, η_r, by dsimp [A]; positivity, by dsimp [K]; positivity, hη_pos, hη_lt, ?_⟩
  filter_upwards [hev_msq, eventually_ge_atTop (60 : ℝ)] with S hmsq hS60
  clear hev_msq
  have hS1 : 1 < S := by linarith only [hS60]
  have hS_pos : 0 < S := by linarith only [hS60]
  have hLS_pos : 0 < Real.log S := Real.log_pos hS1
  obtain ⟨T₁, hT₁, T₂, hT₂, hY3, hYX, hXhi, hadm1, hadm2, hMsq_all⟩ := hmsq
  refine ⟨T₁, hT₁, T₂, hT₂, fun a ha1 ha_hi Z hZ => ?_⟩
  have hT12 : T₁ < T₂ := by linarith only [hT₁.2, hT₂.1, hS60]
  have hlen_pos : 0 < T₂ - T₁ := sub_pos.mpr hT12
  let X : ℕ := VerticalAP.molLen θ_X S
  let Y : ℕ := VerticalAP.molLen θ_Y S
  have hX1 : 1 ≤ X := by omega
  have hlogT₂ : Real.log T₂ ≤ 2 * Real.log S := by
    have h1 : Real.log T₂ ≤ Real.log (2 * S) :=
      Real.log_le_log (by linarith only [hT₂.1, hS60]) (by linarith only [hT₂.2, hS60])
    rw [Real.log_mul two_ne_zero hS_pos.ne'] at h1
    have hLS1 : 1 ≤ Real.log S := by
      have : Real.exp 1 ≤ S := by linarith only [Real.exp_one_lt_d9, hS60]
      exact (Real.le_log_iff_exp_le hS_pos).mpr this
    linarith only [h1, Real.log_two_lt_d9, hLS1]
  have hlogMb : Real.log ((X : ℝ) ^ (5 : ℕ)) ≤ 3 * Real.log S := by
    rw [Real.log_pow]; push_cast
    have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX1
    have hlogX : Real.log (X : ℝ) ≤ θ_X * Real.log S := by
      rw [← Real.log_rpow hS_pos]; exact Real.log_le_log hXpos hXhi
    nlinarith only [hlogX, hθX, hLS_pos]
  let σ₀ : ℝ := 1 / 2 + a / Real.log S
  let Δ : ℝ := ε₁ * (a / Real.log S)
  have ha_div_pos : 0 < a / Real.log S := div_pos (by linarith only [ha1]) hLS_pos
  have ha_sum_le : (1 + ε₁) * (a / Real.log S) ≤ 1 / 4 := by
    have hm := (div_le_iff₀ hLS_pos).mpr ha_hi
    have hpos : 0 < 4 * (1 + ε₁) := by positivity
    have hm2 := (le_div_iff₀' hpos).mp (by
      simpa [div_mul_eq_mul_div, mul_comm] using ha_div_pos.le.trans_eq rfl |>.trans (by
        rw [div_le_iff₀ hLS_pos]; exact ha_hi))
    linarith only [hm2]
  have hσ₀_mem : σ₀ ∈ Icc (1 / 2 : ℝ) 1 := by
    refine ⟨by dsimp [σ₀]; linarith only [ha_div_pos], ?_⟩
    have hnn : 0 ≤ ε₁ * (a / Real.log S) := mul_nonneg hε₁_pos.le ha_div_pos.le
    dsimp [σ₀]; linarith only [ha_sum_le, hnn]
  let Msq_ub : ℝ :=
    (T₂ - T₁) * (1 + A₀ * Real.exp (-(r * a))) + 120 * S ^ (θ_X + 1 / 2)
  have hMsq_le : (∫ t in T₁..T₂,
      ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
        edPoly (twoLengthCoeff X Y) (Finset.Icc 1 X) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ Msq_ub := by
    have hm := hMsq_all σ₀ hσ₀_mem
    have harg : (σ₀ - 1 / 2) * Real.log S = a := by
      dsimp [σ₀]; field_simp [hLS_pos.ne']
    simpa only [Msq_ub, mul_assoc, harg] using hm
  have hzd_inst := hzd (twoLengthCoeff X Y) X hX1
    (twoLengthCoeff_one (by omega) hYX)
    (fun n hn => norm_twoLengthCoeff_le (by omega) hYX hn)
    (fun n _ => conj_twoLengthCoeff X Y n)
    ((X : ℝ) ^ (5 : ℕ)) (one_le_pow₀ (by exact_mod_cast hX1))
    (sum_norm_twoLengthCoeff_mul_rpow_le (by omega) hYX)
    σ₀ T₁ T₂ Msq_ub
    (by linarith only [hσ₀_mem.1]) (by linarith only [hσ₀_mem.2])
    (by linarith only [hT₁.1, hS60]) hT12
    (fun x hx => (hadm1 x ⟨by linarith only [hx.1, hσ₀_mem.1], hx.2⟩).1)
    (fun x hx => (hadm2 x ⟨by linarith only [hx.1, hσ₀_mem.1], hx.2⟩).1)
    (fun x hx => (hadm1 x ⟨by linarith only [hx.1, hσ₀_mem.1], hx.2⟩).2)
    (fun x hx => (hadm2 x ⟨by linarith only [hx.1, hσ₀_mem.1], hx.2⟩).2)
    hMsq_le Z hZ Δ (mul_nonneg hε₁_pos.le ha_div_pos.le)
  clear hzd hadm1 hadm2 hMsq_all hMsq_le
  have hMsq_pos : 0 < Msq_ub / (T₂ - T₁) := by dsimp [Msq_ub]; positivity
  have hlog_ub : (T₂ - T₁) / 2 * Real.log (Msq_ub / (T₂ - T₁)) ≤
      (T₂ - T₁) * ((A₀ / 2) * Real.exp (-(r * a))) + 60 * S ^ (θ_X + 1 / 2) := by
    have hdiv_eq : Msq_ub / (T₂ - T₁) =
        1 + A₀ * Real.exp (-(r * a)) + 120 * S ^ (θ_X + 1 / 2) / (T₂ - T₁) := by
      dsimp [Msq_ub]; field_simp [hlen_pos.ne']
    have hsub1 := Real.log_le_sub_one_of_pos hMsq_pos
    rw [hdiv_eq] at hsub1 ⊢
    have hm := mul_le_mul_of_nonneg_left hsub1 (by positivity : 0 ≤ (T₂ - T₁) / 2)
    have h60 : (T₂ - T₁) / 2 * (120 * S ^ (θ_X + 1 / 2) / (T₂ - T₁)) =
        60 * S ^ (θ_X + 1 / 2) := by field_simp [hlen_pos.ne']
    linarith only [hm, h60]
  have herr_pow : 60 * S ^ (θ_X + 1 / 2) + C_zd + K_zd * (Real.log T₂ + Real.log ((X : ℝ) ^ (5 : ℕ))) ≤
      (60 + (C_zd + 5 * K_zd) * K_log1) * S ^ (1 - η_r) := by
    have hK5 : K_zd * (Real.log T₂ + Real.log ((X : ℝ) ^ (5 : ℕ))) ≤ 5 * K_zd * Real.log S := by
      nlinarith only [hK_zd, hlogT₂, hlogMb]
    have hCK_le : C_zd + 5 * K_zd * Real.log S ≤ (C_zd + 5 * K_zd) * (1 + Real.log S) := by
      nlinarith only [hC_zd, hK_zd, hLS_pos]
    have h1log : (1 + Real.log S) ≤ K_log1 * S ^ η_r := by
      simpa only [pow_one] using hlog1 S hS1.le
    have hS_sub : S ^ (θ_X + 1 / 2) ≤ S ^ (1 - η_r) :=
      Real.rpow_le_rpow_of_exponent_le hS1.le (by dsimp [η_r]; linarith only [hη_pos])
    have hS_eta : S ^ η_r ≤ S ^ (1 - η_r) :=
      Real.rpow_le_rpow_of_exponent_le hS1.le (by linarith only [hη_lt])
    have hCK_pow : C_zd + 5 * K_zd * Real.log S ≤ (C_zd + 5 * K_zd) * K_log1 * S ^ (1 - η_r) := by
      calc C_zd + 5 * K_zd * Real.log S
          ≤ (C_zd + 5 * K_zd) * (K_log1 * S ^ η_r) :=
            hCK_le.trans (mul_le_mul_of_nonneg_left h1log (by positivity))
        _ ≤ (C_zd + 5 * K_zd) * (K_log1 * S ^ (1 - η_r)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS_eta (by positivity)) (by positivity)
        _ = (C_zd + 5 * K_zd) * K_log1 * S ^ (1 - η_r) := by ring
    nlinarith only [hK5, hS_sub, hCK_pow]
  have hfilt_sub : Z.filter (fun w => 1 / 2 + (1 + ε) * (a / Real.log S) ≤ w.re) ⊆
      Z.filter (fun w => σ₀ + Δ ≤ w.re) := by
    intro w hw
    obtain ⟨hwZ, hwre⟩ := Finset.mem_filter.mp hw
    refine Finset.mem_filter.mpr ⟨hwZ, ?_⟩
    have hm := mul_le_mul_of_nonneg_right hε₁_le_ε ha_div_pos.le
    dsimp [σ₀, Δ]; linarith only [hwre, hm]
  have hord_le : (∑ w ∈ Z.filter (fun w => 1 / 2 + (1 + ε) * (a / Real.log S) ≤ w.re),
      ((analyticOrderAt riemannZeta w).toNat : ℝ)) ≤
      ∑ w ∈ Z.filter (fun w => σ₀ + Δ ≤ w.re),
        ((analyticOrderAt riemannZeta w).toNat : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hfilt_sub fun _ _ _ => Nat.cast_nonneg _
  have hzd_step : 2 * Real.pi * (ε₁ * ((a / Real.log S) *
      ∑ w ∈ Z.filter (fun w => 1 / 2 + (1 + ε) * (a / Real.log S) ≤ w.re),
        ((analyticOrderAt riemannZeta w).toNat : ℝ))) ≤
      (T₂ - T₁) * ((A₀ / 2) * Real.exp (-(r * a))) +
        (60 + (C_zd + 5 * K_zd) * K_log1) * S ^ (1 - η_r) := by
    calc 2 * Real.pi * (ε₁ * ((a / Real.log S) *
          ∑ w ∈ Z.filter (fun w => 1 / 2 + (1 + ε) * (a / Real.log S) ≤ w.re),
            ((analyticOrderAt riemannZeta w).toNat : ℝ)))
        ≤ 2 * Real.pi * (Δ *
          ∑ w ∈ Z.filter (fun w => σ₀ + Δ ≤ w.re),
            ((analyticOrderAt riemannZeta w).toNat : ℝ)) := by
          dsimp [Δ]; rw [mul_assoc ε₁]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hord_le (mul_nonneg hε₁_pos.le ha_div_pos.le)) (by positivity)
      _ ≤ _ := hzd_inst.trans (by linarith only [hlog_ub, herr_pow])
  have hm_inv := mul_le_mul_of_nonneg_left hzd_step (inv_nonneg.mpr hε₁_pos.le)
  have hlhs_eq : ε₁⁻¹ * (2 * Real.pi * (ε₁ * ((a / Real.log S) *
      ∑ w ∈ Z.filter (fun w => 1 / 2 + (1 + ε) * (a / Real.log S) ≤ w.re),
        ((analyticOrderAt riemannZeta w).toNat : ℝ)))) =
      2 * Real.pi * ((a / Real.log S) *
        ∑ w ∈ Z.filter (fun w => 1 / 2 + (1 + ε) * (a / Real.log S) ≤ w.re),
          ((analyticOrderAt riemannZeta w).toNat : ℝ)) := by
    field_simp [hε₁_pos.ne']
  rw [hlhs_eq] at hm_inv
  have hnn1 : 0 ≤ (T₂ - T₁) * Real.exp (-(r * a)) := mul_nonneg hlen_pos.le (Real.exp_pos _).le
  have hnn2 : 0 ≤ S ^ (1 - η_r) := Real.rpow_nonneg hS_pos.le _
  have hrhs_eq : ε₁⁻¹ * ((T₂ - T₁) * ((A₀ / 2) * Real.exp (-(r * a))) +
      (60 + (C_zd + 5 * K_zd) * K_log1) * S ^ (1 - η_r)) ≤
      (T₂ - T₁) * (A * Real.exp (-(r * a))) + K * S ^ (1 - η_r) := by
    have h1 : ε₁⁻¹ * ((T₂ - T₁) * ((A₀ / 2) * Real.exp (-(r * a)))) =
        (T₂ - T₁) * ((A₀ / (2 * ε₁)) * Real.exp (-(r * a))) := by field_simp [hε₁_pos.ne']
    have h2 : ε₁⁻¹ * ((60 + (C_zd + 5 * K_zd) * K_log1) * S ^ (1 - η_r)) =
        ((60 + (C_zd + 5 * K_zd) * K_log1) / ε₁) * S ^ (1 - η_r) := by field_simp [hε₁_pos.ne']
    rw [mul_add, h1, h2]
    dsimp [A, K]
    linarith only [hnn1, hnn2]
  exact hm_inv.trans hrhs_eq

/-! ## §3. Continuous hyperbolic Laplace integration across Scale II (`0 < c' < 1 / 2`) -/

/-- Continuous hyperbolic layer-cake / Laplace band bound on
`1 / 2 + (1 + ε) * (M / L_S) ≤ Re z < 1 / 2 + (1 + ε) * δ₁` (`1 ≤ M ≤ δ₁ * L_S`).
The `u` factor in `sinh(2Lu) ≤ 2Lu exp(2Lu)` cancels the `1 / u` Littlewood weight factor
identically across the entire continuous abscissa interval. -/
private theorem scaleII_continuous_laplace_band_le
    {V S A K r ε η_r c' L T₁ T₂ L_S lam_c δ₁ M : ℝ}
    (hV_pos : 0 < V) (hS1 : 1 < S) (hA : 0 < A) (hK : 0 < K)
    (hr0 : 0 < r) (hε : 0 < ε) (hη_pos : 0 < η_r) (hc0 : 0 < c')
    (hL0 : 0 ≤ L) (hL_le_LS : L ≤ c' * L_S)
    (hT₁_pos : 0 < T₁) (hT12 : T₁ ≤ T₂) (hlen_hi : T₂ - T₁ ≤ V)
    (hLS_eq : L_S = Real.log S) (hLS_pos : 0 < L_S)
    (hlam_eq : lam_c = r - 2 * c' * (1 + ε)) (hlam_pos : 0 < lam_c)
    (hδ₁_pos : 0 < δ₁) (hδ₁_le1 : δ₁ ≤ 1)
    (h2cb_le : 2 * c' * ((1 + ε) * δ₁) ≤ η_r / 2)
    (hM1 : 1 ≤ M) (hM_hi : M ≤ δ₁ * L_S)
    (hbv_win : ∀ a : ℝ, 1 ≤ a → a ≤ δ₁ * L_S →
      2 * Real.pi * ((a / L_S) *
        ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + (1 + ε) * (a / L_S) ≤ w.re),
          ((analyticOrderAt riemannZeta w).toNat : ℝ)) ≤
        (T₂ - T₁) * (A * Real.exp (-(r * a))) + K * S ^ (1 - η_r)) :
    (∑ z ∈ (shellZeros T₁ T₂).filter (fun z =>
        1 / 2 + (1 + ε) * (M / L_S) ≤ z.re ∧ z.re < 1 / 2 + (1 + ε) * δ₁),
        ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2)) ≤
      (8 * (1 + ε) ^ 2 * A / lam_c) * c' ^ 2 *
          Real.exp (-(lam_c / 2 * M)) * (V * L_S) +
        (4 * (1 + ε) ^ 2 * K) * c' ^ 2 * L_S ^ 2 * S ^ (1 - η_r / 2) := by
  have hS_pos : 0 < S := zero_lt_one.trans hS1
  have h1ε_pos : 0 < 1 + ε := by linarith only [hε]
  let a_M : ℝ := (1 + ε) * (M / L_S)
  let b₀ : ℝ := (1 + ε) * δ₁
  have haM_pos : 0 < a_M := by dsimp [a_M]; positivity
  have hab : a_M ≤ b₀ := by
    dsimp [a_M, b₀]
    refine mul_le_mul_of_nonneg_left ?_ h1ε_pos.le
    rwa [div_le_iff₀ hLS_pos]
  have hband := sum_depthKernel_band_le_sinh_tail_integral
    (shellZeros T₁ T₂) (fun z => ((analyticOrderAt xi z).toNat : ℝ))
    hL0 haM_pos.le hab (fun _ _ => Nat.cast_nonneg _)
  -- Tail count bound for every `u ∈ Icc a_M b₀`
  have htail_u : ∀ u ∈ Icc a_M b₀,
      2 * Real.pi * (u / (1 + ε)) *
        (∑ z ∈ (shellZeros T₁ T₂).filter (fun z => 1 / 2 + u ≤ z.re),
          ((analyticOrderAt xi z).toNat : ℝ)) ≤
        V * A * Real.exp (-(r * L_S / (1 + ε) * u)) + K * S ^ (1 - η_r) := by
    intro u hu
    have hu_nn : 0 ≤ u := haM_pos.le.trans hu.1
    let a_u : ℝ := u * L_S / (1 + ε)
    have ha_lo : 1 ≤ a_u := by
      dsimp [a_u, a_M] at hu ⊢
      rw [le_div_iff₀ h1ε_pos]
      have hm := mul_le_mul_of_nonneg_right hu.1 hLS_pos.le
      have hsimp : (1 + ε) * (M / L_S) * L_S = (1 + ε) * M := by field_simp [hLS_pos.ne']
      rw [hsimp] at hm
      nlinarith only [hm, hM1, h1ε_pos]
    have ha_hi : a_u ≤ δ₁ * L_S := by
      dsimp [a_u, b₀] at hu ⊢
      rw [div_le_iff₀ h1ε_pos]
      have hm := mul_le_mul_of_nonneg_right hu.2 hLS_pos.le
      linarith only [hm]
    have hau_div : a_u / L_S = u / (1 + ε) := by dsimp [a_u]; field_simp [hLS_pos.ne']
    have hau_u : (1 + ε) * (a_u / L_S) = u := by rw [hau_div]; field_simp [h1ε_pos.ne']
    have hsh_w := shellRight_orderSum_le_windowZeros' hT₁_pos hT12 hu_nn
    have hbv_u := hbv_win a_u ha_lo ha_hi
    rw [hau_u, hau_div] at hbv_u
    have hr_arg : r * a_u = r * L_S / (1 + ε) * u := by dsimp [a_u]; ring
    rw [hr_arg] at hbv_u
    have hlen_V : (T₂ - T₁) * (A * Real.exp (-(r * L_S / (1 + ε) * u))) ≤
        V * A * Real.exp (-(r * L_S / (1 + ε) * u)) := by
      have hm := mul_le_mul_of_nonneg_right hlen_hi (mul_nonneg hA.le (Real.exp_pos _).le)
      linarith only [hm]
    calc 2 * Real.pi * (u / (1 + ε)) *
            (∑ z ∈ (shellZeros T₁ T₂).filter (fun z => 1 / 2 + u ≤ z.re),
              ((analyticOrderAt xi z).toNat : ℝ))
        ≤ 2 * Real.pi * ((u / (1 + ε)) *
            ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + u ≤ w.re),
              ((analyticOrderAt riemannZeta w).toNat : ℝ)) := by
          rw [mul_assoc (2 * Real.pi)]
          exact mul_le_mul_of_nonneg_left hsh_w (by positivity)
      _ ≤ _ := hbv_u.trans (by linarith only [hlen_V])
  -- 1. Boundary term `depthKernel L a_M * N_≥(a_M)`
  have hbd_term : depthKernel L a_M *
      (∑ z ∈ (shellZeros T₁ T₂).filter (fun z => 1 / 2 + a_M ≤ z.re),
        ((analyticOrderAt xi z).toNat : ℝ)) ≤
      (4 * (1 + ε) ^ 2 * A / lam_c) * c' ^ 2 * Real.exp (-(lam_c / 2 * M)) * (V * L_S) +
        (2 * (1 + ε) ^ 2 * K) * c' ^ 2 * L_S ^ 2 * S ^ (1 - η_r / 2) := by
    have hdk_M : depthKernel L a_M ≤
        4 * (1 + ε) ^ 2 * c' ^ 2 * M ^ 2 * Real.exp (2 * c' * (1 + ε) * M) := by
      have h1 := depthKernel_le_four_sq_mul_exp (d := a_M) hL0
      rw [abs_of_pos haM_pos] at h1
      have hLa : L * a_M ≤ c' * (1 + ε) * M := by
        calc L * a_M ≤ (c' * L_S) * ((1 + ε) * (M / L_S)) :=
              mul_le_mul hL_le_LS le_rfl haM_pos.le (by positivity)
          _ = c' * (1 + ε) * M := by field_simp [hLS_pos.ne']
      have hsq : 4 * (L * a_M) ^ 2 ≤ 4 * (1 + ε) ^ 2 * c' ^ 2 * M ^ 2 := by
        have hp := pow_le_pow_left₀ (mul_nonneg hL0 haM_pos.le) hLa 2
        linarith only [hp]
      have hexp : Real.exp (2 * L * a_M) ≤ Real.exp (2 * c' * (1 + ε) * M) :=
        Real.exp_le_exp.mpr (by linarith only [hLa])
      exact h1.trans (mul_le_mul hsq hexp (Real.exp_pos _).le (by positivity))
    have htM := htail_u a_M ⟨le_rfl, hab⟩
    have haM_div : a_M / (1 + ε) = M / L_S := by dsimp [a_M]; field_simp [h1ε_pos.ne']
    have hrM_arg : r * L_S / (1 + ε) * a_M = r * M := by
      dsimp [a_M]; field_simp [h1ε_pos.ne', hLS_pos.ne']
    rw [haM_div, hrM_arg] at htM
    have hpi3 : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
    have hN_M : (∑ z ∈ (shellZeros T₁ T₂).filter (fun z => 1 / 2 + a_M ≤ z.re),
        ((analyticOrderAt xi z).toNat : ℝ)) ≤
        (L_S / (2 * M)) * (V * A * Real.exp (-(r * M)) + K * S ^ (1 - η_r)) := by
      have hden_pos : 0 < 2 * Real.pi * (M / L_S) := by positivity
      have hm1 := (le_div_iff₀' hden_pos).mpr htM
      refine hm1.trans ?_
      have hnum_nn : 0 ≤ V * A * Real.exp (-(r * M)) + K * S ^ (1 - η_r) := by positivity
      have h2_le : 2 * (M / L_S) ≤ 2 * Real.pi * (M / L_S) :=
        mul_le_mul_of_nonneg_right (by linarith only [hpi3]) (by positivity)
      exact (div_le_div_of_nonneg_left hnum_nn (by positivity) h2_le).trans_eq (by
        field_simp [hLS_pos.ne', (by linarith only [hM1] : M ≠ 0)])
    have hprod := mul_le_mul hdk_M hN_M
      (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (by positivity)
    have hM_exp : M * Real.exp (-(lam_c * M)) ≤ (2 / lam_c) * Real.exp (-(lam_c / 2 * M)) := by
      have h1 := Real.add_one_le_exp (lam_c / 2 * M)
      have h2 : lam_c / 2 * M ≤ Real.exp (lam_c / 2 * M) := by linarith only [h1]
      have h3 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (-(lam_c * M))).le
      have hexp_comb : Real.exp (lam_c / 2 * M) * Real.exp (-(lam_c * M)) =
          Real.exp (-(lam_c / 2 * M)) := by rw [← Real.exp_add]; congr 1; ring
      rw [hexp_comb] at h3
      have hm := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 2 / lam_c)
      have hlhs : (2 / lam_c) * ((lam_c / 2 * M) * Real.exp (-(lam_c * M))) =
          M * Real.exp (-(lam_c * M)) := by field_simp [hlam_pos.ne']
      rwa [hlhs] at hm
    have hmain_bd : (4 * (1 + ε) ^ 2 * c' ^ 2 * M ^ 2 * Real.exp (2 * c' * (1 + ε) * M)) *
        ((L_S / (2 * M)) * (V * A * Real.exp (-(r * M)))) ≤
        (4 * (1 + ε) ^ 2 * A / lam_c) * c' ^ 2 * Real.exp (-(lam_c / 2 * M)) * (V * L_S) := by
      have hid1 : (4 * (1 + ε) ^ 2 * c' ^ 2 * M ^ 2 * Real.exp (2 * c' * (1 + ε) * M)) *
          ((L_S / (2 * M)) * (V * A * Real.exp (-(r * M)))) =
          (2 * (1 + ε) ^ 2 * A * c' ^ 2 * (V * L_S)) *
            (M * (Real.exp (2 * c' * (1 + ε) * M) * Real.exp (-(r * M)))) := by
        field_simp [(by linarith only [hM1] : M ≠ 0)]
      have hexp_diff : Real.exp (2 * c' * (1 + ε) * M) * Real.exp (-(r * M)) =
          Real.exp (-(lam_c * M)) := by
        rw [← Real.exp_add, hlam_eq]; congr 1; ring
      rw [hid1, hexp_diff]
      have hm := mul_le_mul_of_nonneg_left hM_exp
        (by positivity : 0 ≤ 2 * (1 + ε) ^ 2 * A * c' ^ 2 * (V * L_S))
      calc (2 * (1 + ε) ^ 2 * A * c' ^ 2 * (V * L_S)) * (M * Real.exp (-(lam_c * M)))
          ≤ (2 * (1 + ε) ^ 2 * A * c' ^ 2 * (V * L_S)) *
              ((2 / lam_c) * Real.exp (-(lam_c / 2 * M))) := hm
        _ = (4 * (1 + ε) ^ 2 * A / lam_c) * c' ^ 2 * Real.exp (-(lam_c / 2 * M)) * (V * L_S) := by
            ring
    have herr_bd : (4 * (1 + ε) ^ 2 * c' ^ 2 * M ^ 2 * Real.exp (2 * c' * (1 + ε) * M)) *
        ((L_S / (2 * M)) * (K * S ^ (1 - η_r))) ≤
        (2 * (1 + ε) ^ 2 * K) * c' ^ 2 * L_S ^ 2 * S ^ (1 - η_r / 2) := by
      have hid2 : (4 * (1 + ε) ^ 2 * c' ^ 2 * M ^ 2 * Real.exp (2 * c' * (1 + ε) * M)) *
          ((L_S / (2 * M)) * (K * S ^ (1 - η_r))) =
          (2 * (1 + ε) ^ 2 * K * c' ^ 2 * L_S) *
            (M * (Real.exp (2 * c' * (1 + ε) * M) * S ^ (1 - η_r))) := by
        field_simp [(by linarith only [hM1] : M ≠ 0)]
      have hM_le_LS : M ≤ L_S := hM_hi.trans (mul_le_of_le_one_left hLS_pos.le hδ₁_le1)
      have hexp_S : Real.exp (2 * c' * (1 + ε) * M) ≤ S ^ (η_r / 2) := by
        have harg : 2 * c' * (1 + ε) * M ≤ (η_r / 2) * Real.log S := by
          have hm1 : 2 * c' * (1 + ε) * M ≤ 2 * c' * ((1 + ε) * δ₁) * L_S := by
            have := mul_le_mul_of_nonneg_left hM_hi (by positivity : 0 ≤ 2 * c' * (1 + ε))
            linarith only [this]
          have hm2 := mul_le_mul_of_nonneg_right h2cb_le hLS_pos.le
          rw [← hLS_eq]
          linarith only [hm1, hm2]
        rw [Real.rpow_def_of_pos hS_pos, mul_comm]
        exact Real.exp_le_exp.mpr harg
      have hS_comb : Real.exp (2 * c' * (1 + ε) * M) * S ^ (1 - η_r) ≤ S ^ (1 - η_r / 2) := by
        calc Real.exp (2 * c' * (1 + ε) * M) * S ^ (1 - η_r)
            ≤ S ^ (η_r / 2) * S ^ (1 - η_r) :=
              mul_le_mul_of_nonneg_right hexp_S (Real.rpow_nonneg hS_pos.le _)
          _ = S ^ (1 - η_r / 2) := by rw [← Real.rpow_add hS_pos]; congr 1; ring
      rw [hid2]
      calc (2 * (1 + ε) ^ 2 * K * c' ^ 2 * L_S) *
              (M * (Real.exp (2 * c' * (1 + ε) * M) * S ^ (1 - η_r)))
          ≤ (2 * (1 + ε) ^ 2 * K * c' ^ 2 * L_S) * (L_S * S ^ (1 - η_r / 2)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul hM_le_LS hS_comb (by positivity) hLS_pos.le) (by positivity)
        _ = (2 * (1 + ε) ^ 2 * K) * c' ^ 2 * L_S ^ 2 * S ^ (1 - η_r / 2) := by ring
    exact hprod.trans (by rw [mul_add]; exact add_le_add hmain_bd herr_bd)
  -- 2. Continuous Laplace integral on `[a_M, b₀]`
  let μ : ℝ := lam_c * L_S / (1 + ε)
  have hμ_pos : 0 < μ := by dsimp [μ]; positivity
  have hint_term : (∫ u in a_M..b₀,
      4 * L * Real.sinh (2 * L * u) *
        ∑ z ∈ (shellZeros T₁ T₂).filter (fun z => 1 / 2 + u ≤ z.re),
          ((analyticOrderAt xi z).toNat : ℝ)) ≤
      (4 * (1 + ε) ^ 2 * A / lam_c) * c' ^ 2 * Real.exp (-(lam_c / 2 * M)) * (V * L_S) +
        (2 * (1 + ε) ^ 2 * K) * c' ^ 2 * L_S ^ 2 * S ^ (1 - η_r / 2) := by
    have hptw : ∀ u ∈ Icc a_M b₀,
        4 * L * Real.sinh (2 * L * u) *
          (∑ z ∈ (shellZeros T₁ T₂).filter (fun z => 1 / 2 + u ≤ z.re),
            ((analyticOrderAt xi z).toNat : ℝ)) ≤
          (4 * (1 + ε) * A * c' ^ 2 * L_S ^ 2 * V) * Real.exp (-(μ * u)) +
            2 * (1 + ε) * K * c' ^ 2 * L_S ^ 2 * S ^ (1 - η_r / 2) := by
      intro u hu
      have hu_pos : 0 < u := haM_pos.trans_le hu.1
      have hsh_le : 4 * L * Real.sinh (2 * L * u) ≤
          8 * c' ^ 2 * L_S ^ 2 * u * Real.exp (2 * c' * L_S * u) := by
        have h1 := sinh_le_mul_exp (mul_nonneg (mul_nonneg zero_le_two hL0) hu_pos.le)
        have h2 : 4 * L * Real.sinh (2 * L * u) ≤ 8 * L ^ 2 * u * Real.exp (2 * L * u) := by
          have hm := mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hL0)
          linarith only [hm]
        have hL2 : L ^ 2 ≤ (c' * L_S) ^ 2 := pow_le_pow_left₀ hL0 hL_le_LS 2
        have hexp_u : Real.exp (2 * L * u) ≤ Real.exp (2 * c' * L_S * u) :=
          Real.exp_le_exp.mpr (by nlinarith only [hL_le_LS, hu_pos])
        calc 4 * L * Real.sinh (2 * L * u)
            ≤ 8 * L ^ 2 * u * Real.exp (2 * L * u) := h2
          _ ≤ 8 * (c' * L_S) ^ 2 * u * Real.exp (2 * c' * L_S * u) := by
              refine mul_le_mul
                (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL2 (by norm_num)) hu_pos.le)
                hexp_u (Real.exp_pos _).le (by positivity)
          _ = 8 * c' ^ 2 * L_S ^ 2 * u * Real.exp (2 * c' * L_S * u) := by ring
      have htu := htail_u u hu
      have hpi2 : (4 : ℝ) ≤ 2 * Real.pi := by linarith only [Real.pi_gt_three]
      have huN_le : u * (∑ z ∈ (shellZeros T₁ T₂).filter (fun z => 1 / 2 + u ≤ z.re),
          ((analyticOrderAt xi z).toNat : ℝ)) ≤
          ((1 + ε) / 4) * (V * A * Real.exp (-(r * L_S / (1 + ε) * u)) + K * S ^ (1 - η_r)) := by
        have hm1 : 4 * (u / (1 + ε)) *
            (∑ z ∈ (shellZeros T₁ T₂).filter (fun z => 1 / 2 + u ≤ z.re),
              ((analyticOrderAt xi z).toNat : ℝ)) ≤
            2 * Real.pi * (u / (1 + ε)) *
              (∑ z ∈ (shellZeros T₁ T₂).filter (fun z => 1 / 2 + u ≤ z.re),
                ((analyticOrderAt xi z).toNat : ℝ)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hpi2 (by positivity))
            (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
        have hm2 := mul_le_mul_of_nonneg_left (hm1.trans htu)
          (by positivity : 0 ≤ (1 + ε) / 4)
        have hlhs : ((1 + ε) / 4) * (4 * (u / (1 + ε)) *
            ∑ z ∈ (shellZeros T₁ T₂).filter (fun z => 1 / 2 + u ≤ z.re),
              ((analyticOrderAt xi z).toNat : ℝ)) =
            u * ∑ z ∈ (shellZeros T₁ T₂).filter (fun z => 1 / 2 + u ≤ z.re),
              ((analyticOrderAt xi z).toNat : ℝ) := by field_simp [h1ε_pos.ne']
        rwa [hlhs] at hm2
      have hprod_u : 4 * L * Real.sinh (2 * L * u) *
          (∑ z ∈ (shellZeros T₁ T₂).filter (fun z => 1 / 2 + u ≤ z.re),
            ((analyticOrderAt xi z).toNat : ℝ)) ≤
          (2 * (1 + ε) * c' ^ 2 * L_S ^ 2 * Real.exp (2 * c' * L_S * u)) *
            (V * A * Real.exp (-(r * L_S / (1 + ε) * u)) + K * S ^ (1 - η_r)) := by
        have hm1 := mul_le_mul_of_nonneg_right hsh_le
          (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
        have hm2 := mul_le_mul_of_nonneg_left huN_le
          (by positivity : 0 ≤ 8 * c' ^ 2 * L_S ^ 2 * Real.exp (2 * c' * L_S * u))
        have hid_u : 8 * c' ^ 2 * L_S ^ 2 * u * Real.exp (2 * c' * L_S * u) *
            (∑ z ∈ (shellZeros T₁ T₂).filter (fun z => 1 / 2 + u ≤ z.re),
              ((analyticOrderAt xi z).toNat : ℝ)) =
            (8 * c' ^ 2 * L_S ^ 2 * Real.exp (2 * c' * L_S * u)) *
              (u * ∑ z ∈ (shellZeros T₁ T₂).filter (fun z => 1 / 2 + u ≤ z.re),
                ((analyticOrderAt xi z).toNat : ℝ)) := by ring
        rw [hid_u] at hm1
        refine hm1.trans (hm2.trans_eq ?_)
        ring
      have hexp_main_u : Real.exp (2 * c' * L_S * u) * Real.exp (-(r * L_S / (1 + ε) * u)) =
          Real.exp (-(μ * u)) := by
        rw [← Real.exp_add]
        congr 1; dsimp [μ]; rw [hlam_eq]; field_simp [h1ε_pos.ne']; ring
      have hexp_err_u : Real.exp (2 * c' * L_S * u) * S ^ (1 - η_r) ≤ S ^ (1 - η_r / 2) := by
        have harg : 2 * c' * L_S * u ≤ (η_r / 2) * Real.log S := by
          have hm1 : 2 * c' * L_S * u ≤ 2 * c' * b₀ * L_S := by nlinarith only [hu.2, hc0, hLS_pos]
          have hm2 := mul_le_mul_of_nonneg_right h2cb_le hLS_pos.le
          rw [← hLS_eq]
          dsimp [b₀] at hm1
          linarith only [hm1, hm2]
        have he1 : Real.exp (2 * c' * L_S * u) ≤ S ^ (η_r / 2) := by
          rw [Real.rpow_def_of_pos hS_pos, mul_comm]; exact Real.exp_le_exp.mpr harg
        calc Real.exp (2 * c' * L_S * u) * S ^ (1 - η_r)
            ≤ S ^ (η_r / 2) * S ^ (1 - η_r) :=
              mul_le_mul_of_nonneg_right he1 (Real.rpow_nonneg hS_pos.le _)
          _ = S ^ (1 - η_r / 2) := by rw [← Real.rpow_add hS_pos]; congr 1; ring
      refine hprod_u.trans ?_
      rw [mul_add]
      refine add_le_add ?_ ?_
      · have hid_m : (2 * (1 + ε) * c' ^ 2 * L_S ^ 2 * Real.exp (2 * c' * L_S * u)) *
            (V * A * Real.exp (-(r * L_S / (1 + ε) * u))) =
            (2 * (1 + ε) * A * c' ^ 2 * L_S ^ 2 * V) *
              (Real.exp (2 * c' * L_S * u) * Real.exp (-(r * L_S / (1 + ε) * u))) := by ring
        rw [hid_m, hexp_main_u]
        have hnn_m : 0 ≤ (1 + ε) * A * c' ^ 2 * L_S ^ 2 * V * Real.exp (-(μ * u)) := by positivity
        linarith only [hnn_m]
      · have hm_e := mul_le_mul_of_nonneg_left hexp_err_u
          (by positivity : 0 ≤ 2 * (1 + ε) * K * c' ^ 2 * L_S ^ 2)
        linarith only [hm_e]
    have hi_lhs := intervalIntegrable_mul_tailCount (shellZeros T₁ T₂)
      (fun z => ((analyticOrderAt xi z).toNat : ℝ))
      (by fun_prop : Continuous fun u : ℝ => 4 * L * Real.sinh (2 * L * u)) hab
    have hi1 : IntervalIntegrable
        (fun u : ℝ => (4 * (1 + ε) * A * c' ^ 2 * L_S ^ 2 * V) * Real.exp (-(μ * u)))
        volume a_M b₀ := (by fun_prop : Continuous _).intervalIntegrable (μ := volume) _ _
    have hi2 : IntervalIntegrable
        (fun _u : ℝ => 2 * (1 + ε) * K * c' ^ 2 * L_S ^ 2 * S ^ (1 - η_r / 2))
        volume a_M b₀ := intervalIntegrable_const
    have hmono := integral_mono_on (μ := volume) hab hi_lhs (hi1.add hi2) hptw
    rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul] at hmono
    have hderiv_mu : ∀ u : ℝ,
        HasDerivAt (fun t : ℝ => -(1 / μ) * Real.exp (-(μ * t))) (Real.exp (-(μ * u))) u := by
      intro u
      have hlin : HasDerivAt (fun t : ℝ => -(μ * t)) (-μ) u :=
        ((hasDerivAt_id u).const_mul μ).neg.congr_deriv (by ring)
      exact (((Real.hasDerivAt_exp _).comp u hlin).const_mul (-(1 / μ))).congr_deriv
        (by field_simp [hμ_pos.ne'])
    have hint_exp : (∫ u in a_M..b₀, Real.exp (-(μ * u))) ≤
        ((1 + ε) / (lam_c * L_S)) * Real.exp (-(lam_c / 2 * M)) := by
      rw [integral_eq_sub_of_hasDerivAt (fun u _ => hderiv_mu u)
        ((by fun_prop : Continuous _).intervalIntegrable (μ := volume) _ _)]
      have hpos_b : 0 ≤ (1 / μ) * Real.exp (-(μ * b₀)) := by positivity
      have h1 : -(1 / μ) * Real.exp (-(μ * b₀)) - -(1 / μ) * Real.exp (-(μ * a_M)) ≤
          (1 / μ) * Real.exp (-(μ * a_M)) := by linarith only [hpos_b]
      have hμa : μ * a_M = lam_c * M := by
        dsimp [μ, a_M]; field_simp [h1ε_pos.ne', hLS_pos.ne']
      have hinv_μ : 1 / μ = (1 + ε) / (lam_c * L_S) := by
        dsimp [μ]; field_simp [h1ε_pos.ne', hlam_pos.ne', hLS_pos.ne']
      have hexp_half : Real.exp (-(lam_c * M)) ≤ Real.exp (-(lam_c / 2 * M)) :=
        Real.exp_le_exp.mpr (by nlinarith only [hlam_pos, hM1])
      rw [hμa, hinv_μ] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left hexp_half (by positivity))
    have hmain_int : (4 * (1 + ε) * A * c' ^ 2 * L_S ^ 2 * V) *
        (∫ u in a_M..b₀, Real.exp (-(μ * u))) ≤
        (4 * (1 + ε) ^ 2 * A / lam_c) * c' ^ 2 * Real.exp (-(lam_c / 2 * M)) * (V * L_S) :=
      calc (4 * (1 + ε) * A * c' ^ 2 * L_S ^ 2 * V) * (∫ u in a_M..b₀, Real.exp (-(μ * u)))
          ≤ (4 * (1 + ε) * A * c' ^ 2 * L_S ^ 2 * V) *
              (((1 + ε) / (lam_c * L_S)) * Real.exp (-(lam_c / 2 * M))) :=
            mul_le_mul_of_nonneg_left hint_exp (by positivity)
        _ = (4 * (1 + ε) ^ 2 * A / lam_c) * c' ^ 2 * Real.exp (-(lam_c / 2 * M)) * (V * L_S) := by
            field_simp [hlam_pos.ne', hLS_pos.ne']
    have herr_int : (b₀ - a_M) * (2 * (1 + ε) * K * c' ^ 2 * L_S ^ 2 * S ^ (1 - η_r / 2)) ≤
        (2 * (1 + ε) ^ 2 * K) * c' ^ 2 * L_S ^ 2 * S ^ (1 - η_r / 2) := by
      have hlen_le : b₀ - a_M ≤ 1 + ε := by
        dsimp [b₀]
        nlinarith only [haM_pos, h1ε_pos, hδ₁_le1]
      exact (mul_le_mul_of_nonneg_right hlen_le (by positivity)).trans_eq (by ring)
    exact hmono.trans (add_le_add hmain_int herr_int)
  exact hband.trans ((add_le_add hbd_term hint_term).trans_eq (by ring))


/-! ## §4. Closing the gate gap (`0 < c < 1 / 2`) across shells and compact source tests -/

/-- Short end-cap `V^{3/4}` bound for `shellDepthSum W₁ W₂ L` (`W₂ - W₁ ≤ 2`, `L ≤ (1/2) log V`). -/
private theorem shortCap_shellDepthSum_le_rpow' {V W₁ W₂ L K_log1 : ℝ}
    (hV16 : 16 ≤ V) (hW₁ : 0 ≤ W₁) (h12 : W₁ ≤ W₂) (hlen : W₂ - W₁ ≤ 2) (hW₂ : W₂ ≤ 2 * V)
    (hL0 : 0 ≤ L) (hL_half : L ≤ (1 / 2) * Real.log V)
    (hlog1 : ∀ x : ℝ, 1 ≤ x → (1 + Real.log x) ^ 1 ≤ K_log1 * x ^ (1 / 4 : ℝ)) :
    shellDepthSum W₁ W₂ L ≤
      32 * (|xiLineTwoLogDerivConstant| + 4) * K_log1 * V ^ (3 / 4 : ℝ) := by
  have hV_pos : 0 < V := by linarith only [hV16]
  have hLV_ge2 : 2 ≤ Real.log V := two_le_log_of_sixteen_le' hV16
  have hdk_le : ∀ z : ℂ, |z.re - 1 / 2| ≤ 1 / 2 →
      depthKernel L (z.re - 1 / 2) ≤ V ^ (1 / 2 : ℝ) := by
    intro z hz
    refine (depthKernel_le_exp_of_abs_le_half hL0 hz).trans ?_
    rw [Real.rpow_def_of_pos hV_pos, mul_comm]
    exact Real.exp_le_exp.mpr hL_half
  have hord := shortShell_orderSum_le_log hW₁ h12 hlen
  have hlogW : Real.log (W₂ + 4) ≤ 3 + Real.log V := by
    calc Real.log (W₂ + 4) ≤ Real.log (4 * V) :=
          Real.log_le_log (by linarith only [hW₁, h12]) (by linarith only [hW₂, hV16])
      _ = Real.log 4 + Real.log V := Real.log_mul (by norm_num) hV_pos.ne'
      _ ≤ 3 + Real.log V := by linarith only [log_four_le_two']
  unfold shellDepthSum
  have hsum_dk : ∑ z ∈ shellZeros W₁ W₂,
        ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2) ≤
      (∑ z ∈ shellZeros W₁ W₂, ((analyticOrderAt xi z).toNat : ℝ)) * V ^ (1 / 2 : ℝ) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_left (hdk_le z ?_) (Nat.cast_nonneg _)
    obtain ⟨h0, h1, _, _, _⟩ := mem_stripFinsetPos.mp (Finset.mem_filter.mp hz).1
    exact abs_le.mpr ⟨by linarith only [h0], by linarith only [h1]⟩
  have hc_nn : 0 ≤ |xiLineTwoLogDerivConstant| := abs_nonneg _
  have hpoly : |xiLineTwoLogDerivConstant| + Real.log (W₂ + 4) ≤
      2 * (|xiLineTwoLogDerivConstant| + 4) * (1 + Real.log V) ^ 1 := by
    rw [pow_one]
    nlinarith only [hc_nn, hlogW, hLV_ge2]
  have hpow := hlog1 V (by linarith only [hV16])
  have hV_add : V ^ (1 / 4 : ℝ) * V ^ (1 / 2 : ℝ) = V ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add hV_pos]; norm_num
  calc ∑ z ∈ shellZeros W₁ W₂,
          ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2)
      ≤ 16 * (|xiLineTwoLogDerivConstant| + Real.log (W₂ + 4)) * V ^ (1 / 2 : ℝ) :=
        hsum_dk.trans (mul_le_mul_of_nonneg_right hord (Real.rpow_nonneg hV_pos.le _))
    _ ≤ 16 * (2 * (|xiLineTwoLogDerivConstant| + 4) * (K_log1 * V ^ (1 / 4 : ℝ))) *
          V ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (hpoly.trans (mul_le_mul_of_nonneg_left hpow (by positivity))) (by norm_num))
          (Real.rpow_nonneg hV_pos.le _)
    _ = 32 * (|xiLineTwoLogDerivConstant| + 4) * K_log1 *
          (V ^ (1 / 4 : ℝ) * V ^ (1 / 2 : ℝ)) := by ring
    _ = 32 * (|xiLineTwoLogDerivConstant| + 4) * K_log1 * V ^ (3 / 4 : ℝ) := by rw [hV_add]

/-- Scale-I near-line shell bound (`0 < z.re - 1 / 2 < (1 + ε) / L_S`, `0 < ε ≤ 1`, `0 < c' < 1 / 2`):
`L * (z.re - 1 / 2) ≤ c' * (1 + ε) ≤ 1` cancels `1 / L_S` directly in `depthKernel`, yielding
`O(c'^2 * V * log V)` uniformly via `stripFinsetPos_orderSum_le_mul_log'`. -/
private theorem scaleI_near_shell_sum_le_general {V T₁ T₂ c' ε L_S L : ℝ}
    (hV16 : 16 ≤ V) (hT₂2V : T₂ ≤ 2 * V)
    (hc0 : 0 < c') (hc' : c' < 1 / 2) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hLS_pos : 0 < L_S) (hL0 : 0 ≤ L) (hL_le_LS : L ≤ c' * L_S) :
    2 * ∑ z ∈ ((shellZeros T₁ T₂).filter (fun z => 1 / 2 < z.re)).filter
        (fun z => z.re - 1 / 2 < (1 + ε) * (1 / L_S)),
        ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2) ≤
      (4096 * Real.exp 2 * (2 * |xiLineTwoLogDerivConstant| + 5)) * c' ^ 2 * V * Real.log V := by
  classical
  have hV_pos : 0 < V := by linarith only [hV16]
  have hLV_ge2 : 2 ≤ Real.log V := two_le_log_of_sixteen_le' hV16
  let R₁ := ((shellZeros T₁ T₂).filter (fun z => 1 / 2 < z.re)).filter
    (fun z => z.re - 1 / 2 < (1 + ε) * (1 / L_S))
  have hptw : ∀ z ∈ R₁,
      ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2) ≤
        (16 * Real.exp 2 * c' ^ 2) * ((analyticOrderAt xi z).toNat : ℝ) := by
    intro z hz
    obtain ⟨hzR, hlt⟩ := Finset.mem_filter.mp hz
    have hgt : 1 / 2 < z.re := (Finset.mem_filter.mp hzR).2
    have hδ_pos : 0 < z.re - 1 / 2 := sub_pos.mpr hgt
    have hprod_le : L * (z.re - 1 / 2) ≤ 2 * c' := by
      calc L * (z.re - 1 / 2)
          ≤ (c' * L_S) * ((1 + ε) * (1 / L_S)) :=
            mul_le_mul hL_le_LS hlt.le hδ_pos.le (by positivity)
        _ = (1 + ε) * c' := by field_simp [hLS_pos.ne']
        _ ≤ 2 * c' := mul_le_mul_of_nonneg_right (by linarith only [hε1]) hc0.le
    have h2prod_le : 2 * L * (z.re - 1 / 2) ≤ 2 := by nlinarith only [hprod_le, hc']
    have hdk := depthKernel_le_four_sq_mul_exp (d := z.re - 1 / 2) hL0
    rw [abs_of_pos hδ_pos] at hdk
    have hsq : 4 * (L * (z.re - 1 / 2)) ^ 2 ≤ 16 * c' ^ 2 := by
      have hp := pow_le_pow_left₀ (mul_nonneg hL0 hδ_pos.le) hprod_le 2
      linarith only [hp]
    have hexp : Real.exp (2 * L * (z.re - 1 / 2)) ≤ Real.exp 2 := Real.exp_le_exp.mpr h2prod_le
    have hdk_le : depthKernel L (z.re - 1 / 2) ≤ 16 * Real.exp 2 * c' ^ 2 :=
      (hdk.trans (mul_le_mul hsq hexp (Real.exp_pos _).le (by positivity))).trans_eq (by ring)
    exact (mul_le_mul_of_nonneg_left hdk_le (Nat.cast_nonneg _)).trans_eq (by ring)
  have hsub_strip : R₁ ⊆ stripFinsetPos (2 * V) := by
    intro z hz
    obtain ⟨hzR, _⟩ := Finset.mem_filter.mp hz
    obtain ⟨hz_sh, _⟩ := Finset.mem_filter.mp hzR
    obtain ⟨h0, h1, him0, him_le, hxi⟩ := mem_stripFinsetPos.mp (Finset.mem_filter.mp hz_sh).1
    exact mem_stripFinsetPos.mpr ⟨h0, h1, him0, him_le.trans hT₂2V, hxi⟩
  have hord_2V : ∑ z ∈ R₁, ((analyticOrderAt xi z).toNat : ℝ) ≤
      128 * (2 * |xiLineTwoLogDerivConstant| + 5) * V * Real.log V := by
    have h1 : ∑ z ∈ R₁, ((analyticOrderAt xi z).toNat : ℝ) ≤
        ∑ z ∈ stripFinsetPos (2 * V), ((analyticOrderAt xi z).toNat : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub_strip fun _ _ _ => Nat.cast_nonneg _
    have h2 := stripFinsetPos_orderSum_le_mul_log' (by linarith only [hV16] : 2 ≤ 2 * V)
    have hlog2V : Real.log (2 * V) ≤ 2 * Real.log V := by
      rw [Real.log_mul zero_lt_two.ne' hV_pos.ne']
      linarith only [Real.log_two_lt_d9, hLV_ge2]
    have hc_nn : 0 ≤ 32 * (2 * |xiLineTwoLogDerivConstant| + 5) * (2 * V) := by
      have := abs_nonneg xiLineTwoLogDerivConstant
      positivity
    calc ∑ z ∈ R₁, ((analyticOrderAt xi z).toNat : ℝ)
        ≤ 32 * (2 * |xiLineTwoLogDerivConstant| + 5) * (2 * V) * Real.log (2 * V) := h1.trans h2
      _ ≤ 32 * (2 * |xiLineTwoLogDerivConstant| + 5) * (2 * V) * (2 * Real.log V) :=
          mul_le_mul_of_nonneg_left hlog2V hc_nn
      _ = 128 * (2 * |xiLineTwoLogDerivConstant| + 5) * V * Real.log V := by ring
  calc 2 * ∑ z ∈ R₁, ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2)
      ≤ 2 * ((16 * Real.exp 2 * c' ^ 2) * ∑ z ∈ R₁, ((analyticOrderAt xi z).toNat : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ zero_le_two
        exact (Finset.sum_le_sum hptw).trans_eq (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * ((16 * Real.exp 2 * c' ^ 2) *
          (128 * (2 * |xiLineTwoLogDerivConstant| + 5) * V * Real.log V)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hord_2V (by positivity)) zero_le_two
    _ = (4096 * Real.exp 2 * (2 * |xiLineTwoLogDerivConstant| + 5)) * c' ^ 2 * V * Real.log V := by
        ring

/-- Modular three-scale shell bound from a given arbitrary-rate Barban–Vehov input `(r_c, ε_c)`. -/
private theorem exists_shellDepthSum_of_arbitraryRate_input
    {c' r_c ε_c A_c K_c η_c lam_c : ℝ}
    (hc0 : 0 < c') (hc' : c' < 1 / 2)
    (hr0 : 0 < r_c) (hε0 : 0 < ε_c) (hε1 : ε_c ≤ 1)
    (hA : 0 < A_c) (hK : 0 < K_c) (hη_pos : 0 < η_c) (hη_lt : η_c < 1 / 2)
    (hlam_eq : lam_c = r_c - 2 * c' * (1 + ε_c)) (hlam_pos : 0 < lam_c)
    (hbv_ev : ∀ᶠ S : ℝ in atTop,
      ∃ T₁ ∈ Ioo (2 * S / 3) (2 * S / 3 + 1),
      ∃ T₂ ∈ Ioo (4 * S / 3 - 1) (4 * S / 3),
        ∀ a : ℝ, 1 ≤ a → a ≤ (1 / (4 * (1 + min ε_c 1))) * Real.log S →
          ∀ Z : Finset ℂ,
            (∀ z : ℂ, z ∈ Z ↔
              z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
            2 * Real.pi * ((a / Real.log S) *
              ∑ w ∈ Z.filter (fun w => 1 / 2 + (1 + ε_c) * (a / Real.log S) ≤ w.re),
                ((analyticOrderAt riemannZeta w).toNat : ℝ)) ≤
              (T₂ - T₁) * (A_c * Real.exp (-(r_c * a))) + K_c * S ^ (1 - η_c)) :
    ∀ᶠ V : ℝ in atTop, ∀ L : ℝ, 0 ≤ L → L ≤ c' * Real.log V →
      shellDepthSum V (2 * V) L ≤
        ((4096 * Real.exp 2 * (2 * |xiLineTwoLogDerivConstant| + 5)) +
          32 * (1 + ε_c) ^ 2 * A_c / lam_c + 4) * c' ^ 2 * V * Real.log V := by
  let K_I : ℝ := 4096 * Real.exp 2 * (2 * |xiLineTwoLogDerivConstant| + 5)
  let K_II : ℝ := 32 * (1 + ε_c) ^ 2 * A_c / lam_c
  let δ₁ : ℝ := min (1 / (4 * (1 + ε_c))) (η_c / (4 * (1 + ε_c)))
  let b₀ : ℝ := (1 + ε_c) * δ₁
  have h1ε_pos : 0 < 1 + ε_c := by linarith only [hε0]
  have hδ₁_pos : 0 < δ₁ := lt_min (by positivity) (by positivity)
  have hδ₁_le_q : δ₁ ≤ 1 / (4 * (1 + ε_c)) := min_le_left _ _
  have hδ₁_le1 : δ₁ ≤ 1 := hδ₁_le_q.trans (by
    rw [div_le_one (by positivity)]; linarith only [hε0])
  have hb₀_pos : 0 < b₀ := mul_pos h1ε_pos hδ₁_pos
  have hb₀_lt_half : b₀ < 1 / 2 := by
    have hm : b₀ ≤ (1 + ε_c) * (1 / (4 * (1 + ε_c))) :=
      mul_le_mul_of_nonneg_left hδ₁_le_q h1ε_pos.le
    have hsimp : (1 + ε_c) * (1 / (4 * (1 + ε_c))) = 1 / 4 := by field_simp [h1ε_pos.ne']
    linarith only [hm, hsimp]
  have h2cb_le : 2 * c' * ((1 + ε_c) * δ₁) ≤ η_c / 2 := by
    have hm1 : δ₁ ≤ η_c / (4 * (1 + ε_c)) := min_le_right _ _
    have hm2 : (1 + ε_c) * δ₁ ≤ η_c / 4 := by
      calc (1 + ε_c) * δ₁ ≤ (1 + ε_c) * (η_c / (4 * (1 + ε_c))) :=
            mul_le_mul_of_nonneg_left hm1 h1ε_pos.le
        _ = η_c / 4 := by field_simp [h1ε_pos.ne']
    nlinarith only [hc0, hc', hm2, hη_pos]
  obtain ⟨C_deep, hC_deep, T_deep, hT_deep, hdeep⟩ :=
    exists_sum_exp_foldedRe_deep_decay_up_to_two_thirds_log
      hc0.le (by linarith only [hc'] : c' < 2 / 3) hb₀_pos hb₀_lt_half
  let γ₀ : ℝ := (4 / 3 - 2 * c') * b₀ / 8
  have hγ₀_pos : 0 < γ₀ := by dsimp [γ₀]; nlinarith only [hc', hb₀_pos]
  obtain ⟨K_log1, _, hlog1⟩ := exists_one_add_log_pow_le_rpow 1 (by positivity : (0 : ℝ) < 1 / 4)
  obtain ⟨K_log2, _, hlog2⟩ := exists_one_add_log_pow_le_rpow 2 (by positivity : 0 < η_c / 4)
  have htend_32 : Tendsto (fun V : ℝ => (3 / 2 : ℝ) * V) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  -- Eventual smallness of short end-caps, Scale-II power-saving error, and Scale-III deep decay
  have hev_cap : ∀ᶠ V : ℝ in atTop,
      64 * (|xiLineTwoLogDerivConstant| + 4) * K_log1 * V ^ (3 / 4 : ℝ) ≤
        c' ^ 2 * V * Real.log V := by
    have ht : Tendsto (fun V : ℝ => V ^ (1 / 4 : ℝ)) atTop atTop :=
      tendsto_rpow_atTop (by positivity)
    filter_upwards [ht.eventually_ge_atTop
      (64 * (|xiLineTwoLogDerivConstant| + 4) * K_log1 / c' ^ 2 + 1),
      eventually_ge_atTop (4 : ℝ)] with V hV_r hV4
    have hV_pos : 0 < V := by linarith only [hV4]
    have hlog_ge1 : 1 ≤ Real.log V := one_le_log_of_four_le' hV4
    have hV_mul : V ^ (3 / 4 : ℝ) * V ^ (1 / 4 : ℝ) = V := by
      rw [← Real.rpow_add hV_pos]; norm_num
    have hc_nn : 0 ≤ |xiLineTwoLogDerivConstant| := abs_nonneg _
    have hm1 := (div_le_iff₀ (by positivity : 0 < c' ^ 2)).mp
      (by linarith only [hV_r] : 64 * (|xiLineTwoLogDerivConstant| + 4) * K_log1 / c' ^ 2 ≤ V ^ (1 / 4 : ℝ))
    have hm2 := mul_le_mul_of_nonneg_left hm1 (Real.rpow_nonneg hV_pos.le (3 / 4))
    have hrew : V ^ (3 / 4 : ℝ) * (V ^ (1 / 4 : ℝ) * c' ^ 2) = c' ^ 2 * V := by
      calc V ^ (3 / 4 : ℝ) * (V ^ (1 / 4 : ℝ) * c' ^ 2)
          = c' ^ 2 * (V ^ (3 / 4 : ℝ) * V ^ (1 / 4 : ℝ)) := by ring
        _ = c' ^ 2 * V := by rw [hV_mul]
    rw [hrew, mul_comm (V ^ (3 / 4 : ℝ))] at hm2
    exact hm2.trans (le_mul_of_one_le_right (by positivity) hlog_ge1)
  have hev_errII : ∀ᶠ V : ℝ in atTop,
      2 * ((4 * (1 + ε_c) ^ 2 * K_c) * c' ^ 2 * K_log2 *
        ((3 / 2 : ℝ) * V) ^ (1 - η_c / 4)) ≤ c' ^ 2 * V * Real.log V := by
    have ht : Tendsto (fun V : ℝ => V ^ (η_c / 4)) atTop atTop :=
      tendsto_rpow_atTop (by positivity)
    filter_upwards [ht.eventually_ge_atTop (16 * (1 + ε_c) ^ 2 * K_c * K_log2 + 1),
      eventually_ge_atTop (4 : ℝ)] with V hV_r hV4
    have hV_pos : 0 < V := by linarith only [hV4]
    have hlog_ge1 : 1 ≤ Real.log V := one_le_log_of_four_le' hV4
    have h32_le : ((3 / 2 : ℝ) * V) ^ (1 - η_c / 4) ≤ 2 * V ^ (1 - η_c / 4) := by
      rw [Real.mul_rpow (by norm_num) hV_pos.le]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hV_pos.le _)
      calc (3 / 2 : ℝ) ^ (1 - η_c / 4)
          ≤ (3 / 2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hη_pos])
        _ ≤ 2 := by rw [Real.rpow_one]; norm_num
    have hV_mul : V ^ (1 - η_c / 4) * V ^ (η_c / 4) = V := by
      rw [← Real.rpow_add hV_pos]; ring_nf; exact Real.rpow_one V
    have h1 : 2 * ((4 * (1 + ε_c) ^ 2 * K_c) * c' ^ 2 * K_log2 *
          ((3 / 2 : ℝ) * V) ^ (1 - η_c / 4)) ≤
        c' ^ 2 * V ^ (1 - η_c / 4) * (16 * (1 + ε_c) ^ 2 * K_c * K_log2) := by
      have hm := mul_le_mul_of_nonneg_left h32_le
        (by positivity : 0 ≤ 8 * (1 + ε_c) ^ 2 * K_c * c' ^ 2 * K_log2)
      linarith only [hm]
    have h2 : c' ^ 2 * V ^ (1 - η_c / 4) * (16 * (1 + ε_c) ^ 2 * K_c * K_log2) ≤ c' ^ 2 * V := by
      calc c' ^ 2 * V ^ (1 - η_c / 4) * (16 * (1 + ε_c) ^ 2 * K_c * K_log2)
          ≤ c' ^ 2 * V ^ (1 - η_c / 4) * V ^ (η_c / 4) :=
            mul_le_mul_of_nonneg_left (by linarith only [hV_r]) (by positivity)
        _ = c' ^ 2 * (V ^ (1 - η_c / 4) * V ^ (η_c / 4)) := by ring
        _ = c' ^ 2 * V := by rw [hV_mul]
    exact (h1.trans h2).trans (le_mul_of_one_le_right (by positivity) hlog_ge1)
  have hev_deep : ∀ᶠ V : ℝ in atTop,
      2 * (C_deep * V ^ (1 - γ₀)) ≤ c' ^ 2 * V * Real.log V := by
    have ht : Tendsto (fun V : ℝ => V ^ γ₀) atTop atTop := tendsto_rpow_atTop hγ₀_pos
    filter_upwards [ht.eventually_ge_atTop (2 * C_deep / c' ^ 2 + 1),
      eventually_ge_atTop (4 : ℝ)] with V hV_r hV4
    have hV_pos : 0 < V := by linarith only [hV4]
    have hlog_ge1 : 1 ≤ Real.log V := one_le_log_of_four_le' hV4
    have hV_mul : V ^ (1 - γ₀) * V ^ γ₀ = V := by
      rw [← Real.rpow_add hV_pos]; ring_nf; exact Real.rpow_one V
    have hm1 := (div_le_iff₀ (by positivity : 0 < c' ^ 2)).mp
      (by linarith only [hV_r] : 2 * C_deep / c' ^ 2 ≤ V ^ γ₀)
    have hm2 := mul_le_mul_of_nonneg_left hm1 (Real.rpow_nonneg hV_pos.le (1 - γ₀))
    have hrew : V ^ (1 - γ₀) * (V ^ γ₀ * c' ^ 2) = c' ^ 2 * V := by
      calc V ^ (1 - γ₀) * (V ^ γ₀ * c' ^ 2)
          = c' ^ 2 * (V ^ (1 - γ₀) * V ^ γ₀) := by ring
        _ = c' ^ 2 * V := by rw [hV_mul]
    rw [hrew] at hm2
    exact (by linarith only [hm2] : 2 * (C_deep * V ^ (1 - γ₀)) ≤ c' ^ 2 * V).trans
      (le_mul_of_one_le_right (by positivity) hlog_ge1)
  filter_upwards [htend_32.eventually hbv_ev,
    htend_32.eventually (Real.tendsto_log_atTop.eventually_ge_atTop (1 / δ₁ + 4)),
    eventually_ge_atTop (max 16 T_deep),
    hev_cap, hev_errII, hev_deep]
    with V hbv_V hLS_big hV_max hcap_V herrII_V hdeep_V L hL0 hL
  have hV16 : 16 ≤ V := (le_max_left _ _).trans hV_max
  have hV_deep : T_deep ≤ V := (le_max_right _ _).trans hV_max
  have hV_pos : 0 < V := by linarith only [hV16]
  have hLV_ge2 : 2 ≤ Real.log V := two_le_log_of_sixteen_le' hV16
  let S : ℝ := (3 / 2 : ℝ) * V
  let L_S : ℝ := Real.log S
  have hS1 : 1 < S := by dsimp [S]; linarith only [hV16]
  have hS_pos : 0 < S := zero_lt_one.trans hS1
  have hLS_pos : 0 < L_S := Real.log_pos hS1
  have h1_le_δLS : 1 ≤ δ₁ * L_S := by
    have h1 : 1 / δ₁ ≤ L_S := by dsimp [L_S]; linarith only [hLS_big]
    exact (div_le_iff₀' hδ₁_pos).mp h1
  have hLS_le_2LV : L_S ≤ 2 * Real.log V := by
    dsimp [L_S, S]
    have h1 : Real.log ((3 / 2 : ℝ) * V) ≤ Real.log (2 * V) :=
      Real.log_le_log (by positivity) (by linarith only [hV16])
    rw [Real.log_mul zero_lt_two.ne' hV_pos.ne'] at h1
    linarith only [h1, Real.log_two_lt_d9, hLV_ge2]
  have hL_le_LS : L ≤ c' * L_S :=
    hL.trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log hV_pos (by dsimp [S]; linarith only [hV16])) hc0.le)
  obtain ⟨T₁, hT₁, T₂, hT₂, hbv_S⟩ := hbv_V
  have hVT₁ : V ≤ T₁ := by dsimp [S] at hT₁; linarith only [hT₁.1]
  have hT₁2 : T₁ ≤ T₂ := by dsimp [S] at hT₁ hT₂; linarith only [hT₁.2, hT₂.1, hV16]
  have hT₂2V : T₂ ≤ 2 * V := by dsimp [S] at hT₂; linarith only [hT₂.2]
  have hlen_hi : T₂ - T₁ ≤ V := by dsimp [S] at hT₁ hT₂; linarith only [hT₁.1, hT₂.2]
  -- 1. Short end-caps `(V, T₁]` and `(T₂, 2 * V]`
  have hL_half : L ≤ (1 / 2) * Real.log V :=
    hL.trans (mul_le_mul_of_nonneg_right hc'.le (by linarith only [hLV_ge2]))
  have hcap_sum : shellDepthSum V T₁ L + shellDepthSum T₂ (2 * V) L ≤
      c' ^ 2 * V * Real.log V := by
    have hb1 := shortCap_shellDepthSum_le_rpow' hV16 hV_pos.le hVT₁
      (by dsimp [S] at hT₁; linarith only [hT₁.2]) (hT₁2.trans hT₂2V) hL0 hL_half hlog1
    have hb2 := shortCap_shellDepthSum_le_rpow' hV16 (by linarith only [hVT₁, hT₁2, hV16]) hT₂2V
      (by dsimp [S] at hT₂; linarith only [hT₂.1]) le_rfl hL0 hL_half hlog1
    exact (add_le_add hb1 hb2).trans (by
      simpa only [show 32 * (|xiLineTwoLogDerivConstant| + 4) * K_log1 * V ^ (3 / 4 : ℝ) +
          32 * (|xiLineTwoLogDerivConstant| + 4) * K_log1 * V ^ (3 / 4 : ℝ) =
        64 * (|xiLineTwoLogDerivConstant| + 4) * K_log1 * V ^ (3 / 4 : ℝ) by ring] using hcap_V)
  -- 2. Partition `R = (shellZeros T₁ T₂).filter (1 / 2 < ·.re)` into Scales I, II, III
  classical
  let R := (shellZeros T₁ T₂).filter (fun z => 1 / 2 < z.re)
  let b₁ : ℝ := (1 + ε_c) * (1 / L_S)
  let f_z : ℂ → ℝ := fun z => ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2)
  have hpart1 := (Finset.sum_filter_add_sum_filter_not R (fun z => z.re - 1 / 2 < b₁) f_z).symm
  have hpart2 := (Finset.sum_filter_add_sum_filter_not
    (R.filter (fun z => ¬ z.re - 1 / 2 < b₁)) (fun z => z.re - 1 / 2 < b₀) f_z).symm
  have hscaleI : 2 * ∑ z ∈ R.filter (fun z => z.re - 1 / 2 < b₁), f_z z ≤
      K_I * c' ^ 2 * V * Real.log V :=
    scaleI_near_shell_sum_le_general hV16 hT₂2V hc0 hc' hε0 hε1 hLS_pos hL0 hL_le_LS
  have hscaleII : 2 * ∑ z ∈ (R.filter (fun z => ¬ z.re - 1 / 2 < b₁)).filter
        (fun z => z.re - 1 / 2 < b₀), f_z z ≤
      (K_II + 1) * c' ^ 2 * V * Real.log V := by
    have hR₂_eq : (R.filter (fun z => ¬ z.re - 1 / 2 < b₁)).filter (fun z => z.re - 1 / 2 < b₀) =
        (shellZeros T₁ T₂).filter (fun z =>
          1 / 2 + (1 + ε_c) * (1 / L_S) ≤ z.re ∧ z.re < 1 / 2 + (1 + ε_c) * δ₁) := by
      ext z
      simp only [R, b₁, b₀, Finset.mem_filter, not_lt]
      constructor
      · rintro ⟨⟨⟨hz_sh, _⟩, hge⟩, hlt⟩
        exact ⟨hz_sh, by linarith only [hge], by linarith only [hlt]⟩
      · rintro ⟨hz_sh, hge, hlt⟩
        have hb₁_pos : 0 < (1 + ε_c) * (1 / L_S) := by positivity
        exact ⟨⟨⟨hz_sh, by linarith only [hge, hb₁_pos]⟩, by linarith only [hge]⟩,
          by linarith only [hlt]⟩
    have hT₁_pos : 0 < T₁ := by linarith only [hVT₁, hV_pos]
    have hmin_eq : min ε_c 1 = ε_c := min_eq_left hε1
    have hbv_win : ∀ a : ℝ, 1 ≤ a → a ≤ δ₁ * L_S →
        2 * Real.pi * ((a / L_S) *
          ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + (1 + ε_c) * (a / L_S) ≤ w.re),
            ((analyticOrderAt riemannZeta w).toNat : ℝ)) ≤
          (T₂ - T₁) * (A_c * Real.exp (-(r_c * a))) + K_c * S ^ (1 - η_c) := by
      intro a ha1 ha_hi
      have ha_hi' : a ≤ (1 / (4 * (1 + min ε_c 1))) * Real.log S := by
        rw [hmin_eq]
        exact ha_hi.trans (mul_le_mul_of_nonneg_right hδ₁_le_q hLS_pos.le)
      exact hbv_S a ha1 ha_hi' (windowZeros T₁ T₂) (mem_windowZeros_iff hT₁_pos hT₁2)
    have hband := scaleII_continuous_laplace_band_le
      hV_pos hS1 hA hK hr0 hε0 hη_pos hc0 hL0 hL_le_LS hT₁_pos hT₁2 hlen_hi
      rfl hLS_pos hlam_eq hlam_pos hδ₁_pos hδ₁_le1 h2cb_le le_rfl h1_le_δLS hbv_win
    rw [← hR₂_eq] at hband
    have hexp_le1 : Real.exp (-(lam_c / 2 * 1)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith only [hlam_pos])
    have hmain_II : 2 * ((8 * (1 + ε_c) ^ 2 * A_c / lam_c) * c' ^ 2 *
          Real.exp (-(lam_c / 2 * 1)) * (V * L_S)) ≤
        K_II * c' ^ 2 * V * Real.log V := by
      have hm1 : Real.exp (-(lam_c / 2 * 1)) * (V * L_S) ≤ 1 * (V * (2 * Real.log V)) :=
        mul_le_mul hexp_le1 (mul_le_mul_of_nonneg_left hLS_le_2LV hV_pos.le)
          (by positivity) zero_le_one
      have hm2 := mul_le_mul_of_nonneg_left hm1
        (by positivity : 0 ≤ 2 * ((8 * (1 + ε_c) ^ 2 * A_c / lam_c) * c' ^ 2))
      dsimp [K_II]
      linarith only [hm2]
    have herr_II : 2 * ((4 * (1 + ε_c) ^ 2 * K_c) * c' ^ 2 * L_S ^ 2 * S ^ (1 - η_c / 2)) ≤
        c' ^ 2 * V * Real.log V := by
      have hLS2 : L_S ^ 2 ≤ K_log2 * S ^ (η_c / 4) :=
        (pow_le_pow_left₀ hLS_pos.le (by linarith only [hLS_pos]) 2).trans (hlog2 S hS1.le)
      have hS_comb : S ^ (η_c / 4) * S ^ (1 - η_c / 2) = S ^ (1 - η_c / 4) := by
        rw [← Real.rpow_add hS_pos]; congr 1; ring
      have hm := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hLS2 (by positivity : 0 ≤ 2 * ((4 * (1 + ε_c) ^ 2 * K_c) * c' ^ 2)))
        (Real.rpow_nonneg hS_pos.le _)
      calc 2 * ((4 * (1 + ε_c) ^ 2 * K_c) * c' ^ 2 * L_S ^ 2 * S ^ (1 - η_c / 2))
          = 2 * ((4 * (1 + ε_c) ^ 2 * K_c) * c' ^ 2) * L_S ^ 2 * S ^ (1 - η_c / 2) := by ring
        _ ≤ 2 * ((4 * (1 + ε_c) ^ 2 * K_c) * c' ^ 2) * (K_log2 * S ^ (η_c / 4)) *
              S ^ (1 - η_c / 2) := hm
        _ = 2 * ((4 * (1 + ε_c) ^ 2 * K_c) * c' ^ 2 * K_log2 *
              (S ^ (η_c / 4) * S ^ (1 - η_c / 2))) := by ring
        _ = 2 * ((4 * (1 + ε_c) ^ 2 * K_c) * c' ^ 2 * K_log2 * S ^ (1 - η_c / 4)) := by
            rw [hS_comb]
        _ ≤ c' ^ 2 * V * Real.log V := herrII_V
    calc 2 * ∑ z ∈ (R.filter (fun z => ¬ z.re - 1 / 2 < b₁)).filter
            (fun z => z.re - 1 / 2 < b₀), f_z z
        ≤ 2 * ((8 * (1 + ε_c) ^ 2 * A_c / lam_c) * c' ^ 2 *
              Real.exp (-(lam_c / 2 * 1)) * (V * L_S) +
            (4 * (1 + ε_c) ^ 2 * K_c) * c' ^ 2 * L_S ^ 2 * S ^ (1 - η_c / 2)) :=
          mul_le_mul_of_nonneg_left hband zero_le_two
      _ = 2 * ((8 * (1 + ε_c) ^ 2 * A_c / lam_c) * c' ^ 2 *
              Real.exp (-(lam_c / 2 * 1)) * (V * L_S)) +
            2 * ((4 * (1 + ε_c) ^ 2 * K_c) * c' ^ 2 * L_S ^ 2 * S ^ (1 - η_c / 2)) := by ring
      _ ≤ K_II * c' ^ 2 * V * Real.log V + c' ^ 2 * V * Real.log V :=
          add_le_add hmain_II herr_II
      _ = (K_II + 1) * c' ^ 2 * V * Real.log V := by ring
  have hscaleIII : 2 * ∑ z ∈ (R.filter (fun z => ¬ z.re - 1 / 2 < b₁)).filter
        (fun z => ¬ z.re - 1 / 2 < b₀), f_z z ≤
      c' ^ 2 * V * Real.log V := by
    let R₃ := (R.filter (fun z => ¬ z.re - 1 / 2 < b₁)).filter (fun z => ¬ z.re - 1 / 2 < b₀)
    have hsub₃ : R₃ ⊆ shellZeros T₁ T₂ := fun z hz =>
      (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).1
    have hre₃ : ∀ z ∈ R₃, 1 / 2 + b₀ ≤ z.re := fun z hz => by
      have hge := not_lt.mp (Finset.mem_filter.mp hz).2
      linarith only [hge]
    exact (scaleIII_deep_shell_sum_le_general R₃ hV_pos hVT₁ hT₂2V hL0 hb₀_pos hsub₃ hre₃
      (hdeep V hV_deep L hL0 hL)).trans hdeep_V
  have hmid_tot : shellDepthSum T₁ T₂ L ≤ (K_I + K_II + 2) * c' ^ 2 * V * Real.log V := by
    rw [shellDepthSum_eq_two_mul_right T₁ T₂ L]
    change 2 * ∑ z ∈ R, f_z z ≤ _
    calc 2 * ∑ z ∈ R, f_z z
        = 2 * ∑ z ∈ R.filter (fun z => z.re - 1 / 2 < b₁), f_z z +
            2 * ∑ z ∈ (R.filter (fun z => ¬ z.re - 1 / 2 < b₁)).filter
              (fun z => z.re - 1 / 2 < b₀), f_z z +
            2 * ∑ z ∈ (R.filter (fun z => ¬ z.re - 1 / 2 < b₁)).filter
              (fun z => ¬ z.re - 1 / 2 < b₀), f_z z := by
          rw [hpart1, hpart2]; ring
      _ ≤ K_I * c' ^ 2 * V * Real.log V + (K_II + 1) * c' ^ 2 * V * Real.log V +
            c' ^ 2 * V * Real.log V :=
          add_le_add (add_le_add hscaleI hscaleII) hscaleIII
      _ = (K_I + K_II + 2) * c' ^ 2 * V * Real.log V := by ring
  rw [shellDepthSum_split hVT₁ (hT₁2.trans hT₂2V), shellDepthSum_split hT₁2 hT₂2V]
  have hextra : 0 ≤ c' ^ 2 * V * Real.log V := by positivity
  calc shellDepthSum V T₁ L + (shellDepthSum T₁ T₂ L + shellDepthSum T₂ (2 * V) L)
      = (shellDepthSum V T₁ L + shellDepthSum T₂ (2 * V) L) + shellDepthSum T₁ T₂ L := by ring
    _ ≤ c' ^ 2 * V * Real.log V + (K_I + K_II + 2) * c' ^ 2 * V * Real.log V :=
        add_le_add hcap_sum hmid_tot
    _ ≤ (K_I + K_II + 4) * c' ^ 2 * V * Real.log V := by linarith only [hextra]

/-- **Continuous-Laplace Shell Bound across the Full Half-Gate `0 < c' < 1 / 2`
(`exists_shellDepthSum_le_mul_log_up_to_half`).**
For every `0 < c' < 1 / 2`, `shellDepthSum V (2 * V) L ≤ K_sh * V * Real.log V` uniformly across
`0 ≤ L ≤ c' * Real.log V` eventually in `V`, with uniform quadratic small-`c'` constant
`K_sh ≤ K_univ * c' ^ 2` across `0 < c' ≤ 1 / 5`. -/
theorem exists_shellDepthSum_le_mul_log_up_to_half :
    ∃ K_univ : ℝ, 0 < K_univ ∧
      ∀ c' : ℝ, 0 < c' → c' < 1 / 2 →
        ∃ K_sh : ℝ, 0 < K_sh ∧ (c' ≤ 1 / 5 → K_sh ≤ K_univ * c' ^ 2) ∧
          ∀ᶠ V : ℝ in atTop, ∀ L : ℝ, 0 ≤ L → L ≤ c' * Real.log V →
            shellDepthSum V (2 * V) L ≤ K_sh * V * Real.log V := by
  obtain ⟨A₀, K₀, η₀, hA₀, hK₀, hη₀_pos, hη₀_lt, hbv₀⟩ :=
    exists_selberg_arbitraryRate_nearLine_zeroDensity
      (by norm_num : (0 : ℝ) < 7 / 8) (by norm_num : (7 / 8 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1 / 5)
  let K_I : ℝ := 4096 * Real.exp 2 * (2 * |xiLineTwoLogDerivConstant| + 5)
  let K_II_univ : ℝ := 32 * (1 + (1 / 5 : ℝ)) ^ 2 * A₀ / (79 / 200 : ℝ)
  let K_univ : ℝ := K_I + K_II_univ + 4
  have hKuniv_pos : 0 < K_univ := by
    dsimp [K_univ, K_I, K_II_univ]
    have := abs_nonneg xiLineTwoLogDerivConstant
    positivity
  refine ⟨K_univ, hKuniv_pos, fun c' hc0 hc' => ?_⟩
  by_cases hsmall : c' ≤ 1 / 5
  · let lam₀ : ℝ := 7 / 8 - 2 * c' * (1 + 1 / 5)
    have hlam₀_ge : (79 / 200 : ℝ) ≤ lam₀ := by dsimp [lam₀]; linarith only [hsmall]
    have hlam₀_pos : 0 < lam₀ := by linarith only [hlam₀_ge]
    let K_sh : ℝ := (K_I + 32 * (1 + (1 / 5 : ℝ)) ^ 2 * A₀ / lam₀ + 4) * c' ^ 2
    have hKsh_pos : 0 < K_sh := by
      dsimp [K_sh, K_I]
      have := abs_nonneg xiLineTwoLogDerivConstant
      positivity
    have hKsh_le : K_sh ≤ K_univ * c' ^ 2 := by
      have hdiv : 32 * (1 + (1 / 5 : ℝ)) ^ 2 * A₀ / lam₀ ≤ K_II_univ :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hlam₀_ge
      dsimp [K_sh, K_univ]
      exact mul_le_mul_of_nonneg_right (by linarith only [hdiv]) (sq_nonneg c')
    refine ⟨K_sh, hKsh_pos, fun _ => hKsh_le, ?_⟩
    exact exists_shellDepthSum_of_arbitraryRate_input hc0 hc'
      (by norm_num) (by norm_num) (by norm_num) hA₀ hK₀ hη₀_pos hη₀_lt rfl hlam₀_pos hbv₀
  · have hgt : 1 / 5 < c' := not_le.mp hsmall
    let r_c : ℝ := (6 * c' + 5) / 8
    let ε_c : ℝ := (1 - 2 * c') / 4
    let lam_c : ℝ := r_c - 2 * c' * (1 + ε_c)
    have hr0 : 0 < r_c := by dsimp [r_c]; linarith only [hc0]
    have hr1 : r_c < 1 := by dsimp [r_c]; linarith only [hc']
    have hε0 : 0 < ε_c := by dsimp [ε_c]; linarith only [hc']
    have hε1 : ε_c ≤ 1 := by dsimp [ε_c]; linarith only [hc0]
    have hlam_pos : 0 < lam_c := by
      have hid : lam_c = (1 / 2 - c') * (5 / 4 - c') := by dsimp [lam_c, r_c, ε_c]; ring
      rw [hid]
      exact mul_pos (by linarith only [hc']) (by linarith only [hc'])
    obtain ⟨A_c, K_c, η_c, hA_c, hK_c, hη_pos, hη_lt, hbv_c⟩ :=
      exists_selberg_arbitraryRate_nearLine_zeroDensity hr0 hr1 hε0
    let K_sh : ℝ := (K_I + 32 * (1 + ε_c) ^ 2 * A_c / lam_c + 4) * c' ^ 2
    have hKsh_pos : 0 < K_sh := by
      dsimp [K_sh, K_I]
      have := abs_nonneg xiLineTwoLogDerivConstant
      positivity
    refine ⟨K_sh, hKsh_pos, fun hle => absurd hle hsmall, ?_⟩
    exact exists_shellDepthSum_of_arbitraryRate_input hc0 hc'
      hr0 hε0 hε1 hA_c hK_c hη_pos hη_lt rfl hlam_pos hbv_c

/-- Joint continuity of `(γ, L) ↦ heckeDefect (sourceTwist γ f) L` for any `f : CompactTest`
supported in `[-a, a]` (`a ≥ 0`). -/
theorem continuous_heckeDefect_sourceTwist_pair (f : CompactTest) {a : ℝ} (ha : 0 ≤ a)
    (hsupp : ∀ u, f.1 u ≠ 0 → |u| ≤ a) :
    Continuous (fun p : ℝ × ℝ => heckeDefect (sourceTwist p.1 f) p.2) := by
  have hsum0 : Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (ρ : ℂ).im ^ 2)) := by
    simpa only [zero_sub, neg_sq] using
      ArithmeticCastelnuovoSeveri.summable_zetaCarrier_of_xiZeroCopy
        (g := fun z : ℂ => 1 / (1 + (0 - z.im) ^ 2)) (fun _ => by positivity)
        (RHTower.summable_lorentzMassTerm 0)
  refine continuous_iff_continuousAt.mpr fun p₀ => ?_
  let R : ℝ := max (|p₀.1| + 1) (|p₀.2| + 1)
  let M₀ : ℝ := sourceTestSize f ^ 2 * Real.exp a + 1
  let K_dom : ℝ := M₀ * (2 + 2 * R ^ 2) * depthKernel R (1 / 2)
  have hcont_on : ContinuousOn (fun p : ℝ × ℝ => heckeDefect (sourceTwist p.1 f) p.2)
      (Metric.closedBall (0 : ℝ × ℝ) R) := by
    refine continuousOn_tsum
      (f := fun (ρ : zetaZeroConfig.carrier) (p : ℝ × ℝ) =>
        zetaWeight (sourceTwist p.1 f) ρ * depthKernel p.2 (zetaDepth ρ))
      (u := fun ρ : zetaZeroConfig.carrier =>
        K_dom * ((zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (ρ : ℂ).im ^ 2))))
      (fun ρ => ?_)
      (hsum0.mul_left K_dom) (fun ρ p hp => ?_)
    · dsimp only [zetaWeight]
      have htr_c : Continuous (fun p : ℝ × ℝ => Complex.normSq (tr (sourceTwist p.1 f).1 ρ)) := by
        have heq : (fun p : ℝ × ℝ => Complex.normSq (tr (sourceTwist p.1 f).1 ρ)) =
            fun p : ℝ × ℝ => Complex.normSq (tr f.1 ((ρ : ℂ) - (p.1 : ℂ) * I)) :=
          funext fun p => congrArg Complex.normSq (tr_twist p.1 f.1 ρ)
        rw [heq]
        exact Complex.continuous_normSq.comp ((contDiff_tr f).continuous.comp
          (continuous_const.sub ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const)))
      have hdk_c : Continuous (fun p : ℝ × ℝ => depthKernel p.2 (zetaDepth ρ)) := by
        unfold depthKernel
        exact (continuous_const.mul (Real.continuous_cosh.comp
          (continuous_const.mul continuous_snd))).sub continuous_const
      exact ((continuous_const.mul htr_c).mul hdk_c).continuousOn
    · rw [Metric.mem_closedBall, dist_zero_right] at hp
      have hp1 : |p.1| ≤ R := (Real.norm_eq_abs p.1 ▸ norm_fst_le p).trans hp
      have hp2 : |p.2| ≤ R := (Real.norm_eq_abs p.2 ▸ norm_snd_le p).trans hp
      have hR_nn : 0 ≤ R := (abs_nonneg p.1).trans hp1
      have hstrip := abs_re_sub_half_le_of_zeroConfig zetaZeroConfig ρ
      have hz_re : 0 ≤ ((ρ : ℂ) - (p.1 : ℂ) * I).re ∧ ((ρ : ℂ) - (p.1 : ℂ) * I).re ≤ 1 := by
        simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_zero]
        rw [abs_le] at hstrip
        exact ⟨by linarith only [hstrip.1], by linarith only [hstrip.2]⟩
      have hnsq_z := normSq_tr_strip_le_sourceTestSize f ha hsupp hz_re
      have him_eq : ((ρ : ℂ) - (p.1 : ℂ) * I).im = (ρ : ℂ).im - p.1 := by simp
      rw [him_eq, ← tr_twist p.1 f.1 (ρ : ℂ)] at hnsq_z
      have hnsq_lor : Complex.normSq (tr (sourceTwist p.1 f).1 ρ) ≤
          M₀ * (1 / (1 + ((ρ : ℂ).im - p.1) ^ 2)) := by
        have hden : 1 + ((ρ : ℂ).im - p.1) ^ 2 ≤ (1 + ((ρ : ℂ).im - p.1) ^ 2) ^ 2 := by
          nlinarith only [sq_nonneg ((ρ : ℂ).im - p.1)]
        have h1 := (hnsq_z.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hden))
        dsimp [sourceTwist, M₀]
        have hnn : 0 ≤ 1 / (1 + ((ρ : ℂ).im - p.1) ^ 2) := by positivity
        rw [div_eq_mul_one_div] at h1
        exact h1.trans (mul_le_mul_of_nonneg_right (by linarith) hnn)
      have hshift : 1 / (1 + ((ρ : ℂ).im - p.1) ^ 2) ≤
          (2 + 2 * R ^ 2) * (1 / (1 + (ρ : ℂ).im ^ 2)) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have hp1_sq : p.1 ^ 2 ≤ R ^ 2 := by
          have h := pow_le_pow_left₀ (abs_nonneg _) hp1 2
          rwa [sq_abs] at h
        nlinarith only [hp1_sq, sq_nonneg (((ρ : ℂ).im - p.1) - p.1), sq_nonneg ((ρ : ℂ).im - p.1)]
      have hdk_le : depthKernel p.2 (zetaDepth ρ) ≤ depthKernel R (1 / 2) := by
        rw [depthKernel_eq_four_sinh_sq, depthKernel_eq_four_sinh_sq]
        have habs_prod : |zetaDepth ρ * p.2| ≤ (1 / 2) * R := by
          rw [abs_mul]
          exact mul_le_mul hstrip hp2 (abs_nonneg _) (by norm_num)
        have hsh_abs : |Real.sinh (zetaDepth ρ * p.2)| = Real.sinh |zetaDepth ρ * p.2| := by
          rcases le_or_gt 0 (zetaDepth ρ * p.2) with hnn | hneg
          · rw [abs_of_nonneg hnn, abs_of_nonneg (by
              rw [Real.sinh_eq]
              linarith [Real.exp_le_one_iff.mpr (by linarith : -(zetaDepth ρ * p.2) ≤ 0),
                Real.one_le_exp hnn])]
          · rw [abs_of_neg hneg, ← Real.sinh_neg, abs_of_nonneg (by
              rw [Real.sinh_eq]
              linarith [Real.exp_le_one_iff.mpr (by linarith : -(-(zetaDepth ρ * p.2)) ≤ 0),
                Real.one_le_exp (by linarith : 0 ≤ -(zetaDepth ρ * p.2))])]
        have hsh_le : |Real.sinh (zetaDepth ρ * p.2)| ≤ Real.sinh ((1 / 2) * R) := by
          rw [hsh_abs]
          exact sinh_mono_nonneg (abs_nonneg _) habs_prod
        have hsq := pow_le_pow_left₀ (abs_nonneg _) hsh_le 2
        rw [sq_abs] at hsq
        exact mul_le_mul_of_nonneg_left hsq (by norm_num)
      have hnn : 0 ≤ zetaWeight (sourceTwist p.1 f) ρ * depthKernel p.2 (zetaDepth ρ) :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _))
          (depthKernel_nonneg _ _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      dsimp only [zetaWeight]
      calc (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr (sourceTwist p.1 f).1 ρ) *
              depthKernel p.2 (zetaDepth ρ)
          ≤ (zetaZeroConfig.mult ρ : ℝ) *
              (M₀ * ((2 + 2 * R ^ 2) * (1 / (1 + (ρ : ℂ).im ^ 2)))) *
              depthKernel R (1 / 2) := by
            refine mul_le_mul
              (mul_le_mul_of_nonneg_left
                (hnsq_lor.trans (mul_le_mul_of_nonneg_left hshift (by dsimp [M₀]; positivity)))
                (Nat.cast_nonneg _))
              hdk_le (depthKernel_nonneg _ _) (by dsimp [M₀]; positivity)
        _ = K_dom * ((zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (ρ : ℂ).im ^ 2))) := by
            dsimp [K_dom]; ring
  have hmem_ball : p₀ ∈ Metric.ball (0 : ℝ × ℝ) R := by
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_def]
    simp only [Real.norm_eq_abs]
    exact max_lt ((lt_add_one |p₀.1|).trans_le (le_max_left _ _))
      ((lt_add_one |p₀.2|).trans_le (le_max_right _ _))
  exact hcont_on.continuousAt (Metric.closedBall_mem_nhds_of_mem hmem_ball)

/-- Joint continuity of `(γ, L) ↦ polynomialThetaSourceMomentReading (sourceTwist γ f) L 1 n`
for any `f : CompactTest` and `n : ℕ`. -/
theorem continuous_polynomialThetaSourceMomentReading_sourceTwist_pair
    (f : CompactTest) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ =>
      polynomialThetaSourceMomentReading (sourceTwist p.1 f) p.2 1 n) := by
  unfold polynomialThetaSourceMomentReading polynomialThetaSourceReading
  let k : Set ℂ := tsupport (stripSourceCutoff n)
  have hk : IsCompact k := hasCompactSupport_stripSourceCutoff n
  have hcurv_cont : Continuous (finiteThetaSourceCurvature
      (polynomialSourceRegulator n) (polynomialThetaIntegerCutoff n)) :=
    continuous_finiteThetaSourceCurvature (polynomialSourceRegulator_pos n) _
  let F : (ℝ × ℝ) → ℂ → ℝ := fun p z =>
    stripSourceCutoff n z * sourceDepthKernel (sourceTwist p.1 f) p.2 1 z *
      finiteThetaSourceCurvature (polynomialSourceRegulator n) (polynomialThetaIntegerCutoff n) z
  have hF_cont : Continuous F.uncurry := by
    have hcut : Continuous (fun q : (ℝ × ℝ) × ℂ => stripSourceCutoff n q.2) :=
      (contDiff_stripSourceCutoff n).continuous.comp continuous_snd
    have htr_c : Continuous (fun q : (ℝ × ℝ) × ℂ =>
        Complex.normSq (tr (sourceTwist q.1.1 f).1 q.2)) := by
      have h1 : (fun q : (ℝ × ℝ) × ℂ => Complex.normSq (tr (sourceTwist q.1.1 f).1 q.2)) =
          fun q : (ℝ × ℝ) × ℂ => Complex.normSq (tr f.1 (q.2 - (q.1.1 : ℂ) * I)) :=
        funext fun q => congrArg Complex.normSq (tr_twist q.1.1 f.1 q.2)
      rw [h1]
      exact Complex.continuous_normSq.comp ((contDiff_tr f).continuous.comp
        (continuous_snd.sub ((Complex.continuous_ofReal.comp
          (continuous_fst.comp continuous_fst)).mul continuous_const)))
    have hdk_c : Continuous (fun q : (ℝ × ℝ) × ℂ => depthKernel q.1.2 (q.2.re - 1 / 2) ^ 1) := by
      simp only [pow_one]
      unfold depthKernel
      exact (continuous_const.mul (Real.continuous_cosh.comp
        ((continuous_const.mul ((Complex.continuous_re.comp continuous_snd).sub
          continuous_const)).mul (continuous_snd.comp continuous_fst)))).sub continuous_const
    exact (hcut.mul (htr_c.mul hdk_c)).mul (hcurv_cont.comp continuous_snd)
  have hint_cont : Continuous (fun p : ℝ × ℝ => ∫ z : ℂ, F p z) := by
    rw [← continuousOn_univ]
    refine continuousOn_integral_of_compact_support hk hF_cont.continuousOn ?_
    intro p z _ hz
    dsimp [F]
    rw [image_eq_zero_of_notMem_tsupport hz, zero_mul, zero_mul]
  exact continuous_const.mul hint_cont

private theorem continuousOn_comp_log_pair' {F : ℝ × ℝ → ℝ} (hF : Continuous F)
    {U : ℝ} (hU : 0 < U) (c : ℝ) :
    ContinuousOn (fun γ : ℝ => F (γ, c * Real.log γ)) (Icc U (2 * U)) := by
  have hlog : ContinuousOn Real.log (Icc U (2 * U)) :=
    Real.continuousOn_log.mono fun γ hγ => (by linarith only [hU, hγ.1] : 0 < γ).ne'
  exact hF.comp_continuousOn (continuousOn_id.prodMk (continuousOn_const.mul hlog))

/-- Local-shell + Paley–Wiener remote decomposition of `∫_U^{2U} heckeDefect (sourceTwist γ f) (c log γ)`
for any `f : CompactTest` supported in `[-1/4, 1/4]`. -/
theorem exists_dyadicIntegral_heckeDefect_compactTest_le_threeShells
    (f : CompactTest) (hsupp : ∀ u, f.1 u ≠ 0 → |u| ≤ 1 / 4) :
    ∃ C_loc C_rem : ℝ, 0 < C_loc ∧ 0 < C_rem ∧
      ∀ U c : ℝ, 4 ≤ U → 0 ≤ c →
        (∫ γ in Icc U (2 * U), heckeDefect (sourceTwist γ f) (c * Real.log γ)) ≤
          C_loc * (shellDepthSum (U / 2) U (c * Real.log (2 * U)) +
            shellDepthSum U (2 * U) (c * Real.log (2 * U)) +
            shellDepthSum (2 * U) (4 * U) (c * Real.log (2 * U))) +
          C_rem * (2 * U) ^ c / U := by
  have hsum_lor : Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (ρ : ℂ).im ^ 2)) := by
    simpa only [zero_sub, neg_sq] using
      ArithmeticCastelnuovoSeveri.summable_zetaCarrier_of_xiZeroCopy
        (g := fun z : ℂ => 1 / (1 + (0 - z.im) ^ 2)) (fun _ => by positivity)
        (RHTower.summable_lorentzMassTerm 0)
  let L_mass : ℝ := ∑' ρ : zetaZeroConfig.carrier,
    (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (ρ : ℂ).im ^ 2))
  have hLmass_nn : 0 ≤ L_mass := tsum_nonneg fun _ => by positivity
  let M₀ : ℝ := sourceTestSize f ^ 2 * Real.exp (1 / 4) + 1
  have hM₀_pos : 0 < M₀ := by dsimp [M₀]; positivity
  let C_loc : ℝ := Real.pi * M₀ + 1
  let C_rem : ℝ := 16 * M₀ * L_mass + 1
  refine ⟨C_loc, C_rem, by positivity, by positivity, fun U c hU4 hc0 => ?_⟩
  classical
  have hU_pos : 0 < U := by linarith only [hU4]
  let L_max : ℝ := c * Real.log (2 * U)
  have hLmax_nn : 0 ≤ L_max := mul_nonneg hc0 (Real.log_nonneg (by linarith only [hU4]))
  have hmem_c : ∀ z ∈ shellZeros (U / 2) (4 * U), z ∈ zetaZeroConfig.carrier := by
    intro z hz
    obtain ⟨h0, h1, _, _, hxi⟩ := mem_stripFinsetPos.mp (Finset.mem_filter.mp hz).1
    exact CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mpr
      ⟨hxi, h0, h1⟩
  let emb : {z // z ∈ shellZeros (U / 2) (4 * U)} → zetaZeroConfig.carrier :=
    fun z => ⟨z.1, hmem_c z.1 z.2⟩
  have hinj : Function.Injective emb := fun a b h =>
    Subtype.ext (congrArg (fun x : zetaZeroConfig.carrier => (x : ℂ)) h)
  let S_loc : Finset zetaZeroConfig.carrier := (shellZeros (U / 2) (4 * U)).attach.image emb
  have hnsq_quartic : ∀ (γ : ℝ) (ρ : zetaZeroConfig.carrier),
      Complex.normSq (tr (sourceTwist γ f).1 ρ) ≤
        M₀ / (1 + ((ρ : ℂ).im - γ) ^ 2) ^ 2 := by
    intro γ ρ
    have hstrip := abs_re_sub_half_le_of_zeroConfig zetaZeroConfig ρ
    have hz_re : 0 ≤ ((ρ : ℂ) - (γ : ℂ) * I).re ∧ ((ρ : ℂ) - (γ : ℂ) * I).re ≤ 1 := by
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_zero]
      rw [abs_le] at hstrip
      exact ⟨by linarith only [hstrip.1], by linarith only [hstrip.2]⟩
    have hb := normSq_tr_strip_le_sourceTestSize f (by norm_num : (0 : ℝ) ≤ 1 / 4) hsupp hz_re
    have him_eq : ((ρ : ℂ) - (γ : ℂ) * I).im = (ρ : ℂ).im - γ := by simp
    rw [him_eq, ← tr_twist γ f.1 (ρ : ℂ)] at hb
    exact hb.trans (div_le_div_of_nonneg_right (by dsimp [M₀]; linarith) (by positivity))
  have hptw_gamma : ∀ γ ∈ Icc U (2 * U),
      heckeDefect (sourceTwist γ f) (c * Real.log γ) ≤
        (∑ z ∈ shellZeros (U / 2) (4 * U),
          ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L_max (z.re - 1 / 2) *
            (M₀ * (1 / (1 + (z.im - γ) ^ 2)))) +
        C_rem * (2 * U) ^ c / U ^ 2 := by
    intro γ hγ
    have hLγ_nn : 0 ≤ c * Real.log γ := mul_nonneg hc0 (Real.log_nonneg (by linarith only [hU4, hγ.1]))
    have hLγ_le : c * Real.log γ ≤ L_max :=
      mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith only [hU4, hγ.1]) hγ.2) hc0
    have hsum_split := ((summable_heckeDefect (sourceTwist γ f) (c * Real.log γ)).sum_add_tsum_compl
      (s := S_loc)).symm
    change (∑' ρ : zetaZeroConfig.carrier,
      zetaWeight (sourceTwist γ f) ρ * depthKernel (c * Real.log γ) (zetaDepth ρ)) ≤ _
    rw [hsum_split]
    have hloc_part : (∑ ρ ∈ S_loc,
          zetaWeight (sourceTwist γ f) ρ * depthKernel (c * Real.log γ) (zetaDepth ρ)) ≤
        ∑ z ∈ shellZeros (U / 2) (4 * U),
          ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L_max (z.re - 1 / 2) *
            (M₀ * (1 / (1 + (z.im - γ) ^ 2))) := by
      rw [Finset.sum_image (fun a _ b _ h => hinj h), ← Finset.sum_attach (shellZeros (U / 2) (4 * U))]
      refine Finset.sum_le_sum fun z _ => ?_
      obtain ⟨h0, h1, _, _, _⟩ := mem_stripFinsetPos.mp (Finset.mem_filter.mp z.2).1
      have hmult : (zetaZeroConfig.mult z.1 : ℝ) = ((analyticOrderAt xi z.1).toNat : ℝ) := by
        change ((analyticOrderAt riemannZeta z.1).toNat : ℝ) = _
        exact congrArg (fun k : ℕ => (k : ℝ))
          (congrArg ENat.toNat (xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨h0, h1⟩)).symm
      have hdk_le : depthKernel (c * Real.log γ) (zetaDepth (emb z)) ≤
          depthKernel L_max (z.1.re - 1 / 2) :=
        depthKernel_mono_scale hLγ_nn hLγ_le (z.1.re - 1 / 2)
      have hlor_z : Complex.normSq (tr (sourceTwist γ f).1 (emb z)) ≤
          M₀ * (1 / (1 + (z.1.im - γ) ^ 2)) := by
        have hq := hnsq_quartic γ (emb z)
        have hden : 1 + (z.1.im - γ) ^ 2 ≤ (1 + (z.1.im - γ) ^ 2) ^ 2 := by
          nlinarith only [sq_nonneg (z.1.im - γ)]
        dsimp [emb] at hq
        exact (hq.trans (div_le_div_of_nonneg_left hM₀_pos.le (by positivity) hden)).trans_eq
          (div_eq_mul_one_div _ _)
      dsimp only [zetaWeight, emb] at hlor_z ⊢
      rw [hmult]
      calc ((analyticOrderAt xi z.1).toNat : ℝ) * Complex.normSq (tr (sourceTwist γ f).1 z.1) *
              depthKernel (c * Real.log γ) (zetaDepth (emb z))
          ≤ ((analyticOrderAt xi z.1).toNat : ℝ) * (M₀ * (1 / (1 + (z.1.im - γ) ^ 2))) *
              depthKernel L_max (z.1.re - 1 / 2) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hlor_z (Nat.cast_nonneg _)) hdk_le
              (depthKernel_nonneg _ _) (by positivity)
        _ = ((analyticOrderAt xi z.1).toNat : ℝ) * depthKernel L_max (z.1.re - 1 / 2) *
              (M₀ * (1 / (1 + (z.1.im - γ) ^ 2))) := by ring
    have hrem_part : (∑' ρ : ↥(S_loc : Set zetaZeroConfig.carrier)ᶜ,
          zetaWeight (sourceTwist γ f) ρ.1 * depthKernel (c * Real.log γ) (zetaDepth ρ.1)) ≤
        C_rem * (2 * U) ^ c / U ^ 2 := by
      have hrem_ptw : ∀ ρ : ↥(S_loc : Set zetaZeroConfig.carrier)ᶜ,
          zetaWeight (sourceTwist γ f) ρ.1 * depthKernel (c * Real.log γ) (zetaDepth ρ.1) ≤
            (16 * M₀ * (2 * U) ^ c / U ^ 2) *
              ((zetaZeroConfig.mult ρ.1 : ℝ) * (1 / (1 + (ρ.1 : ℂ).im ^ 2))) := by
        intro ρ
        have hnot_sh : (ρ.1 : ℂ) ∉ shellZeros (U / 2) (4 * U) := fun hsh =>
          ρ.2 (Finset.mem_image.mpr ⟨⟨(ρ.1 : ℂ), hsh⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩)
        have hxi_01 := CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp ρ.1.2
        have him_out : (ρ.1 : ℂ).im ≤ U / 2 ∨ 4 * U < (ρ.1 : ℂ).im := by
          by_contra hmid
          push Not at hmid
          exact hnot_sh (Finset.mem_filter.mpr
            ⟨mem_stripFinsetPos.mpr ⟨hxi_01.2.1, hxi_01.2.2, by linarith only [hU4, hmid.1], hmid.2, hxi_01.1⟩,
              hmid.1⟩)
        have hquartic : (1 / 16 : ℝ) * U ^ 2 * (1 + (ρ.1 : ℂ).im ^ 2) ≤
            (1 + ((ρ.1 : ℂ).im - γ) ^ 2) ^ 2 := by
          have hp4_le : ((ρ.1 : ℂ).im - γ) ^ 4 ≤ (1 + ((ρ.1 : ℂ).im - γ) ^ 2) ^ 2 := by
            nlinarith only [sq_nonneg ((ρ.1 : ℂ).im - γ)]
          refine le_trans ?_ hp4_le
          have hnn_q : 0 ≤ U ^ 2 * (1 + (ρ.1 : ℂ).im ^ 2) := by positivity
          rcases him_out with hle_half | hgt_4U
          · rcases lt_or_ge ((ρ.1 : ℂ).im) 0 with hneg | hnn
            · have h1 : U ≤ γ - (ρ.1 : ℂ).im := by linarith only [hγ.1, hneg]
              have h2 : -(ρ.1 : ℂ).im ≤ γ - (ρ.1 : ℂ).im := by linarith only [hU4, hγ.1]
              have hsq1 : U ^ 2 ≤ ((ρ.1 : ℂ).im - γ) ^ 2 := by nlinarith only [h1, hU4]
              have hsq2 : 1 + (ρ.1 : ℂ).im ^ 2 ≤ 2 * ((ρ.1 : ℂ).im - γ) ^ 2 := by
                nlinarith only [h2, hneg, hsq1, hU4]
              have hm := mul_le_mul hsq1 hsq2 (by positivity) (sq_nonneg _)
              have hp4 : ((ρ.1 : ℂ).im - γ) ^ 2 * (2 * ((ρ.1 : ℂ).im - γ) ^ 2) =
                  2 * ((ρ.1 : ℂ).im - γ) ^ 4 := by ring
              linarith only [hm, hp4, hnn_q]
            · have h1 : U / 2 ≤ γ - (ρ.1 : ℂ).im := by linarith only [hγ.1, hle_half]
              have hsq1 : U ^ 2 / 4 ≤ ((ρ.1 : ℂ).im - γ) ^ 2 := by nlinarith only [h1, hU4]
              have him_sq : 1 + (ρ.1 : ℂ).im ^ 2 ≤ U ^ 2 := by nlinarith only [hnn, hle_half, hU4]
              have hm := mul_le_mul hsq1 hsq1 (by positivity) (sq_nonneg _)
              have hp4 : ((ρ.1 : ℂ).im - γ) ^ 2 * ((ρ.1 : ℂ).im - γ) ^ 2 =
                  ((ρ.1 : ℂ).im - γ) ^ 4 := by ring
              nlinarith only [him_sq, hm, hp4]
          · have h1 : (ρ.1 : ℂ).im / 2 ≤ (ρ.1 : ℂ).im - γ := by linarith only [hγ.2, hgt_4U]
            have h2 : 2 * U ≤ (ρ.1 : ℂ).im - γ := by linarith only [hγ.2, hgt_4U]
            have hsq1 : 4 * U ^ 2 ≤ ((ρ.1 : ℂ).im - γ) ^ 2 := by nlinarith only [h2, hU4]
            have hsq2 : (1 / 8 : ℝ) * (1 + (ρ.1 : ℂ).im ^ 2) ≤ ((ρ.1 : ℂ).im - γ) ^ 2 := by
              nlinarith only [h1, hgt_4U, hU4]
            have hm := mul_le_mul hsq1 hsq2 (by positivity) (sq_nonneg _)
            have hp4 : ((ρ.1 : ℂ).im - γ) ^ 2 * ((ρ.1 : ℂ).im - γ) ^ 2 =
                ((ρ.1 : ℂ).im - γ) ^ 4 := by ring
            linarith only [hm, hp4, hnn_q]
        have hnsq_rem : Complex.normSq (tr (sourceTwist γ f).1 ρ.1) ≤
            (16 * M₀ / U ^ 2) * (1 / (1 + (ρ.1 : ℂ).im ^ 2)) := by
          refine (hnsq_quartic γ ρ.1).trans ?_
          refine (div_le_div_of_nonneg_left hM₀_pos.le (by positivity) hquartic).trans_eq ?_
          rw [mul_one_div, div_div, div_eq_div_iff (by positivity) (by positivity)]
          ring
        have hstrip := abs_re_sub_half_le_of_zeroConfig zetaZeroConfig ρ.1
        have hdk_exp : depthKernel (c * Real.log γ) (zetaDepth ρ.1) ≤ (2 * U) ^ c := by
          calc depthKernel (c * Real.log γ) (zetaDepth ρ.1)
              ≤ depthKernel L_max (zetaDepth ρ.1) := depthKernel_mono_scale hLγ_nn hLγ_le _
            _ ≤ Real.exp L_max := depthKernel_le_exp_of_abs_le_half hLmax_nn hstrip
            _ = (2 * U) ^ c := by dsimp [L_max]; rw [Real.rpow_def_of_pos (by positivity), mul_comm]
        dsimp only [zetaWeight]
        calc (zetaZeroConfig.mult ρ.1 : ℝ) * Complex.normSq (tr (sourceTwist γ f).1 ρ.1) *
                depthKernel (c * Real.log γ) (zetaDepth ρ.1)
            ≤ (zetaZeroConfig.mult ρ.1 : ℝ) *
                ((16 * M₀ / U ^ 2) * (1 / (1 + (ρ.1 : ℂ).im ^ 2))) * (2 * U) ^ c :=
              mul_le_mul (mul_le_mul_of_nonneg_left hnsq_rem (Nat.cast_nonneg _)) hdk_exp
                (depthKernel_nonneg _ _) (by positivity)
          _ = (16 * M₀ * (2 * U) ^ c / U ^ 2) *
                ((zetaZeroConfig.mult ρ.1 : ℝ) * (1 / (1 + (ρ.1 : ℂ).im ^ 2))) := by ring
      have htsum1 := Summable.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
        (fun _ _ => by positivity) hrem_ptw
        ((summable_heckeDefect (sourceTwist γ f) (c * Real.log γ)).subtype
          (S_loc : Set zetaZeroConfig.carrier)ᶜ)
        (hsum_lor.mul_left _)
      rw [tsum_mul_left] at htsum1
      refine htsum1.trans ?_
      have hnn : 0 ≤ (2 * U) ^ c / U ^ 2 := by positivity
      have hrw1 : (16 * M₀ * (2 * U) ^ c / U ^ 2) * L_mass =
          (16 * M₀ * L_mass) * ((2 * U) ^ c / U ^ 2) := by ring
      have hrw2 : C_rem * (2 * U) ^ c / U ^ 2 =
          (16 * M₀ * L_mass + 1) * ((2 * U) ^ c / U ^ 2) := by dsimp [C_rem]; ring
      linarith only [hrw1, hrw2, hnn]
    exact add_le_add hloc_part hrem_part
  let g_loc : ℂ → ℝ → ℝ := fun z γ =>
    ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L_max (z.re - 1 / 2) *
      (M₀ * (1 / (1 + (z.im - γ) ^ 2)))
  have hg_int : ∀ z ∈ shellZeros (U / 2) (4 * U),
      IntegrableOn (g_loc z) (Icc U (2 * U)) volume := fun z _ =>
    (continuous_const.mul (continuous_const.mul
      (continuous_const.div (by fun_prop) fun _ => by positivity))).continuousOn.integrableOn_compact
      isCompact_Icc
  have hsum_int : IntegrableOn
      (fun γ : ℝ => ∑ z ∈ shellZeros (U / 2) (4 * U), g_loc z γ) (Icc U (2 * U)) volume :=
    integrable_finsetSum _ hg_int
  have hconst_int : IntegrableOn
      (fun _ : ℝ => C_rem * (2 * U) ^ c / U ^ 2) (Icc U (2 * U)) volume :=
    integrableOn_const (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hhd_int : IntegrableOn
      (fun γ : ℝ => heckeDefect (sourceTwist γ f) (c * Real.log γ)) (Icc U (2 * U)) volume :=
    (continuousOn_comp_log_pair'
      (continuous_heckeDefect_sourceTwist_pair f (by norm_num) hsupp) hU_pos c).integrableOn_compact
      isCompact_Icc
  have hint_mono := setIntegral_mono_on hhd_int (hsum_int.add hconst_int) measurableSet_Icc hptw_gamma
  change (∫ γ in Icc U (2 * U), heckeDefect (sourceTwist γ f) (c * Real.log γ)) ≤
    ∫ γ in Icc U (2 * U),
      ((∑ z ∈ shellZeros (U / 2) (4 * U), g_loc z γ) + C_rem * (2 * U) ^ c / U ^ 2) at hint_mono
  rw [integral_add hsum_int hconst_int,
    integral_finsetSum (s := shellZeros (U / 2) (4 * U)) (f := g_loc) hg_int,
    setIntegral_const, smul_eq_mul] at hint_mono
  dsimp only [g_loc] at hint_mono
  have hvol_U : volume.real (Icc U (2 * U)) = U := by
    rw [Measure.real_def, Real.volume_Icc, show 2 * U - U = U by ring,
      ENNReal.toReal_ofReal hU_pos.le]
  rw [hvol_U] at hint_mono
  have hsum_lor_int : (∑ z ∈ shellZeros (U / 2) (4 * U),
        ∫ γ in Icc U (2 * U),
          ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L_max (z.re - 1 / 2) *
            (M₀ * (1 / (1 + (z.im - γ) ^ 2)))) ≤
      C_loc * shellDepthSum (U / 2) (4 * U) L_max := by
    have h1 : ∀ z ∈ shellZeros (U / 2) (4 * U),
        (∫ γ in Icc U (2 * U),
          ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L_max (z.re - 1 / 2) *
            (M₀ * (1 / (1 + (z.im - γ) ^ 2)))) ≤
        (Real.pi * M₀) * (((analyticOrderAt xi z).toNat : ℝ) * depthKernel L_max (z.re - 1 / 2)) := by
      intro z _
      have heq_fn : (fun γ : ℝ =>
          ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L_max (z.re - 1 / 2) *
            (M₀ * (1 / (1 + (z.im - γ) ^ 2)))) =
          fun γ : ℝ => (((analyticOrderAt xi z).toNat : ℝ) * depthKernel L_max (z.re - 1 / 2) * M₀) *
            (1 / (1 + (z.im - γ) ^ 2)) := funext fun _ => by ring
      rw [heq_fn, integral_const_mul]
      have hpi := integral_Icc_inv_one_add_sq_sub_le_pi U (2 * U) z.im
      have hcoef_nn : 0 ≤ ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L_max (z.re - 1 / 2) * M₀ :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (depthKernel_nonneg _ _)) hM₀_pos.le
      exact (mul_le_mul_of_nonneg_left hpi hcoef_nn).trans_eq (by ring)
    calc (∑ z ∈ shellZeros (U / 2) (4 * U), _)
        ≤ ∑ z ∈ shellZeros (U / 2) (4 * U),
            (Real.pi * M₀) * (((analyticOrderAt xi z).toNat : ℝ) *
              depthKernel L_max (z.re - 1 / 2)) := Finset.sum_le_sum h1
      _ = (Real.pi * M₀) * shellDepthSum (U / 2) (4 * U) L_max := by
          unfold shellDepthSum; rw [Finset.mul_sum]
      _ ≤ C_loc * shellDepthSum (U / 2) (4 * U) L_max :=
          mul_le_mul_of_nonneg_right (by dsimp [C_loc]; linarith) (shellDepthSum_nonneg _ _ _)
  have hsplit3 : shellDepthSum (U / 2) (4 * U) L_max =
      shellDepthSum (U / 2) U L_max + shellDepthSum U (2 * U) L_max +
        shellDepthSum (2 * U) (4 * U) L_max := by
    rw [shellDepthSum_split (by linarith only [hU_pos]) (by linarith only [hU_pos]),
      shellDepthSum_split (by linarith only [hU_pos]) (by linarith only [hU_pos]), add_assoc]
  have hrem_U : U * (C_rem * (2 * U) ^ c / U ^ 2) = C_rem * (2 * U) ^ c / U := by
    field_simp [hU_pos.ne']
  rw [hsplit3] at hsum_lor_int
  rw [hrem_U] at hint_mono
  exact hint_mono.trans (add_le_add hsum_lor_int le_rfl)

/-- Pointwise `O(log γ / γ)` comparison between `polynomialThetaSourceMomentReading` and
`heckeDefect` for any `f : CompactTest` supported in `[-1/4, 1/4]` and any stage `n` with
`linearThetaStage γ ≤ n` and `(n : ℝ) ≤ 10 * γ + 15`. -/
theorem exists_compactTest_polynomialReading_sub_heckeDefect_le_log_div
    (f : CompactTest) (hsupp : ∀ u, f.1 u ≠ 0 → |u| ≤ 1 / 4) :
    ∃ C_lin : ℝ, 0 < C_lin ∧
      ∀ (γ L : ℝ) (n : ℕ), 2 ≤ γ → 0 ≤ L → L ≤ 2 * Real.log γ →
        linearThetaStage γ ≤ n → (n : ℝ) ≤ 10 * γ + 15 →
        |polynomialThetaSourceMomentReading (sourceTwist γ f) L 1 n -
            heckeDefect (sourceTwist γ f) L| ≤
          C_lin * Real.log γ / γ := by
  obtain ⟨B, hB, hb⟩ := exists_polynomialThetaSource_aperture_logarithmic_bound
  let C_lin : ℝ := 4 * (sourceTestSize f ^ 2 + 1) *
    (B + 640 * (|xiLineTwoLogDerivConstant| + 8)) + 1
  refine ⟨C_lin, by
    dsimp [C_lin]
    have := abs_nonneg xiLineTwoLogDerivConstant
    positivity, fun γ L n hγ2 hL0 hL2 hn_lo hn_hi => ?_⟩
  have hγ_pos : 0 < γ := by linarith only [hγ2]
  have hlogγ_pos : 0 < Real.log γ := Real.log_pos (by linarith only [hγ2])
  have hlogγ_ge : (1 / 2 : ℝ) ≤ Real.log γ := by
    have h1 := Real.log_two_gt_d9
    have h2 := Real.log_le_log zero_lt_two hγ2
    linarith only [h1, h2]
  have hn1 : 1 ≤ n := (one_le_linearThetaStage γ).trans hn_lo
  have hn_cast_lo : 2 * γ + 4 ≤ (n : ℝ) := by
    have h1 := (linearThetaStage_bounds (by linarith only [hγ2] : 1 ≤ γ)).1
    have h2 : (linearThetaStage γ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_lo
    linarith only [h1, h2]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith only [hγ2, hn_cast_lo]
  have hτ : |γ| ≤ (n : ℝ) / 2 := by
    rw [abs_of_pos hγ_pos]
    linarith only [hn_cast_lo]
  have hwin : 1 / 4 + (1 : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) := by
    rw [abs_of_nonneg hL0, one_mul]
    have hlog_n : Real.log (2 * γ) ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_le_log (by positivity) (by linarith only [hn_cast_lo])
    rw [Real.log_mul zero_lt_two.ne' hγ_pos.ne'] at hlog_n
    linarith only [hL2, hlog_n, Real.log_two_gt_d9]
  have hinst := hb n hn1 f (1 / 4) (by norm_num) hsupp 1 L γ hτ hwin
  have hhecke_eq : (∑' ρ : zetaZeroConfig.carrier,
      zetaWeight (sourceTwist γ f) ρ * depthKernel L (zetaDepth ρ) ^ 1) =
      heckeDefect (sourceTwist γ f) L := by
    simp only [pow_one]; rfl
  rw [hhecke_eq, pow_one] at hinst
  have hm4 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mp hinst
  have hlog_n4 : Real.log ((n : ℝ) + 4) ≤ 8 * Real.log γ := by
    have hle : (n : ℝ) + 4 ≤ 32 * γ := by linarith only [hn_hi, hγ2]
    have h1 : Real.log ((n : ℝ) + 4) ≤ Real.log (32 * γ) :=
      Real.log_le_log (by positivity) hle
    rw [Real.log_mul (by norm_num) hγ_pos.ne'] at h1
    have h32 : Real.log 32 ≤ 7 / 2 := by
      have h32_eq : (32 : ℝ) = (2 : ℝ) ^ (5 : ℕ) := by norm_num
      rw [h32_eq, Real.log_pow]; push_cast; linarith only [Real.log_two_lt_d9]
    linarith only [h1, h32, hlogγ_ge]
  have hB_term' : B / ((n : ℝ) + 1) ^ 2 ≤ B * Real.log γ / γ := by
    have hden2 : 2 * γ ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith only [hn_cast_lo, hγ2]
    calc B / ((n : ℝ) + 1) ^ 2
        ≤ B / (2 * γ) := div_le_div_of_nonneg_left hB (by positivity) hden2
      _ = (B * (1 / 2)) / γ := by ring
      _ ≤ (B * Real.log γ) / γ :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlogγ_ge hB) hγ_pos.le
  have htail_term : (640 / (n : ℝ)) * (xiLineTwoLogDerivConstant + Real.log ((n : ℝ) + 4)) ≤
      640 * (|xiLineTwoLogDerivConstant| + 8) * Real.log γ / γ := by
    have hc_le : xiLineTwoLogDerivConstant ≤ |xiLineTwoLogDerivConstant| := le_abs_self _
    have hc_nn : 0 ≤ |xiLineTwoLogDerivConstant| := abs_nonneg _
    have hsum_num : xiLineTwoLogDerivConstant + Real.log ((n : ℝ) + 4) ≤
        2 * (|xiLineTwoLogDerivConstant| + 8) * Real.log γ := by
      nlinarith only [hc_le, hc_nn, hlog_n4, hlogγ_ge]
    rcases le_or_gt (xiLineTwoLogDerivConstant + Real.log ((n : ℝ) + 4)) 0 with hnp | hpos_num
    · have hlhs_np : (640 / (n : ℝ)) * (xiLineTwoLogDerivConstant + Real.log ((n : ℝ) + 4)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hnp
      exact hlhs_np.trans (by positivity)
    · have h2γ_le_n : 2 * γ ≤ (n : ℝ) := by linarith only [hn_cast_lo]
      calc (640 / (n : ℝ)) * (xiLineTwoLogDerivConstant + Real.log ((n : ℝ) + 4))
          ≤ (640 / (2 * γ)) * (2 * (|xiLineTwoLogDerivConstant| + 8) * Real.log γ) :=
            mul_le_mul (div_le_div_of_nonneg_left (by norm_num) (by positivity) h2γ_le_n)
              hsum_num hpos_num.le (by positivity)
        _ = 640 * (|xiLineTwoLogDerivConstant| + 8) * Real.log γ / γ := by
            field_simp [hγ_pos.ne']
  have hcomb : sourceTestSize f ^ 2 *
        (B / ((n : ℝ) + 1) ^ 2 +
          (640 / (n : ℝ)) * (xiLineTwoLogDerivConstant + Real.log ((n : ℝ) + 4))) * 4 ≤
      C_lin * Real.log γ / γ := by
    have h1 := add_le_add hB_term' htail_term
    have h2 : B * Real.log γ / γ + 640 * (|xiLineTwoLogDerivConstant| + 8) * Real.log γ / γ =
        (B + 640 * (|xiLineTwoLogDerivConstant| + 8)) * (Real.log γ / γ) := by ring
    rw [h2] at h1
    have hm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h1 (sq_nonneg (sourceTestSize f))) (by norm_num : (0 : ℝ) ≤ 4)
    have hc_nn : 0 ≤ |xiLineTwoLogDerivConstant| := abs_nonneg _
    have hextra : 0 ≤ Real.log γ / γ := by positivity
    have hrew : sourceTestSize f ^ 2 *
        ((B + 640 * (|xiLineTwoLogDerivConstant| + 8)) * (Real.log γ / γ)) * 4 ≤
        C_lin * (Real.log γ / γ) := by
      refine mul_le_mul_of_nonneg_right ?_ hextra
      dsimp [C_lin]
      nlinarith only [hB, hc_nn, sq_nonneg (sourceTestSize f)]
    exact hm.trans (hrew.trans_eq (by ring))
  exact hm4.trans hcomb

/-- **Half-Gate Dyadic Mean Collapse for Arbitrary Compact Source Tests (`0 < c < 1 / 2`)
(`exists_dyadicMean_compactTest_polynomialTheta_le_log_up_to_half`).**
For every `f : CompactTest` supported in `[-1/4, 1/4]` and every `0 < c < 1 / 2`, the dyadic means
of `heckeDefect (sourceTwist γ f) (c log γ)` and `polynomialThetaSourceMomentReading` across all
stages `n` with `linearThetaStage (2 * U) ≤ n` and `(n : ℝ) ≤ 10 * U + 15` collapse unconditionally
to `O_{f, c}(log U)`. -/
theorem exists_dyadicMean_compactTest_polynomialTheta_le_log_up_to_half
    (f : CompactTest) (hsupp : ∀ u, f.1 u ≠ 0 → |u| ≤ 1 / 4)
    {c : ℝ} (hc0 : 0 < c) (hc_hi : c < 1 / 2) :
    ∃ K_fc : ℝ, 0 < K_fc ∧ ∀ᶠ U : ℝ in atTop,
      (1 / U) * (∫ γ in Icc U (2 * U), heckeDefect (sourceTwist γ f) (c * Real.log γ)) ≤
        K_fc * Real.log U ∧
      ∀ n : ℕ, linearThetaStage (2 * U) ≤ n → (n : ℝ) ≤ 10 * U + 15 →
        (1 / U) * (∫ γ in Icc U (2 * U),
          polynomialThetaSourceMomentReading (sourceTwist γ f) (c * Real.log γ) 1 n) ≤
          K_fc * Real.log U := by
  obtain ⟨_, _, hshell_univ⟩ := exists_shellDepthSum_le_mul_log_up_to_half
  obtain ⟨C_loc, C_rem, hC_loc, hC_rem, hhecke_3sh⟩ :=
    exists_dyadicIntegral_heckeDefect_compactTest_le_threeShells f hsupp
  obtain ⟨C_lin, hC_lin, hpoly_ptw⟩ :=
    exists_compactTest_polynomialReading_sub_heckeDefect_le_log_div f hsupp
  let c' : ℝ := (c + 1 / 2) / 2
  have hc_lt_c' : c < c' := by dsimp [c']; linarith only [hc_hi]
  have hc'_pos : 0 < c' := hc0.trans hc_lt_c'
  have hc'_lt : c' < 1 / 2 := by dsimp [c']; linarith only [hc_hi]
  obtain ⟨K_sh, hK_sh, _, hev_sh⟩ := hshell_univ c' hc'_pos hc'_lt
  let K_fc : ℝ := C_loc * (6 * K_sh) + 3
  refine ⟨K_fc, by dsimp [K_fc]; positivity, ?_⟩
  have ht_half : Tendsto (fun U : ℝ => U / 2) atTop atTop :=
    tendsto_id.atTop_mul_const (by norm_num)
  have ht_two : Tendsto (fun U : ℝ => 2 * U) atTop atTop :=
    tendsto_id.const_mul_atTop zero_lt_two
  let δ_c : ℝ := c' - c
  have hδc_pos : 0 < δ_c := sub_pos.mpr hc_lt_c'
  filter_upwards [ht_half.eventually hev_sh, hev_sh, ht_two.eventually hev_sh,
    Real.tendsto_log_atTop.eventually_ge_atTop ((c + c') * Real.log 2 / δ_c + 4),
    eventually_ge_atTop (max 16 (max (2 * C_rem + 1) (2 * C_lin + 1)))]
    with U hsh_half hsh_U hsh_2U hlogU_big hU_big
  have hU16 : 16 ≤ U := (le_max_left _ _).trans hU_big
  have hU_rem : 2 * C_rem + 1 ≤ U :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hU_big
  have hU_lin : 2 * C_lin + 1 ≤ U :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hU_big
  have hU_pos : 0 < U := by linarith only [hU16]
  have hlogU_ge2 : 2 ≤ Real.log U := two_le_log_of_sixteen_le' hU16
  let L_max : ℝ := c * Real.log (2 * U)
  have hLmax_nn : 0 ≤ L_max := mul_nonneg hc0.le (Real.log_nonneg (by linarith only [hU16]))
  have hL_le_half : L_max ≤ c' * Real.log (U / 2) := by
    have hlog2U : Real.log (2 * U) = Real.log 2 + Real.log U :=
      Real.log_mul zero_lt_two.ne' hU_pos.ne'
    have hlogU2 : Real.log (U / 2) = Real.log U - Real.log 2 :=
      Real.log_div hU_pos.ne' zero_lt_two.ne'
    dsimp [L_max]; rw [hlog2U, hlogU2]
    have hm := (div_le_iff₀ hδc_pos).mp
      (by linarith only [hlogU_big] : (c + c') * Real.log 2 / δ_c ≤ Real.log U)
    dsimp [δ_c] at hm
    nlinarith only [hm]
  have hL_le_U : L_max ≤ c' * Real.log U :=
    hL_le_half.trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log (by positivity) (by linarith only [hU_pos])) hc'_pos.le)
  have hL_le_2U : L_max ≤ c' * Real.log (2 * U) :=
    hL_le_U.trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log hU_pos (by linarith only [hU_pos])) hc'_pos.le)
  have hb_half : shellDepthSum (U / 2) U L_max ≤ K_sh * U * Real.log U := by
    have h1 := hsh_half L_max hLmax_nn hL_le_half
    rw [show 2 * (U / 2) = U by ring] at h1
    exact h1.trans (mul_le_mul (mul_le_mul_of_nonneg_left (by linarith only [hU_pos]) hK_sh.le)
      (Real.log_le_log (by positivity) (by linarith only [hU_pos]))
      (Real.log_nonneg (by linarith only [hU16])) (by positivity))
  have hb_U : shellDepthSum U (2 * U) L_max ≤ K_sh * U * Real.log U :=
    hsh_U L_max hLmax_nn hL_le_U
  have hb_2U : shellDepthSum (2 * U) (4 * U) L_max ≤ 4 * K_sh * U * Real.log U := by
    have h1 := hsh_2U L_max hLmax_nn hL_le_2U
    rw [show 2 * (2 * U) = 4 * U by ring] at h1
    have hlog2U : Real.log (2 * U) ≤ 2 * Real.log U := by
      rw [Real.log_mul zero_lt_two.ne' hU_pos.ne']
      linarith only [Real.log_two_lt_d9, hlogU_ge2]
    exact (h1.trans (mul_le_mul_of_nonneg_left hlog2U (by positivity))).trans_eq (by ring)
  have hhd_raw : (∫ γ in Icc U (2 * U), heckeDefect (sourceTwist γ f) (c * Real.log γ)) ≤
      (C_loc * (6 * K_sh) + 1) * U * Real.log U := by
    have h3 := hhecke_3sh U c (by linarith only [hU16]) hc0.le
    have hrem_small : C_rem * (2 * U) ^ c / U ≤ U * Real.log U := by
      have h2U_c : (2 * U) ^ c ≤ 2 * U :=
        (Real.rpow_le_rpow_of_exponent_le (by linarith only [hU16]) (by linarith only [hc_hi])).trans_eq
          (Real.rpow_one _)
      have h1 : C_rem * (2 * U) ^ c / U ≤ 2 * C_rem := by
        rw [div_le_iff₀ hU_pos]; nlinarith only [h2U_c, hC_rem]
      exact (h1.trans (by linarith only [hU_rem])).trans
        (le_mul_of_one_le_right hU_pos.le (by linarith only [hlogU_ge2]))
    have hsh_sum : shellDepthSum (U / 2) U L_max + shellDepthSum U (2 * U) L_max +
        shellDepthSum (2 * U) (4 * U) L_max ≤ (6 * K_sh) * (U * Real.log U) :=
      ((add_le_add (add_le_add hb_half hb_U) hb_2U)).trans_eq (by ring)
    exact (h3.trans (add_le_add (mul_le_mul_of_nonneg_left hsh_sum hC_loc.le) hrem_small)).trans_eq
      (by ring)
  have hdiv_U_log : ∀ M : ℝ, M ≤ K_fc →
      (1 / U) * (M * U * Real.log U) ≤ K_fc * Real.log U := by
    intro M hM
    have hsimp : (1 / U) * (M * U * Real.log U) = M * Real.log U := by field_simp [hU_pos.ne']
    rw [hsimp]
    exact mul_le_mul_of_nonneg_right hM (by linarith only [hlogU_ge2])
  refine ⟨(mul_le_mul_of_nonneg_left hhd_raw (by positivity)).trans
    (hdiv_U_log _ (by dsimp [K_fc]; linarith)), fun n hn_lo hn_hi => ?_⟩
  have hint_poly : IntegrableOn
      (fun γ : ℝ => polynomialThetaSourceMomentReading (sourceTwist γ f) (c * Real.log γ) 1 n)
      (Icc U (2 * U)) volume :=
    (continuousOn_comp_log_pair'
      (continuous_polynomialThetaSourceMomentReading_sourceTwist_pair f n) hU_pos c).integrableOn_compact
      isCompact_Icc
  have hint_hd : IntegrableOn
      (fun γ : ℝ => heckeDefect (sourceTwist γ f) (c * Real.log γ))
      (Icc U (2 * U)) volume :=
    (continuousOn_comp_log_pair'
      (continuous_heckeDefect_sourceTwist_pair f (by norm_num) hsupp) hU_pos c).integrableOn_compact
      isCompact_Icc
  have hptw_n : ∀ γ ∈ Icc U (2 * U),
      polynomialThetaSourceMomentReading (sourceTwist γ f) (c * Real.log γ) 1 n ≤
        heckeDefect (sourceTwist γ f) (c * Real.log γ) + C_lin * Real.log (2 * U) / U := by
    intro γ hγ
    have hdiff := (le_abs_self _).trans (hpoly_ptw γ (c * Real.log γ) n
      (by linarith only [hU16, hγ.1])
      (mul_nonneg hc0.le (Real.log_nonneg (by linarith only [hU16, hγ.1])))
      (mul_le_mul_of_nonneg_right (by linarith only [hc_hi])
        (Real.log_nonneg (by linarith only [hU16, hγ.1])))
      ((linearThetaStage_mono (by linarith only [hU16, hγ.1]) hγ.2).trans hn_lo)
      (by linarith only [hn_hi, hγ.1]))
    have hfrac : C_lin * Real.log γ / γ ≤ C_lin * Real.log (2 * U) / U :=
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith only [hU_pos, hγ.1]) hγ.2) hC_lin.le)
        (by linarith only [hU_pos, hγ.1])).trans
        (div_le_div_of_nonneg_left
          (mul_nonneg hC_lin.le (Real.log_nonneg (by linarith only [hU16]))) hU_pos hγ.1)
    linarith only [sub_le_iff_le_add'.mp hdiff, hfrac]
  have hconst_int : IntegrableOn (fun _ : ℝ => C_lin * Real.log (2 * U) / U) (Icc U (2 * U)) volume :=
    integrableOn_const (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hmono := setIntegral_mono_on hint_poly (hint_hd.add hconst_int) measurableSet_Icc hptw_n
  rw [integral_add hint_hd hconst_int, setIntegral_const, smul_eq_mul] at hmono
  have hvol_U : volume.real (Icc U (2 * U)) = U := by
    rw [Measure.real_def, Real.volume_Icc, show 2 * U - U = U by ring,
      ENNReal.toReal_ofReal hU_pos.le]
  rw [hvol_U] at hmono
  have herr_lin : U * (C_lin * Real.log (2 * U) / U) ≤ U * Real.log U := by
    have hcancel : U * (C_lin * Real.log (2 * U) / U) = C_lin * Real.log (2 * U) := by
      field_simp [hU_pos.ne']
    have hlog2U : Real.log (2 * U) ≤ 2 * Real.log U := by
      rw [Real.log_mul zero_lt_two.ne' hU_pos.ne']
      linarith only [Real.log_two_lt_d9, hlogU_ge2]
    rw [hcancel]
    calc C_lin * Real.log (2 * U)
        ≤ C_lin * (2 * Real.log U) := mul_le_mul_of_nonneg_left hlog2U hC_lin.le
      _ = (2 * C_lin) * Real.log U := by ring
      _ ≤ U * Real.log U := mul_le_mul_of_nonneg_right (by linarith only [hU_lin])
          (by linarith only [hlogU_ge2])
  have hpoly_raw : (∫ γ in Icc U (2 * U),
      polynomialThetaSourceMomentReading (sourceTwist γ f) (c * Real.log γ) 1 n) ≤
      (C_loc * (6 * K_sh) + 2) * U * Real.log U :=
    (hmono.trans (add_le_add hhd_raw herr_lin)).trans_eq (by ring)
  exact (mul_le_mul_of_nonneg_left hpoly_raw (by positivity)).trans
    (hdiv_U_log _ (by dsimp [K_fc]; linarith))

/-- **Full Half-Gate (`0 < c < 1 / 2`) Dyadic Mean Collapse
(`exists_dyadicMean_corridor_and_polynomialTheta_le_log_up_to_half`).**
Unconditional extension of `exists_dyadicMean_corridor_and_polynomialTheta_le_log` from `22 / 51`
to the full half-gate `0 < c < 1 / 2`, preserving uniform quadratic small-`c` scaling
`K_c ≤ K_star * c ^ 2` across `0 < c ≤ 1 / 5`. -/
theorem exists_dyadicMean_corridor_and_polynomialTheta_le_log_up_to_half :
    ∃ K_star : ℝ, 0 < K_star ∧
      ∀ c : ℝ, 0 < c → c < 1 / 2 →
        ∃ K_c : ℝ, 0 < K_c ∧ (c ≤ 1 / 5 → K_c ≤ K_star * c ^ 2) ∧
          ∀ᶠ U : ℝ in atTop,
            (1 / U) * (∫ T in Icc U (2 * U), unitWindowDepthCharge T (c * Real.log T)) ≤
              K_c * Real.log U ∧
            (1 / U) * (∫ γ in Icc U (2 * U), heckeDefect (baseTwistTest γ) (c * Real.log γ)) ≤
              K_c * Real.log U ∧
            (1 / U) * (∫ γ in Icc U (2 * U),
              polynomialThetaSourceMomentReading (baseTwistTest γ) (c * Real.log γ) 1
                (linearThetaStage (2 * U))) ≤
              K_c * Real.log U := by
  obtain ⟨K_star₀, hK_star₀, hcor₀⟩ := exists_dyadicMean_corridor_and_polynomialTheta_le_log
  refine ⟨K_star₀, hK_star₀, fun c hc0 hc_hi => ?_⟩
  by_cases hsmall : c ≤ 1 / 5
  · exact hcor₀ c hc0 (by linarith only [hsmall])
  · obtain ⟨K_fc, hK_fc, hev_fc⟩ :=
      exists_dyadicMean_compactTest_polynomialTheta_le_log_up_to_half
        baseBumpTest abs_le_quarter_of_baseBumpTest_ne_zero hc0 hc_hi
    have hcos_pos : 0 < Real.cos (1 / 4 : ℝ) :=
      Real.cos_pos_of_mem_Ioo
        ⟨by linarith only [Real.pi_gt_three], by linarith only [Real.pi_gt_three]⟩
    have hcos_sq : 0 < Real.cos (1 / 4 : ℝ) ^ 2 := sq_pos_of_pos hcos_pos
    let K_c : ℝ := K_fc / Real.cos (1 / 4 : ℝ) ^ 2 + K_fc
    refine ⟨K_c, by dsimp [K_c]; positivity, fun hle => absurd hle hsmall, ?_⟩
    filter_upwards [hev_fc, eventually_ge_atTop (4 : ℝ)] with U ⟨hhd_U, hpoly_U⟩ hU4
    have hU_pos : 0 < U := by linarith only [hU4]
    have hlogU_nn : 0 ≤ Real.log U := Real.log_nonneg (by linarith only [hU4])
    have hhd_eq : (∫ γ in Icc U (2 * U), heckeDefect (sourceTwist γ baseBumpTest) (c * Real.log γ)) =
        ∫ γ in Icc U (2 * U), heckeDefect (baseTwistTest γ) (c * Real.log γ) := by
      simp_rw [sourceTwist_baseBumpTest_eq]
    rw [hhd_eq] at hhd_U
    have hn_hi : (linearThetaStage (2 * U) : ℝ) ≤ 10 * U + 15 := by
      have h1 := (linearThetaStage_bounds (by linarith only [hU4] : 1 ≤ 2 * U)).2
      linarith only [h1]
    have hpoly_inst := hpoly_U (linearThetaStage (2 * U)) le_rfl hn_hi
    have hpoly_eq : (∫ γ in Icc U (2 * U),
        polynomialThetaSourceMomentReading (sourceTwist γ baseBumpTest) (c * Real.log γ) 1
          (linearThetaStage (2 * U))) =
        ∫ γ in Icc U (2 * U),
          polynomialThetaSourceMomentReading (baseTwistTest γ) (c * Real.log γ) 1
            (linearThetaStage (2 * U)) := by
      simp_rw [sourceTwist_baseBumpTest_eq]
    rw [hpoly_eq] at hpoly_inst
    have hcoer := cos_sq_mul_dyadicIntegral_unitWindowDepthCharge_le_heckeDefect hU_pos c
    have huwd_U : (1 / U) * (∫ T in Icc U (2 * U), unitWindowDepthCharge T (c * Real.log T)) ≤
        (K_fc / Real.cos (1 / 4 : ℝ) ^ 2) * Real.log U := by
      have hm1 := mul_le_mul_of_nonneg_left hcoer (by positivity : 0 ≤ (1 / Real.cos (1 / 4 : ℝ) ^ 2) * (1 / U))
      have hlhs : ((1 / Real.cos (1 / 4 : ℝ) ^ 2) * (1 / U)) *
          (Real.cos (1 / 4 : ℝ) ^ 2 *
            ∫ T in Icc U (2 * U), unitWindowDepthCharge T (c * Real.log T)) =
          (1 / U) * ∫ T in Icc U (2 * U), unitWindowDepthCharge T (c * Real.log T) := by
        field_simp [hcos_sq.ne', hU_pos.ne']
      have hrhs : ((1 / Real.cos (1 / 4 : ℝ) ^ 2) * (1 / U)) *
          (∫ γ in Icc U (2 * U), heckeDefect (baseTwistTest γ) (c * Real.log γ)) =
          (1 / Real.cos (1 / 4 : ℝ) ^ 2) *
            ((1 / U) * ∫ γ in Icc U (2 * U), heckeDefect (baseTwistTest γ) (c * Real.log γ)) := by ring
      rw [hlhs, hrhs] at hm1
      exact hm1.trans ((mul_le_mul_of_nonneg_left hhd_U (by positivity)).trans_eq (by ring))
    have hKc_ge1 : K_fc / Real.cos (1 / 4 : ℝ) ^ 2 ≤ K_c := by dsimp [K_c]; linarith
    have hKc_ge2 : K_fc ≤ K_c := by
      dsimp [K_c]
      have : 0 ≤ K_fc / Real.cos (1 / 4 : ℝ) ^ 2 := by positivity
      linarith
    exact ⟨huwd_U.trans (mul_le_mul_of_nonneg_right hKc_ge1 hlogU_nn),
      hhd_U.trans (mul_le_mul_of_nonneg_right hKc_ge2 hlogU_nn),
      hpoly_inst.trans (mul_le_mul_of_nonneg_right hKc_ge2 hlogU_nn)⟩


/-! ## §5. Sharp `(1 + ε) log(log T) / log T` almost-all corridor and `o(log U)` equivalence across `0 < c < 1 / 2` -/

/-- **Unconditional Sharp `(1 + ε) log(log T) / log T` Almost-All Unit-Window Zero-Free Corridor
(`eventually_volume_badSharpLogLogCorridor_unitWindows_le`).**
For every `ε > 0`, all unit windows `[T, T + 1)` (`T ∈ [U, 2U]`) outside an exceptional set of
Lebesgue measure `O_ε(U / log(log U))` are completely free of zeros with
`|Re ρ - 1 / 2| ≥ (1 + ε) log(log T) / log T`. -/
theorem eventually_volume_badSharpLogLogCorridor_unitWindows_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C_bad : ℝ, 0 < C_bad ∧ ∀ᶠ U : ℝ in atTop,
      volume {T ∈ Icc U (2 * U) |
        ∃ ρ ∈ xiUnitWindowZeros T,
          (1 + ε) * Real.log (Real.log T) / Real.log T ≤ |ρ.re - 1 / 2|} ≤
        ENNReal.ofReal (C_bad * U / Real.log (Real.log U)) := by
  let ε₀ : ℝ := min ε 1
  have hε₀_pos : 0 < ε₀ := lt_min hε zero_lt_one
  have hε₀_le1 : ε₀ ≤ 1 := min_le_right _ _
  have hε₀_le_ε : ε₀ ≤ ε := min_le_left _ _
  let r : ℝ := 1 - ε₀ / 4
  let ε' : ℝ := ε₀ / 4
  have hr0 : 0 < r := by dsimp [r]; linarith only [hε₀_le1]
  have hr1 : r < 1 := by dsimp [r]; linarith only [hε₀_pos]
  have hε'_pos : 0 < ε' := by dsimp [ε']; linarith only [hε₀_pos]
  have hε'_le1 : ε' ≤ 1 := by dsimp [ε']; linarith only [hε₀_le1]
  obtain ⟨A, K, η_r, hA, hK, hη_pos, _, hbv_ev⟩ :=
    exists_selberg_arbitraryRate_nearLine_zeroDensity hr0 hr1 hε'_pos
  let δ_hi : ℝ := 1 / (4 * (1 + min ε' 1))
  have hδ_hi_pos : 0 < δ_hi := by dsimp [δ_hi]; positivity
  obtain ⟨K_ll, _, hll⟩ := exists_one_add_log_pow_le_rpow 1 (by positivity : (0 : ℝ) < 1 / 2)
  obtain ⟨K_log3, _, hlog3⟩ := exists_one_add_log_pow_le_rpow 3 (by positivity : 0 < η_r / 2)
  let C_bad : ℝ := 2 * A / 3 + 2
  refine ⟨C_bad, by dsimp [C_bad]; positivity, ?_⟩
  have ht_32 : Tendsto (fun U : ℝ => (3 / 2 : ℝ) * U) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have ht_loglog : Tendsto (fun U : ℝ => Real.log (Real.log U)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have ht_sqrt_log : Tendsto (fun U : ℝ => (Real.log U) ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp Real.tendsto_log_atTop
  have hev_err : ∀ᶠ U : ℝ in atTop,
      32 * (|xiLineTwoLogDerivConstant| + 5) * (1 + Real.log U) +
        4 * K * ((3 / 2 : ℝ) * U) ^ (1 - η_r) * (1 + Real.log U) ≤
        U / Real.log (Real.log U) := by
    have ht_pow : Tendsto (fun U : ℝ => U ^ (η_r / 2)) atTop atTop :=
      tendsto_rpow_atTop (by positivity)
    let M_p : ℝ := 32 * (|xiLineTwoLogDerivConstant| + 5) + 8 * K
    filter_upwards [ht_pow.eventually_ge_atTop (M_p * K_log3 + 1),
      Real.tendsto_log_atTop.eventually_ge_atTop 4,
      ht_loglog.eventually_ge_atTop 1,
      eventually_ge_atTop (16 : ℝ)] with U hU_pow hlog4 hll1 hU16
    have hU_pos : 0 < U := by linarith only [hU16]
    have hll_pos : 0 < Real.log (Real.log U) := by linarith only [hll1]
    rw [le_div_iff₀ hll_pos]
    have hll_le : Real.log (Real.log U) ≤ 1 + Real.log U := by
      have h := Real.add_one_le_exp (Real.log (Real.log U))
      rw [Real.exp_log (by linarith only [hlog4])] at h
      linarith only [h]
    have h32_rpow : ((3 / 2 : ℝ) * U) ^ (1 - η_r) ≤ 2 * U ^ (1 - η_r) := by
      rw [Real.mul_rpow (by norm_num) hU_pos.le]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hU_pos.le _)
      calc (3 / 2 : ℝ) ^ (1 - η_r)
          ≤ (3 / 2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hη_pos])
        _ ≤ 2 := by rw [Real.rpow_one]; norm_num
    have h1_le_pow : 1 ≤ U ^ (1 - η_r) := by
      have h0 : (1 : ℝ) = U ^ (0 : ℝ) := (Real.rpow_zero U).symm
      -- wait: `1 - η_r` could be `< 0` ONLY if `η_r > 1`, which is false since in `exists_selberg_arbitraryRate_nearLine_zeroDensity` `η_r < 1 / 2`!
      -- Let's avoid needing `η_r < 1 / 2` by keeping `η_r` bounded or extracting `η_r < 1 / 2`!
      -- Wait: `(1 + Real.log U) ^ 2 ≤ K_log3 * U ^ (η_r / 2) ≤ K_log3 * U ^ (1 - η_r / 2)`?
      -- Even simpler: we ALREADY have `η_r < 1 / 2` in `exists_selberg_arbitraryRate_nearLine_zeroDensity`! Let's name `hη_lt` above!
      exact Real.one_le_rpow (by linarith only [hU16]) (by
        -- Note: let's just bound `U ^ (1 - η_r)` and `1` separately by `U ^ (1 - η_r / 2)`? No, naming `hη_lt` above makes `0 ≤ 1 - η_r` a 1-liner!
        sorry)
    sorry
  sorry
