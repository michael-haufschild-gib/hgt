import GaloisForLFunctions.RHTower.ClusterRobustHodgeExclusion

/-!
# Edge-concentrated Weil tests

The edge test at height `γ` is `f(u) = e^{-iγu}(s ⋆ g̃)(u)`, where

* `s(u) = sinh(δu)(b² - u²)₊^{5/2}` is the odd edge weight of `IsolatedDeepZeroWeilDetection`,
  concentrated near `u = ±b`, and
* `g = w^{⋆k} ⋆ ⋆_r (I∂ - r̄)w` is the root-killing factor of `LowHeightWeilTests`, with transform
  `G(x) = ŵ(x)^{k+2|L|+1} Π_{r ∈ L}(x - r)(x - r̄)`.

Its transform is `ŝ(z - γ) G(z - γ)`, and its Weil summand is `m_ρ Ψ(γ_ρ - γ)²` with the
real-structured profile `Ψ = I ŝ G` (`Wsummand_edgeTest`, `edgeProfile_conj`).  At `x₀ = -iδ` the
edge weight gives `ŝ(x₀) = P = ∫ s(u) sinh(δu) ≥ b² e^{2δ(b-2)}/16` (`sinhTest_energy_ge_exp`),
against `‖s‖_∞ ≤ cosh(δb) b⁵`: the test gains `e^{2δb}` over its `L²` norm.

* `integral_norm_sq_edgeTest_le`: `∫|f|² ≤ 2(b + M)(cosh(δb) b⁵ ‖g‖₁)²`, with `M = k + 2|L| + 1`,
  from `‖s ⋆ g̃‖_∞ ≤ ‖s‖_∞ ‖g‖₁` (`norm_weilTest_le_sup`) and `‖f ⋆ g̃‖₁ ≤ ‖f‖₁‖g‖₁`
  (`integral_norm_weilTest_le`).
* `integral_norm_edgeKill_le_ratio`: `‖g‖₁ ≤ |G(x₀)| Π_r (‖w'‖₁ + |r|‖w‖₁)/(‖w‖₁|x₀ - r|)`.
  The factors `ŵ` cost nothing, since `|ŵ(x₀)| ≥ ‖w‖₁`.
* `norm_paperFT_sinhTest_sub_le`: `ŝ` moves by at most `P/100` within `1/(10⁵ b⁵)` of `x₀`.
* `re_sq_edgeProfile_nonpos`: cluster zeros contribute `Re Ψ² ≤ 0`.
* `norm_sq_edgeProfile_tail_le`: `|Ψ|²(1 + |Re x|)^{3+E} ≤ e^{2|Im x| b}(4‖s‖_{C²})² C_G`.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23

/-! ### Norms of Weil tests -/

theorem norm_weilTest_le (f g : ℝ → ℂ) (x : ℝ) :
    ‖EF.weilTest f g x‖ ≤ ∫ t, ‖f t‖ * ‖g (t - x)‖ := by
  rw [weilTest_apply]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; ext t; rw [norm_mul, Complex.norm_conj]

/-- `‖(f ⋆ g̃)(x)‖ ≤ sup‖f‖ · ‖g‖₁`. -/
theorem norm_weilTest_le_sup {f g : ℝ → ℂ} {Mf : ℝ} (hMf : ∀ t, ‖f t‖ ≤ Mf)
    (hg : Integrable g) (x : ℝ) : ‖EF.weilTest f g x‖ ≤ Mf * ∫ t, ‖g t‖ := by
  refine (norm_weilTest_le f g x).trans ?_
  have hgi : Integrable (fun t => ‖g (t - x)‖) := hg.norm.comp_sub_right x
  calc ∫ t, ‖f t‖ * ‖g (t - x)‖ ≤ ∫ t, Mf * ‖g (t - x)‖ :=
        integral_mono_of_nonneg (Eventually.of_forall fun t => by positivity)
          (hgi.const_mul Mf)
          (Eventually.of_forall fun t => mul_le_mul_of_nonneg_right (hMf t) (norm_nonneg _))
    _ = Mf * ∫ t, ‖g t‖ := by
        rw [integral_const_mul, integral_sub_right_eq_self (fun t => ‖g t‖) x]

/-- `‖f ⋆ g̃‖₁ ≤ ‖f‖₁ ‖g‖₁`. -/
theorem integral_norm_weilTest_le {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ x, ‖EF.weilTest f g x‖ ≤ (∫ t, ‖f t‖) * ∫ t, ‖g t‖ := by
  set F : ℝ → ℝ := fun t => ‖f t‖ with hF
  set G : ℝ → ℝ := fun v => ‖g (-v)‖ with hG
  have hFi : Integrable F := hf.norm
  have hGi : Integrable G := hg.norm.comp_neg
  have hconv : Integrable (convolution F G (ContinuousLinearMap.mul ℝ ℝ) volume) :=
    hFi.integrable_convolution _ hGi
  have hval : ∫ x, convolution F G (ContinuousLinearMap.mul ℝ ℝ) volume x =
      (∫ t, ‖f t‖) * ∫ t, ‖g t‖ := by
    rw [integral_convolution _ hFi hGi, ContinuousLinearMap.mul_apply']
    congr 1
    exact integral_neg_eq_self (fun v => ‖g v‖) volume
  rw [← hval]
  refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _) hconv
    (Eventually.of_forall fun x => ?_)
  refine (norm_weilTest_le f g x).trans (le_of_eq ?_)
  rw [convolution_def]
  congr 1; ext t
  simp only [hF, hG, ContinuousLinearMap.mul_apply', neg_sub]


/-! ### `L¹` norms of the root convolutions -/

/-- `‖w‖₁` for the unit weight `w = (1 - u²)₊^{5/2}`. -/
def unitL1 : ℝ := ∫ u, |sinhTestWeight 1 u|

/-- `‖w'‖₁` for the unit weight. -/
def unitDerivL1 : ℝ := ∫ u, |deriv (sinhTestWeight 1) u|

theorem rpow_three_halves_of_neg {x : ℝ} (hx : x < 0) : x ^ (3 / 2 : ℝ) = 0 := by
  rw [Real.rpow_def_of_neg hx]
  have : Real.cos (3 / 2 * π) = 0 := by
    rw [show 3 / 2 * π = π / 2 + π by ring, Real.cos_add_pi, Real.cos_pi_div_two, neg_zero]
  rw [this, mul_zero]

theorem deriv_unitWeight_eq (u : ℝ) :
    deriv (sinhTestWeight 1) u = -(2 * u) * (5 / 2) * (1 ^ 2 - u ^ 2) ^ (3 / 2 : ℝ) := by
  have h := hasDerivAt_sub_sq_rpow 1 (5 / 2) (by norm_num) u
  have e : (5 / 2 : ℝ) - 1 = 3 / 2 := by norm_num
  rw [e] at h
  exact h.deriv

theorem abs_deriv_unitWeight_le (u : ℝ) : |deriv (sinhTestWeight 1) u| ≤ 5 := by
  rw [deriv_unitWeight_eq]
  rcases le_or_gt |u| 1 with hu | hu
  · have hb : 0 ≤ 1 ^ 2 - u ^ 2 := by nlinarith [abs_le.mp hu, sq_abs u]
    have h1 : (1 ^ 2 - u ^ 2) ^ (3 / 2 : ℝ) ≤ 1 :=
      Real.rpow_le_one hb (by nlinarith [sq_nonneg u]) (by norm_num)
    have h0 : 0 ≤ (1 ^ 2 - u ^ 2) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hb _
    rw [abs_mul, abs_mul, abs_of_nonneg h0, abs_neg, abs_mul, abs_two]
    have : |(5 / 2 : ℝ)| = 5 / 2 := by norm_num
    rw [this]
    nlinarith [abs_nonneg u]
  · have hneg : 1 ^ 2 - u ^ 2 < 0 := by nlinarith [sq_abs u, abs_nonneg u]
    rw [rpow_three_halves_of_neg hneg, mul_zero, abs_zero]; norm_num

theorem deriv_unitWeight_eq_zero {u : ℝ} (hu : 1 < |u|) : deriv (sinhTestWeight 1) u = 0 := by
  rw [deriv_unitWeight_eq]
  have hneg : 1 ^ 2 - u ^ 2 < 0 := by nlinarith [sq_abs u, abs_nonneg u]
  rw [rpow_three_halves_of_neg hneg, mul_zero]

theorem unitDerivL1_le : unitDerivL1 ≤ 10 := by
  have := integral_le_of_bound_on_Icc (g := fun u => |deriv (sinhTestWeight 1) u|) zero_le_one
    (fun _ => abs_nonneg _) (fun u _ => abs_deriv_unitWeight_le u)
    (fun u hu => by simp [deriv_unitWeight_eq_zero hu])
  unfold unitDerivL1; linarith

theorem unitDerivL1_nonneg : 0 ≤ unitDerivL1 := integral_nonneg fun _ => abs_nonneg _

theorem unitL1_eq : unitL1 = ∫ u, sinhTestWeight 1 u := by
  unfold unitL1; congr 1; ext u; exact abs_of_nonneg (sinhTestWeight_nonneg 1 u)

theorem unitWeightFloor_le_unitL1 : unitWeightFloor ≤ unitL1 := by
  have := unitWeightFloor_le 0
  simp only [zero_mul, Real.cosh_zero, mul_one] at this
  rw [unitL1_eq]; exact this

theorem unitL1_le : unitL1 ≤ 2 := by
  have := integral_le_of_bound_on_Icc (g := fun u => |sinhTestWeight 1 u|) zero_le_one
    (fun _ => abs_nonneg _) (fun u hu => by
      rw [abs_of_nonneg (sinhTestWeight_nonneg 1 u)]
      have hb : 0 ≤ 1 ^ 2 - u ^ 2 := by nlinarith [abs_le.mp hu, sq_abs u]
      exact Real.rpow_le_one hb (by nlinarith [sq_nonneg u]) (by norm_num))
    (fun u hu => by
      have hneg : 1 ^ 2 - u ^ 2 < 0 := by nlinarith [sq_abs u, abs_nonneg u]
      simp only [sinhTestWeight, rpow_five_halves_of_neg hneg, abs_zero])
  unfold unitL1; linarith

theorem unitL1_pos : 0 < unitL1 := lt_of_lt_of_le unitWeightFloor_pos unitWeightFloor_le_unitL1

/-- `‖(I∂ - r̄)w‖₁ ≤ ‖w'‖₁ + |r| ‖w‖₁`. -/
theorem integral_norm_rootShiftFactor_le (r : ℂ) :
    ∫ u, ‖rootShiftFactor (sinhTestWeight 1) r u‖ ≤ unitDerivL1 + ‖r‖ * unitL1 := by
  have hw := sinhTestWeight_contDiff 1
  have hsupp := sinhTestWeight_supp (zero_le_one (α := ℝ))
  have hd : Continuous (deriv (sinhTestWeight 1)) := hw.continuous_deriv (by norm_num)
  have hdi : Integrable (fun u => |deriv (sinhTestWeight 1) u|) := by
    refine hd.abs.integrable_of_hasCompactSupport ?_
    have hs : ∀ u, |deriv (sinhTestWeight 1) u| ≠ 0 → |u| ≤ 1 := fun u hu => by
      by_contra h
      exact hu (by simp [deriv_unitWeight_eq_zero (lt_of_not_ge h)])
    exact hasCompactSupport_of_support_subset_abs hs
  have hwi : Integrable (fun u => |sinhTestWeight 1 u|) :=
    hw.continuous.abs.integrable_of_hasCompactSupport
      (hasCompactSupport_of_support_subset_abs hsupp).abs
  have hfi : Integrable (fun u => ‖rootShiftFactor (sinhTestWeight 1) r u‖) :=
    ((continuous_rootFactor hw r).norm).integrable_of_hasCompactSupport
      (hasCompactSupport_of_support_subset_abs (rootFactor_supp hsupp r)).norm
  calc ∫ u, ‖rootShiftFactor (sinhTestWeight 1) r u‖
      ≤ ∫ u, (|deriv (sinhTestWeight 1) u| + ‖r‖ * |sinhTestWeight 1 u|) := by
        refine integral_mono hfi (hdi.add (hwi.const_mul _)) fun u => ?_
        simp only [rootShiftFactor]
        refine (norm_sub_le _ _).trans (le_of_eq ?_)
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_conj,
          Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    _ = unitDerivL1 + ‖r‖ * unitL1 := by
        rw [integral_add hdi (hwi.const_mul _), integral_const_mul]; rfl

/-- `‖rootConv w rs‖₁ ≤ ‖w‖₁ Π (‖w'‖₁ + |r| ‖w‖₁)`. -/
theorem integral_norm_rootConv_le (rs : List ℂ) :
    ∫ u, ‖rootConv (sinhTestWeight 1) rs u‖ ≤
      unitL1 * (rs.map fun r => unitDerivL1 + ‖r‖ * unitL1).prod := by
  have hw := sinhTestWeight_contDiff 1
  have heven := sinhTestWeight_even 1
  have hsupp := sinhTestWeight_supp (zero_le_one (α := ℝ))
  induction rs with
  | nil =>
    simp only [rootConv, List.map_nil, List.prod_nil, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
    rfl
  | cons r rs ih =>
    obtain ⟨ihc, ihs, -⟩ := rootConv_props hw heven hsupp rs
    have hi1 : Integrable (rootConv (sinhTestWeight 1) rs) :=
      ihc.continuous.integrable_of_hasCompactSupport (hasCompactSupport_of_support_subset_abs ihs)
    have hi2 : Integrable (rootShiftFactor (sinhTestWeight 1) r) :=
      (continuous_rootFactor hw r).integrable_of_hasCompactSupport
        (hasCompactSupport_of_support_subset_abs (rootFactor_supp hsupp r))
    have hnn : 0 ≤ ∫ u, ‖rootShiftFactor (sinhTestWeight 1) r u‖ :=
      integral_nonneg fun _ => norm_nonneg _
    calc ∫ u, ‖rootConv (sinhTestWeight 1) (r :: rs) u‖
        ≤ (∫ u, ‖rootConv (sinhTestWeight 1) rs u‖) *
            ∫ u, ‖rootShiftFactor (sinhTestWeight 1) r u‖ :=
          integral_norm_weilTest_le hi1 hi2
      _ ≤ (unitL1 * (rs.map fun r => unitDerivL1 + ‖r‖ * unitL1).prod) *
            (unitDerivL1 + ‖r‖ * unitL1) :=
          mul_le_mul ih (integral_norm_rootShiftFactor_le r) hnn
            (by have := unitL1_pos.le; exact le_trans (integral_nonneg fun _ => norm_nonneg _) ih)
      _ = _ := by simp only [List.map_cons, List.prod_cons]; ring

/-- `‖plainConv w k f‖₁ ≤ ‖f‖₁ ‖w‖₁^k`. -/
theorem integral_norm_plainConv_le {f : ℝ → ℂ} {A : ℝ} (hf : ContDiff ℝ 2 f)
    (hfs : ∀ u, f u ≠ 0 → |u| ≤ A) (k : ℕ) :
    ∫ u, ‖plainConv (sinhTestWeight 1) k f u‖ ≤ (∫ u, ‖f u‖) * unitL1 ^ k := by
  have hw := sinhTestWeight_contDiff 1
  have heven := sinhTestWeight_even 1
  have hsupp := sinhTestWeight_supp (zero_le_one (α := ℝ))
  induction k with
  | zero => simp [plainConv]
  | succ k ih =>
    obtain ⟨ihc, ihs, -⟩ := plainConv_props hw heven hsupp hf hfs k
    have hi1 : Integrable (plainConv (sinhTestWeight 1) k f) :=
      ihc.continuous.integrable_of_hasCompactSupport (hasCompactSupport_of_support_subset_abs ihs)
    have hi2 : Integrable (fun u => (sinhTestWeight 1 u : ℂ)) :=
      (Complex.continuous_ofReal.comp hw.continuous).integrable_of_hasCompactSupport
        (hasCompactSupport_ofReal_of_abs hsupp)
    have hw1 : ∫ u, ‖(sinhTestWeight 1 u : ℂ)‖ = unitL1 := by
      unfold unitL1; congr 1; ext u; rw [Complex.norm_real, Real.norm_eq_abs]
    calc ∫ u, ‖plainConv (sinhTestWeight 1) (k + 1) f u‖
        ≤ (∫ u, ‖plainConv (sinhTestWeight 1) k f u‖) * ∫ u, ‖(sinhTestWeight 1 u : ℂ)‖ :=
          integral_norm_weilTest_le hi1 hi2
      _ ≤ ((∫ u, ‖f u‖) * unitL1 ^ k) * unitL1 := by
          rw [hw1]; exact mul_le_mul_of_nonneg_right ih unitL1_pos.le
      _ = _ := by ring


/-! ### The edge-concentrated test -/

/-- For a real odd test, `conj ŝ(z̄) = -ŝ(z)`. -/
theorem conj_paperFT_conj_of_odd {s : ℝ → ℝ} (hodd : ∀ u, s (-u) = -s u) (z : ℂ) :
    conj (paperFT (fun u => (s u : ℂ)) (conj z)) = -paperFT (fun u => (s u : ℂ)) z := by
  rw [paperFT_def, paperFT_def, ← integral_conj, ← integral_neg,
    ← integral_neg_eq_self (fun u : ℝ => -((s u : ℂ) * cexp (I * z * u)))]
  congr 1 with u
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, hodd]
  simp only [map_mul, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal, Complex.ofReal_neg]
  ring_nf

/-- The killing factor `w^{⋆k} ⋆ ⋆_{r} (I∂ - r̄)w` over the conjugate pairs of `L`. -/
def edgeKill (k : ℕ) (L : List ℂ) : ℝ → ℂ :=
  plainConv (sinhTestWeight 1) k (rootConv (sinhTestWeight 1) (pairRoots L))

theorem edgeKill_props (k : ℕ) (L : List ℂ) :
    ContDiff ℝ 2 (edgeKill k L) ∧
      (∀ u, edgeKill k L u ≠ 0 → |u| ≤ (k + 2 * L.length + 1 : ℕ)) ∧
      ∀ z, paperFT (edgeKill k L) z = lowHeightProfile (sinhTestWeight 1) k L z := by
  have hw := sinhTestWeight_contDiff 1
  have heven := sinhTestWeight_even 1
  have hsupp := sinhTestWeight_supp (zero_le_one (α := ℝ))
  obtain ⟨hrc, hrs, hrf⟩ := rootConv_props hw heven hsupp (pairRoots L)
  obtain ⟨hpc, hps, hpf⟩ := plainConv_props hw heven hsupp hrc hrs k
  refine ⟨hpc, fun u hu => ?_, fun z => ?_⟩
  · have := hps u hu
    rw [pairRoots_length] at this
    push_cast at this ⊢
    linarith
  · unfold edgeKill
    rw [hpf, hrf, prod_pairRoots, pairRoots_length, lowHeightProfile]
    ring

/-- The core `s ⋆ g̃` of the edge test, with `s = sinh(δu)(b² - u²)₊^{5/2}`. -/
def edgeCore (b δ : ℝ) (k : ℕ) (L : List ℂ) : ℝ → ℂ :=
  EF.weilTest (fun u => (sinhTest b δ u : ℂ)) (edgeKill k L)

/-- The edge test `e^{-iγu}(s ⋆ g̃)(u)`. -/
def edgeTest (γ b δ : ℝ) (k : ℕ) (L : List ℂ) : ℝ → ℂ :=
  fun u => cexp (-(I * γ * u)) * edgeCore b δ k L u

/-- The profile `I ŝ(x) G(x)` of the edge test; the Weil summand is `m_ρ Ψ(x_ρ)²`. -/
def edgeProfile (b δ : ℝ) (k : ℕ) (L : List ℂ) (x : ℂ) : ℂ :=
  I * paperFT (fun u => (sinhTest b δ u : ℂ)) x * lowHeightProfile (sinhTestWeight 1) k L x

theorem edgeCore_props {b : ℝ} (hb : 0 ≤ b) (δ : ℝ) (k : ℕ) (L : List ℂ) :
    ContDiff ℝ 2 (edgeCore b δ k L) ∧
      (∀ u, edgeCore b δ k L u ≠ 0 → |u| ≤ b + (k + 2 * L.length + 1 : ℕ)) ∧
      ∀ z, paperFT (edgeCore b δ k L) z = paperFT (fun u => (sinhTest b δ u : ℂ)) z *
        lowHeightProfile (sinhTestWeight 1) k L z := by
  obtain ⟨hgc, hgs, hgf⟩ := edgeKill_props k L
  have hsc : ContDiff ℝ 2 (fun u => (sinhTest b δ u : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (sinhTest_contDiff b δ)
  have hss : ∀ u, (sinhTest b δ u : ℂ) ≠ 0 → |u| ≤ b := fun u hu =>
    sinhTest_supp (δ := δ) hb u (fun h => hu (by simp [h]))
  have hscs : HasCompactSupport (fun u => (sinhTest b δ u : ℂ)) :=
    hasCompactSupport_of_support_subset_abs hss
  have hgcs : HasCompactSupport (edgeKill k L) := hasCompactSupport_of_support_subset_abs hgs
  refine ⟨EF.weilTest_contDiff hsc hgc.continuous hscs, fun u hu =>
    weilTest_support_abs_le hss hgs u hu, fun z => ?_⟩
  unfold edgeCore
  rw [EF.paperFT_weilTest hsc.continuous hgc.continuous hscs hgcs, hgf,
    lowHeightProfile_conj (sinhTestWeight_even 1), Complex.conj_conj]

theorem edgeTest_props {γ b : ℝ} (hb : 0 ≤ b) (δ : ℝ) (k : ℕ) (L : List ℂ) :
    ContDiff ℝ 2 (edgeTest γ b δ k L) ∧
      (∀ u, edgeTest γ b δ k L u ≠ 0 → |u| ≤ b + (k + 2 * L.length + 1 : ℕ)) ∧
      ∀ z, paperFT (edgeTest γ b δ k L) z = -I * edgeProfile b δ k L (z - γ) := by
  obtain ⟨hc, hs, hf⟩ := edgeCore_props hb δ k L
  refine ⟨?_, fun u hu => hs u (fun h => hu (by simp [edgeTest, h])), fun z => ?_⟩
  · unfold edgeTest
    have h1 : ContDiff ℝ 2 (fun u : ℝ => (u : ℂ)) := Complex.ofRealCLM.contDiff
    have h2 : ContDiff ℝ 2 (fun u : ℝ => -(I * (γ : ℂ) * (u : ℂ))) := (contDiff_const.mul h1).neg
    exact (Complex.contDiff_exp.comp h2).mul hc
  · unfold edgeTest
    rw [paperFT_modulate, hf, edgeProfile]
    ring_nf
    rw [Complex.I_sq]
    ring

theorem edgeProfile_conj (b δ : ℝ) (k : ℕ) (L : List ℂ) (z : ℂ) :
    edgeProfile b δ k L (conj z) = conj (edgeProfile b δ k L z) := by
  have hs := conj_paperFT_conj_of_odd (sinhTest_odd b δ) z
  have hs' : paperFT (fun u => (sinhTest b δ u : ℂ)) (conj z) =
      -conj (paperFT (fun u => (sinhTest b δ u : ℂ)) z) := by
    have := congrArg conj hs
    rwa [Complex.conj_conj, map_neg] at this
  unfold edgeProfile
  rw [hs', lowHeightProfile_conj (sinhTestWeight_even 1), map_mul, map_mul, Complex.conj_I]
  ring

/-- Real structure: the Weil summand of the edge test is `m_ρ Ψ(x_ρ)²`. -/
theorem Wsummand_edgeTest (Z : ZeroConfig) {γ b : ℝ} (hb : 0 ≤ b) (δ : ℝ) (k : ℕ)
    (L : List ℂ) (ρ : ℂ) :
    Z.Wsummand (edgeTest γ b δ k L) (edgeTest γ b δ k L) ρ =
      (Z.mult ρ : ℂ) * edgeProfile b δ k L (gammaOf ρ - γ) ^ 2 := by
  obtain ⟨-, -, hf⟩ := edgeTest_props (γ := γ) hb δ k L
  rw [ZeroConfig.Wsummand, hf, hf]
  have hc : conj (gammaOf ρ) - (γ : ℂ) = conj (gammaOf ρ - γ) := by
    rw [map_sub, Complex.conj_ofReal]
  rw [hc, edgeProfile_conj, map_mul, map_neg, Complex.conj_I, Complex.conj_conj]
  ring_nf
  rw [Complex.I_sq]
  ring


/-! ### The `L²` norm of the edge test -/

theorem abs_sinhTest_le_global {b δ : ℝ} (hb : 0 ≤ b) (hδ : 0 ≤ δ) (t : ℝ) :
    |sinhTest b δ t| ≤ Real.cosh (δ * b) * b ^ 5 := by
  rcases le_or_gt |t| b with ht | ht
  · exact abs_sinhTest_le hb hδ ht
  · rw [sinhTest_eq_zero hb ht, abs_zero]; positivity

theorem integral_norm_edgeKill_le (k : ℕ) (L : List ℂ) :
    ∫ u, ‖edgeKill k L u‖ ≤
      unitL1 ^ (k + 1) * ((pairRoots L).map fun r => unitDerivL1 + ‖r‖ * unitL1).prod := by
  have hw := sinhTestWeight_contDiff 1
  have heven := sinhTestWeight_even 1
  have hsupp := sinhTestWeight_supp (zero_le_one (α := ℝ))
  obtain ⟨hrc, hrs, -⟩ := rootConv_props hw heven hsupp (pairRoots L)
  refine (integral_norm_plainConv_le hrc hrs k).trans ?_
  have hr := integral_norm_rootConv_le (pairRoots L)
  calc (∫ u, ‖rootConv (sinhTestWeight 1) (pairRoots L) u‖) * unitL1 ^ k
      ≤ (unitL1 * ((pairRoots L).map fun r => unitDerivL1 + ‖r‖ * unitL1).prod) * unitL1 ^ k :=
        mul_le_mul_of_nonneg_right hr (pow_nonneg unitL1_pos.le _)
    _ = _ := by ring

/-- `∫ |f|² ≤ 2(b + M)(cosh(δb) b⁵ ‖g‖₁)²` for the edge test, `M = k + 2|L| + 1`. -/
theorem integral_norm_sq_edgeTest_le {γ b δ : ℝ} (hb : 0 ≤ b) (hδ : 0 ≤ δ) (k : ℕ)
    (L : List ℂ) :
    ∫ u, ‖edgeTest γ b δ k L u‖ ^ 2 ≤
      2 * (b + (k + 2 * L.length + 1 : ℕ)) *
        (Real.cosh (δ * b) * b ^ 5 * ∫ u, ‖edgeKill k L u‖) ^ 2 := by
  obtain ⟨hgc, hgs, -⟩ := edgeKill_props k L
  obtain ⟨-, hcs, -⟩ := edgeCore_props hb δ k L
  have hgi : Integrable (edgeKill k L) :=
    hgc.continuous.integrable_of_hasCompactSupport (hasCompactSupport_of_support_subset_abs hgs)
  have hsup : ∀ u, ‖edgeCore b δ k L u‖ ≤ Real.cosh (δ * b) * b ^ 5 * ∫ u, ‖edgeKill k L u‖ :=
    fun u => norm_weilTest_le_sup (fun t => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_sinhTest_le_global hb hδ t) hgi u
  have hnorm : ∀ u, ‖edgeTest γ b δ k L u‖ = ‖edgeCore b δ k L u‖ := fun u => by
    rw [edgeTest, norm_mul, Complex.norm_exp]
    simp
  have hA : 0 ≤ b + (k + 2 * L.length + 1 : ℕ) := by positivity
  refine integral_le_of_bound_on_Icc hA (fun _ => sq_nonneg _) (fun u _ => ?_) (fun u hu => ?_)
  · rw [hnorm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hsup u) 2
  · have : edgeCore b δ k L u = 0 := by
      by_contra h; exact absurd (hcs u h) (not_le.mpr hu)
    rw [hnorm, this, norm_zero]; norm_num

/-! ### The value at the deep zero -/

theorem edgeProfile_neg_I_mul (b δ : ℝ) (hb : 0 ≤ b) (k : ℕ) (L : List ℂ) :
    edgeProfile b δ k L (-(I * δ)) =
      I * ((∫ u, sinhTest b δ u * Real.sinh (δ * u) : ℝ) : ℂ) *
        lowHeightProfile (sinhTestWeight 1) k L (-(I * δ)) := by
  unfold edgeProfile
  rw [paperFT_odd_neg_I_mul (sinhTest_contDiff b δ).continuous (sinhTest_supp hb)
    (sinhTest_odd b δ) δ]

theorem unitL1_le_norm_paperFT_neg_I_mul (δ : ℝ) :
    unitL1 ≤ ‖paperFT (fun u => (sinhTestWeight 1 u : ℂ)) (-(I * δ))‖ := by
  rw [paperFT_unitWeight_neg_I_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (integral_abs_unitWeight_le δ).trans (le_abs_self _)

theorem norm_list_prod_map_eq_prod_norm (l : List ℂ) (f : ℂ → ℂ) :
    ‖(l.map f).prod‖ = (l.map fun r => ‖f r‖).prod := by
  induction l with
  | nil => simp
  | cons r l ih => simp only [List.map_cons, List.prod_cons, norm_mul, ih]

theorem list_prod_map_mul' (l : List ℂ) (f g : ℂ → ℝ) :
    (l.map fun r => f r * g r).prod = (l.map f).prod * (l.map g).prod := by
  induction l with
  | nil => simp
  | cons r l ih => simp only [List.map_cons, List.prod_cons, ih]; ring

/-- **Killing ratio.**  `‖g‖₁ ≤ |G(x₀)| Π_r (‖w'‖₁ + |r|‖w‖₁)/(‖w‖₁ |x₀ - r|)`. -/
theorem integral_norm_edgeKill_le_ratio (δ : ℝ) (k : ℕ) (L : List ℂ)
    (hr : ∀ r ∈ pairRoots L, -(I * (δ : ℂ)) - r ≠ 0) :
    ∫ u, ‖edgeKill k L u‖ ≤
      ‖lowHeightProfile (sinhTestWeight 1) k L (-(I * δ))‖ *
        ((pairRoots L).map fun r =>
          (unitDerivL1 + ‖r‖ * unitL1) / (unitL1 * ‖-(I * (δ : ℂ)) - r‖)).prod := by
  set x₀ := -(I * (δ : ℂ))
  set l := pairRoots L with hl
  set c : ℂ → ℝ := fun r => unitDerivL1 + ‖r‖ * unitL1 with hc
  set q : ℂ → ℝ := fun r => c r / (unitL1 * ‖x₀ - r‖) with hq
  have hm0 := unitL1_pos
  have hW := unitL1_le_norm_paperFT_neg_I_mul δ
  set W := ‖paperFT (fun u => (sinhTestWeight 1 u : ℂ)) x₀‖ with hWdef
  have hsplit : (l.map c).prod = unitL1 ^ l.length * ((l.map fun r => ‖x₀ - r‖).prod *
      (l.map q).prod) := by
    have hpt : ∀ r ∈ l, c r = unitL1 * (‖x₀ - r‖ * q r) := by
      intro r hrl
      have hn : ‖x₀ - r‖ ≠ 0 := norm_ne_zero_iff.mpr (hr r hrl)
      simp only [hq]; field_simp
    rw [List.map_congr_left hpt, list_prod_map_mul', list_prod_map_mul',
      List.map_const', List.prod_replicate]
  have hG : ‖lowHeightProfile (sinhTestWeight 1) k L x₀‖ =
      W ^ (k + 1) * W ^ l.length * (l.map fun r => ‖x₀ - r‖).prod := by
    rw [lowHeightProfile_eq_pairRoots, norm_mul, norm_pow, norm_list_prod_map_eq_prod_norm, ← pow_add]
    congr 2
    rw [hl, pairRoots_length]; ring
  have hq0 : 0 ≤ (l.map q).prod := List.prod_nonneg fun y hy => by
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp hy
    have := unitDerivL1_nonneg; simp only [hq, hc]; positivity
  have hn0 : 0 ≤ (l.map fun r => ‖x₀ - r‖).prod := List.prod_nonneg fun y hy => by
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp hy; positivity
  refine (integral_norm_edgeKill_le k L).trans ?_
  rw [← hl, hsplit, hG]
  calc unitL1 ^ (k + 1) * (unitL1 ^ l.length * ((l.map fun r => ‖x₀ - r‖).prod * (l.map q).prod))
      ≤ W ^ (k + 1) * (W ^ l.length * ((l.map fun r => ‖x₀ - r‖).prod * (l.map q).prod)) := by
        gcongr
    _ = _ := by ring


/-! ### The edge energy and its stability -/

theorem exp_div_four_le_sinh_of_ge_half {y : ℝ} (hy : 1 / 2 ≤ y) : Real.exp y / 4 ≤ Real.sinh y := by
  rw [Real.sinh_eq]
  have h1 : 2 ≤ Real.exp (2 * y) := by
    have := Real.add_one_le_exp (2 * y); linarith
  have h2 : Real.exp (2 * y) = Real.exp y * Real.exp y := by rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  have hy0 := Real.exp_pos y
  nlinarith

/-- The edge energy `P = ∫ s(u) sinh(δu) ≥ b² e^{2δ(b-2)}/16` once `b ≥ 4` and `δ(b - 2) ≥ ½`. -/
theorem sinhTest_energy_ge_exp {b δ : ℝ} (hb : 4 ≤ b) (hδ : 0 < δ) (hδb : 1 / 2 ≤ δ * (b - 2)) :
    b ^ 2 * Real.exp (2 * (δ * (b - 2))) / 16 ≤ ∫ u, sinhTest b δ u * Real.sinh (δ * u) := by
  have h := sinhTest_energy_ge (a := b) (δ := δ) (w := 1) hδ one_pos (by linarith)
  have hb1 : 1 ≤ b := by linarith
  have hr : b ^ 2 ≤ (1 * b) ^ (5 / 2 : ℝ) := by
    rw [one_mul, show b ^ 2 = b ^ (2 : ℝ) by norm_cast]
    exact Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num)
  have hs := exp_div_four_le_sinh_of_ge_half hδb
  have hs0 : 0 ≤ Real.exp (δ * (b - 2)) / 4 := by positivity
  have hsq : (Real.exp (δ * (b - 2)) / 4) ^ 2 ≤ Real.sinh (δ * (b - 2 * 1)) ^ 2 := by
    rw [mul_one]; exact pow_le_pow_left₀ hs0 hs 2
  have he : (Real.exp (δ * (b - 2)) / 4) ^ 2 = Real.exp (2 * (δ * (b - 2))) / 16 := by
    rw [div_pow, ← Real.exp_nat_mul]; norm_num
  rw [he] at hsq
  calc b ^ 2 * Real.exp (2 * (δ * (b - 2))) / 16 = b ^ 2 * (Real.exp (2 * (δ * (b - 2))) / 16) := by
        ring
    _ ≤ (1 * b) ^ (5 / 2 : ℝ) * Real.sinh (δ * (b - 2 * 1)) ^ 2 :=
        mul_le_mul hr hsq (by positivity) (by positivity)
    _ = 1 * (1 * b) ^ (5 / 2 : ℝ) * Real.sinh (δ * (b - 2 * 1)) ^ 2 := by ring
    _ ≤ _ := h

theorem integral_abs_sinhTest_le {b δ : ℝ} (hb : 0 ≤ b) (hδ : 0 ≤ δ) :
    ∫ u, |sinhTest b δ u| ≤ 2 * b * (Real.cosh (δ * b) * b ^ 5) :=
  integral_le_of_bound_on_Icc hb (fun _ => abs_nonneg _) (fun u hu => abs_sinhTest_le hb hδ hu)
    (fun u hu => by rw [sinhTest_eq_zero hb hu, abs_zero])

theorem cosh_le_exp_self_of_nonneg {y : ℝ} (hy : 0 ≤ y) : Real.cosh y ≤ Real.exp y := by
  rw [Real.cosh_eq]
  have : Real.exp (-y) ≤ Real.exp y := Real.exp_le_exp.mpr (by linarith)
  linarith

/-- **Stability of the edge transform.**  At distance `ε ≤ 1/(10⁵ b⁵)` from `-iδ`, the transform
of the edge weight moves by at most `P/100`, `P = ŝ(-iδ)`. -/
theorem norm_paperFT_sinhTest_sub_le {b δ ε : ℝ} (hb : 4 ≤ b) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hδb : 1 / 2 ≤ δ * (b - 2)) (hε0 : 0 ≤ ε) (hε : ε * (10 ^ 5 * b ^ 5) ≤ 1) {z : ℂ}
    (hz : ‖z - -(I * (δ : ℂ))‖ ≤ ε) :
    ‖paperFT (fun u => (sinhTest b δ u : ℂ)) z -
        paperFT (fun u => (sinhTest b δ u : ℂ)) (-(I * δ))‖ ≤
      1 / 100 * ∫ u, sinhTest b δ u * Real.sinh (δ * u) := by
  have hb0 : 0 ≤ b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hb5 : 1 ≤ b ^ 5 := one_le_pow₀ hb1
  have hεb : b * ‖z - -(I * (δ : ℂ))‖ ≤ 1 := by
    have : b * ε ≤ 1 := by nlinarith [pow_le_pow_right₀ hb1 (show 1 ≤ 5 by norm_num)]
    nlinarith [norm_nonneg (z - -(I * (δ : ℂ)))]
  have hlip := norm_paperFT_sub_le (sinhTest_contDiff b δ).continuous (sinhTest_supp hb0) hεb
  have him : |(-(I * (δ : ℂ))).im| = δ := by simp [abs_of_pos hδ]
  rw [him] at hlip
  have hL1 := integral_abs_sinhTest_le hb0 hδ.le
  have hcosh := cosh_le_exp_self_of_nonneg (show 0 ≤ δ * b by positivity)
  have hP := sinhTest_energy_ge_exp hb hδ hδb
  have he2 : Real.exp (2 * (δ * (b - 2))) * Real.exp (4 * δ) = Real.exp (δ * b) * Real.exp (δ * b) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have he4 : Real.exp (4 * δ) ≤ 8 := by
    have h1 : Real.exp (4 * δ) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by linarith)
    have h2 := Real.exp_one_lt_d9
    have h3 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    nlinarith [Real.exp_pos 1]
  set P := ∫ u, sinhTest b δ u * Real.sinh (δ * u)
  set E := Real.exp (δ * b)
  have hE0 : 0 < E := Real.exp_pos _
  -- ‖Δ‖ ≤ 4 b⁷ ε E²
  have hΔ : ‖paperFT (fun u => (sinhTest b δ u : ℂ)) z -
      paperFT (fun u => (sinhTest b δ u : ℂ)) (-(I * δ))‖ ≤ 4 * b ^ 7 * ε * (E * E) := by
    refine hlip.trans ?_
    calc 2 * b * ‖z - -(I * (δ : ℂ))‖ * E * ∫ u, |sinhTest b δ u|
        ≤ 2 * b * ε * E * (2 * b * (Real.cosh (δ * b) * b ^ 5)) := by
          gcongr
      _ ≤ 2 * b * ε * E * (2 * b * (E * b ^ 5)) := by gcongr
      _ = 4 * b ^ 7 * ε * (E * E) := by ring
  -- P ≥ b² E²/128
  have hPlow : b ^ 2 * (E * E) / 128 ≤ P := by
    have hx : b ^ 2 * (E * E) = b ^ 2 * Real.exp (2 * (δ * (b - 2))) * Real.exp (4 * δ) := by
      rw [mul_assoc, he2]
    have : b ^ 2 * (E * E) ≤ b ^ 2 * Real.exp (2 * (δ * (b - 2))) * 8 := by
      rw [hx]; gcongr
    linarith
  have hkey : 4 * b ^ 7 * ε * (E * E) ≤ 1 / 100 * (b ^ 2 * (E * E) / 128) := by
    have hEE : 0 < E * E := by positivity
    have hb2 : 0 < b ^ 2 := by positivity
    have : 4 * b ^ 7 * ε ≤ 1 / 100 * (b ^ 2 / 128) := by
      have h7 : b ^ 7 = b ^ 2 * b ^ 5 := by ring
      rw [h7]
      nlinarith
    nlinarith
  linarith

/-- **Cluster estimate for the edge profile.**  If `G` moves by at most `|G(x₀)|/10`, `ŝ` by at most
`|ŝ(x₀)|/100`, and `Ψ(x₀)` is purely imaginary, then `Re Ψ(z)² ≤ 0`. -/
theorem re_sq_edgeProfile_nonpos {b δ : ℝ} {k : ℕ} {L : List ℂ} {z x₀ : ℂ}
    (hG : ‖lowHeightProfile (sinhTestWeight 1) k L z - lowHeightProfile (sinhTestWeight 1) k L x₀‖ ≤
      1 / 10 * ‖lowHeightProfile (sinhTestWeight 1) k L x₀‖)
    (hs : ‖paperFT (fun u => (sinhTest b δ u : ℂ)) z - paperFT (fun u => (sinhTest b δ u : ℂ)) x₀‖ ≤
      1 / 100 * ‖paperFT (fun u => (sinhTest b δ u : ℂ)) x₀‖)
    (h0 : edgeProfile b δ k L x₀ ^ 2 = -((‖edgeProfile b δ k L x₀‖ ^ 2 : ℝ) : ℂ)) :
    (edgeProfile b δ k L z ^ 2).re ≤ 0 := by
  set s₀ := paperFT (fun u => (sinhTest b δ u : ℂ)) x₀
  set s₁ := paperFT (fun u => (sinhTest b δ u : ℂ)) z
  set G₀ := lowHeightProfile (sinhTestWeight 1) k L x₀
  set G₁ := lowHeightProfile (sinhTestWeight 1) k L z
  have hs1 : ‖s₁‖ ≤ 101 / 100 * ‖s₀‖ := by
    have := norm_le_norm_add_norm_sub' s₁ s₀
    have h2 : ‖s₁‖ ≤ ‖s₀‖ + ‖s₁ - s₀‖ := by
      calc ‖s₁‖ = ‖s₀ + (s₁ - s₀)‖ := by ring_nf
        _ ≤ ‖s₀‖ + ‖s₁ - s₀‖ := norm_add_le _ _
    linarith
  have hnorm0 : ‖edgeProfile b δ k L x₀‖ = ‖s₀‖ * ‖G₀‖ := by
    simp only [edgeProfile, norm_mul, Complex.norm_I, one_mul, s₀, G₀]
  have hdiff : edgeProfile b δ k L z - edgeProfile b δ k L x₀ =
      I * (s₁ * (G₁ - G₀) + (s₁ - s₀) * G₀) := by
    simp only [edgeProfile, s₀, s₁, G₀, G₁]; ring
  have hnear : ‖edgeProfile b δ k L z - edgeProfile b δ k L x₀‖ ≤
      111 / 1000 * ‖edgeProfile b δ k L x₀‖ := by
    rw [hdiff, norm_mul, Complex.norm_I, one_mul, hnorm0]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have hG0 := norm_nonneg G₀
    have hs0 := norm_nonneg s₀
    calc ‖s₁‖ * ‖G₁ - G₀‖ + ‖s₁ - s₀‖ * ‖G₀‖
        ≤ (101 / 100 * ‖s₀‖) * (1 / 10 * ‖G₀‖) + (1 / 100 * ‖s₀‖) * ‖G₀‖ := by
          gcongr
      _ = 111 / 1000 * (‖s₀‖ * ‖G₀‖) := by ring
  have := re_sq_le_of_near (by norm_num : (0 : ℝ) ≤ 111 / 1000) h0 hnear
  have hsq := sq_nonneg ‖edgeProfile b δ k L x₀‖
  nlinarith

/-- **Tail bound for the edge profile.**  In the strip,
`|Ψ(x)|² (1 + |Re x|)^{3+E} ≤ e^{2|Im x| b} (4‖s‖_{C²})² C_G` whenever
`|G(x)|² (1 + |Re x|)^{3+E} ≤ C_G`. -/
theorem norm_sq_edgeProfile_tail_le {b δ : ℝ} (hb : 0 ≤ b) {k : ℕ} {L : List ℂ} {x : ℂ} {E : ℕ}
    {CG : ℝ}
    (hG : ‖lowHeightProfile (sinhTestWeight 1) k L x‖ ^ 2 * (1 + |x.re|) ^ (3 + E) ≤ CG) :
    ‖edgeProfile b δ k L x‖ ^ 2 * (1 + |x.re|) ^ (3 + E) ≤
      Real.exp (2 * |x.im| * b) * (4 * testNorm (sinhTest b δ)) ^ 2 * CG := by
  have hsc : ContDiff ℝ 2 (fun u => (sinhTest b δ u : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (sinhTest_contDiff b δ)
  have hss : ∀ u, (sinhTest b δ u : ℂ) ≠ 0 → |u| ≤ b := fun u hu =>
    sinhTest_supp (δ := δ) hb u (fun h => hu (by simp [h]))
  have hdec := norm_paperFT_le_decay hsc hss x
  have hD1 : 1 ≤ (1 + |x.re|) ^ 2 := one_le_pow₀ (by linarith [abs_nonneg x.re])
  have hT : (∫ u, ‖(sinhTest b δ u : ℂ)‖) + ∫ u, ‖deriv (deriv (fun u => (sinhTest b δ u : ℂ))) u‖ =
      testNorm (sinhTest b δ) := rfl
  rw [hT] at hdec
  have hs : ‖paperFT (fun u => (sinhTest b δ u : ℂ)) x‖ ≤
      Real.exp (|x.im| * b) * (4 * testNorm (sinhTest b δ)) := by
    refine hdec.trans ?_
    have h0 : 0 ≤ Real.exp (|x.im| * b) * (4 * testNorm (sinhTest b δ)) := by
      have := testNorm_nonneg (sinhTest b δ); positivity
    exact div_le_self h0 hD1
  have hs2 := pow_le_pow_left₀ (norm_nonneg _) hs 2
  have hnorm : ‖edgeProfile b δ k L x‖ ^ 2 =
      ‖paperFT (fun u => (sinhTest b δ u : ℂ)) x‖ ^ 2 *
        ‖lowHeightProfile (sinhTestWeight 1) k L x‖ ^ 2 := by
    simp only [edgeProfile, norm_mul, Complex.norm_I, one_mul]; ring
  have he : (Real.exp (|x.im| * b) * (4 * testNorm (sinhTest b δ))) ^ 2 =
      Real.exp (2 * |x.im| * b) * (4 * testNorm (sinhTest b δ)) ^ 2 := by
    rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
  rw [hnorm, mul_assoc]
  rw [he] at hs2
  have hGn : 0 ≤ ‖lowHeightProfile (sinhTestWeight 1) k L x‖ ^ 2 * (1 + |x.re|) ^ (3 + E) := by
    positivity
  calc ‖paperFT (fun u => (sinhTest b δ u : ℂ)) x‖ ^ 2 *
        (‖lowHeightProfile (sinhTestWeight 1) k L x‖ ^ 2 * (1 + |x.re|) ^ (3 + E))
      ≤ Real.exp (2 * |x.im| * b) * (4 * testNorm (sinhTest b δ)) ^ 2 * CG :=
        mul_le_mul hs2 hG hGn (by positivity)

end RHTower
