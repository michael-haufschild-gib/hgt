import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheWindowIndex
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.UnboundedOverlapIsTheRiemannHypothesis
import GaloisForLFunctions.HTGeometry.InertiaScalingSwap
import GaloisForLFunctions.HeckeKreinToeplitz.KernelsOnGroupsAndTheirNegativeIndex

/-!
# The window index counts the right zeros

On a finite family of horizon windows `h_i` the second-order term of the degeneration at the
multiple `K` of the critical curve is the pencil Gram matrix `P_K` (`TheWindowIndex`). This file
splits the pencil and computes its negative index `ind₋(P_K)`, the window index, as a function of
the multiple and of the family.

* **Splitting** (`pencilGram_eq`): `P_K = κ_φ W(H) + (βJ/K) A(H)`, where `W(H)` is Weil's Gram matrix
  of the synthesized tests `H_i = e^{y/2} h_i` and `A(H)_{ij} = ∫ e^{−(β+1)y} H_i H_j` is the
  aliasing Gram matrix, positive semidefinite (`hermQuad_aliasGram_nonneg`).
* **Monotonicity** (`hermNegIndex_pencilGram_mono`): for `βJ ≥ 0` the window index is a
  nondecreasing function of the multiple.
* **Stabilization** (`eventually_hermNegIndex_pencilGram_eq`): for all large multiples the window
  index equals the negative index of Weil's Gram matrix of the synthesized tests (upper bound by
  comparison of forms, lower bound by lower semicontinuity of the index).
* **Exhaustion** (`windowIndex_law`): some family of windows has window index `≥ n` at some multiple
  iff `ζ` has at least `n` distinct zeros right of the critical line. The families are translates
  of the cubic spline moved into a window (AOG `zeta_splineOrbit_negIndex_law` and translation
  invariance of Weil's Gram matrices).
* **RH** (`riemannHypothesis_iff_windowIndex_eq_zero`): RH iff the window index vanishes for every
  family of windows at every multiple.

The window index is the counting function of the right zeros read through the degeneration: the
aliasing norm pays the negative directions of Weil's form up to the multiple, and past the last
critical multiple of a family the index is Weil's index on its span.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23 Matrix
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticCastelnuovoSeveri HTGeometry
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline contDiff_cubicSpline
  cubicSpline_eq_zero)

variable {φ : ℝ → ℝ} {A : ℝ} {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "Λw" => (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ))

/-- Weil's part of the pencil: `κ_φ` times Weil's Gram matrix of the synthesized tests. -/
def weilWindowGram (φ : ℝ → ℝ) (h : ι → ℝ → ℝ) : Matrix ι ι ℂ :=
  (((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) : ℝ) : ℂ) • weilGram Λw fun i => cx (halfWeight (h i))

/-- The aliasing Gram matrix `A(H)_{ij} = ∫ e^{−(β+1)y} H_i H_j`. -/
def aliasGram (β : ℝ) (h : ι → ℝ → ℝ) : Matrix ι ι ℂ :=
  fun i j => ((∫ y, Real.exp (-((β + 1) * y)) * (halfWeight (h i) y * halfWeight (h j) y) : ℝ) : ℂ)

/-! ### Window calculus -/

theorem halfWeight_add (a b : ℝ → ℝ) :
    halfWeight (fun y => a y + b y) = fun y => halfWeight a y + halfWeight b y := by
  funext y; simp only [halfWeight]; ring

theorem halfWeight_sub (a b : ℝ → ℝ) :
    halfWeight (fun y => a y - b y) = fun y => halfWeight a y - halfWeight b y := by
  funext y; simp only [halfWeight]; ring

theorem halfWeight_eq_zero_of_window {h : ℝ → ℝ} (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) :
    ∀ y, y ∉ Set.Icc (-A) 0 → halfWeight h y = 0 := fun y hy => by
  simp [halfWeight, hsupp y hy]

theorem integrable_mul_of_window {w F : ℝ → ℝ} (hw : Continuous w) (hF : Continuous F)
    (hFs : ∀ y, y ∉ Set.Icc (-A) 0 → F y = 0) : Integrable (fun y => w y * F y) :=
  (hw.mul hF).integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (-A) 0)) fun y hy => by
      simp [hFs y hy])

/-- Polarization of a weighted norm on window functions. -/
theorem integral_polarize_of_window {w a b : ℝ → ℝ} (hw : Continuous w) (ha : Continuous a)
    (hb : Continuous b) (has : ∀ y, y ∉ Set.Icc (-A) 0 → a y = 0)
    (hbs : ∀ y, y ∉ Set.Icc (-A) 0 → b y = 0) :
    ((∫ y, w y * (a y + b y) ^ 2) - ∫ y, w y * (a y - b y) ^ 2) / 4 =
      ∫ y, w y * (a y * b y) := by
  rw [← integral_sub (integrable_mul_of_window (A := A) (F := fun y => (a y + b y) ^ 2) hw
      ((ha.add hb).pow 2) fun y hy => by simp [has y hy, hbs y hy])
    (integrable_mul_of_window (A := A) (F := fun y => (a y - b y) ^ 2) hw ((ha.sub hb).pow 2)
      fun y hy => by simp [has y hy, hbs y hy]), ← integral_div]
  congr 1
  funext y
  ring

omit [DecidableEq ι] in
/-- A Gram matrix of a nonnegative weight on window functions is positive semidefinite. -/
theorem hermQuad_weightGram_nonneg {w : ℝ → ℝ} (hw : Continuous w) (hw0 : ∀ y, 0 ≤ w y)
    {H : ι → ℝ → ℝ} (hH : ∀ i, Continuous (H i)) (hHs : ∀ i y, y ∉ Set.Icc (-A) 0 → H i y = 0)
    (x : ι → ℂ) :
    0 ≤ hermQuad (fun i j => ((∫ y, w y * (H i y * H j y) : ℝ) : ℂ)) x := by
  have hint : ∀ i j, Integrable (fun y => ((w y * (H i y * H j y) : ℝ) : ℂ)) := fun i j =>
    (integrable_mul_of_window (A := A) (F := fun y => H i y * H j y) hw ((hH i).mul (hH j))
      fun y hy => by simp [hHs i y hy]).ofReal
  have hpt : ∀ y, ∑ i, star (x i) * ∑ j, ((w y * (H i y * H j y) : ℝ) : ℂ) * x j =
      ((w y * Complex.normSq (∑ j, x j * (H j y : ℂ)) : ℝ) : ℂ) := fun y => by
    rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
    simp only [map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.star_def]
    push_cast
    ring
  have hswap : ∫ y, ∑ i, star (x i) * ∑ j, ((w y * (H i y * H j y) : ℝ) : ℂ) * x j =
      ∑ i, star (x i) * ∑ j, (∫ y, ((w y * (H i y * H j y) : ℝ) : ℂ)) * x j := by
    rw [integral_finsetSum _ fun i _ =>
      (integrable_finsetSum _ fun j _ => (hint i j).mul_const _).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_finsetSum _ fun j _ => (hint i j).mul_const _]
    congr 1
    exact Finset.sum_congr rfl fun j _ => integral_mul_const _ _
  have key : star x ⬝ᵥ ((fun i j => ((∫ y, w y * (H i y * H j y) : ℝ) : ℂ) : Matrix ι ι ℂ) *ᵥ x) =
      ((∫ y, w y * Complex.normSq (∑ j, x j * (H j y : ℂ)) : ℝ) : ℂ) := by
    have e : ∀ i j, ((∫ y, w y * (H i y * H j y) : ℝ) : ℂ) =
        ∫ y, ((w y * (H i y * H j y) : ℝ) : ℂ) := fun i j => integral_complex_ofReal.symm
    simp only [dotProduct, mulVec, Pi.star_apply, e]
    rw [← hswap, ← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall hpt)
  unfold hermQuad
  rw [key, Complex.ofReal_re]
  exact integral_nonneg fun y => mul_nonneg (hw0 y) (Complex.normSq_nonneg _)

omit [DecidableEq ι] in
theorem hermQuad_aliasGram_nonneg (β : ℝ) {h : ι → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) (x : ι → ℂ) :
    0 ≤ hermQuad (aliasGram β h) x :=
  hermQuad_weightGram_nonneg (w := fun y => Real.exp (-((β + 1) * y))) (by fun_prop)
    (fun y => (Real.exp_pos _).le) (H := fun i => halfWeight (h i))
    (fun i => (contDiff_halfWeight (hh i)).continuous)
    (fun i => halfWeight_eq_zero_of_window (hsupp i)) x

/-! ### Splitting the pencil -/

omit [Fintype ι] [DecidableEq ι] in
/-- **Splitting**: `P_K = κ_φ W(H) + (βJ/K) A(H)`. -/
theorem pencilGram_eq {h : ι → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) (β J K : ℝ) :
    pencilGram φ β J K h = weilWindowGram φ h + ((β * J / K : ℝ) : ℂ) • aliasGram β h := by
  ext i j
  have hH : ∀ i, ContDiff ℝ 2 (halfWeight (h i)) := fun i => contDiff_halfWeight (hh i)
  have hHc : ∀ i, HasCompactSupport (halfWeight (h i)) := fun i =>
    hasCompactSupport_halfWeight (hasCompactSupport_of_window (hsupp i))
  have hpol := integral_polarize_of_window (w := fun y => Real.exp (-((β + 1) * y)))
    (by fun_prop) (hH i).continuous (hH j).continuous (halfWeight_eq_zero_of_window (hsupp i))
    (halfWeight_eq_zero_of_window (hsupp j))
  beta_reduce at hpol
  simp only [pencilGram, secondOrderLimit, weilWindowGram, aliasGram, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, weilGram]
  rw [EffectiveArithmeticHodgeTheory.weilPair_real_eq (hH i) (hHc i) (hH j) (hHc j)]
  simp only [halfWeight_add, halfWeight_sub]
  rw [← hpol]
  push_cast
  ring

omit [DecidableEq ι] in
theorem hermQuad_pencilGram {h : ι → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) (β J K : ℝ) (x : ι → ℂ) :
    hermQuad (pencilGram φ β J K h) x =
      hermQuad (weilWindowGram φ h) x + β * J / K * hermQuad (aliasGram β h) x := by
  rw [pencilGram_eq hh hsupp, HTGeometry.hermQuad_add, HTGeometry.hermQuad_smul]

omit [Fintype ι] [DecidableEq ι] in
theorem weilWindowGram_isHermitian (φ : ℝ → ℝ) (h : ι → ℝ → ℝ) :
    (weilWindowGram φ h).IsHermitian := by
  unfold weilWindowGram
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, (weilGram_isHermitian _ _).eq,
    Complex.star_def, Complex.conj_ofReal]

omit [DecidableEq ι] in
theorem hermNegIndex_weilWindowGram (hφ0 : ∫ u, φ u ≠ 0) (hφ2 : 0 < ∫ u, φ u ^ 2)
    (h : ι → ℝ → ℝ) :
    hermNegIndex (weilWindowGram φ h) = hermNegIndex (weilGram Λw fun i => cx (halfWeight (h i))) :=
  hermNegIndex_ofReal_smul (div_pos (by positivity) hφ2) _

/-! ### The window index as a function of the multiple -/

omit [DecidableEq ι] in
/-- **Monotonicity**: for `βJ ≥ 0` the window index is nondecreasing in the multiple. -/
theorem hermNegIndex_pencilGram_mono {h : ι → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) {β J : ℝ} (hβJ : 0 ≤ β * J) {K K' : ℝ}
    (hK : 0 < K) (hKK : K ≤ K') :
    hermNegIndex (pencilGram φ β J K h) ≤ hermNegIndex (pencilGram φ β J K' h) :=
  HeckeKreinToeplitz.hermNegIndex_le_of_hermQuad_le _ _ fun x => by
    rw [hermQuad_pencilGram hh hsupp, hermQuad_pencilGram hh hsupp]
    have hq := hermQuad_aliasGram_nonneg β hh hsupp x
    have := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hβJ hK hKK) hq
    linarith

omit [DecidableEq ι] in
/-- The window index never exceeds Weil's part. -/
theorem hermNegIndex_pencilGram_le_weil {h : ι → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) {β J : ℝ} (hβJ : 0 ≤ β * J) {K : ℝ}
    (hK : 0 < K) :
    hermNegIndex (pencilGram φ β J K h) ≤ hermNegIndex (weilWindowGram φ h) :=
  HeckeKreinToeplitz.hermNegIndex_le_of_hermQuad_le _ _ fun x => by
    rw [hermQuad_pencilGram hh hsupp]
    have := mul_nonneg (div_nonneg hβJ hK.le) (hermQuad_aliasGram_nonneg β hh hsupp x)
    linarith

/-- **Stabilization**: for all large multiples the window index is the negative index of Weil's
Gram matrix of the synthesized tests. -/
theorem eventually_hermNegIndex_pencilGram_eq (hφ0 : ∫ u, φ u ≠ 0) (hφ2 : 0 < ∫ u, φ u ^ 2)
    {h : ι → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) {β J : ℝ} (hβJ : 0 ≤ β * J) :
    ∀ᶠ K in atTop, hermNegIndex (pencilGram φ β J K h) =
      hermNegIndex (weilGram Λw fun i => cx (halfWeight (h i))) := by
  have hlim : ∀ a b, Tendsto (fun K : ℝ => pencilGram φ β J K h a b) atTop
      (𝓝 (weilWindowGram φ h a b)) := fun a b => by
    have h0 : Tendsto (fun K : ℝ => ((β * J / K : ℝ) : ℂ)) atTop (𝓝 0) := by
      have : Tendsto (fun K : ℝ => β * J / K) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have h' := (Complex.continuous_ofReal.tendsto 0).comp this
      rw [Complex.ofReal_zero] at h'
      exact h'
    have := (tendsto_const_nhds (x := weilWindowGram φ h a b)).add
      (h0.mul_const (aliasGram β h a b))
    rw [zero_mul, add_zero] at this
    refine this.congr fun K => ?_
    rw [pencilGram_eq hh hsupp]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have hev := HeckeKreinToeplitz.eventually_le_hermNegIndex (weilWindowGram_isHermitian φ h) hlim
  filter_upwards [hev, eventually_gt_atTop 0] with K hK hK0
  rw [← hermNegIndex_weilWindowGram hφ0 hφ2]
  exact le_antisymm (hermNegIndex_pencilGram_le_weil hh hsupp hβJ hK0) hK

omit [DecidableEq ι] in
/-- The window index is bounded by the number of right zeros at every multiple, for every family. -/
theorem hermNegIndex_pencilGram_le_rightZeros (hφ0 : ∫ u, φ u ≠ 0) (hφ2 : 0 < ∫ u, φ u ^ 2)
    {h : ι → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) {β J : ℝ} (hβJ : 0 ≤ β * J) {K : ℝ}
    (hK : 0 < K) :
    (hermNegIndex (pencilGram φ β J K h) : ℕ∞) ≤
      {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}.encard := by
  have h1 := hermNegIndex_pencilGram_le_weil (φ := φ) hh hsupp hβJ hK
  rw [hermNegIndex_weilWindowGram hφ0 hφ2] at h1
  exact (ENat.coe_le_coe.mpr h1).trans (negIndex_weilGram_le_offLineCount _
    (fun i => cx_contDiff (contDiff_halfWeight (hh i)))
    fun i => cx_hasCompactSupport (hasCompactSupport_halfWeight (hasCompactSupport_of_window (hsupp i))))

/-! ### Exhaustion -/

/-- **Exhaustion**: if `ζ` has at least `n` right zeros, translates of the cubic spline moved into
one window form a family whose window index is `≥ n` at every large multiple. -/
theorem exists_window_family_le_hermNegIndex (hφ0 : ∫ u, φ u ≠ 0) (hφ2 : 0 < ∫ u, φ u ^ 2)
    {β J : ℝ} (hβJ : 0 ≤ β * J) {n : ℕ}
    (hn : (n : ℕ∞) ≤ {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}.encard) :
    ∃ (A : ℝ) (S : Finset ℝ) (h : S → ℝ → ℝ), (∀ i, ContDiff ℝ 2 (h i)) ∧
      (∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) ∧
        ∀ᶠ K in atTop, n ≤ hermNegIndex (pencilGram φ β J K h) := by
  obtain ⟨S, -, hS⟩ := (ArithmeticOrientationGeometry.zeta_splineOrbit_negIndex_law
    (D := Set.univ) (fun v _ ε hε => ⟨v, Set.mem_univ _, by rw [sub_self, abs_zero]; exact hε⟩)
    n).mpr hn
  obtain ⟨T, hTdef⟩ : ∃ T, T = ∑ s ∈ S, |s| := ⟨_, rfl⟩
  have hT : ∀ s ∈ S, |s| ≤ T := fun s hs => hTdef ▸ Finset.single_le_sum (fun i _ => abs_nonneg i) hs
  obtain ⟨h, hdef⟩ : ∃ h : S → ℝ → ℝ,
      h = fun (s : S) y => Real.exp (-(y / 2)) * cubicSpline (y - ((s : ℝ) + -(T + 4))) :=
    ⟨_, rfl⟩
  have hh : ∀ i, ContDiff ℝ 2 (h i) := fun i => by
    rw [hdef]
    exact (Real.contDiff_exp.comp (contDiff_id.div_const 2).neg).mul
      (contDiff_cubicSpline.comp (contDiff_id.sub contDiff_const))
  have hsupp : ∀ i y, y ∉ Set.Icc (-(2 * T + 8)) 0 → h i y = 0 := fun i y hy => by
    have hs := abs_le.mp (hT i i.2)
    rw [hdef]
    simp only
    rw [cubicSpline_eq_zero, mul_zero]
    simp only [Set.mem_Icc, not_and_or, not_le] at hy
    rw [lt_abs]
    rcases hy with hy | hy
    · right; linarith
    · left; linarith
  have hW : weilGram Λw (fun s : S => cx (halfWeight (h s))) =
      weilGram Λw (fun s : S => ArithmeticCastelnuovoSeveri.translate (s : ℝ) (cx cubicSpline)) := by
    rw [← weilGram_translate_add Λw (cx cubicSpline) S (-(T + 4))]
    congr 1
    funext s u
    rw [hdef]
    simp only [cx, ArithmeticCastelnuovoSeveri.translate, halfWeight]
    congr 1
    rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  refine ⟨2 * T + 8, S, h, hh, hsupp, ?_⟩
  filter_upwards [eventually_hermNegIndex_pencilGram_eq hφ0 hφ2 hh hsupp hβJ] with K hK
  rw [hK, hW]
  exact hS

/-- **The window index law.** Some family of windows has window index `≥ n` at some multiple iff
`ζ` has at least `n` distinct zeros right of the critical line. -/
theorem windowIndex_law (hφ0 : ∫ u, φ u ≠ 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {β J : ℝ}
    (hβJ : 0 ≤ β * J) (n : ℕ) :
    (∃ (A : ℝ) (S : Finset ℝ) (h : S → ℝ → ℝ), (∀ i, ContDiff ℝ 2 (h i)) ∧
      (∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) ∧
        ∃ K, 0 < K ∧ n ≤ hermNegIndex (pencilGram φ β J K h)) ↔
      (n : ℕ∞) ≤ {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}.encard := by
  constructor
  · rintro ⟨A, S, h, hh, hsupp, K, hK, hnK⟩
    exact (ENat.coe_le_coe.mpr hnK).trans
      (hermNegIndex_pencilGram_le_rightZeros hφ0 hφ2 hh hsupp hβJ hK)
  · intro hn
    obtain ⟨A, S, h, hh, hsupp, hev⟩ := exists_window_family_le_hermNegIndex hφ0 hφ2 hβJ hn
    obtain ⟨K, hK, hK0⟩ := (hev.and (eventually_gt_atTop 0)).exists
    exact ⟨A, S, h, hh, hsupp, K, hK0, hK⟩

/-- **RH is the vanishing of the window index** for every family of windows at every multiple. -/
theorem riemannHypothesis_iff_windowIndex_eq_zero (hφ0 : ∫ u, φ u ≠ 0)
    (hφ2 : 0 < ∫ u, φ u ^ 2) {β J : ℝ} (hβJ : 0 ≤ β * J) :
    RiemannHypothesis ↔ ∀ (A : ℝ) (S : Finset ℝ) (h : S → ℝ → ℝ), (∀ i, ContDiff ℝ 2 (h i)) →
      (∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) → ∀ K, 0 < K →
        hermNegIndex (pencilGram φ β J K h) = 0 := by
  rw [ArithmeticOrientationGeometry.riemannHypothesis_iff_no_rightZero]
  constructor
  · intro hRH A S h hh hsupp K hK
    have := hermNegIndex_pencilGram_le_rightZeros hφ0 hφ2 hh hsupp hβJ hK
    rw [hRH, Set.encard_empty] at this
    exact_mod_cast nonpos_iff_eq_zero.mp this
  · intro hall
    by_contra hne
    have h1 : ((1 : ℕ) : ℕ∞) ≤ {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}.encard := by
      rw [Nat.cast_one, Set.one_le_encard_iff_nonempty]
      exact Set.nonempty_iff_ne_empty.mpr hne
    obtain ⟨A, S, h, hh, hsupp, K, hK, hK1⟩ := (windowIndex_law hφ0 hφ2 hβJ 1).mpr h1
    rw [hall A S h hh hsupp K hK] at hK1
    exact absurd hK1 (by norm_num)

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
