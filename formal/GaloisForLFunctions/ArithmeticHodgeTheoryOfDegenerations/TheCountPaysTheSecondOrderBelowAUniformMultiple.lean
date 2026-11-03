import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheShortWindowsInheritThePolarization
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SourceDeterminantalSectionsAndArithmeticRiemannRoch

/-!
# The count pays the second order below a uniform multiple

At the critical curve the second-order Gram matrix of a family of horizon windows of length `A` is
the pencil `P_K = κ W(H) + (βJ/K) A(H)`: Weil's Gram matrix of the synthesized tests
`H_i = e^{y/2} h_i` and the aliasing Gram matrix `A(H)_{ij} = ∫ e^{−(β+1)y} H_i H_j`, the count of the
first order through the monodromy. ACS proves an unconditional floor for Weil's form at every
aperture, `Q(F) ≥ −(10 + 72 e^r) ‖F‖²` for tests supported in `[−r, r]`
(`realTestsAt_scalingSubsurface_defect_ge_neg_ten_add_seventy_two_exp`). On windows
(`y ≤ 0`) the aliasing weight is `≥ 1`, so `A(H) ⪰` the `L²` Gram matrix. Hence:

* **Weil's floor on windows** (`weilQuad_window_ge`): `Q(F) ≥ −C(A) ‖F‖²`,
  `C(A) = 10 + 72 e^{A/2}`, for every window test of length `A`.
* **The count pays the second order below a uniform multiple**
  (`pencilGram_posDef_below_uniformMultiple`): if `κ C(A) K < βJ`, the pencil is positive definite
  on every linearly independent family of windows of length `A`; the window index vanishes there
  (`hermNegIndex_pencilGram_eq_zero_below_uniformMultiple`).
* **Mechanism B at every window length** (`below_uniformMultiple_inherit`): along
  `c^{β+1}/log N → K` with `κ C(A) K < βJ`, the Gram matrix of the complete family on the family is
  eventually positive definite; with windows twisted by Ramanujan expansions added, on the mixed
  family as well (`mixed_below_uniformMultiple_inherit`, from `mixed_inherit_of_pencil_pos`).

So every critical multiple `K*(H)` of a window of length `A` is at least `K₀(A) = βJ/(κ C(A))`:
below `K₀(A)` the count of the first order carries the whole second order, unconditionally, on
windows of every length; RH is the statement that the multiple can be taken to infinity.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23 Matrix
open scoped ComplexConjugate ComplexOrder

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri HTGeometry
  RenormalizedArithmeticPotentialTheory.CompletedShell

variable {φ : ℝ → ℝ} {A : ℝ} {κ : Type*} [Fintype κ] [DecidableEq κ]

local notation "Λw" => (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ))

/-- **Weil's floor on windows**: a window test of length `A > 0` has
`Q(F) ≥ −(10 + 72 e^{A/2}) ∫ F²`. -/
theorem weilQuad_window_ge (hA : 0 < A) {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFv : ∀ y, y ∉ Set.Icc (-A) 0 → F y = 0) :
    -(10 + 72 * Real.exp (A / 2)) * ∫ u, F u ^ 2 ≤ weilQuad F := by
  set G : ℝ → ℝ := fun u => F (u - A / 2) with hGdef
  have hG2 : ContDiff ℝ 2 G := hF.comp (contDiff_id.sub contDiff_const)
  have hGv : ∀ u, A / 2 < |u| → G u = 0 := fun u hu => by
    refine hFv _ fun hm => ?_
    rcases le_abs'.mp hu.le with h | h <;> [skip; skip] <;>
      · rcases lt_abs.mp hu with h' | h' <;> linarith [hm.1, hm.2]
  have hGc : HasCompactSupport G :=
    HasCompactSupport.intro (isCompact_Icc (a := -(A / 2)) (b := A / 2)) fun u hu => by
      refine hGv u ?_
      by_contra hle
      push Not at hle
      exact hu (abs_le.mp hle)
  have hGt : tsupport G ⊆ Set.Icc (-(A / 2)) (A / 2) :=
    tsupport_subset_Icc_of_vanish_outside hGv
  let x : ℝ × ℝ × realTestsAt (A / 2) := (0, 0, ⟨⟨G, hG2, hGc⟩, hGt⟩)
  have h := realTestsAt_scalingSubsurface_defect_ge_neg_ten_add_seventy_two_exp (half_pos hA) x
  rw [scalingSubsurface_defect_self] at h
  have hQ : weilPair G G = weilQuad F := by
    show weilQuad G = weilQuad F
    exact weilQuad_comp_sub F (A / 2)
  have hL : ∫ u, G u ^ 2 = ∫ u, F u ^ 2 := integral_sub_right_eq_self (fun u => F u ^ 2) (A / 2)
  have h' : -(10 + 72 * Real.exp (A / 2)) * ∫ u, G u ^ 2 ≤ weilPair G G := h
  rwa [hQ, hL] at h'

omit [DecidableEq κ] in
/-- On windows the aliasing Gram matrix dominates the `L²` Gram matrix:
`∫ |Σ x_j H_j|² ≤ hermQuad (A(H)) x`. -/
theorem integral_normSq_le_hermQuad_aliasGram {β : ℝ} (hβ : -1 ≤ β) {h : κ → ℝ → ℝ}
    (hh : ∀ i, ContDiff ℝ 2 (h i)) (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0)
    (x : κ → ℂ) :
    ∫ y, Complex.normSq (∑ j, x j * (halfWeight (h j) y : ℂ)) ≤ hermQuad (aliasGram β h) x := by
  have hH : ∀ i, Continuous (halfWeight (h i)) := fun i => (contDiff_halfWeight (hh i)).continuous
  have hHv : ∀ i y, y ∉ Set.Icc (-A) 0 → halfWeight (h i) y = 0 := fun i =>
    halfWeight_eq_zero_of_window (hsupp i)
  have hq := hermQuad_weightGram_eq (A := A) (w := fun y => Real.exp (-((β + 1) * y)))
    (by fun_prop) (H := fun i => halfWeight (h i)) hH hHv x
  unfold aliasGram
  rw [hq]
  have hcS : Continuous fun y => Complex.normSq (∑ j, x j * (halfWeight (h j) y : ℂ)) :=
    Complex.continuous_normSq.comp (continuous_finsetSum _ fun j _ =>
      continuous_const.mul (Complex.continuous_ofReal.comp (hH j)))
  have hvan : ∀ y, y ∉ Set.Icc (-A) 0 →
      Complex.normSq (∑ j, x j * (halfWeight (h j) y : ℂ)) = 0 := fun y hy => by
    simp [hHv _ y hy]
  have hi1 : Integrable fun y => Complex.normSq (∑ j, x j * (halfWeight (h j) y : ℂ)) :=
    hcS.integrable_of_hasCompactSupport (HasCompactSupport.intro isCompact_Icc hvan)
  have hi2 : Integrable fun y => Real.exp (-((β + 1) * y)) *
      Complex.normSq (∑ j, x j * (halfWeight (h j) y : ℂ)) :=
    (integrable_mul_of_window (A := A) (F := fun y =>
      Complex.normSq (∑ j, x j * (halfWeight (h j) y : ℂ))) (by fun_prop) hcS hvan)
  refine integral_mono hi1 hi2 fun y => ?_
  by_cases hy : y ∈ Set.Icc (-A) 0
  · have h1 : 1 ≤ Real.exp (-((β + 1) * y)) := by
      have hm : 0 ≤ (β + 1) * (-y) := mul_nonneg (by linarith) (by linarith [hy.2])
      exact Real.one_le_exp (by linarith)
    have h0 := Complex.normSq_nonneg (∑ j, x j * (halfWeight (h j) y : ℂ))
    nlinarith
  · simp [hvan y hy]

omit [DecidableEq κ] in
/-- The `L²` norm of a complex combination splits into its real and imaginary combinations. -/
theorem integral_normSq_eq_re_add_im {H : κ → ℝ → ℝ} (x : κ → ℂ) :
    (fun y => Complex.normSq (∑ j, x j * (H j y : ℂ))) =
      fun y => (∑ j, (x j).re * H j y) ^ 2 + (∑ j, (x j).im * H j y) ^ 2 := by
  funext y
  rw [Complex.normSq_apply]
  simp only [Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  ring_nf

omit [DecidableEq κ] in
/-- **Weil's Gram matrix above its floor**:
`hermQuad (κ W(H)) x ≥ −κ C(A) ∫ |Σ x_j H_j|²`. -/
theorem hermQuad_weilWindowGram_ge (hA : 0 < A) {h : κ → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) (x : κ → ℂ) :
    -((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) * (10 + 72 * Real.exp (A / 2)) *
        ∫ y, Complex.normSq (∑ j, x j * (halfWeight (h j) y : ℂ)) ≤
      hermQuad (weilWindowGram φ h) x := by
  have hH : ∀ i, ContDiff ℝ 2 (halfWeight (h i)) := fun i => contDiff_halfWeight (hh i)
  have hHc : ∀ i, HasCompactSupport (halfWeight (h i)) := fun i =>
    hasCompactSupport_halfWeight (hasCompactSupport_of_window (hsupp i))
  have hHv : ∀ i y, y ∉ Set.Icc (-A) 0 → halfWeight (h i) y = 0 := fun i =>
    halfWeight_eq_zero_of_window (hsupp i)
  have hfloor : ∀ y : κ → ℝ, -(10 + 72 * Real.exp (A / 2)) *
      ∫ u, (∑ i, y i * halfWeight (h i) u) ^ 2 ≤ weilQuad (fun u => ∑ i, y i * halfWeight (h i) u) :=
    fun y => weilQuad_window_ge hA (ContDiff.sum fun i _ => contDiff_const.mul (hH i))
      fun u hu => by simp [hHv _ u hu]
  have hreal : ∀ i j, ((weilGram Λw fun i => cx (halfWeight (h i))) i j).im = 0 := by
    intro i j
    simp only [weilGram]
    rw [EffectiveArithmeticHodgeTheory.weilPair_real_eq (hH i) (hHc i) (hH j) (hHc j),
      Complex.ofReal_im]
  have hint : ∀ y : κ → ℝ, Integrable fun u => (∑ i, y i * halfWeight (h i) u) ^ 2 := by
    intro y
    have hc : Continuous fun u => (∑ i, y i * halfWeight (h i) u) ^ 2 :=
      (continuous_finsetSum _ fun i _ => continuous_const.mul (hH i).continuous).pow 2
    exact hc.integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_Icc (a := -A) (b := 0)) fun u hu => by
        simp [hHv _ u hu])
  rw [integral_normSq_eq_re_add_im, integral_add (hint _) (hint _)]
  unfold weilWindowGram
  rw [HTGeometry.hermQuad_smul, hermQuad_eq_re_add_im hreal,
    hermQuad_weilGram_ofReal hH hHv (fun i => (x i).re),
    hermQuad_weilGram_ofReal hH hHv (fun i => (x i).im)]
  have hκ : 0 ≤ (∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 := by
    have : (0 : ℝ) ≤ ∫ u, φ u ^ 2 := integral_nonneg fun u => sq_nonneg (φ u)
    positivity
  have h1 := hfloor fun i => (x i).re
  have h2 := hfloor fun i => (x i).im
  nlinarith

omit [DecidableEq κ] in
/-- **The count pays the second order below a uniform multiple**: if `κ C(A) K < βJ`, the pencil
is positive definite on every linearly independent family of windows of length `A`. -/
theorem pencilGram_posDef_below_uniformMultiple (hA : 0 < A) {β J K : ℝ} (hβ : -1 ≤ β)
    (hK : 0 < K)
    (hsmall : (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * (10 + 72 * Real.exp (A / 2)) * K < β * J)
    {h : κ → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) (hlin : LinearIndependent ℝ h) :
    ∀ x : κ → ℂ, x ≠ 0 → 0 < hermQuad (pencilGram φ β J K h) x := by
  intro x hx
  rw [pencilGram_eq hh hsupp, HTGeometry.hermQuad_add, HTGeometry.hermQuad_smul]
  set C := (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * (10 + 72 * Real.exp (A / 2)) with hC
  have hκ : 0 ≤ (∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 := by
    have : (0 : ℝ) ≤ ∫ u, φ u ^ 2 := integral_nonneg fun u => sq_nonneg (φ u)
    positivity
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hW := hermQuad_weilWindowGram_ge (φ := φ) hA hh hsupp x
  have hL := integral_normSq_le_hermQuad_aliasGram hβ hh hsupp x
  have hB : 0 < hermQuad (aliasGram β h) x := by
    have h1 := (Matrix.posDef_iff_dotProduct_mulVec.mp (aliasGram_posDef β hh hsupp hlin)).2 hx
    simpa [hermQuad] using (Complex.lt_def.mp h1).1
  have hgap : C < β * J / K := by rw [lt_div_iff₀ hK]; exact hsmall
  have hW' : -C * ∫ y, Complex.normSq (∑ j, x j * (halfWeight (h j) y : ℂ)) ≤
      hermQuad (weilWindowGram φ h) x := by rw [hC]; linarith
  nlinarith

omit [DecidableEq κ] in
/-- **The window index vanishes below the uniform multiple.** -/
theorem hermNegIndex_pencilGram_eq_zero_below_uniformMultiple (hA : 0 < A) {β J K : ℝ}
    (hβ : -1 ≤ β) (hK : 0 < K)
    (hsmall : (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * (10 + 72 * Real.exp (A / 2)) * K < β * J)
    {h : κ → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) (hlin : LinearIndependent ℝ h) :
    hermNegIndex (pencilGram φ β J K h) = 0 := by
  obtain ⟨W, hWr, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex (-(pencilGram φ β J K h))
  have hpos := pencilGram_posDef_below_uniformMultiple (φ := φ) hA hβ hK hsmall hh hsupp hlin
  have hbot : W = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    by_contra hx0
    have h1 := hW x hx hx0
    have h2 := hpos x hx0
    rw [hermQuad_neg] at h1
    linarith
  unfold hermNegIndex
  rw [← hWr, hbot, finrank_bot]

/-- **Mechanism B at every window length.** For every profile with bulk limit
`s^β E₁(s) → J`, and every linearly independent family of horizon windows of length `A > 0`: along
`c^{β+1}/log N → K` with `κ (10 + 72 e^{A/2}) K < βJ`, the Gram matrix of the complete family on the
family is eventually positive definite. -/
theorem below_uniformMultiple_inherit (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ p : ℝ} (hp : 4 < p)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    {β J : ℝ} (hβ : 0 ≤ β)
    (hbulk : Tendsto (fun s => s ^ β * completedShellEnergy φ s) atTop (𝓝 J))
    {h : κ → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i)) (hA : 0 < A)
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) (hlin : LinearIndependent ℝ h)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hsmall : (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * (10 + 72 * Real.exp (A / 2)) * K < β * J)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K)) :
    ∀ᶠ N : ℕ in atTop, ∀ x : κ → ℂ, x ≠ 0 → 0 < hermQuad (horizonGram φ h (c N) N) x := by
  have hpos := pencilGram_posDef_below_uniformMultiple (φ := φ) hA (by linarith) hK hsmall hh
    hsupp hlin
  have hev := eventually_hermQuad_pos_of_tendsto
    (pencilGram_isHermitian hφ hφsupp hφ2 hp hCφ hdecay hβ hbulk hh hA.le hsupp hc1 hK hcrit) hpos
    (tendsto_horizonGram hφ hφsupp hφ2 hp hCφ hdecay hβ hbulk hh hA.le hsupp hc1 hK hcrit)
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1 x hx
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw : 0 < c N / N := div_pos (by linarith [hc1 N]) hN0
  have hs : 0 < (c N)⁻¹ / ∫ u, atomDilate φ (c N / N) u ^ 2 := by
    rw [integral_atomDilate_sq φ hw]
    have : 0 < c N := by linarith [hc1 N]
    positivity
  have := hN x hx
  rw [HTGeometry.hermQuad_smul] at this
  exact pos_of_mul_pos_right this hs.le

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Mixed families from a positive pencil.** If the untwisted pencil is positive definite on an
independent family `h`, then together with any independent family `g` twisted by a Ramanujan
expansion with `Λ > 0`, the complete family is eventually positive definite on the mixed family. -/
theorem mixed_inherit_of_pencil_pos (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ q : ℝ} (hq : 4 < q)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    {β J : ℝ} (hβ : 0 ≤ β)
    (hbulk : Tendsto (fun s => s ^ β * completedShellEnergy φ s) atTop (𝓝 J))
    {h : ι → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i)) {g : κ → ℝ → ℝ} (hg : ∀ j, ContDiff ℝ 2 (g j))
    (hA : 0 ≤ A) (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0)
    (hgsupp : ∀ j y, y ∉ Set.Icc (-A) 0 → g j y = 0) (hling : LinearIndependent ℝ g)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K))
    {S : Finset ℕ} (hS : ∀ m ∈ S, 1 < m) (a : ℕ → ℝ)
    (hΛ : 0 < (∑ m ∈ S, a m ^ 2 * ArithmeticDegenerationTheory.jordanTotient (β + 1) m) * β * J /
      K)
    (hPpos : ∀ x : ι → ℂ, x ≠ 0 → 0 < hermQuad (pencilGram φ β J K h) x) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ι ⊕ κ → ℂ, x ≠ 0 →
      0 < hermQuad (mixedGram φ h g (ramComb S a) (c N) N) x := by
  set Λ := (∑ m ∈ S, a m ^ 2 * ArithmeticDegenerationTheory.jordanTotient (β + 1) m) * β * J / K
    with hΛdef
  have hPnn : ∀ x : ι → ℂ, 0 ≤ hermQuad (pencilGram φ β J K h) x := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp [hermQuad]
    · exact (hPpos x hx).le
  have hTpos : ∀ y : κ → ℂ, y ≠ 0 → 0 < hermQuad (twistLimitGram β Λ g) y := by
    intro y hy
    unfold twistLimitGram
    rw [HTGeometry.hermQuad_smul]
    have h1 := (Matrix.posDef_iff_dotProduct_mulVec.mp (aliasGram_posDef β hg hgsupp hling)).2 hy
    have : 0 < hermQuad (aliasGram β g) y := by simpa [hermQuad] using (Complex.lt_def.mp h1).1
    exact mul_pos hΛ this
  have hTnn : ∀ y : κ → ℂ, 0 ≤ hermQuad (twistLimitGram β Λ g) y := by
    intro y
    by_cases hy : y = 0
    · subst hy; simp [hermQuad]
    · exact (hTpos y hy).le
  have hpos : ∀ x : ι ⊕ κ → ℂ, x ≠ 0 → 0 < hermQuad (mixedLimitGram φ β J K Λ h g) x := by
    intro x hx
    unfold mixedLimitGram
    rw [hermQuad_fromBlocks_zero]
    by_cases hl : (fun i => x (Sum.inl i)) = 0
    · have hr : (fun j => x (Sum.inr j)) ≠ 0 := by
        intro hr
        apply hx
        funext a
        cases a with
        | inl i => exact congrFun hl i
        | inr j => exact congrFun hr j
      exact add_pos_of_nonneg_of_pos (hPnn _) (hTpos _ hr)
    · exact add_pos_of_pos_of_nonneg (hPpos _ hl) (hTnn _)
  have hherm : (mixedLimitGram φ β J K Λ h g).IsHermitian := by
    unfold mixedLimitGram
    exact Matrix.IsHermitian.fromBlocks
      (pencilGram_isHermitian hφ hφsupp hφ2 hq hCφ hdecay hβ hbulk hh hA hsupp hc1 hK hcrit)
      (by simp) (twistLimitGram_isHermitian β Λ g)
  have hev := eventually_hermQuad_pos_of_tendsto hherm hpos
    (tendsto_mixedGram hφ hφsupp hφ2 hq hCφ hdecay hβ hbulk hh hg hA hsupp hgsupp hc1 hK hcrit hS a)
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1 x hx
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw : 0 < c N / N := div_pos (by linarith [hc1 N]) hN0
  have hs : 0 < (c N)⁻¹ / ∫ u, atomDilate φ (c N / N) u ^ 2 := by
    rw [integral_atomDilate_sq φ hw]
    have : 0 < c N := by linarith [hc1 N]
    positivity
  have := hN x hx
  rw [HTGeometry.hermQuad_smul] at this
  exact pos_of_mul_pos_right this hs.le

/-- **Mixed families below the uniform multiple.** Untwisted windows `h` and windows `g` twisted by
a Ramanujan expansion with `Λ > 0`, both independent, on windows of length `A > 0`: if
`κ (10 + 72 e^{A/2}) K < βJ`, the complete family is eventually positive definite on the mixed
family along `c^{β+1}/log N → K`. -/
theorem mixed_below_uniformMultiple_inherit (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ q : ℝ} (hq : 4 < q)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    {β J : ℝ} (hβ : 0 ≤ β)
    (hbulk : Tendsto (fun s => s ^ β * completedShellEnergy φ s) atTop (𝓝 J))
    {h : ι → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i)) {g : κ → ℝ → ℝ} (hg : ∀ j, ContDiff ℝ 2 (g j))
    (hA : 0 < A) (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0)
    (hgsupp : ∀ j y, y ∉ Set.Icc (-A) 0 → g j y = 0) (hlinh : LinearIndependent ℝ h)
    (hling : LinearIndependent ℝ g) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hsmall : (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * (10 + 72 * Real.exp (A / 2)) * K < β * J)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K))
    {S : Finset ℕ} (hS : ∀ m ∈ S, 1 < m) (a : ℕ → ℝ)
    (hΛ : 0 < (∑ m ∈ S, a m ^ 2 * ArithmeticDegenerationTheory.jordanTotient (β + 1) m) * β * J /
      K) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ι ⊕ κ → ℂ, x ≠ 0 →
      0 < hermQuad (mixedGram φ h g (ramComb S a) (c N) N) x :=
  mixed_inherit_of_pencil_pos hφ hφsupp hφ2 hq hCφ hdecay hβ hbulk hh hg hA.le hsupp hgsupp hling
    hc1 hK hcrit hS a hΛ
    (pencilGram_posDef_below_uniformMultiple (φ := φ) hA (by linarith) hK hsmall hh hsupp hlinh)

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
