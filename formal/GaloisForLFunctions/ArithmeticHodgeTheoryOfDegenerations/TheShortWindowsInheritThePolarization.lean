import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheTwistedSectorInheritsThePolarization
import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.TheWindowIndex
import GaloisForLFunctions.RHTower.WeilFullConeRiemannKernelRigidity

/-!
# The short windows inherit the polarization

Mechanism B (a polarized second-order term is inherited by the nearby fibres) holds on the
twisted sector (`twisted_sector_inherits`). On the untwisted horizon layer the second-order Gram
matrix of a family of windows is the pencil `P_K = κ W(H) + (βJ/K) A(H)`: Weil's Gram matrix of the
synthesized tests plus the aliasing Gram matrix, positive definite on an independent family
(`aliasGram_posDef`). On windows of length `≤ 3/5` Weil's form is nonnegative (CWS
`windowIndex_eq_zero_of_le`), so the pencil is positive definite at every multiple:

* **Weil's Gram matrix of short windows is positive semidefinite**
  (`hermQuad_weilWindowGram_nonneg`): its entries are real, so its form splits into the forms of the
  real and imaginary parts of the coefficient vector, each of which is `κ Q` of a real window test.
* **The short windows inherit the polarization** (`short_windows_inherit`): along the critical
  curve, the Gram matrix of the complete family on every linearly independent family of horizon
  windows of length `≤ 3/5` is eventually positive definite; for the tilted spline
  (`short_windows_inherit_exact`).
* **Mixed short families** (`mixed_short_windows_inherit`): untwisted short windows together with
  windows twisted by a nonzero Ramanujan expansion; the limit is block diagonal with both blocks
  positive definite.

So on short windows the degeneration is polarized unconditionally and positivity passes to the
nearby fibres; the count of the first order alone carries it beyond the windows where Weil's form
is known to be positive only if `Q ≥ 0` there, which is RH.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23 Matrix
open scoped ComplexConjugate ComplexOrder

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri HTGeometry
  RenormalizedArithmeticPotentialTheory.CompletedShell

variable {φ : ℝ → ℝ} {A : ℝ} {κ : Type*} [Fintype κ] [DecidableEq κ]

local notation "Λw" => (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ))

omit [DecidableEq κ] in
/-- A Hermitian form with real entries splits into its real and imaginary parts. -/
theorem hermQuad_eq_re_add_im {G : Matrix κ κ ℂ} (hG : ∀ i j, (G i j).im = 0) (x : κ → ℂ) :
    hermQuad G x = hermQuad G (fun i => ((x i).re : ℂ)) + hermQuad G (fun i => ((x i).im : ℂ)) := by
  simp only [hermQuad, dotProduct, mulVec, Pi.star_apply, Complex.re_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  have hGij : G i j = ((G i j).re : ℂ) := Complex.ext rfl (by simp [hG i j])
  rw [hGij]
  simp only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

omit [DecidableEq κ] in
/-- On real coefficient vectors the form of Weil's Gram matrix is Weil's form of the combination. -/
theorem hermQuad_weilGram_ofReal {H : κ → ℝ → ℝ} (hH : ∀ i, ContDiff ℝ 2 (H i))
    (hHv : ∀ i y, y ∉ Set.Icc (-A) 0 → H i y = 0) (y : κ → ℝ) :
    hermQuad (weilGram Λw fun i => cx (H i)) (fun i => (y i : ℂ)) =
      weilQuad (fun u => ∑ i, y i * H i u) := by
  have hHc : ∀ i, HasCompactSupport (H i) := fun i => hasCompactSupport_of_window (hHv i)
  have hf : ∀ i, ContDiff ℝ 2 (cx (H i)) := fun i => Complex.ofRealCLM.contDiff.comp (hH i)
  have hfc : ∀ i, HasCompactSupport (cx (H i)) := fun i => (hHc i).comp_left Complex.ofReal_zero
  rw [hermQuad_weilGram Λw _ hf hfc]
  have hS : (∑ i, conj ((y i : ℂ)) • cx (H i)) = fun u => ((∑ i, y i * H i u : ℝ) : ℂ) := by
    funext u
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.conj_ofReal, cx]
    push_cast; rfl
  rw [hS]
  have hF : ContDiff ℝ 2 (fun u => ∑ i, y i * H i u) :=
    ContDiff.sum fun i _ => contDiff_const.mul (hH i)
  have hFc : HasCompactSupport (fun u => ∑ i, y i * H i u) :=
    hasCompactSupport_of_window (A := A) fun u hu => by simp [hHv _ u hu]
  rw [LogCells.weilQuad_eq_zetaW hF hFc]
  have hcF : ContDiff ℝ 2 (fun u => ((∑ i, y i * H i u : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hF
  have hcFc : HasCompactSupport (fun u => ((∑ i, y i * H i u : ℝ) : ℂ)) :=
    hFc.comp_left Complex.ofReal_zero
  rw [RHTower.zeta_W_eq_weilFullFunctional hcF hcFc]

omit [DecidableEq κ] in
/-- **Weil's Gram matrix of short windows is positive semidefinite.** For windows of length
`A ≤ 3/5`, `hermQuad (κ W(H)) x ≥ 0` for every complex `x`. -/
theorem hermQuad_weilWindowGram_nonneg (hA : A ≤ 3 / 5) {h : κ → ℝ → ℝ}
    (hh : ∀ i, ContDiff ℝ 2 (h i)) (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) (x : κ → ℂ) :
    0 ≤ hermQuad (weilWindowGram φ h) x := by
  have hH : ∀ i, ContDiff ℝ 2 (halfWeight (h i)) := fun i => contDiff_halfWeight (hh i)
  have hHc : ∀ i, HasCompactSupport (halfWeight (h i)) := fun i =>
    hasCompactSupport_halfWeight (hasCompactSupport_of_window (hsupp i))
  have hHv : ∀ i y, y ∉ Set.Icc (-A) 0 → halfWeight (h i) y = 0 := fun i =>
    halfWeight_eq_zero_of_window (hsupp i)
  have hpos := CohomologyOfWindowsOfSpecZ.windowIndex_eq_zero_iff.mp
    (CohomologyOfWindowsOfSpecZ.windowIndex_eq_zero_of_le hA)
  have hQ : ∀ y : κ → ℝ, 0 ≤ weilQuad (fun u => ∑ i, y i * halfWeight (h i) u) := fun y =>
    hpos _ ⟨ContDiff.sum fun i _ => contDiff_const.mul (hH i), fun u hu => by
      simp [hHv _ u hu]⟩
  have hreal : ∀ i j, ((weilGram Λw fun i => cx (halfWeight (h i))) i j).im = 0 := by
    intro i j
    simp only [weilGram]
    rw [EffectiveArithmeticHodgeTheory.weilPair_real_eq (hH i) (hHc i) (hH j) (hHc j),
      Complex.ofReal_im]
  unfold weilWindowGram
  rw [HTGeometry.hermQuad_smul, hermQuad_eq_re_add_im hreal]
  have h1 := hermQuad_weilGram_ofReal hH hHv (fun i => (x i).re)
  have h2 := hermQuad_weilGram_ofReal hH hHv (fun i => (x i).im)
  rw [h1, h2]
  have hκ : 0 ≤ (∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 := by
    have : (0 : ℝ) ≤ ∫ u, φ u ^ 2 := integral_nonneg fun u => sq_nonneg (φ u)
    positivity
  exact mul_nonneg hκ (add_nonneg (hQ _) (hQ _))

/-- **The short windows inherit the polarization.** For every profile with bulk limit
`s^β E₁(s) → J`, `βJ > 0`, and every linearly independent family of horizon windows of length
`A ≤ 3/5`: along `c^{β+1}/log N → K > 0`, the Gram matrix of the complete family on the family is
eventually positive definite. -/
theorem short_windows_inherit (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ p : ℝ} (hp : 4 < p) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    {β J : ℝ} (hβ : 0 ≤ β) (hβJ : 0 < β * J)
    (hbulk : Tendsto (fun s => s ^ β * completedShellEnergy φ s) atTop (𝓝 J))
    {h : κ → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i)) (hA : 0 ≤ A) (hA35 : A ≤ 3 / 5)
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) (hlin : LinearIndependent ℝ h)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K)) :
    ∀ᶠ N : ℕ in atTop, ∀ x : κ → ℂ, x ≠ 0 → 0 < hermQuad (horizonGram φ h (c N) N) x := by
  have hpos : ∀ x : κ → ℂ, x ≠ 0 → 0 < hermQuad (pencilGram φ β J K h) x := by
    intro x hx
    rw [pencilGram_eq hh hsupp, HTGeometry.hermQuad_add, HTGeometry.hermQuad_smul]
    have hW := hermQuad_weilWindowGram_nonneg (φ := φ) hA35 hh hsupp x
    have hB : 0 < hermQuad (aliasGram β h) x := by
      have h1 := (Matrix.posDef_iff_dotProduct_mulVec.mp (aliasGram_posDef β hh hsupp hlin)).2 hx
      simpa [hermQuad] using (Complex.lt_def.mp h1).1
    have hc : 0 < β * J / K := div_pos hβJ hK
    nlinarith
  have hev := eventually_hermQuad_pos_of_tendsto
    (pencilGram_isHermitian hφ hφsupp hφ2 hp hCφ hdecay hβ hbulk hh hA hsupp hc1 hK hcrit) hpos
    (tendsto_horizonGram hφ hφsupp hφ2 hp hCφ hdecay hβ hbulk hh hA hsupp hc1 hK hcrit)
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

/-- **Short windows inherit, tilted spline.** Along `c⁸/log N → K`, the Gram matrix of the complete
family on every linearly independent family of horizon windows of length `≤ 3/5` is eventually
positive definite. -/
theorem short_windows_inherit_exact {h : κ → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i)) (hA : 0 ≤ A)
    (hA35 : A ≤ 3 / 5) (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0)
    (hlin : LinearIndependent ℝ h) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K)) :
    ∀ᶠ N : ℕ in atTop, ∀ x : κ → ℂ, x ≠ 0 →
      0 < hermQuad (horizonGram tiltedUnitSpline h (c N) N) x := by
  have hC : 0 ≤ tiltedDecayConst := by unfold tiltedDecayConst; positivity
  have hcrit' : Tendsto (fun N : ℕ => c N ^ ((7 : ℝ) + 1) / Real.log N) atTop (𝓝 K) := by
    refine hcrit.congr fun N => ?_
    rw [show (7 : ℝ) + 1 = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact short_windows_inherit contDiff_tiltedUnitSpline tiltedUnitSpline_support
    integral_tiltedUnitSpline_sq_pos (p := 8) (by norm_num) hC tiltedUnitSpline_decay (β := 7)
    (by norm_num) (by have := tiltedJordanOne_pos; positivity)
    tendsto_rpow_seven_mul_completedShellEnergy_tilted hh hA hA35 hsupp hlin hc1 hK hcrit'

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] [DecidableEq κ] in
/-- The form of a block-diagonal matrix is the sum of the forms of its blocks. -/
theorem hermQuad_fromBlocks_zero (P : Matrix ι ι ℂ) (T : Matrix κ κ ℂ) (x : ι ⊕ κ → ℂ) :
    hermQuad (fromBlocks P 0 0 T) x =
      hermQuad P (fun i => x (Sum.inl i)) + hermQuad T (fun j => x (Sum.inr j)) := by
  have hx : x = Sum.elim (fun i => x (Sum.inl i)) (fun j => x (Sum.inr j)) := by
    funext a; cases a <;> rfl
  conv_lhs => rw [hx]
  simp only [hermQuad, fromBlocks_mulVec, Matrix.zero_mulVec, zero_add, add_zero, dotProduct,
    Fintype.sum_sum_type, Pi.star_apply, Sum.elim_inl, Sum.elim_inr, Complex.add_re,
    Sum.elim_comp_inl, Sum.elim_comp_inr]

/-- **Mixed short families inherit the polarization.** Untwisted windows `h` and windows `g`
twisted by a Ramanujan expansion `Σ a_m c_m`, both independent, on a window of length `≤ 3/5`,
with `Λ = (Σ a_m² J_{β+1}(m)) βJ/K > 0`: the Gram matrix of the complete family on the mixed
family is eventually positive definite. -/
theorem mixed_short_windows_inherit (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ q : ℝ} (hq : 4 < q)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    {β J : ℝ} (hβ : 0 ≤ β) (hβJ : 0 < β * J)
    (hbulk : Tendsto (fun s => s ^ β * completedShellEnergy φ s) atTop (𝓝 J))
    {h : ι → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i)) {g : κ → ℝ → ℝ} (hg : ∀ j, ContDiff ℝ 2 (g j))
    (hA : 0 ≤ A) (hA35 : A ≤ 3 / 5) (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0)
    (hgsupp : ∀ j y, y ∉ Set.Icc (-A) 0 → g j y = 0) (hlinh : LinearIndependent ℝ h)
    (hling : LinearIndependent ℝ g) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K))
    {S : Finset ℕ} (hS : ∀ m ∈ S, 1 < m) (a : ℕ → ℝ)
    (hΛ : 0 < (∑ m ∈ S, a m ^ 2 * ArithmeticDegenerationTheory.jordanTotient (β + 1) m) * β * J /
      K) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ι ⊕ κ → ℂ, x ≠ 0 →
      0 < hermQuad (mixedGram φ h g (ramComb S a) (c N) N) x := by
  set Λ := (∑ m ∈ S, a m ^ 2 * ArithmeticDegenerationTheory.jordanTotient (β + 1) m) * β * J / K
    with hΛdef
  have hPpos : ∀ x : ι → ℂ, x ≠ 0 → 0 < hermQuad (pencilGram φ β J K h) x := by
    intro x hx
    rw [pencilGram_eq hh hsupp, HTGeometry.hermQuad_add, HTGeometry.hermQuad_smul]
    have hW := hermQuad_weilWindowGram_nonneg (φ := φ) hA35 hh hsupp x
    have hB : 0 < hermQuad (aliasGram β h) x := by
      have h1 := (Matrix.posDef_iff_dotProduct_mulVec.mp (aliasGram_posDef β hh hsupp hlinh)).2 hx
      simpa [hermQuad] using (Complex.lt_def.mp h1).1
    have hc : 0 < β * J / K := div_pos hβJ hK
    nlinarith
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

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
