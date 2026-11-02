import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.TheWindowIndex
import GaloisForLFunctions.ArithmeticEffectivityTheory.TatesLimitLaw

/-!
# Naive heights on window correspondences

A window test `x` of length `a` and an integral correspondence `ξ = Σ ξ(s)[s]` with shifts in
`[a − A, 0]` give the window test `Σ ξ(s) x(· − s)` of length `A` (`corrTest`, `corrTest_isWindowTest`).
Its Weil form is the **window integral Rosati form** `q_x(ξ) = τ_x(ξ ⋆ ξ′)` (`windowRosati`),
homogeneous of degree two (`windowRosati_nsmul`; Weil's form is, `weilQuad_const_mul`).

* **Windowed Tate law** (`exists_window_naiveHeight_iff`): `q_x` has a naive height on the window
  correspondences — a function bounded below at bounded distance from it — iff it is nonnegative
  there. A count at bounded distance from `τ_x(ξ ⋆ ξ′)` exists exactly when the window is Rosati
  positive at `x`.
* **The count recovers the form** (`tendsto_naiveHeight_nsmul_div`): any function at bounded distance
  from `q_x` has `h(mξ)/m² → q_x(ξ)`: a window count determines the window form by Tate's limit.
* **Short windows** (`exists_window_naiveHeight_of_le`): on windows of length `≤ 3/5` every window
  Rosati form has a naive height.
* **All windows** (`riemannHypothesis_iff_forall_window_naiveHeight`): RH holds iff every window
  Rosati form of every length has a naive height. What a proof needs is the count itself: a function
  on window correspondences, nonnegative for an arithmetic reason, at bounded distance from `q_x`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.CohomologyOfWindowsOfSpecZ

open SpacingScaleHarmonicAnalysis ArithmeticCastelnuovoSeveri ArithmeticEffectivityTheory

/-! ### Homogeneity of Weil's form -/

/-- The Weil functional is homogeneous in a real multiple of its argument. -/
theorem weilFullFunctional_ofReal_smul (lam : ℕ → ℝ) (c : ℝ) (k : ℝ → ℂ) :
    RHTower.weilFullFunctional lam ((c : ℂ) • k) = (c : ℂ) * RHTower.weilFullFunctional lam k := by
  unfold RHTower.weilFullFunctional
  rw [paperFT_smul, paperFT_smul]
  have hs : (∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
      (((c : ℂ) • k) (Real.log n) + ((c : ℂ) • k) (-Real.log n))) =
      (c : ℂ) * ∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
        (k (Real.log n) + k (-Real.log n)) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hi : (∫ r : ℝ, paperFT ((c : ℂ) • k) r * (EF.gammaBracket r : ℂ)) =
      (c : ℂ) * ∫ r : ℝ, paperFT k r * (EF.gammaBracket r : ℂ) := by
    rw [← integral_const_mul]
    congr 1; funext r
    rw [paperFT_smul]; ring
  rw [hs, hi]
  ring

/-- **Weil's form is homogeneous of degree two**: `Q(cH) = c² Q(H)`. -/
theorem weilQuad_const_mul (c : ℝ) (H : ℝ → ℝ) :
    weilQuad (fun u => c * H u) = c ^ 2 * weilQuad H := by
  unfold weilQuad
  have hk : EF.weilTest (fun u => ((c * H u : ℝ) : ℂ)) (fun u => ((c * H u : ℝ) : ℂ)) =
      ((c ^ 2 : ℝ) : ℂ) • EF.weilTest (fun u => (H u : ℂ)) (fun u => (H u : ℂ)) := by
    funext y
    rw [Pi.smul_apply, RHTower.weilTest_ofReal_eq, RHTower.weilTest_ofReal_eq, smul_eq_mul,
      ← Complex.ofReal_mul, ← integral_const_mul]
    congr 2; funext t; ring
  rw [hk, weilFullFunctional_ofReal_smul, Complex.re_ofReal_mul]

/-! ### Window correspondences -/

/-- The test `Σ_s ξ(s) x(· − s)` of an integral correspondence `ξ` acting on `x`. -/
def corrTest (x : ℝ → ℝ) (ξ : ℝ →₀ ℤ) : ℝ → ℝ :=
  fun u => ∑ s ∈ ξ.support, (ξ s : ℝ) * x (u - s)

/-- The **window integral Rosati form** `q_x(ξ) = τ_x(ξ ⋆ ξ′) = Q(Σ ξ(s) x(· − s))`. -/
def windowRosati (x : ℝ → ℝ) (ξ : ℝ →₀ ℤ) : ℝ := weilQuad (corrTest x ξ)

/-- The correspondences of a window of length `A` acting on tests of length `a`: shifts in
`[a − A, 0]`. -/
def windowCorr (A a : ℝ) : AddSubgroup (ℝ →₀ ℤ) :=
  (Finsupp.supported ℤ ℤ (Icc (a - A) 0)).toAddSubgroup

theorem corrTest_nsmul (x : ℝ → ℝ) (m : ℕ) (ξ : ℝ →₀ ℤ) :
    corrTest x (m • ξ) = fun u => (m : ℝ) * corrTest x ξ u := by
  funext u
  unfold corrTest
  rw [Finset.mul_sum]
  have hsub : (m • ξ).support ⊆ ξ.support := Finsupp.support_smul
  rw [Finset.sum_subset hsub fun s _ hs => by
    rw [Finsupp.notMem_support_iff.mp hs]; simp]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finsupp.smul_apply, nsmul_eq_mul]
  push_cast; ring

/-- **The window Rosati form is homogeneous of degree two.** -/
theorem windowRosati_nsmul (x : ℝ → ℝ) (m : ℕ) (ξ : ℝ →₀ ℤ) :
    windowRosati x (m • ξ) = (m : ℝ) ^ 2 * windowRosati x ξ := by
  rw [windowRosati, windowRosati, corrTest_nsmul, weilQuad_const_mul]

/-- A window correspondence acting on a window test of length `a` gives a window test of length
`A`. -/
theorem corrTest_isWindowTest {A a : ℝ} {x : ℝ → ℝ} (hx : IsWindowTest a x) {ξ : ℝ →₀ ℤ}
    (hξ : ξ ∈ windowCorr A a) : IsWindowTest A (corrTest x ξ) := by
  have hs : ∀ s ∈ ξ.support, s ∈ Icc (a - A) 0 := fun s hs =>
    (Finsupp.mem_supported ℤ ξ).mp hξ hs
  refine ⟨ContDiff.sum fun s _ => contDiff_const.mul
    (hx.contDiff.comp (contDiff_id.sub contDiff_const)), fun y hy => ?_⟩
  refine Finset.sum_eq_zero fun s hsξ => ?_
  rw [hx.vanish (y - s) fun hm => hy ⟨?_, ?_⟩, mul_zero]
  · linarith [hm.1, (hs s hsξ).1]
  · linarith [hm.2, (hs s hsξ).2]

/-! ### The windowed Tate law -/

/-- **Windowed Tate law**: the window Rosati form at `x` has a naive height on the window
correspondences iff it is nonnegative there. -/
theorem exists_window_naiveHeight_iff (x : ℝ → ℝ) (A a : ℝ) :
    (∃ h : windowCorr A a → ℝ, ∃ K B : ℝ, (∀ ξ, -K ≤ h ξ) ∧
        ∀ ξ, |h ξ - windowRosati x ξ| ≤ B) ↔
      ∀ ξ ∈ windowCorr A a, 0 ≤ windowRosati x ξ := by
  have hq : ∀ (m : ℕ) (ξ : windowCorr A a),
      windowRosati x ↑(m • ξ) = (m : ℝ) ^ 2 * windowRosati x ξ := fun m ξ => by
    rw [AddSubgroup.coe_nsmul, windowRosati_nsmul]
  rw [exists_naiveHeight_iff_nonneg (q := fun ξ : windowCorr A a => windowRosati x ξ) hq]
  exact ⟨fun h ξ hξ => h ⟨ξ, hξ⟩, fun h ξ => h ξ ξ.2⟩

/-- **A window count recovers the window form**: if `|h − q| ≤ B` and `q(mξ) = m²q(ξ)`, then
`h(mξ)/m² → q(ξ)`. -/
theorem tendsto_naiveHeight_nsmul_div {M : Type*} [AddCommGroup M] {q h : M → ℝ}
    (hq : ∀ (m : ℕ) x, q (m • x) = (m : ℝ) ^ 2 * q x) {B : ℝ} (hB : ∀ x, |h x - q x| ≤ B)
    (x : M) : Tendsto (fun m : ℕ => h (m • x) / (m : ℝ) ^ 2) atTop (𝓝 (q x)) := by
  have hlim : Tendsto (fun m : ℕ => q x + (h (m • x) - q (m • x)) / (m : ℝ) ^ 2) atTop
      (𝓝 (q x + 0)) := by
    refine tendsto_const_nhds.add ?_
    have hden : Tendsto (fun m : ℕ => (m : ℝ) ^ 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop
    refine squeeze_zero_norm (a := fun m : ℕ => B / (m : ℝ) ^ 2) (fun m => ?_)
      (tendsto_const_nhds.div_atTop hden)
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (m : ℝ))]
    exact div_le_div_of_nonneg_right (hB _) (sq_nonneg _)
  rw [add_zero] at hlim
  refine hlim.congr' (eventually_atTop.mpr ⟨1, fun m hm => ?_⟩)
  have hm0 : (m : ℝ) ^ 2 ≠ 0 := by positivity
  rw [hq m x]
  field_simp
  ring

/-- **Short windows have naive heights**: on windows of length `≤ 3/5` every window Rosati form is
nonnegative, hence its own naive height. -/
theorem exists_window_naiveHeight_of_le {A a : ℝ} (hA : A ≤ 3 / 5) {x : ℝ → ℝ}
    (hx : IsWindowTest a x) :
    ∃ h : windowCorr A a → ℝ, ∃ K B : ℝ, (∀ ξ, -K ≤ h ξ) ∧
      ∀ ξ, |h ξ - windowRosati x ξ| ≤ B :=
  (exists_window_naiveHeight_iff x A a).mpr fun _ hξ =>
    windowIndex_eq_zero_iff.mp (windowIndex_eq_zero_of_le hA) _ (corrTest_isWindowTest hx hξ)

/-- **RH is the existence of naive heights on all windows.** -/
theorem riemannHypothesis_iff_forall_window_naiveHeight :
    RiemannHypothesis ↔ ∀ A a : ℝ, 0 ≤ a → a ≤ A → ∀ x : ℝ → ℝ, IsWindowTest a x →
      ∃ h : windowCorr A a → ℝ, ∃ K B : ℝ, (∀ ξ, -K ≤ h ξ) ∧
        ∀ ξ, |h ξ - windowRosati x ξ| ≤ B := by
  constructor
  · intro hRH A a ha haA x hx
    refine (exists_window_naiveHeight_iff x A a).mpr fun ξ hξ => ?_
    exact riemannHypothesis_iff_windowForm_nonneg.mp hRH A (ha.trans haA) _
      (corrTest_isWindowTest hx hξ)
  · intro h
    refine riemannHypothesis_iff_windowForm_nonneg.mpr fun A hA H hH => ?_
    have hξ : Finsupp.single (0 : ℝ) (1 : ℤ) ∈ windowCorr A A := by
      refine (Finsupp.mem_supported ℤ _).mpr fun s hs => ?_
      have hs' := Finsupp.support_single_subset (Finset.mem_coe.mp hs)
      rw [Finset.mem_singleton] at hs'
      subst hs'
      exact ⟨by linarith, le_rfl⟩
    have hq := (exists_window_naiveHeight_iff H A A).mp (h A A hA le_rfl H hH) _ hξ
    have hc : corrTest H (Finsupp.single 0 1) = H := by
      funext u
      simp [corrTest]
    rwa [windowRosati, hc] at hq

end GaloisForLFunctions.CohomologyOfWindowsOfSpecZ
