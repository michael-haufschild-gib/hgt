import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.TheWindowDatum
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHodgeDefectCountsTheRightZeros
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteWeilSourceTransfer
import GaloisForLFunctions.LatticeSectionTheory.ThePrimitiveH1OfPrimeFreeCyclesIsAJumpCount
import GaloisForLFunctions.RHTower.WeilConditionalConstantSignRigidity
import GaloisForLFunctions.LatticeSectionTheory.HeckeCorrespondencesAreSimilitudesOfThePrimitiveH1

/-!
# Realizations of the window `h¹`

The window `h¹` is the primitive `h¹` of the Künneth count of LST on the cycle of a window test
(`primitiveH1_windowCycle`): `h_K(x) + h_K(−x) = χ(x) + h¹_K(x) + ½Q(H)` with `h¹_K > 0`
(`kunneth_windowCycle`), so the counts pay everything but half of Weil's window form.

A **realization** of the window `h¹` of length `A` is a real linear map `r` from window tests to a
normed space with `Q(H) = ‖r H‖²` (`IsWindowRealization`): the `h¹` becomes a squared length.

* **A realization forces the sign** (`weilQuad_nonneg_of_isWindowRealization`), so realizations at
  every length give RH.
* **Under RH the zero map realizes every window** (`isWindowRealization_zeroMap`): the coordinates
  `√m_ρ Ĥ(γ_ρ)` in `ℓ²(zeros)`; the Krein reflection `ρ ↦ 1 − ρ̄` is the identity on the line.
  Hence `RH ⟺` every window has a realization in `ℓ²(zeros)`
  (`riemannHypothesis_iff_forall_windowRealization`). The existence of a realization carries no
  information beyond the sign: the content of a window cohomology is a construction of `r` that does
  not use the zeros.
* **No window cohomology is finite-dimensional** (`not_isWindowRealization_of_finiteDimensional`):
  short windows are coercive, `Q(H) ≥ ‖H‖²/4` for windows of length `≤ 1/1000`
  (`weilQuad_ge_of_short`, from the jump count of LST); every window of positive length contains an
  infinite-dimensional coercive subspace, so a realization never has finite-dimensional target. The
  "finite object" of a window can only be finite modulo a threshold (the window genus) or a lattice
  of growing rank.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23
open scoped lp

namespace GaloisForLFunctions.CohomologyOfWindowsOfSpecZ

open SpacingScaleHarmonicAnalysis ArithmeticCastelnuovoSeveri

/-- The window tests of length `A` as a real vector space. -/
def windowTests (A : ℝ) : Submodule ℝ (ℝ → ℝ) where
  carrier := {H | IsWindowTest A H}
  add_mem' {H G} hH hG := ⟨hH.contDiff.add hG.contDiff, fun y hy => by
    simp [hH.vanish y hy, hG.vanish y hy]⟩
  zero_mem' := ⟨contDiff_const, fun _ _ => rfl⟩
  smul_mem' c H hH := ⟨hH.contDiff.const_smul c, fun y hy => by simp [hH.vanish y hy]⟩

theorem mem_windowTests {A : ℝ} {H : ℝ → ℝ} : H ∈ windowTests A ↔ IsWindowTest A H := Iff.rfl

/-- A **realization** of the window `h¹`: a real linear `r` with `Q(H) = ‖r H‖²`. -/
def IsWindowRealization (A : ℝ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : windowTests A →ₗ[ℝ] E) : Prop :=
  ∀ H : windowTests A, weilQuad H = ‖r H‖ ^ 2

variable {A : ℝ}

theorem weilQuad_nonneg_of_isWindowRealization {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {r : windowTests A →ₗ[ℝ] E} (hr : IsWindowRealization A r)
    (H : windowTests A) : 0 ≤ weilQuad H := by
  rw [hr H]; positivity

/-! ### The Künneth `h¹` of a window -/

/-- The cycle `(0, 0, H)` of the scaling surface carried by a window test. -/
def windowCycle (H : windowTests A) : ScalingCycle :=
  (0, 0, ⟨H, H.2.contDiff, H.2.hasCompactSupport⟩)

/-- **The window `h¹` is the primitive Künneth `h¹`**: `h¹_prim(x_H) = ½Q(H)`. -/
theorem primitiveH1_windowCycle (H : windowTests A) :
    LatticeSectionTheory.primitiveH1 scalingSurface (windowCycle H) = weilQuad H / 2 := by
  rw [LatticeSectionTheory.primitiveH1_eq, scalingSurface_defect_self]
  rfl

/-- **Künneth Riemann–Roch on a window**: `h_K(x) + h_K(−x) = χ(x) + h¹_K(x) + ½Q(H)`, and the
Künneth part `h¹_K` is positive because it is a product of counts. -/
theorem kunneth_windowCycle (H : windowTests A) :
    LatticeSectionTheory.kunnethH0 scalingSurface (windowCycle H) +
        LatticeSectionTheory.kunnethH0 scalingSurface (0 - windowCycle H) =
      ArithmeticEffectivityTheory.eulerChar scalingSurface 0 0 (windowCycle H) +
        LatticeSectionTheory.kunnethH1 scalingSurface (windowCycle H) + weilQuad H / 2 ∧
    0 < LatticeSectionTheory.kunnethH1 scalingSurface (windowCycle H) := by
  refine ⟨?_, LatticeSectionTheory.kunnethH1_pos _ _⟩
  rw [LatticeSectionTheory.kunnethH0_add_neg, scalingSurface_defect_self]
  rfl

/-! ### The zero map -/

/-- The complexification of window tests into the test space of the zero configuration. -/
def cxWindow (A : ℝ) : windowTests A →ₗ[ℝ] testSpace where
  toFun H := ⟨cx H, cx_contDiff H.2.contDiff, cx_hasCompactSupport H.2.hasCompactSupport⟩
  map_add' H G := by
    ext u; simp [cx]
  map_smul' c H := by
    ext u; simp [cx, Complex.real_smul]

/-- The **zero map** of a window: `H ↦ (√m_ρ Ĥ(γ_ρ))_ρ` in `ℓ²(zeros of ζ)`. -/
def windowZeroMap (A : ℝ) : windowTests A →ₗ[ℝ] ℓ²(zetaZeroConfig.carrier, ℂ) :=
  ((zeroMap zetaZeroConfig SquareRootThreshold.temperedConfig_zetaZeroConfig).restrictScalars ℝ).comp
    (cxWindow A)

/-- Under RH the Krein reflection `ρ ↦ 1 − ρ̄` fixes every zero. -/
theorem reflectVec_eq_self_of_riemannHypothesis (hRH : RiemannHypothesis)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) : reflectVec zetaZeroConfig x = x := by
  ext τ
  have hfix : reflectCarrier zetaZeroConfig τ = τ := by
    refine Subtype.ext ?_
    have hre := RHTower.WeilConditional.re_eq_half_of_carrier hRH τ
    simp only [reflectCarrier, reflect]
    apply Complex.ext <;> simp [hre]; norm_num
  rw [reflectVec_apply, hfix]

/-- **Under RH the zero map realizes every window.** -/
theorem isWindowRealization_zeroMap (hRH : RiemannHypothesis) (A : ℝ) :
    IsWindowRealization A (windowZeroMap A) := by
  intro H
  have hW := LogCells.weilQuad_eq_zetaW H.2.contDiff H.2.hasCompactSupport
  rw [hW]
  have hi := W_eq_inner zetaZeroConfig SquareRootThreshold.temperedConfig_zetaZeroConfig
    (cxWindow A H) (cxWindow A H)
  have hcx : ((cxWindow A H : testSpace) : ℝ → ℂ) = fun u => ((H : ℝ → ℝ) u : ℂ) := rfl
  rw [hcx, reflectVec_eq_self_of_riemannHypothesis hRH] at hi
  rw [hi]
  have hr : windowZeroMap A H =
      zeroMap zetaZeroConfig SquareRootThreshold.temperedConfig_zetaZeroConfig (cxWindow A H) := rfl
  rw [hr]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

/-- **RH is the existence of a realization of every window** (in `ℓ²(zeros)`). -/
theorem riemannHypothesis_iff_forall_windowRealization :
    RiemannHypothesis ↔ ∀ A : ℝ, 0 ≤ A →
      ∃ r : windowTests A →ₗ[ℝ] ℓ²(zetaZeroConfig.carrier, ℂ), IsWindowRealization A r := by
  constructor
  · exact fun hRH A _ => ⟨windowZeroMap A, isWindowRealization_zeroMap hRH A⟩
  · intro h
    refine riemannHypothesis_iff_windowForm_nonneg.mpr fun A hA H hH => ?_
    obtain ⟨r, hr⟩ := h A hA
    exact weilQuad_nonneg_of_isWindowRealization hr ⟨H, hH⟩

/-! ### Short windows are coercive -/

/-- **Short windows are coercive**: on windows of length `0 < A ≤ 1/1000`, `Q(H) ≥ ‖H‖²/4`
(the jump count of the Gamma factor pays the archimedean constant and the pole). -/
theorem weilQuad_ge_of_short {H : ℝ → ℝ} (hH : IsWindowTest A H) (hA0 : 0 < A)
    (hA : A ≤ 1 / 1000) : (∫ u, H u ^ 2) / 4 ≤ weilQuad H := by
  set G : ℝ → ℝ := fun u => H (u - A / 2) with hG
  have hGv : ∀ y, y ∉ Icc (-(A / 2)) (A / 2) → G y = 0 := fun y hy => by
    refine hH.vanish _ fun hm => hy ⟨?_, ?_⟩ <;> linarith [hm.1, hm.2]
  have hGt : G ∈ realTests := by
    refine ⟨hH.contDiff.comp (contDiff_id.sub contDiff_const), ?_⟩
    exact HasCompactSupport.intro (isCompact_Icc (a := -(A / 2)) (b := A / 2)) hGv
  have hGs : tsupport G ⊆ Icc (-(A / 2)) (A / 2) := by
    refine closure_minimal (fun y hy => ?_) isClosed_Icc
    by_contra hn
    exact hy (hGv y hn)
  have h := LatticeSectionTheory.jumpCount_derivation_of_primeFree_positivity hGt hGs
    (by linarith) (by linarith)
  have hQ : weilPair G G = weilQuad H := by
    show weilQuad G = weilQuad H
    exact weilQuad_comp_sub H (A / 2)
  have hL : ∫ u, G u ^ 2 = ∫ u, H u ^ 2 := integral_sub_right_eq_self (fun u => H u ^ 2) (A / 2)
  rw [hQ, hL] at h
  exact h

/-! ### No finite-dimensional window cohomology -/

/-- The bump of the `i`-th cell `[−a + iδ, −a + (i+1)δ]`: centre `−a + (i + ½)δ`, radius `δ/2`. -/
def cellBump (a δ : ℝ) (hδ : 0 < δ) (i : ℕ) : ContDiffBump (-a + (i + 1 / 2) * δ) :=
  ⟨δ / 4, δ / 2, by positivity, by linarith⟩

/-- The `i`-th cell bump vanishes off the open `i`-th cell. -/
theorem cellBump_eq_zero {a δ : ℝ} (hδ : 0 < δ) (i : ℕ) {y : ℝ}
    (hy : y ∉ Ioo (-a + i * δ) (-a + (i + 1) * δ)) : (cellBump a δ hδ i) y = 0 := by
  refine (cellBump a δ hδ i).zero_of_le_dist ?_
  show δ / 2 ≤ dist y (-a + (i + 1 / 2) * δ)
  rw [Real.dist_eq, le_abs]
  have e1 : ((i : ℝ) + 1 / 2) * δ = i * δ + δ / 2 := by ring
  have e2 : ((i : ℝ) + 1) * δ = i * δ + δ := by ring
  simp only [mem_Ioo, not_and_or, not_lt] at hy
  rcases hy with hy | hy
  · right; linarith
  · left; linarith

/-- A cell bump inside `[−a, 0]` is a window test of length `a`. -/
theorem cellBump_isWindowTest {a δ : ℝ} (hδ : 0 < δ) {i : ℕ} (hi : ((i : ℝ) + 1) * δ ≤ a) :
    IsWindowTest a (cellBump a δ hδ i) := by
  refine ⟨(cellBump a δ hδ i).contDiff, fun y hy => cellBump_eq_zero hδ i fun hm => hy ?_⟩
  have h1 : 0 ≤ (i : ℝ) * δ := by positivity
  exact ⟨by linarith [hm.1], by linarith [hm.2]⟩

/-- Distinct cell bumps vanish at each other's centres; each is `1` at its own. -/
theorem cellBump_center {a δ : ℝ} (hδ : 0 < δ) (i j : ℕ) :
    (cellBump a δ hδ i) (-a + (j + 1 / 2) * δ) = if i = j then 1 else 0 := by
  split_ifs with h
  · subst h
    exact (cellBump a δ hδ i).one_of_mem_closedBall (Metric.mem_closedBall_self (by
      show (0 : ℝ) ≤ δ / 4; positivity))
  · refine cellBump_eq_zero hδ i fun hm => ?_
    obtain ⟨h1, h2⟩ := hm
    have e1 : ((j : ℝ) + 1 / 2) * δ = j * δ + δ / 2 := by ring
    have e2 : ((i : ℝ) + 1) * δ = i * δ + δ := by ring
    rcases lt_or_gt_of_ne h with hij | hij
    · have h3 : ((i : ℝ) + 1) * δ ≤ j * δ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hδ.le
      linarith
    · have h3 : ((j : ℝ) + 1) * δ ≤ i * δ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hδ.le
      linarith

/-- A combination of cell bumps that vanishes everywhere has zero coefficients. -/
theorem eq_zero_of_sum_cellBump {a δ : ℝ} (hδ : 0 < δ) {n : ℕ} (c : Fin n → ℝ)
    (h : ∀ y, ∑ i, c i * cellBump a δ hδ i y = 0) : c = 0 := by
  funext j
  have := h (-a + ((j : ℕ) + 1 / 2) * δ)
  simp_rw [cellBump_center hδ, Fin.val_inj, mul_ite, mul_one, mul_zero] at this
  simpa using this

/-- On a short window a test with `Q(H) = 0` vanishes. -/
theorem eq_zero_of_weilQuad_eq_zero_of_short {H : ℝ → ℝ} (hH : IsWindowTest A H) (hA0 : 0 < A)
    (hA : A ≤ 1 / 1000) (hQ : weilQuad H = 0) (y : ℝ) : H y = 0 := by
  by_contra hy
  have h1 := weilQuad_ge_of_short hH hA0 hA
  have hpos := Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume)
    (f := fun u => H u ^ 2) (x := y) (hH.continuous.pow 2)
    (hH.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num))
    (fun u => sq_nonneg (H u)) (pow_ne_zero 2 hy)
  linarith

/-- **No window cohomology is finite-dimensional**: for `A > 0` no realization of the window `h¹`
has a finite-dimensional target. -/
theorem not_isWindowRealization_of_finiteDimensional (hA : 0 < A) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (r : windowTests A →ₗ[ℝ] E) : ¬ IsWindowRealization A r := by
  intro hr
  set a := min A (1 / 1000) with ha_def
  have ha0 : 0 < a := lt_min hA (by norm_num)
  have haA : a ≤ A := min_le_left _ _
  have ha1 : a ≤ 1 / 1000 := min_le_right _ _
  set n := Module.finrank ℝ E + 1 with hn_def
  set δ := a / n with hδ_def
  have hn0 : (0 : ℝ) < n := by positivity
  have hδ : 0 < δ := div_pos ha0 hn0
  have hcell : ∀ i : Fin n, ((i : ℕ) + 1 : ℝ) * δ ≤ a := fun i => by
    have : ((i : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast i.2
    calc (((i : ℕ) : ℝ) + 1) * δ ≤ n * δ := mul_le_mul_of_nonneg_right this hδ.le
      _ = a := by rw [hδ_def]; field_simp
  -- `n` bumps in disjoint cells of `[−a, 0]`
  let b : Fin n → windowTests A := fun i =>
    ⟨cellBump a δ hδ i, (cellBump_isWindowTest hδ (hcell i)).mono haA⟩
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).mp
    (LinearMap.ker_ne_bot_of_finrank_lt (f := r.comp (Fintype.linearCombination ℝ b))
      (by rw [Module.finrank_fin_fun]; omega))
  rw [LinearMap.mem_ker, LinearMap.comp_apply] at hc
  have hval : ∀ y, ((Fintype.linearCombination ℝ b c : windowTests A) : ℝ → ℝ) y =
      ∑ i, c i * cellBump a δ hδ i y := fun y => by
    rw [Fintype.linearCombination_apply, Submodule.coe_sum, Finset.sum_apply]
    rfl
  have hHa : IsWindowTest a (Fintype.linearCombination ℝ b c : windowTests A) := by
    refine ⟨(Fintype.linearCombination ℝ b c).2.contDiff, fun y hy => ?_⟩
    rw [hval]
    exact Finset.sum_eq_zero fun i _ => by
      rw [(cellBump_isWindowTest hδ (hcell i)).vanish y hy, mul_zero]
  have hQ : weilQuad (Fintype.linearCombination ℝ b c : windowTests A) = 0 := by
    rw [hr, hc, norm_zero]; ring
  exact hc0 (eq_zero_of_sum_cellBump hδ c fun y => by
    rw [← hval]; exact eq_zero_of_weilQuad_eq_zero_of_short hHa ha0 ha1 hQ y)

end GaloisForLFunctions.CohomologyOfWindowsOfSpecZ
