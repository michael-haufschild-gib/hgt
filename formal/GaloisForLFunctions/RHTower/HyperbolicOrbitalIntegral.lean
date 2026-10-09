import GaloisForLFunctions.HTGeometry.ModularCellPointPair
import GaloisForLFunctions.HTGeometry.UpperHalfPlaneStripIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The hyperbolic orbital integral

For `l > 0` let `dilSL l = diag(√l, 1/√l) ∈ SL(2,ℝ)`, acting on `ℍ` by `z ↦ lz`
(`coe_dilSL_smul`).

**Chart** (`lintegral_upperHalfPlane_eq_iterated`).  For `G : ℍ → [0,∞]` given by a measurable
`Gc` on `ℂ`, `∫ G dμ = ∫_{y>0} ∫_x y⁻² Gc(x + iy) dx dy`.

**Fundamental annulus** (`lintegral_eq_tsum_annulus`).  For `N₀ > 1` the annulus
`A = {1 ≤ |z| < N₀}` is a fundamental domain for `⟨dil N₀⟩`:
`∫_ℍ F = Σ_{m ∈ ℤ} ∫_A F(N₀^m z)`.

**Orbital integral** (`lintegral_annulus_pairU_dil`).  `u(z, Nz) = c(1 + (x/y)²)` with
`c = (N − 1)²/(4N)` (`pairU_dilSL_smul`).  Substituting `x = ty` turns `dx dy/y²` into
`dt dy/y`, and the annulus into `1/√(1+t²) ≤ y < N₀/√(1+t²)`, of logarithmic length `log N₀`.  So

`∫_A k(u(z, Nz)) dμ(z) = log N₀ · ∫_ℝ k(c(1 + t²)) dt`.

**Conjugates** (`lintegral_smul_annulus_pairU_conj`): for `γ = g · dil N · g⁻¹` the same holds on
`g • A`, by invariance of `μ` and of `u`.  **Bochner form** (`integral_annulus_pairU_dil`) for
continuous compactly supported real `k`, by splitting `k = k⁺ − k⁻`.

**Selberg's form** (`lintegral_annulus_pairU_dil_abel`).  The substitution `w = c(1 + t²)` gives the
Abel transform `∫_ℝ k(c(1+t²)) dt = c^{-1/2} ∫_c^∞ k(w)(w − c)^{-1/2} dw`
(`lintegral_comp_one_add_sq_eq_abel`), and `√c = |N^{1/2} − N^{-1/2}|/2`.  Hence
`∫_A k(u(z, Nz)) dμ = log N₀ · 2/|N^{1/2} − N^{-1/2}| · Q(c)` with `Q(c) = ∫_c^∞ k(w)(w−c)^{-1/2} dw`.
-/

open MeasureTheory Set UpperHalfPlane GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ENNReal Pointwise

namespace RHTower

noncomputable section

/-! ## The dilations -/

/-- `diag(√l, 1/√l) ∈ SL(2,ℝ)` for `l > 0`. -/
def dilSL (l : ℝ) (hl : 0 < l) : SL(2, ℝ) :=
  ⟨!![Real.sqrt l, 0; 0, (Real.sqrt l)⁻¹], by
    rw [Matrix.det_fin_two_of]
    have : Real.sqrt l ≠ 0 := (Real.sqrt_pos.2 hl).ne'
    field_simp
    ring⟩

theorem coe_dilSL_smul {l : ℝ} (hl : 0 < l) (z : ℍ) : ((dilSL l hl • z : ℍ) : ℂ) = l * z := by
  rw [coe_specialLinearGroup_apply]
  have hs : Real.sqrt l ≠ 0 := (Real.sqrt_pos.2 hl).ne'
  have hsq : ((Real.sqrt l : ℝ) : ℂ) * ((Real.sqrt l : ℝ) : ℂ) = (l : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hl.le]
  simp only [dilSL, Algebra.algebraMap_self, RingHom.id_apply, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Complex.ofReal_zero, zero_mul, add_zero, zero_add, Complex.ofReal_inv]
  have hs' : ((Real.sqrt l : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs
  field_simp
  rw [sq, hsq, mul_comm]

theorem im_dilSL_smul {l : ℝ} (hl : 0 < l) (z : ℍ) : (dilSL l hl • z).im = l * z.im := by
  rw [← UpperHalfPlane.coe_im, coe_dilSL_smul, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, UpperHalfPlane.coe_im]

/-- **The displacement of a dilation.**  `u(z, Nz) = ((N − 1)²/(4N)) (1 + (x/y)²)`. -/
theorem pairU_dilSL_smul {N : ℝ} (hN : 0 < N) (z : ℍ) :
    pairU z (dilSL N hN • z) = (N - 1) ^ 2 / (4 * N) * (1 + ((z : ℂ).re / (z : ℂ).im) ^ 2) := by
  have hy : 0 < (z : ℂ).im := z.im_pos
  rw [pairU, im_dilSL_smul, Complex.dist_eq, coe_dilSL_smul, ← UpperHalfPlane.coe_im]
  have e : (z : ℂ) - N * z = ((1 - N : ℝ) : ℂ) * z := by push_cast; ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, Complex.sq_norm,
    Complex.normSq_apply]
  field_simp
  ring

/-! ## The chart `(y, x) ↦ x + iy` for lower integrals -/

theorem stripEquiv_symm_preimage_range_coe :
    stripEquiv.symm ⁻¹' range UpperHalfPlane.coe = Ioi (0 : ℝ) ×ˢ univ := by
  ext p
  simp only [mem_preimage, stripEquiv_symm_apply, mem_prod, mem_Ioi, mem_univ, and_true]
  constructor
  · rintro ⟨z, hz⟩
    have := z.im_pos
    rw [← UpperHalfPlane.coe_im, hz] at this
    exact this
  · intro hp
    exact ⟨⟨⟨p.2, p.1⟩, hp⟩, rfl⟩

/-- **The chart for lower integrals.**  If `G z = Gc z` with `Gc` measurable on `ℂ`, then
`∫ G dμ = ∫_{y>0} ∫_x y⁻² Gc(x + iy) dx dy`. -/
theorem lintegral_upperHalfPlane_eq_iterated {G : ℍ → ℝ≥0∞} {Gc : ℂ → ℝ≥0∞}
    (hGc : Measurable Gc) (hG : ∀ z : ℍ, G z = Gc z) :
    ∫⁻ z, G z = ∫⁻ y in Ioi (0 : ℝ), ∫⁻ x : ℝ, ENNReal.ofReal ((y ^ 2)⁻¹) * Gc ⟨x, y⟩ := by
  set Fc : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal ((w.im ^ 2)⁻¹) * Gc w with hFc
  have hFcm : Measurable Fc :=
    ((Complex.continuous_im.measurable.pow_const 2).inv.ennreal_ofReal).mul hGc
  have hGm : Measurable G := by
    have : G = fun z : ℍ => Gc z := funext hG
    rw [this]; exact hGc.comp measurable_coe
  rw [volume_eq_comap_withDensity,
    lintegral_withDensity_eq_lintegral_mul _ measurable_hyperbolicDensity hGm]
  have h1 : ∀ z : ℍ, (hyperbolicDensity * G) z = Fc (z : ℂ) := by
    intro z
    simp only [Pi.mul_apply, hyperbolicDensity, hFc, hG, UpperHalfPlane.coe_im]
  simp_rw [h1]
  rw [measurePreserving_coe.lintegral_comp_emb measurableEmbedding_coe Fc]
  rw [← (measurePreserving_stripEquiv.symm).setLIntegral_comp_preimage_emb
    stripEquiv.symm.measurableEmbedding Fc (range UpperHalfPlane.coe),
    stripEquiv_symm_preimage_range_coe, Measure.volume_eq_prod, ← Measure.prod_restrict,
    Measure.restrict_univ,
    lintegral_prod (fun p => Fc (stripEquiv.symm p)) (hFcm.comp stripEquiv.symm.measurable).aemeasurable]
  rfl

/-! ## The fundamental annulus -/

/-- The annulus `{1 ≤ |z| < N₀}`. -/
def dilAnnulus (N₀ : ℝ) : Set ℍ := {z | 1 ≤ ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ < N₀}

/-- The shell `{N₀^m ≤ |z| < N₀^{m+1}}`. -/
def dilShell (N₀ : ℝ) (m : ℤ) : Set ℍ := {z | N₀ ^ m ≤ ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ < N₀ ^ (m + 1)}

theorem measurableSet_dilShell (N₀ : ℝ) (m : ℤ) : MeasurableSet (dilShell N₀ m) := by
  have hc : Continuous fun z : ℍ => ‖(z : ℂ)‖ := continuous_norm.comp continuous_coe
  exact (measurableSet_le measurable_const hc.measurable).inter
    (measurableSet_lt hc.measurable measurable_const)

theorem measurableSet_dilAnnulus (N₀ : ℝ) : MeasurableSet (dilAnnulus N₀) := by
  have hc : Continuous fun z : ℍ => ‖(z : ℂ)‖ := continuous_norm.comp continuous_coe
  exact (measurableSet_le measurable_const hc.measurable).inter
    (measurableSet_lt hc.measurable measurable_const)

theorem iUnion_dilShell {N₀ : ℝ} (hN₀ : 1 < N₀) : ⋃ m : ℤ, dilShell N₀ m = univ := by
  refine eq_univ_of_forall fun z => mem_iUnion.2 ?_
  have hpos : 0 < ‖(z : ℂ)‖ := norm_pos_iff.2 (ne_zero z)
  obtain ⟨m, hm⟩ := exists_mem_Ico_zpow hpos hN₀
  exact ⟨m, hm.1, hm.2⟩

theorem pairwise_disjoint_dilShell {N₀ : ℝ} (hN₀ : 1 < N₀) :
    Pairwise (Function.onFun Disjoint (dilShell N₀)) := by
  intro m n hmn
  rw [Function.onFun, Set.disjoint_left]
  rintro z ⟨h1, h2⟩ ⟨h3, h4⟩
  rcases lt_or_gt_of_ne hmn with h | h
  · have : N₀ ^ (m + 1) ≤ N₀ ^ n := zpow_le_zpow_right₀ hN₀.le (by omega)
    linarith
  · have : N₀ ^ (n + 1) ≤ N₀ ^ m := zpow_le_zpow_right₀ hN₀.le (by omega)
    linarith

theorem preimage_dilShell {N₀ : ℝ} (hN₀ : 1 < N₀) (m : ℤ) :
    (fun z => dilSL (N₀ ^ m) (zpow_pos (by linarith) m) • z) ⁻¹' dilShell N₀ m =
      dilAnnulus N₀ := by
  have hpos : 0 < N₀ ^ m := zpow_pos (by linarith) m
  ext z
  simp only [mem_preimage, dilShell, dilAnnulus, mem_setOf_eq, coe_dilSL_smul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, zpow_add_one₀ (by linarith : N₀ ≠ 0)]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(le_mul_iff_one_le_right hpos).1 (by linarith),
      (mul_lt_mul_iff_right₀ hpos).1 (by linarith)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith, by nlinarith⟩

theorem measurePreserving_dilSL {l : ℝ} (hl : 0 < l) :
    MeasurePreserving (fun z : ℍ => dilSL l hl • z) volume volume :=
  measurePreserving_smul ((dilSL l hl : GL (Fin 2) ℝ)) (volume : Measure ℍ)

theorem measurableEmbedding_dilSL {l : ℝ} (hl : 0 < l) :
    MeasurableEmbedding (fun z : ℍ => dilSL l hl • z) :=
  (MeasurableEquiv.smul ((dilSL l hl : GL (Fin 2) ℝ))).measurableEmbedding

/-- **The annulus is a fundamental domain for `⟨dil N₀⟩`.**
`∫_ℍ F = Σ_{m ∈ ℤ} ∫_A F(N₀^m z)`. -/
theorem lintegral_eq_tsum_annulus {N₀ : ℝ} (hN₀ : 1 < N₀) (F : ℍ → ℝ≥0∞) :
    ∫⁻ z, F z = ∑' m : ℤ, ∫⁻ z in dilAnnulus N₀,
      F (dilSL (N₀ ^ m) (zpow_pos (by linarith) m) • z) := by
  rw [← setLIntegral_univ, ← iUnion_dilShell hN₀,
    lintegral_iUnion (measurableSet_dilShell N₀) (pairwise_disjoint_dilShell hN₀)]
  refine tsum_congr fun m => ?_
  rw [← preimage_dilShell hN₀ m]
  exact ((measurePreserving_dilSL _).setLIntegral_comp_preimage_emb
    (measurableEmbedding_dilSL _) F (dilShell N₀ m)).symm

/-! ## The orbital integral -/

/-- `∫_{a}^{N₀ a} dy/y = log N₀`. -/
theorem lintegral_Ico_inv {a N₀ : ℝ} (ha : 0 < a) (hN₀ : 1 ≤ N₀) :
    ∫⁻ y in Ico a (N₀ * a), ENNReal.ofReal y⁻¹ = ENNReal.ofReal (Real.log N₀) := by
  have hb : a ≤ N₀ * a := by nlinarith
  have hint : IntegrableOn (fun y : ℝ => y⁻¹) (Icc a (N₀ * a)) := by
    refine (continuousOn_inv₀.mono fun y hy => ?_).integrableOn_compact isCompact_Icc
    exact (ha.trans_le hy.1).ne'
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.mono_set Ico_subset_Icc_self)
    ((ae_restrict_iff' measurableSet_Ico).2 (ae_of_all _ fun y hy =>
      inv_nonneg.2 (ha.trans_le hy.1).le)),
    integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb,
    integral_inv_of_pos ha (by positivity), mul_div_assoc, div_self ha.ne', mul_one]

/-- The orbital integrand in the chart. -/
def orbitalChart (k : ℝ → ℝ≥0∞) (N₀ c : ℝ) (w : ℂ) : ℝ≥0∞ :=
  (Set.indicator {w : ℂ | 1 ≤ ‖w‖ ∧ ‖w‖ < N₀} fun w => k (c * (1 + (w.re / w.im) ^ 2))) w

theorem measurable_orbitalChart {k : ℝ → ℝ≥0∞} (hk : Measurable k) (N₀ c : ℝ) :
    Measurable (orbitalChart k N₀ c) := by
  refine Measurable.indicator ?_ ?_
  · exact hk.comp (measurable_const.mul (measurable_const.add
      ((Complex.measurable_re.div Complex.measurable_im).pow_const 2)))
  · exact (measurableSet_le measurable_const continuous_norm.measurable).inter
      (measurableSet_lt continuous_norm.measurable measurable_const)

/-- In the chart the scaled orbital integrand is `1[1 ≤ y√(1+t²) < N₀] k(c(1+t²))`. -/
theorem orbitalChart_mul {k : ℝ → ℝ≥0∞} {N₀ c y : ℝ} (hy : 0 < y) (t : ℝ) :
    orbitalChart k N₀ c ⟨y * t, y⟩ =
      (Set.indicator (Ico (1 / Real.sqrt (1 + t ^ 2)) (N₀ / Real.sqrt (1 + t ^ 2)))
        (fun _ => k (c * (1 + t ^ 2)))) y := by
  have hs : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hnorm : ‖(⟨y * t, y⟩ : ℂ)‖ = y * Real.sqrt (1 + t ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_mk,
      show y * t * (y * t) + y * y = y ^ 2 * (1 + t ^ 2) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hy.le]
  have hq : y * t / y = t := by field_simp
  simp only [orbitalChart, Set.indicator, mem_setOf_eq, hnorm, mem_Ico, hq]
  congr 1
  apply propext
  rw [div_le_iff₀ hs, lt_div_iff₀ hs]

/-- **The orbital integral of a dilation.**  For measurable `k ≥ 0`, `N > 0` and `N₀ > 1`,
`∫_A k(u(z, Nz)) dμ(z) = log N₀ · ∫_ℝ k(((N − 1)²/(4N))(1 + t²)) dt`. -/
theorem lintegral_annulus_pairU_dil {k : ℝ → ℝ≥0∞} (hk : Measurable k) {N : ℝ} (hN : 0 < N)
    {N₀ : ℝ} (hN₀ : 1 < N₀) :
    ∫⁻ z in dilAnnulus N₀, k (pairU z (dilSL N hN • z)) =
      ENNReal.ofReal (Real.log N₀) * ∫⁻ t : ℝ, k ((N - 1) ^ 2 / (4 * N) * (1 + t ^ 2)) := by
  set c := (N - 1) ^ 2 / (4 * N) with hc
  rw [← lintegral_indicator (measurableSet_dilAnnulus N₀)]
  rw [lintegral_upperHalfPlane_eq_iterated (Gc := orbitalChart k N₀ c)
    (measurable_orbitalChart hk N₀ c) (fun z => ?_)]
  swap
  · simp only [Set.indicator, dilAnnulus, orbitalChart, mem_setOf_eq, pairU_dilSL_smul, ← hc]
  -- substitute `x = y t` in the inner integral
  have hinner : ∀ y ∈ Ioi (0 : ℝ), ∫⁻ x : ℝ, ENNReal.ofReal ((y ^ 2)⁻¹) * orbitalChart k N₀ c ⟨x, y⟩ =
      ∫⁻ t : ℝ, ENNReal.ofReal y⁻¹ * (Set.indicator
        (Ico (1 / Real.sqrt (1 + t ^ 2)) (N₀ / Real.sqrt (1 + t ^ 2)))
        (fun _ => k (c * (1 + t ^ 2)))) y := by
    intro y hy
    have hy : (0 : ℝ) < y := hy
    have hmeas : Measurable fun x : ℝ =>
        ENNReal.ofReal ((y ^ 2)⁻¹) * orbitalChart k N₀ c ⟨x, y⟩ :=
      measurable_const.mul ((measurable_orbitalChart hk N₀ c).comp
        (Complex.measurableEquivRealProd.symm.measurable.comp
          (measurable_id.prodMk measurable_const)))
    have hmap := Real.map_volume_mul_left hy.ne'
    have h1 : ∫⁻ t : ℝ, ENNReal.ofReal ((y ^ 2)⁻¹) * orbitalChart k N₀ c ⟨y * t, y⟩ =
        ENNReal.ofReal |y⁻¹| * ∫⁻ x : ℝ, ENNReal.ofReal ((y ^ 2)⁻¹) * orbitalChart k N₀ c ⟨x, y⟩ := by
      rw [← lintegral_map hmeas (measurable_const_mul y), hmap, lintegral_smul_measure, smul_eq_mul]
    rw [abs_of_pos (inv_pos.2 hy)] at h1
    have hne : ENNReal.ofReal y⁻¹ ≠ 0 := by simpa using hy
    have h2 : ∫⁻ x : ℝ, ENNReal.ofReal ((y ^ 2)⁻¹) * orbitalChart k N₀ c ⟨x, y⟩ =
        ENNReal.ofReal y * ∫⁻ t : ℝ, ENNReal.ofReal ((y ^ 2)⁻¹) * orbitalChart k N₀ c ⟨y * t, y⟩ := by
      rw [h1, ← mul_assoc, ← ENNReal.ofReal_mul hy.le, mul_inv_cancel₀ hy.ne', ENNReal.ofReal_one,
        one_mul]
    rw [h2, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun t => ?_
    rw [orbitalChart_mul hy, ← mul_assoc, ← ENNReal.ofReal_mul hy.le]
    congr 2
    field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioi hinner]
  -- swap the order of integration
  have hH : Measurable (Function.uncurry fun (y t : ℝ) => ENNReal.ofReal y⁻¹ * (Set.indicator
      (Ico (1 / Real.sqrt (1 + t ^ 2)) (N₀ / Real.sqrt (1 + t ^ 2)))
      (fun _ => k (c * (1 + t ^ 2)))) y) := by
    have hset : MeasurableSet {p : ℝ × ℝ | 1 / Real.sqrt (1 + p.2 ^ 2) ≤ p.1 ∧
        p.1 < N₀ / Real.sqrt (1 + p.2 ^ 2)} :=
      (measurableSet_le (by fun_prop) measurable_fst).inter
        (measurableSet_lt measurable_fst (by fun_prop))
    have hk' : Measurable fun p : ℝ × ℝ => k (c * (1 + p.2 ^ 2)) := hk.comp (by fun_prop)
    have : (Function.uncurry fun (y t : ℝ) => ENNReal.ofReal y⁻¹ * (Set.indicator
        (Ico (1 / Real.sqrt (1 + t ^ 2)) (N₀ / Real.sqrt (1 + t ^ 2)))
        (fun _ => k (c * (1 + t ^ 2)))) y) = fun p => ENNReal.ofReal p.1⁻¹ *
          Set.indicator {p : ℝ × ℝ | 1 / Real.sqrt (1 + p.2 ^ 2) ≤ p.1 ∧
            p.1 < N₀ / Real.sqrt (1 + p.2 ^ 2)} (fun p => k (c * (1 + p.2 ^ 2))) p := by
      funext p
      simp only [Function.uncurry, Set.indicator, mem_Ico, mem_setOf_eq]
    rw [this]
    exact (measurable_fst.inv.ennreal_ofReal).mul (hk'.indicator hset)
  rw [lintegral_lintegral_swap hH.aemeasurable, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun t => ?_
  have hs : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hsub : Ico (1 / Real.sqrt (1 + t ^ 2)) (N₀ / Real.sqrt (1 + t ^ 2)) ⊆ Ioi 0 :=
    fun y hy => lt_of_lt_of_le (by positivity) hy.1
  set S := Ico (1 / Real.sqrt (1 + t ^ 2)) (N₀ / Real.sqrt (1 + t ^ 2)) with hS
  set K := k (c * (1 + t ^ 2))
  have e : (fun y => ENNReal.ofReal y⁻¹ * S.indicator (fun _ => K) y) =
      S.indicator (fun y => ENNReal.ofReal y⁻¹ * K) := by
    funext y
    simp only [Set.indicator]
    split_ifs <;> simp
  rw [e, setLIntegral_indicator measurableSet_Ico, inter_eq_left.2 hsub,
    lintegral_mul_const _ measurable_inv.ennreal_ofReal, hS,
    show N₀ / Real.sqrt (1 + t ^ 2) = N₀ * (1 / Real.sqrt (1 + t ^ 2)) by ring,
    lintegral_Ico_inv (by positivity) hN₀.le]


/-! ## Conjugates of a dilation -/

/-- **Hyperbolic conjugates.**  For `γ = g · dil N · g⁻¹`,
`∫_{g•A} k(u(z, γz)) dμ(z) = log N₀ · ∫_ℝ k(((N − 1)²/(4N))(1 + t²)) dt`. -/
theorem lintegral_smul_annulus_pairU_conj {k : ℝ → ℝ≥0∞} (hk : Measurable k) {N : ℝ} (hN : 0 < N)
    {N₀ : ℝ} (hN₀ : 1 < N₀) (g : SL(2, ℝ)) :
    ∫⁻ z in g • dilAnnulus N₀, k (pairU z ((g * dilSL N hN * g⁻¹) • z)) =
      ENNReal.ofReal (Real.log N₀) * ∫⁻ t : ℝ, k ((N - 1) ^ 2 / (4 * N) * (1 + t ^ 2)) := by
  have hmp : MeasurePreserving (fun z : ℍ => g • z) volume volume :=
    measurePreserving_smul ((g : GL (Fin 2) ℝ)) (volume : Measure ℍ)
  have hme : MeasurableEmbedding (fun z : ℍ => g • z) :=
    (MeasurableEquiv.smul ((g : GL (Fin 2) ℝ))).measurableEmbedding
  have hpre : (fun z : ℍ => g • z) ⁻¹' (g • dilAnnulus N₀) = dilAnnulus N₀ := by
    ext w
    simp only [mem_preimage, Set.smul_mem_smul_set_iff]
  rw [← hmp.setLIntegral_comp_preimage_emb hme, hpre, ← lintegral_annulus_pairU_dil hk hN hN₀]
  refine lintegral_congr fun w => ?_
  rw [mul_smul, mul_smul, inv_smul_smul, pairU_smul]

/-! ## The Bochner form -/

theorem hasCompactSupport_comp_one_add_sq {k : ℝ → ℝ} (hks : HasCompactSupport k) {c : ℝ}
    (hc : 0 < c) : HasCompactSupport fun t : ℝ => k (c * (1 + t ^ 2)) := by
  obtain ⟨R, hR⟩ := hks.isCompact.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (Real.sqrt (|R| / c))) fun t ht => ?_
  by_contra hne
  have hmem : c * (1 + t ^ 2) ∈ Metric.closedBall (0 : ℝ) R :=
    hR (subset_tsupport _ (Function.mem_support.2 hne))
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs,
    abs_of_pos (by positivity)] at hmem
  apply ht
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  apply Real.abs_le_sqrt
  rw [le_div_iff₀ hc]
  nlinarith [le_abs_self R]

/-- **The orbital integral, Bochner form.**  For continuous compactly supported real `k`,
`N > 0`, `N ≠ 1` and `N₀ > 1`, `∫_A k(u(z, Nz)) dμ(z) = log N₀ · ∫_ℝ k(((N−1)²/(4N))(1 + t²)) dt`. -/
theorem integral_annulus_pairU_dil {k : ℝ → ℝ} (hk : Continuous k) (hks : HasCompactSupport k)
    {N : ℝ} (hN : 0 < N) (hN1 : N ≠ 1) {N₀ : ℝ} (hN₀ : 1 < N₀) :
    ∫ z in dilAnnulus N₀, k (pairU z (dilSL N hN • z)) =
      Real.log N₀ * ∫ t : ℝ, k ((N - 1) ^ 2 / (4 * N) * (1 + t ^ 2)) := by
  set c := (N - 1) ^ 2 / (4 * N) with hc
  have hcpos : 0 < c := by
    have : 0 < (N - 1) ^ 2 := by
      have : N - 1 ≠ 0 := sub_ne_zero.2 hN1
      positivity
    positivity
  set f : ℝ → ℝ := fun t => k (c * (1 + t ^ 2)) with hf
  have hfc : Continuous f := hk.comp (by fun_prop)
  have hfi : Integrable f := hfc.integrable_of_hasCompactSupport
    (hasCompactSupport_comp_one_add_sq hks hcpos)
  set φ : ℍ → ℝ := fun z => k (pairU z (dilSL N hN • z)) with hφ
  have hφeq : φ = fun z : ℍ => k (c * (1 + ((z : ℂ).re / (z : ℂ).im) ^ 2)) := by
    funext z; simp only [hφ]; rw [pairU_dilSL_smul]
  have hφc : Continuous φ := by
    rw [hφeq]
    refine hk.comp (continuous_const.mul (continuous_const.add (Continuous.pow ?_ 2)))
    exact (Complex.continuous_re.comp continuous_coe).div (Complex.continuous_im.comp continuous_coe)
      fun z => z.im_pos.ne'
  have hmk : ∀ g : ℝ → ℝ, Continuous g → Measurable fun x => ENNReal.ofReal (g x) :=
    fun g hg => hg.measurable.ennreal_ofReal
  -- integrability on the annulus
  have hφi : IntegrableOn φ (dilAnnulus N₀) := by
    refine ⟨hφc.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    have h := lintegral_annulus_pairU_dil (k := fun x => ENNReal.ofReal |k x|)
      (hmk _ (continuous_abs.comp hk)) hN hN₀
    simp only [Real.enorm_eq_ofReal_abs]
    rw [h, ← hc]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    have := hfi.hasFiniteIntegral
    rw [HasFiniteIntegral] at this
    simpa only [Real.enorm_eq_ofReal_abs, hf] using this
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hφi,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi]
  have hpos := lintegral_annulus_pairU_dil (k := fun x => ENNReal.ofReal (k x)) (hmk _ hk) hN hN₀
  have hneg := lintegral_annulus_pairU_dil (k := fun x => ENNReal.ofReal (-k x))
    (hmk _ hk.neg) hN hN₀
  simp only [hφ]
  rw [hpos, hneg, ← hc, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.log_nonneg hN₀.le)]
  ring


/-! ## The Abel-transform form -/

/-- An even integrand integrates to twice its integral over `(0, ∞)`. -/
theorem lintegral_even_eq_two_mul {h : ℝ → ℝ≥0∞} (heven : ∀ t, h (-t) = h t) :
    ∫⁻ t : ℝ, h t = 2 * ∫⁻ t in Ioi (0 : ℝ), h t := by
  have hsplit := lintegral_add_compl (μ := volume) h (measurableSet_Ioi (a := (0 : ℝ)))
  rw [compl_Ioi] at hsplit
  have hIic : ∫⁻ t in Iic (0 : ℝ), h t = ∫⁻ t in Iio (0 : ℝ), h t :=
    setLIntegral_congr Iio_ae_eq_Iic.symm
  have himage : (fun t : ℝ => -t) '' Ioi 0 = Iio 0 := by
    ext t; simp
  have hcov := lintegral_image_eq_lintegral_abs_deriv_mul (measurableSet_Ioi (a := (0 : ℝ)))
    (f := fun t : ℝ => -t) (f' := fun _ => -1)
    (fun t _ => (hasDerivAt_neg t).hasDerivWithinAt) (neg_injective.injOn) h
  rw [himage] at hcov
  simp only [abs_neg, abs_one, ENNReal.ofReal_one, one_mul, heven] at hcov
  rw [← hsplit, hIic, hcov, two_mul]

/-- **Abel transform.**  For `c > 0`,
`∫_ℝ k(c(1 + t²)) dt = c^{-1/2} ∫_c^∞ k(w) (w − c)^{-1/2} dw`. -/
theorem lintegral_comp_one_add_sq_eq_abel {k : ℝ → ℝ≥0∞} {c : ℝ} (hc : 0 < c) :
    ∫⁻ t : ℝ, k (c * (1 + t ^ 2)) =
      ENNReal.ofReal (Real.sqrt c)⁻¹ *
        ∫⁻ w in Ioi c, k w * ENNReal.ofReal (Real.sqrt (w - c))⁻¹ := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have himage : (fun t : ℝ => c * (1 + t ^ 2)) '' Ioi 0 = Ioi c := by
    ext w
    constructor
    · rintro ⟨t, ht, rfl⟩
      have : (0 : ℝ) < t := ht
      show c < c * (1 + t ^ 2)
      nlinarith [mul_pos hc (pow_pos this 2)]
    · intro hw
      have hw : c < w := hw
      refine ⟨Real.sqrt ((w - c) / c), Real.sqrt_pos.2 (div_pos (by linarith) hc), ?_⟩
      show c * (1 + Real.sqrt ((w - c) / c) ^ 2) = w
      rw [Real.sq_sqrt (div_pos (by linarith) hc).le]
      field_simp
      ring
  have hinj : InjOn (fun t : ℝ => c * (1 + t ^ 2)) (Ioi 0) := by
    intro t ht t' ht' h
    have ht : (0 : ℝ) < t := ht
    have ht' : (0 : ℝ) < t' := ht'
    have h2 : t ^ 2 = t' ^ 2 := by
      have := mul_left_cancel₀ hc.ne' h
      linarith
    exact (pow_left_inj₀ ht.le ht'.le two_ne_zero).1 h2
  have hcov := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (f := fun t : ℝ => c * (1 + t ^ 2)) (f' := fun t => 2 * c * t)
    (fun t _ => by
      have := ((hasDerivAt_pow 2 t).const_add 1).const_mul c
      exact (this.congr_deriv (by simp; ring)).hasDerivWithinAt)
    hinj (fun w => k w * ENNReal.ofReal (Real.sqrt (w - c))⁻¹)
  rw [himage] at hcov
  rw [hcov]
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ENNReal.ofReal |2 * c * t| *
      (k (c * (1 + t ^ 2)) * ENNReal.ofReal (Real.sqrt (c * (1 + t ^ 2) - c))⁻¹) =
      ENNReal.ofReal (2 * Real.sqrt c) * k (c * (1 + t ^ 2)) := by
    intro t ht
    have ht : (0 : ℝ) < t := ht
    have hsq : Real.sqrt (c * (1 + t ^ 2) - c) = Real.sqrt c * t := by
      rw [show c * (1 + t ^ 2) - c = c * t ^ 2 by ring, Real.sqrt_mul hc.le, Real.sqrt_sq ht.le]
    rw [hsq, abs_of_pos (by positivity), mul_comm (k _), ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    have hc' : c = Real.sqrt c * Real.sqrt c := (Real.mul_self_sqrt hc.le).symm
    calc 2 * c * t * (Real.sqrt c * t)⁻¹
        = 2 * (Real.sqrt c * Real.sqrt c) * t * (Real.sqrt c * t)⁻¹ := by rw [← hc']
      _ = 2 * Real.sqrt c := by field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    show (Real.sqrt c)⁻¹ * (2 * Real.sqrt c) = 2 by field_simp, ENNReal.ofReal_ofNat]
  exact lintegral_even_eq_two_mul fun t => by rw [neg_sq]

theorem sqrt_dil_const {N : ℝ} (hN : 0 < N) :
    Real.sqrt ((N - 1) ^ 2 / (4 * N)) = |Real.sqrt N - (Real.sqrt N)⁻¹| / 2 := by
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have e : (N - 1) ^ 2 / (4 * N) = ((Real.sqrt N - (Real.sqrt N)⁻¹) / 2) ^ 2 := by
    rw [show (N - 1) ^ 2 / (4 * N) = (Real.sqrt N ^ 2 - 1) ^ 2 / (4 * Real.sqrt N ^ 2) by
      rw [Real.sq_sqrt hN.le]]
    field_simp
    ring
  rw [e, Real.sqrt_sq_eq_abs, abs_div, abs_two]

/-- **The orbital integral in Selberg's form.**  With `c = (N − 1)²/(4N)` and
`√c = |N^{1/2} − N^{-1/2}|/2`,
`∫_A k(u(z, Nz)) dμ = log N₀ · (2/|N^{1/2} − N^{-1/2}|) · ∫_c^∞ k(w)(w − c)^{-1/2} dw`. -/
theorem lintegral_annulus_pairU_dil_abel {k : ℝ → ℝ≥0∞} (hk : Measurable k) {N : ℝ} (hN : 0 < N)
    (hN1 : N ≠ 1) {N₀ : ℝ} (hN₀ : 1 < N₀) :
    ∫⁻ z in dilAnnulus N₀, k (pairU z (dilSL N hN • z)) =
      ENNReal.ofReal (Real.log N₀) * ENNReal.ofReal (2 / |Real.sqrt N - (Real.sqrt N)⁻¹|) *
        ∫⁻ w in Ioi ((N - 1) ^ 2 / (4 * N)), k w *
          ENNReal.ofReal (Real.sqrt (w - (N - 1) ^ 2 / (4 * N)))⁻¹ := by
  have hc : 0 < (N - 1) ^ 2 / (4 * N) := by
    have : N - 1 ≠ 0 := sub_ne_zero.2 hN1
    positivity
  rw [lintegral_annulus_pairU_dil hk hN hN₀, lintegral_comp_one_add_sq_eq_abel hc, sqrt_dil_const hN,
    mul_assoc]
  congr 3
  rw [inv_div]

end

end RHTower
