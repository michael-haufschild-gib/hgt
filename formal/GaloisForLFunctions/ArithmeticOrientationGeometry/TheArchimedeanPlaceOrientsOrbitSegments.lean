import GaloisForLFunctions.ArithmeticOrientationGeometry.TheOrientationOfACycle
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHodgeIndexOfZetaHoldsAwayFromLowFrequencies
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheTowerDefectCountsTheFrobeniusEigenvalues

/-!
# The archimedean place orients orbit segments

Arithmetic Castelnuovo–Severi proves that Weil's form of `ζ` is nonnegative on every test of
aperture `a` whose transform vanishes at the pole `i/2` and on an explicit finite grid `D_a` of low
frequencies (`re_W_zeta_nonneg_of_lowGrid`): the archimedean collar pays everything above the
horizon `T(a)`. Read on orbits this becomes an unconditional orientation theorem.

* **Orbit segments of low-blind cycles are oriented** (`orbitSegment_defect_nonneg_of_lowBlind`).
  Let `f` be supported in `[−a, a]` with transform vanishing at the pole and on the grid of the
  larger aperture `a + T/2`. Then the defect is nonnegative on every combination of the
  translates `f(· − s)`, `0 ≤ s ≤ T`: the orbit of `f` has the Hodge index on the scale segment
  `[0, T]`. Translation multiplies the transform by an exponential, so every combination keeps the
  zeros of `h_f` (`paperFT_orbitTest`); recentring by `T/2` puts it in aperture `a + T/2`, and Weil's
  form is translation invariant.
* **Hasse–Weil along the segment** (`hasseWeilAt_of_lowBlind`): such a cycle satisfies
  `|W(f, f(· − t))| ≤ W(f, f)` for every `|t| ≤ T`, unconditionally.
* **The cost of orientation.** Orienting a segment of length `T` costs one linear condition at the
  pole and one per point of the grid `D_{a + T/2}`, whose size grows doubly exponentially in
  `T`; no nonzero cycle meets all of them (`eq_zero_of_lowBlind_forall`): a test whose transform
  vanishes on the grids of every aperture is zero, since the grids become dense in `ℝ`.

So the archimedean place orients every finite orbit segment of a sufficiently blind cycle, and no
cycle along its whole orbit; the remaining orientation of a cycle is decided by its zeros
(`zeta_orientation_iff`).
-/

noncomputable section

open Complex Finset Set
open scoped ComplexConjugate
open Zeta23

namespace GaloisForLFunctions.ArithmeticOrientationGeometry

open ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.SquareRootThreshold (temperedConfig_zetaZeroConfig)

/-- A real test vanishes outside the closed interval containing its topological support. -/
theorem eq_zero_of_not_mem_Icc {f : ℝ → ℝ} {a b : ℝ} (hfs : tsupport f ⊆ Icc a b) {u : ℝ}
    (hu : u ∉ Icc a b) : f u = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hu (hfs h)

/-- The recentred orbit combination `u ↦ Σ_s c_s f(u + T/2 − s)`. -/
def recentredOrbit (T : ℝ) (f : ℝ → ℝ) (S : Finset ℝ) (c : ℝ → ℝ) : ℝ → ℝ :=
  scaleShift (-(T / 2)) (∑ s ∈ S, c s • scaleShift s f)

theorem recentredOrbit_support {a T : ℝ} {f : ℝ → ℝ} (hfs : tsupport f ⊆ Icc (-a) a)
    {S : Finset ℝ} (hS : ∀ s ∈ S, s ∈ Icc 0 T) (c : ℝ → ℝ) :
    tsupport (cx (recentredOrbit T f S c)) ⊆ Icc (-(a + T / 2)) (a + T / 2) := by
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  by_contra hnot
  apply hu
  simp only [cx, recentredOrbit, scaleShift_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Complex.ofReal_eq_zero]
  refine Finset.sum_eq_zero fun s hs => ?_
  have hs' := hS s hs
  rw [eq_zero_of_not_mem_Icc hfs, mul_zero]
  intro hmem
  apply hnot
  constructor <;> linarith [hmem.1, hmem.2, hs'.1, hs'.2]

theorem recentredOrbit_mem {f : ℝ → ℝ} (hf : f ∈ realTests) (T : ℝ) (S : Finset ℝ) (c : ℝ → ℝ) :
    recentredOrbit T f S c ∈ realTests :=
  scaleShift_mem _ (Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (scaleShift_mem s hf))

/-- The recentred combination has transform `e^{−iTz/2} P(z) h_f(z)`; it keeps every zero of `h_f`. -/
theorem paperFT_recentredOrbit_eq_zero {f : ℝ → ℝ} (hf : f ∈ realTests) (T : ℝ) (S : Finset ℝ)
    (c : ℝ → ℝ) {z : ℂ} (hz : paperFT (cx f) z = 0) :
    paperFT (cx (recentredOrbit T f S c)) z = 0 := by
  rw [recentredOrbit, paperFT_cx_scaleShift_apply, paperFT_orbitTest hf, hz, mul_zero, mul_zero]

/-- The zero-side Weil form of `ζ` on the recentred combination is that of the combination. -/
theorem configWeil_recentredOrbit (T : ℝ) (f : ℝ → ℝ) (S : Finset ℝ) (c : ℝ → ℝ) :
    configWeil zetaZeroConfig (recentredOrbit T f S c) (recentredOrbit T f S c) =
      configWeil zetaZeroConfig (∑ s ∈ S, c s • scaleShift s f) (∑ s ∈ S, c s • scaleShift s f) :=
  configWeil_scaleShift_same _ _ _ _

/-- **The archimedean place orients orbit segments.** If `f` is supported in `[−a, a]` and its
transform vanishes at the pole and on the low-frequency grid of aperture `a + T/2`, the defect is
nonnegative on every combination of translates `f(· − s)` with `0 ≤ s ≤ T`. -/
theorem orbitSegment_defect_nonneg_of_lowBlind {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) {f : ℝ → ℝ}
    (hf : f ∈ realTests) (hfs : tsupport f ⊆ Icc (-a) a) (hp : paperFT (cx f) (I / 2) = 0)
    (hgrid : ∀ j ∈ lowGrid (a + T / 2),
      paperFT (cx f) (((j : ℝ) * gridStep (a + T / 2) : ℝ) : ℂ) = 0)
    (S : Finset ℝ) (hS : ∀ s ∈ S, s ∈ Icc 0 T) (c : ℝ → ℝ) :
    0 ≤ zetaScalingDatum.defect (zetaScalingDatum.orbitComb (0, 0, ⟨f, hf⟩) S c)
      (zetaScalingDatum.orbitComb (0, 0, ⟨f, hf⟩) S c) := by
  have hdef : zetaScalingDatum.defect (zetaScalingDatum.orbitComb (0, 0, ⟨f, hf⟩) S c)
      (zetaScalingDatum.orbitComb (0, 0, ⟨f, hf⟩) S c) =
      configWeil zetaZeroConfig (∑ s ∈ S, c s • scaleShift s f)
        (∑ s ∈ S, c s • scaleShift s f) := by
    have h := configSurface_defect zetaZeroConfig temperedConfig_zetaZeroConfig
      (zetaScalingDatum.orbitComb (0, 0, ⟨f, hf⟩) S c)
      (zetaScalingDatum.orbitComb (0, 0, ⟨f, hf⟩) S c)
    rw [configSurface_zeta_eq] at h
    rw [show zetaScalingDatum.defect = scalingSurface.defect from rfl, h]
    have ht := orbitComb_test zetaZeroConfig temperedConfig_zetaZeroConfig (0, 0, ⟨f, hf⟩) S c
    exact congrArg₂ (configWeil zetaZeroConfig) ht ht
  rw [hdef, ← configWeil_recentredOrbit T]
  have hmem := recentredOrbit_mem hf T S c
  exact re_W_zeta_nonneg_of_lowGrid (by linarith) (cx_contDiff hmem.1)
    (recentredOrbit_support hfs hS c) (paperFT_recentredOrbit_eq_zero hf T S c hp)
    fun j hj => paperFT_recentredOrbit_eq_zero hf T S c (hgrid j hj)

/-- **Hasse–Weil along the segment.** A cycle blind to the pole and to the grid of aperture
`a + T/2` satisfies the Hasse–Weil bound at every scale `|t| ≤ T`. -/
theorem hasseWeilAt_of_lowBlind {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) {f : ℝ → ℝ}
    (hf : f ∈ realTests) (hfs : tsupport f ⊆ Icc (-a) a) (hp : paperFT (cx f) (I / 2) = 0)
    (hgrid : ∀ j ∈ lowGrid (a + T / 2),
      paperFT (cx f) (((j : ℝ) * gridStep (a + T / 2) : ℝ) : ℂ) = 0)
    {t : ℝ} (ht : |t| ≤ T) : zetaScalingDatum.HasseWeilAt (0, 0, ⟨f, hf⟩) t := by
  classical
  have key : ∀ s : ℝ, 0 ≤ s → s ≤ T → zetaScalingDatum.HasseWeilAt (0, 0, ⟨f, hf⟩) s := by
    intro s hs0 hsT
    rw [ScalingDatum.hasseWeilAt_iff_defect_nonneg_weilPlane]
    intro r u
    by_cases hs : s = 0
    · subst hs
      rw [zetaScalingDatum.act_zero, ← add_smul]
      have := orbitSegment_defect_nonneg_of_lowBlind ha hT hf hfs hp hgrid {0}
        (fun x hx => by rw [Finset.mem_singleton.mp hx]; exact ⟨le_rfl, hT⟩) (fun _ => r + u)
      simpa [ScalingDatum.orbitComb, zetaScalingDatum.act_zero] using this
    · have h := orbitSegment_defect_nonneg_of_lowBlind ha hT hf hfs hp hgrid {s, 0}
        (fun x hx => by
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact ⟨hs0, hsT⟩
          · rw [Finset.mem_singleton.mp hx]; exact ⟨le_rfl, hT⟩)
        (fun k => if k = s then r else u)
      have hne : (0 : ℝ) ≠ s := fun h0 => hs h0.symm
      simpa [ScalingDatum.orbitComb, Finset.sum_insert, hne, Ne.symm hne,
        zetaScalingDatum.act_zero] using h
  rcases le_or_gt 0 t with h0 | h0
  · exact key t h0 (le_of_abs_le ht)
  · have := key (-t) (by linarith) (by rw [abs_of_neg h0] at ht; exact ht)
    rwa [ScalingDatum.HasseWeilAt, zetaScalingDatum.orbitCorr_neg] at this

/-! ### No cycle is low-blind at every aperture -/

/-- The archimedean horizon grows at least linearly: `a ≤ T(a)`, and `T(a) ≥ 1`. -/
theorem le_horizonFreq {a : ℝ} (ha : 0 ≤ a) : a ≤ horizonFreq a ∧ 1 ≤ horizonFreq a := by
  unfold horizonFreq RHTower.horizonExponent
  have hs : Real.sqrt (Real.exp (2 * a)) = Real.exp a := by
    rw [show 2 * a = a + a by ring, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos a).le]
  rw [hs]
  have h1 : a + 1 ≤ Real.exp a := Real.add_one_le_exp a
  have h2 := Real.add_one_le_exp (2 * (10 + 68 * Real.exp a))
  constructor <;> nlinarith [Real.exp_pos a]

/-- The grid step shrinks: `h(a) ≤ 1/(a + 1)`. -/
theorem gridStep_le {a : ℝ} (ha : 0 ≤ a) : gridStep a ≤ 1 / (a + 1) := by
  have hT := (le_horizonFreq ha).2
  unfold gridStep gridStepOf
  apply one_div_le_one_div_of_le (by linarith)
  have hroot : (a + 1) / 2 ≤ Real.sqrt (horizonFreq a * (a + 1) ^ 3) := by
    apply Real.le_sqrt_of_sq_le
    have : (a + 1) ^ 2 / 4 ≤ (a + 1) ^ 3 := by nlinarith [sq_nonneg (a + 1)]
    nlinarith [pow_pos (show (0 : ℝ) < a + 1 by linarith) 3]
  linarith

/-- **No nonzero cycle is low-blind at every aperture.** If the transform of `f` vanishes on the
low-frequency grids of all apertures `b ≥ a₀`, then `f = 0`: the grids become dense in `ℝ`. -/
theorem eq_zero_of_lowBlind_forall {f : ℝ → ℝ} (hf : f ∈ realTests) {a₀ : ℝ}
    (h : ∀ b, a₀ ≤ b → ∀ j ∈ lowGrid b, paperFT (cx f) (((j : ℝ) * gridStep b : ℝ) : ℂ) = 0) :
    ∀ u, f u = 0 := by
  have hcont : Continuous fun r : ℝ => paperFT (cx f) r :=
    RHTower.WeilOneSided.continuous_paperFT_real_arg
      ((cx_contDiff hf.1).continuous.integrable_of_hasCompactSupport (cx_hasCompactSupport hf.2))
  have hzero : ∀ x : ℝ, paperFT (cx f) x = 0 := by
    intro x
    by_contra hx
    obtain ⟨δ, hδ, hne⟩ := Metric.eventually_nhds_iff.mp (hcont.continuousAt.eventually_ne hx)
    set b := max (max a₀ 0) (max (2 * |x|) (1 / δ)) + 1 with hb
    have hb0 : 0 ≤ b := by rw [hb]; linarith [le_max_right a₀ 0, le_max_left (max a₀ 0) (max (2 * |x|) (1 / δ))]
    have hba : a₀ ≤ b := by rw [hb]; linarith [le_max_left a₀ 0, le_max_left (max a₀ 0) (max (2 * |x|) (1 / δ))]
    have hbx : 2 * |x| ≤ b := by
      rw [hb]; linarith [le_max_left (2 * |x|) (1 / δ), le_max_right (max a₀ 0) (max (2 * |x|) (1 / δ))]
    have hbδ : 1 / δ < b + 1 := by
      rw [hb]; linarith [le_max_right (2 * |x|) (1 / δ), le_max_right (max a₀ 0) (max (2 * |x|) (1 / δ))]
    obtain ⟨hTb, hT1⟩ := le_horizonFreq hb0
    set T := horizonFreq b with hTdef
    set hs := gridStep b with hsdef
    have hs0 : 0 < hs := gridStepOf_pos _ _
    have hs1 : hs ≤ 1 / (b + 1) := gridStep_le hb0
    have hsδ : hs < δ := by
      refine lt_of_le_of_lt hs1 ?_
      rw [div_lt_iff₀ (by linarith)]
      rw [div_lt_iff₀ hδ] at hbδ
      linarith
    set j : ℤ := ⌊x / hs⌋ with hj
    have hj1 : (j : ℝ) ≤ x / hs := Int.floor_le _
    have hj2 : x / hs < j + 1 := Int.lt_floor_add_one _
    have hdist : dist ((j : ℝ) * hs) x < δ := by
      rw [Real.dist_eq, abs_lt]
      have e1 : (j : ℝ) * hs ≤ x := by rwa [le_div_iff₀ hs0] at hj1
      have e2 : x < ((j : ℝ) + 1) * hs := by rwa [div_lt_iff₀ hs0] at hj2
      constructor <;> nlinarith
    have hmem : j ∈ lowGrid b := by
      have hxT : |x| ≤ T / 2 := by linarith
      have hTh : T / hs ≤ (gridHalfOf T b : ℝ) := Nat.le_ceil _
      have hxl : -(T / 2) / hs ≤ x / hs := div_le_div_of_nonneg_right (by linarith [neg_abs_le x]) hs0.le
      have hxu : x / hs ≤ T / hs := div_le_div_of_nonneg_right (by linarith [le_abs_self x]) hs0.le
      have h2 : 1 ≤ T / (2 * hs) := by
        rw [le_div_iff₀ (by positivity)]
        have hb1 : 1 ≤ b := by
          rw [hb]; linarith [le_max_right a₀ 0, le_max_left (max a₀ 0) (max (2 * |x|) (1 / δ))]
        have hb2 : 1 / (b + 1) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
        linarith
      simp only [lowGrid, lowGridOf, Finset.mem_Icc]
      constructor
      · have hlow : -(T / hs) ≤ (j : ℝ) := by
          have h3 := Int.sub_one_lt_floor (x / hs)
          rw [← hj] at h3
          have e : -(T / 2) / hs = -(T / (2 * hs)) := by field_simp [hs0.ne']
          have e2 : T / hs = 2 * (T / (2 * hs)) := by field_simp [hs0.ne']
          rw [e] at hxl
          rw [e2]
          linarith
        have : (-(gridHalfOf T b : ℝ)) ≤ (j : ℝ) := by linarith
        exact_mod_cast this
      · have : (j : ℝ) ≤ (gridHalfOf T b : ℝ) := hj1.trans (hxu.trans hTh)
        exact_mod_cast this
    exact hne hdist (h b hba j hmem)
  intro u
  have := eq_zero_of_paperFT_real_eq_zero (cx_contDiff hf.1).continuous (cx_hasCompactSupport hf.2)
    hzero u
  simpa [cx] using this

end GaloisForLFunctions.ArithmeticOrientationGeometry
