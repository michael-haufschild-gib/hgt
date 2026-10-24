import GaloisForLFunctions.ArithmeticOrientationGeometry.TheOrientationOfACycle
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHodgeIndexOfZetaHoldsAwayFromLowFrequencies

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

end GaloisForLFunctions.ArithmeticOrientationGeometry
