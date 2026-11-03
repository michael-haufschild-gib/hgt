import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheSchurParametersOfSpecZ

/-!
# A window is the union of its lattices

A lattice of `n + 1` translates `φ(· + kh)` of a bump supported in `[−r, 0]` spans tests supported in
`[−(nh + r), 0]` (`latticeTest_eq_zero_of_not_mem`): its **total length** is `nh + r`. The lattice
register and the window register of GWZ are the same tower read in two ways:

* **Windows are their lattices** (`window_nonneg_iff_lattices`): Weil's form is nonnegative on the
  window `W_A` iff every lattice Toeplitz form of total length at most `A` is nonnegative.
* **Strict version** (`window_pos_iff_lattices`): Weil's form is positive on the nonzero tests of
  `W_A` iff every lattice of total length at most `A` of a nonzero bump has positive margins.

So the window length is the total lattice length, a window is positive exactly when all its lattice
canonical systems run with positive margins up to its length, and the first critical length of the
tower is the infimum of the total lengths at which some lattice evolution first loses a margin.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

open CohomologyOfWindowsOfSpecZ DimensionZeroGeometryOfSpecZ SpacingScaleHarmonicAnalysis
  ArithmeticCastelnuovoSeveri

variable {φ : ℝ → ℝ} {h r : ℝ}

/-- A lattice test with `n + 1` sites of a bump supported in `[−r, 0]` is supported in
`[−(nh + r), 0]`. -/
theorem latticeTest_eq_zero_of_not_mem (hsupp : ∀ y, y ∉ Icc (-r) 0 → φ y = 0) (hh : 0 ≤ h)
    {n : ℕ} (x : Fin (n + 1) → ℝ) {u : ℝ} (hu : u ∉ Icc (0 - (n * h + r)) 0) :
    latticeTest φ h x u = 0 := by
  rw [latticeTest_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hk : ((k : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp k.isLt
  have hk0 : (0 : ℝ) ≤ (k : ℕ) := Nat.cast_nonneg _
  rw [hsupp _ fun hm => hu ⟨by nlinarith [hm.1], by nlinarith [hm.2]⟩, mul_zero]

/-- A lattice test of total length at most `A` is a window test of length `A`. -/
theorem isWindowTest_latticeTest (hφ : φ ∈ realTests) (hsupp : ∀ y, y ∉ Icc (-r) 0 → φ y = 0)
    (hh : 0 ≤ h) {n : ℕ} {A : ℝ} (hlen : n * h + r ≤ A) (x : Fin (n + 1) → ℝ) :
    IsWindowTest A (latticeTest φ h x) :=
  ⟨(latticeTest_mem hφ x).1, fun u hu => latticeTest_eq_zero_of_not_mem hsupp hh x fun hm =>
    hu ⟨by linarith [hm.1], hm.2⟩⟩

/-- **Windows are their lattices.** Weil's form is nonnegative on `W_A` iff every lattice Toeplitz
form of total length at most `A` is nonnegative. -/
theorem window_nonneg_iff_lattices {A : ℝ} :
    (∀ G : ℝ → ℝ, IsWindowTest A G → 0 ≤ weilQuad G) ↔
      ∀ φ : ℝ → ℝ, ∀ r : ℝ, IsWindowTest r φ → ∀ h : ℝ, 0 < h → ∀ n : ℕ, n * h + r ≤ A →
        ∀ x : Fin (n + 1) → ℝ, 0 ≤ toeplitzForm (weilSeq φ h) (n + 1) x := by
  constructor
  · intro hW φ r hφ h hh n hlen x
    have hm := mem_realTests_of_isWindowTest hφ
    rw [← weilQuad_latticeTest hm h x]
    exact hW _ (isWindowTest_latticeTest hm hφ.vanish hh.le hlen x)
  · intro hL G hG
    have h1 := hL G A hG 1 one_pos 0 (by simp) (fun _ => 1)
    rw [← weilQuad_latticeTest (mem_realTests_of_isWindowTest hG) 1] at h1
    have hG1 : latticeTest G 1 (fun _ : Fin 1 => (1 : ℝ)) = G := by
      funext u; simp [latticeTest_apply]
    rwa [hG1] at h1

/-- **Strict version.** Weil's form is positive on the nonzero tests of `W_A` iff every lattice of
total length at most `A` of a nonzero bump has positive margins. -/
theorem window_pos_iff_lattices {A : ℝ} :
    (∀ G : ℝ → ℝ, IsWindowTest A G → G ≠ 0 → 0 < weilQuad G) ↔
      ∀ φ : ℝ → ℝ, ∀ r : ℝ, IsWindowTest r φ → φ ≠ 0 → ∀ h : ℝ, 0 < h → ∀ n : ℕ,
        n * h + r ≤ A → ∀ k ≤ n, 0 < levinsonErr (weilSeq φ h) k := by
  constructor
  · intro hW φ r hφ hφ0 h hh n hlen
    have hm := mem_realTests_of_isWindowTest hφ
    refine (toeplitzForm_posDef_iff (weilSeq_isEven φ h) n).mp fun x hx => ?_
    rw [← weilQuad_latticeTest hm h x]
    exact hW _ (isWindowTest_latticeTest hm hφ.vanish hh.le hlen x)
      (latticeTest_ne_zero hm hφ0 hh hx)
  · intro hL G hG hG0
    have h0 := hL G A hG hG0 1 one_pos 0 (by simp) 0 le_rfl
    rw [levinsonErr_zero, weilSeq, latticeTranslate_zero] at h0
    exact h0

end GaloisForLFunctions.GrowingWindowsOfSpecZ
