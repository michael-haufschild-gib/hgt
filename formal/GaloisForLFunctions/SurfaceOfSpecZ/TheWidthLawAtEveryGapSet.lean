import GaloisForLFunctions.SurfaceOfSpecZ.TheCountDoorAtEveryGapSet

/-!
# The width law at every gap set

`TheWidthIsTheStepanovExponentAtThePrimes` and `TheOtherSideAtThePrimes` read the zero width of `ζ`
as the growth exponent of a one-sided bound at the primes, by Landau's theorem for `ζ`. The iterated
gap method gives the same law at every degree set with power-saving gaps and for every
configuration:

* `re_le_iff_bddBelow_rpow_of_powGaps`: for a tempered configuration without real zeros and
  `0 ≤ a < ½`, every zero has `Re ρ ≤ ½ + a` iff `2 Re S(log d) ≥ −K d^a` on `D`;
* `re_le_iff_bddAbove_rpow_of_powGaps`: in the open strip, for every `a ≥ 0`, iff
  `2 Re S(log d) ≤ K d^a` on `D`, real zeros included;
* for `ζ` (`zetaZeroWidth_le_iff_bddBelow_of_powGaps`, `zetaZeroWidth_le_iff_bddAbove_of_powGaps`):
  the zero width is the growth exponent of either one-sided bound at any such `D`.

The forward directions are `|2 Re S(u)| ≤ E e^{au}` at width `a`
(`abs_two_re_lagStructure_le_exp_of_width`).
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-- At width `a` the traces are bounded by `E e^{au}`. -/
theorem abs_two_re_lagStructure_le_exp_of_width {Z : ZeroConfig} (hZ : TemperedConfig Z) {a : ℝ}
    (hwid : ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + a) {u : ℝ} (hu : 0 ≤ u) :
    |2 * (lagStructure Z (boxSpline 1 3) u).re| ≤
      (∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖) * Real.exp (a * u) := by
  have htop : TopDepth Z a := by
    intro z hz
    rcases mem_of_evenCoeff_ne_zero hz with h | h
    · have := hwid _ h; simp at this; linarith
    · have := hwid _ h; simp at this; linarith
  have hF := abs_normTrace_le hZ htop hu
  rw [two_re_lagStructure_eq_normTrace_mul Z a u, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right hF (Real.exp_pos _).le

/-- At width `a`, the traces at a degree `d ≥ 1` are bounded by `E d^a`. -/
theorem abs_two_re_lagStructure_log_le_of_width {Z : ZeroConfig} (hZ : TemperedConfig Z) {a : ℝ}
    (hwid : ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + a) {d : ℕ} (hd : 0 < d) :
    |2 * (lagStructure Z (boxSpline 1 3) (Real.log d)).re| ≤
      (∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖) * (d : ℝ) ^ a := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h := abs_two_re_lagStructure_le_exp_of_width hZ hwid (Real.log_natCast_nonneg d)
  rwa [show Real.exp (a * Real.log d) = (d : ℝ) ^ a by
    rw [Real.rpow_def_of_pos hd0, mul_comm]] at h

/-- **The width law from below at every gap set.** -/
theorem re_le_iff_bddBelow_rpow_of_powGaps (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) {θ : ℝ}
    (hθ1 : θ < 1) {D : Set ℕ} (hD : PowGaps θ D) :
    (∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + a) ↔ ∃ K : ℝ, ∀ d ∈ D,
      -(K * (d : ℝ) ^ a) ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log d)).re := by
  constructor
  · intro hwid
    exact ⟨_, fun d hd => (abs_le.mp (abs_two_re_lagStructure_log_le_of_width hZ hwid
      (hD.1 d hd))).1⟩
  · rintro ⟨K, hK⟩
    exact re_le_of_bddBelow_rpow_of_powGaps Z hZ ha0 ha ha0 le_rfl
      (fun ρ hρ him => absurd him (hnoreal ρ hρ)) hθ1 hD hK

/-- **The width law from above at every gap set**, real zeros included. -/
theorem re_le_iff_bddAbove_rpow_of_powGaps (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hlt : ∀ ρ ∈ Z.carrier, ρ.re < 1) {a : ℝ} (ha0 : 0 ≤ a) {θ : ℝ} (hθ1 : θ < 1) {D : Set ℕ}
    (hD : PowGaps θ D) :
    (∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + a) ↔ ∃ K : ℝ, ∀ d ∈ D,
      2 * (lagStructure Z (boxSpline 1 3) (Real.log d)).re ≤ K * (d : ℝ) ^ a := by
  constructor
  · intro hwid
    exact ⟨_, fun d hd => (abs_le.mp (abs_two_re_lagStructure_log_le_of_width hZ hwid
      (hD.1 d hd))).2⟩
  · rintro ⟨K, hK⟩
    exact re_le_of_bddAbove_rpow_of_powGaps Z hZ hlt ha0 hθ1 hD hK

/-- **The zero width of `ζ` is the Stepanov exponent at every gap set.** -/
theorem zetaZeroWidth_le_iff_bddBelow_of_powGaps {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) {θ : ℝ}
    (hθ1 : θ < 1) {D : Set ℕ} (hD : PowGaps θ D) :
    zetaZeroWidth ≤ a ↔ ∃ K : ℝ, ∀ d ∈ D,
      -(K * (d : ℝ) ^ a) ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log d)).re := by
  rw [zetaZeroWidth_le_iff_re_le ha0]
  exact re_le_iff_bddBelow_rpow_of_powGaps _ temperedConfig_zetaZeroConfig
    zetaZeroConfig_im_ne_zero' ha0 ha hθ1 hD

/-- **The zero width of `ζ` from above at every gap set.** -/
theorem zetaZeroWidth_le_iff_bddAbove_of_powGaps {a : ℝ} (ha0 : 0 ≤ a) {θ : ℝ} (hθ1 : θ < 1)
    {D : Set ℕ} (hD : PowGaps θ D) :
    zetaZeroWidth ≤ a ↔ ∃ K : ℝ, ∀ d ∈ D,
      2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log d)).re ≤ K * (d : ℝ) ^ a := by
  rw [zetaZeroWidth_le_iff_re_le ha0]
  exact re_le_iff_bddAbove_rpow_of_powGaps _ temperedConfig_zetaZeroConfig
    (fun _ hρ => hρ.2.2) ha0 hθ1 hD

end GaloisForLFunctions.SurfaceOfSpecZ
