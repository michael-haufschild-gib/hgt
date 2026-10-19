import GaloisForLFunctions.SquareRootThreshold.DepthProfileFourierModeLaw

/-!
# The Nyquist ceiling for periodic depth profiles

A periodic depth profile `d : ℤ/P → [0, ½]` on the ordinate lattice `2πℤ/L` has local density
`L/2π`, whose Nyquist aperture is `L/2`. The lattice law (`RHTower.offLineLattice_weil_positive_iff`)
says that a uniform off-line lattice hides exactly up to `L/2`. This module shows that `L/2` is a
**ceiling for the whole periodic class** and characterizes the profiles that reach it.

* **Ceiling** (`exists_re_W_profileConfig_neg_of_nyquist_lt`): if some residue is off the line,
  the profile is visible at every aperture `a > L/2`. At the lag `L` all phases `e^{2πirP/P}` are
  `1`, so the mode `D(P) = 2 Σ_r cosh(d_r L)` exceeds the zero mode `2P`.
* **Extremal profiles** (`profileConfig_weil_nonneg_nyquist_iff`): the profile hides up to the
  ceiling `L/2` iff the `P × P` Toeplitz matrix of its depth symbol is positive semidefinite.
* **Uniform depth is extremal** (`uniformProfile_weil_nonneg_of_le_nyquist`): a constant depth has
  `D(m) = 0` for `0 < |m| < P`, hence hides up to `L/2` whatever its size and its period.

So no periodic arrangement of off-line zeros at the density `L/2π` hides beyond the square-root
threshold `L/2`; reaching it requires the Toeplitz positivity of the cosh-depth modes.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- The period mode: `D(P) = 2 Σ_r cosh(d_r L)`. -/
theorem depthSymbol_period (L : ℝ) {P : ℕ} (hP : 0 < P) (d : Fin P → ℝ) :
    depthSymbol L d P = ((2 * ∑ r : Fin P, Real.cosh (d r * L) : ℝ) : ℂ) := by
  have hPc : (P : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
  rw [depthSymbol, Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have he : cexp (2 * π * I * (r : ℕ) * ((P : ℤ) : ℂ) / P) = 1 := by
    rw [show 2 * π * I * ((r : ℕ) : ℂ) * ((P : ℤ) : ℂ) / P = ((r : ℕ) : ℂ) * (2 * π * I) by
      push_cast; field_simp]
    exact Complex.exp_nat_mul_two_pi_mul_I _
  rw [he, mul_one]
  push_cast
  congr 2
  field_simp

/-- The period mode dominates the zero mode, strictly as soon as one residue is off the line. -/
theorem two_mul_lt_re_depthSymbol_period (L : ℝ) (hL : 0 < L) {P : ℕ} (hP : 0 < P)
    (d : Fin P → ℝ) {r₀ : Fin P} (hr₀ : d r₀ ≠ 0) :
    2 * (P : ℝ) < ‖depthSymbol L d P‖ := by
  rw [depthSymbol_period L hP, Complex.norm_real, Real.norm_eq_abs]
  have hlt : ∑ _r : Fin P, (1 : ℝ) < ∑ r : Fin P, Real.cosh (d r * L) := by
    refine Finset.sum_lt_sum (fun r _ => Real.one_le_cosh _) ⟨r₀, Finset.mem_univ _, ?_⟩
    exact Real.one_lt_cosh.mpr (mul_ne_zero hr₀ hL.ne')
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hlt
  rw [abs_of_pos (by linarith)]
  linarith

/-- **Nyquist ceiling.** A periodic depth profile with an off-line residue is visible at every
aperture `a > L/2`. -/
theorem exists_re_W_profileConfig_neg_of_nyquist_lt {L : ℝ} (hL : 0 < L) {P : ℕ} (hP : 0 < P)
    (d : Fin P → ℝ) (hd0 : ∀ r, 0 ≤ d r) (hd1 : ∀ r, d r ≤ 1 / 2) {r₀ : Fin P} (hr₀ : d r₀ ≠ 0)
    {a : ℝ} (ha : L / 2 < a) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      ((profileConfig hL hP d hd0 hd1).W f f).re < 0 := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have ha0 : 0 < a := lt_trans (by positivity) ha
  by_contra hcon
  push Not at hcon
  have hn : P < ⌈2 * a * P / L⌉₊ := by
    rw [Nat.lt_ceil, lt_div_iff₀ hL]
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)] at ha
    nlinarith
  have h := norm_depthSymbol_le_of_weil_nonneg hL hP d hd0 hd1 ha0 hcon hP hn
  have := two_mul_lt_re_depthSymbol_period L hL hP d hr₀
  linarith

/-- **Extremal profiles.** A periodic depth profile hides up to the ceiling `L/2` iff the
`P × P` Toeplitz matrix of its depth symbol is positive semidefinite. -/
theorem profileConfig_weil_nonneg_nyquist_iff {L : ℝ} (hL : 0 < L) {P : ℕ} (hP : 0 < P)
    (d : Fin P → ℝ) (hd0 : ∀ r, 0 ≤ d r) (hd1 : ∀ r, d r ≤ 1 / 2) :
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-(L / 2)) (L / 2) →
        0 ≤ ((profileConfig hL hP d hd0 hd1).W f f).re) ↔
      ∀ c : Fin P → ℂ, 0 ≤ (toeplitzForm (depthSymbol L d) P c).re := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hn : ⌈2 * (L / 2) * P / L⌉₊ = P := by
    rw [show 2 * (L / 2) * P / L = (P : ℝ) by field_simp]
    exact Nat.ceil_natCast P
  rw [profileConfig_weil_nonneg_iff hL hP d hd0 hd1 (by positivity), hn]

/-- A constant depth has no mode strictly between `0` and the period. -/
theorem depthSymbol_const_eq_zero (L δ : ℝ) {P : ℕ} {m : ℤ} (hm : ¬ (P : ℤ) ∣ m) :
    depthSymbol L (fun _ : Fin P => δ) m = 0 := by
  rcases Nat.eq_zero_or_pos P with h | hP
  · subst h; simp [depthSymbol]
  rw [depthSymbol, ← Finset.mul_sum]
  refine mul_eq_zero_of_right _ ?_
  have hz : cexp (2 * π * I * m / P) ≠ 1 := by
    intro h
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h
    apply hm
    have hPc : (P : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
    have hpi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    field_simp at hk
    exact ⟨k, by exact_mod_cast hk⟩
  have hgeom := geom_sum_eq hz P
  have hpow : cexp (2 * π * I * m / P) ^ P = 1 := by
    rw [← Complex.exp_nat_mul]
    have hPc : (P : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
    rw [show (P : ℂ) * (2 * π * I * m / P) = m * (2 * π * I) by field_simp]
    exact Complex.exp_int_mul_two_pi_mul_I m
  rw [hpow, sub_self, zero_div] at hgeom
  rw [← Fin.sum_univ_eq_sum_range (fun i => cexp (2 * π * I * m / P) ^ i)] at hgeom
  refine (Finset.sum_congr rfl fun r _ => ?_).trans hgeom
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/-- **Uniform depth is extremal.** A constant depth `δ` hides up to the ceiling `L/2`, for every
period `P`. -/
theorem uniformProfile_weil_nonneg_of_le_nyquist {L δ : ℝ} (hL : 0 < L) {P : ℕ} (hP : 0 < P)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) {a : ℝ} (ha : 0 < a) (haL : a ≤ L / 2) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    0 ≤ ((profileConfig hL hP (fun _ => δ) (fun _ => hδ0) (fun _ => hδ1)).W f f).re := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  refine profileConfig_weil_nonneg_of_modes hL hP _ _ _ ha ?_ hf hfs
  have hn : ⌈2 * a * P / L⌉₊ ≤ P := by
    rw [Nat.ceil_le, div_le_iff₀ hL]
    nlinarith
  rw [Finset.sum_eq_zero fun m hm => ?_]
  · positivity
  rw [depthSymbol_const_eq_zero L δ, norm_zero]
  rintro ⟨k, rfl⟩
  simp only [Finset.mem_erase, Finset.mem_Ioo] at hm
  obtain ⟨hm0, h1, h2⟩ := hm
  have hk : k ≠ 0 := by rintro rfl; simp at hm0
  have hP' : (P : ℤ) ≤ |(P : ℤ) * k| := by
    rw [abs_mul, abs_of_pos (by exact_mod_cast hP)]
    exact le_mul_of_one_le_right (by positivity) (Int.one_le_abs hk)
  have : |(P : ℤ) * k| < ⌈2 * a * P / L⌉₊ := abs_lt.mpr ⟨h1, h2⟩
  omega

end GaloisForLFunctions.SquareRootThreshold
