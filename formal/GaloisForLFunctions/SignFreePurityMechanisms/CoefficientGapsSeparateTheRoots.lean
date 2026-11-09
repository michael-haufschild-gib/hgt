import GaloisForLFunctions.HTGeometry.SlitPlaneQuotientDiscZeroFree
import GaloisForLFunctions.SignFreePurityMechanisms.SeparationForcesRationality

/-!
# Coefficient gaps separate the roots

The archimedean counterpart of a Newton polygon with distinct slopes. Let `a_0, …, a_n` be nonzero
complex numbers with `|a_{j+1}|² ≥ 9 |a_j| |a_{j+2}|` and put `ρ_j = |a_j| / |a_{j+1}|`.

* On the circle `|z| = 3 ρ_i` the term `a_{i+1} z^{i+1}` exceeds the sum of all the others
  (`HasCoeffGaps.norm_gapPoly_sub_lt`), so by Rouché's theorem `∑ a_j z^j` has exactly `i + 1`
  zeros in `|z| < 3 ρ_i` (`HasCoeffGaps.zeroSumBall_gapPoly`).
* Hence each annulus `3 ρ_{i-1} ≤ |z| < 3 ρ_i` carries one zero: the absolute value is injective
  on the zeros (`HasCoeffGaps.injOn_norm_zeros`).
* For real coefficients the separation principle gives real roots (`im_eq_zero_of_coeff_gaps`).

No sign of a coefficient is used. The price is lacunarity: of three zeros of increasing absolute
value the largest exceeds nine times the smallest (`HasCoeffGaps.nine_mul_norm_lt`).
-/

open Complex Metric Finset
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.SignFreePurityMechanisms

/-! ### Geometric decay and the dominant term -/

/-- A sequence decaying by a factor `3` at each of its first `m` steps has
`s 1 + ⋯ + s m ≤ (s 0 − s m) / 2`. -/
theorem sum_le_of_three_mul_le (s : ℕ → ℝ) (m : ℕ) (h : ∀ i < m, 3 * s (i + 1) ≤ s i) :
    ∑ i ∈ range m, s (i + 1) ≤ (s 0 - s m) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have h1 := ih fun i hi => h i (Nat.lt_succ_of_lt hi)
    have h2 := h m (Nat.lt_succ_self m)
    linarith only [h1, h2]

/-- If `t` grows by a factor `≥ 3` up to the index `k` and decays by a factor `≥ 3` from `k` to
`k + m`, the term `t k` exceeds the sum of all the others. -/
theorem sum_lt_of_dominant (t : ℕ → ℝ) (k m : ℕ) (h0 : 0 < t 0) (hend : 0 ≤ t (k + m))
    (hup : ∀ j < k, 3 * t j ≤ t (j + 1))
    (hdown : ∀ l < m, 3 * t (k + (l + 1)) ≤ t (k + l)) :
    ∑ j ∈ range k, t j + ∑ l ∈ range m, t (k + (l + 1)) < t k := by
  have hrefl : ∑ j ∈ range k, t j = ∑ l ∈ range k, t (k - (l + 1)) := by
    rw [← sum_range_reflect t k]
    exact sum_congr rfl fun l _ => by rw [Nat.sub_sub, add_comm]
  have hD := sum_le_of_three_mul_le (fun l => t (k - l)) k fun l hl => by
    have h3 := hup (k - (l + 1)) (by omega)
    rwa [show k - (l + 1) + 1 = k - l by omega] at h3
  simp only [Nat.sub_zero, Nat.sub_self] at hD
  have hU : ∑ l ∈ range m, t (k + (l + 1)) ≤ (t k - t (k + m)) / 2 :=
    sum_le_of_three_mul_le (fun l => t (k + l)) m hdown
  rw [hrefl]
  linarith only [hD, hU, h0, hend]

/-! ### Coefficient gaps -/

/-- The polynomial function `∑_{j ≤ n} a_j z^j`. -/
def gapPoly (a : ℕ → ℂ) (n : ℕ) (z : ℂ) : ℂ := ∑ j ∈ range (n + 1), a j * z ^ j

/-- The ratio `|a_j| / |a_{j+1}|` of consecutive coefficient sizes. -/
def coeffRatio (a : ℕ → ℂ) (j : ℕ) : ℝ := ‖a j‖ / ‖a (j + 1)‖

/-- Nonzero coefficients up to `n` with gaps `|a_{j+1}|² ≥ 9 |a_j| |a_{j+2}|`. -/
structure HasCoeffGaps (a : ℕ → ℂ) (n : ℕ) : Prop where
  ne_zero : ∀ j ≤ n, a j ≠ 0
  gap : ∀ j, j + 2 ≤ n → 9 * ‖a j‖ * ‖a (j + 2)‖ ≤ ‖a (j + 1)‖ ^ 2

theorem differentiable_gapPoly (a : ℕ → ℂ) (n : ℕ) : Differentiable ℂ (gapPoly a n) := by
  unfold gapPoly
  fun_prop

namespace HasCoeffGaps

variable {a : ℕ → ℂ} {n : ℕ} (h : HasCoeffGaps a n)

include h

theorem norm_pos {j : ℕ} (hj : j ≤ n) : 0 < ‖a j‖ :=
  norm_pos_iff.mpr (h.ne_zero j hj)

theorem coeffRatio_pos {j : ℕ} (hj : j < n) : 0 < coeffRatio a j :=
  div_pos (h.norm_pos hj.le) (h.norm_pos hj)

/-- The ratios grow by a factor at least `9`. -/
theorem nine_mul_coeffRatio_le {j : ℕ} (hj : j + 2 ≤ n) :
    9 * coeffRatio a j ≤ coeffRatio a (j + 1) := by
  have h1 := h.norm_pos (show j + 1 ≤ n by omega)
  have h2 : 0 < ‖a (j + 1 + 1)‖ := h.norm_pos (show j + 1 + 1 ≤ n by omega)
  have hg : 9 * ‖a j‖ * ‖a (j + 1 + 1)‖ ≤ ‖a (j + 1)‖ ^ 2 := h.gap j hj
  unfold coeffRatio
  rw [← mul_div_assoc, div_le_div_iff₀ h1 h2]
  linarith only [hg, sq (‖a (j + 1)‖)]

theorem coeffRatio_mono {j i : ℕ} (hji : j ≤ i) (hi : i < n) :
    coeffRatio a j ≤ coeffRatio a i := by
  induction i, hji using Nat.le_induction with
  | base => exact le_rfl
  | succ i hji ih =>
    have h9 := h.nine_mul_coeffRatio_le (show i + 2 ≤ n by omega)
    have hpos := h.coeffRatio_pos (show i < n by omega)
    linarith only [ih (by omega), h9, hpos]

/-- **Dominance.** For `3 ρ_i ≤ |z| ≤ ρ_{i+1} / 3` the term of degree `i + 1` exceeds the sum of
the others. -/
theorem norm_gapPoly_sub_lt {i : ℕ} (hi : i < n) {z : ℂ} (hlow : 3 * coeffRatio a i ≤ ‖z‖)
    (hup : i + 2 ≤ n → 3 * ‖z‖ ≤ coeffRatio a (i + 1)) :
    ‖gapPoly a n z - a (i + 1) * z ^ (i + 1)‖ < ‖a (i + 1) * z ^ (i + 1)‖ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = i + 1 + m := ⟨n - (i + 1), by omega⟩
  have hx : 0 < ‖z‖ := lt_of_lt_of_le (mul_pos (by norm_num) (h.coeffRatio_pos hi)) hlow
  have hgrow : ∀ j < i + 1, 3 * (‖a j‖ * ‖z‖ ^ j) ≤ ‖a (j + 1)‖ * ‖z‖ ^ (j + 1) := by
    intro j hj
    have hb := h.norm_pos (show j + 1 ≤ i + 1 + m by omega)
    have hr : ‖a j‖ ≤ coeffRatio a i * ‖a (j + 1)‖ :=
      (div_le_iff₀ hb).mp (h.coeffRatio_mono (Nat.lt_succ_iff.mp hj) hi)
    have h3 : 3 * ‖a j‖ ≤ ‖a (j + 1)‖ * ‖z‖ := by
      have hmul := mul_le_mul_of_nonneg_right hlow hb.le
      linarith only [hr, hmul]
    calc 3 * (‖a j‖ * ‖z‖ ^ j) = 3 * ‖a j‖ * ‖z‖ ^ j := by ring
      _ ≤ ‖a (j + 1)‖ * ‖z‖ * ‖z‖ ^ j := mul_le_mul_of_nonneg_right h3 (pow_nonneg hx.le j)
      _ = ‖a (j + 1)‖ * ‖z‖ ^ (j + 1) := by ring
  have hdecay : ∀ l < m, 3 * (‖a (i + 1 + (l + 1))‖ * ‖z‖ ^ (i + 1 + (l + 1))) ≤
      ‖a (i + 1 + l)‖ * ‖z‖ ^ (i + 1 + l) := by
    intro l hl
    rw [show i + 1 + (l + 1) = i + 1 + l + 1 from rfl]
    have hr := (hup (by omega)).trans
      (h.coeffRatio_mono (show i + 1 ≤ i + 1 + l by omega) (show i + 1 + l < i + 1 + m by omega))
    have hb := h.norm_pos (show i + 1 + l + 1 ≤ i + 1 + m by omega)
    unfold coeffRatio at hr
    rw [le_div_iff₀ hb] at hr
    calc 3 * (‖a (i + 1 + l + 1)‖ * ‖z‖ ^ (i + 1 + l + 1))
        = 3 * ‖z‖ * ‖a (i + 1 + l + 1)‖ * ‖z‖ ^ (i + 1 + l) := by ring
      _ ≤ ‖a (i + 1 + l)‖ * ‖z‖ ^ (i + 1 + l) :=
          mul_le_mul_of_nonneg_right hr (pow_nonneg hx.le _)
  have hdom := sum_lt_of_dominant (fun j => ‖a j‖ * ‖z‖ ^ j) (i + 1) m
    (by simpa using h.norm_pos (Nat.zero_le _))
    (mul_nonneg (norm_nonneg _) (pow_nonneg hx.le _)) hgrow hdecay
  have hsplit : gapPoly a (i + 1 + m) z - a (i + 1) * z ^ (i + 1) =
      ∑ j ∈ range (i + 1), a j * z ^ j +
        ∑ l ∈ range m, a (i + 1 + (l + 1)) * z ^ (i + 1 + (l + 1)) := by
    unfold gapPoly
    rw [show i + 1 + m + 1 = i + 1 + (m + 1) from rfl, sum_range_add,
      sum_range_succ' (fun x => a (i + 1 + x) * z ^ (i + 1 + x)) m]
    simp only [add_zero]
    ring
  rw [hsplit]
  calc ‖∑ j ∈ range (i + 1), a j * z ^ j +
        ∑ l ∈ range m, a (i + 1 + (l + 1)) * z ^ (i + 1 + (l + 1))‖
      ≤ ∑ j ∈ range (i + 1), ‖a j‖ * ‖z‖ ^ j +
        ∑ l ∈ range m, ‖a (i + 1 + (l + 1))‖ * ‖z‖ ^ (i + 1 + (l + 1)) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · exact (norm_sum_le _ _).trans_eq (sum_congr rfl fun j _ => by rw [norm_mul, norm_pow])
        · exact (norm_sum_le _ _).trans_eq (sum_congr rfl fun l _ => by rw [norm_mul, norm_pow])
    _ < ‖a (i + 1)‖ * ‖z‖ ^ (i + 1) := hdom
    _ = ‖a (i + 1) * z ^ (i + 1)‖ := by rw [norm_mul, norm_pow]

/-- The polynomial has no zero where one of its terms is dominant. -/
theorem gapPoly_ne_zero {i : ℕ} (hi : i < n) {z : ℂ} (hlow : 3 * coeffRatio a i ≤ ‖z‖)
    (hup : i + 2 ≤ n → 3 * ‖z‖ ≤ coeffRatio a (i + 1)) : gapPoly a n z ≠ 0 := by
  intro hz
  have hlt := h.norm_gapPoly_sub_lt hi hlow hup
  rw [hz, zero_sub, norm_neg] at hlt
  exact lt_irrefl _ hlt

/-- On the circle `|z| = 3 ρ_i` the term of degree `i + 1` is dominant. -/
theorem norm_gapPoly_sub_lt_of_mem_sphere {i : ℕ} (hi : i < n) {z : ℂ}
    (hz : z ∈ sphere (0 : ℂ) (3 * coeffRatio a i)) :
    ‖gapPoly a n z - a (i + 1) * z ^ (i + 1)‖ < ‖a (i + 1) * z ^ (i + 1)‖ := by
  have hnorm : ‖z‖ = 3 * coeffRatio a i := mem_sphere_zero_iff_norm.mp hz
  refine h.norm_gapPoly_sub_lt hi hnorm.ge fun h2 => ?_
  have h9 := h.nine_mul_coeffRatio_le h2
  rw [hnorm]
  linarith only [h9]

end HasCoeffGaps

/-! ### The zero count of a monomial -/

/-- A monomial `c z^k`, `c ≠ 0`, vanishes to order `k` at the origin. -/
theorem zeroMult_monomial {c : ℂ} (hc : c ≠ 0) (k : ℕ) :
    zeroMult (fun z : ℂ => c * z ^ k) 0 = k := by
  have han : AnalyticAt ℂ (fun z : ℂ => c * z ^ k) 0 := by fun_prop
  have hord : analyticOrderAt (fun z : ℂ => c * z ^ k) 0 = (k : ℕ∞) := by
    rw [han.analyticOrderAt_eq_natCast]
    exact ⟨fun _ => c, analyticAt_const, hc, Filter.Eventually.of_forall fun z => by
      simp [mul_comm]⟩
  rw [zeroMult, hord, ENat.toNat_coe]

/-- A monomial `c z^k`, `c ≠ 0`, has `k` zeros in every disc about the origin. -/
theorem zeroSumBall_monomial {c : ℂ} (hc : c ≠ 0) (k : ℕ) {r : ℝ} (hr : 0 < r) :
    zeroSumBall (fun z : ℂ => c * z ^ k) 0 r = (k : ℂ) := by
  have hG : DifferentiableOn ℂ (fun z : ℂ => c * z ^ k) Set.univ := by fun_prop
  have hne : ∀ ζ ∈ sphere (0 : ℂ) r, c * ζ ^ k ≠ 0 := fun ζ hζ =>
    mul_ne_zero hc (pow_ne_zero _ (norm_pos_iff.mp (by
      rw [mem_sphere_zero_iff_norm.mp hζ]
      exact hr)))
  obtain ⟨Z, hball, hzero, hsum⟩ := exists_zeroSet_zeroSumBall hr (lt_add_one r) isOpen_univ
    (Set.subset_univ _) hG hne
  rw [hsum]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hZ : Z = ∅ := Finset.eq_empty_of_forall_notMem fun z hz => by
      have := (hzero z (hball z hz)).mpr hz
      simp [hc] at this
    simp [hZ]
  · have hZ : Z = {0} := by
      ext z
      rw [Finset.mem_singleton]
      constructor
      · intro hz
        have hz0 := (hzero z (hball z hz)).mpr hz
        exact pow_eq_zero_iff hk.ne' |>.mp ((mul_eq_zero.mp hz0).resolve_left hc)
      · rintro rfl
        exact (hzero 0 (mem_ball_self hr)).mp (by simp [hk.ne'])
    rw [hZ, Finset.sum_singleton, zeroMult_monomial hc]

/-! ### One zero in each annulus -/

namespace HasCoeffGaps

variable {a : ℕ → ℂ} {n : ℕ} (h : HasCoeffGaps a n)

include h

/-- **Rouché count.** The polynomial has `i + 1` zeros, with multiplicity, in `|z| < 3 ρ_i`. -/
theorem zeroSumBall_gapPoly {i : ℕ} (hi : i < n) :
    zeroSumBall (gapPoly a n) 0 (3 * coeffRatio a i) = ((i + 1 : ℕ) : ℂ) := by
  have hr : 0 < 3 * coeffRatio a i := mul_pos (by norm_num) (h.coeffRatio_pos hi)
  have hane : a (i + 1) ≠ 0 := h.ne_zero _ hi
  have hG0 : ∀ ζ ∈ sphere (0 : ℂ) (3 * coeffRatio a i), a (i + 1) * ζ ^ (i + 1) ≠ 0 :=
    fun ζ hζ => mul_ne_zero hane (pow_ne_zero _ (norm_pos_iff.mp (by
      rw [mem_sphere_zero_iff_norm.mp hζ]
      exact hr)))
  have hslit : ∀ ζ ∈ sphere (0 : ℂ) (3 * coeffRatio a i),
      gapPoly a n ζ / (a (i + 1) * ζ ^ (i + 1)) ∈ slitPlane := by
    intro ζ hζ
    have hlt := h.norm_gapPoly_sub_lt_of_mem_sphere hi hζ
    have hq : gapPoly a n ζ / (a (i + 1) * ζ ^ (i + 1)) - 1 =
        (gapPoly a n ζ - a (i + 1) * ζ ^ (i + 1)) / (a (i + 1) * ζ ^ (i + 1)) := by
      rw [sub_div, div_self (hG0 ζ hζ)]
    have hnorm : ‖gapPoly a n ζ / (a (i + 1) * ζ ^ (i + 1)) - 1‖ < 1 := by
      rw [hq, norm_div, div_lt_one (norm_pos_iff.mpr (hG0 ζ hζ))]
      exact hlt
    have hre := (Complex.abs_re_le_norm _).trans_lt hnorm
    rw [Complex.sub_re, Complex.one_re] at hre
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith only [(abs_lt.mp hre).1]))
  rw [zeroSumBall_eq_of_quotient_mem_slitPlane hr (lt_add_one _) isOpen_univ (Set.subset_univ _)
    (differentiable_gapPoly a n).differentiableOn (by fun_prop) hG0 hslit]
  exact zeroSumBall_monomial hane (i + 1) hr

/-- The zeros in `|z| < 3 ρ_i` form a finite set of total multiplicity `i + 1`. -/
theorem exists_zeros_lt {i : ℕ} (hi : i < n) :
    ∃ Z : Finset ℂ, (∀ z, z ∈ Z ↔ gapPoly a n z = 0 ∧ ‖z‖ < 3 * coeffRatio a i) ∧
      ∑ ρ ∈ Z, zeroMult (gapPoly a n) ρ = i + 1 ∧ ∀ ρ ∈ Z, 1 ≤ zeroMult (gapPoly a n) ρ := by
  have hr : 0 < 3 * coeffRatio a i := mul_pos (by norm_num) (h.coeffRatio_pos hi)
  have hF := (differentiable_gapPoly a n).differentiableOn (s := Set.univ)
  have hne : ∀ ζ ∈ sphere (0 : ℂ) (3 * coeffRatio a i), gapPoly a n ζ ≠ 0 := by
    intro ζ hζ hz
    have hlt := h.norm_gapPoly_sub_lt_of_mem_sphere hi hζ
    rw [hz, zero_sub, norm_neg] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨Z, hball, hzero, hsum⟩ := exists_zeroSet_zeroSumBall hr (lt_add_one _) isOpen_univ
    (Set.subset_univ _) hF hne
  refine ⟨Z, fun z => ⟨fun hz => ?_, fun hz => ?_⟩, ?_, fun ρ hρ => ?_⟩
  · exact ⟨(hzero z (hball z hz)).mpr hz, mem_ball_zero_iff.mp (hball z hz)⟩
  · exact (hzero z (mem_ball_zero_iff.mpr hz.2)).mp hz.1
  · have hcount := h.zeroSumBall_gapPoly hi
    rw [hsum] at hcount
    exact_mod_cast hcount
  · exact one_le_zeroMult_of_zero hr (lt_add_one _) isOpen_univ (Set.subset_univ _) hF hne
      (hball ρ hρ) ((hzero ρ (hball ρ hρ)).mpr hρ)

/-- Every zero lies in exactly one annulus `3 ρ_{i-1} ≤ |z| < 3 ρ_i`. -/
theorem exists_annulus (hn : 0 < n) {z : ℂ} (hz : gapPoly a n z = 0) :
    ∃ i, i < n ∧ ‖z‖ < 3 * coeffRatio a i ∧ ∀ j < i, 3 * coeffRatio a j ≤ ‖z‖ := by
  have hinside : ∃ i, i < n ∧ ‖z‖ < 3 * coeffRatio a i := by
    refine ⟨n - 1, by omega, ?_⟩
    by_contra hge
    exact h.gapPoly_ne_zero (i := n - 1) (by omega) (not_lt.mp hge) (fun h2 => by omega) hz
  classical
  refine ⟨Nat.find hinside, (Nat.find_spec hinside).1, (Nat.find_spec hinside).2, fun j hj => ?_⟩
  have hnot := Nat.find_min hinside hj
  rw [not_and, not_lt] at hnot
  exact hnot (lt_trans hj (Nat.find_spec hinside).1)

/-- **One zero in each annulus.** Two zeros in the same annulus coincide: the discs of radii
`3 ρ_{i-1}` and `3 ρ_i` carry total multiplicities `i` and `i + 1`. -/
theorem eq_of_mem_annulus {i : ℕ} (hi : i < n) {z w : ℂ} (hz : gapPoly a n z = 0)
    (hw : gapPoly a n w = 0) (hzlt : ‖z‖ < 3 * coeffRatio a i) (hwlt : ‖w‖ < 3 * coeffRatio a i)
    (hzge : ∀ j < i, 3 * coeffRatio a j ≤ ‖z‖) (hwge : ∀ j < i, 3 * coeffRatio a j ≤ ‖w‖) :
    z = w := by
  obtain ⟨Z, hZ, hZsum, hZone⟩ := h.exists_zeros_lt hi
  have hzZ : z ∈ Z := (hZ z).mpr ⟨hz, hzlt⟩
  have hwZ : w ∈ Z := (hZ w).mpr ⟨hw, hwlt⟩
  -- the zeros strictly inside the previous circle
  obtain ⟨Z', hsub, hsum', hz', hw'⟩ : ∃ Z' : Finset ℂ, Z' ⊆ Z ∧
      ∑ ρ ∈ Z', zeroMult (gapPoly a n) ρ = i ∧ z ∉ Z' ∧ w ∉ Z' := by
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact ⟨∅, Finset.empty_subset _, by simp, by simp, by simp⟩
    · obtain ⟨Z', hZ', hZ'sum, -⟩ := h.exists_zeros_lt (show i - 1 < n by omega)
      have hmono := h.coeffRatio_mono (show i - 1 ≤ i by omega) hi
      refine ⟨Z', fun u hu => ?_, by rw [hZ'sum]; omega, fun hmem => ?_, fun hmem => ?_⟩
      · obtain ⟨hu0, hult⟩ := (hZ' u).mp hu
        exact (hZ u).mpr ⟨hu0, hult.trans_le (by linarith only [hmono])⟩
      · exact absurd ((hZ' z).mp hmem).2 (not_lt.mpr (hzge (i - 1) (by omega)))
      · exact absurd ((hZ' w).mp hmem).2 (not_lt.mpr (hwge (i - 1) (by omega)))
  by_contra hne
  have hpair : ({z, w} : Finset ℂ) ⊆ Z \ Z' := by
    intro u hu
    rw [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact Finset.mem_sdiff.mpr ⟨hzZ, hz'⟩
    · exact Finset.mem_sdiff.mpr ⟨hwZ, hw'⟩
  have h2 : 2 ≤ ∑ ρ ∈ Z \ Z', zeroMult (gapPoly a n) ρ := by
    have hz1 := hZone z hzZ
    have hw1 := hZone w hwZ
    calc 2 ≤ zeroMult (gapPoly a n) z + zeroMult (gapPoly a n) w := by omega
      _ = ∑ ρ ∈ ({z, w} : Finset ℂ), zeroMult (gapPoly a n) ρ := (Finset.sum_pair hne).symm
      _ ≤ ∑ ρ ∈ Z \ Z', zeroMult (gapPoly a n) ρ := Finset.sum_le_sum_of_subset hpair
  have htot := Finset.sum_sdiff hsub (f := zeroMult (gapPoly a n))
  omega

/-- **Coefficient gaps separate the roots.** Distinct zeros have distinct absolute values. -/
theorem injOn_norm_zeros : Set.InjOn (fun z : ℂ => ‖z‖) {z | gapPoly a n z = 0} := by
  intro z hz w hw hzw
  simp only [Set.mem_setOf_eq] at hz hw
  dsimp only at hzw
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact absurd hz (by simpa [gapPoly] using h.ne_zero 0 le_rfl)
  obtain ⟨i, hi, hlt, hge⟩ := h.exists_annulus hn hz
  exact h.eq_of_mem_annulus hi hz hw hlt (hzw ▸ hlt) hge (hzw ▸ hge)

/-- **The separated roots are lacunary.** Of three zeros of increasing absolute value, the
largest exceeds nine times the smallest: an annulus `R ≤ |z| ≤ 9R` carries at most two zeros. -/
theorem nine_mul_norm_lt {z w u : ℂ} (hz : gapPoly a n z = 0) (hw : gapPoly a n w = 0)
    (hu : gapPoly a n u = 0) (hzw : ‖z‖ < ‖w‖) (hwu : ‖w‖ < ‖u‖) : 9 * ‖z‖ < ‖u‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact absurd hz (by simpa [gapPoly] using h.ne_zero 0 le_rfl)
  obtain ⟨i, hi, hzlt, hzge⟩ := h.exists_annulus hn hz
  obtain ⟨k, hk, hwlt, hwge⟩ := h.exists_annulus hn hw
  obtain ⟨l, hl, hult, huge⟩ := h.exists_annulus hn hu
  -- the annulus index is strictly increasing in the absolute value
  have hik : i < k := by
    by_contra hki
    rcases Nat.lt_or_eq_of_le (not_lt.mp hki) with hlt | rfl
    · exact absurd (hzge k hlt) (not_le.mpr (hzw.trans hwlt))
    · exact hzw.ne (congrArg norm (h.eq_of_mem_annulus hk hz hw hzlt hwlt hzge hwge))
  have hkl : k < l := by
    by_contra hlk
    rcases Nat.lt_or_eq_of_le (not_lt.mp hlk) with hlt | rfl
    · exact absurd (hwge l hlt) (not_le.mpr (hwu.trans hult))
    · exact hwu.ne (congrArg norm (h.eq_of_mem_annulus hl hw hu hwlt hult hwge huge))
  have h1 := huge (i + 1) (by omega)
  have h9 := h.nine_mul_coeffRatio_le (show i + 2 ≤ n by omega)
  linarith only [h1, h9, hzlt]

end HasCoeffGaps

/-! ### Real coefficients -/

/-- **Archimedean Newton polygon.** A real polynomial with nonzero coefficients and gaps
`a_{j+1}² ≥ 9 |a_j a_{j+2}|` has only real roots. -/
theorem im_eq_zero_of_coeff_gaps (f : Polynomial ℝ) (hne : ∀ j ≤ f.natDegree, f.coeff j ≠ 0)
    (hgap : ∀ j, j + 2 ≤ f.natDegree →
      9 * |f.coeff j| * |f.coeff (j + 2)| ≤ f.coeff (j + 1) ^ 2)
    {z : ℂ} (hz : z ∈ f.rootSet ℂ) : z.im = 0 := by
  have hgaps : HasCoeffGaps (fun j => (f.coeff j : ℂ)) f.natDegree :=
    ⟨fun j hj => by exact_mod_cast hne j hj, fun j hj => by
      simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hgap j hj⟩
  have hzero : ∀ u ∈ f.rootSet ℂ, gapPoly (fun j => (f.coeff j : ℂ)) f.natDegree u = 0 := by
    intro u hu
    have hu0 := (Polynomial.mem_rootSet.mp hu).2
    rw [Polynomial.aeval_eq_sum_range] at hu0
    simpa only [gapPoly, Complex.real_smul] using hu0
  exact im_eq_zero_of_norm_injOn f
    (fun u hu w hw huw => hgaps.injOn_norm_zeros (hzero u hu) (hzero w hw) huw) hz

#print axioms HasCoeffGaps.zeroSumBall_gapPoly
#print axioms HasCoeffGaps.injOn_norm_zeros
#print axioms HasCoeffGaps.nine_mul_norm_lt
#print axioms im_eq_zero_of_coeff_gaps

end GaloisForLFunctions.SignFreePurityMechanisms
