/-
# Disk-arithmetic escape: the viability-certificate instrument

Certifies `K_b ∩ D̄(0,1) = ∅` (window viability) from finite rational data.  The pieces:

* `not_mem_filledJulia_of_gt_xStar` — everything beyond the escape fixed point is outside `K_b`
  (monotone escape, no rate);
* `escape_disk` / `escape_disk_step` — a terminal disk beyond the fixed point escapes
  pointwise, and escape pulls back one quadratic step along the disk chain
  `f(D(c,r)) ⊆ D(c²+b, r(2‖c‖+r))` with rounded centers absorbed into a drift bound `E`;
* square-subdivision layer: exact square splits (`interval_split`), square-in-disk
  (`square_subset_disk`, rational radius `283h/200 ≥ h√2`), and outside-unit-disk pruning
  (`square_outside_unit_*`) — the shape of the machine-generated certificates from
  `computations/rho_curve_recon/`;
* closed forms: `viable_of_sharp` (one step — all `‖b‖ > 2+√2`, every direction: this is what
  pins `ρ(π) = 2+√2` two-sided) and `viable_of_one_chain` (two steps —
  `xStar ‖b‖ + 2‖b‖ + 1 < ‖b‖·‖b+1‖`, the closed-form viable sector reaching `b = 3`).
-/
import GaloisForLFunctions.U0.U0PhiLargeCarrier

open Complex Set Metric Bottcher U0MonotoneEscape U0PhiLargeCarrier

namespace U0DiskEscape

/-- **Everything beyond the escape fixed point is outside the filled Julia set.** -/
theorem not_mem_filledJulia_of_gt_xStar {b z : ℂ} (hb : 2 < ‖b‖) (hz : xStar ‖b‖ < ‖z‖) :
    z ∉ filledJulia b := by
  intro hmem
  obtain ⟨n, hn⟩ := exists_iterate_gt (show (0:ℝ) < ‖b‖ by linarith) hz (max 2 ‖b‖)
  have hcomp := iterate_norm_ge hb hz.le (le_refl ‖z‖) n
  have h2 : max 2 ‖b‖ < ‖(quadratic b)^[n] z‖ := lt_of_lt_of_le hn hcomp
  exact not_mem_filledJulia (le_of_lt (lt_of_le_of_lt (le_max_right _ _) h2))
    (lt_of_le_of_lt (le_max_left _ _) h2) (filledJulia_forward hmem n)

/-- **Terminal disk**: a disk entirely beyond the fixed point escapes pointwise. -/
theorem escape_disk {b c : ℂ} {r : ℝ} (hb : 2 < ‖b‖) (h : xStar ‖b‖ + r < ‖c‖) :
    ∀ z : ℂ, ‖z - c‖ ≤ r → z ∉ filledJulia b := by
  intro z hz
  have hlow : xStar ‖b‖ < ‖z‖ := by
    have h1 : ‖c‖ - ‖z‖ ≤ ‖z - c‖ := by
      have := norm_sub_norm_le c z
      rw [show c - z = -(z - c) by ring, norm_neg] at this
      linarith
    linarith
  exact not_mem_filledJulia_of_gt_xStar hb hlow

/-- **One backward step along a disk chain.**  If the (rounded) image disk `D(c', r')` escapes
and contains `f(D(c,r))` — containment certified by a norm bound `N ≥ ‖c‖` and a drift bound
`E ≥ ‖c² + b − c'‖` with `E + r(2N + r) ≤ r'` — then `D(c,r)` escapes. -/
theorem escape_disk_step {b c c' : ℂ} {r r' E N : ℝ}
    (hN : ‖c‖ ≤ N) (hE : ‖c ^ (2 : ℕ) + b - c'‖ ≤ E) (hr : E + r * (2 * N + r) ≤ r')
    (hnext : ∀ z : ℂ, ‖z - c'‖ ≤ r' → z ∉ filledJulia b) :
    ∀ z : ℂ, ‖z - c‖ ≤ r → z ∉ filledJulia b := by
  intro z hz hmem
  have hr0 : (0 : ℝ) ≤ r := le_trans (norm_nonneg _) hz
  have himg : ‖(z ^ (2 : ℕ) + b) - c'‖ ≤ r' := by
    have hzc : ‖z + c‖ ≤ 2 * N + r := by
      calc ‖z + c‖ = ‖(z - c) + 2 * c‖ := by ring_nf
        _ ≤ ‖z - c‖ + ‖(2 : ℂ) * c‖ := norm_add_le _ _
        _ = ‖z - c‖ + 2 * ‖c‖ := by rw [norm_mul, Complex.norm_ofNat]
        _ ≤ 2 * N + r := by linarith
    have h1 : ‖z ^ (2 : ℕ) - c ^ (2 : ℕ)‖ ≤ r * (2 * N + r) := by
      rw [show z ^ (2 : ℕ) - c ^ (2 : ℕ) = (z - c) * (z + c) by ring, norm_mul]
      exact mul_le_mul hz hzc (norm_nonneg _) hr0
    calc ‖(z ^ (2 : ℕ) + b) - c'‖ = ‖(c ^ (2 : ℕ) + b - c') + (z ^ (2 : ℕ) - c ^ (2 : ℕ))‖ := by ring_nf
      _ ≤ ‖c ^ (2 : ℕ) + b - c'‖ + ‖z ^ (2 : ℕ) - c ^ (2 : ℕ)‖ := norm_add_le _ _
      _ ≤ E + r * (2 * N + r) := add_le_add hE h1
      _ ≤ r' := hr
  have hfz : quadratic b z ∉ filledJulia b := hnext _ (by simpa [quadratic_apply] using himg)
  exact hfz (by simpa using filledJulia_forward hmem 1)

/-! ## The square-subdivision layer -/

/-- 1D interval split: `|t − c| ≤ h` puts `t` in the left or right half. -/
theorem interval_split {t c h : ℝ} (ht : |t - c| ≤ h) :
    |t - (c - h / 2)| ≤ h / 2 ∨ |t - (c + h / 2)| ≤ h / 2 := by
  have h1 := abs_le.mp ht
  rcases le_total t c with hle | hge
  · left; rw [abs_le]; constructor <;> linarith
  · right; rw [abs_le]; constructor <;> linarith

/-- Square-in-disk with rational radius: the square of half-side `h` around `c` is inside
`D(c, 283h/200)` (since `283/200 ≥ √2`). -/
theorem square_subset_disk {c z : ℂ} {h : ℝ} (hh : 0 ≤ h)
    (hre : |z.re - c.re| ≤ h) (him : |z.im - c.im| ≤ h) :
    ‖z - c‖ ≤ 283 / 200 * h := by
  have hsq : ‖z - c‖ ^ (2 : ℕ) = (z.re - c.re) ^ (2 : ℕ) + (z.im - c.im) ^ (2 : ℕ) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  have h1 := abs_le.mp hre
  have h2 := abs_le.mp him
  nlinarith [norm_nonneg (z - c), hsq, sq_nonneg (z.re - c.re), sq_nonneg (z.im - c.im)]

/-- Pruning, real-axis form: the square lies beyond `|Re| = 1`. -/
theorem square_outside_unit_re {cx h : ℝ} (hfar : 1 + h < |cx|) :
    ∀ z : ℂ, |z.re - cx| ≤ h → ¬(‖z‖ ≤ 1) := by
  intro z hre hz
  have h1 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have h2 := abs_le.mp hre
  rcases abs_cases cx with ⟨hc, _⟩ | ⟨hc, _⟩
  · have : 1 + h < cx := by rw [← hc]; exact hfar
    have : 1 < z.re := by linarith
    have := abs_le.mp (le_trans h1 hz)
    linarith
  · have : 1 + h < -cx := by rw [← hc]; exact hfar
    have : z.re < -1 := by linarith
    have := abs_le.mp (le_trans h1 hz)
    linarith

/-- Pruning, imaginary-axis form. -/
theorem square_outside_unit_im {cy h : ℝ} (hfar : 1 + h < |cy|) :
    ∀ z : ℂ, |z.im - cy| ≤ h → ¬(‖z‖ ≤ 1) := by
  intro z him hz
  have h1 : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have h2 := abs_le.mp him
  rcases abs_cases cy with ⟨hc, _⟩ | ⟨hc, _⟩
  · have : 1 + h < cy := by rw [← hc]; exact hfar
    have : 1 < z.im := by linarith
    have := abs_le.mp (le_trans h1 hz)
    linarith
  · have : 1 + h < -cy := by rw [← hc]; exact hfar
    have : z.im < -1 := by linarith
    have := abs_le.mp (le_trans h1 hz)
    linarith

/-- Pruning, corner form: both coordinate strips are separated from the unit disk. -/
theorem square_outside_unit_corner {cx cy h dx dy : ℝ}
    (hdx : 0 ≤ dx) (hdy : 0 ≤ dy) (hx : dx + h ≤ |cx|) (hy : dy + h ≤ |cy|)
    (hfar : 1 < dx ^ (2 : ℕ) + dy ^ (2 : ℕ)) :
    ∀ z : ℂ, |z.re - cx| ≤ h → |z.im - cy| ≤ h → ¬(‖z‖ ≤ 1) := by
  intro z hre him hz
  have hre' : dx ≤ |z.re| := by
    have h1 := abs_le.mp hre
    rcases abs_cases cx with ⟨hc, _⟩ | ⟨hc, _⟩
    · have : dx + h ≤ cx := by rw [← hc]; exact hx
      have : dx ≤ z.re := by linarith
      exact le_trans this (le_abs_self _)
    · have : dx + h ≤ -cx := by rw [← hc]; exact hx
      have : z.re ≤ -dx := by linarith
      calc dx = -(-dx) := by ring
        _ ≤ -z.re := by linarith
        _ ≤ |z.re| := neg_le_abs _
  have him' : dy ≤ |z.im| := by
    have h1 := abs_le.mp him
    rcases abs_cases cy with ⟨hc, _⟩ | ⟨hc, _⟩
    · have : dy + h ≤ cy := by rw [← hc]; exact hy
      have : dy ≤ z.im := by linarith
      exact le_trans this (le_abs_self _)
    · have : dy + h ≤ -cy := by rw [← hc]; exact hy
      have : z.im ≤ -dy := by linarith
      calc dy = -(-dy) := by ring
        _ ≤ -z.im := by linarith
        _ ≤ |z.im| := neg_le_abs _
  have hsq : ‖z‖ ^ (2 : ℕ) = z.re ^ (2 : ℕ) + z.im ^ (2 : ℕ) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have h1 : ‖z‖ ^ (2 : ℕ) ≤ 1 := by nlinarith [norm_nonneg z]
  nlinarith [sq_abs z.re, sq_abs z.im, abs_nonneg z.re, abs_nonneg z.im, hre', him']

/-! ## Closed forms -/

/-- **Sharp one-step viability**: for `xStar ‖b‖ + 1 < ‖b‖` — equivalently `‖b‖ > 2+√2`, EVERY
direction — the whole closed unit disk escapes: `K_b` avoids it. -/
theorem viable_of_sharp {b : ℂ} (hb2 : 2 < ‖b‖) (h : xStar ‖b‖ + 1 < ‖b‖) :
    ∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia b := by
  intro z hz
  refine escape_disk_step (c := 0) (c' := b) (N := 0) (E := 0) (r := 1) (r' := 1)
    (by simp) (by simp) (by norm_num) ?_ z (by simpa using hz)
  exact escape_disk hb2 (by simpa using h)

/-- **Two-step closed-form viability**: `xStar ‖b‖ + 2‖b‖ + 1 < ‖b‖·‖b+1‖` — the criterion
whose sector around the positive ray reaches modulus 3 (`b = 3` gives `12 > xStar 3 + 7`). -/
theorem viable_of_one_chain {b : ℂ} (hb2 : 2 < ‖b‖)
    (h : xStar ‖b‖ + (2 * ‖b‖ + 1) < ‖b‖ * ‖b + 1‖) :
    ∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia b := by
  intro z hz
  refine escape_disk_step (c := 0) (c' := b) (N := 0) (E := 0) (r := 1) (r' := 1)
    (by simp) (by simp) (by norm_num) ?_ z (by simpa using hz)
  refine escape_disk_step (c := b) (c' := b ^ (2 : ℕ) + b) (N := ‖b‖) (E := 0) (r := 1)
    (r' := 2 * ‖b‖ + 1) (le_refl _) (by simp) (by nlinarith [norm_nonneg b]) ?_
  refine escape_disk hb2 ?_
  have hval : ‖b ^ (2 : ℕ) + b‖ = ‖b‖ * ‖b + 1‖ := by
    rw [show b ^ (2 : ℕ) + b = b * (b + 1) by ring, norm_mul]
  linarith [hval.ge, hval.le]

/-- Cross-check: `K_3` avoids the closed unit disk via the two-step closed form (re-deriving
`U0DichotomyWitness.unitDisk_avoids_filledJulia_three` from the kit). -/
example : ∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia (3 : ℂ) := by
  have h3 : ‖(3 : ℂ)‖ = 3 := Complex.norm_ofNat 3
  have h4 : ‖(3 : ℂ) + 1‖ = 4 := by
    rw [show (3 : ℂ) + 1 = 4 by norm_num, Complex.norm_ofNat]
  refine viable_of_one_chain (by rw [h3]; norm_num) ?_
  rw [h3, h4, xStar]
  set S := Real.sqrt (1 + 4 * 3 : ℝ) with hSdef
  have hS : S ≤ 4 := by
    rw [hSdef]
    have h16 : Real.sqrt (1 + 4 * 3 : ℝ) ≤ Real.sqrt 16 := Real.sqrt_le_sqrt (by norm_num)
    rwa [show (16 : ℝ) = 4 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)] at h16
  linarith

end U0DiskEscape

namespace U0DiskEscape

/-! ## Coordinate forms — every certificate condition as a rational inequality -/

/-- Upper norm bound from squared coordinates. -/
theorem norm_le_of_sq {w : ℂ} {N : ℝ} (hN : 0 ≤ N) (h : w.re ^ (2 : ℕ) + w.im ^ (2 : ℕ) ≤ N ^ (2 : ℕ)) :
    ‖w‖ ≤ N := by
  have hsq : ‖w‖ ^ (2 : ℕ) = w.re ^ (2 : ℕ) + w.im ^ (2 : ℕ) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  nlinarith [norm_nonneg w]

/-- Lower norm bound from squared coordinates. -/
theorem le_norm_of_sq {w : ℂ} {M : ℝ} (_hM : 0 ≤ M) (h : M ^ (2 : ℕ) ≤ w.re ^ (2 : ℕ) + w.im ^ (2 : ℕ)) :
    M ≤ ‖w‖ := by
  have hsq : ‖w‖ ^ (2 : ℕ) = w.re ^ (2 : ℕ) + w.im ^ (2 : ℕ) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  nlinarith [norm_nonneg w]

/-- Escape-parameter bound from squared coordinates. -/
theorem two_lt_norm_of_sq {b : ℂ} (h : 4 < b.re ^ (2 : ℕ) + b.im ^ (2 : ℕ)) : 2 < ‖b‖ := by
  have hsq : ‖b‖ ^ (2 : ℕ) = b.re ^ (2 : ℕ) + b.im ^ (2 : ℕ) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  by_contra hcon
  push Not at hcon
  nlinarith [norm_nonneg b]

/-- `xStar ‖b‖ ≤ X` from rational data: `Nb ≥ ‖b‖` (squared), `S² ≥ 1+4Nb`, `X ≥ (1+S)/2`. -/
theorem xStar_le_of_bounds {b : ℂ} {Nb S X : ℝ} (hNb0 : 0 ≤ Nb)
    (hNb : b.re ^ (2 : ℕ) + b.im ^ (2 : ℕ) ≤ Nb ^ (2 : ℕ)) (hS0 : 0 ≤ S) (hS : 1 + 4 * Nb ≤ S ^ (2 : ℕ))
    (hX : (1 + S) / 2 ≤ X) : xStar ‖b‖ ≤ X := by
  have hb : ‖b‖ ≤ Nb := norm_le_of_sq hNb0 hNb
  have h1 : Real.sqrt (1 + 4 * ‖b‖) ≤ S := by
    have h2 : Real.sqrt (1 + 4 * ‖b‖) ≤ Real.sqrt (S ^ (2 : ℕ)) :=
      Real.sqrt_le_sqrt (by linarith)
    rwa [Real.sqrt_sq hS0] at h2
  rw [xStar]
  linarith

/-- Coordinate-form chain step: rational data `(N, E, r, r')` certifies one backward step. -/
theorem escape_step_coords {bx bi cx ci c'x c'i r r' E N : ℝ}
    (hN0 : 0 ≤ N) (hN : cx ^ (2 : ℕ) + ci ^ (2 : ℕ) ≤ N ^ (2 : ℕ))
    (hE0 : 0 ≤ E)
    (hE : (cx ^ (2 : ℕ) - ci ^ (2 : ℕ) + bx - c'x) ^ (2 : ℕ) + (2 * cx * ci + bi - c'i) ^ (2 : ℕ) ≤ E ^ (2 : ℕ))
    (hr : E + r * (2 * N + r) ≤ r')
    (hnext : ∀ z : ℂ, ‖z - (⟨c'x, c'i⟩ : ℂ)‖ ≤ r' → z ∉ filledJulia (⟨bx, bi⟩ : ℂ)) :
    ∀ z : ℂ, ‖z - (⟨cx, ci⟩ : ℂ)‖ ≤ r → z ∉ filledJulia (⟨bx, bi⟩ : ℂ) := by
  refine escape_disk_step (c := ⟨cx, ci⟩) (c' := ⟨c'x, c'i⟩) (N := N) (E := E)
    (norm_le_of_sq hN0 hN) ?_ hr hnext
  refine norm_le_of_sq hE0 ?_
  have hw : ((⟨cx, ci⟩ : ℂ) ^ (2 : ℕ) + (⟨bx, bi⟩ : ℂ) - (⟨c'x, c'i⟩ : ℂ))
      = (⟨cx ^ (2 : ℕ) - ci ^ (2 : ℕ) + bx - c'x, 2 * cx * ci + bi - c'i⟩ : ℂ) := by
    rw [Complex.ext_iff]
    constructor
    · show ((⟨cx, ci⟩ : ℂ) ^ (2 : ℕ) + (⟨bx, bi⟩ : ℂ) - (⟨c'x, c'i⟩ : ℂ)).re = _
      simp [pow_two, Complex.mul_re, Complex.add_re, Complex.sub_re]
    · show ((⟨cx, ci⟩ : ℂ) ^ (2 : ℕ) + (⟨bx, bi⟩ : ℂ) - (⟨c'x, c'i⟩ : ℂ)).im = _
      simp [pow_two, Complex.mul_im, Complex.add_im, Complex.sub_im]
      ring
  rw [hw]
  exact hE

/-- Coordinate-form terminal disk: rational data `(M, Nb, S)` certifies escape past `xStar`. -/
theorem escape_terminal_coords {bx bi cx ci r M Nb S : ℝ}
    (hb2 : 4 < bx ^ (2 : ℕ) + bi ^ (2 : ℕ))
    (hNb0 : 0 ≤ Nb) (hNb : bx ^ (2 : ℕ) + bi ^ (2 : ℕ) ≤ Nb ^ (2 : ℕ))
    (hS0 : 0 ≤ S) (hS : 1 + 4 * Nb ≤ S ^ (2 : ℕ))
    (hM0 : 0 ≤ M) (hM : M ^ (2 : ℕ) ≤ cx ^ (2 : ℕ) + ci ^ (2 : ℕ))
    (hgap : (1 + S) / 2 + r < M) :
    ∀ z : ℂ, ‖z - (⟨cx, ci⟩ : ℂ)‖ ≤ r → z ∉ filledJulia (⟨bx, bi⟩ : ℂ) := by
  have hb2' : 2 < ‖(⟨bx, bi⟩ : ℂ)‖ := two_lt_norm_of_sq hb2
  refine escape_disk hb2' ?_
  have hxs : xStar ‖(⟨bx, bi⟩ : ℂ)‖ ≤ (1 + S) / 2 :=
    xStar_le_of_bounds hNb0 hNb hS0 hS (le_refl _)
  have hc : M ≤ ‖(⟨cx, ci⟩ : ℂ)‖ := le_norm_of_sq hM0 hM
  linarith

/-- Square-to-disk bridge in coordinates (rational radius `283h/200 ≥ h√2`). -/
theorem escape_square_coords {bx bi cx ci h : ℝ} (hh : 0 ≤ h)
    (hdisk : ∀ z : ℂ, ‖z - (⟨cx, ci⟩ : ℂ)‖ ≤ 283 / 200 * h →
      z ∉ filledJulia (⟨bx, bi⟩ : ℂ)) :
    ∀ z : ℂ, |z.re - cx| ≤ h → |z.im - ci| ≤ h → z ∉ filledJulia (⟨bx, bi⟩ : ℂ) := by
  intro z hre him
  exact hdisk z (square_subset_disk hh hre him)

/-- Viability from the root square `[−1,1]²`. -/
theorem viable_of_root_square {bx bi : ℝ}
    (hroot : ∀ z : ℂ, |z.re - 0| ≤ 1 → |z.im - 0| ≤ 1 → ‖z‖ ≤ 1 →
      z ∉ filledJulia (⟨bx, bi⟩ : ℂ)) :
    ∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia (⟨bx, bi⟩ : ℂ) := by
  intro z hz
  refine hroot z ?_ ?_ hz
  · rw [sub_zero]; exact le_trans (Complex.abs_re_le_norm z) hz
  · rw [sub_zero]; exact le_trans (Complex.abs_im_le_norm z) hz

end U0DiskEscape
