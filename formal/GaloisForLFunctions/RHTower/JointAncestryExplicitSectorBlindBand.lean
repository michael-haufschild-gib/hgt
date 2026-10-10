import GaloisForLFunctions.RHTower.JointAncestryExplicitSectorDepth

/-!
# JAS explicit-formula sectors: the bounded-depth blind band

Off the critical line the explicit-formula sector of a strip point loses positivity at some
finite prime depth.  This module proves that the required depth is unbounded near the line:
the local phase of every prime factor is uniformly `O(|σ - 1/2|)`.

Write the local density as `ℓ = F(r₁v) + conj F(r₂v) - 1`, with `F(z) = (1 - z)⁻¹`, radii
`r₁ = p^{-σ}`, `r₂ = p^{σ-1}` and a unit `v`.  Two estimates hold uniformly in the prime and the
circle point when `|σ - 1/2| ≤ 1/4`:

* `Re ℓ ≥ 2/(1 + ρ) - 1 > 0`, where `ρ = 2^{-1/4}` bounds both radii, because `F` maps the disk of
  radius `r` into `Re ≥ 1/(1 + r)`;
* `|Im ℓ| ≤ |F(r₁v) - F(r₂v)| ≤ |r₁ - r₂|/(1 - ρ)²` and
  `|r₁ - r₂| ≤ 2|σ - 1/2| log p · p^{-1/4} ≤ 8|σ - 1/2|`.

Jordan's inequality turns these into `|arg ℓ| ≤ K |σ - 1/2|` with an absolute constant `K`.  Hence
a product over `k` primes has total phase at most `K k |σ - 1/2|`, and its real part is positive
whenever `K k |σ - 1/2| < π/2`.

**Blind band.**  For every depth `k` there is `η_k > 0` such that every strip point with
`|σ - 1/2| < η_k`, on or off the critical line, has positive explicit-formula density at every
depth `≤ k`.  In particular every Xi zero within `η_k` of the critical line is invisible to
positivity tests of depth `≤ k`.  Together with the finite-depth detection theorem, the detection
depth of an off-line point tends to infinity as it approaches the line: a JAS producer based on
explicit-formula positivity must use unbounded prime depth.

The theta-point value of the local density is `(1 - p⁻¹)/((1 - p^{-s})(1 - p^{-(1-s)}))`, so the
depth-`P` density at the theta point is the functional-equation-symmetric truncated Euler product
`ζ_P(s) ζ_P(1 - s)` divided by the truncated pole `ζ_P(1)`.
-/

open Complex Filter
open scoped ComplexConjugate BigOperators

namespace RHTower

noncomputable section

/-- `(1 - z)⁻¹` maps the closed disk of radius `r < 1` into the half-plane `Re ≥ 1/(1 + r)`. -/
theorem inv_one_add_le_re_inv_one_sub {z : ℂ} {r : ℝ} (hz : ‖z‖ ≤ r) (hr : r < 1) :
    1 / (1 + r) ≤ ((1 - z)⁻¹).re := by
  have hr0 : 0 ≤ r := le_trans (norm_nonneg z) hz
  have hre : -r ≤ z.re := by
    have := Complex.abs_re_le_norm z
    have := neg_abs_le z.re
    linarith
  have hre1 : z.re < 1 := by
    have := Complex.re_le_norm z
    linarith
  have hsq : z.re ^ 2 + z.im ^ 2 ≤ r ^ 2 := by
    have h := Complex.sq_norm z
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg z]
  rw [Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub]
  have hden : 0 < (1 - z.re) * (1 - z.re) + -z.im * -z.im := by nlinarith
  rw [div_le_div_iff₀ (by linarith) hden]
  nlinarith

/-- Difference of the Cauchy factor at two radii on one ray. -/
theorem norm_inv_one_sub_sub_le {r₁ r₂ ρ : ℝ} {v : ℂ} (hv : ‖v‖ = 1) (h₁ : 0 ≤ r₁)
    (h₂ : 0 ≤ r₂) (h₁ρ : r₁ ≤ ρ) (h₂ρ : r₂ ≤ ρ) (hρ : ρ < 1) :
    ‖(1 - (r₁ : ℂ) * v)⁻¹ - (1 - (r₂ : ℂ) * v)⁻¹‖ ≤ |r₁ - r₂| / (1 - ρ) ^ 2 := by
  have hn1 : 1 - ρ ≤ ‖1 - (r₁ : ℂ) * v‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((r₁ : ℂ) * v)
    rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg h₁, hv, mul_one] at this
    linarith
  have hn2 : 1 - ρ ≤ ‖1 - (r₂ : ℂ) * v‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((r₂ : ℂ) * v)
    rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg h₂, hv, mul_one] at this
    linarith
  have hpos : 0 < 1 - ρ := by linarith
  have hne1 : (1 - (r₁ : ℂ) * v) ≠ 0 := fun h => by
    rw [h, norm_zero] at hn1; linarith
  have hne2 : (1 - (r₂ : ℂ) * v) ≠ 0 := fun h => by
    rw [h, norm_zero] at hn2; linarith
  rw [inv_sub_inv hne1 hne2, norm_div, norm_mul]
  have hnum : ‖(1 - (r₂ : ℂ) * v) - (1 - (r₁ : ℂ) * v)‖ = |r₁ - r₂| := by
    rw [show (1 - (r₂ : ℂ) * v) - (1 - (r₁ : ℂ) * v) = ((r₁ - r₂ : ℝ) : ℂ) * v by push_cast; ring,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, hv, mul_one]
  rw [hnum, div_le_div_iff₀ (mul_pos (by linarith) (by linarith)) (by positivity)]
  have := mul_le_mul hn1 hn2 hpos.le (by linarith)
  nlinarith [abs_nonneg (r₁ - r₂)]

/-- Jordan's inequality for the argument of a point of the right half-plane. -/
theorem abs_arg_le_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    |z.arg| ≤ Real.pi / 2 * (|z.im| / z.re) := by
  have hne : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz; exact lt_irrefl 0 hz
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hne
  have hle : z.re ≤ ‖z‖ := Complex.re_le_norm z
  have hhalf : |z.arg| ≤ Real.pi / 2 := Complex.abs_arg_le_pi_div_two_iff.mpr hz.le
  have hsin := Complex.sin_arg z
  have key : 2 / Real.pi * |z.arg| ≤ |z.im| / ‖z‖ := by
    rcases le_or_gt 0 z.arg with h | h
    · rw [abs_of_nonneg h] at hhalf ⊢
      have := Real.mul_le_sin h hhalf
      rw [hsin] at this
      calc 2 / Real.pi * z.arg ≤ z.im / ‖z‖ := this
        _ ≤ |z.im| / ‖z‖ := div_le_div_of_nonneg_right (le_abs_self _) hnorm.le
    · rw [abs_of_neg h] at hhalf ⊢
      have := Real.mul_le_sin (by linarith : 0 ≤ -z.arg) hhalf
      rw [Real.sin_neg, hsin] at this
      calc 2 / Real.pi * -z.arg ≤ -(z.im / ‖z‖) := this
        _ = -z.im / ‖z‖ := by ring
        _ ≤ |z.im| / ‖z‖ := div_le_div_of_nonneg_right (neg_le_abs _) hnorm.le
  have h2 : |z.im| / ‖z‖ ≤ |z.im| / z.re := div_le_div_of_nonneg_left (abs_nonneg _) hz hle
  have hpi := Real.pi_pos
  have : |z.arg| ≤ Real.pi / 2 * (|z.im| / ‖z‖) := by
    rw [show Real.pi / 2 * (|z.im| / ‖z‖) = (|z.im| / ‖z‖) / (2 / Real.pi) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    linarith
  calc |z.arg| ≤ Real.pi / 2 * (|z.im| / ‖z‖) := this
    _ ≤ Real.pi / 2 * (|z.im| / z.re) := by gcongr

/-- The common radius bound `ρ = 2^{-1/4}` for strip points within `1/4` of the line. -/
def jasBandRadius : ℝ := Real.exp (-(Real.log 2 / 4))

theorem jasBandRadius_lt_one : jasBandRadius < 1 := by
  rw [jasBandRadius, Real.exp_lt_one_iff]
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  linarith

theorem jasBandRadius_pos : 0 < jasBandRadius := Real.exp_pos _

theorem jasR1_le_band {s : ℂ} (hs : |s.re - 1 / 2| ≤ 1 / 4) (p : Nat.Primes) :
    jasR1 s p ≤ jasBandRadius := by
  have hp2 : Real.log 2 ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast p.2.two_le)
  have hlog := log_prime_pos p
  rw [jasR1, jasBandRadius, Real.exp_le_exp]
  rw [abs_le] at hs
  nlinarith

theorem jasR2_le_band {s : ℂ} (hs : |s.re - 1 / 2| ≤ 1 / 4) (p : Nat.Primes) :
    jasR2 s p ≤ jasBandRadius := by
  have hp2 : Real.log 2 ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast p.2.two_le)
  have hlog := log_prime_pos p
  rw [jasR2, jasBandRadius, Real.exp_le_exp]
  rw [abs_le] at hs
  nlinarith

/-- Radius gap within the band: `|p^{-σ} - p^{σ-1}| ≤ 8 |σ - 1/2|`. -/
theorem abs_jasR1_sub_jasR2_le {s : ℂ} (hs : |s.re - 1 / 2| ≤ 1 / 4) (p : Nat.Primes) :
    |jasR1 s p - jasR2 s p| ≤ 8 * |s.re - 1 / 2| := by
  set L := Real.log (p : ℝ) with hL
  have hlog : 0 < L := log_prime_pos p
  have habs := hs
  rw [abs_le] at hs
  -- exponential mean-value bound: |e^A - e^B| ≤ |A - B| e^{max A B}
  have hmv : ∀ A B : ℝ, B ≤ A → Real.exp A - Real.exp B ≤ (A - B) * Real.exp A := by
    intro A B hBA
    have := Real.add_one_le_exp (B - A)
    have hexp : Real.exp B = Real.exp A * Real.exp (B - A) := by
      rw [← Real.exp_add]; ring_nf
    rw [hexp]
    nlinarith [Real.exp_pos A]
  have hmaxA : -s.re * L ≤ -(L / 4) := by nlinarith
  have hmaxB : -(1 - s.re) * L ≤ -(L / 4) := by nlinarith
  have hLe : L * Real.exp (-(L / 4)) ≤ 4 := by
    have h1 := Real.add_one_le_exp (L / 4)
    have h2 : Real.exp (-(L / 4)) * Real.exp (L / 4) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-(L / 4)), Real.exp_pos (L / 4)]
  have hdiff : |(-s.re * L) - (-(1 - s.re) * L)| = 2 * |s.re - 1 / 2| * L := by
    rw [show (-s.re * L) - (-(1 - s.re) * L) = -(2 * (s.re - 1 / 2) * L) by ring, abs_neg,
      abs_mul, abs_mul, abs_of_pos hlog, abs_two]
  rcases le_total (-(1 - s.re) * L) (-s.re * L) with hle | hle
  · have := hmv _ _ hle
    rw [jasR1, jasR2, abs_of_nonneg (by linarith [Real.exp_le_exp.mpr hle])]
    calc Real.exp (-s.re * L) - Real.exp (-(1 - s.re) * L)
        ≤ ((-s.re * L) - (-(1 - s.re) * L)) * Real.exp (-s.re * L) := this
      _ ≤ (2 * |s.re - 1 / 2| * L) * Real.exp (-(L / 4)) := by
          apply mul_le_mul _ (Real.exp_le_exp.mpr hmaxA) (Real.exp_pos _).le (by positivity)
          rw [← hdiff]; exact le_abs_self _
      _ = 2 * |s.re - 1 / 2| * (L * Real.exp (-(L / 4))) := by ring
      _ ≤ 2 * |s.re - 1 / 2| * 4 := by gcongr
      _ = 8 * |s.re - 1 / 2| := by ring
  · have := hmv _ _ hle
    rw [jasR1, jasR2, abs_sub_comm, abs_of_nonneg (by linarith [Real.exp_le_exp.mpr hle])]
    calc Real.exp (-(1 - s.re) * L) - Real.exp (-s.re * L)
        ≤ ((-(1 - s.re) * L) - (-s.re * L)) * Real.exp (-(1 - s.re) * L) := this
      _ ≤ (2 * |s.re - 1 / 2| * L) * Real.exp (-(L / 4)) := by
          apply mul_le_mul _ (Real.exp_le_exp.mpr hmaxB) (Real.exp_pos _).le (by positivity)
          rw [← hdiff, abs_sub_comm]; exact le_abs_self _
      _ = 2 * |s.re - 1 / 2| * (L * Real.exp (-(L / 4))) := by ring
      _ ≤ 2 * |s.re - 1 / 2| * 4 := by gcongr
      _ = 8 * |s.re - 1 / 2| := by ring

/-- Polar decomposition of the local parameters: `a w = r₁ v` and `b w̄ = r₂ v̄`. -/
theorem jasHoloA_mul_eq (s : ℂ) (p : Nat.Primes) (w : ℂ) :
    jasHoloA s p * w = (jasR1 s p : ℂ) * (cexp (((-(s.im * Real.log p)) : ℝ) * I) * w) := by
  rw [jasHoloA, jasR1, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 2
  apply Complex.ext <;>
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring

theorem jasHoloB_mul_conj_eq (s : ℂ) (p : Nat.Primes) (w : ℂ) :
    jasHoloB s p * conj w =
      (jasR2 s p : ℂ) * conj (cexp (((-(s.im * Real.log p)) : ℝ) * I) * w) := by
  rw [jasHoloB, jasR2, Complex.ofReal_exp, map_mul, ← Complex.exp_conj, ← mul_assoc,
    ← Complex.exp_add]
  congr 2
  apply Complex.ext <;>
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re,
    Complex.conj_im] <;> ring

/-- Absolute band constant. -/
def jasBandConstant : ℝ :=
  Real.pi / 2 * (8 / (1 - jasBandRadius) ^ 2) / (2 / (1 + jasBandRadius) - 1)

theorem jasBandDenom_pos : 0 < 2 / (1 + jasBandRadius) - 1 := by
  have h1 := jasBandRadius_lt_one
  have h0 := jasBandRadius_pos
  rw [sub_pos, lt_div_iff₀ (by linarith)]
  linarith

theorem jasBandConstant_pos : 0 < jasBandConstant := by
  have h1 := jasBandRadius_lt_one
  have hpi := Real.pi_pos
  unfold jasBandConstant
  have : 0 < 1 - jasBandRadius := by linarith
  have := jasBandDenom_pos
  positivity

/-- **Uniform local phase bound** within the band `|σ - 1/2| ≤ 1/4`. -/
theorem abs_arg_jasHoloLocal_le {s : ℂ} (hs : |s.re - 1 / 2| ≤ 1 / 4) (p : Nat.Primes)
    {w : ℂ} (hw : ‖w‖ = 1) :
    |(jasHoloLocal (jasHoloA s p) (jasHoloB s p) w).arg| ≤ jasBandConstant * |s.re - 1 / 2| := by
  set ρ := jasBandRadius
  have hρ1 : ρ < 1 := jasBandRadius_lt_one
  set v : ℂ := cexp (((-(s.im * Real.log p)) : ℝ) * I) * w with hv
  have hvn : ‖v‖ = 1 := by rw [hv, norm_mul, Complex.norm_exp_ofReal_mul_I, hw, one_mul]
  have hr1 := jasR1_le_band hs p
  have hr2 := jasR2_le_band hs p
  have hr1p := (jasR1_pos s p).le
  have hr2p := (jasR2_pos s p).le
  have hl : jasHoloLocal (jasHoloA s p) (jasHoloB s p) w =
      (1 - (jasR1 s p : ℂ) * v)⁻¹ + conj ((1 - (jasR2 s p : ℂ) * v)⁻¹) - 1 := by
    rw [jasHoloLocal, jasHoloA_mul_eq, jasHoloB_mul_conj_eq, map_inv₀, map_sub, map_one,
      map_mul (starRingEnd ℂ) (jasR2 s p : ℂ) v, Complex.conj_ofReal]
  have hreF1 := inv_one_add_le_re_inv_one_sub (z := (jasR1 s p : ℂ) * v)
    (by rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr1p, hvn, mul_one]; exact hr1) hρ1
  have hreF2 := inv_one_add_le_re_inv_one_sub (z := (jasR2 s p : ℂ) * v)
    (by rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr2p, hvn, mul_one]; exact hr2) hρ1
  have hre : 2 / (1 + ρ) - 1 ≤ (jasHoloLocal (jasHoloA s p) (jasHoloB s p) w).re := by
    rw [hl, Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.one_re]
    have : 2 / (1 + ρ) = 1 / (1 + ρ) + 1 / (1 + ρ) := by ring
    linarith
  have him : |(jasHoloLocal (jasHoloA s p) (jasHoloB s p) w).im| ≤
      |jasR1 s p - jasR2 s p| / (1 - ρ) ^ 2 := by
    rw [hl, Complex.sub_im, Complex.add_im, Complex.conj_im, Complex.one_im, sub_zero,
      ← sub_eq_add_neg, ← Complex.sub_im]
    exact (Complex.abs_im_le_norm _).trans
      (norm_inv_one_sub_sub_le hvn hr1p hr2p hr1 hr2 hρ1)
  have hrepos : 0 < (jasHoloLocal (jasHoloA s p) (jasHoloB s p) w).re :=
    lt_of_lt_of_le jasBandDenom_pos hre
  have hgap := abs_jasR1_sub_jasR2_le hs p
  have hden : 0 < (1 - ρ) ^ 2 := by have : 0 < 1 - ρ := by linarith
                                    positivity
  calc |(jasHoloLocal (jasHoloA s p) (jasHoloB s p) w).arg|
      ≤ Real.pi / 2 * (|(jasHoloLocal (jasHoloA s p) (jasHoloB s p) w).im| /
          (jasHoloLocal (jasHoloA s p) (jasHoloB s p) w).re) := abs_arg_le_of_re_pos hrepos
    _ ≤ Real.pi / 2 * ((8 * |s.re - 1 / 2| / (1 - ρ) ^ 2) / (2 / (1 + ρ) - 1)) := by
        gcongr
        · exact jasBandDenom_pos
        · exact him.trans (div_le_div_of_nonneg_right hgap hden.le)
    _ = jasBandConstant * |s.re - 1 / 2| := by
        unfold jasBandConstant; ring

/-- **Bounded-depth positivity in the band.**  If `K · |P| · |σ - 1/2| < π/2`, every depth-`P`
explicit-formula density has positive real part. -/
theorem re_prod_jasHoloLocal_pos_of_band {s : ℂ} (hs : |s.re - 1 / 2| ≤ 1 / 4)
    (P : Finset Nat.Primes) (w : Nat.Primes → ℂ) (hw : ∀ p, ‖w p‖ = 1)
    (hsmall : jasBandConstant * P.card * |s.re - 1 / 2| < Real.pi / 2) :
    0 < (∏ p ∈ P, jasHoloLocal (jasHoloA s p) (jasHoloB s p) (w p)).re := by
  have hs0 : 0 < s.re := by rw [abs_le] at hs; linarith
  have hs1 : s.re < 1 := by rw [abs_le] at hs; linarith
  rw [prod_eq_prod_norm_mul_exp_sum_arg, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  apply mul_pos
  · refine Finset.prod_pos fun p _ => norm_pos_iff.mpr fun h => ?_
    have := re_jasHoloLocal_pos (norm_jasHoloA_lt_one hs0 p) (norm_jasHoloB_lt_one hs1 p) (hw p)
    rw [h, Complex.zero_re] at this
    exact lt_irrefl 0 this
  · apply Real.cos_pos_of_mem_Ioo
    have hsum : |∑ p ∈ P, (jasHoloLocal (jasHoloA s p) (jasHoloB s p) (w p)).arg| ≤
        jasBandConstant * P.card * |s.re - 1 / 2| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ p ∈ P, |(jasHoloLocal (jasHoloA s p) (jasHoloB s p) (w p)).arg|
          ≤ ∑ _p ∈ P, jasBandConstant * |s.re - 1 / 2| :=
            Finset.sum_le_sum fun p _ => abs_arg_jasHoloLocal_le hs p (hw p)
        _ = jasBandConstant * P.card * |s.re - 1 / 2| := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
    have := lt_of_le_of_lt hsum hsmall
    rw [abs_lt] at this
    exact ⟨this.1, this.2⟩

/-- **Blind band.**  For every depth `k` there is a band of half-width `η > 0` around the critical
line in which every strip point, on or off the line, has positive explicit-formula density at
every prime depth `≤ k`. -/
theorem exists_jasBlindBand (k : ℕ) :
    ∃ η > 0, ∀ s : ℂ, |s.re - 1 / 2| < η →
      ∀ (P : Finset Nat.Primes), P.card ≤ k → ∀ (w : Nat.Primes → ℂ), (∀ p, ‖w p‖ = 1) →
        0 < (∏ p ∈ P, jasHoloLocal (jasHoloA s p) (jasHoloB s p) (w p)).re := by
  have hK := jasBandConstant_pos
  refine ⟨min (1 / 4) (Real.pi / (4 * jasBandConstant * (k + 1))), lt_min (by norm_num)
    (by positivity), fun s hs P hP w hw => ?_⟩
  have hs4 : |s.re - 1 / 2| ≤ 1 / 4 := (lt_of_lt_of_le hs (min_le_left _ _)).le
  have hsη : |s.re - 1 / 2| < Real.pi / (4 * jasBandConstant * (k + 1)) :=
    lt_of_lt_of_le hs (min_le_right _ _)
  apply re_prod_jasHoloLocal_pos_of_band hs4 P w hw
  have hcard : (P.card : ℝ) ≤ k + 1 := by exact_mod_cast Nat.le_succ_of_le hP
  have hpos : 0 < 4 * jasBandConstant * ((k : ℝ) + 1) := by positivity
  rw [lt_div_iff₀ hpos] at hsη
  calc jasBandConstant * P.card * |s.re - 1 / 2|
      ≤ jasBandConstant * (k + 1) * |s.re - 1 / 2| := by gcongr
    _ < Real.pi / 2 := by nlinarith [Real.pi_pos, abs_nonneg (s.re - 1 / 2)]

/-- Xi zeros within the blind band are invisible to bounded-depth explicit-formula positivity. -/
theorem exists_xi_jasBlindBand (k : ℕ) :
    ∃ η > 0, ∀ rho : XiDivisorSupport, |(rho : ℂ).re - 1 / 2| < η →
      ∀ (P : Finset Nat.Primes), P.card ≤ k → ∀ (w : Nat.Primes → ℂ), (∀ p, ‖w p‖ = 1) →
        0 < (∏ p ∈ P, jasHoloLocal (jasHoloA (rho : ℂ) p) (jasHoloB (rho : ℂ) p) (w p)).re := by
  obtain ⟨η, hη, h⟩ := exists_jasBlindBand k
  exact ⟨η, hη, fun rho hrho => h _ hrho⟩

/-- **Detection depth diverges at the line.**  For every off-line strip point there is a finite
detecting prime set, but within the depth-`k` blind band every detecting set has more than `k`
primes. -/
theorem jasDetectionDepth_gt_of_band (k : ℕ) :
    ∃ η > 0, ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ 1 / 2 → |s.re - 1 / 2| < η →
      (∃ (P : Finset Nat.Primes) (w : Nat.Primes → ℂ), (∀ p, ‖w p‖ = 1) ∧
        (∏ p ∈ P, jasHoloLocal (jasHoloA s p) (jasHoloB s p) (w p)).re < 0) ∧
      ∀ (P : Finset Nat.Primes) (w : Nat.Primes → ℂ), (∀ p, ‖w p‖ = 1) →
        (∏ p ∈ P, jasHoloLocal (jasHoloA s p) (jasHoloB s p) (w p)).re < 0 → k < P.card := by
  obtain ⟨η, hη, h⟩ := exists_jasBlindBand k
  refine ⟨η, hη, fun s hs0 hs1 hoff hband => ⟨exists_re_prod_jasHoloLocal_neg hs0 hs1 hoff,
    fun P w hw hneg => ?_⟩⟩
  by_contra hle
  exact absurd (h s hband P (not_lt.mp hle) w hw) (not_lt.mpr hneg.le)

/-! ## Theta-point value -/

/-- Theta-point value of the local density. -/
theorem jasHoloLocal_one (a b : ℂ) (ha : a ≠ 1) (hb : b ≠ 1) :
    jasHoloLocal a b 1 = (1 - a * b) / ((1 - a) * (1 - b)) := by
  have h1 : (1 - a) ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  have h2 : (1 - b) ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
  rw [jasHoloLocal, map_one, mul_one, mul_one]
  field_simp
  ring

theorem jasHoloA_mul_jasHoloB (s : ℂ) (p : Nat.Primes) :
    jasHoloA s p * jasHoloB s p = (((p : ℝ)⁻¹ : ℝ) : ℂ) := by
  rw [jasHoloA, jasHoloB, ← Complex.exp_add,
    show -s * (Real.log p : ℂ) + -(1 - s) * (Real.log p : ℂ) = ((-Real.log p : ℝ) : ℂ) by
      push_cast; ring,
    ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log (by exact_mod_cast p.2.pos)]

/-- **Theta-point Euler law.**  At the theta point the depth-`P` explicit-formula density is
`∏ (1 - p⁻¹)/((1 - p^{-s})(1 - p^{-(1-s)}))`: the functional-equation-symmetric truncated Euler
product divided by the truncated pole. -/
theorem prod_jasHoloLocal_one {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (P : Finset Nat.Primes) :
    ∏ p ∈ P, jasHoloLocal (jasHoloA s p) (jasHoloB s p) 1 =
      ∏ p ∈ P, ((1 - (((p : ℝ)⁻¹ : ℝ) : ℂ)) /
        ((1 - jasHoloA s p) * (1 - jasHoloB s p))) := by
  refine Finset.prod_congr rfl fun p _ => ?_
  have ha : jasHoloA s p ≠ 1 := fun h => by
    have := norm_jasHoloA_lt_one hs0 p; rw [h, norm_one] at this; exact lt_irrefl 1 this
  have hb : jasHoloB s p ≠ 1 := fun h => by
    have := norm_jasHoloB_lt_one hs1 p; rw [h, norm_one] at this; exact lt_irrefl 1 this
  rw [jasHoloLocal_one _ _ ha hb, jasHoloA_mul_jasHoloB]

end

end RHTower
