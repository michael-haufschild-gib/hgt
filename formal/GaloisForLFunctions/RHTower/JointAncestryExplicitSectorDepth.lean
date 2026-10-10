import GaloisForLFunctions.RHTower.JointAncestryUnitResiduePoleTrace

/-!
# JAS explicit-formula sectors: positivity is lost only at multi-prime depth

The explicit formula sums, over the zeros `ρ`, the holomorphic sector whose Fourier coefficient
at a positive prime frequency `p^k` is `p^{-kρ}` and at the negative frequency `p^{-k}` is the
functional-equation partner `p^{-k(1-ρ)}`.  On one prime circle this sector has density

`ℓ_{a,b}(w) = (1 - a w)⁻¹ + (1 - b w̄)⁻¹ - 1`,   `a = p^{-s}`, `b = p^{-(1-s)}`,

and on a finite prime torus its density is the product of these local kernels.  The JAS
prime-Poisson sector has the same positive coefficients but the conjugate negative ones; the two
agree exactly when `b = ā`, i.e. on the critical line, where `ℓ` is the Poisson kernel.

This module proves the sharp depth law:

* **Depth one is always positive.**  For every strip point and every prime, `Re ℓ > 0`, because
  `w ↦ (1 - w)⁻¹` maps the unit disk into the half-plane `Re > 1/2`.
* **Critical line.**  For `Re s = 1/2` every finite product of local kernels is a positive real.
* **Finite depth detects every off-line point.**  For `Re s ≠ 1/2`, at the quarter point
  `a w = i|a|` the local kernel has argument at least `|p^{-σ} - p^{σ-1}|/16`.  These arguments
  are not summable over the primes, so a finite prime set accumulates total phase in `(π/2, π)`
  and the product density has negative real part there.

The divergence used is `Σ_p |p^{-σ} - p^{σ-1}| = ∞`, the first-moment form of the
`Σ_p (p^{-σ} - p^{σ-1})² = ∞` that drives prime-Poisson superselection.  Consequently RH is
equivalent to positivity of every Xi zero's explicit-formula sector at every finite prime depth,
and no single prime can witness a failure.
-/

open Complex Filter
open scoped ComplexConjugate Topology BigOperators

namespace RHTower

noncomputable section

/-- Local density of the explicit-formula sector on one prime circle. -/
def jasHoloLocal (a b w : ℂ) : ℂ := (1 - a * w)⁻¹ + (1 - b * conj w)⁻¹ - 1

/-- `(1 - z)⁻¹` maps the open unit disk into the half-plane `Re > 1/2`. -/
theorem half_lt_re_inv_one_sub {z : ℂ} (hz : ‖z‖ < 1) : 1 / 2 < ((1 - z)⁻¹).re := by
  have hre : z.re < 1 := lt_of_le_of_lt (Complex.re_le_norm z) hz
  have hsq : z.re ^ 2 + z.im ^ 2 < 1 := by
    have h := Complex.sq_norm z
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg z]
  rw [Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub]
  have hden : 0 < (1 - z.re) * (1 - z.re) + -z.im * -z.im := by nlinarith
  rw [lt_div_iff₀ hden]
  nlinarith

/-- **Depth one is positive**: the local explicit-formula density has positive real part. -/
theorem re_jasHoloLocal_pos {a b w : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (hw : ‖w‖ = 1) :
    0 < (jasHoloLocal a b w).re := by
  have h1 := half_lt_re_inv_one_sub (z := a * w) (by rw [norm_mul, hw, mul_one]; exact ha)
  have h2 := half_lt_re_inv_one_sub (z := b * conj w)
    (by rw [norm_mul, Complex.norm_conj, hw, mul_one]; exact hb)
  rw [jasHoloLocal, Complex.sub_re, Complex.add_re, Complex.one_re]
  linarith

/-- With conjugate parameters the local density is real. -/
theorem im_jasHoloLocal_conj (a w : ℂ) : (jasHoloLocal a (conj a) w).im = 0 := by
  have h : (1 - conj a * conj w)⁻¹ = conj ((1 - a * w)⁻¹) := by
    rw [map_inv₀, map_sub, map_one, map_mul]
  rw [jasHoloLocal, h, Complex.sub_im, Complex.add_im, Complex.conj_im, Complex.one_im]
  ring

/-- Local parameter `p^{-s}`. -/
def jasHoloA (s : ℂ) (p : Nat.Primes) : ℂ := cexp (-s * (Real.log p : ℂ))

/-- Functional-equation partner parameter `p^{-(1-s)}`. -/
def jasHoloB (s : ℂ) (p : Nat.Primes) : ℂ := cexp (-(1 - s) * (Real.log p : ℂ))

theorem norm_jasHoloA (s : ℂ) (p : Nat.Primes) :
    ‖jasHoloA s p‖ = Real.exp (-s.re * Real.log p) := by
  rw [jasHoloA, Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

theorem norm_jasHoloB (s : ℂ) (p : Nat.Primes) :
    ‖jasHoloB s p‖ = Real.exp (-(1 - s.re) * Real.log p) := by
  rw [jasHoloB, Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

theorem norm_jasHoloA_lt_one {s : ℂ} (hs0 : 0 < s.re) (p : Nat.Primes) : ‖jasHoloA s p‖ < 1 := by
  rw [norm_jasHoloA, Real.exp_lt_one_iff]
  nlinarith [log_prime_pos p]

theorem norm_jasHoloB_lt_one {s : ℂ} (hs1 : s.re < 1) (p : Nat.Primes) : ‖jasHoloB s p‖ < 1 := by
  rw [norm_jasHoloB, Real.exp_lt_one_iff]
  nlinarith [log_prime_pos p]

/-- On the critical line the partner parameter is the conjugate parameter. -/
theorem jasHoloB_eq_conj_jasHoloA {s : ℂ} (hs : s.re = 1 / 2) (p : Nat.Primes) :
    jasHoloB s p = conj (jasHoloA s p) := by
  rw [jasHoloB, jasHoloA, ← Complex.exp_conj]
  congr 1
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im, map_mul, map_neg, Complex.conj_ofReal, hs]
    ring
  · simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im, map_mul, map_neg, Complex.conj_ofReal, hs]
    ring

/-- **Critical line**: every finite product of local explicit-formula densities is a positive
real number. -/
theorem prod_jasHoloLocal_pos_of_critical {s : ℂ} (hs : s.re = 1 / 2) (P : Finset Nat.Primes)
    (w : Nat.Primes → ℂ) (hw : ∀ p, ‖w p‖ = 1) :
    (∏ p ∈ P, jasHoloLocal (jasHoloA s p) (jasHoloB s p) (w p)).im = 0 ∧
      0 < (∏ p ∈ P, jasHoloLocal (jasHoloA s p) (jasHoloB s p) (w p)).re := by
  have hloc : ∀ p, jasHoloLocal (jasHoloA s p) (jasHoloB s p) (w p) =
      (((jasHoloLocal (jasHoloA s p) (jasHoloB s p) (w p)).re : ℝ) : ℂ) := by
    intro p
    apply Complex.ext
    · simp
    · rw [Complex.ofReal_im, jasHoloB_eq_conj_jasHoloA hs]
      exact im_jasHoloLocal_conj _ _
  rw [Finset.prod_congr rfl fun p _ => hloc p, ← Complex.ofReal_prod]
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  exact Finset.prod_pos fun p _ =>
    re_jasHoloLocal_pos (norm_jasHoloA_lt_one (by rw [hs]; norm_num) p)
      (norm_jasHoloB_lt_one (by rw [hs]; norm_num) p) (hw p)

/-! ## The quarter point -/

/-- Quarter point on the circle at prime `p`, with sign `ε = ±1`. -/
def jasQuarterPoint (s : ℂ) (p : Nat.Primes) (ε : ℝ) : ℂ :=
  (ε : ℂ) * I * cexp (((s.im * Real.log p : ℝ) : ℂ) * I)

theorem norm_jasQuarterPoint (s : ℂ) (p : Nat.Primes) {ε : ℝ} (hε : |ε| = 1) :
    ‖jasQuarterPoint s p ε‖ = 1 := by
  rw [jasQuarterPoint, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    hε, Complex.norm_exp_ofReal_mul_I]
  ring

/-- Radii `r₁ = p^{-σ}` and `r₂ = p^{σ-1}`. -/
def jasR1 (s : ℂ) (p : Nat.Primes) : ℝ := Real.exp (-s.re * Real.log p)

def jasR2 (s : ℂ) (p : Nat.Primes) : ℝ := Real.exp (-(1 - s.re) * Real.log p)

theorem jasHoloA_mul_quarter (s : ℂ) (p : Nat.Primes) (ε : ℝ) :
    jasHoloA s p * jasQuarterPoint s p ε = (ε : ℂ) * I * (jasR1 s p : ℂ) := by
  rw [jasHoloA, jasQuarterPoint, jasR1, Complex.ofReal_exp]
  have h : cexp (-s * (Real.log p : ℂ)) * cexp (((s.im * Real.log p : ℝ) : ℂ) * I) =
      cexp (((-s.re * Real.log p : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring
  calc cexp (-s * (Real.log p : ℂ)) * ((ε : ℂ) * I * cexp (((s.im * Real.log p : ℝ) : ℂ) * I))
      = (ε : ℂ) * I * (cexp (-s * (Real.log p : ℂ)) *
          cexp (((s.im * Real.log p : ℝ) : ℂ) * I)) := by ring
    _ = _ := by rw [h]

theorem jasHoloB_mul_conj_quarter (s : ℂ) (p : Nat.Primes) (ε : ℝ) :
    jasHoloB s p * conj (jasQuarterPoint s p ε) = -((ε : ℂ) * I * (jasR2 s p : ℂ)) := by
  rw [jasHoloB, jasQuarterPoint, jasR2, Complex.ofReal_exp, map_mul, map_mul,
    Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  have h : cexp (-(1 - s) * (Real.log p : ℂ)) * cexp (((s.im * Real.log p : ℝ) : ℂ) * -I) =
      cexp (((-(1 - s.re) * Real.log p : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
      Complex.neg_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring
  calc cexp (-(1 - s) * (Real.log p : ℂ)) *
        ((ε : ℂ) * -I * cexp (((s.im * Real.log p : ℝ) : ℂ) * -I))
      = -((ε : ℂ) * I * (cexp (-(1 - s) * (Real.log p : ℂ)) *
          cexp (((s.im * Real.log p : ℝ) : ℂ) * -I))) := by ring
    _ = _ := by rw [h]

/-- Real part of the local density at the quarter point. -/
def jasQuarterRe (r₁ r₂ : ℝ) : ℝ := 1 / (1 + r₁ ^ 2) + 1 / (1 + r₂ ^ 2) - 1

/-- Imaginary part (for sign `+1`) of the local density at the quarter point. -/
def jasQuarterIm (r₁ r₂ : ℝ) : ℝ := r₁ / (1 + r₁ ^ 2) - r₂ / (1 + r₂ ^ 2)

theorem inv_one_sub_I_mul (r : ℝ) :
    (1 - I * (r : ℂ))⁻¹ = ((1 / (1 + r ^ 2) : ℝ) : ℂ) + I * ((r / (1 + r ^ 2) : ℝ) : ℂ) := by
  have hr : (1 + (r : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast (by positivity : (0 : ℝ) < 1 + r ^ 2).ne'
  have key : (((1 / (1 + r ^ 2) : ℝ) : ℂ) + I * ((r / (1 + r ^ 2) : ℝ) : ℂ)) *
      (1 - I * (r : ℂ)) = 1 := by
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  exact (eq_inv_of_mul_eq_one_left key).symm

theorem jasHoloLocal_quarter (s : ℂ) (p : Nat.Primes) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    jasHoloLocal (jasHoloA s p) (jasHoloB s p) (jasQuarterPoint s p ε) =
      ((jasQuarterRe (jasR1 s p) (jasR2 s p) : ℝ) : ℂ) +
        I * ((ε * jasQuarterIm (jasR1 s p) (jasR2 s p) : ℝ) : ℂ) := by
  rw [jasHoloLocal, jasHoloA_mul_quarter, jasHoloB_mul_conj_quarter, sub_neg_eq_add]
  rcases hε with rfl | rfl
  · rw [show (1 : ℂ) - ((1 : ℝ) : ℂ) * I * (jasR1 s p : ℂ) = 1 - I * (jasR1 s p : ℂ) by push_cast; ring,
      show (1 : ℂ) + ((1 : ℝ) : ℂ) * I * (jasR2 s p : ℂ) = 1 - I * ((-jasR2 s p : ℝ) : ℂ) by
        push_cast; ring,
      inv_one_sub_I_mul, inv_one_sub_I_mul]
    simp only [jasQuarterRe, jasQuarterIm]
    push_cast
    ring
  · rw [show (1 : ℂ) - ((-1 : ℝ) : ℂ) * I * (jasR1 s p : ℂ) = 1 - I * ((-jasR1 s p : ℝ) : ℂ) by
        push_cast; ring,
      show (1 : ℂ) + ((-1 : ℝ) : ℂ) * I * (jasR2 s p : ℂ) = 1 - I * (jasR2 s p : ℂ) by
        push_cast; ring,
      inv_one_sub_I_mul, inv_one_sub_I_mul]
    simp only [jasQuarterRe, jasQuarterIm]
    push_cast
    ring

theorem jasQuarterIm_eq (r₁ r₂ : ℝ) :
    jasQuarterIm r₁ r₂ = (r₁ - r₂) * (1 - r₁ * r₂) / ((1 + r₁ ^ 2) * (1 + r₂ ^ 2)) := by
  rw [jasQuarterIm]
  field_simp
  ring

theorem jasR1_mul_jasR2 (s : ℂ) (p : Nat.Primes) : jasR1 s p * jasR2 s p = (p : ℝ)⁻¹ := by
  rw [jasR1, jasR2, ← Real.exp_add,
    show -s.re * Real.log p + -(1 - s.re) * Real.log p = -Real.log p by ring,
    Real.exp_neg, Real.exp_log (by exact_mod_cast p.2.pos)]

theorem jasR1_pos (s : ℂ) (p : Nat.Primes) : 0 < jasR1 s p := Real.exp_pos _

theorem jasR2_pos (s : ℂ) (p : Nat.Primes) : 0 < jasR2 s p := Real.exp_pos _

theorem jasR1_lt_one {s : ℂ} (hs0 : 0 < s.re) (p : Nat.Primes) : jasR1 s p < 1 := by
  rw [jasR1, Real.exp_lt_one_iff]; nlinarith [log_prime_pos p]

theorem jasR2_lt_one {s : ℂ} (hs1 : s.re < 1) (p : Nat.Primes) : jasR2 s p < 1 := by
  rw [jasR2, Real.exp_lt_one_iff]; nlinarith [log_prime_pos p]

/-- The quarter-point imaginary part controls the radius gap. -/
theorem abs_sub_div_eight_le_abs_jasQuarterIm {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (p : Nat.Primes) :
    |jasR1 s p - jasR2 s p| / 8 ≤ |jasQuarterIm (jasR1 s p) (jasR2 s p)| := by
  have h1 := jasR1_pos s p
  have h2 := jasR2_pos s p
  have h1' := jasR1_lt_one hs0 p
  have h2' := jasR2_lt_one hs1 p
  have hprod : jasR1 s p * jasR2 s p ≤ 1 / 2 := by
    rw [jasR1_mul_jasR2]
    exact inv_prime_le_half p
  rw [jasQuarterIm_eq, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) <
      (1 + jasR1 s p ^ 2) * (1 + jasR2 s p ^ 2)), abs_of_pos (by linarith : (0 : ℝ) <
      1 - jasR1 s p * jasR2 s p)]
  rw [le_div_iff₀ (by positivity)]
  have hd : (1 + jasR1 s p ^ 2) * (1 + jasR2 s p ^ 2) ≤ 4 := by
    have a1 : 1 + jasR1 s p ^ 2 ≤ 2 := by nlinarith
    have a2 : 1 + jasR2 s p ^ 2 ≤ 2 := by nlinarith
    calc (1 + jasR1 s p ^ 2) * (1 + jasR2 s p ^ 2) ≤ 2 * 2 :=
          mul_le_mul a1 a2 (by positivity) (by norm_num)
      _ = 4 := by norm_num
  nlinarith [abs_nonneg (jasR1 s p - jasR2 s p)]

/-- The radius gap is at least a fixed multiple of `1/p` off the critical line. -/
theorem exists_pos_le_abs_jasR1_sub_jasR2 {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hoff : s.re ≠ 1 / 2) :
    ∃ c > 0, ∀ p : Nat.Primes, c * (p : ℝ)⁻¹ ≤ |jasR1 s p - jasR2 s p| := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases lt_or_gt_of_ne hoff with hlt | hgt
  · refine ⟨1 - Real.exp ((2 * s.re - 1) * Real.log 2),
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith)), fun p => ?_⟩
    have hp := log_prime_pos p
    have hp2 : Real.log 2 ≤ Real.log (p : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast p.2.two_le)
    have hratio : jasR2 s p = jasR1 s p * Real.exp ((2 * s.re - 1) * Real.log p) := by
      rw [jasR1, jasR2, ← Real.exp_add]; congr 1; ring
    have hmono : Real.exp ((2 * s.re - 1) * Real.log p) ≤
        Real.exp ((2 * s.re - 1) * Real.log 2) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hR1 : (p : ℝ)⁻¹ ≤ jasR1 s p := by
      rw [jasR1, show ((p : ℕ) : ℝ)⁻¹ = Real.exp (-Real.log p) by
        rw [Real.exp_neg, Real.exp_log (by exact_mod_cast p.2.pos)]]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hc0 : 0 ≤ 1 - Real.exp ((2 * s.re - 1) * Real.log 2) := by
      rw [sub_nonneg, Real.exp_le_one_iff]; nlinarith
    rw [hratio, abs_of_nonneg (by nlinarith [jasR1_pos s p, Real.exp_pos ((2 * s.re - 1) * Real.log p)])]
    nlinarith [jasR1_pos s p]
  · refine ⟨1 - Real.exp ((1 - 2 * s.re) * Real.log 2),
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith)), fun p => ?_⟩
    have hp := log_prime_pos p
    have hp2 : Real.log 2 ≤ Real.log (p : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast p.2.two_le)
    have hratio : jasR1 s p = jasR2 s p * Real.exp ((1 - 2 * s.re) * Real.log p) := by
      rw [jasR1, jasR2, ← Real.exp_add]; congr 1; ring
    have hmono : Real.exp ((1 - 2 * s.re) * Real.log p) ≤
        Real.exp ((1 - 2 * s.re) * Real.log 2) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hR2 : (p : ℝ)⁻¹ ≤ jasR2 s p := by
      rw [jasR2, show ((p : ℕ) : ℝ)⁻¹ = Real.exp (-Real.log p) by
        rw [Real.exp_neg, Real.exp_log (by exact_mod_cast p.2.pos)]]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hc0 : 0 ≤ 1 - Real.exp ((1 - 2 * s.re) * Real.log 2) := by
      rw [sub_nonneg, Real.exp_le_one_iff]; nlinarith
    rw [hratio, abs_sub_comm, abs_of_nonneg (by nlinarith [jasR2_pos s p, Real.exp_pos ((1 - 2 * s.re) * Real.log p)])]
    nlinarith [jasR2_pos s p]

/-- Signed quarter point making the imaginary part nonnegative. -/
def jasQuarterSign (s : ℂ) (p : Nat.Primes) : ℝ :=
  if 0 ≤ jasQuarterIm (jasR1 s p) (jasR2 s p) then 1 else -1

theorem jasQuarterSign_cases (s : ℂ) (p : Nat.Primes) :
    jasQuarterSign s p = 1 ∨ jasQuarterSign s p = -1 := by
  unfold jasQuarterSign; split <;> simp

theorem jasQuarterSign_mul_im (s : ℂ) (p : Nat.Primes) :
    jasQuarterSign s p * jasQuarterIm (jasR1 s p) (jasR2 s p) =
      |jasQuarterIm (jasR1 s p) (jasR2 s p)| := by
  unfold jasQuarterSign
  split
  · rename_i h; rw [one_mul, abs_of_nonneg h]
  · rename_i h; rw [abs_of_neg (lt_of_not_ge h)]; ring

/-- Local density at the signed quarter point. -/
def jasQuarterValue (s : ℂ) (p : Nat.Primes) : ℂ :=
  jasHoloLocal (jasHoloA s p) (jasHoloB s p) (jasQuarterPoint s p (jasQuarterSign s p))

theorem jasQuarterValue_eq (s : ℂ) (p : Nat.Primes) :
    jasQuarterValue s p = ((jasQuarterRe (jasR1 s p) (jasR2 s p) : ℝ) : ℂ) +
      I * ((|jasQuarterIm (jasR1 s p) (jasR2 s p)| : ℝ) : ℂ) := by
  rw [jasQuarterValue, jasHoloLocal_quarter s p _ (jasQuarterSign_cases s p),
    jasQuarterSign_mul_im]

theorem jasQuarterValue_re {s : ℂ} (p : Nat.Primes) :
    (jasQuarterValue s p).re = jasQuarterRe (jasR1 s p) (jasR2 s p) := by
  rw [jasQuarterValue_eq]; simp

theorem jasQuarterValue_im {s : ℂ} (p : Nat.Primes) :
    (jasQuarterValue s p).im = |jasQuarterIm (jasR1 s p) (jasR2 s p)| := by
  rw [jasQuarterValue_eq]; simp

theorem jasQuarterValue_re_pos {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (p : Nat.Primes) :
    0 < (jasQuarterValue s p).re := by
  rw [jasQuarterValue]
  exact re_jasHoloLocal_pos (norm_jasHoloA_lt_one hs0 p) (norm_jasHoloB_lt_one hs1 p)
    (norm_jasQuarterPoint s p (by rcases jasQuarterSign_cases s p with h | h <;> rw [h] <;> simp))

theorem norm_jasQuarterValue_le_two {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (p : Nat.Primes) :
    ‖jasQuarterValue s p‖ ≤ 2 := by
  have h1 := jasR1_pos s p
  have h2 := jasR2_pos s p
  have hre : |(jasQuarterValue s p).re| ≤ 1 := by
    rw [jasQuarterValue_re, jasQuarterRe, abs_le]
    constructor
    · have : 0 < 1 / (1 + jasR1 s p ^ 2) := by positivity
      have : 0 < 1 / (1 + jasR2 s p ^ 2) := by positivity
      linarith
    · have : 1 / (1 + jasR1 s p ^ 2) ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith
      have : 1 / (1 + jasR2 s p ^ 2) ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith
      linarith
  have him : |(jasQuarterValue s p).im| ≤ 1 := by
    rw [jasQuarterValue_im, abs_abs, jasQuarterIm, abs_le]
    constructor <;>
    · have e1 : jasR1 s p / (1 + jasR1 s p ^ 2) ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith
      have e2 : jasR2 s p / (1 + jasR2 s p ^ 2) ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith
      have f1 : 0 ≤ jasR1 s p / (1 + jasR1 s p ^ 2) := by positivity
      have f2 : 0 ≤ jasR2 s p / (1 + jasR2 s p ^ 2) := by positivity
      linarith
  calc ‖jasQuarterValue s p‖ ≤ |(jasQuarterValue s p).re| + |(jasQuarterValue s p).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 := by linarith

/-- The quarter-point phase controls the radius gap. -/
theorem arg_jasQuarterValue_ge {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (p : Nat.Primes) :
    |jasR1 s p - jasR2 s p| / 16 ≤ (jasQuarterValue s p).arg := by
  have hre := jasQuarterValue_re_pos hs0 hs1 p
  have hne : jasQuarterValue s p ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hre; exact lt_irrefl 0 hre
  have hnorm := norm_jasQuarterValue_le_two hs0 hs1 p
  have hnpos : 0 < ‖jasQuarterValue s p‖ := norm_pos_iff.mpr hne
  have hargnn : 0 ≤ (jasQuarterValue s p).arg := by
    rw [Complex.arg_nonneg_iff, jasQuarterValue_im]; exact abs_nonneg _
  have hsin := Complex.sin_arg (jasQuarterValue s p)
  have hle := Real.sin_le hargnn
  have himb := abs_sub_div_eight_le_abs_jasQuarterIm hs0 hs1 p
  rw [jasQuarterValue_im] at hsin
  have : |jasQuarterIm (jasR1 s p) (jasR2 s p)| / 2 ≤
      |jasQuarterIm (jasR1 s p) (jasR2 s p)| / ‖jasQuarterValue s p‖ := by
    apply div_le_div_of_nonneg_left (abs_nonneg _) hnpos hnorm
  linarith

theorem arg_jasQuarterValue_lt {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (p : Nat.Primes) :
    (jasQuarterValue s p).arg < Real.pi / 2 :=
  Complex.arg_lt_pi_div_two_iff.mpr (Or.inl (jasQuarterValue_re_pos hs0 hs1 p))

/-- Off the critical line the quarter-point phases over the primes are not summable. -/
theorem not_summable_arg_jasQuarterValue {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hoff : s.re ≠ 1 / 2) :
    ¬ Summable (fun n : ℕ => (jasQuarterValue s (nthPrimeSubtype n)).arg) := by
  obtain ⟨c, hc, hgap⟩ := exists_pos_le_abs_jasR1_sub_jasR2 hs0 hs1 hoff
  intro hsum
  have hprime : Summable (fun p : Nat.Primes => (jasQuarterValue s p).arg) :=
    nthPrimeEquiv.summable_iff.mp hsum
  apply Nat.Primes.not_summable_one_div
  have hbound : Summable (fun p : Nat.Primes => (16 / c) * (jasQuarterValue s p).arg) :=
    hprime.mul_left _
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) hbound
  have h1 := hgap p
  have h2 := arg_jasQuarterValue_ge hs0 hs1 p
  rw [one_div]
  rw [show (16 / c) * (jasQuarterValue s p).arg = (16 * (jasQuarterValue s p).arg) / c by ring,
    le_div_iff₀ hc]
  linarith

/-- Product of nonzero complex numbers in polar form. -/
theorem prod_eq_prod_norm_mul_exp_sum_arg {ι : Type*} (t : Finset ι) (z : ι → ℂ) :
    ∏ i ∈ t, z i = ((∏ i ∈ t, ‖z i‖ : ℝ) : ℂ) * cexp ((∑ i ∈ t, (z i).arg : ℝ) * I) := by
  rw [Complex.ofReal_prod, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => (Complex.norm_mul_exp_arg_mul_I (z i)).symm

/-- **Finite depth detects every off-line strip point.**  Off the critical line some finite
prime set and some point of its torus give the explicit-formula density a negative real part. -/
theorem exists_re_prod_jasHoloLocal_neg {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hoff : s.re ≠ 1 / 2) :
    ∃ (P : Finset Nat.Primes) (w : Nat.Primes → ℂ), (∀ p, ‖w p‖ = 1) ∧
      (∏ p ∈ P, jasHoloLocal (jasHoloA s p) (jasHoloB s p) (w p)).re < 0 := by
  classical
  set φ : ℕ → ℝ := fun n => (jasQuarterValue s (nthPrimeSubtype n)).arg with hφ
  have hφnn : ∀ n, 0 ≤ φ n := fun n => by
    simp only [hφ]
    rw [Complex.arg_nonneg_iff, jasQuarterValue_im]; exact abs_nonneg _
  have hφlt : ∀ n, φ n < Real.pi / 2 := fun n => arg_jasQuarterValue_lt hs0 hs1 _
  have htend : Tendsto (fun N => ∑ n ∈ Finset.range N, φ n) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hφnn).mp
      (not_summable_arg_jasQuarterValue hs0 hs1 hoff)
  have hex : ∃ N, Real.pi / 2 < ∑ n ∈ Finset.range N, φ n :=
    (htend.eventually_gt_atTop (Real.pi / 2)).exists
  set N := Nat.find hex with hN
  have hNspec : Real.pi / 2 < ∑ n ∈ Finset.range N, φ n := Nat.find_spec hex
  have hNpos : N ≠ 0 := by
    intro h0
    rw [h0, Finset.sum_range_zero] at hNspec
    linarith [Real.pi_pos]
  obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero hNpos
  have hprev : ∑ n ∈ Finset.range M, φ n ≤ Real.pi / 2 := by
    have := Nat.find_min hex (show M < N by omega)
    exact le_of_not_gt this
  have hupper : ∑ n ∈ Finset.range N, φ n < Real.pi := by
    rw [hM, Finset.sum_range_succ]
    linarith [hφlt M]
  refine ⟨(Finset.range N).image nthPrimeSubtype,
    fun p => jasQuarterPoint s p (jasQuarterSign s p),
    fun p => norm_jasQuarterPoint s p (by rcases jasQuarterSign_cases s p with h | h <;>
      rw [h] <;> simp), ?_⟩
  have hinj : ∀ x ∈ Finset.range N, ∀ y ∈ Finset.range N,
      nthPrimeSubtype x = nthPrimeSubtype y → x = y :=
    fun x _ y _ h => nthPrimeEquiv.injective h
  rw [Finset.prod_image hinj]
  change (∏ n ∈ Finset.range N, jasQuarterValue s (nthPrimeSubtype n)).re < 0
  rw [prod_eq_prod_norm_mul_exp_sum_arg, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  apply mul_neg_of_pos_of_neg
  · refine Finset.prod_pos fun n _ => norm_pos_iff.mpr ?_
    intro h
    have := jasQuarterValue_re_pos hs0 hs1 (nthPrimeSubtype n)
    rw [h, Complex.zero_re] at this
    exact lt_irrefl 0 this
  · exact Real.cos_neg_of_pi_div_two_lt_of_lt hNspec (by linarith [Real.pi_pos])

/-- **Depth classification.**  A strip point's explicit-formula sector has nonnegative real
density at every finite prime depth exactly on the critical line. -/
theorem forall_re_prod_jasHoloLocal_nonneg_iff {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    (∀ (P : Finset Nat.Primes) (w : Nat.Primes → ℂ), (∀ p, ‖w p‖ = 1) →
      0 ≤ (∏ p ∈ P, jasHoloLocal (jasHoloA s p) (jasHoloB s p) (w p)).re) ↔
      s.re = 1 / 2 := by
  constructor
  · intro h
    by_contra hoff
    obtain ⟨P, w, hw, hneg⟩ := exists_re_prod_jasHoloLocal_neg hs0 hs1 hoff
    exact absurd (h P w hw) (not_le.mpr hneg)
  · intro hs P w hw
    exact (prod_jasHoloLocal_pos_of_critical hs P w hw).2.le

/-- RH is equivalent to positivity of every Xi zero's explicit-formula sector at every finite
prime depth.  Depth one never detects a failure. -/
theorem forall_xi_re_prod_jasHoloLocal_nonneg_iff_riemannHypothesis :
    (∀ (rho : XiDivisorSupport) (P : Finset Nat.Primes) (w : Nat.Primes → ℂ),
      (∀ p, ‖w p‖ = 1) →
        0 ≤ (∏ p ∈ P, jasHoloLocal (jasHoloA (rho : ℂ) p) (jasHoloB (rho : ℂ) p) (w p)).re) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
    intro rho
    have hstrip := xi_divisor_support_re_mem_open_unit rho
    exact (forall_re_prod_jasHoloLocal_nonneg_iff hstrip.1 hstrip.2).1 (h rho)
  · intro hRH rho P w hw
    have hstrip := xi_divisor_support_re_mem_open_unit rho
    exact (forall_re_prod_jasHoloLocal_nonneg_iff hstrip.1 hstrip.2).2
      (xi_divisor_support_re_eq_half_of_rh hRH rho) P w hw

end

end RHTower
