import GaloisForLFunctions.BezoutValuationIncidence.CyclotomicLogarithmFormulaForThePronicGram

/-!
# The cotangent–sawtooth form of the pronic Gram

The cyclotomic-logarithm formula collapses further. With `a_ζ = ζ/(ζ - 1)` and
`Q(z) = (1 - z) log(1 - z)/z`,

`a_ζ a_ξ Q(ζξ) = κ(ζ, ξ) log(1 - ζξ)`,  `κ(ζ, ξ) = 1/(1 - ζ) + 1/(1 - ξ) - 1`,

because `1 - ζξ = (1 - ζ) + ζ(1 - ξ)`. On the unit circle `Re 1/(1 - ζ) = 1/2`, so `κ` is purely
imaginary and the log-modulus parts `log |1 - ζξ|` cancel from the real Gram: only arguments
survive. With `Im 1/(1 - e(x)) = cot(πx)/2` and `arg(1 - e(t)) = π((t))`, where `((t))` is the
sawtooth (zero at integers), this gives, for all moduli `p, q ≥ 2`,

`G^{mc}(p, q) = φ(p) φ(q)/4 - (π/2) Σ_{(a,p)=1} Σ_{(b,q)=1} (cot(πa/p) + cot(πb/q)) ((a/p + b/q))`.

The pronic Gram is an elementary finite cotangent–sawtooth sum: Dedekind–Vasyunin sums
`Σ cot(πa/k) ((ha/k))` in two moduli.
-/

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- The sawtooth `((y)) = {y} - 1/2`, set to zero at integers. -/
def sawtooth (y : ℝ) : ℝ := if Int.fract y = 0 then 0 else Int.fract y - 1 / 2

/-! ## §1. The cotangent kernel -/

/-- `a_ζ a_ξ Q(ζξ) = (1/(1 - ζ) + 1/(1 - ξ) - 1) log(1 - ζξ)`, including `ζξ = 1`. -/
theorem div_mul_div_mul_cyclotomicLogKernel {ζ ξ : ℂ} (hζ0 : ζ ≠ 0) (hξ0 : ξ ≠ 0)
    (hζ1 : ζ ≠ 1) (hξ1 : ξ ≠ 1) :
    ζ / (ζ - 1) * (ξ / (ξ - 1)) * cyclotomicLogKernel (ζ * ξ) =
      (1 / (1 - ζ) + 1 / (1 - ξ) - 1) * log (1 - ζ * ξ) := by
  unfold cyclotomicLogKernel
  split_ifs with h
  · rw [h, sub_self, Complex.log_zero]
    simp
  · have h1 : 1 - ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm hζ1)
    have h2 : 1 - ξ ≠ 0 := sub_ne_zero.mpr (Ne.symm hξ1)
    have h3 : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ1
    have h4 : ξ - 1 ≠ 0 := sub_ne_zero.mpr hξ1
    field_simp
    ring

/-- On the unit circle `Re 1/(1 - ζ) = 1/2`. -/
theorem re_one_div_one_sub {ζ : ℂ} (hζ : ‖ζ‖ = 1) (hζ1 : ζ ≠ 1) : (1 / (1 - ζ)).re = 1 / 2 := by
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ
  have hconj : conj ζ = ζ⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hζ]
    simp
  have h1 : 1 - ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm hζ1)
  have h2 : 1 - ζ⁻¹ ≠ 0 := sub_ne_zero.mpr (by rwa [Ne, eq_comm, inv_eq_one])
  have hsum : 1 / (1 - ζ) + conj (1 / (1 - ζ)) = 1 := by
    rw [map_div₀, map_one, map_sub, map_one, hconj]
    field_simp
    ring
  have h := Complex.re_eq_add_conj (1 / (1 - ζ))
  rw [hsum] at h
  have h' : (((1 / (1 - ζ)).re : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by rw [h]; push_cast; ring
  exact Complex.ofReal_injective h'

/-! ## §2. Explicit trigonometric values -/

theorem exp_two_pi_mul_I_re_im (x : ℝ) :
    (cexp (2 * Real.pi * I * x)).re = Real.cos (2 * (Real.pi * x)) ∧
      (cexp (2 * Real.pi * I * x)).im = Real.sin (2 * (Real.pi * x)) := by
  have h : (2 * Real.pi * I * x : ℂ) = ((2 * (Real.pi * x) : ℝ) : ℂ) * I := by push_cast; ring
  rw [h]
  exact ⟨Complex.exp_ofReal_mul_I_re _, Complex.exp_ofReal_mul_I_im _⟩

/-- `1 - e(x) = 2 sin²(πx) - 2i sin(πx) cos(πx)`. -/
theorem one_sub_exp_re_im (x : ℝ) :
    (1 - cexp (2 * Real.pi * I * x)).re = 2 * Real.sin (Real.pi * x) ^ 2 ∧
      (1 - cexp (2 * Real.pi * I * x)).im =
        -(2 * Real.sin (Real.pi * x) * Real.cos (Real.pi * x)) := by
  obtain ⟨hre, him⟩ := exp_two_pi_mul_I_re_im x
  have hpy := Real.sin_sq_add_cos_sq (Real.pi * x)
  simp only [sub_re, one_re, sub_im, one_im, hre, him, Real.cos_two_mul, Real.sin_two_mul]
  constructor <;> nlinarith [hpy]

/-- `Im 1/(1 - e(x)) = cot(πx)/2` when `sin πx ≠ 0`. -/
theorem im_one_div_one_sub_exp {x : ℝ} (hs : Real.sin (Real.pi * x) ≠ 0) :
    (1 / (1 - cexp (2 * Real.pi * I * x))).im = Real.cot (Real.pi * x) / 2 := by
  obtain ⟨hre, him⟩ := one_sub_exp_re_im x
  have hpy := Real.sin_sq_add_cos_sq (Real.pi * x)
  set w : ℂ := ((1 / 2 : ℝ) : ℂ) + ((Real.cos (Real.pi * x) / (2 * Real.sin (Real.pi * x)) : ℝ) : ℂ) * I
  have hw : (1 - cexp (2 * Real.pi * I * x)) * w = 1 := by
    apply Complex.ext
    · simp only [mul_re, hre, him, w, add_re, add_im, ofReal_re, ofReal_im, mul_im, I_re, I_im,
        one_re]
      field_simp
      nlinarith [hpy]
    · simp only [mul_im, hre, him, w, add_re, add_im, ofReal_re, ofReal_im, mul_re, I_re, I_im,
        one_im]
      field_simp
      ring
  rw [← eq_one_div_of_mul_eq_one_right hw, Real.cot_eq_cos_div_sin]
  simp only [w, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im]
  field_simp
  ring

/-- `arg(1 - e(y)) = π ((y))`. -/
theorem arg_one_sub_exp (y : ℝ) :
    (1 - cexp (2 * Real.pi * I * y)).arg = Real.pi * sawtooth y := by
  have hper : cexp (2 * Real.pi * I * y) = cexp (2 * Real.pi * I * (Int.fract y : ℝ)) := by
    have hy : ((y : ℝ) : ℂ) = ((⌊y⌋ : ℤ) : ℂ) + ((Int.fract y : ℝ) : ℂ) := by
      rw [← Complex.ofReal_intCast, ← Complex.ofReal_add, Int.floor_add_fract]
    rw [hy, mul_add, Complex.exp_add, mul_comm (2 * ↑Real.pi * I) ((⌊y⌋ : ℤ) : ℂ),
      Complex.exp_int_mul_two_pi_mul_I, one_mul]
  rw [hper, sawtooth]
  split_ifs with h0
  · rw [h0]
    simp
  · set t := Int.fract y
    have ht0 : 0 < t := lt_of_le_of_ne (Int.fract_nonneg y) (Ne.symm h0)
    have ht1 : t < 1 := Int.fract_lt_one y
    have hs : 0 < Real.sin (Real.pi * t) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
    obtain ⟨hre, him⟩ := one_sub_exp_re_im t
    have hrot : 1 - cexp (2 * Real.pi * I * t) =
        ((2 * Real.sin (Real.pi * t) : ℝ) : ℂ) *
          (Complex.cos ((Real.pi * (t - 1 / 2) : ℝ) : ℂ) +
            Complex.sin ((Real.pi * (t - 1 / 2) : ℝ) : ℂ) * I) := by
      rw [← Complex.ofReal_cos, ← Complex.ofReal_sin,
        show Real.pi * (t - 1 / 2) = Real.pi * t - Real.pi / 2 by ring,
        Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two]
      apply Complex.ext
      · simp only [hre, mul_re, add_re, ofReal_re, ofReal_im, mul_im, I_re, I_im, add_im]
        ring
      · simp only [him, mul_im, add_re, ofReal_re, ofReal_im, mul_re, I_re, I_im, add_im]
        ring
    rw [hrot, Complex.arg_mul_cos_add_sin_mul_I (by positivity)]
    constructor <;> nlinarith [Real.pi_pos]

/-! ## §3. Parametrizing primitive roots -/

theorem primitiveRoots_eq_image {k : ℕ} (hk : 0 < k) :
    primitiveRoots k ℂ = ((range k).filter fun i => i.Coprime k).image
      fun i : ℕ => cexp (2 * Real.pi * I * ((i : ℝ) / k : ℝ)) := by
  ext ζ
  rw [mem_primitiveRoots hk, Complex.isPrimitiveRoot_iff ζ k hk.ne', mem_image]
  constructor
  · rintro ⟨i, hi, hcop, rfl⟩
    exact ⟨i, mem_filter.mpr ⟨mem_range.mpr hi, hcop⟩, by push_cast <;> ring⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, mem_range.mp (mem_filter.mp hi).1, (mem_filter.mp hi).2, by push_cast <;> ring⟩

theorem sum_primitiveRoots_eq_sum_coprime {k : ℕ} (hk : 0 < k) (f : ℂ → ℝ) :
    ∑ ζ ∈ primitiveRoots k ℂ, f ζ =
      ∑ i ∈ (range k).filter (fun i => i.Coprime k),
        f (cexp (2 * Real.pi * I * ((i : ℝ) / k : ℝ))) := by
  rw [primitiveRoots_eq_image hk, sum_image]
  intro i hi j hj hij
  have hζ := Complex.isPrimitiveRoot_exp k hk.ne'
  have hpow : ∀ m : ℕ, cexp (2 * Real.pi * I * ((m : ℝ) / k : ℝ)) =
      cexp (2 * Real.pi * I / k) ^ m := fun m => by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hpow, hpow] at hij
  exact hζ.pow_inj (mem_range.mp (mem_filter.mp hi).1) (mem_range.mp (mem_filter.mp hj).1) hij

/-! ## §4. The Gram -/

/-- **Argument form.** Only the arguments of `1 - ζξ` enter the mean-centered pronic Gram. -/
theorem pmRamanujanMeanCenteredGram_eq_arg_form {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    RHTower.pmRamanujanMeanCenteredGram p q =
      (p.totient : ℝ) * q.totient / 4 - ∑ ζ ∈ primitiveRoots p ℂ, ∑ ξ ∈ primitiveRoots q ℂ,
        ((1 / (1 - ζ)).im + (1 / (1 - ξ)).im) * (1 - ζ * ξ).arg := by
  have hprim : ∀ {r : ℕ}, 2 ≤ r → ∀ ζ ∈ primitiveRoots r ℂ,
      ‖ζ‖ = 1 ∧ ζ ≠ 0 ∧ ζ ≠ 1 := fun hr ζ hζ => by
    have h := (mem_primitiveRoots (by omega)).mp hζ
    exact ⟨Complex.norm_eq_one_of_pow_eq_one h.pow_eq_one (by omega), h.ne_zero (by omega),
      h.ne_one (by omega)⟩
  have h := congrArg Complex.re (pmRamanujanMeanCenteredGram_eq_cyclotomicLog hp hq)
  simp only [Complex.ofReal_re, add_re, re_sum] at h
  rw [h, sub_eq_add_neg, ← sum_neg_distrib]
  congr 1
  · simp [← Complex.ofReal_natCast]
  refine sum_congr rfl fun ζ hζ => ?_
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun ξ hξ => ?_
  obtain ⟨hζn, hζ0, hζ1⟩ := hprim hp ζ hζ
  obtain ⟨hξn, hξ0, hξ1⟩ := hprim hq ξ hξ
  rw [div_mul_div_mul_cyclotomicLogKernel hζ0 hξ0 hζ1 hξ1, mul_re, Complex.log_im]
  simp only [sub_re, add_re, sub_im, add_im, one_re, one_im, re_one_div_one_sub hζn hζ1,
    re_one_div_one_sub hξn hξ1]
  ring

/-- **Cotangent–sawtooth form of the mean-centered pronic Gram.** -/
theorem pmRamanujanMeanCenteredGram_eq_cotangent_sawtooth {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    RHTower.pmRamanujanMeanCenteredGram p q =
      (p.totient : ℝ) * q.totient / 4 - Real.pi / 2 *
        ∑ a ∈ (range p).filter (fun a => a.Coprime p),
          ∑ b ∈ (range q).filter (fun b => b.Coprime q),
            (Real.cot (Real.pi * (a / p)) + Real.cot (Real.pi * (b / q))) *
              sawtooth ((a : ℝ) / p + (b : ℝ) / q) := by
  have hp0 : 0 < p := by omega
  have hq0 : 0 < q := by omega
  -- a coprime residue is a nonzero fraction strictly inside the unit interval
  have hsin : ∀ {k a : ℕ}, 2 ≤ k → a ∈ (range k).filter (fun a => a.Coprime k) →
      Real.sin (Real.pi * ((a : ℝ) / k)) ≠ 0 := by
    intro k a hk ha
    have hak := mem_range.mp (mem_filter.mp ha).1
    have ha0 : a ≠ 0 := by
      rintro rfl
      have := (mem_filter.mp ha).2
      rw [Nat.coprime_zero_left] at this
      omega
    have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    refine (Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_).ne'
    have : (a : ℝ) / k < 1 := (div_lt_one hkR).mpr (by exact_mod_cast hak)
    nlinarith [Real.pi_pos]
  rw [pmRamanujanMeanCenteredGram_eq_arg_form hp hq, sum_primitiveRoots_eq_sum_coprime hp0,
    mul_sum]
  congr 1
  refine sum_congr rfl fun a ha => ?_
  rw [sum_primitiveRoots_eq_sum_coprime hq0, mul_sum]
  refine sum_congr rfl fun b hb => ?_
  have hprod : cexp (2 * Real.pi * I * ((a : ℝ) / p : ℝ)) *
      cexp (2 * Real.pi * I * ((b : ℝ) / q : ℝ)) =
      cexp (2 * Real.pi * I * ((a : ℝ) / p + (b : ℝ) / q : ℝ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hprod, arg_one_sub_exp, im_one_div_one_sub_exp (hsin hp ha),
    im_one_div_one_sub_exp (hsin hq hb)]
  ring

end

end GaloisForLFunctions.BezoutValuationIncidence
