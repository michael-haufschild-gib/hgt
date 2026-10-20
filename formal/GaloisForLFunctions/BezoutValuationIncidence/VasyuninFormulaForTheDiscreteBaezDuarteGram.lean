import GaloisForLFunctions.BezoutValuationIncidence.PronicReciprocityLawForVasyuninSums
import GaloisForLFunctions.RHTower.BaezDuarteGramDiscrete

/-!
# The Vasyunin formula for the discrete Báez-Duarte Gram

The discrete Báez-Duarte system `{u}`-dilates by `1/m`, and cell cutting gives its Gram matrix as a
pronic series of residues:

`bdGram (1/m₁) (1/m₂) = Σ_{M ≥ 1} (M mod m₁)(M mod m₂) / (m₁ m₂ M(M+1))`.

In the divisor coordinates the residue is a finite exponential sum over the nontrivial `m`-th
roots `ζ_a = e(a/m)`, `0 < a < m`:

`M mod m = -Σ_a α_a (ζ_a^M - 1)`,  `α_a = ζ_a/(ζ_a - 1)`,  `Σ_a α_a = (m - 1)/2`.

This follows from counting multiples: `Σ_{k ≤ M} Σ_a ζ_a^k = m ⌊M/m⌋`. The pronic character sums
`Σ z^M/(M(M+1)) = 1 + Q(z)` then evaluate the series. Real parts of `α Q` give `-log |1 - ζ|`, and
`Π_a (1 - ζ_a) = m`. The cross terms reduce to the cotangent–sawtooth sum, and Hecke's relation
turns that into Vasyunin sums. For all `m₁, m₂ ≥ 1`:

`m₁ m₂ bdGram(1/m₁, 1/m₂) = ((m₁-1) log m₂ + (m₂-1) log m₁)/2`
`                         - (π/2)(V(m₂, m₁) - V(1, m₁) + V(m₁, m₂) - V(1, m₂))`.

This is Vasyunin's evaluation of the Nyman–Beurling–Báez-Duarte Gram matrix. In the Báez-Duarte
reduction, the closed form of these series and the cross tail `∫₁^∞ {v/m}{v} v^{-2} dv` were left as the
remaining unevaluated objects. Both are now explicit:
`2 fractCrossTail(1/m) = (1 - 1/m) + (1 + 1/m) fractSqConst - ((m-1) log m + π V(1, m))/m`.
-/

open Finset Complex RHTower
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- The root of unity `e(a/m)`. -/
def rootAt (m a : ℕ) : ℂ := cexp (2 * Real.pi * I * ((a : ℝ) / m : ℝ))

theorem rootAt_eq_pow (m a : ℕ) : rootAt m a = cexp (2 * Real.pi * I / m) ^ a := by
  rw [rootAt, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem norm_rootAt (m a : ℕ) : ‖rootAt m a‖ = 1 := by
  rw [rootAt, Complex.norm_exp]
  simp

theorem rootAt_ne_one {m a : ℕ} (ha : a ∈ Ico 1 m) : rootAt m a ≠ 1 := by
  obtain ⟨h1, h2⟩ := mem_Ico.mp ha
  rw [rootAt_eq_pow]
  exact (Complex.isPrimitiveRoot_exp m (by omega)).pow_ne_one_of_pos_of_lt (by omega) h2

theorem rootAt_ne_zero (m a : ℕ) : rootAt m a ≠ 0 := Complex.exp_ne_zero _

/-! ## §1. The residue as an exponential sum -/

/-- `Σ_{a < m} ζ_a^k = m [m ∣ k]`. -/
theorem sum_range_rootAt_pow {m : ℕ} (hm : 0 < m) (k : ℕ) :
    ∑ a ∈ range m, rootAt m a ^ k = if m ∣ k then (m : ℂ) else 0 := by
  have hω := Complex.isPrimitiveRoot_exp m hm.ne'
  have hrw : ∀ a, rootAt m a ^ k = (cexp (2 * Real.pi * I / m) ^ k) ^ a := fun a => by
    rw [rootAt_eq_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]
  simp_rw [hrw]
  split_ifs with hd
  · rw [(hω.pow_eq_one_iff_dvd k).mpr hd]
    simp
  · have hne : cexp (2 * Real.pi * I / m) ^ k ≠ 1 := fun h => hd ((hω.pow_eq_one_iff_dvd k).mp h)
    rw [geom_sum_eq hne, ← pow_mul, Nat.mul_comm, pow_mul, hω.pow_eq_one, one_pow, sub_self,
      zero_div]

/-- **The residue as an exponential sum.** `M mod m = -Σ_{0<a<m} α_a (ζ_a^M - 1)`. -/
theorem natMod_eq_spectral {m : ℕ} (hm : 0 < m) (M : ℕ) :
    ((M % m : ℕ) : ℂ) = -∑ a ∈ Ico 1 m, rootAt m a / (rootAt m a - 1) * (rootAt m a ^ M - 1) := by
  -- count the multiples of `m` up to `M`
  have hcount : ∑ k ∈ Icc 1 M, ∑ a ∈ range m, rootAt m a ^ k = (m : ℂ) * (M / m : ℕ) := by
    simp_rw [sum_range_rootAt_pow hm]
    have hIcc : Icc 1 M = Ioc 0 M := by ext; simp only [mem_Icc, mem_Ioc]; omega
    rw [← sum_filter, sum_const, nsmul_eq_mul, hIcc, Nat.Ioc_filter_dvd_card_eq_div]
    ring
  rw [sum_comm, range_eq_Ico, sum_eq_sum_Ico_succ_bot hm] at hcount
  have hzero : ∑ k ∈ Icc 1 M, rootAt m 0 ^ k = M := by
    simp [rootAt]
  rw [hzero] at hcount
  have hgeom : ∀ a ∈ Ico 1 m, ∑ k ∈ Icc 1 M, rootAt m a ^ k =
      rootAt m a / (rootAt m a - 1) * (rootAt m a ^ M - 1) := by
    intro a ha
    have hs : rootAt m a - 1 ≠ 0 := sub_ne_zero.mpr (rootAt_ne_one ha)
    have h := mul_sum_Icc_pow (rootAt m a) M
    field_simp
    linear_combination h
  rw [sum_congr rfl hgeom] at hcount
  have hdiv := Nat.mod_add_div M m
  have hdivC : ((M % m : ℕ) : ℂ) + (m : ℂ) * (M / m : ℕ) = M := by exact_mod_cast hdiv
  linear_combination hcount + hdivC

/-- **Inversion pairing.** `Σ_{0<a<m} α_a = (m - 1)/2`. -/
theorem sum_Ico_rootAt_div_sub_one {m : ℕ} (hm : 0 < m) :
    ∑ a ∈ Ico 1 m, rootAt m a / (rootAt m a - 1) = ((m : ℂ) - 1) / 2 := by
  have hinvroot : ∀ a ∈ Ico 1 m, rootAt m (m - a) = (rootAt m a)⁻¹ := by
    intro a ha
    have hω := Complex.isPrimitiveRoot_exp m hm.ne'
    rw [rootAt_eq_pow, rootAt_eq_pow]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_add, Nat.sub_add_cancel (mem_Ico.mp ha).2.le, hω.pow_eq_one]
  have hrefl : ∑ a ∈ Ico 1 m, rootAt m a / (rootAt m a - 1) =
      ∑ a ∈ Ico 1 m, rootAt m (m - a) / (rootAt m (m - a) - 1) := by
    refine sum_nbij' (fun a => m - a) (fun a => m - a) (fun a ha => ?_) (fun a ha => ?_)
      (fun a ha => ?_) (fun a ha => ?_) (fun a ha => ?_)
    · simp only [mem_Ico] at ha ⊢; omega
    · simp only [mem_Ico] at ha ⊢; omega
    · simp only [mem_Ico] at ha; omega
    · simp only [mem_Ico] at ha; omega
    · simp only [mem_Ico] at ha
      rw [Nat.sub_sub_self ha.2.le]
  have hpair : ∀ a ∈ Ico 1 m, rootAt m a / (rootAt m a - 1) +
      rootAt m (m - a) / (rootAt m (m - a) - 1) = 1 := by
    intro a ha
    rw [hinvroot a ha]
    have h0 := rootAt_ne_zero m a
    have hs : rootAt m a - 1 ≠ 0 := sub_ne_zero.mpr (rootAt_ne_one ha)
    have hs' : (rootAt m a)⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr (by rw [Ne, inv_eq_one]; exact rootAt_ne_one ha)
    have hs'' : 1 - rootAt m a ≠ 0 := sub_ne_zero.mpr (Ne.symm (rootAt_ne_one ha))
    field_simp
    ring
  have h2 : 2 * ∑ a ∈ Ico 1 m, rootAt m a / (rootAt m a - 1) = (m : ℂ) - 1 := by
    rw [two_mul]
    nth_rewrite 2 [hrefl]
    rw [← sum_add_distrib, sum_congr rfl hpair, sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one,
      Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  linear_combination h2 / 2

/-- **The cyclotomic norm.** `Σ_{0<a<m} log |1 - ζ_a| = log m`. -/
theorem sum_Ico_log_norm_one_sub_rootAt {m : ℕ} (hm : 0 < m) :
    ∑ a ∈ Ico 1 m, Real.log ‖1 - rootAt m a‖ = Real.log m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hω := Complex.isPrimitiveRoot_exp (n + 1) (by omega)
  have hprod := hω.prod_one_sub_pow_eq_order
  have hreindex : ∏ a ∈ Ico 1 (n + 1), (1 - rootAt (n + 1) a) =
      ∏ k ∈ range n, (1 - cexp (2 * Real.pi * I / ((n + 1 : ℕ) : ℂ)) ^ (k + 1)) := by
    rw [range_eq_Ico, ← Finset.prod_Ico_add' (fun a => 1 - rootAt (n + 1) a) 0 n 1]
    refine prod_congr (by simp) fun k _ => ?_
    rw [rootAt_eq_pow]
  have hne : ∀ a ∈ Ico 1 (n + 1), ‖1 - rootAt (n + 1) a‖ ≠ 0 := fun a ha =>
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm (rootAt_ne_one ha)))
  have hnorm : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [← Real.log_prod hne, ← norm_prod, hreindex, hprod, hnorm]
  push_cast
  ring_nf

/-! ## §2. The pronic series of a product of residues -/

/-- `α_a Q(ζ_a) = -log(1 - ζ_a)`. -/
theorem rootAt_div_mul_cyclotomicLogKernel {m a : ℕ} (ha : a ∈ Ico 1 m) :
    rootAt m a / (rootAt m a - 1) * cyclotomicLogKernel (rootAt m a) = -log (1 - rootAt m a) := by
  have h1 := rootAt_ne_one ha
  have h0 := rootAt_ne_zero m a
  have hs : rootAt m a - 1 ≠ 0 := sub_ne_zero.mpr h1
  rw [cyclotomicLogKernel, if_neg h1]
  field_simp
  ring

theorem rootAt_mul_rootAt (m₁ m₂ a b : ℕ) :
    rootAt m₁ a * rootAt m₂ b = cexp (2 * Real.pi * I * ((a : ℝ) / m₁ + (b : ℝ) / m₂ : ℝ)) := by
  rw [rootAt, rootAt, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The pronic series of `(M mod m₁)(M mod m₂)`, in closed form.** -/
theorem hasSum_natMod_mul_natMod {m₁ m₂ : ℕ} (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    HasSum (fun M : ℕ => ((M % m₁ : ℕ) : ℝ) * ((M % m₂ : ℕ) : ℝ) / ((M : ℝ) * ((M : ℝ) + 1)))
      ((((m₁ : ℝ) - 1) * Real.log m₂ + ((m₂ : ℝ) - 1) * Real.log m₁) / 2 - Real.pi / 2 *
        ∑ a ∈ Ico 1 m₁, ∑ b ∈ Ico 1 m₂,
          (Real.cot (Real.pi * ((a : ℝ) / m₁)) + Real.cot (Real.pi * ((b : ℝ) / m₂))) *
            sawtooth ((a : ℝ) / m₁ + (b : ℝ) / m₂)) := by
  set α : ℕ → ℕ → ℂ := fun m a => rootAt m a / (rootAt m a - 1)
  set V : ℂ := ∑ a ∈ Ico 1 m₁, ∑ b ∈ Ico 1 m₂, α m₁ a * α m₂ b *
    (cyclotomicLogKernel (rootAt m₁ a * rootAt m₂ b) - cyclotomicLogKernel (rootAt m₁ a) -
      cyclotomicLogKernel (rootAt m₂ b))
  -- the complex series
  have hterm : ∀ M : ℕ, ((((M % m₁ : ℕ) : ℝ) * ((M % m₂ : ℕ) : ℝ) /
      ((M : ℝ) * ((M : ℝ) + 1)) : ℝ) : ℂ) =
      ∑ a ∈ Ico 1 m₁, ∑ b ∈ Ico 1 m₂, α m₁ a * α m₂ b *
        (pronicTerm (rootAt m₁ a * rootAt m₂ b) M - pronicTerm (rootAt m₁ a) M -
          pronicTerm (rootAt m₂ b) M + pronicTerm 1 M) := by
    intro M
    push_cast
    rw [natMod_eq_spectral h₁, natMod_eq_spectral h₂, neg_mul_neg, sum_mul_sum, sum_div]
    refine sum_congr rfl fun a _ => ?_
    rw [sum_div]
    refine sum_congr rfl fun b _ => ?_
    simp only [α, pronicTerm, mul_pow, one_pow]
    ring
  have hV : HasSum (fun M : ℕ => ((((M % m₁ : ℕ) : ℝ) * ((M % m₂ : ℕ) : ℝ) /
      ((M : ℝ) * ((M : ℝ) + 1)) : ℝ) : ℂ)) V := by
    simp only [hterm]
    refine hasSum_sum fun a _ => hasSum_sum fun b _ => ?_
    have hn : ∀ z : ℂ, ‖z‖ = 1 → HasSum (pronicTerm z) (1 + cyclotomicLogKernel z) :=
      fun z hz => hasSum_pronicTerm_of_norm_eq_one hz
    have h := (((hn (rootAt m₁ a * rootAt m₂ b) (by simp [norm_rootAt])).sub
      (hn (rootAt m₁ a) (norm_rootAt m₁ a))).sub (hn (rootAt m₂ b) (norm_rootAt m₂ b))).add
        (hn 1 (by simp))
    have hK1 : cyclotomicLogKernel 1 = 0 := by simp [cyclotomicLogKernel]
    have hval : α m₁ a * α m₂ b * (cyclotomicLogKernel (rootAt m₁ a * rootAt m₂ b) -
        cyclotomicLogKernel (rootAt m₁ a) - cyclotomicLogKernel (rootAt m₂ b)) =
        α m₁ a * α m₂ b * (1 + cyclotomicLogKernel (rootAt m₁ a * rootAt m₂ b) -
          (1 + cyclotomicLogKernel (rootAt m₁ a)) - (1 + cyclotomicLogKernel (rootAt m₂ b)) +
            (1 + cyclotomicLogKernel 1)) := by rw [hK1]; ring
    rw [hval]
    exact h.mul_left _
  have hreal := Complex.reCLM.hasSum hV
  simp only [Complex.reCLM_apply, Complex.ofReal_re] at hreal
  convert hreal using 1
  -- the real part of the closed form
  have hA₁ := sum_Ico_rootAt_div_sub_one h₁
  have hA₂ := sum_Ico_rootAt_div_sub_one h₂
  have hsplit : V = (∑ a ∈ Ico 1 m₁, ∑ b ∈ Ico 1 m₂,
        α m₁ a * α m₂ b * cyclotomicLogKernel (rootAt m₁ a * rootAt m₂ b)) -
      (∑ a ∈ Ico 1 m₁, α m₁ a * cyclotomicLogKernel (rootAt m₁ a)) * (((m₂ : ℂ) - 1) / 2) -
      (∑ b ∈ Ico 1 m₂, α m₂ b * cyclotomicLogKernel (rootAt m₂ b)) * (((m₁ : ℂ) - 1) / 2) := by
    rw [← hA₁, ← hA₂, sum_mul_sum, sum_mul_sum, sum_comm (s := Ico 1 m₂) (t := Ico 1 m₁)]
    simp only [V, ← sum_sub_distrib]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    ring
  -- log-modulus parts of the single sums
  have hsingle : ∀ (m : ℕ), 0 < m →
      (∑ a ∈ Ico 1 m, α m a * cyclotomicLogKernel (rootAt m a)).re = -Real.log m := by
    intro m hm
    rw [re_sum, ← sum_Ico_log_norm_one_sub_rootAt hm, ← sum_neg_distrib]
    refine sum_congr rfl fun a ha => ?_
    simp only [α]
    rw [rootAt_div_mul_cyclotomicLogKernel ha, neg_re, Complex.log_re]
  -- the double sum: only arguments survive
  have hdouble : ∀ a ∈ Ico 1 m₁, ∀ b ∈ Ico 1 m₂,
      (α m₁ a * α m₂ b * cyclotomicLogKernel (rootAt m₁ a * rootAt m₂ b)).re =
        -(Real.pi / 2) * ((Real.cot (Real.pi * ((a : ℝ) / m₁)) +
          Real.cot (Real.pi * ((b : ℝ) / m₂))) * sawtooth ((a : ℝ) / m₁ + (b : ℝ) / m₂)) := by
    intro a ha b hb
    have hsin : ∀ {k c : ℕ}, c ∈ Ico 1 k → Real.sin (Real.pi * ((c : ℝ) / k)) ≠ 0 := by
      intro k c hc
      obtain ⟨hc1, hc2⟩ := mem_Ico.mp hc
      have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      refine (Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_).ne'
      have : (c : ℝ) / k < 1 := (div_lt_one hkR).mpr (by exact_mod_cast hc2)
      nlinarith [Real.pi_pos]
    have hre₁ := re_one_div_one_sub (norm_rootAt m₁ a) (rootAt_ne_one ha)
    have hre₂ := re_one_div_one_sub (norm_rootAt m₂ b) (rootAt_ne_one hb)
    have him₁ : (1 / (1 - rootAt m₁ a)).im = Real.cot (Real.pi * ((a : ℝ) / m₁)) / 2 :=
      im_one_div_one_sub_exp (hsin ha)
    have him₂ : (1 / (1 - rootAt m₂ b)).im = Real.cot (Real.pi * ((b : ℝ) / m₂)) / 2 :=
      im_one_div_one_sub_exp (hsin hb)
    have harg : (1 - rootAt m₁ a * rootAt m₂ b).arg =
        Real.pi * sawtooth ((a : ℝ) / m₁ + (b : ℝ) / m₂) := by
      rw [rootAt_mul_rootAt, arg_one_sub_exp]
    simp only [α]
    rw [div_mul_div_mul_cyclotomicLogKernel (rootAt_ne_zero _ _) (rootAt_ne_zero _ _)
      (rootAt_ne_one ha) (rootAt_ne_one hb), mul_re, Complex.log_im, harg]
    simp only [sub_re, add_re, sub_im, add_im, one_re, one_im, hre₁, hre₂, him₁, him₂]
    ring
  have hD : (∑ a ∈ Ico 1 m₁, ∑ b ∈ Ico 1 m₂,
      α m₁ a * α m₂ b * cyclotomicLogKernel (rootAt m₁ a * rootAt m₂ b)).re =
      -(Real.pi / 2) * ∑ a ∈ Ico 1 m₁, ∑ b ∈ Ico 1 m₂,
        (Real.cot (Real.pi * ((a : ℝ) / m₁)) + Real.cot (Real.pi * ((b : ℝ) / m₂))) *
          sawtooth ((a : ℝ) / m₁ + (b : ℝ) / m₂) := by
    rw [re_sum, mul_sum]
    refine sum_congr rfl fun a ha => ?_
    rw [re_sum, mul_sum]
    exact sum_congr rfl fun b hb => hdouble a ha b hb
  have hcast : ∀ m : ℕ, ((m : ℂ) - 1) / 2 = ((((m : ℝ) - 1) / 2 : ℝ) : ℂ) := fun m => by
    push_cast; ring
  rw [hsplit, sub_re, sub_re, hcast m₂, hcast m₁, Complex.re_mul_ofReal, Complex.re_mul_ofReal,
    hD, hsingle m₁ h₁, hsingle m₂ h₂]
  ring

/-! ## §3. The Báez-Duarte Gram -/

/-- **The Vasyunin formula for the discrete Báez-Duarte Gram.** -/
theorem bdGram_inv_nat_eq_vasyunin {m₁ m₂ : ℕ} (h₁ : 1 ≤ m₁) (h₂ : 1 ≤ m₂) :
    bdGram (1 / (m₁ : ℝ)) (1 / (m₂ : ℝ)) =
      ((((m₁ : ℝ) - 1) * Real.log m₂ + ((m₂ : ℝ) - 1) * Real.log m₁) / 2 - Real.pi / 2 *
        (vasyuninSum m₂ m₁ - vasyuninSum 1 m₁ + vasyuninSum m₁ m₂ - vasyuninSum 1 m₂)) /
          ((m₁ : ℝ) * m₂) := by
  have hm₁ : (0 : ℝ) < m₁ := by exact_mod_cast h₁
  have hm₂ : (0 : ℝ) < m₂ := by exact_mod_cast h₂
  -- Hecke reduces the cotangent–sawtooth sum to Vasyunin sums
  have hhecke : ∑ a ∈ Ico 1 m₁, ∑ b ∈ Ico 1 m₂,
      (Real.cot (Real.pi * ((a : ℝ) / m₁)) + Real.cot (Real.pi * ((b : ℝ) / m₂))) *
        sawtooth ((a : ℝ) / m₁ + (b : ℝ) / m₂) =
      vasyuninSum m₂ m₁ - vasyuninSum 1 m₁ + vasyuninSum m₁ m₂ - vasyuninSum 1 m₂ := by
    simp only [add_mul, sum_add_distrib]
    have e1 : ∑ a ∈ Ico 1 m₁, ∑ b ∈ Ico 1 m₂,
        Real.cot (Real.pi * ((a : ℝ) / m₁)) * sawtooth ((a : ℝ) / m₁ + (b : ℝ) / m₂) =
        vasyuninSum m₂ m₁ - vasyuninSum 1 m₁ := by
      rw [vasyuninSum, vasyuninSum, ← sum_sub_distrib]
      refine sum_congr rfl fun a _ => ?_
      rw [← mul_sum, sum_Ico_sawtooth_add (by omega), mul_sub]
      congr 2 <;> ring_nf
    have e2 : ∑ a ∈ Ico 1 m₁, ∑ b ∈ Ico 1 m₂,
        Real.cot (Real.pi * ((b : ℝ) / m₂)) * sawtooth ((a : ℝ) / m₁ + (b : ℝ) / m₂) =
        vasyuninSum m₁ m₂ - vasyuninSum 1 m₂ := by
      rw [sum_comm, vasyuninSum, vasyuninSum, ← sum_sub_distrib]
      refine sum_congr rfl fun b _ => ?_
      rw [← mul_sum]
      have h := sum_Ico_sawtooth_add (by omega : 0 < m₁) ((b : ℝ) / m₂)
      rw [show ∑ a ∈ Ico 1 m₁, sawtooth ((a : ℝ) / m₁ + (b : ℝ) / m₂) =
          ∑ a ∈ Ico 1 m₁, sawtooth ((b : ℝ) / m₂ + (a : ℝ) / m₁) from
        sum_congr rfl fun a _ => by rw [add_comm], h, mul_sub]
      congr 2 <;> ring_nf
    rw [e1, e2]
    ring
  have hser := hasSum_natMod_mul_natMod (by omega : 0 < m₁) (by omega : 0 < m₂)
  rw [hhecke] at hser
  -- shift to the index of the Báez-Duarte series and divide by `m₁ m₂`
  have hshift := ((hasSum_nat_add_iff' 1).mpr hser).div_const ((m₁ : ℝ) * m₂)
  simp only [Finset.sum_range_one, Nat.zero_mod, Nat.cast_zero, zero_mul, zero_div,
    sub_zero] at hshift
  have hbd := hasSum_bdGram_discrete h₁ h₂
  refine hbd.unique (hshift.congr_fun fun n => ?_)
  push_cast
  field_simp
  ring

/-- **The diagonal.** `m² bdGram(1/m, 1/m) = (m - 1) log m + π V(1, m)`. -/
theorem bdGram_inv_nat_self {m : ℕ} (hm : 1 ≤ m) :
    bdGram (1 / (m : ℝ)) (1 / (m : ℝ)) =
      (((m : ℝ) - 1) * Real.log m + Real.pi * vasyuninSum 1 m) / ((m : ℝ) * m) := by
  have hVmm : vasyuninSum m m = 0 := by
    unfold vasyuninSum
    refine sum_eq_zero fun a _ => ?_
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    rw [show (m : ℝ) * a / m = ((a : ℤ) : ℝ) by field_simp; push_cast; ring,
      show sawtooth ((a : ℤ) : ℝ) = 0 by simp [sawtooth], mul_zero]
  rw [bdGram_inv_nat_eq_vasyunin hm hm, hVmm]
  ring

/-- **The cross tail at `θ = 1/m` is explicit.** -/
theorem fractCrossTail_inv_nat {m : ℕ} (hm : 1 ≤ m) :
    2 * fractCrossTail (1 / (m : ℝ)) =
      (1 - 1 / (m : ℝ)) + (1 + 1 / (m : ℝ)) * fractSqConst -
        (((m : ℝ) - 1) * Real.log m + Real.pi * vasyuninSum 1 m) / m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hθ0 : (0 : ℝ) < 1 / (m : ℝ) := by positivity
  have hθ1 : 1 / (m : ℝ) ≤ 1 := by rw [div_le_one hmR]; exact_mod_cast hm
  have h := bdGram_self_eq (1 / (m : ℝ)) hθ0 hθ1
  rw [bdGram_inv_nat_self hm] at h
  field_simp at h ⊢
  linarith

end

end GaloisForLFunctions.BezoutValuationIncidence
