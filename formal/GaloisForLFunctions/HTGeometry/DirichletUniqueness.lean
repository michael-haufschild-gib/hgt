import GaloisForLFunctions.HTGeometry.DirichletFormal
import GaloisForLFunctions.HTGeometry.PolynomialForwardDifference
import Mathlib

/-!
# Convergence and uniqueness of Dirichlet expansions

A formal Dirichlet series with polynomial coefficients is *bounded* when its coefficients have
uniformly bounded degree and polynomially bounded size.  Such a series converges absolutely on a
right half-line, and the resulting function determines the series: if the sum vanishes identically
on a right half-line then every coefficient vanishes.

The mechanism of the uniqueness proof is the decay principle of
`PolynomialForwardDifference`.  Multiplying by `m0 ^ s`, where `m0` is the least index carrying a
nonzero coefficient, isolates that coefficient up to a tail bounded by a geometric sequence of ratio
`m0 / (m0 + 1) < 1`; a polynomial dominated by such a sequence along the naturals is zero.
-/

open Polynomial Filter

namespace HTGeometry

namespace DirFormal

/-- Uniform degree and polynomial size bounds on the coefficients. -/
structure IsBoundedBy (f : DirFormal) (deg : ℕ) (size expo : ℝ) : Prop where
  size_nonneg : 0 ≤ size
  expo_nonneg : 0 ≤ expo
  natDegree_le : ∀ m, (f m).natDegree ≤ deg
  coeff_le : ∀ m i, ‖(f m).coeff i‖ ≤ size * (m : ℝ) ^ expo

/-- A series is bounded when some degree and size bounds work. -/
def IsBounded (f : DirFormal) : Prop := ∃ d C A, IsBoundedBy f d C A

/-- The value of the `m`-th coefficient is controlled by the size bound. -/
theorem norm_eval_le_of_isBoundedBy {f : DirFormal} {d : ℕ} {C A : ℝ}
    (h : IsBoundedBy f d C A) (m : ℕ) {s : ℝ} (hs : 1 ≤ s) :
    ‖(f m).eval ((s : ℂ))‖ ≤ (d + 1) * C * (m : ℝ) ^ A * s ^ d := by
  have hM : max 1 ‖((s : ℂ))‖ = s := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    exact max_eq_right hs
  have hbase := norm_eval_le_pow (f m) ((s : ℂ))
  rw [hM] at hbase
  refine hbase.trans ?_
  have hsum : (∑ i ∈ Finset.range ((f m).natDegree + 1), ‖(f m).coeff i‖)
      ≤ (d + 1) * (C * (m : ℝ) ^ A) := by
    calc (∑ i ∈ Finset.range ((f m).natDegree + 1), ‖(f m).coeff i‖)
        ≤ ∑ _i ∈ Finset.range ((f m).natDegree + 1), C * (m : ℝ) ^ A :=
          Finset.sum_le_sum fun i _ => h.coeff_le m i
      _ = ((f m).natDegree + 1 : ℕ) * (C * (m : ℝ) ^ A) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (d + 1) * (C * (m : ℝ) ^ A) := by
          refine mul_le_mul_of_nonneg_right ?_
            (mul_nonneg h.size_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m) A))
          have := h.natDegree_le m
          push_cast
          linarith [this, Nat.cast_le (α := ℝ) |>.mpr this]
  have hpow : s ^ (f m).natDegree ≤ s ^ d :=
    pow_le_pow_right₀ hs (h.natDegree_le m)
  calc (∑ i ∈ Finset.range ((f m).natDegree + 1), ‖(f m).coeff i‖) * s ^ (f m).natDegree
      ≤ ((d + 1) * (C * (m : ℝ) ^ A)) * s ^ d := by
        refine mul_le_mul hsum hpow (pow_nonneg (by linarith) _)
          (mul_nonneg (by positivity)
            (mul_nonneg h.size_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m) A)))
    _ = (d + 1) * C * (m : ℝ) ^ A * s ^ d := by ring

/-- The value of a bounded Dirichlet series at a real point. -/
noncomputable def realize (f : DirFormal) (s : ℝ) : ℂ :=
  ∑' m : ℕ, (f m).eval ((s : ℂ)) * (((m : ℝ) ^ (-s) : ℝ) : ℂ)

theorem summable_norm_realize {f : DirFormal} {d : ℕ} {C A : ℝ}
    (h : IsBoundedBy f d C A) {s : ℝ} (hs : A + 2 ≤ s) :
    Summable (fun m : ℕ => ‖(f m).eval ((s : ℂ)) * (((m : ℝ) ^ (-s) : ℝ) : ℂ)‖) := by
  have hs1 : (1 : ℝ) ≤ s := by nlinarith [h.expo_nonneg]
  have hp : Summable (fun m : ℕ => 1 / (m : ℝ) ^ (2 : ℝ)) :=
    (Real.summable_one_div_nat_rpow (p := (2 : ℝ))).mpr (by norm_num)
  have hmaj : Summable (fun m : ℕ =>
      ((d : ℝ) + 1) * C * s ^ d * (1 / (m : ℝ) ^ (2 : ℝ))) := Summable.mul_left _ hp
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hmaj
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hcoef := norm_eval_le_of_isBoundedBy h m hs1
  have hpow : ‖((((m : ℝ) ^ (-s) : ℝ)) : ℂ)‖ = (m : ℝ) ^ (-s) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hmpos.le _)]
  rw [norm_mul, hpow]
  have hmul : (m : ℝ) ^ A * (m : ℝ) ^ (-s) ≤ 1 / (m : ℝ) ^ (2 : ℝ) := by
    rw [← Real.rpow_add hmpos, one_div, ← Real.rpow_neg hmpos.le]
    exact Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
  calc ‖(f m).eval ((s : ℂ))‖ * (m : ℝ) ^ (-s)
      ≤ (((d : ℝ) + 1) * C * (m : ℝ) ^ A * s ^ d) * (m : ℝ) ^ (-s) :=
        mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hmpos.le _)
    _ = (((d : ℝ) + 1) * C * s ^ d) * ((m : ℝ) ^ A * (m : ℝ) ^ (-s)) := by ring
    _ ≤ (((d : ℝ) + 1) * C * s ^ d) * (1 / (m : ℝ) ^ (2 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left hmul ?_
        have hsd : (0 : ℝ) ≤ s ^ d := pow_nonneg (by linarith) d
        have hC := h.size_nonneg
        positivity

theorem summable_realize {f : DirFormal} {d : ℕ} {C A : ℝ}
    (h : IsBoundedBy f d C A) {s : ℝ} (hs : A + 2 ≤ s) :
    Summable (fun m : ℕ => (f m).eval ((s : ℂ)) * (((m : ℝ) ^ (-s) : ℝ) : ℂ)) :=
  Summable.of_norm (summable_norm_realize h hs)

/-- **Uniqueness of Dirichlet expansions.**  A bounded series whose sum vanishes along the natural
numbers is the zero series. -/
theorem eq_zero_of_realize_eq_zero {f : DirFormal} {d : ℕ} {C A : ℝ}
    (h : IsBoundedBy f d C A)
    (hzero : ∀ᶠ (n : ℕ) in atTop, realize f (n : ℝ) = 0) :
    f = 0 := by
  classical
  by_contra hf
  set m0 : ℕ := ord f with hm0
  have hm0pos : 0 < m0 := ord_pos' hf
  set p : ℂ[X] := f m0 with hp
  have hpne : p ≠ 0 := lead_ne_zero' hf
  have hpS : Summable (fun m : ℕ => 1 / (m : ℝ) ^ (2 : ℝ)) :=
    (Real.summable_one_div_nat_rpow (p := (2 : ℝ))).mpr (by norm_num)
  set S : ℝ := ∑' m : ℕ, 1 / (m : ℝ) ^ (2 : ℝ) with hS
  have hSnn : 0 ≤ S := tsum_nonneg fun m => by positivity
  set K : ℝ := ((d : ℝ) + 1) * C * S * ((m0 : ℝ) + 1) ^ (A + 2) with hK
  set r : ℝ := (m0 : ℝ) / ((m0 : ℝ) + 1) with hr
  have hm0R : (0 : ℝ) < (m0 : ℝ) := by exact_mod_cast hm0pos
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    rw [hr, div_lt_one (by linarith)]
    linarith
  refine hpne (eq_zero_of_norm_eval_le_geometric (C := K) (r := r) (k := d) hr0 hr1 ?_)
  filter_upwards [hzero, eventually_ge_atTop (Nat.ceil (A + 2)), eventually_ge_atTop 1]
    with n hn0 hnA hn1
  have hsA : A + 2 ≤ (n : ℝ) := Nat.ceil_le.mp hnA
  have hs1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  set g : ℕ → ℂ := fun m => (f m).eval (((n : ℝ) : ℂ)) * ((((m : ℝ) ^ (-(n : ℝ))) : ℝ) : ℂ)
    with hg
  have hsum : Summable g := summable_realize h hsA
  have hCnn := h.size_nonneg
  have hnd : (0 : ℝ) ≤ (n : ℝ) ^ d := pow_nonneg (by linarith) d
  set L : ℝ := ((d : ℝ) + 1) * C * (n : ℝ) ^ d * ((m0 : ℝ) + 1) ^ (A + 2 - (n : ℝ)) with hL
  have hLnn : 0 ≤ L := by rw [hL]; positivity
  have hsplit : g m0 + ∑' m : ℕ, (if m = m0 then 0 else g m) = 0 := by
    rw [← hsum.tsum_eq_add_tsum_ite m0]; exact hn0
  have hgm0 : g m0 = -∑' m : ℕ, (if m = m0 then 0 else g m) := by linear_combination hsplit
  have hterm : ∀ m : ℕ, ‖(if m = m0 then 0 else g m)‖ ≤ L * (1 / (m : ℝ) ^ (2 : ℝ)) := by
    intro m
    by_cases hme : m = m0
    · rw [if_pos hme, norm_zero]
      positivity
    rw [if_neg hme]
    by_cases hlt : m < m0
    · rw [hg]
      simp only [coeff_eq_zero_of_lt hlt, Polynomial.eval_zero, zero_mul, norm_zero]
      positivity
    · have hmgt : m0 < m := by omega
      have hmposN : 0 < m := by omega
      have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmposN
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmposN
      have hcoef := norm_eval_le_of_isBoundedBy h m hs1
      have hpowm : ‖((((m : ℝ) ^ (-(n : ℝ))) : ℝ) : ℂ)‖ = (m : ℝ) ^ (-(n : ℝ)) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hmpos.le _)]
      rw [hg]
      simp only [norm_mul, hpowm]
      have hmm : (m0 : ℝ) + 1 ≤ (m : ℝ) := by
        have : m0 + 1 ≤ m := by omega
        exact_mod_cast this
      have hexp : (m : ℝ) ^ A * (m : ℝ) ^ (-(n : ℝ))
          ≤ ((m0 : ℝ) + 1) ^ (A + 2 - (n : ℝ)) * (1 / (m : ℝ) ^ (2 : ℝ)) := by
        rw [← Real.rpow_add hmpos, one_div, ← Real.rpow_neg hmpos.le]
        have hsplit2 : A + -(n : ℝ) = (A + 2 - (n : ℝ)) + (-2 : ℝ) := by ring
        rw [hsplit2, Real.rpow_add hmpos]
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hmpos.le _)
        have hnp : (0 : ℝ) ≤ (n : ℝ) - A - 2 := by linarith
        have hb : ((m0 : ℝ) + 1) ^ ((n : ℝ) - A - 2) ≤ (m : ℝ) ^ ((n : ℝ) - A - 2) :=
          Real.rpow_le_rpow (by linarith) hmm hnp
        have hneg : A + 2 - (n : ℝ) = -((n : ℝ) - A - 2) := by ring
        rw [hneg, Real.rpow_neg hmpos.le, Real.rpow_neg (by linarith : (0:ℝ) ≤ (m0:ℝ)+1)]
        exact inv_anti₀ (Real.rpow_pos_of_pos (by linarith) _) hb
      calc ‖(f m).eval (((n : ℝ) : ℂ))‖ * (m : ℝ) ^ (-(n : ℝ))
          ≤ (((d : ℝ) + 1) * C * (m : ℝ) ^ A * (n : ℝ) ^ d) * (m : ℝ) ^ (-(n : ℝ)) :=
            mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hmpos.le _)
        _ = (((d : ℝ) + 1) * C * (n : ℝ) ^ d) * ((m : ℝ) ^ A * (m : ℝ) ^ (-(n : ℝ))) := by ring
        _ ≤ (((d : ℝ) + 1) * C * (n : ℝ) ^ d)
              * (((m0 : ℝ) + 1) ^ (A + 2 - (n : ℝ)) * (1 / (m : ℝ) ^ (2 : ℝ))) := by
            refine mul_le_mul_of_nonneg_left hexp ?_
            positivity
        _ = L * (1 / (m : ℝ) ^ (2 : ℝ)) := by rw [hL]; ring
  have hmajor : Summable (fun m : ℕ => L * (1 / (m : ℝ) ^ (2 : ℝ))) := Summable.mul_left _ hpS
  have hns : Summable (fun m : ℕ => ‖(if m = m0 then 0 else g m)‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hterm hmajor
  have hgm0norm : ‖g m0‖ ≤ L * S := by
    rw [hgm0, norm_neg]
    calc ‖∑' m : ℕ, (if m = m0 then 0 else g m)‖
        ≤ ∑' m : ℕ, ‖(if m = m0 then 0 else g m)‖ := norm_tsum_le_tsum_norm hns
      _ ≤ ∑' m : ℕ, L * (1 / (m : ℝ) ^ (2 : ℝ)) := Summable.tsum_le_tsum hterm hns hmajor
      _ = L * S := by rw [hS, ← tsum_mul_left]
  have hm0inv : ‖g m0‖ = ‖p.eval (((n : ℝ) : ℂ))‖ * (m0 : ℝ) ^ (-(n : ℝ)) := by
    rw [hg, hp]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hm0R.le _)]
  have hposm0 : (0 : ℝ) < (m0 : ℝ) ^ (-(n : ℝ)) := Real.rpow_pos_of_pos hm0R _
  rw [hm0inv] at hgm0norm
  have hbound : ‖p.eval (((n : ℝ) : ℂ))‖ ≤ (L * S) / (m0 : ℝ) ^ (-(n : ℝ)) :=
    (le_div_iff₀ hposm0).mpr hgm0norm
  have hval : (L * S) / (m0 : ℝ) ^ (-(n : ℝ)) = K * (n : ℝ) ^ d * r ^ n := by
    have hrp : ((m0 : ℝ) + 1) ^ (A + 2 - (n : ℝ))
        = ((m0 : ℝ) + 1) ^ (A + 2) / ((m0 : ℝ) + 1) ^ ((n : ℕ) : ℝ) :=
      Real.rpow_sub (by linarith) _ _
    have hinv : ((m0 : ℝ)) ^ (-(n : ℝ)) = 1 / ((m0 : ℝ)) ^ ((n : ℕ) : ℝ) := by
      rw [Real.rpow_neg hm0R.le, one_div]
    have hrn : r ^ n = ((m0 : ℝ)) ^ ((n : ℕ) : ℝ) / ((m0 : ℝ) + 1) ^ ((n : ℕ) : ℝ) := by
      rw [hr, ← Real.rpow_natCast ((m0 : ℝ) / ((m0 : ℝ) + 1)) n,
        Real.div_rpow hm0R.le (by linarith)]
    have h1 : ((m0 : ℝ)) ^ ((n : ℕ) : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hm0R _)
    have h2 : ((m0 : ℝ) + 1) ^ ((n : ℕ) : ℝ) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos (by linarith) _)
    rw [hL, hK, hrp, hinv, hrn]
    field_simp
  rw [hval] at hbound
  have hcast : (((n : ℝ)) : ℂ) = ((n : ℕ) : ℂ) := by push_cast; ring
  rw [hcast] at hbound
  exact hbound

/-- Bounds add. -/
theorem IsBoundedBy.add {f g : DirFormal} {d e : ℕ} {C C' A A' : ℝ}
    (hf : IsBoundedBy f d C A) (hg : IsBoundedBy g e C' A') :
    IsBoundedBy (f + g) (max d e) (C + C') (max A A') where
  size_nonneg := add_nonneg hf.size_nonneg hg.size_nonneg
  expo_nonneg := le_trans hf.expo_nonneg (le_max_left _ _)
  natDegree_le := by
    intro m
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    exact max_le_max (hf.natDegree_le m) (hg.natDegree_le m)
  coeff_le := by
    intro m i
    have hCnn := hf.size_nonneg
    have hC'nn := hg.size_nonneg
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · have hz : ((f + g) 0) = 0 := by
        show f 0 + g 0 = 0
        simp
      rw [hz]
      simp only [Polynomial.coeff_zero, norm_zero]
      positivity
    · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hpos
      have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
      have h1 : ‖(f m).coeff i‖ ≤ C * (m : ℝ) ^ (max A A') :=
        le_trans (hf.coeff_le m i) (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hm1 (le_max_left _ _)) hCnn)
      have h2 : ‖(g m).coeff i‖ ≤ C' * (m : ℝ) ^ (max A A') :=
        le_trans (hg.coeff_le m i) (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hm1 (le_max_right _ _)) hC'nn)
      calc ‖((f + g) m).coeff i‖ = ‖(f m).coeff i + (g m).coeff i‖ := by congr 1
      _ ≤ ‖(f m).coeff i‖ + ‖(g m).coeff i‖ := norm_add_le _ _
      _ ≤ C * (m : ℝ) ^ (max A A') + C' * (m : ℝ) ^ (max A A') := add_le_add h1 h2
      _ = (C + C') * (m : ℝ) ^ (max A A') := by ring

/-- The realisation is additive. -/
theorem realize_add {f g : DirFormal} {d e : ℕ} {C C' A A' : ℝ}
    (hf : IsBoundedBy f d C A) (hg : IsBoundedBy g e C' A')
    {s : ℝ} (hs : max A A' + 2 ≤ s) :
    realize (f + g) s = realize f s + realize g s := by
  have hsf : A + 2 ≤ s := le_trans (by simp) hs
  have hsg : A' + 2 ≤ s := le_trans (by simp) hs
  rw [realize, realize, realize, ← Summable.tsum_add (summable_realize hf hsf) (summable_realize hg hsg)]
  refine tsum_congr fun m => ?_
  have : ((f + g) m) = f m + g m := rfl
  rw [this, Polynomial.eval_add]
  ring

end DirFormal

end HTGeometry
