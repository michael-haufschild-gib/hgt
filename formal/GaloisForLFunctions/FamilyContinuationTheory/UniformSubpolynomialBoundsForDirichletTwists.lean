import GaloisForLFunctions.RHTower.DirichletLSubpolynomial
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62RootNumberNorm
import GaloisForLFunctions.FamilyContinuationTheory.TheSignalExponentIsTheZeroAbscissa

/-!
# Conductor-uniform subpolynomial bounds for Dirichlet twists

`RHTower.exists_lower_bound_subpolynomial` proves that for a single primitive nonprincipal
Dirichlet character `χ`, `‖L(s, χ)‖ ≥ κ(χ) (2 + |Im s|)^{-ε}` right of `zeroAbscissa χ + δ`, using
a compactness bound on the low-height segment `Re w = -2, |t| ≤ 2` whose constant `κ(χ)` depends
inexplicitly on `χ`.

To control mean squares of smoothed Möbius sums over growing families of twists up to `Z^θ`, we
replace that compactness step by an explicit Archimedean ratio across the entire left edge
`Re w = -2`:

* **Root number and right half-plane** (`norm_rootNumber_eq_one_of_primitive`,
  `norm_LFunction_bounds_of_two_le_re`). Every primitive nonprincipal `χ` has `‖χ.rootNumber‖ = 1`,
  and on `Re s ≥ 2` the Basel tail bounds `‖L(s, χ)‖` between `1/4` and `7/4` with absolute
  constants independent of `N` and `χ`.
* **Left edge near the real axis** (`exists_uniform_bound_LFunction_left_edge`). At `w = -2 + it`
  with `0 < |t| ≤ 2`, shifting `Γ((w + d)/2)` to `Re = 1` (`d = 0`) or `Re = 1/2` (`d = 1`) places
  the `t = 0` pole of `Γ(w/2)` in the denominator of `L(w, χ)`, giving an absolute constant `A`
  with `‖L(-2 + it, χ)‖ ≤ A N^{5/2} (1 + |t|³)` for all `t ∈ ℝ` (including `t = 0` by continuity).
* **Conductor-uniform Phragmén–Lindelöf and three circles**
  (`exists_uniform_lower_bound_subpolynomial`). Propagating `O(N^{5/2} ‖z - 4‖³)` across
  `-2 ≤ Re z ≤ 3` and bounding the three-circles interpolation weight uniformly over
  `zeroAbscissa χ ∈ [1/2, 1]` yields an explicit `κ(δ, ε) > 0` independent of `N` and `χ` such
  that `‖L(s, χ)‖ ≥ κ(δ, ε) (N (2 + |Im s|))^{-ε}` for all `Re s ≥ zeroAbscissa χ + δ`.
* **Pole-free Gaussian kernels** (`zetaGaussianKernel`, `dirichletGaussianKernel`,
  `exists_uniform_signal_dirichletGaussianKernel_le`). Using the entire weight
  `gaussianKernel c s = exp((s − c)²)` avoids any pole at `s = 1` for both `ζ` and nonprincipal
  `L(s, χ)`, giving `‖signal (dirichletGaussianKernel χ c) 2 Z‖ ≤ C(c, δ, η) N^η Z^b` uniformly
  across all conductors `N` and all `Z > 0`.
-/

noncomputable section

open Complex MeasureTheory Filter Set Metric
open GaloisForLFunctions.HTGeometry
open scoped Topology

namespace GaloisForLFunctions.FamilyContinuationTheory

/-! ### Modulus-independent root-number and Euler-half-plane bounds -/

theorem norm_rootNumber_eq_one_of_primitive {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) : ‖χ.rootNumber‖ = 1 :=
  RHTower.cglLemma62_primitive_rootNumber_norm_one
    ⟨⟨N, Nat.pos_of_ne_zero (NeZero.ne N)⟩, χ, hχ, hprim⟩

/-- On `Re s ≥ 2`, every Dirichlet `L`-function satisfies `1/4 ≤ ‖L(s, χ)‖ ≤ 7/4`, with constants
independent of the modulus `N` and character `χ`. -/
theorem norm_LFunction_bounds_of_two_le_re {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 2 ≤ s.re) :
    (1 : ℝ) / 4 ≤ ‖DirichletCharacter.LFunction χ s‖ ∧
      ‖DirichletCharacter.LFunction χ s‖ ≤ 7 / 4 := by
  have hs1 : 1 < s.re := by linarith
  have hL := DirichletCharacter.LFunction_eq_LSeries χ hs1
  have hsum : LSeriesSummable (fun n : ℕ => χ n) s :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs1
  have htail_real : (∑' n : ℕ, (1 : ℝ) / (((n + 2 : ℕ) : ℝ)) ^ (2 : ℕ)) ≤ 3 / 4 := by
    have h := RHTower.norm_zetaTail_le (s := (2 : ℂ)) (by simp)
    have hpos : ∀ n : ℕ, 0 ≤ (1 : ℝ) / (((n + 2 : ℕ) : ℝ)) ^ (2 : ℕ) := fun _ => by positivity
    have hrew : (∑' n : ℕ, (1 : ℂ) / ((n : ℂ) + 2) ^ (2 : ℂ)) =
        ((∑' n : ℕ, (1 : ℝ) / (((n + 2 : ℕ) : ℝ)) ^ (2 : ℕ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum]
      refine tsum_congr fun n => ?_
      have hcast : ((n : ℂ) + 2) = (((n + 2 : ℕ) : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
      push_cast
      ring
    rw [hrew, Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg hpos)] at h
    exact h
  have htail_summ : Summable fun n : ℕ => (1 : ℝ) / (((n + 2 : ℕ) : ℝ)) ^ (2 : ℕ) :=
    (summable_nat_add_iff 2).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  have hterm_le : ∀ n : ℕ,
      ‖LSeries.term (fun k : ℕ => χ k) s (n + 2)‖ ≤ (1 : ℝ) / (((n + 2 : ℕ) : ℝ)) ^ (2 : ℕ) := by
    intro n
    have hn0 : n + 2 ≠ 0 := by omega
    rw [LSeries.term_of_ne_zero hn0, norm_div,
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn0)]
    have hbase : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + 2)
    have hpow : (((n + 2 : ℕ) : ℝ)) ^ (2 : ℝ) ≤ (((n + 2 : ℕ) : ℝ)) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le hbase hs
    have hchi : ‖χ ((n + 2 : ℕ) : ZMod N)‖ ≤ 1 := RHTower.norm_dirichletCharacter_le_one χ _
    calc ‖χ ((n + 2 : ℕ) : ZMod N)‖ / (((n + 2 : ℕ) : ℝ)) ^ s.re
        ≤ 1 / (((n + 2 : ℕ) : ℝ)) ^ s.re :=
          div_le_div_of_nonneg_right hchi (by positivity)
      _ ≤ 1 / (((n + 2 : ℕ) : ℝ)) ^ (2 : ℝ) :=
          div_le_div_of_nonneg_left zero_le_one (by positivity) hpow
      _ = 1 / (((n + 2 : ℕ) : ℝ)) ^ (2 : ℕ) := by rw [Real.rpow_two]
  have hshift_summ : Summable fun n : ℕ => LSeries.term (fun k : ℕ => χ k) s (n + 2) :=
    (summable_nat_add_iff 2).mpr hsum
  have hnorm_summ : Summable fun n : ℕ => ‖LSeries.term (fun k : ℕ => χ k) s (n + 2)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_le htail_summ
  have hsplit := hsum.sum_add_tsum_nat_add 2
  have hfin : ∑ i ∈ Finset.range 2, LSeries.term (fun k : ℕ => χ k) s i = 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, LSeries.term_zero, zero_add,
      LSeries.term_of_ne_zero one_ne_zero]
    simp
  rw [hL, LSeries, ← hsplit, hfin]
  have htail_norm : ‖∑' n : ℕ, LSeries.term (fun k : ℕ => χ k) s (n + 2)‖ ≤ 3 / 4 :=
    (norm_tsum_le_tsum_norm hnorm_summ).trans
      ((hnorm_summ.tsum_le_tsum hterm_le htail_summ).trans htail_real)
  constructor
  · have htri := norm_sub_norm_le (1 : ℂ) (-(∑' n : ℕ, LSeries.term (fun k : ℕ => χ k) s (n + 2)))
    rw [sub_neg_eq_add, norm_one, norm_neg] at htri
    linarith
  · have htri := norm_add_le (1 : ℂ) (∑' n : ℕ, LSeries.term (fun k : ℕ => χ k) s (n + 2))
    rw [norm_one] at htri
    linarith

/-! ### Explicit Archimedean ratio on `Re w = -2, 0 < |t| ≤ 2` -/

theorem exists_norm_Gamma_ratio_small_even :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, t ≠ 0 → |t| ≤ 2 →
      ‖Complex.Gamma (((3 : ℂ) - (t : ℂ) * Complex.I + ((0 : ℝ) : ℂ)) / 2)‖ ≤
        A * ‖Complex.Gamma ((((-2 : ℂ) + (t : ℂ) * Complex.I) + ((0 : ℝ) : ℂ)) / 2)‖ := by
  have hcont : ContinuousOn (fun v : ℝ => ‖Complex.Gamma (1 + (v : ℂ) * Complex.I)‖)
      (Set.Icc (-1 : ℝ) 1) := by
    intro v _
    refine (ContinuousAt.norm ?_).continuousWithinAt
    refine (Complex.differentiableAt_Gamma _ fun m hcon => ?_).continuousAt.comp
      (by fun_prop : ContinuousAt (fun u : ℝ => (1 : ℂ) + (u : ℂ) * Complex.I) v)
    have hre := congrArg Complex.re hcon
    simp at hre
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  obtain ⟨v₀, _, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr (by norm_num)) hcont
  have hm₀ : 0 < ‖Complex.Gamma (1 + (v₀ : ℂ) * Complex.I)‖ :=
    norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simp))
  have hG32 : 0 < Real.Gamma (3 / 2) := Real.Gamma_pos_of_pos (by norm_num)
  refine ⟨2 * Real.Gamma (3 / 2) / ‖Complex.Gamma (1 + (v₀ : ℂ) * Complex.I)‖,
    by positivity, fun t htne htle => ?_⟩
  set v : ℝ := t / 2 with hv
  have hvne : v ≠ 0 := by simp [hv, htne]
  have hvabs : |v| ≤ 1 := by
    rw [hv, abs_div, show |(2 : ℝ)| = 2 by norm_num]
    linarith
  have hvmem : v ∈ Set.Icc (-1 : ℝ) 1 := abs_le.mp hvabs
  have hlow : ‖Complex.Gamma (1 + (v₀ : ℂ) * Complex.I)‖ ≤
      ‖Complex.Gamma (1 + (v : ℂ) * Complex.I)‖ := isMinOn_iff.mp hmin v hvmem
  have hshift := norm_Gamma_add_nat (((-1 : ℝ) : ℂ) + (v : ℂ) * Complex.I) 2 fun i hi => by
    interval_cases i
    · intro h
      have hre := congrArg Complex.re h
      simp at hre
    · intro h
      have him := congrArg Complex.im h
      simp [hvne] at him
  have heq2 : ((-1 : ℝ) : ℂ) + (v : ℂ) * Complex.I + ((2 : ℕ) : ℂ) = 1 + (v : ℂ) * Complex.I := by
    push_cast; ring
  rw [heq2, Finset.prod_range_succ, Finset.prod_range_one] at hshift
  have hf0 : ‖((-1 : ℝ) : ℂ) + (v : ℂ) * Complex.I + ((0 : ℕ) : ℂ)‖ ≤ 2 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Nat.cast_zero, add_zero, add_re, ofReal_re, mul_re, I_re, mul_zero, I_im,
      mul_one, sub_zero, add_im, ofReal_im, mul_im, zero_add]
    norm_num
    linarith
  have hf1 : ‖((-1 : ℝ) : ℂ) + (v : ℂ) * Complex.I + ((1 : ℕ) : ℂ)‖ ≤ 1 := by
    have : ((-1 : ℝ) : ℂ) + (v : ℂ) * Complex.I + ((1 : ℕ) : ℂ) = (v : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hvabs
  have hprod : (‖((-1 : ℝ) : ℂ) + (v : ℂ) * Complex.I + ((0 : ℕ) : ℂ)‖ *
      ‖((-1 : ℝ) : ℂ) + (v : ℂ) * Complex.I + ((1 : ℕ) : ℂ)‖) ≤ 2 := by
    nlinarith [norm_nonneg (((-1 : ℝ) : ℂ) + (v : ℂ) * Complex.I + ((1 : ℕ) : ℂ))]
  have hden : ‖Complex.Gamma (1 + (v₀ : ℂ) * Complex.I)‖ ≤
      2 * ‖Complex.Gamma (((-1 : ℝ) : ℂ) + (v : ℂ) * Complex.I)‖ := by
    calc ‖Complex.Gamma (1 + (v₀ : ℂ) * Complex.I)‖
        ≤ ‖Complex.Gamma (1 + (v : ℂ) * Complex.I)‖ := hlow
      _ = _ := hshift
      _ ≤ 2 * ‖Complex.Gamma (((-1 : ℝ) : ℂ) + (v : ℂ) * Complex.I)‖ :=
          mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
  have hnum_re : (((3 : ℂ) - (t : ℂ) * Complex.I + ((0 : ℝ) : ℂ)) / 2).re = 3 / 2 := by simp
  have hnum : ‖Complex.Gamma (((3 : ℂ) - (t : ℂ) * Complex.I + ((0 : ℝ) : ℂ)) / 2)‖ ≤
      Real.Gamma (3 / 2) := by
    have h := norm_Gamma_le_Gamma_re (s := ((3 : ℂ) - (t : ℂ) * Complex.I + ((0 : ℝ) : ℂ)) / 2)
      (by rw [hnum_re]; norm_num)
    rwa [hnum_re] at h
  rw [RHTower.gammaArg_even_den t, ← hv]
  rw [div_mul_eq_mul_div, le_div_iff₀ hm₀]
  calc ‖Complex.Gamma (((3 : ℂ) - (t : ℂ) * Complex.I + ((0 : ℝ) : ℂ)) / 2)‖ *
        ‖Complex.Gamma (1 + (v₀ : ℂ) * Complex.I)‖
      ≤ Real.Gamma (3 / 2) * (2 * ‖Complex.Gamma (((-1 : ℝ) : ℂ) + (v : ℂ) * Complex.I)‖) :=
        mul_le_mul hnum hden hm₀.le hG32.le
    _ = 2 * Real.Gamma (3 / 2) * ‖Complex.Gamma (((-1 : ℝ) : ℂ) + (v : ℂ) * Complex.I)‖ := by
        ring

theorem exists_norm_Gamma_ratio_small_odd :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, |t| ≤ 2 →
      ‖Complex.Gamma (((3 : ℂ) - (t : ℂ) * Complex.I + ((1 : ℝ) : ℂ)) / 2)‖ ≤
        A * ‖Complex.Gamma ((((-2 : ℂ) + (t : ℂ) * Complex.I) + ((1 : ℝ) : ℂ)) / 2)‖ := by
  set m₀ : ℝ := Real.sqrt Real.pi * Real.exp (-(Real.pi / 2))
  have hm₀ : 0 < m₀ := mul_pos (Real.sqrt_pos.mpr Real.pi_pos) (Real.exp_pos _)
  have hG2 : 0 < Real.Gamma 2 := Real.Gamma_pos_of_pos (by norm_num)
  refine ⟨(3 / 2) * Real.Gamma 2 / m₀, by positivity, fun t htle => ?_⟩
  set v : ℝ := t / 2 with hv
  have hvabs : |v| ≤ 1 := by
    rw [hv, abs_div, show |(2 : ℝ)| = 2 by norm_num]
    linarith
  have hexp : Real.exp (-(Real.pi / 2)) ≤ Real.exp (-(Real.pi * |v| / 2)) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [Real.pi_pos]
  have hlow : m₀ ≤ ‖Complex.Gamma (1 / 2 + (v : ℂ) * Complex.I)‖ :=
    (mul_le_mul_of_nonneg_left hexp (Real.sqrt_nonneg _)).trans
      (norm_Gamma_half_add_I_bounds v).1
  have hzne : ((-1 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
  have hshift := norm_Gamma_add_one hzne
  have heq1 : ((-1 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I + 1 = 1 / 2 + (v : ℂ) * Complex.I := by
    push_cast; ring
  rw [heq1] at hshift
  have hf : ‖((-1 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I‖ ≤ 3 / 2 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, I_im, mul_one, sub_zero,
      add_im, ofReal_im, mul_im, zero_add, add_zero]
    rw [abs_of_neg (by norm_num : (-1 / 2 : ℝ) < 0)]
    linarith
  have hden : m₀ ≤ (3 / 2) * ‖Complex.Gamma (((-1 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I)‖ := by
    calc m₀ ≤ ‖Complex.Gamma (1 / 2 + (v : ℂ) * Complex.I)‖ := hlow
      _ = _ := hshift
      _ ≤ (3 / 2) * ‖Complex.Gamma (((-1 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I)‖ :=
          mul_le_mul_of_nonneg_right hf (norm_nonneg _)
  have hnum_re : (((3 : ℂ) - (t : ℂ) * Complex.I + ((1 : ℝ) : ℂ)) / 2).re = 2 := by
    simp; norm_num
  have hnum : ‖Complex.Gamma (((3 : ℂ) - (t : ℂ) * Complex.I + ((1 : ℝ) : ℂ)) / 2)‖ ≤
      Real.Gamma 2 := by
    have h := norm_Gamma_le_Gamma_re (s := ((3 : ℂ) - (t : ℂ) * Complex.I + ((1 : ℝ) : ℂ)) / 2)
      (by rw [hnum_re]; norm_num)
    rwa [hnum_re] at h
  rw [RHTower.gammaArg_odd_den t, ← hv, div_mul_eq_mul_div, le_div_iff₀ hm₀]
  calc ‖Complex.Gamma (((3 : ℂ) - (t : ℂ) * Complex.I + ((1 : ℝ) : ℂ)) / 2)‖ * m₀
      ≤ Real.Gamma 2 * ((3 / 2) * ‖Complex.Gamma (((-1 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I)‖) :=
        mul_le_mul hnum hden hm₀.le hG2.le
    _ = 3 / 2 * Real.Gamma 2 * ‖Complex.Gamma (((-1 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I)‖ := by
        ring

/-! ### Conductor-uniform left-edge, strip, and disc bounds -/

/-- **Conductor-uniform left-edge bound.** There is an absolute constant `A > 0` such that for
every modulus `N`, every primitive nonprincipal `χ : DirichletCharacter ℂ N`, and every `t ∈ ℝ`,
`‖L(-2 + it, χ)‖ ≤ A N^{5/2} (1 + |t|³)`. -/
theorem exists_uniform_bound_LFunction_left_edge :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ ≠ 1 → χ.IsPrimitive → ∀ t : ℝ,
        ‖DirichletCharacter.LFunction χ ((-2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          A * (N : ℝ) ^ ((5 : ℝ) / 2) * (1 + |t| ^ (3 : ℕ)) := by
  obtain ⟨A_odd, hA_odd, hrat_odd⟩ := RHTower.exists_norm_Gamma_ratio_odd
  obtain ⟨A_se, hA_se, hrat_se⟩ := exists_norm_Gamma_ratio_small_even
  obtain ⟨A_so, hA_so, hrat_so⟩ := exists_norm_Gamma_ratio_small_odd
  set M_big : ℝ := max 40 A_odd
  set M_small : ℝ := max A_se A_so
  have hM_big : 0 < M_big := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hM_small : 0 < M_small := lt_of_lt_of_le hA_se (le_max_left _ _)
  set π_max : ℝ := max (Real.pi ^ (-(3 : ℝ) / 2)) (Real.pi ^ (-(2 : ℝ)))
  set π_min : ℝ := min Real.pi (Real.pi ^ ((1 : ℝ) / 2))
  have hπ_max : 0 < π_max := lt_of_lt_of_le (Real.rpow_pos_of_pos Real.pi_pos _) (le_max_left _ _)
  have hπ_min : 0 < π_min := lt_min Real.pi_pos (Real.rpow_pos_of_pos Real.pi_pos _)
  set A : ℝ := (7 / 4) * π_max * max (M_big / 8) M_small / π_min
  have hApos : 0 < A := by positivity
  -- Prove for `t ≠ 0` first, then extend to `t = 0` by continuity.
  have hnonzero : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ ≠ 1 → χ.IsPrimitive → ∀ t : ℝ, t ≠ 0 →
        ‖DirichletCharacter.LFunction χ ((-2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          A * (N : ℝ) ^ ((5 : ℝ) / 2) * (1 + |t| ^ (3 : ℕ)) := by
    intro N _ χ hχ hprim t htne
    obtain ⟨d, hd, hgf⟩ := RHTower.gammaFactor_eq_Gammaℝ χ
    have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
    set w : ℂ := (-2 : ℂ) + (t : ℂ) * Complex.I with hw
    set s : ℂ := (3 : ℂ) - (t : ℂ) * Complex.I with hs
    have hwre : w.re = -2 := by rw [hw]; simp
    have hwim : w.im = t := by rw [hw]; simp
    have hsre : s.re = 3 := by rw [hs]; simp
    have hnum_re : (s + ((d : ℝ) : ℂ)).re = 3 + d := by rw [Complex.add_re, hsre]; simp
    have hden_re : (w + ((d : ℝ) : ℂ)).re = -2 + d := by rw [Complex.add_re, hwre]; simp
    have hden_im : ((w + ((d : ℝ) : ℂ)) / 2).im = t / 2 := by simp [Complex.add_im, hwim]
    have hGden_ne : Complex.Gamma ((w + ((d : ℝ) : ℂ)) / 2) ≠ 0 := by
      refine Complex.Gamma_ne_zero fun m hcon => ?_
      have him := hden_im
      rw [hcon] at him
      simp at him
      exact htne (by linarith)
    have hGden_pos : 0 < ‖Complex.Gamma ((w + ((d : ℝ) : ℂ)) / 2)‖ := norm_pos_iff.mpr hGden_ne
    have hgfden_ne : DirichletCharacter.gammaFactor χ w ≠ 0 := by
      rw [hgf w]
      intro hcon
      rw [Complex.Gammaℝ_eq_zero_iff] at hcon
      obtain ⟨n, hn⟩ := hcon
      have him : (w + ((d : ℝ) : ℂ)).im = t := by rw [Complex.add_im, hwim]; simp
      rw [hn] at him
      simp at him
      exact htne him.symm
    have hgfnum_ne : DirichletCharacter.gammaFactor χ⁻¹ s ≠ 0 := by
      rw [RHTower.gammaFactor_inv, hgf s]
      refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
      rw [hnum_re]
      rcases hd with rfl | rfl <;> norm_num
    have hws : (1 : ℂ) - s = w := by rw [hs, hw]; ring
    have hFE := hprim.completedLFunction_one_sub s
    rw [hws] at hFE
    have hwne : w ≠ 0 := fun h => by rw [h] at hwre; simp at hwre
    have hsne : s ≠ 0 := fun h => by rw [h] at hsre; simp at hsre
    have hΛw : DirichletCharacter.completedLFunction χ w =
        DirichletCharacter.LFunction χ w * DirichletCharacter.gammaFactor χ w := by
      rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ w (Or.inl hwne),
        div_mul_cancel₀ _ hgfden_ne]
    have hΛs : DirichletCharacter.completedLFunction χ⁻¹ s =
        DirichletCharacter.LFunction χ⁻¹ s * DirichletCharacter.gammaFactor χ⁻¹ s := by
      rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ s (Or.inl hsne),
        div_mul_cancel₀ _ hgfnum_ne]
    rw [hΛw, hΛs] at hFE
    have hnorm := congrArg (fun z : ℂ => ‖z‖) hFE
    simp only [norm_mul] at hnorm
    have hNcpow : ‖(N : ℂ) ^ (s - 1 / 2)‖ = (N : ℝ) ^ ((5 : ℝ) / 2) := by
      rw [Complex.norm_natCast_cpow_of_pos hNpos]
      congr 1
      rw [Complex.sub_re, hsre]
      norm_num
    set π₁ : ℝ := Real.pi ^ (-(3 + d) / 2)
    set π₂ : ℝ := Real.pi ^ (-(-2 + d) / 2)
    have hπ₁_le : π₁ ≤ π_max := by
      rcases hd with rfl | rfl
      · simp [π₁, π_max]
      · have : -(3 + (1 : ℝ)) / 2 = -2 := by norm_num
        simp only [π₁, this, π_max, le_max_right]
    have hπ₂_ge : π_min ≤ π₂ := by
      rcases hd with rfl | rfl
      · have : -(-2 + (0 : ℝ)) / 2 = 1 := by norm_num
        simp only [π₂, this, Real.rpow_one, π_min, min_le_left]
      · have : -(-2 + (1 : ℝ)) / 2 = 1 / 2 := by norm_num
        simp only [π₂, this, π_min, min_le_right]
    have hπ₂_pos : 0 < π₂ := lt_of_lt_of_le hπ_min hπ₂_ge
    have hgfden : ‖DirichletCharacter.gammaFactor χ w‖ =
        π₂ * ‖Complex.Gamma ((w + ((d : ℝ) : ℂ)) / 2)‖ := by
      rw [hgf w, norm_Gammaℝ, hden_re]
    have hgfnum : ‖DirichletCharacter.gammaFactor χ⁻¹ s‖ =
        π₁ * ‖Complex.Gamma ((s + ((d : ℝ) : ℂ)) / 2)‖ := by
      rw [RHTower.gammaFactor_inv, hgf s, norm_Gammaℝ, hnum_re]
    rw [hNcpow, norm_rootNumber_eq_one_of_primitive hχ hprim, mul_one, hgfden, hgfnum] at hnorm
    have hLsb : ‖DirichletCharacter.LFunction χ⁻¹ s‖ ≤ 7 / 4 :=
      (norm_LFunction_bounds_of_two_le_re χ⁻¹ (by rw [hsre]; norm_num)).2
    have hGrat : ‖Complex.Gamma ((s + ((d : ℝ) : ℂ)) / 2)‖ ≤
        max (M_big / 8) M_small * (1 + |t| ^ (3 : ℕ)) *
          ‖Complex.Gamma ((w + ((d : ℝ) : ℂ)) / 2)‖ := by
      rcases le_or_gt 2 |t| with hbig | hsmall
      · have hr1 : ‖Complex.Gamma ((s + ((d : ℝ) : ℂ)) / 2)‖ ≤
            M_big * |t / 2| ^ (3 : ℕ) * ‖Complex.Gamma ((w + ((d : ℝ) : ℂ)) / 2)‖ := by
          rcases hd with rfl | rfl
          · exact (RHTower.norm_Gamma_ratio_even hbig).trans
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hGden_pos.le)
          · exact (hrat_odd t hbig).trans
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) hGden_pos.le)
        have habs : |t / 2| ^ (3 : ℕ) = |t| ^ (3 : ℕ) / 8 := by
          rw [abs_div, show |(2 : ℝ)| = 2 by norm_num, div_pow]; norm_num
        rw [habs] at hr1
        refine hr1.trans ?_
        refine mul_le_mul_of_nonneg_right ?_ hGden_pos.le
        have hle1 : M_big / 8 ≤ max (M_big / 8) M_small := le_max_left _ _
        have hle2 : |t| ^ (3 : ℕ) ≤ 1 + |t| ^ (3 : ℕ) := by linarith
        calc M_big * (|t| ^ (3 : ℕ) / 8) = (M_big / 8) * |t| ^ (3 : ℕ) := by ring
          _ ≤ max (M_big / 8) M_small * (1 + |t| ^ (3 : ℕ)) :=
              mul_le_mul hle1 hle2 (by positivity) (by positivity)
      · have hr2 : ‖Complex.Gamma ((s + ((d : ℝ) : ℂ)) / 2)‖ ≤
            M_small * ‖Complex.Gamma ((w + ((d : ℝ) : ℂ)) / 2)‖ := by
          rcases hd with rfl | rfl
          · exact (hrat_se t htne hsmall.le).trans
              (mul_le_mul_of_nonneg_right (le_max_left _ _) hGden_pos.le)
          · exact (hrat_so t hsmall.le).trans
              (mul_le_mul_of_nonneg_right (le_max_right _ _) hGden_pos.le)
        refine hr2.trans ?_
        refine mul_le_mul_of_nonneg_right ?_ hGden_pos.le
        have hle1 : M_small ≤ max (M_big / 8) M_small := le_max_right _ _
        have hle2 : (1 : ℝ) ≤ 1 + |t| ^ (3 : ℕ) := by linarith [pow_nonneg (abs_nonneg t) 3]
        nlinarith
    have hprod : ‖DirichletCharacter.LFunction χ w‖ * π₂ *
        ‖Complex.Gamma ((w + ((d : ℝ) : ℂ)) / 2)‖ ≤
        ((7 / 4) * π_max * max (M_big / 8) M_small) * (N : ℝ) ^ ((5 : ℝ) / 2) *
          (1 + |t| ^ (3 : ℕ)) * ‖Complex.Gamma ((w + ((d : ℝ) : ℂ)) / 2)‖ := by
      calc ‖DirichletCharacter.LFunction χ w‖ * π₂ * ‖Complex.Gamma ((w + ((d : ℝ) : ℂ)) / 2)‖
          = ‖DirichletCharacter.LFunction χ w‖ *
              (π₂ * ‖Complex.Gamma ((w + ((d : ℝ) : ℂ)) / 2)‖) := by ring
        _ = (N : ℝ) ^ ((5 : ℝ) / 2) *
              (‖DirichletCharacter.LFunction χ⁻¹ s‖ *
                (π₁ * ‖Complex.Gamma ((s + ((d : ℝ) : ℂ)) / 2)‖)) := hnorm
        _ ≤ (N : ℝ) ^ ((5 : ℝ) / 2) *
              ((7 / 4) * (π_max * (max (M_big / 8) M_small * (1 + |t| ^ (3 : ℕ)) *
                ‖Complex.Gamma ((w + ((d : ℝ) : ℂ)) / 2)‖))) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hNr.le _)
            refine mul_le_mul hLsb ?_ (by positivity) (by norm_num)
            exact mul_le_mul hπ₁_le hGrat (norm_nonneg _) hπ_max.le
        _ = _ := by ring
    have hcancel := le_of_mul_le_mul_right hprod hGden_pos
    have hπ_step : ‖DirichletCharacter.LFunction χ w‖ * π_min ≤
        ‖DirichletCharacter.LFunction χ w‖ * π₂ :=
      mul_le_mul_of_nonneg_left hπ₂_ge (norm_nonneg _)
    have hdiv : ‖DirichletCharacter.LFunction χ w‖ ≤
        A * (N : ℝ) ^ ((5 : ℝ) / 2) * (1 + |t| ^ (3 : ℕ)) := by
      simp only [A]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hπ_min]
      linarith
    exact hdiv
  refine ⟨A, hApos, fun N _ χ hχ hprim t => ?_⟩
  rcases ne_or_eq t 0 with htne | rfl
  · exact hnonzero N χ hχ hprim t htne
  · have hseq : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hLcont : Continuous fun u : ℝ =>
        ‖DirichletCharacter.LFunction χ ((-2 : ℂ) + (u : ℂ) * Complex.I)‖ :=
      continuous_norm.comp ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
        (by fun_prop))
    have hRcont : Continuous fun u : ℝ => A * (N : ℝ) ^ ((5 : ℝ) / 2) * (1 + |u| ^ (3 : ℕ)) := by
      fun_prop
    exact le_of_tendsto_of_tendsto (hLcont.continuousAt.tendsto.comp hseq)
      (hRcont.continuousAt.tendsto.comp hseq)
      (Eventually.of_forall fun k =>
        hnonzero N χ hχ hprim _ (one_div_ne_zero (by positivity)))

/-- **Conductor-uniform Phragmén–Lindelöf strip bound.** On `-2 ≤ Re z ≤ 3`,
`‖L(z, χ)‖ ≤ C_strip N^{5/2} ‖z - 4‖³` with an absolute constant `C_strip > 0`. -/
theorem exists_uniform_bound_LFunction_strip :
    ∃ C_strip : ℝ, 0 < C_strip ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ ≠ 1 → χ.IsPrimitive → ∀ z : ℂ, -2 ≤ z.re → z.re ≤ 3 →
        ‖DirichletCharacter.LFunction χ z‖ ≤
          C_strip * (N : ℝ) ^ ((5 : ℝ) / 2) * ‖z - 4‖ ^ (3 : ℕ) := by
  obtain ⟨A_left, hA_left, hleft⟩ := exists_uniform_bound_LFunction_left_edge
  set C_strip : ℝ := max (7 / 4) (2 * A_left)
  have hCpos : 0 < C_strip := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨C_strip, hCpos, fun N _ χ hχ hprim z hz1 hz2 => ?_⟩
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hNpow1 : (1 : ℝ) ≤ (N : ℝ) ^ ((5 : ℝ) / 2) :=
    Real.one_le_rpow hN1 (by norm_num)
  have hNpow0 : 0 < (N : ℝ) ^ ((5 : ℝ) / 2) := by positivity
  set M : ℝ := C_strip * (N : ℝ) ^ ((5 : ℝ) / 2)
  have hhr : ∀ w : ℂ, w.re = 3 →
      ‖DirichletCharacter.LFunction χ w / (w - 4) ^ (3 : ℕ)‖ ≤ M := by
    intro w hw
    have hge1 : (1 : ℝ) ≤ ‖w - 4‖ := by
      have h := Complex.abs_re_le_norm (w - 4)
      rw [Complex.sub_re, hw] at h
      norm_num at h
      exact h
    have hpow : (1 : ℝ) ≤ ‖w - 4‖ ^ (3 : ℕ) := one_le_pow₀ hge1
    have hLb := (norm_LFunction_bounds_of_two_le_re χ (s := w) (by rw [hw]; norm_num)).2
    rw [norm_div, norm_pow, div_le_iff₀ (by positivity)]
    have hMge : (7 : ℝ) / 4 ≤ M := by
      calc (7 : ℝ) / 4 ≤ C_strip * 1 := by simp [C_strip]
        _ ≤ C_strip * (N : ℝ) ^ ((5 : ℝ) / 2) := mul_le_mul_of_nonneg_left hNpow1 hCpos.le
    calc ‖DirichletCharacter.LFunction χ w‖ ≤ 7 / 4 := hLb
      _ ≤ M * 1 := by linarith
      _ ≤ M * ‖w - 4‖ ^ (3 : ℕ) := mul_le_mul_of_nonneg_left hpow (by positivity)
  have hhl : ∀ w : ℂ, w.re = -2 →
      ‖DirichletCharacter.LFunction χ w / (w - 4) ^ (3 : ℕ)‖ ≤ M := by
    intro w hw
    have hweq : w = (-2 : ℂ) + (w.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hw]
    have him : |w.im| ≤ ‖w - 4‖ := by
      have h := Complex.abs_im_le_norm (w - 4)
      rwa [Complex.sub_im, show ((4 : ℂ)).im = 0 by norm_num, sub_zero] at h
    have hre6 : (6 : ℝ) ≤ ‖w - 4‖ := by
      have h := Complex.abs_re_le_norm (w - 4)
      rw [Complex.sub_re, hw, show ((4 : ℂ)).re = 4 by norm_num] at h
      norm_num at h
      exact h
    have h1pow : (1 : ℝ) ≤ ‖w - 4‖ ^ (3 : ℕ) := one_le_pow₀ (by linarith)
    have himpow : |w.im| ^ (3 : ℕ) ≤ ‖w - 4‖ ^ (3 : ℕ) :=
      pow_le_pow_left₀ (abs_nonneg _) him 3
    have hLb := hleft N χ hχ hprim w.im
    rw [← hweq] at hLb
    rw [norm_div, norm_pow, div_le_iff₀ (by positivity)]
    have h2A : 2 * A_left ≤ C_strip := le_max_right _ _
    calc ‖DirichletCharacter.LFunction χ w‖
        ≤ A_left * (N : ℝ) ^ ((5 : ℝ) / 2) * (1 + |w.im| ^ (3 : ℕ)) := hLb
      _ ≤ A_left * (N : ℝ) ^ ((5 : ℝ) / 2) * (2 * ‖w - 4‖ ^ (3 : ℕ)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 2 * A_left * (N : ℝ) ^ ((5 : ℝ) / 2) * ‖w - 4‖ ^ (3 : ℕ) := by ring
      _ ≤ C_strip * (N : ℝ) ^ ((5 : ℝ) / 2) * ‖w - 4‖ ^ (3 : ℕ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2A hNpow0.le) (by positivity)
  have hPL := PhragmenLindelof.vertical_strip
    (f := fun w : ℂ => DirichletCharacter.LFunction χ w / (w - 4) ^ (3 : ℕ))
    (a := (-2 : ℝ)) (b := (3 : ℝ)) (C := M) (z := z)
    (RHTower.diffContOnCl_regularized hχ) (RHTower.isBigO_regularized hχ) hhl hhr hz1 hz2
  have hne : z - 4 ≠ 0 := by
    intro h
    have hz4 : z = 4 := by linear_combination h
    rw [hz4] at hz2
    norm_num at hz2
  have hpos : 0 < ‖z - 4‖ ^ (3 : ℕ) := pow_pos (norm_pos_iff.mpr hne) 3
  rwa [norm_div, norm_pow, div_le_iff₀ hpos] at hPL

/-- **Conductor-uniform cubic bound on discs.** -/
theorem exists_uniform_bound_LFunction_disc {a R : ℝ} (hR : 0 ≤ R) (hlow : -2 ≤ a - R) :
    ∃ E₀ : ℝ, 1 ≤ E₀ ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ ≠ 1 → χ.IsPrimitive → ∀ t : ℝ, ∀ z : ℂ, ‖z - ((a : ℂ) + (t : ℝ) * I)‖ ≤ R →
        ‖DirichletCharacter.LFunction χ z‖ ≤
          E₀ * (N : ℝ) ^ ((5 : ℝ) / 2) * (2 + |t|) ^ (3 : ℕ) := by
  obtain ⟨C_strip, hC_strip, hstrip⟩ := exists_uniform_bound_LFunction_strip
  set D : ℝ := R + |a - 4|
  have hD0 : 0 ≤ D := by positivity
  refine ⟨max 1 (7 / 4 + C_strip * (D + 1) ^ (3 : ℕ)), le_max_left _ _,
    fun N _ χ hχ hprim t z hz => ?_⟩
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hNpow1 : (1 : ℝ) ≤ (N : ℝ) ^ ((5 : ℝ) / 2) := Real.one_le_rpow hN1 (by norm_num)
  have hbase3 : (1 : ℝ) ≤ (2 + |t|) ^ (3 : ℕ) := one_le_pow₀ (by linarith [abs_nonneg t])
  set E₀ : ℝ := max 1 (7 / 4 + C_strip * (D + 1) ^ (3 : ℕ))
  have hE₀_ge : 7 / 4 + C_strip * (D + 1) ^ (3 : ℕ) ≤ E₀ := le_max_right _ _
  rcases le_or_gt 2 z.re with hge | hlt
  · have hLb := (norm_LFunction_bounds_of_two_le_re χ hge).2
    have h1 : (7 : ℝ) / 4 ≤ E₀ := by linarith [show (0 : ℝ) ≤ C_strip * (D + 1) ^ (3 : ℕ) by positivity]
    calc ‖DirichletCharacter.LFunction χ z‖ ≤ 7 / 4 := hLb
      _ = (7 / 4) * 1 * 1 := by ring
      _ ≤ E₀ * (N : ℝ) ^ ((5 : ℝ) / 2) * (2 + |t|) ^ (3 : ℕ) :=
          mul_le_mul (mul_le_mul h1 hNpow1 zero_le_one (by linarith)) hbase3 zero_le_one
            (by positivity)
  · set c : ℂ := (a : ℂ) + (t : ℝ) * I
    have hrele : |z.re - a| ≤ R := by
      have hre := Complex.abs_re_le_norm (z - c)
      rw [Complex.sub_re, show c.re = a by simp [c]] at hre
      exact hre.trans hz
    have hre2 : -2 ≤ z.re := by linarith [(abs_le.mp hrele).1]
    have hre3 : z.re ≤ 3 := by linarith
    have hz4 : ‖z - 4‖ ≤ (D + 1) * (2 + |t|) := by
      have h1 : ‖z - 4‖ ≤ ‖z - c‖ + ‖c - 4‖ := by
        simpa [sub_add_sub_cancel] using norm_add_le (z - c) (c - 4)
      have h2 : ‖c - 4‖ ≤ |a - 4| + |t| := by
        refine (Complex.norm_le_abs_re_add_abs_im (c - 4)).trans ?_
        simp [c]
      have h3 : ‖z - 4‖ ≤ D + |t| := by simp only [D]; linarith
      nlinarith [abs_nonneg t]
    calc ‖DirichletCharacter.LFunction χ z‖
        ≤ C_strip * (N : ℝ) ^ ((5 : ℝ) / 2) * ‖z - 4‖ ^ (3 : ℕ) := hstrip N χ hχ hprim z hre2 hre3
      _ ≤ C_strip * (N : ℝ) ^ ((5 : ℝ) / 2) * ((D + 1) * (2 + |t|)) ^ (3 : ℕ) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz4 3) (by positivity)
      _ = C_strip * (D + 1) ^ (3 : ℕ) * (N : ℝ) ^ ((5 : ℝ) / 2) * (2 + |t|) ^ (3 : ℕ) := by ring
      _ ≤ E₀ * (N : ℝ) ^ ((5 : ℝ) / 2) * (2 + |t|) ^ (3 : ℕ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (by positivity)

/-! ### Conductor-uniform three-circles and subpolynomial lower bounds -/

/-- **Conductor-uniform three-circles lower bound.** For every `δ ∈ (0, 1)`, there exist `B > 0`,
`K > 0`, and `θ ∈ [0, 1)` independent of `N` and `χ` such that for every primitive nonprincipal
`χ : DirichletCharacter ℂ N` and every `s` with `zeroAbscissa χ + δ ≤ s.re`,
`‖L(s, χ)‖ ≥ (1/4) exp(-B (K (1 + log(N (2 + |Im s|))))^θ)`. -/
theorem exists_uniform_three_circles_lower_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ B K θ : ℝ, 0 < B ∧ 0 < K ∧ 0 ≤ θ ∧ θ < 1 ∧
      ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
        χ ≠ 1 → χ.IsPrimitive → ∀ s : ℂ, RHTower.zeroAbscissa χ + δ ≤ s.re →
          (1 : ℝ) / 4 * Real.exp (-(B * (K * (1 + Real.log ((N : ℝ) * (2 + |s.im|)))) ^ θ)) ≤
            ‖DirichletCharacter.LFunction χ s‖ := by
  -- Fix three-circles centre abscissa `a = 3` (`m = 1/4`, `M_i = 7/4`).
  obtain ⟨E₀, hE₀1, hdisc_unif⟩ :=
    exists_uniform_bound_LFunction_disc (a := 3) (R := 5 / 2) (by norm_num) (by norm_num)
  set B : ℝ := 2 * (Real.log ((7 / 4 : ℝ) / (1 / 4)) + 1) * (1 / 4) / (1 / 2 - 1 / 4)
  have hlog7 : 0 ≤ Real.log ((7 / 4 : ℝ) / (1 / 4)) := Real.log_nonneg (by norm_num)
  have hB1 : 1 ≤ B := by
    have : B = 2 * (Real.log ((7 / 4 : ℝ) / (1 / 4)) + 1) := by simp only [B]; ring
    linarith
  have hB0 : 0 < B := by linarith
  set K : ℝ := 20 / δ * (Real.log (4 * E₀) + 4)
  have hlog4E : 0 ≤ Real.log (4 * E₀) := Real.log_nonneg (by linarith)
  have hK1 : 1 ≤ K := by
    have h20 : 20 ≤ 20 / δ := by rw [le_div_iff₀ hδ]; linarith
    simp only [K]
    nlinarith
  have hK0 : 0 < K := by linarith
  -- Uniform interpolation weight `< 1` across all `Θ ∈ [1/2, 1]`.
  set D_max : ℝ := Real.log (5 / 2) - Real.log (1 / 4)
  set gap_min : ℝ := Real.log (1 + δ / 5)
  have hD_max : 0 < D_max := sub_pos.mpr (Real.log_lt_log (by norm_num) (by norm_num))
  have hgap_min : 0 < gap_min := Real.log_pos (by linarith)
  have hgap_lt : gap_min < D_max := by
    have h1 : 1 + δ / 5 < 10 := by linarith
    have h2 : Real.log 10 = Real.log ((5 / 2 : ℝ) / (1 / 4)) := by norm_num
    rw [show D_max = Real.log ((5 / 2 : ℝ) / (1 / 4)) from (Real.log_div (by norm_num) (by norm_num)).symm,
      ← h2]
    exact Real.log_lt_log (by positivity) h1
  set θ_u : ℝ := 1 - gap_min / D_max
  have hθ0 : 0 ≤ θ_u := by
    simp only [θ_u, sub_nonneg]
    exact (div_le_one hD_max).mpr hgap_lt.le
  have hθ1 : θ_u < 1 := by
    simp only [θ_u, sub_lt_self_iff]
    exact div_pos hgap_min hD_max
  refine ⟨B, K, θ_u, hB0, hK0, hθ0, hθ1, fun N _ χ hχ hprim s hs => ?_⟩
  set Θ : ℝ := RHTower.zeroAbscissa χ
  have hΘhalf : (1 : ℝ) / 2 ≤ Θ := RHTower.half_le_zeroAbscissa hχ hprim
  have hΘone : Θ ≤ 1 := RHTower.zeroAbscissa_le_one hχ hprim
  set t : ℝ := s.im
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hu2 : (2 : ℝ) ≤ (N : ℝ) * (2 + |t|) := by nlinarith [abs_nonneg t]
  have hlogu : 0 ≤ Real.log ((N : ℝ) * (2 + |t|)) := Real.log_nonneg (by linarith)
  have hexpnn : 0 ≤ B * (K * (1 + Real.log ((N : ℝ) * (2 + |t|)))) ^ θ_u :=
    mul_nonneg hB0.le (Real.rpow_nonneg (by positivity) _)
  rcases lt_or_ge (3 - 1 / 4) s.re with hfar | hnear
  · have hge := (norm_LFunction_bounds_of_two_le_re χ (s := s) (by linarith)).1
    have hexple : Real.exp (-(B * (K * (1 + Real.log ((N : ℝ) * (2 + |t|)))) ^ θ_u)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    nlinarith
  · set r₃ : ℝ := 3 - (Θ + δ / 2)
    set R : ℝ := 3 - (Θ + δ / 4)
    have hr₃_lo : (3 : ℝ) / 2 ≤ r₃ := by simp only [r₃]; linarith
    have hr₃_hi : r₃ ≤ 5 / 2 := by simp only [r₃]; linarith
    have hR_hi : R ≤ 5 / 2 := by simp only [R]; linarith
    have hr₁r₃ : (1 : ℝ) / 4 < r₃ := by linarith
    have hr₃R : r₃ < R := by simp only [r₃, R]; linarith
    set c : ℂ := (3 : ℂ) + (t : ℝ) * I
    have hcre : c.re = 3 := by simp [c]
    have hscnorm : ‖s - c‖ = 3 - s.re := by
      have hsc : s - c = (((s.re - 3 : ℝ)) : ℂ) := by apply Complex.ext <;> simp [c, t]
      rw [hsc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      ring
    have hz1 : (1 : ℝ) / 4 ≤ ‖s - c‖ := by rw [hscnorm]; linarith
    have hz3 : ‖s - c‖ ≤ r₃ := by simp only [hscnorm, r₃]; linarith
    have hne : ∀ z ∈ ball c R, DirichletCharacter.LFunction χ z ≠ 0 := by
      intro z hz
      rw [mem_ball, dist_eq_norm] at hz
      have hre := (abs_lt.mp (lt_of_le_of_lt (Complex.abs_re_le_norm (z - c)) hz)).1
      rw [Complex.sub_re, hcre] at hre
      exact RHTower.LFunction_ne_zero_of_zeroAbscissa_lt hχ (by simp only [R, Θ] at hre ⊢; linarith)
    have hf : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) (ball c R) :=
      (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
    have hMi : ∀ z ∈ ball c (1 / 2), ‖DirichletCharacter.LFunction χ z‖ ≤ 7 / 4 := by
      intro z hz
      rw [mem_ball, dist_eq_norm] at hz
      have hre := (abs_lt.mp (lt_of_le_of_lt (Complex.abs_re_le_norm (z - c)) hz)).1
      rw [Complex.sub_re, hcre] at hre
      exact (norm_LFunction_bounds_of_two_le_re χ (by linarith)).2
    have hmc : (1 : ℝ) / 4 ≤ ‖DirichletCharacter.LFunction χ c‖ :=
      (norm_LFunction_bounds_of_two_le_re χ (by rw [hcre]; norm_num)).1
    set E_N : ℝ := E₀ * (N : ℝ) ^ ((5 : ℝ) / 2)
    have hM : ∀ z ∈ ball c R, ‖DirichletCharacter.LFunction χ z‖ ≤ E_N * (2 + |t|) ^ (3 : ℕ) := by
      intro z hz
      rw [mem_ball, dist_eq_norm] at hz
      exact hdisc_unif N χ hχ hprim t z (hz.le.trans hR_hi)
    have hmain := norm_lower_bound_of_two_radii (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num : (1 : ℝ) / 4 < 1 / 2) (by linarith : (1 : ℝ) / 2 ≤ R) hr₁r₃ hr₃R
      hf hne hMi (by norm_num : (0 : ℝ) < 1 / 4) hmc hM (by norm_num : (0 : ℝ) < 1 / 4) hmc
      hz1 hz3
    set w : ℝ := (Real.log ‖s - c‖ - Real.log (1 / 4)) / (Real.log r₃ - Real.log (1 / 4))
    have hden_pos : 0 < Real.log r₃ - Real.log (1 / 4) :=
      sub_pos.mpr (Real.log_lt_log (by norm_num) hr₁r₃)
    have hden_le : Real.log r₃ - Real.log (1 / 4) ≤ D_max := by
      simp only [D_max]
      linarith [Real.log_le_log (by linarith) hr₃_hi]
    have hw0 : 0 ≤ w := div_nonneg (sub_nonneg.mpr (Real.log_le_log (by norm_num) hz1)) hden_pos.le
    have hwθ : w ≤ θ_u := by
      have hsc_le : ‖s - c‖ ≤ 3 - Θ - δ := by rw [hscnorm]; linarith
      have hpos_3 : 0 < 3 - Θ - δ := by linarith
      have hw_le : w ≤ (Real.log (3 - Θ - δ) - Real.log (1 / 4)) /
          (Real.log r₃ - Real.log (1 / 4)) := by
        refine div_le_div_of_nonneg_right ?_ hden_pos.le
        linarith [Real.log_le_log (by linarith) hsc_le]
      have hrew : (Real.log (3 - Θ - δ) - Real.log (1 / 4)) / (Real.log r₃ - Real.log (1 / 4)) =
          1 - Real.log (r₃ / (3 - Θ - δ)) / (Real.log r₃ - Real.log (1 / 4)) := by
        rw [Real.log_div (by linarith) hpos_3.ne']
        have hne_d : Real.log r₃ - Real.log (1 / 4) ≠ 0 := hden_pos.ne'
        field_simp
        ring
      have hquot : 1 + δ / 5 ≤ r₃ / (3 - Θ - δ) := by
        rw [le_div_iff₀ hpos_3]
        have h3Θ : 3 - Θ - δ ≤ 5 / 2 := by linarith only [hΘhalf, hδ]
        have hr₃_def : r₃ = 3 - Θ - δ / 2 := by simp only [r₃]; ring
        rw [hr₃_def]
        nlinarith only [h3Θ, hδ]
      have hlog_ge : gap_min ≤ Real.log (r₃ / (3 - Θ - δ)) :=
        Real.log_le_log (by positivity) hquot
      have hdiv_ge : gap_min / D_max ≤
          Real.log (r₃ / (3 - Θ - δ)) / (Real.log r₃ - Real.log (1 / 4)) :=
        div_le_div₀ (hgap_min.le.trans hlog_ge) hlog_ge hden_pos hden_le
      linarith only [hw_le, hrew, hdiv_ge, show θ_u = 1 - gap_min / D_max from rfl]
    -- Compare the outer Borel–Carathéodory constant with `K (1 + log(N (2 + |t|)))`.
    set X : ℝ := 2 * (Real.log (E_N * (2 + |t|) ^ (3 : ℕ) / (1 / 4)) + 1) * r₃ / (R - r₃)
    have hRr : R - r₃ = δ / 4 := by simp only [R, r₃]; ring
    have hMm : E_N * (2 + |t|) ^ (3 : ℕ) / (1 / 4) =
        4 * E₀ * ((N : ℝ) ^ ((5 : ℝ) / 2) * (2 + |t|) ^ (3 : ℕ)) := by
      simp only [E_N]; ring
    have hpow_le : (N : ℝ) ^ ((5 : ℝ) / 2) * (2 + |t|) ^ (3 : ℕ) ≤
        ((N : ℝ) * (2 + |t|)) ^ (3 : ℕ) := by
      rw [mul_pow, ← Real.rpow_natCast (N : ℝ) 3]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)) (by positivity)
    have hlog_le : Real.log (E_N * (2 + |t|) ^ (3 : ℕ) / (1 / 4)) ≤
        Real.log (4 * E₀) + 3 * Real.log ((N : ℝ) * (2 + |t|)) := by
      rw [hMm, Real.log_mul (by linarith only [hE₀1]) (by positivity)]
      have h1 := Real.log_le_log (by positivity) hpow_le
      rw [Real.log_pow] at h1
      push_cast at h1
      linarith only [h1]
    have hge1 : 1 ≤ E_N * (2 + |t|) ^ (3 : ℕ) / (1 / 4) := by
      rw [hMm]
      exact one_le_mul_of_one_le_of_one_le (by linarith only [hE₀1])
        (one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hN1 (by norm_num))
          (one_le_pow₀ (by linarith only [abs_nonneg t])))
    have hlog0 : 0 ≤ Real.log (E_N * (2 + |t|) ^ (3 : ℕ) / (1 / 4)) := Real.log_nonneg hge1
    have hX0 : 0 ≤ X := by
      have h1 : 0 ≤ 2 * (Real.log (E_N * (2 + |t|) ^ (3 : ℕ) / (1 / 4)) + 1) := by
        linarith only [hlog0]
      exact div_nonneg (mul_nonneg h1 (by linarith only [hr₃_lo]))
        (by rw [hRr]; positivity)
    have hX_le : X ≤ K * (1 + Real.log ((N : ℝ) * (2 + |t|))) := by
      have h8r : 2 * r₃ / (δ / 4) ≤ 20 / δ := by
        rw [div_le_div_iff₀ (by positivity) hδ]
        nlinarith only [hr₃_hi, hδ]
      have hkey : Real.log (4 * E₀) + 3 * Real.log ((N : ℝ) * (2 + |t|)) + 1 ≤
          (Real.log (4 * E₀) + 4) * (1 + Real.log ((N : ℝ) * (2 + |t|))) := by
        nlinarith only [hlog4E, hlogu]
      calc X = (2 * r₃ / (R - r₃)) * (Real.log (E_N * (2 + |t|) ^ (3 : ℕ) / (1 / 4)) + 1) := by
              simp only [X]; ring
        _ ≤ (20 / δ) * (Real.log (4 * E₀) + 3 * Real.log ((N : ℝ) * (2 + |t|)) + 1) := by
            rw [hRr]
            exact mul_le_mul h8r (by linarith only [hlog_le])
              (by linarith only [hlog0]) (by positivity)
        _ ≤ (20 / δ) * ((Real.log (4 * E₀) + 4) * (1 + Real.log ((N : ℝ) * (2 + |t|)))) :=
            mul_le_mul_of_nonneg_left hkey (by positivity)
        _ = K * (1 + Real.log ((N : ℝ) * (2 + |t|))) := by simp only [K]; ring
    have hY1 : 1 ≤ K * (1 + Real.log ((N : ℝ) * (2 + |t|))) :=
      one_le_mul_of_one_le_of_one_le hK1 (by linarith only [hlogu])
    have hpow1 : B ^ (1 - w) ≤ B := by
      calc B ^ (1 - w) ≤ B ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB1 (by linarith only [hw0])
        _ = B := Real.rpow_one B
    have hpow2 : X ^ w ≤ (K * (1 + Real.log ((N : ℝ) * (2 + |t|)))) ^ θ_u :=
      (Real.rpow_le_rpow hX0 hX_le hw0).trans (Real.rpow_le_rpow_of_exponent_le hY1 hwθ)
    have hprod : B ^ (1 - w) * X ^ w ≤ B * (K * (1 + Real.log ((N : ℝ) * (2 + |t|)))) ^ θ_u :=
      mul_le_mul hpow1 hpow2 (Real.rpow_nonneg hX0 _) hB0.le
    calc (1 : ℝ) / 4 * Real.exp (-(B * (K * (1 + Real.log ((N : ℝ) * (2 + |t|)))) ^ θ_u))
        ≤ (1 / 4) * Real.exp (-(B ^ (1 - w) * X ^ w)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hprod])) (by norm_num)
      _ ≤ ‖DirichletCharacter.LFunction χ c‖ * Real.exp (-(B ^ (1 - w) * X ^ w)) :=
          mul_le_mul_of_nonneg_right hmc (Real.exp_pos _).le
      _ ≤ ‖DirichletCharacter.LFunction χ s‖ := hmain

/-- **Conductor-uniform subpolynomial lower bound.** For every `δ ∈ (0, 1)` and `ε > 0`, there is
`κ > 0` independent of `N` and `χ` such that for every primitive nonprincipal
`χ : DirichletCharacter ℂ N` and every `s` with `zeroAbscissa χ + δ ≤ s.re`,
`κ * (N (2 + |Im s|))^{-ε} ≤ ‖L(s, χ)‖`. -/
theorem exists_uniform_lower_bound_subpolynomial {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hε : 0 < ε) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ ≠ 1 → χ.IsPrimitive → ∀ s : ℂ, RHTower.zeroAbscissa χ + δ ≤ s.re →
        κ * ((N : ℝ) * (2 + |s.im|)) ^ (-ε) ≤ ‖DirichletCharacter.LFunction χ s‖ := by
  obtain ⟨B, K, θ, hB, hK, hθ0, hθ1, hbd⟩ := exists_uniform_three_circles_lower_bound hδ hδ1
  have hbasepos : ∀ u : ℝ, 2 ≤ u → 0 < K * (1 + Real.log u) :=
    fun u hu => mul_pos hK (by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ u)])
  have hcont : ContinuousOn (fun u : ℝ => Real.exp (ε * Real.log u -
      B * (K * (1 + Real.log u)) ^ θ)) (Set.Ici 2) := by
    refine Real.continuous_exp.comp_continuousOn (ContinuousOn.sub ?_ ?_)
    · refine continuousOn_const.mul (Real.continuousOn_log.mono fun u hu => ?_)
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have : (2 : ℝ) ≤ u := hu
      linarith
    · refine continuousOn_const.mul (ContinuousOn.rpow_const ?_
        fun u hu => Or.inl (hbasepos u hu).ne')
      refine continuousOn_const.mul (continuousOn_const.add
        (Real.continuousOn_log.mono fun u hu => ?_))
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have : (2 : ℝ) ≤ u := hu
      linarith
  have hlim : Tendsto (fun u : ℝ => Real.exp (ε * Real.log u -
      B * (K * (1 + Real.log u)) ^ θ)) atTop atTop := by
    refine Real.tendsto_exp_atTop.comp ?_
    have hinner : Tendsto (fun L : ℝ => ε * L - B * (K * (1 + L)) ^ θ) atTop atTop := by
      refine tendsto_atTop_mono' _ ?_
        (Tendsto.const_mul_atTop (by linarith : 0 < ε / 2) tendsto_id)
      filter_upwards [eventually_const_mul_rpow_le (c := B * (K ^ θ * 2 ^ θ)) (ε := ε / 2)
          hθ1 (by linarith only [hε]),
        eventually_ge_atTop (1 : ℝ)] with L hL hL1
      simp only [id_eq]
      have hsplit : (K * (1 + L)) ^ θ = K ^ θ * (1 + L) ^ θ := Real.mul_rpow hK.le (by linarith)
      have h2L : (1 + L) ^ θ ≤ (2 * L) ^ θ := Real.rpow_le_rpow (by linarith) (by linarith) hθ0
      have h2L' : (2 * L) ^ θ = 2 ^ θ * L ^ θ := Real.mul_rpow (by norm_num) (by linarith)
      have hKθ : 0 ≤ K ^ θ := Real.rpow_nonneg hK.le _
      have hmid : B * (K * (1 + L)) ^ θ ≤ B * (K ^ θ * 2 ^ θ) * L ^ θ := by
        rw [hsplit]
        calc B * (K ^ θ * (1 + L) ^ θ)
            ≤ B * (K ^ θ * (2 * L) ^ θ) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2L hKθ) hB.le
          _ = B * (K ^ θ * 2 ^ θ) * L ^ θ := by rw [h2L']; ring
      linarith only [hL, hmid]
    exact hinner.comp Real.tendsto_log_atTop
  obtain ⟨κ₀, hκ₀, hκ⟩ := exists_pos_lower_bound_of_tendsto_atTop hcont
    (fun u _ => Real.exp_pos _) hlim
  refine ⟨κ₀ / 4, by positivity, fun N _ χ hχ hprim s hs => ?_⟩
  have h1 := hbd N χ hχ hprim s hs
  set u : ℝ := (N : ℝ) * (2 + |s.im|)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hu2 : 2 ≤ u := by simp only [u]; nlinarith [abs_nonneg s.im]
  have hupos : 0 < u := by linarith
  have hκu := hκ u hu2
  have hrpow : u ^ (-ε) = Real.exp (-(ε * Real.log u)) := by
    rw [Real.rpow_def_of_pos hupos]; ring_nf
  rw [hrpow]
  have hstep : κ₀ * Real.exp (-(ε * Real.log u)) ≤
      Real.exp (-(B * (K * (1 + Real.log u)) ^ θ)) := by
    calc κ₀ * Real.exp (-(ε * Real.log u))
        ≤ Real.exp (ε * Real.log u - B * (K * (1 + Real.log u)) ^ θ) *
            Real.exp (-(ε * Real.log u)) :=
          mul_le_mul_of_nonneg_right hκu (Real.exp_pos _).le
      _ = Real.exp (-(B * (K * (1 + Real.log u)) ^ θ)) := by
          rw [← Real.exp_add]; ring_nf
  linarith

/-! ### Pole-free Gaussian kernels for `ζ` and Dirichlet `L`-functions -/

/-- Entire Gaussian weight `exp((s − c)²)`; its inverse Mellin signal at `Z/m` is a strictly
positive log-Gaussian smooth cutoff without any pole at `s = 1` or `s = 0`. -/
def gaussianKernel (c : ℝ) (s : ℂ) : ℂ := cexp ((s - c) ^ 2)

/-- Zeta kernel for the pole-free Gaussian cutoff: `(s − 1) exp((s − c)²) / ((s − 1) ζ(s))`,
holomorphic across `s = 1` and equal to `exp((s − c)²) / ζ(s)` on `Re s > 1`. -/
def zetaGaussianKernel (c : ℝ) (s : ℂ) : ℂ :=
  (s - 1) * cexp ((s - c) ^ 2) / RHTower.zetaEntire s

/-- Dirichlet kernel for the pole-free Gaussian cutoff: `exp((s − c)²) / L(s, χ)`. -/
def dirichletGaussianKernel {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (c : ℝ) (s : ℂ) : ℂ :=
  cexp ((s - c) ^ 2) / DirichletCharacter.LFunction χ s

theorem exp_neg_sq_mul_sq_le (t : ℝ) :
    Real.exp (-(t ^ 2)) * (2 + |t|) ^ (2 : ℕ) ≤ 54 / (1 + t ^ 2) := by
  have hpos : 0 < 1 + t ^ 2 := by positivity
  have hE : 0 < Real.exp (t ^ 2) := Real.exp_pos _
  have hA : 2 + |t| ≤ 3 * (1 + t ^ 2) := by
    nlinarith [sq_nonneg (|t| - 1 / 2), sq_abs t, abs_nonneg t]
  have hser := Real.sum_le_exp_of_nonneg (sq_nonneg t) 4
  simp [Finset.sum_range_succ, Nat.factorial] at hser
  have hB : (1 + t ^ 2) ^ (3 : ℕ) ≤ 6 * Real.exp (t ^ 2) := by
    nlinarith [sq_nonneg t, pow_nonneg (sq_nonneg t) 3]
  have hX : (2 + |t|) ^ (2 : ℕ) * (1 + t ^ 2) ≤ 54 * Real.exp (t ^ 2) := by
    have hA2 : (2 + |t|) ^ (2 : ℕ) ≤ 9 * (1 + t ^ 2) ^ (2 : ℕ) := by
      nlinarith [abs_nonneg t]
    calc (2 + |t|) ^ (2 : ℕ) * (1 + t ^ 2)
        ≤ 9 * (1 + t ^ 2) ^ (2 : ℕ) * (1 + t ^ 2) := mul_le_mul_of_nonneg_right hA2 hpos.le
      _ = 9 * (1 + t ^ 2) ^ (3 : ℕ) := by ring
      _ ≤ 9 * (6 * Real.exp (t ^ 2)) := mul_le_mul_of_nonneg_left hB (by norm_num)
      _ = 54 * Real.exp (t ^ 2) := by ring
  rw [le_div_iff₀ hpos, Real.exp_neg]
  calc (Real.exp (t ^ 2))⁻¹ * (2 + |t|) ^ (2 : ℕ) * (1 + t ^ 2)
      = (Real.exp (t ^ 2))⁻¹ * ((2 + |t|) ^ (2 : ℕ) * (1 + t ^ 2)) := by ring
    _ ≤ (Real.exp (t ^ 2))⁻¹ * (54 * Real.exp (t ^ 2)) :=
        mul_le_mul_of_nonneg_left hX (inv_nonneg.mpr hE.le)
    _ = 54 := by field_simp

theorem isSignalKernel_zetaGaussianKernel (c : ℝ) : IsSignalKernel (zetaGaussianKernel c) where
  differentiableAt s hs := by
    unfold zetaGaussianKernel
    exact (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => (w - 1) * cexp ((w - c) ^ 2)) s).div
      (RHTower.differentiable_zetaEntire s) (zetaEntire_ne_zero_of_one_lt_re hs)
  decay B := by
    refine ⟨4 * Real.exp ((B + |c|) ^ 2), fun s h2 hB => ?_⟩
    have hs1 : s ≠ 1 := fun h => by rw [h] at h2; norm_num at h2
    have hz : (1 : ℝ) / 4 ≤ ‖riemannZeta s‖ := RHTower.norm_riemannZeta_ge_of_two_le_re h2
    have hzeq : zetaGaussianKernel c s = cexp ((s - c) ^ 2) / riemannZeta s := by
      unfold zetaGaussianKernel
      rw [RHTower.zetaEntire_eq hs1]
      exact mul_div_mul_left _ _ (sub_ne_zero.mpr hs1)
    rw [hzeq, norm_div, div_le_iff₀ (lt_of_lt_of_le (by norm_num) hz)]
    have hsq : (s.re - c) ^ 2 ≤ (B + |c|) ^ 2 := by
      have habs : |s.re - c| ≤ B + |c| := abs_le.mpr ⟨by linarith [neg_abs_le c, le_abs_self c],
        by linarith [neg_abs_le c, le_abs_self c]⟩
      calc (s.re - c) ^ 2 = |s.re - c| ^ 2 := (sq_abs _).symm
        _ ≤ (B + |c|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
    have hexp : Real.exp (-(s.im ^ 2)) ≤ 1 / (1 + s.im ^ 2) := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp (s.im ^ 2)])
    calc ‖cexp ((s - c) ^ 2)‖
        = Real.exp ((s.re - c) ^ 2) * Real.exp (-(s.im ^ 2)) := by
            rw [norm_cexp_sub_sq, sub_eq_add_neg, Real.exp_add]
      _ ≤ Real.exp ((B + |c|) ^ 2) * (1 / (1 + s.im ^ 2)) :=
          mul_le_mul (Real.exp_le_exp.mpr hsq) hexp (Real.exp_pos _).le (Real.exp_pos _).le
      _ = 4 * Real.exp ((B + |c|) ^ 2) / (1 + s.im ^ 2) * (1 / 4) := by ring
      _ ≤ 4 * Real.exp ((B + |c|) ^ 2) / (1 + s.im ^ 2) * ‖riemannZeta s‖ :=
          mul_le_mul_of_nonneg_left hz (by positivity)

theorem riemannZeta_ne_zero_of_signal_zetaGaussianKernel_le {c b K Z₀ : ℝ} (hb : b < 1)
    (hZ₀ : 0 < Z₀) (hK : ∀ Z : ℝ, Z₀ ≤ Z → ‖signal (zetaGaussianKernel c) 2 Z‖ ≤ K * Z ^ b)
    (ρ : ℂ) (hρ : b < ρ.re) (hρ1 : ρ ≠ 1) : riemannZeta ρ ≠ 0 := by
  obtain ⟨F, hFdiff, hFeq⟩ := exists_differentiableOn_eq_of_signal_le
    (isSignalKernel_zetaGaussianKernel c) (by linarith : b < 2) hZ₀ hK
  set U : Set ℂ := {s : ℂ | b < s.re}
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
  have hA1 : AnalyticOnNhd ℂ (fun s => F s * RHTower.zetaEntire s) U :=
    (hFdiff.mul RHTower.differentiable_zetaEntire.differentiableOn).analyticOnNhd hUo
  have hA2 : AnalyticOnNhd ℂ (fun s : ℂ => (s - 1) * cexp ((s - c) ^ 2)) U :=
    (by fun_prop : Differentiable ℂ fun s : ℂ => (s - 1) * cexp ((s - c) ^ 2)).differentiableOn.analyticOnNhd hUo
  have h2mem : (2 : ℂ) ∈ U := by change b < (2 : ℂ).re; simp; linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ),
      F z * RHTower.zetaEntire z = (z - 1) * cexp ((z - c) ^ 2) := by
    rw [frequently_iff]
    intro S hS
    obtain ⟨ε, hε, hεS⟩ := Metric.mem_nhdsWithin_iff.mp hS
    set z₀ : ℂ := (2 : ℂ) + ((min (ε / 2) (1 / 2) : ℝ) : ℂ)
    have hmin_pos : 0 < min (ε / 2) (1 / 2) := lt_min (by positivity) (by norm_num)
    refine ⟨z₀, hεS ⟨?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      simp only [z₀, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg hmin_pos.le]
      linarith [min_le_left (ε / 2) (1 / 2)]
    · intro h
      have := congrArg Complex.re h
      simp [z₀] at this
      linarith
    · have hzre : max b 1 < z₀.re := by
        simp only [z₀, add_re, re_ofNat, ofReal_re]
        rw [max_eq_right hb.le]
        linarith
      rw [hFeq z₀ hzre]
      unfold zetaGaussianKernel
      exact div_mul_cancel₀ _ (zetaEntire_ne_zero_of_one_lt_re (lt_of_le_of_lt (le_max_right b 1) hzre))
  have hid := hA1.eqOn_of_preconnected_of_frequently_eq hA2 (convex_halfSpace_re_gt b).isPreconnected
    h2mem hfreq hρ
  intro hzero
  have hze : RHTower.zetaEntire ρ = 0 := by rw [RHTower.zetaEntire_eq hρ1, hzero, mul_zero]
  change F ρ * RHTower.zetaEntire ρ = (ρ - 1) * cexp ((ρ - c) ^ 2) at hid
  rw [hze, mul_zero] at hid
  exact mul_ne_zero (sub_ne_zero.mpr hρ1) (Complex.exp_ne_zero _) hid.symm

theorem exists_signal_zetaKernel_le_of_zeroFree_strip {Θ : ℝ} (hΘ : (1 : ℝ) / 2 ≤ Θ)
    (hΘ1 : Θ ≤ 1) (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0) (c : ℝ) {b : ℝ}
    (hb : Θ < b) (hb1 : b < Θ + 1) (hb2 : b ≤ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ Z : ℝ, 0 < Z → ‖signal (zetaKernel c) 2 Z‖ ≤ K * Z ^ b := by
  obtain ⟨C, hC⟩ := exists_norm_zetaKernel_le_of_zeroFree hΘ hΘ1 hzf c
    (by linarith : 0 < b - Θ) (by linarith : b - Θ < 1)
  have hC' : ∀ s : ℂ, b ≤ s.re → s.re ≤ 2 → ‖zetaKernel c s‖ ≤ C / (1 + s.im ^ 2) :=
    fun s h1 h2 => hC s (by linarith) h2
  have hC0 : 0 ≤ C := by
    have h2 := hC 2 (by simp; linarith) (by simp)
    have hnn : 0 ≤ ‖zetaKernel c 2‖ := norm_nonneg _
    simp at h2
    linarith
  refine ⟨(C + 1) / 2, by positivity, fun Z hZ => ?_⟩
  have hC'' : ∀ s : ℂ, b ≤ s.re → s.re ≤ 2 → ‖zetaKernel c s‖ ≤ (C + 1) / (1 + s.im ^ 2) :=
    fun s h1 h2 => (hC' s h1 h2).trans (div_le_div_of_nonneg_right (by linarith) (by positivity))
  rw [signal_eq_of_decay hb2
    (fun s h1 _ => by
      unfold zetaKernel
      exact (by fun_prop : DifferentiableAt ℂ (fun s : ℂ => cexp ((s - c) ^ 2)) s).div
        (RHTower.differentiable_zetaEntire s) (zetaEntire_ne_zero_of_zeroFree hzf (by linarith)))
    hC'' hZ]
  exact norm_signal_le (fun s hs => hC'' s hs.ge (by linarith)) hZ

theorem exists_signal_zetaGaussianKernel_le_of_zeroFree {Θ : ℝ} (hΘ : (1 : ℝ) / 2 ≤ Θ)
    (hΘ1 : Θ ≤ 1) (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0) (c : ℝ) {b : ℝ}
    (hb : Θ < b) (hb1 : b < Θ + 1) (hb2 : b ≤ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ Z : ℝ, 0 < Z → ‖signal (zetaGaussianKernel c) 2 Z‖ ≤ K * Z ^ b := by
  obtain ⟨κ, hκ, hlow⟩ := exists_le_norm_zetaEntire_of_zeroFree hΘ hΘ1 hzf
    (by linarith : 0 < b - Θ) (by linarith : b - Θ < 1)
  set C : ℝ := 54 * Real.exp ((2 + |c|) ^ 2) / κ
  have hCpos : 0 < C := by positivity
  have hdecay : ∀ s : ℂ, b ≤ s.re → s.re ≤ 2 →
      ‖zetaGaussianKernel c s‖ ≤ C / (1 + s.im ^ 2) := by
    intro s hlo hhi
    have hz := hlow s (by linarith) hhi
    have hzpos : 0 < ‖RHTower.zetaEntire s‖ := lt_of_lt_of_le (div_pos hκ (by positivity)) hz
    have hs1_le : ‖s - 1‖ ≤ 2 + |s.im| := by
      refine (Complex.norm_le_abs_re_add_abs_im (s - 1)).trans ?_
      rw [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
      have : |s.re - 1| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    have hsq : (s.re - c) ^ 2 ≤ (2 + |c|) ^ 2 := by
      have habs : |s.re - c| ≤ 2 + |c| := abs_le.mpr ⟨by linarith [neg_abs_le c, le_abs_self c],
        by linarith [neg_abs_le c, le_abs_self c]⟩
      calc (s.re - c) ^ 2 = |s.re - c| ^ 2 := (sq_abs _).symm
        _ ≤ (2 + |c|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
    unfold zetaGaussianKernel
    rw [norm_div, norm_mul, div_le_iff₀ hzpos]
    have hG := exp_neg_sq_mul_sq_le s.im
    calc ‖s - 1‖ * ‖cexp ((s - c) ^ 2)‖
        ≤ (2 + |s.im|) * (Real.exp ((2 + |c|) ^ 2) * Real.exp (-(s.im ^ 2))) := by
            refine mul_le_mul hs1_le ?_ (norm_nonneg _) (by positivity)
            rw [norm_cexp_sub_sq, sub_eq_add_neg, Real.exp_add]
            exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hsq) (Real.exp_pos _).le
      _ = Real.exp ((2 + |c|) ^ 2) * (Real.exp (-(s.im ^ 2)) * (2 + |s.im|) ^ (2 : ℕ)) / κ *
            (κ / (2 + |s.im|)) := by
            have : (0 : ℝ) < 2 + |s.im| := by positivity
            field_simp
      _ ≤ Real.exp ((2 + |c|) ^ 2) * (54 / (1 + s.im ^ 2)) / κ * (κ / (2 + |s.im|)) :=
          mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hG (Real.exp_pos _).le) hκ.le)
            (by positivity)
      _ = C / (1 + s.im ^ 2) * (κ / (2 + |s.im|)) := by simp only [C]; ring
      _ ≤ C / (1 + s.im ^ 2) * ‖RHTower.zetaEntire s‖ :=
          mul_le_mul_of_nonneg_left hz (by positivity)
  refine ⟨C / 2, by positivity, fun Z hZ => ?_⟩
  rw [signal_eq_of_decay hb2
    (fun s h1 _ => by
      unfold zetaGaussianKernel
      exact (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => (w - 1) * cexp ((w - c) ^ 2)) s).div
        (RHTower.differentiable_zetaEntire s)
        (zetaEntire_ne_zero_of_zeroFree hzf (by linarith)))
    hdecay hZ]
  exact norm_signal_le (fun s hs => hdecay s hs.ge (by linarith)) hZ

theorem isSignalKernel_dirichletGaussianKernel {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (c : ℝ) : IsSignalKernel (dirichletGaussianKernel χ c) where
  differentiableAt s hs := by
    unfold dirichletGaussianKernel
    exact (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => cexp ((w - c) ^ 2)) s).div
      (DirichletCharacter.differentiable_LFunction hχ s)
      (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs.le)
  decay B := by
    refine ⟨4 * Real.exp ((B + |c|) ^ 2), fun s h2 hB => ?_⟩
    have hz := (norm_LFunction_bounds_of_two_le_re χ h2).1
    unfold dirichletGaussianKernel
    rw [norm_div, div_le_iff₀ (lt_of_lt_of_le (by norm_num) hz)]
    have hsq : (s.re - c) ^ 2 ≤ (B + |c|) ^ 2 := by
      have habs : |s.re - c| ≤ B + |c| := abs_le.mpr ⟨by linarith [neg_abs_le c, le_abs_self c],
        by linarith [neg_abs_le c, le_abs_self c]⟩
      calc (s.re - c) ^ 2 = |s.re - c| ^ 2 := (sq_abs _).symm
        _ ≤ (B + |c|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
    have hexp : Real.exp (-(s.im ^ 2)) ≤ 1 / (1 + s.im ^ 2) := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp (s.im ^ 2)])
    calc ‖cexp ((s - c) ^ 2)‖
        = Real.exp ((s.re - c) ^ 2) * Real.exp (-(s.im ^ 2)) := by
            rw [norm_cexp_sub_sq, sub_eq_add_neg, Real.exp_add]
      _ ≤ Real.exp ((B + |c|) ^ 2) * (1 / (1 + s.im ^ 2)) :=
          mul_le_mul (Real.exp_le_exp.mpr hsq) hexp (Real.exp_pos _).le (Real.exp_pos _).le
      _ = 4 * Real.exp ((B + |c|) ^ 2) / (1 + s.im ^ 2) * (1 / 4) := by ring
      _ ≤ 4 * Real.exp ((B + |c|) ^ 2) / (1 + s.im ^ 2) * ‖DirichletCharacter.LFunction χ s‖ :=
          mul_le_mul_of_nonneg_left hz (by positivity)

theorem LFunction_ne_zero_of_signal_dirichletGaussianKernel_le {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {c b K Z₀ : ℝ} (hb : b < 1) (hZ₀ : 0 < Z₀)
    (hK : ∀ Z : ℝ, Z₀ ≤ Z → ‖signal (dirichletGaussianKernel χ c) 2 Z‖ ≤ K * Z ^ b)
    (ρ : ℂ) (hρ : b < ρ.re) : DirichletCharacter.LFunction χ ρ ≠ 0 := by
  refine ne_zero_of_signal_le (isSignalKernel_dirichletGaussianKernel hχ c) hb hZ₀ hK
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
    (by fun_prop : Differentiable ℂ fun s : ℂ => cexp ((s - c) ^ 2)).differentiableOn
    (fun _ _ => Complex.exp_ne_zero _) (fun s hs => ?_) ρ hρ
  unfold dirichletGaussianKernel
  exact div_mul_cancel₀ _ (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs.le)

/-- **Conductor-uniform signal bound for primitive Dirichlet twists.** For every Gaussian centre
`c`, gap `δ ∈ (0, 1)`, and conductor exponent `η > 0`, there is `C_sig > 0` independent of `N` and
`χ` such that for every primitive nonprincipal `χ : DirichletCharacter ℂ N`, every
`b ∈ [zeroAbscissa χ + δ, 2]`, and every `Z > 0`,
`‖signal (dirichletGaussianKernel χ c) 2 Z‖ ≤ C_sig * N^η * Z^b`. -/
theorem exists_uniform_signal_dirichletGaussianKernel_le (c : ℝ) {δ η : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < 1) (hη : 0 < η) :
    ∃ C_sig : ℝ, 0 < C_sig ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ ≠ 1 → χ.IsPrimitive → ∀ b : ℝ, RHTower.zeroAbscissa χ + δ ≤ b → b ≤ 2 →
        ∀ Z : ℝ, 0 < Z →
          ‖signal (dirichletGaussianKernel χ c) 2 Z‖ ≤ C_sig * (N : ℝ) ^ η * Z ^ b := by
  set ε : ℝ := min η 1
  have hε : 0 < ε := lt_min hη one_pos
  obtain ⟨κ, hκ, hlow⟩ := exists_uniform_lower_bound_subpolynomial hδ hδ1 hε
  set C₀ : ℝ := 12 * Real.exp ((2 + |c|) ^ 2) / κ
  have hC₀ : 0 < C₀ := by positivity
  refine ⟨C₀ / 2, by positivity, fun N _ χ hχ hprim b hb_lo hb_hi Z hZ => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hNpos : (0 : ℝ) < N := by linarith
  have hdecay : ∀ s : ℂ, b ≤ s.re → s.re ≤ 2 →
      ‖dirichletGaussianKernel χ c s‖ ≤ (C₀ * (N : ℝ) ^ η) / (1 + s.im ^ 2) := by
    intro s h1 h2
    have hLs := hlow N χ hχ hprim s (hb_lo.trans h1)
    have h2pos : (0 : ℝ) < 2 + |s.im| := by positivity
    have h2ge1 : (1 : ℝ) ≤ 2 + |s.im| := by linarith [abs_nonneg s.im]
    have hsplit : ((N : ℝ) * (2 + |s.im|)) ^ (-ε) = (N : ℝ) ^ (-ε) * (2 + |s.im|) ^ (-ε) :=
      Real.mul_rpow hNpos.le h2pos.le
    have hNpow : (N : ℝ) ^ (-η) ≤ (N : ℝ) ^ (-ε) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by simp only [ε]; linarith [min_le_left η 1])
    have htpow : (2 + |s.im|)⁻¹ ≤ (2 + |s.im|) ^ (-ε) := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le h2ge1 (by simp only [ε]; linarith [min_le_right η 1])
    have hLge : κ * (N : ℝ) ^ (-η) / (2 + |s.im|) ≤ ‖DirichletCharacter.LFunction χ s‖ := by
      rw [div_eq_mul_inv, mul_assoc]
      refine (mul_le_mul_of_nonneg_left
        (mul_le_mul hNpow htpow (by positivity) (by positivity)) hκ.le).trans ?_
      rwa [← hsplit]
    have hLpos : 0 < ‖DirichletCharacter.LFunction χ s‖ :=
      lt_of_lt_of_le (div_pos (mul_pos hκ (Real.rpow_pos_of_pos hNpos _)) h2pos) hLge
    have hsq : (s.re - c) ^ 2 ≤ (2 + |c|) ^ 2 := by
      have habs : |s.re - c| ≤ 2 + |c| := by
        have hhalf := RHTower.half_le_zeroAbscissa hχ hprim
        exact abs_le.mpr ⟨by linarith [neg_abs_le c, le_abs_self c],
          by linarith [neg_abs_le c, le_abs_self c]⟩
      calc (s.re - c) ^ 2 = |s.re - c| ^ 2 := (sq_abs _).symm
        _ ≤ (2 + |c|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
    have hG := exp_neg_sq_mul_le s.im
    have hN_inv : (N : ℝ) ^ η * (N : ℝ) ^ (-η) = 1 := by
      rw [← Real.rpow_add hNpos, add_neg_cancel, Real.rpow_zero]
    unfold dirichletGaussianKernel
    rw [norm_div, div_le_iff₀ hLpos]
    calc ‖cexp ((s - c) ^ 2)‖
        ≤ Real.exp ((2 + |c|) ^ 2) * Real.exp (-(s.im ^ 2)) := by
            rw [norm_cexp_sub_sq, sub_eq_add_neg, Real.exp_add]
            exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hsq) (Real.exp_pos _).le
      _ = Real.exp ((2 + |c|) ^ 2) * (Real.exp (-(s.im ^ 2)) * (2 + |s.im|)) / κ *
            ((N : ℝ) ^ η * (N : ℝ) ^ (-η)) * (κ / (2 + |s.im|)) := by
            rw [hN_inv, mul_one]
            field_simp
      _ = Real.exp ((2 + |c|) ^ 2) * (Real.exp (-(s.im ^ 2)) * (2 + |s.im|)) / κ *
            (N : ℝ) ^ η * (κ * (N : ℝ) ^ (-η) / (2 + |s.im|)) := by ring
      _ ≤ Real.exp ((2 + |c|) ^ 2) * (12 / (1 + s.im ^ 2)) / κ *
            (N : ℝ) ^ η * (κ * (N : ℝ) ^ (-η) / (2 + |s.im|)) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity))
              (by positivity)
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hG (Real.exp_pos _).le) hκ.le
      _ = (C₀ * (N : ℝ) ^ η) / (1 + s.im ^ 2) * (κ * (N : ℝ) ^ (-η) / (2 + |s.im|)) := by
            simp only [C₀]; ring
      _ ≤ (C₀ * (N : ℝ) ^ η) / (1 + s.im ^ 2) * ‖DirichletCharacter.LFunction χ s‖ :=
          mul_le_mul_of_nonneg_left hLge (by positivity)
  rw [signal_eq_of_decay hb_hi
    (fun s h1 _ => by
      unfold dirichletGaussianKernel
      exact (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => cexp ((w - c) ^ 2)) s).div
        (DirichletCharacter.differentiable_LFunction hχ s)
        (RHTower.LFunction_ne_zero_of_zeroAbscissa_lt hχ (by linarith)))
    hdecay hZ]
  have hsig := norm_signal_le (fun s hs => hdecay s hs.ge (by linarith)) hZ
  calc ‖signal (dirichletGaussianKernel χ c) b Z‖
      ≤ C₀ * (N : ℝ) ^ η / 2 * Z ^ b := hsig
    _ = C₀ / 2 * (N : ℝ) ^ η * Z ^ b := by ring

end GaloisForLFunctions.FamilyContinuationTheory
