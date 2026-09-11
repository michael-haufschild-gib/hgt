import GaloisForLFunctions.RHTower.BVCoPoissonHalfWeightResonance
import GaloisForLFunctions.RHTower.ReflectionCocycleClass
import Mathlib.Analysis.PSeriesComplex

/-!
# Joining two copies of the occupation tower

The all-pairing-degree tower weights by homological occupation and has reduced Euler coefficients
`ε_n = (-1)^(n-1)` at the energies `n a`, so its spectral trace is the Dirichlet eta function. The
join of two complexes multiplies reduced Euler characteristics with a sign and adds energies, so
joining two copies of the whole tower produces the coefficients

  `-∑_{m+n=k} ε_m ε_n = (k-1) (-1)^(k-1)`,

whose Dirichlet series is exactly `η(s-1) - η(s)`. In the strip `0 < Re s < 1` the function
`η(s-1)` never vanishes, so `η(s-1) - η(s)` and `η` have no common zero there: the join of the
occupation tower with itself neither preserves nor removes the eta zeros. This is the precise
content of the warning that fusion is not a zero-preserving operation on spectral traces.

The Dirichlet series of `RHTower.dirichletEta` is proved here for `1 < Re s`; it is the classical
alternating zeta series, and was not yet available in the corpus.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor

noncomputable section
open Complex _root_.RHTower

/-! ### The Euler coefficients of the self-join -/

/-- **The Euler coefficients of the self-join of the occupation tower.** At total index `k = j+2`
the pairs `(m, k - m)` with `m ≥ 1` contribute `ε_m ε_(k-m) = (-1)^j`, and the join sign flips the
total, giving `(k-1)(-1)^(k-1)`. -/
theorem etaJoinEuler (j : ℕ) :
    -(∑ i ∈ Finset.range (j + 1), (-1 : ℤ) ^ i * (-1 : ℤ) ^ (j - i))
      = ((j : ℤ) + 1) * (-1) ^ (j + 1) := by
  have hterm : ∀ i ∈ Finset.range (j + 1),
      (-1 : ℤ) ^ i * (-1 : ℤ) ^ (j - i) = (-1 : ℤ) ^ j := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [← pow_add, show i + (j - i) = j from by omega]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    pow_succ]
  push_cast
  ring

/-! ### The Dirichlet series of the eta function -/

theorem summable_one_div_nat_add_one_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) := by
  have h := (summable_nat_add_iff 1 (f := fun n : ℕ => 1 / (n : ℂ) ^ s)).mpr
    (Complex.summable_one_div_nat_cpow.mpr hs)
  refine h.congr (fun n => ?_)
  push_cast
  ring_nf

theorem cpow_two_mul_succ {s : ℂ} (k : ℕ) :
    ((2 * ((k : ℂ) + 1))) ^ s = (2 : ℂ) ^ s * ((k : ℂ) + 1) ^ s := by
  have h2 : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
  have hk : (((k : ℝ) + 1 : ℝ) : ℂ) = (k : ℂ) + 1 := by push_cast; ring
  have hmul := mul_cpow_ofReal_nonneg (a := (2 : ℝ)) (b := (k : ℝ) + 1)
    (by norm_num) (by positivity) s
  rw [h2, hk] at hmul
  rw [← hmul]

/-- **The alternating zeta series.** -/
theorem dirichletEta_eq_tsum {s : ℂ} (hs : 1 < s.re) :
    dirichletEta s = ∑' n : ℕ, (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ s := by
  have hg : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) :=
    summable_one_div_nat_add_one_cpow hs
  have hzeta : riemannZeta s = ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s :=
    zeta_eq_tsum_one_div_nat_add_one_cpow hs
  have hinj2 : Function.Injective (fun k : ℕ => 2 * k) := fun a b h => by
    have h' : 2 * a = 2 * b := h
    omega
  have hinj2' : Function.Injective (fun k : ℕ => 2 * k + 1) := fun a b h => by
    have h' : 2 * a + 1 = 2 * b + 1 := h
    omega
  have hge : Summable (fun k : ℕ => 1 / ((((2 * k : ℕ)) : ℂ) + 1) ^ s) :=
    hg.comp_injective hinj2
  have hgo : Summable (fun k : ℕ => 1 / ((((2 * k + 1 : ℕ)) : ℂ) + 1) ^ s) :=
    hg.comp_injective hinj2'
  have hfe : Summable (fun k : ℕ => (-1 : ℂ) ^ (2 * k) / ((((2 * k : ℕ)) : ℂ) + 1) ^ s) := by
    refine hge.congr (fun k => ?_)
    rw [pow_mul, neg_one_sq, one_pow]
  have hfo : Summable
      (fun k : ℕ => (-1 : ℂ) ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℂ) + 1) ^ s) := by
    refine (hgo.neg).congr (fun k => ?_)
    rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
    ring
  have hsplitF := tsum_even_add_odd (f := fun n : ℕ => (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ s)
    hfe hfo
  have hsplitG := tsum_even_add_odd (f := fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) hge hgo
  have hE : ∑' k : ℕ, (-1 : ℂ) ^ (2 * k) / ((((2 * k : ℕ)) : ℂ) + 1) ^ s
      = ∑' k : ℕ, 1 / ((((2 * k : ℕ)) : ℂ) + 1) ^ s := by
    refine tsum_congr (fun k => ?_)
    rw [pow_mul, neg_one_sq, one_pow]
  have hO : ∑' k : ℕ, (-1 : ℂ) ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℂ) + 1) ^ s
      = - ∑' k : ℕ, 1 / ((((2 * k + 1 : ℕ)) : ℂ) + 1) ^ s := by
    rw [← tsum_neg]
    refine tsum_congr (fun k => ?_)
    rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
    ring
  have hodd : ∑' k : ℕ, 1 / ((((2 * k + 1 : ℕ)) : ℂ) + 1) ^ s
      = (2 : ℂ) ^ (-s) * riemannZeta s := by
    rw [hzeta, ← tsum_mul_left]
    refine tsum_congr (fun k => ?_)
    have hbase : ((((2 * k + 1 : ℕ)) : ℂ) + 1) = 2 * ((k : ℂ) + 1) := by push_cast; ring
    rw [hbase, cpow_two_mul_succ, cpow_neg]
    have h2 : (2 : ℂ) ^ s ≠ 0 := by
      refine cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
    field_simp
  have heven : ∑' k : ℕ, 1 / ((((2 * k : ℕ)) : ℂ) + 1) ^ s
      = riemannZeta s - (2 : ℂ) ^ (-s) * riemannZeta s := by
    have hsum := hsplitG
    rw [← hzeta, hodd] at hsum
    linear_combination hsum
  have h2ne : (2 : ℂ) ≠ 0 := by norm_num
  have hpow : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
    rw [show (1 : ℂ) - s = 1 + -s from by ring, cpow_add _ _ h2ne, cpow_one]
  rw [dirichletEta, ← hsplitF, hE, hO, hodd, heven, hpow]
  ring

/-! ### The self-join trace is `η(s-1) - η(s)` -/

/-- **The Dirichlet series of the self-join of the occupation tower is `η(s-1) - η(s)`.** -/
theorem etaJoin_tsum {s : ℂ} (hs : 2 < s.re) :
    ∑' n : ℕ, (n : ℂ) * (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ s
      = dirichletEta (s - 1) - dirichletEta s := by
  have hs1 : 1 < (s - 1).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hs0 : 1 < s.re := by linarith
  have hsum1 : Summable (fun n : ℕ => (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ (s - 1)) := by
    refine ((summable_one_div_nat_add_one_cpow hs1).norm).of_norm_bounded_eventually_nat ?_
    filter_upwards with n
    have hb : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow]
    rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) from by push_cast; ring]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hb, norm_div, norm_one,
      Complex.norm_cpow_eq_rpow_re_of_pos hb]
  have hsum2 : Summable (fun n : ℕ => (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ s) := by
    refine ((summable_one_div_nat_add_one_cpow hs0).norm).of_norm_bounded_eventually_nat ?_
    filter_upwards with n
    have hb : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow]
    rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) from by push_cast; ring]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hb, norm_div, norm_one,
      Complex.norm_cpow_eq_rpow_re_of_pos hb]
  rw [dirichletEta_eq_tsum hs1, dirichletEta_eq_tsum hs0,
    ← Summable.tsum_sub hsum1 hsum2]
  refine tsum_congr (fun n => ?_)
  have hne : ((n : ℂ) + 1) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hsub : ((n : ℂ) + 1) ^ (s - 1) = ((n : ℂ) + 1) ^ s / ((n : ℂ) + 1) := by
    rw [cpow_sub _ _ hne, cpow_one]
  have hpow : ((n : ℂ) + 1) ^ s ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hne)
  rw [hsub]
  field_simp
  ring

/-! ### No common strip zero with eta -/

theorem dirichletEta_sub_one_ne_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    dirichletEta (s - 1) ≠ 0 := by
  have hre : (s - 1).re = s.re - 1 := by rw [Complex.sub_re, Complex.one_re]
  rw [dirichletEta]
  refine mul_ne_zero ?_ ?_
  · intro hz
    have hone : (2 : ℂ) ^ (1 - (s - 1)) = 1 := by linear_combination -hz
    have hb : (0 : ℝ) < 2 := by norm_num
    have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
    have hnorm : ‖(2 : ℂ) ^ (1 - (s - 1))‖ = (2 : ℝ) ^ (1 - (s - 1)).re := by
      rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hb]
    rw [hone, norm_one] at hnorm
    have hrew : (1 - (s - 1)).re = 2 - s.re := by
      rw [Complex.sub_re, Complex.one_re, hre]
      ring
    rw [hrew] at hnorm
    have hgt : (1 : ℝ) < (2 : ℝ) ^ (2 - s.re) := by
      refine Real.one_lt_rpow_iff_of_pos hb |>.mpr (Or.inl ⟨by norm_num, by linarith⟩)
    rw [← hnorm] at hgt
    linarith
  · intro hz
    obtain ⟨n, hn⟩ := (RHTower.riemannZeta_eq_zero_iff_of_re_lt_zero
      (s := s - 1) (by rw [hre]; linarith)).mp hz
    have hre2 := congrArg Complex.re hn
    rw [hre] at hre2
    simp at hre2
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith

/-- **The self-join trace and eta have no common zero in the strip.** -/
theorem etaJoin_ne_zero_of_dirichletEta_eq_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : dirichletEta s = 0) : dirichletEta (s - 1) - dirichletEta s ≠ 0 := by
  rw [hz, sub_zero]
  exact dirichletEta_sub_one_ne_zero h0 h1

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
