/-
# The archimedean tier: `ζ`'s reflection cocycle has nonzero curvature

The reflection cocycle `h_F(s) = F(1−s)/F(s)` has a two-tier weld content.  The conductor tier —
the rate `2·log Q` of a pure power cocycle `Q^{2s−1}` — is *flat*: its curvature
`κ_F(s) = (log h_F)''(s)` vanishes identically (`ReflectionCocycleCurvature`).  This module supplies
the complementary archimedean statement: the pure Gamma quotient

`h(s) = Γ_ℝ(s) / Γ_ℝ(1−s)`,

which is (the inverse of) the reflection cocycle of the archimedean factor and governs `ζ`'s
reflection on the strip, has **nonzero** curvature at `s = 3/4`.  So `ζ` sits *off* the flat conductor
locus — its weld lives one tier above the rate lattice.

The mechanism is fully explicit.  On the right half plane
`logDeriv Γ_ℝ(w) = ψ(w/2)/2 − (log π)/2`, so on a neighbourhood of `3/4` the logarithmic derivative
of `h` is `ψ(s/2)/2 + ψ((1−s)/2)/2 − log π`.  Differentiating, the `log π` constant drops and the chain
factors give
`(log h)''(3/4) = (ψ'(3/8) − ψ'(1/8)) / 4`.
The trigamma value `ψ'(x) = Σ_{n≥0} (x+n)⁻²` is a strictly decreasing positive real for `x > 0`; since
`3/8 > 1/8 > 0`, the difference is strictly negative, hence nonzero.
-/
import GaloisForLFunctions.RHTower.ReflectionCocycleCurvature
import GaloisForLFunctions.RHTower.TrigammaVertical

noncomputable section

namespace RHTower

open Complex Filter

/-- **Trigamma as a partial-sum limit.**  For `0 < z.re` the partial sums `Σ_{n<N} (z+n)⁻²` of the
trigamma series converge to `ψ'(z) = deriv ψ z`.  The differentiated digamma recurrence
`ψ'(z+N) = ψ'(z) − Σ_{n<N} (z+n)⁻²` rearranges each partial sum to `ψ'(z) − ψ'(z+N)`, and the
far-field anchor `ψ'(z+N) → 0` sends the shift term to `0`. -/
theorem deriv_digamma_eq_tsum_limit {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, ((z + (n : ℂ)) ^ (2 : ℕ))⁻¹)
      atTop (nhds (deriv Complex.digamma z)) :=
  deriv_digamma_partialSum_tendsto hz

/-- **Strict trigamma monotonicity at two real points.**  For `0 < x < y` the trigamma values obey
`ψ'(y) < ψ'(x)`, so `ψ'(y) − ψ'(x) ≠ 0`.  Each term `(x+n)⁻²` of the trigamma series strictly
dominates `(y+n)⁻²` (the `n = 0` term strictly, the rest at least weakly), so along the partial sums
the real part of the difference stays `≤ (y²)⁻¹ − (x²)⁻¹ < 0`; taking limits keeps the real part
negative, hence the difference is nonzero. -/
theorem deriv_digamma_real_diff_ne {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    deriv Complex.digamma (y : ℂ) - deriv Complex.digamma (x : ℂ) ≠ 0 := by
  have hy : 0 < y := lt_trans hx hxy
  have hyre : 0 < ((y : ℂ)).re := by rw [Complex.ofReal_re]; exact hy
  have hxre : 0 < ((x : ℂ)).re := by rw [Complex.ofReal_re]; exact hx
  have hSre : ∀ (w : ℝ) (N : ℕ),
      (∑ n ∈ Finset.range N, (((w : ℂ) + (n : ℂ)) ^ (2 : ℕ))⁻¹).re
        = ∑ n ∈ Finset.range N, ((w + n) ^ (2 : ℕ))⁻¹ := by
    intro w N
    rw [show (∑ n ∈ Finset.range N, (((w : ℂ) + (n : ℂ)) ^ (2 : ℕ))⁻¹)
          = ((∑ n ∈ Finset.range N, ((w + n) ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) from ?_, Complex.ofReal_re]
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro n _; push_cast; ring
  have hlim := (deriv_digamma_eq_tsum_limit hyre).sub (deriv_digamma_eq_tsum_limit hxre)
  have hlimre : Tendsto (fun N : ℕ =>
      ((∑ n ∈ Finset.range N, (((y : ℂ) + (n : ℂ)) ^ (2 : ℕ))⁻¹)
        - (∑ n ∈ Finset.range N, (((x : ℂ) + (n : ℂ)) ^ (2 : ℕ))⁻¹)).re)
      atTop (nhds ((deriv Complex.digamma (y : ℂ) - deriv Complex.digamma (x : ℂ)).re)) :=
    ((Complex.continuous_re.tendsto _).comp hlim)
  set C : ℝ := (y ^ (2 : ℕ))⁻¹ - (x ^ (2 : ℕ))⁻¹ with hC
  have hCneg : C < 0 := by
    rw [hC]
    have hsq : x ^ (2 : ℕ) < y ^ (2 : ℕ) := by nlinarith
    have hx2 : (0 : ℝ) < x ^ (2 : ℕ) := by positivity
    have : (y ^ (2 : ℕ))⁻¹ < (x ^ (2 : ℕ))⁻¹ := inv_strictAnti₀ hx2 hsq
    linarith
  have hbound : ∀ᶠ N : ℕ in atTop, ((∑ n ∈ Finset.range N, (((y : ℂ) + (n : ℂ)) ^ (2 : ℕ))⁻¹)
        - (∑ n ∈ Finset.range N, (((x : ℂ) + (n : ℂ)) ^ (2 : ℕ))⁻¹)).re ≤ C := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [Complex.sub_re, hSre, hSre, ← Finset.sum_sub_distrib]
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [Finset.sum_range_succ' (fun n => ((y + n) ^ (2 : ℕ))⁻¹ - ((x + n) ^ (2 : ℕ))⁻¹) M]
    have htail : ∑ n ∈ Finset.range M,
        (((y + (n + 1)) ^ (2 : ℕ))⁻¹ - ((x + (n + 1)) ^ (2 : ℕ))⁻¹) ≤ 0 := by
      apply Finset.sum_nonpos
      intro n _
      have hxn : (0 : ℝ) < x + (n + 1) := by positivity
      have hle : (x + (n + 1)) ^ (2 : ℕ) ≤ (y + (n + 1)) ^ (2 : ℕ) := by nlinarith
      have : ((y + (n + 1)) ^ (2 : ℕ))⁻¹ ≤ ((x + (n + 1)) ^ (2 : ℕ))⁻¹ := inv_anti₀ (by positivity) hle
      linarith
    have h0 : ((y + (0 : ℕ)) ^ (2 : ℕ))⁻¹ - ((x + (0 : ℕ)) ^ (2 : ℕ))⁻¹ = C := by
      push_cast; rw [hC]; ring
    simp only [Nat.cast_add, Nat.cast_one] at htail ⊢
    linarith
  have hle : (deriv Complex.digamma (y : ℂ) - deriv Complex.digamma (x : ℂ)).re ≤ C :=
    le_of_tendsto hlimre hbound
  intro hzero
  rw [hzero, Complex.zero_re] at hle
  linarith

/-- **Closed form of the logarithmic derivative of `Γ_ℝ`.**  On the right half plane
`logDeriv Γ_ℝ(w) = ψ(w/2)/2 − (log π)/2`, since `Γ_ℝ'(w) = Γ_ℝ(w)·(ψ(w/2) − log π)/2` and dividing by
the nonvanishing `Γ_ℝ(w)` cancels the factor. -/
theorem logDeriv_Gammaℝ_of_re_pos {w : ℂ} (hw : 0 < w.re) :
    logDeriv Complex.Gammaℝ w = Complex.digamma (w / 2) / 2 - (Real.log Real.pi : ℂ) / 2 := by
  rw [logDeriv_apply, (hasDerivAt_Gammaℝ_of_re_pos hw).deriv]
  rw [mul_comm (Complex.Gammaℝ w) (Complex.digamma (w / 2) / 2 - (Real.log Real.pi : ℂ) / 2),
    mul_div_assoc, div_self (Complex.Gammaℝ_ne_zero_of_re_pos hw), mul_one]

/-- **The archimedean reflection cocycle has nonzero curvature at `3/4`.**  The second logarithmic
derivative of `h(s) = Γ_ℝ(s)/Γ_ℝ(1−s)` — the pure archimedean weld carried by `ζ`'s reflection on the
strip — is nonzero at `s = 3/4`.  On a neighbourhood of `3/4` (where `s` and `1−s` both have positive
real part) `logDeriv h(s) = ψ(s/2)/2 + ψ((1−s)/2)/2 − log π`; its derivative at `3/4` is
`(ψ'(3/8) − ψ'(1/8))/4`, and strict trigamma monotonicity makes this negative, hence nonzero.  This
places `ζ` off the flat (zero-curvature) conductor locus. -/
theorem archReflCocycle_curvature_ne_zero :
    deriv (logDeriv (fun s : ℂ => Complex.Gammaℝ s / Complex.Gammaℝ (1 - s))) (3 / 4 : ℂ) ≠ 0 := by
  -- The logarithmic derivative of `h` agrees with the closed form near `3/4`.
  have hn1 : {s : ℂ | 0 < s.re} ∈ nhds (3 / 4 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hn2 : {s : ℂ | 0 < (1 - s).re} ∈ nhds (3 / 4 : ℂ) :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds (by norm_num)
  have hEq : (logDeriv (fun s : ℂ => Complex.Gammaℝ s / Complex.Gammaℝ (1 - s)))
      =ᶠ[nhds (3 / 4 : ℂ)]
      (fun s : ℂ => (Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2)
        + (Complex.digamma ((1 - s) / 2) / 2 - (Real.log Real.pi : ℂ) / 2)) := by
    filter_upwards [hn1, hn2] with s hs h1s
    have hfs : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs
    have hgs : Complex.Gammaℝ (1 - s) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos h1s
    have hdf : DifferentiableAt ℂ Complex.Gammaℝ s :=
      (hasDerivAt_Gammaℝ_of_re_pos hs).differentiableAt
    have hinner : HasDerivAt (fun z : ℂ => 1 - z) (-1) s := (hasDerivAt_id s).const_sub 1
    have hdg : DifferentiableAt ℂ (fun z => Complex.Gammaℝ (1 - z)) s :=
      ((hasDerivAt_Gammaℝ_of_re_pos h1s).comp s hinner).differentiableAt
    have hLDrefl : logDeriv (fun z => Complex.Gammaℝ (1 - z)) s
        = - logDeriv Complex.Gammaℝ (1 - s) := by
      have hd : HasDerivAt (fun z : ℂ => Complex.Gammaℝ (1 - z))
          (Complex.Gammaℝ (1 - s)
            * (Complex.digamma ((1 - s) / 2) / 2 - (Real.log Real.pi : ℂ) / 2) * (-1)) s :=
        (hasDerivAt_Gammaℝ_of_re_pos h1s).comp s hinner
      rw [logDeriv_apply, hd.deriv, logDeriv_apply, (hasDerivAt_Gammaℝ_of_re_pos h1s).deriv]
      ring
    rw [logDeriv_div (f := Complex.Gammaℝ) (g := fun z => Complex.Gammaℝ (1 - z)) s hfs hgs hdf hdg,
      hLDrefl, logDeriv_Gammaℝ_of_re_pos hs, logDeriv_Gammaℝ_of_re_pos h1s]
    ring
  rw [hEq.deriv_eq]
  -- Differentiate the closed form at `3/4`.
  have hp1 : HasDerivAt (fun s : ℂ => Complex.digamma (s / 2))
      (deriv Complex.digamma ((3 / 8 : ℝ) : ℂ) * ((1 : ℂ) / 2)) (3 / 4) := by
    have hi : HasDerivAt (fun s : ℂ => s / 2) ((1 : ℂ) / 2) (3 / 4) :=
      (hasDerivAt_id (3 / 4 : ℂ)).div_const 2
    have ho : HasDerivAt Complex.digamma (deriv Complex.digamma ((3 / 8 : ℝ) : ℂ))
        ((3 / 4 : ℂ) / 2) := by
      rw [show ((3 / 4 : ℂ)) / 2 = ((3 / 8 : ℝ) : ℂ) by norm_num]
      exact (digamma_analyticOnNhd_re_pos ((3 / 8 : ℝ) : ℂ) (by norm_num)).differentiableAt.hasDerivAt
    exact ho.comp (3 / 4 : ℂ) hi
  have hp2 : HasDerivAt (fun s : ℂ => Complex.digamma ((1 - s) / 2))
      (deriv Complex.digamma ((1 / 8 : ℝ) : ℂ) * (-(1 : ℂ) / 2)) (3 / 4) := by
    have hi : HasDerivAt (fun s : ℂ => (1 - s) / 2) (-(1 : ℂ) / 2) (3 / 4) := by
      have h := ((hasDerivAt_id (3 / 4 : ℂ)).const_sub (1 : ℂ)).div_const 2
      simpa using h
    have ho : HasDerivAt Complex.digamma (deriv Complex.digamma ((1 / 8 : ℝ) : ℂ))
        ((1 - (3 / 4 : ℂ)) / 2) := by
      rw [show ((1 - (3 / 4 : ℂ)) / 2) = ((1 / 8 : ℝ) : ℂ) by norm_num]
      exact (digamma_analyticOnNhd_re_pos ((1 / 8 : ℝ) : ℂ) (by norm_num)).differentiableAt.hasDerivAt
    exact ho.comp (3 / 4 : ℂ) hi
  have hMc : HasDerivAt
      (fun s : ℂ => (Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2)
        + (Complex.digamma ((1 - s) / 2) / 2 - (Real.log Real.pi : ℂ) / 2))
      (deriv Complex.digamma ((3 / 8 : ℝ) : ℂ) * ((1 : ℂ) / 2) / 2
        + deriv Complex.digamma ((1 / 8 : ℝ) : ℂ) * (-(1 : ℂ) / 2) / 2) (3 / 4) :=
    ((hp1.div_const 2).sub_const _).add ((hp2.div_const 2).sub_const _)
  rw [hMc.deriv]
  have hne : deriv Complex.digamma ((3 / 8 : ℝ) : ℂ) - deriv Complex.digamma ((1 / 8 : ℝ) : ℂ) ≠ 0 :=
    deriv_digamma_real_diff_ne (by norm_num) (by norm_num)
  have hrw : deriv Complex.digamma ((3 / 8 : ℝ) : ℂ) * ((1 : ℂ) / 2) / 2
      + deriv Complex.digamma ((1 / 8 : ℝ) : ℂ) * (-(1 : ℂ) / 2) / 2
      = (deriv Complex.digamma ((3 / 8 : ℝ) : ℂ) - deriv Complex.digamma ((1 / 8 : ℝ) : ℂ)) / 4 := by
    ring
  rw [hrw]
  exact div_ne_zero hne (by norm_num)

end RHTower
