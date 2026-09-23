import GaloisForLFunctions.RHTower.LagExplicitFormula

/-!
# The Weil lag function

`Φ(L) = Σ_ρ e^{L(ρ−½)}/(ρ(1−ρ))`, the sum over the nontrivial zeros of `ξ` with multiplicity, is
absolutely convergent for every real `L`, even in `L`, and equals `2 + γ − log 4π` at `L = 0`.  For
`L > 0` it has the exact prime side

`Φ(L) = e^{−L/2} [ (X − ψ(X)) + X (Σ_{n≤X} Λ(n)/n − L + γ) − log 2π + Σ_{k≥1} X^{−2k}/(2k(2k+1)) ]`,
`X = e^L`,

by the explicit formula with the genus kernel.  Under the Riemann hypothesis every term has modulus
`1/|ρ|²`, so `|Φ(L)| ≤ Φ(0)` for all `L`: the sharp lag bound on the prime side.
-/

open Complex Filter Topology
open ArithmeticFunction (vonMangoldt)

namespace RHTower

noncomputable section

/-- The lag function `Φ(L) = Σ_ρ e^{L(ρ−½)}/(ρ(1−ρ))`. -/
def weilLagFunction (L : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))

/-- `‖e^{L(ρ−½)}‖ = e^{L(β−½)} ≤ e^{|L|/2}` on the strip. -/
theorem norm_weilLagTerm_le (L : ℝ) (q : XiZeroCopy) :
    ‖Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤
      Real.exp (|L| / 2) * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by
  rw [div_eq_mul_one_div, norm_mul, Complex.norm_exp]
  gcongr
  have h0 := xiZeroCopy_re_pos q
  have h1 := xiZeroCopy_re_lt_one q
  have hre : ((L : ℂ) * ((q.1 : ℂ) - 1 / 2)).re = L * (((q.1 : ℂ)).re - 1 / 2) := by
    simp [Complex.mul_re]
  rw [hre]
  have hb : |((q.1 : ℂ)).re - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith
  calc L * (((q.1 : ℂ)).re - 1 / 2) ≤ |L * (((q.1 : ℂ)).re - 1 / 2)| := le_abs_self _
    _ = |L| * |((q.1 : ℂ)).re - 1 / 2| := abs_mul _ _
    _ ≤ |L| * (1 / 2) := by gcongr
    _ = |L| / 2 := by ring

theorem summable_weilLagTerm (L : ℝ) :
    Summable (fun q : XiZeroCopy =>
      Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) :=
  Summable.of_norm_bounded
    (g := fun q : XiZeroCopy => Real.exp (|L| / 2) * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖)
    (summable_inv_mul_one_sub.norm.mul_left _) (norm_weilLagTerm_le L)

/-- `Φ(0) = 2 + γ − log 4π`. -/
theorem weilLagFunction_zero : weilLagFunction 0 = poleSharpConstant := by
  unfold weilLagFunction
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  exact tsum_inv_zero_mul_one_sub_zero

/-- `Φ` is even, by the functional-equation reflection `ρ ↦ 1 − ρ`. -/
theorem weilLagFunction_neg (L : ℝ) : weilLagFunction (-L) = weilLagFunction L := by
  unfold weilLagFunction
  rw [← xiZeroCopyReflectEquiv.tsum_eq (fun q : XiZeroCopy =>
    Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))))]
  refine tsum_congr fun q => ?_
  rw [xiZeroCopy_reflect_val]
  congr 1
  · congr 1; push_cast; ring
  · ring

/-- **Prime side of the lag function.**  For `L > 0`, `X = e^L`,
`Φ(L) = e^{−L/2}[(X − ψ(X)) + X(Σ_{n≤X}Λ(n)/n − L + γ) − log 2π + S(X)]`. -/
theorem weilLagFunction_eq_prime_side {L : ℝ} (hL : 0 < L) :
    weilLagFunction L = Real.exp (-L / 2) *
      (((Real.exp L - Chebyshev.psi (Real.exp L) : ℝ) : ℂ) +
        Real.exp L * (((∑ n ∈ Finset.Icc 1 ⌊Real.exp L⌋₊, vonMangoldt n / (n : ℝ) : ℝ) : ℂ) - L +
          Real.eulerMascheroniConstant) -
        Real.log (2 * Real.pi) + trivialZeroSeries (Real.exp L)) := by
  have hX : 1 < Real.exp L := Real.one_lt_exp_iff.mpr hL
  have h := lag_explicit_formula hX
  rw [Real.log_exp] at h
  rw [← h]
  unfold weilLagFunction
  rw [← tsum_mul_left]
  refine tsum_congr fun q => ?_
  have hcp : ((Real.exp L : ℝ) : ℂ) ^ (q.1 : ℂ) = Complex.exp (L * (q.1 : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos L).ne'), Complex.ofReal_exp,
      Complex.log_exp (by simp; linarith [Real.pi_pos]) (by simp; linarith [Real.pi_pos])]
  rw [hcp, Complex.ofReal_exp, mul_div_assoc', ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Under RH every copy has real part `½`. -/
theorem xiZeroCopy_re_eq_half_of_riemannHypothesis (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    ((q.1 : ℂ)).re = 1 / 2 := by
  have h0 := xiZeroCopy_re_pos q
  have hz : riemannZeta (q.1 : ℂ) = 0 :=
    (xi_eq_zero_iff h0 (xiZeroCopy_ne_one q)).mp (xi_xiZeroCopy_eq_zero q)
  refine hRH _ hz ?_ (xiZeroCopy_ne_one q)
  rintro ⟨n, hn⟩
  have := congrArg Complex.re hn
  simp only [Complex.mul_re, Complex.neg_re, Complex.add_re, Complex.natCast_re, Complex.one_re,
    Complex.neg_im, Complex.add_im, Complex.natCast_im, Complex.one_im] at this
  norm_num at this
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- **The sharp lag bound under RH.**  `|Φ(L)| ≤ Φ(0) = 2 + γ − log 4π` for every `L`. -/
theorem norm_weilLagFunction_le_of_riemannHypothesis (hRH : RiemannHypothesis) (L : ℝ) :
    ‖weilLagFunction L‖ ≤ poleSharpConstant := by
  -- each term has the modulus of `1/(ρ(1−ρ))`, a positive real under RH
  have hterm : ∀ q : XiZeroCopy,
      ‖Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ =
        ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by
    intro q
    rw [div_eq_mul_one_div, norm_mul, Complex.norm_exp]
    have hre : ((L : ℂ) * ((q.1 : ℂ) - 1 / 2)).re = L * (((q.1 : ℂ)).re - 1 / 2) := by
      simp [Complex.mul_re]
    rw [hre, xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q]
    simp
  have hreal : ∀ q : XiZeroCopy,
      (1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) = ((‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ : ℝ) : ℂ) := by
    intro q
    set γ : ℝ := ((q.1 : ℂ)).im with hγ
    have hq : (q.1 : ℂ) = 1 / 2 + γ * I := by
      conv_lhs => rw [← Complex.re_add_im (q.1 : ℂ)]
      rw [xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q]
      push_cast; ring
    have hprod : (q.1 : ℂ) * (1 - (q.1 : ℂ)) = ((1 / 4 + γ ^ (2 : ℕ) : ℝ) : ℂ) := by
      rw [hq]; push_cast
      linear_combination (-(γ : ℂ) ^ (2 : ℕ)) * Complex.I_mul_I
    rw [hprod, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  have hsum : Summable (fun q : XiZeroCopy =>
      ‖Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) := by
    simp_rw [hterm]; exact summable_inv_mul_one_sub.norm
  have hval : ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ = poleSharpConstant := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_tsum, ← tsum_inv_zero_mul_one_sub_zero]
    exact tsum_congr fun q => (hreal q).symm
  calc ‖weilLagFunction L‖ ≤ ∑' q : XiZeroCopy,
        ‖Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ :=
        norm_tsum_le_tsum_norm hsum
    _ = ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by simp_rw [hterm]
    _ = poleSharpConstant := hval

/-- **Sharp prime-side bound under RH.**  For `L > 0`, `X = e^L`,
`|e^{−L/2}[(X − ψ(X)) + X(Σ_{n≤X}Λ(n)/n − L + γ) − log 2π + S(X)]| ≤ 2 + γ − log 4π`. -/
theorem prime_side_lag_bound_of_riemannHypothesis (hRH : RiemannHypothesis) {L : ℝ} (hL : 0 < L) :
    ‖(Real.exp (-L / 2) : ℂ) *
      (((Real.exp L - Chebyshev.psi (Real.exp L) : ℝ) : ℂ) +
        Real.exp L * (((∑ n ∈ Finset.Icc 1 ⌊Real.exp L⌋₊, vonMangoldt n / (n : ℝ) : ℝ) : ℂ) - L +
          Real.eulerMascheroniConstant) -
        Real.log (2 * Real.pi) + trivialZeroSeries (Real.exp L))‖ ≤ poleSharpConstant := by
  rw [← weilLagFunction_eq_prime_side hL]
  exact norm_weilLagFunction_le_of_riemannHypothesis hRH L

end

end RHTower
