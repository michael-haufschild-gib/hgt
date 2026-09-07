import GaloisForLFunctions.RHTower.MontgomeryPairFormTruncation
import GaloisForLFunctions.RHTower.XiLogDerivSymmetry

/-!
# Montgomery's lemma in prime-side form

Montgomery's lemma (`montgomery_lemma_one`) expresses the zero side
`Σ_ρ 2x^ρ/((ρ − a)(ρ − b))`, `a = 3/2 + it`, `b = −1/2 + it`, through the finite von Mangoldt sum
up to `x` and the values of `ξ'/ξ` at `a` and `b`.  Expanding `ξ'/ξ` at `a` and at
`1 − b = 3/2 − it` into polar, archimedean and zeta parts, every non-prime term carrying `x^a`
cancels exactly, and the identity becomes

`Σ_ρ 2x^ρ/((ρ−a)(ρ−b)) = Σ_n Λ(n)·((x/n)^b if n ≤ x else (x/n)^a) + [x/(1−a) − x/(1−b)]
   + x^b [L(Λ, 1−b) − ½ψ((1−b)/2) − ½ψ(b/2+1) + log π − 1/(−b)] − 2 Σ_k x^{−2(k+1)}/((c_k−a)(c_k−b))`.

The prime side is `x^{1/2+it} Σ_n Λ(n) n^{−1/2−it} min(n/x, x/n)`; the three remainder blocks are
`O(x/(1+t²))`, `O(x^{−1/2} log(|t|+2))` and `O(x^{−2}/(1+|t|))`.
-/

open Complex Filter Topology
open ArithmeticFunction (vonMangoldt)

namespace RHTower

/-! ## The conjugate pole and the digamma shift sum -/

theorem one_sub_montgomeryPoleDown (t : ℝ) :
    1 - montgomeryPoleDown t = montgomeryPoleUp (-t) := by
  simp only [montgomeryPoleDown, montgomeryPoleUp]; push_cast; ring

theorem montgomeryPoleUp_ne_zero (t : ℝ) : montgomeryPoleUp t ≠ 0 := by
  intro h; have := congrArg Complex.re h; rw [montgomeryPoleUp_re] at this; norm_num at this

theorem montgomeryPoleUp_sub_one_ne_zero (t : ℝ) : montgomeryPoleUp t - 1 ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp [montgomeryPoleUp_re] at this; norm_num at this

theorem one_sub_montgomeryPoleUp_ne_zero (t : ℝ) : 1 - montgomeryPoleUp t ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp [montgomeryPoleUp_re] at this; norm_num at this

/-- `Σ_{k≥0} (1/(k+2) − 2/(s + 2(k+1))) = ψ(s/2 + 1) + γ − 1` for `Re s > −2`. -/
theorem tsum_digammaShiftTerm_eq {s : ℂ} (hs : -2 < s.re) :
    ∑' k : ℕ, digammaShiftTerm s k
      = Complex.digamma (s / 2 + 1) + (Real.eulerMascheroniConstant : ℂ) - 1 := by
  have hre : 0 < (s / 2 + 1).re := by simp; linarith
  have h1 := hasSum_digammaSeries hre
  have h2 := hasSum_digammaTelescoping
  have h := h1.sub h2
  have hf : (fun k : ℕ => (1 / ((k : ℂ) + 1) - 1 / (s / 2 + 1 + k))
      - (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + 2))) = digammaShiftTerm s := by
    funext k
    unfold digammaShiftTerm
    have : s / 2 + 1 + (k : ℂ) = (s + 2 * ((k : ℂ) + 1)) / 2 := by ring
    rw [this, one_div_div]; ring
  rw [hf] at h
  rw [h.tsum_eq]

/-! ## The prime side -/

/-- The prime-side summand `Λ(n) · ((x/n)^b if n ≤ x else (x/n)^a)`. -/
noncomputable def primeSideTerm (x t : ℝ) (n : ℕ) : ℂ :=
  ((vonMangoldt n : ℝ) : ℂ) *
    (if (n : ℝ) ≤ x then ((x / n : ℝ) : ℂ) ^ montgomeryPoleDown t
      else ((x / n : ℝ) : ℂ) ^ montgomeryPoleUp t)

/-- The prime side `Σ_n Λ(n) · ((x/n)^b if n ≤ x else (x/n)^a)`. -/
noncomputable def primeSide (x t : ℝ) : ℂ := ∑' n : ℕ, primeSideTerm x t n

theorem ofReal_div_cpow {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 0 < n) (s : ℂ) :
    ((x / n : ℝ) : ℂ) ^ s = (x : ℂ) ^ s / (n : ℂ) ^ s := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv,
    show ((x : ℂ) * ((n : ℝ) : ℂ)⁻¹) = (x : ℂ) * (((n : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
    Complex.mul_cpow_ofReal_nonneg hx.le (by positivity), Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hn'.le]; exact Real.pi_ne_zero.symm),
    div_eq_mul_inv]
  push_cast; rfl

/-- `x^s · L(Λ, s) = Σ_n Λ(n) (x/n)^s` for `Re s > 1`. -/
theorem cpow_mul_LSeries_vonMangoldt {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ) ^ s * LSeries (fun n => ((vonMangoldt n : ℝ) : ℂ)) s
      = ∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) * ((x / n : ℝ) : ℂ) ^ s := by
  rw [LSeries, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn.ne', ofReal_div_cpow hx hn]
    ring

theorem summable_vonMangoldt_mul_cpow {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => ((vonMangoldt n : ℝ) : ℂ) * ((x / n : ℝ) : ℂ) ^ s) := by
  have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).mul_left ((x : ℂ) ^ s)
  refine h.congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn.ne', ofReal_div_cpow hx hn]
    ring

theorem primeSideTerm_eq (x t : ℝ) (n : ℕ) :
    primeSideTerm x t n = ((vonMangoldt n : ℝ) : ℂ) * ((x / n : ℝ) : ℂ) ^ montgomeryPoleUp t
      + (if (n : ℝ) ≤ x then ((vonMangoldt n : ℝ) : ℂ) *
          (((x / n : ℝ) : ℂ) ^ montgomeryPoleDown t - ((x / n : ℝ) : ℂ) ^ montgomeryPoleUp t)
        else 0) := by
  unfold primeSideTerm
  split_ifs <;> ring

/-- The prime side as `x^a L(Λ,a)` plus the finite correction below `x`. -/
theorem primeSide_eq {x : ℝ} (hx : 1 < x) (t : ℝ) :
    primeSide x t = (x : ℂ) ^ montgomeryPoleUp t *
        LSeries (fun n => ((vonMangoldt n : ℝ) : ℂ)) (montgomeryPoleUp t)
      + ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((vonMangoldt n : ℝ) : ℂ) *
          (((x / n : ℝ) : ℂ) ^ montgomeryPoleDown t - ((x / n : ℝ) : ℂ) ^ montgomeryPoleUp t) := by
  have hare : 1 < (montgomeryPoleUp t).re := by rw [montgomeryPoleUp_re]; norm_num
  have hx0 : 0 < x := by linarith
  unfold primeSide
  simp_rw [primeSideTerm_eq]
  have hfin : Summable (fun n : ℕ => if (n : ℝ) ≤ x then ((vonMangoldt n : ℝ) : ℂ) *
      (((x / n : ℝ) : ℂ) ^ montgomeryPoleDown t - ((x / n : ℝ) : ℂ) ^ montgomeryPoleUp t)
        else 0) := by
    refine summable_of_ne_finset_zero (s := Finset.Icc 1 ⌊x⌋₊) fun n hn => ?_
    rw [Finset.mem_Icc, not_and_or] at hn
    rcases hn with hn | hn
    · have : n = 0 := by omega
      subst this; simp
    · rw [if_neg]
      intro hle
      exact hn (Nat.le_floor hle)
  rw [(summable_vonMangoldt_mul_cpow hx0 hare).tsum_add hfin, cpow_mul_LSeries_vonMangoldt hx0]
  congr 1
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊) (fun n hn => ?_)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    rw [if_pos]
    exact (Nat.le_floor_iff hx0.le).mp hn.2
  · rw [Finset.mem_Icc, not_and_or] at hn
    rcases hn with hn | hn
    · have : n = 0 := by omega
      subst this; simp
    · rw [if_neg]
      intro hle
      exact hn (Nat.le_floor hle)

/-! ## The remainder blocks -/

/-- The polar remainder `x/(1−a) − x/(1−b)`. -/
noncomputable def polarRemainder (x t : ℝ) : ℂ :=
  (x : ℂ) / (1 - montgomeryPoleUp t) - (x : ℂ) / montgomeryPoleUp (-t)

/-- The `x^b` block `x^b [L(Λ,ā) − ½ψ(ā/2) − ½ψ(b/2+1) + log π − 1/(ā−1)]`, `ā = 1 − b`. -/
noncomputable def xbBlock (x t : ℝ) : ℂ :=
  (x : ℂ) ^ montgomeryPoleDown t *
    (LSeries (fun n => ((vonMangoldt n : ℝ) : ℂ)) (montgomeryPoleUp (-t))
      - Complex.digamma (montgomeryPoleUp (-t) / 2) / 2
      - Complex.digamma (montgomeryPoleDown t / 2 + 1) / 2
      + (Real.log Real.pi : ℂ) - 1 / (montgomeryPoleUp (-t) - 1))

/-- The trivial-zero block `−2 Σ_k x^{c_k}/((c_k−a)(c_k−b))`. -/
noncomputable def trivialBlock (x t : ℝ) : ℂ := -2 * ∑' k : ℕ, montgomeryTrivialTerm x t k

/-- **Montgomery's lemma in prime-side form.**  For `x > 1` and every real `t`,
`Σ_ρ 2x^ρ/((ρ−a)(ρ−b)) = primeSide + polarRemainder + xbBlock + trivialBlock`. -/
theorem tsum_montgomeryZeroTerm_eq_primeSide {x : ℝ} (hx : 1 < x) (t : ℝ) :
    ∑' q : XiZeroCopy, montgomeryZeroTerm x t q
      = primeSide x t + polarRemainder x t + xbBlock x t + trivialBlock x t := by
  have hM := montgomery_lemma_one hx t
  set a := montgomeryPoleUp t with ha
  set b := montgomeryPoleDown t with hb
  set ab := montgomeryPoleUp (-t) with hab
  have hare : 1 < a.re := by rw [ha, montgomeryPoleUp_re]; norm_num
  have habre : 1 < ab.re := by rw [hab, montgomeryPoleUp_re]; norm_num
  have hbre : b.re = -1 / 2 := by rw [hb, montgomeryPoleDown_re]
  have h1b : 1 - b = ab := one_sub_montgomeryPoleDown t
  -- the split of `ξ'/ξ` at `a` and at `ā = 1 − b`
  have hxa := logDeriv_xi_split hare
  have hxab := logDeriv_xi_split habre
  have hGa := logDeriv_Gammaℝ_digamma (by linarith : 0 < a.re)
  have hGab := logDeriv_Gammaℝ_digamma (by linarith : 0 < ab.re)
  have hζa : logDeriv riemannZeta a = -LSeries (fun n => ((vonMangoldt n : ℝ) : ℂ)) a := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hare, logDeriv_apply]; ring
  have hζab : logDeriv riemannZeta ab = -LSeries (fun n => ((vonMangoldt n : ℝ) : ℂ)) ab := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div habre, logDeriv_apply]; ring
  have hxb : logDeriv xi b = -logDeriv xi ab := by
    have := logDeriv_xi_one_sub (1 - b)
    rw [sub_sub_cancel, h1b] at this
    exact this
  -- the digamma shift sums
  have hSa := tsum_digammaShiftTerm_eq (s := a) (by linarith)
  have hSb := tsum_digammaShiftTerm_eq (s := b) (by rw [hbre]; norm_num)
  have hψa : Complex.digamma (a / 2 + 1) = Complex.digamma (a / 2) + (a / 2)⁻¹ := by
    refine Complex.digamma_apply_add_one (a / 2) fun m h => ?_
    have := congrArg Complex.re h
    simp only [Complex.div_re, Complex.neg_re, Complex.natCast_re] at this
    rw [ha, montgomeryPoleUp_re] at this
    simp at this
    linarith [Nat.cast_nonneg (α := ℝ) m]
  -- the prime side
  have hP := primeSide_eq hx t
  -- nonvanishing of the denominators
  have ha0 : a ≠ 0 := montgomeryPoleUp_ne_zero t
  have ha1 : a - 1 ≠ 0 := montgomeryPoleUp_sub_one_ne_zero t
  have h1a : 1 - a ≠ 0 := one_sub_montgomeryPoleUp_ne_zero t
  have hab0 : ab ≠ 0 := montgomeryPoleUp_ne_zero (-t)
  have hab1 : ab - 1 ≠ 0 := montgomeryPoleUp_sub_one_ne_zero (-t)
  rw [hM, h1b, hxa, hxb, hxab, hGa, hGab, hζa, hζab, hSa, hSb, hψa, primeSide_eq hx t]
  unfold polarRemainder xbBlock trivialBlock
  rw [← hab, ← ha, ← hb]
  simp only [mul_sub, Finset.sum_sub_distrib]
  set F₁ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((vonMangoldt n : ℝ) : ℂ) * ((x / n : ℝ) : ℂ) ^ a with hF₁
  set F₂ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((vonMangoldt n : ℝ) : ℂ) * ((x / n : ℝ) : ℂ) ^ b with hF₂
  set ψa := Complex.digamma (a / 2) with hψa'
  set ψab := Complex.digamma (ab / 2) with hψab'
  set ψb := Complex.digamma (b / 2 + 1) with hψb'
  set La := LSeries (fun n => ((vonMangoldt n : ℝ) : ℂ)) a with hLa
  set Lab := LSeries (fun n => ((vonMangoldt n : ℝ) : ℂ)) ab with hLab
  set Tk := ∑' k : ℕ, montgomeryTrivialTerm x t k with hTk
  set xa := (x : ℂ) ^ a with hxa'
  set xb := (x : ℂ) ^ b with hxb'
  set X := (x : ℂ) with hX
  field_simp
  ring

end RHTower
