import GaloisForLFunctions.RHTower.BarnesMellinExpansion

/-!
# The Mellin integrand at a negative integer

For a canonical product of genus `g ≥ 1` the initial contour lies to the left of `-g`, so the
rightward shift crosses the negative integers `-g, …, -1` before reaching `0`.  The reflection
kernel has the same simple pole with residue `(-1)^k` at `w = -k` as at `w = k`, and the remaining
factors of

```text
F_m(w) = (-w)^m x^{-w} ζ(-sw) (-π/sin πw)
```

are analytic there as soon as `-k` is not the pullback `-1/s` of the pole of zeta.  The crossed
residue is therefore `k^m x^{k} ζ(sk) (-(-1)^k)`, which is the term `(-1)^k ζ(sk) x^{k}` of the
Barnes expansion.
-/

open Complex Filter Set MeasureTheory

namespace RHTower

noncomputable section

/-- **The weighted integrand has a simple pole at every negative integer** at which the zeta factor
is regular. -/
theorem barnesIntegrandPow_simplePole_at_negNat {s x : ℝ} (hx : 0 < x) (m k : ℕ)
    (hζ : -(s : ℂ) * (-(k : ℂ)) ≠ 1) :
    (fun w : ℂ => barnesIntegrandPow s x m w
        - ((-(-(k : ℂ))) ^ m * (((x : ℝ) : ℂ) ^ (-(-(k : ℂ)))
            * riemannZeta (-(s : ℂ) * (-(k : ℂ)))) * (-(-1) ^ k))
          / (w - (-(k : ℂ))))
      =O[nhdsWithin (-(k : ℂ)) {(-(k : ℂ))}ᶜ] (fun _ : ℂ => (1 : ℂ)) := by
  have hg : AnalyticAt ℂ (fun w : ℂ =>
      (-w) ^ m * (((x : ℝ) : ℂ) ^ (-w) * riemannZeta (-(s : ℂ) * w))) (-(k : ℂ)) :=
    (analyticAt_neg_pow m _).mul
      ((analyticAt_const_cpow_neg hx _).mul (analyticAt_zetaComp hζ))
  have hh : (fun w : ℂ => -((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * w))
      - (-(-1) ^ k) / (w - (-(k : ℂ))))
      =O[nhdsWithin (-(k : ℂ)) {(-(k : ℂ))}ᶜ] (fun _ : ℂ => (1 : ℂ)) := by
    have hbase := GaloisForLFunctions.HTGeometry.isBigO_inv_sin_sub_inv_at_neg_nat k
    refine hbase.neg_left.congr' ?_ Filter.EventuallyEq.rfl
    refine Filter.Eventually.of_forall fun w => ?_
    simp only [div_eq_mul_inv]
    ring
  have hmain := GaloisForLFunctions.HTGeometry.isBigO_analytic_mul_simplePole hg hh
  refine hmain.congr' (Filter.Eventually.of_forall fun w => ?_) Filter.EventuallyEq.rfl
  simp only [barnesIntegrandPow, barnesIntegrand]
  ring

/-- **Crossing a negative integer.**  If the strip `[σ, σ']` meets the integers only in `-k` and
stays to the right of the pullback of the zeta pole, the shift picks up the kernel residue at
`-k`. -/
theorem verticalIntegral'_shift_negNat {s x : ℝ} (hs : 0 < s) (hx : 0 < x) (m k : ℕ)
    {σ σ' : ℝ} (hσ : σ < -(k : ℝ)) (hσ' : -(k : ℝ) < σ')
    (hlow : -(k : ℝ) - 1 < σ) (hhigh : σ' < -(k : ℝ) + 1)
    (hzeta : -(1 / s) < σ)
    (hσsin : Real.sin (Real.pi * σ) ≠ 0) (hσ'sin : Real.sin (Real.pi * σ') ≠ 0)
    (hσz : -(s : ℝ) * σ ≠ 1) (hσ'z : -(s : ℝ) * σ' ≠ 1) :
    VerticalIntegral' (barnesIntegrandPow s x m) σ'
        - VerticalIntegral' (barnesIntegrandPow s x m) σ
      = (-(-(k : ℂ))) ^ m * (((x : ℝ) : ℂ) ^ (-(-(k : ℂ)))
          * riemannZeta (-(s : ℂ) * (-(k : ℂ)))) * (-(-1) ^ k) := by
  have hpre : ((-(k : ℂ))).re = -(k : ℝ) := by simp
  have hζ : -(s : ℂ) * (-(k : ℂ)) ≠ 1 := by
    intro hcon
    have hre := congrArg Complex.re hcon
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im, Complex.one_re] at hre
    have hsk : s * (k : ℝ) = 1 := by linarith
    have hk : -(1 / s) = -(k : ℝ) := by
      field_simp
      linarith
    rw [hk] at hzeta
    linarith
  have hreg : ∀ w : ℂ, w.re ∈ Set.Icc σ σ' → w ≠ (-(k : ℂ)) →
      -((s : ℝ) : ℂ) * w ≠ 1 ∧ Complex.sin ((Real.pi : ℂ) * w) ≠ 0 := by
    intro w hw hne
    obtain ⟨hwl, hwr⟩ := hw
    refine barnes_regular_of_ne (fun hcon => ?_) (fun n hn => ?_)
    · have hre := re_eq_of_mul_eq_one hs hcon
      rw [hre] at hwl
      linarith
    · have hre : w.re = (n : ℝ) := by rw [hn]; simp
      rw [hre] at hwl hwr
      have h1 : -(k : ℝ) - 1 < (n : ℝ) := lt_of_lt_of_le hlow hwl
      have h2 : (n : ℝ) < -(k : ℝ) + 1 := lt_of_le_of_lt hwr hhigh
      have h1' : ((-(k : ℤ) : ℤ) : ℝ) - 1 < ((n : ℤ) : ℝ) := by push_cast; linarith
      have h2' : ((n : ℤ) : ℝ) < ((-(k : ℤ) : ℤ) : ℝ) + 1 := by push_cast; linarith
      have hz1 : (-(k : ℤ)) - 1 < n := by exact_mod_cast h1'
      have hz2 : n < (-(k : ℤ)) + 1 := by exact_mod_cast h2'
      have hnk : n = -(k : ℤ) := by omega
      exact hne (by rw [hn, hnk]; push_cast; ring)
  refine verticalIntegral'_barnes_shift hs hx m (by rw [hpre]; exact hσ) (by rw [hpre]; exact hσ')
    hreg ?_ hσsin hσz hσ'sin hσ'z
  exact barnesIntegrandPow_simplePole_at_negNat hx m k hζ

end

end RHTower
