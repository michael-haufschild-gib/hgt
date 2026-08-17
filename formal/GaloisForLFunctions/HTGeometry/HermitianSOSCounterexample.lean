import GaloisForLFunctions.HTGeometry.HermitianSOSUnfolding

/-!
# Fejér–Riesz fails for mixed exponents

The two model nonnegative exponential polynomials with a conjugate pair do factor:

`2 e^{βt}(1 - cos γ t) = |{-i}(e^{(β+iγ)t/2} - e^{(β-iγ)t/2})|²`,
`cosh (a t) - cos (b t) = 2 |sinh (t(a+ib)/2)|²`.

Both are Hermitian squares, and the reason is visible in the unfolding: the first unfolds to
`2 e^{βt}(1 - cos γ u)` and the second to `cosh(at) - cos(bu)`, both nonnegative on the whole plane.

That is not a general phenomenon.  The function

`f(t) = 2λ cosh (κ(t - π/γ)) - 2 cos (γ t)`,  `0 < λ < 1`, `κ` large,

is nonnegative on ℝ — the dip of the first term is placed exactly halfway between two peaks of the
cosine — while its unfolding `2λ cosh(κ(t - π/γ)) - 2 cos(γ u)` is negative at `(t,u) = (π/γ, 0)`.
By the unfolding obstruction it is not a sum of Hermitian squares.

So the sum-of-Hermitian-squares cone is strictly smaller than the nonnegative cone: it is the cone
of exponential polynomials that stay nonnegative when growth and phase are decoupled.
-/

open Finset Real

namespace GaloisForLFunctions.HTGeometry

/-! ## A nonnegative exponential polynomial that is not a Hermitian square sum -/

private theorem exists_near_peak {θ : ℝ} (h : 0 < Real.cos θ) :
    ∃ k : ℤ, |θ - 2 * π * k| < π / 2 := by
  refine ⟨round (θ / (2 * π)), ?_⟩
  set k : ℤ := round (θ / (2 * π)) with hk
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have hper : Real.cos (θ - 2 * π * k) = Real.cos θ := by
    rw [show θ - 2 * π * k = θ - (k : ℝ) * (2 * π) from by ring]
    exact Real.cos_sub_int_mul_two_pi θ k
  have hbound : |θ - 2 * π * k| ≤ π := by
    have hr := abs_sub_round (θ / (2 * π))
    have hrw : θ - 2 * π * (k : ℝ) = 2 * π * (θ / (2 * π) - (k : ℝ)) := by
      field_simp
    have habs : |θ - 2 * π * (k : ℝ)| = 2 * π * |θ / (2 * π) - (k : ℝ)| := by
      rw [hrw, abs_mul, abs_of_pos hpi]
    rw [habs]
    nlinarith [hr, hpi.le, abs_nonneg (θ / (2 * π) - (k : ℝ))]
  by_contra hcon
  push Not at hcon
  have hnp : Real.cos (θ - 2 * π * k) ≤ 0 := by
    rcases le_total 0 (θ - 2 * π * k) with hs | hs
    · rw [abs_of_nonneg hs] at hcon hbound
      exact Real.cos_nonpos_of_pi_div_two_le_of_le hcon (by linarith [Real.pi_pos])
    · rw [abs_of_nonpos hs] at hcon hbound
      rw [← Real.cos_neg]
      exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith [Real.pi_pos])
  rw [hper] at hnp
  linarith

/-- **The witness is nonnegative.**  Placing the dip of `2λ cosh` halfway between two peaks of the
cosine, and making the dip narrow enough, keeps the difference nonnegative. -/
theorem counterexample_nonneg {lam0 gam kap : ℝ} (hl0 : 0 < lam0) (hg : 0 < gam) (hk : 0 < kap)
    (hbig : 1 ≤ lam0 * Real.cosh (kap * π / (2 * gam))) (t : ℝ) :
    0 ≤ 2 * lam0 * Real.cosh (kap * (t - π / gam)) - 2 * Real.cos (gam * t) := by
  have hcoshpos : (0 : ℝ) < Real.cosh (kap * (t - π / gam)) :=
    lt_of_lt_of_le zero_lt_one (Real.one_le_cosh _)
  have hpi : (0 : ℝ) < π := Real.pi_pos
  rcases le_total (Real.cos (gam * t)) 0 with hcos | hcos
  · nlinarith
  rcases eq_or_lt_of_le hcos with heq | hpos
  · nlinarith
  obtain ⟨k, hk'⟩ := exists_near_peak hpos
  -- the time is far from the dip
  have hodd : (1 : ℝ) ≤ |2 * (k : ℝ) - 1| := by
    have hne : (2 * k - 1 : ℤ) ≠ 0 := by omega
    have hz : (1 : ℤ) ≤ |2 * k - 1| := Int.one_le_abs hne
    have hcast : ((|2 * k - 1| : ℤ) : ℝ) = |2 * (k : ℝ) - 1| := by
      rw [Int.cast_abs]
      congr 1
      push_cast
      ring
    have : (1 : ℝ) ≤ ((|2 * k - 1| : ℤ) : ℝ) := by exact_mod_cast hz
    linarith [hcast ▸ this]
  have hpeak : π ≤ |2 * π * (k : ℝ) - π| := by
    have h1 : |2 * π * (k : ℝ) - π| = π * |2 * (k : ℝ) - 1| := by
      rw [show 2 * π * (k : ℝ) - π = π * (2 * (k : ℝ) - 1) from by ring, abs_mul,
        abs_of_pos hpi]
    rw [h1]
    nlinarith
  have htri : |2 * π * (k : ℝ) - π|
      ≤ |2 * π * (k : ℝ) - gam * t| + |gam * t - π| := abs_sub_le _ _ _
  have hsym : |2 * π * (k : ℝ) - gam * t| = |gam * t - 2 * π * (k : ℝ)| := abs_sub_comm _ _
  have hkey : π / 2 < |gam * t - π| := by
    rw [hsym] at htri
    linarith
  have hfar : π / (2 * gam) < |t - π / gam| := by
    have hrw : gam * t - π = gam * (t - π / gam) := by field_simp
    rw [hrw, abs_mul, abs_of_pos hg] at hkey
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * gam)]
    nlinarith
  -- so the hyperbolic cosine is at least its value at the edge of the dip
  have hmono : Real.cosh (kap * π / (2 * gam)) ≤ Real.cosh (kap * (t - π / gam)) := by
    refine Real.cosh_le_cosh.mpr ?_
    rw [abs_mul, abs_of_pos hk]
    have h1 : |kap * π / (2 * gam)| = kap * (π / (2 * gam)) := by
      rw [abs_of_pos (by positivity)]
      ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left hfar.le hk.le
  have hcos1 : Real.cos (gam * t) ≤ 1 := Real.cos_le_one _
  have hstep : 2 * lam0 * Real.cosh (kap * π / (2 * gam))
      ≤ 2 * lam0 * Real.cosh (kap * (t - π / gam)) := by nlinarith
  linarith

/-- Such a `κ` exists for every `λ ∈ (0,1)` and every `γ > 0`. -/
theorem exists_kappa {lam0 gam : ℝ} (hl0 : 0 < lam0) (hg : 0 < gam) :
    ∃ kap : ℝ, 0 < kap ∧ 1 ≤ lam0 * Real.cosh (kap * π / (2 * gam)) := by
  have hne : lam0 ≠ 0 := ne_of_gt hl0
  have hpi : (0 : ℝ) < π := Real.pi_pos
  refine ⟨4 * gam / (lam0 * π), by positivity, ?_⟩
  have harg : 4 * gam / (lam0 * π) * π / (2 * gam) = 2 / lam0 := by
    field_simp
    ring
  rw [harg]
  have hc : 1 / lam0 ≤ Real.cosh (2 / lam0) := by
    rw [Real.cosh_eq]
    have h1 := Real.add_one_le_exp (2 / lam0)
    have h2 : (0 : ℝ) < Real.exp (-(2 / lam0)) := Real.exp_pos _
    have h3 : 2 / lam0 / 2 = 1 / lam0 := by field_simp
    linarith [h3]
  calc (1 : ℝ) = lam0 * (1 / lam0) := by field_simp
    _ ≤ lam0 * Real.cosh (2 / lam0) := mul_le_mul_of_nonneg_left hc hl0.le

/-! ## The exponential-polynomial data -/

/-- Exponents of the witness: `±κ` and `±iγ`. -/
noncomputable def cexLam (gam kap : ℝ) : Fin 4 → ℂ :=
  ![(kap : ℂ), -(kap : ℂ), Complex.I * (gam : ℂ), -(Complex.I * (gam : ℂ))]

/-- Coefficients of the witness. -/
noncomputable def cexW (lam0 gam kap : ℝ) : Fin 4 → ℂ :=
  ![(lam0 : ℂ) * Complex.exp (-((kap : ℂ) * ((π / gam : ℝ) : ℂ))),
    (lam0 : ℂ) * Complex.exp ((kap : ℂ) * ((π / gam : ℝ) : ℂ)), -1, -1]

private theorem unfoldChar_ofReal (r t u : ℝ) :
    unfoldChar ((r : ℂ)) t u = Complex.exp (((r * t : ℝ) : ℂ)) := by
  rw [unfoldChar]
  norm_num

private theorem unfoldChar_imagAxis (s t u : ℝ) :
    unfoldChar (Complex.I * (s : ℂ)) t u = Complex.exp (Complex.I * ((s * u : ℝ) : ℂ)) := by
  rw [unfoldChar]
  norm_num

/-- **The unfolding of the witness**: growth in `t`, phase in `u`. -/
theorem cex_unfold (lam0 gam kap : ℝ) (t u : ℝ) :
    unfoldSum (cexW lam0 gam kap) (cexLam gam kap) t u
      = ((2 * lam0 * Real.cosh (kap * (t - π / gam)) - 2 * Real.cos (gam * u) : ℝ) : ℂ) := by
  have e1 : unfoldChar (-(kap : ℂ)) t u = Complex.exp (((-kap * t : ℝ) : ℂ)) := by
    rw [show (-(kap : ℂ)) = (((-kap : ℝ)) : ℂ) from by push_cast; ring, unfoldChar_ofReal]
  have e3 : unfoldChar (-(Complex.I * (gam : ℂ))) t u
      = Complex.exp (Complex.I * (((-gam) * u : ℝ) : ℂ)) := by
    rw [show (-(Complex.I * (gam : ℂ))) = Complex.I * (((-gam : ℝ)) : ℂ) from by push_cast; ring,
      unfoldChar_imagAxis]
  rw [unfoldSum, Fin.sum_univ_four, cexW, cexLam]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [unfoldChar_ofReal, e1, unfoldChar_imagAxis, e3]
  have hA : (lam0 : ℂ) * Complex.exp (-((kap : ℂ) * ((π / gam : ℝ) : ℂ)))
      * Complex.exp (((kap * t : ℝ) : ℂ))
      = (lam0 : ℂ) * Complex.exp (((kap * (t - π / gam) : ℝ) : ℂ)) := by
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hB : (lam0 : ℂ) * Complex.exp ((kap : ℂ) * ((π / gam : ℝ) : ℂ))
      * Complex.exp (((-kap * t : ℝ) : ℂ))
      = (lam0 : ℂ) * Complex.exp (((-(kap * (t - π / gam)) : ℝ) : ℂ)) := by
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hC : (-1 : ℂ) * Complex.exp (Complex.I * ((gam * u : ℝ) : ℂ))
      + (-1 : ℂ) * Complex.exp (Complex.I * (((-gam) * u : ℝ) : ℂ))
      = -(2 * ((Real.cos (gam * u) : ℝ) : ℂ)) := by
    have hz : Complex.I * ((gam * u : ℝ) : ℂ) = ((gam * u : ℝ) : ℂ) * Complex.I := by ring
    have hz2 : Complex.I * (((-gam) * u : ℝ) : ℂ) = -((gam * u : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [hz, hz2, Complex.ofReal_cos]
    have h2 := Complex.two_cos ((gam * u : ℝ) : ℂ)
    linear_combination h2
  have hRHS : ((2 * lam0 * Real.cosh (kap * (t - π / gam)) - 2 * Real.cos (gam * u) : ℝ) : ℂ)
      = (lam0 : ℂ) * Complex.exp (((kap * (t - π / gam) : ℝ) : ℂ))
        + (lam0 : ℂ) * Complex.exp (((-(kap * (t - π / gam)) : ℝ) : ℂ))
        - 2 * ((Real.cos (gam * u) : ℝ) : ℂ) := by
    rw [Real.cosh_eq]
    push_cast
    ring
  rw [hRHS]
  linear_combination hA + hB + hC

theorem cex_eval (lam0 gam kap : ℝ) (t : ℝ) :
    ∑ i, cexW lam0 gam kap i * Complex.exp (cexLam gam kap i * t)
      = ((2 * lam0 * Real.cosh (kap * (t - π / gam)) - 2 * Real.cos (gam * t) : ℝ) : ℂ) := by
  rw [← unfoldSum_diag, cex_unfold]

/-! ## The witness is not a sum of Hermitian squares -/

/-- **Fejér–Riesz fails.**  For `0 < λ < 1` and `κ` large the exponential polynomial
`2λ cosh(κ(t - π/γ)) - 2 cos(γ t)` is nonnegative on `ℝ` yet is not a sum of Hermitian squares. -/
theorem not_isHermitianSOS_of_lt_one {lam0 gam kap : ℝ} (hl1 : lam0 < 1) :
    ¬ ∃ (L m : ℕ) (v : Fin L → Fin m → ℂ) (μ : Fin m → ℂ),
        IsHermitianSOS (cexW lam0 gam kap) (cexLam gam kap) v μ := by
  rintro ⟨L, m, v, μ, hSOS⟩
  have hnn := unfoldSum_nonneg_of_isHermitianSOS _ _ v μ hSOS (π / gam) 0
  rw [cex_unfold] at hnn
  simp only [sub_self, mul_zero, Real.cosh_zero, Real.cos_zero, Complex.ofReal_re] at hnn
  linarith

end GaloisForLFunctions.HTGeometry
