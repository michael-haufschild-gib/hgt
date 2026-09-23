import GaloisForLFunctions.RHTower.CCMCausalPickAffineConjugacy

/-!
# The Euler–Pick transfer boundary

An even real-rooted spectral factor has a positive logarithmic-derivative Pick kernel because each
paired zero contributes the *sum* of two rank-one Gram kernels

```text
kappa_gamma (w, v) = 2 [w/(w^(2 : ℕ)+gamma^(2 : ℕ))] conj [v/(v^(2 : ℕ)+gamma^(2 : ℕ))]
                   + 2 [gamma/(w^(2 : ℕ)+gamma^(2 : ℕ))] conj [gamma/(v^(2 : ℕ)+gamma^(2 : ℕ))] ,
```

and the zero mode contributes `2r/(w conj v)`.  Since the positive cone of finite Hermitian
matrices is closed, entrywise convergence of the dephased logarithmic derivatives transports the
positivity — that is the transfer theorem of section 2.

The CCM aperture phase, however, subtracts the Cauchy kernel `2a/(w + conj v)` with `a = log λ`, so
the canonically phased kernel is not positive.  The periodic background is finite-aperture
*indefinite* — at `w = x + iπ/(2a)` its logarithmic derivative is real and negative — but decays
like `2a/(e^{2aσ} − 1)` on `Re w ≥ σ`, hence is cofinally invisible.  Finally the relative
determinant `sum_j c_j/(d_j − z)` is Herglotz exactly when all `c_j ≥ 0`.
-/

open Complex Matrix Filter Topology

open scoped ComplexOrder

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The paired-zero kernel -/

/-- The paired-zero kernel `(15)`. -/
def pairedZeroKernel (γ : ℝ) (w v : ℂ) : ℂ :=
  2 * (w / (w ^ (2 : ℕ) + (γ : ℂ) ^ (2 : ℕ))) * (starRingEnd ℂ) (v / (v ^ (2 : ℕ) + (γ : ℂ) ^ (2 : ℕ)))
    + 2 * ((γ : ℂ) / (w ^ (2 : ℕ) + (γ : ℂ) ^ (2 : ℕ))) * (starRingEnd ℂ) ((γ : ℂ) / (v ^ (2 : ℕ) + (γ : ℂ) ^ (2 : ℕ)))

/-- **Equation (6).**  The logarithmic-derivative contribution of one paired zero is exactly the
sum of two rank-one Gram kernels. -/
theorem pairedZeroKernel_eq {γ : ℝ} {w v : ℂ}
    (hw : w ^ (2 : ℕ) + (γ : ℂ) ^ (2 : ℕ) ≠ 0)
    (hv : (starRingEnd ℂ) v ^ (2 : ℕ) + (γ : ℂ) ^ (2 : ℕ) ≠ 0)
    (hsum : w + (starRingEnd ℂ) v ≠ 0) :
    (1 / (w + (starRingEnd ℂ) v))
        * (2 * w / (w ^ (2 : ℕ) + (γ : ℂ) ^ (2 : ℕ))
          + 2 * (starRingEnd ℂ) v / ((starRingEnd ℂ) v ^ (2 : ℕ) + (γ : ℂ) ^ (2 : ℕ)))
      = pairedZeroKernel γ w v := by
  unfold pairedZeroKernel
  have hcv : (starRingEnd ℂ) (v / (v ^ (2 : ℕ) + (γ : ℂ) ^ (2 : ℕ)))
      = (starRingEnd ℂ) v / ((starRingEnd ℂ) v ^ (2 : ℕ) + (γ : ℂ) ^ (2 : ℕ)) := by
    rw [map_div₀, map_add, map_pow, map_pow, Complex.conj_ofReal]
  have hcg : (starRingEnd ℂ) ((γ : ℂ) / (v ^ (2 : ℕ) + (γ : ℂ) ^ (2 : ℕ)))
      = (γ : ℂ) / ((starRingEnd ℂ) v ^ (2 : ℕ) + (γ : ℂ) ^ (2 : ℕ)) := by
    rw [map_div₀, map_add, map_pow, map_pow, Complex.conj_ofReal]
  rw [hcv, hcg]
  field_simp
  ring

/-! ## Closure of the positive cone -/

/-- **Section 2, transfer step.**  The positive cone of finite Hermitian matrices is closed under
entrywise limits, so entrywise convergence of positive kernels gives a positive limit kernel. -/
theorem posSemidef_of_tendsto_entrywise {n : ℕ} {M : ℕ → Matrix (Fin n) (Fin n) ℂ}
    {L : Matrix (Fin n) (Fin n) ℂ} (hM : ∀ k, (M k).PosSemidef)
    (hlim : ∀ i j, Tendsto (fun k => M k i j) atTop (nhds (L i j))) :
    L.PosSemidef := by
  constructor
  · ext i j
    have h1 : Tendsto (fun k => (starRingEnd ℂ) (M k j i)) atTop
        (nhds ((starRingEnd ℂ) (L j i))) :=
      (Complex.continuous_conj.tendsto _).comp (hlim j i)
    have h2 : ∀ k, (starRingEnd ℂ) (M k j i) = M k i j := by
      intro k
      have := (hM k).isHermitian
      have hij := congrFun (congrFun this i) j
      simpa [Matrix.conjTranspose_apply] using hij
    have h3 : Tendsto (fun k => M k i j) atTop (nhds ((starRingEnd ℂ) (L j i))) := by
      refine h1.congr fun k => h2 k
    exact tendsto_nhds_unique h3 (hlim i j)
  · intro α
    have hform : ∀ (N : Matrix (Fin n) (Fin n) ℂ),
        (α.sum fun i xi => α.sum fun j xj => star xi * N i j * xj)
          = ∑ i, ∑ j, star (α i) * N i j * α j := by
      intro N
      rw [Finsupp.sum_fintype _ _ (by intro i; simp)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finsupp.sum_fintype _ _ (by intro j; simp)]
    have hconv : Tendsto (fun k => ∑ i, ∑ j, star (α i) * M k i j * α j) atTop
        (nhds (∑ i, ∑ j, star (α i) * L i j * α j)) := by
      refine tendsto_finsetSum _ fun i _ => ?_
      refine tendsto_finsetSum _ fun j _ => ?_
      exact ((hlim i j).const_mul _).mul_const _
    have hnn : ∀ k, (0 : ℝ) ≤ (∑ i, ∑ j, star (α i) * M k i j * α j).re := by
      intro k
      have h := (hM k).2 α
      rw [hform (M k)] at h
      simpa using (Complex.le_def.mp h).1
    have hzero : ∀ k, (∑ i, ∑ j, star (α i) * M k i j * α j).im = 0 := by
      intro k
      have h := (hM k).2 α
      rw [hform (M k)] at h
      simpa using ((Complex.le_def.mp h).2).symm
    have hre : Tendsto (fun k => (∑ i, ∑ j, star (α i) * M k i j * α j).re) atTop
        (nhds ((∑ i, ∑ j, star (α i) * L i j * α j).re)) :=
      (Complex.continuous_re.tendsto _).comp hconv
    have him : Tendsto (fun k => (∑ i, ∑ j, star (α i) * M k i j * α j).im) atTop
        (nhds ((∑ i, ∑ j, star (α i) * L i j * α j).im)) :=
      (Complex.continuous_im.tendsto _).comp hconv
    have hreL := le_of_tendsto_of_tendsto tendsto_const_nhds hre
      (Filter.Eventually.of_forall hnn)
    have himL : (∑ i, ∑ j, star (α i) * L i j * α j).im = 0 :=
      tendsto_nhds_unique (him.congr fun k => hzero k) tendsto_const_nhds
    rw [hform L, Complex.le_def]
    exact ⟨by simpa using hreL, by simpa using himL.symm⟩

/-! ## The aperture phase -/

/-- The Cauchy kernel of the right half-plane. -/
def rightCauchyKernel (w v : ℂ) : ℂ := 1 / (w + (starRingEnd ℂ) v)

/-- **Equation (14).**  The canonically phased determinant kernel is the spectral-factor kernel
minus `2a` times the positive Cauchy kernel. -/
theorem aperturePhaseDefect (a : ℝ) (LG : ℂ → ℂ) (w v : ℂ) :
    ((-(a : ℂ) + LG w) + (starRingEnd ℂ) (-(a : ℂ) + LG v)) / (w + (starRingEnd ℂ) v)
      = (LG w + (starRingEnd ℂ) (LG v)) / (w + (starRingEnd ℂ) v)
        - 2 * (a : ℂ) * rightCauchyKernel w v := by
  unfold rightCauchyKernel
  rw [map_add, map_neg, Complex.conj_ofReal]
  ring

/-! ## The periodic background -/

/-- The periodic scaling background `(14a)`, in the `w` coordinate. -/
def periodicBackground (a : ℝ) (w : ℂ) : ℂ := 1 - Complex.exp (-(2 * (a : ℂ) * w))

/-- Its logarithmic derivative `(14b)`. -/
def periodicBackgroundLogDeriv (a : ℝ) (w : ℂ) : ℂ :=
  2 * (a : ℂ) / (Complex.exp (2 * (a : ℂ) * w) - 1)

/-- **Equation (14b).**  The background logarithmic derivative in closed form. -/
theorem hasDerivAt_periodicBackground (a : ℝ) (w : ℂ) :
    HasDerivAt (periodicBackground a)
      (2 * (a : ℂ) * Complex.exp (-(2 * (a : ℂ) * w))) w := by
  have hlin : HasDerivAt (fun u : ℂ => -(2 * (a : ℂ) * u)) (-(2 * (a : ℂ))) w := by
    have h : HasDerivAt (fun u : ℂ => 2 * (a : ℂ) * u) (2 * (a : ℂ)) w := by
      simpa using (hasDerivAt_id w).const_mul (2 * (a : ℂ))
    exact h.fun_neg
  have hexp := hlin.cexp
  have hsub := (hasDerivAt_const w (1 : ℂ)).sub hexp
  refine hsub.congr_deriv ?_
  ring

theorem periodicBackgroundLogDeriv_eq {a : ℝ} {w : ℂ}
    (h : Complex.exp (2 * (a : ℂ) * w) - 1 ≠ 0) :
    2 * (a : ℂ) * Complex.exp (-(2 * (a : ℂ) * w)) / periodicBackground a w
      = periodicBackgroundLogDeriv a w := by
  unfold periodicBackground periodicBackgroundLogDeriv
  have hexp : Complex.exp (-(2 * (a : ℂ) * w)) * Complex.exp (2 * (a : ℂ) * w) = 1 := by
    rw [← Complex.exp_add]
    simp
  have hne : Complex.exp (-(2 * (a : ℂ) * w)) ≠ 0 := Complex.exp_ne_zero _
  have h1 : 1 - Complex.exp (-(2 * (a : ℂ) * w))
      = Complex.exp (-(2 * (a : ℂ) * w)) * (Complex.exp (2 * (a : ℂ) * w) - 1) := by
    rw [mul_sub, hexp]
    ring
  rw [h1]
  field_simp

/-- **Equation (14c).**  The background logarithmic derivative decays exponentially on every
right half-plane. -/
theorem norm_periodicBackgroundLogDeriv_le {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) {w : ℂ}
    (hw : σ ≤ w.re) :
    ‖periodicBackgroundLogDeriv a w‖ ≤ 2 * a / (Real.exp (2 * a * σ) - 1) := by
  have hexpre : (2 * (a : ℂ) * w).re = 2 * a * w.re := by
    simp [Complex.mul_re]
  have hnorm : ‖Complex.exp (2 * (a : ℂ) * w)‖ = Real.exp (2 * a * w.re) := by
    rw [Complex.norm_exp, hexpre]
  have hge : Real.exp (2 * a * σ) ≤ ‖Complex.exp (2 * (a : ℂ) * w)‖ := by
    rw [hnorm]
    exact Real.exp_le_exp.2 (by nlinarith)
  have hone : (1 : ℝ) < Real.exp (2 * a * σ) := by
    rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_lt_exp.2 (by positivity)
  have hden : Real.exp (2 * a * σ) - 1 ≤ ‖Complex.exp (2 * (a : ℂ) * w) - 1‖ := by
    have h := norm_sub_norm_le (Complex.exp (2 * (a : ℂ) * w)) (1 : ℂ)
    rw [norm_one] at h
    linarith [hge, h]
  have hdenpos : (0 : ℝ) < Real.exp (2 * a * σ) - 1 := by linarith
  unfold periodicBackgroundLogDeriv
  rw [norm_div]
  have hnum : ‖2 * (a : ℂ)‖ = 2 * a := by
    rw [show (2 : ℂ) * (a : ℂ) = ((2 * a : ℝ) : ℂ) from by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
  rw [hnum]
  exact div_le_div_of_nonneg_left (by linarith) hdenpos hden

/-- **Finite-aperture indefiniteness.**  On the horizontal line `Im w = π/(2a)` the background
logarithmic derivative is real and strictly negative. -/
theorem periodicBackgroundLogDeriv_neg {a x : ℝ} (ha : 0 < a) :
    periodicBackgroundLogDeriv a (x + Complex.I * ((Real.pi / (2 * a) : ℝ) : ℂ))
      = ((2 * a / (-(Real.exp (2 * a * x)) - 1) : ℝ) : ℂ) := by
  have ha0 : (a : ℝ) ≠ 0 := ne_of_gt ha
  have ha0C : ((a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha0
  have harg : 2 * (a : ℂ) * ((x : ℂ) + Complex.I * ((Real.pi / (2 * a) : ℝ) : ℂ))
      = ((2 * a * x : ℝ) : ℂ) + ((Real.pi : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp
  have hpi : Complex.exp (((Real.pi : ℝ) : ℂ) * Complex.I) = -1 := by
    rw [Complex.exp_mul_I]
    simp
  have hE : Complex.exp (((2 * a * x : ℝ) : ℂ)) = ((Real.exp (2 * a * x) : ℝ) : ℂ) :=
    (Complex.ofReal_exp _).symm
  unfold periodicBackgroundLogDeriv
  rw [harg, Complex.exp_add, hpi, hE]
  push_cast
  congr 1
  ring

/-! ## The relative determinant and the Herglotz criterion -/

/-- The relative determinant `(23)`. -/
def relativeDeterminant {m : ℕ} (c d : Fin m → ℝ) (z : ℂ) : ℂ :=
  ∑ j, (c j : ℂ) / ((d j : ℂ) - z)

/-- **Equation (24).**  The imaginary part of the relative determinant. -/
theorem im_relativeDeterminant {m : ℕ} (c d : Fin m → ℝ) (z : ℂ) :
    (relativeDeterminant c d z).im
      = ∑ j, c j * z.im / ((d j - z.re) ^ (2 : ℕ) + z.im ^ (2 : ℕ)) := by
  unfold relativeDeterminant
  rw [Complex.im_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hnsq : Complex.normSq ((d j : ℂ) - z) = (d j - z.re) ^ (2 : ℕ) + z.im ^ (2 : ℕ) := by
    simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  rw [div_eq_mul_inv, Complex.mul_im, Complex.inv_im, Complex.inv_re, hnsq]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.ofReal_im]
  ring

/-- **The relative Herglotz criterion, sufficiency.**  Nonnegative coefficients make the relative
determinant map the upper half-plane to its closure. -/
theorem im_relativeDeterminant_nonneg {m : ℕ} {c d : Fin m → ℝ} (hc : ∀ j, 0 ≤ c j)
    {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (relativeDeterminant c d z).im := by
  rw [im_relativeDeterminant c d z]
  refine Finset.sum_nonneg fun j _ => ?_
  have hpos : (0 : ℝ) < (d j - z.re) ^ (2 : ℕ) + z.im ^ (2 : ℕ) := by positivity
  exact div_nonneg (mul_nonneg (hc j) hz.le) hpos.le

end GaloisForLFunctions.RHTower

end
