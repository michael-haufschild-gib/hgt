import GaloisForLFunctions.RHTower.GaussRelativePower

/-!
# The quasi-inner block commutes with pointwise conjugation

Pointwise complex conjugation is an antiunitary involution of `L²(ℝ/ℤ)` that sends `e_j` to
`e_(-j)`.  Every multiplication operator with a *real* symbol commutes with it, and so does the
Gauss diagonal, because `conj d_(-j) = d_j`.  Hence `G` commutes with it, and the diagonal of every
power of `G` at a negative frequency is the complex conjugate of the diagonal at the positive one.

That is exactly what is needed to run the logarithmic mean over the two-sided lattice: the relative
estimate proved at `+n` transfers verbatim to `-n`.
-/

namespace RHTower

open Filter Topology MeasureTheory GaloisForLFunctions
open scoped ENNReal NNReal

noncomputable section

variable {m : ℕ}

/-- Conjugation reflects the Fourier index. -/
theorem fourierCoeff_star (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) (j : ℤ) :
    fourierCoeff ((star u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
        AddCircle (1 : ℝ) → ℂ) j
      = starRingEnd ℂ (fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) (-j)) := by
  rw [fourierCoeff, fourierCoeff, ← integral_conj]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_star u] with z hz
  rw [hz]
  simp only [Pi.star_apply, RCLike.star_def, smul_eq_mul, map_mul, neg_neg]
  rw [fourier_neg]

/-- Two `L²` functions with the same Fourier coefficients agree. -/
theorem lp_ext_fourierCoeff {u v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))}
    (h : ∀ j : ℤ, fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j
      = fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) j) : u = v := by
  refine (fourierBasis (T := (1 : ℝ))).repr.injective ?_
  refine lp.ext (funext fun j => ?_)
  rw [fourierBasis_repr, fourierBasis_repr]
  exact h j

theorem fourierCoeff_fourierLp (j l : ℤ) :
    fourierCoeff ((fourierLp 2 j : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
        AddCircle (1 : ℝ) → ℂ) l = if l = j then 1 else 0 := by
  rw [← fourierBasis_repr]
  have hb : (fourierLp 2 j : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))
      = (fourierBasis (T := (1 : ℝ))) j := by rw [coe_fourierBasis]
  rw [hb, HilbertBasis.repr_self]
  simp only [lp.single_apply, Pi.single_apply]

/-- Conjugation reflects the exponential monomials. -/
theorem star_fourierLp (j : ℤ) :
    star (fourierLp 2 j : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))
      = fourierLp 2 (-j) := by
  refine lp_ext_fourierCoeff fun l => ?_
  rw [fourierCoeff_star, fourierCoeff_fourierLp, fourierCoeff_fourierLp]
  split_ifs with h1 h2 h2
  · simp
  · exact absurd (by omega) h2
  · exact absurd (by omega) h1
  · simp

/-- Conjugation is antiunitary. -/
theorem inner_star_star (u v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    (inner ℂ (star u) (star v) : ℂ) = starRingEnd ℂ (inner ℂ u v) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def, ← integral_conj]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_star u, Lp.coeFn_star v] with z hu hv
  rw [hu, hv]
  simp only [Pi.star_apply, RCLike.star_def, RCLike.inner_apply', map_mul, Complex.conj_conj]

/-! ## The blocks commute with conjugation -/

theorem star_lpBoundedMulCLM_real {sym : AddCircle (1 : ℝ) → ℂ} (hsym : Measurable sym)
    {Cb : ℝ} (hCb0 : 0 ≤ Cb) (hCb : ∀ x, ‖sym x‖ ≤ Cb)
    (hreal : ∀ x, starRingEnd ℂ (sym x) = sym x)
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    star (MeasureTheory.lpBoundedMulCLM hsym hCb0 hCb u)
      = MeasureTheory.lpBoundedMulCLM hsym hCb0 hCb (star u) := by
  refine Lp.ext_iff.mpr ?_
  filter_upwards [Lp.coeFn_star (MeasureTheory.lpBoundedMulCLM hsym hCb0 hCb u),
    MeasureTheory.lpBoundedMulCLM_coeFn hsym hCb0 hCb u,
    MeasureTheory.lpBoundedMulCLM_coeFn hsym hCb0 hCb (star u),
    Lp.coeFn_star u] with z h1 h2 h3 h4
  rw [h1, h3, Pi.star_apply, h2, h4]
  simp only [RCLike.star_def, map_mul, Pi.star_apply]
  rw [hreal z]

theorem star_gaussPrimeScaleBlock {p : ℝ} (hp : 1 < p)
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    star (gaussPrimeScaleBlock hp u) = gaussPrimeScaleBlock hp (star u) :=
  star_lpBoundedMulCLM_real _ _ _ (gaussPrimeScaleCircle_real p) u

theorem star_gaussPrimeScaleInvSqBlock {p : ℝ} (hp : 1 < p)
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    star (gaussPrimeScaleInvSqBlock hp u) = gaussPrimeScaleInvSqBlock hp (star u) :=
  star_lpBoundedMulCLM_real _ _ _ (gaussPrimeScaleInvSqCircle_real p) u

theorem star_gaussDiagonalBlock (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    star (gaussDiagonalBlock hm k p u) = gaussDiagonalBlock hm k p (star u) := by
  refine lp_ext_fourierCoeff fun j => ?_
  rw [fourierCoeff_star, fourierCoeff_gaussDiagonalBlock, fourierCoeff_gaussDiagonalBlock,
    fourierCoeff_star, map_mul]
  congr 1
  rw [gaussSampleValue_neg k p j, Complex.conj_conj]

theorem star_gaussDiagonalBlockStar (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    star (gaussDiagonalBlockStar hm k p u) = gaussDiagonalBlockStar hm k p (star u) := by
  refine lp_ext_fourierCoeff fun j => ?_
  rw [fourierCoeff_star, fourierCoeff_gaussDiagonalBlockStar, fourierCoeff_gaussDiagonalBlockStar,
    fourierCoeff_star, map_mul]
  congr 1
  rw [Complex.conj_conj]
  exact gaussSampleValue_neg k p j

theorem star_lp_smul (c : ℂ) (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    star (c • u) = (starRingEnd ℂ c) • star u := by
  refine Lp.ext_iff.mpr ?_
  filter_upwards [Lp.coeFn_star (c • u), Lp.coeFn_smul c u,
    Lp.coeFn_smul (starRingEnd ℂ c) (star u), Lp.coeFn_star u] with z h1 h2 h3 h4
  rw [h1, h3, Pi.star_apply, h2]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h4]
  simp only [RCLike.star_def, map_mul, Pi.star_apply]

/-- **The quasi-inner block commutes with conjugation.** -/
theorem star_gaussQuasiInnerG (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    star (gaussQuasiInnerG hm k p u) = gaussQuasiInnerG hm k p (star u) := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  rw [gaussQuasiInnerG_apply hm k p hp, gaussQuasiInnerG_apply hm k p hp, star_lp_smul,
    star_gaussPrimeScaleBlock, star_gaussDiagonalBlock, star_gaussPrimeScaleInvSqBlock,
    star_gaussDiagonalBlockStar, star_gaussPrimeScaleBlock]
  congr 1
  simp only [Complex.conj_ofReal]

theorem star_gaussQuasiInnerG_pow (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (r : ℕ)
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    star ((gaussQuasiInnerG hm k p ^ r) u) = (gaussQuasiInnerG hm k p ^ r) (star u) := by
  induction r generalizing u with
  | zero => simp
  | succ r ih =>
      have h1 : ((gaussQuasiInnerG hm k p ^ (r + 1)) u)
          = (gaussQuasiInnerG hm k p ^ r) (gaussQuasiInnerG hm k p u) := by
        rw [pow_succ]
        rfl
      have h2 : ((gaussQuasiInnerG hm k p ^ (r + 1)) (star u))
          = (gaussQuasiInnerG hm k p ^ r) (gaussQuasiInnerG hm k p (star u)) := by
        rw [pow_succ]
        rfl
      rw [h1, h2, ih, star_gaussQuasiInnerG]

/-- **The diagonal of every power of `G` reflects into its conjugate.** -/
theorem inner_gaussQuasiInnerG_pow_neg (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (r : ℕ)
    (n : ℤ) :
    (inner ℂ (fourierLp 2 (-n)) ((gaussQuasiInnerG hm k p ^ r) (fourierLp 2 (-n))) : ℂ)
      = starRingEnd ℂ (inner ℂ (fourierLp 2 n)
        ((gaussQuasiInnerG hm k p ^ r) (fourierLp 2 n))) := by
  rw [← star_fourierLp n, ← star_gaussQuasiInnerG_pow hm k p r, inner_star_star]

/-! ## The sampled magnitude decays like `1/n` at every `m` -/

theorem exists_norm_gaussSampleValue_pow_mul_succ_le (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ‖gaussSampleValue k p ((n : ℤ) + 1)‖ ^ (2 * m) * ((n : ℝ) + 1) ≤ C := by
  obtain ⟨c, C, hc, hC, hb⟩ := exists_gaussComponentPrimeMagnitudeEnergy_bounds hm k p
  have harch : 0 < gaussArchConst m := gaussArchConst_pos hm
  refine ⟨C / gaussArchConst m, by positivity, fun n => ?_⟩
  have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hub := (hb n).2
  rw [gaussComponentPrimeMagnitudeEnergy_eq hm k p n, le_div_iff₀ hden] at hub
  rw [le_div_iff₀ harch]
  calc ‖gaussSampleValue k p ((n : ℤ) + 1)‖ ^ (2 * m) * ((n : ℝ) + 1) * gaussArchConst m
      = gaussArchConst m * ‖gaussSampleValue k p ((n : ℤ) + 1)‖ ^ (2 * m) * ((n : ℝ) + 1) := by
        ring
    _ ≤ C := hub

/-! ## The step scalar -/

theorem norm_gaussStepScalar_conj_eq (k : Fin m) (p : Nat.Primes) (i : ℤ) :
    ‖((p : ℝ) : ℂ) * (starRingEnd ℂ (gaussSampleValue k p i) * gaussSampleValue k p i)‖
      = (p : ℝ) * ‖gaussSampleValue k p i‖ ^ 2 := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have h : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    linarith
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hppos,
    RCLike.norm_conj]
  ring

theorem conj_gaussStepScalar_pow_mul_amplitude (k : Fin m) (p : Nat.Primes) (i : ℤ) (r : ℕ)
    (a : ℝ) :
    starRingEnd ℂ (((((p : ℝ) : ℂ) *
        (starRingEnd ℂ (gaussSampleValue k p i) * gaussSampleValue k p i)) ^ r) * ((a : ℝ) : ℂ))
      = ((((p : ℝ) : ℂ) *
          (starRingEnd ℂ (gaussSampleValue k p i) * gaussSampleValue k p i)) ^ r) *
        ((a : ℝ) : ℂ) := by
  rw [map_mul, map_pow, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
    Complex.conj_conj]
  ring

end

end RHTower
