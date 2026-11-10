import GaloisForLFunctions.InfiniteRankPurityTheory.AFactorWithADirichletSeriesIsPure
import GaloisForLFunctions.InfiniteRankPurityTheory.AZeroFreeDirichletPolynomialIsBoundedBelow
import GaloisForLFunctions.ArithmeticOrientationTheory.AKernelBoundedBelowOnTheHalfPlaneIsAUnit
import GaloisForLFunctions.RHTower.HerglotzDirichletCarrierRigidity
import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# A Dirichlet polynomial with a functional equation is not a factor

Let `D(s) = Σ a_n n^{-s}` be a Dirichlet polynomial with real coefficients and a constant term
which satisfies a functional equation, in the form `|D(1 - s)| = N^{Re s - 1/2} |D(s)|` with
`N > 1`. Then some zero of `D` is not a zero of `ξ`: a degree zero element of the extended Selberg
class does not divide `ξ`. No stability and no smallness is assumed.

Suppose every zero of `D` is a zero of `ξ`. Then:

* all zeros of `D` are on the critical line (purity of a factor), and `D` is bounded below on
  every closed half-plane right of it;
* `norm_dirW_sub_le`: `W(s) = N^{s/2} D(s)` has `|W(1 - s̄)| = |W(s)|`, and by Phragmén–Lindelöf
  `|W(s - δ)| ≤ |W(s)|` for `Re s ≥ 1/2 + δ/2`: the quotient is bounded on the half-plane and of
  modulus one on its boundary;
* `re_dirPhi_nonneg`, `re_dirPhi_eq_zero`: so `Φ = W'/W = (log N)/2 + D'/D` has nonnegative real
  part right of the line, and real part zero on the line off the zeros of `D`;
* `exists_real_coeff_dirPhi`: by the half-plane Wiener lemma `1/D` has an absolutely convergent
  Dirichlet series at `3/2`, hence so has `Φ`, with real coefficients and constant term
  `(log N)/2`;
* `exists_zero_not_xi_zero_of_functionalEquation`: a Herglotz Dirichlet series carried by the
  critical zeros of `ζ` vanishes (`eq_zero_of_herglotz_dirichlet_criticalCarrier`), so
  `(log N)/2 = 0`.
-/

open Complex Filter Topology Set Metric
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.InfiniteRankPurityTheory

open _root_.RHTower GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.ArithmeticOrientationTheory

/-! ### The polynomial, its derivative and the completed function -/

/-- The derivative of a Dirichlet polynomial. -/
def dirDeriv (a : ℕ →₀ ℂ) (s : ℂ) : ℂ :=
  ∑ n ∈ a.support, -(a n * (Real.log n : ℂ)) * (n : ℂ) ^ (-s)

theorem hasDerivAt_finiteDirichletPolynomial {a : ℕ →₀ ℂ} (ha0 : a 0 = 0) (s : ℂ) :
    HasDerivAt (finiteDirichletPolynomial a) (dirDeriv a s) s := by
  unfold dirDeriv
  refine HasDerivAt.fun_sum fun n hn => ?_
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (pos_of_mem_support ha0 hn).ne'
  have h := ((hasDerivAt_id s).neg.const_cpow (c := (n : ℂ)) (Or.inl hn0)).const_mul (a n)
  refine h.congr_deriv ?_
  rw [Complex.natCast_log]
  simp only [Pi.neg_apply, id_eq]
  ring

theorem differentiable_dirDeriv {a : ℕ →₀ ℂ} (ha0 : a 0 = 0) : Differentiable ℂ (dirDeriv a) := by
  intro z
  refine DifferentiableAt.fun_sum fun n hn => ?_
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (pos_of_mem_support ha0 hn).ne'
  exact (differentiableAt_id.neg.const_cpow (Or.inl hn0)).const_mul _

theorem conj_natCast_cpow_neg {n : ℕ} (hn : 0 < n) (s : ℂ) :
    conj ((n : ℂ) ^ (-s)) = (n : ℂ) ^ (-conj s) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [Complex.cpow_def_of_ne_zero hn0, Complex.cpow_def_of_ne_zero hn0, ← Complex.exp_conj,
    map_mul, map_neg, ← Complex.natCast_log, Complex.conj_ofReal]

/-- A Dirichlet polynomial with real coefficients commutes with conjugation. -/
theorem finiteDirichletPolynomial_conj {a : ℕ →₀ ℂ} (ha0 : a 0 = 0) (hreal : ∀ n, (a n).im = 0)
    (s : ℂ) : finiteDirichletPolynomial a (conj s) = conj (finiteDirichletPolynomial a s) := by
  unfold finiteDirichletPolynomial
  rw [map_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [map_mul, conj_natCast_cpow_neg (pos_of_mem_support ha0 hn), Complex.conj_eq_iff_im.mpr (hreal n)]

theorem dirDeriv_conj {a : ℕ →₀ ℂ} (ha0 : a 0 = 0) (hreal : ∀ n, (a n).im = 0) (s : ℂ) :
    dirDeriv a (conj s) = conj (dirDeriv a s) := by
  unfold dirDeriv
  rw [map_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [map_mul, map_neg, map_mul, Complex.conj_ofReal,
    conj_natCast_cpow_neg (pos_of_mem_support ha0 hn), Complex.conj_eq_iff_im.mpr (hreal n)]

/-- The completed function `W(s) = N^{s/2} D(s)`. -/
def dirW (a : ℕ →₀ ℂ) (N : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (s * ((Real.log N / 2 : ℝ) : ℂ)) * finiteDirichletPolynomial a s

/-- The logarithmic derivative `Φ = W'/W = (log N)/2 + D'/D`. -/
def dirPhi (a : ℕ →₀ ℂ) (N : ℝ) (s : ℂ) : ℂ :=
  ((Real.log N / 2 : ℝ) : ℂ) + dirDeriv a s / finiteDirichletPolynomial a s

theorem norm_dirW (a : ℕ →₀ ℂ) (N : ℝ) (s : ℂ) :
    ‖dirW a N s‖ = Real.exp (s.re * (Real.log N / 2)) * ‖finiteDirichletPolynomial a s‖ := by
  rw [dirW, norm_mul, Complex.norm_exp]
  congr 2
  simp

theorem hasDerivAt_dirW {a : ℕ →₀ ℂ} (ha0 : a 0 = 0) (N : ℝ) {s : ℂ}
    (hD : finiteDirichletPolynomial a s ≠ 0) :
    HasDerivAt (dirW a N) (dirW a N s * dirPhi a N s) s := by
  have h1 : HasDerivAt (fun z : ℂ => Complex.exp (z * ((Real.log N / 2 : ℝ) : ℂ)))
      (Complex.exp (s * ((Real.log N / 2 : ℝ) : ℂ)) * ((Real.log N / 2 : ℝ) : ℂ)) s := by
    simpa using ((hasDerivAt_id s).mul_const ((Real.log N / 2 : ℝ) : ℂ)).cexp
  refine (h1.mul (hasDerivAt_finiteDirichletPolynomial ha0 s)).congr_deriv ?_
  rw [dirW, dirPhi]
  field_simp

/-- **The functional equation as a symmetry of the modulus.** -/
theorem norm_dirW_one_sub_conj {a : ℕ →₀ ℂ} (ha0 : a 0 = 0) (hreal : ∀ n, (a n).im = 0) {N : ℝ}
    (hN : 0 < N) (hFE : ∀ s : ℂ, ‖finiteDirichletPolynomial a (1 - s)‖
      = N ^ (s.re - 1 / 2) * ‖finiteDirichletPolynomial a s‖) (s : ℂ) :
    ‖dirW a N (1 - conj s)‖ = ‖dirW a N s‖ := by
  have hc : (1 : ℂ) - conj s = conj (1 - s) := by simp
  rw [norm_dirW, norm_dirW, hc, finiteDirichletPolynomial_conj ha0 hreal, RCLike.norm_conj, hFE s,
    Real.rpow_def_of_pos hN, ← mul_assoc, ← Real.exp_add]
  congr 2
  simp only [Complex.conj_re, Complex.sub_re, Complex.one_re]
  ring

/-! ### The modulus increases to the right -/

/-- A function on the line with a derivative at `0` that does not exceed its value at `0` on a
right neighbourhood has a nonpositive derivative. -/
theorem deriv_nonpos_of_le_right {h : ℝ → ℝ} {h' : ℝ} (hd : HasDerivAt h h' 0) {ε : ℝ}
    (hε : 0 < ε) (hle : ∀ δ, 0 < δ → δ ≤ ε → h δ ≤ h 0) : h' ≤ 0 := by
  refine le_of_tendsto hd.tendsto_slope_zero_right ?_
  filter_upwards [Ioc_mem_nhdsGT hε] with t ht
  rw [zero_add, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht.1.le) (sub_nonpos.mpr (hle t ht.1 ht.2))

/-- **Phragmén–Lindelöf.** With all zeros of `D` on the critical line and the functional equation,
`|W(s - δ)| ≤ |W(s)|` on `Re s ≥ 1/2 + δ/2`. -/
theorem norm_dirW_sub_le {a : ℕ →₀ ℂ} (ha0 : a 0 = 0) (ha1 : a 1 ≠ 0)
    (hreal : ∀ n, (a n).im = 0) {N : ℝ} (hN : 1 < N)
    (hFE : ∀ s : ℂ, ‖finiteDirichletPolynomial a (1 - s)‖
      = N ^ (s.re - 1 / 2) * ‖finiteDirichletPolynomial a s‖)
    (hzf : ∀ z : ℂ, 1 / 2 < z.re → finiteDirichletPolynomial a z ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    {s : ℂ} (hs : 1 / 2 + δ / 2 ≤ s.re) : ‖dirW a N (s - δ)‖ ≤ ‖dirW a N s‖ := by
  have hlog : 0 < Real.log N / 2 := half_pos (Real.log_pos hN)
  obtain ⟨m, hm, hlow⟩ := exists_le_norm_of_zeroFree ha0 ha1
    (show (1 / 2 : ℝ) < 1 / 2 + δ / 2 by linarith) hzf
  set M : ℝ := ∑ n ∈ a.support, ‖a n‖ * (n : ℝ) ^ (-(-δ / 2 - 1)) with hM
  set f : ℂ → ℂ := fun z => dirW a N (z + ((1 / 2 - δ / 2 : ℝ) : ℂ))
    / dirW a N (z + ((1 / 2 + δ / 2 : ℝ) : ℂ)) with hf
  have hWne : ∀ z : ℂ, -(δ / 2) < z.re → dirW a N (z + ((1 / 2 + δ / 2 : ℝ) : ℂ)) ≠ 0 := by
    intro z hz
    rw [dirW]
    exact mul_ne_zero (Complex.exp_ne_zero _) (hzf _ (by simp; linarith))
  have hWd : Differentiable ℂ (dirW a N) := by
    unfold dirW
    exact (Complex.differentiable_exp.comp (differentiable_id.mul_const _)).mul
      (differentiable_finiteDirichletPolynomial a ha0)
  -- holomorphy up to the boundary
  have hd : DiffContOnCl ℂ f {z : ℂ | 0 < z.re} := by
    refine DifferentiableOn.diffContOnCl fun z hz => ?_
    rw [Complex.closure_setOf_lt_re] at hz
    exact ((hWd.comp (differentiable_id.add_const _)).differentiableAt.div
      (hWd.comp (differentiable_id.add_const _)).differentiableAt
      (hWne z (lt_of_lt_of_le (by linarith) hz))).differentiableWithinAt
  -- boundedness on the closed half-plane
  have hbound : ∀ z : ℂ, 0 ≤ z.re → ‖f z‖ ≤ M / m := by
    intro z hz
    rw [hf]
    simp only
    rw [norm_div, norm_dirW, norm_dirW]
    have hre1 : (z + ((1 / 2 - δ / 2 : ℝ) : ℂ)).re = z.re + (1 / 2 - δ / 2) := by simp
    have hre2 : (z + ((1 / 2 + δ / 2 : ℝ) : ℂ)).re = z.re + (1 / 2 + δ / 2) := by simp
    have hnum : ‖finiteDirichletPolynomial a (z + ((1 / 2 - δ / 2 : ℝ) : ℂ))‖ ≤ M :=
      norm_finiteDirichletPolynomial_le a ha0 (by rw [hre1]; linarith)
    have hden : m ≤ ‖finiteDirichletPolynomial a (z + ((1 / 2 + δ / 2 : ℝ) : ℂ))‖ :=
      hlow _ (by rw [hre2]; linarith)
    have hexp : Real.exp ((z + ((1 / 2 - δ / 2 : ℝ) : ℂ)).re * (Real.log N / 2))
        ≤ Real.exp ((z + ((1 / 2 + δ / 2 : ℝ) : ℂ)).re * (Real.log N / 2)) := by
      rw [hre1, hre2]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hM0 : 0 ≤ M := (norm_nonneg _).trans hnum
    rw [div_le_div_iff₀ (mul_pos (Real.exp_pos _) (hm.trans_le hden)) hm]
    calc Real.exp ((z + ((1 / 2 - δ / 2 : ℝ) : ℂ)).re * (Real.log N / 2))
          * ‖finiteDirichletPolynomial a (z + ((1 / 2 - δ / 2 : ℝ) : ℂ))‖ * m
        ≤ Real.exp ((z + ((1 / 2 + δ / 2 : ℝ) : ℂ)).re * (Real.log N / 2)) * M * m :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hexp hnum (norm_nonneg _) (Real.exp_pos _).le) hm.le
      _ ≤ M * (Real.exp ((z + ((1 / 2 + δ / 2 : ℝ) : ℂ)).re * (Real.log N / 2))
            * ‖finiteDirichletPolynomial a (z + ((1 / 2 + δ / 2 : ℝ) : ℂ))‖) := by
          have := mul_le_mul_of_nonneg_left hden
            (mul_nonneg hM0 (Real.exp_pos ((z + ((1 / 2 + δ / 2 : ℝ) : ℂ)).re
              * (Real.log N / 2))).le)
          linarith
  have hexp : ∃ c < (2 : ℝ), ∃ B, f =O[Bornology.cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 < z.re}]
      fun z => Real.exp (B * ‖z‖ ^ c) := by
    refine ⟨0, by norm_num, 0, Asymptotics.IsBigO.of_bound (M / m)
      (eventually_inf_principal.2 (Eventually.of_forall fun z hz => ?_))⟩
    simp only [zero_mul, Real.exp_zero, norm_one, mul_one]
    exact hbound z (le_of_lt hz)
  have hre : IsBoundedUnder (· ≤ ·) atTop fun x : ℝ => ‖f x‖ :=
    isBoundedUnder_of_eventually_le (a := M / m)
      ((eventually_ge_atTop (0 : ℝ)).mono fun x hx => hbound x (by simpa using hx))
  -- modulus one on the boundary
  have him : ∀ x : ℝ, ‖f (x * I)‖ ≤ 1 := by
    intro x
    have hpt : (x : ℂ) * I + ((1 / 2 - δ / 2 : ℝ) : ℂ)
        = 1 - conj ((x : ℂ) * I + ((1 / 2 + δ / 2 : ℝ) : ℂ)) := by
      simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring
    rw [hf]
    simp only
    rw [norm_div, hpt, norm_dirW_one_sub_conj ha0 hreal (zero_lt_one.trans hN) hFE]
    exact (div_self (norm_ne_zero_iff.mpr (hWne _ (by simp; linarith)))).le
  have hz : 0 ≤ (s - ((1 / 2 + δ / 2 : ℝ) : ℂ)).re := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  have hfin := PhragmenLindelof.right_half_plane_of_bounded_on_real hd hexp hre him hz
  rw [hf] at hfin
  simp only at hfin
  have h1 : s - ((1 / 2 + δ / 2 : ℝ) : ℂ) + ((1 / 2 - δ / 2 : ℝ) : ℂ) = s - δ := by
    push_cast
    ring
  have h2 : s - ((1 / 2 + δ / 2 : ℝ) : ℂ) + ((1 / 2 + δ / 2 : ℝ) : ℂ) = s := by ring
  rw [h1, h2, norm_div] at hfin
  have hpos : 0 < ‖dirW a N s‖ := by
    rw [dirW]
    exact norm_pos_iff.mpr (mul_ne_zero (Complex.exp_ne_zero _) (hzf s (by linarith)))
  exact (div_le_one hpos).mp hfin

/-- The derivative at `0` of `δ ↦ |W(s - δ)|²` is `-2 |W(s)|² Re Φ(s)`. -/
theorem hasDerivAt_normSq_dirW_sub {a : ℕ →₀ ℂ} (ha0 : a 0 = 0) (N : ℝ) {s : ℂ}
    (hD : finiteDirichletPolynomial a s ≠ 0) :
    HasDerivAt (fun δ : ℝ => ‖dirW a N (s - δ)‖ ^ 2)
      (-(2 * (‖dirW a N s‖ ^ 2 * (dirPhi a N s).re))) 0 := by
  have hin : HasDerivAt (fun δ : ℝ => s - (δ : ℂ)) (-1) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_sub s
    exact h.congr_deriv (by simp)
  have hW : HasDerivAt (dirW a N) (dirW a N s * dirPhi a N s) (s - ((0 : ℝ) : ℂ)) := by
    simpa using hasDerivAt_dirW ha0 N hD
  have hγ := (hW.scomp (0 : ℝ) hin).norm_sq
  refine hγ.congr_deriv ?_
  simp only [Function.comp_apply, Complex.ofReal_zero, sub_zero, neg_smul, one_smul, inner_neg_right]
  rw [Complex.inner]
  have hmul : dirW a N s * dirPhi a N s * conj (dirW a N s)
      = ((‖dirW a N s‖ ^ 2 : ℝ) : ℂ) * dirPhi a N s := by
    rw [mul_right_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hmul, Complex.re_ofReal_mul]
  ring

/-- **`Φ` is a Herglotz function.** -/
theorem re_dirPhi_nonneg {a : ℕ →₀ ℂ} (ha0 : a 0 = 0) (ha1 : a 1 ≠ 0)
    (hreal : ∀ n, (a n).im = 0) {N : ℝ} (hN : 1 < N)
    (hFE : ∀ s : ℂ, ‖finiteDirichletPolynomial a (1 - s)‖
      = N ^ (s.re - 1 / 2) * ‖finiteDirichletPolynomial a s‖)
    (hzf : ∀ z : ℂ, 1 / 2 < z.re → finiteDirichletPolynomial a z ≠ 0) {s : ℂ}
    (hs : 1 / 2 < s.re) : 0 ≤ (dirPhi a N s).re := by
  have hD := hzf s hs
  have hd := hasDerivAt_normSq_dirW_sub ha0 N hD
  have hle : ∀ δ : ℝ, 0 < δ → δ ≤ 2 * (s.re - 1 / 2) →
      ‖dirW a N (s - δ)‖ ^ 2 ≤ ‖dirW a N (s - ((0 : ℝ) : ℂ))‖ ^ 2 := by
    intro δ hδ hδs
    rw [Complex.ofReal_zero, sub_zero]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_dirW_sub_le ha0 ha1 hreal hN hFE hzf hδ (by linarith)) 2
  have h := deriv_nonpos_of_le_right hd (show 0 < 2 * (s.re - 1 / 2) by linarith) hle
  have hpos : 0 < ‖dirW a N s‖ ^ 2 := by
    rw [dirW]
    exact pow_pos (norm_pos_iff.mpr (mul_ne_zero (Complex.exp_ne_zero _) hD)) 2
  by_contra hneg
  have := mul_neg_of_pos_of_neg hpos (not_le.mp hneg)
  linarith

/-- **`Re Φ` vanishes on the critical line off the zeros of `D`.** -/
theorem re_dirPhi_eq_zero {a : ℕ →₀ ℂ} (ha0 : a 0 = 0) (hreal : ∀ n, (a n).im = 0) {N : ℝ}
    (hN : 0 < N) (hFE : ∀ s : ℂ, ‖finiteDirichletPolynomial a (1 - s)‖
      = N ^ (s.re - 1 / 2) * ‖finiteDirichletPolynomial a s‖) {t : ℝ}
    (hD : finiteDirichletPolynomial a ((1 / 2 : ℂ) + t * I) ≠ 0) :
    (dirPhi a N ((1 / 2 : ℂ) + t * I)).re = 0 := by
  set s : ℂ := (1 / 2 : ℂ) + t * I with hs
  have hd := hasDerivAt_normSq_dirW_sub ha0 N hD
  -- the function `δ ↦ |W(s - δ)|²` is even
  have heven : (fun δ : ℝ => ‖dirW a N (s - δ)‖ ^ 2) ∘ Neg.neg
      = fun δ : ℝ => ‖dirW a N (s - δ)‖ ^ 2 := by
    funext δ
    simp only [Function.comp_apply]
    have hpt : s - ((-δ : ℝ) : ℂ) = 1 - conj (s - (δ : ℂ)) := by
      rw [hs]
      simp only [map_sub, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_div₀, map_one,
        map_ofNat]
      push_cast
      ring
    rw [hpt, norm_dirW_one_sub_conj ha0 hreal hN hFE]
  have hd' : HasDerivAt ((fun δ : ℝ => ‖dirW a N (s - δ)‖ ^ 2) ∘ Neg.neg)
      (-(2 * (‖dirW a N s‖ ^ 2 * (dirPhi a N s).re)) * -1) 0 := by
    have h0 : HasDerivAt (fun δ : ℝ => ‖dirW a N (s - δ)‖ ^ 2)
        (-(2 * (‖dirW a N s‖ ^ 2 * (dirPhi a N s).re))) (-(0 : ℝ)) := by simpa using hd
    exact h0.comp (0 : ℝ) (hasDerivAt_neg 0)
  rw [heven] at hd'
  have huniq := hd.unique hd'
  have hpos : 0 < ‖dirW a N s‖ ^ 2 := by
    rw [dirW]
    exact pow_pos (norm_pos_iff.mpr (mul_ne_zero (Complex.exp_ne_zero _) hD)) 2
  have hzero : ‖dirW a N s‖ ^ 2 * (dirPhi a N s).re = 0 := by linarith
  exact (mul_eq_zero.mp hzero).resolve_left hpos.ne'

/-! ### The Dirichlet series of `Φ` -/

theorem lSeriesSummable_of_finite_support {f : ℕ → ℂ} (hf0 : f 0 = 0) (S : Finset ℕ)
    (hS : ∀ n ∉ S, f n = 0) (s : ℂ) : LSeriesSummable f s :=
  summable_of_ne_finset_zero (s := S) fun n hn => by
    rw [LSeries.term_def₀ hf0, hS n hn, zero_mul]

theorem lSeries_dirDeriv {a : ℕ →₀ ℂ} (ha0 : a 0 = 0) (s : ℂ) :
    LSeries (fun n => -(a n * (Real.log n : ℂ))) s = dirDeriv a s := by
  have hf0 : (fun n : ℕ => -(a n * (Real.log n : ℂ))) 0 = 0 := by simp [ha0]
  rw [LSeries, tsum_eq_sum (s := a.support)]
  · exact Finset.sum_congr rfl fun n _ =>
      LSeries.term_def₀ (f := fun n : ℕ => -(a n * (Real.log n : ℂ))) hf0 s n
  · intro n hn
    rw [LSeries.term_def₀ (f := fun n : ℕ => -(a n * (Real.log n : ℂ))) hf0,
      Finsupp.notMem_support_iff.mp hn]
    simp

/-- The Dirichlet series with conjugated coefficients, at a real point. -/
theorem lSeries_conj_ofReal (f : ℕ → ℂ) (x : ℝ) :
    LSeries (fun n => conj (f n)) (x : ℂ) = conj (LSeries f (x : ℂ)) := by
  rw [LSeries, LSeries, Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne', map_div₀]
    congr 1
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.conj_ofReal]

/-- **`Φ` is a Dirichlet series with real coefficients, absolutely convergent at `3/2`, with
constant term `(log N)/2`.** The inverse of `D` comes from the half-plane Wiener lemma. -/
theorem exists_real_coeff_dirPhi {a : ℕ →₀ ℂ} (ha0 : a 0 = 0) (ha1 : a 1 ≠ 0)
    (hreal : ∀ n, (a n).im = 0) (N : ℝ)
    (hzf : ∀ z : ℂ, 1 / 2 < z.re → finiteDirichletPolynomial a z ≠ 0) :
    ∃ c : ℕ → ℝ, LSeriesSummable (fun n => (c n : ℂ)) (3 / 2) ∧
      (∀ s : ℂ, 3 / 2 ≤ s.re → dirPhi a N s = LSeries (fun n => (c n : ℂ)) s) ∧
      c 1 = Real.log N / 2 := by
  have h32 : ((3 / 2 : ℝ) : ℂ) = 3 / 2 := by push_cast; ring
  -- the polynomial as an element of the Wiener algebra, and its inverse
  set fA : ArithmeticFunction ℂ := ⟨fun n => a n, ha0⟩ with hfA
  have hfAsum : ∀ s : ℂ, LSeriesSummable (⇑fA) s := fun s =>
    lSeriesSummable_of_finite_support ha0 a.support
      (fun n hn => Finsupp.notMem_support_iff.mp hn) s
  have hfAL : ∀ s : ℂ, LSeries (⇑fA) s = finiteDirichletPolynomial a s := fun s =>
    (finiteDirichletPolynomial_eq_LSeries a ha0 s).symm
  obtain ⟨m, hm, hlow⟩ := exists_le_norm_of_zeroFree ha0 ha1
    (show (1 / 2 : ℝ) < 3 / 2 by norm_num) hzf
  set F : WienerAlgebraAt (3 / 2) := ⟨fA, hfAsum _⟩ with hF
  have hunit : IsUnit F := WienerAlgebraAt.isUnit_of_le_norm_lSeries F hm fun s hs => by
    show m ≤ ‖LSeries (⇑fA) s‖
    rw [hfAL]
    exact hlow s hs
  obtain ⟨G, hG⟩ := hunit.exists_right_inv
  have hGsum : ∀ s : ℂ, 3 / 2 ≤ s.re → LSeriesSummable (⇑G.toFn) s := fun s hs =>
    G.summable.of_re_le_re (by simpa using hs)
  have hprod : ∀ s : ℂ, 3 / 2 ≤ s.re →
      finiteDirichletPolynomial a s * LSeries (⇑G.toFn) s = 1 := by
    intro s hs
    have h1 := LSeries_convolution' (hfAsum s) (hGsum s hs)
    rw [ArithmeticFunction.coe_mul, hfAL] at h1
    rw [← h1]
    have h2 : fA * G.toFn = 1 := by
      have := congrArg WienerAlgebraAt.toFn hG
      rwa [WienerAlgebraAt.toFn_mul, WienerAlgebraAt.toFn_one] at this
    rw [h2]
    show LSeries (fun n => (1 : ArithmeticFunction ℂ) n) s = 1
    rw [ArithmeticFunction.one_eq_delta, LSeries_delta]
    rfl
  -- the coefficients of `Φ`
  set fD : ArithmeticFunction ℂ := ⟨fun n => -(a n * (Real.log n : ℂ)), by simp [ha0]⟩ with hfD
  have hfDsum : ∀ s : ℂ, LSeriesSummable (⇑fD) s := fun s =>
    lSeriesSummable_of_finite_support (f := ⇑fD) fD.map_zero a.support
      (fun n hn => by simp [hfD, Finsupp.notMem_support_iff.mp hn]) s
  set d : ℕ → ℂ := fun n => if n = 1 then ((Real.log N / 2 : ℝ) : ℂ) else 0 with hd
  have hdsum : ∀ s : ℂ, LSeriesSummable d s := fun s =>
    lSeriesSummable_of_finite_support (f := d) (by simp [hd]) {1}
      (fun n hn => by simp [hd, Finset.mem_singleton.not.mp hn]) s
  have hdval : ∀ s : ℂ, LSeries d s = ((Real.log N / 2 : ℝ) : ℂ) := by
    intro s
    rw [LSeries, tsum_eq_single 1]
    · simp [LSeries.term, hd]
    · intro n hn
      simp [LSeries.term, hd, hn]
  set e : ℕ → ℂ := d + ⇑(fD * G.toFn) with he
  have hconvsum : ∀ s : ℂ, 3 / 2 ≤ s.re → LSeriesSummable (⇑(fD * G.toFn)) s := fun s hs => by
    rw [← ArithmeticFunction.coe_mul]
    exact (hfDsum s).convolution (hGsum s hs)
  have hesum : LSeriesSummable e (3 / 2) :=
    (hdsum _).add (hconvsum _ (by norm_num))
  have heL : ∀ s : ℂ, 3 / 2 ≤ s.re → LSeries e s = dirPhi a N s := by
    intro s hs
    have hDs : finiteDirichletPolynomial a s ≠ 0 := hzf s (by linarith)
    have hGval : LSeries (⇑G.toFn) s = (finiteDirichletPolynomial a s)⁻¹ :=
      eq_inv_of_mul_eq_one_right (hprod s hs)
    rw [he, LSeries_add (hdsum s) (hconvsum s hs), hdval, ← ArithmeticFunction.coe_mul,
      LSeries_convolution' (hfDsum s) (hGsum s hs), hGval, dirPhi]
    congr 1
    rw [div_eq_mul_inv]
    congr 1
    exact lSeries_dirDeriv ha0 s
  -- the coefficients are real: `Φ` is real on the real axis
  have habs : LSeries.abscissaOfAbsConv e < ⊤ :=
    lt_of_le_of_lt (LSeriesSummable.abscissaOfAbsConv_le hesum) (EReal.coe_lt_top _)
  have hesum' : LSeriesSummable (fun n => conj (e n)) (3 / 2) := by
    have hnorm : ∀ n, ‖LSeries.term (fun n => conj (e n)) (3 / 2) n‖ = ‖LSeries.term e (3 / 2) n‖ := by
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [LSeries.term_zero]
      · rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne', norm_div, norm_div,
          RCLike.norm_conj]
    exact Summable.of_norm ((summable_congr hnorm).mpr hesum.norm)
  have habs' : LSeries.abscissaOfAbsConv (fun n => conj (e n)) < ⊤ :=
    lt_of_le_of_lt (LSeriesSummable.abscissaOfAbsConv_le hesum') (EReal.coe_lt_top _)
  have hev : (fun x : ℝ => LSeries (fun n => conj (e n)) x) =ᶠ[atTop] fun x => LSeries e x := by
    filter_upwards [eventually_ge_atTop (3 / 2 : ℝ)] with x hx
    have hxs : (3 / 2 : ℝ) ≤ ((x : ℝ) : ℂ).re := by simpa using hx
    rw [lSeries_conj_ofReal, heL _ hxs, dirPhi, map_add, map_div₀, Complex.conj_ofReal,
      ← dirDeriv_conj ha0 hreal, ← finiteDirichletPolynomial_conj ha0 hreal, Complex.conj_ofReal]
  have hereal : ∀ n, conj (e n) = e n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [he, hd]
    · exact LSeries.eq_of_LSeries_eventually_eq habs' habs hev hn.ne'
  have hcoe : (fun n => (((e n).re : ℝ) : ℂ)) = e := by
    funext n
    exact Complex.conj_eq_iff_re.mp (hereal n)
  refine ⟨fun n => (e n).re, ?_, fun s hs => ?_, ?_⟩
  · rw [hcoe]
    exact hesum
  · rw [hcoe, heL s hs]
  · show (e 1).re = Real.log N / 2
    simp [he, hd, hfD]

/-! ### The theorem -/

/-- **A Dirichlet polynomial with a functional equation is not a factor of `ξ`.** Real
coefficients, a constant term, and `|D(1 - s)| = N^{Re s - 1/2} |D(s)|` with `N > 1`: some zero of
`D` is not a zero of `ξ`. -/
theorem exists_zero_not_xi_zero_of_functionalEquation (a : ℕ →₀ ℂ) (ha0 : a 0 = 0)
    (ha1 : a 1 ≠ 0) (hreal : ∀ n, (a n).im = 0) {N : ℝ} (hN : 1 < N)
    (hFE : ∀ s : ℂ, ‖finiteDirichletPolynomial a (1 - s)‖
      = N ^ (s.re - 1 / 2) * ‖finiteDirichletPolynomial a s‖) :
    ∃ z : ℂ, finiteDirichletPolynomial a z = 0 ∧ xi z ≠ 0 := by
  by_contra hcon
  have hall : ∀ z : ℂ, finiteDirichletPolynomial a z = 0 → xi z = 0 := fun z hz => by
    by_contra hxi
    exact hcon ⟨z, hz, hxi⟩
  have hane : a ≠ 0 := fun h => ha1 (by rw [h]; rfl)
  -- all zeros are on the critical line
  have hzf : ∀ z : ℂ, 1 / 2 < z.re → finiteDirichletPolynomial a z ≠ 0 := fun z hz h0 => by
    have := re_eq_half_of_dirichletPolynomial_zeros_subset_xi a ha0 hane hall h0
    linarith
  obtain ⟨c, hcsum, hcL, hc1⟩ := exists_real_coeff_dirPhi ha0 ha1 hreal N hzf
  have hΦd : DifferentiableOn ℂ (dirPhi a N) {s : ℂ | 1 / 2 < s.re} := fun s hs =>
    ((differentiableAt_const _).add
      ((differentiable_dirDeriv ha0).differentiableAt.div
        (differentiable_finiteDirichletPolynomial a ha0).differentiableAt
        (hzf s hs))).differentiableWithinAt
  have hlim : ∀ t : ℝ, riemannZeta ((1 / 2 : ℂ) + t * I) ≠ 0 →
      Tendsto (fun s => (dirPhi a N s).re) (𝓝[{s : ℂ | 1 / 2 < s.re}] ((1 / 2 : ℂ) + t * I))
        (𝓝 0) := by
    intro t ht
    have hD : finiteDirichletPolynomial a ((1 / 2 : ℂ) + t * I) ≠ 0 := by
      intro h0
      have hxi := hall _ h0
      refine ht ((xi_eq_zero_iff (by simp) fun h1 => ?_).mp hxi)
      have := congrArg Complex.re h1
      simp at this
    have hcont : ContinuousAt (dirPhi a N) ((1 / 2 : ℂ) + t * I) :=
      continuousAt_const.add ((differentiable_dirDeriv ha0).continuous.continuousAt.div
        (differentiable_finiteDirichletPolynomial a ha0).continuous.continuousAt hD)
    have h := (Complex.continuous_re.continuousAt.comp hcont).tendsto
    rw [Function.comp_apply, re_dirPhi_eq_zero ha0 hreal (zero_lt_one.trans hN) hFE hD] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h := AtomDomination.eq_zero_of_herglotz_dirichlet_criticalCarrier hΦd
    (fun s hs => re_dirPhi_nonneg ha0 ha1 hreal hN hFE hzf hs) hcsum hcL hlim 1 le_rfl
  rw [hc1] at h
  linarith [Real.log_pos hN]

end GaloisForLFunctions.InfiniteRankPurityTheory
