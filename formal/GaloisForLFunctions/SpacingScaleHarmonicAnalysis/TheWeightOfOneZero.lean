import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheAtomicFamilyIsADirichletPolynomial
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheCriticalExponent

/-!
# The weight of one zero

On an atomic test the term of a zero `ρ = β + iγ` in Weil's form is
`m_ρ h_g(γ_ρ) conj h_g(γ̄_ρ) · D_x(γ_ρ) conj D_x(γ̄_ρ)` (`Wsummand_atomicTest`). Its two
Dirichlet-polynomial factors read the weights against `n^{σ}` and `n^{−σ}`, `σ = β − ½`, and their
product is controlled by power sums alone:

* **Power sums** (`sum_rpow_le_of_nonneg`, `sum_rpow_neg_le`, `sum_rpow_mul_sum_rpow_neg_le`):
  `(Σ_{n≤N} n^a)(Σ_{n≤N} n^{−a}) ≤ (N+1)²/(1 − a²)` for `0 ≤ a < 1`, by comparison with
  `∫ t^{±a} dt`.
* **The weight of one zero** (`norm_Wsummand_atomicTest_le`): for a bump supported in `[−r, r]`,
  `‖term_ρ‖ ≤ m_ρ (e^{|σ| r} ‖g‖₁)² ‖x‖² (N + 1)/√(1 − 4σ²)`, and `1 − 4σ² = 4β(1 − β)`.
* **For dilated profiles** (`norm_Wsummand_atomicTest_dilate_le`): relative to the diagonal energy
  `‖x‖² ‖φ_k‖₂² = k ‖x‖² ‖φ‖₂²` the weight is at most
  `m_ρ e^{2|σ|/k} (‖φ‖₁²/‖φ‖₂²) ((N + 1)/k) / (2√(β(1 − β)))`.

`(N + 1)/k` is the overlap ratio up to a factor two. At the spacing a single zero carries a bounded
fraction of the diagonal energy, uniformly in its height and in `N`, and an off-line zero weighs at
most `1/(2√(β(1 − β)))` times the on-line bound: the zeros sample the Dirichlet polynomial at the
Nyquist rate, each with weight at most the overlap ratio.
-/

noncomputable section

open MeasureTheory Finset Zeta23
open scoped Real ComplexConjugate

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open ArithmeticElectrostatics ArithmeticCastelnuovoSeveri

/-! ### Power sums -/

theorem sum_Icc_eq_sum_range (N : ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, f n = ∑ i ∈ range N, f (1 + i) := by
  have h : Icc 1 N = Ico 1 (N + 1) := by
    ext n
    simp only [mem_Icc, mem_Ico]
    omega
  rw [h, sum_Ico_eq_sum_range, Nat.add_sub_cancel]

/-- `Σ_{n ≤ N} n^a ≤ (N + 1)^{a+1}/(a + 1)` for `a ≥ 0`. -/
theorem sum_rpow_le_of_nonneg {a : ℝ} (ha : 0 ≤ a) (N : ℕ) :
    ∑ n ∈ Icc 1 N, (n : ℝ) ^ a ≤ ((N : ℝ) + 1) ^ (a + 1) / (a + 1) := by
  have hmono : MonotoneOn (fun t : ℝ => t ^ a) (Set.Icc 1 (1 + (N : ℝ))) :=
    fun s hs t _ hst => Real.rpow_le_rpow (by linarith [hs.1]) hst ha
  have h := hmono.sum_le_integral
  rw [integral_rpow (Or.inl (by linarith))] at h
  rw [sum_Icc_eq_sum_range]
  push_cast
  refine h.trans ?_
  rw [add_comm (1 : ℝ) N, Real.one_rpow]
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- `Σ_{n ≤ M+1} n^{−a} ≤ (M + 1)^{1−a}/(1 − a)` for `0 ≤ a < 1`. -/
theorem sum_rpow_neg_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (M : ℕ) :
    ∑ n ∈ Icc 1 (M + 1), (n : ℝ) ^ (-a) ≤ ((M : ℝ) + 1) ^ (1 - a) / (1 - a) := by
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-a)) (Set.Icc 1 (1 + (M : ℝ))) :=
    fun s hs t _ hst => Real.rpow_le_rpow_of_nonpos (by linarith [hs.1]) hst (by linarith)
  have h := hanti.sum_le_integral
  rw [integral_rpow (Or.inl (by linarith))] at h
  rw [sum_Icc_eq_sum_range, sum_range_succ']
  push_cast at h ⊢
  simp only [Real.one_rpow] at h ⊢
  rw [show -a + 1 = 1 - a by ring, add_comm (1 : ℝ) M] at h
  have h1a : 0 < 1 - a := by linarith
  have key : (((M : ℝ) + 1) ^ (1 - a) - 1) / (1 - a) + 1 ≤ ((M : ℝ) + 1) ^ (1 - a) / (1 - a) := by
    rw [div_add_one h1a.ne', div_le_div_iff_of_pos_right h1a]
    linarith
  calc ∑ i ∈ range M, (1 + ((i : ℝ) + 1)) ^ (-a) + 1
      ≤ (((M : ℝ) + 1) ^ (1 - a) - 1) / (1 - a) + 1 := by
        refine add_le_add (le_of_eq_of_le ?_ h) le_rfl
        refine sum_congr rfl fun i _ => ?_
        ring_nf
    _ ≤ _ := key

/-- **The product of the two power sums**: `(Σ n^a)(Σ n^{−a}) ≤ (N + 1)²/(1 − a²)`. -/
theorem sum_rpow_mul_sum_rpow_neg_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 N, (n : ℝ) ^ a) * (∑ n ∈ Icc 1 N, (n : ℝ) ^ (-a)) ≤
      ((N : ℝ) + 1) ^ 2 / (1 - a ^ 2) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have h1 := sum_rpow_le_of_nonneg ha0 (M + 1)
  have h2 := sum_rpow_neg_le ha0 ha1 M
  have hS1 : 0 ≤ ∑ n ∈ Icc 1 (M + 1), (n : ℝ) ^ (-a) :=
    sum_nonneg fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hP : (0 : ℝ) < (M : ℝ) + 1 + 1 := by positivity
  have hmono : ((M : ℝ) + 1) ^ (1 - a) ≤ ((M : ℝ) + 1 + 1) ^ (1 - a) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  have h1a : 0 < 1 - a := by linarith
  have h2' : ∑ n ∈ Icc 1 (M + 1), (n : ℝ) ^ (-a) ≤ ((M : ℝ) + 1 + 1) ^ (1 - a) / (1 - a) :=
    h2.trans (div_le_div_of_nonneg_right hmono h1a.le)
  have hprod : ((M : ℝ) + 1 + 1) ^ (a + 1) * ((M : ℝ) + 1 + 1) ^ (1 - a) =
      ((M : ℝ) + 1 + 1) ^ 2 := by
    rw [← Real.rpow_add hP, show a + 1 + (1 - a) = ((2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  push_cast
  calc (∑ n ∈ Icc 1 (M + 1), (n : ℝ) ^ a) * (∑ n ∈ Icc 1 (M + 1), (n : ℝ) ^ (-a))
      ≤ (((M : ℝ) + 1 + 1) ^ (a + 1) / (a + 1)) *
          (((M : ℝ) + 1 + 1) ^ (1 - a) / (1 - a)) := by
        push_cast at h1
        exact mul_le_mul h1 h2' hS1 (by positivity)
    _ = ((M : ℝ) + 1 + 1) ^ 2 / (1 - a ^ 2) := by
        rw [div_mul_div_comm, hprod]
        congr 1
        ring

/-! ### The two factors -/

/-- `‖e^{iz log n}‖ = n^{−Im z}`. -/
theorem norm_cexp_I_mul_log (z : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    ‖Complex.exp (Complex.I * z * (Real.log n : ℂ))‖ = (n : ℝ) ^ (-z.im) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Complex.norm_exp, Real.rpow_def_of_pos hn0]
  congr 1
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_im]
  ring

/-- **Cauchy–Schwarz for the Dirichlet factor**: `‖D_x(z)‖² ≤ ‖x‖² Σ_{n ≤ N} n^{−2 Im z}`. -/
theorem norm_dirichletPoly_sq_le (N : ℕ) (x : ℕ → ℝ) (z : ℂ) :
    ‖dirichletPoly N x z‖ ^ 2 ≤
      (∑ n ∈ Icc 1 N, x n ^ 2) * ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-(2 * z.im)) := by
  have hle : ‖dirichletPoly N x z‖ ≤ ∑ n ∈ Icc 1 N, |x n| * (n : ℝ) ^ (-z.im) := by
    unfold dirichletPoly
    refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun n hn => ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      norm_cexp_I_mul_log z (mem_Icc.mp hn).1]
  have hcs := sum_mul_sq_le_sq_mul_sq (Icc 1 N) (fun n => |x n|) (fun n => (n : ℝ) ^ (-z.im))
  have hsq : ∀ n ∈ Icc 1 N, ((n : ℝ) ^ (-z.im)) ^ 2 = (n : ℝ) ^ (-(2 * z.im)) := fun n _ => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    push_cast
    ring
  simp only [sq_abs] at hcs
  rw [sum_congr rfl hsq] at hcs
  exact (pow_le_pow_left₀ (norm_nonneg _) hle 2).trans hcs

/-- **The bump factor**: for `g` supported in `[−r, r]`, `‖h_g(z)‖ ≤ e^{|Im z| r} ‖g‖₁`. -/
theorem norm_paperFT_le_of_supportedIn {g : ℝ → ℝ} {r : ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgr : SupportedIn r g) (z : ℂ) :
    ‖paperFT (cx g) z‖ ≤ Real.exp (|z.im| * r) * ∫ u, |g u| := by
  unfold paperFT
  have hint : Integrable fun u => |g u| * Real.exp (|z.im| * r) :=
    (hg.integrable_of_hasCompactSupport hgc).abs.mul_const _
  refine (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun u => ?_)).trans
    (le_of_eq (by rw [integral_mul_const, mul_comm]))
  by_cases hu : r < |u|
  · simp [cx, hgr u hu]
  · push Not at hu
    rw [norm_mul, show cx g u = ((g u : ℝ) : ℂ) from rfl, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
    have : (Complex.I * z * (u : ℂ)).re = -(z.im * u) := by
      simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_im]
      ring
    rw [this]
    calc -(z.im * u) ≤ |z.im * u| := neg_le_abs _
      _ = |z.im| * |u| := abs_mul _ _
      _ ≤ |z.im| * r := mul_le_mul_of_nonneg_left hu (abs_nonneg _)

/-! ### The weight of one zero -/

theorem gammaOf_im (ρ : ℂ) : (gammaOf ρ).im = -(ρ.re - 1 / 2) := by
  simp [gammaOf, Complex.div_I]

/-- **The weight of one zero**: for a bump supported in `[−r, r]` and a zero `ρ` with
`σ = Re ρ − ½`, `|σ| < ½`,
`‖term_ρ(f_x)‖ ≤ m_ρ (e^{|σ| r} ‖g‖₁)² ‖x‖² (N + 1)/√(1 − 4σ²)`. -/
theorem norm_Wsummand_atomicTest_le (Z : ZeroConfig) {g : ℝ → ℝ} {r : ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgr : SupportedIn r g) {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ)
    {ρ : ℂ} (hσ : |ρ.re - 1 / 2| < 1 / 2) :
    ‖Z.Wsummand (cx (atomicTest N x g)) (cx (atomicTest N x g)) ρ‖ ≤
      Z.mult ρ * (Real.exp (|ρ.re - 1 / 2| * r) * ∫ u, |g u|) ^ 2 *
        ((∑ n ∈ Icc 1 N, x n ^ 2) * (((N : ℝ) + 1) / Real.sqrt (1 - 4 * (ρ.re - 1 / 2) ^ 2))) := by
  set σ := ρ.re - 1 / 2
  set X := ∑ n ∈ Icc 1 N, x n ^ 2
  set a := 2 * |σ|
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a < 1 := by simp only [a]; linarith
  have ha2 : a ^ 2 = 4 * σ ^ 2 := by simp only [a]; rw [mul_pow, sq_abs]; ring
  have h1a : 0 < 1 - a ^ 2 := by nlinarith
  have hX : 0 ≤ X := sum_nonneg fun n _ => sq_nonneg _
  rw [Wsummand_atomicTest Z hg hgc, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_natCast,
    Complex.norm_conj, Complex.norm_conj]
  -- the bump factors
  have hb1 := norm_paperFT_le_of_supportedIn hg hgc hgr (gammaOf ρ)
  have hb2 := norm_paperFT_le_of_supportedIn hg hgc hgr (conj (gammaOf ρ))
  rw [Complex.conj_im, gammaOf_im, neg_neg] at hb2
  rw [gammaOf_im, abs_neg] at hb1
  have hB : ‖paperFT (cx g) (gammaOf ρ)‖ * ‖paperFT (cx g) (conj (gammaOf ρ))‖ ≤
      (Real.exp (|σ| * r) * ∫ u, |g u|) ^ 2 := by
    rw [sq]
    exact mul_le_mul hb1 hb2 (norm_nonneg _) ((norm_nonneg _).trans hb1)
  -- the Dirichlet factors
  have hd1 := norm_dirichletPoly_sq_le N x (gammaOf ρ)
  have hd2 := norm_dirichletPoly_sq_le N x (conj (gammaOf ρ))
  rw [gammaOf_im] at hd1
  rw [Complex.conj_im, gammaOf_im, neg_neg] at hd2
  have hpow : (∑ n ∈ Icc 1 N, (n : ℝ) ^ (-(2 * -σ))) * ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-(2 * σ)) =
      (∑ n ∈ Icc 1 N, (n : ℝ) ^ a) * ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-a) := by
    rcases le_or_gt 0 σ with h | h
    · have e1 : -(2 * -σ) = a := by simp only [a, abs_of_nonneg h]; ring
      have e2 : -(2 * σ) = -a := by simp only [a, abs_of_nonneg h]
      rw [e1, e2]
    · have e1 : -(2 * -σ) = -a := by simp only [a, abs_of_neg h]
      have e2 : -(2 * σ) = a := by simp only [a, abs_of_neg h, mul_neg]
      rw [e1, e2, mul_comm]
  have hS := sum_rpow_mul_sum_rpow_neg_le ha0 ha1 hN
  have hD : ‖dirichletPoly N x (gammaOf ρ)‖ * ‖dirichletPoly N x (conj (gammaOf ρ))‖ ≤
      X * (((N : ℝ) + 1) / Real.sqrt (1 - 4 * σ ^ 2)) := by
    have hsq : (‖dirichletPoly N x (gammaOf ρ)‖ * ‖dirichletPoly N x (conj (gammaOf ρ))‖) ^ 2 ≤
        X ^ 2 * (((N : ℝ) + 1) ^ 2 / (1 - a ^ 2)) := by
      rw [mul_pow]
      have hs1 : 0 ≤ ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-(2 * σ)) :=
        sum_nonneg fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
      calc ‖dirichletPoly N x (gammaOf ρ)‖ ^ 2 * ‖dirichletPoly N x (conj (gammaOf ρ))‖ ^ 2
          ≤ (X * ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-(2 * -σ))) *
              (X * ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-(2 * σ))) :=
            mul_le_mul hd1 hd2 (sq_nonneg _) ((sq_nonneg _).trans hd1)
        _ = X ^ 2 * ((∑ n ∈ Icc 1 N, (n : ℝ) ^ (-(2 * -σ))) *
              ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-(2 * σ))) := by ring
        _ ≤ X ^ 2 * (((N : ℝ) + 1) ^ 2 / (1 - a ^ 2)) := by
            rw [hpow]
            exact mul_le_mul_of_nonneg_left hS (sq_nonneg _)
    have hrhs : Real.sqrt (X ^ 2 * (((N : ℝ) + 1) ^ 2 / (1 - a ^ 2))) =
        X * (((N : ℝ) + 1) / Real.sqrt (1 - 4 * σ ^ 2)) := by
      rw [Real.sqrt_mul (sq_nonneg X), Real.sqrt_sq hX, Real.sqrt_div' _ h1a.le,
        Real.sqrt_sq (by positivity), ha2]
    rw [← hrhs]
    exact Real.le_sqrt_of_sq_le hsq
  have hm : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
  calc (Z.mult ρ : ℝ) * (‖paperFT (cx g) (gammaOf ρ)‖ * ‖paperFT (cx g) (conj (gammaOf ρ))‖) *
        (‖dirichletPoly N x (gammaOf ρ)‖ * ‖dirichletPoly N x (conj (gammaOf ρ))‖)
      ≤ Z.mult ρ * (Real.exp (|σ| * r) * ∫ u, |g u|) ^ 2 *
          (X * (((N : ℝ) + 1) / Real.sqrt (1 - 4 * σ ^ 2))) := by
        gcongr
    _ = _ := rfl

theorem integral_sq_dilate {k : ℝ} (hk : 0 < k) (φ : ℝ → ℝ) :
    ∫ s, dilate k φ s ^ 2 = k * ∫ s, φ s ^ 2 := by
  unfold dilate
  simp_rw [mul_pow]
  rw [MeasureTheory.integral_const_mul, Measure.integral_comp_mul_left (fun s => φ s ^ 2) k,
    smul_eq_mul, abs_inv, abs_of_pos hk]
  field_simp

/-- **The weight of one zero for a dilated profile**: relative to the diagonal energy
`‖x‖² ‖φ_k‖₂²`, a zero with `σ = Re ρ − ½`, `|σ| < ½`, carries at most
`m_ρ e^{2|σ|/k} (‖φ‖₁²/‖φ‖₂²) ((N + 1)/k)/√(1 − 4σ²)`. -/
theorem norm_Wsummand_atomicTest_dilate_le (Z : ZeroConfig) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφ1 : VanishesOff φ) (hφ2 : 0 < ∫ s, φ s ^ 2) {k : ℝ} (hk : 0 < k) {N : ℕ} (hN : 1 ≤ N)
    (x : ℕ → ℝ) {ρ : ℂ} (hσ : |ρ.re - 1 / 2| < 1 / 2) :
    ‖Z.Wsummand (cx (atomicTest N x (dilate k φ))) (cx (atomicTest N x (dilate k φ))) ρ‖ ≤
      Z.mult ρ * Real.exp (2 * |ρ.re - 1 / 2| / k) * ((∫ s, |φ s|) ^ 2 / ∫ s, φ s ^ 2) *
        ((((N : ℝ) + 1) / k) / Real.sqrt (1 - 4 * (ρ.re - 1 / 2) ^ 2)) *
          ((∑ n ∈ Icc 1 N, x n ^ 2) * ∫ s, dilate k φ s ^ 2) := by
  have hc : Continuous (dilate k φ) := continuous_const.mul (hφ.comp (continuous_const.mul
    continuous_id))
  have hr : SupportedIn (1 / k) (dilate k φ) := fun u hu => dilate_vanishes hφ1 hk hu
  have h := norm_Wsummand_atomicTest_le Z hc (hasCompactSupport_of_vanishes hr) hr hN x hσ
  rw [integral_abs_dilate hk, integral_sq_dilate hk] at *
  refine h.trans (le_of_eq ?_)
  have hk0 : k ≠ 0 := hk.ne'
  have hφ0 : (∫ s, φ s ^ 2) ≠ 0 := hφ2.ne'
  have hexp : Real.exp (|ρ.re - 1 / 2| * (1 / k)) ^ 2 = Real.exp (2 * |ρ.re - 1 / 2| / k) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [mul_pow, hexp]
  field_simp

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
