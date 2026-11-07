import GaloisForLFunctions.RHTower.TwoDilationDivisorMetric
import GaloisForLFunctions.RHTower.XiRealAxisNonvanishing
import GaloisForLFunctions.RHTower.Matveev.HermiteApproximateSchwarz
import Mathlib.Algebra.MvPolynomial.Eval
/-!
# Positive two-prime annihilators of finite zero sets

Every finite set of nontrivial zeta zeros, with arbitrary prescribed multiplicities, has a finite
Dirichlet annihilator with nonnegative real coefficients, constant coefficient one, and support
on powers of two and three. It can be uniformly arbitrarily close to one on `Re s ≥ 1`.

A nontrivial unit phase has arbitrarily late powers with negative real part. Each such power
gives a positive quadratic factor annihilating a prescribed point and its conjugate. Moving
the exponent outward makes its error on the closed right half-plane tend to zero. Products
handle finite sets; the irrational logarithmic ratio of two and three excludes trivial phases.
Taking a sufficiently high power imposes the prescribed zero orders; continuity of the power
map at one retains the desired uniform accuracy.
-/

set_option autoImplicit false

open Complex Filter Topology
open scoped NNReal
noncomputable section
namespace GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

/-- A nontrivial unit complex number has arbitrarily late powers in the left half-plane. -/
theorem exists_large_pow_re_neg {w : ℂ} (hw : ‖w‖ = 1) (hw1 : w ≠ 1) (N : ℕ) :
    ∃ k : ℕ, N ≤ k ∧ (w ^ k).re < 0 := by
  by_contra! h
  have hhalf (k : ℕ) (hk : N ≤ k) : (1 : ℝ) / 2 ≤ (w ^ k).re := by
    have hpos := h k hk
    have hdouble := h (k + k) (by omega)
    rw [pow_add, Complex.mul_re] at hdouble
    have hcircle : (w ^ k).re ^ 2 + (w ^ k).im ^ 2 = 1 := by
      have hs := Complex.normSq_eq_norm_sq (w ^ k)
      rw [Complex.normSq_apply, norm_pow, hw, one_pow] at hs
      nlinarith only [hs]
    nlinarith only [hpos, hdouble, hcircle]
  have hd : 0 < ‖w - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw1)
  obtain ⟨K, hK⟩ := exists_nat_gt (4 / ‖w - 1‖)
  have hK' : 4 < (K : ℝ) * ‖w - 1‖ := (div_lt_iff₀ hd).mp hK
  let S : ℂ := ∑ j ∈ Finset.range K, w ^ (N + j)
  have hlow : (K : ℝ) / 2 ≤ S.re := by
    rw [show S.re = ∑ j ∈ Finset.range K, (w ^ (N + j)).re by
      dsimp [S]; exact map_sum Complex.reAddGroupHom _ _]
    calc
      (K : ℝ) / 2 = ∑ j ∈ Finset.range K, (1 : ℝ) / 2 := by simp; ring
      _ ≤ ∑ j ∈ Finset.range K, (w ^ (N + j)).re :=
        Finset.sum_le_sum fun j _ => hhalf (N + j) (by omega)
  have hgeom : S * (w - 1) = w ^ N * (w ^ K - 1) := by
    dsimp [S]
    simp only [pow_add, ← Finset.mul_sum]
    rw [mul_assoc, geom_sum_mul]
  have hupper : ‖S‖ * ‖w - 1‖ ≤ 2 := by
    rw [← norm_mul, hgeom, norm_mul, norm_pow, hw, one_pow, one_mul]
    calc
      ‖w ^ K - 1‖ ≤ ‖w ^ K‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hw]; norm_num
  have hreal := Complex.re_le_norm S
  have hmul := mul_le_mul_of_nonneg_right (hlow.trans hreal) hd.le
  nlinarith only [hK', hupper, hmul]

/-- The phases at the two least primes cannot both be trivial at a nonzero frequency. -/
theorem two_three_phase_ne_one {γ : ℝ} (hγ : γ ≠ 0) :
    Complex.exp (-(Real.log 2 : ℂ) * (γ : ℂ) * I) ≠ 1 ∨
    Complex.exp (-(Real.log 3 : ℂ) * (γ : ℂ) * I) ≠ 1 := by
  by_contra! h
  let f : ℝ → ℂ := fun x => Complex.exp (-(x : ℂ) * (γ : ℂ) * I)
  have hf : Continuous f := by fun_prop
  have hperiod {p : ℕ} (hp : Complex.exp (-(Real.log p : ℂ) * (γ : ℂ) * I) = 1)
      (x : ℝ) : f (x + Real.log p) = f x := by
    dsimp [f]
    rw [Complex.ofReal_add, neg_add, add_mul, add_mul, Complex.exp_add, hp, mul_one]
  have hind : ∀ m n : ℕ, 0 < m → 0 < n → (2 : ℕ) ^ m ≠ 3 ^ n := by
    intro m n hm _ heq
    have heven : Even ((2 : ℕ) ^ m) := Nat.even_pow.mpr ⟨even_two, hm.ne'⟩
    have hodd : Odd ((3 : ℕ) ^ n) := (by decide : Odd (3 : ℕ)).pow
    rw [heq] at heven
    exact (Nat.not_even_iff_odd.mpr hodd) heven
  have heq := RHTower.eq_of_two_dilation_invariance hf (by norm_num : 2 ≤ (2 : ℕ))
    (by norm_num : 2 ≤ (3 : ℕ)) hind (hperiod h.1) (hperiod h.2) (Real.pi / γ) 0
  have harg : -((Real.pi / γ : ℝ) : ℂ) * (γ : ℂ) * I = -(Real.pi : ℂ) * I := by
    push_cast
    have hγc : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ
    field_simp
  dsimp [f] at heq
  rw [harg, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I] at heq
  norm_num at heq


/-- The real quadratic with a unit complex root and its conjugate. -/
theorem unit_quadratic {w : ℂ} (hw : ‖w‖ = 1) :
    1 + ((-2 * w.re : ℝ) : ℂ) * w + w ^ 2 = 0 := by
  have hc := Complex.normSq_eq_norm_sq w
  rw [Complex.normSq_apply, hw] at hc
  apply Complex.ext
  · simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, pow_two, Complex.zero_re]
    nlinarith only [hc]
  · simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, zero_add, add_zero, pow_two, Complex.zero_im]
    ring

/-- A quadratic error bound depending only on the norm of its argument. -/
theorem unit_quadratic_error {w v : ℂ} (hw : ‖w‖ = 1) {B : ℝ}
    (hB : ‖v‖ ≤ B) :
    ‖1 + ((-2 * w.re : ℝ) : ℂ) * v + v ^ 2 - 1‖ ≤ 2 * B + B ^ 2 := by
  have hc : ‖((-2 * w.re : ℝ) : ℂ)‖ ≤ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have h := Complex.abs_re_le_norm w
    rw [hw] at h
    norm_num only [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith only [h]
  rw [show 1 + ((-2 * w.re : ℝ) : ℂ) * v + v ^ 2 - 1 =
    ((-2 * w.re : ℝ) : ℂ) * v + v ^ 2 by ring]
  calc
    ‖((-2 * w.re : ℝ) : ℂ) * v + v ^ 2‖ ≤
      ‖((-2 * w.re : ℝ) : ℂ)‖ * ‖v‖ + ‖v‖ ^ 2 := by
        simpa only [norm_mul, norm_pow] using norm_add_le (((-2 * w.re : ℝ) : ℂ) * v) (v ^ (2 : ℕ))
    _ ≤ 2 * B + B ^ 2 := by gcongr

/-- The two prime bases. -/
def primeBase (i : Fin 2) : ℝ := if i = 0 then 2 else 3

/-- Evaluation as a finite Dirichlet polynomial supported on powers of two and three. -/
def dirichletEval (s : ℂ) : MvPolynomial (Fin 2) ℝ≥0 →+* ℂ :=
  MvPolynomial.eval₂Hom (Complex.ofRealHom.comp NNReal.toRealHom)
    (fun i => Complex.exp (-(Real.log (primeBase i) : ℂ) * s))

/-- Any nonreal point left of `Re s = 1` can be annihilated by a positive polynomial
arbitrarily close to one on the closed right half-plane. -/
theorem exists_single_annihilator (ρ : ℂ) (hρ : ρ.re < 1) (hi : ρ.im ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MvPolynomial (Fin 2) ℝ≥0,
      MvPolynomial.constantCoeff P = 1 ∧ dirichletEval ρ P = 0 ∧
      ∀ s : ℂ, 1 ≤ s.re → ‖dirichletEval s P - 1‖ < ε := by
  obtain ⟨i, hiw⟩ : ∃ i : Fin 2,
      Complex.exp (-(Real.log (primeBase i) : ℂ) * (ρ.im : ℂ) * I) ≠ 1 := by
    rcases two_three_phase_ne_one hi with h | h
    · exact ⟨0, by simpa only [primeBase, ↓reduceIte] using h⟩
    · exact ⟨1, by simpa [primeBase] using h⟩
  let L := Real.log (primeBase i)
  have hL : 0 < L := by
    apply Real.log_pos
    dsimp [primeBase]
    split_ifs <;> norm_num
  let w := Complex.exp (-(L : ℂ) * (ρ.im : ℂ) * I)
  have hw : ‖w‖ = 1 := by simp [w, Complex.norm_exp]
  let r := Real.exp (L * ρ.re)
  have hr : 0 < r := Real.exp_pos _
  let q := Real.exp (L * (ρ.re - 1))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (mul_neg_of_pos_of_neg hL (sub_neg.mpr hρ))
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have ht' : Tendsto (fun k : ℕ => 2 * q ^ k + (q ^ k) ^ 2) atTop (𝓝 0) := by
    simpa using (ht.const_mul 2).add (ht.pow 2)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ht'.eventually_lt_const hε)
  obtain ⟨k, hk, hkw⟩ := exists_large_pow_re_neg hw hiw (max N 1)
  have hk0 : k ≠ 0 := by omega
  let rnn : ℝ≥0 := ⟨r, hr.le⟩
  let cnn : ℝ≥0 := ⟨-2 * (w ^ k).re, by linarith only [hkw]⟩
  let V : MvPolynomial (Fin 2) ℝ≥0 := MvPolynomial.C rnn * MvPolynomial.X i
  let P : MvPolynomial (Fin 2) ℝ≥0 := 1 + MvPolynomial.C cnn * V ^ k + (V ^ k) ^ 2
  have heval (s : ℂ) : dirichletEval s P =
      1 + ((-2 * (w ^ k).re : ℝ) : ℂ) *
        ((r : ℂ) * Complex.exp (-(L : ℂ) * s)) ^ k +
      (((r : ℂ) * Complex.exp (-(L : ℂ) * s)) ^ k) ^ 2 := by
    simp only [P, V, dirichletEval, map_add, map_one, map_mul, map_pow,
      MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
    rfl
  have hroot : (r : ℂ) * Complex.exp (-(L : ℂ) * ρ) = w := by
    have hexp : (r : ℂ) = Complex.exp ((L * ρ.re : ℝ) : ℂ) := by simp [r]
    rw [hexp, ← Complex.exp_add]
    congr 1
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  refine ⟨P, ?_, ?_, ?_⟩
  · simp [P, V, hk0]
  · rw [heval, hroot]
    exact unit_quadratic (by rw [norm_pow, hw, one_pow])
  · intro s hs
    have hv : ‖(r : ℂ) * Complex.exp (-(L : ℂ) * s)‖ ≤ q := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, Complex.norm_exp]
      simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
        Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
      dsimp [r, q]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith only [hs, hL]
    have hvk : ‖((r : ℂ) * Complex.exp (-(L : ℂ) * s)) ^ k‖ ≤ q ^ k := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hv k
    rw [heval]
    exact (unit_quadratic_error (by rw [norm_pow, hw, one_pow]) hvk).trans_lt
      (hN k (le_trans (le_max_left _ _) hk))


/-- Finite products preserve positive coefficients and can retain any prescribed uniform
accuracy to the right of the line containing all prescribed roots. -/
theorem exists_finite_annihilator (F : Finset ℂ)
    (hF : ∀ ρ ∈ F, ρ.re < 1 ∧ ρ.im ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MvPolynomial (Fin 2) ℝ≥0,
      MvPolynomial.constantCoeff P = 1 ∧ (∀ ρ ∈ F, dirichletEval ρ P = 0) ∧
      ∀ s : ℂ, 1 ≤ s.re → ‖dirichletEval s P - 1‖ < ε := by
  classical
  induction F using Finset.induction_on generalizing ε with
  | empty =>
      refine ⟨1, by simp, by simp, ?_⟩
      intro s _
      simpa using hε
  | @insert ρ F hnot ih =>
      have hρ := hF ρ (Finset.mem_insert_self _ _)
      obtain ⟨Q, hQc, hQz, hQ⟩ := ih
        (fun z hz => hF z (Finset.mem_insert_of_mem hz)) (half_pos hε)
      have hden : 0 < 2 + ε := by linarith only [hε]
      obtain ⟨P, hPc, hPz, hP⟩ := exists_single_annihilator ρ hρ.1 hρ.2
        (div_pos hε hden)
      refine ⟨P * Q, ?_, ?_, ?_⟩
      · rw [map_mul, hPc, hQc, one_mul]
      · intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · rw [map_mul, hPz, zero_mul]
        · rw [map_mul, hQz z hz, mul_zero]
      · intro s hs
        have hq := hQ s hs
        have hp := hP s hs
        have hqn : ‖dirichletEval s Q‖ ≤ 1 + ε / 2 := by
          calc
            ‖dirichletEval s Q‖ = ‖(dirichletEval s Q - 1) + 1‖ := by rw [sub_add_cancel]
            _ ≤ ‖dirichletEval s Q - 1‖ + 1 := by simpa using norm_add_le (dirichletEval s Q - 1) 1
            _ ≤ 1 + ε / 2 := by linarith only [hq]
        have hC : 0 < 1 + ε / 2 := by linarith only [hε]
        rw [map_mul, show dirichletEval s P * dirichletEval s Q - 1 =
          (dirichletEval s P - 1) * dirichletEval s Q + (dirichletEval s Q - 1) by ring]
        calc
          ‖(dirichletEval s P - 1) * dirichletEval s Q + (dirichletEval s Q - 1)‖ ≤
              ‖dirichletEval s P - 1‖ * ‖dirichletEval s Q‖ + ‖dirichletEval s Q - 1‖ := by
            simpa only [norm_mul] using norm_add_le
              ((dirichletEval s P - 1) * dirichletEval s Q) (dirichletEval s Q - 1)
          _ ≤ ‖dirichletEval s P - 1‖ * (1 + ε / 2) + ‖dirichletEval s Q - 1‖ := by
            gcongr
          _ < (ε / (2 + ε)) * (1 + ε / 2) + ε / 2 :=
            add_lt_add (mul_lt_mul_of_pos_right hp hC) hq
          _ = ε := by field_simp; ring

/-- Every finite set of actual nontrivial zeta zeros admits a nonnegative finite Dirichlet
annihilator supported on `2^a 3^b`, with constant coefficient one and arbitrarily small uniform
error from one on `Re s ≥ 1`. No condition on the other zeros is required. -/
theorem exists_xi_zero_annihilator (F : Finset {ρ : ℂ // RHTower.xi ρ = 0})
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MvPolynomial (Fin 2) ℝ≥0,
      MvPolynomial.constantCoeff P = 1 ∧
      (∀ ρ ∈ F, dirichletEval (ρ : ℂ) P = 0) ∧
      ∀ s : ℂ, 1 ≤ s.re → ‖dirichletEval s P - 1‖ < ε := by
  classical
  have hF : ∀ ρ ∈ F.image Subtype.val, ρ.re < 1 ∧ ρ.im ≠ 0 := by
    intro ρ hρ
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hρ
    refine ⟨(RHTower.xi_zero_re_mem_open_unit q.property).2, ?_⟩
    intro hi
    have heq : (((q : ℂ).re : ℝ) : ℂ) = q := by
      apply Complex.ext
      · rfl
      · simpa only [Complex.ofReal_im] using hi.symm
    exact RHTower.xi_ne_zero_of_real (q : ℂ).re (by rw [heq]; exact q.property)
  obtain ⟨P, hPc, hPz, hP⟩ := exists_finite_annihilator (F.image Subtype.val) hF hε
  exact ⟨P, hPc, fun ρ hρ => hPz ρ (Finset.mem_image.mpr ⟨ρ, hρ, rfl⟩), hP⟩


/-- Finite Dirichlet polynomials are entire. -/
theorem differentiable_dirichletEval (P : MvPolynomial (Fin 2) ℝ≥0) :
    Differentiable ℂ (fun s => dirichletEval s P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      simpa only [dirichletEval, MvPolynomial.eval₂Hom_C] using
        (differentiable_const ((Complex.ofRealHom.comp NNReal.toRealHom) c))
  | add P Q hP hQ =>
      simp only [map_add]
      exact hP.add hQ
  | mul_X P i hP =>
      have hX : Differentiable ℂ (fun s => dirichletEval s (MvPolynomial.X i)) := by
        simp only [dirichletEval, MvPolynomial.eval₂Hom_X']
        fun_prop
      simp only [map_mul]
      exact hP.mul hX

/-- Arbitrary finite zero multiplicities can be imposed while retaining positive coefficients
and arbitrarily small uniform error from one on the closed right half-plane. -/
theorem exists_xi_zero_annihilator_with_multiplicities
    (F : Finset {ρ : ℂ // RHTower.xi ρ = 0})
    (m : {ρ : ℂ // RHTower.xi ρ = 0} → ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MvPolynomial (Fin 2) ℝ≥0,
      MvPolynomial.constantCoeff P = 1 ∧
      (∀ ρ ∈ F, dirichletEval (ρ : ℂ) P = 0 ∧
        (m ρ : ℕ∞) ≤ analyticOrderAt (fun s => dirichletEval s P) (ρ : ℂ)) ∧
      ∀ s : ℂ, 1 ≤ s.re → ‖dirichletEval s P - 1‖ < ε := by
  classical
  let M := F.sup m + 1
  have hc : ContinuousAt (fun z : ℂ => z ^ M) 1 := continuousAt_id.pow M
  obtain ⟨δ, hδ, hpow⟩ := Metric.continuousAt_iff.mp hc ε hε
  obtain ⟨Q, hQc, hQz, hQ⟩ := exists_xi_zero_annihilator F hδ
  have hfun : (fun s : ℂ => dirichletEval s (Q ^ M)) =
      (fun s : ℂ => dirichletEval s Q) ^ M := by
    funext s
    exact map_pow (dirichletEval s) Q M
  refine ⟨Q ^ M, by rw [map_pow, hQc, one_pow], ?_, ?_⟩
  · intro ρ hρ
    refine ⟨?_, ?_⟩
    · rw [map_pow, hQz ρ hρ]
      simp [M]
    · rw [hfun]
      have hm : m ρ ≤ M := (Finset.le_sup hρ).trans (Nat.le_succ _)
      have hm' : (m ρ : ℕ∞) ≤ (M : ℕ∞) := by exact_mod_cast hm
      exact hm'.trans
        (GaloisForLFunctions.RHTower.Matveev.natCast_le_analyticOrderAt_pow
          ((differentiable_dirichletEval Q).analyticAt (ρ : ℂ)) (hQz ρ hρ) M)
  · intro s hs
    rw [map_pow]
    have hnear : dist (dirichletEval s Q) 1 < δ := by
      simpa only [dist_eq_norm] using hQ s hs
    simpa only [one_pow, dist_eq_norm] using hpow hnear

end GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

#print axioms GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator.exists_xi_zero_annihilator_with_multiplicities
