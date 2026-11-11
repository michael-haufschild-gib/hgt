import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TwoVerticalLinesWeighTheZerosOfAFunctionOfOrderOne
import GaloisForLFunctions.RHTower.WeilLineIntegralAnyAbscissa
import Zeta23.ThmE.FullLineChiProof

/-!
# A function of order one with a functional equation has Weil's explicit formula

Let `E`, `Ẽ` be entire of order one with `E(1 − s) = W Ẽ(s)`, `W ≠ 0`, both without zeros on
`Re s > 1`, and suppose that on a line `Re s = c`, `1 < c ≤ 3/2`,

`E'/E = m (1/s + 1/(s − 1)) + G − Σ a(n) n^{−s}`,   `Ẽ'/Ẽ = m (1/s + 1/(s − 1)) + G − Σ ã(n) n^{−s}`,

with absolutely convergent Dirichlet series and `G` holomorphic on `Re s > 0` of logarithmic
growth on `1/2 ≤ Re s ≤ 3/2`. Then for a test `k ∈ C²_c` whose transform `H_k` decays to fourth
order on the strip, the zeros `ρ` of `E`, with multiplicity, satisfy

`Σ_ρ H_k(ρ) = m (H_k(0) + H_k(1)) + (1/2π) ∫ k̂(t) (G(½ + it) + G(½ − it)) dt
  − Σ_n n^{−1/2} (a(n) k(log n) + ã(n) k(−log n))`   (`hasSum_zeros_explicit`).

`E` need not be self-dual: this is the explicit formula of a completed `L`-function with
complex coefficients, with `m` the order of its pole and `G` the logarithmic derivative of its
conductor and Gamma factor.

**Proof.** The zeros are weighed by the two lines `Re s = c` and `Re s = 1 − c`. The functional
equation turns the left line into the right line of `Ẽ`. On the right line the pole pair is the
two-line residue identity, `G` moves to the critical line, and each Dirichlet series is a
Fourier inversion (corpus).
-/

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.EntireZeroDivisor
open Zeta23 Zeta23.WeilEF

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open RHTower.WeilLineIntegral

/-! ### A Dirichlet series on a line of absolute convergence -/

theorem continuous_LSeries_line {a : ℕ → ℂ} {c : ℝ} (ha : LSeriesSummable a c) :
    Continuous fun t : ℝ => LSeries a ((c : ℂ) + t * I) := by
  have hcont : ∀ n : ℕ, Continuous fun t : ℝ => LSeries.term a ((c : ℂ) + t * I) n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simpa [LSeries.term_zero] using continuous_const
    · simp only [LSeries.term_of_ne_zero hn]
      refine continuous_const.div ?_ fun t => ?_
      · exact Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hn))
      · exact cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hn))
  exact continuous_tsum hcont ha.norm fun n t => by
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp

/-- A function with the majorant `C/(1 + t²)` against a Dirichlet series on a line of absolute
convergence is integrable. -/
theorem integrable_mul_LSeries_line {φ : ℝ → ℂ} (hφc : Continuous φ) {Cφ : ℝ}
    (hφ : ∀ t : ℝ, ‖φ t‖ ≤ Cφ / (1 + t ^ 2)) {a : ℕ → ℂ} {c : ℝ} (ha : LSeriesSummable a c) :
    Integrable fun t : ℝ => φ t * LSeries a ((c : ℂ) + t * I) := by
  refine ((integrable_inv_one_add_sq.const_mul Cφ).mul_const
    (∑' n, ‖LSeries.term a c n‖)).mono' (hφc.mul (continuous_LSeries_line ha)).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [norm_mul]
  calc ‖φ t‖ * ‖LSeries a ((c : ℂ) + t * I)‖
      ≤ Cφ / (1 + t ^ 2) * ∑' n, ‖LSeries.term a c n‖ :=
        mul_le_mul (hφ t) (RHTower.WeilLineAnyAbscissa.norm_LSeries_line_le ha t) (norm_nonneg _)
          ((norm_nonneg _).trans (hφ t))
    _ = Cφ * (1 + t ^ 2)⁻¹ * ∑' n, ‖LSeries.term a c n‖ := by rw [div_eq_mul_inv]

/-- The pole pair at `0` is bounded and continuous on a line to the right of `1`. -/
theorem integrable_mul_gPair_zero_line {φ : ℝ → ℂ} (hφc : Continuous φ) {Cφ : ℝ}
    (hφ : ∀ t : ℝ, ‖φ t‖ ≤ Cφ / (1 + t ^ 2)) {c : ℝ} (hc1 : 1 < c) :
    Integrable fun t : ℝ => φ t * gPair 0 ((c : ℂ) + t * I) := by
  have hre : ∀ t : ℝ, ((c : ℂ) + t * I).re = c := fun t => by simp
  have hcont : Continuous fun t : ℝ => gPair 0 ((c : ℂ) + t * I) := by
    unfold gPair
    refine Continuous.add ?_ ?_
    · refine continuous_const.div (by fun_prop) fun t h => ?_
      have := congrArg Complex.re h
      simp at this
      linarith
    · refine continuous_const.div (by fun_prop) fun t h => ?_
      have := congrArg Complex.re h
      simp at this
      linarith
  have hbd : ∀ t : ℝ, ‖gPair 0 ((c : ℂ) + t * I)‖ ≤ 1 / c + 1 / (c - 1) := by
    intro t
    unfold gPair
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_div, norm_one, sub_zero]
      refine div_le_div_of_nonneg_left zero_le_one (by linarith) ?_
      have := Complex.abs_re_le_norm ((c : ℂ) + t * I)
      rw [hre, abs_of_pos (by linarith)] at this
      exact this
    · rw [norm_div, norm_one]
      refine div_le_div_of_nonneg_left zero_le_one (by linarith) ?_
      have := Complex.abs_re_le_norm ((c : ℂ) + t * I - (1 - 0))
      have hre' : ((c : ℂ) + t * I - (1 - 0)).re = c - 1 := by simp
      rw [hre', abs_of_pos (show (0 : ℝ) < c - 1 by linarith)] at this
      exact this
  refine ((integrable_inv_one_add_sq.const_mul Cφ).mul_const (1 / c + 1 / (c - 1))).mono'
    (hφc.mul hcont).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [norm_mul]
  calc ‖φ t‖ * ‖gPair 0 ((c : ℂ) + t * I)‖ ≤ Cφ / (1 + t ^ 2) * (1 / c + 1 / (c - 1)) :=
        mul_le_mul (hφ t) (hbd t) (norm_nonneg _) ((norm_nonneg _).trans (hφ t))
    _ = Cφ * (1 + t ^ 2)⁻¹ * (1 / c + 1 / (c - 1)) := by rw [div_eq_mul_inv]

/-! ### The explicit formula -/

/-- `E'/E(1 − s) = −Ẽ'/Ẽ(s)` under `E(1 − s) = W Ẽ(s)`. -/
theorem logDeriv_one_sub_of_dual {E E' : ℂ → ℂ} (hE : Differentiable ℂ E) {W : ℂ} (hW : W ≠ 0)
    (hFE : ∀ s, E (1 - s) = W * E' s) (s : ℂ) : logDeriv E (1 - s) = -logDeriv E' s := by
  have h1 : logDeriv (fun z => E (1 - z)) s = logDeriv E (1 - s) * (-1) := by
    have := logDeriv_comp (f := E) (g := fun z : ℂ => 1 - z) (x := s) (hE _)
      ((differentiableAt_const _).sub differentiableAt_id)
    simp only [Function.comp_def] at this
    rw [this]
    congr 1
    simp
  have h2 : logDeriv (fun z => E (1 - z)) s = logDeriv E' s := by
    rw [show (fun z => E (1 - z)) = fun z => W * E' z from funext hFE]
    exact logDeriv_const_mul s W hW
  rw [h2] at h1
  linear_combination h1

/-- **Weil's explicit formula for a function of order one with a functional equation.** -/
theorem hasSum_zeros_explicit {E E' : ℂ → ℂ} (hE : Differentiable ℂ E) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ s : ℂ, ‖E s‖ ≤ Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)))
    {W : ℂ} (hW : W ≠ 0) (hFE : ∀ s, E (1 - s) = W * E' s)
    (hne : ∀ s : ℂ, 1 < s.re → E s ≠ 0) (hne' : ∀ s : ℂ, 1 < s.re → E' s ≠ 0)
    {m : ℂ} {G : ℂ → ℂ} {a a' : ℕ → ℂ}
    (hGd : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ G s)
    (hGg : ∃ CG : ℝ, 0 < CG ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 2 →
      ‖G (σ + t * I)‖ ≤ CG * Real.log (2 + |t|))
    {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3 / 2)
    (ha : LSeriesSummable a c) (ha' : LSeriesSummable a' c)
    (hlog : ∀ t : ℝ, logDeriv E (c + t * I) =
      m * gPair 0 (c + t * I) + G (c + t * I) - LSeries a (c + t * I))
    (hlog' : ∀ t : ℝ, logDeriv E' (c + t * I) =
      m * gPair 0 (c + t * I) + G (c + t * I) - LSeries a' (c + t * I))
    {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) {D : ℝ}
    (hD : ∀ σ t : ℝ, -1 ≤ σ → σ ≤ 2 → ‖Hfn k (σ + t * I)‖ ≤ D / (1 + t ^ 2) ^ 2) :
    HasSum (fun q : ZeroCopy (fun z => E (z + 2)) => Hfn k (zeroOf E q))
      (m * (Hfn k 0 + Hfn k 1) +
        (1 / (2 * Real.pi) : ℂ) *
          (∫ t : ℝ, paperFT k t * (G (1 / 2 + t * I) + G (1 / 2 - t * I))) -
        ∑' n : ℕ, a n / Real.sqrt n * k (Real.log n) -
        ∑' n : ℕ, a' n / Real.sqrt n * k (-Real.log n)) := by
  -- the zeros lie in the closed strip
  have hstrip : ∀ s, E s = 0 → 0 ≤ s.re ∧ s.re ≤ 1 := by
    intro s hs
    constructor
    · by_contra h
      have h1 : 1 < (1 - s).re := by
        simp only [Complex.sub_re, Complex.one_re]
        linarith [not_le.mp h]
      have h2 := hFE (1 - s)
      rw [sub_sub_cancel] at h2
      rw [h2] at hs
      exact hne' _ h1 ((mul_eq_zero.mp hs).resolve_left hW)
    · by_contra h
      exact hne s (not_le.mp h) hs
  have hH : Differentiable ℂ (Hfn k) := differentiable_Hfn hk hkc
  obtain ⟨hiR, hiL, hsum⟩ := hasSum_zeros_two_lines hE hC hbound (hne 2 (by norm_num)) hstrip hH
    hD hc1 (by linarith)
  have hD0 : 0 ≤ D := by
    have h := (norm_nonneg _).trans (hD 0 0 (by norm_num) (by norm_num))
    simpa using h
  have hD1 : ∀ σ t : ℝ, -1 ≤ σ → σ ≤ 2 → ‖Hfn k (σ + t * I)‖ ≤ D / (1 + t ^ 2) := by
    intro σ t h1 h2
    refine (hD σ t h1 h2).trans ?_
    have ht : (1 : ℝ) ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
    exact div_le_div_of_nonneg_left hD0 (by positivity) (by nlinarith)
  -- the mirror test
  have hkn2 : ContDiff ℝ 2 fun u => k (-u) := hk.comp contDiff_neg
  have hknc : HasCompactSupport fun u => k (-u) := hkc.comp_homeomorph (Homeomorph.neg ℝ)
  have hFm : ∀ t : ℝ, Hfn k (1 - c - t * I) = Hfn (fun u => k (-u)) (c + t * I) :=
    fun t => Hfn_mirror k c t
  have hb1 : ∀ t : ℝ, ‖Hfn k (c + t * I)‖ ≤ D / (1 + t ^ 2) := fun t =>
    hD1 c t (by linarith) (by linarith)
  have hb2 : ∀ t : ℝ, ‖Hfn (fun u => k (-u)) (c + t * I)‖ ≤ D / (1 + t ^ 2) := fun t => by
    rw [← hFm]
    have e : (1 : ℂ) - c - t * I = ((1 - c : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by
      push_cast
      ring
    have h := hD1 (1 - c) (-t) (by linarith) (by linarith)
    rw [neg_sq] at h
    rw [e]
    exact h
  have hcn1 := continuous_Hfn_line hk hkc c
  have hcn2 := continuous_Hfn_line hkn2 hknc c
  -- the left line through the dual function
  have hpt : ∀ t : ℝ, Hfn k (((1 - c : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) *
      logDeriv E (((1 - c : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) =
      -(Hfn (fun u => k (-u)) (c + t * I) * logDeriv E' (c + t * I)) := by
    intro t
    have e1 : ((1 - c : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I = 1 - c - t * I := by
      push_cast
      ring
    have e2 : (1 : ℂ) - c - t * I = 1 - ((c : ℂ) + t * I) := by ring
    rw [e1, hFm, e2, logDeriv_one_sub_of_dual hE hW hFE]
    ring
  have hleft : (∫ t : ℝ, Hfn k ((1 - c : ℝ) + t * I) * logDeriv E ((1 - c : ℝ) + t * I)) =
      -∫ t : ℝ, Hfn (fun u => k (-u)) (c + t * I) * logDeriv E' (c + t * I) := by
    have h1 := integral_neg_eq_self
      (fun t : ℝ => Hfn k ((1 - c : ℝ) + t * I) * logDeriv E ((1 - c : ℝ) + t * I)) volume
    rw [← h1, ← integral_neg]
    exact integral_congr_ae (Eventually.of_forall hpt)
  have hiL' : Integrable fun t : ℝ =>
      Hfn (fun u => k (-u)) (c + t * I) * logDeriv E' (c + t * I) := by
    refine (hiL.comp_neg.neg).congr (Eventually.of_forall fun t => ?_)
    show -(Hfn k (((1 - c : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) *
      logDeriv E (((1 - c : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)) = _
    rw [hpt t, neg_neg]
  -- the pieces on the right line
  have hFc : Continuous fun t : ℝ => Hfn k (c + t * I) + Hfn (fun u => k (-u)) (c + t * I) :=
    hcn1.add hcn2
  have hFb : ∀ t : ℝ, ‖Hfn k (c + t * I) + Hfn (fun u => k (-u)) (c + t * I)‖ ≤
      (D + D) / (1 + t ^ 2) := fun t => by
    refine (norm_add_le _ _).trans ?_
    rw [add_div]
    exact add_le_add (hb1 t) (hb2 t)
  have hiA : Integrable fun t : ℝ =>
      (Hfn k (c + t * I) + Hfn (fun u => k (-u)) (c + t * I)) * gPair 0 (c + t * I) :=
    integrable_mul_gPair_zero_line hFc hFb hc1
  have hiB : Integrable fun t : ℝ => Hfn k (c + t * I) * LSeries a (c + t * I) :=
    integrable_mul_LSeries_line hcn1 hb1 ha
  have hiB' : Integrable fun t : ℝ =>
      Hfn (fun u => k (-u)) (c + t * I) * LSeries a' (c + t * I) :=
    integrable_mul_LSeries_line hcn2 hb2 ha'
  have hiT : Integrable fun t : ℝ => Hfn k (c + t * I) * logDeriv E (c + t * I) +
      Hfn (fun u => k (-u)) (c + t * I) * logDeriv E' (c + t * I) := hiR.add hiL'
  have hmA : Integrable fun t : ℝ =>
      m * ((Hfn k (c + t * I) + Hfn (fun u => k (-u)) (c + t * I)) * gPair 0 (c + t * I)) :=
    hiA.const_mul m
  have hTeq : ∀ t : ℝ, (Hfn k (c + t * I) + Hfn (fun u => k (-u)) (c + t * I)) * G (c + t * I) =
      Hfn k (c + t * I) * logDeriv E (c + t * I) +
          Hfn (fun u => k (-u)) (c + t * I) * logDeriv E' (c + t * I) -
        m * ((Hfn k (c + t * I) + Hfn (fun u => k (-u)) (c + t * I)) * gPair 0 (c + t * I)) +
        Hfn k (c + t * I) * LSeries a (c + t * I) +
        Hfn (fun u => k (-u)) (c + t * I) * LSeries a' (c + t * I) := fun t => by
    rw [hlog t, hlog' t]
    ring
  have hi1 : Integrable fun t : ℝ => Hfn k (c + t * I) * logDeriv E (c + t * I) +
        Hfn (fun u => k (-u)) (c + t * I) * logDeriv E' (c + t * I) -
      m * ((Hfn k (c + t * I) + Hfn (fun u => k (-u)) (c + t * I)) * gPair 0 (c + t * I)) :=
    hiT.sub hmA
  have hi2 : Integrable fun t : ℝ => Hfn k (c + t * I) * logDeriv E (c + t * I) +
        Hfn (fun u => k (-u)) (c + t * I) * logDeriv E' (c + t * I) -
      m * ((Hfn k (c + t * I) + Hfn (fun u => k (-u)) (c + t * I)) * gPair 0 (c + t * I)) +
      Hfn k (c + t * I) * LSeries a (c + t * I) := hi1.add hiB
  -- the integral of the factor `G` through the other integrals
  have hGint : (∫ t : ℝ, (Hfn k (c + t * I) + Hfn (fun u => k (-u)) (c + t * I)) *
        G (c + t * I)) =
      (∫ t : ℝ, Hfn k (c + t * I) * logDeriv E (c + t * I)) +
          (∫ t : ℝ, Hfn (fun u => k (-u)) (c + t * I) * logDeriv E' (c + t * I)) -
        m * (∫ t : ℝ, (Hfn k (c + t * I) + Hfn (fun u => k (-u)) (c + t * I)) *
          gPair 0 (c + t * I)) +
        (∫ t : ℝ, Hfn k (c + t * I) * LSeries a (c + t * I)) +
        ∫ t : ℝ, Hfn (fun u => k (-u)) (c + t * I) * LSeries a' (c + t * I) := by
    rw [integral_congr_ae (Eventually.of_forall hTeq), integral_add hi2 hiB',
      integral_add hi1 hiB, integral_sub hiT hmA, integral_add hiR hiL', integral_const_mul]
  -- the three evaluations
  have hC' : ∀ σ t : ℝ, 1 - c ≤ σ → σ ≤ c → ‖Hfn k (σ + t * I)‖ ≤ D / (1 + t ^ 2) :=
    fun σ t h1 h2 => hD1 σ t (by linarith) (by linarith)
  have hA := two_line_pair hH hC' (z₀ := 0) (by rw [Complex.zero_re]; linarith)
    (by rw [Complex.zero_re]; linarith)
  have hGs := Zeta23.ThmE.line_shift_generic hGd hGg hk hkc hc1 hc2
  simp only [hFm] at hA hGs
  rw [sub_zero] at hA
  have hB := (hasSum_prime_side_line hk hkc ha).tsum_eq
  have hB' := (hasSum_prime_side_line hkn2 hknc ha').tsum_eq
  have hval : (1 / (2 * Real.pi) : ℂ) *
        ((∫ t : ℝ, Hfn k (c + t * I) * logDeriv E (c + t * I)) -
          ∫ t : ℝ, Hfn k ((1 - c : ℝ) + t * I) * logDeriv E ((1 - c : ℝ) + t * I)) =
      m * (Hfn k 0 + Hfn k 1) +
        (1 / (2 * Real.pi) : ℂ) *
          (∫ t : ℝ, paperFT k t * (G (1 / 2 + t * I) + G (1 / 2 - t * I))) -
        ∑' n : ℕ, a n / Real.sqrt n * k (Real.log n) -
        ∑' n : ℕ, a' n / Real.sqrt n * k (-Real.log n) := by
    rw [hleft, hB, hB', ← hGs, hGint, ← hA]
    ring
  rw [← hval]
  exact hsum

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
