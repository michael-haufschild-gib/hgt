import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Periodic patterns cannot satisfy their last lag

A periodic pattern of period `Ng`, with one FE orbit of scaled depth `x_r ≥ 0` and real weight
`w_r` per residue `r < N`, has the lag symbol `D(m) = Σ_r w_r cosh(m x_r) ω^{rm}`, `ω = e^{2πi/N}`.
With `ℓ = 2π/(Ng)` a window of aperture `a` sees the lags `|m|ℓ < 2a`, and two patterns are mimics exactly when
the symbol of their difference vanishes there. This file proves that the symbol of a nonzero
pattern cannot vanish at all `|m| ≤ N − 1` (`eq_zero_of_lagSymbol_eq_zero`). So period-`N`
patterns never hide above `(N − 1)π/(Ng)`, and the period-`6` patterns of
`MixedDepthsHideBeyondTheInghamScale` hide exactly up to `5π/(6g)`.

The proof is a partial-fraction argument on the `2N` nodes `e^{±x_r}ω^r`.
* **The numerator is a monomial** (`lagNumerator_eq_monomial`). With `P = Π_r q_r`,
  `q_r = (X − e^{x_r}ω^r)(X − e^{−x_r}ω^r)`, the numerator `T = Σ_r (w_r/2)(P/(X − a_r) + P/(X − b_r))`
  has its coefficients above `N − 1` given by the positive moments and below by the negative
  moments (`coeff_lagNumerator_high`, `coeff_lagNumerator_low`). Both vanish, so `T = κ X^{N−1}`.
* **On the unit circle** (`eval_lagNumerator_circle`). `q_s(e^{iφ}) = −2e^{iφ}ω^s D_s(φ)` with
  `D_s(φ) = cosh x_s − cos(φ − θ_s)`, so `κ` is a fixed multiple of the Wronskian
  `G(φ) = Σ_r w_r sin(φ − θ_r) Π_{s≠r} D_s(φ)` at every angle (`lagNumerator_coeff_eq`).
* **The Wronskian vanishes** (`lagWronskian_eq_zero`). A node on the line kills `G` at its angle.
  Otherwise `Ψ = Σ_r w_r log D_r` is `2π`-periodic with `Ψ' = G/Π_s D_s`, and Rolle's theorem
  finds a zero. So `T = 0`, and evaluating `T` at each node (or dividing by `X − ω^r` at a node on
  the line) gives `w = 0`.
-/

open Polynomial Finset
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-! ### Nodes of a period pattern -/

/-- `ω = e^{2πi/N}`. -/
def lagRoot (N : ℕ) : ℂ := Complex.exp (2 * π * Complex.I / N)

/-- The outer node `e^{x} ω^r` of residue `r`. -/
def lagOuter (N : ℕ) (x : ℝ) (r : ℕ) : ℂ := (Real.exp x : ℂ) * lagRoot N ^ r

/-- The inner node `e^{−x} ω^r` of residue `r`. -/
def lagInner (N : ℕ) (x : ℝ) (r : ℕ) : ℂ := (Real.exp (-x) : ℂ) * lagRoot N ^ r

/-- The quadratic `(X − e^{x}ω^r)(X − e^{−x}ω^r)` of residue `r`. -/
def lagQuad (N : ℕ) (x : ℝ) (r : ℕ) : ℂ[X] :=
  (X - C (lagOuter N x r)) * (X - C (lagInner N x r))

/-- The node polynomial `P = Π_r q_r` of degree `2N`. -/
def lagNodePoly {N : ℕ} (x : Fin N → ℝ) : ℂ[X] := ∏ r : Fin N, lagQuad N (x r) r

/-- The positive moments `Σ_r (w_r/2)(a_r^m + b_r^m)`. -/
def lagPosMoment {N : ℕ} (x w : Fin N → ℝ) (m : ℕ) : ℂ :=
  ∑ r : Fin N, ((w r : ℂ) / 2) * (lagOuter N (x r) r ^ m + lagInner N (x r) r ^ m)

/-- The negative moments `Σ_r (w_r/2)(a_r^{−m} + b_r^{−m})`. -/
def lagNegMoment {N : ℕ} (x w : Fin N → ℝ) (m : ℕ) : ℂ :=
  ∑ r : Fin N, ((w r : ℂ) / 2) * ((lagOuter N (x r) r ^ m)⁻¹ + (lagInner N (x r) r ^ m)⁻¹)

/-- The partial-fraction numerator `T = Σ_r (w_r/2)(P/(X − a_r) + P/(X − b_r))`. -/
def lagNumerator {N : ℕ} (x w : Fin N → ℝ) : ℂ[X] :=
  ∑ r : Fin N, C ((w r : ℂ) / 2) *
    (lagNodePoly x /ₘ (X - C (lagOuter N (x r) r)) + lagNodePoly x /ₘ (X - C (lagInner N (x r) r)))

theorem norm_lagRoot (N : ℕ) : ‖lagRoot N‖ = 1 := by
  rw [lagRoot, show 2 * π * Complex.I / N = ((2 * π / N : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

theorem lagRoot_pow_inv (N n : ℕ) : (lagRoot N ^ n)⁻¹ = conj (lagRoot N ^ n) := by
  have h : lagRoot N ^ n * conj (lagRoot N ^ n) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow, norm_lagRoot]
    simp
  exact inv_eq_of_mul_eq_one_right h

theorem lagOuter_ne_zero (N : ℕ) (x : ℝ) (r : ℕ) : lagOuter N x r ≠ 0 := by
  have h : lagRoot N ≠ 0 := Complex.exp_ne_zero _
  simp [lagOuter, h]

theorem lagInner_ne_zero (N : ℕ) (x : ℝ) (r : ℕ) : lagInner N x r ≠ 0 := by
  have h : lagRoot N ≠ 0 := Complex.exp_ne_zero _
  simp [lagInner, h]

theorem node_pow_add (N : ℕ) (x : ℝ) (r m : ℕ) :
    lagOuter N x r ^ m + lagInner N x r ^ m =
      ((2 * Real.cosh (m * x) : ℝ) : ℂ) * lagRoot N ^ (r * m) := by
  simp only [lagOuter, lagInner, mul_pow, ← pow_mul]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul,
    Real.cosh_eq]
  push_cast
  ring_nf

theorem node_pow_inv_add (N : ℕ) (x : ℝ) (r m : ℕ) :
    (lagOuter N x r ^ m)⁻¹ + (lagInner N x r ^ m)⁻¹ =
      ((2 * Real.cosh (m * x) : ℝ) : ℂ) * conj (lagRoot N ^ (r * m)) := by
  simp only [lagOuter, lagInner, mul_pow, ← pow_mul, mul_inv]
  rw [lagRoot_pow_inv, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Real.exp_nat_mul,
    ← Real.exp_nat_mul, ← Complex.ofReal_inv, ← Complex.ofReal_inv, ← Real.exp_neg,
    ← Real.exp_neg, Real.cosh_eq]
  push_cast
  ring_nf

/-- The lag symbol vanishing at `m < N` kills the moments of every order `< N`. -/
theorem moments_eq_zero {N : ℕ} {x w : Fin N → ℝ}
    (hsym : ∀ m : ℕ, m < N →
      ∑ r : Fin N, (w r : ℂ) * (Real.cosh (m * x r) : ℂ) * lagRoot N ^ ((r : ℕ) * m) = 0)
    {m : ℕ} (hm : m < N) : lagPosMoment x w m = 0 ∧ lagNegMoment x w m = 0 := by
  constructor
  · rw [lagPosMoment, ← hsym m hm]
    refine sum_congr rfl fun r _ => ?_
    rw [node_pow_add]
    push_cast
    ring
  · have h := congrArg conj (hsym m hm)
    rw [map_zero, map_sum] at h
    rw [lagNegMoment, ← h]
    refine sum_congr rfl fun r _ => ?_
    rw [node_pow_inv_add]
    simp only [map_mul, Complex.conj_ofReal]
    push_cast
    ring

/-! ### The numerator is a monomial -/

/-- Below the division point: at a root `ζ`, `[X^k](p/(X − ζ)) · ζ^{k+1} = −Σ_{i ≤ k} p_i ζ^i`. -/
theorem coeff_divByMonic_mul_pow_of_root {p : ℂ[X]} {ζ : ℂ} (hζ : p.IsRoot ζ) (k : ℕ) :
    (p /ₘ (X - C ζ)).coeff k * ζ ^ (k + 1) = -∑ i ∈ range (k + 1), p.coeff i * ζ ^ i := by
  set q := p /ₘ (X - C ζ) with hq
  have hp : q * (X - C ζ) = p := by rw [mul_comm]; exact mul_divByMonic_eq_iff_isRoot.mpr hζ
  induction k with
  | zero =>
    have h0 : p.coeff 0 = q.coeff 0 * -ζ := by rw [← hp, mul_coeff_zero]; simp
    rw [sum_range_one, h0]
    ring
  | succ k ih =>
    have h1 : p.coeff (k + 1) = q.coeff k - q.coeff (k + 1) * ζ := by
      rw [← hp, coeff_mul_X_sub_C]
    rw [sum_range_succ]
    linear_combination ih + ζ ^ (k + 1) * h1

theorem coeff_divByMonic_of_root {p : ℂ[X]} {ζ : ℂ} (hζ : p.IsRoot ζ) (hζ0 : ζ ≠ 0) (k : ℕ) :
    (p /ₘ (X - C ζ)).coeff k = -∑ i ∈ range (k + 1), p.coeff i * (ζ ^ (k + 1 - i))⁻¹ := by
  have h := coeff_divByMonic_mul_pow_of_root hζ k
  have hpow : ζ ^ (k + 1) ≠ 0 := pow_ne_zero _ hζ0
  rw [← eq_div_iff hpow] at h
  rw [h, neg_div, div_eq_mul_inv, sum_mul]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  have hik : i ≤ k + 1 := by have := mem_range.mp hi; omega
  rw [show ζ ^ (k + 1) = ζ ^ i * ζ ^ (k + 1 - i) by rw [← pow_add, Nat.add_sub_cancel' hik]]
  field_simp

theorem lagQuad_monic (N : ℕ) (x : ℝ) (r : ℕ) : (lagQuad N x r).Monic :=
  (monic_X_sub_C _).mul (monic_X_sub_C _)

theorem lagNodePoly_monic {N : ℕ} (x : Fin N → ℝ) : (lagNodePoly x).Monic :=
  monic_prod_of_monic _ _ fun _ _ => lagQuad_monic _ _ _

theorem natDegree_lagNodePoly {N : ℕ} (x : Fin N → ℝ) : (lagNodePoly x).natDegree = 2 * N := by
  rw [lagNodePoly, natDegree_prod_of_monic _ _ fun _ _ => lagQuad_monic _ _ _]
  have h : ∀ r : Fin N, (lagQuad N (x r) r).natDegree = 2 := fun r => by
    rw [lagQuad, (monic_X_sub_C _).natDegree_mul (monic_X_sub_C _)]
    simp
  simp [h, mul_comm]

theorem lagNodePoly_isRoot_outer {N : ℕ} (x : Fin N → ℝ) (r : Fin N) :
    (lagNodePoly x).IsRoot (lagOuter N (x r) r) := by
  rw [IsRoot, lagNodePoly, eval_prod]
  exact prod_eq_zero (mem_univ r) (by simp [lagQuad])

theorem lagNodePoly_isRoot_inner {N : ℕ} (x : Fin N → ℝ) (r : Fin N) :
    (lagNodePoly x).IsRoot (lagInner N (x r) r) := by
  rw [IsRoot, lagNodePoly, eval_prod]
  exact prod_eq_zero (mem_univ r) (by simp [lagQuad])

theorem coeff_lagNumerator {N : ℕ} (x w : Fin N → ℝ) (k : ℕ) :
    (lagNumerator x w).coeff k = ∑ r : Fin N, ((w r : ℂ) / 2) *
      ((lagNodePoly x /ₘ (X - C (lagOuter N (x r) r))).coeff k +
        (lagNodePoly x /ₘ (X - C (lagInner N (x r) r))).coeff k) := by
  simp [lagNumerator, coeff_C_mul]

/-- Above `N − 1` the coefficients of `T` are positive moments of order `< N`. -/
theorem coeff_lagNumerator_high {N : ℕ} (x w : Fin N → ℝ) (k : ℕ) :
    (lagNumerator x w).coeff k =
      ∑ i ∈ Icc (k + 1) (2 * N), (lagNodePoly x).coeff i * lagPosMoment x w (i - (k + 1)) := by
  rw [coeff_lagNumerator]
  simp only [coeff_divByMonic_X_sub_C, natDegree_lagNodePoly]
  have e : ∀ r : Fin N, ((w r : ℂ) / 2) *
      (∑ i ∈ Icc (k + 1) (2 * N), lagOuter N (x r) r ^ (i - (k + 1)) * (lagNodePoly x).coeff i +
        ∑ i ∈ Icc (k + 1) (2 * N), lagInner N (x r) r ^ (i - (k + 1)) * (lagNodePoly x).coeff i) =
      ∑ i ∈ Icc (k + 1) (2 * N), (lagNodePoly x).coeff i * (((w r : ℂ) / 2) *
        (lagOuter N (x r) r ^ (i - (k + 1)) + lagInner N (x r) r ^ (i - (k + 1)))) :=
    fun r => by
      rw [← sum_add_distrib, mul_sum]
      exact sum_congr rfl fun i _ => by ring
  rw [sum_congr rfl fun r _ => e r, sum_comm]
  exact sum_congr rfl fun i _ => by rw [lagPosMoment, mul_sum]

/-- Below `N − 1` the coefficients of `T` are negative moments of order `≤ k + 1`. -/
theorem coeff_lagNumerator_low {N : ℕ} (x w : Fin N → ℝ) (k : ℕ) :
    (lagNumerator x w).coeff k =
      -∑ i ∈ range (k + 1), (lagNodePoly x).coeff i * lagNegMoment x w (k + 1 - i) := by
  rw [coeff_lagNumerator]
  simp only [coeff_divByMonic_of_root (lagNodePoly_isRoot_outer x _) (lagOuter_ne_zero _ _ _),
    coeff_divByMonic_of_root (lagNodePoly_isRoot_inner x _) (lagInner_ne_zero _ _ _)]
  have e : ∀ r : Fin N, ((w r : ℂ) / 2) *
      (-∑ i ∈ range (k + 1), (lagNodePoly x).coeff i * (lagOuter N (x r) r ^ (k + 1 - i))⁻¹ +
        -∑ i ∈ range (k + 1), (lagNodePoly x).coeff i * (lagInner N (x r) r ^ (k + 1 - i))⁻¹) =
      -∑ i ∈ range (k + 1), (lagNodePoly x).coeff i * (((w r : ℂ) / 2) *
        ((lagOuter N (x r) r ^ (k + 1 - i))⁻¹ + (lagInner N (x r) r ^ (k + 1 - i))⁻¹)) :=
    fun r => by
      rw [← neg_add, ← sum_add_distrib, mul_neg, mul_sum]
      exact congrArg _ (sum_congr rfl fun i _ => by ring)
  rw [sum_congr rfl fun r _ => e r, sum_neg_distrib, sum_comm]
  exact congrArg _ (sum_congr rfl fun i _ => by rw [lagNegMoment, mul_sum])

/-- **The numerator is a monomial.** If the lag symbol vanishes at `m < N`, then
`T = κ X^{N−1}`. -/
theorem lagNumerator_eq_monomial {N : ℕ} {x w : Fin N → ℝ}
    (hsym : ∀ m : ℕ, m < N →
      ∑ r : Fin N, (w r : ℂ) * (Real.cosh (m * x r) : ℂ) * lagRoot N ^ ((r : ℕ) * m) = 0) :
    lagNumerator x w = C ((lagNumerator x w).coeff (N - 1)) * X ^ (N - 1) := by
  ext k
  rw [coeff_C_mul_X_pow]
  split_ifs with hk
  · rw [hk]
  · rcases lt_or_gt_of_ne hk with hlt | hgt
    · rw [coeff_lagNumerator_low]
      refine neg_eq_zero.mpr (sum_eq_zero fun i hi => ?_)
      have hi' := mem_range.mp hi
      rw [(moments_eq_zero hsym (by omega)).2, mul_zero]
    · rw [coeff_lagNumerator_high]
      refine sum_eq_zero fun i hi => ?_
      have hi' := mem_Icc.mp hi
      rw [(moments_eq_zero hsym (by omega)).1, mul_zero]

/-! ### The residue form -/

/-- `T = Σ_r w_r (X − cosh(x_r) ω^r) Π_{s≠r} q_s`. -/
theorem lagNumerator_eq_residue {N : ℕ} (x w : Fin N → ℝ) :
    lagNumerator x w = ∑ r : Fin N, C (w r : ℂ) *
      ((X - C ((Real.cosh (x r) : ℂ) * lagRoot N ^ (r : ℕ))) *
        ∏ s ∈ univ.erase r, lagQuad N (x s) s) := by
  unfold lagNumerator
  refine sum_congr rfl fun r _ => ?_
  set Q := ∏ s ∈ univ.erase r, lagQuad N (x s) s with hQ
  have hP : lagNodePoly x = (X - C (lagOuter N (x r) r)) * ((X - C (lagInner N (x r) r)) * Q) := by
    rw [lagNodePoly, ← mul_prod_erase univ _ (mem_univ r), lagQuad, mul_assoc]
  have hP' : lagNodePoly x = (X - C (lagInner N (x r) r)) * ((X - C (lagOuter N (x r) r)) * Q) := by
    rw [hP]; ring
  have ha : lagNodePoly x /ₘ (X - C (lagOuter N (x r) r)) = (X - C (lagInner N (x r) r)) * Q := by
    rw [hP, mul_divByMonic_cancel_left _ (monic_X_sub_C _)]
  have hb : lagNodePoly x /ₘ (X - C (lagInner N (x r) r)) = (X - C (lagOuter N (x r) r)) * Q := by
    rw [hP', mul_divByMonic_cancel_left _ (monic_X_sub_C _)]
  have hsum : C (lagOuter N (x r) r) = C 2 * C ((Real.cosh (x r) : ℂ) * lagRoot N ^ (r : ℕ)) -
      C (lagInner N (x r) r) := by
    rw [← C_mul, ← C_sub]
    congr 1
    simp only [lagOuter, lagInner, Real.cosh_eq]
    push_cast
    ring
  have h2 : (C (2 : ℂ) : ℂ[X]) = 2 := map_ofNat C 2
  have hw : C ((w r : ℂ) / 2) * C 2 = C (w r : ℂ) := by
    rw [← C_mul, div_mul_cancel₀ _ two_ne_zero]
  rw [ha, hb, hsum, ← hw, h2]
  ring

theorem lagRoot_pow_eq_exp (N r : ℕ) :
    lagRoot N ^ r = Complex.exp (((2 * π * r / N : ℝ) : ℂ) * Complex.I) := by
  rw [lagRoot, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `q_s(e^{iφ}) = −2 e^{iφ} ω^s (cosh x − cos(φ − θ_s))`, `θ_s = 2πs/N`. -/
theorem eval_lagQuad_circle (N : ℕ) (x : ℝ) (s : ℕ) (φ : ℝ) :
    (lagQuad N x s).eval (Complex.exp (φ * Complex.I)) =
      -2 * Complex.exp (φ * Complex.I) * lagRoot N ^ s *
        ((Real.cosh x - Real.cos (φ - 2 * π * s / N) : ℝ) : ℂ) := by
  set θ : ℝ := 2 * π * s / N with hθ
  have hv : lagRoot N ^ s = Complex.exp (θ * Complex.I) := lagRoot_pow_eq_exp N s
  set u := Complex.exp (φ * Complex.I) with hu
  set v := Complex.exp (θ * Complex.I) with hvdef
  have hu0 : u ≠ 0 := Complex.exp_ne_zero _
  have hv0 : v ≠ 0 := Complex.exp_ne_zero _
  have hcos : (2 : ℂ) * (Real.cos (φ - θ) : ℂ) = u / v + v / u := by
    rw [Complex.ofReal_cos, Complex.two_cos]
    push_cast
    rw [sub_mul, Complex.exp_sub, neg_sub, sub_mul, Complex.exp_sub]
  have hcos' : 2 * (u * v) * (Real.cos (φ - θ) : ℂ) = u ^ 2 + v ^ 2 := by
    rw [mul_comm 2, mul_assoc, hcos]
    field_simp
  have hcosh : (2 : ℂ) * (Real.cosh x : ℂ) = (Real.exp x : ℂ) + (Real.exp (-x) : ℂ) := by
    rw [Real.cosh_eq]; push_cast; ring
  have hE : (Real.exp x : ℂ) * (Real.exp (-x) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  simp only [lagQuad, lagOuter, lagInner, eval_mul, eval_sub, eval_X, eval_C, hv]
  rw [Complex.ofReal_sub]
  linear_combination (u * v) * hcosh + v ^ 2 * hE - hcos'

/-- `e^{iφ} − cosh(x) ω^r = ω^r (−(cosh x − cos(φ − θ_r)) + i sin(φ − θ_r))`. -/
theorem circle_sub_centre (N : ℕ) (x : ℝ) (r : ℕ) (φ : ℝ) :
    Complex.exp (φ * Complex.I) - (Real.cosh x : ℂ) * lagRoot N ^ r =
      lagRoot N ^ r * (-((Real.cosh x - Real.cos (φ - 2 * π * r / N) : ℝ) : ℂ) +
        Complex.I * (Real.sin (φ - 2 * π * r / N) : ℂ)) := by
  rw [lagRoot_pow_eq_exp]
  have h : Complex.exp (φ * Complex.I) = Complex.exp (((2 * π * r / N : ℝ) : ℂ) * Complex.I) *
      ((Real.cos (φ - 2 * π * r / N) : ℂ) + (Real.sin (φ - 2 * π * r / N) : ℂ) * Complex.I) := by
    rw [Complex.ofReal_cos, Complex.ofReal_sin, ← Complex.exp_mul_I, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h]
  push_cast
  ring

/-- The depth profile `D_r(φ) = cosh x_r − cos(φ − θ_r)`. -/
def lagDepth {N : ℕ} (x : Fin N → ℝ) (r : Fin N) (φ : ℝ) : ℝ :=
  Real.cosh (x r) - Real.cos (φ - 2 * π * (r : ℕ) / N)

/-- `G(φ) = Σ_r w_r sin(φ − θ_r) Π_{s≠r} D_s(φ)`. -/
def lagWronskian {N : ℕ} (x w : Fin N → ℝ) (φ : ℝ) : ℝ :=
  ∑ r : Fin N, w r * Real.sin (φ - 2 * π * (r : ℕ) / N) * ∏ s ∈ univ.erase r, lagDepth x s φ

/-- **The numerator on the unit circle.** -/
theorem eval_lagNumerator_circle {N : ℕ} (x w : Fin N → ℝ) (φ : ℝ) :
    (lagNumerator x w).eval (Complex.exp (φ * Complex.I)) =
      (-2 * Complex.exp (φ * Complex.I)) ^ (N - 1) * (∏ s : Fin N, lagRoot N ^ (s : ℕ)) *
        (-((∑ r, w r : ℝ) : ℂ) * ((∏ s, lagDepth x s φ : ℝ) : ℂ) +
          Complex.I * (lagWronskian x w φ : ℂ)) := by
  rw [lagNumerator_eq_residue, eval_finsetSum]
  have hterm : ∀ r : Fin N, ((C (w r : ℂ) * ((X - C ((Real.cosh (x r) : ℂ) * lagRoot N ^ (r : ℕ))) *
      ∏ s ∈ univ.erase r, lagQuad N (x s) s)).eval (Complex.exp (φ * Complex.I))) =
      (-2 * Complex.exp (φ * Complex.I)) ^ (N - 1) * (∏ s : Fin N, lagRoot N ^ (s : ℕ)) *
        ((w r : ℂ) * (-(lagDepth x r φ : ℂ) + Complex.I * (Real.sin (φ - 2 * π * (r : ℕ) / N) : ℂ)) *
          ((∏ s ∈ univ.erase r, lagDepth x s φ : ℝ) : ℂ)) := by
    intro r
    have hcard : (univ.erase r).card = N - 1 := by
      rw [card_erase_of_mem (mem_univ r), card_univ, Fintype.card_fin]
    simp only [eval_mul, eval_C, eval_sub, eval_X, eval_prod]
    rw [circle_sub_centre]
    simp only [eval_lagQuad_circle]
    rw [prod_mul_distrib, prod_mul_distrib, prod_const, hcard, ← mul_prod_erase univ
      (fun s : Fin N => lagRoot N ^ (s : ℕ)) (mem_univ r)]
    simp only [lagDepth]
    push_cast
    ring
  rw [sum_congr rfl fun r _ => hterm r, ← mul_sum]
  congr 1
  have hD : ∀ r : Fin N, (lagDepth x r φ : ℂ) * ((∏ s ∈ univ.erase r, lagDepth x s φ : ℝ) : ℂ) =
      ((∏ s, lagDepth x s φ : ℝ) : ℂ) := fun r => by
    rw [← Complex.ofReal_mul, mul_prod_erase univ (fun s => lagDepth x s φ) (mem_univ r)]
  have e : ∀ r : Fin N, (w r : ℂ) * (-(lagDepth x r φ : ℂ) +
      Complex.I * (Real.sin (φ - 2 * π * (r : ℕ) / N) : ℂ)) *
        ((∏ s ∈ univ.erase r, lagDepth x s φ : ℝ) : ℂ) =
      -(w r : ℂ) * ((∏ s, lagDepth x s φ : ℝ) : ℂ) + Complex.I * ((w r *
        Real.sin (φ - 2 * π * (r : ℕ) / N) * ∏ s ∈ univ.erase r, lagDepth x s φ : ℝ) : ℂ) := by
    intro r
    rw [← hD r]
    push_cast
    ring
  rw [sum_congr rfl fun r _ => e r, sum_add_distrib, ← sum_mul, ← mul_sum, sum_neg_distrib,
    ← Complex.ofReal_sum, ← Complex.ofReal_sum, lagWronskian]

/-! ### The Wronskian is constant and vanishes -/

theorem prod_lagRoot_ne_zero (N : ℕ) : (∏ s : Fin N, lagRoot N ^ (s : ℕ)) ≠ 0 :=
  prod_ne_zero_iff.mpr fun _ _ => pow_ne_zero _ (Complex.exp_ne_zero _)

/-- The weights sum to zero: the symbol at `m = 0`. -/
theorem sum_weights_eq_zero {N : ℕ} {x w : Fin N → ℝ} (hN : 0 < N)
    (hsym : ∀ m : ℕ, m < N →
      ∑ r : Fin N, (w r : ℂ) * (Real.cosh (m * x r) : ℂ) * lagRoot N ^ ((r : ℕ) * m) = 0) :
    ∑ r, w r = 0 := by
  have h := hsym 0 hN
  simp only [CharP.cast_eq_zero, zero_mul, mul_zero, Real.cosh_zero, Complex.ofReal_one,
    mul_one, pow_zero] at h
  exact_mod_cast h

/-- **The leading coefficient reads the Wronskian at every angle.** -/
theorem lagNumerator_coeff_eq {N : ℕ} {x w : Fin N → ℝ} (hN : 0 < N)
    (hsym : ∀ m : ℕ, m < N →
      ∑ r : Fin N, (w r : ℂ) * (Real.cosh (m * x r) : ℂ) * lagRoot N ^ ((r : ℕ) * m) = 0)
    (ψ : ℝ) : (lagNumerator x w).coeff (N - 1) = (-2) ^ (N - 1) *
      (∏ s : Fin N, lagRoot N ^ (s : ℕ)) * (Complex.I * (lagWronskian x w ψ : ℂ)) := by
  have hT := lagNumerator_eq_monomial hsym
  have h := eval_lagNumerator_circle x w ψ
  rw [sum_weights_eq_zero hN hsym, Complex.ofReal_zero, neg_zero, zero_mul, zero_add, mul_pow] at h
  rw [hT, eval_mul, eval_C, eval_pow, eval_X] at h
  have hu : Complex.exp (ψ * Complex.I) ^ (N - 1) ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  apply mul_right_cancel₀ hu
  rw [h]
  ring

theorem lagDepth_pos {N : ℕ} {x : Fin N → ℝ} {r : Fin N} (hx : 0 < x r) (φ : ℝ) :
    0 < lagDepth x r φ := by
  unfold lagDepth
  have h1 : 1 < Real.cosh (x r) := Real.one_lt_cosh.mpr hx.ne'
  have h2 := Real.cos_le_one (φ - 2 * π * (r : ℕ) / N)
  linarith

theorem hasDerivAt_lagDepth {N : ℕ} (x : Fin N → ℝ) (r : Fin N) (φ : ℝ) :
    HasDerivAt (fun ψ => lagDepth x r ψ) (Real.sin (φ - 2 * π * (r : ℕ) / N)) φ := by
  have h := (((hasDerivAt_id φ).sub_const (2 * π * (r : ℕ) / N)).cos).const_sub
    (Real.cosh (x r))
  simp only [id, mul_one, neg_neg] at h
  exact h

/-- **The Wronskian vanishes.** With a node on the line, `G` vanishes at its angle. Otherwise
`Ψ = Σ_r w_r log D_r` is `2π`-periodic with `Ψ' = G/Π_s D_s`, and Rolle gives a zero. -/
theorem lagWronskian_eq_zero {N : ℕ} {x w : Fin N → ℝ} (hN : 0 < N) (hx : ∀ r, 0 ≤ x r)
    (hsym : ∀ m : ℕ, m < N →
      ∑ r : Fin N, (w r : ℂ) * (Real.cosh (m * x r) : ℂ) * lagRoot N ^ ((r : ℕ) * m) = 0)
    (φ : ℝ) : lagWronskian x w φ = 0 := by
  have hconst : ∀ ψ, lagWronskian x w ψ = lagWronskian x w φ := by
    intro ψ
    have h1 := lagNumerator_coeff_eq hN hsym ψ
    have h2 := lagNumerator_coeff_eq hN hsym φ
    have hK : (-2 : ℂ) ^ (N - 1) * (∏ s : Fin N, lagRoot N ^ (s : ℕ)) * Complex.I ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (prod_lagRoot_ne_zero N))
        Complex.I_ne_zero
    have h : ((lagWronskian x w ψ : ℝ) : ℂ) = (lagWronskian x w φ : ℂ) := by
      apply mul_left_cancel₀ hK
      linear_combination h2 - h1
    exact_mod_cast h
  by_cases h0 : ∃ r₀, x r₀ = 0
  · obtain ⟨r₀, hr₀⟩ := h0
    rw [← hconst (2 * π * (r₀ : ℕ) / N)]
    unfold lagWronskian
    refine sum_eq_zero fun r _ => ?_
    by_cases hr : r = r₀
    · subst hr
      simp
    · have hD : lagDepth x r₀ (2 * π * (r₀ : ℕ) / N) = 0 := by simp [lagDepth, hr₀]
      rw [prod_eq_zero (mem_erase.mpr ⟨Ne.symm hr, mem_univ r₀⟩) hD, mul_zero]
  · push Not at h0
    have hpos : ∀ r, 0 < x r := fun r => lt_of_le_of_ne (hx r) (Ne.symm (h0 r))
    have hderiv : ∀ ψ, HasDerivAt (fun ψ => ∑ r, w r * Real.log (lagDepth x r ψ))
        (∑ r, w r * (Real.sin (ψ - 2 * π * (r : ℕ) / N) / lagDepth x r ψ)) ψ := fun ψ =>
      HasDerivAt.fun_sum fun r _ =>
        ((hasDerivAt_lagDepth x r ψ).log (lagDepth_pos (hpos r) ψ).ne').const_mul (w r)
    have hper : (∑ r, w r * Real.log (lagDepth x r 0)) =
        ∑ r, w r * Real.log (lagDepth x r (2 * π)) := by
      refine sum_congr rfl fun r _ => ?_
      simp only [lagDepth, zero_sub, Real.cos_neg, Real.cos_two_pi_sub]
    obtain ⟨c, -, hc⟩ := exists_hasDerivAt_eq_zero (by positivity : (0 : ℝ) < 2 * π)
      (fun ψ _ => (hderiv ψ).continuousAt.continuousWithinAt) hper (fun ψ _ => hderiv ψ)
    rw [← hconst c]
    have hD : ∀ r, ∏ s ∈ univ.erase r, lagDepth x s c =
        (∏ s, lagDepth x s c) / lagDepth x r c := fun r => by
      rw [eq_div_iff (lagDepth_pos (hpos r) c).ne', mul_comm,
        mul_prod_erase univ (fun s => lagDepth x s c) (mem_univ r)]
    unfold lagWronskian
    simp_rw [hD]
    have e : ∑ r, w r * Real.sin (c - 2 * π * (r : ℕ) / N) *
        ((∏ s, lagDepth x s c) / lagDepth x r c) =
        (∏ s, lagDepth x s c) * ∑ r, w r * (Real.sin (c - 2 * π * (r : ℕ) / N) / lagDepth x r c) := by
      rw [mul_sum]
      exact sum_congr rfl fun r _ => by ring
    rw [e, hc, mul_zero]

/-! ### Rigidity -/

/-- Nodes of different residues have different arguments. -/
theorem eval_lagQuad_ne_zero {N : ℕ} (hN : 0 < N) {r s : Fin N} (hrs : r ≠ s) (y x : ℝ) :
    (lagQuad N x s).eval ((Real.exp y : ℂ) * lagRoot N ^ (r : ℕ)) ≠ 0 := by
  have hprim := Complex.isPrimitiveRoot_exp N hN.ne'
  have key : ∀ t : ℝ, (Real.exp y : ℂ) * lagRoot N ^ (r : ℕ) ≠ (Real.exp t : ℂ) * lagRoot N ^ (s : ℕ) := by
    intro t h
    have hn := congrArg norm h
    simp only [norm_mul, norm_pow, norm_lagRoot, one_pow, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hn
    rw [hn] at h
    have hω : lagRoot N ^ (r : ℕ) = lagRoot N ^ (s : ℕ) :=
      mul_left_cancel₀ (by exact_mod_cast (Real.exp_pos t).ne') h
    exact hrs (Fin.ext (hprim.pow_inj r.2 s.2 hω))
  simp only [lagQuad, lagOuter, lagInner, eval_mul, eval_sub, eval_X, eval_C]
  exact mul_ne_zero (sub_ne_zero.mpr (key _)) (sub_ne_zero.mpr (key _))

/-- **Periodic patterns cannot satisfy their last lag.** If the lag symbol
`Σ_r w_r cosh(m x_r) ω^{rm}` of a period-`N` pattern with depths `x_r ≥ 0` vanishes for every
`0 ≤ m ≤ N − 1`, all weights vanish. -/
theorem eq_zero_of_lagSymbol_eq_zero {N : ℕ} (hN : 0 < N) {x w : Fin N → ℝ} (hx : ∀ r, 0 ≤ x r)
    (hsym : ∀ m : ℕ, m < N →
      ∑ r : Fin N, (w r : ℂ) * (Real.cosh (m * x r) : ℂ) * lagRoot N ^ ((r : ℕ) * m) = 0) :
    w = 0 := by
  have hκ : (lagNumerator x w).coeff (N - 1) = 0 := by
    rw [lagNumerator_coeff_eq hN hsym 0, lagWronskian_eq_zero hN hx hsym 0, Complex.ofReal_zero,
      mul_zero, mul_zero]
  have hT : lagNumerator x w = 0 := by
    rw [lagNumerator_eq_monomial hsym, hκ, C_0, zero_mul]
  rw [lagNumerator_eq_residue] at hT
  funext r₀
  set e : Fin N → ℂ := fun r => (Real.cosh (x r) : ℂ) * lagRoot N ^ (r : ℕ) with he
  rcases (hx r₀).lt_or_eq with hpos | hzero
  · -- evaluate at the outer node of `r₀`
    have h := congrArg (eval (lagOuter N (x r₀) r₀)) hT
    rw [eval_finsetSum, eval_zero, sum_eq_single r₀] at h
    · simp only [eval_mul, eval_C, eval_sub, eval_X, eval_prod] at h
      have hsub : lagOuter N (x r₀) r₀ - (Real.cosh (x r₀) : ℂ) * lagRoot N ^ (r₀ : ℕ) =
          (Real.sinh (x r₀) : ℂ) * lagRoot N ^ (r₀ : ℕ) := by
        simp only [lagOuter, Real.cosh_eq, Real.sinh_eq]
        push_cast
        ring
      rw [hsub] at h
      have hsinh : (Real.sinh (x r₀) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sinh_pos_iff.mpr hpos).ne'
      have hprod : ∏ s ∈ univ.erase r₀, (lagQuad N (x s) s).eval (lagOuter N (x r₀) r₀) ≠ 0 :=
        prod_ne_zero_iff.mpr fun s hs =>
          eval_lagQuad_ne_zero hN (Ne.symm (ne_of_mem_erase hs)) (x r₀) (x s)
      have hω : lagRoot N ^ (r₀ : ℕ) ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
      simp only [Pi.zero_apply]
      exact_mod_cast (mul_eq_zero.mp h).resolve_right
        (mul_ne_zero (mul_ne_zero hsinh hω) hprod)
    · intro r _ hr
      simp only [eval_mul, eval_C, eval_sub, eval_X, eval_prod]
      rw [prod_eq_zero (mem_erase.mpr ⟨Ne.symm hr, mem_univ r₀⟩), mul_zero, mul_zero]
      simp [lagQuad]
    · intro h
      exact absurd (mem_univ r₀) h
  · -- a node on the line: divide by `X − ω^{r₀}`
    set ω := lagRoot N ^ (r₀ : ℕ) with hωdef
    have hq : lagQuad N (x r₀) r₀ = (X - C ω) ^ 2 := by
      rw [lagQuad, lagOuter, lagInner, ← hzero, neg_zero, Real.exp_zero, Complex.ofReal_one,
        one_mul, sq]
    have he0 : (Real.cosh (x r₀) : ℂ) * lagRoot N ^ (r₀ : ℕ) = ω := by
      rw [← hzero, Real.cosh_zero, Complex.ofReal_one, one_mul]
    have hsplit : ∀ r ∈ univ.erase r₀, C (w r : ℂ) * ((X - C ((Real.cosh (x r) : ℂ) *
        lagRoot N ^ (r : ℕ))) * ∏ s ∈ univ.erase r, lagQuad N (x s) s) =
        (X - C ω) * ((X - C ω) * (C (w r : ℂ) * ((X - C ((Real.cosh (x r) : ℂ) *
          lagRoot N ^ (r : ℕ))) * ∏ s ∈ (univ.erase r).erase r₀, lagQuad N (x s) s))) := by
      intro r hr
      rw [← mul_prod_erase (univ.erase r) (fun s => lagQuad N (x s) s)
        (mem_erase.mpr ⟨Ne.symm (ne_of_mem_erase hr), mem_univ r₀⟩), hq]
      ring
    rw [← add_sum_erase univ _ (mem_univ r₀), sum_congr rfl hsplit, ← mul_sum, he0] at hT
    set S := ∑ r ∈ univ.erase r₀, (X - C ω) * (C (w r : ℂ) * ((X - C ((Real.cosh (x r) : ℂ) *
      lagRoot N ^ (r : ℕ))) * ∏ s ∈ (univ.erase r).erase r₀, lagQuad N (x s) s)) with hS
    have hfac : (X - C ω) * (C (w r₀ : ℂ) * ∏ s ∈ univ.erase r₀, lagQuad N (x s) s + S) = 0 := by
      rw [← hT]
      ring
    have hbr := (mul_eq_zero.mp hfac).resolve_left (X_sub_C_ne_zero ω)
    have hS0 : S.eval ω = 0 := by
      rw [hS, eval_finsetSum]
      exact sum_eq_zero fun r _ => by simp
    have h := congrArg (eval ω) hbr
    rw [eval_add, hS0, add_zero, eval_mul, eval_C, eval_prod, eval_zero] at h
    have hprod : ∏ s ∈ univ.erase r₀, (lagQuad N (x s) s).eval ω ≠ 0 := by
      refine prod_ne_zero_iff.mpr fun s hs => ?_
      have := eval_lagQuad_ne_zero hN (Ne.symm (ne_of_mem_erase hs)) 0 (x s)
      rwa [Real.exp_zero, Complex.ofReal_one, one_mul] at this
    simp only [Pi.zero_apply]
    exact_mod_cast (mul_eq_zero.mp h).resolve_right hprod

end GaloisForLFunctions.ZeroConfigurationGeometry
