import GaloisForLFunctions.RHTower.RiemannKernelTransformInjectivity
import GaloisForLFunctions.HTGeometry.HamburgerQuarterCorrection

/-!
# The Riemann-kernel transform takes no nonzero constant value

For real weights `w` on `n ≥ 1` with `Σ |w(n)| n^{−2} < ∞`, put
`G_w(y) = Σ_n w(n) n^{−1/2} (Φ(y − log n) + Φ(y + log n))`, with `Φ` Riemann's kernel.

**Theorem** (`eq_zero_of_riemannKernelTransform_eq_const_of_sq`).  If `G_w ≡ C` is constant, then
`C = 0` and `w = 0`.

This strengthens `eq_zero_of_riemannKernelTransform_eq_zero_of_sq` (the case `C = 0`).  It is the
form of injectivity needed when only odd tests are available: for an odd test `H`, the pairing
`∫ H G_w′` only sees `G_w` up to an additive constant, the invisible atom at frequency `0`.

**Proof.**  As in the homogeneous case, `G_w = F″ − F/4` with `F(y) = S(y) + S(−y)` and
`S(y) = e^{y/2} θ_a(e^{2y})`, `a = 1 ⋆ w`.  Now `F + 4C` solves `f″ = f/4`, so
`F + 4C = A (e^{y/2} + e^{−y/2})`, which is the odd theta relation with a quarter correction:
`θ_a(x) = −x^{−1/2} θ_a(1/x) + A + A x^{−1/2} − 4C x^{−1/4}`.  The Hamburger argument with the
quarter term (`coeff_eq_zero_of_odd_coeffTheta_relation_quarter_of_sq`) gives `−4C = 0` and
`a = 0`, and Möbius inversion gives `w = 0`.
-/

open Complex MeasureTheory Filter Topology Set Polynomial
open scoped Real

namespace RHTower

noncomputable section

/-- **The Riemann-kernel transform takes no nonzero constant value.** If `Σ |w(n)| n^{−2} < ∞` and
`Σ_n w(n) n^{−1/2} (Φ(y − log n) + Φ(y + log n)) = C` for every `y`, then `C = 0` and `w = 0`. -/
theorem eq_zero_of_riemannKernelTransform_eq_const_of_sq {w : ℕ → ℝ} {C : ℝ}
    (hw2 : Summable fun n : ℕ => |w (n + 1)| / ((n : ℝ) + 1) ^ (2 : ℝ))
    (hG : ∀ y : ℝ, ∑' n : ℕ, w (n + 1) / Real.sqrt ((n + 1 : ℕ) : ℝ) *
      (riemannKernelReal (y - Real.log ((n + 1 : ℕ) : ℝ)) +
        riemannKernelReal (y + Real.log ((n + 1 : ℕ) : ℝ))) = C) :
    C = 0 ∧ ∀ n : ℕ, w (n + 1) = 0 := by
  obtain ⟨K, hw⟩ := exists_abs_le_of_summable_div_sq hw2
  set a := oneConvWeight w with hadef
  have ha := abs_oneConvWeight_le hw
  set S := weightedCuspSeries a 1 with hS
  set S₁ := weightedCuspSeries a (cuspDeriv 1) with hS₁
  set S₂ := weightedCuspSeries a (cuspDeriv (cuspDeriv 1)) with hS₂
  have hshift : ∀ y, ∑' n : ℕ, w (n + 1) / Real.sqrt ((n + 1 : ℕ) : ℝ) *
      riemannKernelReal (y + Real.log ((n + 1 : ℕ) : ℝ)) = S₂ y - S y / 4 := by
    intro y
    have h := tsum_shift_cuspSeries_eq hw riemannCuspPoly y
    simp_rw [cuspSeries_riemannCuspPoly_eq] at h
    rw [h, weightedCuspSeries_riemannCuspPoly ha y]
  have hsummG : ∀ y, Summable fun n : ℕ => w (n + 1) / Real.sqrt ((n + 1 : ℕ) : ℝ) *
      riemannKernelReal (y + Real.log ((n + 1 : ℕ) : ℝ)) := by
    intro y
    have h := summable_shift_cuspSeries hw riemannCuspPoly y
    simpa only [cuspSeries_riemannCuspPoly_eq] using h
  have hF : ∀ y, (S₂ y - S y / 4) + (S₂ (-y) - S (-y) / 4) = C := by
    intro y
    rw [← hshift y, ← hshift (-y)]
    have h := hG y
    have hev : ∀ n : ℕ, riemannKernelReal (y - Real.log ((n + 1 : ℕ) : ℝ)) =
        riemannKernelReal (-y + Real.log ((n + 1 : ℕ) : ℝ)) := by
      intro n
      unfold riemannKernelReal
      rw [show -y + Real.log ((n + 1 : ℕ) : ℝ) = -(y - Real.log ((n + 1 : ℕ) : ℝ)) by ring, abs_neg]
    simp_rw [hev, mul_add] at h
    rw [(hsummG (-y)).tsum_add (hsummG y)] at h
    linarith
  -- `F = S + S(−·) + 4C` solves `F'' = F/4`
  have hd0 : ∀ y, HasDerivAt S (S₁ y) y := fun y => hasDerivAt_weightedCuspSeries ha 1 y
  have hd1 : ∀ y, HasDerivAt S₁ (S₂ y) y :=
    fun y => hasDerivAt_weightedCuspSeries ha (cuspDeriv 1) y
  have hF1 : ∀ y, HasDerivAt (fun y => S y + S (-y) + 4 * C) (S₁ y - S₁ (-y)) y := by
    intro y
    have := ((hd0 y).add ((hd0 (-y)).comp y (hasDerivAt_neg y))).add_const (4 * C)
    exact this.congr_deriv (by ring)
  have hF2 : ∀ y, HasDerivAt (fun y => S₁ y - S₁ (-y)) (S₂ y + S₂ (-y)) y := by
    intro y
    have := (hd1 y).sub ((hd1 (-y)).comp y (hasDerivAt_neg y))
    exact this.congr_deriv (by ring)
  obtain ⟨A, B, hAB⟩ := exists_eq_exp_of_second_deriv hF1 hF2 (fun y => by
    have := hF y; linarith)
  have hAB' : A = B := by
    have h1 := hAB 2
    have h2 := hAB (-2)
    have hsym : S 2 + S (-2) + 4 * C = S (-2) + S (-(-2)) + 4 * C := by rw [neg_neg]; ring
    rw [h1, h2] at hsym
    have hne : Real.exp (2 / 2) ≠ Real.exp (-(2 / 2)) := by
      intro h; have := Real.exp_injective h; linarith
    have hsub : (A - B) * (Real.exp (2 / 2) - Real.exp (-(2 / 2))) = 0 := by
      rw [show -(-2 / 2 : ℝ) = 2 / 2 by ring, show (-2 / 2 : ℝ) = -(2 / 2) by ring] at hsym
      linarith
    rcases mul_eq_zero.mp hsub with h | h
    · linarith
    · exact absurd (sub_eq_zero.mp h) hne
  -- the odd theta relation with a quarter correction
  set a' : ℕ → ℂ := fun k => (a k : ℂ) with ha'
  have htheta : ∀ x : ℝ, 0 < x → GaloisForLFunctions.HTGeometry.coeffTheta a' x =
      (-1) * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * GaloisForLFunctions.HTGeometry.coeffTheta a' x⁻¹) +
        (A : ℂ) + (A : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
          ((-(4 * C) : ℝ) : ℂ) * (x : ℂ) ^ (-(1 / 4 : ℂ)) := by
    intro x hx
    set T : ℝ → ℝ := fun x => ∑' k : ℕ, a (k + 1) * Real.exp (-π * ((k : ℝ) + 1) ^ 2 * x) with hT
    have hθ : ∀ x : ℝ, GaloisForLFunctions.HTGeometry.coeffTheta a' x = (T x : ℂ) := by
      intro x
      rw [GaloisForLFunctions.HTGeometry.coeffTheta, hT, Complex.ofReal_tsum]
      refine tsum_congr fun k => ?_
      simp only [ha']; push_cast; ring_nf
    set y := Real.log x / 2 with hy
    have hx2 : Real.exp (2 * y) = x := by rw [hy, show 2 * (Real.log x / 2) = Real.log x by ring,
      Real.exp_log hx]
    have hx2' : Real.exp (2 * (-y)) = x⁻¹ := by
      rw [show 2 * (-y) = -(2 * y) by ring, Real.exp_neg, hx2]
    have hS : ∀ u, S u = Real.exp (u / 2) * T (Real.exp (2 * u)) := fun u => by
      rw [hS, weightedCuspSeries_one_eq]
    have hrel := hAB y
    rw [hAB', hS y, hS (-y), hx2, hx2'] at hrel
    have hpow : ((x : ℂ) ^ (-(1 / 2 : ℂ))) = ((Real.exp (-y) : ℝ) : ℂ) := by
      rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow hx.le, Real.rpow_def_of_pos hx, hy]
      congr 1; ring_nf
    have hpow4 : ((x : ℂ) ^ (-(1 / 4 : ℂ))) = ((Real.exp (-(y / 2)) : ℝ) : ℂ) := by
      rw [show (-(1 / 4 : ℂ)) = ((-(1 / 4) : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow hx.le, Real.rpow_def_of_pos hx, hy]
      congr 1; ring_nf
    have hE1 : Real.exp (-(y / 2)) * Real.exp (y / 2) = 1 := by rw [← Real.exp_add]; simp
    have hE2 : Real.exp (-(y / 2)) * Real.exp (-(y / 2)) = Real.exp (-y) := by
      rw [← Real.exp_add]; ring_nf
    have hreal : T x = -(Real.exp (-y) * T x⁻¹) + B + B * Real.exp (-y) -
        4 * C * Real.exp (-(y / 2)) := by
      have h := congrArg (fun t => Real.exp (-(y / 2)) * t) hrel
      beta_reduce at h
      have e1 : Real.exp (-(y / 2)) * (Real.exp (y / 2) * T x + Real.exp (-y / 2) * T x⁻¹ + 4 * C) =
          T x + Real.exp (-y) * T x⁻¹ + 4 * C * Real.exp (-(y / 2)) := by
        rw [show -y / 2 = -(y / 2) by ring, mul_add, mul_add, ← mul_assoc, hE1, ← mul_assoc, hE2,
          one_mul]
        ring
      have e2 : Real.exp (-(y / 2)) * (B * Real.exp (y / 2) + B * Real.exp (-(y / 2))) =
          B + B * Real.exp (-y) := by
        rw [mul_add, show Real.exp (-(y / 2)) * (B * Real.exp (y / 2)) =
          B * (Real.exp (-(y / 2)) * Real.exp (y / 2)) by ring, hE1,
          show Real.exp (-(y / 2)) * (B * Real.exp (-(y / 2))) =
          B * (Real.exp (-(y / 2)) * Real.exp (-(y / 2))) by ring, hE2, mul_one]
      rw [e1, e2] at h
      linarith
    rw [hθ x, hθ x⁻¹, hpow, hpow4, hreal, hAB']
    push_cast
    ring
  have ha'sum : Summable fun n : ℕ => ‖a' (n + 1)‖ / ((n : ℝ) + 1) ^ (2 : ℝ) := by
    refine (summable_oneConvWeight_div_rpow_two hw2).congr fun n => ?_
    simp only [ha', Complex.norm_real, Real.norm_eq_abs, hadef]
  obtain ⟨hγ, hzero'⟩ :=
    GaloisForLFunctions.HTGeometry.coeff_eq_zero_of_odd_coeffTheta_relation_quarter_of_sq
      ha'sum htheta
  have hC : C = 0 := by
    have h : (-(4 * C) : ℝ) = 0 := by exact_mod_cast hγ
    linarith
  have hzero : ∀ k : ℕ, a (k + 1) = 0 := fun k => by
    have h : (a (k + 1) : ℂ) = 0 := hzero' k
    exact_mod_cast h
  refine ⟨hC, ?_⟩
  -- Möbius inversion
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have h := hzero n
    unfold a oneConvWeight at h
    rw [← Nat.cons_self_properDivisors (Nat.succ_ne_zero n), Finset.sum_cons] at h
    have hprop : ∑ d ∈ (n + 1).properDivisors, w d = 0 := by
      refine Finset.sum_eq_zero fun d hd => ?_
      obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp hd
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd (Nat.succ_pos n)
      obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      exact ih e (by omega)
    linarith

end

end RHTower
