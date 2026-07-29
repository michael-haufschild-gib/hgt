import Mathlib

/-!
# Radial orientation from unit-circle roots

A polynomial whose roots lie on the unit circle has a strict inward logarithmic-derivative
inequality on the open unit disk.  After the standard exponential substitution and centering by
half the degree, this becomes a strict negative oriented current in the upper half-plane.

The result is finite and root-location-local: it does not use a limiting measure or a positivity
representation of the resulting analytic phase.
-/

open Complex Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- One unit-circle root contributes strictly less than one half to the inward radial logarithmic
derivative at every point of the open unit disk. -/
theorem re_div_sub_lt_half_of_norm_lt_one_of_norm_eq_one
    {w ζ : ℂ} (hw : ‖w‖ < 1) (hζ : ‖ζ‖ = 1) :
    (w / (w - ζ)).re < 1 / 2 := by
  let u : ℂ := w / ζ
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hζ
    norm_num at hζ
  have huNorm : ‖u‖ < 1 := by
    dsimp only [u]
    rw [norm_div, hζ, div_one]
    exact hw
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, norm_one] at huNorm
    exact lt_irrefl 1 huNorm
  have hden : 0 < normSq (u - 1) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr hu1)
  have huSq : normSq u < 1 := by
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg u]
  have hquot : w / (w - ζ) = u / (u - 1) := by
    dsimp only [u]
    field_simp
  rw [hquot, Complex.div_re]
  have hdenEq : normSq (u - 1) = normSq u - 2 * u.re + 1 := by
    rw [Complex.normSq_sub]
    simp
    ring
  rw [show u.re * (u - 1).re / normSq (u - 1) +
      u.im * (u - 1).im / normSq (u - 1) =
      (normSq u - u.re) / normSq (u - 1) by
    simp only [Complex.normSq_apply, sub_re, one_re, sub_im, one_im, sub_zero]
    ring]
  rw [div_lt_iff₀ hden, hdenEq]
  nlinarith

/-- Summing the root contributions gives the strict half-degree radial bound for every nonconstant
complex polynomial whose roots lie on the unit circle. -/
theorem re_mul_derivative_div_lt_half_natDegree_of_roots_unit
    (P : Polynomial ℂ) (hP : P ≠ 0) (hdeg : 0 < P.natDegree)
    (hroots : ∀ ζ ∈ P.roots, ‖ζ‖ = 1)
    {w : ℂ} (hw : ‖w‖ < 1) :
    (w * (P.derivative.eval w / P.eval w)).re < (P.natDegree : ℝ) / 2 := by
  have hPw : P.eval w ≠ 0 := by
    intro h
    have hwmem : w ∈ P.roots := (Polynomial.mem_roots hP).2 h
    have := hroots w hwmem
    linarith
  have hsplits : P.Splits := IsAlgClosed.splits P
  have hlog := hsplits.eval_derivative_div_eval_of_ne_zero hPw
  have hcard : P.roots.card = P.natDegree := hsplits.natDegree_eq_card_roots.symm
  have hne : P.roots ≠ 0 := by
    intro h
    rw [h, Multiset.card_zero] at hcard
    omega
  rw [hlog, ← Multiset.sum_map_mul_left]
  have hre := map_multiset_sum Complex.reCLM.toAddMonoidHom
    (Multiset.map (fun i => w * (1 / (w - i))) P.roots)
  change ((Multiset.map (fun i => w * (1 / (w - i))) P.roots).sum).re = _ at hre
  rw [hre, Multiset.map_map]
  change (Multiset.map (fun x => (w * (1 / (w - x))).re) P.roots).sum < _
  rw [show (Multiset.map (fun x => (w * (1 / (w - x))).re) P.roots).sum =
      (Multiset.map (fun x => (w / (w - x)).re) P.roots).sum by
    congr 1
    apply Multiset.map_congr rfl
    intro x _hx
    simp only [div_eq_mul_inv, one_mul]]
  calc
    (Multiset.map (fun x => (w / (w - x)).re) P.roots).sum <
        (Multiset.map (fun _x : ℂ => (1 / 2 : ℝ)) P.roots).sum := by
      exact Multiset.sum_lt_sum_of_nonempty hne fun ζ hζ =>
        re_div_sub_lt_half_of_norm_lt_one_of_norm_eq_one hw (hroots ζ hζ)
    _ = (P.natDegree : ℝ) / 2 := by
      simp [hcard, nsmul_eq_mul]
      ring

/-- The degree-centered exponential phase associated with a polynomial. -/
def centeredUnitCirclePolynomialPhase
    (P : Polynomial ℂ) (L : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-I * (((P.natDegree : ℝ) * L / 2 : ℝ) : ℂ) * z) *
    P.eval (Complex.exp (I * (L : ℂ) * z))

/-- Explicit derivative of the degree-centered exponential phase. -/
def centeredUnitCirclePolynomialPhaseDerivative
    (P : Polynomial ℂ) (L : ℝ) (z : ℂ) : ℂ :=
  let w := Complex.exp (I * (L : ℂ) * z)
  let c := Complex.exp (-I * (((P.natDegree : ℝ) * L / 2 : ℝ) : ℂ) * z)
  c * (I * (L : ℂ)) *
    (w * P.derivative.eval w - ((P.natDegree : ℝ) / 2 : ℂ) * P.eval w)

theorem hasDerivAt_centeredUnitCirclePolynomialPhase
    (P : Polynomial ℂ) (L : ℝ) (z : ℂ) :
    HasDerivAt (centeredUnitCirclePolynomialPhase P L)
      (centeredUnitCirclePolynomialPhaseDerivative P L z) z := by
  let alpha : ℂ := (((P.natDegree : ℝ) * L / 2 : ℝ) : ℂ)
  let w : ℂ := Complex.exp (I * (L : ℂ) * z)
  let c : ℂ := Complex.exp (-I * alpha * z)
  have hc : HasDerivAt (fun u : ℂ => Complex.exp (-I * alpha * u))
      ((-I * alpha) * c) z := by
    refine ((Complex.hasDerivAt_exp (-I * alpha * z)).comp z
      ((hasDerivAt_id z).const_mul (-I * alpha))).congr_deriv ?_
    dsimp only [c]
    ring
  have hw : HasDerivAt (fun u : ℂ => Complex.exp (I * (L : ℂ) * u))
      ((I * (L : ℂ)) * w) z := by
    refine ((Complex.hasDerivAt_exp (I * (L : ℂ) * z)).comp z
      ((hasDerivAt_id z).const_mul (I * (L : ℂ)))).congr_deriv ?_
    dsimp only [w]
    ring
  have hP : HasDerivAt (fun u : ℂ => P.eval (Complex.exp (I * (L : ℂ) * u)))
      (((I * (L : ℂ)) * w) * P.derivative.eval w) z := by
    refine ((P.hasDerivAt w).comp z hw).congr_deriv ?_
    ring
  unfold centeredUnitCirclePolynomialPhase
  refine (hc.mul hP).congr_deriv ?_
  dsimp only [centeredUnitCirclePolynomialPhaseDerivative, alpha, w, c]
  push_cast
  ring

/-- A centered exponential phase built from unit-circle roots has strict negative oriented current
at every upper-half-plane point. -/
theorem centeredUnitCirclePolynomialPhase_current_lt_zero
    (P : Polynomial ℂ) (hP : P ≠ 0) (hdeg : 0 < P.natDegree)
    (hroots : ∀ ζ ∈ P.roots, ‖ζ‖ = 1)
    {L : ℝ} (hL : 0 < L) {z : ℂ} (hz : 0 < z.im) :
    ((centeredUnitCirclePolynomialPhaseDerivative P L z) *
      (starRingEnd ℂ) (centeredUnitCirclePolynomialPhase P L z)).im < 0 := by
  let w : ℂ := Complex.exp (I * (L : ℂ) * z)
  let c : ℂ := Complex.exp (-I * (((P.natDegree : ℝ) * L / 2 : ℝ) : ℂ) * z)
  have hwre : (I * (L : ℂ) * z).re = -L * z.im := by
    simp [Complex.mul_re]
  have hwNorm : ‖w‖ < 1 := by
    dsimp [w]
    rw [Complex.norm_exp, hwre, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by nlinarith)
  have hPw : P.eval w ≠ 0 := by
    intro h
    have hwmem : w ∈ P.roots := (Polynomial.mem_roots hP).2 h
    have hwunit := hroots w hwmem
    linarith
  have hrad := re_mul_derivative_div_lt_half_natDegree_of_roots_unit
    P hP hdeg hroots hwNorm
  have hnormc : 0 < Complex.normSq c :=
    Complex.normSq_pos.mpr (Complex.exp_ne_zero _)
  have hnormP : 0 < Complex.normSq (P.eval w) := Complex.normSq_pos.mpr hPw
  have hderivative : centeredUnitCirclePolynomialPhaseDerivative P L z =
      c * (I * (L : ℂ)) *
        (w * (P.derivative.eval w / P.eval w) -
          ((P.natDegree : ℝ) / 2 : ℂ)) * P.eval w := by
    change c * (I * (L : ℂ)) *
        (w * P.derivative.eval w -
          ((P.natDegree : ℝ) / 2 : ℂ) * P.eval w) = _
    symm
    calc
      c * (I * (L : ℂ)) *
          (w * (P.derivative.eval w / P.eval w) -
            ((P.natDegree : ℝ) / 2 : ℂ)) * P.eval w =
        c * (I * (L : ℂ)) *
          ((w * (P.derivative.eval w / P.eval w) -
            ((P.natDegree : ℝ) / 2 : ℂ)) * P.eval w) := by ring
      _ = c * (I * (L : ℂ)) *
          (w * P.derivative.eval w -
            ((P.natDegree : ℝ) / 2 : ℂ) * P.eval w) := by
        rw [sub_mul, mul_assoc w,
          div_mul_cancel₀ (P.derivative.eval w) hPw]
  have hphase : centeredUnitCirclePolynomialPhase P L z = c * P.eval w := rfl
  have halg :
      (centeredUnitCirclePolynomialPhaseDerivative P L z) *
          (starRingEnd ℂ) (centeredUnitCirclePolynomialPhase P L z) =
        (Complex.normSq c * Complex.normSq (P.eval w) * L : ℝ) *
          (I * (w * (P.derivative.eval w / P.eval w) -
            ((P.natDegree : ℝ) / 2 : ℂ))) := by
    rw [hderivative, hphase, map_mul]
    calc
      c * (I * (L : ℂ)) *
            (w * (P.derivative.eval w / P.eval w) -
              ((P.natDegree : ℝ) / 2 : ℂ)) * P.eval w *
          ((starRingEnd ℂ) c * (starRingEnd ℂ) (P.eval w)) =
        (c * (starRingEnd ℂ) c) *
          (P.eval w * (starRingEnd ℂ) (P.eval w)) *
            ((L : ℂ) * (I * (w * (P.derivative.eval w / P.eval w) -
              ((P.natDegree : ℝ) / 2 : ℂ)))) := by ring
      _ = _ := by
        rw [mul_conj c, mul_conj (P.eval w)]
        push_cast
        ring
  rw [halg]
  have hre :
      (I * (w * (P.derivative.eval w / P.eval w) -
        ((P.natDegree : ℝ) / 2 : ℂ))).im =
      (w * (P.derivative.eval w / P.eval w)).re - (P.natDegree : ℝ) / 2 := by
    simp [Complex.mul_im]
  rw [Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [hre]
  exact mul_neg_of_pos_of_neg (mul_pos (mul_pos hnormc hnormP) hL)
    (sub_neg.mpr hrad)

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Geometric and prime-power divisor packets -/

/-- The ordinary finite geometric polynomial with `N` terms. -/
def finiteGeometricPolynomial (N : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range N, X ^ j

@[simp] theorem finiteGeometricPolynomial_coeff (N m : ℕ) :
    (finiteGeometricPolynomial N).coeff m = if m < N then 1 else 0 := by
  simp [finiteGeometricPolynomial, Polynomial.coeff_X_pow]

theorem finiteGeometricPolynomial_natDegree
    (N : ℕ) (hN : 0 < N) :
    (finiteGeometricPolynomial N).natDegree = N - 1 := by
  apply le_antisymm
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    simp [finiteGeometricPolynomial, Polynomial.coeff_X_pow]
    omega
  · apply Polynomial.le_natDegree_of_ne_zero
    simp [finiteGeometricPolynomial, Polynomial.coeff_X_pow]
    omega

theorem finiteGeometricPolynomial_ne_zero
    (N : ℕ) (hN : 0 < N) :
    finiteGeometricPolynomial N ≠ 0 :=
  (Polynomial.monic_geom_sum_X (show N ≠ 0 by omega)).ne_zero

/-- Every root of a nonempty finite geometric polynomial lies on the unit circle. -/
theorem finiteGeometricPolynomial_root_norm_eq_one
    (N : ℕ) (hN : 0 < N) {ζ : ℂ}
    (hζ : (finiteGeometricPolynomial N).eval ζ = 0) :
    ‖ζ‖ = 1 := by
  have hsum : ∑ j ∈ Finset.range N, ζ ^ j = 0 := by
    simpa [finiteGeometricPolynomial, Polynomial.eval_geom_sum] using hζ
  have hgeom := geom_sum_mul ζ N
  rw [hsum, zero_mul] at hgeom
  have hzpow : ζ ^ N = 1 := sub_eq_zero.mp hgeom.symm
  exact (isOfFinOrder_iff_pow_eq_one.mpr ⟨N, hN, hzpow⟩).norm_eq_one

/-- The centered `N`-term exponential packet.  For `L = log p`, its frequencies are exactly the
centered exponent divisors of a prime power with exponent `N - 1`. -/
def centeredGeometricExponentialPacket (N : ℕ) (L : ℝ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range N,
    Complex.exp
      (I * (((((j : ℕ) : ℝ) - ((N - 1 : ℕ) : ℝ) / 2) * L : ℝ) : ℂ) * z)

/-- Explicit derivative of the centered geometric exponential packet. -/
def centeredGeometricExponentialPacketDerivative (N : ℕ) (L : ℝ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range N,
    (I * (((((j : ℕ) : ℝ) - ((N - 1 : ℕ) : ℝ) / 2) * L : ℝ) : ℂ)) *
      Complex.exp
        (I * (((((j : ℕ) : ℝ) - ((N - 1 : ℕ) : ℝ) / 2) * L : ℝ) : ℂ) * z)

theorem centeredUnitCirclePolynomialPhase_eq_centeredGeometricExponentialPacket
    (N : ℕ) (hN : 0 < N) (L : ℝ) (z : ℂ) :
    centeredUnitCirclePolynomialPhase (finiteGeometricPolynomial N) L z =
      centeredGeometricExponentialPacket N L z := by
  have hdeg := finiteGeometricPolynomial_natDegree N hN
  unfold centeredUnitCirclePolynomialPhase centeredGeometricExponentialPacket
  rw [hdeg]
  simp only [finiteGeometricPolynomial, Polynomial.eval_geom_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem hasDerivAt_centeredGeometricExponentialPacket
    (N : ℕ) (L : ℝ) (z : ℂ) :
    HasDerivAt (centeredGeometricExponentialPacket N L)
      (centeredGeometricExponentialPacketDerivative N L z) z := by
  unfold centeredGeometricExponentialPacket centeredGeometricExponentialPacketDerivative
  have hsum := HasDerivAt.sum (u := Finset.range N)
    (A := fun j (u : ℂ) =>
      Complex.exp
        (I * (((((j : ℕ) : ℝ) - ((N - 1 : ℕ) : ℝ) / 2) * L : ℝ) : ℂ) * u))
    (A' := fun j =>
      (I * (((((j : ℕ) : ℝ) - ((N - 1 : ℕ) : ℝ) / 2) * L : ℝ) : ℂ)) *
        Complex.exp
          (I * (((((j : ℕ) : ℝ) - ((N - 1 : ℕ) : ℝ) / 2) * L : ℝ) : ℂ) * z))
    (fun j _hj => by
      let a : ℂ :=
        I * (((((j : ℕ) : ℝ) - ((N - 1 : ℕ) : ℝ) / 2) * L : ℝ) : ℂ)
      refine ((Complex.hasDerivAt_exp (a * z)).comp z
        ((hasDerivAt_id z).const_mul a)).congr_deriv ?_
      dsimp only [a]
      ring)
  rw [show
    (∑ j ∈ Finset.range N, fun u : ℂ =>
      Complex.exp
        (I * (((((j : ℕ) : ℝ) - ((N - 1 : ℕ) : ℝ) / 2) * L : ℝ) : ℂ) * u)) =
      fun u : ℂ => ∑ j ∈ Finset.range N,
        Complex.exp
          (I * (((((j : ℕ) : ℝ) - ((N - 1 : ℕ) : ℝ) / 2) * L : ℝ) : ℂ) * u) by
    funext u
    simp only [Finset.sum_apply]] at hsum
  exact hsum

theorem centeredUnitCirclePolynomialPhaseDerivative_eq_centeredGeometricExponentialPacketDerivative
    (N : ℕ) (hN : 0 < N) (L : ℝ) (z : ℂ) :
    centeredUnitCirclePolynomialPhaseDerivative (finiteGeometricPolynomial N) L z =
      centeredGeometricExponentialPacketDerivative N L z := by
  have hfun : centeredUnitCirclePolynomialPhase (finiteGeometricPolynomial N) L =
      centeredGeometricExponentialPacket N L := by
    funext u
    exact centeredUnitCirclePolynomialPhase_eq_centeredGeometricExponentialPacket N hN L u
  have hleft := hasDerivAt_centeredUnitCirclePolynomialPhase
    (finiteGeometricPolynomial N) L z
  have hright := hasDerivAt_centeredGeometricExponentialPacket N L z
  rw [hfun] at hleft
  exact hleft.unique hright

/-- Strict upper-half-plane orientation of every nontrivial centered geometric packet. -/
theorem centeredGeometricExponentialPacket_current_lt_zero
    (N : ℕ) (hN : 1 < N) {L : ℝ} (hL : 0 < L) {z : ℂ} (hz : 0 < z.im) :
    (centeredGeometricExponentialPacketDerivative N L z *
      (starRingEnd ℂ) (centeredGeometricExponentialPacket N L z)).im < 0 := by
  have hN0 : 0 < N := by omega
  have hP := finiteGeometricPolynomial_ne_zero N hN0
  have hdegpos : 0 < (finiteGeometricPolynomial N).natDegree := by
    rw [finiteGeometricPolynomial_natDegree N hN0]
    omega
  have hroots : ∀ ζ ∈ (finiteGeometricPolynomial N).roots, ‖ζ‖ = 1 := by
    intro ζ hζ
    exact finiteGeometricPolynomial_root_norm_eq_one N hN0
      ((Polynomial.mem_roots hP).1 hζ)
  rw [← centeredUnitCirclePolynomialPhaseDerivative_eq_centeredGeometricExponentialPacketDerivative
    N hN0 L z, ← centeredUnitCirclePolynomialPhase_eq_centeredGeometricExponentialPacket
      N hN0 L z]
  exact centeredUnitCirclePolynomialPhase_current_lt_zero
    (finiteGeometricPolynomial N) hP hdegpos hroots hL hz

/-- The centered analytic divisor packet of the prime power `p^a`. -/
def primePowerCenteredDivisorPhase (p a : ℕ) (z : ℂ) : ℂ :=
  centeredGeometricExponentialPacket (a + 1) (Real.log p) z

/-- Explicit derivative of the centered prime-power divisor packet. -/
def primePowerCenteredDivisorPhaseDerivative (p a : ℕ) (z : ℂ) : ℂ :=
  centeredGeometricExponentialPacketDerivative (a + 1) (Real.log p) z

/-- Every nonconstant prime-power divisor phase has strict negative upper oriented current. -/
theorem primePowerCenteredDivisorPhase_current_lt_zero
    {p a : ℕ} (hp : 1 < p) (ha : 0 < a) {z : ℂ} (hz : 0 < z.im) :
    (primePowerCenteredDivisorPhaseDerivative p a z *
      (starRingEnd ℂ) (primePowerCenteredDivisorPhase p a z)).im < 0 := by
  exact centeredGeometricExponentialPacket_current_lt_zero (a + 1) (by omega)
    (Real.log_pos (by exact_mod_cast hp)) hz

/-! ## Exact signed Fejer polarization -/

@[simp] theorem finiteGeometricPolynomial_succ (N : ℕ) :
    finiteGeometricPolynomial (N + 1) =
      finiteGeometricPolynomial N + X ^ N := by
  simp [finiteGeometricPolynomial, Finset.sum_range_succ]

private theorem X_sub_one_ne_zero : (X - 1 : Polynomial ℂ) ≠ 0 := by
  intro h
  have hc := congrArg (Polynomial.eval 0) h
  norm_num at hc

/-- An odd-length geometric packet is the difference of two consecutive analytic squares. -/
theorem finiteGeometricPolynomial_odd_eq_square_sub_shift_square (a : ℕ) :
    finiteGeometricPolynomial (2 * a + 1) =
      finiteGeometricPolynomial (a + 1) ^ 2 -
        X * finiteGeometricPolynomial a ^ 2 := by
  apply mul_right_cancel₀ X_sub_one_ne_zero
  rw [show finiteGeometricPolynomial (2 * a + 1) * (X - 1) =
      X ^ (2 * a + 1) - 1 by
    simpa [finiteGeometricPolynomial] using
      geom_sum_mul (X : Polynomial ℂ) (2 * a + 1)]
  symm
  have ha1 : finiteGeometricPolynomial (a + 1) * (X - 1) = X ^ (a + 1) - 1 := by
    simpa [finiteGeometricPolynomial] using
      geom_sum_mul (X : Polynomial ℂ) (a + 1)
  have ha0 : finiteGeometricPolynomial a * (X - 1) = X ^ a - 1 := by
    simpa [finiteGeometricPolynomial] using geom_sum_mul (X : Polynomial ℂ) a
  have hrec : finiteGeometricPolynomial (a + 1) =
      finiteGeometricPolynomial a + X ^ a := finiteGeometricPolynomial_succ a
  rw [sub_mul]
  calc
    finiteGeometricPolynomial (a + 1) ^ 2 * (X - 1) -
        X * finiteGeometricPolynomial a ^ 2 * (X - 1) =
      finiteGeometricPolynomial (a + 1) *
          (finiteGeometricPolynomial (a + 1) * (X - 1)) -
        X * finiteGeometricPolynomial a *
          (finiteGeometricPolynomial a * (X - 1)) := by ring
    _ = finiteGeometricPolynomial (a + 1) * (X ^ (a + 1) - 1) -
        X * finiteGeometricPolynomial a * (X ^ a - 1) := by rw [ha1, ha0]
    _ = X ^ (2 * a + 1) - 1 := by
      rw [hrec]
      linear_combination ha0

/-- An even-length geometric packet is the difference of two adjacent Gram cross-products. -/
theorem finiteGeometricPolynomial_even_eq_cross_sub_shift_cross (a : ℕ) :
    finiteGeometricPolynomial (2 * a + 2) =
      finiteGeometricPolynomial (a + 1) * finiteGeometricPolynomial (a + 2) -
        X * finiteGeometricPolynomial a * finiteGeometricPolynomial (a + 1) := by
  apply mul_right_cancel₀ X_sub_one_ne_zero
  rw [show finiteGeometricPolynomial (2 * a + 2) * (X - 1) =
      X ^ (2 * a + 2) - 1 by
    simpa [finiteGeometricPolynomial] using
      geom_sum_mul (X : Polynomial ℂ) (2 * a + 2)]
  symm
  have ha2 : finiteGeometricPolynomial (a + 2) * (X - 1) = X ^ (a + 2) - 1 := by
    simpa [finiteGeometricPolynomial] using
      geom_sum_mul (X : Polynomial ℂ) (a + 2)
  have ha0 : finiteGeometricPolynomial a * (X - 1) = X ^ a - 1 := by
    simpa [finiteGeometricPolynomial] using geom_sum_mul (X : Polynomial ℂ) a
  have ha1 : finiteGeometricPolynomial (a + 1) * (X - 1) = X ^ (a + 1) - 1 := by
    simpa [finiteGeometricPolynomial] using
      geom_sum_mul (X : Polynomial ℂ) (a + 1)
  rw [sub_mul]
  calc
    (finiteGeometricPolynomial (a + 1) * finiteGeometricPolynomial (a + 2)) *
          (X - 1) -
        X * finiteGeometricPolynomial a * finiteGeometricPolynomial (a + 1) * (X - 1) =
      finiteGeometricPolynomial (a + 1) *
          (finiteGeometricPolynomial (a + 2) * (X - 1)) -
        X * (finiteGeometricPolynomial a * (X - 1)) *
          finiteGeometricPolynomial (a + 1) := by ring
    _ = finiteGeometricPolynomial (a + 1) * (X ^ (a + 2) - 1) -
        X * (X ^ a - 1) * finiteGeometricPolynomial (a + 1) := by rw [ha2, ha0]
    _ = (finiteGeometricPolynomial (a + 1) * (X - 1)) *
        (X ^ (a + 1) + 1) := by ring
    _ = X ^ (2 * a + 2) - 1 := by rw [ha1]; ring

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Two-sided radial control -/

theorem re_div_sub_ge_neg_norm_div_one_sub_norm
    {w ζ : ℂ} (hw : ‖w‖ < 1) (hζ : ‖ζ‖ = 1) :
    -(‖w‖ / (1 - ‖w‖)) ≤ (w / (w - ζ)).re := by
  have hdenPos : 0 < 1 - ‖w‖ := sub_pos.mpr hw
  have hdist : 1 - ‖w‖ ≤ ‖w - ζ‖ := by
    rw [← hζ]
    rw [norm_sub_rev]
    exact norm_sub_norm_le ζ w
  have hdistPos : 0 < ‖w - ζ‖ := lt_of_lt_of_le hdenPos hdist
  have hnorm : ‖w / (w - ζ)‖ ≤ ‖w‖ / (1 - ‖w‖) := by
    rw [norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg w) hdenPos hdist
  have hre := Complex.abs_re_le_norm (w / (w - ζ))
  have hneg : -‖w / (w - ζ)‖ ≤ (w / (w - ζ)).re :=
    neg_le_of_abs_le hre
  linarith

theorem re_mul_derivative_div_ge_neg_natDegree_mul_norm_div_one_sub_norm_of_roots_unit
    (P : Polynomial ℂ) (hP : P ≠ 0)
    (hroots : ∀ ζ ∈ P.roots, ‖ζ‖ = 1)
    {w : ℂ} (hw : ‖w‖ < 1) :
    -((P.natDegree : ℝ) * (‖w‖ / (1 - ‖w‖))) ≤
      (w * (P.derivative.eval w / P.eval w)).re := by
  have hPw : P.eval w ≠ 0 := by
    intro h
    have hwmem : w ∈ P.roots := (Polynomial.mem_roots hP).2 h
    have := hroots w hwmem
    linarith
  have hsplits : P.Splits := IsAlgClosed.splits P
  have hlog := hsplits.eval_derivative_div_eval_of_ne_zero hPw
  have hcard : P.roots.card = P.natDegree := hsplits.natDegree_eq_card_roots.symm
  rw [hlog, ← Multiset.sum_map_mul_left]
  have hre := map_multiset_sum Complex.reCLM.toAddMonoidHom
    (Multiset.map (fun i => w * (1 / (w - i))) P.roots)
  change ((Multiset.map (fun i => w * (1 / (w - i))) P.roots).sum).re = _ at hre
  rw [hre, Multiset.map_map]
  change -((P.natDegree : ℝ) * (‖w‖ / (1 - ‖w‖))) ≤
    (Multiset.map (fun x => (w * (1 / (w - x))).re) P.roots).sum
  rw [show (Multiset.map (fun x => (w * (1 / (w - x))).re) P.roots).sum =
      (Multiset.map (fun x => (w / (w - x)).re) P.roots).sum by
    congr 1
    apply Multiset.map_congr rfl
    intro x _hx
    simp only [div_eq_mul_inv, one_mul]]
  calc
    -((P.natDegree : ℝ) * (‖w‖ / (1 - ‖w‖))) =
        (Multiset.map (fun _x : ℂ => -(‖w‖ / (1 - ‖w‖))) P.roots).sum := by
          simp [hcard, nsmul_eq_mul]
    _ ≤ (Multiset.map (fun x => (w / (w - x)).re) P.roots).sum := by
      exact Multiset.sum_map_le_sum_map _ _ fun ζ hζ =>
        re_div_sub_ge_neg_norm_div_one_sub_norm hw (hroots ζ hζ)


end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Reverse critical phase budget -/

/-- A unit-circle polynomial evaluated at the critical reverse phase. -/
def reverseCriticalUnitCirclePolynomialPhase
    (P : Polynomial ℂ) (L : ℝ) (z : ℂ) : ℂ :=
  P.eval (Complex.exp (I * (L : ℂ) * (-z + I / 2)))

/-- Explicit derivative of the critical reverse phase. -/
def reverseCriticalUnitCirclePolynomialPhaseDerivative
    (P : Polynomial ℂ) (L : ℝ) (z : ℂ) : ℂ :=
  let w := Complex.exp (I * (L : ℂ) * (-z + I / 2))
  (-I * (L : ℂ)) * w * P.derivative.eval w

theorem hasDerivAt_reverseCriticalUnitCirclePolynomialPhase
    (P : Polynomial ℂ) (L : ℝ) (z : ℂ) :
    HasDerivAt (reverseCriticalUnitCirclePolynomialPhase P L)
      (reverseCriticalUnitCirclePolynomialPhaseDerivative P L z) z := by
  let w : ℂ := Complex.exp (I * (L : ℂ) * (-z + I / 2))
  have hinner : HasDerivAt (fun u : ℂ => I * (L : ℂ) * (-u + I / 2))
      (-I * (L : ℂ)) z := by
    refine (((hasDerivAt_id z).neg.add_const (I / 2)).const_mul
      (I * (L : ℂ))).congr_deriv ?_
    ring
  have hw : HasDerivAt (fun u : ℂ =>
      Complex.exp (I * (L : ℂ) * (-u + I / 2)))
      ((-I * (L : ℂ)) * w) z := by
    refine ((Complex.hasDerivAt_exp
      (I * (L : ℂ) * (-z + I / 2))).comp z hinner).congr_deriv ?_
    dsimp only [w]
    ring
  unfold reverseCriticalUnitCirclePolynomialPhase
  refine ((P.hasDerivAt w).comp z hw).congr_deriv ?_
  dsimp only [reverseCriticalUnitCirclePolynomialPhaseDerivative, w]
  ring

/-- On every fixed left-strip fibre, the reverse critical phase has an upper current budget
linear in the degree. -/
theorem reverseCriticalUnitCirclePolynomialPhase_current_le
    (P : Polynomial ℂ) (hP : P ≠ 0)
    (hroots : ∀ ζ ∈ P.roots, ‖ζ‖ = 1)
    {L : ℝ} (hL : 0 ≤ L) {z : ℂ} (hz : z.im < 1 / 2) :
    (reverseCriticalUnitCirclePolynomialPhaseDerivative P L z *
      (starRingEnd ℂ) (reverseCriticalUnitCirclePolynomialPhase P L z)).im ≤
      L * (P.natDegree : ℝ) *
        (Real.exp (-L * (1 / 2 - z.im)) /
          (1 - Real.exp (-L * (1 / 2 - z.im)))) *
        Complex.normSq (reverseCriticalUnitCirclePolynomialPhase P L z) := by
  let w : ℂ := Complex.exp (I * (L : ℂ) * (-z + I / 2))
  have hgap : 0 < 1 / 2 - z.im := sub_pos.mpr hz
  have hwre : (I * (L : ℂ) * (-z + I / 2)).re = -L * (1 / 2 - z.im) := by
    rw [Complex.mul_re]
    have hILre : (I * (L : ℂ)).re = 0 := by simp [Complex.mul_re]
    have hILim : (I * (L : ℂ)).im = L := by simp [Complex.mul_im]
    rw [hILre, hILim]
    have him : (-z + I / 2).im = -z.im + 1 / 2 := by norm_num
    rw [him]
    ring
  have hwNorm : ‖w‖ = Real.exp (-L * (1 / 2 - z.im)) := by
    dsimp [w]
    rw [Complex.norm_exp, hwre]
  by_cases hL0 : L = 0
  · subst L
    simp [reverseCriticalUnitCirclePolynomialPhaseDerivative]
  have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
  have hwlt : ‖w‖ < 1 := by
    rw [hwNorm]
    calc
      Real.exp (-L * (1 / 2 - z.im)) < Real.exp 0 :=
        Real.exp_lt_exp.mpr (by nlinarith [mul_pos hLpos hgap])
      _ = 1 := Real.exp_zero
  have hPw : P.eval w ≠ 0 := by
    intro h
    have hwmem : w ∈ P.roots := (Polynomial.mem_roots hP).2 h
    have := hroots w hwmem
    linarith
  have hrad :=
    re_mul_derivative_div_ge_neg_natDegree_mul_norm_div_one_sub_norm_of_roots_unit
      P hP hroots hwlt
  have hnormP : 0 < Complex.normSq (P.eval w) := Complex.normSq_pos.mpr hPw
  have hderivative :
      reverseCriticalUnitCirclePolynomialPhaseDerivative P L z =
        (-I * (L : ℂ)) *
          (w * (P.derivative.eval w / P.eval w)) * P.eval w := by
    change (-I * (L : ℂ)) * w * P.derivative.eval w = _
    have hcancel :
        (w * (P.derivative.eval w / P.eval w)) * P.eval w =
          w * P.derivative.eval w := by
      rw [mul_assoc, div_mul_cancel₀ (P.derivative.eval w) hPw]
    calc
      (-I * (L : ℂ)) * w * P.derivative.eval w =
          (-I * (L : ℂ)) * (w * P.derivative.eval w) := by ring
      _ = (-I * (L : ℂ)) *
          ((w * (P.derivative.eval w / P.eval w)) * P.eval w) := by rw [hcancel]
      _ = _ := by ring
  have hphase : reverseCriticalUnitCirclePolynomialPhase P L z = P.eval w := rfl
  rw [hderivative, hphase]
  have halg :
      ((-I * (L : ℂ)) * (w * (P.derivative.eval w / P.eval w)) * P.eval w *
        (starRingEnd ℂ) (P.eval w)).im =
        -L * Complex.normSq (P.eval w) *
          (w * (P.derivative.eval w / P.eval w)).re := by
    rw [mul_assoc _ (P.eval w), mul_conj]
    simp [Complex.mul_im, Complex.normSq_apply]
    ring
  rw [halg]
  rw [hwNorm] at hrad
  have hcoef : 0 ≤ L * Complex.normSq (P.eval w) :=
    mul_nonneg hL (Complex.normSq_nonneg _)
  nlinarith


end

end GaloisForLFunctions.HTGeometry
