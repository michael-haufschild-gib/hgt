import GaloisForLFunctions.HTGeometry.GammaShiftDatum
import GaloisForLFunctions.HTGeometry.DigammaFieldValuationRational

/-!
# The algebra of shifted data, and an inhabited class

A datum against the shifted boundary shape multiplies on products and negates on inverses, exactly
as the signature `(16)` of the shifted law prescribes.  Together with the data of the generators —
a constant, a power of `Γ(s+λ)`, a power of the vertical logarithm, and a polynomial, whose datum is
its degree and its leading coefficient — this gives the datum of every shifted Gamma monomial with
rational coefficients.

So the hypothesis "the coefficients have shifted data", which carries the projective boundary, the
finite phase law and the zeta exclusion, is satisfied by an explicit family.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {σ lam : ℝ}

/-- A line function has a datum when its normalization against a shifted shape converges to a
nonzero constant. -/
def HasShiftDatum (lam σ : ℝ) (φ : ℝ → ℂ) (d : ℤ) (ω : ℝ) (b : ℤ) (c : ℂ) : Prop :=
  c ≠ 0 ∧ Tendsto (fun t : ℝ => φ t / gammaShiftShape lam σ d ω b t) atTop (nhds c)

/-- The trivial shape is one. -/
theorem gammaShiftShape_zero {t : ℝ} (ht : 3 ≤ t) :
    gammaShiftShape lam σ 0 0 0 t = 1 := by
  have htpos : (0 : ℝ) < t := by linarith
  rw [gammaShiftShape, zpow_zero, zpow_zero, Complex.ofReal_zero, Complex.cpow_zero]
  ring

/-- **Data multiply on products.** -/
theorem HasShiftDatum.mul (hσ : 0 < σ + lam) {φ χ : ℝ → ℂ} {d : ℤ} {ω : ℝ} {b : ℤ} {c : ℂ}
    {d' : ℤ} {ω' : ℝ} {b' : ℤ} {c' : ℂ}
    (h : HasShiftDatum lam σ φ d ω b c) (h' : HasShiftDatum lam σ χ d' ω' b' c') :
    HasShiftDatum lam σ (fun t => φ t * χ t) (d + d') (ω + ω') (b + b') (c * c') := by
  obtain ⟨hc, hlim⟩ := h
  obtain ⟨hc', hlim'⟩ := h'
  refine ⟨mul_ne_zero hc hc', ?_⟩
  refine (hlim.mul hlim').congr' ?_
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with t ht
  have hS : gammaShiftShape lam σ d ω b t ≠ 0 := gammaShiftShape_ne_zero hσ ht _ _ _
  have hS' : gammaShiftShape lam σ d' ω' b' t ≠ 0 := gammaShiftShape_ne_zero hσ ht _ _ _
  rw [← gammaShiftShape_mul hσ ht]
  field_simp

/-- **Inversion negates a datum.** -/
theorem HasShiftDatum.inv (hσ : 0 < σ + lam) {φ : ℝ → ℂ} {d : ℤ} {ω : ℝ} {b : ℤ} {c : ℂ}
    (h : HasShiftDatum lam σ φ d ω b c) :
    HasShiftDatum lam σ (fun t => (φ t)⁻¹) (-d) (-ω) (-b) c⁻¹ := by
  obtain ⟨hc, hlim⟩ := h
  refine ⟨inv_ne_zero hc, ?_⟩
  refine (hlim.inv₀ hc).congr' ?_
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with t ht
  have hS : gammaShiftShape lam σ d ω b t ≠ 0 := gammaShiftShape_ne_zero hσ ht _ _ _
  have hSneg : gammaShiftShape lam σ (-d) (-ω) (-b) t ≠ 0 := gammaShiftShape_ne_zero hσ ht _ _ _
  have hone : gammaShiftShape lam σ d ω b t * gammaShiftShape lam σ (-d) (-ω) (-b) t = 1 := by
    rw [gammaShiftShape_mul hσ ht]
    simpa using gammaShiftShape_zero ht
  have hSinv : gammaShiftShape lam σ (-d) (-ω) (-b) t = (gammaShiftShape lam σ d ω b t)⁻¹ :=
    eq_inv_of_mul_eq_one_right hone
  rw [hSinv, inv_div_inv, inv_div]

/-- **Division subtracts data.** -/
theorem HasShiftDatum.div (hσ : 0 < σ + lam) {φ χ : ℝ → ℂ} {d : ℤ} {ω : ℝ} {b : ℤ} {c : ℂ}
    {d' : ℤ} {ω' : ℝ} {b' : ℤ} {c' : ℂ}
    (h : HasShiftDatum lam σ φ d ω b c) (h' : HasShiftDatum lam σ χ d' ω' b' c') :
    HasShiftDatum lam σ (fun t => φ t / χ t) (d - d') (ω - ω') (b - b') (c / c') := by
  have hmul := h.mul hσ (h'.inv hσ)
  refine ⟨div_ne_zero h.1 h'.1, ?_⟩
  have heq : ∀ t : ℝ, φ t * (χ t)⁻¹ = φ t / χ t := fun t => (div_eq_mul_inv _ _).symm
  have hval : c * (c' : ℂ)⁻¹ = c / c' := (div_eq_mul_inv _ _).symm
  obtain ⟨-, hlim⟩ := hmul
  rw [hval] at hlim
  refine hlim.congr fun t => ?_
  show φ t * (χ t)⁻¹ / gammaShiftShape lam σ (d + -d') (ω + -ω') (b + -b') t
    = φ t / χ t / gammaShiftShape lam σ (d - d') (ω - ω') (b - b') t
  rw [← div_eq_mul_inv (φ t) (χ t), show d + -d' = d - d' by ring,
    show ω + -ω' = ω - ω' by ring, show b + -b' = b - b' by ring]

/-- A nonzero constant has the trivial datum. -/
theorem hasShiftDatum_const {c : ℂ} (hc : c ≠ 0) :
    HasShiftDatum lam σ (fun _ => c) 0 0 0 c := by
  refine ⟨hc, ?_⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with t ht
  rw [gammaShiftShape_zero ht, div_one]

/-- An integer power of the shifted Gamma has datum `(n, 0, 0)` with residue `1`. -/
theorem hasShiftDatum_gammaPow (hσ : 0 < σ + lam) (n : ℤ) :
    HasShiftDatum lam σ (fun t => gammaLine (σ + lam) t ^ n) n 0 0 1 := by
  refine ⟨one_ne_zero, ?_⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with t ht
  have hΓ : gammaLine (σ + lam) t ≠ 0 := gammaLine_ne_zero hσ t
  have htpos : (0 : ℝ) < t := by linarith
  rw [gammaShiftShape, Complex.ofReal_zero, Complex.cpow_zero, zpow_zero, one_mul, mul_one,
    div_self (zpow_ne_zero _ hΓ)]

/-- An integer power of the vertical logarithm has datum `(0, 0, b)` with residue `1`. -/
theorem hasShiftDatum_vertLogPow (b : ℤ) :
    HasShiftDatum lam σ (fun t => vertLog t ^ b) 0 0 b 1 := by
  refine ⟨one_ne_zero, ?_⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with t ht
  have hL : vertLog t ≠ 0 := vertLog_ne_zero_of_three_le ht
  rw [gammaShiftShape, Complex.ofReal_zero, Complex.cpow_zero, zpow_zero, one_mul, one_mul,
    div_self (zpow_ne_zero _ hL)]

/-- **A nonzero polynomial has a datum**: its degree is the argument exponent and its leading
coefficient is the residue. -/
theorem hasShiftDatum_poly (hσ : 0 < σ + lam) {q : Polynomial ℂ} (hq : q ≠ 0) :
    HasShiftDatum lam σ (fun t => q.eval ((σ : ℂ) + (t : ℂ) * Complex.I)) 0
      ((q.natDegree : ℕ) : ℝ) 0 q.leadingCoeff := by
  refine ⟨Polynomial.leadingCoeff_ne_zero.mpr hq, ?_⟩
  have hpoly := tendsto_eval_div_pow_natDegree_of_norm_atTop (tendsto_norm_vertical σ) q
  refine hpoly.congr' ?_
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with t ht
  have htpos : (0 : ℝ) < t := by linarith
  have hs : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := vertical_ne_zero_of_pos (σ := σ) htpos
  have hL : vertLog t ≠ 0 := vertLog_ne_zero_of_three_le ht
  have hΓ : gammaLine (σ + lam) t ≠ 0 := gammaLine_ne_zero hσ t
  refine congrArg (fun w => q.eval ((σ : ℂ) + (t : ℂ) * Complex.I) / w) ?_
  rw [gammaShiftShape, zpow_zero, zpow_zero, one_mul, mul_one,
    show (((q.natDegree : ℕ) : ℝ) : ℂ) = ((q.natDegree : ℕ) : ℂ) by push_cast; ring,
    Complex.cpow_natCast]

/-- **Every shifted Gamma monomial with rational coefficients has a datum.**  Its `Γ`-degree is the
power of `Γ(s+λ)`, its real argument exponent is the degree difference of the two polynomials, its
logarithm exponent is the power of `log s`, and its residue is the constant times the quotient of
the leading coefficients. -/
theorem hasShiftDatum_monomial (hσ : 0 < σ + lam) {c : ℂ} (hc : c ≠ 0) (n : ℤ)
    {q p : Polynomial ℂ} (hq : q ≠ 0) (hp : p ≠ 0) (b : ℤ) :
    HasShiftDatum lam σ
      (fun t => c * gammaLine (σ + lam) t ^ n
        * (q.eval ((σ : ℂ) + (t : ℂ) * Complex.I) / p.eval ((σ : ℂ) + (t : ℂ) * Complex.I))
        * vertLog t ^ b)
      n (((q.natDegree : ℕ) : ℝ) - ((p.natDegree : ℕ) : ℝ)) b
      (c * (q.leadingCoeff / p.leadingCoeff)) := by
  have hconst := hasShiftDatum_const (lam := lam) (σ := σ) hc
  have hgam := hasShiftDatum_gammaPow (lam := lam) (σ := σ) hσ n
  have hratio := (hasShiftDatum_poly (lam := lam) hσ hq).div hσ (hasShiftDatum_poly hσ hp)
  have hlog := hasShiftDatum_vertLogPow (lam := lam) (σ := σ) b
  have hstep := ((hconst.mul hσ hgam).mul hσ hratio).mul hσ hlog
  have hd : (0 : ℤ) + n + (0 - 0) + 0 = n := by ring
  have hω : (0 : ℝ) + 0 + (((q.natDegree : ℕ) : ℝ) - ((p.natDegree : ℕ) : ℝ)) + 0
      = ((q.natDegree : ℕ) : ℝ) - ((p.natDegree : ℕ) : ℝ) := by ring
  have hb : (0 : ℤ) + 0 + (0 - 0) + b = b := by ring
  have hcc : c * 1 * (q.leadingCoeff / p.leadingCoeff) * 1
      = c * (q.leadingCoeff / p.leadingCoeff) := by ring
  rw [hd, hω, hb, hcc] at hstep
  exact hstep

end

end GaloisForLFunctions.HTGeometry
