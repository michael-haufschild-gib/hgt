import GaloisForLFunctions.HTGeometry.CharacteristicModeDimension
import GaloisForLFunctions.HTGeometry.RealAnalyticZeroFiniteness

/-!
# The interior trace of a CCM screw solution is a finite characteristic packet

Four exact mechanisms of the card are formalized.

*The real characteristic set is finite.*  The corrected polar–Euler–Gamma symbol grows like
`log |ξ|`, so all of its real zeros lie in a compact interval; a real-analytic function that is not
identically zero has finitely many zeros there.

*The damped rational factor.*  With `b = p/(1+ξ²)^L` the local differential operator `(1+D²)^L`
restores the polynomial exactly: `(1+ξ²)^L b(ξ) = p(ξ)`.  This is `(11)`.

*The zero-free multiplier is invertible.*  A symbol bounded away from zero is an injective
multiplier with the explicit inverse multiplier `1/c`, and the factorization `W = b·c` turns the
null equation `W(D)u = 0` into `p(D)v = 0` with `v = c(D)u`.  This is `(4)`, `(5)`, `(10)` and `(8)`.

*The interior packet is finite-dimensional of dimension `d_a`.*  Passing from the symbol variable to
the derivative variable sends `p_a` to a polynomial whose roots are `i τ`, `τ` a real characteristic
crossing, with multiplicity `ν_τ`; the solution space of that operator has dimension exactly
`∑_τ ν_τ = d_a`.  This is `(9)` and the dimension count, carried by
`HTGeometry/CharacteristicModeDimension.lean`.

The distributional localization to `D'(I)`, the smooth extension of `W/b` across each crossing, and
the exterior Evans relation are cited analytic parents and stay outside the Lean statement.
-/

open Complex Filter Set

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The real characteristic set is finite -/

/-- **Equation (2), consequence.**  A real-analytic symbol that tends to `+∞` at infinity has a
finite real zero set: growth confines the zeros to a compact interval, and a nonzero real-analytic
function has no accumulating zero. -/
theorem finite_realZeroSet_of_tendsto_atTop {W : ℝ → ℝ}
    (hW : AnalyticOnNhd ℝ W Set.univ)
    (hgrow : Filter.Tendsto W (Filter.cocompact ℝ) Filter.atTop) :
    {ξ : ℝ | W ξ = 0}.Finite := by
  have hev : ∀ᶠ ξ in Filter.cocompact ℝ, 0 < W ξ :=
    hgrow (Filter.eventually_gt_atTop 0)
  have hpos : {ξ : ℝ | 0 < W ξ} ∈ Filter.cocompact ℝ := hev
  obtain ⟨K, hK, hKsub⟩ := Filter.mem_cocompact.mp hpos
  obtain ⟨x₀, hx₀⟩ := hev.exists
  have hzsub : {ξ : ℝ | W ξ = 0} ⊆ K ∩ W ⁻¹' {0} := by
    intro ξ hξ
    refine ⟨?_, hξ⟩
    by_contra hK'
    have := hKsub hK'
    rw [Set.mem_setOf_eq] at this hξ
    rw [hξ] at this
    exact lt_irrefl 0 this
  refine Set.Finite.subset ?_ hzsub
  exact GaloisForLFunctions.HTGeometry.finite_zeros_of_analyticOnNhd isPreconnected_univ hW
    (Set.mem_univ x₀) (ne_of_gt hx₀) hK (Set.subset_univ K)

/-! ## The damped rational factor -/

theorem one_add_sq_ne_zero (ξ : ℝ) : (1 : ℂ) + (ξ : ℂ) ^ 2 ≠ 0 := by
  have hcast : (1 : ℂ) + (ξ : ℂ) ^ 2 = ((1 + ξ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hcast]
  exact Complex.ofReal_ne_zero.mpr (by positivity)

/-- The damped rational factor `(4)`, `b_a = p_a/(1+ξ²)^{L_a}`. -/
def dampedFactor (p : Polynomial ℂ) (N : ℕ) (ξ : ℝ) : ℂ :=
  p.eval (ξ : ℂ) / ((1 : ℂ) + (ξ : ℂ) ^ 2) ^ N

/-- **Equation (11).**  The local differential operator `(1+D²)^{L}` restores the polynomial
factor exactly. -/
theorem localOperator_dampedFactor (p : Polynomial ℂ) (N : ℕ) (ξ : ℝ) :
    ((1 : ℂ) + (ξ : ℂ) ^ 2) ^ N * dampedFactor p N ξ = p.eval (ξ : ℂ) := by
  rw [dampedFactor, mul_div_cancel₀]
  exact pow_ne_zero _ (one_add_sq_ne_zero ξ)

theorem dampedFactor_ne_zero {p : Polynomial ℂ} {N : ℕ} {ξ : ℝ} (h : p.eval (ξ : ℂ) ≠ 0) :
    dampedFactor p N ξ ≠ 0 := by
  rw [dampedFactor]
  exact div_ne_zero h (pow_ne_zero _ (one_add_sq_ne_zero ξ))

/-! ## The zero-free multiplier -/

/-- The corrected symbol quotient `(4)`, `c_a = W_a/b_a`. -/
def symbolQuotient (W b : ℝ → ℂ) : ℝ → ℂ := fun ξ => W ξ / b ξ

/-- **Equation (4).**  Away from the zeros of the damped factor the quotient reproduces the
symbol. -/
theorem symbolQuotient_mul {W b : ℝ → ℂ} {ξ : ℝ} (hb : b ξ ≠ 0) :
    symbolQuotient W b ξ * b ξ = W ξ := by
  rw [symbolQuotient, div_mul_cancel₀ _ hb]

/-- **Equation (5), injectivity.**  A symbol bounded away from zero is an injective multiplier. -/
theorem multiplier_injective {c : ℝ → ℂ} {m : ℝ} (hm : 0 < m) (hc : ∀ ξ, m ≤ ‖c ξ‖)
    {u v : ℝ → ℂ} (h : ∀ ξ, c ξ * u ξ = c ξ * v ξ) : u = v := by
  funext ξ
  have hcξ : c ξ ≠ 0 := by
    intro h0
    have := hc ξ
    rw [h0, norm_zero] at this
    linarith
  exact mul_left_cancel₀ hcξ (h ξ)

/-- **Equation (5), inverse multiplier.**  The reciprocal symbol inverts the multiplier
pointwise. -/
theorem inverse_multiplier {c : ℝ → ℂ} {m : ℝ} (hm : 0 < m) (hc : ∀ ξ, m ≤ ‖c ξ‖)
    (u : ℝ → ℂ) (ξ : ℝ) : (c ξ)⁻¹ * (c ξ * u ξ) = u ξ := by
  have hcξ : c ξ ≠ 0 := by
    intro h0
    have := hc ξ
    rw [h0, norm_zero] at this
    linarith
  rw [← mul_assoc, inv_mul_cancel₀ hcξ, one_mul]

/-! ## The interior reduction -/

/-- **Equations (6), (7), (10), (11) ⟹ (8).**  On the symbol side, a null vector of the complete
symbol is a null vector of the polynomial factor after the invertible change of variable. -/
theorem polynomial_symbol_eq_zero {W c u v : ℝ → ℂ} {p : Polynomial ℂ} {N : ℕ}
    (hW : ∀ ξ, W ξ = dampedFactor p N ξ * c ξ)
    (hv : ∀ ξ, v ξ = c ξ * u ξ)
    (hzero : ∀ ξ, W ξ * u ξ = 0) (ξ : ℝ) :
    p.eval (ξ : ℂ) * v ξ = 0 := by
  have hstep : p.eval (ξ : ℂ) * v ξ
      = ((1 : ℂ) + (ξ : ℂ) ^ 2) ^ N * (W ξ * u ξ) := by
    rw [← localOperator_dampedFactor p N ξ, hv, hW]
    ring
  rw [hstep, hzero, mul_zero]

/-! ## The characteristic packet in the derivative variable -/

/-- The characteristic mode polynomial `(3)` written in the derivative variable: the real crossing
`τ` becomes the frequency `i τ`. -/
def modePoly (Z : Finset ℝ) (ν : ℝ → ℕ) : Polynomial ℂ :=
  ∏ τ ∈ Z, (Polynomial.X - Polynomial.C (Complex.I * (τ : ℂ))) ^ ν τ

theorem modePoly_ne_zero (Z : Finset ℝ) (ν : ℝ → ℕ) : modePoly Z ν ≠ 0 := by
  rw [modePoly]
  refine Finset.prod_ne_zero_iff.mpr fun τ _ => pow_ne_zero _ ?_
  exact Polynomial.X_sub_C_ne_zero _

/-- **Equation (3).**  The packet degree is the total crossing multiplicity `d_a`. -/
theorem natDegree_modePoly (Z : Finset ℝ) (ν : ℝ → ℕ) :
    (modePoly Z ν).natDegree = ∑ τ ∈ Z, ν τ := by
  rw [modePoly, Polynomial.natDegree_prod _ _ (fun τ _ => pow_ne_zero _
    (Polynomial.X_sub_C_ne_zero _))]
  exact Finset.sum_congr rfl fun τ _ => by
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]

/-- **Equation (9), multiplicities.**  The multiplicity of the frequency `i τ` is exactly the
analytic multiplicity `ν_τ` of the crossing. -/
theorem rootMultiplicity_modePoly {Z : Finset ℝ} {ν : ℝ → ℕ} {τ : ℝ} (hτ : τ ∈ Z) :
    (modePoly Z ν).rootMultiplicity (Complex.I * (τ : ℂ)) = ν τ := by
  classical
  set M : Polynomial ℂ :=
    ∏ κ ∈ Z.erase τ, (Polynomial.X - Polynomial.C (Complex.I * (κ : ℂ))) ^ ν κ with hM
  have hfac : modePoly Z ν = M * (Polynomial.X - Polynomial.C (Complex.I * (τ : ℂ))) ^ ν τ := by
    rw [modePoly, hM, Finset.prod_erase_mul _ _ hτ]
  have hMroot : ¬ M.IsRoot (Complex.I * (τ : ℂ)) := by
    rw [Polynomial.IsRoot, hM, Polynomial.eval_prod]
    refine Finset.prod_ne_zero_iff.mpr fun κ hκ => ?_
    have hκτ : κ ≠ τ := (Finset.mem_erase.mp hκ).1
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    refine pow_ne_zero _ (sub_ne_zero.mpr ?_)
    intro hcon
    exact hκτ (by exact_mod_cast (mul_left_cancel₀ Complex.I_ne_zero hcon).symm)
  have hMzero : M ≠ 0 := fun h => hMroot (by rw [h]; simp)
  rw [hfac, Polynomial.rootMultiplicity_mul
    (mul_ne_zero hMzero (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _))),
    Polynomial.rootMultiplicity_eq_zero hMroot, Polynomial.rootMultiplicity_X_sub_C_pow, zero_add]

/-- **Equation (9), the mode basis.**  Every characteristic mode `x^k e^{i τ x}` with `k < ν_τ`
solves the reduced interior equation. -/
theorem realConstCoeffOp_charMode_modePoly {Z : Finset ℝ} {ν : ℝ → ℕ} {τ : ℝ} (hτ : τ ∈ Z)
    {k : ℕ} (hk : k < ν τ) :
    GaloisForLFunctions.HTGeometry.realConstCoeffOp (modePoly Z ν)
      (GaloisForLFunctions.HTGeometry.charMode (Complex.I * (τ : ℂ)) k) = 0 :=
  GaloisForLFunctions.HTGeometry.realConstCoeffOp_charMode
    (by rw [rootMultiplicity_modePoly hτ]; exact hk)

/-- **Equation (9) and the dimension count.**  The ambient interior solution space of the reduced
equation has dimension exactly `d_a = ∑_τ ν_τ`. -/
theorem finrank_characteristicPacket (Z : Finset ℝ) (ν : ℝ → ℕ) :
    Module.finrank ℂ (GaloisForLFunctions.HTGeometry.solutionSpace (modePoly Z ν))
      = ∑ τ ∈ Z, ν τ := by
  rw [GaloisForLFunctions.HTGeometry.finrank_solutionSpace (modePoly_ne_zero Z ν),
    natDegree_modePoly]

/-- **Equation (9), exhaustiveness.**  Every smooth interior solution is a finite sum of blocks
whose frequencies are among the `i τ` and whose degrees are below the crossing multiplicities. -/
theorem exists_characteristic_packet {Z : Finset ℝ} {ν : ℝ → ℕ} {v : ℝ → ℂ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hzero : GaloisForLFunctions.HTGeometry.realConstCoeffOp (modePoly Z ν) v = 0) :
    ∃ (S : Finset ℂ) (P : ℂ → Polynomial ℂ),
      v = ∑ μ ∈ S, GaloisForLFunctions.HTGeometry.polyExp (P μ) μ ∧
        ∀ μ ∈ S, P μ ≠ 0 → (modePoly Z ν).eval μ = 0 ∧
          (P μ).natDegree < (modePoly Z ν).rootMultiplicity μ :=
  GaloisForLFunctions.HTGeometry.exists_characteristic_modes hv (modePoly_ne_zero Z ν) hzero

end GaloisForLFunctions.RHTower

end
