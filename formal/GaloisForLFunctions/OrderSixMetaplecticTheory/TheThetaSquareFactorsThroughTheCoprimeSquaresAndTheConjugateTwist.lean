import GaloisForLFunctions.OrderSixMetaplecticTheory.TheConjugateCubicTwistAndTheCoprimeSquaresShareTheDoublePole

/-!
# The theta square factors through the q-coprime squares and the conjugate twist

Patterson's relations at an odd primary prime q (ρ = |q|, t = ρ^{−s}): T(xq³) = ρT(x), T(xq²) = 0 for q ∤ x. Splitting
the squared theta series D(s) = Σ T(h)²(4π|ξ_h|)^{−s} by v_q(h) ∈ {0}, {1}, {2}, [3, ∞) gives (`thetaSq_euler`)

(1 − ρ²t³) D(s) = D_{cop}(s) + t D_q(s),   D_q(s) = Σ_{q∤x} T(xq)²(4π|ξ_x|)^{−s}.

With T(xq) = g₂(9x)T(x)/ρ and the Gauss-sum shifts g(x) = χ(x)⁻¹g₁, g₂(9x) = χ²(9x)⁻¹g₂, one has
g₁ g₂(9x)² = χ(9)⁻¹g₂² g(x) (`gauss_sq_shift`), so g₁D_q = ρ⁻²χ(9)⁻¹g₂² D_g (`gaussDirichlet_pCoeff`): the q-divisible
part of θ² is the **conjugate twist**. The Gauss sums have |g₁| = |g₂| = ρ and N(q) = ρ² (`norm_gaussAt_one`, `card_res_eq`).
-/

noncomputable section

open Filter Function Topology
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-! ### Gauss sums at shifted frequencies -/

/-- g₂(h) = Σ_u χ²(u)ψ(uh). -/
def gaussAt2 (h : O) : ℂ := ∑ u : P.Res, (P.chi ^ 2) u * P.traceChar (u * P.res h)

theorem mulChar_inv_apply (χ' : MulChar P.Res ℂ) (a : P.Res) (ha : a ≠ 0) : χ' a⁻¹ = (χ' a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel₀ ha, MulChar.map_one])

theorem sum_mulChar_shift (χ' : MulChar P.Res ℂ) (a c : P.Res) (ha : a ≠ 0) :
    ∑ u : P.Res, χ' u * P.traceChar (u * (a * c)) = (χ' a)⁻¹ * ∑ u : P.Res, χ' u * P.traceChar (u * c) := by
  rw [← (mulRight_bijective₀ a⁻¹ (inv_ne_zero ha)).sum_comp (fun u => χ' u * P.traceChar (u * (a * c))),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_mul, P.mulChar_inv_apply χ' a ha, show v * a⁻¹ * (a * c) = v * c by field_simp]
  ring

/-- g(h) = χ(h)⁻¹g₁ (both sides vanish when q ∣ h). -/
theorem gaussAt_eq (h : O) : P.gaussAt h = (P.chi (P.res h))⁻¹ * P.gaussAt 1 := by
  by_cases hh : P.res h = 0
  · rw [hh, MulChar.map_zero, inv_zero, zero_mul, gaussAt, hh]
    simp only [mul_zero, AddChar.map_zero_eq_one, mul_one]
    exact MulChar.sum_eq_zero_of_ne_one P.chi_ne_one
  · have := P.sum_mulChar_shift P.chi (P.res h) 1 hh
    simp only [mul_one] at this
    simp only [gaussAt, map_one, mul_one]
    exact this

/-- g₂(9h) = χ²(9h)⁻¹g₂ for q ∤ h. -/
theorem gaussAt2_eq (h : O) (hh : ¬ P.p ∣ h) :
    P.gaussAt2 (9 * h) = ((P.chi ^ 2) (9 * P.res h))⁻¹ * P.gaussAt2 1 := by
  have hx : P.res h ≠ 0 := fun h0 => hh ((P.res_eq_zero_iff h).mp h0)
  have ha : (9 : P.Res) * P.res h ≠ 0 := mul_ne_zero P.nine_ne_zero' hx
  have := P.sum_mulChar_shift (P.chi ^ 2) (9 * P.res h) 1 ha
  simp only [mul_one] at this
  simp only [gaussAt2, map_one, mul_one]
  rw [show P.res (9 * h) = 9 * P.res h by rw [map_mul, map_ofNat]]
  exact this

/-- **The square shift.** g₁ g₂(9h)² = χ(9)⁻¹g₂² g(h) for q ∤ h. -/
theorem gauss_sq_shift (h : O) (hh : ¬ P.p ∣ h) :
    P.gaussAt 1 * P.gaussAt2 (9 * h) ^ 2 = (P.chi 9)⁻¹ * P.gaussAt2 1 ^ 2 * P.gaussAt h := by
  have hx : P.res h ≠ 0 := fun h0 => hh ((P.res_eq_zero_iff h).mp h0)
  have h9 := P.nine_ne_zero'
  have hA := P.chi_cube 9 h9
  have hB := P.chi_cube (P.res h) hx
  rw [P.gaussAt2_eq h hh, P.gaussAt_eq h, MulChar.pow_apply' _ (by norm_num), map_mul, P.chi_inv_eq_sq 9 h9,
    P.chi_inv_eq_sq _ hx]
  have e : ((P.chi 9 * P.chi (P.res h)) ^ 2)⁻¹ = P.chi 9 * P.chi (P.res h) := by
    refine inv_eq_of_mul_eq_one_right ?_
    linear_combination (P.chi (P.res h) ^ 3) * hA + hB
  rw [e]
  ring

/-! ### Norms -/

theorem card_res_eq : (Fintype.card P.Res : ℝ) = ‖ringComplex P.p‖ ^ 2 := by
  have h : Fintype.card P.Res = Ideal.absNorm (Ideal.span {P.p}) := by
    simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [ringComplex_norm_sq_eq_absNorm_span, h]

theorem norm_gaussSum_traceChar (χ' : MulChar P.Res ℂ) (hχ : χ' ≠ 1) :
    ‖gaussSum χ' P.traceChar‖ = ‖ringComplex P.p‖ := by
  have h := gaussSum_mul_gaussSum_eq_card hχ (principalTraceChar_primitive P.p P.ne_zero)
  rw [← star_gaussSum_eq] at h
  have hn : (‖gaussSum χ' P.traceChar‖ : ℂ) ^ 2 = (Fintype.card P.Res : ℂ) := by
    rw [← Complex.conj_mul', mul_comm]
    exact h
  have hr : ‖gaussSum χ' P.traceChar‖ ^ 2 = ‖ringComplex P.p‖ ^ 2 := by
    rw [← P.card_res_eq]
    exact_mod_cast hn
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hr

theorem gaussAt_one_eq : P.gaussAt 1 = gaussSum P.chi P.traceChar := by
  simp only [gaussAt, map_one, mul_one, gaussSum]

theorem gaussAt2_one_eq : P.gaussAt2 1 = gaussSum (P.chi ^ 2) P.traceChar := by
  simp only [gaussAt2, map_one, mul_one, gaussSum]

theorem norm_gaussAt_one : ‖P.gaussAt 1‖ = ‖ringComplex P.p‖ := by
  rw [P.gaussAt_one_eq]
  exact P.norm_gaussSum_traceChar _ P.chi_ne_one

theorem norm_gaussAt2_one : ‖P.gaussAt2 1‖ = ‖ringComplex P.p‖ := by
  rw [P.gaussAt2_one_eq]
  exact P.norm_gaussSum_traceChar _ P.chi_sq_ne_one

theorem gaussAt_one_ne_zero : P.gaussAt 1 ≠ 0 := by
  intro h
  have := P.norm_gaussAt_one
  rw [h, norm_zero] at this
  exact P.norm_pos.ne' this.symm

/-! ### Patterson's relation through the conjugate twist -/

theorem primeCubicGauss_two (h : O) : primeCubicGauss P.p P.prime P.primary 2 h = P.gaussAt2 h := by
  rw [primeCubicGauss_eq_gaussSum, gaussSum, gaussAt2]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [show residueTraceQuotientChar h P.p P.prime.ne_zero = P.psi h from rfl, P.psi_eq_traceChar]

/-- The q-divisible coefficients T(xq)² on x coprime to q. -/
def pCoeff (h : O) : ℂ := if P.p ∣ h then 0 else rationalSourceResidualFourierCoefficient (h * P.p) ^ 2

theorem pCoeff_gauss (h : O) : P.gaussAt 1 * P.pCoeff h =
    (P.chi 9)⁻¹ * P.gaussAt2 1 ^ 2 * ((‖ringComplex P.p‖ : ℂ) ^ 2)⁻¹ * P.gaussCoeff h := by
  have hP : (‖ringComplex P.p‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr P.norm_pos.ne'
  unfold pCoeff gaussCoeff
  split_ifs with hh
  · have h0 : P.res h = 0 := (P.res_eq_zero_iff h).mpr hh
    rw [P.gaussAt_eq h, h0, MulChar.map_zero, inv_zero]
    ring
  · rw [rationalSourceResidualFourierCoefficient_prime_factor P.p P.prime P.primary h hh, P.primeCubicGauss_two,
      div_mul_eq_mul_div, div_pow]
    have key := P.gauss_sq_shift h hh
    field_simp
    linear_combination (rationalSourceResidualFourierCoefficient h ^ 2) * key

theorem gaussDirichlet_pCoeff (s : ℂ) : P.gaussAt 1 * besselDirichlet P.pCoeff s =
    (P.chi 9)⁻¹ * P.gaussAt2 1 ^ 2 * ((‖ringComplex P.p‖ : ℂ) ^ 2)⁻¹ * besselDirichlet P.gaussCoeff s := by
  rw [besselDirichlet, besselDirichlet, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun h => ?_
  split_ifs
  · ring
  · rw [← mul_assoc, P.pCoeff_gauss]
    ring

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
