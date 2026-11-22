import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing.MissingDirection
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing.RankCorrection

/-!
# Fourth traces of thermal hyperplane omissions

One omitted heat packet changes the squared critical heat by a single
rank-one operator. Its trace involves ordinary partition readings at three
successive real temperatures. Every off-diagonal shell entry of the square
is nonzero.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace ComplexConjugate

/-- Inverse temperature of the squared packet amplitude. -/
def massParameter (s : HeatVectorDomain) : ℂ := conj s.val+s.val

theorem massParameter_real (s : HeatVectorDomain) : massParameter s = ((2*s.val.re:ℝ):ℂ) := by
  apply Complex.ext <;> simp [massParameter,two_mul]

private theorem mass_advanced (s : HeatVectorDomain) :
    massParameter (advanced s) = massParameter s+1 := by
  simp only [massParameter,advanced,map_add,map_div₀,map_one,map_ofNat]
  ring

private theorem packet_mass (s : HeatVectorDomain) :
    inner ℂ (packet s) (packet s) = riemannZeta (massParameter s) :=
  groundState_overlap_zeta s s

private theorem packet_norm (s : HeatVectorDomain) :
    ((‖packet s‖^2:ℝ):ℂ) = riemannZeta (massParameter s) :=
  (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (packet s)).symm.trans (packet_mass s)

private theorem packet_mass_ne_zero (s : HeatVectorDomain) : riemannZeta (massParameter s) ≠ 0 := by
  rw [← packet_norm]
  exact Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr
    (_root_.RHTower.PrimeCoShift.groundState_ne_zero s.property)))

private theorem adjoint_critical : adjoint criticalOperator = criticalOperator :=
  critical_isPositive.isSelfAdjoint.star_eq

/-- The exact rank-one correction to the squared physical propagator. -/
theorem omitted_packet_square (s : HeatVectorDomain) :
    (projected (omitLine (packet s)))^2 = squareHeat.val -
      (riemannZeta (massParameter s))⁻¹ • rankOne ℂ (packet (advanced s)) (packet (advanced s)) := by
  rw [projected_square,← critical_packet]
  apply ContinuousLinearMap.ext
  intro f
  change criticalOperator ((ℂ ∙ packet s)ᗮ.starProjection (criticalOperator f)) =
    criticalOperator (criticalOperator f) -
      (riemannZeta (massParameter s))⁻¹ • ((inner ℂ (criticalOperator (packet s)) f) • criticalOperator (packet s))
  rw [Submodule.starProjection_orthogonal',sub_apply,one_apply,Submodule.starProjection_singleton,
    packet_norm,map_sub,map_smul,smul_smul,div_eq_inv_mul]
  rw [← adjoint_inner_left criticalOperator f (packet s),adjoint_critical]

/-- Omitting a heat packet changes the fourth trace by a ratio of three adjacent partition values. -/
theorem omitted_packet_trace (s : HeatVectorDomain) :
    let w := massParameter s
    opTrace ((projected (omitLine (packet s)))^4) =
      riemannZeta 2-2*riemannZeta (w+2)/riemannZeta w+(riemannZeta (w+1)/riemannZeta w)^2 := by
  let v := packet (advanced s)
  have hv : inner ℂ v v = riemannZeta (massParameter s+1) := by rw [packet_mass,mass_advanced]
  have ha : inner ℂ v (squareHeat.val v) = riemannZeta (massParameter s+2) := by
    change inner ℂ v (criticalOperator (criticalOperator v)) = _
    rw [← adjoint_inner_left criticalOperator (criticalOperator v) v,adjoint_critical]
    change inner ℂ (criticalOperator (packet (advanced s))) (criticalOperator (packet (advanced s))) = _
    rw [critical_packet,packet_mass,mass_advanced,mass_advanced]
    congr 1
    ring
  change opTrace (((projected (omitLine (packet s)))^2)^2) = _
  rw [omitted_packet_square,rank_one_trace_square squareHeat v,ha,hv]
  change opTrace ((criticalOperator^2)^2) - _ + _ = _
  rw [critical_fourth_trace]
  simp only [div_eq_mul_inv]
  ring

/-- At the reciprocal state the trace uses the second, third and fourth integer partition values. -/
theorem reciprocal_fourth_trace :
    opTrace ((projected (omitLine (packet ⟨1,by norm_num⟩)))^4) =
      riemannZeta 2-2*riemannZeta 4/riemannZeta 2+(riemannZeta 3/riemannZeta 2)^2 := by
  have he := omitted_packet_trace ⟨1,by norm_num⟩
  norm_num only [massParameter,map_one] at he
  exact he

/-- Squared propagation connects each pair of distinct occupation shells. -/
theorem omitted_packet_mixes (s : HeatVectorDomain) (ij : {ij : ℕ × ℕ // ij.1 ≠ ij.2}) :
    coefficients ((projected (omitLine (packet s)))^2) ij.val.1 ij.val.2 ≠ 0 := by
  let i := number ij.val.1
  let j := number ij.val.2
  have hij : i ≠ j := fun he => ij.property (number_injective he)
  rw [omitted_packet_square]
  change ((squareHeat.val (lp.single 2 j (1:ℂ))) -
    (riemannZeta (massParameter s))⁻¹ • ((inner ℂ (packet (advanced s)) (lp.single 2 j (1:ℂ))) • packet (advanced s))) i ≠ 0
  rw [lp.coeFn_sub,Pi.sub_apply,lp.coeFn_smul,Pi.smul_apply,lp.coeFn_smul,Pi.smul_apply,
    lp.inner_single_right,RCLike.inner_apply,one_mul]
  change (criticalOperator^2) (lp.single 2 j (1:ℂ)) i - _ ≠ 0
  rw [critical_square_apply,lp.single_apply,Pi.single_eq_of_ne hij,mul_zero,zero_sub,neg_ne_zero]
  change (riemannZeta (massParameter s))⁻¹*(conj (packet (advanced s) j)*packet (advanced s) i) ≠ 0
  rw [packet_apply,packet_apply]
  exact mul_ne_zero (inv_ne_zero (packet_mass_ne_zero s))
    (mul_ne_zero (map_ne_zero _ (Complex.exp_ne_zero _)) (Complex.exp_ne_zero _))

#print axioms omitted_packet_square
#print axioms omitted_packet_trace
#print axioms reciprocal_fourth_trace
#print axioms omitted_packet_mixes

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
