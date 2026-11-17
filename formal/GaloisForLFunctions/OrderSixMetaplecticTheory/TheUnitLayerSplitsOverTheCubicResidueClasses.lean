import GaloisForLFunctions.OrderSixMetaplecticTheory.TheUnitLayerOfThePrincipalTwistHasASimplePole
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheCubicLayerOfTheFamilyAtColumnOneReachesTheUnitLayer

/-!
# The unit layer splits over the cubic residue classes

For an odd primary prime `q` and a cube root of unity `c`, the unit layer restricted to the ideals whose primary
generator lies in the cubic class `χ_q(gen A) = c`,

`S^{[c]}_1(w) = Σ_{χ_q(gen A) = c} σ(A)N(A)^{−w}`   (`classSeries`),

is `⅓(S^{1_q}_1 + c̄S^{χ_q}_1 + c̄²S^{χ̄_q}_1)` (`classSeries_eq`): the indicator of a cubic class is the average of the
three characters of the cubic grade. All three unit layers have simple poles at `w = 2/3` (shifted Hecke and
fractional traces, the selector on the coprime squares), with residues that are local multiples of `Res S₁`
(`twistUnitResidue_closed`, `conjUnitResidue_eq_mul`, `principalUnitResidue_eq_mul`). Hence (`classSeries_simple_pole`,
`classUnitResidue_eq`):

`Res_{w=2/3} S^{[c]}_1 = ⅓(N^{4/3}χ(−4)χ(9)⁻¹/A_q + c̄·2N^{5/6}/(N + 1)·\overline{(9/q)₃}G̃(q) + c̄²·NJ_q/(g(χ_q)A_q))·Res S₁`,

`N = N(q)`, `A_q = A_q(4/3)`: the squared Gauss sums are distributed over the cubic classes modulo `q` with an explicit
main term in each class, its class dependence carried by the Gauss sum `G̃(q)` and the Jacobi sum `J_q`.
-/

noncomputable section

open Filter Topology
open scoped BigOperators Classical

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

/-- The indicator of a cube root of unity among the cube roots of unity. -/
theorem cube_root_indicator (c ζ : ℂ) (hc : c ^ 3 = 1) (hζ : ζ ^ 3 = 1) :
    (if ζ = c then (1 : ℂ) else 0) = 1 / 3 * (1 + c⁻¹ * ζ + c⁻¹ ^ 2 * ζ⁻¹) := by
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num)] at hc
    exact zero_ne_one hc
  have hζ0 : ζ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num)] at hζ
    exact zero_ne_one hζ
  have hci : c⁻¹ ^ 3 = 1 := by rw [inv_pow, hc, inv_one]
  have hζζ : ζ * ζ ^ 2 = 1 := by
    rw [← pow_succ']
    exact hζ
  have hζi : ζ⁻¹ = ζ ^ 2 := (eq_inv_of_mul_eq_one_right hζζ).symm
  split_ifs with h
  · rw [h, inv_mul_cancel₀ hc0]
    have hc3 : c⁻¹ ^ 2 * c⁻¹ = 1 := by
      rw [← pow_succ]
      exact hci
    rw [hc3]
    norm_num
  · set u := c⁻¹ * ζ with hu
    have hu3 : u ^ 3 = 1 := by rw [hu, mul_pow, hci, hζ, one_mul]
    have hu1 : u ≠ 1 := by
      intro h1
      apply h
      have := congrArg (fun x => c * x) h1
      simp only [hu, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul, mul_one] at this
      exact this
    have hsq : c⁻¹ ^ 2 * ζ⁻¹ = u ^ 2 := by rw [hζi, hu, mul_pow]
    have hsum : 1 + u + u ^ 2 = 0 := by
      have h0 : (u - 1) * (1 + u + u ^ 2) = 0 := by linear_combination hu3
      exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hu1)
    rw [hsq]
    linear_combination (-(1 : ℂ) / 3) * hsum

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-- **The indicator of a cubic class is the average of the three characters of the cubic grade.** -/
theorem class_indicator (c : ℂ) (hc : c ^ 3 = 1) (x : P.Res) :
    (if P.chi x = c then (1 : ℂ) else 0) =
      1 / 3 * ((1 : MulChar P.Res ℂ) x + c⁻¹ * P.chi x + c⁻¹ ^ 2 * P.chi⁻¹ x) := by
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num)] at hc
    exact zero_ne_one hc
  by_cases hx : x = 0
  · subst hx
    rw [MulChar.map_zero, MulChar.map_zero, MulChar.map_zero, if_neg (Ne.symm hc0)]
    ring
  · rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr hx), MulChar.inv_apply_eq_inv']
    exact cube_root_indicator c _ hc (P.chi_cube x hx)

/-- The unit layer on the cubic class `χ_q(gen A) = c`. -/
def classSeries (c : ℂ) (w : ℂ) : ℂ :=
  ∑' A : Ideal O, if Squarefree A then unramifiedNormWeight w A *
    ((if P.chi (P.res (primaryIdealGenerator A)) = c then (1 : ℂ) else 0) *
      (ringComplex (symbol 1 (primaryIdealGenerator A)) ^ 2 * thetaSquareWeight A)) else 0

theorem summable_twistedSquarefreeW (φ : MulChar P.Res ℂ) (w : ℂ) (hw : 1 < w.re) :
    Summable (fun A : Ideal O => if Squarefree A then unramifiedNormWeight w A *
      (φ (P.res (primaryIdealGenerator A)) *
        (ringComplex (symbol 1 (primaryIdealGenerator A)) ^ 2 * thetaSquareWeight A)) else 0) :=
  summable_unitLayerTerm (P.resTwist φ) (P.norm_resTwist_le φ) w hw

/-- **`S^{[c]}_1 = ⅓(S^{1_q}_1 + c̄S^{χ_q}_1 + c̄²S^{χ̄_q}_1)`.** -/
theorem classSeries_eq (c : ℂ) (hc : c ^ 3 = 1) (w : ℂ) (hw : 1 < w.re) :
    P.classSeries c w = 1 / 3 * (P.twistedSquarefreeSeriesW (1 : MulChar P.Res ℂ) 1 w +
      c⁻¹ * P.twistedSquarefreeSeriesW P.chi 1 w + c⁻¹ ^ 2 * P.twistedSquarefreeSeriesW P.chi⁻¹ 1 w) := by
  have s1 := P.summable_twistedSquarefreeW 1 w hw
  have s2 := (P.summable_twistedSquarefreeW P.chi w hw).mul_left c⁻¹
  have s3 := (P.summable_twistedSquarefreeW P.chi⁻¹ w hw).mul_left (c⁻¹ ^ 2)
  unfold twistedSquarefreeSeriesW
  rw [← tsum_mul_left, ← tsum_mul_left, ← s1.tsum_add s2, ← (s1.add s2).tsum_add s3, ← tsum_mul_left]
  unfold classSeries
  refine tsum_congr fun A => ?_
  by_cases hsq : Squarefree A
  · simp only [if_pos hsq]
    rw [P.class_indicator c hc]
    ring
  · simp only [if_neg hsq]
    ring

/-! ### The residues -/

theorem eulerFactorQ_four_thirds_eq :
    P.eulerFactorQ (4 / 3) = 1 - (‖ringComplex P.p‖ : ℂ) ^ 2 * (((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-(4 / 3 : ℂ))) ^ 3 := by
  have hρ := P.rho_ne_zero
  set u : ℂ := ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (1 / 3 : ℂ) with hudef
  have hu3 : u ^ 3 = ((‖ringComplex P.p‖ : ℝ) : ℂ) := by
    rw [hudef, ← Complex.cpow_nat_mul]
    norm_num
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num)] at hu3
    exact hρ hu3.symm
  have ht : ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-(4 / 3 : ℂ)) = (u ^ 4)⁻¹ := by
    rw [Complex.cpow_neg, hudef, ← Complex.cpow_nat_mul]
    norm_num
  rw [ht, P.eulerFactorQ_four_thirds_rho, ← hu3]
  field_simp

/-- **The principal twist multiplies the unit-layer residue by `N^{4/3}χ(−4)χ(9)⁻¹/A_q(4/3)`.** -/
theorem principalUnitResidue_eq_mul (h2 : (2 : P.Res) ≠ 0) :
    P.principalUnitResidue = P.normC ^ 2 * (P.chi (-4) * (P.chi 9)⁻¹) *
      ((‖ringComplex P.p‖ * ‖ringComplex P.p‖ : ℝ) : ℂ) ^ ((4 / 3 : ℂ) - 2) / P.conjFactor (4 / 3) *
        untwistedSResidue := by
  have hW := unitFrequencyWeight_ne_zero (4 / 3)
  have hC := scalar_star_ne_zero
  have hL := LFunction_chi3D_one_ne_zero
  have hE := P.eulerFactorQ_ne_zero (s := 4 / 3) (by norm_num)
  have hA := P.conjFactor_ne_zero h2 (4 / 3) (by norm_num)
  rw [untwistedSResidue_eq_denom, principalUnitResidue, P.principalLimit_eq h2, ← P.eulerFactorQ_four_thirds_eq]
  unfold combinationDenom
  rw [clearedCubeZeta_four_thirds]
  field_simp

/-- The residue of `M(s)S^{[c]}_1(s/2)` at `4/3`. -/
def classUnitResidue (c : ℂ) : ℂ :=
  1 / 3 * (P.principalUnitResidue + c⁻¹ * P.twistUnitResidue + c⁻¹ ^ 2 * P.conjUnitResidue)

/-- **Each cubic class of the unit layer has a simple pole.** For an odd primary prime `q` and `c³ = 1`,
`M(s)S^{[c]}_1(s/2)` continues to `{4/3 < Re s < 13/3, Im s > 0}` and a punctured neighbourhood of `4/3`, and
`(s − 4/3)M(s)S^{[c]}_1(s/2) → classUnitResidue c`. -/
theorem classSeries_simple_pole (h2 : (2 : P.Res) ≠ 0) (c : ℂ) (hc : c ^ 3 = 1) :
    ∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im → Λ s = besselSqMellin s * P.classSeries c (s / 2)) ∧
      (∀ s : ℂ, 4 / 3 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) * Λ s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (P.classUnitResidue c)) := by
  obtain ⟨Λ₁, h1e, h1d, h1n, h1l, -⟩ := P.principalUnitLayer_simple_pole h2
  obtain ⟨Λχ, hχe, hχd, hχn, hχl, -⟩ := P.cubicUnitLayer_simple_pole
  obtain ⟨Λc, hce, hcd, hcn, hcl, -⟩ := P.conjugateUnitLayer_simple_pole h2
  refine ⟨fun s => 1 / 3 * (Λ₁ s + c⁻¹ * Λχ s + c⁻¹ ^ 2 * Λc s), fun s hs4 hs hi => ?_, fun s hs1 hs hi => ?_, ?_,
    ?_⟩
  · have hw : 1 < (s / 2).re := by rw [Complex.div_ofNat_re]; linarith
    show 1 / 3 * (Λ₁ s + c⁻¹ * Λχ s + c⁻¹ ^ 2 * Λc s) = _
    rw [h1e s hs4 hs hi, hχe s hs4 hs hi, hce s hs4 hs hi, P.classSeries_eq c hc _ hw]
    ring
  · exact ((((h1d s hs1 hs hi).add ((hχd s hs1 hs hi).const_mul _)).add ((hcd s hs1 hs hi).const_mul _))).const_mul _
  · filter_upwards [h1n, hχn, hcn] with s a b d
    exact (((a.add (b.const_mul _)).add (d.const_mul _))).const_mul _
  · have h := (((h1l.add (hχl.const_mul c⁻¹)).add (hcl.const_mul (c⁻¹ ^ 2)))).const_mul (1 / 3 : ℂ)
    refine h.congr fun s => ?_
    ring

/-- **The cubic-class residues in closed form.** `Res S^{[c]}_1 = ⅓(N^{4/3}χ(−4)χ(9)⁻¹/A_q
+ c̄·2ρ^{5/3}/(ρ² + 1)·\overline{(9/q)₃}G̃(q) + c̄²·NJ_q/(g(χ_q)A_q))·Res S₁`. -/
theorem classUnitResidue_eq (h2 : (2 : P.Res) ≠ 0) (c : ℂ) :
    P.classUnitResidue c = 1 / 3 *
      (P.normC ^ 2 * (P.chi (-4) * (P.chi 9)⁻¹) *
          ((‖ringComplex P.p‖ * ‖ringComplex P.p‖ : ℝ) : ℂ) ^ ((4 / 3 : ℂ) - 2) / P.conjFactor (4 / 3) +
        c⁻¹ * (2 * ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (5 / 3 : ℂ) / ((‖ringComplex P.p‖ : ℂ) ^ 2 + 1) *
          (star (ringComplex (symbol 9 P.p)) * normalizedCubicUnitGauss P.p)) +
        c⁻¹ ^ 2 * (P.normC * P.fracJacobi / (P.gaussAt 1 * P.conjFactor (4 / 3)))) * untwistedSResidue := by
  rw [classUnitResidue, P.principalUnitResidue_eq_mul h2, P.twistUnitResidue_closed, P.conjUnitResidue_eq_mul h2]
  ring

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
