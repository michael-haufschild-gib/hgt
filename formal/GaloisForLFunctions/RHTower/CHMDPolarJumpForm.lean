import GaloisForLFunctions.RHTower.CHMDDoobSourceGraph

/-!
# The polar jump form on the theta–cosh mass space

The pole kernel `2cosh((x−y)/2)` of the Weil functional is the rank-two product
`2cosh(x/2)cosh(y/2) − 2sinh(x/2)sinh(y/2)`. Against the theta weights it defines a jump
Dirichlet form on `L²(Θ cosh(x/2) dx)`. For every square-integrable profile `v` its energy is
`‖v‖² − 2⟨v,1⟩² + 2⟨v,tanh(·/2)⟩²`: the theta–cosh mass is the diagonal of the polar jump form
and the pole term of the Weil functional is its off-diagonal part. The form is nonnegative and
bounded by twice the mass. The proof expands the square into six product terms and integrates each
with Fubini; the odd half-density `Θ sinh(·/2)` has zero integral and the even one has integral `1/2`.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDPolar
open CHMDDoobGraph

/-- The odd half-density `Θ(x) sinh(x/2)`. -/
def sinhDensity (x : ℝ) : ℝ := riemannKernelReal x * Real.sinh (x / 2)

/-- The bounded odd profile `tanh(x/2)`. -/
def tanhHalf (x : ℝ) : ℝ := Real.tanh (x / 2)

/-- The polar jump weight `cosh((x−y)/2) Θ(x) Θ(y)` on a pair of points. -/
def polarWeight (p : ℝ × ℝ) : ℝ :=
  Real.cosh ((p.1 - p.2) / 2) * riemannKernelReal p.1 * riemannKernelReal p.2

/-- The polar jump energy of a profile. -/
def polarEnergy (v : ℝ → ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, polarWeight p * (v p.1 - v p.2) ^ 2 ∂((volume : Measure ℝ).prod volume)

theorem continuous_tanhHalf : Continuous tanhHalf := by
  have h : tanhHalf = fun x => Real.sinh (x / 2) / Real.cosh (x / 2) := by
    funext x; exact Real.tanh_eq_sinh_div_cosh _
  rw [h]
  exact (Real.continuous_sinh.comp (continuous_id.div_const 2)).div
    (Real.continuous_cosh.comp (continuous_id.div_const 2)) fun x => (Real.cosh_pos _).ne'

theorem abs_tanhHalf_le_one (x : ℝ) : |tanhHalf x| ≤ 1 := (Real.abs_tanh_lt_one _).le

theorem continuous_sinhDensity : Continuous sinhDensity :=
  continuous_riemannKernelReal.mul (Real.continuous_sinh.comp (continuous_id.div_const 2))

/-- `Θ sinh(x/2) = tanh(x/2) · Θ cosh(x/2)`. -/
theorem sinhDensity_eq (x : ℝ) : sinhDensity x = tanhHalf x * massDensity x := by
  unfold sinhDensity tanhHalf massDensity
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [(Real.cosh_pos (x / 2)).ne']

theorem abs_sinhDensity_le (x : ℝ) : |sinhDensity x| ≤ massDensity x := by
  rw [sinhDensity_eq, abs_mul, abs_of_pos (massDensity_pos x)]
  exact mul_le_of_le_one_left (massDensity_pos x).le (abs_tanhHalf_le_one x)

theorem sinhDensity_neg (x : ℝ) : sinhDensity (-x) = -sinhDensity x := by
  unfold sinhDensity
  rw [WeilExcess.riemannKernelReal_neg, neg_div, Real.sinh_neg, mul_neg]

/-- The polar weight is the rank-two difference of the two half-density products. -/
theorem polarWeight_eq (p : ℝ × ℝ) :
    polarWeight p = massDensity p.1 * massDensity p.2 - sinhDensity p.1 * sinhDensity p.2 := by
  unfold polarWeight massDensity sinhDensity
  rw [sub_div, Real.cosh_sub]
  ring

theorem polarWeight_nonneg (p : ℝ × ℝ) : 0 ≤ polarWeight p :=
  mul_nonneg (mul_nonneg (Real.cosh_pos _).le (riemannKernelReal_pos _).le)
    (riemannKernelReal_pos _).le

theorem polarEnergy_nonneg (v : ℝ → ℝ) : 0 ≤ polarEnergy v :=
  integral_nonneg fun p => mul_nonneg (polarWeight_nonneg p) (sq_nonneg _)

/-- The even half-density has total mass `1/2`. -/
theorem integral_massDensity : (∫ x, massDensity x) = 1 / 2 := by
  simpa only [massDensity] using integral_riemannKernelReal_cosh_half

/-- The odd half-density has total mass `0`. -/
theorem integral_sinhDensity : (∫ x, sinhDensity x) = 0 := by
  have h := integral_neg_eq_self (fun x => sinhDensity x) (volume : Measure ℝ)
  simp only [sinhDensity_neg, integral_neg] at h
  linarith

theorem integrable_sinhDensity : Integrable sinhDensity :=
  integrable_massDensity.mono' continuous_sinhDensity.aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact abs_sinhDensity_le x)

/-- Integrals against the mass measure are weighted Lebesgue integrals. -/
theorem integral_mass (f : ℝ → ℝ) :
    (∫ x, f x ∂massMeasure) = ∫ x, massDensity x * f x := by
  rw [massMeasure, integral_weighted volume continuous_massDensity.measurable
    (Eventually.of_forall fun x => (massDensity_pos x).le)]

theorem integrable_mass_iff (f : ℝ → ℝ) :
    Integrable f massMeasure ↔ Integrable (fun x => massDensity x * f x) := by
  rw [massMeasure, integrable_weighted_iff volume continuous_massDensity.measurable
    (Eventually.of_forall fun x => (massDensity_pos x).le)]

theorem aestronglyMeasurable_volume_of_mass {v : ℝ → ℝ}
    (hv : AEStronglyMeasurable v massMeasure) : AEStronglyMeasurable v volume :=
  hv.mono_ac volume_absolutelyContinuous_mass

/-- **Polar identity.** For every square-integrable profile the polar jump energy is the mass
minus twice the squared ground pairing plus twice the squared `tanh(·/2)` pairing. -/
theorem polarEnergy_eq {v : ℝ → ℝ} (hv : MemLp v 2 massMeasure) :
    polarEnergy v =
      (∫ x, v x ^ 2 ∂massMeasure) - 2 * (∫ x, v x ∂massMeasure) ^ 2 +
        2 * (∫ x, v x * tanhHalf x ∂massMeasure) ^ 2 := by
  have hvm : AEStronglyMeasurable v volume := aestronglyMeasurable_volume_of_mass hv.1
  -- the six integrable factors
  have hA : Integrable massDensity := integrable_massDensity
  have hB : Integrable sinhDensity := integrable_sinhDensity
  have hAv2 : Integrable (fun x => massDensity x * v x ^ 2) :=
    (integrable_mass_iff _).mp hv.integrable_sq
  have hAv : Integrable (fun x => massDensity x * v x) :=
    (integrable_mass_iff _).mp (hv.integrable one_le_two)
  have hBv2 : Integrable (fun x => sinhDensity x * v x ^ 2) := by
    refine hAv2.mono' (continuous_sinhDensity.aestronglyMeasurable.mul (hvm.pow 2))
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (v x))]
    exact mul_le_mul_of_nonneg_right (abs_sinhDensity_le x) (sq_nonneg _)
  have hBv : Integrable (fun x => sinhDensity x * v x) := by
    refine hAv.norm.mono' (continuous_sinhDensity.aestronglyMeasurable.mul hvm)
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (massDensity_pos x)]
    exact mul_le_mul_of_nonneg_right (abs_sinhDensity_le x) (abs_nonneg _)
  -- pointwise expansion into six product terms
  have hpt : ∀ p : ℝ × ℝ, polarWeight p * (v p.1 - v p.2) ^ 2 =
      ((massDensity p.1 * v p.1 ^ 2) * massDensity p.2 +
        massDensity p.1 * (massDensity p.2 * v p.2 ^ 2) -
        2 * ((massDensity p.1 * v p.1) * (massDensity p.2 * v p.2))) -
      ((sinhDensity p.1 * v p.1 ^ 2) * sinhDensity p.2 +
        sinhDensity p.1 * (sinhDensity p.2 * v p.2 ^ 2) -
        2 * ((sinhDensity p.1 * v p.1) * (sinhDensity p.2 * v p.2))) := by
    intro p
    rw [polarWeight_eq]
    ring
  have i1 : Integrable (fun p : ℝ × ℝ => (massDensity p.1 * v p.1 ^ 2) * massDensity p.2)
      (volume.prod volume) := hAv2.mul_prod hA
  have i2 : Integrable (fun p : ℝ × ℝ => massDensity p.1 * (massDensity p.2 * v p.2 ^ 2))
      (volume.prod volume) := hA.mul_prod hAv2
  have i3 : Integrable (fun p : ℝ × ℝ =>
      2 * ((massDensity p.1 * v p.1) * (massDensity p.2 * v p.2))) (volume.prod volume) :=
    (hAv.mul_prod hAv).const_mul 2
  have i4 : Integrable (fun p : ℝ × ℝ => (sinhDensity p.1 * v p.1 ^ 2) * sinhDensity p.2)
      (volume.prod volume) := hBv2.mul_prod hB
  have i5 : Integrable (fun p : ℝ × ℝ => sinhDensity p.1 * (sinhDensity p.2 * v p.2 ^ 2))
      (volume.prod volume) := hB.mul_prod hBv2
  have i6 : Integrable (fun p : ℝ × ℝ =>
      2 * ((sinhDensity p.1 * v p.1) * (sinhDensity p.2 * v p.2))) (volume.prod volume) :=
    (hBv.mul_prod hBv).const_mul 2
  have i12 : Integrable (fun p : ℝ × ℝ => (massDensity p.1 * v p.1 ^ 2) * massDensity p.2 +
      massDensity p.1 * (massDensity p.2 * v p.2 ^ 2)) (volume.prod volume) := i1.add i2
  have i123 : Integrable (fun p : ℝ × ℝ => (massDensity p.1 * v p.1 ^ 2) * massDensity p.2 +
      massDensity p.1 * (massDensity p.2 * v p.2 ^ 2) -
      2 * ((massDensity p.1 * v p.1) * (massDensity p.2 * v p.2))) (volume.prod volume) :=
    i12.sub i3
  have i45 : Integrable (fun p : ℝ × ℝ => (sinhDensity p.1 * v p.1 ^ 2) * sinhDensity p.2 +
      sinhDensity p.1 * (sinhDensity p.2 * v p.2 ^ 2)) (volume.prod volume) := i4.add i5
  have i456 : Integrable (fun p : ℝ × ℝ => (sinhDensity p.1 * v p.1 ^ 2) * sinhDensity p.2 +
      sinhDensity p.1 * (sinhDensity p.2 * v p.2 ^ 2) -
      2 * ((sinhDensity p.1 * v p.1) * (sinhDensity p.2 * v p.2))) (volume.prod volume) :=
    i45.sub i6
  unfold polarEnergy
  simp_rw [hpt]
  rw [integral_sub i123 i456, integral_sub i12 i3, integral_sub i45 i6, integral_add i1 i2,
    integral_add i4 i5, integral_const_mul, integral_const_mul,
    integral_prod_mul (fun x => massDensity x * v x ^ 2) massDensity,
    integral_prod_mul massDensity (fun x => massDensity x * v x ^ 2),
    integral_prod_mul (fun x => massDensity x * v x) (fun x => massDensity x * v x),
    integral_prod_mul (fun x => sinhDensity x * v x ^ 2) sinhDensity,
    integral_prod_mul sinhDensity (fun x => sinhDensity x * v x ^ 2),
    integral_prod_mul (fun x => sinhDensity x * v x) (fun x => sinhDensity x * v x),
    integral_massDensity, integral_sinhDensity, integral_mass, integral_mass, integral_mass]
  have hS : (∫ x, sinhDensity x * v x) = ∫ x, massDensity x * (v x * tanhHalf x) := by
    congr 1
    funext x
    rw [sinhDensity_eq]
    ring
  rw [hS]
  ring

end RHTower.CHMDPolar
