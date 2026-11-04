import GaloisForLFunctions.SignedWindowCriticality.ThePoleChargesTheSupersolution
import GaloisForLFunctions.ArithmeticCriticalityTheory.TranslateGroundStateLorentzLaw

/-!
# The window reads the outside charges of a theta gauge

A **theta gauge** is a combination of translates `ω = Σ_j α_j τ_{b_j}`, `τ_b = Φ(· − b)/Φ` (ACT
`translateSpan`), with test coordinate `M = Φω = Σ_j α_j Φ(· − b_j)`. Its source is exact,
`𝓛_Dω − Φcosh(x/2)ω = −Φ(A cosh(x/2) − B sinh(x/2))`, `A = Σα_j cosh(b_j/2)`, `B = Σα_j sinh(b_j/2)`
(ACT), and its total pole charges are `∫M cosh(x/2) = A/2`, `∫M sinh(x/2) = B/2`
(`integral_thetaGauge_mul_cosh`, `integral_thetaGauge_mul_sinh`): the source carries exactly the
gauge's own charges, twice.

* **Outside-charge identity** (`fullZeroForm_thetaGauge_eq`). For every set `S` and `u ∈ C²_c`,
  `Ẑ(Φωu) = J_M(u) + 2V_s^S(u) − 2V_c^S(u) + 2τ_s^S∫u²M sinh(x/2) − 2τ_c^S∫u²M cosh(x/2)`, with
  `V^S` the charge variances on `S` and `τ^S = (total charge) − (charge on S)` the charges outside
  `S`. The outside charges enter with the pole's signs: the outside sinh charge is slack, the
  outside cosh charge is deficit.
* **Every theta gauge is critical on the line** (`fullZeroForm_thetaGauge_eq_univ`):
  `Ẑ(Φωu) = J_M(u) + 2V_s(u) − 2V_c(u)` with variances on the whole line; no potential remains.
* **The even sector is supercritical in an even theta gauge** (`fullZeroForm_evenThetaGauge_window`).
  If `M` is even and nonnegative and `u` is even and vanishes off `(−c, c)`, then
  `Ẑ(Φωu) = J_M(u) − 2V_c(u) − 2τ_c∫u²M cosh(x/2) ≤ J_M(u)`: the window loses the cosh credit carried
  outside it.

In the odd sector the same identity gives the shifted ground states their window slack
(`ShiftedGroundStatesArePoleChargedOnEveryWindow`); in the even sector it gives a deficit. A window
is subcritical in odd theta gauges and supercritical in even ones, in line with the observed order
of the sector ground energies (the even one is smaller).
-/

open MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality

open _root_.RHTower _root_.RHTower.CHMDPolar
open GaloisForLFunctions.ArithmeticCriticalityTheory

variable {ι : Type*} (s : Finset ι) (α b : ι → ℝ)

/-- The test coordinate of a theta gauge. -/
theorem thetaGauge_coordinate (x : ℝ) :
    riemannKernelReal x * translateSpan s α b x = ∑ j ∈ s, α j * riemannKernelReal (x - b j) :=
  riemannKernelReal_mul_translateSpan s α b x

/-- The total cosh charge of a theta gauge is `A/2`. -/
theorem integral_thetaGauge_mul_cosh :
    (∫ x, riemannKernelReal x * translateSpan s α b x * Real.cosh (x / 2)) =
      translateCoshCoefficient s α b / 2 := by
  have h : (fun x => riemannKernelReal x * translateSpan s α b x * Real.cosh (x / 2)) =
      fun x => ∑ j ∈ s, α j * (riemannKernelReal (x - b j) * Real.cosh (x / 2)) := by
    funext x; rw [thetaGauge_coordinate, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h, integral_finsetSum _ fun j _ =>
    (integrable_riemannKernelReal_sub_mul_cosh_half (b j)).const_mul (α j)]
  unfold translateCoshCoefficient
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by
    rw [integral_const_mul, integral_riemannKernelReal_sub_mul_cosh_half]; ring

/-- The total sinh charge of a theta gauge is `B/2`. -/
theorem integral_thetaGauge_mul_sinh :
    (∫ x, riemannKernelReal x * translateSpan s α b x * Real.sinh (x / 2)) =
      translateSinhCoefficient s α b / 2 := by
  have h : (fun x => riemannKernelReal x * translateSpan s α b x * Real.sinh (x / 2)) =
      fun x => ∑ j ∈ s, α j * (riemannKernelReal (x - b j) * Real.sinh (x / 2)) := by
    funext x; rw [thetaGauge_coordinate, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h, integral_finsetSum _ fun j _ =>
    (integrable_riemannKernelReal_sub_mul_sinh_half (b j)).const_mul (α j)]
  unfold translateSinhCoefficient
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by
    rw [integral_const_mul, integral_riemannKernelReal_sub_mul_sinh_half]; ring

/-- The Markov energy in a theta gauge (ACT's general-gauge representation). -/
theorem markovEnergy_thetaGauge {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) :
    markovEnergy (fun x => (phiDoobTest (fun y => translateSpan s α b y * u y) x : ℂ)) =
      signedJumpEnergy (fun y => riemannKernelReal y * translateSpan s α b y) u +
        ∫ x, u x ^ 2 * (riemannKernelReal x * translateSpan s α b x) * translateSource s α b x := by
  obtain ⟨C, hC0, hM⟩ := exists_abs_riemannKernelReal_mul_translateSpan_le s α b
  exact markovEnergy_phiDoob_mul_eq_signedJump_add_source (contDiff_translateSpan s α b) hC0 hM
    (integrableOn_archLevy_twoSidedShiftGenerator_translateSpan s α b)
    (summable_atom_twoSidedShiftGenerator_translateSpan s α b)
    (twoSidedGenerator_translateSpan_sub_potential s α b) (continuous_translateSource s α b) hu huc

/-- **Outside-charge identity of a theta gauge.** For every set `S` and every `u ∈ C²_c`:
`Ẑ(Φωu) = J_M(u) + 2V_s^S(u) − 2V_c^S(u) + 2τ_s^S∫u²M sinh − 2τ_c^S∫u²M cosh`. -/
theorem fullZeroForm_thetaGauge_eq (S : Set ℝ) {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (huc : HasCompactSupport u) :
    fullZeroForm (phiDoobTest fun y => translateSpan s α b y * u y) =
      signedJumpEnergy (fun y => riemannKernelReal y * translateSpan s α b y) u +
        2 * chargeVariance (fun x => riemannKernelReal x * translateSpan s α b x *
          Real.sinh (x / 2)) S u -
        2 * chargeVariance (fun x => riemannKernelReal x * translateSpan s α b x *
          Real.cosh (x / 2)) S u +
        2 * (translateSinhCoefficient s α b / 2 - sinhCharge (translateSpan s α b) S) *
          (∫ x, u x ^ 2 * (riemannKernelReal x * translateSpan s α b x * Real.sinh (x / 2))) -
        2 * (translateCoshCoefficient s α b / 2 - coshCharge (translateSpan s α b) S) *
          ∫ x, u x ^ 2 * (riemannKernelReal x * translateSpan s α b x * Real.cosh (x / 2)) := by
  set ω := translateSpan s α b
  have hω := (contDiff_translateSpan s α b).continuous
  have hsupp2 : HasCompactSupport fun x => u x ^ 2 :=
    huc.comp_left (g := fun z : ℝ => z ^ 2) (by norm_num)
  have his : Integrable fun x => u x ^ 2 * (riemannKernelReal x * ω x * Real.sinh (x / 2)) :=
    ((hu.continuous.pow 2).mul (continuous_mul_sinh hω)).integrable_of_hasCompactSupport
      hsupp2.mul_right
  have hic : Integrable fun x => u x ^ 2 * (riemannKernelReal x * ω x * Real.cosh (x / 2)) :=
    ((hu.continuous.pow 2).mul (continuous_mul_cosh hω)).integrable_of_hasCompactSupport
      hsupp2.mul_right
  have hsrc : (∫ x, u x ^ 2 * (riemannKernelReal x * ω x) * translateSource s α b x) =
      translateSinhCoefficient s α b *
          (∫ x, u x ^ 2 * (riemannKernelReal x * ω x * Real.sinh (x / 2))) -
        translateCoshCoefficient s α b *
          ∫ x, u x ^ 2 * (riemannKernelReal x * ω x * Real.cosh (x / 2)) := by
    have h1 : (∫ x, (translateSinhCoefficient s α b *
          (u x ^ 2 * (riemannKernelReal x * ω x * Real.sinh (x / 2))) -
        translateCoshCoefficient s α b *
          (u x ^ 2 * (riemannKernelReal x * ω x * Real.cosh (x / 2))))) =
        (∫ x, translateSinhCoefficient s α b *
          (u x ^ 2 * (riemannKernelReal x * ω x * Real.sinh (x / 2)))) -
        ∫ x, translateCoshCoefficient s α b *
          (u x ^ 2 * (riemannKernelReal x * ω x * Real.cosh (x / 2))) :=
      integral_sub (his.const_mul _) (hic.const_mul _)
    rw [integral_const_mul, integral_const_mul] at h1
    rw [← h1]
    exact integral_congr_ae (Eventually.of_forall fun x => by
      simp only [translateSource]; ring)
  unfold fullZeroForm
  rw [markovEnergy_thetaGauge s α b hu huc, hsrc, oddPoleMoment_phiDoob_mul,
    evenPoleMoment_phiDoob_mul]
  unfold chargeVariance sinhCharge coshCharge
  ring

/-- **Every theta gauge is critical on the line.** -/
theorem fullZeroForm_thetaGauge_eq_univ {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (huc : HasCompactSupport u) :
    fullZeroForm (phiDoobTest fun y => translateSpan s α b y * u y) =
      signedJumpEnergy (fun y => riemannKernelReal y * translateSpan s α b y) u +
        2 * chargeVariance (fun x => riemannKernelReal x * translateSpan s α b x *
          Real.sinh (x / 2)) univ u -
        2 * chargeVariance (fun x => riemannKernelReal x * translateSpan s α b x *
          Real.cosh (x / 2)) univ u := by
  rw [fullZeroForm_thetaGauge_eq s α b univ hu huc]
  have hs : sinhCharge (translateSpan s α b) univ = translateSinhCoefficient s α b / 2 := by
    unfold sinhCharge; rw [Measure.restrict_univ, integral_thetaGauge_mul_sinh]
  have hc : coshCharge (translateSpan s α b) univ = translateCoshCoefficient s α b / 2 := by
    unfold coshCharge; rw [Measure.restrict_univ, integral_thetaGauge_mul_cosh]
  rw [hs, hc]
  ring

/-- The integral of an odd function over a symmetric interval vanishes. -/
theorem setIntegral_Ioo_neg_of_odd {g : ℝ → ℝ} (hodd : ∀ x, g (-x) = -g x)
    (c : ℝ) (hc : 0 ≤ c) : ∫ x in Ioo (-c) c, g x = 0 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith)]
  have h := intervalIntegral.integral_comp_neg (a := -c) (b := c) g
  rw [neg_neg] at h
  have h2 : (∫ x in -c..c, g (-x)) = -∫ x in -c..c, g x := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun x _ => by simp only [hodd]
  linarith

/-- The integral of an odd function over the line vanishes. -/
theorem integral_eq_zero_of_odd {g : ℝ → ℝ} (hodd : ∀ x, g (-x) = -g x) : ∫ x, g x = 0 := by
  have h := integral_neg_eq_self (μ := volume) g
  simp_rw [hodd, integral_neg] at h
  linarith

/-- **The even sector is supercritical in an even theta gauge.** If the test coordinate `M = Φω` is
even and nonnegative, and `u` is even and vanishes off `(−c, c)`, then
`Ẑ(Φωu) = J_M(u) − 2V_c(u) − 2τ_c∫u²M cosh(x/2)` with `τ_c = A/2 − ∫_{−c}^{c} M cosh(x/2)`. -/
theorem fullZeroForm_evenThetaGauge_window {c : ℝ} (hc : 0 ≤ c)
    (hMeven : ∀ x, riemannKernelReal (-x) * translateSpan s α b (-x) =
      riemannKernelReal x * translateSpan s α b x)
    (hB : translateSinhCoefficient s α b = 0)
    {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    fullZeroForm (phiDoobTest fun y => translateSpan s α b y * u y) =
      signedJumpEnergy (fun y => riemannKernelReal y * translateSpan s α b y) u -
        2 * chargeVariance (fun x => riemannKernelReal x * translateSpan s α b x *
          Real.cosh (x / 2)) (Ioo (-c) c) u -
        2 * (translateCoshCoefficient s α b / 2 - coshCharge (translateSpan s α b) (Ioo (-c) c)) *
          ∫ x, u x ^ 2 * (riemannKernelReal x * translateSpan s α b x * Real.cosh (x / 2)) := by
  rw [fullZeroForm_thetaGauge_eq s α b (Ioo (-c) c) hu huc, hB]
  set ω := translateSpan s α b
  have hω := (contDiff_translateSpan s α b).continuous
  have hsodd : ∀ x, riemannKernelReal (-x) * ω (-x) * Real.sinh (-x / 2) =
      -(riemannKernelReal x * ω x * Real.sinh (x / 2)) := fun x => by
    rw [hMeven, show -x / 2 = -(x / 2) by ring, Real.sinh_neg]; ring
  have h1 : sinhCharge ω (Ioo (-c) c) = 0 := by
    unfold sinhCharge
    exact setIntegral_Ioo_neg_of_odd hsodd c hc
  have h2 : (∫ x, u x ^ 2 * (riemannKernelReal x * ω x * Real.sinh (x / 2))) = 0 :=
    integral_eq_zero_of_odd fun x => by rw [heven, hsodd]; ring
  have h3 : (∫ x, u x * (riemannKernelReal x * ω x * Real.sinh (x / 2))) = 0 :=
    integral_eq_zero_of_odd fun x => by rw [heven, hsodd]; ring
  unfold chargeVariance
  rw [h1, h2, h3]
  ring

/-- In an even theta gauge with nonnegative coordinate the window form is at most the Markov
Dirichlet form minus the outside cosh deficit. -/
theorem fullZeroForm_evenThetaGauge_le {c : ℝ} (hc : 0 ≤ c)
    (hMeven : ∀ x, riemannKernelReal (-x) * translateSpan s α b (-x) =
      riemannKernelReal x * translateSpan s α b x)
    (hM0 : ∀ x, 0 ≤ riemannKernelReal x * translateSpan s α b x)
    (hB : translateSinhCoefficient s α b = 0)
    {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x)
    (hub : ∀ x, x ∉ Ioo (-c) c → u x = 0) :
    fullZeroForm (phiDoobTest fun y => translateSpan s α b y * u y) ≤
      signedJumpEnergy (fun y => riemannKernelReal y * translateSpan s α b y) u -
        2 * (translateCoshCoefficient s α b / 2 - coshCharge (translateSpan s α b) (Ioo (-c) c)) *
          ∫ x, u x ^ 2 * (riemannKernelReal x * translateSpan s α b x * Real.cosh (x / 2)) := by
  rw [fullZeroForm_evenThetaGauge_window s α b hc hMeven hB hu huc heven]
  have hV := chargeVariance_nonneg (m := fun x => riemannKernelReal x * translateSpan s α b x *
    Real.cosh (x / 2)) (continuous_mul_cosh (contDiff_translateSpan s α b).continuous)
    (fun x _ => mul_nonneg (hM0 x) (Real.cosh_pos _).le) hu.continuous hub
  linarith

end GaloisForLFunctions.SignedWindowCriticality

end
