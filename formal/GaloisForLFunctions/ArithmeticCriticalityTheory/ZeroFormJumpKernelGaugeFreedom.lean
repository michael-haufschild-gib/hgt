import GaloisForLFunctions.ArithmeticCriticalityTheory.ThetaConvolutionFoldedInfinityFailure
import GaloisForLFunctions.ArithmeticCriticalityTheory.ZeroFormGaugeInvariance
import GaloisForLFunctions.ArithmeticCriticalityTheory.SingleShiftCompleteness

/-!
# The zero form is a jump form in every odd gauge; gauge freedom of RH

Let `ω` be a gauge whose source is a multiple of `sinh(x/2)`,
`𝓛_D ω − Φ cosh(x/2) ω = σ sinh(x/2) Φ`, with test coordinate `M = Φω` and pole mass
`∫ M sinh(x/2) = σ/2`; odd theta convolutions (`σ = B_φ`) and finite superpositions of shifted
ground states (`σ = 2 Σ c_j sinh(a_j/2)`) are of this kind. With `μ = M sinh(x/2)`, the source term of
the ground-state representation minus the pole term is a variance,
`σ ∫ u² μ − 2 (∫ u μ)² = ∫∫ (u(x) − u(y))² μ(x) μ(y)`, so the zero form `Z = Q − 2(∫ F sinh)²` is a
pure jump form (`zeroForm_phiDoob_mul_eq_signedJump_add_varianceEnergy`):

    Z(Φ(ω u)) = ∫ dm(t) ∫ M(x)M(x+t)(u(x) − u(x+t))² dx + ∫∫ μ(x)μ(y)(u(x) − u(y))² dx dy.

Both pieces carry the factor `M(x)M(y)`; the conductance per unit `M ⊗ M` is the gauge-free kernel
`dm(|x − y|) + sinh(x/2) sinh(y/2)`. For an odd gauge positive on `(0, ∞)`, `μ ≥ 0` everywhere and the
variance conductances are positive for every pair, including pairs across the origin, where the jump
conductances `−|M(x)M(y)| dm(|x − y|)` are negative.

**Gauge freedom.** Every smeared shifted ground state `ω_ν = ∫ ν(c) ω_c dc` (`ν ≥ 0`, `ν ≠ 0`,
supported in `(0, ∞)`) is the convolution gauge of `ν − ν(−·)`, positive on `(0, ∞)`, and complete:
RH holds if and only if `J_M(u) + ∫∫ μμ (u(x) − u(y))² ≥ 0` for every even `u ∈ C²_c`
(`riemannHypothesis_iff_forall_smearedGauge_jumpForm_nonneg`). RH has the same pure-jump form in
every gauge of this continuum.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### The variance energy -/

/-- The all-pairs jump energy `∫∫ (u(x) − u(y))² μ(x) μ(y) dx dy`. -/
def varianceEnergy (μ u : ℝ → ℝ) : ℝ := ∫ x, ∫ y, (u x - u y) ^ 2 * (μ x * μ y)

/-- `∫∫ (u(x) − u(y))² μ(x)μ(y) = 2 (∫ μ)(∫ u² μ) − 2 (∫ u μ)²` for integrable `μ` and bounded
continuous `u`. -/
theorem varianceEnergy_eq {μ u : ℝ → ℝ} (hμ : Integrable μ) (hu : Continuous u) {Z : ℝ}
    (hZ : ∀ x, |u x| ≤ Z) :
    varianceEnergy μ u = 2 * (∫ x, μ x) * (∫ x, u x ^ 2 * μ x) - 2 * (∫ x, u x * μ x) ^ 2 := by
  have h1 : Integrable fun x => u x * μ x :=
    hμ.bdd_mul hu.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hZ x)
  have h2 : Integrable fun x => u x ^ 2 * μ x :=
    hμ.bdd_mul (hu.pow 2).aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hZ x) 2)
  set I₀ := ∫ x, μ x
  set I₁ := ∫ x, u x * μ x
  set I₂ := ∫ x, u x ^ 2 * μ x
  have hin : ∀ x, (∫ y, (u x - u y) ^ 2 * (μ x * μ y)) =
      μ x * (u x ^ 2 * I₀ - 2 * u x * I₁ + I₂) := fun x => by
    have e : (fun y => (u x - u y) ^ 2 * (μ x * μ y)) = fun y =>
        (μ x * u x ^ 2) * μ y - (2 * μ x * u x) * (u y * μ y) + μ x * (u y ^ 2 * μ y) :=
      funext fun y => by ring
    have i1 : Integrable fun y => (μ x * u x ^ 2) * μ y := hμ.const_mul _
    have i2 : Integrable fun y => (2 * μ x * u x) * (u y * μ y) := h1.const_mul _
    have i3 : Integrable fun y => μ x * (u y ^ 2 * μ y) := h2.const_mul _
    have i12 : Integrable fun y => (μ x * u x ^ 2) * μ y - (2 * μ x * u x) * (u y * μ y) :=
      i1.sub i2
    rw [e, integral_add i12 i3, integral_sub i1 i2, integral_const_mul, integral_const_mul,
      integral_const_mul]
    ring
  unfold varianceEnergy
  simp_rw [hin]
  have e : (fun x => μ x * (u x ^ 2 * I₀ - 2 * u x * I₁ + I₂)) = fun x =>
      I₀ * (u x ^ 2 * μ x) - (2 * I₁) * (u x * μ x) + I₂ * μ x := funext fun x => by ring
  have j1 : Integrable fun x => I₀ * (u x ^ 2 * μ x) := h2.const_mul _
  have j2 : Integrable fun x => (2 * I₁) * (u x * μ x) := h1.const_mul _
  have j3 : Integrable fun x => I₂ * μ x := hμ.const_mul _
  have j12 : Integrable fun x => I₀ * (u x ^ 2 * μ x) - (2 * I₁) * (u x * μ x) := j1.sub j2
  rw [e, integral_add j12 j3, integral_sub j1 j2, integral_const_mul, integral_const_mul,
    integral_const_mul]
  ring

/-! ### The zero form as a jump form -/

/-- **The zero form is a jump form.** If `𝓛_D ω − Φ cosh(x/2) ω = σ sinh(x/2) Φ` and
`∫ Φ ω sinh(x/2) = σ/2`, then for every `u ∈ C²_c(ℝ)`,
`Z(Φ(ω u)) = J_M(u) + ∫∫ (u(x) − u(y))² μ(x)μ(y)` with `M = Φω`, `μ = M sinh(x/2)`. -/
theorem zeroForm_phiDoob_mul_eq_signedJump_add_varianceEnergy {ω u : ℝ → ℝ} {C σ : ℝ}
    (hω : ContDiff ℝ 2 ω) (hC0 : 0 ≤ C)
    (hM : ∀ y, |riemannKernelReal y * ω y| ≤ C * Real.exp (-(24 * |y|)))
    (hA : ∀ x, IntegrableOn (fun t => archLevyDensity t * twoSidedShiftGenerator ω t x) (Ioi 0))
    (hP : ∀ x, Summable fun n : ℕ => vonMangoldtAtom n * twoSidedShiftGenerator ω (Real.log n) x)
    (hsrc : ∀ x, twoSidedGenerator ω x - riemannKernelReal x * Real.cosh (x / 2) * ω x =
      riemannKernelReal x * (σ * Real.sinh (x / 2)))
    (hmass : (∫ x, riemannKernelReal x * ω x * Real.sinh (x / 2)) = σ / 2)
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) :
    zeroForm (phiDoobTest fun y => ω y * u y) =
      signedJumpEnergy (fun y => riemannKernelReal y * ω y) u +
        varianceEnergy (fun x => riemannKernelReal x * ω x * Real.sinh (x / 2)) u := by
  set μ : ℝ → ℝ := fun x => riemannKernelReal x * ω x * Real.sinh (x / 2) with hμ_def
  have hμi : Integrable μ := by
    refine (integrable_exp_neg_eight_mul_abs.const_mul C).mono'
      ((continuous_riemannKernelReal.mul hω.continuous).mul
        (Real.continuous_sinh.comp (continuous_id.div_const 2))).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    have hs : |Real.sinh (x / 2)| ≤ Real.exp (8 * |x|) :=
      (abs_sinh_le_exp_abs _).trans (exp_abs_half_le_exp_eight x)
    have he : Real.exp (-(24 * |x|)) * Real.exp (8 * |x|) ≤ Real.exp (-(8 * |x|)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith [abs_nonneg x])
    rw [Real.norm_eq_abs, hμ_def, abs_mul]
    calc |riemannKernelReal x * ω x| * |Real.sinh (x / 2)|
        ≤ (C * Real.exp (-(24 * |x|))) * Real.exp (8 * |x|) :=
          mul_le_mul (hM x) hs (abs_nonneg _) (by positivity)
      _ = C * (Real.exp (-(24 * |x|)) * Real.exp (8 * |x|)) := by ring
      _ ≤ C * Real.exp (-(8 * |x|)) := mul_le_mul_of_nonneg_left he hC0
  obtain ⟨Z, hZ⟩ := huc.exists_bound_of_continuous hu.continuous
  have hZ' : ∀ x, |u x| ≤ Z := fun x => by simpa [Real.norm_eq_abs] using hZ x
  have hV := varianceEnergy_eq hμi hu.continuous hZ'
  have hQ := markovEnergy_phiDoob_mul_eq_signedJump_add_source (g := fun x => σ * Real.sinh (x / 2))
    hω hC0 hM hA hP hsrc (continuous_const.mul (Real.continuous_sinh.comp
      (continuous_id.div_const 2))) hu huc
  have hpole : oddPoleMoment (phiDoobTest fun y => ω y * u y) = ∫ x, u x * μ x := by
    unfold oddPoleMoment phiDoobTest
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only [hμ_def]; ring)
  have hsrcint : (∫ x, u x ^ 2 * (riemannKernelReal x * ω x) * (σ * Real.sinh (x / 2))) =
      σ * ∫ x, u x ^ 2 * μ x := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only [hμ_def]; ring)
  have hmass' : (∫ x, μ x) = σ / 2 := hmass
  unfold zeroForm
  rw [hQ, hpole, hsrcint, hV, hmass']
  ring

/-! ### Odd theta convolutions -/

/-- **The zero form in an odd convolution gauge.** For odd `φ ∈ C²_c` and every `u ∈ C²_c`,
`Z(Φ(ω_φ u)) = J_{Φ∗φ}(u) + ∫∫ (u(x) − u(y))² μ(x)μ(y)`, `μ = (Φ ∗ φ) sinh(x/2)`. -/
theorem zeroForm_phiDoob_convGauge_mul_eq {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hodd : ∀ b, φ (-b) = -φ b) {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (huc : HasCompactSupport u) :
    zeroForm (phiDoobTest fun y => convGauge φ y * u y) =
      signedJumpEnergy (thetaConv φ) u +
        varianceEnergy (fun x => thetaConv φ x * Real.sinh (x / 2)) u := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_thetaConv_le hφ hφc
  have hsrc : ∀ x, twoSidedGenerator (convGauge φ) x -
      riemannKernelReal x * Real.cosh (x / 2) * convGauge φ x =
        riemannKernelReal x * (convSinhCoefficient φ * Real.sinh (x / 2)) := fun x => by
    rw [twoSidedGenerator_convGauge_sub_potential hφ hφc, convSource_eq hφ hφc,
      convCoshCoefficient_eq_zero_of_odd hodd]
    ring
  have hmass : (∫ x, riemannKernelReal x * convGauge φ x * Real.sinh (x / 2)) =
      convSinhCoefficient φ / 2 := by
    simp_rw [riemannKernelReal_mul_convGauge]
    exact integral_thetaConv_mul_sinh_half hφ hφc
  have h := zeroForm_phiDoob_mul_eq_signedJump_add_varianceEnergy (contDiff_convGauge hφ hφc) hC0
    hC (integrableOn_archLevy_twoSidedShiftGenerator_convGauge hφ hφc)
    (summable_atom_twoSidedShiftGenerator_convGauge hφ hφc) hsrc hmass hu huc
  simp_rw [riemannKernelReal_mul_convGauge] at h
  exact h

/-! ### Smeared shifted ground states -/

/-- The odd profile `ν(b) − ν(−b)` of a smearing density `ν` on `(0, ∞)`; its theta convolution is
`∫ ν(c) m_c dc`. -/
def smearedProfile (ν : ℝ → ℝ) (b : ℝ) : ℝ := ν b - ν (-b)

theorem smearedProfile_neg (ν : ℝ → ℝ) (b : ℝ) : smearedProfile ν (-b) = -smearedProfile ν b := by
  unfold smearedProfile
  rw [neg_neg]
  ring

theorem thetaConv_smearedProfile {ν : ℝ → ℝ} (hν : Continuous ν) (hνc : HasCompactSupport ν)
    (x : ℝ) : thetaConv (smearedProfile ν) x = ∫ c, ν c * shiftDifference c x := by
  have i1 : Integrable fun b => ν b * riemannKernelReal (x - b) :=
    integrable_mul_riemannKernelReal_sub hν hνc x
  have i2 : Integrable fun b => ν (-b) * riemannKernelReal (x - b) := by
    have := (integrable_mul_riemannKernelReal_sub hν hνc (-x)).comp_neg
    refine this.congr (Eventually.of_forall fun b => ?_)
    simp only
    rw [show -x - -b = -(x - b) by ring, riemannKernelReal_neg']
  have h2 : (∫ b, ν (-b) * riemannKernelReal (x - b)) = ∫ c, ν c * riemannKernelReal (x + c) := by
    rw [← integral_neg_eq_self (fun c => ν c * riemannKernelReal (x + c)) volume]
    exact integral_congr_ae (Eventually.of_forall fun b => by
      simp only
      rw [show x + -b = x - b by ring])
  have i3 : Integrable fun c => ν c * riemannKernelReal (x + c) := by
    refine (integrable_mul_riemannKernelReal_sub hν hνc (-x)).congr (Eventually.of_forall fun c => ?_)
    simp only
    rw [show -x - c = -(x + c) by ring, riemannKernelReal_neg']
  unfold thetaConv smearedProfile
  have e : (fun b => (ν b - ν (-b)) * riemannKernelReal (x - b)) =
      fun b => ν b * riemannKernelReal (x - b) - ν (-b) * riemannKernelReal (x - b) :=
    funext fun b => by ring
  rw [e, integral_sub i1 i2, h2, ← integral_sub i1 i3]
  refine integral_congr_ae (Eventually.of_forall fun c => ?_)
  simp only
  unfold shiftDifference
  ring

/-- A nonnegative smearing density on `(0, ∞)`, not identically zero, gives a gauge positive on
`(0, ∞)`: `∫ ν(c) m_c(x) dc > 0` for `x > 0`. -/
theorem thetaConv_smearedProfile_pos {ν : ℝ → ℝ} (hν : Continuous ν) (hνc : HasCompactSupport ν)
    (hν0 : ∀ b, 0 ≤ ν b) (hνpos : ∀ b, b ≤ 0 → ν b = 0) {b₀ : ℝ} (hb₀ : 0 < ν b₀) {x : ℝ}
    (hx : 0 < x) : 0 < thetaConv (smearedProfile ν) x := by
  rw [thetaConv_smearedProfile hν hνc]
  have hb₀pos : 0 < b₀ := by
    by_contra h
    rw [hνpos b₀ (not_lt.mp h)] at hb₀
    exact lt_irrefl _ hb₀
  have hcont : Continuous fun c => ν c * shiftDifference c x :=
    hν.mul ((continuous_riemannKernelReal.comp (continuous_const.sub continuous_id)).sub
      (continuous_riemannKernelReal.comp (continuous_const.add continuous_id)))
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := b₀) hcont
    hνc.mul_right (fun c => ?_) (mul_pos hb₀ (shiftDifference_pos hb₀pos hx)).ne'
  show (0 : ℝ) ≤ ν c * shiftDifference c x
  rcases le_or_gt c 0 with hc | hc
  · rw [hνpos c hc, zero_mul]
  · exact mul_nonneg (hν0 c) (shiftDifference_pos hc hx).le

/-! ### Gauge freedom -/

/-- **Gauge freedom of RH.** For every smearing density `ν ∈ C²_c`, `ν ≥ 0`, vanishing on
`(−∞, 0]` and not identically zero, with `M = Φ ∗ (ν − ν(−·)) = ∫ ν(c) m_c dc` and
`μ = M sinh(x/2) ≥ 0`: RH holds if and only if
`J_M(u) + ∫∫ (u(x) − u(y))² μ(x)μ(y) ≥ 0` for every even `u ∈ C²_c(ℝ)`. -/
theorem riemannHypothesis_iff_forall_smearedGauge_jumpForm_nonneg {ν : ℝ → ℝ}
    (hν : ContDiff ℝ 2 ν) (hνc : HasCompactSupport ν) (hν0 : ∀ b, 0 ≤ ν b)
    (hνpos : ∀ b, b ≤ 0 → ν b = 0) {b₀ : ℝ} (hb₀ : 0 < ν b₀) :
    RiemannHypothesis ↔
      ∀ u : ℝ → ℝ, ContDiff ℝ 2 u → HasCompactSupport u → (∀ x, u (-x) = u x) →
        0 ≤ signedJumpEnergy (thetaConv (smearedProfile ν)) u +
          varianceEnergy (fun x => thetaConv (smearedProfile ν) x * Real.sinh (x / 2)) u := by
  set φ := smearedProfile ν with hφ_def
  have hφ : ContDiff ℝ 2 φ := hν.sub (hν.comp contDiff_neg)
  have hφc : HasCompactSupport φ := hνc.sub (hνc.comp_homeomorph (Homeomorph.neg ℝ))
  have hodd : ∀ b, φ (-b) = -φ b := smearedProfile_neg ν
  have hMpos : ∀ x, 0 < x → 0 < thetaConv φ x := fun x hx =>
    thetaConv_smearedProfile_pos hν.continuous hνc hν0 hνpos hb₀ hx
  have hMne : ∀ x, x ≠ 0 → thetaConv φ x ≠ 0 := fun x hx => by
    rcases lt_or_gt_of_ne hx with h | h
    · have := hMpos (-x) (by linarith)
      rw [thetaConv_neg_of_odd hodd] at this
      linarith
    · exact (hMpos x h).ne'
  rw [riemannHypothesis_iff_forall_odd_zeroForm_nonneg]
  constructor
  · intro hRH u hu huc heven
    have hv : ContDiff ℝ 2 fun y => convGauge φ y * u y := (contDiff_convGauge hφ hφc).mul hu
    have hvc : HasCompactSupport fun y => convGauge φ y * u y := huc.mul_left
    have hvodd : ∀ x, (fun y => convGauge φ y * u y) (-x) = -(fun y => convGauge φ y * u y) x :=
      fun x => by simp only [convGauge_neg_of_odd hodd, heven]; ring
    rw [← zeroForm_phiDoob_convGauge_mul_eq hφ hφc hodd hu huc]
    exact hRH _ hv hvc hvodd
  · intro h
    by_contra hRH
    rw [← riemannHypothesis_iff_forall_odd_zeroForm_nonneg] at hRH
    obtain ⟨F, ε, hF, hFc, hε, hFodd, hvan, hneg⟩ :=
      exists_odd_vanishing_markovEnergy_neg_of_not_riemannHypothesis hRH
    set u : ℝ → ℝ := fun x => F x / thetaConv φ x with hu_def
    have hu : ContDiff ℝ 2 u := by
      rw [contDiff_iff_contDiffAt]
      intro x
      by_cases hx : |x| < ε
      · have hev : u =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
          filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hx] with y hy
          simp only [hu_def, hvan y hy, zero_div]
        exact contDiffAt_const.congr_of_eventuallyEq hev
      · have hx0 : x ≠ 0 := by
          rintro rfl
          exact hx (by rwa [abs_zero])
        exact hF.contDiffAt.div (contDiff_thetaConv hφ hφc).contDiffAt (hMne x hx0)
    have huc : HasCompactSupport u := hFc.mono fun x hx hFx => hx (by simp only [hu_def, hFx,
      zero_div])
    have heven : ∀ x, u (-x) = u x := fun x => by
      simp only [hu_def, hFodd, thetaConv_neg_of_odd hodd, neg_div_neg_eq]
    have htest : phiDoobTest (fun y => convGauge φ y * u y) = F := funext fun x => by
      unfold phiDoobTest
      by_cases hx : x = 0
      · subst hx
        have hF0 : F 0 = 0 := hvan 0 (by rwa [abs_zero])
        simp [hu_def, hF0]
      · rw [← mul_assoc, riemannKernelReal_mul_convGauge, hu_def]
        field_simp [hMne x hx]
    have hZ := h u hu huc heven
    rw [← zeroForm_phiDoob_convGauge_mul_eq hφ hφc hodd hu huc, htest] at hZ
    have hle : zeroForm F ≤ markovEnergy (fun x => (F x : ℂ)) := by
      unfold zeroForm
      nlinarith [sq_nonneg (oddPoleMoment F)]
    linarith

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
