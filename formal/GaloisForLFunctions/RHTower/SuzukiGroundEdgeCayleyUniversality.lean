import GaloisForLFunctions.RHTower.SuzukiProjectiveDefectBoundary
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Suzuki's ground-edge Cayley universality

Suzuki's shifted finite-aperture carrier has two parity energies.  If the shift distance `τ` from a
simple even ground state is small compared with the odd spectral gap and the ground overlap, the
even resolvent pole dominates.  This module packages the exact dimensionless leakage parameter

`τ * oddBudget / (gap * groundMass)`

and proves that its vanishing forces the defect angle to one.

This apparent survival is itself a no-go: locally uniform holomorphic convergence then saturates
the equality case of Schwarz's lemma, so the carrier is forced to the universal Cayley map
`(z-i)/(z+i)`.  Arithmetic information can survive only in an intermediate shift window where
ground-edge leakage does not vanish and the far-negative free boundary is also avoided.

The theorem is unconditional.  It does not postulate a restricted-Weil operator in Lean: its exact
analytic inputs are lower/upper resolvent-energy bounds, the Fourier endpoint identities, and local
uniform Schur convergence.  `deriv_suzukiFourierLivsic_disk_zero_eq_defectAngle` is the connector
from Suzuki's reflected Fourier pair to those energy variables.
-/

open Complex Metric Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- **Upper-half-plane Schwarz equality.**  An anchored Schur function whose disk-conjugate has
derivative one at the origin is exactly the line Cayley map. -/
theorem upperHalfPlane_cayley_rigidity
    {θ : ℂ → ℂ}
    (hd : DifferentiableOn ℂ θ {z : ℂ | 0 < z.im})
    (hθ : ∀ z : ℂ, 0 < z.im → ‖θ z‖ ≤ 1)
    (hθi : θ I = 0)
    (hderiv : deriv (fun w => θ (suzukiUpperCayleyInv w)) 0 = 1) :
    Set.EqOn θ GaloisForLFunctions.HTGeometry.lineCayley {z : ℂ | 0 < z.im} := by
  let f : ℂ → ℂ := fun w => θ (suzukiUpperCayleyInv w)
  have hopen : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hfdiff : DifferentiableOn ℂ f (ball 0 1) := by
    intro w hw
    have hwlt : ‖w‖ < 1 := by simpa [mem_ball_zero_iff] using hw
    have hw1 : w ≠ 1 := by
      intro h
      rw [h, norm_one] at hwlt
      exact (lt_irrefl 1) hwlt
    have hinv : DifferentiableAt ℂ suzukiUpperCayleyInv w := by
      change DifferentiableAt ℂ (fun v : ℂ => I * ((1 + v) / (1 - v))) w
      fun_prop (disch := exact sub_ne_zero.mpr (Ne.symm hw1))
    have him := suzukiUpperCayleyInv_im_pos_of_norm_lt_one hwlt
    have hθat : DifferentiableAt ℂ θ (suzukiUpperCayleyInv w) :=
      hd.differentiableAt (hopen.mem_nhds him)
    exact (hθat.comp w hinv).differentiableWithinAt
  have hmaps : MapsTo f (ball 0 1) (closedBall 0 1) := by
    intro w hw
    rw [mem_closedBall, dist_zero_right]
    have hwlt : ‖w‖ < 1 := by simpa [mem_ball_zero_iff] using hw
    exact hθ _ (suzukiUpperCayleyInv_im_pos_of_norm_lt_one hwlt)
  have hf0 : f 0 = 0 := by
    simpa [f, suzukiUpperCayleyInv] using hθi
  have hzero : (0 : ℂ) ∈ ball 0 1 := by simp
  have hnorm : ‖dslope f 0 0‖ = (1 : ℝ) / 1 := by
    rw [dslope_same]
    change ‖deriv (fun w => θ (suzukiUpperCayleyInv w)) 0‖ = _
    rw [hderiv, norm_one]
    norm_num
  have hmaps' : MapsTo f (ball 0 1) (closedBall (f 0) 1) := by
    simpa [hf0] using hmaps
  have haff := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div
    hfdiff hmaps' hzero hnorm
  intro z hz
  change 0 < z.im at hz
  have hden : z + I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at him
    linarith
  let w := GaloisForLFunctions.HTGeometry.lineCayley z
  have hw : w ∈ ball (0 : ℂ) 1 := by
    simpa [w, mem_ball_zero_iff, GaloisForLFunctions.HTGeometry.lineCayley] using
      (GaloisForLFunctions.cayley_upperHalfPlane_to_disk z hz)
  have hfw := haff hw
  have hfid : f w = w := by
    simpa [hf0, dslope_same, f, hderiv] using hfw
  have hinv : suzukiUpperCayleyInv w = z := by
    exact suzukiUpperCayleyInv_lineCayley hden
  calc
    θ z = θ (suzukiUpperCayleyInv w) := congrArg θ hinv.symm
    _ = f w := rfl
    _ = w := hfid
    _ = GaloisForLFunctions.HTGeometry.lineCayley z := rfl

/-- The signed projective polarization of the even and odd resolvent energies. -/
def suzukiDefectAngle (evenEnergy oddEnergy : ℝ) : ℝ :=
  (evenEnergy - oddEnergy) / (evenEnergy + oddEnergy)

/-- The dimensionless odd-channel leakage through a simple even ground pole. -/
def suzukiGroundLeakage (τ oddBudget gap groundMass : ℝ) : ℝ :=
  τ * oddBudget / (gap * groundMass)

/-- The disk derivative of Suzuki's reflected Fourier Livšic carrier is the exact endpoint ratio
`F(i)/F(-i)`.  This is the analytic form of `2i Θ'(i)=C/N`. -/
theorem deriv_suzukiFourierLivsic_disk_zero
    {F : ℂ → ℂ}
    (hFi : DifferentiableAt ℂ F I) (hFni : DifferentiableAt ℂ F (-I))
    (hFni0 : F (-I) ≠ 0) :
    deriv (fun w => suzukiLivsicQuotient
      (suzukiFourierNumerator F) (suzukiFourierDenominator F)
      (suzukiUpperCayleyInv w)) 0 = F I / F (-I) := by
  have hsub : HasDerivAt (fun z : ℂ => z - I) 1 I := by
    simpa only [Pi.sub_apply, id_eq, sub_zero] using
      (hasDerivAt_id I).sub (hasDerivAt_const I I)
  have hnum : HasDerivAt (suzukiFourierNumerator F) (F I) I := by
    have h := hsub.mul hFi.hasDerivAt
    simpa [suzukiFourierNumerator] using h
  have hdenDiff : DifferentiableAt ℂ (suzukiFourierDenominator F) I := by
    unfold suzukiFourierDenominator
    fun_prop
  have hden0 : suzukiFourierDenominator F I ≠ 0 := by
    simp only [suzukiFourierDenominator]
    apply mul_ne_zero
    · norm_num
    · simpa using hFni0
  have hquot : HasDerivAt
      (suzukiLivsicQuotient (suzukiFourierNumerator F) (suzukiFourierDenominator F))
      (F I / (2 * I * F (-I))) I := by
    have h := hnum.div hdenDiff.hasDerivAt hden0
    convert h using 1
    simp only [suzukiFourierNumerator, suzukiFourierDenominator, sub_self, zero_mul]
    norm_num
    field_simp
    ring
  have hadd : HasDerivAt (fun w : ℂ => 1 + w) 1 0 := by
    simpa using (hasDerivAt_const 0 (1 : ℂ)).add (hasDerivAt_id 0)
  have hsub' : HasDerivAt (fun w : ℂ => 1 - w) (-1) 0 := by
    simpa using (hasDerivAt_const 0 (1 : ℂ)).sub (hasDerivAt_id 0)
  have hinv : HasDerivAt suzukiUpperCayleyInv (2 * I) 0 := by
    have h := (hadd.div hsub' (by norm_num : (1 : ℂ) - 0 ≠ 0)).const_mul I
    convert h using 1
    ring
  have hquot' : HasDerivAt
      (suzukiLivsicQuotient (suzukiFourierNumerator F) (suzukiFourierDenominator F))
      (F I / (2 * I * F (-I))) (suzukiUpperCayleyInv 0) := by
    simpa [suzukiUpperCayleyInv] using hquot
  have hcomp : HasDerivAt
      (fun w => suzukiLivsicQuotient
        (suzukiFourierNumerator F) (suzukiFourierDenominator F)
        (suzukiUpperCayleyInv w))
      ((F I / (2 * I * F (-I))) * (2 * I)) 0 := by
    simpa [Function.comp_def] using hquot'.comp 0 hinv
  have hderiv := hcomp.deriv
  convert hderiv using 1
  field_simp

/-- Under the parity endpoint identities `F(i)=Eₑ-Eₒ` and `F(-i)=Eₑ+Eₒ`, the disk derivative is
exactly the normalized defect angle. -/
theorem deriv_suzukiFourierLivsic_disk_zero_eq_defectAngle
    {F : ℂ → ℂ} {evenEnergy oddEnergy : ℝ}
    (hFi : DifferentiableAt ℂ F I) (hFni : DifferentiableAt ℂ F (-I))
    (hsum : evenEnergy + oddEnergy ≠ 0)
    (hFiValue : F I = ((evenEnergy - oddEnergy : ℝ) : ℂ))
    (hFniValue : F (-I) = ((evenEnergy + oddEnergy : ℝ) : ℂ)) :
    deriv (fun w => suzukiLivsicQuotient
      (suzukiFourierNumerator F) (suzukiFourierDenominator F)
      (suzukiUpperCayleyInv w)) 0 =
        (suzukiDefectAngle evenEnergy oddEnergy : ℂ) := by
  rw [deriv_suzukiFourierLivsic_disk_zero hFi hFni
    (by rw [hFniValue]; exact ofReal_ne_zero.mpr hsum), hFiValue, hFniValue]
  simp only [suzukiDefectAngle, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_add]

/-- **Quantitative ground-pole law.**  A ground lower bound `groundMass/τ`, an odd energy budget
`oddBudget/gap`, and positivity force `0 ≤ 1-κ ≤ 2ρ`. -/
theorem suzukiDefectAngle_ground_leakage_bound
    {τ gap groundMass oddBudget evenEnergy oddEnergy : ℝ}
    (hτ : 0 < τ) (hgap : 0 < gap) (hground : 0 < groundMass)
    (hoddBudget : 0 ≤ oddBudget) (hodd : 0 ≤ oddEnergy)
    (heven : groundMass / τ ≤ evenEnergy)
    (hoddUpper : oddEnergy ≤ oddBudget / gap) :
    0 ≤ 1 - suzukiDefectAngle evenEnergy oddEnergy ∧
      1 - suzukiDefectAngle evenEnergy oddEnergy ≤
        2 * suzukiGroundLeakage τ oddBudget gap groundMass := by
  have hevenPos : 0 < evenEnergy :=
    lt_of_lt_of_le (div_pos hground hτ) heven
  have hsumPos : 0 < evenEnergy + oddEnergy := add_pos_of_pos_of_nonneg hevenPos hodd
  have hidentity :
      1 - suzukiDefectAngle evenEnergy oddEnergy =
        2 * oddEnergy / (evenEnergy + oddEnergy) := by
    rw [suzukiDefectAngle]
    field_simp
    ring
  rw [hidentity]
  constructor
  · exact div_nonneg (mul_nonneg (by norm_num) hodd) hsumPos.le
  · calc
      2 * oddEnergy / (evenEnergy + oddEnergy) ≤ 2 * oddEnergy / evenEnergy := by
        gcongr
        exact le_add_of_nonneg_right hodd
      _ ≤ 2 * (oddBudget / gap) / (groundMass / τ) := by
        gcongr
      _ = 2 * suzukiGroundLeakage τ oddBudget gap groundMass := by
        rw [suzukiGroundLeakage]
        field_simp

/-- Vanishing ground leakage makes the normalized defect angle tend to one, allowing every
spectral parameter in the bound to vary along an arbitrary nontrivial filter. -/
theorem suzukiDefectAngle_tendsto_one
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {τ gap groundMass oddBudget evenEnergy oddEnergy : ι → ℝ}
    (hdata : ∀ᶠ j in l,
      0 < τ j ∧ 0 < gap j ∧ 0 < groundMass j ∧ 0 ≤ oddBudget j ∧
        0 ≤ oddEnergy j ∧ groundMass j / τ j ≤ evenEnergy j ∧
        oddEnergy j ≤ oddBudget j / gap j)
    (hleakage : Tendsto
      (fun j => suzukiGroundLeakage (τ j) (oddBudget j) (gap j) (groundMass j))
      l (nhds 0)) :
    Tendsto (fun j => suzukiDefectAngle (evenEnergy j) (oddEnergy j)) l (nhds 1) := by
  have hnonneg : ∀ᶠ j in l,
      0 ≤ 1 - suzukiDefectAngle (evenEnergy j) (oddEnergy j) := by
    filter_upwards [hdata] with j hj
    rcases hj with ⟨hτ, hgap, hground, hbudget, hodd, heven, hoddUpper⟩
    exact (suzukiDefectAngle_ground_leakage_bound
      hτ hgap hground hbudget hodd heven hoddUpper).1
  have hupper : ∀ᶠ j in l,
      1 - suzukiDefectAngle (evenEnergy j) (oddEnergy j) ≤
        2 * suzukiGroundLeakage (τ j) (oddBudget j) (gap j) (groundMass j) := by
    filter_upwards [hdata] with j hj
    rcases hj with ⟨hτ, hgap, hground, hbudget, hodd, heven, hoddUpper⟩
    exact (suzukiDefectAngle_ground_leakage_bound
      hτ hgap hground hbudget hodd heven hoddUpper).2
  have hdiff : Tendsto
      (fun j => 1 - suzukiDefectAngle (evenEnergy j) (oddEnergy j)) l (nhds 0) :=
    squeeze_zero' hnonneg hupper (by simpa using hleakage.const_mul 2)
  have hone : Tendsto
      (fun j : ι => (1 : ℝ) - (1 - suzukiDefectAngle (evenEnergy j) (oddEnergy j)))
      l (nhds ((1 : ℝ) - 0)) := tendsto_const_nhds.sub hdiff
  simpa using hone

/-- If anchored Schur carriers converge locally uniformly and their disk derivatives tend to one,
the limit is the universal Cayley map.  Derivative convergence is obtained from Weierstrass's
locally uniform limit theorem, not assumed for the limit. -/
theorem suzukiGroundEdge_cayley_limit
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {Θ : ι → ℂ → ℂ} {θ : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn Θ θ l {z : ℂ | 0 < z.im})
    (hhol : ∀ᶠ j in l, DifferentiableOn ℂ (Θ j) {z : ℂ | 0 < z.im})
    (hbound : ∀ z : ℂ, 0 < z.im → ‖θ z‖ ≤ 1)
    (hanchor : θ I = 0)
    (hangle : Tendsto
      (fun j => deriv (fun w => Θ j (suzukiUpperCayleyInv w)) 0) l (nhds 1)) :
    Set.EqOn θ GaloisForLFunctions.HTGeometry.lineCayley {z : ℂ | 0 < z.im} := by
  let U : Set ℂ := {z : ℂ | 0 < z.im}
  let D : Set ℂ := ball 0 1
  have hUOpen : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hmaps : MapsTo suzukiUpperCayleyInv D U := by
    intro w hw
    change 0 < (suzukiUpperCayleyInv w).im
    apply suzukiUpperCayleyInv_im_pos_of_norm_lt_one
    simpa [D, mem_ball_zero_iff] using hw
  have hinvDiff : DifferentiableOn ℂ suzukiUpperCayleyInv D := by
    intro w hw
    have hwlt : ‖w‖ < 1 := by simpa [D, mem_ball_zero_iff] using hw
    have hw1 : w ≠ 1 := by
      intro h
      rw [h, norm_one] at hwlt
      exact (lt_irrefl 1) hwlt
    change DifferentiableWithinAt ℂ (fun v : ℂ => I * ((1 + v) / (1 - v))) D w
    exact (by fun_prop (disch := exact sub_ne_zero.mpr (Ne.symm hw1)))
  have hconvDisk : TendstoLocallyUniformlyOn
      (fun j w => Θ j (suzukiUpperCayleyInv w))
      (fun w => θ (suzukiUpperCayleyInv w)) l D := by
    exact hconv.comp suzukiUpperCayleyInv hmaps hinvDiff.continuousOn
  have hholDisk : ∀ᶠ j in l,
      DifferentiableOn ℂ (fun w => Θ j (suzukiUpperCayleyInv w)) D := by
    filter_upwards [hhol] with j hj
    simpa [Function.comp_def] using hj.comp hinvDiff hmaps
  have hderivConv : Tendsto
      (fun j => deriv (fun w => Θ j (suzukiUpperCayleyInv w)) 0) l
      (nhds (deriv (fun w => θ (suzukiUpperCayleyInv w)) 0)) := by
    have h := hconvDisk.deriv hholDisk isOpen_ball
    simpa [D] using h.tendsto_at (by simp : (0 : ℂ) ∈ ball 0 1)
  have hderiv : deriv (fun w => θ (suzukiUpperCayleyInv w)) 0 = 1 :=
    tendsto_nhds_unique hderivConv hangle
  have hθdiff : DifferentiableOn ℂ θ {z : ℂ | 0 < z.im} :=
    hconv.differentiableOn hhol hUOpen
  exact upperHalfPlane_cayley_rigidity hθdiff hbound hanchor hderiv

/-- **Ground-edge Cayley universality.**  If the exact even/odd resolvent bounds make the leakage
parameter vanish, every locally uniform anchored Schur limit is the universal Cayley carrier.
Consequently a non-Cayley arithmetic limit requires nonvanishing excited-state leakage. -/
theorem suzukiGroundEdge_cayley_universality
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {Θ : ι → ℂ → ℂ} {θ : ℂ → ℂ}
    {τ gap groundMass oddBudget evenEnergy oddEnergy : ι → ℝ}
    (hconv : TendstoLocallyUniformlyOn Θ θ l {z : ℂ | 0 < z.im})
    (hhol : ∀ᶠ j in l, DifferentiableOn ℂ (Θ j) {z : ℂ | 0 < z.im})
    (hbound : ∀ z : ℂ, 0 < z.im → ‖θ z‖ ≤ 1)
    (hanchor : θ I = 0)
    (hdata : ∀ᶠ j in l,
      0 < τ j ∧ 0 < gap j ∧ 0 < groundMass j ∧ 0 ≤ oddBudget j ∧
        0 ≤ oddEnergy j ∧ groundMass j / τ j ≤ evenEnergy j ∧
        oddEnergy j ≤ oddBudget j / gap j)
    (hleakage : Tendsto
      (fun j => suzukiGroundLeakage (τ j) (oddBudget j) (gap j) (groundMass j))
      l (nhds 0))
    (hderivAngle : ∀ᶠ j in l,
      deriv (fun w => Θ j (suzukiUpperCayleyInv w)) 0 =
        (suzukiDefectAngle (evenEnergy j) (oddEnergy j) : ℂ)) :
    Set.EqOn θ GaloisForLFunctions.HTGeometry.lineCayley {z : ℂ | 0 < z.im} := by
  have hangle0 := suzukiDefectAngle_tendsto_one hdata hleakage
  have hangle0C : Tendsto
      (fun j => (suzukiDefectAngle (evenEnergy j) (oddEnergy j) : ℂ))
      l (nhds 1) := by
    simpa using Complex.continuous_ofReal.continuousAt.tendsto.comp hangle0
  have heq :
      (fun j => (suzukiDefectAngle (evenEnergy j) (oddEnergy j) : ℂ)) =ᶠ[l]
        (fun j => deriv (fun w => Θ j (suzukiUpperCayleyInv w)) 0) :=
    hderivAngle.mono fun j hj => hj.symm
  have hangle : Tendsto
      (fun j => deriv (fun w => Θ j (suzukiUpperCayleyInv w)) 0) l (nhds 1) :=
    hangle0C.congr' heq
  exact suzukiGroundEdge_cayley_limit hconv hhol hbound hanchor hangle

/-- **Positive scale-selection survivor.**  Under the exact Suzuki energy and derivative laws, a
non-Cayley locally uniform limit forces the ground leakage parameter not to converge to zero.  This
is the usable necessary condition left by the ground-edge no-go. -/
theorem suzukiGroundEdge_nonCayley_forces_leakage_not_tendsto_zero
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {Θ : ι → ℂ → ℂ} {θ : ℂ → ℂ}
    {τ gap groundMass oddBudget evenEnergy oddEnergy : ι → ℝ}
    (hconv : TendstoLocallyUniformlyOn Θ θ l {z : ℂ | 0 < z.im})
    (hhol : ∀ᶠ j in l, DifferentiableOn ℂ (Θ j) {z : ℂ | 0 < z.im})
    (hbound : ∀ z : ℂ, 0 < z.im → ‖θ z‖ ≤ 1)
    (hanchor : θ I = 0)
    (hdata : ∀ᶠ j in l,
      0 < τ j ∧ 0 < gap j ∧ 0 < groundMass j ∧ 0 ≤ oddBudget j ∧
        0 ≤ oddEnergy j ∧ groundMass j / τ j ≤ evenEnergy j ∧
        oddEnergy j ≤ oddBudget j / gap j)
    (hderivAngle : ∀ᶠ j in l,
      deriv (fun w => Θ j (suzukiUpperCayleyInv w)) 0 =
        (suzukiDefectAngle (evenEnergy j) (oddEnergy j) : ℂ))
    (hnonCayley : ¬Set.EqOn θ GaloisForLFunctions.HTGeometry.lineCayley
      {z : ℂ | 0 < z.im}) :
    ¬Tendsto
      (fun j => suzukiGroundLeakage (τ j) (oddBudget j) (gap j) (groundMass j))
      l (nhds 0) := by
  intro hleakage
  exact hnonCayley (suzukiGroundEdge_cayley_universality
    hconv hhol hbound hanchor hdata hleakage hderivAngle)

end GaloisForLFunctions.RHTower
