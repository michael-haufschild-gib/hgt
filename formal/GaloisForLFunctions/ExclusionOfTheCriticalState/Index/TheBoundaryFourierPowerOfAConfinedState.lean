import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.ThePoissonSpectrumOfAConfinedState
import GaloisForLFunctions.HTGeometry.HardyBoundary.NegativeHalfLineLaplaceHardy
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# The boundary Fourier power of a confined state

At the confinement weight the two halves of the translated pairing give the
squared modulus of the actual Laplace transform. This determines the weighted
state's Fourier power at every frequency from the full zero divisor. In a
finite off-line layer the transform decays inversely with distance throughout
the closed half-plane Re w ≥ −4.
-/

noncomputable section
open MeasureTheory Set Complex Filter Zeta23
open scoped ComplexConjugate Asymptotics Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- Splitting an absolutely integrable correlation at zero gives both
orientations of the positive-lag pairing. -/
private theorem correlation_split {g k : ℝ → ℂ} (hg : Integrable g) (hk : Integrable k) :
    (∫ u, g u) * (∫ v, k v) =
      (∫ t in Ioi (0:ℝ), ∫ u, g u * k (u+t)) + ∫ t in Ioi (0:ℝ), ∫ u, k u * g (u+t) := by
  let C := fun t : ℝ => ∫ u, g u * k (u+t)
  have hprod : Integrable (fun v : ℝ × ℝ => g v.2 * k (v.2+v.1))
      ((volume : Measure ℝ).prod volume) :=
    (measurePreserving_prod_add_swap volume volume).integrable_comp_of_integrable (hg.mul_prod hk)
  have hC : Integrable C := hprod.integral_prod_left
  have htot : (∫ t, C t) = (∫ u, g u) * (∫ v, k v) := by
    change (∫ t : ℝ, ∫ u : ℝ, g u * k (u+t)) = _
    rw [integral_integral_swap hprod]
    simp_rw [integral_const_mul,integral_add_left_eq_self k]
    exact integral_mul_const _ _
  have hrefl (t : ℝ) : C (-t) = ∫ u, k u * g (u+t) := by
    unfold C
    rw [← integral_add_right_eq_self (fun u => g u * k (u + -t)) t]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by simp only [add_neg_cancel_right,mul_comm]
  have hn := integral_comp_neg_Ioi 0 C
  rw [neg_zero] at hn
  simp_rw [hrefl] at hn
  have hs := integral_add_compl (s := Ioi (0:ℝ)) measurableSet_Ioi hC
  rw [compl_Ioi,← hn,htot] at hs
  exact hs.symm

private def tiltDatum (F : ℝ → ℝ) (w : ℂ) (u : ℝ) : ℂ := cexp (w*u) * cx F u

/-- The unit energy tilt gives absolute integrability throughout Re w > −5. -/
private theorem integrable_tiltDatum {R : ℝ} (hr : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) {w : ℂ} (hw : -5 < w.re) : Integrable (tiltDatum F w) := by
  have ht := hF.tilt_domain hr zero_le_one le_rfl
  have hz : (-(w+1)).re < 4 := by simp only [neg_re,add_re,one_re]; linarith only [hw]
  have hi := integrable_cexp_neg_mul_cx ht hz
  rw [neg_neg] at hi
  refine hi.congr (Eventually.of_forall fun u => ?_)
  change cexp ((w+1)*u) * ((Real.exp (-(1*u)) * F u : ℝ) : ℂ) = cexp (w*u) * (F u : ℂ)
  rw [Complex.ofReal_mul,Complex.ofReal_exp,← mul_assoc,← Complex.exp_add]
  congr 2
  push_cast
  ring

private def confLag (F : ℝ → ℝ) (p : ℂ) (t : ℝ) : ℂ :=
  cexp (-(p*t)) * (criticalHalfLineExponentialPair F (shiftProfile F t) : ℂ)

/-- Opposite tilts split the eighth exponential weight between the two profiles. -/
private theorem tilted_correlation (F : ℝ → ℝ) (p : ℂ) (t : ℝ) :
    (∫ u, tiltDatum F (p-8) u * tiltDatum F (-p) (u+t)) = confLag F p t := by
  rw [confLag,criticalHalfLineExponentialPair,← integral_complex_ofReal,← integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro u
  have he : cexp ((p-8)*u) * cexp (-p*((u+t : ℝ):ℂ)) =
      cexp (-(p*t)) * (Real.exp (-(8*u)) : ℂ) := by
    rw [Complex.ofReal_exp,← Complex.exp_add,← Complex.exp_add]
    congr 1
    push_cast
    ring
  change (cexp ((p-8)*u) * (F u : ℂ)) * (cexp (-p*((u+t : ℝ):ℂ)) * (F (u+t) : ℂ)) =
    cexp (-(p*t)) * ((F u * F (u+t) * Real.exp (-(8*u)) : ℝ):ℂ)
  rw [Complex.ofReal_mul,Complex.ofReal_mul]
  linear_combination (F u : ℂ) * (F (u+t) : ℂ) * he

/-- The Cauchy transform of the full zero pairing, with all multiplicities. -/
def confinedZeroResolvent (F : ℝ → ℝ) (p : ℂ) : ℂ :=
  (∑' q : onLineCopies, (zeroValueMass F q : ℂ) * (p-centredZero q)⁻¹) + reflectedOffLineResolvent F p

private theorem zeroResolvent_integral {R : ℝ} (hr : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) {p : ℂ} (hp : 1 < p.re) :
    confinedZeroResolvent F p = -(criticalAliasCoefficient R : ℂ) * ∫ t in Ioi (0:ℝ), confLag F p t :=
  hF.translated_zero_resolvent hr hp

/-- In the strip 3 < Re p < 5 the two reflected Cauchy transforms recover
the product of the state's actual Laplace values at p−8 and −p. -/
theorem IsConfinedNullVector.strip_laplace_product {R : ℝ} (hr : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) {p : ℂ} (hl : 3 < p.re) (hu : p.re < 5) :
    confinedZeroResolvent F p + confinedZeroResolvent F (8-p) =
      -(criticalAliasCoefficient R : ℂ) *
        (negativeHalfLineLaplace (cx F) (p-8) * negativeHalfLineLaplace (cx F) (-p)) := by
  have hg := integrable_tiltDatum hr hF (w := p-8) (by simp only [sub_re,re_ofNat]; linarith only [hl])
  have hk := integrable_tiltDatum hr hF (w := -p) (by rw [neg_re]; linarith only [hu])
  have h := correlation_split hg hk
  have he (t : ℝ) : (∫ u, tiltDatum F (-p) u * tiltDatum F (p-8) (u+t)) = confLag F (8-p) t := by
    rw [← tilted_correlation,show 8-p-8 = -p by ring,neg_sub]
  simp_rw [tilted_correlation F p,he] at h
  rw [zeroResolvent_integral hr hF (p := p) (by linarith only [hl]),
    zeroResolvent_integral hr hF (p := 8-p) (by rw [sub_re,re_ofNat]; linarith only [hu]),
    ← mul_add,← h]
  rfl

private theorem zeroResolvent_conj {R : ℝ} (hr : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) {p : ℂ} (hp : 1 < p.re) :
    confinedZeroResolvent F (conj p) = conj (confinedZeroResolvent F p) := by
  rw [zeroResolvent_integral hr hF (p := conj p) (by simpa using hp),zeroResolvent_integral hr hF hp,
    map_mul,map_neg,Complex.conj_ofReal,← integral_conj]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only [confLag,map_mul,← Complex.exp_conj,map_neg,Complex.conj_ofReal]

/-- The weighted Fourier power at each frequency equals the real part of the
full zero resolvent on the confinement boundary. -/
theorem IsConfinedNullVector.boundary_fourier_power {R : ℝ} (hr : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) (y : ℝ) :
    (criticalAliasCoefficient R / 2) * ‖negativeHalfLineLaplace (cx F) ⟨-4,y⟩‖^2 =
      -(confinedZeroResolvent F ⟨4,y⟩).re := by
  let p : ℂ := ⟨4,y⟩
  have h := hF.strip_laplace_product hr (p := p) (by norm_num [p]) (by norm_num [p])
  have hp : 8-p = conj p := by apply Complex.ext <;> simp [p]; norm_num
  have hw : p-8 = (⟨-4,y⟩ : ℂ) := by apply Complex.ext <;> simp [p]; norm_num
  have hm : -p = conj (⟨-4,y⟩ : ℂ) := by apply Complex.ext <;> simp [p]
  rw [hp,zeroResolvent_conj hr hF (by norm_num [p]),Complex.add_conj,hw,hm] at h
  rw [show cx F = fun u => (F u : ℂ) from rfl,negativeHalfLineLaplace_real_conj,Complex.mul_conj,
    Complex.normSq_eq_norm_sq,← Complex.ofReal_neg,← Complex.ofReal_mul,Complex.ofReal_inj] at h
  change 2*(confinedZeroResolvent F p).re =
    -criticalAliasCoefficient R * ‖negativeHalfLineLaplace (cx F) ⟨-4,y⟩‖^2 at h
  change _ = -(confinedZeroResolvent F p).re
  linear_combination h / 2

/-- At each ordinate the off-line transform supplies both the continuous Fourier
power and the Poisson-weighted mass of all critical-line copies. -/
theorem IsConfinedNullVector.boundary_poisson_identity {R : ℝ} (hr : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) (y : ℝ) :
    (criticalAliasCoefficient R / 2) * ‖negativeHalfLineLaplace (cx F) ⟨-4,y⟩‖^2 +
      (∑' q : onLineCopies, zeroValueMass F q * (4 / (16+(y-(centredZero q).im)^2))) =
      -(reflectedOffLineResolvent F ⟨4,y⟩).re := by
  let p : ℂ := ⟨4,y⟩
  let l := fun q : onLineCopies => (zeroValueMass F q : ℂ) * (p-centredZero q)⁻¹
  have hl : Summable l := by
    apply Summable.of_norm_bounded (((hF.summable_zero_traces hr).1).subtype (· ∈ onLineCopies))
    intro q
    have hd : 1 ≤ ‖p-centredZero q‖ := by
      have h := (le_abs_self (p-centredZero q).re).trans (Complex.abs_re_le_norm _)
      rw [sub_re,show (centredZero q).re = 0 from q.property,sub_zero] at h
      exact (by norm_num [p] : (1:ℝ) ≤ p.re).trans h
    have hi : ‖(p-centredZero q)⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hd
    change ‖(zeroValueMass F q : ℂ) * (p-centredZero q)⁻¹‖ ≤ zeroValueMass F q
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (zeroValueMass_nonneg _ _)]
    exact mul_le_of_le_one_right (zeroValueMass_nonneg _ _) hi
  have he (q : onLineCopies) :
      (l q).re = zeroValueMass F q * (4 / (16+(y-(centredZero q).im)^2)) := by
    change ((zeroValueMass F q : ℂ) * (p-centredZero q)⁻¹).re = _
    rw [Complex.re_ofReal_mul,Complex.inv_re,Complex.normSq_apply,sub_re,sub_im,
      show (centredZero q).re = 0 from q.property,sub_zero]
    change zeroValueMass F q * (4/(4*4+(y-(centredZero q).im)*(y-(centredZero q).im))) = _
    rw [sq]; norm_num
  have h := hF.boundary_fourier_power hr y
  change _ = -((∑' q, l q) + reflectedOffLineResolvent F p).re at h
  rw [add_re,Complex.re_tsum hl] at h
  simp_rw [he] at h
  linarith only [h]

/-- For a finite off-line divisor the pointwise Fourier power of the actual
weighted state decays quadratically over the entire frequency axis. -/
theorem IsConfinedNullVector.boundary_fourier_decay {R : ℝ} (hr : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) (hfin : BacklundConverse.FiniteOffLine) :
    ∃ C : ℝ, ∀ y : ℝ, (1+y^2)*‖negativeHalfLineLaplace (cx F) ⟨-4,y⟩‖^2 ≤ C := by
  obtain ⟨C,hC⟩ := paired_reflectedOffLineResolvent_bound F hfin (by norm_num : (2:ℝ) ≤ 4)
  let a := criticalAliasCoefficient R / 2
  have ha : 0 < a := div_pos (criticalAliasCoefficient_positive hr) two_pos
  let V := fun y : ℝ => reflectedOffLineResolvent F ⟨4,y⟩
  have hle (y : ℝ) : a*‖negativeHalfLineLaplace (cx F) ⟨-4,y⟩‖^2 ≤ -(V y).re := by
    have h := hF.boundary_poisson_identity hr y
    have hpos : 0 ≤ ∑' q : onLineCopies, zeroValueMass F q * (4/(16+(y-(centredZero q).im)^2)) :=
      tsum_nonneg fun q => mul_nonneg (zeroValueMass_nonneg _ _) (by positivity)
    exact (le_add_of_nonneg_right hpos).trans_eq h
  refine ⟨C / a,fun y => (le_div_iff₀ ha).mpr ?_⟩
  have hneg : a*‖negativeHalfLineLaplace (cx F) ⟨-4,-y⟩‖^2 ≥ 0 :=
    mul_nonneg ha.le (sq_nonneg _)
  have hb := hle (-y)
  have hrn := (neg_le_abs (V y + V (-y)).re).trans (Complex.abs_re_le_norm _)
  rw [add_re] at hrn
  have hv : a*‖negativeHalfLineLaplace (cx F) ⟨-4,y⟩‖^2 ≤ ‖V y + V (-y)‖ := by
    linarith only [hle y,hb,hneg,hrn]
  calc (1+y^2)*‖negativeHalfLineLaplace (cx F) ⟨-4,y⟩‖^2*a =
      (1+y^2)*(a*‖negativeHalfLineLaplace (cx F) ⟨-4,y⟩‖^2) := by ring
    _ ≤ (1+y^2)*‖V y + V (-y)‖ := mul_le_mul_of_nonneg_left hv (by positivity)
    _ ≤ C := hC y

/-- The linear numerator can be recovered from bounded analytic regularizations
by taking their poles to negative infinity. -/
private theorem linear_halfPlane_maximum {L : ℂ → ℂ} {M K : ℝ}
    (hd : DiffContOnCl ℂ L {w | 0 < w.re}) (hM : ∀ w : ℂ, 0 ≤ w.re → ‖L w‖ ≤ M)
    (hK : 0 ≤ K) (hb : ∀ y : ℝ, ‖(1+(y:ℂ)*I) * L ((y:ℂ)*I)‖ ≤ K)
    (z : ℂ) (hz : 0 ≤ z.re) : ‖(1+z)*L z‖ ≤ K := by
  have hcl : closure {w : ℂ | 0 < w.re} ⊆ {w : ℂ | 0 ≤ w.re} :=
    closure_minimal (fun w hw => show 0 ≤ w.re from le_of_lt hw) (isClosed_le continuous_const Complex.continuous_re)
  have reg (r : ℝ) (hr : 0 < r) : ‖(1+z)*L z‖ ≤ K*‖1+(r:ℂ)*z‖ := by
    let D := fun w : ℂ => 1+(r:ℂ)*w
    let f := fun w : ℂ => (1+w)/D w * L w
    have hD (w : ℂ) (hw : 0 ≤ w.re) : 1 ≤ ‖D w‖ := by
      have h := (le_abs_self (D w).re).trans (Complex.abs_re_le_norm _)
      change (1+(r:ℂ)*w).re ≤ _ at h
      rw [add_re,one_re,Complex.re_ofReal_mul] at h
      exact (le_add_of_nonneg_right (mul_nonneg hr.le hw)).trans h
    have hn (w : ℂ) (hw : 0 ≤ w.re) : D w ≠ 0 :=
      norm_pos_iff.mp (zero_lt_one.trans_le (hD w hw))
    have hdD : Differentiable ℂ D := by dsimp [D]; fun_prop
    have hdN : Differentiable ℂ (fun w : ℂ => 1+w) := by fun_prop
    have hf : DiffContOnCl ℂ f {w | 0 < w.re} := by
      constructor
      · intro w hw
        exact ((hdN.differentiableAt.div hdD.differentiableAt (hn w (le_of_lt hw))).differentiableWithinAt).mul (hd.1 w hw)
      · intro w hw
        exact ((hdN.differentiableAt.div hdD.differentiableAt (hn w (hcl hw))).continuousAt.continuousWithinAt).mul (hd.2 w hw)
    have hbound (w : ℂ) (hw : 0 ≤ w.re) : ‖f w‖ ≤ (1+2/r)*M := by
      have he : (r:ℂ)*w = D w - 1 := by dsimp [D]; ring
      have h := norm_sub_le (D w) 1
      rw [← he,norm_mul,Complex.norm_real,Real.norm_of_nonneg hr.le,norm_one] at h
      have hw' : ‖w‖ ≤ (2/r)*‖D w‖ := by
        rw [div_mul_eq_mul_div,le_div_iff₀ hr]
        linarith only [h,hD w hw,mul_comm r ‖w‖]
      have hq : ‖(1+w)/D w‖ ≤ 1+2/r := by
        rw [norm_div,div_le_iff₀ (norm_pos_iff.mpr (hn w hw))]
        calc ‖1+w‖ ≤ 1+‖w‖ := by simpa only [norm_one] using norm_add_le (1:ℂ) w
             _ ≤ ‖D w‖+(2/r)*‖D w‖ := add_le_add (hD w hw) hw'
             _ = _ := by ring
      exact (norm_mul _ _).trans_le (mul_le_mul hq (hM w hw) (norm_nonneg _) (by positivity))
    have hg : ∃ c < (2:ℝ), ∃ B : ℝ, f =O[Bornology.cobounded ℂ ⊓ principal {w | 0 < w.re}]
        fun w => Real.exp (B*‖w‖^c) := by
      refine ⟨1,by norm_num,0,Asymptotics.IsBigO.of_bound ((1+2/r)*M) ?_⟩
      filter_upwards [mem_inf_of_right (mem_principal_self {w : ℂ | 0 < w.re})] with w hw
      simpa only [zero_mul,Real.exp_zero,norm_one,mul_one] using hbound w (le_of_lt hw)
    have hreal : IsBoundedUnder (· ≤ ·) atTop fun x : ℝ => ‖f (x:ℂ)‖ := by
      refine ⟨(1+2/r)*M,?_⟩
      change ∀ᶠ x : ℝ in atTop, ‖f (x:ℂ)‖ ≤ (1+2/r)*M
      filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
      exact hbound x hx
    have hfval (w : ℂ) : ‖f w‖ = ‖(1+w)*L w‖/‖D w‖ := by
      rw [show f w = (1+w)*L w/D w by dsimp [f]; ring,norm_div]
    have hb' (y : ℝ) : ‖f ((y:ℂ)*I)‖ ≤ K := by
      have hy : 0 ≤ ((y:ℂ)*I).re := by simp
      rw [hfval,div_le_iff₀ (norm_pos_iff.mpr (hn _ hy))]
      exact (hb y).trans (le_mul_of_one_le_right hK (hD _ hy))
    have h := PhragmenLindelof.right_half_plane_of_bounded_on_real hf hg hreal hb' hz
    rwa [hfval,div_le_iff₀ (norm_pos_iff.mpr (hn _ hz))] at h
  have hc : Continuous (fun r : ℝ => K*‖1+(r:ℂ)*z‖) := by fun_prop
  have hlim : Tendsto (fun r : ℝ => K*‖1+(r:ℂ)*z‖) (𝓝[>] 0) (𝓝 K) := by
    simpa using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact reg r hr

/-- In a finite off-line layer the Laplace transform of every confined state
has uniform inverse-linear decay on the whole closed half-plane Re w ≥ −4. -/
theorem IsConfinedNullVector.halfPlane_laplace_decay {R : ℝ} (hr : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) (hfin : BacklundConverse.FiniteOffLine) :
    ∃ K : ℝ, ∀ w : ℂ, -4 ≤ w.re → ‖(w+5)*negativeHalfLineLaplace (cx F) w‖ ≤ K := by
  let f := confinedHalf F
  have hfi : Integrable f := by
    apply (integrable_tiltDatum hr hF (w := -4) (by norm_num)).congr
    apply Eventually.of_forall
    intro u
    change cexp (-4*u) * (F u : ℂ) = ((Real.exp (-(4*u)) * F u : ℝ) : ℂ)
    rw [Complex.ofReal_mul,Complex.ofReal_exp]
    push_cast
    rw [neg_mul]
  have hs : ∀ u, 0 ≤ u → f u = 0 := fun u hu => by simp [f,confinedHalf,hF.1.support u hu]
  have hf2 : MemLp f 2 volume :=
    (memLp_two_iff_integrable_sq_norm (measurable_confinedHalf hF.1).aestronglyMeasurable).mpr
      (integrable_sq_confinedHalf hF.1)
  let L := negativeHalfLineLaplace f
  have hL : DiffContOnCl ℂ L {z | 0 < z.re} :=
    ⟨(isHalfPlaneHardy_negativeHalfLineLaplace hf2 hs).holo,
      (continuousOn_negativeHalfLineLaplace hfi hs).mono (closure_minimal
        (fun z hz => show 0 ≤ z.re from le_of_lt hz) (isClosed_le continuous_const Complex.continuous_re))⟩
  have he (z : ℂ) : L z = negativeHalfLineLaplace (cx F) (z-4) := by
    apply integral_congr_ae
    apply Eventually.of_forall
    intro u
    change cexp (z*u) * ((Real.exp (-(4*u)) * F u : ℝ) : ℂ) = cexp ((z-4)*u) * (F u : ℂ)
    rw [Complex.ofReal_mul,Complex.ofReal_exp,← mul_assoc,← Complex.exp_add]
    congr 2
    push_cast
    ring
  obtain ⟨C,hC⟩ := hF.boundary_fourier_decay hr hfin
  have hb (y : ℝ) : ‖(1+(y:ℂ)*I)*L ((y:ℂ)*I)‖ ≤ Real.sqrt C := by
    apply Real.le_sqrt_of_sq_le
    have hy : ‖1+(y:ℂ)*I‖^2 = 1+y^2 := by
      rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
      simp [Complex.mul_re,Complex.mul_im,pow_two]
    have hpt : (y:ℂ)*I-4 = (⟨-4,y⟩ : ℂ) := by apply Complex.ext <;> simp
    rw [norm_mul,mul_pow,hy,he,hpt]
    exact hC y
  refine ⟨Real.sqrt C, fun w hw => ?_⟩
  have h := linear_halfPlane_maximum hL (fun z hz => norm_negativeHalfLineLaplace_le hfi hs hz)
    (Real.sqrt_nonneg C) hb (w+4) (by rw [add_re,re_ofNat]; linarith only [hw])
  rwa [he,add_sub_cancel_right,show 1+(w+4) = w+5 by ring] at h

#print axioms IsConfinedNullVector.strip_laplace_product
#print axioms IsConfinedNullVector.boundary_fourier_power
#print axioms IsConfinedNullVector.boundary_poisson_identity
#print axioms IsConfinedNullVector.boundary_fourier_decay
#print axioms IsConfinedNullVector.halfPlane_laplace_decay
end GaloisForLFunctions.ExclusionOfTheCriticalState
