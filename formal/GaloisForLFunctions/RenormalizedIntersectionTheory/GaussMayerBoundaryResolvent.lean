import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerScatteringMultiplicity
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerScatteringNormalization

/-! Actual constant-input, evaluation-output inverse entries identify the
Mayer scattering sector. Their meromorphic germs retain pole multiplicity
even when the determinant and its cofactor vanish together. -/

open Complex Set Filter Topology
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerCutoff MayerParameter MayerScatteringMultiplicity
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerBoundaryResolvent

/-- Actual positive-unit inverse entry, with ring inversion zero at nonunits. -/
def positiveBoundary (w : ℂ) : ℂ :=
  ((Ring.inverse (1-source w)) (constant 1)).1 zeroPoint

/-- Actual negative-unit inverse entry with the same convention. -/
def negativeBoundary (w : ℂ) : ℂ :=
  ((Ring.inverse (1+source w)) (constant 1)).1 zeroPoint

private theorem determinant_zero_iff_not_isUnit {w : ℂ} (hw : 0 < w.re) :
    sourceDeterminant w 1=0 ↔ ¬ IsUnit (1-source w) := by
  rw [sourceDeterminant_eq hw,MayerFredholm.determinant_eq_zero_iff_not_isUnit hw,
    one_smul,← source_eq hw]

/-- The actual positive-unit inverse entry is the signed Fredholm cofactor ratio. -/
theorem positiveBoundary_eq_cofactor {w : ℂ} (hw : 0 < w.re) :
    positiveBoundary w=-MayerPole.polePart w 1/sourceDeterminant w 1 := by
  by_cases hu : IsUnit (1-source w)
  · let f : DiscSpace := Ring.inverse (1-source w) (constant 1)
    have hf₀ : f-source w f=constant 1 := by
      have h := congrArg (fun T : DiscSpace →L[ℂ] DiscSpace => T (constant 1))
        (Ring.mul_inverse_cancel (1-source w) hu)
      exact h
    have hf : f-regularized w hw f=constant 1 := by
      rwa [← source_eq hw]
    have hD : sourceDeterminant w 1 ≠ 0 := fun hd =>
      (determinant_zero_iff_not_isUnit hw).mp hd hu
    have hB := MayerCoprimeCofactor.polePart_eq_response_of hw f hf
    change f.1 zeroPoint=-MayerPole.polePart w 1/sourceDeterminant w 1
    rw [hB]
    field_simp [hD]
  · have hD := (determinant_zero_iff_not_isUnit hw).mpr hu
    rw [positiveBoundary,Ring.inverse_non_unit _ hu,hD,div_zero]
    rfl

/-- The negative-unit constant-input response is invisible to evaluation at zero,
including source parameters with noninvertible negative-unit operators. -/
theorem negativeBoundary_zero {w : ℂ} (hw : 0 < w.re) : negativeBoundary w=0 := by
  have hr : (1+source w) (MayerCancellation.response w)=constant 1 := by
    change MayerCancellation.response w+source w (MayerCancellation.response w)=constant 1
    rw [source]
    simp only [_root_.add_apply,_root_.smul_apply,MayerCancellation.projection_response,
      smul_zero,zero_add]
    rw [MayerCancellation.remainder_response hw]
    abel
  by_cases hu : IsUnit (1+source w)
  · have hi := congrArg (fun T : DiscSpace →L[ℂ] DiscSpace => T (MayerCancellation.response w))
      (Ring.inverse_mul_cancel (1+source w) hu)
    change Ring.inverse (1+source w) ((1+source w) (MayerCancellation.response w))=
      MayerCancellation.response w at hi
    rw [hr] at hi
    rw [negativeBoundary,hi,MayerCancellation.response_apply]
    change 1-(1+0 : ℂ)^(-w)=0
    simp only [add_zero,Complex.one_cpow,sub_self]
  · rw [negativeBoundary,Ring.inverse_non_unit _ hu]
    rfl

private theorem analyticAt_determinant {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    AnalyticAt ℂ (fun v => sourceDeterminant v 1) w := by
  have hw1 : w ≠ 1 := by intro he; norm_num [he] at h1
  have ho : IsOpen {v : ℂ | 0 < v.re ∧ v ≠ 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_compl_singleton
  exact (differentiableOn_sourceDeterminant 1).analyticAt (ho.mem_nhds ⟨h0,hw1⟩)

private theorem eventually_determinant_ne_zero {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    ∀ᶠ v in 𝓝[≠] w, sourceDeterminant v 1 ≠ 0 := by
  rcases (analyticAt_determinant h0 h1).eventually_eq_zero_or_eventually_ne_zero with he | he
  · exact False.elim (determinant_order_ne_top h0 h1 (analyticOrderAt_eq_top.mpr he))
  · exact he

/-- The actual inverse entry has the shifted-zeta ratio as its meromorphic germ. -/
theorem positiveBoundary_germ {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    positiveBoundary =ᶠ[𝓝[≠] w] fun v => 2*riemannZeta (v-1)/riemannZeta v := by
  have ho : IsOpen {v : ℂ | 0 < v.re ∧ v.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hs : ∀ᶠ v in 𝓝[≠] w, 0 < v.re ∧ v.re < 1 :=
    nhdsWithin_le_nhds (ho.mem_nhds ⟨h0,h1⟩)
  filter_upwards [hs,eventually_determinant_ne_zero h0 h1] with v hv hD
  have hv1 : v ≠ 1 := by intro he; norm_num [he] at hv
  have hv2 : v ≠ 2 := by intro he; norm_num [he] at hv
  have hZ : riemannZeta v ≠ 0 := fun hz => hD (sourceDeterminant_zero_of_zeta_zero hv.1 hv.2 hz)
  have h := MayerCofactorContinuation.zeta_cofactor_identity hv.1 hv1 hv2
  rw [positiveBoundary_eq_cofactor hv.1]
  field_simp [hD,hZ]
  linear_combination -h

private theorem analyticAt_numerator {w : ℂ} (h1 : w.re < 1) :
    AnalyticAt ℂ (fun v => 2*riemannZeta (v-1)) w := by
  have hs : w-1 ≠ 1 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.sub_re,Complex.one_re] at hr
    linarith only [hr,h1]
  exact analyticAt_const.mul
    ((GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta hs).comp
      (f := fun v : ℂ => v-1) (analyticAt_id.sub analyticAt_const))

/-- The actual scalar inverse entry is meromorphic throughout the open strip. -/
theorem meromorphicAt_positiveBoundary {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    MeromorphicAt positiveBoundary w := by
  have hw1 : w ≠ 1 := by intro he; norm_num [he] at h1
  have hZ := GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta hw1
  exact ((analyticAt_numerator h1).meromorphicAt.div hZ.meromorphicAt).congr
    (positiveBoundary_germ h0 h1).symm

private theorem zeta_order_finite {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    analyticOrderAt riemannZeta w ≠ ⊤ := by
  intro ht
  have h := determinant_order h0 h1
  rw [ht,add_top] at h
  exact determinant_order_ne_top h0 h1 h

/-- Exact scattering pole multiplicity of the actual inverse entry. -/
theorem positiveBoundary_order {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    meromorphicOrderAt positiveBoundary w=
      -((analyticOrderNatAt riemannZeta w : ℤ) : WithTop ℤ) := by
  have hw1 : w ≠ 1 := by intro he; norm_num [he] at h1
  have hZ := GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta hw1
  have hQ := analyticAt_numerator (w := w) h1
  have hQ0 : 2*riemannZeta (w-1) ≠ 0 :=
    mul_ne_zero (by norm_num) (shifted_zeta_ne_zero h0 h1)
  have hQo : meromorphicOrderAt (fun v => 2*riemannZeta (v-1)) w=0 := by
    rw [hQ.meromorphicOrderAt_eq,hQ.analyticOrderAt_eq_zero.mpr hQ0]
    rfl
  have hfin := ENat.coe_toNat (zeta_order_finite h0 h1)
  rw [meromorphicOrderAt_congr (positiveBoundary_germ h0 h1)]
  change meromorphicOrderAt ((fun v => 2*riemannZeta (v-1))/riemannZeta) w=_
  rw [meromorphicOrderAt_div hQ.meromorphicAt hZ.meromorphicAt,hQo,zero_sub,
    hZ.meromorphicOrderAt_eq,← hfin]
  simp [analyticOrderNatAt]

/-- Actual constant-mode scattering poles are exactly the strip zeta zeros. -/
theorem positiveBoundary_pole_iff {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    meromorphicOrderAt positiveBoundary w < 0 ↔ riemannZeta w=0 := by
  have hw1 : w ≠ 1 := by intro he; norm_num [he] at h1
  have hZ := GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta hw1
  have hfin : (analyticOrderNatAt riemannZeta w : ℕ∞)=analyticOrderAt riemannZeta w :=
    ENat.coe_toNat (zeta_order_finite h0 h1)
  have hz : riemannZeta w=0 ↔ analyticOrderNatAt riemannZeta w ≠ 0 := by
    rw [← hZ.analyticOrderAt_ne_zero,← hfin]
    simp
  rw [positiveBoundary_order h0 h1,hz]
  norm_cast
  omega

/-- The genuine Poincare coefficient is the Gamma-normalized actual boundary inverse entry. -/
theorem actualScattering_eq_boundary (P : _root_.RHTower.D4BMEisensteinAbsoluteConvergenceParameter) :
    MayerScatteringNormalization.actualScattering P=
      MayerScatteringNormalization.archimedeanFactor P.s/2*positiveBoundary (2*P.s) := by
  have hw : 0 < (2*P.s).re := by
    norm_num [Complex.mul_re]
    linarith only [P.re_gt_one]
  rw [MayerScatteringNormalization.actualScattering_eq_cofactor,
    positiveBoundary_eq_cofactor hw]
  ring

/-- Independent scattering continuation agrees with the normalized actual inverse germ. -/
theorem scattering_germ {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    (fun v => MayerScatteringNormalization.scatteringEntry (v/2)) =ᶠ[𝓝[≠] w]
      fun v => MayerScatteringNormalization.archimedeanFactor (v/2)/2*positiveBoundary v := by
  filter_upwards [positiveBoundary_germ h0 h1] with v hv
  rw [MayerScatteringNormalization.scatteringEntry,hv]
  have he : 2*(v/2)=v := by ring
  rw [he]
  ring

private def archimedeanUnit (w : ℂ) : ℂ :=
  MayerScatteringNormalization.archimedeanFactor (w/2)/2

private theorem archimedeanUnit_analytic_unit {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    AnalyticAt ℂ archimedeanUnit w ∧ archimedeanUnit w ≠ 0 := by
  have hden : ∀ n : ℕ, w/2 ≠ -(n : ℂ) := by
    intro n hn
    have hr := congrArg Complex.re hn
    simp at hr
    linarith only [hr,h0,Nat.cast_nonneg (α := ℝ) n]
  have hnum : ∀ n : ℕ, w/2-1/2 ≠ -(n : ℂ) := by
    intro n hn
    have hr := congrArg Complex.re hn
    simp at hr
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · norm_num at hr
      linarith only [hr,h1]
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hnpos)
      linarith only [hr,h0,hn1]
  have hD₀ := Complex.Gamma_ne_zero hden
  have hN₀ := Complex.Gamma_ne_zero hnum
  have hD : AnalyticAt ℂ Complex.Gamma (w/2) :=
    (Meromorphic.Gamma (w/2)).analyticAt (Complex.continuousAt_Gamma _ hden)
  have hN : AnalyticAt ℂ Complex.Gamma (w/2-1/2) :=
    (Meromorphic.Gamma (w/2-1/2)).analyticAt (Complex.continuousAt_Gamma _ hnum)
  have hf : AnalyticAt ℂ (fun v : ℂ => v/2) w :=
    analyticAt_id.div analyticAt_const (by norm_num)
  have hDc : AnalyticAt ℂ (fun v : ℂ => Complex.Gamma (v/2)) w :=
    hD.comp (f := fun v : ℂ => v/2) hf
  have hNc : AnalyticAt ℂ (fun v : ℂ => Complex.Gamma (v/2-1/2)) w :=
    hN.comp (f := fun v : ℂ => v/2-1/2) (hf.sub analyticAt_const)
  have hπ : (Real.pi : ℂ)^(1/2 : ℂ) ≠ 0 := by
    intro he
    exact (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      ((Complex.cpow_eq_zero_iff (Real.pi : ℂ) (1/2 : ℂ)).mp he).1
  constructor
  · exact ((analyticAt_const.mul hNc).div hDc hD₀).div analyticAt_const (by norm_num)
  · exact div_ne_zero (div_ne_zero (mul_ne_zero hπ hN₀) hD₀) (by norm_num)

/-- The independently normalized scattering coefficient has the same pole multiplicity
at the exact spectral parameter s=w/2. -/
theorem scattering_order {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    meromorphicOrderAt MayerScatteringNormalization.scatteringEntry (w/2)=
      -((analyticOrderNatAt riemannZeta w : ℤ) : WithTop ℤ) := by
  have hc : meromorphicOrderAt
      (MayerScatteringNormalization.scatteringEntry ∘ fun v : ℂ => v/2) w=
      meromorphicOrderAt MayerScatteringNormalization.scatteringEntry (w/2) := by
    apply meromorphicOrderAt_comp_of_deriv_ne_zero
    · exact analyticAt_id.div analyticAt_const (by norm_num)
    · simp
  rw [← hc]
  simp only [Function.comp_def]
  rw [meromorphicOrderAt_congr (scattering_germ h0 h1)]
  change meromorphicOrderAt (archimedeanUnit*positiveBoundary) w=_
  obtain ⟨hA,hA₀⟩ := archimedeanUnit_analytic_unit h0 h1
  rw [meromorphicOrderAt_mul_of_ne_zero hA hA₀,positiveBoundary_order h0 h1]

/-- Exact pole criterion for the independent Poincare scattering continuation. -/
theorem scattering_pole_iff {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    meromorphicOrderAt MayerScatteringNormalization.scatteringEntry (w/2) < 0 ↔
      riemannZeta w=0 := by
  rw [scattering_order h0 h1,← positiveBoundary_order h0 h1]
  exact positiveBoundary_pole_iff h0 h1

#print axioms positiveBoundary_eq_cofactor
#print axioms negativeBoundary_zero
#print axioms positiveBoundary_germ
#print axioms meromorphicAt_positiveBoundary
#print axioms positiveBoundary_order
#print axioms positiveBoundary_pole_iff
#print axioms actualScattering_eq_boundary
#print axioms scattering_germ
#print axioms scattering_order
#print axioms scattering_pole_iff
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerBoundaryResolvent
