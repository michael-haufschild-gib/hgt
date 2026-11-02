import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCofactorContinuation
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerPositivePoleCoefficient
import GaloisForLFunctions.RHTower.ReflectionCocycleClass
import GaloisForLFunctions.HTGeometry.RiemannZetaMeromorphic

/-! The constant-mode scattering divisor is the excess of the actual Mayer
source determinant over its signed cofactor. Common zeros cancel with
exact multiplicity; the remaining divisor is precisely that of zeta. -/

open Complex Set Filter Topology
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerParameter
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScatteringMultiplicity

/-- The shifted numerator has no zero anywhere in the open critical strip. -/
theorem shifted_zeta_ne_zero {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    riemannZeta (w-1) ≠ 0 := by
  apply _root_.RHTower.riemannZeta_ne_zero_of_re_lt_zero
  · simpa only [Complex.sub_re,Complex.one_re] using sub_neg.mpr h1
  · intro n hn
    have hr := congrArg Complex.re hn
    norm_num [Complex.sub_re,Complex.mul_re] at hr
    linarith only [hr,h0,Nat.cast_nonneg (α := ℝ) n]

/-- Exact local factorization separates the cofactor's common-zero multiplicity. -/
theorem determinant_factorization {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    sourceDeterminant w 1=
      riemannZeta w*(-MayerPole.polePart w 1/(2*riemannZeta (w-1))) := by
  have hw1 : w ≠ 1 := by intro he; norm_num [he] at h1
  have hw2 : w ≠ 2 := by intro he; norm_num [he] at h1
  have h := MayerCofactorContinuation.zeta_cofactor_identity h0 hw1 hw2
  field_simp [shifted_zeta_ne_zero h0 h1]
  linear_combination h

/-- Actual determinant zeros consist exactly of zeta zeros and cofactor zeros. -/
theorem sourceDeterminant_zero_iff {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    sourceDeterminant w 1=0 ↔ riemannZeta w=0 ∨ MayerPole.polePart w 1=0 := by
  have hden : 2*riemannZeta (w-1) ≠ 0 :=
    mul_ne_zero (by norm_num) (shifted_zeta_ne_zero h0 h1)
  rw [determinant_factorization h0 h1,mul_eq_zero]
  simp only [div_eq_zero_iff,neg_eq_zero,hden,or_false]

/-- The remainder determinant has three exact, possibly overlapping zero causes. -/
theorem regularPart_zero_iff {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    MayerPole.regularPart w 1=0 ↔
      riemannZeta w=0 ∨ MayerPole.polePart w 1=0 ∨ riemannZeta (w-1)=-(1/2 : ℂ) := by
  have hw1 : w ≠ 1 := by intro he; norm_num [he] at h1
  have hw2 : w ≠ 2 := by intro he; norm_num [he] at h1
  have hfactor : 1+2*riemannZeta (w-1)=0 ↔ riemannZeta (w-1)=-(1/2 : ℂ) := by
    constructor
    · intro h
      linear_combination (1/2 : ℂ)*h
    · intro h
      linear_combination 2*h
  rw [MayerCofactorContinuation.regularPart_eq_shifted_zeta_factor h0 hw1 hw2,
    mul_eq_zero,hfactor,sourceDeterminant_zero_iff h0 h1]
  tauto

/-- Every strip zero of zeta is a zero of the actual positive-unit determinant. -/
theorem sourceDeterminant_zero_of_zeta_zero {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1)
    (hz : riemannZeta w=0) : sourceDeterminant w 1=0 := by
  rw [determinant_factorization h0 h1,hz,zero_mul]

/-- A strip zeta zero supplies a genuine positive-unit eigenfunction of the
holomorphic remainder, because the full source's constant zeta mode vanishes. -/
theorem remainder_eigenfunction_of_zeta_zero {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1)
    (hz : riemannZeta w=0) :
    ∃ f : MayerCutoff.DiscSpace, f ≠ 0 ∧ remainder w f=f := by
  have hd := sourceDeterminant_zero_of_zeta_zero h0 h1 hz
  rw [sourceDeterminant_eq h0] at hd
  obtain ⟨f,hf0,hf⟩ := (MayerFredholm.determinant_eq_zero_iff_eigenvector h0 one_ne_zero).mp hd
  refine ⟨f,hf0,?_⟩
  rw [← source_eq h0,source,hz,zero_smul,zero_add,inv_one,one_smul] at hf
  exact hf

/-- The source half-plane admits a single holomorphic cofactor, including at one. -/
private theorem analyticOn_cofactor :
    AnalyticOnNhd ℂ (fun w => MayerPole.polePart w 1) {w : ℂ | 0 < w.re} :=
  (MayerPole.differentiableOn_polePart 1).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

/-- Positive-real nonvanishing prevents an identically vanishing cofactor germ. -/
theorem cofactor_order_ne_top {w : ℂ} (h0 : 0 < w.re) :
    analyticOrderAt (fun v => MayerPole.polePart v 1) w ≠ ⊤ := by
  apply analyticOn_cofactor.analyticOrderAt_ne_top_of_isPreconnected
    MayerCofactorContinuation.rightHalfPlane_preconnected (x := 1) (by norm_num) h0
  rw [(analyticOn_cofactor 1 (by norm_num)).analyticOrderAt_eq_zero.mpr
    MayerPositivePole.polePart_one_one_ne_zero]
  exact ENat.zero_ne_top

/-- The shifted-zeta factor is a holomorphic unit on the critical strip. -/
private def scatteringUnit (w : ℂ) : ℂ := -1/(2*riemannZeta (w-1))

private theorem analyticAt_scatteringUnit {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    AnalyticAt ℂ scatteringUnit w := by
  have hs : w-1 ≠ 1 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.sub_re,Complex.one_re] at hr
    linarith only [hr,h1]
  exact analyticAt_const.div
    (analyticAt_const.mul ((GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta hs).comp
      (f := fun z : ℂ => z-1) (analyticAt_id.sub analyticAt_const)))
    (mul_ne_zero (by norm_num) (shifted_zeta_ne_zero h0 h1))

private theorem scatteringUnit_ne_zero {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    scatteringUnit w ≠ 0 :=
  div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) (shifted_zeta_ne_zero h0 h1))

/-- Every determinant zero has exactly its cofactor order plus the zeta order.
This identity retains common zeros instead of testing a totalized quotient. -/
theorem determinant_order {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    analyticOrderAt (fun v => sourceDeterminant v 1) w=
      analyticOrderAt (fun v => MayerPole.polePart v 1) w+analyticOrderAt riemannZeta w := by
  have hw1 : w ≠ 1 := by intro he; norm_num [he] at h1
  have hZ := (GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta hw1)
  have hB := analyticOn_cofactor w h0
  have hU := analyticAt_scatteringUnit h0 h1
  have he : (fun v => sourceDeterminant v 1) =ᶠ[𝓝 w]
      riemannZeta*(fun v => MayerPole.polePart v 1)*scatteringUnit := by
    have ho : IsOpen {v : ℂ | 0 < v.re ∧ v.re < 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    filter_upwards [ho.mem_nhds ⟨h0,h1⟩] with v hv
    rw [determinant_factorization hv.1 hv.2]
    change _=riemannZeta v*MayerPole.polePart v 1*(-1/(2*riemannZeta (v-1)))
    ring
  rw [analyticOrderAt_congr he,analyticOrderAt_mul (hZ.mul hB) hU,
    analyticOrderAt_mul hZ hB,hU.analyticOrderAt_eq_zero.mpr (scatteringUnit_ne_zero h0 h1),
    add_zero,add_comm]

private theorem zeta_order_ne_top {w : ℂ} (hw1 : w ≠ 1) :
    analyticOrderAt riemannZeta w ≠ ⊤ := by
  have hZ : AnalyticOnNhd ℂ _root_.RHTower.zetaResidueUnit univ :=
    fun z _ => _root_.RHTower.analyticAt_zetaResidueUnit z
  have hZ1 : _root_.RHTower.zetaResidueUnit 1 ≠ 0 := by
    simp only [_root_.RHTower.zetaResidueUnit,Function.update_self,ne_eq,one_ne_zero,not_false_eq_true]
  have hfinite := hZ.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (x := 1) (mem_univ 1) (mem_univ w)
    (by rw [(hZ 1 (mem_univ 1)).analyticOrderAt_eq_zero.mpr hZ1]; exact ENat.zero_ne_top)
  intro htop
  apply hfinite
  apply analyticOrderAt_eq_top.mpr
  filter_upwards [analyticOrderAt_eq_top.mp htop,isOpen_ne.mem_nhds hw1] with z hz hz1
  rw [_root_.RHTower.zetaResidueUnit,Function.update_of_ne hz1,hz,mul_zero]

/-- Both contributions to the determinant divisor are finite. -/
theorem determinant_order_ne_top {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    analyticOrderAt (fun v => sourceDeterminant v 1) w ≠ ⊤ := by
  have hw1 : w ≠ 1 := by intro he; norm_num [he] at h1
  obtain ⟨n,hn⟩ := ENat.ne_top_iff_exists.mp (cofactor_order_ne_top h0)
  obtain ⟨m,hm⟩ := ENat.ne_top_iff_exists.mp (zeta_order_ne_top hw1)
  rw [determinant_order h0 h1,← hn,← hm,← Nat.cast_add]
  exact ENat.coe_ne_top _

/-- Exact finite multiplicities of the scattering divisor after cancellation. -/
theorem determinant_orderNat {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    analyticOrderNatAt (fun v => sourceDeterminant v 1) w=
      analyticOrderNatAt (fun v => MayerPole.polePart v 1) w+analyticOrderNatAt riemannZeta w := by
  have hw1 : w ≠ 1 := by intro he; norm_num [he] at h1
  simp only [analyticOrderNatAt,determinant_order h0 h1,
    ENat.toNat_add (cofactor_order_ne_top h0) (zeta_order_ne_top hw1)]

/-- The scattering-sector event is exactly excess determinant order over cofactor order. -/
theorem zeta_zero_iff_excess_order {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    riemannZeta w=0 ↔
      analyticOrderAt (fun v => MayerPole.polePart v 1) w <
        analyticOrderAt (fun v => sourceDeterminant v 1) w := by
  have hw1 : w ≠ 1 := by intro he; norm_num [he] at h1
  have hz := (GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta hw1)
  rw [← hz.analyticOrderAt_ne_zero,determinant_order h0 h1]
  obtain ⟨n,hn⟩ := ENat.ne_top_iff_exists.mp (cofactor_order_ne_top h0)
  rw [← hn]
  cases h : analyticOrderAt riemannZeta w with
  | top => simp
  | coe m => norm_cast; omega

#print axioms shifted_zeta_ne_zero
#print axioms determinant_factorization
#print axioms sourceDeterminant_zero_iff
#print axioms regularPart_zero_iff
#print axioms sourceDeterminant_zero_of_zeta_zero
#print axioms remainder_eigenfunction_of_zeta_zero
#print axioms cofactor_order_ne_top
#print axioms determinant_order
#print axioms determinant_order_ne_top
#print axioms determinant_orderNat
#print axioms zeta_zero_iff_excess_order

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScatteringMultiplicity
