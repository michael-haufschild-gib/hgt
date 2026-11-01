import GaloisForLFunctions.ArithmeticHarmonicAnalysis.DilatedVonMangoldtJets
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.IntegerDilationThetaGammaIndependence

/-! Actual zeta dilations and logarithmic derivatives as rotated analytic germs.
Rotation places the common zero-free half-plane at the upper end. -/

open Complex Filter Set Topology
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped Classical Differential UpperEndDifferentialInstances UpperEndComplexTowerInstances
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.DilationGerms
open DilatedVonMangoldt
noncomputable section

def dilate (r : ℝ) (s : ℂ) : ℂ := riemannZeta ((r : ℂ)*s)

/-- Analyticity on the exact half-plane used by the actual Dirichlet expansion. -/
theorem dilate_analytic_right (r : ℝ) :
    AnalyticOnNhd ℂ (dilate r) {z : ℂ | 1 < r*z.re} := by
  apply DifferentiableOn.analyticOnNhd _
    (isOpen_lt continuous_const (continuous_const.mul continuous_re))
  intro z hz
  have hrs : 1 < ((r : ℂ)*z).re := by simpa using hz
  have hne : (r : ℂ)*z ≠ 1 := by
    intro he
    rw [he] at hrs
    norm_num at hrs
  exact ((differentiableAt_riemannZeta hne).comp z
    (differentiableAt_id.const_mul _)).differentiableWithinAt

/-- The logarithmic source is analytic on the same genuine zero-free half-plane. -/
theorem source_analytic_right (r : ℝ) :
    AnalyticOnNhd ℂ (source r) {z : ℂ | 1 < r*z.re} := by
  intro z hz
  have hrs : 1 < ((r : ℂ)*z).re := by simpa using hz
  have hζ : AnalyticAt ℂ riemannZeta ((r : ℂ)*z) := by
    have h := dilate_analytic_right 1 ((r : ℂ)*z) (by simpa using hrs)
    change AnalyticAt ℂ (fun s => riemannZeta ((1 : ℂ)*s)) ((r : ℂ)*z) at h
    simpa only [one_mul] using h
  change AnalyticAt ℂ (fun s => -(r : ℂ) *
    (deriv riemannZeta ((r : ℂ)*s) / riemannZeta ((r : ℂ)*s))) z
  exact analyticAt_const.mul
    ((hζ.deriv.div hζ (riemannZeta_ne_zero_of_one_lt_re hrs)).comp
      (analyticAt_const.mul analyticAt_id))

/-- Positive real dilation keeps the pole of zeta outside the physical upper half-plane. -/
theorem dilate_analytic_upper (r : ℝ) (hr : 0 < r) :
    AnalyticOnNhd ℂ (dilate r) (upperTail 0) := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_upperTail 0)
  intro z hz
  have hi : 0 < ((r : ℂ)*z).im := by
    simpa only [mul_im,ofReal_re,ofReal_im,zero_mul,add_zero] using mul_pos hr hz
  have hne : (r : ℂ)*z ≠ 1 := by
    intro he
    rw [he] at hi
    norm_num at hi
  exact ((differentiableAt_riemannZeta hne).comp z
    (differentiableAt_id.const_mul _)).differentiableWithinAt

private theorem rotated_re (z : ℂ) : (-I*z).re = z.im := by simp [mul_re]

theorem rotated_mem_right (r : ℝ) (hr : 0 < r) {z : ℂ}
    (hz : z ∈ upperTail (1/r)) : 1 < r*(-I*z).re := by
  change 1/r < z.im at hz
  rw [rotated_re,mul_comm]
  exact (div_lt_iff₀ hr).mp hz

theorem dilate_rotated_analytic (r : ℝ) (hr : 0 < r) :
    AnalyticOnNhd ℂ (fun z => dilate r (-I*z)) (upperTail (1/r)) := by
  intro z hz
  exact (dilate_analytic_right r _ (rotated_mem_right r hr hz)).comp
    (analyticAt_const.mul analyticAt_id)

theorem source_rotated_analytic (r : ℝ) (hr : 0 < r) :
    AnalyticOnNhd ℂ (fun z => source r (-I*z)) (upperTail (1/r)) := by
  intro z hz
  exact (source_analytic_right r _ (rotated_mem_right r hr hz)).comp
    (analyticAt_const.mul analyticAt_id)

def physicalZetaAnalytic (r : ℝ) (hr : 0 < r) : upperEndAnalyticSubring :=
  ⟨Germ.coeRingHom upperEndFilter (dilate r),⟨_,0,dilate_analytic_upper r hr,rfl⟩⟩

def rotatedZetaAnalytic (r : ℝ) (hr : 0 < r) : upperEndAnalyticSubring :=
  ⟨Germ.coeRingHom upperEndFilter (fun z => dilate r (-I*z)),
    ⟨_,1/r,dilate_rotated_analytic r hr,rfl⟩⟩

def rotatedSourceAnalytic (r : ℝ) (hr : 0 < r) : upperEndAnalyticSubring :=
  ⟨Germ.coeRingHom upperEndFilter (fun z => source r (-I*z)),
    ⟨_,1/r,source_rotated_analytic r hr,rfl⟩⟩

theorem deriv_dilate (r : ℝ) (s : ℂ) :
    deriv (dilate r) s = (r : ℂ)*deriv riemannZeta ((r : ℂ)*s) := by
  change deriv (fun z => riemannZeta ((r : ℂ)*z)) s = _
  simpa only [smul_eq_mul] using deriv_comp_mul_left (r : ℂ) riemannZeta s

/-- The source is the negative logarithmic derivative of the literal dilated function. -/
theorem source_eq_neg_logDeriv_dilate (r : ℝ) (s : ℂ) :
    source r s = -(deriv (dilate r) s / dilate r s) := by
  rw [source,_root_.RHTower.zetaLogDeriv,deriv_dilate,dilate]
  ring

/-- The rotation factor in the actual logarithmic differential equation is `I`. -/
theorem rotated_dilate_deriv (r : ℝ) (hr : 0 < r) {z : ℂ}
    (hz : z ∈ upperTail (1/r)) :
    deriv (fun w => dilate r (-I*w)) z = I*source r (-I*z)*dilate r (-I*z) := by
  have hne : dilate r (-I*z) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using rotated_mem_right r hr hz)
  rw [deriv_comp_mul_left,smul_eq_mul,source_eq_neg_logDeriv_dilate]
  calc
    _ = I * -(deriv (dilate r) (-I*z) / dilate r (-I*z) * dilate r (-I*z)) := by
      rw [div_mul_cancel₀ _ hne]
      ring
    _ = _ := by ring

def complexAnalytic : ℂ →+* upperEndAnalyticSubring :=
  upperEndPolyToAnalytic.comp Polynomial.C

theorem complexAnalytic_repr (c : ℂ) :
    upperEndAnalyticSubring.subtype (complexAnalytic c) =
      Germ.coeRingHom upperEndFilter (fun _ : ℂ => c) := by
  rw [complexAnalytic,RingHom.comp_apply,polyToAnalytic_subtype]
  congr 1
  ext z
  exact Polynomial.eval_C

theorem rotatedZetaAnalytic_ne_zero (r : ℝ) (hr : 0 < r) :
    rotatedZetaAnalytic r hr ≠ 0 := by
  intro h
  have hg := congrArg (fun a : upperEndAnalyticSubring => a.val) h
  change ((fun z => dilate r (-I*z)) : Germ upperEndFilter ℂ) =
    ((fun _ : ℂ => (0 : ℂ)) : Germ upperEndFilter ℂ) at hg
  have hz : ∀ᶠ z in upperEndFilter, dilate r (-I*z) = 0 := Germ.coe_eq.mp hg
  have hn : ∀ᶠ z in upperEndFilter, dilate r (-I*z) ≠ 0 := by
    rw [upperEndFilter_basis.eventually_iff]
    refine ⟨1/r,trivial,fun z hz => ?_⟩
    exact riemannZeta_ne_zero_of_one_lt_re (by simpa using rotated_mem_right r hr hz)
  obtain ⟨z,hz,hn⟩ := (hz.and hn).exists
  exact hn hz

/-- The actual first-order logarithmic equation holds in the analytic germ ring. -/
theorem rotatedZetaAnalytic_deriv (r : ℝ) (hr : 0 < r) :
    upperEndAnalyticDeriv (rotatedZetaAnalytic r hr) =
      complexAnalytic I * rotatedSourceAnalytic r hr * rotatedZetaAnalytic r hr := by
  apply Subtype.ext
  change upperEndGermDeriv ((fun z => dilate r (-I*z)) : Germ upperEndFilter ℂ) =
    (complexAnalytic I : Germ upperEndFilter ℂ) *
      ((fun z => source r (-I*z)) : Germ upperEndFilter ℂ) *
      ((fun z => dilate r (-I*z)) : Germ upperEndFilter ℂ)
  rw [show (complexAnalytic I : Germ upperEndFilter ℂ) =
    ((fun _ : ℂ => I) : Germ upperEndFilter ℂ) from complexAnalytic_repr I]
  rw [upperEndGermDeriv_coe,← Germ.coe_mul,← Germ.coe_mul,Germ.coe_eq]
  change ∀ᶠ z in upperEndFilter,
    deriv (fun w => dilate r (-I*w)) z = I*source r (-I*z)*dilate r (-I*z)
  rw [upperEndFilter_basis.eventually_iff]
  exact ⟨1/r,trivial,fun _ hz => rotated_dilate_deriv r hr hz⟩

def rotatedZetaMero (r : ℝ) (hr : 0 < r) : upperEndMeroField :=
  algebraMap upperEndAnalyticSubring upperEndMeroField (rotatedZetaAnalytic r hr)

def rotatedSourceMero (r : ℝ) (hr : 0 < r) : upperEndMeroField :=
  algebraMap upperEndAnalyticSubring upperEndMeroField (rotatedSourceAnalytic r hr)

theorem rotatedZetaMero_ne_zero (r : ℝ) (hr : 0 < r) : rotatedZetaMero r hr ≠ 0 := by
  intro h
  apply rotatedZetaAnalytic_ne_zero r hr
  apply IsFractionRing.injective upperEndAnalyticSubring upperEndMeroField
  simpa only [rotatedZetaMero,map_zero] using h

/-- Rotation identifies the meromorphic logarithmic derivative with `I` times the actual source. -/
theorem rotatedZetaMero_logDeriv (r : ℝ) (hr : 0 < r) :
    (rotatedZetaMero r hr)′ / rotatedZetaMero r hr =
      algebraMap ℂ upperEndMeroField I * rotatedSourceMero r hr := by
  apply (div_eq_iff (rotatedZetaMero_ne_zero r hr)).mpr
  rw [rotatedZetaMero,upperEndMeroFieldDifferential_algebraMap,
    rotatedZetaAnalytic_deriv,map_mul,map_mul]
  rfl

/-- A finite positive dilation packet admits a convergence line beyond every germ cutoff. -/
theorem exists_common_line {ι : Type*} [Fintype ι]
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (H : ℝ) :
    ∃ sigma : ℝ, H < sigma ∧ 0 < sigma ∧ ∀ i, 1 < r i*sigma := by
  classical
  let sigma := max (H+1) (1+∑ i, 1/r i)
  have hright : 1+∑ i, 1/r i ≤ sigma := le_max_right _ _
  have hleft : H+1 ≤ sigma := le_max_left _ _
  have hsum : 0 ≤ ∑ i, 1/r i :=
    Finset.sum_nonneg (fun i _ => (div_pos zero_lt_one (hr i)).le)
  refine ⟨sigma,by linarith only [hleft],by linarith only [hright,hsum],?_⟩
  intro i
  have hi : 1/r i ≤ ∑ j, 1/r j :=
    Finset.single_le_sum (fun j _ => (div_pos zero_lt_one (hr j)).le) (Finset.mem_univ i)
  have hri : 1/r i < sigma := by linarith only [hi,hright]
  simpa only [mul_comm] using (div_lt_iff₀ (hr i)).mp hri

#print axioms dilate_analytic_right
#print axioms source_analytic_right
#print axioms dilate_analytic_upper
#print axioms dilate_rotated_analytic
#print axioms source_rotated_analytic
#print axioms source_eq_neg_logDeriv_dilate
#print axioms rotated_dilate_deriv
#print axioms rotatedZetaAnalytic_ne_zero
#print axioms rotatedZetaAnalytic_deriv
#print axioms rotatedZetaMero_ne_zero
#print axioms rotatedZetaMero_logDeriv
#print axioms exists_common_line
end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.DilationGerms
