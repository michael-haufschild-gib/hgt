import GaloisForLFunctions.RHTower.Sieve.Buchstab.EntireCorrection
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Entire exponential factor and signed Buchstab moments

Removing the polar term gives an exponential of the entire complementary
exponential integral. Its differential equation determines all signed moments
of the actual delay profile.
-/

namespace RHTower.Sieve.Buchstab
open Set Filter Topology Complex MeasureTheory
noncomputable section


/-- The entire removable kernel (1 - exp(-z))/z. -/
def einComplexKernel := dslope (fun z : ℂ => -Complex.exp (-z)) 0

private theorem kernel_entire : Differentiable ℂ einComplexKernel := by
  have h : Differentiable ℂ (fun z : ℂ => -Complex.exp (-z)) := by fun_prop
  exact fun z => (analyticAt_dslope_of_analyticAt_of_analyticAt (h.analyticAt 0) (h.analyticAt z)).differentiableAt

theorem einComplexKernel_mul (z : ℂ) : z*einComplexKernel z = 1-Complex.exp (-z) := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [einComplexKernel,dslope_of_ne _ hz,slope_def_field]
    simp only [sub_zero,neg_zero,Complex.exp_zero]
    field_simp
    ring

private theorem kernel_real (s : ℝ) : einComplexKernel (s:ℂ) = (einKernel s:ℂ) := by
  by_cases hs : s = 0
  · subst s
    have hd := (((hasDerivAt_id (0:ℂ)).neg.cexp).neg).deriv
    simpa [einComplexKernel,dslope_same,einKernel,logIntegralKernel_zero] using hd
  · have h := einComplexKernel_mul (s:ℂ)
    have hs' : (s:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
    apply mul_left_cancel₀ hs'
    rw [h,einKernel,logIntegralKernel_of_ne hs]
    push_cast
    rw [Complex.exp_neg]
    field_simp [Complex.exp_ne_zero,hs']

private theorem existsEin : ∃ f : ℂ → ℂ, f 0=0 ∧ ∀ z, HasDerivAt f (einComplexKernel z) z := by
  obtain ⟨f,h₀,h⟩ := kernel_entire.isExactOn_univ.with_val_at 0 0
  exact ⟨f,h₀,fun z => h z (mem_univ _)⟩

/-- The entire Ein primitive normalized at the origin. -/
def entireEin := Classical.choose existsEin

theorem entireEin_zero : entireEin 0 = 0 := (Classical.choose_spec existsEin).1
theorem hasDerivAt_entireEin (z : ℂ) : HasDerivAt entireEin (einComplexKernel z) z :=
  (Classical.choose_spec existsEin).2 z

theorem entireEin_real (s : ℝ) : entireEin (s:ℂ) = (einCompare s:ℂ) := by
  let f (x : ℝ) := entireEin (x:ℂ) - (einCompare x:ℂ)
  have h (x : ℝ) : HasDerivAt f 0 x := by
    have h₁ := (hasDerivAt_entireEin (x:ℂ)).comp_ofReal
    rw [kernel_real] at h₁
    apply (h₁.fun_sub (hasDerivAt_einCompare x).ofReal_comp).congr_deriv
    exact sub_self _
  have hh := is_const_of_deriv_eq_zero (fun x => (h x).differentiableAt) (fun x => (h x).deriv) s 0
  apply sub_eq_zero.mp
  simpa only [f,Complex.ofReal_zero,entireEin_zero,show einCompare 0 = 0 by simp [einCompare],sub_self] using hh

/-- Removing the pole and restoring the constant term of the true Laplace transform. -/
def regularMass (z : ℂ) : ℂ := (enclosureLimit:ℂ) + z*(1+correctionMoment 0 z)

private theorem regularMass_entire : Differentiable ℂ regularMass := by
  intro z
  exact (((hasDerivAt_id z).mul ((hasDerivAt_correctionMoment 0 z).const_add 1)).const_add
    (enclosureLimit:ℂ)).differentiableAt

private theorem continuedMass_real (s : Ioi (0:ℝ)) : continuedMass (s.val:ℂ) = (laplaceMass s:ℂ) := by
  rw [continuedMass_eq_integral ⟨(s.val:ℂ),s.property⟩,laplaceMass,← integral_complex_ofReal]
  congr 1
  funext t
  push_cast
  rfl

private theorem regularMass_real_pos (s : Ioi (0:ℝ)) : regularMass (s.val:ℂ) = (regular s:ℂ) := by
  rw [regular_eq_mul s,← laplaceMass_eq_transform s,Complex.ofReal_mul,Complex.ofReal_add,
    Complex.ofReal_one,← continuedMass_real]
  dsimp only [regularMass,continuedMass]
  field_simp [Complex.ofReal_ne_zero.mpr s.property.ne']
  ring

/-- Global exponential formula, including every point on the negative real axis. -/
theorem regularMass_eq_exp (z : ℂ) :
    regularMass z = Complex.exp (entireEin z-(Real.eulerMascheroniConstant:ℂ)) := by
  let g (z : ℂ) := Complex.exp (entireEin z-(Real.eulerMascheroniConstant:ℂ))
  have hg : Differentiable ℂ g := fun z =>
    ((hasDerivAt_entireEin z).sub_const (Real.eulerMascheroniConstant:ℂ)).cexp.differentiableAt
  have ht : Tendsto (fun r : ℝ => (r:ℂ)) (𝓝[>] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have ha : AnalyticOnNhd ℂ regularMass univ := fun w _ => regularMass_entire.analyticAt w
  have hb : AnalyticOnNhd ℂ g univ := fun w _ => hg.analyticAt w
  have hfreq : ∃ᶠ w in 𝓝[≠] (0:ℂ), regularMass w = g w := ht.frequently (Filter.Eventually.frequently (by
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [regularMass_real_pos ⟨r,hr⟩]
      simp [g,regular,entireEin_real]))
  exact congrFun (ha.eq_of_frequently_eq hb hfreq) z

theorem regularMass_ne_zero (z : ℂ) : regularMass z ≠ 0 :=
  regularMass_eq_exp z ▸ Complex.exp_ne_zero _

/-- The meromorphic continuation of the Laplace transform omits the value -1
everywhere off its pole. -/
theorem continuedMass_ne_neg_one (z : {z : ℂ // z ≠ 0}) : continuedMass z.val ≠ -1 := by
  intro h
  apply regularMass_ne_zero z.val
  have he : regularMass z.val = z.val*(1+continuedMass z.val) := by
    dsimp [regularMass,continuedMass]
    field_simp [z.property]
    ring
  rw [he,h,add_neg_cancel,mul_zero]

theorem regularMass_ode (z : ℂ) : z*deriv regularMass z = (1-Complex.exp (-z))*regularMass z := by
  have hd := ((hasDerivAt_entireEin z).sub_const (Real.eulerMascheroniConstant:ℂ)).cexp
  rw [funext regularMass_eq_exp,hd.deriv,← einComplexKernel_mul]
  ring

private theorem deriv_x_mul (n : ℕ) (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    iteratedDeriv (n+1) (fun z => z*f z) 0 = (n+1:ℕ)*iteratedDeriv n f 0 := by
  rw [iteratedDeriv_fun_mul (f := fun z : ℂ => z) (g := f) contDiffAt_id (hf.contDiff.contDiffAt)]
  simp only [iteratedDeriv_fun_id_zero,mul_ite,mul_one,mul_zero,ite_mul,zero_mul]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

/-- The scaled derivatives of the regular factor are the actual correction
moments. The affine term contributes only at first order. -/
theorem regularMass_jet (n : ℕ) :
    iteratedDeriv (n+1) regularMass 0 =
      (n+1:ℕ)*((if n=0 then 1 else 0)+correctionMoment n 0) := by
  unfold regularMass
  rw [iteratedDeriv_const_add (Nat.succ_pos n),deriv_x_mul n _
    (fun z => ((hasDerivAt_correctionMoment 0 z).const_add 1).differentiableAt)]
  by_cases hn : n=0
  · simp [hn]
  · rw [iteratedDeriv_const_add (Nat.pos_of_ne_zero hn),iteratedDeriv_correction]
    simp [hn]

/-- Finite recurrence for every signed moment, obtained by differentiating
the exponential-integral differential equation at the former pole. -/
theorem regularMass_jet_recurrence (n : ℕ) :
    (n+1:ℕ)*iteratedDeriv (n+1) regularMass 0 =
      ∑ i ∈ Finset.range (n+2), ((n+1).choose i:ℂ)*
        (if i=0 then 0 else -(-1:ℂ)^i)*iteratedDeriv (n+1-i) regularMass 0 := by
  have h := congrArg (fun f : ℂ → ℂ => iteratedDeriv (n+1) f 0) (funext regularMass_ode)
  rw [deriv_x_mul n _ regularMass_entire.deriv,← iteratedDeriv_succ',
    iteratedDeriv_fun_mul (by fun_prop) regularMass_entire.contDiff.contDiffAt] at h
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  by_cases hi : i = 0
  · simp [hi]
  · rw [if_neg hi,iteratedDeriv_const_sub (Nat.pos_of_ne_zero hi)]
    change iteratedDeriv i (fun z : ℂ => -Complex.exp (-z)) 0 = _
    rw [iteratedDeriv_fun_neg,show (fun z : ℂ => Complex.exp (-z)) =
      (fun z : ℂ => Complex.exp ((-1)*z)) by funext z; simp,iteratedDeriv_cexp_const_mul]
    simp

private theorem signedMoment_real (k : ℕ) :
    correctionMoment k 0 =
      Complex.ofReal (∫ t in Ioi (0:ℝ), (-t)^k*(buchstab t-enclosureLimit)) := by
  rw [correctionMoment_eq_integral,← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  push_cast
  simp

/-- The first two nonconstant signed moments of the actual limiting error.
The first moment weights by t, and the second by t squared. -/
theorem integral_buchstab_linear_quadratic :
    (∫ t in Ioi (0:ℝ), t*(buchstab t-enclosureLimit)) = -enclosureLimit/4 ∧
    (∫ t in Ioi (0:ℝ), t^2*(buchstab t-enclosureLimit)) = -enclosureLimit/18 := by
  have h₁ := regularMass_jet 0
  have h₂ := regularMass_jet_recurrence 1
  have h₃ := regularMass_jet_recurrence 2
  have j₂ := regularMass_jet 1
  have j₃ := regularMass_jet 2
  have hv : regularMass 0 = (enclosureLimit:ℂ) := by simp [regularMass]
  norm_num [Finset.sum_range_succ,Nat.choose,correctionMoment_zero,hv] at h₁ h₂ h₃ j₂ j₃
  rw [signedMoment_real] at j₂ j₃
  simp only [pow_one,neg_mul,integral_neg,Complex.ofReal_neg,neg_sq] at j₂ j₃
  have realPart {z w : ℂ} (h : z = w) : z.re = w.re := congrArg Complex.re h
  replace h₁ := realPart h₁
  replace h₂ := realPart h₂
  replace h₃ := realPart h₃
  replace j₂ := realPart j₂
  replace j₃ := realPart j₃
  norm_num [Complex.mul_re] at h₁ h₂ h₃ j₂ j₃
  constructor <;> linarith only [h₁,h₂,h₃,j₂,j₃]

#print axioms regularMass_eq_exp
#print axioms continuedMass_ne_neg_one
#print axioms regularMass_jet_recurrence
#print axioms integral_buchstab_linear_quadratic

end
end RHTower.Sieve.Buchstab
