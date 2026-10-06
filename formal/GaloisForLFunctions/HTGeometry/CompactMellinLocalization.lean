import GaloisForLFunctions.HTGeometry.FractionalCompactMultiplier
import GaloisForLFunctions.HTGeometry.PositiveQuadrantMellinLines
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMRetardedCompactWeakRealization

/-!
# Actual compact Mellin localization and first Euler coefficients

Fixed smooth cutoffs equal one near the stationary physical box and the full
Mellin parameter square. The literal weighted coefficient is jointly smooth:
on physical support both coordinates are positive, and off that support the
complete coefficient is locally zero. Joint compactness yields uniform
fractional and L2 multiplier bounds, also for both first Euler coefficients.

The localized logarithmic profile has an exact first Euler derivative and an
exact Schwartz realization. No uniform Schwartz seminorm is assumed. The
remaining BAG task is to assemble these bounds with the logarithmic chart
estimate into weighted Mellin Fourier energy and attach the actual exterior.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped FourierTransform Topology ContDiff ENNReal
namespace GaloisForLFunctions.HTGeometry
private abbrev E := HTGeometry.QuadrantLogSpace

private def physicalBox (a b : ℝ) : Set E := {x | ∀i, x i∈Icc a b}
private def physicalOpenBox (a b : ℝ) : Set E := {x | ∀i, x i∈Ioo a b}

private theorem compact_physicalBox (a b : ℝ) : IsCompact (physicalBox a b) := by
  have hh := (isCompact_univ_pi (fun _ : Fin 2 => isCompact_Icc (a := a) (b := b))).image
    (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ))
  convert hh using 1
  ext x
  constructor
  · intro hx
    refine ⟨WithLp.ofLp x,?_,?_⟩
    · exact fun i _ => hx i
    · exact WithLp.toLp_ofLp 2 x
  · rintro ⟨y,hy,rfl⟩
    exact fun i => hy i (mem_univ i)

private theorem open_physicalOpenBox (a b : ℝ) : IsOpen (physicalOpenBox a b) := by
  have hh : IsOpen (⋂i : Fin 2, {x : E | x i∈Ioo a b}) :=
    isOpen_iInter_of_finite (fun i : Fin 2 =>
      isOpen_Ioo.preimage (EuclideanSpace.proj i : E→L[ℝ]ℝ).continuous)
  simpa only [physicalOpenBox,Set.iInter_setOf] using hh

private theorem physical_cutoff_exists :
    ∃χ : E→ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ⊆physicalOpenBox (1/8) 8 ∧
      ∃ V : Set E, IsOpen V ∧ physicalBox (1/4) 4⊆V ∧ ∀x∈V, χ x=1 := by
  apply RHTower.D4BMRetardedCompactWeakRealization.exists_contDiff_cutoff
    (compact_physicalBox (1/4) 4) (open_physicalOpenBox (1/8) 8)
  intro x hx i
  have hi := hx i
  constructor <;> linarith only [hi.1,hi.2]

private theorem parameter_cutoff_exists :
    ∃η : E→ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      tsupport η⊆physicalOpenBox (-1) 4 ∧
      ∃ V : Set E, IsOpen V ∧ physicalBox 1 2⊆V ∧ ∀x∈V, η x=1 := by
  apply RHTower.D4BMRetardedCompactWeakRealization.exists_contDiff_cutoff
    (compact_physicalBox 1 2) (open_physicalOpenBox (-1) 4)
  intro x hx i
  have hi := hx i
  constructor <;> linarith only [hi.1,hi.2]

private def mellinCoefficient (η χ : E→ℝ) (z : E×E) : ℂ :=
  ((η z.1*χ z.2*Real.exp (z.1 0*Real.log (z.2 0)+z.1 1*Real.log (z.2 1)) : ℝ) : ℂ)

private theorem mellin_coefficient_smooth (η χ : E→ℝ)
    (hη : ContDiff ℝ ∞ η) (hχ : ContDiff ℝ ∞ χ)
    (hsupp : tsupport χ⊆physicalOpenBox (1/8) 8) :
    ContDiff ℝ ∞ (mellinCoefficient η χ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hx : z.2∈tsupport χ
  · have hpos (i : Fin 2) : 0<z.2 i := lt_trans (by norm_num) ((hsupp hx i).1)
    have hc (i : Fin 2) : ContDiff ℝ ∞ (fun w : E×E => w.2 i) :=
      (EuclideanSpace.proj i : E→L[ℝ]ℝ).contDiff.comp contDiff_snd
    have hp (i : Fin 2) : ContDiff ℝ ∞ (fun w : E×E => w.1 i) :=
      (EuclideanSpace.proj i : E→L[ℝ]ℝ).contDiff.comp contDiff_fst
    have hr : ContDiffAt ℝ ∞ (fun w : E×E =>
        η w.1*χ w.2*Real.exp (w.1 0*Real.log (w.2 0)+w.1 1*Real.log (w.2 1))) z :=
      ((hη.comp contDiff_fst).contDiffAt.mul (hχ.comp contDiff_snd).contDiffAt).mul
        (((hp 0).contDiffAt.mul ((hc 0).contDiffAt.log (hpos 0).ne')).add
          ((hp 1).contDiffAt.mul ((hc 1).contDiffAt.log (hpos 1).ne'))).exp
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp z hr
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    have he := (notMem_tsupport_iff_eventuallyEq.mp hx).comp_tendsto continuous_snd.continuousAt
    filter_upwards [he] with w hw
    change χ w.2=0 at hw
    simp only [mellinCoefficient,hw,mul_zero,zero_mul,Complex.ofReal_zero]

private theorem mellin_coefficient_support (η χ : E→ℝ) :
    tsupport (mellinCoefficient η χ)⊆tsupport η×ˢtsupport χ := by
  apply closure_minimal ?_ ((isClosed_tsupport η).prod (isClosed_tsupport χ))
  intro z hz
  constructor
  · apply subset_tsupport η
    intro he
    exact hz (by simp [mellinCoefficient,he])
  · apply subset_tsupport χ
    intro he
    exact hz (by simp [mellinCoefficient,he])

private theorem mellin_coefficient_compact (η χ : E→ℝ)
    (hη : HasCompactSupport η) (hχ : HasCompactSupport χ) :
    HasCompactSupport (mellinCoefficient η χ) :=
  (hη.prod hχ).of_isClosed_subset isClosed_closure (mellin_coefficient_support η χ)

/-- Fixed physical cutoff, equal to one near the BAG stationary box. -/
def mellinLocalizationCutoff : E→ℝ := Classical.choose physical_cutoff_exists

private def mellinParameterCutoff : E→ℝ := Classical.choose parameter_cutoff_exists

/-- The physical localization is smooth, compactly supported away from both
axes, and identically one on an open neighborhood of the full stationary box. -/
theorem mellinLocalizationCutoff_spec :
    ContDiff ℝ ∞ mellinLocalizationCutoff ∧ HasCompactSupport mellinLocalizationCutoff ∧
      (∀x∈tsupport mellinLocalizationCutoff, ∀i, x i∈Ioo (1/8 : ℝ) 8) ∧
      ∃ V : Set E, IsOpen V ∧ {x : E | ∀i, x i∈Icc (1/4 : ℝ) 4}⊆V ∧
        ∀x∈V, mellinLocalizationCutoff x=1 := Classical.choose_spec physical_cutoff_exists

private theorem mellinParameterCutoff_spec :
    ContDiff ℝ ∞ mellinParameterCutoff ∧ HasCompactSupport mellinParameterCutoff ∧
      tsupport mellinParameterCutoff⊆physicalOpenBox (-1) 4 ∧
      ∃ V : Set E, IsOpen V ∧ physicalBox 1 2⊆V ∧ ∀x∈V, mellinParameterCutoff x=1 :=
  Classical.choose_spec parameter_cutoff_exists

/-- Actual compact extension in Mellin parameters and physical variables. -/
def compactMellinCoefficient (z : E×E) : ℂ :=
  mellinCoefficient mellinParameterCutoff mellinLocalizationCutoff z

/-- Joint smoothness includes the coordinate axes, where localization is locally zero. -/
theorem compactMellinCoefficient_smooth : ContDiff ℝ ∞ compactMellinCoefficient :=
  mellin_coefficient_smooth _ _ mellinParameterCutoff_spec.1
    mellinLocalizationCutoff_spec.1 mellinLocalizationCutoff_spec.2.2.1

/-- Both parameter and physical supports are compact. -/
theorem hasCompactSupport_compactMellinCoefficient : HasCompactSupport compactMellinCoefficient :=
  mellin_coefficient_compact _ _ mellinParameterCutoff_spec.2.1 mellinLocalizationCutoff_spec.2.1

/-- The extension agrees exactly with the weighted physical cutoff on every
Mellin parameter in the complete compact parameter square. -/
theorem compactMellinCoefficient_eq
    (σ : {q : E // ∀i, q i∈Icc (1 : ℝ) 2}) (x : E) :
    compactMellinCoefficient (σ.1,x)=
      ((mellinLocalizationCutoff x*Real.exp (σ.1 0*Real.log (x 0)+σ.1 1*Real.log (x 1)) : ℝ) : ℂ) := by
  obtain ⟨V,_,hV,hη⟩ := mellinParameterCutoff_spec.2.2.2
  have he := hη σ.1 (hV σ.2)
  simp only [compactMellinCoefficient,mellinCoefficient,he,one_mul]

/-- The coefficient on the value of the physical function after one log derivative. -/
def compactMellinEulerValue (i : Fin 2) (z : E×E) : ℂ :=
  -((z.2 i : ℝ) : ℂ)*fderiv ℝ compactMellinCoefficient z (0,HTGeometry.quadrantLogBasis i)

/-- The coefficient on the corresponding physical derivative after one log derivative. -/
def compactMellinEulerDerivative (i : Fin 2) (z : E×E) : ℂ :=
  -((z.2 i : ℝ) : ℂ)*compactMellinCoefficient z

/-- All actual first Euler coefficients are jointly smooth and compactly supported. -/
theorem compactMellinEuler_coefficients (i : Fin 2) :
    (ContDiff ℝ ∞ (compactMellinEulerValue i) ∧ HasCompactSupport (compactMellinEulerValue i)) ∧
    (ContDiff ℝ ∞ (compactMellinEulerDerivative i) ∧ HasCompactSupport (compactMellinEulerDerivative i)) := by
  have hc : ContDiff ℝ ∞ (fun z : E×E => -((z.2 i : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp
      ((EuclideanSpace.proj i : E→L[ℝ]ℝ).contDiff.comp contDiff_snd)).neg
  have hd : ContDiff ℝ ∞ (fun z : E×E =>
      fderiv ℝ compactMellinCoefficient z (0,HTGeometry.quadrantLogBasis i)) :=
    (compactMellinCoefficient_smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  exact ⟨⟨hc.mul hd,
      (hasCompactSupport_compactMellinCoefficient.fderiv_apply ℝ (0,HTGeometry.quadrantLogBasis i)).mul_left⟩,
    ⟨hc.mul compactMellinCoefficient_smooth,hasCompactSupport_compactMellinCoefficient.mul_left⟩⟩

/-- Euler differentiation keeps both physical coordinates in the same compact
positive region as the original coefficient. -/
theorem compactMellinEuler_support (i : Fin 2) :
    tsupport (compactMellinEulerValue i)⊆tsupport compactMellinCoefficient ∧
      tsupport (compactMellinEulerDerivative i)⊆tsupport compactMellinCoefficient := by
  exact ⟨tsupport_mul_subset_right.trans (tsupport_fderiv_apply_subset ℝ (0,HTGeometry.quadrantLogBasis i)),
    tsupport_mul_subset_right⟩

/-- The literal Mellin coefficient and its two coefficients in one Euler derivative. -/
def compactMellinJetCoefficient (i : Fin 2) (k : Fin 3) : E×E→ℂ :=
  match k with
  | 0 => compactMellinCoefficient
  | 1 => compactMellinEulerValue i
  | _ => compactMellinEulerDerivative i

/-- All three members of the actual joint parameter family have proved compact smooth data. -/
theorem compactMellinJetCoefficient_spec (i : Fin 2) (k : Fin 3) :
    ContDiff ℝ ∞ (compactMellinJetCoefficient i k) ∧
      HasCompactSupport (compactMellinJetCoefficient i k) := by
  fin_cases k
  · exact ⟨compactMellinCoefficient_smooth,hasCompactSupport_compactMellinCoefficient⟩
  · exact (compactMellinEuler_coefficients i).1
  · exact (compactMellinEuler_coefficients i).2

/-- Uniform admitted physical fractional energy for the actual Mellin coefficient
and both first Euler coefficients. Constants are independent of parameter and input. -/
theorem compactMellinJetCoefficient_uniform_fractional_energy
    (s : {r : ℝ // r∈Ioo (0 : ℝ) 1}) (i : Fin 2) (k : Fin 3) (v : E) :
    ∃ C : ℝ, 0<C ∧ ∀(σ : E) (f : SchwartzMap E ℂ),
      let L := ∫⁻ h in Ioi (0 : ℝ), ∫⁻ x : E,
        ENNReal.ofReal (‖compactMellinJetCoefficient i k (σ,x)*f x-
          compactMellinJetCoefficient i k (σ,x+h • v)*f (x+h • v)‖^2*h^(-(1+2*s.1)))
      L < (∞ : ℝ≥0∞) ∧ L ≤ ENNReal.ofReal C*
        (ENNReal.ofReal (∫ξ : E, |inner ℝ v ξ|^(2*s.1)*‖(𝓕 f) ξ‖^2)+
          ENNReal.ofReal (∫x : E, ‖f x‖^2)) := by
  exact compact_parameter_multiplier_fractional_schwartz s
    ⟨compactMellinJetCoefficient i k,(compactMellinJetCoefficient_spec i k).1.of_le (by simp),
      (compactMellinJetCoefficient_spec i k).2⟩ v

private def mellinCoord (i : Fin 2) : E→L[ℝ]ℝ := EuclideanSpace.proj i

private def mellinLogNodeDerivative (u : E) : E→L[ℝ]E :=
  (((-Real.exp (-u 0)) • mellinCoord 0).smulRight (HTGeometry.quadrantLogBasis 0))+
    (((-Real.exp (-u 1)) • mellinCoord 1).smulRight (HTGeometry.quadrantLogBasis 1))

private theorem mellin_logNode_hasFDeriv (u : E) :
    HasFDerivAt HTGeometry.quadrantLogNode (mellinLogNodeDerivative u) u := by
  have h (i : Fin 2) := (((mellinCoord i).hasFDerivAt (x := u)).neg.exp).smul_const
    (HTGeometry.quadrantLogBasis i)
  apply ((h 0).add (h 1)).congr_fderiv
  ext v
  simp [mellinCoord,mellinLogNodeDerivative]

private theorem mellin_logNode_basis (u : E) (i : Fin 2) :
    mellinLogNodeDerivative u (HTGeometry.quadrantLogBasis i)=
      (-HTGeometry.quadrantLogNode u i) • HTGeometry.quadrantLogBasis i := by
  fin_cases i <;>
    simp [mellinLogNodeDerivative,mellinCoord,HTGeometry.quadrantLogBasis,HTGeometry.quadrantLogNode_apply]

/-- Compactly localized logarithmic profile with the actual joint Mellin coefficient. -/
def compactLocalizedMellinProfile (σ : E) (f : SchwartzMap E ℂ) (u : E) : ℂ :=
  compactMellinCoefficient (σ,HTGeometry.quadrantLogNode u)*f (HTGeometry.quadrantLogNode u)

/-- Exact identification with the desired weighted log pullback on the moving Mellin lines. -/
theorem compactLocalizedMellinProfile_eq
    (σ : {q : E // ∀i, q i∈Icc (1 : ℝ) 2}) (f : SchwartzMap E ℂ) (u : E) :
    compactLocalizedMellinProfile σ.1 f u=
      ((Real.exp (-σ.1 0*u 0-σ.1 1*u 1) : ℝ) : ℂ)*
        (mellinLocalizationCutoff (HTGeometry.quadrantLogNode u) : ℂ)*f (HTGeometry.quadrantLogNode u) := by
  rw [compactLocalizedMellinProfile,compactMellinCoefficient_eq σ]
  simp only [HTGeometry.quadrantLogNode_apply,Real.log_exp,Complex.ofReal_mul]
  rw [show σ.1 0*(-u 0)+σ.1 1*(-u 1)=-σ.1 0*u 0-σ.1 1*u 1 by ring]
  ring

/-- Exact first logarithmic derivative. Both the coefficient derivative and the
physical derivative of the input remain, with their literal Euler coefficients. -/
theorem compactLocalizedMellinProfile_euler (σ : E) (f : SchwartzMap E ℂ) (u : E) (i : Fin 2) :
    fderiv ℝ (compactLocalizedMellinProfile σ f) u (HTGeometry.quadrantLogBasis i)=
      compactMellinEulerValue i (σ,HTGeometry.quadrantLogNode u)*f (HTGeometry.quadrantLogNode u)+
        compactMellinEulerDerivative i (σ,HTGeometry.quadrantLogNode u)*
          fderiv ℝ f (HTGeometry.quadrantLogNode u) (HTGeometry.quadrantLogBasis i) := by
  have hn := mellin_logNode_hasFDeriv u
  have hp := (hasFDerivAt_const σ u).prodMk hn
  have hA := (compactMellinCoefficient_smooth.differentiable (by simp)
    (σ,HTGeometry.quadrantLogNode u)).hasFDerivAt.comp u hp
  have hf := f.differentiableAt.hasFDerivAt.comp u hn
  have hd := (hA.mul hf).fderiv
  have hpair : ((0 : E→L[ℝ]E).prod (mellinLogNodeDerivative u))
      (HTGeometry.quadrantLogBasis i)=
        (-HTGeometry.quadrantLogNode u i) • (0,HTGeometry.quadrantLogBasis i) := by
    simp only [ContinuousLinearMap.prod_apply,zero_apply,mellin_logNode_basis,Prod.smul_mk,smul_zero]
  change fderiv ℝ (compactLocalizedMellinProfile σ f) u= _ at hd
  rw [hd]
  simp only [add_apply,smul_apply,ContinuousLinearMap.comp_apply,mellin_logNode_basis,hpair,
    map_smul,Complex.real_smul,smul_eq_mul,Complex.ofReal_neg,Function.comp_apply,
    compactMellinEulerValue,compactMellinEulerDerivative]
  ring

/-- Every jet coefficient remains in the fixed positive physical box. -/
theorem compactMellinJetCoefficient_support (i : Fin 2) (k : Fin 3) :
    ∀z∈tsupport (compactMellinJetCoefficient i k), ∀j, z.2 j∈Ioo (1/8 : ℝ) 8 := by
  have hs : tsupport (compactMellinJetCoefficient i k)⊆tsupport compactMellinCoefficient := by
    fin_cases k
    · exact Subset.rfl
    · exact (compactMellinEuler_support i).1
    · exact (compactMellinEuler_support i).2
  intro z hz j
  exact mellinLocalizationCutoff_spec.2.2.1 z.2
    ((mellin_coefficient_support mellinParameterCutoff mellinLocalizationCutoff) (hs hz)).2 j

/-- The actual coefficient family also has a uniform L2 mass bound. -/
theorem compactMellinJetCoefficient_uniform_mass (i : Fin 2) (k : Fin 3) :
    ∃ C : ℝ, 0<C ∧ ∀(σ : E) (f : E→ℂ),
      (∫⁻ x : E, ENNReal.ofReal (‖compactMellinJetCoefficient i k (σ,x)*f x‖^2)) ≤
        ENNReal.ofReal C*∫⁻ x : E, ENNReal.ofReal (‖f x‖^2) := by
  obtain ⟨M,hM⟩ := (compactMellinJetCoefficient_spec i k).2.exists_bound_of_continuous
    (compactMellinJetCoefficient_spec i k).1.continuous
  refine ⟨M^2+1,by positivity,fun σ f => ?_⟩
  calc (∫⁻ x : E, ENNReal.ofReal (‖compactMellinJetCoefficient i k (σ,x)*f x‖^2))
      ≤ ∫⁻ x : E, ENNReal.ofReal (M^2)*ENNReal.ofReal (‖f x‖^2) := by
        apply lintegral_mono
        intro x
        change ENNReal.ofReal (‖compactMellinJetCoefficient i k (σ,x)*f x‖^2) ≤
          ENNReal.ofReal (M^2)*ENNReal.ofReal (‖f x‖^2)
        rw [norm_mul,mul_pow,ENNReal.ofReal_mul (sq_nonneg _)]
        exact mul_le_mul_left (ENNReal.ofReal_le_ofReal
          (pow_le_pow_left₀ (norm_nonneg _) (hM (σ,x)) 2)) _
    _ = ENNReal.ofReal (M^2)*∫⁻ x : E, ENNReal.ofReal (‖f x‖^2) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith : M^2 ≤ M^2+1)) _

private def mellinPhysicalLocalize (f : SchwartzMap E ℂ) : SchwartzMap E ℂ := by
  have hc : HasCompactSupport (fun x : E => (mellinLocalizationCutoff x : ℂ)) :=
    mellinLocalizationCutoff_spec.2.1.comp_left Complex.ofReal_zero
  have hprod : HasCompactSupport (fun x : E => (mellinLocalizationCutoff x : ℂ)*f x) := hc.mul_right
  exact hprod.toSchwartzMap
    ((Complex.ofRealCLM.contDiff.comp mellinLocalizationCutoff_spec.1).mul (f.smooth ⊤))

/-- The actual localized moving-line logarithmic profile, as a proved Schwartz function. -/
def compactLocalizedMellinSchwartz
    (σ : {q : E // ∀i, q i∈Icc (1 : ℝ) 2}) (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  HTGeometry.PositiveLine.quadrantLogSchwartz
    (fun i => ⟨σ.1 i,zero_lt_one.trans_le (σ.2 i).1⟩) (mellinPhysicalLocalize f)

/-- Exact Schwartz realization; membership here supplies no assumed uniform seminorm budget. -/
theorem compactLocalizedMellinSchwartz_apply
    (σ : {q : E // ∀i, q i∈Icc (1 : ℝ) 2}) (f : SchwartzMap E ℂ) (u : E) :
    compactLocalizedMellinSchwartz σ f u=compactLocalizedMellinProfile σ.1 f u := by
  rw [compactLocalizedMellinSchwartz,HTGeometry.PositiveLine.quadrantLogSchwartz_apply,
    compactLocalizedMellinProfile_eq σ f u,Complex.real_smul]
  change ((Real.exp (-σ.1 0*u 0-σ.1 1*u 1) : ℝ) : ℂ)*
      ((mellinLocalizationCutoff (HTGeometry.quadrantLogNode u) : ℂ)*f (HTGeometry.quadrantLogNode u))= _
  ring

/-- The exact Euler derivative belongs to the same literal localized Schwartz profile. -/
theorem compactLocalizedMellinSchwartz_euler
    (σ : {q : E // ∀i, q i∈Icc (1 : ℝ) 2}) (f : SchwartzMap E ℂ) (u : E) (i : Fin 2) :
    fderiv ℝ (compactLocalizedMellinSchwartz σ f) u (HTGeometry.quadrantLogBasis i)=
      compactMellinEulerValue i (σ.1,HTGeometry.quadrantLogNode u)*f (HTGeometry.quadrantLogNode u)+
        compactMellinEulerDerivative i (σ.1,HTGeometry.quadrantLogNode u)*
          fderiv ℝ f (HTGeometry.quadrantLogNode u) (HTGeometry.quadrantLogBasis i) := by
  have he : (compactLocalizedMellinSchwartz σ f : E→ℂ)=compactLocalizedMellinProfile σ.1 f :=
    funext (compactLocalizedMellinSchwartz_apply σ f)
  rw [he]
  exact compactLocalizedMellinProfile_euler σ.1 f u i

end GaloisForLFunctions.HTGeometry
