import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMScalarCutoffPeriodStrip
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLiteralCyclicPeierlsAffineCuspIncidence
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGlobalSmoothForcing
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPWWeakSourceOpticalWard

/-!
# PW-B weak-source mass positivity

The literal cusp-subtracted source is nonzero at every Xi zero copy on both physical branches.
Its weak finite-energy response has strictly positive mass. The proof uses the exact low-strip
forcing, horizontal scalar mean, two distinct Weyl powers, and the corpus's zero-free-side
coefficient law. This removes the mass-vanishing escape from PW-B's crossed optical Ward law;
it does not identify that law with the ordered literal CTP current or prove RH.
-/

open Complex Real Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open RHTower
open RHTower.D4BMGlobalAngularResponse RHTower.D4BMJointSource
open RHTower.D4BMModularCore RHTower.D4BMCuspProjection
open RHTower.D4BMLiteralCyclicPeierlsAffineCuspIncidence


private theorem two_cpow_nonzero_on_low (s A B : ℂ) (hs : 2*s ≠ 1)
    (hAB : A ≠ 0 ∨ B ≠ 0) :
    ∃ y : ℝ, 1 < y ∧ y < 2 ∧ A*(y:ℂ)^s+B*(y:ℂ)^(1-s) ≠ 0 := by
  by_contra h
  push Not at h
  let y : ℝ := 3/2
  have hy : 0 < y := by norm_num [y]
  have hy1 : 1 < y := by norm_num [y]
  have hy2 : y < 2 := by norm_num [y]
  have hzero : A*(y:ℂ)^s+B*(y:ℂ)^(1-s) = 0 := h y hy1 hy2
  have hlocal : (fun t : ℝ => A*(t:ℂ)^s+B*(t:ℂ)^(1-s)) =ᶠ[𝓝 y]
      (fun _ => 0) := by
    filter_upwards [((isOpen_Ioo).mem_nhds ⟨hy1,hy2⟩)] with t ht
    exact h t ht.1 ht.2
  have hderiv := ((GaloisForLFunctions.RHTower.hasDerivAt_cpow_ofReal (w := s) hy).const_mul A).add
    ((GaloisForLFunctions.RHTower.hasDerivAt_cpow_ofReal (w := 1-s) hy).const_mul B)
  have hd0 : A*(s*(y:ℂ)^(s-1))+B*((1-s)*(y:ℂ)^((1-s)-1))=0 := by
    have he := hderiv.congr_of_eventuallyEq hlocal.symm
    have hconst : HasDerivAt (fun _ : ℝ => (0:ℂ)) 0 y := hasDerivAt_const y 0
    exact he.unique hconst
  have hyc : (y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hpow1 : (y:ℂ)^(s-1)*(y:ℂ)=(y:ℂ)^s := by
    calc
      _ = (y:ℂ)^(s-1)*(y:ℂ)^1 := by rw [Complex.cpow_one]
      _ = (y:ℂ)^((s-1)+1) := (Complex.cpow_add _ _ hyc).symm
      _ = _ := by congr 1; ring
  have hpow2 : (y:ℂ)^((1-s)-1)*(y:ℂ)=(y:ℂ)^(1-s) := by
    calc
      _ = (y:ℂ)^((1-s)-1)*(y:ℂ)^1 := by rw [Complex.cpow_one]
      _ = (y:ℂ)^(((1-s)-1)+1) := (Complex.cpow_add _ _ hyc).symm
      _ = _ := by congr 1; ring
  have hd1 : A*s*(y:ℂ)^s+B*(1-s)*(y:ℂ)^(1-s)=0 := by
    calc
      _ = A*s*((y:ℂ)^(s-1)*(y:ℂ)) + B*(1-s)*((y:ℂ)^((1-s)-1)*(y:ℂ)) := by
        rw [hpow1,hpow2]
      _ = (A*(s*(y:ℂ)^(s-1))+B*((1-s)*(y:ℂ)^((1-s)-1)))*(y:ℂ) := by ring
      _ = 0 := by rw [hd0]; ring
  have hdiff : (2*s-1)*(A*(y:ℂ)^s)=0 := by
    linear_combination hd1 - (1-s)*hzero
  have hAu : A*(y:ℂ)^s=0 := (mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hs)
  have hBu : B*(y:ℂ)^(1-s)=0 := by simpa [hAu] using hzero
  have hA0 : A = 0 := (mul_eq_zero.mp hAu).resolve_right
    (Complex.cpow_ne_zero_iff.mpr (.inl hyc))
  have hB0 : B = 0 := (mul_eq_zero.mp hBu).resolve_right
    (Complex.cpow_ne_zero_iff.mpr (.inl hyc))
  exact hAB.elim (fun hA => hA hA0) (fun hB => hB hB0)

theorem pwb_forcingVector_ne_zero (q : RHTower.XiZeroCopy) (b : Bool) :
    forcingVector q b ≠ 0 := by
  have hAB : reflectedCompletedLambda (2 * (q.1 : ℂ)) ≠ 0 ∨
      reflectedCompletedLambda (2 * (q.1 : ℂ) - 1) ≠ 0 := by
    by_cases hleft : (q.1 : ℂ).re < 1/2
    · right
      intro h
      exact affine_lower_lambda_zero_not_left q ⟨h,hleft⟩
    · left
      unfold reflectedCompletedLambda
      have htwo : (2 * (q.1 : ℂ)).re = 2 * (q.1 : ℂ).re := by
        norm_num [Complex.mul_re]
      apply mul_ne_zero
      · apply Complex.Gammaℝ_ne_zero_of_re_pos
        have hge : 1/2 ≤ (q.1 : ℂ).re := le_of_not_gt hleft
        rw [htwo]
        linarith
      · apply riemannZeta_ne_zero_of_one_le_re
        have hge : 1/2 ≤ (q.1 : ℂ).re := le_of_not_gt hleft
        rw [htwo]
        linarith
  have hs : 2 * (q.1 : ℂ) ≠ 1 := (principal_weyl_exponents_pairwise_ne q).1
  obtain ⟨y,hy1,hy2,hpr⟩ := two_cpow_nonzero_on_low (q.1 : ℂ)
    (reflectedCompletedLambda (2*(q.1 : ℂ)))
    (reflectedCompletedLambda (2*(q.1 : ℂ)-1)) hs hAB
  have hy : 0 < y := by linarith
  intro hF
  have hae : (fun z : UpperHalfPlane => forcing q b (coordinates z)) =ᵐ[angularMeasure]
      (0 : UpperHalfPlane → ℂ) := by
    have h := forcingVector_coe q b
    rw [hF] at h
    exact h.symm.trans (Lp.coeFn_zero ℂ 2 angularMeasure)
  have haeFdo : (fun z : UpperHalfPlane => forcing q b (coordinates z)) =ᵐ[volume.restrict fdo]
      (0 : UpperHalfPlane → ℂ) := by
    change (fun z : UpperHalfPlane => forcing q b (coordinates z)) =ᵐ[volume.restrict fd]
      (0 : UpperHalfPlane → ℂ) at hae
    exact ae_restrict_of_ae_restrict_of_subset fdo_subset_fd hae
  have hcoords : Continuous coordinates := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact UpperHalfPlane.continuous_re
    · exact UpperHalfPlane.continuous_im
  have hc : Continuous (fun z : UpperHalfPlane => forcing q b (coordinates z)) :=
    (forcing_continuousOn q b).comp_continuous hcoords (fun z => z.im_pos)
  have hpoint := Measure.eqOn_open_of_ae_eq haeFdo isOpen_fdo hc.continuousOn continuousOn_const
  have hparam : parameter q b ≠ 0 := by
    change D4BMQuadraticMixedSource.branchParameter (q.1 : ℂ) b ≠ 0
    exact neg_ne_zero.mp (D4BMQuadraticMixedSource.xi_cusp_denominators q b).2.1
  have hscalar (x : ℝ) (hx : x ∈ Ioo (-1/2 : ℝ) (1/2)) :
      scalar (center q) ![x,y] = 0 := by
    let z : UpperHalfPlane := ⟨⟨x,y⟩, by simpa using hy⟩
    have hzfdo : z ∈ fdo := by
      change 1 < Complex.normSq (⟨x,y⟩:ℂ) ∧ |x| < 1/2
      constructor
      · change 1 < x*x+y*y
        nlinarith [sq_nonneg x]
      · rcases hx with ⟨hxl,hxr⟩
        exact abs_lt.mpr ⟨by nlinarith,hxr⟩
    have hz := hpoint hzfdo
    have he : forcing q b ![x,y] = 0 := by simpa [z,coordinates] using hz
    rw [forcing_low q b _ hy2] at he
    have hp2 : parameter q b / 2 ≠ 0 := div_ne_zero hparam (by norm_num)
    have hsq : scalar (center q) ![x,y] ^ (2 : ℕ) = 0 :=
      (mul_eq_zero.mp he).resolve_left hp2
    exact sq_eq_zero_iff.mp hsq
  have hmean0 : mean (fun x => scalar (center q) ![x,y]) = 0 := by
    change (∫ x in Ioc (-1/2:ℝ) (1/2), scalar (center q) ![x,y]) = 0
    rw [integral_Ioc_eq_integral_Ioo]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hscalar x hx
  have hprincipal : principal (center q) ![0,y] = 0 := by
    rw [← mean_scalar (center q) hy]
    exact hmean0
  apply hpr
  rw [← principal_center_weyl_coefficients q ⟨y,hy⟩]
  exact hprincipal

theorem pwb_weakSourceMass_pos (q : RHTower.XiZeroCopy) (b : Bool) :
    0 < weakSourceMass q b := by
  have hforcing := pwb_forcingVector_ne_zero q b
  have hresp : embedding (weakResponse q b) ≠ 0 := by
    intro hz
    have hr : weakResponse q b = 0 := embedding_injective (by simpa using hz)
    have horth : ∀ v, inner ℂ (embedding v) (forcingVector q b) = 0 := by
      intro v
      have he := weakResponse_spec q b v
      have hn : -inner ℂ (embedding v) (forcingVector q b) = 0 := by
        simpa [hr] using he.symm
      exact neg_eq_zero.mp hn
    exact hforcing (embedding_dense.eq_zero_of_inner_right ℂ (by
      rintro w ⟨v,rfl⟩
      exact horth v))
  exact pow_pos (norm_pos_iff.mpr hresp) 2

