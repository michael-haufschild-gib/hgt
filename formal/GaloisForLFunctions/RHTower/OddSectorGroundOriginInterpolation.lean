import GaloisForLFunctions.RHTower.OddSectorGroundZeroInterpolation

/-!
# The origin coordinate of the corrected odd ground spectrum

The canonical odd generator has a forced zero at the origin. If its first
derivative also vanishes, division by squared frequency produces one positive
derivative representative in the same aperture. Its own first derivative is
nonzero. Thus the forced origin zero can have order one or three, and the
exceptional triple zero contributes a single positive spectral coordinate.
-/

open Complex MeasureTheory Set Filter Topology Polynomial
open scoped InnerProduct ComplexConjugate
noncomputable section
namespace RHTower.OddSector
open GaloisForLFunctions.HTGeometry.FourierLaplaceDivision
open CCMRealRootedGround CCMGroundStructure CCMGroundQuadrature

theorem transform_hasDerivAt (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (z : ℂ) :
    HasDerivAt (unitaryLaplace (timeRep a u))
      (deriv (unitaryLaplace (timeRep a u)) z) z :=
  (CCMXiStrip.differentiable_unitaryLaplace a.2.le
    (integrable_timeRep a u) (supportedIn_timeRep a u) z).hasDerivAt

theorem transform_deriv_smul (a : SuzukiPositiveAperture)
    (c : ℂ) (u : CCMArchimedeanFormDomain a) :
    deriv (unitaryLaplace (timeRep a (c • u))) 0 =
      c * deriv (unitaryLaplace (timeRep a u)) 0 := by
  rw [funext (unitaryLaplace_timeRep_smul a u c)]
  exact ((transform_hasDerivAt a u 0).const_mul c).deriv

theorem transform_deriv_sub (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) :
    deriv (unitaryLaplace (timeRep a (u-v))) 0 =
      deriv (unitaryLaplace (timeRep a u)) 0 -
        deriv (unitaryLaplace (timeRep a v)) 0 := by
  have he : unitaryLaplace (timeRep a (u-v)) =
      fun w => unitaryLaplace (timeRep a u) w-unitaryLaplace (timeRep a v) w := by
    funext w
    exact (evalAt a w).map_sub u v
  rw [he]
  exact ((transform_hasDerivAt a u 0).sub (transform_hasDerivAt a v 0)).deriv

/-- Double division at the origin retains the odd complete form domain exactly
when its first transform derivative vanishes. -/
theorem exists_odd_origin_paired_div (a : SuzukiPositiveAperture)
    {u : CCMArchimedeanFormDomain a} (hu : ccmArchimedeanFormReflection a u = -u)
    (hd : deriv (unitaryLaplace (timeRep a u)) 0 = 0) :
    ∃ v : CCMArchimedeanFormDomain a, ccmArchimedeanFormReflection a v = -v ∧
      ∀ w : ℂ, unitaryLaplace (timeRep a u) w =
        w^2 * unitaryLaplace (timeRep a v) w := by
  have hz : unitaryLaplace (timeRep a u) 0 = 0 := by
    have he := odd_transform_neg a hu 0
    simp only [neg_zero] at he
    linear_combination he / 2
  obtain ⟨v₁,hv₁⟩ := exists_div a u hz
  have hfac₁ (w : ℂ) : unitaryLaplace (timeRep a u) w =
      w * unitaryLaplace (timeRep a v₁) w := by
    by_cases hw : w=0
    · simp [hw,hz]
    · rw [hv₁ w hw,sub_zero,mul_div_cancel₀ _ hw]
  have hv₁0 : unitaryLaplace (timeRep a v₁) 0 = 0 := by
    have he := ((hasDerivAt_id (0 : ℂ)).mul (transform_hasDerivAt a v₁ 0)).deriv
    change deriv (fun w : ℂ => w * unitaryLaplace (timeRep a v₁) w) 0 = _ at he
    rw [← funext hfac₁,hd] at he
    simpa using he.symm
  obtain ⟨v,hv⟩ := exists_div a v₁ hv₁0
  have hfac₂ (w : ℂ) : unitaryLaplace (timeRep a v₁) w =
      w * unitaryLaplace (timeRep a v) w := by
    by_cases hw : w=0
    · simp [hw,hv₁0]
    · rw [hv w hw,sub_zero,mul_div_cancel₀ _ hw]
  have hfac (w : ℂ) : unitaryLaplace (timeRep a u) w =
      w^2 * unitaryLaplace (timeRep a v) w := by
    rw [hfac₁,hfac₂]
    ring
  have hc := (CCMXiStrip.differentiable_unitaryLaplace a.2.le
    (integrable_timeRep a v) (supportedIn_timeRep a v)).continuous
  have hodd : (fun w : ℂ => unitaryLaplace (timeRep a v) (-w)) =
      fun w => -unitaryLaplace (timeRep a v) w := by
    apply Continuous.ext_on
      (dense_univ.sdiff_finite (Polynomial.finite_setOf_isRoot
        (pow_ne_zero 2 (Polynomial.X_ne_zero : (X : ℂ[X]) ≠ 0))))
      (hc.comp continuous_neg) hc.neg
    intro w hw
    have hn : w^2 ≠ 0 := by simpa [Polynomial.IsRoot.def] using hw.2
    change unitaryLaplace (timeRep a v) (-w) = -unitaryLaplace (timeRep a v) w
    apply mul_left_cancel₀ hn
    have he := hfac (-w)
    rw [neg_sq,odd_transform_neg a hu,hfac w] at he
    linear_combination -he
  refine ⟨v,?_,hfac⟩
  apply eq_of_transform_eq a
  intro t
  rw [CCMEvenSector.unitaryLaplace_reflection]
  exact (congrFun hodd t).trans ((evalAt a t).map_neg v).symm

private theorem ground_pair_right_zero (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : G ∈ oddArithmeticGroundSpace a)
    (u : CCMArchimedeanFormDomain a) : arithmeticShiftedForm a u G = 0 := by
  rw [arithmeticShiftedForm_conj,arithmeticShiftedForm,
    (mem_arithmeticGroundSpace_iff a G).mp hG.1 u,sub_self,map_zero]

private theorem origin_quotient_annihilates (a : SuzukiPositiveAperture)
    {G v : CCMArchimedeanFormDomain a} (hG : G ∈ oddArithmeticGroundSpace a)
    (hfac : ∀ w : ℂ, unitaryLaplace (timeRep a G) w =
      w^2 * unitaryLaplace (timeRep a v) w)
    {u : CCMArchimedeanFormDomain a} (hu : ccmArchimedeanFormReflection a u = -u)
    (hd : deriv (unitaryLaplace (timeRep a u)) 0 = 0) :
    arithmeticShiftedForm a u v = 0 := by
  obtain ⟨k,_,hk⟩ := exists_odd_origin_paired_div a hu hd
  have he := arithmeticShiftedForm_quadratic_transfer a u G k v
    (c := 0) (map_zero conj)
    (fun w => by simpa using hk w) (fun w => by simpa using hfac w)
  rw [he]
  exact ground_pair_right_zero a hG k

/-- The origin quotient has nonzero first derivative, excluding every origin
zero of odd order at least five without a simplicity assumption. -/
theorem oddGroundGenerator_origin_quotient_deriv_ne_zero (a : SuzukiPositiveAperture)
    {G v : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    (hv : ccmArchimedeanFormReflection a v = -v)
    (hfac : ∀ w : ℂ, unitaryLaplace (timeRep a G) w =
      w^2 * unitaryLaplace (timeRep a v) w) :
    deriv (unitaryLaplace (timeRep a v)) 0 ≠ 0 := by
  intro hd
  have hz := origin_quotient_annihilates a hG.1 hfac hv hd
  have hp := oddGroundGenerator_quotient_pos a hG hv 0
    (fun w => by simpa using hfac w)
  rw [hz,Complex.zero_re] at hp
  exact lt_irrefl 0 hp

private theorem shifted_self_real (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    arithmeticShiftedForm a u u = ((arithmeticShiftedForm a u u).re : ℂ) := by
  have h := arithmeticShiftedForm_conj a u u
  apply Complex.ext
  · rfl
  · have hi := congrArg Complex.im h
    simp only [Complex.conj_im] at hi
    simp only [Complex.ofReal_im]
    linarith

/-- The exceptional origin node is represented by a positive derivative
coordinate, orthogonal to every nonzero generator-node coordinate. -/
theorem exists_oddGround_origin_representative (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    (hd : deriv (unitaryLaplace (timeRep a G)) 0 = 0) :
    ∃ e : CCMArchimedeanFormDomain a, ∃ ρ : ℝ,
      ccmArchimedeanFormReflection a e = -e ∧
      deriv (unitaryLaplace (timeRep a e)) 0 = 1 ∧ 0 < ρ ∧
      (∀ u : CCMArchimedeanFormDomain a, ccmArchimedeanFormReflection a u = -u →
        arithmeticShiftedForm a e u =
          (ρ : ℂ)*deriv (unitaryLaplace (timeRep a u)) 0) ∧
      ∀ z : ℂ, z ≠ 0 → unitaryLaplace (timeRep a G) z = 0 →
        unitaryLaplace (timeRep a e) z = 0 := by
  obtain ⟨v,hv,hfac⟩ := exists_odd_origin_paired_div a hG.1.2 hd
  have hvd := oddGroundGenerator_origin_quotient_deriv_ne_zero a hG hv hfac
  let e := (deriv (unitaryLaplace (timeRep a v)) 0)⁻¹ • v
  have heo : ccmArchimedeanFormReflection a e = -e := by
    dsimp only [e]
    rw [map_smul,hv,smul_neg]
  have hed : deriv (unitaryLaplace (timeRep a e)) 0 = 1 := by
    rw [transform_deriv_smul,inv_mul_cancel₀ hvd]
  let ρ := (arithmeticShiftedForm a e e).re
  have hρ : 0 < ρ := by
    dsimp only [ρ,e]
    have hscale (c : ℂ) : (arithmeticShiftedForm a (c • v) (c • v)).re =
        ‖c‖^2 * (arithmeticShiftedForm a v v).re := by
      rw [arithmeticShiftedForm_smul_left,arithmeticShiftedForm_smul_right,
        ← mul_assoc,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [hscale]
    exact mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (inv_ne_zero hvd)))
      (oddGroundGenerator_quotient_pos a hG hv 0 (fun w => by simpa using hfac w))
  refine ⟨e,ρ,heo,hed,hρ,?_,?_⟩
  · intro u hu
    let k := u - deriv (unitaryLaplace (timeRep a u)) 0 • e
    have hko : ccmArchimedeanFormReflection a k = -k := by
      dsimp only [k]
      rw [map_sub,map_smul,hu,heo,smul_neg,neg_sub_neg,neg_sub]
    have hkd : deriv (unitaryLaplace (timeRep a k)) 0 = 0 := by
      rw [transform_deriv_sub,transform_deriv_smul,hed,mul_one,sub_self]
    have hkv := origin_quotient_annihilates a hG.1 hfac hko hkd
    have hke : arithmeticShiftedForm a k e = 0 := by
      rw [arithmeticShiftedForm_smul_right,hkv,mul_zero]
    have hek : arithmeticShiftedForm a e k = 0 := by
      rw [arithmeticShiftedForm_conj,hke,map_zero]
    change arithmeticShiftedForm a e
      (u - deriv (unitaryLaplace (timeRep a u)) 0 • e) = 0 at hek
    rw [arithmeticShiftedForm_sub_right,arithmeticShiftedForm_smul_right,
      shifted_self_real] at hek
    dsimp only [ρ]
    linear_combination hek
  · intro z hz0 hz
    have hvz : unitaryLaplace (timeRep a v) z = 0 :=
      (mul_eq_zero.mp ((hfac z).symm.trans hz)).resolve_left (pow_ne_zero 2 hz0)
    rw [unitaryLaplace_timeRep_smul,hvz,mul_zero]

/-- Unconditional origin classification for a canonical corrected odd ground:
either its forced zero is simple, or exactly one positive derivative coordinate
is supplied by its squared-frequency quotient. -/
theorem exists_canonical_oddGround_origin_coordinate (a : SuzukiPositiveAperture) :
    ∃ G : CCMArchimedeanFormDomain a, IsOddArithmeticGroundGenerator a G ∧
      (deriv (unitaryLaplace (timeRep a G)) 0 ≠ 0 ∨
        ∃ v : CCMArchimedeanFormDomain a,
          ccmArchimedeanFormReflection a v = -v ∧
          (∀ w : ℂ, unitaryLaplace (timeRep a G) w =
            w^2 * unitaryLaplace (timeRep a v) w) ∧
          deriv (unitaryLaplace (timeRep a v)) 0 ≠ 0) := by
  obtain ⟨G,hG,_,_⟩ := exists_canonical_oddArithmeticGround_generator a
  refine ⟨G,hG,?_⟩
  by_cases hd : deriv (unitaryLaplace (timeRep a G)) 0 = 0
  · obtain ⟨v,hv,hfac⟩ := exists_odd_origin_paired_div a hG.1.2 hd
    exact Or.inr ⟨v,hv,hfac,oddGroundGenerator_origin_quotient_deriv_ne_zero a hG hv hfac⟩
  · exact Or.inl hd

end RHTower.OddSector
