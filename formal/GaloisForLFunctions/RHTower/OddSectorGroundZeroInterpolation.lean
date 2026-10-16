import GaloisForLFunctions.RHTower.OddSectorGroundPolynomialStructure
import GaloisForLFunctions.RHTower.FiniteZeroSubquadraticTwoRayDecay
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# Nondegenerate spectral interpolation for the corrected odd Weil ground

Real quadratic multipliers transfer across the full arithmetic-corrected
Hermitian form, including its signed pole term. Paired zero quotients of the
canonical ground generator have positive energy and nonzero evaluation at
their own nodes. They give simple nonzero generator zeros and exact positive
evaluation representatives, without a ground-simplicity assumption.
-/

open Complex MeasureTheory Set Filter Topology Polynomial
open scoped InnerProduct ComplexConjugate
noncomputable section
namespace RHTower.OddSector
open GaloisForLFunctions.HTGeometry.FourierLaplaceDivision
open CCMRealRootedGround CCMGroundStructure CCMGroundQuadrature CCMFullRealRootedGround

private theorem transform_continuous (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) : Continuous (unitaryLaplace (timeRep a u)) :=
  (CCMXiStrip.differentiable_unitaryLaplace a.2.le
    (integrable_timeRep a u) (supportedIn_timeRep a u)).continuous

/-- Paired division at any nonzero zero preserves oddness and the actual form domain. -/
theorem exists_odd_paired_div (a : SuzukiPositiveAperture)
    {u : CCMArchimedeanFormDomain a} (hu : ccmArchimedeanFormReflection a u = -u)
    {z : ℂ} (hz0 : z ≠ 0) (hz : unitaryLaplace (timeRep a u) z = 0) :
    ∃ v : CCMArchimedeanFormDomain a, ccmArchimedeanFormReflection a v = -v ∧
      ∀ w : ℂ, unitaryLaplace (timeRep a u) w =
        (w^2-z^2)*unitaryLaplace (timeRep a v) w := by
  have hnz : -z ≠ z := fun h => hz0 (by linear_combination -h/2)
  have hzm : unitaryLaplace (timeRep a u) (-z) = 0 := by
    rw [odd_transform_neg a hu,hz,neg_zero]
  obtain ⟨v₁,hv₁⟩ := exists_div a u hz
  have hv₁m : unitaryLaplace (timeRep a v₁) (-z) = 0 := by rw [hv₁ _ hnz,hzm,zero_div]
  obtain ⟨v,hv⟩ := exists_div a v₁ hv₁m
  have hfac₁ (w : ℂ) : unitaryLaplace (timeRep a u) w =
      (w-z)*unitaryLaplace (timeRep a v₁) w := by
    by_cases hw : w=z
    · rw [hw,hz,sub_self,zero_mul]
    · rw [hv₁ w hw]
      field_simp [sub_ne_zero.mpr hw]
  have hfac₂ (w : ℂ) : unitaryLaplace (timeRep a v₁) w =
      (w+z)*unitaryLaplace (timeRep a v) w := by
    by_cases hw : w = -z
    · rw [hw,hv₁m,neg_add_cancel,zero_mul]
    · rw [hv w hw,sub_neg_eq_add]
      field_simp [show w+z ≠ 0 by simpa only [sub_neg_eq_add] using sub_ne_zero.mpr hw]
  have hfac (w : ℂ) : unitaryLaplace (timeRep a u) w =
      (w^2-z^2)*unitaryLaplace (timeRep a v) w := by rw [hfac₁,hfac₂]; ring
  let P : ℂ[X] := X^2-C (z^2)
  have hP : P ≠ 0 := by
    intro he
    have he' := congrArg (fun p : ℂ[X] => p.coeff 2) he
    simpa [P] using he'
  have hodd : (fun w : ℂ => unitaryLaplace (timeRep a v) (-w)) =
      fun w => -unitaryLaplace (timeRep a v) w := by
    apply Continuous.ext_on (dense_univ.sdiff_finite (Polynomial.finite_setOf_isRoot hP))
      ((transform_continuous a v).comp continuous_neg) (transform_continuous a v).neg
    intro w hw
    have hw' : w^2-z^2 ≠ 0 := by simpa [P,Polynomial.IsRoot.def] using hw.2
    apply mul_left_cancel₀ hw'
    have he := hfac (-w)
    rw [neg_sq,odd_transform_neg a hu,hfac w] at he
    linear_combination -he
  refine ⟨v,?_,hfac⟩
  apply eq_of_transform_eq a
  intro t
  rw [CCMEvenSector.unitaryLaplace_reflection]
  exact (congrFun hodd t).trans ((evalAt a t).map_neg v).symm

theorem arithmeticShiftedForm_sub_left (a : SuzukiPositiveAperture)
    (u v w : CCMArchimedeanFormDomain a) :
    arithmeticShiftedForm a (u-v) w =
      arithmeticShiftedForm a u w - arithmeticShiftedForm a v w := by
  simp only [arithmeticShiftedForm,arithmeticForm,map_sub,inner_sub_left]
  ring

private theorem shiftedForm_re_eq_of_products (a : SuzukiPositiveAperture)
    (u v x y : CCMArchimedeanFormDomain a)
    (he : ∀ w : ℂ,
      conj (unitaryLaplace (timeRep a u) (conj w))*unitaryLaplace (timeRep a v) w =
      conj (unitaryLaplace (timeRep a x) (conj w))*unitaryLaplace (timeRep a y) w) :
    (arithmeticShiftedForm a u v).re = (arithmeticShiftedForm a x y).re := by
  have hk (w : ℂ) :
      conj (unitaryLaplace (timeRep a (u+v)) (conj w))*
          unitaryLaplace (timeRep a (u+v)) w +
        conj (unitaryLaplace (timeRep a (x-y)) (conj w))*
          unitaryLaplace (timeRep a (x-y)) w =
      conj (unitaryLaplace (timeRep a (u-v)) (conj w))*
          unitaryLaplace (timeRep a (u-v)) w +
        conj (unitaryLaplace (timeRep a (x+y)) (conj w))*
          unitaryLaplace (timeRep a (x+y)) w := by
    have h₁ := he w
    have h₂ := congrArg conj (he (conj w))
    simp only [map_mul,Complex.conj_conj] at h₂
    simp only [← evalAt_apply,map_add,map_sub] at h₁ h₂ ⊢
    linear_combination 2*h₁ + 2*h₂
  have hr (b : ℂ) : (conj b*b).re = ‖b‖^2 := by
    simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im,
      Complex.sq_norm,Complex.normSq_apply]
    ring
  have hs (t : ℝ) :
      ‖unitaryLaplace (timeRep a (u+v)) t‖^2 +
        ‖unitaryLaplace (timeRep a (x-y)) t‖^2 =
      ‖unitaryLaplace (timeRep a (u-v)) t‖^2 +
        ‖unitaryLaplace (timeRep a (x+y)) t‖^2 := by
    simpa only [Complex.conj_ofReal,Complex.add_re,hr] using congrArg Complex.re (hk t)
  have hp : poleTerm a (u+v) + poleTerm a (x-y) =
      poleTerm a (u-v) + poleTerm a (x+y) := by
    have hpos := hk (polarPoint (1/2))
    have hneg := hk (polarPoint (-1/2))
    rw [conj_polarPoint] at hpos hneg
    rw [show -(-1/2 : ℝ) = 1/2 by ring] at hneg
    have hp := congrArg Complex.re hpos
    have hm := congrArg Complex.re hneg
    simp only [poleTerm,Complex.add_re] at hp hm ⊢
    linarith
  have hb := arithmeticShiftedForm_diagonal_balance a (u+v) (x-y) (u-v) (x+y) hs hp
  simp only [arithmeticShiftedForm_add_left,arithmeticShiftedForm_add_right,
    arithmeticShiftedForm_sub_left,arithmeticShiftedForm_sub_right,
    arithmeticShiftedForm_conj a u v,arithmeticShiftedForm_conj a x y,
    Complex.add_re,Complex.sub_re,Complex.conj_re] at hb
  linarith

/-- Equality of entire polarized products preserves the full corrected Hermitian form. -/
theorem arithmeticShiftedForm_eq_of_transform_products (a : SuzukiPositiveAperture)
    (u v x y : CCMArchimedeanFormDomain a)
    (he : ∀ w : ℂ,
      conj (unitaryLaplace (timeRep a u) (conj w))*unitaryLaplace (timeRep a v) w =
      conj (unitaryLaplace (timeRep a x) (conj w))*unitaryLaplace (timeRep a y) w) :
    arithmeticShiftedForm a u v = arithmeticShiftedForm a x y := by
  apply Complex.ext
  · exact shiftedForm_re_eq_of_products a u v x y he
  · have hi := shiftedForm_re_eq_of_products a u (I • v) x (I • y) (fun w => by
      simp only [unitaryLaplace_timeRep_smul]
      linear_combination I * he w)
    rw [arithmeticShiftedForm_smul_right,arithmeticShiftedForm_smul_right] at hi
    simpa only [Complex.mul_re,Complex.I_re,Complex.I_im,zero_mul,one_mul,
      zero_sub,neg_inj] using hi

/-- A real quadratic multiplier transfers across the signed, corrected form. -/
theorem arithmeticShiftedForm_quadratic_transfer (a : SuzukiPositiveAperture)
    (u v k h : CCMArchimedeanFormDomain a) {c : ℂ} (hc : conj c = c)
    (hu : ∀ w : ℂ, unitaryLaplace (timeRep a u) w =
      (w^2-c)*unitaryLaplace (timeRep a k) w)
    (hv : ∀ w : ℂ, unitaryLaplace (timeRep a v) w =
      (w^2-c)*unitaryLaplace (timeRep a h) w) :
    arithmeticShiftedForm a u h = arithmeticShiftedForm a k v := by
  apply arithmeticShiftedForm_eq_of_transform_products
  intro w
  rw [hu,hv]
  simp only [map_mul,map_sub,map_pow,Complex.conj_conj,hc]
  ring

private theorem ground_left_zero (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : G ∈ oddArithmeticGroundSpace a)
    (u : CCMArchimedeanFormDomain a) : arithmeticShiftedForm a G u = 0 := by
  rw [arithmeticShiftedForm,(mem_arithmeticGroundSpace_iff a G).mp hG.1 u,sub_self]

private theorem ground_right_zero (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : G ∈ oddArithmeticGroundSpace a)
    (u : CCMArchimedeanFormDomain a) : arithmeticShiftedForm a u G = 0 := by
  rw [arithmeticShiftedForm_conj,ground_left_zero a hG,map_zero]

private theorem shiftedForm_self_real (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    arithmeticShiftedForm a u u = ((arithmeticShiftedForm a u u).re : ℂ) := by
  have hi := congrArg Complex.im (arithmeticShiftedForm_conj a u u)
  simp only [Complex.conj_im] at hi
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    linarith

private theorem shiftedForm_smul_diagonal (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (c : ℂ) :
    (arithmeticShiftedForm a (c • u) (c • u)).re =
      ‖c‖^2 * (arithmeticShiftedForm a u u).re := by
  rw [arithmeticShiftedForm_smul_left,arithmeticShiftedForm_smul_right,
    ← mul_assoc,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

/-- Every paired zero quotient of the canonical generator has strictly positive corrected energy. -/
theorem oddGroundGenerator_quotient_pos (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    {v : CCMArchimedeanFormDomain a} (hv : ccmArchimedeanFormReflection a v = -v)
    (z : ℂ) (hfac : ∀ w : ℂ, unitaryLaplace (timeRep a G) w =
      (w^2-z^2)*unitaryLaplace (timeRep a v) w) :
    0 < (arithmeticShiftedForm a v v).re := by
  by_contra hn
  have hnull : (arithmeticShiftedForm a v v).re = 0 :=
    le_antisymm (le_of_not_gt hn) (arithmeticShiftedForm_odd_nonneg a ⟨v,hv⟩)
  obtain ⟨P,hP⟩ := hG.2.2 v ((mem_oddArithmeticGroundSpace_iff a v).mpr ⟨hv,hnull⟩)
  have hpoly : (X-C (z^2))*P = 1 := by
    apply polynomial_sq_mul_transform_injective a hG.2.1
    intro t
    have he := hfac t
    rw [hP] at he
    simp only [Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_X,
      Polynomial.eval_C,Polynomial.eval_one,one_mul]
    linear_combination -he
  have he := congrArg (fun p : ℂ[X] => p.eval (z^2)) hpoly
  simpa using he

private theorem zeroQuotient_annihilates (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : G ∈ oddArithmeticGroundSpace a)
    {z : ℂ} (hz0 : z ≠ 0) (hc : conj (z^2) = z^2)
    {v : CCMArchimedeanFormDomain a}
    (hfac : ∀ w : ℂ, unitaryLaplace (timeRep a G) w =
      (w^2-z^2)*unitaryLaplace (timeRep a v) w)
    {u : CCMArchimedeanFormDomain a} (hu : ccmArchimedeanFormReflection a u = -u)
    (hz : unitaryLaplace (timeRep a u) z = 0) : arithmeticShiftedForm a u v = 0 := by
  obtain ⟨k,_,hk⟩ := exists_odd_paired_div a hu hz0 hz
  rw [arithmeticShiftedForm_quadratic_transfer a u G k v hc hk hfac]
  exact ground_right_zero a hG k

/-- The canonical zero quotient never vanishes at its own nonzero axis node. -/
theorem oddGroundGenerator_quotient_eval_ne_zero (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    {z : ℂ} (hz0 : z ≠ 0) (hc : conj (z^2) = z^2)
    {v : CCMArchimedeanFormDomain a} (hv : ccmArchimedeanFormReflection a v = -v)
    (hfac : ∀ w : ℂ, unitaryLaplace (timeRep a G) w =
      (w^2-z^2)*unitaryLaplace (timeRep a v) w) :
    unitaryLaplace (timeRep a v) z ≠ 0 := by
  intro hz
  have he := zeroQuotient_annihilates a hG.1 hz0 hc hfac hv hz
  have hp := oddGroundGenerator_quotient_pos a hG hv z hfac
  rw [he,Complex.zero_re] at hp
  exact lt_irrefl 0 hp

/-- All nonzero zeros of the canonical generator are simple; multiplicity is not assumed. -/
theorem oddGroundGenerator_deriv_ne_zero (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    {z : ℂ} (hz0 : z ≠ 0) (hc : conj (z^2) = z^2)
    (hz : unitaryLaplace (timeRep a G) z = 0) :
    deriv (unitaryLaplace (timeRep a G)) z ≠ 0 := by
  obtain ⟨v,hv,hfac⟩ := exists_odd_paired_div a hG.1.2 hz0 hz
  have hvz := oddGroundGenerator_quotient_eval_ne_zero a hG hz0 hc hv hfac
  have hdv := (CCMXiStrip.differentiable_unitaryLaplace a.2.le
    (integrable_timeRep a v) (supportedIn_timeRep a v) z).hasDerivAt
  have hd := (((hasDerivAt_id z).pow 2).sub_const (z^2)).mul hdv
  rw [funext hfac]
  rw [hd.deriv]
  simpa only [pow_one,mul_one,sub_self,zero_mul,add_zero] using
    mul_ne_zero (mul_ne_zero (two_ne_zero : (2 : ℂ) ≠ 0) hz0) hvz

/-- An actual positive Riesz representative for evaluation at every nonzero generator zero. -/
theorem exists_oddGround_zero_representative (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    {z : ℂ} (hz0 : z ≠ 0) (hc : conj (z^2) = z^2)
    (hz : unitaryLaplace (timeRep a G) z = 0) :
    ∃ e : CCMArchimedeanFormDomain a, ∃ ρ : ℝ,
      ccmArchimedeanFormReflection a e = -e ∧
      unitaryLaplace (timeRep a e) z = 1 ∧ 0 < ρ ∧
      (∀ u : CCMArchimedeanFormDomain a, ccmArchimedeanFormReflection a u = -u →
        arithmeticShiftedForm a e u = (ρ : ℂ)*unitaryLaplace (timeRep a u) z) ∧
      ∀ w : ℂ, unitaryLaplace (timeRep a G) w = 0 → w^2 ≠ z^2 →
        unitaryLaplace (timeRep a e) w = 0 := by
  obtain ⟨v,hv,hfac⟩ := exists_odd_paired_div a hG.1.2 hz0 hz
  have hvz := oddGroundGenerator_quotient_eval_ne_zero a hG hz0 hc hv hfac
  let e := (unitaryLaplace (timeRep a v) z)⁻¹ • v
  have heo : ccmArchimedeanFormReflection a e = -e := by
    dsimp only [e]
    rw [map_smul,hv,smul_neg]
  have hez : unitaryLaplace (timeRep a e) z = 1 := by
    rw [unitaryLaplace_timeRep_smul,inv_mul_cancel₀ hvz]
  let ρ := (arithmeticShiftedForm a e e).re
  have hρ : 0 < ρ := by
    dsimp only [ρ,e]
    rw [shiftedForm_smul_diagonal]
    exact mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (inv_ne_zero hvz)))
      (oddGroundGenerator_quotient_pos a hG hv z hfac)
  refine ⟨e,ρ,heo,hez,hρ,?_,?_⟩
  · intro u hu
    let k := u - unitaryLaplace (timeRep a u) z • e
    have hko : ccmArchimedeanFormReflection a k = -k := by
      dsimp only [k]
      rw [map_sub,map_smul,hu,heo,smul_neg,neg_sub_neg,neg_sub]
    have hkz : unitaryLaplace (timeRep a k) z = 0 := by
      change (evalAt a z) (u - unitaryLaplace (timeRep a u) z • e) = 0
      rw [map_sub,map_smul,evalAt_apply,evalAt_apply,hez,smul_eq_mul,mul_one,sub_self]
    have hkv := zeroQuotient_annihilates a hG.1 hz0 hc hfac hko hkz
    have hke : arithmeticShiftedForm a k e = 0 := by
      rw [arithmeticShiftedForm_smul_right,hkv,mul_zero]
    have hek : arithmeticShiftedForm a e k = 0 := by
      rw [arithmeticShiftedForm_conj,hke,map_zero]
    change arithmeticShiftedForm a e (u - unitaryLaplace (timeRep a u) z • e) = 0 at hek
    rw [arithmeticShiftedForm_sub_right,arithmeticShiftedForm_smul_right,
      shiftedForm_self_real] at hek
    dsimp only [ρ]
    linear_combination hek
  · intro w hw hwz
    have hvw : unitaryLaplace (timeRep a v) w = 0 := by
      exact (mul_eq_zero.mp ((hfac w).symm.trans hw)).resolve_left (sub_ne_zero.mpr hwz)
    rw [unitaryLaplace_timeRep_smul,hvw,mul_zero]

/-- Every same-aperture transform has infinitely many distinct squared nonzero zeros.
This makes the spectral interpolation construction available at every finite size. -/
theorem exists_ccm_transform_squared_zero_sequence (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    ∃ z : ℕ → ℂ, Function.Injective (fun n => (z n)^2) ∧
      ∀ n, z n ≠ 0 ∧ unitaryLaplace (timeRep a u) (z n) = 0 := by
  classical
  have hf := CCMXiStrip.differentiable_unitaryLaplace a.2.le
    (integrable_timeRep a u) (supportedIn_timeRep a u)
  let A : ℝ := 2 * Real.pi * a.1
  let B : ℝ := ∫ x : ℝ, ‖timeRep a u x‖
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := integral_nonneg fun x => norm_nonneg _
  have hg (w : ℂ) : ‖unitaryLaplace (timeRep a u) w‖ ≤
      Real.exp ((A+B)*(1+‖w‖)^(1 : ℝ)) := by
    rw [Real.rpow_one]
    have him : 2 * Real.pi * |w.im| * a.1 ≤ A*‖w‖ := by
      calc
        _ = A*|w.im| := by dsimp only [A]; ring
        _ ≤ A*‖w‖ := mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm w) hA
    have hBe : B ≤ Real.exp B := by linarith [Real.add_one_le_exp B]
    calc
      _ ≤ Real.exp (2 * Real.pi * |w.im| * a.1)*B :=
        CCMPolarObstruction.norm_unitaryLaplace_le (integrable_timeRep a u)
          (supportedIn_timeRep a u) w
      _ ≤ Real.exp (A*‖w‖)*Real.exp B :=
        mul_le_mul (Real.exp_le_exp.mpr him) hBe hB (Real.exp_nonneg _)
      _ = Real.exp (A*‖w‖+B) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hB (norm_nonneg w)])
  have hdec : Tendsto (fun r : ℝ => ‖unitaryLaplace (timeRep a u) r‖)
      (cocompact ℝ) (𝓝 0) := by
    simpa only [unitaryLaplace_ofReal,norm_zero] using
      (Real.zero_at_infty_fourier (timeRep a u)).norm
  have hinf := zeroSet_infinite_of_subquadratic_twoRayDecay hf zero_le_one
    one_lt_two (add_nonneg hA hB) hg (hdec.mono_left atTop_le_cocompact)
    ((hdec.mono_left atBot_le_cocompact).comp Filter.tendsto_neg_atTop_atBot)
  let S : Set ℂ := {z | unitaryLaplace (timeRep a u) z = 0 ∧ z ≠ 0}
  have hS : S.Infinite := by
    simpa only [S,Set.mem_sdiff,Set.mem_setOf_eq,Set.mem_singleton_iff] using
      hinf.sdiff (Set.finite_singleton 0)
  have hsq : ((fun z : ℂ => z^2) '' S).Infinite := by
    intro hfin
    apply hS (hfin.of_finite_fibers (fun z : ℂ => z^2) ?_)
    intro c _
    have hP : (X^2-C c : ℂ[X]) ≠ 0 := by
      intro he
      have he' := congrArg (fun p : ℂ[X] => p.coeff 2) he
      simpa using he'
    apply (Polynomial.finite_setOf_isRoot hP).subset
    intro z hz
    simp only [Polynomial.IsRoot.def,Polynomial.eval_sub,Polynomial.eval_pow,
      Polynomial.eval_X,Polynomial.eval_C]
    exact sub_eq_zero.mpr hz.2
  let f := hsq.natEmbedding _
  choose z hz hsqz using fun n => (f n).2
  refine ⟨z,?_,fun n => ⟨(hz n).2,(hz n).1⟩⟩
  intro n m he
  apply f.injective
  apply Subtype.ext
  rw [← hsqz n,← hsqz m]
  exact he

end RHTower.OddSector
