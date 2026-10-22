import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNonstationaryMoment

/-! Linear transport of the original finite part to one common rational weight. -/
namespace RHTower.D4BMJointSource
open Complex Set MeasureTheory D4BMLaplaceRadial GaloisForLFunctions.HTGeometry
open scoped Polynomial
noncomputable section
set_option autoImplicit false

theorem nonstationaryMoment_congr (P Q : ℂ[X]) (j k : ℕ) (w : ℂ)
    (h : ∀ x ∈ Icc (0:ℝ) 1, nonstationaryWeight P j x=nonstationaryWeight Q k x) :
    nonstationaryMoment P j w=nonstationaryMoment Q k w := by
  have hc (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) : nonstationaryCore P j w x=nonstationaryCore Q k w x := by
    exact congrArg (power (-4*w) (2-x)*·) (h x hx)
  have h0 := hc 0 (by constructor <;> norm_num)
  dsimp only [nonstationaryMoment,firstEndpointMellin,firstEndpointMellinRemainder]
  rw [h0]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  dsimp only
  rw [hc x ⟨hx.1.le,hx.2⟩]

theorem nonstationaryMoment_remainder_integrable (P : ℂ[X]) (j : ℕ) (w : ℂ)
    (hw : -2 < w.re) :
    IntegrableOn (fun x : ℝ => (x:ℂ)^w*(nonstationaryCore P j w x-nonstationaryCore P j w 0))
      (Ioc (0:ℝ) 1) := by
  obtain ⟨C,_,hC⟩ := nonstationaryCore_first_bound P j w
  have hm : Measurable (nonstationaryCore P j w) := by
    unfold nonstationaryCore nonstationaryWeight power
    fun_prop
  exact firstEndpointMellinRemainder_integrable (F := fun _ => nonstationaryCore P j w)
    (by norm_num) hw hm hC

theorem nonstationaryMoment_add (P Q : ℂ[X]) (j : ℕ) (w : ℂ) (hw : -2 < w.re) :
    nonstationaryMoment (P+Q) j w=nonstationaryMoment P j w+nonstationaryMoment Q j w := by
  have he (x : ℝ) : nonstationaryCore (P+Q) j w x=nonstationaryCore P j w x+nonstationaryCore Q j w x := by
    simp only [nonstationaryCore,nonstationaryWeight,Polynomial.eval_add,add_div,mul_add]
  simp only [nonstationaryMoment,firstEndpointMellin,firstEndpointMellinRemainder,he]
  have hi : (fun x : ℝ => (x:ℂ)^w*((nonstationaryCore P j w x+nonstationaryCore Q j w x)-
      (nonstationaryCore P j w 0+nonstationaryCore Q j w 0))) =
      (fun x : ℝ => (x:ℂ)^w*(nonstationaryCore P j w x-nonstationaryCore P j w 0)+
        (x:ℂ)^w*(nonstationaryCore Q j w x-nonstationaryCore Q j w 0)) := by
    funext x; ring
  rw [hi,integral_add (nonstationaryMoment_remainder_integrable P j w hw)
    (nonstationaryMoment_remainder_integrable Q j w hw)]
  ring

theorem nonstationaryMoment_C_mul (c : ℂ) (P : ℂ[X]) (j : ℕ) (w : ℂ) :
    nonstationaryMoment (Polynomial.C c*P) j w=c*nonstationaryMoment P j w := by
  have he (x : ℝ) : nonstationaryCore (Polynomial.C c*P) j w x=c*nonstationaryCore P j w x := by
    simp only [nonstationaryCore,nonstationaryWeight,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  simp only [nonstationaryMoment,firstEndpointMellin,firstEndpointMellinRemainder,he]
  have hi : (fun x : ℝ => (x:ℂ)^w*(c*nonstationaryCore P j w x-c*nonstationaryCore P j w 0)) =
      (fun x : ℝ => c*((x:ℂ)^w*(nonstationaryCore P j w x-nonstationaryCore P j w 0))) := by
    funext x; ring
  rw [hi,integral_const_mul]
  ring

theorem nonstationaryMoment_sub (P Q : ℂ[X]) (j : ℕ) (w : ℂ) (hw : -2 < w.re) :
    nonstationaryMoment (P-Q) j w=nonstationaryMoment P j w-nonstationaryMoment Q j w := by
  rw [show P-Q=P+Polynomial.C (-1)*Q by simp [sub_eq_add_neg],nonstationaryMoment_add P _ j w hw,
    nonstationaryMoment_C_mul]
  ring

theorem nonstationaryMoment_lift (P : ℂ[X]) (j k : ℕ) (w : ℂ) :
    nonstationaryMoment ((2+3*Polynomial.X)^k*P) (j+k) w=nonstationaryMoment P j w := by
  apply nonstationaryMoment_congr
  intro x hx
  have ha : (2-(x:ℂ)) ≠ 0 := by exact_mod_cast (show (2-x:ℝ) ≠ 0 by linarith [hx.2])
  have hb : (2+3*(x:ℂ)) ≠ 0 := by exact_mod_cast (show (2+3*x:ℝ) ≠ 0 by linarith [hx.1])
  have hb' : (2+(x:ℂ)*3) ≠ 0 := by simpa only [mul_comm] using hb
  simp only [nonstationaryWeight,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_add,
    Polynomial.eval_ofNat,Polynomial.eval_X,pow_add]
  field_simp [ha,hb,hb']

end
end RHTower.D4BMJointSource
