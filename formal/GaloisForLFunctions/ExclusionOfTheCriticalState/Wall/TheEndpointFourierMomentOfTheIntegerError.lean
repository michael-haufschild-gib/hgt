import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.ParsevalForTheIntegerQuadrature

/-!
# The boundary line of the integer quadrature

At the half tilt the physical positive-ray square mass would dominate the
Fourier integrals on every approaching subcritical line. Fatou then bounds
the product of the boundary zeta values with the half-tilted state.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped FourierTransform
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open HTGeometry ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory

/-- On opposite rays the zero and half tilts dominate all intermediate
tilts at once, with an integrable majorant when the endpoint is finite. -/
theorem squared_intermediate_tilt_le {D : ℝ → ℝ} {β : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 1/2) (t : ℝ) :
    (Real.exp (β*t)*D t)^2 ≤ (D t)^2 + (Ioi (0:ℝ)).indicator (fun v => (Real.exp (v/2)*D v)^2) t := by
  rcases le_or_gt t 0 with ht | ht
  · rw [indicator_of_notMem (show t ∉ Ioi (0:ℝ) from not_lt.mpr ht),add_zero,mul_pow]
    have h1 : Real.exp (β*t) ≤ 1 := Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos hβ ht)
    exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (Real.exp_pos _).le h1)
  · rw [indicator_of_mem (show t ∈ Ioi (0:ℝ) from ht),mul_pow,mul_pow]
    have h1 : Real.exp (β*t) ≤ Real.exp (t/2) := Real.exp_le_exp.2 (by
      linarith only [mul_le_mul_of_nonneg_right hβ' ht.le])
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.exp_pos _).le h1 2) (sq_nonneg _)).trans
      (le_add_of_nonneg_left (sq_nonneg _))

/-- A finite half-tilted square integral on the positive ray would put the
boundary zeta multiplier times the reflected state in L². -/
theorem criticalState_endpoint_integer_fourier_moment {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal)) {F Φ : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    (hend : IntegrableOn (fun t => (tiltedIntegerError Φ (1/2) t)^2) (Ioi 0)) :
    Integrable (fun ξ : ℝ => ‖riemannZeta (((2*Real.pi*ξ:ℝ):ℂ)*I)*
      negativeHalfLineLaplace (cx F) (1/2-((2*Real.pi*ξ:ℝ):ℂ)*I)‖^2) := by
  let A := ∫ u, Real.exp (-u/2)*Φ u
  let D := fun t : ℝ => integerReferenceWave Φ t-Real.exp (t/2)*A
  let g := fun t : ℝ => D t^2+(Ioi (0:ℝ)).indicator (fun v => (Real.exp (v/2)*D v)^2) t
  have htilt {a : ℝ} (ha : 0 ≤ a) (ha' : a < 1/2) :=
    criticalState_subcritical_integer_error hW ht hF hc he hC hb ha ha'
  have hsq {a : ℝ} (ha : 0 ≤ a) (ha' : a < 1/2) :
      Integrable (fun t => (tiltedIntegerError Φ a t)^2) := by
    have h := htilt ha ha'
    simpa only [Real.norm_eq_abs,sq_abs] using (memLp_two_iff_integrable_sq_norm h.1).1 h
  have hD : Integrable fun t => D t^2 := by
    simpa only [tiltedIntegerError,D,A,zero_mul,Real.exp_zero,one_mul] using hsq (a := 0) le_rfl (by norm_num)
  have hhalf : IntegrableOn (fun t => (Real.exp (t/2)*D t)^2) (Ioi 0) := by
    simpa only [tiltedIntegerError,D,A,one_div_mul_eq_div] using hend
  have hg : Integrable g := hD.add ((integrable_indicator_iff measurableSet_Ioi).2 hhalf)
  let σ := fun n : ℕ => (1/((n:ℝ)+1))/2
  let β := fun n : ℕ => 1/2-σ n
  have hσ (n : ℕ) : 0 < σ n ∧ σ n ≤ 1/2 := by
    dsimp only [σ]
    exact ⟨by positivity,div_le_div_of_nonneg_right
      ((one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) (by linarith only [Nat.cast_nonneg (α := ℝ) n])).trans_eq (by norm_num))
      (by norm_num)⟩
  have hβ (n : ℕ) : 0 ≤ β n ∧ β n < 1/2 := ⟨sub_nonneg.2 (hσ n).2,sub_lt_self _ (hσ n).1⟩
  let s := fun (n : ℕ) (ξ : ℝ) => (σ n:ℂ)+((2*Real.pi*ξ:ℝ):ℂ)*I
  let Z := fun z : ℂ => riemannZeta z*negativeHalfLineLaplace (cx F) (1/2-z)
  let f := fun (n : ℕ) (ξ : ℝ) => ‖Z (s n ξ)‖^2
  let v := fun (n : ℕ) (t : ℝ) => (tiltedIntegerError Φ (β n) t:ℂ)
  have hdata (n : ℕ) : Integrable (v n) ∧ (∀ ξ, 𝓕 (v n) ξ=Z (s n ξ)) ∧
      (∫ t, (tiltedIntegerError Φ (β n) t)^2) = ∫ ξ, f n ξ := by
    have hs (n : ℕ) : 1/2-β n=σ n := sub_sub_cancel _ _
    simpa only [v,s,Z,f,hs] using criticalState_integer_quadrature_parseval hW ht hF hc he hC hb (hβ n).1 (hβ n).2
  have hcont (n : ℕ) : Continuous (f n) := by
    have h := (RHTower.continuous_fourier_of_integrable (hdata n).1).norm.pow 2
    have he : f n = fun ξ => ‖𝓕 (v n) ξ‖^2 := by funext ξ; simp only [f,(hdata n).2.1]
    rw [he]; exact h.congr fun ξ => rfl
  have hint (n : ℕ) : Integrable (f n) := by
    have hv : MemLp (v n) 2 := (memLp_two_iff_integrable_sq_norm (hdata n).1.1).2 (by
      simpa only [v,Complex.norm_real,Real.norm_eq_abs,sq_abs] using hsq (hβ n).1 (hβ n).2)
    have h := RHTower.integrable_norm_sq_fourier (hdata n).1 hv
    simpa only [f,← (hdata n).2.1] using h
  have hbound (n : ℕ) : (∫ ξ, f n ξ) ≤ ∫ t, g t := by
    rw [← (hdata n).2.2]
    exact integral_mono (hsq (hβ n).1 (hβ n).2) hg (squared_intermediate_tilt_le (D := D) (hβ n).1 (hβ n).2.le)
  have hσlim : Tendsto σ atTop (𝓝 0) := by
    simpa only [σ,zero_div] using tendsto_one_div_add_atTop_nhds_zero_nat.div_const (2:ℝ)
  let w := fun ξ : ℝ => ((2*Real.pi*ξ:ℝ):ℂ)*I
  have hlim (ξ : ℝ) : Tendsto (fun n => f n ξ) atTop (𝓝 (‖Z (w ξ)‖^2)) := by
    have hre : (w ξ).re=0 := by simp [w]
    have hs : Tendsto (fun n => s n ξ) atTop (𝓝 (w ξ)) := by
      simpa only [s,w,ofReal_zero,zero_add,Function.comp_apply] using ((Complex.continuous_ofReal.tendsto 0).comp hσlim).add_const (w ξ)
    have hne : w ξ ≠ 1 := by intro h; rw [h,one_re] at hre; norm_num at hre
    have hd := criticalHalfLineEnergyDomain_of_groundState hF
    have hL := differentiableAt_laplace_of_sq hd hd.exponential (w := 1/2-w ξ) (by simp [Complex.sub_re,hre]; norm_num)
    exact (((differentiableAt_riemannZeta hne).continuousAt.tendsto.comp hs).mul
      (hL.continuousAt.tendsto.comp (tendsto_const_nhds.sub hs))).norm.pow 2
  exact (integrable_and_integral_le_of_tendsto (fun n => (hcont n).measurable)
    (fun _ _ => sq_nonneg _) hint hbound hlim).1

#print axioms criticalState_endpoint_integer_fourier_moment
end GaloisForLFunctions.ExclusionOfTheCriticalState
