import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ForecastWindows.Conditioning.KernelMaximal
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.GaussianDilation

/-! # A dimension bound for conditional resolution at a prescribed forecast -/

open Set MeasureTheory ProbabilityTheory Real
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows.Conditioning
noncomputable section

private abbrev law (I : Type*) [Fintype I] := Measure.pi fun _ : I => gaussianReal 0 1

private theorem jacobian_le {a : ℝ} {n : ℕ} (ha : 1≤a) (hd : (n:ℝ)*(a-1)≤1) :
    a^n≤exp 1 := by
  have h := add_one_le_exp (a-1)
  rw [sub_add_cancel] at h
  exact (pow_le_pow_left₀ (zero_le_one.trans ha) h n).trans
    (by rw [←Real.exp_nat_mul]; exact exp_le_exp.mpr hd)

variable {I J : Type*} [Fintype I] [Fintype J]

/-- At a common dilation of the forecast, only the Jacobian of each
coefficient block and the linear change in window width enter. -/
private theorem slice_dilation (F : (I→ℝ)×(J→ℝ)→ℝ) (hf : Measurable F)
    (hscale : ∀ a> (0:ℝ), ∀ x y, a*F (a • x,a • y)=F (x,y))
    {T L Q a : ℝ} (hQ : 0<Q) (ha : 1≤a) (hx : a^Fintype.card I≤exp 1)
    (hw : a^Fintype.card J*(L*a)≤Q) :
    (law I).real {x | (x,T)∈excessKernel (law J) F Q} ≤
      exp 1*(law I).real {x | (x,a*T)∈excessKernel (law J) F L} := by
  let B := {x | (x,T)∈excessKernel (law J) F Q}
  have hm : MeasurableSet B := (measurableSet_excessKernel (law J) hf hQ).preimage
    (measurable_id.prodMk measurable_const)
  have ha₀ := zero_lt_one.trans_le ha
  have hsub : (fun x : I→ℝ => a • x) ⁻¹' B ⊆ {x | (x,a*T)∈excessKernel (law J) F L} := by
    rintro x ⟨h,hh,hbad⟩
    refine ⟨a*h,mul_pos ha₀ hh,?_⟩
    let E := {y | |F (a • x,y)-T|<h}
    have hE : MeasurableSet E := measurableSet_lt
      ((hf.comp (measurable_const.prodMk measurable_id)).sub_const T).abs measurable_const
    have he : (fun y : J→ℝ => a • y) ⁻¹' E={y | |F (x,y)-a*T|<a*h} := by
      ext y
      change |F (a • x,a • y)-T|<h ↔ |F (x,y)-a*T|<a*h
      rw [←hscale a ha₀ x y,←mul_sub,abs_mul,abs_of_pos ha₀,mul_lt_mul_iff_right₀ ha₀]
    have hp := gaussian_dilation_comparison ha E hE
    rw [he] at hp
    apply (mul_lt_mul_iff_right₀ (pow_pos ha₀ (Fintype.card J))).mp
    calc
      a^Fintype.card J*(L*(a*h)) = (a^Fintype.card J*(L*a))*h := by ring
      _ ≤ Q*h := mul_le_mul_of_nonneg_right hw hh.le
      _ < _ := hbad.trans_le hp
  exact (gaussian_dilation_comparison ha B hm).trans
    (mul_le_mul hx (measureReal_mono (μ:=law I) hsub (measure_ne_top _ _))
      measureReal_nonneg (exp_pos 1).le)

/-- At any prescribed positive date T, the probability that the conditional
mass exceeds M h/T at even one radius h is at most 16 e²(d+1)/M,
where d is the total dimension of the two Gaussian blocks. -/
theorem gaussian_conditional_maximal (F : (I→ℝ)×(J→ℝ)→ℝ) (hf : Measurable F)
    (hscale : ∀ a> (0:ℝ), ∀ x y, a*F (a • x,a • y)=F (x,y))
    {T M : ℝ} (hT : 0<T) (hM : 0<M) :
    (law I).real {x | (x,T)∈excessKernel (law J) F (M/T)} ≤
      16*(exp 1)^2*((Fintype.card I:ℝ)+Fintype.card J+1)/M := by
  let d : ℝ := (Fintype.card I:ℝ)+Fintype.card J+1
  let w := T/d
  let L := M/(2*exp 1*T)
  let S := excessKernel (law J) F L
  let p := (law I).real {x | (x,T)∈excessKernel (law J) F (M/T)}
  have hd : 1≤d := by dsimp only [d]; linarith only [(Nat.cast_nonneg (Fintype.card I) : (0:ℝ) ≤ Fintype.card I),(Nat.cast_nonneg (Fintype.card J) : (0:ℝ) ≤ Fintype.card J)]
  have hd₀ : 0<d := zero_lt_one.trans_le hd
  have hw : 0<w := div_pos hT hd₀
  have hL : 0<L := div_pos hM (mul_pos (mul_pos zero_lt_two (exp_pos _)) hT)
  have hs : MeasurableSet S := measurableSet_excessKernel (law J) hf hL
  have hslice (u : ℝ) (hu : u∈Ioo T (T+w)) :
      ENNReal.ofReal (p/exp 1) ≤ law I ((fun x => (x,u)) ⁻¹' S) := by
    let a := u/T
    have ha : 1≤a := (one_le_div hT).mpr hu.1.le
    have hau : a*T=u := div_mul_cancel₀ _ hT.ne'
    have har : a-1≤1/d := by
      apply (sub_le_iff_le_add).mpr
      apply (div_le_iff₀ hT).mpr
      apply hu.2.le.trans_eq
      dsimp only [w]
      ring
    have ha₂ : a≤2 := by
      have hi := one_div_le_one_div_of_le zero_lt_one hd
      linarith only [har,hi]
    have hdim (n : ℕ) (hn : (n:ℝ)≤d) : a^n≤exp 1 := by
      apply jacobian_le ha
      exact (mul_le_mul hn har (sub_nonneg.mpr ha) hd₀.le).trans_eq (by field_simp [hd₀.ne'])
    have hi := hdim (Fintype.card I) (by dsimp only [d]; linarith only [(Nat.cast_nonneg (Fintype.card J) : (0:ℝ) ≤ Fintype.card J)])
    have hj := hdim (Fintype.card J) (by dsimp only [d]; linarith only [(Nat.cast_nonneg (Fintype.card I) : (0:ℝ) ≤ Fintype.card I)])
    have hprice : a^Fintype.card J*(L*a)≤M/T := calc
      _ ≤ exp 1*(L*2) := mul_le_mul hj (mul_le_mul_of_nonneg_left ha₂ hL.le)
        (mul_nonneg hL.le (zero_le_one.trans ha)) (exp_pos _).le
      _ = M/T := by dsimp only [L]; field_simp [(exp_pos (1:ℝ)).ne',hT.ne']
    have h := slice_dilation F hf hscale (T:=T) (div_pos hM hT) ha hi hprice
    rw [hau] at h
    rw [←ofReal_measureReal (measure_ne_top _ _)]
    apply ENNReal.ofReal_le_ofReal
    exact (div_le_iff₀ (exp_pos _)).mpr (h.trans_eq (mul_comm ..))
  have hint : ENNReal.ofReal (p/exp 1*w) ≤ ENNReal.ofReal (8/L) := calc
    _ = ∫⁻ _u : ℝ in Ioo T (T+w), ENNReal.ofReal (p/exp 1) := by
      rw [setLIntegral_const,Real.volume_Ioo,add_sub_cancel_left,ENNReal.ofReal_mul (div_nonneg measureReal_nonneg (exp_pos _).le)]
    _ ≤ ∫⁻ u : ℝ in Ioo T (T+w), law I ((fun x => (x,u)) ⁻¹' S) := lintegral_mono_ae
      ((ae_restrict_mem measurableSet_Ioo).mono fun u hu => hslice u hu)
    _ ≤ ∫⁻ u : ℝ, law I ((fun x => (x,u)) ⁻¹' S) := setLIntegral_le_lintegral _ _
    _ = (law I).prod volume S := (Measure.prod_apply_symm hs).symm
    _ ≤ _ := prod_excessKernel (law I) (law J) hf hL
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0≤8/L)).mp hint
  change p≤16*(exp 1)^2*d/M
  apply (le_div_iff₀ hM).mpr
  have h := mul_le_mul_of_nonneg_right hreal (mul_nonneg (mul_nonneg (exp_pos 1).le hd₀.le) (div_nonneg hM.le hT.le))
  dsimp only [L,w] at h
  convert h using 1 <;> field_simp [hT.ne',hM.ne',hd₀.ne',(exp_pos (1:ℝ)).ne'] <;> ring

#print axioms gaussian_conditional_maximal
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows.Conditioning
