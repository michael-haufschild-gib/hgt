import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekGammaMobiusReflectedFrullani

/-! Endpoint-sensitive kernel and complete atom bound for the original nonlocal generator
on the literal reflected arithmetic source. No spectral balance is assumed. -/

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open ArithmeticFunction MeasureTheory Set Filter Topology
noncomputable section

/-- Scalar kernel of the original weighted translation on a reflected Gamma atom. -/
def pwGammaReciprocalTranslationKernel (a x h : ℝ) : ℝ :=
  Real.exp (-h)*(Real.exp (-a/(x+h))-Real.exp (-a/x))/h

theorem pwGammaReciprocalTranslationKernel_zero (x h : ℝ) :
    pwGammaReciprocalTranslationKernel 0 x h = 0 := by
  simp [pwGammaReciprocalTranslationKernel]

theorem pwGammaReciprocalTranslationKernel_nonneg {a x h : ℝ}
    (ha : 0 ≤ a) (hx : 0 < x) (hh : 0 < h) :
    0 ≤ pwGammaReciprocalTranslationKernel a x h := by
  have he : Real.exp (-a/x) ≤ Real.exp (-a/(x+h)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div]
    apply neg_le_neg
    exact div_le_div_of_nonneg_left ha hx (by linarith)
  exact div_nonneg (mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr he)) hh.le

theorem pwGammaReciprocalTranslationKernel_pos {a x h : ℝ}
    (ha : 0 < a) (hx : 0 < x) (hh : 0 < h) :
    0 < pwGammaReciprocalTranslationKernel a x h := by
  have he : Real.exp (-a/x) < Real.exp (-a/(x+h)) := by
    apply Real.exp_lt_exp.mpr
    rw [neg_div, neg_div]
    apply neg_lt_neg
    exact div_lt_div_of_pos_left ha hx (by linarith)
  exact div_pos (mul_pos (Real.exp_pos _) (sub_pos.mpr he)) hh

/-- The exact reciprocal difference retains both source denominators. -/
theorem pwGammaReciprocalTranslationKernel_le {a x h : ℝ}
    (ha : 0 ≤ a) (hx : 0 < x) (hh : 0 < h) :
    pwGammaReciprocalTranslationKernel a x h ≤
      (a/(x*(x+h)))*Real.exp (-h)*Real.exp (-a/(x+h)) := by
  have hxH : 0 < x+h := add_pos hx hh
  let v : ℝ := a*h/(x*(x+h))
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hi : 1-Real.exp (-v) ≤ v := by
    linarith [Real.add_one_le_exp (-v)]
  have he : Real.exp (-a/x) = Real.exp (-a/(x+h))*Real.exp (-v) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [v]
    field_simp
    ring
  rw [pwGammaReciprocalTranslationKernel, he]
  calc
    _ = (Real.exp (-h)*Real.exp (-a/(x+h)))*(1-Real.exp (-v))/h := by ring
    _ ≤ (Real.exp (-h)*Real.exp (-a/(x+h)))*v/h := by gcongr
    _ = _ := by dsimp [v]; field_simp

private theorem pwGammaSameSource_exp_neg_bound (k : ℕ) {y : ℝ} (hy : 0 < y) :
    Real.exp (-y) ≤ (k.factorial : ℝ)/y^k := by
  have hf : (0 : ℝ) < k.factorial := by positivity
  have hb := Real.pow_div_factorial_le_exp y hy.le k
  rw [Real.exp_neg]
  apply (le_div_iff₀ (pow_pos hy k)).mpr
  rw [inv_mul_eq_div]
  exact (div_le_iff₀ (Real.exp_pos y)).mpr
    (by simpa only [mul_comm] using (div_le_iff₀ hf).mp hb)

/-- A common polynomial majorant preserving the h=0 cancellation and x=0 endpoint. -/
theorem pwGammaReciprocalTranslationKernel_polynomial_le (k : ℕ) {a x h : ℝ}
    (ha : 0 < a) (hx : 0 < x) (hh : 0 < h) :
    pwGammaReciprocalTranslationKernel a x h ≤
      (((k+1).factorial : ℝ)/a^k)*Real.exp (-h)*(x+h)^k/x := by
  have hxH := add_pos hx hh
  calc
    _ ≤ (a/(x*(x+h)))*Real.exp (-h)*Real.exp (-a/(x+h)) :=
      pwGammaReciprocalTranslationKernel_le ha.le hx hh
    _ ≤ (a/(x*(x+h)))*Real.exp (-h)*(((k+1).factorial : ℝ)/(a/(x+h))^(k+1)) := by
      gcongr
      simpa only [neg_div] using pwGammaSameSource_exp_neg_bound (k+1) (div_pos ha hxH)
    _ = _ := by rw [div_pow, pow_succ]; field_simp; ring

/-- Separable joint majorant, with displacement first and original source coordinate second. -/
def pwGammaSameSourceMajorant (k : ℕ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (-p.1)*(‖pwGammaRaySource p.2‖/p.2)*(p.2^k+p.1^k)

private theorem pwGammaSameSource_inverse_moment_eq (k : ℕ) {x : ℝ} (hx : 0 < x) :
    x^k*(‖pwGammaRaySource x‖/x) = Real.exp (-x)*x^(((k : ℝ)+1/2)-1) := by
  rw [pwGammaRaySource_eq hx, Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.sqrt_eq_rpow]
  calc
    _ = Real.exp (-x)*(x^(k : ℝ)*x^(1/2 : ℝ)/x^(1 : ℝ)) := by
      rw [Real.rpow_natCast, Real.rpow_one]
      ring
    _ = _ := by rw [← Real.rpow_add hx, ← Real.rpow_sub hx]

theorem pwGammaRaySource_inverse_polynomial_moment_integrable (k : ℕ) :
    IntegrableOn (fun x : ℝ => x^k*(‖pwGammaRaySource x‖/x)) (Ioi 0) :=
  IntegrableOn.congr_fun (Real.GammaIntegral_convergent (s := (k : ℝ)+1/2) (by positivity))
    (fun x hx => (pwGammaSameSource_inverse_moment_eq k hx).symm) measurableSet_Ioi

theorem pwGammaRaySource_inverse_polynomial_moment_integral (k : ℕ) :
    (∫ x in Ioi (0 : ℝ), x^k*(‖pwGammaRaySource x‖/x)) = Real.Gamma ((k : ℝ)+1/2) := by
  rw [Real.Gamma_eq_integral (by positivity : 0 < (k : ℝ)+1/2)]
  exact setIntegral_congr_fun measurableSet_Ioi (fun x hx => pwGammaSameSource_inverse_moment_eq k hx)

private theorem pwGammaSameSource_exp_moment_integrable (k : ℕ) :
    IntegrableOn (fun h : ℝ => h^k*Real.exp (-h)) (Ioi 0) := by
  have he := Real.GammaIntegral_convergent (s := (k : ℝ)+1) (by positivity)
  apply IntegrableOn.congr_fun he _ measurableSet_Ioi
  intro h hh
  change Real.exp (-h)*h^((k : ℝ)+1-1) = h^k*Real.exp (-h)
  rw [add_sub_cancel_right, Real.rpow_natCast]
  ring

private theorem pwGammaSameSource_exp_moment_integral (k : ℕ) :
    (∫ h in Ioi (0 : ℝ), h^k*Real.exp (-h)) = Real.Gamma ((k : ℝ)+1) := by
  rw [Real.Gamma_eq_integral (by positivity : 0 < (k : ℝ)+1)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro h hh
  change h^k*Real.exp (-h) = Real.exp (-h)*h^((k : ℝ)+1-1)
  rw [add_sub_cancel_right, Real.rpow_natCast]
  ring

theorem pwGammaSameSourceMajorant_split (k : ℕ) (p : ℝ × ℝ) :
    pwGammaSameSourceMajorant k p =
      Real.exp (-p.1)*(p.2^k*(‖pwGammaRaySource p.2‖/p.2))+
        (p.1^k*Real.exp (-p.1))*(‖pwGammaRaySource p.2‖/p.2) := by
  rw [pwGammaSameSourceMajorant]
  ring

theorem pwGammaSameSourceMajorant_integrable (k : ℕ) :
    Integrable (pwGammaSameSourceMajorant k)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have he : IntegrableOn (fun h : ℝ => Real.exp (-h)) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using pwGammaSameSource_exp_moment_integrable 0
  have hx : IntegrableOn (fun x : ℝ => ‖pwGammaRaySource x‖/x) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using pwGammaRaySource_inverse_polynomial_moment_integrable 0
  have h0 := he.mul_prod (pwGammaRaySource_inverse_polynomial_moment_integrable k)
  have h1 := (pwGammaSameSource_exp_moment_integrable k).mul_prod hx
  exact (h0.add h1).congr (Eventually.of_forall (fun p => (pwGammaSameSourceMajorant_split k p).symm))

theorem pwGammaSameSourceMajorant_integrable_section (k : ℕ) (x : ℝ) :
    IntegrableOn (fun h : ℝ => pwGammaSameSourceMajorant k (h,x)) (Ioi 0) := by
  have he : IntegrableOn (fun h : ℝ => Real.exp (-h)) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using pwGammaSameSource_exp_moment_integrable 0
  have h0 := he.mul_const (x^k*(‖pwGammaRaySource x‖/x))
  have h1 := (pwGammaSameSource_exp_moment_integrable k).mul_const (‖pwGammaRaySource x‖/x)
  exact (h0.add h1).congr (Eventually.of_forall (fun h => (pwGammaSameSourceMajorant_split k (h,x)).symm))

theorem pwGammaReciprocalTranslationKernel_integrable {a x : ℝ} (ha : 0 ≤ a) (hx : 0 < x) :
    IntegrableOn (pwGammaReciprocalTranslationKernel a x) (Ioi 0) := by
  rcases eq_or_lt_of_le ha with he | ha
  · subst a
    have hz : pwGammaReciprocalTranslationKernel 0 x = 0 := by
      funext h
      exact pwGammaReciprocalTranslationKernel_zero x h
    rw [hz]
    exact integrable_zero _ _ _
  have he : IntegrableOn (fun h : ℝ => Real.exp (-h)/x) (Ioi 0) := by
    have ht := (pwGammaSameSource_exp_moment_integrable 0).div_const x
    simpa only [IntegrableOn, pow_zero, one_mul] using ht
  have hm : Measurable (pwGammaReciprocalTranslationKernel a x) := by
    unfold pwGammaReciprocalTranslationKernel
    fun_prop
  apply Integrable.mono' he hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  rw [Real.norm_of_nonneg (pwGammaReciprocalTranslationKernel_nonneg ha.le hx hh)]
  simpa only [Nat.zero_add, Nat.factorial_one, Nat.cast_one, pow_zero, div_one, one_mul, mul_one] using
    pwGammaReciprocalTranslationKernel_polynomial_le 0 ha hx hh

theorem pwGammaReciprocalTranslationKernel_integral_pos {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    0 < ∫ h in Ioi (0 : ℝ), pwGammaReciprocalTranslationKernel a x h := by
  have hp : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] pwGammaReciprocalTranslationKernel a x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    exact (pwGammaReciprocalTranslationKernel_pos ha hx hh).le
  rw [setIntegral_pos_iff_support_of_nonneg_ae hp (pwGammaReciprocalTranslationKernel_integrable ha.le hx)]
  have hs : Function.support (pwGammaReciprocalTranslationKernel a x) ∩ Ioi (0 : ℝ) = Ioi 0 := by
    apply inter_eq_right.mpr
    intro h hh
    exact (pwGammaReciprocalTranslationKernel_pos ha hx hh).ne'
  rw [hs]
  simp

/-- Positive scalar weight retained in the complete same-source operator defect. -/
def pwGammaSameSourceDefectWeight (n : ℕ) (x : ℝ) : ℝ :=
  if n = 0 then 0 else Real.sqrt (n : ℝ)*
    ((∫ h in Ioi (0 : ℝ), pwGammaReciprocalTranslationKernel ((n : ℝ)-1) x h)+
      Real.log (n : ℝ)*Real.exp (-((n : ℝ)-1)/x))

theorem pwGammaSameSourceDefectWeight_zero (x : ℝ) : pwGammaSameSourceDefectWeight 0 x = 0 := by
  simp [pwGammaSameSourceDefectWeight]

theorem pwGammaSameSourceDefectWeight_one (x : ℝ) : pwGammaSameSourceDefectWeight 1 x = 0 := by
  simp [pwGammaSameSourceDefectWeight, pwGammaReciprocalTranslationKernel_zero]

theorem pwGammaSameSourceDefectWeight_pos {n : ℕ} (hn : 1 < n) {x : ℝ} (hx : 0 < x) :
    0 < pwGammaSameSourceDefectWeight n x := by
  have hn0 : 0 < n := lt_trans zero_lt_one hn
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  rw [pwGammaSameSourceDefectWeight, if_neg (Nat.ne_of_gt hn0)]
  apply mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast hn0))
  exact add_pos (pwGammaReciprocalTranslationKernel_integral_pos (by linarith) hx)
    (mul_pos (Real.log_pos hn1) (Real.exp_pos _))

theorem pwGammaSameSourceMajorant_nonneg (k : ℕ) {h x : ℝ} (hh : 0 < h) (hx : 0 < x) :
    0 ≤ pwGammaSameSourceMajorant k (h,x) := by
  unfold pwGammaSameSourceMajorant
  positivity

theorem pwGammaReciprocalTranslationKernel_source_le (k : ℕ) {a x h : ℝ}
    (ha : 0 < a) (hx : 0 < x) (hh : 0 < h) :
    ‖pwGammaRaySource x‖*pwGammaReciprocalTranslationKernel a x h ≤
      (((k+1).factorial : ℝ)/a^k*2^(k-1))*pwGammaSameSourceMajorant k (h,x) := by
  calc
    _ ≤ ‖pwGammaRaySource x‖*((((k+1).factorial : ℝ)/a^k)*Real.exp (-h)*(x+h)^k/x) :=
      mul_le_mul_of_nonneg_left (pwGammaReciprocalTranslationKernel_polynomial_le k ha hx hh) (norm_nonneg _)
    _ ≤ ‖pwGammaRaySource x‖*((((k+1).factorial : ℝ)/a^k)*Real.exp (-h)*
        (2^(k-1)*(x^k+h^k))/x) := by
      gcongr
      exact add_pow_le hx.le hh.le k
    _ = _ := by rw [pwGammaSameSourceMajorant]; ring

/-- Original translation applied to the literal reflected arithmetic atom, on both positive rays. -/
def pwGammaMobiusSameSourceAtom (z : ℂ) (n : ℕ) (p : ℝ × ℝ) : ℂ :=
  (pwGammaWeightedTranslation p.1 (pwGammaMobiusReflectedAtom z n) p.2-
    (Real.exp (-p.1) : ℂ)*pwGammaMobiusReflectedAtom z n p.2)/(p.1 : ℂ)

theorem pwGammaMobiusSameSourceAtom_eq (z : ℂ) {n : ℕ} (hn : 0 < n) {h x : ℝ}
    (hh : 0 ≤ h) (hx : 0 < x) :
    pwGammaMobiusSameSourceAtom z n (h,x) =
      (((moebius n : ℤ) : ℂ)*Complex.exp (-z*(Real.log (n : ℝ) : ℂ)))*
        ((Real.sqrt (n : ℝ) : ℂ)*pwGammaRaySource x*
          (pwGammaReciprocalTranslationKernel ((n : ℝ)-1) x h : ℂ)) := by
  have hxH := add_pos_of_pos_of_nonneg hx hh
  rw [pwGammaMobiusSameSourceAtom, pwGammaWeightedTranslation_source_ratio _ hh hx,
    pwGammaMobiusReflectedAtom_eq z hn hxH, pwGammaMobiusReflectedAtom_eq z hn hx,
    pwGammaReciprocalTranslationKernel]
  push_cast
  field_simp [pwGammaRaySource_ne_zero]

theorem pwGammaMobiusSameSourceAtom_zero (z : ℂ) : pwGammaMobiusSameSourceAtom z 0 = 0 := by
  funext p
  simp [pwGammaMobiusSameSourceAtom, pwGammaMobiusReflectedAtom_zero, pwGammaWeightedTranslation]

theorem pwGammaMobiusSameSourceAtom_one (z : ℂ) {h x : ℝ}
    (hh : 0 ≤ h) (hx : 0 < x) : pwGammaMobiusSameSourceAtom z 1 (h,x) = 0 := by
  rw [pwGammaMobiusSameSourceAtom_eq z zero_lt_one hh hx]
  simp [pwGammaReciprocalTranslationKernel_zero]

private theorem pwGammaSameSource_coefficient_bound {N n : ℕ} {z : ℂ}
    (hz : ‖z‖ ≤ (N : ℝ)) (hn : 0 < n) :
    ‖Complex.exp (-z*(Real.log (n : ℝ) : ℂ))‖ ≤ (n : ℝ)^N := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hre : -z.re ≤ (N : ℝ) :=
    (neg_le_abs z.re).trans ((Complex.abs_re_le_norm z).trans hz)
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  calc
    _ ≤ Real.exp ((N : ℝ)*Real.log (n : ℝ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hre (Real.log_nonneg hn1))
    _ = _ := by rw [Real.exp_nat_mul, Real.exp_log hnr]

/-- Complete atom bound uniform on every bounded coefficient region. -/
theorem pwGammaMobiusSameSourceAtom_norm_le {N : ℕ} {z : ℂ}
    (hz : ‖z‖ ≤ (N : ℝ)) (n : ℕ) {h x : ℝ} (hh : 0 < h) (hx : 0 < x) :
    ‖pwGammaMobiusSameSourceAtom z (n+2) (h,x)‖ ≤
      (2^(N+1)*((N+4).factorial : ℝ)*2^(N+2))*(1/((n : ℝ)+1)^(2 : ℕ))*
        pwGammaSameSourceMajorant (N+3) (h,x) := by
  have hn : 0 < n+2 := by omega
  have hn1 : (1 : ℝ) ≤ ((n+2 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n+2 by omega)
  have ha : (0 : ℝ) < ((n+2 : ℕ) : ℝ)-1 := by push_cast; linarith [(show (0 : ℝ) ≤ n from Nat.cast_nonneg n)]
  have hmu : ‖((moebius (n+2) : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (show |moebius (n+2)| ≤ 1 from abs_moebius_le_one)
  have hc := pwGammaSameSource_coefficient_bound hz hn
  have hs := Real.sqrt_le_self_iff.mpr (Or.inr hn1)
  have hK := pwGammaReciprocalTranslationKernel_nonneg ha.le hx hh
  have hJ := pwGammaSameSourceMajorant_nonneg (N+3) hh hx
  rw [pwGammaMobiusSameSourceAtom_eq z hn hh.le hx]
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.norm_of_nonneg hK]
  calc
    _ ≤ (1*((n+2 : ℕ) : ℝ)^N)*
        ((((n+2 : ℕ) : ℝ))*‖pwGammaRaySource x‖*pwGammaReciprocalTranslationKernel (((n+2 : ℕ) : ℝ)-1) x h) := by
      gcongr
    _ = ((n+2 : ℕ) : ℝ)^(N+1)*
        (‖pwGammaRaySource x‖*pwGammaReciprocalTranslationKernel (((n+2 : ℕ) : ℝ)-1) x h) := by
      rw [pow_succ]; ring
    _ ≤ ((n+2 : ℕ) : ℝ)^(N+1)*
        (((((N+3)+1).factorial : ℝ)/(((n+2 : ℕ) : ℝ)-1)^(N+3)*2^((N+3)-1))*
          pwGammaSameSourceMajorant (N+3) (h,x)) := by
      exact mul_le_mul_of_nonneg_left
        (pwGammaReciprocalTranslationKernel_source_le (N+3) ha hx hh) (by positivity)
    _ ≤ (2*((n : ℝ)+1))^(N+1)*
        ((((N+4).factorial : ℝ)/((n : ℝ)+1)^(N+3)*2^(N+2))*
          pwGammaSameSourceMajorant (N+3) (h,x)) := by
      simp only [Nat.cast_add, Nat.cast_ofNat, show N+3+1=N+4 by omega,
        show N+3-1=N+2 by omega]
      rw [show (n : ℝ)+2-1=(n : ℝ)+1 by ring]
      gcongr
      linarith
    _ = _ := by
      rw [mul_pow, show N+3=(N+1)+2 by omega, pow_add]
      field_simp
      ring

end
end RHTower
