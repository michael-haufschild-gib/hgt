import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekGammaMobiusMomentDetector

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open MeasureTheory Set Filter Topology
noncomputable section

/-- The original ground-subtracted source in reciprocal coordinates. -/
def pwGammaMobiusReciprocalTail (z : ℂ) (x : ℝ) : ℂ :=
  pwGammaMobiusTilt z (1/x)/pwGammaRaySource (1/x)-1

def pwGammaMobiusReciprocalInverseWeight (z : ℂ) (p n : ℕ) : ℝ :=
  ‖pwGammaMobiusReciprocalCoefficient z n‖/((n:ℝ)+1)^p

private theorem pwGammaCutoff_exp_bound (p : ℕ) {y : ℝ} (hy : 0<y) :
    Real.exp (-y) ≤ (p.factorial:ℝ)/y^p := by
  have hf : (0:ℝ)<p.factorial := by positivity
  have hb := Real.pow_div_factorial_le_exp y hy.le p
  rw [Real.exp_neg]
  apply (le_div_iff₀ (pow_pos hy p)).mpr
  rw [inv_mul_eq_div]
  exact (div_le_iff₀ (Real.exp_pos y)).mpr
    (by simpa only [mul_comm] using (div_le_iff₀ hf).mp hb)

theorem pwGammaMobiusReciprocalInverseWeight_bound {N p : ℕ} {z : ℂ}
    (hz : ‖z‖≤(N:ℝ)) (hp : N+3≤p) (n : ℕ) :
    pwGammaMobiusReciprocalInverseWeight z p n ≤ 2^(N+1)*(1/((n:ℝ)+1)^2) := by
  have ha : (0:ℝ)<(n:ℝ)+1 := by positivity
  have ha1 : (1:ℝ)≤(n:ℝ)+1 := by linarith [Nat.cast_nonneg (α:=ℝ) n]
  unfold pwGammaMobiusReciprocalInverseWeight
  calc
    _ ≤ ((n+2:ℕ):ℝ)^(N+1)*(1/((n:ℝ)+1)^p) := by
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right (pwGammaMobiusReciprocalCoefficient_norm_le hz n)
        (pow_pos ha p).le
    _ ≤ (2*((n:ℝ)+1))^(N+1)*(1/((n:ℝ)+1)^(N+3)) := by
      apply mul_le_mul
      · gcongr
        push_cast
        linarith [Nat.cast_nonneg (α:=ℝ) n]
      · apply one_div_le_one_div_of_le (by positivity)
        exact pow_le_pow_right₀ ha1 hp
      · positivity
      · positivity
    _ = _ := by
      rw [mul_pow, show N+3=(N+1)+2 by omega, pow_add]
      field_simp
      ring

theorem pwGammaMobiusReciprocalInverseWeight_summable {N p : ℕ} {z : ℂ}
    (hz : ‖z‖≤(N:ℝ)) (hp : N+3≤p) :
    Summable (pwGammaMobiusReciprocalInverseWeight z p) := by
  have hs : Summable (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)^2) := by
    have ht := (Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective Nat.succ_injective
    simpa only [Function.comp_def, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using ht
  apply (hs.mul_left (2^(N+1))).of_nonneg_of_le
  · intro n
    unfold pwGammaMobiusReciprocalInverseWeight
    positivity
  · exact pwGammaMobiusReciprocalInverseWeight_bound hz hp

private theorem pwGammaCutoff_atom_exp_bound (z : ℂ) (p n : ℕ) {x : ℝ} (hx : 0<x) :
    ‖pwGammaMobiusReciprocalCoefficient z n*(Real.exp (-((n:ℝ)+1)/x):ℂ)‖ ≤
      pwGammaMobiusReciprocalInverseWeight z p n*((p.factorial:ℝ)*x^p) := by
  have ha : (0:ℝ)<(n:ℝ)+1 := by positivity
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ ‖pwGammaMobiusReciprocalCoefficient z n‖*((p.factorial:ℝ)/(((n:ℝ)+1)/x)^p) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [neg_div] using pwGammaCutoff_exp_bound p (div_pos ha hx)
    _ = _ := by
      unfold pwGammaMobiusReciprocalInverseWeight
      rw [div_pow]
      field_simp

theorem pwGammaMobiusReciprocalTail_atoms_summable (z : ℂ) {x : ℝ} (hx : 0<x) :
    Summable (fun n => pwGammaMobiusReciprocalCoefficient z n*
      (Real.exp (-((n:ℝ)+1)/x):ℂ)) := by
  obtain ⟨N,hN⟩ := exists_nat_ge ‖z‖
  exact ((pwGammaMobiusReciprocalInverseWeight_summable hN (le_refl (N+3))).mul_right
    (((N+3).factorial:ℝ)*x^(N+3))).of_norm_bounded
      (fun n => pwGammaCutoff_atom_exp_bound z (N+3) n hx)

private theorem pwGammaCutoff_tail_weight_bound (z : ℂ) (p : ℕ)
    (hs : Summable (pwGammaMobiusReciprocalInverseWeight z p)) {x : ℝ} (hx : 0<x) :
    ‖pwGammaMobiusReciprocalTail z x‖ ≤
      ((p.factorial:ℝ)*(∑' n, pwGammaMobiusReciprocalInverseWeight z p n))*x^p := by
  rw [pwGammaMobiusReciprocalTail, pwGammaMobiusTilt_reciprocal_tail_eq z hx]
  have ht := tsum_of_norm_bounded (hs.hasSum.mul_right ((p.factorial:ℝ)*x^p))
    (fun n => pwGammaCutoff_atom_exp_bound z p n hx)
  simpa only [mul_assoc, mul_comm, mul_left_comm] using ht

theorem pwGammaMobiusReciprocalTail_polynomial_bound (z : ℂ) :
    ∃ p : ℕ, ∃ C : ℝ, 0≤C ∧ ∀ x : ℝ, 0<x → ‖pwGammaMobiusReciprocalTail z x‖≤C*x^p := by
  obtain ⟨N,hN⟩ := exists_nat_ge ‖z‖
  refine ⟨N+3, ((N+3).factorial:ℝ)*(∑' n, pwGammaMobiusReciprocalInverseWeight z (N+3) n), ?_, ?_⟩
  · apply mul_nonneg (by positivity)
    exact tsum_nonneg (fun n => by unfold pwGammaMobiusReciprocalInverseWeight; positivity)
  · intro x hx
    exact pwGammaCutoff_tail_weight_bound z (N+3)
      (pwGammaMobiusReciprocalInverseWeight_summable hN le_rfl) hx

/-- Each requested endpoint order has a bound for the entire signed arithmetic tail. -/
theorem pwGammaMobiusReciprocalTail_flat_bound (z : ℂ) (m : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ x : ℝ, 0<x → x≤1 → ‖pwGammaMobiusReciprocalTail z x‖≤C*x^m := by
  obtain ⟨N,hN⟩ := exists_nat_ge ‖z‖
  let p := N+m+3
  let C : ℝ := (p.factorial:ℝ)*(∑' n, pwGammaMobiusReciprocalInverseWeight z p n)
  have hC : 0≤C := by
    apply mul_nonneg (by positivity)
    exact tsum_nonneg (fun n => by unfold pwGammaMobiusReciprocalInverseWeight; positivity)
  refine ⟨C,hC,?_⟩
  intro x hx hx1
  have ht := pwGammaCutoff_tail_weight_bound z p
    (pwGammaMobiusReciprocalInverseWeight_summable hN (by dsimp [p]; omega)) hx
  calc
    _ ≤ C*x^p := ht
    _ = C*x^m*x^(N+3) := by rw [show p=m+(N+3) by dsimp [p]; omega, pow_add]; ring
    _ ≤ C*x^m*1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hx.le hx1) (by positivity)
    _ = C*x^m := mul_one _

/-- The original reciprocal difference, before either gain or loss is integrated. -/
def pwGammaMobiusReciprocalResponse (z : ℂ) (v h : ℝ) : ℂ :=
  (Real.exp (-h):ℂ)*(pwGammaMobiusReciprocalTail z (v+h)-pwGammaMobiusReciprocalTail z v)/(h:ℂ)

theorem pwGammaMobiusReciprocalResponse_eq_tsum (z : ℂ) {v h : ℝ}
    (hv : 0<v) (hh : 0<h) :
    pwGammaMobiusReciprocalResponse z v h = ∑' n, pwGammaMobiusReciprocalCoefficient z n*
      (pwGammaReciprocalTranslationKernel ((n:ℝ)+1) v h:ℂ) := by
  unfold pwGammaMobiusReciprocalResponse pwGammaMobiusReciprocalTail
  rw [pwGammaMobiusTilt_reciprocal_tail_eq z (add_pos hv hh),
    pwGammaMobiusTilt_reciprocal_tail_eq z hv,
    ← (pwGammaMobiusReciprocalTail_atoms_summable z (add_pos hv hh)).tsum_sub
      (pwGammaMobiusReciprocalTail_atoms_summable z hv), ← tsum_mul_left, ← tsum_div_const]
  apply tsum_congr
  intro n
  unfold pwGammaReciprocalTranslationKernel
  push_cast
  ring

/-- The endpoint-flat kernel estimate survives the complete signed sum. -/
theorem pwGammaMobiusReciprocalResponse_weight_bound {N r : ℕ} {z : ℂ}
    (hz : ‖z‖≤(N:ℝ)) (hr : N+2≤r) {v h : ℝ} (hv : 0<v) (hh : 0<h) :
    ‖pwGammaMobiusReciprocalResponse z v h‖ ≤
      (((r+2).factorial:ℝ)*(∑' n, pwGammaMobiusReciprocalInverseWeight z (r+1) n))*
        Real.exp (-h)*(v+h)^r := by
  rw [pwGammaMobiusReciprocalResponse_eq_tsum z hv hh]
  have hs := pwGammaMobiusReciprocalInverseWeight_summable hz (by omega : N+3≤r+1)
  have hb : ∀ n : ℕ, ‖pwGammaMobiusReciprocalCoefficient z n*
      (pwGammaReciprocalTranslationKernel ((n:ℝ)+1) v h:ℂ)‖ ≤
      pwGammaMobiusReciprocalInverseWeight z (r+1) n*
        (((r+2).factorial:ℝ)*Real.exp (-h)*(v+h)^r) := by
      intro n
      have ha : (0:ℝ)<(n:ℝ)+1 := by positivity
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg
        (pwGammaReciprocalTranslationKernel_nonneg ha.le hv hh)]
      calc
        _ ≤ ‖pwGammaMobiusReciprocalCoefficient z n‖*
            ((((r+2).factorial:ℝ)/((n:ℝ)+1)^(r+1))*Real.exp (-h)*(v+h)^r) :=
          mul_le_mul_of_nonneg_left (pwGammaReciprocalTranslationKernel_flat_bound r ha hv hh) (norm_nonneg _)
        _ = _ := by unfold pwGammaMobiusReciprocalInverseWeight; ring
  have ht := tsum_of_norm_bounded (hs.hasSum.mul_right
    (((r+2).factorial:ℝ)*Real.exp (-h)*(v+h)^r)) hb
  simpa only [mul_assoc, mul_comm, mul_left_comm] using ht


/-- This is the normalized response of the already admitted original operator. -/
theorem pwGammaMobiusReciprocalResponse_source_eq (z : ℂ) {v h : ℝ}
    (hv : 0<v) (hh : 0<h) :
    pwGammaMobiusReciprocalResponse z v h =
      pwGammaMobiusSameSourceResponse z v h/pwGammaRaySource v := by
  rw [pwGammaMobiusSameSourceResponse, pwGammaWeightedTranslation_source_ratio _ hh.le hv]
  unfold pwGammaMobiusReciprocalResponse pwGammaMobiusReciprocalTail pwGammaRayInverseReflection
  simp only [one_div]
  field_simp [pwGammaRaySource_ne_zero]
  ring

theorem pwGammaMobiusReciprocalResponse_integrable (z : ℂ) {v : ℝ} (hv : 0<v) :
    IntegrableOn (pwGammaMobiusReciprocalResponse z v) (Ioi 0) := by
  apply IntegrableOn.congr_fun
    ((pwGammaMobiusSameSourceResponse_integrable z hv).div_const (pwGammaRaySource v))
    _ measurableSet_Ioi
  intro h hh
  exact (pwGammaMobiusReciprocalResponse_source_eq z hv hh).symm

theorem pwGammaMobiusReciprocalResponse_integral_eq (z : ℂ) {v : ℝ} (hv : 0<v) :
    (∫ h in Ioi (0:ℝ), pwGammaMobiusReciprocalResponse z v h) =
      pwGammaMobiusSameSourceCurrent z v/pwGammaRaySource v := by
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun h hh => pwGammaMobiusReciprocalResponse_source_eq z hv hh), integral_div]
  rfl

/-- The retained near-diagonal integral is flat at every requested order. -/
theorem pwGammaMobiusReciprocalResponse_near_flat_bound (z : ℂ) (m : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ v : ℝ, 0<v → v≤1 →
      ‖∫ h in (0:ℝ)..v, pwGammaMobiusReciprocalResponse z v h‖ ≤ C*v^(m+1) := by
  obtain ⟨N,hN⟩ := exists_nat_ge ‖z‖
  let r := N+m+2
  let A : ℝ := ((r+2).factorial:ℝ)*(∑' n, pwGammaMobiusReciprocalInverseWeight z (r+1) n)
  have hA : 0≤A := by
    apply mul_nonneg (by positivity)
    exact tsum_nonneg (fun n => by unfold pwGammaMobiusReciprocalInverseWeight; positivity)
  refine ⟨A*2^r, by positivity, ?_⟩
  intro v hv hv1
  have hb : ∀ h ∈ uIoc (0:ℝ) v, ‖pwGammaMobiusReciprocalResponse z v h‖ ≤ (A*2^r)*v^r := by
    intro h hh
    have hh' : h ∈ Ioc (0:ℝ) v := by simpa only [uIoc_of_le hv.le] using hh
    have ht := pwGammaMobiusReciprocalResponse_weight_bound hN
      (show N+2≤r by dsimp [r]; omega) hv hh'.1
    calc
      _ ≤ A*Real.exp (-h)*(v+h)^r := ht
      _ ≤ A*1*(2*v)^r := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by linarith [hh'.1])) hA
        · exact pow_le_pow_left₀ (add_pos hv hh'.1).le (show v+h≤2*v by linarith [hh'.2]) r
        · exact (pow_pos (add_pos hv hh'.1) r).le
        · positivity
      _ = (A*2^r)*v^r := by rw [mul_pow]; ring
  have ht := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [sub_zero, abs_of_pos hv] at ht
  calc
    _ ≤ (A*2^r)*v^r*v := ht
    _ = (A*2^r)*v^(m+1)*v^(N+2) := by
      rw [mul_assoc, ← pow_succ, show r+1=(m+1)+(N+2) by dsimp [r]; omega, pow_add]
      ring
    _ ≤ (A*2^r)*v^(m+1)*1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ hv.le hv1) (by positivity)
    _ = (A*2^r)*v^(m+1) := mul_one _


/-- The signed reciprocal source is measurable on its physical half-line. -/
theorem pwGammaMobiusReciprocalTail_aestronglyMeasurable (z : ℂ) :
    AEStronglyMeasurable (pwGammaMobiusReciprocalTail z) (volume.restrict (Ioi 0)) := by
  have hm : Measurable (fun x : ℝ => ∑' n, pwGammaMobiusReciprocalCoefficient z n*
      (Real.exp (-((n:ℝ)+1)/x):ℂ)) := by
    apply Measurable.tsum
    intro n
    fun_prop
  apply hm.aestronglyMeasurable.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (pwGammaMobiusTilt_reciprocal_tail_eq z hx).symm

/-- Exponential damping admits the complete signed source at infinity. -/
theorem pwGammaMobiusReciprocalTail_exp_integrable (z : ℂ) :
    IntegrableOn (fun x : ℝ => (Real.exp (-x):ℂ)*pwGammaMobiusReciprocalTail z x) (Ioi 0) := by
  obtain ⟨p,C,hC,hb⟩ := pwGammaMobiusReciprocalTail_polynomial_bound z
  have hi : IntegrableOn (fun x : ℝ => Real.exp (-x)*x^p) (Ioi 0) := by
    simpa only [add_sub_cancel_right, Real.rpow_natCast] using
      Real.GammaIntegral_convergent (s:=(p:ℝ)+1) (by positivity)
  apply (hi.const_mul C).mono'
  · exact (by fun_prop : AEStronglyMeasurable (fun x : ℝ => (Real.exp (-x):ℂ))
        (volume.restrict (Ioi 0))).mul (pwGammaMobiusReciprocalTail_aestronglyMeasurable z)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc
      _ ≤ Real.exp (-x)*(C*x^p) := mul_le_mul_of_nonneg_left (hb x hx) (Real.exp_pos _).le
      _ = _ := by ring

/-- Every coefficient in a finite cutoff expansion uses this original-source integral. -/
def pwGammaMobiusReciprocalEndpointIntegrand (z : ℂ) (j : ℕ) (x : ℝ) : ℂ :=
  (Real.exp (-x):ℂ)*pwGammaMobiusReciprocalTail z x/(x:ℂ)^(j+1)

def pwGammaMobiusReciprocalEndpointMoment (z : ℂ) (j : ℕ) : ℂ :=
  ∫ x in Ioi (0:ℝ), pwGammaMobiusReciprocalEndpointIntegrand z j x

theorem pwGammaMobiusReciprocalEndpointIntegrand_norm (z : ℂ) (j : ℕ) {x : ℝ} (hx : 0<x) :
    ‖pwGammaMobiusReciprocalEndpointIntegrand z j x‖ =
      Real.exp (-x)*‖pwGammaMobiusReciprocalTail z x‖/x^(j+1) := by
  unfold pwGammaMobiusReciprocalEndpointIntegrand
  rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg hx.le]

theorem pwGammaMobiusReciprocalEndpointIntegrand_integrable (z : ℂ) (j : ℕ) :
    IntegrableOn (pwGammaMobiusReciprocalEndpointIntegrand z j) (Ioi 0) := by
  have hi := (pwGammaMobiusReciprocalTail_exp_integrable z).norm.add
    (pwGammaMobiusReciprocalMomentIntegrand_integrable z j).norm
  apply hi.mono'
  · unfold pwGammaMobiusReciprocalEndpointIntegrand
    simp only [div_eq_mul_inv]
    exact ((by fun_prop : AEStronglyMeasurable (fun x : ℝ => (Real.exp (-x):ℂ))
      (volume.restrict (Ioi 0))).mul (pwGammaMobiusReciprocalTail_aestronglyMeasurable z)).mul
        (by fun_prop)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [pwGammaMobiusReciprocalEndpointIntegrand_norm z j hx]
    have hn : 0 ≤ Real.exp (-x)*‖pwGammaMobiusReciprocalTail z x‖ := by positivity
    have he : ‖(Real.exp (-x):ℂ)*pwGammaMobiusReciprocalTail z x‖ =
        Real.exp (-x)*‖pwGammaMobiusReciprocalTail z x‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hm : ‖pwGammaMobiusReciprocalMomentIntegrand z j x‖ =
        Real.exp (-x)*‖pwGammaMobiusReciprocalTail z x‖/x^(j+3) := by
      unfold pwGammaMobiusReciprocalMomentIntegrand pwGammaMobiusReciprocalTail
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_pos (Real.exp_pos _) (pow_pos hx _)).le]
      ring
    dsimp only [Pi.add_apply]
    rw [he, hm]
    by_cases hx1 : x≤1
    · have hp : x^(j+3)≤x^(j+1) := by
        rw [show j+3=(j+1)+2 by omega, pow_add]
        exact mul_le_of_le_one_right (pow_pos hx _).le (pow_le_one₀ hx.le hx1)
      exact (div_le_div_of_nonneg_left hn (pow_pos hx _) hp).trans (le_add_of_nonneg_left hn)
    · have hp : (1:ℝ)≤x^(j+1) := one_le_pow₀ (le_of_not_ge hx1)
      exact (div_le_self hn hp).trans (le_add_of_nonneg_right (div_nonneg hn (pow_pos hx _).le))

theorem pwGammaMobiusReciprocalEndpointMoment_detector_eq (z : ℂ) (k : ℕ) :
    pwGammaMobiusReciprocalEndpointMoment z (k+2) = pwGammaMobiusReciprocalMoment z k := by
  rw [pwGammaMobiusReciprocalEndpointMoment, ← pwGammaMobiusReciprocalMoment_integral_eq]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  unfold pwGammaMobiusReciprocalEndpointIntegrand pwGammaMobiusReciprocalMomentIntegrand
    pwGammaMobiusReciprocalTail
  push_cast
  rw [show k+2+1=k+3 by omega]
  ring

/-- Dividing by any fixed power preserves the endpoint flatness needed by cutoff subtraction. -/
theorem pwGammaMobiusReciprocalEndpointIntegrand_flat_bound (z : ℂ) (j m : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ x : ℝ, 0<x → x≤1 →
      ‖pwGammaMobiusReciprocalEndpointIntegrand z j x‖≤C*x^m := by
  obtain ⟨C,hC,hb⟩ := pwGammaMobiusReciprocalTail_flat_bound z (m+(j+1))
  refine ⟨C,hC,?_⟩
  intro x hx hx1
  rw [pwGammaMobiusReciprocalEndpointIntegrand_norm z j hx]
  calc
    _ ≤ 1*(C*x^(m+(j+1)))/x^(j+1) := by
      apply div_le_div_of_nonneg_right _ (pow_pos hx _).le
      exact mul_le_mul (Real.exp_le_one_iff.mpr (by linarith)) (hb x hx hx1)
        (norm_nonneg _) zero_le_one
    _ = C*x^m := by rw [one_mul, pow_add]; field_simp

/-- Every removed initial piece of every actual moment is flat, with its cutoff retained. -/
theorem pwGammaMobiusReciprocalEndpointMoment_near_flat_bound (z : ℂ) (j m : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ v : ℝ, 0<v → v≤1 →
      ‖∫ x in (0:ℝ)..v, pwGammaMobiusReciprocalEndpointIntegrand z j x‖≤C*v^(m+1) := by
  obtain ⟨C,hC,hb⟩ := pwGammaMobiusReciprocalEndpointIntegrand_flat_bound z j m
  refine ⟨C,hC,?_⟩
  intro v hv hv1
  have hi : ∀ x∈uIoc (0:ℝ) v, ‖pwGammaMobiusReciprocalEndpointIntegrand z j x‖≤C*v^m := by
    intro x hx
    have hx' : x∈Ioc (0:ℝ) v := by simpa only [uIoc_of_le hv.le] using hx
    exact (hb x hx'.1 (hx'.2.trans hv1)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx'.1.le hx'.2 m) hC)
  have ht := intervalIntegral.norm_integral_le_of_norm_le_const hi
  rw [sub_zero, abs_of_pos hv, mul_assoc, ← pow_succ] at ht
  exact ht

end
end RHTower
