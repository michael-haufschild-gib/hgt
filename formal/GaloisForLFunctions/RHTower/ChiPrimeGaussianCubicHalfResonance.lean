import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicRowCancellation

/-!
# Complete physical Gaussian cubic rows at the three-halves resonance

The literal frozen profile is `W(3*x/2)*V(x)`. Its lower band endpoint does
not vanish. Abel summation and one signed integration retain that boundary,
giving uniform inverse-frequency decay after exact logarithmic unweighting.

For actual full-band primes, parity makes the half-integer phase exactly
negative and excludes zero residual `2*p-3*r`. The final bound controls each
complete physical q-row, with its contraction removed and both kernel errors
and the moving height window retained.

Summing these bounds over the prime-pair resonance family requires a separate
arithmetic argument. The full signed cubic and downstream BAG recurrence remain
open; this leaf does not assert RH.
-/

noncomputable section
open Complex MeasureTheory Set Filter Finset
open scoped Topology
namespace RHTower
open GaloisForLFunctions.RHTower

/-- Scaled Abel error with both physical band endpoints retained. -/
theorem primeProfile_scaledAbel_error
    (c : ℕ → ℂ) (f f' : ℝ → ℂ) (ell : ℂ) {N L ε : ℝ}
    (hN : 0 < N) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hf : ∀ x ∈ Icc (1 : ℝ) 2, HasDerivAt f (f' x) x)
    (hfc : ContinuousOn f' (Icc (1 : ℝ) 2))
    (hfb : ∀ x ∈ Icc (1 : ℝ) 2, ‖f' x‖ ≤ L)
    (hA : ∀ x ∈ Icc N (2 * N), ‖primeProfileCum c x - ell * (x : ℂ)‖ ≤ ε * x) :
    ‖(∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, f ((n : ℝ) / N) * c n) / (N : ℂ) -
      ell * (∫ x in (1 : ℝ)..2, f x)‖ ≤ (‖f 1‖+2*‖f 2‖+2*L)*ε := by
  have hNC : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
  let g : ℝ → ℂ := fun x => f (x / N)
  let gp : ℝ → ℂ := fun x => (N : ℂ)⁻¹ * f' (x / N)
  have hmap : ∀ x ∈ Icc N (2 * N), x / N ∈ Icc (1 : ℝ) 2 := by
    intro x hx
    exact ⟨(le_div_iff₀ hN).mpr (by simpa using hx.1),
      (div_le_iff₀ hN).mpr hx.2⟩
  have hg : ∀ x ∈ Icc N (2 * N), HasDerivAt g (gp x) x := by
    intro x hx
    have hh := (hf (x / N) (hmap x hx)).scomp x ((hasDerivAt_id x).div_const N)
    simpa only [g, gp, one_div, Complex.real_smul, Complex.ofReal_inv, Function.comp_def, id_eq] using hh
  have hgpc : ContinuousOn gp (Icc N (2 * N)) :=
    continuousOn_const.mul (hfc.comp (continuous_id.div_const N).continuousOn hmap)
  have hgp : IntervalIntegrable gp volume N (2 * N) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : N ≤ 2 * N)).mpr hgpc.integrableOn_Icc
  have hderiv : IntegrableOn (deriv g) (Icc N (2 * N)) :=
    hgpc.integrableOn_Icc.congr_fun (fun x hx => (hg x hx).deriv.symm) measurableSet_Icc
  have hg1 : g N = f 1 := by dsimp [g]; rw [div_self hN.ne']
  have hg2 : g (2 * N) = f 2 := by dsimp [g]; rw [mul_div_cancel_right₀ _ hN.ne']
  have hab := sum_mul_eq_sub_sub_integral_mul c hN.le (by linarith : N ≤ 2 * N)
    (fun x hx => (hg x hx).differentiableAt) hderiv
  rw [hg1, hg2,
    ← intervalIntegral.integral_of_le (by linarith : N ≤ 2 * N)] at hab
  have hdint : (∫ x in N..2 * N, deriv g x * primeProfileCum c x) =
      ∫ x in N..2 * N, gp x * primeProfileCum c x := by
    apply intervalIntegral.integral_congr
    intro x hx
    change deriv g x * primeProfileCum c x = gp x * primeProfileCum c x
    rw [(hg x (by simpa only [uIcc_of_le (by linarith : N ≤ 2 * N)] using hx)).deriv]
  change (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, g n * c n) =
    f 2 * primeProfileCum c (2*N)-f 1 * primeProfileCum c N-
      (∫ x in N..2 * N, deriv g x * primeProfileCum c x) at hab
  rw [hdint] at hab
  have hgA : IntervalIntegrable (fun x => gp x * primeProfileCum c x) volume N (2 * N) := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : N ≤ 2 * N)).mpr
    exact integrableOn_mul_sum_Icc c hN.le hgpc.integrableOn_Icc
  have hgl : IntervalIntegrable (fun x => gp x * (ell * (x : ℂ))) volume N (2 * N) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : N ≤ 2 * N)).mpr
      (hgpc.mul (continuous_const.mul Complex.continuous_ofReal).continuousOn).integrableOn_Icc
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := g) (u' := gp) (v := fun x : ℝ => (x : ℂ)) (v' := fun _ => (1 : ℂ))
    (fun x hx => hg x (by simpa only [uIcc_of_le (by linarith : N ≤ 2 * N)] using hx))
    (fun x _ => Complex.ofRealCLM.hasDerivAt) hgp (intervalIntegrable_const)
  simp only [mul_one, hg1, hg2] at hibp
  have hscale : (∫ x in N..2 * N, g x) = (N : ℂ) * ∫ x in (1 : ℝ)..2, f x := by
    dsimp only [g]
    rw [intervalIntegral.integral_comp_div _ hN.ne']
    simp only [div_self hN.ne', mul_div_cancel_right₀ _ hN.ne', Complex.real_smul]
  have hmain : (∫ x in N..2 * N, gp x * (ell * (x : ℂ))) =
      ell * (f 2 * ((2*N:ℝ):ℂ)-f 1*(N:ℂ)-(N:ℂ)*∫ x in (1:ℝ)..2,f x) := by
    simp_rw [show ∀ x : ℝ, gp x * (ell * (x : ℂ)) = ell * (gp x * (x : ℂ)) by intro x; ring]
    have he : (∫ x in N..2 * N, gp x * (x : ℂ)) =
        f 2 * ((2*N:ℝ):ℂ)-f 1*(N:ℂ)-(N:ℂ)*∫ x in (1:ℝ)..2,f x := by
      rw [hscale] at hibp
      linear_combination hibp
    rw [intervalIntegral.integral_const_mul, he]
  have hdiff : (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, g n * c n) -
      ell * (N : ℂ) * (∫ x in (1 : ℝ)..2, f x) =
      f 2*(primeProfileCum c (2*N)-ell*((2*N:ℝ):ℂ))-
      f 1*(primeProfileCum c N-ell*(N:ℂ))-
      (∫ x in N..2 * N, gp x * (primeProfileCum c x - ell * (x : ℂ))) := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub hgA hgl, hab, hmain]
    ring
  have hb (x : ℝ) (hx : x ∈ Icc N (2 * N)) :
      ‖gp x * (primeProfileCum c x - ell * (x : ℂ))‖ ≤ 2 * L * ε := by
    have hxn : 0 ≤ x := hN.le.trans hx.1
    rw [norm_mul]
    have hgpbound : ‖gp x‖ ≤ L / N := by
      dsimp only [gp]
      rw [norm_mul, norm_inv, Complex.norm_of_nonneg hN.le]
      calc
        _ ≤ N⁻¹ * L := mul_le_mul_of_nonneg_left (hfb _ (hmap x hx)) (inv_nonneg.mpr hN.le)
        _ = _ := by ring
    calc
      _ ≤ (L / N) * (ε * x) := mul_le_mul hgpbound (hA x hx) (norm_nonneg _) (by positivity)
      _ ≤ (L / N) * (ε * (2 * N)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hx.2 hε) (by positivity)
      _ = _ := by field_simp
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (C := 2 * L * ε) (fun x hx => hb x (by
      simpa only [uIcc_of_le (by linarith : N ≤ 2 * N)] using
        (show x ∈ uIcc N (2 * N) from uIoc_subset_uIcc hx)))
  have hwhole : ‖(∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, g n * c n) -
      ell * (N : ℂ) * (∫ x in (1 : ℝ)..2, f x)‖ ≤
      ((‖f 1‖+2*‖f 2‖+2*L)*ε)*N := by
    have hI : ‖∫ x in N..2*N,gp x*(primeProfileCum c x-ell*(x:ℂ))‖≤(2*L*ε)*N := by
      simpa only [show 2*N-N=N by ring,abs_of_pos hN] using hint
    have h1:=hA N ⟨le_rfl,by linarith⟩
    have h2:=hA (2*N) ⟨by linarith,le_rfl⟩
    rw [hdiff]
    calc
      _ ≤ ‖f 2*(primeProfileCum c (2*N)-ell*((2*N:ℝ):ℂ))‖+
          ‖f 1*(primeProfileCum c N-ell*(N:ℂ))‖+
          ‖∫ x in N..2*N,gp x*(primeProfileCum c x-ell*(x:ℂ))‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ ‖f 2‖*(ε*(2*N))+‖f 1‖*(ε*N)+(2*L*ε)*N := by
        simp only [norm_mul]
        gcongr
      _ = _ := by ring
  have heq : (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, f ((n : ℝ) / N) * c n) / (N : ℂ) -
      ell * (∫ x in (1 : ℝ)..2, f x) =
      ((∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, g n * c n) -
        ell * (N : ℂ) * (∫ x in (1 : ℝ)..2, f x)) / (N : ℂ) := by
    dsimp only [g]
    field_simp [hNC]
  rw [heq, norm_div, Complex.norm_of_nonneg hN.le]
  exact (div_le_iff₀ hN).mpr hwhole


/-- The actual frozen profile at the three-halves cubic resonance. -/
def primeGaussianThreeHalvesProfile (x : ℝ) : ℂ :=
  (bagPhysicalHeightWindow ((3/2:ℝ)*x) : ℂ) * smoothAFECutoff x

private theorem edge_profile_smooth : ContDiffOn ℝ 2 primeGaussianThreeHalvesProfile (Ioi (0:ℝ)) :=
  ((Complex.ofRealCLM.contDiff.comp (bagPhysicalHeightWindow.contDiff.comp
    (contDiff_const.mul contDiff_id))).contDiffOn).mul contDiffOn_smoothAFECutoff_pos

private theorem edge_profile_jet :
    (∀ x ∈ Icc (1:ℝ) 2, HasDerivAt primeGaussianThreeHalvesProfile
      (deriv primeGaussianThreeHalvesProfile x) x) ∧
    ContinuousOn primeGaussianThreeHalvesProfile (Icc (1:ℝ) 2) ∧
    ContinuousOn (deriv primeGaussianThreeHalvesProfile) (Icc (1:ℝ) 2) := by
  have hs : Icc (1:ℝ) 2 ⊆ Ioi (0:ℝ) := fun x hx => lt_of_lt_of_le (by norm_num) hx.1
  have hd : ContDiffOn ℝ 1 (deriv primeGaussianThreeHalvesProfile) (Ioi (0:ℝ)) :=
    edge_profile_smooth.deriv_of_isOpen isOpen_Ioi (by norm_num)
  exact ⟨fun x hx => (edge_profile_smooth.differentiableOn (by norm_num)).hasDerivAt
    (Ioi_mem_nhds (hs hx)), edge_profile_smooth.continuousOn.mono hs,
    hd.continuousOn.mono hs⟩

/-- One signed Fourier integration, including both boundary values. -/
theorem primeProfile_fourier_once
    (f f' : ℝ → ℂ) {B τ : ℝ} (hτ : τ≠0)
    (hf : ∀ x ∈ Icc (1:ℝ) 2, HasDerivAt f (f' x) x)
    (hc : ContinuousOn f' (Icc (1:ℝ) 2))
    (hB : ∀ x ∈ Icc (1:ℝ) 2, ‖f' x‖≤B) :
    ‖∫ x in (1:ℝ)..2, f x * bourgainOscillation (τ*x)‖ ≤
      (‖f 1‖+‖f 2‖+B)/|τ| := by
  let a : ℂ := (τ:ℂ)*I
  let e : ℝ → ℂ := fun x => bourgainOscillation (τ*x)
  have he (x:ℝ) : HasDerivAt e (a*e x) x := by
    have h := (((Complex.ofRealCLM.hasDerivAt (x:=x)).const_mul (τ:ℂ)).mul_const I).cexp
    simpa only [e,a,bourgainOscillation,Complex.ofReal_mul,Complex.ofRealCLM_apply,
      Complex.ofReal_one,mul_one,mul_assoc,mul_comm,mul_left_comm] using h
  have hec : Continuous e := continuous_iff_continuousAt.mpr (fun x => (he x).continuousAt)
  have hei : IntervalIntegrable (fun x => a*e x) volume 1 2 :=
    (continuous_const.mul hec).intervalIntegrable _ _
  have hfi : IntervalIntegrable f' volume 1 2 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mpr hc.integrableOn_Icc
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x hx => hf x (by simpa only [uIcc_of_le (by norm_num : (1:ℝ)≤2)] using hx))
    (fun x _ => he x) hfi hei
  have factor : (∫ x in (1:ℝ)..2, f x*(a*e x)) =
      a*(∫ x in (1:ℝ)..2,f x*e x) := by
    simp_rw [show ∀ x, f x*(a*e x)=a*(f x*e x) by intro x;ring]
    exact intervalIntegral.integral_const_mul _ _
  rw [factor] at h1
  have hn : ‖∫ x in (1:ℝ)..2,f' x*e x‖≤B := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (C:=B) (fun x hx => show ‖f' x*e x‖≤B from by
        rw [norm_mul,show ‖e x‖=1 from norm_bourgainOscillation _ ,mul_one]
        exact hB x (by simpa only [uIcc_of_le (by norm_num : (1:ℝ)≤2)] using
          (show x ∈ uIcc (1:ℝ) 2 from uIoc_subset_uIcc hx)))
    norm_num at hb ⊢
    exact hb
  have heq := congrArg norm h1
  rw [norm_mul,show ‖a‖=|τ| by simp [a,Complex.norm_real,Real.norm_eq_abs]] at heq
  have ht : ‖f 2*e 2-f 1*e 1-(∫ x in (1:ℝ)..2,f' x*e x)‖ ≤ ‖f 1‖+‖f 2‖+B := by
    calc
      _ ≤ ‖f 2*e 2‖+‖f 1*e 1‖+‖∫ x in (1:ℝ)..2,f' x*e x‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ ‖f 1‖+‖f 2‖+B := by
        simp only [norm_mul,show ‖e 1‖=1 from norm_bourgainOscillation _,
          show ‖e 2‖=1 from norm_bourgainOscillation _,mul_one]
        linarith
  exact (le_div_iff₀ (abs_pos.mpr hτ)).mpr (by rw [mul_comm,heq];exact ht)
private def edgeInvDenom (l x : ℝ) : ℂ := (1+(l:ℂ)*(Real.log x:ℂ))⁻¹
private def edgeLogProfile (l x : ℝ) : ℂ := primeGaussianThreeHalvesProfile x * edgeInvDenom l x
private def edgeLogProfileD (l x : ℝ) : ℂ :=
  deriv primeGaussianThreeHalvesProfile x * edgeInvDenom l x -
    primeGaussianThreeHalvesProfile x*(l:ℂ)*(x:ℂ)⁻¹*edgeInvDenom l x^2
private theorem edge_denom_pos {l x:ℝ} (hl:0≤l) (hx:1≤x) : 1≤1+l*Real.log x := by
  have := mul_nonneg hl (Real.log_nonneg hx)
  linarith

private theorem edge_inv_deriv {l x:ℝ} (hl:0≤l) (hx:1≤x) :
    HasDerivAt (edgeInvDenom l) (-(l:ℂ)*(x:ℂ)⁻¹*edgeInvDenom l x^2) x := by
  have hx0 : 0<x := by linarith
  have hd : (1+(l:ℂ)*(Real.log x:ℂ))≠0 := by
    have : (1+l*Real.log x:ℝ)≠0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (edge_denom_pos hl hx))
    exact_mod_cast this
  have hh := (((Real.hasDerivAt_log hx0.ne').ofReal_comp).const_mul (l:ℂ)).const_add 1
  have hi := hh.inv hd
  apply hi.congr_deriv
  simp only [edgeInvDenom,Complex.ofReal_inv,div_eq_mul_inv,inv_pow]
  ring

private theorem edge_log_profile_deriv {l x:ℝ} (hl:0≤l) (hx:x∈Icc (1:ℝ) 2) :
    HasDerivAt (edgeLogProfile l) (edgeLogProfileD l x) x := by
  have hh := (edge_profile_jet.1 x hx).mul (edge_inv_deriv hl hx.1)
  apply hh.congr_deriv
  dsimp only [edgeLogProfileD]
  ring


private theorem edge_log_profile_continuous (l:ℝ) (hl:0≤l) :
    ContinuousOn (edgeLogProfile l) (Icc (1:ℝ) 2) ∧
    ContinuousOn (edgeLogProfileD l) (Icc (1:ℝ) 2) := by
  have hi : ContinuousOn (edgeInvDenom l) (Icc (1:ℝ) 2) :=
    fun x hx => (edge_inv_deriv hl hx.1).continuousAt.continuousWithinAt
  have hxi : ContinuousOn (fun x:ℝ => (x:ℂ)⁻¹) (Icc (1:ℝ) 2) := by
    intro x hx
    exact (((Complex.ofRealCLM.hasDerivAt (x:=x)).inv
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le (by norm_num) hx.1)))).continuousAt).continuousWithinAt
  obtain ⟨_,hf,hf'⟩ := edge_profile_jet
  exact ⟨hf.mul hi, (hf'.mul hi).sub (((hf.mul continuousOn_const).mul hxi).mul (hi.pow 2))⟩
private theorem edge_inv_norm {l x:ℝ} (hl:0≤l) (hx:1≤x) : ‖edgeInvDenom l x‖≤1 := by
  have hd := edge_denom_pos hl hx
  rw [edgeInvDenom,norm_inv,show (1+(l:ℂ)*(Real.log x:ℂ))=((1+l*Real.log x:ℝ):ℂ) by push_cast;rfl,
    Complex.norm_of_nonneg (by linarith : 0≤1+l*Real.log x)]
  exact inv_le_one_of_one_le₀ hd

private theorem edge_log_profile_bounds :
    ∃ B:ℝ, 0<B ∧ ∀ l∈Icc (0:ℝ) 1, ∀ x∈Icc (1:ℝ) 2,
      ‖edgeLogProfile l x‖≤B ∧ ‖edgeLogProfileD l x‖≤2*B := by
  obtain ⟨_,hf,hf'⟩ := edge_profile_jet
  obtain ⟨B0,hB0⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  obtain ⟨B1,hB1⟩ := isCompact_Icc.exists_bound_of_continuousOn hf'
  let B := |B0|+|B1|+1
  have hB : 0<B := by dsimp [B];positivity
  refine ⟨B,hB,?_⟩
  intro l hl x hx
  have h0 : ‖primeGaussianThreeHalvesProfile x‖≤B := (hB0 x hx).trans (by dsimp [B]; nlinarith [le_abs_self B0,abs_nonneg B1])
  have h1 : ‖deriv primeGaussianThreeHalvesProfile x‖≤B := (hB1 x hx).trans (by dsimp [B]; nlinarith [le_abs_self B1,abs_nonneg B0])
  have hi := edge_inv_norm hl.1 hx.1
  have hlc : ‖(l:ℂ)‖≤1 := by rw [Complex.norm_of_nonneg hl.1];exact hl.2
  have hxi : ‖(x:ℂ)⁻¹‖≤1 := by
    rw [norm_inv,Complex.norm_of_nonneg (by linarith [hx.1])]
    exact inv_le_one_of_one_le₀ hx.1
  have hm0 : ‖primeGaussianThreeHalvesProfile x*edgeInvDenom l x‖≤B := by
    rw [norm_mul]; calc
      _ ≤ B*1 := mul_le_mul h0 hi (norm_nonneg _) hB.le
      _ = B := mul_one B
  have hterm (z:ℂ) (hz:‖z‖≤B) : ‖z*(l:ℂ)*(x:ℂ)⁻¹*edgeInvDenom l x^2‖≤B := by
    rw [norm_mul,norm_mul,norm_mul,norm_pow]
    calc
      _ ≤ B*1*1*1^2 := by gcongr
      _ = B := by ring
  have hm1 : ‖deriv primeGaussianThreeHalvesProfile x*edgeInvDenom l x‖≤B := by
    rw [norm_mul];calc
      _ ≤ B*1 := mul_le_mul h1 hi (norm_nonneg _) hB.le
      _ = B := mul_one B
  refine ⟨hm0, ?_⟩
  dsimp only [edgeLogProfileD]
  exact (norm_sub_le _ _).trans (by linarith [hterm _ h0])
private theorem edge_profile_unweight_sum {N:ℝ} (hN:1<N) (τ:ℝ) :
    (∑ q∈Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊,
      (edgeLogProfile (1/Real.log N) ((q:ℝ)/N)*bourgainOscillation (τ*((q:ℝ)/N)))*
        primeResidueLogCoefficient 1 0 q) =
    (Real.log N:ℂ)*∑ q∈primeProfileBand N,
      primeGaussianThreeHalvesProfile ((q:ℝ)/N)*bourgainOscillation (τ*((q:ℝ)/N)) := by
  rw [Finset.mul_sum,primeProfileBand,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hp:q.Prime
  · have hqN : N<(q:ℝ) := (Nat.floor_lt (by linarith : 0≤N)).mp (Finset.mem_Ioc.mp hq).1
    have hq0 : 0<(q:ℝ) := by linarith
    have hL : Real.log N≠0 := (Real.log_pos hN).ne'
    have hqL : Real.log (q:ℝ)≠0 := (Real.log_pos (hN.trans hqN)).ne'
    have hLC : (Real.log N:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hL
    have hqLC : (Real.log (q:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hqL
    simp only [primeResidueLogCoefficient,hp,Nat.mod_one,and_self,ite_true]
    dsimp only [edgeLogProfile,edgeInvDenom]
    rw [Real.log_div hq0.ne' (by linarith : N≠0)]
    push_cast only [Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_one]
    have hden : 1+1/(Real.log N:ℂ)*((Real.log (q:ℝ):ℂ)-(Real.log N:ℂ)) =
        (Real.log (q:ℝ):ℂ)/(Real.log N:ℂ) := by field_simp;ring
    rw [hden,inv_div]
    field_simp [hqLC]
  · simp [primeResidueLogCoefficient,hp]

private theorem edge_osc_deriv (τ x:ℝ) :
    HasDerivAt (fun y => bourgainOscillation (τ*y))
      (((τ:ℂ)*I)*bourgainOscillation (τ*x)) x := by
  have h := (((Complex.ofRealCLM.hasDerivAt (x:=x)).const_mul (τ:ℂ)).mul_const I).cexp
  simpa only [bourgainOscillation,Complex.ofReal_mul,Complex.ofRealCLM_apply,Complex.ofReal_one,mul_one,mul_assoc,mul_comm,mul_left_comm] using h

private theorem edge_osc_continuous (τ:ℝ) : Continuous (fun x => bourgainOscillation (τ*x)) :=
  continuous_iff_continuousAt.mpr (fun x => (edge_osc_deriv τ x).continuousAt)

/-- Uniform signed Fourier control for the actual three-halves resonance profile.
The nonzero lower band boundary and the exact prime logarithmic weight are retained. -/
theorem exists_primeGaussianThreeHalvesProfile_fourier_bound :
    ∃ C:ℝ, 0<C ∧ ∀ᶠ N:ℝ in atTop, ∀ τ:ℝ, τ≠0 →
      ‖∑ q∈primeProfileBand N,
        primeGaussianThreeHalvesProfile ((q:ℝ)/N)*bourgainOscillation (τ*((q:ℝ)/N))‖ ≤
        C*N/Real.log N*(1/|τ|+(1+|τ|)/(Real.log N)^12) := by
  obtain ⟨B,hB,hbound⟩ := edge_log_profile_bounds
  refine ⟨9*B,by positivity,?_⟩
  filter_upwards [eventually_primeProfileCum_log_error 12,eventually_gt_atTop (1:ℝ)] with N hN hN1
  intro τ hτ
  let l:ℝ := 1/Real.log N
  have hL : 0<Real.log N := by linarith [hN.1]
  have hl : l∈Icc (0:ℝ) 1 := ⟨by dsimp [l];positivity,by
    dsimp [l];exact (div_le_one hL).mpr hN.1.le⟩
  let f : ℝ→ℂ := fun x => edgeLogProfile l x*bourgainOscillation (τ*x)
  let f' : ℝ→ℂ := fun x => edgeLogProfileD l x*bourgainOscillation (τ*x)+
    edgeLogProfile l x*(((τ:ℂ)*I)*bourgainOscillation (τ*x))
  have hderiv : ∀ x∈Icc (1:ℝ) 2, HasDerivAt f (f' x) x :=
    fun x hx => (edge_log_profile_deriv hl.1 hx).mul (edge_osc_deriv τ x)
  have hfc : ContinuousOn f' (Icc (1:ℝ) 2) :=
    ((edge_log_profile_continuous l hl.1).2.mul (edge_osc_continuous τ).continuousOn).add
      ((edge_log_profile_continuous l hl.1).1.mul (continuousOn_const.mul (edge_osc_continuous τ).continuousOn))
  have hbd : ∀ x∈Icc (1:ℝ) 2, ‖f' x‖≤3*B*(1+|τ|) := by
    intro x hx
    obtain ⟨hg,hg'⟩ := hbound l hl x hx
    have hn := norm_add_le (edgeLogProfileD l x*bourgainOscillation (τ*x))
      (edgeLogProfile l x*(((τ:ℂ)*I)*bourgainOscillation (τ*x)))
    simp only [norm_mul,norm_bourgainOscillation,norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs] at hn
    dsimp only [f']
    exact hn.trans (by nlinarith [abs_nonneg τ,mul_le_mul_of_nonneg_right hg (abs_nonneg τ)])
  have hab := primeProfile_scaledAbel_error (primeResidueLogCoefficient 1 0) f f' 1
    (by linarith : 0<N) (by positivity : 0≤3*B*(1+|τ|))
    (by positivity : 0≤1/(Real.log N)^12) hderiv hfc hbd
    (fun x hx => by simpa [one_mul,one_div,mul_comm,mul_left_comm,mul_assoc,div_eq_mul_inv] using hN.2 x hx.1)
  have hend (x:ℝ) (hx:x∈Icc (1:ℝ) 2) : ‖f x‖≤B := by
    dsimp only [f]
    rw [norm_mul,norm_bourgainOscillation,mul_one]
    exact (hbound l hl x hx).1
  have hfour0 := primeProfile_fourier_once (edgeLogProfile l) (edgeLogProfileD l) hτ
    (fun x hx => edge_log_profile_deriv hl.1 hx)
    (edge_log_profile_continuous l hl.1).2
    (fun x hx => (hbound l hl x hx).2)
  have hfour : ‖∫ x in (1:ℝ)..2, f x‖≤4*B/|τ| := by
    exact hfour0.trans (div_le_div_of_nonneg_right
      (by linarith [(hbound l hl 1 (by constructor <;> norm_num)).1,
        (hbound l hl 2 (by constructor <;> norm_num)).1]) (abs_nonneg τ))
  have hab' : ‖(∑ q∈Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊, f ((q:ℝ)/N)*
      primeResidueLogCoefficient 1 0 q)/(N:ℂ)-1*(∫ x in (1:ℝ)..2,f x)‖≤
        9*B*(1+|τ|)*(1/(Real.log N)^12) := by
    exact hab.trans (mul_le_mul_of_nonneg_right
      (by nlinarith [hend 1 (by constructor <;> norm_num),
        hend 2 (by constructor <;> norm_num),mul_nonneg hB.le (abs_nonneg τ)])
      (by positivity))
  let S := ∑ q∈primeProfileBand N, primeGaussianThreeHalvesProfile ((q:ℝ)/N)*bourgainOscillation (τ*((q:ℝ)/N))
  have hu := edge_profile_unweight_sum hN1 τ
  change _=(Real.log N:ℂ)*S at hu
  change ‖(∑ q∈Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊,
    (edgeLogProfile (1/Real.log N) ((q:ℝ)/N)*bourgainOscillation (τ*((q:ℝ)/N)))*
      primeResidueLogCoefficient 1 0 q)/(N:ℂ)-1*(∫ x in (1:ℝ)..2,f x)‖≤_ at hab'
  rw [hu,one_mul] at hab'
  have hsum := (norm_le_norm_sub_add ((Real.log N:ℂ)*S/(N:ℂ)) (∫ x in (1:ℝ)..2,f x)).trans
    (add_le_add hab' hfour)
  rw [norm_div,norm_mul,Complex.norm_of_nonneg hL.le,Complex.norm_of_nonneg (by linarith : 0≤N)] at hsum
  have hNN : N≠0 := by linarith
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hL).mpr
  have hh := (div_le_iff₀ (by linarith : 0<N)).mp hsum
  dsimp only [S] at hh
  calc
    _ = Real.log N * ‖S‖ := by ring
    _ ≤ (9*B*(1+|τ|)*(1/Real.log N^12)+4*B/|τ|)*N := hh
    _ ≤ (9*B*(1+|τ|)*(1/Real.log N^12)+9*B/|τ|)*N := by gcongr; linarith
    _ = _ := by ring

private def halfRowFrequency (N : ℝ) (p r : ℕ) : ℝ :=
  Real.pi*(2*(p:ℝ)-3*r)*N/r

private def halfRowFactor (N : ℝ) (p r : ℕ) : ℂ :=
  -((2*Real.pi:ℂ)*smoothAFECutoff ((p:ℝ)/N)*
    (starRingEnd ℂ) (smoothAFECutoff ((r:ℝ)/N))/(r:ℂ))

private def halfRowFlatEntry (N : ℝ) (p q r : ℕ) : ℂ :=
  halfRowFactor N p r * primeGaussianThreeHalvesProfile ((q:ℝ)/N) *
    bourgainOscillation (halfRowFrequency N p r*((q:ℝ)/N))

private theorem half_row_phase {N : ℝ} (hN : N≠0) (p : ℕ) {q r : ℕ}
    (hq : q.Prime) (hq2 : q≠2) (hr : (r:ℝ)≠0) :
    bourgainOscillation (2*Real.pi*((p:ℝ)*q/r)) =
      -bourgainOscillation (halfRowFrequency N p r*((q:ℝ)/N)) := by
  have he : 2*Real.pi*((p:ℝ)*q/r) =
      halfRowFrequency N p r*((q:ℝ)/N)+3*Real.pi*q := by
    dsimp [halfRowFrequency]
    field_simp
    ring
  obtain ⟨n,hn⟩ := hq.odd_of_ne_two hq2
  have hi : bourgainOscillation (3*Real.pi*q) = -1 := by
    unfold bourgainOscillation
    have heq : I*((3*Real.pi*q:ℝ):ℂ) = Real.pi*I+((3*n+1:ℕ):ℂ)*(2*Real.pi*I) := by
      rw [hn]
      push_cast
      ring
    rw [heq,Complex.exp_add,Complex.exp_pi_mul_I,Complex.exp_nat_mul_two_pi_mul_I,mul_one]
  rw [he]
  unfold bourgainOscillation at hi ⊢
  rw [Complex.ofReal_add,mul_add,Complex.exp_add,hi,mul_neg_one]

private theorem half_row_factor_norm {N : ℝ} (hN : 0<N) {p r : ℕ}
    (hp : p∈primeProfileBand N) (hr : r∈primeProfileBand N) :
    ‖halfRowFactor N p r‖ ≤ 8/N := by
  obtain ⟨_,hpN,_⟩ := primeProfileBand_mem hN.le hp
  obtain ⟨_,hrN,_⟩ := primeProfileBand_mem hN.le hr
  have hr0 : (0:ℝ)<r := hN.trans hrN
  have hpn := norm_smoothAFECutoff_le_one (div_pos (hN.trans hpN) hN)
  have hrn := norm_smoothAFECutoff_le_one (div_pos hr0 hN)
  dsimp [halfRowFactor]
  rw [norm_neg,norm_div,norm_mul,norm_mul,Complex.norm_conj,
    show (2*↑Real.pi:ℂ)=((2*Real.pi:ℝ):ℂ) by push_cast;rfl,
    Complex.norm_of_nonneg (by positivity : 0≤2*Real.pi),Complex.norm_natCast]
  calc
    _ ≤ (2*Real.pi)*1*1/r := by gcongr
    _ ≤ 8/N := by
      apply (div_le_div_iff₀ hr0 hN).mpr
      nlinarith [Real.pi_lt_four]

private theorem half_row_profile_norm {x : ℝ} (hx : 0<x) :
    ‖primeGaussianThreeHalvesProfile x‖≤1 := by
  rw [primeGaussianThreeHalvesProfile,norm_mul,Complex.norm_of_nonneg bagPhysicalHeightWindow.nonneg]
  exact (mul_le_mul bagPhysicalHeightWindow.le_one (norm_smoothAFECutoff_le_one hx)
    (norm_nonneg _) (by norm_num)).trans_eq (by ring)

private theorem half_row_window_lipschitz :
    ∃ L:ℝ, 0<L ∧ ∀ x∈Icc (0:ℝ) 4, ∀ y∈Icc (0:ℝ) 4,
      |bagPhysicalHeightWindow y-bagPhysicalHeightWindow x|≤L*|y-x| := by
  have hc : Continuous (deriv (fun x:ℝ => bagPhysicalHeightWindow x)) :=
    (bagPhysicalHeightWindow.contDiff (n:=1)).continuous_deriv_one
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨|B|+1,by positivity,?_⟩
  intro x hx y hy
  have hb : ∀ t∈Icc (0:ℝ) 4, ‖deriv (fun x:ℝ => bagPhysicalHeightWindow x) t‖≤|B|+1 :=
    fun t ht => (hB t ht).trans (by linarith [le_abs_self B])
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun t _ => (bagPhysicalHeightWindow.contDiff (n:=1)).differentiable (by norm_num) t)
      hb (convex_Icc (0:ℝ) 4) hx hy

private theorem half_row_window_error {N L:ℝ} (hN : 0<N) (hL : 0≤L)
    (hLip : ∀ x∈Icc (0:ℝ) 4, ∀ y∈Icc (0:ℝ) 4,
      |bagPhysicalHeightWindow y-bagPhysicalHeightWindow x|≤L*|y-x|)
    {p q r:ℕ} (hp:p∈primeProfileBand N) (hq:q∈primeProfileBand N)
    (hr:r∈primeProfileBand N) :
    |bagPhysicalHeightWindow ((p:ℝ)*q/((r:ℝ)*N))-
      bagPhysicalHeightWindow ((3/2:ℝ)*((q:ℝ)/N))|≤2*L*|2*(p:ℝ)-3*r|/N := by
  obtain ⟨_,hpN,hp2⟩ := primeProfileBand_mem hN.le hp
  obtain ⟨_,hqN,hq2⟩ := primeProfileBand_mem hN.le hq
  obtain ⟨_,hrN,hr2⟩ := primeProfileBand_mem hN.le hr
  have hr0 : (0:ℝ)<r := hN.trans hrN
  have hq0 : (0:ℝ)<q := hN.trans hqN
  have hx : (3/2:ℝ)*((q:ℝ)/N) ∈ Icc (0:ℝ) 4 := by
    refine ⟨by positivity,?_⟩
    have hqdiv := (div_le_iff₀ hN).mpr hq2
    linarith
  have hy : (p:ℝ)*q/((r:ℝ)*N) ∈ Icc (0:ℝ) 4 := by
    refine ⟨by positivity,(div_le_iff₀ (mul_pos hr0 hN)).mpr ?_⟩
    have hm := mul_le_mul hp2 hq2 hq0.le (by positivity : 0≤2*N)
    nlinarith
  have he : (p:ℝ)*q/((r:ℝ)*N)-(3/2:ℝ)*((q:ℝ)/N) = (2*(p:ℝ)-3*r)*q/(2*((r:ℝ)*N)) := by
    field_simp
  have hd : |(p:ℝ)*q/((r:ℝ)*N)-(3/2:ℝ)*((q:ℝ)/N)|≤2*|2*(p:ℝ)-3*r|/N := by
    rw [he,abs_div,abs_mul,abs_of_pos hq0,abs_of_pos (by positivity : 0<2*((r:ℝ)*N))]
    apply (div_le_div_iff₀ (by positivity : 0<2*((r:ℝ)*N)) hN).mpr
    have hh : (q:ℝ)≤2*r := by linarith
    have hm := mul_le_mul_of_nonneg_left hh (abs_nonneg (2*(p:ℝ)-3*r))
    nlinarith [mul_le_mul_of_nonneg_right hm hN.le]
  exact (hLip _ hx _ hy).trans ((mul_le_mul_of_nonneg_left hd hL).trans_eq (by ring))

private theorem half_row_flat_error {N L:ℝ} (hN : 2<N) (hL : 0≤L)
    (hLip : ∀ x∈Icc (0:ℝ) 4, ∀ y∈Icc (0:ℝ) 4,
      |bagPhysicalHeightWindow y-bagPhysicalHeightWindow x|≤L*|y-x|)
    {p q r:ℕ} (hp:p∈primeProfileBand N) (hq:q∈primeProfileBand N)
    (hr:r∈primeProfileBand N) :
    ‖primeGaussianCubicMainEntry N p q r-halfRowFlatEntry N p q r‖≤
      16*L*|2*(p:ℝ)-3*r|/N^2 := by
  have hN0 : 0<N := by linarith
  have hqP := (primeProfileBand_mem hN0.le hq).1
  have hq2 : q≠2 := by
    have hh := (primeProfileBand_mem hN0.le hq).2.1
    intro heq
    subst q
    norm_num at hh
    linarith
  have hr0 : (0:ℝ)<r := hN0.trans (primeProfileBand_mem hN0.le hr).2.1
  have hq0 : (0:ℝ)<q := hN0.trans (primeProfileBand_mem hN0.le hq).2.1
  have he : primeGaussianCubicMainEntry N p q r-halfRowFlatEntry N p q r =
    halfRowFactor N p r*smoothAFECutoff ((q:ℝ)/N)*
      ((bagPhysicalHeightWindow ((p:ℝ)*q/((r:ℝ)*N))-
        bagPhysicalHeightWindow ((3/2:ℝ)*((q:ℝ)/N)):ℝ):ℂ)*
      bourgainOscillation (halfRowFrequency N p r*((q:ℝ)/N)) := by
    dsimp [primeGaussianCubicMainEntry,halfRowFlatEntry,primeGaussianThreeHalvesProfile]
    rw [half_row_phase hN0.ne' p hqP hq2 hr0.ne']
    dsimp [halfRowFactor]
    push_cast
    ring
  rw [he,norm_mul,norm_mul,norm_mul,norm_bourgainOscillation,mul_one,
    Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ (8/N)*1*(2*L*|2*(p:ℝ)-3*r|/N) := by
      exact mul_le_mul (mul_le_mul (half_row_factor_norm hN0 hp hr)
        (norm_smoothAFECutoff_le_one (div_pos hq0 hN0)) (norm_nonneg _) (by positivity))
        (half_row_window_error hN0 hL hLip hp hq hr) (abs_nonneg _) (by positivity)
    _ = _ := by ring

private theorem half_row_flat_norm {N:ℝ} (hN:0<N) {p q r:ℕ}
    (hp:p∈primeProfileBand N) (hq:q∈primeProfileBand N) (hr:r∈primeProfileBand N) :
    ‖halfRowFlatEntry N p q r‖≤8/N := by
  dsimp [halfRowFlatEntry]
  rw [norm_mul,norm_mul,norm_bourgainOscillation,mul_one]
  exact (mul_le_mul (half_row_factor_norm hN hp hr)
    (half_row_profile_norm (div_pos (hN.trans (primeProfileBand_mem hN.le hq).2.1) hN))
    (norm_nonneg _) (by positivity)).trans_eq (mul_one _)

private theorem half_row_physical_to_fourier :
    ∃ C:ℝ, 0<C ∧ ∀ N:ℝ, 2<N → ∀ p∈primeProfileBand N, ∀ r∈primeProfileBand N,
      ‖primeGaussianCubicCompleteRow N p r‖ ≤
        (8/N)*‖∑ q∈primeProfileBand N,
          primeGaussianThreeHalvesProfile ((q:ℝ)/N)*
            bourgainOscillation (halfRowFrequency N p r*((q:ℝ)/N))‖ +
        C*(1+|2*(p:ℝ)-3*r|)/(N*Real.log N)+8/N := by
  obtain ⟨Cp,hCp,hphysical⟩ := exists_primeGaussianCubic_entry_error
  obtain ⟨L,hL,hLip⟩ := half_row_window_lipschitz
  let A:ℝ := 2*Real.log 4
  have hA : 0<A := by dsimp [A];positivity
  refine ⟨(Cp+16*L)*A,by positivity,?_⟩
  intro N hN p hp r hr
  have hN0 : 0<N := by linarith
  have hN1 : 1<N := by linarith
  have hlog : 0<Real.log N := Real.log_pos hN1
  let d:ℝ := |2*(p:ℝ)-3*r|
  let E:ℝ := (Cp+16*L)*(1+d)/N^2
  let V:ℕ→ℂ := fun q => primeGaussianCubicCoefficient N p q r*primeGaussianCubicKernel N p q r
  let F:ℕ→ℂ := fun q => halfRowFlatEntry N p q r
  let D:ℕ→ℂ := fun q => if q=r then 0 else V q-F q
  have hE : 0≤E := by dsimp [E,d];positivity
  have hd (q:ℕ) (hq:q∈primeProfileBand N) : ‖D q‖≤E := by
    dsimp only [D]
    split_ifs with heq
    · simpa only [norm_zero] using hE
    · have he := (norm_sub_le_norm_sub_add_norm_sub (V q)
          (primeGaussianCubicMainEntry N p q r) (F q)).trans
        (add_le_add (hphysical N hN1 p hp q hq r hr)
          (half_row_flat_error hN hL.le hLip hp hq hr))
      refine he.trans ?_
      dsimp only [E,d]
      rw [←add_div]
      apply div_le_div_of_nonneg_right _ (sq_nonneg N)
      nlinarith [abs_nonneg (2*(p:ℝ)-3*r)]
  have hident : primeGaussianCubicCompleteRow N p r =
      (∑ q∈primeProfileBand N,D q)+(∑ q∈primeProfileBand N,F q)-F r := by
    have hpoint (q:ℕ) : (if q=r then 0 else V q)=D q+F q-(if q=r then F r else 0) := by
      dsimp [D]
      split_ifs with h <;> simp [h]
    change (∑ q∈primeProfileBand N,if q=r then 0 else V q)=_
    simp_rw [hpoint]
    simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq']
    simp only [hr,ite_true]
  have hD : ‖∑ q∈primeProfileBand N,D q‖≤(primeProfileBand N).card*E := by
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum hd).trans_eq (by simp))
  have hcount : (primeProfileBand N).card*E≤(Cp+16*L)*A*(1+d)/(N*Real.log N) := by
    have hc := primeProfileBand_card_log_le hN1
    change (primeProfileBand N).card*Real.log N≤A*N at hc
    have hm := mul_le_mul_of_nonneg_right hc
      (show 0≤(Cp+16*L)*(1+d) by dsimp [d];positivity)
    dsimp [E]
    apply (le_div_iff₀ (mul_pos hN0 hlog)).mpr
    field_simp [hN0.ne']
    nlinarith
  have hF : ‖∑ q∈primeProfileBand N,F q‖≤
      (8/N)*‖∑ q∈primeProfileBand N,primeGaussianThreeHalvesProfile ((q:ℝ)/N)*
        bourgainOscillation (halfRowFrequency N p r*((q:ℝ)/N))‖ := by
    simp only [F,halfRowFlatEntry,mul_assoc,←Finset.mul_sum,norm_mul]
    exact mul_le_mul_of_nonneg_right (half_row_factor_norm hN0 hp hr) (norm_nonneg _)
  rw [hident]
  exact (norm_sub_le _ _).trans ((add_le_add
    ((norm_add_le _ _).trans (add_le_add (hD.trans hcount) hF))
    (half_row_flat_norm hN0 hp hr hr)).trans_eq (by dsimp [d];ring))

private theorem half_row_frequency_bounds {N:ℝ} (hN:0<N) {p r:ℕ}
    (hr:r∈primeProfileBand N) :
    |2*(p:ℝ)-3*r| ≤ |halfRowFrequency N p r| ∧
      |halfRowFrequency N p r| ≤8*|2*(p:ℝ)-3*r| := by
  obtain ⟨_,hrN,hr2⟩ := primeProfileBand_mem hN.le hr
  have hr0 : (0:ℝ)<r := hN.trans hrN
  have he : |halfRowFrequency N p r|=Real.pi*|2*(p:ℝ)-3*r| *N/r := by
    dsimp [halfRowFrequency]
    rw [abs_div,abs_mul,abs_mul,abs_of_pos Real.pi_pos,
      abs_of_pos hN,abs_of_pos hr0]
  rw [he]
  have hd := abs_nonneg (2*(p:ℝ)-3*r)
  constructor
  · apply (le_div_iff₀ hr0).mpr
    have h1 := mul_le_mul_of_nonneg_left hr2 hd
    have h2 := mul_le_mul_of_nonneg_right (le_of_lt Real.pi_gt_three) (mul_nonneg hd hN.le)
    nlinarith
  · apply (div_le_iff₀ hr0).mpr
    have h1 := mul_le_mul_of_nonneg_left hrN.le hd
    have h2 := mul_le_mul_of_nonneg_right (le_of_lt Real.pi_lt_four) (mul_nonneg hd hN.le)
    nlinarith

/-- Complete actual noncontracting q-rows have a uniform signed bound.
Every prime q in the original band and both physical kernel errors are accounted for. -/
theorem exists_primeGaussianCubicCompleteRow_half_resonance_bound :
    ∃ C:ℝ, 0<C ∧ ∀ᶠ N:ℝ in atTop, ∀ p∈primeProfileBand N, ∀ r∈primeProfileBand N,
      ‖primeGaussianCubicCompleteRow N p r‖ ≤
        C/Real.log N*(1/|2*(p:ℝ)-3*r|+(1+|2*(p:ℝ)-3*r|)/(Real.log N)^12+
          (1+|2*(p:ℝ)-3*r|)/N)+C/N := by
  obtain ⟨Cf,hCf,hfour⟩ := exists_primeGaussianThreeHalvesProfile_fourier_bound
  obtain ⟨Cp,hCp,hrow⟩ := half_row_physical_to_fourier
  let C:ℝ := 64*Cf+Cp+8
  have hC : 0<C := by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [hfour,eventually_gt_atTop (2:ℝ)] with N hf hN
  intro p hp r hr
  have hN0 : 0<N := by linarith
  have hL : 0<Real.log N := Real.log_pos (by linarith : 1<N)
  let d:ℝ := |2*(p:ℝ)-3*r|
  have hd : 0<d := by
    apply abs_pos.mpr
    intro heq
    have hrP := (primeProfileBand_mem hN0.le hr).1
    have hrN := (primeProfileBand_mem hN0.le hr).2.1
    have hr2 : r≠2 := by intro hh;subst r;norm_num at hrN;linarith
    obtain ⟨j,hj⟩ := hrP.odd_of_ne_two hr2
    have hz : 2*(p:ℝ)=3*r := sub_eq_zero.mp heq
    have hzN : 2*p=3*r := by exact_mod_cast hz
    omega
  obtain ⟨hτl,hτu⟩ := half_row_frequency_bounds (p:=p) hN0 hr
  have hτ : halfRowFrequency N p r≠0 := abs_pos.mp (hd.trans_le hτl)
  have hInv : 1/|halfRowFrequency N p r|≤1/d :=
    one_div_le_one_div_of_le hd hτl
  have hterm : 1/|halfRowFrequency N p r|+
      (1+|halfRowFrequency N p r|)/(Real.log N)^12 ≤
      8*(1/d+(1+d)/(Real.log N)^12) := by
    have hfreq : (1+|halfRowFrequency N p r|)/(Real.log N)^12≤
        8*(1+d)/(Real.log N)^12 :=
      div_le_div_of_nonneg_right (by change _≤8*(1+d);dsimp [d];linarith)
        (pow_nonneg hL.le 12)
    have hi0 : 0≤1/d := by positivity
    rw [show 8*(1+d)/(Real.log N)^12 = 8*((1+d)/(Real.log N)^12) by ring] at hfreq
    linarith
  have hFourier : (8/N)*‖∑ q∈primeProfileBand N,primeGaussianThreeHalvesProfile ((q:ℝ)/N)*
      bourgainOscillation (halfRowFrequency N p r*((q:ℝ)/N))‖ ≤
      (64*Cf/Real.log N)*(1/d+(1+d)/(Real.log N)^12) := by
    calc
      _ ≤ (8/N)*(Cf*N/Real.log N*(1/|halfRowFrequency N p r|+
        (1+|halfRowFrequency N p r|)/(Real.log N)^12)) :=
          mul_le_mul_of_nonneg_left (hf _ hτ) (by positivity)
      _ ≤ (8/N)*(Cf*N/Real.log N*(8*(1/d+(1+d)/(Real.log N)^12))) := by gcongr
      _ = _ := by field_simp;ring
  have hcmp : 64*Cf/Real.log N≤C/Real.log N := by
    apply div_le_div_of_nonneg_right _ hL.le
    dsimp [C];linarith
  have hcmpP : Cp/Real.log N≤C/Real.log N := by
    apply div_le_div_of_nonneg_right _ hL.le
    dsimp [C];linarith
  have hcmp8 : 8/N≤C/N := by
    apply div_le_div_of_nonneg_right _ hN0.le
    dsimp [C];linarith
  have hterm0 : 0≤1/d+(1+d)/(Real.log N)^12 := by positivity
  calc
    _ ≤ (8/N)*‖∑ q∈primeProfileBand N,primeGaussianThreeHalvesProfile ((q:ℝ)/N)*
        bourgainOscillation (halfRowFrequency N p r*((q:ℝ)/N))‖+
        Cp*(1+d)/(N*Real.log N)+8/N := hrow N hN p hp r hr
    _ ≤ (64*Cf/Real.log N)*(1/d+(1+d)/(Real.log N)^12)+
        Cp*(1+d)/(N*Real.log N)+8/N := by gcongr
    _ = (64*Cf/Real.log N)*(1/d+(1+d)/(Real.log N)^12)+
        (Cp/Real.log N)*((1+d)/N)+8/N := by ring
    _ ≤ (C/Real.log N)*(1/d+(1+d)/(Real.log N)^12)+
        (C/Real.log N)*((1+d)/N)+C/N := by
          exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hcmp hterm0)
            (mul_le_mul_of_nonneg_right hcmpP (by positivity))) hcmp8
    _ = _ := by dsimp [d];ring


end RHTower
