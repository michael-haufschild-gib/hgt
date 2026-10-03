import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicHalfResonance
import GaloisForLFunctions.RHTower.PrimeProgressionPowerLog

/-!
# Actual Gaussian prime profiles with growing frequencies

The full moving physical window is retained uniformly over the physical ratio
interval. Quantitative prime progression error supplies the Abel input; all
endpoints, the exact logarithmic weight and the signed integral main remain.
-/

noncomputable section
open Complex MeasureTheory Set Filter Finset
open scoped Topology
namespace RHTower
open GaloisForLFunctions.RHTower

/-- The actual physical window at a varying prime ratio, with its Gaussian cutoff. -/
def primeGaussianScaledProfile (ξ x : ℝ) : ℂ :=
  (bagPhysicalHeightWindow (ξ*x) : ℂ) * smoothAFECutoff x

private theorem scaled_profile_smooth (ξ : ℝ) :
    ContDiffOn ℝ 2 (primeGaussianScaledProfile ξ) (Ioi (0:ℝ)) :=
  ((Complex.ofRealCLM.contDiff.comp (bagPhysicalHeightWindow.contDiff.comp
    (contDiff_const.mul contDiff_id))).contDiffOn).mul contDiffOn_smoothAFECutoff_pos

private theorem scaled_profile_jet (ξ : ℝ) :
    (∀ x ∈ Icc (1:ℝ) 2, HasDerivAt (primeGaussianScaledProfile ξ)
      (deriv (primeGaussianScaledProfile ξ) x) x) ∧
    ContinuousOn (primeGaussianScaledProfile ξ) (Icc (1:ℝ) 2) ∧
    ContinuousOn (deriv (primeGaussianScaledProfile ξ)) (Icc (1:ℝ) 2) := by
  have hs : Icc (1:ℝ) 2 ⊆ Ioi (0:ℝ) := fun x hx => lt_of_lt_of_le (by norm_num) hx.1
  have hd : ContDiffOn ℝ 1 (deriv (primeGaussianScaledProfile ξ)) (Ioi (0:ℝ)) :=
    (scaled_profile_smooth ξ).deriv_of_isOpen isOpen_Ioi (by norm_num)
  exact ⟨fun x hx => ((scaled_profile_smooth ξ).differentiableOn (by norm_num)).hasDerivAt
    (Ioi_mem_nhds (hs hx)), (scaled_profile_smooth ξ).continuousOn.mono hs,
    hd.continuousOn.mono hs⟩

private theorem scaled_profile_norm (ξ : ℝ) {x : ℝ} (hx : 0<x) :
    ‖primeGaussianScaledProfile ξ x‖≤1 := by
  rw [primeGaussianScaledProfile,norm_mul,Complex.norm_of_nonneg bagPhysicalHeightWindow.nonneg]
  exact (mul_le_mul bagPhysicalHeightWindow.le_one (norm_smoothAFECutoff_le_one hx)
    (norm_nonneg _) (by norm_num)).trans_eq (by ring)

private theorem scaled_profile_bounds :
    ∃ B:ℝ, 0<B ∧ ∀ ξ∈Icc (1/2:ℝ) 2, ∀ x∈Icc (1:ℝ) 2,
      ‖primeGaussianScaledProfile ξ x‖≤B ∧ ‖deriv (primeGaussianScaledProfile ξ) x‖≤B := by
  have hWc : Continuous (deriv (fun y:ℝ => bagPhysicalHeightWindow y)) :=
    (bagPhysicalHeightWindow.contDiff (n:=1)).continuous_deriv_one
  have hVc : ContinuousOn (deriv smoothAFECutoff) (Icc (1:ℝ) 2) := by
    have hs : Icc (1:ℝ) 2 ⊆ Ioi (0:ℝ) := fun x hx => lt_of_lt_of_le (by norm_num) hx.1
    have hd : ContDiffOn ℝ 1 (deriv smoothAFECutoff) (Ioi (0:ℝ)) :=
      contDiffOn_smoothAFECutoff_pos.deriv_of_isOpen isOpen_Ioi (by norm_num)
    exact hd.continuousOn.mono hs
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hWc.continuousOn : ContinuousOn (deriv (fun y:ℝ => bagPhysicalHeightWindow y)) (Icc (0:ℝ) 4))
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hVc
  let B := 2*|M|+|D|+1
  have hB : 0<B := by dsimp [B];positivity
  have hB1 : 1≤B := by dsimp [B];linarith [abs_nonneg M,abs_nonneg D]
  refine ⟨B,hB,fun ξ hξ x hx => ⟨(scaled_profile_norm ξ (by linarith only [hx.1])).trans hB1,?_⟩⟩
  have hx0 : 0<x := by linarith only [hx.1]
  have hξ0 : 0≤ξ := by linarith only [hξ.1]
  have hξx : ξ*x∈Icc (0:ℝ) 4 := ⟨mul_nonneg hξ0 hx0.le, by
    exact (mul_le_mul hξ.2 hx.2 hx0.le (by norm_num)).trans_eq (by norm_num)⟩
  have hW := ((bagPhysicalHeightWindow.contDiff (n:=1)).differentiable (by norm_num) (ξ*x)).hasDerivAt
  have hV := (contDiffOn_smoothAFECutoff_pos.differentiableOn (by norm_num)).hasDerivAt (Ioi_mem_nhds hx0)
  have hd : HasDerivAt (primeGaussianScaledProfile ξ)
      (((deriv (fun y:ℝ => bagPhysicalHeightWindow y) (ξ*x)*ξ : ℝ):ℂ)*smoothAFECutoff x+
        (bagPhysicalHeightWindow (ξ*x):ℂ)*deriv smoothAFECutoff x) x := by
    simpa only [primeGaussianScaledProfile,Function.comp_def,Pi.mul_apply,mul_one] using!
      (((hW.comp x ((hasDerivAt_id x).const_mul ξ)).ofReal_comp).mul hV)
  have hw : |deriv (fun y:ℝ => bagPhysicalHeightWindow y) (ξ*x)|≤|M| := by
    simpa only [Real.norm_eq_abs] using (hM (ξ*x) hξx).trans (le_abs_self M)
  have hv : ‖deriv smoothAFECutoff x‖≤|D| := (hD x hx).trans (le_abs_self D)
  have hfirst : ‖(((deriv (fun y:ℝ => bagPhysicalHeightWindow y) (ξ*x)*ξ:ℝ):ℂ)*smoothAFECutoff x)‖≤2*|M| := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_nonneg hξ0]
    calc
      _ ≤ (|M| *2)*1 := mul_le_mul
        (mul_le_mul hw hξ.2 hξ0 (abs_nonneg M)) (norm_smoothAFECutoff_le_one hx0)
        (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hsecond : ‖(bagPhysicalHeightWindow (ξ*x):ℂ)*deriv smoothAFECutoff x‖≤|D| := by
    rw [norm_mul,Complex.norm_of_nonneg bagPhysicalHeightWindow.nonneg]
    exact (mul_le_mul bagPhysicalHeightWindow.le_one hv (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  rw [hd.deriv]
  exact (norm_add_le _ _).trans ((add_le_add hfirst hsecond).trans (by dsimp [B];linarith))

private def profileInvDenom (l x : ℝ) : ℂ := (1+(l:ℂ)*(Real.log x:ℂ))⁻¹

/-- The exact logarithmic correction needed to pass from theta to the prime profile. -/
def primeGaussianScaledLogProfile (ξ l x : ℝ) : ℂ :=
  primeGaussianScaledProfile ξ x * (1+(l:ℂ)*(Real.log x:ℂ))⁻¹

private def scaledLogProfileD (ξ l x : ℝ) : ℂ :=
  deriv (primeGaussianScaledProfile ξ) x * profileInvDenom l x -
    primeGaussianScaledProfile ξ x*(l:ℂ)*(x:ℂ)⁻¹*profileInvDenom l x^2

private theorem profile_denom_pos {l x:ℝ} (hl:0≤l) (hx:1≤x) : 1≤1+l*Real.log x := by
  have := mul_nonneg hl (Real.log_nonneg hx)
  linarith

private theorem profile_inv_deriv {l x:ℝ} (hl:0≤l) (hx:1≤x) :
    HasDerivAt (profileInvDenom l) (-(l:ℂ)*(x:ℂ)⁻¹*profileInvDenom l x^2) x := by
  have hx0 : 0<x := by linarith
  have hd : (1+(l:ℂ)*(Real.log x:ℂ))≠0 := by
    have : (1+l*Real.log x:ℝ)≠0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (profile_denom_pos hl hx))
    exact_mod_cast this
  have hh := (((Real.hasDerivAt_log hx0.ne').ofReal_comp).const_mul (l:ℂ)).const_add 1
  have hi := hh.inv hd
  apply hi.congr_deriv
  simp only [profileInvDenom,Complex.ofReal_inv,div_eq_mul_inv,inv_pow]
  ring

private theorem scaled_log_profile_deriv (ξ : ℝ) {l x:ℝ} (hl:0≤l) (hx:x∈Icc (1:ℝ) 2) :
    HasDerivAt (primeGaussianScaledLogProfile ξ l) (scaledLogProfileD ξ l x) x := by
  have hh := ((scaled_profile_jet ξ).1 x hx).mul (profile_inv_deriv hl hx.1)
  apply hh.congr_deriv
  dsimp only [scaledLogProfileD]
  ring

private theorem scaled_log_profile_continuous (ξ l:ℝ) (hl:0≤l) :
    ContinuousOn (primeGaussianScaledLogProfile ξ l) (Icc (1:ℝ) 2) ∧
    ContinuousOn (scaledLogProfileD ξ l) (Icc (1:ℝ) 2) := by
  have hi : ContinuousOn (profileInvDenom l) (Icc (1:ℝ) 2) :=
    fun x hx => (profile_inv_deriv hl hx.1).continuousAt.continuousWithinAt
  have hxi : ContinuousOn (fun x:ℝ => (x:ℂ)⁻¹) (Icc (1:ℝ) 2) := by
    intro x hx
    exact (((Complex.ofRealCLM.hasDerivAt (x:=x)).inv
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le (by norm_num) hx.1)))).continuousAt).continuousWithinAt
  obtain ⟨_,hf,hf'⟩ := scaled_profile_jet ξ
  exact ⟨hf.mul hi, (hf'.mul hi).sub (((hf.mul continuousOn_const).mul hxi).mul (hi.pow 2))⟩

private theorem profile_inv_norm {l x:ℝ} (hl:0≤l) (hx:1≤x) : ‖profileInvDenom l x‖≤1 := by
  have hd := profile_denom_pos hl hx
  rw [profileInvDenom,norm_inv,show (1+(l:ℂ)*(Real.log x:ℂ))=((1+l*Real.log x:ℝ):ℂ) by push_cast;rfl,
    Complex.norm_of_nonneg (by linarith : 0≤1+l*Real.log x)]
  exact inv_le_one_of_one_le₀ hd

private theorem scaled_log_profile_bounds :
    ∃ B:ℝ, 0<B ∧ ∀ ξ∈Icc (1/2:ℝ) 2, ∀ l∈Icc (0:ℝ) 1, ∀ x∈Icc (1:ℝ) 2,
      ‖primeGaussianScaledLogProfile ξ l x‖≤B ∧ ‖scaledLogProfileD ξ l x‖≤2*B := by
  obtain ⟨B,hB,hbound⟩ := scaled_profile_bounds
  refine ⟨B,hB,?_⟩
  intro ξ hξ l hl x hx
  obtain ⟨h0,h1⟩ := hbound ξ hξ x hx
  have hi := profile_inv_norm hl.1 hx.1
  have hlc : ‖(l:ℂ)‖≤1 := by rw [Complex.norm_of_nonneg hl.1];exact hl.2
  have hxi : ‖(x:ℂ)⁻¹‖≤1 := by
    rw [norm_inv,Complex.norm_of_nonneg (by linarith [hx.1])]
    exact inv_le_one_of_one_le₀ hx.1
  have hm0 : ‖primeGaussianScaledProfile ξ x*profileInvDenom l x‖≤B := by
    rw [norm_mul]
    exact (mul_le_mul h0 hi (norm_nonneg _) hB.le).trans_eq (mul_one B)
  have hterm : ‖primeGaussianScaledProfile ξ x*(l:ℂ)*(x:ℂ)⁻¹*profileInvDenom l x^2‖≤B := by
    rw [norm_mul,norm_mul,norm_mul,norm_pow]
    calc
      _ ≤ B*1*1*1^2 := by gcongr
      _ = B := by ring
  have hm1 : ‖deriv (primeGaussianScaledProfile ξ) x*profileInvDenom l x‖≤B := by
    rw [norm_mul]
    exact (mul_le_mul h1 hi (norm_nonneg _) hB.le).trans_eq (mul_one B)
  refine ⟨hm0, ?_⟩
  dsimp only [scaledLogProfileD]
  exact (norm_sub_le _ _).trans (by linarith only [hm1,hterm])

/-- Actual logarithmic prime coefficient in a residue class. -/
def primeProgressionLogCoefficient (Q : ℕ) (a : ZMod Q) (n : ℕ) : ℂ :=
  if n.Prime ∧ (n : ZMod Q)=a then (Real.log n : ℂ) else 0

/-- The whole residue-restricted prime band. -/
def primeProgressionBand (Q : ℕ) (a : ZMod Q) (N : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊).filter (fun n : ℕ => n.Prime ∧ (n : ZMod Q)=a)

private theorem progression_cumulative_eq (Q : ℕ) (a : ZMod Q) (x : ℝ) :
    primeProfileCum (primeProgressionLogCoefficient Q a) x = (primeProgressionTheta Q a x : ℂ) := by
  classical
  rw [primeProfileCum, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le _)]
  simp only [primeProgressionLogCoefficient, Nat.not_prime_zero, false_and, ↓reduceIte, zero_add,
    primeProgressionTheta, Complex.ofReal_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime <;> by_cases ha : (n : ZMod Q)=a <;> simp [hp,ha]

private theorem profile_unweight_sum (Q : ℕ) (a : ZMod Q) (ξ τ:ℝ) {N:ℝ} (hN:1<N) :
    (∑ q∈Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊,
      (primeGaussianScaledLogProfile ξ (1/Real.log N) ((q:ℝ)/N)*bourgainOscillation (τ*((q:ℝ)/N)))*
        primeProgressionLogCoefficient Q a q) =
    (Real.log N:ℂ)*∑ q∈primeProgressionBand Q a N,
      primeGaussianScaledProfile ξ ((q:ℝ)/N)*bourgainOscillation (τ*((q:ℝ)/N)) := by
  classical
  rw [Finset.mul_sum,primeProgressionBand,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hp:q.Prime ∧ (q:ZMod Q)=a
  · have hqN : N<(q:ℝ) := (Nat.floor_lt (by linarith : 0≤N)).mp (Finset.mem_Ioc.mp hq).1
    have hq0 : 0<(q:ℝ) := by linarith
    have hL : Real.log N≠0 := (Real.log_pos hN).ne'
    have hqL : Real.log (q:ℝ)≠0 := (Real.log_pos (hN.trans hqN)).ne'
    have hLC : (Real.log N:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hL
    have hqLC : (Real.log (q:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hqL
    simp only [primeProgressionLogCoefficient,hp.1,hp.2,and_self,ite_true]
    dsimp only [primeGaussianScaledLogProfile]
    rw [Real.log_div hq0.ne' (by linarith : N≠0)]
    push_cast only [Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_one]
    have hden : 1+1/(Real.log N:ℂ)*((Real.log (q:ℝ):ℂ)-(Real.log N:ℂ)) =
        (Real.log (q:ℝ):ℂ)/(Real.log N:ℂ) := by field_simp;ring
    rw [hden,inv_div]
    field_simp [hqLC]
  · simp [primeProgressionLogCoefficient,hp]

private theorem profile_osc_deriv (τ x:ℝ) :
    HasDerivAt (fun y => bourgainOscillation (τ*y))
      (((τ:ℂ)*I)*bourgainOscillation (τ*x)) x := by
  have h := (((Complex.ofRealCLM.hasDerivAt (x:=x)).const_mul (τ:ℂ)).mul_const I).cexp
  simpa only [bourgainOscillation,Complex.ofReal_mul,Complex.ofRealCLM_apply,Complex.ofReal_one,mul_one,mul_assoc,mul_comm,mul_left_comm] using h

private theorem profile_osc_continuous (τ:ℝ) : Continuous (fun x => bourgainOscillation (τ*x)) :=
  continuous_iff_continuousAt.mpr (fun x => (profile_osc_deriv τ x).continuousAt)

/-- The full actual prime profile has its signed progression main term, uniformly
in the physical ratio and in every oscillation frequency. The cumulative prime
estimate and the amplitude regularity are constructed from the source. -/
theorem exists_primeGaussianProgressionProfile_power_log (Q : ℕ) [NeZero Q] :
    ∃ c C N₀ : ℝ, 0<c ∧ 0<C ∧ 3≤N₀ ∧ ∀ N:ℝ, N₀≤N →
      ∀ a:ZMod Q, IsUnit a → ∀ ξ∈Icc (1/2:ℝ) 2, ∀ τ:ℝ,
      ‖(Real.log N:ℂ)*(∑ p∈primeProgressionBand Q a N,
          primeGaussianScaledProfile ξ ((p:ℝ)/N)*bourgainOscillation (τ*((p:ℝ)/N)))/(N:ℂ)-
        (Q.totient:ℂ)⁻¹*(∫ x in (1:ℝ)..2,
          primeGaussianScaledLogProfile ξ (1/Real.log N) x*bourgainOscillation (τ*x))‖ ≤
        C*(1+|τ|)*Real.exp (-(c*Real.log N^((1:ℝ)/10))) := by
  obtain ⟨B,hB,hbound⟩ := scaled_log_profile_bounds
  obtain ⟨c,A,X,hc,hA,hX,hAP⟩ := exists_primeProgressionTheta_power_log (Q:=Q)
  refine ⟨c,9*B*(A+1),max X (Real.exp 1),hc,by positivity,
    hX.trans (le_max_left _ _),?_⟩
  intro N hN a ha ξ hξ τ
  have hNX : X≤N := (le_max_left _ _).trans hN
  have hN3 : 3≤N := hX.trans hNX
  have hN1 : 1<N := by linarith only [hN3]
  have hN0 : 0<N := by linarith only [hN3]
  have hL : 0<Real.log N := Real.log_pos hN1
  have hL1 : 1≤Real.log N := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hN)
  let l : ℝ := 1/Real.log N
  let ε : ℝ := A*Real.exp (-(c*Real.log N^((1:ℝ)/10)))
  let ell : ℂ := (Q.totient:ℂ)⁻¹
  have hl : l∈Icc (0:ℝ) 1 := ⟨by dsimp [l];positivity, (div_le_one hL).mpr hL1⟩
  have hε : 0≤ε := by dsimp [ε];positivity
  have hcum : ∀ x∈Icc N (2*N),
      ‖primeProfileCum (primeProgressionLogCoefficient Q a) x-ell*(x:ℂ)‖≤ε*x := by
    intro x hx
    have hx0 : 0≤x := hN0.le.trans hx.1
    rw [progression_cumulative_eq]
    have he : (primeProgressionTheta Q a x:ℂ)-ell*(x:ℂ) =
        ((primeProgressionTheta Q a x-x/Q.totient:ℝ):ℂ) := by
      dsimp only [ell]
      push_cast
      ring
    rw [he,Complex.norm_real,Real.norm_eq_abs]
    have hdecay : Real.exp (-(c*Real.log x^((1:ℝ)/10)))≤
        Real.exp (-(c*Real.log N^((1:ℝ)/10))) := by
      apply Real.exp_le_exp.mpr
      exact neg_le_neg (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hL.le (Real.log_le_log hN0 hx.1) (by positivity)) hc.le)
    exact (hAP a ha x (hNX.trans hx.1)).trans
      ((mul_le_mul_of_nonneg_left hdecay (mul_nonneg hA hx0)).trans_eq (by dsimp [ε];ring))
  let f : ℝ→ℂ := fun x => primeGaussianScaledLogProfile ξ l x*bourgainOscillation (τ*x)
  let f' : ℝ→ℂ := fun x => scaledLogProfileD ξ l x*bourgainOscillation (τ*x)+
    primeGaussianScaledLogProfile ξ l x*(((τ:ℂ)*I)*bourgainOscillation (τ*x))
  have hderiv : ∀ x∈Icc (1:ℝ) 2, HasDerivAt f (f' x) x :=
    fun x hx => (scaled_log_profile_deriv ξ hl.1 hx).mul (profile_osc_deriv τ x)
  have hfc : ContinuousOn f' (Icc (1:ℝ) 2) :=
    ((scaled_log_profile_continuous ξ l hl.1).2.mul (profile_osc_continuous τ).continuousOn).add
      ((scaled_log_profile_continuous ξ l hl.1).1.mul
        (continuousOn_const.mul (profile_osc_continuous τ).continuousOn))
  have hbd : ∀ x∈Icc (1:ℝ) 2, ‖f' x‖≤3*B*(1+|τ|) := by
    intro x hx
    obtain ⟨hg,hg'⟩ := hbound ξ hξ l hl x hx
    have hn := norm_add_le (scaledLogProfileD ξ l x*bourgainOscillation (τ*x))
      (primeGaussianScaledLogProfile ξ l x*(((τ:ℂ)*I)*bourgainOscillation (τ*x)))
    simp only [norm_mul,norm_bourgainOscillation,norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs] at hn
    dsimp only [f']
    have hm := mul_le_mul_of_nonneg_right hg (abs_nonneg τ)
    have hp := mul_nonneg hB.le (abs_nonneg τ)
    linarith only [hn,hg',hm,hp,hB]
  have hab := primeProfile_scaledAbel_error (primeProgressionLogCoefficient Q a) f f' ell
    hN0 (by positivity : 0≤3*B*(1+|τ|)) hε hderiv hfc hbd hcum
  have hend (x:ℝ) (hx:x∈Icc (1:ℝ) 2) : ‖f x‖≤B := by
    dsimp only [f]
    rw [norm_mul,norm_bourgainOscillation,mul_one]
    exact (hbound ξ hξ l hl x hx).1
  have hfront : ‖f 1‖+2*‖f 2‖+2*(3*B*(1+|τ|))≤9*B*(1+|τ|) := by
    have h1 := hend 1 (by constructor <;> norm_num)
    have h2 := hend 2 (by constructor <;> norm_num)
    have hp := mul_nonneg hB.le (abs_nonneg τ)
    linarith only [h1,h2,hp]
  have hab' := hab.trans (mul_le_mul_of_nonneg_right hfront hε)
  have hunweight := profile_unweight_sum Q a ξ τ hN1
  change (∑ p∈Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊, f ((p:ℝ)/N)*primeProgressionLogCoefficient Q a p)=_ at hunweight
  rw [hunweight] at hab'
  apply hab'.trans
  dsimp only [ε]
  have hp : 0≤9*B*(1+|τ|)*Real.exp (-(c*Real.log N^((1:ℝ)/10))) := by positivity
  nlinarith only [hp]

/-- A full residue prime row has uniform inverse-frequency control, with the
proved growing-frequency arithmetic error and all band boundaries retained. -/
theorem exists_primeGaussianProgressionProfile_fourier_bound (Q : ℕ) [NeZero Q] :
    ∃ c C N₀ : ℝ, 0<c ∧ 0<C ∧ 3≤N₀ ∧ ∀ N:ℝ, N₀≤N →
      ∀ a:ZMod Q, IsUnit a → ∀ ξ∈Icc (1/2:ℝ) 2, ∀ τ:ℝ, τ≠0 →
      ‖∑ p∈primeProgressionBand Q a N,
          primeGaussianScaledProfile ξ ((p:ℝ)/N)*bourgainOscillation (τ*((p:ℝ)/N))‖ ≤
        C*N/Real.log N*(1/|τ|+(1+|τ|)*Real.exp (-(c*Real.log N^((1:ℝ)/10)))) := by
  obtain ⟨c,A,X,hc,hA,hX,hmain⟩ := exists_primeGaussianProgressionProfile_power_log Q
  obtain ⟨B,hB,hbound⟩ := scaled_log_profile_bounds
  let C := A+4*B*‖(Q.totient:ℂ)⁻¹‖
  have hC : 0<C := by dsimp [C];positivity
  refine ⟨c,C,max X (Real.exp 1),hc,hC,hX.trans (le_max_left _ _),?_⟩
  intro N hN a ha ξ hξ τ hτ
  have hNX : X≤N := (le_max_left _ _).trans hN
  have hN3 := hX.trans hNX
  have hN0 : 0<N := by linarith only [hN3]
  have hL : 0<Real.log N := Real.log_pos (by linarith only [hN3])
  have hL1 : 1≤Real.log N := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hN)
  have hl : 1/Real.log N∈Icc (0:ℝ) 1 := ⟨by positivity,(div_le_one hL).mpr hL1⟩
  have hf := primeProfile_fourier_once
    (primeGaussianScaledLogProfile ξ (1/Real.log N)) (scaledLogProfileD ξ (1/Real.log N)) hτ
    (fun x hx => scaled_log_profile_deriv ξ hl.1 hx)
    (scaled_log_profile_continuous ξ _ hl.1).2
    (fun x hx => (hbound ξ hξ _ hl x hx).2)
  have hfour : ‖∫ x in (1:ℝ)..2,
      primeGaussianScaledLogProfile ξ (1/Real.log N) x*bourgainOscillation (τ*x)‖≤4*B/|τ| := by
    apply hf.trans
    apply div_le_div_of_nonneg_right _ (abs_nonneg τ)
    have h1 := (hbound ξ hξ _ hl 1 (by constructor <;> norm_num)).1
    have h2 := (hbound ξ hξ _ hl 2 (by constructor <;> norm_num)).1
    linarith only [h1,h2]
  let S := ∑ p∈primeProgressionBand Q a N,
    primeGaussianScaledProfile ξ ((p:ℝ)/N)*bourgainOscillation (τ*((p:ℝ)/N))
  let J := ∫ x in (1:ℝ)..2,
    primeGaussianScaledLogProfile ξ (1/Real.log N) x*bourgainOscillation (τ*x)
  have herr := hmain N hNX a ha ξ hξ τ
  change ‖(Real.log N:ℂ)*S/(N:ℂ)-(Q.totient:ℂ)⁻¹*J‖≤_ at herr
  have hJ : ‖(Q.totient:ℂ)⁻¹*J‖≤‖(Q.totient:ℂ)⁻¹‖*(4*B/|τ|) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hfour (norm_nonneg _)
  have htri := (norm_le_norm_sub_add ((Real.log N:ℂ)*S/(N:ℂ)) ((Q.totient:ℂ)⁻¹*J)).trans
    (add_le_add herr hJ)
  rw [norm_div,norm_mul,Complex.norm_of_nonneg hL.le,Complex.norm_of_nonneg hN0.le] at htri
  have hcoeff : A*(1+|τ|)*Real.exp (-(c*Real.log N^((1:ℝ)/10)))+
      ‖(Q.totient:ℂ)⁻¹‖*(4*B/|τ|) ≤
      C*(1/|τ|+(1+|τ|)*Real.exp (-(c*Real.log N^((1:ℝ)/10)))) := by
    have h1 : 0≤A/|τ| := div_nonneg hA.le (abs_nonneg τ)
    have h2 : 0≤4*B*‖(Q.totient:ℂ)⁻¹‖*(1+|τ|)*Real.exp (-(c*Real.log N^((1:ℝ)/10))) := by positivity
    dsimp only [C]
    simp only [div_eq_mul_inv] at h1 ⊢
    nlinarith only [h1,h2]
  have hh := (div_le_iff₀ hN0).mp (htri.trans hcoeff)
  change ‖S‖≤_
  calc
    ‖S‖ = (Real.log N*‖S‖)/Real.log N := by field_simp
    _ ≤ (C*(1/|τ|+(1+|τ|)*Real.exp (-(c*Real.log N^((1:ℝ)/10))))*N)/Real.log N :=
      div_le_div_of_nonneg_right hh hL.le
    _ = _ := by ring

end RHTower
