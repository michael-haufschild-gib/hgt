import GaloisForLFunctions.RHTower.WeilWorkExposingRayCoherentGap
import GaloisForLFunctions.RHTower.WeilFullConeSpectralConsistency
import GaloisForLFunctions.RHTower.WeilPositivityMajorantRigidity

/-!
# Local-seed capacity of the literal exposing source

Unequal short polar seeds satisfy an exact finite variance energy identity, even though
archimedeanWeilSymbol changes sign. The existing half-log-two ground gap then bounds
any real Fourier evaluation of the completed source. The literal truncated Riemann
source retains a fixed positive value at zero, uniformly for every cutoff L >= 2.
Consequently every such variance completion, and the entire finite exposing mixture,
has a fixed positive total-energy floor. This does not bound arbitrary atom repairs.

Paper proof: docs/reports/weil-work/results/02-exposing-ray/LOCAL-SEED-CAPACITY-PROOF.md.
-/

open MeasureTheory Set Real Complex Filter Topology Zeta23
open scoped ENNReal
noncomputable section
namespace RHTower.ExposingRayLocalCapacity

private theorem compact_of_polar {a : ℝ} {f : ℝ → ℂ} (hf : IsPolarTest a f) :
    HasCompactSupport f := isCompact_Icc.of_isClosed_subset isClosed_closure hf.2.2.1

/-- Finite variance, allowing completely unequal seed moduli. -/
private theorem variance {ι : Type*} [Fintype ι] (w : ι → ℝ) (v : ι → ℂ)
    (M : ℝ) (z : ℂ) (hM : 0 < M) (hw : ∑ i, w i = M)
    (hz : ∑ i, (w i : ℂ)*v i = z) :
    ‖z‖^2 + ∑ i, (w i/M)*‖(M : ℂ)*v i-z‖^2 = M*∑ i, w i*‖v i‖^2 := by
  have hre : ∑ i, w i*(v i).re = z.re := by
    simpa using congrArg Complex.re hz
  have him : ∑ i, w i*(v i).im = z.im := by
    simpa using congrArg Complex.im hz
  have he : ∀ i, (w i/M)*‖(M : ℂ)*v i-z‖^2 =
      M*(w i*‖v i‖^2)-2*z.re*(w i*(v i).re)-2*z.im*(w i*(v i).im)+
        (‖z‖^2/M)*w i := by
    intro i
    simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.sub_im,Complex.mul_im]
    field_simp [hM.ne']
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_sub_distrib,
    ← Finset.mul_sum,← Finset.mul_sum,← Finset.mul_sum,← Finset.mul_sum,hw,hre,him,
    div_mul_cancel₀ _ hM.ne']
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

private theorem weighted_square_le {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (v : ι → ℂ) (hw : ∀ i, 0 ≤ w i) (hM : 0 < ∑ i, w i) :
    ‖∑ i, (w i : ℂ)*v i‖^2 ≤ (∑ i, w i)*∑ i, w i*‖v i‖^2 := by
  have h := variance w v (∑ i,w i) (∑ i,(w i : ℂ)*v i) hM rfl rfl
  have hp : 0 ≤ ∑ i, (w i/(∑ j,w j))*
      ‖((∑ j,w j : ℝ) : ℂ)*v i-(∑ j,(w j : ℂ)*v j)‖^2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (div_nonneg (hw i) hM.le) (sq_nonneg _))
  linarith

/-- The exact Fourier evaluation bound on the half-log-two source window. -/
theorem short_fourier_bound {g : ℝ → ℂ} (hg : IsPolarTest (Real.log 2/2) g) (t : ℝ) :
    ‖paperFT g t‖^2 ≤ Real.log 2 * ∫ u : ℝ, ‖g u‖^2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let S : Set ℝ := Icc (-(Real.log 2/2)) (Real.log 2/2)
  let J : ℝ := ∫ u in S, ‖g u‖
  have hi : IntegrableOn (fun u => ‖g u‖) S := hg.2.1.continuous.norm.integrableOn_Icc
  have hi2 : IntegrableOn (fun u => ‖g u‖^2) S :=
    (hg.2.1.continuous.norm.pow 2).integrableOn_Icc
  have hc : IntegrableOn (fun _ : ℝ => J^2) S := continuous_const.integrableOn_Icc
  have hv : volume.real S = Real.log 2 := by
    rw [Real.volume_real_Icc_of_le (by linarith)]
    ring
  have hI : (∫ u in S, ‖g u‖) = ∫ u : ℝ, ‖g u‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    rw [image_eq_zero_of_notMem_tsupport (fun hx => hu (hg.2.2.1 hx)),norm_zero]
  have hH : (∫ u in S, ‖g u‖^2) = ∫ u : ℝ, ‖g u‖^2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    rw [image_eq_zero_of_notMem_tsupport (fun hx => hu (hg.2.2.1 hx)),norm_zero,zero_pow (by norm_num)]
  have he : (∫ u in S, (Real.log 2*‖g u‖-J)^2) =
      (Real.log 2)^2*(∫ u in S, ‖g u‖^2)-2*Real.log 2*J*J+J^2*Real.log 2 := by
    calc _ = ∫ u in S, ((Real.log 2)^2*‖g u‖^2-(2*Real.log 2*J)*‖g u‖)+J^2 := by
          apply integral_congr_ae
          filter_upwards with u
          ring
      _ = _ := by
        have hia : IntegrableOn (fun u => (Real.log 2)^2*‖g u‖^2) S := hi2.const_mul _
        have hib : IntegrableOn (fun u => (2*Real.log 2*J)*‖g u‖) S := hi.const_mul _
        have his : IntegrableOn (fun u => (Real.log 2)^2*‖g u‖^2-(2*Real.log 2*J)*‖g u‖) S := hia.sub hib
        rw [integral_add his hc,
          integral_sub hia hib,integral_const_mul,integral_const_mul,
          setIntegral_const,hv,smul_eq_mul]
        dsimp [J]
        ring
  have hp : 0 ≤ ∫ u in S, (Real.log 2*‖g u‖-J)^2 := integral_nonneg (fun u => sq_nonneg _)
  rw [he] at hp
  have hmul : Real.log 2*J^2 ≤ Real.log 2*(Real.log 2*(∫ u in S, ‖g u‖^2)) := by nlinarith only [hp]
  have hcs := le_of_mul_le_mul_left hmul hl
  have hFT := WeilSpectral.norm_paperFT_real_le g t
  rw [← hI] at hFT
  calc ‖paperFT g t‖^2 ≤ J^2 := pow_le_pow_left₀ (norm_nonneg _) hFT 2
    _ ≤ _ := by rwa [hH] at hcs

/-- Literal polar seeds in the known positive window pay a fixed Fourier evaluation cost. -/
theorem short_energy_capacity {g : ℝ → ℂ} (hg : IsPolarTest (Real.log 2/2) g) (t : ℝ) :
    (π/(5*Real.log 2))*‖paperFT g t‖^2 ≤ archEnergy g := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := mul_le_mul_of_nonneg_left (short_fourier_bound hg t)
    (by positivity : 0 ≤ π/(5*Real.log 2))
  calc _ ≤ (π/(5*Real.log 2))*(Real.log 2*(∫ u : ℝ, ‖g u‖^2)) := h
    _ = (π/5)*(∫ u : ℝ, ‖g u‖^2) := by field_simp
    _ ≤ _ := ExposingRayCoherentGap.c2_halfLogTwo_coercivity hg

/-- A finite positive mean of independently translated short polar seeds. -/
def mixture {ι : Type*} [Fintype ι] (w : ι → ℝ) (g : ι → ℝ → ℂ)
    (x : ι → ℝ) (u : ℝ) : ℂ := ∑ i, (w i : ℂ)*g i (u-x i)

/-- The canonical variance residual; its coefficient in energy is `w i / ∑ w`. -/
def varianceRepair {ι : Type*} [Fintype ι] (w : ι → ℝ) (g : ι → ℝ → ℂ)
    (x : ι → ℝ) (i : ι) (u : ℝ) : ℂ :=
  ((∑ j, w j : ℝ) : ℂ)*g i (u-x i)-mixture w g x u

private theorem translate_polar {a A : ℝ} {g : ℝ → ℂ} (hg : IsPolarTest a g)
    (x : ℝ) (hA : a+|x| ≤ A) : IsPolarTest A (fun u => g (u-x)) := by
  refine ⟨by linarith [abs_nonneg x, hg.1], hg.2.1.comp (contDiff_id.sub contDiff_const), ?_, ?_, ?_⟩
  · apply closure_minimal _ isClosed_Icc
    intro u hu
    have hs := hg.2.2.1 (subset_tsupport g hu)
    constructor <;> linarith [hs.1, hs.2, le_abs_self x, neg_abs_le x]
  · rw [paperFT_translate',hg.2.2.2.1,mul_zero]
  · rw [paperFT_translate',hg.2.2.2.2,mul_zero]

private theorem paperFT_sum {ι : Type*} [Fintype ι] {a : ℝ}
    (w : ι → ℝ) (g : ι → ℝ → ℂ) (hg : ∀ i, IsPolarTest a (g i)) (z : ℂ) :
    paperFT (fun u => ∑ i,(w i : ℂ)*g i u) z = ∑ i,(w i : ℂ)*paperFT (g i) z := by
  have hi (i : ι) : Integrable (fun u => (w i : ℂ)*(g i u*Complex.exp (I*z*u))) :=
    ((hg i).2.1.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      (compact_of_polar (hg i)).mul_right |>.const_mul _
  unfold paperFT
  simp_rw [Finset.sum_mul,mul_assoc]
  rw [integral_finsetSum _ (fun i _ => by simpa only [mul_assoc] using hi i)]
  simp_rw [integral_const_mul]

private theorem sum_polar {ι : Type*} [Fintype ι] {a : ℝ}
    (ha : 0 ≤ a) (w : ι → ℝ) (g : ι → ℝ → ℂ) (hg : ∀ i, IsPolarTest a (g i)) :
    IsPolarTest a (fun u => ∑ i,(w i : ℂ)*g i u) := by
  refine ⟨ha, ContDiff.sum (fun i _ => contDiff_const.mul (hg i).2.1), ?_, ?_, ?_⟩
  · apply closure_minimal _ isClosed_Icc
    intro u hu
    by_contra h
    apply hu
    apply Finset.sum_eq_zero
    intro i _
    rw [image_eq_zero_of_notMem_tsupport (fun hx => h ((hg i).2.2.1 hx)),mul_zero]
  · rw [paperFT_sum w g hg]
    simp only [fun i => (hg i).2.2.2.1,mul_zero,Finset.sum_const_zero]
  · rw [paperFT_sum w g hg]
    simp only [fun i => (hg i).2.2.2.2,mul_zero,Finset.sum_const_zero]

private theorem paperFT_linear {a : ℝ} {f g : ℝ → ℂ} (hf : IsPolarTest a f)
    (hg : IsPolarTest a g) (M : ℝ) (z : ℂ) :
    paperFT (fun u => (M : ℂ)*f u-g u) z = (M : ℂ)*paperFT f z-paperFT g z := by
  have hfi : Integrable fun u => f u*Complex.exp (I*z*u) :=
    (hf.2.1.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport (compact_of_polar hf).mul_right
  have hgi : Integrable fun u => g u*Complex.exp (I*z*u) :=
    (hg.2.1.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport (compact_of_polar hg).mul_right
  unfold paperFT
  have he : (fun u => ((M : ℂ)*f u-g u)*Complex.exp (I*z*u)) =
      fun u => (M : ℂ)*(f u*Complex.exp (I*z*u))-g u*Complex.exp (I*z*u) := by funext u; ring
  rw [he,integral_sub (hfi.const_mul _) hgi,integral_const_mul]

private theorem linear_polar {a : ℝ} {f g : ℝ → ℂ} (hf : IsPolarTest a f)
    (hg : IsPolarTest a g) (M : ℝ) : IsPolarTest a (fun u => (M : ℂ)*f u-g u) := by
  refine ⟨hf.1,(contDiff_const.mul hf.2.1).sub hg.2.1,?_,?_,?_⟩
  · apply closure_minimal _ isClosed_Icc
    intro u hu
    by_contra h
    have hf0 := image_eq_zero_of_notMem_tsupport (fun hx => h (hf.2.2.1 hx))
    have hg0 := image_eq_zero_of_notMem_tsupport (fun hx => h (hg.2.2.1 hx))
    exact hu (by simp [hf0,hg0])
  · rw [paperFT_linear hf hg,hf.2.2.2.1,hg.2.2.2.1,mul_zero,sub_zero]
  · rw [paperFT_linear hf hg,hf.2.2.2.2,hg.2.2.2.2,mul_zero,sub_zero]

private def aperture {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ := Real.log 2/2+∑ i,|x i|

private theorem aperture_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) : 0 ≤ aperture x := by
  unfold aperture
  positivity

private theorem seed_polar {ι : Type*} [Fintype ι] (g : ι → ℝ → ℂ) (x : ι → ℝ)
    (hg : ∀ i, IsPolarTest (Real.log 2/2) (g i)) (i : ι) :
    IsPolarTest (aperture x) (fun u => g i (u-x i)) := by
  apply translate_polar (hg i)
  change Real.log 2/2+|x i| ≤ Real.log 2/2+∑ j,|x j|
  linarith [Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)]

private theorem mixture_polar {ι : Type*} [Fintype ι] (w : ι → ℝ) (g : ι → ℝ → ℂ)
    (x : ι → ℝ) (hg : ∀ i, IsPolarTest (Real.log 2/2) (g i)) :
    IsPolarTest (aperture x) (mixture w g x) :=
  sum_polar (aperture_nonneg x) w _ (seed_polar g x hg)

private theorem repair_polar {ι : Type*} [Fintype ι] (w : ι → ℝ) (g : ι → ℝ → ℂ)
    (x : ι → ℝ) (hg : ∀ i, IsPolarTest (Real.log 2/2) (g i)) (i : ι) :
    IsPolarTest (aperture x) (varianceRepair w g x i) :=
  linear_polar (seed_polar g x hg i) (mixture_polar w g x hg) _

private theorem norm_translate (g : ℝ → ℂ) (x t : ℝ) :
    ‖paperFT (fun u => g (u-x)) t‖ = ‖paperFT g t‖ := by
  rw [paperFT_translate',norm_mul]
  have he : I*(t : ℂ)*x = ((t*x : ℝ) : ℂ)*I := by push_cast; ring
  rw [he,Complex.norm_exp_ofReal_mul_I,one_mul]

private theorem fourier_mean {ι : Type*} [Fintype ι] (w : ι → ℝ) (g : ι → ℝ → ℂ)
    (x : ι → ℝ) (hg : ∀ i, IsPolarTest (Real.log 2/2) (g i)) (t : ℝ) :
    ∑ i,(w i : ℂ)*paperFT (fun u => g i (u-x i)) t = paperFT (mixture w g x) t :=
  (paperFT_sum w _ (seed_polar g x hg) t).symm

private theorem density_identity {ι : Type*} [Fintype ι] (w : ι → ℝ) (g : ι → ℝ → ℂ)
    (x : ι → ℝ) (hg : ∀ i, IsPolarTest (Real.log 2/2) (g i))
    (hM : 0 < ∑ i,w i) (t : ℝ) :
    ‖paperFT (mixture w g x) t‖^2+
      ∑ i,(w i/(∑ j,w j))*‖paperFT (varianceRepair w g x i) t‖^2 =
        (∑ j,w j)*∑ i,w i*‖paperFT (g i) t‖^2 := by
  have hi (i : ι) : paperFT (varianceRepair w g x i) t =
      ((∑ j,w j : ℝ) : ℂ)*paperFT (fun u => g i (u-x i)) t-paperFT (mixture w g x) t :=
    paperFT_linear (seed_polar g x hg i) (mixture_polar w g x hg) _ _
  simp_rw [hi]
  have h := variance w (fun i => paperFT (fun u => g i (u-x i)) t) _ _ hM rfl
    (fourier_mean w g x hg t)
  simpa only [norm_translate] using h

/-- Exact energy accounting for arbitrary, unequal short seeds. The symbol may change sign. -/
theorem variance_energy_identity {ι : Type*} [Fintype ι] (w : ι → ℝ) (g : ι → ℝ → ℂ)
    (x : ι → ℝ) (hg : ∀ i, IsPolarTest (Real.log 2/2) (g i)) (hM : 0 < ∑ i,w i) :
    archEnergy (mixture w g x)+∑ i,(w i/(∑ j,w j))*archEnergy (varianceRepair w g x i) =
      (∑ j,w j)*∑ i,w i*archEnergy (g i) := by
  let D (f : ℝ → ℂ) (t : ℝ) := ‖paperFT f t‖^2*archimedeanWeilSymbol (t/(2*π))
  have hI {a : ℝ} {f : ℝ → ℂ} (hf : IsPolarTest a f) : Integrable (D f) :=
    integrable_normSq_paperFT_mul_arch hf.2.1 hf.2.2.1
  have hF := hI (mixture_polar w g x hg)
  have hR (i : ι) := hI (repair_polar w g x hg i)
  have hG (i : ι) := hI (hg i)
  change (∫ t,D (mixture w g x) t)+∑ i,(w i/(∑ j,w j))*(∫ t,D (varianceRepair w g x i) t) =
    (∑ j,w j)*∑ i,w i*(∫ t,D (g i) t)
  have hs : Integrable (fun t => ∑ i,(w i/(∑ j,w j))*D (varianceRepair w g x i) t) :=
    integrable_finsetSum _ (fun i _ => (hR i).const_mul _)
  calc _ = (∫ t,D (mixture w g x) t)+∫ t,∑ i,(w i/(∑ j,w j))*D (varianceRepair w g x i) t := by
        rw [integral_finsetSum _ (fun i _ => (hR i).const_mul _)]
        simp only [integral_const_mul]
    _ = ∫ t,D (mixture w g x) t+∑ i,(w i/(∑ j,w j))*D (varianceRepair w g x i) t :=
      (integral_add hF hs).symm
    _ = ∫ t,(∑ j,w j)*∑ i,w i*D (g i) t := by
      apply integral_congr_ae
      filter_upwards with t
      have hd := congrArg (fun y : ℝ => y*archimedeanWeilSymbol (t/(2*π)))
        (density_identity w g x hg hM t)
      simpa only [D,add_mul,Finset.sum_mul,mul_assoc] using hd
    _ = _ := by
      rw [integral_const_mul,integral_finsetSum _ (fun i _ => (hG i).const_mul _)]
      simp only [integral_const_mul]

/-- Any Fourier value of the completed source forces a positive, profile-independent cost. -/
theorem variance_energy_capacity {ι : Type*} [Fintype ι] (w : ι → ℝ) (g : ι → ℝ → ℂ)
    (x : ι → ℝ) (hw : ∀ i,0 ≤ w i) (hg : ∀ i,IsPolarTest (Real.log 2/2) (g i))
    (hM : 0 < ∑ i,w i) (t : ℝ) :
    (π/(5*Real.log 2))*‖paperFT (mixture w g x) t‖^2 ≤
      archEnergy (mixture w g x)+∑ i,(w i/(∑ j,w j))*archEnergy (varianceRepair w g x i) := by
  have hκ : 0 ≤ π/(5*Real.log 2) := by positivity
  have hj := weighted_square_le w (fun i => paperFT (fun u => g i (u-x i)) t) hw hM
  rw [fourier_mean w g x hg] at hj
  simp only [norm_translate] at hj
  have he : (π/(5*Real.log 2))*(∑ i,w i*‖paperFT (g i) t‖^2) ≤ ∑ i,w i*archEnergy (g i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc _ = w i*((π/(5*Real.log 2))*‖paperFT (g i) t‖^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (short_energy_capacity (hg i) t) (hw i)
  rw [variance_energy_identity w g x hg hM]
  calc _ ≤ (π/(5*Real.log 2))*((∑ i,w i)*∑ i,w i*‖paperFT (g i) t‖^2) :=
      mul_le_mul_of_nonneg_left hj hκ
    _ = (∑ i,w i)*((π/(5*Real.log 2))*∑ i,w i*‖paperFT (g i) t‖^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he hM.le

/-- A fixed positive Fourier mass retained by every cutoff `L ≥ 2`. -/
def riemannMass : ℝ := (1-2*polarWeight 1)*
  ∫ u in Icc (-(1/2 : ℝ)) (1/2 : ℝ), riemannKernelReal u

private theorem polar_factor_pos : 0 < 1-2*polarWeight 1 := by
  have hc : 1 < Real.cosh (1/2 : ℝ) := Real.one_lt_cosh.mpr (by norm_num)
  have hp : polarWeight 1 < 1/2 := by
    unfold polarWeight
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  linarith

private theorem kernel_local_mass_pos :
    0 < ∫ u in Icc (-(1/2 : ℝ)) (1/2 : ℝ),riemannKernelReal u := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall (fun u => (riemannKernelReal_pos u).le))
    continuous_riemannKernelReal.integrableOn_Icc).mpr
  have hs : Function.support riemannKernelReal = univ := by
    ext u
    simp only [Function.mem_support,mem_univ,iff_true]
    exact (riemannKernelReal_pos u).ne'
  rw [hs,univ_inter,Real.volume_Icc]
  norm_num

theorem riemannMass_pos : 0 < riemannMass := mul_pos polar_factor_pos kernel_local_mass_pos

/-- The actual unit-shift polar Riemann source retains a uniform Fourier value at zero. -/
theorem riemann_fourier_mass {L : ℝ} (hL : 2 ≤ L) :
    riemannMass ≤ ‖paperFT (polarRiemannDifference L 1) 0‖ := by
  have hI : Integrable (truncatedRiemannKernelReal L) :=
    (continuous_truncatedRiemannKernelReal L).integrable_of_hasCompactSupport
      (hasCompactSupport_truncatedRiemannKernelReal L)
  have hi : (∫ u in Icc (-(1/2 : ℝ)) (1/2 : ℝ),riemannKernelReal u) ≤
      ∫ u,truncatedRiemannKernelReal L u := by
    calc _ = ∫ u in Icc (-(1/2 : ℝ)) (1/2 : ℝ),truncatedRiemannKernelReal L u := by
          apply setIntegral_congr_fun measurableSet_Icc
          intro u hu
          have hab : |u| ≤ L-1 := (abs_le.mpr hu).trans (by linarith)
          rw [truncatedRiemannKernelReal,bulkCutoff_eq_one hab,mul_one]
      _ ≤ _ := setIntegral_le_integral hI
        (Eventually.of_forall (truncatedRiemannKernelReal_nonneg L))
  have hz : paperFT (truncatedRiemannKernel L) 0 =
      ((∫ u,truncatedRiemannKernelReal L u : ℝ) : ℂ) := by
    simp only [paperFT,mul_zero,zero_mul,Complex.exp_zero,mul_one,truncatedRiemannKernel_eq]
    exact integral_complex_ofReal
  have he : paperFT (polarRiemannDifference L 1) 0 =
      (((1-2*polarWeight 1)*(∫ u,truncatedRiemannKernelReal L u) : ℝ) : ℂ) := by
    rw [paperFT_polarRiemannDifference]
    simp only [mul_zero,zero_mul,Complex.exp_zero,mul_one,hz]
    push_cast
    ring
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg
    (mul_nonneg polar_factor_pos.le (integral_nonneg (truncatedRiemannKernelReal_nonneg L)))]
  exact mul_le_mul_of_nonneg_left hi polar_factor_pos.le

/-- A cutoff-, count-, weight-, translation-, and seed-independent lower bound. -/
def riemannCapacity : ℝ := (π/(5*Real.log 2))*riemannMass^2

theorem riemannCapacity_pos : 0 < riemannCapacity := by
  exact mul_pos (by positivity) (sq_pos_of_pos riemannMass_pos)

/-- Every local-seed variance representation of the literal Riemann source pays the same capacity.
No sign premise is imposed on its archimedean energy or on the variance residuals. -/
theorem riemann_local_completion_floor {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (g : ι → ℝ → ℂ) (x : ι → ℝ) {L : ℝ} (hL : 2 ≤ L)
    (hw : ∀ i,0 ≤ w i) (hg : ∀ i,IsPolarTest (Real.log 2/2) (g i)) (hM : 0 < ∑ i,w i)
    (hF : mixture w g x = polarRiemannDifference L 1) :
    riemannCapacity ≤ archEnergy (polarRiemannDifference L 1)+
      ∑ i,(w i/(∑ j,w j))*archEnergy (varianceRepair w g x i) := by
  have h := variance_energy_capacity w g x hw hg hM 0
  rw [hF] at h
  exact (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ riemannMass_pos.le (riemann_fourier_mass hL) 2) (by positivity)).trans h

/-- Completing every source of the literal finite exposing mixture through short seeds retains
at least the fixed contribution of its unit-shift source, with the exact `1/(2π)` weight. -/
theorem exposing_mixture_local_completion_floor {K : ℕ}
    (ι : Fin (K+1) → Type*) [∀ k,Fintype (ι k)]
    (w : ∀ k,ι k → ℝ) (g : ∀ k,ι k → ℝ → ℂ) (x : ∀ k,ι k → ℝ)
    {L : ℝ} (hL : 2 ≤ L) (hw : ∀ k i,0 ≤ w k i)
    (hg : ∀ k i,IsPolarTest (Real.log 2/2) (g k i)) (hM : ∀ k,0 < ∑ i,w k i)
    (hF : ∀ k,mixture (w k) (g k) (x k) = polarRiemannDifference L (1/(k.val+1 : ℝ))) :
    riemannCapacity/(2*π) ≤ ∑ k : Fin (K+1),((1/2 : ℝ)^k.val/(2*π))*
      (archEnergy (polarRiemannDifference L (1/(k.val+1 : ℝ)))+
        ∑ i,(w k i/(∑ j,w k j))*archEnergy (varianceRepair (w k) (g k) (x k) i)) := by
  let E (k : Fin (K+1)) := archEnergy (polarRiemannDifference L (1/(k.val+1 : ℝ)))+
    ∑ i,(w k i/(∑ j,w k j))*archEnergy (varianceRepair (w k) (g k) (x k) i)
  have hE (k : Fin (K+1)) : 0 ≤ E k := by
    have h := variance_energy_capacity (w k) (g k) (x k) (hw k) (hg k) (hM k) 0
    rw [hF k] at h
    exact le_trans (by positivity) h
  have hz : mixture (w 0) (g 0) (x 0) = polarRiemannDifference L 1 := by
    simpa using hF 0
  have h0 : riemannCapacity ≤ E 0 := by
    simpa [E] using riemann_local_completion_floor (w 0) (g 0) (x 0) hL (hw 0) (hg 0) (hM 0) hz
  have hs : ((1/2 : ℝ)^(0 : Fin (K+1)).val/(2*π))*E 0 ≤
      ∑ k : Fin (K+1),((1/2 : ℝ)^k.val/(2*π))*E k :=
    Finset.single_le_sum (fun k _ => mul_nonneg (by positivity : 0 ≤ (1/2 : ℝ)^k.val/(2*π)) (hE k)) (Finset.mem_univ 0)
  have hc := mul_le_mul_of_nonneg_left h0 (by positivity : 0 ≤ 1/(2*π))
  have hs' : (1/(2*π))*E 0 ≤ ∑ k : Fin (K+1),((1/2 : ℝ)^k.val/(2*π))*E k := by
    simpa only [Fin.val_zero,pow_zero] using hs
  change riemannCapacity/(2*π) ≤ ∑ k : Fin (K+1),((1/2 : ℝ)^k.val/(2*π))*E k
  calc _ = (1/(2*π))*riemannCapacity := by ring
    _ ≤ _ := hc.trans hs'

end RHTower.ExposingRayLocalCapacity
