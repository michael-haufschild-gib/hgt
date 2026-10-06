import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicWindowTransition
import GaloisForLFunctions.RHTower.ChiCubicControlledCutoff
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Derivative budgets for the actual normalized cubic amplitude

The core `V(x)/(1+h*log x)` has uniformly bounded derivatives on
`h ∈ [0,1]`, `x ∈ [1,2]`: its denominator is at least one, partial derivatives
are jointly smooth, and the parameter rectangle is compact. Leibniz's rule
combines these bounds with the selected shrinking cutoff's edge-mass bounds.
The resulting full amplitude satisfies `∫ |F^(n)| ≤ C_n / δ^(n-1)` for every
order, with natural subtraction. Its mass and first variation are uniform.

An exact identity attaches this amplitude to the original Gaussian/logarithmic
Mellin slice at physical scale `N`. The final theorem applies to every
`N ≥ exp 1` and every admissible edge width `H`, with `δ = H/N`.
There is no assumed regularity budget or cancellation premise. Coupled Fourier
energy and moving signed transfer remain separate obligations.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
open GaloisForLFunctions.RHTower
namespace RHTower.BAGTrace

private theorem partial_smooth (k : ℕ) {f : ℝ→ℝ→ℂ} {z : ℝ×ℝ}
    (hf : ContDiffAt ℝ ∞ (Function.uncurry f) z) :
    ContDiffAt ℝ ∞ (fun w : ℝ×ℝ => iteratedDeriv k (f w.1) w.2) z := by
  induction k with
  | zero =>
    change ContDiffAt ℝ ∞ (fun w : ℝ×ℝ => f w.1 w.2) z at hf
    simpa only [iteratedDeriv_zero] using hf
  | succ k ih =>
    have hcomp : ContDiffAt ℝ ∞
        (fun w : (ℝ×ℝ)×ℝ => iteratedDeriv k (f w.1.1) w.2) (z,z.2) :=
      ih.comp (z,z.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have hd : ContDiffAt ℝ ∞
        (fun w : ℝ×ℝ => fderiv ℝ (iteratedDeriv k (f w.1)) w.2) z :=
      hcomp.fderiv contDiffAt_snd (by simp)
    simpa only [iteratedDeriv_succ,deriv] using hd.clm_apply
      (contDiffAt_const (c := (1 : ℝ)))

private def core (h x : ℝ) : ℂ :=
  smoothAFECutoff x / ((1+h*Real.log x : ℝ) : ℂ)

private theorem core_smooth {h x : ℝ} (hh : h∈Icc (0 : ℝ) 1)
    (hx : x∈Icc (1 : ℝ) 2) :
    ContDiffAt ℝ ∞ (Function.uncurry core) (h,x) := by
  have hxpos : 0<x := lt_of_lt_of_le zero_lt_one hx.1
  have hV : ContDiffAt ℝ ∞ smoothAFECutoff x :=
    contDiffOn_smoothAFECutoff_infty_pos.contDiffAt (Ioi_mem_nhds hxpos)
  have hl : ContDiffAt ℝ ∞ (fun w : ℝ×ℝ => Real.log w.2) (h,x) :=
    contDiffAt_snd.log hxpos.ne'
  have hd : ContDiffAt ℝ ∞ (fun w : ℝ×ℝ => ((1+w.1*Real.log w.2 : ℝ) : ℂ))
      (h,x) := Complex.ofRealCLM.contDiff.contDiffAt.comp (h,x)
        (contDiffAt_const.add (contDiffAt_fst.mul hl))
  have hlog : 0≤Real.log x := Real.log_nonneg hx.1
  have hn : (1+h*Real.log x : ℝ) ≠ 0 :=
    ne_of_gt (by nlinarith [mul_nonneg hh.1 hlog] : 0 < 1+h*Real.log x)
  change ContDiffAt ℝ ∞ (fun w : ℝ×ℝ => smoothAFECutoff w.2 /
    ((1+w.1*Real.log w.2 : ℝ) : ℂ)) (h,x)
  simpa only [div_eq_mul_inv,Pi.inv_apply,Function.comp_def] using
    (hV.comp (h,x) contDiffAt_snd).mul (hd.inv (Complex.ofReal_ne_zero.mpr hn))

private theorem core_derivative_bounds (k : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ h∈Icc (0 : ℝ) 1, ∀ x∈Icc (1 : ℝ) 2,
      ‖iteratedDeriv k (core h) x‖≤C := by
  have hc : ContinuousOn (fun w : ℝ×ℝ => iteratedDeriv k (core w.1) w.2)
      (Icc (0 : ℝ) 1 ×ˢ Icc (1 : ℝ) 2) := by
    intro w hw
    exact (partial_smooth k (core_smooth hw.1 hw.2)).continuousAt.continuousWithinAt
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc
  refine ⟨max C 0+1,by positivity,fun h hh x hx => ?_⟩
  exact (hC (h,x) ⟨hh,hx⟩).trans (by linarith [le_max_left C 0])

private theorem derivative_off_box {f : ℝ→ℂ}
    (hf : ∀x : ℝ, x∉Icc (1 : ℝ) 2 → f x=0) (n : ℕ)
    {x : ℝ} (hx : x∉Icc (1 : ℝ) 2) : iteratedDeriv n f x=0 := by
  have hs : tsupport f⊆Icc (1 : ℝ) 2 :=
    closure_minimal (Function.support_subset_iff'.mpr hf) isClosed_Icc
  rw [iteratedDeriv_eq_iteratedFDeriv]
  have hn : x∉Function.support (iteratedFDeriv ℝ n f) :=
    fun h => hx (hs (support_iteratedFDeriv_subset n h))
  simp [Function.notMem_support.mp hn]

private def cutC (δ x : ℝ) : ℂ := (bagCubicControlledCutoff δ x : ℂ)

private theorem cut_smooth (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) :
    ContDiff ℝ ∞ (cutC δ.1) :=
  Complex.ofRealCLM.contDiff.comp (bagCubicControlledCutoff_properties δ).1

private theorem cut_off (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)})
    {x : ℝ} (hx : x∉Icc (1 : ℝ) 2) : cutC δ.1 x=0 := by
  have hz := (bagCubicControlledCutoff_properties δ).2.2.2.1 x
    (fun h => hx ⟨h.1.le,h.2.le⟩)
  simp only [cutC,hz,Complex.ofReal_zero]

private theorem cut_integrable (n : ℕ)
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) :
    Integrable (fun x : ℝ => ‖iteratedDeriv n (cutC δ.1) x‖) := by
  exact (GaloisForLFunctions.HTGeometry.integrable_iteratedDeriv_blockWindowC n
    (p := 1+δ.1) (q := 2-δ.1) δ.2.1).norm

private theorem cut_mass (n : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)},
      (∫x : ℝ, ‖iteratedDeriv n (cutC δ.1) x‖)≤C/δ.1^(n-1) := by
  cases n with
  | zero =>
    refine ⟨1,zero_lt_one,fun δ => ?_⟩
    simp only [iteratedDeriv_zero,Nat.zero_sub,pow_zero,div_one]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (1 : ℝ) 2)
      (fun x hx => by rw [cut_off δ hx,norm_zero])]
    calc (∫ x : ℝ in Icc (1 : ℝ) 2, ‖cutC δ.1 x‖)
        ≤ ∫ _ : ℝ in Icc (1 : ℝ) 2, (1 : ℝ) :=
          setIntegral_mono_on (by simpa using (cut_integrable 0 δ).integrableOn)
            (integrableOn_const isCompact_Icc.measure_lt_top.ne) measurableSet_Icc
            (fun x _ => by
              rw [cutC,Complex.norm_real,Real.norm_eq_abs,
                abs_of_nonneg ((bagCubicControlledCutoff_properties δ).2.2.1 x).1]
              exact ((bagCubicControlledCutoff_properties δ).2.2.1 x).2)
      _ = 1 := by norm_num
  | succ n =>
    obtain ⟨C,hC,hb⟩ := bagCubicControlledCutoff_derivative_budgets n
    refine ⟨C,hC,fun δ => ?_⟩
    have heq := GaloisForLFunctions.iteratedDeriv_ofReal_comp
      (bagCubicControlledCutoff_properties δ).1 (n+1)
    change (∫x : ℝ, ‖iteratedDeriv (n+1)
      (fun x : ℝ => (bagCubicControlledCutoff δ.1 x : ℂ)) x‖)≤_
    simp only [heq,Complex.norm_real,Nat.add_sub_cancel]
    exact (hb δ).2

/-- Full normalized Gaussian/logarithmic slice with the selected relative cutoff. -/
def bagCubicNormalizedSlice (δ h x : ℝ) : ℂ := cutC δ x*core h x

private theorem slice_off (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)})
    (h : ℝ) {x : ℝ} (hx : x∉Icc (1 : ℝ) 2) : bagCubicNormalizedSlice δ.1 h x=0 := by
  simp only [bagCubicNormalizedSlice,cut_off δ hx,zero_mul]

private theorem slice_smooth (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)})
    (h : {r : ℝ // r∈Icc (0 : ℝ) 1}) : ContDiff ℝ ∞ (bagCubicNormalizedSlice δ.1 h.1) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x∈Icc (1 : ℝ) 2
  · exact (cut_smooth δ).contDiffAt.mul
      ((core_smooth h.2 hx).comp x (contDiffAt_const.prodMk contDiffAt_id))
  · have heq : bagCubicNormalizedSlice δ.1 h.1 =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
      filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hx] with y hy
      exact slice_off δ h.1 hy
    exact contDiffAt_const.congr_of_eventuallyEq heq

/-- Smoothness and exact fixed-band support of the full moving amplitude. -/
theorem bagCubicNormalizedSlice_properties
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1}) :
    ContDiff ℝ ∞ (bagCubicNormalizedSlice δ.1 h.1) ∧
    (∀x : ℝ, x∉Icc (1 : ℝ) 2 → bagCubicNormalizedSlice δ.1 h.1 x=0) :=
  ⟨slice_smooth δ h,fun _ hx => slice_off δ h.1 hx⟩

private theorem slice_integrable (n : ℕ)
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1}) :
    Integrable (fun x : ℝ => ‖iteratedDeriv n (bagCubicNormalizedSlice δ.1 h.1) x‖) := by
  have hs : HasCompactSupport (iteratedDeriv n (bagCubicNormalizedSlice δ.1 h.1)) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (Function.support_subset_iff'.mpr (fun x hx => derivative_off_box
        (fun y hy => slice_off δ h.1 hy) n hx))
  exact ((slice_smooth δ h).continuous_iteratedDeriv n (by exact_mod_cast (le_top : (n : ℕ∞)≤⊤))).integrable_of_hasCompactSupport
    hs |>.norm

/-- All-order L1 derivative budgets, uniform in the logarithmic parameter and edge width. -/
theorem bagCubicNormalizedSlice_derivative_budgets (n : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)},
      ∀h : {r : ℝ // r∈Icc (0 : ℝ) 1},
      Integrable (fun x : ℝ => ‖iteratedDeriv n (bagCubicNormalizedSlice δ.1 h.1) x‖) ∧
      (∫x : ℝ, ‖iteratedDeriv n (bagCubicNormalizedSlice δ.1 h.1) x‖)≤C/δ.1^(n-1) := by
  choose A hA hAc using cut_mass
  choose B hB hBc using core_derivative_bounds
  let C := ∑i∈Finset.range (n+1), (n.choose i : ℝ)*A i*B (n-i)
  have hC : 0≤C := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i).le) (hB (n-i)).le)
  refine ⟨C+1,by positivity,fun δ h => ⟨slice_integrable n δ h,?_⟩⟩
  let M : ℝ→ℝ := fun x => ∑i∈Finset.range (n+1),
    (n.choose i : ℝ)*‖iteratedDeriv i (cutC δ.1) x‖*B (n-i)
  have hMi (i : ℕ) : Integrable (fun x : ℝ =>
      (n.choose i : ℝ)*‖iteratedDeriv i (cutC δ.1) x‖*B (n-i)) :=
    ((cut_integrable i δ).const_mul _).mul_const _
  have hM : Integrable M := integrable_finsetSum _ (fun i _ => hMi i)
  have hpoint (x : ℝ) : ‖iteratedDeriv n (bagCubicNormalizedSlice δ.1 h.1) x‖≤M x := by
    by_cases hx : x∈Icc (1 : ℝ) 2
    · have hcore : ContDiffAt ℝ (n : ℕ) (core h.1) x :=
        ((core_smooth h.2 hx).comp x (contDiffAt_const.prodMk contDiffAt_id)).of_le
          (by exact_mod_cast (le_top : (n : ℕ∞)≤⊤))
      change ‖iteratedDeriv n (cutC δ.1 * core h.1) x‖≤_
      rw [iteratedDeriv_mul ((cut_smooth δ).of_le (by exact_mod_cast (le_top : (n : ℕ∞)≤⊤))).contDiffAt hcore]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i hi => ?_))
      simp only [norm_mul,Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left (hBc (n-i) h.1 h.2 x hx) (by positivity)
    · rw [derivative_off_box (fun y hy => slice_off δ h.1 hy) n hx,norm_zero]
      exact Finset.sum_nonneg (fun i _ =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (hB (n-i)).le)
  calc (∫x : ℝ, ‖iteratedDeriv n (bagCubicNormalizedSlice δ.1 h.1) x‖)
      ≤ ∫x : ℝ, M x := integral_mono (slice_integrable n δ h) hM hpoint
    _ = ∑i∈Finset.range (n+1),
        (n.choose i : ℝ)*(∫x : ℝ, ‖iteratedDeriv i (cutC δ.1) x‖)*B (n-i) := by
      rw [integral_finsetSum _ (fun i _ => hMi i)]
      simp only [integral_mul_const,integral_const_mul]
    _ ≤ ∑i∈Finset.range (n+1), (n.choose i : ℝ)*(A i/δ.1^(n-1))*B (n-i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i≤n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hp : δ.1^(n-1)≤δ.1^(i-1) := pow_le_pow_of_le_one δ.2.1.le
        (by linarith only [δ.2.2]) (Nat.sub_le_sub_right hin 1)
      have hb : (∫x : ℝ, ‖iteratedDeriv i (cutC δ.1) x‖)≤A i/δ.1^(n-1) :=
        (hAc i δ).trans (div_le_div_of_nonneg_left (hA i).le (pow_pos δ.2.1 _) hp)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb
        (Nat.cast_nonneg _)) (hB (n-i)).le
    _ = C/δ.1^(n-1) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ (C+1)/δ.1^(n-1) := div_le_div_of_nonneg_right (by linarith)
      (pow_nonneg δ.2.1.le _)


/-- Exact identification with the original physical Mellin slice; no asymptotic replacement. -/
theorem bagCubicNormalizedSlice_eq_actual (N : {r : ℝ // 1<r})
    (H : {r : ℝ // r∈Ioo (0 : ℝ) (N.1/2)}) (x : ℝ) :
    (Real.log N.1 : ℂ)*bagCubicMellinSliceValue N.1
      (bagCubicControlledBandCutoff N.1 H.1) 0 (N.1*x) =
      bagCubicNormalizedSlice (H.1/N.1) (1/Real.log N.1) x := by
  have hN : 0<N.1 := lt_trans zero_lt_one N.2
  let δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)} :=
    ⟨H.1/N.1,div_pos H.2.1 hN,(div_lt_iff₀ hN).mpr (by linarith only [H.2.2])⟩
  have heq : N.1*x/N.1=x := by field_simp
  simp only [bagCubicMellinSliceValue,bagCubicControlledBandCutoff,heq,
    neg_zero,zero_mul,bourgainOscillation,Complex.ofReal_zero,mul_zero,Complex.exp_zero,mul_one]
  by_cases hx : x∈Icc (1 : ℝ) 2
  · have hxp : 0<x := lt_of_lt_of_le zero_lt_one hx.1
    have hlog : Real.log N.1 ≠ 0 := (Real.log_pos N.2).ne'
    rw [Real.log_mul hN.ne' hxp.ne']
    dsimp only [bagCubicNormalizedSlice,cutC,core]
    have hn : (Real.log N.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog
    have hd : (1 : ℂ)+1/(Real.log N.1 : ℂ)*(Real.log x : ℂ) =
        ((Real.log N.1 : ℂ)+(Real.log x : ℂ))/(Real.log N.1 : ℂ) := by
      field_simp [hn]
    simp only [Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_one]
    rw [hd,div_div_eq_mul_div]
    ring
  · have hz := (bagCubicControlledCutoff_properties δ).2.2.2.1 x
      (fun hh => hx ⟨hh.1.le,hh.2.le⟩)
    change bagCubicControlledCutoff (H.1/N.1) x=0 at hz
    simp only [hz,Complex.ofReal_zero,zero_mul,zero_div,mul_zero]
    exact (slice_off δ (1/Real.log N.1) hx).symm

/-- The original selected Gaussian/logarithmic slice has every required derivative budget. -/
theorem bagCubicControlledSlice_derivative_budgets (n : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀N : {r : ℝ // Real.exp 1≤r},
      ∀H : {r : ℝ // r∈Ioo (0 : ℝ) (N.1/2)},
      let f : ℝ→ℂ := fun x => (Real.log N.1 : ℂ)*bagCubicMellinSliceValue N.1
        (bagCubicControlledBandCutoff N.1 H.1) 0 (N.1*x)
      Integrable (fun x : ℝ => ‖iteratedDeriv n f x‖) ∧
      (∫x : ℝ, ‖iteratedDeriv n f x‖)≤C/(H.1/N.1)^(n-1) := by
  obtain ⟨C,hC,hb⟩ := bagCubicNormalizedSlice_derivative_budgets n
  refine ⟨C,hC,fun N H => ?_⟩
  have hN1 : 1<N.1 := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr zero_lt_one) N.2
  have hN : 0<N.1 := lt_trans zero_lt_one hN1
  have hL : 1≤Real.log N.1 := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) N.2
  let δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)} :=
    ⟨H.1/N.1,div_pos H.2.1 hN,(div_lt_iff₀ hN).mpr (by linarith only [H.2.2])⟩
  let h : {r : ℝ // r∈Icc (0 : ℝ) 1} :=
    ⟨1/Real.log N.1,div_nonneg zero_le_one (by linarith),
      (div_le_iff₀ (Real.log_pos hN1)).mpr (by simpa using hL)⟩
  have heq : (fun x : ℝ => (Real.log N.1 : ℂ)*bagCubicMellinSliceValue N.1
      (bagCubicControlledBandCutoff N.1 H.1) 0 (N.1*x)) = bagCubicNormalizedSlice δ.1 h.1 :=
    funext (bagCubicNormalizedSlice_eq_actual ⟨N.1,hN1⟩ H)
  dsimp only
  rw [heq]
  exact hb δ h


end RHTower.BAGTrace
