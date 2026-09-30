import GaloisForLFunctions.RHTower.LiClockCriticalGaussianCutoff
import GaloisForLFunctions.RHTower.LiClockPairedEtaInfinitePartitionBorel
import GaloisForLFunctions.RHTower.LiClockPairedEtaInfinitePartitionBoundary
import Mathlib.Tactic

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower

def liClockPairedEtaCriticalQuarterClock (N : ℕ) : ℝ :=
  Real.log (2*(N : ℝ))/4

def liClockPairedEtaCriticalInteriorClock (N : ℕ) : ℝ :=
  Real.log (2*(N : ℝ))/4-1

private theorem cs_compact_even_integral {f : ℝ → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hf : Continuous f) (he : ∀ x : ℝ, f (-x) = f x)
    (hz : ∀ x : ℝ, L ≤ |x| → f x = 0) :
    (∫ x : ℝ, f x) = 2 * ∫ x in Icc 0 L, f x := by
  have hcut : (∫ x in Icc (-L) L, f x) = ∫ x : ℝ, f x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    apply hz x
    by_contra h
    have ha : |x| < L := lt_of_not_ge h
    exact hx ⟨(abs_lt.mp ha).1.le, (abs_lt.mp ha).2.le⟩
  have hneg : (∫ x in (-L)..0, f x) = ∫ x in (0 : ℝ)..L, f x := by
    have h := intervalIntegral.integral_comp_neg (f := f) (a := (0 : ℝ)) (b := L)
    simpa only [he, neg_zero] using h.symm
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (μ := (volume : Measure ℝ))
    (hf.intervalIntegrable (-L) 0) (hf.intervalIntegrable 0 L)
  rw [← hcut, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show -L ≤ L by linarith), ← hadd, hneg,
    intervalIntegral.integral_of_le hL, ← integral_Icc_eq_integral_Ioc]
  ring


/- Prepared source bridge; requires certified AngularKernel and existing finite sources.
   No unfinished dependency import or compiler claim is attached to this fragment. -/

private theorem cs_summable_even (w : ℝ) :
    Summable (fun j : ℕ => w^(2*j) / (((2*j).factorial : ℝ)^2)) := by
  have hr : Summable (fun n : ℕ => w^n / ((n.factorial : ℝ)^2)) := by
    apply Complex.summable_ofReal.mp
    simpa only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast] using
      (summable_norm_liClockCriticalScalarTermComplex (w : ℂ)).of_norm
  exact hr.comp_injective (fun x y h => by omega)

private theorem cs_even_kernel_neg (w : ℝ) :
    liClockCriticalEvenKernel (-w) = liClockCriticalEvenKernel w := by
  unfold liClockCriticalEvenKernel
  apply tsum_congr
  intro j
  simp only [pow_mul, neg_sq]

private theorem cs_compact_mul_integrable {g : ℝ → ℝ} {L : ℝ}
    (hg : Continuous g) (hz : ∀ x : ℝ, L ≤ |x| → g x = 0)
    (φ : ℝ → ℝ) (hφ : Continuous φ) : Integrable (fun x => g x * φ x) := by
  have hs : Function.support (fun x => g x * φ x) ⊆ Icc (-L) L := by
    intro x hx
    have hxg : g x ≠ 0 := (mul_ne_zero_iff.mp hx).1
    have hxL : |x| < L := lt_of_not_ge (fun h => hxg (hz x h))
    exact ⟨(abs_lt.mp hxL).1.le, (abs_lt.mp hxL).2.le⟩
  exact (integrableOn_iff_integrable_of_support_subset hs).mp
    ((hg.mul hφ).continuousOn.integrableOn_Icc)

private theorem cs_borel_raw_integral
    {g : ℝ → ℝ} {M : ℕ → ℝ} {L Z B t : ℝ}
    (hL : 0 ≤ L) (hZ : Z ≠ 0) (ht : 0 ≤ t)
    (hg : Continuous g) (hp : ∀ x : ℝ, 0 ≤ g x)
    (he : ∀ x : ℝ, g (-x) = g x) (hz : ∀ x : ℝ, L ≤ |x| → g x = 0)
    (hm : ∀ j : ℕ, (∫ x : ℝ, x^(2*j)*g x) = Z^2*M j)
    (hb : HasSum (fun j : ℕ => M j*t^(2*j)/((2*j).factorial : ℝ)^2) B) :
    B = (2/Z^2) * ∫ x in Icc 0 L, g x * liClockCriticalEvenKernel (t*x) := by
  let f : ℕ → ℝ → ℝ := fun j x =>
    g x * (t*x)^(2*j) / ((2*j).factorial : ℝ)^2
  have hfpos : ∀ j x, 0 ≤ f j x := by
    intro j x
    dsimp [f]
    rw [mul_pow]
    apply div_nonneg
    · exact mul_nonneg (hp x) (mul_nonneg (pow_nonneg ht _) (by
        rw [pow_mul]
        positivity))
    · positivity
  have hfsum : ∀ x, HasSum (fun j => f j x)
      (g x * liClockCriticalEvenKernel (t*x)) := by
    intro x
    apply ((cs_summable_even (t*x)).hasSum.mul_left (g x)).congr_fun
    intro j
    dsimp [f]
    ring
  have hfc : Continuous (fun x => g x * liClockCriticalEvenKernel (t*x)) :=
    hg.mul (continuous_liClockCriticalEvenKernel.comp (continuous_const.mul continuous_id))
  have hfi : Integrable (fun x => g x * liClockCriticalEvenKernel (t*x)) :=
    cs_compact_mul_integrable hg hz _
      (continuous_liClockCriticalEvenKernel.comp (continuous_const.mul continuous_id))
  have hfb : Integrable (fun x => ∑' j, f j x) :=
    hfi.congr (Filter.Eventually.of_forall (fun x => (hfsum x).tsum_eq.symm))
  have hsum : HasSum (fun j => ∫ x : ℝ, f j x)
      (∫ x : ℝ, g x * liClockCriticalEvenKernel (t*x)) := by
    apply MeasureTheory.hasSum_integral_of_dominated_convergence f
    · intro j
      have hc : Continuous (f j) := by
        dsimp [f]
        exact (hg.mul ((continuous_const.mul continuous_id).pow _)).div_const _
      exact hc.aestronglyMeasurable
    · intro j
      exact Filter.Eventually.of_forall (fun x => le_of_eq (Real.norm_of_nonneg (hfpos j x)))
    · exact Filter.Eventually.of_forall (fun x => (hfsum x).summable)
    · exact hfb
    · exact Filter.Eventually.of_forall hfsum
  have hterm (j : ℕ) : (∫ x : ℝ, f j x) =
      Z^2 * (M j*t^(2*j)/((2*j).factorial : ℝ)^2) := by
    have heq : f j = fun x : ℝ =>
        (t^(2*j)/((2*j).factorial : ℝ)^2) * (x^(2*j)*g x) := by
      funext x
      dsimp [f]
      rw [mul_pow]
      ring
    rw [heq, integral_const_mul, hm j]
    ring
  have hsumB : HasSum (fun j => ∫ x : ℝ, f j x) (Z^2*B) := by
    apply (hb.mul_left (Z^2)).congr_fun
    exact hterm
  have hfold : (∫ x : ℝ, g x * liClockCriticalEvenKernel (t*x)) =
      2 * ∫ x in Icc 0 L, g x * liClockCriticalEvenKernel (t*x) := by
    apply cs_compact_even_integral hL hfc
    · intro x
      rw [he x, show t*(-x) = -(t*x) by ring, cs_even_kernel_neg]
    · intro x hx
      rw [hz x hx, zero_mul]
  have hZ2 : Z^2 ≠ 0 := pow_ne_zero _ hZ
  calc
    B = (Z^2*B)/Z^2 := by field_simp
    _ = (2*(∫ x in Icc 0 L, g x * liClockCriticalEvenKernel (t*x)))/Z^2 := by
      rw [← hsum.unique hsumB, hfold]
    _ = _ := by ring

theorem liClockPairedEtaPartitionBorelKernel_eq_critical_integral
    {N : ℕ} (hN : 0<N) {t : ℝ} (ht : 0≤t) :
  liClockPairedEtaPartitionBorelKernel N t =
    (2/liClockPairedEtaPartitionNormalizer N^2) *
      ∫ r in Set.Icc 0 (Real.log (2*(N : ℝ))),
        liClockPairedEtaPartitionRawDifferenceDensity N r *
          liClockCriticalEvenKernel (t*r) := by
  have hL : 0 ≤ Real.log (2*(N : ℝ)) := by
    apply Real.log_nonneg
    have hNr : 1 ≤ (N : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hN.ne')
    linarith
  apply cs_borel_raw_integral hL (liClockPairedEtaPartitionNormalizer_pos hN).ne' ht
    (continuous_liClockPairedEtaPartitionRawDifferenceDensity N)
    (liClockPairedEtaPartitionRawDifferenceDensity_nonneg N)
    (liClockPairedEtaPartitionRawDifferenceDensity_even N)
    (fun _ hx => liClockPairedEtaPartitionRawDifferenceDensity_zero_of_log_le_abs hx)
    (liClockPairedEtaPartitionRawDifferenceDensity_moment hN)
  simpa only [liClockPairedEtaPartitionBorelKernel_eq_tsum] using
    (summable_liClockPairedEtaPartitionBorelTerm hN t).hasSum

theorem liClockPairedEtaContiguousBorelKernel_eq_critical_integral
    {L t : ℝ} (hL : 0<L) (ht : 0≤t) :
  liClockPairedEtaContiguousBorelKernel L t =
    (2/liClockPairedEtaContiguousPartitionNormalizer L^2) *
      ∫ r in Set.Icc 0 L,
        liClockPairedEtaContiguousRawDifferenceDensity L r *
          liClockCriticalEvenKernel (t*r) := by
  apply cs_borel_raw_integral hL.le (liClockPairedEtaContiguousPartitionNormalizer_pos hL).ne' ht
    (continuous_liClockPairedEtaContiguousRawDifferenceDensity L)
    (liClockPairedEtaContiguousRawDifferenceDensity_nonneg L)
    (liClockPairedEtaContiguousRawDifferenceDensity_even L)
    (fun _ hx => liClockPairedEtaContiguousRawDifferenceDensity_zero_of_le_abs hx)
    (liClockPairedEtaContiguousRawDifferenceDensity_moment hL)
  have hs := (summable_liClockPairedEtaContiguousBorelTerm hL t).hasSum
  change HasSum _ (liClockPairedEtaContiguousBorelKernel L t) at hs
  apply hs.congr_fun
  intro j
  unfold liClockPairedEtaContiguousBorelCoefficient
  ring

private theorem cs_contiguous_raw_closed {L r : ℝ} (hr : r ∈ Icc 0 L) :
    liClockPairedEtaContiguousRawDifferenceDensity L r =
      Real.exp (-r/2) - Real.exp (-L+r/2) := by
  by_cases h : r < L
  · rw [liClockPairedEtaContiguousRawDifferenceDensity_eq_of_nonneg hr.1 h]
    have he : Real.exp (-r/2) * Real.exp (r-L) = Real.exp (-L+r/2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    nlinarith
  · have heq : r = L := le_antisymm hr.2 (le_of_not_gt h)
    rw [liClockPairedEtaContiguousRawDifferenceDensity_zero_of_le_abs
      (by simpa only [abs_of_nonneg hr.1] using heq.ge)]
    subst r
    rw [show -L+L/2 = -L/2 by ring, sub_self]

private theorem cs_actual_raw_error_point {N : ℕ} (hN : 0 < N) {r : ℝ}
    (hr : r ∈ Icc 0 (Real.log (2*(N:ℝ)))) :
    |liClockPairedEtaPartitionRawDifferenceDensity N r -
      (Real.log 2/2)*Real.exp (-r/2)| ≤
      Real.exp (-Real.log (2*(N:ℝ))+r/2) +
        (Real.pi^2/16)*Real.exp (-3*r/2) := by
  have hdef := liClockPairedEtaInfinitePartitionRawDifferenceDensity_sub_finite_le hN r
  rw [liClockPairedEtaHalfLineRawDifferenceDensity_sub_contiguous,
    abs_of_nonneg hr.1] at hdef
  have hd : liClockPairedEtaInfinitePartitionRawDifferenceDensity r -
      liClockPairedEtaPartitionRawDifferenceDensity N r ≤
      Real.exp (-Real.log (2*(N:ℝ))+r/2) := by
    by_cases h : r < Real.log (2*(N:ℝ))
    · simpa only [if_pos h, sub_eq_add_neg, add_comm] using hdef.2
    · have heq : r = Real.log (2*(N:ℝ)) := le_antisymm hr.2 (le_of_not_gt h)
      rw [if_neg h] at hdef
      simpa only [← heq, show -r+r/2 = -r/2 by ring] using hdef.2
  have ha : |liClockPairedEtaPartitionRawDifferenceDensity N r -
      liClockPairedEtaInfinitePartitionRawDifferenceDensity r| ≤
      Real.exp (-Real.log (2*(N:ℝ))+r/2) := by
    rw [abs_sub_comm, abs_of_nonneg hdef.1]
    exact hd
  have ht := liClockPairedEtaInfinitePartitionRawDifferenceDensity_error_le r
  rw [abs_of_nonneg hr.1] at ht
  exact (abs_sub_le _ _ _).trans (add_le_add ha ht)

private theorem cs_actual_raw_error_integral {N : ℕ} (hN : 0 < N)
    {t : ℝ} (ht : 0 ≤ t) :
    |∫ r in Icc 0 (Real.log (2*(N:ℝ))),
      (liClockPairedEtaPartitionRawDifferenceDensity N r -
        (Real.log 2/2)*Real.exp (-r/2))*liClockCriticalEvenKernel (t*r)| ≤
      (∫ r in Icc 0 (Real.log (2*(N:ℝ))),
        Real.exp (-Real.log (2*(N:ℝ))+r/2)*liClockCriticalEvenKernel (t*r)) +
      (Real.pi^2/16)*(2/3)*Real.cosh (2*t/3) := by
  let L : ℝ := Real.log (2*(N:ℝ))
  let f : ℝ → ℝ := fun r =>
    (liClockPairedEtaPartitionRawDifferenceDensity N r -
      (Real.log 2/2)*Real.exp (-r/2))*liClockCriticalEvenKernel (t*r)
  let b : ℝ → ℝ := fun r => Real.exp (-L+r/2)*liClockCriticalEvenKernel (t*r)
  let d : ℝ → ℝ := fun r => Real.exp (-3*r/2)*liClockCriticalEvenKernel (t*r)
  have hF : Continuous (fun r : ℝ => liClockCriticalEvenKernel (t*r)) :=
    continuous_liClockCriticalEvenKernel.comp (by fun_prop)
  have hf : Continuous f :=
    ((continuous_liClockPairedEtaPartitionRawDifferenceDensity N).sub
      (continuous_const.mul (by fun_prop))).mul hF
  have hb : Continuous b := (by fun_prop : Continuous (fun r : ℝ => Real.exp (-L+r/2))).mul hF
  have hd : Continuous d := (by fun_prop : Continuous (fun r : ℝ => Real.exp (-3*r/2))).mul hF
  have hfi : IntegrableOn (fun r => |f r|) (Icc 0 L) := hf.abs.integrableOn_Icc
  have hbi : IntegrableOn b (Icc 0 L) := hb.integrableOn_Icc
  have hdi : IntegrableOn d (Icc 0 L) := hd.integrableOn_Icc
  have hm : (∫ r in Icc 0 L, |f r|) ≤
      ∫ r in Icc 0 L, b r + (Real.pi^2/16)*d r := by
    apply setIntegral_mono_on hfi (hbi.add (hdi.const_mul _)) measurableSet_Icc
    intro r hr
    change |f r| ≤ b r + (Real.pi^2/16)*d r
    have hp := mul_le_mul_of_nonneg_right (cs_actual_raw_error_point hN hr)
      (liClockCriticalEvenKernel_nonneg (t*r))
    simpa only [f, b, d, L, abs_mul,
      abs_of_nonneg (liClockCriticalEvenKernel_nonneg (t*r)), add_mul, mul_assoc] using hp
  have hneg (r : ℝ) : -3*r/2 = -(3/2:ℝ)*r := by ring
  have hfull : IntegrableOn d (Ioi 0) := by
    simpa only [d, hneg] using
      (integrableOn_liClockCriticalEvenKernel_decay (a := (3/2:ℝ)) (by norm_num) ht)
  have htail : (∫ r in Icc 0 L, d r) ≤ (2/3)*Real.cosh (2*t/3) := by
    rw [integral_Icc_eq_integral_Ioc]
    have hmono : (∫ r in Ioc 0 L, d r) ≤ ∫ r in Ioi 0, d r :=
      setIntegral_mono_set hfull
        (Filter.Eventually.of_forall (fun r => mul_nonneg (Real.exp_pos _).le
          (liClockCriticalEvenKernel_nonneg (t*r))))
        (Filter.Eventually.of_forall (fun r hr => hr.1))
    have he := liClockCriticalEvenKernel_decay_integral (a := (3/2:ℝ)) (by norm_num) ht
    have he' : (∫ r in Ioi 0, d r) = (2/3)*Real.cosh (2*t/3) := by
      simpa only [d, hneg, show (1/(3/2):ℝ)=2/3 by norm_num,
        show t/(3/2)=2*t/3 by ring] using he
    exact he' ▸ hmono
  change |∫ r in Icc 0 L, f r| ≤ (∫ r in Icc 0 L, b r) + _
  calc
    _ ≤ ∫ r in Icc 0 L, |f r| := abs_integral_le_integral_abs
    _ ≤ ∫ r in Icc 0 L, b r + (Real.pi^2/16)*d r := hm
    _ = (∫ r in Icc 0 L, b r) + (Real.pi^2/16)*(∫ r in Icc 0 L, d r) := by
      rw [integral_add hbi (hdi.const_mul _), integral_const_mul]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left htail (show 0 ≤ Real.pi^2/16 by positivity)
      nlinarith

private theorem cs_cutoff_mass_raw {t L : ℝ} (ht : 0 ≤ t) (hL : 0 < L) :
    Real.exp (-2*t) * (∫ r in Icc 0 L,
      Real.exp (-r/2)*liClockCriticalEvenKernel (t*r)) =
      2*(liClockCriticalCutoffMeasure t).real (Icc 0 L) := by
  rw [liClockCriticalCutoffMeasure_real_Icc ht hL]
  have he : liClockCriticalEvenRadialDensity t = fun r : ℝ =>
      ((1/2)*Real.exp (-2*t))*(Real.exp (-r/2)*liClockCriticalEvenKernel (t*r)) := by
    funext r
    unfold liClockCriticalEvenRadialDensity
    rw [show -2*t-r/2 = -2*t+(-r/2) by ring, Real.exp_add]
    ring
  rw [he, integral_const_mul]
  ring

theorem liClockPairedEtaContiguousBorelKernel_scaled_eq_cutoff
    {L t : ℝ} (hL : 0<L) (ht : 0≤t) :
    Real.exp (-2*t)*liClockPairedEtaContiguousBorelKernel L t =
      (4/liClockPairedEtaContiguousPartitionNormalizer L^2) *
        ((liClockCriticalCutoffMeasure t).real (Set.Icc 0 L)-
          liClockCriticalCutoffLoss t L) := by
  have hF : Continuous (fun r : ℝ => liClockCriticalEvenKernel (t*r)) :=
    continuous_liClockCriticalEvenKernel.comp (by fun_prop)
  have ha : IntegrableOn (fun r : ℝ =>
      Real.exp (-r/2)*liClockCriticalEvenKernel (t*r)) (Icc 0 L) :=
    ((by fun_prop : Continuous (fun r : ℝ => Real.exp (-r/2))).mul hF).integrableOn_Icc
  have hb : IntegrableOn (fun r : ℝ =>
      Real.exp (-L+r/2)*liClockCriticalEvenKernel (t*r)) (Icc 0 L) :=
    ((by fun_prop : Continuous (fun r : ℝ => Real.exp (-L+r/2))).mul hF).integrableOn_Icc
  have hi : (∫ r in Icc 0 L, liClockPairedEtaContiguousRawDifferenceDensity L r *
      liClockCriticalEvenKernel (t*r)) =
      (∫ r in Icc 0 L, Real.exp (-r/2)*liClockCriticalEvenKernel (t*r)) -
      (∫ r in Icc 0 L, Real.exp (-L+r/2)*liClockCriticalEvenKernel (t*r)) := by
    rw [← integral_sub ha hb]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [cs_contiguous_raw_closed hr]
    ring
  rw [liClockPairedEtaContiguousBorelKernel_eq_critical_integral hL ht, hi]
  have hm := cs_cutoff_mass_raw ht hL
  have hl := liClockCriticalCutoffLoss_raw_integral ht hL
  calc
    _ = (2/liClockPairedEtaContiguousPartitionNormalizer L^2) *
        (Real.exp (-2*t)*(∫ r in Icc 0 L, Real.exp (-r/2)*liClockCriticalEvenKernel (t*r)) -
          Real.exp (-2*t)*(∫ r in Icc 0 L, Real.exp (-L+r/2)*liClockCriticalEvenKernel (t*r))) := by ring
    _ = _ := by rw [hm, hl]; ring

theorem liClockPairedEtaPartitionBorelKernel_scaled_critical_error_le
    {N : ℕ} (hN : 0<N) {t : ℝ} (ht : 0≤t) :
    |Real.exp (-2*t)*liClockPairedEtaPartitionBorelKernel N t -
      (2*Real.log 2/liClockPairedEtaPartitionNormalizer N^2) *
        (liClockCriticalCutoffMeasure t).real (Set.Icc 0 (Real.log (2*(N : ℝ))))| ≤
      (4/liClockPairedEtaPartitionNormalizer N^2) *
        liClockCriticalCutoffLoss t (Real.log (2*(N : ℝ))) +
      (4*(Real.pi^2/16)/(3*liClockPairedEtaPartitionNormalizer N^2)) *
        Real.exp (-2*t)*Real.cosh (2*t/3) := by
  let L : ℝ := Real.log (2*(N:ℝ))
  let Z : ℝ := liClockPairedEtaPartitionNormalizer N
  have hL : 0 < L := by
    apply Real.log_pos
    have hNr : 1 ≤ (N:ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hN.ne')
    linarith
  have hF : Continuous (fun r : ℝ => liClockCriticalEvenKernel (t*r)) :=
    continuous_liClockCriticalEvenKernel.comp (by fun_prop)
  have ha : IntegrableOn (fun r : ℝ =>
      liClockPairedEtaPartitionRawDifferenceDensity N r*liClockCriticalEvenKernel (t*r)) (Icc 0 L) :=
    ((continuous_liClockPairedEtaPartitionRawDifferenceDensity N).mul hF).integrableOn_Icc
  have hb : IntegrableOn (fun r : ℝ =>
      Real.exp (-r/2)*liClockCriticalEvenKernel (t*r)) (Icc 0 L) :=
    ((by fun_prop : Continuous (fun r : ℝ => Real.exp (-r/2))).mul hF).integrableOn_Icc
  have hi : (∫ r in Icc 0 L, (liClockPairedEtaPartitionRawDifferenceDensity N r -
      (Real.log 2/2)*Real.exp (-r/2))*liClockCriticalEvenKernel (t*r)) =
      (∫ r in Icc 0 L, liClockPairedEtaPartitionRawDifferenceDensity N r*liClockCriticalEvenKernel (t*r)) -
      (Real.log 2/2)*(∫ r in Icc 0 L, Real.exp (-r/2)*liClockCriticalEvenKernel (t*r)) := by
    rw [← integral_const_mul, ← integral_sub ha (hb.const_mul _)]
    apply integral_congr_ae
    exact ae_of_all _ (fun r => by ring)
  have hm := cs_cutoff_mass_raw ht hL
  have hm' : (liClockCriticalCutoffMeasure t).real (Icc 0 L) =
      (Real.exp (-2*t)*(∫ r in Icc 0 L, Real.exp (-r/2)*liClockCriticalEvenKernel (t*r)))/2 := by
    linarith
  have he : Real.exp (-2*t)*liClockPairedEtaPartitionBorelKernel N t -
      (2*Real.log 2/Z^2)*(liClockCriticalCutoffMeasure t).real (Icc 0 L) =
      (2*Real.exp (-2*t)/Z^2) * (∫ r in Icc 0 L,
        (liClockPairedEtaPartitionRawDifferenceDensity N r -
          (Real.log 2/2)*Real.exp (-r/2))*liClockCriticalEvenKernel (t*r)) := by
    rw [liClockPairedEtaPartitionBorelKernel_eq_critical_integral hN ht, hi, hm']
    dsimp only [L, Z]
    ring
  have hp : 0 ≤ 2*Real.exp (-2*t)/Z^2 := by positivity
  change |Real.exp (-2*t)*liClockPairedEtaPartitionBorelKernel N t -
    (2*Real.log 2/Z^2)*(liClockCriticalCutoffMeasure t).real (Icc 0 L)| ≤ _
  rw [he, abs_mul, abs_of_nonneg hp]
  calc
    _ ≤ (2*Real.exp (-2*t)/Z^2) *
        ((∫ r in Icc 0 L, Real.exp (-L+r/2)*liClockCriticalEvenKernel (t*r)) +
          (Real.pi^2/16)*(2/3)*Real.cosh (2*t/3)) :=
      mul_le_mul_of_nonneg_left (cs_actual_raw_error_integral hN ht) hp
    _ = (2/Z^2)*(Real.exp (-2*t)*(∫ r in Icc 0 L,
          Real.exp (-L+r/2)*liClockCriticalEvenKernel (t*r))) +
        (4*(Real.pi^2/16)/(3*Z^2))*Real.exp (-2*t)*Real.cosh (2*t/3) := by ring
    _ = _ := by rw [liClockCriticalCutoffLoss_raw_integral ht hL]; dsimp only [L, Z]; ring

private theorem cs_exp_cosh_tendsto {t : ℕ → ℝ}
    (ht : Tendsto t atTop atTop) :
    Tendsto (fun n => Real.exp (-2*t n)*Real.cosh (2*t n/3))
      atTop (nhds 0) := by
  have h1 : Tendsto (fun n => Real.exp ((-4/3:ℝ)*t n)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (ht.const_mul_atTop_of_neg (by norm_num))
  have h2 : Tendsto (fun n => Real.exp ((-8/3:ℝ)*t n)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (ht.const_mul_atTop_of_neg (by norm_num))
  have h := (h1.add h2).div_const 2
  norm_num only [zero_add, zero_div] at h
  apply h.congr
  intro n
  rw [Real.cosh_eq, ← mul_div_assoc, mul_add, ← Real.exp_add, ← Real.exp_add]
  congr 2 <;> congr 1 <;> ring

private theorem cs_scaled_ratio
    {A U t : ℕ → ℝ} {a b : ℝ}
    (ha : Tendsto (fun n => Real.exp (-2*t n)*A n) atTop (nhds a))
    (hb : Tendsto (fun n => Real.exp (-2*t n)*U n) atTop (nhds b))
    (hb0 : b ≠ 0) :
    Tendsto (fun n => A n/U n) atTop (nhds (a/b)) := by
  exact (ha.div hb hb0).congr (fun n =>
    mul_div_mul_left (A n) (U n) (Real.exp_ne_zero _))

private theorem cs_negative_gap
    {A U t : ℕ → ℝ} {a b : ℝ}
    (ht : Tendsto t atTop atTop)
    (ha : Tendsto (fun n => Real.exp (-2*t n)*A n) atTop (nhds a))
    (hb : Tendsto (fun n => Real.exp (-2*t n)*U n) atTop (nhds b))
    (hab : a < b) :
    Tendsto (fun n => A n-U n) atTop atBot := by
  have hd : Tendsto (fun n => Real.exp (-2*t n)*(A n-U n)) atTop
      (nhds (a-b)) := (ha.sub hb).congr (fun n => by ring)
  have he : Tendsto (fun n => Real.exp (2*t n)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (ht.const_mul_atTop (by norm_num))
  exact (he.atTop_mul_neg (sub_neg.mpr hab) hd).congr (fun n => by
    rw [← mul_assoc, ← Real.exp_add]
    have hx : 2*t n + -2*t n = 0 := by ring
    rw [hx]
    simp)


theorem liClockPairedEtaCriticalTransition_scaled_limits
    {ν : ℕ→ℕ} {t : ℕ→ℝ} {u : ℝ}
    (hν : Tendsto ν atTop atTop)
    (hT : Tendsto (fun k =>
      (t k-Real.log (2*(ν k : ℝ))/4)/Real.sqrt (Real.log (2*(ν k : ℝ))))
      atTop (nhds u)) :
  Tendsto (fun k => Real.exp (-2*t k)*liClockPairedEtaPartitionBorelKernel (ν k) (t k))
    atTop (nhds (liClockPairedEtaInfinitePartitionComparisonLimit/2 *
      liClockCriticalGaussianCDF (-2*u))) ∧
  Tendsto (fun k => Real.exp (-2*t k)*
      liClockPairedEtaContiguousBorelKernel (Real.log (2*(ν k : ℝ))) (t k))
    atTop (nhds ((1/2)*liClockCriticalGaussianCDF (-2*u))) := by
  let L : ℕ → ℝ := fun k => Real.log (2*(ν k : ℝ))
  have hL : Tendsto L atTop atTop := tendsto_liClockPairedEtaPartitionLogEndpoint.comp hν
  have ht : Tendsto t atTop atTop := (liClockCriticalWindow_kinematics hL hT).1
  have hNp : ∀ᶠ k in atTop, 0 < ν k := hν.eventually (eventually_gt_atTop 0)
  have hLp : ∀ᶠ k in atTop, 0 < L k := hL.eventually (eventually_gt_atTop 0)
  have htp : ∀ᶠ k in atTop, 0 ≤ t k :=
    (ht.eventually (eventually_gt_atTop 0)).mono (fun _ h => h.le)
  have hc := tendsto_liClockCriticalCutoffMeasure_cutoff hL hT
  have hl := tendsto_liClockCriticalCutoffLoss hL hT
  have hZA := tendsto_liClockPairedEtaInfinitePartitionNormalizer.comp hν
  have hZU := tendsto_liClockPairedEtaHalfLinePartitionNormalizer.comp hν
  have hZA0 : liClockPairedEtaInfinitePartitionNormalizer^2 ≠ 0 :=
    pow_ne_zero _ liClockPairedEtaInfinitePartitionNormalizer_pos.ne'
  have hqa : Tendsto (fun k => 2*Real.log 2/liClockPairedEtaPartitionNormalizer (ν k)^2)
      atTop (nhds liClockPairedEtaInfinitePartitionComparisonLimit) := by
    exact tendsto_const_nhds.div (hZA.pow 2) hZA0
  have hq4 : Tendsto (fun k => 4/liClockPairedEtaPartitionNormalizer (ν k)^2)
      atTop (nhds (4/liClockPairedEtaInfinitePartitionNormalizer^2)) :=
    tendsto_const_nhds.div (hZA.pow 2) hZA0
  have hqt : Tendsto (fun k => 4*(Real.pi^2/16)/(3*liClockPairedEtaPartitionNormalizer (ν k)^2))
      atTop (nhds (4*(Real.pi^2/16)/(3*liClockPairedEtaInfinitePartitionNormalizer^2))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.mul (hZA.pow 2))
      (mul_ne_zero (by norm_num) hZA0)
  have hbd : Tendsto (fun k =>
      (4/liClockPairedEtaPartitionNormalizer (ν k)^2)*liClockCriticalCutoffLoss (t k) (L k) +
      (4*(Real.pi^2/16)/(3*liClockPairedEtaPartitionNormalizer (ν k)^2))*
        Real.exp (-2*t k)*Real.cosh (2*t k/3)) atTop (nhds 0) := by
    have h := (hq4.mul hl).add (hqt.mul (cs_exp_cosh_tendsto ht))
    simp only [mul_zero, zero_add] at h
    exact h.congr (fun _ => by ring)
  have herr : Tendsto (fun k =>
      Real.exp (-2*t k)*liClockPairedEtaPartitionBorelKernel (ν k) (t k) -
      (2*Real.log 2/liClockPairedEtaPartitionNormalizer (ν k)^2)*
        (liClockCriticalCutoffMeasure (t k)).real (Set.Icc 0 (L k))) atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hbd
    filter_upwards [hNp, htp] with k hN htk
    simpa only [Real.norm_eq_abs, L] using
      liClockPairedEtaPartitionBorelKernel_scaled_critical_error_le hN htk
  have ha := herr.add (hqa.mul hc)
  have hea : liClockPairedEtaInfinitePartitionComparisonLimit*
      (liClockCriticalGaussianCDF (-2*u)/2) =
      liClockPairedEtaInfinitePartitionComparisonLimit/2*
        liClockCriticalGaussianCDF (-2*u) := by ring
  rw [zero_add, hea] at ha
  have hactual : Tendsto (fun k => Real.exp (-2*t k)*
      liClockPairedEtaPartitionBorelKernel (ν k) (t k)) atTop
      (nhds (liClockPairedEtaInfinitePartitionComparisonLimit/2*
        liClockCriticalGaussianCDF (-2*u))) :=
    ha.congr (fun _ => by ring)
  have hqu : Tendsto (fun k => 4/liClockPairedEtaContiguousPartitionNormalizer (L k)^2)
      atTop (nhds 1) := by
    have hq : Tendsto (fun k => 4/liClockPairedEtaContiguousPartitionNormalizer (L k)^2)
        atTop (nhds (4/(2:ℝ)^2)) :=
      tendsto_const_nhds.div (hZU.pow 2) (by norm_num)
    norm_num at hq
    exact hq
  have hu := hqu.mul (hc.sub hl)
  have heu : 1*(liClockCriticalGaussianCDF (-2*u)/2-0) =
      (1/2)*liClockCriticalGaussianCDF (-2*u) := by ring
  rw [heu] at hu
  have href : Tendsto (fun k => Real.exp (-2*t k)*
      liClockPairedEtaContiguousBorelKernel (L k) (t k)) atTop
      (nhds ((1/2)*liClockCriticalGaussianCDF (-2*u))) := by
    apply hu.congr'
    filter_upwards [hLp, htp] with k hLk htk
    exact (liClockPairedEtaContiguousBorelKernel_scaled_eq_cutoff hLk htk).symm
  exact ⟨hactual, href⟩

theorem tendsto_liClockPairedEtaCriticalTransition_ratio
    {ν : ℕ→ℕ} {t : ℕ→ℝ} {u : ℝ}
    (hν : Tendsto ν atTop atTop)
    (hT : Tendsto (fun k =>
      (t k-Real.log (2*(ν k : ℝ))/4)/Real.sqrt (Real.log (2*(ν k : ℝ))))
      atTop (nhds u)) :
  Tendsto (fun k => liClockPairedEtaPartitionBorelKernel (ν k) (t k) /
    liClockPairedEtaContiguousBorelKernel (Real.log (2*(ν k : ℝ))) (t k))
    atTop (nhds liClockPairedEtaInfinitePartitionComparisonLimit) := by
  have hs := liClockPairedEtaCriticalTransition_scaled_limits hν hT
  have hcdf : 0 < liClockCriticalGaussianCDF (-2*u) :=
    (liClockCriticalGaussianCDF_pos_lt_one (-2*u)).1
  have hb : (1/2:ℝ)*liClockCriticalGaussianCDF (-2*u) ≠ 0 :=
    ne_of_gt (mul_pos (by norm_num) hcdf)
  have h := cs_scaled_ratio hs.1 hs.2 hb
  have he : (liClockPairedEtaInfinitePartitionComparisonLimit/2*
      liClockCriticalGaussianCDF (-2*u))/((1/2)*liClockCriticalGaussianCDF (-2*u)) =
      liClockPairedEtaInfinitePartitionComparisonLimit := by
    apply (div_eq_iff hb).2
    ring
  rwa [he] at h

theorem tendsto_liClockPairedEtaCriticalTransition_gap
    {ν : ℕ→ℕ} {t : ℕ→ℝ} {u : ℝ}
    (hν : Tendsto ν atTop atTop)
    (hT : Tendsto (fun k =>
      (t k-Real.log (2*(ν k : ℝ))/4)/Real.sqrt (Real.log (2*(ν k : ℝ))))
      atTop (nhds u)) :
  Tendsto (fun k => liClockPairedEtaPartitionBorelKernel (ν k) (t k) -
    liClockPairedEtaContiguousBorelKernel (Real.log (2*(ν k : ℝ))) (t k)) atTop atBot := by
  have hL := tendsto_liClockPairedEtaPartitionLogEndpoint.comp hν
  have ht := (liClockCriticalWindow_kinematics hL hT).1
  have hs := liClockPairedEtaCriticalTransition_scaled_limits hν hT
  apply cs_negative_gap ht hs.1 hs.2
  have h := mul_lt_mul_of_pos_right liClockPairedEtaInfinitePartitionComparisonLimit_lt_one
    (liClockCriticalGaussianCDF_pos_lt_one (-2*u)).1
  linarith

private theorem cs_scaled_cosh_eq (t : ℝ) :
    Real.exp (-2*t)*Real.cosh (2*t) = (1+Real.exp (-4*t))/2 := by
  have hp : Real.exp (-2*t)*Real.exp (2*t)=1 := by
    rw [← Real.exp_add]
    norm_num
  have hn : Real.exp (-2*t)*Real.exp (-(2*t))=Real.exp (-4*t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Real.cosh_eq]
  calc
    _ = (Real.exp (-2*t)*Real.exp (2*t)+Real.exp (-2*t)*Real.exp (-(2*t)))/2 := by ring
    _ = _ := by rw [hp, hn]

private theorem cs_scaled_cosh_tendsto :
    Tendsto (fun t : ℝ => Real.exp (-2*t)*Real.cosh (2*t)) atTop (nhds (1/2)) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-4*t)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num))
  have h := (he.const_add (1:ℝ)).div_const 2
  simp only [add_zero] at h
  exact h.congr (fun t => (cs_scaled_cosh_eq t).symm)

theorem liClockPairedEtaCriticalTransition_signed_error_limits
    {ν : ℕ→ℕ} {t : ℕ→ℝ} {u : ℝ}
    (hν : Tendsto ν atTop atTop)
    (hT : Tendsto (fun k =>
      (t k-Real.log (2*(ν k : ℝ))/4)/Real.sqrt (Real.log (2*(ν k : ℝ))))
      atTop (nhds u)) :
    Tendsto (fun k => Real.exp (-2*t k) *
      (liClockPairedEtaPartitionBorelKernel (ν k) (t k)-
        liClockPairedEtaInfinitePartitionBorelKernel (t k)))
      atTop (nhds (-(liClockPairedEtaInfinitePartitionComparisonLimit/2)*
        liClockCriticalGaussianCDF (2*u))) ∧
    Tendsto (fun k => Real.exp (-2*t k) *
      (liClockPairedEtaContiguousBorelKernel (Real.log (2*(ν k : ℝ))) (t k)-
        liClockPairedEtaHalfLineBorelKernel (t k)))
      atTop (nhds (-(1/2)*liClockCriticalGaussianCDF (2*u))) := by
  have hL : Tendsto (fun k : ℕ => Real.log (2*(ν k:ℝ))) atTop atTop := by
    simpa only [Function.comp_def] using tendsto_liClockPairedEtaPartitionLogEndpoint.comp hν
  have ht := (liClockCriticalWindow_kinematics hL hT).1
  have hf := liClockPairedEtaCriticalTransition_scaled_limits hν hT
  have hi := tendsto_liClockPairedEtaInfinitePartitionBorelKernel_scaled.comp ht
  simp only [Function.comp_def] at hi
  have hu : Tendsto (fun k => Real.exp (-2*t k)*liClockPairedEtaHalfLineBorelKernel (t k))
      atTop (nhds (1/2)) := by
    simpa only [Function.comp_def, liClockPairedEtaHalfLineBorelKernel_eq_cosh] using cs_scaled_cosh_tendsto.comp ht
  have hp : liClockCriticalGaussianCDF (-2*u) = 1-liClockCriticalGaussianCDF (2*u) := by
    rw [show -2*u=-(2*u) by ring, liClockCriticalGaussianCDF_neg]
  have ha := hf.1.sub hi
  have hb := hf.2.sub hu
  have ha' : liClockPairedEtaInfinitePartitionComparisonLimit/2*liClockCriticalGaussianCDF (-2*u) -
      liClockPairedEtaInfinitePartitionComparisonLimit/2 =
      -(liClockPairedEtaInfinitePartitionComparisonLimit/2)*liClockCriticalGaussianCDF (2*u) := by
    rw [hp]
    ring
  have hb' : (1/2)*liClockCriticalGaussianCDF (-2*u)-(1/2:ℝ) =
      -(1/2)*liClockCriticalGaussianCDF (2*u) := by
    rw [hp]
    ring
  rw [ha'] at ha
  rw [hb'] at hb
  exact ⟨ha.congr (fun k => by ring), hb.congr (fun k => by ring)⟩

theorem liClockPairedEtaCriticalTransition_absolute_error_limits
    {ν : ℕ→ℕ} {t : ℕ→ℝ} {u : ℝ}
    (hν : Tendsto ν atTop atTop)
    (hT : Tendsto (fun k =>
      (t k-Real.log (2*(ν k : ℝ))/4)/Real.sqrt (Real.log (2*(ν k : ℝ))))
      atTop (nhds u)) :
    Tendsto (fun k => Real.exp (-2*t k) *
      |liClockPairedEtaPartitionBorelKernel (ν k) (t k)-
        liClockPairedEtaInfinitePartitionBorelKernel (t k)|)
      atTop (nhds ((liClockPairedEtaInfinitePartitionComparisonLimit/2)*
        liClockCriticalGaussianCDF (2*u))) ∧
    Tendsto (fun k => Real.exp (-2*t k) *
      |liClockPairedEtaContiguousBorelKernel (Real.log (2*(ν k : ℝ))) (t k)-
        liClockPairedEtaHalfLineBorelKernel (t k)|)
      atTop (nhds ((1/2)*liClockCriticalGaussianCDF (2*u))) := by
  have hs := liClockPairedEtaCriticalTransition_signed_error_limits hν hT
  have hp := (liClockCriticalGaussianCDF_pos_lt_one (2*u)).1
  have ha : -(liClockPairedEtaInfinitePartitionComparisonLimit/2)*liClockCriticalGaussianCDF (2*u)<0 :=
    mul_neg_of_neg_of_pos (by linarith [liClockPairedEtaInfinitePartitionComparisonLimit_pos]) hp
  have hb : -(1/2:ℝ)*liClockCriticalGaussianCDF (2*u)<0 := mul_neg_of_neg_of_pos (by norm_num) hp
  constructor
  · have h := hs.1.abs
    rw [abs_of_neg ha] at h
    have he : -(-(liClockPairedEtaInfinitePartitionComparisonLimit/2)*liClockCriticalGaussianCDF (2*u)) =
        (liClockPairedEtaInfinitePartitionComparisonLimit/2)*liClockCriticalGaussianCDF (2*u) := by ring
    rw [he] at h
    exact h.congr (fun k => by rw [abs_mul, abs_of_pos (Real.exp_pos _)])
  · have h := hs.2.abs
    rw [abs_of_neg hb] at h
    have he : -(-(1/2:ℝ)*liClockCriticalGaussianCDF (2*u)) =
        (1/2)*liClockCriticalGaussianCDF (2*u) := by ring
    rw [he] at h
    exact h.congr (fun k => by rw [abs_mul, abs_of_pos (Real.exp_pos _)])

theorem liClockPairedEtaCriticalTransition_complex_norm_error_limits
    {ν : ℕ→ℕ} {t : ℕ→ℝ} {u : ℝ}
    (hν : Tendsto ν atTop atTop)
    (hT : Tendsto (fun k =>
      (t k-Real.log (2*(ν k : ℝ))/4)/Real.sqrt (Real.log (2*(ν k : ℝ))))
      atTop (nhds u)) :
    Tendsto (fun k => Real.exp (-2*‖(t k : ℂ)‖) *
      ‖liClockPairedEtaPartitionBorelKernelComplex (ν k) (t k : ℂ)-
        liClockPairedEtaInfinitePartitionBorelKernelComplex (t k : ℂ)‖)
      atTop (nhds ((liClockPairedEtaInfinitePartitionComparisonLimit/2)*
        liClockCriticalGaussianCDF (2*u))) ∧
    Tendsto (fun k => Real.exp (-2*‖(t k : ℂ)‖) *
      ‖liClockPairedEtaContiguousBorelKernelComplex (Real.log (2*(ν k : ℝ))) (t k : ℂ)-
        liClockPairedEtaHalfLineBorelKernelComplex (t k : ℂ)‖)
      atTop (nhds ((1/2)*liClockCriticalGaussianCDF (2*u))) := by
  have hL : Tendsto (fun k : ℕ => Real.log (2*(ν k:ℝ))) atTop atTop := by
    simpa only [Function.comp_def] using tendsto_liClockPairedEtaPartitionLogEndpoint.comp hν
  have ht := (liClockCriticalWindow_kinematics hL hT).1
  have hs := liClockPairedEtaCriticalTransition_absolute_error_limits hν hT
  constructor
  · apply hs.1.congr'
    filter_upwards [hν.eventually (eventually_gt_atTop 0), ht.eventually (eventually_gt_atTop 0)]
      with k hnk htk
    rw [liClockPairedEtaPartitionBorelKernelComplex_ofReal hnk,
      liClockPairedEtaInfinitePartitionBorelKernelComplex_ofReal, ← Complex.ofReal_sub]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg htk.le]
  · apply hs.2.congr'
    filter_upwards [hL.eventually (eventually_gt_atTop 0), ht.eventually (eventually_gt_atTop 0)]
      with k hlk htk
    rw [liClockPairedEtaContiguousBorelKernelComplex_ofReal hlk,
      liClockPairedEtaHalfLineBorelKernelComplex_ofReal, ← Complex.ofReal_sub]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg htk.le]

theorem liClockPairedEtaCriticalQuarter_limits :
  Tendsto (fun N : ℕ =>
    (Real.exp (-2*liClockPairedEtaCriticalQuarterClock N)*
       liClockPairedEtaPartitionBorelKernel N (liClockPairedEtaCriticalQuarterClock N),
     Real.exp (-2*liClockPairedEtaCriticalQuarterClock N)*
       liClockPairedEtaContiguousBorelKernel (Real.log (2*(N : ℝ)))
         (liClockPairedEtaCriticalQuarterClock N)))
    atTop (nhds (liClockPairedEtaInfinitePartitionComparisonLimit/4, (1/4 : ℝ))) ∧
  Tendsto (fun N : ℕ =>
    (Real.exp (-2*liClockPairedEtaCriticalQuarterClock N)*
       |liClockPairedEtaPartitionBorelKernel N (liClockPairedEtaCriticalQuarterClock N)-
         liClockPairedEtaInfinitePartitionBorelKernel (liClockPairedEtaCriticalQuarterClock N)|,
     Real.exp (-2*liClockPairedEtaCriticalQuarterClock N)*
       |liClockPairedEtaContiguousBorelKernel (Real.log (2*(N : ℝ)))
           (liClockPairedEtaCriticalQuarterClock N)-
         liClockPairedEtaHalfLineBorelKernel (liClockPairedEtaCriticalQuarterClock N)|))
    atTop (nhds (liClockPairedEtaInfinitePartitionComparisonLimit/4, (1/4 : ℝ))) ∧
  Tendsto (fun N : ℕ =>
    (Real.exp (-2*‖(liClockPairedEtaCriticalQuarterClock N : ℂ)‖)*
       ‖liClockPairedEtaPartitionBorelKernelComplex N (liClockPairedEtaCriticalQuarterClock N : ℂ)-
         liClockPairedEtaInfinitePartitionBorelKernelComplex (liClockPairedEtaCriticalQuarterClock N : ℂ)‖,
     Real.exp (-2*‖(liClockPairedEtaCriticalQuarterClock N : ℂ)‖)*
       ‖liClockPairedEtaContiguousBorelKernelComplex (Real.log (2*(N : ℝ)))
           (liClockPairedEtaCriticalQuarterClock N : ℂ)-
         liClockPairedEtaHalfLineBorelKernelComplex (liClockPairedEtaCriticalQuarterClock N : ℂ)‖))
    atTop (nhds (liClockPairedEtaInfinitePartitionComparisonLimit/4, (1/4 : ℝ))) := by
  have hT : Tendsto (fun N : ℕ =>
      (liClockPairedEtaCriticalQuarterClock N-Real.log (2*(N:ℝ))/4)/
        Real.sqrt (Real.log (2*(N:ℝ)))) atTop (nhds (0:ℝ)) := by
    simpa only [liClockPairedEtaCriticalQuarterClock, sub_self, zero_div] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (nhds 0))
  have hs := liClockPairedEtaCriticalTransition_scaled_limits (ν := id) (t := liClockPairedEtaCriticalQuarterClock) tendsto_id hT
  have ha := liClockPairedEtaCriticalTransition_absolute_error_limits (ν := id) (t := liClockPairedEtaCriticalQuarterClock) tendsto_id hT
  have hc := liClockPairedEtaCriticalTransition_complex_norm_error_limits (ν := id) (t := liClockPairedEtaCriticalQuarterClock) tendsto_id hT
  have hv : liClockPairedEtaInfinitePartitionComparisonLimit/2*(1/2:ℝ) =
      liClockPairedEtaInfinitePartitionComparisonLimit/4 := by ring
  have hu : (1/2:ℝ)*(1/2)=1/4 := by norm_num
  constructor
  · simpa only [id_eq, mul_zero, liClockCriticalGaussianCDF_zero, hv, hu] using hs.1.prodMk_nhds hs.2
  constructor
  · simpa only [id_eq, mul_zero, liClockCriticalGaussianCDF_zero, hv, hu] using ha.1.prodMk_nhds ha.2
  · simpa only [id_eq, mul_zero, liClockCriticalGaussianCDF_zero, hv, hu] using hc.1.prodMk_nhds hc.2

theorem liClockPairedEtaCriticalInterior_limits :
  Tendsto (fun N : ℕ =>
    (Real.exp (-2*liClockPairedEtaCriticalInteriorClock N)*
       liClockPairedEtaPartitionBorelKernel N (liClockPairedEtaCriticalInteriorClock N),
     Real.exp (-2*liClockPairedEtaCriticalInteriorClock N)*
       liClockPairedEtaContiguousBorelKernel (Real.log (2*(N : ℝ)))
         (liClockPairedEtaCriticalInteriorClock N)))
    atTop (nhds (liClockPairedEtaInfinitePartitionComparisonLimit/4, (1/4 : ℝ))) ∧
  Tendsto (fun N : ℕ =>
    (Real.exp (-2*liClockPairedEtaCriticalInteriorClock N)*
       |liClockPairedEtaPartitionBorelKernel N (liClockPairedEtaCriticalInteriorClock N)-
         liClockPairedEtaInfinitePartitionBorelKernel (liClockPairedEtaCriticalInteriorClock N)|,
     Real.exp (-2*liClockPairedEtaCriticalInteriorClock N)*
       |liClockPairedEtaContiguousBorelKernel (Real.log (2*(N : ℝ)))
           (liClockPairedEtaCriticalInteriorClock N)-
         liClockPairedEtaHalfLineBorelKernel (liClockPairedEtaCriticalInteriorClock N)|))
    atTop (nhds (liClockPairedEtaInfinitePartitionComparisonLimit/4, (1/4 : ℝ))) ∧
  Tendsto (fun N : ℕ =>
    (Real.exp (-2*‖(liClockPairedEtaCriticalInteriorClock N : ℂ)‖)*
       ‖liClockPairedEtaPartitionBorelKernelComplex N (liClockPairedEtaCriticalInteriorClock N : ℂ)-
         liClockPairedEtaInfinitePartitionBorelKernelComplex (liClockPairedEtaCriticalInteriorClock N : ℂ)‖,
     Real.exp (-2*‖(liClockPairedEtaCriticalInteriorClock N : ℂ)‖)*
       ‖liClockPairedEtaContiguousBorelKernelComplex (Real.log (2*(N : ℝ)))
           (liClockPairedEtaCriticalInteriorClock N : ℂ)-
         liClockPairedEtaHalfLineBorelKernelComplex (liClockPairedEtaCriticalInteriorClock N : ℂ)‖))
    atTop (nhds (liClockPairedEtaInfinitePartitionComparisonLimit/4, (1/4 : ℝ))) := by
  have hroot := Real.tendsto_sqrt_atTop.comp tendsto_liClockPairedEtaPartitionLogEndpoint
  simp only [Function.comp_def] at hroot
  have hz := hroot.const_div_atTop (-1:ℝ)
  have hT : Tendsto (fun N : ℕ =>
      (liClockPairedEtaCriticalInteriorClock N-Real.log (2*(N:ℝ))/4)/
        Real.sqrt (Real.log (2*(N:ℝ)))) atTop (nhds (0:ℝ)) := by
    apply hz.congr
    intro N
    unfold liClockPairedEtaCriticalInteriorClock
    ring
  have hs := liClockPairedEtaCriticalTransition_scaled_limits (ν := id) (t := liClockPairedEtaCriticalInteriorClock) tendsto_id hT
  have ha := liClockPairedEtaCriticalTransition_absolute_error_limits (ν := id) (t := liClockPairedEtaCriticalInteriorClock) tendsto_id hT
  have hc := liClockPairedEtaCriticalTransition_complex_norm_error_limits (ν := id) (t := liClockPairedEtaCriticalInteriorClock) tendsto_id hT
  have hv : liClockPairedEtaInfinitePartitionComparisonLimit/2*(1/2:ℝ) =
      liClockPairedEtaInfinitePartitionComparisonLimit/4 := by ring
  have hu : (1/2:ℝ)*(1/2)=1/4 := by norm_num
  constructor
  · simpa only [id_eq, mul_zero, liClockCriticalGaussianCDF_zero, hv, hu] using hs.1.prodMk_nhds hs.2
  constructor
  · simpa only [id_eq, mul_zero, liClockCriticalGaussianCDF_zero, hv, hu] using ha.1.prodMk_nhds ha.2
  · simpa only [id_eq, mul_zero, liClockCriticalGaussianCDF_zero, hv, hu] using hc.1.prodMk_nhds hc.2

theorem liClockPairedEtaCriticalInterior_shared_witness :
  ∀ᶠ N : ℕ in atTop,
    0<liClockPairedEtaCriticalInteriorClock N ∧
    liClockPairedEtaCriticalInteriorClock N<Real.log (2*(N : ℝ))/4 ∧
    ‖(liClockPairedEtaCriticalInteriorClock N : ℂ)‖<Real.log (2*(N : ℝ))/4 ∧
    liClockPairedEtaInfinitePartitionComparisonLimit/8≤
      Real.exp (-2*‖(liClockPairedEtaCriticalInteriorClock N : ℂ)‖)*
        ‖liClockPairedEtaPartitionBorelKernelComplex N (liClockPairedEtaCriticalInteriorClock N : ℂ)-
          liClockPairedEtaInfinitePartitionBorelKernelComplex (liClockPairedEtaCriticalInteriorClock N : ℂ)‖ ∧
    (1/8 : ℝ)≤
      Real.exp (-2*‖(liClockPairedEtaCriticalInteriorClock N : ℂ)‖)*
        ‖liClockPairedEtaContiguousBorelKernelComplex (Real.log (2*(N : ℝ)))
            (liClockPairedEtaCriticalInteriorClock N : ℂ)-
          liClockPairedEtaHalfLineBorelKernelComplex (liClockPairedEtaCriticalInteriorClock N : ℂ)‖ := by
  have hc := liClockPairedEtaCriticalInterior_limits.2.2
  have ha := hc.fst_nhds.eventually_const_lt
    (show liClockPairedEtaInfinitePartitionComparisonLimit/8 <
      liClockPairedEtaInfinitePartitionComparisonLimit/4 by
        linarith [liClockPairedEtaInfinitePartitionComparisonLimit_pos])
  have hu := hc.snd_nhds.eventually_const_lt (show (1/8:ℝ)<1/4 by norm_num)
  filter_upwards [tendsto_liClockPairedEtaPartitionLogEndpoint.eventually (eventually_gt_atTop 4), ha, hu]
    with N hL hA hU
  have ht : 0<liClockPairedEtaCriticalInteriorClock N := by
    unfold liClockPairedEtaCriticalInteriorClock
    linarith
  have hi : liClockPairedEtaCriticalInteriorClock N<Real.log (2*(N:ℝ))/4 := by
    unfold liClockPairedEtaCriticalInteriorClock
    linarith
  refine ⟨ht, hi, ?_, hA.le, hU.le⟩
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] using hi

theorem liClockPairedEtaCriticalQuarter_no_actual_open_envelope :
  ¬∃ E : ℕ→ℝ, Tendsto E atTop (nhds 0) ∧
    ∀ᶠ N : ℕ in atTop, ∀ z : ℂ,
      ‖z‖<Real.log (2*(N : ℝ))/4 →
      Real.exp (-2*‖z‖)*‖liClockPairedEtaPartitionBorelKernelComplex N z-
        liClockPairedEtaInfinitePartitionBorelKernelComplex z‖≤E N := by
  rintro ⟨E, hE, hb⟩
  have hs := hE.eventually_lt_const
    (show (0:ℝ)<liClockPairedEtaInfinitePartitionComparisonLimit/8 by
      exact div_pos liClockPairedEtaInfinitePartitionComparisonLimit_pos (by norm_num))
  obtain ⟨N, hN, hEN, hbN⟩ :=
    (liClockPairedEtaCriticalInterior_shared_witness.and (hs.and hb)).exists
  have h := hbN (liClockPairedEtaCriticalInteriorClock N : ℂ) hN.2.2.1
  linarith [hN.2.2.2.1]

theorem liClockPairedEtaCriticalQuarter_no_reference_open_envelope :
  ¬∃ E : ℕ→ℝ, Tendsto E atTop (nhds 0) ∧
    ∀ᶠ N : ℕ in atTop, ∀ z : ℂ,
      ‖z‖<Real.log (2*(N : ℝ))/4 →
      Real.exp (-2*‖z‖)*
        ‖liClockPairedEtaContiguousBorelKernelComplex (Real.log (2*(N : ℝ))) z-
          liClockPairedEtaHalfLineBorelKernelComplex z‖≤E N := by
  rintro ⟨E, hE, hb⟩
  have hs := hE.eventually_lt_const (show (0:ℝ)<1/8 by norm_num)
  obtain ⟨N, hN, hEN, hbN⟩ :=
    (liClockPairedEtaCriticalInterior_shared_witness.and (hs.and hb)).exists
  have h := hbN (liClockPairedEtaCriticalInteriorClock N : ℂ) hN.2.2.1
  linarith [hN.2.2.2.2]

theorem liClockPairedEtaCriticalQuarter_no_actual_closed_envelope :
  ¬∃ E : ℕ→ℝ, Tendsto E atTop (nhds 0) ∧
    ∀ᶠ N : ℕ in atTop, ∀ z : ℂ,
      ‖z‖≤Real.log (2*(N : ℝ))/4 →
      Real.exp (-2*‖z‖)*‖liClockPairedEtaPartitionBorelKernelComplex N z-
        liClockPairedEtaInfinitePartitionBorelKernelComplex z‖≤E N := by
  rintro ⟨E, hE, hb⟩
  apply liClockPairedEtaCriticalQuarter_no_actual_open_envelope
  refine ⟨E, hE, ?_⟩
  filter_upwards [hb] with N hN
  intro z hz
  exact hN z hz.le

theorem liClockPairedEtaCriticalQuarter_no_reference_closed_envelope :
  ¬∃ E : ℕ→ℝ, Tendsto E atTop (nhds 0) ∧
    ∀ᶠ N : ℕ in atTop, ∀ z : ℂ,
      ‖z‖≤Real.log (2*(N : ℝ))/4 →
      Real.exp (-2*‖z‖)*
        ‖liClockPairedEtaContiguousBorelKernelComplex (Real.log (2*(N : ℝ))) z-
          liClockPairedEtaHalfLineBorelKernelComplex z‖≤E N := by
  rintro ⟨E, hE, hb⟩
  apply liClockPairedEtaCriticalQuarter_no_reference_open_envelope
  refine ⟨E, hE, ?_⟩
  filter_upwards [hb] with N hN
  intro z hz
  exact hN z hz.le

end RHTower
end
