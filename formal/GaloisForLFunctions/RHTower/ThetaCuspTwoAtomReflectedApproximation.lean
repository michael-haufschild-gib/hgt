import GaloisForLFunctions.RHTower.ThetaCuspTwoAtomSourceApproximation
import GaloisForLFunctions.RHTower.ThetaCuspFactoredReflectionError

/-!
# Complete reflected error around the literal two-atom source

Factor before differentiation, retaining the exact reflected first-atom jets.
The positive deep tail is controlled at every point beyond the compact energy
interval, while the second atom remains exact in the finite convolution.
-/
open Filter Topology
open scoped ContDiff
namespace RHTower
noncomputable section
set_option maxHeartbeats 1500000

/-- The deep-tail scale condition holds throughout the unclosed middle interval. -/
theorem thirtySevenTenths_le_firstAtomScale_of_energy_endpoint {x : ℝ} (hx : 8/95 ≤ x) :
    37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x := by
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 16/95) 3
  norm_num [Finset.sum_range_succ] at he
  have hm := he.trans (Real.exp_le_exp.mpr (show (16/95 : ℝ) ≤ 2*x by linarith))
  have hp := mul_le_mul_of_nonneg_left hm Real.pi_pos.le
  simp only [thetaCuspSingleAtomReflectionScale, Nat.cast_one, one_pow, mul_one]
  nlinarith [Real.pi_gt_d2]

/-- Exact relative partition of the two retained atoms. -/
def thetaCuspTwoAtomLikelihoodPartition (x : ℝ) : ℝ :=
  thetaCuspTwoAtomSource x/thetaCuspSourceTerm x 1

/-- Smoothness of the literal two-atom partition on the positive half-line. -/
theorem contDiffAt_thetaCuspTwoAtomLikelihoodPartition {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ ∞ thetaCuspTwoAtomLikelihoodPartition x :=
  contDiff_thetaCuspTwoAtomSource.contDiffAt.div (contDiff_thetaCuspSourceAtom 1).contDiffAt
    (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)).ne'

/-- Literal reflected jet of the first two source atoms. -/
def thetaCuspTwoAtomReflectionJet (n : ℕ) (x : ℝ) : ℝ :=
  iteratedDeriv n (fun t => thetaCuspTwoAtomSource (x+t)*thetaCuspTwoAtomSource (x-t)) 0

/-- The retained model has its exact full finite Leibniz formula. -/
theorem thetaCuspTwoAtomReflectionJet_eq (n : ℕ) (x : ℝ) :
    thetaCuspTwoAtomReflectionJet n x =
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*iteratedDeriv i thetaCuspTwoAtomSource x*
        ((-1 : ℝ)^(n-i)*iteratedDeriv (n-i) thetaCuspTwoAtomSource x) := by
  have hf : ContDiff ℝ n thetaCuspTwoAtomSource := contDiff_thetaCuspTwoAtomSource.of_le
    (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  unfold thetaCuspTwoAtomReflectionJet
  have hl : ContDiffAt ℝ n (fun t : ℝ => thetaCuspTwoAtomSource (x+t)) 0 :=
    (hf.comp (contDiff_const.add contDiff_id)).contDiffAt
  have hr : ContDiffAt ℝ n (fun t : ℝ => thetaCuspTwoAtomSource (x-t)) 0 :=
    (hf.comp (contDiff_const.sub contDiff_id)).contDiffAt
  rw [iteratedDeriv_fun_mul hl hr]
  simp only [iteratedDeriv_comp_const_add, iteratedDeriv_comp_const_sub, add_zero, sub_zero, smul_eq_mul]

/-- Relative reflected error, retaining both cross terms and the quadratic deep tail. -/
def thetaCuspTwoAtomReflectionError (x t : ℝ) : ℝ :=
  thetaCuspTwoAtomLikelihoodPartition (x+t)*thetaCuspDeepLikelihoodRemainder (x-t)+
    thetaCuspDeepLikelihoodRemainder (x+t)*thetaCuspTwoAtomLikelihoodPartition (x-t)+
    thetaCuspDeepLikelihoodRemainder (x+t)*thetaCuspDeepLikelihoodRemainder (x-t)

/-- Actual derivative of the complete relative reflected error. -/
def thetaCuspTwoAtomReflectionErrorJet (n : ℕ) (x : ℝ) : ℝ :=
  iteratedDeriv n (thetaCuspTwoAtomReflectionError x) 0

private theorem reflected_smooth {f : ℝ → ℝ} (n : ℕ) {x : ℝ} (hf : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ n (fun t : ℝ => f (x+t)) 0 ∧
      ContDiffAt ℝ n (fun t : ℝ => f (x-t)) 0 := by
  have h : ContDiffAt ℝ n f x := hf.of_le
    (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  constructor
  · exact (show ContDiffAt ℝ n f (x+0) by simpa using h).comp (0 : ℝ)
      (contDiffAt_const.add contDiffAt_id)
  · exact (show ContDiffAt ℝ n f (x-0) by simpa using h).comp (0 : ℝ)
      (contDiffAt_const.sub contDiffAt_id)

/-- All derivatives of the factored error are explicit finite convolutions of literal jets. -/
theorem thetaCuspTwoAtomReflectionErrorJet_eq (n : ℕ) {x : ℝ} (hx : 0 < x) :
    thetaCuspTwoAtomReflectionErrorJet n x =
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*(-1 : ℝ)^(n-i)*
        (iteratedDeriv i thetaCuspTwoAtomLikelihoodPartition x*
            iteratedDeriv (n-i) thetaCuspDeepLikelihoodRemainder x+
          iteratedDeriv i thetaCuspDeepLikelihoodRemainder x*
            iteratedDeriv (n-i) thetaCuspTwoAtomLikelihoodPartition x+
          iteratedDeriv i thetaCuspDeepLikelihoodRemainder x*
            iteratedDeriv (n-i) thetaCuspDeepLikelihoodRemainder x) := by
  obtain ⟨hal, har⟩ := reflected_smooth n (contDiffAt_thetaCuspTwoAtomLikelihoodPartition hx)
  obtain ⟨hel, her⟩ := reflected_smooth n (contDiffAt_thetaCuspDeepLikelihoodRemainder hx)
  unfold thetaCuspTwoAtomReflectionErrorJet thetaCuspTwoAtomReflectionError
  rw [iteratedDeriv_fun_add ((hal.mul her).add (hel.mul har)) (hel.mul her),
    iteratedDeriv_fun_add (hal.mul her) (hel.mul har),
    iteratedDeriv_fun_mul hal her, iteratedDeriv_fun_mul hel har, iteratedDeriv_fun_mul hel her]
  simp only [iteratedDeriv_comp_const_add, iteratedDeriv_comp_const_sub,
    add_zero, sub_zero, smul_eq_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Exact source identity near every positive reflection center. -/
theorem thetaCuspNativeTwoAtomReflectionError_eventually_factor {x : ℝ} (hx : 0 < x) :
    (fun t : ℝ => thetaCuspFullSource (x+t)*thetaCuspFullSource (x-t)-
      thetaCuspTwoAtomSource (x+t)*thetaCuspTwoAtomSource (x-t)) =ᶠ[𝓝 0]
    (fun t : ℝ => (thetaCuspSourceTerm (x+t) 1*thetaCuspSourceTerm (x-t) 1)*
      thetaCuspTwoAtomReflectionError x t) := by
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, t ∈ Set.Ioo (-x) x := Ioo_mem_nhds (by linarith) hx
  filter_upwards [hsmall] with t ht
  have hl : 0 < x+t := by linarith [ht.1]
  have hr : 0 < x-t := by linarith [ht.2]
  have hFl := thetaCuspFullSource_sub_two_eq_first_mul_deep hl
  have hFr := thetaCuspFullSource_sub_two_eq_first_mul_deep hr
  have hfl := (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hl (by norm_num : 0 < (1 : ℕ))).ne'
  have hfr := (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hr (by norm_num : 0 < (1 : ℕ))).ne'
  have heL : thetaCuspFullSource (x+t) = thetaCuspTwoAtomSource (x+t)+
      thetaCuspSourceTerm (x+t) 1*thetaCuspDeepLikelihoodRemainder (x+t) := by linarith only [hFl]
  have heR : thetaCuspFullSource (x-t) = thetaCuspTwoAtomSource (x-t)+
      thetaCuspSourceTerm (x-t) 1*thetaCuspDeepLikelihoodRemainder (x-t) := by linarith only [hFr]
  rw [heL, heR]
  unfold thetaCuspTwoAtomReflectionError thetaCuspTwoAtomLikelihoodPartition
  field_simp [hfl, hfr]
  ring

/-- Exact reflected error convolution preserves every first-atom reflection cancellation. -/
theorem thetaCuspNativeReflectionJet_sub_two_eq_factored (n : ℕ) {x : ℝ} (hx : 0 < x) :
    thetaCuspNativeReflectionJet n x-thetaCuspTwoAtomReflectionJet n x =
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*thetaCuspFirstAtomReflectionJet i x*
        thetaCuspTwoAtomReflectionErrorJet (n-i) x := by
  obtain ⟨hfl, hfr⟩ := reflected_smooth n (contDiff_thetaCuspSourceAtom 1).contDiffAt (x := x)
  obtain ⟨hFl, hFr⟩ := reflected_smooth n contDiff_thetaCuspFullSource.contDiffAt (x := x)
  obtain ⟨hTl, hTr⟩ := reflected_smooth n contDiff_thetaCuspTwoAtomSource.contDiffAt (x := x)
  obtain ⟨hal, har⟩ := reflected_smooth n (contDiffAt_thetaCuspTwoAtomLikelihoodPartition hx)
  obtain ⟨hel, her⟩ := reflected_smooth n (contDiffAt_thetaCuspDeepLikelihoodRemainder hx)
  have hE : ContDiffAt ℝ n (thetaCuspTwoAtomReflectionError x) 0 :=
    ((hal.mul her).add (hel.mul har)).add (hel.mul her)
  have he := Filter.EventuallyEq.iteratedDeriv_eq n (thetaCuspNativeTwoAtomReflectionError_eventually_factor hx)
  rw [iteratedDeriv_fun_sub (hFl.mul hFr) (hTl.mul hTr),
    iteratedDeriv_fun_mul (hfl.mul hfr) hE] at he
  exact he

end
end RHTower
