import GaloisForLFunctions.RHTower.ThetaCuspSharpFiniteCooling
import GaloisForLFunctions.RHTower.ThetaCuspNativeJetFirstAtomApproximation

/-!
# Exact reflected likelihood factorization before taking absolute values

The complete reflected error is the first-atom reflected product times the
linear-plus-quadratic likelihood correction. Its finite jet convolution retains
the first-atom reflection cancellations.
-/
open Filter Topology
namespace RHTower
noncomputable section

/-- Relative correction to the first-atom reflected product. -/
def thetaCuspLikelihoodReflectionError (x t : ℝ) : ℝ :=
  thetaCuspLikelihoodSourceRemainder (x+t)+thetaCuspLikelihoodSourceRemainder (x-t)+
    thetaCuspLikelihoodSourceRemainder (x+t)*thetaCuspLikelihoodSourceRemainder (x-t)

/-- Literal derivative of the reflected likelihood correction. -/
def thetaCuspLikelihoodReflectionErrorJet (n : ℕ) (x : ℝ) : ℝ :=
  iteratedDeriv n (thetaCuspLikelihoodReflectionError x) 0

private theorem remainder_left_contDiff (n : ℕ) {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ n (fun t : ℝ => thetaCuspLikelihoodSourceRemainder (x+t)) 0 := by
  have h : ContDiffAt ℝ n thetaCuspLikelihoodSourceRemainder x :=
    (contDiffAt_thetaCuspLikelihoodSourceRemainder hx).of_le
    (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have h' : ContDiffAt ℝ n thetaCuspLikelihoodSourceRemainder (x+0) := by simpa using h
  exact h'.comp (0 : ℝ) (contDiffAt_const.add contDiffAt_id)

private theorem remainder_right_contDiff (n : ℕ) {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ n (fun t : ℝ => thetaCuspLikelihoodSourceRemainder (x-t)) 0 := by
  have h : ContDiffAt ℝ n thetaCuspLikelihoodSourceRemainder x :=
    (contDiffAt_thetaCuspLikelihoodSourceRemainder hx).of_le
    (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have h' : ContDiffAt ℝ n thetaCuspLikelihoodSourceRemainder (x-0) := by simpa using h
  exact h'.comp (0 : ℝ) (contDiffAt_const.sub contDiffAt_id)

/-- The relative correction retains both linear derivative terms and the complete quadratic sum. -/
theorem thetaCuspLikelihoodReflectionErrorJet_eq (n : ℕ) {x : ℝ} (hx : 0 < x) :
    thetaCuspLikelihoodReflectionErrorJet n x =
      (1+(-1 : ℝ)^n)*iteratedDeriv n thetaCuspLikelihoodSourceRemainder x +
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*
        iteratedDeriv i thetaCuspLikelihoodSourceRemainder x *
        ((-1 : ℝ)^(n-i)*iteratedDeriv (n-i) thetaCuspLikelihoodSourceRemainder x) := by
  have hl := remainder_left_contDiff n hx
  have hr := remainder_right_contDiff n hx
  unfold thetaCuspLikelihoodReflectionErrorJet thetaCuspLikelihoodReflectionError
  rw [iteratedDeriv_fun_add (hl.add hr) (hl.mul hr), iteratedDeriv_fun_add hl hr,
    iteratedDeriv_fun_mul hl hr]
  simp only [iteratedDeriv_comp_const_add, iteratedDeriv_comp_const_sub,
    add_zero, sub_zero, smul_eq_mul]
  ring

/-- The complete source reflection error factors locally through the unexpanded first-atom product. -/
theorem thetaCuspNativeReflectionError_eventually_factor {x : ℝ} (hx : 0 < x) :
    (fun t : ℝ => thetaCuspFullSource (x+t)*thetaCuspFullSource (x-t)-
      thetaCuspSourceTerm (x+t) 1*thetaCuspSourceTerm (x-t) 1) =ᶠ[𝓝 0]
    (fun t : ℝ => (thetaCuspSourceTerm (x+t) 1*thetaCuspSourceTerm (x-t) 1)*
      thetaCuspLikelihoodReflectionError x t) := by
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, t ∈ Set.Ioo (-x) x :=
    Ioo_mem_nhds (by linarith) hx
  filter_upwards [hsmall] with t ht0
  have ht : 0 < x+t := by linarith [ht0.1]
  have ht' : 0 < x-t := by linarith [ht0.2]
  rw [thetaCuspFullSource_eq_first_mul_likelihoodPartition (thetaCuspLikelihoodCoordinate_pos ht.le),
    thetaCuspFullSource_eq_first_mul_likelihoodPartition (thetaCuspLikelihoodCoordinate_pos ht'.le)]
  unfold thetaCuspLikelihoodReflectionError thetaCuspLikelihoodSourceRemainder
  ring

/-- Exact all-order reflected error convolution, with reflection cancellation preserved in each factor. -/
theorem thetaCuspNativeReflectionJet_sub_first_eq_factored (n : ℕ) {x : ℝ} (hx : 0 < x) :
    thetaCuspNativeReflectionJet n x-thetaCuspFirstAtomReflectionJet n x =
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*thetaCuspFirstAtomReflectionJet i x *
        thetaCuspLikelihoodReflectionErrorJet (n-i) x := by
  have hf : ContDiff ℝ n (fun y : ℝ => thetaCuspSourceTerm y 1) := by
    unfold thetaCuspSourceTerm thetaCuspSeed
    fun_prop
  have hF : ContDiff ℝ n thetaCuspFullSource := contDiff_thetaCuspFullSource.of_le
    (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have hfl : ContDiffAt ℝ n (fun t : ℝ => thetaCuspSourceTerm (x+t) 1) 0 :=
    (hf.comp (contDiff_const.add contDiff_id)).contDiffAt
  have hfr : ContDiffAt ℝ n (fun t : ℝ => thetaCuspSourceTerm (x-t) 1) 0 :=
    (hf.comp (contDiff_const.sub contDiff_id)).contDiffAt
  have hFl : ContDiffAt ℝ n (fun t : ℝ => thetaCuspFullSource (x+t)) 0 :=
    (hF.comp (contDiff_const.add contDiff_id)).contDiffAt
  have hFr : ContDiffAt ℝ n (fun t : ℝ => thetaCuspFullSource (x-t)) 0 :=
    (hF.comp (contDiff_const.sub contDiff_id)).contDiffAt
  have hl := remainder_left_contDiff n hx
  have hr := remainder_right_contDiff n hx
  have hL : ContDiffAt ℝ n (thetaCuspLikelihoodReflectionError x) 0 := (hl.add hr).add (hl.mul hr)
  have he := Filter.EventuallyEq.iteratedDeriv_eq n (thetaCuspNativeReflectionError_eventually_factor hx)
  rw [iteratedDeriv_fun_sub (hFl.mul hFr) (hfl.mul hfr),
    iteratedDeriv_fun_mul (hfl.mul hfr) hL] at he
  exact he

end
end RHTower
