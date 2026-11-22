import GaloisForLFunctions.HTGeometry.ParametricSpectralBranch
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # Distinct boundary slopes after adjoining a strongly split spin -/
open Filter Topology
namespace GaloisForLFunctions.HTGeometry.FirstGate.Boundary
noncomputable section
variable {I : Type*} [Fintype I]

private theorem locally_injective (f : I → ℂ → ℂ) (hf : ∀ j, ContinuousAt (f j) 0)
    (hi : Function.Injective (fun j => f j 0)) :
    ∀ᶠ u in 𝓝 (0:ℂ), Function.Injective (fun j => f j u) := by
  have h (i j : I) : ∀ᶠ u in 𝓝 (0:ℂ), (f i u=f j u → i=j) := by
    by_cases hij : i=j
    · exact Eventually.of_forall fun _ _ => hij
    · exact (((hf i).ne_iff_eventually_ne (hf j)).mp (hi.ne hij)).mono (fun _ hn he => (hn he).elim)
  exact eventually_all.mpr (fun i => eventually_all.mpr (h i))

private theorem cross_ne (f g : I → ℂ → ℂ) (hf : ∀ j, ContinuousAt (f j) 0)
    (hg : ∀ j, ContinuousAt (g j) 0) (hn : ∀ i j, f i 0≠g j 0) :
    ∀ᶠ u in 𝓝 (0:ℂ), ∀ i j, f i u≠g j u :=
  eventually_all.mpr (fun i => eventually_all.mpr (fun j => ((hf i).ne_iff_eventually_ne (hg j)).mp (hn i j)))

omit [Fintype I] in
private theorem sum_inj (a b : I→ℂ) (ha : Function.Injective a) (hb : Function.Injective b)
    (hab : ∀ i j, a i≠b j) : Function.Injective (Sum.elim a b) := by
  rintro (i|i) (j|j) h
  · exact congrArg Sum.inl (ha h)
  · exact (hab i j h).elim
  · exact (hab j i h.symm).elim
  · exact congrArg Sum.inr (hb h)

/-- The physical energy is ±1/u+e(±u). Its derivative with respect to the new
onsite field is ±[1−u²e′(±u)]. Close to zero both the energies and the slopes
are pairwise distinct, provided both old lists are distinct at zero. -/
theorem two_sector_separation (e : I → ℂ → ℂ) (ha : ∀ j, AnalyticAt ℂ (e j) 0)
    (h₀ : Function.Injective (fun j => e j 0))
    (h₁ : Function.Injective (fun j => deriv (e j) 0)) :
    ∀ᶠ u in 𝓝 (0:ℂ), u≠0 →
      Function.Injective (Sum.elim (fun j => u⁻¹+e j u) (fun j => -u⁻¹+e j (-u))) ∧
      Function.Injective (Sum.elim (fun j => 1-u^2*deriv (e j) u)
        (fun j => -1+u^2*deriv (e j) (-u))) := by
  have he := locally_injective e (fun j => (ha j).continuousAt) h₀
  have hd (j : I) : ContinuousAt (deriv (e j)) 0 := (ha j).deriv.continuousAt
  have hr := locally_injective (fun j => deriv (e j)) hd h₁
  have hneg : Tendsto (fun u : ℂ => -u) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg.continuousAt (x := (0:ℂ))).tendsto
  have flip (F : ℂ → ℂ) (hF : ContinuousAt F 0) : ContinuousAt (fun u : ℂ => F (-u)) 0 := by
    simpa only [ContinuousAt,Function.comp_def,neg_zero] using hF.tendsto.comp hneg
  have hec := cross_ne (fun j u => 1+u*e j u) (fun j u => -1+u*e j (-u))
    (fun j => continuousAt_const.add (continuousAt_id.mul (ha j).continuousAt))
    (fun j => continuousAt_const.add (continuousAt_id.mul (flip _ (ha j).continuousAt)))
    (fun i j => by norm_num)
  have hrc := cross_ne (fun j u => 1-u^2*deriv (e j) u) (fun j u => -1+u^2*deriv (e j) (-u))
    (fun j => continuousAt_const.sub ((continuousAt_id.pow 2).mul (hd j)))
    (fun j => continuousAt_const.add ((continuousAt_id.pow 2).mul (flip _ (hd j))))
    (fun i j => by norm_num)
  filter_upwards [he,hneg.eventually he,hr,hneg.eventually hr,hec,hrc] with u ep em rp rm ec rc
  intro hu
  constructor
  · refine sum_inj _ _ (fun _ _ h => ep (add_left_cancel h)) (fun _ _ h => em (add_left_cancel h)) ?_
    intro i j hij
    apply ec i j
    have hh := congrArg (u*·) hij
    simpa only [mul_add,mul_neg,mul_inv_cancel₀ hu] using hh
  · apply sum_inj _ _ _ _ rc
    · intro i j hij
      exact rp (mul_left_cancel₀ (pow_ne_zero _ hu) (sub_right_inj.mp hij))
    · intro i j hij
      exact rm (mul_left_cancel₀ (pow_ne_zero _ hu) (add_left_cancel hij))

#print axioms two_sector_separation
end
end GaloisForLFunctions.HTGeometry.FirstGate.Boundary
