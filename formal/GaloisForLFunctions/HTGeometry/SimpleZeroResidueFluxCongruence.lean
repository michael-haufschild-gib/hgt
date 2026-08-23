import GaloisForLFunctions.HTGeometry.FiniteJetQuotientCongruence
import GaloisForLFunctions.HTGeometry.ResidueFilledFluxGerm
import GaloisForLFunctions.HTGeometry.ReflectedDividedDifference

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- At a simple zero, the canonical residue-filled flux germ is the germ of the
regular logarithmic flux of its divided unit in the translated coordinate. -/
theorem fluxGerm_eventuallyEq_simpleZeroResidueFlux {f u : ℂ → ℂ} {ρ : ℂ}
    (hf : AnalyticAt ℂ f ρ) (hu : Differentiable ℂ u)
    (hfac : ∀ z, f z = (z - ρ) * u z) (hu0 : u ρ ≠ 0) :
    fluxGerm f ρ =ᶠ[𝓝 0] simpleZeroResidueFlux (fun x => u (x + ρ)) := by
  have hfun : f = fun z => (z - ρ) * u z := funext hfac
  have hroot : f ρ = 0 := by rw [hfac]; simp
  have hderiv : deriv f ρ = u ρ := by
    rw [hfun]
    change deriv ((fun z : ℂ => z - ρ) * u) ρ = u ρ
    simpa using (((hasDerivAt_id ρ).sub_const ρ).mul (hu ρ).hasDerivAt).deriv
  have hderivne : deriv f ρ ≠ 0 := by rwa [hderiv]
  have hord : analyticOrderAt f ρ = (1 : ℕ∞) :=
    hf.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hroot hderivne
  have hne : ∀ᶠ x : ℂ in 𝓝 0, u (x + ρ) ≠ 0 := by
    have hT : ContinuousAt (fun x : ℂ => x + ρ) 0 := by fun_prop
    have hUne : ∀ᶠ y in 𝓝 ρ, u y ≠ 0 :=
      (hu.continuous.continuousAt : ContinuousAt u ρ).eventually_ne hu0
    have hUne' : ∀ᶠ y in 𝓝 ((0 : ℂ) + ρ), u y ≠ 0 := by
      simpa using hUne
    exact hT.tendsto.eventually hUne'
  filter_upwards [hne] with x hx
  by_cases hx0 : x = 0
  · subst x
    rw [fluxGerm_zero, hord]
    simp [simpleZeroResidueFlux]
  · rw [fluxGerm_of_ne_zero f ρ hx0, hfac (ρ + x)]
    have hderivfac : deriv f (ρ + x) = u (ρ + x) + x * deriv u (ρ + x) := by
      rw [hfun]
      change deriv ((fun z : ℂ => z - ρ) * u) (ρ + x) = _
      have h := (((hasDerivAt_id (ρ + x)).sub_const ρ).mul
        (hu (ρ + x)).hasDerivAt).deriv
      simpa using h
    rw [hderivfac]
    have hshiftderiv : deriv (fun y => u (y + ρ)) x = deriv u (x + ρ) := by
      rw [← iteratedDeriv_one, iteratedDeriv_comp_add_const, iteratedDeriv_one]
    rw [simpleZeroResidueFlux, hshiftderiv]
    have hx' : u (ρ + x) = u (x + ρ) := by ring
    rw [hx']
    field_simp [hx0, hx]
    ring

/-- Agreement of two entire simple-zero germs through depth `K + 1` fixes the
residue-filled completed flux through depth `K`.  The proof factors both germs by their
removable divided slopes and uses the exact one-step Taylor-jet shift. -/
theorem fluxGerm_iteratedDeriv_jet_congr_of_simple_zero {f g : ℂ → ℂ} {ρ : ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hfzero : f ρ = 0) (hgzero : g ρ = 0)
    (hfderiv : deriv f ρ ≠ 0) (hgderiv : deriv g ρ ≠ 0) {K : ℕ}
    (hjet : ∀ j ≤ K + 1, iteratedDeriv j f ρ = iteratedDeriv j g ρ) :
    ∀ k ≤ K, iteratedDeriv k (fluxGerm f ρ) 0 = iteratedDeriv k (fluxGerm g ρ) 0 := by
  have hfan : AnalyticOnNhd ℂ f Set.univ :=
    hf.differentiableOn.analyticOnNhd isOpen_univ
  have hgan : AnalyticOnNhd ℂ g Set.univ :=
    hg.differentiableOn.analyticOnNhd isOpen_univ
  have hfAt : AnalyticAt ℂ f ρ := hfan ρ (by simp)
  have hgAt : AnalyticAt ℂ g ρ := hgan ρ (by simp)
  have hdf : Differentiable ℂ (dslope f ρ) := by
    rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]
    exact hf.differentiableOn
  have hdg : Differentiable ℂ (dslope g ρ) := by
    rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]
    exact hg.differentiableOn
  let u : ℂ → ℂ := fun x => dslope f ρ (x + ρ)
  let v : ℂ → ℂ := fun x => dslope g ρ (x + ρ)
  have huDiff : Differentiable ℂ u := by
    dsimp only [u]
    exact hdf.comp (differentiable_id.add_const ρ)
  have hvDiff : Differentiable ℂ v := by
    dsimp only [v]
    exact hdg.comp (differentiable_id.add_const ρ)
  let U : Set ℂ := {x | u x ≠ 0} ∩ {x | v x ≠ 0}
  have hUopen : IsOpen U := by
    exact (isOpen_ne.preimage huDiff.continuous).inter
      (isOpen_ne.preimage hvDiff.continuous)
  have huan : AnalyticOnNhd ℂ u U := by
    intro x hx
    exact (huDiff.differentiableOn.analyticOnNhd isOpen_univ) x (by simp)
  have hvan : AnalyticOnNhd ℂ v U := by
    intro x hx
    exact (hvDiff.differentiableOn.analyticOnNhd isOpen_univ) x (by simp)
  have huCont : ContDiffOn ℂ (⊤ : ℕ∞) u U := huan.contDiffOn hUopen.uniqueDiffOn
  have hvCont : ContDiffOn ℂ (⊤ : ℕ∞) v U := hvan.contDiffOn hUopen.uniqueDiffOn
  have h0 : (0 : ℂ) ∈ U := by
    constructor
    · simpa [u, dslope_same] using hfderiv
    · simpa [v, dslope_same] using hgderiv
  have hunitjet : ∀ j ≤ K, iteratedDeriv j u 0 = iteratedDeriv j v 0 := by
    intro j hj
    change iteratedDeriv j (fun x => dslope f ρ (x + ρ)) 0 =
      iteratedDeriv j (fun x => dslope g ρ (x + ρ)) 0
    rw [iteratedDeriv_comp_add_const, iteratedDeriv_comp_add_const]
    simp only [zero_add]
    rw [HTGeometry.iteratedDeriv_dslope_self_eq_iteratedDeriv_succ_div hfAt j,
      HTGeometry.iteratedDeriv_dslope_self_eq_iteratedDeriv_succ_div hgAt j,
      hjet (j + 1) (by omega)]
  have hsimple := simpleZeroResidueFlux_jet_congr hUopen huCont hvCont
    (fun w hw => hw.1) (fun w hw => hw.2) h0 hunitjet
  have hfacf : ∀ z, f z = (z - ρ) * dslope f ρ z := by
    intro z
    have hs := sub_smul_dslope f ρ z
    rw [hfzero, sub_zero, smul_eq_mul] at hs
    exact hs.symm
  have hfacg : ∀ z, g z = (z - ρ) * dslope g ρ z := by
    intro z
    have hs := sub_smul_dslope g ρ z
    rw [hgzero, sub_zero, smul_eq_mul] at hs
    exact hs.symm
  have hfluxf : fluxGerm f ρ =ᶠ[𝓝 0] simpleZeroResidueFlux u := by
    simpa [u] using fluxGerm_eventuallyEq_simpleZeroResidueFlux hfAt hdf hfacf
      (by simpa [dslope_same] using hfderiv)
  have hfluxg : fluxGerm g ρ =ᶠ[𝓝 0] simpleZeroResidueFlux v := by
    simpa [v] using fluxGerm_eventuallyEq_simpleZeroResidueFlux hgAt hdg hfacg
      (by simpa [dslope_same] using hgderiv)
  intro k hk
  calc
    iteratedDeriv k (fluxGerm f ρ) 0 = iteratedDeriv k (simpleZeroResidueFlux u) 0 :=
      hfluxf.iteratedDeriv_eq k
    _ = iteratedDeriv k (simpleZeroResidueFlux v) 0 := hsimple k hk
    _ = iteratedDeriv k (fluxGerm g ρ) 0 := (hfluxg.iteratedDeriv_eq k).symm

end GaloisForLFunctions.HTGeometry
