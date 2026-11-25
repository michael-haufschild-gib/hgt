import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicTimes.DenseSpecialization
import GaloisForLFunctions.HTGeometry.FiniteAlgebraicCoefficientLindemannWeierstrass

/-! # Exponential sums at every nonzero time algebraic over the physical parameters -/

open Set MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicTimes
noncomputable section

/-- Distinct spectral actions and their coefficients may vary analytically.
Algebraic values over rational parameters suffice to exclude cancellation
at all nonzero times algebraic over the sampled parameter field. -/
theorem ae_exponential_sum_ne_zero {m : ℕ} {I : Type*} [Fintype I] {U : Set (Fin m → ℝ)}
    (hU : IsOpen U) (a w : I → (Fin m → ℝ) → ℂ)
    (ha : ∀ i, AnalyticOnNhd ℝ (a i) U) (hw : ∀ i, AnalyticOnNhd ℝ (w i) U)
    (halg : ∀ (q : Fin m → ℚ), (fun i => (q i:ℝ))∈U → ∀ j,
      IsAlgebraic ℚ (a j (fun i => (q i:ℝ))) ∧ IsAlgebraic ℚ (w j (fun i => (q i:ℝ)))) :
    ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)), x∈U → Function.Injective (fun j => w j x) →
      (∃ j, a j x≠0) → ∀ t : ℝ, t≠0 → IsAlgebraic (parameterField x) t →
        ∑ j, a j x*Complex.exp (w j x*(t:ℂ))≠0 := by
  classical
  let V := {x∈U | Function.Injective (fun j => w j x) ∧ ∃ j, a j x≠0}
  have ho : IsOpen V := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨hux,hi,j,hj⟩ := hx
    have hdiff (i l : I) : ∀ᶠ y in 𝓝 x, i≠l → w i y≠w l y := by
      by_cases h : i=l
      · exact .of_forall fun _ h' => False.elim (h' h)
      · have hn := ((hw i x hux).sub (hw l x hux)).continuousAt.eventually_ne (sub_ne_zero.mpr (hi.ne h))
        exact hn.mono fun _ hh _ => sub_ne_zero.mp hh
    filter_upwards [hU.mem_nhds hux,eventually_all.mpr fun i => eventually_all.mpr (hdiff i),
      (ha j x hux).continuousAt.eventually_ne hj] with y hy h hne
    exact ⟨hy,fun {i l} h' => by_contra fun hn => h i l hn h',j,hne⟩
  let W := V ×ˢ ({0}ᶜ : Set ℝ)
  let G (p : (Fin m → ℝ) × ℝ) := ∑ j, a j p.1*Complex.exp (w j p.1*(p.2:ℂ))
  have hG : AnalyticOnNhd ℝ G W := by
    intro p hp
    apply Finset.analyticAt_fun_sum
    intro j _
    apply ((ha j p.1 hp.1.1).comp analyticAt_fst).mul
    apply analyticAt_cexp.restrictScalars.comp
    exact ((hw j p.1 hp.1.1).comp analyticAt_fst).mul ((Complex.ofRealCLM.analyticAt _).comp analyticAt_snd)
  have hsep (q : Fin m → ℚ) (t : ℝ) (hp : (fun i => (q i:ℝ),t)∈W) (ht : IsAlgebraic ℚ t) :
      G (fun i => (q i:ℝ),t)≠0 := by
    let x := fun i => (q i:ℝ)
    obtain ⟨⟨hx,hi,j,hj⟩,ht0⟩ := hp
    have htc : IsAlgebraic ℚ (t:ℂ) := ht.algHom (IsScalarTower.toAlgHom ℚ ℝ ℂ)
    have hne : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ht0
    intro hzero
    apply hj
    exact GaloisForLFunctions.RHTower.exp_algebraic_relation_eq_zero
      (fun l => w l x*(t:ℂ)) (fun l => a l x) (fun l => ((halg q hx l).2.mul htc))
      (fun l k h => hi (mul_right_cancel₀ hne h)) (fun l => (halg q hx l).1) hzero j
  filter_upwards [ae_algebraic_time_transfer (ho.prod isClosed_singleton.isOpen_compl) hG hsep] with x hx hu hi ha t ht hal
  exact hx t ⟨⟨hu,hi,ha⟩,ht⟩ hal

#print axioms ae_exponential_sum_ne_zero
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicTimes
