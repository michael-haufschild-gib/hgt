import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.RealSlice

/-! # Real-slice character independence with moving spectral projectors -/

open Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.CircuitContacts
open SelectedDates.AlgebraicCurves
noncomputable section

/-- Orbit tests have field-dependent coefficients because the eigenprojectors
move. A relation on a real field interval forces every algebraic coefficient
germ to vanish separately. -/
theorem weighted_exp_sum_real_slice {I : Type*} [Fintype I] (f a : I → ℂ → ℂ)
    (hf : ∀ i, AnalyticAt ℂ (f i) 0) (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (hF : ∀ i, IsAlgebraic (RatFunc ℂ) (ofMero (f i) (hf i).meromorphicAt))
    (hA : ∀ i, IsAlgebraic (RatFunc ℂ) (ofMero (a i) (ha i).meromorphicAt))
    (hd : ∀ i j, i≠j → ∀ c : ℂ, ¬ ((fun z => f i z-f j z) =ᶠ[𝓝[≠] 0] fun _ => c))
    (hz : ∀ᶠ x : ℝ in 𝓝 0, ∑ i, a i x*Complex.exp (f i x)=0) :
    ∀ i, ofMero (a i) (ha i).meromorphicAt=0 := by
  let g (i : I) (z : ℂ) := a i z*Complex.exp (f i z)
  have hg (i : I) : AnalyticAt ℂ (g i) 0 := (ha i).mul (hf i).cexp
  have hs : AnalyticAt ℂ (fun z => ∑ i, g i z) 0 := Finset.analyticAt_fun_sum _ fun i _ => hg i
  have he := AnalyticAt.eventuallyEq_zero_of_eventually_ofReal_eq_zero hs hz
  let c (i : I) : curveField := ⟨ofMero (a i) (ha i).meromorphicAt,mem_algebraicClosure_iff.mpr (hA i)⟩
  have hzero : ∑ i, (c i:MeroGerm)*ofMero (fun z => Complex.exp (f i z)) (hf i).cexp.meromorphicAt=0 := by
    have hp (i : I) : (c i:MeroGerm)*ofMero (fun z => Complex.exp (f i z)) (hf i).cexp.meromorphicAt =
        ofMero (g i) (hg i).meromorphicAt := by
      change ofMero (a i) (ha i).meromorphicAt*_ = _
      rw [ofMero_mul]
      rfl
    simp_rw [hp]
    rw [sum_germs g _ hs.meromorphicAt,ofMero_eq_zero_iff]
    exact he.filter_mono nhdsWithin_le_nhds
  intro i
  exact congrArg Subtype.val (algebraic_action_exponentials f hf hF hd c hzero i)

/-- If an orbit test is nonzero at one physical date on the baseline,
its coefficients cannot vanish identically near the baseline. -/
theorem field_test_nontrivial {I : Type*} [Fintype I] (f a : I → ℂ → ℂ)
    (hf : ∀ i, AnalyticAt ℂ (f i) 0) (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (hF : ∀ i, IsAlgebraic (RatFunc ℂ) (ofMero (f i) (hf i).meromorphicAt))
    (hA : ∀ i, IsAlgebraic (RatFunc ℂ) (ofMero (a i) (ha i).meromorphicAt))
    (hd : ∀ i j, i≠j → ∀ c : ℂ, ¬ ((fun z => f i z-f j z) =ᶠ[𝓝[≠] 0] fun _ => c))
    {u : ℂ} (hu : ∑ i, a i 0*Complex.exp (u*f i 0)≠0) :
    ∃ᶠ x : ℝ in 𝓝 0, ∑ i, a i x*Complex.exp (f i x)≠0 := by
  by_contra h
  have hz : ∀ᶠ x : ℝ in 𝓝 0, ∑ i, a i x*Complex.exp (f i x)=0 := by
    simpa only [not_frequently,not_not] using h
  have hc := weighted_exp_sum_real_slice f a hf ha hF hA hd hz
  apply hu
  apply Finset.sum_eq_zero
  intro i _
  have hi := (ofMero_eq_zero_iff _).mp (hc i)
  have h₁ : Tendsto (a i) (𝓝[≠] (0:ℂ)) (𝓝 (a i 0)) :=
    (ha i).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h₂ : Tendsto (a i) (𝓝[≠] (0:ℂ)) (𝓝 0) := tendsto_const_nhds.congr' hi.symm
  rw [tendsto_nhds_unique h₁ h₂,zero_mul]

#print axioms field_test_nontrivial
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.CircuitContacts
