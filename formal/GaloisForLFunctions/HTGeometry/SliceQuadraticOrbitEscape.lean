/-
# The labeling orbit of the quadratic-rate relation on the traceless slice

The rigidity theorem for a quadratic-rate identity consumes only the two-parameter split slice
`(z, g) ↦ (boolShift z, g · X)` of a one-qubit extension chart, on which the local field is
traceless by construction.  Symmetrising over all labelings therefore also stays on that slice: if
the orbit product vanished at every slice point of the chart, then at each admissible `z` some
labeling would have a vanishing germ in `g`, and finitely many labelings cannot cover an infinite
set of admissible `z` values, so one labeling would be flat on an infinite set -- which the rigidity
theorem refutes.

Main results:
* `exists_eventually_eq_zero_of_prod_eventually_eq_zero` — a finite product of germs of analytic
  functions vanishes only if one factor does.
* `exists_sliceQuadraticOrbit_ne_zero` — **the labeling orbit is nonzero at a traceless slice
  point**.
-/
import GaloisForLFunctions.HTGeometry.ChartQuadraticRateEscape
import GaloisForLFunctions.HTGeometry.LayerSliceQuadraticTrace

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The germ ring of analytic functions has no zero divisors.**  If a finite product of functions
analytic at a point vanishes near that point, one of the factors does. -/
theorem exists_eventually_eq_zero_of_prod_eventually_eq_zero {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℂ → ℂ) (w : ℂ) (hf : ∀ i, AnalyticAt ℂ (f i) w)
    (hprod : ∀ᶠ g in 𝓝 w, ∏ i, f i g = 0) :
    ∃ i, ∀ᶠ g in 𝓝 w, f i g = 0 := by
  classical
  by_contra hcon
  have hcon' : ∀ i, ¬ (∀ᶠ g in 𝓝 w, f i g = 0) := fun i h => hcon ⟨i, h⟩
  have hne : ∀ i, ∀ᶠ g in 𝓝[≠] w, f i g ≠ 0 := by
    intro i
    rcases (hf i).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd h (hcon' i)
    · exact h
  have hall : ∀ᶠ g in 𝓝[≠] w, ∀ i, f i g ≠ 0 := Filter.eventually_all.mpr hne
  have hzero : ∀ᶠ g in 𝓝[≠] w, ∏ i, f i g = 0 := nhdsWithin_le_nhds hprod
  have hfalse : ∀ᶠ g in 𝓝[≠] w, False := by
    filter_upwards [hall, hzero] with g hg hg0
    exact (Finset.prod_ne_zero_iff.mpr fun i _ => hg i) hg0
  have hnb : Filter.NeBot (𝓝[≠] w) := by infer_instance
  exact hnb.ne (Filter.eventually_false_iff_eq_bot.mp hfalse)

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- **The labeling orbit of the quadratic-rate relation is nonzero at a traceless slice point.** -/
theorem exists_sliceQuadraticOrbit_ne_zero [Nonempty A] (hcard : 3 ≤ Fintype.card A)
    {E : A → ℝ} (hE : Function.Injective fun a => (E a : ℂ))
    (hgap : ∀ α β γ δ : A, α ≠ β → γ ≠ δ →
      ((E β : ℂ) - (E α : ℂ)) = ((E δ : ℂ) - (E γ : ℂ)) → (α, β) = (γ, δ))
    {M : Matrix A A ℂ} (hMherm : M.IsHermitian) (hM : ∀ α β : A, α ≠ β → M α β * M β α ≠ 0)
    {z₀ : ℂ}
    (hbase : Function.Injective (layeredEnergy (fun a => (E a : ℂ)) (boolShift z₀)))
    (C : LocalExtensionEigenbranchChart (fun a => (E a : ℂ)) (boolShift z₀) M)
    (c : A × Bool → ℂ) (κ : ℂ) (hzero : ∑ i, c i = 0) (hcne : c ≠ 0) :
    ∃ z g : ℂ, selectedPairChartPoint (boolShift z₀) false true z g ∈ C.U ∧
      (∏ σ : Equiv.Perm (A × Bool),
        ((∑ i, c i * C.branch (σ i)
            (selectedPairChartPoint (boolShift z₀) false true z g)) ^ (2 : ℕ)
          - κ * ((localExtensionMatrix (fun a => (E a : ℂ))
              (selectedPairChartPoint (boolShift z₀) false true z g).1 M
              (selectedPairChartPoint (boolShift z₀) false true z g).2) ^ (2 : ℕ)).trace)) ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨D⟩ := exists_selectedLayerSliceData E (boolShift z₀) M hbase C
    (by decide : (false : Bool) ≠ true)
  set V : Matrix (A × Bool) (A × Bool) ℂ := layerCrossPerturbation M with hV
  have hMne : M ≠ 0 := by
    obtain ⟨a, b, hab⟩ : ∃ a b : A, a ≠ b := by
      have : 1 < Fintype.card A := by omega
      exact Fintype.exists_pair_of_one_lt_card this
    intro h0
    exact hM a b hab (by rw [h0]; simp)
  have hQv : (V ^ (2 : ℕ)).trace ≠ 0 := trace_sq_layerCrossPerturbation_ne_zero hMherm hMne
  set bad : Set ℂ := Set.range (fun p : A × A => (E p.2 : ℂ) - (E p.1 : ℂ)) with hbad
  set S' : Set ℂ := D.S \ bad with hS'
  have hS'inf : S'.Infinite := D.infinite.sdiff (Set.finite_range _)
  have hshiftline : ∀ z : ℂ, selectedPairShiftLine (boolShift z₀) false true z = boolShift z :=
    fun z => selectedPairShiftLine_boolShift z₀ z
  have havoid : ∀ z ∈ S', z ≠ 0 ∧ ∀ α β : A, α ≠ β → z ≠ (E β : ℂ) - (E α : ℂ) := by
    intro z hz
    refine ⟨?_, fun α β _ hEq => hz.2 ⟨(α, β), hEq.symm⟩⟩
    intro h0
    obtain ⟨a⟩ : Nonempty A := inferInstance
    exact hz.2 ⟨(a, a), by rw [h0]; ring⟩
  have hinj : ∀ z ∈ S', Function.Injective (layerSplitEnergy (fun a => (E a : ℂ)) z) := by
    intro z hz
    have := D.simple z hz.1
    rwa [hshiftline z, layeredEnergy_boolShift] at this
  have hslicemat : ∀ z g : ℂ,
      localExtensionMatrix (fun a => (E a : ℂ))
          (selectedPairChartPoint (boolShift z₀) false true z g).1 M
          (selectedPairChartPoint (boolShift z₀) false true z g).2
        = Matrix.diagonal (layerSplitEnergy (fun a => (E a : ℂ)) z) + g • V := by
    intro z g
    show localExtensionMatrix (fun a => (E a : ℂ))
        (selectedPairShiftLine (boolShift z₀) false true z) M
        (g • selectedLayerExchangeMatrix false true) = _
    rw [localExtensionMatrix_selectedLayer, hshiftline z, layeredEnergy_boolShift,
      selectedLayerCoupling_bool]
  set fac : Equiv.Perm (A × Bool) → ℂ → ℂ → ℂ := fun σ z g =>
    (∑ i, c i * C.branch (σ i) (selectedPairChartPoint (boolShift z₀) false true z g)) ^ (2 : ℕ)
      - κ * ((∑ x, layerSplitEnergy (fun a => (E a : ℂ)) z x ^ (2 : ℕ)) + g ^ (2 : ℕ) * (V ^ (2 : ℕ)).trace)
    with hfac
  have hfacEq : ∀ (σ : Equiv.Perm (A × Bool)) (z g : ℂ), fac σ z g
      = (∑ i, c i * C.branch (σ i)
            (selectedPairChartPoint (boolShift z₀) false true z g)) ^ (2 : ℕ)
        - κ * ((localExtensionMatrix (fun a => (E a : ℂ))
              (selectedPairChartPoint (boolShift z₀) false true z g).1 M
              (selectedPairChartPoint (boolShift z₀) false true z g).2) ^ (2 : ℕ)).trace := by
    intro σ z g
    rw [hfac, hslicemat z g, trace_sq_layerExtensionSlice]
  have hprodZero : ∀ z ∈ S', ∀ᶠ g in 𝓝 (0 : ℂ), ∏ σ : Equiv.Perm (A × Bool), fac σ z g = 0 := by
    intro z hz
    filter_upwards [D.memChart z hz.1] with g hg
    rw [Finset.prod_congr rfl (fun σ _ => hfacEq σ z g)]
    exact hcon z g hg
  have hfacAnalytic : ∀ z ∈ S', ∀ σ : Equiv.Perm (A × Bool),
      AnalyticAt ℂ (fun g => fac σ z g) 0 := by
    intro z hz σ
    refine AnalyticAt.sub ?_ ?_
    · refine AnalyticAt.pow ?_ 2
      refine Finset.analyticAt_fun_sum _ fun i _ => ?_
      exact analyticAt_const.mul (D.analytic z hz.1 (σ i))
    · exact analyticAt_const.mul (analyticAt_const.add
        ((analyticAt_id.pow 2).mul analyticAt_const))
  have hsome : ∀ z ∈ S', ∃ σ : Equiv.Perm (A × Bool),
      ∀ᶠ g in 𝓝 (0 : ℂ), fac σ z g = 0 := by
    intro z hz
    exact exists_eventually_eq_zero_of_prod_eventually_eq_zero (fun σ => fac σ z) 0
      (fun σ => hfacAnalytic z hz σ) (hprodZero z hz)
  set T : Equiv.Perm (A × Bool) → Set ℂ := fun σ =>
    {z | z ∈ S' ∧ ∀ᶠ g in 𝓝 (0 : ℂ), fac σ z g = 0} with hT
  have hcover : S' ⊆ ⋃ σ : Equiv.Perm (A × Bool), T σ := by
    intro z hz
    obtain ⟨σ, hσ⟩ := hsome z hz
    exact Set.mem_iUnion.mpr ⟨σ, hz, hσ⟩
  obtain ⟨σ, hσinf⟩ : ∃ σ : Equiv.Perm (A × Bool), (T σ).Infinite := by
    by_contra hall
    push Not at hall
    exact hS'inf ((Set.finite_iUnion hall).subset hcover)
  set d : A × Bool → ℂ := fun j => c (σ.symm j) with hd
  have hdne : d ≠ 0 := by
    intro h0
    refine hcne ?_
    funext i
    have := congrFun h0 (σ i)
    simpa [hd] using this
  have hdsum : (∑ j, d j) = 0 := by
    rw [hd]
    rw [Fintype.sum_equiv σ (fun i => c i) (fun j => c (σ.symm j)) fun i => by simp] at hzero
    exact hzero
  have hTsub : ∀ z ∈ T σ, z ∈ S' := fun z hz => hz.1
  refine hdne ?_
  refine localExtension_quadraticRate_eq_zero_unconditional hcard hE hgap hM d
    (κ := κ) (Q₀ := fun z => ∑ x, layerSplitEnergy (fun a => (E a : ℂ)) z x ^ (2 : ℕ)) hQv hσinf
    (fun z hz => havoid z (hTsub z hz)) (fun z hz => hinj z (hTsub z hz))
    (fun z i g => C.branch i (selectedPairChartPoint (boolShift z₀) false true z g))
    (fun z hz i => D.analytic z (hTsub z hz).1 i) ?_ ?_ ?_ hdsum
  · intro z hz i
    have := D.base z (hTsub z hz).1 i
    rwa [hshiftline z, layeredEnergy_boolShift] at this
  · intro z hz i
    have hr := D.root z (hTsub z hz).1 i
    filter_upwards [hr] with g hg
    rwa [hshiftline z, layeredEnergy_boolShift, selectedLayerCoupling_bool] at hg
  · intro z hz
    filter_upwards [hz.2] with g hg
    have hswap : (∑ i, c i * C.branch (σ i)
        (selectedPairChartPoint (boolShift z₀) false true z g))
        = ∑ j, d j * C.branch j
          (selectedPairChartPoint (boolShift z₀) false true z g) :=
      Fintype.sum_equiv σ _ _ fun i => by simp [hd]
    rw [hfac] at hg
    simp only [sub_eq_zero] at hg
    rw [← hswap]
    exact hg

end

end GaloisForLFunctions.HTGeometry
