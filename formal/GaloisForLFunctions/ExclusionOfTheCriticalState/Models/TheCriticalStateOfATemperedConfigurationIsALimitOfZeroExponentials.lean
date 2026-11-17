import GaloisForLFunctions.ExclusionOfTheCriticalState.Models.TemperedConfigurationsWithAFiniteOffLineLayerHaveCriticalStates

/-!
# The critical state of a tempered configuration is a limit of zero exponentials

For a layered energy (a nonnegative series of squares plus a finite-rank form) every ground state
with `λ ≠ 0` lies in the closed linear span of the layer vectors (`mem_closure_span_of_groundState`):
a vector orthogonal to all of them is admissible with zero pairing against the state, and the
Euler–Lagrange equation `𝓔(F, G) = λ⟪F, G⟫` then forces `⟪F, G⟫ = 0`.

For a tempered configuration `Z` the layer vectors are the exponentials
`e^{(z+8)u} cos(Im z · u)`, `e^{(z+8)u} sin(Im z · u)` at the shifted points `z = ±(ρ − ½)` of the
configuration (`zeroExponentials`). So the critical state of every conjugation-invariant tempered
configuration with a finite nonempty off-line layer is a norm limit in
`E = L²(e^{−8u} du, u < 0)` of finite exponential sums at its zeros
(`exists_configCriticalState_closure`). With finitely many on-line points as well the sums are
finite and the state is itself such a sum (`quartet_criticalState_explicit`).
-/

noncomputable section
open Set Filter Topology Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ExclusionOfTheCriticalState

namespace GroundState

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι κ : Type*}

/-- **A ground state lies in the closed span of the layer vectors.** -/
theorem LayeredEnergy.mem_closure_span_of_groundState [CompleteSpace E] [Fintype κ]
    (L : LayeredEnergy E ι κ) {F : E} {lam : ℝ} (hlam : lam ≠ 0) (hF : L.Admissible F)
    (hE : L.energy F = lam * ‖F‖ ^ 2) (hmin : ∀ G, L.Admissible G → lam * ‖G‖ ^ 2 ≤ L.energy G) :
    F ∈ (Submodule.span ℝ (Set.range L.a ∪ Set.range L.b ∪ Set.range L.p ∪
      Set.range L.q)).topologicalClosure := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
  intro G hG
  have h0 : ∀ x ∈ Set.range L.a ∪ Set.range L.b ∪ Set.range L.p ∪ Set.range L.q,
      inner ℝ x G = 0 := fun x hx =>
    Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span hx) hG
  have ha : ∀ j, inner ℝ (L.a j) G = 0 := fun j => h0 _ (Or.inl (Or.inl (Or.inl ⟨j, rfl⟩)))
  have hb : ∀ j, inner ℝ (L.b j) G = 0 := fun j => h0 _ (Or.inl (Or.inl (Or.inr ⟨j, rfl⟩)))
  have hp : ∀ k, inner ℝ (L.p k) G = 0 := fun k => h0 _ (Or.inl (Or.inr ⟨k, rfl⟩))
  have hq : ∀ k, inner ℝ (L.q k) G = 0 := fun k => h0 _ (Or.inr ⟨k, rfl⟩)
  -- `G` is invisible to every term of the energy
  have hGa : L.Admissible G := by
    have h : L.term G = fun _ => 0 := by
      funext j; unfold LayeredEnergy.term; rw [ha j, hb j]; ring
    unfold LayeredEnergy.Admissible
    rw [h]
    exact summable_zero
  have hpair : L.pair F G = 0 := by
    unfold LayeredEnergy.pair
    simp only [ha, hb, hp, hq, mul_zero, add_zero, zero_div, tsum_zero, Finset.sum_const_zero]
  have h := L.pair_eq_of_groundState hF hE hmin hGa
  rw [hpair] at h
  rw [real_inner_comm]
  exact (mul_eq_zero.mp h.symm).resolve_left hlam

end GroundState

namespace ModelStates

open GroundState
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)

/-- The exponential vectors of `Z` at the shifted points `±(ρ − ½)` of its carrier. -/
def zeroExponentials (Z : ZeroConfig) : Set ConfSpace :=
  {v | ∃ ρ ∈ Z.carrier, v = cosVec (ρ.re - 1 / 2) ρ.im ∨ v = sinVec (ρ.re - 1 / 2) ρ.im ∨
    v = cosVec (1 / 2 - ρ.re) (-ρ.im) ∨ v = sinVec (1 / 2 - ρ.re) (-ρ.im)}

variable {Z : ZeroConfig}

theorem layerVectors_subset_zeroExponentials (hfin : (offLineSet Z).Finite) :
    Set.range (configEnergy hfin).a ∪ Set.range (configEnergy hfin).b ∪
      Set.range (configEnergy hfin).p ∪ Set.range (configEnergy hfin).q ⊆ zeroExponentials Z := by
  rintro v (((⟨ρ, rfl⟩ | ⟨ρ, rfl⟩) | ⟨⟨x, b⟩, rfl⟩) | ⟨⟨x, b⟩, rfl⟩)
  · refine ⟨ρ.1, ρ.1.2, Or.inl ?_⟩
    show cosVec 0 (ρ.1 : ℂ).im = _
    rw [ρ.2, sub_self]
  · refine ⟨ρ.1, ρ.1.2, Or.inr (Or.inl ?_)⟩
    show sinVec 0 (ρ.1 : ℂ).im = _
    rw [ρ.2, sub_self]
  · refine ⟨x, (hfin.mem_toFinset.mp x.2).1, ?_⟩
    cases b <;> simp [configEnergy]
  · refine ⟨x, (hfin.mem_toFinset.mp x.2).1, ?_⟩
    cases b <;> simp [configEnergy]

/-- **The critical state of a tempered configuration is a limit of exponential sums at its zeros.**
For a conjugation-invariant tempered configuration with a finite off-line layer containing `ρ₀`, the
confined critical state lies in the closed span of the exponentials `zeroExponentials Z`. -/
theorem exists_configCriticalState_closure (hZ : TemperedConfig Z) (hfin : (offLineSet Z).Finite)
    (hconj : ∀ ρ ∈ Z.carrier, conj ρ ∈ Z.carrier ∧ Z.mult (conj ρ) = Z.mult ρ)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) (hre : ρ₀.re ≠ 1 / 2) :
    ∃ (a : ℝ) (F : ConfSpace), 0 < a ∧ (configEnergy hfin).Admissible F ∧ ‖F‖ = 1 ∧
      (configEnergy hfin).energy F + a * ‖F‖ ^ 2 = 0 ∧
      (∀ G : ConfSpace, (configEnergy hfin).Admissible G →
        0 ≤ (configEnergy hfin).energy G + a * ‖G‖ ^ 2) ∧
      F ∈ (Submodule.span ℝ (zeroExponentials Z)).topologicalClosure := by
  obtain ⟨a, F, ha, hFa, hF1, hEq, hmin⟩ := exists_configCriticalState hZ hfin hconj hρ₀ hre
  refine ⟨a, F, ha, hFa, hF1, hEq, hmin, ?_⟩
  have h := (configEnergy hfin).mem_closure_span_of_groundState (lam := -a) (neg_ne_zero.mpr ha.ne')
    hFa (by linarith) (fun G hG => by have := hmin G hG; linarith)
  exact Submodule.topologicalClosure_mono
    (Submodule.span_mono (layerVectors_subset_zeroExponentials hfin)) h

#print axioms exists_configCriticalState_closure

end ModelStates

end GaloisForLFunctions.ExclusionOfTheCriticalState
