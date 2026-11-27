import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ShortArcHaar

/-! # Differences of phase packets contained in short arcs -/
open Finset Set
namespace GaloisForLFunctions.HTGeometry.PassageMoments.ExtremePair.ArcPacking
noncomputable section
variable {I : Type*} [Fintype I] [Nonempty I]

/-- An enclosing arc admits real representatives in one interval after
a common phase shift. Conversely the least representative is a usable anchor. -/
theorem arc_lifts (x : I → UnitAddCircle) {r : ℝ} (hr : 0≤r) :
    x∈enclosingUnitArc r ↔ ∃ c : UnitAddCircle, ∃ f : I → ℝ,
      (∀ i, f i∈Icc 0 r) ∧ ∀ i, x i=c+(f i:UnitAddCircle) := by
  classical
  constructor
  · intro h
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp h
    have hall (j : I) : x j-x i∈forwardUnitArc r := by
      by_cases hji : j=i
      · subst j
        exact ⟨0,⟨le_rfl,hr⟩,by simp⟩
      · exact hi j hji
    choose f hf hcoe using hall
    exact ⟨x i,f,hf,fun j => by rw [hcoe j]; abel⟩
  · rintro ⟨c,f,hf,he⟩
    obtain ⟨i,_,hi⟩ := exists_mem_eq_inf' (s:=Finset.univ) univ_nonempty f
    apply Set.mem_iUnion.mpr
    refine ⟨i,fun j _ => ⟨f j-f i,⟨sub_nonneg.mpr (hi ▸ inf'_le _ (mem_univ j)),?_⟩,?_⟩⟩
    · exact (sub_le_self _ (hf i).1).trans (hf j).2
    · rw [he i,he j,AddCircle.coe_sub]; abel

/-- Subtracting packets of arc length r doubles the length. -/
theorem arc_sub {x y : I → UnitAddCircle} {r : ℝ} (hr : 0≤r)
    (hx : x∈enclosingUnitArc r) (hy : y∈enclosingUnitArc r) : x-y∈enclosingUnitArc (2*r) := by
  obtain ⟨a,f,hf,hx'⟩ := (arc_lifts x hr).mp hx
  obtain ⟨b,g,hg,hy'⟩ := (arc_lifts y hr).mp hy
  refine (arc_lifts _ (by positivity)).mpr ⟨a-b-(r:UnitAddCircle),fun i => f i-g i+r,?_,?_⟩
  · intro i
    obtain ⟨hf₀,hf₁⟩ := hf i
    obtain ⟨hg₀,hg₁⟩ := hg i
    constructor <;> linarith only [hf₀,hf₁,hg₀,hg₁]
  · intro i
    rw [Pi.sub_apply,hx' i,hy' i,AddCircle.coe_add,AddCircle.coe_sub]; abel

/-- Duplicating a synchronized phase preserves the same arc width. -/
theorem arc_pullback {J : Type*} [Fintype J] [Nonempty J] (e : J → I) {x : I → UnitAddCircle}
    {r : ℝ} (hr : 0≤r) (hx : x∈enclosingUnitArc r) : x ∘ e∈enclosingUnitArc r := by
  obtain ⟨a,f,hf,hv⟩ := (arc_lifts x hr).mp hx
  exact (arc_lifts _ hr).mpr ⟨a,f ∘ e,fun j => hf (e j),fun j => hv (e j)⟩

#print axioms arc_sub
end
end GaloisForLFunctions.HTGeometry.PassageMoments.ExtremePair.ArcPacking
