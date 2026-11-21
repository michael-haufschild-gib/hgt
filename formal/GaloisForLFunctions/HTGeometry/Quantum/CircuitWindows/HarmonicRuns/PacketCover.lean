import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.HarmonicRuns.TranslatedArcs
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.HarmonicRuns.Itineraries

/-! # Covering moving circuit targets by short spectral tubes -/
open Filter Set MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.HarmonicRuns
noncomputable section
open SharpOccupation

private theorem enclosing_of_forward {I : Type*} [Fintype I] [Nonempty I]
    (θ : I → UnitAddCircle) {r : ℝ} (h : ∀ j, θ j ∈ forwardUnitArc r) :
    θ ∈ enclosingUnitArc r := by
  classical
  choose u hu he using h
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty u
  refine mem_iUnion.mpr ⟨i,fun j _ => ⟨u j-u i,⟨?_,?_⟩,?_⟩⟩
  · apply sub_nonneg.mpr
    rw [←hi]
    exact Finset.inf'_le u (Finset.mem_univ j)
  · linarith only [(hu j).2,(hu i).1]
  · rw [AddCircle.coe_sub,he,he]

/-- Rounding one global arc endpoint per harmonic suffices for every
energy coordinate. Each resulting packet lies in a single translated tube
of width (r+δ)/m. The number of centers is independent of dimension. -/
theorem packet_cover {I : Type*} [Fintype I] [Nonempty I] {m Q : ℕ}
    (hm : 0 < m) (g : Fin Q → UnitAddCircle) {δ r : ℝ}
    (hg : ∀ z : UnitAddCircle, ∃ i, z-g i ∈ forwardUnitArc δ)
    (hr : 0 ≤ r) (hδ : 0 ≤ δ) (hshort : 3*(r+δ) < 1)
    (p : Fin m → I → UnitAddCircle) :
    ∃ B : (Fin m → Fin Q) → I → UnitAddCircle, ∀ θ : I → UnitAddCircle,
      (∀ l : Fin m, ((l.val+1) • θ-p l) ∈ enclosingUnitArc r) →
      ∃ f : Fin m → Fin Q, θ-B f ∈ enclosingUnitArc ((r+δ)/(m:ℝ)) := by
  classical
  let c (f : Fin m → Fin Q) (j : I) (l : Fin m) := p l j+g (f l)
  choose B hB using fun (f : Fin m → Fin Q) (j : I) =>
    arcHistory_enclosed hm (c f j) (add_nonneg hr hδ) hshort
  refine ⟨B,?_⟩
  intro θ ht
  choose i u hu he using fun l => exists_anchor_lifts hr (ht l)
  let left (l : Fin m) := ((l.val+1) • θ-p l) (i l)
  choose f v hv hev using fun l => hg (left l)
  refine ⟨f,enclosing_of_forward _ (fun j => hB f j (θ j) ?_)⟩
  intro l
  refine ⟨u l j+v l,⟨add_nonneg (hu l j).1 (hv l).1,add_le_add (hu l j).2 (hv l).2⟩,?_⟩
  rw [AddCircle.coe_add,he,hev]
  change (((l.val+1) • θ j-p l j)-left l)+(left l-g (f l)) = (l.val+1) • θ j-(p l j+g (f l))
  abel

/-- Absolute spectral phases measured in turns. -/
def turns {n : ℕ} (H : selfAdjoint (Register n)) (t : ℝ) (j : Fin n → Bool) : UnitAddCircle :=
  ((-(t*H.2.isHermitian.eigenvalues j)/(2*Real.pi):ℝ):UnitAddCircle)

private def offset {I : Type*} (ψ : I → ℝ) (j : I) : UnitAddCircle :=
  ((ψ j/(2*Real.pi):ℝ):UnitAddCircle)

private theorem shifted_iff {n : ℕ} (H : selfAdjoint (Register n)) (ψ : (Fin n → Bool) → ℝ)
    (r : Icc (0:ℝ) (1/2)) (t : ℝ) :
    t ∈ shiftedTimes H ψ r ↔ turns H t-offset ψ ∈ enclosingUnitArc r := by
  let θ := fun j => -(t*H.2.isHermitian.eigenvalues j)-ψ j
  change spectralEnclosingArcLength θ ≤ 2*Real.pi*(r:ℝ) ↔ _
  rw [←mem_enclosingUnitArc_iff_spectralEnclosingArcLength θ r]
  have he : (fun j => ((θ j/(2*Real.pi):ℝ):UnitAddCircle)) = turns H t-offset ψ := by
    funext j
    exact (congrArg (fun b : ℝ => (b:UnitAddCircle)) (sub_div _ _ _)).trans (AddCircle.coe_sub ..)
  rw [he]

private theorem turns_nat_mul {n : ℕ} (H : selfAdjoint (Register n)) (k : ℕ) (t : ℝ) :
    turns H ((k:ℝ)*t) = k • turns H t := by
  funext j
  simp only [turns,Pi.smul_apply,←AddCircle.coe_nsmul,nsmul_eq_mul]
  congr 1
  ring

private theorem exists_offset {I : Type*} (b : I → UnitAddCircle) :
    ∃ ψ : I → ℝ, offset ψ = b := by
  let u (i : I) := (AddCircle.equivIco (1:ℝ) 0 (b i) : ℝ)
  refine ⟨fun i => u i*(2*Real.pi),funext fun j => ?_⟩
  change ((u j*(2*Real.pi)/(2*Real.pi):ℝ):UnitAddCircle) = b j
  rw [mul_div_cancel_right₀ _ two_pi_pos.ne']
  exact AddCircle.coe_equivIco

/-- A prescribed unitary itinerary is covered by at most Qᵐ translated
physical tubes. Each tube carries the angular error divided by m. -/
theorem itinerary_cover {n m Q : ℕ} (H : selfAdjoint (Register n)) (hm : 0 < m)
    (W : Fin m → Matrix.unitaryGroup (Fin n → Bool) ℂ) (g : Fin Q → UnitAddCircle)
    {δ r η : ℝ} (hg : ∀ z : UnitAddCircle, ∃ i, z-g i ∈ forwardUnitArc δ)
    (hr : 0 ≤ r) (hδ : 0 ≤ δ) (hshort : 3*(r+δ) < 1) (hη : η ≤ zeroGateArcTolerance r) :
    ∃ ψ : (Fin m → Fin Q) → (Fin n → Bool) → ℝ,
      itinerary H W η ⊆ ⋃ f, shiftedTimes H (ψ f) ((r+δ)/(m:ℝ)) := by
  choose q hq using fun l => unitary_visits_subset_shifted H (W l)
  let p (l : Fin m) := offset (q l)
  obtain ⟨B,hB⟩ := packet_cover hm g hg hr hδ hshort p
  choose ψ hψ using fun f => exists_offset (B f)
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hhalf : r < 1/2 := by linarith only [hδ,hshort]
  let a : Icc (0:ℝ) (1/2) := ⟨r,hr,hhalf.le⟩
  let b : Icc (0:ℝ) (1/2) := ⟨(r+δ)/(m:ℝ),div_nonneg (add_nonneg hr hδ) (Nat.cast_nonneg _),
    (div_le_self (add_nonneg hr hδ) hm1).trans (by linarith only [hshort])⟩
  refine ⟨ψ,?_⟩
  intro t ht
  have hmem (l : Fin m) : (l.val+1) • turns H t-p l ∈ enclosingUnitArc r := by
    obtain ⟨c,hc,hclose⟩ := ht l
    have hl := (shifted_iff H (q l) a _).mp (hq l r hr hhalf _ c hc (hclose.trans hη))
    rw [←turns_nat_mul]
    simpa only [Nat.cast_add_one,a,p] using hl
  obtain ⟨f,hf⟩ := hB (turns H t) hmem
  refine mem_iUnion.mpr ⟨f,(shifted_iff H (ψ f) b t).mpr ?_⟩
  rwa [hψ f]

#print axioms packet_cover
#print axioms itinerary_cover
end
end GaloisForLFunctions.HTGeometry.HarmonicRuns
