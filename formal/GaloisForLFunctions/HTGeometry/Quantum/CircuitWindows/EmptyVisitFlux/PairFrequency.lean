import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.BoxLaw
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.FaceGeometry
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPauliPrefixPhaseLaw

/-! # Inward crossings at a specified ordered pair of energy levels -/
open Matrix Filter Set Topology MeasureTheory
namespace GaloisForLFunctions.HTGeometry.EmptyVisitFlux
noncomputable section

/-- Successive positive times at which the faster left endpoint is exactly
r turns behind the slower right endpoint. -/
def pairDate (E : I → ℝ) (i j : I) (r : ℝ) (k : ℕ) : ℝ :=
  (1-r+(k:ℝ))*(2*Real.pi/(E i-E j))

private theorem relative_phase {I : Type*} [Fintype I] [DecidableEq I]
    (E : I → ℝ) (i : I) (a : {j : I // j ≠ i}) (t : ℝ) :
    flow (fun k => E k/(2*Real.pi)) t a.val-flow (fun k => E k/(2*Real.pi)) t i =
      finiteClockPhasePoint (projectiveFrequency E i) t a := by
  change ((t*(E a.val/(2*Real.pi)):ℝ):UnitAddCircle)-((t*(E i/(2*Real.pi)):ℝ):UnitAddCircle) =
    ((t*(E a.val-E i)/(2*Real.pi):ℝ):UnitAddCircle)
  rw [←AddCircle.coe_sub]
  congr 1
  ring

/-- Among the exact pair contacts, the long-run fraction at which both
endpoints are the unique extremes of an affordable arc is r^(D−2). -/
theorem pair_contact_frequency {I : Type*} [Fintype I] [DecidableEq I] (E : I → ℝ)
    (hi : MaximallyProjectiveEnergy E) (i j : I) (hji : E j < E i) (r : Icc (0:ℝ) (1/2))
    (A : Set UnitAddCircle) (hA : A ∈ ({openArc r,forwardUnitArc r} : Set (Set UnitAddCircle))) :
    Tendsto (fun N : ℕ => (countTicks (fun k => pairFace A (fun b => E b/(2*Real.pi)) r
        (pairDate E i j r k) i j) (N+1):ℝ)/(N+1)) atTop (𝓝 ((r:ℝ)^(Fintype.card I-2))) := by
  classical
  let J := {b : I // b ≠ i}
  have hne : j ≠ i := fun he => hji.ne (congrArg E he)
  let b : J := ⟨j,hne⟩
  let K := {q : J // q ≠ b}
  let ω := projectiveFrequency E i
  let τ := 2*Real.pi/(E i-E j)
  let a := (1-(r:ℝ))*τ
  have hg := sub_pos.mpr hji
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  have hw : τ*ω b=(-1:ℤ)*(2*Real.pi) := by
    change 2*Real.pi/(E i-E j)*(E j-E i) = _; push_cast; field_simp [hg.ne']; ring
  have heq (k : ℕ) : pairDate E i j r k = a+(k:ℝ)*τ := by unfold pairDate; dsimp only [a,τ]; ring
  have hpin (k : ℕ) : flow (fun z => E z/(2*Real.pi)) (pairDate E i j r k) j -
      flow (fun z => E z/(2*Real.pi)) (pairDate E i j r k) i = ((r:ℝ):UnitAddCircle) := by
    rw [relative_phase E i b]
    change ((pairDate E i j r k*(E j-E i)/(2*Real.pi):ℝ):UnitAddCircle)=_
    rw [show pairDate E i j r k*(E j-E i)/(2*Real.pi) = (r:ℝ)-(k+1:ℕ) by
      unfold pairDate; push_cast; field_simp [hg.ne']; ring,AddCircle.coe_sub]
    have hone : ((1:ℝ):UnitAddCircle)=0 := AddCircle.coe_period 1
    have hn : ((((k+1:ℕ):ℝ)):UnitAddCircle) = 0 := by
      rw [show ((k+1:ℕ):ℝ)=(k+1) • (1:ℝ) by rw [nsmul_eq_mul,mul_one]]
      rw [AddCircle.coe_nsmul,hone,nsmul_zero]
    rw [hn,sub_zero]
  let test := fun k : ℕ => finiteClockPhasePoint (fun l : K => ω l.val) (a+k*τ) ∈ Set.pi (univ : Set K) (fun _ => A)
  have ht (k : ℕ) : pairFace A (fun z => E z/(2*Real.pi)) r (pairDate E i j r k) i j ↔ test k := by
    have hx (l : K) : flow (fun z => E z/(2*Real.pi)) (pairDate E i j r k) l.val.val -
        flow (fun z => E z/(2*Real.pi)) (pairDate E i j r k) i =
        finiteClockPhasePoint (fun c : K => ω c.val) (a+(k:ℝ)*τ) l := by
      rw [relative_phase E i l.val,heq]
      rfl
    constructor
    · intro h l _
      change _ ∈ A
      rw [←hx l]
      exact h.2.2 _ l.val.property (fun he => l.property (Subtype.ext he))
    · intro h
      refine ⟨div_lt_div_of_pos_right hji (by positivity),hpin k,?_⟩
      intro l hli hlj
      let c : K := ⟨⟨l,hli⟩,fun he => hlj (congrArg Subtype.val he)⟩
      exact (hx c).symm ▸ h c (mem_univ _)
  have hcount : Fintype.card K=Fintype.card I-2 := by
    have hj : Fintype.card J=Fintype.card I-1 := by simp [J,Fintype.card_subtype_compl]
    have hk : Fintype.card K=Fintype.card J-1 := by simp [K,Fintype.card_subtype_compl]
    omega
  have hbox : Set.pi (univ : Set K) (fun _ => A) ∈ ({openBox K r,closedBox K r} : Set (Set (K → UnitAddCircle))) := by
    rcases hA with h | h
    · exact Or.inl (congrArg (fun S => Set.pi (univ : Set K) (fun _ => S)) h)
    · exact Or.inr (congrArg (fun S => Set.pi (univ : Set K) (fun _ => S)) (show A=forwardUnitArc r from h))
  have h := pinned_box_frequencies ω (maximallyProjectiveEnergy_projectiveFrequency_independent E hi i)
    b hτ.ne' (-1) hw a r _ hbox
  change Tendsto (fun N : ℕ => (countTicks test (N+1):ℝ)/(N+1)) atTop (𝓝 ((r:ℝ)^Fintype.card K)) at h
  rw [hcount] at h
  have he : (fun k => pairFace A (fun z => E z/(2*Real.pi)) r (pairDate E i j r k) i j) = test :=
    funext fun k => propext (ht k)
  rwa [he]

#print axioms pair_contact_frequency
end
end GaloisForLFunctions.HTGeometry.EmptyVisitFlux
