import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.TriplePacking

/-! # Three mutually signalling sites require three calls across their separating cuts -/
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- Pool all information within each fibre and retain only inter-fibre calls. -/
def contract (f : V→W) : List (V×V) → List (W×W)
  | [] => []
  | e::w => if f e.1=f e.2 then contract f w else (f e.1,f e.2)::contract f w

theorem contract_input (f : V→W) (w : List (V×V)) {i j : V} (h : j∈inputs w i) :
    f j∈inputs (contract f w) (f i) := by
  induction w generalizing i j with
  | nil => simpa only [inputs,Finset.mem_singleton,contract] using congrArg f (Finset.mem_singleton.mp h)
  | cons e w ih =>
    by_cases he : f e.1=f e.2
    · rw [contract,if_pos he]
      by_cases hi : i=e.1 ∨ i=e.2
      · rw [inputs,if_pos hi,Finset.mem_union] at h
        have hh : f j∈inputs (contract f w) (f e.2) :=
          h.elim (fun h => he ▸ ih h) (fun h => ih h)
        rcases hi with rfl | rfl
        · rwa [he]
        · exact hh
      · exact ih (by simpa only [inputs,if_neg hi] using h)
    · rw [contract,if_neg he]
      by_cases hi : i=e.1 ∨ i=e.2
      · rw [inputs,if_pos hi,Finset.mem_union] at h
        have hi' : f i=f e.1 ∨ f i=f e.2 := hi.imp (congrArg f) (congrArg f)
        rw [inputs,if_pos hi',Finset.mem_union]
        exact h.imp (fun h => ih h) (fun h => ih h)
      · exact inputs_mono _ _ _ (ih (by simpa only [inputs,if_neg hi] using h))

/-- Any three distinct bins with a fully exchanging representative in
each require three inter-bin calls. A gate crossing both cuts counts once. -/
theorem three_bin_floor (w : List (V×V)) (f : V→Fin 3) (v : Fin 3→V)
    (hv : ∀ i, f (v i)=i) (hall : ∀ i j, v j∈inputs w (v i)) :
    3≤(contract f w).length := by
  have h := path_exchange_budget (contract f w) (fun i j _ _ => by
    simpa only [hv] using contract_input f w (hall i j))
  omega

end GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal
