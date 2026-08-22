import GaloisForLFunctions.HTGeometry.HaferkampFlattenedTerminalPhaseGenericity

/-!
# Pre-saturation terminal-phase rank witness

Appendix B of Haferkamp--Faist--Kothakonda--Eisert--Yunger Halpern (2022)
requires one fresh nonidentity Pauli direction for each backwards-light-cone
block.  The finite Pauli dictionary has enough such directions strictly below
the `4^n - 1` saturation threshold.  This module packages the selection,
compatible BLC assembly, and real terminal-phase derivative-rank bound into
one closed witness theorem.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace BackwardsLightCone

/-- Every backwards-light-cone architecture on at least two qubits admits a
terminal-phase chart whose contraction derivative has rank at least `T` in the
strict Pauli pre-saturation range. -/
theorem exists_terminalPhase_rank_witness
    {n T : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    (cone : BackwardsLightCone n edges root) (hn : 1 < n)
    (hT : T < 4 ^ n - 1) :
    ∃ labels : List (Fin n → Option (Fin 3)),
      ∃ assembly : TerminalBlockPrefixAssembly cone 1 labels,
        T ≤ Module.finrank ℝ
          (fderiv ℝ (fun x => (assembly.terminalPhaseLiftedWord x).reverse.prod) 0).range := by
  obtain ⟨P, hPnonid, hPind⟩ :=
    exists_linearIndependent_haferkampNonidentityPauliFamily hT
  let labels : List (Fin n → Option (Fin 3)) := List.ofFn P
  have hlabels_nonid : ∀ Q ∈ labels, Q ≠ fun _ => none := by
    intro Q hQ
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hQ
    rw [← hi]
    exact hPnonid i
  obtain ⟨assembly⟩ :=
    nonempty_terminalBlockPrefixAssembly cone hn labels hlabels_nonid 1
      one_isFinitePauliClifford
  refine ⟨labels, assembly, ?_⟩
  have hlength : labels.length = T := by
    simp [labels]
  let cast : Fin labels.length → Fin T := fun i => Fin.cast hlength i
  have hcast_inj : Function.Injective cast := Fin.cast_injective hlength
  have hget (i : Fin labels.length) : labels.get i = P (cast i) := by
    change (List.ofFn P).get i = P (cast i)
    rw [List.get_ofFn]
  have hlabels_ind : LinearIndependent ℂ
      (fun i : Fin labels.length => finitePauliMatrix (labels.get i)) := by
    rw [show (fun i : Fin labels.length => finitePauliMatrix (labels.get i)) =
        ((fun i => finitePauliMatrix (P i)) ∘ cast) by
      funext i
      rw [hget]
      rfl]
    exact hPind.comp cast hcast_inj
  rw [← hlength]
  exact assembly.finrank_range_ge_terminalPhaseContraction_fderiv hlabels_ind

end BackwardsLightCone

end

end GaloisForLFunctions.HTGeometry
