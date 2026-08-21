import GaloisForLFunctions.HTGeometry.HaferkampBlockPrefixStep

/-!
# Recursive terminal-aware BLC block assembly

This is the literal recursion in Appendix B: every fresh Pauli direction is
first transported through the existing Clifford prefix, then receives a BLC
block with a retained terminal `SU(4)` coordinate.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace BackwardsLightCone

/-- A chronological sequence of terminal-aware BLC blocks, indexed by the
exact contraction of all earlier blocks. -/
inductive TerminalBlockPrefixAssembly
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    (cone : BackwardsLightCone n edges root) :
    Matrix.unitaryGroup (Fin n → Bool) ℂ →
      List (Fin n → Option (Fin 3)) → Type
  | nil (pre : Matrix.unitaryGroup (Fin n → Bool) ℂ) :
      TerminalBlockPrefixAssembly cone pre []
  | cons {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
      {P : Fin n → Option (Fin 3)} {Ps : List (Fin n → Option (Fin 3))}
      (step : TerminalBlockPrefixStep cone pre P)
      (tail : TerminalBlockPrefixAssembly cone
        (edgeListBlockContraction edges step.block.gates * pre) Ps) :
      TerminalBlockPrefixAssembly cone pre (P :: Ps)

/-- Every finite nonidentity Pauli list admits the recursively compatible
sequence of physical BLC blocks required by Appendix B. -/
theorem nonempty_terminalBlockPrefixAssembly
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    (cone : BackwardsLightCone n edges root) (hn : 1 < n)
    (labels : List (Fin n → Option (Fin 3)))
    (hlabels : ∀ P ∈ labels, P ≠ fun _ => none)
    (pre : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (hpre : IsFinitePauliClifford pre) :
    Nonempty (TerminalBlockPrefixAssembly cone pre labels) := by
  induction labels generalizing pre with
  | nil => exact ⟨.nil pre⟩
  | cons P Ps ih =>
      have hP : P ≠ fun _ => none := hlabels P (by simp)
      have hPs : ∀ Q ∈ Ps, Q ≠ fun _ => none := by
        intro Q hQ
        exact hlabels Q (by simp [hQ])
      obtain ⟨step⟩ := cone.exists_terminalBlockPrefixStep hn pre hpre P hP
      have hblock := step.block.contraction_isFinitePauliClifford
      have hnext : IsFinitePauliClifford
          (edgeListBlockContraction edges step.block.gates * pre) :=
        isFinitePauliClifford_mul _ _ hblock hpre
      obtain ⟨tail⟩ := ih hPs _ hnext
      exact ⟨.cons step tail⟩

end BackwardsLightCone

end

end GaloisForLFunctions.HTGeometry
