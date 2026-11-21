import GaloisForLFunctions.HTGeometry.TwoLocalProjectiveTrotterCompilerLaw

/-! # Single-site-pair gate circuits -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- A circuit consisting of one prescribed lifted two-site gate. -/
def TwoQubitCircuit.singleOn {n : ℕ} (a b : Fin n) (h : a ≠ b)
    (G : Matrix.specialUnitaryGroup (Bool × Bool) ℂ) : TwoQubitCircuit n where
  gateCount := 1
  architecture := {sites := fun _ => (a,b),distinct := fun _ => h}
  gates := fun _ => G

theorem TwoQubitCircuit.singleOn_eval {n : ℕ} (a b : Fin n) (h : a ≠ b)
    (G : Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    (TwoQubitCircuit.singleOn a b h G).eval = twoQubitLift a b h G := by
  simp [TwoQubitCircuit.singleOn,TwoQubitCircuit.eval,TwoQubitArchitecture.contraction,
    TwoQubitArchitecture.gateLift,List.ofFn_succ]

end
end GaloisForLFunctions.HTGeometry
