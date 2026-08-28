# HC87 modular-superselection charged-unitary bypass no-go (2026-08-28)

Formal module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingModularSuperselectionChargedUnitaryBypassNoGo`.
Card: `docs/drafts/pipeline/3-formalized/hb-modular-superselection-charged-unitary-bypass-no-go.md`.

New result: coordinate transposition on `lp (fun _ : ℕ × ℕ => ℂ) 2`, realized by corpus `HTGeometry.lpReindexEquiv (Equiv.prodComm ℕ ℕ)`, maps the actual HC86 visible charged double-KMS half-density exactly to the partner half-density for every theta Hawking resonance and prime. At positive horizon charge, this exact bounded unitary conjugation coexists with the complete Xi source-modular superselection certificate, physical port-dissipation identity, failure of occupation-preserving alignment, and failure of every finite-Rees-moderate scalar sewing family. Main theorem is a closed universal proposition with no external assumptions.

Route impact: modular superselection separates scalar prime-valuation profiles but is representation-relative; it cannot by itself exclude the charged doubled-sector escape. HB must derive source-faithful representation selection or a phase-sensitive Ward law that rules out coordinate/charge conjugation.

Audit: direct Lean passed; targeted build passed 10,999/10,999; representative axioms only `propext`, `Classical.choice`, `Quot.sound`; lint had only pre-existing unreachable modules and no HC87 finding. Umbrella import wired. Frontier map remained read-only.

Next hardest audit: phase-sensitive chiral Ward / tilted-backreaction corpus laws; test whether they exclude swap or admit a conjugate phase-twist escape.