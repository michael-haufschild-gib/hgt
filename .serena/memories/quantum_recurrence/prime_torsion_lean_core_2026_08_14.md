# Prime-torsion target-cap Lean core (2026-08-14)

Formalized three unconditional modules:

- `formal/GaloisForLFunctions/HTGeometry/PrimeTorsionOrbitAvoidance.lean`: general finite automorphism survivor bound, exact `p^d-(p-1)|bad|` lower count, complete nonzero prime-scalar avoidance.
- `formal/GaloisForLFunctions/HTGeometry/FiniteGridCoherenceMoment.lean`: generalized alias-free grid from `M=2n+1` to every `2n<M`; exact norm moment equals `M^d` times permutation floor; deterministic cap cardinal and factorial-square-moment bounds; translated cap membership/cardinality; finite target union.
- `formal/GaloisForLFunctions/HTGeometry/PrimeTorsionTargetCapPolygon.lean`: if prime `p`, `2n<p`, and `(p-1)N n! (sum w_i^2)^n < threshold^(2n)`, exists q whose every nonzero scalar multiple avoids every translated target cap.

All wired into `HTGeometry.lean`. Final `lake build GaloisForLFunctions.HTGeometry.PrimeTorsionTargetCapPolygon` succeeded. Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`. `scripts/formal_tools.py lint` found no forbidden declaration error but failed globally because unrelated concurrent RHTower/HTGeometry modules were unwired; our modules were reachable.

New Stage-3 card: `docs/drafts/pipeline/3-formalized/prime-torsion-target-cap-polygon-law.md`. Parent Stage-2 card updated to `[LEAN CORE PROVED]`; master frontier log updated.

Scientific delta: modulus/polygon order and replica order decouple. Exact moment requires only `2n<p`, allowing modest n to control cap size while p remains exponentially large. Remaining formal frontier is arbitrary normalized-ray target reduction plus autonomous dense-flow shadowing/circuit asymptotics. First Brown onset remains separate hard core.