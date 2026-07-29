Continuation sharpened actuality conservation.

Active Stage-1 card: docs/drafts/pipeline/1-in-progress/actuality-conservation-boundary-colligation-law.md. Public ontology now has two nested headlines: “Every event turns a quantum possibility into a piece of spacetime” and sharper “Spacetime is the quantum symmetry that could not survive an event.” Exceptional local version: “Reality does not happen inside spacetime. An event changes the symmetry law of a quantum distinction, and its new law is spacetime.”

Exact source audit:
- PurePairProductProjection.lean already proves commuting complex structures J1,J2 select comparison involution and exact agreement/disagreement projectors/ranges.
- quantum-disagreement-spacetime-law.md already records 6+4 source, pure-tangent reporter no-go, colour-preserving normal H/C2 survivor.
- QuaternionicWeakSpacetimeFracture.lean proves same real H carrier has left action (central -1 = -I4, no common fixed vector) and diagonal conjugation action (central -1 = +I4, invariant scalar 1 plus imaginary 3).
- four-dimensional-higgs-event-fracture-law.md already has local Pati-Salam carrier H⊕V6, source 2+2, target 1+3, T=0_H⊕I6, and global topological-debt/no-soldering no-go.

New exact bridge formalized:
- Paper: docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/symmetry-fracture-unitary-defect-conservation.md
- Lean: formal/GaloisForLFunctions/HTGeometry/SymmetryFractureDefectConservation.lean
For self-adjoint involution A, P=(1-A)/2, Q=(1+A)/2, and two-sided unitary U, define T=UQ and S=UP. Lean proves U=T+S, TA=T, SA=-S, T†T=Q, S†S=P, cross-orthogonality, TT†+SS†=1, initial/final defect equalities, ker T=im P, im S=ker T†, target reporter kernel=im T, canonical coker(T)≃im P, and that S realizes the defect equivalence. For trace-2 ten-involution existing theorem gives 4/6/4. This turns Lost≃New from dimension postulate into conditional unitary defect theorem.

Physics jump: exceptional local parent may take U=identity on underlying H⊕V6 while endpoint representation law changes. Then T=0_H⊕I6 and S=I_H⊕0_6. Six common directions preserve representation; four directions transmute from weak 2+2 to scalar+three 1+3. Actualization candidate is change of representation law, not carrier destruction or added Stinespring environment.

Hostile boundary:
- algebra is standard Julia/Halmos/partial-isometry defect theory, not new math;
- generic Stinespring U is noncanonical and unitary dilation has continuity issues;
- transported grading can make odd sector vanish;
- Cartan/broken-symmetry gravity is prior;
- local same-carrier identity does not solve EventTopologicalDebt or global Higgs≅TM no-go;
- outgoing 1+3 is not yet Lorentzian operational tangent, actualization, gravity, dynamics, or prediction.
Next exact open core: SOURCE-CANONICAL CHANGE OF REPRESENTATION LAW—derive why objective exceptional event selects left-to-diagonal quaternionic change and why outgoing 1+3 becomes causal geometry.

Verification: direct `lake env lean` passed; final `lake build GaloisForLFunctions.HTGeometry.SymmetryFractureDefectConservation` passed 2948/2948; #print axioms only propext/Classical.choice/Quot.sound; git diff --check passed; no stale Lean/lake process. Repository lint still fails only because concurrently edited unrelated ParametricSpectralBranch, SpectralCausality, SteinerMobiusDuality are not reachable from umbrella; generated indexes were repeatedly made stale by concurrent SteinerMobiusDuality edits. Shared workspace externally created commit d37511c1 (`research`) during work; this agent did not commit.
