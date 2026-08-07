# Replica–Hilbert coarea incidence advance, 2026-08-07

## Conjecture loop
- C0 raw incidence-normalized coarea action: REDISCOVERED/CIRCULAR. Coarea formula makes it exactly pushforward event probability, retaining fibre sheets but giving no bound.
- C1 one-copy target span: USELESS in general because a short universal dictionary may linearly span full ambient space.
- C2 survivor: lift occupied return-removed targets to r-fold pure tensors first, then take span.

## Proved law
For target family z_c with replica norms <=1, S_r=span{z_c^tensor r}, q_r(psi)=||Proj_Sr psi^tensor r||^2:
- fidelity(psi,z_c)^r <= q_r(psi) for every c;
- complete capture union at threshold a is contained in {q_r>=a^r};
- for any finite quenched measure, P(capture) <= integral q_r / a^r.
No circuit-by-circuit union bound.

Define target synthesis A_r and evaluation A_r^*. Finrank(range A_r^*) = finrank(S_r). This is the finite-coordinate homogeneous Hilbert number of the occupied Veronese image. Duplicate labels do not change S_r, q_r, or Hilbert number. At r>0, adjoining zero (exact-return residual) changes none of them.

## Files
- Lean: formal/GaloisForLFunctions/HTGeometry/ReplicaHilbertCoareaIncidenceLaw.lean
- Card: docs/drafts/pipeline/3-formalized/replica-hilbert-coarea-incidence-law.md
- Umbrella import added to formal/GaloisForLFunctions/HTGeometry.lean
- Capstone: replicaHilbert_completeIncidence_bound

## Verification
- lake env lean module: PASS
- lake build GaloisForLFunctions.HTGeometry.ReplicaHilbertCoareaIncidenceLaw: PASS
- axioms: only propext, Classical.choice, Quot.sound
- global lint reached new module with no forbidden declaration, but was red on four unrelated concurrently added unreachable modules.

## Exact remaining frontier
This closes representation/complete-union/duplicate/return-zero problems, not Brown–Susskind. Need quenched growing-r bound for the single moment pairing integral ||Proj_Sr psi_J(t)^tensor r||^2 dP(J), plus proof circuit endpoint Hilbert growth does not fill symmetric sector too cheaply. Novelty of recurrence application remains externally unverified; underlying projection/adjoint rank facts are classical.
