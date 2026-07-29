# No-one-story interaction law and unitary-completion flatness (2026-07-29)

Active parent card: `docs/drafts/pipeline/1-in-progress/actuality-conservation-boundary-colligation-law.md`.

## Exact second flatness no-go

Paper/Stage3 card: `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/fixed-carrier-unitary-completion-flatness.md`.
Lean: `formal/GaloisForLFunctions/HTGeometry/UnitaryCompletionMemoryFlatness.lean`.

Let A be a self-adjoint involution, P=(1-A)/2, Q=(1+A)/2. For two-sided unitaries U,V with the same visible preserving part UQ=VQ, define relative completion memory mu(U,V)=U†V. Lean proves:
- mu is two-sided unitary;
- mu Q = Q mu = Q;
- mu = Q + P mu P;
- V=U mu and VP=(UP)mu;
- mu(U,V)mu(V,W)=mu(U,W);
- triangular holonomy is identity;
- exact fiber classification: completions of UQ are precisely V=UR for two-sided unitary R fixing Q on both sides; R is unique.

Interpretation boundary: hidden completion freedom is real and exactly defect-supported, but any globally endpoint-labelled completion family is a pure coboundary. Therefore neither endpoints nor full unitary labels on one fixed carrier can generate force curvature.

Verification: direct `lake env lean GaloisForLFunctions/HTGeometry/UnitaryCompletionMemoryFlatness.lean` passed; final `lake build GaloisForLFunctions.HTGeometry.UnitaryCompletionMemoryFlatness` passed 2949/2949; axiom audit only propext/Classical.choice/Quot.sound; proof-debt scan clean; repository lint and `lint --check-generated` passed; no computations used.

## Frozen stronger conjecture

`[CONJECTURE — NO-ONE-STORY INTERACTION LAW]`

Every fundamental event is locally complete: no physical distinction is destroyed. But no endpoint-only reversible account of all events is compatible with their physical composition. The unique obstruction to such a global account is every fundamental interaction.

Public headline: **Every force exists because the universe cannot fit all its facts into one reversible story.**
Gravity version: **Gravity is the disagreement that remains after every quantum event has been made locally reversible.**

This supersedes the weaker idea that an assigned local history/memory field itself carries gravity. Globally assigned memories are flat. Force must be failure of functorial, path-independent globalization of source-complete local colligations.

Preliminary hostile verdict: `SURVIVES PRELIMINARY ATTACK`, no truth/novelty inference.
- Not merely absence of global section/topological nontriviality; curvature can exist on trivial bundles.
- Not anomaly inconsistency; target must be globally consistent and anomaly-free.
- Not ordinary completion torsor/connection/gerbe; those are parent mathematics.
- Narasimhan-Ramanan universal connections show completion geometry can realize arbitrary compact gauge connections and selects no physics.
- Hellerman-Orlando-Watanabe show gravitational anomalies already obstruct local tensor factorization.
- Karthik et al. arXiv:2607.05643 show coherently controlled equivalent Stinespring dilations can be operationally distinct, so completion history is not automatically gauge; generic lab history remains a false positive.

## Exact open core

`EXCEPTIONAL COMPLETION-DESCENT UNIQUENESS`: starting only from compatible exceptional pure pair and source-complete actualization, derive a presentation-invariant higher descent law with local conservative 4/6/4 colligations, zero obstruction for flat lab/QRF realizations, nontrivial obstruction for interactions even on trivial regions, exactly GSM + Lorentz gravity + mixed Higgs/soldering, Einstein/chiral/anomaly-free IR dynamics, HT source-nonclosure, no fifth force, and a finite prediction.

Representation lesson: global representability by endpoint-labelled objects is common flatness mechanism behind wall, quaternionic endpoint, and unitary-completion no-gos. New math must classify the unique exceptional non-flat descent law, not add a connection to globally supplied objects.