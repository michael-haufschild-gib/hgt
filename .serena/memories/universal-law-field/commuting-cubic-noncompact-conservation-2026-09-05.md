# Commuting cubic conservation — verified, not RH

Goal ACTIVE; RH unproved. New leaf `formal/GaloisForLFunctions/RHTower/CommutingSourceCubicConservation.lean` (268 lines), wired into RHTower umbrella after NestedSourceCubicConservation. No umbrella/full builds.

Main theorem `RHTower.commutingSourceCubicAssociator_nuclear_conservation` at line64: orthogonal P,Q,R, only PQ=QP (no nesting), and C=(R-P)^3-(R-Q)^3-(Q-P)^3 Schatten1. Set U=Q-PQ,V=P-PQ,W=I-U-V,A=WRU,B=WRV,J=VRU. Then A,B,J HS; TrC=0; with a=||A||HS²,b=||B||HS²,j=||J||HS², real diagonal traces UCU,VCV,WCW equal -a-2j,b+2j,a-b. No individual displacement compactness assumption. Generalizes `mem:universal-law-field/nested-cubic-noncompact-conservation-2026-09-05`.

Proof: U,V,W joint orthogonal partition. Block identities UCU=-(A†A+2J†J),VCV=B†B+2JJ†,WCW=AA†-BB†. Nuclear UCU has summable nonnegative diagonal => A,J HS. Subtract nuclear JJ† from VCV => B HS. Nuclear pinching and HS cyclicity cancel all three channels. Positive survivor is finite matched transition energies, not merely a negative result.

Scope: kills ordinary integral charge from THIS cubic associator with commuting source projections even if nonnested/noncompact. Does NOT classify noncommuting P,Q, nontracial/modular pairings, or other cubic defects. No literal arithmetic projection/theta model instantiated, no source-to-Xi capacity identification, no RH bound. Operator-theoretic bridge; priority/new-field claim NOT made. Do not automatically nominate noncommuting projections as the new RH mechanism.

STATUS CANNOT-296 updated, F661 added; 4996 lines. Keep under5000. No broad positivity no-go inferred.

Verification: `/tmp/hgt_commuting_cubic_conservation.lean` exact installed proof modulo final #print/blanklines. Final `lake env lean /tmp/hgt_commuting_cubic_conservation.lean` session24880 EXIT0, axioms only propext/Classical.choice/Quot.sound. `scripts/formal_tools.py lint` session75460 EXIT0 existing size warnings. git diff --check passed; diff -B installed vs scratch (without #print) passed. API scratch session40911 EXIT0. All own process handles terminal, no own active Lean process; no heartbeats raised, no missing oleans needed.

Lean efficiency: rectangular HS product theorem takes hA then hB and proves B comp A, so Gram A†A uses hA then hA.adjoint. Give explicit operator to memRectSchattenClass_iff_memSchattenClass to avoid expensive metavariable inference (initial omitted operator hit 200000 heartbeats; explicit term fixes). Use typed local equalities `(opTrace (adjoint A*A)).re = hsNormSq A := re_opTrace_adjoint_comp_self hA` before rw, since generic RCLike.re does not rw against Complex.re directly. Use simp only [neg_one_smul,neg_neg] on nuclear negative Gram sums; broad simp reordered summands. Algebra compiled at default heartbeats after explicit corner factorizations. No empirical computations.

Literature audit: Kittaneh1986 On zero-trace commutators, primary Cambridge PDF read: bounded normal first factor does NOT by itself force trace-class commutator trace zero. Don't use illicit cyclicity of nonnuclear products. New theorem checked by positive block argument, not that false shortcut.

Next: this bounded architecture variant is closed. Return to a genuinely different source mechanism, guided by corpus locks; do not keep weakening nesting/compactness or present this bridge as a new field. Need exact new implication to RH, not novelty by search miss.
