# Nodal adaptive arithmetic source landing (2026-08-12)

Formal module: `RHTower.XiShiftedNodalAdaptiveArithmeticSourceLanding`.
Report: mass-shifted spectral-trace route equations 9.3.664–9.3.673.
Pipeline card: `docs/drafts/pipeline/3-formalized/mass-shifted-nodal-adaptive-source-landing.md`.

For real polynomial p and shifted moment functional L_y, set A=L(p²), B=L(pXp),
C=L((Xp)²), Q=A·Xp-B·p. Lean proves L(pQ)=0, L(Q²)=A(AC-B²), and
L(pXQ)=AC-B². At y=w², the crossing is a literal rational–Gamma-minus-von-Mangoldt
completed arithmetic landing with one common adaptive kernel, and equals
Re(M_p(0)M_p(2)-M_p(1)²).

Actual moving admission is retained: with source rates S_A=-A', S_B=-B', S_C=-C',
the literal bilinear source is A S_C-B S_B and
D'=-(ArithmeticSource + (S_A C-S_B B)).

New corpus nodal and rational-node descent yield RH iff all real nodal landings are nonnegative,
and equivalently iff a countable rational-node landing family is nonnegative. This does not prove
the signs. Universal principle: unbounded Hankel rank is transferred into adaptive nodal source
complexity while receiver remains degree-one/2×2.

Audits: direct Lean pass; targeted module build pass (12122 jobs); ten capstones axioms only
propext/Classical.choice/Quot.sound; placeholder and diff checks pass. Repo-wide formal lint is
currently blocked only by unrelated concurrently added unreachable Bourgain/Sieve/HTGeometry
modules; new module is umbrella-wired and not reported.