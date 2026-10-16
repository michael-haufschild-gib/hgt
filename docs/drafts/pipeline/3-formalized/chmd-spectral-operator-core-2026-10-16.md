# CHMD: a spectral core for the actual maximal generator

Status: FORMALIZED INFRASTRUCTURE. This does not qualify as CHMD frontier progress.
Overall RH goal remains active and unproved.

The preceding work gave an exact finite-sample signed-generator
range and unique reduced inverse. The present question was how that algebraic
construction reaches the full maximal operator, without assuming an infinite
cardinal expansion or closed range.

## Corpus and preliminary attack

The CHMD deep query `finite sample source generator core reduced resolvent
critical eigenspace completeness` completed with no partial stages or errors,
72,892 inventoried files and none pending. It returned the previous algebraic
inverse and the physical compact C2 operator core, but no spectral operator core.
A whole-corpus query returned useful generic form-range/density lemmas but was
partial because its final local-model JSON was malformed. Compiler metadata is
mostly pending/stale; these searches do not certify absence.

Do not infer that finite-sample sources themselves form an operator core from
the dense image of their signed generator. That implication needs an additional
argument. The bounded resolvent provides a different construction with an exact
proof. Bare cyclicity is an intermediate bridge, not the final RH claim.

## Exact statement

Write H for the actual mass space, R=(1+L)^(-1), C=ker(R-1/2),
K=massSamplingSpan, and V for all finite-Xi-sample mass vectors. Define

`T = V + R(V)`.

Conjecture: T is a core for the actual maximal generator L. More precisely,
every u in D(L) is the graph-norm limit of actual domain vectors u_n in T.
The construction retains the complete critical component, every prime jump,
and both polar samples. No RH, finite number of off-line zeros, zero simplicity,
spectral gap, bounded signed inverse, or infinite cardinal expansion is assumed.

## Dependency-closed paper proof

1. V is a real subspace and lies in D(L), by finite-sample admission. R(H) is
   D(L), so T is contained in D(L).
2. C is contained in V: critical vectors have all Xi and polar samples zero.
   On C, R=1/2 and L=1.
3. The previous exact range theorem says each b in K has a finite-sample
   preimage v with R(2v+b)=v. Hence Rb=v-2Rv belongs to T.
4. For u in D(L), put z=u+Lu, so Rz=u. Split z=c+r using the actual orthogonal
   critical projection. Since closure(K)=C-perp, choose b_n in K with b_n -> r.
   Set z_n=c+b_n and u_n=Rz_n. Then u_n=(1/2)c+Rb_n belongs to T.
5. Continuity of R gives u_n -> Rz=u. The exact maximal-generator identity
   L(Rz_n)=z_n-Rz_n gives Lu_n -> z-u=Lu. Thus T is an actual operator core.
6. Graph lifts of u_n converge in the full energy graph: for differences,
   the graph norm squared is the mass pairing with u_n+Lu_n. This also yields
   approximation of arbitrary completed graph vectors by T, using the dense
   Riesz range. The critical and reduced parts can be retained separately.
7. Every signed-radical graph source is a critical mass vector, by its zero
   mixed pairing and the established resolvent-preimage identity. Thus the
   whole radical lies in the spectral graph core. Removing the critical graph
   projection preserves that core. Given any convergent core sequence q_n for
   p, replace it by P(p)+(1-P)q_n. The new sequence stays in the core, converges
   to p, and differs from p only in the orthogonal complement of the radical.
   For reduced p, every approximant is reduced as well.

The proof closes spectral completion after one resolvent application. It does
not establish density of V alone, and does not exclude bound states. A stronger
unregularized synthesis claim must be attacked independently rather than silently
substituted for this theorem.

## Work and validation

The three leaves `CHMDSpectralOperatorCore`, `CHMDSpectralGraphCompletion`, and
`CHMDReducedSpectralCore` contain 28 declarations. Targeted builds and final
plain `lake env lean` checks passed for all three. All 28 declarations passed
the axiom audit with only `propext`, `Classical.choice`, and `Quot.sound`.
Toolchain probes passed; the three leaves are wired into RHTower.

The first global lint run failed on another writer's unwired
`CHMDBoundStateDimension` and a stale generated API index. A second index
refresh passed. Global lint was not rerun after the user explicitly redirected
work away from generic spectral infrastructure. No global green gate is claimed.

## Scope correction

The user correctly rejected this work as movement toward an RH proof. Operator
cores and general spectral theory do not supply the missing arithmetic sign.
Do not pursue further generic spectral completions, counting bounds, or RH
equivalences as substitutes for that sign.

The arithmetic pivot checked the actual prime-chain factorization, theta
harmonic identity, reflected-prime singularity, and upward-rate obstruction.
The complete source still subtracts `phiDoobCoshMass (fun x => v x ^ 2)`.
Positive chain variances alone do not pay this subtraction. A positive scalar
gauge cannot remove the reflected negative component; spatial rate order also
fails at the first prime threshold. These are existing results, not new findings.

The attempted nonlocal factorization has no dependency-closed paper proof.
No new arithmetic theorem, exclusion of off-line zeros, or qualifying frontier
advance was obtained in this turn. Further Lean code requires a proved argument
that removes an identified arithmetic obstruction.
