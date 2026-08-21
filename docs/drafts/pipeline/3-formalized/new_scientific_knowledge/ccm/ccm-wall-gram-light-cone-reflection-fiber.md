# CCM wall-Gram light-cone reflection fiber

## Status

Formalized unconditionally in
`GaloisForLFunctions.RHTower.CCMActualHeadWallGramLightConeReflectionFiber`.
This retires direct scalar transport of wall-light orientation through the completed Γ-wall
producer. The positive survivor is an exact parity-sector classification pointing to an odd
holonomy/Schur carrier.

## New knowledge

Let `J_n(f)` be the actual-head wall-chord jet current. Lean proves

\[
J_n(\mathcal R f)=-J_n(f),
\]

where `R` is physical `L²` reflection. Global sign does not change this quadratic current, so both
reflection eigenspaces are in its kernel:

\[
\mathcal Rf=f\ \text{or}\ \mathcal Rf=-f
\quad\Longrightarrow\quad J_n(f)=0.
\]

The two positive Suzuki slacks are exchanged by reflection:

\[
E_n^+(\mathcal Rf)=E_n^-(f),
\qquad
E_n^-(\mathcal Rf)=E_n^+(f).
\]

On the literal complete restricted-Weil form domain, the completed actual Γ-wall outgoing
producer has the opposite grading:

\[
P_a(\mathcal Ru)=P_a(u),
\qquad
J_n(\mathcal Ru)=-J_n(u).
\]

Lean therefore proves a selector no-go: if a scalar function of `P_a(u)` equals `J_n(u)` for every
form-domain vector, then `J_n` is identically zero. Direct scalar completed-producer transport
cannot retain wall orientation.

## Higher principle and pivot

Earlier failures to choose a chord square-root sheet and later success of spectral differentiation
are two shadows of one `Z/2` grading. Scalar completed cosine producers live in the reflection-even
quotient. Differentiated wall orientation lives in the reflection-odd quadratic sector and measures
only even/odd interference; it vanishes on both diagonal parity blocks. Since restricted-Weil
energy itself splits into those diagonal blocks, the jet contraction alone cannot prove their
positivity.

Surviving route must not ask an even scalar producer to select an odd sheet. It must introduce an
odd covariant carrier—holonomy, commutator, or off-diagonal block—and feed its positive square or
Schur complement back into the even completed quadratic. Corpus search should now target exact
odd Gamma/Robin/Neumann holonomy channels with a closed mass-shell or PSD completion law.

## Lean audit

- scratch check: passed;
- direct leaf check: passed;
- exact leaf-module build: passed;
- umbrella import: wired, not built;
- capstone axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
