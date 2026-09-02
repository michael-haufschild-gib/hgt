# Integral curved Tate formation-properness index law

- **ID:** `ULF-ICTFPI-1`
- **Stage:** 2-fully-proven
- **Type:** unconditional completion-index fusion theorem
- **Status:** dependency-closed paper proof; Lean-certified

## Statement

Fix one multiplicity-labelled Xi point `q`. Retain one scalar source marker. Its finite landing at
stage `n` is the literal Meyer--Tate arithmetic differential of the dyadic Xi Green chain; its
physical landing is the completed Xi Green vertical boundary. Give both the fixed target exactness
flag whose boundary space is the literal finite arithmetic graph.

Define the integral formation-completion index by

`I(q)=ev_((2 Re(q)-1) log 2)(det C_T)`.

Then:

1. every finite landing is a boundary;
2. finite landings converge pointwise in Hilbert graph norm to the physical landing for every `q`;
3. the source-marked exactness states converge in provenance topology iff `I(q)=0`;
4. the completed Xi boundary is born beyond finite arithmetic formation iff `I(q) != 0`;
5. recovered compact prime history descends iff `I(q)=0`;
6. `I(q)=0` iff `Re(q)=1/2`.

Consequently universal source-marked provenance continuity, and equivalently universal vanishing
of `I`, is RH.

## Proof

The prime-cycle trace-one law identifies each finite Meyer--Tate differential with a finite graph
admission, so every finite state is escape-free. The cofinal averaging theorem gives pointwise norm
convergence to the completed vertical boundary. The source-marked exactness topology makes
escape-freedom closed: convergence of the finite exact states therefore forces physical
escape-freedom. Conversely, on the critical line the completed Green coefficient vanishes, hence
no physical source marker survives and the provenance convergence criterion is vacuous.

Physical escape-freedom is membership of the Xi vertical boundary in the finite arithmetic graph,
which the formation-completion boundary theorem identifies exactly with `Re(q)=1/2`.
`ULF-IRRCF-1` identifies Gamma evaluation of `det C_T` with paired positive curvature. Its radical
is zero precisely when `(2 Re(q)-1) log 2=0`, hence precisely on the critical line. Existing
formation-boundary and compact-recurrence equivalences give clauses 4 and 5. Quantification over
all Xi copies gives the global RH equivalences.

## Meaning

Ordinary vector convergence is information-neutral and occurs on and off line. Horizontal anomaly
lives in failure of the fixed source-survival tests to converge. Thus `det C_T` is the numerical
obstruction index seen by the source-marked exactness topology. Completion may create a homology
class even when every finite stage is exact; the index measures exactly that birth.

## Boundary

This theorem does not prove universal provenance continuity and therefore does not prove RH. Its
topology retains source markers and survival truth values, but not the actual boundary primitives.
At an exact physical state every survival test is absent, so the positive convergence direction is
vacuous. A genuine source law must instead construct compatible finite primitives, or an equivalent
zero-independent properness theorem. Assuming source-marked continuity alone is still RH-equivalent.

## Dependency audit

- Literal Meyer--Tate finite differential and cofinal averaging convergence.
- Arithmetic formation-completion/Roos/physical boundary fusion.
- Compact recurrence descent fusion.
- Source-marked exactness topology and closed escape-freedom.
- Integral curved Tate determinant and Gamma base change.
- No RH, critical-line, positivity, compactness, fitted lattice, or extra axiom premise.
