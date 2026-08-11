# Source-edge polar reconstruction, variation, and recurrence law

- **ID:** ULF-SFHM-3
- **Stage:** 3-formalized
- **Type:** LITERAL SOURCE REALIZATION OF COHERENT-HISTORY MECHANICS
- **Status:** `[PAPER-PROVED] [LEAN-FORMALIZED] [UNCONDITIONAL]`
  `[THREE-ORGAN FUSION] [JOINT RECONSTRUCTION] [EXACT CONSERVATION]`
  `[FOURTH-ORGAN PREDICTION] [NOT RH]`

## 1. Why this theorem exists

The abstract coherent-history field already proves that generated complex histories have two
executions: coherent summation and positive variation.  Its open gate was literal source
realization.  The prime-exponent Möbius formation supplies one.

Fix a prime `p`.  The normalized arithmetic source channels restrict to oriented exponent edges

\[
 e_j=\delta_{m+j}-\delta_{m+j+1}.
 \tag{PV.1}
\]

These edges are not a fitted route graph: they are the coefficient profiles of
`mPart_(m+j+1)(mu)-mPart_(m+j)(mu)` on the actual prime-power ray.

Let `z in C` be a complex character of the exponent lattice, so
`chi_z(delta_e)=z^e`.  The response of `(PV.1)` is

\[
 a_j(z)=z^{m+j}-z^{m+j+1}=z^{m+j}(1-z).
 \tag{PV.2}
\]

The same generated source history now has three structurally different readings:

1. arithmetic/incidence: the edge `e_j`;
2. coherent phase/history: the complex response `a_j(z)`;
3. positive admission/cost: the variation mass `|a_j(z)|`.

## 2. Joint reconstruction

### Theorem 2.1 — two adjacent responses reconstruct the character

For every `j`,

\[
 \boxed{a_{j+1}(z)=z a_j(z).}
 \tag{PV.3}
\]

Consequently, if one adjacent response is nonzero,

\[
 \boxed{z={a_{j+1}(z)\over a_j(z)}.}
 \tag{PV.4}
\]

Thus two generated responses jointly reconstruct both radial coordinate `|z|` and phase coordinate
`z/|z|`.  The exceptional zero response occurs exactly at a degenerate source/character event
(`z=1`, or at the zero character after positive depth); it must be recorded rather than divided
away.

### Proof

Multiply `(PV.2)` by `z`.  Division by the assumed nonzero response gives `(PV.4)`. QED.

This is stronger than positivity alone or phase alone.  Magnitudes reconstruct `|z|`; normalized
phase ratios reconstruct `z/|z|`; together they reconstruct `z`.

## 3. Coherent boundary conservation and positive history

For a block of `r>=1` generated edges define

\[
 S_r(z)=\sum_{j=0}^{r-1}a_j(z),
 \qquad
 V_r(z)=\sum_{j=0}^{r-1}|a_j(z)|.
 \tag{PV.5}
\]

### Theorem 3.1 — coherent/variation fusion

\[
 \boxed{S_r(z)=z^m-z^{m+r}=z^m(1-z^r),}
 \tag{PV.6}
\]

\[
 \boxed{V_r(z)=|z|^m|1-z|\sum_{j=0}^{r-1}|z|^j.}
 \tag{PV.7}
\]

In particular, on the phase locus `|z|=1`,

\[
 \boxed{V_r(z)=r|1-z|.}
 \tag{PV.8}
\]

The exact retained interference budget is

\[
 \boxed{D_r(z)=V_r(z)-|S_r(z)|\ge0,}
 \tag{PV.9}
\]

and satisfies the phase-dispersion conservation law

\[
 \boxed{
 V_r(z)^2=|S_r(z)|^2+
 {1\over2}\sum_{j,k}|a_j(z)||a_k(z)|
 \left|{a_j(z)\over|a_j(z)|}-{a_k(z)\over|a_k(z)|}\right|^2.}
 \tag{PV.10}
\]

The zero terms are omitted from `(PV.10)`.

### Proof

Equation `(PV.6)` telescopes because each interior exponent occurs with both signs.  Taking norms
in `(PV.2)` and summing gives `(PV.7)` and `(PV.8)`.  The triangle inequality gives `(PV.9)`.
Equation `(PV.10)` is the finite coherent-history phase-dispersion identity applied to the literal
source responses `(PV.2)`. QED.

This closes a source-realization gate: coherent cancellation and positive history are two
executions of the same arithmetic formation, not independently chosen route observables.

## 4. Polar refinement separates phase recurrence from radial criticality

Put `q=|z|`.  Phase quotient sends `z` to its radial coordinate `q`; the first nontrivial harmonic
refinement energy of the normalized magnitude history `(1,q,q^2)` is

\[
 \begin{aligned}
 H(z)
 &=2\big((q-1)^2+(q^2-q)^2\big)-(q^2-1)^2\\
 &=\boxed{(q-1)^4}.
 \end{aligned}
 \tag{PV.11}
\]

### Theorem 4.1 — polar criticality

\[
 \boxed{H(z)=0\iff |z|=1.}
 \tag{PV.12}
\]

Thus the two memories are independent and complementary:

- phase-dispersion memory records disagreement among unit phases;
- harmonic-refinement memory records radial nonunitarity after phase quotient.

Coherent-history interference alone cannot select the radial origin: if `z>0`, all responses in
`(PV.2)` have one common phase and the dispersion term vanishes even when `z!=1`.  Harmonic
refinement supplies the missing radial detector without killing unitary phase evolution.

### Proof

Expand `(PV.11)`.  A real fourth power vanishes exactly when `q-1=0`. QED.

## 5. Fourth-organ prediction: exact recurrence with open source history

Take the parity character `z=-1`.  Then

\[
 a_j(-1)=2(-1)^{m+j},
 \qquad
 V_r(-1)=2r.
 \tag{PV.13}
\]

For every `n>=0`,

\[
 \boxed{S_{2n}(-1)=0,\qquad V_{2n}(-1)=4n.}
 \tag{PV.14}
\]

### Theorem 5.1 — source-native recurrent shadow/open variation

The coherent observer closes exactly after every two source edges, while the positive generated
history grows linearly without bound.  Equivalently, the exact interference budget on an even
block is

\[
 \boxed{D_{2n}(-1)=4n.}
 \tag{PV.15}
\]

### Proof

Parity makes consecutive responses opposite.  Every pair cancels coherently, while each response
has modulus two. QED.

This theorem was forced by `(PV.6)`--`(PV.10)` in a fourth organ: recurrence/cofinal admission.
It does not add an arbitrary universal cover or complexity counter.  Open history is the positive
execution of the same source edges whose coherent execution recurs.

## 6. RH selection consequence — typed but still open

For a divisor parameter `rho`, the natural prime character has radial part

\[
 |z_p(\rho)|=p^{2\operatorname{Re}\rho-1}.
 \tag{PV.16}
\]

The polar refinement theorem therefore gives

\[
 \boxed{H(z_p(\rho))=0\iff \operatorname{Re}\rho={1\over2}.}
 \tag{PV.17}
\]

This is the promised selection receiver, reached only after source generation, three-organ fusion,
joint reconstruction, conservation, and the fourth-organ theorem.

It is not RH.  The missing statement is now exact:

> Prove that the physical Xi-zero deformation is a legal source-formed character section whose
> radial response descends through exponent-edge refinement with zero harmonic memory, while the
> resulting class survives the admitted completion.

If proved before Xi specialization, `(PV.17)` would force the critical line.  Assuming harmonic
descent merely at zeros would be circular.

## 7. Hostile boundaries

1. Generic character algebra, triangle inequalities, polar decomposition, and finite Dirichlet
   energy are classical.  Field content is their common source-formation interpretation.
2. The parity theorem is a finite/cofinal algebraic history law, not physical time by itself.
3. Positive variation is completion-sensitive; an infinite carrier needs an admitted topology.
4. Phase dispersion and radial harmonicity are not interchangeable.  Each has exact countermodels
   invisible to the other.
5. This realizes one literal arithmetic source sector.  It does not yet realize every frontier
   organ or provide the Xi harmonic-descent theorem.

## 8. Lean certification

`GaloisForLFunctions.HTGeometry.SourceFormationHarmonicMechanics` certifies:

- literal Möbius source channels as prime-exponent edges;
- coherent block telescoping;
- two-response character reconstruction;
- positive parity-history growth and exact even-block coherent closure;
- radial harmonic energy vanishing exactly on the unit circle.

No computation certificate, project axiom, RH hypothesis, `sorry`, `admit`, `opaque`, or `unsafe`
declaration is used.
- 2026-08-11 -- Lean surface audited complete against the card; promoted to stage 3.
- 2026-08-11 -- Lean surface audited complete against the card; promoted to stage 3.
