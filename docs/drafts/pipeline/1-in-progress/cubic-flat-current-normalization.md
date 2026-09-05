# Cubic flat-current normalization

**Status:** CFC-1 FALSE; exact positive circulant first-jet bridge on paper.
Arithmetic operator identification remains open.

**RH chain:** literal completed prime–Gamma source → noncommuting flat source
triple → Hardy cubic boundary charge → multiplicity-normalized Xi index.
The experiment tests normalization constraints on the second arrow, not RH.

**Checked locks:** `CubicAggregateSpectralCurrent`, `CubicBoundaryChargeTransport`,
`CubicBoundaryNonzeroCharge`, `FormationAnchoredCubicContourCharge`,
`CompletedSEMContourBoundary`; full-corpus research queries for flat triples,
spectral polynomial relations, boundary winding, and source normalization.
Scalar arithmetic winding already lands with exact multiplicity and `2πi`.
The existing nonzero operator example is not that arithmetic source.

## Frozen discriminator CFC-1

For arbitrary finite-dimensional orthogonal projections P,Q,R, put
S=P+Q+R and K=[P,Q]+[Q,R]+[R,P]. Conjecture:

`[S,K]=0 ⇒ K (3K² + S²(3I−S)²)=0`.

The conjecture asks whether the active current, not the ambient dimension,
forces a fixed spectral curve. It matches the charged two-channel model;
the leading K is essential because P=Q gives K=0 and arbitrary aggregate
spectrum. No proof strategy is known. Failure in any dimension refutes it.
It is a normalization discriminator, not a claimed universal RH producer.

Closest parents: standard Toeplitz commutator/area formulas and cubic relative
index theory. Corpus and arXiv/journal searches through 2026-09-05 did not
locate this exact statement; this is not a priority certification.

**Experiment:** constrained projection triples, independent seeded starts,
dimensions 2,3,4,6. Require small projection and flatness residuals; report
the candidate polynomial residual separately. Floating-point acceptance is
not proof. If a violation survives, reconstruct an exact witness before Lean.
If no violation appears, no inference of truth or arithmetic admission follows.

**[OPEN CORE]:** prove or refute CFC-1, then identify what its verdict permits
for the literal coefficient-faithful source, without encoding an index by hand.

## Exact verdict and positive survivor

CFC-1 fails for the three rank-one projections onto
`(1,0,1)/√2`, `(1,1,0)/√2`, `(0,1,1)/√2`.
Their entries are rational. With `J` the all-ones matrix,
`S=(I+J)/2` and `K=circ(0,1/4,-1/4)`.
They commute, and the proposed left side is exactly `K≠0`.

**[BRIDGE, paper complete]:** write
`circ(a,b,c)=[[a,b,c],[c,a,b],[b,c,a]]`. For a real constant t and a
complex u with `t²+|u|²=1`, let `V=circ(t,u,0)` and let Pj be the
outer product of column j of V with its conjugate. Each column has norm
one, so Pj is an orthogonal projection. Put `x=tu`, `y=conj(x)`.
Direct multiplication, with no spectral assumption, gives

`ΣPj=G=circ(1,x,y)`,
`K=[P0,P1]+[P1,P2]+[P2,P0]=circ(0,x-y²,x²-y)`.

All circulants commute, hence `[G,K]=0`. Differentiation and matrix trace give

`Tr(G dK)=d[2(x³-y³)]+3(y dx-x dy)`,
`d Tr(G dK)=-6 dx∧dy`.

For `y=conj(x)` the latter is `12i d(Re x)∧d(Im x)`.
Thus higher-dimensional flat sources have continuous area charge; the
two-channel curve is not a universal normalization law.

For `x=r u`, `y=r/u`, `|u|=1`, two identical copies and `6r²=1` give

`2 Tr(G dK)=d[4(x³-y³)]+2 du/u`.

Reversing the last two projection labels reverses K. The real-line Hardy
convention is `Tr C=i/(4π)∮Tr(G dK)`, so this reversed doubled source
has cubic boundary charge exactly `wind(u)`, after integrating the exact
polynomial derivative. This conclusion requires a proved operator admission
and trace transport for this new matrix source; the first-jet identity itself
does not supply those analytic steps.

The constants exist without a source-dependent clock:
`r=1/√6`, `t=√((1+1/√3)/2)`, `b=√((1-1/√3)/2)`, `u=b·phase(f)`.
Then `t²+b²=1`, `tb=r`. Nothing refers to a zero count.

**Coefficient retention, paper bridge:** phase alone is not injective.
For `a=|f|`, tensor each projection with the real rank-one graph projection
`E(a)=(1+a²)⁻¹[[1,a],[a,a²]]`. Its aggregate is `E(a)⊗G`.
The diagonal, amplitude off-diagonal, and phase off-diagonal entries are
`D=1/(1+a²)`, `A=a/(1+a²)`, `B=r·phase(f)/(1+a²)`.
They recover the literal source as `f=A B/(r D²)`.
This is value-faithful nonlinear encoding, not an assertion of linearity.
Moreover `Tr(E²)=1` and `Tr(E dE)=0`; tensoring preserves `Tr(G dK)`.
For a nonzero closed source loop, `du/u=df/f-d log|f|`; the real-log term
has zero integral. Hence the target charge is its ordinary source winding,
not an off-line-zero selector.

**Remaining formal obligations:** source-jet matrix bridge; graph retention;
actual matrix Hardy admission and trace theorem; closed-loop and arithmetic
contour landing. Do not report the requested arithmetic producer as proved
until all these steps are closed. No conservation or RH conclusion follows
from unit normalization alone.
