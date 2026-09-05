# Cubic flat-current normalization

**Status:** CFC-1 FALSE. The complete source-loop winding realization is
Lean-proved in `CubicCirculantWindingIntegral.exists_faithful_circulant_winding_cubic`
(declaration namespace `RHTower`), retaining exact source recovery, genuine
doubled/reversed Hardy compression, and ordinary cubic trace `(2πi)⁻¹∫f'/f`.
Literal arithmetic contour specialization remains Lean-open; independent
arithmetic zero-charge control remains mathematically unproved.

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

**[FORMALIZATION GAP]:** specialize the source-loop theorem to a smooth
traversal of the literal arithmetic rectangle and use the already-proved completed
prime–Gamma argument principle. No prescribed index may enter the source construction.
**[OPEN CORE]:** independent arithmetic control forcing the resulting strict-right
charge to vanish. Admission, recovery, and exact normalization hold for every
eligible smooth source; those properties alone cannot supply this selection.

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
polynomial derivative. Operator admission and trace transport for this matrix
source and the integrated winding identity are Lean-proved.

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

## Source charge theorem proved in Lean

Let f:ℝ→ℂ be smooth, nowhere zero, and equal to the same nonzero constant
outside a compact interval. There is a fixed source-value-faithful family of
three 12-channel orthogonal multiplier projections whose Hardy-rounded
projections have trace-class combined cubic and ordinary cubic trace

`(2πi)⁻¹ ∫ f'(s)/f(s) ds`.

**Proof.** Use the real constants above, phase q=f/|f|, and the column
projections of V=circ(t,bq,0). Tensor with E(|f|), take two identical copies,
and reverse the last two projection labels. All matrix entries are smooth
and constant outside the interval. Their deviations from those constants
are Schwartz. Entrywise scalar Hardy nuclearity therefore proves every
cutoff/source commutator is trace class; finite coordinate inclusions and
projections preserve that ideal. Pointwise projection identities give
orthogonal multiplier projections, and the circulant and graph identities
give aggregate/current commutation.

Apply `exists_rounded_cubic_with_boundary_trace` on the finite orthogonal
sum of twelve copies of L²(ℝ). Expanding the finite block trace and applying
the scalar CCM cocycle to each entry gives
`Tr C=i/(4π) ∫Tr(S K')`. Constants cause no boundary term because the
derivative integrates to zero. Graph insertion preserves this pairing,
doubling multiplies it by two, and label reversal negates it. The exact
polynomial primitive has equal endpoint values. Unit normalization leaves
`(2πi)⁻¹∫q'/q`. Finally `q'/q=f'/f-(log|f|)'`; the real logarithm has
equal endpoint values. This proves the formula. Source-value recovery is
the displayed entrywise identity before Hardy compression; no claim of
bounded inverse recovery after compression is made.

This construction uses f pointwise, not its zero count. Applied to a smooth
orientation-preserving traversal of a zero-free arithmetic contour, the
argument principle retains analytic multiplicity. The corpus already
identifies the completed prime–Gamma contour integral with that multiplicity
in `FormationAnchoredCubicContourCharge`. This is a source-to-charge
realization, not a proof that its charge vanishes on strict-right contours.

**Lean-closed analytic bridge:**
`cubicFiniteMatrix_admissible_boundary_trace` proves the ordinary matrix
cocycle with coefficient `i/(2π)` for constant-plus-Schwartz symbols, including
all off-diagonal coefficients and the vanishing constant boundary terms.
`exists_rounded_finiteSource_cubic_with_local_charge` constructs genuine
rounded projections and proves `Tr C=i/(4π)∫Tr(S K')`.
`exists_rounded_faithful_circulant_source` applies it to the explicit
six-channel amplitude-retaining source of any smooth nowhere-zero f constant
outside a compact set; its conclusion also recovers f pointwise from that
same source aggregate. Smoothness, compact deviation, orthogonality, flatness,
and nuclear admission are proved, not added as source-law fields.

**Exact integrated bridge:** `integral_cyclicFaithfulSourceSymbol_current`
identifies the actual admitted matrix current, including its actual derivative,
with `∫f'/f`. `exists_faithful_circulant_winding_cubic` chooses t,b before f,
recovers f from the same source aggregate, and constructs genuine doubled/reversed
projections whose combined cubic has ordinary trace `(2πi)⁻¹∫f'/f`. Its nuclear
corrections are relative to the explicitly doubled source compressions with
labels `0,2,1`. Neither the trace nor the winding is a premise.

**Remaining Lean obligation:** literal arithmetic contour specialization.
The winding leaf passed scratch/published checks, is wired without an umbrella
build, and its five principal axiom audits contain only `propext`,
`Classical.choice`, `Quot.sound`. These are standard analytic bridges, not new
arithmetic conservation or budget theorems. Do not report the requested Xi
operator-index identification as Lean-proved until contour specialization closes.
