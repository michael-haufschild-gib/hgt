# Real-positive Meyer degrees are controlled by their Hermitian part

- **ID:** qii-hermitian-part-degree
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** ../1-in-progress/q-ii-source-effectivity-and-linear-degree.md
- **Statement:** For every complex-linear degree on genuine Meyer cohomology, the real sharp-square reading equals the reading of its canonical Hermitian part. If nonnegative, that part restricts on every finite jet packet to nonnegative critical value weights.

## Why the qualification matters

The finite-jet classification currently assumes a Hermitian degree. Positivity
of only the real part of each square does not imply that the original degree
itself is Hermitian. Its anti-Hermitian part is invisible to those real square
readings. A claim that every real-positive degree itself kills higher jets
would therefore exceed the proved statement.

## Paper proof [PROVED HERE]

For a complex-linear degree d on the actual involutive convolution quotient,
define d*(u)=conjugate(d(u^sharp)). Two conjugations make d* complex-linear;
the involution law gives d**=d. Put h=(d+d*)/2 and k=(d-d*)/(2i). Both h
and k are Hermitian and d=h+ik. The decomposition is unique.

Every arithmetic sharp square q=u*u^sharp satisfies q^sharp=q, by the actual
commutative product and involution laws. Hence h(q)=Re(d(q)), as a complex
number with zero imaginary part, while k(q)=Im(d(q)). Thus real square
positivity of d is precisely square positivity of h; k contributes no real
intersection reading.

Apply the dependency-closed finite-jet classification to h. All off-line
blocks and all positive-order critical jets vanish under h. Critical local
identities receive nonnegative real weights. On every finite causal packet,
h is exactly the corresponding sum of zeroth critical values. Finite
nonnegative critical point weights give actual whole-quotient examples;
adding i times any Hermitian degree leaves their real square positivity
unchanged.

## Scope and next question

This is an exact finite-packet restriction and a whole-quotient decomposition
of the degree. It does not classify discontinuous functionals on arbitrary
infinite packets. No passage from finite packet formulas to an infinite sum
is authorized without a continuity or algebraic recovery proof.

Corpus search found matrix Hermitian-part and linear-involution splitting
lemmas, but no existing genuine Meyer degree version. The algebraic
decomposition is a standard mechanism; the source application and its exact
scope are the point. External novelty unverified. Complete unrun Lean draft:
`/tmp/QIIMeyerHermitianDegreePartDraft.lean`, including uniqueness, exact square
projection, and the finite causal restriction without a Hermiticity premise
on the original degree.

Actual candidate: `formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/MeyerHermitianDegreePart.lean`; unverified and unwired. The scratch copy remains until actual-file verification succeeds.
