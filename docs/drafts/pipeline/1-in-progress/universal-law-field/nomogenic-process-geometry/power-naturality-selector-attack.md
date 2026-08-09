# Power-naturality selector attack

- **ID:** ULF-NPG-PNSA-1
- **Stage:** 1-in-progress
- **Type:** conjecture -> failure -> positive survivor
- **Status:** [SELECTOR CONJECTURE FAILED] [CLASSIFICATION SURVIVED]
  [ABSOLUTE DEPTH MARK FORCED] [NOT RH]

## Conjecture attacked

The source-native power interventions

\[
P_r(n)=n^r
\]

act on a radial deformation parameter by \(a\mapsto ra\). Since zero is the only common fixed
point, conjecture that power naturality alone selects the radial origin and hence supplies the
missing source-normal inverse--dagger relation.

## Failure

Power naturality compares different ramification depths. It does not identify their raw coordinate
frames. A comparison from raw depth to a depth-normalized observer may rescale its component at
depth \(m\) by \(1/m\). This family is natural:

\[
\frac1{rm}(r x)=\frac1m x.
\]

Consequently the raw radial defect \(d_m(a)=ma\) descends to

\[
\frac1m d_m(a)=a
\]

for every \(a\), not only \(a=0\). The hoped-for selector is false.

## Positive survivor

The failure is rigid. The companion theorem proves:

1. every monoid-homomorphic intervention natural in the free commutative source is a unique
   uniform power operation;
2. every linear ramification comparison from raw weight-one transport to trivial normalized
   transport is a unique scalar multiple of \(1/m\);
3. a depth-independent comparison is forced to vanish;
4. the canonical inverse-depth comparison retains every radial parameter exactly.

Thus power naturality does not merely fail to select zero. It classifies the entire normalization
loophole. A successful source-normal dagger mechanism must supply an absolute depth/frame, forbid
inverse-depth normalization, or introduce an operation outside the natural free-commutative-monoid
intervention algebra.

## Successor attack and second failure

The corpus does carry a literal additive depth successor (m\mapsto m+1), so the next conjecture
was that joint naturality under multiplication (m\mapsto rm) and succession (m\mapsto m+1)
would destroy inverse-depth normalization.

It does not. The raw depth clock is (mx), so successor transport is

\[
mx\longmapsto (m+1)x,
\qquad
T_{m,m+1}=\frac{m+1}{m}.
\]

The same inverse-depth comparison trivializes it:

\[
\frac1{m+1}T_{m,m+1}x=\frac1m x.
\]

The actual Xi depth-successor asymptotic in the corpus has precisely this normalization shape:
its defect is (O(1/m)), while multiplication by (m) recovers the logarithmic connection.
Therefore adding more homogeneous depth operations is not the answer.

## Higher pivot

Treat depth transport as a rank-one local system over the source-operation category. Any transport
of endpoint-ratio form

\[
T_{m,n}=w_n/w_m
\]

is pure gauge, with canonical trivialization (w_m^{-1}). Multiplication and succession are only
two restrictions of the same exact transport (T_{m,n}=n/m).

The next field-level classifier is therefore not another source operation. It is the obstruction
to global trivialization: loop/interchange holonomy, noninvertible transport, singular admission,
or a genuinely nonhomogeneous event. The corpus already contains the abstract clock-holonomy
parent theorem; the open task is to construct one literal pre-zero source loop whose holonomy is
both nontrivial and the common producer of several route organs.

## Log

- 2026-08-09 — fixed-point selector conjectured from \(a\mapsto ra\).
- 2026-08-09 — inverse-depth natural transformation killed the selector; exact classification
  extracted as positive survivor.
- 2026-08-09 — additive depth successor also proved homogeneous and inverse-depth gauge-trivial;
  pivoted from operation enumeration to transport-holonomy classification.
