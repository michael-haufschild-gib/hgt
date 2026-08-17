# Coinduced degree-lowering, exact reporter, and global formation-recovery law

- **ID:** ULF-CPFM-2
- **Stage:** 2-fully-proven
- **Type:** THEOREM / GLOBAL FORMATION LAW / SELECTION-BRIDGE ARCHITECTURE
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [LEAN PENDING] [NOT RH]
- **Date:** 2026-08-17

## 1. The mismatch this theorem resolves

Central packet formation naturally produces a \(2\)-cocycle. Fixed-point rigidity acts on a
\(1\)-cocycle. The missing operation is not another route-specific detector: it is a faithful
degree-lowering mechanism together with an exact recovery kernel.

Let \(G,A\) be abelian groups and let \(c:G\times G\to A\) satisfy

\[
 c(x,g)+c(x+g,h)=c(g,h)+c(x,g+h).
 \tag{DL.1}
\]

Assume the left normalization \(c(0,g)=0\). Put

\[
 (R_gf)(x)=f(x+g),\qquad
 b_c(g)(x)=c(x,g).
 \tag{DL.2}
\]

Functions differing by a constant are regarded as the same coinduced history.

## 2. Canonical degree lowering

### Theorem 2.1 — exact transgression identity

For all \(g,h,x\in G\),

\[
 \boxed{
 b_c(g+h)=b_c(g)+R_gb_c(h)-\operatorname{const}(c(g,h)).}
 \tag{DL.3}
\]

Equivalently, modulo constants,

\[
 [b_c(g+h)]=[b_c(g)]+R_g[b_c(h)].
 \tag{DL.4}
\]

The original degree-two law is reconstructed from the degree-one formation defect at any basepoint:

\[
 \boxed{
 c(g,h)=b_c(g)(x)+b_c(h)(x+g)-b_c(g+h)(x).}
 \tag{DL.5}
\]

#### Proof

Rearrange (DL.1). No topology, norm, choice of route, or completion enters. QED.

Thus degree lowering is information-neutral before a reporter is chosen.

## 3. Cohomological faithfulness

Call \(b:G\to A^G\) a **coinduced coboundary modulo constants** when there are
\(F,k:G\to A\) with

\[
 b(g)(x)=F(x+g)-F(x)+k(g).
 \tag{DL.6}
\]

For \(\phi:G\to A\), write

\[
 (\delta\phi)(g,h)=\phi(h)-\phi(g+h)+\phi(g).
 \tag{DL.7}
\]

### Theorem 3.1 — degree-lowering faithfulness

For a left-normalized \(2\)-cocycle \(c\),

\[
 \boxed{
 b_c\text{ is a coinduced coboundary modulo constants}
 \iff c=\delta\phi\text{ for some }\phi:G\to A.}
 \tag{DL.8}
\]

#### Proof

Suppose (DL.6) holds. At \(x=0\), normalization gives

\[
 k(g)=F(0)-F(g).
\]

At \(x=g\) with second argument \(h\),

\[
 c(g,h)=F(g+h)-F(g)+F(0)-F(h).
\]

Taking \(\phi(x)=F(0)-F(x)\) gives \(c=\delta\phi\). Conversely, if
\(c=\delta\phi\), take \(F=-\phi\) and \(k=\phi\) in (DL.6). QED.

This is the exact \(H^2\to H^1\) dimension shift needed by packet formation. It is not yet a
Hilbert-space statement.

## 4. Exact reporter and global recovery kernel

Let \(H\) be an abelian group. An **exact coinduced reporter** consists of

\[
 D:A^G\to H,
 \qquad
 \rho_g:H\to H,
\]

where \(D\) is additive, every \(\rho_g\) is an additive automorphism, and:

1. \(\rho_0=1\) and \(\rho_{g+h}=\rho_g\rho_h\);
2. \(D(\operatorname{const}(a))=0\);
3. \(D(R_gf)=\rho_gD(f)\);
4. \(\ker D\) consists exactly of constant functions;
5. \(D\) is surjective.

Define the lowered packet

\[
 \beta_c(g)=D(b_c(g)).
 \tag{DL.9}
\]

### Theorem 4.1 — global formation and recovery

The lowered packet is a genuine \(1\)-cocycle:

\[
 \boxed{
 \beta_c(g+h)=\beta_c(g)+\rho_g\beta_c(h),\qquad \beta_c(0)=0.}
 \tag{DL.10}
\]

Moreover, if \(\beta_c\) is a \(1\)-coboundary,

\[
 \beta_c(g)=\rho_g\xi-\xi,
 \tag{DL.11}
\]

then \(c\) is a \(2\)-coboundary.

#### Proof

Apply \(D\) to (DL.3). Constant killing and equivariance give (DL.10).

For recovery, choose \(F\in A^G\) with \(D(F)=\xi\). Then

\[
 D\bigl(b_c(g)-(R_gF-F)\bigr)=0.
\]

Exactness of the kernel makes the parenthesized function constant, so (DL.6) holds. Theorem
3.1 gives \(c=\delta\phi\). QED.

This theorem supplies the global formation/recovery mechanism that the prior field programme was
missing. The load-bearing datum is now explicit: a source-derived exact reporter, not a fitted
scalar selector.

## 5. Selection architecture

Suppose in addition that \(H\) is Hilbert, \(\rho\) is unitary, and a source group has the fixed-point
property for affine isometric actions. Then every \(\beta_c\) is a coboundary. Theorem 4.1 forces
the central packet class \(c\) to split.

Therefore an RH architecture may legitimately have the following form:

1. off the selected locus, a source formation produces a non-split central packet class \(c\);
2. source normalization constructs one exact Hilbert reporter \(D\) before divisor specialization;
3. higher-rank fixed-point rigidity makes \(\beta_c\) a coboundary;
4. global recovery makes \(c\) split, contradicting step 1.

This card proves the algebraic engine connecting steps 2--4. It does not construct the arithmetic
source reporter in step 2 and therefore does not prove RH.

## 6. Sharp boundaries

1. **Kernel exactness is load-bearing.** If \(\ker D\) contains nonconstant histories, a lowered
   coboundary need not imply that \(c\) splits.
2. **Surjectivity can be weakened only to \(\xi\in\operatorname{ran}D\).** Without a lift of the fixed
   point, recovery cannot start.
3. **Equivariance is load-bearing.** A constant-killing linear reporter without
   \(D R_g=\rho_gD\) does not produce a \(1\)-cocycle.
4. **Raw quotient is not automatically Hilbert.** The algebraic quotient \(A^G/A\) may be
   non-Hausdorff or indiscrete under a chosen source topology, and transgression values may fail
   square-integrability. This is the precise global admission/properness frontier.
5. **Property-(T) is not used here.** It becomes relevant only after a unitary Hilbert realization
   of the exact reporter has independently been constructed.
6. **No scalar energy alone is faithful.** The reporter must recover every nonconstant coinduced
   history, not merely preserve one packet norm.

## 7. Parent boundary

The algebraic construction is the standard coinduced-module dimension-shift mechanism in group
cohomology. The field-level contribution is its exact coupling to central packet formation,
observer-kernel faithfulness, and the explicit global selection gate. Existing corpus topology
theorems showing indiscrete coinduced quotients are not contradictions; they diagnose failure of
condition 4 for those completions.

## 8. Lean target

Formalize the unconditional algebraic core:

1. (DL.3) and (DL.5);
2. normalized right-zero law and equivalence (DL.8);
3. exact-reporter structure and genuine action law;
4. lowered \(1\)-cocycle identity (DL.10);
5. recovery theorem \((DL.11) \Rightarrow c=\delta\phi\).

Do not axiomatize property-(T), Hilbert admission, or an arithmetic source realization.
