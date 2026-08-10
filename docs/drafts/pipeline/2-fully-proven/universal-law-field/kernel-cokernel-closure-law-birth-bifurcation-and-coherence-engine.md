# Kernel--cokernel--closure law-birth bifurcation and coherence engine

- **ID:** ULF-KCL-1
- **Stage:** 2-fully-proven
- **Type:** ROUTE-INDEPENDENT MECHANISM THEOREM
- **Statement:** Cokernel controls existence of a higher-law carrier, kernel controls its next
  coherence, and closure gap controls exact-versus-Hausdorff-visible birth.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT]
  [DUAL COUNTERMODELS] [LEAN-CERTIFIED] [UMBRELLA-BUILT] [AXIOM-AUDITED] [NOT RH]

## 1. Setup

Let \(M\) be an additive semigroup, let \(E,F\) be normed vector spaces over a nontrivially
normed field, and let \(T:E\to F\) be linear. For a binary compensator
\(\kappa:M^2\to F\), define

\[
a_\kappa(x,y,z)
=\kappa(x,y)+\kappa(x+y,z)-\kappa(y,z)-\kappa(x,y+z).
\tag{KCL.1}
\]

Define algebraic and separated carrier classes

\[
\xi_T=[a_\kappa]_{F/\operatorname{im}T},
\qquad
\bar\xi_T=[a_\kappa]_{F/\overline{\operatorname{im}T}}.
\tag{KCL.2}
\]

For a ternary carrier \(h:M^3\to E\), define

\[
P_h(w,x,y,z)
=h(w,x,y)+h(w,x+y,z)+h(x,y,z)-h(w+x,y,z)-h(w,x,y+z).
\tag{KCL.3}
\]

## 2. Carrier-bifurcation theorem

### Theorem 2.1

For every triple \((x,y,z)\):

1. \(\xi_T=0\) iff some \(e\in E\) satisfies \(Te=a_\kappa(x,y,z)\);
2. \(\bar\xi_T=0\) iff
   \(a_\kappa(x,y,z)\in\overline{\operatorname{im}T}\);
3. exactly one phase holds:

   \[
   \begin{array}{ll}
   \text{exact birth:}&a_\kappa\in\operatorname{im}T,\\
   \text{mirage birth:}&
     a_\kappa\in\overline{\operatorname{im}T}\setminus\operatorname{im}T,\\
   \text{separated residual:}&
     a_\kappa\notin\overline{\operatorname{im}T};
   \end{array}
   \tag{KCL.4}
   \]

4. Hausdorff separation sends \(\xi_T\) to \(\bar\xi_T\);
5. closed range forbids mirage birth;
6. dense range kills every separated carrier class.

### Proof

Quotient zero criteria give

\[
[a]_{F/\operatorname{im}T}=0\iff a\in\operatorname{im}T,
\qquad
[a]_{F/\overline{\operatorname{im}T}}=0
  \iff a\in\overline{\operatorname{im}T}.
\]

Range membership is existence of a preimage. Split first on range membership and then on closure
membership for the exclusive trichotomy. Inclusion
\(\operatorname{im}T\subseteq\overline{\operatorname{im}T}\) induces item 4. Closedness makes
range equal closure; density makes closure equal \(F\). \(\square\)

## 3. Coherence-transfer theorem

### Theorem 3.1

Both carrier classes satisfy pentagon:

\[
\xi(w,x,y)+\xi(w,x+y,z)+\xi(x,y,z)
=\xi(w+x,y,z)+\xi(w,x,y+z).
\tag{KCL.5}
\]

If a global carrier satisfies \(Th(x,y,z)=a_\kappa(x,y,z)\), then

\[
\boxed{P_h(w,x,y,z)\in\ker T.}
\tag{KCL.6}
\]

If \(T\) is injective, every exact carrier is therefore a coherent ternary law.

### Proof

Expanding and cancelling gives the universal associator pentagon

\[
a_\kappa(w,x,y)+a_\kappa(w,x+y,z)+a_\kappa(x,y,z)
=a_\kappa(w+x,y,z)+a_\kappa(w,x,y+z).
\tag{KCL.7}
\]

Apply either quotient map for KCL.5. Additivity and \(Th=a_\kappa\) give
\(T(P_h)=P_{Th}=P_{a_\kappa}=0\), proving KCL.6. Injectivity makes the kernel zero.
\(\square\)

## 4. Mechanism dictionary

| feature of \(T\) | law-theoretic effect |
|---|---|
| surjective | every pointwise associator has a carrier |
| injective | carrier coherence is reflected |
| closed range | exact and approximable birth coincide |
| dense range | Hausdorff observation erases every carrier obstruction |
| isomorphism | existence and coherence strictify simultaneously |

A cokernel defect does not automatically demand another arity: it already satisfies pentagon and
demands carrier/admission promotion. A kernel defect is mechanism that can force next arity.

## 5. Dense-mirage countermodel

Let \(H=\ell^2(\mathbb N;\mathbb C)\) and let \(T=\Gamma_1:H\to H\) be
**gammaRadialReporter 1**. Corpus proves unconditionally that \(T\) is compact, injective, dense,
and not surjective. Choose \(a\notin\operatorname{im}T\) and set

\[
\kappa_a(x,y)=(x^2y)a.
\]

Then \(a_{\kappa_a}(x,y,z)=2xyz\,a\). Since range is complex linear,
\(2a\notin\operatorname{im}T\), while density puts \(2a\) in its closure. Hence

\[
\boxed{\xi_T(\kappa_a;1,1,1)\ne0,\qquad
\bar\xi_T(\kappa_a;1,1,1)=0.}
\tag{KCL.8}
\]

Exact higher-law birth fails while every Hausdorff carrier observer reports closure.

## 6. Kernel-ambiguity countermodel

Let \(T:\mathbb Z\to\mathbb Z/2\mathbb Z\) be reduction modulo two. Take zero binary
compensator and

\[
h(x,y,z)=2x^2yz.
\]

Then \(Th=0=a_\kappa\), but direct expansion gives

\[
P_h(w,x,y,z)=-4wxyz.
\]

Thus \(P_h(1,1,1,1)=-4\ne0\) while \(T(P_h)=0\). Carrier existence does not imply carrier
coherence when \(T\) is noninjective.

## 7. Hostile audit

1. **Generic homological algebra?** Yes at ingredient level. Claim is coupled mechanics and
   interpretation, not priority for kernels or quotients.
2. **Pentagon means physical curvature?** No connection, transport, or spacetime is constructed.
3. **Dense range selects an approximate carrier?** No canonical sequence, rate, cost, or admitted
   primitive follows.
4. **Pointwise exactness gives a continuous global carrier?** No. Choice gives only a set-theoretic
   carrier.
5. **Noninjectivity always creates next arity?** No. It only permits a kernel-valued next defect.
6. **Topology source-derived?** Not here. The theorem classifies a supplied topology.
7. **Every corpus route unified?** Not yet. Naturality, composition, and source realization remain
   gates.

## 8. Strong positive survivor

Dual cells prove independence:

- injective + dense + non-surjective can fail existence while hiding failure after separation;
- surjective + noninjective can pass existence while failing coherence.

No scalar obstruction size, single curvature class, or one-sided exactness test replaces this
kernel--cokernel--closure engine.

## 9. Lean certification

Module **GaloisForLFunctions.HTGeometry.ConstitutiveCarrierBifurcation** certifies range and
closure criteria, trichotomy, both pentagon laws, kernel landing, injective coherence reflection,
closed-range exclusion, both unconditional countermodels, and one closed capstone.

Direct foreground elaboration, formal lint, source-level axiom audit, and final 11,537-job
Universal Law Field umbrella build pass. Headline declarations depend only on Mathlib-standard
propext, Classical.choice, and Quot.sound.

## 10. Scope

No RH endpoint, route repair, physical curvature, source-selected topology, nonlinear carrier,
global continuity, or field-constitution claim is made. Next target is composition law for
successive carrier refinements.

## Log

- 2026-08-10 — paper proof closed; dual countermodels checked in Lean scratch.
- 2026-08-10 — theorem formalized, axiom-audited, linted, wired into umbrella, and final-built.
