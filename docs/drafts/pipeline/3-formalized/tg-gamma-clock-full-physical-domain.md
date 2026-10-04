# TG C9.18c: both physical Gamma sectors and Fourier-invariant maximal domain

- **Stage:** 3-formalized
- **Route:** TG, full physical singular Gamma operator
- **Lean:** SoninGammaClockPhysicalDomain.lean; final audit and all fifteen foundation queries pass

## Corpus basis

C9.18b identifies the literal strong finite Gamma integral on the even
carrier and its exact maximal-domain convergence criterion. The existing
soninParityMultiplier has modulus one and commutes with every positive
physical dilation. SoninEvenCarrier identifies evenSubspace with the
fixed space of physical reflection and supplies its orthogonal projection.
Mathlib's orthogonalDecomposition uses the actual Hilbert L2 product.
Searches: tg-c918c-parity-search and tg-c918c-sum-search in /tmp. The latter
is nonpartial but contains mostly source-only candidates; all APIs must
be checked in this toolchain. No full Gamma-domain theorem was found.

## Dependency-closed paper construction

Let J be the existing n=1 parity multiplier, R physical reflection, P
the even orthogonal projection. Their actual almost-everywhere formulas
prove J^2=I and RJ=-JR; the exceptional spatial origin is Lebesgue null.
The complement of the even space consists exactly of Rf=-f. Thus J
restricts to a unitary from the odd space to the even space, with inverse
again J. Compose the orthogonal even/odd decomposition with this unitary
on its second component. This gives a full physical unitary
 Wf=(Pf,J(I-P)f), W^-1(x,y)=x+Jy.
Both sectors are retained, and W intertwines every positive dilation
with the two copies of the existing even dilation.

Let T be C9.18b's maximal even Gamma operator. Define the two-sector
operator T+T on D(T) x D(T), acting componentwise in the Hilbert L2 product.
It is densely defined since each component domain is dense. Inner products
split by components. Formal self-adjointness follows componentwise;
conversely testing the adjoint against (x,0) and (0,y) forces both coordinates
into D(T), and identifies both adjoint actions. Hence this operator is
self-adjoint on precisely that product domain. Pull back by W to obtain G.

Apply the same two-component construction to each actual finite even
Gamma operator. Its physical action is the original finite strong integral:
W and its inverse pass through the integrable orbit, and dilation
intertwining preserves both terms and the full -2I counterterm. Convergence
in the Hilbert product is equivalent to coordinatewise norm convergence.
C9.18b's exact iff on each coordinate therefore proves that every nontrivial
countably generated cofinal family converges on f exactly when f is in
D(G), with limit Gf. This is necessity as well as sufficiency.

The literal finite symmetric dilation integral commutes with the physical
Fourier unitary, since Fourier exchanges the two inverse dilation terms.
For f in D(G), apply Fourier to its convergent original cutoff family.
Finite commutation and the exact full-domain iff imply Fourier f belongs
to D(G) and G(Fourier f)=Fourier(Gf). The same argument with the inverse
Fourier unitary gives equality of domains, not only forward inclusion.

## Scope

Every stated construction is now audited in Lean; this closes the maximal
domain of the literal full physical Gamma kernel. Arithmetic energy summability,
source-to-Hardy compatibility and strict sub-unit control remain open.
No RH proof or falsification is asserted.

Closed 2026-10-04. Required lake --old env lean production-leaf audit exits0
with empty diagnostics. All fifteen public foundation queries pass with
only propext, Classical.choice and Quot.sound. No added axioms or holes.
Umbrella wired; index exits0 and all fifteen declarations are present.
Global lint exits1 on twenty unrelated unreachable leaves, with no finding
in this module. Audit logs: /tmp/tg-c918c-final.log, -axioms.log, -index.log,
-lint.log. No full or umbrella builds and no heartbeat changes.
