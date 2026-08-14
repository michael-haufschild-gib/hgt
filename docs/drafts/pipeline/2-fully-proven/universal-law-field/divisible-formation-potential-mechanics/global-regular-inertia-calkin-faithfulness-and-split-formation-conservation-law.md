# Global regular-inertia Calkin faithfulness and split-formation conservation law

- **ID:** ULF-DFPM-4
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / GLOBAL FORMATION / EXACT SELECTION LOCUS
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [SOURCE-CANONICAL HILBERT SUM] [CALKIN-FAITHFUL] [MAXIMAL ESSENTIAL SEPARATION] [SPLIT-FORMATION COMPATIBLE] [RH-EQUIVALENT SPECIALIZATION] [SOURCE ADMISSION STILL OPEN] [NO LEAN IN THIS PASS]

## 1. Why another finite-root calculation is not enough

ULF-DFPM-3 proves that a nonzero integer divisor charge is visible in every sufficiently deep
regular inertia packet.  A weighted sum of finite costs still leaves an avoidable question: why
that weight?  The present theorem removes it.

The root-depth tower itself canonically supplies one finite regular Hilbert module at every depth.
Taking their Hilbert direct sum is the ordinary countable formation operation.  Compactness of the
resulting global symmetry relative to the identity is then a yes/no property with no tunable
cofinal weight.

## 2. Global regular formation

For every integer \(n\ge 2\), put

\[
 C_n=\mathbb Z/n\mathbb Z,
 \qquad H_n=\ell^2(C_n),
 \qquad L_{n,q}e_x=e_{x+[q]_n}.
 \tag{GRC.1}
\]

Form the canonical Hilbert sum

\[
 H_\infty=\bigoplus_{n\ge2}^{\ell^2}H_n
 \tag{GRC.2}
\]

and the block-diagonal unitary

\[
 U_q=\bigoplus_{n\ge2}L_{n,q}\in\mathcal U(H_\infty).
 \tag{GRC.3}
\]

Let \(\pi:\mathcal B(H_\infty)\to\mathcal Q(H_\infty)\) be the quotient to the Calkin algebra.

## 3. Exact Calkin formation theorem

### Theorem 3.1 — faithful maximally separated charge representation

The assignment

\[
 \rho_{\mathrm{ess}}:\mathbb Z\longrightarrow
 \mathcal U(\mathcal Q(H_\infty)),
 \qquad
 q\longmapsto\pi(U_q),
 \tag{GRC.4}
\]

is an injective group homomorphism.  More sharply, for all \(q,q'\in\mathbb Z\),

\[
 \boxed{
 \|\pi(U_q)-\pi(U_{q'})\|
 =\begin{cases}
 0,&q=q',\\
 2,&q\ne q'.
 \end{cases}}
 \tag{GRC.5}
\]

Consequently the following are equivalent:

1. \(q=0\);
2. \(U_q-I\) is compact;
3. \(U_q-I\) belongs to some Schatten class \(\mathcal S^p\), \(0<p<\infty\);
4. \(U_q\) lies in the determinant-class group \(I+\mathcal S^1\);
5. \(\pi(U_q)=1\) in the Calkin algebra.

Thus compact/restricted formation selects zero charge without choosing a depth weight.

### Proof

The finite translations obey \(L_{n,q+q'}=L_{n,q}L_{n,q'}\), hence
\(U_{q+q'}=U_qU_{q'}\); (GRC.4) is a homomorphism.

Fix \(h=q-q'\ne0\).  Write \(a=v_2(|h|)\).  Choose infinitely many odd primes \(p\nmid h\)
and set

\[
 n_p=2^{a+1}p.
\]

Then

\[
 \gcd(n_p,|h|)=2^a,
 \qquad
 \operatorname{ord}_{C_{n_p}}([h])=2p.
 \tag{GRC.6}
\]

By the cycle-spectrum theorem ULF-DFPM-3, \(L_{n_p,h}\) has eigenvalue \(-1\).  Choose a unit
\((-1)\)-eigenvector \(\xi_p\in H_{n_p}\), regarded as a vector of \(H_\infty\).  Distinct block
vectors \(\xi_p\) are orthonormal, hence weakly converge to zero.  For every compact operator
\(K\),

\[
 \|K\xi_p\|\longrightarrow0.
\]

Since \((U_h-I)\xi_p=-2\xi_p\),

\[
 \|(U_h-I+K)\xi_p\|\longrightarrow2.
\]

Therefore the essential norm of \(U_h-I\) is at least \(2\).  The reverse inequality follows
from \(\|U_h-I\|\le2\), so

\[
 \|\pi(U_h)-1\|=2.
 \tag{GRC.7}
\]

Multiplication by the unitary \(U_{q'}\) preserves essential norm and

\[
 U_q-U_{q'}=U_{q'}(U_h-I),
\]

which proves (GRC.5).  Injectivity follows.  A Schatten-class operator is compact, and a zero
operator belongs to every Schatten class, proving the five-way equivalence. ∎

### Corollary 3.2 — compact repair cannot erase charge

For \(q\ne q'\) and compact \(K\),

\[
 \boxed{\|U_q-U_{q'}+K\|\ge2.}
 \tag{GRC.8}
\]

The upper bound \(\|U_q-U_{q'}\|\le2\) makes this sharp.  The global charge defect is therefore
not merely noncompact: it is maximally separated in the essential norm.

## 4. Split-formation fusion and joint reconstruction

Let \(K:X\rightsquigarrow Y\) be a common recovery kernel and

\[
 \mathsf E_K(\mu)(dx,dy)=\mu(dx)K(x,dy)
\]

the split formation of ULF-PFM-2.  Let \(A:X\to X\) be a measurable bijection, and let
\(\widehat A_K\) be its canonical recovery lift.  Attach to a formed law its global inertia mark:

\[
 \mathfrak P_K(\mu,q)=\bigl(\mathsf E_K(\mu),\pi(U_q)\bigr).
 \tag{GRC.9}
\]

### Theorem 4.1 — two-component reconstruction and conservation

The packet (GRC.9) jointly reconstructs \((\mu,q)\): projection reconstructs \(\mu\), while
Theorem 3.1 reconstructs \(q\).  For all observer laws \(\mu,\nu\) and charges \(q,q'\), the
signature

\[
 \boxed{
 \mathfrak D\bigl((\mu,q),(\nu,q')\bigr)
 =\left(D(\mu\Vert\nu),
   2\mathbf 1_{q\ne q'}\right)}
 \tag{GRC.10}
\]

is exactly reproduced on formed packets by

\[
 \left(
 D(\mathsf E_K\mu\Vert\mathsf E_K\nu),
 \|\pi(U_q)-\pi(U_{q'})\|
 \right).
 \tag{GRC.11}
\]

If an action sends \((\mu,q)\mapsto(A_*\mu,q)\), then its canonical common-recovery lift preserves
both entries of (GRC.10).  The first is preserved by reversible split-formation information
isometry; the second is unchanged because the integer charge is transported rather than altered.

### Proof

Projection of \(\mathsf E_K\mu\) to \(X\) is \(\mu\).  Theorem 3.1 makes
\(q\mapsto\pi(U_q)\) injective.  ULF-PFM-2 proves

\[
 D(\mathsf E_K\mu\Vert\mathsf E_K\nu)=D(\mu\Vert\nu)
\]

and invariance under the recovery lift of \(A\).  Equation (GRC.5) proves the second entry. ∎

This is the promised fusion law across four structurally different organs:

| organ | retained datum |
|---|---|
| probability/information | KL geometry of observer laws |
| recovery/formation | sufficient common kernel and exact projection |
| divisor/root history | integer charge and all finite residues |
| operator topology | faithful Calkin unitary with discrete essential metric |

Neither component is a metaphor for the other.  They coexist in one reconstructive packet and obey
one exact conservation law.

## 5. Functional-equation action is neutral, not selecting

The completed theta functional equation of ULF-PFM-2 acts by the reflection
\(a\mapsto-a\) and lifts through the common Hasse recovery kernel without changing KL
information.  A holomorphic reflection transports local divisor multiplicity; it does not
annihilate it.  Hence the induced action on (GRC.9) preserves \(q\) and therefore fixes
\(\pi(U_q)\).

The combined functional-equation lift is information-neutral in the strong two-component sense
(GRC.10): it preserves both statistical distinguishability and essential charge.  This proves a
sharp no-go:

> functional-equation neutrality cannot turn a nonzero divisor charge into a compactly formed
> global inertia symmetry.

The selection law must be global formation, not reflection.

## 6. Divisor and RH specialization

Let \(R\) be a meromorphic formation transfer on a domain, and let a small contour \(\Gamma\)
carry integer charge

\[
 q_\Gamma=\frac1{2\pi i}\int_\Gamma(-d\log R).
\]

Attach \(U_{q_\Gamma}\) by (GRC.3).

### Corollary 6.1 — global compact-formation selection

The following are equivalent:

1. the divisor of \(R\) vanishes;
2. every sufficiently small contour packet satisfies \(U_{q_\Gamma}-I\in\mathcal K(H_\infty)\);
3. every such packet is determinant class;
4. every such Calkin charge is trivial.

For the Euler-shell transfer \(R_{m,r}\) on \(\Re s>1/2\), each is equivalent to RH.

### Proof

Small-contour charges are exactly the local divisor orders.  Theorem 3.1 makes compact or
determinant-class formation equivalent to zero local order.  ULF-DFPM-1 identifies the poles of
\(R_{m,r}\) in the strict-right half-plane with the nontrivial zeta zeros there, including
multiplicity; functional-equation reflection turns their absence into RH. ∎

This is an unconditional equivalence, not an RH proof.  The remaining load-bearing theorem is:

> the literal pre-zero source forms its complete root-inertia symmetry in the compactly restricted
> (or determinant-class) global formation group.

Unlike a weighted action bound, this admission statement has a fixed target category and cannot be
weakened by retuning depth weights.

## 7. Hostile boundaries

1. **Finite packets imply compact global formation.** False.  Every finite block is unitary and
   periodic, while a nonzero global charge is maximally noncompact.
2. **The Hilbert sum hides a chosen weight.** False at the operator level: changing equivalent
   Hilbert norms blockwise does not turn infinitely many norm-two witnesses into a compact family.
   Non-equivalent damping can erase the obstruction, but then it changes the formation functor.
3. **Calkin triviality follows from functional equation.** False.  Reflection preserves local
   multiplicity and hence the Calkin mark.
4. **A compact correction can repair the packet.** False by (GRC.8).
5. **Root-stack existence supplies restricted formation.** False.  Root stacks construct every
   finite inertia block; they do not make their global regular action compact relative to identity.
6. **Restricted formation is already a source theorem.** False.  It is now the exact open
   admission gate, not a consequence smuggled into the construction.
7. **Fock implementability follows from compactness.** Not asserted.  A chosen polarization would
   impose a different Hilbert--Schmidt commutator condition.  The theorem proves only compact,
   Schatten, determinant-class, and Calkin statements explicitly listed above.

## 8. Parent mathematics and literature boundary

Regular representations, Calkin algebras, weakly-null tests for compactness, and restricted unitary
groups are established mathematics.  For the compact-perturbation unitary group
\(\mathcal U_\infty(H)=\{U:U-I\text{ compact}\}\), see Neeb,
*Unitary Representations of Unitary Groups*, arXiv:1308.1500.  Determinant-line constructions and
their renormalization are likewise established; see Dang, *Renormalization of determinant lines in
Quantum Field Theory*, arXiv:1901.10542.

No located source proves the specific fusion (GRC.10), the exact Calkin metric (GRC.5) for the full
root-depth tower, or the Euler-shell specialization.  No external novelty claim is needed.  The
field-level advance is a fixed global formation gate replacing an arbitrary weighted properness
axiom.

No Lean was written or built in this research pass.
