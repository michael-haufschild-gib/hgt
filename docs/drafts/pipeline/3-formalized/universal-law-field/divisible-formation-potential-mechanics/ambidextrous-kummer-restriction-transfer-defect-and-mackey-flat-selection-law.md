# Ambidextrous Kummer restriction--transfer defect and Mackey-flat selection law

- **ID:** ULF-DFPM-5
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / AMBIDEXTROUS FORMATION / EXACT ALGEBRAIC SELECTOR
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [RESTRICTION-INCLUSION FUSION] [CROSSED DEFECT COCYCLE] [JOINT RECONSTRUCTION] [FINITE WITNESS] [GLOBAL PROPERNESS] [RH-EQUIVALENT SPECIALIZATION] [SOURCE BIFLATNESS OPEN] [FULLY LEAN-FORMALIZED]

## 1. Mechanism

A root tower has two canonical but different depth-change laws.  If \(n\mid m\), then:

1. a fine \(m\)-th root can be raised to an \(n\)-th root (**restriction**);
2. an \(n\)-th root of unity is also an \(m\)-th root of unity (**covariant inclusion**).

Ordinary divisor holonomy is automatically coherent for the first law.  It is not coherent for the
second.  Their mismatch is a source-independent crossed defect.  Vanishing of that defect at all
depth changes forces divisor charge zero.

This is not another object attached to a route.  It is a law governing simultaneous covariant and
contravariant formation.

## 2. Canonical depth maps

Write \(C_n=\mathbb Z/n\mathbb Z\).  For \(n\mid m\), define

\[
 R_{m,n}:C_m\longrightarrow C_n,
 \qquad [x]_m\longmapsto[x]_n,
 \tag{ART.1}
\]

and

\[
 T_{n,m}:C_n\longrightarrow C_m,
 \qquad [x]_n\longmapsto[(m/n)x]_m.
 \tag{ART.2}
\]

Under \(C_j\cong\mu_j\), (ART.1) is \(z\mapsto z^{m/n}\), while (ART.2) is the inclusion
\(\mu_n\hookrightarrow\mu_m\).  Both maps are canonical group homomorphisms.  For
\(n\mid m\mid\ell\),

\[
 R_{\ell,n}=R_{m,n}R_{\ell,m},
 \qquad
 T_{n,\ell}=T_{m,\ell}T_{n,m}.
 \tag{ART.3}
\]

The maps are not inverse in general.  This non-invertibility is load-bearing.

## 3. Ambidextrous defect

For integer divisor charge \(q\), put \(q_n=[q]_n\in C_n\).  Restriction is always flat:

\[
 R_{m,n}(q_m)=q_n.
 \tag{ART.4}
\]

Define the covariant-inclusion defect

\[
 \Delta_{n,m}(q)
 =q_m-T_{n,m}(q_n)\in C_m.
 \tag{ART.5}
\]

### Theorem 3.1 — crossed defect and exact selection

For every \(n\mid m\mid\ell\),

\[
 \boxed{
 \Delta_{n,\ell}(q)
 =\Delta_{m,\ell}(q)+T_{m,\ell}\Delta_{n,m}(q).}
 \tag{ART.6}
\]

Moreover, the following are equivalent:

1. \(q=0\);
2. \(\Delta_{n,m}(q)=0\) for every \(n\mid m\);
3. \(q_m=T_{n,m}(q_n)\) for every doubling \(m=2n\);
4. (3) holds for every sufficiently large \(n\).

For every \(q\ne0\) and every \(n>|q|\), the failure is explicit:

\[
 \boxed{
 \Delta_{n,2n}(q)=[-q]_{2n}\ne0.}
 \tag{ART.7}
\]

Thus one cofinal family of finite restriction--transfer squares already selects zero charge.

### Proof

Functoriality of transfer gives

\[
\begin{aligned}
 \Delta_{n,\ell}(q)
 &=q_\ell-T_{n,\ell}q_n\\
 &=(q_\ell-T_{m,\ell}q_m)
   +T_{m,\ell}(q_m-T_{n,m}q_n),
\end{aligned}
\]

which is (ART.6).

If \(q=0\), every defect vanishes.  Conversely, take \(n>|q|\).  Since
\(T_{n,2n}([q]_n)=[2q]_{2n}\),

\[
 \Delta_{n,2n}(q)=[q-2q]_{2n}=[-q]_{2n}.
\]

The inequality \(0<|q|<n<2n\) makes this class nonzero.  This proves (ART.7) and all four
equivalences. ∎

### Corollary 3.2 — defect reconstruction

The marked cofinal defect family

\[
 \bigl(\Delta_{n,2n}(q)\bigr)_{n\ge2}
 \tag{ART.8}
\]

reconstructs \(q\).  Indeed, once \(n>|q|\), its centered integer representative is \(-q\).
Equivalently, equality of the complete defect families for \(q,q'\) implies \(q=q'\).

Restriction holonomy and transfer defect are complementary readings of the same charge:
restriction retains \([q]_n\), while the doubling defect eventually retains the unsimplified
integer \(-q\).

## 4. Regular-packet realization and global properness

On \(H_{2n}=\ell^2(C_{2n})\), let

\[
 V_{n,q}=L_{2n,\Delta_{n,2n}(q)}.
 \tag{ART.9}
\]

Form

\[
 H_{\mathrm{amb}}=\bigoplus_{n\ge2}^{\ell^2}H_{2n},
 \qquad
 V_q=\bigoplus_{n\ge2}V_{n,q}.
 \tag{ART.10}
\]

### Theorem 4.1 — ambidextrous Calkin properness

\[
 \boxed{
 V_q-I\text{ is compact}
 \Longleftrightarrow
 V_q-I\text{ is Schatten}
 \Longleftrightarrow
 q=0.}
 \tag{ART.11}
\]

For \(q\ne0\),

\[
 \boxed{\|\pi(V_q)-1\|=2.}
 \tag{ART.12}
\]

### Proof

If \(q=0\), (ART.7) gives \(V_q=I\).  Suppose \(q\ne0\), and put
\(a=v_2(|q|)\).  Choose infinitely many odd primes \(p\nmid q\), set
\(n_p=2^ap\), and note that \(n_p>|q|\) after discarding finitely many terms.  By (ART.7), the
translation in the \(2n_p=2^{a+1}p\) block is \([-q]\).  Its order is \(2p\), so its regular
permutation has eigenvalue \(-1\).  Unit \((-1)\)-eigenvectors from distinct blocks form a
weakly-null orthonormal sequence on which \(V_q-I\) has norm \(2\).  Compact corrections vanish
on that sequence.  Hence the essential norm is at least \(2\), and the unitary upper bound gives
equality.  Schatten operators are compact, proving (ART.11). ∎

The algebraic selector (ART.7) and topological selector (ART.11) are therefore two shadows of one
ambidextrous defect, not independent hypotheses.

## 5. Functional-equation neutrality

A holomorphic functional-equation reflection transports local divisor order with multiplicity.  It
therefore transports \(q_n\), \(\Delta_{n,m}(q)\), and \(V_q\) without changing them.  Combined
with ULF-PFM-2, the lifted action obeys two conservation laws:

\[
 D(\widehat A_K\mathsf E_K\mu\Vert
   \widehat A_K\mathsf E_K\nu)
 =D(\mu\Vert\nu),
 \tag{ART.13}
\]

\[
 \|\pi(V_q)-1\|
 \quad\text{is invariant.}
 \tag{ART.14}
\]

Thus information-neutral reflection and ambidextrous formation are orthogonal laws.  Reflection
conserves the defect; simultaneous restriction--transfer flatness annihilates it.

## 6. Divisor and RH specialization

For a meromorphic formation transfer \(R\), let

\[
 q_\Gamma=\frac1{2\pi i}\int_\Gamma(-d\log R)
\]

on every sufficiently small contour.

### Corollary 6.1 — Mackey-flat divisor selection

The following are equivalent:

1. the divisor of \(R\) vanishes;
2. every local Kummer charge section is simultaneously restriction-flat and inclusion-flat;
3. every sufficiently large local doubling square has zero defect;
4. every local ambidextrous global packet is compactly restricted.

For the Euler-shell transfer \(R_{m,r}\) on \(\Re s>1/2\), these conditions are equivalent to RH.

### Proof

Theorem 3.1 makes inclusion-flatness equivalent to zero local integer order.  Vanishing of every
local order is vanishing of the divisor.  Theorem 4.1 gives the compact formulation.  ULF-DFPM-1
identifies strict-right orders of \(R_{m,r}\) with zeta-zero multiplicities; functional-equation
reflection converts their absence to RH. ∎

This remains an equivalence, not an RH proof.  The exact source gate is now finite and algebraic:

> prove that source-generated root refinement is horizontal not only for restriction, which is
> automatic, but also for the canonical covariant inclusion law.

No limiting estimate, arbitrary capacity, or chosen compactness norm is needed once that law is
available.

## 7. Hostile boundaries

1. **Restriction coherence implies inclusion coherence.** False; every integer charge satisfies
   restriction coherence, while only zero satisfies both cofinally.
2. **Covariant inclusion is a section of restriction.** False in general:
   \(R_{m,n}T_{n,m}\) is multiplication by \(m/n\) on \(C_n\).
3. **The defect is ordinary cohomological curvature.** Not claimed.  It is a crossed naturality
   defect between opposite depth variances; (ART.6) is its exact composition law.
4. **Root stacks are automatically Mackey-flat.** False.  They retain nonzero inertia and satisfy
   restriction coherence without transfer flatness.
5. **Functional equation supplies inclusion flatness.** False.  It preserves multiplicities and
   hence preserves (ART.5).
6. **The inclusion law is already source-generated.** Open.  The maps are canonical on Kummer
   inertia, but the literal arithmetic source has not yet been proved horizontal for them.
7. **One fixed finite square selects every charge.** False.  A fixed square only sees a residue.
   Cofinal doubling, or one square with \(n>|q|\), is load-bearing.

## 8. Parent mathematics and scope

Restriction, covariant induction/inclusion, Mackey functors, cyclic Kummer groups, and regular
representations are established mathematics.  Mackey-functor treatments of restriction and
transfer include Todea, *Symmetric cohomology of groups as a Mackey functor*, arXiv:1412.2089, and
Brazelton, *Homotopy Mackey functors of equivariant algebraic K-theory*, arXiv:2102.06724.  The
present two-map divisibility-poset system is **not** claimed to satisfy a full double-coset Mackey
axiom; “ambidextrous” refers only to its explicitly defined opposite variances.  The exact crossed
defect (ART.6), cofinal doubling classification (ART.7), and fusion with split-formation
information neutrality are the field mechanism being tested here.  No external novelty claim is
needed.

The theorem proves no source transfer-flatness, no root construction, and no RH.  It replaces a
global analytic admission axiom by one exact finite-level formation law whose failure is completely
reconstructed and topologically amplified.

## 9. Lean formalization boundary

Every theorem of this card is now Lean-certified, unconditionally and without added hypotheses.

| Module | Content |
|---|---|
| `HTGeometry.ConstitutiveAmbidextrousKummerSelection` | the finite doubling selector (ART.7) |
| `HTGeometry.AmbidextrousKummerDepthCalculus` | (ART.1)–(ART.8): both depth maps, their functoriality, the crossed cocycle, Theorem 3.1 and Corollary 3.2 |
| `HTGeometry.LpReindexCompactDichotomy` | the reusable reindexing Calkin engine: a permutation defect is compact iff the moved set is finite, and its distance to the compacts is at least two once orbits grow |
| `HTGeometry.AmbidextrousKummerCalkinProperness` | (ART.9)–(ART.12) and Corollary 6.1 for an arbitrary local charge family |
| `RHTower.MackeyFlatDivisorSelection` | the Euler-shell specialization of Corollary 6.1 and the charge-invariance form of (ART.14) |
| `HTGeometry.ConstitutiveFunctionalEquationPacketLift` | (ART.13), the information isometry of the lifted action |

Axiom audit over all public declarations of the four ambidextrous modules: 66 declarations, only
`propext`, `Classical.choice`, `Quot.sound`; no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`.
All leaves are wired into `UniversalLawField.lean` and their area umbrellas.

Source covariant-inclusion horizontalness is not a theorem of this card; it remains the declared
source-genesis gate.
