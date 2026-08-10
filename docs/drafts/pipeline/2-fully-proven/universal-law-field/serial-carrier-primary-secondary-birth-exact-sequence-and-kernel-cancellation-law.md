# Serial-carrier primary--secondary birth exact sequence and kernel-cancellation law

- **ID:** ULF-PSB-1
- **Stage:** 2-fully-proven
- **Type:** ROUTE-INDEPENDENT MECHANISM THEOREM
- **Statement:** Successive carriers split law birth into a primary obstruction and a canonical
  secondary obstruction; the outer kernel is exactly the cancellation freedom between them.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT]
  [EXACT-SEQUENCE LAW] [DUAL COUNTERMODELS] [LEAN-CERTIFIED] [UMBRELLA-BUILT]
  [AXIOM-AUDITED] [NOT RH]

## 1. Setup

Let \(\Bbbk\) be a field, let \(E,K,A\) be \(\Bbbk\)-vector spaces, and let

\[
E\xrightarrow{S}K\xrightarrow{T}A
\tag{PSB.1}
\]

be linear maps. Define

\[
P_T=\frac{A}{\operatorname{im}T},\qquad
C_{T,S}=\frac{A}{\operatorname{im}(TS)},\qquad
Q_{T,S}=\frac{K}{\operatorname{im}S+\ker T}.
\tag{PSB.2}
\]

For an ambient residual \(a\in A\), its **primary obstruction** is

\[
\pi_T(a)=[a]_{P_T}.
\tag{PSB.3}
\]

If \(\pi_T(a)=0\), choose \(k\in K\) with \(Tk=a\). Its **secondary obstruction** is

\[
\sigma_{T,S}(a)=[k]_{Q_{T,S}}.
\tag{PSB.4}
\]

## 2. Primary--secondary birth theorem

### Theorem 2.1

The class in (PSB.4) is independent of the chosen outer lift. Moreover:

1. \(\pi_T(a)=0\) iff an outer lift \(k\) with \(Tk=a\) exists;
2. once an outer lift exists,

   \[
   [a]_{C_{T,S}}=0
   \quad\Longleftrightarrow\quad
   \sigma_{T,S}(a)=0;
   \tag{PSB.5}
   \]

3. equivalently, a composite lift exists iff

   \[
   k\in\operatorname{im}S+\ker T;
   \tag{PSB.6}
   \]

4. every residual lies in exactly one phase:

   \[
   \begin{array}{ll}
   \text{primary failure:}&a\notin\operatorname{im}T,\\
   \text{completed birth:}&a\in\operatorname{im}(TS),\\
   \text{secondary failure:}&a\in\operatorname{im}T\setminus
      \operatorname{im}(TS).
   \end{array}
   \tag{PSB.7}
   \]

### Proof

The primary zero criterion is the quotient zero criterion. If \(Tk=Tk'\), then
\(k-k'\in\ker T\), so \(k\) and \(k'\) define the same class modulo
\(\operatorname{im}S+\ker T\).

Suppose first that \(a=TS(e)\). For any outer lift \(Tk=a\),

\[
k=S(e)+(k-S(e)),\qquad T(k-S(e))=0,
\]

so \(k\in\operatorname{im}S+\ker T\). Conversely, if
\(k=S(e)+n\) with \(n\in\ker T\), then

\[
a=Tk=TS(e)+Tn=TS(e).
\]

This proves (PSB.5)--(PSB.6). Splitting first on membership in \(\operatorname{im}T\), then on
membership in \(\operatorname{im}(TS)\subseteq\operatorname{im}T\), proves the exclusive
trichotomy. \(\square\)

## 3. Exact-sequence law

### Theorem 3.1

There is a canonical short exact sequence

\[
0\longrightarrow Q_{T,S}
\xrightarrow{\ i\ }C_{T,S}
\xrightarrow{\ p\ }P_T
\longrightarrow0,
\tag{PSB.8}
\]

where

\[
i([k])=[Tk],\qquad p([a])=[a].
\tag{PSB.9}
\]

### Proof

The map \(i\) is well-defined because

\[
T(\operatorname{im}S+\ker T)=\operatorname{im}(TS).
\]

If \(i([k])=0\), then \(Tk=TS(e)\) for some \(e\), hence
\(k=S(e)+(k-S(e))\in\operatorname{im}S+\ker T\), so \([k]=0\). Thus \(i\) is injective.

The inclusion \(\operatorname{im}(TS)\subseteq\operatorname{im}T\) makes \(p\) well-defined and
surjective. Finally,

\[
[a]\in\ker p
\iff a\in\operatorname{im}T
\iff a=Tk\text{ for some }k
\iff [a]=i([k]),
\]

so \(\operatorname{im}i=\ker p\). \(\square\)

## 4. Kernel-cancellation theorem

### Theorem 4.1

The condition \(k\in\operatorname{im}S\) is not invariant and is strictly stronger than
composite birth. The exact invariant is (PSB.6). In particular, a component of an outer lift
outside \(\operatorname{im}S\) is harmless precisely when it can be moved into \(\ker T\).

### Laboratory A: cancellation repairs apparent inner failure

Let

\[
S(e)=(e,0),\qquad T_+(x,y)=x+y,
\]

and take \(a=1\), \(k=(0,1)\). Then \(T_+k=1\) and
\(k\notin\operatorname{im}S\), but

\[
k=S(1)+(-1,1),\qquad (-1,1)\in\ker T_+.
\]

Therefore the secondary obstruction vanishes and \(T_+S(1)=1\): the apparent failure is exactly
cancelled by outer-kernel freedom.

### Laboratory B: genuine secondary failure

Keep \(S(e)=(e,0)\), but let

\[
T_2(x,y)=y.
\]

For \(a=1\), \(k=(0,1)\) is an outer lift, so the primary obstruction vanishes. But
\(T_2S=0\), hence no composite lift of \(1\) exists and the secondary class is nonzero.

The two laboratories have the same inner carrier and the same chosen outer lift. What differs is
whether outer-kernel freedom intersects the missing direction. This is why kernel data cannot be
discarded after a cokernel obstruction vanishes.

## 5. Mechanism laws

1. **Birth is staged.** Vanishing of a late obstruction does not imply end-to-end production.
2. **Kernels are active.** They are compensating freedoms, not bookkeeping leftovers.
3. **Secondary obstruction is relative.** It lives modulo both inner production and outer
   invisibility.
4. **Later doctrine cannot repair primary failure.** It can only cancel an inner mismatch after
   an outer lift exists.
5. **Serial obstructions form extensions, not a scalar sum.** No universal scalar defect can retain
   the information in (PSB.8).

These laws are independent of any RH endpoint. They describe how constitutive mechanisms compose.

## 6. Relation to existing mathematics

The proof uses standard quotient exactness and the first/third isomorphism mechanisms. Existing
corpus specializations include quotient-tower transitions, octahedral relative fibres,
kernel--cokernel index arithmetic, and Shilov-deficit composition. ULF-PSB-1 does not claim a new
exact-sequence technique. Its field content is the interpretation of that exact sequence as a
universal law-birth mechanism with a falsifiable kernel-cancellation rule.

## 7. Sharp boundary and next problem

Replacing ranges by closed ranges does not automatically preserve (PSB.8). The preimage of a
closed composite range need not equal
\(\overline{\operatorname{im}S+\ker T}\), and images of closed subspaces need not be closed.
The next mechanism must classify when completion commutes with serial birth and when a new
closure-interchange defect appears. No such topological exactness is asserted here.

## 8. Falsifiers

This theorem is falsified by any example where one of the following fails:

1. two outer lifts of the same residual define different secondary classes;
2. a composite lift exists while the secondary class is nonzero;
3. the canonical map \(Q_{T,S}\to C_{T,S}\) is noninjective;
4. its image differs from the kernel of \(C_{T,S}\to P_T\);
5. the quotient transition is not surjective.

The proofs exclude all five over vector spaces.

## 9. Lean certificate

`HTGeometry.ConstitutiveCarrierComposition` formalizes definitions, zero criteria, lift
independence, exclusive phase trichotomy, the canonical short exact sequence, kernel cancellation,
genuine secondary failure, and one unconditional capstone containing both laboratories. Direct
foreground elaboration and formal lint pass. The final
`lake build GaloisForLFunctions.HTGeometry.UniversalLawField` audit succeeds with `11,542` jobs.
Source-level `#print axioms` on the main equivalence, exactness theorem, trichotomy, lift
independence, and capstone reports only `propext`, `Classical.choice`, and `Quot.sound`.
