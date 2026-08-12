# Semantic--lineage scaled-idempotent and ghost-neutrality law

- **ID:** ULF-FFM-1
- **Stage:** 2 -- fully proven on paper
- **Type:** THEOREM / CROSS-MECHANISM FUSION LAW
- **Parents:** ULF-CRGM-3 and ULF-WFM-2
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [LEAN-FORMALIZED] [BRIDGE]`
  `[FORMATION/RECOVERY FUSION] [SCALED IDEMPOTENT] [GHOST NEUTRALITY]`
  `[CERTIFICATE-BLIND CARRIER] [NOT RH]`
- **Formal status:** Lean formalized in
  `GaloisForLFunctions.HTGeometry.ConstitutiveSemanticLineageWittFusion`.

## 1. Mathematical delta

Operator-certificate genealogy and Witt formation were previously separate mechanisms. Their exact
fusion is forced by the common recovery equation. The formed history operator is a scaled
idempotent, so every polynomial and ghost observation of that operator forgets the certificate
history. The missing information is not another spectral invariant. It is the factorization of the
formed operator into semantic and lineage packets.

This is a mechanism theorem, not an RH route theorem.

## 2. Packet formation

Let `K` be a field, let `I` be a finite type of cardinality `m`, and let `V` be a `K`-vector space.
For every `i in I`, choose a linear equivalence

\[
 A_i:V\simeq V.
\]

On the history space `H=I -> V`, define the semantic and lineage packets

\[
 B_A(x)=\sum_{i\in I}A_i x_i,
 \qquad
 (Q_Av)_i=A_i^{-1}v.
\tag{FF.1}
\]

Define the formed carrier

\[
 P_A=Q_AB_A:H\longrightarrow H.
\tag{FF.2}
\]

No positivity, topology, endpoint, or spectral parameter enters these definitions.

## Theorem 3.1 -- exact recovery and scaled idempotence

For every certificate family `A`:

\[
 \boxed{B_AQ_A=mI_V,}
\tag{FF.3}
\]

\[
 \boxed{P_A^2=mP_A,}
\tag{FF.4}
\]

and, for every integer `n>=1`,

\[
 \boxed{P_A^n=m^{n-1}P_A.}
\tag{FF.5}
\]

If `m` is nonzero in `K`, then `E_A=m^{-1}P_A` is an idempotent. Moreover,

\[
 \ker E_A=\ker B_A,
 \qquad
 \operatorname{ran}E_A=\operatorname{ran}Q_A,
\tag{FF.6}
\]

and

\[
 H=\operatorname{ran}Q_A\oplus\ker B_A.
\tag{FF.7}
\]

### Proof

For `v in V`, every summand of `B_AQ_Av` is

\[
 A_iA_i^{-1}v=v.
\]

There are `m` summands, proving `(FF.3)`. Associativity gives

\[
 P_A^2=Q_AB_AQ_AB_A=Q_A(mI_V)B_A=mP_A,
\]

which proves `(FF.4)`. Induction proves `(FF.5)`.

If `m` is invertible, `(FF.4)` gives `E_A^2=E_A`. Equation `(FF.3)` shows that `Q_A` is injective
and `B_A` is surjective. Hence `P_Ax=0` iff `B_Ax=0`, and every vector in the range of `P_A` lies
in the range of `Q_A`, while

\[
 P_AQ_Av=Q_AB_AQ_Av=mQ_Av
\]

puts every lineage vector in the range of `P_A`. This proves `(FF.6)`. The standard image--kernel
decomposition of an idempotent proves `(FF.7)`. QED.

## Theorem 4.1 -- certificate families are conjugate carriers

Define the pointwise certificate gauge

\[
 D_A:H\longrightarrow H,
 \qquad
 (D_Ax)_i=A_ix_i.
\tag{FF.8}
\]

It is a linear equivalence. If `1` denotes the constant identity certificate family, then

\[
 \boxed{D_AP_A=P_1D_A.}
\tag{FF.9}
\]

Consequently all `P_A` have the same similarity class. Any invariant depending only on the formed
carrier through composition, polynomial functional calculus, rank, or constant-recurrence data is
certificate-blind; in finite dimension the same holds for characteristic polynomial, trace, and
determinant.

### Proof

For `x in H`,

\[
 (D_AP_Ax)_i=A_iA_i^{-1}\sum_jA_jx_j=\sum_jA_jx_j.
\]

Also

\[
 (P_1D_Ax)_i=\sum_j(D_Ax)_j=\sum_jA_jx_j.
\]

Thus `(FF.9)` holds coordinatewise. Similarity invariance gives the final statement. QED.

## Theorem 5.1 -- exact operator ghost law

Define the `n`-th recovery ghost by

\[
 \Gamma_{A,n}=B_AP_A^nQ_A:V\longrightarrow V
 \qquad(n\ge0).
\tag{FF.10}
\]

Then

\[
 \boxed{\Gamma_{A,n}=m^{n+1}I_V.}
\tag{FF.11}
\]

In particular:

1. `Gamma_(A,n)` is independent of every certificate `A_i`;
2. the ghost sequence obeys the first-order recurrence
   \[
   \boxed{\Gamma_{A,n+1}=m\Gamma_{A,n};}
   \tag{FF.12}
   \]
3. over `C`, it is the operator-valued lift of the one-mode Witt ghost with mode `m`;
4. if `m` is nonzero, any Hankel or constant-recurrence observer built only from these ghosts sees
   one mode, regardless of the complexity or conditioning of the certificate history; when `m=0`
   the ghost packet is identically zero.

### Proof

For `n=0`, `(FF.11)` is `(FF.3)`. For general `n`, use `(FF.5)` when `n>0`, then `(FF.3)` twice:

\[
 B_AP_A^nQ_A
 =m^{n-1}B_AQ_AB_AQ_A
 =m^{n+1}I_V.
\]

The recurrence is immediate. The scalar Witt ghost of the one-mode packet `(m)` is `m^k`, so the
remaining statements follow. QED.

## 6. Information-neutrality and its exact limit

Theorem 5.1 is stronger than invariance under one functional equation. It says that the complete
formed ghost packet is constant on the entire certificate-factorization space.

This does **not** mean certificate history is absent. ULF-CRGM-3 proves that, on finite-dimensional
Hilbert fibres, the factorization energies

\[
 E_A^{\rm sem}=\|B_A\|_{\rm HS}^2,
 \qquad
 E_A^{\rm lin}=\|Q_A\|_{\rm HS}^2
\]

satisfy a sharp polar law and vary with the certificates. For a one-dimensional two-stage example
`A_0=1`, `A_1=r>0`,

\[
 E_A^{\rm sem}E_A^{\rm lin}
 =(1+r^2)(1+r^{-2})
 =2+r^2+r^{-2},
\tag{FF.13}
\]

while every carrier ghost remains `2^(n+1)`. Thus carrier spectrum and factorization work are
independent sorts of information.

## 7. Mechanism consequences

1. **Why formed-carrier searches stall.** Trace, determinant, recurrence, Hankel rank, and polynomial
   functional calculus of `P_A` cannot recover certificate history: `(FF.9)` forbids it.
2. **Why common recovery is information-neutral.** Recovery removes certificate dependence exactly,
   not approximately.
3. **Where constitutive information lives.** It lives in the factorization fibre of `P_A`, not in
   the similarity class of `P_A`.
4. **What a selector must see.** A selector must be sensitive to factorization work, admission, or
   properness. A scalar invariant of the formed carrier is structurally incapable of selecting.

## 8. Hostile boundary and literature

Scaled idempotents, dual reconstruction systems, oblique frames, similarity invariants, and Witt
ghosts are established mathematics. Relevant parents include Massey--Ruiz--Stojanoff,
*Robust dual reconstruction systems and fusion frames* (arXiv:1112.1654), Heineken--Morillas,
*Oblique dual fusion frames* (arXiv:1612.05493), and Dotto--Krause--Nikolaus--Patchkoria,
*Witt vectors with coefficients and TR* (arXiv:2312.12971).

The theorem is therefore labelled `[BRIDGE]`. Its value is the exact ULF fusion and the resulting
no-go: formed-carrier invariants have already discarded the data on which global selection must
act.

No source-normal proper action on the factorization fibre is constructed here. No arithmetic
certificate stream, Xi landing, or RH conclusion is asserted.

## 9. Lean certificate

Module `formal/GaloisForLFunctions/HTGeometry/ConstitutiveSemanticLineageWittFusion.lean`
formalizes exactly:

- semantic and lineage linear maps for an arbitrary finite certificate family;
- `(FF.3)--(FF.5)`;
- pointwise conjugacy `(FF.9)`;
- ghost identity `(FF.11)`, recurrence `(FF.12)`, certificate independence, and the one-mode Witt
  comparison;
- capstone theorem `semanticLineageWittFusion_unconditional`.

Direct elaboration, leaf build, and the `HTGeometry.UniversalLawField` umbrella build pass. Scratch
axiom prints report only `propext`, `Classical.choice`, and `Quot.sound`; no added axiom, `sorry`,
`admit`, `unsafe`, or opaque proof is used. The detailed Stage-3 certificate is stored under
`pipeline/3-formalized/universal-law-field/formation-factorization-mechanics/`.
