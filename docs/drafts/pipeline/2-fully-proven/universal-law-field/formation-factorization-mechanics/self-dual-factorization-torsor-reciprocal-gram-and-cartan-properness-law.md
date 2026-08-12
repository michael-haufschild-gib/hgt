# Self-dual factorization torsor, reciprocal-Gram reconstruction, and Cartan properness law

- **ID:** ULF-FFM-2
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM / FACTORIZATION-GEOMETRY FUSION LAW
- **Parents:** ULF-FFM-1, ULF-CRGM-3, functional-equation packet lift
- **Status:** `[PAPER-PROVED] [LEAN-FORMALIZED CORE] [FORMATION TORSOR]`
  `[ADJOINT-REVERSAL FIXED LOCUS] [RECIPROCAL POSITIVE GRAMS] [PROPER WORK]`
  `[RECURRENT PHASE / OPEN RADIAL HISTORY] [NOT RH]`

## 1. Mathematical delta

ULF-FFM-1 proves that a formed carrier and all its recovery ghosts are blind to certificate
history. This theorem determines what replaces those blind invariants.

For a fixed self-adjoint scaled-idempotent carrier, every exact recovery factorization lies in one
free transitive general-linear torsor. Adjoint reversal acts on that torsor by

\[
 S\longmapsto (S^*)^{-1}.
\tag{CT.1}
\]

Its fixed locus is exactly the unitary stratum. Although the formed carrier forgets `S`, the two
positive leg-Grams are reciprocal and reconstruct `S^*S`. Their trace defect is a proper function
on the full factorization fibre. Along a commuting phase/Cartan flow, the phase projection is
recurrent while the radial factorization history has unbounded work unless its Cartan generator
vanishes.

This is a mechanism theorem. It creates no RH endpoint and assumes no arithmetic parameter.

## 2. Exact recovery fibre

Let `V` and `H` be finite-dimensional complex Hilbert spaces, with

\[
 r=\dim_{\mathbb C}V\ge1.
\]

Let

\[
 \iota:V\longrightarrow H
\]

be an isometric embedding. Put

\[
 E=\iota\iota^*.
\tag{CT.2}
\]

Then `E` is the orthogonal projection onto `ran iota`, `iota* iota=I_V`, and `rank E=r`.
Fix a real number `m>0` and set

\[
 P=mE,
 \qquad
 Q_0=\sqrt m\,\iota,
 \qquad
 B_0=\sqrt m\,\iota^*.
\tag{CT.3}
\]

Thus

\[
 B_0Q_0=mI_V,
 \qquad
 Q_0B_0=P.
\tag{CT.4}
\]

Define the exact recovery fibre over `P` by

\[
 \mathcal F_P=
 \left\{(B,Q):
 B:H\to V,\ Q:V\to H,\ BQ=mI_V,\ QB=P
 \right\}.
\tag{CT.5}
\]

## Theorem 3.1 — factorization fibre is a general-linear torsor

For every `S in GL(V)`, define

\[
 B_S=S^{-1}B_0,
 \qquad
 Q_S=Q_0S.
\tag{CT.6}
\]

Then `(B_S,Q_S)` belongs to `F_P`, and

\[
 \boxed{
 GL(V)\longrightarrow\mathcal F_P,
 \quad S\longmapsto(B_S,Q_S)}
\tag{CT.7}
\]

is a bijection. Equivalently, the right action

\[
 (B,Q)\cdot T=(T^{-1}B,QT)
\tag{CT.8}
\]

is free and transitive on `F_P`.

### Proof

Equation `(CT.4)` gives

\[
 B_SQ_S=S^{-1}B_0Q_0S=mI_V,
 \qquad
 Q_SB_S=Q_0SS^{-1}B_0=P,
\]

so `(CT.6)` lands in the fibre.

Conversely, let `(B,Q)` lie in `F_P`. Since `BQ=mI_V`, the map `Q` is injective. Moreover,

\[
 EQ=m^{-1}QBQ=Q,
\]

so `ran Q` lies in `ran E`. Both spaces have dimension `r`; hence

\[
 \operatorname{ran}Q=\operatorname{ran}E=\operatorname{ran}\iota.
\]

Define

\[
 S=m^{-1/2}\iota^*Q.
\tag{CT.9}
\]

It is invertible and `Q=Q_0S`. From `QB=P`,

\[
 Q(B-S^{-1}B_0)=0.
\]

Injectivity of `Q` gives `B=S^{-1}B_0`. Thus `(CT.7)` is surjective. Uniqueness follows from
injectivity of `Q_0`, proving bijectivity. Formula `(CT.8)` is the transported right multiplication
action and is therefore free and transitive. QED.

## 4. Adjoint reversal and its fixed locus

Define

\[
 \mathscr R(B,Q)=(Q^*,B^*).
\tag{CT.10}
\]

## Theorem 4.1 — self-dual factorization equals unitary recovery

Adjoint reversal is an involution of `F_P`. In torsor coordinates it is

\[
 \boxed{\rho(S)=(S^*)^{-1}.}
\tag{CT.11}
\]

Its fixed locus is exactly

\[
 \boxed{\operatorname{Fix}(\rho)=U(V).}
\tag{CT.12}
\]

Equivalently,

\[
 \mathscr R(B_S,Q_S)=(B_S,Q_S)
 \iff B_S=Q_S^*
 \iff S^*S=I_V.
\tag{CT.13}
\]

### Proof

Because `P=P*` and `m` is real,

\[
 Q^*B^*=(BQ)^*=mI_V,
 \qquad
 B^*Q^*=(QB)^*=P.
\]

Thus `(CT.10)` preserves the fibre, and applying it twice gives the identity.

Since `B_0=Q_0^*`,

\[
 Q_S^*=S^*B_0=B_{(S^*)^{-1}},
 \qquad
 B_S^*=Q_0(S^*)^{-1}=Q_{(S^*)^{-1}},
\]

proving `(CT.11)`. A fixed point satisfies `S=(S*)^{-1}`, equivalently `S*S=I`; this is exactly
unitarity. QED.

Adjoint reversal is the coordinate-free formation analogue of a functional equation exchanging
semantic and lineage packets. Common recovery remains fixed; the factorization is fixed only in
the unitary chamber.

## 5. Reciprocal positive-Gram reconstruction

Define the normalized lineage and semantic leg-Grams on `V`:

\[
 G_Q(S)=m^{-1}Q_S^*Q_S,
 \qquad
 G_B(S)=m^{-1}B_SB_S^*.
\tag{CT.14}
\]

## Theorem 5.1 — positivity retains exactly the Cartan coordinate

For every `S in GL(V)`,

\[
 \boxed{G_Q(S)=S^*S,}
\tag{CT.15}
\]

\[
 \boxed{G_B(S)=(S^*S)^{-1},}
\tag{CT.16}
\]

and therefore

\[
 \boxed{G_B(S)G_Q(S)=I_V.}
\tag{CT.17}
\]

Consequently the paired positive-Gram packet reconstructs the full positive Cartan coordinate
`S*S`. It forgets only the left unitary polar factor. Adjoint reversal exchanges the two reciprocal
Grams.

### Proof

Using `iota* iota=I`,

\[
 m^{-1}Q_S^*Q_S
 =S^*\iota^*\iota S
 =S^*S.
\]

Similarly,

\[
 m^{-1}B_SB_S^*
 =S^{-1}\iota^*\iota(S^{-1})^*
 =S^{-1}(S^*)^{-1}
 =(S^*S)^{-1}.
\]

This proves `(CT.15)--(CT.17)`. Polar decomposition writes `S=U(S*S)^(1/2)`; hence `S*S`
determines the factorization modulo left unitary gauge. QED.

This corrects an overbroad slogan. Positive formation is a phase quotient, but it is not a total
factorization quotient: it retains the noncompact radial coordinate exactly.

## 6. Proper Cartan work

Let `sigma_1(S),...,sigma_r(S)>0` be the singular values of `S`. Define

\[
 \mathcal W(S)
 =m^{-1}\left(\|B_S\|_{\rm HS}^2+\|Q_S\|_{\rm HS}^2\right)-2r.
\tag{CT.18}
\]

## Theorem 6.1 — exact work formula, rigidity, and properness

For every `S in GL(V)`,

\[
 \boxed{
 \mathcal W(S)
 =\|S\|_{\rm HS}^2+\|S^{-1}\|_{\rm HS}^2-2r
 =\sum_{j=1}^r\left(\sigma_j-\sigma_j^{-1}\right)^2.}
\tag{CT.19}
\]

Hence:

1. `W(S)>=0`;
2. `W(S)=0` iff `S` is unitary iff the factorization is fixed by adjoint reversal;
3. `W(rho(S))=W(S)`;
4. `W(USV)=W(S)` for all unitary `U,V`;
5. `W:GL(V)->[0,infinity)` is proper.

### Proof

Equations `(CT.15)--(CT.16)` give

\[
 m^{-1}\|Q_S\|_{\rm HS}^2=\operatorname{tr}(S^*S)=\sum_j\sigma_j^2,
\]

\[
 m^{-1}\|B_S\|_{\rm HS}^2=\operatorname{tr}((S^*S)^{-1})
 =\sum_j\sigma_j^{-2}.
\]

Subtracting `2r` proves `(CT.19)`. Every summand is nonnegative and vanishes exactly at
`sigma_j=1`, which is equivalent to unitarity. Adjoint reversal inverts every singular value;
left and right unitary multiplication preserve them, proving items 3 and 4.

If `W(S)<=C`, then

\[
 \|S\|_{\rm HS}^2\le C+2r,
 \qquad
 \|S^{-1}\|_{\rm HS}^2\le C+2r.
\tag{CT.20}
\]

Thus the sublevel is bounded in the finite-dimensional matrix space and every least singular value
is at least `(C+2r)^(-1/2)`. It is closed: a convergent sequence satisfying `(CT.20)` cannot acquire
a kernel. Hence every sublevel is compact. QED.

## 7. Cartan rays, recurrent phase, and open factorization history

Let `X=X*` and `Y*=-Y` on `V`, and assume `[X,Y]=0`. Define

\[
 S_t=e^{tY}e^{tX}.
\tag{CT.21}
\]

Let `lambda_1,...,lambda_r` be the real eigenvalues of `X`.

## Theorem 7.1 — compact phase and proper radial selection

For every real `t`,

\[
 \boxed{\rho(S_t)=e^{tY}e^{-tX},}
\tag{CT.22}
\]

\[
 \boxed{
 \mathcal W(S_t)
 =4\sum_{j=1}^r\sinh^2(t\lambda_j).}
\tag{CT.23}
\]

The unitary phase orbit `e^(tY)` has compact closure and returns arbitrarily close to the identity
at unbounded positive times. Nevertheless:

\[
 \boxed{
 \sup_{t\in\mathbb R}\mathcal W(S_t)<\infty
 \iff X=0,}
\tag{CT.24}
\]

and, more strongly, bounded work along any sequence with `|t_n|->infinity` implies `X=0`.

Thus a closed recurrent phase projection can coexist with an open factorization history, while
proper factorization work selects the neutral radial generator exactly.

### Proof

Commutation gives

\[
 S_t^*=e^{tX}e^{-tY},
 \qquad
 (S_t^*)^{-1}=e^{tY}e^{-tX},
\]

proving `(CT.22)`. Unit multiplication does not change singular values, so the singular values of
`S_t` are `e^(t lambda_j)`. Substitution into `(CT.19)` yields

\[
 e^{2t\lambda_j}+e^{-2t\lambda_j}-2
 =4\sinh^2(t\lambda_j),
\]

proving `(CT.23)`. A finite-dimensional unitary one-parameter group has compact torus closure and
is recurrent. If any `lambda_j` is nonzero, its summand diverges along every sequence
`|t_n|->infinity`; conversely `X=0` makes the work identically zero. QED.

## 8. Joint reconstruction and conservation identity

The formed carrier and the paired positive legs obey the exact ledger

\[
 \boxed{
 \underbrace{Q_SB_S}_{mE}\quad\text{is constant},
 \qquad
 \underbrace{m^{-1}Q_S^*Q_S}_{G}
 \underbrace{m^{-1}B_SB_S^*}_{G^{-1}}=I,
 \qquad
 \mathcal W=\operatorname{tr}(G+G^{-1}-2I).}
\tag{CT.25}
\]

It fuses four previously separate organs:

1. exact recovery/factorization;
2. functional-equation adjoint reversal;
3. positive Gram/capacity geometry;
4. recurrence with open lifted history and proper work.

The first component loses all factorization data. The second and third reconstruct precisely the
noncompact radial coordinate. The phase survives only in the full factorization history.

## 9. Conjecture-to-proof/failure loops

### Loop A — carrier invariants reconstruct exact recovery

**Failed.** ULF-FFM-1 already proves carrier and ghost blindness.

**Positive survivor.** The exact recovery fibre is the torsor `(CT.7)`, not another carrier
invariant.

### Loop B — varying recovery is the missing information current

**Failed as frontier.** The corpus already contains the conditional-KL chain rule and proves that
variable conditional innovations add nonnegatively. That is a known information ledger, not the
missing formation geometry.

**Positive survivor.** Recovery variation must be separated into compact unitary gauge and
noncompact Cartan displacement.

### Loop C — positivity erases every factorization coordinate

**Failed.** One positive carrier can erase phase, but the paired positive leg-Grams satisfy
`(CT.15)--(CT.17)` and reconstruct `S*S` exactly.

**Positive survivor.** Positivity is the quotient from `GL(V)` to its positive Cartan cone, not a
collapse to a scalar.

### Loop D — adjoint reversal has a large ambiguous fixed locus

**Failed.** The fixed locus is exactly `U(V)` by `(CT.12)`.

**Positive survivor.** Self-dual exact recovery is equivalent to zero Cartan work.

### Loop E — recurrent observation closes the history

**Failed.** The phase in `(CT.21)` is recurrent for every `X`, while work diverges for every
nonzero `X`.

**Positive survivor.** Bounded recurrent history is a properness theorem, not a recurrence theorem.

### Loop F — proper work alone proves RH

**Failed.** The theorem contains no arithmetic source map identifying off-centre displacement with
`X` and no proof that physical histories have bounded factorization work.

**Positive survivor.** Any final selector must produce both facts before specialization; neither
can be imported from the endpoint.

## 10. Literature and hostile significance audit

Dual reconstruction systems, descriptions of dual frames, polar decomposition, the positive cone
`GL/U`, and logarithmic/polar minimization are established mathematics. Relevant primary parents
include:

- Massey--Ruiz--Stojanoff, *Robust dual reconstruction systems and fusion frames*,
  arXiv:1112.1654;
- Heineken--Morillas, *Oblique dual Fusion Frames*, arXiv:1612.05493;
- Kamuda--Kuzel, *On Description of Dual Frames*, arXiv:2007.09216;
- Neff--Nakatsukasa--Fischle, *A logarithmic minimization property of the unitary polar factor*,
  arXiv:1302.3235;
- Liu, *A Self-Dual Frame Formalism of the SO(3) Yang--Mills Theory*, arXiv:2607.14204.

The abstract ingredients are occupied. The exact corpus leverage is the coupled ledger `(CT.25)`:
one common-recovery carrier is certificate-blind, adjoint reversal fixes exactly the unitary
factorization, reciprocal positive leg-Grams reconstruct the Cartan coordinate, and that coordinate
has a proper work law compatible with recurrent compact phase. No priority claim is made for the
ingredients.

## 11. Exact boundary and next gate

The theorem is finite-dimensional and assumes a self-adjoint scaled projection with equal recovery
rank. It does not cover nonclosed ranges, unbounded factorizations, indefinite/Krein recovery,
branching complexes, or source-derived arithmetic certificates.

The next gate is now sharp:

> Construct a literal pre-zero arithmetic factorization whose functional equation acts as
> adjoint reversal on the factorization torsor, whose paired positive reporters realize the
> reciprocal-Gram ledger, and whose source law bounds the proper work along the physical orbit.

Only then can `(CT.24)` select the zero Cartan generator and be compared with the RH displacement.

## 12. Lean certificate and exact boundary

The unconditional algebraic/properness core is formalized in
`formal/GaloisForLFunctions/HTGeometry/ConstitutiveSelfDualFactorizationGeometry.lean`:

1. `exactRecoveryFactorizationEquiv` classifies every exact recovery pair by one gauge;
2. `exactRecoveryFactorization_reverse_fixed_iff` identifies reversal-fixed pairs with balanced
   gauges;
3. `semanticGramGauge_mul_lineageGramGauge` proves reciprocal-Gram conservation;
4. `cartanModeWork_add_two`, `cartanModeWork_nonneg`, and `cartanModeWork_eq_zero_iff` certify the
   reciprocal exponential work identity and its zero locus;
5. `eq_zero_of_bounded_cartanPacketWork` proves that uniformly bounded finite-packet work along all
   natural depths forces every radial rate to vanish.

This certificate is deliberately more abstract than the Hilbert-space presentation: it proves the
torsor/reversal/Gram laws in every involutive star-group, then proves the properness selector for a
finite real Cartan packet. The finite-dimensional matrix compact-sublevel theorem, singular-value
formula, and compact unitary recurrence statement remain paper-only and are not claimed as Lean
certified by this card.

## Log

- 2026-08-12 — variable-recovery conjecture killed by existing conditional-KL theorem.
- 2026-08-12 — exact factorization torsor and adjoint-reversal fixed locus proved.
- 2026-08-12 — reciprocal positive-Gram reconstruction and proper Cartan work proved.
- 2026-08-12 — recurrent-phase/open-radial-history theorem proved.
- 2026-08-12 — exact gauge classification, adjoint fixed locus, reciprocal-Gram conservation, and
  finite-packet bounded-work selection formalized in Lean and wired into the ULF umbrella.
