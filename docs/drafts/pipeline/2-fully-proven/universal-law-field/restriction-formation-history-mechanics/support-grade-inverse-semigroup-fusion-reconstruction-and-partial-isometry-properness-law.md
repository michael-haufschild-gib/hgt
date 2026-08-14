# Support--grade inverse-semigroup fusion, reconstruction, and partial-isometry properness law

- **ID:** ULF-RFHM-1
- **Stage:** 2-fully-proven
- **Type:** UNIVERSAL-LAW FIELD THEOREM / SUPPORT--HISTORY FUSION
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [BRIDGE] [NATIVE-SUPPORT NO-GO]
  [INVERSE-SEMIGROUP FUSION] [JOINT RECONSTRUCTION] [EXACT CONSERVATION]
  [PARTIAL-ISOMETRY PROPERNESS] [FUNCTIONAL-EQUATION NEUTRALITY] [NO LEAN IN THIS PASS]

## 1. The doctrine mismatch

Let (E) be a meet-semilattice, written multiplicatively:

\[
 ef=e\wedge f,
 \qquad e^2=e.
 \tag{RFH.1}
\]

Let (G) be a group.  Native divisor support belongs to the first doctrine: intersection is
idempotent.  Kummer phase, recurrence, and reversible history belong to the second: every element
is invertible.

### Theorem 1.1 -- no coefficient-faithful group-like support landing

Every semigroup homomorphism

\[
 \phi:E\longrightarrow G
 \tag{RFH.2}
\]

is trivial:

\[
 \boxed{\phi(e)=1_G\quad(e\in E).}
 \tag{RFH.3}
\]

### Proof

Since (e^2=e),

\[
 \phi(e)^2=\phi(e^2)=\phi(e).
\]

Multiplication by (phi(e)^{-1}) gives (phi(e)=1_G).  ∎

This is stronger than saying a particular proposed map has not been found.  No multiplicative map
from native support intersection to a group can retain even one nontrivial support bit.

## 2. The fused carrier

Assume now that (E) has a least element (0), and that (G) acts on (E) by meet-semilattice
automorphisms.  Write (ge) for the action.  On

\[
 S=E\rtimes G=E\times G
 \tag{RFH.4}
\]

define

\[
 (e,g)(f,h)=(e\wedge gf,gh),
 \tag{RFH.5}
\]

and

\[
 (e,g)^*=(g^{-1}e,g^{-1}).
 \tag{RFH.6}
\]

The first coordinate records where an execution is admitted.  The second records its reversible
history.  Formula `(RFH.5)` is not a direct product: the second support is transported before the
two domains are intersected.

### Theorem 2.1 -- restriction fusion

The following hold.

1. (S) is an inverse semigroup with inverse operation `(RFH.6)`.
2. Its idempotents are exactly
   
   \[
    E(S)=\{(e,1):e\in E\}.
    \tag{RFH.7}
   \]
3. Range support, source support, and reversible grade are
   
   \[
   \begin{aligned}
    r(e,g)&=(e,g)(e,g)^*=(e,1),\\
    d(e,g)&=(e,g)^*(e,g)=(g^{-1}e,1),\\
    \gamma(e,g)&=g.
   \end{aligned}
   \tag{RFH.8}
   \]
4. They obey the exact conservation laws
   
   \[
    \gamma(st)=\gamma(s)\gamma(t),
    \qquad
    r(st)=r(s)\wedge \gamma(s)r(t),
    \tag{RFH.9}
   \]
   where the second equation is read in (E\cong E(S)).
5. The pair ((r,\gamma)) jointly reconstructs every element:
   
   \[
    \boxed{(r(e,g),\gamma(e,g))=((e,1),g)\Longrightarrow(e,g).}
    \tag{RFH.10}
   \]

Neither observer is complete by itself whenever both (E) and (G) are nontrivial.

### Proof

Associativity follows from the action law and preservation of meets:

\[
\begin{aligned}
 ((e,g)(f,h))(k,l)
   &=(e\wedge gf\wedge ghk,ghl),\\
 (e,g)((f,h)(k,l))
   &=(e\wedge g(f\wedge hk),ghl)\\
   &=(e\wedge gf\wedge ghk,ghl).
\end{aligned}
\]

For (s=(e,g)), direct calculation gives

\[
 ss^*=(e,1),
 \qquad
 s^*s=(g^{-1}e,1),
 \qquad
 ss^*s=s,
 \qquad
 s^*ss^*=s^*.
\]

All elements ((e,1)) are idempotent and commute.  Conversely, if ((e,g)^2=(e,g)), then
(g^2=g), so (g=1).  Thus the displayed inverse is the unique inverse and `(RFH.7)` holds.
Equations `(RFH.8)`--`(RFH.10)` follow immediately from `(RFH.5)`. ∎

### Corollary 2.2 -- every group quotient erases native support

If (psi:S\to H) is any semigroup homomorphism to a group, then

\[
 \psi(e,1)=1_H
 \qquad(e\in E).
 \tag{RFH.11}
\]

Hence no group-valued quotient of the fused carrier is jointly faithful when (E) is nontrivial.

### Proof

Restrict (psi) to the idempotent semilattice `(RFH.7)` and apply Theorem 1.1. ∎

## 3. Canonical partial-isometry realization

Let

\[
 \mathcal H=\ell^2(E\times G)
 \tag{RFH.12}
\]

with standard basis (delta_{(a,k)}).  For (e\in E), let (P_e) be the coordinate projection
onto

\[
 \{(a,k):a\le e\},
 \tag{RFH.13}
\]

and for (g\in G), let

\[
 U_g\delta_{(a,k)}=\delta_{(ga,gk)}.
 \tag{RFH.14}
\]

The action preserves the order and (0), so (U_g) is unitary and

\[
 U_gP_eU_g^{-1}=P_{ge},
 \qquad
 P_eP_f=P_{e\wedge f}.
 \tag{RFH.15}
\]

Define

\[
 V_{e,g}=P_eU_g.
 \tag{RFH.16}
\]

### Theorem 3.1 -- faithful proper operator shadow

For all (s,t\in S):

1. (V_sV_t=V_{st}) and (V_s^*=V_{s^*});
2. (V_s) is a partial isometry with
   
   \[
    V_sV_s^*=P_{r(s)},
    \qquad
    V_s^*V_s=P_{d(s)};
    \tag{RFH.17}
   \]
3. (s\mapsto V_s) is injective;
4. distinct packets are uniformly separated:
   
   \[
    \boxed{s\ne t\Longrightarrow 1\le\|V_s-V_t\|\le2;}
    \tag{RFH.18}
   \]
   if (gamma(s)\negamma(t)), the lower bound improves to (sqrt2);
5. with (S) discrete and (B(\mathcal H)) carrying operator norm, (s\mapsto V_s) is a proper
   map onto its image.

### Proof

Using `(RFH.15)`,

\[
\begin{aligned}
 V_{e,g}V_{f,h}
   &=P_eU_gP_fU_h\\
   &=P_eP_{gf}U_{gh}\\
   &=P_{e\wedge gf}U_{gh}=V_{(e,g)(f,h)}.
\end{aligned}
\]

Also

\[
 V_{e,g}^*=U_{g^{-1}}P_e=P_{g^{-1}e}U_{g^{-1}}=V_{(e,g)^*}.
\]

This proves items 1 and 2.

For faithfulness, suppose (V_{e,g}=V_{f,h}).  Since (0\le e,f), applying both operators to
(delta_{(0,1)}) gives

\[
 \delta_{(0,g)}=\delta_{(0,h)},
\]

so (g=h).  Right multiplication by (U_g^{-1}) gives (P_e=P_f).  Since (e\in\downarrow e),
equality of the two principal downsets gives (e\le f); symmetrically (f\le e), hence (e=f).

If (g\ne h), the same test vector produces two orthogonal unit vectors, so

\[
 \|V_{e,g}-V_{f,h}\|\ge\sqrt2.
\]

If (g=h) but (e\ne f), the principal downsets differ.  Choose (a) in their symmetric
difference and put (v=U_g^{-1}\delta_{(a,1)}).  Exactly one of (P_eU_gv,P_fU_gv) is the unit
vector (delta_{(a,1)}), while the other is zero.  Thus the norm difference is at least one.
The upper bound two follows because every (V_s) is a contraction.

Finally, a compact subset of a metric space is totally bounded and therefore contains only
finitely many points of a (1)-separated subset.  By `(RFH.18)`, the inverse image of every compact
set is finite.  This is properness for the discrete source. ∎

The operator theorem is not an arbitrary linearization.  Range and source projections are exactly
the native support idempotents, while the unitary coordinate shift is exactly the reversible grade.

## 4. Information-neutral symmetries

Let (sigma_E:E\to E) be a semilattice automorphism and
(sigma_G:G\to G) a group automorphism satisfying

\[
 \sigma_E(ge)=\sigma_G(g)\sigma_E(e).
 \tag{RFH.19}
\]

Then

\[
 \sigma(e,g)=(\sigma_E(e),\sigma_G(g))
 \tag{RFH.20}
\]

is an inverse-semigroup automorphism.  The basis permutation

\[
 W_\sigma\delta_{(a,k)}
   =\delta_{(\sigma_E(a),\sigma_G(k))}
 \tag{RFH.21}
\]

is unitary and obeys

\[
 \boxed{W_\sigma V_sW_\sigma^{-1}=V_{\sigma(s)}.}
 \tag{RFH.22}
\]

Thus every compatible functional-equation involution acts isometrically on the fused packet.  It
transports support and history together; it neither creates support nor repairs a failed landing.

### Proof

Equation `(RFH.19)` makes `(RFH.20)` preserve `(RFH.5)` and `(RFH.6)`.  Equation `(RFH.21)` sends
the downset of (e) to the downset of (sigma_E(e)) and intertwines (U_g) with
(U_{\sigma_G(g)}).  Conjugating `(RFH.16)` gives `(RFH.22)`. ∎

## 5. Exact corpus fusion and fourth-organ prediction

The theorem fuses four independently present corpus organs.

| role | native datum | theorem shadow |
|---|---|---|
| source support | Frobenius-invariant generalized-divisor support | idempotent (e\in E) |
| pro history | finite Kummer/recurrence grade | invertible (g\in G) |
| formation/execution | transported domain intersection | inverse-semigroup product `(RFH.5)` |
| operator topology | projection plus reversible shift | partial isometry (P_eU_g) |

The corpus theorem `deningerSpecZFrobeniusColimitGeneralizedDivisor_eq_preimage` proves that the
actual `Spec Z` generalized divisor is a Frobenius-stable support subset.  Finite intersections of
such supports form (E).  The Kummer history supplies (G); its action on supports may be trivial,
while a functional equation may act nontrivially on both coordinates.

The withheld fourth-organ theorem forced by this fusion is `(RFH.18)`: after both native
coordinates are retained, any change of support or history produces a uniform operator-norm gap.
Neither the group observer nor the support observer alone can imply this.  Joint reconstruction
`(RFH.10)` and properness are consequences of one fused partial-symmetry carrier.

## 6. Consequence for the former group-like landing gate

The former ind--pro programme asked the native generalized-divisor support to produce one
group-like rational-Witt element.  If that comparison is required to respect native support
intersection, Theorem 1.1 proves that it is necessarily trivial.  Therefore it cannot carry local
divisor multiplicity or distinguish a nonempty support.

The correct next gate is not

> construct a group-like element from support,

but

> construct the literal Euler-shell packet as a restriction element whose range projection is the
> source generalized-divisor support and whose reversible grade is the already reconstructed
> Kummer history.

Even that construction would not prove RH: Theorem 2.1 reconstructs a packet; it does not force its
grade or support to be trivial.  Selection requires one further source law about the common
ind--pro fixed spectrum of the fused restriction packet.

## 7. Hostile boundaries

1. **Inverse semigroups are not new.**  Semidirect products of semilattices by groups, restriction
   semigroups, partial actions, étale groupoids, and their (C^*)-algebras are established parent
   mathematics.  This theorem is a `[BRIDGE]`; the research delta is the exact source-doctrine
   no-go and the replacement of group-like landing by a jointly faithful partial-symmetry packet.
2. **A pair is not automatically source-native.**  The literal source must independently generate
   both coordinates and their compatibility.  Declaring ((e,g)) by hand is theatre.
3. **Support intersection is not divisor addition.**  `(RFH.5)` models sequential admission and
   execution, not addition of Cartier or analytic divisors.
4. **Properness is norm-discrete, not compact generation.**  The theorem supplies a sharp global
   separation law.  It does not construct a locally compact groupoid or a physical action.
5. **Functional equation is neutral.**  Unitary conjugacy preserves all packet information and
   therefore cannot select a fixed locus by itself.
6. **No RH claim.**  The Euler-shell restriction-packet landing and its common fixed-spectrum law
   remain open.

## 8. Parent mathematics and priority boundary

Kudryavtseva, *Partial monoid actions and a class of restriction semigroups*,
[arXiv:1402.5849](https://arxiv.org/abs/1402.5849), treats restriction semigroups arising from
partial actions and identifies semidirect products of semilattices by groups as the inverse case.
Fujieda--Katsura--Uchimura, *A categorical approach to inverse semigroups, etale groupoids, and
their C*-algebras*, [arXiv:2410.20661](https://arxiv.org/abs/2410.20661), constructs the modern
functorial passage from inverse semigroup actions through transformation groupoids to groupoid
(C^*)-algebras.

Those theories supply the ambient machinery.  They do not identify the HGT generalized-divisor
support/Kummer-history doctrine mismatch or prove the source-specific replacement gate in Section
6.  No external novelty claim is made.

No Lean was written or built in this research pass.
