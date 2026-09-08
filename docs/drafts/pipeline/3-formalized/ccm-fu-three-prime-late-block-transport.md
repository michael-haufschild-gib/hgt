# CCM-FU: complete three-prime transport and intermediate successor budgets

- **Stage:** 3-formalized; scratch and exact-file checks, new-closure axiom audit and global formal lint passed. Lake packaging audit remains pending.
- **Proof chain:** Actual divisor source → renewable signed reserve → exhaustive prime selection → uniform signed Abel bound → RH.
- **Closed:** Exact full third interaction; its source sign; complete transport through isolated late-prime blocks; exact overlap-payment threshold; endpoint control of every intermediate successor envelope in those blocks.
- **Open:** Choosing admitted block endpoints, repair by nonisolated primes, exhaustive processing and a uniform every-cutoff bound. RH remains unproved.

## The full third interaction

Let F_P(R) be the existing literal signed selection fibre at cutoff M,
Q_P its full energy and K_d the original unsigned dilation channel. For
distinct unprocessed active primes p,q,r, define

D3(P;p,q,r)=Q_(P+p+q+r)-Q_(P+p+q)-Q_(P+p+r)-Q_(P+q+r)
             +Q_(P+p)+Q_(P+q)+Q_(P+r)-Q_P.

For every remaining label R free of p,q,r write a,b,c,d,e,f,g,h for the
fibres at R, R+p, R+q, R+r, R+p+q, R+p+r, R+q+r, R+p+q+r. Lean proves

D3(P;p,q,r)=2 sum_R(a*h+b*g+c*f+d*e).

This includes every retained label and all joint products. The third
interaction is what remains after the first and second energy changes
are retained in a prescribed-prime/repair/successor comparison.

At the original core, D3(empty;p,q,r)<=0. If the processed core consists
only of isolated late primes s with s<M<=2s, the same inequality holds
whenever p*q*r>=M, without assuming a nonnegative current head, current
energy bound or successful earlier prime order.

## Complete transport, including active overlaps

Let L be any unprocessed block of isolated late primes and let P be an
arbitrary starting core. The new primes p,q,r are outside L. Lean proves

D3(P+L;p,q,r)=D3(P;p,q,r)
 +2*(sum_(s in L) signedChannel_s)*F_P({p,q,r}).

The core P need not have retained parity or a nonnegative head. The
identity has no supplied reserve or analytic sign premise. The signed
block mass and the original retained triple fibre account for the
complete change; no term growing with the number of block steps is
discarded.

If p*q*r>=M, the retained triple fibre is zero by actual product support.
Thus any such late block leaves D3 exactly unchanged, for every starting
core. For a block starting at the original core, the identity becomes

D3(L;p,q,r)=D3(empty;p,q,r)
 +2*(sum_(s in L) K_s)*K_(p*q*r).

Consequently Lean gives the exact source condition

D3(L;p,q,r)<=0
 iff 2*(sum_(s in L) K_s)*K_(p*q*r)<=-D3(empty;p,q,r).

The right side is an independently defined, nonnegative original
third-order margin when the three primes are active. This identifies
precisely how much of that margin the consumed late mass spends in the
active-overlap sector. It does not assert the inequality holds for an
arbitrary block, or reject blocks paid by other reserve.

## No accumulated intermediate cost inside a late block

Let Psi(P)=max(Q_P,{Q_(P+q): q active and unprocessed}) be the existing
exact successor envelope. For every R subset L, Lean proves

Psi(P+R)<=max(Psi(P),Psi(P+L)).

Both the current energy and every remaining successor are included.
There is no nonnegative-head condition and no additive per-prime loss.
Thus two admitted endpoints suffice to keep every intermediate subset
admitted, in every order within this late-prime block. This completes
intermediate admission for this class of blocks; it neither selects an
admitted endpoint nor extends to nonisolated primes.

## Dependency-closed paper proofs

Subtract the existing p,q mixed energy difference at P from the same
difference at P+r. Split each sum into r-free and r-containing labels.
Insertion adds the two r partners to an r-free fibre and makes an
r-containing retained fibre zero. Expansion cancels the old terms,
leaving exactly the four complementary products above.

Every original fibre has sign (-1)^card(R). The cardinalities in each
complementary pair add to 2*card(R)+3, so each product is nonpositive.
This proves the original sign including active triple overlaps.

Product support makes h=0 whenever p*q*r>=M. Each remaining factor has
a nonempty retained label. The already proved source law for late-prime
blocks preserves the original parity of every such label, even if the
empty head changes sign. Thus every remaining complementary product is
nonpositive, proving the late-core sign statement.

For the complete transport, use the existing exact block-energy identity

Q_(C+L)=Q_C+2*F_C(empty)*S+S^2-sum_(s in L) signedChannel_s^2,

where S is the signed block mass. Apply it at all eight cores C formed
from P by p,q,r. All constant and singleton-square terms cancel in D3.
Three prime differences of the scalar head equal F_P({p,q,r}) exactly,
by three applications of the literal fibre insertion identity. This
proves the transport law for arbitrary P, including active joint support.

At P=empty, the signed block mass equals minus the unsigned mass, and
the retained triple fibre equals -K_(p*q*r). These signs follow from
actual prime Möbius coefficients and the existing unsigned-product
identification, not a numerical evaluation. Substitution gives the full
unsigned law; rearranging gives the exact margin condition.

For the envelope theorem, the existing actual-energy endpoint theorem
already bounds Q_(P+R). For a successor q outside L, apply that same
theorem at the starting core P+q. Its two endpoint energies occur in
Psi(P) and Psi(P+L). For q in L but not yet R, apply the original
endpoint theorem to R+q. These two cases exhaust every available
successor, proving the displayed Psi bound.

## Lean implementation and validation

- `MobiusDivisorThirdEnergyInteraction.lean`: one definition and seven public theorems.
- `MobiusDivisorLateBlockSuccessorEnvelope.lean`: one public theorem.

Both leaves passed foreground `lake env lean` scratch checks and exact
source-file checks with only their own olean emission. One external
audit of the nine new declaration closures found only propext,
Classical.choice and Quot.sound; no old declaration was re-audited.
Global formal lint and scoped whitespace checks passed. Imports are
wired into RHTower. No umbrella or old prerequisite was rebuilt. Lake
packaging remains pending because its prerequisite graph would trigger
a broad stale rebuild. No numerical experiment or computational proof
premise was used.

## Exact remaining repair obligation

The complete third term is now explicit, and its renewal through late
blocks is exact. The full repair still must choose a prime so that every
successor's sum of first, second and third changes fits the original
budget. The positive envelope endpoint law removes intermediate loss
inside late blocks but supplies no admitted endpoint. Any argument
that also processes small, nonisolated primes must track their changes
to the triple fibre and the lower-order reserves. None of these missing
source comparisons is assumed as a theorem premise or claimed solved.
