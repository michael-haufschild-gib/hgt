# Exterior elimination forces a positive Feshbach self-energy on Suzuki's pruned seam

- **ID:** `suzuki-exterior-feshbach-pruning-law`
- **Stage:** 3-formalized
- **Type:** SOURCE-SPECIFIC EXACT CLASSIFICATION / CARRIER CORRECTION
- **Scientific status:** `[PROVED HERE] [NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** Connes/CCM restricted-Weil form through Suzuki completed zero modes
- **Inputs:** `suzuki-exterior-residual-rigged-wiener-realization.md`,
  `suzuki-support-pruned-selfadjoint-seam-carrier.md`
- **Primary source:** M. Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096v1, formulas (2.6)--(2.8)

## 1. Result and correction

The exact global valuation-Wiener carrier cannot be sent to Suzuki's strict-interior carrier by
merely compressing the prime adjacency:

```text
full inverse -> P_S (alpha I+T)^(-1) P_S
```

is not the inverse of

```text
alpha P_S+P_S T P_S.                                    (1)
```

Every prime word that leaves the aperture and later returns is deleted by `(1)` but remains in the
global inverse.  Exact exterior elimination restores all such words as a Feshbach self-energy.

Let \(X_p=\ell^p(V)\), \(p=1\) or \(2\), let \(P\) be coordinate restriction to a set
\(S\subset V\), put \(Q=I-P\), and let \(T\in\mathcal B(X_p)\).  For real
\(\alpha>\|T\|\), define on \(QX_p\)

```text
D_alpha=alpha I_Q+Q T Q,

Sigma_alpha=P T Q D_alpha^(-1) Q T P.                  (2)
```

If \(f\in QX_p\) and

```text
(alpha I+T)c=f,                                         (3)
```

then the interior and exterior components satisfy the exact equations

```text
[alpha P+P T P-Sigma_alpha]P c
  =-P T Q D_alpha^(-1)f,                                (4)

Q c=D_alpha^(-1)[f-Q T P c].                            (5)
```

Moreover,

```text
||D_alpha^(-1)|| <=1/(alpha-||T||),

||Sigma_alpha||
 <=||T||^2/(alpha-||T||),                               (6)

||P T Q D_alpha^(-1)f||
 <=||T||/(alpha-||T||)||f||.                            (7)
```

On \(\ell^2\), if \(T=T^*\), then

```text
Sigma_alpha=Sigma_alpha^* >=0.                          (8)
```

For Suzuki's visible-prime adjacency the correction is strictly nonzero as soon as at least one
prime power is visible.  Thus the formerly proposed literal intertwiner with only
\(P_S T P_S\) is false.  The strongest correct survivor is the exact pruned carrier

```text
support-pruned adjacency - positive exterior self-energy
```

with a simultaneously renormalized two-port source.

## 2. Banach-space proof

Coordinate projections have norm at most one on both \(\ell^1\) and \(\ell^2\).  On \(QX_p\),

```text
D_alpha
 =alpha[I_Q+alpha^(-1)Q T Q].
```

Since \(\|QTQ\|\leq\|T\|<\alpha\), the Neumann series converges in operator norm:

```text
D_alpha^(-1)
 =alpha^(-1) sum_(k>=0)(-alpha^(-1)Q T Q)^k.            (9)
```

Its geometric majorant proves the first estimate in `(6)`.

Apply \(P\) and \(Q\) to `(3)`.  The scalar part has no mixed blocks, hence

```text
(alpha P+P T P)P c+P T Q Q c=0,                        (10)

Q T P P c+D_alpha Q c=f.                               (11)
```

Solving `(11)` gives `(5)`.  Substitution in `(10)` gives `(4)` with `(2)`.  The remaining norm
bounds follow from

```text
||P T Q||<=||T||,       ||Q T P||<=||T||.               (12)
```

No invertibility of the effective interior operator is assumed in this derivation.  If the full
inverse is used instead, `(4)` is exactly the usual block inverse identity

```text
P(alpha I+T)^(-1)P
 =[alpha P+P T P-Sigma_alpha]^(-1)                     (13)
```

on \(PX_p\).

## 3. Exact excursion expansion

Insert `(9)` into `(2)`:

```text
Sigma_alpha
 =sum_(k>=0)(-1)^k alpha^(-k-1)
    P T Q (Q T Q)^k Q T P.                             (14)
```

Every summand in `(14)` has the following path meaning:

```text
interior
 -> one step to exterior
 -> k steps staying exterior
 -> one step back to interior.                          (15)
```

The \(Q\) between every two steps is decisive.  Therefore `(14)` restores exactly all
leave--stay-outside--return words and no others.  Likewise the effective source is

```text
-P T Q D_alpha^(-1)f
 =sum_(k>=0)(-1)^(k+1)alpha^(-k-1)
    P T Q(Q T Q)^k f,                                  (16)
```

which is the exact sum of paths that start at an exterior endpoint, remain exterior for \(k\)
steps, and enter the aperture for the first time.

Equations `(14)` and `(16)` are the missing global-to-pruned classification.  They show that
support pruning is compatible with the global carrier only after exterior returns and exterior
source propagation are retained.

## 4. Hilbert sign

Now take \(p=2\), assume \(T=T^*\), and use the orthogonal decomposition

```text
X_2=PX_2 direct-sum QX_2.
```

For \(y\in QX_2\),

```text
<D_alpha y,y>
 =alpha||y||^2+<T y,y>
 >=(alpha-||T||)||y||^2.                               (17)
```

Thus \(D_\alpha\) is strictly positive, its inverse is strictly positive, and

```text
Q T P=(P T Q)^*.
```

Consequently, for \(x\in PX_2\),

```text
<Sigma_alpha x,x>
 =<D_alpha^(-1)Q T P x,Q T P x>
 >=0.                                                   (18)
```

This proves `(8)`.  Since also

```text
D_alpha <=(alpha+||T||)I_Q,
```

functional calculus gives the useful lower estimate

```text
<Sigma_alpha x,x>
 >=||Q T P x||^2/(alpha+||T||).                         (19)
```

The sign is therefore not an artifact of a norm bound: exterior elimination always subtracts a
positive operator from the strict-interior block.

## 5. Suzuki specialization

Fix \(a>0\).  On the oriented valuation carrier let

```text
T=A_a^prime
 =-sum_(p^j<=exp(2a)) w_(p,j)
   [U_(j e_p)+U_(-j e_p)],

w_(p,j)=(log p)/p^(j/2)>0,                              (20)

P=P_a^S,       Q=I-P,

M_a=2 sum_(p^j<=exp(2a)) w_(p,j).                       (21)
```

Then \(T=T^*\) on \(\ell^2\) and \(\|T\|\leq M_a\) on both \(\ell^1\) and \(\ell^2\).
Suzuki's exact multiplier split supplies

```text
alpha_a(xi)=log<xi>+q_a(xi),                            (22)
```

where \(q_a\) is real and bounded.  Choose \(\Xi_a\) so that

```text
alpha_a(xi)>M_a       for |xi|>=Xi_a.                   (23)
```

The two root vectors are exterior because their physical positions are the two endpoints:

```text
P e_(left,0)=P e_(right,0)=0.                           (24)
```

For the completed exterior Hardy source

```text
f(xi)
 =exp(+iaxi)B_-(xi)e_(left,0)
  +exp(-iaxi)B_+(xi)e_(right,0),                        (25)
```

the high-frequency global Wiener carrier \(c(\xi)\) from the predecessor theorem obeys `(3)`
with \(\alpha=\alpha_a(\xi)\).  Hence its exact strict-interior component obeys

```text
[alpha_a P+P T P-Sigma_a(xi)]P c(xi)=j_a(xi),           (26)

j_a(xi)=-P T QD_a(xi)^(-1)f(xi).                       (27)
```

The bounds are

```text
||Sigma_a(xi)||_1, ||Sigma_a(xi)||_2
 <=M_a^2/[alpha_a(xi)-M_a],                             (28)

||j_a(xi)||_1
 <=M_a/[alpha_a(xi)-M_a]
   [|B_-(xi)|+|B_+(xi)|].                               (29)
```

Since \(B_\pm\in L^2(\mathbb R)\), equation `(29)` proves that the renormalized interior source is
in high-frequency \(L^2(\ell^1)\), hence in \(L^2(\ell^2)\).  Equation `(28)` says

```text
||Sigma_a(xi)||=O(1/log|xi|).                           (30)
```

This is a genuine lower-order correction, but it is not zero.

## 6. Strict nonvanishing at every nontrivial aperture

Assume \(p^j\leq e^{2a}\) for some prime power.  Let

```text
delta=j e_p,
v=(left,delta).                                         (31)
```

Its location is

```text
x(v)=-a+j log p,
```

which lies strictly in \((-a,a)\) because \(0<j\log p\leq2a\); at equality it is the opposite
endpoint and one may instead choose any strictly visible prime power.  Thus, whenever a strictly
visible prime power exists, \(v\in S_a\).  The exterior component of \(Tv\) has endpoint
coordinate

```text
(Q T P e_v)(left,0)=-w_(p,j).                           (32)
```

No other prime-power step reaches that coordinate, by unique factorization.  Hence

```text
||Q T P e_v||>=w_(p,j),                                 (33)
```

and `(19)` gives

```text
<Sigma_a(xi)e_v,e_v>
 >=w_(p,j)^2/[alpha_a(xi)+||T||] >0.                    (34)
```

At an aperture where a prime power lies exactly at the opposite endpoint but no prime power is
strictly visible, the strict-interior prime carrier is empty and there is no interior block to
correct.  Therefore every nonempty Suzuki strict-interior prime sector has a nonzero positive
self-energy.

## 7. What this closes—and what it does not

This theorem closes the original-Fourier algebraic half of
`SUZUKI-RIGGED-CARRIER-INTERTWINER`:

```text
global ell1 Wiener carrier in xi
 -> exact strict-interior ell1 subset ell2 carrier in xi
 -> exact classification of all deleted-return paths.   (35)
```

It also falsifies the proposed homogeneous equation with only the compressed adjacency
\(P T P\).  The correct local equation contains \(-\Sigma_a(D)\) and the effective exterior
source \(j_a\).  With the Gamma-normalized positive adjacency
\(T_a^\Gamma=-A_a^{\rm prime}\), the interior block in `(26)` is
\(\alpha_aP-PT_a^\Gamma P-\Sigma_a\), retaining Suzuki's literal prime sign.  Since
\(\Sigma_a(\xi)\) is self-adjoint and positive on the physical line, its original-\(x\) Fourier
multiplier is bounded self-adjoint on the high-frequency Hilbert carrier.

This is not yet the logarithmic boundary operator used in the Gamma theorems.  The change

```text
r=distance to an oriented seam,       L=-log r
```

is nonlinear.  A translation-invariant multiplier in the original coordinate \(x\) does not
remain the same translation-invariant multiplier in \(L\).  Writing \(\mathcal U\) for the
unitary boundary-log chart, the actual correction is

```text
S_a^log=U Sigma_a(D_x) U^(-1),                           (36)
```

whose kernel contains the nonlinear difference
\(e^{-L}-e^{-M}\) and the chart Jacobian.  Replacing `(36)` by
\(\Sigma_a(D_L)\) would be a second false intertwiner.

Applying the existing Gamma-current and weighted-tail theorems therefore requires one more exact
source theorem:

```text
FESHBACH-LOG CONJUGATION:
compute (36) in every oriented seam chart,
extract its bounded self-adjoint Mellin-leading part,
and prove its remainder, cutoff commutator, and renormalized
exterior source lie in the physical block/weighted L2 class.              (37)
```

Bound `(30)` alone does not prove `(37)`: inverse-log symbol decay is not a Mellin kernel theorem,
and a bounded decaying multiplier need not have a controlled commutator after nonlinear boundary
straightening.  The source formula `(14)`, the regularity of \(\alpha_a\), and the exact chart
Jacobians must be used.  Low frequencies, where \(D_a(\xi)\) can fail to be invertible, remain in
the two-port return problem and may carry the RH content.

There is now an exact positive alternative to this elimination path.
`suzuki-root-retained-exterior-dilation.md` keeps \(Q\), including both endpoint roots, through the
physical Gamma normal equation and projects only afterward.  If the half-log trace lies in \(Q\),
then the strict-interior component lies in unweighted boundary-log
`H1(dL) intersect L2(dL)` and satisfies

```text
(2L I+R-P T P)(P F)'+P F=P T Q(Q F)',
```

with the retained exterior source in `L2(dL)`.  This is not spatial `H1(dr)`, which requires an
exponentially weighted derivative.  Every leave-and-return word remains in the powers
\(T^k\); no Feshbach term is deleted.  Thus `(37)` remains the correct problem **if exterior
coordinates are eliminated**, but it is no longer a necessary Route-O gate.  Root retention is
the stronger completion-safe survivor.

## 8. Hostile audit

1. **No compressed-inverse substitution.**  Equation `(13)` includes the self-energy; deleting it
   is false whenever `(34)` holds.
2. **No small-equals-zero argument.**  The correction is \(O(1/\log|\xi|)\), not absent.
3. **No sign guess.**  Positivity follows from the exact factorization
   \(\Sigma=(PTQ)D^{-1}(PTQ)^*\).
4. **No Fourier/Mellin conflation.**  The original-\(x\) multiplier must be conjugated by the
   nonlinear boundary-log chart before any Gamma theorem applies.
5. **No `ell2` evaluation.**  All scalar phase reconstruction remains on the `ell1` rigging.
6. **No global division at zeros.**  Exterior inversion is used only under `(23)`.
7. **No RH claim.**  `(37)`, nonzero-trace corona return, raw Evans injectivity, and whole-route
   producer classes P and I remain open.

## 9. Novelty boundary and external audit

Schur complements and Feshbach maps are classical.  No novelty is claimed for Sections 2--4 in
isolation.  Corpus search and a targeted external search of Suzuki's source, Connes--Consani
compression/prolate work, and Feshbach--Schur references found no prior identification of:

```text
Suzuki global valuation-Wiener inverse
 -> strict-aperture prime-word pruning
 -> positive exterior-return self-energy
 -> exact two-port source renormalization
 -> unavoidable pre-Gamma boundary-log conjugation problem.              (38)
```

The new claim is the source-specific classification `(26)`--`(38)` and the resulting correction
of the Route-O frontier.  Priority remains unverified.

## 10. Lean certificate

The dependency-closed operator content is formalized unconditionally in

```text
formal/GaloisForLFunctions/RHTower/
  SuzukiExteriorFeshbachPruning.lean
```

It proves:

```text
feshbach_eliminate_exterior
feshbachGramSelfEnergy_isPositive
suzukiExteriorReturnGramSelfEnergy_isPositive
```

The last theorem exposes Suzuki's actual strict-interior coordinate projection, exterior
complement, and finite prime adjacency; `Droot` is the square-root factor of the positive exterior
inverse.  The same formal wave also adds the sign-correct
`suzukiGammaPositivePrimeAdjacency=-suzukiSupportPrunedPrimeAdjacency` and proves its
self-adjointness.

The infinite Neumann norm bound and strict source nonvanishing remain paper mathematics because
the formal tree does not yet contain the exterior resolvent on the restricted carrier.  The
analytic Feshbach--log conjugation `(37)` remains paper-open and does not appear in Lean as a
hypothesis disguised as a source realization.

## Gates

- [x] derive exact global-to-pruned block equations
- [x] classify every exterior leave/return word
- [x] prove sharp high-frequency operator bounds
- [x] prove positive sign on the Hilbert carrier
- [x] prove strict nonvanishing on every nonempty Suzuki prime sector
- [x] preserve `ell1 subset ell2` rigging and `L2` effective source
- [x] formalize exact two-block elimination and positive Suzuki Gram self-energy
- [x] formalize Gamma-normalized prime-adjacency sign
- [x] construct root-retained self-adjoint dilation bypassing pre-log exterior elimination
- [x] prove its strict-interior projection and exact exterior source are physical `H1`/`L2`
- [ ] prove exact boundary-log conjugation of the Feshbach correction
- [ ] prove its Gamma cutoff commutator regularity
- [ ] close trace-zero completed carrier equation
- [ ] prove corona no-return and raw Evans injectivity
- [ ] RH
