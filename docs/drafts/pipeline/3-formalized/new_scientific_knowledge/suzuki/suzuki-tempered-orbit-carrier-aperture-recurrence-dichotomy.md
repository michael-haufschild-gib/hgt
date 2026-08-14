# A tempered nonselfadjoint Suzuki orbit carrier exists exactly below the aperture-recurrence barrier

- **ID:** `suzuki-tempered-orbit-carrier-aperture-recurrence-dichotomy`
- **Stage:** 3 — formalized in Lean 4
- **Type:** EXACT POSITIVE CARRIER / SHARP SMALL-DIVISOR CLASSIFICATION
- **Scientific status:** `[PAPER-PROVED] [UNCONDITIONAL] [NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** completed Evans/logarithmic-seam branch of Connes/CCM
- **Inputs:** `suzuki-localized-orbit-lift-selfadjointness-trilemma.md`,
  `suzuki-two-port-return-redundancy-and-interior-null-core.md`,
  `suzuki-gamma-weighted-tail-coercivity.md`

## 0. Scope correction after nonnormal Hardy audit

The carrier, root reconstruction, weighted-shift bounds, event summability, and terminal derivative
coercivity in this card remain proved. The claim that bounded nonnormal transport is sufficient for
the **preceding shifted-\(L^2\) Hardy step** was not proved: its frequency propagator contains
\(\exp(-ixT_{a,\rho}/2)\), whose norm need not have polynomial growth.

The radial exponential carrier has a Hatano--Nelson limit spectrum, so finite exponential
recurrence is not the sharp Hardy-admission class. The corrected classifier is
`suzuki-log-recurrence-polynomial-carrier-trichotomy.md`:

```text
finite logarithmic recurrence
 -> polynomial carrier + polynomial prime group;         [PAPER-PROVED]

finite exponential recurrence only
 -> event summability, but nonnormal dichotomy remains.  [OPEN]
```

## 1. Result

The bounded/covariant/self-adjoint orbit-lift trilemma does not force use of the delocalized Wiener
relation.  Physical translated profiles have an exact bounded Hilbert carrier after one gives up
ordinary self-adjointness of the weighted prime adjacency.  The resulting adjacency is bounded,
nonnormal, and still sufficient for the terminal \(2L\) numerical-range estimate.

Let \(P_a\) be the finite set of visible primes and put

```text
G_a=Z^(P_a),
ell(nu)=sum_p nu_p log p,
|nu|_1=sum_p |nu_p|.                                    (1)
```

For \(0<rho<1\), define

```text
w_rho(nu)=rho^(|nu|_1),
(J_rho u)_nu=w_rho(nu) U_nu u,
(U_nu u)(x)=u(x-ell(nu)).                               (2)
```

Then:

1. \(w_\rho\in\ell^2(G_a)\), \(J_\rho\) is bounded, and

   ```text
   ||J_rho u||_(ell2(L2))=||w_rho||_2 ||u||_2;          (3)
   ```

2. root projection is a bounded exact reconstruction:

   ```text
   (J_rho u)_0=u;                                       (4)
   ```

3. every visible prime translation intertwines exactly with a weighted coordinate shift, and the
   complete prime adjacency becomes a bounded operator \(T_{a,\rho}\);
4. \(T_{a,\rho}\) is generally nonselfadjoint, as required by the trilemma, but

   ```text
   |Re <T_(a,rho)z,z>|
   <=||T_(a,rho)|| ||z||^2,                             (5)
   ```

   so multiplication by \(2L\) absorbs it on a sufficiently terminal ray exactly as in the
   self-adjoint energy proof.

Thus bounded analysis, exact physical localization, exact prime intertwining, and bounded root
reconstruction coexist.  Ordinary self-adjointness is the dispensable corner of the former
trilemma.

There is one sharp obstruction to using this carrier uniformly at every aperture.  Define the
nonresonant prime-log recurrence exponent

```text
R(a)
 =limsup_(|nu|_1->infinity, ell(nu)!=2a)
    [-log |2a-ell(nu)|]_+ / |nu|_1.                    (6)
```

If \(R(a)<\infty\), then for every \(0<\sigma<1\) one can choose
\(\rho=e^{-\kappa}\) with

```text
kappa>sigma R(a)                                        (7)
```

so all weighted near-opposite-end activations are square summable in the physical Gamma weight
\(e^{\sigma L}\).

This finite-type class has full Lebesgue measure; in fact \(R(a)=0\) for almost every aperture.
But apertures with \(R(a)=\infty\) are dense.  At each such relative-Liouville aperture, every
orbit weight whose ratios across prime generators are uniformly bounded below has too little
decay to control all near-endpoint activations in any positive Gamma strip.

The exact frontier is therefore:

```text
finite recurrence type:
  bounded localized nonselfadjoint carrier survives;    [POSITIVE]

relative-Liouville type:
  every tempered weighted orbit carrier fails the
  required Gamma-strip boundary summation;               [NO-GO FOR THIS CLASS]

all-aperture Suzuki theorem:
  needs continuity/closed-graph passage across the
  exceptional set, or a genuinely nontempered relation. [OPEN]                 (8)
```

## 2. Square-summability and bounded root reconstruction

Because \(P_a\) is finite,

```text
sum_(nu in G_a) rho^(2|nu|_1)
 =product_(p in P_a)
   [sum_(m in Z)rho^(2|m|)]
 =[(1+rho^2)/(1-rho^2)]^(#P_a)<infinity.                (9)
```

Unitarity of every physical translation gives

```text
sum_nu ||w_rho(nu)U_nu u||_2^2
 =||u||_2^2 sum_nu w_rho(nu)^2,                         (10)
```

which proves `(3)`.  Since \(w_\rho(0)=1\), coordinate zero gives `(4)`.  Unlike unit-phase
codiagonal evaluation, root projection has norm one on \(\ell^2(G_a;L^2)\).

The same construction works pointwise for bounded completed modes:

```text
sum_nu ||w_rho(nu)U_nu u||_infinity^2
 =||w_rho||_2^2||u||_infinity^2.                        (11)
```

Thus no completed-domain summability is assumed.

## 3. Exact weighted prime intertwining

For a valuation step \(s\in G_a\), let

```text
(S_s z)_nu=z_(nu+s).                                    (12)
```

Coordinatewise,

```text
(J_rho U_s u)_nu
 =w_rho(nu)U_(nu+s)u
 =[w_rho(nu)/w_rho(nu+s)](S_s J_rho u)_nu.             (13)
```

Define

```text
(S_(s,rho)z)_nu
 =[w_rho(nu)/w_rho(nu+s)]z_(nu+s).                     (14)
```

Then `(13)` is the exact intertwining law

```text
J_rho U_s=S_(s,rho)J_rho.                              (15)
```

The triangle inequality for \(\ell^1\)-length gives

```text
||nu+s|_1-|nu|_1|<=|s|_1,
rho^|s|_1
 <=w_rho(nu)/w_rho(nu+s)
 <=rho^(-|s|_1).                                        (16)
```

Since an unweighted coordinate translation is unitary,

```text
||S_(s,rho)||<=rho^(-|s|_1).                            (17)
```

Write Suzuki's finite symmetric prime part as

```text
T_a=sum_(s in Sigma_a)c_s U_s,                          (18)
```

where \(\Sigma_a\) contains the visible \(\pm j e_p\).  Equations `(15)`--`(17)` give

```text
J_rho T_a=T_(a,rho)J_rho,
T_(a,rho)=sum_s c_s S_(s,rho),

||T_(a,rho)||
 <=sum_s |c_s|rho^(-|s|_1)<infinity.                    (19)
```

This is exact; no Feshbach deletion or orbit approximation occurs.

The adjoint of \(S_{s,\rho}\) has the reciprocal edge ratio, so \(T_{a,\rho}\) is ordinarily
self-adjoint only when the weight has constant modulus along every active edge.  That is precisely
the impossible case classified by the predecessor trilemma.  Here self-adjointness is not
asserted.

## 4. Nonnormality does not obstruct terminal Gamma coercivity

For every bounded operator \(B\) on a Hilbert space,

```text
|Re <Bz,z>|<=||B|| ||z||^2.                             (20)
```

The shifted Gamma multiplier has the lower numerical-range bound

```text
Re <R_sigma z,z>>=-kappa_sigma||z||^2.                  (21)
```

Consequently

```text
Re <(2L+R_sigma-T_(a,rho))z,z>
 >=[2L-kappa_sigma-||T_(a,rho)||]||z||^2.               (22)
```

After increasing the terminal cutoff, the bracket is positive.  Every weak-mollifier step in the
weighted-tail proof uses only `(22)`, boundedness of the coupling, and the Gamma lower bound.
Self-adjointness of \(T\) is not load-bearing there.

This corrects only the terminal derivative estimate: ordinary \(\ell^2\) self-adjointness is not
needed once shifted \(L^2\) is known. It does not remove the nonnormal shifted-\(L^2\) Hardy gate.

## 5. Finite recurrence type gives weighted endpoint summability

Near an opposite-end collision, valuation \(\nu\) has physical distance

```text
delta_nu=|2a-ell(nu)|,
L_nu=-log delta_nu.                                     (23)
```

Exact resonances \(\delta_\nu=0\) are separated as finitely labelled oriented root ports and are
omitted from `(6)`.  Suppose \(R(a)<\infty\).  For every \(\epsilon>0\), all sufficiently large
\(\nu\) satisfy

```text
L_nu<=[R(a)+epsilon]|nu|_1.                             (24)
```

With \(\rho=e^{-\kappa}\),

```text
e^(sigma L_nu)w_rho(nu)
 <=exp(-[kappa-sigma(R(a)+epsilon)]|nu|_1).             (25)
```

Choose \(\epsilon\) so the bracket is positive.  The number of lattice points with
\(|\nu|_1=N\) is \(O_a((1+N)^{d-1})\), where \(d=\#P_a\).  Squaring `(25)` and summing over \(N\)
therefore proves

```text
sum_(nu:delta_nu!=0)
 e^(2sigma L_nu)w_rho(nu)^2<infinity.                   (26)
```

The same estimate remains true after multiplication by any fixed inverse-log grade or polynomial
in \(L_\nu\).  Hence every finite-grade boundary activation and every exponentially localized
Gamma commutator enters the weighted orbit carrier at finite recurrence type.

Equation `(26)` is an admission theorem, not the completed zero-mode theorem.  One must still
derive the exact vector boundary-log equation and prove that its trace is supported only on the
two oriented roots.

## 6. Almost every aperture has recurrence exponent zero

Fix a bounded aperture interval \(K\), a constant \(c>0\), and lattice length \(N\).  For each
\(\nu\) with \(|\nu|_1=N\), the set

```text
{a in K:0<|2a-ell(nu)|<exp(-cN)}
```

has length at most \(e^{-cN}\).  There are \(O_a((1+N)^{d-1})\) such \(\nu\), so

```text
sum_N measure{
  a in K: exists |nu|_1=N,
  0<|2a-ell(nu)|<exp(-cN)}
 <infinity.                                             (27)
```

Borel--Cantelli implies that almost every \(a\in K\) has only finitely many such approximations.
Intersect over positive rational \(c\).  For almost every \(a\),

```text
[-log|2a-ell(nu)|]_+/|nu|_1 ->0 along the limsup,
```

which is \(R(a)=0\).  Exhausting the positive half-line by bounded \(K\) proves the full-measure
claim. `QED`

## 7. Dense relative-Liouville apertures and the sharp tempered no-go

The prime-log group is dense as soon as two visible primes are present.  Let \(\Gamma=\ell(G_a)\).
Every open aperture interval contains \(a\) and distinct \(\nu_n\) with

```text
0<|2a-ell(nu_n)|<exp(-|nu_n|_1^2).                     (28)
```

To construct one, work in twice the chosen interval.  Recursively choose a point
\(\gamma_n=\ell(\nu_n)\in\Gamma\) inside the preceding open interval, then choose a nested open
interval around \(\gamma_n\) of radius smaller than
\(\exp(-|\nu_n|_1^2)\), one quarter of the preceding radius, and avoiding the first \(n\)
enumerated points of \(\Gamma\).  Density supplies the next center.  The nested closures have one
limit \(\theta\notin\Gamma\), and \(\theta=2a\) satisfies `(28)`.  Since the initial interval was
arbitrary, these apertures are dense.  Equation `(28)` gives \(R(a)=\infty\).

Now let \(w:G_a\to(0,\infty)\) be any tempered orbit weight with \(w(0)>0\) and uniformly bounded
inverse edge ratios:

```text
w(nu)/w(nu+s)>=C^(-1)
for every active unit generator s.                      (29)
```

Iteration along a shortest word gives

```text
w(nu)>=w(0)C^(-|nu|_1).                                 (30)
```

At the approximants `(28)`, for every \(\sigma>0\),

```text
e^(sigma L_n)w(nu_n)
 >w(0)exp(sigma|nu_n|_1^2-|nu_n|_1 log C)
 ->infinity.                                            (31)
```

Thus no estimate based on a bounded weighted adjacency can put all such activations in a positive
Gamma strip.  This is sharp against `(25)`: finite exponential recurrence is exactly what an
exponentially tempered orbit metric can absorb.

## 8. Correct source conjecture

The positive carrier suggests a new, strictly more concrete connector.

### `SUZUKI-TEMPERED-ORBIT-NORMAL-IDENTITY`

For every aperture with \(R(a)<\infty\), lift a completed zero mode by `(2)`, retain exact
resonances as two oriented root ports, subtract the coordinatewise physical limits, and prove:

1. the resulting boundary-log vector lies in the weighted orbit Hilbert space;
2. it satisfies the literal Gamma normal equation with bounded coupling \(T_{a,\rho}\);
3. its half-log trace is supported only on the two physical roots;
4. the low port and polar term belong to the weighted source block.

If both physical traces vanish, `(22)` then gives the weighted derivative with
\(\sigma>1/2\), hence \(H^1_0\).

This conjecture is stronger than a generic carrier assertion and weaker than RH.  It has an exact
falsifier: an independent half-log trace at an interior orbit coordinate or a coordinatewise
cutoff source violating `(26)`.

For \(R(a)=\infty\), either pass the supported nullspace theorem by closed-graph/continuity from
finite-type apertures, or use a nontempered relation.  Pretending that one fixed weighted Hilbert
carrier works at all apertures is now ruled out.

## 9. Hostile audit

1. **No self-adjointness claim.** The carrier intentionally chooses the nonnormal corner allowed
   by the trilemma; its Hardy consequence is now explicitly separated.
2. **No illegal evaluation.**  Reconstruction is coordinate-zero projection, not infinite
   codiagonal summation.
3. **No covariance theatre.**  Equation `(15)` is exact intertwining with the actual conjugated
   adjacency.
4. **No all-aperture claim.**  Dense relative-Liouville apertures are proved and isolated.
5. **No trace propagation claim.**  Root support of the vector half-log trace remains the hard
   source identity.
6. **No RH claim.**  Even the normal identity leaves nonzero-trace Evans return and raw Evans
   injectivity.

## 10. Novelty boundary

Weighted orbit representations, Borel--Cantelli, and Liouville constructions are classical
separately.  Candidate-new source knowledge is their exact conjunction for Suzuki:

```text
give up ordinary seam self-adjointness
 -> exact bounded physical orbit carrier with root reconstruction;

prime-log recurrence exponent
 -> sharp admission boundary for physical Gamma weights;

finite type full measure / Liouville type dense
 -> precise exceptional-aperture structure of the remaining connector.       (32)
```

Corpus search found no previous Suzuki carrier organized by `(6)` or the dichotomy `(8)`.
External priority remains unaudited.

## 11. Lean status

Formalized unconditionally:

```text
formal/GaloisForLFunctions/RHTower/SuzukiOrbitWeightSummability.lean
formal/GaloisForLFunctions/RHTower/SuzukiOrbitCarrier.lean
formal/GaloisForLFunctions/RHTower/SuzukiApertureRecurrence.lean
formal/GaloisForLFunctions/RHTower/SuzukiApertureAlmostEvery.lean
formal/GaloisForLFunctions/RHTower/SuzukiLiouvilleAperture.lean
```

`(1)`--`(2)` are `orbitLength`, `orbitWeight`, `orbitTranslate`; `(9)` is `tsum_orbitWeight_sq`
(exact mass `((1+ρ²)/(1-ρ²))^{#P}`, computed through `ℝ≥0∞` where the coordinate split is
unconditional); `(3)`, `(10)`, `(11)` are `tsum_sq_orbitLift` and `tsum_sq_orbitLift_const`;
`(4)` is `orbitTranslate_zero`; `(12)`--`(15)` are `orbitShiftRatio` and `orbitLift_translate`;
`(16)`--`(19)` are `abs_orbitShiftRatio_le`, `tsum_sq_orbitWeightedShift_le` and its `E`-form;
`(5)`, `(20)`--`(22)` are `abs_re_inner_le_norm_mul_sq` and `re_inner_terminal_le`;
`(23)`--`(26)` are `apertureDefect`, `apertureDepth`, `weighted_activation_le`,
`summable_weighted_apertureActivation` and its graded form; `(27)` is `ae_finite_apertureApprox`
(Borel–Cantelli against the `(2N+1)^{#P} e^{-cN}` majorant); `(28)` is `dense_liouvilleApertures`
(Baire, from density of the displacement range); `(29)`--`(30)` are `weight_ge_of_edge_bound`;
`(31)` is `liouville_activation_unbounded`.  Every theorem audits to
`[propext, Classical.choice, Quot.sound]`.

## Gates

- [x] construct square-summable exponential valuation weights
- [x] prove bounded physical orbit analysis and root reconstruction
- [x] prove exact weighted prime intertwining
- [x] bound the complete nonnormal prime adjacency
- [x] prove terminal Gamma coercivity needs boundedness, not self-adjointness
- [x] retract boundedness as sufficient for nonnormal shifted-\(L^2\) Hardy transfer
- [x] define exact aperture recurrence exponent
- [x] prove finite recurrence type implies weighted endpoint summability
- [x] prove recurrence exponent zero for almost every aperture
- [x] construct dense relative-Liouville apertures
- [x] prove class-complete no-go for tempered weights there
- [x] formalize `(1)`--`(5)`, `(9)`--`(31)` unconditionally in Lean 4
- [ ] prove `SUZUKI-TEMPERED-ORBIT-NORMAL-IDENTITY`
- [ ] pass exceptional apertures or construct a nontempered relation
- [ ] prove trace-zero completed modes enter `H1_0`
- [ ] prove completed Evans injectivity
- [ ] RH or whole-Connes no-go
