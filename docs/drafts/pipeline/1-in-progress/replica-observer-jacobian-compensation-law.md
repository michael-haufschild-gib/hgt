# Replica observer-Jacobian compensation law

- **ID:** `replica-observer-jacobian-compensation-law`
- **Stage:** 1 — in progress
- **Type:** failure-driven frontier theorem / invariant correction
- **Status:** `[PAPER-PROVED] [LEAN PENDING] [FRONTIER ADVANCE] [NOVELTY UNVERIFIED]`
- **Parent:** `oriented-no-shortcut-without-return-law.md`
- **Replaces:** raw growing-replica observer-Jacobian pseudodeterminant as the
  proposed complete-circuit-union invariant
- **Date:** 2026-08-07

## Public sentence

Copies can amplify a Jacobian without adding a single distinguishable event:
replica gain is real only after observer duplication and matching tube dilation
have been quotiented out.

## Exact frontier

The qualitative observer-carrier theorem proves that one nonzero analytic
minor confines every exact lower-codimension target carrier to one Gaussian-null
critical locus.  The proposed quantitative successor was a growing-replica
lower-tail bound for the observer-Jacobian pseudodeterminant, intended to
control approximate target tubes after the complete circuit union.

That proposal silently treats raw output-coordinate multiplicity as physical
transversality.  The first theorem below shows this is impossible: repeating
identical observer coordinates changes the raw determinant by an arbitrary
power without changing any event.  The second theorem identifies the same
compensation for physical iid quantum replicas.

## Conjecturing protocol

### Conjecture 1 — raw replica pseudodeterminant beats circuit entropy

Let `D F_r(x)` be the Jacobian of an order-`r` observer reporter.  Conjecture
that its nonzero Gram determinant acquires a replica exponent strong enough to
make every approximate circuit tube small after unioning all circuit words.

**Hostile attack — `[FALSIFIED]`.**  Duplicate every reporter coordinate `k`
times.  The shortcut event is literally unchanged, but the Jacobian Gram is
multiplied by `k`, so a rank-`v` determinant is multiplied by `k^v`.  Since `k`
is arbitrary, any raw determinant-only conclusion would prove arbitrarily
strong probability bounds for one fixed event.  Raw reporter pseudodeterminant
is therefore not an invariant of the observation problem.

### Conjecture 2 — physical tensor copies escape the duplication no-go

Perhaps the artificial-coordinate counterexample is irrelevant because an
`r`-copy quantum state is a physical Veronese embedding rather than a copied
coordinate list.

**Hostile attack — `[FALSIFIED]`.**  For a normalized pure-state model, the
pullback Fubini--Study metric, equivalently one quarter of the pure-state QFI
Gram, is multiplied exactly by `r` under `psi |-> psi^(tensor r)`.  Thus its
rank-`v` Gram determinant is multiplied by exactly `r^v`, only polynomial in
replica order at fixed observer rank.  Meanwhile squared fidelity is raised
to the same power:

\[
 |\langle\psi^{\otimes r},\phi^{\otimes r}\rangle|^2
   =|\langle\psi,\phi\rangle|^{2r}.
\]

For every positive `r` and threshold `0 <= a <= 1`,

\[
 a^r\le |\langle\psi,\phi\rangle|^{2r}
 \quad\Longleftrightarrow\quad
 a\le |\langle\psi,\phi\rangle|^2.                 \tag{1}
\]

Hence the correctly matched `r`-copy fidelity tube has exactly the same
preimage as the one-copy tube.  The local metric dilation and tube dilation
compensate exactly.  Tensor replication does not turn a local coarea estimate
into a growing-replica circuit-union estimate.

### Conjecture 3 — normalize the determinant and retain a replica lower tail

Divide out the deterministic metric multiplicity.  For rank `v`, define

\[
 \widehat\Delta_r(x)=r^{-v}\det G_r(x),              \tag{2}
\]

where `G_r` is the intrinsic projective observer Gram on the `r`-copy model.

**Verdict — `[PAPER-PROVED]`.**  For iid pure-state replicas,

\[
 \boxed{\widehat\Delta_r(x)=\det G_1(x)}             \tag{3}
\]

pointwise.  Consequently, under every probability law `mu` and for every
threshold `tau`,

\[
 \boxed{
 \mu\{\widehat\Delta_r\le\tau\}
   =\mu\{\det G_1\le\tau\}.}                        \tag{4}
\]

This is the exact growing-replica lower-tail law.  It is an invariance law,
not decay.  No quantitative analytic estimate can improve `(4)` without
adding information absent from the local observer Jacobian.

### Conjecture 4 — complete circuit union may still gain after replication

Let `C` be any finite circuit dictionary and let

\[
 S_1(a)=\{x:\exists c\in C,\ a\le f_c(x)\},
 \qquad
 S_r(a)=\{x:\exists c\in C,\ a^r\le f_c(x)^r\},      \tag{5}
\]

where `0 <= f_c(x)` is squared fidelity with target `c`.

**Verdict — `[PAPER-PROVED]`.**  Applying `(1)` before the existential
quantifier gives

\[
 \boxed{S_r(a)=S_1(a)}                               \tag{6}
\]

for every finite or infinite dictionary, with no measurability or selector
assumption.  The conclusion survives the complete circuit union exactly.

### Stronger replacement conjecture — incidence-normalized replica action

The determinant failure identifies the missing variable.  A complete-union
bound needs two independent inputs:

1. **intrinsic transversality**, measured by the frame-normalized observer
   Jacobian after quotienting duplicate reporter directions; and
2. **endpoint--circuit incidence**, measuring how much of the autonomous
   endpoint image is met by the shallow-circuit tube after longitudinal
   returns are removed.

The first factor controls the volume of one genuinely different local sheet.
The second controls how many such sheets the complete circuit union actually
occupies.  Neither factor can be recovered from the other.  The new open
quantity is therefore a coarea-weighted incidence action, not a raw
pseudodeterminant:

\[
 \mathcal A_{t,s,\epsilon}
 =-\log\!\int_{E_{s,\epsilon}}
     \left(\int_{F_t^{-1}(y)}
       {\varphi(J)\over J_vF_t(J)}
       \,d\mathcal H^{m-v}(J)\right)
   d\mathcal H^v(y),                                  \tag{7}
\]

where `E_(s,epsilon)` is the complete shallow-circuit tube, `varphi` is the
Gaussian coefficient density, and the inner integral includes all endpoint
sheets.  Formula `(7)` is the coarea disintegration of the actual aggregate
event.  A pointwise Jacobian lower tail sees the denominator but not fibre
multiplicity or which part of the image is occupied by `E_(s,epsilon)`.

The next risky conjecture is:

> After removing the permitted earlier-return component by anchor rephasing,
> the ordinary fixed-`q` Gaussian local-Hamiltonian ensemble has a quenched
> growing-replica upper bound on the **incidence-normalized action `(7)`**
> strong enough to beat the depth-`s` circuit language.

This conjecture is not proved.  Unlike the retired determinant conjecture, it
cannot be changed by duplicating observers or circuit labels and it represents
the complete circuit union before any targetwise union bound.

## Dependency-closed proof

### A. Uniform reporter duplication

Let `J` be an `N x v` real Jacobian and set

\[
 G(J)_{ij}=\sum_{a=1}^N J_{ai}J_{aj}.                 \tag{8}
\]

For an integer `k>0`, form `J^[k]` by repeating each row exactly `k` times.
Then

\[
\begin{aligned}
 G(J^{[k]})_{ij}
 &=\sum_{b=1}^k\sum_{a=1}^N J_{ai}J_{aj}\\
 &=kG(J)_{ij}.
\end{aligned}                                        \tag{9}
\]

The determinant is homogeneous of degree `v` in a scalar matrix multiple, so

\[
 \det G(J^{[k]})=k^v\det G(J).                       \tag{10}
\]

But a duplicated reporter map has the same zero set, the same exact fibres,
and the same approximate tube preimage when its output norm and threshold are
transported through the diagonal isometry.  In particular, duplicating a
target label does not change an existential target union.  Equations
`(9)`--`(10)` therefore prove that the unnormalized determinant is coordinate
multiplicity, not observation information.

For `k>0`, division by `k^v` in `(10)` gives exact normalized invariance.  If
`J=J(x)` is random, pointwise equality implies equality of the lower-tail sets
and hence `(4)` for every measure.

### B. Projective tensor-replica metric

Let `psi(x)` be normalized and write `u=Dpsi(x)[h]`, `w=Dpsi(x)[k]`.  Its
projective Hermitian tangent form is

\[
 Q_1(u,w)=\langle u,w\rangle
 -\langle u,\psi\rangle\langle\psi,w\rangle.          \tag{11}
\]

The derivative of the `r`-copy vector is

\[
 D(\psi^{\otimes r})[h]
 =\sum_{a=1}^r
   \psi^{\otimes(a-1)}\otimes u\otimes
   \psi^{\otimes(r-a)}.                              \tag{12}
\]

Expanding the inner product of two sums in `(12)`, diagonal slot pairs give
`r <u,w>`, while distinct slot pairs give
`r(r-1)<u,psi><psi,w>`.  The component parallel to
`psi^(tensor r)` equals `r<u,psi>`, so its projective subtraction is
`r^2<u,psi><psi,w>`.  Therefore

\[
 Q_r(u,w)
 =r\langle u,w\rangle+r(r-1)
   \langle u,\psi\rangle\langle\psi,w\rangle
  -r^2\langle u,\psi\rangle\langle\psi,w\rangle
 =rQ_1(u,w).                                         \tag{13}
\]

Taking real parts gives the Fubini--Study Gram, and multiplying by four gives
the pure-state QFI Gram.  Thus every selected `v x v` Gram block is multiplied
by `r`, proving `(2)`--`(4)`.

### C. Exact tube and union compensation

Tensor-product inner products multiply, proving the fidelity identity before
`(1)`.  The map `z |-> z^r` is strictly increasing on nonnegative reals for
every `r>0`; hence `(1)`.  Existential quantification over any dictionary
preserves logical equivalence pointwise, proving `(6)`.  No target union,
metric-net argument, or probability estimate occurs.

## Why analytic small-ball machinery cannot repair the raw invariant

- Carbery--Wright gives polynomial sublevel estimates with an exponent that
  pays polynomial degree.  The autonomous endpoint minor is analytic rather
  than fixed-degree polynomial, and replica degree grows.  More importantly,
  no sublevel theorem can distinguish a reporter from `k` identical copies of
  itself unless the norm is normalized first.
- Effective Remez and Lojasiewicz bounds require analytic-complexity constants
  (degree, Bang degree, derivative bounds, or tame compact geometry).  One
  nonzero value, which suffices for the qualitative null-set theorem, supplies
  no uniform lower-tail constant.
- Coarea contains reciprocal Jacobian **and fibre multiplicity**.  A Jacobian
  lower tail alone cannot control an easy set that already occupies the full
  endpoint image, even when the Jacobian is identically one.

## External priority audit

- Additivity of QFI for iid copies and the fact that the degree-`r` Veronese
  embedding pulls the Fubini--Study form back to `r` times itself are classical.
- Carbery--Wright polynomial small-ball inequalities and quantitative
  Remez/Lojasiewicz theory are classical quantitative tools, but they do not
  supply a complete-circuit-union incidence theorem for one static local
  Hamiltonian.
- Quantum-control literature studies singular endpoint maps and qualitative
  transversality, not the duplicate-invariant coarea/circuit-incidence problem.
- No audited source was found that states the exact no-go at the interface of
  iid quantum replica moments, observer-Jacobian tube bounds, and the complete
  autonomous circuit union.

Priority verdict: generic identities are `[REDISCOVERED]`; their use to retire
raw growing-replica pseudodeterminant and isolate incidence-normalized action is
`[NOVELTY UNVERIFIED]`.  No standalone novelty claim is authorized.

Primary sources checked:

- Carbery and Wright, *Distributional and L-q norm inequalities for
  polynomials over convex bodies in R^n*, MRL 8 (2001),
  https://doi.org/10.4310/MRL.2001.v8.n3.a1.
- Rainer, *Effective quasianalytic Remez inequalities on tame sets*,
  arXiv:2606.08183.
- Barndorff-Nielsen and Gill, *Fisher information in quantum statistics*,
  arXiv:quant-ph/9808009.
- Wu, Dominy, Ho, and Rabitz, *Singularities of Quantum Control Landscapes*,
  arXiv:0907.2354.

## Hostile review

1. **Does this prove Brown--Susskind growth?** No.  It proves that the named
   determinant-only open core cannot prove it and identifies the missing joint
   invariant.
2. **Is determinant scaling novel?** No.  Homogeneity, QFI additivity, and
   Veronese metric scaling are classical.  Novelty can lie only in the
   circuit-union no-go and the resulting incidence formulation.
3. **Could a different unnormalized reporter evade the theorem?** It could
   produce a larger determinant, but unless that enlargement survives reporter
   duplication/whitening it is coordinate bookkeeping.  A physical claim must
   use an intrinsic reporter norm.
4. **Does intrinsic pseudodeterminant become useless?** No.  It controls local
   sheet volume and exact critical carriers.  It is one factor in `(7)`, not
   the factor that counts aggregate circuit incidence.
5. **Does `(7)` merely rename shortcut probability?** As written, it is an
   exact coarea representation, not yet an independently bounded invariant.
   The next theorem must decompose or bound its fibre/incidence term using
   local-Hamiltonian structure; defining `(7)` alone is not closure.
6. **Could high-order jets beat the no-go?** Possibly.  The theorem rules out
   first-order raw Jacobian amplification.  Any higher-order proposal must be
   normalized against replica metric dilation and must control aggregate
   incidence rather than reintroducing targetwise union.

## Formalization gate

- [ ] Uniform reporter-duplication Gram identity.
- [ ] Determinant scaling and normalized determinant invariance.
- [ ] Exact lower-tail set/measure invariance.
- [ ] Power-threshold equivalence under arbitrary complete target union.
- [ ] Pure-state tensor-replica projective Gram scaling.
- [ ] Axiom audit and umbrella reachability.
- [ ] Update parent frontier: raw pseudodeterminant retired; incidence-normalized
      action becomes open core.

