# Observer-clock transmutation groupoid, neutral-charge anomaly, and properness law

- **ID:** ULF-TAFM-19
- **Stage:** 2-fully-proven
- **Type:** universal mechanism / global formation-properness classification
- **Parents:** ULF-TAFM-15 through ULF-TAFM-18
- **Status:** dependency-closed paper proof; Lean formalisation complete

## 1. Field object: one source, many clocks

For source density `mu : N -> R` and observer clock `c : N -> R`, define

\[
 dc_k=c_{k+1}-c_k,
 \qquad q^c_k=\mu_k dc_k,
 \qquad F^c_N=\sum_{k=0}^N q^c_k.                    \tag{OCT.1}
\]

When `dc_k != 0`, relative rate from `c` to `d` is

\[
 \lambda_{c\to d}(k)=\frac{dd_k}{dc_k}.              \tag{OCT.2}
\]

### Theorem 1.1 -- reconstruction and clock groupoid

At every nondegenerate edge,

\[
 q^d_k=q^c_k\lambda_{c\to d}(k).                     \tag{OCT.3}
\]

The reference charge reconstructs `mu_k=q^c_k/dc_k` and therefore every target-clock charge.
Across three nondegenerate clocks,

\[
 \lambda_{c\to e}(k)=
 \lambda_{c\to d}(k)\lambda_{d\to e}(k).             \tag{OCT.4}
\]

#### Proof

Both statements are cancellation of the nonzero clock edges in `(OCT.2)`. Thus clocks are not
separate route coordinates. Their nondegenerate changes form a multiplicative groupoid acting on
one source density. QED.

## 2. Exact clock-acceleration conservation

Let `q` be a reference-clock charge, `lambda` a relative rate, and
`Q_N=sum_(k=0)^N q_k`.

### Theorem 2.1 -- boundary storage plus acceleration work

For every finite depth,

\[
 \sum_{k=0}^N q_k\lambda_k
 =Q_N\lambda_N+
   \sum_{k=0}^{N-1}Q_k(\lambda_k-\lambda_{k+1}).       \tag{OCT.5}
\]

#### Proof

At `N=0` both sides are `q_0 lambda_0`. In the successor step use
`Q_(N+1)=Q_N+q_(N+1)` and add the last acceleration term
`Q_N(lambda_N-lambda_(N+1))`. All `Q_N lambda_(N+1)` terms cancel, leaving the old response plus
`q_(N+1)lambda_(N+1)`. QED.

Equation `(OCT.5)` is the common mechanism: a charge closed by one observer may remain open after
clock change because an unbounded relative rate amplifies boundary storage and acceleration work.

## 3. Global properness classification

For `m>=1`, define neutral unit dipole

\[
 \delta^{(m)}_k=1_{k=m}-1_{k=0}.                      \tag{OCT.6}
\]

It has total charge zero and `l1` mass exactly two. Its rate response is

\[
 \sum_{k=0}^m\delta^{(m)}_k\lambda_k
 =\lambda_m-\lambda_0.                                \tag{OCT.7}
\]

### Theorem 3.1 -- neutral-dipole properness criterion

The following are equivalent:

1. `lambda` is uniformly bounded;
2. responses of all neutral unit dipoles are uniformly bounded.

If `lambda` is unbounded, then for every `A` there is a neutral finite charge of `l1` mass two
whose target response has absolute value greater than `A`.

#### Proof

If `|lambda_k|<=B`, `(OCT.7)` is at most `2B`. Conversely, if
`|lambda_m-lambda_0|<=B`, then

\[
 |\lambda_m|\le B+|\lambda_0|,
\]

while `m=0` is already bounded by `|lambda_0|`. Negating the equivalence yields arbitrarily large
dipole responses without changing total charge or `l1` mass. QED.

This is a global formation/properness theorem, not a source endpoint. Uniform clock-change
compactness fails exactly when fixed resource can be amplified without bound.

## 4. Literal harmonic--Riesz landing

Use completed prime--polar--Gamma density

\[
 \mu_k=R(k+1)+2\gamma,
\]

where `R=psi-id`. Define clocks

\[
 c_h(k)=-\frac1{k+1},
 \qquad c_{1/2}(k)=\sqrt{k+1}.                         \tag{OCT.8}
\]

Their edges are

\[
 dc_h(k)=\frac1{k+1}-\frac1{k+2},
 \qquad dc_{1/2}(k)=\sqrt{k+2}-\sqrt{k+1}.            \tag{OCT.9}
\]

The harmonic charge is exactly the existing completed harmonic source. It is absolutely summable
and its infinite total is zero. The square-root response is exactly

\[
 \sum_{k=0}^{M-2}(R(k+1)+2\gamma)
   (\sqrt{k+2}-\sqrt{k+1})
 =\mathcal R_M,                                       \tag{OCT.10}
\]

the literal completed Möbius--divisor Riesz moment. Thus closed harmonic observer and open Riesz
history are two gauges of one source density.

### Theorem 4.1 -- literal relative clock is unbounded

For `k>=3`,

\[
 k+1\le
 \lambda_{h\to1/2}(k)
 =\frac{\sqrt{k+2}-\sqrt{k+1}}
        {1/(k+1)-1/(k+2)}.                            \tag{OCT.11}
\]

#### Proof

Put `a=k+1`, `b=k+2`, `d=sqrt b-sqrt a`, and `s=sqrt b+sqrt a`. Then `ds=1`. For `a,b>=4`,
`sqrt a<=a/2` and `sqrt b<=b/2`, hence `s<=b`. Therefore `1=ds<=db`. Since the harmonic edge is
`1/(ab)`, the ratio is `dab>=a=k+1`. QED.

Theorem 3.1 now produces fixed-mass neutral harmonic charges with arbitrarily large square-root
response. Universal boundedness, compactness, positivity, or recurrence cannot control this clock
change.

## 5. New architecture and exact remaining producer

The field object is the source together with its observer-clock groupoid and graph domains of the
generally unbounded transmutation maps. This explains four corpus phenomena with one law:

1. recurrence: harmonic observer closes with zero total charge;
2. open history: square-root observer retains amplified boundary history;
3. hypertranscendence/noncompactness: unbounded relative clock rate makes fixed-resource dipoles
   escape;
4. positivity: local phase quotient sees squared target current but not signed acceleration
   cancellation.

RH cannot be universal boundedness of the harmonic-to-Riesz operator; `(OCT.11)` disproves that.
It is exceptional-domain regularity of the one arithmetic charge under this unbounded operator.
The remaining source theorem must prove joint cancellation in `(OCT.5)` for literal harmonic
prefixes and clock acceleration, using multiplicative prime feedback. Estimating the two terms by
absolute value destroys the exact zero charge and regresses to the known RH-strength wall.

## Hostile audit

1. **Not Abel summation renamed.** Abel summation is one identity; the new law supplies source
   reconstruction across clocks, multiplicative clock composition, and a sharp properness
   classification by neutral fixed-mass probes.
2. **Not a route endpoint.** The theorem applies to every source density and every nondegenerate
   clock family.
3. **Not a hidden RH premise.** Literal clock-rate unboundedness and harmonic zero charge are
   unconditional. No bound on literal Riesz response is asserted.
4. **No generic-compactness theatre.** The theorem proves generic compactness impossible and
   retypes selection as exceptional-domain source regularity.
5. **No phase/magnitude conflation.** ULF-TAFM-18 governs local orientation quotient; ULF-TAFM-19
   governs amplitude amplification by observer-clock acceleration.

## Gates

- [x] dependency-closed generic proof
- [x] literal harmonic/Riesz clock identification
- [x] literal relative-rate unboundedness
- [x] Lean formalisation
- [ ] source-specific exceptional-domain cancellation law
- [ ] RH selection consequence
