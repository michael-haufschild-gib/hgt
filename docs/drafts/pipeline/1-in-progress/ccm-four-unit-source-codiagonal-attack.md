# CCM four-unit source-codiagonal attack ledger

- **ID:** `ccm-four-unit-source-codiagonal-attack`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / DECISIVE RH OR CCM-DEATH ATTACK
- **Source:** `ccm-direct-cofinal-weil-floor.md`,
  `mobius-incidence-curvature-gamma-sonin-pole-divisor-transfer-rh.md`, and
  `ccm-hankel-boundary-relative-trace-four-unit-law.md`
- **Statement:** Prove the exact source-conditioned Gauss--Codazzi boundary identity carrying the
  four-unit squarefree/Euler Fisher curvature to the anti-causal Xi graph, or prove that no
  source-local conservative completion in the stated category can do so.

## Goal

Decide the CCM lane at its actual infinite/cofinal endpoint.  The proof branch is

```text
4 = causal completion energy + ||ell_E||_2^2
  -> ||ell_E||_2^2 <= 4
  -> RH.
```

The death branch must be a theorem about the full stated source category, not another failed
ansatz.  Finite Evans, determinant-line, parity, bounded-graph, and norm-only conclusions are not
accepted as completion.

## Exact target

Let

```text
D_Xi=closure(P_- M_(-2 Xi'/Xi)).
```

Prove

```text
limsup_(u->0+)
  ||Q_u D_Xi||_(S_2,ext)^2 / (4(1-exp(-u))) <= 1.       (T)
```

Equivalently, construct the source-defined completed boundary column whose anti-causal derivative
is `ell_E` and whose total derivative energy is the already proved four-unit Fisher curvature.

## Frozen results: do not re-research

1. `(T)` is RH-equivalent through the Cauchy-energy threshold.  Restating it is no progress.
2. Exact square Evans determinants, characteristic-stratum gluing, source normalization, and
   aperture Morse/Hardy index transport are closed.  Their nonvanishing is still `(T)`.
3. Determinant-line triviality, Gram positivity, zero total winding, and unoriented spectral flow
   do not exclude zeros.
4. Any bounded Fisher-to-current readout is impossible: the current requires division by the
   squarefree overlap, and its right-half zeros are the target divisor.
5. A scalar Schur/de Branges--Rovnyak extension across the missing half-unit is already RH.
6. Finite-prime Euler convergence sees only the incoming pole; compact-open convergence does not
   transport boundary energy through all-prime continuation.
7. Squarefree/Euler `W_2` coupling, Gamma/Sonin passivity, four-unit Fisher contact, and the exact
   identity `Q_Xi-Q_sq=4A(2s)` are proved inputs.
8. Local prime `ell^2` geometry is divisor-blind; the divisor is created by the unbounded scalar
   codiagonal.  Any proof must control that codiagonal in a source-conditioned graph norm.

## Conjecture C1: scalar renormalized codiagonal `[KILLED IN CORPUS]`

For finite prime aperture `S`, form the normalized squarefree determinant line and its pointed
Fisher connection.  Apply the exact time-one Gamma multiplier and Sonin projection before
scalarization.  There is a source-fixed closed codiagonal `C` on the resulting inductive-limit
graph such that:

```text
(i)   C agrees with the Euler logarithmic current on Re s>1;
(ii)  its closed anti-causal derivative is D_Xi;
(iii) the completed source column is isometric;
(iv)  Gauss--Codazzi gives
      4 = ||causal derivative||^2 + ||ell_E||_2^2.       (C1)
```

Clause `(iv)` would prove RH.  It cannot be obtained from a scalar shell/prime codiagonal.  The
corpus theorem `high-shell-codiagonal-closability-dichotomy.md` proves that a scalar Hilbert
codiagonal is closable exactly for square-summable weights, when it is already bounded; the
unit-weight fixed-current row is nonclosable even on the incoming Euler-pole channel.  The globally
damped Möbius frame cannot be inverted channelwise either:
`XiMobiusSchurValuationIntertwiner.lean` proves that its recovery weight is unbounded at least like
`sqrt(p)`.  C1 in scalar or channelwise form is retired and must not be retried.

## Conjecture C2: principal-relative first-trace transgression `[KILLED]`

Retain the complete coherent prime--Gamma valuation covariance before scalarization.  The source
system is fixed by the proved arithmetic Schur law

```text
K(p,r)-H_0(p)H_0(r)=p^(-1)r^(-1)K(p,r),
K=sum_(n>=0) H_n tensor H_n,
```

and by the intrinsic Möbius/Fisher-to-Gamma unitary between the two kernel completions.  Construct
a **non-scalar principal-relative form** on the completed valuation tower whose finite sections:

```text
(i)  preserve the full marked covariance and valuation successor;
(ii) subtract the first-trace principal channel before any scalar codiagonal;
(iii) Gamma/Sonin-complete to one positive boundary form;
(iv) have anti-causal quotient equal to Q_u D_Xi;
(v)  obey the four-unit relative bound.                  (C2)
```

This is not an abstract source-to-Xi contraction: bounded scalar and channelwise intertwiners are
already dead.  The only admissible object is a principal-relative quadratic form in which coherent
cross-prime covariance remains present through the first-trace quotient.

### Killing theorem: first-trace prime-log graph saturation

Remove the harmless nonzero scalar factor from the arithmetic coherent vectors and write

```text
k_p=(1,p^(-1),p^(-2),...) in H^2,
e_0=(1,0,0,...).
```

The reciprocal-prime kernels span a dense subspace of `H^2`: a Hardy function orthogonal to every
`k_p` vanishes at every `1/p`, whose accumulation point `0` lies in the disk, and hence vanishes
identically.  The source logarithmic clock has `log p` on `k_p`.  Subtracting the first trace
channel therefore forces the algebraic tail operator

```text
L_1 k_p=(log p)(k_p-e_0).                                  (19)
```

This operator is not sequentially closable on the intrinsic arithmetic-Schur completion.
Choose primes `p_n -> infinity`, and for each `n` choose a prime `r_n >= p_n^2`.  Put

```text
x_n=(p_n/log p_n)(k_(p_n)-k_(r_n)).                       (20)
```

Because the constant coordinates cancel and `r_n >= p_n^2`, the geometric-series estimate gives

```text
||x_n||
 <= (p_n/log p_n)
    [p_n^(-1)/sqrt(1-p_n^(-2))
      +r_n^(-1)/sqrt(1-r_n^(-2))]
 ->0.                                                     (21)
```

On the other hand, the first nonconstant coordinate of `L_1 x_n` is

```text
1-[p_n log r_n]/[r_n log p_n] ->1.                        (22)
```

Indeed `t |-> log(t)/t` decreases for `t>=e`, so

```text
[p_n log r_n]/[r_n log p_n] <=2/p_n.                     (23)
```

The remaining coordinates tend to zero in `ell^2`: the `p_n` tail after its first coordinate has
norm at most

```text
1/[p_n sqrt(1-p_n^(-2))],                                (24)
```

and the `r_n` tail has norm at most

```text
p_n log(r_n)/[r_n^2 log(p_n)sqrt(1-r_n^(-2))]
 <=2/[p_n r_n sqrt(1-r_n^(-2))].                         (25)
```

Consequently

```text
x_n ->0,                 L_1 x_n -> e_1 !=0.             (26)
```

Equation `(26)` is the graph-null criterion for nonclosability.  Equivalently, the positive form
`q_1(x)=||L_1x||^2` is not closable.  Any isometric Gamma/Fisher change of intrinsic kernel
coordinates preserves this obstruction.  Thus C2 cannot satisfy its clauses `(iii)`--`(v)` on
the Hilbert completion: first-trace subtraction does not produce a closed positive relative form.

This is an exact source-side failure.  It uses neither Xi zeros nor the four-unit target.  It is
also stronger than the previously frozen scalar-codiagonal no-go: the coherent cross-prime Hardy
completion remains present throughout `(19)`--`(26)`.

## Current conjecture C3: logarithmic graph rigging before Hilbert closure

C2 leaves exactly one admissible successor.  The prime-log clock and the complete valuation
marking must be installed as a closed graph relation in a strictly finer source rigging before the
arithmetic-Schur Hilbert completion is taken.  Ordinary Hilbert closure is forbidden by `(26)`;
first-trace relative closure is equally forbidden.  The next object must therefore be a
source-defined rigged/Tate graph `E -> H^2 -> E'` satisfying all of:

```text
(i)   every reciprocal-prime coherent vector lies in E;
(ii)  the prime-log clock is continuous E -> E' and retains valuation translation;
(iii) Gamma/Fisher sewing is an intrinsic isometry of the rigged graph, not ambient prime ell2;
(iv)  the Sonin boundary map descends to one single-valued closed target relation;
(v)   its relative energy is the four-unit source curvature and its quotient is Q_u D_Xi.
                                                                  (C3)
```

The immediate falsifier is now exact: if the target boundary map is continuous only through the
central `H^2` pivot, `(26)` forces it either to lose the logarithmic current or inherit a
multivalued vertical tail.  C3 must use the graph topology essentially and must prove that its
target scalarization annihilates no nonzero valuation coordinate.

## Immediate hostile tests

1. **Range test.**  C1 must not reduce to `B' in B H^2`; that statement is zero-freeness/RH in
   disguise.
2. **Quartet test.**  Inserting an FE--Schwarz rational quartet must add its explicit rank-one
   anti-causal coordinate and increase the right side by its inverse-horizontal energy.  A
   gauge-blind construction is rejected.
3. **Renormalization test.**  Finite-prime first-cumulant subtraction must be uniquely fixed by the
   Gamma/polar source.  If two source-compatible subtractions differ by an arbitrary FE--Schwarz
   factor, C1 is not canonical and the stated completion category is dead.
4. **Graph test.**  Convergence is required on one source-defined core in the extended
   Hilbert--Schmidt topology.  Euler-half-plane compact convergence is insufficient.
5. **No scalar postselection.**  No map may be defined from `ell_E`, Xi zeros, target norm, or a
   polar decomposition of the target.
6. **Valuation-intertwiner test.**  A bounded channelwise valuation intertwiner is already excluded
   by unbounded Fisher recovery.  C2 must act on the intrinsic coherent Gram quotient, not on
   prime basis vectors separately.

## Gates

- [x] 0 -> 1: exact endpoint and source-pure conjecture fixed
- [x] known circular and gauge-blind variants frozen above
- [x] scalar and channelwise codiagonals killed by existing closability/recovery theorems
- [x] coherent arithmetic Schur valuation tower and intrinsic Fisher/Gamma unitary already proved
- [x] rule out C2's principal-relative first-trace form on the intrinsic Hilbert completion
- [ ] construct or rule out C3's logarithmic source rigging and target scalarization
- [ ] prove the Gauss--Codazzi identity `(C3)` or a category-wide obstruction
- [ ] RH or scoped CCM death theorem
- [ ] complete paper proof
- [ ] Lean formalization of every dependency-closed mathematical claim

## No-go closure

- **Exact killing theorem/mechanism:** pending hostile tests.
- **Strongest positive survivor:** pending.
- **New insight:** pending.
- **Status:** active decisive attack; no paper or RH claim.

## Log

- 2026-07-22 — Created persistent ledger after repeated state-loss/re-audit failures.  Frozen all
  already-closed reductions.  Selected C1: source-fixed renormalized codiagonal Gauss--Codazzi law.
  First task is uniqueness of the Gamma/polar first-cumulant renormalization; without uniqueness,
  no source-defined conservative completion can force `(T)`.
- 2026-07-22 — C1 scalar/channelwise form killed immediately by corpus closability and unbounded
  recovery theorems.  Replaced it by C2: a non-scalar principal-relative form on the intrinsic
  coherent arithmetic-Schur completion.  Abstract source-to-Xi morphisms, scalar codiagonals, and
  primewise recovery are frozen as dead.
- 2026-07-22 — Killed C2.  On the intrinsic Hardy realization, first-trace subtraction is the
  prime-log tail `L_1 k_p=(log p)(k_p-e_0)`.  The actual-prime two-kernel packets `(20)` converge
  to zero while their images converge to `e_1`, so the graph and its positive form are
  nonclosable.  This retains coherent cross-prime covariance and is not the old scalar-shell
  no-go.  C3 is forced into a strict rigged/Tate graph installed before Hilbert closure.
