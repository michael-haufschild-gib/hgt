# Suzuki opposite-shift cross-sewn exterior product and projective pole invariant

- **ID:** `suzuki-opposite-shift-cross-sewn-exterior-product`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / SOURCE-SEMANTICS CORRECTION / RH FRONTIER REDUCTION
- **Scientific status:** `[FORMALIZED] [FULLY PROVEN ON PAPER] [SOURCE-SPECIFIC] [NOVELTY AUDITED] [NOT AN RH PROOF]`
- **Primary source:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
  [arXiv:2606.09096v1](https://arxiv.org/abs/2606.09096), Theorem 1.5, Corollary 1.6,
  and Sections 7--8.
- **Parent:** `suzuki-opposite-shift-parity-harmonic-recovery`
- **Lean module:**
  `GaloisForLFunctions.RHTower.SuzukiOppositeShiftCrossSewnExterior`

## Actual frontier exposed by corpus

Corpus cannot prove that Suzuki's finite-aperture source produces an off-real analytic exterior
channel in cofinal aperture limit. That producer statement is RH-bearing: exterior pole tomography
proves every nonreal Xi zero creates an unavoidable simple pole whenever characteristic factor is
analytic and nonzero there.

Previous opposite-shift theorem proves

```text
G_eta+G_(-eta)=2G_0,
E_eta(W,I)+E_(-eta)(W,I)=2E_0(W,I),                     (1)
```

where `G_eta=R_eta^(-1)` and `E_eta(W,I)=G_eta W-I`. Second identity is valid algebra, but actual
finite-aperture `+eta` and `-eta` source problems are built from different resolvents and source
transforms. Corpus and Suzuki's paper supply no theorem identifying their characteristic functions,
interval contributions, or gauges. Suzuki only says shift-independence of zeros is expected from a
Hilbert-space isomorphism; he explicitly says shift control requires new arithmetic analysis.
Therefore common-channel average in `(1)` is not the actual source pair.

## Theorem A: distinct-channel cross-sewing `[PROVED HERE]`

For arbitrary channels `(W_+,I_+)` and `(W_-,I_-)`, define

```text
C_eta
 := W_- E_eta(W_+,I_+) + W_+ E_(-eta)(W_-,I_-),         (2)
P := 2 W_+ W_-,
J := W_- I_+ + W_+ I_- .                                (3)
```

Then pointwise on all of `C`, including `z=0` and every Xi zero,

```text
C_eta = E_0(P,J).                                       (4)
```

No equality, common gauge, nonvanishing, limiting process, or RH assumption on two source channels
occurs in `(4)`.

### Proof

Expand definition and use only exact opposite-multiplier projection from parent theorem:

```text
C_eta
 =W_-(G_eta W_+-I_+) + W_+(G_(-eta)W_--I_-)
 =(G_eta+G_(-eta))W_+W_--(W_-I_++W_+I_-)
 =2G_0W_+W_--J
 =G_0P-J
 =E_0(P,J).
```

Every operation is polynomial after already-totalized multipliers are treated as function values,
so formula has no hidden denominator condition.

## Theorem B: independent-gauge covariance and projective descent `[PROVED HERE]`

Apply unrelated gauges to two channels:

```text
(W_+,I_+) -> (g_+W_+,g_+I_+),
(W_-,I_-) -> (g_-W_-,g_-I_-).                           (5)
```

Direct expansion gives

```text
C_eta[g_+,g_-]=g_+g_- C_eta,
P[g_+,g_-]=g_+g_- P,
J[g_+,g_-]=g_+g_- J.                                   (6)
```

Consequently normalized cross-sewn channel

```text
N_eta := C_eta/P                                       (7)
```

is invariant under independent gauges at every point where `g_+g_-` is nonzero. In particular,
zero-free entire gauges need not be matched across shifts.

Away from zeros of `W_+W_-`, `(4)` becomes stronger shift-elimination identity

```text
N_eta
 =G_0-(1/2)(I_+/W_+ + I_-/W_-).                        (8)
```

Thus explicit opposite shift cancels before any cofinal limit. Formula `(8)` is a projective
observable of two source lines: both unrelated normalizations and affine shift coordinate disappear.

### Proof

Every term of first cross summand in `(2)` acquires factor `g_-g_+`; same holds for second. Each
term of `(3)` acquires same product, proving `(6)`. Cancel nonzero product in `(7)`. Divide `(4)`
by `2W_+W_-` and split cross interval quotient:

```text
(W_-I_+ + W_+I_-)/(2W_+W_-)
 =(1/2)(I_+/W_+ + I_-/W_-),
```

which proves `(8)`.

## Theorem C: product real-zero closure and RH criteria `[PROVED HERE]`

Assume `W_+`, `W_-`, `I_+`, and `I_-` are entire and both characteristic factors have only real
zeros. Then `P` and `J` are entire, and `P` has only real zeros. Therefore existing exterior pole
tomography, now in generic real-zero form, gives

```text
RH <=> C_eta is analytic at every nonreal point.         (9)
```

Since `P` is analytic and nonzero off real axis, multiplication or division by `P` preserves local
analyticity there. Hence projectively gauge-invariant criterion is

```text
RH <=> N_eta is analytic at every nonreal point.        (10)
```

### Proof

Products and sums of entire functions are entire. If `P(z)=0`, nonzero constant `2` implies
`W_+(z)=0` or `W_-(z)=0`, hence `Im z=0`. Apply generic exterior criterion to `(P,J,eta=0)` and
rewrite its channel using `(4)`, proving `(9)`. At every nonreal `z`, real-zero closure gives
`P(z)!=0`; analyticity of `C_eta/P` follows from analyticity of `C_eta`, while converse follows by
multiplying `N_eta` by `P` on neighborhood where `P` remains nonzero. This proves `(10)`.

## Theorem D: universal normalized Xi-pole tomography `[PROVED HERE]`

Let `z` be nonreal Xi zero of arbitrary multiplicity

```text
m=ord_z(XiC)>=1.
```

Under hypotheses of Theorem C, `P(z)!=0`. Existing exterior tomography applied to `(4)` gives

```text
ord_z(C_eta)=-1,
TC_z(C_eta)=m P(z)/z^2.                                 (11)
```

Division by analytic nonzero `P` yields

```text
ord_z(N_eta)=-1,
TC_z(N_eta)=m/z^2.                                      (12)
```

Formula `(12)` is independent of `eta`, both characteristic functions, both interval parts, and
both independent gauges. It is universal projective obstruction: opposite source sewing cannot
move, cancel, or renormalize a hypothetical nonreal Xi pole.

### Proof

Nonreal `z` and real-zero hypotheses imply `P(z)!=0`. Apply parent exterior order and trailing
coefficient theorems to zero-shift remainder `E_0(P,J)` and use `(4)`, obtaining `(11)`. Analytic
nonzero `P` has meromorphic order zero and trailing coefficient `P(z)`. Quotient order subtracts
zero; quotient trailing coefficient divides by `P(z)`. Cancellation proves `(12)`. Xi-zero theorem
already implies `z!=0`, so displayed coefficient is defined without extra premise.

## Scientific-method test outcomes

- [x] **T1 source-object test:** opposite finite shifts use different resolvents/source transforms;
      neither corpus nor source identifies their gauges. Suzuki labels zero independence an
      expectation, not theorem.
- [x] **T2 algebra test:** `(4)` uses only `G_eta+G_(-eta)=2G_0`; no division or nonvanishing.
- [x] **T3 divisor test:** product zero off real would force factor zero off real, impossible.
- [x] **T4 analytic test:** `P` and `J` entire by sum/product closure.
- [x] **T5 gauge test:** independent covariance `(6)` is exact; normalized observable descends
      whenever gauges are nonzero.
- [x] **T6 pole test:** product nonvanishing exposes simple Xi pole; normalization leaves universal
      coefficient `(12)`.
- [x] **T7 converse test:** under RH, Xi multiplier and all source quotients are analytic off real;
      `(4)` and `(8)` give both directions of `(9)`--`(10)`.
- [x] **T8 totalization test:** cross-sewn identity stated globally; quotient identities state
      exact nonvanishing premises.
- [x] **T9 computation/RH test:** no computation and no RH assumption enter theorem proofs.

## Novelty audit

- Repository search found opposite multiplier average, common-channel average, flat shift
  holonomy, and exterior pole tomography, but no distinct-channel cross-sewing, product
  characteristic, independent-gauge descent, or universal normalized pole coefficient.
- Suzuki's paper constructs finite-shift characteristic functions and expects their zero sets to
  be shift independent, but gives none of `(2)`--`(12)` and no opposite-shift product observable.
- Current primary-literature searches for Suzuki/Xi opposite-shift products and cross-sewn
  characteristic channels found no collision. General product/divisor algebra is standard;
  novelty claim is limited to source-specific synthesis and exact projective obstruction.

## Corrected open core

### Subsequent source-admissibility correction

The algebraic theorem above remains valid, but its proposed actual source schedule is not
unconditional. Suzuki requires each real shift to satisfy `lambda<lambda_a`. A nonzero opposite
pair `lambda,-lambda` satisfies both inequalities exactly when `|lambda|<lambda_a`; existence of
such a pair is equivalent to `lambda_a>0`. Thus actual opposite-channel availability can import
the localized Weil/RH positivity that route seeks to prove.

`suzuki-admissible-two-shift-affine-sewing.md` supersedes source schedule: every half-line below an
arbitrary floor contains two distinct shifts, and any two distinct source shifts reconstruct zero
shift by exact affine sewing. Its pair-change theorem also proves that all such normalized
observables have same nonreal singular germ modulo analytic interval-quotient corrections.

This theorem does not prove RH. It removes two false prerequisites from source producer:

```text
no need W_+=W_-;
no need common gauge across shifts.
```

For opposite shifts considered purely algebraically, remaining frontier was:

> Identify actual finite-aperture exterior pairs `(W_+,I_+)`, `(W_-,I_-)` and prove their
> projectively normalized cross-sewn channel `N_eta` has cofinal analytic continuation at every
> nonreal point.

The superseding affine theorem removes need to construct an opposite pair. Its remaining frontier
is to identify one arbitrary admissible pair with actual source channels and prove off-real
analytic continuation. By `(10)`--`(12)`, continuation remains sufficient for RH and cannot be
faked by gauge choice, characteristic normalization, zero multiplicity, or channel cancellation.

## Lean status

Formalized declarations:

```text
suzukiCrossSewnCharacteristic
suzukiCrossSewnIntervalPart
suzukiCrossSewnExterior
suzukiCrossSewnNormalizedExterior
suzukiCrossSewnExterior_eq_zeroShift
suzukiCrossSewnCharacteristic_independentGauge
suzukiCrossSewnIntervalPart_independentGauge
suzukiCrossSewnExterior_independentGauge
suzukiCrossSewnNormalizedExterior_independentGauge
suzukiCrossSewnNormalizedExterior_eq_zeroShift
analyticAt_suzukiCrossSewnCharacteristic
analyticAt_suzukiCrossSewnIntervalPart
suzukiCrossSewnCharacteristic_ne_zero_of_im_ne_zero
suzukiCrossSewnCharacteristic_zero_im
riemannHypothesis_iff_suzukiExteriorRemainder_analytic_offReal_of_realZeros
riemannHypothesis_iff_suzukiCrossSewnExterior_analytic_offReal
riemannHypothesis_iff_suzukiCrossSewnNormalizedExterior_analytic_offReal
meromorphicOrderAt_suzukiCrossSewnExterior_eq_neg_one
meromorphicTrailingCoeffAt_suzukiCrossSewnExterior
meromorphicOrderAt_suzukiCrossSewnNormalizedExterior_eq_neg_one
meromorphicTrailingCoeffAt_suzukiCrossSewnNormalizedExterior
```

Direct Lean checks of new module, SOTA ledger, and RHTower umbrella pass. Formal lint passes.
Exact module build passes (`8994/8994`). Axiom audit of every theorem reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Log

- 2026-07-21 — corpus audit falsified common-`W` source interpretation; cross-sewn product
  conjecture entered Stage 1.
- 2026-07-21 — conjecture survived source, algebra, divisor, analytic, gauge, pole, totalization,
  and novelty tests. Paper proof dependency-closed; promoted to Stage 2.
- 2026-07-21 — complete theorem package formalized in Lean; direct checks, lint, exact build, and
  axiom audit pass. Promoted to Stage 3.
