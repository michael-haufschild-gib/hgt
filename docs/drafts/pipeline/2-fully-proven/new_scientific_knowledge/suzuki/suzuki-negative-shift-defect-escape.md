# Suzuki negative-shift defect escape

- **ID:** `suzuki-negative-shift-defect-escape`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / SUZUKI SCREW ROUTE / SHIFT-SELECTION NO-GO
- **Scientific status:** `[PAPER-PROVED] [CANDIDATE NEW SOURCE-SPECIFIC NO-GO]`
  `[GENERIC INPUTS KNOWN] [PRIORITY UNVERIFIED] [NOT AN RH PROOF] [NO NUMERICAL EVIDENCE]`
- **Primary source:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096v1 (2026), Theorem 1.5 and the discussion after Corollary 1.6.
- **Statement:** For every cofinal aperture sequence, admissible shifts can be chosen sufficiently
  negative that Suzuki's canonically anchored Livsic quotients converge locally uniformly to zero
  on the upper half-plane.  Therefore noncollapse and shift independence cannot hold uniformly
  over all shifts below the restricted Weil floor.

## Exact source family

For fixed `a>0`, let `A_a` be Suzuki's lower-bounded self-adjoint restricted Weil operator and let
`lambda_a=inf spec(A_a)`.  For `lambda<lambda_a`, put

```text
T_(a,lambda)=A_a-lambda I,
v_(a,lambda,+)=T_(a,lambda)^(-1) exp(x),
v_(a,lambda,-)=T_(a,lambda)^(-1) exp(-x).
```

Parity gives `v_- (x)=v_+(-x)`.  With

```text
F_(a,lambda)(z)=integral_(-a)^a v_(a,lambda,+)(x) exp(izx) dx,
```

the finite-aperture Livsic carrier already isolated in the project is

```text
Theta_(a,lambda)(z)
 =((z-i)F_(a,lambda)(z))/((z+i)F_(a,lambda)(-z)).        (1)
```

Suzuki's all-angle reality theorem makes `(1)` Schur on the upper half-plane and anchors it by
`Theta_(a,lambda)(i)=0`.

## Negative-shift escape theorem `[PAPER-PROVED]`

Let `a_n -> infinity`.  Then there exist `lambda_n<lambda_(a_n)` such that

```text
Theta_(a_n,lambda_n) -> 0                                (2)
```

locally uniformly on the upper half-plane.

The proof has three dependency-closed steps.

1. For fixed `a`, write `lambda=-r`.  The standard lower-bounded self-adjoint resolvent law gives

   ```text
   r(A_a+rI)^(-1)f -> f in L2(-a,a),       r->infinity. (3)
   ```

   Applied to `exp(+x)` and `exp(-x)`, Fourier Cauchy--Schwarz upgrades `(3)` locally uniformly in
   `z`.  The common factor `r` cancels from `(1)`.

2. The limiting free-interval carrier is exactly

   ```text
   Theta_a^free(z)
    =(exp(-2a)-exp(2iaz))/(1-exp(-2a)exp(2iaz)).          (4)
   ```

   On every compact `K` in the upper half-plane, if
   `delta=min_(z in K) Im z>0`, then

   ```text
   sup_K |exp(2iaz)| <= exp(-2a delta),
   sup_K |Theta_a^free|
    <= (exp(-2a)+exp(-2a delta))
       /(1-exp(-2a)exp(-2a delta)) -> 0.                 (5)
   ```

3. Choose an exhaustion `K_1 subset K_2 subset ...` of the upper half-plane.  For each `n`, use
   `(3)` at aperture `a_n` to choose `lambda_n` so negative that

   ```text
   sup_(K_n)|Theta_(a_n,lambda_n)-Theta_(a_n)^free|<1/n.
   ```

   Equations `(5)` and the exhaustion prove `(2)`.

## Defect-angle survivor

The first anchored jet has an exact source meaning.  Define

```text
kappa_(a,lambda)=2i Theta'_(a,lambda)(i).                 (6)
```

Direct differentiation of `(1)` gives

```text
kappa_(a,lambda)
 =F_(a,lambda)(i)/F_(a,lambda)(-i)
 =<v_-,v_+>_T/||v_+||_T^2.                              (7)
```

Writing `v_e=(v_++v_-)/2` and `v_o=(v_+-v_-)/2`, parity makes these the even and odd defect
components and gives

```text
kappa_(a,lambda)
 =(||v_e||_T^2-||v_o||_T^2)
  /(||v_e||_T^2+||v_o||_T^2),       |kappa|<1.           (8)
```

Thus the first obstruction to collapse is a normalized even--odd defect-energy imbalance, not the
restricted Weil floor itself.  For the free carrier,

```text
kappa_a^free=2a/sinh(2a) -> 0.                           (9)
```

A nonzero lower bound for `|kappa|` is a sufficient source-side noncollapse certificate.  It is not
necessary: a nonzero Schur limit may have a higher-order zero at `i`.  The full necessary-and-
sufficient certificate is survival of some fixed anchored derivative order.

## Positive survivor: projective defect compactification

The negative-shift theorem exposes a positive carrier rather than only a failed quantifier.
Multiplying a positive source operator `T` by any scalar `c>0` sends its normalized deficiency
vectors to `v_+/c,v_-/c`.  Both Fourier terms in `(1)` acquire the same factor `1/c`, so

```text
Theta_(cT)=Theta_T.                                      (10)
```

Thus the finite-aperture carrier lives on the **projective positive resolvent ray** of `T`, not on
its absolute scale.  The normalized two-defect Gram state is

```text
G_def(T)
 =1/(2N) [[N,C],[C,N]],
N=||v_+||_T^2=||v_-||_T^2,
C=<v_-,v_+>_T.                                          (11)
```

It is invariant under `(10)`.  Its parity eigenvectors are `(1,1)` and `(1,-1)`, with eigenvalues

```text
p_even=(1+kappa)/2=||v_e||_T^2/(||v_e||_T^2+||v_o||_T^2),
p_odd =(1-kappa)/2=||v_o||_T^2/(||v_e||_T^2+||v_o||_T^2). (12)
```

Hence `kappa` is not an arbitrary derivative: it is the signed polarization of a canonical
two-state defect density matrix.  The far-negative projective endpoint is the universal free
state, whose polarization is `(9)` and tends to zero cofinally.  The no-go therefore identifies an
actual boundary stratum in the moduli of Suzuki carriers.

There is an unconditional source-defined chart away from the arbitrary absolute shift.  For every
`tau>0`, choose

```text
lambda_a^(tau)=lambda_a-tau,
T_a^(tau)=A_a-lambda_a I+tau I.                          (13)
```

Then `lambda_a^(tau)<lambda_a` for every aperture, and the bottom of `T_a^(tau)` is exactly `tau`.
This **ground-centered projective family** exists without RH and cannot be confused with the
RH-bearing unshifted choice `lambda=0`.  It is the canonical family on which to ask the next
noncollapse question.

The forward research program forced by the theorem is therefore exact:

```text
ground-centered projective resolvents `(13)`
  -> prove survival of one fixed anchored defect jet
  -> identify the resulting nonzero Schur limit
  -> only then compare it with the global Xi/de Branges carrier. (14)
```

This replaces the false request for all-shift independence with a concrete, unconditional shift
selection and a measurable defect-survival invariant.  It does not assert that `(13)` already
survives cofinally; that is the new source-side problem.

## Hostile audit

1. **Normalization.** Suzuki's proof fixes the basis by
   `T v_+=exp(x)` and `T v_-=exp(-x)`, not merely by equal norms.  Hence the same positive scalar
   `r` multiplies both Fourier transforms and cancels from `(1)`.
2. **Quotient passage.** The free denominator in `(4)` is nonzero on the upper half-plane because
   `|exp(-2a)exp(2iaz)|<1`.  On a compact set it therefore has a positive minimum.  Suzuki's
   finite-shift denominators are nonzero there by the all-angle Hermite--Biehler theorem.  Uniform
   numerator and denominator convergence consequently gives uniform quotient convergence.
3. **First jet is not complete.** Aleman--Martin--Ross recall that arbitrary contractive analytic
   functions vanishing at `i` occur as Livsic functions if nondense symmetric relations are
   allowed.  In particular, higher powers of the Cayley factor show that `(7)` can vanish while
   the carrier is nonzero.  Only the full anchored jet criterion is necessary and sufficient.
4. **No circularity.** The shifts tend away from the RH-bearing value `lambda=0`; no positivity of
   `A_a` or assumption about the Weil floor is used.
5. **Exact scope.** The theorem refutes uniform noncollapse over all admissible shift schedules.  It
   does not by itself refute equality of a specially reparametrized finite-aperture spectrum, nor
   does it identify a viable canonical shift.

## Literature collision audit

The strong resolvent law `(3)`, the free differentiation model, and the general Livsic
characteristic-function formalism are classical.  Aleman--Martin--Ross (2012) give the general
Livsic representation and show that the characteristic function is a complete unitary invariant;
Belyi--Makarov--Tsekanovskii (2014) relate its Cayley transform to normalized Donoghue/Herglotz
functions.  These sources prevent novelty claims for `(3)`, `(4)`, or `(6)` separately.

Suzuki's June 2026 paper explicitly says that control of `lambda<lambda_a` is important and expects
shift independence in the positive regime, but it does not analyze the negative-shift end, derive
the free carrier `(4)`, identify the cofinal collapse `(2)`, or extract the parity defect angle
`(7)`--`(8)`.  Targeted searches of the cited Livsic/de Branges literature found no application of
this escape mechanism to Suzuki's screw family.  The exact source-specific no-go is therefore a
candidate new result pending specialist priority review.

## No-go closure

- **Exact killing mechanism:** the allowed half-line `lambda<lambda_a` contains arbitrarily
  negative shifts, where the source resolvent forgets `A_a` and approaches the free interval.
- **Strongest positive survivor:** the projective carrier law `(10)`, the defect Gram spectrum
  `(11)`--`(12)`, and the unconditional ground-centered chart `(13)`.  A viable cofinal family must
  retain a nontrivial anchored defect jet in that chart.
- **New insight:** the shift parameter is a projective compactification coordinate.  Arbitrary
  negative shifts hit the universal free boundary; the live route is ground-centered defect
  survival, not admissible-shift independence.
- **Status:** dependency-closed paper proof; generic parent theory classified as known; exact
  source-specific priority remains unverified.  The source operator is not yet represented in
  Lean, so only dependency-closed analytic survivors may enter Stage 3 separately.

## Gates

- [x] exact source formula and admissible shift half-line isolated
- [x] free carrier and proposed collapse estimate derived
- [x] defect-angle/parity formula derived
- [x] projective invariance and defect Gram spectrum derived
- [x] unconditional ground-centered shift chart isolated
- [x] hostile paper-proof audit closed
- [x] primary-literature collision audit closed at the source-specific level
- [x] dependency-closed projective/free-boundary survivor formalized in Lean
- [ ] concrete restricted-Weil resolvent escape theorem formalized in Lean
- [ ] source-side defect-retaining shift selected
- [ ] RH

## Log

- 2026-07-21 — created after the arbitrary-shift noncollapse conjecture failed, promoted to Stage
  2 after the paper proof closed, and connected to the separately formalized projective Gram,
  parity, ground-chart, and compact-open free-boundary survivors in
  `SuzukiProjectiveDefectBoundary.lean`.
