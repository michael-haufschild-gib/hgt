# Reflected-Gaussian source grade and resolved singular admission

- **ID:** `deninger-meyer-reflected-gaussian-resolved-admission`
- **Stage:** 3-formalized
- **Type:** SOURCE CONSTRUCTION / SINGULAR ADMISSION / RESOLVED CONSERVATIVITY
- **Status:** `[LOCAL-RESEARCH] [PAPER PROOF COMPLETE] [LEAN-PROVED]`
- **Parent:** `../1-in-progress/deninger-meyer-gaussian-green-resolvent.md`
- **Publication context:**
  `../4-publication-ready/riemann-hellinger-hodge-green-descent/main.tex`
- **Lean modules:**
  `../../../../formal/GaloisForLFunctions/RHTower/Deninger/DeningerMeyerReflectedGaussianHorizonAdmission.lean`
  and
  `../../../../formal/GaloisForLFunctions/RHTower/Deninger/DeningerMeyerReflectedGaussianResolvedAdmission.lean`

## 1. Frontier closed by this result

The Gaussian--Gamma residue nonadmission theorem factors every diagonal admission into the forced
analytic inverse `W` and an independent square-summable horizon grade `h`:

```text
(h(q) W(q)) R(q) = h(q).
```

An arbitrary decaying `h` would be circular. This result constructs `h` before divisor restriction
from one fixed reflection-invariant Meyer source, proves its `ell^2` admission, carries the admitted
residue into actual cross-prime Calderon--Witt incidence, and proves that the resolved-provenance
coface quotient retains it at every displacement.

## 2. Source-defined horizon grade

Let `g_ref` be the fixed Paugam-invariant centered logarithmic Meyer Gaussian already constructed
in the source complex. Define

```text
h(q) = Mellin(g_ref)(rho_q).
```

This definition precedes Xi-divisor restriction: the divisor only evaluates the pre-existing
source Mellin transform. The exact source calculation gives

```text
h(q) = exp(-tau * xiSpectralPoint(q)^2),
tau = 1/(4*pi) > 0.
```

Hence `h(q)` never vanishes. Functional-equation reflection and line conjugation give

```text
h(Rq) = h(q),
h(Cq) = conjugate(h(q)).
```

The positive-time Xi heat summability theorem at time `2*tau` yields

```text
sum_q |h(q)|^2 < infinity.                         (1)
```

No zero location, RH, positivity, interpolation, or divisor-indexed choice enters this step.

## 3. Singular residue admission

Let `R(q)` be the forced completed Xi/Gamma residue and `W(q)` its unique analytic inverse from the
Gaussian singular source. Set

```text
d(q) = h(q) W(q),
x(q) = d(q) R(q).
```

The residue identity `W(q)R(q)=1` gives

```text
x(q) = h(q).                                      (2)
```

Equation (1) therefore makes `x` an honest completed Xi/source-jet vector. Because `h(q)` and
`W(q)` are nonzero for every divisor copy, the weighting is coefficient-faithful rather than a
support truncation.

## 4. Actual incidence and resolved conservation

Fix distinct arithmetic primes `p != q`, and let `w_pq` be the existing nonzero actual
Calderon--Witt cross-prime incidence witness. The coefficient-faithful completed incidence map sends
`x` to a vector `I_pq(x)`. At every Xi divisor copy `r`, its decoded source value is exactly

```text
sourceValue_r(I_pq(x)) = h(r) * w_pq != 0.        (3)
```

Thus neither completion nor incidence transport erases any coefficient.

Before codiagonalization, the resolved source defect is

```text
Delta_r = (h(r) w_pq, -h(r) w_pq) != 0.           (4)
```

Its raw codiagonal is zero:

```text
Sigma_2(Delta_r) = 0.                             (5)
```

Equation (5) proves again that scalarized Green covariance cannot certify conservation. The
resolved-provenance lift instead inserts the unchanged incidence vector as `(0,I_pq(x))` before
forming adjacent cofaces. Those cofaces have zero provenance, so projection to `I_pq(x)` descends
through their closed span. The descended projection is a left inverse of the quotient source map:

```text
P_a(Q_a(I_pq(x))) = I_pq(x)                       (6)
```

for every displacement `a`. Equations (3) and (6) imply

```text
Q_a(I_pq(x)) != 0                                (7)
```

for every `a`. This is the required resolved, pre-codiagonal conservation of the admitted fixed
source packet.

## 5. Hostile audit

### Arbitrary heat damping

Rejected. `h` is not selected after inspecting the Xi divisor; it is the Mellin transform of one
fixed reflected Meyer cohomology class. Its reflection and conjugation laws are source theorems.

### Reusing a downstream `ell^2` norm

Rejected. Square summability follows from the explicit positive-time heat trace of the fixed source.
The incidence completion is used only after admission has been proved.

### Declaring codiagonal covariance sufficient

False. The admitted source has a nonzero antidiagonal defect whose codiagonal is exactly zero.
Resolved provenance, not codiagonal cancellation, retains the packet.

### Claiming RH or Hermitian descent

Rejected. The construction proves survival, not vanishing, of the resolved class. It does not yet
identify this completed source vector with the actual global Green resolved range, nor prove the
source Gram domination that would force the RH-bearing class to vanish.

## 6. New scientific content and remaining frontier

The independent horizon grade demanded by Gaussian-residue nonadmission is no longer missing. One
fixed reflected Meyer source supplies it, and its admitted singular packet survives actual
Calderon--Witt incidence and resolved Hellinger--Gamma quotienting without coefficient loss.

Subsequent exact range classification proves that the vector is not in the current compact-dual
comparison Green range: that range consists exactly of finite-support Xi vectors, whereas this
vector is nonzero at every copy of the infinite Xi divisor.  It lies in the closure of the range.
See `deninger-meyer-reflected-gaussian-green-range-wall.md`.

Route L therefore has three ordered coupled gates:

1. construct the source-native nonlocal completion forced by this closure-without-range wall and
   extend finite oriented Green transport to it;
2. identify its compatible resolved range with the closed adaptive prime-normal source range;
3. derive Hermitian Gram domination on that common range from prime/Gamma/co-Poisson structure.

The second is the first remaining arithmetic range theorem; the third is the RH-bearing
polarization theorem.  Neither can be replaced by another arbitrary damping weight or positivity
assumed on the divisor side.

## 7. Lean certificate

Headline theorems:

- `summable_norm_sq_reflectedGaussianHorizonGrade`
- `reflectedGaussianHorizonAdmissionWeight_mul_packet`
- `summable_reflectedGaussianHorizonAdmissionPacket`
- `reflectedGaussianHorizonAdmittedResidue_apply`
- `reflectedGaussianHorizonAdmittedIncidence_sourceValue_ne_zero`
- `reflectedGaussianHorizonAdmittedResolvedDefect_ne_zero`
- `reflectedGaussianHorizonAdmittedResolvedDefect_codiagonal`
- `reflectedGaussianHorizonAdmittedResolvedClass_projection`
- `reflectedGaussianHorizonAdmittedResolvedClass_ne_zero`

All statements are unconditional.

## Log

- 2026-08-03 -- Constructed reflected-Gaussian source horizon grade and proved square summability.
- 2026-08-03 -- Admitted forced singular residue and transported it coefficient-faithfully into
  actual Calderon--Witt incidence.
- 2026-08-03 -- Proved nonzero unsquared resolved defect, exact codiagonal loss, and split-injective
  survival in the resolved Hellinger--Gamma quotient at every displacement.
