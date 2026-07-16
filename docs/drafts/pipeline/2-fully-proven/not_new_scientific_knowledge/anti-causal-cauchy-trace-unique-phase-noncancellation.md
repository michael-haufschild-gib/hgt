# The unweighted anti-causal Cauchy trace is the unique phase-noncancelling Hankel energy

- **ID:** `anti-causal-cauchy-trace-unique-phase-noncancellation`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / POSITIVE NO-GO RESIDUE
- **Scientific status:** `[PROVED HERE] [NOT A NOVELTY CLAIM] [NOT RH]`
- **Parents:**
  - `infinitesimal-euler-leakage-cauchy-energy-threshold.md`;
  - `../squarefree-fixed-current-right-half-ward-localization.md`;
  - `../../1-in-progress/source-polarized-laurent-pluecker-tangent-ward-law.md`.
- **Statement:** In the natural power-weighted Hankel energy scale of a finite right-half divisor,
  the unweighted `L2` trace is the unique nonnegative power for which every cross mode contributes
  positively for every pair of ordinates.  Standard Hilbert--Schmidt/Quillen energy has the wrong
  weight and cannot inherit the four-unit per-zero exclusion by discarding cross terms.

## Weighted divisor energies

Let

```text
ell(t)=2 sum_j m_j exp(-z_j t),
z_j=a_j+i gamma_j,
a_j>0,  m_j>0.                                           (1)
```

For `alpha>=0`, define

```text
E_alpha(ell)=integral_0^infinity t^alpha |ell(t)|^2 dt.   (2)
```

Termwise integration gives

```text
E_alpha(ell)
 =4 Gamma(alpha+1) sum_(j,k) m_j m_k
    Re[(z_j+conj(z_k))^(-(alpha+1))].                    (3)
```

Indeed, for `Re lambda>0`,

```text
integral_0^infinity t^alpha exp(-lambda t) dt
 =Gamma(alpha+1)lambda^(-(alpha+1)).                     (4)
```

## Unique entrywise positivity

Write

```text
z_j+conj(z_k)=r exp(i theta),       |theta|<pi/2.         (5)
```

Then the cross entry in `(3)` has sign

```text
sign cos((alpha+1)theta).                                 (6)
```

For `alpha=0`, one has `|theta|<pi/2`, hence

```text
Re[(z_j+conj(z_k))^(-1)]>0                               (7)
```

for every pair.  This is the strictly entrywise-positive Cauchy kernel used by the four-unit Ward
threshold.

For every `alpha>0`, choose

```text
pi/(2(alpha+1))<theta<min(pi/2,3pi/(2(alpha+1))).          (8)
```

The interval is nonempty, and `cos((alpha+1)theta)<0`.  Every angle in `(-pi/2,pi/2)` occurs as
`arg(x+iy)` with `x>0`.  Taking two divisor modes with `a_j+a_k=x` and
`gamma_j-gamma_k=y` therefore makes their cross entry in `(3)` negative.

Consequently:

> Among the power weights `t^alpha`, `alpha>=0`, the unweighted energy `alpha=0` is the unique
> energy whose Gram expansion is entrywise positive for every right-half divisor packet.

## Why this matters for the HT Ward route

For one mode of multiplicity `m`,

```text
E_0=2m^2/a.                                               (9)
```

Every nontrivial-strip displacement has `0<a<1/2`, so `(9)` is strictly greater than four.  Since
all cross entries are positive at `alpha=0`, the same lower bound survives in every multimode
packet.

The standard Hilbert--Schmidt norm of a Hankel operator with kernel `ell(x+y)` is instead

```text
||H_ell||_HS^2=integral_0^infinity t |ell(t)|^2 dt=E_1.  (10)
```

Its cross kernel is the square of the Cauchy denominator and can have negative real part.  Thus a
Quillen, restricted-Grassmannian, or determinant-line estimate controlling only `(10)` does not
yield the phase-independent diagonal lower bound `(9)`.

**No-go.**  The cofinal half-form BKS conjecture cannot stop at Hilbert--Schmidt implementability,
Quillen curvature, or an `E_1` bound.

**Positive successor.**  The required source-rigged quantization must have a genuine boundary
trace map into unweighted Hardy `L2`.  This explains why the escaping Pluecker tangent and its
source half-density are load-bearing: they must improve one half-order beyond ordinary determinant
geometry and retain the unique phase-noncancelling Cauchy trace.

## Anti-theatre verdict

The theorem does not prove that the source trace is bounded by four.  It proves that replacing the
trace by a more standard determinant/Hankel norm loses the exact no-cancellation property needed
for RH.  Any successful topological proof must therefore construct the unweighted trace itself,
not merely a nearby Sobolev or operator-ideal norm.

## Gates

- [x] all power-weighted energies computed
- [x] unweighted Cauchy cross entries proved strictly positive
- [x] every positive weight shown to admit a negative cross entry
- [x] Hilbert--Schmidt/Quillen weight identified as `alpha=1`
- [x] positive source-rigged boundary-trace successor stated
- [ ] construct that trace for the completed squarefree reciprocal-horizon seam
- [ ] prove its capacity-to-Hardy norm is at most one
