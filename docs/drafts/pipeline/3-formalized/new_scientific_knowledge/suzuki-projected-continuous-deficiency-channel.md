# Suzuki projected continuous deficiency channels collapse to one sine clock

- **ID:** `suzuki-projected-continuous-deficiency-channel`
- **Stage:** 3-formalized
- **Type:** SOURCE CORRECTION / THEOREM / FRONTIER REDUCTION
- **Primary source:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096v1, Sections 8.2--8.3
- **Parents:** `suzuki-exterior-pole-tomography-neumann-boundary`,
  `suzuki-neumann-clock-annihilator`, `suzuki-admissible-two-shift-affine-sewing`
- **Lean:** `GaloisForLFunctions.RHTower.SuzukiProjectedContinuousDeficiency`
- **RH used:** no
- **Computation used:** no

## Actual frontier, before this theorem

The corpus has removed source-shift selection, gauge, pair choice, and characteristic-divisor
ambiguity.  Its remaining RH-bearing statement was:

```text
construct one affine-sewn exterior observable from two actual admissible
finite-aperture Suzuki source channels, independently of the Xi quotient,
and prove that its continuation is holomorphic at every nonreal point.       (F)
```

The interval/exterior split in `(F)` still used Suzuki's Section 8.3 passage from the projected
operator `G_a=P_aGP_a` to an unprojected convolution.  This theorem corrects that passage and
classifies the entire interval ambiguity exactly.

## 1. Projection correction

Let

```text
L0 = {u in L2(-a,a) : integral u=0},
G_a=P_a G P_a : L0 -> L0,
K_a=(-Delta_N)^(-1) : L0 -> L0,
S_(a,eta)=G_a-eta K_a.                                  (1)
```

Every ordinary `L2` value of `S_(a,eta)` has zero mean.  Section 8.3 prints

```text
S_(a,eta)v_+ = e^x+i,
S_(a,eta)v_- = e^(-x)-i.                                (2)
```

Neither right side has zero mean.  Thus `(2)` is not an equality in `L0`.  It can only be read as
an equality modulo constants in the dual of the zero-mean test space.  The raw TeX confirms the
origin of the issue: it defines `G_a=P_aGP_a`, then later writes the unprojected kernel `g(x-y)`
without the output projection.

Canonical zero-mean representatives of the exponential classes are

```text
e^x-s_a,       e^(-x)-s_a,
s_a=sinh(a)/a.                                           (3)
```

More generally, the canonical representative of `e^(-izx)` is

```text
e^(-izx)-m_a(z),
m_a(z)=(1/(2a)) integral_(-a)^a e^(-izt)dt.              (4)
```

The adjoint equation determines only the constant class.  It does not permit the exponential
coefficient and the inhomogeneous constant to be normalized independently.  If the exponential
coefficient is one, the constant forcing is `z m_a(z)`, not universally `1`.

This also resolves the printed comparison factor.  Formally applying `-d^2/dx^2` to `(4)` gives

```text
T_(a,eta)w_z=z^2 e^(-izx).                               (5)
```

Hence the factor is `z^2` whenever the domain comparison is legitimate; at `z=+-i` it is `-1`.
The printed `-lambda^2` has the opposite sign if `lambda` is the adjoint spectral variable and
cannot be the form shift.  Equation `(5)` is a diagnostic, not a claim that the compact
first-kind inverse maps these endpoint-nonsmooth data into ordinary `L2`.  The source itself notes
`H(S_a)` is not contained in `L2`, so no such unproved regularity is used below.

## 2. Exact global representative law

Put

```text
r0(x-y)=-|x-y|/2,
N_a(x,y)=(x^2+y^2)/(4a)-|x-y|/2+a/6.                    (6)
```

For a zero-mean source `v` and `M2(v)=integral y^2v(y)dy`, direct substitution gives

```text
K_a v=r0*v+M2(v)/(4a),                                  (7)
P_a(g*v)=g*v-avg_a(g*v).                                (8)
```

Therefore the global shifted convolution `k_eta*v=(g-eta r0)*v` satisfies on the interval

```text
k_eta*v=S_(a,eta)v+c_(a,eta)(v),
c_(a,eta)(v)=avg_a(g*v)+eta M2(v)/(4a).                 (9)
```

Only one scalar is lost by projection.  Reflection commutes with `S_(a,eta)`, `g`, `r0`, and
`K_a`.  Normalize the two deficiency classes by reflection.  Their global interval
representatives consequently have the form

```text
h_+(x)=e^x+c,
h_-(x)=e^(-x)+c                                         (10)
```

with the same scalar `c`.  No value or estimate for `c` is needed.

## 3. The projected interval sine-clock theorem `[PROVED HERE]`

Use Fourier convention

```text
F_+(z)=integral_(-a)^a h_+(x)e^(ixz)dx,
F_-(z)=integral_(-a)^a h_-(x)e^(ixz)dx.                 (11)
```

More generally, suppose differentiable `h_+,h_-` and a scalar `c` satisfy

```text
h_+'-h_+=-c,
h_-'+h_-= c.                                            (12)
```

Then integration by parts gives

```text
(z-i)F_+
 =i integral(h_+'-h_+)e^(ixz)dx-i[h_+e^(ixz)]_(-a)^a,

(z+i)F_-
 =i integral(h_-'+h_-)e^(ixz)dx-i[h_-e^(ixz)]_(-a)^a.  (13)
```

At phase `q=+1`, the two bulk integrals cancel exactly.  If reflection makes the endpoint sums
equal to one scalar `A`,

```text
h_+(a)+h_-(a)=h_+(-a)+h_-(-a)=A,                        (14)
```

then `(13)` becomes

```text
(z-i)F_+(z)+(z+i)F_-(z)
 =-i A(e^(iaz)-e^(-iaz))
 =2A sin(az).                                           (15)
```

Thus the complete projected interval bracket is one sine clock.  The source's displayed
opposite constants produced a phase-`-1` cancellation; output projection and reflection show the
correct phase is `+1`.

For `a!=0` and `A!=0`, every zero of `(15)` is real.  In particular,

```text
Im z !=0  ->  2A sin(az)!=0.                            (16)
```

So the corrected interval term cannot cancel a hypothetical nonreal Xi pole.

## 4. Affine two-shift consequence

At one aperture, let the two admissible source shifts have endpoint scalars `A_alpha,A_beta`.
Their interval functions are

```text
I_alpha(z)=2A_alpha sin(az),
I_beta(z) =2A_beta  sin(az).                             (17)
```

The already proved arbitrary-target affine interval term therefore factors as

```text
J_(alpha,beta->gamma)(z)
 =2sin(az)
   [(beta-gamma)W_beta(z)A_alpha
    -(alpha-gamma)W_alpha(z)A_beta].                    (18)
```

This is the new source-identification gain.  The interval side is no longer an arbitrary entire
function and requires no aperture estimate: every projection choice is confined to two scalars,
and every sewn interval term carries the same explicit real-zero sine factor.  The actual
exterior distribution is obtained by subtracting `(17)` from the source-defined global shifted
convolution before any Xi quotient is used.

## 5. Decisive RH-proof test

The strongest attempted successor was:

> After removing the sine clock, the affine-sewn exterior quotient is a Hilbert-space Weyl
> function and is therefore holomorphic off the real axis.

This does not follow.  Positivity of each admissible `S_(a,eta)` controls only the compressed
interval metric.  The exterior Schur complement contains the uncompressed global screw kernel.
Its positivity is equivalent to RH.  Moreover, if the target lies outside the two source shifts,
one barycentric coefficient is negative, so generic Herglotz convexity is unavailable.  Calling
the exterior quotient a Weyl function would silently insert the theorem being proved.

This falsification is useful because it isolates the terminal problem without the previous
projection noise:

```text
source-defined global shifted convolutions
 -> subtract the explicit sine clocks (17)
 -> affine sew two admissible shifts
 -> prove the resulting exterior Schur complement is holomorphic off R
 -> RH.                                                  (19)
```

No shift-floor limit, arbitrary interval entire term, endpoint estimate, or phase choice remains
in `(19)`.

## Hostile audit

- [x] `G_a=P_aGP_a` and zero-mean range checked against raw v1 TeX.
- [x] Printed `(2)` rejected only as an ordinary `L0` equality; its quotient-by-constants reading
      is retained.
- [x] No `H(S_a) subset L2` regularity assumed.
- [x] Neumann correction `(7)` uses zero mean exactly where the `x^2` and constant terms vanish.
- [x] Reflection gives one common scalar in `(10)`.
- [x] Fourier signs in `(13)` checked with `d/dx e^(ixz)=iz e^(ixz)`.
- [x] Bulk cancellation occurs at `q=+1`; endpoint clock `(15)` checked without division by `z`.
- [x] Nonreal nonvanishing `(16)` uses the complete complex sine zero classification.
- [x] Affine factorization `(18)` proved before division by characteristics.
- [x] Hilbert-Weyl shortcut hostile-tested and rejected as circular.
- [x] Repository and primary-literature searches found no projected Suzuki sine-clock correction.

## Formalization

Lean proves the dependency-closed exact core:

```text
suzukiProjectedInteriorBracket_eq_boundary
suzukiProjectedInteriorBracket_eq_sineClock
suzukiProjectedSineClock_ne_zero_of_im_ne_zero
suzukiAffineSewnIntervalPart_projectedSineClock
```

The generalized deficiency-domain regularity and exterior Schur complement are deliberately not
represented by abstract placeholders.

## Gates

- [x] 0 -> 1: source-pure statement, exact source discrepancy, competing conjectures
- [x] 1 -> 2: projection, reflection, sine-clock, affine factorization, hostile proof test
- [x] 2 -> 3: direct Lean check, exact module build, lint, axiom audit, imports
- [ ] 3 -> 4: external referee-level novelty audit and standalone note

## Log

- 2026-07-21 -- printed ordinary Fredholm representatives rejected by zero-mean range.
- 2026-07-21 -- quotient-by-constants reading retained; canonical centering and reflection derived.
- 2026-07-21 -- phase `+1` bulk cancellation and exact sine-clock law proved.
- 2026-07-21 -- affine common-factor theorem proved; Hilbert-Weyl shortcut falsified as circular.
- 2026-07-21 -- dependency-closed exact core formalized; direct SOTA check, exact module build,
  formal lint, and axiom audit passed.
