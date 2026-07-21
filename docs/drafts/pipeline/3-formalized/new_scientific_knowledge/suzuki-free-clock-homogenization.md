# Suzuki free boundary is clock-spectrum homogenization

- **ID:** `suzuki-free-clock-homogenization`
- **Stage:** 3-formalized
- **Type:** THEOREM / SUZUKI SCREW ROUTE / EXACT BOUNDARY CLASSIFICATION
- **Scientific status:** `[PAPER-PROVED] [FORMALIZED] [NOVELTY UNVERIFIED]`
  `[GENERIC TANGENT/HERGLOTZ THEORY KNOWN] [NOT AN RH PROOF] [NO NUMERICAL EVIDENCE]`
- **Primary source:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096v1 (2026), Theorem 1.5 and Sections 6--8.

## Exact claim

For `a>0`, let

```text
q_a=exp(-2a),
y_a(z)=exp(2iaz),
Theta_a^free(z)=(q_a-y_a(z))/(1-q_a y_a(z)),
m_a^free(z)=i(1+Theta_a^free(z))/(1-Theta_a^free(z)).       (1)
```

Then on the upper half-plane,

```text
m_a^free(z)=coth(a) tan(az).                                (2)
```

Its Nevanlinna measure is the exact half-integer clock

```text
mu_a=(coth(a)/a) sum_(k in Z) delta_((k+1/2)pi/a),           (3)
```

with zero affine constant and zero linear coefficient.  As `a->infinity`,

```text
mu_a -> dx/pi vaguely,
m_a^free -> i locally uniformly on Im z>0.                  (4)
```

At the opposite Suzuki boundary, the Cayley Livsic carrier

```text
Theta_edge(z)=(z-i)/(z+i)                                  (5)
```

has normalized Herglotz transform

```text
m_edge(z)=z.                                                (6)
```

In the Nevanlinna representation, `(6)` has zero finite measure and unit linear coefficient:
all normalized spectral mass lies at the projective point at infinity.  Thus Suzuki's two
universal shift boundaries erase arithmetic by different exact mechanisms:

```text
far-negative end -> equally weighted clock atoms homogenize to Lebesgue measure,
simple ground end -> finite spectral mass escapes to the linear point at infinity. (7)
```

## Proof

### 1. Exact Cayley algebra

On `Im z>0`, `|y_a(z)|=exp(-2a Im z)<1`, while `0<q_a<1`; every denominator below is nonzero.
Direct algebra gives

```text
1+Theta_a^free
 =[(1-q_a y_a)+(q_a-y_a)]/(1-q_a y_a)
 =(1+q_a)(1-y_a)/(1-q_a y_a),

1-Theta_a^free
 =[(1-q_a y_a)-(q_a-y_a)]/(1-q_a y_a)
 =(1-q_a)(1+y_a)/(1-q_a y_a).                              (8)
```

Therefore

```text
m_a^free(z)
 =i (1+q_a)/(1-q_a) (1-y_a(z))/(1+y_a(z)).                (9)
```

The elementary exponential identities

```text
(1+exp(-2a))/(1-exp(-2a))=coth(a),
i(1-exp(2iaz))/(1+exp(2iaz))=tan(az)                      (10)
```

turn `(9)` into `(2)`.  At `z=i`, `(2)` gives

```text
m_a^free(i)=coth(a) i tanh(a)=i,                          (11)
```

matching the canonical Suzuki normalization.

### 2. Exact clock measure

The poles of `tan(az)` are the simple real points

```text
x_(a,k)=(k+1/2)pi/a,       k in Z,                        (12)
```

and its residue at each pole is `-1/a`.  Hence the residue of `m_a^free` is
`-coth(a)/a`.  In the Nevanlinna convention

```text
m(z)=alpha z+b+
 integral_R [1/(t-z)-t/(1+t^2)] dmu(t),                  (13)
```

an atom of mass `w` at `t` has residue `-w`.  Thus `(3)` is the only possible finite-plane
measure.  Oddness gives `b=0`.  Along the positive imaginary axis,

```text
m_a^free(iy)=i coth(a)tanh(ay)=O_a(1),       y->infinity,
```

so `alpha=0`.  Uniqueness in the Nevanlinna representation proves `(3)` exactly.  Equation
`(11)` equivalently states the normalized Poisson-mass identity

```text
sum_(k in Z) [coth(a)/a]/[1+x_(a,k)^2]=1.                 (14)
```

### 3. Homogenization

Let `phi` be continuous with compact support and put `h=pi/a`.  Equation `(3)` gives

```text
integral phi dmu_a
 =coth(a)/pi * h sum_(k in Z) phi(h(k+1/2)).              (15)
```

Only finitely many summands meet the support of `phi`.  Midpoint Riemann sums converge to
`integral_R phi(x)dx`, and `coth(a)->1`.  Hence `(15)` tends to

```text
(1/pi) integral_R phi(x)dx,                              (16)
```

which is `(4)` at the measure level.  The measure `dx/pi` has normalized Nevanlinna transform
`i` on the upper half-plane.  Alternatively, local uniform convergence follows immediately from
`Theta_a^free->0` and the Cayley formula in `(1)`.

### 4. Ground endpoint

For `z!=-i`, direct Cayley inversion gives

```text
i [1+(z-i)/(z+i)]/[1-(z-i)/(z+i)]=z.                     (17)
```

This is `(6)`.  In `(13)`, `m(z)=z` is exactly `alpha=1`, `b=0`, `mu=0`.  Thus `(7)` compares
two distinct boundary mechanisms, not two descriptions of the same collapse.

## Hostile attacks

1. **Generic theory is classical.**  Tangent is a standard meromorphic Herglotz function; its
   clock poles and residues, the Nevanlinna representation, and vague convergence of uniform
   lattices are parent theory.  Candidate new content is only the exact identification of
   Suzuki's free projective carrier with this clock law and its comparison with the ground-edge
   mass-at-infinity law.
2. **No divisor transport is claimed.**  Convergence of Herglotz transforms on the open upper
   half-plane does not by itself preserve boundary atoms.  In fact `(3)--(4)` exhibit their
   homogenization explicitly.
3. **No RH positivity is hidden.**  The free representative is the already proved far-negative
   projective boundary.  The calculation uses only `a>0`; it never chooses the RH-bearing shift
   `lambda=0`.
4. **Leakage is not sufficient.**  A measure can be neither `dx/pi` nor mass at infinity and still
   have finite support, mixed continuous spectrum, or the wrong infinite divisor.  Avoiding the
   two exact endpoints is only a necessary first separation.
5. **The target topology is stronger.**  A successful Suzuki limit must prevent both vague
   homogenization and escape to the linear term, while retaining a tight infinite atomic divisor.
   A single defect angle or finite Schur prefix cannot certify that.

## Positive survivor and new frontier

The leakage number from `suzuki-ground-edge-cayley-universality.md` controls the first disk moment.
Equations `(2)--(7)` show that the true intermediate-window invariant is the complete normalized
Nevanlinna decomposition:

```text
linear mass at infinity
  + finite-plane spectral measure
  + spectral type and infinite atomic support.            (18)
```

For a divisor-bearing Suzuki schedule one must prove, on the same cofinal sequence:

```text
linear coefficient -> 0,                                 (no ground escape)
finite-plane measures do not approach dx/pi,             (no clock homogenization)
a tight infinite atomic component survives,              (no finite/continuous collapse)
its atoms and weights identify the Xi/de Branges divisor. (arithmetic weld) (19)
```

This replaces “keep `rho_a(tau_a)` nonzero” by a measure-level source target.  Nonzero leakage is
only the first-moment shadow of `(19)`.

## Literature and priority audit

- Suzuki constructs the all-angle finite-aperture characteristic family and states that shift
  control is part of the open problem, but does not identify `(2)`, `(3)`, or `(7)`.
- Tangent as a Nevanlinna--Herglotz function with an equal-weight lattice measure is classical.
- Livsic/de Branges and Clark-measure theory classically identify self-adjoint extension spectra
  with boundary measures of inner characteristic functions.
- Searches through 2026-07-21 found no Suzuki follow-up deriving the free clock measure or the
  two-mechanism boundary classification.  This is evidence only; source-specific priority remains
  unverified.

## Formalization

`formal/GaloisForLFunctions/RHTower/SuzukiHerglotzBoundaryStates.lean` proves unconditionally:

- the exact identity `(2)` on the upper half-plane;
- the exact half-integer clock denominator `(12)`;
- the canonical anchor `m_a(i)=i`;
- the locally uniform transform limit in `(4)`;
- connection to the already formalized opposite Cayley identity `(6)`.

`[OPEN CORE]` The measure-valued statements `(3)--(4)` remain on paper.  Add them to Lean only
when the existing locally finite measure infrastructure can express the genuine infinite clock
sum and vague convergence without replacing either by an abstract wrapper.

## Gates

- [x] internal Suzuki and Schur/Herglotz corpus audited
- [x] exact free Cayley transform derived
- [x] clock poles, residues, and Nevanlinna parameters derived
- [x] vague homogenization proof closed on paper
- [x] opposite mass-at-infinity boundary identified
- [x] RH circularity and topology attacks recorded
- [x] current source and literature search completed
- [x] hostile normalization audit closed
- [x] dependency-closed transform theorem formalized in Lean
- [ ] specialist novelty review
- [ ] source proof of tight infinite atomic retention
- [ ] Xi divisor identification
- [ ] RH
