# BV prime-window Laurent orientation polarization

- **ID:** `bv-prime-window-laurent-orientation-polarization`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[TOP-DOWN INTERFACE DISCHARGE]`, `[VALUE RELATION]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** the formal compact-BV prime-window quadrature, holomorphy, Dirichlet identity,
  meromorphic continuation, and divisor tomography;
  `burnol-copoisson-berezin-diagonal-reflection-law.md`
- **Statement:** The normalized Burnol bilateral-aperture orientation at every nontrivial zeta zero
  is exactly the forward-minus-inverse squared Laurent-residue norm of an explicit moving-prime
  Dirichlet series.  The canonical polar-renormalized source and its exact residues are now
  formalized.  A single fixed dyadic sharp window detects every right off-critical zero; a fixed
  countable, reflection-stable family of rational interval windows detects every zero fibre.

## 1. Prime-window source series

Let `W` be a complex compactly supported bounded-variation function on `(0,infinity)`, with support
bounded away from zero, and put

```text
M_W(s)=integral_0^infinity W(x)x^(-s)dx,

D_W(s)=sum_(n>=1) n^(-s)
         sum_(k>=1) Lambda(k)k^(-1/2)W(n/k).             (1)
```

The formal BV prime-window theorem proves on `Re(s)>3/2` that

```text
D_W(s)=-M_W(s) zeta'(s-1/2)/zeta(s-1/2)+E_W(s),         (2)
```

where `M_W` is entire and `E_W` is holomorphic on `Re(s)>1/2`.  Therefore the right side of `(2)`
is the canonical meromorphic continuation of `D_W` to that half-plane.

Let `rho` be a nontrivial zeta zero of multiplicity `m_rho`, and set

```text
s_rho=rho+1/2.
```

Since the logarithmic derivative has residue `m_rho` at `rho`, `(2)` gives the exact Laurent value

```text
R_W(rho):=Res_(s=s_rho) D_W(s)=-m_rho M_W(s_rho).       (3)
```

This is a source value: `D_W` is built from von Mangoldt weights and a finite multiplicative
window, while the continuation remainder is holomorphic and contributes no residue.

The formal corpus uses the canonically polar-renormalized coefficient

```text
p_W(N)=2M_W(3/2)sqrt(N)-2T_W(N),                         (3a)
```

and writes its meromorphic continuation as `Scal_W`.  At the same shifted zero its residue is

```text
calR_W(rho):=Res_(s=s_rho) Scal_W(s)
             =2m_rho M_W(s_rho).                        (3b)
```

Thus every formula below has a formally available polar-source version: replace `R` by `calR`
and multiply each squared-norm difference by `4`.  The sign and normalized orientation are
unchanged.

## 2. Forward and inverse window dilations

Fix `r>1` and define the unnormalized reciprocal dilations

```text
W_r^+(x)=W(rx),
W_r^-(x)=W(x/r).                                         (4)
```

Changing variables in the Mellin integral gives

```text
M_(W_r^+)(s)=r^(s-1)M_W(s),
M_(W_r^-)(s)=r^(1-s)M_W(s).                              (5)
```

Write

```text
lambda_r(rho)=r^(rho-1/2),
R_+(rho)=R_(W_r^+)(rho),
R_-(rho)=R_(W_r^-)(rho).                                 (6)
```

Equations `(3)`--`(5)` imply

```text
R_+(rho)=-m_rho M_W(s_rho) lambda_r(rho),
R_-(rho)=-m_rho M_W(s_rho) lambda_r(rho)^(-1).           (7)
```

Consequently

```text
|R_+(rho)|^2-|R_-(rho)|^2
 =m_rho^2 |M_W(s_rho)|^2
   (r^(2 Re(rho)-1)-r^(1-2 Re(rho))).                   (8)
```

For the canonical polar source, Lean's residue theorem gives in the same notation

```text
|calR_+(rho)|^2-|calR_-(rho)|^2
 =4m_rho^2 |M_W(s_rho)|^2
   (r^(2 Re(rho)-1)-r^(1-2 Re(rho))).                  (8a)
```

Equivalently, the same quantity is the Hermitian polarization

```text
Re ((R_+(rho)-R_-(rho)) conjugate(R_+(rho)+R_-(rho))).  (9)
```

When `M_W(s_rho)` is nonzero, division by the positive factor in `(8)` gives

```text
(|R_+(rho)|^2-|R_-(rho)|^2)
 /(m_rho^2 |M_W(s_rho)|^2)
 =2 sinh(2 log(r)(Re(rho)-1/2)).                         (10)
```

The right side of `(10)` is exactly the normalized Burnol co-Poisson Berezin value of the
bilateral aperture holonomy at `rho`.  Thus the abstract quotient orientation has an explicit
prime-window Laurent reader.

## 3. Exact source reflection

Define the reciprocal-conjugate window

```text
W#(x)=conjugate(W(1/x)).                                 (11)
```

It is again compact BV, and a second change of variables gives

```text
M_(W#)(s)=conjugate(M_W(2-conjugate(s))).                (12)
```

The window involution swaps reciprocal dilation:

```text
(W_r^+)#=(W#)_r^-,
(W_r^-)#=(W#)_r^+.                                      (13)
```

For the functional-equation reflection `rho#=1-conjugate(rho)`, one has
`s_(rho#)=2-conjugate(s_rho)` and `m_(rho#)=m_rho`.  Combining `(3)`, `(12)`, and `(13)` yields

```text
R_((W#)_r^-)(rho#)=conjugate(R_+(rho)),
R_((W#)_r^+)(rho#)=conjugate(R_-(rho)).                  (14)
```

Hence reflection negates the oriented residue norm difference.  Formula `(9)` may equivalently
be written as a bilinear pairing between the source residue at `rho` and the reflected source
residue at `rho#`; no zero-location hypothesis is used.

## 4. A countable separating source family

Let

```text
W_(a,b)=1_[a,b],  a,b positive rational, a<b.            (15)
```

This family is countable and consists of compact BV windows.  For every complex `s`, at least one
member has `M_W(s)!=0`: continuity of `x |-> x^(-s)` and its value `1` at `x=1` give a real
neighborhood of `1` on which its real part is positive; choose rational `a<b` inside that
neighborhood.  The integral over `[a,b]` then has positive real part.

For rational `r>1`, the operations `(4)` and `(11)` keep the endpoints rational.  Thus one fixed
countable prime-window source family, closed under all operations used above, detects the
orientation at every zero with no zero-dependent source adjoined to the family.

For the right-half-plane RH implication, even the countable choice is unnecessary.  Take the
fixed sharp window `W=1_[1,2]`.  Its Mellin transform

```text
M_W(s)=(2^(1-s)-1)/(1-s)                               (15a)
```

has all of its zeros on `Re(s)=1`, so it is nonzero at every `s_rho` with
`Re(rho)>1/2`.  With the fixed integer dilation `r=2`, the two explicit windows are
`1_[1/2,1]` and `1_[2,4]`, and

```text
calR_+(rho)/calR_-(rho)=2^(2rho-1).                    (15b)
```

## 5. Top-down consequence

For any nontrivial zero with `Re(rho)>1/2`, use the fixed dyadic sharp window above.  Equation
`(8a)` gives

```text
|calR_+(rho)|<=|calR_-(rho)|  ->  Re(rho)=1/2.           (16)
```

Therefore the following source theorem would imply RH:

```text
forward BV prime-window Laurent residue is contractive relative to
the inverse residue on every right-half nontrivial pole
  -> every right-half zero is critical by (8a)
  -> every zero is critical by functional-equation reflection
  -> RH.                                                 (17)
```

The gain is an exact interface discharge, not the sign itself.  The common horizontal charge is
now the difference of two explicit source-residue norms, and functional-equation reflection
literally swaps the two channels.  The remaining theorem is a prime-source Laurent contraction;
assuming it, or assuming the vanishing of `(8)`, would still be RH-bearing.

## 6. Formal and literature boundary

The following formal files prove the complete continuation and divisor-residue input:

- `formal/GaloisForLFunctions/RHTower/BVPrimeWindowQuadrature.lean`: compact BV Mellin transform
  and uniform first-order quadrature;
- `formal/GaloisForLFunctions/RHTower/BVPrimeWindowHolomorphy.lean`: entire Mellin transform and
  holomorphic prime-weighted error series on `Re(s)>1/2`;
- `formal/GaloisForLFunctions/RHTower/BVPrimeWindowDirichlet.lean`: identity `(2)` on the common
  half-plane of absolute convergence;
- `formal/GaloisForLFunctions/RHTower/BVPrimeWindowContinuation.lean`: the polar coefficient
  `(3a)`, its ordinary Dirichlet series, and the meromorphic `continuedSource` on `Re(s)>1/2`;
- `formal/GaloisForLFunctions/RHTower/BVPrimeWindowDivisorTomography.lean`: the exact residue
  `(3b)`, the Mellin-censorship pole-order theorem, and the fixed-window RH holomorphy criterion.

These modules are wired through `formal/GaloisForLFunctions/RHTower.lean`.
`BVPrimeWindowDilationOrientation.lean` now constructs the forward and inverse compact-BV
windows, proves their exact Mellin and continued-source residue covariance, and formalizes the
oriented squared-norm comparison `(8a)`--`(10)`, including its strict sign and zero locus.  The
reciprocal-conjugate window involution `(11)`--`(14)` remains paper-level.

Burnol's source-defined co-Poisson quotient and its zero evaluators are supplied by
J.-F. Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta
function*, J. Theor. Nombres Bordeaux 16 (2004), 65--94, especially Theorem 3.1.  The Laurent
calculation itself is the elementary residue consequence of `(2)`.

The exact finite-coefficient provider behind the missing contraction is proved in
`bv-prime-window-polar-coefficient-decimation-law.md`.  Its live scale-zero boundary construction
is `../../1-in-progress/bv-prime-window-decimation-boundary-contraction-rh.md`.

## Gates

- [x] exact BV prime-window Dirichlet identity located in the live formal corpus
- [x] formal meromorphic continuation and Laurent residue formula for the canonical polar source
- [x] forward/inverse dilation residue law
- [x] exact squared-norm polarization of the Burnol aperture orientation
- [x] exact reciprocal-window/functional-equation reflection
- [x] one fixed dyadic sharp window detects every right off-critical zero
- [x] fixed countable rational interval family separates every zero fibre
- [ ] prove the right-half prime-source Laurent contraction `(16)`
- [x] formalize compact-BV forward and inverse dilation
- [ ] formalize reciprocal-conjugate window reflection
- [x] formalize the oriented comparison `(8a)`--`(10)`
- [ ] compose an unconditional source contraction to RH
