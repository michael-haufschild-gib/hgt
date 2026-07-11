# Additive heat aperture has an infinite shifted-zeta echo ladder

- **ID:** `additive-heat-aperture-shifted-zeta-echo-ladder`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper); coefficient laws formalized in Lean
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** The small-aperture expansion of the additive heat energy contains one complex
  channel for every backward zeta value `zeta(s-k)`; at a nontrivial zeta zero exactly the zeroth
  rung disappears and every later rung is provably nonzero.

## Source observable

For `s=sigma+it` with `1/2<sigma<1`, let

```text
Psi_s(n)=n^(-s)/sqrt(zeta(2sigma)),
H_x(m,n)=exp(-pi x(m-n)^2),
E_s(x)=<Psi_s,H_x Psi_s>.
```

The value `E_s(x)` is finite and strictly positive for every `x>0`. The first heat-aperture theorem
identifies its leading singular value, zeroth complex echo, and finite part. This card gives the
complete complex echo family.

## Echo-ladder theorem `[PROVED HERE]`

There are real-channel coefficients `D_m(s)` such that the full polyhomogeneous expansion has the
form

```text
zeta(2sigma)E_s(x)
 ~ L(s)x^(sigma-1)
   +sum_(k>=0) [
       C_k(s)conj(zeta(s-k))x^((s+k-1)/2)
       +conj(C_k(s)conj(zeta(s-k))x^((s+k-1)/2))]
   +sum_(m>=0) D_m(s)x^m.                              (1)
```

Here `D_0(s)=|zeta(s)|^2`, and the exact archimedean echo coefficient is

```text
C_k(s)
 = Gamma(1-s) sin(pi(s+k)/2)
   (4pi)^((s+k-1)/2) Gamma((s+k)/2)
   /(k! sqrt(pi)).                                     (2)
```

For `t!=0`, the echo exponents have imaginary parts `+t/2` and `-t/2`, while the regular ladder
has real integer exponents, so every coefficient in (1) is intrinsically identifiable. For real
`s` in the strip, the echo exponents are nonintegral and remain distinct from the regular ladder.

More precisely, truncating the complex echo sum after `k=N` leaves a singular--regular remainder
of order `O_s(x^((sigma+N)/2))`; the smooth regular square has its ordinary integer-power heat
expansion.

## Proof

The boundary polylogarithm has the convergent local expansion

```text
f_s(theta)
 =Gamma(1-s)(-i theta)^(s-1)
  +sum_(k>=0) zeta(s-k)(i theta)^k/k!                 (3)
```

for `|theta|<2pi`. Put

```text
A_+(s)=Gamma(1-s)exp(-i pi(s-1)/2),
A_-(s)=Gamma(1-s)exp(+i pi(s-1)/2).
```

On the positive side, the coefficient of the singular term times the conjugate of the `k`-th
regular term is

```text
A_+(s)(-i)^k conj(zeta(s-k))/k!.
```

On the negative side it is

```text
A_-(s)i^k conj(zeta(s-k))/k!.
```

The heat kernel is even, so the averaged phase factor is

```text
[A_+(s)(-i)^k+A_-(s)i^k]/2
 =Gamma(1-s)sin(pi(s+k)/2).                            (4)
```

The Gaussian moment

```text
integral W_x(theta)|theta|^(s+k-1)dtheta/(2pi)
 =(4pi x)^((s+k-1)/2)Gamma((s+k)/2)/sqrt(pi)
```

then gives (2) and the `k`-th complex channel in (1). Taylor expansion of the smooth regular
square gives the real integer-power coefficients `D_m(s)`. Termwise truncation of (3), followed by
the same Gaussian moment bound, gives the stated remainder and hence the full expansion.

## Archimedean two-step law `[PROVED HERE]`

The coefficients satisfy

```text
C_(k+2)(s)
 =-[2pi(s+k)/((k+1)(k+2))] C_k(s).                    (5)
```

This follows immediately from

```text
sin(pi(s+k+2)/2)=-sin(pi(s+k)/2),
Gamma((s+k+2)/2)=((s+k)/2)Gamma((s+k)/2),
(k+2)!=(k+2)(k+1)k!.
```

Thus the even and odd echo values are each generated from one initial coefficient by exact
rational multipliers in `s`.

Writing `(a)_m` for the rising Pochhammer symbol, iteration of (5) gives the closed parity laws

```text
C_(2m)(s)
 =C_0(s)(-1)^m(4pi)^m(s/2)_m/(2m)!,

C_(2m+1)(s)
 =C_1(s)(-1)^m(4pi)^m((s+1)/2)_m/(2m+1)!.            (5a)
```

Hence the complete archimedean ladder is determined by the two values `C_0,C_1`.

## Single-missing-rung law `[PROVED HERE]`

Every `C_k(s)` is nonzero in the open critical strip. Indeed, Gamma has no zeros, its displayed
arguments have positive real part where needed, and `sin(pi(s+k)/2)=0` would force `s+k` to be an
even integer, which is incompatible with `1/2<Re(s)<1`.

For every `k>=1`,

```text
zeta(s-k)!=0.                                          (6)
```

To prove (6), put `w=s-k`. The functional equation expresses `zeta(w)` as nonzero archimedean
factors times `zeta(1-w)`. Since `Re(1-w)>1`, the Euler product gives `zeta(1-w)!=0`; the open-strip
condition excludes negative even `w`, because such a value would force `Re(s)` to be an integer.

Consequently,

```text
zeta(s)=0
 iff
the k=0 complex echo is absent and every k>=1 echo is present. (7)
```

The first surviving value is the previously recorded tangent `i zeta(s-1)`. Formula (7) upgrades
that tangent to an infinite, recursively weighted nonvanishing ladder.

## Law developed from the relation

The heat aperture separates the zeta divisor from all backward shifts of that divisor. A
nontrivial zero is therefore an **isolated echo defect** in parameter depth: it removes exactly one
coefficient from a source-defined infinite family and leaves the entire tail nonzero.

For RH, the law gives a canonical measurement vocabulary:

```text
RH
 iff
every isolated zeroth-rung defect in the critical strip occurs at sigma=1/2. (8)
```

Equation (8) is a faithful measurement reformulation, not a proof of localization. Its new content
is the rigidity of the tail: no backward-shift cancellation can imitate the zeroth-rung defect.

## Novelty audit

The parent ingredients are classical: Jonquière's expansion, the zeta functional equation,
Poisson summation, and Gaussian moments. Searches across polylogarithm heat asymptotics, periodic
zeta Gaussian summability, zeta heat kernels, shifted zeta values, and additive heat regularization
found these ingredients separately. No located source states the full channel expansion (1), the
coefficient recurrence (5), or the single-missing-rung law (7) for this positive quadratic
observable.

Connes's zeta-zero heat trace and general zeta/heat-kernel literature concern spectral traces or
Mellin transforms, rather than this additive Toeplitz heat energy of the normalizable vector
`n^(-s)`. The candidate-new label remains provisional pending independent expert comparison.

## Lean certificate

The module

```text
formal/GaloisForLFunctions/RHTower/HeatApertureEchoLadder.lean
```

formalizes the actual coefficients (2) and proves

```text
heatApertureEchoCoeff_add_two
heatApertureEchoCoeff_ne_zero
riemannZeta_sub_nat_ne_zero_of_criticalStrip
```

The targeted build passes. Each final theorem depends only on Lean's standard `propext`,
`Classical.choice`, and `Quot.sound` axioms. The positive additional value for a complete Lean
formalization of (1) is the local polylogarithm expansion with a Gaussian asymptotic-integration
theorem.

## Gates

- [x] exact infinite value family isolated
- [x] complete paper proof of the echo expansion
- [x] coefficient recurrence and nonvanishing proved
- [x] shifted-zeta tail nonvanishing proved
- [x] core coefficient and zeta-value laws formalized in Lean
- [x] targeted build and axiom audit pass
- [x] focused literature collision search
- [ ] formalize Jonquière expansion and Gaussian asymptotic integration
- [ ] independent specialist novelty audit

## References checked

- A. Jonquière, *Note sur la série `sum x^n/n^s`*, Bulletin de la Société Mathématique de France
  17 (1889), 142--152.
- NIST DLMF §25.12, especially the local polylogarithm expansion 25.12.12.
- J. Lagarias and W.-C. Winnie Li, *The Lerch Zeta Function III: Polylogarithms and Special
  Values*, Research in the Mathematical Sciences 3 (2016).
- A. Connes, *Heat Expansion and Zeta*, arXiv:2402.13082, for comparison with a different
  zeta-zero heat observable.

## Log

- 2026-07-11 -- Expanded the single echo to the complete shifted-zeta ladder, proved the two-step
  archimedean recurrence and single-missing-rung law, completed a focused novelty search, and
  formalized the coefficient and shifted-zeta nonvanishing theorems.
