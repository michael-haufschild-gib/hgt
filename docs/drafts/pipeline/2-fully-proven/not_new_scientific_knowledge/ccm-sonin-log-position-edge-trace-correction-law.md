# The ordinary-position Fourier-cutoff leakage is a two-edge Sobolev trace bundle

- **ID:** `ccm-sonin-log-position-edge-trace-correction-law`
- **Stage:** 2-fully-proven / not-new
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** Fourier differentiation, Sobolev boundary traces,
  `critical-euler-position-commutator-carrier-law.md`, and the exact Sonin projection correction

## Coordinate scope

`[PROVED IN LEAN; ROUTE CORRECTION]` The multiplier in this card is ordinary position `x`. It is
not the logarithmic position `log|x|` forced by the Euler orbital-length identity. Lean now proves

```text
[log|x|,U_p]=-log(p)U_p,
[x,U_p]=(1-p)xU_p,
```

and proves that the second commutator is not a scalar multiple of `U_p` when `p != 1`.

After the exact logarithmic-coordinate unitary makes `U_p` an additive translation, the original
Sonin Fourier transform becomes an involutive translation-reversing scattering operator `J_log`,
not the ordinary Fourier transform used below. The formal theorem and corrected carrier law are in
`../../3-formalized/not_new_scientific_knowledge/sonin-log-coordinate-mellin-scattering-carrier.md`.

Consequently the edge calculation below is correct standard Fourier distribution theory, but its
identification as the degree-one Euler/Sonin source carrier is retired. The live commutator is
`[log|x|,B_a]` in the original coordinate, equivalently `[M_t,J_log]` in the logarithmic coordinate.

## Statement

Use the Fourier convention

```text
hat(f)(xi)=integral_R f(x)exp(-2 pi i x xi)dx.            (1)
```

Let

```text
Xf(x)=x f(x),
P_a=M_(1_[-a,a]),
B_a=F^(-1)M_(1_[-a,a])F,
Q_(0,a)=I-P_a-B_a.                                       (2)
```

The operator `Q_(0,a)` is the formal physical/Fourier Sonin complement used as the principal part
of the exact intersection projection. On Schwartz functions, the ordinary-position commutator is the
distribution

```text
F[X,B_a]f
 =i/(2 pi)
   [delta_(-a)hat(f)(-a)-delta_a hat(f)(a)].              (3)
```

Consequently

```text
-i <[X,Q_(0,a)]f,g>_dist
 =1/(2 pi)
   [hat(f)(a)conjugate(hat(g)(a))
    -hat(f)(-a)conjugate(hat(g)(-a))].                    (4)
```

Thus the principal log-position leakage is exactly a signed two-edge Sobolev trace form.  It is
not a bounded `L2` operator and does not disappear under parity: it is the polarized cross between
the even and odd edge channels.

Let `Q_a` be the exact Sonin intersection projection and

```text
C_a=Q_a-Q_(0,a).                                         (5)
```

The formal tree proves that `C_a` is Hilbert--Schmidt.  Transporting logarithmic position through
`Q_a`, however, requires the strictly stronger weighted correction

```text
[X,C_a],
```

whose integral kernel, whenever `C_a` has kernel `K_a`, is

```text
(x-y)K_a(x,y).                                           (6)
```

Hilbert--Schmidt control of `K_a` alone gives no control of `(6)`.  Hence a successful Sonin
position-commutator construction is forced to carry the edge trace `(4)` together with a first
relative moment of the exact projection correction.

## Exact resolvent dressing of the edge trace

The correction in `(5)` is not algebraically opaque.  Put

```text
A=P_a,             B=B_a,             E=I-A,
T=BAB,             V=(I-T)^(-1).                           (6a)
```

The strict time--frequency alternating-block theorem gives `||T||<1`, and the exact two-projection
formula is

```text
Q_a=E-EVBE.                                               (6b)
```

On every common rigged form core on which the following compositions are defined,

```text
[X,Q_a]
 =-EV(
      [X,B] A B V B
      +B A [X,B] V B
      +[X,B]
    )E.                                                   (6c)
```

Indeed `[X,E]=[X,A]=0`, the inverse-commutator identity gives

```text
[X,V]=V[X,T]V,                                           (6d)
```

and

```text
[X,T]=[X,B]AB+BA[X,B].                                   (6e)
```

Substitution into `[X,Q_a]=-E[X,VB]E` proves `(6c)`.

Thus every term of the exact position anomaly factors through the same two-edge distribution
`[X,B]` from `(3)`.  The Hilbert--Schmidt correction does not introduce an unrelated infinite
family of position defects.  It dresses the universal edge bundle by the prolate resolvent `V`.

The analytic caveat is load-bearing: `V` is a bounded operator on `L2`, while `[X,B]` maps a
Sobolev test space into boundary distributions.  Formula `(6c)` is not an `L2` bounded-operator
identity until `V`, `A`, `B`, and `E` are extended to a compatible rigged Sobolev pair.  Establishing
that extension and the relative trace after pairing with Euler leakage is the precise remaining
operator theorem.

## Proof of the edge formula

For the convention `(1)`,

```text
F(Xf)=i/(2 pi) partial_xi hat(f).                         (7)
```

Writing `chi_a=1_[-a,a]`, distributional differentiation gives

```text
partial_xi chi_a=delta_(-a)-delta_a.                     (8)
```

Therefore

```text
F[X,B_a]f
 =i/(2 pi)
   [partial_xi(chi_a hat(f))-chi_a partial_xi hat(f)]
 =i/(2 pi)(partial_xi chi_a)hat(f),                       (9)
```

which is `(3)`.  Since `[X,P_a]=0` and `Q_(0,a)=I-P_a-B_a`, one has

```text
[X,Q_(0,a)]=-[X,B_a].                                    (10)
```

Pairing `(3)` against `hat(g)` and multiplying by `-i` proves `(4)`. `QED`

## Exact parity polarization

Let

```text
Gamma_a f=(hat(f)(a),hat(f)(-a)).                        (11)
```

Equation `(4)` is the pullback of the signature matrix `diag(1,-1)` under `Gamma_a`.  If `f` and
`g` have the same parity, the right side vanishes.  If `f` is even and `g` is odd, then

```text
-i <[X,Q_(0,a)]f,g>_dist
 =1/pi hat(f)(a)conjugate(hat(g)(a)).                    (12)
```

Thus logarithmic position supplies one even edge coordinate and one odd edge coordinate, coupled
by a bilateral polarization.  The skew Euler logarithm also reverses parity.  Their compressed
product is therefore even and is the correct location of the Hermitian von-Mangoldt response.

## Sharp domain consequence

The formal complement does not preserve the domain of `X`.  Choose a Schwartz function with
`hat(f)(a) !=0`.  Then

```text
hat(B_a f)=chi_a hat(f)                                  (13)
```

has a jump at `a`, hence is not in `H1(R)`.  By Plancherel's characterization of the position
domain, `B_a f` is not in `D(X)`.  The terms `f` and `P_a f` have continuous Fourier transforms and
cannot cancel this jump, so generically

```text
Q_(0,a)f notin D(X).                                     (14)
```

Accordingly, the compressed position commutator cannot be defined by pretending that the sharp
formal complement preserves an operator core.  It must be constructed as a boundary form or by
proving an exact cancellation with `C_a`.

## Ordinary-position carrier law

The exact Sonin projection is

```text
Q_a=Q_(0,a)+C_a,                                        (15)
```

with `C_a` Hilbert--Schmidt.  On any common form core where the terms are meaningful,

```text
[X,Q_a]=[X,Q_(0,a)]+[X,C_a].                            (16)
```

Equations `(4)`, `(6)`, and `(6c)` identify the complete resource for the ordinary-position
commutator:

```text
two signed frequency-edge evaluations
  + their exact prolate-resolvent dressing V
  + the equivalent first relative moment (x-y)K_a(x,y)
  + a boundary/relative trace.                           (17)
```

A proof may show that `[X,C_a]` cancels the distributional edge charge or gives a finite relative
trace. It may not infer either conclusion from compactness or the unweighted Hilbert--Schmidt norm
of `C_a`.

This carrier does not generate `log(p)` under dilation. It is therefore not an RH-closing CCM
carrier. A successful construction must instead exhibit the nonlocal Mellin-scattering commutator
`[M_t,J_log]`, together with its source-defined relative trace.

## Relation to the bilateral zero channel

The even/odd polarization in `(12)` has the same signature pattern as the quartet resolvent split

```text
cosh(a t) channel minus sinh(a t) channel.
```

This is a formal analogy only. The edge trace does not supply the Euler orbital-length incidence.

## Scope and classification

The theorem is standard Fourier distribution and Sobolev trace calculus applied to the precise
formal Sonin complement. It is not new scientific knowledge. Its earlier identification with the
Euler logarithmic source was a coordinate mismatch. The corrected logarithmic scattering theorem
is formalized in Lean.

## Gates

- [x] principal position commutator computed as a two-edge distribution
- [x] exact even/odd boundary polarization identified
- [x] failure of sharp-cutoff position-domain invariance proved
- [x] Hilbert--Schmidt correction separated from its required first relative moment
- [x] exact Sonin position anomaly factored through the resolvent-dressed two-edge trace
- [x] ordinary-position scope separated from the Euler orbital-length carrier
- [x] corrected logarithmic-coordinate Sonin scattering formalized
- [x] ordinary-position scalar-commutator substitution retired
