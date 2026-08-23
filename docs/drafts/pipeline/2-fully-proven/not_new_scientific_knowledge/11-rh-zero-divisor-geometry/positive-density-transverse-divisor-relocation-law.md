# Positive-density transverse divisor relocation law

- **ID:** `positive-density-transverse-divisor-relocation-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / finite-order HT route no-go
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Two functional-equation- and Schwarz-symmetric entire hypertranscendental functions
  of exact order one can have the same complete differential-translation field after one fixed
  differential-algebraic base extension and exactly the same zero-ordinate counting measure, while
  one divisor lies entirely on the critical line and the other has a positive-density pair of
  off-line vertical lattices.

## Construction

Write

```text
w=s-1/2.
```

Fix `beta>0` with `2 beta-1 notin Z`, and put

```text
C_beta(s)=1/(Gamma(beta+i w) Gamma(beta-i w)).                 (1)
```

The carrier theorem in `finite-order-symmetry-ht-rational-gauge-blindness.md` proves that
`C_beta` is entire, hypertranscendental over `C(s)`, of exact order one, invariant under
`s |-> 1-s` and Schwarz conjugation, and has only the simple critical-line zeros

```text
w=+/- i(n+beta),  n>=0.                                      (2)
```

For a fixed real `a!=0`, define the two differential-algebraic envelopes

```text
A_0(w)=cosh(w)^2,
A_a(w)=cosh(w-a) cosh(w+a),                                  (3)
```

and the two carriers

```text
F_0(s)=C_beta(s) A_0(s-1/2),
F_a(s)=C_beta(s) A_a(s-1/2).                                 (4)
```

## Exact divisor relocation `[PROVED]`

The zeros of `cosh` are

```text
z_k=-(2k+1) pi i/2,  k in Z.                                (5)
```

Therefore `A_0` has a double zero at every `z_k`, while `A_a` has the two simple zeros

```text
-a+z_k,  a+z_k                                               (6)
```

and no others. In particular, if `Im_*` denotes pushforward of a divisor by the imaginary-part
map, then

```text
Im_* Div(A_0)=2 sum_(k in Z) delta_(Im z_k)
             =Im_* Div(A_a).                                (7)
```

Since the carrier divisor is common to both products, equation `(7)` gives the exact identity

```text
Im_* Div(F_0)=Im_* Div(F_a).                                (8)
```

Thus for every `T>=0`, including multiplicity and with either common boundary convention,

```text
sum_(F_0(rho)=0, |Im(rho)|<=T) ord_rho(F_0)
 =
sum_(F_a(rho)=0, |Im(rho)|<=T) ord_rho(F_a).                 (9)
```

The centered notation in `(9)` suppresses the real shift by `1/2`; imaginary parts are unchanged.

All zeros of `F_0` lie on `Re(s)=1/2`. The function `F_a` has, in addition to the common carrier
zeros, the off-line lattices

```text
s=1/2 +/- a -(2k+1) pi i/2,  k in Z.                        (10)
```

Their combined vertical density is

```text
# {rho in (10): |Im(rho)|<=T}=4T/pi+O(1).                   (11)
```

Hence this is a positive-density transverse relocation, not a finite divisor perturbation.

## Symmetry, order, and hypertranscendence `[PROVED]`

Both envelopes in `(3)` are even and Schwarz-real. Consequently both functions in `(4)` satisfy

```text
F(1-s)=F(s),
F(conj(s))=conj(F(s)).                                      (12)
```

The envelopes are exponential polynomials of order at most one. Multiplication by them keeps the
order of the carrier at most one. The common carrier zero sequence `(2)` has exponent of convergence
one, so neither product can have order below one. Both `F_0` and `F_a` therefore have exact order
one.

Each `A_b` is differentially algebraic over `C(s)`. If one of the products `F_b=C_beta A_b` were
differentially algebraic, division by the nonzero DA meromorphic function `A_b` would make
`C_beta` differentially algebraic. This contradicts the carrier theorem. Hence both products are
hypertranscendental.

On the critical line the relocated envelope is strictly positive:

```text
A_a(i y)=|cosh(a+i y)|^2>0.                                (13)
```

Thus it does not cancel or alter the common critical-line carrier zeros. It only installs the two
off-line lattices `(10)`.

## Complete differential-translation field equality `[PROVED]`

Let

```text
K=C(s,e^(2s)).                                               (14)
```

This is a translation-stable differential field: `D e^(2s)=2e^(2s)` and
`T_h e^(2s)=e^(2h)e^(2s)` for every complex `h`. It is differentially algebraic over `C(s)`.
The product-to-sum identity gives

```text
A_a(w)=(cosh(2w)+cosh(2a))/2,                               (15)
```

so every complex translate of every `A_a(s-1/2)` is a nonzero element of `K`.

For every `h in C`,

```text
T_h F_b=(T_h A_b)(T_h C_beta),  b in {0,a}.                 (16)
```

The factor `T_h A_b` is invertible in the meromorphic field `K`. Therefore

```text
K<(T_h F_0)_(h in C)>_D
 =K<(T_h C_beta)_(h in C)>_D
 =K<(T_h F_a)_(h in C)>_D.                                 (17)
```

The same equality holds for every selected finite shift family and includes all derivative jets.

Because `K/C(s)` is differential-algebraic, adjoining `K` changes no differential transcendence
degree. Applying this to every subfamily shows that the finite-translate differential matroids of
`F_0` and `F_a` have the same rank function already over `C(s)`. Equation `(17)` is deliberately
stated over `K`: equality of rank after a DA base extension does not imply equality of the complete
differential relation ideals over the smaller base.

The logarithmic source classes agree as well:

```text
Dlog(F_a)-Dlog(F_0)=Dlog(A_a)-Dlog(A_0) in K.               (18)
```

Thus `F_0` and `F_a` define the same class in the additive quotient of meromorphic logarithmic
derivatives by the DA field. The source class, the complete ordinate measure, and all finite
differential-translation ranks can therefore agree simultaneously while transverse localization
changes on a positive-density divisor.

## No-go theorem for ordinate-only HT implementations

Let an implementation invariant factor through the following package:

1. exact entire order one;
2. the scalar functional equation and Schwarz reality;
3. hypertranscendence and all finite differential-translation ranks;
4. the complete translated differential field after a fixed DA base extension; and
5. the logarithmic source class modulo that DA field; and
6. the complete zero-ordinate counting measure, not merely its asymptotic Weyl law.

Then the invariant has the same value on `F_0` and `F_a`, although the RH-type divisor statement is
true for `F_0` and false for `F_a`. Consequently no theorem using only this package can produce a
divisor-location conclusion.

This closes the following implementations, not the complete named routes:

- a Hilbert--Polya or Berry--Keating implementation that identifies only spectral heights and their
  exact multiplicities, without a characteristic determinant or transverse-width theorem;
- a Connes absorption-spectrum implementation that retains energies but discards the resonance
  widths distinguishing `(10)` from the line;
- a de Branges implementation using only order, height counting, and HT type rather than the exact
  Hermite--Biehler inner quotient and kernel positivity;
- an attempted derivation of Weil or Li positivity solely from the preserved HT/translation package;
- a prime-truncated Nyman--Beurling implementation whose only claimed extra input is the same
  differential-translation package.

Exact Weil positivity, all Li coefficients, the full Nyman--Beurling closure problem, an exact
self-adjoint determinant, and a canonical de Branges inner function all see the transverse divisor
and are not excluded.

## Parent-theory and novelty verdict

`[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`. The proof combines three established mechanisms:

1. the explicit zeros and exponential type of elementary `cosh` products;
2. closure of differentially algebraic meromorphic functions under field operations; and
3. the rank-one difference-Galois hypertranscendence criterion used for `C_beta`.

The general zero distribution and indicator geometry of exponential polynomials is classical, and
the exact relocation pair in `(3)` is immediate once written down. The RH-facing information-loss
statement is useful, but it fails the anti-theatre and parent-theory novelty gates.

Primary parent references:

- Hardouin--Singer, *Differential Galois Theory of Linear Difference Equations*,
  `https://arxiv.org/abs/0801.1493`;
- Heittokangas et al., *Value distribution of exponential polynomials and their role in the
  theories of complex differential equations and oscillation theory*,
  `https://doi.org/10.1112/blms.12719`.

## Lean status

`CoshQuartetEnvelope.lean` formalizes the displaced envelope, its complete two-lattice zero set,
evenness, Schwarz reality, period group, and strict critical-axis positivity.
`CoshPolynomialExactOrderOne.lean` supplies explicit order-one bounds. The reflected-gamma carrier,
its Hardouin--Singer hypertranscendence, divisor pushforward equality, and differential-field
statement `(17)` are not formalized. This complete card therefore remains at stage 2.

## Gates

- [x] complete unconditional paper proof
- [x] exact positive-density off-line relocation, not finite implantation
- [x] exact ordinate measure equality
- [x] full DA-base differential-translation field equality
- [x] route consequences bounded to the invariant package actually preserved
- [x] parent-theory novelty rejection
- [ ] complete unconditional Lean formalization of the whole claim

## Lean status update (2026-08-23)

`formal/GaloisForLFunctions/RHTower/CoshQuartetEnvelopeMultiplicity.lean` strengthens the existing
quartet-envelope substrate with the exact complex derivative, simplicity of every zero for nonzero
displacement, and exclusion of every central-vertical-line zero. The leaf is wired through
`RHTower.lean`, was checked with `lake env lean`, target-built, and its new theorem declarations
audit to only `propext`, `Classical.choice`, and `Quot.sound`.

This closes the elementary multiplicity and transverse-placement facts for the displaced envelope.
It does not formalize the reflected-Gamma carrier, shared ordinate-divisor measure, or the
differential-translation field identity; the complete card remains at stage 2.

`formal/GaloisForLFunctions/RHTower/CoshQuartetEnvelopeOrdinates.lean` now
formalizes the exact support-level ordinate invariance of the elementary
quartet witness: for every pair of real displacements and every ordinate `y`,
there is an envelope zero with imaginary part `y` for one displacement iff
there is one for the other. The leaf is wired into `RHTower.lean`, direct
checked, target-built as
`GaloisForLFunctions.RHTower.CoshQuartetEnvelopeOrdinates`, and both new
theorems audit only to `propext`, `Classical.choice`, and `Quot.sound`.

This establishes the full ordinate-support component, not the divisor measure
with analytic multiplicities or the reflected-Gamma/differential-field parts;
the card remains at stage 2.

The same ordinate leaf now proves the local multiplicity-pairing witness: at
every odd half-integer lattice ordinate, every nonzero displacement has two
distinct envelope zeros with that common imaginary part, and both are simple.
This new declaration was direct-checked, target-built, and axiom-audited to
standard Lean foundations. It supplies the finite elementary pairing behind the
common ordinate count, but does not replace the missing analytic divisor
pushforward equality for the Gamma-multiplied carriers.

`formal/GaloisForLFunctions/RHTower/ReflectedGammaCarrier.lean` now
formalizes the centered carrier
`1/(Gamma(beta + i z) Gamma(beta - i z))` itself: global analyticity,
its exact two critical-axis zero lattices, central-line confinement of every
zero, evenness, and Schwarz reality. The leaf is wired into `RHTower.lean`,
direct-checked, target-built as
`GaloisForLFunctions.RHTower.ReflectedGammaCarrier`, and all five declarations
audit only to `propext`, `Classical.choice`, and `Quot.sound`.

The remaining carrier work is the product/divisor analysis with the Cosh
envelopes, including exact multiplicity pushforward and the HT/differential
translation field. This card therefore remains stage 2.

`formal/GaloisForLFunctions/RHTower/ReflectedGammaQuartetRelocation.lean`
now combines the reflected-Gamma carrier with the actual Cosh quartet. It
formally proves global analyticity, evenness, Schwarz reality, centrality of
the undisplaced product divisor, exact identification of all off-central zeros
with the Cosh zeros, production of off-central full-carrier zeros for every
nonzero displacement, and equality of the complete zero-ordinate *support*
for all displacements. The leaf is wired into `RHTower.lean`, direct-checked,
target-built as
`GaloisForLFunctions.RHTower.ReflectedGammaQuartetRelocation`, and all seven
new declarations audit only to `propext`, `Classical.choice`, and `Quot.sound`.

This is a substantial closure of `(4)`, `(8)`, `(10)`, and `(12)` at the
support level. Exact analytic-order/multiplicity pushforward, order-one and
hypertranscendence of the complete products, and their differential-translation
field identity remain necessary before stage 3.
