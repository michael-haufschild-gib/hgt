# The critical Mobius germ has an exact four-unit formal Gamma-conormal cross-pair

- **ID:** `mobius-gamma-contact-transgression-four-unit-charge`
- **Stage:** 3-formalized
- **Type:** GENERAL HT SOURCE-CONORMAL GEOMETRY / FORMAL CROSS-PAIR
- **Scientific status:** `[PROVED FORMAL IDENTITY] [LEAN-FORMALIZED] [SOURCE-NATURALITY REFUTED] [NOT AN RH BRIDGE]`
- **Parents:**
  - `gamma-capacity-current-transgression.md`;
  - `hypertranscendental-two-scale-factorial-wall.md`;
  - `not_new_scientific_knowledge/mobius-critical-fisher-stein-contact-law.md`;
  - `../2-fully-proven/mobius-critical-fisher-tangent-hilbert-lift.md`.
- **Lean:** `formal/GaloisForLFunctions/RHTower/MobiusGammaContactTransgression.lean`.

## The distinguished analytic section

The completed critical squarefree--Mobius score is `2(1-y)` against the mean-one exponential
law.  Its analytic score-density is

```text
f(z)=2(1-z)exp(-z).                                      (1)
```

Every derivative is explicit:

```text
D^k f(z)=2(-1)^k(k+1-z)exp(-z).                          (2)
```

Gamma's source conormal is the actual unit-shift functional

```text
lambda_k=D^k(exp(D)-1),
lambda_k(f)=sum_(n>=0) f^(n+k+1)(0)/(n+1)!.              (3)
```

The series in `(3)` converges, and Taylor's theorem gives the formal shift evaluation

```text
lambda_k(f)=D^k f(1)-D^k f(0)
           =2(-1)^k[k exp(-1)-(k+1)].                    (4)
```

At the basic boundary layer,

```text
lambda_0(f)=f(1)-f(0)=-2,
|lambda_0(f)|^2=4.                                       (5)
```

Equations `(1)`--`(5)` are an exact formal cross-pair between an entire germ and the Taylor
functional representing unit translation.  They do **not** identify the critical variable `y`
with Gamma's affine argument.  Therefore `(5)` is not a source-natural characterization of the
Fisher tangent and does not close the source-Galois transgression problem.

The source-natural comparison is instead Mellin duality:

```text
M[2(1-y)exp(-y)](z)=2[Gamma(z)-Gamma(z+1)].              (5a)
```

Its exact radial, completed, and normal-cone forms are proved in
`mobius-mellin-gamma-normal-cone.md` and Lean-formalized in
`MobiusMellinGammaNormalCone.lean`.

## The two-scale no-go and its positive theorem

The differentiated response in `(4)` grows linearly:

```text
|lambda_k(f)| asymptotic to 2(1-exp(-1))k.                (6)
```

Hence the raw response family is not in unweighted `ell^2` over derivative order.  Gamma's
factorial conormal can act on every fixed derivative translate while the assembled raw response
still has infinite clock capacity.

**No-go.**  This Gamma-conormal cross-pair cannot live in one unweighted raw-jet
Hilbert completion.  Finite conormal summability does not imply square summability across the
source-operator orbit.

**Positive HT theorem.**  Taylor/Gevrey-one normalization retains the entire response as the
analytic shift-defect germ

```text
Delta_Gamma f(z)=f(z+1)-f(z)
 =2exp(-z)[(1-exp(-1))z-1].                               (7)
```

Its Taylor coefficients are `lambda_k(f)/k!` and are square summable.  The RH source therefore
realizes the two-scale factorial-wall mechanism exactly: source-conormal depth and observable
derivative order do not assemble in the raw topology, while the critical Gevrey-one completion
does.

There is a sharper finite-stage obstruction.  The charge visible through the first `N` raw
boundary symbols is exactly

```text
c_N=sum_(n=0)^(N-1) f^(n+1)(0)/(n+1)!
   =2[(-1)^N/N!-1].                                      (7a)
```

Hence

```text
c_1=-4,       |c_1|^2=16,       c_N->-2.                 (7b)
```

Odd and even truncations approach the terminal charge from opposite sides.  In particular, the
finite Gamma boundary currents cannot be assembled as a tower of four-unit contractions in the
raw truncation order.

The truncation residue is not arbitrary.  Let

```text
s_N=(-1)^(N+1)/N!                                       (7c)
```

be the actual reciprocal-Gamma pole microscope scale from the factorial asymptotic connection.
Then Lean proves the exact renormalization law

```text
c_N+2s_N=-2,
|c_N+2s_N|^2=4                         for every N.       (7d)
```

**Positive HT theorem.**  Gamma's own factorial capacity connection supplies precisely the
counterterm which turns the oscillating raw conormal currents into the terminal four-unit charge
at every depth.  This is not generic Taylor subtraction: `s_N` is the source normalization of the
reciprocal-Gamma pole chart and its inverse is the unbounded flat gauge of the nontrivial Gamma
bounded-uniformization class.

Thus any use of this formal cross-pair must retain the factorially renormalized joint source-depth/
observable-order graph.  The calculation gives a genuine HT truncation theorem, but it does not
show that this graph is the zeta source graph.

## Why the scalar Ward identity is not a topological transgression

The reciprocal squarefree transfer already constructed from the finite Mobius contractions is

```text
T_sigma(s)=1/[zeta(sigma) X_sq(s)].                       (8)
```

Its projective logarithmic connection is

```text
d log T_sigma=-X_sq'/X_sq=Q_sq/2.                         (9)
```

Combining the scalar equality `(5)` and `(9)` gives

```text
Q_sq=-lambda_0(f) d log T_sigma.                         (10)
```

Consequently

```text
P_anti[-lambda_0(f)d log T_sigma]
 =P_anti Q_sq
 =ell_E.                                                  (11)
```

But `(10)` only substitutes the number `lambda_0(f)=-2` into `Q_sq=2 d log T_sigma`.  It does not
construct a map from the Gamma conormal space to the reciprocal-horizon tangent space.  In
particular, the two variables have not been compared and no positive metric is transported.

The earlier interpretation

```text
Gamma source-conormal boundary charge
  cap reciprocal-projective Cech connection
  = completed squarefree Ward current.                    (12)
```

is therefore withdrawn.  The equality is useful bookkeeping, not a cap product.

## Correct RH successor

The RH-bearing topology is the deformation-to-the-normal-cone of the vanishing completed Möbius
transfer, not `(10)`.  Its exceptional section is `X_sq^(-1)` and its projective connection is
`Q_sq`.  The corrected bold conjecture is the exceptional Gauss--Ward theorem in
`mobius-mellin-gamma-normal-cone.md`: construct the positive singular Hermitian Pluecker/Rees
extension and identify its exceptional second fundamental form with `c_sq directSum ell_E`.

The exact finite renormalization `(7d)` remains potentially useful as a Gamma-depth chart of that
extension, but it is not itself evidence that the extension exists.

## Gates

- [x] critical analytic contact section identified
- [x] all derivative jets computed
- [x] basic Gamma conormal charge proved equal to `-2`
- [x] charge energy proved equal to four
- [x] full differentiated conormal response computed
- [x] exact finite charge and factorial truncation error computed
- [x] naive stagewise four-unit contraction falsified in Lean
- [x] truncation error identified with the actual reciprocal-Gamma pole scale
- [x] exact four-unit factorial renormalization proved in Lean at every depth
- [x] raw-jet square-summability no-go isolated
- [x] Gevrey-one shift-defect germ identified
- [x] Lean formalization checked directly and by targeted build
- [x] scalar identity `(10)` derived
- [x] source-coordinate identification audited and rejected
- [x] source-natural Mellin--Gamma successor isolated
- [ ] determine whether the factorial cross-pair embeds in the exceptional Rees/Tate graph
- [ ] use only if that source-natural embedding is proved
