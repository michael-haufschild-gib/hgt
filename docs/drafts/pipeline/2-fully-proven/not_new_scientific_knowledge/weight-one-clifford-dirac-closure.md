# Weight-one Clifford--Dirac closure

- **ID:** `weight-one-clifford-dirac-closure`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / LEAN SOURCE CORE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Lean:** `formal/GaloisForLFunctions/RHTower/WeightOneCliffordDirac.lean`
- **Statement:** On `L²(R_+,dt)`, the closed weight-one Dirac operator
  `Q_a=(t d/dt+1/2)+aJ`, with `Jf(t)=t^(-1)f(t^(-1))`, has domain transported from `H¹(R)` and
  self-adjoint square `Q_a²=C²+a²` on the transported `H²(R)` domain.

## Source theorem

Let

```text
(Uf)(x) = exp(x/2) f(exp x),
(Jf)(t) = t^(-1) f(t^(-1)),
C = t d/dt + 1/2,
Q_a = C + aJ,                a in R.
```

Then `U:L²(R_+,dt)->L²(R,dx)` is unitary and

```text
U C U^(-1) = partial_x,
U J U^(-1) = R,              (Rg)(x)=g(-x).
```

On `L²(R)`, take `partial_x` with domain `H¹(R)`.  The reflection `R` is a bounded self-adjoint
unitary, preserves every Sobolev space, and anticommutes with `partial_x`.  Therefore

```text
P_a = partial_x + aR,         Dom(P_a)=H¹(R)
```

is closed and

```text
Dom(P_a²)=H²(R),
P_a²=partial_x²+a².
```

The Fourier transform makes `P_a²` multiplication by the real function `a²-ξ²` under the
unitary-frequency convention.  Hence `P_a²` is self-adjoint.  Transport by `U` gives the claimed
closed realization of `Q_a` and its self-adjoint square on `L²(R_+,dt)`.

## Proof

The norm identity

```text
integral_R |exp(x/2)f(exp x)|² dx
  = integral_R exp(x)|f(exp x)|² dx
  = integral_(0,infinity) |f(t)|² dt
```

shows that `U` is an isometry; the inverse is

```text
(U^(-1)g)(t)=t^(-1/2)g(log t),  t>0,
```

so `U` is unitary.  Direct differentiation gives

```text
partial_x(Uf)(x)
  = exp(x/2)[exp(x)f'(exp x)+(1/2)f(exp x)]
  = U(Cf)(x).
```

Also

```text
U(Jf)(x)
  = exp(x/2)exp(-x)f(exp(-x))
  = (Uf)(-x),
```

which proves the two intertwining identities.

The weak derivative satisfies `partial_x R=-R partial_x`; reflection preserves `H¹` and `H²`.
Since `aR` is bounded, the bounded perturbation theorem makes `P_a` closed on `H¹`.  For
`g in H¹`,

```text
P_a g in H¹
  iff partial_x g + aRg in H¹
  iff partial_x g in H¹
  iff g in H².
```

Thus `Dom(P_a²)=H²`.  On that domain,

```text
P_a²
  = partial_x² + a(partial_x R+R partial_x)+a²R²
  = partial_x²+a².
```

The Fourier transform identifies `partial_x²+a²` with its maximal real multiplication operator,
which is self-adjoint.  This completes the proof. `[PROVED HERE]`

## Lean boundary

Lean proves the source identities on smooth profiles:

- `centeredScaleGenerator_weightOneInversion`: `CJ=-JC`;
- `weightOneCliffordDirac_sq`: `(C+aJ)²f=C²f+a²f`;
- `weightOneCliffordEnergy_eq_quadraticScaleEnergy`: the Mellin symbol
  `a²+(w-1/2)²` is a real affine transform of `-w(w-1)`;
- `xiWeightOneCliffordSpectralReality_iff_riemannHypothesis`: reality of this symbol at every Xi
  zero is equivalent to RH.

The unbounded-operator closure is proved on paper because the current formal corpus does not yet
provide the required Sobolev-domain and self-adjoint multiplication-operator library surface.

## Positive and negative consequences

The Clifford algebra and operator closure are no longer open in the RH route.  The exact remaining
theorem is a completed determinant or scattering comparison

```text
xi(rho)=0
  -> a²+(rho-1/2)² belongs to spectrum(Q_a²+V_source),
```

where `V_source` is a self-adjoint prime--Gamma boundary or scattering perturbation constructed
before the Xi divisor is read.

The free operator alone cannot supply this implication: its spectrum is a real half-line and it
contains no arithmetic determinant.  This no-go has positive content.  The bulk geometry is now
fixed and self-adjoint; all arithmetic difficulty is localized in a source-defined self-adjoint
perturbation and its determinant identity.  Adding a divisor-selected boundary condition would be
circular.

## Gates

- [x] 0 -> 1: source operator, domains, attack, and RH endpoint explicit
- [x] 1 -> 2: complete unitary, closure, square-domain, and self-adjointness proof
- [ ] 2 -> 3: formalize the Sobolev closed-operator theorem when the required library surface exists
- [ ] 3 -> 4: only as a lemma inside a source determinant/scattering construction
