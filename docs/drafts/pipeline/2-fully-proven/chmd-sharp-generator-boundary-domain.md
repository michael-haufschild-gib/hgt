# Sharp boundary admission for the actual arithmetic generator

- **ID:** chmd-sharp-generator-boundary-domain
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean pending)
- **Statement:** Every half-line source projection preserves the domain of the actual CHMD arithmetic generator. Its generator commutator is an everywhere-defined bounded skew-adjoint operator on mass L2, with norm bounded independently of the cut location.

## Route and contribution

The route remains complete odd theta–Doob positivity, hence RH. The open
arithmetic obligations are reflected-prime collar payment and primitive
nodal defect payment. Sharp form localization does not alone permit
localizing an eigenvector equation. The theorem here supplies the actual
operator-domain admission and a bounded boundary forcing term. It does
not assert that the forcing has a favorable sign.

## Dependency-closed paper proof

Let `H=L2(mu)` be the actual theta–cosh mass space, `V=SourceGraph`,
`J:V->H` its source embedding and `A` the existing arithmetic generator.
Write `P_c` for multiplication by `1_(-infinity,c)`. The sharp spatial
cut theorem gives its lift `C_c:V->V`, with `J C_c=P_c J`. The source
projection `P_c` is self-adjoint and contractive on `H`.

Put `T=sharpBoundaryPhysical`, so `Tu=Theta*u` is ordinary complex L2,
viewed as a real Hilbert space. In positive distance coordinates define
the two bounded maps

```
U_-(u)(t)=(Tu)(c-t),  U_+(u)(s)=(Tu)(c+s),  s,t>0.
```

The literal Gamma boundary operator `K` has kernel
`archLevyDensity(s+t)=ccmGammaTranslationDensity(s+t)` and norm at most
`2*pi`. Its pairings are absolutely integrable for arbitrary L2 inputs.
Consequently

```
F_c=U_-^* K U_+,
B_c=F_c-F_c^*,
b_c(u,v)=Re<K U_+(u), U_-(v)>-Re<K U_+(v), U_-(u)>.
```

This constructs a bounded real operator `B_c` on all of `H`, of norm
at most `2*||K||*||T||^2 <= 4*pi*||T||^2`, independently of `c`.
Its definition gives skew-adjointness directly and
`<B_c u,v>=b_c(u,v)`.

For graph vectors `p,q`, expand the two literal differences. Across a
crossing edge `(x,y)`, with `x<c<y`,

```
Delta(P_c p)*Delta(q)-Delta(p)*Delta(P_c q)
  =p(y)q(x)-p(x)q(y).
```

Elsewhere the difference vanishes. Multiply by the actual archimedean
edge weight and transport by `(h,x)->(c-x,x+h-c)`. Absolute boundary
integrability just proved justifies the identity of integrals. It gives
the archimedean form defect `b_c(Jp,Jq)`; no boundary trace is used.

The complete prime generator `G=primeGenerator` is bounded on all of
`H`, so the prime form defect is represented by
`G P_c-P_c G`. The mass inner product cancels because `P_c` is
self-adjoint. Thus the complete graph inner product satisfies

```
<C_c p,q>_V-<p,C_c q>_V=<D_c Jp,Jq>_H,
D_c=B_c+G P_c-P_c G,
||D_c|| <= 4*pi*||T||^2+2*||G||.
```

Every term is an actual source operator. `D_c` is skew-adjoint. Let `R`
be the existing Riesz resolvent. Testing against every `q` in the graph
and using the defining Riesz identity now proves

```
rieszLift(P_c w+D_c Rw)=C_c(rieszLift w),
R(P_c w+D_c Rw)=P_c Rw.
```

For `u` in the actual generator domain, the established identity
`R(u+Au)=u` therefore gives

```
P_c u in domain(A),
A(P_c u)=P_c Au+D_c u.
```

The last equality follows from injectivity of `R`. In particular the
localized eigenvector equation has the stated bounded forcing, without
an assumed domain admission or unproved sampling estimate.

## Corpus inputs inspected

- `CCMRestrictedWeilGammaBoundaryPairing`: actual positive-half-line
  boundary operator, norm bound and absolute pairing integrability.
- `CHMDSharpSpatialCut`: actual sharp form-domain admission.
- `CHMDBoundedPrimeGenerator`: complete bounded prime generator.
- `CHMDStationaryLocalTransform.thetaToVolume`: actual bounded physical map.
- `CHMDOperatorCutoffCommutator`: smooth-cut form identity, used only as
  a proof pattern; its slope bound does not apply to sharp cuts.
- `CHMDCompactSupportOperatorCore`: exact resolvent-to-generator domain
  argument and already established smooth operator localization.

## Gates

- [x] Complete paper proof, including full-domain boundary integrability.
- [ ] Concrete real boundary operator and exact graph pairing in Lean.
- [ ] Actual generator-domain admission and action in Lean.
- [ ] Candidate and final repository checks; standard-axiom audit.
- [ ] Umbrella wiring and scratch cleanup.

No global multiplier-domain theorem for a different CCM operator is
claimed here. No arithmetic positivity or RH conclusion is asserted.
