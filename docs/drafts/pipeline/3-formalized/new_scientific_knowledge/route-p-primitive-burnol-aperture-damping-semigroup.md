# Route P primitive Burnol aperture damping semigroup

- **ID:** `route-p-primitive-burnol-aperture-damping-semigroup`
- **Stage:** 3-formalized
- **Label:** `P-G187`
- **Source:** P-G185, P-G186, positive-aperture Burnol conormal geometry
- **Statement:** The weighted aperture translations
  `T_c f(L)=L/(L+c) f(L+c)` form a contraction semigroup for `c>=0`, diagonalize every Burnol
  conormal feature, realize P-G185 joint damping by the exact change of variables `s=2c`, and have
  a sharp operator wall at `c=0`: every negative time sends one explicit finite-energy datum to a
  nonintegrable reciprocal-square pole.

## Conjecture, proof, and pivot

P-G185 proved only an arithmetic statement: the primitive joint-damping codiagonal is summable
exactly for `s>=0`. P-G186 then realized its undamped base matrix as the Gram of actual inverse
Burnol-window features on `L2(R_+,dL)`. The conjecture was that these are shadows of one aperture
evolution, rather than unrelated convergence and Gram facts.

For `c>=0`, define

```text
(T_c f)(L) = [L/(L+c)] f(L+c),     L>0.                              (1)
```

The cocycle telescopes:

```text
T_c T_d = T_(c+d),     T_0=I.                                       (2)
```

For the universal Burnol conormal feature

```text
F_z(L)=L exp[-(z-1/2)L],                                             (3)
```

one has the exact eigenlaw

```text
T_c F_z = exp[-c(z-1/2)] F_z.                                       (4)
```

Therefore the primitive feature at
`z=1/2+lambda_(p,e)+i kappa`, `lambda_(p,e)=log(p^(e+1))`, obeys

```text
||T_c F_(p,e,kappa)||_2^2
 = exp[-2c lambda_(p,e)] ||F_(p,e,kappa)||_2^2.                      (5)
```

Lean also proves that the undamped energy in `(5)` is exactly the P-G186 base Gram diagonal.
Since

```text
exp[-2c log n] = n^(-2c),                                            (6)
```

the dynamically damped base mass is literally P-G185's joint-damping weight with `s=2c`.
Consequently its complete primitive family is summable exactly for `c>=0`.

For a general continuous finite-energy datum, `0<=L/(L+c)<=1` and translation discards the
initial interval `(0,c)`, giving

```text
||T_c f||_2^2 <= ||f||_2^2.                                         (7)
```

The converse is sharp and uses a genuine `L2` input, not the nonintegrable constant function.
Let

```text
f_wall(u)=1_(0,1)(u).                                                (8)
```

It has finite positive-aperture energy. If `c<0`, then on
`L in (-c,-c+1)`,

```text
|T_c f_wall(L)|^2 = [L/(L+c)]^2,                                    (9)
```

which dominates a nonzero multiple of `(L+c)^(-2)`. Translation reduces local integrability to
that of `x^(-2)` on `(0,1)`, contradicted by the sharp power-integrability criterion. Thus no
negative time preserves the full positive-aperture `L2` domain.

## New route knowledge

P-G185's zero-width Dirichlet chamber and the P-G186 Burnol Gram are the same semigroup wall in
different coordinates. The remaining completed transport cannot be ordinary backward evolution
inside the positive-aperture Hilbert space. The obstruction is a unilateral boundary defect at
`L=0`, not merely slow prime decay.

Together with W-H185's exponential-type range no-go, this points to a stricter architecture. The
polar--Gamma/functional-equation sector must act before positive Gram comparison and supply the
missing boundary/dilation channel that creates slower completed modes. A minimal-unitary-dilation
interpretation is now a concrete conjectural producer, not a proved identification: P-G187 proves
the unilateral semigroup and its exact defect wall, but does not yet identify its dilation defect
with the completed Gamma--polar surplus.

## Novelty and theatre audit

Internal corpus search found P-G185's summability wall, P-G186's Burnol Gram, and later tail-rate
range obstructions, but no weighted-aperture semigroup joining them, no exact `s=2c` dynamical
identification, and no finite-energy negative-time pole theorem.

Primary-source audit found the general theory of weighted translation semigroups on
`L2(R_+)`, Burnol's co-Poisson/Sonine Hilbert realization, and Connes--Consani's scaling-Hamiltonian
and positivity obstruction. None of the audited sources states `(1)`--`(9)` for Burnol conormal
features with primitive Euler weights:
[Phatak--Sholapurkar](https://arxiv.org/abs/1804.08981),
[Burnol](https://arxiv.org/abs/math/0203120),
[Burnol co-Poisson](https://arxiv.org/abs/math/0407443), and
[Connes--Consani](https://arxiv.org/abs/1910.14368).
No external priority claim is made beyond the exact Route P synthesis formalized here.

The negative-time proof uses an explicit finite-energy input and a local reciprocal-square
divergence theorem. It does not infer operator failure from a non-`L2` constant test. No RH
conclusion is claimed, and no boundary transport is smuggled in as an assumption.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/RoutePPrimitiveBurnolApertureDampingSemigroup.lean
```

Capstones:

- `routePBurnolForwardDampingShift_add`;
- `routePBurnolForwardDampingShift_windowFeature`;
- `routePBurnolApertureEnergy_forwardDampingShift_le`;
- `routePBurnolApertureEnergy_primitiveFeature_eq_baseWeight`;
- `routePBurnolApertureEnergy_forwardDampingShift_primitiveFeature_eq_baseMass`;
- `routePPrimitiveBurnolSemigroupBaseMass_eq_jointDampingWeight`;
- `summable_routePPrimitiveBurnolSemigroupBaseMass_iff`;
- `routePBurnolBackwardWallTest_integrable`;
- `routePBurnolForwardDampingShift_negative_not_integrable`.

Verification:

- `/tmp/pg187.lean`: `lake env lean /tmp/pg187.lean` passed cleanly;
- exact leaf build passed;
- `/tmp/pg187_audit.lean`: capstones depend only on `propext`, `Classical.choice`, `Quot.sound`;
- targeted forbidden-declaration scan: clean;
- umbrella import wired; umbrella not built.

## Gates

- [x] paper proof dependency-closed
- [x] exact unconditional Lean formalization
- [x] genuine finite-energy negative-time witness
- [x] exact P-G185/P-G186 dynamical identification
- [x] scratch verification
- [x] exact leaf build
- [x] axiom and forbidden-declaration audit
- [x] umbrella wired without umbrella build
- [ ] identify completed polar--Gamma surplus as a source-derived dilation/defect channel
- [ ] construct matrix-complete boundary transport to Xi divisor nodes
- [ ] unconditional RH
