# Mobius incidence curvature is KMS entropy production with a universal singular gap response

- **ID:** `mobius-incidence-kms-universal-gap-response-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / ANTI-CAUSAL WARD ROUTE TEST
- **Scientific status:** `[PROVED HERE] [PROOF-DELIVERY TEST] [NOVELTY GATE BYPASSED BY REQUEST] [NOT RH]`
- **Parents:**
  - `mobius-incidence-clock-gini-fisher-four-unit-law.md`
  - `complementary-packet-affine-flux-fisher-ward-isometry.md`
  - `../3-formalized/thermodynamic-affinity-clock-holonomy.md`
- **Formal consumer:**
  `GaloisForLFunctions.RHTower.PrimeArchEntropyProductionResponseRH`
- **Statement:** Every finite squarefree incidence curvature admits an exact Hermitian finite-KMS
  entropy-production realization.  In the critical limit its passive spectral measure is the
  universal measure `2|x|exp(-|x|)dx`, of total mass four.  Its response has a nonremovable
  logarithmic derivative singularity at the centered origin, so it cannot converge to the
  analytic continued prime--archimedean trace and cannot discharge the formal KMS-to-RH capstone.

## Exact finite KMS realization

Fix `sigma>1`, `epsilon=sigma-1`, and a finite nonempty set `D` of squarefree positive integers.
Put

```text
p_d=d^(-sigma)/sum_(e in D)e^(-sigma),
E_d=epsilon log d,
beta=sigma/epsilon.                                      (1)
```

Then `p_d` is exactly the finite Gibbs weight for energy `E_d` at inverse temperature `beta`.
For `d!=e`, choose the real symmetric Hermitian amplitude by

```text
|A_de|^2
 =4epsilon p_d p_e/[sigma |p_e-p_d|],
A_dd=0.                                                  (2)
```

Distinct positive integers have distinct Gibbs weights, so `(2)` is defined.  The KMS
entropy-production transition intensity is

```text
I_de
 =(p_e-p_d)log(p_e/p_d)|A_de|^2
 =4epsilon p_d p_e|log d-log e|
 =4p_d p_e|E_d-E_e|.                                    (3)
```

It is symmetric and nonnegative.  Summing `(3)` gives exactly the finite incidence/Gini energy

```text
sum_(d,e in D)I_de
 =4epsilon E_D|H-H'|,
H=log d.                                                 (4)
```

Thus the four-unit Mobius curvature is not merely analogous to thermodynamic dissipation: it is
an exactly normalized finite KMS entropy production.

## Critical response theorem

Let `D` increase cofinally through the squarefree integers and then let `sigma->1+`.  The proved
squarefree clock law gives

```text
Y_sigma=epsilon H  ->  Y~Exp(1).                         (5)
```

For two independent copies, the oriented gap `X=Y-Y'` has the Laplace density

```text
rho_X(x)=1/2 exp(-|x|).                                  (6)
```

The transition passive response attached to `(3)` is

```text
R_(sigma,D)(z)
 =sum_(d,e in D) I_de/[z-(E_d-E_e)].                    (7)
```

For every fixed `Im z>0`, the integrand `|x|/(z-x)` is bounded and continuous on the real line.
Consequently `(5)` and cofinal truncation give

```text
R_(sigma,D)(z) -> R_infinity(z)
 =2 integral_R |x|exp(-|x|)/(z-x)dx
 =4z integral_0^infinity x exp(-x)/(z^2-x^2)dx.          (8)
```

The limiting positive spectral measure is

```text
dmu_infinity(x)=2|x|exp(-|x|)dx,
mu_infinity(R)=4.                                        (9)
```

Hence `R_infinity` is anti-Herglotz and carries exactly the four-unit source budget.

## Analytic mismatch at the centered origin

On the positive imaginary axis, `(8)` gives

```text
R_infinity(i eta)/(i eta)
 =-4 integral_0^infinity x exp(-x)/(x^2+eta^2)dx.        (10)
```

The integral in `(10)` diverges to `+infinity` as `eta->0+`: on `[eta,1]` it is bounded below by

```text
(exp(-1)/2) integral_eta^1 dx/x.
```

Thus `R_infinity(z)/z` has logarithmically divergent magnitude at the origin.  In particular,
`R_infinity` has no holomorphic extension through `z=0` with finite derivative.

The continued prime--archimedean relative trace is already formalized to be analytic at `0` and
to vanish there.  Therefore it cannot equal `(8)` on any punctured upper neighborhood of `0`.
The exact convergence premise of
`riemannHypothesis_of_finiteKMSEntropyProductionResponse_tendsto` fails for this canonical
incidence normalization.

## No-go and positive HT theorem

**No-go:** scalar KMS entropy production erases the arithmetic framing.  Its critical response
remembers only the universal difference law of two exponential clocks, not the prime/Gamma
continuation or the squarefree overlap whose zeros carry the anti-causal divisor.

**Positive HT theorem:** a constrained hypertranscendental source can have an exactly calibrated
finite thermodynamic realization whose scalar passive response converges to a universal boundary-
layer law.  Equality of positive energy, passivity, and total Ward charge does not preserve the
analytic germ of the completed source.

**Proof-relevant successor:** retain the oriented current or the packet edge as an operator-valued
transition mark through Gamma/Sonin completion, and scalarize only on the closed squarefree
multiplication graph.  Any scalarization made before that graph quotient necessarily produces
`(8)` and loses the divisor.

## Gates

- [x] exact finite Gibbs realization
- [x] explicit Hermitian amplitude
- [x] KMS entropy production equals the incidence/Gini energy entry by entry
- [x] total critical mass equals four
- [x] limiting Laplace-gap spectral measure computed
- [x] passive response computed
- [x] logarithmic derivative singularity at the centered origin proved
- [x] incompatibility with the analytic continued prime--archimedean trace proved
- [x] scalar entropy-production RH route rejected by proof delivery rather than novelty
- [ ] construct the oriented operator-valued marked response on the closed squarefree graph
- [ ] RH
