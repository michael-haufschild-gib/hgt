# CCM-EP physical-child Fredholm wall transport

- **Status:** Formalized; targeted source check, leaf build, and axiom audit pass
- **Lean module:** `GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesPhysicalChildFredholmTransport`
- **Route:** CCM-EP / SP-E

## Frontier and novelty audit

Corpus search was performed before conjecturing. Queries covered physical child Fredholm
coefficients, ordered prime tuples, wall-normalized Stokes weights, balanced squared-child
determinants, and aperture-uniform determinant convergence. Existing P-G105V--P-G105X supplied:

- exact child-kernel factorization into transported diagonal weights and normalized cubic kernel;
- convergence of every fixed normalized wall Fredholm coefficient;
- one all-order Hadamard majorant and locally uniform convergence for normalized atomic wall laws;
- cofinal trace-class child operator and fixed-aperture physical determinant convergence.

P-G105X explicitly left identification with physical child coefficients open. No declaration
identified literal child minors with normalized atomic coefficients or transported P-G105X's
locally uniform limit through the singular Stokes mass `S_d -> 4`.

Targeted primary-literature search checked Connes--Consani's archimedean Weil-positivity work,
Connes--Moscovici's prolate operator, and Suzuki's screw-function and screw-line papers. These
develop trace/prolate/screw criteria, but the search found no corpus-specific P-G105K Stokes child,
ordered-prime Fredholm transport, or forced four-unit wall scaling. Diagonal-congruence algebra is
standard; claimed new content is its exact arithmetic instantiation and wall-limit consequence.

## New theorem

Let `w_d(p)` be literal transported Stokes weight, `S_d=sum_p w_d(p)`, and

```text
C(p,q) = 8 log(p)^(3/2) log(q)^(3/2) / (log(p)+log(q))^3.
```

For every positive aperture, order `n`, and ordered prime tuple `a`, exact physical child matrix is

```text
K_d(a_i,a_j) = sqrt(w_d(a_i)) C(a_i,a_j) sqrt(w_d(a_j)).
```

Therefore

```text
det K_d[a_i,a_j]
  = (product_i w_d(a_i)) det C[a_i,a_j].
```

Since normalized atomic weight is `w_d/S_d`, factorial-normalized complete ordered-prime
coefficient satisfies

```text
physicalChildCoefficient(d,n) = S_d^n * wallCoefficient(d,n).
```

Repeated tuples are retained and vanish only through their literal determinant. No order,
permutation, prime label, or cross-prime incidence is discarded.

The exact identity yields

```text
physicalChildDet(d,z) = wallDet(d,S_d z).
```

Using unconditional `S_d -> 4`, P-G105X fixed-coefficient convergence, and one common Hadamard
majorant, Lean proves both pointwise and locally uniform closed-disc convergence

```text
physicalChildDet(d,z) -> wallDet(expMeasure(1),4z),  d -> 0+.
```

## Scientific consequence

CCM-EP's coefficient-transport and order-uniform wall gates are closed for literal cofinal child
Fredholm expansion. Wall rescaling is forced by quantized Stokes charge `4`; it is not fitted to Xi.
Remaining EP core is arithmetic spectral landing: identify exponential-wall determinant's balanced
squared-child divisor with Xi without inserting Xi coefficients or zero data.

## Lean certificate

Principal declarations:

- `routePPrimitiveGammaJuliaStokesPhysicalChildFredholmMatrix_factorization`
- `det_routePPrimitiveGammaJuliaStokesPhysicalChildFredholmMatrix`
- `prod_transportWeight_eq_current_pow_mul_normalized`
- `routePPrimitiveGammaJuliaStokesPhysicalChildFredholmCoefficient_eq`
- `tendsto_routePPrimitiveGammaJuliaStokesPhysicalChildFredholmCoefficient_nhdsGT_zero`
- `norm_routePPrimitiveGammaJuliaStokesPhysicalChildFredholmCoefficient_le`
- `routePPrimitiveGammaJuliaStokesPhysicalChildFredholmEntireDet_eq_scaledWall`
- `tendsto_routePPrimitiveGammaJuliaStokesPhysicalChildFredholmEntireDet_nhdsGT_zero`
- `tendstoUniformlyOn_routePPrimitiveGammaJuliaStokesPhysicalChildFredholmEntireDet_nhdsGT_zero`

Verification after umbrella wiring:

- `lake env lean GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesPhysicalChildFredholmTransport.lean`
  passes;
- `lake build GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesPhysicalChildFredholmTransport`
  passes;
- `#print axioms` on matrix factorization, determinant transport, coefficient transport,
  coefficient limit, Hadamard bound, scaled determinant identity, pointwise wall limit, and
  locally uniform wall limit reports only `propext`, `Classical.choice`, and `Quot.sound`.
