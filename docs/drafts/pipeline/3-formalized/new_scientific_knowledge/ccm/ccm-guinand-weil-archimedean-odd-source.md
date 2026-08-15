# CCM Guinand--Weil singular archimedean odd source

- **Status:** LEAN-FORMALIZED
- **Lane:** CCM-FU / mixed-order source dictionary
- **Novelty scope:** corpus-new endpoint-order classification and exact complete odd-source weld;
  published archimedean sine integral and restricted-Weil counterterm are external inputs
- **Formal source:**
  `formal/GaloisForLFunctions/RHTower/CCMGuinandWeilArchimedeanOddSource.lean`

## Failed order-zero conjecture

C58 suggested that pole, prime, and archimedean channels could all be represented as finite-measure
functionals in `C([0,1],R)^*`. The literal archimedean density

```text
rho_Gamma(h)=exp(h/2)/(exp(h)-exp(-h))                            (1)
```

has a first-order endpoint pole. Lean proves its exact principal coefficient:

```text
h rho_Gamma(h) -> 1/2  as h -> 0+.                               (2)
```

Thus the raw Gamma channel is not another ordinary bounded density at the source endpoint. The
correct object is a higher-order source acting after an endpoint cancellation, as already encoded
globally by the counterterm in `ccmPublishedRestrictedArchimedeanPairing`.

## Positive survivor: physical sine cancellation

For every real frequency `xi`, Lean proves

```text
sin(xi h) rho_Gamma(h) -> xi/2  as h -> 0+,                      (3)
```

and proves the product interval-integrable on every positive finite aperture by an explicit
uniform bound. Therefore the physical odd coordinate can be formed without any totalized or
principal-value fiction:

```text
A_a(n)=-(1/pi) integral_0^(2a)
       sin(2*pi*n*omega_a(h)) rho_Gamma(h) dh.                    (4)
```

The affine horizon reflection `omega_a(h)=1-h/(2a)` turns the integrand in `(4)` into the published
logarithmic sine test with the required sign. Lean proves

```text
A_a(n)=ccmPublishedArchimedeanSineCoefficient(a,pi*n/a).         (5)
```

## Complete odd-source dictionary

Adding `(5)` to C59's separately constructed pole--prime continuous functional gives

```text
completedPhysicalOddSource(a,n)
  = ccmPublishedSourceSineCoefficient(a,pi*n/a)                  (6)
```

for every `a>0` and every natural mode `n`. Equation `(6)` is the complete published odd source,
with all three arithmetic channels retained before addition.

## CCM-FU consequence

The source space must be graded by distributional order. A single order-zero measure dual is
adequate for finite primes and the compact pole density but not for the raw Gamma endpoint. This
explains why attempts to place every channel in one finite-measure representation stalled: they
were shadows of a mixed-order source complex. Remaining matrix dictionary is the
endpoint-renormalized weighted-cosine diagonal, where the Gamma counterterm cannot disappear.

## Lean declarations

- `tendsto_h_mul_ccmPublishedArchimedeanDensity`
- `tendsto_sin_mul_ccmPublishedArchimedeanDensity`
- `ccmGuinandWeil_intervalIntegrable_sin_mul_archimedeanDensity`
- `ccmGuinandWeilArchimedeanOddSourceValue`
- `ccmGuinandWeil_intervalIntegrable_archimedeanOddSourceIntegrand`
- `ccmGuinandWeilArchimedeanOddSourceValue_eq_published`
- `ccmGuinandWeilCompletedPhysicalOddSourceValue`
- `ccmGuinandWeilCompletedPhysicalOddSourceValue_eq_published`

Targeted `lake env lean` and `lake build
GaloisForLFunctions.RHTower.CCMGuinandWeilArchimedeanOddSource` pass. `#print axioms` on principal
limit and capstone reports only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.
