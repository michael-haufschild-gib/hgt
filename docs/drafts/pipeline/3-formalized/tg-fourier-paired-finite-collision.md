# TG literal Fourier pairing removes the finite collision

- **ID:** TG-C8-FINITE
- **Stage:** 3-formalized
- **Route:** TG
- **Module:** `RHTower.PrimeBurnolFourierPair`
- **Parent:** `../1-in-progress/tg-fourier-paired-source-collision.md`

## Exact theorem

For every finite injective prime-depth packet, the clock-zero source columns
`f_i(r)=A_i r exp(-lambda_i r)` extend to the even physical functions
`e_i(x)=A_i |x| exp(-lambda_i |x|)`. The actual L2 family `(e_i, Fourier(e_i))` is linearly
independent. Its complete mixed Gram therefore has nonzero determinant. No Gamma matching,
independence, convergence, invertibility, or RH premise appears in either endpoint.

The exact Fourier integral is

`Fourier(e_i)(t) = 2 A_i (lambda_i²-(2 pi t)²)/(lambda_i²+(2 pi t)²)²`.

The even extension is unnormalized. Its positive-half-line restriction is exactly the existing
source; no implicit isometric or budget normalization is made.

## Proof and frontier contribution

The half-line monomial Laplace integral evaluates both Fourier half-lines. L1 and L2 admission
and the identification of the actual L2 Fourier image with this integral are proved. A vanishing
joint mixture on the positive real axis gives an entire identity after multiplying by all
squared rational denominators. Evaluation at `i lambda_j/(2 pi)` isolates its j-th Fourier
coefficient because all rates are distinct and positive. Existing literal source independence
then forces the remaining coefficients to vanish.

Thus an actual noncentral Fourier channel repairs the finite kernel that coherent opposite
clocks had at zero. Every cross-prime and Fourier cross term remains in the Gram. This is a
positive source result; finite repair alone does not produce a cofinal inverse, the completed
Gamma–Xi identity, a Hardy projection, or the TG action bound. The exact completion boundary is
formalized separately in `PrimeBurnolFourierCompletion`.

## Audit

- Production `lake --old env lean -o ... PrimeBurnolFourierPair.lean`: exit 0, no warnings.
- Separate `lake --old env lean /tmp/tg-c8-audit-01a0.lean`: all nine public theorems report
  only `propext`, `Classical.choice`, and `Quot.sound`.
- Default heartbeats; wired into RHTower; no full or umbrella build, numerical experiment,
  subagent, commit, or push. Final shared lint status is recorded on the completion card.
