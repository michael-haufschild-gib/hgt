# Corpus grounding

Searches were run before formula selection:

- `scripts/formal_tools.py research "complete positive-delay image direct characteristic physical cross current explicit coefficient cancellation next open"`
- `scripts/formal_tools.py research "signed_delay_finite_transfer spinTwo direct image branch antisymmetry numerical selector"`
- `scripts/formal_tools.py research "nativeSpinTwoTrace signed delay fullSquarePotential scalar center XiZeroCopy numerical circle mean explicit evaluation"`
- `scripts/formal_tools.py research "hyperbolic Bochner Laplacian squared scalar eigenfunction Hessian norm square fullSquarePotential spinTwo"`

The numerical object is grounded in current source, not a remembered HB model:

- `ThetaCuspHawkingBMSpinTwoDelayCharacteristic.lean`: `delayArgument`, `causalDelayStart`, `delayBulk`, `delayCurrent_endpoints`, and `signed_delay_finite_transfer`.
- `ThetaCuspHawkingBMNativeSpinTwoSource.lean`: `nativeSpinTwoTrace` and the full-square source.
- Current completed Eisenstein scalar and Fourier coefficients used by those source definitions.
- Current hyperbolic Bochner/Laplacian identities used to evaluate the spin-two density from scalar jets.

The search found no previous computation of this literal signed finite action. It also made the scope boundary explicit: the theorem closes characteristic and terminal delay-current endpoints, but physical lift/response currents and outer modular angular Green faces are separate source modules and are not terms of `signed_delay_finite_transfer`.

