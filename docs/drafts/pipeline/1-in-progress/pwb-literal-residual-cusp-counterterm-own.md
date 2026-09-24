# PW-B literal residual-current cusp counterterm

- **Stage:** cusp-face premise formalized; PW-B incidence still open.
- **Chain:** literal CTP cap/lift → physical cyclic-Peierls metric current → residual cusp Stokes face → source-faithful outer boundary incidence → optical extinction → RH.

The corpus has the exact finite-height Stokes law for the original metric/left-QNM residual current, and separately proves rapid integrated cusp remainders for its square-reader and angular-flux terms. The hard test is whether these two results combine for the **actual frozen radial coefficients**, without dropping either face.

For `q,reader : XiZeroCopy`, physical branch/fibre data, and positive-height base point, put `A=cyclicPeierlsSquareCoefficient … base` and `B=cyclicPeierlsCapFluxCoefficient … base`. Let `J(y)=cyclicPeierlsResidualCuspBoundary … y`. Its candidate forced counterterm is

`P(y)=A·squareReaderPrincipalCuspFlux q reader y+B·constantVerticalFlux (center q) (physicalAngularParameter reader) y`.

**Proved:** For every `w : ℂ`, `y^w·(J(y)-P(y))→0` as `y→∞`; the unweighted form is proved separately. Lean: `ThetaCuspHawkingBMPWResidualCuspAsymptotic.lean`, theorems `residualCuspBoundary_weighted_sub_principal_tendsto_zero` and `residualCuspBoundary_sub_principal_tendsto_zero`. Proof splits the actual frozen-coefficient current under the width-one integral, then applies the corpus's complete square-reader forcing-tail and angular-flux integrated-decay theorems. No source component is dropped. Direct Lean check, exact-module `lake --old build`, axiom print, and formal lint passed; axiom print shows only Lean's standard `propext`, `Classical.choice`, `Quot.sound`.

**Whole-route meaning:** Outer *angular cusp-face reduction* of literal metric current is closed. Still open: identify time/radial two-event CTP functional with this same current, determine its two principal-channel incidence, and prove optical extinction. Zero boundary cannot be assumed: the explicit principal pair must be transported or countertermed source-faithfully.

**Guardrail from corpus:** `metric_only_incidence_forces_fullCausalPair_zero` already rules out deriving ordered CTP incidence from the exchange-symmetric complementary metric alone. Next carrier must retain the ordered current/contact sector alongside this metric cusp counterterm.
