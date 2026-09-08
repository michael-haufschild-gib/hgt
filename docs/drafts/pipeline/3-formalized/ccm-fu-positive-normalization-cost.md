# CCM-FU: physical cost of positive conditional normalization

- Stage: 3-formalized.
- Type: [BRIDGE], derived from existing source estimates; not a new RH conjecture.
- Goal chain: actual divisor source → uniform signed-energy control → O(M) Abel bound → CCM-FU → RH.
- Frontier map read only.

## Proved statement

Let `C_d(M)` be the literal source, `Q(M)=Σ C_d(M)^2`, and
`U(M)=Σ |C_d(M)|`, summing over `1≤d≤M`.

Unconditionally, `Q(M)` has positive quadratic lower growth and `U(M)`
has positive `M sqrt(M)` lower growth. More precisely, some fixed `c>0`
and `N≥1` satisfy, for every `M≥N`,

    c M Q(M) ≤ U(M)² ≤ M Q(M).

Thus the effective source size `U(M)^2/Q(M)` is bounded above and below
by positive constant multiples of M. The upper bound holds at every M.

For every nonnegative probability assignment `w_d` to these actual
indices, with `w_d=0` allowed only when `C_d=0`, weighted Cauchy gives
`U(M)^2 ≤ Σ C_d(M)^2/w_d`. If U is positive, `w_d=|C_d|/U` attains
equality, with the zero-source terms handled explicitly. Requiring every
weight to be strictly positive does not change the order of the optimum:

    w_d = (|C_d| + U/M)/(2U)

is a strictly positive probability assignment for M>0 and U>0, with
weighted energy at most `2U² ≤ 2M Q`. Therefore the optimized cost is
of order `M Q`, including under strict positivity. This is a sharp scale
comparison, not a rejection of source-specific quantitative dissipation.

## Dependency-closed paper argument

The corpus's first-prime reserve at prime two gives some fixed `c>0`
and all sufficiently large M:
`c M² ≤ Q(M)`, because the paired retained energy is nonnegative.
Every individual amplitude is at most `(3/5)sqrt(M)`.
Consequently `Q(M) ≤ sqrt(M) U(M)` and
`U(M) ≤ (3/5)M sqrt(M)`. Squaring the first inequality gives
`Q²≤M U²`; multiply `c M²≤Q` by Q and cancel the positive M to obtain
the lower effective-size bound. Finite Cauchy gives `U²≤M Q`.

The weighted lower bound is finite Cauchy; zero weights are split off
using their zero source coefficient. For optimal weights each summand
is `U |C_d|`. For strictly positive weights each summand is at most
`2U |C_d|`, and summing proves the claimed bound. All constants in the
source lower growth laws come from existing unconditional source results.

## Proof attempt beyond the bridge

The closest corpus alternative is exact conditional-variance dissipation
from `RouteEPhysicalFibreCoarea`. Its weighted energy contracts under
regrouping. Applying only that contraction carries the positive
normalization cost above into the terminal unnormalized estimate.
The required source-level saving in conditional energy remains to be
proved; positive normalization itself does not supply it. This statement
does not say that raw energy must grow by M under processing: the
weighting changes the energy being estimated.

For the optimal physical law `π_d=|C_d|/U`, use observable `sgn(C_d)`.
Its initial energy is one and its terminal conditional energy is
`(S/U)²`, where `S=Σ C_d`. Because `U` has scale `M sqrt(M)`, the target
`S=O(M)` requires terminal conditional energy `O(1/M)`. Equivalently,
the cumulative normalized variance must reach `1-O(1/M)`. Mere
nonnegativity or monotonicity of that variance leaves this estimate open.

At an intermediate partition, let `U_R` be a cell's absolute source mass
and `F_R` its signed mass. Conditional energy is
`E=(1/U)Σ_R F_R²/U_R`, with empty-mass cells contributing zero. The
exact comparison is `Σ_R F_R² ≤ U (max_R U_R) E`. The largest cell mass
starts at order at most `sqrt(M)` but becomes U at the endpoint. Thus
the relevant dynamic bound must control the product of the growing
cell mass and the dissipating conditional energy; the initial factor-M
cost cannot be silently discarded. No such dynamic source bound is
proved by the new leaf.

The cumulative-defect method in `MobiusBlockDefectEnergy` retains signed
prefix energy instead of total variation. Its exact Abel identity still
requires a bound on the actual signed prefix defects and their endpoint.
No such critical-rate bound has been obtained here. Numerical scans are
not needed to establish these algebraic and source-growth facts.

The uniform mean theorem in `DivisorUnsignedChannelExactMean` was also
checked as a possible source of quantitative dissipation. It gives
`A(M,d)=a sqrt(M)+o(sqrt(M))` uniformly when M/d tends to infinity.
On `d≤M/T`, its main signed sum still contains the actual truncated
Möbius sum `a sqrt(M) Σ_{d≤M/T} μ(d)`, rather than a complete Euler
product. Its absolute error is at most `ε sqrt(M) floor(M/T)` after
choosing T for ε, and the complementary d-tail remains. Neither bound
has the required O(M) scale. Dropping that tail or replacing the
truncated divisor set by the full prime cube would lose source terms.

## Lean surface and validation

Module:
[MobiusDivisorPositiveNormalizationCost](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorPositiveNormalizationCost.lean).

Ten public theorems:

- `mobiusDivisorAbsoluteMass_le`
- `mobiusDivisorDiagonal_le_sqrt_mul_absoluteMass`
- `exists_mobiusDivisorDiagonal_quadratic_lower`
- `exists_mobiusDivisorAbsoluteMass_lower`
- `mobiusDivisorAbsoluteMass_sq_le_card_diagonal`
- `exists_mobiusDivisorAbsoluteMass_sq_lower_diagonal`
- `mobiusDivisorAbsoluteMass_sq_le_weightedEnergy`
- `mobiusDivisorAbsoluteMass_optimal_weights`
- `exists_mobiusDivisor_positiveNormalization_cost`
- `exists_mobiusDivisor_strictlyPositiveNormalization_upper`

The complete scratch file and installed leaf passed `lake env lean`.
Only the new leaf olean was emitted. A separate scratch file audited the
ten new theorems once: only `propext`, `Classical.choice`, and `Quot.sound`.
No computational evidence or added axiom is used. The leaf is imported
by RHTower, without an umbrella build or re-audit of old declarations.

The final `lake build GaloisForLFunctions.RHTower.MobiusDivisorPositiveNormalizationCost`
passed in an isolated temporary package containing the byte-identical
leaf and this repository's toolchain. Empty-glob dependency packages
exposed the existing cached library directories; they contained no
dependency source targets. Lake compiled only the new leaf, reporting
9.1 seconds and successful completion with three jobs. Temporary cache
package manifests produced packaging warnings, with no Lean warnings.
No full or umbrella build ran.

Corpus indexes include the new module. Formal lint passed with existing
large-file warnings. Owned scratch files and the temporary audit package
were removed; no owned Lean process remained. The frontier map was not
edited. RH remains open; the goal is not complete.
