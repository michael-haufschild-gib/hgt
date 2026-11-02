# Arithmetic Degeneration Theory (ADT): polarized limits of the sum–product surface

Namespace `GaloisForLFunctions.ArithmeticDegenerationTheory`; umbrella `ArithmeticDegenerationTheory.lean`.
Everything is unconditional. Theorems named `riemannHypothesis_iff_*` are equivalences, not proofs of RH.

## 1. Motivation

The research has reduced RH to one even integer `κ = κ(K_ζ)`, the number of distinct zeros right of
the critical line, read on one hyperplane `v₁^⊥` (pole-orthogonal vectors) of one degenerating family
of finite quadratic forms: the complete Weil matrices `W_{φ,c,N}` (atoms of a profile `φ` of width
`c/N` at `log n`, `n ≤ N`). Three walls stand in front of every route, and each is a question.

- **Σ (sign).** *What decides the sign of a form whose margin has fallen below the contribution of a
  single zero?* At the receiver scale the margin of the complete form and the zero side have the
  same order. A statement proved without zero information holds for every datum sharing that
  information, including data with off-line zeros, so it stops below their edge (EHT). The answer
  cannot be an inequality.
- **Π (precision).** *What produces a count at square-root precision over `ℤ`?* Over `𝔽_q` the count
  is a dimension (sections) or a cardinality (kernel points). Over `ℤ` every candidate count is soft
  or exactly RH (LST, ACS).
- **Γ (selection).** *What canonical operation identifies the reflection pairing `ρ ↔ 1 − ρ` with the
  conjugation pairing `ρ ↔ ρ̄`?* Over `𝔽_q` it is complex conjugation of Frobenius eigenvalues,
  forced by the polarization of the Jacobian. Over `ℤ` it has four RH-equivalent readings (EHT,
  Frobenius at infinity) and no construction.

The corpus has proved the logic behind these walls: estimates stop at the edge; every integer
invariant of the family, read at an RH-complete resolution, is RH; every selector is a margin on a
partial form. What can cross the edge is a statement that holds there **by structure** — an identity,
an inherited polarization, or an integer with a structural bound.

There is a classical theory in which positivity survives a degeneration by structure: Hodge theory
of degenerations. The polarization of a variation of Hodge structure over a punctured polydisc
degenerates in the naive limit; Schmid's nilpotent-orbit and `SL₂`-orbit theorems and the
multi-variable theory of Cattani–Kaplan–Schmid recover it. After rescaling by the monodromy weight
filtration the limit is a polarized mixed Hodge structure, polarized on its graded pieces, and the
polarization of the nearby fibres is inherited from it.

**ADT's thesis.** RH is the Hodge–Riemann relation of the degenerating family `W_{φ,c,N}` along the
resolution axis. The degeneration has a monodromy: the dilation semigroup `n ↦ pn`, one branch per
prime, the branches meeting only at the archimedean place. Positivity is to be obtained the way
Hodge theory of degenerations obtains it — not by estimating the limit (which is zero) but by
identifying the rescaled limiting structure, proving its polarization, identifying the extension
data between its graded pieces, and proving or exactly refuting inheritance. Counts, traces and
quantized readings are the three ways an identity can carry a sign through a limit.

ADT has carried this out for the limit. The rescaled limit exists, is explicit, and is arithmetic:
the **Jordan-totient form**. The monodromy is the dilation monoid acting on conductors by valuation
lowering; the limiting polarization is a tensor product of one weight string per prime; it is
inherited exactly up to the RH exponent, where the extension data begin to carry the zeros. The sign
is therefore a second-order phenomenon of the degeneration.

## 2. The dictionary

| Hodge theory of degenerations | ADT | Lean |
|---|---|---|
| parameter `t → 0` on a punctured disc | resolution `(c, N)`: overlap `c → ∞`, horizon `N → ∞` | EHT |
| monodromy, nilpotent `N` | dilation `n ↦ pn` on conductors: `c_m(pn) = w_p(m) c_{ℓ_p m}(n)` | `ramanujanLagCoefficient_prime_mul_eq` |
| cone of commuting nilpotents | lowerings by distinct primes commute; pole conductor the unique fixed point | `conductorLower_comm`, `forall_conductorLower_eq_self_iff` |
| quasi-unipotent monodromy | eventually idempotent monodromy: `D_p^{v+1} = D_p^v` on conductors of `p`-valuation `v` | `dilation_eventually_idempotent` |
| weight filtration | conductor towers `{m'p^a}` as weight strings | `jordanCoefficient_tower` |
| naive limit degenerates | `E_m(c) → 0` along every growing schedule | EHT `tendsto_limitForm_comp` |
| rescaled limit | `c^β E_m(c) → K J_{β+1}(m)/φ(m)` | `tendsto_rpow_mul_completedConductorEnergy` |
| polarized graded pieces | Jordan coefficients `J(m) > 0` | `jordanCoefficient_pos` |
| limiting MHS of a product | tensor law `J(1)J(ab) = J(a)J(b)` | `jordanCoefficient_mul_of_coprime` |
| extension data | cross-conductor residual channels | `conductorDeviation` |
| polarization recovered from graded pieces and extension data | cone expansion: `⟨W r_e, r_e⟩ = (log N)⁻¹ Σ_g θ_g(e)² Top_{c_g,N/g}(R_{e/(e,g)})` | `completeWeilEnergy_ramanujan_cone_expansion` |
| nilpotent-orbit theorem | rescaled finite family → Jordan form below exponent `1/8` | `tendsto_rescaledConductorGram` |
| `SL₂`-orbit approximation (one-variable scaling) | exact scaling form `E_m(c) = J(m)c⁻⁷R_m(c/m)` | `rpow_seven_mul_completedConductorEnergy_eq_scaling` |
| distance to the nilpotent orbit | relative residual `≍ c^{β+1}/log N` | HWV `exists_relative_conductorDeviation_sum_le` |
| `SL₂`-orbit | pole pair of the boost–successor plane, blind on `v₁^⊥` | RIT, AKG |
| one negative square of the period domain | the pole: gluing determinant, glued index `κ + 1` | `det_redhefferMatrix`; AKG |
| degeneration of a family of fibres | twists: the limit tends to an overlap-independent form `F_λ`; `F_Λ = 0` | `tendsto_packetEnergy_atTop`, `twistLimitEnergy_vonMangoldt` |
| function fields | finite monodromy, trivial flow, detection by window `2g` | EHT, ACS |

## 3. Objects

| Object | Lean | Meaning |
|---|---|---|
| Complete Weil family | RAPT `completeWeilMatrix`, `completeWeilEnergy` | the variation |
| Ramanujan packets | RAPT `normalizedRamanujanHorizonVector`, `ramanujanPoleProfile` | graded pieces, `r_m(n) = c_m(n)/√(φ(m)n)` |
| Completed conductor energies | RAPT `completedConductorEnergy` | `E_m(c) = φ(m)⁻¹ Σ_{d∣m} μ(m/d) d E(c/d)` |
| Spectral tail | `spectralTail` | `T(x) = ∫_x^∞ |φ̂(2πt)|² dt` |
| Jordan totient, zeta sums | `jordanTotient`, `jordanAF`, `zetaSum`, `coprimeZetaSum` | `J_k = μ ∗ id^k`, `Σ n^{-k}`, `Σ_{(n,m)=1} n^{-k}` |
| Tilted spline data | `splineNumerator`, `splineWeight`, `splineNumeratorMean`, `tiltedTailConstant` | `q(x) = (sinh²1 + sin²x)⁴`, `(1+x²)⁻⁴`, its mean, `A_φ` |
| Jordan coefficient | `jordanCoefficient` | `J(m) = lim c⁷E_m(c) = (2A_φ/M) ζ(8) J₈(m)/φ(m)` |
| Conductor entries | `conductorEntry`, `conductorDeviation`, `rescaledConductorGram` | `⟨W r_e, r_{e'}⟩`, its residual channel, `c⁷` times it |
| Lowering, weights | `conductorLower`, `dilationWeight`, `dilationFactor`, `coneFactor` | `ℓ_p m`, `w_p(m) ∈ {1, p−1, p}`, `θ_p(m) ∈ {1/√p, √((p−1)/p), 1}`, `θ_g(m) = √(φ(m)/(gφ(m/(m,g))))` |
| Top-stratum energy | `topStratumEnergy` | `Σ_{(a,b)=1} W_{c,M}(a,b) y_a y_b` |
| `p`-integer | `pInteger` | `[8]_p = (p⁸−1)/(p−1)` |
| Scaling function | `tailProfile`, `shellAverage`, `scalingFunction` | `g(y) = y⁷T(y)`, `R_m(x) = Σ_{(n,m)=1} n^{-8}g(nx)/(A_φ Σ_{(n,m)=1} n^{-8})` |
| Divisibility, Möbius, Redheffer forms | `divisibilityMatrix`, `moebiusMatrix`, `redhefferMatrix` | `[i∣j]`, `μ(j/i)[i∣j]`, `[i∣j ∨ j=1]` |
| Stars, strata, nerve | HWV `starRestrict`, `completeWeilEnergy_gcd_stratification`, `nerveEulerChar` | the cone and its gluing |
| Glued archimedean state | AKG `archGlue`, `weilArchState` | the one negative square |
| Trace carriers | RHTower CCM `ccmArchimedeanWeilDistribution`, Sonin cutoffs | positivity as a trace |
| Section counts | LST `primitiveH1`, `kunnethH0`, `coneCount` | positivity as a count |
| Quantized readings | EHT `horizonDefect`; RHTower `xiHorizontalCollisionCharge` | positivity as an integer |
| Twisted limit structure | RAPT `packetEnergy`, `twistLimitEnergy`, `primeFlipWeight` | `Σ β_m² E_m(c) + F_λ(y)` |
| Fakes | ACS `goldenDatum`; LST Epstein lattices; prime-flip and Liouville twins | the control |

## 4. Language

- **Resolution** `(c, N)`; **universal regime / edge / RH regime** as in EHT.
- **Edge-valid statement**: holds at every resolution, edge included (identity, inherited
  polarization, integer with a structural bound).
- **Carrier**: a mechanism carrying a sign through a limit — a count, a trace, a quantized reading.
- **Tail exponent** `β` of a profile: `x^β T(x) → A`. The tilted spline has `β = 7`.
- **Rescaled limit**: the limit of `c^β ⟨W r_e, r_{e'}⟩`. **Jordan form**: `Σ J(m) y_m²`.
- **Weight string**: a conductor tower `{m'p^a}` with the steps of the Jordan coefficient along it.
  **Bottom step** (`p ∥ m`): `[β+1]_p`. **Deep step** (`p² ∣ m`): `p^β`.
- **Subthreshold block** `m ≪ c` (degenerating, Jordan); **threshold** `m ≍ c` (receiver);
  **pure block** `m ≫ c` (non-degenerating, energies `≍ log m`).
- **Extension datum**: the residual channel `⟨W r_e, r_{e'}⟩ − E_e⟨r_e, r_{e'}⟩`.
- **Inheritance radius**: the largest exponent `α` such that along every schedule
  `c ≤ (log N)^α` the rescaled extension data vanish.
- **Gluing**: a rank-one or one-hyperplane coupling through the pole.
- **Fake**: a datum on which a soft law holds and RH fails.

## 5. Mechanisms

**A. The edge logic selects the carriers.** An estimate valid for a class of data stops below the
edge of every off-line member (EHT); an integer read at an RH-complete resolution is RH. A sign must
be carried by an identity, an inherited polarization, or an integer with a structural bound, built
from the Euler product, the functional equation and the pole as identities.

**B. Regular tails give arithmetic rescaled limits.** The conductor-one energy is the repayment series
`E(c) = (2/M) Σ_n n⁻¹ T(nc)`. If `x^β T(x) → A`, Tannery's theorem gives `c^β E(c) → (2A/M) ζ(β+1)`.
The conductor energies are Möbius combinations of the star energies `d E(c/d)`, and the rescaled
star energy of depth `d` is `d^{β+1}` times that of the pole: the dilation monoid acts on the rescaled
limit by the character `d ↦ d^{β+1}`, whose Möbius transform is Jordan's totient. The coprime
repayment series gives the same limit as `(2A/(Mφ(m))) m^{β+1} Σ_{(n,m)=1} n^{-(β+1)}`, manifestly
positive; comparing the two readings is the identity `ζ(k) J_k(m) = m^k Σ_{(n,m)=1} n^{-k}`.

**C. The tilted spline's spectrum is explicit.** With `x = πt/4`,
`|φ̂(2πt)|² = (1/64)((sinh²1 + sin²x)/(1 + x²))⁴`: the boosted cubic spline has transform
`(sin z/z)⁴` on the line `z = x − i`, and `|sin(x − i)|² = sinh²1 + sin²x`. The numerator is
`π`-periodic; a block comparison over periods shows that a periodic factor modulating an antitone
integrable weight contributes its mean, so `c⁷ T(c) → A_φ = (4/π)⁷/(16π) · μ_q/7 > 0`.

**C′. The exponent is the profile's.** For every `C²` profile supported in `[0, 1]`, two
integrations by parts and Riemann–Lebesgue give `|φ̂(2πt)|² = o(t⁻⁴)`, so `x³T(x) → 0` and
`c³E_m(c) → 0`: every admissible profile degenerates faster than cubically. The tilted spline
degenerates at exactly the seventh power: `c^βE_m(c)` tends to `0`, to `J(m)`, or to `∞` according as
`β < 7`, `β = 7`, `β > 7`. The exponent is analytic (the profile), the coefficients arithmetic (the
conductor).

**D. The limiting mixed structure.** In the conductor basis
`⟨W r_e, r_{e'}⟩ = E_e ⟨r_e, r_{e'}⟩ + (extension datum)`. The Gram of the packets tends to the
identity (RAPT); `c⁷ E_e → J(e)`; HWV bounds the extension data relative to the margins by
`O((c⁸(1 + log c)² (log N)^{1/k}/log N)²)`. Along every schedule `c ≤ (log N)^α`, `α < 1/8`, the
rescaled form converges entrywise to the Jordan form, and every fixed packet inherits its positivity.
The first-order non-orthogonality of the packets is itself carried by the monodromy: the `1/log N`
off-diagonal of the exact Gram law joins a conductor only to its tower neighbours `m p^k`
(CompletedArithmeticForms `normalizedRamanujanHorizonVector_gram_exact`).

**E. The inheritance radius is the RH exponent.** Below `1/8` the rescaled extension data vanish on
every fixed pair of conductors; at every multiple of `(log N)^{1/8}` positivity of the conductor Gram
over all conductors is RH (HWV). For the tilted spline the exponent is `1/(7+1)`: margin `c^{-7}`
against a residual of order `c/log N`. For a general profile the same balance reads `1/(β+1)`; EHT's
profile covariance (RH regime from `c⁴/log N → ∞` for every `C²` profile) is the case `β = 3`.

**F. The monodromy lowers conductors.** Möbius lowering: any Möbius transform `Σ_{d∣m} μ(m/d) g(d)` of
a function homogeneous along the `p`-tower (`g(pd) = a h(d)`, `g(d) = h(d)` for `p ∤ d`) is `a` (if
`p² ∣ m`) or `a − 1` (if `p ∥ m`) times the transform of `h` at `m/p`. For Ramanujan sums
(`g(d) = d[d ∣ pn]`) this is the dilation law; for Jordan's totient (`g(d) = d^k`) it is the tower
law. In the pole gauge the dilation is an isometric lowering deep in a tower (`θ_p(m) = 1`).
Iterating, a string of length `v = v_p(m)` is exhausted after exactly `v` dilations,
`c_m(p^k n) = φ(p^v) c_{m/p^v}(n)` for `k ≥ v`: the monodromy is eventually idempotent
(`D_p^v(D_p − 1) = 0` on the string), with spectrum `{0, 1}` instead of the roots of unity of a
quasi-unipotent monodromy, and `c_m(dn) = φ(m)` whenever `m ∣ d`.

**F′. The monodromy in closed form and the cone expansion.** The weights telescope along a
factorization: `c_m(gn) = (φ(m)/φ(m/(m,g))) c_{m/(m,g)}(n)` for all `g ≥ 1`, i.e. the dilation by `g`
lowers `m` to `m/gcd(m,g)`; in the pole gauge `r_m(gn) = θ_g(m) r_{m/(m,g)}(n)`. Combined with the gcd
stratification (HWV), the energy of a graded piece is a positive combination over the cone of
top-stratum energies of lowered conductors at the star resolutions:
`⟨W_{c,N} r_e, r_e⟩ = (log N)⁻¹ Σ_{g≤N} θ_g(e)² Top_{c_g,⌊N/g⌋}(R_{e/(e,g)})`. The polarization of
every graded piece is reconstructed from top-stratum data: this identifies the extension data of the
limiting structure with the top coprime stratum. The Möbius gluing of stars inverts the expansion:
`Top_{c,N}(r_e) = ⟨W r_e, r_e⟩ + (log N)⁻¹ Σ_{2≤d≤N} μ(d) θ_d(e)² ⟨W_{c_d,⌊N/d⌋} R_{e/(e,d)}, R_{e/(e,d)}⟩`.
Graded pieces and top stratum are a Möbius pair over the cone; the forward direction is sign-free,
the inverse alternating, which is why positivity of the graded pieces does not pass to the top
stratum.

**G. Weight strings and the tensor law.** Along a `p`-tower the Jordan coefficient climbs by `[8]_p`
at the bottom and by `p⁷` per deep step: `J(p^a) = J(1)[8]_p p^{7(a−1)}`. For coprime conductors
`J(1)J(ab) = J(a)J(b)`. The limiting polarization is a tensor product of independent strings, one per
prime; the archimedean place enters only through the scalar `J(1)`.

**H. The uniform law on the subthreshold block.** Every term of the coprime repayment series samples
the tail at `ac/m ≥ c/m`, so `|c⁷E_m(c) − J(m)| ≤ εJ(m)` uniformly for `m ≤ c/X(ε)`. The Jordan
polarization is exact on the whole degenerating block; the threshold `m ≍ c` is where each conductor
reaches the receiver; beyond it the energies grow like `log m` (pure part, RAPT
`log_conductor_sub_log_overlap_le_completedEnergy`). Exactly: `E_m(c) = J(m)c⁻⁷R_m(c/m)`, where the
scaling function `R_m` averages one profile function `g(y) = y⁷T(y)` over the shells prime to `m`;
`R_m → 1` at the degenerating end uniformly in `m`, and `0 ≤ R_m(x) ≤ Cx` at the pure end. On fixed
packets the form inherits the Jordan polarization with arbitrarily small loss, uniformly in the
coefficients. The two factors read different data: `R_m` depends only on the prime factors of `m`
(the branches of the cone it lies on), `J(m)` on the valuations (the positions in the strings). A
whole `p`-tower degenerates along the single function `R_p`:
`c⁷E_{p^a}(c) = J(1)[8]_p p^{7(a−1)} R_p(c/p^a)`.

**H′. The whole subthreshold block inherits the Jordan form.** Along every schedule below `1/8` and
for every `ε`, eventually and for all coefficients on the growing block `{e ≤ c/X(ε)}`,
`|c⁷⟨Wx, x⟩ − Σ J(e)b_e²| ≤ ε Σ J(e)b_e²`. Three errors are controlled relative to the Jordan form:
the diagonal (uniform Jordan law), the non-orthogonality of the packets
(`|⟨r_e, r_{e'}⟩ − δ| ≤ (2ee'(√(φ(e)φ(e')) + 1) + 1)/log N`, from periodicity and orthogonality of
Ramanujan sums over a period, weighted by the spread `√ζ(8)Q⁴` of the Jordan coefficients: `O(c⁸/log N)`),
and the extension data (relative Hilbert–Schmidt norm, HWV). This is the inherited polarization on the
subthreshold block `m ≲ c` past the universal regime `1/9` of the whole space.

**I. Gluing at the pole.** The divisibility form `[i ∣ j]` on `1..N` is unipotent (determinant `1`,
inverse the Möbius form). Gluing every vertex to the pole — replacing the pole column by `𝟙` — gives
Redheffer's matrix, whose determinant is the Mertens function (Cramer's rule: the pole coordinate of
`Z⁻¹𝟙`). The whole arithmetic of `μ` is created by one rank-one gluing at the pole, and it equals the
Euler characteristic of the nerve of the star cover (HWV). The coprimality form of the top stratum
has inertia (`#{μ=1}`, `#{μ=−1}`, `#{μ=0}`) and signature `M(N)` (RHTower): determinant and signature
readings of the same gluing.

**J. Traces.** The archimedean Weil distribution is a trace, `−W_∞(g ⋆ g*) = Tr(ϑ(g)(1 − P − P̂)ϑ(g)†)`,
and `1 − P − P̂` is the central Sonin projection modulo compacts (RHTower CCM). The middle operator
`A = 1 − P − Q` of two self-adjoint idempotents satisfies `A² + (P − Q)² = 1` and anticommutes with
`P − Q`, so its generic spectrum is symmetric; `Re⟨Av, v⟩ = −‖Qv‖²` on the range of `P`,
`−‖Pv‖²` on the range of `Q`, and `A = 1` on the common kernel. The archimedean carrier is therefore
negative semidefinite on the whole time-limited space and on the whole band-limited space: the trace
identity at `∞` is an identity with an indefinite middle operator, and the pole terms must pay its
negative part.

**K. Counts and quantized readings** (LST, AOG, EHT): Gaussian lattice `h⁰` with linear
Riemann–Roch; Künneth `h¹ = h¹_K + ½δ`; bidegree counts blind; collision charges bound horizon
defects. A count carries the sign only if it reads the primitive part; an integer only with a
structural bound below `2`.

**L. Complete degeneration selects `ζ`.** For a twist `λ` with summable defect the fixed-overlap
limit on Ramanujan packets is `Σ β_m² E_m(c) + F_λ(y)` with `F_λ` independent of the overlap (RAPT).
As `c → ∞` it tends to `F_λ`, not to `0`. For `λ = Λ` the defect vanishes and the degeneration is
complete, with the Jordan rescaled limit. For a prime flip, `F_{ω_p}` is positive on the pole packet
(`4 log p Σ_j p^{-(2j+1)}`) and negative on some unit packet: the twin degenerates to an indefinite
form of weight zero, and its rescaled energy tends to `−∞`. The same holds for every nonempty finite
flip set `S`: its residue `F_{ω_S}` is positive on the pole profile and negative on the flip-set trial.
Selection here is an identity (`d_Λ = 0`), not a margin; it does not decide the sign of `ζ`.

## 6. Questions and answers

| Question | Answer | Lean |
|---|---|---|
| What is the rescaled limit of the degenerating family, and is it polarized? | For a profile with regular tail `x^βT(x) → A`, the rescaled conductor energies converge to `(2A/M)ζ(β+1)J_{β+1}(m)/φ(m) > 0`. For the tilted spline `β = 7` with explicit `A_φ`, and the rescaled finite family converges entrywise to the Jordan form along every schedule below `1/8`. | `tendsto_rpow_mul_completedConductorEnergy`, `tendsto_rpow_seven_mul_spectralTail_tiltedUnitSpline`, `tendsto_rescaledConductorGram` |
| What sets the rate of the degeneration? | The profile: every admissible profile has `c³E_m(c) → 0`; the tilted spline has exponent exactly `7`. The rate sets the Jordan exponent and the inheritance radius; the arithmetic sets the coefficients. | `tendsto_rpow_three_mul_completedConductorEnergy`, `tiltedUnitSpline_degeneration_exponent` |
| How does the monodromy act on the graded pieces? | By valuation lowering: `c_m(pn) = w_p(m)c_{ℓ_p m}(n)`, `r_m(pn) = θ_p(m) r_{ℓ_p m}(n)`. Lowerings commute; the pole conductor is the unique common fixed point. | `ramanujanLagCoefficient_prime_mul_eq`, `ramanujanPoleProfile_prime_mul`, `conductorLower_comm` |
| Is the conductor filtration the weight filtration? | Yes in the rescaled sense: along each tower the Jordan coefficient is a weight string (`[8]_p`, then `p⁷` per step); the polarization tensorizes over the primes. | `jordanCoefficient_tower`, `jordanCoefficient_mul_of_coprime`, `jordanCoefficient_prime_pow` |
| Where is the inheritance radius? | Exactly at the RH exponent `1/8`: below it the rescaled extension data vanish; at its multiples positivity is RH. | `inheritance_radius` |
| Is the polarization inherited on the subthreshold block past the universal regime? | Yes: on the whole growing block `{e ≤ c/X(ε)}` along every schedule below `1/8`, `c⁷⟨Wx,x⟩` is within `ε` of the Jordan form, uniformly in the coefficients. | `eventually_subthreshold_block_jordan` |
| Is the limit exact on growing blocks? | On the whole subthreshold block `m ≤ c/X(ε)`, uniformly; exactly, the degeneration has the scaling form `E_m(c) = J(m)c⁻⁷R_m(c/m)` with `R_m → 1` (degenerating end) and `R_m(x) ≤ Cx` (pure end), uniformly in `m`. | `uniform_jordan_law`, `rpow_seven_mul_completedConductorEnergy_eq_scaling`, `abs_scalingFunction_sub_one_le`, `scalingFunction_le` |
| What do the two factors of the degeneration see? | The scaling function sees only the branches (prime support), the Jordan coefficient only the weights (valuations); a tower degenerates along one scaling function. | `scalingFunction_eq_of_primeFactors_eq`, `completedConductorEnergy_prime_pow_eq` |
| Are the extension data the top stratum? | Yes, exactly: every graded-piece energy is a `θ²`-weighted cone sum of top-stratum energies of lowered conductors at the star resolutions, and conversely every top-stratum energy is the Möbius-signed cone sum of lowered graded energies. | `ramanujanLagCoefficient_mul_eq`, `ramanujanPoleProfile_mul_eq`, `completeWeilEnergy_ramanujan_cone_expansion`, `topStratumEnergy_ramanujan_moebius_expansion` |
| What kind of monodromy is it? | Eventually idempotent, not quasi-unipotent: on a `p`-string of length `v`, `D_p^{v+1} = D_p^v`; the nilpotent length is the valuation. | `ramanujanLagCoefficient_prime_pow_mul`, `dilation_eventually_idempotent`, `ramanujanLagCoefficient_mul_of_dvd` |
| What does the archimedean trace carrier contribute? | An indefinite middle operator: symmetric generic spectrum, negative on time- and band-limited vectors, identity on their common orthocomplement; positivity must come from the pole terms or from another carrier. | `archimedeanCarrier_twoProjection`, `archimedeanCarrier_negative_on_timeLimited` |
| Does the limit see the zeros, and does it select `ζ`? | It does not see the zeros: it is computed from the profile's tail and the arithmetic of the conductor; zeros enter at the quantum `1/log N`. It does select `ζ` among prime-flip twins by structure: only `ζ` degenerates completely; every flip degenerates to a nonzero indefinite form and has no rescaled limit. | `tendsto_rpow_mul_completedConductorEnergy`; `primeFlip_degenerates_indefinitely`, `tendsto_rescaled_packetEnergy_primeFlip`, `tendsto_rescaled_packetEnergy_vonMangoldt` |
| Is there a signature/determinant invariant refining the nerve's Euler characteristic? | The Mertens function is the determinant of the pole gluing of the divisibility form and the signature of the coprimality form; RH is half-power growth of either; unconditionally the gluing determinant oscillates at `±c√N`. | `det_redhefferMatrix`, `riemannHypothesis_iff_det_redhefferMatrix`, `det_redhefferMatrix_omega_pm_sqrt`; RHTower `finiteMobiusCoprimeSignature_eq_sum_Icc` |

## 7. Pillar theorems

| Pillar | Lean | Status |
|---|---|---|
| Jordan-totient rescaled limit for regular tails (Möbius and coprime forms) | `tendsto_rpow_mul_completedShellEnergy`, `tendsto_rpow_mul_completedConductorEnergy`, `tendsto_rpow_mul_completedConductorEnergy_coprime` | proved |
| Exact spectrum and regular tail of the tilted spline | `shellSpectrum_tiltedUnitSpline`, `periodic_tail_squeeze`, `tendsto_rpow_seven_mul_spectralTail_tiltedUnitSpline` | proved |
| Degeneration exponent: every admissible profile faster than cubic; the tilted spline exactly seventh order | `tendsto_paperFT_atTop`, `tendsto_rpow_three_mul_spectralTail`, `tendsto_rpow_three_mul_completedConductorEnergy`, `tiltedUnitSpline_degeneration_exponent` | proved |
| Limiting mixed structure of the complete Weil family | `tendsto_rescaled_conductorDeviation`, `tendsto_rescaledConductorGram`, `tendsto_rescaled_packet`, `eventually_pos_of_rescaled_limit` | proved |
| Inheritance radius = RH exponent | `inheritance_radius` | proved; equivalence half from HWV |
| Monodromy: dilation lowers the conductor; commuting cone | `ramanujanLagCoefficient_prime_mul_eq`, `ramanujanPoleProfile_prime_mul`, `conductorLower_comm`, `dilationWeight_cocycle` | proved |
| Weight strings and tensor law of the limiting polarization | `sum_divisors_moebius_lowering`, `jordanCoefficient_tower`, `jordanCoefficient_mul_of_coprime`, `jordanCoefficient_prime_pow` | proved |
| Uniform Jordan law on the subthreshold block | `uniform_jordan_law`, `tendsto_ratio_of_subthreshold` | proved |
| The whole growing subthreshold block inherits the Jordan form below `1/8` | `abs_inner_normalizedRamanujanHorizonVector_sub_le`, `jordanCoefficient_bounds`, `block_bound`, `block_estimate_at`, `eventually_subthreshold_block_jordan` | proved |
| Exact scaling form; both ends of the scaling function; inherited polarization with small loss | `rpow_seven_mul_completedConductorEnergy_eq_scaling`, `abs_scalingFunction_sub_one_le`, `scalingFunction_le`, `eventually_inherited_polarization` | proved |
| Eventually idempotent monodromy | `ramanujanLagCoefficient_prime_pow_mul`, `dilation_eventually_idempotent`, `ramanujanLagCoefficient_mul_of_dvd` | proved |
| Graded pieces and top stratum are Möbius dual over the cone | `topStratumEnergy_ramanujan_moebius_expansion` | proved |
| Monodromy in closed form; cone expansion into top strata | `ramanujanLagCoefficient_mul_eq`, `ramanujanPoleProfile_mul_eq`, `completeWeilEnergy_ramanujan_cone_expansion` | proved |
| The archimedean trace carrier is indefinite (two-projection identities; negative on time- and band-limited spaces) | `twoProjection_sq_add_sq`, `twoProjection_anticomm`, `archimedeanCarrier_negative_on_timeLimited`, `archimedeanCarrier_negative_on_bandLimited` | proved |
| Branches and weights separate; a tower degenerates along one scaling function | `scalingFunction_eq_of_primeFactors_eq`, `completedConductorEnergy_prime_pow_eq` | proved |
| Mertens function = gluing determinant at the pole; square-root oscillation | `det_redhefferMatrix`, `det_redhefferMatrix_eq_nerveEulerChar`, `riemannHypothesis_iff_det_redhefferMatrix`, `det_redhefferMatrix_omega_pm_sqrt` | proved; equivalence |
| Complete degeneration selects `ζ` among prime-flip and finite-flip twins | `tendsto_packetEnergy_atTop`, `packetEnergy_vonMangoldt`, `primeFlip_degenerates_indefinitely`, `tendsto_rescaled_packetEnergy_primeFlip`, `finiteFlip_residue_indefinite` | proved |

## 8. Tools

**Developed.**
- Tannery passage for rescaled repayment series; Jordan totients with real exponent; zeta and
  coprime zeta sums.
- Periodic tail squeeze: periodic modulation of antitone integrable weights.
- Exact modulus of the uniform transform on a boosted line.
- Error envelopes for power-of-log schedules (`exists_tendsto_envelope`).
- Möbius lowering lemma for Möbius transforms homogeneous along a tower.
- Lowering maps of conductors and their cone.
- Divisibility/Möbius/Redheffer matrices and the Cramer-rule gluing determinant.
- Large-overlap limits of twisted limit structures.
- Closed-form monodromy `c_m(gn) = (φ(m)/φ(m/(m,g))) c_{m/(m,g)}(n)` and the forward and Möbius-dual
  cone expansions over the gcd stratification.
- Uniform non-orthogonality bound for Ramanujan packets; a deterministic block bound (diagonal, Gram
  and extension errors relative to a weighted form); bilinear Cauchy–Schwarz with Hilbert–Schmidt norm.
- Two-projection calculus for self-adjoint idempotents.
- Riemann–Lebesgue for the paper transform; tail exponents of profiles.

**To build.**
- Second-order rescaled limit at the critical curve `c⁸ ≍ log N`.
- Rescaled limits for twists with non-summable defect (the Liouville twin, cofinite flips).
- A uniform pure-end law `E_m(c) = log(m/c) + τ(m) + O(1)` for `m ≫ c ≥ 1` (below touching the
  conductor energy is exactly RAPT's reference energy; the lower bound is RAPT's
  `log_conductor_sub_log_overlap_le_completedEnergy`).

## 9. Open research topics

1. **Second order at the critical curve.** Along `c⁸ = K log N` the rescaled extension data are of
   order one. Identify their limit on fixed packets, its dependence on the zeros, and its sign.
2. **The threshold block `m ≍ c`.** The receiver of each conductor; the coupling of the degenerating
   block to the pure block (the 1/9 → 1/8 gap of the whole space).
3. **Trace carriers at the primes**: a semilocal carrier with logarithmic response at `2`, then
   `{2, 3}`; the archimedean gluing as a trace identity.
4. **The `GL₂` section theory of the split surface**: Voronoi as logarithmic Serre duality of the cone
   count; Eisenstein series at the centre.
5. **The top stratum**: successor and archimedean coupling of coprime atoms; sum–product inequality on
   conductor packets.
6. **Quantized readings with source bounds**: Szegő-type positivity of the integer-theta symbol.
7. **The conjugation side from the prime side**: Hecke defects at logarithmic scale.
8. **Naive heights** at bounded distance from the Rosati form.
9. **The scattering side**: Lax–Phillips and Lewis–Zagier structure on the Gauss–Mayer
   eigenfunctions.
10. **Calibration**: rescaled limits over `𝔽_q(T)`; the limiting structure of the fakes.

## 10. Traps

| Trap | Fact |
|---|---|
| The limit structure polarizes the edge | It degenerates to `0` along every growing schedule (EHT) |
| A positive rescaled limit is progress toward RH | It depends only on the profile's tail and the conductor; zeros enter at the quantum `1/log N` |
| Inheritance can be pushed by sharper estimates | Its radius is the RH exponent; at `c ≍ (log N)^{1/8}` the extension data carry the zeros |
| The weights of the limit are a common floor | They are an arithmetic weight string per prime, tensorized over the primes |
| Dilation is a Lefschetz operator | On conductors it is a lowering operator; isometric deep in a tower |
| Lowerings generate positivity | They fix the pole conductor and lower everything else to it; they transport the polarization, they do not create it |
| The `SL₂` of the pole carries the sign | It is blind on `v₁^⊥` (RIT) |
| A trace identity is a positivity statement | The archimedean middle operator `1 − P − P̂` is negative semidefinite on the time-limited and band-limited spaces (`archimedeanCarrier_negative_on_timeLimited`) |
| Local unipotent structure glues freely | One rank-one gluing at the pole creates the Mertens function |
| Soft laws select | Every soft law holds on the fakes |
| Selecting `ζ` by its limit decides the sign | Complete degeneration separates `ζ` from its flips by an identity; the sign of `ζ` sits in the second-order term |

## 11. Context

| Neighbour | Interface |
|---|---|
| EdgeHodgeTheory | edge, limit form, integer readings; ADT computes EHT's rescaled limit (its "to build" second-order asymptotics) |
| HodgeTheoryWithoutVarieties | stars, gluing, nerve, cross-conductor deviation; ADT reads stars and conductors as monodromy and weight |
| RenormalizedArithmeticPotentialTheory | complete Weil matrix, completed conductor energies, repayment, quasimodes, orthonormality |
| CriticalArithmeticCorrelationTheory | universal regime, bilinear residuals, polylogarithmic packets |
| LatticeSectionTheory, ArithmeticOrientationGeometry | counts, primitive `h¹`, theta `h⁰` |
| ArithmeticCouplingTheory | packet identity, localization in a finite conductor sector |
| AdelicKreinGeometry, RenormalizedIntersectionTheory | gluing at `∞`, pole blindness |
| RHTower (CCM, Sonin, Möbius coprime inertia) | archimedean trace identities; inertia of the coprimality form |
| ArithmeticCastelnuovoSeveri | calibration over `𝔽_q`, fakes |

## 12. Success criteria

| Criterion | Status |
|---|---|
| A limiting polarized structure with the prime cone as monodromy, polarized on graded pieces, extension data identified | Rescaled limit, monodromy (closed form), weight strings, tensor law, extension data = top stratum (cone expansion), inheritance on the whole growing subthreshold block below `1/8`: proved |
| The inheritance radius determined exactly | `1/8` for the tilted spline: inheritance proved below it (on every fixed packet and on the whole growing subthreshold block), RH at it; the same balance gives `1/(β+1)` for a profile of tail exponent `β` |
| Positivity on `v₁^⊥` past the universal regime by an edge-valid mechanism | Open; ADT locates it in the second-order limit at the critical curve |
| A count or trace equal to `½W` on a growing family, starting with the prime-free window | Open (CCM trace identity at `∞`; pole terms not yet carried) |
| A gluing theorem with one negative square and an exact coupling | Determinant form at the pole: Redheffer; signature form: coprime inertia; AKG index `κ + 1` |
| Exact behaviour on the fakes | Prime-flip and finite-flip twins: incomplete degeneration to an indefinite residue, no rescaled limit (proved); the limit is zero-blind; Liouville twin and lattice fakes open |

## 13. What counts as a contribution

- A Lean theorem, unconditional, in this folder, wired into the umbrella.
- It is a statement about the degenerating family read through its limit — rescaled limits,
  monodromy, weight strings, extension data, inheritance, carriers, gluing, calibration — or a tool a
  pillar uses.
- It says which kind of statement it is: identity, inherited polarization, integer invariant,
  estimate (and in which regime), equivalence with RH, or no-go with its positive survivor.
- Restatements of neighbouring programmes and numerical certificates do not count.

## 14. Big picture

The complete Weil family degenerates, and ADT has computed its limiting mixed structure. After
rescaling by the decay `c^β` of the pole conductor, the family converges to a positive diagonal form
in the conductor basis whose coefficients are Jordan totients over Euler's totient: an arithmetic
invariant, not a common floor. The dilation monoid acts on the graded pieces by lowering the
conductor, prime by prime, with commuting lowerings and the pole conductor as the unique fixed
point; along each tower the limiting polarization is a weight string, and over the primes it is a
tensor product. This is the arithmetic analogue of a nilpotent orbit with a cone of commuting
monodromies, and it is exact on the whole degenerating block of conductors below the threshold,
where the finite family inherits it with arbitrarily small loss. The monodromy is eventually
idempotent rather than quasi-unipotent, and in closed form it lowers a conductor `m` to `m/gcd(m,g)`;
through it the energies of the graded pieces and of the top coprime stratum determine each other by a
Möbius pair over the cone.

The structure is inherited exactly up to the RH exponent. There the extension data — the
cross-conductor residual channels, which live in the top coprime stratum — reach the size of the
margins, and their positivity at every constant multiple of the exponent is RH. The limit itself is
blind: it is computed from the profile and the integers. The sign of RH is the sign of the
second-order term of the degeneration at the critical curve, and the gluing that produces the
global arithmetic is a single rank-one coupling at the pole whose determinant is the Mertens
function.
