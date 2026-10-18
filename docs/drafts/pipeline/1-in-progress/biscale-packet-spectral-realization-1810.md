# Spectral realization of signed lattice correlations with grid and polar constraints

- **ID:** biscale-packet-spectral-realization-1810
- **Stage:** 1-in-progress
- **Type:** BRIDGE; classical factorization plus existing source energy mechanisms
- **Parent:** [field programme](biscale-field-development-1810.md), items 8 and 11

## Exact target and scope

Fix `S=8 log(3/2)>2`, `q=exp(S/2)=81/16`, and a real nonzero smooth seed `ψ` whose autocorrelation is supported in `[-ρ,ρ]`, with `ρ<S/2`. Write `kψ(x)=autocorr(ψ,x)/autocorr(ψ,0)`. For a finite real symmetric sequence `H_(−j)=H_j`, supported in `[-D,D]`, with `H_0=1`, prescribe the **whole correlation profile**

`h_H(x)=Σ_(j=−D)^D H_j kψ(x−jS)`.

This distinction matters: prescribing only the samples `h(jS)` does not determine polar balance between samples. Define the Laurent polynomial `H(z)=Σ_j H_j z^j`.

Proposed exact classification: this profile is the normalized autocorrelation of a real smooth compact source if and only if `H(e^(it))≥0` for every real `t`. If both exponential moments of the seed are nonzero, imposing zero polar moment is equivalent to the additional condition `H(q)=0`. Nonnegative seeds provide that nonvanishing condition from an actual construction.

The source can be chosen as one finite train `f=Σ_(j=0)^D c_j ψ(·−jS)`. This is an actual source, not a spectral mixture. Source normalization is obtained by dividing by its positive `L²` norm.

## Proof mechanism and outstanding checks

Necessity of nonnegativity follows from positive definiteness of the sampled autocorrelation sequence: its finite Fourier polynomial is nonnegative. A direct route is to apply positive definiteness to long modulated finite vectors and divide by their length, obtaining the Fejér-weighted sums and their finite limit. This avoids assuming that one finite Toeplitz matrix certifies all extensions.

For sufficiency, the real form of Fejér–Riesz gives `H(z)=C(z)C(z⁻¹)`, with real polynomial `C` of degree at most `D`. Real coefficients follow by choosing conjugation-invariant reciprocal root pairs; roots on the unit circle have even multiplicity. Expanding the train autocorrelation gives the prescribed profile. Its diagonal mass is `H_0 autocorr(ψ,0)` because the translated seed correlations are disjoint at the lattice centers.

The two source exponential moments are multiplied by `C(q)` and `C(q⁻¹)`. Their product is multiplied by `H(q)`, so polar balance has the stated criterion. This also follows from the prescribed whole profile, and is therefore necessary for any source realizing that profile.

Fejér–Riesz is classical; see [Dritschel–Rovnyak, introductory theorem and root proof](https://uva.theopenscholar.com/files/james-rovnyak/files/p71.pdf). The real-coefficient argument and the sampled-positive-definiteness necessity must be proved in the exact conventions used here. No formal factorization theorem has yet been verified in this toolchain.

## Grid constraints and quantitative cost

Every positive lattice center is `jS=log((3/2)^(8j))`, never the logarithm of an integer: the reduced denominator is `2^(8j)`. Rational separation gives an explicit positive lower bound of order `3^(−8D)` on the distance of every center with `1≤j≤D` from the logarithmic grid. Choose `ρ` below one quarter of that bound and below `1/2`. The zero-center lobe also misses every `log n`, `n≥2`; negative centers cause no positive-grid intersections. Thus the complete profile vanishes on the entire logarithmic grid, while retaining every prescribed nonzero `H_j` at the off-grid center `jS`.

The existing small-support seed theorem gives energy at most `C−log ρ`. Existing local-correlation stability transfers this bound to every separated train with a fixed tail constant, independent of its coefficients and packet count. The resulting upper cost is `C₁+C₂D`. The actual source support can be bounded by `DS` plus the seed diameter, provided the chosen seed construction tracks source support as well as correlation support.

When `H_D≠0`, both endpoint coefficients of a degree-`D` factor are nonzero. Existing full-span grid rigidity gives a lower energy cost proportional to `DS`, hence to `D`. This lower bound is to be imported, not reproved. Its `S>2` separation assumptions are why this card uses `8 log(3/2)` instead of the smaller `log(3/2)` suggested initially.

Required exact arithmetic detail: for each grid integer, bound the logarithmic distance from `log(3^(8j)/2^(8j))` using its nonzero rational numerator; split off integers outside a fixed multiplicative neighborhood before applying the mean-value estimate. The claimed order is a target bound, not an already audited constant.

## Nonempty signed class and boundaries

`C(z)=1−q⁻¹z` gives, after diagonal normalization, `H_1=−1/(q+q⁻¹)`, a nonzero negative off-grid correlation, and `H(q)=0`. Multiplying this factor by arbitrary real polynomials produces higher-degree balanced profiles.

An isolated PSD finite Gram matrix is insufficient: the target requires positivity of the entire zero-extended sequence. Even that positivity alone does not imply polar balance. Conversely, the criterion concerns this entire prescribed packet profile; it must not be presented as a criterion for arbitrary finitely sampled data.

## Corpus and verification gates

Existing source inspected: `FiniteIntegerTrainPackets` (source, lag coefficients and exact grouped correlation), `FiniteIntegerTrainPolar` (exponential symbols and polar multiplier), `FiniteTrainUniformEnergy` (minimum active grid distance, construction and matching energy bounds), `FiniteCopyTailRigidity` (full-span lower cost), and `LocalCorrelationEnergyStability` (local agreement and logarithmic seed cost). Reuse these mechanisms.

The hybrid corpus query `integer packet train Fejer Riesz Laurent polynomial polar signed correlation realization` returned the polar-symbol identities and related source constructions. Its snapshot inventory was complete, but compiled metadata were mostly pending or stale; it does not establish absence of a factorization theorem. The separate factorization query returned partial results, including `QuantumAlg/Util/Polynomial/Complement/Laurent/Witness.lean`. That file has reciprocal-conjugate root selection, unit-circle even-multiplicity arguments and residual-polynomial factor certificates. The inspected endpoints concern bounded complements or require a factor certificate; a general real Fejér–Riesz theorem applicable to this profile has not yet been verified. Reuse that root machinery where applicable.

- [ ] Complete exact arithmetic distance and support bounds.
- [ ] Prove the finite-sequence positivity criterion and real factorization in the current Lean corpus.
- [ ] Instantiate an actual nonnegative smooth seed with all required quantitative bounds.
- [ ] Prove the unconditional classification, including zero/degree boundary cases.
- [ ] Derive exact polar equivalence and two-sided cost for the actual normalized sources.
- [ ] Direct source/axiom audits, wiring, index and lint.

This card is a candidate extension, not a completed item 8 and not evidence of an independent mathematical field.
