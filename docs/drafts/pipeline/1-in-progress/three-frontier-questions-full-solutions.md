# Joint edge payment, source orientation, and the heat count

- **ID:** three-frontier-questions
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-3010/obstacles-summary.md` §2.3
- **Statement:** Resolve Q1–Q3 and every listed subquestion by unconditional Lean theorems.

## Required conclusions

| Question | Required mathematical conclusion | Status |
|---|---|---|
| Q1 | All-vector logarithmic defect reserve for the complete Weil form; defect-relative conductor decomposition | Reserve formalized uniformly for `1≤c≤(log log N)^α`, every `0<α<1/16`; conductor/shell decomposition open |
| Q1/A1 | Top-band joint cancellation, then top-band perturbations of Ramanujan modes | Formalized: actual Ramanujan witness coefficient is at most `Kφ mφ(m)G(1+log N)`, uniformly for `N≥8`, `1≤c≤N/4`; exact quadratic expansion and all direct Lean/axiom audits passed. [Proof](../3-formalized/nonpolar-ramanujan-top-band-cancellation.md) |
| Q1/A2 | Growing Euler heads and joint head–pole–tail cancellation | Formalized: literal all-prime mixed source minus both polar terms is `o(√Y)` on detail–far-window witnesses, uniformly for bounded coefficients on fixed finite families |
| Q1/O1 | Ramanujan–Plancherel decomposition of the shell block | Full agreement-shell identity open. [Two-conductor top band](../3-formalized/two-conductor-top-band-polar-channel.md), [finite adjunction spectrum](../3-formalized/finite-divisor-jet-adjunction-spectrum.md), and [signed-source smoothed square completion](../3-formalized/autocorrelation-divisor-jet-square-completion.md) formalized |
| Q2 | Equality of the two actual Ξ source polarizations | Open; corpus theorem identifies this with RH |
| Q2/defect | Theta–prime expression for `(σ − 1/2)S(s) − Re(ξ′/ξ)(s)`, at some `σ > 1` | Formalized at `s=4`: `xiResolventDefect_four_eq_thetaPrime`; both theta limits and prime-series convergence proved, direct check and standard-axiom audit passed |
| Q2/charge | Theta-prefix reading of window collision charge with explicit error | Formalized: `finiteThetaCollisionReading_error` gives a canonical separation threshold; convergence and eventual exact integer rounding are proved |
| Q2/calibration | Integer analogue of the calibrated explicit-formula Rosati pairing | Formalized: `tsum_explicit_eq_xiWeilPolarization` and `norm_sq_sub_explicit_eq_half_reflectionDefect`; source and transitive standard-axiom audits passed |
| Q3 | Actual growth law for the de Bruijn–Newman nonreal count at zero | Open |
| Q3/flux | Consequence of summing the actual localized outer flux over heights | Open |
| Q3/tower | Arithmetic ceiling for a nonblind prime tower | Open |
| Q3/functional | Global monotone functional for the actual zero dynamics | Formalized: full squared-depth energy is continuous, nonincreasing and pays `2∫N` between positive times; zero energy iff all heat zeros are real |

The [profiled adjunction lag charge](../3-formalized/profiled-adjunction-lag-kernel.md)
is also positive on arbitrary real translates, including the exact logarithmic mesh.
Its comparison with the complete Weil kernel remains open.

## Proof discipline

Existing criteria, bounds and obstructions are inputs, not substitutes for these conclusions.
Every claimed solution requires the exact theorem, dependency audit and successful
`lake --old env lean` check. No unproved sign or analytic input may enter a premise.

## Mathematical inputs

- `riemannHypothesis_iff_xiResolvent_sourcePolarizations_eq`: exact orientation receiver.
- `exists_card_deep_le_mul_nonrealZeroCount`: transfers a heat-count law to deep-zero counts.
- The stronger `exists_card_deep_le_heat_count_at_uniform_depth_scale` gives
  `#F≤C log X·N(t)` when `t log X≤cδ²`, with a depth-independent height threshold.
  Its transitive audit and the persistence theorem's audit passed with only the
  standard three axioms. It supplies no upper bound on `N(t)`.
- The corpus's [inverse-logarithmic heat ladder](../3-formalized/the-heat-count-ladder-at-inverse-logarithmic-heat.md)
  transfers `N(t)≤exp(A t^{−α})` to subpower deep-zero density for every `α<1`;
  polynomial growth gives exponent `a+1`. The actual count bound is still missing.
- `exists_abs_jointWitnessCoefficient_le_uniform_overlap`: the pole and shells cancel on the
  top-band witness with bound `Kφ G(c + 1 + log N)`, uniformly for `1 ≤ c ≤ N/4`.
  Arbitrary coefficient vectors remain outside this theorem.
- `completedShellEnergy_div_conductor_le` and `log_conductor_sub_log_overlap_le_completedEnergy`
  prove `E_m(c) ≥ E_1(c/m) ≥ log(m/c) + min(0, completeWeilSelfFinitePart φ 1)`.
  Both are uniform scalar laws with direct Lean and standard-axiom audits; finite-horizon
  operator transfer remains separate.

## Formalized fixed-overlap reserve

Let `R_N = (log N)I − P_N`, with conductor eigenvalues
`λ_m = γ + log m + tameDifferent(m)`. The row bounds compare `R_N` with `D_N`
up to an absolute multiple of the mass. Starting from the proved reserve
`W_N ≥ β(c)D_N − B(c)I`, `β(c) ≍ c⁻⁷`, set `δ(c)=β(c)/2`.
Then `W_N − δ(c)R_N` still has a positive defect reserve. Its conductor
quasimode energies are `E_m(c) − δ(c)λ_m`.

Proved scalar input: `E_m(c) ≥ δ(c)(λ_m − C log(2c))`, uniformly in `m,c≥1`.
For polynomially bounded `m`, use `E_m(c)≥0` and `tameDifferent(m)≤log m`.
For larger `m`, bound the finite shell correction using the divisor formula
for Ramanujan sums and a polynomial lower bound for the totient.
Finite Ramanujan approximation plus norm quasimodes transfers this floor to
the shifted matrices. `exists_completeWeil_logarithmic_defect_reserve` proves
`∃a,C>0, ∀c≥1, eventually N, ∀x`; direct Lean check and standard-axiom audit
passed. Proof: `../3-formalized/logarithmic-reserve-by-shifting-the-prime-energy.md`.

## Prescribed growing-overlap reserve

The separate common-horizon argument now proves absolute `a,C>0` such that,
for every `0<α<1/16`, eventually all `1≤c≤(log log N)^α` and all vectors satisfy
`W_N(c,x)≥a c⁻⁷[D_N(x)−C log(2c)‖x‖²]`.
The complete matrix itself is positive definite throughout the same range.

The uniform conductor residual is
`‖W_N(c)u_m−E_m(c)u_m‖²≤K m⁴[c⁵/log N+c¹⁰(log N/N)²+c³/√log N]`
for every logarithmic conductor range. Exponential confinement gives a
subpower-of-`log N` cutoff when `16α<1`; its summed residual is smaller than
the common conductor floor. The same argument applies after shifting prime
energy and adding the scalar logarithmic correction.

[Positivity](../3-formalized/complete-weil-positivity-at-growing-iterated-log-overlap.md)
and [logarithmic reserve](../3-formalized/logarithmic-defect-reserve-at-iterated-logarithmic-overlap.md)
passed all direct Lean and standard-axiom audits; umbrella imports are present.
The agreement-shell identity and RH-complete overlap remain open.

## Exact harmonic and prime components

For `u_m=c_m/√φ(m)`, the harmonic Gram finite part is exactly
`B_ml=γ·1_(m=l)−I(m,l)/√(φ(m)φ(l))`, where `I` is the torsion intersection.
On every coefficient vector supported in `1≤m≤Q`, `Q≥2`,
`|∑_(n≤N)(∑_m a_m u_m(n))²/n−H_N∑_m a_m²+T_Q(a)|`
`≤Q(Q−1)/(N+1)∑_m a_m²`.
Here `T_Q(a)=∑_(m,l≤Q)a_m a_l I(m,l)/√(φ(m)φ(l))`.

The [exact finite part](../3-formalized/ramanujan-harmonic-gram-finite-parts-are-prime-local.md)
and [uniform remainder](../3-formalized/harmonic-ramanujan-gram-has-a-logarithmic-operator-bound.md)
passed all direct Lean and standard-axiom audits.

For `v_m,N=u_m/√(n log N)`, the literal full prime matrix also has the exact
finite part `⟨v_m,N,P_N v_l,N⟩−1_(m=l)log N`
`→−I(m,l)/√(φ(m)φ(l))−1_(m=l)[log m+tameDifferent(m)]`.
Its diagonal is `−2log m`; finite polarization gives every fixed packet's
quadratic limit. [Proof and final Lean audit](../3-formalized/prime-conductor-finite-parts-retain-the-torsion-boundary.md).
The centered fixed-prime head instead tends to
`+I(m,l)/√(φ(m)φ(l))−1_(m=l)[log m+tameDifferent(m)]`;
its complementary boundary tends to `−2I(m,l)/√(φ(m)φ(l))`.
The exact head/full-matrix identity and both ordered limits passed final
Lean and standard-axiom audits. [Proof](../3-formalized/prime-conductor-heads-and-tails-have-opposite-torsion-limits.md).
At cutoff `floor(N^theta)`, `0<theta≤1`, the exact leading term is
`theta(2−theta)delta_ml log N`; the finite part is
`(1−2theta)I/√(φ(m)φ(l))−delta_ml[log m+tau(m)+2(1−theta)gamma]`.
The square-root head is diagonal. Scalar-identity centering retains
`(1−theta²)B_ml`, and bands between powers carry `2(beta−alpha)B_ml`.
[Exact formulas and final Lean audit](../3-formalized/square-root-prime-heads-diagonalize-conductor-finite-parts.md).
The complete Gamma, pole, and successor-shell identity remains open.

The [affine period identity](../3-formalized/affine-shell-correlations-select-conductor-quotients.md)
is exact: `∑_(n<M)c_m(n)c_l(kn+h)=1_(m=l/gcd(l,k)) M c_l(h)` for positive
conductors dividing `M`. Its finite-packet expansion retains every mixed entry.
The logarithmic horizon boundary is separate.

## Full-divisor resolvent identity

At `Re s>1`, positivity of `Re(s−ρ)⁻¹` gives absolute convergence of
`S(s)=Σ|s−ρ|⁻²`. The signed depth sum is
`(Re s−1/2)S(s)−Re ξ′/ξ(s)`. Reindexing by `ρ↦1−conj ρ` and using
`pair_depth_resolvent` identifies it with
`Σ 2(Re s−1/2)(Re ρ−1/2)²/(|s−ρ|²|s−ρ*|²)`.
Formalized in `HilbertianExplicitFormulas/TheXiResolventDepthIdentity.lean` as
`sub_mul_xiSamePointResolvent_sub_logDeriv`. Its prime expansion is
`xiResolventDepth_eq_samePoint_sub_arch_add_prime`. Direct Lean check passed;
both transitive axiom sets are exactly `propext`, `Classical.choice`, `Quot.sound`.
`TheResolventDepthHasAThetaPrimeExpression` identifies `S(4)` with two limits of
finite integer theta-prefix readings of `χ_R(z)/(|4−z|²+χ_0(z−4))`.
Both limits exist. The source definition contains no zero locations.

## Gates

Q3's functional is proved in
`../3-formalized/the-global-heat-depth-energy-dissipates.md`.
It gives `E(b)+2∫_a^b N≤E(a)` for `0<a≤b`, through all collisions.
No finite initial energy or growth bound as `t↓0` has been proved.

- [x] Full requested conclusions fixed.
- [ ] Dependency-closed paper proofs of every conclusion.
- [ ] Exact Lean formalizations, umbrella imports and axiom audits.
