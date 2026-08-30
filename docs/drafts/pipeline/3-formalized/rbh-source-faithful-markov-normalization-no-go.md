# RBH source-faithful Markov normalization no-go

- **ID:** RBH-FAITHFUL-MARKOV-NORMALIZATION
- **Stage:** 3-formalized
- **Type:** NO-GO THEOREM / COMPLETE CLASSIFICATION
- **Source:** `rh-current-frontier-map.md` RBH source-first balance producer core
- **Statement:** Every source-faithful reflection-natural normalization preserves the fixed locus of the literal two-channel RBH source, while every reflection-symmetric two-state Markov generator is a single-rate exchange generator whose finite-time heat flow preserves nonzero channel imbalance and whose infinite-time balance erases it for every input.

## Goal
Kill normalization and Markov heat equilibration as independent producers of RBH balance. Full
attempted RH chain:

`literal reflected bi-heat source -> reflection-natural normalization or Markov heat equilibration -> multiplicity-leading channel balance -> shared information Ward charge zero -> every Xi divisor lies on critical wall -> RH`.

Success significantly reduces proof burden: a surviving RBH proof must derive raw channel balance
from an additional source law. Neither faithful normalization nor finite-time heat evolution can
create it, and infinite-time equilibration is nonselective.

## Gates
- [x] 0 -> 1 in-progress: corpus-led hard producer, exact RH chain, attack plan, provisional novelty boundary
- [x] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 -> 3 formalized: Lean capstone, targeted `lake build`, axiom audit
- [ ] 3 -> 4 publication-ready: standalone paper and external expert novelty audit

## Corpus basis
- `ReflectedBiHeatMultiplicityLeadingJetBalance` identifies actual leading-jet norm balance exactly with `Re rho = 1/2`, globally exactly with RH.
- `ReflectedBiHeatSourceNormalizationClassification` covers only fixed linear reporters and common scalar normalization.
- `ReflectedBiHeatPositiveMatrixApertureClassification` covers all finite entrywise-positive quadratic aperture mixtures.
- `ReflectedBiHeatFiniteCommensurateChebyshevClassification` covers arbitrary finite commensurate signed aperture packets.
- `ReflectedBiHeatFZZDeningerInformationWardTransmutation` identifies RBH imbalance with the shared FZZ-P/PW-B/Deninger Ward charge by strictly positive factors.
- Mandatory corpus search found no arbitrary nonlinear source-faithful normalization theorem and no finite-time versus infinite-time RBH Markov-flow classification.

## Frozen conjecture and proof chain
1. For reflections `S` and `T`, an injective equivariant map `N`, satisfying `N(Sx)=T(Nx)`, reflects fixed points: `T(Nx)=Nx` iff `Sx=x`. If an off-fixed source is sent to a fixed output, `N(Sx)=N(x)` and `N` is not injective.
2. Every real two-channel linear generator commuting with channel swap, conserving total mass infinitesimally, and having nonnegative off-diagonal rates is uniquely
   `L_r(u,v)=(r(v-u), r(u-v))` for one `r >= 0`.
3. Its flow is
   `P_t(u,v)=((u+v+exp(-2rt)(u-v))/2, (u+v-exp(-2rt)(u-v))/2)`.
   It preserves mass, commutes with reflection, is positive for `r,t >= 0`, obeys the semigroup law, and is injective at every finite time.
4. Exact transverse law:
   `(P_t(u,v)).1-(P_t(u,v)).2=exp(-2rt)(u-v)`.
   Since the multiplier is strictly positive, finite-time balance occurs iff `u=v`. For `r>0`, this difference tends to zero for every input as `t -> +infinity`.
5. Apply to the actual multiplicity-leading RBH norm pair. At every finite time, normalized balance is equivalent to `Re rho=1/2`; universal balance is equivalent to RH. At infinite time every pair balances whether RH is true or false, so limiting balance cannot select Xi support.

## Hostile attacks
1. **Nonlinear normalization:** theorem is set-theoretic; no linearity, continuity, norm, or finite-dimensional target is assumed.
2. **Channel-dependent normalization:** allowed whenever it is reflection-equivariant and source-faithful; off-wall output balance forces a source-orbit collision.
3. **Finite-time heat miracle:** exact positive exponential multiplier forbids it.
4. **Infinite-time equilibrium as selector:** limit is balanced for every source pair, hence carries no wall information.
5. **Signed/negative mixing:** excluded only from Markov branch; arbitrary faithful equivariant maps remain covered by fixed-locus theorem.
6. **Overclaim:** result kills normalization-only and reflection-symmetric Markov-equilibration RBH producers. A genuinely additional source law directly forcing raw Ward charge zero remains possible, but is no longer supplied by RBH heat dynamics.

## Provisional literature audit
General two-state continuous-time Markov-chain formulas and finite Markov entropy gradient flows are
classical. Search through August 2026 found no work applying the faithful fixed-locus dichotomy or
the finite-time/infinite-time Markov selectivity theorem to the literal multiplicity-leading
reflected bi-heat Xi channels. Novelty claim is restricted to this exact RBH synthesis and route
closure, not the parent two-state semigroup algebra.

## Paper proof
`[PROVED HERE]`.  Equivariance gives `N(Sx)=T(Nx)`.  If `T(Nx)=N(x)` and `N` is
injective, then `N(Sx)=N(x)` implies `Sx=x`; converse follows directly from equivariance.  If
`Sx != x`, fixed output instead witnesses noninjectivity.

Write a general real two-channel generator as
`L(u,v)=(Au+Bv,Cu+Dv)`.  Commutation with channel swap, tested at `(1,0)`, gives
`A=D` and `B=C`.  Infinitesimal conservation of total mass, tested at `(1,0)` and `(0,1)`,
gives `A+C=0` and `B+D=0`.  Nonnegative off-diagonal rates therefore leave exactly
`A=D=-r`, `B=C=r`, `r>=0`.

In mean/difference coordinates its flow is
`P_t(u,v)=((u+v+q_t(u-v))/2,(u+v-q_t(u-v))/2)` with `q_t=exp(-2rt)`.
The exponential addition law proves `P_(s+t)=P_s P_t`; differentiation gives
`P'_t=L_r P_t`; and `0<q_t<=1` at nonnegative rate/time proves positivity.  Total mass is
fixed and difference is exactly `q_t(u-v)`.  Since `q_t` is nonzero at every finite time,
`P_t` is injective and balanced exactly when `u=v`.  If `r>0`, exponential decay gives
`q_t(u-v)->0` for every input.

For actual multiplicity-leading RBH norms, existing dependency-closed theorem
`reflectedBiHeatMultiplicityLeadingJetNorms_two_eq_iff` identifies `u=v` exactly with
`Re rho=1/2`, and its universal quantification exactly with RH.  This proves every claimed route
consequence without an unproved premise.

## No-go closure
- **Exact killing theorem/mechanism:** `[ROUTE-CLASS KILL][PROVED HERE][LEAN-PROVED]`. Every arbitrary nonlinear source-faithful reflection-natural normalization preserves the exact fixed locus. Every reflection-symmetric conservative two-channel Markov generator has one exchange rate, and its finite-time flow multiplies raw RBH imbalance by a strictly positive exponential. Neither mechanism can create balance off wall.
- **Strongest positive survivor:** Complete physical dichotomy. Finite time preserves all reflection-odd source information and remains an exact RH receiver. Positive-rate infinite time erases the odd channel for every input and is therefore universally balanced but nonselective. An off-wall fixed normalized output is an exact certificate that the normalization collapsed the free reflected source orbit.
- **New insight:** RBH heat relaxation cannot supply its own missing Ward law. Faithful dynamics retain the Ward charge at every finite time; equilibrium destroys precisely that charge independently of Xi support. Any surviving RBH chain must add a genuinely source-first raw balance law rather than derive it from normalization or equilibration.
- **Status:** Dependency-closed paper proof and Lean formalization complete. Novelty is route-specific and bounded: parent two-state CTMC algebra is classical; corpus and literature audits found no faithful-normalization/finite-time/infinite-time classification for actual multiplicity-leading RBH Xi channels.
- **Lean theorem:** `RHTower.reflectedBiHeat_sourceFaithfulMarkovNormalization_noGo` in `ReflectedBiHeatSourceFaithfulMarkovNormalizationNoGo.lean`. Direct `lake env lean` passed. Targeted build and axiom/lint audits recorded below.

## Audit
- Direct `lake env lean GaloisForLFunctions/RHTower/ReflectedBiHeatSourceFaithfulMarkovNormalizationNoGo.lean`: PASS, no diagnostics.
- Targeted `lake build GaloisForLFunctions.RHTower.ReflectedBiHeatSourceFaithfulMarkovNormalizationNoGo`: PASS.
- `#print axioms RHTower.reflectedBiHeat_sourceFaithfulMarkovNormalization_noGo`: only `propext`, `Classical.choice`, and `Quot.sound`.
- Umbrella import wired in `GaloisForLFunctions.RHTower`; no umbrella/full build run.
- Global `scripts/formal_tools.py lint` remains red only on unrelated pre-existing theorem-area umbrella reachability debt; new module is reachable and produced no lint failure.

## Log
- 2026-08-30 — frozen after fixed-linear, positive-matrix, and finite signed-packet conjectures were rejected by mandatory corpus audit as already classified.
- 2026-08-30 — conjecture proved dependency-closed on paper and formalized in Lean; moved to stage 3.
