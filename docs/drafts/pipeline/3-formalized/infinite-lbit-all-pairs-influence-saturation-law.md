# Infinite l-bit all-pairs influence saturation law

- **ID:** `infinite-lbit-all-pairs-influence-saturation-law`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Labels:** `[LEAN-PROVED] [NOVELTY UNVERIFIED]`
- **Source:** Anderson-dynamical-localization hostile comparison

## Exact claim

For the explicit countable quasi-local l-bit coefficient field, let
\(\tau_t(X_x)\) be the Heisenberg-evolved flip at \(x\). For every distinct
pair \(x\ne y\),
\[
 \sup_{t\in\mathbb R}
 \|[\tau_t(X_x),X_y]\|_{\mathrm{op}}=2
\]
on continuous amplitudes with the uniform norm.

Together with the already formalized fixed-time estimate
\[
 \|[\tau_t(X_x),X_y]\|_{\mathrm{op}}
 \le
 \min\{2,4K|t|2^{-|x-y|}\},
\]
this gives the exact order-of-quantifiers separation
\[
 \forall t:\quad
 \lim_{|x-y|\to\infty}\|[\tau_t(X_x),X_y]\|_{\mathrm{op}}=0,
 \qquad
 \forall x\ne y:\quad
 \sup_t\|[\tau_t(X_x),X_y]\|_{\mathrm{op}}=2.
\]
At the explicit saturation witness \(t_{xy}>0\), the same locality estimate
also gives the division-free delay law
\[
 2\le 4K t_{xy}2^{-|x-y|}.
\]

The theorem does not assert Anderson dynamical localization. It proves
that the explicit interacting l-bit field fails every nontrivial
time-uniform decaying commutator bound.

## Paper proof

Every coefficient \(J_S\) on a nonempty support is strictly positive: its
rational scale is positive and its prime-log factor is positive.

Fix \(x\ne y\) and let \(\mathbf 0\) be the all-false configuration. A
double flip cancels every interaction not containing both sites. For a
support \(S\) containing \(x,y\), its Walsh character is \(+1\) at
\(\mathbf 0\), remains \(+1\) after both flips, and is \(-1\) after either
single flip. Therefore
\[
 D_{xy}:=
 E(\mathbf 0^{xy})-E(\mathbf 0^x)-E(\mathbf 0^y)+E(\mathbf 0)
 =
 4\sum_{S\ni x,y}J_S.
\]
Absolute summability justifies termwise subtraction. The sum is strictly
positive because it contains \(S=\{x,y\}\), whose coefficient is positive.

The exact commutator formula at \(\mathbf 0\) is a unit phase times the
difference of two phases whose relative angle is \(tD_{xy}\). Choose
\[
 t_{xy}=\frac{\pi}{D_{xy}}.
\]
For the constant unit amplitude, the commutator value at \(\mathbf 0\) has
modulus \(2\). Hence the operator norm is at least \(2\). The triangle
inequality for the two unit phases gives the universal upper bound \(2\),
so equality holds at \(t_{xy}\), and consequently the all-time supremum is
exactly \(2\). Substituting this equality, the unit amplitude and
\(t_{xy}>0\) into the fixed-time commutator bound gives
\[
 2\le 4K t_{xy}2^{-|x-y|}.
\]

## External frontier

- Kim--Chandran--Abanin prove the established logarithmic-light-cone upper
  scaling for localized integrals of motion.
- Chen--Zhou--Huse--Fradkin derive the exact l-bit OTO phase and its
  logarithmic crossover.
- Hamza--Sims--Stolz prove time-uniform exponentially decaying
  commutators in an Anderson-localized disordered XY chain.

Thus the qualitative eventual-propagation mechanism is literature-known.
Potential novelty is restricted to exact all-pairs operator-norm
saturation for one infinite quasi-local field and its conjunction with
maximal finite-environment rational rank.

## Hostile verdict

`[BRIDGE]` pending exact priority confirmation. The theorem is sharper than
the current upper bound and closes the Anderson comparison, but it does
not alone establish new physics: known l-bit OTO formulas already predict
eventual interaction-mediated influence.

The positive insight is exact:

> Fixed-time exponential locality and time-uniform Anderson locality are
> inequivalent. In the explicit interacting field, every distance is
> exponentially delayed but none is permanently isolated.

## Formalization

Implemented in
`formal/GaloisForLFunctions/HTGeometry/InfiniteLBitAllPairsInfluenceSaturationLaw.lean`.
Capstones:

- `quasiLocalInfiniteLBitCoefficient_pos`;
- `infiniteLBitEnergyDoubleFlip_allFalse_eq`;
- `infiniteLBitEnergyDoubleFlip_allFalse_pos`;
- `quasiLocalInfiniteLBitPairSaturationTime`;
- `norm_quasiLocalInfiniteLBitFlipCommutator_pairSaturationTime`;
- `two_le_pairSaturationTime_mul_weightedInfluenceRate`;
- `exists_quasiLocalInfiniteLBit_allPairsInfluenceSaturation`.

The direct module check passed with `lake env lean`. The axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound`.

## Promotion gates

- [x] exact claim
- [x] dependency-closed paper proof
- [x] primary-literature parent-theory audit
- [x] exact Lean formalization
- [x] axiom audit
- [ ] independent expert priority review
