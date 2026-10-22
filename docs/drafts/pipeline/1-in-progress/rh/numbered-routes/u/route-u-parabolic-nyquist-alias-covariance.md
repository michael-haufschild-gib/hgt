# Route U parabolic Nyquist alias covariance

- **ID:** U-PARABOLIC-NYQUIST
- **Stage:** 1-in-progress
- **Type:** FALSIFIED
- **Source:** `route-u-dyadic-cayley-source-multiresolution.md` · `(U-DYC-global)`
- **Statement:** Fixed-node dyadic coherence does not exchange with the Xi divisor: the quadratic
  shell `|gamma| = u (k+1)^2` folds the fine phase onto the coarse Nyquist wall and produces an
  anti-coherent `(1,-1)` even/odd mode with logarithmic zero-density mass.

## Goal

Hostile-test the proposed global even/odd divisor exchange rather than promoting pointwise
convergence without a uniform majorant.  Extract the exact moving-scale chart and determine what a
renormalized Route U source observable must cancel before any positivity argument can start.

## Gates

- [x] 0 → 1 in-progress: exact falsifier, source-native definitions, hostile proof, positive survivor
- [ ] 1 → 2 fully-proven: finish the full normalized covariance constant and tail-tightness proof
- [ ] 2 → 3 formalized: formalize the Riemann--von Mangoldt scaled divisor measure and covariance
- [ ] 3 → 4 publication-ready: standalone theorem, proof, novelty audit, Lean certificate

## Frozen claims

Write `a=k+1`, coarse alias period `L_a=pi a`, fine mass `2a`, and

```text
phi_2a(alpha) = 2a arctan(alpha/(2a)).
```

For a nonzero real-even compact smooth carrier `g`, let `F` be its positive Fourier extension.  The
fine lattice sample splits as `S_a=E_a+O_a`, where exact even reindexing gives

```text
E_a(alpha) = (1/2) P_a(phi_2a(alpha))
```

and `P_a` is coarse-periodic with period `pi a`.

### U-PN-PHASE — proved on paper and in Lean

For every `u>0`, on the real quadratic shell `alpha=u a^2`,

```text
phi_2a(u a^2) - pi a
  = -2a arctan(2/(u a))
  --> -4/u.
```

The corresponding real hard-edge resolvent profile satisfies

```text
a^2 * (2a)^2 / ((2a)^2 + (u a^2)^2)
  = 4 / (4/a^2 + u^2)
  --> 4/u^2.
```

Lean module:
`formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgeParabolicNyquistAlias.lean`.
Public statements are premise-free by taking `u` in the positive-real subtype:

- `routeUDyadicParabolicFoldedPhase_eq`
- `tendsto_routeUDyadicParabolicFoldedPhase`
- `tendsto_routeUDyadicParabolicComplexFoldedPhase`
- `routeUDyadicParabolicScaledResolventWeight_eq`
- `tendsto_routeUDyadicParabolicScaledResolventWeight`

All pass `lake env lean`; exact module `.olean` is built.  Axiom audit is
`[propext, Classical.choice, Quot.sound]`.

### U-DYC-global — falsified on paper

Choose a compact interval `I` of positive `u` on which `F(-4/u)` is bounded away from zero.  Such
an interval exists because `F` is continuous, real-even, and not identically zero.  Uniformly for
Xi zeros with `gamma/a^2 in I` and strip displacement `|eta|<1/2`:

```text
phi_2a(gamma+i eta) - pi a = -4/u + o(1),
E_a(gamma+i eta) = F(-4/u)/2 + o(1),
S_a(gamma+i eta) = o(a^-N) for every fixed N,
O_a(gamma+i eta) = -E_a(gamma+i eta) + o(1),
w_2a(gamma+i eta) = 4/(u^2 a^2) + o(a^-2).
```

Riemann--von Mangoldt gives `asymp a^2 log a` multiplicity-counted zeros in that shell.  Hence the
real part of the even square channel alone grows by `c_I log a` for some `c_I>0`; it cannot converge
to the finite value predicted by `(U-DYC-global)`.  The odd square has the same sign, while the
even/odd cross channel has the opposite sign.  The pointwise theorem `(U-DYC-point)` remains true;
failure is exactly nonuniform exchange across the moving divisor shell.

### U-PN-COVARIANCE — strongest current conjecture

The hostile calculation predicts the exact normalized matrix law

```text
(1/log a) sum_q w_2a(q)
  [[E_a(q)^2, E_a(q) O_a(q)],
   [E_a(q) O_a(q), O_a(q)^2]]

--> C_g [[1,-1],[-1,1]],

C_g = (1/(4 pi)) integral_R F(x)^2 dx > 0.          (U-PN-COVARIANCE)
```

The constant follows from the multiplicity-exact scaled density

```text
(1/(a^2 log a)) sum_{gamma>0} delta_(gamma/a^2) --> (1/pi) du,
```

the limits above, negative-ordinate doubling, and `x=-4/u`.  This claim survives preliminary
attack but remains open until the low-`u` and high-`u` tails are written as a dependency-closed
uniform-integrability proof.

## No-go closure

- **Exact killing mechanism:** pointwise convergence holds only in the infrared chart
  `gamma=O(1)`.  The divisor contains a quadratic ultraviolet chart `gamma=Theta(a^2)` with
  `Theta(a^2 log a)` zeros.  There the fine phase is at its Nyquist boundary and parity changes from
  coherent `(1,1)` to anti-coherent `(1,-1)`.
- **Strongest positive survivor:** exact premise-free phase fold `-4/u`, exact scaled resolvent
  `4/u^2`, and conjectural universal anti-diagonal covariance constant `C_g`.
- **New insight:** individual polyphase channels are not trace-class.  Only coherent recombination
  cancels their ultraviolet logarithm.  Any viable Route U positivity observable must subtract or
  annihilate the anti-diagonal Nyquist mode before taking the full divisor trace.
- **Status:** scalar chart is paper- and Lean-proved.  Local shell falsifier is paper-proved from
  classical Riemann--von Mangoldt plus existing arbitrary-power Paley--Wiener alias decay.  Full
  covariance constant and its Xi-divisor Lean proof remain open.

## Universal reinterpretation

Repeated Route U failures are shadows of one renormalization law.  Fixed-divisor limits see only
the central phase and suggest finite signed trace duplication.  Global zero density forces a second
chart at spectral height `mass^2`; dyadic downsampling folds that chart through the Nyquist wall and
creates an anti-diagonal logarithmic counterterm.  Scalar positivity, raw `2 x 2` positivity, and
dominated exchange all fail when this counterterm is ignored.  Prime--Gamma source data can matter
only in the finite part left after this universal ultraviolet cancellation.

## Open Lean core

1. Extend the folded-phase limit uniformly to `gamma/a^2` in a compact positive interval and
   `|eta|<=1/2`.
2. Prove moving-window coarse periodization convergence and fine-Nyquist arbitrary-power decay.
3. Build a multiplicity-exact Riemann--von Mangoldt theorem for `XiZeroCopy`; no such theorem is
   currently exposed by the corpus.
4. Prove low/high shell tightness and the normalized covariance limit.
5. Reinsert the completed prime--Gamma source only after subtracting the universal anti-diagonal
   counterterm; test whether the finite part gains a sign or reproduces the original signed trace.

## Literature audit

- Butzer--Ferreira--Higgins--Schmeisser--Stens, *The sampling theorem, Poisson's summation formula,
  general Parseval formula, reproducing kernel formula and the Paley--Wiener theorem for bandlimited
  signals -- their interconnections*, Applicable Analysis 90 (2011),
  <https://doi.org/10.1080/00036811003627567>.  Supplies classical Poisson/sampling equivalences and
  alias formulas, not the Xi quadratic-shell covariance.
- Beaty--Higgins, *Aliasing and Poisson Summation in the Sampling Theory of Paley--Wiener Spaces*,
  JFAA 1 (1995), <http://eudml.org/doc/59449>.  Classical aliasing context; no zeta-divisor result.
- Hasanalizade--Shen--Wong, *Counting zeros of the Riemann zeta function*,
  <https://arxiv.org/abs/2107.06506>.  Gives an explicit Riemann--von Mangoldt error strong enough
  for the shell count.

No audited source was found for the combined zeta-zero, dyadic-polyphase, quadratic-shell
anti-diagonal covariance.  `[NOVELTY UNVERIFIED]` remains mandatory pending broader expert search.

## Log

- 2026-08-14 — Hostile test of `(U-DYC-global)` discovered quadratic Nyquist shell and
  infrared/ultraviolet parity flip.
- 2026-08-14 — Proved exact folded-phase and scaled-resolvent laws in Lean; compiled missing exact
  dependency `.olean`s serially, compiled exact new module `.olean`, audited axioms, and wired
  umbrella without building umbrella or project.

## 2026-08-14 ultraviolet parity closure

`U-PN-LOCAL-PARITY` is now premise-free and Lean-proved for every positive shell coordinate `u`,
compact approximation `n`, and Schwartz profile `f`:

```text
even_a(u) -->  (1/2) F_n(-4/u),
full_a(u) -->  0,
odd_a(u)  --> -(1/2) F_n(-4/u),
(even_a(u), odd_a(u)) --> (F_n(-4/u)/2, -F_n(-4/u)/2).
```

Paper proof: exact coarse-alias periodicity folds the fine quadratic-shell phase to `-4/u`; complex
HEPW continuity and uniform alias-tail decay give the even limit.  In the fine chart the unfolded
phase tends to positive infinity, uniform Paley--Wiener decay kills the central extension, and the
fine alias tail vanishes quadratically.  Exact recombination `odd = full - even` forces the negative
half-profile.  No zero-counting theorem enters this local law.

Lean module:
`formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgeParabolicNyquistParity.lean`.
Closed declarations:

- `routeUComplexHardEdgePeriodizationAt_sub_aliasPeriod`
- `tendsto_routeUDyadicParabolicEvenSample`
- `tendsto_routeUDyadicParabolicFullSample_zero`
- `tendsto_routeUDyadicParabolicOddSample`
- `tendsto_routeUDyadicParabolicParityPair`

Axiom audit for all four limit theorems: `[propext, Classical.choice, Quot.sound]`.  Exact module
`.olean` compiled at Lake's module path and umbrella import wired; umbrella was not built.

This closes prior open-core item 2 on each fixed positive real parabolic shell.  Remaining hard core
is genuinely global: compact-`u`/strip-uniform strengthening, multiplicity-exact Xi
Riemann--von Mangoldt, tail tightness, and normalized covariance.  Local ultraviolet parity is no
longer conjectural: Route U's shell mode is rigorously `(1,-1)`, so any unrenormalized positive
polyphase trace is structurally aimed at the wrong parity sector.

## 2026-08-14 null-form pivot

The proposed normalized anti-diagonal covariance may still be a true descriptive asymptotic, but
it cannot be Route U's closing positive producer.  The formally proved two-channel classification
in `route-u-nyquist-null-form-rigidity.md` shows that every constant PSD quadratic annihilating the
anti-diagonal shell collapses exactly to full fine-sample square.  Hence a PSD renormalization either
retains the ultraviolet logarithm or loses all independent cross-scale information.

The strongest positive survivor is the signed null form

```text
J=(E+O)(E-O)=E^2-O^2,
```

unique modulo full fine-sample square.  Lean proves `J->0` in both fixed-divisor infrared and every
positive parabolic ultraviolet shell.  The live global target is now a complete-divisor weighted
summation/source identity for `J`, not proof of the raw covariance constant.  `U-PN-COVARIANCE`
remains a secondary descriptive conjecture; it is no longer the selected Route-U producer.
