# BM finite-source Green radical classification

- **ID:** HB-BM-FSGR
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `HB-BM3-PPC` physical-source open core · exact physical BM horizon Green kernels
- **Statement:** `[LEAN-PROVED] [REDISCOVERED] [BRIDGE]` For every finite interior radial source packet and every nonresonant BM angular parameter, canonical ingoing and outgoing Green responses agree as functions exactly when one explicit normalizable-mode source moment vanishes.

## Goal

Classify all finite radial dark sources before inserting the augmented Einstein quadratic source.
Replace unjustified inference from point-source Green noncollapse to arbitrary-source noncollapse by
one exact scalar moment obligation.

This does not prove RH. It closes finite radial propagation and leaves source-first evaluation of
the literal augmented Einstein quadratic profile.

## Gates

- [x] 0 → 1 in-progress: exact statement frozen from current Lean kernel identities
- [x] 1 → 2 fully-proven: dependency-closed proof and hostile review
- [x] 2 → 3 formalized: exact Lean theorem, targeted build, lint, and axiom audit
- [ ] 3 → 4 publication-ready: standalone proof and priority audit

## Exact frozen claim

Fix `n : Nat`, `chi : Complex` with `chi.re != 0`, a finite set `S`, interior points
`t_i in (0,1)`, and complex source weights `f_i`. Let `V(z)` be the exact BM normalizable AdS
solution, `G_in(t,z)` and `G_out(t,z)` the canonical regular-horizon and
complementary-horizon right Green kernels, and

`M_V(f) = sum_(i in S) f_i V(t_i)`.

Let `A_R` and `A_C` be the nonzero forbidden/source connection coefficients of regular and
complementary horizon solutions, and let `lambda = 4n+3+2i chi` be the complementary Frobenius
exponent. Define

`g_BM = -4 lambda / (A_R A_C)`.

Then

`sum_i f_i (G_in(t_i,z)-G_out(t_i,z)) = g_BM M_V(f) V(z)`

for every real `z`, `g_BM != 0`, and therefore

`(forall z, sum_i f_i G_in(t_i,z) = sum_i f_i G_out(t_i,z)) iff M_V(f)=0`.

The same classification holds on every `XiZeroCopy` after substituting the corpus BM angular
parameter.

## Hostile attack targets

- Denominators might depend on source point after sewing.
- `lambda`, `A_R`, or `A_C` might vanish despite `chi.re != 0`.
- Response equality as functions might fail to imply scalar projection zero if `V` were the zero
  function.
- Claim might be only classical rank-one resolvent theory, not new scientific knowledge.

## No-go closure

- **Exact killing theorem/mechanism:** point-source noncollapse does not exclude cancellations among finite radial packets; Green difference has rank one.
- **Strongest positive survivor:** conjectured exact radical classification above.
- **New insight:** physical HB source incidence reduces to one normalizable-mode moment, not a global kernel-equality problem.
- **Status:** internal audit complete; paper proof and priority audit pending.

## Log

- 2026-08-27 — created from latest Lean corpus after Gauss/Jost and physical-horizon incidence closure.

## Complete paper proof

`[PAPER-PROVED]` Exact Wronskian sewing gives, at every interior source point,

`D_R(t) = -A_R/2` and `D_C(t) = -A_C/2`.

Thus denominators are independent of `t`. Substitution in corpus finite-source projection gives

`P(f) = sum_i f_i [-lambda V(t_i)/(D_R(t_i)D_C(t_i))]`

`= [-4 lambda/(A_R A_C)] sum_i f_i V(t_i) = g_BM M_V(f)`.

The assumptions `chi.re != 0` imply `lambda != 0`, `A_R != 0`, and `A_C != 0`; hence
`g_BM != 0`. Existing finite-response factorization now yields

`R_in(f;z)-R_out(f;z)=g_BM M_V(f)V(z)`.

If `M_V(f)=0`, response difference vanishes for every `z`. Conversely, exact square-root AdS
asymptotics provide an interior `z_0` with `V(z_0) != 0`. If response difference vanishes for every
`z`, evaluation at `z_0`, followed by nonvanishing of `g_BM` and `V(z_0)`, forces `M_V(f)=0`.
This proves the claimed equivalence. Xi specialization uses the premise-free theorem
`d4BMXiMixedHorizonAngularMomentum_re_ne_zero`.

## Hostile review and priority verdict

- Denominator dependence is eliminated by exact global Wronskian identities, not assumed.
- All three gain factors are formally nonzero under the stated nonresonance condition.
- Converse uses a proved interior nonzero point of the normalizable solution; no global
  nonvanishing claim is needed.
- General rank-one resolvent difference is Krein/Sturm--Liouville theory. External primary
  literature includes Clark--Gesztesy--Nichols--Zinchenko (2012/2014) and
  Allan--Kim--Michajlyszyn--Nichols--Rung (2019/2026). Exact BM hypergeometric coefficient and
  finite-source radical specialization appear corpus-specific, but mechanism is not new.

Verdict: `[REDISCOVERED] [BRIDGE] [PAPER-PROVED]`, not candidate new scientific knowledge.

## Updated no-go closure

- **Exact killing theorem/mechanism:** finite source packets have an exact codimension-one dark
  radical; point-source noncollapse cannot supply source-global noncollapse.
- **Strongest positive survivor:** complete radical classification by `M_V` with explicit nonzero
  BM gain `g_BM`.
- **New insight:** actual augmented Einstein incidence is now one source-moment evaluation. Any
  replacement conjecture must prove phase/sign alignment or compute this moment from the literal
  quadratic source; generic Green noncollapse is insufficient.
- **Status:** dependency-closed paper proof and exact Lean formalization complete.

## Lean formalization

- Module: `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMSecondHarmonicFiniteSourceGreenRadical.lean`
- Exact classification:
  `d4BMPlusPlusFiniteIngoing_eq_outgoing_iff_normalizableSourceMoment_eq_zero`
- Supporting factorization:
  `d4BMPlusPlusFiniteIngoing_sub_outgoingRightEndpointGreenResponse_eq_gain_mul_moment`
- Direct check: `lake env lean` passed.
- Final targeted audit:
  `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicFiniteSourceGreenRadical`
  passed.
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.
- `scripts/formal_tools.py lint`: passed.
- Wired into `formal/GaloisForLFunctions/RHTower.lean`.

- 2026-08-27 — paper proof closed; hostile audit identifies classical Krein parent theory and
  freezes exact one-moment survivor.
- 2026-08-27 — exact theorem formalized, targeted module built, axioms audited, formal lint passed,
  and umbrella import wired.
