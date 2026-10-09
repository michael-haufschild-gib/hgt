# Finite excess controls mixed-sign log-shift potentials

- **ID:** weil-logshift-one-sided-excess-control
- **Stage:** 3-formalized
- **Source policy:** Lean corpus only. No external papers, numerical experiments,
  heartbeat increases, full builds or umbrella builds.
- **Write scope:** new Lean leaf, umbrella import, this card, generated index,
  owned scratch and cross-session memory.

## Context and exact conjecture

Previous turn proved a uniform potential criterion assuming absolute summability
of normalized deviation. Finite excess alone does not imply that assumption.
The unrestricted mixed-sign rigidity question remains open.

Let a(n)=WeilExcess.weilDeviation(lam,n), e(n)=max(a(n),0), E=sum e(n).
Selected conjecture: finite E and WeilLogShiftAsymptoticPositive(lam) imply

    |a(n)| <= 100 E for every n,

and, without assuming summable deficit, every signed potential series converges
and psi(0)<=psi(log m) for every integer m>=2. Thus the necessary potential
constraint survives under one-sided summability, including infinite deficits.

This does not assert absolute summability, uniform convergence of the expanding
panel under the weaker assumption, or the converse potential criterion.

## Corpus audit and attack

- Documented `logShift excess bounded` query: one relevant kernel-norm bound;
  no coefficient-control or one-sided potential theorem.
- Existing finite-panel excess-mass budget is quantitative even with a negative
  panel floor. It can be combined with arbitrarily small asymptotic tolerances.
- Existing full-cone potential estimates need only a logarithmic bound on a,
  although their public wrappers assume full Weil positivity. The new constant
  bound supplies that analytic input from the much smaller test family.
- No unsupported kernel monotonicity or external novelty claim is used.
- Verdict: SURVIVES PRELIMINARY ATTACK; exact partial premise discharge.

## Dependency-closed paper proof [CLOSED]

1. Every finite visible excess sum is <=E. Each positive deviation is <=E.
2. If a(n)<0, put d=-a(n)>0, choose t=log d, and apply the existing finite-panel
   budget after both its cutoff and the asymptotic-floor cutoff. Use panel floor
   -(4K(0))*epsilon. The budget gives d/100-epsilon<=E.
3. Let epsilon decrease to zero. Then d<=100E. Together with step 1 and E>=0,
   this proves |a(n)|<=100E for all n, including the guarded zero entries.
4. The constant bound implies |a(n)|<=2log n+100E. Existing exponential kernel
   decay and the summable logarithmic inverse-square majorant make the potential
   terms summable for every fixed shift. Dominated convergence proves truncated
   potentials converge at every fixed shift, with no full-positivity input.
5. The exact functional decomposition for a fixed shift is zero-side value plus
   2(psi_L(log m)-psi_L(0)). The zero-side norm tends to zero at fixed m by the
   existing near-radical energy limit. Hence the fixed probe converges to
   2(psi(log m)-psi(0)).
6. The probe enters every sufficiently late finite panel. Asymptotic positivity
   bounds its values below by every negative epsilon eventually, so its limit
   is nonnegative. This gives the potential inequality for every m>=2.
7. Original WeilLogShiftTestsPositive implies the asymptotic predicate, and raw
   summable excess gives Summable deviationExcess via the existing conversion.
8. The same coefficient bound makes every deficit-potential series summable.
   The excess potential is at most 2K(0)E at every shift. Split the signed
   potential as excess potential minus deficit potential. Step 6 therefore
   gives the uniform sampled bound

       deficitPotential(log m) <= 2K(0)E - psi(0),  m>=2.

   This supplies both convergence of the deficit potential at every real shift
   and one bound at all integer-log sample points, without full Weil positivity.

## Work log

- [x] Read objective; previous turn classified as verified progress.
- [x] Audit exact corpus sources and close paper proof.
- [x] Check APIs and formalize the quantitative bound and potential consequences.
- [x] Leaf/axiom audits, wire, index, lint and promote card.
- [x] All owned jobs terminal; removed all eight inventoried scratch files and
  verified absence. Recorded `research/weil-logshift-one-sided-excess-control-2026-10-09`.

**[PAPER PROVED; LEAN VERIFIED]**

## Implemented result

Source: `formal/GaloisForLFunctions/RHTower/WeilLogShiftExcessControl.lean`.

- `abs_weilDeviation_le_total_excess_of_logShiftAsymptoticPositive`: the
  quantitative global bound |a(n)|<=100E, under asymptotic positivity and
  Summable deviationExcess.
- `summable_potential_of_logShiftAsymptoticPositive`: every signed potential
  series is summable at every real shift.
- `tendsto_truncatedPotential_of_logShiftAsymptoticPositive`: fixed-shift
  truncated-potential convergence under one-sided summability.
- `tendsto_logShift_probe_of_summable_excess`: exact fixed-probe limit
  2(psi(log m)-psi(0)) as real window size tends to infinity.
- `logShiftAsymptotic_potential_le_of_summable_excess`: necessary potential
  inequalities for every integer m>=2, with no absolute-summability premise.
- `logShiftTests_potential_le_of_summable_excess`: original exact countable
  positivity plus raw summable excess supplies those same inequalities.
- `deficit_potential_control_of_summable_excess`: deficit potential converges
  at every real shift and is bounded at every integer-log sample by
  2K(0)E-psi(0).

## Significance and next cycle

This discharges the absolute-summability premise from the NECESSARY potential
constraints and supplies coefficient and deficit-potential control from the
small countable test family. It does not prove summable deficit, a uniform
potential limit over the expanding panel under these weaker assumptions, the
converse criterion, or equality of a mixed-sign sequence with von Mangoldt.
External novelty remains unassessed under the user's source restriction.

No work was deferred for effort estimates. The next concrete gap is upgrading
the sampled deficit-potential bound to control at all real shifts or to a
CauchyBounded deficit. A possible route uses positivity of K on a compact
interval to bound deficit mass in each logarithmic unit interval from a nearby
integer-log sample, then sums the exponentially decaying tails. That route
still needs its own dependency and proof audit; no such upgrade is claimed here.

## Verification log

- Final leaf check exited 0 without diagnostics and emitted its olean using
  `lake --old env lean` at default heartbeat; no full or umbrella build.
- Umbrella import observed exactly once at line 6930.
- Index command exited 0; all seven public declarations are indexed.
- Scoped whitespace checks produced no diagnostics.
- Authoritative lint exited 1 on ten unrelated unreachable modules:
  `RHTower.SincSeparatorContour`, `RHTower.SincSeparatorMellin`,
  `RHTower.StretchedBoseDefect`, `RHTower.StretchedBoseSeparator`;
  `HTGeometry.ApertureConeCalculus`, `HTGeometry.ApertureConeWinding`,
  `HTGeometry.ApertureLogTranslation`, `HTGeometry.ApertureOpenHistoryIdeal`,
  `HTGeometry.BoundaryCoronaCStarAlgebra`, `HTGeometry.ComplexRateGammaIntegral`.
  No lint error concerns this module.
- Separate import/signature/axiom audit exited 0. All seven public signatures
  were inspected, and all seven declarations depend exactly on
  `[propext, Classical.choice, Quot.sound]`.
