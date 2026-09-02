# HB arbitrary-global causal Peierls–AIME no-go

- **ID:** HB-GLOBAL-CAUSAL-AIME-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` HB open core
- **Statement:** No reciprocal, Schwarz-exchanged complex-linear retarded/advanced pair on the full Xi carrier can make its causal-jump same-fibre source response supply exact unit AIME cancellation on every Xi copy.

## RH proof chain closed or reduced

`++-` Einstein–Teukolsky source at opposite simple QNM → same-pole remainder `-AIME` → unit BM incidence → HB endpoint → RH.

This card attacks the remaining producer arrow. It kills the entire canonical linear causal Peierls realization class, including arbitrary cross-fibre/channel mixing; it does not claim that every possible QNM left projection is a Peierls source pairing.

## Exact route class

For each `n`, exclude `Gret,Gadv : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier` satisfying:

1. `HBXiPeierlsRetardedAdvancedReciprocal Gret Gadv`;
2. `HBXiPeierlsRetardedToAdvancedSchwarzExchange Gret Gadv`;
3. at every `q`, the full unit-seed projected residue with constant same-pole remainder
   `⟪Gret-Gadv · plus(1,q), minus(1,q)⟫` equals the unit BM target.

No diagonal, local, finite-range, bounded, support, or fibre-preservation assumption occurs.

## Corpus basis

`scripts/formal_tools.py research` located:

- `hbXiPeierlsRetardedAdvancedCausalJump_skew` and `_channelSchwarzOdd`;
- `hbXiPeierlsGlobalPropagator_sourceResponse_schwarzReal` for arbitrary global maps;
- `d4FullCrossBranchProjectedResidue_eq_unitBMTarget_iff_forcedCounterterm_of_criticalLine`;
- `d4FundamentalQNMCrossBranchAIMENumerator_one_im_ne_zero_of_re_eq_half`;
- `nonempty_xiCriticalLineResolventCopy_of_hardy`.

## Hostile audit

- Cross-fibre mixing does not evade the global Schwarz-reality theorem: its proof uses only Peierls skewness, channel-Schwarz oddness, pairing Schwarz reality, and canonical conjugate source packets.
- RH does not rescue the class: at a Hardy critical fibre the BM target vanishes, while exact full-residue matching still forces the nonreal `-AIME` remainder.
- This is not the existing global BM-incidence iff-RH theorem: that theorem pairs the causal response directly with the BM target; here the response is the non-AIME remainder inside the full AIME residue.
- Literature through August 2026 treats AIME secular forcing, QNM bilinear projections, higher-order QNM expansions, and causal Green decompositions, but the audit found no theorem combining this Xi critical-fibre phase obstruction with reciprocal/Schwarz-exchanged Peierls response. Novelty status: internal-new; external-new after targeted audit, not an exhaustive-proof claim.

Verdict: **SURVIVES PRELIMINARY ATTACK**.

## Dependency-closed paper proof

1. Assume a route witness and choose Hardy's unconditional critical Xi copy `q`.
2. Reciprocity makes `Δ = Gret-Gadv` Peierls-skew; Schwarz exchange makes `Δ` channel-Schwarz odd.
3. Arbitrary-global response rigidity makes `⟪Δ plus(1,q), minus(1,q)⟫` Schwarz-real, hence its imaginary part is zero.
4. Universal full-residue incidence at `q` and criticality force that response to equal the negative unit AIME numerator.
5. The unit AIME numerator has nonzero imaginary part at every critical Xi copy. Contradiction.

No open dependency remains.

## No-go closure

- **Exact killing mechanism:** causal reciprocity plus Schwarz exchange forces a real canonical source response where exact AIME cancellation requires a nonreal response.
- **Strongest positive survivor:** any HB producer retaining canonical source packets must abandon at least one of complex-linearity, Peierls reciprocity, retarded/advanced Schwarz exchange, or the canonical same-fibre pairing. Mere non-diagonal mixing is insufficient.
- **New insight:** surviving left-QNM projection must be genuinely biorthogonal/non-Peierls, source-dependent nonlinear, or use a different real structure/carrier.
- **Status:** `[LEAN-PROVED]`; theorem `d4HBArbitraryGlobalLinearCausalPeierlsAIMERouteKilled` in module `ThetaCuspHawkingHBArbitraryGlobalLinearCausalPeierlsAIMENoGo`; direct Lean and targeted build pass; standard axioms only.

## Gates

- [x] 0 → 1: exact source-pure route class, attack, and RH proof chain fixed
- [x] 1 → 2: complete proof above; no open dependency
- [x] 2 → 3: direct Lean PASS; targeted build `13488/13488`; `propext`, `Classical.choice`, `Quot.sound`
