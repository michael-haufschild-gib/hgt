# Hyperbolic source-pair deletion at critical normalization

- **ID:** RP-30 through RP-32
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Route RP; actual signed source pairs, retaining every gcd class.

## Proved statement

Let A_M(d)=mobiusDivisorDilationChannel M d. Unconditionally,

    sum_{1<=d,e<=M, d*e<=M} A_M(d)*A_M(e) / M^2 -> 0.

The exact full-square partition retains every complementary pair:

    (sum_{d<=M} A_M(d))^2
      = sum_{d*e<=M} A_M(d)*A_M(e)
        + sum_{d*e>M} A_M(d)*A_M(e).

Consequently the normalized full square differs from the normalized
complementary sum by a term tending to zero. Both diagonal portions are
retained. No coprimality restriction or individual pair-sign assumption occurs.

This settles the growing hyperbolic sector. It does not bound the remaining
complementary sum, pay either native RP square debt, or prove/falsify RH.

## Dependency-closed paper proof

Write V_M(d) for the unsigned channel, v_M(d)=V_M(d)/sqrt(M), and
c=log(2*pi)/2-gamma-1/4.

1. **Uniform profile remainder (RP-30).** There exist C>=0,T>=1 such that
   |v_M(d)-c|<=C/floor(M/d)^(1/40) whenever d>0 and floor(M/d)>=T.
   The growing reciprocal-phase Fourier cutoff pays the terminal Bernoulli
   residue. The reciprocal correction, square births, smooth term, and exact
   clipped interpolation are retained. The global bound |v_M(d)|<=3/5
   extends this to one constant C' satisfying
   |v_M(d)-c|<=C'/e^(1/40) for every positive pair d*e<=M.
2. **Constant-profile convolution (RP-31).** For
   P_M=sum_{d*e<=M} mu(d)*mu(e), square-root hyperbola inclusion-exclusion gives
   P_M=2*sum_{d<=r} mu(d)*Mertens(floor(M/d))-Mertens(r)^2,
   r=floor(sqrt(M)). The corpus's log-squared Mertens rate bounds
   |P_M|/M by 2*B*H_r/log(r)^2+(B/log(r)^2)^2, which tends to zero.
3. **Actual quotient prefixes (RP-32).** On the cell
   M/(j+1)<e<=M/j, the exact clipped homothety gives
   A_M(e)=mu(e)*(sqrt(e)*a_j+sqrt(M)*b_j),
   where a_j=V_j(1)-sqrt(j)*D(j), b_j=D(j).
   Discrete Abel summation bounds every square-root-weighted Möbius prefix
   below M by 2*sqrt(M)*mertensSup(M). Ordinary interval sums are at most
   2*mertensSup(M), weighted intervals at most 4*sqrt(M)*mertensSup(M).
   Thus each fixed cell is o(M*sqrt(M)). The full-channel log-normalized
   asymptotic starts the induction; subtracting adjacent cells yields
   sum_{d<=M/e} A_M(d)/(M*sqrt(M))->0 for every fixed positive e.
   The actual fixed pair rows, finite strips, and finite corners are also paid.
4. **Whole-sector assembly (RP-32).** Define b_M(d)=mu(d)*(v_M(d)-c).
   Symmetry gives the exact normalized profile difference as

       sum_e mu(e)*(v_M(e)+c)*
         (sum_{d<=M/e} b_M(d))/M.

   Each fixed row tends to zero by step 3 and ordinary Mertens cancellation.
   Step 1 and floor(M/e)<=M/e bound every row, uniformly for M>0, by

       C'*(3/5+|c|)/e^(41/40).

   This is summable. Tannery's theorem sends the whole row sum to zero.
   Adding c^2*P_M/M proves the literal sector limit.
5. **Native partition.** Finite distributivity splits the full signed square
   exactly at d*e=M. The proved sector limit supplies the complementary
   remainder statement without deleting any diagonal or common-divisor term.

The exponent is not optimized; its positive value makes the row bound
summable. No numerical experiment supplies any part of this proof.

## Lean endpoints

- RoutePTerminalModularPowerSaving.lean: actual terminal residue power saving.
- RoutePUnsignedProfilePowerSaving.lean:
  routeP_unsigned_channels_uniform_power_saving.
- RoutePMobiusHyperbolaCancellation.lean:
  routeP_mobius_hyperbola_div_tendsto_zero.
- RoutePFixedHyperbolicStrips.lean:
  routeP_channel_quotient_cell,
  routeP_quotient_cell_bound,
  routeP_quotient_cell_normalized_tendsto,
  routeP_fixed_quotient_prefix_tendsto,
  routeP_fixed_pair_row_tendsto,
  routeP_fixed_pair_strip_tendsto,
  routeP_fixed_pair_corner_tendsto.
- RoutePHyperbolicPairDeletion.lean:
  routeP_hyperbolic_pair_sector_tendsto_zero,
  routeP_hyperbolic_pair_partition,
  routeP_complementary_pair_remainder_tendsto_zero.

## Audit

RP-30 and RP-31 final leaf and axiom audits passed as recorded in the working
log. Both RP-32 leaves passed foreground
lake --old env lean <module> -o <olean>, exit 0 without diagnostics.
Both are wired once into RHTower. No full/umbrella build ran.
Separate RP-32 axiom audit passed exit 0. All ten public theorems use exactly
[propext, Classical.choice, Quot.sound]; printed endpoint types have no
implicit analytical premises.
Selected whitespace and forbidden-token/resource checks passed. Global lint
exited 1 on ten unrelated unreachable modules; neither new leaf is flagged.
No global lint pass is claimed.

## Remaining hard problem

Prove a uniform quadratic upper bound for the full literal sum over d*e>M,
or exhibit unbounded normalized positive excursions that falsify the critical
bound. Common-divisor classes must remain together. Existing individual-sign,
positive-Gram, finite-core delayed-repair, and Xi-norm obstructions still apply.
Do not redo the now-paid hyperbolic sector or substitute an RH criterion for
the missing arithmetic estimate.

