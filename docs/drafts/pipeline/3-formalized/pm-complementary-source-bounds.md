# Route PM: signed source estimates for complementary cancellation

- **ID:** pm-complementary-source-bounds
- **Stage:** 3-formalized
- **Source:** current harmonic Möbius log-power theorem, finite Abel identity, actual Ramanujan multiples inversion.
- **Lean:** `PMRamanujanComplementarySourceBounds.lean`, three public theorems.
- **Parent:** `pm-complementary-prime-sector-cancellation.md`.

For 0<epsilon<1/2, the actual centered divisor remainder satisfies

    |D_epsilon(N)| <= 1+C_epsilon N^(1-epsilon)/log^4 N

eventually. Its proof splits at Y=floor(N/log^8 N). Increasing and decreasing Abel summation retain the signed large-divisor floor sum and the signed infinite density tail. The exact hyperbola split is exported separately. No conjectural estimate is assumed.

For 0<=beta<epsilon, Q>0 and N<=Q, the actual natural Ramanujan truncation satisfies

    |Z_(Q-1)(N)-D_epsilon(N)|
      <= N Q^(-beta) [sum_(m>=1) m^(-(1+epsilon-beta))]^2.

Exact Möbius multiples inversion identifies the cofactor tail. Its coefficient moment produces the bound before spatial summation. With Q=P^2 and beta=3epsilon/4, its anchored error energy is O(P^(1-3epsilon)); that energy estimate is now formalized inside the complementary cancellation leaf.

## Audit

Targeted old-mode leaf build passed. Final actual-file `lake env lean` passed with no diagnostics. All three exported declarations have only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`). Umbrella wired exactly once; no umbrella build. Global lint has eleven unrelated unreachable-module errors and no finding for this leaf. No added axiom, sorry, admission premise, computation, or heartbeat increase.

## Boundary

These estimates support the now audited negative mixed-energy law for the actual complementary denominator sector. The estimates retain positive-power energy growth for epsilon<1/2 and do not prove PM admission or RH. Removing that growth in the complete signed source remains the hard open producer.
