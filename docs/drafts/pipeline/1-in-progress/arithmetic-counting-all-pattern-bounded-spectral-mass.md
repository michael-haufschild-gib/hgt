# Counted spectral mass for arbitrary prime patterns

- **ID:** ACP-ALL-PATTERN-BOUNDED-SPECTRAL-MASS
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / proof plan
- **Parent:** arithmetic-counting-positivity.md
- **Input under formalization:** ../2-fully-proven/arithmetic-counting-all-pattern-actual-conductor-coordinates.md

## Targets

For any prime pattern P and any threshold T outside the arithmetic energy
set, prove that the actual squared constraint mass on energies below T
tends to sum_(m:E_m<T) a_P(m)^2. This includes every eigenline in the
bounded window, with multiplicity, not only selected conductor lines.

Then prove the actual full scalar resolvent below the first excitation
converges to sum_m a_P(m)^2/(E_m-gamma-s), for every P and 0<s<2 log 2.
At positive Euler density this is the normalized infinite arithmetic
secular series. At zero density the proposed absolute limit is zero.

## Existing count input, read and checked as a statement

TheBoundedPrimeSpectrumIsTheAdjunctionSpectrum.lean proves
eventually_fullPrime_spectral_count_eq: away from the arithmetic energy
set, the literal prime-matrix sublevel count eventually equals the finite
arithmetic conductor count. The entire proof was read. Its lower bound
comes from distinct conductor packets; its upper bound comes from the
finite Ramanujan coordinate certificate and residual estimates. No RH
assumption appears in this statement.

TheAdjunctionEnergyHasFiniteSublevels.lean was also read: E_m-gamma>=log m,
the strict conductor sublevel is finite, and its members have a positive
gap below its threshold. These are leads for the bounded-window transfer;
transitive audits must still accompany any new consuming theorem.

## Proof plan

1. For the finite conductor sublevel S, choose the actual eigenline
   sequences from the all-pattern coordinate transfer. Distinct limiting
   energies make their indices eventually distinct. Their energies are
   eventually below T.
2. The exact sublevel cardinality then makes this finite injection
   surjective onto the actual low-energy indices. Reindex the finite mass
   sum and use the already proved coordinate limits.
3. When c=0, every a_P(m) vanishes, so every fixed bounded-energy sublevel
   has asymptotically zero constraint mass. This strengthens escape from
   fixed conductor packets to escape from all bounded energy windows.
4. For the resolvent, isolate the unique ground line, keep a large regular
   bounded-energy packet, and bound the high-energy tail by unit total
   horizon mass divided by T-gamma-s. Let T increase through regular
   thresholds. Supply an explicit existence argument for arbitrarily
   large regular thresholds; do not assume an ordering of conductor
   energies by conductor size.
5. At positive density the existing unit-mass packet resolvent lemma is
   an alternative route. Compare dependencies before choosing the common
   proof, and keep the zero-density case fully explicit.

## Sharp unresolved boundary

An absolute resolvent limit of zero does not determine its eventual sign,
so it does not determine the greatest gap at zero Euler density. The
relative ground/positive-tail balance remains a separate problem.
In particular, divergent unnormalized conductor mass need not by itself
force divergence after division by energy. Whether zero-density patterns
can retain a positive gap remains a question here, not a conclusion.

No paper proof or Lean endpoint is claimed on this card yet. The full
Weil positivity producer and the broader programme remain open.
