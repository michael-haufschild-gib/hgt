# JAS sparse localization (cycles 206–210)

**Status:** Formalized in Lean 4 (standard axioms). MUST-1392, 1393 (+add. 1, 2), 1395, 1397 (+add.).

## Statement (three families, three roles)

RH ⟺
1. **Half-plane:** single-prime JAS tests on large primes are positive at some level `σ < ½`. This gives `Re ρ ≤ ½ + max(σ, ¼)`.
2. **Chains:** level-one log-weight window tests are positive on the windows `(2^{2^k}, 2^{2^{k+1}}]`.
3. **Attained tops:** level-one constant-vector interval tests are positive at the dyadic scales `y = 2^m`.

Lean: `RHTower.riemannHypothesis_iff_singlePrime_and_doubleExpWindows_and_dyadicScales` (module `RHTower/JointAncestrySparseChainExclusion`).

## The exception laws behind it

- **Attained top ⇒ positive lower density of lag excursions.** Real residue limit plus Abel bound, with no local finiteness. See `RHTower/WeilLagFunctionDensityZeroExcursion`.
  - Quantitative form: upper density ≥ `Re w_{ρ₀}/(4W)`.
- **Given ¬chain, constant-vector positivity** may either
  - fail on any lower-density-zero set of log-scales, or
  - be required only at one geometric progression of scales (`RHTower/JointAncestryProgressionScales`; majorant single-base Dirichlet lemma).
- **Chain exclusion (corpus, under quasi-RH)** needs window tests only on chain-rich index sets. The window exponent θ is chosen after the peak, using uniform window conditions on `[θ₂/2, θ₂]`. The doubly exponential indices are chain-rich (`chainRichWindows_doubleExp`).
- **Without side conditions:** all scales or exponentially thin exceptions (MUST-1390). The Paley–Wiener range (∫f/t = ∞) is OPEN.

## Reading

- Given a power-saving PNT (quasi-RH), the RH content of route JAS is localized on two countable, extremely sparse test families.
- Sparse families cannot replace quasi-RH:
  - sparse-prime single-prime tests are blind to chains above `½ + σ`;
  - chain exclusion needs power-saving Perron bounds (corpus diagnosis).
- The irreducible core is the half-plane, i.e. the classical power-saving prime number theorem. Everything else is sparse positivity.

## Open
- The Paley–Wiener rigid side: subexponential exceptions without side conditions. Linear Bochner bounds at period times do not suffice; compensator rigidity is needed.
- Sparser single-prime families yielding a half-plane: blocked by chains above `½ + σ`.
