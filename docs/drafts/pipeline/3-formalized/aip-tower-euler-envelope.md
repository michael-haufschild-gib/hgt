# The Euler-factor tower law for the prime side of the critical form

- **ID:** aip-tower-euler-envelope
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `ArithmeticIncidencePositivity` README §5 open problem 7(c) and research topic 6 (the
  ledger past the windows); `ArithmeticCriticalityTheory` README §5 frontier 1 (the prime-side
  inequality)
- **Statement:** For every continuous test `F` supported in `[−B, B]` and every prime `p`,
  `(p − 1) · C_p(F) ≤ log p · (A(0) + √p · A(log p))`, where
  `C_p(F) = Σ_{k ≥ 1} Λ(p^k) p^{−k/2} A(k log p)` is the ledger charge of the whole tower of `p`
  and `A = autoCorr F`.

## Goal

The incidence ledger reads the prime side strip by strip, one strip per prime power, and the open
core is that the costs of several shifts must be paid at once (research topic 6). This card supplies
the first unconditional law that ties all shifts of one tower together: the charge of all powers
`p, p², p³, …` is a function of the single first-power datum `A(log p)` with explicit Euler
constants.

- The proper prime powers of the ledger carry no information of their own: their costs are absorbed
  into the prime's own autocorrelation, so the cost side of mechanism 43 is bounded by a functional
  of the *prime* strips alone. (Dropping them is false — `RHTower.primeWeights_not_weilPositive` —
  but bounding the tower by its first power is not.)
- The law is a *discount*, not an envelope. In the general form, with `z ∈ (0,1)`, `L > 0`:
  `Σ_{m≥1} z^m A(mL) ≤ z/(1−z) · A(0) − z/(1−z²) · (A(0) − A(L))`. Every unit of first-lag fold
  defect `A(0) − A(L)` discounts the whole tower. A test uncorrelated at the prime shift charges
  the tower at most `log p/(p − 1) · A(0)` instead of the resonant maximum `log p/(√p − 1) · A(0)`.
- Units: the law is an a priori bound on the cost side at every aperture, PNT-free and with no
  family average, one character, modulus one, shift zero.
- Selectivity: for `ζ(s−a)ζ(s+a)` the tower weight becomes `z = p^{a−1/2}` and the geometric
  envelope diverges exactly at `a = ½`, so the mechanism measures the off-line distance; it is not
  a statement about an arbitrary even positive kernel. For a Beurling system the law holds for each
  generator that has a tower of powers, with the constants of that generator.

### The prime side is carried by the primes (second pass)

Reindexing the prime side `Σ_{n ≥ 2} Λ(n) n^{−1/2} A(log n)` by towers (`Nat.Primes.prodNatEquiv`)
and applying the tower law prime by prime gives, for every finite set `T` of primes containing all
primes below the horizon `e^{2B}`,

    primeSide F ≤ Σ_{p ∈ T} log p/(p − 1) · (A(0) + √p · A(log p)).

The right-hand side is the *first-power* part of the prime side, inflated by `p/(p − 1) ≤ 2`, plus
`A(0) · Σ_{p ∈ T} log p/(p − 1)`, which by Mertens (corpus: `RHTower.MertensFirst`) is
`O(B) · A(0)`. So the proper prime powers are a sector of size *aperture × mass*, while the ledger's
demand at aperture `B` is of size `e^{B}`: **the whole exponential demand of the incidence ledger
sits on the primes and their first-power autocorrelations.** This localizes open problem 7(c) to a
statement about `A(log p)`, `p` prime, with no prime powers left in it.

### The ratio off-diagonal is the whole difficulty (third pass)

Pairing the test against the weighted translate train of the prime shifts and applying
Cauchy–Schwarz to the pairing gives the **shift-Gram law**

    (Σ_k α_k A(c_k))² ≤ A(0) · Σ_{j,k} α_j α_k A(c_k − c_j),

for any finite family of shifts. At the prime shifts `c_k = log k` with the atoms `α_k = Λ(k)k^{−1/2}`
the second factor is the correlation form of the prime shifts, indexed by the **ratios** `k/j` —
the ratio pairs of the incidence structure — and it splits exactly as

    diagonal `A(0) Σ_k Λ(k)²/k`  +  `ratioOffDiagonal F n`.

The diagonal is of size `A(0)(log n)²`, so the diagonal bound on the prime side is `A(0) log n`:
archimedean size, the size the Weil archimedean term supplies. The trivial bound is `A(0)√n`.
Hence the entire gap between the trivial prime side and an archimedean-size prime side is carried
by the off-diagonal ratio correlations, and "the ratio pairs are not positively correlated"
(`ratioOffDiagonal F n ≤ 0`) is a *sufficient* replacement hypothesis
(`abs_sum_prime_autoCorr_le_of_ratioOffDiagonal_nonpos`). Together with the second pass this says:
after the prime powers are absorbed and the diagonal is paid by the archimedean side, what remains
is one statement about prime pairs at correlated ratios.

### The ledger with the prime powers eliminated (fourth pass)

The ledger's net charge at a relevant shift is exactly the atom times the autocorrelation,
`evenStripGain_n − oddStripCost_n = −2 Λ(n) n^{−1/2} A(log n)`
(`evenStripGain_sub_oddStripCost_eq`, from the corpus even–odd identity
`integral_mul_shift_eq_two_reflectedOdd_sub`), so the ledger's whole prime sector is `−2` times the
prime side (`sum_evenStripGain_sub_sum_oddStripCost`). Feeding in the prime-only bound gives, for
every odd `F ∈ C²_c` supported in `[−r, r]` and every plateau radius `R > r`
(`fullZeroForm_ge_primeOnlyLedger`):

    Ẑ(F) ≥ pool + crossing potential + gauge remainder − pole charge
           − 2 Σ_{p ∈ T} log p/(p − 1) · (A(0) + √p · A(log p)).

No prime power appears on the right. This is the ledger of mechanism 43 with its cost side reduced
to prime data, at every aperture.

### Two towers: the product and ratio shifts as payers (fifth pass)

Reading the `b`-train `G = Σ_{k ≤ N} w^k F(· + kb)` as the test and applying the tower law to it at
the spacing `a` gives a law for the whole lattice of mixed lags. The autocorrelation of the train is
the **train lag charge** `A_G(s) = Σ_{j,k ≤ N} w^{j+k} A(s + (k − j)b)`
(`autoCorr_geoTrain_eq_trainLagCharge`), a two-sided `b`-ladder of the lag `s`, and

    (1 − z²) Σ_{m ≥ 1} z^m A_G(ma) ≤ z² A_G(0) + z A_G(a)

(`one_sub_sq_mul_tsum_trainLagCharge_le`, with the discount form
`tsum_trainLagCharge_le_envelope_sub_discount`). At `z = p^{−1/2}`, `a = log p`, `w = q^{−1/2}`,
`b = log q` the lags on the left are the integers `p^m q^{±i}` — the **product** shifts
`log(p^m q^i)` and the **ratio** shifts `log(p^m/q^i)` of the pair `{p, q}`, with the Euler weights
of both primes — and the right side is the `q`-ladder at the two lags `0` and `log p`. So the whole
coupling graph between two towers (AIP open problem 6) is controlled by two ladder charges.

Alongside: the **incidence energy of a pair of spacings**
`A(0) − A(a) − A(b) + (A(a+b) + A(a−b))/2`, a quarter of `‖(1−T_a)(1−T_b)F‖²`, is nonnegative
(`pairIncidenceEnergy_nonneg`) — the first unconditional positivity in which the product shift
`a + b` and the ratio shift `a − b` of two prime shifts appear together.

### The Gram closure: the same-prime sector is bounded (sixth pass)

In the correlation form of the prime side the off-diagonal entry of a pair `(j, k)` of prime powers
is read at the logarithm of their ratio. The ratio is an integer exactly when the two are powers of
the same prime, and then the entries close back onto the towers: for every prime `p`

    towerRatioPairs p F = log²p/(p − 1) · (tower lag charge of p)        (`towerRatioPairs_eq`)

and therefore, by the tower law,

    towerRatioPairs p F ≤ log²p/(p − 1)² · (A(0) + √p · A(log p))       (`towerRatioPairs_le`).

The weight `log²p √p/(p−1)²` is `≍ log²p/p^{3/2}`, so summed over the primes this sector is `O(A(0))`
— a **bounded** sector — while the prime side itself is of size `√N · A(0)`. Together with the third
pass: the diagonal of the Gram form is archimedean-size, the same-prime off-diagonal is bounded, and
the entire difficulty of the prime side sits in the **cross-prime** off-diagonal, the pairs
`(p^i, q^s)`, `p ≠ q`, read at the lag `log(p^i/q^s)`. That is the object the bi-tower law of the
fifth pass is built for.

### The tower is paid by the strip of its first atom (seventh pass)

In the ledger's own objects: for an odd test supported in `[−r, r]`,

    towerCharge p F ≤ log p/(p − 1) · A(0) + p/(2(p − 1)) · evenStripGain F r p

(`towerCharge_le_firstAtomStrip`, `towerCharge_le_evenStripGain`, using the corpus odd strip bound
`integral_mul_shift_le_strip`). So the whole tower of `p` costs at most half the Euler inflation
(`p/(p−1) ≤ 2`) of the **even strip gain of its first atom**, plus an archimedean-size term.
Mechanism 35 pays that gain from the atom's own strip, so the ledger's allocation problem over all
prime powers reduces to one over the primes with the same strip budgets.

### The decorrelation criterion (eighth pass)

Distinct integers below the horizon `N` have logarithms separated by at least `1/N`
(`one_div_le_abs_log_sub_log`, from `log(u/v) ≥ 1 − v/u ≥ 1/u`): every **cross** lag of the prime
side avoids the resolution scale of the horizon. Hence if the test decorrelates beyond that scale,
`|A(t)| ≤ ρ A(0)` for `|t| ≥ 1/N`, the correlation form is diagonal up to `ρ` and

    |Σ_{k ≤ N} Λ(k)k^{−1/2} A(log k)| ≤ A(0) √(Σ_{k ≤ N} Λ(k)²/k + ρ (Σ_{k ≤ N} Λ(k)/√k)²)

(`abs_sum_prime_autoCorr_le_of_decorrelated`). The first sum is `≍ log²N`, the second `≍ N`, so a
test that decorrelates to `ρ ≲ log²N/N` beyond the lag `1/N` has an **archimedean-size** prime side.
This is a replacement hypothesis on the test, proved sufficient: tests that resolve the scale `1/N`
— the zero spacing at the horizon — are harmless. It is the first unconditional sufficient
condition in the programme that is a property of the test alone and covers every aperture.

### The archimedean floor of a decorrelating test (ninth pass)

The same decorrelation hypothesis that tames the prime side forces a *logarithmic* archimedean
energy. With `ω(t) ≥ e^{−1/2}/(2t)` on `(0,1]` and `A(0) − A(t) ≥ (1 − ρ)A(0)` for `t ≥ δ`,

    ∫_δ^1 ω(t) ‖F − F(·+t)‖² dt ≥ e^{−1/2} (1 − ρ) A(0) log(1/δ)

(`archBandEnergy_ge_of_decorrelated`, with `continuous_autoCorr_of_lipschitz` supplying the
regularity). At `δ = 1/N` this is `≍ A(0) log N` — the same order as the eighth pass's bound on the
prime side. So **in the decorrelating regime the two sides of the critical inequality are
commensurable**: the comparison is a question of constants, not of orders, whereas on the trivial
allocation the demand is `√N` against a logarithmic supply. This locates the only regime in which
the ledger can balance, and says what has to be won there: a constant.

### The coupling graph of two shifts, with tunable weights (tenth and eleventh passes)

The weighted double difference `(1 − λT_a)(1 − μT_b)F` gives, for every pair of weights,

    2λ(1+μ²) A(a) + 2μ(1+λ²) A(b) ≤ (1+λ²)(1+μ²) A(0) + 2λμ (A(a+b) + A(a−b))

(`two_shift_coupling`). Normalising (`λ = 1`, `θ = μ/(1+μ²) ∈ (0, ½]`) gives the sharp
one-parameter law

    A(a) + 2θ A(b) ≤ A(0) + θ (A(a+b) + A(a−b))                    (`autoCorr_coupling_le`)

with the **exact identity**

    A(0) + θ(A(a+b)+A(a−b)) − A(a) − 2θA(b) = (1−2θ)(A(0) − A(a)) + 2θ · pairIncidenceEnergy F a b

(`autoCorr_coupling_identity`). In symbol form the slack is `(1 − cos aξ)(1 − 2θ cos bξ)`, so
`θ ≤ ½` is exactly the admissible range: **the edge weight of the coupling graph between two
towers is at most ½**, and the payers are the product shift `a+b` and the ratio shift `a−b`. This
is AIP open problem 6 (the coupling graph between windows) with its edges and their sharp weights.

### The witness: the envelope is attained by a multiplicative progression (twelfth pass)

`ResonantTrainWitness.lean`: for a bump `g` of diameter below the spacing, the train
`S = Σ_{k ≤ M} g(· + kL)` has `A_S(mL) = (M + 1 − m) A_g(0)`
(`autoCorr_resonantTrain`, `autoCorr_resonantTrain_zero`) and

    geoLagCharge z L S ≥ ((M+1)(z − z^{M+1})/(1−z) − z/(1−z)²) · A_g(0)

(`geoLagCharge_resonantTrain_ge`). Against its mass `(M+1)A_g(0)` the train charges the fraction
`z/(1−z) − z^{M+1}/(1−z) − z/((M+1)(1−z)²)` → `z/(1−z)`: **the Euler envelope is sharp, and its
extremal tests are the trains carried by a multiplicative progression** `{1, p, p², …}` — at
`L = log p`, the tower of `p` itself. The content of the tower law is therefore its discount.

### The coupling weight ½ is sharp (thirteenth pass)

On the train resonant at `b = L` and blind at `a = L/2` (`autoCorr_resonantTrain_eq_zero` gives the
blindness away from the lattice of multiples) the coupling law reads `2θ M ≤ M + 1`, so every
`θ > ½` fails for large `M` (`exists_resonantTrain_coupling_fails`): the admissible range of the
coupling graph's edge weight is exactly `[0, ½]`, matching the symbol computation.

### The squarefree incidence positivity (fourteenth pass)

Taking the product of the two-shift squares over a whole finite family of shifts gives one term per
**subset**, and the self-pairing of

    Σ_{S ⊆ s} (−1)^{|S|} (Π_{i ∈ S} λ_i) F(· + Σ_{i ∈ S} a_i)

is nonnegative (`squarefree_incidence_nonneg`, on the Finset-indexed Gram expansion
`testPairing_finsetComb` now in the calculus):

    0 ≤ Σ_{S, T ⊆ s} (−1)^{|S|+|T|} (Π_{i∈S} λ_i)(Π_{j∈T} λ_j) A(Σ_{j∈T} a_j − Σ_{i∈S} a_i).

At `a i = log p i` the vertices are the **squarefree divisors** of `Π p i` and the lags are the
logarithms of their ratios: the whole incidence lattice of a squarefree modulus constrains the
charges of its primes at once, with weights the allocation may choose. `|s| = 1` is
`2λ A(t) ≤ (1+λ²) A(0)` (`two_mul_autoCorr_le`), `|s| = 2` the two-shift coupling law.

### The divisor-lattice Gram form and the blindness of the Möbius comb (fifteenth pass)

For one modulus `q` and any weighting `c` of its divisors, the comb `Σ_{d ∣ q} c d · F(· + log d)`
has nonnegative energy, so the **ratio-incidence matrix of a modulus is positive semidefinite**
(`divisor_gram_nonneg`): every minor is an unconditional inequality among the charges at the ratios
of divisors of a single modulus — one character, modulus one, no family average. On the *resonant*
direction (maximal correlation at every divisor ratio) the form collapses to
`(Σ_{d ∣ q} c d)² A(0)` (`divisor_gram_eq_of_resonant`), hence vanishes for the **Möbius row** of
any `q ≠ 1` (`moebius_divisor_gram_eq_zero_of_resonant`) while the trivial row gives the maximum
`τ(q)² A(0)`. So on the divisor lattice of one modulus the Möbius row is exactly the weight that
annihilates the resonant mode — the mode the eighth and ninth passes identify as the hard one.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure
- [x] 1 → 2 fully-proven: resolvent identity of the geometric train plus the two-step square
- [x] 2 → 3 formalized:
      `GaloisForLFunctions.ArithmeticIncidencePositivity.PrimeTowerEulerEnvelope`, wired into the
      programme umbrella, `lake --old env lean` clean, no `sorry`/axiom
- [ ] 3 → 4 publication-ready

## Approach

For a spacing `L > 0` and `z ∈ (0,1)` let `S_N = Σ_{k ≤ N} z^k F(· + kL)` be the geometric train.
It is a truncated resolvent: `S_N − z S_N(· + L) = F − G`, `G = z^{N+1} F(· + (N+1)L)`
(`geoTrain_resolvent`). Substituting this split into the three pairings `A(0)`, `A(L)` and the lag
charge gives, with `X = A_S(0)`, `Y = A_S(L)`, `Y₂ = A_S(2L)` and tail errors supported on `G`:

    A(0)              = (1+z²) X − 2z Y + e_A
    A(L)              = (1+z²) Y − z (X + Y₂) + e_B
    Σ_{m≥1} z^m A(mL) = z Y − z² X + z e₁

The coefficient of `Y` in `z² A(0) + z A(L) − (1 − z²) Σ z^m A(mL)` cancels identically, leaving

    z² A(0) + z A(L) − (1 − z²) Σ_{m≥1} z^m A(mL) = z² (X − Y₂) + (errors),

and `X ≥ Y₂` is `|A_S(2L)| ≤ A_S(0)` for the train. The tail errors are pairings of translate
combinations, bounded by the product of the coefficient masses times `A(0)`, hence `O(z^N)`; letting
`N → ∞` removes them. All analysis used is the bilinearity and translation invariance of `∫ A B` on
continuous compactly supported functions; no Fourier transform, no Herglotz representation, no PNT.

## Lean

Module `formal/GaloisForLFunctions/ArithmeticIncidencePositivity/PrimeTowerEulerEnvelope.lean`.

- `one_sub_sq_mul_geoLagCharge_le` — `(1 − z²) Σ_{m≥1} z^m A(mL) ≤ z² A(0) + z A(L)`
- `geoLagCharge_le_envelope_sub_discount` — the envelope-minus-discount form
- `sub_one_mul_towerCharge_le` — the prime tower law `(p−1) C_p(F) ≤ log p (A(0) + √p A(log p))`
- `towerCharge`, `towerCharge_eq_log_mul_geoLagCharge`, `vonMangoldtAtom_prime_pow` — the tower
  atoms are geometric with ratio `p^{−1/2}`
- `primeSide`, `primeSide_eq_tsum_towerCharge` — the prime side is the sum of the tower charges
- `primeSide_le_sum_primes` — the prime-only bound on the whole prime side
- `towerCharge_le_div`, `towerCharge_eq_zero_of_horizon`, `vonMangoldtAtom_eq_zero_of_not_isPrimePow`,
  `primeSide_summable`
- `one_div_le_abs_log_sub_log`, `abs_sum_prime_autoCorr_le_of_decorrelated` — the decorrelation
  criterion
- `archBandEnergy`, `archBandEnergy_ge_of_decorrelated`, `continuous_autoCorr_of_lipschitz` — the
  archimedean floor of a decorrelating test
- `weightedDoubleDifference`, `two_shift_coupling`, `autoCorr_coupling_identity`,
  `autoCorr_coupling_le` — the coupling graph of two shifts with its sharp edge weight
- `sq_sum_autoCorr_le` — the shift-Gram law for any finite shift family
- `sq_sum_prime_autoCorr_le`, `primeCorrelationForm_eq`, `ratioOffDiagonal`,
  `abs_sum_prime_autoCorr_le_of_ratioOffDiagonal_nonpos`, `autoCorr_log_sub_log`
- infrastructure: `translateComb`, `abs_pair_comb_le` (Gram bound), `geoTrain`, `geoTail`,
  `geoTrain_resolvent`, `abs_autoCorr_le_autoCorr_zero`, `autoCorr_eq_zero_of_support`,
  `geoLagCharge_eq_sum`

Related corpus infrastructure not reused (right-translate convention differs):
`RHTower.integral_translateComb_autocorr` in `WeilPositivityMajorantRigidity`.

## Next

- The visibility witness: the resonant train of disjoint bumps at spacing `L` attains the Euler
  envelope in the limit, so the constant `z/(1−z)` is sharp and the discount is the whole content.
- Feed the law into the ledger: bound `Σ_n oddStripCost_n − Σ_n evenStripGain_n` over all prime
  powers by the prime-only functional it dominates.

## Modules

- `ArithmeticIncidencePositivity/TranslatePairingCalculus.lean` — the reusable pairing calculus
  (`testPairing`, `ContCompact`, Gram expansion and bound, `geoTrain`, `geoTail`,
  `geoTrain_resolvent`, Cauchy–Schwarz, `abs_autoCorr_le_autoCorr_zero`)
- `ArithmeticIncidencePositivity/DivisorLatticeGramPositivity.lean` — the divisor-lattice Gram form
  (`divisorComb`, `divisor_gram_nonneg`, `divisor_gram_eq_of_resonant`,
  `moebius_divisor_gram_eq_zero_of_resonant`)
- `ArithmeticIncidencePositivity/SquarefreeIncidencePositivity.lean` — the subset-lattice law
  (`squarefreeComb`, `squarefree_incidence_nonneg`, `two_mul_autoCorr_le`)
- `ArithmeticIncidencePositivity/ResonantTrainWitness.lean` — the witness
  (`resonantTrain`, `autoCorr_resonantTrain`, `geoLagCharge_resonantTrain_ge`)
- `ArithmeticIncidencePositivity/BiTowerIncidenceLaw.lean` — the two-tower law
  (`trainLagCharge`, `one_sub_sq_mul_tsum_trainLagCharge_le`,
  `tsum_trainLagCharge_le_envelope_sub_discount`)
- `ArithmeticIncidencePositivity/PrimeTowerEulerEnvelope.lean` — the laws
- `ArithmeticIncidencePositivity/PrimeTowerLedgerReduction.lean` — the ledger form
  (`autoCorr_eq_zero_of_support_le`, `primeSideCharge_eq_sum_relevantShifts`,
  `evenStripGain_sub_oddStripCost_eq`, `sum_evenStripGain_sub_sum_oddStripCost`,
  `fullZeroForm_ge_primeOnlyLedger`, `towerCharge_le_firstAtomStrip`,
  `towerCharge_le_evenStripGain`)

## Log

- 2026-10-22 — created, proved and formalized in one pass
- 2026-10-22 — second pass: the prime side reindexed by towers, prime-only bound formalized
  (`primeSide_le_sum_primes`); the proper-prime-power sector is `O(B) · A(0)`
- 2026-10-22 — third pass: shift-Gram law, the prime-shift correlation form and its diagonal split,
  and the sufficiency of a nonpositive ratio off-diagonal
- 2026-10-22 — fourth pass: the incidence ledger with the prime powers eliminated
  (`fullZeroForm_ge_primeOnlyLedger`), wired into the programme umbrella
- 2026-10-22 — fifth pass: the pairing calculus split into a reusable module; the bi-tower law and
  the nonnegativity of the pair incidence energy
- 2026-10-22 — sixth pass: the Gram closure at one prime (`towerRatioPairs_eq`, `towerRatioPairs_le`):
  the same-prime off-diagonal is a tower charge, hence a bounded sector
- 2026-10-22 — seventh pass: the tower is paid by the even strip gain of its first atom
  (`towerCharge_le_evenStripGain`): the ledger's allocation reduces to the primes
- 2026-10-22 — eighth pass: the decorrelation criterion
  (`abs_sum_prime_autoCorr_le_of_decorrelated`): a test resolving the scale `1/N` has an
  archimedean-size prime side
- 2026-10-22 — ninth pass: the archimedean floor of a decorrelating test
  (`archBandEnergy_ge_of_decorrelated`): both sides are `≍ A(0) log N` in that regime
- 2026-10-22 — tenth and eleventh passes: the two-shift coupling law with tunable weights and its
  sharp one-parameter form (edge weight `≤ ½`, payers the product and ratio shifts)
- 2026-10-22 — twelfth pass: the resonant-train witness; the Euler envelope is attained by trains on
  a multiplicative progression
- 2026-10-22 — thirteenth pass: the coupling weight `½` is sharp
  (`exists_resonantTrain_coupling_fails`)
- 2026-10-22 — fourteenth pass: the squarefree incidence positivity over the subset lattice, with
  the Finset-indexed Gram expansion added to the calculus
- 2026-10-22 — fifteenth pass: the divisor-lattice Gram positivity of a modulus and the blindness of
  its Möbius row on the resonant direction
