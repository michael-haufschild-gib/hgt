# THIM WP5 loop: the parity pair (goal: 100 significant contributions)

- **ID:** thim-wp5-parity-1020
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) per contribution; CONJECTURE for open items
- **Source:** docs/reports/work-packages.md §WP5; THIM README §5 research topic 1 (mechanism 5)
- **Statement:** Construct two weights with identical divisor-sum, Ramanujan and pronic Gram data and
  opposite trans-horizon energy growth, or prove no such pair exists and name the additive observable
  that separates them.

## Contract (from WP5)
A contribution counts when it (1) constructs a pair with both proofs, or (2) proves impossibility with
the separating observable and its exact loss, or (3) bounds the complete signed trans-horizon energy at
one fixed `ε < 1/2` with all terms retained, or (4) bounds the odd-sector low-prime diagonal potential
independently and moves the aperture unit in WP1/WP3; AND (5) names the step `k ↦ k+1`, `N ↦ N+1` or
`k ↦ pk` where the arithmetic of `ℕ` enters. Not counted: small-horizon thresholds, Buchstab band signs,
second-order crossover terms, schedule classifications.

## Precise data notions used
For a weight `c` with absolutely convergent Ramanujan coefficients `w_c(e) = Σ_{e|d} c(d)/d`:
- **Ramanujan data:** the amplitude spectrum `|w_c(e)|`.
- **Divisor-sum data:** the complete-period (Haar) translation statistics of the divisor-sum signal
  `c * 1`: mean `w_c(1)` and lag covariances `Σ_e c_e(h) w_c(e)²` at every additive lag `h`.
- **Pronic Gram data:** the pronic Gram kernel `𝒢(e₁,e₂)` with the weighted entries
  `|w(e₁) w(e₂) 𝒢(e₁,e₂)|`, in particular every mode mass `w(e)² 𝒢(e,e)`.
These are exactly the data invariant under the **parity involution** `w ↦ λ·w` on moduli (for
squarefree support `λ(e) = μ(e)`): translation statistics are diagonal in the Selberg coordinates, so
they see `w(e)²` only. Signed Ramanujan coefficients pin an admissible weight (Möbius inversion over
multiples), so with signed data no pair exists trivially; the parity is the real content.
- **Trans-horizon energy:** the pronic receiver energy `E_T(c) = Σ_{n≤T} A_c(n)²/(n(n+1))`,
  `A_c(n) = Σ_{j≤n} ((c*1)(j) − w_c(1))` (equivalent up to `×2 + 1/2` to the interior energy).

## Conjecture queue
1. Parity twin `c'_ε` of `c_ε = μ(d)d^{-ε}`: Ramanujan coefficients `|w_ε(e)|`, nonnegative row,
   `c'_ε(d) ≥ κ_ε μ²(d) d^{-ε}`; `E_T(c'_ε) → ∞` for `ε ≤ 1/2`; with the corpus bound
   `exists_pmPowerDampedDivisorDiscreteEnergy_budget_of_half_le` this is the pair at `ε = 1/2`.
2. Exact loss: `E(λw) − E(w) = 4 X` with `X` the cross-parity pronic pairing; at `ε < 1/2` the receiver
   bound ⇔ `X_T = E⁺_T/2 + O(1)` against `E⁺_T ≍ T^{1−2ε}`.
3. Separating observable for the twin: dilation correlations `k ↦ pk` (edges `e | pe` flip sign).
4. Horizon-escape pair: sharp Möbius rows vs smooth rows with the same pointwise limits.

## Log
- 2026-10-20 — card created; README §5 and WP5 read; corpus searched (no parity-pair work; BVI
  `pmPronicVaughan_flip_energy_gap` is the generic polarization algebra only).

## Contribution ledger (append-only)
- **C1 · The parity pair at half damping** — `ParityTwinOfTheDampedMoebiusWeight`,
  `ParityPairAtHalfDamping`. Headline `parityPair_at_half_damping`: `c_{1/2}(d) = μ(d)d^{-1/2}` and
  its parity twin `c'_{1/2}` have Ramanujan coefficients `w(e)` and `μ(e)w(e)` (identical amplitudes,
  so identical mean, variance, every lag covariance `Σ c_e(h)w(e)²`, successor/primitive energies and
  pronic mode masses; `sq_weightRamanujanCoeff_parityTwin`), `c' ≥ 0`, and opposite receiver growth:
  `E_T(c_{1/2})` bounded (corpus Mellin bound, ζ(1+it) ≠ 0), `E_T(c'_{1/2}) → ∞`.
  Twin: `c'_ε(d) = (ρ_ε/U_ε) d μ²(d) ∏_{p|d} 1/(p^{1+ε}−2)` (`parityTwinWeight`), Ramanujan identity
  `hasSum_parityTwin_ramanujan` via the coprime recursion `U_e = (1+u_ε(p))U_{pe}` along `k ↦ pk`
  (`parityTwinCoprimeMass_prime`) and `u/(1+u) = 1/(p^{1+ε}−1)`; domination
  `c'_ε(d) ≥ (ρ_ε/U_ε)μ²(d)d^{-ε}` (`parityTwinWeight_ge`).
  Divergence `tendsto_weightPronicEnergy_parityTwin` for every `0 < ε ≤ 1/2`: counting multiples along
  `k ↦ k+1` (`sum_Icc_sum_divisors_eq_floor`) gives the drift `A_c(n) ≤ −nΣ_{n<d≤2n} c(d)/d` for any
  nonnegative weight (`weightCenteredPrefix_le_neg_drift`); squarefree density in `(n,2n]`
  (`squarefree_count_dyadic_ge`, ≥ n/8 for n ≥ 100) makes each cell `≥ c/n`.
  Separating observable: prime moduli, `W_{c'}(p) = −w_ε(p) > 0` (`weightRamanujanCoeff_parityTwin_prime`),
  the mean along the dilation `k ↦ pk`.
  New insight: ε = 1/2 is the first damping at which receiver boundedness depends on the parity of the
  moduli (above it every weight with |c(d)| ≤ d^{-ε} is absolutely bounded); for 0 < ε < 1/2 the twin
  always diverges, so a receiver bound at ε is *equivalent* to the existence of the parity pair at ε —
  mechanism 5 is the PM receiver itself, and its Type-II content is the cancellation between moduli of
  even and odd ω. Standard axioms (5 audited); both modules wired; lint shows no THIM error.
- **C2 · A parity pair at every damping: the character mod four** —
  `CharacterFourParityPairAtEveryDamping`. Headline `chiFour_parityPair` (every `0 < ε ≤ 1/2`):
  `c_χ(d) = χ₄(d)d^{-ε}` and the nonnegative `c_+(d) = (L_ε/O_ε)1_{odd}(d)d^{-ε}` have Ramanujan
  coefficients related by the twist `W_{c_+}(e) = χ₄(e)W_χ(e)` (`weightRamanujanCoeff_oddTwin`;
  `χ₄(e) = (−1)^{Ω₃(e)}` on odd e: parity of the prime factors ≡ 3 mod 4), hence identical amplitudes
  and translation data; `E_T(c_χ)` bounded, `E_T(c_+) → ∞`. Both proofs unconditional and elementary.
  General engine `exists_weightPronicEnergy_dampedSign_le`: **any sign pattern with bounded partial
  sums pays the receiver at every ε > 0**. Mechanism: hyperbola split at `D`
  (`abs_weightCenteredPrefix_dampedSign_le`: `|A(n)| ≤ 2BD + 4Bn(D+1)^{-1-ε}`) — short moduli
  absolutely, long moduli counted along the cofactor step `k ↦ k+1` as `Σ_k Σ_{D<d≤n/k} c(d)` and the
  tail by Abel summation against antitone `d^{-ε}`, `d^{-1-ε}` (`abs_sum_block_rpow_le`,
  `abs_tsum_tail_rpow_le`, reusing BVI `abs_sum_range_mul_antitone_le`); `D = ⌊n^{1/(2+ε)}⌋` gives
  `|A(n)| ≤ 6B n^{1/(2+ε)}` (`abs_weightCenteredPrefix_dampedSign_le_rpow`), exponent `< 1/2`.
  Divergence through the generalized `tendsto_weightPronicEnergy_of_drift` (any nonnegative weight
  with dyadic drift `K(2n)^{-ε}`, `ε ≤ 1/2`), odd moduli `2j+1 ∈ (n,2n]` (`oddTwin_drift_ge`).
  `L_ε > 0` from the head `1 − 3^{-ε}/3` and an Abel tail `≤ 2·5^{-1-ε}` (`chiFourDampedMass_pos`).
  New insight: mechanism 5 exists unconditionally throughout the hard regime `ε < 1/2`: the
  additive period-four cancellation of `χ₄` (a single-modulus additive input) is exactly what the
  parity-blind data miss and what pays the receiver; for `μ` the same engine needs partial sums
  `≪ x^β` with `β < ε` (pointwise hyperbola loses `1/2` against the Mellin threshold `β − 1/2`).
  Standard axioms (4 audited); wired.
- **C3 · The parity rows at every horizon (AIP open problem 5)** —
  `CharacterFourParityRowsAtEveryHorizon`. Headline `chiFour_parityRows` (every `0 < ε ≤ 1/2`): the
  horizon-`N` row `c_N = χ₄(d)d^{-ε}1_{d≤N}` and its twin `c'_N = scaledSelbergRow N c_N σ`
  (`σ` = sign extension of χ₄) have, at **every** horizon, Selberg coordinates equal up to sign
  (`sq_selbergMultiplesCoord_chiFourTwinRow` ⇒ every complete-period quadratic form agrees) and
  identical two-point translated moments (`translatedMoment_two_chiFourTwinRow`, via BVI two-point
  blindness), are separated by a cubic translated moment at every `N ≥ 3`
  (`exists_translatedMoment_three_chiFourTwinRow_ne`: zero-product triple `ζ₃ζ₃ζ₃ = 1`,
  `Y(3)³(1−χ₄(3)³) = 2Y(3)³ ≠ 0`, `Y_N(3) = −3^{-1-ε}L_{N/3}`, `L_X ∈ [1−2^{-ε}, 1+2^{-ε}]`), and have
  opposite growth of the pronic discrepancy energy `horizonPronicEnergy`: uniformly bounded for `c_N`
  (`horizonPronicEnergy_chiFourRow_le`, the C2 engine with explicit constant, truncated χ₄ keeps
  partial sums in `{0,1}`), → ∞ with `N` for `c'_N`
  (`eventually_lt_horizonPronicEnergy_chiFourTwinRow`).
  Mechanism of the divergence: the twin rows converge divisor by divisor to the positive odd weight
  (`tendsto_chiFourTwinRow`, dominated convergence over the Möbius cofactor `m` in the level-`N`
  Ramanujan inversion; limit identified through `(Σ μ(m)o(m))·O_ε = 1`,
  `tsum_moebius_mul_oddW_mul_oddDampedMass`, from the corpus multiples inversion), the receiver at a
  fixed cutoff is continuous (`tendsto_weightPronicEnergy_of_pointwise`), and the limit's drift
  diverges (C2).
  New insight: the additive observable separating the parity rows is the **cubic translated moment**
  at the single modulus 3 (degree 3, the least degree at which an odd-order sign is visible); all
  degree-2 (translation) data, all Ramanujan amplitudes and all complete-period forms coincide at every
  horizon, yet the pronic discrepancy energy separates bounded from divergent. The growth of the twins
  lives below the horizon (cells `M ≤ N`), where the twin rows reproduce the drift of `c_+`.
  Standard axioms (2 audited); wired.
- **C4 · Local Euler factors cannot separate: the pronic dilation contraction** —
  `LocalEulerFactorsAndPronicDilationContraction`. Exact mechanism of the step `k ↦ pk`: the pronic
  weight contracts the dilation `n ↦ ⌊n/p⌋` by exactly `p^{-1/2}` (`sum_pronic_dilate_le`,
  `pronicNorm_dilate_le`; blocks `Σ_{r<p} 1/((pk+r)(pk+r+1)) = 1/(pk(k+1))`). A local factor
  `c ⋆ (δ₁ − aδ_p)` (`localFactorWeight`) acts on the receiver prefix as
  `A'(n) = A(n) − aA(⌊n/p⌋) + am{n/p}` (`weightCenteredPrefix_localFactorWeight`, via
  `S_{c'}(n) = S_c(n) − aS_c(⌊n/p⌋)`), so `‖A'‖ ≤ (1+|a|p^{-1/2})‖A‖ + |am|` for every `a`
  (`pronicNorm_localFactor_le`) and `(1−|a|p^{-1/2})‖A‖ ≤ ‖A'‖ + |am|` (`pronicNorm_le_of_localFactor`).
  Headline `bounded_weightPronicEnergy_localFactor_iff`: **for |a| < √p (the zero of 1 − ap^{-s} left
  of the critical line) the receiver growth class is invariant.** Sharp (`criticalLine_sharpness`): the
  geometric weight `g(p^k) = p^{k/2}` has unbounded energy (window drift `√(n/p)` on `(n, pn]`) while
  `g ⋆ (δ₁ − √pδ_p) = δ₁` has zero energy. Parity flips: for `c(pd) = xc(d)`,
  `c^{(p)} ⋆ (δ₁ + xδ_p) = c ⋆ (δ₁ − xδ_p)` (`localFactorWeight_primeParityFlip`), so one flip (hence
  finitely many) never separates when `|x| < √p` (`bounded_weightPronicEnergy_primeParityFlip_iff`);
  applied to `χ₄d^{-ε}` at every prime (`bounded_weightPronicEnergy_chiFour_flip_iff`). Pronic norm
  toolkit: Minkowski (`pronicNorm_add_le`), scaling, bounded functions (`sum_Icc_pronic_eq`).
  New insight: the receiver is a **local critical-line detector** — Euler factors (zeros) never hurt;
  inverse factors (poles at Re s = log_p|a|) hurt iff the pole is at Re s ≥ 1/2. A parity pair is a
  global phenomenon needing infinitely many flipped primes (the twins flip a positive density of
  primes and acquire the pole of ζ at s = 1 − ε, right of the line iff ε ≤ 1/2 — exactly C1's
  threshold). Selectivity: for `ζ(s−a)ζ(s+a)`, `a < 1/2`, every local factor is left of the line, so no
  finite set of primes sees the off-line zeros. The Fermi cell response is the sieve receiver under the
  factor `1 − 2·2^{-s}` (`a = 2 > √2`): forward control only. Standard axioms (4 audited); wired.
- **C5 · Cubic moments pin the parity of odd rows (no pair survives degree three)** —
  `CubicMomentsPinTheParityOfOddRows`. `sign_cube_eq_one_of_translatedMoment_three`: if a sign twist
  `scaledSelbergRow N c σ` has the cubic translated moments of `c` and `Y_N(q) ≠ 0` at odd `q`, then
  `σ(q)³ = 1` (zero-product triple `ζ_qζ_qζ_q^{q−2} = 1`, uniform for odd `q ≥ 1`). Headline
  `scaledSelbergRow_eq_of_translatedMoment_three`: for rows supported on the odd moduli (`Y_N = 0` at
  even, `≠ 0` at odd `q`), equal cubic data ⇒ the twist is the row on `[1,N]` (BVI Ramanujan inversion
  `ramanujan_inverse_selbergCoords_eq`). Instance `chiFourRow_eq_of_cubic_moments` (all `N`, every
  `σ`). Impossibility with the separating observable named: the parity rows of C3 agree at degree 2
  and differ at degree 3; at degree 3 no sign-twisted pair of the character rows exists, loss zero.
  The additive step is the translation `k ↦ k + v` read at three points. Standard axioms (2); wired.
- **C6 · The even flip is the Fermi transform of the even part** —
  `EvenFlipIsTheFermiTransformOfTheEvenPart`. `translatedMoment_evenFlipRow`: for squarefree-supported
  rows the even flip `c^♭ = scaledSelbergRow N c ε₂` (`ε₂ = −1` on even moduli) has the translated
  moments of `c` at **every degree and shift** (zero-product tuples carry an even number of 2·odd
  orders: raise `Πζ_i = 1` to the odd `M = Π oddpart(ord ζ_i)`; `evenSign_eq_pow`). Row identity
  `evenFlipRow_eq` (four-free rows on `[1,N]`): `c^♭ = c + c_e ⋆ (δ₁ − 2δ₂)`, `c_e(d) = 1_odd(d)c(2d)`,
  i.e. `c^♭(d) = c(d) + c(2d)` (d odd), `−c(d)` (d even) — the Fermi cell factor `1 − 2·2^{-s}`.
  `pronicNorm_evenFlipRow_sub_le`: `|‖A_{c^♭}‖ − ‖A_c‖| ≤ (1+√2)‖A_{c_e}‖ + 2|m_e|` (C4 forward, mean
  unchanged); `bounded_horizonPronicEnergy_evenFlipRow_iff`: with uniformly paid even parts the flip
  preserves uniform boundedness.
  New insight: the unique sign twist of a squarefree row that no additive observable of any degree can
  see is a translation by the odd part of the period, and on the receiver it is the **Fermi transform
  of the even part** — THIM's Fermi–Nyman cells are exactly the moment-invisible parity. Its loss is
  controlled by a receiver of the same kind (the even part), never by a new mechanism. Standard axioms
  (4 audited); wired.
- **C7 · Cubic moments pin squarefree rows up to the even flip (the PM receiver rows)** —
  `CubicMomentsPinSquarefreeRowsUpToTheEvenFlip`. `sign_two_mul_eq_of_translatedMoment_three`: at an
  even squarefree modulus `2q'` the zero-product triple `η^{q'}·η²·η^{q'−2} = 1` (η primitive of order
  `2q'`; orders `2, q', 2q'`) gives `σ(2)σ(q')σ(2q') = 1`. Headline
  `scaledSelbergRow_eq_or_evenFlip_of_translatedMoment_three`: if the coordinates are nonzero exactly at
  squarefree moduli, any sign twist with the row's cubic translated moments is the row or its even flip
  on `[1,N]`. Instance `pmCofactor_twist_eq_or_evenFlip`: every PM cofactor row (coordinates
  `w_ε(e) = ρ_εμ(e)/D_ε(e)`, `selbergMultiplesCoord_pmCofactor_ne`) at every level `Q`.
  Combined with C6: **cubic additive data determine the PM receiver rows' receiver up to the Fermi
  receiver of the even part** — impossibility of a cubic-matched parity pair except through the prime
  2, with exact loss `(1+√2)‖A_{c_e}‖ + 2|m_e|`. The parity of a PM row is a cubic additive observable;
  the only degree-free residue is local at 2. Standard axioms (2 audited); wired.
- **C8 · Parity pairs of every real character, and the parity barrier** —
  `RealCharacterParityPairsAndTheParityBarrier`. For every nontrivial `χ : MulChar (ZMod q) ℤ` (real
  Dirichlet character): partial sums `≤ q` (`abs_sum_range_charSign_le`, period sum zero via
  `MulChar.sum_eq_zero_of_ne_one`), `L(1+ε,χ) ≠ 0` (`charDampedMass_ne_zero`, Mathlib nonvanishing on
  Re s > 1), twin `c_+ = (|L|/O)1_{(d,q)=1}d^{-ε}` with identical Ramanujan amplitudes
  (`abs_weightRamanujanCoeff_charTwin`; twist = parity of inert prime factors), drift on the residues
  `1+qj ∈ (n,2n]` (`charTwin_drift_ge`). Headline `char_parityPair`: a parity pair at every
  `0 < ε ≤ 1/2` for every real non-principal character.
  **`parity_barrier`**: at every `0 < ε ≤ 1/2` there is no function `F` of the Ramanujan amplitudes with
  `E_T(c) ≤ F(|W_c|)` for all weights `|c(d)| ≤ Kd^{-ε}` — the formal parity barrier of the receiver
  (mechanism 5): any receiver bound below half damping must read the signs of the coefficients, i.e.
  first-order data at prime moduli (`k ↦ pk`) or cubic translated moments (`k ↦ k+v`, C5/C7).
  Standard axioms (2 audited); wired.
- **C8 amendment** — `parity_barrier` restated in its faithful form: for `0 < ε ≤ 1/2` and every
  `K > 0` there is no `Φ` with `ReceiverBounded c ↔ Φ(|W_c|)` on `DampedClass K ε` (the rescaled χ₄
  pair lies in the class). The first version ("no `F` with `E_T ≤ F(|W_c|)`") followed from one
  divergent weight alone and did not use the pair. Smul laws for prefix, energy, coefficients.
- **C9 · Half damping is the exact threshold of the parity pair** —
  `HalfDampingIsTheExactThresholdOfTheParityPair`. Exact split along `k ↦ k+1`
  (`weightCenteredPrefix_eq_split`): `A_c(n) = Σ_{d≤n} c(d)(⌊n/d⌋ − n/d) − nΣ_{d>n} c(d)/d`;
  universal bound `|A_c(n)| ≤ K C_ε n^{1−ε}`, `C_ε = 1 + 1/(1−ε) + 1/ε`
  (`abs_weightCenteredPrefix_le_of_dampedClass`; corpus head `RHTower.sum_rpow_neg_head_le`, tail
  `HTGeometry.tsum_shift_rpow_le`), cells `≤ (KC_ε)² n^{-2ε}`, maximal growth
  `E_T ≤ (KC_ε)² Σ_{n≤T} n^{-2ε}` on the whole class (`weightPronicEnergy_le_of_dampedClass`).
  Above 1/2: one constant bounds every receiver in `𝒞(K,ε)` (`exists_uniform_weightPronicEnergy_bound`).
  Extremality (`char_parityPair_extremal`): for every real non-principal χ and `0 < ε ≤ 1/2`, the
  twin's energy is pinched between `a Σ_{8q≤n≤T} n^{-2ε}` and `b Σ_{n≤T} n^{-2ε}`
  (`weightCell_ge_rpow_of_drift`: drift ⇒ cell `≥ (K²/4)n^{-2ε}`), the character's is bounded: the
  pair realizes both extremes of the class. Headline `receiverBounded_amplitudeInvariant_iff`: for
  every `K > 0`, `ε > 0`, receiver boundedness on `𝒞(K,ε)` is a function of the Ramanujan amplitudes
  **iff `ε > 1/2`**. Sharp boundary of mechanism 5; the whole difference lives in the tail
  `nΣ_{d>n}c(d)/d` (trans-horizon moduli) and the head drift, both of order `n^{1−ε}`.
  Standard axioms (3 audited); wired.
- **C10 · Dyadic masses govern positive receivers** — `DyadicMassesGovernPositiveReceivers`.
  Headline `bounded_weightPronicEnergy_iff_summable_dyadicMass`: a nonnegative weight has bounded
  receiver **iff** `Σ_k M_k²/2^k < ∞`, `M_k = Σ_{2^k<d≤2^{k+1}} c(d)` (`dyadicMass`). Two-sided with
  explicit constants: lower `Σ_{k<K} M_{k+1}²/2^{k+1} ≤ 16 E_{2^K}` (`sum_dyadicMass_sq_le_weightPronicEnergy`:
  the trans-horizon block `(2^{k+1},2^{k+2}]` drifts every prefix `n ≤ 2^{k+1}` through the C4 window
  drift), upper `E_T ≤ 12c(1)² + 100Σ M_k²/2^k` (`weightPronicEnergy_le_dyadicMass`): finite support
  `−(C(n)+n·tail(n)) ≤ A ≤ 0` (`sq_weightCenteredPrefix_le_of_support`), block bounds
  `C ≤ c(1)+Σ_{j≤k}M_j`, `tail ≤ Σ_{j≥k}M_j2^{-j}`, two discrete Hardy inequalities with geometric
  weights (`sum_sq_partialSum_div_two_pow_le`, `sum_two_pow_mul_sq_tail_le`, constant 12 via
  Sedrakyan/Cauchy–Schwarz with weights (3/2)^j, (2/3)^j), then truncation `d ≤ 2^J` and the C3
  pointwise-continuity of the receiver at fixed cutoff. `weightRamanujanCoeff_nonneg`: on nonnegative
  weights amplitudes = signed coefficients.
  Insight: without signs there is no cancellation — the receiver of a positive weight is exactly the
  `ℓ²(2^{-k})` norm of its dyadic masses (steps `k ↦ k+1` in the floor sum and `k ↦ 2k` in the
  blocks). Every parity pair has a sign-changing member, and its positive member diverges exactly
  when `M_k ≠ o(2^{k/2})` in `ℓ²`; for densities `c ≍ d^{-ε}`, `M_k ≍ 2^{k(1−ε)}` — the threshold 1/2
  is the square-root law of the dyadic masses. Standard axioms (2 audited); wired.
- **C11 · Critical Wiener convolutions preserve the receiver; the Liouville parity pair** —
  `CriticalWienerConvolutionsPreserveTheReceiver`. Exact convolution law along the dilation `k ↦ qk`
  (`weightCenteredPrefix_dirichletConv`, via corpus `RHTower.floorTransform_comp`):
  `A_{g⋆c}(n) = Σ_{q≤n} g(q)A_c(⌊n/q⌋) + m_c A_g(n)` at mean `m_g m_c` (`hasSum_dirichletConv_div`,
  fiberwise regrouping of the product family). Norm law (`pronicNorm_dirichletConv_le`):
  `‖A_{g⋆c}‖ ≤ G‖A_c‖ + (√2+1)G|m_c|`, `G = Σ|g(q)|q^{-1/2}`; sawtooth `‖⌊n/q⌋ − n/q‖ ≤ √2 q^{-1/2}`
  (`pronicNorm_sawtooth_le`), sawtooth expansion of critical kernels
  (`pronicNorm_weightCenteredPrefix_le_critical`), finite Minkowski. Headline
  `receiverBounded_dirichletConv`: **bounded receivers are preserved by convolution with every kernel of
  the critical Wiener algebra** (`CriticalWiener g`: Dirichlet series absolutely convergent on
  Re s ≥ 1/2); C4's local factors are its finite kernels. Application: `λd^{-ε} = 1_□d^{-ε} ⋆ μd^{-ε}`
  (`dampedLiouville_eq_dirichletConv`, corpus `liouvilleR_eq_dirichletConv`), square kernel critical
  with `G = ζ(1+2ε)` (`criticalWiener_dampedSquare`), so `receiverBounded_liouville_of_moebius` at every
  ε > 0. **Liouville parity pair** (`liouville_parityPair_of_moebius`, unconditional instance
  `liouville_parityPair_at_half_damping`): `λ(d)d^{-1/2}` (bounded) and the smooth power `κd^{-1/2}`
  (`liouvilleTwin`, κ = m_λ/ζ(3/2), divergent) have equal Ramanujan amplitudes `|m_λ|e^{-3/2}` —
  λ completely multiplicative of modulus one. The parity of Ω is the entire difference between the
  Liouville weight and the constant weight.
  Insight: the twist kernels of all our pairs lie outside the critical Wiener algebra exactly when
  ε ≤ 1/2 (for χ: `g(p) = 2p^{-ε}` on inert p, `Σ_p p^{-1/2-ε} = ∞`); the algebra is the class of
  receiver-preserving symmetries, the parity twist is the smallest step outside it.
  Standard axioms (3 audited); wired.
- **C12 · The first pronic moment is the von Mangoldt pairing; it separates every real-character
  pair** — `FirstPronicMomentIsTheVonMangoldtPairing`. Sawtooth superposition
  `A_c(n) = Σ_d c(d)ψ_d(n)`, `ψ_d(n) = ⌊n/d⌋ − n/d` (`weightCenteredPrefix_eq_tsum_sawtooth`).
  Summation by parts along `n ↦ n+1` (`ψ_d(n) − ψ_d(n−1) = 1_{d|n} − 1/d`):
  `Σ_{n≤N} ψ_d(n)/(n(n+1)) = (H_{⌊N/d⌋} − H_N)/d − ψ_d(N)/(N+1)` (`sum_range_sawtooth_div_pronic`),
  harmonic numbers along `k ↦ dk` give `−log d` (`tendsto_harmonic_div_sub_harmonic`, Mathlib
  `Real.tendsto_harmonic_sub_log`), so `Σ_n ψ_d(n)/(n(n+1)) = −log d/d` (`hasSum_sawtooth_div_pronic`).
  Fubini on ℕ×ℕ (`hasSum_weightCenteredPrefix_div_pronic`) and fibrewise regrouping by `d = ek`
  (`tsum_log_eq_tsum_vonMangoldt`, Mathlib `vonMangoldt_sum`) give, on the damped class
  (`hasSum_firstPronicMoment`): **`Σ_n A_c(n)/(n(n+1)) = −Σ_d c(d)log d/d = −Σ_e Λ(e)W_c(e)`** — the
  first pronic moment of the receiver (equivalently the logarithmic mean `Σ_j ((c*1)(j) − m)/j`) is a
  signed first-order observable supported on prime powers (weight-level form of the BVI mode law
  `Σ_M P_q(M)/(M(M+1)) = −Λ(q)`). Separation (`firstPronicMoment_char_sub_twin`): for every real
  non-principal χ and every ε > 0, `M(c_χ) − M(c_+) = Σ_e Λ(e)e^{-1-ε}(|L|χ(e)² − Lχ(e)) > 0`, every
  term ≥ 0, positive at a prime with χ(p) = −1 if L > 0 (`exists_prime_charSign_eq_neg_one`, descent
  through prime factorizations) and at p² for p ∤ q if L < 0 (`exists_prime_charSign_sq_eq_one`).
  This is the separating additive observable with its exact loss: the Λ-weighted mass of the prime
  powers the twist flips, `2|L|Σ_{χ(e) = −sgn L} Λ(e)e^{-1-ε}`. Standard axioms (2 audited); wired.
- **C13 · The first pronic moment orders every pair with a positive member** —
  `FirstPronicMomentOrdersPositivePairs`. Damped Ramanujan bound `|W_c(e)| ≤ KZ e^{-1-ε}`
  (`abs_weightRamanujanCoeff_le_of_dampedClass`), summable Λ-pairings. Headline
  `firstPronicMoment_sub_of_positive_twin`: if `c₊ ≥ 0` has the amplitudes of `c` (both damped), then
  `M(c) − M(c₊) = Σ_e Λ(e)(|W_c(e)| − W_c(e)) ≥ 0`, **strict iff `W_c < 0` at some prime power** —
  so every parity pair with a positive member is ordered by the first pronic moment, and a pair the
  first moment cannot separate must have `W_c ≥ 0` on all prime powers: its parity lives entirely on
  composite moduli (sharp structural restriction on first-moment-blind pairs). Instance
  `firstPronicMoment_liouvilleTwin_lt` (every ε > 0; `W_λ(2) = −2^{-1-ε}m_λ < 0`); C12 is the
  character instance. Standard axioms (2 audited); wired.
- **C14 · A parity pair the first pronic moment cannot see** —
  `FirstMomentBlindParityPairOfTheNegatedMoebiusWeight`. `c_b = 2ρ_εδ₁ − μ(d)d^{-ε}`
  (`negatedMoebiusWeight`): `W_{c_b}(e) = 2ρ[e=1] − w_ε(e)` (`weightRamanujanCoeff_negatedMoebius`),
  mean ρ_ε, and `A_{c_b} = −A_{μd^{-ε}}` (`weightCenteredPrefix_negatedMoebius`): the Möbius receiver.
  Headline `firstMomentBlind_parityPair` (0 < ε ≤ 1/2), against the PM twin `c'_ε`: equal amplitudes
  at every modulus; **equal coefficients at every prime power** (`μ(p) = −1`, `w_ε(p^k) = 0` for
  k ≥ 2; `weightRamanujanCoeff_negatedMoebius_eq_twin`); **equal first pronic moments** (first-moment
  law on both sides; twin in the damped class at exponent ε/2, `parityTwinWeight_mem_dampedClass`);
  opposite signs at every `pq` (`W_{c_b}(pq) < 0 < W_{c'}(pq)`); twin divergent. Unconditional at
  half damping (`receiverBounded_negatedMoebius_half`). Realises the equality case of C13: the
  parity of this pair lives entirely on composite moduli; the first separating observable is
  supported on ω(e) ≥ 2 (Λ⋆Λ weight). Standard axioms (2 audited); wired.
- **C15 · The second von Mangoldt moment separates the first-moment-blind pair** —
  `SecondVonMangoldtMomentSeparatesTheBlindPair`. General divisor pairing (`tsum_divisorPairing`): for
  `a ≥ 0` with `Σ_{e|d} a(e) = g(d)`, `Σ_d c(d)g(d)/d = Σ_e a(e)W_c(e)` (fibrewise regrouping). Second
  von Mangoldt function `Λ₂ = Λ·log + Λ⋆Λ` (`secondVonMangoldt`), `Σ_{e|d}Λ₂(e) = log²d`
  (`sum_divisors_secondVonMangoldt`, via `Λ⋆1 = log` and `log(ab) = log a + log b`), `0 ≤ Λ₂ ≤ log²`,
  `Λ₂(6) > 0`. Logarithmic moment law (`firstPronicMoment_logWeight`): on the damped class
  `M(c·log) = −Σ_d c(d)log²d/d = −Σ_e Λ₂(e)W_c(e)` — the first pronic moment of the log-weight is an
  additive observable reading the moduli with ω ≤ 2. Headline `logMoment_separates_firstMomentBlind`
  (every ε > 0): `M(c_b·log) − M(c'·log) = Σ_e Λ₂(e)ρ_ε(μ(e)+μ(e)²)/D_ε(e) > 0` — termwise ≥ 0,
  supported on squarefree `pq` (the prime-power terms vanish since μ + μ² = 0 there), positive at
  `e = 6`. Exact loss = `2ρ_εΣ_{e=pq}Λ₂(e)/D_ε(e)`. Hierarchy: the k-th logarithmic moment reads
  `Λ_k`, supported on ω ≤ k; a pair blind to the first k moments has its parity on ω > k.
  Standard axioms (2 audited); wired.
- **C16 · The Möbius and Liouville receivers are equivalent** —
  `MoebiusAndLiouvilleReceiversAreEquivalent`. Square-dilated Möbius `μ(√q)1_□(q)` (`squareMoebius`,
  corpus `RHTower.mPart 2`) inverts the square indicator (corpus HTGeometry
  `powerDilation_moebius_zeta_cancel`), so `μ = μ(√·)1_□ ⋆ λ` (`moebiusR_eq_dirichletConv_squareMoebius`)
  and `μd^{-ε} = μ(√·)1_□d^{-ε} ⋆ λd^{-ε}` (`dampedMoebius_eq_dirichletConv`); the kernel is critical
  Wiener (`criticalWiener_dampedSquareMoebius`). With C11: **`receiverBounded_moebius_iff_liouville`**
  — at every ε > 0 the receiver of μ(d)d^{-ε} is bounded iff that of λ(d)d^{-ε} is; the Möbius and
  Liouville parity pairs exist at exactly the same dampings. RH criterion on the Liouville weight
  alone (`riemannHypothesis_of_liouville_cofinal_receiver`): bounded Liouville receivers at
  arbitrarily small damping ⇒ RH (via corpus `riemannHypothesis_of_pmPowerDamped_cofinal_discrete_budget`).
  The step: square dilation k ↦ j²k. Standard axioms (2 audited); wired.
- **C17 · The receiver of a multiplicative weight is decided at the primes** —
  `ReceiverOfMultiplicativeWeightsIsDecidedAtThePrimes`. For multiplicative `f` with `|f| ≤ 1`:
  `f = (f⋆1) ⋆ μ` (`dampedMultiplicative_eq_dirichletConv`); if `f(p) = −1` at every prime then
  `g = f⋆1` has `g(p) = 0`, `|g(p^k)| ≤ k−1` (`abs_mul_zeta_apply_prime_pow_le`), Euler factors
  `1 + O(p^{-1-2ε})` (bound `x/(1−x)² − x ≤ 32x²`, x = p^{-1/2-ε}), and via the corpus Euler-product
  bound `RHTower.pm_summable_of_multiplicative_local_bound`, `g d^{-ε}` is critical Wiener
  (`criticalWiener_mul_zeta`). Headlines: `receiverBounded_of_primes_neg_one` — **every
  multiplicative f ≡ −1 on primes is paid wherever μ is**; unconditional at half damping
  (`receiverBounded_half_of_primes_neg_one`): μ, λ, and all Möbius-like weights (any values ≤ 1 on
  higher prime powers). Conversely `not_receiverBounded_of_primes_one`: multiplicative `f ≥ 0` with
  `f(p) = 1` (so f ≥ μ²) diverges for every 0 < ε ≤ 1/2 (squarefree drift).
  Insight: parity enters the receiver of a multiplicative weight only through the prime dilations
  `k ↦ pk`; higher prime powers are critical-Wiener negligible. Standard axioms (2 audited); wired.
- **C18 · Pretentious multiplicative weights and the receiver trichotomy** —
  `PretentiousMultiplicativeWeightsAndTheReceiverTrichotomy`. General kernel lemma
  (`criticalWiener_of_multiplicative`): multiplicative g with g(p) = 0, |g(p^k)| ≤ Bk is critical
  Wiener (Euler factors 1 + 32Bp^{-1-2ε}). Character model: `μχ` inverts `χ`
  (`charMoebiusAF_mul_charAF`), `g = f⋆μχ` has `g(p^{m+1}) = f(p^{m+1}) − χ(p)f(p^m)`
  (`mul_charMoebius_apply_prime_pow`), so `receiverBounded_of_primes_char`: **every multiplicative
  |f| ≤ 1 with f(p) = χ(p) (χ real non-principal) has bounded receiver at every ε > 0**
  (unconditional, all dampings). Headline `receiver_trichotomy`: χ-pretentious ⇒ bounded at every
  damping; μ-pretentious ⇒ bounded at 1/2 (wherever μ is); 1-pretentious, f ≥ 0 ⇒ divergent for all
  ε ≤ 1/2. The receiver classifies multiplicative weights by the model they pretend to at the primes;
  the arithmetic enters only through `k ↦ pk`, p prime. Standard axioms (audited); wired.
- **C19 · The horizon law of positive rows** — `HorizonLawOfPositiveRows`. Rows of horizon `2^J`
  (`dyadicRow`): masses equal those of c inside the horizon, vanish beyond. Two-sided horizon law:
  `(1/16)Σ_{k<J−1}M_{k+1}²/2^{k+1} ≤ E_{2^{J−1}}(c_J)` (`sum_dyadicMass_sq_le_rowEnergy`) and
  `E_T(c_J) ≤ 12c(1)² + 100Σ_{k<J}M_k²/2^k` uniformly in T (`rowEnergy_le`): each horizon step
  `N ↦ 2N` adds one dyadic block `≍ M_J²/2^J`. Headline `rows_uniformly_bounded_iff`: **for nonnegative
  weights the horizon limit commutes with the receiver** — rows uniformly bounded iff the weight's
  receiver is bounded (contrast: C3's sign-twisted χ₄ rows have pointwise limit with divergent
  receiver; non-commutation needs signs). Standard axioms (2 audited); wired.
- **C19 correction** — the contrast clause is wrong: C3's twin rows diverge and so does their limit
  c₊ (no non-commutation there). Whether signed rows can be uniformly bounded with a divergent limit
  (or conversely) is open on this card; positivity gives commutation.
- **C20 · Unimodular completions of real characters are parity partners of the smooth power** —
  `UnimodularCharacterCompletionsAreParityPartnersOfTheSmoothPower`. General smooth twin for any
  completely multiplicative unimodular sign s with L_s ≠ 0 (`smoothTwin`, equal amplitudes
  `abs_weightRamanujanCoeff_smoothTwin`, divergence `tendsto_weightPronicEnergy_smoothTwin`).
  Completion `χ̂` (`charCompletion`: χ̂(p) = χ(p) for p ∤ q, 1 for p | q; for χ₄: (−1)^{Ω₃(n)}),
  completely multiplicative and unimodular; `χ̂ = 1_{q-smooth} ⋆ χ` (`charCompletionAF_eq`, via
  `IsMultiplicative.eq_iff_eq_on_prime_powers`); the q-smooth kernel is a finite Euler product,
  critical Wiener (`criticalWiener_smoothPart`); mean `L(1+ε,χ̂) = L(1+ε,χ)∏_{p|q}(1−p^{-1-ε})^{-1} ≠ 0`
  (`charCompletionMass_ne_zero`). Headline `charCompletion_parityPair`: **for every real
  non-principal χ and every 0 < ε ≤ 1/2, the ±1-valued χ̂(d)d^{-ε} (bounded) and the full-density
  smooth power κd^{-ε} (divergent) have identical Ramanujan amplitudes** — unconditional at every
  damping, bounded member without zeros (unlike χ) and positive member of full density (unlike the
  character twins). The parity of the inert prime factors (k ↦ pk, p inert) is the whole difference.
  Standard axioms (audited); wired.
- **C21 · Sparse prime flips preserve the receiver** — `SparsePrimeFlipsPreserveTheReceiver`.
  Completely multiplicative unimodular signs (`UnimodularSign`, inverse `μf`,
  `moebiusAF_mul_af`); flip kernel `g = f'⋆μf` with `g(p^{m+1}) = f'(p)^m(f'(p) − f(p))`
  (`flipKernel_apply_prime_pow`) — zero over primes where f, f' agree, ≤ 2 elsewhere; Euler factors
  ≤ 1 + 8p^{-1/2-ε} on the flip set (`criticalWiener_flipKernel`). Headline
  `receiverBounded_of_sparse_flip`: **if f and f' differ only on primes P with Σ_{p∈P}p^{-1/2-ε} < ∞,
  their receivers at ε are bounded together** — the global sum of C4's local criterion. Consequence
  `not_receiverBounded_of_sparse_negative_primes`: a unimodular completely multiplicative sign whose
  −1-primes have convergent p^{-1/2-ε}-mass diverges for ε ≤ 1/2 (smooth-power class): **a bounded
  ±1 pattern must flip a non-sparse prime set** — the necessary condition matching C20 (inert primes,
  density 1/2). The receiver sees parity only through prime sets of divergent critical-line mass.
  Standard axioms (2 audited); wired.
- **C22 · The logarithmic moment hierarchy separates every pair with a positive member** —
  `LogarithmicMomentHierarchySeparatesEveryPositivePair`. Higher von Mangoldt functions
  (`higherVonMangoldt k = Λ_{k+1}`, Λ_{k+2} = Λ_{k+1}·log + Λ_{k+1}⋆Λ): Σ_{e|d}Λ_{k+1}(e) = log^{k+1}d
  (`sum_divisors_higherVonMangoldt`), 0 ≤ Λ_{k+1} ≤ log^{k+1}, **positive exactly on e ≥ 2 with
  ≤ k+1 distinct prime factors** (`higherVonMangoldt_pos`, prime-power recursion). Moment law
  (`firstPronicMoment_logPowWeight`): `M(c·log^k) = −Σ_e Λ_{k+1}(e)W_c(e)` on the damped class (log-power
  weights stay damped at ε/2, `logPowWeight_mem_dampedClass`); ordering for positive pairs
  (`logMoment_sub_of_positive_twin`). Möbius inversion over multiples on the damped class
  (`hasSum_moebius_mul_weightRamanujanCoeff`: c(d)/d = Σ_m μ(m)W_c(dm)), hence **Ramanujan coefficients
  determine the weight** (`eq_of_weightRamanujanCoeff_eq`); δ₁-shift preserves the receiver
  (`receiverBounded_sub_unitMass`). Headline `exists_logMoment_separating`: **if c₁ ≥ 0 has the
  amplitudes of c and their receivers differ, some logarithmic pronic moment separates them strictly,
  M(c₁·log^k) < M(c·log^k)** — no parity pair with a positive member is invisible to the hierarchy;
  the order of the first separating moment is the least ω(e) with W_c(e) < 0 (C14: order 1 blind,
  order 2 separates). Standard axioms (3 audited); wired.
- **C23 · The logarithmic moments are a complete receiver invariant** —
  `LogarithmicMomentsAreACompleteReceiverInvariant`. `M(c·log^k) = −Σ_d c(d)log^{k+1}d/d`
  (`firstPronicMoment_logPowWeight_eq_tsum`) is up to sign the (k+1)-st derivative at s = 1 of
  `L_c(s) = Σ c(d)d^{-s}`, holomorphic on Re s > 1 − ε (Mathlib `LSeries_iteratedDeriv`,
  `LSeries_analyticOnNhd`). Equal moments of all orders ⇒ all positive-order derivatives of
  `L_c − L_{c'}` vanish at 1 ⇒ constant on a ball (Mathlib `Complex.hasSum_taylorSeries_on_ball`) ⇒
  constant on the half-plane (identity theorem) ⇒ `c = c'` off d = 1 (Dirichlet coefficient uniqueness
  `LSeries.eq_of_LSeries_eventually_eq`) (`eq_add_unitMass_of_logMoments_eq`); δ₁ is invisible to the
  receiver (`receiverBounded_add_unitMass`). Headline `exists_logMoment_ne`: **every parity pair,
  whatever the signs of its members, is separated by some logarithmic pronic moment M(c·log^k)** — the
  log-moment family is a complete system of separating additive observables for the receiver (C22
  adds the ordering and the exact order for positive pairs). Standard axioms (2 audited); wired.

### C24 — Every real character carries parity rows at every horizon (formalized)
- Module: `TransHorizonIncidenceMechanics/RealCharacterParityRowsAtEveryHorizon.lean`, capstone `char_parityRows`.
- Statement: for every real non-principal χ mod q and 0 < ε ≤ 1/2, the horizon-N rows `c_N = χ d^{-ε} 1_{d≤N}`
  and their twins `c'_N` (Selberg coordinates χ̂(e)Y_N(e), χ̂ the unimodular completion) have Selberg
  coordinates equal up to sign and identical two-point translated moments at every N; eventually in N a
  cubic translated moment separates them (at an odd n₀ with χ(n₀) = −1, from `sign_cube_eq_one_of_translatedMoment_three`);
  the rows have pronic energy ≤ 36 q² Σ n^{2/(2+ε)−2} uniformly in N; the twins' energy → ∞.
- Mechanism: twin rows converge divisor-wise to `(L/O) 1_{(d,q)=1} d^{-ε}` (dominated convergence, Möbius inversion
  of the unit mass `O` via `hasSum_moebius_mul_weightRamanujanCoeff`); the signed twin has the receiver of the
  positive twin (`weightPronicEnergy_smul`, t = sign L).
- Step named: N ↦ N+1 (horizon), with the separating additive observable the cubic translated moment at one inert odd modulus.
- Generalizes C3 (χ₄ only) to all real characters; partial sums ≤ q replace {0,1}.
