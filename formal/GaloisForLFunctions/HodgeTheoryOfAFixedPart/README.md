# Hodge Theory of a Fixed Part (HFP)

Namespace `GaloisForLFunctions.HodgeTheoryOfAFixedPart`; umbrella `HodgeTheoryOfAFixedPart.lean`;
14 modules. Specification: §2.9 of
[the review-1011 summary](../../../docs/reports/review-1011/obstacles-summary.md); card
`docs/drafts/pipeline/3-formalized/hfp-hodge-theory-of-a-fixed-part-programme.md`.

Status: **Lean** = proved in this folder; **corpus** = proved elsewhere in the corpus;
**[C]** = published mathematics not in the corpus; **open** = no theorem.

## 1. Motivation

A Hodge index theorem turns a statement in law into a statement at every zero. The known proofs
take the sign from one of three sources.

- **A family.** Monodromy and weights over a base. `ζ` has no moduli: a Dirichlet series with its
  functional equation is a multiple of it, and an arithmetic family sees only its variable part.
  `ζ` is the fixed part of all of them.
- **A surface.** An ample class and a count of sections on a two-dimensional object. The square
  of `Spec ℤ` is a curve: the union of the Frobenius graphs, glued along the primes.
- **A Frobenius with zero derivative.** Simultaneous vanishing at the primes of a window costs
  the count of the window.

HFP is the Hodge theory of the one object that is left: the pairing of the degree points of the
arithmetic square. Its entries are finite parts, not intersection numbers of a surface:

  `Γ_m · Γ_n = jet + contact` off the diagonal, `Γ_n · Γ_n = −log(n/2π)`.

A contact is the order of the scheme `Γ_m ∩ Γ_n`; a jet is a trace of the same Frobenius on the
archimedean fibre; the self-intersection is the logarithm of the density of the comb that
contains the point, over `2π`. On packets the pairing tends to `2 d₁ d₂ − Z(f)`, twice the product
of the degrees minus the sum over the zeros, and the inequality of Castelnuovo and Severi
`D·D ≤ 2 d₁ d₂` for all packets is the Riemann hypothesis (corpus).

The programme asks what an index theorem for this object can rest on when no family, no surface
of finite type and no cheap Frobenius exists: which comb, which classes have sections, what a
section certifies, at which scale the inequality is a statement, and how many directions can
violate it.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Degree point | `n : ℕ`, `n ≥ 1` | the graph `Γ_n` of `F_n` on the arithmetic square, at `log n` |
| Real divisor | `c : ℕ → ℝ` on a finite set `S` | `D = Σ c_n γ_n`; for a packet `f` sampled at the scale `N`, `c_n = f(log(n/N))/√n` (`sampleCoord`) |
| Jet | corpus `jetKernel` | `½(1/|m − n| + 1/(m + n))` |
| Jet of a weight | `jetLevel j` | `min(m, n)^{2j}/max(m, n)^{2j+1}`: the weight `−2j` of the archimedean fibre |
| Contact | `contact`, `contactW w` | `Λ(n/m)` for `m ∣ n`; with weights `w` in place of `Λ` |
| Counterterm | `counterterm` | `log(n/2π)` |
| Pairing | `combPairing S c`, `combBilin` | `Σ_{m≠n} c_m c_n (jet + contact) − Σ c_n² log(n/2π)` |
| Degrees | `degOne`, `degTwo` | `d₁ = Σ c_n/n`, `d₂ = Σ c_n`; the pole plane is `2 d₁ d₂` |
| Weil's form on the comb | `combForm`, `formBilin`, `combFormW w` | `2 d₁ d₂ − D·D` |
| Potential, Dirichlet form | `combPotential`, `combDirichlet` | the row of a point in `S` minus its counterterm; `Σ (c_m − c_n)² Γ_m·Γ_n` |
| Window | `Ioc N (N + M)` | the degree points above the scale `N`, of ratio at most `1 + M/N` |
| Blocks | `blockIndex`, `blockKernel` | `B` consecutive degree points; `1/(2B|i − j|)` between blocks at distance `≥ 2` |
| Flat tail | `fun _ => 1` on `Icc 1 N` | `Σ_{n ≤ N} γ_n`: the second ruling cut at `N` |
| Gauge of the flat tail | `tailPotential`, `tailRow` | Weil's form of the flat divisor against `γ_n` |
| Chebyshev's function | `chebyshev` | `ψ(K) = Σ_{k ≤ K} Λ(k)` |
| Carry cocycle | `carryCocycle M N` | `log C(M + N, M)` |
| Sections of the tower | corpus `orbitLatticeMap` | `b` digits on each of the `τ(M)` lines of the level `M` |
| Section at a prime | `primePointSection p` | `p − e_p`: zero on every `Γ_{p^j}`, `p` on the diagonal |
| Stable, separated comb | `FrobeniusStable`, `Separated`, `frobeniusOrbit` | `kS ⊆ S` for `k ≥ 1`; distinct points at distance `≥ σ`; `δℕ` |
| Two-bump divisor | `twoBumpPacket v`, `spline` | the cubic spline and its translate by `v`: `Γ_1 + Γ_p` smeared, for `v = log p` |
| Approximation by weights | `combFormJets J` | Weil's form with the Dirichlet form of the jets cut at `J` weights |
| Comb of a curve | `curveContact`, `curvePairing`, `curveCombForm` | degree points `q^k`; contacts `N_j/q^{j/2}`; diagonal `2 − 2g`; Weil's form of a curve datum |

## 3. Language

- **Comb**: a locally finite set of degree points with masses. **Counterterm**: the logarithm of
  its density over `2π`. **Normal form**: the pairing in the coordinates `c_n = f_n/√n`, one
  matrix on the positive integers with no scale in it.
- **Packet**: `f ∈ C²_c` in the logarithmic coordinate, sampled at a scale. **Real divisor**: any
  real vector on finitely many degree points. **Finite scale**: a statement at one `N` for all
  real divisors of a window. **Limit**: a statement on the samples of a packet as `N → ∞`.
- **Contact below / above** a graph `Γ_m`: with `Γ_d`, `d ∣ m`, `d < m`; with `Γ_{mk}`, `k ≥ 2`.
- **Balance of Zariski**: the contacts below `Γ_n` sum to `log n`, the divergent part of its
  counterterm.
- **Gauge** of a positive divisor `h`: the form written as a potential `(𝔚h)_n/h_n` on the
  squares plus a Dirichlet form.
- **Index**: the number of positive squares of the pairing with the two rulings adjoined; one
  plus the number of negative squares of Weil's form. **Defect** of a splitting
  `P_W E − c P_{W♯} E'`: the divisor `W`.
- **Certified** contact: one that divisibility forces on every section vanishing on the other
  graph. **Small** section: one bounded on a graph by the degree minus the jets.
- **Weight** `−2j`: the `j`-th jet of the archimedean fibre. **Resolved** at the scale `N`: up
  to a remainder `(1 − 1/N)^{2J}`.

## 4. Mechanisms

Built on (corpus): contacts plus jets; comb finite parts; the limit `2 d₁ d₂ − Z(f)` of the
pairing; the section-count theorem; the index law of a Hermite–Biehler sum and the Pontryagin
law; logarithmic windows with exceptional sets; the comb selects the contacts.

Developed here (Lean):

1. **The normal form.** `degreeForm + 2·degreeContact` of a sampled packet is `combPairing` of
   `c_n = f_n/√n`; jets `½(1/|m − n| + 1/(m + n))`, contacts `Λ(n/m)`, diagonal `−log(n/2π)`,
   pole `1/m + 1/n`. The form `2 d₁ d₂ − D·D` of the samples tends to the sum over the zeros.
2. **Zariski's lemma on a comb.** Off the diagonal the matrix is nonnegative:
   `D·D = Σ c_n² V(n) − ½ Σ_{m≠n} (c_m − c_n)² Γ_m·Γ_n ≤ Σ c_n² V(n)`.
3. **The balance.** The contacts below `Γ_n` sum to `log n`; on a set that contains the proper
   divisors of `n`, `V(n)` is the row of the jets, the contacts above, and `log 2π`.
4. **Schur's test after one subtraction.** A kernel that depends only on the blocks of its two
   points vanishes on the divisors with zero block sums. The singular part of the jet minus
   `1/(2B|i − j|)` has a row `≤ H_{2B} + 2`.
5. **The gauge of the flat tail.** `2 d₁ d₂ − D·D = Σ c_n² ρ(n) + ½ Σ (Γ_m·Γ_n − 1/m − 1/n)(c_m − c_n)²`
   with `ρ(n) = N/n − ψ(N/n) + H_N − ½(H_{N−n} + H_{N+n}) + 3/(4n) − log 2π` on `[1, N]`.
6. **Chebyshev's identity is a contact energy.** `Γ_n` meets the tail in `log n + ψ(N/n)`;
   `Σ_{n ≤ N} ψ(N/n) = log N!`.
7. **Each weight is a Hardy square.** `jet = Σ_j min^{2j}/max^{2j+1}`; by Abel summation the
   kernel of the weight `−2j` with the diagonal `1/n` is a positive combination of the squares of
   `Σ_{n ≤ t} c_n n^{2j}`.
8. **The triangular pigeonhole.** Values on `Γ_1, …, Γ_K` bounded by `B_n` and glued by the
   necklace congruences take at most `Π (⌊2B_n/n⌋ + 1)` vectors.
9. **Necklace divisibility.** A section vanishing on `Γ_d` for the proper divisors `d` of `n`
   has `n ∣ x_n`; one vanishing on `Γ_{pm}` has `p ∣ x_m`.
10. **Collision.** Two orbits `ℕ` and `θℕ`, `θ` irrational, have points at every small positive
    distance; a point `α·a/b` in lowest terms and `α` have multiples at the distance `α/b`.
11. **Sampling.** A negative direction of the limit is a negative direction at every large scale.

## 5. Questions

| # | Question | Answer | Status |
|---|---|---|---|
| Q1 | Which comb is canonical on a window? | The orbit of one point under the Frobenius monoid. A comb that carries the contacts is stable under every `F_k`; one whose jets are bounded off the diagonal is uniformly separated; a separated stable comb lies in one orbit `δℕ`, and a stable subset of an orbit that contains its generator is the orbit. Two orbits with an irrational ratio collide. The torus `δ` does not enter the normal form. The counterterm of this comb is fixed twice: by the balance of Zariski, and as what is left of the diagonals `Σ c_n²/n` of infinitely many weights of the jets, each a Hardy square. On the sub-comb `gℕ` it is larger by `log g` (corpus). | Lean: `exists_orbit_of_separated`, `eq_orbit_of_generator_mem`, `exists_near_collision`, `den_le_of_separated`, `sum_contact_properDivisors`, `neg_le_sum_sum_jetLevel`; corpus: `AbsoluteGeometryOfSpecZ.not_exists_counterterm_of_two_combs` |
| Q2 | What is the second axiom that turns the exact section count into Bézout? | A bound from above on the section. On the tower both axioms hold for the tower's own degrees: a nonzero section vanishing on `Γ_1, …, Γ_K` exists once the count `(A + 1)^{bτ(M)}` exceeds `Π_{n ≤ K}(⌊2B_n/n⌋ + 1)`, the gluing index `K!` entering as the second term; on its first graph `n > K` it has `n ≤ |x_n| ≤ σ(M)·b·A·q^{bn}`, the product formula. For the pairing of the normal form restriction certifies every contact below a graph and, above it, one contact for each prime; it certifies neither the contacts with the higher prime powers above (`p − e_p` vanishes on every `Γ_{p^j}` and is `p` on the diagonal) nor any jet. So Bézout for a class with a section is the statement that the section is small: `log|x_m|` at most the degree minus the jets and the prime powers. A count of small sections for classes with a packet component is open. | Lean: `exists_orbitLatticeMap_vanishing`, `exists_orbitLatticeMap_first_graph`, `natCast_dvd_ghostComponent_of_vanish`, `sum_contact_properDivisors_le_log_abs`, `sum_contact_primes_le_log_abs`, `primePointSection_spec`, `log_abs_primePointSection_lt`; corpus: `ArithmeticCorrespondencePositivity.hodgeIndex_iff_exists_sectionCount` |
| Q3 | Is the index of the degree-point pairing at most one on every window? | **At finite scale, on short windows: yes.** For `18M ≤ N`, every set of degree points in `(N, N + M]` and every real divisor: `D·D ≤ −(1/40)Σc_n²` and `2 d₁ d₂ − D·D ≥ (1/50)Σc_n²`. **On every window the index is finite, uniformly in the scale**: for a ratio `≤ Q` there is `R` such that at every scale `N ≥ R` Weil's form is nonnegative on the real divisors whose sums over fewer than `2QR` blocks vanish. **Finite scale decides the limit**: if at arbitrarily large scales `2 d₁ d₂ − D·D ≥ −ηΣc_n²` on the windows, for every `η > 0`, the Riemann hypothesis holds; if it fails, every large scale has a real divisor with `Σc_n² ≤ C` and form `≤ −ε`. In the limit on packets: width `≤ 181/250` (corpus); every window iff RH (corpus). A splitting of `ξ` with a defect of degree `κ` bounds the index by `1 + κ`. | Lean: `combForm_ge_of_short`, `combPairing_le_of_short`, `exists_blockSize_combForm_nonneg`, `blockIndex_lt`, `riemannHypothesis_of_frequently_combForm_ge`, `exists_window_combForm_neg_of_not_riemannHypothesis`, `hermNegIndex_zeroGram_zeta_le_of_hermiteBiehler`; corpus: `AbsoluteGeometryOfSpecZ.tendsto_degreePairing_le_degrees_of_width` |
| Q4 | How do the carries enter the pairing? | Through the counterterm. The contacts are not invariant under addition: the gluing conditions of the block `(M, M + N]`, and its counterterm, are those of its translate `[1, N]` plus `log C(M + N, M)`, the `Λ`-weighted carries of `M + N`. In the gauge of the flat tail the potential is `N/n − ψ(N/n)` plus the harmonic row: the remainder of the prime number theorem, with limit `k − ψ(k) − log 2π − ½log(1 − k⁻²)` along `N = kn`. The octave above the tail has no primes: `Γ_n`, `N < n ≤ 2N + 1`, meets the tail in `log n`, and `Σ_{n ≤ N}(ψ(2N/n) − ψ(N/n)) = log C(2N, N) + log N!`; the line `n = 1` carries the primes of `(N, 2N]`, the lines `n ≥ 2` the carries and the gluing index. Weil's form of the flat tail is `2N·H_N − (N + ½)H_{2N} + (5/4)H_N + N − log N! − N log 2π`, per point `→ 2 + γ − log 4π`. | Lean: `sum_counterterm_Ioc`, `carryCocycle_eq_sum_carry`, `tailPotential_Icc`, `tendsto_tailRow_mul`, `sum_contact_Icc_of_octave`, `sum_chebyshev_octave`, `sum_chebyshev_octave_lines`, `combForm_flatTail`, `tendsto_combForm_flatTail_div` |
| Q5 | Why does the argument fail for integer-norm monoids, which the square does not see? | The comb sees them. The balance of Zariski holds at every degree point iff the contact weights are `Λ`; a multiplicative system has every integer as a norm exactly once iff its weights are `Λ`. On the flat tail the form with weights `w` is the form of the square minus `2Σ_k (w(k) − Λ(k))⌊N/k⌋`: an excess `Σ(w − Λ)(k)/k` of contact mass above `1 + γ/2 − ½log 4π`, the first Li coefficient, violates the inequality at every large scale; a double contact at the prime `2` does. In the limit every weight other than `Λ` fails (corpus). Short windows do not see the weights. | Lean: `sum_divisors_eq_log_iff`, `multiplicity_eq_one_iff`, `combFormW_flatTail`, `eventually_combFormW_flatTail_neg`, `eventually_combFormW_doubleTwo_neg`, `combFormW_ge_of_short`; corpus: `AbsoluteGeometryOfSpecZ.not_combBezout_of_ne` |

## 6. Tools

| Tool | Content | Module |
|---|---|---|
| T1 Calculus of comb finite parts | the normal form, its identification with the pairing of the degree points and its limits; Zariski's lemma; potentials; the gauge of a flat divisor; the jets by weights | `TheNormalFormOfThePairingOfTheDegreePoints`, `WeilsFormInTheGaugeOfTheFlatTail`, `TheJetsAreASumOfHardySquares` |
| T2 Section counts on towers of lines | the triangular pigeonhole; sections vanishing on the first `K` graphs; the first graph of a section; divisibility on a graph | `RiemannRochOnTheTowerHasTheGluingIndex`, `WhatTheSectionsOfTheSquareCertify` |
| T3 The index law at infinite rank | negative definiteness on short windows; the block kernel and the Schur test for a signed kernel; codimension bounds uniform in the scale; finite scale against the limit; index against the defect of a splitting | `TheHodgeIndexHoldsAtEveryScaleOnShortWindows`, `TheIndexOfAWindowIsFiniteAtEveryScale`, `TheInequalityAtFiniteScaleDecidesTheLimit`, `TheIndexOfThePairingIsAtMostTheDefectOfASplitting` |
| T4 Window locality with exceptional sets | the two-bump divisor of a prime and its form; logarithmic windows off `Ce^{δT}` primes; all finite-scale statements hold on arbitrary subsets of a window | `OneInequalityPerPrimeOnTheComb` |
| Calibration | contact weights in place of `Λ`; the comb of a curve datum | `TheCombOfUnitMassesFixesTheContacts`, `ShortWindowsDoNotSeeTheContacts`, `TheCombOfACurve` |
| T5 The carry cocycle | counterterm and gluing conditions of a block; Chebyshev's identity; the octave | `WeilsFormInTheGaugeOfTheFlatTail` |
| T6 Ordered approximations | Weil's form with the first `J` weights of the jets: increasing in `J`, below the form, with the exact error `½Σ(min/max)^{2J}·jet·(c_m − c_n)²`, at most `(1 − 1/N)^{2J}` of the Dirichlet form of the jets on `[1, N]` | `TheJetsAreASumOfHardySquares` |

## 7. Criteria

Readings of the criteria of the specification on the mechanisms of §4. No mechanism of the
folder proves the inequality on all windows; the readings say what each does on the calibration.

| # | Criterion | Reading |
|---|---|---|
| K1 | Reproduce Weil's proof for curves, where the comb is `q^ℤ` | The statement is reproduced, the proof is not. Over a curve the normal form has the contacts `N_j/q^{j/2}`, no jets, and the diagonal `2 − 2g`, the same formula at the lag `0`: no counterterm (`curvePairing_eq_sum`). Weil's form on the comb is the Toeplitz form of the Frobenius eigenvalues and the inequality on all real divisors is purity (`curveCombForm_eq_toeplitz`, `curveCombForm_nonneg_iff_unitary`). On a regular surface restriction certifies every contact, prime powers included [C]; on the square it does not (`log_abs_primePointSection_lt`). The folder has no count for classes with a packet component, over a curve or over `ℤ`. |
| K2 | Reproduce the Lagarias–Suzuki line law as an index-one statement | Done: a tempered configuration carried by the zeros of the cleared constant term has at most one negative square for `Y ≥ 1` and none for `Y ≤ 4πe^{−γ}` (`hermNegIndex_zeroGram_le_one_of_constantTerm`, `hermNegIndex_zeroGram_eq_zero_of_constantTerm`). |
| K3 | Fail on the fakes | Short windows pass for every system of contact weights (`combFormW_ge_of_short`), and so does the finite index: these statements are not selective. The flat tail fails on an excess of contacts (`eventually_combFormW_flatTail_neg`). The golden datum fails on its comb (`exists_curveCombForm_goldenDatum_neg`). In the limit every weight other than `Λ` fails (corpus `combBezout_iff`). |
| K4 | Use the coefficient size exactly | The normal form is the critical normalization: contacts `Λ(k)` against the counterterm `log(n/2π)`. The tolerance of the flat tail is the first Li coefficient, `0.023…` of contact mass. |
| K5 | Not be uniform in real characters | No statement of the folder is about a family. |
| K6 | Be pointwise | The finite-scale statements hold at one scale `N` and on every subset of the window; the window criterion is one prime at a time (`riemannHypothesis_iff_twoBump_windows_off_finset`). |
| K7 | Respect the no-gos | No object of finite type and no glued carrier is used; contacts and jets are not exchanged: restriction certifies contacts and no jet; the diagonal is the counterterm of the comb, and the comb is forced (`exists_orbit_of_separated`). |

## 8. Milestones

| # | Milestone | Status |
|---|---|---|
| M1 | Contacts, jets, comb finite parts, the section-count theorem, windows, the pairing with limit `2 d₁ d₂ − Z(f)` | corpus |
| M2 | The pairing on classes of the tower | Lean: classes `D − Σ_{n ≤ K} Γ_n` with a section (`exists_orbitLatticeMap_vanishing`); their restriction to a graph (`exists_orbitLatticeMap_first_graph`); the contacts of the normal form that restriction certifies and those it does not (`WhatTheSectionsOfTheSquareCertify`) |
| M3 | The statement over a curve in comb language | Lean: `curvePairing_eq_sum`, `curveCombForm_eq_toeplitz`, `curveCombForm_nonneg_iff_unitary`, `curveCombForm_singleton` |
| M4 | Bézout at larger bounded apertures | Lean: at every finite scale, ratio `19/18`, all real divisors (`combForm_ge_of_short`); at every ratio up to finitely many block sums (`exists_blockSize_combForm_nonneg`). Corpus: in the limit, width `181/250`; from zeros verified to a height (`VerifiedHeightRungs.windowPositiveAt_of_rhVerifiedThrough`) |
| M5 | Castelnuovo–Severi for combs | open: the Riemann hypothesis |

## 9. Pillar theorems

| Theorem | Lean |
|---|---|
| The normal form is the pairing of the degree points; Weil's form on the comb tends to the sum over the zeros | `combPairing_sample`, `tendsto_combForm_sample` |
| Zariski's lemma on a comb | `combPairing_eq_potential_sub_dirichlet` |
| The inequality at every finite scale on short windows, with a margin | `combForm_ge_of_short` |
| The index of a window is finite, uniformly in the scale | `combForm_nonneg_of_blockSum_eq_zero`, `exists_blockSize_combForm_nonneg` |
| The inequality at finite scale gives the Riemann hypothesis; a zero off the line is seen at every large scale | `riemannHypothesis_of_frequently_combForm_ge`, `exists_window_combForm_neg_of_not_riemannHypothesis` |
| In the gauge of the flat tail the potential is the remainder of the prime number theorem | `combForm_eq_gauge`, `tailPotential_Icc`, `tendsto_tailRow_mul` |
| Chebyshev's identity is the contact energy of the tail; the carry cocycle | `sum_chebyshev_div`, `sum_counterterm_Ioc`, `sum_chebyshev_octave` |
| Weil's form of the flat tail | `combForm_flatTail`, `tendsto_combForm_flatTail_div` |
| The jets are a sum of Hardy squares; the pairing at the scale `N` is resolved by about `N` weights | `hasSum_jetLevel`, `sum_mul_mul_jetLevel_nonneg`, `combForm_sub_combFormJets`, `combForm_sub_combFormJets_le` |
| Riemann–Roch on the tower with the gluing index; Bézout in necklace coordinates | `exists_fiber_of_triangular`, `exists_orbitLatticeMap_vanishing`, `natCast_dvd_ghostComponent_of_vanish` |
| Restriction certifies the contacts below and the primes above, not the prime powers above | `sum_contact_properDivisors_le_log_abs`, `sum_contact_primes_le_log_abs`, `log_abs_primePointSection_lt` |
| The comb of unit masses fixes the contacts; the tolerance of the flat tail is the first Li coefficient | `sum_divisors_eq_log_iff`, `multiplicity_eq_one_iff`, `eventually_combFormW_flatTail_neg` |
| A separated comb stable under the Frobenius monoid is one orbit | `exists_orbit_of_separated` |
| One inequality per prime on logarithmic windows with exceptions, for the two-bump divisor | `tendsto_combForm_twoBumpPacket`, `riemannHypothesis_iff_twoBump_windows_off_finset` |
| The index of the pairing is at most the defect of a splitting; the line law is an index-one statement | `hermNegIndex_zeroGram_le_of_hermiteBiehler`, `hermNegIndex_zeroGram_le_one_of_constantTerm` |
| Over a curve the inequality on the comb is purity; the golden datum fails | `curveCombForm_nonneg_iff_unitary`, `exists_curveCombForm_goldenDatum_neg` |

All are unconditional.

## 10. Traps

| Trap | Truth |
|---|---|
| The pairing is a limit object | in the normal form it is one matrix, defined at every scale and on every real divisor |
| The normal form is nonnegative on every finite set | `2 d₁ d₂ − D·D = c²(1 − log π) < 0` for the single divisor `c·γ_2` (`combForm_singleton_two_neg`): the counterterm is negative below `2π`; the statements are for windows at a scale. Over a curve a single graph has `2g·e²` |
| The inequality at finite scale is the limit statement | it implies it; the converse for all real divisors is open |
| Short-window positivity is evidence | it holds for every system of contact weights |
| A positive potential helps | the potential is positive and the Dirichlet form enters with the minus sign; in the gauge of the flat tail the potential is `N/n − ψ(N/n)`, which changes sign |
| Contacts lower the pairing | they raise it: the inequality bounds jets plus contacts from above by the pole |
| The contact numbers are intersection multiplicities | below a graph they are; above it the graphs `Γ_{mp}, Γ_{mp²}, …` pass through one point and impose one condition |
| Bézout for a class with a section is free | on the tower it is the product formula for the tower's degrees; for the normal form it needs the section to be small by the jets |
| A count of sections gives the sign | the gluing index is the second term of Riemann–Roch; the conclusion with Bézout is `log n ≤ n·b·log q` |
| The counterterm is a convention | it is forced by the balance of Zariski and equals the diagonals left out by the weights of the jets |
| The jets are one kernel | they are a sum over the archimedean weights of positive semidefinite kernels without their diagonals; `N` of them resolve the scale `N` |
| The comb can be chosen | a separated comb that carries the contacts is one orbit; two incommensurable orbits collide |
| The flat tail tests the contacts | it weighs them by `1/k`: it sees their mass, with tolerance `λ₁`, and not their arithmetic |
| A finite index is a step to index one | the bound on the codimension grows like `Q·e^{2ψ(Q)}`; index one on every window is the Riemann hypothesis |

## 11. Open research topics

| Topic | Statement |
|---|---|
| The inequality at finite scale | Does the Riemann hypothesis imply, for every ratio `Q` and `η > 0`, that `2 d₁ d₂ − D·D ≥ −ηΣc_n²` for all real divisors of the windows of ratio `Q` at all large scales? With `riemannHypothesis_of_frequently_combForm_ge` this would make the finite matrices a criterion in both directions. |
| The index at finite scale | Is the number of negative squares of Weil's form on a window at a large scale the Hodge defect of the limit on that window? One inequality is sampling (`exists_window_combForm_neg_of_not_riemannHypothesis`); the upper bound known is the number of blocks. |
| The first contact at finite scale | The inequality for all real divisors on windows of ratio up to `2` (no contact) and up to `3` (the contact `Λ(2)`): in the limit it is known to width `181/250`. |
| Small sections | A count of the sections of the tower bounded on each graph by the degree minus the jets, with the pairing of the normal form as its second term: Riemann–Roch for classes with a packet component. |
| The prime powers | Restriction on the square loses `ψ − θ`. Is there an object on which the graphs `Γ_{mp^j}` meet `Γ_m` in general position? |
| The flat-tail cone | On the span of the flat tails `[1, A]`, `N ≤ A ≤ 2N`, the form is free of primes and explicit. Is it nonnegative at every scale? |
| A splitting with a bounded defect | By `hermNegIndex_zeroGram_zeta_le_of_hermiteBiehler` it bounds the index of the pairing. |

## 12. Context

| Programme | Interface |
|---|---|
| AbsoluteGeometryOfSpecZ | the square, `jetKernel`, `degreeForm`, `degreeContact`, the limit of the pairing, `zeroSum`, the tower `orbitLatticeMap`, necklace coordinates, carries, harmonic rows |
| ArithmeticCastelnuovoSeveri | zero configurations, `zeroGram`, the Pontryagin law, curve data and the Frobenius span |
| InfiniteRankPurityTheory | the index law of a Hermite–Biehler sum, the cleared constant term, the exceptional parameter |
| SurfaceOfSpecZ | logarithmic windows with exceptional sets |
| SquareRootThreshold | the lag structure of a bump, the two-bump identity, the box spline, tempered configurations |
| ArithmeticCorrespondencePositivity | a section count with Riemann–Roch and Bézout is the Hodge index |
| HyperbolicArakelovTheory | the arithmetic clock: ordered energies below Weil's form in the continuum, the counterpart of `combFormJets` |
| ArithmeticWeightTheory | the fixed-part theorem for arithmetic families: why no family is used here |

HFP adds to the corpus the finite-scale side of the pairing of the degree points: an exact matrix
with theorems at one scale, an index bound uniform in the scale, the reading of the counterterm
and of the carries inside the matrix, and the list of what a section of the square certifies.

## 13. Success criteria and contributions

Each of Q1–Q5 has an answer with theorems of the folder; each tool T1–T6 is a module with
theorems; each criterion K1–K7 has a reading; M2, M3 and M4 are theorems of the folder. M5 is the
Riemann hypothesis and is open, as are the topics of §11.

A **contribution** must be unconditional; act on the normal form of the pairing or on the
sections of the square and of the tower; say which question, tool, criterion or milestone it
addresses; and be one of: an exact identity of the normal form, an inequality at finite scale for
all real divisors, an index statement, a calibration on a system of contact weights or on a
curve, or a statement of what a section certifies. A restatement of the inequality on packets as
an equivalent of the Riemann hypothesis is not a contribution; a theorem that holds for every
system of contact weights is one only if it says so.
