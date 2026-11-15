# Review 14-11: consolidated report and big-picture reading (Fable)

Checkpoint `60139af75d`; the working tree holds uncommitted peer modules, read here at the level of their statements. Inputs: the frontier map, the killed-routes ledger, the review-1411 unification, obstacle and
walls ledgers, and the Lean corpus read through the search tool (programme READMEs, formalized cards, statements, proofs).
No build, compile, axiom audit or web search was run. Statuses of modules are reported as the corpus states them.

**Tags.** [L] Lean statement and proof read in source for this report. [S] Lean statement read, proof not read.
[R] programme README, pipeline card or ledger. [D] deduction of this report: not in the corpus, needs a paper proof and a
Lean proof before anything is built on it.

**Notation.** `Θ = sup Re ρ`, width `w = Θ − ½` (`zetaZeroWidth`), depth of a zero `δ(ρ) = |Re ρ − ½|`, quartet
`{ρ, ρ̄, 1 − ρ, 1 − ρ̄}`. ZAL: finitely many zeros beyond every positive depth (`ApproachesLine`). AAL: for every `h ≥ 0`,
finitely many zeros right of `½ + h` means none (`AsymptoticAbscissaLaw`). B13: finitely many off-line zeros means none
(AAL at `h = 0`). Landing: ZAL implies finitely many off-line zeros (`ZetaLandingLaw`).

---

## Answers in brief

| # | Question | Answer |
|---|---|---|
| 1 | Big picture | One producer (`Θ ≤ 7/8`), many exact rulers of the width, three atoms. Every route stops at the same passage: from a law, a mean, a half-plane or a finite stage to one function on one line. Solved obstacles: §1.2. Left: O1–O8 of §1.3. |
| 2 | Opportunities | Exchange the 7/8 theorem at every ruler; the converse rate law of the windows (margin exponent `3/8 + ε`); the Grössencharacter rung (frame wall `31/48`); a saving at the floor bin; the exact probe over `𝔽_q[T]`. |
| 3 | Clear path to quasi-RH | Quasi-RH is a theorem at `7/8`. Below `7/8` there is a price list and no path; below `3/5` the producer class has no member. |
| 4 | Clear path to 70% on the line | No. The missing input is a signed bound for prime pairs past bandwidth one: `I ≤ 7/45` at bandwidth `4/3`. |
| 5 | The one question | Can the gluing calculus of the windows prove a margin exponent below `½` with no input on zeros? |
| 6 | The same without signs and spectra | Is `3/5` a wall of the Möbius descent or of the Gauss class: does a source with an independent reflection exist at a lower price? |
| 7 | A field for the walls | Exponent dynamics of the critical strip: rulers, levers, seeds, fixed points, stage maps. |
| 8 | A field without signs and spectra | Power operations on `L`-functions: operations that act on the abscissa and reach the unit `ζ` with an independent bound. |
| 9 | `𝔽₁` | Six stages with gates. The two that decide: Weil's inequality for `𝔽_q[T]` inside the window calculus; a symmetry that scales the form, or the theorem that none exists. |
| 10 | Close WD | WD is a ruler. Closing it as a proof needs an estimate at exponent zero; stages D1–D6 end in a closure record with six survivors. |
| 11 | Close ACS | A continuity method with openness proved and closedness missing; stages A1–A7; the acid test is the function field. |
| 12 | Galois theory of zeros | GTZ plus four directions (representation ring, operations, orbits of characters, products). Orders of zeros can be governed; location enters only through the position of conjugation. |
| 13 | RH false | Three worlds; the constraints on any off-line zero; no strategy that is not the mirror image of a proof attempt; a localization chain that lacks its first link. |
| 14 | Missed opportunities | Eleven assemblies with no hypothesis (§14.1). None touches the atoms or the exponent `7/8`. |

---

## 1. Big picture: obstacles solved, obstacles left

### 1.1 The shape of the corpus

The corpus has three kinds of theorems about the zeros of `ζ`, and the distance to a proof of RH is the distance between them.

**One producer.** A producer is a theorem that yields a zero-free half-plane with no hypothesis on zeros. The corpus has
exactly one: the metaplectic Möbius descent. Its headline statements are in
`MetaplecticMobiusDescent/Detector/QuasiRiemannHypothesis.lean` [L]:

| Statement | Lean |
|---|---|
| `ζ(s) ≠ 0` for `Re s > 7/8`; every zero with `Re s > 0` has `1/8 ≤ Re s ≤ 7/8` | `riemannZeta_ne_zero_of_seven_eighths_lt_re`, `riemannZeta_zero_mem_quasiRH_strip` |
| `L(s, χ) ≠ 0` for `Re s > 7/8`, every Dirichlet character of every modulus | `DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re` |
| the same for the Hecke family of `ℚ(ω)`: finite-order residue characters of `ℤ[ω]` trivial on units (`HeckeFamily.Character`) | `hecke_nonzero` |
| `w ≤ 3/8` | `SquareRootThreshold.zetaZeroWidth_le_three_eighths` |

**Many receivers.** A receiver is an exact dictionary between the width and the exponent of one arithmetic or geometric
quantity. At exponent zero each receiver is an RH-equivalent; none of them produces its own input.

| Receiver | Dictionary | Lean | Exponent the 7/8 theorem gives |
|---|---|---|---|
| Möbius signal | `Θ ≤ b` iff the signal is `O(Z^{b'})` for every `b' > b` | `zetaZeroAbscissa_le_iff_forall_signal_le` [S] | `7/8` |
| Möbius polynomial at one height | `w ≤ β` iff `\|M_X(½ + it₀)\| ≤ C X^{β+ε}` for all `X` | `zetaZeroWidth_le_iff_pointwise` [L] | `3/8` |
| Mollified moment on `[0,1]` | `w ≤ β` iff `∫₀¹\|ζM_X\|² ≤ B X^{2(β+ε)}` | `zetaZeroWidth_le_iff_unit_window` [S] | `3/4` |
| Long moments (WD) | pure moment `≤ C T^{4+2wθ}`, mollified `≤ C T^{6+2wθ}`; a cofinal slope `2β` with one `K` gives `w ≤ β` | `exists_pure_moebius_moment_le_zetaZeroWidth`, `zetaZeroWidth_le_of_cofinal_moebius_mollifier_slope` [S] | slope `3/4` |
| Zeros of the Möbius polynomials | they condense exactly on `Re s = Θ` | `exists_zero_moebiusPoly_near`, `eventually_moebiusPoly_ne_zero` [R] | no zeros accumulate right of `7/8` |
| Margin of the neutral windows (ACS) | margin `≥ −C K^θ` on ratio `3K + 1`, `θ < ½`, gives `w ≤ θ`; converse open | `zetaZeroWidth_le_of_neutralWindow_marginRate` [S] | `3/8 + ε` if the converse holds |
| Dressed positivity (JAS) | signal `O(Z^b)` gives PSD level `b + ½ + ε` | [R] | level `11/8 + ε` |
| Heat flow | `Λ ≤ w²/2`; heat threshold `≤ w²/3` | `newmanConstant_le_half_sq_zetaZeroWidth`, `wdHeatThreshold_le_third_sq_zetaZeroWidth` [S] | `Λ ≤ 9/128` |
| Integer degrees (Stepanov count) | crude bound `\|c_B(log k²)\| ≤ k^{2σ}` iff a zero-free strip | `SurfaceOfSpecZ.zetaZeroWidth_le_iff_crude_integerDegrees` [R] | strip of width `3/8` |
| Prime trace moments (weights) | `2k`-th moment `≤ C N^{1+A}`, `1 + \|A\| < k`, gives `w ≤ (1 + \|A\|)/(2k)` | `zetaZeroWidth_le_of_primeTraceMoment_le` [R] | — |
| Weil lag | lag `≤` total weight times `e^{3L/8}` | `three_eighths_endpoint_bounds` [S] | proved |
| Window visibility | positivity at aperture `R ≥ e⁶` excludes depth `≥ 1/R` for zeros of height `2 ≤ \|γ\| ≤ H(R)`, a horizon that depends on `R` | `zeta_abs_re_sub_half_lt_of_le_onsetAperture` [S] | — |
| Overlap of the complete Weil matrix | tilted unit spline: positive definite for `1 ≤ c ≤ 2K(log N)^{1/8}` at one `K > 0`; eventual nonnegativity at overlap `2(log N)^α`, `α > ¼`, iff RH | `exists_critical_multiple_completeWeilMatrix_posDef`, `tiltedUnitSpline_overlap_window` [S] | — |

**Three atoms.** RH factors exactly: `RH ⇔ ZAL ∧ B13 ∧ Landing` (`riemannHypothesis_iff_three_atoms` [L]), equivalently
`RH ⇔ ZAL ∧ AAL` (`riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw` [S]). AAL says: for every `h ≥ 0`
the zeros right of `½ + h` are none or infinitely many (`asymptoticAbscissaLaw_iff_encard_rightOf_le_one` [L]). B13 is a
dichotomy of one index: the negative index of the real packets is `0` or `∞`
(`finiteOffLine_imp_rh_iff_packetIndex_zero_or_infinite` [L]).

### 1.2 Hard obstacles solved

| Obstacle | What is proved | Source |
|---|---|---|
| A zero-free half-plane | `Θ ≤ 7/8` for `ζ`, all Dirichlet `L`-functions, the Hecke family of `ℚ(ω)` | MMD [L] |
| Where the producer ends | Every Möbius-signed Gauss/Jacobi pairing `(c, k)` has uncoupled boundary `(c+1)/k ≥ 2/3`, tower fixed point `c/(k−1) ≥ 3/5` with equality only at `(3, 6)`, and one-step boundary `(c+½)/k ≥ 7/12`; none reaches `c ≤ (k−1)/2` | `three_fifths_le_coupledBarrier`, `coupledBarrier_eq_three_fifths_iff`, `not_exists_moebiusGaussPairing_reaching_critical_line` [S] |
| Where the frame wall is | The continued probe correction vanishes at `s` iff `L(6s − 3, ψ₆χ) = 0`; it is nonzero on `Re s ≥ 2/3`, has infinitely many zeros in `7/12 ≤ Re s < 2/3`, and no nonvanishing continuation below `7/12` | `continuedProbeCorrection_eq_zero_iff` [L], `infinite_zeros_continuedProbeCorrection_in_strip` [S] |
| Where the estimates stop | Binding bin `7/8` (a vertex), floor bin `13/15`, free reflection-sieve floor `5/6`; crossing a floor needs a saving before Cauchy–Schwarz | `norm_sq_bilinearFloorSum_le_mul_signedGram`, `escape_below_free_floor_bound` [S] |
| What RH consists of | Three atoms; AAL characterized; B13 as an index dichotomy | ELT, FFA, ACS [L] |
| Which hypotheses cannot suffice | Every finite layer is realized by an integer-norm Euler product with linear counting; every finite layer is realized with the functional equation; the compact Selberg zeta has Euler product, functional equation and a finite nonempty off-line set; a Beurling system with unit multiplicity and decaying functional-equation defect is the rational primes | FFA, IRW, CompactHyperbolicSurfaces, EulerFETransport [R] |
| ACS as a statement about windows | RH iff at every cutoff the neutral windows have a common gap; the gap is needed only on windows of index one; index of the neutral part `= 1 +` number of zeros right of the line | `riemannHypothesis_iff_exists_gap_neutralWindow`, `riemannHypothesis_of_gap_of_bound_windows`, `exists_le_hermNegIndex_neutralWindow_iff` [L] |
| A first selective sign | Floor `10⁻¹³` at aperture `log 2` at every block size for ratio `< 4`; first step with gap `1/50000`; the sign twin fails the first overlap step | `weilFloor_apertureLogTwo`, `neutralWindow_floor_two_prime_window` [S], GCW [R] |
| Whole-space positivity at growing overlap | The complete Weil matrix of the tilted unit spline is positive definite uniformly for `1 ≤ c ≤ (log N)^α`, every `α < 1/8`, and up to `2K(log N)^{1/8}` for one `K`; at fixed overlap its low spectrum is the completed conductor spectrum | `eventually_tiltedUnitSpline_completeWeilMatrix_posDef_below_one_eighth`, `exists_critical_multiple_completeWeilMatrix_posDef` [S]; RAPT [R] |
| Where the sign comes from in Hodge-index language | The sign hypothesis is a gauge fixing by the archimedean place and selects the Euler point; trickle-down over `𝔽_q` is the square-root count; for `ζ` the Hodge index holds on a fixed fraction of the atomic spacing; every symmetry over `ℤ` is an isometry | ALG: `exists_nonneg_gauge_iff`, `forall_weightedTrickleDown_iff_exists_pointCount_ge`, `atomicIntersectionGram_isHyperbolic`, `boost_isometry` [R] |
| Width as a local reading | The width is read at one height by all prefix lengths, or on one unit window | MZF [L] |
| Proportion | Simple critical zeros `≥ 0.67250071` (imported census); exact exchange rates for `70%` and `75%`; positivity alone reaches neither | `simple_critical_proportion_ge_67250071`, `positivity_does_not_reach_seventy_percent_at_any_bandwidth` [S] |
| Heat flow | `Λ ≤ 1/8`; the nonreal count `N(t)` is nonincreasing and right-continuous at `0`; RH iff `N(t) = 0` for small `t > 0`; the forward monodromy group has index at most two in the signed permutations | RHTower/Heat, GTZ [S] |
| Sign-free inputs | The integrality lattice of the horizon is exact and its floor attained; five of Deligne's six moves; fixed-shift logarithmic Chowla; Brauer induction; the density bound with exponent `30/13` | ASRP, AWT, `tendsto_logAvg_liouville_shift`, `brauer_induction`, `exists_zeroHeightBox_ncard_le_thirtyThirteenths` [R/S] |

### 1.3 Obstacles left before a proof or a falsification

| # | Obstacle | Exact form in the corpus |
|---|---|---|
| O1 | No second producer | Every route except MMD is a receiver. Its dictionary is exact and its input is missing. |
| O2 | The producer class is closed | Inside the class: the estimates stop at the vertex `7/8`; the floors `13/15`, `5/6` need signed savings; the frame wall `2/3` needs a zero-free half-plane for the weight-one sextic Grössencharacter family, which is not in the Hecke family of the 7/8 theorem. Below `3/5`: no pairing exists. |
| O3 | Half-plane to line | No theorem turns `Θ ≤ b` into `Θ ≤ b' < b` for `ζ` alone. The one statement of that shape, the return transfer, is equivalent to RH under a strip `Θ < 1` (FCT, `TheReturnTransferIsTheRiemannHypothesisUnderAStrip` [R]); the strip is a theorem, so the transfer is RH. |
| O4 | The atoms | ZAL, B13, Landing are open. The fakes of §1.2 show that each needs Euler product, functional equation and integrality together, and those three together determine `ζ`. |
| O5 | ACS | An a priori gap on bound windows. The Hodge index on a bound window gives gap `≥ 0` and no more; a positive gap from boundness alone is RH (GCW [R]). |
| O6 | WD | One `K` for unbounded mollifier length; the long branch pays the negative moments `Σ\|ρζ′(ρ)\|^{−2}` (`not_forall_moebiusPoly_energy_le` [R]). |
| O7 | Sign-free routes | Stepanov's count needs vanishing that is cheap and exact, and no place supplies both (ALST [R]); Deligne's sixth move, the a priori pole location, is missing and `ζ` is the fixed part of every family (AWT [R]); the Galois route needs a restriction on the position of complex conjugation and none is known (GTZ [R]). |
| O8 | Falsification | No structural statement forces an off-line zero. The corpus has the constraints such a zero obeys and the localization theorems (§13). |

### 1.4 Reading: one wall, seen from every route [D]

**A point from a law.** Every theorem of §1.2 is about a family (twists, rows, characters), a mean (moments,
proportions), a half-plane (an exponent) or a finite stage (aperture, window ratio, prefix length, height). RH is about one
function on one line. In each route the open step is the same passage to a limit, and in each route the corpus has both
halves of the reason it is open: an equivalence saying the limit statement is RH, and a no-go saying the finite stages do
not decide it.

| Route | Finite stage (proved) | Limit (equivalent to RH) | Why the stages do not decide |
|---|---|---|---|
| Producer | half-plane `7/8` | exponent `½` | tower fixed point `≥ 3/5` |
| ACS | gap at ratio `< 4`, every block size | gap at every ratio | a fixed aperture reads zeros only up to a finite height: in a background of logarithmic density `L` a pair of multiplicity `k` at depth `δ` hides while `2δa ≤ log(4δL/k)` (`windowPositiveAt_multiplicityPairConfig_of_le_log` [S]); a zero of depth `1/a` hides above height `e^{4a}` (`exists_hidden_inv_aperture_zero_above_single_exp` [S]) |
| Complete Weil matrix | positive definite up to overlap `2K(log N)^{1/8}`, one `K` | nonnegative at overlap `(log N)^α`, `α > ¼` | the reserve of the small multiple does not decide the sign at larger multiples (CACT [R]) |
| WD | moment bounds at bounded length | one `K` at unbounded length | short mollifiers leave the last-scale defect (MZF [R]) |
| Proportion | `0.6725` | `1` | positivity cost `≥ 1 + 3/π²` |
| Heat | `Λ ≤ 1/8`, `Λ ≤ w²/2` | no nonreal zero at small positive time | the bound is the width again |
| Families (AWT, CRF, GTZ) | generic member | trivial member `ζ` | `ζ` is the fixed part; row averages are blind to the target mode |
| Atoms | finite layers excluded on models | no layer | models with every finite layer exist |

**A wall is a fixed point.** In the one route that has a transport of half-planes, the wall is computed: a pairing `(c, k)`
transports `Θ ≤ b` to `Θ ≤ (c + b)/k` and stops at the fixed point `c/(k − 1)`
(`abscissa_le_max_fixedPoint_of_tower` [S]). Two consequences. (i) Mixing pairings does not help: the fixed point of a
composite `T₁ ∘ T₂` is `(c₁k₂ + c₂)/(k₁k₂ − 1)`, a convex combination of `c₁/(k₁ − 1)` and `c₂/(k₂ − 1)` with weights
`k₂(k₁ − 1)/(k₁k₂ − 1)` and `(k₂ − 1)/(k₁k₂ − 1)`, so every mixed tower stays at `≥ 3/5`. (ii) The line is the fixed point
only of a transport centred on the line, `c = (k − 1)/2`. In the Gauss class the Möbius sign has a price: the parity law
forces at least two characters of order `≥ 3`, each completed factor of order `m` costs `(½ − 1/m)k` and each row twist
`k/2 − 1`, and the total is `c ≥ (2/3)k − 1` (`two_thirds_mul_period_sub_one_le_pairingC` [S]). Quadratic factors are free
and carry no sign. The Liouville identity `Σλ(n)n^{−s} = ζ(2s)/ζ(s)` has `(c, k) = (0, 2)` and a frame that reaches the
line, and no reflection. The two requirements, a reflection and a frame on the line, are each satisfiable and are not
satisfied together by any object in the corpus (CRF topic 5 [R]).

**What a proof needs.** Either a transport with fixed point `½` (a second producer or an amplifier of the 7/8 strip), or
the atoms one by one. Everything else in the corpus measures the width; nothing else moves it.

---

## 2. Opportunities

Ranked by whether a proof step is available. "Unconditional" means: a theorem with no hypothesis on zeros.

| # | Opportunity | Lean objects it starts from | First lemma | Payoff |
|---|---|---|---|---|
| 1 | Exchange the 7/8 theorem at every receiver | table of §1.1; `zetaZeroWidth_le_three_eighths` | one instantiation per receiver (list in §14) | unconditional bounds on `M(x)`, Möbius polynomials, moments, `Λ`, PSD level; uniform statements in arithmetic progressions |
| 2 | Converse rate law for the neutral margin | `zetaZeroWidth_le_of_neutralWindow_marginRate`, `MarginRate`; converse proved for the odd states of the ends (MAFT [R]) | width `θ` gives margin `≥ −C_ε ρ^{θ+ε}` for all packets | unconditional margin exponent `3/8 + ε`; the margin exponent becomes an exact ruler of the width (§5) |
| 3 | The Grössencharacter rung | `grossenLFunction 𝔪 ψ k`, `continuedProbeCorrection_eq_zero_iff` | the 7/8 machine for weight `k ≥ 1` sextic Grössencharacters of `ℚ(ω)` | the correction is zero-free on `Re s > 31/48` (zeros have `Re(6s − 3) ≤ 7/8`) [D]; the frame wall is at `31/48`, below `2/3` |
| 4 | A saving before Cauchy–Schwarz at the floor bin | `norm_sq_bilinearFloorSum_le_mul_signedGram`, `escape_below_free_floor_bound` | a power saving `s` in the signed Gram off-diagonal | half-plane `5/6 − s`: `¾` at `s = 1/12`, `2/3` at `s = 1/6` |
| 5 | The probe over `𝔽_q[T]`, `q ≡ 1 mod 6` | CRF topic 6 [R]; nothing built | exact evaluation of the row first moment where the Kubota series is rational | decides whether the floors `13/15`, `5/6` are losses of estimation or structure |
| 6 | Parity of the off-line count | `eight_dvd_nonrealZeroCount` [L], `eventually_nonrealZeroCount_eq_of_finite` [S] | assembly (§14.1, item 10) | proper forward monodromy and finitely many off-line zeros give an even number of quartets |
| 7 | Heilbronn characters | `brauer_induction`, Artin completions with functional equation (AGZ) | `ord_{s₀} L(s, ·)` is additive on virtual characters | multiplicity laws for zeros of Dedekind zeta functions (§12) |
| 8 | Signed surplus at bandwidth `4/3` | `primeCoalescentSurplus`, `PrimeCoalescentSurplusAtMost` | surplus `≤ (1/18 + o(1)) N(T, 2T)` for one profile | `75%` simple critical zeros; any `β < 5/36` beats `2/3` (TTPC [R]) |
| 9 | Cofactor cancellation | growing-order Gaussian current, centred type-II cofactors (ELT [R]) | prime-weighted restricted cofactor cancellation | a current that sees an isolated top quartet (B13) |
| 10 | Next apertures of ACS | GCW, WTZ | floors at `ρ = 2.25, 2.53, 3.21`; fourth ladder excess at `Q = 2` | certified range of the continuity method (§11) |

Opportunities 1, 2, 3, 6, 7 are unconditional statements whose inputs are in the corpus. Opportunities 4, 5, 8, 9 need an
estimate the corpus does not have; each names it.

---

## 3. Is there a clear path to quasi-RH?

Quasi-RH in the sense `Θ < 1` is a theorem of the corpus: `Θ ≤ 7/8` [L]. The live question is a smaller exponent. There is
no clear path below `7/8`; there is a complete map of what each exponent costs.

Half-plane as a function of the twist exponent `θ` at `n = 6`: `½ + (5/12)θ`. Floor escape:
`θ ≥ 4/5 − (12/5)s` for a bilinear saving `s`.

| Half-plane | What it needs | Status |
|---|---|---|
| `7/8` | binding bin, `θ = 9/10` | proved; the optimum of the published geometry lies in `(7/8 − 1/2500, 7/8]` (walk card [R]) |
| `13/15` | floor bin, `θ = 22/25` | needs a different row count in the binding bin; the tuple-sum bias (walk C9) is open |
| `5/6` | free reflection-sieve floor, `θ = 4/5` | needs the row mean square at its generic size |
| `¾` | saving `s = 1/12` before Cauchy–Schwarz | no estimate |
| `2/3` | saving `s = 1/6`; frame wall of the uncoupled correction | no estimate; wall proved |
| `31/48` | the Grössencharacter rung at `7/8` | rung not proved [D] |
| `3/5` | all rungs of the tower and every estimate at `3/5` | fixed point of the class; attained only by the cubic–sextic pairing |
| `7/12` | GRH for the Grössencharacter in the correction | conditional; below it no nonvanishing continuation |
| `½` | saving `s = 1/3` and a pairing with `c ≤ (k − 1)/2` | no such pairing exists [S] |

Three statements follow.

1. The first step below `7/8` is not a matter of constants: `7/8` is a vertex of the exponent polytope, and the next two
   floors are set by taking absolute values across rows and by Cauchy–Schwarz between rows and columns. Each is crossed
   only by a signed estimate.
2. The descent has two independent ladders. The estimates (`σ₀`) bind first; the frame (the tower) binds at `2/3` and
   ends at `3/5`. The frame ladder has an unconditional rung available (opportunity 3); the estimate ladder does not.
3. For other `L`-functions: Dirichlet characters of every modulus and the Hecke family of `ℚ(ω)` are covered. Hecke
   characters of other number fields, Grössencharacters with infinity type and Artin `L`-functions are not
   (frontier map, ACS entry [R]).

Verdict: quasi-RH is proved; an improvement of the exponent has a map and no path; `Θ < 3/5` is unreachable by the
producer class as a theorem.

---

## 4. Is there a clear path to at least 70% of the zeros on the line?

No. The corpus has the exact exchange rates, and the input they call for is missing.

**State.** `simple_critical_proportion_ge_67250071` [S]: at least `0.67250071` of the zeros are simple and on the line.
The statement rests on the imported census `Zeta23` and the local pair-correlation constant `HD(1)`.

**Exchange rates (TTPC [R]).** The Gram certificate gives the simple critical proportion `2 − κ`.

| Bandwidth | `κ` | Proportion | Input |
|---|---|---|---|
| `λ ≤ 1` | `1/λ + λ/3 ≥ 4/3` | `≤ 2/3` | pair correlation in `\|α\| ≤ 1` (known) |
| `λ = 4/3` | `9/8 + (9/8) I`, `I = ∫₁^{4/3}(4/3 − α) F(α) dα` | `75%` iff `I ≤ 1/9`; `70%` iff `I ≤ 7/45` | `F` beyond `α = 1` |

GUE has `I = 1/18` (proportion `13/16`). A pointwise bound `F ≤ Υ` on `(1, 4/3]` gives `I ≤ Υ/18`: `75%` iff `Υ ≤ 2`, and
`70%` iff `Υ ≤ 14/5` [D]. The sieve majorant gives `I ≤ 8/27`, above both thresholds. The unsigned additive sieve would
need `Υ ≤ 8/9` against the parity factor `2`.

**No-go.** `positivity_does_not_reach_seventy_percent_at_any_bandwidth` [S]: at every bandwidth, a nonnegative `F` that
agrees with the known range costs more than `13/10`. Sub-threshold data and positivity do not certify `70%`.

**The dichotomy that is proved.** `critical_proportion_or_simple_offLine θ` [S]: either a proportion `θ` of zeros is on
the line, or a proportion `1 + HD(1) − 2θ − ε` of zeros is simple and off the line near it. At `θ = 7/10`: `27.25%`
simple off-line zeros. So a proof of `70%` can also go through an upper bound for simple off-line zeros near the line.

**The mollifier side.** A real unit-bounded mollifier of length `T^θ` has normalized moment `≥ 1 + 1/(8 + 6θ)`
(`necessary_length` [L]); MZF proves a positive proportion at `θ = 13/50` with a small constant. Long mollifiers reach
`70%` only with twisted moments beyond the lengths the corpus controls (`N ≤ U^{21/50}`,
`exists_twisted_second_moment_le` [S]).

**The missing input, stated once.** A signed bound for prime pairs beyond the diagonal range: the coalescent surplus
`≤ (7/45 + o(1))·`normalization at bandwidth `4/3`, or `F ≤ 14/5` on `(1, 4/3]`. Unsigned bounds lose the parity
factor. The 7/8 theorem does not enter: the certificate is local to the line.

---

## 5. The one question

### 5.1 The filter

A question is admitted here if it passes seven tests. (T1) It is not equivalent to RH or to one of the three atoms.
(T2) It is decided by a proof or a refutation, not by a computation. (T3) Its positive answer has a consequence that is a
theorem of the corpus. (T4) No finite window decides it. (T5) It is false on at least one fake of the corpus. (T6) The
input it needs is named, and no Lean theorem refutes that input. (T7) It is not of a shape the corpus has answered.

No statement `X` with `X ⇒ RH` strictly below the atoms passes. Every candidate found is an atom (ZAL, B13, Landing), a
receiver at exponent zero (an RH-equivalent), or true on a fake. The question below is not of the form `X ⇒ RH`. It asks
for the second producer, at the place where the corpus has the most structure for one.

### 5.2 The question: can the window calculus produce a half-plane?

**Setting.**
- [S] `zetaZeroWidth_le_of_neutralWindow_marginRate`: if for some `0 ≤ θ < ½` and `C` every shifted window
  `neutralWindow (3K+1) R (3KR) + C·K^θ` has negative index at most one, then `w ≤ θ`.
- [S] `riemannHypothesis_iff_initialWindow_margin_bddBelow`: RH iff one constant shift works for the initial windows at
  every ratio.
- [R] The shift `C·K^{1/2}` works with no hypothesis: the binding energy is of order `√ρ` and is carried by the long maps
  between the two ends of a window (MAFT).

Define the **margin exponent** `θ_ACS` as the infimum of the `θ ∈ [0, ½]` for which such a `C` exists. Then
`w ≤ θ_ACS ≤ ½`.

**Question.** Is `θ_ACS < ½` provable from the gluing calculus of the windows (Green matrices of the middle, floor trees,
overlap steps), with no statement about zeros as an input?

**Why it is less than RH and less than a better quasi-RH.** By the first lemma below and the 7/8 theorem,
`θ_ACS ≤ 3/8`: the statement asked for is true for every `θ > 3/8`. What is asked is a proof by a different calculus.

**Why its answer is a breakthrough in both directions.**
- *Yes.* A second producer exists, and it is centred: the window is symmetric under the functional equation, a gluing
  step has no frame cost, and the same recursion with bounded loss is RH. The wall of the producer class (fixed point
  `≥ 3/5`, §1.4) does not apply to it. It is the first zero-free half-plane obtained from a sign.
- *No* (a fake with the same gluing data and margin exponent `½`). The window calculus is a ruler and not a lever. ACS
  closes as a producer, and with it every route whose input is the same gluing data; the exact dictionary stays.

**First lemma: the ruler is exact.** `w ≤ β` implies margin `≥ −C_ε K^{β+ε}` for all packets. MAFT has it for the odd
states of the two ends [R]. Its consequence is a theorem about finite integer matrices with no hypothesis: every neutral
window of ratio `3K + 1`, at every block size, has at most one eigenvalue below `−C_ε K^{3/8+ε}` [D].

**Second lemma: a doubling inequality.** `loss(2K) ≤ λ·loss(K) + C` for the loss of the margin under one balanced
gluing. The trivial value is `λ = √2`. Any `λ < √2` gives `θ_ACS ≤ log₂ λ < ½`. The 7/8 theorem predicts that
`λ = 2^{3/8+ε}` is true. RH is `λ = 1` with summable additive terms [D]. MAFT lists the contraction of the conditional
coupling at the balanced split as open [R]; GCW bounds the excess of one overlap step by a coupling norm
(`windowExcess_le_couplingNorm` [S]).

**Tests.**

| Test | Verdict |
|---|---|
| T1 | a half-plane statement; at `θ ∈ (3/8, ½)` it follows from a proved theorem once the first lemma holds |
| T2, T4 | all `K` and all `R` |
| T3 | `zetaZeroWidth_le_of_neutralWindow_marginRate` |
| T5 | the sign twin `ω₂ = −1` has index `≥ 2` at ratio `≥ 3` [R], so a sign-blind bound for the coupling cannot give the saving; an integer-norm Euler model with zeros on `Re s = Θ` has margin exponent `Θ − ½` once the dictionary is proved for models [D] |
| T6 | inputs: the first lemma; the contraction at the balanced split. The no-gos of the corpus (fixed-rank gluing at ratio four, truncation to the prime 2, sign-blind Green bounds) exclude classes of proofs, not the statement |
| T7 | MAFT poses the converse; the comparison of the calculus with the exponent of the producer is not posed in the corpus |

**What it does not give.** RH needs exponent zero with a bounded constant. A proof of `θ_ACS ≤ 3/8` by the calculus does
not move `Θ`.

### 5.3 Runner-up questions

| Question | First lemma | What the answer gives | Why second |
|---|---|---|---|
| The Grössencharacter rung: is the 7/8 theorem true for `grossenLFunction 𝔪 ψ k`, weight `k ≥ 1`? | the probe for a family with infinity type | the frame wall is at `31/48` | moves a wall the estimates do not reach (they stop at `7/8`) |
| The exact probe over `𝔽_q[T]`: are the floors `13/15`, `5/6` attained where the Kubota series is rational? | row first moment in closed form | separates loss of estimation from structure | a calibration, no statement over `ℤ` |
| The critical exponent of the complete Weil matrix: is positivity at overlap `(log N)^α` a theorem for `1/8 ≤ α ≤ ¼`, or is it RH there? | the band–far budget `c⁸ = o(log N)` of the proof below `1/8` | the exact scale at which whole-space positivity turns into RH | an RH-receiver on one side |
| Cofactor cancellation: prime-weighted restricted cofactors against the residue of an isolated top quartet | the signed estimate named by ELT | B13 for a top layer | an atom; the pick of the peer summary |
| Peer summary §2.4–2.6, §2.21: floor at aperture `½ log 5`; survival of the target mode in the kernel of a family-residue operator; descent of local divisor orders; B13 by defect replication | as stated there [R] | as stated there | not re-posed here |

---

## 6. The one question if signs and spectra are excluded

### 6.1 Reading of the exclusion

Excluded: every argument whose engine is the sign of a quadratic or Hermitian form (Weil's criterion, Hodge index, Gram
and PSD certificates, Li coefficients, de Branges spaces, the neutral windows, joint ancestry), and every realization of
the zeros as a spectrum or as resonances. Kept: inequalities used as estimates inside an argument whose engine is an
identity (Cauchy–Schwarz, large sieve). Under the strictest reading, where no inequality that comes from a positive form
may be used, the classical zero-free region is excluded as well (it rests on `3 + 4cos θ + cos 2θ ≥ 0`) and nothing
analytic is left. This report uses the first reading.

### 6.2 What is left

| Kept | Engine | State |
|---|---|---|
| Producer (MMD, FCT, CRF) | exact Möbius-signed identity, reflection, estimates | `7/8`; the class ends at `3/5` |
| Moments (WD, MZF) | mean values of Dirichlet polynomials | exact ruler; the long branch outputs eventual depth bounds |
| Integrality (ALST, ASRP, AET, TTPO) | a nonzero integer is at least one | the lattice of the horizon is exact; Stepanov's vanishing is missing |
| Monodromy and Galois (GTZ, heat cover) | groups and parity | index at most two; the sign of the forward group is open |
| Rigidity (EulerFETransport, IRW, FFA, ELT) | Euler product, functional equation, integrality together | Beurling rigidity; finite layers exist on fakes |
| Counting (density, census) | zero-density, proportions | exponent `30/13`; `0.6725` |

Removed: ACS, WTZ, GCW, MAFT, ALG, HF, RW, JAS, CACT, the geometry of `𝔽₁` as a Hodge-index geometry, the AdS and
ringdown dictionaries, and every Hilbert–Pólya reading.

### 6.3 The two skeletons of a sign-free proof

1. A producer whose transport has fixed point `½`.
2. The three atoms. ZAL has an engine: bounded dyadic mollified moments at length `T^θ`, `θ > ½`, give eventual depth
   `< 1/(2θ) + ε` (`eventual_depth_bound_of_dyadic_moebius_moment` [L]); for every `θ` this is ZAL [D]. B13 has a
   candidate engine, the growing-order current of ELT, with one missing signed estimate. Landing has no engine in the
   corpus.

### 6.4 The question: is 3/5 a wall of the method or of the Gauss class?

**Setting.** A *source* is an exact identity that writes a Möbius-signed Dirichlet series of complete exponential sums as
a quotient containing `ζ` at a dilated argument `ks − c`, with a reflection (a functional equation for the dual sums)
that makes independent estimates possible. For monomials in Gauss and Jacobi sums the classification is a theorem [S]:
the Möbius sign holds iff (`Π = 1` and `r` odd) or (`Π` quadratic and `r` even); at least two factors are not quadratic
(`two_le_length_nonQuadraticPart`); `c ≥ (2/3)k − 1`; the fixed point is `≥ 3/5`.

**Question.** Does a source exist outside the Gauss class with `c/(k − 1) < 3/5`? In other words: is the pair (Möbius
sign, reflection) available at a price below two non-quadratic Gauss factors?

**Why the two classical identities at order two do not answer it [D].** The Liouville identity
`Σλ(n)n^{−s} = ζ(2s)/ζ(s)` has its correction at dilation two (transport `b ↦ b/2`, fixed point below the line) and no
reflection. The Eisenstein series, `ζ(2s)E(z, s) = ½Σ_{(m,n)≠0} y^s|mz + n|^{−2s}`, has target `ζ(2s)`, no correction,
and a reflection; the reflection is circular: the functional equation of `E` contains the quotient `ξ(2s − 1)/ξ(2s)`,
the target itself. At order two the root number is a character and the reflection of the Möbius-signed side returns the
unknown. At order `≥ 3` the root numbers are Gauss sums with their own generating series (the theta functions of the
cubic and sextic covers), the reflection is independent of the target, and each such factor costs weight. The question
asks whether an independent reflection exists at a lower price.

**Why its answer is a breakthrough in both directions.** *Yes*: a frame below every Gauss pairing; with
`c ≤ (k − 1)/2` the frame reaches the line and the problem moves to estimates. *No*: with signs excluded no producer
reaches below `3/5`, as a theorem, and a sign-free proof has to be skeleton 2.

**First lemma: abelian rigidity [D, classical input not in the corpus].** A multiplicative `a(d)` whose value at a prime
is a monomial in Gauss sums of characters of `𝔽_p^×` of pure absolute value is a pairing of the corpus class: all
multiplicative relations among Gauss sums come from the norm relation, the reflection `g(χ)g(χ̄) = χ(−1)p` and the
product relation of Hasse and Davenport, up to sign (Stickelberger; Hasse's conjecture). Built natively, this closes the
abelian case with the theorem `three_fifths_le_coupledBarrier`.

**Second lemma: rank at least two.** For local sums of Kloosterman type, `Σμ(d)a(d)d^{−s}` is `1/L(π, s)` times a
correction at `2s`. The identity of the corpus, `μ(d)a_E(d) = Σ_x (f(x)/d)`, gives `1/(L(E, s)ζ(2s − 1))` and has no
reflection (walk ledger [R]). `ζ` enters such a source only through a trivial constituent. To prove: a source of rank
`≥ 2` whose target contains `ζ(ks − c)` has `c/(k − 1) ≥ 3/5`; or to exhibit one below.

**Third lemma: convexity.** Composites of sources stay above the best single fixed point (§1.4) [D]. The answer is
decided on single sources.

**Tests.** T1: a classification of identities. T2, T4: no window is involved. T3:
`abscissa_le_max_fixedPoint_of_tower` turns a source with estimates into a bound for `Θ`. T5: the two identities at
order two above are sources without an independent reflection. T6: the named input is a theta function whose coefficients are
Gauss sums of order `n`; the corpus has `n = 3` (walk ledger C10 [R]). T7: the Gauss class is answered; its complement
is not.

### 6.5 Runner-up questions under the exclusion

| Question | State |
|---|---|
| Stepanov's vanishing over `ℤ`: an auxiliary function with cheap and exact vanishing | exact order costs one unit of `log₂ N` per order for integer auxiliaries (`two_pow_le_length_of_vanishesToOrder` [R]); inseparability exists at each finite place and not at the archimedean one |
| The Siegel half at square-root precision | the lattice of the horizon is exact and attains its floor; the precision is lost in the analytic ceiling (ASRP [R]) |
| The sign of the forward monodromy group | one simple complex collision off the centre has `k = 0`, `c = 1` and violates both parity laws, so `G₊ = W` is expected [D]; a proper `G₊` would force collision masses divisible by eight |
| An isolated top quartet | the cofactor estimate of ELT |

---

## 7. The walls as questions without tools: a field

### 7.1 What the walls say

The walls ledger has three families. P (production): an estimate at exponent zero is missing and every route that needs
it is a receiver. U (uniform exclusion): a statement holds at every finite stage and its limit is RH. R (faithful
realization): the object that would carry the sign does not exist in finite type. Read together: the corpus has many
ways to measure `Θ` and one way to move it. The tools that are missing concern maps on exponents and maps between
stages. No programme of the corpus has these maps as its subject.

### 7.2 The field: exponent dynamics of the critical strip

**Viewpoint.** `Θ` is one number read by many rulers. A proof of RH is a contraction of `[½, 1]` with fixed point `½`
applied to a seed, or a stage recursion whose cumulative loss is bounded. The field studies the maps and their fixed
points, not the readings.

**Objects.**

| Object | Definition | Instances in the corpus |
|---|---|---|
| Ruler | a quantity with an exponent `e` and a two-sided theorem `e = w` | Möbius signal; Möbius polynomial at one height; unit window; zeros of the Möbius polynomials |
| Half ruler | one side only | margin of the windows (`w ≤ θ_ACS`); heat (`Λ ≤ w²/2`; `δ²/(200 log γ) ≤ Λ` from one zero) |
| Lever | a theorem `Θ ≤ b ⇒ Θ ≤ T(b)` with `T(b) < b` | none for `ζ` alone; `T(b) = (c + b)/k` across a tower |
| Seed | a bound with no hypothesis | `7/8` |
| Wall | the largest fixed point of the available levers below the seed | `3/5` (frame); `7/8` (estimates) |
| Centre | the fixed point of a lever; centred means `½` or below | the Liouville identity |
| Price | the contribution of one factor to `c` | `(½ − 1/m)k` per completed factor of order `m`; `k/2 − 1` per row twist |
| Stage | a finite parameter whose limit is the statement | aperture, ratio, mollifier exponent, degree, overlap, height |
| Stage map | a theorem that passes from stage `n` to stage `2n` with a loss | one block of the openness induction; one overlap step |
| Loss exponent | growth rate of the cumulative loss | `½` trivial; `< ½` a half-plane; bounded is RH |

**Principles.**
1. Measuring is not moving. An exact ruler transfers every bound and creates none.
2. A wall is a fixed point. It is crossed by another lever, not by better constants.
3. Convexity. Composites of affine levers stay above the best fixed point.
4. Centring. A lever reaches the line iff its centre is the line; for a dilation, `c = (k − 1)/2`.
5. Independence of the reflection. A reflection that contains the target is circular; an independent one has a price.
6. Action. A law over a family becomes a lever only if the family acts on the abscissa (dilation, tensor power, base
   change). A mean over a family that does not act is blind to its trivial member.
7. Uniformity. A stage statement is worth its constant: one constant for all stages is the theorem, each stage alone is
   a certificate.

**Criteria for a result of the field.** It (i) proves a ruler two-sided, or (ii) lowers a fixed point, or (iii) gives a
ruler a stage map with an explicit loss factor, or (iv) proves that every lever of a class has fixed point `≥ b`, or
(v) supplies a seed for a family. A result that adds a ruler or certifies one more stage is outside the field.

**Questions.**

| # | Question | First theorem |
|---|---|---|
| E1 | Which half rulers are exact? | the converse rate law of the margin for all packets; a two-sided law between `Λ` and `w` |
| E2 | Which rulers have a stage map with loss factor below the trivial one? | the doubling inequality of §5.2; a slope law for long moments from `θ` to `2θ` |
| E3 | Is there a centred lever with an independent reflection? | §6.4 |
| E4 | Is every lever built from complete exponential sums of bounded rank non-centred? | abelian rigidity and convexity |
| E5 | What do the two levers of a function field become over `ℤ`? Tensor powers (a bound for all even powers gives the line) and base change (a count at every `q^n` gives the line) both act on the abscissa. Over `ℤ` the powers `g(χ)^n` are the tensor powers of rank one; they reach `ζ` only through torsion, and torsion of order `≥ 3` has a price | the price law as a statement about weights of rank-one tensor powers [D] |
| E6 | Which families admit a seed? | the Grössencharacter rung; Hecke characters of a second field |
| E7 | For each lever, which property of `ζ` does it use that an integer-norm Euler model with zeros on `Re s = Θ` lacks? | the list, lever by lever |

**Topics.** The exactness of the margin; the doubling law; seeds at 3/8 for every ruler (§14); the closure of the abelian
class; the acid test over `𝔽_q[T]` (prove the gap of the windows there by stage maps, without Weil's theorem);
the critical exponent of the complete Weil matrix between `1/8` and `¼` as a stage problem with two proved ends.

**What the field is not.** It does not replace a route. Its first theorems are §5.2 and §6.4 and items 1, 2, 9 of §14.
Its place among the fields named in the review ledgers (conversion of laws into points, defect transport, gluing of
windows): those have defects, exceptions and windows as objects; this one has the maps on exponents.

---

## 8. The same under the exclusion of signs and spectra: a field

### 8.1 The walls that remain

With signs excluded the walls are P2–P4 (Gauss completion, truncated continuation, loss of phase and target), P6
(restricted cofactors), U2–U4 (long moments, B13, Landing), U6 (heat time zero), R3–R4 and R8 (heat against arithmetic
Galois groups, purity, roots). The sign-free programmes of the corpus are built around identities (FCT, CRF), layers
(ELT, FFA), integrality (ALST, ASRP), orders and monodromy (GTZ) and conversions of laws (CTZ, IRP). The common missing
tool is an operation on `L`-functions that acts on the abscissa, has `ζ` in its range, and comes with a bound that does
not contain the target. The Gauss class is the one built instance; its theory is closed at `3/5`.

### 8.2 The field: power operations on L-functions

**Viewpoint.** Every proof of a Riemann hypothesis without a sign uses a power operation: tensor powers (Deligne), base
change (Stepanov, Bombieri), Newton polygons of a Frobenius power (Carlitz–Goss). `ζ` is the unit for these operations,
and an operation is blind to its unit. The producer of the corpus reaches the unit through torsion: a power of a Gauss
sum of order `m` lands on the trivial character. The field studies power operations on `L`-functions over `ℤ` as maps on
abscissae and asks which of them reach the unit.

**Objects.**

| Object | Definition | In the corpus |
|---|---|---|
| Operation | a map `Φ` on a class of Euler products with `Θ(L) ≤ T_Φ(Θ(Φ L))` | dilation by a pairing `(c, k)` |
| Unit | `ζ`; `Φ(ζ) = ζ` for tensor operations | AWT: `ζ` is the fixed part of every family [R] |
| Torsion point | an object `L` with `Φ^m(L)` containing the unit | characters of order `m`; the cubic and sextic Gauss sums |
| Root-number series | the Dirichlet series of the root numbers of a family | the theta functions of the cubic and sextic covers; Kubota series |
| Independent reflection | a functional equation of the root-number series that does not contain the unit | order `≥ 3` only |
| Price | the weight that one torsion factor contributes | `(½ − 1/m)k` |
| Rung | the next operation in a tower and its seed | Grössencharacter `L`-functions of weight `k` |
| Calibration | the same operation over `𝔽_q[T]` | CRF topic 6; nothing built |

**Language.** Order of torsion, price, centre, independent or circular reflection, rung, seed, unit.

**Principles.**
1. An operation is blind to its unit; the unit is reached through torsion.
2. Torsion of order two is free and its reflection is circular. Torsion of order `≥ 3` has an independent reflection
   and a price.
3. The Möbius sign needs two factors of order `≥ 3` (parity law of the corpus).
4. A tower of operations ends at its fixed point; mixing operations does not go below the best one.
5. An estimate is taken after the identity has isolated the target: norms are blind to parity, to phase and to the
   target mode (`BilinearFormsAreParityBlind`, `TheAverageRowIsBlindToTheTarget` [R]).
6. Calibrate where the root-number series is rational.

**Criteria.** An operation is admitted with three items: the identity, the reflection, and a bound that does not contain
the target. A result counts if it classifies operations of a class, evaluates a root-number moment exactly, supplies a
rung, or proves a lower bound for the centre of a class.

**Questions.**

| # | Question | State |
|---|---|---|
| S1 | Are Gauss monomials the only abelian operations? | classical (Stickelberger, Hasse–Davenport); not in the corpus |
| S2 | Does an operation of rank `≥ 2` reach the unit, and at which centre? | one identity without reflection in the corpus |
| S3 | Is there a theta function with Gauss-sum coefficients of order `n ≥ 4` and a usable reflection? | open (walk ledger C10); the budget of quadratic products at `m ≥ 4` is `≥ 25/28` [R] |
| S4 | The rung: the 7/8 machine for Grössencharacters of weight `k` | not built |
| S5 | Exact row first moments over `𝔽_q[T]` | not built |
| S6 | Which operation over `ℤ` plays the part of base change? On the torsion of the prime torus the Adams operations are a Galois action; on the prime orbit the dilation fixes one point (ALST [R]) | open |

**Topics.** Closure of the abelian class; the price law as a theorem about weights; non-abelian operations (Kloosterman
sheaves, symmetric powers) and their centres; the rung and the wall `31/48`; calibration over `𝔽_q[T]`; the place of the
Chebyshev–Nair stencils (an identity with integrality as its bound and no reflection: slope one is the infimum and is
not attained [R]).

**Relation to the built programmes.** FCT, CRF and the three-fifths theorem are the chapter on Gauss monomials. AWT has
five of Deligne's six moves and names the sixth. ALST has Lefschetz and the self-improvement and names the missing
vanishing. The field is the common statement of what these three lack: an operation that reaches the unit with an
independent bound.

---

## 9. A research programme to construct `𝔽₁`

Aim: a geometry in which `Spec ℤ` has a square and one inequality on that square is a theorem. A definition of `𝔽₁` is
not the aim. No step below is a proof of RH, and no step may assume it.

### 9.1 What the corpus fixes (AGZ, SurfaceOfSpecZ, ACS) [S/R]

| Item | Statement | Lean |
|---|---|---|
| The square | cofree object with Frobenius lifts `ψ_p(a) = a^p + p·b`; ghost ring; `F_k V_k = k`, and `F`, `V` commute only for `k = 1` | `FrobeniusLifts`, `ghostLift`, `frobenius_verschiebung`, `ghost_frobenius_verschiebung_commute_iff` |
| Contacts | `log #ℤ/J(1, n) = Λ(n)`; no object of finite type carries the contacts | `FrobeniusLifts.exists_contact_not_in_square` |
| Intersection numbers | Weil's off-diagonal is jets plus contacts; `Γ_m·Γ_n = √(mn)·(archimedean density + prime kernel)` | `frobeniusIntersection_eq_tsum_jets_add_contacts`, `frobeniusIntersection_eq_sqrt_mul` |
| Genus | infinite: `g(n) = 1 + (n/2)log(n/2π)`; Riemann–Hurwitz for number rings | `riemannHurwitz` |
| Sign | Bézout with the comb is RH; one positive square on packets is RH; the Hodge index of the scaling surface is RH | `riemannHypothesis_iff_combBezout`, `riemannHypothesis_iff_one_positive_square_packets`, `scalingSurface_hodgeIndex_iff` |
| Index | index of the neutral part `= 1 +` number of zeros right of the line | `exists_le_hermNegIndex_neutralWindow_iff` [L] |
| Symmetries | Frobenius over `𝔽_q` scales the form by `q`; power maps and successor shifts over `ℤ` are not conformal; boosts are isometries | `not_conformal_powerMap`, `not_conformal_succShift`, `boost_isometry` [R] |
| Operations | the Adams operations see only the norms (fixed ideal of `ψ_n` on `ℤ[x]` = product of the primes with `p − 1 \| n − 1`) | `span_fixed_adams`, `prim_adamsOp` |
| Reciprocity | Brauer induction; every Artin `L`-function has a completion with functional equation; conductor supported on the ramified primes | `brauer_induction`; AGZ [R] |

### 9.2 What any construction has to respect (no-gos of the ledgers [R])

Finite-rank integral Frobenius does not exist. A perfect Frobenius square keeps no contact. Nonnegative self-pairings of
the diagonals give at least two positive squares: the diagonals carry negative self-pairings of logarithmic size. The
Lefschetz weight `Λ(n) + 1 + 1/(n² − 1)` is not a cardinality and the glued count is not a trace. Convex bodies do not
carry the pairing. Sections count as on a curve: the quadratic term of a Riemann–Roch count exists iff RH (criterion C14
of AGZ). Inseparability exists at the finite places only.

### 9.3 The missing item, stated once

"One property of the square that is an inequality" (AGZ). By §9.1 the candidates are equivalent to RH when stated on the
whole square. The programme therefore has to produce the inequality from a structure, and the only structure that does
this over `𝔽_q` is a symmetry that scales the form. Over `ℤ` every symmetry in the corpus is an isometry and the positive
square comes from the pole plane.

### 9.4 Stages and gates

| Stage | Content | Gate (a theorem that decides whether to go on) |
|---|---|---|
| F1 Calibration | write `𝔽_q[T]` in the language of §9.1: square, contacts, jets, windows; `𝔽_p[T] → ℤ` as deformation by the carry cocycle | Weil's inequality for `𝔽_q[T]` is proved inside the calculus of the windows, with Frobenius as the only extra structure |
| F2 The scaling symmetry | find what replaces the conformal Frobenius | a correspondence on the square of `ℤ` that scales the neutral form by a factor `≠ 1` on a nonzero subspace; or a theorem that none exists in a stated class (the two non-conformality theorems are its first cases) |
| F3 The archimedean gauge | the sign as a gauge fixing by the archimedean place (`exists_nonneg_gauge_iff`) | an a priori bound for the gauge on bound windows that is not the Hodge index itself |
| F4 A quadratic count at bounded ratio | Riemann–Roch with a quadratic term on windows of ratio `< 4`, where the floors are theorems | the count reproduces the floor `10⁻¹³` with a structural constant |
| F5 Refinement | functoriality under refinement of blocks; index does not go down | the index law as a theorem of the geometry |
| F6 Reciprocity | Artin conductor exponents; the square of a number ring | Hodge index statements for Dedekind squares at the same ratios |

**Stop rule.** If F2 ends in the no-go, the square of `ℤ` is a language for ACS and adds no inequality: the programme
merges into §11. If F1 fails (the calculus cannot prove Weil's theorem where it is true), the window calculus is not the
right carrier and stages F3–F5 are not started.

**First three theorems.** (1) The gate of F1 for `q ≡ 1 mod 6` with the Kummer modules of the finite-field calibration
(`FunctionField/KummerExactRamification`, `KummerInertiaFixedFields`, `KummerRationalChartCount`; the places of the model are
classified in `KummerFinitePlaceCenters` and `KummerInfinityPlaceCenter`). (2) Non-conformality
for the full monoid generated by power maps and shifts. (3) The structural constant of the first overlap step: the gap
`1/50000` expressed through the charge-corrected Green form of the middle.

---

## 10. A research programme to close route WD

### 10.1 The route

Frontier map [R]: source current or window energy, then a collision-charge bound, all-resolution sectoriality, or
cofinal control of long mollified moments, then RH. Its three closing statements:

| Form | Statement | Dictionary |
|---|---|---|
| W1 fixed window | `∫₀¹\|ζM_N\|²` is subpolynomial in `N` | `zetaZeroWidth_le_iff_unit_window` at `β = 0` [S]; at one height: `zetaZeroWidth_le_iff_pointwise` [L] |
| W2 cofinal long prefixes | one `K`, unbounded `θ`, moments `O_θ(T^K)` | `zetaZeroWidth_le_of_cofinal_moebius_mollifier_slope` at slope zero [S] |
| W3 parity energy | sparse subpolynomial compact parity energy, giving `K = 3` | frontier map [R] |

### 10.2 What is proved inside the route

| Result | Lean |
|---|---|
| Upper bounds `T^{4+2wθ}` (pure) and `T^{6+2wθ}` (mollified) | `exists_pure_moebius_moment_le_zetaZeroWidth`, `exists_moebius_mollifier_moment_le_zetaZeroWidth` [S] |
| Depth ladder: `θ > ½` and dyadic moment `≤ CT` give eventual depth `< 1/(2θ) + ε` | `eventual_depth_bound_of_dyadic_moebius_moment` [L] |
| Necessary length: real unit-bounded coefficients of length `T^θ` give normalized moment `≥ 1 + 1/(8 + 6θ)` | `necessary_length` [L] |
| The last scale survives every short weight: the defect of a polynomial mollifier is set by the primes just above its length, at rate `2θ` | MZF [R] |
| A long Möbius second moment with logarithmic slope `S` bounds `Σ\|ρζ′(ρ)\|^{−2}` by `4S` | `not_forall_moebiusPoly_energy_le` [R] |
| Fejér means are signed logarithmic collision forms; the `Λ` coefficients have size between `X²/log X` and `X² log² X` | InfiniteRankWeilTheory [R] |
| Logarithmic corridors: small measure of exceptional windows, no extinction | CDG [R] |
| Positive proportion of critical zeros at `θ = 13/50` | MZF [S] |

### 10.3 Diagnosis [D]

WD is a ruler. Each of W1–W3 is exact in the width, the 7/8 theorem gives each of them at exponent `3/8`, and nothing in
the route lowers an exponent. Three facts fix what closing means.

1. A moment bound at one `θ` carries no information on `Θ`: the constant `K` absorbs it. Only cofinal `θ` counts.
2. The one finite-`θ` statement with a consequence for zeros is the depth ladder. It is nontrivial for `θ > 1` and it
   passes the 7/8 theorem at `θ = 4/3` (`1/(2θ) < 3/8`). The twisted moments of the corpus reach length
   `U^{21/50}`.
3. W1 and W3 are cancellation of a full square in signed sums with `Λ` coefficients of size `X²`: wall P1 of the walls
   ledger, with no partial form.

### 10.4 Programme

| Stage | Content | Gate |
|---|---|---|
| D1 Exchange | instantiate at `3/8`: `\|M_X(½ + it₀)\| ≤ C X^{3/8+ε}`; `∫₀¹\|ζM_X\|² ≤ B X^{3/4+ε}`; moments `T^{4+3θ/4}`, `T^{6+3θ/4}` | Lean corollaries; no research |
| D2 Exactness of the long ruler | a lower bound `T^{4+2wθ−ε}` for the pure moment along a sequence of `T` | the cofinal slope equals `2w`; WD is then a ruler in both directions and serves falsification (§13) |
| D3 Stage map in `θ` | an inequality from length `T^θ` to `T^{2θ}` with a loss factor | any factor below the one that gives slope `2·(3/8)` is a better quasi-RH; no candidate in the corpus |
| D4 The price of sharpening | make `not_forall_moebiusPoly_energy_le` two-sided: which sharpening of W2 is equivalent to which bound for `Σ\|ρζ′(ρ)\|^{−2}` | separates the forms of W2 that are RH from those that are RH with simple zeros and a negative-moment bound |
| D5 ZAL engine | bounded dyadic mollified moments for `θ > 1` | needs twisted moments beyond every length in the literature known to the corpus; the first consequence appears only past `θ = 1` |
| D6 Decision | if D3 has no candidate after D1, D2, D4: retire WD as a producer | closure record below |

**Closure record if D6 is reached** (no-go discipline). Negative statement: no estimate inside WD moves `Θ`; each closing
form is wall P1. Positive survivors, all in Lean: the width is read at one height by all prefix lengths; the depth
ladder; the necessary length; the last-scale defect; the price in negative moments; the instantiations of D1. Use after
closure: ruler for the field of §7, engine for ZAL in a sign-free skeleton (§6.3).

---

## 11. A research programme to close route ACS

### 11.1 The route as a continuity method

RH iff at each cutoff `Q ≥ 2` the windows of index one have a common gap `c_Q > 0`
(`riemannHypothesis_iff_exists_gap_neutralWindow` [L]; no gap uniform in `Q` is needed).

| Step | State | Lean |
|---|---|---|
| Nonempty | ratio `≤ 3` for `Q ≥ 2`, `< 4` for `Q ≥ 3`, at every block size; first overlap step with gap `1/50000` through ratio `10609/5000` | `neutralWindow_floor_two_prime_window` [S]; GCW [R] |
| Open | a gap on the bound windows passes to one more block (thin tail) | `riemannHypothesis_of_gap_of_bound_windows` [L] |
| Closed | missing: the second eigenvalue of a bound window stays away from zero | `exists_bound_window_without_gap` [L]: where the bound range ends, the gap of shorter bound windows closes |

The Hodge index on a bound window gives gap `≥ 0`; a positive gap from boundness alone is RH (GCW [R]).

### 11.2 Four ladders, one statement

| Ladder | Proved | RH | Missing step |
|---|---|---|---|
| Ratio of the neutral windows | `< 4` | every ratio | fourth ladder excess at `Q = 2`; ratio four, where the prime square 4 enters |
| Aperture of the full Weil form | `log 2`, floor `10⁻¹³` | every aperture | next apertures; a certificate at aperture `a` reads zeros below a finite height only |
| Margin exponent | `½` | bounded margin | `3/8 + ε` by the converse rate law (§5.2) |
| Overlap of the complete Weil matrix | `2K(log N)^{1/8}`, one `K` (tilted spline) | `(log N)^α`, `α > ¼`; every bounded multiple of the critical overlap `≍ L(log L)²`, `L = log log N`, for logarithmic Denjoy–Carleman profiles (`riemannHypothesis_iff_forall_critical_multiple` [R]) | the band between `1/8` and `¼`; one multiple `K` is one aperture `½ log K + O(1)` |

### 11.3 Where an a priori gap can come from [D]

| Source | State |
|---|---|
| A symmetry that scales the form (Frobenius over `𝔽_q`) | every symmetry over `ℤ` in the corpus is an isometry (ALG) |
| The pole plane, as the archimedean gauge | `exists_nonneg_gauge_iff` [R]: the sign is a gauge fixing; no bound for the gauge |
| A stage map with loss below the trivial one | §5.2, second lemma |
| Exclusion of the limit object | if gaps close at fixed `Q`, the limit is the critical half-line state of HF: unique up to sign, outer, cyclic, Laplace transform zero-free on the closed right half-plane [R]. An arithmetic property incompatible with it closes the method (wall U5) |
| Certificates | extend the proved range; give no limit |

### 11.4 Programme

| Stage | Content | Gate |
|---|---|---|
| A1 | converse rate law for all packets | margin exponent `≤ 3/8 + ε` with no hypothesis |
| A2 | doubling inequality at the balanced split | any `λ < √2`: second producer. A fake with `λ = √2` and the same gluing data: ACS is a ruler |
| A3 | acid test: the gap of the windows of `𝔽_q[T]` by stage maps, without Weil's theorem | if the calculus cannot prove the gap where it is true, A2 is not pursued by this calculus |
| A4 | the critical state: list the identities it satisfies (dilation, reflection, cyclicity) and test them against the prime weights | one identity that the actual source violates |
| A5 | the critical exponent of the tilted spline between `1/8` and `¼` | the scale at which whole-space positivity becomes RH, as a theorem |
| A6 | certificates: `Q = 2` fourth excess; ratio four; aperture `½ log 5` (peer summary) | range of the base case |
| A7 | function-field calibration: a transfer of positivity from the Kummer modules that is compatible with `ζ` | named open in the frontier map |

**Closure record if A2 ends in a fake.** Negative statement: the gluing calculus of the windows cannot produce a
half-plane. Positive survivors: the index law (index `= 1 +` right zeros), openness, the floors through ratio four, the
rate dictionary with exponent `3/8`, the first step as one bound state of the middle. ACS then stands as the exact
geometric form of RH and as the test bench of §9.

---

## 12. A research programme for a general Galois theory of zeros

### 12.1 What exists (GTZ) [S/L]

| Layer | Statement | Lean |
|---|---|---|
| Fields | `K` (complete-fibre traces) and `B` (prime traces); fibre equations are finite Galois over `B`; the degree of the residue field of a zero is the size of its orbit | GTZ [R] |
| Exact form of RH | all zeros on the line iff a `σ` of the group lifts the reflection on the zeros and every prime weight lies in `B` | `forall_re_eq_half_iff` [L] |
| Heat cover | the forward monodromy group has index `≤ 2` in the signed permutations and is transitive; it is proper iff its turns obey one parity law; a proper group forces collision masses divisible by eight | `exists_not_mem_forwardMonodromy_iff_exists_turn_parity`, `mem_forwardMonodromy_of_not_eight_dvd_collisionMass` [S/L] |
| Conjugation | RH iff the fibre conjugation is trivial at every positive time off the branch times | `riemannHypothesis_iff_fibreConj_eq_one` [S] |
| Jensen equations | Galois group `C₂ ≀ S_n` over the coefficient field, or a rational relation among the normalized moments | `jensenGal_full_or_exists_moment_relation` [S] |
| Transcendence | traces at rationally independent heights are algebraically independent; `p^z` algebraic at three primes iff `z ∈ ℚ` | `primeTraceFunction_algebraicIndependent`, `three_prime_exponentials_algebraic_iff` [S] |
| Comparison | arithmetic groups act on finite continued windows as heat monodromy; no whole-fibre identification | GTZ [R]; walls R3 |

Limit stated by GTZ: the theory gives a route only through a restriction that the primes or the branch divisor impose on
the position of complex conjugation, and none is known.

### 12.2 What "general" adds

| Direction | Object | First theorem | Source |
|---|---|---|---|
| G1 Representation ring | the zero divisor as an additive map `R(G) → Div(ℂ)`, `χ ↦ div L(s, χ)`, for a finite Galois group `G` | the Heilbronn character `θ_{s₀} = Σ_χ ord_{s₀}L(s, χ)·χ` restricts to a character on every subgroup; `Σ_χ ord_{s₀}L(s, χ)² ≤ (ord_{s₀}ζ_K)²` (Heilbronn; Foote and Murty) [D, classical, not in the corpus] | `brauer_induction`; Artin completions with functional equation (AGZ) |
| G2 Operations | Adams operations on `R(G)` against dilations and powers on divisors | compatibility of `ψ_k` with the divisors of abelian characters: `div L(s, χ^k)` | `prim_adamsOp`, `span_fixed_adams` |
| G3 Families of characters | the group that permutes the zero sets `Z(χ^σ)`, `σ ∈ Gal(ℚ(χ)/ℚ)`; reflection maps `Z(χ)` to `Z(χ̄)` | the exact form `forall_re_eq_half_iff` for a Galois orbit of Dirichlet characters; the 7/8 theorem holds on the whole orbit | `DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re` |
| G4 Products | the monodromy of the heat cover of `ξ_K = Π ξ(χ)^{χ(1)}` against the monodromies of the factors | block structure: collisions between zeros of different factors are not branch points of the factors | heat modules of GTZ |
| G5 Invariants | parity, collision mass, discriminants of the Jensen equations | the sign of `G₊` | parity-law module |

### 12.3 Stages

| Stage | Content | Gate |
|---|---|---|
| Z1 | decide the sign of `G₊` | expected `G₊ = W` [D]: one simple complex collision off the centre has `k = 0`, `c = 1` and violates both parity laws. If so, the heat cover has no invariant beyond transitivity, and the parity route to B13 closes |
| Z2 | Heilbronn characters in Lean from `brauer_induction` | multiplicity laws: `ord_ρ ζ ≤ ord_ρ ζ_K` for `K/ℚ` Galois (Aramata–Brauer); a zero of `ζ_K` of order one belongs to one abelian character (Stark) |
| Z3 | algebraic relations across heights | open in GTZ; decides whether `B` has a presentation |
| Z4 | a restriction from the source that separates the lift of the reflection from conjugation | the only door to RH in this theory, by the limit statement |
| Z5 | the theory for the Hecke family of `ℚ(ω)` and for Dirichlet characters, where the 7/8 theorem holds | uniform statements on orbits of characters |

**What the programme can and cannot give.** G1–G2 give laws for orders of zeros across a Galois group. They do not
locate zeros: `ζ` is the trivial representation, every induction contains it, and an off-line zero of `ζ` is a zero of
every `ζ_K` with no further constraint. Location enters only through Z4.

---

## 13. If RH is false

### 13.1 The three worlds

By `riemannHypothesis_iff_three_atoms`, a false RH is one of three worlds.

| World | Zeros off the line | Atom that fails | What the corpus forces | Model |
|---|---|---|---|---|
| F | finitely many, at least one | B13 | index of the real packets finite and positive; index of the Künneth square infinite; if `G₊` is proper, the number of quartets is even [D] | compact Selberg zeta: Euler product, functional equation, finite real off-line set |
| S | infinitely many, depths tending to zero | Landing | `N(t)` unbounded as `t ↓ 0`; ZAL and Lindelöf hold | functional-equation models with approaching remainders (no Euler product) |
| D | infinitely many beyond some depth | ZAL | `Θ > ½`; by AAL-type statements the top layer is empty or infinite under window non-attainment | integer-norm Euler models with a prescribed layer |

World F is invisible to every law, density and proportion in the corpus. World D is the one constrained by the density
theorem. World S is constrained by the census and by Selberg-type density near the line.

### 13.2 What an off-line zero `ρ = ½ + δ + iγ` obeys (no hypothesis)

| Constraint | Statement | Lean |
|---|---|---|
| Strip | `\|δ\| ≤ 3/8` | `riemannZeta_zero_mem_quasiRH_strip` [L] |
| Flattening | `\|ζ(½ + iγ)\| ≤ 480e²(\|γ\| + 2)(\|γ\| + 5)δ²` for `\|δ\| ≤ 1/16`, `\|γ\| ≥ 3` | `norm_zeta_center_le_of_offline_zero` [L] |
| Heat | `δ²/(200 log γ) ≤ Λ` for `γ ≥ e^{1600}` | `le_newmanConstant_of_offLine_zero_quadratic` [L] |
| Multiplicity | `m(ρ) ≤ ((3/(8π))cos((4π/3)δ) + ε) log\|γ\|` | SquareRootThreshold [R] |
| Density | `N(σ, T) ≤ D(1 + log T)^B T^{(30/13+ε)(1−σ)}` | `exists_zeroHeightBox_ncard_le_thirtyThirteenths` [S] |
| Proportion | at most `1 − 0.6725` of the zeros; off-line multiple mass `≤ 1/6` | `simple_critical_proportion_ge_67250071`, `offLineMultipleMass_le_one_sixth` [S] |
| Index | one negative square of the neutral windows per right zero | `exists_le_hermNegIndex_neutralWindow_iff` [L] |
| Visibility | at aperture `a`, depth `≥ 1/a` is excluded below a height horizon; above it a zero hides | WVL [S] |
| Jensen | no nonreal root through degree 31922 | VerifiedHeightRungs [R] |

### 13.3 (a) A programme to prove RH wrong

A proof of ¬RH with no computation is an Ω-theorem. The corpus turns ¬RH into equivalent statements of that kind:

| Statement equivalent to or implied by ¬RH | Lean |
|---|---|
| the lag is unbounded on prime powers | `riemannHypothesis_of_primePowerLag_le` (contrapositive) [S] |
| the margin of the initial windows is unbounded below | `riemannHypothesis_iff_initialWindow_margin_bddBelow` [S] |
| some neutral window has two negative squares | `exists_le_hermNegIndex_neutralWindow_iff` [L] |
| `N(t) ≠ 0` for every small `t > 0` | `riemannHypothesis_iff_eventually_nonrealZeroCount_eq_zero` [S] |
| the Möbius partial sums have zeros right of the line on compact sets, for arbitrarily long sums | `zetaZeroWidth_le_iff_moebiusPoly_zero_free` [S] |
| the joint-ancestry abscissa is at least `1 +` the largest depth (it is `0` under RH) | `jasAbscissa_eq_zero_or_one_add_sSup_le` [S] |
| the Künneth square of Weil's kernel has infinitely many negative squares (none under RH) | RIT [R] |

Two kinds of strategy follow, and neither has a first step in the corpus.

1. **Gap laws.** The last two rows are dichotomies with a gap: the quantity is zero or at least a definite amount. A
   soft proof that it is positive disproves RH. No theorem of the corpus bounds any of these quantities from below
   without zeros.
2. **Ω-results from arithmetic.** Every Ω-theorem for `ψ(x) − x` or `M(x)` beyond the square root is derived from a
   zero. An independent one needs a lower bound for an oscillation from the integers alone. The integrality lattice
   gives one-sided bounds for the main term (slope one, not attained) and nothing at the square-root scale (ASRP [R]).

Programme, as far as it goes: (i) choose the world; F is the one no theorem constrains. (ii) Prove a forcing statement
for that world: does a top quartet force replicas near multiples of its ordinate (open in ELT)? Forcing with a
contradiction proves B13; forcing without one describes the counterexample. (iii) Make every ruler two-sided (D2 of §10,
A1 of §11): a two-sided ruler turns a lower bound for a moment or a margin into an off-line zero. (iv) Keep the gap laws
as the targets of any soft lower bound.

Verdict: the corpus has no strategy for a disproof that is not the mirror image of a proof attempt, and no evidence in
either direction is claimed here.

### 13.4 (b) A concrete counterexample without computation

A counterexample is a region with an off-line zero or a finite object that certifies one.

| Certificate | Finite object | Lean |
|---|---|---|
| Window | a neutral window with index two | index law [L] |
| Integer | one `n ≥ 2` that violates the integer lag inequality (a `Π⁰₁` form of RH) | `riemannHypothesis_iff_integerLagInequality` [S] |
| Heat | a time `t > 0` with a nonreal zero of the heat-evolved function | `riemannHeat_zeros_real` for `t ≥ 1/8` [S] |
| Jensen | a Jensen polynomial with a nonreal root | degree `> 31922` |
| Test function | a `C²` test of compact support with negative Weil value | `offLine_visible` [S] |

Each certificate, once named, is checked by computation; "without computation" can only mean that the certificate is
produced by a proof. The localization chain for that exists: a positive heat threshold gives an off-line zero below a
height (`exists_offLine_zero_below_of_wdHeatThreshold_pos` [S]), and zeros on the line below `H` give threshold
`≤ 100/log(H − ½)` (`wdHeatThreshold_le_of_zeros_on_line_below` [S]); so a proved lower bound `τ₀` for the threshold
puts an off-line zero below height `e^{100/τ₀} + ½` [D]. From a box, the visibility law gives the aperture at which a
window sees it, and the index law gives the window. The chain lacks its first link: a structural positive lower bound
for the heat threshold or for one of the gap quantities. Passing from an unbounded lag to an explicit integer needs an
effective form of Landau's theorem, which the corpus does not have.

---

## 14. Missed opportunities

Assemblies of theorems of the corpus that are not in the corpus. Each is a deduction [D] and needs a Lean proof. Search
of consumers was by name.

### 14.1 Assemblies that give theorems with no hypothesis

| # | Pieces | Result | Size of the work |
|---|---|---|---|
| 1 | `newmanConstant_le_half_sq_zetaZeroWidth` + `zetaZeroWidth_le_three_eighths` | `Λ ≤ 9/128` in the normalization where the corpus has `Λ ≤ 1/8` (`newmanConstant_le`); with `wdHeatThreshold_le_third_sq_zetaZeroWidth`: heat threshold `≤ 3/64` | two lines |
| 2 | `exists_moebius_power_bound_of_abscissa_lt` + `Θ ≤ 7/8` | `\|M(n)\| ≤ C_β n^β` for every `β > 7/8` | one line |
| 3 | rulers of §1.1 at `3/8` | `\|M_X(½ + it₀)\| ≤ C X^{3/8+ε}`; `∫₀¹\|ζM_X\|² ≤ B X^{3/4+ε}`; moments `T^{4+3θ/4}`, `T^{6+3θ/4}`; dressed PSD level `11/8 + ε`; Möbius partial sums eventually zero-free on compacts right of `7/8` | one line each |
| 4 | `jasAbscissa_eq_zero_or_one_add_sSup_le` + `xiZeroHalfPlaneBound_zetaZeroAbscissa_sub_half` + `3/8` | the gap law of the joint-ancestry abscissa with no hypothesis: it is `0` or `≥ 1 +` the largest depth | short |
| 5 | walk ledger C16 (`Θ < 1` gives Transfer ⇔ RH) + `Θ ≤ 7/8` | Transfer ⇔ RH with no premise | one line |
| 6 | `DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re` (every modulus) | no exceptional zero right of `7/8`; by the standard arguments, each to be proved: an effective lower bound for `L(1, χ)` and for class numbers; `ψ(x; q, a) = x/φ(q) + O(x^{7/8+ε})` uniformly in `q`; least prime in a progression `≪ q^{8+ε}`; least quadratic non-residue `≪ (log p)^{8+ε}` (the corpus has the Burgess–Vinogradov exponent) | a module each; the one consumer of the theorem in the corpus is `χ₋₃` |
| 7 | `hecke_nonzero` + class field theory of `ℚ(ω)` | Dedekind zeta functions of abelian extensions of `ℚ(ω)`, and of pure cubic fields `ℚ(∛m)` through `ζ_{ℚ(∛m)} = ζ·L(s, χ_m)`, are zero-free right of `7/8` | needs the identification of the family with ray class characters |
| 8 | zero-free half-plane + Borel–Carathéodory | `ζ(σ + it)^{±1} ≪ \|t\|^ε` for `σ ≥ 7/8 + ε` (Lindelöf right of `7/8`); the corpus has a polynomial bound for `1/ζ` there (`exists_invZeta_poly_seven_eighths`) | short |
| 9 | `abscissa_le_max_fixedPoint_of_tower` for two pairings | composite towers: the fixed point of `T₁ ∘ T₂` is a convex combination of `c₁/(k₁ − 1)` and `c₂/(k₂ − 1)`; every mixed tower stays at `≥ 3/5` | short; extends the no-go to mixed towers |
| 10 | `eight_dvd_nonrealZeroCount` + `eventually_nonrealZeroCount_eq_of_finite` | proper forward monodromy and finitely many off-line zeros give an even number of quartets; one simple quartet forces `G₊ = W` | short |
| 11 | `continuedProbeCorrection_eq_zero_iff` + a zero-free half-plane `b` for the Grössencharacter family | the correction is zero-free on `Re s > (3 + b)/6`; with `b = 7/8` the frame wall is `31/48` | conditional on the rung; the reduction is one line |

### 14.2 Theorems without consumers

`tendsto_logAvg_liouville_shift` (fixed-shift logarithmic Chowla) and `brauer_induction` are not used outside their
programmes. The first is an input in law for the recurrent-sign receivers of the AAL programme; the second is the
entry to §12, G1. The all-moduli Dirichlet theorem has one consumer.

### 14.3 What was looked for and not found

No assembly of theorems of the corpus was found that proves or refutes AAL, ZAL, B13 or Landing, that lowers `7/8`, or
that gives a second producer. The reasons are those of §1.4: every candidate chain passes through a ruler at exponent
zero or through a stage limit. The disjunction `quasiRH_or_asymptoticAbscissaLaw` has its left side as a theorem and
carries no information on AAL.

### 14.4 Routes that an assembly would close

| Route | Assembly | State |
|---|---|---|
| Parity of the heat cover as a door to B13 | Z1 of §12: one simple complex collision off the centre | expected; the existence of such a collision is to be proved |
| WD as a producer | §10.3 | closed in substance; record of §10.4 not written in the ledgers |
| Mixed Gauss towers | item 9 | a short theorem |
| Fixed aperture as a door to a half-plane | `exists_hidden_inv_aperture_zero_above_single_exp` | closed in the corpus: a finite aperture reads finite height |
