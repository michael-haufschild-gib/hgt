# Routine work, open problems, and the shape of the missing mathematics

Companion: [per-route assessment of all 29 routes, 18 candidates and 15 walls](hard-obstacles-2010.md).

## 1. Assessment

Every route in the [route ledger](../rh-current-frontier-map.md) ends in one unproved statement that implies RH or in one unconstructed object whose construction would be such a statement. None of these remaining steps is routine, and no routine task on the list below moves any of them. What is routine is small: auditing a handful of Lean sources into umbrella theorems, formalizing two classical facts the [walls ledger](../walls/walls-ledger.md) records on paper, settling a few stated equivalences and converses, and sharpening named constants.

The open steps collapse into six families (§2.2). Two of them, square-root cancellation of a signed prime sum and positivity of the complete Weil form, are the same problem in different coordinates and carry the others. The corpus proves that the identity layer, the positivity-of-pieces layer, the finite-data layer and the averaging layer are each insufficient, and it names the five mechanisms one of which any proof must supply. No existing field supplies one. §2.3 states what a field that does would have to be.

## 2.1 Tasks that are just work

Each item is finishable with known methods. The last column states what the item does not do; none supplies a sign or bound that closes a route.

| Task | Kind | Routes | What it yields | What it does not yield |
|---|---|---|---|---|
| Audit `TransHorizonIncidenceMechanics/HalfDampingDissipationLaw` into umbrella status (`R(ε)/ε → 1/2`, `R(ε)/variance → 1`). | Lean closure | MC, PM, BVI | Small-damping rates of the renormalized defect become [L]. | No bound at any `ε < 1/2`. |
| Audit `BezoutValuationIncidence/LogHarmonicReadoutAndTheMobiusRowEnergyFloor` (untracked source). | Lean closure | CTF, BVI | For `−μ_N` the `Λ`-readout tends to its target and the centred pronic energy has floor `κ/(4 log N)`. | No vanishing of the centred energy. |
| Audit `RHTower/ZetaStripBohrFourierCoefficients` (untracked source). | Lean closure | BAG | Bohr–Fourier coefficients `n^{−σ}` of `ζ` on `σ + it`. | No fixed-base-disc return. |
| Audit `arithmetic-positivity-theory/CriticalPrimeChannelUniformBound` and `CriticalCompleteFormHighScalePositivity`. | Lean closure | EWU, RW | `ℓ²`-uniform prime channel and positive definiteness of the complete uncollared critical form on high dyadic blocks. | Nonselective: the family is positive without RH. |
| Audit `ArithmeticCriticalityTheory/PlateauGaugeWindowWeilPositivity`. | Lean closure | ACT, RW, SRT | `Ẑ(F) ≥ (3/40)∫F²` on supports below `e^{−2}/2`. | Below the first prime; no prime shift enters. |
| Audit `BiScaleUncertainty/ExactSingleIntegerBlindSymbolSlack` and wire `BiScaleUncertainty/PacketSignGapLaw`. | Lean closure | HF/EWU; WL | Sharp slack on power grids; bounded sign gaps of bounded packets. | Sparse-grid constants and oscillation laws, no sign. |
| Formalize the classical unboundedness of `S(T)` (Wall 14, paper only). | Lean closure | HF, RN, TG, candidates | Excludes finite-rank prime modifications of the archimedean operator, strengthening the proved non-integrability. | Constrains constructions; produces none. |
| Formalize the Mehler–Fock / Bochner–Godement dictionary (Wall 13, paper only). | Lean closure | RW, HF, OWU, CHMD, ACT | The identification of the Bochner cone with positive-definite zonal functions on the arc, behind the cone-mismatch theorems. | No transfer compatible with blindness beyond the window sector. |
| Prove or refute the RH converse of the shift-averaged ACT inequality. | Receiver bookkeeping | ACT | Whether averaging over shifts loses RH content. | The single-shift inequality stays open either way. |
| Decide whether the RW/SZ/CHMD common-core equality extends to the completed source norms. | Receiver bookkeeping | SZ, RW, CHMD | One receiver or three. | No sign. |
| Rewrite the complete log-renormalized interior remainder of the pronic receiver as an explicit Type-II bilinear form plus `O_ε(1)` through the existing Heath-Brown/Vaughan dictionary. | Receiver bookkeeping | MC, PM, BVI | Names the open remainder as a bilinear form in Möbius with modular-inverse structure. | The dispersion estimate for that form (BVI tool 3). |
| Decide the renormalized-defect sign at every horizon `N ≥ 2` and the least long-window threshold. | Finite/universal | BVI, THIM | Universal-weight sign laws at small horizons. | Universal in the weight, hence no RH content. |
| Selectivity audit: for each positivity theorem on a test family, state what it says for `ζ(s−a)ζ(s+a)`, for a Beurling system with an off-line zero, and for the Liouville-twisted weight. | Receiver bookkeeping | all positivity routes | Separates nonselective theorems from candidates for closing. | Nothing about ζ itself. |
| Named constants: plateau-gauge radius toward `t₀/2`; APT block threshold `M₀`, slopes `s, s_c`, offsets; TH/TT inner-chamber region in `(t, Z)`; SRT aperture `1/100` toward Yoshida's; capacity-ratio approach rate. | Finite calculation | ACT, EWU, TH, TT, SRT | Sharper constants in nonselective regimes. | No regime change: none crosses a prime shift or a power. |
| Finite checks the routes name: finite blocks of Hausdorff orders and shifts (PA); fixed-rank Hankel forms (HCF, TH); a specified disc (XN); a finite range of integers (RB); a finite schedule (FU). | Finite calculation | PA, HCF, TH, XN, RB, FU | Certified finite statements. | Leave infinitely many orders, ranks, discs or integers. |

Two statements that are sometimes listed as intermediate milestones are not on this list because they are not of lesser difficulty than RH-strength problems:

- A horizon-uniform bound on the complete pronic energy at **one fixed** damping `ε ∈ (0, 1/2)`. It implies the zero-translation law `ζ(ρ) = 0, Re ρ > 1/2 + ε ⟹ ζ(ρ − ε) = 0` (`pmPowerDamped_zero_translation` [L]), a rigidity of the zero set no known method produces; the unsigned method stops at `ε = 1/2`, the absolute-convergence line.
- A one-sided power bound `O(x^θ)` with any `θ < 1` on a Chebyshev or Möbius quantity. By Landau it is the zero-free half-plane `Re s > θ`.

## 2.2 Open mathematical obstacles

Six families. They are not proved independent; a theorem closing one would close others.

### O1. Square-root cancellation of a signed prime sum (Wall 1)

**Routes.** WL, MC, PM, CTF, PBM, RB, FU, RP, LI; BVI, MSC, EGC, DR as candidates; SRT's window reduction lands here.

**Exact receivers.** `ψ(x) − x = O(√x log² x)`; `M(x) = O_ε(x^{1/2+ε})`; the one-sided `±∫₀ᵀ(eᵗ − ψ(eᵗ))dt ≤ Be^{T/2}`; the linear band `∫₀^L Ẽ² = O(L)`; `d_N → 0`; cofinal admission of the power-damped Möbius source; convergence of the regularized prime series at every `σ > 1/2`; the Robin inequality on colossally abundant integers. Each is RH-equivalent or RH-sufficient [L].

**What is known to be insufficient.** Divisor-sum (Type I) information gives the constant `2`, never `1` (parity). Exponential-sum methods save `exp(−c(log x)^{3/5})`, never a power. Zero-density estimates count in strips, not at every height. Unsigned majorants stop at absolute convergence. The positive absolute envelope of the signed covariance grows at the wrong exponent [L]. Mertens is `Ω±(√x)`; the receiver is one-sided at exponent zero with a logarithmic loss.

**What a mechanism must satisfy** (walls ledger, companion note on Wall 1): it must fail for Beurling systems (use the additive structure of `ℕ`); survive the degenerate point of one character, modulus one, shift zero, with no family average; carry information beyond polynomial length equal to height at square-root precision; and distinguish `log 4` from `log 6`. Additive tools (large sieve, dispersion, Poisson) meet the first and third only after averaging over a family; multiplicative tools are Beurling-invariant. No known tool meets all four.

### O2. Positivity of the complete Weil form (Walls 8, 11, 12, 13)

**Routes.** RW, EWU, OWU, CHMD, HF, ACT, SRT, TT, PA; JAS at level one.

**Exact equivalent forms** [L]. The odd capacity inequality `sinhPairing(g)² ≤ 2·markovEnergy(g)` on compact odd tests; the single-shift inequality `D_a(u) ≤ 2S_a(u) + V_a(u)` at any one `a > 0` for even profiles; the nonnegative-cone inequality `Lévy_arch(v) + Lévy_prime(v) + 2(∫Φv e^{x/2})(∫Φv e^{−x/2}) ≥ ∫Φ cosh(x/2) v²` with no signed term; nonnegativity on difference two-bump tests at every height and late lag, each reading one dyadic prime window; prime-blind positivity on the full integer-log grid; the even blind minimum nonnegative at every aperture; absence of sign-changing odd CHMD eigenstates above `1/2`.

**What is known.** The cone is the point `Λ`; prime-blind positivity fails if any prime-power node is deleted; the form is critical in every term (no Hardy weight, minimal prime rates, indispensable variance, capacity ratio tending to `1`), and near-null families exist under RH, so a certificate must cancel exactly. Positivity holds unconditionally on apertures `≤ 1/100` and below `e^{−2}/2`, at single heights for `√X ≤ (¼ − ε) log T`, and on every restricted family whose archimedean energy grows (factorial, Müntz, high-block critical sources); all of these are nonselective. In every coordinate system the unpaid term is the signed prime−polar pairing `Σ Λ(n)n^{−1/2}h(log n) − ∫2cosh(x/2)h`, which is a Chebyshev-error gauge: O2 contains O1. The negative conductances of the jump form are confined to the prime anti-diagonals `|x| + y = log n` and the axes near the origin. Every pointwise supersolution with a nonnegative profile fails at both ends; a supersolution, if one exists, is sign-changing with `∫M dm ≤ 0` and `∫₀^∞ M cosh ≤ 0`. Every certificate of positivity is the critical-zero measure (Wall 12): a positivity producer is a spectral realization of the zeros. Pointwise cones transfer to the Bochner cone only on the window sector (Wall 13).

### O3. Uniformity through a critical parameter (Walls 3, 4)

**Routes.** TH, HCF (all degrees at one heat time), PA (all Hausdorff orders at one shift), LA, SZ, TT (the critical shift, time or axis), GTA (rank-uniform decay), XN (all discs), WD (all zero blocks).

**Shape.** Each route has a fixed-parameter theorem (eventual in another parameter) and needs the common-parameter theorem. Fixed rank `N` is blind above height `O(N√log N)`; the unconditional de Bruijn–Newman bound is the strip width `1/8`; shifts, differences and heat flow are real-rooted exactly beyond the strip edge. The missing step is control at the critical parameter itself, which in each case is O1 or O2 again.

### O4. Complete signed history and transport (Walls 1, 10, 14)

**Routes.** FU, RP, LI, SZ (Wronskian), TG, EGC.

**Shape.** The quantity is a sum over a history (blocks, fibres, cutoffs, contour copies); the positive pieces are proved and the signed cross terms between pieces (seed, inherited action, covariance, high-LCM fibres, moving core, endpoints, Gamma floor) are not. Absolute payment fails (fibre variation diverges, trace masses stay positive, envelopes fail); strong convergence does not pay norm or trace costs; the receivers are one-sided bounds whose exponent is the zero abscissa.

### O5. Every height, not almost every (Walls 3, 7)

**Routes.** BAG (conditioned return on a prescribed disc), SRT (same-height window inequality; visibility of a non-attained top at a controlled lag), LA (near-double pairs), JAS (exceptional vectors), WL/MC (exceptional lags).

**Shape.** Every unconditional statement about the zeros near the line is averaged: density, proportion, typical phase, almost-all intervals, pair correlation in the diagonal range. RH is a statement about one function at every height. Around an off-line zero the recurrence set has density zero; finite prime polynomials attain every phase pattern at suitable heights (Kronecker–Bohr), so pointwise positivity must come from the coupling, through the functional equation, between finitely many primes and the infinite tail. Conditioning on an event of density `κ` costs `1/κ` generically. The upgrade from almost all to all is exactly where an off-line zero would sit.

### O6. Arithmetic realization (Walls 5, 12, 14, 15)

**Routes.** HF (cohomology), RN and TG (native completion, transgression); candidates APF, BSH, CDC, DR, EWJ, FEL, HJ, IRK, MSC, PCS, PTR, RFHM, SC, SEC, W1C, WBF, PW-B.

**Shape.** The object sought is a space, operator, form or geometry that produces the prime powers, carries the Gamma and polar data, has a trace recovering the explicit formula, and places the zero support on the line. Constraints proved: self-adjointness is cheap (any real diagonal spectrum is realizable); unitary producers have unit-modulus Euler factors; the prime part is not trace class, finite rank or finite deficiency and is as large as `S(T)`; compact models fail Weyl density; positive currents and positive-definite transforms are orientation-blind; zero-indexed constructions (zero algebra, `XiZeroCopy`, divisor-support tests) are circular until their decisive premise is proved from the source. This is the only family where a construction rather than an estimate is sought, and the only one where the function-field proofs give a template.

### How the families relate

O2 and O1 are one problem: the Chebyshev-error gauge identifies the unpaid term of every positivity route with the one-sided prime bound, and SRT's window reduction identifies RH with a bound on one dyadic prime window at one height. O3 and O4 are O1/O2 with a limiting parameter attached. O5 is the quantifier gap of every averaged method and sits inside every route that uses density or typicality. O6 is the construction form of O2: by Wall 12 a certificate of positivity is a spectral realization of the zeros, so an arithmetic realization and a positivity proof are the same object seen from two sides.

## 2.3 Does closing these obstacles need a new field?

### The case

Nothing proves that a new field is necessary; one unexpected estimate inside existing analytic number theory would suffice. But the corpus does prove, route by route, why each existing layer stops where it stops, and the stopping points share one description. Sieve and bilinear methods see the additive structure of `ℕ` but only after averaging over a family, and divisor-sum information is parity-blind. Multiplicative, spectral and explicit-formula methods are Beurling-invariant: everything they prove holds for generalized integer systems with off-line zeros. Dirichlet-form and criticality methods give the right sign framework, but their identities hold for any even positive kernel; the arithmetic enters only through the equation of motion of `Θ`, and every nonnegative gauge fails. Arithmetic geometry has the template (Frobenius, finite-dimensional cohomology, the Hodge index theorem) and no object over `ℤ`. Each field has one of the three properties a closing theorem must have at once: it must see both operations of `ℕ` at a single modulus; it must carry a sign structure (one negative square, the pole plane); and it must be resolved at the zero spacing, that is at square-root precision at every height. No existing field has its basic objects built with all three. In that sense, yes: the missing step appears to lie in a field that does not yet exist. Its name is immaterial; its content is fixed by the walls.

### What the field is about

The sign of the critical arithmetic form as a property of the incidence structure of the integers: which integers are multiples of which, and which are consecutive, read at a window `(X/2, 2X)` with precision `√X`. Equivalently, the deterministic behaviour of the prime phase process `Σ_{n ∈ window} Λ(n) n^{−1/2 − iγ}` at a single height, as opposed to its statistics.

### Objects and language it is built on

- **The window and its two structures.** A dyadic window of integers with multiplication (divisibility, prime powers, the node set `{log n}` and its criticality at `log 4` versus `log 6`) and addition (`gcd(n, n+1) = 1`, the Bézout relation `pa − qb = h`, residue classes omitted modulo `p`, the Diophantine spacing of jumps of `{N/p}` and `{N/q}`). The corpus's Selberg coordinates, pronic Gram, valuation clocks and radical states are its finite coordinates.
- **The signed conductance form.** The jump form `J_M(u) + V_μ(u)` of a gauge `M`: conductances `M(x)M(y)(dm(|x−y|) + sinh(x/2)sinh(y/2))`, positive on same-side lags `|x−y| = log m` and on all variance pairs, negative on the anti-diagonals `|x| + y = log n` and near the axes. RH is its nonnegativity; its criticality is proved. This is the object on which "positivity" has a definite arithmetic meaning: an inequality between anti-diagonal and same-side prime atoms.
- **The pole plane.** The Lorentz form `(B² − A²)/2` on the theta span, which is the radical of the full zero form; the archimedean place behaves as a one-negative-square (Hodge-index-type) form.
- **Tests and gauges.** Difference two-bump tests reading one dyadic window (two real parameters, one sign); even profiles in a Doob gauge; prime-blind autocorrelations; the configuration of zeros as a tempered configuration determined by the all-aperture form.
- **Scale language.** Height `T`, aperture `a`, bandwidth `λ = log X/log T`, depth `δ`, resolution, horizon ratio, damping. Every statement names its height and aperture and the strongest unconditional value known.

### Mechanisms it must discover

1. **A prime-side inequality with no slack.** Payment of each anti-diagonal atom `Λ(n)n^{−1/2}` by same-side atoms and the variance, on all even profiles, at one shift. Its smallest instance is a gauge argument through the first prime window, past `log 2/2`, paying the single atom of `2` by the potential. The corpus shows the paying object cannot be a nonnegative function; the field needs a theory of sign-changing supersolutions, or of positive solutions for forms with negative conductances on an arithmetic set of pairs: a ground-state representation and a Harnack-type propagation across the prime shifts `log 2, log 3, …` for which no analogue exists.
2. **Single-modulus bilinear dispersion.** Cancellation in `Σ_{p∼P} Σ_{q∼Q} a_p b_q 𝒢^{ec}(p,q)` through the reciprocity `{N/pq} ↔ p̄/q + q̄/p` and the modular inverses, without an external character or modulus average. Classical dispersion crosses the Nyquist threshold `θ = 1` only after averaging; the receiver sits at `θ = 2` for one character and modulus one.
3. **A deterministic phase law.** The coupling, through the functional equation, of the finitely many primes in one window to the infinite tail at one height, replacing the Kronecker–Bohr freedom of finite prime polynomials by a constraint on the actual function. BAG's conditioned tail on a prescribed disc and SRT's same-height inequality are the two forms of this question; both are at present answered only statistically.
4. **A definite spectral realization with a large prime part.** By Wall 12 the certificate of positivity is the zero measure; a proof must therefore exhibit the Hilbert space and self-adjoint operator realizing it, with a prime modification of the archimedean reference that is not trace class and is as large as `S(T)`, and whose Euler factors are not unit-modulus. The field's positivity theorem and its realization theorem are the same theorem.
5. **A parity-breaking additive input at a single modulus.** The minimal observable that separates two weights with identical divisor-sum data, Ramanujan covariances and pronic Gram data but opposite trans-horizon energy growth. Its existence as a pair is the sharp statement of what sieve data cannot see; its negation is a Type-II input that does not exist in present analytic number theory.

### Criteria the field must meet

- **Selectivity.** Every theorem states what it says for `ζ(s−a)ζ(s+a)`, for a Beurling system with an off-line zero, and for the Liouville-twisted weight. A statement surviving all three is not about RH.
- **No family average.** Statements hold for one character, modulus one, shift zero.
- **Square-root precision beyond the diagonal.** Prime sums of length at least the height, controlled beyond the mean-value regime.
- **Node criticality.** The mechanism distinguishes `log 4` from `log 6`; sampling-density, Nyquist and generic uncertainty arguments are excluded in advance.
- **Every height.** A statement about an exceptional set, a proportion or a typical member is infrastructure, not progress.
- **Complete expression, no margin.** Mean, diagonal, mixed terms, Gamma and polar charges, endpoints and inherited history are retained; the inequality to be proved is critical, so certificates with slack are impossible and exact cancellation is the only form a proof can take.
- **Units.** Progress on positivity is reported as the level `a` at which the Hodge index holds for the actual configuration, or as a bound on the reflection defect `Z(f) − W(f,f)`; progress on cancellation as the exponent `θ` actually obtained; progress on localization as the depth `δ(n, R)` excluded below height `T(n, R)`. Identities, finite classifications and nonselective positivity count as zero in these units.
- **Calibration.** A method claiming a cofinal sign or cancellation should either reproduce the corresponding theorem over `F_q[T]` or say why it cannot.

### Questions it must answer

1. Is the odd arithmetic jump form critical or supercritical, and what object certifies the answer? (RH is "not supercritical".)
2. Which profiles leave the anti-diagonal prime mass unpaid, and what classifies them?
3. How does one dyadic prime window at one height couple to the archimedean term through the functional equation; what replaces phase freedom?
4. What is the smallest additive input breaking parity at a single modulus, and what is its exact loss?
5. In which Schatten or deficiency class, on which Hilbert space, do the primes modify the archimedean operator to realize the critical-zero measure?
6. What in the multiplicative incidence of the node set `{log n}` makes `log 4` indispensable and `log 6` redundant, and how is that read by a positivity argument?
7. What is the exact tradeoff between aperture, height localization and arithmetic length needed to make a given off-line configuration visible, and what is the strongest estimate available at that length?

### Tools it aims to develop

- Ground-state representations in sign-changing gauges and a Harnack inequality for the arithmetic jump kernel across prime shifts.
- Localized explicit formulas at height `T` with the off-diagonal pair structure at bandwidth `λ > 1`, organized around the square-root threshold rather than the cutoff.
- Internal bilinear dispersion with modular inverses at a single modulus.
- Profile decompositions in the complete-form norm (origin bubbles, distant copies, oscillatory waves) reducing positivity on all tests to positivity on single-frequency profiles.
- Conditioned-tail estimates for the deterministic zeta orbit on a prescribed disc, beating the generic `1/κ` loss.
- Quantitative selectivity units and a function-field calibration module.

### What it would look like in practice

Theorems come in pairs: every invisibility theorem with a visibility witness, every identity with the estimate it enables or the sharp boundary it proves. Every statement is calibrated by height, aperture and the strongest unconditional value. Positivity statements are checked against the shifted pair and against Beurling systems before they count. The first theorems within reach are falsifiable and not routine: the gauge argument through the first prime window; existence or impossibility of a sign-changing folded supersolution satisfying both moment conditions; the parity pair for trans-horizon sieve data; a single-modulus dispersion estimate on the prime-pair Gram; localized positivity at aperture `α log T` for all heights outside an explicit exceptional set, which would isolate the every-height problem as the sole remainder. Each of these either produces the first selective, cofinal, weight-specific estimate the corpus does not have, or sharpens the obstruction into a positive survivor. That, and not another equivalent formulation of RH, is what would constitute progress.
