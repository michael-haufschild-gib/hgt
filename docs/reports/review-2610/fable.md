# Review 2610 — Fable: the frontier read as one problem, and what a field that solves it would look like

Status: 2026-10-26. Sources: the six review documents named in the brief (route ledger, killed routes, route unification, hard obstacles, walls ledger, what-forces-blindness) and the 27 programme READMEs, read in full; the Lean corpus searched with `scripts/formal_tools.py research` (batches A–F, logged in `logs/fable-review-2610.md`). Nothing was compiled or audited; `[L]`, `[S]`, `[P]` are quoted from the ledgers. This is an interpretation of other agents' mathematics, not a verification of it.

The three questions of the brief are answered in §3 (new mechanism), §4 (three focus questions) and §5 (the new field). §1 is the consolidated ledger of what is and is not proved; §2 is the reading on which §3–§5 rest.

---

## 1. The consolidated ledger

### 1.1 One sentence per wall

Every obstacle in the corpus is one of three readings of a single sentence — *what forces the actual arithmetic source `Λ` (with its pole weight one and its Gamma factor) to be blind to off-line zeros?* — read as a **rate** (Wall 1, critical arithmetic sign), as a **transfer** (Wall 3, readings, norms, limits, selection) or as a **carrier** (Wall 14, realization and forcing). The corpus has proved the three readings equivalent at their endpoints: a generic orbit's growth rate is the depth of the deepest zero it sees; orbit Hodge positivity is blindness; the maximal sharp-stable positive Meyer ideal is the off-line-blind ideal and equals the whole source iff RH.

### 1.2 What is proved (the load-bearing theorems)

The following are the results on which every later judgement in this report depends. They are quoted from the ledgers; each is `[L]` unless marked.

**Blindness of single-channel positivity.**
- Every sharp-stable right convolution ideal of the Meyer source with nonnegative trace lies inside `meyerTraceBoundedIdeal`, the ideal of sources whose Mellin transform vanishes at every off-line zero; this ideal carries Hodge index, Riemann–Roch, Bézout and ampleness unconditionally and equals the whole source iff RH (`isGreatest_meyerSharpPositiveIdeal`). Every scale-shift-invariant Weil-nonnegative test space is off-line blind.
- Positivity on point-stable coupled carriers forces reflected off-line fibres to be isotropic; convolution ideals without sharp stability are only half-blind; the left-blind ideal (bounded backward flow) is positive, strictly larger than the blind ideal if `¬RH`, and the whole source iff RH (`CoupledPositivityIsIsotropy`).
- The blind ideal is closed in the natural Fréchet topology, dense in the critical-jet topology, and closed there iff RH. Spectral synthesis inside it is complete: critical jets plus the Poisson boundary synthesize the full-jet blind ideal.

**Multiplicative positivity is a complete boundary theory and a closed interior method.**
- The boundary divisor of nonnegative log-coefficients is an even positive-definite function on `ℝ`; integer values and a simple pole make it a sign character of a subgroup; pole isolation makes it `δ₀` — hence `ζ(1+it) ≠ 0`, with each of the four invariants necessary (`boundary_forcing_law`). A pole of order `k` carries at most `⌊k/2⌋` boundary zeros, every placement realized (`total_zero_mass_le`, `BoundaryZeroCapacity`). Locally finite and absolutely summable positive-definite profiles are exactly the boundary divisors of integral Euler products.
- In the interior the method reduces to one scalar law: exclusion iff `√A + √(Gη) < √B`, width exactly `(√B − √A)²/G`; the Fejér barrier `a₁ ≤ 2cos(π/(K+2))a₀` and the multi-frequency cap `a(γ) ≤ 2a(0)` bound every finite certificate by `(3 − 2√2)/(2L)`; the quantum budget `b(η) = (√A + √(Gη))²/B` satisfies `b(½) ≥ 1` once `L ≥ 0.17`: **there is no quantized inequality at the critical line inside multiplicative positivity** (`fejer_quantumBudget_half`).
- Completed positive systems (holomorphic nonvanishing on `Re s > 1`, positive-definite vertical sections of `Re(−F′/F)`, order-one completion with the functional equation): `κ < 2Σm` forces a zero off `Re s = 1`; at most `⌊κ/2⌋` zeros in a collar of width `≍ 1/(d log T)`; `5d < 9κ`; the pole-budget-one class is exactly `ℝ^× · ζ` (`TheSimplePoleClassIsZeta`); a positive Laplace correction of `ξ` with the functional equation is trivial (`simple_pole_nonneg_laplace_refund_rigidity`); pole order two admits every off-line type (real pairs, refunded quartets).

**Rigidity identifies the source and nothing else.**
- A positive measure on `[1,∞)` with Riemann's theta law is a Dirac comb on the integers; a Beurling system with the completed functional equation is `ζ` with a norm-preserving bijection of prime labels onto the rational primes (`PositiveMeasureHamburgerRigidity`, `BeurlingRiemannFunctionalEquationRigidity`). Every relaxation (pole order two or three, strip poles, no FE, no positivity) has an explicit off-line model. Rigidity is linear in the measure; zeros are not.

**Pole order pays inserted charge exactly and intrinsic charge not at all.**
- `(Weil-index increment) = (pole-order increment) + R_crit − I_crit` is an identity; the absolute inequality `ind₋ ≤ ord₁F − 1` is false; for `ζ` every deformation yields only lower bounds on its index (`WeilIndexConservation`). Hence `ζ`'s own off-line zeros, if any, are paid only by oscillation of the zero sum — a rate, i.e. Wall 1 (face 1.16).

**Depth homogeneity.**
- Every amplification over `ℤ` tested — harmonic twists `n^{−ikt}`, Følner height coupling, family averages over `χ mod q`, external and relative tensor powers, archimedean moments — gains on a zero's depth exactly as fast as it pays in arithmetic length. Product receivers see depth only through total length (`ProductReceiversSeeDepthOnlyThroughTotalLength`); gauge Jensen makes every multiplicative amplification lose linearly; family moments lose linearly unless flat, and flat on a curve is pure (`MomentAmplificationOfAnyFamilyLosesLinearly`). Over `𝔽_q` the loss of a base is fixed and disappears under `2k`-th roots; over `ℤ` no base is known. Receiver form: `|c(t)|^k ≤ Ce^{L_k t}` gives width `≤ L_k/k`; linear loss is the strip; sublinear loss is RH (`TheBaseIsAFixedLoss`).

**The first rung of every cancellation receiver is a fixed zero-free strip.**
- Balanced statistic, centred-prime band, short windows, every Vaughan power improvement, JAS level one, PBM abscissa, WL rate `σ`, admission at a fixed damping: each weakest nontrivial statement is `Θ < 1` (`balancedStatisticPowerSaving_iff`, `UniformVaughanPowerBoundsAreFixedStrips`). Unconditional arithmetic stops at Vinogradov–Korobov; no receiver has a target between VK and a fixed strip.

**Gauge: multiplicative information is an orbit, arithmetic is a point.**
- The gauge torus `(ℝ/ℤ)^{primes}` acts by unimodular completely multiplicative twists; every product-coincidence statistic is gauge invariant; every additive relation (`ab − cd = h`, affine maps, the successor) is gauge charged. Haar-almost every twist of a bounded source has square-root cancellation `|Σ_{n≤N} a_nχ(n)| ≤ C√N log²N`; for `μ` the half-power law holds a.e., fails at the Liouville twin `μ²`, and holds at the arithmetic point `0` iff RH (`AlmostEveryGaugePointCancelsToTheSquareRoot`). The exceptional set is comeager and Haar-null; the point `0` lies in its closure. The coalescent prime-pair surplus is pure gauge charge and splits exactly over the Dirichlet stabilizers.
- The boundary of a dilation at a finite horizon with absorbing boundary is finite and nonzero exactly at the weight `n^{−1/2}`, where it equals `log a` — the archimedean degree; the Möbius boundary tends to `0` (PNT) while its Liouville twin's boundary stays `≥ 1/100` (`TheMoebiusBoundarySeparatesGaugeTwins`). This is the only proved mechanism that separates the arithmetic point from a twin.

**Local geometry: multiplicative symmetry is hyperbolic exactly off the line.**
- At a reflection pair `{ρ, 1−ρ̄}` the Rosati trace has signature `(1,1)`; Hecke, archimedean and twisted symbols act as boosts iff `Re ρ ≠ ½`, forcing isotropy of every positive cyclic span; elliptic action occurs only on the line or at a resonant prime, and a non-real point resonates at most at one prime. The successor is unipotent on polar fibres: zeros are atoms of the archimedean dilation spectrum, and the successor reads only its continuous part (`successor_sees_autocorrelation`, `successor_blind_of_atomic_archimedean`). The integer successor forces the Hecke weight `(nd)^{−1/2}` on dilations, is positive definite iff `s ≥ ½`, and its dilation spectrum is Kronecker-null, mutually singular with Weil's correlation (`TheIntegerSuccessorForcesTheHeckeWeight`, `TheCriticalLineOfTheIntegerSuccessorIsTheKakutaniWall`).

**Weil's argument over `ℤ`, layer by layer** (ACP): identities, the theorem of the square and the budget `δ(x,x)` are free and hold on the golden datum `1 − 5X + 5X²`; kernel counts are blind to complex quartets (the complex fake `q = 16`, roots `±8i, ±2i`); the spectrum of symmetric squares is the sign; exterior-power counts force unitarity over `𝔽_q`; Rosati positivity is RH; the base is a fixed loss. Affine correspondences of `ℤ` have genus zero. Nonlocalizing positivity exists (radius `3/10`, every prime weight) and is source-blind; on nonnegative tests `ζ` is the worst twin.

**Averaged positivity and its selection boundary.**
- Short-window averaged Weil positivity holds at aperture `κ₀ log Γ` on windows `Γ^{99/100} ≤ H ≤ Γ/8` (`ShortWindowAveragedWeilPositivity`, new since 2510); at all but `CH/η` zero ordinates every `F ≥ 0` satisfies `Q_γ(F) ≥ (∫F)² − 4η(A+1)²e^A N(F)²`. The negative floor is governed by `Φ(γ) = Σ_ρ (Re ρ−½)²/(1+(Im ρ−γ)²)²`, which is large exactly at an off-line ordinate; a negative witness persists on height length `2(1−r/Z)/A` (`TheWitnessOfAZeroPersistsForTheReciprocalAperture`). Selection below the zero spacing is RH-strength.

**The square-root threshold.** An off-line lattice at zero density is invisible to every test of aperture `≤ L/2` (primes up to `X ≍ T`) and visible beyond; hiding is mimicry; for `ζ` hiding needs collapsed clusters. Montgomery's pair correlation holds unconditionally at leading order for `0 < α < 1` (`tendsto_montgomeryForm_div_leadingOrder`); beyond `α = 1` the content is the signed coalescent prime-pair surplus; `β ≤ 1/18` at bandwidth `4/3` gives a `3/4` proportion, `β < 5/36` beats `2/3`.

**Quantization on the quadratic side.** The Hodge defect `D = sup_a hodgeDefectAt(ζ,a)` counts distinct right zeros; it is even; `RH ⇔ D < 2`; collision mass after small positive heat equals `2(D+E)`; `2·#{distinct right zeros below T} ≤ horizontalCollisionCharge(T)`; a real-valued source quantity eventually below the two-unit quantum gives RH (`riemannHypothesis_of_twoPrimeSourceExcess_eventually_bounded_lt_two`).

**Escape states.** The cofactor Gram of the damped Möbius receiver is a translation Gram of the log profile with Laplace symbol `G(s) = ζ(s)(1/ζ(s+ε) − Re(1/ζ(1+ε)))/s`; escape states of finite and `ℓ¹` dominant configurations are phase kernels of rank the number of dominant translated zeros, horizon averages select them, dilation acts as the archimedean flow (ACP P18–P26, the last `[S]`); `RH ⇔` every actual cofactor limit at every `0 < ε < ½` has positive gauge mass. For `ζ` what remains is the explicit-formula split of the profile — an analytic input of the type the explicit formula for `M(x)` needs.

**Arithmetic Euler characteristic.** The two-pole Chebyshev defect `E(s) = e^s + s − 1 − ψ(e^s)` equals polar-box degrees of freedom minus weighted prime nodes, and at `s = log(N+1)` equals `N − log|ℤ/Q_Nℤ|`, `Q_N = lcm(1..N+1)/(N+1)`: integer degree minus logarithmic torsion; it is not an ordinary dimension difference (`E(log 3/2) ∈ (0,1)`); adjacent period reductions have cyclic kernels of log-order `Λ(N+1)` (`boxDefect_eq_degree_sub_log_torsion`). The theta `h⁰` of `Spec ℤ` has exact Riemann–Roch `h⁰(d) − h⁰(−d) = d` and recovers `Λ(s)` by Mellin transform; this is the base's Riemann–Roch, it gives the functional equation, not the surface's Hodge index.

### 1.3 What is not proved (and is not an artefact of the formalization)

- Any unconditional signed estimate at a positive slack: bounded critical energy, a one-sided lag bound, an `H¹` floor at rate below `½`, admission of the damped Möbius receiver at any `ε < ½`, a fixed zero-free strip.
- Any Weil-type sign on an RH-complete family at unbounded aperture; the even sector past `½ log 2`; the odd sector beyond `181/500`.
- Any selection theorem from short-window averages to one height below the zero spacing.
- Any budget for intrinsic charge: a source bound on the Hodge defect, the collision charge or the two-prime source excess below `2`; even finiteness of `D` (which would already give finitely many off-line zeros).
- Any base over `Spec ℤ` with fixed loss; any gauge-charged correspondence with a budget independent of the order.
- Any section theory on the scaling surface whose Riemann–Roch is proved without the sign; every ample cone's RR is equivalent to the Hodge inequality (universal floor law), finite readings never give Bézout, positive majorants give Bézout but kill RR.
- The coalescent surplus at bandwidth `4/3`; the explicit-formula split of the damped Möbius prefix; residue summability of `1/ζ′(ρ)` along a line of zeros.
- The first gauge-charged window: whether odd positivity on `[−181/500, 181/500]` fails for the weight with `Λ(2)` flipped (the Liouville-twisted certificate exists only with an explicit prime-2 correction term, `re_weilFullFunctional_liouvilleTwist_odd_window`).

### 1.4 What changed between the 2510 review and this reading

Short windows `H ≥ Γ^{99/100}` replace `[Γ,2Γ]`; the pole-budget-one completed class is `ℝ^×·ζ` `[L]`; the Haar-a.e. square-root law and the charged-boundary threshold `σ = ¼` are in; the theorem of the square and the similitude budget are proved free `[L]`; exterior-power counts force unitarity over `𝔽_q` `[L]`; zero-cost contraction of real off-critical pairs in completed systems `[L]`; anchor-paid and height-coupled quartet contractions and the countable escape model are `[S]`. None of these moves a wall; each sharpens its boundary.

---

## 2. The reading: why the three walls are one hole, and what shape it has

### 2.1 Every proved forcing is "exact identity + quantization", and quantization runs out at the local zero density

The three forcing laws share a shape: an exact identity whose two sides have different regularity (a sum of nonnegative terms equals a computable constant), followed by an integer step (integer divisor orders, integer-valued positive-definite functions, integer pole order). Each stops at a computed boundary, and the boundary is always the same number: the **local density of zeros**.

- A pole budget is `O(1)` (`κ`); an archimedean budget is `Re(Γ_ℝ′/Γ_ℝ)(σ+it) ≍ ½ log|t|`, which is the local zero count `(1/2π) log t` per unit height. The height-coupled multiplicity bound `8N + 4m_{½} + 4m_{½+iγ} < 18κ + 3d log(3+|γ|) − 7d/2` says it exactly: the number of off-line quartets at an ordinate is bounded by the number of zeros there. Budgets built from the pole and the Gamma factor are saturated by on-line zeros alone.
- Hence no inequality of the form `budget ≥ weighted zero charge` can see an off-line zero unless off-line zeros are *more expensive* than on-line ones in that inequality. They are, but only through growth in a scale: an off-line pair at depth `δ` contributes `p^{mδ}` to the Lefschetz sequence `c_m` while on-line zeros contribute rotations; a fixed budget is overflowed on a segment of length `≍ log(budget/weight)/δ` (ACP P12). This is Weil's inequality `|Σα_i^m| ≤ 2g q^{m/2}` and the corpus's `RH ⇔ |c_m| ≤ c_0` at any one prime: the triangle inequality saturated by unitary eigenvalues, violated eventually by any non-unitary one.
- So the hole is not a missing budget. The budget `c_0 = W(g,g)` is free; its *positivity* — that it is a budget at all — is full Weil positivity. "The budget is free, its sufficiency is not" (ACP P2). Over `𝔽_q` sufficiency comes from Riemann–Roch on `C × C`: sections exist in quadratic abundance when `D² > 0`, effective divisors meet the ample class nonnegatively, hence Hodge index. Over `ℤ` the universal floor law shows that *every ample cone's* RR is equivalent to the Hodge inequality: inside a cone formalism effectivity is tautological. Weil's sections are dimensions of genuine function spaces; the corpus's section counts do not grow (`h⁰ ≤ 1`; rank counts are reweighting-invariant).

### 2.2 Why quantization has no slack at pole order one

The completed-positive class at `κ = 1` is the single point `ℝ^×·ζ`. Positive relative deformations of `ξ` at pole order one are trivial. A forcing law acts on a *class*; at `κ = 1` the class is a point, so class-level forcing (invariants, capacity, deformation bookkeeping) has nothing left to say. The next forcing law must act on an object strictly larger than `ζ` in which `ζ` sits non-rigidly: a **family over a base** (F1) or a **surface in which `ζ`'s data form a fibre** (F3). This is the structural reason the corpus keeps arriving at Deligne's base and Weil's surface, and why "more invariants on the line" is finished.

### 2.3 Counts versus oscillation: where integrality lives over `ℤ`

Over `𝔽_q` both sides of the explicit formula are counts. Over `ℤ` the prime side is a sum of logarithms of orders of finite cyclic groups — `Λ(N+1)` is the log-order of the kernel of `ℤ/lcm(1..N+1) → ℤ/lcm(1..N)` — and the zero side is an oscillatory sum. The explicit formula reads: *logarithmic torsion = oscillation of the zeros + archimedean density*. RH says the oscillation is square-root small. The integers over `ℤ` are therefore not dimensions but **log-torsions**, i.e. real numbers of a special kind; the arithmetic Euler characteristic `E(s) = degree − log torsion` is the honest analogue of `χ(O(D))`, and it is *not* of the form `h⁰ − h¹` with natural-valued `h`'s. An arithmetic cohomology for this problem must be real-valued (log-volumes, as in van der Geer–Schoof's `h⁰ = log θ`), and effectivity must be positivity of a log-volume, not membership in a cone. The corpus has the base version (theta `h⁰` on `Spec ℤ` with exact RR = Poisson); the surface version is absent and is the content of F3.

### 2.4 The finite places are sign-blind; the sign lives at the archimedean boundary

Complete-period quadratic data (the geometry over `ℤ/lcm(1..N)`, Selberg coordinates, Ramanujan sums) are exactly sign-blind: they classify sources only up to independent Selberg-coordinate signs. Dilation boundaries at an absorbing horizon are finite and nonzero only at the critical weight, where they equal the archimedean degree `log a = Σ_p v_p(a) log p` — the product formula appearing as a boundary term. The Möbius boundary tends to zero, its Liouville twin's does not: orientation is visible *only* at the boundary, i.e. at the archimedean place. This is the `ℤ`-analogue of the fact that over `𝔽_q` everything is finite and the sign is carried by finite cohomology; over `ℤ` the sign must be carried by an **archimedean (Arakelov-type) object**. It is also why the only non-tautological positive-definite structure the corpus found on `Aff(ℚ)` with the integer successor is `p`-adic (Hecke weight, Kronecker-null spectrum) and mutually singular with Weil's archimedean correlation: additive structure, read through positive-definite functions, couples to the finite places; the zeros are atoms of the archimedean spectrum and are invisible to it.

### 2.5 Selection is a vicious circle at the zero's own height

Averaged positivity at logarithmic aperture holds in short windows, with a negative floor proportional to `Φ(γ)`, the squared depth of the zeros near `γ`. A witness of an off-line zero at `γ₀` persists on height length `≍ 1/A`. To exclude the zero one needs the sign at heights within `1/A` of `γ₀` with `A → ∞`, where the prime polynomial at that height is dominated by that zero. Phases of finite prime sets recur syndetically, so no eventual saving exists at every height; a saving at the height of a zero forces a companion. Selection below the zero spacing is Wall 1 in Wall 3's clothing.

### 2.6 Frobenius is the ring map `ℤ` does not have

Over `𝔽_q` the sign is produced by a correspondence (Frobenius) that is simultaneously additive and multiplicative. Over `ℤ` the dilations are multiplicatively covariant and additive in the trivial sense, the successor is additive only, affine correspondences have genus zero (at most one periodic point, two graphs meet at most once), and the only ring endomorphism of `ℤ` is the identity. The coupling of `+` and `×` in `ℤ` is carried by Bézout relations (`gcd(n,n+1) = 1`, `pa − qb = 1`) and by the carries of positional arithmetic — exactly the gauge-charged data. Every mechanism that sees RH must use them; the corpus proved this twice (Beurling systems satisfy every multiplicative identity; gauge orbits satisfy every multiplicative statistic). The successor laws found so far (one-third floor, quantized biases) are density-scale, not square-root-scale.

### 2.7 The three questions of the 2510 review are one question in three currencies

F1 (a base with fixed loss), F2 (signed near-coincidences beyond the threshold) and F3 (Riemann–Roch for oscillatory payment) are the same demand: **a term that does not scale with amplification, attached to the actual arithmetic point, that reads oscillation rather than pole charge, and that localizes at off-line pairs with a non-hyperbolic local symmetry.** The ledger's four phrases are the four faces of this one object; §5 proposes a field whose purpose is to construct it.

---

## 3. Question 1 — is there a mechanism that circumvents or destroys a wall?

### 3.1 Verdict

No mechanism in sight destroys a wall. What the corpus has done is to show that Walls 1, 3 and 14 are one wall, and to compute its exact shape (§2). Three families of mechanisms are finished and should not be reopened: single-channel quadratic positivity on sharp-stable carriers (blind by theorem); finite or height-coupled multiplicative certificates (capped by growth; no quantum at `½`); invariants and pole bookkeeping on the line (rigid at `κ = 1`). The honest statement is that any new mechanism must come from a *larger object* than `ζ` on the line (§2.2) and must satisfy the four criteria of §2.7.

Within that constraint, four candidate mechanisms are worth building. Each is stated with its first provable statement, the battery it must pass, and what would kill it.

### 3.2 M1 — oscillatory capacity through the two-unit collision quantum

**Idea.** The quadratic side has what the multiplicative side lacks: a quantized inequality at the critical line. `D` is even and `RH ⇔ D < 2`; the two-prime source excess is a *real* quantity whose eventual bound below `2` implies RH, and the ledger notes that "a merely normalized `o(N(T))` estimate cannot replace this absolute bound below the two-unit quantum". The target is not `D = 0` but `charge < 2`: the fractional part is free. A real-valued arithmetic quantity bounded by `1.99` would do.

**Why it is not already dead.** The known no-go (holomorphic clocks realize quantized zero-side forms only as `0/∞` growth; a sub-unit margin is idle, KR-R3) concerns *holomorphic* readers of the zeros. The two-prime source excess is built from prime data and a Cesàro carrier, not from a holomorphic function of the zeros. The budget `2` is a *fixed* number (it does not scale with height or aperture), so a bound below it is exactly a term that does not scale.

**First statement.** Prove any unconditional *finite* bound on the horizontal collision charge uniformly in `T`. This alone gives finitely many off-line zeros, hence `Θ < 1` — a fixed zero-free strip — and would be the first unconditional theorem in the corpus beyond Vinogradov–Korobov. The second statement is the bound below `2`.

**What blocks.** The small-time ceiling on collision mass diverges as `t ↓ 0` (`CεR(t) log(2+3R(t))`); every known bound is a count of local zeros, i.e. density, not sign (§2.1). A finite bound requires reading the *oscillation* of the horizontal zero pairs — the same demand as F3. M1 is the place where F3 has a numerical target.

**Battery.** Must fail for `CompletedPositiveSystem 2 1` real pairs and refunded quartets (their collision charge is `≥ 2`), reproduce the collar results as capacity statements, and be stated without reference to the zero divisor.

### 3.3 M2 — gauge-charged windows and the square-root boundary law

**Idea.** The only proved separation of the arithmetic point from a twin is the Möbius boundary (PNT at the boundary). The only positivity window that meets a prime is the odd window `181/500`, whose Liouville-twisted version carries an explicit prime-2 correction. Two statements would make "gauge charge" a theorem-producing principle rather than an organizing one:
1. decide whether odd positivity on `[−181/500, 181/500]` fails for the weight with `Λ(2)` flipped (ACP §9.2). A failure is the first unconditional positivity theorem that distinguishes `ζ` from a dominated twin, on a sign-changing atom, exactly where ACP P7 says it can happen;
2. the square-root boundary law (ACG §9.2): a signed source whose escaped pairing against the flat critical source is `O(N^{−θ})` uniformly in the multiplier `a`, for some `θ > 0`. For `μ` this is a zero-free strip — the correct first rung of Wall 1 — but stated in coordinates (finite horizon, absorbing boundary, affine action) that retain the additive structure the multiplicative formulation discards.

**Why it matters.** It is the only route in which the Beurling and Liouville countermodels are excluded *by the mechanism itself*, not by a battery check afterwards.

**What blocks.** Beyond `½ log 2` the even sector pays the pole directions; past the first prime every window must pay several strips and the pole jointly (AIP); the boundary law at square-root scale is quasi-RH. Progress is a window past `½ log 2` on the full sector whose certificate uses the sign of the atom at `log 2`.

### 3.4 M3 — an intrinsic exterior square for `ζ`

**Idea.** Over `𝔽_q` kernel counts on `H¹` miss complex quartets and exterior powers `Λ^k H¹` repair this; `Λ²H¹` is intrinsic and carries no shifted poles. Over `ℤ` the height-coupled lift `F(s)²F(s+iγ)F(s−iγ)` imitates `Λ²` (it collides `±iγ` onto `0` and supplies the real anchor the real-anchor law demands) but pays shifted Gamma factors and leaves the class `[S]`. The question (ACP §9.3) is sharp: construct a completed positive system whose divisor is the exterior square of `ζ`'s (zeros at `ρ_i + ρ_j − ½`-type sums) with pole data `(κ₀, κ_γ) = (1, 0)` and no shifted Gamma, or prove that every positive lift realizing `(±iγ) ↦ 0` over `ℤ` carries shifted poles.

**Why it matters.** With an intrinsic `Λ²`, complex quartets contract at zero pole tax inside the original class and the `κ = 1` rigidity turns from an obstruction into a forcing law. The Rankin–Selberg field law (ACP P15: the polar residue of `Λ ⋆ Λ` at a zero is the field of all other zeros, transversal exactly on critical configurations) says the object is nonlocal at the polar level — which is what an exterior square should be.

**What blocks.** Depth homogeneity: an exterior square built as a product of spectra is homogeneous (AKT); it must be built as a *correspondence* (layer 2), i.e. a pairing on the product, not a product of pairings. Likely outcome: an impossibility theorem naming the shifted-pole cost as intrinsic over `ℤ`, which would itself be a sharp positive survivor.

### 3.5 M4 — escape completeness for `ζ` by an explicit formula for the damped Möbius prefix

**Idea.** Prove, at one `ε ∈ (0,½)`, that `A_ε(n)` splits into the dominant configuration of translated zeros `ρ − ε` plus a remainder of subdominant energy. This is a contour shift of `G(s)e^{su}` past the translated zeros and needs growth of `1/ζ(s+ε)` on horizontal segments between zeros and summability of residues `ζ(ρ−ε)/(ζ′(ρ)(ρ−ε))` (ACP §9.8–9.9).

**Why it matters.** It closes the escape classification (U1's only non-rate handle): escape states would be *exactly* translated-zero phase kernels, with gauge mass zero, and the receiver's module structure (paid ideal, Wiener hull, horizon order) would become a statement about `ζ`'s zero set alone. It also produces, as a by-product, an unconditional explicit formula for the damped Möbius function with controlled remainder.

**Honest cost.** This is classical hard analysis of the `M(x)` explicit-formula type; its payoff is a classification, not a sign. It belongs to the infrastructure of the field in §5, not to its breakthroughs.

### 3.6 Mechanisms I would not pursue

New RH-equivalent receivers in new units; new single-channel positive carriers; new countermodels with a proper subset of the four invariants; new pole-order bookkeeping; family averages or tensor powers of `ζ` as amplification; attempts to read orientation from complete-period (finite-place) data; positive-definite functions on `Aff(ℚ)` with free successor coordinates; Lee–Yang, Ising, photonic or operator realizations whose inputs are the zeros.

---

## 4. Question 2 — the three open questions to focus on

The 2510 review chose F1, F2, F3. I keep F2 and F3, make them concrete, and replace F1 (the base problem, which the corpus has shown to be non-abelian and not definable from multiplicative structure — a foundational problem for §5 rather than a research target) by the gauge-charged boundary. The criterion: each question must have a first rung that is a *new unconditional theorem*, must sit at the meeting point of two walls, and must be falsifiable by a battery.

### OQ1 — Signed near-coincidence of prime pairs beyond the square-root threshold

**Statement.** Bound the coalescent prime-pair surplus at bandwidth `λ = 4/3`: `oddEvenShiftPrimeCoalescentSurplus u η T ≤ (β + o(1)) N(T,2T)` for one profile and one `0 < η < 1/3`, i.e. the signed correlation of odd primes `(m, m+2h)` with `|log(m/m′)| ≤ T^{−1+η}`, integrated against the signed coalescent kernel. Targets: `β < 5/36` beats `2/3`; `β ≤ 577/4500` beats `HD(1)`; `β ≤ 1/18` gives `3/4`; the Hardy–Littlewood value is `−1/144`.

**Why this one.** It is the square-root threshold in its plainest form, at *finite* bandwidth, with a numerical budget. The obstruction is exactly characterized: the surplus is pure gauge charge, Haar-a.e. twists satisfy every budget, and the actual statistic is its congruent part over each Dirichlet stabilizer plus a discrepancy of zero character mean. The remaining target is the **residue-class discrepancy of close prime pairs** against a signed kernel — a problem of the Matomäki–Radziwiłł–Tao type, where the live technology (Fourier uniformity, logarithmic Chowla, short-interval prime correlations) is the strongest it has ever been. Poisson without repulsion fails (`+1/16`); the budget needs arithmetic repulsion: this is a genuine test of whether the Hardy–Littlewood singular series can be controlled at scale `1/T` with a sign.

**First rung.** Any `β < 5/36`: a new proportion theorem. **Payoff.** Progress on the simplicity and critical proportions; the first signed estimate beyond `X = T` in the corpus; the "constants-only law" of AKT becomes testable.

**Battery.** Must use the actual primes (fails for Haar-typical twists in the sense that it gives *less* than the typical bound), must retain all prime powers before elimination, must not be a positive-kernel bound (which bounds the worst twist).

### OQ2 — The first gauge-charged positivity theorem and the square-root boundary law

**Statement.** (a) Decide the Liouville-twisted odd window: is `Re W_w(F ⋆ F̃) ≥ 0` for all odd `F` supported in `[−181/500, 181/500]` when `w = Λ` with `Λ(2)` flipped? (b) Extend unconditional positivity on the *full* sector past `½ log 2` by a certificate that uses the sign of the atom at `log 2` and fails on the flipped twin. (c) The square-root boundary law: escaped pairing `O(N^{−θ})` uniformly in the multiplier for the signed source `μ(j)/√j`.

**Why this one.** The corpus's central thesis — multiplicative information is an orbit, arithmetic is a point — has exactly one proved instance (the Möbius boundary at PNT strength). Every route needs a sign that is specific to the gauge point. (a) is decidable by a finite certificate and would be the first positivity theorem in the corpus that is *selective*; (b) is the first window that reads a sign-changing atom on all tests; (c) is the first rung of Wall 1 (a fixed zero-free strip) in the coordinates that keep the additive structure.

**First rung.** (a). **Payoff.** Converts gauge charge from an organizing principle into a producer; identifies which tests (negative atom at `log 2`, ACP P7) carry selectivity; gives the field of §5 its first *charged* positivity law.

**Battery.** Golden datum and Beurling systems (no successor), the Liouville twin, the shifted pair; the certificate must name the atom whose sign it uses.

### OQ3 — Riemann–Roch on the scaling surface with real-valued cohomology (F3 made concrete)

**Statement.** Define `h⁰` and `h¹` on the scaling surface as log-volumes of genuine function spaces — functions in polar boxes with vanishing conditions at the weighted prime nodes, or theta-type log-volumes — prove the exact identity `E(s) = h⁰ − h¹` with `h⁰, h¹ ≥ 0` *defined independently of the sign of the Weil form*, with Serre duality `h¹(D) = h⁰(K − D)` given by the functional equation and `K` the archimedean (Gamma) divisor, and show that `h⁰` of a class with positive self-intersection grows — a section count beyond the Nyquist diagonal that beats the mean value theorem using the actual `Λ`.

**Why this one.** It is the only face at which Wall 14 has a constructive, non-tautological target: the corpus proved that *within cone formalisms* RR is the sign (universal floor law), that finite readings never give Bézout, and that `h⁰ ≤ 1` cannot pay unbounded fibre intersection. The arithmetic Euler characteristic already has one computation (degree minus log torsion); RR is its second computation. The retirement criterion is stated by AOT: if the only sections are those the large sieve counts, the contribution is a dictionary — and that is a theorem worth having too.

**First rung.** A *selective* section count beyond the diagonal at one exponent — one that separates `Λ` from the shifted pair `Λ(n)(n^a + n^{−a})` (rank counts cannot; Frobenius mass can). **Payoff.** If `h⁰` grows, effectivity is constructed and the Hodge index follows by the corpus's own equivalences; if it does not, the theorem "sections over `ℤ` are large-sieve sections" is the precise form of the square-root threshold on the geometric side, identifying OQ1 and OQ3 as one question.

**Battery.** Must reproduce Weil for curves with `h⁰` the dimension and budget `2g`; must fail RR on the golden datum's positive graph cone; must not read `x² ≥ 0`.

### Why not F1 as a focus question

The base must be non-abelian, must not be definable from multiplicative structure (over-regular Beurling countermodels), and over `ℤ` the only candidate "genus-zero base" visible in the corpus is the pole plane — a two-dimensional hyperbolic space, not a space with points. F1 is the right *foundational* question of §5; as a research target it has no first rung.

---

## 5. Question 3 — the field that would supply the missing tools

### 5.1 What the walls ask, read as one question

The walls, read as questions mathematics cannot presently answer:

1. Which integer, attached to the integers themselves and not to the zeros, bounds the oscillation of the zero sum? (Wall 1.16, 14.4)
2. What is a *section* on `Spec ℤ × Spec ℤ`, and when do sections exist in quadratic abundance? (14.4, 14.6, B3.5)
3. What is the ring map that couples `+` and `×` in `ℤ` strongly enough to separate the arithmetic point from its gauge twins at square-root scale? (B3.20, B3.21, 1.15)
4. How does a positivity proved on average over heights localize at a single height below the zero spacing? (3.14, B1.4)
5. What is the base over which `ζ`'s zeros are local data with a fixed loss? (14.14, B3.19)

Each is answered over `𝔽_q` by one structure — the intersection theory of correspondences on a surface with finite-dimensional cohomology and the Frobenius ring map. Over `ℤ` the corpus has the surface (scaling surface), the correspondences (Hecke algebra with Rosati), the identities (Lefschetz, adjunction, theorem of the square, budget), the base's Riemann–Roch (theta), and exact no-gos for every substitute. The field proposed here is the one whose object is the missing structure.

### 5.2 Name and definition

**Arithmetic effectivity theory** (working name): the study of real-valued cohomology and effectivity on the arithmetic surface `Spec ℤ × Spec ℤ` — concretely, on the scaling surface with its correspondence ring, its finite-horizon presentations and its gauge torus — with the aim of producing *signs from integers*: an intersection-theoretic proof of positivity in which every inequality is the comparison of two computations of one Euler characteristic, and in which the integers are log-orders of finite groups and log-volumes of lattices rather than dimensions.

Its guiding sentence: *RH is the Hodge index theorem of an arithmetic surface whose points are the primes with residue size `log p`, whose cohomology is measured by volume, whose Frobenius is the Hecke correspondence ring, and whose boundary is the archimedean place.*

### 5.3 Point of view

- **Surface, not line.** Work on `Spec ℤ × Spec ℤ` (cycles, correspondences, pairings), never on functions of one variable `s`. Every statement about `ζ` is a statement about a cycle, a correspondence or a class on the surface.
- **Counts before estimates, identities before signs.** Every sign is to be derived from an exact identity between two independent computations of an integer-valued or log-torsion-valued invariant, with positivity entering only through the existence of a section (`h⁰ > 0`) or the order of a group.
- **The archimedean place is the boundary.** The finite places are sign-blind; orientation is carried by boundary terms at the critical weight, where the product formula appears. Cohomology is Arakelov-type: log-volumes, theta functions, Gamma factors as the canonical class.
- **Gauge charge is the arithmetic.** Every statement declares whether its quantities are gauge invariant (multiplicative, orbit-level) or gauge charged (additive, point-level). Only charged statements can be RH-relevant; charged statements must name the additive relation they use.
- **Budgets must not scale.** Every amplification declares its loss law; the field seeks structures with a fixed loss (bases, budgets of correspondences, archimedean constants), and rejects anything whose gain on depth equals its cost in length.
- **Local type at off-line pairs.** Every correspondence declares its local type (hyperbolic, elliptic, unipotent) at reflection pairs; forcing can come only from non-hyperbolic action on localizing carriers.
- **Calibration is mandatory.** Every construction is run over `𝔽_q` (must reproduce Weil with budget `2g`), on the golden datum and the complex fake (must fail), on the pole-order-two models, Beurling systems, the shifted pair and the Liouville twin (must be separated from `ζ`).

### 5.4 Objects

| Object | Role | Present status |
|---|---|---|
| Scaling surface `S`: pole plane `⟨H,V⟩` (signature `(1,1)`, the `ℙ¹`-like base with poles at `0, 1`) ⊕ tests; pairing = explicit formula | the arithmetic surface | built (ACS, AOG); Hodge index ⇔ RH |
| Correspondence ring `G →₀ ℝ` with Rosati, Hecke graphs, normalized graphs, budget `δ(x,x)` | Frobenius replacement | built (AOG, ACP); theorem of the square free |
| Finite-horizon presentations `{0..N}` with affine action and absorbing boundary; escaped pairing; torsion `ℤ/lcm` | finite places and their boundary | built (BG, ACG); boundary = archimedean degree |
| Gauge torus `(ℝ/ℤ)^{primes}`; gauge charge; Dirichlet and sign subgroups; archimedean line | the orbit/point distinction | built (ACG) |
| Arithmetic Euler characteristic `E(s) = degree − log torsion`; node-divisor `h⁰`-supply/`h¹`-obstruction | the invariant to compute twice | one computation built |
| Theta `h⁰` on the base with RR; the Gamma factor as canonical divisor; the sharp involution as Serre duality | real-valued cohomology | base only |
| Completed positive systems; height-coupled systems; contraction multipliers | the deformation class of `ζ` | built; `κ = 1` rigid |
| Escape states as phase kernels of translated zeros; gauge mass | the limit objects of receivers | model built; `ζ` open |
| Hodge defect `D`, collision charge, two-prime source excess | the quantized target | built; no budget |
| Section spaces: polar boxes with weighted prime-node conditions; Dirichlet samplings; paid ideals of `𝒲_{1/2}` | candidates for `h⁰` | partial (AOT); not selective |

### 5.5 Language

*Degree* (pairing with `H + V`), *budget* (self-defect of a cycle), *charge* (negative index of a form; collision mass), *capacity* (largest charge a positive structure admits), *inserted vs intrinsic charge*, *gauge invariant vs gauge charged*, *local type* (hyperbolic/elliptic/unipotent at a reflection pair), *scaling class* (gain exponent vs cost exponent of an amplification), *loss law*, *persistence scale* (`≍ 1/A`), *boundary* (escaped pairing at a horizon), *torsion* (order of a finite transition group), *section* (an element of a function space with prescribed poles and nodes), *effective* (`h⁰ > 0`). A contribution names, for every quantity, its gauge type, its local type, its scaling class and its battery behaviour.

### 5.6 Foundational principles the field must establish (its axioms-to-be-theorems)

1. **Surface Riemann–Roch.** An exact identity `E(D) = h⁰(D) − h¹(D) + h²(D)` on `S` with `h^i ≥ 0` real-valued and defined without the sign of the pairing; `h²(D) = h⁰(K − D)` by the functional equation; `K` the archimedean divisor.
2. **Product formula at the boundary.** The boundary of every correspondence at the critical weight equals its archimedean degree (proved for dilations); the boundary calculus is a cocycle (proved).
3. **Effectivity.** `h⁰(D) > 0` implies `D · (ample) ≥ 0`: effective classes meet the pole plane nonnegatively; Bézout for sections (the corpus has Bézout for nonnegative tests via the Lévy jump form; the field needs it for sections).
4. **Abundance.** If `D² > 0` then `h⁰(nD)` grows quadratically in `n` — the sections exist. This is the step the universal floor law shows cannot be a cone axiom; it must be a theorem about the function space.
5. **Budget law.** `δ(x,x)` is invariant along orbits (proved); its sufficiency follows from 1–4 (formal, proved as an equivalence).
6. **Charge law.** The additive structure enters only through gauge-charged sections (built from `ab − cd = h`, successor graphs as moved diagonals at Nyquist scale); the coupling of `+` and `×` is a statement about which sections exist.
7. **Localization law.** A global inequality on `S` localizes at a reflection pair iff the carrier localizes; isolation needs hyperbolic growth or length `≳` inverse spacing (proved); the field needs the selection theorem that turns abundance of sections at aperture `A` into a sign at one height within `1/A`.

### 5.7 Criteria it must fulfil

Derived from the corpus's no-gos; a construction failing any of them is already dead.

1. Reproduce Weil's theorem for curves, with `h⁰` the dimension, budget `2g`, and the theorem of the square in genus one.
2. Fail on the golden datum `1 − 5X + 5X²` and the complex fake (`±8i, ±2i`): both pass every identity, every count positivity, every Künneth/Adams positivity, Bézout and ampleness on Rosati cones; only RR separates them.
3. Separate `ζ` from `CompletedPositiveSystem 2 1` pairs and quartets, pole-order-three and strip-pole quartets, over-regular Beurling systems, `Γ_ℝ^d` solutions for `d ≥ 3`, dominated and flipped twins, the shifted pair.
4. Use all four invariants jointly (positivity, functional equation, simple pole, strip holomorphy); reproduce `κ = 1` rigidity and the boundary capacity `⌊κ/2⌋`.
5. Contain a term that does not scale with amplification; state the loss law of every amplification used.
6. Be gauge charged: fail on the Liouville twin by the mechanism, not by a battery check.
7. Localize with non-hyperbolic local symmetry at off-line pairs, or prove that localization is unnecessary because abundance is global.
8. Read oscillatory payment: see `ζ`'s own zeros through a term that is not pole charge; reproduce the index–pole conservation identity as its relative case.
9. Never substitute a reading for its source (no finite readings as Bézout, no complete-period data as orientation, no averages as selected heights, no zero-indexed objects as pre-divisor constructions, no transfer from a zero-free region as forcing).
10. Be unconditional and in Lean: no RH-equivalent hypothesis, no interface carrying the missing input.

### 5.8 Research topics, in order

1. **Sections on `S` (OQ3).** Candidate function spaces: polar boxes with weighted prime nodes (the `E(s)` computation), theta-type log-volumes (van der Geer–Schoof on the surface), paid ideals of the critical Wiener algebra. Prove RR for one of them; test selectivity against the shifted pair; locate the Nyquist diagonal in each.
2. **The boundary law at square-root scale (OQ2c)** and the first gauge-charged window (OQ2a–b).
3. **Residue-class discrepancy of coalescent prime pairs (OQ1).**
4. **Oscillatory capacity (M1):** finiteness of `D`; the two-prime source excess below `2`.
5. **The intrinsic exterior square (M3)** or its impossibility theorem.
6. **Escape completeness for `ζ` (M4):** the explicit formula for the damped Möbius prefix; summability of `ζ(ρ−ε)/(ζ′(ρ)(ρ−ε))`.
7. **The base problem (F1) as `ℙ¹` over `𝔽₁`:** is the pole plane a base in Deligne's sense — can a local system over it have `ζ`'s zeros as eigenvalues with fixed loss? State the axioms (simple pole, no zeros, self-dual system with nonnegative even tensor-power log-coefficients, computable pole part) and prove that multiplicatively definable data admit Beurling countermodels.
8. **Charged correspondences.** Pair forms on `ℕ × ℕ` from `ab − cd = h`, successor graphs as moved diagonals, Pell/norm-form orbits (where the sign gauge sees infinitely many partners); find one with a budget independent of the order.
9. **Selection calculus.** From short-window averages to heights: exceptional sets below the persistence scale `1/A`; the scale-matched schedule `L/2 < A(L) ≤ L` with precision `o(L³)`.
10. **Depth homogeneity as a theorem per class** (W8): a scaling-class calculus with gain and cost exponents, proved for mixed-sign, renormalized and family receivers.
11. **Arithmetic Stepanov.** The corpus has characteristic-zero Stepanov for shifted roots-of-unity subgroups (`#{x : x^t = α, (x−μ)^t = β} < 4B²`); the arithmetic version needs auxiliary sections over `ℤ` whose forced vanishing bounds a spectral count — the same object as topic 1.
12. **Calibration library.** Every topic run over `𝔽_q[t]` (gauge torus, degree character, successor charge, where Weil's bound enters) and on the full battery.

### 5.9 How the field would know it is empty

- If every section space on `S` with RR has `h⁰` bounded by the large-sieve count (AOT's retirement criterion), effectivity over `ℤ` is the square-root threshold and the field's content is the dictionary identifying OQ1 and OQ3.
- If every gauge-charged window past `½ log 2` fails on the full sector, selectivity is not a positivity property at bounded aperture and the field must work only at unbounded aperture.
- If every positive lift realizing `(±iγ) ↦ 0` carries shifted poles, the exterior square is not intrinsic over `ℤ` and the quartet obstruction is absolute.
- If the collision charge admits no finite source bound, oscillatory capacity is not a quadratic-side object.

Each of these is a theorem the field would prove; none has been proved.

---

## 6. Closing

What the corpus has achieved is not a route but a *map*: the exact boundary of every mechanism that can be built from positivity of `Λ`, the functional equation, the simple pole and strip holomorphy, taken one, two or three at a time, on the line. The map says that the fourth forcing law is not on the line. It is on the surface, it is charged, it does not scale, and it reads oscillation through sections. The three questions of §4 are the three places where that law would first become visible as a theorem; the field of §5 is the one in which it would be stated.

---

## Appendix A — what was read

Reports: `docs/reports/rh-current-frontier-map.md` (checkpoint `8765b382d`), `docs/reports/rh-killed-routes.md`, `docs/reports/review-2510/route-unification-ledger.md`, `docs/reports/review-2510/hard-obstacles.md`, `docs/reports/review-2510/walls-ledger.md`, `docs/reports/review-2510/what-forces-blindness.md`. READMEs: arithmetic-positivity-theory, BiScaleUncertainty, TransHorizonIncidenceMechanics, BezoutValuationIncidence, ArithmeticCriticalityTheory, SquareRootThreshold, ArithmeticIncidencePositivity, ArithmeticContinuationAndCriticalEnergy, ScaleSignedIncidenceCriticality, ArithmeticCompensationTheory, ArithmeticCastelnuovoSeveri, SignedArithmeticEnergyIncidence, TransThresholdPairCorrelation, ArithmeticOrientationTheory, ArithmeticOrientationGeometry, ArithmeticLocalDivisorGeometry, SignedSuccessorArithmetic, ArithmeticDefectRigidity, BiarithmeticGeometry, MultiplicativePositivityGeometry, ArithmeticPositiveDuality, StripBochnerWeilForcing, ArithmeticCorrelationGeometry, ArithmeticKunnethTheory, ArithmeticCorrespondencePositivity.

Corpus searches (declaration leads cited above are leads from the search tool, not audited): oscillatory capacity; escape states; Rankin–Selberg; base/tensor loss; Bézout/successor; short-window averaging; coalescent surplus; Hodge defect/collision; prime anti-diagonals; elliptic carriers; quasicrystals; Bost–Connes; Lee–Yang; Stepanov; character families; Guth–Maynard; Mertens explicit formula; residue summability; Selberg CLT; pair correlation; successor/continuous spectrum; exterior square; symmetric Hecke; theta `h⁰`; witness persistence; repulsion; gauge-charged window; arithmetic Euler characteristic; pole plane. Log: `logs/fable-review-2610.md`.

## Appendix B — dictionary of the three currencies

| Currency | Reading of blindness | Endpoint theorem | First rung | Partial-progress axis |
|---|---|---|---|---|
| Rate (U1) | growth of a generic orbit = depth of deepest seen zero | `RH ⇔ groundRate = 0 ⇔ E bounded ⇔ cofinal admission` | fixed strip `Θ < 1` | none below quasi-RH; escape classification |
| Sign (U2) | Weil positivity = spectral side of the explicit formula positive | `RH ⇔ μ(A) > 0 ∀A ⇔ finite-level weights exist ⇔ Bochner on T²` | windows `3/10`, `181/500`; averages at `log Γ` | aperture; selection |
| Carrier (U3) | exhaustion of the maximal blind ideal | `meyerTraceBoundedIdeal = ⊤ ⇔ RH`; Hodge index ⇔ RH; `D < 2 ⇔ RH` | boundary forcing; capacity `⌊κ/2⌋`; `κ = 1` rigidity | sections; budget; base |
