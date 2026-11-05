# Fable report — the RH programme read as one problem

Companion to `rh-current-frontier-map.md`, `rh-killed-routes.md`, `review-0311/route-unification-ledger.md`,
`review-0511/route-obstacles.md`, `review-0511/obstacles-summary.md`, `review-0511/walls-ledger.md`, and the
paper proof `docs/drafts/pipeline/2-fully-proven/two-sided-theta-mollifier-trap.md` (taken as correct). Corpus facts
were checked against Lean statements through the corpus search tool; the declarations relied on are listed in
Appendix A.

Evidence: `[L]` Lean statement read in this review; `[L*]` Lean per the ledgers, not re-read here; `[P]` the paper
proof of the theta-trap card; `[D]` derived in this report from `[L]`/`[P]` statements; `[N]` numerical (summary 1.15);
`[E]` external mathematics outside the corpus, cited from memory and to be checked before use.

Notation. `w := zetaZeroWidth = sup_ρ |Re ρ − ½|` (RH ⇔ `w = 0`; a zero-free half-plane `Re s > 1 − η`, "quasi-RH",
⇔ `w ≤ ½ − η`). Windows have half-width `a` and length `L = 2a`; `W = H − P` is Weil's form, `H` the archimedean–polar
part (all prime weights `0`), `P` the prime part with weights `w_n = Λ(n)n^{−1/2}` at the lags `log n`. A mollifier
is `Ψ(s) = Σ_{d≤y} b_d d^{−s}`, `b_1 = 1`; it is prefix-exact to `X_1` when `c_n = Σ_{d|n} b_d = 0` for `2 ≤ n ≤ X_1`
(the Möbius mollifier `b_d = μ(d)`, `d ≤ X`, is prefix-exact to `X`).

## 1. The picture in six statements

### 1.1 One number
Every wall measures `w`. In Lean, for ζ: the orbit correlation of one generic bump grows like `e^{wt}` and no faster
(`zeta_orbitCorr_rate_iff_zetaZeroWidth_le`, and RH ⇔ eventually bounded, `riemannHypothesis_iff_eventually_bounded_of_generic`)
[L]; the window ground energy on windows of length `L` decays no faster than `−Ce^{wL}` (Σ28) [L*]; the de Bruijn–Newman
constant on the nonnegative heat axis vanishes iff `w = 0` (`zetaZeroWidth_eq_zero_iff_newmanConstant_eq_zero`) [L];
the number of right zeros equals the supremum of negative indices of spline-atomic Weil Grams on log shifts
(`zeta_splineAtomic_negIndex_law`) [L]; the inner-cap flux of WD is the off-line generating function `Σ m_ρ e^{(ρ−½)t}`
[L*]. There is no second invariant in play anywhere in the corpus: a route either computes `w` in its own coordinates
or proves something blind to `w`.

### 1.2 One sign in three coordinates
RH ⇔ every two-site lattice window of every nonzero bump is positive definite
(`riemannHypothesis_iff_two_site_posDef`) ⇔ `|c_φ(t)| < Q(φ)` for every bump and `t ≠ 0`
(`riemannHypothesis_iff_abs_weilOrbitCorr_lt`) ⇔ every Levinson error is positive ⇔ every Schur parameter lies
strictly inside its Levinson error (`posDef_succ_iff_abs_schur_lt`) [L]. The two-site entry is the trivial-divisor
moment minus one smoothed prime count over `[e^{t−2r}, e^{t+2r}]` (Σ ∩ Π) [L*/D]; the completed Weil form is the Krein
form of zero coordinates, and the Mayer defect vanishes exactly on the quarter line (Σ ∩ Γ:
`mayerDefect_nonneg_representation_iff`, `resonantLewisPeriod_coIsometryDefect_lt_zero_iff`) [L]. All of this is
receiver: exact, RH-equivalent, and silent on which side holds.

### 1.3 Criticality
Every exact reading sits at zero slack. Full Weil positivity forces the weights to be `Λ`
(`weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt`, with `eq_vonMangoldt_of_weilPositiveFull` unconditional)
[L]; the window cone's coordinates converge to `Λ(n)` (`exists_forall_abs_sub_vonMangoldt_lt`) [L]; the only
admissible Hardy multiple is `1` and no Hardy weight survives on odd tests [L*]; the Perron structure ends exactly at
`log ρ`, `ρ³ = ρ + 1` [L*]; the Mayer defect is `≤ 0` always and `= 0` exactly on `Re s = ¼`
(`retainedHeckeChannel_defect_sign`) [L]; the Euler side of the finite free split is stable with drift exactly
`θ_S/2` [L*]; the heat saddle enters at exactly `½/log X` [L*]; numerical margins of the arithmetic point collapse from
`1.8×10⁻⁴` at `c = 0.40` to `1.6×10⁻¹¹` at `c = 0.66` [N]. A proof of RH is therefore not an estimate with room to
spare; it is an identity at the boundary of a cone that contains exactly one point.

### 1.4 Blindness theorems
Every finite aperture is blind to every width: for all `a` and `0 < δ ≤ ½` there is a tempered configuration of width
`δ` whose Weil form is nonnegative on tests supported in `[−a, a]` (`exists_configWidth_eq_and_weil_nonneg_on_aperture`)
[L]. Every property of weights that implies the count `ψ(x) − x = O(√x log²x)` is false for the Liouville twin, cannot
hold for both `a` and `a + εn^{−η}` (`0 ≤ η < ½`), is not determined by any finite window, and has stabilizer inside
the square-root class (`deciding_input_necessary_properties`, `not_of_finite_window`) [L]. Hadamard powers of Weil's
kernel carry RH at every degree (`riemannHypothesis_iff_isPosDefKernel_zetaKernel_pow`) and the Künneth square has
index `0` or `∞` (`riemannHypothesis_or_negIndex_kunnethZeta_eq_top`) [L]: Deligne's tensor-power amplification has
no analogue. Type I and Type II information are parity-blind (APR) [L*]; counts, Tate positivity, finite-rank
realizations, finite templates past spread `6`, Markov and sign-gauge certificates past `log ρ` and `½log 2`,
size-only heat repair, and height-local decisions are all refuted at explicit thresholds [L*].

### 1.5 The vacuity boundary and the two ladders `[D]`
Read quantitatively, Σ and Π are two ladders whose first rung with zero content is a zero-free half-plane
(quasi-RH), and whose top is RH. Every known result stands exactly on the near side of the content boundary.

| Ladder | Parameter | Trivial / known | First content rung | What the rung gives | Top |
|---|---|---|---|---|---|
| Σ, growth of window negativity | `σ` in `W(f) ≥ −Ce^{σL}‖f‖²` on windows of length `L` | `σ = ½` is trivial (`Λ ≥ 0`, `Σ_{n≤e^L}Λ(n)/√n ≍ e^{L/2}`); sub-exponential corrections are the classical zero-free regions | `σ < ½` | zero-free half-plane `Re s > ½ + σ` (Σ28) [L*] | `σ → 0` |
| Σ, positivity aperture | `a*(ζ)` | `a_∞ ≈ 0.362` [L*]; zero information needs `a ≳ 4` in the model, `≈ 20` with the explicit detector [L*/D] | `a ≈ 4 … 20` | depth `≈ e^{−a/(C log T)}` excluded at height `T` [L*] | `a* = ∞` |
| Π, mollifier length | `θ`, `X = T^θ`, bounded dyadic mean square of `ζ M_X`, `M_X` prefix-exact | asymptotics for `θ < 4/7` (Conrey) and `θ < 17/33` for general coefficients (Bettin–Chandee–Radziwiłł) [E]; the large sieve stops at `θ = 1` | `θ > 1` | `w ≤ 1/(2θ) + ε` eventually (card (3)) [P] | `θ → ∞` |
| Π, density near the line | `c` in `N(σ,T) ≪ T^{1 − c(σ−½)}` | Selberg `c = ¼` [E]; a bounded mollified mean square at length `T^θ` gives `c = 2θ` through the spike of the card and only `c = θ` through Littlewood–Jensen [P/D]; the density hypothesis is `c = 2` | `c > 2` | `N(σ,T) < 1` for `σ > ½ + 1/c`: a zero-free half-plane | `c → ∞` |
| P5, heat horizon | `κ` in `Λ_X ≤ κ/log X` | `κ = 6600/9991`, sharp for its four-piece margin [L*]; the saddle is `½` | `κ < ½` | collision exclusion at height `X` below the saddle [L*] | `Λ_X = 0` |

The coincidence is not accidental: the deciding-input theorem says every precision-blind tool must stop before the
content boundary, and the content boundary of each ladder is exactly where the tool class changes (from `Λ ≥ 0` and
mean values to signed cancellation). The two ladders also explain each other: the density exponent `c = 2θ` near the
line is twice the mollifier exponent (the card's spike bounds each zero's unit window by `Y^{2δ}`, where
Littlewood–Jensen only sees the log-average), so "the density hypothesis near the critical line" and "mollifiers of
length `T`" are the same threshold, and "beyond the density hypothesis" is the same statement as "beyond the large
sieve" and as "a zero-free half-plane".

### 1.6 Sign versus size; fixed length versus scaling length `[D]`
Positivity at window half-width `a` confines every zero at height `T` to depth
`< 10⁶ exp(−a/(480000 log(T+3)))` [L*]: a window of fixed length resolves depth exponentially in its length, at all
heights at once. A mean square at Dirichlet length `T^θ` resolves depth `1/(2θ)` at height `T` [P]: polynomially in
the logarithmic length, and only at the height it is tied to. The signed explicit formula is exponentially more
efficient than any unsigned mean value, which is why the Σ programme is right in principle; but Σ statements are
"fixed length, all heights" and Π statements are "length proportional to log height", and the two are identified only
through `w` (1.1). No transfer between the ladders exists below the content boundary [D]: a Π result at `θ < 1` is
not a Σ result at any aperture, and conversely.

## 2. Status quo

### 2.1 Receivers (RH-equivalences proved in Lean)
Two-site positivity, strict orbit Cauchy–Schwarz, Levinson/Schur recursion [L]; Weil cone `= {Λ}` [L]; Hadamard and
Künneth powers [L]; Mayer–Krein positivity, quarter line, retained Hecke channel [L]; squared-gap reality at near
coincidences (`pair_type_of_hankel`, explicit heights in `pair_centre_and_gap_rvm_explicit`) [L]; finite free:
RH ⇔ Möbius-mollified Jensen polynomials stable at infinitely many degrees
(`riemannHypothesis_iff_frequently_stable_mollified`) [L]; de Branges chain: RH or a fixed evaluation kernel diverges at
contact (`riemannHypothesis_or_kernel_unbounded_at_contact`, with a genuine Hermite–Biehler structure,
`kernel_christoffelDarboux`) [L]; Hodge index of the scaling surface ⇔ RH (`scalingSurface_hodgeIndex_iff`) [L];
critical-scale clustering in eight forms (`criticalClustering_logMean_mollifier_hecke_tfae`) [L]; Speiser on the line
with the exact identity `2 Re(ζ'/ζ)(½+it) = Re(χ'/χ)` (`two_mul_re_logDeriv_riemannZeta_criticalLine`) [L];
Báez-Duarte hard direction (`exists_bdRiesz_norm_lt_of_rh`) and the mollifier defect as a sawtooth form
(`mollifierDefect_eq`) [L]; Bagchi recurrence and universality interfaces [L].

### 2.2 Selection and uniqueness
Only `Λ` is Weil-positive; every nontrivial prime pattern is separated; Selberg-class rigidity at `σ = ½`; Legendre
`J(ρ)` real ⇔ RH; an approximate functional equation with small critical-line defect forces a Beurling system's
primes to be the primes (`beurling_primes_of_critical_line_defect`) [L/L*]. Selection is complete and automatic after
positivity; it never produces positivity (Γ16).

### 2.3 What is unconditionally positive or bounded
Weil's form is positive on all real `C²` tests to total length `≈ 0.7243` [L*] and on the two-site lattice to
`n·h + r ≤ 181/250` (`toeplitzPosDef_of_short`) [L]; floors `(1/20000)/2^k` along a strictly increasing aperture tower
from `a_1 ∈ (0.362, 0.3621)` [L*]; the complete Weil matrix is positive definite below the eighth-root overlap and at
one small critical multiple [L*]; `|ζ(½+it)| ≤ C t^{33/200} log t` (`exists_norm_riemannZeta_half_le_subWeyl`) [L];
`newmanConstant < 1/8` (Ki–Kim–Lee) [L]; the heat horizon `6600/9991` [L*]; the critical-line census `≥ 0.6725` [L*].
Below `log 5` the window problem is the `{2, 3, 4}` sliver band, below `log 4` a two-weight convex membership, with
margins `10⁻⁵`–`10⁻⁸` [L*/N].

### 2.4 Structure theorems
The window algebra is a truncated Dirichlet λ-ring without internal Frobenius; Frobenius at scale `t` is translation
by `t` [L*]. The window tower is a canonical system: Weil sequences are Toeplitz, their Levinson recursion is explicit,
under RH every lattice is Szegő singular (Σγ² = ∞) [L*/L]. The even kernel is Markov exactly to `log ρ`; the odd
sector is frustrated from `½log 2`; frustration is switching-invariant (`frustrationIndex_switch`,
`isBalanced_iff_frustrationIndex_eq_zero`) and controls the ground energy (`groundEnergy_le_frustrationMass`) [L].
The camera identifies configurations to clusters of diameter `e^{−c log³T}` and reads squared gaps from three
prime-side images [L]. A pincer programme not listed among the research programmes shows diluted crystal
configurations become visible at explicit apertures and formulates a crystal-gap/prime-torus incompatibility
(`dci_pincer_master_theorem`) [L]: shielding configurations are themselves constrained by the primes.
Finite free probability reproduces de Bruijn–Newman criticality exactly: heated Jensen
polynomials never split for any `t > 0` (`eventually_not_splits_heatOp_jensenPoly_XiC`) while symmetrized Euler
products split at every degree (`splits_jensenPoly_symEuler`) [L].

### 2.5 The theta-trap card `[P]` and what follows from it `[D]`
The card proves: (1) for `0 < θ < 1`, every mollifier of length `≤ T^θ` with bounded coefficients has dyadic mean
square `≥ (1 + e^{−2a} log(1/θ) − ε)T` at `σ = ½ + a/log T`, and `≥ (c e^{−2a}/θ − ε)T`; (2) for every fixed nonzero
Dirichlet polynomial `Ψ` the Jensen budget `½ log(T⁻¹∫|ζΨ|²) − T⁻¹∫ log|Ψ|` diverges like `½ log log T`; (3) an off-line
zero of depth `δ_0` forces a spike `≳ δ_0 e^{−2αδ_0²} Y^{2δ_0}` in the mollified mean square near its ordinate for every
prefix-cancelling mollifier, hence bounded dyadic mean squares at prefix length `T^{θ_1}` give `w ≤ 1/(2θ_1) + ε`
eventually, and cofinal boundedness at all lengths gives RH.

Consequences.
- **The Π ladder is a theorem.** Length exponent `θ_1` buys width `1/(2θ_1)`; content starts at `θ_1 > 1`, exactly where
  Montgomery–Vaughan and the large sieve stop (1.5). Mean-value technology currently reaches `θ ≈ 4/7` (Möbius) and
  `17/33` (general) [E]; the gap to content is the Π wall in numbers.
- **The Jensen route to 100% clustering is RH-complete.** `B20` (`T⁻¹∫_T^{2T} log|ζ(½+it)| dt → 0`) through
  Littlewood–Jensen needs mollifiers `Ψ_T` with `T⁻¹∫|ζΨ_T|² → 1` and `T⁻¹∫ log|Ψ_T| → 0`. By (1) this needs length
  `T^{1−o(1)}` at least; by the floor's structure (every `y`-rough integer contributes `|b_1|²/v`) the excess over `1` is
  carried by the coefficients `c_n`, `n ≥ 2`, so forcing it to vanish forces approximate prefix exactness at every
  length, which is the hypothesis of (3) at every `θ`: RH. (Modulo matching the approximate prefix-cancellation
  hypothesis of (3) exactly.) `B20` remains the strongest valid sub-RH zero statement (6.1), but its only known
  mechanism is as hard as RH.
- **The critical-scale depth distribution has a method floor.** At depth `a/log T` the Jensen budget with length `T^θ`
  is `≈ ½ e^{−2a} log(1/θ)`: the proportion of zeros deeper than `2a/log T` cannot be pushed below `≍ e^{−2a}log(1/θ)/a`
  by Littlewood–Jensen with `θ < 1`. Selberg's density exponent `¼` near the line [E] is of this type.
- **Fixed mollifiers are useless for the line.** (2) kills every "choose one good Euler or Möbius polynomial" strategy
  for log-mean or clustering statements.

## 3. The walls read as mathematics

### 3.1 Σ: positivity inherited along the aperture without margin
Σ is a "fixed length, all heights" statement (1.6). Its content is that positivity of `W` on `[−a, a]` propagates to
`[−a−ε, a+ε]` for every `a` with zero slack: the de Branges chain never reaches contact [L]. Frustration past `log ρ`
(even) and `½log 2` (odd), unswitchable by any sign gauge [L*/L], removes at one stroke every positivity-preserving
mechanism of mathematics: Perron–Frobenius and Beurling–Deny (Markov certificates), Lee–Yang (ferromagnetic
real-rootedness; frustrated models violate the circle theorem [E]), Griffiths–Kelly–Sherman inequalities
(`PrimeIsingArbitraryGraphGKSNoGo`) [L], and—because reflection positivity is proved in statistical mechanics through
the transfer matrix's positivity—also the standard proof of Γ. Σ and Γ are one obstruction: a frustrated signed form
that is nevertheless reflection positive (if RH) for a reason no positivity-preserving structure explains.

### 3.2 Π: the parity problem in multiplicative-character form
For additive phases `e(nα)`, Vaughan's identity turns `Σ Λ(n) e(nα)` into Type I sums (exact, Möbius) and Type II
bilinear sums where the bilinear structure produces power savings. For multiplicative phases `n^{−it}` the Type II
sums factor, `Σ a_m b_n (mn)^{−it} = (Σ a_m m^{−it})(Σ b_n n^{−it})`, and give nothing pointwise; this is the content of
"bilinear forms are parity blind" [L*]. What survives is mean values of Dirichlet polynomials, which are sharp up to
length `T` (large sieve). Beyond length `T`, the mean square of `Σ_{n≤X} a_n n^{−it}` over `[T, 2T]` is governed by the
near-diagonal `|m − n| ≲ X/T`, i.e. by the additive shifted correlations `Σ_n a_n ā_{n+h}` for `1 ≤ h ≤ X/T`
(Conrey–Keating's framework) [E/D]. For Möbius coefficients these are Chowla correlations, and the saving required is a
factor `≍ T/X` on average over `h`, not the `o(1)` of Matomäki–Radziwiłł–Tao [E]. The Π wall at its first content rung
is therefore one explicit additive problem: Möbius autocorrelations with power saving on average over shifts
`h ≤ T^{θ_1 − 1}`, `θ_1 > 1` (7.3).

### 3.3 Γ: reflection positivity of a frustrated system, and the quarter line
PM has shown the Krein form on resonant states is strictly negative off `Re s = ¼` in two coordinate systems, and that
any nonnegative representation of the defect is RH [L]. In scattering language the sign is the one PM cannot
produce: the Hecke eigenvalue `p^{s−½} + p^{½−s}` of the resonant Eisenstein series has modulus `p^{(1−β)/2}`, and RH
says all resonances are equally non-tempered, at `p^{1/4}` [D]. Arthur-type constraints do not apply to resonant
states, which are not in `L²`.

### 3.4 The dynamical mirror
For dynamical zeta functions, zero-free strips are provable: Dolgopyat's method and the fractal uncertainty principle
(Dyatlov–Zahl, Bourgain–Dyatlov) give essential spectral gaps for convex cocompact hyperbolic surfaces [E]. Two facts
of that theory are instructive. First, even there the line is not reached: the Jakobson–Naud conjecture (resonances
left of `δ/2` apart from `δ`) is open; strips come from decay of correlations and uncertainty (size), the line would
need an exact symmetry [E]. Second, the arithmetic surface sits at the degenerate parameter `δ = 1` (full limit set,
cusp) where the fractal uncertainty principle gives nothing, and the Mayer operator `L_s = Σ_n (n+x)^{−2s} f(1/(n+x))`
ceases to be a transfer operator exactly on `Re s = ½`, the pole of `ζ(2s)`; the RH-bearing resonances live at
`Re s ∈ (¼, ½)`, reached only by meromorphic continuation (Lewis–Zagier), where no Ruelle–Perron–Frobenius structure
is available [E/D]. The quasi-RH/RH gap is not an artifact of arithmetic; arithmetic only removes the quasi-RH tools
as well.

### 3.5 Non-perturbativity
The deciding-input theorem (precision-faithfulness against `εn^{−η}`) [L], the collapse of the window cone to `{Λ}`
[L], and the Beurling fakes with regular integers and off-line zeros [L*] say the same thing: RH is a rigidity
property of the integers, unstable under every small perturbation of the data. Any method robust under perturbation
(statistics, density, averages, size bounds, almost-all) is excluded by construction. The proof must use exact
identities (`Λ⋆1 = log`, the Euler product, the functional equation) non-perturbatively, as Weil's proof over `𝔽_q`
uses exact integers (intersection numbers, dimensions of sections).

### 3.6 `𝔽_q` versus `ℤ`: the missing second invariant
Over `𝔽_q` the Hodge index theorem on `C × C` plays two independent integers against each other: the dimension of
sections `h⁰(D)` (Riemann–Roch) and the intersection number `D²`; effectivity is nonnegativity of a count. Over `ℤ`
the corpus has shown the two coincide: the count-valued primitive `h¹` of a window is `½Q`, Weil's form itself
(LST) [L*]. There is no second quantity to compare, which is the exact reason the count face is closed. The only
candidate for an independent invariant in the corpus is the "genus function" whose upper law is open and independent
of RH (Π16/B24) [L*].

## 4. Question 1 — circumventing or destroying a wall

**Assessment: no existing mechanism destroys a wall, and none circumvents one; the walls are the quasi-RH threshold
written in three coordinates, and every tool class known to mathematics stops at that threshold (1.5).** What the
review adds is where the walls are thin and what a breach would look like.

1. **The Π ladder has a developed technology below its content boundary.** Twisted second moments and Kloosterman
   spectral theory moved the general-coefficient barrier past `½` in 2017 [E]; the range `θ ∈ (4/7, 1)` is open,
   movable, and has no zero content, so it can be attacked without proving anything about zeros. The card turns every
   step past `θ = 1` into a zero-free half-plane. This is the only place where a classical, active technology meets a
   wall with a proven exchange rate (2.5). The Σ ladder has no analogous sub-threshold rungs: its sub-exponential
   corrections are the Vinogradov–Korobov exponent, unmoved since 1958 [E].
2. **The additive form of the first rung.** By 3.2, bounded mean squares of Möbius-type Dirichlet polynomials of
   length `T^{θ_1}`, `θ_1 > 1`, are governed by Möbius autocorrelations at shifts `h ≤ T^{θ_1−1}` with a saving
   `≍ T^{1−θ_1}` on average over `h` [D]. This is parity-sensitive and precision-faithful, as the deciding-input theorem
   requires, and it is an additive statement to which sieve and spectral methods apply in principle. It is the Π wall
   made concrete rather than circumvented.
3. **Frustration-tolerant positivity.** Since Σ and Γ are one obstruction (3.1), a new mechanism must certify
   positivity of a frustrated, infinite-rank, zero-slack form. The only families of mathematics that certify positivity
   of frustrated forms are exact sum-of-squares certificates (semidefinite duality; `B9`, exact SOS on one two-prime
   lattice) and Hodge–Riemann/Lorentzian signature theorems (one negative square, exactly the glued Weil signature
   `κ_ζ + 1 = 1` under RH) [L*]. The latter are proved by continuity along nondegenerate families, and nondegeneracy is
   `B10`, RH itself (Σ14) [L*]. The former needs an arithmetic structure for the squares; `B9` is where to look, and
   the corpus has no candidate.
4. **What would count as a breach.** A statement that is (i) uniform in aperture or in height, (ii) false for the
   Liouville twin and for `Λ + εn^{−η}`, (iii) not a reformulation of `w`. The corpus contains none, and the audit of
   question forms in the summary (2.5) shows why every candidate so far failed one of the three.

## 5. Question 2 — a wildly different approach

**Assessment: none exists in current mathematics, for a structural reason.** Every characterization of RH is an
equivalence, and every equivalence is a reading of `w` (1.1); an approach that "does not touch the walls" would have to
produce information about `w` without reading it, which is a producer. The corpus already covers, as receivers or
no-gos, every reading I know: positivity, precision, realization, deformation, recurrence, counts, function-field
transfer, quasicrystals, Lee–Yang, moment problems, Hermite–Biehler, finite free probability, visibility,
identification, Bost–Connes, Deninger, Connes trace formulas, Selberg/Maass traces, Nyman–Beurling, Speiser,
Beurling systems, universality. Below, the readings that are absent or only touched, with verdicts.

| Reading | In corpus | Verdict |
|---|---|---|
| Fourier interpolation and uniqueness pairs (Radchenko–Viazovska; Bondarenko–Radchenko–Seip, with the zeros of ζ as interpolation nodes) [E] | absent | A duality reading of the explicit formula; a receiver. Its toolbox (modular forms, Hardy-space interpolation, LP-dual "magic functions") is the one that produced exact zero-slack certificates in sphere packing; relevant to Programme A (10.3), not a route. |
| Dynamical spectral gaps (Dolgopyat; fractal uncertainty) [E] | Mayer/Lewis present; Dolgopyat/FUP absent | Gives strips, never the line, and degenerates at `δ = 1` (3.4). A PM-native zero-free region (B46) is the honest test. |
| Entropy decrement; Furstenberg systems of the Möbius flow (Tao; Frantzikinakis–Host) [E] | absent (A21 is a task) | Genuinely parity-sensitive, the only such mechanism of the last decade; precision-blind (`o(1)`, logarithmic averages). Its power-saving version is the additive form of the Π wall (4.2). |
| Hodge–Riemann / Lorentzian polynomials / combinatorial Hodge theory (AHK; Brändén–Huh) [E] | HWV, ALG present | Signature `(1, n−1)` is the right target shape; the proofs need nondegenerate continuity or semismall decompositions; the corpus found no signed cancellation in the divisor complex (HWV) and continuity is `B10`. |
| Interlacing families / finite free probability (Marcus–Spielman–Srivastava; Ramanujan graphs) [E] | FFP present | Proves existence of one good member of a family, not identification of a given member; FFP shows the source split of `Ξ` is unstable [L]. |
| Rodgers–Tao dynamical rigidity [E] | heat flow present | Works in the direction `Λ ≥ 0` because forward heat crystallizes and ζ's zeros are not crystalline; the RH direction is backward collision exclusion, non-generic, invisible to statistics (`B14`). |
| Deuring–Heilbronn repulsion [E] | absent | The one zero-repulsion mechanism over `ℚ`, driven by nonnegative coefficients of a product L-function and a real exceptional zero; no self-repulsion law for complex zeros of ζ is known. A structural question in the spirit of `B13` (7.1), not a route. |
| Keating–Snaith recipe, ratios conjecture, Fyodorov–Hiary–Keating, multiplicative chaos [E] | absent | Value-distribution statistics at the scale of typical fluctuations; zeros are extreme events outside the regime; precision-blind. |
| Beurling moduli: ζ as a rigid point among Beurling systems with functional equation | substantial | The corpus has fakes with regular integers and off-line zeros and a stability theorem (small critical-line FE defect ⇒ the actual primes) [L]; rigidity, not stability, is the right frame (3.5). |
| Speiser / Levinson–Montgomery: critical points of `log|ζ|` [E] | present [L] | A Morse-theoretic coordinate for `w` (zeros of `ζ'` left of the line ↔ off-line zeros); the exact identity on the line is in Lean. Receiver. |
| Franel–Landau / Farey discrepancy [E] | sawtooth form present [L] | The mollifier defect is a sawtooth `L²` form (`mollifierDefect_eq`); Farey statistics connect Π (CTF) to the cusp of the modular surface (PM). A loop of equivalences. |

Two readings are nevertheless worth stating because they are the cleanest forms of the problem.

- **RH as a feasibility problem without primes.** RH ⇔ for every `c` the convex set `𝒜(c) = {λ : H − P_λ ≥ 0 on [−c,c]}`
  is nonempty, and only `Γ`, the pole and the lag positions `log n` enter [L*]; dually (prime-blind positivity, P2):
  RH ⇔ `H(f) ≥ 0` on every test on `[−c, c]` whose autocorrelations vanish at all lags `log n ≤ 2c` [L*]. The
  arithmetic enters only through the additive semigroup `{log n} = ⟨log p⟩` and the Gamma weight; the primes are output
  (uniqueness), not input. This is a statement in harmonic analysis: the lag semigroup of the integers is
  "frequency-repelling" for the archimedean weight, which is negative below `τ_0(a)` and positive above (Σ29) [L*].
- **RH as the arithmetic Hamiltonian's regularity.** The window tower is a de Branges chain whose spectral data are the
  zeros and whose Hamiltonian is computable stage by stage from primes through the Levinson recursion [L*/L]; RH ⇔ no
  finite contact ⇔ a regular Hamiltonian at every length (Σ66, B51). The inverse spectral problem is solved in
  principle; the direct problem (regularity from the arithmetic recursion) is RH.

Neither is a new route; both say what a new route must look like (10).

## 6. Question 3 — breakthrough questions below RH and quasi-RH

Each item is checked against the summary's tests T1–T7; where it fails a test the failure is stated.

### 6.1 Whole programme
**Q3.1a. 100% critical-scale clustering (`B20`).** `T⁻¹∫_T^{2T} log|ζ(½+it)|dt → 0`, equivalently all but
`o(T log T)` zeros in `(T, 2T]` within `κ/log T` of the line for every fixed `κ`; eight forms in Lean [L]. Passes
T1–T5, T7; the only known mechanism (Littlewood–Jensen with mollifiers) is RH-complete by the card (2.5), so T6 is
open: a proof needs a handle on the log-mean that is not a mean square at length `≥ T`. Candidates for such a handle
are the negative moments / small values of `|ζ|` on the line and zero-side critical-scale density, both undeveloped.
Content: RH on average at the mean-spacing scale.

**Q3.1b. The sub-threshold Π rungs.** Bounded dyadic mean square of `ζ M_X` for the prefix-exact Möbius mollifier,
`X = T^θ`, `θ ∈ (4/7, 1)`; and the twisted second moment `∫_T^{2T}|ζ(½+it)|²(h/k)^{it}dt` with power-saving error for
`hk ≤ T^{2θ}` in the same range [E]. No zero content (T3 is methodological only), but each step is the technology the
first content rung needs, with a proven exchange rate waiting at `θ > 1` [P].

### 6.2 Route PM
**Q3.2. PM-native zero-free region (`B46`).** Prove `β < 1 − c/log|γ|` for the zeros of `ζ(2s)` from the Lewis–Hecke
carrier alone, i.e. a spectral estimate for the continued Mayer operator at `Re s = ½ + c/(2 log|t|)`. Sub-quasi-RH
(reproves a classical theorem). Its advance is methodological: the Dolgopyat–Baladi–Vallée estimates for the Gauss
map transfer operator exist near the pressure line `Re s = 1` [E]; `Re s = ½` is the pole of `ζ(2s)` and the edge of
the operator's domain (3.4). Success would show the carrier holds arithmetic beyond identification; failure would show
PM is a pure receiver. Risk, as the summary notes: the positivity used may reduce to the Euler product (A15).

### 6.3 Route MC
**Q3.3a. Two-point Chowla without logarithmic averaging.** `Σ_{n≤x} λ(n)λ(n+1) = o(x)` [E]. Not implied by RH and not
implying it (fails the summary's T1 clause "implied by RH", passes the others); parity-sensitive, which the walls
demand; precision-blind, so not an RH advance but the natural next step of the only parity-breaking mechanism known.
**Q3.3b. The Möbius mean square beyond the large sieve, below content.** `∫_T^{2T}|Σ_{n≤X} μ(n)n^{−½−it}|²dt ≪ T log X`
for `X = T^θ`, `θ ∈ (1, 1+η)`: by 3.2 this is Chowla on average over `h ≤ T^{θ−1}` with saving `T^{1−θ}`. It has no
direct zero content by itself (the mollified form is what the card uses), but it is the exact additive quantity behind
the first content rung.

### 6.4 Route WD
**Q3.4. `D_win` (`B21`) and `B20`.** `D_win`: for every `A`, at most `ε(A)V` unit windows of `[V, 2V]` contain a zero of
depth `≥ A/log V`, `ε(A) → 0` [L]. Valid, decision, false for Davenport–Heilbronn and `ζ(s)ζ(s−ε)`; no mechanism
(T6). WD's own content is otherwise zero-free verbatim (inner caps). The card sharpens WD's density branch: the
Littlewood–Jensen method floor at depth `a/log T` is `≍ e^{−2a} log(1/θ)` (2.5), so `B20`/`D_win` need a non-Jensen
input.

### 6.5 Route HF
**Q3.5. Positivity of the entire twisted sector (`B6`).** At every critical multiple and through all conductors and
moving frequencies, every twisted direction of the complete Weil family carries a positive count [L*: fixed
families]. Sub-RH (twisted sectors carry no Weil sign), decision, structural consequence: it isolates RH in the single
untwisted direction `κQ + (βJ/K)·weighted Gram` per window (Σ1j, AHD) [L*], so that HF's full-space sign becomes a
one-dimensional-per-window statement about Weil's form at the frequency pole. It does not open a door (the untwisted
direction is `R_1(A) = ⊤ ⇔ A/2 ≤ a*`, the Σ wall), but it is HF's one remaining non-vacuous structural theorem.

## 7. Question 4 — questions that would open the path wide

A question opens the path only if it names a producer. Every producer with zero content is at least a zero-free
half-plane (1.5). The items below are therefore quasi-RH or structural; none is below quasi-RH, which is the finding.

### 7.1 Whole programme
**Q4.1a. The first content rung of the Π ladder.** Bounded dyadic mean square of `ζ M_X` for a prefix-exact mollifier
of length `X = T^{θ_1}`, one `θ_1 > 1`. By the card [P] this is a zero-free half-plane `Re s > 1 − 1/(2θ_1) − ε`
eventually; climbing `θ_1 → ∞` is RH. The path is explicit and graded, which no other route offers.
**Q4.1b. The zero–one law (`B13`): `κ ∈ {0, ∞}`.** Finitely many off-line zeros ⇒ none. Sub-RH in strength, false
for the tempered lattice-plus-one-pair model (so a proof must use the Euler product) [L*], passes T1–T5 and T7; no
mechanism (T6): the `{0, ∞}` laws in Lean need escape, mixing or height decay of the carrier [L*]. It would convert RH
into an eventual statement and kill every finite-exception scenario; door-shaped like `B57`, and like `B57` it has no
mechanism.

### 7.2 Route PM
**Q4.2. A uniform spectral gap for the continued Mayer operator in `Re s ∈ (½ − η, ½]`**: a zero-free strip for
`ζ(2s)` near `Re(2s) = 1`, i.e. quasi-RH, by dynamical means. The obstacles are known: no Ruelle–Perron–Frobenius
structure past the pole line, no porosity for the fractal uncertainty principle (3.4). This is the dynamical twin of
Q4.1a.

### 7.3 Route MC
**Q4.3. Möbius autocorrelations with power saving on average over shifts.** `Σ_{h ≤ H}|Σ_{n≤x} μ(n)μ(n+h)| ≪ x` for
`H = x^{η}`, one `η > 0` (a factor `H` better than trivial, versus the `o(Hx)` of Matomäki–Radziwiłł–Tao) [E]. By 3.2
this is the additive content of the mean square of Möbius polynomials of length `x^{1+η}`, hence (through the
mollified form) of Q4.1a. It is parity-breaking and precision-faithful. Not implied by RH; stronger than needed in a
different direction; the natural statement for the production side.

### 7.4 Route WD
**Q4.4. None.** WD's RH-level estimates are the emptiness of the off-line set in another form [L]; its sub-RH content is
6.4.

### 7.5 Route HF
**Q4.5. None below the stage step.** Transport across one prime is induction on an antitone threshold, Dirichlet-shift
companions reduce long windows to head windows, and a head window is a window (`B55`) [L*]. The one door-shaped
statement, kick admission at every stage (`B2`), is RH as induction.

## 8. Question 5 — three questions to focus on

1. **The Π ladder, from `θ = 4/7` upward (6.1b, 7.1a).** It is the only wall with an active classical technology
   below its content boundary and a proven exchange rate above it. Sub-targets in order: the twisted second moment of
   ζ with power saving for `hk` up to `T^{2θ}`, `θ ∈ (4/7, 1)`; the bounded dyadic mollified mean square at `θ < 1`;
   the structure theorem that writes the `θ > 1` mean square as near-diagonal Möbius correlations plus evaluated
   terms (3.2); then one `θ_1 > 1`.
2. **100% critical-scale clustering (`B20`) by a non-Jensen mechanism (6.1a).** It is the strongest valid zero
   statement below RH, with eight Lean forms, and the card has now shown that its standard route is RH-complete; the
   research question is the alternative handle on the log-mean (small values of ζ on the line; zero-side density at
   the critical scale). A negative structural result ("every route to `B20` through Dirichlet-polynomial mean values is
   RH-complete") would itself be valuable and is within reach of the card's methods.
3. **The stage step as mechanism discovery (`B2`, `B3`, `B4`, `B5`, `B56`).** The odd unit window and the windows below
   `log 4` and `log 5` are exact finite problems in two or three weights with margins `10⁻⁴`–`10⁻¹²` [N]. They carry no
   zero information and are not doors (summary 2.8), and I agree. They are the only place where the exact certificate
   can be *written down* and inspected for what pays the kick: whether the identity `Λ⋆1 = log` on the collar, the
   Hecke/Rosati structure of the collar pairing, or a Levinson identity. The value is the shape of the certificate, not
   the window; the risk, which must be stated, is that the shape is accidental.

The three are complementary: 1 is production, 2 is the first zero statement production must deliver, 3 is the
structure that production must eventually match.

## 9. Question 6 — the one question

**There is no question below quasi-RH with zero content whose known routes are not RH-complete.** `B20`'s route is
RH-complete (2.5); `D_win` has no mechanism; every statement with power-saving global prime content is a zero-free
half-plane (1.5); every critical-scale statement reduces to mean values at length `≥ T`. This agrees with the summary's
verdict and sharpens its reason: the obstruction is the content boundary of 1.5, a property of the equivalence web,
not a shortage of ideas.

Given that, the one question I would put first is the **structure theorem for long Möbius mean squares**:

> For `1 < θ < 2`, express `∫_T^{2T} |ζ(½+it) M_X(½+it)|² dt`, `M_X` the prefix-exact Möbius mollifier of length
> `X = T^θ`, as an explicit main term plus an explicit sum of shifted correlations `Σ_n c_n c_{n+h}` of the
> coefficients `c_n = Σ_{d|n, d≤X} μ(d)` of `ζM_X` over `1 ≤ h ≤ T^{θ−1}` with explicit kernels (bilinear
> Möbius–Möbius sums with congruence conditions; pure `Σ μ(n)μ(n+h)` for the unmollified polynomial), plus an
> error `o(T)`, unconditionally.

It is below quasi-RH (a reduction, not a bound), it is a decision (the identity holds with the stated error or it does
not), its written consequence is that the first content rung becomes one additive estimate (7.3) with the exchange
rate of the card, and it meets the deciding-input criteria (parity and precision live in the correlations). It opens
the door in the only sense available: it replaces a family of equivalences by one classical problem with its own
toolbox (shifted convolutions, the δ-method, Kuznetsov), and it tells the Σ programme exactly which additive
cancellation its certificates must encode. Its risk is that the residual correlation sum is as hard as RH; the
structure theorem would make that risk precise instead of implicit.

## 10. Question 7 — the field the walls ask for

Read as questions, the walls ask: (Σ) why positivity of a frustrated form is inherited along its aperture with no
margin; (Π) which functionals of a multiplicative function carry its sign at square-root precision; (Γ) why a
reflection acts as a positivity when no positivity-preserving structure is present. The summary proposes two
programmes, A (critical Hardy theory of the window cone, receiver) and B (arithmetic production, producer). I read
them as two coordinates of one field, because in a critical problem the certificate *is* the producer: there is no
estimate step between exhibiting the exact object and concluding.

### 10.1 Name and point of view
**Arithmetic criticality: the theory of exactly critical, frustrated positive forms generated by multiplicative
recursion.** Its point of view: RH is not an inequality to be estimated but a zero-slack identity to be constructed,
uniformly in a scale parameter, from exact arithmetic identities; the construction is rigid (non-perturbative) and
algebraic in character, with analysis only to pass to the limit.

### 10.2 Objects
The window tower `W_A` and its de Branges chain (Hermite–Biehler functions `E_a`, Hamiltonian `H(t)`); the lattice
canonical systems of Spec ℤ (Weil sequences, Schur parameters, Levinson predictors); the calibration cones `𝒜(c)` and
their duals, the prime-blind cones; the window algebra as a truncated Dirichlet λ-ring; the signed coupling graphs of
the parity sectors with their frustration index; the gauge torus `∏_p S¹` with its vertical flow and Adams
semigroup, the arithmetic point as the common fixed point; the Beurling moduli of systems with functional equation;
the mollified mean squares and their near-diagonal correlation structure.

### 10.3 Language and tools
Criticality and optimal Hardy weights for nonlocal forms; frustration and switching; Krein–Pontryagin index and
generalized Nevanlinna functions; Schur–Levinson recursion and Szegő–Verblunsky theory; Wiener–Hopf and renewal
factorization of the archimedean symbol; semidefinite and LP duality with exact (zero-slack) extremizers, in the style
of the sphere-packing magic functions; reflection positivity; mean values of long Dirichlet polynomials and shifted
convolutions.

### 10.4 Foundational principles (each a theorem in the corpus)
P1 Finite apertures are blind to width; statements must be uniform in `c` [L]. P2 Inputs are parity-breaking,
precision-faithful, of unbounded aperture, with stabilizer in the square-root class [L]. P3 Positivity-preserving
certificates (Markov, Perron, Lee–Yang, GKS, counts, finite rank, finite templates) end at explicit thresholds
(`log ρ`, `½log 2`, `c* ∈ (½log 5, ½log 6]`, spread `6`) [L*/L]. P4 The certificate format is exact in both parity
sectors, with gauge freedom only in the pole direction [L*]. P5 Sign, precision and reflection are one quantity `w`
[L]. P6 Content begins at the quasi-RH threshold on every ladder, with the exchange rates `w ≤ σ` and
`w ≤ 1/(2θ)` [L*/P].

### 10.5 Criteria the field must meet
Reproduce the thresholds `21/40`, `log ρ`, `½log 2`, `c*`, `181/250`, `a_1`, `1/8`, `6600/9991`, `17/33`, `4/7`; be
false for the fakes (off-line lattices, Davenport–Heilbronn, the Liouville twin, `Λ + εn^{−η}`, `ζ(s)ζ(s−ε)`, Beurling
systems with regular integers and off-line zeros); contain the function-field calibration as the degenerate case
("curves fail at their number of angles", the Cayley ladder is the sharp Weil bound over `𝔽_q`) [L*]; and produce,
before any sign for ζ, exact finite-level theorems whose certificates have transferable shape.

### 10.6 Research topics
T1 The arithmetic Hamiltonian: construct `H(t)` of the Weil canonical system from the prime side (the Levinson
recursion is the lattice version [L]) and formulate regularity as a property of the kick law (`B2`, `B51`, A41).
T2 Exact sum-of-squares structure on prime lattices (`B9`) and signed supersolutions at the first stages (`B3`, `B4`,
`B5`, `B56`), read for a general law (8.3).
T3 LP-dual extremizers for the prime-blind cones: the arithmetic analogue of magic functions for the lag semigroup
`{log n}` against the Gamma weight (5, first reading).
T4 Effective uniqueness and the margin law of the window cone (`B58`, `B59`): the rate at which finite levels pin `Λ`.
T5 The long-mollifier structure theorem (9) and the Π ladder (8.1).
T6 The zero–one law for the index (`B13`) and self-repulsion of complex zeros (Deuring–Heilbronn for ζ).
T7 Calibration: which property of `{log n}` together with `Γ_ζ` is used—Beurling systems and the Selberg class as the
space in which ζ is a rigid point.

### 10.7 What the field would not be
Not a statistical theory (random matrices, value distribution, almost-all results): excluded by P2. Not a count or
Hodge-index theory over ℤ: closed by the coincidence of count and form (3.6). Not a positivity-preserving theory:
excluded by P3. It would be closest, in spirit, to the exact extremal-function theory that resolved sphere packing and
to Weil's own proof, where every quantity is an exact integer and positivity is a theorem about a lattice.

## Appendix A — Lean anchors read in this review

GrowingWindowsOfSpecZ: `riemannHypothesis_iff_two_site_posDef`, `riemannHypothesis_iff_abs_weilOrbitCorr_lt`,
`riemannHypothesis_iff_levinsonErr_pos`, `posDef_succ_iff_abs_schur_lt`, `toeplitzPosDef_of_short`,
`exists_degenerate_lattice_of_not_riemannHypothesis`, `schurParam_eq`, `log_le_sum_of_recurrence`.
RHTower: `weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt`, `eq_vonMangoldt_of_weilPositiveFull`,
`riemannHypothesis_iff_primeBlindPositiveAt_one`, `newmanConstant_nonneg` (restricted to the nonnegative heat axis by
definition), `newmanConstant_lt_eighth`, `exists_multiple_zero_of_newmanConstant_pos`,
`two_mul_re_logDeriv_riemannZeta_criticalLine`, `deriv_riemannZeta_ne_zero_of_re_zeros`, `exists_bdRiesz_norm_lt_of_rh`,
`riemannHypothesis_iff_eventually_bounded_of_generic` (AOG), `zeta_orbitCorr_rate_iff_zetaZeroWidth_le` (AOG),
`eventually_montgomeryForm_lower_uniform`, `integrable_and_integral_norm_sq_zeta_criticalLine`,
`zetaDiscStronglyRecurrentOn_iff_headTargetUniformlyDense`.
ArithmeticOfSquareRootPrecision: `deciding_input_necessary_properties`, `not_of_finite_window`,
`not_count_and_count_add_smul_powerWeight`, `countAtPrecision_half_iff`.
SquareRootThreshold: `exists_configWidth_eq_and_weil_nonneg_on_aperture`, `offLineLattice_re_W_nonneg`,
`zetaZeroWidth_eq_zero_iff_newmanConstant_eq_zero`, `zetaZeroWidth_le_windowCeilingExcessExponent`,
`zetaContactAperture_eq_sSup_windowPositiveApertures`.
RenormalizedIntersectionTheory: `riemannHypothesis_iff_isPosDefKernel_zetaKernel_pow`,
`riemannHypothesis_iff_negIndex_kunnethZeta_eq_zero`, `riemannHypothesis_or_negIndex_kunnethZeta_eq_top`,
`mayerDefect_nonneg_representation_iff`, `resonantLewisPeriod_coIsometryDefect_lt_zero_iff`,
`retainedHeckeChannel_defect_sign`, `retainedHeckeChannel_defect_reflect`, `isMayerResonance_quarter_of_Xi_eq_zero`,
`mayerPeriodCore_finite_whole_haar_iff_resonance`.
ZeroConfigurationGeometry: `hankel_ratio_eq`, `pair_type_of_hankel`, `pair_centre_and_gap_rvm_explicit`,
`exists_isolating_window_pair_of_bump`.
FiniteFreeProbability: `riemannHypothesis_iff_frequently_stable_mollified`, `eventually_not_splits_heatOp_jensenPoly_XiC`,
`splits_jensenPoly_symEuler`, `eventually_le_card_roots_jensenReverse_XiC`, `im_neg_of_one_le`, `turan_of_splits_jensenRev`.
CanonicalSystemOfTheWindowTower: `riemannHypothesis_or_kernel_unbounded_at_contact`, `kernel_christoffelDarboux`,
`hermiteBiehler_norm_difference`.
ConjugateDiagonalGeometry: `criticalClustering_logMean_mollifier_hecke_tfae`,
`criticalClustering_of_tendsto_xiCriticalRatio_one`, `dyadicMean_corridor_and_polynomialTheta_littleO_log_tfae`.
ArithmeticCastelnuovoSeveri: `scalingSurface_hodgeIndex_iff`, `posIndex_intersectionGram_le`.
HodgeTheoryWithoutVarieties: `strictHodgeRiemann_iff`, `hodgeRiemann_transport_on`, `hardLefschetz_of_riemannHypothesis`.
ArithmeticOrientationTheory: `frustrationIndex_switch`, `isBalanced_iff_frustrationIndex_eq_zero`,
`groundEnergy_le_frustrationMass`. ArithmeticCorrelationGeometry: `ae_moebius_chowla`.
ArithmeticProduction: `mollifierDefect_eq`, `mollifierDefect_ge_band`. ArithmeticPositiveDuality:
`beurling_primes_of_critical_line_defect`, `eq_smul_diracComb`. SpacingScaleHarmonicAnalysis:
`zeta_splineAtomic_negIndex_law`. ArithmeticHarmonicAnalysis: `exists_norm_riemannZeta_half_le_subWeyl`.
FrustratedArithmeticDirichletForms: `hardyInterval`, `ArithmeticPartIsOptimalHardyTerm`,
`coupling_eq_weilOrbitCorr_of_even`. CriticalHardyTheoryOfTheWindowCone: `exists_forall_abs_sub_vonMangoldt_lt`.
DilutionCrystallizationPincer: `dci_pincer_master_theorem`, `crystal_gap_prime_torus_incompatibility`.
