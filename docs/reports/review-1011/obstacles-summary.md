# Obstacles summary — status quo

Companion to [route-obstacles.md](route-obstacles.md) (per route), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ) and [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem). Corpus checkpoint: commit `9a43b8670d` with its working tree (2026-11-10). Working log: `logs/review-1011-frontier-facts.md`.

**Evidence.** `[L*]` Lean statement read for this report (source, or the statement returned by the corpus search tool); `[L]` recorded as integrated Lean in the frontier map, the scoped-obstruction ledger, a programme table of `formal/` or a formalized pipeline card returned by the search tool, not re-read; `[S]` Lean source present, graded unfinished or unintegrated by the frontier map or untracked in the working tree, statement read; `[K]` Lean with transitive axiom audit as recorded; `[D]` deduction made here from `[L*]`/`[S]` statements; `[C]` classical, not in the corpus; `[A]` assessment. Sections 2.3–2.14 and 3 are interpretation and ideation: every untagged statement there is a proposal, not a result.

**38 live formulations; 12 candidates** (SEC, CDC/BSH, S3, APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF). HJ is PA; PCS is a retired label.

**Notation.** `Θ=sup Re ρ`; `Θ∞=inf{σ≥½: finitely many zeros have Re ρ>σ}`; **ZAL** `Θ∞=½`; **AAL** `Θ=Θ∞`; **B13** finitely many off-line zeros ⇒ none; **Landing** ZAL ⇒ finitely many off-line zeros; **DH** ¬AAL ⇒ ZAL; **B56** `Θ<1⇒Θ=½`. `c_B` the orbit correlation of the cubic spline, `c_p=c_B(log p)`, `c_B(log d)=A(d)−P(d)` with `P(d)` the smoothed von Mangoldt count in the window of `d` and `A(d)` its archimedean-plus-pole prediction. A **logarithmic window** at `T` is `{p: |log p−T|≤32 log(T+2)}`. **World I** ¬AAL; **world I-a** its part with a remainder on the line (finitely many off-line zeros); **world I-b** its part with an off-line tail; **world II** AAL ∧ ¬ZAL. **`𝒵(γ_min,C)`**: tempered reflection-symmetric zero configurations without real zeros, lowest ordinate `≥γ_min`, `N(t,t+1)≤C log(|t|+3)`. The **depth** of a zero is `|Re ρ−½|`. `𝒢=W(ℤ)` the arithmetic square, `Γ_n` its graphs. **Comb pairing** of a real divisor `D=Σc_nγ_n` on a finite set of degree points: `Γ_m·Γ_n=½(1/|m−n|+1/(m+n))+Λ(n/m)` off the diagonal (jets plus contacts), `Γ_n·Γ_n=−log(n/2π)`; degrees `d₁=Σc_n/n`, `d₂=Σc_n`; **comb form** `2d₁d₂−D·D`. A **window of ratio `Q`** is `(N,QN]`; its **aperture** is `a=½log Q`. **`𝒜(a)`**: the set of real weight systems `w` for which Weil's form with contact weights `w` is nonnegative at aperture `a`. A statement is **selective** if it fails for some system that shares all of ζ's structures but one. The **twisted part** of the square of a quadratic ring of conductor `q`: jets, counterterm `log(qn/2π)`, contacts `Λχ`, no pole plane. `E_r` the arithmetic-clock Green energy. A **heavy return**: a `δ`-return, `δ≤1/20`, of a subset of the primes `≤y` omitting at most `1/1000` of the `p^{−1/2}`-mass.

## 1. Big picture

### 1.1 One inequality per prime; its resolution is logarithmic
RH ⇔ `∃K`: `2c_p≥−K` at every prime ⇔ `P(p)≤A(p)+K` ⇔ Weil positivity of the two-bump `B+τ_{log p}B` at every prime [L*] ⇔ a floor on the scale limits of the comb form on two-bump packets at `log p` [L*] ⇔ every effective prime class carries an `ℕ`-count with Tate limit `δ_p(1,1)` [L].

| Sample | A one-sided bound gives | Evidence |
|---|---|---|
| all primes; any power-saving gap set | RH | [L*]/[L] |
| primes of arbitrarily late `r√T` windows; two-prime difference lags in such windows | RH; every tempered configuration without real zeros is decided | [L*] |
| primes of arbitrarily late logarithmic windows | RH; width `≤α` from the floor `−Kp^α`; a power saving `α<½` ⇔ quasi-RH; absolute form equivalent | [L*] |
| the same windows, outside at most `Ce^{δT}` primes per window, `δ<1`, chosen freely per window | RH; width form; the same statement as a floor on two-bump comb packets | [L*] |
| windows `T≤log p≤T+80/δ+1`, if the deep ordinates are `δ`-separated | width bound, from below or from above; only the deep ordinates need the separation | [L*] (conditional on the separation) |
| windows of unbounded radius (any Bohr-dense set) | an attained top lies on the line: world I is excluded | [L*]/[L] |
| windows of radius `R(T)→∞`, `R=o(log T)`, in the class `𝒵(γ_min,C)` | nothing: one configuration with unattained top `½+Θ` passes every floor, also at the prime logarithms; `R` is built with the configuration | [L*] |
| windows of any fixed length, in the class `𝒵(γ_min,C)` | nothing | [L*] |
| primes off a density-zero set; very smooth degrees; finitely many Frobenii | nothing without attainment; with ZAL, RH | [L*]/[L] |

If RH fails, every sufficiently late logarithmic window holds a violator of every floor outside every set of `Ce^{δT}` primes [L*]. Unconditionally the error has the Vinogradov–Korobov saving [L].

**The counter-configuration [L*]/[D].** Its level `k` consists of the ordinates `d/(4(k+1))`, `4(k+1)Γ_k≤d≤8(k+1)Γ_k`, each split into two simple zeros at distance `O(1/T_k)`, all at one depth `x_k`: at least `8(k+1)Γ_k` zeros of one depth with ordinate in `[Γ_k,2Γ_k+1]`. A near-coincident pair with equal weights contributes `2cos(εu/2)` times one mode at the scale `u`: the pairs synthesize the signed amplitudes of a trigonometric polynomial that is positive on the window [D]. For ζ the zeros of depth `≥d₀` below height `V` number `o(V)` and at most `T^{(30/13)(1−σ)+ε}` lie right of `σ∈[½,5/6]` [L*].

### 1.2 Two worlds, three atoms
`Θ<1 ⇔ Θ∞<1`; ¬AAL ⇒ `Θ<1`; failure of quasi-RH forces `Θ=Θ∞=1` and AAL [L*].

| World | Description | Proved inside it |
|---|---|---|
| I: ¬AAL | a finite isolated top layer at `β<1` over a remainder `≤Θ∞<β`; I-a: the remainder on the line; I-b: an off-line tail | zero-free strip; `M(x)=O(x^{β′})`, `β′<1`; heavy returns later than `exp(c·y^{1−β″})`, `β″<Θ`; a complete finite-layer receiver; a floor on windows of any unbounded radius fails [L*] |
| II: AAL ∧ ¬ZAL | `Θ=Θ∞>½`: the top is approached by infinitely many zeros | the receivers; at the level of `𝒵` it passes every floor below the logarithmic radius [L*] |

RH ⇔ ZAL ∧ B13 ∧ Landing; AAL ⇔ B13 ∧ Landing ∧ DH; a failure of the abscissa law fails exactly one of B13, Landing, DH [L*]. B13 is the emptiness of world I-a, DH the emptiness of world I-b [D]. Landing is a tail law, undecided below every height; an FE model with approaching quartets and a positive integer-norm Euler product with approaching remainders both violate it [L*]/[L]. Classical Deuring–Heilbronn holds for a real zero of a primitive quadratic `L(s,χ)` with a uniform constant; graded repulsion is refuted on integer-norm Euler products [L*].

To prove AAL one may assume quasi-RH: AAL ⇔ (`Θ<1` ⇒ AAL) [D]. B56 implies AAL [D]. World I-a is the world of a bounded index: finitely many non-real zeros ⇔ the nonreal zero count of the heat flow is bounded as `t↓0` [L*]; the `n`-th critical length of the window index is infinite ⇔ at most `n` distinct right zeros [L].

### 1.3 The finite-layer receiver is complete; the gap is the exclusion
In world I, for every top zero `ρ` at `β` and every observation line `σ<β` [L*]:
- prime-only damping filters read the divisor at every damping speed; with polynomial contraction the complete prime filter has growth, a positive finite critical modulus and decay according to the exponent;
- the top has two distinct positive ordinates, or the corrected current diverges at every damping `a` with `a(β−σ)>π/2`;
- for every moment order `r≥1` the Gaussian prime moment minus its pole is the centred Vaughan current up to `O_r((1+1/η)/t)` on admissible cutoffs; truncating cofactors changes the current by exactly the complementary convolution, both continuum terms kept;
- at `σ=½`, `X=e^{at}`, moment order `⌊κt/log t⌋`: the actual unfiltered prime-minus-pole current equals the centred type-II current on cofactors `≤⌈2t^{J+3}⌉` up to `O(e^{−at/4})`, uniformly in the admissible Gaussian sector [K];
- complete unweighted lattice pairs of cofactors `m≥2k` are `≤2/t^b` for every fixed `b`, eventually, uniformly up to polynomial cutoffs in the rotating sector [S]; the lattice pair equals its Gaussian main term up to the relative error `(2048r³Re(ε)t²W²)^r` [S];
- the even-mask prime cross form under Gaussian localization is eventually positive, uniformly in the moment order: a prime-invariant mask does not keep a nonpositive cross term [K];
- for `½≤σ≤5/6` and `c>(30/13)(1−σ)`, `T^c` one-separated returns to every small disc at a zero right of `σ` exclude it.

Open [L]: the near-diagonal cofactor pairs, the prime-weighted sum with both continuum corrections, the transfer through the growing-order filter. An arithmetic upper bound for the signed centred type-II current at a growing isolated mode beats the trivial bound of a prime sum of length `e^{at/2}` at height `t` by the power `1−β`: it is the exclusion of the layer (B145) [D].

### 1.4 Rigidity: ζ has no moduli, and a family sees only its variable part
- A Dirichlet series with ζ's FE is a multiple of ζ; a countable Beurling system with an `L¹` or `L²` FE defect is the rational primes; count distance `o(log n)` forces the rational primes [L].
- A gauge fibre with a nonzero analytic residue at `1` is `ζ·exp(H)` left of `1` [L]. Normalized analytic unit phases keep every multiplicity of ζ on `Re s>max(½,1−mt)` and have a moving branch; no finite real affine mixture has entire scaling; the `χ₄`-selected pair has a zero of order four at `1−2t` and a double pole at `1−4t`, scaling limit `ζ(2)(w+2)⁴/(w+4)²` [L*]. Every finite residue-class mixture has the scaling profile of its principal average, and no joint holomorphic endpoint germ matches its Euler product even on nearby real arguments [S].
- Fixed part: for every finite measure on the gauge torus and every continuous amplifier the moment is at least the atom at the trivial fibre times the trivial bound; the trivial fibre has mass zero or tending to zero in the five canonical family classes; with the trace of ζ retained, sublinear tensor growth of a cover family ⇔ RH [L*]. The module does not classify every arithmetic family.
- The Eisenstein line law holds over every symmetric fixed part in the closed strip [L*].
- Haar-almost every fibre over the prime torus extends zero-free to `Re s>½`; ζ is the fibre over one point [L*].

### 1.5 The zeros of ξ have no arithmetic constituent among Dirichlet polynomials
- A bounded holomorphic function on `Re s>x` given by an absolutely convergent Dirichlet series, whose zeros there are zeros of ξ, has all of them on the line: Bohr recurrence of a zero against the density-zero law of the deep zeros [L*].
- Every Dirichlet polynomial with at least two terms has a zero that is not a zero of ξ; no hypothesis on the support [L*]. Mechanism: if `−Gζ/s` is holomorphic in the strip and bounded near the line, with absolutely convergent expansions in scales `≤1` right of the line and `≥1` left of it, the constant terms agree, by the jump of the fractional part; for `G=D′/D` this forces the lowest and the highest frequency to coincide [L*].
- A zero-free exponential polynomial is bounded below on closed half-planes; its inverse expands over the monoid of frequencies up to the zero-free abscissa [L*].
- Not covered [L]: bounded Dirichlet series with zeros on the line, partial common zeros, limits of approximants.

### 1.6 Exactness over ℤ has an exact price
`x↦xⁿ` is additive in characteristic `q` exactly when `n` is a power of `q`; `Λ(n)` is the `log q`-weighted number of primes at which `F_n` is a Frobenius [L*]. Order `m` of the Fermat-quotient derivations at every prime of `S` costs `log|a|≥m·Σ_{p∈S}log p`; `ℤ` has no ring endomorphism but the identity [L*]. The minimal fixed-point auxiliary has log length `ψ(N)`, and RH ⇔ `ψ(N)≤N+C√N log²N` [L*]. On the tower of lines Riemann–Roch has the gluing index `K!` and Bézout gives `n≤|x_n|`: the product formula [L*]. A section of the square that vanishes on the graphs of the proper divisors of `m` and not on `Γ_m` pays all those contacts; upward it pays one contact per distinct prime: `p−e_p` vanishes on every `Γ_{p^j}` and has the value `p` on `Γ_1` [L*]. The carry is a cocycle that is not a coboundary; the carry defect and the window-count defect are complementary up to `½log(πN)+o(1)` [L*]. At one prime Stepanov's method runs on the first Witt carry: `|Σ_{n≤p}e(an^p/p²)|≤5p^{11/12}` [L*].

### 1.7 The comb: one matrix on the integers, a Hodge index equivalent to RH, no slack
- **Pairing and zeros.** On packets the pairing of the degree points tends to `2d₁d₂−Z(f)`; RH ⇔ exactly one positive square on the two rulings and every finite family of packets; the defect has at most `#{ρ: Re ρ>½}` negative squares [L*].
- **The sign is carried by the contacts.** Comb Bézout with weights `w` ⇔ RH ∧ `w=Λ`; unit masses on the integers force `w=Λ`; with a doubled weight at `2` the flat tail violates the inequality at every large scale [L*].
- **No slack in the counterterm.** With the counterterm `log(n/2π)−c` the inequality holds for all packets ⇔ `c≤0` ∧ RH; for every `c>0` a packet with both degrees zero has `Z(g)<c∫g²` [S].
- **Finite scale.** On `S⊆(N,N+M]`, `18M≤N`, every real divisor has comb form `≥(1/50)Σc_n²`. For every ratio `Q` there is `R` such that for `N≥R` the comb form is nonnegative on the real divisors of `(N,QN]` whose sums over blocks of `⌊N/R⌋` points vanish; the blocks are fewer than `2QR` [L*]. If for every ratio and every `η>0` the comb form is `≥−ηΣc_n²` on every real divisor of the window at arbitrarily large scales, RH holds; if RH fails, some ratio has, at every large scale, a real divisor with `Σc_n²≤C` and comb form `≤−ε` [L*].
- **Selectivity.** A window of ratio `≤2` contains no pair in divisibility: the form is the same for every system of contact weights, and the short-window floor holds for all of them. On the single point `{2}` the form is `c²(1−log π)<0`: nonnegativity on every finite set is false [L*].
- **Jets by weights.** `½(1/|m−n|+1/(m+n))=Σ_{j≥0}min^{2j}/max^{2j+1}`; each weight, with the diagonal `1/n`, is positive semidefinite (a Hardy square); the truncations to the first `J` weights increase to the comb form, with remainder `≤(1−1/N)^{2J}` times half the Dirichlet form of the jets [L*]. The weights are the even multipoles `r_<^ℓ/r_>^{ℓ+1}`, `ℓ=2j`, of the Newtonian kernel `1/|x−y|` in `ℝ³` between a point at distance `m` on an axis and the pair `±n`; the weight-zero kernel `1/max` at the points `0` and `∞` gives the pairings `1/n` and `1` with the two rulings [D]. The contact form of one prime is `log p` times the sum over the chains `{mp^k}` of the square of the chain sum minus its diagonal [D].
- **Potential.** In the gauge of the flat tail the potential at `n` is `N/n−ψ(N/n)` plus an explicit smooth term; the form of the flat tail per degree point tends to `2+γ−log 4π`, twice the first Li coefficient [L*]/[D].
- **Curves.** On the comb `q^ℤ` of a curve the comb form is the Toeplitz form of the normalized Frobenius eigenvalues; nonnegativity on every finite set ⇔ purity; on one graph it is `2g·e_k²`; no jets, no counterterm; the golden datum violates it [S]. Purity of a curve datum is decided on the window of `#spectrum` degree points [L*].
- **Quadratic rings.** For a real primitive character of conductor `q>1` the ideals counted by their norms sit on the comb of the integers with contacts `Λ(n)(1+χ(n))`; the pairing tends to `2d₁d₂−Z_ζ−Z_χ`; the twisted part has no pole plane and the counterterm `log(qn/2π)`; the class group does not enter; with the conductor `qe^{−c}`, `c>0`, some packet of degree zero has a positive pairing [S].
- **Index and splittings.** If the right zeros are zeros of `P_WE−cP_{W♯}E′` with `|E′|≤|E|` right of the line and `W` of `κ` points, Weil's form has at most `κ` negative squares; the cleared Eisenstein constant term gives at most one for `Y≥1` and none for `1≤Y≤4πe^{−γ}` [L*].
- **Counting.** The gluing index of the first `N` graphs is `N!`; `G(T)−N(T)+S(T)→½log 2π−7/8`; the contacts at a height are the smoothed increments of `S`, up to the off-line correction [L*].

### 1.8 The adelic carrier and three regulators
Every adelic-invariant kernel with a torus-orbit functional has a constant degree diagonal; no scalar counterterm removes the jump `−2‖g‖²log p` between `p` and `p³` [L*]. The weighted mixed hyperbolic Green kernel converges over the rational torus, has a leafwise Robin finite part, and its spherical average at parameter `½` is the minimal Green kernel of the all-prime weighted adjacency [L*]; none of these identifies Weil's degree diagonal [L].

| Regulator | Finite cutoff | Limit | Evidence |
|---|---|---|---|
| Cusp cutoff at height `Y≥1` | index at most one; all zeros on the line for `Y≤4πe^{−γ}` | `(s−1)ξ(2s)` after normalization | [L*] |
| Green damping of the arithmetic clock, `r↑1` | `0≤W−E_r≤(1−r²)‖f′‖²/2`; finite exactly on the closed Weil form domain | Weil's form, from below | [L*] |
| Scattering tower of height `N` | jump density `(1−e^{−Nt})·archLevyDensity`, contacts weighted `1−n^{−N}`; a continuous `L²` extension; the mass-corrected second-height defect tends to `½∫|u′|²` on smooth interior packets | the closed Weil form on its domain, `+∞` outside | [K]/[L] |

The tower of height `N` is the explicit formula of the quotient `Λ(s)/Λ(s+N)` of completed zeta functions: contact weights `Λ(n)(1−n^{−N})`, Gamma symbol the difference of the logarithmic derivatives at `s+N` and `s` [D]. Both convergent regulators approach Weil's form from below by a positive jump tail; in each, RH reads: the regulated energy is at least minus its own defect [D].

### 1.9 Aperture and height
`RHVerifiedThrough(windowHeight a)` gives the sign on `[−a,a]`; RH is verified through 67 [L*]. Positivity at aperture `a` forces, for every zero of depth `δ` at `|γ|≥103`: `δa<12((4n_δ+2)log(10⁶/δ)+log(A₀log(|γ|+3))+18)`, `n_δ` the number of zeros of depth `≥δ/8` within `±100` [L*]: an isolated deep zero is resolved at aperture of order `(log log γ)/δ`, a zero with `n_δ` deep neighbours at aperture of order `n_δ/δ`. Positivity at aperture `λ·½log(T/2π)`, `λ>1`, bounds the depth at height `T` by `exp(−c log³(T/2π))` [L*]. For `T≥e³⁶⁰` a configuration with ζ's local counts and finitely many off-line zeros has a zero of depth `δ` at `T` and is window-positive at aperture `(log T)/36` [L]. A window blind to a set of lower density `D` has aperture `≥πD`; a cancelling cluster at aperture `a` has upper uniform density `≥2a/π` at any depth; finite clusters never cancel [L*]/[L]. The inequality of the display binds only for `δa>564` [D]; the proved apertures are below `½`.

At the critical curve `R_c=R_polar=R_halfline≤W₀`; exactly one of: RH; ¬RH and `R_polar<W₀`; ¬RH and `R_polar=W₀` finite with every critical half-line ground state orthogonal to the polar source [L*]. The third case is undecided (B104).

### 1.10 Index, limits, flow and separation
A Hermite–Biehler defect of degree `κ` has at most `κ` exceptional points; the bound passes to locally uniform limits; RH ⇔ ξ is a limit of conjugation-real entire functions with at most one right-half zero each [L*]. On the flow a locally finite summable module is determined by its trace, and Castelnuovo–Severi on every divisor of Frobenius graphs ⇔ pure and effective ⇔ positive definite central trace; for the zero motive ⇔ RH [L*]. RH ⇔ the ordinate is injective on the zeros [L*]. No vertical progression consists of zeros; each half progression contains non-zeros at arbitrarily large index [L*]. Approximants that are Lee–Yang or half-plane stable polynomials in the prime fields have linear zero counts and do not converge to a zero-free factor times `Ξ` [L]. `H_{−τ}` has infinitely many non-real zeros for every `τ>0` [L].

### 1.11 The horizon has complete and sharp receivers
RH ⇔ every compact pulse rings down at `e^{−(¼−ε)τ}` ⇔ every tent reflection Krein form has negative index `0` ⇔ one cavity energy of Hecke forms decays at `y^{¾−ε}` [L*]. For one Hecke eigenform: RH ⇔ sharp rate ∧ no nonhalving Shimura zero [L*]. RH ⇔ an `ℕ`-valued count with Tate limit the integer probes exists [L*].

### 1.12 The dark range and the returns of the prime orbit
Heavy returns do not occur while `log t≤(log y)^{3/2−ε}` [L*]; a strip of depth `h` gives `log t≥c·y^{½−h}`; two-prime returns obey Baker's depth law [L]. RH ⇔ ζ is strongly recurrent in the strip [L*]; the graded count excludes a zero only if power-many separated returns of ζ to its own target are produced [L]. The transfer of candidate S3 implies B56, hence AAL [D].

### 1.13 Law and point
Past the Vinogradov–Korobov region every unconditional theorem of the corpus about the location of the zeros is in law: density exponent `30/13`, deep zeros `o(V)`, off-line second moment `o(V)`, Matomäki–Radziwiłł for μ, critical-line density `0.67250071`, typical-height signs [L*]/[L]. Two pointwise theorems use the density law or the additive structure of the integers, and both concern constituents of ξ, not ξ (§1.5).

### 1.14 The Mertens level in several geometries
Producer rates, Farey discrepancy, the nerve, the prime-vertex indices, the gluing quotient and the centred count of the orientation cover over ℤ read `M(N)`; cover weight `½` ⇔ RH; RH ⇔ either one-sided quarter-power law of the weighted squarefree count [L*]/[L].

### 1.15 Receivers are complete; every known producer has a price
For each mechanism by which a Riemann hypothesis or a statement of its type is proved elsewhere, the corpus holds a Lean statement that fixes what the mechanism gives over ℤ.

| Mechanism | What the corpus proves about it | Evidence |
|---|---|---|
| Surface, sections, Riemann–Roch (Weil) | the square is a curve; no object of finite type; sections pay one contact per prime above; Riemann–Roch with Bézout on the tower is the product formula | [L*] |
| A bounded-below naive height and Tate's limit | a quadratic form within bounded distance of a function bounded below is nonnegative; RH ⇔ such a height exists on every window | [L*] |
| A family with monodromy (Deligne) | fixed-part laws in the five canonical classes; ζ is rigid | [L*]/[L] |
| A Frobenius with zero derivative (Stepanov) | cost `m·θ(S)`; reaches Chebyshev; one prime: `p^{11/12}` | [L*] |
| Ferromagnetic stability (Lee–Yang) | zeros of stable prime polynomials lie on the line and are not zeros of ζ; linear zero counts | [L*]/[L] |
| A dominant half (Hermite–Biehler; Lagarias–Suzuki) | index law and semicontinuity; index one pencils converge to `(s−1)ξ(2s)`; the natural theta half has infinitely many right zeros; index of the pairing ≤ defect of a splitting | [L*]/[L] |
| Newton polygons (Sheats) | digit combinatorics in Lean without the optimality of the greedy composition; separation by absolute value is excluded for ζ; the carry is a nonzero class | [S]/[L] |
| Heat flow | nonreal count antitone; infinitely many non-real zeros at every negative time | [L] |
| Jensen polynomials | the finite-stratum law gives RH; `N_d≤300√(d log d)` | [L] |
| Recurrence (Bagchi) | RH ⇔ strong recurrence; power-many separated returns exclude a zero | [L*] |
| Existence of weights (duality) | prime-blind positivity at level `A+1` ⇒ some weight system is Weil-positive to level `A`; RH ⇔ the archimedean symbol plus the positive pole mass is nonnegative on blind combinations | [L*] |
| Positive ground states (Perron–Frobenius, Barta) | a nonnegative jump kernel does not increase under `v↦|v|`; the window form contains the pole moments `+2cosh²−2sinh²`, which increase [D]; nonnegative eigenvectors with small edge mass have bounded eigenvalue | [L*]/[L] |
| Power sums (Turán) | among `n` consecutive powers one power sum is bounded below, without separation | [L*] |
| Transfer operators (Mayer, Lewis) | three-term equation; the Eisenstein period is a Hecke eigenfunction | [L*] |
| Approximation by dilates (Nyman–Beurling), Speiser, Farey, Li | receivers in Lean | [L*]/[L] |

Consequences [D]: every route of the corpus is a receiver; no statement of the corpus produces the sign, the count or the bound at a contact beyond a verified height and the classical zero-free region. The mechanisms for which the corpus search returns no statement are listed with a verdict in §2.9.

### 1.16 Where a statement has slack
| Form of RH | Slack | Evidence |
|---|---|---|
| the sign over all test functions of a window | none: best margin `≤K exp(11c/2−πe^{2(c−2)})`; no change of one contact weight; no change of the constant `2π` | [L*]/[S] |
| a floor at the primes for one fixed bump | any floor `−Kp^α` with `α` arbitrarily small on logarithmic windows gives width `α`: `P(p)≤A(p)+p^{o(1)}` suffices | [L*] |
| the index | one unit: at most one complex zero per approximant suffices | [L*] |
| returns | a power: `T^c` returns, `c>(30/13)(1−σ)` | [L*] |
| the heat flow | none at time zero | [L] |

An estimate can meet a statement only where it has slack: on the prime side, for one fixed test [D].

### 1.17 What is ruled out
| Mechanism | Verdict | Evidence |
|---|---|---|
| A family (gauge twists, characters, vertical shifts, Hecke forms, covers, analytic prime smoothings, finite residue-class mixtures) as a source of purity for ζ | fixed-part laws; isozeric deformations; moving or delayed singularity; no joint endpoint germ | [L*]/[S] |
| A receiver below the logarithmic radius at the level of `𝒵` | block tower with unattained top | [L*] |
| A Dirichlet polynomial, or a bounded Dirichlet series with an off-line zero, as an exact constituent of ξ | no polynomial is a factor; bounded factors are pure | [L*] |
| One glued adelic-invariant carrier object with Weil's diagonal | constant diagonal; discriminant jump | [L*]/[L] |
| A finite-type object with Frobenius lifts carrying the contacts | fibres infinite; forced wrong contacts | [L*] |
| Sections of the square as certificates of the contacts | one upward contact per prime; no prime powers above; no jets | [L*] |
| Positivity on short windows as information on the primes | the form on a window of ratio `≤2` is independent of the contact weights | [L*] |
| Nonnegativity of the comb form on every finite set | negative on `{2}` | [L*] |
| A Frobenius for a window; cheap simultaneous vanishing; Riemann–Roch with Bézout on the tower as a producer | one prime per power map; cost `m·θ(S)`; product formula | [L*] |
| The carry as a bound for the window count | complementary identity; nonzero cocycle class | [L*] |
| One counterterm across combs or scales; a constant other than `2π` | the counterterm is the density of the comb; Bézout fixes the constant | [L*]/[S] |
| Other contact weights with the same jets and counterterm | Bézout on the comb selects `Λ` | [L*] |
| A prime-invariant cofactor mask as a nonpositive cross term | positive after Gaussian localization | [K] |
| Stable polynomials in the prime fields as approximants of `Ξ` | linear zero counts | [L] |
| Positivity of a critical ground state as a route to its polar charge | the pole moments are not of jump type | [D] |
| The gluing count as a count of zeros at a height | misses by the unbounded remainder `S` | [L*] |
| Integral or trace-class Frobenius modules for the zeros; a class or half class of one Frobenius among the zeros | Tate twists only; divergent ladders | [L]/[L*] |
| Purity of a fixed part from the line law of its family | holds over impure fixed parts | [L*] |
| A fixed window length uniform over tempered configurations; density-zero exceptions without ZAL | low off-line pair; unattained tops | [L*] |
| Landing from the FE alone or the Euler product alone; graded repulsion from Euler products | models | [L*]/[L] |
| Euler-region or VK bounds for filters as exclusion of a finite layer | ranges separated by `a(1−β)/2` | [L*]/[L] |
| One Hecke eigenform as a complete receiver without side condition | halving pairs; Shimura zeros | [L*] |
| Markov, Perron, size-only payment, floor tower, universal holomorphic multipliers, fixed theta heads, positive Laplace mixtures | refuted or bounded | [L]/[L*] |
| Positivity, Euler products, integrality, linear counting, continuation, reflection, positive Hecke and two-prime polynomials as any atom | one-offs and annihilators | [L] |
| Schur, `C*`, KMS, internal modular conjugation, half-sided inclusions as zero locators | blind or excluded | [L] |
| Bounded-height Diophantine certificates against returns; return bounds as uniform routes to ZAL | Kronecker-scale cap; label statements | [L]/[L*] |

## 2.1 Tasks that are just work

Difficulty is established only where a known argument exists; `(unverified)` marks the rest. None of these decides RH.

### Assemblies of proved pieces
| # | Task | Routes | Basis |
|---|---|---|---|
| A72 | Count door on logarithmic windows with exceptional sets | ACS, HF, PM, SRT | `riemannHypothesis_iff_prime_logarithmic_windows_off_finset` |
| A73 | One-sided upper side (`2c_p≤K`) on logarithmic windows (unverified) | SRT, ACS | `exists_bddAbove_exp_windows_of_prime_windows` |
| A75 | Lean form of "the transfer of S3 implies `Θ<1⇒Θ=½`" | BAG, S3 | heavy returns in a strip; logarithmic-window criterion |
| A76 | Exceptional sets in the absolute and signed window criteria (unverified) | SRT, ACS, CDGeo | `prime_power_windows_transfer_off_finset` |
| A71 | Local tensor moments: uniform-in-`k` moments of `c_B` over the primes of late windows ⇔ RH [D] | ACS, AWT | window criteria with exceptional sets |
| A56 | Explicit rung: `RHVerifiedThrough T` ⇒ the two-bump sign for all `p≤P(T)` (unverified) | SRT, ACS | supports of the two-bump tests |
| A80 | Converse at finite scale: RH ⇒ for every ratio the comb form is nonnegative on every real divisor of `(N,QN]`, `N≥N₀(Q)`; with a verified height in place of RH for one ratio (unverified) | ACS, HF | the block decomposition; `tendsto_combForm_sample`; unbounded density of the zeros (`eq_zero_of_blind_of_unbounded_density`) |
| A79, A81 | Matching constants in the aperture–height exchange; `R(Q)` and the index bound `2QR(Q)` against the resolution law (unverified) | RW, ACS | `windowPositiveAt_of_rhVerifiedThrough`; `zeta_resolution_law_of_hodgeIndex`; `exists_blockSize_combForm_nonneg` |
| A82 | The Li ladder as comb forms of tails: the flat tail gives `2λ₁`; identify `λ_n` with the comb form of the `n`-th tail (unverified) | LI, ACS | `tendsto_combFormW_flatTail_div` |
| A83 | Density-matched counter-configuration: an on-line background of ζ's density changes the trace by a bounded amount [D] | SRT, ACS | summability of the spline weights |
| A90 | The flow criterion in prime form: RH ⇔ the lag function is positive definite on `ℝ` [D] | WL, ACS | `castelnuovoSeveri_iff_positiveDefinite`; `zeroMotive_castelnuovoSeveri_iff` |
| A92 | Resolution law on the prime side: a floor on windows of length `L` at the scale `u` against the number of deep neighbours; first statements: a sum of `n` modes with frequencies `≥Γ` and nonnegative real part on an interval of length `L` has `ΓL≤(2n+1)π` [D]; a floor forces `‖Re Q‖_{L¹(w)}≤K‖w‖₁+Σ|a_j||ŵ(γ_j)|` [D] | SRT, ACS, ZCG | `zeta_resolution_law_of_hodgeIndex`; `re_le_of_bddBelow_exp_windows_of_deepSeparated`; `pi_mul_le_aperture_of_blind` |
| A93 | Exchange atlas: for each receiver the parameter range implied by `RHVerifiedThrough(H)` and the height excluded by the receiver at a parameter value (unverified) | all rungs | A56, A79–A81; `finite_nonreal_zeros_iff_exists_nonrealZeroCount_le`; the Li and Jensen receivers |
| A94 | Index at finite scale: the negative index of the comb form on `(N,QN]` at large `N` equals the window index at aperture `½log Q` (unverified) | ACS, HF | `exists_blockSize_combForm_nonneg`; `exists_windows_le_weilNegIndex`; the card of critical lengths |
| A95 | A top layer of at most `k` quartets is seen on windows of a length depending on `k` alone, without separation of its ordinates (unverified) | SRT, ELT | `exists_norm_powerSum_ge`; `onLine_of_bddBelow_of_isBohrDenseAtTop` |
| A96 | The first selective window: the interval of weights `w(2)` for which the inequality holds on windows of ratio `<3` at every large scale (unverified) | ACS | `combFormW_eq_combForm_of_window`; the margins at width `181/250` and at the enlarged aperture |
| A97 | Lean form of [D]: the jets as even multipoles of the Newtonian kernel on an axis; the rulings as the points `0` and `∞` of the weight-zero kernel; the contact form of a prime as chain squares minus the diagonal | ACS | `hasSum_jetLevel`; `sum_mul_mul_jetLevel_nonneg` |
| A98 | Lean form of [D]: RH ⇔ `𝒜(a)≠∅` for every aperture (compactness of the feasible sets with the rigidity of `Λ`) | RW, ACS | `exists_weilPositiveUpTo_of_primeBlindPositive`; `aperturePositive_congr`; `combBezout_iff` |
| A99 | Lean form of [D]: the tower of height `N` as the explicit formula of `Λ(s)/Λ(s+N)`; RH ⇔ the regulated energy is at least minus its jump-tail defect | HAT | `rawEnergy_eq_cutoff`; `tendsto_scatteringSecondHeightSymbol` |
| A100 | The trivial aperture of a conductor: the twisted part of the square of a quadratic ring of conductor `q` is negative semidefinite on windows of aperture `a` with `4e^a+C≤log q` [D]; the exceptional square at aperture `log log q+O(1)` [D] (§3) | ACS, HF | `tendsto_twistedForm_add_twistedContact`; `grh_iff_primeWindow_nonneg` |

### Finite verification and explicit constants
| # | Task | Routes | Basis |
|---|---|---|---|
| A1 | Certified `RHVerifiedThrough T` past 67 | all rungs | `rhVerifiedThrough_sixtySeven` |
| A2, A3 | Numeric values of the explicit heights; two-weight membership on the first windows | window routes, TH, LA, HCF | explicit definitions |
| A4, A5 | Theta rank 15 and beyond; certificate of the center-tail failure (unverified) | TH | height 67 |
| A6, A7 | Cone widths; certificates on the anti-diagonals (unverified) | CHT, ACT | convex programs |
| A9, A13 | Explicit constants at the eighth-root horizon; near-gcd charges (unverified) | HF, AIP | proved limits |
| A47, A58 | Constants of the one-quartet world; effective gap iteration (unverified) | ELT, ACS | envelope and gap theorems |
| A48 | Hasse–Weil tests of smoothed Frobenius pairs at verified scales | ACS, HF | window rungs |
| A89 | A prescribed radius in the sub-logarithmic counterexample; the constant in `32 log(T+2)` (unverified) | SRT | the block tower |

### Classical inputs to formalize
| # | Task | Routes | Basis |
|---|---|---|---|
| A18, A21 | Twisted second moments past `21/50`; logarithmic two-point Chowla [C] | WD, MC | classical |
| A26 | Weyl asymptotic `N(Λ)∼Λ/12` [C] | PM, BHR | order `N(Λ)≍Λ` |
| A33 | Fourier coefficients of the cubic residue [C] | MC, MMD | nonzero residue |
| A41 | Count law for every curve over `𝔽_q`, first case plane quartics [C] | ACS, PM | crude-bound self-improvement |
| A59 | Short-interval primes in a residue class [C] | ACS, SRT | gap sets |
| A84 | Optimality of the greedy carry-free composition and the Newton polygon of the Carlitz–Goss zeta function [C] | sign-free calibration | `tokenPrefix_iff_inverseContent`; `IsOptimal.removeLast`; `exists_dominant_digitBlock` |
| A101 | Classical Deuring–Heilbronn in the form of the twisted comb: an exceptional square forces a margin on the other squares of the twisted part [C] | BAG, ACS | the uniform real-zero repulsion theorem; `tendsto_twistedForm_add_twistedContact` |

### Further items
| # | Task | Routes | Basis |
|---|---|---|---|
| A16 | Numerical `r,m,q` (unverified) | RW | Galerkin |
| A19 | Heat horizon: an explicit height for the exponent `(3/2+ε)/t` (unverified) | ZCG | zeros of `H_t` beyond `2π·exp(40/t)` are real [L] |
| A20 | Jensen rung toward the saddle scale (unverified) | LA | verified height gives real-rooted degrees |
| A24, A37 | Certified scans; resonators below the Kronecker scale (unverified) | TH, BAG | column calculus |
| A28, A30, A42, A46 | Reciprocal-quadric traces; best stencil exponent under RH; Gamma-weighted transport to the adaptive head; singular indices (unverified) | ACS, WL, TH, MC | stated bases |
| A54 | Cusp expansion for Bianchi resolvents | HAT | carrier theorems |
| A55, A68 | FE rigidity with an `L¹` or `L²` defect for Beurling prime measures; a landing calibration with ζ's Gamma factor (unverified) | BAG, ELT | exact-FE rigidity; approaching models |
| A86 | The transfer of the growing-order reduction through the top-mode filter; the near-diagonal cofactor pairs (unverified) | ZCG, BAG | `eventually_gaussianGrowingCofactorPair_rapid_decay`; filtered cofactor localization |
| A91 | The Hodge index on the square of a number ring of higher degree; the comb of a general Dedekind zeta function (unverified) | ACS | `tendsto_quadraticForm_add_idealContact`; `TheArithmeticSquareOfADedekindDomain` |

## 2.2 Open mathematical obstacles

### The common minimal face
| # | Problem | Strength | Routes |
|---|---|---|---|
| B130 | `P(p)≤A(p)+K` on a decisive sample: every prime, or the primes of arbitrarily late logarithmic windows off `Ce^{δT}` exceptions; any growth `Kp^σ`, `σ<½`, is a zero-free strip. Known: the VK saving | RH (≥qRH) | ACS, SRT, WL, HF, ZCG, HAT-C |
| B151 | The prime-side resolution law in ζ's class: the radius that decides configurations with ζ's local counts and with deep zeros of density zero. The aperture side has the law with the number of deep neighbours [L*]; the prime side has the logarithmic radius at the level of `𝒵` [L*]; first statements A92 | method | ACS, SRT, ZCG |
| B144 | Separation of the deep off-line ordinates of ζ; gives bounded windows by `[L*]` | sub | SRT, ACS |

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Weil's sign on every window; equivalently the regulated energies bounded below by minus their defect | RH | all sign routes, HAT-C |
| B152 | The comb form on a full window at finite scale: `≥−ηΣc_n²` at arbitrarily large scales for every ratio and `η` gives RH [L*]; the converse is A80 | RH | ACS, HF |
| B154 | **The exceptional square**: for the twisted part of the square of a quadratic ring, the sign on windows of aperture `log log q+C` for every `C` (§3). Known: aperture `log log q−log 4` [D] | Landau–Siegel | ACS, HF, BAG |
| B2, B4, B5 | Bounded oscillation of `Ψ` to contact; outer predictors and Schur bands; kick admission | RH | RW, GWZ, WTZ |
| B6, B8, B101 | Full-space sign at every critical multiple; head thresholds; polar payment at every ratio | RH | HF, SRT, AIP |
| B104 | **Polar orthogonality**: can a critical half-line ground state at finite `W₀` be orthogonal to the polar source (§2.4) | method | HF, SRT, AIP, ACS, SC |
| B123 | Correlated arithmetic pairings dominating the depleted kernel | method | HF |
| B9–B11 | No zero mode; top coprime stratum; exact SOS on a two-prime lattice | RH | HF, SC, ACS |
| B12, B14, B23 | Index ceiling uniform in resolution; any interior width value; `N_d` bounded | ≥qRH | CHMD, LA |
| B15 | Past Vinogradov–Korobov | sub | every route |
| B16, B17, B3 | Decay law of the margin; signed ground states past `log ρ`; variation of `r` free of `1/μ` | sub / method | CHT, RW |
| B18 | Prime-blind positivity on nonnegative blind mixtures; equivalently `𝒜(a)≠∅` at every aperture [D] | RH | RW |
| B19–B21, B102 | Torus law for `S*`; amplitude oscillation; all theta ranks; sign of the adaptive head near critical zeros | RH | TH |
| B22, B24, B25 | Outer roots of the Jensen polynomials; collisions at small time; frequency below one | RH | LA, ZCG |
| B27, B28, B47 | Runs of simple critical zeros; local positivity at fixed `λ` on density-one heights; multiplicity by a non-size input | sub | ZCG, RW |
| B29–B45 | The single open estimates of PTR, HCF, PA, XN, GTA, TT, CHMD, RN, SZ, TG, SC, ACS, HF, FU/CFC/RP, LI, ACT, AIP | RH | as named |
| B124 | Finite initial depth budgets of the heat divisor | ≥qRH to RH | ZCG, LA |
| B146 | An independent family of bounded index converging to ξ; a splitting of ξ whose defect is certified without the zeros | RH (producer) | W1C, PTR, IRP |

### Π — precision and production
| # | Problem | Strength | Routes |
|---|---|---|---|
| B48–B54 | Deciding input at square-root precision; endpoint energy; trivial-gauge half power; moving power windows; rows and BSY; regularized partial sums; extremal inequality | RH | WL, MC, SQF, JAS, CTF, PBM, RB |
| B55, B67 | Polynomial stencil rate; parity at power saving | ≥qRH to RH | WL, MC |
| B56 | `Θ<1⇒Θ=½`; implies AAL [D]; implied by the transfer of S3 [D] | sub | whole programme |
| B57 | Depth density `o(T)`: all but `o(N)` zeros within `o(1/log T)` of the line | sub | WD, CTF, MC, RW, PM |
| B58–B61 | `D_win`; cluster wall; Green moments at deep zeros; a detector past the last scale | sub | WD, MC |
| B62, B63, B66 | Cofinal long moment; collision charge; near-unit holomorphic budgets | RH | WD, CTF, AIF |
| B91, B94 | Cut-kernel mass; cubic theta identification and rational transfer | RH; past VK | RAC, MMD |
| B46, B96, B97, B100, B121, B137 | Proportional saving at length `(log X)^{2K}` at all heights; tail law at the Kronecker scale; first return past the VK rung; savings on moving blocks; freezing beyond the cap; collective depth floor uniform in `π(y)` | sub | BAG, PTT, TAPO, TTPO, CDGeo |
| B106 | A correspondence on the orientation cover with bounded local indices | RH | MC, HAT |
| B110, B126, B127 | Thick crude count; a one-sided bound on a sampling set; positive-measure lag recurrence | AAL | WL, ZCG, ACS, IWT |
| B145 | The signed centred type-II current, with both continuum terms, at a growing isolated mode; within it: the near-diagonal cofactor pairs and the prime-weighted lattice sum | AAL [D] | ZCG, BAG, ELT |
| B148 | The transfer of candidate S3 | ≥B56 [D] | S3, BAG |
| B150 | A form factor bounded by `4` on `(1,10/9)` | sub | census |
| B64, B65 | Signed pair information beyond bandwidth one; genus upper law and logarithmic Serre duality | sub; indep. | census, ACS |
| B98 | Positive-generator integer-norm systems: which count distance forbids a finite top layer | method | RAC, SPAL, APD |
| B113 | Möbius × quarter-disc remainder `O(X^{½+ε})` | beyond RH | PM |

### Γ — selection, reflection, transport, count
| # | Problem | Strength | Routes |
|---|---|---|---|
| B13 | Finitely many off-line zeros ⇒ none (world I-a) | sub | whole programme |
| B138 | Landing for ζ (as an atom) | sub | ZCG, LA, ELT, HF |
| B141 | Deuring–Heilbronn for ζ: `¬AAL⇒ZAL` (world I-b; §2.5) | sub | BAG, ZCG, ELT |
| B83 | AAL = B13 ∧ Landing ∧ DH | sub | BAG, JAS, SC, ZCG, WL |
| B89, B112, B128 | A bounded aligned return at each right zero; the FE into vertical transport; replication | sub | BAG, ZCG, EFT |
| B153 | **Bounded almost periodic constituents**: can a bounded Dirichlet series on a half-plane containing the critical line have a zero and all its zeros among those of ξ (§2.6) | method | IRP, W1C, PTR, PM |
| B68, B71 | Reflection Krein positivity, flux, dispersion; universal decay and the horizon rates `y^{¾−ε}` | RH | PM |
| B72–B76 | Cutoff-uniform target mass; the candidate zero-parameter conditions; FE-pair reality | RH | BAG, candidates, ZCG |
| B80, B81 | FE twins in the full class; candidate landings | sub; producer | SEL; candidates |
| B86 | Endpoint character positivity at unbounded rank | RH | ECP, ACS |
| B87 | A nonnegative count on the rays `Γ_1+Γ_p`, defined without `Q` | RH | ACS, HF, PM |
| B88 | The sign of the comb finite part / of the Gram defect | RH | HF, ACS, HAT, AGZ |
| B114, B117 | A realization of the partner involution outside the excluded classes; a regulated horizon pure at every cutoff with ξ as its limit (§2.7) | producer | PM |
| B147 | Shimura nonvanishing at `ρ/4+¼` for one Hecke eigenform | indep. | PM |
| B149 | Bézout for the comb pairing on effective classes, from a property of the object (`CombBezout Λ`) | RH (producer) | ACS, HF, AGZ |
| B69, B70 | A positive physical or graph carrier; a lower bound for the Hecke dispersion from it | producer; sub | PM, W1C, PTR |
| B77 | `0∉E`: polynomial repulsion at the value zero | indep. | ZCG, LA |
| B78, B79 | Rosati positivity of the window reflection; band holomorphy of `Λ(s)/Λ(s+1)` | RH | HF, ACS, PM |
| B82 | Inner-field decay | ≥qRH | BAG, CTF |
| B92, B93 | A rotated relation with coefficients of the size of `Q`; a contradiction beyond the extremal law | RH | ZCG |
| B111, B116 | `ZAL⇒RH` = B13 ∧ Landing; linear AAL at one fixed slope | sub | ZCG, WL |
| — | ZAL | ≥qRH | whole programme |

### Settled method questions
| # | Question | Answer | Evidence |
|---|---|---|---|
| B143 | Decisive radius in the class `𝒵(γ_min,C)` | no bounded window and not every unbounded radius; the logarithmic radius decides ζ | [L*] |
| B140, B139, A64, A66 | Shortest decisive radius for ζ; sparse scale-local windows; sign-free local decision | radius `32 log(T+2)` with exceptional sets; absolute, width and signed-deletion forms | [L*] |
| B138 (as a method question) | Which structures decide landing | three-atom factorization; fails for the FE alone and for the Euler product alone | [L*] |
| B85, B142 | A family producing purity at ζ | none among the canonical families and their finite residue-class mixtures | [L*]/[S] |
| B133, question (G) | One glued carrier object for the diagonal | no; survivors: comb finite parts, weighted covariance, the clock, the scattering tower | [L*] |
| A85, exact factors | Dirichlet polynomials as factors of ξ, any support | none | [L*] |
| A87, two-block face | The comb form on two-bump packets at a prime | one inequality per prime on the comb, on logarithmic windows with exceptions | [L*] |
| A88 | Deep neighbours forced by positivity | the aperture-side resolution law with the neighbour count | [L*] |
| Field of fixed-part Hodge theory, its questions | Which comb; the carries; integer-norm monoids; the second axiom on the tower; the statement over a curve; over a quadratic ring; the two-block case; what the sections certify; the constant of the counterterm | one orbit of the Frobenius monoid; a nonzero class complementary to the window count; unit masses fix `Λ`; the product formula; a Toeplitz form with purity as its sign; contacts `Λ(1+χ)` with the conductor as a density and no class group; one inequality per prime; one contact per prime above; `2π` forced, no slack | [L*]/[S] |
| A70 | Torus periodization of the mixed Green kernel | absolutely convergent, symmetric, descends; leafwise Robin diagonal | [L*] |
| B125 | No halving pairs as a condition for the one-eigenform receiver | void; the condition is the Shimura zero (B147) | [L*] |
| A50 | Finite-stratum laws on the cosine and shifted Jensen families | Jensen: the law gives RH; cosine: the law gives RH ⇔ ZAL | [L*]/[L] |
| A65, A67, A74 | Two-prime local criterion; dominant-ordinate divergence; graded recurrence | theorems | [L*] |
| — | Periodicity of the zeros in height, two-sided and one-sided | none | [L*] |
| (S1), (S2) | A Frobenius with cheap simultaneous vanishing over ℤ; a sign-free quantity bounding the fibres of the height map | no (cost `m·θ(S)`); a receiver (ordinate injectivity ⇔ RH) | [L*] |
| Topological question on `S(T)` | Is the remainder the index of the archimedean gluing | the gluing conditions are the smooth count; the contacts at a height are the smoothed increments of `S` | [L*] |
| 𝔽₁ questions Q1–Q10, Q12–Q14, Q17, Q18 | see §2.14 | answered | [L*]/[S] |
