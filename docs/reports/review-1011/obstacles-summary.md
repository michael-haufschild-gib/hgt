# Obstacles summary — status quo

Companion to [route-obstacles.md](route-obstacles.md) (per route), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ) and [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem). Corpus checkpoint: commit `d0cfbbc75f` with its working tree (2026-11-10). Working log: `logs/review-1011-frontier-facts.md`.

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
- Finitely many simple poles of `−Gζ/s` on the line do not change the agreement of the constant terms: the two series of fractional parts differ by a continuous polar part [L*].
- Not covered [L]: bounded Dirichlet series with zeros on the line, partial common zeros, limits of approximants.

### 1.6 Exactness over ℤ has an exact price
`x↦xⁿ` is additive in characteristic `q` exactly when `n` is a power of `q`; `Λ(n)` is the `log q`-weighted number of primes at which `F_n` is a Frobenius [L*]. Order `m` of the Fermat-quotient derivations at every prime of `S` costs `log|a|≥m·Σ_{p∈S}log p`; `ℤ` has no ring endomorphism but the identity [L*]. The minimal fixed-point auxiliary has log length `ψ(N)`, and RH ⇔ `ψ(N)≤N+C√N log²N` [L*]. On the tower of lines Riemann–Roch has the gluing index `K!` and Bézout gives `n≤|x_n|`: the product formula [L*]. A section of the square that vanishes on the graphs of the proper divisors of `m` and not on `Γ_m` pays all those contacts; upward it pays one contact per distinct prime: `p−e_p` vanishes on every `Γ_{p^j}` and has the value `p` on `Γ_1` [L*]. The carry is a cocycle that is not a coboundary; the carry defect and the window-count defect are complementary up to `½log(πN)+o(1)` [L*]. At one prime Stepanov's method runs on the first Witt carry: `|Σ_{n≤p}e(an^p/p²)|≤5p^{11/12}` [L*].

### 1.7 The comb: one matrix on the integers, a Hodge index equivalent to RH, no positive margin
- **Pairing and zeros.** On packets the pairing of the degree points tends to `2d₁d₂−Z(f)`; RH ⇔ exactly one positive square on the two rulings and every finite family of packets; the defect has at most `#{ρ: Re ρ>½}` negative squares [L*].
- **The sign is carried by the contacts.** Comb Bézout with weights `w` ⇔ RH ∧ `w=Λ`; unit masses on the integers force `w=Λ`; with a doubled weight at `2` the flat tail violates the inequality at every large scale [L*].
- **The constant of the counterterm.** With the counterterm `log(n/2π)−c` the inequality holds for all packets ⇔ `c≤0` ∧ RH; for every `c>0` a packet with both degrees zero has `Z(g)<c∫g²` [S]. So no positive margin exists, and a uniform floor `Z(f)≥−C∫f²` over all packets, with any fixed `C`, is RH.
- **Finite scale.** On `S⊆(N,N+M]`, `18M≤N`, every real divisor has comb form `≥(1/50)Σc_n²`. For every ratio `Q` there is `R` such that for `N≥R` the comb form is nonnegative on the real divisors of `(N,QN]` whose sums over blocks of `⌊N/R⌋` points vanish; the blocks are fewer than `2QR` [L*]. If for every ratio and every `η>0` the comb form is `≥−ηΣc_n²` on every real divisor of the window at arbitrarily large scales, RH holds; if RH fails, some ratio has, at every large scale, a real divisor with `Σc_n²≤C` and comb form `≤−ε` [L*].
- **Selectivity.** A window of ratio `≤2` contains no pair in divisibility: the form is the same for every system of contact weights, and the short-window floor holds for all of them. On the single point `{2}` the form is `c²(1−log π)<0`: nonnegativity on every finite set is false [L*].
- **Jets by weights.** `½(1/|m−n|+1/(m+n))=Σ_{j≥0}min^{2j}/max^{2j+1}`; each weight, with the diagonal `1/n`, is positive semidefinite (a Hardy square); the truncations to the first `J` weights increase to the comb form, with remainder `≤(1−1/N)^{2J}` times half the Dirichlet form of the jets [L*]. The weights are the even multipoles `r_<^ℓ/r_>^{ℓ+1}`, `ℓ=2j`, of the Newtonian kernel `1/|x−y|` in `ℝ³` between a point at distance `m` on an axis and the pair `±n`; the weight-zero kernel `1/max` at the points `0` and `∞` gives the pairings `1/n` and `1` with the two rulings [D]. The contact form of one prime is `log p` times the sum over the chains `{mp^k}` of the square of the chain sum minus its diagonal [D].
- **Potential.** In the gauge of the flat tail the potential at `n` is `N/n−ψ(N/n)` plus an explicit smooth term; the form of the flat tail per degree point tends to `2+γ−log 4π`, twice the first Li coefficient [L*]/[D].
- **Curves.** On the comb `q^ℤ` of a curve the comb form is the Toeplitz form of the normalized Frobenius eigenvalues; nonnegativity on every finite set ⇔ purity; on one graph it is `2g·e_k²`; no jets, no counterterm; the golden datum violates it [S]. Purity of a curve datum is decided on the window of `#spectrum` degree points [L*].
- **Quadratic rings.** For a real primitive character of conductor `q>1` the ideals counted by their norms sit on the comb of the integers with contacts `Λ(n)(1+χ(n))`; the pairing tends to `2d₁d₂−Z_ζ−Z_χ`; the twisted part has no pole plane and the counterterm `log(qn/2π)`; the class group does not enter; with the conductor `qe^{−c}`, `c>0`, some packet of degree zero has a positive pairing [S]. The defect of the pairing has at most as many negative squares as ζ and `L(s,χ)` together have zeros right of the line; on packets shorter than `log 2`, for an odd character of conductor `q≥4π` or an even one of conductor `q≥128π`, the twisted part is nonpositive and the inequality holds on the square of the ring with the margin `∫f²/5000` [S].
- **Index and splittings.** If the right zeros are zeros of `P_WE−cP_{W♯}E′` with `|E′|≤|E|` right of the line and `W` of `κ` points, Weil's form has at most `κ` negative squares; the cleared Eisenstein constant term gives at most one for `Y≥1` and none for `1≤Y≤4πe^{−γ}` [L*].
- **Counting.** The gluing index of the first `N` graphs is `N!`; `G(T)−N(T)+S(T)→½log 2π−7/8`; the contacts at a height are the smoothed increments of `S`, up to the off-line correction [L*].

### 1.8 The adelic carrier and three regulators
Every adelic-invariant kernel with a torus-orbit functional has a constant degree diagonal; no scalar counterterm removes the jump `−2‖g‖²log p` between `p` and `p³` [L*]. The weighted mixed hyperbolic Green kernel converges over the rational torus, has a leafwise Robin finite part, and its spherical average at parameter `½` is the minimal Green kernel of the all-prime weighted adjacency [L*]; the weighted adelic adjacency has norm equal to its Schur edge, approached by finite nonnegative charges, and below the tempered edge no nonnegative point-source supersolution exists [S]; none of these identifies Weil's degree diagonal [L].

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
| Newton polygons (Sheats) | digit combinatorics in Lean; optimal ⇔ greedy for two parts and for one residue class; constraints on a minimal nongreedy optimum; the general optimality open; separation by absolute value is excluded for ζ; the carry is a nonzero class | [S]/[L] |
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
| the sign over all test functions | no positive margin: best margin of a window `≤K exp(11c/2−πe^{2(c−2)})`; no change of one contact weight; no constant above `2π`. Downward: a uniform floor `−C∫f²` over all packets, any fixed `C`, is RH | [L*]/[S] |
| a floor at the primes for one fixed bump | any floor `−Kp^α` with `α` arbitrarily small on logarithmic windows gives width `α`: `P(p)≤A(p)+p^{o(1)}` suffices | [L*] |
| the index | one unit: at most one complex zero per approximant suffices | [L*] |
| returns | a power: `T^c` returns, `c>(30/13)(1−σ)` | [L*] |
| the heat flow | none at time zero | [L] |

An estimate can meet a statement where it has slack: on the prime side `p^{o(1)}` for one fixed test; on the sign side any uniform constant over all packets [D].

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
| A78 | Cluster form of the separated-window theorem (unverified) | SRT, ACS | `re_le_of_bddBelow_exp_windows_of_deepSeparated` |
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
| A84 | Optimality of the greedy carry-free composition and the Newton polygon of the Carlitz–Goss zeta function [C] | sign-free calibration | `tokenPrefix_iff_inverseContent`; `isOptimal_two_iff_isGreedy`; `isOptimal_iff_isGreedy_single_residue`; `exists_deficient_coordinate_of_minimal` |
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
| Field of fixed-part Hodge theory, its questions | Which comb; the carries; integer-norm monoids; the second axiom on the tower; the statement over a curve; over a quadratic ring; the two-block case; what the sections certify; the constant of the counterterm | one orbit of the Frobenius monoid; a nonzero class complementary to the window count; unit masses fix `Λ`; the product formula; a Toeplitz form with purity as its sign; contacts `Λ(1+χ)` with the conductor as a density and no class group; one inequality per prime; one contact per prime above; `2π` forced; no positive margin | [L*]/[S] |
| A70 | Torus periodization of the mixed Green kernel | absolutely convergent, symmetric, descends; leafwise Robin diagonal | [L*] |
| B125 | No halving pairs as a condition for the one-eigenform receiver | void; the condition is the Shimura zero (B147) | [L*] |
| A50 | Finite-stratum laws on the cosine and shifted Jensen families | Jensen: the law gives RH; cosine: the law gives RH ⇔ ZAL | [L*]/[L] |
| A65, A67, A74 | Two-prime local criterion; dominant-ordinate divergence; graded recurrence | theorems | [L*] |
| — | Periodicity of the zeros in height, two-sided and one-sided | none | [L*] |
| (S1), (S2) | A Frobenius with cheap simultaneous vanishing over ℤ; a sign-free quantity bounding the fibres of the height map | no (cost `m·θ(S)`); a receiver (ordinate injectivity ⇔ RH) | [L*] |
| Topological question on `S(T)` | Is the remainder the index of the archimedean gluing | the gluing conditions are the smooth count; the contacts at a height are the smoothed increments of `S` | [L*] |
| 𝔽₁ questions Q1–Q10, Q12–Q14, Q17, Q18 | see §2.14 | answered | [L*]/[S] |

## 2.3 Frankenstein routes

**No assembly closes RH.** Every assembly below has an open input of RH, AAL, ≥qRH or Landau–Siegel strength, or names one. Their value is to collapse independent problems into one, to decouple the producers a proof needs, or to fix what a missing input must contain.

| # | Parts | What the assembly gives | Missing input | Gain |
|---|---|---|---|---|
| F1 | **Two-world skeleton.** A floor on windows of any unbounded radius (kills world I) with any ZAL receiver, or a floor on logarithmic windows (kills both) | RH [L*] | one floor | below the logarithmic radius the two worlds need two inputs at the level of `𝒵` [L*] |
| F2 | **One inequality per prime, local, with exceptions.** Prime two-bumps, Stepanov count, count door, sign-free form, logarithmic windows, power-thin exceptional sets, two-bump comb packets | Σ, Π and count readings are one number per prime on sparse windows [L*] | B130 on one sequence of windows | one target with slack `p^{o(1)}` (§1.16) |
| F3 | **Deligne skeleton over ℤ.** Tensor positivity, Künneth, Rankin square, gauge family with big monodromy | every step except the family step, which the fixed-part laws close [L*] | none exists inside the canonical families | support, not a route |
| F4 | **Critical curve.** Threshold identities, hierarchy, pole channel, ground states, classification | one inequality and one orthogonality [L*] | B104 | RH ⇔ `R_c=W₀` if the orthogonal case is excluded [D] |
| F5 | **Horizon.** Cavity receivers, reflection Krein forms, one-eigenform reduction, count door | physics reduces to one rate or one reflection sign [L*] | B71 or B68 | receivers complete and sharp |
| F6 | **Regulators.** Cusp cutoff, Green damping, scattering tower, comb finite parts | one pure regulator with the limit `(s−1)ξ(2s)`; two regulators that approach Weil's form from below by a positive jump tail [L*]/[K]/[D] | B88, B117 | RH ⇔ regulated energy ≥ minus its defect, in two regulators |
| F7 | **Rigidity.** Hamburger, FE-defect isolation, count distance, isozeric deformations, fixed part, factor theorems | ζ is identified by any two of its structures, has no moduli and no Dirichlet-polynomial constituent [L*] | B112, B153 | no calibration that deforms ζ exists; the calibrations with both structures are other `L`-functions (F22) |
| F8 | **Finite-layer world.** Free strip, Mertens power saving, late heavy returns, filters at every speed, centred Vaughan currents at growing order, separated cofactor pairs | a complete receiver with an exact gap `a(1−β)/2` [L*]/[K]/[S] | B145 | the missing bound is the exclusion |
| F9 | **Exactness.** Frobenius at one prime, `m·θ(S)`, Chebyshev auxiliaries, tower Riemann–Roch, sections of the square, carry cocycle | every exact method over ℤ returns the product formula or Chebyshev [L*] | B97, B137, B121 | what survives is approximate, growing-height information |
| F10 | **Count skeleton.** Tate principle, hyperelliptic count law, contacts in `𝒢`, tower of lines, section counts | Riemann–Roch has an exact count; Bézout for the comb pairing is the Hodge index [L*] | B87, B149 | the count door and the sign door need the same statement |
| F11 | **Construct, then identify.** Index semicontinuity, FE rigidity, the index of the pairing ≤ the defect of a splitting | a nonzero limit of index-one functions with ζ's FE and a Dirichlet series gives RH; a splitting of defect `κ` bounds the index of the comb pairing by `1+κ` [L*] | B146 | the only pointwise conversion with one unit of slack; Dirichlet polynomials and stable prime polynomials are excluded as pieces [L*]/[L] |
| F12 | **Graded recurrence.** Transport receivers with the density theorem; strong recurrence ⇔ RH | `T^c` one-separated returns, `c>(30/13)(1−σ)`, exclude a zero right of `σ` [L*] | returns of ζ to its own target | power-sparse returns suffice |
| F13 | **Sign-free skeleton.** Signed deletion, two-sided windows, ordinate injectivity, index law, recurrence against density, two-sided constant terms | RH from `\|c_p\|≤K` on log-square windows; two pointwise theorems on constituents [L*] | a two-sided producer; B153 | under the constraint the receiver is complete |
| F14 | **Dark range.** Savings, heavy-return dictionary, strip breadth, collective counts | one first-return statement, proved to the VK height [L*]/[L] | B97, B137 | gap `(log y)^{3/2}` against `y^c` |
| F15 | **Theta wall.** Adaptive head `=ζ(½+ib)` up to `O(\|b\|^{−½})` [L] | all ranks reduce to the size and sign of ζ on the line near its zeros | B102 | merges TH with the critical-line sizes |
| F16 | **Census.** Covariance ceiling, exchange rates, near-line alternatives | `70%` follows from a bounded form factor [L*]/[L] | B150 | a law statement with exact receivers |
| F17 | **The comb at finite scale.** Normal form, short windows, finite index, forced weights and constant, jets by weights, curves, quadratic rings | RH ⇔ one explicit matrix on the integers has one positive square on every window in the limit; the statement at finite scale with any relative slack suffices [L*]/[S] | B152 | the same matrix for ζ, a curve (no jets, no counterterm) and a quadratic ring (conductor as density) |
| F18 | **Flow.** Trace determines the module; Castelnuovo–Severi on the flow | RH ⇔ the lag function is positive definite on `ℝ` [D] | the sign | WL and ACS are one statement on the flow |
| F19 | **Remainder.** Gluing index, zero count, contacts at a height | zero count at a height = gluing conditions − contacts + off-line correction, smoothed [L*] | — | the index formula of the square is the argument principle |
| F20 | **Existence half.** Prime-blind duality, dependence of the aperture on finitely many weights, rigidity of `Λ` | RH ⇔ at every aperture some real weight system is Weil-positive: the feasible sets are compact, convex and nested, and a common point is `Λ` [D] | a construction of feasible weights (B18) | a producer need not know `Λ`; if RH fails, some aperture admits no weights at all, for a reason that involves no prime |
| F21 | **Resolution atlas.** Aperture law with neighbour count, cut crystal, logarithmic prime windows, heat count, curve determinacy, verified height | every graded receiver is a chart on the plane of depth and height; the charts differ in exchange rate [L*]/[D] | A93 | where a verified height buys most; which finite-parameter theorems carry information on zeros |
| F22 | **Conductor ladder.** Quadratic-ring comb, twisted part without pole plane, classical Deuring–Heilbronn, the trivial aperture | the twisted part is negative semidefinite to aperture `log log q−log 4`, and with a margin on packets shorter than `log 2` for conductors `≥128π`; an exceptional zero is one positive square at aperture about `log log q` [S]/[D]/[A] | B154 | the smallest unsolved instance of the missing sign, inside the corpus's objects; every sign mechanism can be run on it without RH |

**Closest to the open core: F2, F17, F8, F11, F22.**

### What a contradiction search may assume in world I (F8)
| In world I | Evidence |
|---|---|
| `Θ<1`; isolated top `β`, attained; remainder `≤Θ∞<β` above the layer's heights | [L*] |
| `M(x)=O(x^{β′})`, `β′<1` | [L*] |
| heavy returns at `t≥T₁` need `log t≥c·y^{1−β″}`, `β″<Θ` | [L*] |
| filters read each top residue at every damping speed | [L*] |
| two distinct positive top ordinates, or pointwise divergence of the corrected current | [L*] |
| centred type-II currents on polynomially many cofactors with error `O(e^{−at/4})`; separated cofactor pairs negligible | [K]/[S] |
| one-separated returns to a small disc at a zero right of `σ` number fewer than `T^c`, `c>(30/13)(1−σ)` | [L*] |
| no half progression of zeros through a top zero | [L*] |
| every floor fails on windows of every unbounded radius; a layer of `k` quartets is seen on windows of a length depending on `k` (A95, unverified) | [L*] |
| in world I-a the window index and the nonreal heat count are bounded | [L*]/[L] |

No contradiction comes from exact identities alone, from positivity, Euler products, integrality or counting alone, from the FE with order one and reality, from a property shared by the heat family, or from any in-law statement [L*]/[L]/[D].

## Validation tests for 2.4–2.8 and 3

| Test | Requirement |
|---|---|
| T1 | Implied by RH and not implying quasi-RH; for §2.5 and §3 also not implying AAL (or a method question implied by nothing about ζ's zeros) |
| T2 | Answered by proving or refuting a stated inequality, identity or implication |
| T3 | A named consequence can be written down for either answer |
| T4 | Not decided by a finite rung |
| T5 | False on a corpus fake, or calibrated on the fakes |
| T6 | Names an input not refuted in Lean |
| T7 | Moves a wall; not a shape already answered |
| T8 | Not a named long-standing problem in disguise (RH, quasi-RH, ZAL, AAL, B13, Lindelöf, pair correlation, Hardy–Littlewood, Chowla, past VK, Landau–Siegel, strip self-improvement); its first step uses corpus objects and has one named obstacle |

**No question passes all tests and is a door to RH.** The corpus search by meaning returns a statement for every structural question about receivers that was generated for this report: resolution on the aperture side, existence of weights, finite determinacy over curves, selectivity of short windows, the constant of the counterterm, the comb of a quadratic ring, exact polynomial constituents, positive ground states, stable approximants, strong recurrence (§1.15; log §6). The questions below are those that the search leaves open; each states its limit and its failed tests.

## 2.4 Breakthrough question below RH and quasi-RH: does the pole channel see every failure first?

**Question (B104).** *If RH fails, is every critical half-line ground state charged?* At the critical curve `R=c⁸/log N` the three cases are RH; ¬RH with `R_polar<W₀`; ¬RH with `R_polar=W₀` finite and every unit critical half-line ground state orthogonal to the polar source [L*]. Is the third case empty?

**What is proved [L*].** `R_c=R_polar=R_halfline`; a critical ground state `F` at `W₀` with polar pairing `S` gives `R_polar≤(1/W₀+D₀S²/(7J(1)D₀²I₈+J_bulk(1)S²))^{−1}`, so a charged ground state forces `R_polar<W₀`; payment at a ratio leaves the reserves `(1/R−1/S)(7J(1)·I₈+J(1)t²)` at every smaller ratio; a terminal window close to the horizon receives a strictly positive polar source at every critical ratio. No countable square-bounded family of holomorphic multipliers dominates the depleted kernel.

**What either answer gives.**
| Answer | Effect |
|---|---|
| The third case is empty | ¬RH ⇒ `R_polar<W₀`: the complete matrix fails strictly before the windows; RH ⇔ `R_c=W₀`; the five routes that meet at the critical curve (HF, SRT, AIP, ACS, SC) have one inequality with a rank-one payment [D] |
| A polar-orthogonal ground state is consistent | a second failure mode that the pole channel does not see; at such a threshold the complete matrix carries no information beyond the windows |

**First step and obstacle.** The window part of the half-line form is `lowGammaForm−primeSum+2cosh²−2sinh²` of the half moments [L*]. Its prime part and its jet part are of jump type, and a form of jump type does not increase under `F↦|F|` [L*]; the pole moments do increase when the two moments have one sign. A critical ground state therefore need not be of one sign, and its charge cannot be read from the sign of the polar source [D]. What remains is the Euler–Lagrange equation of the truncated form at `W₀` with the weight `e^{−8u}`: the charge is one linear functional of its solutions. Named obstacle: the equation contains the full zero side.

**Tests.** T1: vacuous under RH; implies no width. T2–T4: pass. T5: tempered fixed-ratio models show positivity at a fixed ratio is not automatic [K]. T6, T7: pass (Σ135, Σ139, B6, B101). T8: not a named problem.

**Limit.** Confined to the critical curve; it produces no sign.

## 2.5 Breakthrough question below AAL: the Deuring–Heilbronn sector

**Question (B141).** *Does an isolated top layer of ζ force the remaining zeros onto the line?* That is, is world I-b (`½<Θ∞<Θ<1`) empty.

**Position [L*]/[D].** AAL ⇔ B13 ∧ Landing ∧ DH, and a failure of AAL fails exactly one of the three. B13 is the emptiness of world I-a, the world of a bounded index, and contains the exclusion of one quartet; Landing is an atom of the RH path. DH is the only sector of AAL off the RH path and is vacuous in every ZAL world. B56 implies DH.

**What the sector looks like [L*]/[D].** At the top: a finite layer read by prime-only filters at every damping speed, Mertens power saving, two distinct top ordinates or a divergent corrected current. In the tail: infinitely many zeros approaching `Re s=Θ∞∈(½,β)`, of density zero in height, with heavy returns later than `exp(c·y^{1−Θ∞−ε})`.

**Calibrations.** Positive integer-norm two-scale Euler products realize every `(Θ,Θ₂,Θ∞)=(β,θ₂,θ)` with `½<θ≤θ₂<β<2/3`, and every graded repulsion bound is refuted on that class [L*]. For a real zero of a primitive quadratic `L(s,χ)` repulsion holds with a constant uniform in conductor, height and zeros [L*]: the one world in which an isolated layer is not excluded and its action on the other zeros is a theorem is the exceptional world of a real character (§3).

**What either answer gives.**
| Answer | Effect |
|---|---|
| Yes | world I consists of world I-a only: AAL ⇔ B13 ∧ Landing = (ZAL ⇒ RH); the finite-layer receiver is run over remainders on the line, where the index is bounded |
| A proof that no FE ∧ Euler identity decides it | a world `½<Θ∞<Θ<1` is consistent with everything the corpus uses; AAL needs vertical transport (B112) |

**First step and obstacle.** The classical mechanism needs a zero that nearly cancels the pole; ζ has none. On a line `Θ∞<σ<β` the complete filter that deletes the finite top is bounded by `Ch^dt^Ne^{at(c−σ)/2}` for every `c>Θ∞` [L], and the top modes grow at rate `a(β−σ)/2`. The question is whether the reflected top, entering through the FE, forces a term on the tail side that this bound forbids. Named obstacle: every filtered current is the filtered zero sum; a contradiction needs an inequality that the explicit formula does not imply.

**Tests.** T1: implied by AAL; implies none of ZAL, B13, quasi-RH. T2–T4: pass. T5: false on integer-norm two-scale products [L*]. T6: not refuted. T7: moves B83, Γ184. T8: contains the exclusion of an isolated top over a ¬ZAL remainder; not Landau–Siegel.

**Limit.** One sector of AAL; B13 and Landing are separate atoms.

## 2.6 If positivity, Weil positivity and spectral methods are excluded

"Spectral" is read as spectral theory of operators in every form; "positivity" includes nonnegativity of counts, Dirichlet coefficients, kernels and averaging measures, the Hodge index and Tate limits. Kept: Fourier analysis, mean values used as bounds, exponential sums, absolute convergence, continuation, power sums, integrality, recurrence, the argument principle.

**What survives [L*].**
- **Receiver.** RH ⇔ `|c_p|≤K` on arbitrarily late log-square windows, proved with complex deletion filters; RH ⇔ the ordinate is injective on the zeros.
- **Counting by winding.** The Hermite–Biehler index law and its semicontinuity; the index of the comb pairing is at most the defect of a splitting.
- **Recurrence against density.** A bounded Dirichlet series whose zeros are zeros of ξ is pure.
- **Two-sided constant terms.** If `−Gζ/s` is bounded and holomorphic in the strip with one-sided absolutely convergent scale expansions on the two sides, the constant terms agree; no Dirichlet polynomial is a factor of ξ. The mechanism is the jump of the fractional part: the additive structure of the integers.
- **Priced producers.** Frobenius at one prime; integrality reaches Chebyshev; exponential sums reach VK; Turán's power sums give two-sided detection without separation.
- **A calibration in characteristic `p`.** The digit combinatorics of the Carlitz–Goss zeta function is in Lean; an optimal composition is greedy for two parts and for one residue class [L*]; the general optimality of the greedy composition is open (A84).

Both pointwise theorems of this list are about constituents of ξ. Under the constraint the corpus has no theorem that locates a zero of ξ, and the corpus search returns no sign-free mechanism from outside that does (§2.9).

**The question (B153).** *Do the zeros of ζ carry an almost periodic constituent?* Let `F` be bounded and holomorphic on `Re s>x` with `x<½`, given by an absolutely convergent Dirichlet series far to the right, not identically zero, and suppose every zero of `F` in `Re s>x` is a zero of ξ. Can `F` have a zero?

**What is proved [L*].** The zeros of such an `F` lie on the line. For a Dirichlet polynomial the answer is no. The zeros of ξ contain no vertical progression, no half progression and no `ℓ²` perturbation of one.

**What either answer gives.**
| Answer | Effect |
|---|---|
| No | the zero set of ξ contains the zero set of no bounded almost periodic function: every exact arithmetic constituent is excluded, polynomials and series alike; a producer by construction and limit (F11) cannot use pieces that share zeros with ξ |
| Yes | an arithmetic object whose zeros are infinitely many zeros of ξ, all on the line by the factor theorem: a purity statement for an infinite set of zeros with no sign in its proof |

**First step and obstacle.** A zero of `F` recurs along a relatively dense set of shifts; near each shift ξ has zeros because its gaps tend to zero [C], so positions alone give no contradiction. The zero measure of `F` is almost periodic; the zero measure of ξ has the transform of the explicit formula, atoms at `±log p^k` and a continuous part. The polynomial proof uses the highest frequency for the expansion left of the line. Named obstacle: a series has no highest frequency and is not defined left of `x`.

**Tests.** T1: a method question, implied by nothing about the location of ζ's zeros. T2–T4: pass. T5: curve zeta functions are their own constituents; polynomials are excluded [L*]. T6: not refuted. T7: moves B146, Γ212. T8: not a named problem; first step in corpus objects, one named obstacle.

**Limit.** It decides what can share zeros with ξ, not where the zeros of ξ are. Under the constraint no question below quasi-RH does more.

## 2.7 If RH is a physical phenomenon in AdS with a modular horizon

**What is proved [L*]/[L]/[K].** The modular horizon is the quotient of the Rindler wedge of AdS₄ by `SL₂(ℤ)`; its resonances sit at the zeros of `ξ(2s)`; RH ⇔ every pulse rings down at the quarter rate ⇔ one cavity energy of Hecke forms decays at `y^{¾−ε}` ⇔ every reflection Krein form has no negative square. Three regulators are in Lean (§1.8). A bulk built from one adelic-invariant kernel with Weil's diagonal does not exist.

**The reading [D].**
- The cusp cutoff is a unitary system at every cutoff and converges to `(s−1)ξ(2s)`.
- The clock and the scattering tower converge to Weil's form and differ from it by a positive jump tail: `0≤W−E_r≤(1−r²)‖f′‖²/2`; the second-height defect of the tower tends to `½∫|u′|²`. In both, RH reads: the regulated energy is at least minus its own defect. Positivity of the jump term does not bound the form [L].
- The tower of height `N` is the explicit formula of `Λ(s)/Λ(s+N)`. At `N=1` this is the scattering quotient, whose size comparison `|ξ(w−1)|≤|ξ(w)|` on `Re w>1` is unconditional [L*]. Integer heights move the reflected zeros to the left; they do not approach the line.

**The question (B117).** *Is there a regulator of the modular horizon that is unitary at every cutoff and has ξ as its limit?* A family of self-adjoint boundary conditions on the quotient of the wedge whose secular functions are conjugation-real, have at most one right-half zero, and converge locally uniformly to ξ. Then RH holds [L*]. The three regulators of the corpus show the two ways to miss: a unitary regulator with the limit at a shifted argument, and regulators with the right limit whose defect is a jump tail of one sign.

**Why it opens the path.** It replaces a sign at the horizon by unitarity of each regulated system and continuity of the limit; the identification of the limit is free [L]; internal modular conjugation, vacuum-fixing partners, half-sided inclusions and the glued invariant bulk are excluded [L]/[L*]; graph black holes with `t²>4q` are impure at every size [L].

**A physical calibration [D]/[A].** In the twisted sector of a quadratic ring the conductor enters as a mass term `log q`; below the aperture `log log q−log 4` it dominates every contact, and an exceptional zero is one unstable mode appearing at aperture about `log log q` (§3). A physical principle that stabilizes the horizon of ζ and is uniform in the sector must stabilize this mode.

**Limit.** A regulator whose secular function is built from the zeros is a restatement.

## 2.8 If RH is a problem of topology or geometry

**What is proved [L*]/[S].** The arithmetic square is a curve; its graphs meet in the primes; no object of finite type carries the contacts; sections pay one contact per prime above. The pairing of the degree points has a Hodge index theorem equivalent to RH, with no positive margin, no other weight and no larger constant in the counterterm. In the normal form it is one matrix on the integers: windows of ratio `≤19/18` are negative definite at every scale for every system of weights; windows of ratio `≤2` do not see the contacts; the index of a window is finite uniformly in the scale; the jets are a sum of positive semidefinite weights. The same matrix without jets and without counterterm is the Toeplitz form of a curve, decided on a window of `2g+1` points [L*]/[D]; with the conductor as a density it is the square of a quadratic ring, in which the class group does not enter.

**Readings [D].**
- *Genus function.* In the normalization of a curve, where the form on one graph is `2g·e²`, the form on the degree point `n` is `e²(2+n log(n/2π))`: the genus at `n` is `1+(n/2)log(n/2π)`, negative at `n=2,3`, and of the order of the number of zeros below the height `πn`.
- *Riemann–Hurwitz.* The counterterm of a quadratic ring, `log(qn²/(2π)²)`, is twice that of the integers plus `log q`: the conductor is the ramification term.
- *Electrostatics.* The jets are the Newtonian interaction in `ℝ³` of charges at the points `±n` of an axis, and the two rulings are the points `0` and `∞`.

**Geometric question (B152).** *Is the comb form on the real divisors of a window bounded below by `−ηΣc_n²` at arbitrarily large scales, for every ratio and every `η`?* This gives RH [L*]. A statement that separates the integers from a fake must involve a window with a contact or the flat tail [L*]; the first such window has ratio between `2` and `3` and one contact (A96).

**The smallest geometric instance (B154).** On the squares of quadratic rings the twisted part is a lattice without a positive class. It is negative semidefinite on windows of aperture `log log q−log 4` for the trivial reason that the conductor dominates the contacts [D]; an exceptional zero is one positive square at aperture about `log log q` [A]. The Hodge index of these squares at apertures `log log q+C` is the Landau–Siegel problem (§3).

**Topological question (B106).** *Is there a correspondence on the orientation cover over ℤ with bounded local indices and Lefschetz number the number of points of the cover?* It would bound the centred count `|M(N)|` by the dimension of the middle cohomology times `N^{½}` [L*].

**Limit.** B152 at every ratio is RH; B154 is a named problem.

## 2.9 New field for RH: selective arithmetic

**Does RH need a new field?** Yes, and not a further language for the inequality. The fields named for this place in the reports of this series exist as programmes: the arithmetic Castelnuovo–Severi theory, the surface and the absolute geometry of Spec ℤ, the infinite-rank purity theory, the arithmetic weight theory and the Hodge theory of a fixed part. Their theorems are in §1.4–§1.7. Each ends at the same statement, a sign with no positive margin, and each is a receiver. The census of §1.15 shows that every mechanism that proves a statement of this type elsewhere has a Lean-fixed price over ℤ. What no programme of the corpus contains is a producer.

**Mathematics for which the corpus search returns no statement, with a verdict [A].**
| Mechanism | What it would give | Verdict |
|---|---|---|
| Integrality with an archimedean size condition (Pólya–Carlson, Borel–Dwork, Fekete–Szegő, formal-analytic arithmetic surfaces) [C] | exact structure of sections: a section of `𝒢` is an integer sequence with the necklace congruences; bounded ones are cyclotomic | no bridge to a sign: the archimedean pairing of the comb is a Riesz kernel of exponent one in the lag, not the logarithmic Green function of a surface |
| Convexity of semigroups of sections (Brunn–Minkowski, Okounkov bodies) [C] | a Hodge index from a count | needs a rank-two valuation on sections; sections pay one contact per prime [L*] |
| Measure and cocycle rigidity of commuting dilations [C] | classification of invariant measures of the Frobenius monoid | no optimal exponent; the orbit theorem and the carry class are its only instances in the corpus |
| Spectral reciprocity of moments [C] | exact identities between families | the zeros enter at `ρ/2`, under the Maass spectrum at `½` |
| Interlacing families [C] | one good member from a real-rooted average | needs a family; the fixed-part laws leave none |
| Fourier interpolation at the zeros and at `log n` [C] | a basis dual to the explicit formula, without positivity | unconditional for functions analytic in a strip; no statement about the location is known to follow |
| Entropy decrement [C] | cancellation at most scales | `o(1)` only; the receivers need `p^{−½+o(1)}` |
| The Habiro ring, prismatic and `q`-de Rham cohomology [C] | functions on the formal neighbourhood of the cyclotomic divisors of `𝔾_m` over ℤ, with every Frobenius lift | an object, not a mechanism; see §2.14 Q20 |

None of these is a producer. The field that RH needs has no existing name.

| Aspect | Content |
|---|---|
| What it is about | Selective statements at unbounded scale: inequalities that hold for ζ and fail for a system sharing all its structures but one, and that are not transports of the classical zero-free region, of a density theorem, of rigidity or of a verified height. Their sources, their slack, their smallest instances |
| What it is like | A theory of producers: for every candidate mechanism a price, a calibration on a fake and a calibration on a true `L`-function with a possible exceptional zero. It does not add an equivalent of RH |
| Established | The prices of §1.15; non-selectivity of short windows; no positive margin, no other weight, no larger constant; a uniform floor on the sign side and `p^{o(1)}` on the prime side as the available slack; the feasible sets `𝒜(a)` and RH ⇔ all nonempty [D]; resolution laws on the aperture side; the comb of a curve and of a quadratic ring [L*]/[S] |
| Criteria for a producer | P1 it proves the two-block inequality at one prime ratio at fixed width. P2 it fails with a doubled weight at `2` and with a constant other than `2π`. P3 it proves no margin: at every negative time the heat flow has non-real zeros. P4 it uses the FE and the Euler product jointly: it fails on the integer-norm one-off, the `cosh` models and the heat family. P5 it is not a family, not a section count, not a stable approximant, not a positive ground state. P6 run on the twisted part of a quadratic ring it closes the gap `log 4` of the conductor ladder, or it uses the pole plane in a way that the twisted part does not have. P7 over a curve it reproduces the Toeplitz statement. P8 its output is pointwise |
| Questions it must answer | Which unconditional theorems of the corpus are selective at unbounded scale, and from which sources (A93)? Is there a source beyond exponential sums, mean values, rigidity and the additive identity of the fractional part? Can a feasible weight system be constructed at every aperture (F20)? Is the exceptional square removable (B154)? What is the first selective window (A96)? |
| Tools it develops | The slack map; the exchange atlas; feasible sets and their duality; the conductor ladder; calibration on fakes and on true `L`-functions; the resolution laws |
| Objects | Selective inequalities, sources, prices, feasible sets `𝒜(a)`, exceptional squares, trivial apertures, charts of depth and height |
| Language | selective, source, price, slack, trivial aperture, exceptional square, feasible weights, chart |
| Mechanisms | Built on: the receivers and prices of the corpus. To discover: one source of pointwise information at square-root precision |

**Main conjecture.** There is a selective inequality for ζ at unbounded scale whose proof is not a transport of the classical region. **Milestones.** M1 the atlas of sources (A93). M2 the exceptional square (B154). M3 a zero-free strip in one aspect. M4 RH.

## 2.10 New field for AAL: repulsion theory of isolated layers

**Does AAL need a new field?** Yes. The instrumentation of world I exists as `ExceptionalLayerTheory` with the abscissa laws: filters at every speed, centred currents at growing order, separated cofactor pairs. Its residual is the exclusion itself (B145). What does not exist is a theory of how an isolated layer acts on the other zeros. Its one theorem is classical and concerns a real zero.

| Aspect | Content |
|---|---|
| What it is about | The action of a finite isolated layer on the remaining zeros of an object with FE and Euler product: repulsion, forced approach to the line, forced relations among residues. The two worlds I-a (bounded index) and I-b (off-line tail) |
| What it is like | Deuring–Heilbronn theory for a layer that is not real: the layer is a finite datum, and the theory computes what it forces at every height and in every other member of a family |
| Established | The sector theorem; classical repulsion for a real zero of a primitive quadratic `L(s,χ)`, uniform in conductor, height and zeros; refutation of every graded repulsion bound on integer-norm products; the instrumentation of world I; the comb of a quadratic ring with its twisted part [L*]/[S] |
| Criteria | Reproduce the classical real case. Fail on integer-norm two-scale and approaching Euler products, on `cosh` models and on `ζ(s−h)`. Use the FE and the Euler product jointly. Not be a statement in law. Treat a quartet as two squares and a real zero as one |
| Questions it must answer | Is world I-b empty (B141)? In world I-a, does a bounded index force a relation among the top residues? Is classical repulsion a margin on the other squares of the twisted comb (A101)? Does the reflected top act on the tail? What bounds the near-diagonal cofactor pairs (A86, B145)? |
| Tools it develops | Finite-layer filters; centred currents; the twisted comb; repulsion constants; Turán's power sums for layers of bounded size (A95) |
| Objects | Layers, tails, exceptional squares, repulsion laws, filters, corrected currents |
| Language | layer, tail, repulsion, exceptional, sector, bounded index |
| Mechanisms | Built on: the sector theorem, classical Deuring–Heilbronn, the instrumentation. To discover: repulsion by a non-real layer |

**Main conjecture.** An isolated non-real top layer of an object with ζ's structures forces the remaining zeros onto the line. **Milestones.** M1 [L*] instrumentation; the real case. M2 the real case in comb form (A101). M3 B141. M4 B13. M5 AAL.

## 2.11 New field for RH without positivity: constituent theory of the zeros

**Does a positivity-free RH need a new field?** Yes. The mechanisms that survive the constraint exist as `SignFreePurityMechanisms` and in the factor theorems of `InfiniteRankPurityTheory`. They prove purity for objects that share zeros with ξ, and ξ has no Dirichlet-polynomial constituent. No mechanism inside or outside the corpus locates a zero of ξ under the constraint.

| Aspect | Content |
|---|---|
| What it is about | Which objects with an arithmetic expansion can share zeros with ξ: exactly, on a half-plane, in a box, in the limit. The zero measure of ξ against almost periodic measures |
| What it is like | A theory of what the zero set does not contain: progressions, half progressions, zero sets of polynomials; proved by recurrence against density and by the jump of the fractional part |
| Established | Bounded Dirichlet-series factors are pure; no Dirichlet polynomial is a factor; two-sided constant terms; no progression, half progression or `ℓ²` perturbation; the index law; the anti-crystal law for the zeros [L*]/[L] |
| Criteria | No sign of a form and no operator. Hold for curve zeta functions, whose constituents are themselves. Fail for the non-tempered pair. Be pointwise |
| Questions it must answer | Do the zeros carry an almost periodic constituent (B153)? Up to which height can a Dirichlet polynomial of length `N` share off-line zeros with ξ, by recurrence against the density theorem? Can a sequence of approximants share zeros in growing boxes? Which splittings have a defect certified by sizes in a height window? What replaces the carry-free digit calculus when the carry is a nonzero class? |
| Tools it develops | Recurrence against density; two-sided constant terms; inverse expansions of zero-free exponential polynomials; the index law; Turán's power sums; the digit calculus |
| Objects | Constituents, factors, almost periodic measures, boxes, defects, deletion filters |
| Language | constituent, factor, recurrence, jump, defect, box |
| Mechanisms | Built on: the two pointwise theorems. To discover: a sign-free mechanism that acts on ξ itself; if B153 is answered in the negative, the constraint leaves none among the known ones |

**Main conjecture.** No bounded almost periodic function has a zero and all its zeros among those of ξ. **Milestones.** M1 [L*] polynomials. M2 series on a half-plane containing the line (B153). M3 approximate constituents in boxes. M4 a sign-free statement about ξ itself.

## 2.12 New field for RH as AdS physics: positive-energy theory of arithmetic horizons

**Does it need a new field?** Yes. The receivers, the Krein bookkeeping and three regulators exist as `BlackHoleRingdown`, `ArithmeticScatteringHolography`, `ArithmeticHolographyOfTheModularHorizon`, `CountingHolography` and `HyperbolicArakelovTheory`. The regulators show that a cutoff either keeps unitarity and moves the limit, or keeps the limit and loses the sign by a positive jump tail (§2.7). What physics would have to supply is a stability theorem.

| Aspect | Content |
|---|---|
| What it is about | Stability of systems whose energy is a jump form with the archimedean Lévy density and the prime contacts, coupled to a pole of rank two: when the pole does not bind a mode. Sectors labelled by a conductor, in which the conductor is a mass |
| What it is like | A positive-energy theorem at a bound with no positive margin: the unstable mode, if any, appears at an aperture, is one mode in a real sector and two in a complex one |
| Established | Ringdown, cavity and Krein receivers; the three regulators with their defects; the tower as the explicit formula of `Λ(s)/Λ(s+N)` [D]; the conductor as a density in the twisted sector [S]; the trivial aperture [D] |
| Criteria | Built from the places and the horizon, never from the zeros. Unitary at every cutoff with ξ as limit, or a stability argument on the limit itself. Impure for graph black holes with `t²>4q`. Uniform in the sector only if it stabilizes the exceptional mode. No margin |
| Questions it must answer | Which regulator is unitary at every cutoff with ξ as its limit (B117)? Is there a regulator whose defect is not a jump tail? What is the mode born at `4πe^{−γ}`? Does a mass term stabilize a sector beyond its trivial aperture (B154)? What selects the Shimura nonvanishing for one eigenform (B147)? |
| Tools it develops | Maass–Selberg calculus at general cutoff; the index law and its semicontinuity; the scattering tower with its exact jump kernel; Green damping; the twisted comb |
| Objects | The modular horizon, cutoffs, towers, jump kernels, defects, sectors, exceptional modes |
| Language | regulator, defect, jump tail, sector, mass, exceptional mode, trivial aperture |
| Mechanisms | Built on: the regulators and receivers. To discover: a positive-energy principle for a jump form with a pole |

**Main conjecture.** A unitary regulated family has secular functions of index at most one converging locally uniformly to ξ. **Milestones.** M1 [L*]/[K] the three regulators. M2 the regulators in the twisted sector with the conductor as mass. M3 the exceptional mode (B154). M4 a universal positive decay rate. M5 RH.

## 2.13 New field for RH as topology or geometry: genus theory of arithmetic squares

**Does it need a new field?** Yes. The lattice and index theory of the square exists as `AbsoluteGeometryOfSpecZ` and `HodgeTheoryOfAFixedPart`. It has the pairing, its normal form, its index, the comb of a curve and of a quadratic ring. It has no theorem in which the Hodge index is obtained from the geometry of a square at unbounded scale. The place where geometry gives it for a trivial reason is high genus.

| Aspect | Content |
|---|---|
| What it is about | The family of squares of number rings over the square of ℤ: genus functions, ramification, twisted parts. The regime in which the counterterm dominates the contacts, its boundary, and the first square that can violate the index there |
| What it is like | Over a finite field the Weil bound is trivial when the genus is large against the field; over ℤ the same holds for the twisted part of a ring of large conductor at bounded aperture. The theory lives at the boundary of that regime |
| Established | The genus function `1+(n/2)log(n/2π)` [D]; the counterterm as a density, additive under covers with the conductor as ramification [S]/[D]; the pairing of a quadratic ring as the sum of the part of ℤ and a twisted part without pole plane; no class group; the constant forced by Bézout; no gap on packets of degree zero [S]; finite determinacy over curves [L*] |
| Criteria | Reproduce curves: no jets, no counterterm, a window of `2g+1` points. Be selective. Treat a twisted part as a lattice without a positive class. Respect the no-gos: no finite type, no glued carrier, no section count |
| Questions it must answer | Is the twisted lattice negative semidefinite at aperture `log log q+C` (B154)? Is the comb form bounded below at finite scale at every ratio (B152)? What is the genus function of a ring of higher degree, and do the isotypic parts of a Galois ring carry separate indices (A91)? Does the index of a cover bound the index of its base? What is the weight filtration on the middle cohomology of the orientation cover (B106)? |
| Tools it develops | The normal form on norms; genus functions; Riemann–Hurwitz for counterterms; trivial apertures; block decompositions; Toeplitz calibration |
| Objects | Squares of rings, combs of norms, twisted parts, genus functions, exceptional squares, windows, blocks |
| Language | genus at a degree point, ramification, twisted part, trivial aperture, exceptional square |
| Mechanisms | Built on: the comb of ℤ, of a curve and of a quadratic ring. To discover: a reason of the square that removes one positive square beyond the trivial aperture |

**Main conjecture.** The twisted part of the square of every quadratic ring is negative semidefinite on windows of aperture `log log q+C`, for every `C`, for all large conductors. **Milestones.** M1 [S] the quadratic comb. M2 the trivial aperture (A100). M3 one exceptional square removed (B154). M4 windows of every ratio for the square of ℤ (RH).

## 2.14 A research programme to construct `𝔽₁`

**Goal.** A geometry in which Spec ℤ has a product with itself and one of the two proofs for curves runs. The programme is `AbsoluteGeometryOfSpecZ` with `HodgeTheoryOfAFixedPart`.

**What the corpus fixes.**
| Question | Answer | Evidence |
|---|---|---|
| Q1 Which endomorphisms have `N(n)` fixed points | the Witt Frobenius `F_n` on `𝒢=W(ℤ)`; `log#(ℤ/J(1,n))=Λ(n)` | [L*] |
| Q2 Multiplicity at a prime over `𝔽₁` | the order of the `p`-derivation; between graphs the contact order | [L*]/[L] |
| Q3 Why the diagonal is not local | a branch of a curve with torsion conormal classes; its archimedean entry is `log(density/2π)` of a comb | [L*]/[L] |
| Q4 Ampleness; Riemann–Roch ⇒ Hodge index | not without a second axiom; on the tower both axioms hold and give the product formula | [L*] |
| Q5 Gamma factor and pole as geometry | weights of the same Frobenius: `0,1` for the pole plane, `−2j` for the jets; each weight of the jets is a positive semidefinite kernel | [L*] |
| Q6 Integer-norm monoids other than ℤ | invisible to the square; on the comb unit masses force `Λ` | [L*] |
| Q7 Normal direction of the diagonal | none in characteristic zero in the square | [L] |
| Q8 A duality exchanging contacts and jets | none | [L] |
| Q9 Weil's diagonal as a finite part | on combs of degree points, with the comb's counterterm; the constant `2π` is forced: no larger constant, and every smaller one is the same statement | [L*]/[S] |
| Q10 One object | the real algebra `𝒮_q`: stable under every shift, containing the tower, the pole plane and the jets, with exact counts | [L*] |
| Q12 The comb | the density of the comb at the point; a separated comb stable under the Frobenius monoid is one orbit | [L*] |
| Q13 Carries | a cocycle that is not a coboundary; complementary to the window count | [L*] |
| Q14 The additive datum | the comb of unit masses: `w=Λ` | [L*] |
| Q17 Number rings | quadratic rings: contacts `Λ(1+χ)` on the comb of norms, counterterm `log(qn²/(2π)²)`, pairing `2d₁d₂−Z_ζ−Z_χ`; the class group does not enter; for a complex place the jets are `1/|m−n|` | [S] |
| Q18 The two-block face | one inequality per prime on the comb, on logarithmic windows with exceptions | [L*] |
| The statement over a curve | the comb `q^ℤ`; a Toeplitz form; purity is its sign; no jets and no counterterm | [S] |
| What the sections certify | the contacts below; one contact per prime above; no prime powers above; no jets | [L*] |
| Q11 Bézout | `CombBezout Λ` ⇔ RH; a theorem on packets of width `≤181/250`; at every scale on windows of ratio `≤19/18`, where it holds for every weight system | [L*] |

**State of the constructions.**
| Construction | State |
|---|---|
| A. Frobenius lifts (the Stepanov side) | closed: cost `m·θ(S)` [L*] |
| B. Carries | closed: a nonzero class; an identity with the window count [L*] |
| C. The surface (the Weil side) | the invariant glued carrier is refuted; survivors: comb finite parts, the weighted covariance, the scattering tower, the clock [L*] |
| D. The archimedean fibre | weight lines; each weight a Hardy square; the Newtonian reading on an axis [L*]/[D] |
| E. A second dimension | the tower of lines; Riemann–Roch with the gluing index; Bézout on it is the product formula; sections pay one contact per prime [L*] |
| F. The lattice | one matrix at finite scale; short windows negative definite and blind to the contacts; finite index; Hodge index ⇔ RH; no positive margin; any uniform floor is RH [L*]/[S] |
| G. Number rings | squares indexed by ideals; the quadratic comb with its twisted part [L*]/[S] |
| H. Curves | the Toeplitz comb; finite determinacy [S]/[L*] |

**Criteria the construction must meet.**
1. Reproduce Weil's and Stepanov's proofs for curves; over `𝔽_q[T]` there are no carries, no jets and no counterterm.
2. Counts alone are not enough: the golden datum has integral counts and a negative divisor [S].
3. Use the FE and the Euler product: the integer-norm one-off, the `cosh` models and the heat family must fail.
4. Infinite type: no finite fibre.
5. The diagonal is the density of a comb with the constant `2π`.
6. Positivity is derived, and sections do not derive it.
7. The statement lives at finite scale on real divisors, is selective only on windows with a contact, and has no margin.
8. Applied to the square of a quadratic ring it gives the index of the twisted part, or it uses the pole plane.

**Questions the programme must answer.**
- Q11 Bézout for the comb pairing (RH).
- Q15 The full window at finite scale (B152); the converse (A80).
- Q16 The fibre: a positive divisor in whose gauge the potential is nonnegative; for the flat tail it is the remainder of the prime number theorem.
- Q19 The Li ladder as the comb form on a sequence of tails (A82).
- Q20 **An object whose functions pay every contact.** On `𝔾_m` over ℤ the cyclotomic divisors `Φ_n=0` have `log|Res(Φ_m,Φ_n)|=φ(m)Λ(n/m)` for `m|n`, `m<n`, and `Λ(n)=log Φ_n(1)` [C]; the ring is factorial, so a function vanishing on `Φ_{p^j}=0`, `j≤J`, has the value `p^J` at `1`: every upward contact is paid [C]. Its degree points have the masses `φ(n)`, its archimedean pairing is logarithmic, and with the standard metric its pairing is the product formula. The square is its quotient by the Galois action, where the masses are units and the certification is lost [L*]. Which datum between the two carries unit masses and paid contacts?
- Q21 The exceptional square on the squares of quadratic rings (B154).
- Q22 The genus function and Riemann–Hurwitz for the counterterm; rings of higher degree and their isotypic parts (A91).
- Q23 A square for some weights: the feasible set `𝒜(a)` as the set of squares with the jets and the counterterm of ℤ; its points other than `Λ` at finite aperture (F20).

**Tools.** Witt vectors and Λ-structures; necklace coordinates and gluing indices; comb finite parts and the normal form; Hardy squares; block Schur tests; the carry cocycle; the index law; combs of norms.

**Milestones.** M1 [L*] questions Q1–Q10. M2 [L*] the comb pairing, the comb, the carries, the additive datum. M3 [L*]/[S] the finite-scale theorems, curves, quadratic rings, the forced constant. M4 an object with paid contacts and unit masses (Q20). M5 the exceptional square (Q21). M6 Bézout (RH).

## 3. The one big question: can the exceptional square be removed?

**Why the question is not about ζ.** The decisive radius of the minimal face is settled at the level of configurations (B143); its refinement in ζ's class is a transport of a law that exists on the aperture side (B151, A92). The critical curve has one undecided case (B104) and AAL one sector off the RH path (B141); both are stated in §2.4 and §2.5 and neither produces a sign. Every other structural question generated for this report is decided in Lean (§1.15). The corpus has receivers in every language and no producer, and no statement about ζ below AAL passes the tests as a door. The smallest unsolved instance of the missing sign lies in an object that the corpus has built: the twisted part of the square of a quadratic ring.

**Question (B154).** Let `χ` be a real primitive character of conductor `q`, and `Z_χ` the form of the twisted part: jets, the counterterm `log(qn/2π)` and twice the contacts `Λχ`, on packets in a window of aperture `a` [S]. *Is `Z_χ≥0` on windows of aperture `log log q+C`, for every `C` and all large `q`?*

**What is proved.**
- The twisted part tends to minus the sum over the zeros of `L(s,χ)`, has no pole plane, and its counterterm is that of a comb `q` times as dense as the integers; the class group does not enter [S]. GRH for `χ` is a prime-window statement of the same shape as for ζ [L*].
- The defect of the pairing of the ring has at most as many negative squares as ζ and `L(s,χ)` together have zeros right of the line; on packets shorter than `log 2`, for an odd character of conductor `q≥4π` or an even one of conductor `q≥128π`, the twisted part is nonpositive and Castelnuovo–Severi holds on the square of the ring with the margin `∫f²/5000` [S].
- For a real zero of a primitive quadratic `L(s,χ)` repulsion holds with a uniform constant [L*].
- *Trivial aperture* [D]. The contact term of a packet of aperture `a` is at most `2Σ_{n≤e^{2a}}Λ(n)n^{−½}≤(4+o(1))e^a` times its mass, and the archimedean term is bounded below; hence `Z_χ≥0` whenever `4e^a+C₀≤log q`, that is to aperture `log log q−log 4`.
- *One square* [D]. A real zero `β` and its reflection contribute `2f̃(β)f̃(1−β)` with `f̃(s)=∫f(u)e^{(s−½)u}du`; over packets of unit mass on `[−a,a]` the minimum is `−(sinh(2da)/d−2a)`, `d=β−½`, of the order of `−e^a` for `β` near `1`. It is one negative square of `Z_χ`.
- *Where it shows* [A]. On the minimizing packet the zeros on the line contribute about `log q` times the mass; the square is visible when `e^a` exceeds about `log q`, at aperture about `log log q`. The gap to the trivial aperture is about `log 4`: a factor `16` in the ratio of the window.
- For ζ itself the corresponding world is empty for an elementary reason: ζ has no real zero in the strip, so the index of its pairing is even.

**What either answer gives.**
| Answer | Effect |
|---|---|
| A mechanism of the corpus proves the sign at aperture `log log q+C` | exceptional zeros do not exist; the mechanism is a producer of the missing sign at unbounded scale in the conductor aspect, the first in the corpus, and the route that owns it is a route |
| Each sign mechanism is shown to stop at the trivial aperture on the ladder | the Σ routes are receivers in the conductor aspect as well: comb finite parts, regulators, the critical curve, the clock, the count door and the index law are tested on one square without touching RH, and the test is a theorem per route |
| The gap is closed from the other side by a model | an object with FE, Euler product, integer norms and a ring behind it with one positive square: the calibration that the corpus lacks, since ζ admits no deformation |

**Why this question.** It is the same matrix as for ζ with one change, the conductor in the counterterm, and one simplification, no pole plane. The number of squares to remove is one, the gap is a bounded number in aperture, and the range below the gap is a theorem. Every criterion that a producer must meet for ζ (§2.9) can be checked on it. Classical Deuring–Heilbronn is its repulsion theory, and its physical and geometric readings are in §2.7 and §2.8.

**First step and obstacle.** Prove the trivial aperture and the one-square computation in Lean on the twisted comb (A100); state classical repulsion as a margin on the remaining squares (A101); run the proved window theorems of ζ — the margins at width `181/250`, the short-window floor, the finite index — on the twisted part with the conductor explicit. Named obstacle: the trivial bound uses the absolute values of the contacts; passing `log 4` needs the signs of `χ` at the primes below `(log q)²`.

**Tests.** T1: fails in the strict sense — the statement is implied by GRH for `χ`, is independent of RH for ζ and implies no width for ζ. T2–T4: pass. T5: calibrated on curves, where the twisted parts of a cover are negative definite by the Hodge index of the covering surface. T6: not refuted. T7: moves Σ156, F22. T8: fails — it is the Landau–Siegel problem in the form of the comb; it is posed because it is the smallest instance of the wall and the only one with a bounded gap.

**Limit.** It decides whether the corpus contains a producer; it does not prove RH.

### Alternatives considered
| Question | Effect | Verdict |
|---|---|---|
| Polar orthogonality (B104, §2.4) | the critical curve becomes one inequality | passes; produces no sign |
| Deuring–Heilbronn for ζ (B141, §2.5) | AAL reduced to the RH path | passes; no model with both structures to test a mechanism |
| Almost periodic constituents (B153, §2.6) | every exact arithmetic constituent excluded, or a pure infinite subset | passes; decides constituents, not zeros |
| The prime-side resolution law in ζ's class (B151) | the last parameter of the receiver of the minimal face | a transport of the aperture-side law; first statements A92 |
| The full window at finite scale (B152) | the Hodge index on real vectors | RH at all ratios |
| An independent family of bounded index (B146); Bézout for the comb pairing (B149); a unitary regulator (B117); feasible weights at every aperture (B18) | RH | producers of RH strength |
| Depth density `o(T)` (B57); bounded form factor (B150) | first unconditional near-line inputs | census problems |
| `Θ<1⇒Θ=½` (B56); the transfer of S3 (B148); the signed centred type-II current (B145) | AAL and more | fail T1 |
| Finite stratum (B13); landing as an atom (B138) | atoms of the RH path | B13 fails T8; landing has no first step |
