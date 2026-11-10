# Obstacles summary — status quo

Companion to [route-obstacles.md](route-obstacles.md) (per route), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ) and [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem). Corpus checkpoint: commit `5bebbe1136` with its working tree (2026-11-10). Working log: `logs/review-1011-frontier-facts.md`.

**Evidence.** `[L*]` Lean statement read for this report (source or corpus search tool); `[L]` recorded as integrated Lean in the frontier map, the scoped-obstruction ledger or a programme table of `formal/`, not re-read; `[S]` Lean source present, graded unfinished or unintegrated by the frontier map or untracked in the working tree, statement read; `[K]` Lean with transitive axiom audit as recorded; `[D]` deduction made here from `[L*]`/`[S]` statements; `[C]` classical, not in the corpus; `[A]` assessment. Sections 2.3–2.14 and 3 are interpretation and ideation: every untagged statement there is a proposal, not a result.

**38 live formulations; 12 candidates** (SEC, CDC/BSH, S3, APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF). HJ is PA; PCS is a retired label.

**Notation.** `Θ=sup Re ρ`; `Θ∞=inf{σ≥½: finitely many zeros have Re ρ>σ}`; **ZAL** `Θ∞=½`; **AAL** `Θ=Θ∞`; **B13** finitely many off-line zeros ⇒ none; **Landing** ZAL ⇒ finitely many off-line zeros; **DH** ¬AAL ⇒ ZAL; **B56** `Θ<1⇒Θ=½`. `c_B` the orbit correlation of the cubic spline, `c_p=c_B(log p)`, `c_B(log d)=A(d)−P(d)` with `P(d)` the smoothed von Mangoldt count in the window of `d` and `A(d)` its archimedean-plus-pole prediction. A **logarithmic window** at `T` is `{p: |log p−T|≤32 log(T+2)}`. **World I** ¬AAL; **world II** AAL ∧ ¬ZAL. **`𝒵(γ_min,C)`**: tempered reflection-symmetric zero configurations without real zeros, lowest ordinate `≥γ_min`, `N(t,t+1)≤C log(|t|+3)`. **`𝒵₀`**: the configurations of `𝒵` whose zeros of depth `≥d₀` number `o(T)` below height `T`, for every `d₀>0`. `𝒢=W(ℤ)` the arithmetic square, `Γ_n` its graphs, `J(m,n)` the ideal of `Γ_m∩Γ_n`. **Comb pairing** of a real divisor `D=Σc_nγ_n` on a finite set of degree points: `Γ_m·Γ_n=½(1/|m−n|+1/(m+n))+Λ(n/m)` off the diagonal, `Γ_n·Γ_n=−log(n/2π)`; degrees `d₁=Σc_n/n`, `d₂=Σc_n`; **comb form** `2d₁d₂−D·D`. `E_r` the arithmetic-clock Green energy. A **heavy return**: a `δ`-return, `δ≤1/20`, of a subset of the primes `≤y` omitting at most `1/1000` of the `p^{−1/2}`-mass.

## 1. Big picture

### 1.1 One inequality per prime; its resolution is logarithmic in the class `𝒵`
RH ⇔ `∃K`: `2c_p≥−K` at every prime ⇔ `P(p)≤A(p)+K` ⇔ Weil positivity of the two-bump `B+τ_{log p}B` at every prime [L*] ⇔ every effective prime class carries an `ℕ`-count with Tate limit `δ_p(1,1)` [L].

| Sample | A one-sided bound gives | Evidence |
|---|---|---|
| all primes; any power-saving gap set | RH | [L*]/[L] |
| primes of arbitrarily late `r√T` windows; two-prime difference lags in such windows | RH; on such windows every tempered configuration without real zeros is decided | [L*] |
| primes of arbitrarily late logarithmic windows `\|log p−T\|≤32 log(T+2)` | RH; width `≤α` from the floor `−Kp^α`; a power saving `α<½` ⇔ quasi-RH; absolute form equivalent | [L*] |
| the same windows, outside at most `Ce^{δT}` primes per window, `δ<1`, chosen freely per window | RH; width form; Stepanov form `P(p)≤A(p)+Kp^σ` | [L*] |
| windows `T≤log p≤T+80/δ+1`, if the deep ordinates are `δ`-separated | width bound, from below or from above | [L*] (conditional on the separation) |
| windows of unbounded radius (any Bohr-dense set) | an attained top lies on the line: world I is excluded | [L*]/[L] |
| windows of radius `R(T)→∞`, `R=o(log T)`, in the class `𝒵(γ_min,C)` | nothing: one configuration with unattained top `½+Θ` passes every floor, also at the prime logarithms; `R` is built with the configuration | [S] |
| windows of any fixed length, in the class `𝒵(γ_min,C)` | nothing: one configuration passes every floor on windows of every length | [S] |
| primes off a density-zero set; very smooth degrees; finitely many Frobenii | nothing without attainment; with ZAL, RH | [L*]/[L] |

If RH fails, every sufficiently late logarithmic window holds a violator of every floor outside every set of `Ce^{δT}` primes [L*]. Unconditionally the error has the Vinogradov–Korobov saving [L].

**The counter-configuration is not in ζ's class [D].** Its level `k` consists of the ordinates `d/(4(k+1))`, `4(k+1)Γ_k≤d≤8(k+1)Γ_k`, each split into two simple zeros at distance `O(1/T_k)`, all at one depth `x_k` [S]: at least `8(k+1)Γ_k` zeros of real part `½+x_k` with ordinate in `[Γ_k,2Γ_k+1]`. For ζ the zeros of depth `≥d₀` below height `V` number `o(V)` for every `d₀>0`, and at most `T^{(30/13)(1−σ)+ε}` lie right of `σ∈[½,5/6]` [L*]. The low off-line pair, the only other corpus counterexample to short windows, violates the lowest ordinate. The decisive radius in the subclass `𝒵₀`, to which ζ belongs, is open (B151, §3).

### 1.2 Two worlds, three atoms
`Θ<1 ⇔ Θ∞<1`; ¬AAL ⇒ `Θ<1`; failure of quasi-RH forces `Θ=Θ∞=1` and AAL [L*]. A failure of RH lies in exactly one of two worlds [D]:

| World | Description | Proved inside it |
|---|---|---|
| I: ¬AAL | a finite isolated top layer at `β<1` over a remainder `≤Θ∞<β` | zero-free strip; `M(x)=O(x^{β′})`, `β′<1`; heavy returns later than `exp(c·y^{1−β″})`, `β″<Θ`; a complete finite-layer receiver; a floor on windows of any unbounded radius fails [L*] |
| II: AAL ∧ ¬ZAL | `Θ=Θ∞>½`: the top is approached by infinitely many zeros | the receivers; at the level of `𝒵` it passes every floor below the logarithmic radius [S] |

RH ⇔ ZAL ∧ B13 ∧ Landing; AAL ⇔ B13 ∧ Landing ∧ DH; a failure of the abscissa law fails exactly one of B13, Landing, DH [L*]. Landing is a tail law, undecided below every height; an FE model with approaching quartets and a positive integer-norm Euler product with approaching remainders both violate it [L*]/[L]. Classical Deuring–Heilbronn holds for a real zero of a primitive quadratic `L(s,χ)` with a uniform constant; graded repulsion is refuted on integer-norm Euler products [L*].

To prove AAL one may assume quasi-RH: AAL ⇔ (`Θ<1` ⇒ AAL) [D]. B56 implies AAL [D].

### 1.3 The finite-layer receiver is complete; the gap is the exclusion
In world I, for every top zero `ρ` at `β` and every observation line `σ<β` [L*]:
- prime-only damping filters read the divisor at every damping speed; with polynomial contraction the complete prime filter has growth, a positive finite critical modulus and decay according to the exponent; AAL, or top zeros supply prime filters with a fixed positive critical modulus;
- the top has two distinct positive ordinates, or the corrected current diverges at every damping `a` with `a(β−σ)>π/2`; a dominant ordinate forces the divergence;
- for every moment order `r≥1` the Gaussian prime moment minus its pole is the centred Vaughan current up to `O_r((1+1/η)/t)` on admissible cutoffs; truncating cofactors changes the current by exactly the complementary convolution, both continuum terms kept; the filtered cofactor reduction error is `O(h^k/t)`;
- at `σ=½`, `X=e^{at}`, with moment order `r log t≍κt`, `κ≤a/32`, the unfiltered reduction error is `≤C(1+t²)(1+at)e^{−(3a/8)t}`, and with `UW≥Xt²` the discarded cofactor tail is `≤784e^{−t²}`: the centred current restricted to at most `3t^{J+3}` cofactors differs from the prime moment minus its pole by at most `Ce^{−(a/4)t}`; only the cofactor is truncated, the long prime variable and both continuum terms remain [S];
- for `½≤σ≤5/6` and `c>(30/13)(1−σ)`, `T^c` one-separated returns to every small disc at a zero right of `σ` exclude it.

The growth range and the Vinogradov–Korobov decay range are separated by `a(1−β)/2`. An arithmetic upper bound for the signed centred type-II current at a growing isolated mode beats the trivial bound of a prime sum of length `e^{at/2}` at height `t` by the power `1−β`: it is the exclusion of the layer (B145) [D].

### 1.4 Rigidity: ζ has no moduli, and a family sees only its variable part
- A Dirichlet series with ζ's FE is a multiple of ζ; a countable Beurling system with an `L¹` or `L²` FE defect is the rational primes; count distance `o(log n)` forces the rational primes [L].
- A gauge fibre with a nonzero analytic residue at `1` is `ζ·exp(H)` left of `1` [L]. For every analytic profile `Φ`, unimodular on `[0,1]`, `Φ(0)=1`, `Φ(1)=−1`: the fibre keeps every multiplicity of ζ on `Re s>max(½,1−mt)`, no function analytic at `(t,s)=(0,1)` regularizes the family, the fibre rescaled at `s=1+tw` over `t²` converges to the zero-free non-polynomial profile `ζ(2)exp(−Σc_{n+1}log(w+n+1))`, and an entire scaling profile forces `Re Φ′(1)≤−2` [L*]. The `χ₄`-selected pair of profiles has a zero of order four at `1−2t` and a double pole at `1−4t`, with scaling limit `ζ(2)(w+2)⁴/(w+4)²` [S]: the singularity is delayed, not removed.
- Fixed part: for every finite measure on the gauge torus and every continuous amplifier the moment is at least the atom at the trivial fibre times the trivial bound; amplification beats it strictly at a nontrivial torsion fibre; product positivity passes from base to product and not back; the trivial fibre has mass zero or tending to zero in the five canonical family classes; with the trace of ζ retained, sublinear tensor growth of a cover family ⇔ RH [L*]. The module does not classify every arithmetic family.
- The Eisenstein line law holds over every symmetric fixed part in the closed strip: the purity of all members of a family is the closed strip of its fixed part, never its line [L*].

Consequences [D]: Deligne's family step has no producer among these families; no fake keeps Euler product, FE and coefficient size and moves a zero.

### 1.5 The off-line zeros have no arithmetic constituent
A function given by an absolutely convergent Dirichlet series, bounded and holomorphic on `Re s>x`, whose zeros there are zeros of ξ, has all its zeros there on the line: a zero recurs along a relatively dense set of shifts (Bohr), while off the line the shifts that carry a zero of ζ near `ρ₀+iτ` have density zero [L*]. A Dirichlet polynomial with a constant term whose zeros lie on the line satisfies `|D(1−s̄)|=N^{Re s−½}|D(s)|`, `N>1`; a Dirichlet polynomial with a constant term and such a functional equation has a zero that is not a zero of ξ [L*]. Hence no Dirichlet polynomial with a constant term, none whose lowest frequency divides the others, none in one base and none with two terms has all its zeros among those of ξ [L*]. If `−Gζ/s` is holomorphic in the strip and bounded near the line, with a generalized Dirichlet expansion `Σb_ia_i^s`, `0<a_i≤1`, right of the line and `Σc_jq_j^s`, `q_j≥1`, left of it, the constant terms on the two sides agree, by the jump of the fractional part [L*]. Polynomials without constant term on several bases, partial common zeros and approximation are not covered.

### 1.6 Exactness over ℤ has an exact price
`x↦xⁿ` is additive in characteristic `q` exactly when `n` is a power of `q`; `Λ(n)` is the `log q`-weighted number of primes at which `F_n` is a Frobenius [L*]. Order `m` of the Fermat-quotient derivations at every prime of `S` costs `log|a|≥m·Σ_{p∈S}log p`, attained by `Πp^m`; `ℤ` has no ring endomorphism but the identity [L*]. The minimal fixed-point auxiliary has log length `ψ(N)`, and RH ⇔ `ψ(N)≤N+C√N log²N` [L*]. On the tower of lines a nonzero section vanishing on `Γ_1,…,Γ_K` exists by a count whose second term is the gluing index `K!`, and its first nonvanishing graph gives `n≤|x_n|`: Riemann–Roch and Bézout hold there and their conclusion is the product formula [S]. The carry is a cocycle that is not a coboundary, in digit and in Witt form; the carry defect and the window-count defect are complementary up to `½log(πN)+o(1)`, so a bound for one is a bound for the other [L*]. At one prime Stepanov's method runs on the first Witt carry: the fibres of the truncated logarithm over `𝔽_p` have at most `100p^{2/3}` points and `|Σ_{n≤p}e(an^p/p²)|≤5p^{11/12}` [L*].

### 1.7 The square of Spec ℤ is a curve; its pairing has a Hodge index theorem equivalent to RH
- **Contacts and jets.** `Γ_m·Γ_n=Σ_{j≥0}m^{1+2j}n^{−2j}+g·log#(ℤ/J(a,b))`; `log#(ℤ/J(1,n))=Λ(n)`; no Witt Verschiebung carries the off-diagonal [L*].
- **No finite type.** The fibre of the square over `p` is infinite; a ring with Frobenius lifts, a ℤ-point and a finite fibre has a contact that is not Weil's; a perfect square keeps no contact [L*].
- **One ring.** The real algebra generated by the orbit ring with a base, `χ_1` and `τ` is stable under every shift and contains the tower of lines, the pole plane and the jets, with exact counts on every weight line [L*].
- **The pairing weighs the zeros.** On packets the pairing of the degree points tends to `2d₁d₂−Z(f)`; twice the contacts tend to the pole and archimedean part minus `Z(f)`; `Z(f)≥−D(f)` with `D≥0` supported on the off-line zeros; RH ⇔ `D≡0` [L*].
- **Hodge index.** On every finite family of packets the defect `2d₁d₂−D·D` has at most `#{ρ: Re ρ>½}` negative squares; RH ⇔ the intersection form on `H,V` and every finite family of packets has exactly one positive square [S].
- **The sign is carried by the contacts.** Packets of width `≤181/250`, of any sign, satisfy the inequality with margin `∫f²/5000`; every positivity certificate at aperture `a` transports to packets of length `2a` [L*]. Comb Bézout with weights `w` ⇔ RH ∧ `w=Λ`; a weight differing from `Λ` at one integer fails on some packet without hypothesis; with `−log 2` at `k=2` some packet exceeds `2d₁d₂` [L*]. Unit masses on the integers force `w=Λ`; an excess `Σ(w(k)−Λ(k))/k>1+γ/2−½log 4π` of contact mass makes the flat tail violate the inequality at every large scale [S].
- **Finite scale.** In the coordinates `c_n=f_n/√n` the pairing is one matrix on the integers with no scale in it. On `S⊆(N,N+M]`, `18M≤N`, every real divisor has `D·D≤−(1/40)Σc_n²` and comb form `≥(1/50)Σc_n²`. For every ratio bound `Q` there is `R` such that at every scale `N≥R` the comb form is nonnegative on the real divisors of `(N,QN]` whose sums over blocks of `⌊N/R⌋` points vanish; the blocks are fewer than `2QR` [S]. If for every ratio and every `η>0` the comb form is `≥−ηΣc_n²` on every real divisor of the window at arbitrarily large scales, RH holds; if RH fails, some ratio has, at every large scale, a real divisor with `Σc_n²≤C` and comb form `≤−ε` [S].
- **The potential is the prime number theorem.** In the gauge of the flat tail the potential at `n` is `N/n−ψ(N/n)+H_N−½(H_{N−n}+H_{N+n})+3/(4n)−log 2π`; `Σ_{n≤N}ψ(N/n)=log N!` is the contact energy of the tail; the form of the flat tail per degree point tends to `2+γ−log 4π`, twice the first Li coefficient [S]/[D].
- **Diagonal.** The counterterm is the logarithm of the density of the comb at the point; between two combs the pairing changes by the mass times the logarithm of the ratio of the densities [L*]; on the comb of squares, which is not a dilate of the integers, the counterterm is `log(n/4π)` and the pairing is twice the form on the integers plus a continuous kernel plus `2 log 2` times the mass [S]. A uniformly separated comb stable under every multiplication `x↦kx` is one orbit `δℕ` of the Frobenius monoid: up to the torus the comb of all degree points is the only separated comb that carries every contact from one point [S].
- **Weights under scaling.** Tested against a packet at the scale `e^a`, the contact weights are `e^{∓a/2}` for the pole plane, the jets against the symbol of the Gamma factor, and `−m_ρĝ(γ_ρ)e^{(ρ−½)a}` for every zero; pointwise the shifts of the point count span every finite set of degrees and distinguish nothing [L*].
- **Counting.** The gluing index of the first `N` graphs is `N!`; `G(T)−N(T)+S(T)→½log 2π−7/8` and `G(T)−N(T)` is unbounded around that constant [L*]. The prime polynomial of a window at a height is the contact weights at that height, and contacts plus the off-line correction minus the smoothed increments of `S` tend to `0` [S]: the gluing conditions are the archimedean count and the contacts are the remainder.
- **Number rings.** For a Dedekind domain the square is indexed by the nonzero ideals; the diagonal and `Γ_{𝔭^j}` meet in `Spec R/𝔭`; the necklace coordinate at `𝔡` is the ideal `𝔡`; an orbit exists iff `𝔡` is principal [L*].

### 1.8 The adelic carrier: a Green pairing off the diagonal, no glued diagonal
Every adelic-invariant kernel with a torus-orbit functional has a constant degree diagonal and its dyadic pairing with Weil's off-diagonal tends to `−∞`; no scalar counterterm removes the jump `−2‖g‖²log p` between `p` and `p³` [L*]. The weighted mixed hyperbolic Green kernel converges absolutely over the rational torus on every pair, descends symmetrically, has stabilizers `±1` and a leafwise Robin finite part; its spherical average at parameter `½` is integrable at every pair of finite vertices and equals the minimal Green kernel of the all-prime weighted adjacency [L*]. None of these identifies Weil's degree diagonal [L]. Weil's functional on packets is the limit of Robin-normalized Maass–Selberg diagonals, independent of the centre of the packet [L*]. The arithmetic clock gives `0≤W−E_r≤(1−r²)‖f′‖²/2` uniformly on a support window; the damped form has a finite limit exactly on the closed Weil form domain; the coercively shifted damped inverses converge strongly to the restricted Weil covariance [L*]. RH ⇔ `E_r(f)≥−(1−r²)‖f′‖²/2` near `r=1` on every packet [D].

### 1.9 The window sign is verification height; the critical curve has one undecided case
RH ⇔ `Ψ` locally bounded on precontact intervals [L*]. `RHVerifiedThrough(windowHeight a)` gives the sign on `[−a,a]`; RH is verified through 67 [L*]; window positivity at `a` bounds the pair energy of every off-line site by the cell count of its sea [L*].

At the critical curve `R_c=R_polar=R_halfline≤W₀`; the complete matrix is positive ⇔ the primitive hyperplane is ∧ the pole channel is; `R_c=W₀` ⇔ the pole channel is eventually positive at every ratio below `W₀` [L*]. Exactly one of: RH; ¬RH and `R_polar<W₀`; ¬RH and `R_polar=W₀` finite with every critical half-line ground state polar-orthogonal [L*]. The third case is undecided (B104).

### 1.10 Index, limits, flow and separation
A Hermite–Biehler defect of degree `κ` has at most `κ` exceptional points, and `cosh` models attain every index; the bound passes to locally uniform limits; RH ⇔ ξ is a limit of conjugation-real entire functions with at most one right-half zero each [L*]. The cleared Eisenstein constant term has all zeros on the line for `1≤Y≤4πe^{−γ}` and one real exceptional pair above [L*]. On the flow a locally finite summable module is determined by its trace, and Castelnuovo–Severi on every divisor of Frobenius graphs ⇔ pure and effective ⇔ positive definite central trace; for the zero motive ⇔ RH [L*]. RH ⇔ the ordinate is injective on the zeros ⇔ `|c_p|≤K` at every prime [L*]. No vertical progression consists of zeros, at any real part; each half progression contains non-zeros at arbitrarily large index and no sequence of zeros is eventually within an `ℓ²` perturbation of one [L*].

### 1.11 The horizon has complete and sharp receivers
RH ⇔ every compact pulse rings down at `e^{−(¼−ε)τ}` ⇔ every tent reflection Krein form has negative index `0` ⇔ one cavity energy of Hecke forms decays at `y^{¾−ε}` [L*]. For one Hecke eigenform: RH ⇔ sharp rate ∧ no nonhalving Shimura zero [L*]. RH ⇔ an `ℕ`-valued count with Tate limit the integer probes exists [L*].

### 1.12 The dark range and the returns of the prime orbit
Heavy returns do not occur while `log t≤(log y)^{3/2−ε}` [L*]; a strip of depth `h` gives `log t≥c·y^{½−h}`; two-prime returns obey Baker's depth law [L]; return bounds are statements about the labels: a route from them to ZAL uniform over a class containing `ζ(s−h)` refutes the return conjecture [L*]. The transfer of candidate S3 implies B56, hence AAL, and its hypothesis is implied by quasi-RH [D].

### 1.13 Law and point
Past the Vinogradov–Korobov region every unconditional theorem of the corpus about the zeros is in law: density exponent `30/13`, deep zeros `o(V)`, off-line second moment `o(V)`, Matomäki–Radziwiłł for μ, critical-line density `0.67250071`, typical-height signs [L*]/[L]. On the prime side a zero is visible at every scale, so power-thin exceptional sets of primes are harmless; on the height side a zero is one point [D]. One law statement has entered a pointwise theorem: the density-zero law of the deep zeros proves the purity of every bounded Dirichlet-series factor (§1.5).

### 1.14 The Mertens level in several geometries
Producer rates, Farey discrepancy, the nerve, the prime-vertex indices, the gluing quotient and the centred count of the orientation cover over ℤ read `M(N)`; cover weight `½` ⇔ RH; rates `K^{−a}` for all `a<½` give RH; RH ⇔ either one-sided quarter-power law of the weighted squarefree count [L*]/[L].

### 1.15 What is ruled out
| Mechanism | Verdict | Evidence |
|---|---|---|
| A family (gauge twists, characters, vertical shifts, Hecke forms, covers, analytic prime smoothings and their mixtures) as a source of purity for ζ | fixed-part laws; isozeric deformations; moving branch; delayed pole | [L*]/[S] |
| A receiver below the logarithmic radius at the level of `𝒵` | block tower with unattained top | [S] |
| A bounded Dirichlet series, or a Dirichlet polynomial with a constant term, as an exact factor carrying off-line zeros or all of its zeros in ξ | factors are pure; forced FE; Herglotz series vanish | [L*] |
| One glued adelic-invariant carrier object with Weil's diagonal; the quotient Robin diagonal as Weil's diagonal | constant diagonal; drift `−∞`; discriminant jump | [L*]/[L] |
| A finite-type object with Frobenius lifts carrying the contacts | fibres infinite; forced wrong contacts | [L*] |
| A Frobenius for a window; cheap simultaneous vanishing over ℤ; Riemann–Roch with Bézout on the tower as a producer | one prime per power map; cost `m·θ(S)`; product formula | [L*]/[S] |
| The carry as a bound for the window count; removing carries by a choice of section | complementary identity; nonzero cocycle class | [L*] |
| A diagonal entry attached to a degree point; one counterterm across combs or scales | the counterterm is the density of the comb | [L*] |
| Other contact weights with the same jets and counterterm | Bézout on the comb selects `Λ`; unit masses force `Λ` | [L*]/[S] |
| Pointwise closure of the shifts of the point count as a selector of the zero weights | the shifts span every finite projection | [L*] |
| The gluing count as a count of zeros at a height | misses by the unbounded remainder `S` | [L*] |
| Integral or trace-class Frobenius modules for the zeros; a class or half class of one Frobenius among the zeros | Tate twists only; divergent ladders | [L]/[L*] |
| Purity of a fixed part from the line law of its family | holds over impure fixed parts | [L*] |
| Separation of the zeros by absolute value (coefficient gaps) | three critical ordinates in a dyadic range | [L] |
| The transfer of candidate S3 as a method question; the clock energy as an independent producer | implies B56; `E_r≤W` | [D]; [L*] |
| A fixed window length uniform over tempered configurations; density-zero exceptions without ZAL | low off-line pair; unattained tops | [L*] |
| Landing from the FE alone or the Euler product alone; graded repulsion from Euler products | models | [L*]/[L] |
| Euler-region or VK bounds for filters as exclusion of a finite layer | ranges separated by `a(1−β)/2` | [L*]/[L] |
| One Hecke eigenform as a complete receiver without side condition | halving pairs; Shimura zeros | [L*] |
| Markov, Perron, size-only payment, floor tower, universal holomorphic multipliers, fixed theta heads, positive Laplace mixtures | refuted or bounded | [L] |
| Positivity, Euler products, integrality, linear counting, continuation, reflection, positive Hecke and two-prime polynomials as any atom | one-offs and annihilators | [L] |
| Schur, `C*`, KMS, internal modular conjugation, half-sided inclusions as zero locators | blind or excluded | [L] |
| Bounded-height Diophantine certificates against returns; return bounds as uniform routes to ZAL | Kronecker-scale cap; label statements | [L]/[L*] |

## 2.1 Tasks that are just work

Difficulty is established only where a known argument exists; `(unverified)` marks the rest. None of these decides RH.

### Assemblies of proved pieces
| # | Task | Routes | Basis |
|---|---|---|---|
| A72 | Count door on logarithmic windows with exceptional sets | ACS, HF, PM, SRT | `riemannHypothesis_iff_prime_logarithmic_windows_off_finset`; the count gives the floor |
| A73 | One-sided upper side (`2c_p≤K`) on logarithmic windows (unverified) | SRT, ACS | `exists_bddAbove_exp_windows_of_prime_windows` |
| A75 | Lean form of "the transfer of S3 implies `Θ<1⇒Θ=½`" | BAG, S3 | heavy returns in a strip; logarithmic-window criterion |
| A76 | Exceptional sets in the absolute and signed window criteria (unverified) | SRT, ACS, CDGeo | `zeta_re_le_iff_abs_prime_logSquare_power_windows_signed`; `prime_power_windows_transfer_off_finset` |
| A71 | Local tensor moments: uniform-in-`k` moments of `c_B` over the primes of late windows ⇔ RH [D] | ACS, AWT | window criteria with exceptional sets |
| A56 | Explicit rung: `RHVerifiedThrough T` ⇒ the two-bump sign for all `p≤P(T)` (unverified) | SRT, ACS | supports of the two-bump tests |
| A78 | Cluster form of the separated-window theorem (unverified) | SRT, ACS | `re_le_of_bddBelow_exp_windows_of_separatedOrdinates` |
| A79, A81 | Matching constants in the aperture–height exchange; the block constant `R(Q)` and the index bound `2QR(Q)` against the visibility height (unverified) | RW, ACS | `windowPositiveAt_of_rhVerifiedThrough`; `exists_blockSize_combForm_nonneg`; visibility laws |
| A80 | Finite-scale rung: `RHVerifiedThrough(H(Q))` ⇒ comb form `≥0` on every real divisor of `(N,QN]`, `N≥N₀(Q)` (unverified) | ACS, HF | the block decomposition; `tendsto_combForm_sample`; the window rung |
| A82 | The Li ladder as comb forms of tails: the flat tail gives `2λ₁` [S]; identify `λ_n` with the comb form of the `n`-th tail (unverified) | LI, ACS | `tendsto_combForm_flatTail_div` |
| A83 | Density-matched counter-configuration: an on-line background of ζ's density changes the trace by a bounded amount [D] | SRT, ACS | summability of the spline weights |
| A87 | The comb form on two-block divisors: two short blocks at scales `N` and `pN` reduce to the Stepanov bound at `p` [D] | ACS, SRT | `riemannHypothesis_iff_weil_primeTwoBumps`; `tendsto_combForm_sample` |
| A90 | The flow criterion in prime form: RH ⇔ the lag function is positive definite on `ℝ` [D] | WL, ACS | `castelnuovoSeveri_iff_positiveDefinite`; `zeroMotive_castelnuovoSeveri_iff` |

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
| A84 | Optimality of the greedy carry-free composition and the Newton polygon of the Carlitz–Goss zeta function [C] | sign-free calibration | `tokenPrefix_iff_inverseContent`; `exists_positive_cyclicDifference_content_iff` |

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
| A85 | Dirichlet polynomials without constant term on several bases as factors (unverified) | W1C, PM | `exists_zero_not_xi_zero_of_dvd`, `…_of_oneBase` |
| A86 | The transfer of the growing-order reduction through the top-mode filter (unverified) | ZCG, BAG | `norm_gaussianHigherCentredVaughanError_le_exponential`; `gaussianHigherCentredVaughan_sub_cofactorCurrent_eq`; filtered cofactor localization |
| A88 | A floor on a window of length `L` forces a deep neighbour within `O(1/L)` of every dominant deep ordinate (unverified); first step of B151 | SRT, ACS | deletion filters; positive-definiteness of nonnegative functions on a window |
| A91 | The pairing, the comb counterterm and the Hodge index on the square of a number ring (unverified) | ACS | `TheArithmeticSquareOfADedekindDomain` |

## 2.2 Open mathematical obstacles

### The common minimal face
| # | Problem | Strength | Routes |
|---|---|---|---|
| B130 | `P(p)≤A(p)+K` on a decisive sample: every prime, or the primes of arbitrarily late logarithmic windows off `Ce^{δT}` exceptions; any growth `Kp^σ`, `σ<½`, is a zero-free strip. Known: the VK saving | RH (≥qRH) | ACS, SRT, WL, HF, ZCG, HAT-C |
| B151 | **Resolution in ζ's class**: do bounded windows, or every unbounded radius, decide the class `𝒵₀` of configurations whose deep zeros have density zero (§3) | method | ACS, SRT, WL, HF, SOSZ |
| B144 | Separation of the off-line ordinates of ζ; gives bounded windows by `[L*]` | sub | SRT, ACS |

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Weil's sign on every window; equivalently `E_r(f)≥−ε` near `r=1` on every packet | RH | all sign routes, HAT-C |
| B152 | The comb form on a full window at finite scale: nonzero block sums and their cross terms, at every ratio. A lower bound `−ηΣc_n²` at arbitrarily large scales, for every ratio and `η`, gives RH [S]; the converse at a fixed ratio is A80 | RH; each ratio a finite-height statement [A] | ACS, HF |
| B2, B4, B5 | Bounded oscillation of `Ψ` to contact; outer predictors and Schur bands; kick admission | RH | RW, GWZ, WTZ |
| B6, B8, B101 | Full-space sign at every critical multiple; head thresholds; polar payment at every ratio | RH | HF, SRT, AIP |
| B104 | **Polar orthogonality**: can a critical half-line ground state at finite `W₀` be polar-orthogonal; equivalently for the third case, is the pole channel positive at every ratio below `W₀` (§2.4) | method | HF, SRT, AIP, ACS, SC |
| B123 | Correlated arithmetic pairings dominating the depleted kernel | method | HF |
| B9–B11 | No zero mode; top coprime stratum; exact SOS on a two-prime lattice | RH | HF, SC, ACS |
| B12, B14, B23 | Index ceiling uniform in resolution; any interior width value; `N_d` bounded | ≥qRH | CHMD, LA |
| B15 | Past Vinogradov–Korobov | sub | every route |
| B16, B17, B3 | Decay law of the margin; signed ground states past `log ρ`; variation of `r` free of `1/μ` | sub / method | CHT, RW |
| B18 | Prime-blind positivity on nonnegative blind mixtures | RH | RW |
| B19–B21, B102 | Torus law for `S*`; amplitude oscillation; all theta ranks; sign of the adaptive head near critical zeros | RH | TH |
| B22, B24, B25 | Outer roots of the Jensen polynomials; collisions at small time; frequency below one | RH | LA, ZCG |
| B27, B28, B47 | Runs of simple critical zeros; local positivity at fixed `λ` on density-one heights; multiplicity by a non-size input | sub | ZCG, RW |
| B29–B45 | The single open estimates of PTR, HCF, PA, XN, GTA, TT, CHMD, RN, SZ, TG, SC, ACS, HF, FU/CFC/RP, LI, ACT, AIP | RH | as named |
| B124 | Finite initial depth budgets of the heat divisor | ≥qRH to RH | ZCG, LA |
| B146 | An independent family of bounded index converging to ξ (index certified without the zeros); exact Dirichlet-polynomial factors with a constant term are excluded | RH (producer) | W1C, PTR, IRP |

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
| B145 | The signed centred type-II current, with both continuum terms, at a growing isolated mode | AAL [D] | ZCG, BAG, ELT |
| B148 | The transfer of candidate S3 | ≥B56 [D] | S3, BAG |
| B150 | A form factor bounded by `4` on `(1,10/9)` | sub | census |
| B64, B65 | Signed pair information beyond bandwidth one; genus upper law and logarithmic Serre duality | sub; indep. | census, ACS |
| B98 | Positive-generator integer-norm systems: which count distance forbids a finite top layer | method | RAC, SPAL, APD |
| B113 | Möbius × quarter-disc remainder `O(X^{½+ε})` | beyond RH | PM |

### Γ — selection, reflection, transport, count
| # | Problem | Strength | Routes |
|---|---|---|---|
| B13 | Finitely many off-line zeros ⇒ none | sub | whole programme |
| B138 | Landing for ζ (as an atom) | sub | ZCG, LA, ELT, HF |
| B141 | Deuring–Heilbronn for ζ: `¬AAL⇒ZAL` (§2.5) | sub | BAG, ZCG, ELT |
| B83 | AAL = B13 ∧ Landing ∧ DH | sub | BAG, JAS, SC, ZCG, WL |
| B89, B112, B128 | A bounded aligned return at each right zero; the FE into vertical transport; replication | sub | BAG, ZCG, EFT |
| B68, B71 | Reflection Krein positivity, flux, dispersion; universal decay and the horizon rates `y^{¾−ε}` | RH | PM |
| B72–B76 | Cutoff-uniform target mass; the candidate zero-parameter conditions; FE-pair reality | RH | BAG, candidates, ZCG |
| B80, B81 | FE twins in the full class; candidate landings | sub; producer | SEL; candidates |
| B86 | Endpoint character positivity at unbounded rank | RH | ECP, ACS |
| B87 | A nonnegative count on the rays `Γ_1+Γ_p`, defined without `Q` | RH | ACS, HF, PM |
| B88 | The sign of the comb finite part / of the Gram defect | RH | HF, ACS, HAT, AGZ |
| B114, B117 | A realization of the partner involution outside the excluded classes; a regulated horizon pure at every cutoff with ξ as its limit | producer | PM |
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
| B143 | Decisive radius in the class `𝒵(γ_min,C)`: bounded windows, or every unbounded radius | neither: one configuration with unattained top beats every floor on windows of every length; some monotone `R→∞`, `R=o(log T)`, fails; the logarithmic radius decides ζ. The counter-configuration violates the density theorem [D]; residual B151 | [S] |
| B140, B139, A64, A66 | Shortest decisive radius for ζ; sparse scale-local windows; sign-free local decision | radius `32 log(T+2)` with exceptional sets; absolute, width and signed-deletion forms | [L*] |
| B138 (as a method question) | Which structures decide landing | three-atom factorization; fails for the FE alone and for the Euler product alone | [L*] |
| B85, B142 | A family producing purity at ζ | none among the canonical families: fixed-part laws; analytic smoothings and their mixtures are isozeric with a moving or delayed singularity | [L*]/[S] |
| B133, question (G) | One glued carrier object for the diagonal | no; survivors: comb finite parts, weighted covariance, the clock, the scattering tower | [L*] |
| A70 | Torus periodization of the mixed Green kernel | absolutely convergent, symmetric, descends; leafwise Robin diagonal; the critical spherical average is the minimal Green kernel | [L*] |
| B125 | No halving pairs as a condition for the one-eigenform receiver | void; the condition is the Shimura zero (B147) | [L*] |
| A50 | Finite-stratum laws on the cosine and shifted Jensen families | Jensen: the law gives RH; cosine: the law gives RH ⇔ ZAL | [L*]/[L] |
| A65, A67, A74 | Two-prime local criterion; dominant-ordinate divergence; graded recurrence | theorems | [L*] |
| — | Periodicity of the zeros in height, two-sided and one-sided | none | [L*] |
| — | Exact arithmetic factors of ξ | a bounded Dirichlet-series factor is pure; no Dirichlet polynomial with a constant term is a factor | [L*] |
| (S1), (S2) | A Frobenius with cheap simultaneous vanishing over ℤ; a sign-free quantity bounding the fibres of the height map | no (cost `m·θ(S)`); a receiver (ordinate injectivity ⇔ RH) | [L*] |
| §2.8 topological question | Is the remainder `S(T)` the index of the archimedean gluing | the gluing conditions are the smooth count; the contacts tested at a height are the smoothed increments of `S`, up to the off-line correction | [L*]/[S] |
| §2.9 questions | Which comb; the carries; integer-norm monoids; the second axiom on the tower | a separated comb stable under the Frobenius monoid is one orbit, with its own density as counterterm; the carry cocycle of a block, a nonzero class complementary to the window count; the comb of unit masses fixes `Λ`; on the tower Riemann–Roch and Bézout give the product formula | [L*]/[S] |
| 𝔽₁ questions Q1–Q10, Q12–Q14 | Endomorphisms, multiplicity, locality of the diagonal, ampleness, Gamma factor and pole, integer-norm monoids, normal direction, duality, diagonal as finite part, one object, the comb, the carries, the additive datum | answered (§2.14) | [L*]/[S] |

## 2.3 Frankenstein routes

**No assembly closes RH.** Every assembly below has an open input of RH, AAL or ≥qRH strength, or names one. Their value is to collapse independent problems into one, to decouple the producers a proof needs, or to fix what a missing input must contain.

| # | Parts | What the assembly gives | Missing input | Gain |
|---|---|---|---|---|
| F1 | **Two-world skeleton.** A floor on windows of any unbounded radius (kills world I) with any ZAL receiver, or a floor on logarithmic windows (kills both) | RH [L*] | one floor | below the logarithmic radius the two worlds need two inputs at the level of `𝒵` [S] |
| F2 | **One inequality per prime, local, with exceptions.** Prime two-bumps, Stepanov count, count door, sign-free form, logarithmic windows, power-thin exceptional sets | Σ, Π and count readings are one number per prime on sparse windows [L*] | B130 on one sequence of windows | every prime-side route has one target, at scales and with exceptions it may choose |
| F3 | **Deligne skeleton over ℤ.** Tensor positivity, Künneth, Rankin square, gauge family with big monodromy | every step except the family step, which the fixed-part laws close [L*] | none exists inside the canonical families | the tensor branch is support, not a route |
| F4 | **Critical curve.** Threshold identities, hierarchy, pole channel, ground states, classification | one inequality and one orthogonality [L*] | B104 | RH ⇔ `R_c=W₀` if the orthogonal case is excluded [D] |
| F5 | **Horizon.** Cavity receivers, reflection Krein forms, one-eigenform reduction, count door | physics reduces to one rate or one reflection sign [L*] | B71 or B68 | receivers complete and sharp |
| F6 | **The diagonal.** Adelic Green formula, comb finite parts, scattering tower, clock with exact form domain, refutation of the glued carrier | Weil's form has three exact regulated presentations with one sign [L*] | B88 | every glued invariant presentation is closed |
| F7 | **Rigidity.** Hamburger, FE-defect isolation, count distance, isozeric deformations, fixed part, factor purity | ζ is identified by any two of its structures, has no moduli and no bounded arithmetic factor [L*] | B112 | no calibration with both structures exists |
| F8 | **Finite-layer world.** Free strip, Mertens power saving, late heavy returns, filters at every speed, top-ordinate dichotomy, centred Vaughan currents at every moment order and at exponential scales | a complete receiver with an exact gap `a(1−β)/2` [L*]/[S] | B145 | the missing bound is the exclusion; the reduction error is exponentially small |
| F9 | **Exactness.** Frobenius at one prime, `m·θ(S)`, Chebyshev auxiliaries, tower Riemann–Roch, carry cocycle, orbit rigidity | every exact method over ℤ returns the product formula or Chebyshev [L*]/[S] | B97, B137, B121 | what survives is approximate, growing-height information |
| F10 | **Count skeleton.** Tate principle, hyperelliptic count law, contacts in `𝒢`, tower of lines, section counts | Riemann–Roch has an exact count; Bézout for the comb pairing is the Hodge index [L*] | B87, B149 | the count door and the sign door need the same statement |
| F11 | **Construct, then identify.** Index semicontinuity with FE rigidity | a nonzero limit of index-one functions with ζ's FE and a Dirichlet series is a multiple of ζ and gives RH [L*]/[D] | B146 | names a producer class; exact polynomial factors are excluded from it |
| F12 | **Graded recurrence.** Transport receivers with the density theorem | `T^c` one-separated returns, `c>(30/13)(1−σ)`, exclude a zero right of `σ` [L*] | quantitative transport | BAG needs power-sparse returns, not positive density |
| F13 | **Sign-free skeleton.** Signed deletion, two-sided windows, ordinate injectivity, index law, recurrence against the density theorem | RH from `\|c_p\|≤K` on log-square windows without positive averaging; purity of bounded Dirichlet-series factors without a sign [L*] | a two-sided producer | under the constraint the receiver is complete and one purity theorem is proved |
| F14 | **Dark range.** Savings, heavy-return dictionary, strip breadth, collective counts, collision counts | one first-return statement, proved to the VK height and, in a strip, to `exp(c·y^{1−Θ∞})` [L*]/[L] | B97, B137 | gap `(log y)^{3/2}` against `y^c` |
| F15 | **Theta wall.** Adaptive head `=ζ(½+ib)` up to `O(\|b\|^{−½})` [L] | all ranks reduce to the size and sign of ζ on the line near its zeros | B102 | merges TH with the critical-line sizes |
| F16 | **Census.** Covariance ceiling, exchange rates, near-line alternatives | `70%` follows from a bounded form factor [L*]/[L] | B150 | a law statement with exact receivers |
| F17 | **Hodge lattice at finite scale.** Normal form, Zariski's lemma, short-window coercivity, block Schur test, index law, verified-height rung | RH ⇔ one explicit symmetric matrix on the integers — off-diagonal `½(1/\|m−n\|+1/(m+n))+Λ(n/m)`, diagonal `−log(n/2π)`, pole plane `1/m+1/n` — has one positive square on every window, in the limit on packets [S]; at finite scale its index is finite uniformly in the scale, a lower bound `−ηΣc_n²` at arbitrarily large scales gives RH, and under ¬RH a negative direction of bounded norm exists at every large scale [S] | B152 | Weil's form, the count door and the Li ladder read one matrix; each ratio is a finite-height statement once A80 is done [A] |
| F18 | **Flow.** Trace determines the module; Castelnuovo–Severi on the flow; zeros as weights of the contacts under scaling | RH ⇔ the lag function is positive definite on `ℝ` [D] | the sign | WL and ACS are one statement on the flow |
| F19 | **Remainder.** Gluing index, zero count, contacts at a height | zero count at a height = archimedean gluing conditions − contacts at that height + off-line correction, smoothed [S] | — | the index formula of the square is the argument principle; purity is the vanishing of its correction |

**Closest to the open core: F2, F17, F8, F11.** F2 and F17 are the two exact forms of one target: F2 on two-bump packets at prime ratios [D], F17 on all real divisors of a window. F8 shows that world I is fully instrumented. F11 is the one conversion from law to point whose identification step is a theorem.

### What a contradiction search may assume in world I (F8)
| In world I | Evidence |
|---|---|
| `Θ<1`; isolated top `β`, attained; remainder `≤Θ∞<β` above the layer's heights | [L*] |
| `M(x)=O(x^{β′})`, `β′<1` | [L*] |
| heavy returns at `t≥T₁` need `log t≥c·y^{1−β″}`, `β″<Θ` | [L*] |
| filters read each top residue at every damping speed; fixed positive critical modulus at the polynomial boundary | [L*] |
| two distinct positive top ordinates, or pointwise divergence of the corrected current | [L*] |
| centred Vaughan reductions at every moment order; exponentially small error at exponential scales | [L*]/[S] |
| one-separated returns to a small disc at a zero right of `σ` number fewer than `T^c`, `c>(30/13)(1−σ)` | [L*] |
| no half progression of zeros through a top zero, nor an `ℓ²` perturbation of one | [L*] |
| every floor fails on windows of every unbounded radius | [L*]/[L] |

No contradiction comes from exact identities alone, from positivity, Euler products, integrality or counting alone, from the FE with order one and reality, from a property shared by the heat family, or from any in-law statement [L*]/[L]/[D].

## Validation tests for 2.4, 2.5 and 3

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

**No question passes all tests and is a door to RH.** Every statement about the zeros of ζ below AAL is one of the sectors B13, Landing, DH or a structure theorem of world I; every pointwise prime-side statement past the VK saving is a named problem; the transfer of S3 and B56 imply AAL [D]. The questions below are the strongest that pass; each states its limit.

## 2.4 Breakthrough question below RH and quasi-RH: does the pole channel see every failure first?

**Question (B104).** *If RH fails, is every critical half-line ground state charged?* At the critical curve `R=c⁸/log N` the three cases are RH; ¬RH with `R_polar<W₀`; ¬RH with `R_polar=W₀` finite and every unit critical half-line ground state orthogonal to the polar source [L*]. Is the third case empty?

**What is proved [L*].** `R_c=R_c^{PSD}=R_polar=R_halfline`; the hierarchy `0<R_c≤R_nonneg≤R_polar≤R_high=W₀`; the complete matrix at ratio `R` is positive ⇔ the primitive hyperplane is ∧ the pole channel is; below `W₀` the primitive hyperplane is eventually positive, so the pole channel decides; `R_c=W₀` ⇔ the pole channel is eventually positive at every `R<W₀`; a charged critical ground state forces `R_polar<W₀`; `log R_c≥log c₁+c₂a` for every `a≤a*(ζ)`. No countable square-bounded family of holomorphic multipliers dominates the depleted kernel [L].

**What either answer gives.**
| Answer | Effect |
|---|---|
| The third case is empty | ¬RH ⇒ `R_polar<W₀`. RH ⇔ `R_c=W₀` ⇔ pole-channel positivity at every ratio below the window threshold: the five routes that meet at the critical curve (HF, SRT, AIP, ACS, SC) and their nine programmes have one inequality, a rank-one payment, with no separate window statement [D] |
| A polar-orthogonal ground state is consistent | a second failure mode that the pole channel does not see; at such a threshold the complete matrix carries no information beyond the windows, and the critical-curve programme ends at the window sign |

**Why this question.** The critical curve is the one place where the corpus has a complete reduction — compactness, threshold identities, hierarchy, ground states, classification — with exactly one undecided case. It is a statement about a variational problem on a half-line, implied by RH and implying nothing about the width.

**First step and obstacle.** Write the Euler–Lagrange equation of the Gamma-truncated charged critical form at `W₀`; the polar pairing is one linear functional of the ground state; test whether the equation forces it to be nonzero through the depleted kernel `m(z)=4/(¼−z²)−12/(64−z²)`. Named obstacle: the ground state is a limit of nonpositive directions and its equation contains the full zero side.

**Tests.** T1: vacuous under RH; implies no width. T2: emptiness of a case. T3: the table. T4: no finite rung. T5: the classification separates the cases; tempered fixed-ratio models show positivity at a fixed ratio is not automatic [K]. T6: not refuted. T7: moves Σ135, Σ139, B6, B101. T8: not a named problem.

**Limit.** Confined to the critical curve; it produces no sign.

### Alternatives
| Question | Why it matters | Verdict |
|---|---|---|
| Resolution in ζ's class (B151, §3) | the last parameter of the receiver of the minimal face | passes; the one question |
| The full window at finite scale (B152) | the Hodge index as a statement on real vectors | RH at all ratios; each ratio just work [A] |
| Separation of the off-line ordinates (B144) | bounded windows for ζ by an `[L*]` theorem | passes T1–T7; no first step |
| Depth density `o(T)` (B57) | first unconditional input in law for seven near-line receivers | a 100%-type census problem; cannot decide an atom |
| Shimura nonvanishing at `ρ/4+¼` (B147) | the one-eigenform receiver without side condition | excludes coincidences of zeros of two functions |
| Bounded form factor (B150) | `70%` on the line | a pair-correlation problem past the diagonal |
| A72, A73, A80, A82, A87, A90 | sharper receivers and identifications | just work |

## 2.5 Breakthrough question below AAL: the Deuring–Heilbronn sector, with a free strip

**Question (B141).** *Does an isolated top layer of ζ force the zeros to approach the line?* That is, is the world `½<Θ∞<Θ<1` empty.

**Position [L*]/[D].** AAL ⇔ B13 ∧ Landing ∧ DH, and a failure of AAL fails exactly one of the three. B13 contains the exclusion of one off-line quartet; Landing is an atom of the RH path. DH is the only sector of AAL off the RH path, and it is vacuous in every ZAL world. The extreme form `¬AAL ⇒ finitely many off-line zeros` is equivalent to `AAL ⇔ B13` [L*]. B56 implies DH.

**What the sector looks like.** Every world in which AAL fails has `Θ<1` [L*]. A DH-violating world is doubly instrumented [L*]/[D]:
- at the top: a finite layer at `β`, read by prime-only filters at every damping speed; Mertens power saving; two distinct top ordinates or a divergent corrected current; every floor fails on windows of every unbounded radius;
- in the tail: infinitely many zeros approaching `Re s=Θ∞∈(½,β)`, of density zero in height, with heavy returns later than `exp(c·y^{1−Θ∞−ε})`.

**Calibrations [L*].** Positive integer-norm two-scale Euler products with linear counting realize every `(Θ,Θ₂,Θ∞)=(β,θ₂,θ)` with `½<θ≤θ₂<β<2/3`, and every graded repulsion bound is refuted on that class; classical Deuring–Heilbronn holds for a real zero of a primitive quadratic `L(s,χ)` with a constant uniform in conductor, height and zeros.

**What either answer gives.**
| Answer | Effect |
|---|---|
| Yes | world I consists of ZAL worlds only: AAL ⇔ B13 ∧ Landing = (ZAL ⇒ RH); AAL research is RH-path research; the finite-layer receiver needs to be run only over remainders on the line |
| A proof that no FE ∧ Euler identity decides it | a world `½<Θ∞<Θ<1` is consistent with everything the corpus uses; AAL needs vertical transport (B112) |

**First step and obstacle.** The classical mechanism needs a zero that nearly cancels the pole; ζ has none. The anchor available here is the tail: on a line `Θ∞<σ<β` the complete filter that deletes the finite top is bounded by `C h^d t^N e^{at(c−σ)/2}` for every `c>Θ∞` when the remainder lies left of `c` [L], and the top modes grow at rate `a(β−σ)/2`. The question is whether the reflected top `1−β̄`, entering through the FE, forces a term on the tail side that this bound forbids. Named obstacle: every filtered current is the filtered zero sum; a contradiction needs an inequality that the explicit formula does not imply, and no model with both structures exists to test one (§1.4).

**Tests.** T1: implied by AAL; implies none of ZAL, B13, quasi-RH. T2: an implication. T3: the table. T4: a tail statement, neither asymptotic nor local below a height [L*]. T5: false on integer-norm two-scale products [L*]. T6: not refuted. T7: moves B83, Γ184, F1, F8. T8: contains the exclusion of an isolated top over a ¬ZAL remainder; not Landau–Siegel.

**Limit.** One sector of AAL; B13 and Landing are separate atoms.

### Alternatives
| Question | Effect | Verdict |
|---|---|---|
| The signed centred type-II current at a growing isolated mode (B145) | contradiction in world I | fails T1: it is the exclusion of the layer [D] |
| The transfer of S3 (B148); B56 | AAL and more | fail T1: imply AAL [D] |
| Can the top layer be a single quartet | pointwise divergence of the corrected current at every supercritical speed [L*] | a structure theorem of world I; it excludes nothing |
| B13; the one-quartet world | the minimal finite layer | fails T8: single-quartet exclusion |
| Thick crude count, sampling-set bound, lag recurrence (B110, B126, B127) | AAL | contain AAL |

## 2.6 If positivity, Weil positivity and spectral methods are excluded

"Spectral" is read as spectral theory of operators in every form; "positivity" includes nonnegativity of counts, Dirichlet coefficients, kernels and averaging measures, the Hodge index and Tate limits. Kept: Fourier analysis, mean values used as bounds, exponential sums, absolute convergence, continuation, power sums, integrality, Diophantine approximation and transcendence, recurrence, Jensen and Rouché.

**What survives [L*].**
- **Receiver.** RH ⇔ `|c_p|≤K` on arbitrarily late log-square windows, proved with complex deletion filters and no positive averaging; width form; RH ⇔ the ordinate is injective on the zeros.
- **Counting by winding.** A Hermite–Biehler defect of degree `κ` has at most `κ` exceptional points, with every index attained; the bound passes to locally uniform limits; the Eisenstein pencil is of index one and the half-shifts `ξ(s+½)±ξ(s−½)` are of index zero, certified by `‖G(w−1)‖≤‖G(w)‖` on `Re w>1`.
- **Recurrence against density.** A bounded Dirichlet series whose zeros are zeros of ξ is pure: Bohr recurrence of a zero against the density-zero law of the deep zeros. `T^c` separated returns, `c>(30/13)(1−σ)`, exclude a zero right of `σ`. This is the only mechanism of the corpus that proves a purity statement inside the strip without a sign and without absolute convergence.
- **Forced symmetry.** A Dirichlet polynomial with a constant term and its zeros on the line has a functional equation.
- **Priced producers.** Frobenius at one prime, cost `m·θ(S)`; integrality reaches Chebyshev; exponential sums reach VK; Stepanov at one prime reaches `p^{11/12}` for Heilbronn sums; separation by absolute value is excluded for ζ.
- **A calibration in characteristic `p`.** The Carlitz–Goss zeta function has a Riemann hypothesis by Newton polygons [C]; its combinatorial input — which collections of base-`p` digits of `N` split into parts divisible by `p^s−1` — is in Lean; the optimality of the greedy composition is not (A84).

**The question.** *Is ξ a locally uniform limit of size-certified Hermite–Biehler sums of bounded defect?* That is: entire `E_n`, finite divisors `W_n` of degree `≤κ` in the right half-plane, inequalities `|W_n^♯E_n^♯|≤|W_nE_n|` on `Re s>½` proved from Dirichlet-series sizes, Stirling and exponential sums alone, and `W_nE_n+W_n^♯E_n^♯→ξ`. Then ξ has at most `κ` right zeros [L*].

**Why it opens the path under the constraint.**
- It is the only conversion from sizes to the location of every zero that uses neither a sign of a form nor an operator, and the corpus has its two theorems: the index law and its semicontinuity.
- It has calibrations on both sides: the Eisenstein pencil, certified by absolute convergence, converges to `(s−1)ξ(2s)` and not to ξ; the natural theta half has infinitely many right zeros [L]; a ferromagnetic chain on the Γ sites is real-rooted and has the Riemann–Siegel cosine sum with frozen phase as its first-order term [L*]; no Dirichlet polynomial with a constant term can be an exact piece of ξ [L*].
- For the natural deformations the defect degree is the width axis: a certificate must reach inside the strip, which sizes on `Re s>1` do not.

**Second lead under the constraint.** The recurrence mechanism needs an object that is uniformly almost periodic inside the strip and whose zeros are zeros of ξ. Which objects attached to ζ are bounded Dirichlet series on a half-plane `Re s>x`, `x<1`? None is known to the corpus; the factor theorem shows that any such object is automatically pure.

**Strength.** A bounded defect is finite off-line support, hence at least ZAL; RH then needs B13. Under the constraint no question below quasi-RH passes the tests.

## 2.7 If RH is a physical phenomenon in AdS with a modular horizon

**What is proved [L*]/[L].** The modular horizon is the quotient of the Rindler wedge of AdS₄ by `SL₂(ℤ)`; its resonances sit at the zeros of `ξ(2s)`; RH ⇔ every pulse rings down at the quarter rate ⇔ one cavity energy of Hecke forms decays at `y^{¾−ε}` ⇔ every reflection Krein form has no negative square. Three regulators of the horizon are in Lean:

| Regulator | Finite cutoff | Limit |
|---|---|---|
| Cusp cutoff at height `Y≥1` | pure: index at most one; all zeros on the line for `Y≤4πe^{−γ}`, one real exceptional pair above | `(s−1)ξ(2s)` after normalization: not ξ |
| Scattering tower at cusp height one | Robin-normalized Maass–Selberg diagonals with one scalar counterterm; no sign | Weil's functional on packets |
| Green damping of the arithmetic clock, `r↑1` | `E_r≤W`; finite exactly on the closed Weil form domain; shifted inverses converge strongly | Weil's form, with error `≤(1−r²)‖f′‖²/2` |

A bulk built from one adelic-invariant kernel with Weil's diagonal does not exist; the weighted adelic Green kernel is a positive covariance with a Robin diagonal on the rational torus and does not sign Weil's form.

**The reading [D].** Purity at finite cutoff and the right limit are split between the regulators: the cusp cutoff is unitary and pure and converges to the wrong function; the tower and the clock converge to Weil's form and carry no sign at finite cutoff. The index is lower semicontinuous, so a limit of regulated systems with at most one complex mode has at most one. In the clock regulator RH reads: `E_r(f)≥−(1−r²)‖f′‖²/2` near `r=1` on every packet — positivity up to the regulator's own error.

**The question (B117).** *Is there a regulator of the modular horizon that is pure at every cutoff and has ξ as its limit?* A family of self-adjoint boundary conditions on the quotient of the wedge — a wall, a stretched horizon, a defect at a marked point, or a two-parameter interpolation between the cusp cutoff and the clock — whose secular functions are conjugation-real, have at most one right-half zero, and converge locally uniformly to ξ as the regulator is removed. Then RH holds [L*].

**Why it opens the path.**
- It replaces a sign at the horizon by two structural properties: unitarity of each regulated system and continuity of the limit.
- The identification of the limit is free: a limit with ζ's FE and a Dirichlet series is a multiple of ζ [L].
- It is what the closed classes leave: internal modular conjugation, vacuum-fixing partners, half-sided inclusions and the glued invariant bulk are excluded [L]/[L*]; regulators are not.
- It is calibrated: the cutoff family is pure with the wrong limit; graph black holes with `t²>4q` are impure at every size [L]; the exceptional mode born at `4πe^{−γ}` shows what a regulator may create on the real axis and not off it.

**Second physical question (B147).** For one Hecke eigenform the receiver is complete up to one selection rule: no zero of its Shimura integral at `ρ/4+¼` for a nonhalving right zero `ρ` [L*]. A physical reason for that nonvanishing would make every single mode of the cavity a sharp receiver.

**Limit.** A regulator whose secular function is built from the zeros is a restatement; the family must be built from the places and the horizon.

## 2.8 If RH is a problem of topology or geometry

**What is proved [L*]/[S].** The arithmetic square is a curve; its graphs meet in the primes; the contacts are the prime part of Weil's off-diagonal and the jets the archimedean part; no object of finite type carries the contacts. The pairing of the degree points has a Hodge index theorem equivalent to RH: exactly one positive square on `H,V` and every finite family of packets; its defect has at most as many negative squares as ζ has zeros right of the line. In the normal form the pairing is one matrix on the integers; the graphs of a window of ratio `≤19/18` span a negative definite lattice at every scale; on a window of ratio `≤Q` the comb form is nonnegative off fewer than `2QR(Q)` block sums. The pairing has Zariski's form `D·D=Σc_n²V(n)−½Σ(c_m−c_n)²Γ_m·Γ_n` with nonnegative off-diagonal entries; in the gauge of the flat tail the potential is the remainder of the prime number theorem. The gluing conditions of the graphs count the zeros in the mean; the contacts at a height are the remainder `S`. The orientation cover over ℤ has centred count `M(N)`, weight `≥½`, weight `½` ⇔ RH.

**Geometric question (B152).** *Is the lattice spanned by the two rulings and the graphs of a window hyperbolic at every finite scale?* For every ratio `Q` and every large `N`: `D·D≤2d₁d₂` for every real divisor on the degree points of `(N,QN]`. In the limit on packets this is RH, and the finite-scale inequality with any relative slack at arbitrarily large scales implies RH [S]; on short windows it is a theorem at every scale [S]; in between the index is finite uniformly in the scale [S]. The geometric content is a reason of the configuration: every off-diagonal intersection number is nonnegative, as for curves on a surface, and the short windows are negative definite, as for an exceptional configuration. What is missing is a fibre: a positive divisor in whose gauge the potential is nonnegative and the signed part of the Dirichlet form — the pole plane contributes `1/m+1/n` against the jets and the contacts — is controlled. For the flat tail the potential is `N/n−ψ(N/n)+O(1)`.

**Topological question (B106).** *Is there a correspondence on the orientation cover over ℤ with bounded local indices and Lefschetz number the number of points of the cover?* It would bound the centred count `|M(N)|` by the dimension of the middle cohomology times `N^{½}` [L*]. Known: the prime-vertex indices localize `1−M(N)` and are unbounded; every self-map homotopic to the identity fixes the primes of `(N/2,N]` [L].

**The index formula of the square [S].** Zeros below a height = gluing conditions − contacts at that height + off-line correction + constant, after smoothing by the window. It is the argument principle read on the square: the gluing index is the smooth term, the contacts are `S`. Purity is the vanishing of the correction, not a new index.

**Why these open the path.**
- They are the two-dimensional statements the no-gos leave: not finite type, not a glued invariant carrier, not a duality between contacts and jets, not a diagonal attached to a point.
- They use objects with exact finite-scale definitions: one integer-indexed matrix; one cover with an integer count.
- The calibration is exact over `𝔽_q[T]`: no carries, an orientation cover with `qⁿ` points; over ℤ the carry is a nonzero cocycle class and the carry term is complementary to the window count [L*].

**Limit.** The hyperbolicity of the lattice at every ratio is RH; each fixed ratio is a finite-height statement [A].

## 2.9 New field for RH: Hodge theory of a fixed part

**Does RH need a new field?** Yes. Each known conversion of a statement in law into a statement at every zero has an exact price over ℤ: a sign needs a two-dimensional object, and the square is a curve; an integrality gap needs cheap vanishing, and its cost is the count; recurrence stops at the Kronecker scale; a family sees only its variable part; separation is a receiver; limits of pure objects follow the width axis; exact arithmetic factors are pure and do not cover (§1.4–§1.10). ζ is rigid, infinite-rank, and its diagonal is a comb finite part. The field exists in the corpus as the programme `HodgeTheoryOfAFixedPart`.

| Aspect | Content |
|---|---|
| What it is about | The pairing of the degree points — contacts, jets, comb counterterm — as one symmetric matrix on the integers; its index on windows; its effective classes; its potential and its Dirichlet form |
| What it is like | Arakelov theory in which the datum at a point is the density of a comb, not a metric; intersection numbers that are finite parts; statements on real vectors at finite scale, on windows of bounded ratio; no families and no moduli |
| Established | Normal form and Zariski's lemma; coercivity `(1/50)Σc_n²` on windows of ratio `≤19/18` at every scale; finite index at every scale; limit `2d₁d₂−Z(f)` and Hodge index ⇔ RH on packets with the index law; margins on packets of width `≤181/250`; the comb fixes `Λ`; the density is the counterterm; a separated comb is one orbit of the Frobenius monoid; the gauge of the flat tail; the inequality at finite scale decides the limit; Riemann–Roch on the tower with the gluing index and Bézout as the product formula [L*]/[S] |
| Criteria | Reproduce Weil's proof for curves, where the comb is `q^ℤ`. Fail on the golden datum, the integer-norm one-offs (the comb sees them [L*]), the `cosh` models, the heat family and the non-tempered pair. Use the coefficient size exactly. Be pointwise. Respect the no-gos: no finite type, no glued invariant carrier, no duality between contacts and jets, no diagonal attached to a point, no producer from the tower's own Riemann–Roch |
| Questions it must answer | The sign on a full window, with nonzero block sums and their cross terms (B152). Which positive divisor is the fibre of a window: in which gauge is the potential nonnegative? How does the index of a window grow with its ratio, against the visibility height (A79, A81)? Is the Li ladder the comb form on a sequence of tails (A82)? What is the statement over a curve in comb language, and over a number ring (A91)? Is there an intrinsic reason for the two-block case, which is Stepanov's bound (A87)? |
| Tools it develops | Zariski's lemma on combs; block Schur tests with one subtraction; gauges by positive divisors; the carry cocycle of a block; the index law at infinite rank; window locality with exceptional sets; ordered approximations (the clock) |
| Objects | Degree points, real divisors, jets, contacts, counterterm, comb pairing and comb form, degrees, potential, windows, blocks, the flat tail, the gluing index, the tower of lines |
| Language | comb, density, finite part, contact, jet, potential, gauge, block, window, ratio, effective class, defect, index |
| Mechanisms | Built on: contacts plus jets, comb finite parts, the pairing weighs the zeros, index law, logarithmic windows with exceptions, normal form, Zariski's lemma. To discover: the sign of the block-sum part of a window from a property of the comb |

**Main conjecture (Castelnuovo–Severi at finite scale).** For every ratio `Q` there is `N₀` such that `D·D≤2d₁d₂` for every real divisor on the degree points of `(N,QN]`, `N≥N₀`, for a reason intrinsic to the comb. **Milestones.** M1 [L*]/[S] the pairing, its limit, the Hodge index on packets, margins to width `181/250`, the comb fixes the contacts. M2 [S] normal form, short windows at every scale, finite index at every scale, the flat-tail gauge. M3 each ratio from a verified height (A80). M4 the statement over a curve and over a number ring in comb language. M5 every ratio (RH).

## 2.10 New field for AAL: arithmetic surgery theory

**Does AAL need a new field?** Yes. AAL says that no finite layer of zeros can be isolated at the top. World I is completely described and its identities are consistent; over a curve the statement is free by periodicity; over ℤ the zeros contain no vertical progression, no half progression and no `ℓ²` perturbation of one; the only exact symmetries of the prime orbit are dilations and the FE preserves height [L*]/[L]. What is missing is an obstruction theory for finite modifications of the divisor of an object with both structures. No programme folder carries this name; its theorems sit in `ExceptionalLayerTheory`, `ArithmeticPositiveDuality` and the abscissa laws.

| Aspect | Content |
|---|---|
| What it is about | Finite surgery on the zero divisor of an FE–Euler object: which of the structures — Euler product, Dirichlet series, FE, coefficient size, the count `⌊x⌋` — survive the insertion, removal or relocation of finitely many quartets; isolated layers as obstructed surgeries |
| What it is like | Obstruction theory: a finite layer has a class in arithmetic data (first integer gap, Bohr almost periodicity, annihilator mass, heavy-return exponents, the centred type-II current), and AAL is the vanishing of the set of unobstructed layers |
| Established | The sector theorem; the instrumentation of world I at every damping speed and every moment order; exponentially small reduction error at exponential scales; top-ordinate dichotomy; rational relocation destroys Bohr almost periodicity and the Dirichlet series; floors on unbounded windows exclude an attained top [L*]/[L]/[S] |
| Criteria | Reproduce periodicity over `𝔽_q`. Fail on the one-offs, the two-scale and approaching Euler products, the `cosh` models and `ζ(s−h)`. Not be a statement in law. Permit real isolated zeros where the classical theory permits them and forbid non-real ones |
| Questions it must answer | Is the divisor of ζ surgery-rigid? Which invariant detects an inserted layer in the presence of both structures? Does the FE turn an isolated layer into a second layer at another height? Does the tail at `Θ∞` constrain the top (B141)? What bounds the signed type-II current at a growing mode (B145)? |
| Tools it develops | Relocation calculus; finite-layer filters; centred Vaughan currents; heavy-return laws in a strip; positive annihilators and their phase geometry; graded recurrence against density theorems |
| Objects | Finite layers, tails, filters, corrected currents, annihilators, relocation densities, Euler heads and tails |
| Language | layer, tail, surgery, relocation, obstruction, sector, transport, replication |
| Mechanisms | Built on: the sector theorem, the instrumentation of world I, the calibrations, classical Deuring–Heilbronn. To discover: an obstruction to isolating a non-real layer that uses the FE and the Euler product jointly |

**Main conjecture (surgery rigidity).** No object with ζ's functional equation, Euler product and coefficient size has an isolated non-real top layer. **Milestones.** M1 [L*] world I instrumented. M2 an obstruction class for a one-quartet layer. M3 DH (B141). M4 the landing sector. M5 AAL.

## 2.11 New field for RH without positivity: sign-free index and recurrence theory

**Does a positivity-free RH need a new field?** Yes. The sign-free proofs of a Riemann hypothesis have priced shadows over ℤ: Stepanov's needs a Frobenius with zero derivative, and the cost of simultaneous vanishing is the count; separation by a Newton polygon needs coefficient gaps, and the critical ordinates have none; the Carlitz–Goss proof lives where addition has no carries, and over ℤ the carry is a nonzero class [L*]. What remains inside the constraint is counting by winding and recurrence against density. Its theorems sit in `SignFreePurityMechanisms` and `InfiniteRankPurityTheory`.

| Aspect | Content |
|---|---|
| What it is about | Splittings `ξ=E+E^♯`, their defects and size certificates; limits of functions of bounded index; almost periodic objects whose zeros are zeros of ξ; two-sided local bounds on windows as the prime-side interface |
| What it is like | Hermite–Biehler theory with no positive kernel: comparisons of moduli and winding numbers, sizes from Dirichlet series, Stirling and exponential sums; Bohr recurrence set against zero-density theorems |
| Established | Index law at every index, attained; semicontinuity; the Eisenstein pencil and the half-shifts certified by sizes; signed window criteria; ordinate injectivity ⇔ RH; a bounded Dirichlet-series factor is pure; a Dirichlet polynomial with its zeros on the line has a functional equation and is not a factor; graded recurrence [L*] |
| Criteria | No sign of a form and no operator. Fail for the non-tempered pair. Be pointwise. Not be uniform in real characters unless it excludes exceptional zeros. Explain why the natural theta half fails |
| Questions it must answer | Which splitting has a bounded defect? How does the defect degree move along the natural deformations? Which objects attached to ζ are uniformly almost periodic inside the strip? Can a two-sided bound on logarithmic windows be converted into a size comparison of two halves? What replaces the carry-free digit calculus of Carlitz–Goss when the carry is a nonzero class? |
| Tools it develops | The index law and its semicontinuity; Rouché counts; signed deletion filters; two-sided window criteria; recurrence against density; exponential sums at the exact normalization; ultrametric calibration |
| Objects | Halves, defects, pencils, exceptional parameters, deletion filters, windows, almost periodic factors, digit contents |
| Language | half, defect, index, exceptional point, size certificate, winding, recurrence, factor |
| Mechanisms | Built on: index law, semicontinuity, signed window criteria, factor purity. To discover: a size certificate inside the strip, or an almost periodic object carrying the zeros |

**Main conjecture (bounded defect).** ξ is a locally uniform limit of size-certified Hermite–Biehler sums of bounded defect. **Milestones.** M1 [L*] index law; pencil; signed windows. M2 [L*] the Lagarias–Suzuki law and the half-shifts from sizes alone; factor purity. M3 a splitting with defect `O(log T)` in height windows. M4 a bounded defect (finite stratum). M5 B13 without a sign.

## 2.12 New field for RH as AdS physics: cutoff holography of arithmetic horizons

**Does it need a new field?** Yes. The horizon has complete receivers and exact Krein bookkeeping; the bulk reading with one invariant kernel is refuted; three regulators are known, and purity at finite cutoff and the right limit are split between them (§2.7). There is no theory of the regulators of an arithmetic horizon and of the index along their flow. No programme folder carries this name; its theorems sit in `HyperbolicArakelovTheory`, `BlackHoleRingdown`, `ArithmeticHolographyOfTheModularHorizon` and `InfiniteRankPurityTheory`.

| Aspect | Content |
|---|---|
| What it is about | Families of self-adjoint boundary conditions on the quotient of the Rindler wedge of AdS₄ by `SL₂(ℤ)`: cutoffs at cusp height `Y`, walls, defects at marked points, Green damping; their secular functions and energies; the number of complex modes along the flow; renormalized limits |
| What it is like | Holographic renormalization with a Krein count: each regulated system is unitary and has index at most one; exceptional real modes are born at explicit thresholds; the renormalized limit inherits the index bound |
| Established | Line law at every cusp cutoff; threshold `4πe^{−γ}`; scattering-tower normalization; clock energies with exact form domain and resolvent convergence; reflection Krein law; cavity receivers; torus Green kernel with Robin diagonal; critical spherical average [L*] |
| Criteria | Build from the places and the horizon, never from the zeros. Reproduce the established laws. Make graph black holes with `t²>4q` and the non-tempered pair impure. Avoid the closed classes |
| Questions it must answer | Which regulator is pure at every cutoff and has ξ as its limit (B117)? Is the index monotone in the cutoff? What is the mode born at `4πe^{−γ}`? Is the reflection Krein form the limit of the positive forms of regulated systems? Is there a regulator whose energies approach Weil's form with an error of one sign and a manifestly nonnegative regulated energy? What selects the Shimura nonvanishing for one eigenform? |
| Tools it develops | Walls and pseudo-Laplacians [C]; Maass–Selberg calculus at general cutoff; the index law and its semicontinuity; the scattering tower; Green damping; cavity energies and reflection Krein forms |
| Objects | The modular horizon, cutoffs, seeds, cavity functions, constant terms, exceptional parameters, clock energies, reflection Krein forms, weighted adelic Green kernels |
| Language | regulator, cutoff, wall, secular function, exceptional mode, index, renormalized limit, cavity, resonance |
| Mechanisms | Built on: line law, exceptional parameter, scattering tower, clock, cavity receivers, Krein law, index semicontinuity. To discover: the regulator |

**Main conjecture (unitary regulator).** A family of self-adjoint regulated horizons has secular functions of index at most one converging locally uniformly to ξ. **Milestones.** M1 [L*] cutoff family, tower, clock, receivers. M2 the index along one regulator flow other than the cusp cutoff. M3 a regulator whose limit has ζ's FE. M4 a universal positive decay rate (zero-free strip). M5 RH.

## 2.13 New field for RH as topology or geometry: lattice and index theory of the arithmetic square

**Does it need a new field?** Yes. The geometric objects exist with exact counts — the square, its contacts, the tower of lines, the gluing index, the comb lattice of a window, the orientation cover — and the classical forms of the surface are closed: finite type, an invariant glued carrier, a duality between the finite and the archimedean parts. There is no theory of hyperbolic lattices of infinite type whose signature is governed by a zero count. Its theorems sit in `AbsoluteGeometryOfSpecZ` and `HodgeTheoryOfAFixedPart`.

| Aspect | Content |
|---|---|
| What it is about | The lattice spanned by the two rulings and the Frobenius graphs with the comb pairing; its signature on windows; the lattice of gluing conditions of index `N!`; the remainder `S` as contacts at a height; the carry class; the weight of the orientation cover; the squares of number rings and their class groups |
| What it is like | Surface theory without a surface: Zariski's lemma, exceptional configurations, a Hodge index, an index formula per height window — on an object of infinite type whose intersection numbers are finite parts |
| Established | Gluing index and its asymptotics; the count at every height with `S`; contacts at a height read `S`; negative definite short windows; finite index at every scale; Hodge index ⇔ RH on packets; carry cocycle nonzero and complementary to the window count; the square of a Dedekind domain with orbits ⇔ principal ideals [L*]/[S] |
| Criteria | Reproduce `𝔽_q[T]`: no carries, self-similar counts, an orientation cover with `qⁿ` points. Respect the no-gos. Express purity as the signature of one lattice per window. Fail on integer-norm monoids through the comb |
| Questions it must answer | Is the window lattice hyperbolic at every finite scale (B152)? What is the fibre class of a window? Is there a complex whose first cohomology in a height window is spanned by the zeros of that window? What is the weight filtration on the middle cohomology of the orientation cover at infinite rank (B106)? What do the class group and the units of a number ring add to the lattice? |
| Tools it develops | Necklace lattices and gluing indices; comb pairings and Zariski's lemma; block decompositions; carries as a cocycle; infinite-rank Lefschetz theory with the Meyer flow |
| Objects | Graphs, contacts, necklace matrices, towers of lines, weight lines, combs, windows, blocks, the orientation cover, ideal-indexed squares |
| Language | gluing condition, gluing index, height window, lattice of a window, signature, fibre class, carry, effective class, weight |
| Mechanisms | Built on: gluing index against the zero count, contacts at a height, the comb lattice, Zariski's lemma, orientation-cover weight. To discover: the hyperbolicity of the window lattice from the configuration |

**Main conjecture (hyperbolic windows).** For every window the lattice of its graphs and the two rulings has exactly one positive square at every large scale. **Milestones.** M1 [L*] gluing index and its asymptotics. M2 [L*]/[S] the count per height with `S`; the contacts as the remainder. M3 [S] short windows negative definite; finite index. M4 windows of bounded ratio from verified height. M5 every window (RH).

## 2.14 A research programme to construct `𝔽₁`

**Goal.** A geometry in which Spec ℤ has a product with itself and one of the two proofs for curves runs: Weil's (a surface with a Hodge index) or Stepanov's (an endomorphism and an auxiliary). The programme is `AbsoluteGeometryOfSpecZ`, continued by `HodgeTheoryOfAFixedPart`.

**What the corpus fixes.**
| Question | Answer | Evidence |
|---|---|---|
| Q1 Which endomorphisms have `N(n)` fixed points | the Witt Frobenius `F_n` on `𝒢=W(ℤ)`; on the diagonal `log#(ℤ/J(1,n))=Λ(n)`; `1+1/(n²−1)` is the trace of `F_n` on the jets; `N` itself is not an element of the square | [L*] |
| Q2 Multiplicity at a prime over `𝔽₁` | the order of the `p`-derivation; between graphs the contact order; evaluated jets measure integer order only where the first and `p`-th ghost components agree | [L*]/[L] |
| Q3 Why the diagonal is not local | it is a branch of a curve with torsion conormal classes; its archimedean entry is `log(density/2π)` of a comb | [L*]/[L] |
| Q4 Ampleness; Riemann–Roch ⇒ Hodge index | not without a second axiom; on the tower both axioms hold and give the product formula | [L]/[S] |
| Q5 Gamma factor and pole as geometry | weights of the same Frobenius on the sequence ring: `0,1` for the pole plane, `−2j` for the jets | [L*] |
| Q6 Integer-norm monoids other than ℤ | invisible to the square; visible on the comb: unit masses force `Λ`, and any other weight fails Bézout on some packet | [L*]/[S] |
| Q7 Normal direction of the diagonal | none in characteristic zero in the square; `∂/∂Y` on the toric surface of a base | [L] |
| Q8 A duality exchanging contacts and jets | none; transposition is the FE and preserves both parts | [L] |
| Q9 Weil's diagonal as a finite part | on combs of degree points, with the comb's counterterm; never one glued invariant object | [L*] |
| Q10 One object | the real algebra `𝒮_q` generated by the orbit ring with a base, `χ_1` and `τ`: stable under every shift, containing the tower, the pole plane and the jets, with exact counts. Pointwise the cyclic module of the point count has every weight; against packets at a scale the contacts have the weights `±½`, the jets and `ρ−½` | [L*] |
| Q12 The comb | the density of the comb at the point; between combs the pairing changes by the mass times the logarithm of the ratio of the densities; a separated comb stable under the Frobenius monoid is one orbit `δℕ` | [L*]/[S] |
| Q13 Carries | a cocycle that is not a coboundary, in digit and in Witt form; complementary to the window count: it bounds nothing | [L*] |
| Q14 The additive datum | the comb of unit masses: every integer is a norm exactly once ⇔ `w=Λ` | [S] |
| Q11 Bézout | `CombBezout Λ` ⇔ RH; a theorem on packets of width `≤181/250` and at every scale on windows of ratio `≤19/18`; open | [L*]/[S] |

**State of the constructions.**
| Construction | State |
|---|---|
| A. Frobenius lifts (the Stepanov side) | closed: order `m` at the primes of `S` costs `m·θ(S)`; at one prime Stepanov's method bounds Heilbronn sums [L*] |
| B. Carries (transport from `𝔽_q[T]`) | closed: a nonzero class; an identity with the window count [L*] |
| C. The surface (the Weil side) | the invariant glued carrier is refuted; survivors: comb finite parts, the weighted covariance, the scattering tower, the clock [L*] |
| D. The archimedean fibre | weight lines with the jets and the pole plane; no gluing by a duality [L*] |
| E. A second dimension | the toric surface of a base and the tower of lines; one ring `𝒮_q`; Riemann–Roch with the gluing index; Bézout on it is the product formula [L*]/[S] |
| F. The lattice | the comb pairing as one matrix at finite scale; Zariski's lemma; short windows negative definite; finite index; Hodge index ⇔ RH [S] |
| G. Number rings | squares indexed by ideals; contacts `log N𝔭`; orbits ⇔ principal ideals [L*] |

**Criteria the construction must meet.**
1. Reproduce Weil's and Stepanov's proofs for curves; over `𝔽_q[T]` there are no carries.
2. Counts alone are not enough: the golden datum has effective elements and is impure [L].
3. Use the FE: the integer-norm one-off and the approaching Euler product must fail.
4. Use the Euler product: `cosh` models and the heat family must fail.
5. See the coefficient size: the non-tempered pair must fail.
6. Infinite type: no finite fibre; no finitely generated Frobenius-stable lattice.
7. The diagonal is the density of a comb, not the discriminant and not a number attached to a point.
8. Positivity, if used, is derived: Riemann–Roch and Bézout are two axioms, and on the tower they give the product formula.
9. The archimedean place is a fibre of the same Frobenius.
10. The statement lives at finite scale on real divisors, and its index is finite uniformly in the scale.

**Questions the programme must answer.**
- Q11 Bézout for the comb pairing (RH).
- Q15 The full window: nonzero block sums and their cross terms at every ratio (B152).
- Q16 The fibre: a positive divisor of a window in whose gauge the potential is nonnegative; for the flat tail it is the remainder of the prime number theorem.
- Q17 Number rings: the comb, the counterterm and the Hodge index on the square of `𝒪_K`; what the class group, which obstructs the orbits, does to the lattice (A91).
- Q18 The two-block face: Stepanov's bound as the Hodge index on two short blocks at prime ratio, for a reason of the lattice (A87).
- Q19 The Li ladder as the comb form on a sequence of tails (A82).

**Tools.** Witt vectors and Λ-structures; necklace coordinates and gluing indices; towers of lines with digit counts; comb finite parts and the normal form; Zariski's lemma; block Schur tests; the carry cocycle; the index law.

**Objects and language.** Arithmetic square, graph, contact, ghost component, Teichmüller point, orbit, tower of lines, base, weight line, jet, pole plane, comb, density, carry, real divisor, potential, gauge, window, block, effective class.

**Mechanisms.** Built on the answered questions, the pairing as a weighing of the zeros, and the finite-scale theorems. To discover: the sign of the block-sum part of a window.

**Milestones.** M1 [L*] questions Q1–Q9; the pairing equal to `2d₁d₂` minus the zero sum on packets. M2 [L*] the object of Q10 with its count. M3 [L*] the comb pairing on that object; the comb, the carries and the additive datum (Q12–Q14). M4 [L*]/[S] Bézout at bounded apertures: width `181/250`, the enlarged aperture, every scale on short windows; finite index at every scale. M5 Bézout (RH).

**Decisive early test.** An integer-norm system with an off-line pair lifts to the square through its norms and is invisible there; on the comb its contact weights differ from `Λ` and Bézout fails for it on some packet [L*]. The construction passes the test.

## 3. The one big question: does the density theorem restore short windows?

**Question (B151).** Let `𝒵₀(γ_min,C)` be the class of tempered reflection-symmetric zero configurations without real zeros, with lowest ordinate at least `γ_min>0`, local counts `N(t,t+1)≤C log(|t|+3)`, and deep zeros of density zero: for every `d₀>0` the zeros of depth `≥d₀` below height `T` number `o(T)`. ζ belongs to `𝒵₀` [L*]/[L].
1. *Bounded windows.* Is there `L` such that a floor `2 Re S(u)≥−K` on windows `[u_k,u_k+L]`, `u_k→∞`, forces every zero of a configuration in `𝒵₀` onto the line?
2. *Unbounded windows.* If not, does every radius `R(T)→∞` decide `𝒵₀`?
3. *Power form.* The same with the density bound `N(σ,T)≤T^{θ(σ)}`, `θ(σ)<1`, which ζ satisfies for `σ>17/30` [L*].

**What is proved.** Radius `32 log(T+2)` decides ζ, with power-thin exceptional sets and in width form [L*]. Radius `r√T` decides every tempered configuration [L*]. Under `δ`-separation of the deep ordinates the length `80/δ+1` decides, from either side [L*]. In the class `𝒵` without the density condition no bounded length decides and some radius `R=o(log T)` fails [S]. A floor on windows of any unbounded radius excludes an attained top [L*].

**Why the class matters [D].** Both corpus counterexamples to short windows violate a property of ζ. The low off-line pair violates the lowest ordinate. The block tower is positive on its window by synthesizing a constant from high frequencies: at level `k` it uses the full arithmetic progression of ordinates of step `1/(4(k+1))` across `[Γ_k,2Γ_k]`, two zeros per step, all at one depth — `8(k+1)Γ_k` deep zeros where ζ has `o(Γ_k)`.

**What the mechanisms suggest [A].** These are heuristics, not theorems.
- A nonnegative function on a window has a windowed Fourier transform dominated by its value at frequency zero. A deep ensemble with all ordinates `≥γ_min` leaks little to frequency zero, so a floor forces every dominant deep ordinate to have a deep neighbour within `O(1/L)`: separated ensembles are visible (the mechanism of the separated-window theorem).
- A cluster of `n` deep ordinates at spacing `g` cancels on a window of length `L` only to relative size `(gL)^{n−1}`, and must beat the growth `e^{xT}` of its modes: a self-cancelling cluster hides only near its own scale, and a fixed cluster becomes visible on every later window.
- To hide older clusters a later level must be positive and dominant on its window. A sum of modes with ordinates `≥Γ` that is positive on a window of length `L` has its phase unwound against `e^{iΓu}`; by the zero count of exponential sums this needs of the order of `ΓL` modes within a bounded number of octaves above `Γ`. With deep zeros of density zero such a level does not exist at large height.

**What either answer gives.**
| Answer | Effect |
|---|---|
| Bounded windows decide `𝒵₀` | RH ⇔ `∃C,K`: for infinitely many `x`, `P(p)≤A(p)+K` at the primes of `[x,Cx]`, off power-thin exceptions; the only zero-side input is the density theorem, which is a theorem; the count door, the upper side and the two-sided form hold on the same windows; world II is excluded by a floor on bounded windows, so every window-type receiver of AAL is a receiver of RH; the separation hypothesis (B144) is unnecessary; a producer may work at bounded ratio on scales of its choice |
| Every unbounded radius decides `𝒵₀`, bounded ones do not | RH ⇔ the Stepanov bound on `[x,e^{R}x]` for any `R→∞`, with no ZAL premise; the obstruction to bounded windows is a sparse cluster mechanism that the answer exhibits |
| Neither | an interference construction compatible with the density theorem: tail worlds with ζ's counting and ζ's density of deep zeros pass floors below the logarithmic radius; the logarithmic radius is the resolution of the minimal face for ζ's own class, and ZAL cannot be removed from any shorter receiver; the construction shows what world II must look like |

**Why this question.** RH has one minimal face shared by the three wall families, and the resolution of that face is the last open parameter of its receiver. The answer in the class `𝒵` is negative for a reason that ζ does not share. The density theorem is the one statement in law that has entered a pointwise theorem of the corpus (the purity of bounded Dirichlet-series factors); the question asks whether it enters the receiver of the minimal face as well. It is a statement about configurations, implied by nothing about the location of ζ's zeros.

**First step and obstacle.** Prove the neighbour statement (A88): a floor on a window of length `L≥L₀(γ_min,C)` forces, for every deep ordinate whose mode is dominant on the window, a second deep ordinate within `O(1/L)`. Then bound the number of modes of a positive dominant level from below by the argument principle. The named obstacle is dominance under an unattained top: which zeros dominate at scale `T` is decided by `x_ρT−8 log γ_ρ`, not by a fixed finite set, and near-coincident deep pairs are not excluded by density zero.

**Tests.** T1: method. T2: three stated alternatives. T3: the table. T4: no finite rung. T5: calibrated on the low off-line pair (fails without `γ_min`), on the block tower (fails without density zero) [S], on separated configurations (bounded suffices) and on general tempered configurations (`√T`). T6: the refuting configuration of the larger class is outside `𝒵₀` [D]. T7: moves Σ146, Σ149, Σ152, B130, B126, B144, F1, F2; the answered shape is the class `𝒵`, not `𝒵₀`. T8: not a named problem; first step in corpus objects, one named obstacle.

**Limit.** It decides where the bound must be proved, not whether it holds. No question below AAL that passes the tests does more.

### Alternatives considered
| Question | Effect | Verdict |
|---|---|---|
| Polar orthogonality (B104, §2.4) | the critical curve becomes one inequality | passes; Σ block only |
| Deuring–Heilbronn for ζ (B141, §2.5) | AAL reduced to the RH path | passes; no model with both structures to test a mechanism |
| The full window at finite scale (B152) | the Hodge index on real vectors | RH at all ratios; each ratio just work [A] |
| Shimura nonvanishing (B147) | one eigenform as a sharp receiver | receiver only |
| Separation of the off-line ordinates (B144) | bounded windows for ζ | no first step |
| Depth density `o(T)` (B57); bounded form factor (B150) | first unconditional near-line inputs | census problems; cannot decide an atom |
| `Θ<1⇒Θ=½` (B56); the transfer of S3 (B148) | RH from quasi-RH; a route through returns | fail T1: imply AAL [D] |
| The signed centred type-II current (B145) | contradiction in world I | fails T1: the exclusion itself |
| An independent family of bounded index (B146); Bézout for the comb pairing (B149); a pure regulator (B117) | RH | producers of RH strength |
| Finite stratum (B13); landing as an atom (B138) | atoms of the RH path | B13 fails T8; landing has no first step: a zero at depth `δ` is lost at every speed below `π/(2δ)` [L*] |
