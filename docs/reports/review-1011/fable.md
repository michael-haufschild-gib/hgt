# Consolidated review — big picture, obstacles, questions, programmes

**Sources.** [Frontier map](../rh-current-frontier-map.md), [scoped obstructions](../rh-killed-routes.md), [unification ledger](route-unification-ledger.md), [route obstacles](route-obstacles.md), [walls ledger](walls-ledger.md), [obstacles summary](obstacles-summary.md), the programme READMEs under `formal/GaloisForLFunctions/`, the pipeline cards, and the Lean corpus through `scripts/formal_tools.py research`. Corpus checkpoint `64f7831503` with its working tree. Working log: `logs/review-1011-fable-report.md`.

**Evidence.**
- `[L*]` Lean statement read for this report. `[M]` module docstring read, statement not re-read.
- `[L]`, `[K]`, `[S]` as graded in the frontier map: integrated Lean; Lean with transitive axiom audit; source present, unfinished or unintegrated.
- `[P]` paper proof on a pipeline card. `[D]` deduction made in this report, not a Lean theorem. `[A]` assessment.
- `[C]` published mathematics quoted from memory; not in the corpus and not checked against a source. Every `[C]` item needs a check before it is used.

**Where the five ledgers and the corpus differ.**

| Ledger row | Corpus |
|---|---|
| Σ156, B154: the exceptional square is open, gap `log 4` | no gap: the trivial aperture of a conductor is `log log q+o(1)`; every dominated system is positive below it with margin, the Liouville twist fails above it (`exists_trivialAperture_margin`, `tendsto_trivialAperture_sub_log`) `[L*]` |
| Γ212, B153: bounded almost periodic constituents open | no absolutely convergent Dirichlet series, and no absolutely convergent expansion over the positive rationals on a strip, has a zero in a strip about the line with its zeros there among those of `ξ` (`LSeries_ne_zero_of_strip_zeros_subset_xi`, `expansion_ne_zero_of_strip_zeros_subset_xi`) `[M]`; open only for the bounded class on `Re s>x`, `0≤x<½` |
| A68: a landing calibration with ζ's Gamma factor is missing | `exists_riemann_gamma_counting_model_without_landing` `[L*]` |
| A92, A95, B151: prime-side resolution law, finite layers | `sign_interval_resolution` (`ΓL≤nπ`) `[L*]`; `FiniteTopLayersNeedNoSeparation` `[M]` |
| A97, A98, A99, A100, A101 open | Newtonian multipoles and chain squares `[M]`; feasible squares at every aperture `[L*]`; jump-tail floor `[M]`; trivial aperture with uniform constant `[M]`; repulsion margin `[S]` |
| Q20 of §2.14: an object with unit masses and paid contacts | the paying ring `ℤ[y_p]` and the planar square (`TheEulerFactorsOfTheDivisorSumPayEveryContact`, `ThePlanarSquareHasTheContactsOfTheSquareAndPaysThem`) `[M]`/`[S]`; on the planar square the values on `Γ_m` of the sections vanishing on a finite set `S` are exactly the product of the contact ideals (`planarValues_eq_prod`) `[M]` |
| §2.13: genus function and Riemann–Hurwitz as readings | `TheCountertermOfANumberRingObeysRiemannHurwitz` `[M]`; the index of the square of an abelian ring equals the number of right zeros (`exists_le_negIndex_ringDefect_iff`) `[L*]` |
| S3: the transfer is open | the transfer implies `Θ<1 ⇒ RH` (`HomogeneousReturnTransferImpliesStripCollapse`) `[S]` |

---

## 1. The big picture

### 1.1 One object, two exact forms

Every live formulation reads one quantity. For the cubic spline `B` let `c_B(u)` be the real part of its lag structure under Weil's form; `c_B(log d)=A(d)−P(d)`, the archimedean-plus-pole prediction minus the smoothed von Mangoldt count in the window of `d`.

- **One inequality per prime.** RH ⇔ `2c_B(log p)≥−K` at the primes of arbitrarily late windows `|log p−T|≤32 log(T+2)`, outside at most `Ce^{δT}` primes per window, any fixed `δ<1` (`riemannHypothesis_iff_prime_logarithmic_windows_off_finset`) `[L*]`. The exponent of the floor is the zero width; a power saving is quasi-RH; the two-sided form needs no sign `[L]`.
- **One matrix on the integers.** The comb pairing of the degree points — jets `½(1/|m−n|+1/(m+n))`, contacts `Λ(n/m)`, diagonal `−log(n/2π)` — has the limit `2d₁d₂−Z(f)` on packets. RH ⇔ `D·D≤2d₁d₂` on every packet ⇔ one positive square on the two rulings and every finite family of packets `[L]`. The negative index of the defect on packets is exactly the number of zeros right of the line, for ζ and for the square of an abelian number ring `[L*]`.

The form has no margin. The weights are forced (`CombBezout w ⇔ RH ∧ w=Λ`), the constant `2π` is forced (`combBezoutShift_iff: c≤0 ∧ RH`) `[L*]`, the best margin of a window decays doubly exponentially `[L]`, and RH ⇔ at every aperture some weight system satisfies Bézout, with no compatibility between apertures (`riemannHypothesis_iff_forall_exists_combBezoutAt`) `[L*]`.

### 1.2 The second coordinate: two worlds, three atoms

`Θ=sup Re ρ`, `Θ∞=inf{σ: finitely many zeros right of σ}`. ZAL `Θ∞=½`; AAL `Θ=Θ∞`; B13 finitely many off-line zeros ⇒ none; Landing ZAL ⇒ finitely many off-line zeros; DH ¬AAL ⇒ ZAL.

- RH ⇔ ZAL ∧ B13 ∧ Landing; AAL ⇔ B13 ∧ Landing ∧ DH `[L]`; `Θ<1 ⇔ Θ∞<1` (`quasiRH_iff_zetaAsymptoticAbscissa_lt_one`) `[L*]`.
- A failure of RH is world I (¬AAL: a finite isolated top layer at `β<1` at bounded height, a free strip above it, a Mertens power saving) or world II (AAL ∧ ¬ZAL: a tail approaching `Re s=Θ∞>½`) `[L]`.
- The atoms are properties of ζ alone `[D]`. Each calibration class drops one structure: integer-norm Euler products carry finite top layers and approaching remainders `[L]`; an entire function with the Riemann functional equation, the Riemann Gamma factor, residue one at `1` and the zero count of `ξ` within one has every zero off the line, approaching it, and violates Landing `[L*]`. A Dirichlet series with ζ's functional equation is a multiple of ζ `[L]`. So no model with both structures exists on which an atom can be tested.

### 1.3 The ladder: what is known is sizes

`SelectiveArithmetic` puts every sign statement on one scale. A system has a mass `m` (log conductor; log height of a modulated packet; both add) and a packet an aperture `a`. The rung is `κ=a/log m`.

| Fact | Evidence |
|---|---|
| Below rung 1 the mass pays every dominated contact system `|w|≤Λ`: twisted parts of real and complex characters, with margin `½(1−e^{−η/2})log q∫f²` at `a≤log log q−η`; Weil's form of ζ on packets of bounded shape at height `t`, `a≤log log|t|−η` | `exists_trivialAperture_margin`, `exists_height_margin` `[L*]` |
| At rung `1+o(1)` both one-structure fakes fail: the Liouville twist (Euler product, no functional equation) and the lattice with one pair (functional equation, no Euler product) | `tendsto_trivialAperture_sub_log` `[L*]`; `isolatedPair_neg_of_rung` `[M]` |
| Prime side of the exchange rate: partial sums `≤Cn^{½+γ}` buy the sign up to `κ<1/(2γ)` on bounded shapes | `exists_cancellation_margin` `[M]` |
| Zero side: an isolated pair of depth `δ` shows at `κ=1/(2δ)`; positivity at aperture `κ log m` forces a second off-line zero within `m^κ` of a zero of depth `>1/(2κ)` | `isolatedPair_nonneg_of_rung`, `zeta_companion_of_rung` `[M]` |
| The classical zero-free regions, Landau–Page and Siegel sit at rung `1+o(1)`; a strip of width `ε` is rung `1/(1−2ε)`; RH is every rung | SA atlas `[M]` |

**Two ladders, one rate `[D]`.** The mollifier ladder of `ConjugateDiagonalGeometry` and `MultiscaleMollifiedZetaField` has the same exchange rate. Dyadic boundedness of `∫_T^{2T}|ζΨ|²` for prefix-cancellation mollifiers of length `≥T^{θ₁}` forces `|Re ρ−½|<1/(2θ₁)+ε` for all but finitely many zeros; cofinal boundedness for unbounded `θ` is RH; the growth exponent of `∫_1^T|ζM_{T^θ}|²` has slope `2·width` in `θ` (`TwoSidedThetaMollifierTrap`, `LongMoebiusSecondMomentRigidity`) `[M]`. Depth `1/(2κ)` on the aperture ladder and depth `1/(2θ)` on the mollifier ladder are one axis.

| Axis | Kind of statement | Proved | Quasi-RH | RH |
|---|---|---|---|---|
| aperture rung `κ` | pointwise, every height | `κ<1` (sizes); classical regions at `1+o(1)` `[L*]` | one `κ>1` | every `κ` |
| mollifier exponent `θ` | mean value over `[T,2T]` | `θ<½` with both gcd main terms `[K]`; `17/33`, `4/7` `[C]` | one `θ>1` | unbounded `θ` |
| breadth of heavy returns of the primes `≤y` | pointwise, every height | none while `log t≤(log y)^{3/2−ε}` `[L]` | — | — |

Two consequences `[D]`.
1. On the pointwise ladder no rung is proved in `(1,∞)`, and every candidate first step is a classical problem: the region `1−c/log log t` (height), the least non-residue at the scale `log²q` (conductor), a Brun–Titchmarsh constant below `2` (family).
2. On the mean-value ladder rungs exist below `θ=1` and each is a density or census statement. Above `θ=1` the conversion from a mean value to every zero is a theorem: one off-line zero contributes a spike `Y^{2δ}` that exceeds the whole budget `T`. The conversion costs length past the height.

### 1.4 Hard obstacles that are solved

| Obstacle | What is a theorem | Anchor |
|---|---|---|
| Many routes | one inequality per prime; one matrix; route classes by source identity | SOSZ, AGZ, HFP `[L]` |
| Global data in the decision step | logarithmic windows with power-thin exceptions; `√T` windows; two primes; counts on windows; one-sided upper side `[S]` | SOSZ ScaleLocality `[L*]`/`[L]` |
| A decision without positivity | `|c_p|≤K` on windows by complex deletion filters; RH ⇔ ordinate injectivity | SOSZ, SignFreePurityMechanisms `[L]` |
| Resolution of the minimal face | no receiver below the logarithmic radius in class `𝒵`; `n` modes of frequency `≥Γ` keep one sign on length `≤nπ/Γ`; a finite top layer of ζ is seen on windows whose length depends only on the number of its quartets | `sign_interval_resolution` `[L*]`; `FiniteTopLayersNeedNoSeparation` `[M]` |
| The exceptional coordinate | sector theorem; quasi-RH as a tail law; world I instrumented: filters at every speed, centred Vaughan currents at growing order, top-ordinate dichotomy | ZCG, ELT `[L]`/`[K]` |
| Landing as a method question | fails for the Euler product alone and for the functional equation with ζ's Gamma factor and count | APD `[L]`; IRW `[L*]` |
| The price of sizes | trivial aperture `log log(mass)` in the conductor and the height aspect; no gap; exchange rates on both sides | SA `[L*]`/`[M]` |
| Critical compactness | `R_c=R_polar=R_halfline≤W₀`; three-way classification; subcritical positivity below exponent `1/8` | AHD, CACT `[L]`/`[K]` |
| The window chain | RH ⇔ `Ψ` locally bounded on precontact intervals; sign at aperture `a` from verification to `windowHeight(a)`; RH through height 67 | CSTW, AIF, VHR `[L]` |
| Rigidity | Hamburger; FE-defect isolation for countable systems; isozeric gauge deformations; the fixed part of the canonical families; continuous prime measures are not rigid (`ζ·exp(ε/(s+1)²)`) `[S]` | HTGeometry, EFT, AWT `[L]` |
| Constituents | bounded Dirichlet-series factors are pure; no exponential polynomial is a factor (`infinite_zeros_not_xi_zeros`) `[L*]`; the jump law on every strip; Wiener's lemma on a strip; no absolutely convergent Dirichlet series is a constituent with a zero, in a half-plane or in a strip; limits of box constituents lose their zeros | IRP, CTZ `[L*]`/`[M]` |
| Exactness over ℤ | Frobenius at one prime; cost `m·θ(S)`; Stepanov at one prime (`p^{11/12}`); Riemann–Roch with Bézout on the tower is the product formula; the carry is a nonzero class complementary to the window count | SFPM, ALST, AGZ `[L]` |
| The square of Spec ℤ | `W(ℤ)` is a curve with the prime contacts; no finite-type carrier; one ring of sequences with exact counts; unit masses with paid contacts exist on the paying ring and the planar square, and Bézout by restriction is an equality there | AGZ `[L]`/`[M]` |
| The diagonal | the density of a comb, counterterm `log(density/2π)`; no glued invariant carrier; the constant `2π` forced | AGZ, HAT `[L*]`/`[L]` |
| The lattice | normal form at finite scale; short windows coercive and blind to the contacts; finite index; jets are even Newtonian multipoles; contacts are chain squares; the index counts the right zeros exactly; genus `1+(n/2)log(n/2π)` and Riemann–Hurwitz for number rings | HFP, AGZ `[L*]`/`[M]` |
| Regulators | clock, scattering tower, cusp cutoff; RH ⇔ the jump-tail floor at every fixed height | HAT `[L]`/`[M]` |
| The horizon | one cavity function is a complete sharp receiver; reflection Krein index counts off-line zeros | AHMH `[L]` |
| Prime distribution and census in law | Guth–Maynard `30/13`; Matomäki–Radziwiłł for μ at every length; simple critical zeros `≥0.67250071`; alternatives at `70, 75, 80%` | RHTower, IGP `[L*]`/`[L]` |
| Scope of failed mechanisms | 42 dead mechanisms and the scoped obstructions with survivors | killed-routes |

### 1.5 What stands between the corpus and a proof or a refutation

**(a) No producer.** Every route is a receiver. Every unconditional pointwise statement lies below rung 1 or at `1+o(1)` and holds for a whole class of fakes (§1.3). Every mechanism that proves a statement of this type elsewhere has a Lean-fixed price over ℤ (obstacles summary §1.15).

**(b) The wall has one description `[D]`.** A rung above one needs a power saving of the contacts on the integers between `m` and `m^{2κ}`, with both structures used jointly (SA mechanisms 6–8). The Liouville twist is the fake on the Euler side. A statement that separates ζ from it at that range is a parity-sensitive statement at a power-saving scale. Type I and Type II norms, coefficient norms and finitely many linear laws are parity-blind `[L]`. The same wall is the square-root threshold in every regime: bandwidth `1` in the census, `θ=1` for mollifiers, rung `1` for apertures, the Vinogradov range for short sums.

**(c) The atoms.** ZAL is at least quasi-RH. B13, Landing and DH have no calibration with both structures (§1.2), and no inequality known in mathematics uses the functional equation and the Euler product jointly and is pointwise in the zeros `[A]`: the joint theorems are in law (Selberg, Levinson, the census), the pointwise ones are identities (Hamburger, the jump law).

**(d) World I is invisible to mean values `[D]`.** Relocating finitely many zeros preserves vertical square means `[L]`; a long prime or Möbius sum at one point is controlled only through the zeros; the gap between the Vinogradov–Korobov range and the growth range of a top mode is `a(1−β)/2` `[L]`.

**(e) Structural gaps.** The dark range (Dirichlet polynomials longer than the height, and prime sums shorter than the Vinogradov range). Bézout from a property of the object: the square, the tower, the planar square and the lattice exist, and on each the section count returns an identity (the product formula; the product of the contact ideals) `[L]`/`[M]`.

**(f) A refutation.** Nothing in the corpus points to one. §11 states what a refutation would have to exhibit.

---

## 2. Opportunities

None closes a wall of §1.5. Ranked by what they would change.

| # | Opportunity | What it gives | State |
|---|---|---|---|
| 1 | **Finish the constituent theory in the bounded class** | the zero set of `ξ` contains the zero set of no bounded almost periodic function; closes every "exact piece" route (W1C, PTR, PM pieces) | Wiener class in Lean `[M]`; bounded class on `Re s>x`, `0≤x<½`: the left expansion of `F′/F` is only square summable `[P]` |
| 2 | **The census past the diagonal** (§4) | `70%`; the first statement of the corpus that uses bandwidth above `1` | the positivity ceiling of the certificate is undetermined and decidable; the Conrey–Ghosh–Gonek ratio at `θ=½` is `19/27` and has a Krein form without RH `[D]` |
| 3 | **A positivity-free census** | a proportion of zeros on the line proved by winding and mean values only | the Levinson gate is a hypothesis `[M]`; the twisted second moment for `θ<½` is in Lean `[K]`; the assembly is open (§12) |
| 4 | **The ladder as one theorem** | quasi-RH ⇔ one rung `κ>1` on isolated zeros ⇔ one bounded long mollifier moment `θ>1` ⇔ slope `<1`; the cluster hypothesis made explicit | pieces `[M]`/`[L]`; assembly open (§12) |
| 5 | **A fake for the height aspect** | sharpness of rung 1 for ζ's own class (block-aligned phases) | listed as "to build" in SA |
| 6 | **Rough packets** | whether cancellation of partial sums pays the sign on all packets of an aperture or only on bounded shapes | open in SA; decides if the prime-side exchange rate is a statement about `Σw(n)n^{−iτ}` uniformly in `τ` |
| 7 | **Number rings beyond abelian** | the index law with Artin characters; the class group as characters of the ideal comb | quadratic and cyclotomic of prime conductor in Lean; Hecke and Artin explicit formulas absent |
| 8 | **Critical curve** (B104) | the five routes at the critical curve reduce to the pole channel if no critical half-line ground state is polar-orthogonal | open; decidable on the isolated-pair class first `[A]` |

Two observations.
- **Verification is the only source of selective signs at bounded mass.** At height zero the archimedean symbol is negative at low frequency, and the proved apertures (below `½`) use the contact at `2` with its sign `[L]`. Each larger aperture follows from verification to the explicit `windowHeight(a)` `[L]`; by the height aspect zeros above `exp(e^{a+η})` are invisible to packets of bounded shape at aperture `a`, so the intrinsic exchange is of that order unless a zero-free strip is known `[D]`.
- **Clusters are the difference between a rung and a strip `[D]`.** Positivity on a rung excludes isolated deep zeros and forces companions otherwise `[M]`; half-period deletion resolves `n` modes at a cost linear in `n` `[L*]`. A bound for the number of deep zeros in a window of length `(log t)^κ` would turn the rung law into an equivalence with a strip; a bounded local count of deep zeros in unit windows is stronger than Lindelöf `[C]`.

---

## 3. Quasi-RH: is there a clear path?

**No.**

What the corpus establishes.
- Quasi-RH is a tail law: `Θ<1 ⇔ Θ∞<1` `[L*]`. Its failure is world II at `Θ=Θ∞=1`: zeros approaching the line `Re s=1` on a set of heights of density zero.
- Seven equivalent forms across routes (`quasiRH_crossRoute_seven_way_tfae`): escaped Möbius laws, centred prime bands, prime and Möbius power-window savings, receiver damping rate `<½` `[L*]`. A one-sided power saving at the primes of late logarithmic windows off power-thin exceptions `[L]`.
- On the ladder `[D]` from `[M]`: quasi-RH ⇐ one bounded dyadic second moment with a prefix-cancellation mollifier of length `T^{θ₁}`, `θ₁>1`; quasi-RH ⇒ the sign on bounded shapes at every rung below `1/(2·width)`; the sign at one rung `κ>1` at all large heights excludes isolated zeros of depth `>1/(2κ)`.
- In mean-square form `[D]`: with `X=T^θ`, `∫_1^T|M_X(½+it)|²dt` is `T/X` times the variance of μ in intervals of length `X/T`; slope `<1` in `θ` is a power saving of that variance for intervals of length `x^{1−1/θ}`. The corpus has Matomäki–Radziwiłł at every length with a saving that is not a power `[L]`.

Why this is not a path.
1. The only mechanisms for a zero-free region are positivity at the pole with growth bounds, and exponential sums. Both end at rung `1+o(1)` (SA atlas) `[M]`.
2. Between the proved range and quasi-RH there is no rung on the pointwise ladder (§1.3). The first step past rung 1 by a constant `C` is the region `1−c/log log t` `[D]`.
3. On the mean-value ladder the rungs below `θ=1` do not add up to a rung above it: at `θ≤1` a mollified second moment bounds `Σ_ρT^{2θ(β−½)}` by `O(T)`, a density estimate `[C]`; at `θ>1` the diagonal does not dominate and the off-diagonal is a correlation sum of μ with power saving.
4. A producer uniform in the target of the prime torus also removes the exceptional zero of a real character `[D]`; the conductor ladder shows that sizes, multiplicativity and the functional equation alone stop at rung 1 `[L*]`.
5. Return bounds are label statements shared by `ζ(s−h)` `[L]`; the transfer of S3 would make quasi-RH equal to RH `[S]`.

A proof of quasi-RH needs a source, not an assembly. The corpus fixes its form: a power saving of ζ's contacts on the integers up to a fixed power of the mass, uniform in the height, that fails for the Liouville twist and for the lattice with a pair.

---

## 4. Seventy per cent of the zeros on the line

### 4.1 Status

- `simple_critical_proportion_ge_67250071` `[L*]`: simple critical zeros `≥(0.67250071−ε)N(T)`. The constant is `HD(1)+10⁻⁸`, `HD(1)=3/2−cot(1/√2)/√2`: the rank–trace certificate of the vendored `Zeta23` package (Alpöge–Furman, Theorem D; Montgomery–Taylor window at bandwidth 1) plus the disjoint-triple pinching of `IncommensurableGaborPinching` `[M]`.
- The mechanism `[M]`: the hat-unit Gram matrix of the zeros splits as `P+Q`, `P⪰0` from the critical zeros, `Q` from the off-line pairs `{ρ,1−ρ̄}`, each a block with eigenvalues `m(g+1)`, `−m(g−1)`. At bandwidth `λ<1` the prime side is diagonal and `H(λ)=2−1/λ−λ/3`.
- `critical_proportion_or_simple_offLine` `[L*]`: for every `θ`, `N₀≥θN` or the simple off-line zeros number at least `(1+HD(1)−2θ−ε)N`. A failure of `70%` needs `(0.2725−1/A−ε)N` simple off-line zeros within `A/log T` of the line `[M]`.
- Exchange rates `[M]`: a form factor `F≤4` on `(1,10/9)` certifies `7/10`; at bandwidth `4/3` the same proportion is the trans-threshold integral `∫₁^{4/3}(4/3−α)F≤7/45`.

### 4.2 Verdict: no clear path. Three doors and what each lacks

**(i) Bounded form factor above bandwidth 1 (B150).** `F≤B` on `(1,λ)` is an upper bound of the correct order for the variance of primes in intervals of length `X^{1−1/λ}` `[D]`. Selberg's bound under RH is one logarithm larger and Goldston's positivity bound controls only an average of `F` over unit intervals `[C]`. Asymptotics for almost all shifts with a saving `log^{−A}` per shift do not reach it: the main terms cancel and a relative precision `(log X)/H` is needed `[D]`. The statement is not known to follow from RH `[C]`.

**(ii) Positivity alone.** The best bound for the trans-threshold integral from `F=α` on `[0,1]`, `F≥0` and a nonnegative pair density lies in `[1/18+47/750, 8/27]` at bandwidth `4/3` `[M]`. The threshold for `70%`, `7/45`, lies inside this interval, so the corpus neither proves nor excludes a `70%` certificate from positivity `[D]`. A single spike of the admissible mass at `1⁺` over the GUE background gives about `0.14<7/45` `[D]`; published semidefinite computations for the simple-zero problem under RH report a ceiling near `0.675` `[C]`, which predicts that a stronger adversary exists. The ceiling is a linear programme and is decidable.

**(iii) The mollified derivative at the zeros.** For the ratio `|Σ_ρζ′M(ρ)|²/(N·Σ_ρ|ζ′M(ρ)|²)` the optimum at mollifier length `T^θ` is `1−(1+θ)^{−3}`: `19/27>7/10` at `θ=½`, below the square-root threshold (`ZetaCGGMollifierOptimum`) `[M]`. Under RH this is a theorem for simple zeros `[C]`. Without RH `[D]`: with `a_ρ=ζ′M(ρ)` and `M` real,
`S₂^K:=Σ_ρ a_ρ·ζ′M(1−ρ)=Σ_{on}|a_ρ|²+Σ_{pairs}2Re(a_ρ ā_{ρ*})`,
a form that is positive on the critical zeros and hyperbolic on each off-line pair. With `a_±` the symmetric and antisymmetric parts on the pairs, `S₂^K=‖a₊‖²−‖a₋‖²` and `|S₁|²≤(N₀^{simple}+2p)(S₂^K+‖a₋‖²)`. For a close pair `ζ′(ρ*)≈−ζ′(ρ)`: the pair lies almost in the negative part, the opposite sign to the unweighted Gram matrix, where a close pair looks like a double zero. The corpus has the robust form on the subspace of mollifiers that vanish at all off-line pairs (`norm_firstMoment_sq_le_card_simple_crit`) `[L*]`, of codimension up to twice the number of pairs, which can exceed the dimension `T^θ` `[D]`. Missing: the two discrete moments as theorems for `θ<½`, and an upper bound for the displacement energy `‖a₋‖²=½Σ_{pairs}|a_ρ−a_{ρ*}|²` at census scale. Because `19/27` exceeds `7/10` by `0.0037`, the bound has to be `o(NL²)` in effect `[D]`.

Also exact and unfed: the source covariance ceiling `6π/5`; the local count of off-line zeros `[L]`.

### 4.3 What a failure of `70%` looks like `[D]`

More than `13.6%` of the ordinates carry a horizontal doublet of width `≤2A/log T`. Each doublet is one hyperbolic plane in both Gram forms, with opposite signs of its near-null direction. A certificate that uses both forms on the same family of test vectors is the natural object; none is in the corpus.

---

## 5. The one big question

### 5.1 Questions not to pose

| Question | State |
|---|---|
| B154 the exceptional square; the gap `log 4` | no gap; the sign at `log log q+C` is the least non-residue at the scale `log²q` `[L*]`/`[D]` |
| B153 almost periodic constituents | No in the Wiener class, in a half-plane and in a strip `[M]`; open in the bounded class, `0≤x<½` |
| B143, B151, A92, A95 the resolution of the minimal face | logarithmic radius in class `𝒵`; `ΓL≤nπ`; finite top layers need no separation `[L*]`/`[M]` |
| (G) one glued object for the diagonal | refuted; the diagonal is the density of a comb `[L]` |
| (S3), B148 the transfer from homogeneous breadth | it implies `Θ<1⇒RH` `[S]` |
| B131, B132, B136, B138, B139, B140 | settled in the sense posed `[L]` |
| (FP), (S1), (S2), B85, B86, B125, B142 | settled: fixed part; price `m·θ(S)`; separation is a receiver `[L]` |
| Q20 unit masses with paid contacts | exists: paying ring, planar square; Bézout by restriction is an equality there and gives no sign `[M]`/`[S]` |
| A68 landing with ζ's Gamma factor and count | not forced `[L*]` |
| The first rung past a trivial aperture, in any aspect | a classical problem in each: region `1−c/log log t`, least non-residue at `log²q`, Brun–Titchmarsh constant below `2` `[D]` |
| B152, B149, B146, B117, B87, B18 | RH or producers of RH strength |

### 5.2 Verdict

**No question below RH and quasi-RH passes the tests as a door.** The tests: not an equivalent of RH or of quasi-RH; answered by a proof or a refutation of a stated inequality, identity or implication; a consequence for either answer; not decided by a finite window; false on a corpus fake; a first step with an input that is not refuted; not a shape that is answered.

The reason is a set of theorems, not a lack of candidates.
1. Pointwise statements below rung 1 are sizes and hold for whole classes of fakes; at rung `1+o(1)` both one-structure fakes fail; the first rung above is a classical problem in every aspect (§1.3).
2. Mean values of length below the height are stable under relocation of finitely many zeros and give densities; above the height the conversion to a point is a theorem and its input is quasi-RH (§1.3, §3).
3. Structural questions about receivers are answered in Lean as fast as they are posed (§5.1); every such answer has been "a receiver" or "a price".
4. The atoms have no model with both structures (§1.2).

### 5.3 The question that would change the map: is the top of the zeros attained off the line?

> **(AAL)** If `Θ>½`, the supremum `Θ` of the real parts is not attained by a finite set of zeros: infinitely many zeros have real part above `Θ−ε` for every `ε>0`.

Equivalent form `[D]` from `[L]`: with `G(u)=e^{−(Θ−½)u}c_B(u)`, either RH holds (`G` is an almost periodic function with the frequencies of all zeros), or `G` tends to a nonzero finite trigonometric polynomial (world I), or `G→0` (world II). AAL says the middle case does not occur: if `Θ>½` the smoothed prime error is `o(x^Θ)`.

**Why this one.**
- It is implied by RH and implies no zero-free strip `[L]`; it is not a tail law and not a bounded-height law: adding or removing one isolated quartet changes it `[D]`.
- With AAL: RH ⇔ ZAL ⇔ finitely many off-line zeros ⇔ finite negative index ⇔ bounded heat counts ⇔ eventual Hadamard positivity `[L]`. The finite-stratum receivers of SC, LA, JAS, WL, PTR and the Krein–Langer index become receivers of RH, and a failure of RH is confined to a tail.
- World I is the most rigid world in the corpus: a finite layer at bounded height read by prime filters at every damping speed, a Mertens power saving, heavy returns later than `exp(c·y^{1−β′})`, a uniform negative excursion of the top trace on every window whose length depends only on the number of top quartets `[L]`/`[M]`.

**What a proof may not be `[D]`.** A mean value (relocation invariance). An identity of the explicit formula (every filtered current is the filtered zero sum). A bound for a long prime sum (controlled only through the zeros). A statement on sizes. A statement that holds for integer-norm Euler products or for entire functions with ζ's functional equation, Gamma factor and count. It has to be an inequality that uses both structures and is pointwise in the zeros; no such inequality exists in the corpus or, to my knowledge, elsewhere `[A]`.

**Tests.** Not an equivalent of RH or quasi-RH: passes. Proof or refutation: one-sided, a refutation is a refutation of RH. Consequence: above. Finite window: passes. Fakes: false on integer-norm one-offs and on functional-equation models `[L]`. First step: **fails** — the instrumented reduction ends at the signed centred type-II current at a growing isolated mode, which is the exclusion itself (B145). Answered shape: no.

It is the target, not a door. Its three sectors are B13 (bounded index), Landing and DH; none has a first step.

### 5.4 Decidable questions with a first step

Each is two-sided and none produces a sign.

| # | Question | First step | Either answer gives |
|---|---|---|---|
| 1 | **Constituents in the bounded class.** Can a bounded Dirichlet series on `Re s>x`, `0≤x<½`, have a zero and all its zeros there among those of `ξ`? | the jump law for expansions that are square summable on the left; Bohr's inequality gives absolute convergence only on `Re s>x+½` `[P]` | No: every exact arithmetic piece is excluded. Yes: an infinite set of zeros proved on the line by recurrence against density, with no sign |
| 2 | **The positivity ceiling of the census certificate** (§4.2 (ii)) | the linear programme behind `PositivityCannotReachTheThreeQuarterThreshold`, with the threshold `7/45` | below `7/45` at every bandwidth: `70%` is a theorem. Above: positivity is closed for `70%`, as it is for `75%` |
| 3 | **Polar orthogonality at the critical curve** (B104) | the isolated-pair lattice of SA, where the critical direction is `sinh(δu)e^{iγu}` and its polar pairing is explicit `[D]` | empty third case: five routes share one rank-one payment. A model with an orthogonal state: the complete matrix carries no information beyond the windows |
| 4 | **Rough packets** (SA topic 4) | bounds for `Σw(n)n^{−iτ}` uniform in `τ` from cancellation of partial sums | the prime-side exchange rate holds on all packets, or the rung law is a statement about bounded shapes only |
| 5 | **Clusters on a rung** | `zeta_companion_of_rung` with the half-period law | whether the sign on a rung is equivalent to a strip for configurations with ζ's local counts and deep zeros of density zero |

---

## 6. The one big question without positivity and without spectral theory

"Spectral" is read as spectral theory of operators in every form; "positivity" includes nonnegativity of forms, kernels, counts, coefficients and averaging measures. Kept: Fourier analysis, mean values used as bounds, exponential sums, absolute convergence, continuation, power sums, integrality, recurrence, the argument principle.

**What survives.**
- *Receivers.* RH ⇔ `|c_p|≤K` on windows, by complex deletion filters; RH ⇔ the ordinate is injective on the zeros `[L]`.
- *Three conversions from a law to a point* `[D]`, each a theorem in one setting:
  1. recurrence against density — a zero of an almost periodic object recurs with positive density, and deep zeros of ζ have density zero: constituents are pure, and in the Wiener class have no zero `[L*]`/`[M]`;
  2. budget overflow — one off-line zero costs more than a mean-value budget: long mollifiers `[M]`;
  3. winding — the index law and its semicontinuity; half-period deletion for finite layers `[L*]`.
- *The additive identity.* The jump of the fractional part: the jump law on every strip `[M]`.
- *Priced producers.* Frobenius at one prime, integrality, exponential sums, linear forms in logarithms `[L]`.
- *A census by winding.* Levinson's method uses the argument principle and a mean value as a bound. Its gate is a hypothesis in the corpus and the twisted second moment below the square root is a theorem `[M]`/`[K]`. The `0.6725` theorem uses a positive semidefinite Gram matrix and is outside the constraint.

**Verdict.** Under the constraint no question below quasi-RH passes the tests. Conversion 2 is the only one that reaches every zero of `ξ`, and its input is a rung `θ>1`. Conversions 1 and 3 reach constituents, finite layers and limits. The target is the same as in §5.3, and the absence of a first step is the same.

**The question with a first step.**

> **(C1)** Constituents in the bounded class (§5.4, row 1).

It is the last open case of the only sign-free pointwise mechanism that uses the integers additively. A negative answer leaves, among the known sign-free mechanisms, none that shares zeros with `ξ` exactly; the sign-free route to `ξ` itself is then conversion 2 alone.

**Two sign-free statements that are assemblies, not questions** (§12): a proportion of zeros on the line by Levinson's method from the twisted moment for `θ<½`; the ladder theorem of §2 row 4, whose proof uses no sign.

---

## 7. A new field for the walls

### 7.1 What exists

| What the walls call for | Programme |
|---|---|
| a surface, a diagonal, a lattice with a Hodge index | `SurfaceOfSpecZ`, `AbsoluteGeometryOfSpecZ`, `HodgeTheoryOfAFixedPart`, `ArithmeticCastelnuovoSeveri` |
| a Kähler package without a variety | `HodgeTheoryWithoutVarieties`: stars, flux, transport; fails at the top coprime stratum, the additive coupling of the multiplicative towers |
| purity at infinite rank | `InfiniteRankPurityTheory`, `InfiniteRankWeilTheory` |
| prices of mechanisms, fakes, ladders | `SelectiveArithmetic` |
| what shares zeros with `ξ` | `ConstituentTheoryOfTheZeros` |
| an isolated layer and its instruments | `ExceptionalLayerTheory`, `ZeroConfigurationGeometry` |
| both structures jointly, rigidity | `EulerFETransportTheory`, `ArithmeticWeightTheory` |
| long mollifiers, the mollified field | `MultiscaleMollifiedZetaField`, `ArithmeticProduction`, `ConjugateDiagonalGeometry` |
| returns of the prime orbit | `PrimeTorusTheory`, `TranscendenceTheoryOfThePrimeOrbit`, `CollectiveDiophantineGeometry` |
| horizons and regulators | `HyperbolicArakelovTheory`, `ArithmeticHolographyOfTheModularHorizon`, `CountingHolography` |

The walls are not walls of language. Each programme ends at the same statement, and §1.3 says which: a rung above one. What no programme contains is a source.

### 7.2 The field: parity-sensitive arithmetic at power-saving scale

| Aspect | Content |
|---|---|
| What it is about | Pointwise cancellation of multiplicative data on the integers up to a fixed power of the mass, in the range where sieve weights, bilinear norms and exponential sums are blind: between `m` and `m^{2κ}` for a conductor or a height `e^m`. The object that marks the blind range is the Liouville twin: every statement of the field holds for the true object and fails for it |
| Why the walls are this | The rung law has two sides with one rate: a saving `n^{½+γ}` in the contacts buys the rung `1/(2γ)`, a zero of depth `δ` shows at `1/(2δ)` `[M]`. The fake on the Euler side is the Liouville twist `[L*]`; parity blindness of Type I and Type II information is a theorem `[L]`; the square-root threshold of the census, of mollifiers and of the dark range is the same blindness in the mean `[D]` |
| Point of view | Parity is not a defect of sieves but an invariant: the class of statements closed under the twin involution `w↦λw`. A source is a statement outside that class. The field classifies the statements outside it by what breaks the involution |
| What breaks the involution in the corpus | (1) the pole: the sign of the polar boundary term separates the antipode `[S]`. (2) additive identities of the floor: `Λ∗1=log` selects Λ; `Σ_kF(⌊x/k⌋)=⌊√x⌋` forces λ; unit comb masses force Λ `[L]`. (3) the conductor: the Liouville twist has none `[L*]`. (4) mean values at every length: Matomäki–Radziwiłł `[L]`. None is pointwise at power-saving scale |
| Objects | twins and the twin involution; the dominated box; parity-sensitive functionals; one-structure fakes (Liouville twist, lattice with a pair); short sums `Σ_{n≤m^{2κ}}w(n)n^{−½−iτ}`; cut identities; the jump of the fractional part; exceptional characters as the one world where the involution is nearly a symmetry |
| Language | twin, parity class, parity-sensitive, source, rung, exchange rate, companion, cluster, saving at a range |
| Foundational principles | (i) A source uses both structures jointly: each one-structure fake fails at rung 1 `[L*]`/`[M]`. (ii) A source is pointwise; statements in law are exchanged at the height (§1.3). (iii) No margin: a source proves an inequality whose equality case is approached. (iv) Every mechanism is priced before it is used. (v) A source uniform in the target of the prime torus contains the exclusion of exceptional zeros; a source for ζ alone has to use the identity of the torus or the pole `[D]` |
| Criteria | P1–P8 of `SelectiveArithmetic`. In addition: it fails for the Liouville twist and for the lattice with a pair at the same rung; over `𝔽_q[T]` it reproduces square-root cancellation at short range and names what replaces the Frobenius; run in the mean it reproduces Matomäki–Radziwiłł; it does not follow from the explicit formula |
| Questions it must answer | Which additive identity of the integers is parity-sensitive at the range `(m,m^{2κ})` and not only at the range of its own length? Is there a pointwise consequence of parity breaking in the mean, under isolation of deep zeros? What is the exact parity class of the comb form at finite scale: which windows separate Λ from `λΛ`, at which margin? Does an exceptional character, if it exists, supply a source for ζ (the conductor ladder read backwards)? |
| Research topics | the twin involution on the comb lattice and on the cut system; parity-sensitive identities at short range; the rung law with clusters; the function-field calibration at short range; exceptional characters as sources; the pole as a parity breaker past rung `1+o(1)` |
| Tools it would develop | parity-sensitive bilinear decompositions; short-range forms of the cut identities; a transfer from the mean to isolated points; the ladder as a measuring instrument for every candidate |
| Built on | SA (prices, ladders, fakes), RAC and CTZ (additive identities), APR and AGT (blindness theorems, twins), MZF (the mean), ELT (isolated layers) |
| To discover | one statement outside the parity class that is pointwise at a power of the mass |

**Main conjecture.** There is a parity-sensitive inequality for ζ on the integers up to `m^{2κ}`, some `κ>1`, uniform in the height. **Milestones.** M1 the parity class of every unconditional theorem of the corpus (an atlas column). M2 a pointwise statement outside the class at rung `1+o(1)` that is not the classical region. M3 one rung above one in one aspect. M4 every rung.

**Status of the proposal `[A]`.** The area is the classical parity problem. What the corpus adds is its exact form: one rate, two fakes, no margin, the price of every known mechanism. Mathematics outside the corpus that acts on this wall, with verdicts: large values by additive energy (Guth–Maynard) — in law, imported as a corollary `[L]`; entropy decrement and nilsequence methods — savings that are not powers `[C]`; interpolation formulas for the pair of the logarithms of the integers and the zeros — identities, no location statement `[C]`; Euler systems — bounds at integer points, no statement in the strip `[C]`.

---

## 8. A new field without positivity and without spectral theory

**Conversion theory: from a law to a point, for a rigid object.**

| Aspect | Content |
|---|---|
| What it is about | The corpus proves much in law (densities, the census, mean values, typical heights, almost every fibre of the prime torus) and RH is a statement about every zero of one object without moduli. The field studies the mechanisms that turn a law into a statement at a point without a sign, their domains and their prices |
| The three conversions | recurrence against density; budget overflow; winding (§6). Each has one theorem in the corpus and no theory |
| Point of view | A conversion is a pair: an amplification of one exception (it recurs, it overflows, it winds) and a law that the amplified exception violates. The exception is a zero of depth `δ`; the law is a density or a mean value. The field computes, for each conversion, the amplification as a function of depth and scale, and compares it with the exponent of the law |
| Objects | exceptional sets of heights and their local structure (clusters, companions, energy); transport and return counts of a zero; spikes of long polynomials at a zero; budgets; indices of approximants; the hull of ζ and the identity fibre |
| Language | law, point, exception, amplification, budget, overflow, transport exponent, density exponent, index, isolation |
| Foundational principles | (i) A law never excludes; an amplified exception does. (ii) An amplification is measured against the sharpest law: `T^c` returns against `(30/13)(1−σ)` `[L]`; a spike `Y^{2δ}` against `T` `[M]`; one unit of index against one zero `[L]`. (iii) The identity fibre is special and typical at once: it continues analytically, almost every fibre has a natural boundary, and RH says it is typical for zero-freeness `[L]`/`[D]`. (iv) No sign and no operator |
| Criteria | Reprove the three theorems as one scheme. Over `𝔽_q` reduce to periodicity of the zeros in height. Fail on integer-norm one-offs (finite exceptions do not recur), on the non-tempered pair (exceptions of positive density), and on `ζ(s−h)`. Not uniform in real characters unless it excludes exceptional zeros. State the exchange with length: which conversions stay below the height |
| Questions it must answer | Is there an amplification of one zero that is unconditional below the height? What is the transport exponent of a zero of ζ: how many returns does one zero right of `σ` force? Does recurrence against density extend from uniformly almost periodic objects to objects almost periodic in the mean, when the functional equation supplies the other side of the line? Which splittings of `ξ` have a defect certified by sizes in a height window? |
| Research topics | the bounded class (C1); explicit heights for constituents of bounded length; the graded form of Bagchi's criterion with the Guth–Maynard exponent; local structure of the deep zeros; the Levinson census as a winding statement with the twisted moment in Lean; the separation proof of the Carlitz–Goss zeta function as a calibration in characteristic `p` |
| Built on | CTZ, IRP (conversions 1 and 3), CDG and MZF (conversion 2), ZCG Recurrence, SOSZ ScaleLocality, SFPM |
| To discover | an amplification that needs no length past the height; or a proof that none exists in a stated class |

**Main conjecture.** Every sign-free conversion of a law about the zeros of ζ into a statement at every zero has an input of the strength of a rung above one. **Milestones.** M1 the three conversions in one scheme with their exponents. M2 the bounded class. M3 a no-go for amplification below the height in the class of quadratic mean values, from relocation invariance. M4 a conversion outside that class.

**Status `[A]`.** No folder owns the conversions as a subject; the theorems are in five programmes. The main conjecture is a statement about methods and can be approached by classification, as the conductor ladder was.

---

## 9. A research programme for `𝔽₁`

### 9.1 Aim

Not a definition of `𝔽₁`. A geometry in which Spec ℤ has a product with itself and the inequality of Castelnuovo and Severi on that product is a theorem. The programme is `AbsoluteGeometryOfSpecZ` with `HodgeTheoryOfAFixedPart`; `SelectiveArithmetic` is its test bench.

### 9.2 What the corpus fixes

| Item | Theorem | Evidence |
|---|---|---|
| The square | `𝒢=W(ℤ)`: the Frobenius graphs glued along the primes; a curve; gluing index `N!`; no object of finite type carries the contacts | `[L]` |
| Three squares | `Spec 𝒢 → Spec T → S_q=Spec ℤ[Y]`: contacts without diagonal; a diagonal with a normal direction and a bilinear count without primitive part; no single one carries contacts, jets and a diagonal | `[M]` |
| One ring | `𝒮_q`: stable under the shifts, contains the tower, the pole plane and the jets, exact section counts; the zeros are the weights of the contacts against packets at a scale, and pointwise every weight | `[L]` |
| Paid contacts with unit masses | the paying ring `ℤ[y_p]` (graphs are lattice points with coordinates `p+…+p^{v_p(n)}`) and the planar square, glued as the trace of a regular surface on its graphs: forced values `Π_{n∈S}J(m,n)`, attained | `[M]`/`[S]` |
| The pairing | jets + contacts − counterterm `→2d₁d₂−Z(f)`; Bézout ⇔ RH; proved to an aperture below `½`; index = number of right zeros | `[L]`/`[L*]` |
| The diagonal | the density of the comb, `log(density/2π)`; `2π` is the threshold; not one glued carrier | `[L*]`/`[L]` |
| The archimedean fibre | weight lines of the same Frobenius with another Verschiebung; the jets are the even multipoles of the Newtonian kernel on an axis of `ℝ³`; the two rulings are the origin and infinity | `[L]`/`[M]` |
| The finite contacts | at each prime a sum of squares over prime chains minus the diagonal | `[M]` |
| Frobenius | a power map is a Frobenius at one prime; order `m` on `S` costs `m·θ(S)`; the functional equation is `F↔V` and preserves primes and Gamma factor | `[L]`/`[M]` |
| Carries | a cocycle that is not a coboundary; its defect is minus the defect of the window count | `[L]` |
| Sections | Riemann–Roch with Bézout on the tower is the product formula; on the planar square restriction is an equality of ideals; neither gives a sign | `[L]`/`[M]` |
| Number rings | contacts `Λ(1+ΣRe χ_i)` on the comb of norms; counterterm with the conductors as ramification, `2g_K(n)−2=d(2g(n)−2)+nR`; the index is the number of right zeros of the zeta function of the ring; the class group does not enter | `[L*]`/`[M]` |
| Curves | the comb `q^ℤ`: Toeplitz form, no jets, no counterterm, decided on `2g+1` points | `[S]`/`[L]` |
| Twisted parts | positive below the trivial aperture `log log q` for every dominated system; no information on the character there | `[L*]` |

### 9.3 What it would be like `[D]`

1. Spec ℤ over `𝔽₁` is a curve of infinite genus with a genus function, `g(n)=1+(n/2)log(n/2π)` at the degree point `n`: negative at `2, 3`, of the order of the number of zeros below the height `πn`.
2. Its Frobenius is a monoid at the finite places and a flow at infinity. No single map is a Frobenius at two primes, so there is no auxiliary polynomial with cheap vanishing.
3. Its square is of infinite type. The prime part of every off-diagonal intersection number is a contact order; the archimedean part is a jet; the diagonal is a density, not a self-intersection of a class with a normal bundle.
4. Its cohomology has infinite rank, no lattice stable under three Frobenii, weights `0, 1` (pole plane), `−2j` (jets) and `ρ`; the point count is the logarithm of the order of a fixed scheme plus a trace, and `Λ` is not a trace of any order.
5. Passing from `𝔽_p[T]` to ℤ is a deformation by the carry, and the carry is not a coboundary: `𝔽₁` does not remove it.
6. Extensions of the base are covers with ramification (the conductor), not extensions of the constant field: the zeta function of a cyclotomic ring is a product over characters, and ζ is the fixed part of every such family.

### 9.4 Criteria

| # | Criterion | Test |
|---|---|---|
| C1 | reproduces Weil and Stepanov for curves | Toeplitz comb; count law of hyperelliptic curves `[L]` |
| C2 | counts alone are not enough | the golden datum fails `[L]` |
| C3 | uses the functional equation | integer-norm one-offs fail; the Liouville twist fails at rung 1 `[L*]` |
| C4 | uses the Euler product | `cosh` models, the heat family and the lattice with a pair fail `[L]`/`[M]` |
| C5 | sees the exact normalization | the non-tempered pair fails; the constant `2π` and the weights `Λ` are forced `[L*]` |
| C6 | infinite type, no finite fibre, no stable lattice | `[L]` |
| C7 | the diagonal is the density of a comb | `[L*]` |
| C8 | positivity is derived, and not from a section count | product formula on the tower; payment on the paying ring `[L]`/`[M]` |
| C9 | selective only where a contact enters; no margin | windows of ratio `≤2` are blind `[L]` |
| C10 | on a number ring it gives the index of each character, or uses the pole plane | index law over characters `[L*]` |
| C11 | below the trivial aperture it proves nothing that the dominated box does not have | SA `[L*]` |
| C12 | at finite scale it is a statement on real divisors with finite index | HFP `[L]` |

### 9.5 Questions the programme must answer

| # | Question | State |
|---|---|---|
| 1 | Bézout for the comb pairing from a property of the object | RH; no property known that turns a count into an inequality between graphs on different lines |
| 2 | What replaces "ample class and Riemann–Roch imply the Hodge index"? | on the tower both axioms give the product formula `[L]`; the Kähler package of the divisibility complex exists except at the top coprime stratum, where hard Lefschetz along the overlap flow is RH (HWV) `[M]` |
| 3 | Is there a geometric object whose intersection form is the sum of the chain squares at every prime and the Newtonian multipoles on an axis, with the density as counterterm? | each summand has a model (trees at the Ramanujan point, `ℍ³` Green function, a comb); no glued invariant object `[L]` |
| 4 | What replaces extension of constants, the tensor-power trick and the family? | nothing among covers and twists: fixed part; a cover bounds its base `[L*]` |
| 5 | The full window at finite scale, and the converse | block averages decide `[L]`; nonzero block sums open (B152); converse open (A80) |
| 6 | Integer-norm systems on their own comb: does Bézout there hold exactly when the zeros are on a line? | open (AGZ §13.3); a separated comb stable under the Frobenius monoid is one orbit, so the comb of ℤ has no moduli `[L]` |
| 7 | Ideals as degree points; class-group characters; non-abelian rings | Hecke and Artin explicit formulas are not in the corpus |
| 8 | A count with Tate limit the integer probes | RH ⇔ such an `ℕ`-count exists `[L]`; no construction |
| 9 | The Li ladder as comb forms of tails | open (A82) |

### 9.6 Constructions for the next stage, with kill conditions

| Construction | Deliverable | Kill condition | State |
|---|---|---|---|
| I. A Lefschetz operator on the comb lattice | an operator on the real divisors of a window with Hodge–Riemann at a base point and transport that is not RH | every candidate has hard Lefschetz equivalent to RH | met for dilation, overlap flow and coupling Laplacian (HWV) `[M]`; other operators untested |
| II. The archimedean fibre as a boundary | the jets as the trace on an axis of a harmonic object in `ℝ³` or `ℍ³`, glued to the trees so that the glued form is the comb form | every invariant gluing has a constant degree diagonal | met for adelic-invariant kernels `[L]`; non-invariant gluings along a comb open |
| III. Stepanov on the planar square | a section of small height vanishing on the graphs of a window, nonzero on `Γ_1` | the forced value is the full product of the contact ideals and is attained, so vanishing is paid exactly | met (`planarValues_eq_prod`, `exists_planar_vanishing`) `[M]` |
| IV. Squares of towers | the index law for the squares of the rings of a tower with bounded root discriminant; the limit form per degree | the form of ζ has weight `1/[K:ℚ]` in the limit | expected met `[D]`: fixed part |
| V. The own comb | the pairing of an integer-norm system on its own comb | the jets of a non-lattice comb are not an archimedean factor; the pairing is not a zero sum | open |
| VI. A count | natural numbers `K_p(m)` on the rays `Γ_1+Γ_p` with quadratic Tate limit | no definition without the form | open |

### 9.7 Tools, objects, language, mechanisms

- **Built on.** Witt vectors and Λ-structures; necklace coordinates; comb finite parts and the normal form; Hardy squares and chain squares; the index law; combs of norms; the conductor ladder.
- **Language.** square, graph, contact, jet, comb, density, counterterm, genus at a degree point, ramification, twisted part, rung, paying ring, planar sequence.
- **To discover.** One property of the square that is an inequality: a positive class whose positivity is not the statement to be proved. Every structure in the corpus is an identity (product formula, complementary carry, payment of contacts) or a receiver.

### 9.8 Order of work

1. Close IV as a theorem (kill); III is closed.
2. II for non-invariant gluings along the comb of the integers; V for one integer-norm one-off.
3. I with one operator outside the three tested ones, on the first selective window (ratio between `2` and `3`, one contact).
4. Hecke characters and one non-abelian ring.

**Decisive test.** A construction whose Bézout holds for an integer-norm system with an off-line pair, for the Liouville twist at rung 1, or for a wrong constant, is wrong `[L*]`.

---

## 10. A research programme for a Galois theory of the zeros

### 10.1 The statement

For a curve over `𝔽_q` the Frobenius eigenvalues are roots of a polynomial over ℤ; `ι: α↦q/α` commutes with the Galois group, complex conjugation `c` is one element of it, and RH is `c=ι`. For ζ, with `ι: ρ↦1−ρ` and `c: ρ↦ρ̄`:

> RH ⇔ `c=ι` on the zero set ⇔ `ιc`, which preserves the ordinate, is the identity ⇔ the ordinate is injective on the zeros `[L]`.

The two involutions are declared as permutations of the zero carrier in the corpus (`zetaZeroConjPerm`, `conjEquiv`, `fesEquiv`).

### 10.2 What the corpus fixes

| Ingredient of a Galois theory | Over ℤ | Evidence |
|---|---|---|
| An equation of finite degree | none: no finite-rank integral model, no lattice stable under three Frobenii, `Λ` is not a trace of any order | `[L]` |
| An algebraic differential or difference equation | none: ζ is hypertranscendental over the field generated by Gamma and theta functions; algebraic dilates are differentially independent | `[L]` |
| Factors (reducibility) | none in the Wiener class: no Dirichlet polynomial is a factor; no absolutely convergent Dirichlet series is a constituent with a zero | `[L*]`/`[M]` |
| A cyclic symmetry in height (the Frobenius of a curve) | none: no vertical progression or half progression of zeros | `[L]` |
| An invariant valuation that separates the roots | the mechanism is a theorem (an invariant function injective on the roots puts them in the base field); by absolute value it is excluded for ζ; the ordinate separates iff RH | `[M]`/`[L]` |
| Covers | the zeros of the zeta function of an abelian ring are graded by characters; the index of its square is the sum over the characters; a cover bounds its base | `[L*]`/`[M]` |
| Finite approximants | Jensen polynomials: the non-real root count `N_d` is nondecreasing with supremum the off-line multiplicity, `N_d≤300√(d log d)` | `[L]` |
| A calibration where separation proves purity | the Carlitz–Goss zeta function: digit calculus and carry recursions in Lean; general optimality of the greedy composition open | `[S]` |

### 10.3 Six meanings of "the equation", and the group of each

| Reading | Roots and group | What it can and cannot do |
|---|---|---|
| A. The trace form | the algebra of functions on the zero set with the involution `f*(s)=conj f(1−s̄)`; Hermite's theorem: the signature of the trace form counts the roots fixed by `ιc` | this is Weil's form; its negative index on packets is the number of right zeros `[L*]`. It sees `c`, and it is a sign |
| B. The torus of the zero motive `[D]` | character group the ℤ-span of the zeros modulo their linear relations; the flow `t↦(e^{tρ})_ρ`; the Frobenius at `p` is the time `log p` | RH ⇔ every character has the same absolute value on the flow. The group is as large as the relations allow; a large group proves nothing (golden datum `[L]`) |
| C. Artin's formalism | for a Galois ring with group `G` the orders of vanishing of the Artin `L`-functions at a point form a virtual character of `G` `[C]` | `G` acts on multiplicity spaces of a cover, not on the zeros of ζ; ζ is the trivial isotypic part |
| D. Differential Galois theory | relations among ζ and its derivatives | there are none `[L]`: the group is everything |
| E. The `p`-adic zeta function | its zeros are the characteristic roots of a Galois group acting on a module over the Iwasawa algebra `[C]` | the one setting where zeros of a zeta function of ℚ are roots of a characteristic series of a Galois action; no purity statement there, and no bridge to the complex zeros; absent from the corpus |
| F. Jensen polynomials | real polynomials of degree `d`; `c` has `N_d/2` transpositions; the sign of the discriminant is `(−1)^{N_d/2}` `[D]` | a parity invariant of the off-line count computable from coefficients; it does not locate `c` |

### 10.4 Criteria

1. Over `𝔽_q` it reproduces the hyperoctahedral group and the centrality of `c`.
2. It locates `c`; it does not measure the group.
3. It is pointwise: an invariant that holds at one zero of an orbit holds on the orbit, and the first zeros are on the line `[L]`. It succeeds if "on the line" is such an invariant and the group is transitive.
4. Integrality enters as trace integrality with an archimedean size, because no lattice exists.
5. It contains the separation proof of the Carlitz–Goss case, and names the archimedean substitute for a Newton polygon; coefficient gaps are excluded `[L]`.
6. It does not follow from a statement that holds for entire functions with ζ's functional equation, Gamma factor and count `[L*]`.

### 10.5 Questions

1. **Relations.** Which ℤ-linear relations hold among the zeros beyond `ρ+(1−ρ)=1`? The torus of reading B has the dimension of the answer. The corpus has the parity of ordinate relations and annihilator masses `[L]`.
2. **Ground field.** Over which field generated by prime-side data are the power sums of the zeros in a rectangle defined, and is the group of the local Weierstrass polynomial the full hyperoctahedral group?
3. **Location of `c`.** Is there a generating set of that group whose elements commute with `c` for a structural reason?
4. **The separating invariant.** The fibre spread of the height map is twice the width `[L]`. Which prime-side computation proves injectivity of the ordinate on one rectangle without locating the zeros, uniformly in the height?
5. **Covers.** For a non-abelian Galois ring, is the virtual character of the off-line zeros at a point constrained beyond the cyclic restrictions `[C]`? In the corpus: does the index law hold character by character for Artin `L`-functions?
6. **The `p`-adic side.** Is there one object whose characteristic series at the place `p` is the `p`-adic zeta function and whose trace at the archimedean place is the explicit formula?
7. **Discriminants.** Is the sign of the discriminant of the Jensen polynomials of `Ξ` eventually constant in the degree at each shift?
8. **Irreducibility.** Past the Wiener class: the bounded class (C1 of §6); limits of approximants (index-one limits give RH `[L]`).

### 10.6 Tools, objects, mechanisms

- **Tools to develop.** Galois theory of local Weierstrass polynomials with coefficients given by contour integrals; conjugacy of zeros of a Dirichlet series with a functional equation; the trace form at infinite rank with the index law; Heilbronn-type characters for the index; the digit calculus with a nonzero carry; discriminants and resultants of Jensen polynomials.
- **Objects.** the zero algebra with its involution; the torus of the zero motive with its flow; the squares of Galois rings; Jensen and Weierstrass polynomials; the Iwasawa module.
- **Mechanisms to discover.** An archimedean invariant of the symmetry that separates the roots; or a location of `c` that does not pass through the sign of the trace form.

### 10.7 Limit

In finite rank the centrality of `c` is a consequence of purity. Galois theory proves purity only through an invariant valuation, and that is non-archimedean. Reading A is the only one that sees `c`, and it is Weil's sign.

---

## 11. A research programme under the assumption that RH is false

### 11.1 What a failure is

| | World I (¬AAL) | World II (AAL ∧ ¬ZAL) |
|---|---|---|
| Shape | a finite top layer at `β=Θ<1`, at bounded height | infinitely many zeros with real part tending to `Θ=Θ∞>½` |
| Forced `[L]` | a zero-free strip above some height; `M(x)=O(x^{β′})`, `β′<1`; the normalized prime error tends to a nonzero finite trigonometric polynomial `[D]`; a uniform negative excursion on every window of a length set by the number of top quartets `[M]`; filters read every top residue | deep zeros of density zero; nothing else |
| A counterexample | canonical: the layer is definable from the primes | no zero is distinguished |

Every failure satisfies, without hypothesis: ordinates above 67 `[L]`; depth below `½` by the Vinogradov–Korobov margin `[L]`; at most `T^{(30/13)(1−σ)+ε}` zeros right of `σ` `[L]`; at least `67.25%` of the zeros simple and on the line `[L*]`; each off-line zero gives an explicit positive lower bound for the de Bruijn–Newman constant, quadratic in the depth `[L]`; every late logarithmic window has a prime that violates the floor outside every power-thin set `[L]`; at every large scale some window has a real divisor of bounded norm with comb form `≤−ε` `[L]`; beyond some aperture no weight system is feasible (`exists_aperture_forall_not_combBezoutAt`) `[L*]`; the intersection form on packets has `1+κ` positive squares, `κ` the number of right zeros `[L*]`, an even number because ζ has no real zero in the strip `[D]`.

### 11.2 Certificates

A refutation exhibits one finite object. Each row is an equivalence in Lean.

| Certificate | Statement |
|---|---|
| A dual certificate at one aperture | a nonnegative mixture of autocorrelations supported in `[−2a,2a]` that vanishes at `±log n`, `n≤e^{2a}`, with negative archimedean-plus-pole energy; exists iff RH fails `[L]`/`[L*]` |
| A divisor | a real divisor on `(N,QN]` with negative comb form in the limit sense of HFP `[L]` |
| A collision | one multiple zero of `H_t` at one `t>0` (`not_riemannHypothesis_of_multiple_zero`) `[L*]` |
| A polynomial | one Jensen polynomial of `Ξ` with a non-real root `[L]` |
| A number | a negative Li coefficient `[L]`; a failure of Robin's inequality at one `n>5040` `[C]` (the corpus has the eventual criteria at `lcm(1,…,n)` and at colossally abundant numbers `[L]`) |
| A prime | none: a single violation of the floor at one prime decides nothing; a violation in every late window does `[L]` |

### 11.3 (a) Proving RH wrong

Three strategies, each with its obstacle.

1. **A clash.** Find a consequence of RH that an unconditional theorem contradicts. The corpus supplies the sharpest consequences: every window positive with a margin that decays doubly exponentially; the feasible cone pinned to `Λ`; every `H_t`, `t>0`, with simple real zeros; the form factor equal to `α` on `[0,1]`. It supplies the unconditional theorems of §1.4. No pair clashes: every unconditional theorem is a size, a law or an identity, and RH is consistent with all three kinds `[A]`. A clash needs the same source as a proof, used in the other direction.
2. **World I by existence.** Prove that the normalized prime error does not tend to zero and that `Θ>½`. This is ¬AAL together with ¬RH; the instruments of `ExceptionalLayerTheory` read a layer and do not produce one.
3. **A dual certificate by construction.** At one aperture `a₀` exhibit the blind mixture with negative energy. The energy is linear on a convex cone defined without primes except through the nodes `log n`; the cone at aperture `a` has finitely many node conditions. The exact blind test of the corpus (transform `Ξ` times a zero-free factor) has energy `0` and lies in the radical, so it certifies nothing `[D]`. A certificate has to be found at an aperture beyond `½`, and below `½` none exists `[L]`.

**Criteria.** The method fails over `𝔽_q` and on the Lagarias–Suzuki pencils for `1≤Y≤4πe^{−γ}`, where purity is a theorem `[L]`. It succeeds on the fakes: it finds the off-line zeros of an integer-norm one-off, of the lattice with a pair, of the non-tempered pair, from their prime data alone. It respects every constraint of §11.1.

### 11.4 (b) A concrete counterexample without computation

- **In world I the counterexample is a limit formula.** `β=limsup log|ψ_B(x)−x|/log x`; the ordinates are the frequencies of the limit of `x^{−β}(ψ_B(x)−x)` in `log x`; multiplicities are its amplitudes; prime-only filters recover each residue at every damping speed `[L]`. A proof of ¬AAL is a concrete counterexample in this sense, and the first violation of Robin's inequality along the colossally abundant numbers is determined by the top trace `[D]`.
- **In world II** a counterexample is a sequence, and a proof is a statement of the form "for every `ε` a zero with real part above `Θ−ε` exists". The receiver side gives one: failure of the floor in every late logarithmic window.
- **Without naming a zero.** A dual certificate at one aperture, or one collision of the heat flow at a positive time.

### 11.5 Objects, language, tools

- **Objects.** top layers, tails, the normalized prime error, dual cones of blind mixtures, feasible cones, collisions of `H_t`, the negative subspace of the comb lattice.
- **Language.** world, layer, certificate, blind mixture, collision time, first failing aperture, index.
- **Tools.** the filters and currents of ELT; half-period deletion; the duality of feasible weights; the heat flow near time zero; the exact index theorem.
- **To discover.** A reason for a collision at a positive time, or for an isolated top; neither has a candidate.

### 11.6 Assessment `[A]`

The programme is the mirror of the proof programme. Every certificate is an equivalent of the failure, every strategy needs the source that a proof needs, and the corpus contains no asymmetry between the two directions: no unconditional theorem is closer to contradicting RH than to proving it. The useful output of this programme is the list of §11.1, which any model or argument about a failure has to satisfy.

---

## 12. Missed opportunities

### 12.1 Assemblies of proved pieces

| # | Assembly | Inputs | Effect |
|---|---|---|---|
| 1 | **The ladder theorem.** One statement with the rate `depth=1/(2κ)=1/(2θ)`: cancellation `γ` ⇒ sign to `κ<1/(2γ)`; a bounded dyadic moment at `θ>1` ⇒ depth `<1/(2θ)+ε` eventually; slope `<1` of the long Möbius moment ⇔ quasi-RH; the sign on a rung ⇒ no isolated zero of depth `>1/(2κ)` | `exists_cancellation_margin`, `zeta_companion_of_rung`, `TwoSidedThetaMollifierTrap`, `LongMoebiusSecondMomentRigidity`, `quasiRH_crossRoute_seven_way_tfae` | the seven-way list of quasi-RH gains the mollifier and aperture forms; the cluster hypothesis that separates a rung from a strip is explicit |
| 2 | **A positivity-free census.** Discharge the Levinson mean-square gate with the twisted second moment for `θ<½` | `LevinsonProportionGate`, `TwistedSecondMomentsBelowSquareRoot`, `TwistedPairsBelowSquareRoot` | a proportion of critical zeros proved by winding and mean values; the first census under the constraint of §6 |
| 3 | **The positivity ceiling.** The linear programme behind the `75%` no-go at the threshold `7/45`, at every bandwidth | `PositivityCannotReachTheThreeQuarterThreshold`, `SeventyPercentExchangeRates`, `fejer_shifted_bound_gap` | `70%` as a theorem, or positivity closed for `70%` |
| 4 | **The Krein form of the mollified derivative.** `S₂^K=‖a₊‖²−‖a₋‖²`; `|S₁|²≤(N₀^{simple}+2p)(S₂^K+‖a₋‖²)`; a close pair lies in the negative part | `ZetaCGGMollifierOptimum`, `OffLineAnnihilatingWeightsCountCriticalZeros`, the rank–trace slack of `Zeta23TheoremASpectralSlack` | a second Gram form in which an off-line doublet has the opposite sign; names the displacement energy as the one missing bound for `19/27` |
| 5 | **The trichotomy of the normalized prime error.** RH, a nonzero finite trigonometric limit, or limit zero | `exists_expansion_of_top`, `FiniteModeWindowLength`, the sector theorem | AAL as a statement on one function; the world of a failure is read from the primes |
| 6 | **B13 in index form.** B13 ⇔ the negative index of the defect of the comb pairing on packets is `0` or infinite | `exists_le_negIndex_ringDefect_iff` for ζ alone | one lattice statement for the bounded-index sector; in world I-a the intersection form has `1+2k` positive squares, `k` the number of quartets |
| 7 | **The exchange between verification and aperture.** The explicit `windowHeight(a)` is an iterated exponential; the visibility laws make heights up to about `e^{2a}` necessary; the height aspect suggests `exp(e^{a+η})` as sufficient, and `exp(e^{(1−2ε)a})` under a strip of width `ε` `[D]`. Determine the order | `windowHeight`, `exists_height_margin`, the visibility laws | the window routes at bounded mass as verification with an exact exchange rate; a stage step is a zero-free strip |
| 8 | **The depth sum with a constant.** `Σ_{β>½}(β−½)≤cT` with `c` from the mollified moment at `θ<½` and Littlewood's lemma | MZF moments, `exists_logIntegral_le_of_secondMoment` | the inner field bound of AIF with an explicit constant |

### 12.2 Published inputs whose formalization changes a status `[C]`

| Input | Effect |
|---|---|
| Twisted second moments for general coefficients past `θ=½` (to `17/33`), and to `4/7` for Möbius-type coefficients | the first rungs past the square root on the mean-value ladder; density near the line with exponent `2θ` |
| The two discrete mollified moments of `ζ′` at the zeros for `θ<½` | the Krein census of row 4; under RH the proportion `19/27` |
| Selberg's bound for the variance of primes in short intervals under RH; Goldston's average bound for the form factor | the exact position of B150 relative to RH |
| Interpolation formulas for the pair of the logarithms of the integers and the zeros | a sign-free duality statement for §8; no location statement known |
| The main conjecture for the `p`-adic zeta function | reading E of §10.3 |

### 12.3 Routes and tasks that the theorems of the corpus close

| Item | Reason | Recommendation `[A]` |
|---|---|---|
| Calibrations of B13, Landing, DH | every model drops a structure; with both structures the class is ζ `[L]`/`[L*]` | stop building models of atoms; the three model theorems are the scope statement |
| Exact arithmetic pieces that share zeros with `ξ` (W1C by factors, PTR and PM pieces) | no constituent in the Wiener class; limits of box constituents lose their zeros `[M]` | closed except the bounded class |
| The first rung of any ladder as an "open door" | a classical problem in each aspect (§5.1) | treat as targets; no work without a source |
| Sections, Riemann–Roch and Stepanov on any ring of sections of the square | product formula on the tower; equality of ideals on the planar square `[L]`/`[M]` | closed |
| Covers and families as producers | fixed part; index additive over characters; a cover bounds its base `[L*]` | support only |
| The transfer of S3 | at least the strength of `Θ<1⇒RH` `[S]` | closed |
| Stage steps of the window tower; theta ranks one at a time | verification (row 7); the frozen floor tower `[L]` | one rung per verified height; no induction without a strip |
| Scheduled sums (FU, CFC, RP); source completions (SEC, CDC, APF, EWJ, RFHM, WBF) | exact criteria, no estimate on advancing histories; one condition per zero | frozen |
| Positivity alone for the census | closed at `75%` `[L]`; at `70%` decided by row 3 | decide, then close or prove |
| Mean values of length below the height as detectors of single zeros | relocation invariance `[L]`; the conversion needs `θ>1` `[M]` | density and census only |

---

## 13. Answers in one line each

1. **Big picture.** One inequality per prime and one matrix on the integers, with no margin; the corpus has every receiver, the price of every known mechanism, and the exact scale of what is known: sizes, below rung 1. Standing: a source above rung 1 (a parity-sensitive, joint, pointwise power saving), and the atoms ZAL, B13, Landing.
2. **Opportunities.** Constituents in the bounded class; the census past the diagonal; a positivity-free census; the ladder as one theorem; none closes a wall.
3. **Quasi-RH.** No clear path: it is one rung above 1, one bounded long mollifier moment with `θ>1`, a power-saving variance of μ in long intervals; no rung between the proved range and it on the pointwise ladder.
4. **Seventy per cent.** No clear path: `67.25%` is a theorem; three doors, each missing one input; whether positivity alone reaches `70%` is undetermined in the corpus and decidable.
5. **One question.** No question below RH and quasi-RH is a door. The target is AAL — is the top of the zeros attained off the line — and it has no first step; the decidable questions with a first step are listed in §5.4.
6. **Without positivity.** The same verdict; three sign-free conversions from a law to a point exist; the question with a first step is constituents in the bounded class.
7. **New field.** The walls are not walls of language; what is missing is a source: parity-sensitive arithmetic at power-saving scale.
8. **New field without positivity.** Conversion theory: recurrence against density, budget overflow, winding, as one subject with exponents.
9. **`𝔽₁`.** The square, the ring, the lattice, the genus and the paid contacts exist as theorems; open is one property that is an inequality; six constructions with kill conditions.
10. **Galois theory.** RH ⇔ `c=ι` ⇔ the ordinate is injective; no equation, no factor, no periodicity, no lattice; the reading that sees `c` is the trace form and is Weil's sign.
11. **RH false.** Two worlds and a list of constraints; certificates are finite and equivalent to the failure; in world I the counterexample is a limit formula in the primes; no asymmetry toward a refutation is visible.
12. **Missed.** Eight assemblies (the ladder theorem, a positivity-free census, the positivity ceiling, the Krein census, the trichotomy, B13 in index form, verification as a rung, the depth sum) and ten closures.
