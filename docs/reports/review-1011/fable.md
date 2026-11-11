# Consolidated review — big picture, obstacles, questions, programmes

**Sources.** [Frontier map](../rh-current-frontier-map.md), [scoped obstructions](../rh-killed-routes.md), [unification ledger](route-unification-ledger.md), [route obstacles](route-obstacles.md), [walls ledger](walls-ledger.md), [obstacles summary](obstacles-summary.md), the programme READMEs under `formal/GaloisForLFunctions/`, the pipeline cards (among them the quasi-RH and metaplectic cards), the cached external text of `[X]`, and the Lean corpus through `scripts/formal_tools.py research`. Corpus checkpoint `bde2b99c84` with its working tree. Working log: `logs/review-1011-fable-report.md`.

**Evidence.**
- `[L*]` Lean statement read for this report. `[M]` module docstring read, statement not re-read.
- `[L]`, `[K]`, `[S]` as graded in the frontier map: integrated Lean; Lean with transitive axiom audit; source present, unfinished or unintegrated.
- `[P]` paper proof on a pipeline card. `[D]` deduction made in this report, not a Lean theorem. `[A]` assessment.
- `[C]` published mathematics quoted from memory; not in the corpus and not checked against a source. Every `[C]` item needs a check before it is used.
- `[X]` a theorem of an external source that is cached in the repository, outside the native import graph, and not checked for this report. One source carries this tag: the zero-free half-plane `Re s>7/8` described below.

**Where the five ledgers and the corpus differ.**

| Ledger row | Corpus |
|---|---|
| Σ156, B154: the exceptional square is open, gap `log 4` | no gap: the trivial aperture of a conductor is `log log q+o(1)`; every dominated system is positive below it with margin, the Liouville twist fails above it (`exists_trivialAperture_margin`, `tendsto_trivialAperture_sub_log`) `[L*]` |
| Γ212, B153: bounded Dirichlet constituents | `bounded_dirichlet_constituent_ne_zero` excludes zeros for every half-plane boundary `[M]`; the existing strip theorems cover absolutely convergent ordinary Dirichlet series and expansions over the positive rationals (`LSeries_ne_zero_of_strip_zeros_subset_xi`, `expansion_ne_zero_of_strip_zeros_subset_xi`) |
| A68: a landing calibration with ζ's Gamma factor is missing | `exists_riemann_gamma_counting_model_without_landing` `[L*]` |
| A92, A95, B151: prime-side resolution law, finite layers | `sign_interval_resolution` (`ΓL≤nπ`) `[L*]`; `FiniteTopLayersNeedNoSeparation` `[M]` |
| A97, A98, A99, A100, A101 open | Newtonian multipoles and chain squares `[M]`; feasible squares at every aperture `[L*]`; jump-tail floor `[M]`; trivial aperture with uniform constant `[M]`; repulsion margin `[S]` |
| Q20 of §2.14: an object with unit masses and paid contacts | the paying ring `ℤ[y_p]` and the planar square (`TheEulerFactorsOfTheDivisorSumPayEveryContact`, `ThePlanarSquareHasTheContactsOfTheSquareAndPaysThem`) `[M]`/`[S]`; on the planar square the values on `Γ_m` of the sections vanishing on a finite set `S` are exactly the product of the contact ideals (`planarValues_eq_prod`) `[M]` |
| §2.13: genus function and Riemann–Hurwitz as readings | `TheCountertermOfANumberRingObeysRiemannHurwitz` `[M]`; the index of the square of an abelian ring equals the number of right zeros (`exists_le_negIndex_ringDefect_iff`) `[L*]` |
| S3: the transfer is open | the transfer implies `Θ<1 ⇒ RH` (`HomogeneousReturnTransferImpliesStripCollapse`) `[S]`; RH implies the transfer, and under `Θ<1` the transfer is equivalent to RH (`homogeneousReturnWindowTransfer_iff_riemannHypothesis`) `[L*]` |
| A zero-free half-plane is an unproved strength class (`≥qRH`); `Θ<1` is a missing premise (S3, JAS, WL) | `[X]`: `Θ≤7/8` as an external theorem; a local programme for its arithmetic (`MetaplecticMobiusDescent`) and exact Lean analyses of its boundary (`QuasiRHDetectorScaleBudget`, `QuasiRHDetectorGramTradeoff`, `TheSevenEighthsGeometryIsAVertex`) `[M]`. The JAS capstones carry no premise (`riemannHypothesis_iff_jasDressedPSD_one`) `[L*]`, and under `Θ<1` the S3 transfer is RH `[L*]` |

**A zero-free half-plane outside the native graph `[X]`.** The five ledgers do not mention it. The repository holds a source that states a zero-free half-plane as a theorem: *The Quasi-Riemann Hypothesis: a zero-free half-plane `Re s>7/8`* (OpenAI, dated 30 September 2026; text in `logs/review-2410-current-audit/quasi-rh-seven-eighths.txt`; Lean sources in `tmp/hgt-openai-math/quasirh-source`, not built in this repository). Statement: no finite-order Hecke `L`-function over `ℚ(√−3)` and no Dirichlet `L`-function, ζ included, has a zero in `Re s>7/8`; its Part I gives `11/12`. The cards `quasi-rh-fixed-strip-improvement` and `metaplectic-mobius-descent` treat it as the accepted upstream baseline, keep it outside the native import graph and add no axiom for it. `MetaplecticMobiusDescent` (104 files) formalizes its arithmetic and the residue of the cubic Eisenstein family; the theta identification, the removal of cube indices and the uniform transfer estimates are open there `[M]`. This report did not check `[X]`. Every statement that depends on it carries the tag, and the native state stands beside it.

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
- With `[X]`, `Θ≤7/8`: world II at `Θ=1` does not occur, and a failure of RH is a top layer at `β≤7/8` or a tail approaching `Re s=Θ∞≤7/8`. Under any half-plane bound the positivity abscissa of the dressed lag aggregate is `0` or at least `½+Θ`, and RH ⇔ `JasDressedPSD 1` with no premise (`riemannHypothesis_iff_jasDressedPSD_one`) `[L*]`; positivity on the characters of large primes at a level `σ∈[1,3/2]` is the half-plane `Re ρ≤σ−½`, in both directions up to `ε` (`xiZeroHalfPlaneBound_of_jasDressedPSDAbove`, `jasDressedPSDAbove_of_xiZeroHalfPlaneBound`) `[L]`: the levels of the aggregate and the half-planes are one scale.
- The atoms are properties of ζ alone `[D]`. Each calibration class drops one structure: integer-norm Euler products carry finite top layers and approaching remainders `[L]`; an entire function with the Riemann functional equation, the Riemann Gamma factor, residue one at `1` and the zero count of `ξ` within one has every zero off the line, approaching it, and violates Landing `[L*]`. A Dirichlet series with ζ's functional equation is a multiple of ζ `[L]`. So no model with both structures exists on which an atom can be tested.

### 1.3 The ladder: what is known is sizes

`SelectiveArithmetic` puts every sign statement on one scale. A system has a mass `m` (log conductor; log height of a modulated packet; both add) and a packet an aperture `a`. The rung is `κ=a/log m`.

| Fact | Evidence |
|---|---|
| Below rung 1 the mass pays every dominated contact system `\|w\|≤Λ`: twisted parts of real and complex characters, with margin `½(1−e^{−η/2})log q∫f²` at `a≤log log q−η`; Weil's form of ζ on packets of bounded shape at height `t`, `a≤log log\|t\|−η` | `exists_trivialAperture_margin`, `exists_height_margin` `[L*]` |
| At rung `1+o(1)` both one-structure fakes fail: the Liouville twist (Euler product, no functional equation) and the lattice with one pair (functional equation, no Euler product) | `tendsto_trivialAperture_sub_log` `[L*]`; `isolatedPair_neg_of_rung` `[M]` |
| Prime side of the exchange rate, both directions: partial sums `≤Cn^{½+γ}` buy the sign up to `κ<1/(2γ)` on bounded shapes; the sign at aperture `a` with margin on the two polar packets bounds the Riesz mean of the contacts at `Y=e^{2a}` by `√Y(3log q+C log³Y)` | `exists_cancellation_margin`, `exists_riesz_le_of_polar_nonneg` `[M]` |
| Zero side: an isolated pair of depth `δ` shows at `κ=1/(2δ)`; positivity at aperture `κ log m` forces a second off-line zero within `m^κ` of a zero of depth `>1/(2κ)` | `isolatedPair_nonneg_of_rung`, `zeta_companion_of_rung` `[M]` |
| The classical zero-free regions, Landau–Page and Siegel sit at rung `1+o(1)`; a strip of width `ε` is rung `1/(1−2ε)`; RH is every rung | SA atlas `[M]` |

**Two ladders, one rate `[D]`.** The mollifier ladder of `ConjugateDiagonalGeometry` and `MultiscaleMollifiedZetaField` has the same exchange rate. Dyadic boundedness of `∫_T^{2T}|ζΨ|²` for prefix-cancellation mollifiers of length `≥T^{θ₁}` forces `|Re ρ−½|<1/(2θ₁)+ε` for all but finitely many zeros; cofinal boundedness for unbounded `θ` is RH; the growth exponent of `∫_1^T|ζM_{T^θ}|²` has slope `2·width` in `θ` (`TwoSidedThetaMollifierTrap`, `LongMoebiusSecondMomentRigidity`) `[M]`. Depth `1/(2κ)` on the aperture ladder and depth `1/(2θ)` on the mollifier ladder are one axis.

| Axis | Kind of statement | Proved | Quasi-RH | RH |
|---|---|---|---|---|
| aperture rung `κ` | pointwise, every height | natively `κ<1` (sizes), classical regions at `1+o(1)` `[L*]`; with `[X]` the rung `4/3` in the height and conductor aspects | one `κ>1` | every `κ` |
| mollifier exponent `θ` | mean value over `[T,2T]` | `θ<½` with both gcd main terms `[K]`; `17/33`, `4/7` `[C]` | one `θ>1` | unbounded `θ` |
| resonator length `κ` at an abscissa `σ∈(½,1)` | mean value of `\|Rζ\|²` over `[T,2T]`, arbitrary coefficients | the full convolution diagonal for every `κ<2σ−1`, with error `η·Σ\|r_m\|²` uniform in the coefficients (`eventually_resonatorMean_zeta_uniform`, working tree) `[L*]`; the admissible length is `0` on the line | — | — |
| breadth of heavy returns of the primes `≤y` | pointwise, every height | none while `log t≤(log y)^{3/2−ε}` `[L]` | — | — |

Two consequences `[D]`.
1. Natively no rung of the pointwise ladder is proved in `(1,∞)`, and every candidate first step by sizes is a classical problem: the region `1−c/log log t` (height), the least non-residue at the scale `log²q` (conductor), a Brun–Titchmarsh constant below `2` (family). `[X]` gives the rung `4/3` in the height and conductor aspects at once, with no exceptional zero right of `7/8` and least quadratic non-residue `≤C(log p)^A`. Its source is not a size. Over `ℤ[ω]` the cube of the normalized cubic Gauss sum of a squarefree primary ideal is its Möbius value times a phase (`CubingTheCompositeGaussSumRecoversMobius`) `[M]`; a completed cubic theta sum has two exact representations, and the reciprocals of a whole family of Hecke `L`-functions are continued across the rightmost zeros of the family `[X]`.
2. On the mean-value ladder rungs exist below `θ=1` and each is a density or census statement. Above `θ=1` the conversion from a mean value to every zero is a theorem: one off-line zero contributes a spike `Y^{2δ}` that exceeds the whole budget `T`. The conversion costs length past the height.

### 1.4 Hard obstacles that are solved

| Obstacle | What is a theorem | Anchor |
|---|---|---|
| Many routes | one inequality per prime; one matrix; route classes by source identity | SOSZ, AGZ, HFP `[L]` |
| Global data in the decision step | logarithmic windows with power-thin exceptions; `√T` windows; two primes; counts on windows; one-sided upper side `[S]` | SOSZ ScaleLocality `[L*]`/`[L]` |
| A decision without positivity | `\|c_p\|≤K` on windows by complex deletion filters; RH ⇔ ordinate injectivity | SOSZ, SignFreePurityMechanisms `[L]` |
| Resolution of the minimal face | no receiver below the logarithmic radius in class `𝒵`; `n` modes of frequency `≥Γ` keep one sign on length `≤nπ/Γ`; a finite top layer of ζ is seen on windows whose length depends only on the number of its quartets | `sign_interval_resolution` `[L*]`; `FiniteTopLayersNeedNoSeparation` `[M]` |
| The exceptional coordinate | sector theorem; quasi-RH as a tail law; world I instrumented: filters at every speed, centred Vaughan currents at growing order, top-ordinate dichotomy | ZCG, ELT `[L]`/`[K]` |
| Landing as a method question | fails for the Euler product alone and for the functional equation with ζ's Gamma factor and count | APD `[L]`; IRW `[L*]` |
| The price of sizes | trivial aperture `log log(mass)` in the conductor and the height aspect; no gap; exchange rates on both sides | SA `[L*]`/`[M]` |
| A fixed zero-free half-plane | `[X]`: `Re s>7/8` for Hecke `L`-functions over `ℚ(√−3)`, Dirichlet `L`-functions and ζ. Natively: Möbius as the cube of a cubic Gauss coefficient, cubic reciprocity, the nonzero residue of the cubic Eisenstein family at `4/3`; exact abscissa receivers at the actual `Θ` (the cumulative square energy of the normalized Abel source has infimum exponent `2Θ`; a one-sided head bound at any positive power cutoff contracts the width); the exponent budget of the boundary `7/8` | `[X]`; MMD `[M]`; RHTower `QuasiRH*` `[M]` |
| Critical compactness | `R_c=R_polar=R_halfline≤W₀`; three-way classification; subcritical positivity below exponent `1/8` | AHD, CACT `[L]`/`[K]` |
| The window chain | RH ⇔ `Ψ` locally bounded on precontact intervals; sign at aperture `a` from verification to `windowHeight(a)`; RH through height 67 | CSTW, AIF, VHR `[L]` |
| Rigidity | Hamburger; FE-defect isolation for countable systems; isozeric gauge deformations; the fixed part of the canonical families; continuous prime measures are not rigid (`ζ·exp(ε/(s+1)²)`) `[S]` | HTGeometry, EFT, AWT `[L]` |
| Constituents | bounded Dirichlet-series factors are pure; no exponential polynomial is a factor (`infinite_zeros_not_xi_zeros`) `[L*]`; the jump law on every strip; Wiener's lemma on a strip; no bounded ordinary Dirichlet series is a constituent with a zero on a half-plane, and no Wiener constituent has a zero on a strip; limits of box constituents lose their zeros | IRP, CTZ `[L*]`/`[M]` |
| Exactness over ℤ | Frobenius at one prime; cost `m·θ(S)`; Stepanov at one prime (`p^{11/12}`); Riemann–Roch with Bézout on the tower is the product formula; the carry is a nonzero class complementary to the window count | SFPM, ALST, AGZ `[L]` |
| The square of Spec ℤ | `W(ℤ)` is a curve with the prime contacts; no finite-type carrier; one ring of sequences with exact counts; unit masses with paid contacts exist on the paying ring and the planar square, and Bézout by restriction is an equality there | AGZ `[L]`/`[M]` |
| The diagonal | the density of a comb, counterterm `log(density/2π)`; no glued invariant carrier; the constant `2π` forced | AGZ, HAT `[L*]`/`[L]` |
| The lattice | normal form at finite scale; short windows coercive and blind to the contacts; finite index; jets are even Newtonian multipoles; contacts are chain squares; the index counts the right zeros exactly; genus `1+(n/2)log(n/2π)` and Riemann–Hurwitz for number rings | HFP, AGZ `[L*]`/`[M]` |
| Regulators | clock, scattering tower, cusp cutoff; RH ⇔ the jump-tail floor at every fixed height | HAT `[L]`/`[M]` |
| The horizon | one cavity function is a complete sharp receiver; reflection Krein index counts off-line zeros | AHMH `[L]` |
| Prime distribution and census in law | Guth–Maynard `30/13`; Matomäki–Radziwiłł for μ at every length; simple critical zeros `≥0.67250071`; alternatives at `70, 75, 80%` | RHTower, IGP `[L*]`/`[L]` |
| Scope of failed mechanisms | 42 dead mechanisms and the scoped obstructions with survivors | killed-routes |

### 1.5 What stands between the corpus and a proof or a refutation

**(a) One producer, and it is external.** Natively every route is a receiver: every unconditional pointwise statement of the native graph lies below rung 1 or at `1+o(1)` and holds for a whole class of fakes (§1.3), and every mechanism that proves a statement of this type elsewhere has a Lean-fixed price over ℤ (obstacles summary §1.15). The one producer is `[X]`. Its boundary `7/8` is an exponent budget with an exact Lean analysis (§3.3): a vertex of three estimates, and inside the published probe the boundary lies in `[13/15, 7/8]` `[M]`. Between `13/15` and `½` there is no producer, and for the step from a half-plane to the line the corpus has one statement of the right shape, with no known use of its premise (§13.1).

**(b) The wall has one description `[D]`.** A rung above one needs a power saving of the contacts on the integers between `m` and `m^{2κ}`, with both structures used jointly (SA mechanisms 6–8). The Liouville twist is the fake on the Euler side. A statement that separates ζ from it at that range is a parity-sensitive statement at a power-saving scale. Type I and Type II norms, coefficient norms and finitely many linear laws are parity-blind `[L]`. The same wall is the square-root threshold in every regime: bandwidth `1` in the census, `θ=1` for mollifiers, rung `1` for apertures, the Vinogradov range for short sums. `[X]` crosses it at one place, with an identity and a family: Möbius over `ℤ[ω]` is a cube of cubic Gauss sums, and the estimate is a mean square over sextic twists of the size of its diagonal, obtained for Möbius coefficients through that identity (card `metaplectic-mobius-descent`).

**(c) The atoms.** ZAL is at least quasi-RH. B13, Landing and DH have no calibration with both structures (§1.2), and no inequality of the native corpus uses the functional equation and the Euler product jointly and is pointwise in the zeros `[A]`: the joint theorems are in law (Selberg, Levinson, the census), the pointwise ones are identities (Hamburger, the jump law). `[X]` is such an inequality for the half-plane: it uses the functional equation of a theta function and the Euler products of a family, and it excludes every zero right of `7/8`. It says nothing on an atom.

**(d) World I is invisible to mean values `[D]`.** Relocating finitely many zeros preserves vertical square means `[L]`; a long prime or Möbius sum at one point is controlled only through the zeros; the gap between the Vinogradov–Korobov range and the growth range of a top mode is `a(1−β)/2` `[L]`.

**(e) Structural gaps.** The dark range (Dirichlet polynomials longer than the height, and prime sums shorter than the Vinogradov range). Bézout from a property of the object: the square, the tower, the planar square and the lattice exist, and on each the section count returns an identity (the product formula; the product of the contact ideals) `[L]`/`[M]`.

**(f) A refutation.** Nothing in the corpus points to one. §11 states what a refutation would have to exhibit.

---

## 2. Opportunities

None closes a wall of §1.5. Ranked by what they would change.

| # | Opportunity | What it gives | State |
|---|---|---|---|
| 0 | **The external half-plane inside the native graph** | `Θ≤7/8` as a Lean theorem of the corpus; every `Θ<1` premise discharged: positivity of the dressed aggregate on large primes above level `11/8`, the rung `4/3`, the return-free windows of S3 (§12.1 row 9) | arithmetic conversion, reciprocity and the Eisenstein residue in Lean `[M]`; theta identification, cube removal and uniform transfer open (MMD) |
| 1 | **Bounded Dirichlet constituents** | a nonzero bounded holomorphic ordinary Dirichlet series whose zeros are zeros of `ξ` is zero-free on its half-plane | closed for every half-plane boundary by `bounded_dirichlet_constituent_ne_zero` `[M]`; positive survivor: a finite-prime projection preserving its zero set and bound |
| 2 | **The census past the diagonal** (§4) | `70%`; the first statement of the corpus that uses bandwidth above `1` | the integrable Fourier positivity class has ceiling at most `1−3/π²<7/10` `[M]`; the Conrey–Ghosh–Gonek ratio at `θ=½` is `19/27` and has a Krein form without RH `[D]` |
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

**One: the external theorem `[X]` and its formalization. There is no second path.**

### 3.1 The external theorem `[X]`

- **Statement.** No finite-order Hecke `L`-function over `F=ℚ(√−3)` and no Dirichlet `L`-function has a zero in `Re s>7/8`; in particular `Θ≤7/8`. Corollaries stated in the source: no exceptional real zero right of `7/8`; the least quadratic non-residue modulo `p` is `≤C(log p)^A`.
- **Principle.** `β*` is the supremum of the real parts of the zeros of the whole family of primitive finite-order Hecke characters over `F`. Fix a boundary `σ₀<β*` and an affine exponent `C(s)=s+c`. To every target `η` a sum `J_η(Z)` is attached with a direct bound `|J_η(Z)|≪Z^{C(σ₀)+ω}` and a comparison `|J_η(Z)−f_η(Z)|≪Z^{C(β*)−σ}`, where `f_η` is the Mellin integral of `Z^{C(s)}/L_F(s,η)` with finitely many Euler factors deleted. Margins `ω, σ` independent of `η` continue every reciprocal across a common distance left of `β*`: a contradiction. The boundary is the exponent of the direct bound minus `c` `[D]`: `1/4+2/3=11/12` in Part I, `3/16+11/16=7/8` in Part II.
- **The sum.** A completed cubic theta sum, averaged against sextic residue characters and the target. Its indices are `cn³` with `c` squarefree. It has two exact representations: the reflection of the cubic theta coefficients, and Poisson summation in the averaging variable, with frequencies `ua⁶`, `u` sixth-power-free. The row `u=1` contains `1/L_F(s,η)`. The other rows contain finite-order Hecke twists of the target; for this reason the whole family enters the proof for ζ.
- **The estimates.** Direct bound: a quadratic large sieve for the reflected rows and a planar additive large sieve. Comparison: a zero detector attaches to each row with a zero above a floor a large Dirichlet polynomial with ideal Möbius coefficients and a large plain one; a sextic large sieve counts such rows. Part II has prime compensation, unequal scales, a second moment of the inverse polynomial with prime factors (two finite Poisson transformations shorten the row range) and a fourth moment with short prime factors.
- **The source.** Parity enters through one identity: on squarefree primary products the cube of the normalized cubic Gauss sum is the ideal Möbius value times a phase.

### 3.2 State inside the corpus

| Item | State |
|---|---|
| `γ(I,ψ)³=μ(I)p/‖p‖`; `μ(I)·conj(G₁)=c(I,ψ)G₂` with `‖c‖=1`; cubic reciprocity in all cases; cubic Jacobi symbols; ramified supplements; the Kubota multiplier on `Γ(3)` | Lean `[M]` (`MetaplecticMobiusDescent`) |
| cubic Eisenstein series for `Re s>2`; quotient of finite volume; meromorphic resolvent at the eigenvalue `8/9`; nonzero residue at `4/3` | Lean `[M]` |
| the Fourier coefficients of the residue are the cubic Gauss sums; cube indices `ρ(pq³)=‖q‖ρ(p)` | open (card `cubic-theta-residue-and-gauss-coefficients`) |
| the mean square `Σ_{0<N(u)≤D^{1+θ}}\|Σ_n μ_K(n)(u/n)₆W(N(n)/D)\|²≪D^{2+θ+ε}`; uniform transfer bounds for the two Poisson transformations | open: "no local dependency-closed proof" (card `metaplectic-mobius-descent`) |
| the endpoints `Θ≤11/12`, `Θ≤7/8` | external Lean sources cached, not built here; the card records an external endpoint `riemannZeta_ne_zero_of_re_gt_elevenTwelfths` as not checked locally |

The path is clear in this sense: three named local steps and an audit of the transfer estimates. It is a formalization path. Its risk is the uniformity of the transfer.

### 3.3 Why `7/8`: the budget of the boundary in Lean `[M]`

| Fact | Declaration |
|---|---|
| at slot length `1/6` every redistribution of the two scales gives `7/8` | `fixed_slot_boundary` |
| longer slots, in the model that charges the face of zero retained length in full: budget `11/12−L/4+max(0,(6L−1)/5)/2≥7/8`, equality only at `L=1/6` | `retunedBoundary_sharp_minimum` |
| that face sits at rescaled slot length `d=1/6−h/5` and its term carries the factor `Z^{−d}` of the external (15.8): total exponent `−1/6+4h/5≤0`; the reflected allowance costs nothing when `1+3ℓ≤2M` (`M` the row length), on the edge `M+ℓ=1` up to `ℓ=1/5` | `tupleExponent_zero_retained_face`, `tupleExponent_reflectedAllowance_nonpos` |
| low boundary of a geometry: `5/6+M/12−ℓ/6+(M+ℓ−1)₊/2`; past `M+ℓ=1` the dual sum of the reflected rows is longer than the row sum | `lowGram_sub_principalShift`, `reflectedExponent_dual_length_face` |
| high side: the exponent of the top nonprincipal rows at the published geometry is at most `−49/440640` in every bin (external Lemma 20.2) and equals `−7/30672` in the bin `δ=79/204` with full prime amplitude | `endpoint_certificate`, `endpoint_binding_bin` |
| every geometry with low boundary at most `7/8−1/4000` has a positive high exponent in that bin: the published geometry is a vertex of the low bound, the row count of that bin and the dual length | `endpointExponent_pos_of_lowBoundary_le` |
| the floor of the probe: in the bin `δ=0` (rows with no zero right of the line) with the trivial count of rows, every geometry with low boundary below `13/15` has a positive high exponent, in both regimes of the Gram bound; with the count `U^{1−δ}` in every bin the balanced geometry `l_x=l_y=2/5`, `ℓ=1/5` reaches `13/15` | `endpointExponent_floor_bin_pos_of_lowBoundaryGen_lt`, `endpointExponent_balanced` |
| a saving `s` in the Gram power at the original scales gives `7/8−s/16` | `gram_power_saving_boundary` |
| improving only the exceptional (sixth-power) frequencies ends at `23/27` | `ordinaryGramBoundary_sharp_minimum` |
| a Gram profile `1+P^ν+P^κ/Y` reaches `5/6` iff `ν≤1/15` and `κ+4ν≤4/3` | `gramProfile_five_sixths_feasible_iff` |
| with the unit term retained the minimum is `29/36>3/4` | `unitGramBoundary_sharp_minimum` |
| the strips `5/6` and `3/4` are the energy exponents `5/3+ε` and `3/2+ε` of the cyclotomic remainder on any positive-power band | `five_sixths_strip_iff_chebyshevPowerBand`, `three_quarters_strip_iff_chebyshevPowerBand` |
| a one-sided head bound `H_θ(N)/N≤C+CN^c` at any fixed `θ>0` gives `Θ≤½+max(0,c)` | `zetaZeroAbscissa_le_of_mobiusDivisorQuotientPowerHead_le_rpow` |

These are constraints on the exponents of one method and exact receivers. None is an estimate. The Gram bound of the external source admits every coefficient array of norm one at the exceptional frequencies; the Möbius signs of the actual source are dropped at that step (card `quasi-rh-fixed-strip-improvement`).

### 3.4 Independently of `[X]`

The corpus has no route of its own to a zero-free half-plane.

What it establishes.
- Quasi-RH is a tail law: `Θ<1 ⇔ Θ∞<1` `[L*]`.
- Seven equivalent forms across routes (`quasiRH_crossRoute_seven_way_tfae`): escaped Möbius laws, centred prime bands, prime and Möbius power-window savings, receiver damping rate `<½` `[L*]`. A one-sided power saving at the primes of late logarithmic windows off power-thin exceptions `[L]`.
- On the ladder `[D]` from `[M]`: quasi-RH ⇐ one bounded dyadic second moment with a prefix-cancellation mollifier of length `T^{θ₁}`, `θ₁>1`; quasi-RH ⇒ the sign on bounded shapes at every rung below `1/(2·width)`; the sign at one rung `κ>1` at all large heights excludes isolated zeros of depth `>1/(2κ)`.
- In mean-square form `[D]`: with `X=T^θ`, `∫_1^T|M_X(½+it)|²dt` is `T/X` times the variance of μ in intervals of length `X/T`; slope `<1` in `θ` is a power saving of that variance for intervals of length `x^{1−1/θ}`. The corpus has Matomäki–Radziwiłł at every length with a saving that is not a power `[L]`.

Why none of this is a path.
1. The classical mechanisms for a zero-free region are positivity at the pole with growth bounds, and exponential sums. Both end at rung `1+o(1)` (SA atlas) `[M]`.
2. The first step past rung 1 by a constant `C` is the region `1−c/log log t` `[D]`; sizes do not give it.
3. On the mean-value ladder the rungs below `θ=1` do not add up to a rung above it: at `θ≤1` a mollified second moment bounds `Σ_ρT^{2θ(β−½)}` by `O(T)`, a density estimate `[C]`; at `θ>1` the diagonal does not dominate and the off-diagonal is a correlation sum of μ with power saving.
4. A producer uniform in the target of the prime torus also removes the exceptional zero of a real character `[D]`; the conductor ladder shows that sizes, multiplicativity and the functional equation alone stop at rung 1 `[L*]`. `[X]` is uniform in the conductor and removes exceptional zeros.
5. Return bounds are label statements shared by `ζ(s−h)` `[L]`; a strip of one function does not improve itself: `ξ(s+a)ξ(s−a)` has an Euler product and a functional equation `[L]`. `[X]` acts on a family closed under twists.

The form of a native source is the one fixed in §1.5(b): a power saving of ζ's contacts on the integers up to a fixed power of the mass, uniform in the height, that fails for the Liouville twist and for the lattice with a pair.

---

## 4. Seventy per cent of the zeros on the line

### 4.1 Status

- `simple_critical_proportion_ge_67250071` `[L*]`: simple critical zeros `≥(0.67250071−ε)N(T)`. The constant is `HD(1)+10⁻⁸`, `HD(1)=3/2−cot(1/√2)/√2`: the rank–trace certificate of the vendored `Zeta23` package (Alpöge–Furman, Theorem D; Montgomery–Taylor window at bandwidth 1) plus the disjoint-triple pinching of `IncommensurableGaborPinching` `[M]`.
- The mechanism `[M]`: the hat-unit Gram matrix of the zeros splits as `P+Q`, `P⪰0` from the critical zeros, `Q` from the off-line pairs `{ρ,1−ρ̄}`, each a block with eigenvalues `m(g+1)`, `−m(g−1)`. At bandwidth `λ<1` the prime side is diagonal and `H(λ)=2−1/λ−λ/3`.
- `critical_proportion_or_simple_offLine` `[L*]`: for every `θ`, `N₀≥θN` or the simple off-line zeros number at least `(1+HD(1)−2θ−ε)N`. A failure of `70%` needs `(0.2725−1/A−ε)N` simple off-line zeros within `A/log T` of the line `[M]`.
- Exchange rates `[M]`: a form factor `F≤4` on `(1,10/9)` certifies `7/10`; at bandwidth `4/3` the same proportion is the trans-threshold integral `∫₁^{4/3}(4/3−α)F≤7/45`.

### 4.2 Verdict: no clear path. Three doors and what each lacks

**(i) Bounded form factor above bandwidth 1 (B150).** `F≤B` on `(1,λ)` is an upper bound of the correct order for the variance of primes in intervals of length `X^{1−1/λ}` `[D]`. Selberg's bound under RH is one logarithm larger and Goldston's positivity bound controls only an average of `F` over unit intervals `[C]`. Asymptotics for almost all shifts with a saving `log^{−A}` per shift do not reach it: the main terms cancel and a relative precision `(log X)/H` is needed `[D]`. The statement is not known to follow from RH `[C]`.

**(ii) Positivity alone.** Closed for `70%` in the integrable Fourier positivity class `[M]`. For every continuous nonnegative integrable test `g` with `g(0)>0`, integrable real transform `h=𝓕g`, and `h≤0` outside `[-1,1]`, the certificate cost is at least `1+3/π²>13/10` (`positivity_test_cost_ge_totient_limit`). Exact totient grid laws have positive coefficients and origin masses tending to that bound. Gaussian regularization gives continuous admissible form factors with Frobenius value above `13/10` at every prescribed bandwidth (`positivity_does_not_reach_seventy_percent_at_any_bandwidth`). At `4/3`, the finite-spike construction additionally has `F≥1` outside the unit band and integral above `7/45`; the all-bandwidth result does not impose this extra lower bound.

**(iii) The mollified derivative at the zeros.** For the ratio `|Σ_ρζ′M(ρ)|²/(N·Σ_ρ|ζ′M(ρ)|²)` the optimum at mollifier length `T^θ` is `1−(1+θ)^{−3}`: `19/27>7/10` at `θ=½`, below the square-root threshold (`ZetaCGGMollifierOptimum`) `[M]`. Under RH this is a theorem for simple zeros `[C]`. Without RH `[D]`: with `a_ρ=ζ′M(ρ)` and `M` real,
`S₂^K:=Σ_ρ a_ρ·ζ′M(1−ρ)=Σ_{on}|a_ρ|²+Σ_{pairs}2Re(a_ρ ā_{ρ*})`,
a form that is positive on the critical zeros and hyperbolic on each off-line pair. With `S₁=Σ_ρa_ρ`, `p` the number of off-line pairs with nonzero weights and `a_±` the symmetric and antisymmetric parts on the pairs, `S₂^K=‖a₊‖²−‖a₋‖²` and `|S₁|²≤(N₀^{simple}+2p)(S₂^K+‖a₋‖²)`. For a close pair `ζ′(ρ*)≈−ζ′(ρ)`: the pair lies almost in the negative part, the opposite sign to the unweighted Gram matrix, where a close pair looks like a double zero. The corpus has the robust form on the subspace of mollifiers that vanish at all off-line pairs (`norm_firstMoment_sq_le_card_simple_crit`) `[L*]`, of codimension up to twice the number of pairs, which can exceed the dimension `T^θ` `[D]`. Missing: the two discrete moments as theorems for `θ<½`, and an upper bound for the displacement energy `‖a₋‖²=½Σ_{pairs}|a_ρ−a_{ρ*}|²` at census scale. Because `19/27` exceeds `7/10` by `0.0037`, the bound has to be `o(N log²T)` in effect `[D]`.

Also exact and unfed: the source covariance ceiling `6π/5`; the local count of off-line zeros `[L]`.

### 4.3 What a failure of `70%` looks like `[D]`

More than `13.6%` of the ordinates carry a horizontal doublet of width `≤2A/log T`. Each doublet is one hyperbolic plane in both Gram forms, with opposite signs of its near-null direction. A certificate that uses both forms on the same family of test vectors is the natural object; none is in the corpus.

---

## 5. The one big question

### 5.1 Questions not to pose

| Question | State |
|---|---|
| B154 the exceptional square; the gap `log 4` | no gap; the sign at `log log q+C` is the least non-residue at the scale `log²q` `[L*]`/`[D]` |
| B153 Dirichlet constituents | No in the bounded ordinary Dirichlet class on every half-plane; no in the Wiener class on a strip `[M]` |
| B143, B151, A92, A95 the resolution of the minimal face | logarithmic radius in class `𝒵`; `ΓL≤nπ`; finite top layers need no separation `[L*]`/`[M]` |
| (G) one glued object for the diagonal | refuted; the diagonal is the density of a comb `[L]` |
| (S3), B148 the transfer from homogeneous breadth | it implies `Θ<1⇒RH` `[S]`; under `Θ<1` it is equivalent to RH `[L*]` |
| B131, B132, B136, B138, B139, B140 | settled in the sense posed `[L]` |
| (FP), (S1), (S2), B85, B86, B125, B142 | settled: fixed part; price `m·θ(S)`; separation is a receiver `[L]` |
| Q20 unit masses with paid contacts | exists: paying ring, planar square; Bézout by restriction is an equality there and gives no sign `[M]`/`[S]` |
| A68 landing with ζ's Gamma factor and count | not forced `[L*]` |
| The first rung past a trivial aperture, in any aspect | by sizes a classical problem in each: region `1−c/log log t`, least non-residue at `log²q`, Brun–Titchmarsh constant below `2` `[D]`; with `[X]` the rung `4/3` holds in the height and conductor aspects |
| A zero-free half-plane for ζ | `[X]`; the open item is its native proof (§3.2), not the statement |
| B152, B149, B146, B117, B87, B18 | RH or producers of RH strength |

### 5.2 Verdict

**Among the questions that the corpus's own receivers pose, none below RH and quasi-RH passes the tests as a door. With `[X]` one question passes (§5.5).** The tests: not an equivalent of RH or of quasi-RH; answered by a proof or a refutation of a stated inequality, identity or implication; a consequence for either answer; not decided by a finite window; false on a corpus fake; a first step with an input that is not refuted; not a shape that is answered.

The reason is a set of theorems, not a lack of candidates.
1. Pointwise statements below rung 1 are sizes and hold for whole classes of fakes; at rung `1+o(1)` both one-structure fakes fail; by sizes the first rung above is a classical problem in every aspect (§1.3).
2. Mean values of length below the height are stable under relocation of finitely many zeros and give densities; above the height the conversion to a point is a theorem and its input is quasi-RH (§1.3, §3).
3. The structural questions about receivers are answered in Lean (§5.1); every answer is "a receiver" or "a price".
4. The atoms have no model with both structures (§1.2).

### 5.3 The question that would change the map: is the top of the zeros attained off the line?

> **(AAL)** If `Θ>½`, the supremum `Θ` of the real parts is not attained by a finite set of zeros: infinitely many zeros have real part above `Θ−ε` for every `ε>0`.

Equivalent form `[D]` from `[L]`: with `G(u)=e^{−(Θ−½)u}c_B(u)`, either RH holds (`G` is an almost periodic function with the frequencies of all zeros), or `G` tends to a nonzero finite trigonometric polynomial (world I), or `G→0` (world II). AAL says the middle case does not occur: if `Θ>½` the smoothed prime error is `o(x^Θ)`.

**Why this one.**
- It is implied by RH and implies no zero-free strip `[L]`; it is not a tail law and not a bounded-height law: adding or removing one isolated quartet changes it `[D]`.
- With AAL: RH ⇔ ZAL ⇔ finitely many off-line zeros ⇔ finite negative index ⇔ bounded heat counts ⇔ eventual Hadamard positivity `[L]`. The finite-stratum receivers of SC, LA, JAS, WL, PTR and the Krein–Langer index become receivers of RH, and a failure of RH is confined to a tail.
- World I is the most rigid world in the corpus: a finite layer at bounded height read by prime filters at every damping speed, a Mertens power saving, heavy returns later than `exp(c·y^{1−β′})`, a uniform negative excursion of the top trace on every window whose length depends only on the number of top quartets `[L]`/`[M]`.

**What a proof may not be `[D]`.** A mean value (relocation invariance). An identity of the explicit formula (every filtered current is the filtered zero sum). A bound for a long prime sum (controlled only through the zeros). A statement on sizes. A statement that holds for integer-norm Euler products or for entire functions with ζ's functional equation, Gamma factor and count. It has to be an inequality that uses both structures and is pointwise in the zeros. The native corpus has none; `[X]` is one for the half-plane `Re s>7/8`, and its mechanism acts on the supremum over a family, which a finite top layer of ζ alone does not move `[A]`.

**Tests.** Not an equivalent of RH or quasi-RH: passes. Proof or refutation: one-sided, a refutation is a refutation of RH. Consequence: above. Finite window: passes. Fakes: false on integer-norm one-offs and on functional-equation models `[L]`. First step: **fails** — the instrumented reduction ends at the signed centred type-II current at a growing isolated mode, which is the exclusion itself (B145). Answered shape: no.

It is the target, not a door. Its three sectors are B13 (bounded index), Landing and DH; none has a first step.

### 5.4 Decidable questions with a first step

Each is two-sided and none produces a sign.

| # | Question | First step | Either answer gives |
|---|---|---|---|
| 1 | **Constituents in the bounded class.** Can a nonzero bounded ordinary Dirichlet series have a zero and all its zeros among those of `ξ` on its half-plane? | `bounded_dirichlet_constituent_ne_zero`; finite-prime zero-set projection | No for every half-plane boundary `[M]` |
| 2 | **The positivity ceiling of the census certificate** (§4.2 (ii)) | `positivity_test_cost_ge_totient_limit`; exact totient grid laws and Gaussian regularization | closed: every admissible integrable Fourier positivity test costs at least `1+3/π²>13/10` `[M]` |
| 3 | **Polar orthogonality at the critical curve** (B104) | the isolated-pair lattice of SA, where the critical direction is `sinh(δu)e^{iγu}` and its polar pairing is explicit `[D]` | empty third case: five routes share one rank-one payment. A model with an orthogonal state: the complete matrix carries no information beyond the windows |
| 4 | **Rough packets** (SA topic 4) | bounds for `Σw(n)n^{−iτ}` uniform in `τ` from cancellation of partial sums | the prime-side exchange rate holds on all packets, or the rung law is a statement about bounded shapes only |
| 5 | **Clusters on a rung** | `zeta_companion_of_rung` with the half-period law | whether the sign on a rung is equivalent to a strip for configurations with ζ's local counts and deep zeros of density zero |

### 5.5 With `[X]`: is the boundary `7/8` arithmetic or bookkeeping?

> **(B★)** In the Gram form of the detector of `[X]`, bound the contribution of the exceptional frequencies (ideal valuations divisible by six) with the Möbius weights of the actual source, before the norm bound: does `sourceCanonicalSum` on `exceptionalFrequencies` with `sourceMobiusWeight` save a power over the count of those frequencies?

**Answer `[D]`: No** (card `family-continuation-walk`, conjectures C1–C5; read off the cached text of `[X]`, §6.1 and §15.2, and not checked against its Lean sources). The weights `μ(d)` of the Gram form invert the coprimality of two columns; they are a sieve of density `1/ζ_K(2)` and carry no cancellation. The additive Gram form of the columns is, by Poisson summation in the row, a multiplicative form in the frequency `k`: for two columns of coprime moduli the correlation is one term, `χ_{s₁}(k)\bar χ_{s₂}(k)` times a reciprocity factor (`sum_column_mul_conj_column_of_coprime`, `sum_weight_mul_column_mul_conj_column` `[L*]`, in the model of residues modulo integers). At the frequencies on which the symbols are `1` the terms add without cancellation (`sum_exceptional_correlation` `[L*]`): the exceptional part is the number of sixth-power frequencies times the square of the plain column sum. It is the dual of an incomplete character sum, present because the row ball `Q` is shorter than the conductor `Y²` of a pair of columns, and absent in the balanced geometry of Part I. The same plain column sum multiplies the principal signal, so centering the columns removes both.

Consequence `[D]`. In the exponent budget the unit term alone gives the boundary `x/6+5/6−L/6` (`29/36` as `x→0`, `23/27` under `P²≤Y`); the exceptional term adds `(y−x)/12` and makes the boundary `7/8` for every `x`. The exponent `1/6` is exact, the region of `gramProfile_five_sixths_feasible_iff` needs `ν≤1/15`, and so the profile `1+P^ν+P^κ/Y` does not reach `5/6`. The slot length is not capped at `1/6` by the reflected energy: the face that the budget of `retunedBoundary_sharp_minimum` charges is paid by the tuple factor (§3.3). The published geometry is a vertex of three published estimates `[M]`: the low bound `5/6+M/12−ℓ/6`, the row count of the bin `δ=79/204` (zeros of the row characters near real part `0.69`) at full prime amplitude, and the condition `M+ℓ≤1` that the dual sum of the reflected rows is not longer than the row sum. With these three estimates the boundary of the probe lies in `(7/8−1/4000, 7/8]` (`endpointExponent_pos_of_lowBoundary_le`); the row count depends on the top of the zeros through the plain capacity `(1−2m)/(6κ)`, `κ=2β−1`, and with the count at any `κ∈[11/15,3/4]` the boundary lies in `(7/8−1/2500, 7/8]` (`endpointExponent_pos_of_lowBoundary_le_at`). A lower boundary inside this probe needs one of: a better count of the rows of that bin (a density estimate for sextic twists at `σ≈0.69`), a reflected mean square past the dual length, or a Gram bound below the exceptional term; the last is excluded by the answer above. The room is small `[M]`: bounds of Riemann-hypothesis quality for every nonprincipal row, summed trivially over the rows, give no geometry below `13/15`, and the count `U^{1−δ}` in every bin gives exactly `13/15` at the balanced geometry, where the exceptional term is absent. Inside the probe the boundary lies in `[13/15, 7/8]`; `5/6` needs cancellation across the nonprincipal rows or another probe.

---

## 6. The one big question without positivity and without spectral theory

"Spectral" is read as spectral theory of operators in every form; "positivity" includes nonnegativity of forms, kernels, counts, coefficients and averaging measures. Kept: Fourier analysis, mean values used as bounds, exponential sums, absolute convergence, continuation, power sums, integrality, recurrence, the argument principle.

**What survives.**
- *Receivers.* RH ⇔ `|c_p|≤K` on windows, by complex deletion filters; RH ⇔ the ordinate is injective on the zeros `[L]`.
- *Conversions from a law to a point* `[D]`, each a theorem in one setting:
  1. recurrence against density — a zero of an almost periodic object recurs with positive density, and deep zeros of ζ have density zero: constituents are pure, and in the Wiener class have no zero `[L*]`/`[M]`;
  2. budget overflow — one off-line zero costs more than a mean-value budget: long mollifiers `[M]`;
  3. winding and sign changes — the index law and its semicontinuity `[L]`; for finite layers, half-period deletion, a count of the sign changes of a finite trigonometric sum `[L*]`;
  4. the rightmost zero of a family against a mean square over its twists — a zero of one member gives large Dirichlet polynomials in many rows of a completed sum, and a large sieve bounds the number of such rows `[X]`.
- *The additive identity.* The jump of the fractional part: the jump law on every strip `[M]`.
- *Priced producers.* Frobenius at one prime, integrality, exponential sums, linear forms in logarithms `[L]`.
- *A census by winding.* Levinson's method uses the argument principle and a mean value as a bound. Its gate is a hypothesis in the corpus and the twisted second moment below the square root is a theorem `[M]`/`[K]`. The `0.6725` theorem uses a positive semidefinite Gram matrix and is outside the constraint.

**Verdict.** Under the constraint no question of the native corpus below quasi-RH passes the tests. Among conversions 1–3, the second is the only one that reaches every zero of `ξ`, and its input is a rung `θ>1`; the first and the third reach constituents, finite layers and limits. Conversion 4 reaches every zero right of `7/8` `[X]`. The target is the same as in §5.3, and the absence of a first step is the same.

**`[X]` under the constraint `[A]`.** The external argument uses no sign of a form attached to ζ and no operator whose spectrum is the zeros. Its tools are an identity for Gauss sums, the reflection of the cubic theta coefficients, Poisson summation, large sieves used as bounds, and a zero detector. The cubic theta function is a residue of an Eisenstein family; its construction is spectral, its use is through a functional equation. A strict reading of the constraint removes `[X]`; the reading "no positivity of a form attached to ζ, no spectral realization of the zeros" keeps it, and then the half-plane and question (B★) of §5.5 stand under the constraint.

**The bounded constituent question.**

> **(C1), closed `[M]`.** Nonzero bounded ordinary Dirichlet constituents are zero-free on every half-plane (`bounded_dirichlet_constituent_ne_zero`).

A finite-prime projection preserves the complete zero set and bound of a pure bounded ordinary Dirichlet series. The finite-prime representative is zero-free, hence so is the original. The argument needs no factorization preserving zero multiplicities.

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
| Möbius as a coefficient with a functional equation | `MetaplecticMobiusDescent` (the arithmetic of `[X]`) |

The walls are not walls of language. Each programme ends at the same statement, and §1.3 says which: a rung above the proved ones. No native programme contains a source; the one source is `[X]`.

### 7.2 The field: parity-sensitive arithmetic at power-saving scale

| Aspect | Content |
|---|---|
| What it is about | Pointwise cancellation of multiplicative data on the integers up to a fixed power of the mass, in the range where sieve weights, bilinear norms and exponential sums are blind: between `m` and `m^{2κ}` for a conductor `e^m` or a height `e^m`. The object that marks the blind range is the Liouville twin: every statement of the field holds for the true object and fails for it |
| Why the walls are this | The rung law has two sides with one rate: a saving `n^{½+γ}` in the contacts buys the rung `1/(2γ)`, a zero of depth `δ` shows at `1/(2δ)` `[M]`. The fake on the Euler side is the Liouville twist `[L*]`; parity blindness of Type I and Type II information is a theorem `[L]`; the square-root threshold of the census, of mollifiers and of the dark range is the same blindness in the mean `[D]` |
| Point of view | Parity is not a defect of sieves but an invariant: the class of statements closed under the twin involution `w↦λw`. A source is a statement outside that class. The field classifies the statements outside it by what breaks the involution |
| What breaks the involution in the corpus | (1) the pole: the sign of the polar boundary term separates the antipode `[S]`. (2) additive identities of the floor: `Λ∗1=log` selects Λ; `Σ_kF(⌊x/k⌋)=⌊√x⌋` forces λ; unit comb masses force Λ `[L]`. (3) the conductor: the Liouville twist has none `[L*]`. (4) mean values at every length: Matomäki–Radziwiłł `[L]`. (5) reciprocity: over `ℤ[ω]` the cube of the cubic Gauss sum is Möbius, so a Möbius-weighted sum is a sum of cubic theta coefficients, which have a functional equation `[M]`. (1)–(4) are not pointwise at power-saving scale; (5) is the source of `[X]` |
| Objects | twins and the twin involution; the dominated box; parity-sensitive functionals; one-structure fakes (Liouville twist, lattice with a pair); short sums `Σ_{n≤m^{2κ}}w(n)n^{−½−iτ}`; cut identities; the jump of the fractional part; exceptional characters as the one world where the involution is nearly a symmetry |
| Language | twin, parity class, parity-sensitive, source, rung, exchange rate, companion, cluster, saving at a range |
| Foundational principles | (i) A source uses both structures jointly: each one-structure fake fails at rung 1 `[L*]`/`[M]`. (ii) A source is pointwise; statements in law are exchanged at the height (§1.3). (iii) No margin: a source proves an inequality whose equality case is approached. (iv) Every mechanism is priced before it is used. (v) A source uniform in the target of the prime torus contains the exclusion of exceptional zeros; a source for ζ alone has to use the identity of the torus or the pole `[D]` |
| Criteria | P1–P8 of `SelectiveArithmetic`. In addition: it fails for the Liouville twist and for the lattice with a pair at the same rung; over `𝔽_q[T]` it reproduces square-root cancellation at short range and names what replaces the Frobenius; run in the mean it reproduces Matomäki–Radziwiłł; it does not follow from the explicit formula |
| Questions it must answer | Which additive identity of the integers is parity-sensitive at the range `(m,m^{2κ})` and not only at the range of its own length? Is there a pointwise consequence of parity breaking in the mean, under isolation of deep zeros? What is the exact parity class of the comb form at finite scale: which windows separate Λ from `λΛ`, at which margin? Does an exceptional character, if it exists, supply a source for ζ (the conductor ladder read backwards)? |
| Research topics | the twin involution on the comb lattice and on the cut system; parity-sensitive identities at short range; the rung law with clusters; the function-field calibration at short range; exceptional characters as sources; the pole as a parity breaker past rung `1+o(1)` |
| Tools it would develop | parity-sensitive bilinear decompositions; short-range forms of the cut identities; a transfer from the mean to isolated points; the ladder as a measuring instrument for every candidate |
| Built on | SA (prices, ladders, fakes), RAC and CTZ (additive identities), APR and AGT (blindness theorems, twins), MZF (the mean), ELT (isolated layers), `MetaplecticMobiusDescent` (the identity of `[X]`) |
| To discover | natively, one statement outside the parity class that is pointwise at a power of the mass. `[X]` is one, at the rung `4/3`. Past it: the identities of the kind of (5) that split into two Gauss sums are three, and (5) has the least boundary among them `[D]` (§13.5); a saving at the exceptional frequencies does not exist (§5.5). Inside (5) the open inputs are a density estimate for the sextic twists (the room `[13/15,7/8]`) and, below `13/15`, cancellation across the twists |

**Main conjecture.** For every `κ` there is a parity-sensitive inequality for ζ on the integers up to `m^{2κ}`, uniform in the height. **Milestones.** M1 the parity class of every unconditional theorem of the corpus (an atlas column). M2 `[X]` in the native graph: the rung `4/3`. M3 the classification of the identities of type (5): which covers and which fields turn Möbius into coefficients with a functional equation. M4 a rung above `4/3`. M5 every rung.

**Status of the proposal `[A]`.** The field has one theorem, `[X]`, and one folder that formalizes its arithmetic; it has no theory: no classification of the identities, and no account of the boundary beyond one exponent budget. The area is the classical parity problem. What the corpus adds is its exact form: one rate, two fakes, no margin, the price of every known mechanism. Mathematics outside the corpus that acts on this wall, with verdicts: large values by additive energy (Guth–Maynard) — in law, imported as a corollary `[L]`; entropy decrement and nilsequence methods — savings that are not powers `[C]`; interpolation formulas for the pair of the logarithms of the integers and the zeros — identities, no location statement `[C]`; Euler systems — bounds at integer points, no statement in the strip `[C]`.

---

## 8. A new field without positivity and without spectral theory

**Conversion theory: from a law to a point, for a rigid object.**

| Aspect | Content |
|---|---|
| What it is about | The corpus proves much in law (densities, the census, mean values, typical heights, almost every fibre of the prime torus) and RH is a statement about every zero of one object without moduli. The field studies the mechanisms that turn a law into a statement at a point without a sign, their domains and their prices |
| The conversions | recurrence against density; budget overflow; winding; the rightmost zero of a family against a mean square over its twists `[X]` (§6). Each has one theorem and no theory |
| Point of view | A conversion is a pair: an amplification of one exception (it recurs, it overflows, it winds) and a law that the amplified exception violates. The exception is a zero of depth `δ`; the law is a density or a mean value. The field computes, for each conversion, the amplification as a function of depth and scale, and compares it with the exponent of the law |
| Objects | exceptional sets of heights and their local structure (clusters, companions, energy); transport and return counts of a zero; spikes of long polynomials at a zero; budgets; indices of approximants; the hull of ζ and the identity fibre |
| Language | law, point, exception, amplification, budget, overflow, transport exponent, density exponent, index, isolation |
| Foundational principles | (i) A law never excludes; an amplified exception does. (ii) An amplification is measured against the sharpest law: `T^c` returns against `(30/13)(1−σ)` `[L]`; a spike `Y^{2δ}` against `T` `[M]`; one unit of index against one zero `[L]`. (iii) The identity fibre is special and typical at once: it continues analytically, almost every fibre has a natural boundary, and RH says it is typical for zero-freeness `[L]`/`[D]`. (iv) No sign and no operator |
| Criteria | Reprove the three theorems as one scheme. Over `𝔽_q` reduce to periodicity of the zeros in height. Fail on integer-norm one-offs (finite exceptions do not recur), on the non-tempered pair (exceptions of positive density), and on `ζ(s−h)`. Not uniform in real characters unless it excludes exceptional zeros. State the exchange with length: which conversions stay below the height |
| Questions it must answer | Is there an amplification of one zero that is unconditional below the height? What is the transport exponent of a zero of ζ: how many returns does one zero right of `σ` force? Does recurrence against density extend from uniformly almost periodic objects to objects almost periodic in the mean, when the functional equation supplies the other side of the line? Every splitting has its defect certified by sizes on one circle (`encard_zeros_le_of_norm_le_on_sphere`) `[M]`: which splittings of `ξ` have an arithmetic bound for the defect? |
| Research topics | explicit heights for constituents of bounded length; the graded form of Bagchi's criterion with the Guth–Maynard exponent; local structure of the deep zeros; the Levinson census as a winding statement with the twisted moment in Lean; the separation proof of the Carlitz–Goss zeta function as a calibration in characteristic `p` |
| Built on | CTZ, IRP (conversions 1 and 3), CDG and MZF (conversion 2), ZCG Recurrence, SOSZ ScaleLocality, SFPM |
| To discover | an amplification that needs no length past the height; or a proof that none exists in a stated class |

**Main conjecture.** Every sign-free conversion of a law about the zeros of ζ into a statement at every zero either has an input of the strength of the rung that it produces, or acts on a family through an identity of the type of §7.2 (5). **Milestones.** M1 the three conversions in one scheme with their exponents. M2 bounded Dirichlet constituents, closed `[M]`. M3 finite-relocation invariance for growing quadratic tests, formalized `[M]`. M4 a conversion outside that class.

**Status `[A]`.** No folder owns the conversions as a subject; the theorems are in five programmes. The main conjecture is a statement about methods and can be approached by classification, as for the conductor ladder.

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
| Carries | a cocycle that is not a coboundary; its defect is minus the defect of the window count; the jump law on a strip is the law of the carry (`carrySeries_eq_of_strip`) | `[L]`/`[M]` |
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
| C8 | positivity is derived, and not from a section count | product formula on the tower; equality of ideals on the planar square `[L]`/`[M]` |
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
| 4 | What replaces extension of constants, the tensor-power trick and the family? | among covers and twists used as averages, nothing: fixed part; a cover bounds its base `[L*]`. `[X]` uses a family in another way: it is closed under the sextic twists that Poisson summation produces, and the argument acts on its rightmost zero |
| 5 | The full window at finite scale, and the converse | block averages decide `[L]`; nonzero block sums open (B152); converse open (A80) |
| 6 | Integer-norm systems on their own comb: does Bézout there hold exactly when the zeros are on a line? | No. On the comb of squares the system of the squares, with zeta function `ζ(2s)`, fails Bézout without hypothesis (`not_weilPositiveFull_squareSystemWeight`, `exists_packet_squarePairing_gt`): the jets of a comb are those of the archimedean factor of ζ in the coordinate of the norms and do not follow the system `[M]`. A separated comb stable under the Frobenius monoid is one orbit, so the comb of ℤ has no moduli `[L]` |
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
| V. The own comb | the pairing of an integer-norm system on its own comb | the jets of a non-lattice comb are not an archimedean factor; the pairing is not a zero sum | met for the system of the squares (`OnItsOwnCombTheSystemOfTheSquaresFailsBezout`) `[M]` |
| VI. A count | natural numbers `K_p(m)` on the rays `Γ_1+Γ_p` with quadratic Tate limit | no definition without the form | open |

### 9.7 Tools, objects, language, mechanisms

- **Built on.** Witt vectors and Λ-structures; necklace coordinates; comb finite parts and the normal form; Hardy squares and chain squares; the index law; combs of norms; the conductor ladder.
- **Language.** square, graph, contact, jet, comb, density, counterterm, genus at a degree point, ramification, twisted part, rung, paying ring, planar sequence.
- **To discover.** One property of the square that is an inequality: a positive class whose positivity is not the statement to be proved. Every structure in the corpus is an identity (product formula, complementary carry, payment of contacts) or a receiver.

### 9.8 Order of work

1. Close IV as a theorem (kill); III and V are closed.
2. II for non-invariant gluings along the comb of the integers.
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
| A calibration where separation proves purity | the Carlitz–Goss zeta function: digit calculus, carry recursions and the unique optimality of the greedy carry-free composition in Lean | `[M]` |

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
8. **Irreducibility.** Wiener and bounded ordinary Dirichlet constituents are excluded `[M]`; limits of approximants remain receivers (index-one limits give RH `[L]`).

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
| Shape | a finite top layer at `β=Θ<1`, at bounded height (`β≤7/8` with `[X]`) | infinitely many zeros with real part tending to `Θ=Θ∞>½` (`Θ∞≤7/8` with `[X]`) |
| Forced `[L]` | a zero-free strip above some height; `M(x)=O(x^{β′})`, `β′<1`; the normalized prime error tends to a nonzero finite trigonometric polynomial `[D]`; a uniform negative excursion on every window of a length set by the number of top quartets `[M]`; filters read every top residue | deep zeros of density zero; nothing else |
| A counterexample | canonical: the layer is definable from the primes | no zero is distinguished |

Every failure satisfies, without hypothesis: ordinates above 67 `[L]`; depth below `½` by the Vinogradov–Korobov margin `[L]`, and at most `3/8` with `[X]`; at most `T^{(30/13)(1−σ)+ε}` zeros right of `σ` `[L]`; at least `67.25%` of the zeros simple and on the line `[L*]`; each off-line zero gives an explicit positive lower bound for the de Bruijn–Newman constant, quadratic in the depth `[L]`; every late logarithmic window has a prime that violates the floor outside every power-thin set `[L]`; at every large scale some window has a real divisor of bounded norm with comb form `≤−ε` `[L]`; beyond some aperture no weight system is feasible (`exists_aperture_forall_not_combBezoutAt`) `[L*]`; the intersection form on packets has `1+κ` positive squares, `κ` the number of right zeros `[L*]`, an even number because ζ has no real zero in the strip `[D]`.

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
| 3 | **The positivity ceiling.** Every integrable Fourier positivity test has cost at least `1+3/π²`; continuous countermodels preserve both positivities and the exact unit band at every prescribed bandwidth | `positivity_test_cost_ge_totient_limit`, `positivity_does_not_reach_seventy_percent_at_any_bandwidth` | positivity closed for `70%` `[M]` |
| 4 | **The Krein form of the mollified derivative.** `S₂^K=‖a₊‖²−‖a₋‖²`; `\|S₁\|²≤(N₀^{simple}+2p)(S₂^K+‖a₋‖²)`; a close pair lies in the negative part | `ZetaCGGMollifierOptimum`, `OffLineAnnihilatingWeightsCountCriticalZeros`, the rank–trace slack of `Zeta23TheoremASpectralSlack` | a second Gram form in which an off-line doublet has the opposite sign; names the displacement energy as the one missing bound for `19/27` |
| 5 | **The trichotomy of the normalized prime error.** RH, a nonzero finite trigonometric limit, or limit zero | `exists_expansion_of_top`, `FiniteModeWindowLength`, the sector theorem | AAL as a statement on one function; the world of a failure is read from the primes |
| 6 | **B13 in index form.** B13 ⇔ the negative index of the defect of the comb pairing on packets is `0` or infinite | `exists_le_negIndex_ringDefect_iff` for ζ alone | one lattice statement for the bounded-index sector; in world I-a the intersection form has `1+2k` positive squares, `k` the number of quartets |
| 7 | **The exchange between verification and aperture.** The explicit `windowHeight(a)` is an iterated exponential; the visibility laws make heights up to about `e^{2a}` necessary; the height aspect suggests `exp(e^{a+η})` as sufficient, and `exp(e^{(1−2ε)a})` under a strip of width `ε` `[D]` (`ε=1/8` with `[X]`). Determine the order | `windowHeight`, `exists_height_margin`, the visibility laws | the window routes at bounded mass as verification with an exact exchange rate; a stage step is a zero-free strip |
| 8 | **The depth sum with a constant.** `Σ_{β>½}(β−½)≤cT` with `c` from the mollified moment at `θ<½` and Littlewood's lemma | MZF moments, `exists_logIntegral_le_of_secondMoment` | the inner field bound of AIF with an explicit constant |
| 9 | **The map under a strip.** With the half-plane bound as the explicit premise that the Lean statements carry: large-prime positivity of the dressed aggregate at every level above `11/8`; the rung `4/3` on bounded shapes (`exists_cancellation_margin` with `γ=3/8`); return-free windows of the prime orbit at prime cutoff `T^{16}` (S3) `[D]`. The equivalences RH ⇔ `JasDressedPSD 1` ⇔ positive Bernoulli product tests on large primes at level one carry no premise `[L*]` | `jasDressedPSDAbove_of_xiZeroHalfPlaneBound`, `exists_jasDressedPSDAbove_of_signal_le`, `riemannHypothesis_iff_jasDressedPSD_one`, `riemannHypothesis_iff_exists_jasProductPositiveAbove_one`, SA, `WeightedReturnCounts` | the corpus's statements at `Θ≤7/8`; unconditional when `[X]` is in the native graph |

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
| Exact arithmetic pieces that share zeros with `ξ` (W1C by factors, PTR and PM pieces) | no constituent in the Wiener or bounded Dirichlet class (`bounded_dirichlet_constituent_ne_zero`); limits of box constituents lose their zeros `[M]` | closed |
| The first rung of any ladder by sizes | a classical problem in each aspect (§5.1); `[X]` reaches the rung `4/3` by another source | no work by sizes; the open rung is the one above `4/3` |
| Sections, Riemann–Roch and Stepanov on any ring of sections of the square | product formula on the tower; equality of ideals on the planar square `[L]`/`[M]` | closed |
| Covers and families as averages over their members | fixed part; the index of the square of an abelian ring is the number of distinct right-hand zeros in the union of the zero sets of `ζ` and its characters, additive over characters only when they share no such zero (`exists_le_negIndex_ringDefect_iff`); a cover bounds its base `[L*]` | support only. A family used through its rightmost zero is the producer of `[X]`; this closure does not cover it |
| The transfer of S3 | at least the strength of `Θ<1⇒RH` `[S]`; equivalent to RH under `Θ<1` `[L*]` | closed |
| Stage steps of the window tower; theta ranks one at a time | verification (row 7); the frozen floor tower `[L]` | one rung per verified height; no induction without a strip |
| Scheduled sums (FU, CFC, RP); source completions (SEC, CDC, APF, EWJ, RFHM, WBF) | exact criteria, no estimate on advancing histories; one condition per zero | frozen |
| Positivity alone for the census | every admissible integrable Fourier positivity test has cost at least `1+3/π²>13/10` (`positivity_test_cost_ge_totient_limit`) `[M]`; continuous countermodels also exist at every bandwidth | closed for `70%`; additional constraints remain outside this class |
| Mean values of length below the height as detectors of single zeros | relocation invariance `[L]`; the conversion needs `θ>1` `[M]` | density and census only |

---

## 13. The most likely route, written as a walk

### 13.1 The guess `[A]`

A proof of RH most likely has two legs.

- **Leg A, a half-plane.** The reciprocals of a whole family of `L`-functions are continued across the rightmost zeros of the family. The source is an identity that turns Möbius coefficients into coefficients with a functional equation; the estimates are mean squares over the twists that the identity produces. `[X]` is this leg at `7/8`.
- **Leg B, from a half-plane to the line.** A statement that fails in every strip of positive width and that uses a half-plane as a hypothesis. The corpus has one statement of this kind, the return transfer B3 of §13.2. Under a strip it is equivalent to RH `[L*]`, as every such statement that follows from RH is; a proof of it would have to use its premise, the absence of heavy returns, and no use of that premise is known. B1 and B2 are readings of the abscissa (level `σ` of the dressed aggregate on large primes is `Re ρ≤σ−½`; a head bound with exponent `c` is `Θ≤½+c`), and B4 is a case split. A half-plane from leg A is a point of these scales, not a step towards the line.

Why this route and not another.

| Route | A source that exists | Slack | State |
|---|---|---|---|
| Family continuation with a reciprocity identity (leg A) | yes `[X]` | positive exponent margins, uniform in conductor and height | `7/8` `[X]`; the exponent budget of the boundary is in Lean `[M]` |
| The sign of Weil's form at every aperture (RW, HF, ACS, §9) | none | none: forced weights, forced constant, margins that decay doubly exponentially `[L*]`/`[L]` | every receiver is exact; every structure found returns an identity |
| The ladder by sizes and exponential sums (SA) | sizes | none past rung `1+o(1)` | closed at rung 1 by two fakes `[L*]`/`[M]` |
| Long mollifiers and Möbius moments (WD, MZF) | diagonal mean values | any fixed power of the height (`riemannHypothesis_iff_cofinal_pure_moebius_moment`) `[L*]` | `θ<½` `[K]`; past the height the mean runs over fewer frequencies than the polynomial has terms, and the statement is the Mertens form of RH `[D]` |
| Recurrence and transfer (BAG, S3) | return-free windows under a strip `[L]` | a power | under a strip the premise of the transfer holds in every late window and the transfer is equivalent to RH `[L*]` |
| Limits of pure objects (LA, W1C, heat) | none | none | receivers |

The choice rests on `[X]`, which this report did not check. If stage W0 fails, no route has a source and §1.5(a) holds in its native form.

A point about the geometric programmes (§9) `[D]`. The receivers with slack ask for a power, not for a sign: a floor `−Kp^α` on prime windows gives width `α` `[L]`; a bound `C_θT^{K}` with `K` independent of `θ` for the Möbius polynomial of length `T^θ` gives RH `[L*]`. A construction that yields an inequality with any power margin feeds these. The constructions of §9 aim at Weil's sign, which has no margin, and each returns an identity. `[X]` uses an identity (reciprocity for cubic Gauss sums) together with crude mean-square bounds, and this combination is what the function-field proofs of parity-sensitive statements use: Pellet's identity (`discriminant_character_eq_moebius`) with Weil's bound `[M]`/`[C]`.

### 13.2 The skeleton

**Leg A `[X]`.** For a boundary `σ₀` and an affine exponent `C(s)=s+c`: a completed sum `J_η(Z)` for every member `η` of a family closed under the twists that the argument produces; a direct bound `|J_η|≪Z^{C(σ₀)+ω}`; a comparison `|J_η−f_η|≪Z^{C(β*)−σ}` with the Mellin integral of `Z^{C(s)}/L(s,η)`; margins uniform in `η`. Then `β*≤σ₀`. The boundary is the exponent of the direct bound minus `c` `[D]`. RH by leg A alone is the statement that for every `σ₀>½` such a sum exists.

A strip of one function does not improve itself: `ξ(s+a)ξ(s−a)` has an Euler product and a functional equation, and its zeros stay on two lines `[L]`. Leg A acts on a family.

**Leg B, receivers.**

| | Receiver | Open input |
|---|---|---|
| B1 | RH ⇔ `JasDressedPSD 1` `[L*]`, with no half-plane premise (`riemannHypothesis_iff_jasDressedPSD_one`). The dressed lag aggregate has entries `(uv)^{−σ}Φ(log v−log u)`, `Φ` the Weil lag function; positivity is monotone in `σ`, holds at `σ=2`, and on large primes at `σ≥3/2`; positivity on large primes at a level `σ≥1` is the half-plane `Re ρ≤σ−½`, in both directions up to `ε` `[L]`; Bernoulli product tests on large primes suffice `[M]`. The levels and the half-planes are one scale: a signal bound with exponent `b` is level `b+½` (`exists_jasDressedPSDAbove_of_signal_le` `[L*]`), and leg A does not shorten the way to level one | positivity at one level `σ≤1`, which is RH |
| B2 | the cumulative square energy of the normalized Abel source has infimum exponent `2Θ`; on the power mesh `1+2m(Θ−½)`; a one-sided head bound at any positive power cutoff contracts the width `[M]` | one estimate with an exponent below the one that `Θ` gives |
| B3 | a strip of half-width `h<½` excludes heavy identity returns of the primes below `T^{2/(½−h)}` up to `exp(ηT)` `[L]`; a uniform transfer to bounded prime traces on `log²` windows gives RH `[S]`. RH gives the transfer, since the prime traces are bounded at every prime, and under a strip its premise holds in every late window: under a strip the transfer is equivalent to RH (`homogeneousReturnWindowTransfer_iff_riemannHypothesis` `[L*]`), neither weaker nor stronger than what it has to deliver | a use of the absence of heavy returns |
| B4 | RH ⇔ ZAL ∧ B13 ∧ Landing `[L]`; instruments for a finite top layer (ELT) | each atom |

### 13.3 The walk

Each stage states what to prove, when it passes, where it is expected to stop `[A]`, and what to record at a stop. A stage that needs the half-plane carries it as a premise, as `jasDressedPSDAbove_of_xiZeroHalfPlaneBound` does; no axiom stands for `[X]`.

| Stage | Prove | Inputs | Passes when | Expected `[A]` | Record at a stop |
|---|---|---|---|---|---|
| **W0** the half-plane in the native graph | (a) the Fourier coefficients of the residue of the cubic Eisenstein family at `4/3` are the normalized cubic Gauss sums with the different-symbol phase, and `ρ(pq³)=‖q‖ρ(p)`; (b) removal of the cube indices by Möbius inversion; (c) the mean square of §3.2 with uniform bounds for both Poisson transformations; (d) detector and continuation: `Θ≤11/12`, then `Θ≤7/8` | `MetaplecticMobiusDescent`, where (a) is a theorem: the Fourier coefficient of the cubic residual source at a squarefree-times-cube index `ab³` is `\|b\|` times the conjugate symbol of the different times the normalized cubic Gauss sum of `a`, and these indices are its unramified support (`normalized_sourceFourier_squarefree_cube`, `sourceFourier_squarefree_cube_support_iff` `[L*]`); `HeckeLFunctions` (ray class characters of a number field: continuation, Euler product, functional equation); `FamilyContinuationTheory`: the continuation step for that family and its signal as the smoothed Möbius sum over the squarefree ideals (`heckeLFunction_ne_zero_of_family_common_signal`, `signal_heckeKernel_eq_tsum` `[L*]`); cards `metaplectic-mobius-descent`, `cubic-theta-residue-and-gauss-coefficients`; the cached external sources | both endpoints are Lean theorems of the native graph | passes if `[X]` is correct; the step at risk is (c), the uniformity of the transfer | the first estimate that fails, with its exponent; every later stage is conditional and says so |
| **W1** the map under the strip | the corollaries of §12.1 row 9: the rung `4/3`; large-prime positivity above level `11/8`; return-free windows at prime cutoff `T^{16}`; the scope guards without world II at `Θ=1` | JAS, SA, S3, ZCG modules | each is a corollary of the endpoint of W0 | passes: assemblies. The endpoint is read exactly by the signal of the zeta kernel: `Θ≤b` if and only if the signal is `O(Z^{b'})` for every `b'>b` (`zetaZeroAbscissa_le_iff_forall_signal_le` `[L*]`). In the native Hecke formalism the half-plane of the family of `ℚ` contains the one of `ζ` (`xiZeroHalfPlaneBound_of_heckeHalfPlane_rat` `[L*]`), and so does the half-plane of the family of the third cyclotomic field: `ζ_K=ζ·L(·,χ₋₃)` (`dedekindZeta_thirdCyclotomic`, `xiZeroHalfPlaneBound_of_heckeHalfPlane_thirdCyclotomic` `[L*]`). The transfer for a Dirichlet character (a ray class character `χ∘N`) is not in Lean | — |
| **W2** room below `7/8` (answered No `[D]`, §5.5) | question (B★) of §5.5: a power saving for the Möbius-weighted sum over the exceptional frequencies | `fixed_slot_boundary`, `retunedBoundary_sharp_minimum`, `gram_power_saving_boundary`; `QuasiRHShiftCorrelation`, `QuasiRHCharacterCorrelation` (CM4); `QuasiRHSubfieldMoment`; `IntegerIntervalResonance` | a saving `s>0` for the actual source: boundary `7/8−s/16` | undetermined; the first gate that no theorem predicts. A stop means: Möbius weights that come from inverting a coprimality restriction carry no cancellation where the sextic character is trivial `[D]` | the exact size of the weighted exceptional sum, and the best boundary of the profile at that size |
| **W3** `5/6` and `3/4` | one of: a joint Gram estimate in the region `ν≤1/15`, `κ+4ν≤4/3`; the near-band energy exponents `5/3+ε`, `3/2+ε`; even-total binary correlations of `μχ` of size `m^{2/3+ε}`, `m^{1/2+ε}`; the mesh covariances `J^{5+ε}`, `J^{3+ε}` | `QuasiRHDetectorGramTradeoff`, `ChebyshevThinBandAbscissa`, `QuasiRHPowerMeshMeanSquareAbscissa`, `QuasiRHDilationCovarianceAbscissa` | one estimate | inside the detector the floor of the low side is `29/36` unless the unit term, the principal normalization or the reflected allowance is replaced (`unitGramBoundary_sharp_minimum`); with the high side the published geometry is a vertex and the boundary stays above `7/8−1/4000` (`endpointExponent_pos_of_lowBoundary_le`), the binding estimate being the row count of the bin `δ=79/204`. The values `5/6` and `3/4` are not reachable inside the detector: its floor is `13/15` even with Riemann-hypothesis bounds for every row (`endpointExponent_floor_bin_pos_of_lowBoundaryGen_lt`). The receivers outside the detector have no source; positive weighting of the dilation channels is excluded with sharp exponents (`QuasiRHHighDilationPositiveEnvelope`) | the boundary reached; which of the three terms is the floor |
| **W4** the limit of leg A | for every `σ₀>½` a completed sum with two representations and margins at `σ₀`; or a theorem that the infimum of the boundaries over a stated class of sums and large sieves is above `½` | the budget modules as the model of such a theorem | boundary `½+ε` for every `ε` | stops. The direct bound is a mean square followed by Cauchy–Schwarz: it reaches the square root of the number of terms, and the principal signal is normalized by the same count. In the exact receivers of the corpus the line is the endpoint exponent (cumulative energy `r=1`; binary correlations below every power), and none of them is a mean square over a larger family. The boundary `½` needs cancellation inside the mean square. For the class of geometries of the compensated probe with termwise bounds on the nonprincipal rows the infimum is a theorem `[M]`: `13/15`, the cost of the rows without zeros right of the line when they are summed trivially (`endpointExponent_floor_bin_pos_of_lowBoundaryGen_lt`); below it the sum over the sextic twists has to cancel, a statement of the type of the ratios conjectures for the family. The dual-length term of the low side cannot be replaced by a bound for the rows that passes through the twists: Poisson summation in the row index expresses the mean square of the rows through the Möbius sums of the twists, the principal twists are the target with multiplicity and full prime amplitude, and with their excess at a zero `β` the low boundary is `β` identically (`lowBoundaryFree_add_half_principalExcess` `[M]`). The low estimate is the statement that the mean square of the rows is generic, and a zero right of the boundary is an excess in it; only a bound that sees the rows without the twists (the reflection) is an input. Without the dual-length term the low boundary is at least `5/6` (`five_sixths_le_lowBoundaryFree` `[M]`). The room `[13/15,7/8]` is the distance of the published row count from the density hypothesis for the sextic twists near real part `0.69` `[D]`. The source identity is one Jacobi sum with three realizations in one row variable; the two of lower order have rows of conductor `q_m³`, `q_m⁴` and larger corners (`corner_three_four`, `corner_four_three` `[M]`) | the infimum boundary of the class, as a theorem about exponents |
| **W5** leg B1 | `JasDressedPSD σ` for one `σ≤1`; or positivity of the Bernoulli product tests on the characters of all large primes at level one | `jasDressedPSD_two`; `exists_jasDressedPSDAbove_three_halves`; under the strip, large-prime positivity above `11/8`; `jasDressedPSDAbove_zeroFree_or_edge` | one level `σ≤1` | stops between `11/8` and `1`. Positivity above some `X` at a level `σ∈[1,3/2)` forces `\|Re ρ−½\|≤σ−1`: each level below `11/8` is a half-plane of its own, and level one is the line. Diagonal dominance ends where `Σ_p p^{−σ+δ}` diverges, at `σ=1+δ`; below that level the statement is a sign on products of large primes | the least level reached, and the family of tests on which positivity holds |
| **W6** leg B3 | the uniform transfer from return-free intervals to bounded absolute prime traces on `log²` windows | `WeightedReturnCounts`; `HomogeneousReturnTransferImpliesStripCollapse`; SOSZ windows | the transfer is a theorem | stops at the transfer: under a strip it is equivalent to RH (`homogeneousReturnWindowTransfer_iff_riemannHypothesis` `[L*]`); identity returns of the prime orbit are not the returns that carry a zero, and bounds on prime labels are shared by `ζ(s−h)` `[L]` | the longest window for which the transfer holds |
| **W7** leg B4 | AAL under `Θ≤7/8` (no finite top layer at `β∈(½,7/8]`), then ZAL | ELT, ZCG; `FiniteTopLayersNeedNoSeparation` | each atom | no first step (§5.3): the reduction ends at the signed centred type-II current at an isolated mode | — |
| **W8** | RH from one of W4, W5, W6, W7 | | | | |

### 13.4 Where the walk is expected to end `[A]`

W0 and W1 are formalization and assembly. W2 has the answer No (§5.5): the exceptional exponent is exact, and W3 inside the detector stops within `1/4000` of `7/8`, at a vertex of the low bound, the row count of one middle bin and the dual length of the reflected rows (§3.3). W4 to W7 stop at their first step. The expected end state is a native theorem `Θ≤b` with `b` in `[13/15,7/8]`, which is positivity of the dressed aggregate on large primes above level `b+½`; RH is level one (`riemannHypothesis_iff_jasDressedPSD_one`), a point of the same scale. What stands after it is the wall of §1.5(b) with the rung `1/(2b−1)` in the place of rung 1: a parity-sensitive power saving one step further, for which leg A has no second identity and leg B no producer.

### 13.5 What would change the guess

- **W0 fails.** No producer exists; the guess has no basis.
- **W2 has the answer No and no second completed sum is found.** Leg A sits at the vertex of §3.3.
- **A count of the sextic twists whose `L`-function has a zero near real part `0.69`, with exponent below the published `21766/32589≈0.668`, or a mean square of the reflected rows past the dual length `M+ℓ=1`.** Either moves the vertex: the high exponent of the binding bin is `−7/30672` at the published geometry `[M]`.
- **A second identity of the type of §7.2 (5).** Each one is a new leg A with its own budget. Those that split into two Gauss sums are classified below; over `ℤ[ω]` the sign comes from `J(χ_p,χ_p)=−p` for the cubic character of a primary prime `p` `[M]`. The sign law holds at every odd order: the `n`-th power of a Gauss sum of odd order `n` is `−N` modulo `(1−ζ)²`, and of even order `χ(−1)N` (`exists_gaussSum_pow_orderOf_eq_of_odd`, `exists_gaussSum_pow_orderOf_eq_of_even` `[L*]`). In the cubic architecture with one row variable the order six of the row twist is forced, and the floor of the balanced budget with principal frequencies the `n`-th powers is `1−4/(5n)` (`lowBoundaryOrder_lt_floorBinOrder` `[M]`): `13/15` at `n=6`, `11/15` at `n=3`, `3/5` at `n=2`. The cube identity `γ₃³=με` has realizations of order three with more row variables (the cubic theta row with two cubic twists; three cubic twists, which is the functional equation of `L(s,χ_A)³` with root number `μ(A)ε(A)`); their balanced low boundary is at least `1` (`one_le_lowBoundaryDesign` `[M]`), and the duplication formula turns the first of them into the published design. The source identity is one Jacobi sum: `g(χ)g(φ)=J(χ,φ)g(χφ)` with `χφ` quadratic and `J≡−1` (`exists_gaussSum_mul_gaussSum_eq` `[L*]`), `χ` the row coefficient and `φ` the row twist. Besides (cubic, sextic) there are two pairs with one row variable: order four with `φ=χ` over `ℚ(i)` (`γ₄²=μ·`explicit), frequencies fourth powers, and (sextic, cubic) over `ℚ(√−3)`, frequencies cubes. Their rows are sums of Gauss sums of order four and six, whose twist by `φ` is a change of frequency with conductor `q_m³` and `q_m⁴`; the published rows have conductor `q_m²` and reflect to a quadratic twist. Without slots the corners are `8/9`, `25/28`, `49/54` (`corner_two_six`, `corner_three_four`, `corner_four_three` `[M]`): the published design is the best of the three `[D]`. Without the dual-length term the low boundary at order `n` is at least `1−1/n` (`one_sub_inv_le_lowBoundaryOrderFree` `[M]`): `5/6`, `3/4`, `2/3` for sixth powers, fourth powers, cubes.
- **A level of the dressed aggregate below `11/8` proved as a positivity statement.** It is a half-plane below `7/8` (`xiZeroHalfPlaneBound_of_jasDressedPSDAbove`): a producer of another kind for the same scale.
- **An inequality with a power margin from a construction of §9.** By the receivers with slack (§13.1) it is a leg A of another kind.

### 13.6 Rules for the walk

- Before an estimate is attempted, the tests: it fails for the Liouville twist and for the lattice with a pair (§1.3); a self-improvement of a strip uses the family, because it fails for `ξ(s+a)ξ(s−a)`; a statement on prime labels fails for `ζ(s−h)`; a bound that holds for every coefficient array of norm one saves nothing at the exceptional frequencies.
- Exponents are theorems before estimates are sought: each stage first fixes its budget in Lean, as `QuasiRHDetectorScaleBudget` and `QuasiRHDetectorGramTradeoff` do for the detector.
- At a stop the strongest positive statement that the obstruction leaves is proved in Lean and recorded on the card of the stage.

---

## 14. Answers in one line each

1. **Big picture.** One inequality per prime and one matrix on the integers, with no margin; the corpus has every receiver, the price of every known mechanism, and the exact scale of what is known: sizes, below rung 1. Standing: natively a source above rung 1 (a parity-sensitive, joint, pointwise power saving); with `[X]` a source below `7/8`; and the atoms ZAL, B13, Landing.
2. **Opportunities.** The external half-plane inside the native graph; the census using information beyond raw positivity; a positivity-free census; the ladder as one theorem. Bounded Dirichlet constituents and the raw positivity route to `70%` are closed `[M]`.
3. **Quasi-RH.** One path: the external theorem `[X]` (`Θ≤7/8`, by continuation of the reciprocals of a family, with reciprocity for cubic Gauss sums as source) and its formalization, with three open local steps. No second path: by the corpus's own receivers quasi-RH is one rung above 1, one bounded long mollifier moment with `θ>1`, a power-saving variance of μ in long intervals, and sizes do not reach it.
4. **Seventy per cent.** `67.25%` is a theorem. The integrable Fourier positivity class has census ceiling at most `1−3/π²<7/10` `[M]`; reaching `70%` requires information beyond its unit-band data and two positivities.
5. **One question.** Among the corpus's own questions none below RH and quasi-RH is a door; the target is AAL — is the top of the zeros attained off the line — and it has no first step; the decidable questions with a first step are listed in §5.4. With `[X]` one question passed the tests: do the Möbius signs at the exceptional frequencies of the detector save a power (§5.5). Its answer is No `[D]`; the published geometry is a vertex of three estimates and the boundary of the probe stays above `7/8−1/4000` `[M]`, the binding one on the high side being the count of the rows whose characters have zeros near real part `0.69`.
6. **Without positivity.** Sign-free conversions from a law to a point exist, three native and one in `[X]`; bounded Dirichlet constituents are now excluded by `bounded_dirichlet_constituent_ne_zero` `[M]`. `[X]` uses no sign of a form attached to ζ and survives the constraint in its narrow reading.
7. **New field.** The walls are not walls of language; what is missing is a source: parity-sensitive arithmetic at power-saving scale. Its one theorem is `[X]`; its open core is the classification of the identities that turn Möbius into coefficients with a functional equation.
8. **New field without positivity.** Conversion theory: recurrence against density, budget overflow, winding, and the rightmost zero of a family `[X]`, as one subject with exponents.
9. **`𝔽₁`.** The square, the ring, the lattice, the genus and the paid contacts exist as theorems; open is one property that is an inequality; six constructions with kill conditions.
10. **Galois theory.** RH ⇔ `c=ι` ⇔ the ordinate is injective; no equation, no factor, no periodicity, no lattice; the reading that sees `c` is the trace form and is Weil's sign.
11. **RH false.** Two worlds and a list of constraints (with `[X]` every failure lies in `1/8≤Re s≤7/8`); certificates are finite and equivalent to the failure; in world I the counterexample is a limit formula in the primes; no asymmetry toward a refutation is visible.
12. **Missed.** Nine assemblies (the ladder theorem, a positivity-free census, the positivity ceiling, the Krein census, the trichotomy, B13 in index form, verification as a rung, the depth sum, the map under a strip) and ten closures.
13. **Most likely route.** Two legs: a half-plane by continuing the reciprocals of a family across its rightmost zeros, with a reciprocity identity as source (`[X]` at `7/8`), and a conversion of a half-plane into the line, for which the corpus has no reduction: positivity of the dressed aggregate on large primes at level `σ` is the half-plane `σ−½` and RH ⇔ `JasDressedPSD 1` with no premise, the head bounds are abscissa laws, and the return transfer, the one statement of the right shape, is equivalent to RH under a strip `[L*]` with no known use of its premise. The gate of §5.5 is closed with the answer No; inside the published probe the boundary lies in `[13/15,7/8]` `[M]`, and a lower boundary needs cancellation across the nonprincipal rows or another probe.
