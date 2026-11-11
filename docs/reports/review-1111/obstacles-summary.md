# Obstacles summary — status quo

Companion to [route-obstacles.md](route-obstacles.md) (per route), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ) and [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem). Corpus checkpoint: commit `f31c63def1` with its working tree (2026-11-11). Fact log: `logs/review-1111-status-quo-facts.md`; identifiers in parentheses refer to log §3, `D1–D8` to log §5.

**Evidence.** `[L*]` Lean statement read at the declaration for this report; `[N]` declaration located through the corpus search index, docstring read; `[F]`, `[KR]` stated by the frontier map and the scoped-obstruction ledger at the checkpoint, Lean not re-read; `[S]` module graded unfinished or unintegrated by the frontier map; `[D]` deduction made here from `[L*]` statements; `[C]` classical mathematics quoted from memory, not in the corpus, to be checked before use; `[A]` assessment; `[X]` one external source cached in the repository, outside the native import graph and not checked here: a zero-free half-plane `Re s>7/8` for ζ, Dirichlet `L`-functions and Hecke `L`-functions over `ℚ(√−3)`. The frontier map states that the native graph has no unconditional `7/8` theorem [F]. Sections 2.3–2.14 and 3 are interpretation and ideation: every untagged statement there is a proposal, not a result.

**38 live formulations; 12 candidates** (SEC, CDC/BSH, S3, APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF). HJ is PA; PCS, DR, PW-B are retired labels.

**Notation.** As in [route-obstacles.md](route-obstacles.md): `Θ`, `Θ∞`, ZAL, AAL, B13, Landing, DH, B56; world I, world II, the edge world; the prime trace `2Re S(log p)`; logarithmic windows; tangent datum and normalized trace; the comb pairing and the comb form; step packets; system, mass, dominated, rung, trivial aperture, Liouville twist; `JasDressedPSD σ`; the signal of the zeta kernel. **The scale** is the common parameter of the graded receivers (§1.2). A statement is **off the scale** if it carries no exponent (§1.5).

## 1. Big picture

### 1.1 One object, two exact forms
- **One inequality per prime.** RH ⇔ `2Re S(log p)≥−K` at the primes of arbitrarily late logarithmic windows outside `Ce^{δT}` primes per window. Equivalent on the same windows: the upper bound alone, without omissions; `ℕ`-counts on the surviving rays `Γ_1+Γ_p` with quadratic limit the plane defect; local even moments with one growth exponent for all orders; the absolute value [L*] (S1–S6).
- **One matrix on the integers.** RH ⇔ exactly one positive square of the comb pairing on packets; the negative index of the defect is the number of distinct right zeros, for ζ with Dirichlet characters, for every primitive ray class character of every number field, for every Dedekind zeta function through its ideals, and for the class characters together [L*] (G4, G5, AGZ6–AGZ8). At finite scale: RH ⇔ `𝔚_{3K+1}≥0` on step packets of `3KR` blocks for all `K,R`, a family of finite matrices whose entries are pole moments `log(b/a)`, `b−a`, a closed form of the jets and overlaps `(b/k−a)⁺` with the weights `Λ(k)`, `k≤3K+1`; ⇔ eventual exact nonnegativity of the comb form on every fixed ratio window; ⇔ a positive coefficient-mass floor `γ(Q)` on each ratio window [L*] (AGZ1, AGZ2, HFP1, HFP2).

### 1.2 One scale
Every graded receiver of the corpus is an equivalence at each level of one scale [D] (D1):

| Reading | Parameter | Depth it reaches | Evidence |
|---|---|---|---|
| saving of the contacts `n^{½+γ}` | `γ` | sign to rung `κ<1/(2γ)` | [L*] (L6, SA1) |
| the sign on a rung `κ` | `κ` | no isolated zero of depth `>1/(2κ)` | [L*] (L9, SA1) |
| bounded dyadic Möbius moment at length `T^θ` | `θ>1` | depth `<1/(2θ)+ε` eventually | [L*] (J6, SA1) |
| level of the dressed aggregate on large primes | `σ≥1` | `\|Re ρ−½\|≤σ−1` | [L*] (J1) |
| exponent of the signal of the zeta kernel | `b∈[½,1)` | `Θ≤b`, and conversely | [L*] (FCT2) |
| exponent of a floor of the two-bump form | `σ` | floor exactly `σ` | [L*] (FFA1) |
| window moment of order `2k` with exponent `A` | `A/2k` | the abscissa law at depths `≥A/2k` | [L*] (FFA10) |
| horocycle exponent | `α` | `Θ≤2−2α`; with a finite Euler filter `Θ∞≤2−2α` | [L*,S] (N8) |

Level one, rung `∞`, every `b>½`, exponent zero: each end of the scale is RH. Sizes prove the scale up to rung `1−o(1)`: every dominated system is positive with margin below the trivial aperture `log log(mass)` and the Liouville twist fails just above it, in the conductor aspect; in the height aspect the gap between floor and failure is `log(π/2)` [L*] (L1–L5, SA6). At the first conductor rung the sign for a real character forces primes with `χ(p)=1` and with `χ(p)=−1` below `e^{2η}log²q` [L*] (SA3). At a rung `κ` the sign on bounded shapes fails only on a set of heights of measure `≤T^{1−1/(2κ)+ε}` [L*] (SA2). Natively no rung above one is proved in any aspect; `[X]` states the level `b=7/8`.

### 1.3 Three structures; every two have a model
ζ has an Euler product, the Riemann functional equation, and every integer with multiplicity one. The corpus has a model for each structure alone and for pairs [L*] unless marked:

| Structure kept | Model | What fails | Evidence |
|---|---|---|---|
| reflection symmetry, temperedness (every identity of the explicit formula) | every tangent datum is the top layer of a finite symmetric configuration | AAL, B13 | FFA15 |
| positivity of the prime measure, a simple pole | a nonnegative density with any finite layer at any `Θ<1` | AAL | FFA14 |
| Euler product over natural norms, natural coefficients, linear counting | every finite divisor right of the line, with multiplicities, continuation to `Re s>½` | AAL, B13; graded repulsion (two-scale products) | FFA12, N3, S15 |
| Euler product over the rational primes, with repetition | every finite layer at `17/30<Θ<1` | AAL | FFA13 |
| nonnegative prime and integer densities, integer count `N(x)−ρx−C→0` (continuous system) | a rational zeta function with one off-line pair, tending to `1` on vertical lines | AAL; recurrence of a zero | [N] (X1, X2) |
| the Riemann functional equation, Gamma factor, residue one, order `≤1`, count within one | all zeros simple, off the line, approaching it | Landing | C6 |
| Euler product and a functional equation of degree two on the integers, unbounded coefficients | `ξ(s+a)ξ(s−a)`: every abscissa moved by `a` | ZAL; strip self-improvement | [KR] |
| both structures up to an integrable defect, positive continuous prime measure | `ζ(s)exp(ε/(s+1)²)` | nothing: the zeros are those of ζ | W1 |
| the Riemann functional equation with an `L²` defect on a countable system; or count `n+o(log n)` | the rational primes alone | — | C13; [KR] (X3) |
| Euler product over geodesic norms and a functional equation, order two | Selberg zeta functions of surfaces with small eigenvalues: finitely many real zeros in `(½,1)` | B13 | [C] |

Consequences [D] (D8). What the models realize is analytic, positive, or multiplicative with integer norms. What no model of the corpus realizes is the unit multiplicity of every integer and the exact functional equation, and each of the two alone identifies ζ. Both are statements about addition on ℤ. The atoms have no model among Dirichlet series over the integers with the Riemann functional equation; outside that class B13 fails in a classical family.

### 1.4 Two worlds, three atoms, one shape of world I
`Θ<1 ⇔ Θ∞<1`; a failure of quasi-RH is `Θ=Θ∞=1` with AAL [L*] (S13). RH ⇔ ZAL ∧ B13 ∧ Landing [F]; B13 ⇔ the supremal negative index on real packets is `0` or `∞` [L*] (S16).

World I has one shape. At `b_*=Θ−½` the normalized trace is in exactly one of four sectors: RH; top line empty and trace `→0`; top line finite nonempty and trace asymptotic to a nonzero real trigonometric polynomial; top line infinite and no such limit [L*,S] (N1). AAL is the absence of the third sector, and it has four equivalent or sufficient forms [L*]:

| Form | Statement | Evidence |
|---|---|---|
| unit gap | for every line `Re s=½+h` the number of zeros to its right is at most one or infinite | FFA5 |
| non-attainment | for every depth `b` bounding all zeros there are a length `L` and arbitrarily late windows of length `L` on which the trace is `≤εe^{bu}` for every `ε`; the same for `ψ(x)−x` against `x^β` on multiplicative windows, and at the primes of the window | FFA4, FFA6, FFA7 |
| amplification | one growth exponent for all even moments of the trace on late windows of one length | FFA9 |
| horizon | no nonzero Euler polynomial filter accelerates the horocycle rate past `1−Θ/2` | N8 [S] |

The receivers hold for every tempered conjugation-symmetric configuration without real right zeros, so their hypotheses fail on every model of §1.3 [L*] (FFA docstrings). A one-sided floor on windows of one length has a finite-stratum model; floors at every length give AAL [L*] (FFA8, S12). In world I the multiplicities are quantized: the Bohr mean of the normalized trace at a top frequency is zero or at least `2|B̂|²` in modulus [L*] (FFA17); `1/ζ` and `ζ(2s)/ζ(s)` have at a right zero a pole of order the multiplicity [N] (FFA18).

### 1.5 Off the scale: four kinds, each with a receiver and a kill
| Kind | Receiver | Kill | Evidence |
|---|---|---|---|
| homogeneous floor | a floor `−C‖f‖²` of the clock regulator at one cutoff per large aperture gives RH | the regulator lies below Weil's form at every cutoff: a negative direction of the limit is negative before the limit | [L*] (FFA24) |
| unit gap | an analytic approximant of ζ with at most one right zero, infinitely often, gives RH; a form with one negative square in which the right zeros are a symmetric spectrum gives RH | `Λ(s)/Λ(s+N)` has exactly the right zeros of ζ; the heat flow has the nonreal count of its limit | [L*] (FFA20, FFA25, FFA26) |
| certificate | some feasible weight system at every aperture gives RH | feasible systems converge to `Λ` in every coordinate; the pencils `ξ(s+h)+ξ(s−h)` and the cleared Eisenstein constant term are no Dirichlet series over their dominant half | [N]; [L*] (FFA21, FFA27, N4 [S]) |
| amplification | one exponent for all even window moments gives AAL | bounds of all orders with one exponent are bounds for the powers of the sup norm; one order `2k` reaches depth `A/2k` | [L*] (FFA9–FFA11) |
| symmetrization | a functional decreasing under projection to the line | an entire symbol monotone under splitting has zero real part on the line; additive functionals of the depths are functions of the inner masses | [L*] (FFA28, FFA29) |
| replication | a bounded normalization of translates at every right zero gives AAL | under a finite right layer every locally uniform limit of normalized translates vanishes | [L*] (FFA19) |

### 1.6 The half-plane route is two estimates
Over `K=ℚ(ζ₃)`: if, whenever the pole-cleared Hecke `L`-functions of `K` are zero-free in `Re s>β`, every ray class character `η` has a sum `J_η` with `‖J_η(Z)‖≤CZ^{a₁}` and `‖J_η(Z)−f_η(Z)‖≤CZ^{a₂}`, `f_η` the signal of `exp((s−c)²)H_η(s)/((s−1)L(s,η))`, with `a₁,a₂<β` common to all characters and for every `β>σ₀`, then `Θ≤σ₀` [L*] (N5). Continuation, the factorization `ζ_K=ζ·L(χ₋₃)` and the supremum step are theorems [L*] (FCT5, FCT6). The source identity is in Lean: the cube of the normalized composite cubic Gauss sum is the ideal Möbius value times a phase; for characters of order dividing `n>2`, `g(χ)g(φ)=(−1+z(μ−1)²)g(χφ)`; for odd order `g(χ)^n=−card F+z(μ−1)²`, for even order the sign is `χ(−1)` [L*] (W5, FCT9, F3). The cubic residue with normalized Gauss coefficients on squarefree-times-cube support, and its Gauss-series formulas for `Re s>2`, are in Lean [F].

The exponent budget of the published probe is in Lean as a calculus of exponents, not of sums [L*] (FCT11–FCT17):

| Statement | Value |
|---|---|
| boundary with the published row count | in `(7/8−1/4000, 7/8]`: a vertex of three estimates |
| nonprincipal rows with RH-quality bounds, summed trivially | not below `13/15` |
| twist order `n` in place of six | balanced floor `1−4/(5n)`; conductor corners `8/9` at `(κ,n)=(2,6)`, `≥25/28` at `(3,4)`, `≥49/54` at `(4,3)` |
| two or more row variables of order `≥3` | balanced low boundary `≥1` |
| reflected rows evaluated through the same twists | the low boundary equals the zero `β`: circular |
| without the dual-length term | `≥5/6`; at order `n`: `≥1−1/n` |

Deductions [D] (D4). The room inside the probe is `[13/15,7/8]`. The Möbius sign needs an order above two (F3), and at order `n` the low side is at least `1−1/n`; so no source of this architecture has a boundary below `2/3`, and with the accounting of the published design not below `13/15`. Natively open: removal of the cube sum in the source comparison, the properties of the corrections `H_η`, and both savings uniformly in the character [F].

### 1.7 Finite scale and the index in the aperture
The negative index of the restricted Weil form is nondecreasing in the aperture; immediately right of an aperture it is the index plus the nullity; resonant apertures are finite below every bound [F] (ACCE1). `r≤#`right zeros ⇔ for some ratio and margin the robust index of the finite comb is eventually `≥r` [L*] (HFP3); the unshifted comb index at ratio `Q` lies eventually between the aperture index and index plus nullity [L*,S] (HFP4). So RH ⇔ no aperture carries a null mode, and in world I with finitely many off-line zeros finitely many resonant apertures carry the whole index [D] (D2).

### 1.8 The square returns identities; deformations return RH
Bézout holds for one constant, one set of contacts, one tree length [L*] (G1–G3). Planar restriction is an equality of ideals; the count on two graphs is the split norm; the sections of the first `N` graphs in aligned boxes number the volume over `N!`, with no quadratic term; the system of the squares fails on its own comb; in towers the base has weight `1/d`, among class characters `1/h` [L*] (G7–G10, AGZ8, AGZ10). The price path of any `n₀≥2` adds a square to the zero sum, is monotone, holds on packets of a given length from a threshold on, and on all packets is RH at every parameter; the tree-length path exists at `2` only [L*] (AGZ3–AGZ5). Every one-parameter family through ζ in the corpus has the count of its limit or is RH at every parameter [D] (D5).

### 1.9 Constituents
No bounded holomorphic Dirichlet series on a half-plane, at any abscissa, and no absolutely convergent expansion on a strip about the line, has a zero there with its zeros among those of ξ; a Wiener expansion with an interior zero has nonsummable residues `Σ|m_ρζ(ρ)/ρ|` with no purity premise, and no `ℓ^p` family of displacements carries its zeros to zeros of ζ [L*] (CTZ1–CTZ4). Every box has a Dirichlet polynomial with exactly the zeros of ξ, of unbounded length [L*] (K4). The convergent series `(1−2^{1−s})ζ(s)` has in the open strip exactly the zeros of ζ [C]: between the bounded class and the convergent class no question with a first step is open [D] (D6).

### 1.10 Verification
RH is verified through 67; verification through `windowHeight(a)` gives the sign on `[−a,a]` [L*] (J2, J3); for this construction `log log log windowHeight(a)=c·a^{4/3}+log 138+o(1)` [F]. The form on tests supported in `[−a,a]` is diagonal in frequency: `(1/2π)∫|f̂|²·symbol_a` plus the pole terms, with `symbol_a(τ)≥log|τ|−C−2Σ_{n≤e^{2a}}Λ(n)/√n`; so the part of the integral above `T_a=exp(C+2ψ₁(e^{2a}))` is nonnegative for every test [D] (D3, from L8). The best margin of a window is at most `K exp(11a/2−πe^{2(a−2)})` [KR].

### 1.11 Law and point
Past the Vinogradov–Korobov region every unconditional native theorem about the location of the zeros of ξ is in law: twisted moments below the square root, resonator means, the measure of exceptional heights on a rung, the depth sum `Σm_ρ·depth≤CT` [L*] (A119, log §3.17), `67.25%` simple critical zeros. Finite relocation of zeros is invisible to quadratic tests of length `o(T²)` [KR]. The pointwise theorems act on constituents, finite layers, models and regulators. `[X]` is pointwise right of `7/8`.

### 1.12 Receivers are complete; the price of each producer mechanism
| Mechanism | What the corpus proves | Evidence |
|---|---|---|
| Surface, sections, Riemann–Roch (Weil) | identities; no quadratic term in the count of sections | [L*] |
| A bounded-below naive height and Tate's limit | RH ⇔ counts on the surviving prime rays; hyperelliptic curves have the count law | [L*] |
| A family with monodromy (Deligne); the tensor-power trick | fixed part; weights `1/d`, `1/h`; all orders of a window moment are sup bounds | [N]/[L*] |
| A Frobenius with zero derivative (Stepanov) | at one prime `p^{11/12}` | [F] |
| A dominant half (Hermite–Biehler); pure objects | index law; sizes on a circle; pure objects are no Dirichlet series over their dominant half | [L*] |
| Deformation to a known case | price paths, tree lengths: RH at every parameter; mass: floor to the trivial aperture | [L*] |
| A regulator | clock below the form; tower and heat flow with the count of the limit | [L*] |
| Recurrence (Bagchi); normal families | RH ⇔ strong recurrence; zero limits under a finite layer; no bounded constituent | [N]/[L*] |
| Existence of weights (duality) | RH ⇔ feasible weights at every aperture; they converge to `Λ` | [N]/[L*] |
| Sizes of the contacts | the trivial aperture; nothing beyond | [L*] |
| Mean values | below the square root; relocation-invariant below the height | [L*]/[KR] |
| Power sums, half-period deletion, Vandermonde on windows | finite layers on bounded windows | [L*] |
| Continuation of the reciprocals of a family with a reciprocity identity | one implication with two estimates; budget room `[13/15,7/8]`; the half-plane is `[X]` | [L*]; [X] |

Consequence [D]: natively every route is a receiver. The one producer is `[X]`, outside the native graph.

### 1.13 What is ruled out
| Mechanism | Verdict | Evidence |
|---|---|---|
| The explicit formula, positivity of the prime measure, Euler products over integer norms or rational primes, linear counting, as a constraint on a finite top layer | every tangent datum is realized | [L*] |
| One-sided floors on windows of one length; windows below the logarithmic radius | models | [L*] |
| A regulator as a source of a sign, a unit gap or an index bound before the limit | below the limit, or the count of the limit | [L*] |
| A certificate other than `Λ`; a pure object with ζ's Gamma factor as a certificate | converge to `Λ`; no Dirichlet series | [L*] |
| Linear statistics and additive depth functionals as monotone quantities under projection | excluded | [L*] |
| Replication of a top zero by a normal family of translates | zero limits | [L*] |
| Amplification over the order of a window moment as an independent source | it is a sup bound | [L*] |
| A path of squares as a transport of the sign | RH at every parameter | [L*] |
| A Gauss-sum probe of the published architecture below `13/15`; other orders, more row variables, other conductors; reflected rows through the same twists | budget | [L*] |
| A bounded or Wiener constituent of ξ with a zero | none | [L*] |
| The return transfer as a step from a strip to the line | RH under a strip | [L*] |
| Positivity alone as a 70% census certificate | cost `≥1+3/π²` | [KR] |
| Sizes of the contacts beyond the trivial aperture; a bounded gap for the exceptional square; sections of the square as a source of a sign; a free contact weight, constant, scale or tree length; a per-degree limit in a tower; an own comb; landing from the functional equation with Gamma factor and count; repulsion from Euler products; rigidity of positive continuous prime measures; bilinear statements as parity-sensitive information; a family as a source of purity by averaging; one glued invariant carrier | as recorded | [L*]/[KR] |

## 2.1 Tasks that are just work

Difficulty is established only where a known argument exists; `(unverified)` marks the rest. None of these decides RH. Status by corpus search at the checkpoint (log §3.17, §4).

### The native half-plane (given `[X]`)
| # | Task | Routes | Basis |
|---|---|---|---|
| A118a | removal of the cube sum in the comparison of the cubic-residue sum with the corrected signal | JAS, MC, S3 | `zetaZeroAbscissa_le_of_two_estimates` (N5); cubic residue formulas [F] |
| A118b | the corrections `H_η`: holomorphic and nonvanishing right of the boundary, bounded on `Re s≥2` | — | `heckeHalfPlane_of_family_corrected_signal` |
| A118c | the comparison saving uniformly in the ray class character | — | `exists_bound_of_height_estimates` (FCT8) |
| A118d | the direct bound: reflection of the completed theta row; quadratic and sextic large sieves over `ℤ[ω]`; the zero detector with its bins | — | planar and Eisenstein large sieves, buffered bins [F]; budget (FCT11) |

### Assemblies of proved pieces
| # | Task | Routes | Basis |
|---|---|---|---|
| A132 | The order of the verification height. Sizes pay every frequency above `T_a=exp(C+2ψ₁(e^{2a}))` [D]; a lower bound for the margin of the verified part (a sampling inequality for band-limited functions on the verified ordinates) would give `log log windowHeight(a)=O(a)` in place of a triple exponential (unverified) | RW, SRT, TH, LI, HCF | `feasible_of_symbol_nonneg`, `weilAtomSymbol_eq_twisted` (L8); `windowPositiveAt_of_rhVerifiedThrough`; the margin ceiling [KR]; `sourceQuadratic_ge_of_offLineCopiesLocallyBounded` [N] |
| A133 | Artin characters of non-abelian extensions: the index law per character (unverified) | ACS, HF | the index law for ray class characters (AGZ6–AGZ8); `hasSum_zeros_explicit` (AGZ14) |
| A134 | The main expression of the linear Levinson detector below the square root: a proportion of critical zeros from the native twisted moments (unverified) | WD | detector identity and `O(T^{7/8})` remainder [F] |
| A135 | The step-packet matrices at window ratios 4 and 7 as certified finite statements with the block-approximation error (unverified) | ACS, HF, RW | `riemannHypothesis_iff_forall_packetForm_stepPacket_nonneg`; `packetForm_flatPacket_eq` |
| A136 | Integration of the modules graded [S]: the unshifted comb index, the trace classification, the reflected halves, the Laguerre tails, the Euler-filtered horocycle exponents, the detector remainders | — | frontier map |
| A137 | The tangent data of `μ` and `λ` with an explicit formula for `M(x)` in world I (unverified) | ZCG, MC | `meromorphicOrderAt_mobius` (FFA18) |
| A78, A89 | Cluster form of the separated-window theorem; a prescribed radius in the sub-logarithmic model (unverified) | SRT | the finite-mode theorem |
| A47 | Constants of the one-quartet world (unverified) | ZCG, BAG | the growing-order reduction |

### Finite verification and explicit constants
| # | Task | Routes | Basis |
|---|---|---|---|
| A1 | Certified `RHVerifiedThrough T` past 67 | all rungs | `rhVerifiedThrough_sixtySeven` |
| A2, A3 | Numeric values of the explicit heights; membership on the first windows | window routes, TH, LA, HCF | explicit definitions |
| A4, A5 | Theta rank 15 and beyond; certificate of the center-tail failure (unverified) | TH | height 67 |
| A6, A7 | Cone widths; certificates on the anti-diagonals (unverified) | CHT, ACT | convex programs |
| A9, A13 | Constants at the eighth-root horizon; near-gcd charges (unverified) | HF, AIP | proved limits |
| A117 | End points of the feasible interval of `w(2)` on the first selective window | RW, ACS | `poleFeasible_of_abs_sub_le`; `exists_bounds_fst_of_lt` |
| A19 | An explicit height for the heat horizon | ZCG | `riemannHeat_no_collision_near_height_subWeyl_band` (existence of `X₁`) |
| A48, A58 | Hasse–Weil tests at verified scales; effective gap iteration (unverified) | ACS | window rungs |

### Classical inputs to formalize
| # | Task | Routes | Basis |
|---|---|---|---|
| A18, A21 | Twisted second moments past the square root; logarithmic two-point Chowla [C] | WD, MC | `θ<½` in Lean |
| A26 | Weyl asymptotic `N(Λ)∼Λ/12` [C] | PM | `weyl_law_order`: order `Λ` |
| A33 | Fourier coefficients of the cubic residue at all heights [C] | MC, MMD | formulas for `Re s>2` [F] |
| A41 | Count law for every curve over `𝔽_q`, first case plane quartics [C] | ACS, PM | elliptic and split hyperelliptic curves |
| A59 | Short-interval primes in a residue class [C] | ACS, SRT | gap sets |
| A115 | The Newton polygon of the Carlitz–Goss zeta function from the greedy optimum [C] | sign-free calibration | `isOptimal_iff_isGreedy` |
| A120 | A finite nonempty stratum with both structures: Selberg zeta functions of surfaces with a small eigenvalue [C] | BAG, ZCG | `selbergSmallEigenvalue_offCritical` [N]; the Selberg Euler product [N] |

### Further items
A16 numerical `r,m,q`; A20 a Jensen rung toward the saddle scale; A24 certified scans; A28 reciprocal-quadric traces; A30 best stencil exponent under RH; A42 Gamma-weighted transport to the adaptive head; A46 singular indices; A54 cusp expansion for Bianchi resolvents (all unverified).

## 2.2 Open mathematical obstacles

### The common minimal face
| # | Problem | Strength | Routes |
|---|---|---|---|
| B130 | `P(p)≤A(p)+K`, or the upper bound of the trace, on the primes of arbitrarily late logarithmic windows; any growth `Kp^σ`, `σ<½`, is a zero-free strip. Known natively: the VK saving | RH (≥qRH) | ACS, SRT, WL, HF, ZCG, HAT-C |
| B159 | A rung above one: a power saving of ζ's contacts on the integers between `m` and `m^{2κ}`, uniform in the height, that fails for the Liouville twist | ≥qRH | every sign route; BAG |
| B144 | Separation of the deep off-line ordinates of ζ | sub | SRT, ACS |

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Weil's sign on every window; equivalently the fixed-height energy floors | RH | all sign routes, HAT-C |
| B152 | The sign on step packets, in any of its four finite-scale forms | RH | ACS, HF |
| B160 | `JasDressedPSD 1` | RH | JAS |
| B18 | A construction of feasible weights at every aperture: by FFA21 it is the sign for `Λ` up to coordinates at the edge of the window | RH | RW |
| B2, B4, B5 | Bounded oscillation of `Ψ` to contact (no null mode at any aperture); outer predictors and Schur bands; kick admission | RH | RW, GWZ, WTZ |
| B6, B8, B101 | Full-space sign at every critical multiple; head thresholds; polar payment at every ratio | RH | HF, SRT, AIP |
| B104 | Polar orthogonality at the critical curve: whether a critical half-line ground state at finite `W` can be orthogonal to the polar source | method | HF, SRT, AIP, ACS, SC |
| B123 | Correlated arithmetic pairings dominating the depleted kernel | method | HF |
| B156 | Arithmetic cluster exclusion on a rung for ζ | method | SA, RW |
| B9–B11 | No zero mode; top coprime stratum; exact SOS on a two-prime lattice | RH | HF, SC, ACS |
| B12, B14, B23 | Index ceiling uniform in resolution; any interior width value; `N_d` bounded | ≥qRH | CHMD, LA |
| B15 | Past Vinogradov–Korobov | sub | every route |
| B16, B17, B3 | Decay law of the margin; signed ground states past `log ρ`; variation of `r` free of `1/μ` | sub / method | CHT, RW |
| B19–B21, B102 | Torus law for `S*`; amplitude oscillation; all theta ranks; the signed adaptive head | RH | TH |
| B22, B24, B25 | Outer roots of the Jensen polynomials; collisions at small time; frequency below one | RH | LA, ZCG |
| B27, B28, B47 | Runs of simple critical zeros; local positivity at fixed `λ` on density-one heights; multiplicity by a non-size input | sub | ZCG, RW |
| B29–B45 | The single open estimates of PTR, HCF, PA, XN, GTA, TT, CHMD, RN, SZ, TG, SC, ACS, HF, FU/CFC/RP, LI, ACT, AIP | RH | as named |
| B124 | Finite initial depth budgets of the heat divisor | ≥qRH to RH | ZCG, LA |
| B146, B171 | An independent family of bounded index converging to ξ; a form of signature `(1,∞)` from the places in which the right zeros are a symmetric spectrum | RH (producer) | W1C, PTR, IRP, PM |

### Π — precision and production
| # | Problem | Strength | Routes |
|---|---|---|---|
| B161 | The signal bound `O(Z^b)`, `b<1`, natively: equivalent to `Θ≤b`. `[X]`: `b=7/8` | ≥qRH | JAS, MC |
| B174 | The density of sextic twists with a zero near real part `0.69`: the room `[13/15,7/8]` of the probe | sub (given `[X]`) | JAS, MC |
| B175 | A bound for the reflected rows that does not pass through the twists; cancellation across nonprincipal rows: a boundary below `13/15` | producer | JAS, MC |
| B48–B54 | Deciding input at square-root precision; endpoint energy; trivial-gauge half power; moving power windows; rows and BSY; regularized partial sums; extremal inequality | RH | WL, MC, SQF, JAS, CTF, PBM, RB |
| B55, B67 | Polynomial stencil rate; parity at power saving | ≥qRH to RH | WL, MC |
| B56 | `Θ<1⇒Θ=½` | ≥B56 | whole programme |
| B57 | Depth density `o(T)` | sub | WD, CTF, MC, RW, PM |
| B58–B61 | `D_win`; cluster wall; Green moments at deep zeros; a detector past the last scale | sub | WD, MC |
| B62, B63, B66 | Cofinal long moment; collision charge; near-unit holomorphic budgets | RH | WD, CTF, AIF |
| B91, B94 | Cut-kernel mass; cubic theta identification and rational descent | RH; past VK | RAC, MMD |
| B46, B97, B121, B137 | Proportional saving at length `(log X)^{2K}` at all heights; first return past the VK rung; freezing beyond the cap; collective depth floor | sub | BAG, PTT, TAPO, TTPO, CDGeo |
| B106 | A correspondence on the orientation cover with bounded local indices | RH | MC, HAT |
| B110, B126, B127 | Thick crude count; a one-sided bound on a sampling set; positive-measure lag recurrence | AAL | WL, ZCG, ACS, IWT |
| B145 | The signed, prime-weighted centred type-II current, with both continuum terms, at a growing isolated mode | AAL [D] | ZCG, BAG, ELT |
| B148 | The return transfer | RH under a strip | S3, BAG |
| B150 | Arithmetic upper control of the pair correlation beyond frequency one: a form factor bounded by `4` on `(1,10/9)` | sub | census |
| B173 | A two-sided subexponential bound of the trace on late windows of one length | AAL | ZCG |

### Γ — selection, reflection, transport, count
| # | Problem | Strength | Routes |
|---|---|---|---|
| B13 | Finitely many off-line zeros ⇒ none ⇔ the packet index is `0` or `∞` | sub | whole programme |
| B138 | Landing for ζ | sub | ZCG, LA, ELT, HF |
| B141 | Deuring–Heilbronn for ζ: `¬AAL⇒ZAL` | sub | BAG, ZCG, ELT |
| B83, B170 | AAL; non-attainment for ζ in any receiver form | sub / AAL | BAG, JAS, SC, ZCG, WL |
| B157 | What excludes a finite stratum when both structures are present | method | BAG, ZCG, ELT |
| B89, B112, B128 | A bounded aligned return at each right zero; the functional equation into vertical transport; replication by a mechanism other than normal families | sub | BAG, ZCG, EFT |
| B68, B71 | Reflection Krein positivity, flux, dispersion; universal decay and the horizon rates | RH | PM |
| B72–B76 | Cutoff-uniform target mass; the candidate zero-parameter conditions; FE-pair reality | RH | BAG, candidates, ZCG |
| B80, B81 | FE twins in the full class; candidate landings | sub; producer | SEL; candidates |
| B86 | Endpoint character positivity at unbounded rank | RH | ECP, ACS |
| B87 | A nonnegative count on the rays `Γ_1+Γ_p`, defined without `Q` | RH | ACS, HF, PM |
| B88 | The sign of the comb finite part | RH | HF, ACS, HAT, AGZ |
| B114, B117 | A realization of the partner involution outside the excluded classes; a regulator with a sign, a gap or an index bound before the limit | producer | PM |
| B147 | Shimura nonvanishing at `ρ/4+¼` for one Hecke eigenform | indep. | PM |
| B149, B169 | Bézout for the comb pairing from a property of the object; a group with a doubling on which the defect is a canonical height | RH (producer) | ACS, HF, AGZ |
| B172 | A nonlinear functional of the zero configuration that decreases under projection to the line and is computed from the primes | producer | ZCG, HF |
| — | ZAL | ≥qRH | whole programme |

### Settled method questions
| # | Question | Answer | Evidence |
|---|---|---|---|
| B153 | A bounded or almost periodic constituent of ξ with a zero | none, at any abscissa in the bounded class and on any strip in the Wiener class; no purity premise; no `ℓ^p` transport | [L*] (CTZ1–CTZ4) |
| B158 (budget form) | The boundary of the order-`n` probe; whether its infimum is `½` | room `[13/15,7/8]` for the cubic design; other orders, more row variables and other conductors are worse; the low side is `≥1−1/n`; reflected rows through the twists are circular | [L*] (FCT11–FCT17) |
| B169 (path half) | A Lefschetz path at an odd prime | the tree-length path exists at `2` only; the price path exists at every `n₀≥2`, and on all packets it is RH at every parameter | [L*] (AGZ3–AGZ5) |
| B148 (strength) | The return transfer | RH gives it; under `Θ<1` it is equivalent to RH | [L*] (FCT4) |
| B156 (configurations) | Whether the sign at an aperture is a strip | no: deep zeros at ζ's density with positivity on `[−a,a]`, for every `a` | [L*] (SA5) |
| B117 (the three regulators) | Whether the clock, the tower or the heat flow supplies a sign or a gap before the limit | no | [L*] (FFA24–FFA26) |
| B172 (linear, additive) | A linear statistic or additive depth functional monotone under projection | none | [L*] (FFA28, FFA29) |
| A80, A114 | The converse at finite scale; the limit matrices on step packets | equivalences with RH | [L*] (AGZ1, AGZ2, HFP1, HFP2) |
| A82 | The Li ladder as comb forms of tails | the Laguerre tails per degree point tend to the paired Li coefficients, with and without damping | [L*] (HFP5, N6 [S]) |
| A94 | The unshifted index at a fixed window | between the aperture index and index plus nullity; equality off resonances | [L*,S] (HFP4) |
| A102 | The additive gap of the height aspect | `log(π/2)` | [L*] (SA6) |
| A103, A104, A105, A108, A113 | The ladder as one statement; exceptional heights; deep zeros under a rung sign; the first conductor rung; the map under a half-plane | theorems | [L*] (SA1–SA5) |
| A109 | The normalized prime error | the boundary trace without isolation; four sectors | [F]; [L*,S] (N1) |
| A112 | The positivity ceiling of the 70% certificate | cost `≥1+3/π²>13/10` at every bandwidth | [KR] |
| A116 | Hecke characters; ideals as degree points | exact index for every primitive ray class character of every number field, for Dedekind zeta functions and for class characters; Artin characters are A133 | [L*] (AGZ6–AGZ9) |
| A119 | The depth sum | `Σm_ρ·depth≤CT` | [L*] (log §3.17) |
| A121, A123–A131 | Non-attainment and moments; floors; the unit gap; regulators; the tangent datum; feasible sets as positive measures; pure objects; projection; amplification | theorems with their kills | [L*] (FFA1–FFA30, N1–N4) |
| A86 | The near-diagonal cofactor pairs and the filter transfer | unweighted row and filter transfer done; the weighted current is B145 | [F] |
| B154, B155, B143, B151, A68, A55, A72, A73, A76, A71, A83, A56, A90, A98, A99, A97, A100, A101, A96, A91, A84, A37, Q20 | as recorded in review-1011 and in the scoped-obstruction ledger | answered | [L*]/[KR] |

## 2.3 Frankenstein routes

**No assembly closes RH in the native graph.** Every assembly has an open input of RH, AAL or ≥qRH strength, or returns an identity. With `[X]` no assembly reaches the line either: the corpus has no reduction from a half-plane to the line that is not RH itself [L*] (FCT4, J1).

| # | Parts | What the assembly gives | Missing input | Gain |
|---|---|---|---|---|
| F29 | **One scale.** Level of the dressed aggregate; signal exponent; rungs; mollifier depth; window moments; floors | every graded receiver is one number [L*] | a level above the trivial one natively | a proposed estimate is placed on the scale before work starts |
| F30 | **Two estimates.** Family frame over `ℚ(ζ₃)` with corrections; cube identity; cubic residue; budget | `Θ≤σ₀` from a direct and a comparison bound [L*] | A118a–d for `σ₀=7/8`; B174, B175 below | the half-plane route is a single Lean implication; its room is `[13/15,7/8]` |
| F31 | **Half-plane, then line.** `[X]`; level and signal; return transfer; three rungs | under `Θ≤b`: rung `1/(2b−1)`, level `b+½`, return-free windows [L*] | a step from a strip to the line: the transfer is RH under a strip, level one is RH | none: no assembly crosses from `b` to `½` |
| F32 | **Finite scale.** Step packets; ratio windows; robust index; index jumps | RH ⇔ sign of explicit finite matrices; the index is the sum of the nullities at resonant apertures [L*]/[D] | exclusion of a null mode at every aperture (B2, B152) | one exact object in finite rank at each scale |
| F33 | **World I off the scale.** Non-attainment; unit gap; quantum; four sectors; filters; currents | AAL from any of four forms; a complete description of the tangent datum [L*] | B170; or B145 | every form fails on the one-structure models: a proof has to use addition on ℤ |
| F34 | **Verification with sizes.** Verified height; symbol positivity above `T_a`; margin ceiling | a window sign from a height of double-exponential order, if the margin of the verified part has a matching lower bound [D] | A132 | the rung ladder from verification becomes usable beyond the first contact |
| F2 | **One inequality per prime**, with upper side, counts, moments | Σ, Π and count readings are one number per prime on sparse windows [L*] | B130 on one sequence of windows | one target |
| F8 | **Finite-layer world.** Filters, centred currents, half-period deletion | a complete receiver [L*]/[F] | B145 | world I is excluded by one signed current |
| F26 | **Covers.** Exact index for every Hecke character; class characters | the index of one number ring bounds that of ℤ [L*] | the index of a ring | support, not a route |
| F11 | **Construct, then identify.** Index semicontinuity, unit gaps, rigidity | an approximant with a gap gives RH [L*] | B146, B171 | regulators of the corpus are excluded as approximants |
| F6 | **Regulators.** Clock, scattering tower, heat flow | RH ⇔ the energy floor at one fixed height [L*] | B88, B117 | one fixed finite height suffices |

**Closest to the open core: F30 (the only producer, external), F33 (the only target off the scale with a complete receiver), F32.**

### What a contradiction search may assume in world I
`Θ<1`; attained isolated top `β`; `M(x)=O(x^{β′})`, `β′<1` [L*] (C7); `ψ(x)−x=x^βT(log x)+O(x^{β−η})` with `T` a nonzero real trigonometric polynomial, attained on every multiplicative window and at the primes of every late window [L*] (FFA6, FFA7 docstrings); every late window of length `(k+1)π/67` holds a point below every floor [L*] (S10); quantized multiplicities [L*] (FFA17); every locally uniform limit of normalized translates along a phase return vanishes [L*] (FFA19); a nonzero Euler filter of degree twice the number of top quartets accelerates the horocycle rate [D] from N8; with finitely many off-line zeros the packet index is finite and positive [L*] (S16); level-one dressed positivity fails [L*] (L13). No contradiction comes from exact identities alone, from positivity, Euler products over integer norms, integrality or counting alone, from the functional equation with ζ's Gamma factor and count, from a regulator, or from any statement in law [L*].
