# Obstacles summary — status quo

Companion to [route-obstacles.md](route-obstacles.md) (per route), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ) and [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem). Corpus checkpoint: commit `65731ede04` with its working tree (2026-11-11). Fact log: `logs/review-1111-status-quo-facts.md`; identifiers in parentheses refer to log §3, `D1–D8` to log §5.

**Evidence.** `[L*]` Lean statement read at the declaration for this report; `[N]` declaration located through the corpus search index, docstring read; `[F]`, `[KR]` stated by the frontier map and the scoped-obstruction ledger at the checkpoint, Lean not re-read; `[S]` module graded unfinished or unintegrated by the frontier map; `[D]` deduction made here from `[L*]` statements; `[C]` classical mathematics quoted from memory, not in the corpus, to be checked before use; `[A]` assessment; `[P]` proved on a pipeline card at stage 2 (paper proof, Lean formalization in progress), taken as correct here: `docs/drafts/pipeline/2-fully-proven/shortest-generic-twist-family.md` (log §3.21); `[X]` one external source cached in the repository, outside the native import graph and not checked here: a zero-free half-plane `Re s>7/8` for ζ, Dirichlet `L`-functions and Hecke `L`-functions over `ℚ(√−3)`. The frontier map states that the native graph has no unconditional `7/8` theorem [F]. Sections 2.3–2.14, 3 and 4 are interpretation and ideation: every untagged statement there is a proposal, not a result.

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
| exponent of a twist family: a generic mean square of the Möbius sums of length `Z` over the principal `n`-th-power twists of norm up to `Z^θ` | `θ` | `Θ≤½+(1−1/n)θ/2`, and conversely; the least `θ` is `(n/(n−1))(2Θ−1)` | [P] (SG1) |
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
| Euler product over the rational primes, each once; multiplicative coefficients `0≤a(n)≤C_εn^ε`; `0≤Λ′≤2Λ`; meromorphy on ℂ; polynomial bounds for `F` and `1/F` right of `Θ` (given `Θ<1`) | `ζ(s)/(ζ(s+1−ρ₀)ζ(s+1−ρ̄₀))` with finitely many Euler factors removed: exactly the pair `ρ₀,ρ̄₀` right of `Θ`; a pole in the left strip | the abscissa law at the frontier of ζ | M1 |
| nonnegative prime and integer densities, integer count `N(x)−ρx−C→0` (continuous system) | a rational zeta function with one off-line pair, tending to `1` on vertical lines | AAL; recurrence of a zero | [N] (X1, X2) |
| the Riemann functional equation, Gamma factor, residue one, order `≤1`, count within one | all zeros simple, off the line, approaching it | Landing | C6 |
| Euler product and a functional equation of degree two on the integers, unbounded coefficients | `ξ(s+a)ξ(s−a)`: every critical zero `ρ` gives zeros `ρ±a` off the line | ZAL; strip self-improvement | [L*] (log §3.18); [KR] |
| both structures up to an integrable defect, positive continuous prime measure | `ζ(s)exp(ε/(s+1)²)` | nothing: the zeros are those of ζ | W1 |
| the Riemann functional equation with an `L²` defect on a countable system; or count `n+o(log n)`; or the axioms of the Selberg class in degree one | the rational primes alone; a primitive Dirichlet `L`-function with an imaginary shift | — | C13; [KR] (X3); [L*] (log §3.18) |
| Euler product over geodesic norms and a functional equation, order two | Selberg zeta functions of surfaces with small eigenvalues: finitely many real zeros in `(½,1)` | B13 | [C] |

Consequences [D] (D8). A mechanism that reads the Euler product through the zero configuration has floor `½`: the property "the right zeros are the divisor of an Euler product over natural norms" holds for every finite datum [L*] (M2); a producer has to use the Euler product on the function. What the models realize is analytic, positive, or multiplicative with integer norms or with the rational primes and bounded coefficients. What no model of the corpus realizes is the unit multiplicity of every integer and the exact functional equation, and each of the two alone identifies ζ. Both are statements about addition on ℤ. The atoms have no model among Dirichlet series over the integers with the Riemann functional equation; outside that class B13 fails in a classical family.

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
| positive form: a generic mean square of the Möbius sums of length `Z` over the twists of norm up to `Z^θ`, the target occurring among its twists with multiplicity `P^{1/n}` | the half-plane `½+(1−1/n)θ/2`; for the sextic symbol `11/12` at `θ=1`, `7/8` at `9/10`, `13/15` at `22/25`, `5/6` at `4/5`; `½` at `θ=0` for every order (M3) |

The family law is a level of the scale [P] (SG1–SG3). For smoothed Möbius sums twisted by residue symbols of order `n≥2`, the principal `n`-th-power subfamily has a generic mean square exactly for `θ≥(n/(n−1))(2Θ−1)`; the minimum is attained, and it is `0` iff RH. For the full Jacobi family (`n=2`) a generic mean square at some `θ>0` gives the abscissa `≤min(1,½+θ/4)` for ζ and for the quadratic character of every odd squarefree modulus, and the mean square is generic at every `θ` iff RH and GRH for all odd fundamental quadratic twists hold. With bounded positive squarefree weights in place of `μ` no family is generic below `θ=n/(n−1)`.

In the single variable `θ=(2n/(n−1))(σ₀−½)` the class of reflection, slots and large sieves has sharp floors [L*] (TB1–TB8):

| Mechanism | Floor in `θ` | Half-plane at `n=6` |
|---|---|---|
| reflected optimal sextic multiplicative large sieve | `10/9` | `26/27` |
| additive planar sieve without slots; the dual diagonal | `1` | `11/12`; at order `n`: `1−1/(2n)` |
| two or more row variables, `n≥3` | `n/(n−1)` | `1` |
| conductor corners `(κ,n)=(2,6)`, `(3,4)`, `(4,3)` | `14/15`, `22/21`, `11/9` | `8/9` at `(2,6)` |
| the published geometry in its binding bin | `9/10`; no geometry reaches `9/10−3/5000` with the published row count | `7/8` |
| the floor bin summed trivially, every order, both Gram regimes | `(5n−8)/(5(n−1))`: `22/25`, `4/5`, `7/10` at `n=6,4,3` | `13/15` |
| rows of nonnegative rescaled length, without the dual-length term | `(n−2)/(n−1)`: `4/5`, `½`, `0` at `n=6,3,2` | `5/6` |
| reflected rows evaluated through the order-`n` twists | `(n/(n−1))(2β−1)`: the zero itself | circular |

Deductions [D] (D4, log §3.21). The room inside the probe is `[13/15,7/8]`, in the twist exponent `[22/25,9/10]`. A generic mean square of a family that contains its principal twists is not an input below its half-plane: it is that half-plane. The floors name what a producer of this class lacks: a row count in the binding bin between `9/10` and `22/25` (B174), a bound of the floor bin below trivial summation between `22/25` and `4/5` (B175), and below `(n−2)/(n−1)` rows that reflection does not supply. The free floor is zero only at order two, where the power of a Gauss sum carries the parity of the character and not the Möbius sign [L*] (F3): the class reaches the line at no order with a power source. The conversion from law to point is the multiplicity with which the target occurs among its twists. Natively open: removal of the cube sum in the source comparison, the properties of the corrections `H_η`, and both savings uniformly in the character [F].

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
| The Euler product read through the zero configuration; the Euler product over the rational primes with bounded nonnegative coefficients, meromorphy and polynomial growth, without the functional equation | floor `½`; a one-off pair above the frontier of ζ | [L*] (M1, M2) |
| One-sided floors on windows of one length; windows below the logarithmic radius | models | [L*] |
| A regulator as a source of a sign, a unit gap or an index bound before the limit | below the limit, or the count of the limit | [L*] |
| A certificate other than `Λ`; a pure object with ζ's Gamma factor as a certificate | converge to `Λ`; no Dirichlet series | [L*] |
| Linear statistics and additive depth functionals as monotone quantities under projection | excluded | [L*] |
| Replication of a top zero by a normal family of translates | zero limits | [L*] |
| Amplification over the order of a window moment as an independent source | it is a sup bound | [L*] |
| A path of squares as a transport of the sign | RH at every parameter | [L*] |
| A Gauss-sum probe of the published architecture below `13/15`; other orders, more row variables, other conductors; reflected rows through the same twists; multiplicative in place of additive large sieves on the reflected rows | budget; in the twist exponent the floors `22/25`, `1`, `n/(n−1)`, `10/9` | [L*] (FCT11–FCT17, TB1–TB8) |
| A generic mean square over a twist family as an input below its half-plane; positive weights in place of `μ` | on the principal twists it is the half-plane `½+(1−1/n)θ/2`; positive weights are not generic below `n/(n−1)` | [P] (SG1, SG3) |
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
| A133 | Artin characters of non-abelian extensions: the index law per character; first case the degree-two character of the splitting field of `X³−2`, a Hecke `L`-function of a cubic character over `ℚ(√−3)` (unverified) | ACS, HF | the index law for ray class characters (AGZ6–AGZ8); the Dedekind index of the non-abelian ring of the cube roots of two (M4); `hasSum_zeros_explicit` (AGZ14) |
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
| B18 | A construction of feasible weights at every aperture; every system feasible at a large aperture is within `ε` of `Λ` at each fixed `n` [L*] (FFA21) | RH | RW |
| B2, B4, B5 | Bounded oscillation of `Ψ` to contact (no null mode at any aperture); outer predictors and Schur bands; kick admission | RH | RW, GWZ, WTZ |
| B6, B8, B101 | Full-space sign at every critical multiple; head thresholds; polar payment at every ratio | RH | HF, SRT, AIP |
| B104 | Polar orthogonality at the critical curve: whether a critical half-line ground state at finite `W` can be orthogonal to the polar source | method | HF, SRT, AIP, ACS, SC |
| B123 | Correlated arithmetic pairings dominating the depleted kernel | method | HF |
| B156 | Arithmetic cluster exclusion on a rung for ζ | method | SA, RW |
| B9–B11 | No zero mode; top coprime stratum; exact SOS on a two-prime lattice | RH | HF, SC, ACS |
| B12, B14, B23 | Index ceiling uniform in resolution; any interior width value; `N_d` bounded | ≥qRH | CHMD, LA |
| B15 | Past Vinogradov–Korobov | sub | every route |
| B16, B17, B3 | Decay law of the margin; signed ground states past `log ρ`; variation of `r` free of `1/μ` | sub / method | CHT, RW |
| B176 | The cost of a window: whether RH through `exp(C·e^{2a})` gives the sign on `[−a,a]`; a lower bound for the margin of the verified part (§2.4) | sub / method | RW, SRT, TH, LI, HCF |
| B179 | A symplectic structure in which the index of the comb is a Maslov index of the aperture path (§2.8) | producer | RW, HF, ACS |
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
| B175 | A bound for the nonprincipal rows of a twist family with cancellation across the rows, not passing through the twists: a twist exponent below the floor bin `(5n−8)/(5(n−1))`, a boundary below `13/15` for the sextic symbol (§2.5) | producer; of the strength of its half-plane [P] | JAS, MC |
| B180 | The reflection of the completed theta row without Eisenstein series (§2.11) | method | JAS, MC |
| B181 | The comparison estimate of the two-estimate implication at `7/8`: removal of the cube indices, the corrections `H_η`, uniformity in the character (§3) | producer lemma | JAS, MC, S3 |
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
| B182 | The least remainder of the integer count of a discrete system with integer norms that has a zero right of the line which ζ lacks: is there one with `N(x)=Ax+O(x^β)`, `β<1`; with `β<½` (§4) | method (a construction); the negative side is of GRH type | WL, MC |
| B89, B112, B128 | A bounded aligned return at each right zero; the functional equation into vertical transport; replication by a mechanism other than normal families | sub | BAG, ZCG, EFT |
| B68, B71 | Reflection Krein positivity, flux, dispersion; universal decay and the horizon rates | RH | PM |
| B72–B76 | Cutoff-uniform target mass; the candidate zero-parameter conditions; FE-pair reality | RH | BAG, candidates, ZCG |
| B80, B81 | FE twins in the full class; candidate landings | sub; producer | SEL; candidates |
| B86 | Endpoint character positivity at unbounded rank | RH | ECP, ACS |
| B87 | A nonnegative count on the rays `Γ_1+Γ_p`, defined without `Q` | RH | ACS, HF, PM |
| B88 | The sign of the comb finite part | RH | HF, ACS, HAT, AGZ |
| B114, B117 | A realization of the partner involution outside the excluded classes; a regulator with a sign, a gap or an index bound before the limit | producer | PM |
| B147 | Shimura nonvanishing at `ρ/4+¼` for one Hecke eigenform | indep. | PM |
| B178 | A relaxation lower bound for a horizon with a cusp: a resonance-free strip of positive width for `ξ(2s−1)/ξ(2s)` from a principle that fails under deformation of the group (§2.7) | ≥qRH (producer) | PM |
| B149, B169 | Bézout for the comb pairing from a property of the object; a group with a doubling on which the defect is a canonical height | RH (producer) | ACS, HF, AGZ |
| B172 | A nonlinear functional of the zero configuration that decreases under projection to the line and is computed from the primes | producer | ZCG, HF |
| — | ZAL | ≥qRH | whole programme |

### Settled method questions
| # | Question | Answer | Evidence |
|---|---|---|---|
| B153 | A bounded or almost periodic constituent of ξ with a zero | none, at any abscissa in the bounded class and on any strip in the Wiener class; no purity premise; no `ℓ^p` transport | [L*] (CTZ1–CTZ4) |
| B158 (budget form) | The boundary of the order-`n` probe; whether its infimum is `½` | room `[13/15,7/8]` for the cubic design; other orders, more row variables and other conductors are worse; the low side is `≥1−1/n`; reflected rows through the twists are circular | [L*] (FCT11–FCT17) |
| B177 | The least exponent `θ` of a twist family with a generic mean square of the Möbius sums | on the principal `n`-th-power twists it is `(n/(n−1))(2Θ−1)`, attained, and zero iff RH: a level of the scale; for the Jacobi family the infimum is zero iff RH and GRH for the quadratic twists; positive weights are not generic below `n/(n−1)`; reflection, slots and large sieves have the floors `10/9`, `1`, `9/10`, `(5n−8)/(5(n−1))`, `(n−2)/(n−1)` | [P] (SG1–SG3); [L*] (TB1–TB8) |
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
| B154, B155, B143, B151, A68, A55, A72, A73, A76, A71, A83, A56, A90, A98, A99, A97, A100, A101, A96, A91, A84, A37, Q20 | the exceptional square; the edge alternative at level one; the resolution of the minimal face; landing with ζ's Gamma factor; rigidity of prime measures; counts, upper side, absolute forms and moments on logarithmic windows; density-matched models; prime two-bumps from a verified height; flow criterion; feasible weights; the tower; multipoles; trivial aperture; first selective window; abelian rings; greedy compositions; growing resonators; paid contacts | answered, as recorded in the scoped-obstruction ledger and in the declarations of log §3 | [L*]/[KR] |

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

## Validation tests for 2.4–2.8, 3 and 4

| Test | Requirement |
|---|---|
| T1 | Implied by RH and not implying quasi-RH; for §3 also not implying AAL; or a method question implied by nothing about ζ's zeros |
| T2 | Answered by proving or refuting a stated inequality, identity or implication |
| T3 | A named consequence for either answer |
| T4 | Not decided by a finite rung |
| T5 | False on a corpus model, or calibrated on the models |
| T6 | Names an input not refuted in Lean |
| T7 | Moves a wall; not a shape answered in Lean |
| T8 | Not a named long-standing problem in disguise; a first step in corpus objects with one named obstacle |

**No statement about the zeros of ζ below RH, quasi-RH and AAL passes all tests as a door.** Reason, in theorems: a graded statement is a level of the one scale (§1.2), and the first level above the sizes is a classical problem in each aspect; a statement off the scale is of one of four kinds, each with its kill (§1.5); the structural questions that had a first step are answered (§2.2, settled). The questions below are method and producer questions; each states its failed tests. Every one was checked against the corpus by sentence queries (log §3.18, §3.20).

## 2.4 Breakthrough question below RH and quasi-RH: is the cost of a window double exponential?

**Position.** Each window is a finite-height statement, and the corpus pays for it with a height whose triple logarithm is `c·a^{4/3}` [F]. The proved sign reaches the half-width `181/500`, just past the first contact [L*]. With this cost no verified height gives a window containing the contacts of `2` and `3`, and every rung of class C8 (windows, prime two-bumps, Li coefficients, theta ranks, Jensen degrees) inherits it.

**Question (B176).** *Is there an absolute `C` such that RH through the height `exp(C·e^{2a})` gives Weil's sign on `[−a,a]`?*

**What is proved.** The transfer at triple-exponential cost [L*] (J3). The form at aperture `a` is diagonal in frequency, and its symbol is nonnegative above `T_a=exp(C+2ψ₁(e^{2a}))` for every test: sizes pay all high frequencies exactly, with no error term [D] (D3). The best margin of a window is at most `K exp(11a/2−πe^{2(a−2)})` [KR]. RH ⇔ the ground energy tends to `0` with the aperture [N]. Under local boundedness of the off-line copies the form has a floor `−K(M,a)∫|u|²` [N].

**What either answer gives.**
| Answer | Effect |
|---|---|
| Yes | every certified height is a window of half-width about `½log log H`; the frontier of unconditional Weil positivity leaves the first contact by finite computation (A1, A135); the rungs of class C8 get a usable rate; the ground energy has a floor `−ε(H,a)` with explicit `ε` |
| No: the margin of the verified part is below `exp(−Ce^{2a})` for every `C` | the verification ladder does not leave the first contacts; a single window beyond them is an input of the strength of its own sign; the routes of class C8 keep finite rungs as illustrations only |

**First step and obstacle.** Above the frequency `≈2πe^{2a}` the verified ordinates are denser than the Nyquist rate `a/π` of tests supported in `[−a,a]` [C], and a lower sampling inequality there gives coercivity of the verified part; above `T_a` the sizes give it. Named obstacle: the band below `2πe^{2a}`, where the ordinates undersample and the margin is small by the ceiling above; the corpus has upper sampling bounds and the ceiling, and no matching lower bound (log §3.18).

**Tests.** T1: implied by RH; implies no width. T2, T3: pass. T4: the question is a rate, uniform in `a`; each instance is finite. T5: calibrated on pure lattices, where the boundary `a≤L/2` is exact [KR], and on the dominated box, which fails at `log log t+log(π/2)+η`: no transfer from sizes alone passes `log log H`. T6: pass. T7: moves Σ82, Σ171. T8: not a named problem.

**Limit.** It produces no sign beyond verified heights. A second native question below RH with a first step is open: polar orthogonality at the critical curve (B104): at finite `R_polar=W`, can every critical half-line ground state be orthogonal to the polar source [L*] (C3)?

## 2.5 Breakthrough question for the search for a producer: is there cancellation across the rows of a twist family?

**Position.** The search has closed classes. Off the scale: homogeneous floors, unit gaps, certificates, amplification, symmetrization (linear and additive), replication by normal families, each with a kill (§1.5). On the scale: sizes (rung one), mean values (in law), regulators and paths (count of the limit, or RH at every parameter). A mechanism that reads the Euler product through the zeros has floor `½` [L*] (M2). One producer class is not closed: a completed sum with a direct bound and a comparison with its signal (§1.6). Its conversion from a law to a point is in Lean: the target occurs among its own twists, because the `n`-th power residue symbol of `a^n` is trivial, so a mean square over the family bounds the target [L*] (M3).

**The law of a family is the scale (B177) [P].** The least exponent `θ` at which the mean square of the Möbius sums of length `Z` over the principal `n`-th-power twists of norm up to `Z^θ` is generic is `(n/(n−1))(2Θ−1)`: it is attained, and it is zero iff RH (SG1). For the full Jacobi family a generic mean square at `θ` bounds the abscissa of ζ and of every quadratic twist of odd squarefree modulus by `½+θ/4`, and the infimal exponent is zero iff RH and GRH for those twists hold (SG2). Genericity is cancellation: with positive squarefree weights no family is generic below `n/(n−1)` (SG3). A mean square over a family that contains its principal twists is therefore a receiver, of the strength of the half-plane `½+(1−1/n)θ/2`.

**The class of the published design has floors [L*] (TB1–TB8, FCT11–FCT17).** In the twist exponent: `1` without slots (the dual diagonal), `10/9` with the optimal sextic multiplicative large sieve on the reflected rows, `n/(n−1)` with two or more row variables, `9/10` for the published geometry in its binding bin, `(5n−8)/(5(n−1))` for the floor bin summed trivially (`22/25` for the sextic symbol), `(n−2)/(n−1)` for rows of nonnegative rescaled length without the dual-length term (`4/5` for the sextic symbol). Reflected rows evaluated through the order-`n` twists return the zero. The sign needs an odd order above two (F3), and the free floor vanishes at order two only.

**Question (B175).** *Is there a bound for the nonprincipal rows of a twist family with cancellation across the rows: an estimate of the floor bin below trivial summation that does not pass through the twists and does not bound the principal rows?* Each saving lowers the twist exponent from `(5n−8)/(5(n−1))` toward `(n−2)/(n−1)`: for the sextic symbol the boundary moves from `13/15` toward `5/6`.

**What either answer gives.**
| Answer | Effect |
|---|---|
| a saving across the rows of the floor bin | a boundary below `13/15`: the first estimate of a source programme beyond the published design; with the row count of B174 the room `[13/15,7/8]` is no floor of the route |
| no saving: a family of rows on which trivial summation of the floor bin is sharp | half-planes through reflection, slots and large sieves end at `13/15` by a theorem about exponents and one model; RH needs a statement off the scale or a source outside the class |
| below `(n−2)/(n−1)` in either case | not reached by the class at any order with a power source [D]: rows that reflection does not supply, or a source at order two, are separate inputs |

**First step and obstacle.** The floor bin of the geometry `(2/5,2/5,1/5)`, where with the row count `R=1−δ` every bin has the exponent `(q−δ/2)/5` in the prime amplitude `q` [L*] (TB6), written as one bilinear sum in the row index and the Möbius variable. Named obstacle: below `θ=1` a mean square over the family is outside the range of a large sieve (TB2); the corpus has the planar and the Eisenstein large sieve and no estimate with cancellation across a family, and by SG1 every such estimate that includes the principal twists is of the strength of its half-plane.

**Tests.** T1: fails as a statement below quasi-RH: a producer, of the strength of the half-plane it gives [P]; it is implied by nothing about ζ's zeros only on the nonprincipal rows. T2–T4: pass. T5: calibrated on the published vertex (`θ=9/10`), on the floor geometry, and on positive weights, which are not generic below `n/(n−1)` [P]. T6: pass: the floors hold for trivial summation; cancellation across rows is not refuted in Lean. T7: moves Π163 below its floor bin. T8: cancellation in a family of twisted Möbius sums below the large-sieve range is a problem of classical type for the twist family [A].

**The gate.** Whether the corpus has a producer at all is not this question but the native status of the two estimates at `7/8` (§3).

## 2.6 If positivity, Weil positivity and spectral methods are excluded

"Spectral" is read as spectral theory of operators in every form, automorphic spectral theory included; "positivity" includes nonnegativity of forms, kernels, counts, coefficients and averaging measures. Kept: Fourier analysis, mean values used as bounds, exponential sums, Poisson summation, absolute convergence, continuation, power sums, integrality, recurrence, the argument principle.

**What survives [L*].**
- *Receivers.* RH ⇔ `|2Re S(log p)|≤K` on logarithmic windows (S6); ordinate injectivity [N]; the exponent of the signal (FCT2). For AAL: two-sided non-attainment, the unit gap by the argument principle, the quantum of a multiplicity (FFA4–FFA7, FFA5, FFA17).
- *Conversions.* Recurrence against density and prime contraction (no bounded constituent); the jump law; half-period deletion; the Vandermonde bound on windows (FFA30).
- *Identities.* The Jacobi-sum sign law; Poisson summation in a row (one term) (FCT9, FCT10).
- *Settled.* No bounded or Wiener constituent with a zero; the budget of the Gauss-sum probe; archimedean coefficient gaps do not separate the ordinates [KR].

`[X]` under the constraint [A]: its large sieves are bounds and its identity is algebraic; the reflection of its completed theta row is a functional equation known through Eisenstein series on a cover [C]. The strict reading removes it.

**An observation that frees one tool [D].** `Σλ(n)Λ(n)n^{−s}=ζ′/ζ(s)−2ζ′/ζ(2s)` has in `Re s>½` the pole at `1` and poles exactly at the zeros of ζ. So the top layer of `Λ` and of its Liouville twist coincide, and AAL is invariant under the twist. The parity blindness of bilinear statements [L*] (W3) is therefore no obstruction to AAL, while it is one to every sign. What a bilinear proof of AAL has to use, and what every integer-norm model lacks, is Poisson summation in the cofactor variables with remainders of size `O(1)`.

**Question (B145).** *Does the prime-weighted centred type-II current at a growing isolated mode cancel below the recovered residue?* Proved: under ¬AAL filters recover the top residues; the growing-order Gaussian current reduces to centred type-II cofactors `≤3t⁷¹` with a filtered error `≤2h^d exp(−at/8)`; separated complete unweighted lattice pairs decay faster than every power; the unweighted near-diagonal row is summable [F]. Open: the cofactor sum with the prime weights, keeping both continuum corrections.

| Answer | Effect |
|---|---|
| Yes | AAL with no sign of a form and no operator; then RH ⇔ ZAL |
| No: a lower bound for the current of the size of the residue | the Vaughan–Gaussian architecture does not exclude a finite layer; world I needs an input outside exponential sums |

**Tests.** T1: fails as a question below AAL; it is of AAL strength [D]. T2, T3: pass. T5: it has to fail for Euler products over natural norms with a finite layer; it does where the proof uses Poisson summation with `O(1)` remainders [D]. T7: moves Π149. T8: the weighted sum is a Type II sum in the dark range [A]; the first step exists (the unweighted row), the obstacle is the prime weight.

**Limit.** Under the constraint the step from AAL to RH is ZAL, a half-plane statement at every depth, and the corpus has no sign-free non-spectral source for it.

## 2.7 If RH is a physical phenomenon in AdS with a modular horizon

**What is proved [L*]/[N].** The resonances of the modular horizon are the zeros of `ξ(2s)`. RH ⇔ every pulse rings down at the quarter rate ⇔ positivity of the reflection Krein forms ⇔ one cavity energy decays at `y^{¾−ε}`. The supremum of the universal horocycle exponents is `1−Θ/2`; with a nonzero Euler polynomial filter `P(y d/dy)` it is `1−Θ∞/2`, and no filter passes `3/4`; ZAL ⇔ filtered rates approach `3/4`; AAL ⇔ no filter accelerates past the unfiltered optimum (N8 [S]). Every regulator of the corpus has the count of its limit (FFA24–FFA26). At every fixed scattering height the energy floor is RH (H1). The stratum of exceptional eigenvalues of congruence quotients is empty below `3/16` (J7).

**Readings [D] (D7).**
- *World I is ordinary ringdown, and it is removable.* A finite top layer is a finite set of least-damped modes; a differential filter of degree twice their number removes them from every pulse. AAL says that no finite filter helps.
- *World II is a tail.* Modes approach a rate above the symmetric one and no filter reaches `3/4`.
- *RH is a saturated bound.* The symmetry of the resonances bounds the relaxation exponent by `3/4`; RH says the bound is attained. What physics has to supply is a lower bound for the damping of the slowest mode, with no margin.

**Question (B178).** *Is there a relaxation lower bound for a horizon with a cusp: a principle that gives the scattering matrix `ξ(2s−1)/ξ(2s)` a resonance-free strip of positive width?* A strip of width `β` is the half-plane `Θ≤1−2β` [D]. For open hyperbolic systems with a fractal trapped set, strips beyond the pressure bound are theorems, proved by an uncertainty principle and not by positivity [C]. The modular horizon is not such a system: its trapped set is everything except the excursions into one cusp [C].

**What the corpus says about the candidates.** A Hölder dynamical realization of ζ gives a zero-free strip, and the oscillation estimate fails on additive realizations of the prime lengths [N] (ArithmeticResonanceTheory). Graph horizons with commuting Hecke operators and slow resonances exist [KR]. Under deformation of the group, cusp forms are expected to dissolve into resonances near the unitary axis [C]: a principle that holds for every cusped surface of the same area is false. So the principle has to use the arithmetic of the group, and Hecke symmetry alone is not enough.

| Answer | Effect |
|---|---|
| A gap of any width | the first native producer: a half-plane; the edge world is excluded |
| A cusped model with the same local dynamics and resonances approaching the axis, in Lean | the gap is not a property of the horizon; the physical reading supplies receivers and no source |

**Tests.** T1: fails; a producer of ≥qRH strength. T2: passes for the calibration; the principle is a research direction. T5: has to fail on non-arithmetic cusped surfaces and on graph horizons with slow resonances. T8: no first step beyond the two calibrations.

**Limit.** A gap is a half-plane; equal damping is the maximal gap and is not reached by a principle with a margin. The regulator question B117 stands in sharpened form: a regulator with a sign, a unit gap or an index bound before the limit; the clock, the tower and the heat flow have none.

## 2.8 If RH is a problem of topology or geometry

**What is proved [L*].** The pairing of the degree points has a Hodge index theorem equivalent to RH, with exact index the number of right zeros, for ζ and for every Hecke `L`-function of every number field; discriminants and conductors enter as the density of the comb, and below the first contact a large discriminant gives the inequality with a margin (AGZ6–AGZ9). Every datum of the pairing is forced; every path through the square of ℤ is RH at each parameter (AGZ3–AGZ5). At finite scale the inequality is the sign of explicit finite matrices (AGZ1). The sections of the square count linearly: volume over the gluing index, no quadratic term (AGZ10). The index is nondecreasing in the aperture and jumps by the nullity at resonant apertures [F].

**Readings [D].**
- *The aperture is a time.* The restricted forms are a path of quadratic forms; the index counts the resonant apertures with their nullities, as a Morse index counts conjugate points; RH ⇔ the path has no conjugate point (D2).
- *The square is one-dimensional for counting.* Its sections count like points of a lattice of rank one per graph; the quadratic count that a height needs is absent from the object (AGZ10).
- *Spec ℤ is not a member of a family.* Constant, contacts, tree lengths, prices, mass: every deformation is forced or returns RH (D5).

**Question (B179).** *Is the index of the comb a Maslov index: is there a symplectic space and a path of Lagrangian subspaces, defined from the places without the zeros, whose crossings with a fixed Lagrangian are the resonant apertures with their nullities?* A Maslov index is invariant under homotopy with fixed ends [C]. The corpus has the scalar flow of the chain (`L`, `q`, `Ψ`, with `ΔL=ΔΨ−∫sinh 2L`) [F], the jump law of the index, and the unit-gap receivers; it has no symplectic structure for the family and no declaration of this kind (log §3.18).

| Answer | Effect |
|---|---|
| Yes, and the index is determined by the two ends of the path | a topological computation of the number of right zeros: a producer of unit-gap kind |
| Yes, and the far end carries the zeros | the topological route is the boundedness of `Ψ` to contact (B2) in another language: a kill of the reading |
| No such structure | the index of the comb is not a Morse index of a variational problem: a structural negative for every homotopy argument |

**Tests.** T1: fails; a producer of RH strength. T2: passes for the existence of the structure. T5: for the Liouville twist the index is positive just above the trivial aperture; a structure that does not see this is wrong. T8: not a named problem; first step: the Hamiltonian form of the canonical system of the window tower, obstacle: the end at infinite aperture.

**Carried questions.** A count quadratic in the divisor with the comb defect as its Tate limit (B87, B169): on a hyperelliptic curve the defect of an integral class is such a count [L*] (C11); over ℤ the object's own count is linear. A correspondence on the orientation cover with bounded local indices (B106): the signed localization `Σ_p index=N+1−count` is a theorem [L*] (log §3.17).

**Limit.** No geometric question below RH is open that the corpus has not answered with an identity or with an equivalence.

## 2.9 New field for RH: arithmetic of the unit multiplicity

**Does RH need a new field?** Not a further language for receivers. Five fields exist as programmes and end at theorems:

| Field | Programme | Where it ends |
|---|---|---|
| reciprocity sources | FCT, MMD | one implication with two estimates; budget room `[13/15,7/8]`; the law of a twist family is a level of the scale [P]; floors of reflection and large sieves in the twist exponent |
| gap theory of finite strata | FFA, ELT | receivers off the scale; every finite datum realized under one structure; the weighted current open |
| conversion theory | CTZ, IRP | bounded and Wiener classes closed |
| relaxation theory of horizons | HAT, BHR, AHMH, FFA | regulators with the count of their limit; exponents `1−Θ/2`, `1−Θ∞/2` |
| Lefschetz paths and heights | AGZ, HFP | paths transport no sign; linear count of sections |

134 programme folders cover the mechanism classes that can be named. What the corpus does not contain is a statement off the scale that fails on every model of §1.3. The two properties of ζ that no model has, unit multiplicity of the integers and the exact functional equation, appear in the corpus only as rigidity theorems: they identify ζ and bound nothing. A field is justified as the theory that turns them into inequalities.

| Aspect | Content |
|---|---|
| What it is about | Inequalities that hold because every integer occurs exactly once: Poisson summation on ℤ and exact Type I sums, used jointly with the Euler product, and their action on tangent data, certificates and indices |
| What it is like | An effective form of the rigidity theorems, in which the conclusion is not "the system is ζ" but an inequality that degrades with a defect. Its test bench is the ladder of models: continuous systems with regular integers, natural norms, rational primes with repetition |
| Established | Rigidity in four forms: an `L²` functional-equation defect; count `n+o(log n)`; integrable defects at unit density; the degree-one classification of the Selberg class [L*]/[KR]/[N]. Lower bounds for the defect from a displacement of primes or integers [N]. Every finite datum under one structure [L*]. The receivers off the scale [L*]. Poisson summation in cofactor lattices in the currents of ELT [F] |
| Criteria | U1 it fails on each model of §1.3 and names the line of the proof that uses unit multiplicity. U2 it is off the scale, or holds at every level of the scale. U3 it is pointwise in the zeros. U4 it degrades continuously with a defect and is false at the defect of the nearest model. U5 for AAL it may be invariant under the Liouville twist; for a sign it must not be. U6 it is not a linear identity of the explicit formula: those are tautologies on a tangent datum. U7 for curves it reproduces the count law |
| Questions it must answer | What is the defect of an Euler product over natural norms with a prescribed finite layer, and is it bounded below by the datum? Does a finite datum survive Poisson summation in two variables (B145)? Is there an integer produced by Poisson summation whose archimedean size is below one exactly when a datum is absent? How fast do feasible systems approach `Λ`, as an inequality on the last visible contact? |
| Tools it develops | Poisson and Voronoi summation on tangent data; Vaughan-type identities with exact Type I terms; a defect calculus; quantile discretization as a generator of models; the scale as measuring instrument |
| Objects | Systems, defects, tangent data, certificates, quanta |
| Language | unit multiplicity, defect, datum, attainment, quantum, off the scale |
| Mechanisms | Built on: the rigidity theorems, the models, the receivers, the currents. To discover: an inequality in which a defect and a finite datum cannot both vanish |

**Main conjecture.** A multiplicative system over natural norms with unit multiplicity has no finite datum (AAL); in strong form, no zero off the line. **Milestones.** M1 the defect of the finite-layer models. M2 the tangent data of `μ`, `λ` and of additive twists (A137). M3 the weighted current for one quartet. M4 B145. M5 an inequality of unit-gap kind.

**Status [A].** The field has rigidity theorems and models and no inequality. If its first inequality does not exist, the statement of §1.12 stands: natively every route is a receiver.

## 2.10 New field for AAL: additive arithmetic of finite layers

**Does AAL need a new field?** The two halves exist: the receivers and the tangent datum (FFA), the instruments (ELT). No programme joins them. The junction is narrower than §2.9: it concerns a finite datum only.

| Aspect | Content |
|---|---|
| What it is about | What addition on ℤ does to a finite top layer: the datum of `Λ`, `μ`, `λ`; its image under bilinear decompositions and under Poisson summation in the cofactors; the signed currents in which it appears |
| What it is like | A theory of one finite-dimensional object, the trigonometric polynomial `T` of world I, under operations that the one-structure models do not have. It is sign-free and parity-even |
| Established | Four sectors of the normalized trace; attainment on every window and at the primes; quantized multiplicities; orders of `1/ζ` and `ζ(2s)/ζ(s)` at a top zero; zero limits of normalized translates; filters, growing-order reduction, the unweighted near-diagonal row [L*]/[F] |
| Criteria | Acts at every depth with constants that do not degenerate as the depth tends to zero. Uses a finite datum. Fails on Euler products over natural norms and over rational primes with repetition, at the step that uses a remainder `O(1)`. May be invariant under the Liouville twist. Is not a statement in law |
| Questions it must answer | B145. Is a top layer of one quartet excluded (A47)? Does the leading coefficient `1/ζ′(ρ)` of `μ` at a top zero obey a bound from exact Type I sums? Is world I with a tail empty (B141)? Does the datum of `Λ` determine a relation among the data of twisted multiplicative functions? |
| Tools it develops | Gaussian filters at growing order; cofactor lattices; exact continuum corrections; Bohr means and quanta; the models as counterexamples to every step that does not use addition |
| Objects | Data, layers, currents, cofactors, quanta, filters |
| Language | datum, attainment, current, cofactor, quantum, sector |
| Mechanisms | Built on: FFA, ELT. To discover: one bilinear identity in which the datum enters with a constraint |

**Main conjecture.** AAL. **Milestones.** M1 the data of `μ` and `λ` (A137). M2 the one-quartet world. M3 the weighted near-diagonal row. M4 B145. M5 B141.

## 2.11 New field for RH without positivity: elementary reciprocity analysis

**Does a positivity-free, non-spectral RH need a new field?** For AAL the field of §2.10 is sign-free and non-spectral as it stands. For the step from AAL to the line the corpus has one source class, and its only instance rests on one spectral input: the reflection of the completed theta row.

| Aspect | Content |
|---|---|
| What it is about | Summation formulas for Gauss sums of order at least three proved by Poisson summation and reciprocity alone, and the half-planes they give through the two-estimate frame |
| What it is like | A budget calculus first, estimates second: every proposed formula is placed on the scale before work starts |
| Established | The Jacobi-sum sign law at every order above two; Poisson summation in a row as one term; a common prime of two columns as a Jacobi sum of modulus one off the zero frequency; the planar and Eisenstein large sieves; the frame; the budget [L*]/[F] |
| Criteria | No operator and no sign of a form. The direct bound is a large sieve used as a bound. The boundary is a theorem about exponents. It fails for even order, where the sign is the parity of the character |
| Questions it must answer | Is the reflection of the completed theta row provable without Eisenstein series (B180)? What boundary does the frame give with the non-reflected side alone? What is the least twist exponent `θ` reachable without spectral input, against the floors of the class with the reflection (§1.6)? |
| Tools it develops | Reciprocity in cyclotomic rings; large sieves over rings of integers with residue symbols; the budget calculus |
| Objects | Rows, columns, twists, slots, boundaries |
| Language | source, row, column, slot, boundary, floor bin |
| Mechanisms | Built on: FCT, MMD. To discover: an elementary reflection, or a proof that the non-spectral boundary is strictly above the spectral one |

**Main conjecture [A].** Without spectral input the two-estimate frame has a boundary strictly above the one of the published design. **Milestones.** M1 the budget without the reflection. M2 B180 or its refutation in the calculus. M3 the floors of §1.6 without the reflection.

**Tests for B180.** T8: the functional equation of Dirichlet series of Gauss sums of order three is known through Eisenstein series on a cover [C]; an elementary proof is a recognized open question of that subject, not of this corpus.

## 2.12 New field for RH as AdS physics: uncertainty principles for the cusp

**Does it need a new field?** The receivers, the regulators and the filters exist (HAT, BHR, AHMH, CTH, FFA); dynamical realizations and their limits exist (ArithmeticResonanceTheory). One mechanism has no programme: a lower bound for the damping of the slowest mode.

| Aspect | Content |
|---|---|
| What it is about | Resonance-free strips for horizons of finite volume with a cusp, where the escape is through the cusp and the trapped set is not fractal; the role of the arithmetic of the group in such a strip |
| What it is like | The theory of essential spectral gaps of open systems [C], transplanted to a setting in which its hypothesis fails and the gap, if any, is arithmetic |
| Established | Exponents `1−Θ/2` and `1−Θ∞/2`; filters; regulators with the count of their limit; `3/16` for the bound states of congruence quotients; Hölder realizations give a strip and additive realizations have no oscillation estimate [L*]/[N] |
| Criteria | Built from the horizon and the places, never from the zeros. False for a non-arithmetic cusped surface of the same area and for graph horizons with slow resonances. Not a consequence of Hecke symmetry alone. A gap with a margin is a half-plane; the maximal gap needs an equality case |
| Questions it must answer | B178. Which property of the cusp excursions of an arithmetic group fails under deformation of the group? Is there a horizon of this family with isolated least-damped modes, as a calibration of world I? What is the horizon meaning of the quantum of a multiplicity? |
| Tools it develops | Transfer operators of the cusp excursions; uncertainty estimates for sets that are not fractal; Euler filters; the fixed-height floor |
| Objects | Horizons, excursions, resonances, filters, gaps |
| Language | gap, slow mode, filter, excursion, saturation |
| Mechanisms | Built on: the receivers and the filters. To discover: a principle that separates the modular group from its deformations |

**Main conjecture.** An arithmetic cusped horizon has a resonance-free strip. **Milestones.** M1 the two calibrations in Lean. M2 a gap in a toy family where it is a theorem. M3 any gap for the modular horizon. M4 saturation.

## 2.13 New field for RH as topology or geometry: symplectic index theory of the aperture

**Does it need a new field?** The lattice and index theory exists (AGZ, HFP), with the exact index for every Hecke character, the finite-scale reduction and the jump law. Paths exist and transport nothing. What no programme contains is a topological computation of the index.

| Aspect | Content |
|---|---|
| What it is about | The family of restricted Weil forms as a path in the aperture; its conjugate points; a symplectic structure in which the index is a Maslov index; the ends of the path |
| What it is like | Morse theory of a variational problem whose second variation is the comb form [C]; the arithmetic enters as impulses at the logarithms of the integers |
| Established | Index nondecreasing in the aperture; jumps equal nullities; resonances finite below every bound; robust index of the finite comb; the scalar flow of the chain; unit-gap receivers [F]/[L*] |
| Criteria | The index of the Liouville twist is positive just above the trivial aperture. A wrong constant, weight or tree length produces a conjugate point. The structure is defined without the zeros. A unit gap suffices: index at most one is index zero |
| Questions it must answer | B179. Is a null mode at a resonant aperture charged (B104)? Are the nullities even? What is the end of the path at infinite aperture, and does it exist for the finite combs of a fixed ratio? Is there a second object whose path has the same ends and no conjugate point? |
| Tools it develops | Hamiltonian form of the canonical system; Lagrangian paths; comparison theorems; the finite comb as discretization |
| Objects | Apertures, null modes, conjugate points, Lagrangian planes, ends |
| Language | conjugate aperture, nullity, crossing, end, homotopy |
| Mechanisms | Built on: the jump law, the robust index, the flow. To discover: a homotopy invariant that equals the index |

**Main conjecture.** The aperture path of ζ has no conjugate point, and this is the vanishing of a homotopy invariant. **Milestones.** M1 the Hamiltonian form. M2 the Maslov index on the finite combs. M3 the ends. M4 a comparison object. M5 index zero.

## 2.14 A research programme to construct `𝔽₁`

**Goal.** A geometry in which Spec ℤ has a product with itself and the inequality of Castelnuovo and Severi on that product is a theorem. The programme is `AbsoluteGeometryOfSpecZ` with `HodgeTheoryOfAFixedPart`; `SelectiveArithmetic` and `FloorFreeArithmetic` are its test benches.

**What the corpus fixes [L*] unless marked.**
| Item | Theorem |
|---|---|
| The pairing | jets + contacts − counterterm `→2d₁d₂−Z(f)`; Bézout ⇔ RH; index = number of right zeros |
| Forced data | the constant (`c≤0`), each contact at its price `2\|t\|/√n`, tree lengths `log p` |
| Number rings | for every number field: ideals as degree points, contacts `Σ_{N𝔭^k=n}ψ(𝔭)^k log N𝔭`, the counterterm with discriminant and conductor, exact index per ray class character and for the Dedekind zeta function; the class characters together carry the ideals of trivial class with pole-plane weight `1/h` |
| Below the first contact | a discriminant above `(128π)^{r₁+r₂−1}(4π)^{r₂}` gives the inequality with margin `∫f²/5000` |
| Finite scale | RH ⇔ the sign of `𝔚_{3K+1}` on step packets ⇔ eventual nonnegativity on every ratio window; robust index = right zeros |
| Tails | the comb form is a quadratic form in the increments with rows the remainder of the prime number theorem; Laguerre tails → Li coefficients |
| Sections | planar restriction is an equality of ideals; sections of the first `N` graphs in aligned boxes: volume over `N!` |
| Deformations | the price path at every `n₀≥2` and the tree length: RH at every parameter on all packets |
| Certificates | every system feasible at a large aperture is within `ε` of `Λ` at each `n` |
| Curves | the defect of an integral class on a hyperelliptic curve is a natural number, quadratic on rays |

**What it would be like [D].** Spec ℤ over `𝔽₁` is a curve of infinite genus whose square is rigid: it is not a member of a family, every one of its invariants is forced, and its Néron–Severi lattice is the same for every number ring up to the density of the comb. Its sections count like a curve, not like a surface. Its index is a function of the aperture with jumps at null modes. Passing from `𝔽_p[T]` to ℤ keeps the lattice and loses the count.

**State of the constructions.**
| Construction | Deliverable | State |
|---|---|---|
| I. A path on the comb lattice | transport of the sign from a known case | closed: price paths at every prime, tree-length path at `2`; RH at every parameter |
| II. The archimedean fibre glued to the trees | the comb form as a glued form | invariant gluings refuted [KR]; every free parameter forced |
| III. Stepanov on the planar square | a small section vanishing on a window | closed: equality of ideals |
| IV. Squares of towers and of class fields | the index law per character | closed for ray class characters; the base has weight `1/d`, `1/h`; Artin characters open (A133) |
| V. The own comb | Bézout for an integer-norm system on its comb | closed: fails for the squares |
| VI. A count | natural numbers with quadratic Tate limit | the object's count is linear; counts on surviving prime rays ⇔ RH; no definition without the form (B87) |
| VII. Finite scale | the inequality in finite rank | closed as an equivalence: step packets |
| VIII. The index as a topological invariant | index zero from the ends of the aperture path | not started (B179) |

**Criteria.** C1 reproduces Weil and Stepanov for curves. C2 counts alone are not enough. C3 uses the functional equation: integer-norm models with a finite layer fail, the Liouville twist fails at rung one. C4 uses the Euler product. C5 sees the exact normalization. C6 infinite type. C7 the diagonal is the density of a comb, with discriminant and conductor. C8 positivity is derived, and not from a section count. C9 selective only where a contact enters; no margin. C10 on a number ring it gives the index of each ray class character. C11 below the trivial aperture it proves nothing that the dominated box does not have. C12 at finite scale it is the sign on step packets. C13 it is a statement at the point: no deformation of the square transports it. C14 its count is quadratic in the divisor. C15 it treats a null mode at a resonant aperture.

**Questions the programme must answer.**
1. A count quadratic in the divisor (B87, B169).
2. Bézout from a property of the object (B149).
3. The index as a homotopy invariant of the aperture path (B179).
4. Artin characters (A133).
5. The step-packet matrices as the intersection matrices of an object with a known index theorem.
6. The polar charge of a null mode (B104).

**Tools.** Witt vectors and Λ-structures; comb finite parts; step packets and flat packets; the index law for Hecke characters; combs of norms; the scale; tangent data.

**Order of work [A].** A133; the Hamiltonian form of the canonical system (first step of B179); a quadratic count. **Decisive test.** A construction whose Bézout holds for an integer-norm system with a finite layer, for the Liouville twist at rung one, for a wrong constant, or along a path of squares, is wrong [L*].

## 3. The one big question: are the two estimates theorems at `7/8`?

**Why not a question about ζ.** No statement about the zeros of ζ below AAL and quasi-RH passes the tests (verdict before §2.4). Natively every route is a receiver, every kind of statement off the scale has its kill, and every regulator has the count of its limit. The repository holds one producer, external and unchecked here. The frontier map states that the native graph has no unconditional `7/8` theorem [F].

**What is in Lean.** The route is one implication (`zetaZeroAbscissa_le_of_two_estimates`): over `ℚ(ζ₃)`, a direct bound `Z^{a₁}` and a comparison `Z^{a₂}` with the corrected signal, with `a₁,a₂<β` common to all ray class characters whenever the family is zero-free in `Re s>β`, for every `β>σ₀`, give `Θ≤σ₀` [L*] (N5). The source identity, the cubic residue with its Gauss coefficients, the large sieves over the plane and over the Eisenstein integers, the buffered bins and the exponent budget are in Lean [L*]/[F].

**Question (B181).** *Is the comparison estimate a theorem: does the completed sum built from the cubic residue, after removal of the cube indices, differ from the corrected signal of every ray class character of `ℚ(ζ₃)` by `Z^{β−m}`, with one `m>0` for the whole family and with corrections `H_η` that are holomorphic and nonvanishing right of `7/8` and bounded on `Re s≥2`?* The frontier map lists exactly these three items as open [F] (A118a–c). The direct estimate is the second half (A118d).

**Why this question.**
- It is the only place where a producer exists, and the corpus's own analysis of it found one circular step: the reflected rows evaluated through the same twists return the zero [L*] (FCT16). A check of the other steps is not routine.
- It is below quasi-RH in kind: an identity between explicit sums with an error estimate, uniform in a family; no information on zeros enters except the hypothesis of the continuation step.
- Its answer decides the premise of several routes at once.

**What either answer gives.**
| Answer | Effect |
|---|---|
| Yes, and the direct estimate holds | native `Θ≤7/8`: the edge world is excluded; `Θ∞<1`; the return transfer is exactly RH (FCT4); the three rungs hold with `b=7/8` (SA4): rung up to `4/3`, level `11/8` on large primes, return-free windows; family continuation is a live route with the room `[13/15,7/8]` as its frontier (B174) |
| Yes for the comparison, the direct estimate fails | the failing estimate has a named exponent in the budget calculus; the boundary of what holds is a theorem |
| No | the corpus is producer-free; §2.5 and §2.9 are the frame |

**First step and obstacle.** The Gauss-series formulas of the cubic residue for `Re s>2` are in Lean and its all-height Fourier/Bessel formulas are graded [S]; the first step is the removal of the cube indices on the unit cusp. Named obstacle: uniformity in the character of the height comparison, for which the receiver `heckeHalfPlane_of_family_height_estimates` fixes the form of the required bound.

**Tests.** T1: a producer lemma, implied by nothing about ζ's zeros; alone it implies no half-plane. T2–T4: pass. T5: the comparison has to fail for sources of even order, where the sign is the parity of the character [L*] (F3). T6: pass. T7: moves Π93, Π159, Π162. T8: not a named problem; its inputs are those of the external source, unchecked here.

**Dependence.** The question rests on `[X]`. It asks for no step of `[X]` to be trusted.

### Alternatives considered
| Question | Effect | Verdict |
|---|---|---|
| The cost of a window (B176, §2.4) | the verification ladder leaves the first contact, or is retired | native; passes; produces no sign beyond verified heights |
| Polar orthogonality (B104) | the critical curve becomes one inequality | native; open; produces no sign |
| Cancellation across the rows of a twist family (B175, §2.5) | a boundary below the floor bin of the class | a producer of the strength of its half-plane [P]; fails T1 |
| The least remainder of the integer count of a fake (B182, §4) | the count as a structure with or without a model | a method question on models; its negative side is of GRH type |
| The weighted current (B145, §2.6) | AAL without positivity | AAL strength; fails T1 |
| A relaxation lower bound (B178, §2.7); a Maslov index (B179, §2.8); a quadratic count (B87, B169); `JasDressedPSD 1` (B160); the sign on step packets (B152) | a half-plane or RH | producers; fail T1 |
| What excludes a finite stratum with both structures (B157) | a calibration for the atoms | a method question; proves no atom |
| Deuring–Heilbronn for ζ (B141); B13; Landing | atoms | no first step |
| Depth density `o(T)` (B57); arithmetic control beyond frequency one (B150) | first near-line inputs past the diagonal | census problems |

## 4. A question on the models: where is the last fake?

**Why a question about models.** Of the two properties of ζ that no model has (§1.3), the unit multiplicity of the integers is a quantity: the remainder of the integer count `N(x)−Ax`. On that axis the corpus has the two ends and no point between. A **fake** is a system other than the rational primes whose zeta function has a zero in `Re s>½` at a point where ζ does not vanish.

**What is in Lean.**

| Class | Remainder of the count | Zeros right of the line | Evidence |
|---|---|---|---|
| discrete systems with integer norms | `o(log n)`, in particular bounded | the system is the rational primes; every other such system has remainder `≥c·log n` at arbitrarily large `n` | [L*] (LF1, LF2) |
| the odd primes with extra labels of norms `3` and `4` | `O(log²x)` | exactly the zeros of ζ on `Re s>0`: no fake | [L*] (LF3) |
| natural generators `q_k≥2`, natural coefficients; continuation to `Re s>½`, for the wave products to `Re s>⅓` | known in the mean only: `Σ_{n<N}a_n/N→A` | every finite divisor at `½<Θ<1`; a top pair with infinitely many pairs of prescribed real parts | [L*] (FFA12, N3, LF6, LF7) |
| multiplicative coefficients in `{0,1,4}`, generators of negative multiplicity at `2` | bounded: `−3≤N(x)−x≤0` | a zero in `½<Re s<1`, repeated with period `2π/log 2` | [L*] (LF4) |
| continuous systems with nonnegative prime and integer densities | `→0` after a constant; a quadratic polynomial in `log x` | one off-line pair; a nonreal zero at `2/3+i` | [L*] (LF6); [L*]/[N] (LF5) |

For coefficient sequences that are only multiplicative, and for continuous systems, the count is no constraint: a fake exists at bounded remainder. For discrete systems with nonnegative generators and integer norms the count is rigid below `log n`, the one model at `log²x` is no fake, and every fake of the corpus has a count without a rate. For systems generated by the rational primes outside a set with convergent reciprocal sum the Möbius sums are not `O(x^θ)` for any `θ<½` [L*] (LF9).

**Question (B182).** *What is the least remainder of the integer count of a fake among discrete systems with integer norms? In exponents: is there a fake with `N(x)=Ax+O(x^β)` for some `β<1`, and is there one with `β<½`?*

**Why this question.**
- It measures the one structure that has no model. The rigidity theorems state where unit multiplicity identifies ζ; the question asks at which remainder it starts to bind, which is milestone M1 of §2.9 with the count as the defect.
- Its positive side is a construction: no zero of ζ enters, and the corpus has the tools: quantile discretization of a prime density with integer rounding [N] (LF8), the finite-layer and wave products (FFA12, LF7), the continuation from a count remainder [N] (LF10).
- The classical theory of generalized primes gives a calibration [C], not in the corpus: with real norms, random placement of the primes gives systems with `β=½+ε` whose zeros approach `Re s=1`; the exponents of the prime count and of the integer count are not both below `½`; the Dedekind zeta function of a quadratic field is a discrete system with integer norms and `β≤1/3`. Below `½` the known systems are arithmetic.

**What either answer gives.**
| Answer | Effect |
|---|---|
| A fake with `β<½` | the count is a structure with a model: unit multiplicity acts only as the exact count, below `log n`; a proof uses it as an identity (Poisson summation with a bounded remainder), not as an estimate; criterion U4 of §2.9 has no continuous form in the count; a row of §1.3 |
| Fakes with `β<1`, and the constructions stop at `½` | the obstruction that stops them is a statement on the generators: below the square root the positions of the primes cancel in `Σq_k^{−s}` beyond what independent placement gives. That statement is the candidate for the inequality of §2.9; its first instance is the periodicity of a character |
| No fake with a rate | a negative answer for `β>1/3` says that every right zero of every real primitive Dirichlet `L`-function is a zero of ζ [D] from [C]: of GRH type, without a first step |

**First step and obstacle.** The count of the corpus's own fakes. They are Euler products over quantile-discretized norms, with `log ζ_B(s)=∫e^{−su}w(u)du+sΛ(s)+R(s)` and `Λ` the transform of a discrepancy bounded by one [N] (LF8). A bound for `ζ_B` that is polynomial in `|t|` on a line `Re s=σ₁` gives `β≤σ₁+ε` [C]. Named obstacle: the discrepancy bound gives only `|sΛ(s)|≤|s|/Re s` [D], an exponential bound for the product; a polynomial bound needs cancellation in the discrepancy of the generators, from the quantiles or from a random choice of the rounding.

**Tests.** T1: a method question on models; its positive side is implied by nothing about ζ's zeros; its negative side is of GRH type, so only the construction is a door. T2: an existence statement with an exponent. T3: named for each answer. T4: pass. T5: calibrated on the five classes of the table. T6: pass. T7: moves the count row of §1.3 and milestone M1 of §2.9; not a shape answered in Lean (log §3.20). T8: for real norms the question belongs to the classical theory of generalized primes [C], where the range below `½` may be a recorded open problem; not checked. The first step is in corpus objects.

**Dependence.** None on `[X]`.
