# Obstacles summary — status quo

Companion to [route-obstacles.md](route-obstacles.md) (per route), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ) and [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem). Corpus checkpoint: commit `b23b54cd36` with its working tree (2026-11-11). Fact log: `logs/review-1111-rev2-facts.md`; identifiers in parentheses refer to log §4, §6, §8 and §9, `D1–D9` to log §7.

**Evidence.** `[L*]` Lean statement read at the declaration for this report; `[F]`, `[KR]` stated by the frontier map and the scoped-obstruction ledger at the checkpoint, both read in full; `[S]` module graded unfinished or unintegrated by the frontier map; `[D]` deduction made here from `[L*]` statements, not a Lean theorem; `[C]` classical mathematics quoted from memory, not in the corpus, to be checked before use; `[A]` assessment; `[X]` the theorem of the external source cached in the repository (OpenAI, 30 September 2026), taken as proved: every finite-order Hecke `L`-function over `ℚ(√−3)` and every Dirichlet `L`-function, ζ included, is zero-free in `Re s>7/8`; so `Θ≤7/8`. Its formalization in the Lean corpus is incomplete: the native graph has no `7/8` theorem [F], and the missing steps are just work (A118). **Natively** refers to the Lean graph. Sections 2.3–2.18 and 3 are interpretation and ideation: every untagged statement there is a proposal, not a result.

**38 live formulations; 12 candidates** (SEC, CDC/BSH, S3, APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF). HJ is PA; PCS, DR, PW-B are retired labels.

**Notation.** As in [route-obstacles.md](route-obstacles.md): `Θ`, `Θ∞`, `w`, ZAL, AAL, B13, Landing, DH, B56; world I, world II; the prime trace `2Re S(log p)`; logarithmic windows; tangent datum and normalized trace; the comb pairing, the comb form, the power tails `F_a`; step packets; system, mass, dominated, rung, trivial aperture, Liouville twist; `JasDressedPSD σ`; the signal of the zeta kernel; fake; the probe and its correction `H_η`. **The scale** is the common parameter of the graded receivers (§1.2). A statement is **off the scale** if it carries no exponent (§1.5).

## 1. Big picture

### 1.1 One object, two exact forms
- **One inequality per prime.** RH ⇔ `2Re S(log p)≥−K` at the primes of arbitrarily late logarithmic windows outside `Ce^{δT}` primes per window. Equivalent on the same windows: the upper bound alone, without omissions; the absolute value; `ℕ`-counts on the surviving rays with quadratic limit the plane defect; local even moments with one growth exponent for all orders; the limit of the two-bump comb form [L*] (MF1–MF5, MF9).
- **One matrix on the integers.** RH ⇔ exactly one positive square of the comb pairing on packets; the negative index of the defect is the number of distinct right zeros, for ζ with Dirichlet characters, for every Dedekind zeta function through its ideals, for the class characters together, and for the degree-two Artin character of the splitting field of `X³−2` [L*] (AG3, AR3). At finite scale: RH ⇔ `𝔚_{3K+1}≥0` on step packets of `3KR` blocks for all `K,R`; ⇔ eventual floors `−ηΣc²` on every ratio window; ⇔ a positive coefficient-mass floor `γ(Q)` on each ratio window [L*] (AG5, HF1). The distance between the comb at block size `B` and the matrix `𝔚_Q` is at most `6(J+1)(2X+16(1+log 2XB)+2ψ(Q))/B` per unit of `Σσ²` [L*] (SP1).

### 1.2 One scale
Every graded receiver of the corpus is an equivalence at each level of one scale [D] (D1):

| Reading | Parameter | Depth it reaches | Evidence |
|---|---|---|---|
| saving of the contacts `n^{½+γ}` | `γ` | sign to rung `κ<1/(2γ)` | [L*] (SA-g) |
| the sign on a rung `κ` | `κ` | no isolated zero of depth `>1/(2κ)` | [L*] (SA-g) |
| bounded dyadic Möbius moment at length `T^θ` | `θ>1` | depth `<1/(2θ)+ε` eventually | [L*] (SA-g) |
| level of the dressed aggregate on large primes | `σ≥1` | `\|Re ρ−½\|≤σ−1` | [L*] (JA1) |
| exponent of the signal of the zeta kernel | `b∈[½,1)` | `Θ≤b`, and conversely | [L*] (FC1) |
| exponent of a twist family: a generic mean square of the Möbius sums of length `Z` over the principal `n`-th-power twists of norm up to `Z^θ` | `θ` | `Θ≤½+(1−1/n)θ/2`, and conversely; the least `θ` is `(n/(n−1))(2Θ−1)` | [L*] (TF1, TF2) |
| growth exponent of the power tail `F_a` | `σ` at `0<a<½` | `Θ≤1−a+σ`, and conversely; convergence exactly for `a<½−w` | [L*] (PT2, PT3) |
| exponent of a floor of the two-bump form | `σ` | floor exactly `σ` | [L*] (FF1) |
| window moment of order `2k` with exponent `A` | `A/2k` | the abscissa law at depths `≥A/2k` | [L*] (FF4) |
| horocycle exponent; ringdown rate | `α`; `δ` | `Θ≤2−2α` (with a finite Euler filter `Θ∞≤2−2α`); `Θ≤1−2δ` | [L*] (log §4.8; RD1) |

Level one, rung `∞`, every `b>½`, every `a<½`, exponent zero: each end of the scale is RH. Sizes prove the scale up to rung `1−o(1)`: every dominated system is positive with margin below the trivial aperture `log log(mass)` and the Liouville twist fails just above it; in the height aspect a dominated system fails at `log log t+log(π/2)+η` [L*] (SA-a, SA-b). At the first conductor rung the sign for a real character forces primes with `χ(p)=1` and with `χ(p)=−1` below `e^{2η}log²q` [L*] (SA-e). At a rung `κ` the sign on bounded shapes fails only on a set of heights of measure `≤T^{1−1/(2κ)+ε}` [L*] (SA-c). The level `b=7/8` is a theorem [X]: the rung `κ<4/3` for the centred contacts, positivity on large primes above the level `11/8`, heavy returns only for `log t≥c·y^{1/8}` [L*] (SA-d), the power tails converge for `a<1/8`, every pulse rings down at the rate `1/16` and the horocycle exponent is at least `9/16` [D] (D2). In Lean no rung above one is proved in any aspect. The open part of the scale is `½<b<7/8`.

### 1.3 Three structures; every two have a model
ζ has an Euler product, the Riemann functional equation, and every integer with multiplicity one. The corpus has a model for each structure alone and for pairs [L*] unless marked:

| Structure kept | Model | What fails | Evidence |
|---|---|---|---|
| reflection symmetry, temperedness (every identity of the explicit formula) | every tangent datum is the top layer of a finite symmetric configuration | AAL, B13 | FF6 |
| positivity of the prime measure, a simple pole | a nonnegative density with any finite layer at any `Θ<1` | AAL | FF6 |
| Euler product over natural norms, natural coefficients, linear counting | every finite divisor right of the line, with multiplicities, continuation to `Re s>½`; two-scale products with a tail | AAL, B13; graded repulsion | FF6, MD2 |
| Euler product over the rational primes, with repetition | every finite layer at `17/30<Θ<1` | AAL | FF6 |
| Euler product over the rational primes with real weights in `[0,2]`; multiplicative coefficients `0≤a(n)≤C_εn^ε`; meromorphy on ℂ; polynomial bounds for `F` and `1/F` right of `Θ` (given `Θ<1`, which holds [X]) | `ζ(s)/(ζ(s+1−ρ₀)ζ(s+1−ρ̄₀))` with finitely many Euler factors removed: exactly the pair `ρ₀,ρ̄₀` right of `Θ`; a pole in the left strip | the abscissa law at the frontier of ζ | MD3 |
| a subset of the rational primes: every integer once or not at all; count `Ax+O(x^β)` for any `β>½`; from a half-plane `Re s>Θ` of ζ the exponent `½−(1−max(Θ,¾))/64`, so `½−1/512` [X]; under RH every `β>⅓` | the integers free of a thin set of primes: a real fake zero, with non-real ones on its vertical line | the line, by a real zero; a non-real pair alone on top is not modelled | IF4, IF5, IF7; [D] (D6) |
| integer norms, a real character | the system with zeta function `ζ·L(s,χ)`, count `L(1,χ)x+O(√x)` | a fake iff `L(s,χ)` has a right zero that ζ lacks | IF3 |
| the Riemann functional equation, Gamma factor, residue one, growth of order one, count within one | all zeros simple, off the line, approaching it | Landing | MD1 |
| Euler product and a functional equation of degree two on the integers, unbounded coefficients | `ξ(s+a)ξ(s−a)`: every critical zero `ρ` gives zeros `ρ±a` off the line | ZAL; strip self-improvement | [KR] |
| both structures up to an integrable defect, positive continuous prime measure | `ζ(s)exp(ε/(s+1)²)` | nothing: the zeros are those of ζ | RG1 |
| the Riemann functional equation with an integrable defect on a countable system; or a bounded count error at slope one | the rational primes alone | — | RG1, CR1 |
| Euler product over geodesic norms and a functional equation, order two | Selberg zeta functions of surfaces with small eigenvalues: finitely many real zeros in `(½,1)` | B13 | [C] |

Consequences [D]. A mechanism that reads the Euler product through the zero configuration has floor `½` [L*] (FF1); a producer has to use the Euler product on the function. A power saving of the count is realized by models at every exponent above `½`, and below `½` given a zero-free half-plane of ζ; so the count as a power does not separate ζ. Every such model is a deletion of primes and has a real zero on top; additions alone never fake, and a system that only adds primes vanishes at its real abscissa [L*] (IF1, IF7, AO1). What no model of the corpus realizes is the exact count (a bounded error) and the exact functional equation, and each of the two alone identifies ζ. The atoms have no model among Dirichlet series over the integers with the Riemann functional equation; outside that class B13 fails in a classical family.

### 1.4 Two worlds, three atoms, one shape of world I
Quasi-RH is a theorem: `Θ≤7/8` [X]; with `Θ<1 ⇔ Θ∞<1` [L*] (AT2) also `Θ∞≤7/8`, and the world `Θ=Θ∞=1` is excluded. A failure of RH is a finite isolated top layer at some `β≤7/8` (world I) or a tail with `½<Θ=Θ∞≤7/8` (world II). RH ⇔ ZAL ∧ B13 ∧ Landing; AAL ⇔ B13 ∧ extreme DH [L*] (AT1); B13 ⇔ the supremal negative index on real packets is `0` or `∞` [L*] (AC1).

At `b_*=Θ−½` the normalized trace is in exactly one of four sectors: RH; top line empty and trace `→0`; top line finite nonempty and trace asymptotic to a nonzero real trigonometric polynomial; top line infinite and no such limit [L*] (FF14). The absence of the third sector gives AAL; it is not equivalent to AAL: a tempered symmetric configuration with AAL has a finite top line below which the zeros accumulate [L*] (FF14). World I is the third sector with an isolated top line. Receivers of AAL [L*]:

| Form | Statement | Evidence |
|---|---|---|
| unit gap | AAL ⇔ for every line `Re s=½+h` the number of zeros to its right is at most one or infinite | FF2 |
| non-attainment | for every depth `b` bounding all zeros there are a length `L` and arbitrarily late windows of length `L` on which the trace is `≤εe^{bu}` for every `ε` ⇒ AAL; the same for `ψ(x)−x` against `x^β` on multiplicative windows, and at the primes of the window | FF2, FF3 |
| amplification | one growth exponent for all even moments of the trace on late windows of one length ⇒ AAL | FF4 |
| horizon | AAL ⇔ no nonzero Euler polynomial filter accelerates the horocycle rate past `1−Θ/2` | log §4.8 |

The receivers are theorems about tempered conjugation-symmetric configurations, so their hypotheses fail on every configuration of §1.3 that violates AAL. A one-sided floor on windows of one length has a finite-stratum model; floors at every length give AAL [L*] (FF5, MF7). In world I the multiplicities are quantized: the Bohr mean of the normalized trace at a top frequency is zero or at least `2\|B̂\|²` in modulus [L*] (FF7); the Gaussian window sums of `μ` and of `λ` are asymptotic to their residues at the top zeros, polynomials of degree the multiplicity minus one times `e^{ρu}`, with leading numerators that differ by the unit `ζ(2ρ)` [L*] (TD1).

### 1.5 Off the scale: each kind has a receiver and a kill
| Kind | Receiver | Kill | Evidence |
|---|---|---|---|
| homogeneous floor | a floor `−C‖f‖²` of the clock regulator at one cutoff per large aperture gives RH | the regulator lies below Weil's form at every cutoff | [L*] (FF11) |
| unit gap | an analytic approximant of ζ with at most one right zero, infinitely often, gives RH; a form with one negative square in which the right zeros are a symmetric spectrum gives RH | `Λ(s)/Λ(s+N)` has a unit gap iff RH; the heat flow has at least two nonreal zeros at small times unless RH | [L*] (FF9, FF11) |
| certificate | some feasible weight system at every aperture gives RH | feasible systems converge to `Λ` in every coordinate; the pencils `ξ(s+h)+ξ(s−h)` and the cleared Eisenstein constant term are no Dirichlet series over their dominant half | [L*] (FW1, FF10, FF12) |
| amplification | one exponent for all even window moments gives AAL | bounds of all orders with one exponent are bounds for the powers of the sup norm; one order `2k` reaches depth `A/2k` | [L*] (FF4) |
| symmetrization | a functional decreasing under projection to the line | a linear statistic monotone under splitting has `Re F″≤0` at every split point; a differentiable function of finitely many linear statistics that is monotone has a gradient symbol whose real part vanishes on the line when it is bounded below and tends to zero | [L*] (FF13, GL1) |
| replication | a bounded normalization of translates at every right zero gives AAL | under a finite right layer every bounded normalization tends to zero | [L*] (FF8) |
| positivity of a prime density | excludes a finite layer on the line of the pole, by the count `2M≤A` | below the line of the pole a compensator on a bounded interval restores positivity for every layer | [L*] (PL1, FF6) |
| the count as a power | a bounded count error identifies the rational primes | fakes at every exponent above `½`, and below it from a half-plane of ζ | [L*] (CR1, IF4, IF5) |

### 1.6 The half-plane: a theorem at `7/8`, an implication in Lean, three nested limits
`Θ≤7/8` is a theorem, for ζ, for every Dirichlet `L`-function and for every finite-order Hecke `L`-function over `ℚ(√−3)` [X].

**The frame in Lean.** Over `K=ℚ(ζ₃)`: if, whenever every `L(s,η)` is zero-free in `Re s>β` off `1`, every ray class character `η` has a sum `J_η` with `‖J_η(Z)‖≤CZ^{a₁}` and `‖J_η(Z)−f_η(Z)‖≤CZ^{a₂}`, `f_η` the signal of `exp((s−c)²)H_η(s)/L(s,η)`, with `a₁,a₂<β` common to all characters and for every `β>σ₀`, then `Θ≤σ₀` [L*] (FS2). The form of the step with pole-cleared kernels `(s−1)L(s,ψ)` has a false premise as soon as the family contains a nonprincipal character [L*] (FS1). With the correction of the probe itself, which is the principal correction with the phases `κ_v⁶`, the corrections are holomorphic and nonvanishing right of `σ≥7/8` and the implication holds for `7/8≤σ₀<1` with the two estimates as its only premises [L*] (FS6); with the principal corrections it holds for `2/3<σ₀<1` [L*] (FS3).

**The source in Lean.** The cube of the composite cubic Gauss sum is the ideal Möbius value times a phase; for odd order `g(χ)^n=−card F+z(μ−1)²`, for even order the sign is `χ(−1)` [L*] (CU1, FC4). The Poisson coefficients of the probe: reciprocity for the quadratic and sextic symbols, multiplicativity up to reciprocity, the values at prime powers, the local factor in closed form; the principal row is `ζ^S(6z)ζ^S(w)L^S(x,η)⁻¹∏H_v` in its absolute region; the correction of an unramified row has no pole in `w` [L*] (FS4, FS5, FS7). The quadratic large sieve over `ℤ[ω]` holds at exponent one [L*] (QS1). Not in Lean: the full arithmetic Poisson series and its continuation, the comparison with the reciprocal signal, the reflection of the completed theta row, the sextic sieve, the zero detector, and both savings uniformly in the character [F] (A118).

**The budget in Lean** is a calculus of exponents, not of sums [L*] (TB, LP, FG, MV, FC3):

| Statement | Value |
|---|---|
| positive form: a generic mean square over the twists of norm up to `Z^θ` with the target among them | the half-plane `½+(1−1/n)θ/2`; at `n=6`: `11/12` at `θ=1`, `7/8` at `9/10`, `13/15` at `22/25`, `5/6` at `4/5`; `½` at `θ=0` |
| the published geometry `(17/48,23/48,1/6)` | `θ=9/10`; no geometry reaches `θ≤9/10−6/6250` with a row count `≥21766/32589−10⁻⁴` in the bin `δ=79/204` |
| the row count `1−δ+η` in the bins | boundary `θ=((5+6η)n−8)/((5+6η)(n−1))`: `22/25` at `η=0`, `9/10` at the published excess |
| the floor bin summed trivially (`R₀=1`), every order, both Gram regimes | `θ≥(5n−8)/(5(n−1))`: `13/15` at `n=6` |
| the floor bin with a row exponent `R₀≥½+1/n` | `θ≥((6R₀−1)n−8)/((6R₀−1)(n−1))`: `4/5` at `R₀=5/6`, `2/3` at `R₀=2/3` (`n=6`) |
| matched phases | saturate the signed Gram of the rows at `\|B₀\|²A₀²`: with worst-case amplitudes `R₀=1` |
| rows with the hybrid slot retained, every geometry, `n≥3` | `θ≥(n−2)/(n−1)`: the half-plane `1−1/n`, `5/6` at `n=6` |
| a bilinear row–column saving `s` taken before Cauchy–Schwarz | `θ≥(n−2)/(n−1)−(2n/(n−1))s`: the half-plane `1−1/n−s`; at `n=6`: `¾` at `s=1/12`, `½` at `s=1/3` |
| reflection and summation words | elements of `SL₂` with an invariant quadratic form: elliptic, parabolic or hyperbolic; unitary re-expansion preserves the `L²` norm of the rows |
| reflected rows through the same twists | return the zero `β`: circular |
| sieve terms `K^uN^v` with `4u+3v≥5` | no half-plane at any family length; the optimal sextic multiplicative sieve has the floor `26/27`, the additive planar sieve `1−1/(2n)` |
| two or more row variables; other conductors and orders | `θ≥n/(n−1)`; the corners of the designs without slots are at least `8/9` (conductor exponent two, every order `n≥6`), `25/28` (order four with itself as twist), `49/54` (sextic coefficient, cubic twist); a cover of odd order `n₀≥3` has principal frequencies of order `2n₀`, and among the orders `n≥6` the order six has the least corner |

**The law of a family is the scale** [L*] (TF1–TF4). The principal `n`-th-power subfamily has a generic mean square exactly for `θ≥(n/(n−1))(2Θ−1)`; with `μ²` in place of `μ` exactly for `θ≥n/(n−1)`; the Jacobi family is generic at every `θ` iff RH and GRH for the odd squarefree quadratic twists hold.

**The correction is an `L`-function** [D] (D3). The local factor of the correction is `(1−Q⁻²)(1−Q⁻¹(A Q^{3−6s}−ηQ^{−s})/(1−ηQ^{−s}))/(1−A Q^{3−6s})` with `A=κ⁶`, `κ=(π̄/\|π\|)η(π)` at a primary prime [L*] (PC2). So `H_η(s)=L^S(6s−3,ψ₆η⁶)·E_η(s)`, with `ψ₆(π)=(π̄/\|π\|)⁶` a Hecke character of infinite order of `ℚ(ω)` and `E_η` absolutely convergent on `Re s>½`. The Euler product of `H_η` converges absolutely exactly on `Re s>2/3` [L*] (PC3), and `H_η` vanishes at the points `s=(3+w)/6`, `w` a zero of `L(·,ψ₆η⁶)`, all of which lie in `½<Re s<2/3` [C].

**Three nested limits** [D] (D3, D4):

| Limit | Value at `n=6` | What sets it | What crosses it |
|---|---|---|---|
| the room of the estimates | `[13/15,7/8]` | the row count of the binding bin | a density count for the sextic twists (B174) |
| the floor of the squares | `13/15`, then `5/6` | trivial summation of the floor bin; every Cauchy–Schwarz row sieve | signed cancellation across the rows for the actual coefficients (B175) |
| the wall of the frame | `2/3` | the abscissa of the correction `L(6s−3,ψ₆η⁶)`; its zeros in `½<Re s<2/3` | a zero-free half-plane for the characters `ψ₆^kη`; with one abscissa for the tower the frame is valid on `Re s>(3+b)/6`, with fixed point `3/5`; under GRH for the tower the wall is `7/12` (B184) |

The line lies below all three.

### 1.7 Finite scale and the index in the aperture
Immediately right of an aperture the index of the restricted Weil form is the negative index plus the nullity [L*] (IA1); resonant apertures are locally finite [F]. `r≤#`right zeros ⇔ for some ratio and margin the robust index of the finite comb is eventually `≥r` [L*] (HF2); the unshifted comb index at ratio `Q` lies eventually between the aperture index and index plus nullity, with equality off resonances [L*] (HF3). So RH ⇔ no aperture carries a null mode, and with finitely many off-line zeros finitely many resonant apertures carry the whole index [D].

### 1.8 The square returns identities; deformations return RH
Bézout holds for one constant, one set of contacts, one tree length [L*] (AG1). Planar restriction is an equality of ideals; the count on two graphs is the split norm; the system of the squares fails on its own comb; in towers the base has weight `1/d` [KR]; the sections of the first `N` graphs in aligned boxes number the volume over `N!`, with no quadratic term [L*] (AG6). The price path of any `n₀≥2` is monotone, holds on packets of a given length from a threshold on, and on all packets is RH at every parameter [L*] (AG2). Every one-parameter family through ζ in the corpus has the count of its limit or is RH at every parameter [D].

### 1.9 Constituents
No bounded holomorphic Dirichlet series on a half-plane, and no absolutely convergent expansion on a strip about the line, has a zero there with its zeros among those of ξ; a Wiener expansion with an interior zero has nonsummable residues with no purity premise, and no `ℓ^p` family of displacements carries its zeros to zeros of ζ [L*] (CT1). Every box has a Dirichlet polynomial with exactly the zeros of ξ, of unbounded length [F].

### 1.10 Verification
RH is verified through 67; verification through `windowHeight(a)` gives the sign on `[−a,a]` [L*] (VR1). There is `C` such that RH through `exp(exp(C·a))` gives the sign on `[−a,a]` for every `a≥1` [L*] (VH1). The mechanism: a derivative minorant of an interval finds a verified zero within `σ` of every height at which two prime polynomials are not large, such heights fill most of every window, and local sampling at separated verified zeros controls the transform. The constant of the proof exceeds `10⁸`, so the height for `a=1` exceeds `exp(exp(10⁸))` and the verified height 67 gives no window through it [D] (D5). The best margin of a window is at most `K exp(11A/2−πe^{2(A−2)})` [KR]. The proved sign reaches the half-width `181/500` [L*] (SA-j); the absolute cost of the primes stays below the Lévy energy up to a half-width in `(½log 5,½log 6]` [KR].

### 1.11 Law and point
One pointwise theorem holds past the Vinogradov–Korobov region: no zero right of `7/8` [X]. Left of `7/8` every unconditional theorem about the location of the zeros of ξ is in law: twisted moments below the square root; a positive proportion of critical zeros of odd multiplicity from those moments, `κ=(1−log(18/5)/(13/10))/4` [L*] (LV1); `67.25%` simple critical zeros in the objects of the imported `Zeta23` [L*] (CN1); the measure of exceptional heights on a rung; the depth sum `Σm_ρ·depth≤CT` [L*] (DS1); the visibility of a bounded near-top cluster without a deep companion [L*] (CM3). Finite relocation of zeros is invisible to quadratic tests of length `o(T²)` [KR]. The other pointwise theorems act on constituents, finite layers, models and regulators.

### 1.12 Receivers are complete; the price of each producer mechanism
| Mechanism | What the corpus proves | Evidence |
|---|---|---|
| Surface, sections, Riemann–Roch (Weil) | identities; no quadratic term in the count of sections | [L*]/[KR] |
| A bounded-below naive height and Tate's limit | RH ⇔ counts on the surviving prime rays; hyperelliptic curves have the count law | [L*] |
| A family with monodromy (Deligne); the tensor-power trick | fixed part; weights `1/d`, `1/h`; all orders of a window moment are sup bounds | [F]/[L*] |
| A Frobenius with zero derivative (Stepanov) | at one prime `p^{11/12}` | [F] |
| A dominant half (Hermite–Biehler); pure objects | index law; sizes on a circle; pure objects are no Dirichlet series over their dominant half | [L*] |
| Dominance in an ultrametric field (Newton polygon) | the Riemann hypothesis for the Goss zeta function; no norm for ξ | [L*] (CG1); [F] |
| Deformation to a known case | price paths: RH at every parameter; mass: floor to the trivial aperture | [L*] |
| A regulator | clock below the form; tower and heat flow with the count of the limit | [L*] |
| Recurrence (Bagchi); normal families | RH ⇔ strong recurrence; zero limits under a finite layer; no bounded constituent | [F]/[L*] |
| Existence of weights (duality) | RH ⇔ feasible weights at every aperture; they converge to `Λ` | [L*] |
| Sizes of the contacts | the trivial aperture; nothing beyond | [L*] |
| Positivity of the prime measure | the line `Re s=1`, by the count `2M≤A` | [L*] (PL1) |
| The count of the integers as a power | fakes above `½`, below `½` from a half-plane | [L*] |
| Mean values | below the square root; a positive proportion on the line; relocation-invariant below the height | [L*]/[KR] |
| Power sums, half-period deletion, Vandermonde on windows; cameras | finite layers on bounded windows; near-top clusters | [L*] |
| Continuation of the reciprocals of a family with a reciprocity identity | the half-plane `Re s>7/8` [X]; in Lean one implication with two estimates, the budget with its floors, the correction | [X]; [L*] |

Consequence [D]: one mechanism is a producer, and it has produced the half-plane `Re s>7/8` [X]. Every other route is a receiver. The step from the half-plane to the line is not among the producers: on every receiver it is RH itself (§2.3), and the producer has the three limits of §1.6 above the line.

### 1.13 What is ruled out
| Mechanism | Verdict | Evidence |
|---|---|---|
| The explicit formula, positivity of the prime measure, Euler products over integer norms or rational primes, linear counting, as a constraint on a finite top layer | every tangent datum is realized | [L*] |
| The Euler product read through the zero configuration; the Euler product over the rational primes with bounded nonnegative coefficients, meromorphy and polynomial growth, without the functional equation | floor `½`; a one-off pair above the frontier of ζ | [L*] (FF1, MD3) |
| A power saving of the integer count as a constraint on the zeros | fakes | [L*] (IF4, IF5) |
| A fake by finitely many edits, by additions alone, or with zero density at `β≤½`; a deletion fake without a real zero on top | none | [L*] (IF1, IF2, IF7, AO1) |
| Positivity of a prime density inside the strip | a compensator exists for every layer | [L*] (PL1, FF6) |
| One-sided floors on windows of one length; windows below the logarithmic radius, at every prescribed radius | models | [L*] |
| A regulator as a source of a sign, a unit gap or an index bound before the limit | below the limit, or the count of the limit | [L*] |
| A certificate other than `Λ`; a pure object with ζ's Gamma factor as a certificate | converge to `Λ`; no Dirichlet series | [L*] |
| Linear statistics, and differentiable functions of finitely many of them, as monotone quantities under projection | excluded to first order | [L*] (FF13, GL1) |
| Replication of a top zero by a normal family of translates | zero limits | [L*] |
| Amplification over the order of a window moment as an independent source | it is a sup bound | [L*] |
| A path of squares as a transport of the sign | RH at every parameter | [L*] |
| A Gauss-sum probe of the published architecture below `13/15` by geometry or row counts; below `5/6` by any Cauchy–Schwarz row sieve, by unitary re-expansion or by reflection–summation words; other orders, more row variables, other conductors; reflected rows through the same twists; multiplicative in place of additive large sieves | budget | [L*] (TB, LP, FG, MV) |
| A generic mean square over a twist family as an input below its half-plane; positive weights in place of `μ` | on the principal twists it is the half-plane; positive weights are not generic below `n/(n−1)` | [L*] (TF1, TF3) |
| The family step with pole-cleared kernels | a false premise for a nonprincipal character | [L*] (FS1) |
| The frame of the probe below `2/3` with its nonvanishing premise | the correction has zeros in `½<Re s<2/3` | [D] (D3) |
| A bounded or Wiener constituent of ξ with a zero | none | [L*] |
| The return transfer as a step from a strip to the line | RH under a strip | [L*] |
| Positivity alone as a 70% census certificate | cost `≥1+3/π²` | [L*] (PC1) |
| Sizes of the contacts beyond the trivial aperture; sections of the square as a source of a sign; a free contact weight, constant, scale or tree length; a per-degree limit in a tower; an own comb; landing from the functional equation with Gamma factor and count; repulsion from Euler products; rigidity of positive continuous prime measures; bilinear statements as parity-sensitive information; a family as a source of purity by averaging; one glued invariant carrier | as recorded | [L*]/[KR] |

## 2.1 Tasks that are just work

Difficulty is established only where a known argument exists; `(unverified)` marks the rest. None of these decides RH.

### The half-plane `Re s>7/8` in Lean
The theorem is [X]. The items are its steps that the Lean graph lacks; A138 collects its corollaries.

| # | Task | Routes | Basis |
|---|---|---|---|
| A118a | the full arithmetic Poisson series of the probe, its continuation, and the removal of the cube sum in the comparison with the corrected signal | JAS, MC, S3 | `zetaZeroAbscissa_le_of_two_reciprocal_estimates`, `exists_cutoff_zetaZeroAbscissa_le_of_probe_estimates` (FS2, FS6); the principal row and the local factors (FS4, FS5) |
| A118c | the comparison saving uniformly in the ray class character | — | `heckeHalfPlane_of_family_reciprocal_height_estimates` (FS2) |
| A118d | the direct bound: reflection of the completed theta row; the sextic large sieve over `ℤ[ω]`; the zero detector with its bins | — | the quadratic sieve `sieveNorm_sharp` (QS1); the second Poisson reflection of a pair of rows with its transfer to child energies, `full_uniform_integrated_fixed_second_mode_transfer` (SR1); planar and Eisenstein large sieves [F]; budget (TB) |
| A118-I | a first native half-plane: the boundary `11/12` of the balanced design without slots [D] | — | `positiveFormBoundary_six_one`, `lowBoundaryDesign_one_six` (FC3) |
| A138 | The corollaries of `Θ≤7/8` as unconditional statements: the rung `κ<4/3` for the centred contacts, positivity on large primes above the level `11/8`, return bounds `log t≥c·y^{1/8}`; the return transfer ⇔ RH with no premise; every member of the seven-way equivalence; `Θ∞≤7/8`; the ringdown rate `1/16` and the horocycle exponent `≥9/16`; the signal bound for every `b>7/8`; the convergence of the power tails for `a<1/8`; a fake at `½−1/512`; the index of the degree-two Artin character of `X³−2` counts zeros in `(½,7/8]` | every route that reads the scale | SA-d, FC2, QR1, FC1, RD1, PT3, IF5, AR1–AR3 |
| A139 | the identity `H_η=L^S(6s−3,ψ₆η⁶)E_η`, the absolute convergence and nonvanishing of `E_η` on `Re s>½`, and the zeros of `H_η` in `½<Re s<2/3` (unverified) | JAS, MC | `principalLocalFactor`, `norm_principalLocalFactor_sub_one_le` (PC2, PC3) |
| A141 | the half-plane [X] for number fields containing `ζ₃` and, by base change to `K(ζ₃)`, for every ray class character of every number field; the index of every such character then counts zeros in `(½,7/8]` (unverified) [C] | ACS, HF | the family step for every number field (FS2); the index law (AG3) |

### Assemblies of proved pieces
| # | Task | Routes | Basis |
|---|---|---|---|
| A142 | The verification rate: a constant `C` of ordinary size in `exp(exp(C·a))` | RW, SRT, TH, LI, HCF | `exists_doubleExp_windowPositive` (VH1) |
| A143 | The sign of `𝔚_4` and of `𝔚_7` on step packets as certified finite statements with a margin (unverified) | ACS, HF, RW | `le_combForm_of_packetForm_ge`, the ratios 4 and 7 (SP2, SP3) |
| A140 | The sign on windows of half-width below `½log 5`: the range in which the kicks of `{2,3,4}` cost less than the Lévy energy (unverified) | RW, ACT, EWU, OWU | the edge cost and the `991/1000` bound [F]/[KR] |
| A144 | The tangent data of `μ` and `λ` under additive twists (unverified) | ZCG, MC | `tangentDatum_mobius` (TD1) |
| A145 | The index law for Artin characters beyond the monomial case (unverified) | ACS, HF | `exists_le_negIndex_artinGram_iff` (AR3) |
| A136 | Integration of the modules graded [S]: the reduction of the logarithmic correlations of `λ` to their prime dilates; the box cameras | — | frontier map; (LC3, BC1, BC2) |

### Finite verification and explicit constants
| # | Task | Routes | Basis |
|---|---|---|---|
| A1 | Certified `RHVerifiedThrough T` past 67 | all rungs | `rhVerifiedThrough_sixtySeven` |
| A2, A3 | Numeric values of the explicit heights; membership on the first windows | window routes, TH, LA, HCF | explicit definitions |
| A4, A5 | Theta rank 15 and beyond; certificate of the center-tail failure (unverified) | TH | height 67 |
| A6, A7 | Cone widths; certificates on the anti-diagonals (unverified) | CHT, ACT | convex programs |
| A9, A13 | Constants at the eighth-root horizon; near-gcd charges (unverified) | HF, AIP | proved limits |
| A117 | End points of the feasible interval of `w(2)` on the first selective window | RW, ACS | `poleFeasible_of_abs_sub_le` |
| A19 | An explicit height for the heat horizon | ZCG | existence of the horizon [F] |
| A48, A58 | Hasse–Weil tests at verified scales; effective gap iteration (unverified) | ACS | window rungs |

### Classical inputs to formalize
| # | Task | Routes | Basis |
|---|---|---|---|
| A18 | Twisted second moments past the square root [C] | WD, MC | `θ<½` in Lean (TM1) |
| A21 | Logarithmic two-point Chowla [C]: the mean of the correlations `c(ph)` over the primes of a scale | MC | logarithmic averages, limit functionals, entropy decrement; `exists_scale_corr_close`: `\|c(h)−avg_{p∈𝐏_k}c(ph)\|≤6ε` at infinitely many scales (LC3) [S] |
| A26 | Weyl asymptotic `N(Λ)∼Λ/12` [C] | PM | the order `Λ` [F] |
| A33 | Fourier coefficients of the cubic residue at all heights [C] | MC, MMD | formulas for `Re s>2` [F] |
| A41 | Count law for every curve over `𝔽_q`, first case plane quartics [C] | ACS, PM | `hyperelliptic_spanDefect_is_count` |
| A120 | A finite nonempty stratum with both structures: Selberg zeta functions of surfaces with a small eigenvalue [C] | BAG, ZCG | `selbergSmallEigenvalue_offCritical` (log §5) |

### Further items
A16 numerical `r,m,q`; A20 a Jensen rung toward the saddle scale; A24 certified scans; A28 reciprocal-quadric traces; A30 best stencil exponent under RH; A42 Gamma-weighted transport to the adaptive head; A46 singular indices; A54 cusp expansion for Bianchi resolvents (all unverified).

## 2.2 Open mathematical obstacles

**Strength** as in [route-obstacles.md](route-obstacles.md). `≥qRH` marks a statement that implies a zero-free half-plane, Lindelöf or ZAL. The half-plane `Re s>7/8` is a theorem [X]: an item of that strength is open where it gives a half-plane below `7/8`, or where it is not known to follow from [X].

### The common minimal face
| # | Problem | Strength | Routes |
|---|---|---|---|
| B130 | `P(p)≤A(p)+K`, or the upper bound of the trace, on the primes of arbitrarily late logarithmic windows; any growth `Kp^σ`, `σ<½`, is a zero-free strip | RH (≥qRH) | ACS, SRT, WL, HF, ZCG, HAT-C |
| B159 | A rung `κ≥4/3`: a power saving of ζ's contacts on the integers between `m` and `m^{2κ}`, uniform in the height, that fails for the Liouville twist. For the centred contacts the rungs `κ<4/3` hold by [X]; in Lean no rung above one | a half-plane below `7/8` | every sign route; BAG |
| B144 | Separation of the deep off-line ordinates of ζ | sub | SRT, ACS |

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Weil's sign on every window; equivalently the fixed-height energy floors | RH | all sign routes, HAT-C |
| B152 | The sign on step packets, in any of its finite-scale forms | RH | ACS, HF |
| B160 | `JasDressedPSD 1` | RH | JAS |
| B18 | A construction of feasible weights at every aperture; every system feasible at a large aperture is within `ε` of `Λ` at each fixed `n` | RH | RW |
| B2, B4, B5 | Bounded oscillation of `Ψ` to contact (no null mode at any aperture); outer predictors and Schur bands; kick admission | RH | RW, GWZ, WTZ |
| B6, B8, B101 | Full-space sign at every critical multiple; head thresholds; polar payment at every ratio | RH | HF, SRT, AIP |
| B104 | Polar orthogonality at the critical curve: whether a critical half-line ground state at finite `W` can be orthogonal to the polar source | method | HF, SRT, AIP, ACS, SC |
| B123 | Correlated arithmetic pairings dominating the depleted kernel | method | HF |
| B156 | Arithmetic cluster exclusion on a rung for ζ | method | SA, RW |
| B9–B11 | No zero mode; top coprime stratum; exact SOS on a two-prime lattice | RH | HF, SC, ACS |
| B12, B14, B23 | Index ceiling uniform in resolution; any interior width value; `N_d` bounded | ≥qRH | CHMD, LA |
| B15 | Pointwise savings past Vinogradov–Korobov in the Lean graph | sub | every route |
| B16, B17, B3 | Decay law of the margin; signed ground states past `log ρ`; variation of `r` free of `1/μ` | sub / method | CHT, RW |
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
| B161 | The signal bound `O(Z^b)` for some `b<7/8`: equivalent to `Θ≤b`. For every `b>7/8` it is a theorem [X]; in Lean no `b<1` is proved | a half-plane below `7/8` | JAS, MC |
| B174 | The row count of the binding bin: the number of sextic twists marked in the bin `δ=79/204`, below the published `U^{21766/32589}`; with the count `1−δ+η` the twist exponent is `((5+6η)n−8)/((5+6η)(n−1))` (§2.4) | a half-plane in `[13/15,7/8)`; density type | JAS, MC |
| B175 | Signed cancellation across the rows of the floor bin for the actual coefficients: a row exponent `R₀<1`; below `5/6` a bilinear saving taken before Cauchy–Schwarz (§2.5) | producer; a half-plane below `13/15`, below `5/6` | JAS, MC |
| B184 | The frame below `2/3`: a form of the probe that reads `L(s,η)` alone, or a common half-plane for the tower `ψ₆^kη` whose `L`-functions are the corrections (§3) | method; a half-plane below `2/3` | JAS, MC, every graded receiver |
| B180 | The reflection of the completed theta row without Eisenstein series (§2.11) | method | JAS, MC |
| B48–B54 | Deciding input at square-root precision; endpoint energy; trivial-gauge half power; moving power windows; rows and BSY; regularized partial sums; extremal inequality | RH | WL, MC, SQF, JAS, CTF, PBM, RB |
| B55, B67 | Polynomial stencil rate; parity at power saving | ≥qRH to RH | WL, MC |
| B56 | `Θ<1⇒Θ=½`; with `Θ≤7/8` [X] it is RH | RH | whole programme |
| B57 | Depth density `o(T)` | sub | WD, CTF, MC, RW, PM |
| B58–B61 | `D_win`; cluster wall; Green moments at deep zeros; a detector past the last scale | sub | WD, MC, ZCG |
| B62, B63, B66 | Cofinal long moment; collision charge; near-unit holomorphic budgets | RH | WD, CTF, AIF |
| B91 | Cut-kernel mass | RH | RAC |
| B46, B97, B121, B137 | Proportional saving at length `(log X)^{2K}` at all heights (for `K>8` from [X] [D]); first return past the VK rung; freezing beyond the cap; collective depth floor | sub | BAG, PTT, TAPO, TTPO, CDGeo |
| B106 | A correspondence on the orientation cover with bounded local indices | RH | MC, HAT |
| B110, B126, B127 | Thick crude count; a one-sided bound on a sampling set; positive-measure lag recurrence | AAL | WL, ZCG, ACS, IWT |
| B145 | The signed, prime-weighted centred type-II current, with both continuum terms, at a growing isolated mode (§2.6) | AAL [D] | ZCG, BAG, ELT |
| B148 | The return transfer | RH: the equivalence holds under `Θ<1` [L*] (FC2), which is [X] | S3, BAG |
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
| B183 | A fake with a count `Ax+O(x^β)`, `β<½`, and no real fake zero: a two-sided edit of the rational primes, some deleted and some doubled, with one non-real pair on top (§2.10) | method (a construction); the negative side is of GRH type | WL, MC, BAG, ZCG |
| B89, B112, B128 | A bounded aligned return at each right zero; the functional equation into vertical transport; replication by a mechanism other than normal families | sub | BAG, ZCG, EFT |
| B68, B71 | Reflection Krein positivity, flux, dispersion; universal decay and the horizon rates | RH | PM |
| B69 | A prime-faithful lossless stack for the cosine producers | producer | PTR |
| B72–B76 | Cutoff-uniform target mass; the candidate zero-parameter conditions; FE-pair reality | RH | BAG, candidates, ZCG |
| B80, B81 | FE twins in the full class; candidate landings | sub; producer | SEL; candidates |
| B86 | Endpoint character positivity at unbounded rank | RH | ECP, ACS |
| B87 | A nonnegative count on the rays `Γ_1+Γ_p`, defined without `Q` | RH | ACS, HF, PM |
| B88 | The sign of the comb finite part | RH | HF, ACS, HAT, AGZ |
| B114, B117 | A realization of the partner involution outside the excluded classes; a regulator with a sign, a gap or an index bound before the limit | producer | PM |
| B147 | Shimura nonvanishing at `ρ/4+¼` for one Hecke eigenform | indep. | PM |
| B178 | A relaxation rate beyond the tempered exponent `½` for a horizon with a cusp, from a principle of the horizon and with no family of twists (§2.7) | producer, independent of [X] | PM |
| B149, B169 | Bézout for the comb pairing from a property of the object; a group with a doubling on which the defect is a canonical height | RH (producer) | ACS, HF, AGZ |
| B172 | A functional of the zero configuration that decreases under projection to the line and is not a differentiable function of finitely many linear statistics | producer | ZCG, HF |
| — | ZAL | ≥qRH | whole programme |

### Settled questions
| # | Question | Answer | Evidence |
|---|---|---|---|
| B176, A132 | The cost of a window | double exponential: RH through `exp(exp(C·a))` gives the sign on `[−a,a]`; the constant is of size `10⁸` | [L*] (VH1) |
| B177 | The least exponent `θ` of a twist family with a generic mean square of the Möbius sums | on the principal `n`-th-power twists `(n/(n−1))(2Θ−1)`, attained, zero iff RH; for the Jacobi family zero iff RH and GRH for the quadratic twists; positive weights are not generic below `n/(n−1)` | [L*] (TF1–TF4) |
| B182 | The least remainder of the integer count of a fake among discrete systems with integer norms | fakes at every `β>½`; from a half-plane of ζ below `½`; under RH every `β>⅓`; natively `Θ=1` (with AAL) or a fake below `½`; none by finite edits; positive density at `β≤½`; a deletion has a real zero on top; the infimum lies in `[0,½]` | [L*] (IF1–IF8) |
| B158 (budget form) | The boundary of the order-`n` probe | the table of §1.6 | [L*] (TB, LP, FG, MV) |
| B169 (path half) | A Lefschetz path at an odd prime | the price path exists at every `n₀≥2`, and on all packets it is RH at every parameter | [L*] (AG2) |
| B148 (strength) | The return transfer | RH gives it; under `Θ<1` it is equivalent to RH, and `Θ<1` holds [X] | [L*] (FC2); [X] |
| B94, B181 | The cubic theta identification; the comparison estimate at `7/8` | theorems [X]; their Lean steps are A118a–d | [X]; [F] |
| quasi-RH | Whether `Θ<1` | `Θ≤7/8`; `Θ∞≤7/8`; the world `Θ=Θ∞=1` is excluded | [X]; [L*] (AT2) |
| B156 (configurations) | Whether the sign at an aperture is a strip | no: deep zeros at ζ's density with positivity on `[−a,a]`, for every `a` | [L*] (SA-f) |
| B117 (the three regulators) | Whether the clock, the tower or the heat flow supplies a sign or a gap before the limit | no | [L*] (FF11) |
| B172 (first order) | A linear statistic, or a differentiable function of finitely many, monotone under projection | the gradient symbol vanishes on the line | [L*] (FF13, GL1) |
| B153 | A bounded or almost periodic constituent of ξ with a zero | none | [L*] (CT1) |
| A133 | An Artin character of a non-abelian extension | the index law for the degree-two character of `X³−2`, through the cubic character of `2` over `ℚ(ω)` | [L*] (AR1–AR3) |
| A135 | The step-packet matrices at finite scale | explicit block error; transfer of a margin in both directions; the ratios 4 and 7 written out | [L*] (SP1–SP3) |
| A134 | A proportion of critical zeros from the native twisted moments | `κ=(1−log(18/5)/(13/10))/4` at the length `U^{13/50}` | [L*] (LV1) |
| A137 | The tangent data of `μ` and `λ` in world I | residues at the top zeros; leading numerators differ by `ζ(2ρ)` | [L*] (TD1) |
| A89 | A prescribed radius in the sub-logarithmic model | every nonnegative `R=o(log T)`; one configuration for all radii `≤(C/256)log log T` | [L*] (SL1, SL2) |
| A115 | The Newton polygon of the Carlitz–Goss zeta function | the Riemann hypothesis for the Goss zeta function at `z∈ℤ_p∖ℕ` | [L*] (CG1) |
| A59 | Short-interval primes in a residue class | every interval `(x,x+x^θ]`, `θ=1−1/(16(14·10⁷+12))` | [L*] (SI1) |
| A118b | The corrections `H_η` | holomorphic and nonvanishing right of `2/3` (principal) and of `7/8` (probe), bounded on `Re s≥2` | [L*] (FS3, FS6) |
| A80, A114, A82, A94 | The converse at finite scale; the limit matrices on step packets; the Li ladder as comb forms of tails; the unshifted index | equivalences and limits | [L*] (AG5, HF1, HF3, HF4) |
| A102–A105, A108, A113 | The ladder as one statement; exceptional heights; deep zeros under a rung sign; the first conductor rung; the additive gap `log(π/2)`; the map under a half-plane | theorems | [L*] (SA-a–SA-g) |
| A109, A121, A123–A131 | The normalized prime error; non-attainment and moments; floors; the unit gap; regulators; the tangent datum; feasible sets as positive measures; pure objects; projection; amplification | theorems with their kills | [L*] (FF1–FF14) |
| A112 | The positivity ceiling of the 70% certificate | cost `≥1+3/π²` | [L*] (PC1) |
| A116, A119 | Ideals as degree points; the depth sum | exact index for Dedekind zeta functions and class characters; `Σm_ρ·depth≤CT` | [L*] (AG3, DS1) |

## 2.3 Frankenstein routes

**No assembly closes RH.** One assembly is a theorem: the two estimates give `Θ≤7/8` [X]. Every other assembly has an open input of RH or AAL strength, an input that is a half-plane below `7/8`, or returns an identity. No assembly reaches the line from the half-plane: the corpus has no reduction from a half-plane to the line that is not RH itself [L*] (FC2, JA1).

| # | Parts | What the assembly gives | Missing input | Gain |
|---|---|---|---|---|
| F29 | **One scale.** Level of the dressed aggregate; signal exponent; rungs; mollifier depth; window moments; floors; twist exponent; power tails; ringdown | every graded receiver is one number [L*]; the level `b=7/8` is proved [X] | a level below `7/8`; in Lean a level above the trivial one | a proposed estimate is placed on the scale before work starts |
| F30 | **Two estimates.** The family step with reciprocal kernels; the probe's correction; the cube identity; the Poisson coefficients; the quadratic sieve; the budget | `Θ≤7/8` [X]; in Lean `Θ≤σ₀` from a direct and a comparison bound, for `7/8≤σ₀<1` with the probe's correction [L*] | in Lean A118; for `σ₀<7/8` the chain B174, B175, B184 | the half-plane is one Lean implication away from the native graph; its limits are `[13/15,7/8]`, `5/6`, `2/3` |
| F31 | **Half-plane, then line.** `[X]`; level and signal; return transfer; three rungs | with `b=7/8`: rung `κ<4/3`, level `11/8`, return bounds; the return transfer ⇔ RH [L*] with [X] | a step from the strip to the line: the transfer and level one are RH | none: no assembly crosses from `7/8` to `½` |
| F32 | **Finite scale.** Step packets with explicit block error; ratio windows; robust index; index jumps | RH ⇔ sign of explicit finite matrices; a matrix margin at one ratio transfers to the comb at every block size past an explicit threshold [L*] | the sign of the matrices (B152); exclusion of a null mode at every aperture (B2) | one exact object in finite rank at each scale, with certified transfer |
| F33 | **World I off the scale.** Non-attainment; unit gap; quantum; four sectors; filters; currents; tangent data of `μ`, `λ` | AAL from any receiver form; a complete description of the tangent datum [L*] | B170; or B145 | every form fails on the one-structure models: a proof has to use the exact count or the functional equation |
| F35 | **The necessity calculus.** Fakes; add-only systems; the meromorphic Euler firewall; positivity on the line of the pole | what a proof of AAL cannot be built from: positivity, Euler products with real weights in `[0,2]`, integer norms with a count rate (for a real top) [L*] | the model with a non-real pair on top and a count rate (B183) | a proposed argument for AAL is tested on the models before work starts |
| F36 | **The lattice with a level.** The index law for Hecke and Artin characters; [X]; base change | for the degree-two character of `X³−2`: zero-free in `Re s>7/8`, index = zeros in `(½,7/8]` [D] with [X] | A141 for every number ring | the index of every comb counts zeros in one strip |
| F37 | **Verification with a rate.** Verified height; derivative minorant; local sampling; step packets | a window sign from a height of double-exponential order [L*]; a certified matrix margin would give the comb sign at explicit block sizes | a usable constant (A142); a certified margin (A143) | the rung ladder has a rate; the first selective windows are finite statements with stated sizes |
| F38 | **Mean values on the line.** Twisted moments below the square root; the Levinson gate; cameras; depth sum | a positive proportion of critical zeros natively; visibility of isolated near-top clusters [L*] | length past the square root (A18); the cluster wall (B59) | the in-law half of the near-line picture is native |
| F2 | **One inequality per prime**, with upper side, counts, moments | Σ, Π and count readings are one number per prime on sparse windows [L*] | B130 on one sequence of windows | one target |
| F11 | **Construct, then identify.** Index semicontinuity, unit gaps, rigidity | an approximant with a gap gives RH [L*] | B146, B171 | regulators of the corpus are excluded as approximants |
| F6 | **Regulators.** Clock, scattering tower, heat flow | RH ⇔ the energy floor at one fixed height [L*] | B88, B117 | one fixed finite height suffices |

**Closest to the open core: F30 (the one producer; its exponent and its frame are the open part), F33 with F35 (the only target off the scale with a complete receiver and a model theory), F32.**

### What a contradiction search may assume in world I
`Θ≤7/8` [X]; attained isolated top `β≤7/8`; `M(x)=O(x^{β′})`, `β′<1` [L*] (AT4); `ψ(x)−x=O(x^β)` attained in absolute value on every late multiplicative window and at the primes of every late window [L*] (FF3); the Gaussian window sums of `μ` and `λ` equal their top residues up to `o(e^{Θu})`, with leading numerators related by `ζ(2ρ)` [L*] (TD1); quantized multiplicities [L*] (FF7); every bounded normalization of translates along a phase return tends to zero [L*] (FF8); a nonzero Euler filter accelerates the horocycle rate [L*] (log §4.8); with finitely many off-line zeros the packet index is finite and positive [L*] (AC1); level-one dressed positivity fails [L*] (SA-h). No contradiction comes from exact identities alone, from positivity, Euler products over integer norms, integrality or a count rate alone, from the functional equation with ζ's Gamma factor and count, from a regulator, or from any statement in law [L*].

## Validation tests for 2.4–2.8 and 3

| Test | Requirement |
|---|---|
| T1 | Implied by RH, or by GRH for the family at hand, and implying neither RH nor AAL; or a method question implied by nothing about ζ's zeros. A half-plane below `7/8` satisfies T1 |
| T2 | Answered by proving or refuting a stated inequality, identity or implication |
| T3 | A named consequence for either answer |
| T4 | Not decided by a finite rung |
| T5 | False on a corpus model, or calibrated on the models |
| T6 | Names an input not refuted in Lean |
| T7 | Moves a wall; not a shape answered in Lean |
| T8 | Not a named long-standing problem in disguise; a first step in corpus objects with one named obstacle |

**No statement about the zeros of ζ below RH and AAL passes all tests as a door to the line.** Quasi-RH is a theorem [X]. What is open below RH and AAL on the scale is the exponent, and the one producer has three limits above the line (§1.6): a density count (§2.4), a signed estimate (§2.5) and the reach of its frame (§3). A statement off the scale is of one of the kinds of §1.5, each with its kill; the structural questions that had a first step are answered (§2.2, settled). Every question below was checked against the corpus by sentence queries (log §5).

## 2.4 Breakthrough question below RH: does the half-plane move?

**Position.** One pointwise theorem about the zeros of ζ holds past the Vinogradov–Korobov region, and it is a vertex of the estimates of its proof [L*] (TB). Every receiver of the scale reads its level: the rung, the level on large primes, the return bound, the ringdown rate, the power tails, the fake exponent, the strip in which every comb index counts (§1.2, A138).

**What is in Lean.** At the published geometry the boundary is `θ=9/10`. In the bin `δ=79/204` no geometry reaches `θ≤9/10−6/6250` as long as the row count is at least `21766/32589−10⁻⁴` [L*] (TB). With a row count `1−δ+η` the boundary is `θ=((5+6η)n−8)/((5+6η)(n−1))`: it interpolates between `22/25` (`η=0`, the count of the density hypothesis) and `9/10` (the published excess) [L*] (FG). With the count `1−δ` in every bin the geometry `(2/5,2/5,1/5)` attains `13/15` [L*] (TB).

**Question (B174).** *Is the number of nonprincipal sextic twists of norm up to `U` that the zero detector marks in the bin `δ=79/204` at most `U^R` with `R<21766/32589−10⁻⁴`?* It is a zero-density count for the family of the twists.

| Answer | Effect |
|---|---|
| a count below the published one in the binding bin | `Θ≤σ₀` with `σ₀<7/8`: the first motion of the exponent; every receiver of A138 moves with it |
| the count `1−δ` in every bin | `Θ≤13/15`: the rung `κ<15/11`, the level `41/30` on large primes, the ringdown rate `1/15`, tails for `a<2/15` [D] |
| below `13/15` | not by a count: trivial summation of the floor bin stops there for every count (§2.5) |

**First step and obstacle.** The statement of the row count of [X] in the binding bin as one inequality for the witnesses of that bin, beside the budget; it needs the zero detector of A118d. Named obstacle: the count comes from a sextic sieve whose optimal form has the floor `26/27` on the reflected side [L*] (TB); a smaller count needs a density argument that is not a large sieve, or a sieve restricted to the witnesses of the bin.

**Tests.** T1: passes: implied by GRH for the sextic twists; a half-plane in `[13/15,7/8)`. T2, T4: pass. T3: fails: the question is one-sided; a negative answer would contradict GRH for the twists. T5: calibrated on the vertex, on the interpolation in `η`, on the floor geometry. T6: pass. T7: moves Π163 inside its room. T8: a zero-density estimate for a family of Hecke `L`-functions, of classical type [A].

**Limit.** The best outcome is `13/15`. The question does not lead to the line.

## 2.5 Breakthrough question for the search for a producer: is there signed cancellation across the rows?

**Position.** The search has closed classes. Off the scale: the kinds of §1.5. On the scale: sizes (rung one), mean values (in law), regulators and paths (count of the limit, or RH at every parameter), counts (fakes). One class is a producer: a completed sum with a direct bound and a comparison with its signal. Its conversion from a law to a point is that the target occurs among its own twists [L*] (FC3); a mean square over a family that contains its principal twists is the half-plane itself [L*] (TF1). Everything this class does with squares is mapped: for every Cauchy–Schwarz row sieve, every geometry, every reflection–summation word and every unitary re-expansion the twist exponent is at least `(n−2)/(n−1)` [L*] (MV); with matched phases the signed Gram of the rows is as large as the trivial bound [L*] (FG). Among the orders `n≥6`, which contain the covers of odd order, the sextic design has the least corner [L*] (LP).

**What is in Lean about the crossing.** Interchanging the row and the column sum before absolute values bounds the bilinear floor sum by the column energy times the exact signed Gram form of the rows, diagonal plus the real part of the off-diagonal [L*] (FG). With a row exponent `R₀` in place of `1` the floor is `((6R₀−1)n−8)/((6R₀−1)(n−1))` for `R₀≥½+1/n` [L*] (FG). Below the free floor the boundary is `1−1/n−s` with `s` a saving taken before Cauchy–Schwarz: `¾` needs `s≥1/12`, the line `s≥1/3` at `n=6` [L*] (MV).

**Question (B175).** *For the actual coefficients of the probe — the amplitudes of the reflected rows and the Möbius weights of the columns — is the off-diagonal of the signed Gram of the floor bin negative of the order of the diagonal: is the row exponent `R₀<1`, and is there a positive saving `s` before Cauchy–Schwarz? Or do the actual amplitudes align with one column, as matched phases do?*

| Answer | Effect |
|---|---|
| `R₀<1` | a boundary below `13/15`: the first estimate of the producer that is not a square |
| `R₀≤5/6` and `s>0` | a boundary below `5/6`: the class is not capped by its squares; the thresholds `1/12` (`¾`), `1/6` (the wall of the frame), `1/3` (the line) measure the rest |
| the actual amplitudes saturate | half-planes through reflection, slots and sieves end at `13/15` (at `5/6` if only `s=0`): every graded receiver keeps `[X]` as its only level from this producer, and RH needs a statement off the scale or a different source |

**First step and obstacle.** The signed Gram of the floor bin at the geometry `(2/5,2/5,1/5)` with the actual kernel: the off-diagonal entry of two rows is a column sum of a product of two residue symbols, whose conductor exceeds the column length; after Poisson summation in the column it is a sum of the Poisson coefficients that are in Lean (FS5). The arithmetic of such a pair is in Lean as an identity: with the two Möbius signs the mixed Gauss factor of disjoint prime sets is a quadratic symbol of the residues modulo 4 times a column factor of each set, so the pair is a sum over the residue classes of separated pairs; what follows the identity in Lean is a weighted Cauchy–Schwarz inequality over the outer tuples, with the two child-row energies on the right [L*] (SR1). The first step is the outer sum of the separated pair without that inequality. Named obstacle: the completed sum of a pair of rows is the full arithmetic Poisson series, the same object that A118a lacks; every bound of it by a large sieve returns to a square.

**Tests.** T1: passes as a half-plane below `13/15`; it is not known to follow from GRH for the rows. T2–T4: pass. T5: calibrated on matched phases (saturation), on `μ²` (not generic below `n/(n−1)`), on the principal twists (circular). T6: pass: saturation is proved for chosen amplitudes, not for the actual ones [KR]. T7: moves Π163 below its floor bin and Π167. T8: bilinear forms with Gauss sums of order six with cancellation, of classical type [A]; the first step is in corpus objects.

**Limit.** A saving of any size is a half-plane; the frame of the probe has its own wall at `2/3` (§3).

## 2.6 If positivity, Weil positivity and spectral methods are excluded

"Spectral" is read as spectral theory of operators in every form, automorphic spectral theory included; "positivity" includes nonnegativity of forms, kernels, counts, coefficients and averaging measures. Kept: Fourier analysis, mean values used as bounds, exponential sums, Poisson summation, absolute convergence, continuation, power sums, integrality, recurrence, the argument principle, dominance in ultrametric fields.

**What the corpus says about the premise [L*].** Positivity of a prime density reads the line of the pole and nothing inside the strip (PL1, FF6). A system that only adds primes vanishes at its real abscissa; a deletion has a real zero on top (AO1, IF7): the Landau mechanism locates real singularities only. Positivity alone does not certify 70% of the zeros (PC1). One Riemann hypothesis in the corpus is proved with no sign: the Goss zeta function, by strict log-concavity of coefficient norms in an ultrametric field, where a sum has the size of its largest term (CG1).

**What survives.**
- *Receivers.* RH ⇔ the absolute value of the trace is bounded at the primes of arbitrarily late logarithmic windows (MF9); ordinate injectivity [F]; the exponent of the signal (FC1); convergence of the power tails (PT3). For AAL: two-sided non-attainment, the unit gap by the argument principle, the quantum of a multiplicity (FF2, FF3, FF7).
- *Conversions.* Recurrence against density and prime contraction (no bounded constituent); half-period deletion; power sums on a cluster (cameras); sizes on a circle (CT1, CM1).
- *Identities.* The Jacobi-sum sign law; the reciprocity laws and Poisson coefficients of the probe, proved in Lean by Gauss sums and Poisson summation (FC4, FS5).

`[X]` under the constraint [A]: its identity is algebraic and its sieves are bounds; the reflection of its completed theta row is known through Eisenstein series on a cover [C]. Under the strict reading the half-plane `Re s>7/8` is not available. The floor `5/6` of §1.6 is a floor of squares: what crosses it is, by its definition, an estimate taken before Cauchy–Schwarz. The constraint and the second limit of the producer ask for the same thing.

**An observation that frees one tool [D].** `Σλ(n)Λ(n)n^{−s}=ζ′/ζ(s)−2ζ′/ζ(2s)` has in `Re s>½` the pole at `1` and poles exactly at the zeros of ζ. So the top layer of `Λ` and of its Liouville twist coincide, and AAL is invariant under the twist; in Lean the tangent data of `μ` and `λ` have the same support and degrees (TD1). The parity blindness of bilinear statements is therefore no obstruction to AAL, while it is one to every sign.

**Question (B145).** *Does the prime-weighted centred type-II current at a growing isolated mode cancel below the recovered residue?* Proved: under ¬AAL filters recover the top residues; the growing-order Gaussian current reduces to centred type-II cofactors with a filtered error `≤2h^d exp(−at/8)` [L*] (EL1); the unweighted near-diagonal row is summable [F]. Open: the cofactor sum with the prime weights, keeping both continuum corrections.

| Answer | Effect |
|---|---|
| Yes | AAL with no sign of a form and no operator; then RH ⇔ ZAL |
| No: a lower bound for the current of the size of the residue | the Vaughan–Gaussian architecture does not exclude a finite layer; world I needs an input outside exponential sums |

**Tests.** T1: fails as a question below AAL; it is of AAL strength [D]. T2, T3: pass. T5: it has to fail for Euler products over natural norms with a finite layer, for the firewall and for the fakes; it does where the proof uses Poisson summation with `O(1)` remainders [D]. T7: moves Π149. T8: a Type II sum in the dark range [A]; the first step exists (the unweighted row), the obstacle is the prime weight.

**Limit.** Under the constraint the step from AAL to RH is ZAL, a half-plane at every depth; its sign-free source is the probe with an elementary reflection (B180) and with estimates that are not squares (B175), and that source stops at the wall of its frame (§3).

## 2.7 If RH is a physical phenomenon in AdS with a modular horizon

**What is proved [L*]/[F].** The resonances of the modular horizon are the zeros of `ξ(2s)`. A zero-free strip `Re ρ≤1−2δ` ⇔ every compact pulse decays like `e^{−(δ−ε)τ}`; RH ⇔ the quarter rate (RD1) ⇔ positivity of the reflection Krein forms ⇔ one cavity energy decays at `y^{¾−ε}` [F]. The supremum of the universal horocycle exponents is `1−Θ/2`; with a nonzero Euler polynomial filter `P(y d/dy)` it is `1−Θ∞/2`, and no filter passes `3/4`; ZAL ⇔ filtered rates approach `3/4`; AAL ⇔ no filter accelerates (log §4.8). Every regulator of the corpus has the count of its limit (FF11). At every fixed scattering height the energy floor is RH (HA1). No Maass cusp form of a congruence group `Γ(N)` has `0<λ<3/16` (SG1). With `Θ≤7/8` [X]: the rate `1/16` and the exponent `9/16` [D].

**Readings [D].**
- *World I is ordinary ringdown, and it is removable.* A finite top layer is a finite set of least-damped modes; a differential filter of degree twice their number removes them from every pulse. AAL says that no finite filter helps.
- *World II is a tail.* Modes approach a rate above the symmetric one and no filter reaches `3/4`.
- *RH is a saturated bound.* The symmetry of the resonances bounds the relaxation exponent by `3/4`; RH says the bound is attained.
- *The exponent `½` is the wall of every `L²` principle.* The unconditional exponent is `½`, the value at `Θ=1`. A horizon without complementary series has mixing at the tempered rate `y^{1/2}` for square-integrable observables [C]; a pulse at a point of the horizon and a closed horocycle are not square-integrable, and their rate beyond `½` is carried by the excursions into the cusp alone.

**Question (B178).** *Is there a proof, from a principle of the horizon and with no family of twists, that compact pulses on a cusped arithmetic horizon relax at a rate beyond the tempered exponent `½`: any `δ>0`?* A rate `δ` is the half-plane `Θ≤1−2δ` (RD1); `δ=1/16` is [X].

**What the corpus says about the candidates.** A Hölder dynamical realization of ζ gives a zero-free strip, and the oscillation estimate fails on additive realizations of the prime lengths [KR]. Graph horizons with commuting Hecke operators and slow resonances exist [KR]. Positive KMS horizons, internal modular conjugation and half-sided inclusions do not select the line [KR]. Under deformation of the group, cusp forms are expected to dissolve into resonances near the unitary axis [C]: a principle that holds for every cusped surface of the same area is false.

| Answer | Effect |
|---|---|
| a rate `δ>0` from the horizon | a second producer, independent of the twist family; `δ>1/16` is a half-plane below `7/8` |
| a cusped model with the same local dynamics and resonances approaching the axis, in Lean | the rate `1/16` is a property of the arithmetic and not of the horizon; the physical reading supplies receivers and no source |

**Tests.** T1: passes as a half-plane when `δ>1/16`; below it is a second proof of a theorem by another mechanism. T2: passes for the calibration; the principle is a research direction. T5: has to fail on non-arithmetic cusped surfaces and on graph horizons with slow resonances. T8: no first step beyond the two calibrations.

**Limit.** A rate is a half-plane; equal damping is the maximal rate and is not reached by a principle with a margin.

## 2.8 If RH is a problem of topology or geometry

**What is proved [L*].** The pairing of the degree points has a Hodge index theorem equivalent to RH, with exact index the number of right zeros, for ζ, for Dedekind zeta functions, for class characters and for an Artin character of a non-abelian extension (AG3, AR3). Every datum of the pairing is forced; every path through the square of ℤ is RH at each parameter (AG1, AG2). At finite scale the inequality is the sign of explicit finite matrices with an explicit block error (AG5, SP1). The sections of the square count linearly (AG6). The index jumps by the nullity at an aperture (IA1); the unshifted comb index reads it off resonances (HF3). The sign at aperture `a` follows from verification to `exp(exp(Ca))` (VH1) and confines the zeros up to height `2πe^a` to depth `<exp(−c log³\|γ\|)` (SL3): with the lowest off-line zero at height `γ₁`, no aperture below `(1/C)log log γ₁` carries a negative direction, and if its depth is at least `exp(−c log³γ₁)` the aperture `log(γ₁/2π)` carries one [D] (D5).

**Readings [D].**
- *The aperture is a time.* The restricted forms are a path of quadratic forms; the index counts the resonant apertures with their nullities, as a Morse index counts conjugate points; RH ⇔ the path has no conjugate point.
- *The square is one-dimensional for counting.* Its sections count like points of a lattice of rank one per graph.
- *Spec ℤ is not a member of a family.* Constant, contacts, tree lengths, prices, mass: every deformation is forced or returns RH.

**Question (B179).** *Is the index of the comb a Maslov index: is there a symplectic space and a path of Lagrangian subspaces, defined from the places without the zeros, whose crossings with a fixed Lagrangian are the resonant apertures with their nullities?* The corpus has the scalar flow of the chain (`L`, `q`, `Ψ`) [F], the jump law of the index, and the unit-gap receivers; it has no symplectic structure for the family (log §5).

| Answer | Effect |
|---|---|
| Yes, and the index is determined by the two ends of the path | a topological computation of the number of right zeros: a producer of unit-gap kind |
| Yes, and the far end carries the zeros | the topological route is the boundedness of `Ψ` to contact (B2) in another language |
| No such structure | the index of the comb is not a Morse index of a variational problem |

**Tests.** T1: fails; a producer of RH strength. T2: passes for the existence of the structure. T5: for the Liouville twist the index is positive just above the trivial aperture; a structure that does not see this is wrong. T8: not a named problem; first step: the Hamiltonian form of the canonical system of the window tower, obstacle: the end at infinite aperture.

**Carried questions.** A count quadratic in the divisor with the comb defect as its Tate limit (B87, B169); a correspondence on the orientation cover with bounded local indices (B106).

**Limit.** No geometric question below RH is open that the corpus has not answered with an identity or with an equivalence.

## 2.9 New field for RH: coherence theory of reciprocity families

**Does RH need a new field?** Not a further language for receivers. The fields that the mechanism classes call for exist as programmes and end at theorems:

| Field | Programme | Where it ends |
|---|---|---|
| reciprocity sources and family continuation | FCT, MMD | the half-plane `Re s>7/8` [X]; in Lean the frame with reciprocal kernels, the probe's correction, the budget with every floor of its squares, the law of a twist family |
| gap theory of finite strata | FFA, ELT | receivers off the scale; tangent data; every finite datum realized under one structure; the weighted current open |
| the count and its imitations | SPAL, RAC | bounded errors are rigid; fakes at every power above `½` and below it from a half-plane |
| conversion theory | CTZ, IRP, SignFreePurityMechanisms | bounded and Wiener classes closed; one sign-free Riemann hypothesis (Goss) |
| relaxation theory of horizons | HAT, BHR, AHMH | regulators with the count of their limit; exponents `1−Θ/2`, `1−Θ∞/2` |
| Lefschetz paths, heights, finite scale | AGZ, HFP | paths transport no sign; linear count of sections; explicit matrices |

136 programme folders cover the mechanism classes that can be named. What none of them contains is an estimate of a family that is not a square. The one producer bounds a law by squares and converts it to a point by the multiplicity of the target; its limits `13/15` and `5/6` are limits of that step, and its frame has a second family inside it (§1.6). A field is justified for exactly this.

| Aspect | Content |
|---|---|
| What it is about | The phase relation between the amplitudes of a family of rows and the columns of a reciprocity kernel: when arithmetic amplitudes align with a column (coherence, saturation) and when they cancel; the exact evaluation of signed Gram forms; the towers of families that correct one another |
| What it is like | The theory of large sieves read one level deeper: the object is the off-diagonal of the Gram form with its sign, the result an evaluation and not a bound. Its model case is the principal subfamily, which is always coherent and is the target |
| Established | The signed Gram identity; saturation by matched phases; the floors of every Cauchy–Schwarz sieve; the invariance of row norms under unitary re-expansion and the trichotomy of reflection–summation words; the law of the principal twists; the Poisson coefficients of the cubic probe and the quadratic sieve [L*] (FG, MV, TF1, FS5, QS1). The correction as an `L`-function of a second family [D] |
| Criteria | H1 it evaluates before Cauchy–Schwarz. H2 it saturates on matched phases and on the principal twists. H3 it fails for `μ²` and for even order, where the sign is the parity of the character. H4 its exponents are stated in the twist exponent, against the thresholds `1/12`, `1/6`, `1/3`. H5 it treats the correction of a family as a member of the theory, not as a constant |
| Questions it must answer | B175. Which directions of amplitude space are coherent for the sextic kernel besides the principal twists? Is the signed Gram of two rows a completed sum with its own reflection? B184: do the families `ψ₆^kη` close under correction, and what is their common abscissa? |
| Tools it develops | Poisson summation in the column of a pair of rows; reciprocity for products of residue symbols; completed sums in two row variables; the budget calculus with a signed term |
| Objects | Rows, columns, amplitudes, signed Gram forms, coherent directions, corrections, towers |
| Language | coherence, saturation, signed Gram, saving before Cauchy–Schwarz, correction, tower, wall of the frame |
| Mechanisms | Built on: FCT, MMD. To discover: an identity that evaluates the off-diagonal of a signed Gram form of the actual coefficients |

**Main conjecture [A].** Off the principal twists the actual amplitudes of the sextic probe are incoherent: `R₀<1`, with a positive saving before Cauchy–Schwarz. **Milestones.** M1 the signed Gram of the floor bin with the actual kernel after Poisson summation. M2 `R₀<1`. M3 A139 and the first member of the tower. M4 a saving `s>0`. M5 the common abscissa of the tower.

**Status [A].** The field has identities and floors and no estimate. Its reach is bounded by its own frame: with every saving the cubic probe stops at the wall of its correction, `2/3`, and a tower with one abscissa stops at `3/5` [D]. For the stretch between that limit and the line the corpus has no object. A source for it has to meet four conditions: the Möbius sign as a coefficient (odd order); the target among the family with multiplicity; a reflection; and a correction whose Euler product converges on the whole half-plane `Re s>½`.

## 2.10 New field for AAL: additive arithmetic of finite layers

**Does AAL need a new field?** Its parts exist in three programmes and no programme joins them: the receivers and the tangent datum (FFA), the instruments (ELT), the models (SPAL, APD). The junction has theorems on both sides of what it has to prove.

| Aspect | Content |
|---|---|
| What it is about | What addition on ℤ does to a finite top layer: the datum of `Λ`, `μ`, `λ`; its image under bilinear decompositions and under Poisson summation in the cofactors; the signed currents in which it appears; and the models that show which inputs a proof cannot do without |
| What it is like | A theory of one finite-dimensional object, the trigonometric polynomial of world I, with a model theory attached: every proposed step is run on the fakes, the firewall and the Euler products with a prescribed divisor |
| Established | Four sectors of the normalized trace; attainment on every window and at the primes; quantized multiplicities; the tangent data of `μ` and `λ` with the factor `ζ(2ρ)`; zero limits of normalized translates; filters, growing-order reduction, the unweighted near-diagonal row; positivity on the line of the pole only; the real zero on top of every deletion; the firewall [L*]/[F] |
| Criteria | Acts at every depth with constants that do not degenerate as the depth tends to zero. Uses a finite datum. Fails on Euler products over natural norms, on the firewall and on the fakes, at a step that uses a remainder `O(1)` or the functional equation. May be invariant under the Liouville twist. Is not a statement in law and not positivity of a prime density |
| Questions it must answer | B145. B183: is there a model with integer norms, a count rate below `√x` and a non-real pair alone on top; if not, a count rate forces a real top zero without positivity, and ζ has none. The data under additive twists (A144). Is world I with a tail empty (B141)? |
| Tools it develops | Gaussian filters at growing order; cofactor lattices; exact continuum corrections; Bohr means and quanta; two-sided prime edits with discrepancy at every frequency |
| Objects | Data, layers, currents, cofactors, quanta, filters, edits |
| Language | datum, attainment, current, cofactor, quantum, sector, fake |
| Mechanisms | Built on: FFA, ELT, SPAL. To discover: one bilinear identity in which the datum enters with a constraint |

**Main conjecture.** AAL. **Milestones.** M1 the data of `μ` and `λ`: in Lean (TD1). M2 the model with a non-real top (B183), or its exclusion. M3 the weighted near-diagonal row. M4 B145. M5 B141.

**The model question (B183).** The fakes of the corpus with a count rate are deletions and have a real zero on top; additions never fake; the models with a non-real pair have real weights (the firewall) or counts in the mean only. A two-sided edit, some primes deleted and some doubled, is in neither class [L*] (IF7, AO1, MD3). If it exists with a count below `√x`, AAL has no proof from an Euler product over the rational primes with multiplicities `0,1,2`, integrality and a power saving of the count. If it does not, a count rate forces a real zero on top of every finite layer.

## 2.11 New field for RH without positivity: reciprocity calculus without squares

**Does a positivity-free, non-spectral RH need a new field?** For AAL the field of §2.10 is sign-free and non-spectral as it stands. For the half-planes the corpus has one source class, and under the constraint it meets two prohibitions: its reflection is spectral (B180), and its conversion and its sieves are squares. The arithmetic of the probe is in Lean with elementary proofs: Gauss and Jacobi sums, reciprocity for quadratic and sextic symbols, Poisson coefficients, the quadratic sieve [L*] (FC4, FS5, QS1).

| Aspect | Content |
|---|---|
| What it is about | Family sums of Gauss-sum coefficients evaluated by reciprocity and Poisson summation alone, with no operator and no inequality between a sum and a sum of squares; the half-planes that such evaluations give through the two-estimate frame |
| What it is like | The field of §2.9 with one tool removed. The floor `5/6` is a floor of squares, so the constraint removes what cannot cross it and keeps what can |
| Established | The sign law at every order above two; the Poisson coefficients and the local factor; the frame, in which the half-plane follows from two bounds by a contour argument; the budget [L*]. A Riemann hypothesis proved by dominance alone, in an ultrametric field (CG1) |
| Criteria | No operator and no sign of a form. No Cauchy–Schwarz between rows and columns. The reflection of the theta row by Poisson summation at the cusps. Fails for even order. Its boundary is a theorem about exponents |
| Questions it must answer | B180. B175 in the form of an identity. What boundary does the frame give with the non-reflected side alone? Is there an archimedean statement with the strength of strict log-concavity of norms: a quantity attached to ξ in which one term dominates at every point off the line? |
| Tools it develops | Reciprocity in cyclotomic rings; Poisson summation on the Eisenstein lattice at three cusps; exact evaluation of pair sums; the budget calculus |
| Objects | Rows, columns, twists, slots, pair sums, boundaries |
| Language | source, row, column, slot, pair sum, boundary |
| Mechanisms | Built on: FCT, MMD. To discover: an elementary reflection; an evaluation of a pair sum |

**Main conjecture [A].** Without squares the two-estimate frame has no floor at `5/6`; without spectral input its boundary is that of the elementary reflection. **Milestones.** M1 the budget without the reflection. M2 B180 or its refutation in the calculus. M3 the pair sum of the floor bin as an identity.

**Limit.** The wall of the frame at `2/3` is not an effect of positivity and stays [D].

## 2.12 New field for RH as AdS physics: relaxation theory of arithmetic cusps

**Does it need a new field?** The receivers, the regulators and the filters exist (HAT, BHR, AHMH, CTH, FFA); dynamical realizations and their limits exist (ArithmeticResonanceTheory). One mechanism has no programme: a lower bound for the damping of the slowest mode beyond the tempered rate.

| Aspect | Content |
|---|---|
| What it is about | Relaxation rates of observables that are not square-integrable — a pulse at a point of the horizon, a closed horocycle — on horizons of finite volume with a cusp; the part of the rate that the excursions into the cusp carry; the role of the arithmetic of the group in it |
| What it is like | The theory of essential spectral gaps of open systems [C], in a setting where the trapped set is not fractal and the gap, if any, is arithmetic. Its reference rate is the tempered exponent `½`, its ceiling `3/4` |
| Established | The rate ⇔ strip dictionary; exponents `1−Θ/2` and `1−Θ∞/2`; filters; regulators with the count of their limit; no bound state of `Γ(N)` below `3/16`; Hölder realizations give a strip and additive realizations have no oscillation estimate [L*]/[KR]. The rate `1/16` through a family of twists [X] |
| Criteria | Built from the horizon and the places, never from the zeros. Beats the exponent `½`. False for a non-arithmetic cusped surface of the same area and for graph horizons with slow resonances. Not a consequence of Hecke symmetry, of KMS positivity or of modular conjugation alone. A rate with a margin is a half-plane; the maximal rate needs an equality case |
| Questions it must answer | B178. Which property of the cusp excursions of an arithmetic group fails under deformation of the group? Is there a horizon of this family with isolated least-damped modes, as a calibration of world I? What is the horizon meaning of the quantum of a multiplicity? |
| Tools it develops | Transfer operators of the cusp excursions; estimates for singular observables; Euler filters; the fixed-height floor |
| Objects | Horizons, excursions, resonances, filters, rates |
| Language | rate, slow mode, filter, excursion, saturation, tempered wall |
| Mechanisms | Built on: the receivers and the filters. To discover: a principle that separates the modular group from its deformations |

**Main conjecture.** An arithmetic cusped horizon relaxes faster than the tempered rate for a reason of the horizon. **Milestones.** M1 the two calibrations in Lean. M2 a rate in a toy family where it is a theorem. M3 a rate `δ>0` for the modular horizon proved from the horizon; a rate above `1/16`. M4 saturation.

## 2.13 New field for RH as topology or geometry: symplectic index theory of the aperture

**Does it need a new field?** The lattice and index theory exists (AGZ, HFP), with the exact index for Hecke characters and one Artin character, the finite-scale reduction with explicit errors and the jump law. Paths exist and transport nothing. What no programme contains is a topological computation of the index.

| Aspect | Content |
|---|---|
| What it is about | The family of restricted Weil forms as a path in the aperture; its conjugate points; a symplectic structure in which the index is a Maslov index; the ends of the path |
| What it is like | Morse theory of a variational problem whose second variation is the comb form [C]; the arithmetic enters as impulses at the logarithms of the integers |
| Established | Jumps equal nullities; resonant apertures locally finite; robust index of the finite comb; the unshifted index between index and index plus nullity; the scalar flow of the chain; unit-gap receivers; the first conjugate aperture between `(1/C)log log γ₁` and `log(γ₁/2π)` for a lowest off-line zero at height `γ₁` of depth at least `exp(−c log³γ₁)` [L*]/[F]/[D] |
| Criteria | The index of the Liouville twist is positive just above the trivial aperture. A wrong constant, weight or tree length produces a conjugate point. The structure is defined without the zeros. A unit gap suffices: index at most one is index zero. It is additive over the constituents of a number ring, as the index law is |
| Questions it must answer | B179. Is a null mode at a resonant aperture charged (B104)? Are the nullities even? What is the end of the path at infinite aperture, and does it exist for the finite combs of a fixed ratio? What is the order of the first conjugate aperture of a deep zero: the rung of the sizes or the rung at which clusters hide (B156)? |
| Tools it develops | Hamiltonian form of the canonical system; Lagrangian paths; comparison theorems; the finite comb with explicit block error as discretization |
| Objects | Apertures, null modes, conjugate points, Lagrangian planes, ends |
| Language | conjugate aperture, nullity, crossing, end, homotopy |
| Mechanisms | Built on: the jump law, the robust index, the flow. To discover: a homotopy invariant that equals the index |

**Main conjecture.** The aperture path of ζ has no conjugate point, and this is the vanishing of a homotopy invariant. **Milestones.** M1 the Hamiltonian form. M2 the Maslov index on the finite combs. M3 the ends. M4 a comparison object. M5 index zero.

## 2.14 A research programme to construct `𝔽₁`

**Goal.** A geometry in which Spec ℤ has a product with itself and the inequality of Castelnuovo and Severi on that product is a theorem. The programme is `AbsoluteGeometryOfSpecZ` with `HodgeTheoryOfAFixedPart`; `SelectiveArithmetic`, `FloorFreeArithmetic` and `SumProductArithmeticOfTheLogarithm` are its test benches.

**What the corpus fixes [L*] unless marked.**
| Item | Theorem |
|---|---|
| The pairing | jets + contacts − counterterm `→2d₁d₂−Z(f)`; Bézout ⇔ RH; index = number of right zeros |
| Forced data | the constant (`c≤0`), each contact at its price `2\|t\|/√n`, tree lengths `log p` |
| Number rings | ideals as degree points; the pairing of a primitive ray class character tends to its pole plane minus its zero sum; exact index for the Dedekind zeta function; the class characters together carry the ideals of trivial class with pole-plane weight `1/h` |
| A non-abelian extension | the degree-two character of `Gal(ℚ(∛2,ω)/ℚ)`: contacts `(#{x³=2 in 𝔽_{p^m}}−1)log p`, explicit formula, index law |
| Below the first contact | a discriminant above `(128π)^{r₁+r₂−1}(4π)^{r₂}` gives the inequality with margin `∫f²/5000` |
| Finite scale | RH ⇔ the sign of `𝔚_{3K+1}` on step packets ⇔ a positive mass floor on every ratio window; robust index = right zeros; block error `6(J+1)E(R+J,Q,B)` |
| Tails | Laguerre tails → Li coefficients; power tails: growth `σ` at `a` ⇔ `Θ≤1−a+σ`, convergence radius `½−w` |
| Sections | sections of the first `N` graphs in aligned boxes: volume over `N!`; planar restriction is an equality of ideals [KR] |
| Deformations | the price path at every `n₀≥2`: RH at every parameter on all packets |
| Certificates | every system feasible at a large aperture is within `ε` of `Λ` at each `n` |
| Counts of models | a bounded count error identifies the rational primes; a count rate does not: fakes |
| Curves | the defect of an integral class on a hyperelliptic curve is a natural number, quadratic on rays |

**What it would be like [D].** Spec ℤ over `𝔽₁` is a curve of infinite genus whose square is rigid: it is not a member of a family, every one of its invariants is forced, and its Néron–Severi lattice is the same for every number ring up to the density of the comb, with an index that is additive over Artin constituents in the one non-abelian case that is computed. Its sections count like a curve, not like a surface. Its index is a function of the aperture with jumps at null modes. Its zero width is read on one sequence of tails. Passing from `𝔽_p[T]` to ℤ keeps the lattice and loses the count; what distinguishes ℤ from its imitations is the exact count and the functional equation, not a count rate.

**State of the constructions.**
| Construction | Deliverable | State |
|---|---|---|
| I. A path on the comb lattice | transport of the sign from a known case | closed: price paths at every prime; RH at every parameter |
| II. The archimedean fibre glued to the trees | the comb form as a glued form | invariant gluings refuted [KR]; every free parameter forced |
| III. Stepanov on the planar square | a small section vanishing on a window | closed: equality of ideals |
| IV. Squares of towers, class fields and Galois extensions | the index law per character | closed for the characters above; the base has weight `1/d`, `1/h`; general Artin characters open (A145) |
| V. The own comb | Bézout for an integer-norm system on its comb | closed: fails for the squares |
| VI. A count | natural numbers with quadratic Tate limit | the object's count is linear; counts on surviving prime rays ⇔ RH; no definition without the form (B87) |
| VII. Finite scale | the inequality in finite rank | closed as an equivalence with explicit errors; no sign of a matrix `𝔚_Q` beyond the first contact (A143) |
| VIII. The index as a topological invariant | index zero from the ends of the aperture path | not started (B179) |
| IX. The width on the tails | the scale read on the comb | closed as an equivalence; for `a+w<½` the limit is the zero pairing `2ξ′/ξ(1−a)/(1−2a)` [L*] (PT4) |

**Criteria.** C1 reproduces Weil and Stepanov for curves. C2 counts alone are not enough, and a count rate is not enough: fakes. C3 uses the functional equation: integer-norm models with a finite layer fail, the Liouville twist fails at rung one. C4 uses the Euler product on the function. C5 sees the exact normalization. C6 infinite type. C7 the diagonal is the density of a comb, with discriminant and conductor. C8 positivity is derived, and not from a section count. C9 selective only where a contact enters; no margin. C10 on a number ring it gives the index of each character, additively. C11 below the trivial aperture it proves nothing that the dominated box does not have. C12 at finite scale it is the sign on step packets. C13 it is a statement at the point: no deformation of the square transports it. C14 its count is quadratic in the divisor. C15 it treats a null mode at a resonant aperture. C16 its tails grow at the rate of the width.

**Questions the programme must answer.**
1. A count quadratic in the divisor (B87, B169).
2. Bézout from a property of the object (B149).
3. The index as a homotopy invariant of the aperture path (B179).
4. Artin characters in general (A145).
5. The step-packet matrices as the intersection matrices of an object with a known index theorem; first the sign of `𝔚_4` (A143).
6. The polar charge of a null mode (B104).

**Tools.** Witt vectors and Λ-structures; comb finite parts; step packets with explicit errors; the index law for Hecke and Artin characters; combs of norms; the scale; tangent data; fakes as counter-geometries.

**Order of work [A].** A143; A145; the Hamiltonian form of the canonical system (first step of B179); a quadratic count. **Decisive test.** A construction whose Bézout holds for an integer-norm system with a finite layer, for a fake, for the Liouville twist at rung one, for a wrong constant, or along a path of squares, is wrong [L*].

## 2.15 A research programme to close the route WD

**Goal.** A bound `O_θ(T^K)`, with one `K` and unbounded `θ`, for the second moment of ζ times a Möbius mollifier of length `T^θ`; or the collision bound to which it is equivalent [F].

**What the corpus fixes.**
| Item | Statement | Evidence |
|---|---|---|
| Receiver | RH ⇔ the mollified moment on `[0,1]` is subpolynomial in the length; a cofinal bound with fixed `K` suffices | [F] |
| Depth | dyadic boundedness at length `T^θ`, `θ>½`, leaves finitely many zeros beyond depth `1/(2θ)+ε` | [L*] (SA-g) |
| Proved range | `θ<½`: two main terms and a power saving, also displaced | [L*] (TM1) |
| On the line | at `θ=13/50` a positive proportion of critical zeros of odd multiplicity | [L*] (LV1) |
| Dictionary | finite Fejér means are signed logarithmic collision forms; the actual coefficients have size between `X²/log X` and `X²log²X` | [F] |
| Necessary length | a normalized moment within `K₀/log T` of one forces `log N≥log²T/(6K₀)−(4/3)log T`; fixed polynomial length gives excess `≥1/(8+6θ)` | [KR] |
| Blindness | Type II norms are blind to multiplicative signs; raw `μ`, `λ` moments on the line are unbounded in the length; a finite relocation of zeros is invisible to quadratic tests of length `o(T²)`; a short weight does not remove the last-scale defect | [KR] |
| Purity | an impure Euler factor passes every upper bound up to a constant; the limit one of the mollified moment detects it | [KR] |

**What it would be like [D].** A mean-value theory for Dirichlet polynomials longer than the height. Below the height a mean value is a diagonal; above it the off-diagonal is a correlation of the truncated Möbius divisor sums at shifts up to the length over the height, and the theory is a theory of those correlations with a power saving. On the scale, a bounded dyadic moment at `θ` is the half-plane `½+1/(2θ)`: the route passes `7/8` at `θ=4/3` and reaches the line only cofinally.

**Criteria.** W1 the bound fails for `ζ(s)(1−cp^{−s})`, `c>√p`, in the limit one. W2 it fails for a configuration with finitely many zeros relocated, which needs length beyond `T²`. W3 it is not a Type II norm bound. W4 it keeps the pole and the Barban–Vehov diagonal exact. W5 its exponent `K` does not grow with `θ`. W6 at `θ<4/3` it gives nothing that [X] does not give.

**Questions it must answer.**
1. Twisted moments for `½≤θ<1` (A18): which coefficient structure carries the off-diagonal [C].
2. The exact collision form of the moment for `θ≥1`, with the pole terms.
3. A power saving of the collision count at one `θ>4/3`: a half-plane below `7/8` (B161).
4. The same with `K` fixed along a sequence `θ→∞` (B62).
5. Whether a bounded moment at one `θ` follows from the half-plane `½+1/(2θ)`: the converse of the depth theorem.

**Tools.** Gallagher's transfer from logarithmic windows; the Selberg integral dictionary; shifted correlations of sieve weights; the Levinson gate as a test of constants; logarithmic averages and the entropy decrement (A21) as the only correlation input in Lean.

**Objects, language, mechanisms.** Mollifiers, prefixes, collars, collisions, last scales; length, depth, excess, purity. Built on: MZF, CDG, APR. To discover: a correlation estimate with a power saving that sees the sign of `μ`.

**Milestones.** M1 `θ<½`: in Lean. M2 a proportion on the line: in Lean; a better constant needs M3. M3 A18. M4 the collision dictionary at `θ≥1`. M5 a saving at one `θ>4/3`. M6 the cofinal bound.

**Decisive test.** An argument that bounds the moment of the impure twin to the limit one, or sees no difference after a finite relocation at length below `T²`, is wrong [KR].

**Limit [A].** The cofinal bound is RH. Every partial result of this route is a level of the scale, and above `θ=4/3` it competes with the producer of §1.6.

## 2.16 A research programme to close the route ACS

**Goal.** The inequality of Castelnuovo and Severi on the degree points: one positive square of the comb pairing; equivalently the sign of the finite matrices `𝔚_Q` on step packets, a mass floor on every ratio window, or subpolynomial power tails for every `a<½`.

**What the corpus fixes.** The table of §2.14, and:
| Item | Statement | Evidence |
|---|---|---|
| The minimal face | one inequality per prime on logarithmic windows, as the limit of two-bump comb forms | [L*] (MF5) |
| Transfer | combs ↔ step packets ↔ smooth packets, in both directions, with the error `6(J+1)(2X+16(1+log 2XB)+2ψ(Q))/B` | [L*] (AG5, SP1, SP2) |
| Index | exact for Hecke characters, Dedekind zeta functions, class characters, one Artin character; B13 ⇔ index `0` or `∞` | [L*] (AG3, AR3, AC1) |
| Tails | `F_a=O(N^{σ+ε})` ⇔ `Θ≤1−a+σ`; RH ⇔ every tail converges | [L*] (PT2, PT3) |
| Short windows | on a window with no divisibility among its degrees the form does not depend on the contacts; a single degree `n` is negative exactly at `n=2,3` | [KR] |
| The proved sign | half-width `181/500` | [L*] (SA-j) |

**What it would be like [D].** Three tracks on one lattice. *Matrices*: the sign of an explicit family of finite matrices, ratio by ratio; each ratio is a finite-height statement, and the error of every finite stage is explicit. *Index*: the number of negative directions as a function of the aperture; the route closes if no aperture carries a null mode. *Tails*: one scalar sequence per exponent, whose growth is the width; this track is the scale read on the comb.

**Criteria.** The criteria C1–C16 of §2.14. In addition: S1 at ratios below 2 it proves nothing about the contacts. S2 it gives a margin `γ(Q)>0` at each ratio and none uniform in `Q`. S3 on the tails it gives nothing at `a<1/8` that [X] does not give.

**Questions it must answer.**
1. The sign of `𝔚_4` and `𝔚_7` with a margin (A143): the first windows with two and three contacts.
2. A structural reason for one positive square on a subfamily of step packets that grows with the ratio.
3. Bézout from a property of the object (B149); a quadratic count (B87, B169).
4. The polar charge of a null mode (B104); the index as a homotopy invariant (B179).
5. Subpolynomial tails at one `a>1/8`: a half-plane below `7/8` on the comb.
6. The index law for Artin characters (A145) and for every number ring with the level of [X] (A141).

**Tools.** Schur complements of the step-packet matrices against the pole plane; the explicit block error; the robust index; the Mellin calculus of the tails; the index law; fakes and wrong data as tests.

**Objects, language, mechanisms.** Degree points, contacts, jets, combs, packets, blocks, tails; Bézout, index, null mode, mass floor, width. Built on: AGZ, HFP, ACCE. To discover: a property of the lattice that is an inequality.

**Milestones.** M1 explicit finite criteria: in Lean. M2 A143. M3 a growing subfamily. M4 the sign at every ratio (B152), or the index dichotomy (B13) with ZAL.

**Decisive test.** As in §2.14.

**Limit [A].** Each finite stage is a rung; the uniform statement is RH. No structure of the square in the corpus is an inequality.

## 2.17 A research programme to close the route ZCG

**Goal.** One of: no positive-time collision of the heat flow; the floor on a decisive sequence of prime windows; or the three atoms ZAL, B13, Landing.

**What the corpus fixes.**
| Item | Statement | Evidence |
|---|---|---|
| Worlds | a failure of RH is world I or world II, with top at most `7/8` | [X]; [L*] (AT1, AT2) |
| World I receivers | unit gap; non-attainment; one exponent for all moments; four sectors | [L*] (FF2–FF4, FF14) |
| World I instruments | filters; growing-order currents; tangent data of `μ`, `λ`; quanta | [L*] (EL1, TD1, FF7) |
| World I models | every datum under one structure; the firewall; fakes with a real top | [L*] (FF6, MD3, IF7) |
| World II | ZAL is a half-plane at every depth: the scale; filtered horocycle rates approach `3/4` iff ZAL | [L*] (log §4.8) |
| Landing, DH | local below no height; not forced by the functional equation with Gamma factor and count; refuted for Euler products alone | [L*] (AT3, MD1, MD2) |
| Heat | RH ⇔ no collision; `N(t)≥2` at small times unless RH; backward heat has nonreal zeros | [L*] (HT1, FF11); [KR] |
| Cameras | a bounded near-top cluster is visible or has a deep companion within a fixed gap; the exterior costs `O(1/log T)` | [L*] (CM1–CM4) |
| Resolution | no window below the logarithmic radius decides, at any prescribed radius | [L*] (SL2) |

**What it would be like [D].** Two programmes that share instruments. *World I* is a finite-dimensional problem with a complete receiver and a complete model theory: it closes by one inequality that fails on every model, and the models say where such an inequality can come from (§2.10). *World II* is the scale: it closes by half-planes at every depth and inherits the limits of the producer (§1.6). The heat flow joins them at small time and has the count of its limit. The cameras are the instrument of world II in law: they see an isolated cluster near the top and say nothing when clusters grow.

**Criteria.** Z1 a world-I statement fails on the configurations of FF6, on the firewall and on the fakes. Z2 it is two-sided or holds at every length: one-sided floors on one length have models. Z3 a statement about windows below the logarithmic radius decides nothing. Z4 a world-II statement is placed on the scale before work starts. Z5 a camera statement names the cluster size and the gap it needs. Z6 nothing in law is used as a point.

**Questions it must answer.**
1. B145 or B170: world I.
2. B183: the model with a non-real top.
3. B141: is world I with a tail empty?
4. B13 and Landing: no first step is known; which input beyond one structure they need (B157, A120).
5. B59: the cluster wall of the cameras at the heights they need.
6. The half-planes of world II: the questions of §2.18.

**Tools.** Filters, currents, quanta, half-period deletion; Turán power sums in centred cameras; the model ladder; the scale.

**Objects, language, mechanisms.** Worlds, atoms, layers, data, clusters, companions; attainment, quantum, sector, visibility. Built on: FFA, ELT, SPAL, MZF, ZCG. To discover: one inequality for a finite layer that uses the exact count or the functional equation.

**Milestones.** M1 receivers and instruments: in Lean. M2 B183. M3 the weighted current for one quartet. M4 AAL. M5 ZAL through the scale. M6 Landing and B13.

**Decisive test.** An argument for AAL that holds for a tempered symmetric configuration, for the firewall, or for a fake with a real top replaced by a non-real pair, is wrong.

**Limit [A].** AAL and ZAL together are RH. The corpus has a receiver for each and a producer for neither below `7/8`.

## 2.18 A research programme to close the route MC/JAS

**Goal.** The signal bound `O(Z^b)` for every `b>½`; equivalently level one of the dressed aggregate on large primes.

**What the corpus fixes.** §1.6 in full, and: the signal is a smoothed Möbius sum and its exponent is the abscissa (FC1); level `σ` ⇔ half-plane `σ−½` (JA1); the centred orientation count is `M(N)` (OC1); producer rates are the Mertens level (RT1); bilinear norms are blind to the sign [KR].

**What it would be like [D].** A programme of exponents with four stages, each with its own kind of input:

| Stage | Half-plane | Input | Kind |
|---|---|---|---|
| 0 | `7/8` in the native graph | A118, first the balanced design at `11/12` | just work |
| 1 | `7/8 → 13/15` | the row count of the binding bin (B174) | a density estimate |
| 2 | `13/15 → 5/6 →` below | signed cancellation across the rows (B175): `R₀<1`, then a saving `s` before Cauchy–Schwarz | an estimate that is not a square |
| 3 | `2/3 → 3/5` | the correction as an `L`-function (A139); a common half-plane of the tower (B184) | a coupled system of families |
| 4 | below `3/5` | no object in the corpus | — |

**Criteria.** J1 every estimate is placed in the twist exponent before work starts. J2 a mean square that contains the principal twists is not an input. J3 positive weights fail; even order fails; two row variables fail. J4 below `5/6` nothing is a square. J5 below `2/3` the family contains the characters of its corrections. J6 a source for the last stretch has a correction that converges on `Re s>½` (§2.9).

**Questions it must answer.**
1. B174, B175, B184, in this order of depth.
2. Does the probe extend to the characters `ψ₆^kη` of infinite order, with the same frame?
3. Is `3/5` the limit of every form of the cubic probe, or of the form in Lean?
4. Is there a source with a correction that converges on the half-plane: an identity for the Möbius sign whose sixth-power part enters at an argument `≥1` on `Re s=½`?
5. Level one directly (B160): no first step.

**Tools.** The budget calculus; the signed Gram; Poisson coefficients; sieves over `ℤ[ω]`; the scale as a ruler; the model `μ²`.

**Objects, language, mechanisms.** Signals, rows, columns, bins, slots, corrections, towers; boundary, floor, saving, wall. Built on: FCT, MMD, SA. To discover: a signed evaluation; a frame without a second family.

**Milestones.** M1 the native `11/12`, then `7/8`. M2 a boundary below `7/8`. M3 `R₀<1`. M4 A139. M5 a saving `s>0`. M6 the tower.

**Decisive test.** An estimate that holds for `μ²`, for matched phases, or for a family with its principal twists counted as input, proves no half-plane.

**Limit [A].** With every stage completed the programme reaches `3/5`, or `7/12` given GRH for the tower [D]. It is the only programme of the corpus that has produced a theorem about the zeros, and it does not reach the line in its present frame.

## 3. The one big question: how far does the frame of the producer reach?

**Where the question sits.** One mechanism has produced a pointwise theorem about the zeros [X]. Every graded receiver of the corpus — levels, rungs, mollifier lengths, returns, tails, ringdown — reads its exponent and has no other producer. Whether this mechanism is a route to the line or a route to a fixed half-plane decides what all of them can expect from it.

**What is in Lean [L*].** The half-plane follows from two estimates for a sum compared with the signal of `exp((s−c)²)H_η(s)/L(s,η)`, under the premise that `H_η` is holomorphic and nonvanishing right of the boundary (FS2). For the probe that premise is proved right of `7/8`, for the principal corrections right of `2/3` (FS3, FS6). The local factor of the correction is `(1−Q⁻²)(1−Q⁻¹(AQ^{3−6s}−ηQ^{−s})/(1−ηQ^{−s}))/(1−AQ^{3−6s})` with `A=κ⁶`, and its distance from one is `≤14Q^{−e}` for `e≤min(6σ−3,1+σ,2)` (PC2, PC3). In three variables the correction of an unramified row is within `80Q^{−1−ε₀}` of one on `Re x≥51/100`, `Re w≥−1/100`, `Re(x+w)≥1+ε₀`, `Re z≥17/50` (FS7); there the factor `L(6x+6z−4,ψ₆η⁶)` of the deduction below has its argument right of `1`.

**What follows [D] (D3).** `H_η=L^S(6s−3,ψ₆η⁶)·E_η` with `E_η` absolutely convergent on `Re s>½`. The first factor is a Hecke `L`-function of a character of infinite order: entire, with all its nontrivial zeros in `½<Re s<2/3` [C]. So the premise of the frame fails left of `(3+Θ_ψ)/6`, a number in `[7/12,2/3]`. With `H_η` only holomorphic the frame concludes: the zeros of `L(s,η)` right of the boundary are zeros of `L(6s−3,ψ₆η⁶)`. Dividing the correction out transfers its Möbius sum to the direct bound, whose trivial estimate has the exponent `2/3`. If the frame holds for the characters `ψ₆^kη` with corrections of the same form, and the tower has one abscissa `b`, the frame is valid on `Re s>(3+b)/6`; the map `b↦(3+b)/6` has the fixed point `3/5`; under GRH for the tower the wall is `7/12`. The corpus has two other pairs of this kind: halving pairs `ζ(ρ)=ζ(ρ/2)=0`, which force `Θ≥2/3` [KR], and Shimura zeros at `ρ/4+¼` [F].

**Question (B184).** *Is there a form of the probe that reads the zeros of `L(s,η)` alone on `Re s>½`: a completed sum with the reciprocal of the target in its principal row and a correction whose Euler product converges on the whole half-plane? Or is every form of the cubic probe a coupled system — the correction of `η` an `L`-function of `ψ₆η⁶` — whose common half-plane cannot pass `3/5`?*

**Why this question.**
- It is below RH, AAL and every half-plane: its first half is an identity between Euler products and a classical fact about zeros of Hecke `L`-functions.
- It decides whether the scale is a route to the line. If the coupling is intrinsic, no saving in the estimates of §2.4 and §2.5 leads from this producer to RH; the routes JAS, MC, S3, the depth reading of WD, the rungs of RW, HF, ACS, SRT and the exponent of PM have a ceiling at `3/5` through it, and RH needs a statement off the scale or a source of another kind.
- If a form without coupling exists, the line is reached by estimates alone, and the thresholds of §1.6 measure what is missing.
- It costs little: the first step is one identity in the objects of two Lean modules.

**What an answer gives.**
| Answer | Effect |
|---|---|
| the identity `H_η=L^S(6s−3,ψ₆η⁶)E_η` and zeros of `H_η` in the strip (A139) | the frame in Lean is confined to `Re s>2/3` unconditionally; a wall Π168 with an exact position |
| the probe extends to the tower with corrections of the same form | a coupled system of half-planes; with one abscissa its limit is `3/5`; quasi-RH for the `L`-functions of the characters `ψ₆^kη` is a theorem to prove with the method of [X] |
| every form of the cubic probe has a correction with zeros in the strip | the producer is a route to `3/5` (or `7/12`), not to the line: a kill of the scale as an RH route through this source, with its exact position |
| a form with a correction that converges on `Re s>½` | the line is reachable by estimates: B175 with `s=1/3` is the one missing input |

**First step and obstacle.** A139: the factor `∏(1−κ_v⁶N(v)^{3−6s})⁻¹` as the `L`-function of the character `v↦κ_v⁶` on ideals, and the remaining product on `Re s>½`. Named obstacle: the Hecke characters of the corpus are ray class characters of finite order; the tower needs characters with an angular part, and the frame, the Poisson coefficients and the sieves for them.

**Tests.** T1: a method question about the frame, implied by nothing about ζ's zeros; its second branch is a half-plane for a family of `L`-functions, implied by GRH. T2: an identity, and an existence statement with stated properties. T3: named for each answer. T4: pass. T5: calibrated on the two corrections that are in Lean (right of `2/3`, right of `7/8`), on the three-variable region where the correction is close to one near `Re x=½`, and on the halving pairs. T6: pass. T7: sets Π168; moves Π159. T8: not a named problem; the first step is in corpus objects.

**Limit.** The question concerns one source. A negative answer leaves RH where it is and removes its only producer from the list of routes to the line.

**Dependence.** On the definitions of the probe in Lean; the half-plane `7/8` is [X].

### Alternatives considered
| Question | Effect | Verdict |
|---|---|---|
| The row count of the binding bin (B174, §2.4) | the exponent moves inside `[13/15,7/8)` | one-sided; a density estimate; does not lead to the line |
| Signed cancellation across the rows (B175, §2.5) | a boundary below the floors of the squares | the estimate the producer lacks; hard; its value depends on the answer to B184 |
| A fake with a non-real top and a count rate (B183, §2.10) | the inputs that a proof of AAL cannot do without | a model question; closes the model theory of world I |
| The weighted current (B145, §2.6) | AAL without positivity | AAL strength; fails T1 |
| Polar orthogonality (B104) | the critical curve becomes one inequality | native; open; produces no sign |
| The steps of [X] that the Lean graph lacks (A118) | the half-plane in the native graph | just work |
| A relaxation rate from the horizon (B178, §2.7) | a second producer of a half-plane | no first step beyond two calibrations |
| A Maslov index (B179, §2.8); a quadratic count (B87, B169); `JasDressedPSD 1` (B160); the sign on step packets (B152) | RH | producers of RH strength; fail T1 |
| What excludes a finite stratum with both structures (B157) | a calibration for the atoms | a method question; proves no atom |
| Deuring–Heilbronn for ζ (B141); B13; Landing | atoms | no first step |
| Depth density `o(T)` (B57); arithmetic control beyond frequency one (B150) | first near-line inputs past the diagonal | census problems |
