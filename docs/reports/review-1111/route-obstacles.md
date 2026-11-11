# Route obstacles — status quo

Scope: the 38 live route formulations, the 12 route candidates and the supporting programmes. For each route: the path, what is established, the obstacles that are **(a) just work**, and the obstacles that are **(b) open mathematics nobody has a solution to**.

**Corpus checkpoint:** commit `b23b54cd36` with its working tree (2026-11-11). Fact log: `logs/review-1111-rev2-facts.md` (cited as "log §n"; identifiers such as `MF1`, `FS2` are entries of log §4, §6, §8 and §9, `D1–D9` of log §7). Companions: [obstacles-summary.md](obstacles-summary.md) (A/B lists, ideation, the one question), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ), [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem).

**Live** means source observable, proved RH-sufficient receiver and explicit open estimate. **Candidate** means the source-to-receiver step is missing. Formulations are not independent mechanisms: HJ is PA; the BSY criterion of FEL belongs to CTF; PCS, DR, PW-B are retired labels. A criterion, a source construction, a quotient equality or a scalar grade does not discharge an arithmetic sign or vanishing.

**Evidence.**
- `[L*]` Lean statement read at the declaration for this report; the declaration is listed in the log under the identifier given in parentheses.
- `[F]` stated by the frontier map at the checkpoint; `[KR]` stated by the scoped-obstruction ledger at the checkpoint. Both were read in full for this report. `[S]` marks a module that the frontier map grades unfinished or unintegrated.
- `[D]` deduction made in this report from `[L*]` statements; not a Lean theorem. `[C]` classical mathematics quoted from memory, not in the corpus. `[A]` assessment.
- `[X]` the theorem of the external source cached in the repository (OpenAI, 30 September 2026), taken as proved: every finite-order Hecke `L`-function over `ℚ(√−3)` and every Dirichlet `L`-function, ζ included, is zero-free in `Re s>7/8`; so `Θ≤7/8`. Its formalization in the Lean corpus is incomplete: the native graph has no `7/8` theorem [F], and the missing steps are just work (A118). Every row that uses `[X]` carries the tag and states the form proved in Lean beside it. **Natively** refers to the Lean graph.

**Strength.** RH; ≥qRH (implies a zero-free half-plane, Lindelöf or ZAL; the half-plane `Re s>7/8` is a theorem [X], so an item of this strength is open where it gives a half-plane below `7/8` or is not known to follow from [X]); AAL (implies the asymptotic abscissa law); sub (implies neither a half-plane nor AAL); method; producer; indep.

**Labels.** `A*` just-work items and `B*` open problems are listed in [obstacles-summary.md](obstacles-summary.md). `(unverified)` marks A items whose difficulty is not established. Σ, Π, Γ refer to [walls-ledger.md](walls-ledger.md).

**Notation.** `Θ=sup Re ρ`; `Θ∞=inf{σ≥½: finitely many zeros have Re ρ>σ}`; `w=Θ−½` the zero width. **ZAL** `Θ∞=½`; **AAL** `Θ=Θ∞`; **B13** finitely many off-line zeros ⇒ none; **Landing** ZAL ⇒ finitely many off-line zeros; **DH** ¬AAL ⇒ ZAL; **B56** `Θ<1 ⇒ Θ=½`. `S(u)` the lag structure of the cubic spline `B`, `2Re S(log p)` the prime trace; `P(d)` the smoothed von Mangoldt count in the window of `d`, `A(d)` its archimedean-plus-pole prediction. A **logarithmic window** at `T` is `{p: |log p−T|≤32 log(T+2)}`. **World I**: ¬AAL, a finite isolated top layer at `β<1`. **World II**: AAL ∧ ¬ZAL. The **depth** of a zero is `|Re ρ−½|`. A **tangent datum** is a depth `0<b≤½`, a finite set of positive ordinates and a multiplicity for each; the **normalized trace** at depth `b` is `2Re S(u)e^{−bu}`. **Comb pairing** of a real divisor `D=Σc_nγ_n`: off the diagonal `½(1/|m−n|+1/(m+n))+Λ(n/m)` (jets plus contacts), on the diagonal `−log(n/2π)`; `d₁=Σc_n/n`, `d₂=Σc_n`; **comb form** `2d₁d₂−D·D`. The **power tail** at `0<a<½` is `F_a(N)=N^{2a−1}·combForm([1,N])(n^{−a})`. A **window of ratio `Q`** is `(N,QN]`, its **aperture** `½log Q`. A **system** is a weight system `w` with a **mass** `m` (log conductor, or log height of a modulated packet); `w` is **dominated** if `|w|≤Λ`; the **rung** of an aperture `a` is `κ=a/log m`; the **trivial aperture** is the supremum of the apertures at which every dominated system is feasible. The **Liouville twist** is `w(p^k)=(−1)^k log p`. `JasDressedPSD σ`: positive semidefiniteness of the `σ`-dressed lag aggregate. The **signal** of a kernel `G` is `(1/2π)∫G(2+it)Z^{2+it}dt`; the zeta kernel is `exp((s−c)²)/((s−1)ζ(s))`. A **step packet** is `σ_je^{u/2}` on the windows `(log(R+j),log(R+j+1)]`. A **fake** at the exponent `β` is a discrete system with integer norms, other than the rational primes, with count `Ax+O(x^β)`, whose pole-cleared zeta function continues to `Re s>½` and vanishes there at a point where ζ does not. The **probe** is the cubic-theta sum of [X]; its **correction** `H_η` is the Euler product that remains when `ζ(6z)ζ(w)/L(x,η)` is divided out of its principal row at the residue `w=1`, `z=1/6`.

## 0. The picture

| Fact | Evidence | Consequence |
|---|---|---|
| RH ⇔ `∃K`: `2Re S(log p)≥−K` at the primes of arbitrarily late logarithmic windows outside at most `Ce^{δT}` primes per window (`δ<1`); ⇔ the upper bound alone on undeleted windows; ⇔ `ℕ`-counts on the surviving prime rays with quadratic limit the plane defect; ⇔ one growth exponent for all even local moments; ⇔ the limit of the two-bump comb form at each such prime | [L*] (MF1–MF5) | sign, prime count and count door are one number per prime on sparse windows |
| For every nonnegative `R=o(log T)` there is a simple tempered configuration with logarithmic unit counts, unattained top `½+Θ` and arbitrarily late windows `\|u−T\|≤R(T)` above every floor; a density-matched one for some `R→∞` | [L*] (SL2, MF8) | below the logarithmic radius no receiver at the level of configurations decides RH |
| Floors with constants depending on `k` on arbitrarily late windows of each length `(k+1)π/67` give AAL; a one-sided floor on windows of one length has a finite-stratum model | [L*] (MF7, FF5) | world I is seen on bounded windows; the two forms of non-attainment differ |
| At `b_*=Θ−½` the normalized trace is in exactly one of four sectors: RH (Bohr almost periodic); top line empty (trace `→0`); top line finite nonempty (trace asymptotic to a nonzero trigonometric polynomial); top line infinite (no trigonometric-polynomial limit). Excluding the third gives AAL; the converse fails on a configuration | [L*] (FF14) | AAL follows from the absence of one asymptotic shape |
| AAL ⇔ for every line `Re s=½+h` the number of zeros to its right is at most one or infinite | [L*] (FF2) | AAL is a unit gap |
| Every tangent datum is the top layer of a finite tempered symmetric configuration; of a nonnegative density with a simple pole (any `Θ<1`); of an Euler product over natural norms with natural coefficients, linear counting and continuation to `Re s>½`, with the prescribed multiplicities; of an Euler product over rational primes with repetition for `17/30<Θ<1` | [L*] (FF6) | the explicit formula, positivity, Euler products over integer norms and counting put no condition on a finite top layer |
| AAL, or `Θ<1` (which holds [X]) and for every `β∈(Θ,1)`, `γ₀≠0` a meromorphic function with an Euler product over the rational primes, multiplicative coefficients `0≤a(n)≤C_εn^ε`, `0≤Λ′≤2Λ`, polynomial bounds for itself and its inverse, exactly the pair `β±iγ₀` right of `Θ`, and a pole in `0<Re s<1−Θ`. The class of configurations whose right zeros are the divisor of an Euler product over natural norms has floor `½` | [L*] (MD3, FF1) | the Euler product with bounded coefficients, without the functional equation, does not give the abscissa law; a producer has to use the Euler product on the function, not on its zeros |
| Integer-norm fakes exist at every count exponent `β>½`; from a zero-free half-plane `Re s>Θ` of ζ at `β=½−(1−max(Θ,¾))/64`, so at `½−1/512` [X]; under RH at every `β>⅓`. A fake omits infinitely many rational primes; at `β≤½` it has positive density. Every prime-deletion fake with a count rate has a real fake zero on or right of all its fake zeros; a system that only adds primes vanishes at its real abscissa | [L*] (IF1–IF8, AO1); [X] | the remainder of the integer count as a power does not separate ζ; a fake built by deleting or by adding primes has a real zero on top |
| Positivity of a prime density with pole weight `A` and a finite layer of total multiplicity `M` on the line of the pole holds eventually iff `2M≤A`; with a simple pole only the empty layer is admitted; below the line of the pole a compensator on a bounded interval restores positivity for every layer | [L*] (PL1, FF6) | the classical positivity argument reads the line `Re s=1` and nothing inside the strip |
| `Θ≤7/8`: quasi-RH is a theorem; with `Θ<1 ⇔ Θ∞<1` also `Θ∞≤7/8`, and the world `Θ=Θ∞=1` is excluded; RH ⇔ ZAL ∧ B13 ∧ Landing; B13 ⇔ the supremal negative index on real packets is `0` or `∞` | [X]; [L*] (AT1, AT2, AC1) | a failure of RH is world I or world II, with top at most `7/8`; three atoms |
| A function with the Riemann Gamma factor, residue one, growth of order one and the zero count of ξ within one has all zeros simple, off the line, approaching it, and no landing; two-scale Euler products over natural norms refute graded repulsion | [L*] (MD1, MD2) | Landing and DH follow from neither structure alone |
| For `η>0` and large `q`: every dominated system has the floor `½(1−e^{−η/2})log q∫\|F\|²` at `a≤log log q−η`; at `a≥log log q+η` the Liouville twist and `−Λ` fail on the odd polar packet and `Λ` without pole plane on the even one; the trivial aperture is `log log q+o(1)`. At height `t`: a dominated system fails at `log log t+log(π/2)+η` | [L*] (SA-a, SA-b) | sizes prove the sign to rung `1−o(1)` and nothing beyond |
| One theorem: cancellation `(C,γ)` with `2γκ<1` pays the sign on bounded shapes to `a≤κ log log q`; positivity on tests of aperture `κ log(A log\|γ\|)` forces a second off-line zero near a zero of depth `δ>1/(2κ)`; a bounded dyadic Möbius moment at length `T^θ`, `θ>1`, confines high zeros to depth `<1/(2θ)+ε`; seven power savings are equivalent to `Θ<1`, and all hold [X] | [L*] (SA-g, QR1); [X] | one exchange rate `γ=δ=1/(2κ)=1/(2θ)` |
| At aperture `κ log log T` the paired sign on bounded shapes fails only on a set of heights in `[T,2T]` of measure `≤T^{1−1/(2κ)+ε}`; for every `a>0`, `0<δ≤½` a tempered configuration at ζ's density is positive on `[−a,a]` with zeros of depth `δ` at unbounded heights | [L*] (SA-c, SA-f) | the sizes fail at aligned heights only; the sign at a fixed aperture is not a strip at the level of configurations |
| RH ⇔ `JasDressedPSD 1` ⇔ positivity at level one on all large primes ⇔ positivity at infinity at every level above one; for `½≤b<1`: `Θ≤b` ⇔ the signal of the zeta kernel is `O(Z^{b′})` for every `b′>b`; the signal is `Σμ(n)·signal(poleKernel)(Z/n)`; a signal bound `O(Z^b)` gives the level `b+½+ε` on large primes | [L*] (JA1, FC1) | levels, half-planes and the exponent of one smoothed Möbius sum are one scale |
| For `0<a<½`, `σ≥0`: the power tail `F_a` is `O(N^{σ+ε})` iff every zero has `Re ρ≤1−a+σ`; the tails converge for `a+w<½` and diverge for `a+w>½`; RH ⇔ every tail converges | [L*] (PT1–PT3) | the comb reads the zero width on one explicit sequence |
| Over `ℚ(ζ₃)`: if zero-freeness of every `L(s,η)` in `Re s>β` off `1` gives every ray class character a sum with a direct bound `Z^{a₁}` and a comparison `Z^{a₂}` with the signal of `exp((s−c)²)H_η(s)/L(s,η)`, `a₁,a₂<β` common, for every `β>σ₀`, then `Θ≤σ₀`. The pole-cleared form of the step has a false premise for a nonprincipal character. With the probe's own correction the implication is a theorem for `7/8≤σ₀<1`, with the principal corrections for `2/3<σ₀<1` | [L*] (FS1–FS3, FS6) | in Lean the half-plane is one implication whose only premises are two estimates; at `σ₀=7/8` the two estimates are theorems [X] |
| The correction is `H_η=L^S(6s−3,ψ₆η⁶)·E_η`, `ψ₆(π)=(π̄/\|π\|)⁶`, `E_η` absolutely convergent on `Re s>½`: its Euler product converges absolutely exactly on `Re s>2/3`, and it has infinitely many zeros in `½<Re s<2/3` | [D] (D3) from [L*] (PC2, PC3); [C] | the frame of the probe is unconditional right of `2/3`; below it the probe reads the zeros of `L(s,η)` modulo the zeros of a second family |
| Exponent budget of the probe: boundary `7/8` at the published geometry `(17/48,23/48,1/6)`; no geometry reaches `7/8−1/2500` with a row count `≥21766/32589−10⁻⁴` in the bin `δ=79/204`; the floor bin summed trivially stops at `1−4/(5n)` (`13/15` at `n=6`); rows of nonnegative rescaled length stop at `1−1/n` (`5/6`), with the hybrid slot retained for every geometry; reflected rows through the same twists return the zero; a boundary `5/6−s` needs a bilinear row–column saving `s` taken before Cauchy–Schwarz (`¾`: `1/12`; `½`: `1/3`); among the orders `n≥6` the order six has the least corner of the designs without slots | [L*] (TB, LP, FG, MV, FC3) | the room inside the Gauss-sum probe is `[13/15,7/8]`; below `5/6` the class needs a signed estimate |
| A generic mean square of the smoothed Möbius sums over the principal `n`-th-power twists of norm up to `Z^θ` holds exactly for `θ≥(n/(n−1))(2Θ−1)`; the minimum is zero iff RH; with `μ²` the range is `θ≥n/(n−1)`; the full Jacobi family is generic at every `θ` iff RH and GRH for the odd squarefree quadratic twists | [L*] (TF1–TF4) | a mean square over a family that contains its principal twists is a receiver of the strength of its half-plane |
| `CombBezoutShift c ⇔ c≤0 ∧ RH`; one contact changed by `t` at `n₀`: Bézout ⇔ RH ∧ `2\|t\|/√n₀≤c`; tree of `p` at length `ℓ`: Bézout ⇔ RH ∧ `ℓ=log p`; along the price path of any `n₀≥2` Bézout on all packets is RH at every parameter | [L*] (AG1, AG2) | constant, contacts and tree lengths are forced; a path transports no sign |
| RH ⇔ exactly one positive square of the intersection Gram on packets; the negative index counts the distinct right zeros for ζ with Dirichlet characters, for a Dedekind zeta function, for the class characters together, and for the degree-two Artin character of the splitting field of `X³−2`; the pairing of a primitive ray class character of a number field tends to its pole plane minus its zero sum | [L*] (AG3, AR1–AR3) | the Hodge index is the exact count of the right zeros, also for a character of a non-abelian extension |
| RH ⇔ `𝔚_{3K+1}≥0` on step packets of `3KR` blocks for all `K,R` ⇔ eventual floors `−ηΣc²` on every ratio window ⇔ a positive coefficient-mass floor `γ(Q)` on each ratio window; `r≤#`right zeros ⇔ eventually `r≤` the robust comb index; at block size `B` the comb form per point differs from `𝔚_Q` by at most `6(J+1)E(R+J,Q,B)Σσ²`, `E=(2X+16(1+log 2XB)+2ψ(Q))/B` | [L*] (AG5, HF1, HF2, SP1–SP3) | the inequality at finite scale is an equivalence in three forms, with an explicit transfer between a matrix margin and the comb |
| RH ⇔ some feasible weight system at every aperture; every system feasible at a large aperture is within `ε` of `Λ` at each `n`; feasibility at an aperture ⇔ spectral kernels positive definite on node intervals; the pencils `ξ(s+h)+ξ(s−h)` and the cleared Eisenstein constant term over their dominant halves are no Dirichlet series | [L*] (FW1, FF10, FF12) | the existence half of the sign carries no freedom in the limit |
| The clock regulator lies below Weil's form at every cutoff; `Λ(s)/Λ(s+N)` has at most one right zero ⇔ RH; the heat flow has at least two nonreal zeros at every small time unless RH; a form with one negative square in which the right zeros are a symmetric spectrum gives RH | [L*] (FF9, FF11) | no regulator of the corpus supplies a unit gap before the limit |
| A bounded holomorphic Dirichlet series on `Re s>x` whose zeros are zeros of ξ has no zero; a Wiener expansion on a strip with an interior zero has nonsummable residues and admits no `ℓ^p` transport of its zeros to zeros of ζ | [L*] (CT1) | ξ has no bounded or Wiener constituent with a zero |
| RH, or `R_polar<W`, or `R_polar=W` finite with every critical half-line ground state orthogonal to the polar source | [L*] (AH1) | the critical curve has one undecided case (B104) |
| RH through height 67; RH through `windowHeight(a)` gives the sign on `[−a,a]`; there is `C` with: RH through `exp(exp(C·a))` gives the sign on `[−a,a]` for every `a≥1`; the constant of the proof exceeds `10⁸` | [L*] (VR1, VH1); [D] (D5) | each window is a finite-height statement at double-exponential cost; height 67 gives no window through this theorem |
| Displaced twisted second moment of `ζ·`(real polynomial of length `T^θ`), `θ<½`, bounded by its main terms plus a power saving; from these moments at `θ=13/50`: eventually `N_odd(U)≥κN_ζ(U)`, `κ=(1−log(18/5)/(13/10))/4≈0.0037`; simple critical zeros `≥(0.67250071−ε)N(T)` in the objects of the imported `Zeta23`; positivity cost of a pair-correlation certificate `≥1+3/π²` | [L*] (TM1, LV1, CN1, PC1) | the mean-value ladder is proved below the square root and gives a positive proportion natively; positivity alone does not certify 70% |
| Universal horocycle exponent `sup=1−Θ/2`; with a nonzero Euler polynomial filter `sup=1−Θ∞/2`, never above `3/4`; ZAL ⇔ filtered rates approach `3/4`; AAL ⇔ no filter accelerates; zeros `Re ρ≤1−2δ` ⇔ every compact pulse decays like `e^{−(δ−ε)τ}` | [L*] (module summary, log §4.8; RD1) | on the horizon the scale is a relaxation rate; `δ=1/16` and the exponent `9/16` hold [X] |
| The Goss zeta function of `𝔽_q[T]` at `z∈ℤ_p∖ℕ` has exactly the zeros `ρ_d∈𝔽_p((1/T))`, simple, of strictly decreasing norms: strict log-concavity of the coefficient norms and an ultrametric Newton polygon | [L*] (CG1) | one Riemann hypothesis in the corpus is proved with no sign; no corresponding norm is identified for ξ [F] |
| `Θ≤7/8` for ζ, for Dirichlet `L`-functions and for finite-order Hecke `L`-functions over `ℚ(√−3)`. In Lean: the cube of the composite cubic Gauss sum is the ideal Möbius value times a phase; `g(χ)^n=−card F+z(μ−1)²` for odd order `n>2`, `χ(−1)card F+…` for even order; the quadratic large sieve over `ℤ[ω]` is `≪(MN)^ε(M+N)` | [X]; [L*] (CU1, FC4, QS1) | one producer, and it has produced a half-plane; its source identity, its frame and one of its sieves are in Lean, its two estimates are not (A118) |

## 1. Mechanism classes

| Class | Mechanism | Status |
|---|---|---|
| M1 Signed criticality | primes pay the archimedean–polar deficit by sign | exact on every window; a window at aperture `a` follows from verification to `exp(exp(Ca))` |
| M2 Calibration | window cones, feasible sets, margins | feasible sets nonempty at every aperture ⇔ RH; they shrink to `Λ`; margins decay doubly exponentially [KR] |
| M3 Canonical flow | `L, q, Ψ` of the Weil chain | RH ⇔ `Ψ` locally bounded on precontact intervals [L*] (PS1) |
| M4 Reflection | Krein forms, ringdown, horocycles, cavity energies | sharp receivers; horocycle exponents are `1−Θ/2` and `1−Θ∞/2` |
| M5 Square-root cancellation | smoothed prime counts, long moments, squarefree counts | receivers closed; estimates open |
| M6 Continuation | heat, cosine, Jensen | collision-free flow ⇔ RH [L*] (HT1); the flow has the count of its limit |
| M7 Zero geometry | cameras, Blaschke factors, inner field | a bounded near-top cluster is visible or has a deep companion nearby [L*] (CM3); clusters hide [KR] |
| M8 Finite-layer receiver | damping filters, centred Vaughan currents, half-period deletion, non-attainment | complete in world I; four-sector classification of the trace; tangent data of `μ`, `λ` |
| M9 Production | integer stencils, integrality, Stepanov over ℤ | rate = Mertens level [L*] (RT1); at one prime `p^{11/12}` [F] |
| M10 Count | nonnegative count with quadratic Tate limit | hyperelliptic curves [L*] (CL1); over ℤ the count of sections in boxes has no quadratic term [L*] (AG6) |
| M11 Orbit at finite time | prime phases, returns, resonators | depth by Baker; breadth to VK; under `Θ≤b` heavy returns need `log t≥c·y^{1−b}` [L*] (SA-d) |
| M12 Critical compactness | thresholds, pole channel, half-line ground states | three-way classification [L*] |
| M13 Topology of the prime complex | nerve, persistence, orientation cover | centred count `M(N)`, `Ω_±(√N)`; weight `½` ⇔ RH [L*] (OC1) |
| M14 Infinite-rank elimination | towers, thick sets, attained tops | with an attained top a thick crude count is RH [F] |
| M15 Prime-degree sampling | logarithmic windows, exceptions, upper side, counts, moments | complete receiver [L*] |
| M16 Intersection on half-products | adelic carrier, Green kernels | invariant glued diagonal refuted [KR]; critical adelic inverse unbounded [L*] (HA1) |
| M17 Absolute geometry | square, contacts, carries, rings, paths, tails | forced data; exact index for Hecke characters and one Artin character; paths transport no sign; power tails read the width |
| M18 FE rigidity | Hamburger, defects, prime measures | countable systems with an integrable defect are the rational primes [L*] (RG1); continuous prime measures keep every zero |
| M19 Exceptional-coordinate atoms | ZAL, B13, Landing, DH | RH = ZAL ∧ B13 ∧ Landing; all open for ζ |
| M20 Families and monodromy | gauge torus, covers, towers, class characters | fixed-part laws; the base has weight `1/d`, `1/h` [KR] |
| M21 Index and limits | index law, unit gaps, sizes on a circle | index-one limits give RH; unit gaps pass to limits; no approximant with a gap |
| M22 Separation | ordinate injectivity, digit calculus, ultrametric Newton polygons | receiver for ξ [F]; a complete proof for the Goss zeta function [L*] (CG1) |
| M23 Hodge lattice at finite scale | comb pairing, block averages, step packets | RH in three finite-scale forms; robust index = right zeros; explicit block error |
| M24 Arithmetic constituents | recurrence against density, jump law, prime contraction | none with a zero in the bounded and the Wiener class |
| M25 The ladder | mass, aperture, rung | sizes to rung `1−o(1)`; one exchange rate |
| M26 Family continuation | signal of a reciprocal kernel; two estimates; reciprocity | the half-plane `Re s>7/8` [X]; in Lean the frame with reciprocal kernels, the probe's correction, the budget and its floors |
| M27 Dressed positivity | lag aggregate at a level | level one ⇔ RH; level `σ` ⇔ half-plane `σ−½` |
| M28 Floor-free receivers | homogeneous, unit gap, certificate, amplification, symmetrization | each kind has its receiver and its kill (block S13) |
| M29 Models of the count | deletions, additions, characters, finite edits | fakes at every exponent above `½`, below it from a half-plane; a real zero on top of every deletion |
| Amplifiers | Diophantine repulsion, integrality, isolation, Turán, positive annihilators | amplify or reshape a certificate, produce none [KR] |

## 2. Shared obstacle blocks

### S1. Complete Weil family at the critical curve
Routes: HF, SRT, AIP, ACS (atomic), SC. Programmes: CACT, AHD, CSAR, ACPL, ADT, RAPT.

Established:
- `0<R_PD=R_PSD=R_polar=R_halfline≤W=R_prim=R_high=inf_A windowThreshold(A)`, each infinite iff RH [F]; the three-way classification [L*] (AH1).
- Complete tilted-spline matrix positive definite for every exponent below `1/8` eventually, uniformly in `1≤c≤(log N)^α` [L*] (CW1); through one fixed small multiple of `(log N)^{1/8}` [F]; no countable square-bounded family of holomorphic multipliers dominates the depleted kernel [KR].

| | Obstacle | Strength |
|---|---|---|
| A9 | explicit constants of the eighth-root horizon and the Beurling schedule | — |
| A13 | near-gcd charges and periods beyond the admissible scale (unverified) | — |
| B6, B101 | full-space sign at every critical multiple; polar payment at every ratio | RH |
| B104 | whether a critical half-line ground state at finite `W` can be polar-orthogonal | method |
| B123 | correlated arithmetic pairings dominating the depleted kernel | method |

### S2. Window tower, canonical flow and the aperture–height exchange
Routes: RW, EWU, OWU, ACT, CHMD, TT (odd), SZ, RN, LI, HF, ACS, SRT. Programmes: CWS, WTZ, DZG, GWZ, CSTW, SWC, FADF, CHT, AIF, VHR, WVL, SA, ACCE.

Established:
- RH ⇔ `W≥0` on every window [F]; RH ⇔ `Ψ` and `L=artanh r` bounded on every bounded precontact interval [L*] (PS1).
- `RHVerifiedThrough(windowHeight a)` ⇒ the sign on `[−a,a]`; RH through height 67 [L*] (VR1); `∃C`: RH through `exp(exp(Ca))` ⇒ the sign on `[−a,a]`, `a≥1` [L*] (VH1), with `C>10⁸` [D].
- RH ⇔ every aperture admits a real weight system with nonnegative Weil form; ¬RH ⇔ some aperture admits none [L*] (FW1). For `2a<log 2` feasibility does not depend on the weights; `\|w(n)\|≤√n(log(1+1/r)+C)` with the pole plane; every `w(2)` with `√2\|w(2)−log 2\|≤1/5000` is feasible up to `a=181/500` [L*] (SA-j).
- Certificates: for every `n≥2`, `ε>0` there is an aperture beyond which every feasible system has `\|λ(n)−Λ(n)\|≤ε` [L*] (FF10). Margins: best margin of a window `≤K exp(11A/2−πe^{2(A−2)})`; floors `(1/20000)/2^k` through `a_k`, `a_∞<0.3621` [KR]. The absolute edge cost of the primes reaches one at `c_*∈(½log 5,½log 6]`; below `2c<log 5` the kicks of `{2,3,4}` cost less than `991/1000` of the Lévy energy [F]/[KR].
- Index in the aperture: immediately right of an aperture the index is the negative index plus the nullity [L*] (IA1); resonant apertures are locally finite [F].
- Positivity at aperture `a` confines every zero with `T₀(c)≤\|γ\|≤2πe^a` to depth `<exp(−c log³\|γ\|)` [L*] (SL3); a configuration with ζ's local counts hides a zero of depth `δ` at height `T` to aperture `(log T)/36` [KR].
- The ladder (block S12).

| | Obstacle | Strength |
|---|---|---|
| A1–A3, A6 | certified verification past 67, numeric heights, first-window membership, cone widths | — |
| A142 | a constant of ordinary size in the verification rate | — |
| A140 | the sign on windows of half-width below `½log 5`, where the absolute cost of the primes is below one (unverified) | — |
| A117 | end points of the feasible interval of `w(2)` on the first selective window | — |
| B1, B2, B4, B5 | sign on every window; bounded oscillation of `Ψ` to contact; outer predictors; kick admission | RH |
| B3, B16, B17 | variation of `r` free of `1/μ`; decay law of the margin; signed ground states past `log ρ` | sub / method |
| B179 | a symplectic structure in which the index in the aperture is a Maslov index | producer |

### S3. Prime-degree sampling and scale locality
Routes: ACS, SRT, WL, HF, ZCG, PM (count door), HAT-C. Programmes: SOSZ, CDGeo, FFA, ShortIntervalPrimesInProgressions.

Established:
- The forms of the minimal face on logarithmic windows, the absolute value among them [L*] (MF1–MF5, MF9); width `≤σ` ⇔ the same with `Kp^σ` [L*] (MF1, MF2); two fixed primes on windows of radius `r√T` [L*] (MF6).
- Floors at every length give AAL [L*] (MF7); counter-configurations at every prescribed sub-logarithmic radius, also density-matched and at prime samples [L*] (SL2, MF8); one-sided floors on windows of one length have finite-stratum models [L*] (FF5).
- Every interval `(x,x+x^θ]`, `θ=1−1/(16(14·10⁷+12))`, with `x` large contains a prime `p≡a (q)`, for every modulus and reduced class [L*] (SI1).
- A global floor `−K` bounds the weighted absolute mass with sharp coefficient two [KR].

| | Obstacle | Strength |
|---|---|---|
| A58 | effective gap iteration (unverified) | — |
| B130 | the bound itself on any decisive sample | RH (≥qRH at `p^σ`, `σ<½`) |
| B144 | separation of the deep off-line ordinates of ζ | sub |

### S4. Continuation, nodal geometry, index and constituents
Routes: ZCG, LA, PTR, HCF, PA, GTA, XN, WD, TH. Candidates: W1C. Programmes: NGF, FFP, ADO, AES, IRP, CTZ.

Established:
- RH ⇔ every zero of every `H_t`, `t>0`, is simple; `N_d≤300√(d log d)` for `log d≥6.1·10⁶` [L*] (HT1); RH ⇔ infinitely many Jensen degrees real-rooted [F]; `N(t)≤1` on times accumulating at `0` gives RH, and without RH `N(t)≥2` at every small time [L*] (FF11); `H_{−τ}`, `τ>0`, has nonreal zeros [KR].
- ξ a locally uniform limit of entire functions with at most `κ` right zeros has at most `κ` [L*] (IX1); a splitting of ξ with sizes on one circle bounds its zeros in the disc by the degree of the factored half [L*] (CT1); a unit gap of analytic approximants passes to the limit [L*] (FF11).
- RH ⇔ the prime lag function is positive definite on `ℝ` [L*] (IX1).
- Constituents: none with a zero in the bounded class and in the Wiener class of a strip [L*] (CT1); every box has a Dirichlet polynomial with exactly the zeros of ξ, of unbounded length [F].

| | Obstacle | Strength |
|---|---|---|
| A19, A20 | heat horizon with an explicit height; Jensen rung past `d⁴≪T log T` (unverified) | — |
| B24, B25 | collisions at small time, all heights; frequency below one | RH |
| B22, B23 | outer roots of the Jensen polynomials; `N_d` bounded | RH; ≥qRH |
| B124 | finite initial depth budgets of the heat divisor | ≥qRH to RH |
| B146 | an independent family of bounded index converging to ξ; a splitting of ξ with certified defect | RH (producer) |
| B27, B47 | runs of simple critical zeros; multiplicity by a non-size input | sub |

### S5. Near-line geometry, long moments and the census
Routes: WD, CTF, MC, TG. Programmes: CDG, APR, MZF, AIF, IGP, TransThresholdPairCorrelation.

Established:
- RH ⇔ the Möbius-mollified second moment on `[0,1]` is subpolynomial in the length; a cofinal bound `O_θ(T^K)` with fixed `K` and unbounded `θ` suffices [F]; dyadic boundedness at length `T^θ`, `θ>½`, leaves finitely many zeros beyond depth `1/(2θ)+ε` [L*] (SA-g).
- For `0≤θ<½`: the displaced twisted second moment with its main terms and an arbitrary power saving [L*] (TM1). With one mollifier of length `⌊U^{13/50}⌋` the dyadic detector law holds with the constant `18/5`, and eventually `N_odd(U)≥κN_ζ(U)`, `κ=(1−log(18/5)/(13/10))/4>0` [L*] (LV1).
- Census: simple critical zeros `≥0.67250071` in the objects of the imported `Zeta23` [L*] (CN1); five consecutive simple critical ordinates at `≥N(T)/5000` starts [F]; every continuous integrable `g≥0` with transform `≤0` outside the unit band has positivity cost `≥1+3/π²` [L*] (PC1).
- Depth: `Σ_{\|γ−t\|≤T}m_ρ·depth≤CT` [L*] (DS1). Finite symmetric relocation of zeros is invisible to quadratic tests of length `o(T²)` on fixed lines right of `½` [KR].
- Cameras: a cluster of at most `N` zeros in an ordinate window `1/(10c log T)`, one of them within `E/log T` of the top, is visible at a lag `ν·A log T` with a signal bounded below, or a zero within depth `d` of the top lies within distance `g`; the exterior mass is `O(1/log T)` [L*] (CM1–CM4). Box-convolution cameras of order `n` pay a finite gapped exterior at `O((hg)^{−n})` times the Lorentzian mass [L*,S] (BC1, BC2); the camera branch has no pointwise control of the prime side at the selected centres [F].

| | Obstacle | Strength |
|---|---|---|
| A18, A21 | twisted moments past the square root; logarithmic two-point Chowla [C]: in Lean the entropy decrement and, at infinitely many scales, `\|c(h)−avg_{p∈𝐏_k}c(ph)\|≤6ε` for the logarithmic correlations `c` of `λ` [L*,S] (LC3); the mean over the prime dilates is not bounded | — |
| B57 | depth density `o(T)` | sub |
| B58–B61 | `D_win`; cluster wall; Green moments at deep zeros; a detector past the last scale | sub |
| B62, B66 | cofinal long moment; near-unit holomorphic budgets | RH |
| B150 | a form factor bounded by `4` on `(1,10/9)`: arithmetic upper control beyond frequency one | sub |

### S6. Production, precision and the Mertens level
Routes: WL, MC, SQF, PBM, RB, JAS, CTF, FU, CFC, RP. Programmes: ASRP, APR, AGT, AKLT, AE, AAD, RAC, MMD, SPAL, HWV, RIAC, ALST.

Established:
- `c₁/(√K(1+log K))≤bestRate K≤exp(−(log K)^α)` for `0<α<3/5` [L*] (RT1); rates `K^{−a}` for all `a<½` give RH [F]; RH ⇔ either one-sided quarter-power law of the weighted squarefree count [F]; RH ⇔ Robin's inequality at `lcm(1,…,n)` for large `n` [F].
- Orientation cover: centred count `=M(N)=Ω_±(√N)`; weight `½` ⇔ RH [L*] (OC1). AAL, or `\|M(x)\|≤Cx^β` with `β<1` [L*] (AT4). In world I the Gaussian window sums of `μ` and `λ` are asymptotic to their residues at the top zeros; the leading numerators differ by `ζ(2ρ)` [L*] (TD1).
- Every Type II bound is invariant under multiplicative signs [KR]; prime-power-supported forms vanish on coprime boxes away from `1` [L*] (PB1).
- Stepanov at one prime: `\|Σ_{n≤p}e(an^p/p²)\|≤5p^{11/12}` [F].

| | Obstacle | Strength |
|---|---|---|
| A30, A33, A46 | best stencil exponent under RH; cubic residue coefficients; singular indices past the cubic cutoff | — |
| B48, B49, B50, B53, B54 | deciding input at square-root precision and its classical faces | RH |
| B55, B67 | polynomial stencil rate; parity at power saving | ≥qRH to RH |
| B15 | pointwise savings past Vinogradov–Korobov in the Lean graph (the half-plane [X] is past it) | sub |
| B56 | `Θ<1 ⇒ Θ=½`; with `Θ≤7/8` [X] it is RH | RH |
| B106 | a correspondence on the orientation cover with bounded local indices | RH |

### S7. Reflection, carriers and the modular horizon
Routes: PM, HAT-C. Candidate: W1C. Programmes: RIT, BHR, ASH, AHMH, CTH, IRP, HAT.

Established:
- RH ⇔ every compact pulse rings down at the quarter rate; a rate `δ` ⇔ `Re ρ≤1−2δ` [L*] (RD1); RH ⇔ positivity of the reflection Krein forms ⇔ horocycle error `O(y^{¾−ε})` of one cuspidal function; one Hecke eigenform: RH ⇔ sharp rate ∧ no nonhalving Shimura zero; any halving pair forces `Θ≥2/3` [F]/[KR].
- Horocycle exponents: unfiltered supremum `1−Θ/2`; with a nonzero Euler polynomial filter `1−Θ∞/2`; no filter passes `3/4`; ZAL ⇔ filtered rates approach `3/4`; AAL ⇔ no filter accelerates past the unfiltered optimum [L*] (log §4.8).
- Regulators: the clock lies below Weil's form at every cutoff, and a floor `−C‖f‖²` at one cutoff per large aperture gives RH [L*] (FF11); the tower of height `N` is the logarithmic derivative of `Λ(s)/Λ(s+N)` plus Robin and polar terms; for every `N`, RH ⇔ the corrected energy is at least minus the jump tail ⇔ the raw energy is at least minus its full defect [L*] (HA1); the tower quotient has a unit gap ⇔ RH [L*] (FF11).
- No bounded critical inverse of the adelic adjacency; the critical spherical operator integral is not integrable [L*] (HA1).
- No Maass cusp form with `0<λ<3/16` on `Γ(N)`, every `N` [L*] (SG1).
- On a hyperelliptic curve the defect of an integral class is a natural number, quadratic on rays [L*] (CL1); RH ⇔ an `ℕ`-valued count with Tate limit the integer probes [F].

| | Obstacle | Strength |
|---|---|---|
| A26 | Weyl asymptotic `N(Λ)∼Λ/12` [C] | — |
| A54 | cusp expansion for Bianchi resolvents | — |
| B68 | independent reflection Krein positivity, Krein flux, dispersion bound | RH |
| B71 | universal decay `e^{−t/4}`; horocycle, Farey, Narain or cavity rate `y^{¾−ε}` | RH |
| B87 | a count with Tate limit `Q`, defined without `Q` | RH |
| B147 | Shimura nonvanishing at `ρ/4+¼` for one eigenform | indep. |
| B114, B117, B171 | a realization of the partner involution outside the excluded classes; a regulator with a unit gap before the limit; a form of signature `(1,∞)` in which the right zeros are a symmetric spectrum | producer |
| B178 | a relaxation rate beyond the tempered exponent `½` for a horizon with a cusp from a principle of the horizon, with no family of twists; the rate `9/16` holds [X] | producer, independent of [X] |

### S8. The exceptional coordinate: two worlds and three atoms
Routes: BAG, ZCG, JAS (shell), SC (undamped), WL (thick runs), ACS (sampling branch), LA (finite support), RW (polar ground energy). Programmes: ZCG AbscissaLaws, ELT, EFT, IWT, IRW, IRP, APD, AAD, TAPO, FFA, SPAL.

Established:
- `Θ≤7/8` [X]; `Θ<1 ⇔ Θ∞<1` [L*] (AT2), so `Θ∞≤7/8` and the world `Θ=Θ∞=1` is excluded. RH ⇔ ZAL ∧ B13 ∧ Landing; linear AAL ⇔ B13 ∧ Landing; AAL ⇔ B13 ∧ extreme DH [L*] (AT1); Landing is local below no height [L*] (AT3).
- One-structure calibrations: block S14.
- World I receivers: non-attainment on windows, for `ψ(x)−x`, at the primes; the unit gap; the quantum of a multiplicity; one growth exponent for all even window moments; the four-sector classification [L*] (FF2–FF4, FF7, FF14). A moment of order `2k` with exponent `A` reaches depths `≥A/2k`; bounds of all orders with one exponent are sup bounds [L*] (FF4).
- World I instruments: prime filters recover the top residues; the growing-order current reduces to centred type-II cofactors with a filtered error `≤2h^d exp(−at/8)` [L*] (EL1); the unweighted near-diagonal row is summable [F]; the tangent data of `μ` and `λ` [L*] (TD1).
- Replication: under a finite nonempty right layer every bounded normalization of translates along a phase return tends to zero [L*] (FF8).
- B13 ⇔ the supremal negative index on real packets is `0` or `∞`; that index is the number of distinct right zeros [L*] (AC1).
- Level one on large primes gives AAL, B56 and `Θ=½` [L*] (SA-h).

| | Obstacle | Strength |
|---|---|---|
| A120 | a finite nonempty stratum with both structures in Lean: Selberg zeta functions of surfaces with a small eigenvalue [C] | — |
| A144 | the tangent data under additive twists (unverified) | — |
| B13, B138 | finite stratum; landing for ζ | sub |
| B141 | Deuring–Heilbronn for ζ: `¬AAL ⇒ ZAL` | sub |
| B83, B170 | AAL; non-attainment for ζ in any of its receiver forms | sub / AAL |
| B89, B112, B128 | a bounded aligned return at each right zero; FE into vertical transport; replication by a mechanism other than normal families | sub |
| B145 | the signed, prime-weighted centred type-II current, with both continuum terms, at a growing isolated mode | AAL [D] |
| B110, B126, B127 | thick crude count; a bound on a sampling set; positive-measure lag recurrence | AAL |
| B157 | which structure of ζ that a Selberg-type zeta function lacks excludes a finite stratum | method |
| B183 | a fake with a count `Ax+O(x^β)`, `β<½`, and no real fake zero: a two-sided edit of the rational primes with one non-real pair on top | method (a construction); the negative side is of GRH type |
| — | ZAL | ≥qRH |

### S9. Prime orbit at finite time
Routes: BAG, TH, SRT, every route at all heights. Candidate: S3. Programmes: PTT, TAPO, TTPO, CDGeo, SPAL, ALST.

Established:
- Near-total `p^{−1/2}`-mass returns of the primes `≤y` need `log t>(log y)^{3/2−ε}` [F]; under `Θ≤b` heavy returns need `log t≥c·y^{1−b}` [L*] (SA-d), so `y^{1/8}` [X].
- Under `Θ<1` the return transfer is equivalent to RH; RH gives it [L*] (FC2). With `Θ≤7/8` [X] the transfer is equivalent to RH.
- For `½<σ<1` and a finite resonator the dyadic mean of `\|Rζ\|²` is the convolution diagonal [L*] (RM1); uniformly for resonators of length `T^κ`, `κ<2σ−1` [F].

| | Obstacle | Strength |
|---|---|---|
| A24 | certified scans (unverified) | — |
| B46 | proportional saving at length `(log X)^{2K}`, all heights; for `K>8` it follows from [X] [D] | sub |
| B97, B137 | constant-precision first return past the VK rung; a collective depth floor uniform in `π(y)` | sub |
| B148 | the transfer of candidate S3 | RH (the strip is [X]) |
| B121 | freezing control beyond the precision cap | sub |

### S10. The diagonal, counts and absolute geometry
Routes: ACS, HF, HAT-C, PM (count branch), LI. Programmes: SOSZ, HAT, AGZ, HFP, AE, RIAC, HHAC, CTH, LST, KPA.

Established:
- Forced data and price paths [L*] (AG1, AG2); lengthening the tree of an odd prime fails on packets wider than `log p`, and for `p=2` the admissible lengths on packets of width at most `log 4` form a closed ray [KR].
- Index: one positive square ⇔ RH; exact count of right zeros for ζ with Dirichlet characters, for a Dedekind zeta function through the ideals, for the class characters together with pole-plane weight `1/h`, and for the degree-two Artin character of `Gal(ℚ(∛2,ω)/ℚ)`, whose contacts are `(#{x∈𝔽_{p^m}:x³=2}−1)log p` [L*] (AG3, AR1–AR3). Below the first contact a discriminant above `(128π)^{r₁+r₂−1}(4π)^{r₂}` gives the inequality with margin `∫f²/5000` [L*] (AG4).
- Sections and counts: planar restriction is an equality of ideals; the count on two graphs is the split norm and fails the parallelogram law; the system of the squares fails on its own comb; in a tower the base has weight `1/d` [KR]; the sections of the first `N` graphs in aligned boxes number the volume over `N!` [L*] (AG6).
- Finite scale: RH ⇔ the sign of `𝔚_{3K+1}` on step packets ⇔ eventual floors `−ηΣc²` on every ratio window ⇔ a positive mass floor on each ratio window [L*] (AG5, HF1); the robust index counts the right zeros [L*] (HF2); the unshifted index lies between the aperture index and index plus nullity, with equality off resonances [L*] (HF3); the block error is explicit, with the ratios 4 and 7 written out, and no sign of `𝔚_4`, `𝔚_7` is proved [L*] (SP1–SP3).
- Tails: the Laguerre tails per degree point tend to the paired Li coefficients [L*] (HF4); the power tails read the width (block S12) [L*] (PT1–PT3); for `a+w<½` their limit is the zero pairing `2ξ′/ξ(1−a)/(1−2a)` [L*] (PT4).
- Carrier: no adelic-invariant glued kernel has Weil's diagonal [KR].

| | Obstacle | Strength |
|---|---|---|
| A28, A41, A48 | reciprocal-quadric traces; count law for plane quartics [C]; Hasse–Weil tests at verified scales | — |
| A143 | the sign of `𝔚_4` and `𝔚_7` on step packets as certified statements (unverified) | — |
| A141 | the half-plane [X] for number fields containing `ζ₃` and, by base change, for every ray class character (unverified) [C] | — |
| B87 | a count on the rays `Γ_1+Γ_p`, defined without `Q` | RH |
| B88 | the sign of the comb finite part | RH |
| B149, B169 | Bézout for the comb pairing from a property of the object; a group with a doubling on which the defect is a canonical height | RH (producer) |
| B152 | the sign on step packets, in any of its finite-scale forms | RH |

### S11. Families, rigidity and exactness
Routes: ACS (tensor branch), ECP, HF, SC, BAG. Programmes: AWT, AK, ALST, SignFreePurityMechanisms, EFT, SEL.

Established:
- Fixed-part laws; sublinear tensor growth with the trace of ζ retained ⇔ RH [F]; pole-preserving gauge deformations are isozeric [KR].
- Countable Beurling systems with an integrable or `L²` functional-equation defect are the rational primes [L*] (RG1)/[KR]; positive continuous prime measures are not rigid and keep every zero [L*] (RG1).
- The Goss zeta function: its coefficients form an entire series with simple slopes, and its zeros are simple and lie in the base field [L*] (CG1).
- `ξ(s+a)ξ(s−a)` keeps a functional equation and an Euler product and moves every abscissa by `a`; strip self-improvement for the family holds iff `Θ=1` [KR].

| | Obstacle | Strength |
|---|---|---|
| B86 | positivity of the endpoint character at unbounded rank | RH |
| B80 | FE twins with off-line zeros in the full class | sub |

### S12. The ladder, the level, the signal and the probe
Routes: RW, HF, ACS, SRT (rungs); JAS, MC, WL, S3 (legs). Programmes: SA, FCT, MMD, RHTower `QuasiRH*`, CDG.

Established ([L*] with log identifiers):
- Sizes and fakes (SA-a, SA-b); bounded shapes do not decide feasibility (SA-i); the first conductor rung forces primes with both signs below `e^{2η}log²q` (SA-e); exceptional heights of measure `≤T^{1−1/(2κ)+ε}` (SA-c); exchange (SA-g).
- Given `Θ≤b`: the rung `(2b−1)κ<1` for the centred contacts, positivity on large primes above the level `b+½`, return bounds (SA-d).
- Level and signal (JA1, FC1); power tails (PT1–PT3).
- Frame: the family step with reciprocal kernels for every number field and, over `ℚ(ζ₃)`, for ζ (FS2); principal corrections holomorphic and within `½` of `1` right of every `σ>2/3` (FS3); the probe's correction is the principal correction with the phases `κ_v⁶`, holomorphic and nonvanishing right of `σ≥7/8` (FS6). The principal row is `ζ^S(6z)ζ^S(w)L^S(x,η)⁻¹∏H_v` in its absolute region; the correction of an unramified row has no pole in `w` (FS4, FS7).
- Source: the cube identity (CU1); the sign law at odd and even order (FC4); the arithmetic of the Poisson coefficients (reciprocity, multiplicativity, prime-power values, local factor) (FS5, module summaries); no cancellation over the exceptional frequencies of a coprime column pair [KR].
- Sieves: the quadratic large sieve over `ℤ[ω]` at exponent one, also for bounded columns on quadratic-supported ideals (QS1); the planar and the Eisenstein large sieve [F].
- Budget (TB, LP, FG, MV, FC3): block row of §0. The law of a twist family (TF1–TF4).
- The correction as an `L`-function and the wall of the frame at `2/3` [D] (D3).

| | Obstacle | Strength |
|---|---|---|
| A118 | the theorem [X] in the native graph: the full arithmetic Poisson series and its continuation; removal of the cube sum in the comparison; both savings uniformly in the character; reflection of the completed theta row; the sextic large sieve; the zero detector. In Lean on the direct side: the quadratic sieve (QS1) and the second Poisson reflection of a pair of rows, separated exactly over the residues modulo 4 and bounded by the geometric mean of two child-row energies with a loss `(H·N𝔟₀)^ε` [L*] (SR1). A first target is the boundary `11/12` of the balanced design without slots | — (just work) |
| A138 | the corollaries of `Θ≤7/8` as unconditional statements (summary §2.1) | — (just work) |
| A139 | the identity `H_η=L^S(6s−3,ψ₆η⁶)E_η` and the absolute convergence of `E_η` on `Re s>½` (unverified) | — |
| B159 | a rung `κ≥4/3`: a power saving of the contacts on the integers between `m` and `m^{2κ}`, uniform in the height, that fails for the Liouville twist | a half-plane below `7/8` |
| B156 | clusters on a rung for ζ: arithmetic cluster exclusion | method |
| B160 | `JasDressedPSD 1` | RH |
| B161 | the signal bound `O(Z^b)` for some `b<7/8`; for every `b>7/8` it is a theorem [X]; in Lean no `b<1` | a half-plane below `7/8` |
| B174 | the row count of the binding bin `δ=79/204` below the published `U^{21766/32589}`; with the count `1−δ+η` the boundary is `½+(5/12)·((5+6η)6−8)/(5(5+6η))` | a half-plane in `[13/15,7/8)`; density type |
| B175 | signed cancellation across the rows of the floor bin for the actual coefficients: a row exponent `R₀<1`, and below `5/6` a saving taken before Cauchy–Schwarz | producer; a half-plane below `13/15`, below `5/6` |
| B184 | the frame below `2/3`: the zeros of the correction `L(6s−3,ψ₆η⁶)`; a common half-plane for the tower `ψ₆^kη` | method; a half-plane below `2/3` |
| B180 | the reflection of the completed theta row without Eisenstein series | method |

### S13. Floor-free receivers and their kills
Routes: every route (as a filter on proposed estimates). Programme: FFA.

Established ([L*] with log identifiers):
- Floors: what holds for every tempered symmetric configuration has floor `½`; a floor of exponent `σ` has floor exactly `σ`; a mechanism that reads only ordinate counts has floor `½`; so has the class of Euler divisors (FF1).
- Homogeneous kind: a floor of the clock regulator at one cutoff per aperture gives RH; the regulator lies below its limit (FF11).
- Unit-gap kind: AAL ⇔ at most one or infinitely many zeros right of every line (FF2); the quantum of a multiplicity (FF7); unit gaps pass to limits; the tower and the heat flow have the count of their limit (FF11); an index-one realization gives RH (FF9).
- Certificate kind: feasible systems converge to `Λ`; feasibility is positive definiteness on intervals and tapered kernels are transforms of positive measures; the pure objects with ζ's Gamma factor are no Dirichlet series over their dominant half (FF10, FF12).
- Amplification kind: one exponent for all even window moments gives AAL; one order reaches depth `A/2k`; all orders are sup bounds (FF4).
- Symmetrization: a linear statistic that does not decrease under splitting has `Re F″≤0` at the split point; a differentiable function of finitely many linear statistics that is monotone under every small split has a gradient symbol whose real part is concave on the line, and zero if bounded below and tending to zero (FF13, GL1).
- Positivity on the line of the pole (PL1); systems that only add primes (AO1).

| | Obstacle | Strength |
|---|---|---|
| B170 | non-attainment for ζ | AAL |
| B171 | a form of signature `(1,∞)` from the places in which the right zeros are a symmetric spectrum | RH (producer) |
| B172 | a functional of the zero configuration that decreases under projection to the line and is not a differentiable function of finitely many linear statistics | producer |
| B173 | a two-sided subexponential bound of the trace on late windows of one length | AAL (RH on those windows) |

### S14. Models of one or two structures
Routes: every route (as calibration). Programmes: FFA, APD, EFT, IWT, SPAL, RAC, SEL.

Established ([L*] with log identifiers unless marked):
- Reflection symmetry and temperedness: every tangent datum (FF6). Positive prime density with a simple pole: every finite layer at any `Θ<1` (FF6). Euler products over natural norms: every finite divisor with multiplicities; two-scale products with a tail (FF6, MD2). Rational primes with repetition: `Θ>17/30` (FF6). Rational primes with real weights in `[0,2]`, meromorphic, polynomially bounded with its inverse: one pair above the frontier of ζ (MD3).
- Integer norms and a count rate: fakes at every `β>½`, with a real fake zero and non-real ones on the same vertical line; below `½` from a half-plane of ζ; none by finite edits; none at `β≤½` with zero density; the system of a real character has count `L(1,χ)x+O(√x)` and is a fake iff `L(s,χ)` has a right zero that ζ lacks (IF1–IF8). A bounded count error at slope one forces the rational primes (CR1).
- The Riemann functional equation with Gamma factor, residue one and count: zeros off the line approaching it (MD1). An integrable defect on a countable system: the rational primes (RG1). A continuous prime measure with an integrable defect: the zeros of ζ (RG1).
- Euler product and a functional equation of degree two with unbounded coefficients: `ξ(s+a)ξ(s−a)` [KR]. Positive finite Euler prefix twins with an off-line zero and a scalar functional equation [KR].

| | Obstacle | Strength |
|---|---|---|
| B183 | a model with integer norms, a count rate below `√x` and a non-real pair alone on top | method |
| B157 | a calibration with an Euler product and a functional equation together | method |

## 3. Live routes

Receiver statements are as stated by the frontier map [F] unless marked; open estimates are its "Open" entries.

### WL — Weil lag
- **Path:** bounded prime-deficit critical energy, or positive definiteness of the prime lag, or an attained top with an `O(√X)` prime deviation on a thick set of scales → RH.
- **Established:** endpoint energy bounded ⇔ RH; RH ⇔ the prime lag is positive definite on `ℝ` [L*] (IX1); RH ⇔ attained top ∧ thick `O(√X)` deviation.
- **(a)** A30.
- **(b)** bounded endpoint energy (B49); deciding input (B48); attainment with the thick estimate (B110); the sign of the lag Gram matrices from prime counts (B1).

### RW — Restricted Weil ground energy
- **Path:** `μ(a)≥0` at every radius → RH; equivalently some feasible weight system at every aperture.
- **Established:** RH ⇔ `Ψ` locally bounded on precontact intervals [L*] (PS1); RH ⇔ feasible weights at every aperture [L*] (FW1); feasible systems converge to `Λ` [L*] (FF10); verified-height rungs [L*] (VR1, VH1); block S2.
- **(a)** A1–A3, A16, A117, A140, A142.
- **(b)** B1, B2, B4, B18. The existence quantifier of B18 carries no freedom in the limit.

### FU — Signed prime scheduling
- **Path:** signed Möbius history → one-sided sampled Abel bound → RH.
- **Established:** either one-sided bound on `A(j^m)/j^m` ⇔ RH; one controlled sample per backward window of length `N^{1−δ}` suffices.
- **(a)** none. **(b)** complete-history bounds across advancing clocks (B42).

### CFC — First-clock lower bound
- **Path:** first-clock source bounded below on a tail → RH.
- **Established:** exact tail criterion.
- **(a)** none. **(b)** the lower bound with prime, archimedean and endpoint terms (B42).

### RP — History floor
- **Path:** eventual linear floor of the normalized history → RH.
- **Established:** exact linear-floor criterion; sublinear floors impossible [KR].
- **(a)** none. **(b)** high-LCM pairs, moving core and singular terms in one floor (B42).

### PA — Prime–archimedean passivity (HJ alias)
- **Path:** prime−Gamma response sign → RH.
- **Established:** calibrated Hausdorff-row sign above an explicit radius; the remaining entries ⇔ RH.
- **(a)** A1. **(b)** signs below the explicit shift, uniformly in the degree (B31).

### MC — Möbius cancellation
- **Path:** half-power Möbius cancellation → RH.
- **Established:** bounded damped Möbius energy at arbitrarily small damping ⇔ RH; centred orientation count `=M(N)` [L*] (OC1); AAL or a Mertens power saving [L*] (AT4); the signal of the zeta kernel is a smoothed Möbius sum and its exponent is the zero abscissa [L*] (FC1); the cube identity [L*] (CU1); the law of the principal twist family [L*] (TF1); the tangent data of `μ` and `λ` in world I [L*] (TD1).
- **(a)** A21, A33, A46, A118, A139.
- **(b)** B48, B50, B15; a bounded-index correspondence (B106); the signal bound (B161); B174, B175, B184.

### SQF — Weighted squarefree count
- **Path:** a one-sided `O(t^{−¼−ε})` bound of `Σμ(n)²e^{−nt}−6/(π²t)` → RH.
- **Established:** RH ⇔ the upper law ⇔ the lower law; the error is `Ω_±(t^{−1/4})`.
- **(a)** none. **(b)** the quarter-power bound for one sign (B48 family).

### TT — Theta tail / Wold
- **Path:** bounded weighted endpoint energy at each `0<t<½` → RH.
- **Established:** RH ⇔ a bound `C_t` for every `0<t<½`; a uniform bound on a shrinking band.
- **(a)** none. **(b)** `C_t` at every fixed `t` (B34).

### LA — Jensen line anchor
- **Path:** Jensen polynomials real-rooted, or sublinear root height → RH.
- **Established:** RH ⇔ infinitely many Jensen degrees real-rooted; `N_d≤300√(d log d)` [L*] (HT1); at each fixed degree only finitely many shifts fail real-rootedness, and excluding the nonempty finite exceptions at every degree gives RH.
- **(a)** A20, A1.
- **(b)** outer roots (B22); bounded `N_d` gives finite support only (B23, then B13, B138); heat budgets (B124).

### ZCG — Zero-configuration geometry / heat descent / abscissa laws
- **Path:** no positive-time collision → RH; or a decisive prime-window floor; or ZAL ∧ B13 ∧ Landing.
- **Established:** collision exclusion ⇔ RH [L*] (HT1); ordinate injectivity ⇔ RH [F]; blocks S3, S4, S8, S13, S14; the four-sector classification [L*] (FF14); cameras [L*] (CM1–CM4).
- **(a)** A19, A120, A144.
- **(b)** B24, B25, B47, B27, B124; B130; B83 through non-attainment (B170), transport (B89, B112, B128) or the signed current (B145); B13, B138, B141; the cluster and gap geometry at the heights the cameras need (B59).

### TG — Topological sub-unit gate
- **Path:** cubic defect trace norm `<1` → integer zero count vanishes → RH.
- **Established:** exact integer trace; enclosed multiplicity at most the trace norm; endpoint and Gaussian central-gap receivers.
- **(a)** none. **(b)** trace norm below one on every formation rectangle, or the Gaussian passage (B38).

### HF — Hodge / complete cells
- **Path:** complete arithmetic form `≥0` → Hodge index → RH.
- **Established:** blocks S1, S10; one positive square ⇔ RH and the exact index for Hecke characters and one Artin character [L*]; three-way classification [L*] (AH1).
- **(a)** A9, A13, A141, A143.
- **(b)** B6, B101, B104, B123, B8, B41, B10, B87, B88, B149, B152.

### HAT-C — Arithmetic-clock Green energy
- **Path:** one clock, or one fixed scattering height → the energy floor → `W≥0` on packets ⇔ RH.
- **Established:** the clock lies below Weil's form at every cutoff; a floor at one cutoff per large aperture gives RH [L*] (FF11); for every fixed `N`, RH ⇔ the corrected-energy floor ⇔ the raw-energy floor with its full defect; the tower is the completed-zeta quotient [L*] (HA1).
- **(a)** none.
- **(b)** the floor at one fixed height on all apertures: this is `W≥0` (B1). Negative Weil directions are negative at every cutoff.

### CHMD — Causal hyperbolic–modular duality
- **Path:** bounded prime wave, or the odd half-threshold bound → RH.
- **Established:** wave and Doob receivers; normalized prime-minus-pole decay uniformly over detail horizons.
- **(a)** none. **(b)** either side of the unnormalized wave bound; the complete odd sign (B35, B4).

### TH — Theta moment positivity
- **Path:** signed center-mixed jets → all-rank Hankel positivity → RH.
- **Established:** ranks `≤14` for `0<a≤½`; rank `N` from verified height `41+6(N+2)log(N+2)`; the adaptive critical Dirichlet sum is `ζ(½+ib)` up to `O(\|b\|^{−½})`.
- **(a)** A4, A5, A24, A42.
- **(b)** signed adaptive head near cancellation (B102); amplitude oscillation (B20); all ranks (B21).

### RN — Theta renewal
- **Path:** exclusion of joint nodes, or the theta-ground energy comparison → RH.
- **Established:** two-ended formula recovers Ξ with multiplicities; complete Weil sign ⇔ the energy comparison in theta ground coordinates.
- **(a)** none. **(b)** joint-node exclusion or the comparison (B36).

### WD — Ward / collision / long moments
- **Path:** cofinal long-mollifier moments, or collision bounds → RH.
- **Established:** RH ⇔ subpolynomial control of the mollified moment; a cofinal bound with fixed exponent and unbounded `θ` suffices; the twisted moment below the square root [L*] (TM1); a positive proportion of critical zeros from those moments at `θ=13/50` [L*] (LV1); finite Fejér means are signed logarithmic collision forms; block S5.
- **(a)** A18.
- **(b)** B62, B57–B61, B63: the cofinal criterion needs unbounded `θ`, the proved range stops at `θ<½`; quadratic tests of length `o(T²)` do not see a finite relocation [KR].

### LI — Paired Li / Cayley ladders
- **Path:** subexponential lower bound of the clock response, or the Cayley–Li sign → RH.
- **Established:** RH ⇔ the ladder sign on primitive vectors; RH ⇔ a subexponential lower bound of the clock response; `λ_n≥0` for `n≤314`; every paired Li coefficient is the limit per degree point of the comb form of a Laguerre tail [L*] (HF4).
- **(a)** A1. **(b)** the lower bound or the sign (B43): neither representation gives a sign uniform in `n`.

### SZ — Suzuki screw
- **Path:** rectangular Ward defect bounded below → RH.
- **Established:** completed Abel source bounded ⇔ RH; `\|A_N\|≤C√N e^{−c·vkScale N}`.
- **(a)** none. **(b)** bounded completed residual (B37, B1).

### PM — Physical model
- **Path:** scattering source → reflection Krein sign, ringdown rate, cavity-energy rate, or a count → RH.
- **Established:** block S7.
- **(a)** A26.
- **(b)** B68, B71, B87; B147; B114, B117, B171; B178. Polynomial filters erase finite exceptions; their sharp rate gives ZAL and leaves AAL.

### PTR — Cosine source
- **Path:** no exceptional point of the cosine producers on the open depth band → RH.
- **Established:** RH ⇔ the strict Laguerre sign at every `0<h<½`; ZAL gives finite nonreal defects at every positive shift.
- **(a)** none. **(b)** the sign below the VK boundary (B29); a prime-faithful lossless stack (B69). Bounded and Wiener pieces sharing zeros with ξ are excluded [L*] (CT1).

### JAS — Joint ancestry
- **Path:** level-one dressed positivity on large primes; or subpower control on finite power windows of square shells → RH.
- **Established:** RH ⇔ `JasDressedPSD 1` ⇔ positivity at level one on all large primes ⇔ positivity at infinity at every level above one [L*] (JA1); a signal bound `O(Z^b)` ⇔ the half-plane `b` and gives the level `b+½+ε` on large primes [L*] (FC1, SA-d); with `b=7/8` [X] the level `11/8+ε` holds; in world I the Gaussian signals of `μ` and `λ` have their top-residue asymptotics [L*] (TD1).
- **(a)** A118, A138, A139.
- **(b)** `JasDressedPSD 1` (B160); the signal bound below `7/8` (B161), through B174, B175, B184; the moving `k`-window control (B51). The bound at `7/8` is a strip and gives no level-one positivity.

### CTF — Chronological tail / Báez–Duarte
- **Path:** unit-bounded rows, BSY sign, cut-kernel mass → RH.
- **Established:** RH ⇔ unit-bounded rows reach every tolerance; RH ⇔ the BSY sign; RH ⇔ one fixed log-dilation equality.
- **(a)** none. **(b)** B52, B66, B91.

### HCF — Heat trace
- **Path:** two prime-log heat grids nonnegative at every degree → RH.
- **Established:** two-grid criterion at fixed offsets; detector degree explicit.
- **(a)** A1. **(b)** nonnegativity at every degree (B30).

### XN — Newton discs
- **Path:** line-centred self-map discs covering every zero → RH.
- **Established:** coverage and source-margin criteria.
- **(a)** none. **(b)** the cover (B32).

### BAG — Self-return
- **Path:** uniform head-target density → RH; transport → AAL.
- **Established:** strong recurrence ⇔ RH; `T^c` separated returns, `c>(30/13)(1−σ)`, exclude a zero right of `σ` [L*] (GR1); under a finite right layer normalized returns have only the zero limit [L*] (FF8); the resonator mean controls ζ in mean square [L*] (RM1).
- **(a)** none.
- **(b)** uniform target mass (B72); transport (B83, B89); breadth past VK (B97, B137); B145.

### EWU — Even sector
- **Path:** even blind minimum `≥0` at every aperture → RH.
- **Established:** RH ⇔ prime-blind positivity on the even cone; attained blind minimum `≥1/20` for `a≤(log 2+1/50)/2`.
- **(a)** A1–A3. **(b)** B4, B17, B44.

### GTA — Schur charge
- **Path:** cofinally small quartic charge → RH.
- **Established:** full-mode compactness and finite-prefix operator-norm convergence each ⇔ RH; cofinally small charge suffices.
- **(a)** none. **(b)** charge below `ε` at arbitrarily late stages (B33).

### OWU — Odd sector
- **Path:** archimedean-minus-prime positivity on odd tests → RH.
- **Established:** RH ⇔ positivity on odd tests with the polar hyperplane; unit-window floors.
- **(a)** A1–A3, A6. **(b)** B4, B17, B44.

### PBM — Regularized abscissa
- **Path:** convergence of the pole-regularized series right of `½` → RH.
- **Established:** exact convergence equivalence.
- **(a)** none. **(b)** the partial-sum bound (B53).

### RB — Robin / Nicolas
- **Path:** eventual extremal inequality → RH.
- **Established:** eventual criteria at colossally abundant numbers and at `lcm(1,…,n)`.
- **(a)** none. **(b)** the inequality (B54).

### SRT — Lag localization
- **Path:** the prime two-bump sign on a decisive sample → RH.
- **Established:** block S3 [L*]; two-bump apertures `a=4+(log p)/2` give prime packet rungs from verified heights [F].
- **(a)** A9.
- **(b)** B130; B6, B101.

### ACT — Single shift
- **Path:** the variation inequality at one shift → RH.
- **Established:** single-shift receiver; outward kicks of `{2,3,4}` cost `<991/1000` of the Lévy energy below `2c<log 5`; variance-free certificates fail for `c>273/400`.
- **(a)** A7, A140. **(b)** one shift uniform in profile (B44, B4).

### AIP — Incidence
- **Path:** global incidence allocation → RH.
- **Established:** exact allocation; VK signed cost.
- **(a)** A9, A13. **(b)** signed cost `C_σe^{2σr}` (B45); polar payment (B101, B104).

### SC — Stokes / Witt–Krein
- **Path:** bounded Gaussian-damped coupling, or glued index `≤1` → RH.
- **Established:** bounded Gaussian cone coupling ⇔ RH; glued index `=κ_ζ+1`; undamped coupling on a two-prime cone gives AAL.
- **(a)** none. **(b)** the damped bound; sublinear tensor loss (B39); ZAL for the undamped branch.

### ACS — Castelnuovo–Severi on the degree points
- **Path:** the comb sign, or subpolynomial growth of the power tails → step and smooth packet positivity → RH; or the prime-window floor.
- **Established:** block S10. The transfer between combs, step packets and smooth packets is closed in both directions, with an explicit block error [L*] (AG5, SP1–SP3). RH ⇔ every power tail converges ⇔ every power tail is subpolynomial [L*] (PT2, PT3).
- **(a)** A28, A41, A48, A141, A143.
- **(b)** B152, B149, B169, B88, B87; B130; B28; subpolynomial tails as `a↑½` (this is the width, B161 at every level); or force the packet index to be `0` or `∞` (B13).

### ECP — Endpoint character positivity
- **Path:** endpoint jets → coherent symmetric-group class functions → PSD character Grams at every rank ⇔ RH.
- **Established:** column projections nonnegative; Toeplitz minors through order 200; four mixed shapes.
- **(a)** none. **(b)** positivity at arbitrary rank (B86).

## 4. Candidates

Each needs its source-to-receiver step first (B81). Dormant pending a source mechanism: SEC, CDC/BSH, APF, EWJ, RFHM, WBF. Established facts are [F] unless marked.

| Candidate | Established | (a) Just work | (b) Open mathematics |
|---|---|---|---|
| S3 | a strip of depth `h` excludes heavy identity returns up to `exp(ηT)`; RH gives the transfer; under `Θ<1` the transfer ⇔ RH [L*] (FC2) | none | an arithmetic proof of the transfer (B148): with `Θ≤7/8` [X] the transfer is equivalent to RH; in Lean the premise `Θ<1` is A118 |
| SEC | Fock boundedness at every strip parameter ⇔ `Re s=½` | none | a ζ-selective bound from the Sonin source |
| CDC/BSH | marked prices agree iff `Re s=½` | none | arithmetic descent on actual zero fibres |
| APF | prime/grade trace reconstruction on real labels | none | full-divisor exhaustion and RH landing |
| EGC | zero-pair contour; count error `≤32ε²log T/T` | none | height-fibre isolation; outer landing |
| EWJ | all-depth reporter; norm exhaustion only on the blind plane | none | faithful endpoint admission |
| FEL | KL accounting | none | a predeclared history forcing the BSY sign |
| IRK | finite idempotent traces; Meyer–Ξ free resolution | none | projective lift identifying trace with Chern charge |
| MSC | unweighted `L²` discrepancy; conormal transport | none | Sonin/Weil sign landing |
| RFHM | support source; creation; strong exhaustion | none | RH-sufficient orientation law |
| W1C | Laguerre–Pólya approximants on one interval give RH; index-one limits give RH [L*] (IX1, FF11); an index-one realization of the right zeros gives RH [L*] (FF9) | none | an independent index-one family or realization (B146, B171) |
| WBF | Gram recovers magnitudes and phase class | none | arithmetic stream and Ξ landing |

## 5. Supporting programmes

| Programme | Established | (a) | (b) |
|---|---|---|---|
| FFA (floor-free arithmetic) | floors of mechanisms; non-attainment receivers; tangent datum, quantum, four sectors; every finite datum realized under one structure; unit gaps and their kills; certificates converge to `Λ`; projection statistics with the gradient law; positivity on the line of the pole; add-only systems; tangent data of `μ`, `λ` [L*] | A144 | B170–B173 |
| SPAL (sum–product arithmetic of the logarithm) | count rigidity; integer-norm fakes above and below `½`; obstructions for finite edits and zero density; the real fake zero of a deletion [L*] | — | B183 |
| SOSZ ScaleLocality | logarithmic and `√T` windows; exceptions; upper side; counts; local moments; finite top layers; counter-configurations at every sub-logarithmic radius [L*] | A58 | B130, B144 |
| SA (selective arithmetic) | trivial aperture in both aspects; feasible sets; the cancellation and depth ladder; exceptional heights with power saving; first conductor rung; three rungs under a half-plane; deep zeros at ζ density with positivity at a fixed aperture [L*] | A117 | B159, B156 |
| FCT (family continuation) | the family step with reciprocal kernels; principal and probe corrections; the principal row as an Euler product; arithmetic of the Poisson coefficients; signal as a Möbius sum; signal exponent = abscissa = level; the budget with vertex, floors, orders, corners, signed Gram and reflection invariants; the law of a twist family [L*] | A118, A139 | B161, B174, B175, B184 |
| MMD | cubic Gauss arithmetic, the cube identity, the cubic residue with Gauss coefficients; the quadratic large sieve over `ℤ[ω]`; the second Poisson reflection of a pair of rows as a separated identity with a Cauchy–Schwarz transfer to child energies [L*]/[F] (QS1, SR1) | A33, A118 | — |
| CTZ (constituents) | none with a zero in the bounded and the Wiener class; nonsummable residues; no `ℓ^p` transport; sizes on a circle [L*] | — | — |
| HFP (Hodge theory of a fixed part) | mass floors on ratio windows; robust index; unshifted index; Li tails [L*] | A143 | B152, B149 |
| AGZ | forced data; price paths; step packets with explicit block error; exact index for Hecke characters, Dedekind zeta functions, class characters and one Artin character; discriminant below first contact; sections in boxes; power tails [L*] | A141, A143 | B149, B169, B88, B87 |
| ELT | atoms; filters; growing-order reduction; near-diagonal row [L*]/[F] | — | B141, B145, B138, B13 |
| ZCG AbscissaLaws, Recurrence | split, atoms, tail law; graded recurrence [L*] | — | B13, B83, B138 |
| IRW / EFT / APD | the paired ξ model; continuous prime measures; Beurling rigidity; the meromorphic Euler firewall [L*]; relocation invisible to growing quadratic tests [KR] | — | B112 |
| IRP | index semicontinuity; flow criterion [L*] | — | B146 |
| AWT | fixed-part laws; cover-family tensor criterion [F] | — | B86 |
| SignFreePurityMechanisms | the Riemann hypothesis for the Goss zeta function; ultrametric Newton polygons [L*]; height separation ⇔ bounded prime traces [F] | — | B148 |
| ShortIntervalPrimesInProgressions | primes of every reduced class in `(x,x+x^θ]`; zero density and Littlewood's region for a character [L*] | — | — |
| HAT | clock; tower as a completed-zeta quotient; fixed-height floors ⇔ RH; unbounded critical inverse [L*] | A54 | B88, B117 |
| AHMH / BHR / ASH / CTH | cavity receivers, reflection Krein forms, halving descent, ringdown, count door [F]; ringdown rate ⇔ strip; horocycle exponents with Euler filters; the hyperelliptic count [L*] | A26, A41 | B68, B71, B87, B147, B178 |
| TTPO / CDGeo / PTT / TAPO | depth law, VK breadth, strip breadth, collective counts [F]; resonator means [L*] | A24 | B46, B97, B137 |
| ALST / AAD / RAC / APR | Stepanov degrees; producer rates [L*]; cut kernel; parity blindness [KR] | A30 | B48, B55, B67 |
| AHD / CACT | threshold identities, pole channel, ground states, classification; positivity below the eighth root [L*] | A9, A13 | B104, B123 |
| MZF / CDG | twisted moments below the square root; the Levinson gate with a positive critical proportion; centred cameras; mollifier trap [L*]/[F] | A18 | B62, B57, B59 |
| Census (IGP, TTPC) | `0.67250071`; positivity cost `≥1+3/π²` [L*] | — | B150, B57 |
| VHR / TCS | verified-height rungs; height 67; the double-exponential window height [L*]; rank and degree entries [F] | A1–A5, A142 | — |
| LogarithmicChowla | logarithmic averages, limit functionals, entropy decrement; the correlation `c(h)` of `λ` is within `6ε` of its mean over the prime dilates `c(ph)` at infinitely many scales [L*,S] (LC3) | A21 | — |

## 6. Decisive wall per route

| Wall | Routes |
|---|---|
| The minimal face: `P(p)≤A(p)+K` on the primes of logarithmic windows off power-thin exceptions | ACS, SRT, WL, HF, ZCG, HAT-C, PM (count), every window route through the prime two-bumps |
| Σ: the sign on every window, equivalently every rung, verification at every height, one positive square, the sign on step packets, feasible weights at every aperture | RW, EWU, OWU, ACT, CHMD, SZ, RN, AIP, SC, LI, TT (odd), HF, HAT-C, ACS |
| Σ: continuation at small time and the theta head at the critical zeros | ZCG (heat), PTR, LA, GTA, XN, HCF, PA, TH |
| Π: square-root precision and long moments past the height | WL, MC, SQF, PBM, RB, CTF, FU, CFC, RP, TT (endpoint), WD, TG |
| One scale: level one of the dressed aggregate (RH); a level above one = a half-plane = the exponent of the signal = the growth of a power tail. The level `11/8` is proved [X], not in the native graph. Below it the producer has three nested limits: the room `[13/15,7/8]` of its estimates, the floor `5/6` of its squares, the wall `2/3` of its frame [D] | JAS; MC (signal); S3; ACS (tails) |
| Γ: reflection and count | PM, ECP |
| The exceptional coordinate: world I (B13, Landing, DH; non-attainment) and world II (ZAL) | BAG, ZCG, JAS shell, SC undamped, WL thick runs, LA finite support |
| The dark range: prime sums shorter than the Vinogradov length in the Lean graph (with [X]: shorter than a power of the logarithm of the height), Dirichlet polynomials longer than the height | every route at all heights; BAG; TH certificates; WD; the centred type-II current of ELT; the rungs above one in the height aspect |
| Missing source landing | the twelve candidates |
