# Walls ledger — status quo

**Corpus checkpoint:** commit `65731ede04` with its working tree (2026-11-11). Fact log: `logs/review-1111-status-quo-facts.md` (identifiers in parentheses refer to log §3). Companions: [route-obstacles.md](route-obstacles.md), [route-unification-ledger.md](route-unification-ledger.md), [obstacles-summary.md](obstacles-summary.md).

Three wall families carry the frontier. **Σ** is the critical sign of the window form, **Π** the precision and production of the prime count, **Γ** the selection of ζ, the reflection of its zeros and their position in height. They meet in one minimal face, in one lattice and on one scale.

- **The minimal face.** RH ⇔ `P(p)≤A(p)+K` at the primes of arbitrarily late logarithmic windows `|log p−T|≤32 log(T+2)`, outside at most `Ce^{δT}` primes per window; the same with the upper side alone, with `ℕ`-counts on the surviving prime rays, with local even moments under one exponent, and with the absolute value [L*] (S1–S6). At the level of configurations no shorter window decides, also at ζ's density [L*] (S8, S9).
- **The lattice.** RH ⇔ exactly one positive square of the comb pairing on packets; the negative index of the defect is the number of distinct right zeros, for ζ and for every Hecke `L`-function of every number field [L*] (G4, AGZ6–AGZ8). At finite scale RH is the sign of explicit finite matrices on step packets and the eventual nonnegativity of the comb form on every ratio window [L*] (AGZ1, HFP1). Constant, contacts and tree lengths are forced [L*] (G1–G3).
- **The scale.** Saving `γ`, rung `κ`, depth `δ`, mollifier exponent `θ`, level `σ`, signal exponent `b`, floor exponent, moment order: `γ=δ=1/(2κ)=1/(2θ)`, `b=σ−½`, depth `=A/2k` [L*] (SA1, J1, FCT2, FFA1, FFA10). Every graded receiver is an equivalence at each level of this scale [D].
- **Off the scale.** Four kinds of statement have no exponent: a homogeneous floor, a unit gap, a certificate, an amplification over all orders. Each has a receiver and a kill in Lean [L*] (FFA).

[Frontier](../rh-current-frontier-map.md): **38 live formulations, 12 candidates**. [Scoped obstructions](../rh-killed-routes.md) separate failed mechanisms from open replacements.

**Status.** **Solved** (the face is a theorem), **Partially solved**, **Sharpened** (open, exact form a theorem), **Open**, **No-go** (mechanism refuted), **Classified**, **Reduced** (theorem-level equivalent named), **Settled** (a method question answered). **Strength:** RH, ≥qRH, ≥B56, AAL, sub, indep., identity, method, producer. **Evidence:** `[L*]` Lean statement read for this ledger; `[N]` declaration located by the corpus search, docstring read; `[F]`, `[KR]` stated by the frontier map and the scoped-obstruction ledger at the checkpoint; `[S]` module graded unfinished by the frontier map; `[D]` deduction; `[C]` classical; `[A]` assessment; `[X]` the external half-plane theorem, cached, unchecked, outside the native import graph.

Notation as in [route-obstacles.md](route-obstacles.md).

## Σ — critical sign

| Wall | Status | Strength | Content |
|---|---|---|---|
| Σ1 Weil's sign | Sharpened | RH | RH ⇔ `W≥0` on every window [N] ⇔ `Ψ` locally bounded on precontact intervals [N] ⇔ the floor on logarithmic prime windows [L*] ⇔ the raw scattering energy at one fixed height is at least minus its full defect [L*] (H1) ⇔ one positive square of the comb pairing [L*] (G4) ⇔ some feasible weight system at every aperture [N] ⇔ the sign on step packets [L*] (AGZ1) |
| Σ1b, Σ1k Subcritical regime; one critical multiple | Solved | sub | complete tilted-spline matrix positive definite at every fixed overlap eventually and at `c≤2K₁(log N)^{1/8}` [L*] (W11) |
| Σ1c–Σ1x Critical-curve calculus | Classified | sub / method | shell–pole payment, conductor resolution, receiving charges, top-collar Gårding, alias notch, Gamma reserves [F]/[KR] |
| Σ1u, Σ129 Threshold law | Solved (identities) | RH (all thresholds `=⊤`) | `0<R_PD=R_PSD=R_polar=R_halfline≤W=R_prim=R_high=inf_A windowThreshold(A)`; each infinite iff RH [F]; `R_polar=R_halfline` [L*] (C1) |
| Σ4 Finite index / heat count | Sharpened | ≥qRH; RH for index 0 | uniformly bounded `N(t)` ⇔ finite off-line support; `N(t)≤1` on times accumulating at `0` ⇒ RH; with finitely many nonreal zeros `N(t)` is their number for small `t` [L*] (FFA25) |
| Σ6 Rank and degree uniformity | Partially solved | RH | theta ranks `≤14`; all ranks reduce to the adaptive head [F] |
| Σ13–Σ15 Tensor amplification; deformation to a positive matrix; separable assemblies | No-go | — | [KR] |
| Σ20 Scheduled prime sums | Open | RH | FU, CFC, RP, LI receivers; no estimate on advancing histories [F] |
| Σ27 Window stages | Partially solved | sub | floors `(1/20000)/2^k` on `a_k`, `a_∞<0.3621`; a neighbourhood of `log 2` feasible for `w(2)` up to `a=181/500` [F]/[L*] (L14) |
| Σ28, Σ41 Negativity budget; aperture–depth duality | Sharpened / Classified | ≥qRH; sub | positivity on a camera aperture forces `\|depth\|<exp(−c log³(T/2π))` at height `T` [L*] (W12); a configuration with ζ's local counts hides a deep zero at `T` to aperture `(log T)/36` [KR] |
| Σ42, Σ53, Σ57 Markov, size-only payment, Perron | No-go | — | [KR] |
| Σ49 Reality by continuation | Sharpened | RH | RH ⇔ every zero of every `H_t`, `t>0`, is simple [L*] (C8) |
| Σ56, Σ66, Σ113 Onset aperture; contact; restoring bound | Sharpened | RH | RH ⇔ `Ψ` and `L=artanh r` locally bounded [N]; RH ⇔ no aperture carries a null mode [D] (Σ168) |
| Σ73–Σ80 Hausdorff rows, heat grids, theta endpoint, renewal, cosine, quartic charge, cubic gate | Sharpened | RH | exact receivers of PA, HCF, TT, RN, PTR, GTA, TG [N] |
| Σ82 Finite-rung principle | Partially solved | sub | `RHVerifiedThrough 67`; verification through `windowHeight(a)` ⇒ the sign on `[−a,a]`; every prime cutoff lies below `primePacketRung(T)` for large `T` [L*] (J2–J4) |
| Σ98, Σ133 Theta heads | No-go (fixed heads); Sharpened | RH (all ranks) | [KR]/[F] |
| Σ116, Σ117 Weighted Gårding; typical-height sign | No-go (full horizon); Solved (in law) | sub | at aperture `κ log log T` the paired sign on bounded shapes fails on a set of heights of measure `≤T^{1−1/(2κ)+ε}` [L*] (SA2) |
| Σ135, Σ139 Pole channel; half-line ground states | Sharpened | method | RH, or `R_polar<W`, or `R_polar=W` finite with every critical half-line ground state polar-orthogonal [L*] (C3); the third case is B104 |
| Σ140 Holomorphic multipliers | No-go | — | [KR] |
| Σ137, Σ138, Σ141, Σ144, Σ145, Σ148, Σ151 The minimal face | Solved (identity) | RH; ≥qRH at `p^σ` | floor off `Ce^{δT}` primes; upper side on undeleted windows; `ℕ`-counts on the surviving rays; local even moments with one exponent; absolute form [L*] (S1–S7); `√T` and two-prime windows [F] |
| Σ146, Σ152 Resolution of the minimal face | Settled | method | a tempered model with unattained top passes every floor below the logarithmic radius, also density-matched and at prime samples [L*] (S8, S9); `n` modes of frequency `≥Γ` with one sign on a length `L` have `ΓL≤nπ` [L*] (S11) |
| Σ147 Bounded windows against world I | Solved (receivers) | AAL | a top of at most `k` positive ordinates breaks every floor on every late window of length `(k+1)π/67`; floors with constants depending on `k` give AAL [L*] (S10, S12); a one-sided floor on windows of one length has a finite-stratum model [L*] (FFA8) |
| Σ149 Short windows and deep-ordinate separation | Classified | method | [KR] |
| Σ150, Σ172 Regulated energies | Solved (identity); No-go (as a source) | RH (sign) | the clock lies below Weil's form at every cutoff; a floor `−C‖f‖²` at one cutoff per large aperture gives RH; a negative direction of the limit is negative at every cutoff [L*] (FFA24) |
| Σ153 Hodge index of the degree-point pairing | Solved (identity) | RH | RH ⇔ exactly one positive square on packets; positive index `≤1+#{ρ: Re ρ>½}` [L*] (G4) |
| Σ154, Σ165, Σ166 The comb form at finite scale | Solved (identity) | RH (every ratio) | RH ⇔ `𝔚_{3K+1}≥0` on step packets of `3KR` blocks, all `K,R` ⇔ for every ratio and `η>0` eventually `−ηΣc²≤` comb form ⇔ eventual exact nonnegativity on every ratio window ⇔ a positive mass floor `γ(Q)` on each ratio window [L*] (AGZ1, AGZ2, HFP1, HFP2); floors on block-constant divisors give RH [L*] (J11) |
| Σ155, Σ158 Forced data | Solved (identity) | RH (sign) | `CombBezoutShift c ⇔ c≤0 ∧ RH`; one contact changed by `t`: Bézout ⇔ RH ∧ `2\|t\|/√n₀≤c`; tree of `p`: Bézout ⇔ RH ∧ `ℓ=log p` [L*] (G1–G3) |
| Σ156 The exceptional square | Solved (no gap) | method | every dominated twisted part is positive to `log log q−η` and the dominated box fails at `log log q+η` [L*] (L1, L2); a real zero repels the other zeros of its character [L*] (G12); the sign at `log log q+η` forces primes with `χ(p)=1` and with `χ(p)=−1` below `e^{2η}log²q` [L*] (SA3) |
| Σ157 Selectivity of windows | Solved | method | for `2a<log 2` feasibility does not depend on the weights; box law above first contact; a neighbourhood of `log 2` feasible up to `a=181/500` [L*] (L10, L14, G11) |
| Σ159 Jets and contacts in normal form | Solved (identity) | identity | [F] |
| Σ160, Σ170 Feasible weights and certificates | Solved (identity); No-go (freedom) | RH | RH ⇔ every aperture admits a feasible system; ¬RH ⇔ some aperture admits none [N]; for every `n≥2`, `ε>0` every system feasible beyond some aperture has `\|λ(n)−Λ(n)\|≤ε`; feasibility at an aperture ⇔ spectral kernels positive definite on node intervals; tapered kernels are transforms of finite positive measures [L*] (FFA21–FFA23) |
| Σ161 The trivial aperture | Solved (sharp) | method | conductor: floor for every dominated system at `a≤log log q−η`; the Liouville twist, `−Λ`, and `Λ` without pole plane fail at `log log q+η`; trivial aperture `log log q+o(1)`. Height: floor at `a≤log log\|t\|−η`; a dominated system fails at `log log t+log(π/2)+η` [L*] (L1–L5, SA6) |
| Σ162 The exchange rate | Solved (receivers) | ≥qRH (a rung above one) | one theorem for the saving, the rung, the companion zero and the mollifier depth [L*] (SA1); the sign on the polar packets bounds the Riesz mean at square-root scale [L*] (L7); a height is a conductor of the twisted contacts [L*] (L8); bounded shapes do not decide feasibility [L*] (L11) |
| Σ163 Depth on the ladder; clusters | Settled (configurations); Open (ζ) | method | for every `a>0`, `0<δ≤½` a tempered configuration at ζ's density is positive on `[−a,a]` with zeros of depth `δ` at unbounded heights [L*] (SA5); for ζ and primitive characters the sign on a rung forces a companion of a deep zero [L*] (L9); arithmetic cluster exclusion is B156 |
| Σ164 Level-one dressed positivity | Solved (identity) | RH | RH ⇔ `JasDressedPSD 1` ⇔ level one on all large primes ⇔ positivity at infinity above every level `σ>1`; a level `σ≥1` gives the half-plane `σ−½` [L*] (J1); level one gives AAL, B56 and `Θ=½` [L*] (L13) |
| Σ167 Index in the aperture | Solved (identity) | identity | immediately right of an aperture the index is negative index plus nullity; resonant apertures finite below every bound [F]; `r≤#`right zeros ⇔ eventually `r≤` robust comb index [L*] (HFP3); the unshifted comb index lies between the aperture index and index plus nullity [L*,S] (HFP4) |
| Σ168 Null modes | Sharpened | RH | RH ⇔ no aperture carries a null mode of the restricted form; with finitely many off-line zeros finitely many resonant apertures carry the whole index [D]; a topological computation of the index is B179 |
| Σ169 Paths | Settled (no transport) | method | price path at every `n₀≥2`: zero sum plus a square, monotone, threshold on packets of length `L`; on all packets Bézout along the path is RH at every parameter; the tree-length path exists at `2` only [L*] (AGZ3–AGZ5) |
| Σ171 Order of the verification height | Open | sub | `log log log windowHeight(a)=c·a^{4/3}+log 138+o(1)` for the construction [F]; the symbol is nonnegative above `exp(C+2ψ₁(e^{2a}))` for every test [D]; margin ceiling `exp(11a/2−πe^{2(a−2)})` [KR]; a lower bound for the margin of the verified part is missing (A132, B176) |

## Π — precision and production

| Wall | Status | Strength | Content |
|---|---|---|---|
| Π1, Π4 Global law; window precision | Solved (equivalences) | RH | classical one-sided receivers [N] |
| Π2 Deciding input | Open | RH | no native unconditional input at square-root precision [F] |
| Π3, Π67, Π70, Π71 Producer cost, ceilings and rates | Solved (exponent scale) | sub / ≥qRH / RH | rate `≥c₁/(√K(1+log K))` for alphabet `≤K` [L*] (W2); rates `K^{−a}` for all `a<½` give RH [F] |
| Π7, Π151, Π166 Census | Partially solved; No-go (positivity) | sub | simple critical zeros `≥0.67250071` [L*] (C4); positivity cost `≥1+3/π²>13/10` for the full Fourier positivity class at every bandwidth; a pair-density deficit supports diagonal mass `<13/10` only [KR] |
| Π22, Π65 Near-line density; log-mean | Reduced | sub | depth density `o(T)` open (B57) [F] |
| Π40, Π148 Strip self-improvement; the return transfer | Open; Settled (strength) | ≥B56; RH under a strip | fails for `ξ(s+a)ξ(s−a)` [KR]; the return transfer gives `Θ<1⇒RH`, and under `Θ<1` it is equivalent to RH [L*] (J12, FCT4) |
| Π41, Π42, Π56, Π161 Mean-value ladder | Solved (range `θ<½`); Sharpened | RH (receivers) | RH ⇔ cofinal polynomial boundedness of the Möbius-mollified second moment with one exponent [N]; dyadic boundedness at `θ>½` leaves finitely many zeros beyond depth `1/(2θ)+ε` [L*] (J6); twisted moments for `θ<½` with main terms and power saving, also for the first two displacement derivatives [L*] (J5)/[F] |
| Π46, Π55 Parity blindness | No-go | — | every bilinear statement is invariant under the Liouville twist [L*] (W3) |
| Π51 Vinogradov–Korobov barrier | Open | sub | every native unconditional pointwise saving is VK [F] |
| Π53, Π54, Π80 Cluster wall; negative moments; short-sum barrier | Open | sub | [F] |
| Π66, Π125, Π126, Π146, Π153 Integrality; Stepanov degrees; one prime | Solved (price) | RH (degree bound) | `\|Σ_{n≤p}e(an^p/p²)\|≤5p^{11/12}` [F] |
| Π93 Möbius as a cubic Gauss coefficient | Solved (identity); descent open | past VK | cube identity [L*] (W5); the cubic residue with normalized Gauss coefficients on squarefree-times-cube support; Gauss-series formulas for `Re s>2` [F]; open: removal of the cube sum (A118) |
| Π94, Π128–Π130, Π137 Returns of the prime orbit | Partially solved | sub; ≥qRH in a strip | near-total returns need `log t>(log y)^{3/2−ε}` [F]; under `Θ≤b` heavy returns need `log t≥c·y^{1−b}` [L*] (SA4); resonator means [L*] (W8)/[F] |
| Π102, Γ221 One-structure worlds | Solved (countermodels) | — | every tangent datum occurs in a finite symmetric configuration, a nonnegative density with a simple pole, an Euler product over natural norms with linear counting and the prescribed multiplicities, and for `Θ>17/30` over rational primes with repetition [L*] (FFA12–FFA15, N3); a continuous Beurling system with integer count `N(x)−ρx−C→0` has a one-off pair [N]; given `Θ<1`, a meromorphic Euler product over the rational primes with bounded nonnegative multiplicative coefficients and polynomial growth of itself and its inverse has exactly one pair right of `Θ` and a pole in the left strip; the Euler product read through the zero configuration has floor `½` [L*] (M1, M2) |
| Π105, Π127 Farey, nerve, orientation cover | Solved (identity) | RH (weight `½`) | centred cover count `=M(x)` [L*] (C12) |
| Π112–Π114 Exceptional rank; thick crude count | Sharpened | AAL; RH with attainment | RH ⇔ attained top ∧ thick `O(√X)` deviation [N] |
| Π141, Π142, Π145 Gauge family; the fixed part | Classified; No-go | method | fixed-part laws [N]; in a cyclotomic tower the base has weight `1/d`, among the class characters `1/h` [L*] (G10, AGZ8) |
| Π147, Π155, Π156 The arithmetic square; sections | Classified | — | planar restriction is an equality of ideals [L*] (G7); sections of the first `N` graphs in aligned boxes: volume over `N!` [L*] (AGZ10) |
| Π149 Centred Vaughan currents | Solved (reduction); bound open | AAL | cofactors `≤3t⁷¹`, filtered error controlled, unweighted near-diagonal row summable [F]; open: the prime-weighted sum (B145) |
| Π154 The carry class | Classified | — | [KR] |
| Π158 Reciprocity sources | Classified (local); Settled (designs) | producer | `g(χ)^n=−card F+z(μ−1)²` for odd order `n>2`, `χ(−1)card F+…` for even order [L*] (F3); `g(χ)g(φ)=(−1+z(μ−1)²)g(χφ)` [L*] (FCT9); the one-variable cubic/sextic design is the best of the tested designs (Π163) |
| Π159, Π162 Family continuation | Reduced | ≥qRH | frame for all ray class characters with holomorphic corrections [L*] (FCT5); `Θ≤b` ⇔ signal `O(Z^{b′})` for every `b′>b` [L*] (FCT2); over `ℚ(ζ₃)` the two estimates with common exponents below every `β>σ₀` give `Θ≤σ₀` [L*] (N5); `[X]`: `σ₀=7/8`; natively open (B161) |
| Π160, Π163 The budget of the probe | Settled | method | boundary `7/8` at every redistribution of the two scales [L*] (J10); the published geometry is a vertex: boundary in `(7/8−1/4000,7/8]` with its row count; floor bin `13/15`; order floor `1−4/(5n)`; conductor corners `8/9`, `25/28`, `49/54`; two or more row variables `≥1`; reflected rows through the same twists return the zero; without the dual-length term `≥5/6`, at order `n` `≥1−1/n` [L*] (FCT11–FCT17); no cancellation over the exceptional frequencies of a coprime column pair [L*] (F4); positive form: boundary `½+(1−1/n)θ/2` for a generic mean square over twists of norm up to `Z^θ` [L*] (M3) |
| Π164 The half-plane map | Solved (receivers) | — (given a half-plane) | `Θ≤b` gives the rung `(2b−1)κ<1` for the centred contacts, large-prime positivity above the level `b+½`, return-free windows [L*] (SA4) |
| Π165 Levinson detector below the square root | Partially solved | sub | the detector is three moments plus jets and two taper terms; linear mollifier: explicit main expression plus `O(T^{7/8})` [F] ([S] for the remainder); open: the main expression (A134) |

## Γ — selection, reflection, position

| Wall | Status | Strength | Content |
|---|---|---|---|
| Γ1 Self-return | Open | RH | strong recurrence ⇔ RH [N] |
| Γ15, Γ33, Γ35, Γ167 Rigidity of ζ | Solved (classification) | method | countable Beurling systems with an `L²` defect are the rational primes [L*] (C13); count `n+o(log n)` forces the rational primes [KR]; positive continuous prime measures keep every zero with an integrable defect [L*] (W1) |
| Γ24, Γ62, Γ95 Mayer reflection; Hecke dispersion; Krein flux | Sharpened | RH | [F] |
| Γ67, Γ183 Abscissa split and atoms | Solved (identity) | identity | RH ⇔ ZAL ∧ B13 ∧ Landing [F]; `Θ<1⇔Θ∞<1` [L*] (S13); Landing is local below no height [L*] (S14) |
| Γ68, Γ69, Γ220 AAL and its receivers | Open; Solved (receivers) | sub | non-attainment of the trace on windows, of `ψ(x)−x`, at the primes; one growth exponent for all even window moments; the four-sector classification; excluding a nonzero trigonometric-polynomial limit gives AAL [L*] (FFA4–FFA7, FFA9, N1, N2); the receivers hold for every tempered conjugation-symmetric configuration |
| Γ73, Γ145 One-off countermodels; firewall | No-go (positive data) | — | the half-plane abscissa law fails for continuous Beurling systems with regular integers, for Euler products over integer norms and over rational primes, and for one reflection pair [N] (X1) |
| Γ86, Γ121, Γ122, Γ226 Modular horizon | Solved (identity) | RH (rate) | RH ⇔ quarter ringdown ⇔ horocycle rate `y^{¾−ε}` [N]/[F]; universal horocycle exponent `sup=1−Θ/2`; with a nonzero Euler polynomial filter `sup=1−Θ∞/2`; no filter passes `3/4`; ZAL ⇔ filters approach `3/4`; AAL ⇔ no filter accelerates [L*,S] (N8) |
| Γ89, Γ148, Γ157 Physical positivity; modular conjugation; half-sided inclusions | No-go | — | [KR] |
| Γ96, Γ125, Γ154, Γ227 Count law; count door | Solved (curves); Sharpened (ℤ); No-go (sections) | RH | hyperelliptic defect is an `ℕ`-count quadratic on rays [L*] (C11); RH ⇔ an `ℕ`-count with Tate limit the integer probes [N]; ⇔ counts on the surviving prime rays [L*] (S4); the count of sections in boxes has no quadratic term [L*] (AGZ10) |
| Γ137, Γ161, Γ181 Positive annihilators | No-go | — | [KR] |
| Γ141, Γ185, Γ218 The functional equation admits approaching remainders | No-go | method | the Riemann functional equation, Gamma factor, residue one, order `≤1` and the count of ξ within one allow simple zeros off the line approaching it [L*] (C6) |
| Γ182 The landing law | Sharpened; Settled (method) | sub | open for ζ as an atom |
| Γ184 The Deuring–Heilbronn sector | Classified (models); Open for ζ | sub | graded repulsion refuted on Euler products over natural norms [L*] (S15); a real zero repels the other zeros of its character [L*] (G12); B141 open |
| Γ192 Two worlds | Solved (identity) | identity | `Θ<1⇔Θ∞<1`; ¬quasi-RH ⇔ `Θ=Θ∞=1` ∧ AAL [L*] (S13) |
| Γ195, Γ222 Index law and unit gaps | Solved (law); No-go (regulators) | RH | RH ⇔ ξ is a limit of conjugation-real functions with at most one right zero [L*] (C5); AAL ⇔ at most one or infinitely many zeros right of every line [L*] (FFA5); a mean below the quantum `2\|B̂\|²` excludes a zero [L*] (FFA17); unit gaps pass to limits; `Λ(s)/Λ(s+N)` has a unit gap ⇔ RH; the heat flow has the count of its limit; an index-one realization gives RH [L*] (FFA20, FFA25, FFA26) |
| Γ196, Γ197 One glued carrier; adelic Green kernel | No-go; Classified | — | invariant glued carrier refuted [KR]; no bounded critical Green matrix; the critical spherical integral is not integrable [L*] (H3) |
| Γ198, Γ213, Γ216, Γ225 One matrix for ζ and for number rings; exact index | Solved (identity) | identity | the defect of ζ with finitely many primitive Dirichlet characters has index zero iff none has a right zero [L*] (G5); the same count for every primitive ray class character of every number field, for a Dedekind zeta function through its ideals, and for the class characters together [L*] (AGZ6–AGZ8); below the first contact a large discriminant gives the inequality with margin [L*] (AGZ9); B13 ⇔ the supremal index on real packets is `0` or `∞` [L*] (S16) |
| Γ202, Γ214 The scattering tower | Solved (identity) | RH (sign) | the tower is the logarithmic derivative of `Λ(s)/Λ(s+N)` plus Robin and polar terms; for every `N`, RH ⇔ the corrected-energy floor ⇔ the raw-energy floor [L*] (H1, H2) |
| Γ203 Separation by the height | Solved (receiver) | RH | ordinate injectivity ⇔ RH [N]; optimal ⇔ greedy in the Carlitz–Goss calculus [L*] (J8) |
| Γ206 Graded recurrence | Solved (receiver) | ≥qRH (the return count) | `T^c` separated returns, `c>(30/13)(1−σ)`, exclude a zero right of `σ` [L*] (C10) |
| Γ208 Castelnuovo–Severi on the flow | Solved (identity) | RH | RH ⇔ the prime lag function is positive definite on `ℝ` [N] |
| Γ209, Γ212, Γ215, Γ224 Constituents | Solved | method | no bounded holomorphic Dirichlet series on a half-plane and no Wiener expansion on a strip has a zero with its zeros among those of ξ; one interior zero of a Wiener expansion gives nonsummable residues and excludes every `ℓ^p` transport of its zeros to zeros of ζ; every box has a Dirichlet polynomial with exactly the zeros of ξ, of unbounded length [L*] (CTZ1–CTZ4, K3, K4); the jump law with summable poles [L*] (K2) |
| Γ217 Structures of the square return identities | No-go / Classified | — | planar restriction; split norm; own comb; tower weight; discriminant margin below first contact [L*] (G7–G10, AGZ9) |
| Γ219 Finite strata with both structures | Open | method | every calibration of an atom in the corpus drops a structure; Selberg zeta functions of surfaces with small eigenvalues have both and a finite real stratum [C]; the stratum of congruence quotients is empty below `3/16` [L*] (J7); B157 |
| Γ223 Symmetrization | No-go (linear, additive) | method | an entire symbol with real part tending to `0` that is monotone under splitting has zero real part on the line; additive functionals of the depths are functions of the inner masses [L*] (FFA28, FFA29); nonlinear functionals are B172 |
| Γ228 Replication | No-go (normal families) | method | under a finite nonempty right layer every locally uniform limit of normalized translates along a phase return vanishes [L*] (FFA19) |
| Γ229 Pure objects as certificates | No-go | method | the pencils `ξ(s+h)+ξ(s−h)`, `h>0`, and the cleared Eisenstein constant term at every height are no Dirichlet series over their dominant half [L*] (FFA27, N4 [S]) |

## Scoped no-gos and surviving replacements

| Boundary | Exact scope and survivor |
|---|---|
| Sizes of the contacts | positive to rung `1−o(1)`, the dominated box fails at `1+o(1)` (Σ161). Survivor: a saving that fails for the Liouville twist (B159) |
| Windows below the logarithmic radius; one-sided floors on windows of one length | configurations, also density-matched; a finite-stratum model at every length (Σ146, Σ147). Survivors: the logarithmic radius; two-sided non-attainment; floors at every length |
| The explicit formula, positivity, Euler products over integer norms, linear counting as a constraint on a finite top layer | every tangent datum is realized (Π102). Survivor: unit multiplicity of every integer and the exact functional equation |
| Regulators as a source of a unit gap, a sign or an index bound | the clock lies below its limit; tower and heat flow have the count of their limit; price paths and tree lengths are RH at every parameter (Σ150, Σ169, Γ222). Survivor: a realization with one negative square (B171) |
| Certificates other than `Λ` | converge to `Λ`; pure objects with ζ's Gamma factor are no Dirichlet series (Σ160, Γ229) |
| Linear statistics and additive depth functionals as monotone quantities under projection | Γ223. Survivor: nonlinear functionals (B172) |
| Replication of a zero through a normal family of translates | Γ228. Survivor: prime transport, signed currents (B89, B145) |
| Amplification over the order of a window moment | all orders with one exponent are sup bounds; one order reaches depth `A/2k` (Γ220) |
| The Gauss-sum probe below `13/15`; other twist orders, more row variables, other conductors; reflected rows through the same twists | Π163. Survivor: a generic mean square over a shorter twist family by a bound that does not pass through the twists (B175, B177) |
| Bounded and Wiener constituents with a zero | none (Γ224). Survivor: exact finite-height matching with growing length |
| Sections of the square, of the tower, of the planar square; section counts in boxes | identities; no quadratic term (Π155, Γ227). Survivor: counts on prime rays with the plane defect as limit, equivalent to RH |
| A free weight, constant, scale or tree length; an own comb; a per-degree tower limit; a path | forced, failing, or RH at every parameter (Σ155, Σ169, Γ217) |
| Landing or repulsion from one structure; rigidity of positive prime measures | models (Γ218, Γ184, Γ15). Survivor: joint inputs; a calibration with both structures (Γ219) |
| Bilinear statements as parity-sensitive | invariant under the Liouville twist (Π46). Survivor: reciprocity identities (Π158) |
| Mean values below the height as detectors of single zeros | finite relocation is invisible to quadratic tests of length `o(T²)` [KR]; proved range `θ<½` (Π161) |
| Positivity alone as a census certificate at 70% | cost `≥1+3/π²` (Π166). Survivor: arithmetic upper control beyond frequency one (B150) |
| The return transfer as a step from a strip to the line | it is RH under a strip (Π148) |
| Families as producers by averaging | fixed part; weights `1/d`, `1/h` (Π145). Survivor: a family used through its rightmost zero (Π159) |
| Markov, Perron, size-only payment, floor tower, universal multipliers, fixed theta heads, positive Laplace mixtures; Schur, KMS, internal modular conjugation; bounded-height Diophantine certificates against returns | as recorded in the scoped-obstruction ledger [KR] |

## Bridges

| Bridge | Anchor |
|---|---|
| One inequality per prime: Weil test = Stepanov count = count on a prime ray = sign-free trace = upper side, on logarithmic windows off power-thin exceptions | SOSZ [L*] |
| One matrix on the integers: Weil's form on packets = comb form → zero sum; exact index = number of right zeros, for every Hecke character | AGZ, HFP [L*] |
| One scale: `γ=δ=1/(2κ)=1/(2θ)`, `b=σ−½`, depth `=A/2k`, floor exponent `=` floor | SA, RHTower, FCT, FFA [L*] |
| Finite scale: step packets = ratio windows = block-constant divisors; robust index = right zeros; index jumps = nullities | AGZ, HFP, ACCE [L*]/[F] |
| A height is a conductor of the twisted contacts; a floor is a conductor | SA [L*] |
| The half-plane route = two estimates for one completed sum over `ℚ(ζ₃)` | FCT [L*] |
| Möbius = cube of a cubic Gauss sum; one Jacobi sum carries the sign at every order above two | MMD, FCT [L*] |
| AAL = non-attainment = unit gap = no accelerating filter = absence of a trigonometric-polynomial limit | FFA, BHR [L*] |
| B13 ⇔ the packet index is `0` or `∞` | ACS [L*] |
| Feasible weights at every aperture ⇔ Bézout at every aperture ⇔ positive definite spectral kernels on intervals; certificates → `Λ` | ASRP, AGZ, FFA [N]/[L*] |
| Regulated energy at a fixed height + jump tail = the closed Weil form; the tower = `Λ(s)/Λ(s+N)`; every regulator has the count of its limit | HAT, FFA [L*] |
| Window sign ⇐ verification height; the symbol is nonnegative above a double-exponential frequency | VHR, SA [L*]/[D] |
| Critical curve: `R_polar=R_halfline≤W`; three-way classification | AHD [L*] |
| The Li ladder = comb forms of Laguerre tails per degree point | HFP, AGZ [L*] |
| Recurrence against density + the jump law + prime contraction ⇒ no constituents | CTZ [L*] |
| Mertens level = producer rate = orientation cover | AAD, HAT [L*]/[F] |

## Strength of the open walls

- **RH:** Σ1, Σ6 (all ranks), Σ20, Σ49, Σ56, Σ66, Σ73–Σ80, Σ113, Σ129 (thresholds `=⊤`), the minimal face (Σ137–Σ151), Σ150 (sign), Σ153, Σ154/Σ165/Σ166 (every ratio), Σ155 (sign), Σ160, Σ164, Σ168, Π2, Π42, Π126, Π127, Γ1, Γ24, Γ62, Γ95, Γ121, Γ122, Γ154, Γ195, Γ203, Γ208, Γ214 (the floor), Γ222 (a unit gap of the tower).
- **≥qRH:** Σ4, Σ28, Σ162 (a rung above one), ZAL, Π3 (polynomial rate), Π159/Π162 (the two estimates; `[X]` outside the native graph), Γ206 (the return count).
- **≥B56:** Π40.
- **AAL:** Π114, Σ147 (the floors), Γ220 (non-attainment), Π149 (the weighted current).
- **sub:** Σ27, Σ82, Σ116, Σ117, Σ171, Π7, Π22, Π51, Π53, Π54, Π65, Π80, Π94, Π161 (past the square root), Π165, Γ68, Γ182 (landing as an atom), Γ184 (DH for ζ), B13, B174.
- **method / producer / indep.:** Σ135 and Σ139 (B104), Σ163 (B156), Σ168 (B179), Σ171 (B176), Π158 and Π163 (B175, B177, B180), Π162 (B181), Γ219 (B157), Γ222 (B171), Γ223 (B172), Γ226 (B178).
