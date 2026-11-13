# Walls ledger — status quo

**Corpus checkpoint:** `fdc9cfc40f` (2026-11-13), working-tree sources included. Fact log: `logs/review-1311-status-quo-facts.md` (cited as "log §n"). Companions: [route-obstacles.md](route-obstacles.md), [route-unification-ledger.md](route-unification-ledger.md), [obstacles-summary.md](obstacles-summary.md).

Three wall families carry the frontier. **Σ** is the critical sign of the window form, **Π** the precision and production of the prime count, **Γ** the selection of ζ, the reflection of its zeros and their position. They meet in one inequality per prime, one finite-scale matrix, one cover of the time plane, and one scale.

- **The minimal face.** RH ⇔ `P(p)≤A(p)+K` at the primes of arbitrarily late logarithmic windows, outside `Ce^{δT}` primes per window; equivalently the upper side, counts on surviving rays, copositive prime planes; for two fixed primes, a bound at their difference lags within `r√T` of arbitrarily late `T` [L*] (log §4.8, §4.9, §4.12). No window below the logarithmic radius decides [L*].
- **The finite-scale matrix.** RH ⇔ on every window, disjointly supported nonnegative packets satisfy the Hodge inequality `N(x,x)N(y,y)≤N(x,y)²` whenever `N(x,x)<0` ⇔ every bound state has one sign [L*]. Certified: one bound state for `50J≤53R`, none on narrow windows `16J≤R`, the first blocks of ratio four [L*] (log §4.1, §4.7, §4.9).
- **Binding.** The two halves of a window of ratio four glue through one pair of charges only at block size one; every model of their coupling of rank `r` with `600(r+1)≤H` leaves two bound states; with the contacts of 2 and 3 weakened or Liouville-twisted the window has two bound states [L*] (log §4.1). The sign at ratio three and four with the true contacts is open (B192).
- **The path.** The index of the restricted Weil form is the number of crossings of the aperture path; the supremum at energy zero is the number of right zeros; RH ⇔ no crossing [L*] (log §4.8, §4.10).
- **The critical object.** RH, or a finite critical ratio with a critical half-line state: unique up to sign, outer, cyclic, without Laplace zeros in the closed right half-plane, stable along the energy branch [L*] (log §4.2). Its charge is undecided (B104).
- **The cover.** RH ⇔ no positive real branch time of the heat cover ⇔ the conjugation monodromy is trivial at every positive real non-branch time; over forward times the cover is tame: no escape, finitely many branch times on boxes; every forward branch time is a nontrivial monodromy, and a monodromy group that preserves every pair `{z,−z}` gives RH [L*] (log §4.4, §4.11, §4.13, §4.14).
- **The scale.** Saving, rung, depth, mollifier exponent, level, signal exponent, twist exponent, critical-comb growth, relaxation rate: one number [D]. `b=7/8` is `[X]`; the open part is `½<b<7/8`.
- **The producer.** One class with an exact end: square-root cancellation gives `2/3`; the frame of every `6r`-periodic Gauss pairing has its fixed point at `(4r−1)/(6r−1)≥3/5` [L*] (log §4.8).
- **The door of world I.** Among countable systems with unit multiplicities a defect decaying at any rate forces the rational primes; among positive real weights defects grow arbitrarily slowly with prescribed off-line zeros; fake edits have defect energy `≥cT log T`; an odd fake zero needs a count exponent of at least half its real part [L*] (log §4.3, §4.10).

[Frontier](../rh-current-frontier-map.md): **38 live formulations, 12 candidates**. [Scoped obstructions](../rh-killed-routes.md).

**Status.** **Solved** (the face is a theorem), **Partially solved**, **Sharpened** (open, exact form a theorem), **Reduced** (theorem-level equivalent named), **Open**, **No-go** (mechanism refuted), **Classified**, **Settled** (a method question answered). **Strength:** RH, ≥qRH, AAL, sub, indep., identity, method, producer. **Evidence:** `[L*]` Lean statement read at the declaration and recorded in the fact log; `[doc]` module docstring; `[F]`, `[KR]` stated by the frontier map and the scoped-obstruction ledger at the checkpoint; `[S]` unfinished per the frontier map; `[D]` deduction; `[C]` classical, from memory; `[A]` assessment; `[X]` the half-plane `Θ≤7/8`, taken as proved; in the Lean source a statement without hypotheses (`riemannZeta_ne_zero_of_seven_eighths_lt_re`, `riemannZeta_zero_mem_quasiRH_strip`; statements and final assembly read, log §4.14), graded `[S]` by the frontier map: validation of its dependency chain is just work (A118); its consequences on receivers are `[D]`. **≥qRH** is open where it gives a half-plane below `7/8`.

## Σ — critical sign

| Wall | Status | Strength | Content |
|---|---|---|---|
| Σ1 Weil's sign | Sharpened | RH | RH ⇔ `W≥0` on every window [F] ⇔ `Ψ` bounded on precontact portions [F] ⇔ the floor on logarithmic prime windows [L*] ⇔ feasible weights at every aperture [L*] ⇔ no crossing of the aperture path [L*] ⇔ the Hodge inequality on every neutral window [L*] ⇔ subpolynomial critical comb [L*] |
| Σ1b, Σ1k Subcritical regime | Solved | sub | complete tilted-spline matrix positive definite below the eighth root eventually [L*]; one fixed small multiple of `(log N)^{1/8}` [F] |
| Σ1c–Σ1x Critical-curve calculus | Classified | sub / method | [F]/[KR] |
| Σ1u, Σ129 Threshold law | Solved (identities) | RH | `0<R_PD=…=R_halfline≤W=…`, each infinite iff RH [F]; `polarPaymentCriticalThreshold=⊤ ⇔ RH` [L*] |
| Σ4 Finite index / heat count | Sharpened | ≥qRH; RH for index 0 | finitely many non-real zeros at every positive time, infinitely many at every negative time [doc]; `N_d≤300√(d log d)` [F] |
| Σ6 Rank and degree | Partially solved | RH | theta rank 14 for `0<a≤½` [L*]; rank `N` from verified height [F] |
| Σ13–Σ15 Tensor amplification; deformation to positive matrices; separable assemblies | No-go | — | [KR] |
| Σ20 Scheduled sums | Open | RH | receivers only [F] |
| Σ27 Window stages | Partially solved | sub | floor `1/5000` on windows of ratio `≤103/50`; `{2,3,4}` kicks below `991/1000` of the Lévy energy for `2c<log 5` [F] |
| Σ28, Σ41 Negativity budget; aperture–depth | Sharpened / Classified | ≥qRH; sub | positivity at aperture `a` confines zeros up to `2πe^a` to depth `<exp(−c log³\|γ\|)`; an isolated pair shows at the rung of its depth [L*] (log §4.10) |
| Σ42, Σ53, Σ57 Markov, size-only, Perron | No-go | — | [KR] |
| Σ49 Reality by continuation | Sharpened | RH | RH ⇔ every zero of every `H_t`, `t>0`, simple [L*] ⇔ no positive real branch time [L*] (Σ193) |
| Σ56, Σ66, Σ113 Onset; contact; restoring bound | Sharpened | RH | [F] |
| Σ73–Σ80 Sector receivers | Sharpened | RH | PA, HCF, TT, RN, PTR, GTA, TG [F] |
| Σ82 Finite-rung principle | Partially solved | sub | `RHVerifiedThrough 67` [L*]; verification through a height ⇒ the sign on `[−a,a]` [L*] |
| Σ98, Σ133 Theta heads | No-go (fixed heads); Sharpened | RH | [KR]/[F] |
| Σ116, Σ117 Weighted Gårding; typical heights | No-go; Solved in law | sub | exceptional heights on a rung have power-small measure [L*] (`eventually_boundedShape_rung_exceptions_sharp`) |
| Σ135, Σ139 Pole channel; half-line ground states | Sharpened | method | RH, or `R_polar<W₀`, or `R_polar=W₀` with every critical state polar-orthogonal [L*]; a charged critical state gives `R_polar<W₀` [L*] (B104) |
| Σ140 Holomorphic multipliers | No-go | — | [KR] |
| Σ137–Σ151 The minimal face | Solved (identity) | RH; ≥qRH at `p^σ` | forms of §0 of the route report; `Θ<1` ⇔ a power floor [L*] |
| Σ146, Σ152 Resolution | Settled | method | prescribed sublogarithmic windows do not bound the class; a density-matched configuration survives [L*] |
| Σ147 Bounded windows against world I | Solved (receivers) | AAL | floors at every length `(k+1)π/67` give AAL [L*]; one length has models [F] |
| Σ150, Σ172 Regulated energies | Solved (identity); No-go (source) | RH | a Green–Weil energy floor gives RH [L*]; `E_r≤W` at every cutoff [F] |
| Σ153 Hodge index of the comb pairing | Solved (identity) | RH | [L*] (Σ183) |
| Σ154, Σ165, Σ166 Comb at finite scale | Solved (identity) | RH | RH ⇔ a positive mass floor on every ratio window [L*] |
| Σ155, Σ158 Forced data | Solved (identity) | RH | constant (`c≤0 ∧ RH`), weights (`RH ∧ w=Λ`), contacts at their price, counterterm at the supremum of the symbol [L*] |
| Σ156 The exceptional square | Solved | method | trivial aperture `log log q+o(1)`; a system aligned with a height fails beyond it; the Liouville system form is below `−K‖F‖²` at aperture `≥log log q+η` [L*] |
| Σ157 Selectivity of windows | Solved | method | weights invisible for `2a<log 2`; contacts vanish on windows of ratio below two [L*] |
| Σ160, Σ170 Feasible weights; certificates | Solved; No-go (freedom) | RH | feasible at every aperture ⇔ RH; feasible systems converge to `Λ` [L*] |
| Σ162 Exchange rate | Solved (receivers); rungs `κ<4/3` by `[X]` | a half-plane below `7/8` | one theorem for saving, rung, isolated depth, mollifier depth [L*]; the rung `κ<4/3` from `[X]` is a deduction, no rung above one is a Lean statement (A138) |
| Σ163 Depth on the ladder | Settled (configurations); Open (ζ) | method | [F]; B156 |
| Σ164 Level-one dressed positivity | Solved (identity) | RH | level one above some prime ⇒ RH; RH ⇒ every level `≥½` [L*] |
| Σ167 Index in the aperture | Solved (identity) | identity | index = sum of nullities below = number of eigenvalues below the energy [L*] |
| Σ168 Null modes | Sharpened | RH | RH ⇔ every aperture crossing number is zero; RH or a unique ground-energy crossing; a single simple null mode on a short aperture [L*] |
| Σ169 Paths | Settled (no transport) | method | a contact altered and paid at its price is RH at every parameter [L*] |
| Σ171 Verification rate | Solved (rate) | sub | RH through `exp(exp(Ca))` ⇒ sign on `[−a,a]`; `C` not explicit; explicit `windowHeight` [L*] (A142) |
| Σ173 Power tails | Solved (identity) | RH (every `a`); ≥qRH (one `a>1/8`) | Abel integrability ⇔ `a+w≤½`; convergence ⇔ every zero has `Re ρ<1−a`; the critical comb has growth exponent the width [L*] |
| Σ174 Matrices and combs | Partially solved | sub (each ratio) | margin `1/20` at the first block sizes of ratio four; refinement transfer of margins above the threshold `log R≥E_Q+2C_Q²/μ₀+μ₀`; at most `300000` negative squares at ratio four [L*]; the threshold at the proved margin is `log R≥2.5·10⁴` [D] (Σ189) |
| Σ175 Morse index = Maslov index | Solved (identity) | identity | crossing multiplicity = Lagrangian intersection number; index = number of crossings [L*] |
| Σ176 Finite-scale Hodge index of the neutral part | Solved (identity); Partially solved (sign) | RH (every window) | supremal neutral index = 1 + number of right zeros; exactly one for `50J≤53R` at every block size [L*] |
| Σ177 Polar Lagrangian and charged null modes | Sharpened | method | below the polar ground energy every crossing is charged and the nullity is at most two [L*]; B104 |
| Σ178 The gluing law | Solved (law); Settled (rank one on actual windows) | method | glued form `A(x)+B(y)−2(u·x)(v·y)`: one negative square iff `αβ≥1`, two if `α,β<0`, `αβ<1`; brackets by lowered and raised potentials; response-matrix inertia for several charges [L*]; on the halves of ratio four: Σ185 |
| Σ179 Bound-state counts from the potential | Solved | sub | index `≤1+` number of deep wells [L*] |
| Σ180 Charged ground vector at finite scale | Solved (`4J≤R`) | method | a ground vector of the block matrix has one sign and both charges nonzero of one sign [L*]; windows with `R≤J` open (B104) |
| Σ181 The critical half-line state | Sharpened | RH (existence); method (charge) | RH, or a state at a finite `W₀`: zero energy, weak equation, unique up to sign [L*]; structure: Σ190, Σ191 |
| Σ182 Li coefficients on the comb | Solved (identity) | identity | Laguerre tails of the comb tend to the paired Li coefficients; without RH both signs recur in windows of bounded length [L*] |
| Σ183 The Hodge inequality on positive packets | Solved (identity) | RH | RH ⇔ `∀Q,R,J` with `1≤R≤J`, `R+J≤QR`, `∀x,y≥0` with `x_ky_k=0` and `N(x,x)<0`: `N(x,x)N(y,y)≤N(x,y)²` [L*] (`riemannHypothesis_iff_forall_wells_bound`); index `≥2` ⇔ two unbound wells ⇔ a sign-changing bound state [L*] |
| Σ184 Bound states have one sign | Solved (identity) | RH | RH ⇔ every eigenvector of every neutral window with negative eigenvalue has one sign; the off-diagonal entries are negative [L*] (`riemannHypothesis_iff_forall_bound_state_one_sign`) |
| Σ185 Rank-one gluing at ratio four | Settled | method | charges `u_iv_j≤K_{ij}` with lowered halves nonnegative on the kernels and susceptibility product `≥1` exist iff `R=1`; for `R≥2` every admissible pair has product `<1` and lowered index `≥2`; at `R=1` the product exceeds `8/5` [L*] (`halves_of_ratio_four_glue_iff_eq_one`) |
| Σ186 The rank of the binding | Solved | method | for `600(r+1)≤H`, `Q≥2`: every rank-`r` model of the coupling between `(2H,4H]` and `(4H,8H]`, with any positive weights paying the error, has lowered index `≥2`; at `R=2` rank two glues with zero excess and index one [L*]; the contact of 2 is supported on the graph of `b↦⌊b/2⌋`, of rank proportional to the block size [D] |
| Σ187 Narrow windows | Solved | sub | `16J≤R`: index zero, potential above one, strictly positive definite; the union of two narrow windows has index zero; for adjacent narrow windows opposite-sign spike charges give negative susceptibilities with arbitrarily large product [L*]; the susceptibility criterion carries no information there [D] |
| Σ188 Selective binding | Solved (boundary); Open (true contacts) | sub; method | `ω(2)∈[−4,0]` ⇒ index `≥2` for `J≥2R`; `ω(2),ω(3)∈[−5/2,19/40]` ⇒ index `≥2` for `J≥3R`; Liouville twist ⇒ index `≥2` for `J≥2R`; a constant raised by `2/5` ⇒ index `≥2` on `(R,4R]`; on the half-constant plane two bound states as soon as `(J+K_ω)²<2(D+δ)²`; the true weights give a positive direction there [L*]; the sign with the true weights (B192) |
| Σ189 Reach of the finite procedures at ratio four | Classified | sub | margin transfer needs `log R≥2.5·10⁴` at margin `1/20` and `≥1.2·10³` at any margin `≤1`; the explicit window height contains `exp(winE+2π)` and `48^{2n}`; the verified height is 67 [D] from [L*] (log §5) |
| Σ190 The half-line energy branch | Solved | method | at every `R>0`: attained unit-mass floor, minimizer unique up to sign, Laplace transform zero-free on `Re z>0`; floor strictly concave in `1/R`; exponential mass of minimizers strictly decreasing; at `W₀`: floor zero, derivative `−a(W₀)∫F²e^{−8u}/W₀` [L*] (log §4.2) |
| Σ191 Structure of the critical state | Solved | method | no Laplace zero on `Re z≥0`; outer multiplier; causal translates dense in `L²` of the half-line; positive mass on every terminal interval; equality in the wall bound iff a translated critical state; weighted and polar stability along the branch; polar residual bounded by the critical energy [L*] (log §4.2); none of these decides the polar pairing [F] |
| Σ192 Strong confinement | Partially solved | sub | `\|λ(R)−a−log a\|≤K`, `c≤a·δ_R≤C`; Gamma comparison on logarithmic-domain profiles [L*]; written closure [S]: `λ(R)−a−log a→μ` (the infimum of the logarithmic form with linear confinement), `a·δ_R→1`, `a·∫(−u)F²→1/8` (`universal_softLogarithmic_confinement_limit`; statements read, log §4.14); verification, attainment of `μ` and convergence of the rescaled profiles (A158) [F]; the regime `R→0` does not reach the sign at `R→∞` [F] |
| Σ193 Branch times | Sharpened | RH | RH ⇔ no branch time is real and positive; every zero of the centre value has `Re τ>0`; central collisions at forward nonreal times, infinitely many; RH holds if every forward monodromy preserves every pair `{z,−z}` [L*] (`riemannHypothesis_of_forwardMonodromy_preserves_pairs`; log §4.4, §4.14) |
| Σ194 Tameness over forward times | Solved | method | far zeros simple on boxes; finitely many branch times on boxes; isolated in `Re τ>0`; no escape; every zero lifts along branch-free forward paths; transport is a bijection of fibres [L*] (log §4.9, §4.11) |
| Σ195 The time of ζ | Sharpened | RH | `0` is a limit of real branch times, or infinitely many nonreal zeros escape along every short real segment across `0`; RH fails, or `0` is a limit of nonpositive branch times, or every nonreal zero at small negative time escapes before `0` [L*] (log §4.4) |
| Σ196 The Metzler dichotomy | Solved (law) | method | a Metzler form with positive row sums and connected support has one positive square ⇔ trickle-down inequality ⇔ hyperbolic links; the atomic intersection form is hyperbolic at small widths for every completely multiplicative sign twin; nonnegative gauge ⇔ `χ(p)=1` for `p≤N` [doc] (log §4.11) |
| Σ197 Jensen census | Solved (identity) | RH (`N_d=0`) | `N_d=4Q_d`; `sup 4Q_d` = off-line multiplicity; at each degree finitely many shifts fail real-rootedness; `N_d=0` for `2·10⁷d⁴≤T log T` under verification to `T` [L*] (log §4.8, §4.9) |
| Σ198 Two-prime form of the minimal face | Solved (identity) | RH | for primes `p≠q`, `r>0`: RH ⇔ a lower bound of the orbit correlation at the two-Frobenius lags within `r√T` of arbitrarily late `T`; RH ⇔ the Weil lag function is bounded above on `{k log p+l log q}` [L*] (log §4.9) |

## Π — precision and production

| Wall | Status | Strength | Content |
|---|---|---|---|
| Π1, Π4 Global law; window precision | Solved (equivalences) | RH | [F] |
| Π2 Deciding input | Open | RH | no subset of the count class contains the Liouville weight, is stable under `εn^η`, `η<½`, or is decided by finite prefixes [L*] (log §4.8) |
| Π3, Π67, Π70, Π71 Producer cost and rates | Solved (exponent scale) | sub / ≥qRH / RH | polynomial rate ⇔ Mertens power saving [L*] |
| Π7, Π151, Π166 Census | Partially solved; No-go (positivity) | sub | `0.67250071` in `Zeta23` objects; positivity cost `>13/10` [L*] |
| Π22, Π65 Near-line density | Reduced | sub | bounded inner field ⇔ depth density `O(T)`; the inner field is bounded at infinity [L*] (log §4.9); density `o(T)` (B57) |
| Π40, Π148 Strip self-improvement; return transfer | Open; Settled (strength) | RH | under `Θ<1` the transfer ⇔ RH [F]; `[X]` |
| Π41, Π42, Π56, Π161 Mean-value ladder | Solved (`θ<½`); Sharpened | RH | twisted moments; positive proportion; depth `<1/(2θ)+ε` from dyadic boundedness at `θ>1` [L*] |
| Π46, Π55 Parity blindness | No-go | — | [KR] |
| Π51 Vinogradov–Korobov barrier | Open | sub | twisted Chebyshev sums of ζ above polylogarithmic frequencies [L*]; `[X]` past it |
| Π53, Π54, Π80 | Open | sub | [F] |
| Π66, Π125, Π126, Π146, Π153 Integrality; Stepanov | Solved (price) | RH (degree bound) | `p^{11/12}` at one prime [F] |
| Π94, Π128–Π130, Π137 Returns | Partially solved | sub | `c·y^{1−b}≤log t` under `Θ≤b` [L*] |
| Π102, Γ221 One-structure worlds | Solved (countermodels) | — | FE with Gamma factor and count, no landing; Euler product over the rational primes with a count rate, every finite layer [L*] |
| Π105, Π127 Orientation cover | Solved (identity) | RH | centred count `M(N)=Ω_±(√N)` [F] |
| Π112–Π114 Thick crude count | Sharpened | AAL; RH with attainment | [F] |
| Π141, Π142, Π145 Families | Classified; No-go | method | fixed parts [F]/[KR]; RH ⇔ sublinear tensor exponent [L*] |
| Π147, Π155, Π156 The square; sections | Classified | — | sections in aligned boxes: volume over the gluing index [L*] |
| Π149 Centred Vaughan currents | Solved (reduction); open (bound) | AAL | growing-order current reduced to centred cofactors [F]; B145 |
| Π158 Reciprocity sources | Classified | producer | Möbius sign at odd order of a Gauss sum; two Gauss sums with a quadratic product [L*] |
| Π159, Π162 Family continuation | Solved at `7/8` [X]; Reduced below | a half-plane below `7/8` | two estimates with reciprocal kernels give `Θ≤σ₀`; `Θ≤b` ⇔ the signal is `≪Z^{b′}` for every `b′>b` [L*] |
| Π160, Π163 The budget | Settled (exponents); Open (count) | method; `[13/15,7/8)` | binding bin: endpoint exponent `−7/30672` at `7/8`, positive at boundary `≤7/8−1/4000`; sieve threshold; corner `8/9` [L*]; floor bin `1−4/(5n)` [KR]; B174 |
| Π164 The half-plane map | Solved (receivers) | — | three rungs under `Θ≤b` [L*] |
| Π167 The floor of the squares | Sharpened | producer | a phase-blind floor Gram needs a saving `≥1/12` for `¾` and `≥1/3` for `½` at `n=6` [KR]; reduced to the long columns (Π175) |
| Π168 The wall of the frame | Solved | method | the correction factors through a Grössencharacter `L`-function at `6s−3`; the continued correction has infinitely many zeros in a strip right of `7/12` [L*] |
| Π169 Sieves over the Eisenstein integers | Partially solved | sub | quadratic large sieve [L*]; a sextic sieve is absent |
| Π170 Primes in short progressions | Solved | sub | `(x,x+x^θ]`, every reduced class [L*] |
| Π171 Cameras | Solved (in law; adaptive isolation) | sub | adaptive clusters with complete exterior mass `≤¼`; centred prime mean squares [L*]; pointwise prime cost at the selected centres (B59) |
| Π172 Logarithmic correlations of `λ` | Solved | sub | `(log x)^{−1}Σ_{n≤x}λ(n)λ(n+h)/n→0` for every `h≥1` [L*] (`tendsto_logAvg_liouville_shift`); no rate, no half power [F] |
| Π173 The coupled tower | Solved | a half-plane | zero transfer `ρ↦6ρ−3`; reach `max(σ₀,3/5)` with estimates on every level; `7/12` under sextic GRH [L*] |
| Π174 The end of the Gauss-sum class | Classified | producer | square-root cancellation across the rows of the floor bin gives the half-plane `1−2/n`: `2/3` at `n=6` [L*]/[D]; B187 |
| Π175 The long columns | Sharpened | a half-plane in `(2/3,13/15)` | root number of a row = theta phase times the square of the theta coefficient; short columns incoherent [L*]; B185 |
| Π176 Short columns and the average row | Solved | method | short Gram diagonal; average row target-free [L*] |
| Π177 The barrier of the `6r`-periodic pairings | Solved | producer | coupled fixed point `(4r−1)/(6r−1)≥3/5`, equal to `3/5` iff `r=1` [L*]; B187 |
| Π178 Poles of the theta-square series | Solved (untwisted) | method | factorization over cube frequencies; double pole at `4/3`; the rotated correlations see only the three-divisible layer [L*]; layers `m=0,1` and the twisted column (A148) |
| Π179 The half-plane `7/8` in Lean | Partially solved (written) | a half-plane (`7/8`) | stated without hypotheses in source: `ζ(s)≠0` and `L(s,χ)≠0` for `Re s>7/8`, every Dirichlet character; the Hecke family over `ℚ(√−3)`; zeros of ζ with `Re s>0` have `Re s∈[1/8,7/8]`; assembly from certified detector bands through the moment batches and the common probe, then norm base change (statements read, log §4.14) [S]; validation of the producer and dependency chain (A118) [F]; the receivers with the half-plane inserted (A138) |
| Π180 Short-interval Liouville | Solved | sub | `Σ_{X≤m<2X}\|Σ_{m<n≤m+h}λ(n)\|²≤εh²X`; the twisted form for `χ≠1` [L*] (log §4.5, §4.10) |
| Π181 Runs of simple critical zeros | Solved (four, five) | sub | positive proportions of starts of four and of five consecutive simple critical zeros [L*] (log §4.9); longer runs (B27) |
| Π182 Tangent data in world I | Solved | identity | under `Θ∞<Θ` tangent data of `μ` and `λ` [L*] (log §4.7); additive twists (A144) |

## Γ — selection, reflection, position

| Wall | Status | Strength | Content |
|---|---|---|---|
| Γ1 Self-return | Open | RH | strong recurrence ⇔ RH [F]; RH ⇔ relative compactness of the orbit [L*] |
| Γ15, Γ33, Γ35, Γ167 Rigidity of ζ | Solved (classification) | method | `L¹` defects force the rational primes [L*]; among countable unit-multiplicity systems with `Σnorm^{−3/2}<∞` a defect `O((1+\|t\|)^{−a})`, any `a>0`, forces them (Γ245) |
| Γ24, Γ62, Γ95 Mayer; Hecke dispersion; Krein flux | Sharpened | RH | [F] |
| Γ67, Γ183 Abscissa split and atoms | Solved (identity) | identity | RH ⇔ ZAL ∧ B13 ∧ Landing; `Θ<1⇔Θ∞<1` [L*] |
| Γ68, Γ69, Γ220 AAL and its receivers | Open; Solved (receivers) | sub | AAL ⇔ at most one or infinitely many zeros right of every line [L*]; constant-vector signs on infinitely many dyadic prime shells ⇒ AAL [L*] (log §4.13); unit gap; non-attainment [F] |
| Γ73, Γ145 One-offs; firewall | No-go (positive data) | — | AAL, or meromorphic positive Euler models with an isolated pair [KR] |
| Γ86, Γ121, Γ122, Γ226 Modular horizon | Solved (identity) | RH (rate) | RH ⇔ quarter ringdown rate; strip `Re ρ≤1−2δ` ⇔ rate `δ`; pulse rate = horocycle rate; Weyl order; every right zero is seen by a pair of Hecke forms; one form seeing all right zeros forces `ζ(ρ/2)≠0` [L*]; `selberg_status` (Γ252); a rate from the horizon B178, B188 |
| Γ89, Γ148, Γ157 Physical positivity; modular conjugation; half-sided inclusions | No-go | — | [KR] |
| Γ96, Γ125, Γ154, Γ227 Count law | Solved (curves); Sharpened (ℤ); No-go (sections) | RH | hyperelliptic count [F]; counts on prime rays ⇔ RH [L*] |
| Γ137, Γ161, Γ181 Positive annihilators | No-go | — | [KR] |
| Γ141, Γ185, Γ218 FE with approaching remainders | No-go | method | Riemann Gamma factor, count within one, no landing [L*] |
| Γ182 Landing | Sharpened | sub | under the landing law: RH ⇔ zeros approach the line ∧ (finite off-line ⇒ RH) [L*]; B138 |
| Γ184 Deuring–Heilbronn | Classified (models); Open (ζ) | sub | a finite layer with a tail over the rational primes [L*]; B141 |
| Γ192 Two worlds | Solved; edge world excluded [X] | identity | [L*]; [X] |
| Γ195, Γ222 Index law; unit gaps | Solved (law); No-go (regulators) | RH | the tower quotient has a unit gap iff RH [L*] |
| Γ196, Γ197 Glued carrier; adelic Green kernel | No-go; Classified | — | [KR] |
| Γ198, Γ213, Γ216, Γ225 One matrix for number rings | Solved (identity) | identity | exact index for the zeta functions of abelian number rings [L*] |
| Γ203 Separation | Solved (receiver) | RH | ordinate injectivity ⇔ RH [F] |
| Γ206 Graded recurrence | Solved (receiver) | ≥qRH | `T^c` returns, `c>(30/13)(1−σ)` [F] |
| Γ208 Flow | Solved (identity) | RH | prime lag Gram matrices positive semidefinite ⇔ RH [F] |
| Γ209, Γ212, Γ215, Γ224 Constituents | Solved | method | none bounded or Wiener with a zero [F] |
| Γ217 Structures of the square | No-go / Classified | — | [KR] |
| Γ219 Finite strata with both structures | Open | method | B157, A120 |
| Γ223 Symmetrization | No-go (first order) | method | monotonicity under every small split forces a concave real trace of the gradient symbol [L*]; B172 |
| Γ228 Replication | No-go (normal families) | method | normalizations of translates tend to zero at a finite layer [L*] |
| Γ230 Integer count of a fake | Solved | method | every exponent `β>½` is an integer-norm fake exponent, realized by prime deletions with a real and a non-real fake zero; a fake at `β≤½` has positive density and omits infinitely many primes; a prime-deletion fake at `β≤½` has a real fake zero on or right of all its fake zeros; under RH every `β>1/3` is a fake exponent [L*] (`integerNormFake_complete_solution`) |
| Γ231 The top of a fake | Solved above the pair; Open below `√x` | method | a non-real pair alone on top for `½<Re ρ<14/15`; at `β≤½` balanced or a real top; even order above twice the count exponent; `(1−θ)Re ρ≤2β(2−θ)` [L*]; B183 |
| Γ233 Index of Artin characters | Solved (quotients, powers); Reduced (all characters) | identity | quotients of configurations and their powers [L*]; Γ251 |
| Γ234 Ultrametric dominance | Solved (Goss) | method | [L*]; no norm for ξ [F] |
| Γ235 Affine coincidences of zeros | Classified | method | halving pairs [KR]; the probe's pairs `(ρ,6ρ−3)` [L*] |
| Γ237 Two-sided edits as models | Solved (countermodels) | — | every finite layer; sparse configurations; zeros on and rising to a vertical line; zeros symmetric in a strip; a finite layer of ζ edited away [L*] |
| Γ238 Laws of the edits | Solved (laws) | method | balance or real top; parity; floor of prime edits `≥13/30` [L*]; the order law at higher multiples (A155) |
| Γ239 The FE axis | Solved (to a window) | method | fake edits: defect energy `≥(A²/(256πp₀))T log T`, defect not `≤c√log\|t\|`; pair and quartet twins [L*]; the window between `T log T` and `T^{1+ε}` (B191) |
| Γ240 The zero field | Solved (identity); Classified (group) | RH | algebraic and normal over the source field; no transitivity; `K_even⊆ℝ` ⇔ RH; the zero field equals the source field or is a quadratic extension of the even width field by one imaginary offset [L*] |
| Γ241 Virtual configurations; number rings | Solved (identity) | identity | the index of a difference counts zeros and poles off the line; contacts of a number ring = point counts over finite fields [L*] |
| Γ242 The frontier dichotomy | Solved | method | `Θ=1` with AAL, or `Θ<1` and fake edits with mean-square defect `≤C_εT^ε` at every `½<β₀<3/2−Θ` [L*]; a signed fake with bounded defect [L*]; B191 |
| Γ243 Prime trace and reflection fields | Solved (identity); Open (orbits) | RH | reflection field = trace field ⇔ RH; rational real parts have the orbit `{ρ,ρ̄}`; the FE reflection lifts, uniquely, ⇔ every square relation among reflection radicands has even cardinality; two algebraic prime values force a real rational zero [L*]; B190 |
| Γ244 Objects of a failure | Solved (identities) | RH | an odd bound state; a defective hard-edge block; `Re ξ′/ξ<0` right of the line; a negative definite Markov plane; an empty feasible set [L*] |
| Γ245 FE rigidity at any decay | Solved | method | countable Beurling system, unit multiplicities, `Σ\|x\|^{−3/2}<∞`, Hamburger strip class, defect `O((1+\|t\|)^{−a})`, `a>0` ⇒ `β=½`, the counting measure of the rational primes, `ζ_B=ζ`, a norm-preserving bijection of labels; no fake zeros [L*] (`beurlingSystem_rigidity_of_decaying_defect`) |
| Γ246 Slow defects of positive weighted systems | Solved (countermodels) | method | `∀Φ→∞`, `μ<½`: a countable system with positive real weights, ℚ-independent log-generators, continuation to `Re s>1/3`, zeros at `1−μ±iγ`, count `Ax+O(x^{4/5})`, defect `≤Φ(\|t\|)` eventually [L*] (`exists_positiveWeighted_beurling_slow_defect`) |
| Γ247 Real-weighted fakes on the integers | Solved | method | a fake with `a₁=1` has a coefficient `a_m≠1` and an Abel floor; its defect is not `o(1)` and not power-decaying; a signed three-term system on the powers of 2 has a fake zero `¾+i` and bounded defect [L*] |
| Γ248 Scenario table of world I | Classified | method | integer-norm fake edit with a count rate: defect not Abel-sublinear, not `o(1)`, not power-decaying, not bounded, not `≤c√log\|t\|`; if `½<β₀<3/2−Θ`: mean defect below `cT^{2α}` at arbitrarily large `T`; positive real weights: `‖g(t)‖<c\|t\|^α` eventually; least deleted prime arbitrarily large at a fixed zero [L*] (log §4.3) |
| Γ249 The forward monodromy group | Solved (construction); Open (structure) | method | transports along forward loops form a group of permutations of the zeros of `H_τ`; transports are unique; every element commutes with `z↦−z`; the groups at two base times are isomorphic; the turn around a collision is the reflection of its Hermite sheets, of order two; every forward branch time gives an element `≠1`; a centre time gives an element exchanging some zero `z≠0` with `−z`, so the group is not trivial; a collision away from the centre gives an element that moves a pair; transport depends only on the homotopy class of the forward path [L*] (log §4.13, §4.14); existence of such a collision, generators, transitivity (B193) |
| Γ250 Conjugation is a monodromy | Solved (identity) | RH | over a positive real non-branch time complex conjugation of the fibre is a forward monodromy (through the time `1/8`, where all zeros are real); RH ⇔ it is the identity at every such time [L*] (`fibreConj_mem_forwardMonodromy`, `riemannHypothesis_iff_fibreConj_eq_one`); the turn around a central collision carries a zero `z` to `−z` [L*] (`exists_turn_transports_ne`) |
| Γ251 Artin Euler products | Solved (abelian form; cyclotomic reciprocity); Reduced (general reciprocity) | identity | `L(s,Ind σ)=L(s,σ)`; integer relations of characters; every Artin Euler product a product of integer powers of abelian ones; reciprocity for cyclotomic characters; Artin map onto; norm index `≤[L:K]`; Herbrand quotients; norm index modulo a congruence subgroup for cyclic extensions; norms positive at ramified real places; the degree of a cyclic extension divides the norm index `[K^×:N L^×·(K^×∩W_k∩P)·K_S]`; the Artin map over an intermediate field is the Artin map of the norm [L*] (log §4.5, §4.9, §4.11, §4.13, §4.14); the ideal-class form, Artin's lemma, triviality on a ray (A154) |
| Γ252 Status of Selberg's conjecture | Solved | method | `λ₁≥3/16` on every congruence subgroup; `λ₁≥¼` for levels dividing `N²`, `N≤25`; in weight `½` the theta function has eigenvalue `3/16` [L*]; an argument whose inputs hold in weight `½` cannot pass `3/16` [doc] |
| Γ253 Jensen equations | Solved (dichotomy) | method | the degree-`2n` centred Jensen equation has group `C₂≀S_n` over its coefficient field, or a nonzero rational polynomial vanishes on its normalized moments; the coefficients are algebraically independent ⇔ the normalized moments are [L*] (log §4.4); independence of the moments open |
| Γ254 Orderings of the squared-width field | Solved (identity) | method | every ordering defines complex conjugation ⇔ every squared width is a sum of squares; no ordering defines an automorphism besides the identity and conjugation ⇔ every product of two radicands is a sum of squares [L*] (log §4.4) |

## Scoped no-gos and surviving replacements

| Boundary | Exact scope and survivor |
|---|---|
| sizes of the contacts | positive to rung `1−o(1)`; aligned systems and the Liouville twist fail beyond the trivial aperture (Σ156). Survivor: a saving that fails for the Liouville twist (B159) |
| windows below the logarithmic radius; one-sided floors of one length | models (Σ146, Σ147). Survivors: the logarithmic radius; floors at every length; two primes at radius `r√T` (Σ198) |
| explicit formula, positivity, Euler products over the rational primes with multiplicities `0,1,2`, count rates | every finite layer realized (Π102, Γ237). Survivor: unit multiplicities with the reflection up to a decaying error (Γ245), or a count below half the layer |
| a growth bound on the FE defect as a selector among positive weights | arbitrarily slow defects with off-line zeros (Γ246). Survivor: decay among unit multiplicities (Γ245); boundedness among unit multiplicities undecided (B191) |
| a bounded FE defect as a selector among real signed weights | a fake (Γ247). Survivor: decay |
| the functional equation up to an error of mean size `T^ε` among prime edits | fakes if `Θ<1` (Γ242). Survivor: a decaying defect; the gap `T log T` to `T^{1+ε}` (B191) |
| a count rate above the pair forcing a real top | two-sided edits (Γ231). Survivor below `√x`: balanced edits only (B183) |
| the frame of the cubic probe and of every `6r`-periodic Gauss pairing | fixed point `≥3/5` (Π173, Π177). Survivor: a pairing outside the class (B187) |
| the cubic probe's estimates | square-root endpoint `2/3` (Π174). Survivor inside: the long columns (B185) |
| a rotation of the theta correlation by a unit | reads the three-divisible layer only (Π178). Survivor: independent data for `m=0,1` (A148) |
| gluing two halves of a window through one pair of charges | only at block size one (Σ185). Survivor: none at rank one |
| gluing through a fixed number of charges, or any model of the coupling of bounded rank | two bound states for `600(r+1)≤H` (Σ186). Survivor: rank growing with the block size, or a signed comparison keeping the true contacts (B192) |
| the susceptibility criterion on positive-definite windows | satisfied with arbitrary product (Σ187). Survivor: none; the criterion informs only windows with a bound state |
| the sign of a window from sizes of the contacts of 2 and 3 | weights `≤19/40`, or the Liouville twist, give two bound states (Σ188). Survivor: the true weights (B192) |
| certified margins or a verified height as a route to the index at ratio four | thresholds `log R≥2.5·10⁴`, a window height beyond every verified height (Σ189). Survivor: a proof from the contacts (B192) |
| the atomic Hodge index as a selective statement | holds for every sign twin (Σ196). Survivor: none at small widths |
| stability, cyclicity, outer structure of the critical state as a decision of its charge | all hold in both cases (Σ191). Survivor: a Green or boundary-trace identity (B104) |
| strong confinement as a route to the weak-confinement sign | different regime (Σ192) |
| membership of conjugation in the forward monodromy, commutation with the reflection | do not force triviality (Γ249, Γ250). Survivor: a group that preserves every pair gives RH [L*]; the existence of an exchange (B193) |
| triviality of the whole forward monodromy group | refuted: at every base time a loop exchanges some zero `z≠0` with `−z` [KR]; [L*]. Survivors: pair preservation ⇒ RH; RH ⇔ triviality of the one element conjugation |
| transport of zeros to the time of ζ | no uniform control as `τ→0` (Σ195) |
| the Kuznetsov–Kloosterman mechanism as a source of a rate beyond `3/16` | sharp in weight `½` (Γ252). Survivor: an input that fails in weight `½` (B188) |
| logarithmic correlation decay of `λ` as a source of half power | no rate (Π172) |
| a mean square containing the principal twists; positive weights | the half-plane itself [F] |
| bounded and Wiener constituents | none (Γ224) |
| sections, towers, own combs, paths | identities; RH at every parameter (Σ169, Γ217) |
| regulators | the count of the limit (Σ150, Γ222). Survivor: a realization with one negative square (B171) |
| certificates other than `Λ` | converge to `Λ` (Σ160) |
| linear statistics under projection | Γ223. Survivor: B172 |
| replication by normal families | Γ228. Survivors: transport, currents (B89, B145) |
| bilinear statements as parity-sensitive | sign-blind (Π46) |
| mean values below the height as detectors of single zeros | `θ<½` proved (Π161); finite relocation invisible [KR] |
| positivity alone at 70% | cost `>13/10` (Π166). Survivor: B150 |
| the return transfer | RH under a strip (Π148) |
| a transitive Galois action on the zeros | none (Γ240). Survivor: orbits inside `{±δ}` (B190) |
| Markov, Perron, size-only payment, floor tower, universal multipliers, fixed theta heads, positive Laplace mixtures, internal modular conjugation, bounded-height Diophantine certificates | as recorded [KR] |

## Bridges

| Bridge | Anchor |
|---|---|
| one inequality per prime: Weil test = count on a prime ray = upper side = copositive prime plane = two-prime lags | SOSZ [L*] |
| one matrix at finite scale: Weil's form on step packets = product of the charges + potential + Dirichlet form of the jets and the floor-map contacts | AGZ [L*] |
| one bound state = Hodge inequality between positive packets without common blocks = one-sign bound states | AGZ [L*] |
| binding = the true contacts of the small primes; rank of the binding = block size | AGZ [L*]; [D] |
| a window with negative off-diagonal entries = a Metzler form: index zero in the stability regime, one in the hyperbolic regime | ALG [doc]; AGZ [L*]; [D] |
| Morse index of the aperture path = Lagrangian intersection number | AGZ [L*] |
| a failure of RH = one critical half-line state = one positive real branch time = one nontrivial conjugation monodromy | AHD, GaloisTheoryOfZeros [L*] |
| the functional equation = local monodromy at the central collisions; complex conjugation = a forward monodromy | GaloisTheoryOfZeros [L*] |
| one scale: saving, rung, depth, mollifier, level, signal, twist exponent, critical-comb growth, rate | SA, FCT, AGZ, BHR [L*]; [D] |
| the width and the Li coefficients on one sequence: the comb | AGZ [L*] |
| half-plane route = two estimates for one completed sum; correction = Grössencharacter `L`-function at `6s−3`; every period has fixed point `≥3/5` | FCT [L*] |
| AAL = unit gap = no accelerating filter = shell signs | FFA, BHR, AKLT [L*]/[F] |
| B13 ⇔ packet index `0` or `∞` | ACS [L*] |
| the door of world I: unit multiplicities with a decaying defect = the rational primes | EFT [L*] |
| a count rate = nothing about the zeros above half the layer | WZC [L*] |
| window sign ⇐ verification at `exp(exp(Ca))` | VHR [L*] |
| Artin `L`-function = integer powers of abelian Euler products | RHTower/Artin [L*] |
| the zero field: `H=B` ⇔ `K_even⊆ℝ` ⇔ RH | GaloisTheoryOfZeros [L*] |
| twisted moments below the square root ⇒ a positive proportion on the line | MZF [L*] |
| the congruence mechanism = `3/16`, attained in weight `½` | RHTower [L*] |

## Strength of the open walls

- **RH:** Σ1, Σ6 (all ranks), Σ20, Σ49, Σ56, Σ66, Σ73–Σ80, Σ113, Σ129, the minimal face, Σ150 (sign), Σ153, Σ154/Σ165/Σ166, Σ155, Σ160, Σ164, Σ168, Σ173 (every `a`), Σ175 (no crossing), Σ176 (every window), Σ181 (existence), Σ183, Σ184, Σ193, Σ195, Σ197 (`N_d=0`), Σ198, Π2, Π42, Π126, Π127, Γ1, Γ24, Γ62, Γ95, Γ121, Γ122, Γ154, Γ195, Γ203, Γ208, Γ222, Γ240, Γ243, Γ244, Γ250.
- **≥qRH** (open below `7/8`): Σ4, Σ28, Σ162, Σ173 (one `a>1/8`), ZAL, Π3, Π159/Π162 (B161), Π163 (B174), Π167/Π175 (B185), Γ206, Γ226 (a rate `δ>1/16`).
- **AAL:** Π114, Σ147, Γ220, Π149.
- **sub:** Σ27, Σ82, Σ116, Σ117, Σ171, Σ174, Σ188 (B192), Σ192, Π7, Π22, Π51, Π53, Π54, Π65, Π80, Π94, Π161, Π169, Π171, Π181, Γ68, Γ182, Γ184, B13.
- **method / producer / indep.:** Σ135, Σ139, Σ177, Σ180, Σ181, Σ191 (B104), Σ163 (B156), Σ186, Σ188 (B192), Π158 (B180), Π174, Π177 (B187), Γ219 (B157), Γ222 (B171), Γ223 (B172), Γ226 (B178, B188), Γ231 (B183), Γ234 (a norm for ξ), Γ239, Γ242 (B191), Γ243 (B190), Γ249 (B193), Γ253 (moment independence).
- **just work:** Π179 (A118), Π178 (A148), Γ251 (A154), Σ171 (A142), Σ162 (A138), Σ192 (A158).
