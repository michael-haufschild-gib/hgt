# Walls ledger — status quo

**Corpus checkpoint:** `5920325719` with its working tree (2026-11-12). Fact log: `logs/review-1211-status-quo-facts.md` (identifiers `FC-T*`, `CR*`, `ST*`, `AG-*`, `PC*`, `WZ*`, `GZ1`, `CAM1`, deductions `D1–D8`, baseline declarations §6). Companions: [route-obstacles.md](route-obstacles.md), [route-unification-ledger.md](route-unification-ledger.md), [obstacles-summary.md](obstacles-summary.md).

Three wall families carry the frontier. **Σ** is the critical sign of the window form, **Π** the precision and production of the prime count, **Γ** the selection of ζ, the reflection of its zeros and their position. They meet in one inequality per prime, one finite-scale matrix, one path of Lagrangians, and one scale.

- **The minimal face.** RH ⇔ `P(p)≤A(p)+K` at the primes of arbitrarily late logarithmic windows, outside `Ce^{δT}` primes per window; equivalently the upper side, `ℕ`-counts on surviving rays, one moment exponent, two-bump comb limits [L*]. No window below the logarithmic radius decides [L*].
- **The finite-scale matrix.** RH ⇔ the neutral part of the step-packet matrix (a potential plus a Dirichlet form with attracting jets and contacts) has exactly one negative square on every window `(R,R+J]`, `R≤J` [L*] (AG-F1, AG-F4). Certified on every window of ratio `≤103/50` at every block size, on the first blocks of ratios 4 and 7, and on thin packets at every ratio [L*].
- **The path.** The index of the restricted Weil form is the Maslov index of the conormal path against the graph of Weil's operator; its supremum at energy zero is the number of right zeros; RH ⇔ no crossing [L*] (AG-L1–AG-L3).
- **The scale.** Saving, rung, depth, mollifier exponent, level, signal exponent, twist exponent, floor exponent, moment ratio, critical-comb growth, relaxation rate: one number [D]. `b=7/8` is `[X]`; the open part is `½<b<7/8`.
- **The producer.** One class, with an exact end: the cubic probe reaches `2/3` with square-root cancellation in every bin and its frame stops at `3/5` (coupled tower) [L*]; [D] (D1). The square-root endpoint of the class is `1−2/n` at conductor exponent two, `½` only at twist order four, where no sign-carrying design is known [D] (D2).
- **The door of world I.** Every structure set weaker than the Euler product with the functional equation as an identity (or with a count below the floor) has a model with a finite layer; with the identity the system is the rational primes [L*]; [D] (D5).

[Frontier](../rh-current-frontier-map.md): **38 live formulations, 12 candidates**. [Scoped obstructions](../rh-killed-routes.md).

**Status.** **Solved** (the face is a theorem), **Partially solved**, **Sharpened** (open, exact form a theorem), **Reduced** (theorem-level equivalent named), **Open**, **No-go** (mechanism refuted), **Classified**, **Settled** (a method question answered). **Strength:** RH, ≥qRH, AAL, sub, indep., identity, method, producer. **Evidence:** `[L*]` statement read at the declaration; `[doc]` module docstring; `[F]`, `[KR]` frontier map and scoped-obstruction ledger, read in full; `[S]` unfinished per the frontier map; `[D]` deduction; `[C]` classical, from memory; `[A]` assessment; `[X]` the external theorem `Θ≤7/8`, taken as proved, not in the Lean graph (A118). **≥qRH** is open where it gives a half-plane below `7/8`.

## Σ — critical sign

| Wall | Status | Strength | Content |
|---|---|---|---|
| Σ1 Weil's sign | Sharpened | RH | RH ⇔ `W≥0` on every window [F] ⇔ `Ψ` locally bounded [L*] ⇔ the floor on logarithmic prime windows [L*] ⇔ feasible weights at every aperture [L*] ⇔ one positive square of the comb pairing [L*] ⇔ no crossing of the aperture path [L*] ⇔ one negative square of every neutral window [L*] ⇔ subpolynomial critical comb [L*] |
| Σ1b, Σ1k Subcritical regime | Solved | sub | complete tilted-spline matrix positive definite below the eighth root eventually [L*]; one fixed small multiple of `(log N)^{1/8}` [F] |
| Σ1c–Σ1x Critical-curve calculus | Classified | sub / method | [F]/[KR] |
| Σ1u, Σ129 Threshold law | Solved (identities) | RH | `0<R_PD=…=R_halfline≤W=…`, each infinite iff RH [F] |
| Σ4 Finite index / heat count | Sharpened | ≥qRH; RH for index 0 | `N(t)≤1` near `0` gives RH; else `N(t)≥2` [L*]; `N_d≤300√(d log d)` [F] |
| Σ6 Rank and degree | Partially solved | RH | theta ranks `≤14`; rank `N` from verified height [F] |
| Σ13–Σ15 Tensor amplification; deformation to positive matrices; separable assemblies | No-go | — | [KR] |
| Σ20 Scheduled sums | Open | RH | receivers only [F] |
| Σ27 Window stages | Partially solved | sub | floor `1/5000` on tests of length `181/250` [L*]; `{2,3,4}` kicks below `991/1000` of the Lévy energy for `2c<log 5` [F] |
| Σ28, Σ41 Negativity budget; aperture–depth | Sharpened / Classified | ≥qRH; sub | positivity at aperture `a` confines zeros up to `2πe^a` to depth `<exp(−c log³\|γ\|)` [L*] |
| Σ42, Σ53, Σ57 Markov, size-only, Perron | No-go | — | [KR] |
| Σ49 Reality by continuation | Sharpened | RH | RH ⇔ every zero of every `H_t`, `t>0`, simple [L*] |
| Σ56, Σ66, Σ113 Onset; contact; restoring bound | Sharpened | RH | [L*]/[F] |
| Σ73–Σ80 Sector receivers | Sharpened | RH | PA, HCF, TT, RN, PTR, GTA, TG [F] |
| Σ82 Finite-rung principle | Partially solved | sub | height 67; verification through `windowHeight(a)` ⇒ the sign on `[−a,a]` [F] |
| Σ98, Σ133 Theta heads | No-go (fixed heads); Sharpened | RH | [KR]/[F] |
| Σ116, Σ117 Weighted Gårding; typical heights | No-go; Solved in law | sub | exceptional heights of measure `≤T^{1−1/(2κ)+ε}` [L*] |
| Σ135, Σ139 Pole channel; half-line ground states | Sharpened | method | RH, or `R_polar<W`, or `R_polar=W` with polar-orthogonal ground states [L*]; on the aperture side: a neutral ground mode ⇔ `μ(a)=μ₀(a)` [L*] (B104) |
| Σ140 Holomorphic multipliers | No-go | — | [KR] |
| Σ137–Σ151 The minimal face | Solved (identity) | RH; ≥qRH at `p^σ` | five forms; `Θ<1` ⇔ floor `−Kp^α`, `α<½` [L*] |
| Σ146, Σ152 Resolution | Settled | method | every sub-logarithmic radius has a counter-configuration; density-matched for some `R→∞` [L*] |
| Σ147 Bounded windows against world I | Solved (receivers) | AAL | floors at every length `(k+1)π/67` give AAL [L*]; one length has models [L*] |
| Σ150, Σ172 Regulated energies | Solved (identity); No-go (source) | RH | the clock lies below Weil's form [L*] |
| Σ153 Hodge index of the comb pairing | Solved (identity) | RH | one positive square ⇔ RH [L*] |
| Σ154, Σ165, Σ166 Comb at finite scale | Solved (identity) | RH | RH ⇔ a positive mass floor on every ratio window [L*] |
| Σ155, Σ158 Forced data | Solved (identity) | RH | constant, contacts at their price, tree lengths [L*] |
| Σ156 The exceptional square | Solved | method | trivial aperture `log log q+o(1)`; the first rung forces both prime signs [L*] |
| Σ157 Selectivity of windows | Solved | method | weights invisible for `2a<log 2` [L*] |
| Σ160, Σ170 Feasible weights; certificates | Solved; No-go (freedom) | RH | [L*] |
| Σ161 Trivial aperture | Solved (sharp) | method | conductor and height aspects [L*] |
| Σ162 Exchange rate | Solved (receivers); rungs `κ<4/3` by `[X]` | a half-plane below `7/8` | one theorem for saving, rung, companion, mollifier depth [L*]; no rung above one in Lean |
| Σ163 Depth on the ladder | Settled (configurations); Open (ζ) | method | deep zeros at ζ density with positivity on `[−a,a]` [L*]; B156 |
| Σ164 Level-one dressed positivity | Solved (identity) | RH | level one gives AAL and `Θ=½` [L*] |
| Σ167 Index in the aperture | Solved (identity) | identity | jump = nullity [L*]; index law `negativeRank b E=Σ_{a<b}weilNullity a E` [L*] |
| Σ168 Null modes | Sharpened | RH | RH ⇔ no aperture carries a null mode at `E=0` [L*]; `r` right zeros ⇔ `r` null modes on finitely many apertures [L*] |
| Σ169 Paths | Settled (no transport) | method | price paths RH at every parameter [L*] |
| Σ171 Verification rate | Solved (rate) | sub | RH through `exp(exp(Ca))` ⇒ sign on `[−a,a]`; `C` not explicit [L*] (A142) |
| Σ173 Power tails | Solved (identity) | RH (every `a`); ≥qRH (one `a>1/8`) | Abel integrability ⇔ `a+w≤½`; ordinary convergence ⇔ every zero has `Re ρ<1−a`, attained or not [L*] (`powerCombTailConverges_iff_forall_zero_re_lt`); the critical comb never converges; its growth exponent is the width [L*] |
| Σ174 Matrices and combs | Partially solved | sub (each ratio) | margins at the first block sizes of ratios 4 and 7; coarse-block transfer past `log R≥E_Q+2C_Q²/μ₀+μ₀`; at most `(Q−1)⌈e^{E_Q}⌉` negative squares at every block size, `300000` at ratio four [L*]; index zero at every block size of ratio 4 open (A146) |
| Σ175 Morse index = Maslov index | Solved (identity) | identity | conormals of the apertures: an increasing Lagrangian path independent of the primes, ending at the horizontal Lagrangian; crossings with the graph of Weil's operator = null modes; index = number of crossings; supremum at `E=0` = number of right zeros [L*] (AG-L1–AG-L3) |
| Σ176 Finite-scale Hodge index of the neutral part | Solved (identity); Partially solved (sign) | RH (every window) | RH ⇔ exactly one negative square of every neutral window with `R≤J`; certified at ratio `≤103/50` for every block size, at the first blocks of ratios 4 and 7, on thin packets at every ratio [L*] (AG-F1, AG-F5–AG-F8); a bound-state count of a weighted-graph Schrödinger operator [D] |
| Σ177 Polar Lagrangian and charged null modes | Sharpened | method | below `μ₀(a)` null modes are charged and the index is the crossing number of a path of Lagrangian planes in `ℂ²×ℂ²` (even and odd line); ground modes charged ⇔ `μ(a)<μ₀(a)`; unconditional on apertures `≤½(log 2+1/50)`; nullities not all even [L*] (AG-L5–AG-L9); B104 |

## Π — precision and production

| Wall | Status | Strength | Content |
|---|---|---|---|
| Π1, Π4 Global law; window precision | Solved (equivalences) | RH | [F] |
| Π2 Deciding input | Open | RH | no native input at square-root precision [F] |
| Π3, Π67, Π70, Π71 Producer cost and rates | Solved (exponent scale) | sub / ≥qRH / RH | `bestRate`; polynomial rate ⇔ Mertens power saving [L*] |
| Π7, Π151, Π166 Census | Partially solved; No-go (positivity) | sub | `0.67250071` in `Zeta23` objects; positivity cost `>13/10` [L*] |
| Π22, Π65 Near-line density | Reduced | sub | squared right-depth moment `o(V)` [KR]; first-moment density `o(T)` open (B57) |
| Π40, Π148 Strip self-improvement; return transfer | Open; Settled (strength) | RH | under `Θ<1` the transfer ⇔ RH [L*]; `[X]` |
| Π41, Π42, Π56, Π161 Mean-value ladder | Solved (`θ<½`); Sharpened | RH | twisted moments [L*]; depth at `θ>1` [L*] |
| Π46, Π55 Parity blindness | No-go | — | [KR] |
| Π51 Vinogradov–Korobov barrier | Open | sub | VK in Lean for ζ and Dirichlet `L` [F]/[doc]; `[X]` past it |
| Π53, Π54, Π80 | Open | sub | [F] |
| Π66, Π125, Π126, Π146, Π153 Integrality; Stepanov | Solved (price) | RH (degree bound) | `p^{11/12}` [F] |
| Π93 Möbius as a cubic Gauss coefficient | Solved (identity) | past VK | cube identity [L*]; removal of the cube sum A118a |
| Π94, Π128–Π130, Π137 Returns | Partially solved | sub | `c·y^{1−b}≤log t` under `Θ≤b` [L*] |
| Π102, Γ221 One-structure worlds | Solved (countermodels) | — | tangent data realized under each structure [L*] |
| Π105, Π127 Orientation cover | Solved (identity) | RH | centred count `M(N)=Ω_±(√N)` [L*] |
| Π112–Π114 Thick crude count | Sharpened | AAL; RH with attainment | [F] |
| Π141, Π142, Π145 Families | Classified; No-go | method | fixed parts [F]/[KR] |
| Π147, Π155, Π156 The square; sections | Classified | — | sections count linearly [L*] |
| Π149 Centred Vaughan currents | Solved (reduction); open (bound) | AAL | cofactors `≤3t^{71}`, filtered error `≤2h^d exp(−at/8)` [L*]; B145 |
| Π154 Carry class | Classified | — | [KR] |
| Π158 Reciprocity sources | Classified | producer | sign law: Möbius sign at odd order, parity at even order [L*]; three sign-carrying designs `(2,6),(3,4),(4,3)` [L*] |
| Π159, Π162 Family continuation | Solved at `7/8` [X]; Reduced (Lean) | a half-plane below `7/8` | two estimates with reciprocal kernels and a holomorphic nonvanishing correction give `Θ≤σ₀` [L*]; no `b<1` in Lean |
| Π160, Π163 The budget | Settled (exponents); Open (count) | method; `[13/15,7/8)` | room, sieve terms, corners [L*]; B174 |
| Π164 The half-plane map | Solved (receivers) | — | three rungs under `Θ≤b` [L*] |
| Π165 Levinson gate | Solved | sub | `κ=(1−log(18/5)/(13/10))/4` [L*] |
| Π167 The floor of the squares | Sharpened | producer; a half-plane below `13/15`, `5/6` | every Cauchy–Schwarz sieve stops at `5/6`; matched phases saturate [L*]; reduced to the long columns (Π175) |
| Π168 The wall of the frame | Solved | method | `H_η=L^S(6s−3,ψ₆η⁶)E`, `E` nonvanishing on `Re s>½`; frame premise below `2/3` ⇔ a zero-free half-plane of the phase `L`-function; correction zeros in `7/12≤Re s<2/3`, no nonvanishing continuation below `7/12` [L*] |
| Π169 Sieves over the Eisenstein integers | Partially solved | sub | quadratic sieve `≪(MN)^ε(M+N)` [L*]; sextic sieve open (A118d) |
| Π170 Primes in short progressions | Solved | sub | `(x,x+x^θ]`, every class; Siegel–Walfisz in windows [L*] |
| Π171 Cameras | Solved (in law) | sub | box cameras: mass `2A`, geometric exterior loss, order-uniform prime cost, fixed depth deficits paid [doc]; prime cost of the adaptive profile open (B59) |
| Π172 Logarithmic correlations of `λ` | Partially solved | sub | entropy decrement; circle method; prime kernel off the major arcs [L*]; MR for `λχ` open (A147) |
| Π173 The coupled tower | Solved | a half-plane | zero transfer `ρ↦6ρ−3`; reach `max(σ₀,3/5)` with estimates on every tower level; `7/12` under sextic GRH; fixed point of `(3+b)/6` [L*] (FC-T1) |
| Π174 The end of the Gauss-sum class | Classified [D] | producer | square-root endpoint `1−2/n` at conductor exponent two (`signedGram_phase_endpoints`) = `2/3` at `n=6` = the uncoupled wall; `½` only at `n=4`; sign-carrying designs have `κn=12` [L*]; [D] (D1, D2); B187 |
| Π175 The long columns | Sharpened | a half-plane in `(2/3,13/15)` | root numbers `G(u)γ₂(u)²`, `γ₂³=μ·u/\|u\|`; the reflected Gram is twisted by them; coherent at `R₀=2/3` (Kubota) [L*]; [C]; B185 |
| Π176 Short columns and the average row | Solved | method | short columns incoherent to every order; short sextic Gram diagonal; average row target-free [L*] (CR1, CR2, CR6) |

## Γ — selection, reflection, position

| Wall | Status | Strength | Content |
|---|---|---|---|
| Γ1 Self-return | Open | RH | strong recurrence ⇔ RH [F] |
| Γ15, Γ33, Γ35, Γ167 Rigidity of ζ | Solved (classification) | method | `L¹`/`L²` FE defects force the rational primes; a bounded count error forces them [L*] |
| Γ24, Γ62, Γ95 Mayer; Hecke dispersion; Krein flux | Sharpened | RH | [F] |
| Γ67, Γ183 Abscissa split and atoms | Solved (identity) | identity | RH ⇔ ZAL ∧ B13 ∧ Landing; `Θ<1⇔Θ∞<1` [L*]/[F] |
| Γ68, Γ69, Γ220 AAL and its receivers | Open; Solved (receivers) | sub | unit gap; non-attainment; moments; four sectors [L*] |
| Γ73, Γ145 One-offs; firewall | No-go (positive data) | — | [L*] |
| Γ86, Γ121, Γ122, Γ226 Modular horizon | Solved (identity) | RH (rate) | ringdown rate ⇔ strip; pulse rate = horocycle rate; filters [L*]; a rate from the horizon B178, B188 |
| Γ89, Γ148, Γ157 Physical positivity; modular conjugation; half-sided inclusions | No-go | — | [KR] |
| Γ96, Γ125, Γ154, Γ227 Count law | Solved (curves); Sharpened (ℤ); No-go (sections) | RH | hyperelliptic count [L*]; counts on prime rays ⇔ RH [L*] |
| Γ137, Γ161, Γ181 Positive annihilators | No-go | — | [KR] |
| Γ141, Γ185, Γ218 FE with approaching remainders | No-go | method | Riemann Gamma factor, residue one, count within one, off-line zeros approaching the line, no landing [L*] |
| Γ182 Landing | Sharpened | sub | B138 |
| Γ184 Deuring–Heilbronn | Classified (models); Open (ζ) | sub | an isolated pair above an infinite tail over the rational primes with a count rate [L*] (WZ5); B141 |
| Γ192 Two worlds | Solved; edge world excluded [X] | identity | [L*]; [X] |
| Γ195, Γ222 Index law; unit gaps | Solved (law); No-go (regulators) | RH | [L*] |
| Γ196, Γ197 Glued carrier; adelic Green kernel | No-go; Classified | — | [KR] |
| Γ198, Γ213, Γ216, Γ225 One matrix for number rings | Solved (identity) | identity | exact index for Dirichlet, Dedekind, class characters [L*] |
| Γ202, Γ214 Scattering tower | Solved (identity) | RH (sign) | tower = completed-zeta quotient [L*] |
| Γ203 Separation | Solved (receiver) | RH | ordinate injectivity ⇔ RH [F] |
| Γ206 Graded recurrence | Solved (receiver) | ≥qRH | `T^c` returns, `c>(30/13)(1−σ)` [L*] |
| Γ208 Flow | Solved (identity) | RH | prime lag positive definite ⇔ RH [L*] |
| Γ209, Γ212, Γ215, Γ224 Constituents | Solved | method | none bounded or Wiener with a zero [L*] |
| Γ217 Structures of the square | No-go / Classified | — | [KR]/[L*] |
| Γ219 Finite strata with both structures | Open | method | B157, A120 |
| Γ223 Symmetrization | No-go (first order) | method | [L*]; B172 |
| Γ228 Replication | No-go (normal families) | method | [L*] |
| Γ229 Pure objects as certificates | No-go | method | [L*] |
| Γ230 Integer count of a fake | Solved | method | fakes at every `β>½`; below `½` from a half-plane [L*] |
| Γ231 The top of a fake | Solved above `√x`; Open below | method | deletions have a real top; additions never fake; two-sided edits: a non-real pair alone at every count exponent `>½` [L*] (WZ1); below `½`: balanced or a real top, odd zeros above twice the count exponent are excluded [L*] (WZ2, WZ3); B183 |
| Γ232 Positivity on the line of the pole | Solved | method | [L*] |
| Γ233 Index of an Artin character | Solved (one character, quotients) | identity | `X³−2`; quotients of products of configurations [L*]; Brauer induction A150 |
| Γ234 Ultrametric dominance | Solved (Goss) | method | [L*]; no norm for ξ [F] |
| Γ235 Affine coincidences of zeros | Classified | method | halving pairs force `Θ≥2/3` [KR]; the probe's pairs `(ρ,6ρ−3)` [L*] |
| Γ236 Tangent data of `μ`, `λ` | Solved | identity | [F]; additive twists A144 |
| Γ237 Two-sided edits as models | Solved (countermodels) | — | over the rational primes with multiplicities `0,1,2`, integer norms, a count rate: every finite layer; an isolated pair above an infinite half-scale tail; every configuration approaching the line; every sparse configuration; quartets symmetric in a strip; a finite layer of ζ edited away [L*] (WZ1, WZ4–WZ7) |
| Γ238 Laws of the edits | Solved (laws) | method | balance or real top below a fake zero; parity of orders above `2max(β,c₀,θ/3)`; additions paid in full `κ₊≤max(β,κ₋)`; count floor; floor of prime edits `≥13/30`, `≥1/6` on the strip `c=1/3` [L*]/[doc] (WZ2–WZ4, WZ7) |
| Γ239 The FE axis | Solved at `L¹`/`L²`; Open beyond | method | a fake continuing to the line has a non-integrable FE defect [D] (D5); the least defect of a fake B186 |
| Γ240 The zero field | Solved (identity); Classified (topology) | RH | `L` algebraic and normal over `K`; `L=K` ⇔ RH [F]; Euclidean-continuous source automorphisms are identity and conjugation; detecting quadratic characters exist iff splitting and a nonzero width; over the field of squared widths the group is the sign families killing every square-class relation [doc] (GZ1, GZ2) |
| Γ241 Virtual configurations; number rings | Solved (identity) | identity | the index of `W_A−W_B` counts zeros and poles off the line; Dedekind's divisibility on the line as no negative square; the neutral form of a number ring has index `1+` right zeros; its contacts are its point counts over `𝔽_{p^m}` [L*] (AG-V1–AG-V4) |

## Scoped no-gos and surviving replacements

| Boundary | Exact scope and survivor |
|---|---|
| sizes of the contacts | positive to rung `1−o(1)`; the Liouville twist fails at `1+o(1)` (Σ161). Survivor: a saving that fails for the Liouville twist (B159) |
| windows below the logarithmic radius; one-sided floors of one length | models (Σ146, Σ147). Survivors: the logarithmic radius; floors at every length |
| explicit formula, positivity, Euler products over integer norms or the rational primes with multiplicities `0,1,2`, linear counting, count rates | every finite layer, tail and landing failure realized (Π102, Γ237). Survivor: the Euler product with the FE as an identity, or with a count below the floor |
| a count rate above `√x` forcing a real top | two-sided edits (Γ231). Survivor below `√x`: balanced edits only (B183) |
| the Euler product with an FE defect in `L¹` or `L²` | rigid: the rational primes (Γ15). Survivor: non-integrable defects (B186) |
| the cubic probe's frame | coupled tower, `3/5` (Π173). Survivor: a source whose transfer fixes the line, or a source without completion (B187) |
| the cubic probe's estimates | square-root endpoint `2/3` (Π174). Survivor inside: the long columns down to `2/3` (B185) |
| Cauchy–Schwarz row sieves; geometry and row counts | `5/6`, `13/15` (Π163, Π167). Survivors: B174, B185 |
| the pole-cleared family step | false premise (Π159). Survivor: reciprocal kernels with a correction |
| a mean square containing the principal twists; positive weights | the half-plane itself; not generic below `n/(n−1)` (Π163) |
| bounded and Wiener constituents | none (Γ224) |
| sections, towers, own combs, paths | identities; RH at every parameter (Σ169, Γ217) |
| regulators | the count of the limit (Σ150, Γ222). Survivor: a realization with one negative square (B171) |
| certificates other than `Λ` | converge to `Λ` (Σ160) |
| linear statistics under projection | Γ223. Survivor: B172 |
| replication by normal families | Γ228. Survivors: transport, currents (B89, B145) |
| amplification over the moment order | sup bounds (Γ220) |
| bilinear statements as parity-sensitive | sign-blind (Π46); AAL is Liouville-invariant [D] |
| mean values below the height as detectors of single zeros | finite relocation invisible [KR]; `θ<½` proved (Π161) |
| positivity alone at 70% | cost `>13/10` (Π166). Survivor: B150 |
| the return transfer | RH under a strip (Π148) |
| families by averaging | fixed part (Π145). Survivor: a family used through its rightmost zero (Π159) |
| a verified height through the double-exponential rate | `C` not explicit (Σ171). Survivors: A2, A3, A142 |
| the continuum form as positivity improving | Markov stability fails on long intervals [KR]. Survivor: the finite-scale one-sign ground vector of the neutral part (Σ176) |
| Markov, Perron, size-only payment, floor tower, universal multipliers, fixed theta heads, positive Laplace mixtures, KMS, internal modular conjugation, bounded-height Diophantine certificates | as recorded [KR] |

## Bridges

| Bridge | Anchor |
|---|---|
| one inequality per prime: Weil test = Stepanov count = count on a prime ray = upper side = two-bump comb | SOSZ, HFP [L*] |
| one matrix at finite scale: Weil's form on step packets = charges + potential + Dirichlet form; neutral index = right zeros + 1 | AGZ [L*] |
| Morse index of the aperture path = Maslov index of the conormals against the graph of Weil's operator | AGZ [L*] |
| polar Lagrangian: charged null modes = crossings with the charge axis in `ℂ²×ℂ²` | AGZ [L*] |
| one scale: saving, rung, depth, mollifier, level, signal, twist exponent, tail growth, critical-comb growth, rate | SA, FCT, AGZ, BHR [L*]; [D] |
| the width on one sequence: critical-comb growth exponent = zero width | AGZ [L*] |
| half-plane route = two estimates for one completed sum; correction = phase `L`-function at `6s−3`; zero transfer `ρ↦6ρ−3` | FCT, CRF [L*] |
| Möbius = cube of a cubic Gauss sum; root number of a row = square of the theta coefficient | MMD, CRF [L*] |
| a mean square over the principal twists = the half-plane of the target | FCT [L*] |
| AAL = unit gap = no accelerating filter | FFA, BHR [L*] |
| B13 ⇔ packet index `0` or `∞` | ACS [L*] |
| the door of world I: Euler product + FE identity, or + count below the floor | WZC, EFT, APD [L*]; [D] |
| the FE with an integrable defect = the rational primes | EFT [L*] |
| a count rate = nothing about the zeros; a bounded count error = the rational primes | SPAL, WZC [L*] |
| regulated energy at a fixed height = the closed Weil form; every regulator has the count of its limit | HAT, FFA [L*] |
| window sign ⇐ verification at `exp(exp(Ca))` | VHR [L*] |
| quotients of `L`-functions: index = zeros and poles off the line | AGZ [L*] |
| the zero field: `L=K` ⇔ RH | GaloisTheoryOfZeros [F] |
| twisted moments below the square root ⇒ a positive proportion on the line | MZF [L*] |

## Strength of the open walls

- **RH:** Σ1, Σ6 (all ranks), Σ20, Σ49, Σ56, Σ66, Σ73–Σ80, Σ113, Σ129, the minimal face, Σ150 (sign), Σ153, Σ154/Σ165/Σ166, Σ155, Σ160, Σ164, Σ168, Σ173 (every `a`), Σ175 (no crossing), Σ176 (every window), Π2, Π42, Π126, Π127, Γ1, Γ24, Γ62, Γ95, Γ121, Γ122, Γ154, Γ195, Γ203, Γ208, Γ214, Γ222, Γ240.
- **≥qRH** (open below `7/8`): Σ4, Σ28, Σ162, Σ173 (one `a>1/8`), ZAL, Π3, Π159/Π162 (B161), Π163 (B174), Π167/Π175 (B185), Γ206, Γ226 (a rate `δ>1/16`).
- **AAL:** Π114, Σ147, Γ220, Π149.
- **sub:** Σ27, Σ82, Σ116, Σ117, Σ171, Σ174 (A146), Π7, Π22, Π51, Π53, Π54, Π65, Π80, Π94, Π161, Π169, Π171, Π172, Γ68, Γ182, Γ184, B13.
- **method / producer / indep.:** Σ135, Σ139, Σ177 (B104), Σ163 (B156), Π158 (B180), Π174 (B187), Γ219 (B157), Γ222 (B171), Γ223 (B172), Γ226 (B178, B188), Γ231 (B183), Γ233 (A150), Γ234 (a norm for ξ), Γ239 (B186).
