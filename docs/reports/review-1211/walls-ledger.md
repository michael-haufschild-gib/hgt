# Walls ledger — status quo

**Corpus checkpoint:** `dd55ee70d9` (2026-11-12), working-tree sources included. Fact log: `logs/review-1211-rev2-facts.md` (cited as "log §n"). Companions: [route-obstacles.md](route-obstacles.md), [route-unification-ledger.md](route-unification-ledger.md), [obstacles-summary.md](obstacles-summary.md).

Three wall families carry the frontier. **Σ** is the critical sign of the window form, **Π** the precision and production of the prime count, **Γ** the selection of ζ, the reflection of its zeros and their position. They meet in one inequality per prime, one finite-scale matrix, one path of Lagrangians, and one scale.

- **The minimal face.** RH ⇔ `P(p)≤A(p)+K` at the primes of arbitrarily late logarithmic windows, outside `Ce^{δT}` primes per window; equivalently the upper side, `ℕ`-counts on surviving rays, one moment exponent, copositive prime planes [L*] (log §15). No window below the logarithmic radius decides [L*].
- **The finite-scale matrix.** RH ⇔ the neutral part of the step-packet matrix has exactly one negative square on every window `(R,R+J]`, `R≤J` [L*]. Certified on windows with `50J≤53R` at every block size, on narrow windows `16J≤R` (at most one), on the first blocks of ratio four, and on thin packets at every ratio [L*] (log §2, §14).
- **The induction step.** Two windows glued through the product of their charges hold exactly one bound state iff their susceptibilities multiply to at least one; the union of two adjacent windows holds at most the bound states of the glued model with lowered potentials [L*] (log §2).
- **The path.** The index of the restricted Weil form is the number of crossings of the aperture path; the crossing multiplicity is a Lagrangian intersection number; the supremum at energy zero is the number of right zeros; RH ⇔ no crossing [L*] (log §14).
- **The critical object.** RH, or a finite critical ratio with a critical half-line state: unique up to sign, zero energy, weak equation, Laplace transform without zeros in the open right half-plane [L*] (log §1).
- **The scale.** Saving, rung, depth, mollifier exponent, level, signal exponent, twist exponent, floor exponent, critical-comb growth, relaxation rate: one number [D]. `b=7/8` is `[X]`; the open part is `½<b<7/8`.
- **The producer.** One class with an exact end: square-root cancellation gives `2/3`; the frame of every `6r`-periodic Gauss pairing has its fixed point at `(4r−1)/(6r−1)≥3/5` [L*] (log §16).
- **The door of world I.** No fake has a decaying FE defect; fake edits have defect energy `≥cT log T`; if `Θ<1`, fakes with defect energy `≤C_εT^{1+ε}` exist; fakes exist at every count exponent above the pair, and an odd fake zero needs a count exponent of at least half its real part [L*] (log §3, §9, §12, §18).

[Frontier](../rh-current-frontier-map.md): **38 live formulations, 12 candidates**. [Scoped obstructions](../rh-killed-routes.md).

**Status.** **Solved** (the face is a theorem), **Partially solved**, **Sharpened** (open, exact form a theorem), **Reduced** (theorem-level equivalent named), **Open**, **No-go** (mechanism refuted), **Classified**, **Settled** (a method question answered). **Strength:** RH, ≥qRH, AAL, sub, indep., identity, method, producer. **Evidence:** `[L*]` Lean statement read at the declaration and recorded in the fact log; `[doc]` module docstring; `[F]`, `[KR]` stated by the frontier map and the scoped-obstruction ledger; `[S]` unfinished per the frontier map; `[card]` proved on the pipeline card of B186, no Lean declaration; `[D]` deduction; `[C]` classical, from memory; `[A]` assessment; `[X]` the external theorem `Θ≤7/8`, taken as proved, its native steps just work (A118). **≥qRH** is open where it gives a half-plane below `7/8`.

## Σ — critical sign

| Wall | Status | Strength | Content |
|---|---|---|---|
| Σ1 Weil's sign | Sharpened | RH | RH ⇔ `W≥0` on every window [F] ⇔ `Ψ` locally bounded [F] ⇔ the floor on logarithmic prime windows [L*] ⇔ feasible weights at every aperture [L*] ⇔ no crossing of the aperture path [L*] ⇔ one negative square of every neutral window [L*] ⇔ subpolynomial critical comb [L*] |
| Σ1b, Σ1k Subcritical regime | Solved | sub | complete tilted-spline matrix positive definite below the eighth root eventually [L*]; one fixed small multiple of `(log N)^{1/8}` [F] |
| Σ1c–Σ1x Critical-curve calculus | Classified | sub / method | [F]/[KR] |
| Σ1u, Σ129 Threshold law | Solved (identities) | RH | `0<R_PD=…=R_halfline≤W=…`, each infinite iff RH [F] |
| Σ4 Finite index / heat count | Sharpened | ≥qRH; RH for index 0 | finitely many non-real zeros at every positive time, infinitely many at every negative time [L*]; `N_d≤300√(d log d)` [F] |
| Σ6 Rank and degree | Partially solved | RH | theta ranks `≤14`; rank `N` from verified height [F] |
| Σ13–Σ15 Tensor amplification; deformation to positive matrices; separable assemblies | No-go | — | [KR] |
| Σ20 Scheduled sums | Open | RH | receivers only [F] |
| Σ27 Window stages | Partially solved | sub | block-matrix margin `1/5000` on windows with `50J≤53R` [L*]; `{2,3,4}` kicks below `991/1000` of the Lévy energy for `2c<log 5` [F] |
| Σ28, Σ41 Negativity budget; aperture–depth | Sharpened / Classified | ≥qRH; sub | positivity at aperture `a` confines zeros up to `2πe^a` to depth `<exp(−c log³\|γ\|)` [L*]; an isolated zero of depth `δ` is negative on the rung `κ>1/(2δ)` [L*] (log §24) |
| Σ42, Σ53, Σ57 Markov, size-only, Perron | No-go | — | [KR] |
| Σ49 Reality by continuation | Sharpened | RH | RH ⇔ every zero of every `H_t`, `t>0`, simple [L*] |
| Σ56, Σ66, Σ113 Onset; contact; restoring bound | Sharpened | RH | [F] |
| Σ73–Σ80 Sector receivers | Sharpened | RH | PA, HCF, TT, RN, PTR, GTA, TG [F] |
| Σ82 Finite-rung principle | Partially solved | sub | height 67 [F]; verification through a height ⇒ the sign on `[−a,a]` [L*] |
| Σ98, Σ133 Theta heads | No-go (fixed heads); Sharpened | RH | [KR]/[F] |
| Σ116, Σ117 Weighted Gårding; typical heights | No-go; Solved in law | sub | exceptional heights of measure `≤T^{1−1/(2κ)+ε}` on the rung `κ` [L*] |
| Σ135, Σ139 Pole channel; half-line ground states | Sharpened | method | RH, or `R_polar<W₀`, or `R_polar=W₀` with a polar-orthogonal critical state [L*]; a charged critical state gives `R_polar<W₀` [L*]; on the aperture side: no neutral ground mode ⇔ `μ(a)<μ₀(a)` [L*] (B104) |
| Σ140 Holomorphic multipliers | No-go | — | [KR] |
| Σ137–Σ151 The minimal face | Solved (identity) | RH; ≥qRH at `p^σ` | five forms; `Θ<1` ⇔ floor `−Kp^α`, `α<½` [L*] |
| Σ146, Σ152 Resolution | Settled | method | prescribed sublogarithmic windows do not bound the class; a density-matched configuration survives [L*] |
| Σ147 Bounded windows against world I | Solved (receivers) | AAL | floors at every length `(k+1)π/67` give AAL [L*]; one length has models [F] |
| Σ150, Σ172 Regulated energies | Solved (identity); No-go (source) | RH | a Green–Weil energy floor gives RH [L*]; the clock lies below Weil's form [F] |
| Σ153 Hodge index of the comb pairing | Solved (identity) | RH | RH ⇔ the neutral Gram has at most one negative square [L*] |
| Σ154, Σ165, Σ166 Comb at finite scale | Solved (identity) | RH | RH ⇔ a positive mass floor on every ratio window [L*] |
| Σ155, Σ158 Forced data | Solved (identity) | RH | constant (`c≤0 ∧ RH`), weights (`RH ∧ w=Λ`), contacts at their price [L*] |
| Σ156 The exceptional square | Solved | method | trivial aperture `log log q+o(1)` [L*]; a system aligned with a height fails above `log log T+log 2` [L*] |
| Σ157 Selectivity of windows | Solved | method | weights invisible for `2a<log 2` [L*] |
| Σ160, Σ170 Feasible weights; certificates | Solved; No-go (freedom) | RH | feasible at every aperture ⇔ RH; feasible systems converge to `Λ` [L*] |
| Σ161 Trivial aperture | Solved (sharp) | method | [L*]/[F] |
| Σ162 Exchange rate | Solved (receivers); rungs `κ<4/3` by `[X]` | a half-plane below `7/8` | one theorem for saving, rung, isolated depth, mollifier depth [L*]; no rung above one in Lean |
| Σ163 Depth on the ladder | Settled (configurations); Open (ζ) | method | [F]; B156 |
| Σ164 Level-one dressed positivity | Solved (identity) | RH | level one gives AAL and `Θ=½` [L*] |
| Σ167 Index in the aperture | Solved (identity) | identity | `negativeRank b E=Σ_{a<b}weilNullity a E` = number of eigenvalues below `E` [L*] |
| Σ168 Null modes | Sharpened | RH | RH ⇔ no aperture carries a null mode at `E=0`; a single simple null mode on a short aperture [L*] |
| Σ169 Paths | Settled (no transport) | method | a contact altered and paid at its price is RH at every parameter [L*] |
| Σ171 Verification rate | Solved (rate) | sub | RH through `exp(exp(Ca))` ⇒ sign on `[−a,a]`; `C` not explicit [L*] (A142) |
| Σ173 Power tails | Solved (identity) | RH (every `a`); ≥qRH (one `a>1/8`) | Abel integrability ⇔ `a+w≤½`; convergence ⇔ every zero has `Re ρ<1−a`; the critical comb never converges; its growth exponent is the width [L*] |
| Σ174 Matrices and combs | Partially solved | sub (each ratio) | margins `1/20`, `1/100` at the first block sizes of ratio four; refinement transfer of margins; at most `(Q−1)⌈e^{E_Q}⌉` negative squares at every block size, `300000` at ratio four [L*]; index zero at every block size of ratio four (A146) |
| Σ175 Morse index = Maslov index | Solved (identity) | identity | crossing multiplicity = Lagrangian intersection number of the aperture conormal with the graph of Weil's operator; index = number of crossings; supremum at `E=0` = number of right zeros [L*] (log §14) |
| Σ176 Finite-scale Hodge index of the neutral part | Solved (identity); Partially solved (sign) | RH (every window) | RH ⇔ exactly one negative square of every neutral window with `R≤J`; certified for `50J≤53R` at every block size; the neutral index is at most the block index plus one, and the pole adds one negative square [L*] (log §14, §22) |
| Σ177 Polar Lagrangian and charged null modes | Sharpened | method | below `μ₀(a)` every crossing is charged and the rank is at most two; unconditional on apertures `≤½(log 2+1/50)`, energies `<1/20` [L*]; B104 |
| Σ178 The gluing law | Solved (law); Open (actual windows) | method; sub at each ratio | glued form `A(x)+B(y)−2(u·x)(v·y)`: exactly one negative square if `αβ≥1`, exactly two if `α,β<0`, `αβ<1`; the union of adjacent windows holds at most the bound states of the glued model with potentials lowered by the excess couplings [L*]; at least those of the model with raised potentials [D]; no susceptibility of an actual window is bounded outside the certified ranges (B189, A156) |
| Σ179 Bound-state counts from the potential | Solved | sub | couplings `≥λ` ⇒ index `≤1+#{blocks with potential <−λJ}`; `16J≤R` ⇒ index `≤1` from the potential `≥−½` and the couplings `≥1/(2J)` [L*] |
| Σ180 Charged ground vector at finite scale | Solved (`4J≤R`) | method | a ground vector of the block matrix has one sign and both charges nonzero of one sign [L*]; windows with `R≤J` open (B104) |
| Σ181 The critical half-line state | Sharpened | RH (existence); method (charge) | RH, or a state at a finite `W₀`: zero full energy, mixed energy zero against the energy domain, unique up to sign, `∫F e^{zu}≠0` on `Re z>0`, a logarithmic convolution of one `L²` half-line source [L*] (log §1, §13); open: the pairing with the polar source, Laplace zeros on `Re z=0` |
| Σ182 Li coefficients on the comb | Solved (identity) | identity | `combW(Icc 1 N)(laguerreTail n N)/N→Re xiLiPaired n`; without RH negative and positive paired Li indices recur in windows of bounded length [L*] |

## Π — precision and production

| Wall | Status | Strength | Content |
|---|---|---|---|
| Π1, Π4 Global law; window precision | Solved (equivalences) | RH | [F] |
| Π2 Deciding input | Open | RH | no native input at square-root precision [F] |
| Π3, Π67, Π70, Π71 Producer cost and rates | Solved (exponent scale) | sub / ≥qRH / RH | polynomial rate ⇔ Mertens power saving [L*]; `bestRate` bounds [F] |
| Π7, Π151, Π166 Census | Partially solved; No-go (positivity) | sub | `0.67250071` in `Zeta23` objects; positivity cost `>13/10` [L*] |
| Π22, Π65 Near-line density | Reduced | sub | squared right-depth moment `o(V)` [KR]; first-moment density `o(T)` (B57) |
| Π40, Π148 Strip self-improvement; return transfer | Open; Settled (strength) | RH | under `Θ<1` the transfer ⇔ RH [F]; `[X]` |
| Π41, Π42, Π56, Π161 Mean-value ladder | Solved (`θ<½`); Sharpened | RH | twisted moments; depth `<1/(2θ)+ε` from dyadic boundedness at `θ>1` [L*] |
| Π46, Π55 Parity blindness | No-go | — | [KR] |
| Π51 Vinogradov–Korobov barrier | Open | sub | twisted Chebyshev sums of ζ `≤K/(log X)^4` on `(log X)^{19}≤\|τ\|≤X` [L*]; `[X]` past it |
| Π53, Π54, Π80 | Open | sub | [F] |
| Π66, Π125, Π126, Π146, Π153 Integrality; Stepanov | Solved (price) | RH (degree bound) | `p^{11/12}` [F] |
| Π93 Möbius as a cubic Gauss coefficient | Solved (identity) | past VK | cube identity [F] |
| Π94, Π128–Π130, Π137 Returns | Partially solved | sub | `c·y^{1−b}≤log t` under `Θ≤b` [L*] |
| Π102, Γ221 One-structure worlds | Solved (countermodels) | — | FE with Gamma factor and count, no landing; Euler product over the rational primes with a count rate, every finite layer [L*] |
| Π105, Π127 Orientation cover | Solved (identity) | RH | centred count `M(N)=Ω_±(√N)` [F] |
| Π112–Π114 Thick crude count | Sharpened | AAL; RH with attainment | [F] |
| Π141, Π142, Π145 Families | Classified; No-go | method | fixed parts [F]/[KR] |
| Π147, Π155, Π156 The square; sections | Classified | — | sections of the first `N` graphs in aligned boxes: volume over `N!` [L*] |
| Π149 Centred Vaughan currents | Solved (reduction); open (bound) | AAL | growing-order current reduced to centred cofactors [F]; B145 |
| Π154 Carry class | Classified | — | [KR] |
| Π158 Reciprocity sources | Classified | producer | Möbius sign at odd order of a Gauss sum, parity at even order [L*]; designs `(2,6),(3,4),(4,3)` [L*]/[F] |
| Π159, Π162 Family continuation | Solved at `7/8` [X]; Reduced (Lean) | a half-plane below `7/8` | two estimates with reciprocal kernels for every Hecke character give `Θ≤σ₀` [L*]; unconditionally in Lean `Θ≤1` |
| Π160, Π163 The budget | Settled (exponents); Open (count) | method; `[13/15,7/8)` | binding bin `δ=79/204`, sieve threshold, corners `8/9`, `49/54` [L*]; `25/28` [F]; B174 |
| Π164 The half-plane map | Solved (receivers) | — | three rungs under `Θ≤b` [L*] |
| Π165 Levinson gate | Solved | sub | [F] |
| Π167 The floor of the squares | Sharpened | producer; a half-plane below `13/15`, `5/6` | every Cauchy–Schwarz sieve stops at `5/6` [L*]; reduced to the long columns (Π175) |
| Π168 The wall of the frame | Solved | method | the correction factors through a Grössencharacter `L`-function at `6s−3`; the continued correction has infinitely many zeros in `7/12≤Re s<2/3` [L*] |
| Π169 Sieves over the Eisenstein integers | Partially solved | sub | quadratic large sieve [L*]; a sextic sieve is absent |
| Π170 Primes in short progressions | Solved | sub | `(x,x+x^θ]`, every reduced class [L*] |
| Π171 Cameras | Solved (in law; adaptive isolation) | sub | adaptive clusters with complete exterior mass `≤¼`; boundary exterior mass at fixed width; centred prime mean squares [L*]; pointwise prime cost at the selected centres (B59) |
| Π172 Logarithmic correlations of `λ` | Partially solved | sub | reduction to prime dilates; prime kernel off the major arcs [L*]; open: a bound for `V(b/s,T)` (A147) |
| Π173 The coupled tower | Solved | a half-plane | zero transfer `ρ↦6ρ−3`; reach `max(σ₀,3/5)` with estimates on every level; `7/12` under sextic GRH [L*] |
| Π174 The end of the Gauss-sum class | Classified | producer | square-root endpoint `(n−4)/(n−1)` in the twist exponent, the half-plane `1−2/n`: `2/3` at `n=6`, `½` only at `n=4` [L*]; [D]; B187 |
| Π175 The long columns | Sharpened | a half-plane in `(2/3,13/15)` | root numbers `G(u)γ₂(u)²`; the Gram of two rows is a completed sum twisted by them [L*]; the half-plane `1−2/(3(6R₀−1))` for a remainder exponent `R₀≥2/3` [D]; B185 |
| Π176 Short columns and the average row | Solved | method | short columns cancel; short Gram bounded; average row target-free [L*] |
| Π177 The barrier of the `6r`-periodic pairings | Solved | producer | local resonance norm `Q^{(4r−1)−6rs}`: uncoupled boundary `2/3` for every `r`; coupled fixed point `(4r−1)/(6r−1)≥3/5`, equal to `3/5` iff `r=1` [L*]; a pairing `(c,k)` has boundary `(c+1)/k` and fixed point `c/(k−1)` [D]; B187 |
| Π178 Poles of the theta-square series | Solved (untwisted) | method | `Σ_I N(I)^{−w}τ(I)²=C̄²ζ_K(3w−1)·(squarefree sum)`; `(s−4/3)²M·D→108π³r³`; rotated correlation `54π³r³`; twisted squarefree combination a simple pole; a rotation by `ε≠±1` reads the layers `m≥2` [L*]; layers `m=0,1` and the twisted column (A148) |
| Π179 The port of `[X]` | Partially solved | a half-plane (`7/8`) | `beta ≤ 7/8` from a uniform continuation margin; centred exceptional rows; source shells; radial comparison with retained energies as hypotheses [L*]; retained-energy induction and detector saving (A118) [F] |
| Π180 Short-interval Liouville | Solved (`χ≠1`); Partially solved (`χ=1`) | sub | `Σ_{k<X}\|Σ_{X+k<n≤X+k+h}λχ(n)\|²≤εh²X` for `χ≠1`; for `χ=1` top-scale blocks `≤(log X)^{−3}` above polylogarithmic frequencies, the ladder on a frequency set [L*], twisted partial sums `o(N)` for `2\|τ\|≤√N` [S]; the low-frequency mean square (A147) |

## Γ — selection, reflection, position

| Wall | Status | Strength | Content |
|---|---|---|---|
| Γ1 Self-return | Open | RH | strong recurrence ⇔ RH [F]; RH ⇔ relative compactness of the orbit and of its bubbles [L*] |
| Γ15, Γ33, Γ35, Γ167 Rigidity of ζ | Solved (classification) | method | `L¹` defects, and `L²` defects of polynomial size, force the rational primes [L*]; a defect `O(\|t\|^{−½+ε})` forces them among unweighted countable systems [card] |
| Γ24, Γ62, Γ95 Mayer; Hecke dispersion; Krein flux | Sharpened | RH | [F] |
| Γ67, Γ183 Abscissa split and atoms | Solved (identity) | identity | RH ⇔ ZAL ∧ B13 ∧ Landing; `Θ<1⇔Θ∞<1`; `¬(Θ<1)` ⇔ both abscissas equal one [L*] |
| Γ68, Γ69, Γ220 AAL and its receivers | Open; Solved (receivers) | sub | AAL ⇔ at most one or infinitely many zeros right of every line [L*]; unit gap; non-attainment; moments [F] |
| Γ73, Γ145 One-offs; firewall | No-go (positive data) | — | AAL, or a meromorphic tempered Euler product with real weights and a one-off pair above the frontier [doc] |
| Γ86, Γ121, Γ122, Γ226 Modular horizon | Solved (identity) | RH (rate) | RH ⇔ quarter ringdown rate; pulse rate = horocycle rate; Weyl order `cΛ≤N(Λ)≤CΛ`; no cusp form below `3/16` on congruence groups [L*]; a rate from the horizon B178, B188 |
| Γ89, Γ148, Γ157 Physical positivity; modular conjugation; half-sided inclusions | No-go | — | [KR] |
| Γ96, Γ125, Γ154, Γ227 Count law | Solved (curves); Sharpened (ℤ); No-go (sections) | RH | hyperelliptic count [F]; counts on prime rays ⇔ RH [L*] |
| Γ137, Γ161, Γ181 Positive annihilators | No-go | — | [KR] |
| Γ141, Γ185, Γ218 FE with approaching remainders | No-go | method | Riemann Gamma factor, residue one, count within one, off-line zeros approaching the line, no landing [L*] |
| Γ182 Landing | Sharpened | sub | B138 |
| Γ184 Deuring–Heilbronn | Classified (models); Open (ζ) | sub | an isolated pair above an infinite half-scale tail over the rational primes with a count rate [L*]; B141 |
| Γ192 Two worlds | Solved; edge world excluded [X] | identity | [L*]; [X] |
| Γ195, Γ222 Index law; unit gaps | Solved (law); No-go (regulators) | RH | `Λ(s)/Λ(s+N)` has a unit gap iff RH [L*] |
| Γ196, Γ197 Glued carrier; adelic Green kernel | No-go; Classified | — | [KR] |
| Γ198, Γ213, Γ216, Γ225 One matrix for number rings | Solved (identity) | identity | exact index for Dedekind zeta functions [L*]; Dirichlet and class characters [F] |
| Γ202, Γ214 Scattering tower | Solved (identity) | RH (sign) | tower = completed-zeta quotient [L*] |
| Γ203 Separation | Solved (receiver) | RH | ordinate injectivity ⇔ RH [F] |
| Γ206 Graded recurrence | Solved (receiver) | ≥qRH | `T^c` returns, `c>(30/13)(1−σ)` [F] |
| Γ208 Flow | Solved (identity) | RH | prime lag positive definite ⇔ RH [F] |
| Γ209, Γ212, Γ215, Γ224 Constituents | Solved | method | none bounded or Wiener with a zero [F] |
| Γ217 Structures of the square | No-go / Classified | — | [KR] |
| Γ219 Finite strata with both structures | Open | method | B157, A120 |
| Γ223 Symmetrization | No-go (first order) | method | linear statistics are not monotone under projection [L*]; B172 |
| Γ228 Replication | No-go (normal families) | method | normalizations of translates tend to zero at a finite layer [L*] |
| Γ229 Pure objects as certificates | No-go | method | [F] |
| Γ230 Integer count of a fake | Solved | method | an integer-norm fake with remainder `O(x^β)`, `β<1`, has positive density; fakes at every count exponent above the pair [L*] |
| Γ231 The top of a fake | Solved above the pair; Open below `√x` | method | a non-real pair alone on top at every count exponent in `(Re ρ,1)`, `½<Re ρ<14/15`; at `β≤½` balanced or a real top; an odd zero of the edit exponential needs `Re ρ≤2max(β,c₀,θ/3)`; the greedy pair twin has `β≥Re ρ/2` [L*]; B183 |
| Γ232 Positivity on the line of the pole | Solved | method | [F] |
| Γ233 Index of Artin characters | Solved (one character, quotients, powers); Reduced (all characters) | identity | `X³−2`; quotients of configurations; `n` copies of a quotient; Brauer induction for finite groups [L*]; the reciprocity law for monomial characters (A154) |
| Γ234 Ultrametric dominance | Solved (Goss) | method | [L*]; no norm for ξ [F] |
| Γ235 Affine coincidences of zeros | Classified | method | halving pairs force `Θ≥2/3` [KR]; the probe's pairs `(ρ,6ρ−3)` [L*] |
| Γ236 Tangent data of `μ`, `λ` | Solved | identity | [F]; additive twists A144 |
| Γ237 Two-sided edits as models | Solved (countermodels) | — | over the rational primes with multiplicities `0,1,2`, integer norms, a count rate: every finite layer; an isolated pair above an infinite half-scale tail; zeros decreasing to the line; zeros rising to a line; sparse configurations; quartets symmetric in a strip; a finite layer of ζ edited away [L*] (log §9, §18) |
| Γ238 Laws of the edits | Solved (laws) | method | balance or real top; parity of orders above `2max(β,c₀,θ/3)`; `(1−θ)Re ρ≤2β(2−θ)`; floor of prime edits `≥13/30` [L*]; the order law at higher multiples (A155) |
| Γ239 The FE axis | Solved (to a window) | method | no fake has a decaying defect (Abel floor from two unequal coefficients); fake edits: `∫‖g‖²e^{−\|t\|/T}≥(A²/(256πp₀))T log T`, `g` not `≤c√log\|t\|`; pair and quartet twins: `g=2iζ·Im M` [L*] (log §3); the window between `T log T` and `T^{1+ε}` (B191) |
| Γ240 The zero field | Solved (identity); Classified (group) | RH | `L` algebraic and normal over `K`; `K` = the field of the zeros ⇔ RH; conjugation central; orbits finite; no transitivity; critical zeros fixed; over the squared widths the group is the sign families annihilating the square-class relations; the reflection lifts iff `−1` is not a square [L*] (log §4, §24) |
| Γ241 Virtual configurations; number rings | Solved (identity) | identity | the index of a difference counts zeros and poles off the line; Dedekind's divisibility on the line as no negative square; the neutral form of a number ring has index `1+` right zeros; its contacts are its point counts over the finite fields [L*] |
| Γ242 The frontier dichotomy | Solved | method | `Θ=1` with AAL, or `Θ<1` and for every `½<β₀<3/2−Θ`, `ζ(β₀+iγ₀)≠0`, `β₀<β_c<1` a two-sided edit: fake at `β_c`, positive density, continuation below `½` with the zeros of ζ and the pair, `‖g‖≤K_ε\|ζ(½+2it)\|(1+\|t\|)^ε`, mean square `≤C_εT^ε` [L*] (`frontier_dichotomy`); among real signed weights a fake with a bounded defect and Abel floor `≥1/12` [L*]; the lower bounds for a fake's defect are those of its least deleted prime [card]; fakes at `β₀≥3/2−Θ` (B191) |
| Γ243 Prime trace and reflection fields | Solved (identity); Open (orbits) | RH | an embedding fixing the prime trace field sends a zero to a zero with centred real part `±` the original; the reflection field equals the trace field ⇔ RH; an orbit meeting the line lies on it; rational real parts have the orbit `{ρ,ρ̄}`; `p^ρ`, `r^ρ` both algebraic force `Re ρ∈ℚ` [L*]; orbits at irrational real parts, an automorphism besides conjugation (B190) |
| Γ244 Objects of a failure | Solved (identities) | RH | RH fails ⇔ an odd bound state ⇔ a defective hard-edge block ⇔ a point right of the line with `Re ξ′/ξ<0` ⇔ a negative definite Markov plane ⇔ an aperture with an empty feasible set [L*] (log §20); the critical half-line state (Σ181) |

## Scoped no-gos and surviving replacements

| Boundary | Exact scope and survivor |
|---|---|
| sizes of the contacts | positive to rung `1−o(1)`; aligned systems fail above `log log T+log 2` (Σ156, Σ161). Survivor: a saving that fails for the Liouville twist (B159) |
| windows below the logarithmic radius; one-sided floors of one length | models (Σ146, Σ147). Survivors: the logarithmic radius; floors at every length |
| explicit formula, positivity, Euler products over integer norms or the rational primes with multiplicities `0,1,2`, linear counting, count rates | every finite layer, tail and landing failure realized (Π102, Γ237). Survivor: the reflection up to a decaying error, or a count below half the layer |
| a count rate above the pair forcing a real top | two-sided edits (Γ231). Survivor below `√x`: balanced edits only (B183) |
| the functional equation up to an error of mean size `T^ε` as a selector of ζ among prime edits | fakes if `Θ<1` (Γ242). Survivor: a decaying defect (Γ239); the gap `T log T` to `T^{1+ε}` (B191) |
| a bounded FE defect as a selector among real signed weights | a fake (Γ242). Survivor: decay |
| a lower bound for the defect in the depth of the fake zero alone | constants of the least deleted prime [card]. Survivor: a joint inequality with the count remainder |
| the frame of the cubic probe and of every `6r`-periodic Gauss pairing | fixed point `≥3/5` (Π173, Π177). Survivor: a pairing with `c/(k−1)<3/5` (B187) |
| the cubic probe's estimates | square-root endpoint `2/3` (Π174). Survivor inside: the long columns down to `2/3` (B185) |
| Cauchy–Schwarz row sieves; geometry and row counts | `5/6`, `13/15` (Π163, Π167). Survivors: B174, B185 |
| a rotation of the theta correlation by a unit | reads the layers `m≥2` only (Π178). Survivor: independent ramified data for `m=0,1` (A148) |
| the index of a union as the sum of the indices | glued windows: one or two bound states by the susceptibility product (Σ178). Survivor: the susceptibility criterion (B189) |
| a mean square containing the principal twists; positive weights | the half-plane itself [F] |
| bounded and Wiener constituents | none (Γ224) |
| sections, towers, own combs, paths | identities; RH at every parameter (Σ169, Γ217) |
| regulators | the count of the limit (Σ150, Γ222). Survivor: a realization with one negative square (B171) |
| certificates other than `Λ` | converge to `Λ` (Σ160) |
| linear statistics under projection | Γ223. Survivor: B172 |
| replication by normal families | Γ228. Survivors: transport, currents (B89, B145) |
| amplification over the moment order | sup bounds (Γ220) |
| bilinear statements as parity-sensitive | sign-blind (Π46); AAL is Liouville-invariant [D] |
| mean values below the height as detectors of single zeros | finite relocation invisible [KR]; `θ<½` proved (Π161) |
| short-interval mean squares of `λχ` as a source of half power | none [F] (Π180) |
| positivity alone at 70% | cost `>13/10` (Π166). Survivor: B150 |
| the return transfer | RH under a strip (Π148) |
| families by averaging | fixed part (Π145). Survivor: a family used through its rightmost zero (Π159) |
| a verified height through the double-exponential rate | `C` not explicit (Σ171). Survivors: A2, A3, A142 |
| a transitive Galois action on the zeros; a second real symmetry of the prime translations | none (Γ240, Γ243). Survivor: orbits inside `{±δ}` (B190) |
| the reflection argument against Laplace zeros of the critical state | gains nothing on the imaginary axis (Σ181). Survivor: B104 |
| Markov, Perron, size-only payment, floor tower, universal multipliers, fixed theta heads, positive Laplace mixtures, KMS, internal modular conjugation, bounded-height Diophantine certificates | as recorded [KR] |

## Bridges

| Bridge | Anchor |
|---|---|
| one inequality per prime: Weil test = count on a prime ray = upper side = copositive prime plane | SOSZ [L*] |
| one matrix at finite scale: Weil's form on step packets = product of the charges + neutral part; neutral index = right zeros + 1 | AGZ [L*] |
| bound states glue through the charges: index one ⇔ susceptibility product `≥1` | AGZ [L*] |
| Morse index of the aperture path = Lagrangian intersection number | AGZ [L*] |
| a failure of RH = one critical half-line state | AHD [L*] |
| one scale: saving, rung, depth, mollifier, level, signal, twist exponent, tail growth, critical-comb growth, rate | SA, FCT, AGZ, BHR [L*]; [D] |
| the width and the Li coefficients on one sequence: the comb | AGZ [L*] |
| half-plane route = two estimates for one completed sum; correction = Grössencharacter `L`-function at `6s−3`; zero transfer `ρ↦6ρ−3`; every period has fixed point `≥3/5` | FCT [L*] |
| root number of a row = `G(u)γ₂(u)²`; theta-square series = `ζ_K(3w−1)` × squarefree sum | CRF, STCC [L*] |
| AAL = unit gap = no accelerating filter | FFA, BHR [L*]/[F] |
| B13 ⇔ packet index `0` or `∞` | ACS [L*] |
| the door of world I: the reflection up to a decaying error, or a count below half the layer | WZC, EFT, APD [L*]; [D] |
| a fake zero = the image of the pole under `s↦s+1−ρ₀`; the zeros of ζ become poles of the model | WZC [card]/[doc] |
| the FE with a decaying defect = the rational primes among edits; with an `L¹`/`L²` defect among countable systems | EFT, WZC [L*] |
| a count rate = nothing about the zeros above half the layer | WZC [L*] |
| window sign ⇐ verification at `exp(exp(Ca))`; isolated zero ⇒ negative window on the rung `κ>1/(2δ)` | VHR, SA [L*] |
| quotients and powers of `L`-functions: index = zeros and poles off the line | AGZ [L*] |
| the zero field: `K=L` ⇔ `H=B` ⇔ `K_even⊆ℝ` ⇔ RH | GaloisTheoryOfZeros [L*] |
| twisted moments below the square root ⇒ a positive proportion on the line | MZF [L*] |
| logarithmic correlations of `λ` = prime dilates with a kernel bounded off the major arcs | LogarithmicChowla [L*] |

## Strength of the open walls

- **RH:** Σ1, Σ6 (all ranks), Σ20, Σ49, Σ56, Σ66, Σ73–Σ80, Σ113, Σ129, the minimal face, Σ150 (sign), Σ153, Σ154/Σ165/Σ166, Σ155, Σ160, Σ164, Σ168, Σ173 (every `a`), Σ175 (no crossing), Σ176 (every window), Σ181 (existence), Π2, Π42, Π126, Π127, Γ1, Γ24, Γ62, Γ95, Γ121, Γ122, Γ154, Γ195, Γ203, Γ208, Γ214, Γ222, Γ240, Γ243, Γ244.
- **≥qRH** (open below `7/8`): Σ4, Σ28, Σ162, Σ173 (one `a>1/8`), ZAL, Π3, Π159/Π162 (B161), Π163 (B174), Π167/Π175 (B185), Γ206, Γ226 (a rate `δ>1/16`).
- **AAL:** Π114, Σ147, Γ220, Π149.
- **sub:** Σ27, Σ82, Σ116, Σ117, Σ171, Σ174 (A146), Σ178 at each ratio (B189), Π7, Π22, Π51, Π53, Π54, Π65, Π80, Π94, Π161, Π169, Π171, Π172, Π180, Γ68, Γ182, Γ184, B13.
- **method / producer / indep.:** Σ135, Σ139, Σ177, Σ180, Σ181 (B104), Σ163 (B156), Σ178 (B189), Π158 (B180), Π174, Π177 (B187), Γ219 (B157), Γ222 (B171), Γ223 (B172), Γ226 (B178, B188), Γ231 (B183), Γ234 (a norm for ξ), Γ239, Γ242 (B191), Γ243 (B190).
- **just work:** Π179 (A118), Π178 (A148), Π180 (A147), Γ233 (A154), Σ171 (A142), Γ15 on the card (A153).
