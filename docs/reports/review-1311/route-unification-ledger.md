# Route unification ledger — status quo

The 38 live formulations and 12 candidates are faces of three core problems: **U-Σ** (sign), **U-Π** (precision and production) and **U-Γ** (selection, reflection and position). Their RH-level endpoints meet in one object with five exact forms, on one scale, at one door.

- **One inequality per prime.** `P(p)≤A(p)+K` on the primes of sparse logarithmic windows, off power-thin exceptions; equivalently the upper side, counts on the surviving rays, copositive prime planes; for two fixed primes a bound at their difference lags on windows of radius `r√T` [L*].
- **One matrix at finite scale.** The step-packet matrix of every window is the product of its two charges plus a neutral part; the neutral part is a potential plus the Dirichlet form of a graph whose weights are the jets and the floor-map contacts `Λ(k)/k`. RH ⇔ on every window two disjointly supported nonnegative packets, one of negative energy, satisfy `N(x,x)N(y,y)≤N(x,y)²` ⇔ every bound state has one sign [L*].
- **One binding.** A window of ratio three or four holds one bound state only through the true contacts of 2 and 3: weakened or Liouville-twisted contacts leave two. The coupling of the two halves of a window has rank proportional to the block size: one pair of charges glues them only at block size one, and no model of bounded rank does at large block size [L*].
- **One path.** The index of the restricted Weil form at an aperture is the number of crossings below it; the crossing multiplicity is a Lagrangian intersection number; the supremum is the number of right zeros; RH ⇔ no crossing [L*].
- **One cover.** The zeros of the heat family form a cover of the time plane. Over forward times it is tame: no zero escapes, branch times are finite on boxes, transport is a bijection. Every forward branch time acts by a nontrivial monodromy, the reflection of its Hermite sheets; a central one carries some zero `z≠0` to `−z`, so the group is not trivial. Complex conjugation of the zeros over a positive real time is a monodromy of this cover; RH ⇔ it is the identity ⇔ no branch time is real and positive; RH holds if every monodromy preserves every pair [L*].
- **One scale.** Saving `γ`, rung `κ`, depth `δ`, mollifier `θ`, level `σ`, signal exponent `b`, twist exponent, critical-comb growth, relaxation rate: one number [L*]; [D]. `b=7/8` is `[X]`; the open part is `½<b<7/8`.

Transversal to the three cores:
- **Two worlds.** A failure of RH is world I (a finite isolated top layer) or world II (a tail), with top `≤7/8` [X]; RH ⇔ ZAL ∧ B13 ∧ Landing [L*].
- **One critical object.** A failure of RH is a critical half-line state at a finite critical ratio: unique up to sign, outer, cyclic, without Laplace zeros in the closed right half-plane, stable along its energy branch [L*]. On the cover it is a positive real branch time; on a window it is a second bound state, which changes sign [L*].
- **One producer, with an end.** A completed sum over the twists of ζ over `ℚ(ζ₃)` gives `Re s>7/8` [X]. Its estimates reach `2/3` with square-root cancellation; its frame is a coupled tower with fixed point `3/5`, and `(4r−1)/(6r−1)≥3/5` at every period `6r` [L*]; [D].
- **One door.** Among countable systems with unit multiplicities, a functional-equation defect decaying at any rate forces the rational primes. Among positive real weights the defect can grow arbitrarily slowly with prescribed off-line zeros. A fake edit of the rational primes has defect energy `≥cT log T`, and an odd fake zero needs a count exponent of at least half its real part [L*].

**The common input [D].** The small primes are where the three cores meet. U-Σ: the contacts of 2 and 3 are the binding of every window of ratio three and four, and the first open sign is there. U-Π: the producer is a sum of cubic and sextic Gauss sums over `ℚ(ζ₃)`, whose wall is a Grössencharacter `L`-function at `6s−3`. U-Γ: the door of world I is unit multiplicity at every prime together with the reflection, and the least deleted prime sets the constant of the defect energy. In receiver form two primes suffice (two-prime lags, two heat grids at `log 2` and `log 3`); in producer form the binding needs rank proportional to the block size. Sampling is cheap, binding is not.

**Why there are three cores [D].** No test is compact on both sides of the explicit formula. A compact prime side (U-Σ) leaves infinitely many zero modes and only an exact sign decides. A localized zero side (U-Π) lets a crude bound decide and leaves the prime side at square-root precision. U-Γ is the involution `ρ↦1−ρ̄`, the selection of ζ among systems with its local structures, and the position of its zeros. The scale interpolates between the first two; the two involutions of the zeros, reflection and conjugation, are monodromies of one cover.

Corpus checkpoint: `fdc9cfc40f` (2026-11-13), working-tree sources included; fact log `logs/review-1311-status-quo-facts.md` (cited as "log §n"). Evidence: `[L*]` Lean statement read at the declaration and recorded in the fact log; `[doc]` module docstring; `[F]`, `[KR]` stated by the frontier map and the scoped-obstruction ledger at the checkpoint; `[S]` unfinished per the frontier map; `[D]` deduction; `[C]` classical; `[A]` assessment; `[X]` the half-plane `Θ≤7/8`, taken as proved; in the Lean source a statement without hypotheses (`riemannZeta_ne_zero_of_seven_eighths_lt_re`, `riemannZeta_zero_mem_quasiRH_strip`; statements and final assembly read, log §4.14), graded `[S]` by the frontier map: validation of its dependency chain is just work (A118); its consequences on receivers are `[D]`. Locators: [frontier map](../rh-current-frontier-map.md), [scoped obstructions](../rh-killed-routes.md), [walls](walls-ledger.md), [routes](route-obstacles.md), [summary](obstacles-summary.md).

**Equivalence through RH transfers truth, not mechanism.** Only an explicit source identity or a proved transport carries an estimate from one route to another. Section 3 separates the two.

## 0. Unifying statements

- **One inequality per prime [L*].** RH ⇔ the floor, the upper side, the counts or the copositivity of the prime planes on the primes of late logarithmic windows; `Θ<1` ⇔ a power floor; two primes at radius `r√T` (log §4.8, §4.9, §4.12).
- **One resolution [L*]/[F].** Prescribed sublogarithmic windows do not bound the class; finite layers are resolved by floors at every length; one-sided floors of one length have models.
- **One matrix [L*].** RH ⇔ the Hodge inequality on positive packets without common blocks ⇔ one-sign bound states; the supremal neutral index is one plus the number of right zeros; certified: one bound state for `50J≤53R`, none for `16J≤R`, the first blocks of ratio four (log §4.1, §4.7, §4.9).
- **One binding [L*].** Rank-one gluing of the halves of ratio four iff block size one; lowered index `≥2` for every rank-`r` model with `600(r+1)≤H`; two bound states with weakened or twisted contacts (log §4.1).
- **One regime change [doc]; [D].** The neutral window has negative off-diagonal entries, so its negative is a Metzler form. Narrow windows are its stability regime (no bound state); windows of ratio `≥2` are its hyperbolic regime (one bound state ⇔ a trickle-down inequality). At small widths the hyperbolic regime holds for every sign twin; selectivity starts at ratio three.
- **One index [L*].** Index law in the aperture and in the energy; crossing multiplicity = Lagrangian intersection number; below the polar ground energy every crossing is charged.
- **One index for number rings [L*].** Zeta functions of abelian number rings, quotients of configurations and their powers: the index counts zeros and poles off the line. Every Artin Euler product is a product of integer powers of abelian Euler products; reciprocity holds for cyclotomic characters; the general reciprocity law is absent.
- **One selection [L*].** Constant, weights and contacts are forced; feasible systems converge to `Λ`.
- **One scale [L*]; [D].** Saving = isolated depth = `1/(2κ)` = `1/(2θ)`; signal exponent = abscissa; critical-comb growth = width; rate `δ` ⇔ strip `1−2δ`; sizes to rung `1−o(1)`.
- **Two worlds, three atoms [L*].** `Θ<1⇔Θ∞<1`; RH ⇔ ZAL ∧ B13 ∧ Landing; B13 ⇔ packet index `0` or `∞`; AAL ⇔ at most one or infinitely many zeros right of every line.
- **One freedom [L*].** Over the rational primes with multiplicities `0,1,2` and a count rate: a non-real pair alone, any finite layer, zeros on and rising to a line, sparse configurations, quartets symmetric in a strip, a layer of ζ removed. With positive real weights: prescribed off-line zeros with a defect below any unbounded function.
- **One rigidity [L*].** Unit multiplicities with a defect `O((1+|t|)^{−a})`, `a>0`, are the rational primes; real-weighted fakes on the integers have an Abel floor; a fake edit has defect energy `≥cT log T`; an odd zero of an edit exponential needs a count exponent of at least half its real part.
- **One count for every regulator [L*]/[F].** A Green–Weil floor gives RH; the tower quotient has a unit gap iff RH; a contact altered and paid at its price is RH at every parameter.
- **One critical curve, one critical state [L*].** RH, or `R_polar<W₀`, or `R_polar=W₀` with polar-orthogonal states; the energy branch is attained, unique, strictly concave; the critical state is outer and cyclic.
- **One cover [L*].** Branch times; Hermite sheets at collisions; transport over forward times; the forward monodromy group commuting with `z↦−z`; the turn around a branch time as a nontrivial element, exchanging some `z≠0` with `−z` at a centre time; transport by homotopy class; conjugation as a monodromy; RH ⇔ no positive real branch time; a pair-preserving group ⇒ RH.
- **One horizon [L*].** RH ⇔ the quarter ringdown rate; pulse rate = horocycle rate; Weyl order; `λ₁≥3/16` on congruence groups, attained by the theta function in weight `½`.
- **One source [X]; [L*]; [D].** Two estimates give `Re s>7/8`; the class ends at `2/3` (estimates) and at `(4r−1)/(6r−1)≥3/5` (frame, every period).
- **One field [L*].** The centred zeros generate a field normal over the field of complete-fibre traces; `K_even⊆ℝ` ⇔ reflection field = prime trace field ⇔ RH; the Jensen equations have the full signed-permutation group or their moments are dependent.
- **Law and point [D].** One pointwise theorem past Vinogradov–Korobov (`7/8`, [X]); everything else on the zeros of ξ is in law: positive proportions, runs of five simple zeros, logarithmic Chowla, short-interval mean squares, bounded inner field.
- **One dominance [L*].** The Goss Riemann hypothesis: simple zeros of strictly decreasing norms.

## 1. Faces of the one object

| Reading | Statement | Anchor |
|---|---|---|
| local prime count with exceptions | `P(p)≤A(p)+K` off `Ce^{δT}` primes | SOSZ [L*] |
| upper side | `2Re S(log p)≤K` | SOSZ [L*] |
| counts on prime rays | effective counts on logarithmic windows | SOSZ [L*] |
| two primes | a floor at the lags `k log p+l log q` within `r√T` | SOSZ [L*] |
| prime planes | copositive | SOSZ [L*] |
| positive packets | the Hodge inequality `N(x,x)N(y,y)≤N(x,y)²` without common blocks | AGZ [L*] |
| bound states | every bound state of every window has one sign | AGZ [L*] |
| ratio windows | a positive mass floor on each ratio | HFP [L*] |
| critical comb | subpolynomial growth; absolute Abel integrability | AGZ [L*] |
| feasible weights | some system Weil-positive at every aperture | ASRP [L*] |
| aperture path | no crossing | AGZ [L*] |
| critical state | no critical half-line state at a finite ratio; `polarPaymentCriticalThreshold=⊤` | AHD [L*] |
| objects of a failure | no odd bound state, no defective hard-edge block, no negative definite Markov plane, `Re ξ′/ξ≥0` right of the line | RHTower [L*] |
| heat cover | no positive real branch time; conjugation monodromy trivial | GaloisTheoryOfZeros [L*] |
| heat family | every zero of every `H_t`, `t>0`, simple | RHTower [L*] |
| Jensen | `N_d=0` at every degree | GaloisTheoryOfZeros, FFP [L*]/[F] |
| tower quotient | a unit gap | FFA [L*] |
| level one | the dressed aggregate positive at level one above some prime | RHTower [L*] |
| signal | `≪Z^{b′}` for every `b′>½` | FCT [L*] |
| three atoms | ZAL ∧ B13 ∧ Landing | ELT, ZCG [L*] |
| margin | `bestMargin→0` on the window cone | CHT [L*] |
| Li / Cayley | ladder sign; Laguerre tails of the comb | ALG [doc]; AGZ [L*] |
| compactness | the orbit of translates relatively compact | AIF [L*] |
| zero field | reflection field = prime trace field; `K_even⊆ℝ` | GaloisTheoryOfZeros [L*] |
| ringdown, horocycle | the quarter rate | BHR [L*] |
| tensor | sublinear tensor exponent | AWT [L*] |
| windows, canonical flow, thresholds, flow, classical counts, BSY, recurrence | as in the frontier map | [F] |

## 2. Axes

### 2.1 Scale axis of the minimal face
| Window radius at `T` | Decides | Anchor |
|---|---|---|
| `32 log(T+2)` off `Ce^{δT}` primes | RH; width; upper side; counts | SOSZ [L*] |
| `r√T`, two primes, all difference lags | RH | SOSZ [L*] |
| prescribed sublogarithmic radii | nothing at the level of configurations | SOSZ, ZCG [L*] |
| every bounded length `(k+1)π/67` | AAL | SOSZ [L*] |
| one length, one-sided | nothing: models | FFA [F] |

### 2.2 Ratio axis of the finite-scale matrix
| Window | What holds | Anchor |
|---|---|---|
| ratio `<2` | no contact: the weights are invisible | HFP, CWS [L*] |
| narrow, `16J≤R` | no bound state; positive definite; potential above one | AGZ [L*] |
| `4J≤R` | a ground vector of the block matrix has one sign and is charged | AGZ [L*] |
| `R≤J`, `50J≤53R`, every block size | exactly one bound state | AGZ [L*] |
| ratio three, `J≥2R` | two bound states if the contact of 2 has weight in `[−4,0]`, or under the Liouville twist; with the true weight open (B192) | AGZ [L*] |
| ratio four, `J≥3R` | two bound states if the contacts of 2 and 3 have weights in `[−5/2,19/40]`; first blocks certified with margin `1/20`; at most `300000` negative squares at every block size; with the true weights open (B192) | AGZ [L*] |
| the halves of ratio four | glue through one pair of charges iff `R=1`; rank two at `R=2`; rank `r` fails for `600(r+1)≤H` | AGZ [L*] |
| every ratio, every block size | one bound state is RH (B152) | AGZ [L*] |
| tails | critical comb growth = width; Laguerre tails = Li coefficients | AGZ [L*] |

### 2.3 Aperture axis
| Aperture | What holds | Anchor |
|---|---|---|
| `2a<log 2` | feasibility independent of the weights | SA [L*] |
| a short aperture | a single simple null mode | AGZ [L*] |
| every aperture | index = Σ nullities below = number of crossings; RH ⇔ every crossing number is zero | AGZ [L*] |
| the trivial aperture `log log q+o(1)` | aligned systems and the Liouville twist fail beyond it | SA [L*] |
| verified height `exp(exp(Ca))` | sign on `[−a,a]` | VHR [L*] |
| the critical ratio `W₀` | the critical half-line state | AHD [L*] |

### 2.4 The scale
| Level | Sign side | Mean values | Level / signal / tail / rate | Anchor |
|---|---|---|---|---|
| rung `κ<1` | dominated systems positive | `θ<½`; a positive proportion | — | SA, MZF [L*] |
| rung `1+o(1)` | aligned systems fail | the square root | trivial level | SA [L*] |
| rung `κ>1` | a saving `γ<1/(2κ)`; exceptional heights of power-small measure | one bounded moment at `θ=κ` confines depth to `<1/(2θ)+ε` | `b=½+1/(2κ)`; comb growth `b−½`; rate `(1−b)/2` | SA, AGZ, BHR [L*]; [D] |
| `b=7/8` | rung `κ<4/3` | — | comb growth `≤3/8`; rate `1/16`; returns `y^{1/8}` | [X]; [D] |
| `b∈[2/3,7/8)` | — | — | the producer's room: row count, long columns | FCT, CRF [L*]; [D] |
| `b∈[3/5,2/3)` | — | — | the frame, with estimates beyond square root | FCT [L*]; [D] |
| `b<3/5` | — | — | no source in the corpus; excluded for every `6r`-periodic Gauss pairing | FCT [L*]; [D] |
| every `κ` | RH | cofinal Möbius moment | level one; quarter rate | [L*]/[F] |

### 2.5 The exceptional coordinate
| Level | Statement | Status |
|---|---|---|
| quasi-RH | `Θ<1⇔Θ∞<1` | `[X]`; equivalence [L*] |
| ZAL | `Θ∞=½` | ≥qRH; open |
| Landing | ZAL ⇒ finitely many off-line zeros | sub; open; under it RH ⇔ approach ∧ B13 [L*] |
| B13 | finitely many off-line ⇒ none ⇔ packet index `0` or `∞` | sub; open |
| AAL | at most one or infinitely many zeros right of every line | sub; open; receivers: shell signs, non-attainment, unit gap [L*]/[F] |
| B56 | `Θ<1⇒Θ=½` | RH with `[X]` |
| the count axis | fakes at every exponent above `½`; an odd fake zero needs a count exponent of at least half its real part; balanced or real top at `β≤½` | [L*]; below `√x` open (B183) |
| the FE axis, unit multiplicities | decay at any rate ⇒ the rational primes; fake edits `≥cT log T`; `T^{1+ε}` under `Θ<1` for `½<β₀<3/2−Θ` | [L*]; bounded defects and the gap open (B191) |
| the FE axis, positive weights | arbitrarily slow defects with off-line zeros | [L*] |
| the door | unit multiplicities with the reflection up to a decaying error, or a count below half the layer | [L*]; [D] |

### 2.6 The time axis of the heat cover
| Time | What holds | Anchor |
|---|---|---|
| negative real | infinitely many nonreal zeros | GaloisTheoryOfZeros [doc] |
| `0` (ζ) | real branch times accumulate, or infinitely many nonreal zeros escape across `0` | GaloisTheoryOfZeros [L*] |
| positive real | finitely many nonreal zeros; RH ⇔ no branch time here; conjugation is a forward monodromy at non-branch times | GaloisTheoryOfZeros [L*] |
| `1/8` | all zeros real | GaloisTheoryOfZeros [L*] |
| forward, nonreal | the central branch times: infinitely many, none real; the turn around one carries a zero `z` to `−z`: the reflection of the functional equation | GaloisTheoryOfZeros [L*] |
| forward boxes | far zeros simple; finitely many branch times; no escape; bijective transport | GaloisTheoryOfZeros [L*] |

### 2.7 Conversions from law to point
| Conversion | Where it is a theorem | Over ℤ for ξ |
|---|---|---|
| sign of a form | Weil for curves [C] | U-Σ; no producer |
| gluing of pieces | one bound state ⇔ susceptibility product `≥1` [L*] | fails at rank one beyond block size one; the binding has full rank [L*] |
| trickle-down | Metzler forms: local hyperbolicity ⇒ global [doc] | the links of an actual window with the true contacts: open (B192) |
| integrality gap | Stepanov [C] | `p^{11/12}` at one prime [F] |
| unit gap | index-one limits [F] | no approximant with a gap [F] |
| budget overflow | long mollifiers [L*] | needs length past the height |
| power sums in cameras | adaptive clusters [L*] | in law; pointwise prime cost open |
| a bounded-below height | Néron–Tate [C] | sections count linearly [L*] |
| a family with monodromy | Deligne [C] | fixed part [F]; the heat cover has a nontrivial monodromy group containing conjugation and an element exchanging some `z≠0` with `−z`; pair-preserving ⇒ RH; no restriction on the group is proved [L*]; triviality of the group refuted [KR] |
| ultrametric dominance | Goss [L*] | no norm for ξ [F] |
| the FE with the Euler product | rigidity at any decay among unit multiplicities [L*] | identifies ζ; says nothing about the zeros of ζ |
| the rightmost zero of a family against its twists | `Re s>7/8` [X] | reach `2/3`, frame `≥3/5` at every period [L*]; [D] |
| compactness at the critical ratio | a unique outer cyclic critical state [L*] | its charge open (B104) |
| Kloosterman sums with Weil's bound | `λ₁≥3/16` [L*] | sharp in weight `½`; no rate for the resonances |

### 2.8 The curve proof and its ℤ-counterparts
| Ingredient over `𝔽_q` | ℤ-counterpart | Status over ℤ |
|---|---|---|
| finite rank; periodic zeros | ZAL or an attained top | open |
| Stepanov | `P(p)≤A(p)+K` on logarithmic windows | open (B130) |
| `C×C`, Néron–Severi, Hodge index | the neutral part of every window; the Hodge inequality on positive packets | certified at ratio `≤103/50` and on narrow windows; open (B152) |
| the intersection number of two effective divisors without common components is `≥0` | the off-diagonal entries of the neutral part are negative: two packets without common blocks attract | theorem [L*] |
| induction on the pieces of a surface | gluing of windows | the law is a theorem; through finitely many charges it fails [L*] |
| Hodge index as a topological count | Morse index of the aperture path as a Lagrangian intersection count | closed as an identity |
| genus, Riemann–Hurwitz | number rings; quotients and powers | theorem [L*] |
| point counts over `𝔽_{q^m}` | the contacts of a number ring are its point counts over the finite fields | theorem [L*] |
| characters; Artin `L`-functions | Brauer induction; abelian product form; cyclotomic reciprocity | theorem [L*]; general reciprocity absent (A154) |
| count law | counts on prime rays | hyperelliptic [F]; over ℤ ⇔ RH [L*] |
| deformation | price paths; the heat cover | RH at every parameter [L*]; RH ⇔ no positive real branch time [L*] |
| Weil's bound feeding parity | the cube identity with sieves | `[X]`; class end `2/3`, frame `≥3/5` |
| the zeta function as a polynomial | the critical comb | growth = width [L*] |
| Frobenius acting on the roots | the forward monodromy group acting on the zeros of `H_τ` | a group containing conjugation and, from every centre time, an element exchanging some `z≠0` with `−z` [L*]; exchanges, generators, transitivity open (B193) |

### 2.9 Off the scale
| Kind | Receiver | Kill | Anchor |
|---|---|---|---|
| homogeneous floor | energy floor ⇒ RH | clock below the form | FFA [L*]/[F] |
| unit gap | index-one ⇒ RH | tower quotient: unit gap iff RH | FFA [L*] |
| certificate | feasible weights ⇒ RH | converge to `Λ` | FFA [L*] |
| symmetrization | a decreasing functional | a concave gradient symbol is forced | FFA [L*] |
| replication | bounded normalization ⇒ AAL | zero limits | FFA [L*] |
| the count as a power | — | fakes at every exponent above `½` | SPAL, WZC [L*] |
| the FE as a growth bound | decay ⇒ the primes among unit multiplicities | slow defects among positive weights; bounded defect among signed weights | EFT [L*] |
| prime edits with a count rate | — | floor `≥13/30` | WZC [L*] |
| a fixed number of charges | the gluing law | rank law of the binding | AGZ [L*] |
| sizes of the contacts | — | weakened contacts: two bound states | AGZ [L*] |

## 3. Which routes are the same problem

### 3.1 Same problem by source identity or proved transport
| Family | Routes | Identity | Anchor |
|---|---|---|---|
| **Prime-degree inequality** | ACS, SRT, WL (prime windows), HF and RW through the two-bumps, ZCG (sampling), HAT-C, PM (count) | one number per prime on logarithmic windows; two primes at radius `r√T` | SOSZ [L*] |
| **Finite-scale matrix** | ACS, HF, HAT-C, LI (tails), RW (feasible weights) | Weil's form on step packets = charges + potential + Dirichlet form; Hodge inequality ⇔ RH | AGZ, HFP [L*] |
| **Binding** | ACS, HF, RW | one bound state of a union through the contacts between its parts | AGZ [L*] |
| **Aperture path** | RW, EWU, OWU, ACT, CHMD, SZ, RN, AIP, HF, SRT, SC | index = Σ nullities = crossings; polar shadow | AGZ [L*] |
| **The scale** | RW, EWU, OWU, ACT, HF, ACS, SRT (rungs); MC, WL, BAG (savings); WD (mollifier); JAS (level, signal); ACS (critical comb); PM (rates); S3 (returns) | one number | SA, FCT, AGZ, BHR [L*]; [D] |
| **Regulators** | HAT-C, PM, W1C | the count of the limit | HAT, FFA [L*]/[F] |
| **Critical curve and critical state** | HF, SRT, AIP, ACS (atomic), SC | three-way classification; one extremal function | AHD [L*] |
| **Exceptional coordinate** | ZCG, BAG, JAS (shell), SC (undamped), WL (thick runs), LA (finite support), PM (filtered rates) | two worlds; atoms; the door | ELT, ZCG, FFA, WZC, EFT [L*]/[F] |
| **Lag and flow** | WL, ACS (flow), SC | prime lag Gram matrices positive semidefinite ⇔ RH | [F] |
| **Mertens level** | MC, SQF, WL, PBM, RB, CTF, FU, CFC, RP | rate ⇔ level; the signal | AAD, FCT [L*] |
| **Horizon** | PM with BHR, ASH, CTH, AHMH | one scattering matrix; rates | [L*]/[F] |
| **Heat cover** | ZCG (heat), LA, PTR, HCF | branch times; Jensen quartets; conjugation monodromy | GaloisTheoryOfZeros [L*] |
| **Constituents and index** | W1C, PTR, PM, LA | no bounded constituent; semicontinuity | CTZ, IRP, FFA [F] |
| **Tensor and family** | ECP, ACS (tensor), HF (covers) | fixed part; index per character | AWT [L*]/[F]; AGZ [L*] |
| **Half-plane legs** | JAS, MC, S3, WD (depth), ACS (tails), PM (rate) | each is `Θ≤b`; one producer with an end | FCT, SA, AGZ, BHR [L*] |
| **Zero field** | LA, ZCG | reflection field = trace field ⇔ RH | GaloisTheoryOfZeros [L*] |
| Aliases | HJ→PA; BSY of FEL→CTF | definitions | frontier |

### 3.2 Same endpoint, distinct mechanism
| Group | Routes | Common form only |
|---|---|---|
| scheduled sums | FU, CFC, RP, LI | one-sided history floors |
| finite-degree detectors | PA, HCF, TH, LA, GTA, XN, TG | a sign or a bound at every degree |
| source completions | SEC, CDC/BSH, APF, EWJ, RFHM, WBF | a source plus one condition at each zero |
| dark-range inputs | B46, B57, B97, B121, B137, B145, B159 | prime sums below the Vinogradov length |
| world-I inputs | B13, B138, B141, B145, B128, B170, B183, B191 | a statement using unit multiplicities with the reflection, or the exact count |
| producers of RH strength | B87, B146, B149, B169, B114, B117, B171, B160, B152 | a positive, index-one or level-one statement built without the zeros |
| producers of a half-plane | `[X]`; B161 via B174, B185; B187; B178, B188 | two estimates for one completed sum; a rate from the horizon |
| method questions on the Σ core | B104, B192 | the charge of the critical state; the first selective sign |
| method questions on the Γ core | B190, B191, B193 | orbits of zeros; bounded defects; the forward monodromy group |

### 3.3 Classes

**Σ-classes.**
| Class | Observable | Routes | Identity or receiver |
|---|---|---|---|
| C1 window form | `W≥0` on every window | RW, EWU, OWU, ACT, AIP, HF, SRT, ACS | window ⇔ threshold ⇔ sectors [F] |
| C2 canonical flow | `r, q, Ψ` | RW, SZ | `Ψ` bounded on precontact portions ⇔ RH [F] |
| C3 critical compactness | thresholds, pole channel, the critical half-line state | HF, SRT, AIP, SC | classification; energy branch; outer, cyclic, stable [L*] |
| C4 continuation | Laguerre, collisions, Jensen | PTR, ZCG, LA, HCF, PA | receivers |
| C5 scheduled sums | history floors | FU, CFC, RP, LI | receivers |
| C6 theta moments | ranks, heads | TH | rank 14 [L*] |
| C7 regulated energies | clock, tower | HAT-C | floor ⇒ RH [L*] |
| C8 verified-height rungs | windows, ranks, degrees | RW, TH, LA, LI, PA, HCF, SRT | double-exponential rate [L*] |
| C28 finite-scale matrix | step packets, neutral part | ACS, HF, LI | Hodge inequality ⇔ RH; certified ranges [L*] |
| C31 the scale (rungs) | sign at a rung | RW, HF, ACS, SRT, EWU, OWU | sizes; exchange rate [L*] |
| C32 dressed positivity | the level | JAS | level one ⇔ RH [L*] |
| C34 index in the aperture | crossings; polar Lagrangian | RW, HF, ACS | Morse = Maslov [L*] |
| C37 tails of the comb | critical comb; power tails; Laguerre tails | ACS, LI | growth = width; Li coefficients [L*] |
| C39 gluing of windows | susceptibilities; brackets; response matrices | ACS, HF, RW | law [L*]; rank one only at block size one [L*] |
| C41 selective binding | the contacts of 2 and 3; the half-constant plane | ACS, HF, RW | weakened contacts ⇒ two bound states [L*]; the true contacts open |
| C42 Metzler regimes | stability and hyperbolic regimes; trickle-down | ACS, HF, LI | dichotomy [doc]; twist-blind at small widths |

**Π-classes.**
| Class | Observable | Routes | Identity or receiver |
|---|---|---|---|
| C9 prime-degree sampling | decisive samples | ACS, SRT, WL, ZCG | logarithmic windows; two primes [L*] |
| C10 one-point precision | `ψ`, `M`, squarefree count | WL, MC, SQF, PBM, RB, JAS, CTF | classical criteria |
| C11 production | stencils | WL, MC | rate = Mertens level [L*] |
| C12 long moments, census, cameras, short intervals, correlations | moments; runs of simple zeros; adaptive clusters; mean squares of `λ`; logarithmic Chowla | WD, CTF, ZCG, MC | in law [L*] |
| C13 returns | heavy returns; resonators | BAG, TH, SRT; S3 | `y^{1/8}` [X]; transfer = RH [F] |
| C14 exactness | Frobenius at one prime; sections | ACS, BAG | priced; identities |
| C15 families | towers | ECP, ACS | fixed part |
| C16 orientation cover | centred count | MC | `M(N)` [F] |
| C33 sources | signal, completed sums, Gauss sums, budget, corrections, coherence, theta-square series | JAS, MC; S3 | `[X]`; frame `≥3/5` at every period; square-root endpoint `2/3`; long columns [L*]; [D] |

**Γ-classes.**
| Class | Observable | Routes | Identity or receiver |
|---|---|---|---|
| C17 two worlds and atoms | `Θ`, `Θ∞` | ZCG, BAG, JAS, SC, WL, LA | RH = ZAL ∧ B13 ∧ Landing [L*] |
| C18 finite-layer receiver | filters, currents, non-attainment, tangent data, shell signs | ZCG, BAG, SRT, JAS | complete [L*]/[F] |
| C19 rigidity | FE defects, counts | ZCG, BAG, MC | the door: unit multiplicities with a decaying defect, or a count below half the layer [L*]; [D] |
| C20 horizon | ringdown, horocycles, Weyl order, `3/16` | PM | sharp receivers; the congruence mechanism is sharp in weight `½` [L*] |
| C21 count | Tate limits; sections | ACS, HF, PM | counts on rays ⇔ RH; sections linear [L*] |
| C22 diagonal | density of the comb | HF, ACS, HAT-C | forced constant [L*] |
| C23 absolute geometry | contacts, rings, paths, quotients, characters | ACS, HF | identities; index for quotients and powers; abelian form of Artin Euler products [L*] |
| C24 index, limits, flow | index-one limits | PTR, WL, W1C | semicontinuity [F] |
| C25 separation and dominance | ordinate injectivity; Newton polygons | ZCG | Goss [L*] |
| C26 recurrence | returns, translates, compactness | BAG | zero limits; RH ⇔ compact orbit [L*] |
| C27 source completion | zero-parameter conditions | candidates | landings missing |
| C30 constituents | bounded, Wiener | W1C, PTR, PM | none with a zero [F] |
| C35 floor-free receivers | the off-scale kinds | every route | receiver and kill [L*]/[F] |
| C36 models | one-structure models; two-sided edits; signed and positive weights | every route | every finite datum realized; slow defects among positive weights [L*] |
| C38 zero field | group over the source field; prime trace and reflection fields; Jensen equations; orderings | LA, ZCG | trivial ⇔ RH; full group or dependent moments [L*] |
| C40 objects of a failure | critical state, odd bound state, defective block, Markov plane, empty aperture, sign-changing bound state, positive real branch time | every Σ route | each exists ⇔ RH fails [L*] |
| C43 monodromy of the heat cover | transport, forward monodromy, turns around branch times, conjugation | ZCG, LA | conjugation ∈ forward monodromy; trivial ⇔ RH; every forward branch time acts nontrivially; pair-preserving group ⇒ RH; transport depends only on the homotopy class [L*]; triviality of the group refuted [KR] |

C1, C2, C7, C9, C28, C31, C34, C37, C39, C41 and C42 are dictionaries of one form: C9 on prime samples, C28 on finite matrices, C39 and C41 on their unions, C42 as its two regimes, C31 graded by mass, C34 along the aperture, C37 on one sequence. C32, C33, C37 and the rates of C20 are the same scale. C10, C11, C16 are the Mertens level and C33 is its only producer class. C17–C19 with C35 and C36 are one programme on the exceptional coordinate, whose door is C19. C21–C23 and C28 are one programme on the count and the diagonal. C3 and C40 are the Σ core read from the side of a failure. C4, C38 and C43 are one programme on the zeros as a set with symmetries: a field, a cover, a group.

### 3.4 Constructive transfers and their limits
| Sources / routes | Established transfer | Input not transported |
|---|---|---|
| SOSZ → ACS, SRT, WL, HF, ZCG, PM | RH from logarithmic prime windows and from two primes [L*] | the bound |
| AGZ, HFP → ACS, HF, LI, RW | finite-scale matrix; Hodge inequality; certified ranges; refinement transfer; gluing law and brackets; rank law; weakened contacts; Morse = Maslov [L*] | the sign with the true contacts at ratio three and beyond; the charge of the first crossing |
| ALG → ACS, HF | Metzler dichotomy; trickle-down [doc] | hyperbolic links of an actual window |
| VHR → window routes | verified height ⇒ window sign at `exp(exp(Ca))`; explicit `windowHeight` [L*] | verification at every height; a height within reach |
| SA → RW, HF, ACS, WD | sizes below rung one; one exchange theorem; three rungs under a half-plane [L*] | a saving past rung one |
| FCT, CRF, STCC, MMD → JAS, MC, S3 | frame, coupled tower, barrier at every period, budget, coherence, root numbers, theta-square poles [L*]; the half-plane `7/8` stated without hypotheses in source [S] | the two estimates; the long columns; a pairing outside the class |
| [X] → every graded receiver | the level `7/8` [D] | a level below `7/8` |
| MZF, CDG, IGP → WD, ZCG | moments below the square root; positive proportion; runs of simple zeros; adaptive cameras [L*] | length past the square root; pointwise prime cost |
| MatomakiRadziwill, LogarithmicChowla → MC, WD | short-interval mean squares; logarithmic two-point Chowla [L*] | a rate; half power |
| CTZ, IRP, FFA → W1C, PTR, PM | no bounded constituent; unit gaps pass to limits [F] | an approximant with a gap |
| AHD / CACT → HF, SRT, AIP | thresholds, classification, the energy branch, structure and stability of the critical state [L*] | the polar pairing of the state |
| HAT, FFA → window routes | fixed-height floor ⇔ RH [F] | the floor |
| ELT → ZCG, BAG | filters; growing-order reduction [F] | the prime-weighted current |
| WZC, FFA, SPAL, APD, EFT → ZCG, BAG | models for every structure set short of the door; rigidity at any decay [L*] | a statement at the door that sees a layer |
| BHR, RHTower → PM | exponents read `Θ`, `Θ∞` [F]; `3/16` and its sharpness [L*] | a rate from the horizon |
| GaloisTheoryOfZeros → LA, ZCG | quartet exhaustion; zero field; heat cover with forward monodromy; local monodromies as group elements; conjugation as a monodromy; pair-preserving group ⇒ RH [L*] | a restriction forcing triviality; control at `τ→0` |
| RHTower/Artin → ACS, HF | Brauer induction; abelian product form; cyclotomic reciprocity [L*] | general reciprocity |
| SignFreePurityMechanisms → ZCG | Goss by dominance [L*] | a norm for ξ |

## 4. U-Σ — the sign

Core problem: binding. Every two positive packets without common blocks, one of negative energy, are coupled at least as strongly as the geometric mean of their energies. Equivalently: no crossing of the aperture path, `W≥0` on every window, one-sign bound states, feasible weights at every aperture, `Ψ` bounded on precontact portions, the energy floor at one fixed height, level one, subpolynomial critical comb, no critical half-line state, no positive real branch time. Each window is a finite-height statement at a height beyond reach; each ratio is a family of matrices; the binding is carried by the contacts of the small primes and has full rank; a failure is one function.

| Face | Routes / programmes | Reduction |
|---|---|---|
| complete atomic matrix; critical state | HF, SRT, AIP, SC; CACT, AHD | classification; structure of the state; B104 |
| ground energy, chain, cone, feasible sets, aperture path | RW, EWU, OWU, ACT; CSTW, CHT, AIF, SA, FFA, AGZ | crossings; certificates converge to `Λ` |
| prime two-bumps | SRT, ACS; SOSZ | logarithmic windows; two primes |
| finite-scale matrix and its binding | ACS, HF; AGZ, HFP, ALG | Hodge inequality; certified ranges; rank law; B152, B192 |
| regulated energies | HAT-C | fixed-height floor |
| dressed positivity | JAS | level one |
| moments and ladders | TH, LI, PA, HCF | all ranks, entries, degrees |
| heat, cosine, Jensen | ZCG, PTR, LA | positive real branch times; small time |
| scheduled sums, charge, gate, renewal | FU, CFC, RP, GTA, TG, RN, SZ, CHMD | floors and gates |

## 5. U-Π — precision and production

Core problem: square-root precision of one smoothed prime count; in scale form a saving of the contacts; in signal form a power saving of one smoothed Möbius sum. One producer class exists: completed sums of Gauss-sum coefficients over the twists of ζ, with a reflection, two estimates and a correction. It has produced `7/8` [X]; in the Lean source the statement carries no hypothesis; validation of its chain is work (A118) [S]. Its estimates reach `2/3` with square-root cancellation; its frame couples the target to a tower of Grössencharacter families with fixed point `3/5`, and no period of the Gauss pairings has a lower one [L*]; [D]. In law the picture is native: short-interval mean squares of `λ`, logarithmic two-point Chowla, twisted moments below the square root [L*]. None of these carries a rate at half power.

| Face | Routes / programmes | Reduction |
|---|---|---|
| prime-degree crude bounds | ACS, SRT, WL; SOSZ | B130; VK |
| classical one-sided counts | WL, MC, SQF, PBM, RB, CTF | RH-level equivalences |
| the signal and its sources | JAS, MC; FCT, MMD, CRF, STCC | `7/8` [X]; B174, B185, B187 |
| producers and auxiliaries | WL, MC; AAD, ALST, RAC | rate = Mertens level |
| long moments, census, cameras, correlations | WD, CTF, MC; CDG, APR, MZF, IGP, MatomakiRadziwill, LogarithmicChowla | `θ<½`; unbounded `θ` needed |
| returns and the dark range | BAG, TH; S3; TTPO, PTT, TAPO, ELT | VK height; transfer = RH |
| families | ECP, ACS; AWT, AK | fixed part |
| orientation cover | MC; RIAC, HAT | cover weight |

## 6. U-Γ — selection, reflection, position

Core problem: the two involutions of the zeros, reflection `ρ↦1−ρ̄` and conjugation, and the selection of ζ, used as a source of control on the position of the zeros. In world form: exclude world I (B13, Landing; non-attainment) and world II (ZAL). In model form: a statement at the door — unit multiplicities with the reflection up to a decaying error, or the count below half the layer — that sees a layer. In count form: Bézout for the comb pairing. In horizon form: a rate or a reflection sign. In Galois form: the group of width reflections is trivial. In cover form: the conjugation monodromy is trivial.

| Face | Routes / programmes | Status |
|---|---|---|
| two worlds and atoms | ZCG, BAG, JAS, SC, WL, LA; ELT, IRW, SOSZ, FFA | receivers complete |
| models, rigidity, constituents | ZCG, BAG, W1C; WZC, EFT, APD, SPAL, CTZ, IRP | selection of ζ complete among unit multiplicities at any decay; no statement at the door sees a layer (B170, B145, B191) |
| horizon and count | PM; BHR, ASH, AHMH, CTH, STCC | sharp receivers; `3/16` and its sharpness; count door |
| square, diagonal, lattice | HF, ACS, HAT-C; AGZ, HFP, HAT | identities; index for quotients and powers |
| index, limits, flow | PTR, WL, W1C; IRP, FFA | unit gaps pass to limits |
| recurrence | BAG; TAPO, AAD, FFA, AIF | zero limits at a finite layer; compactness ⇔ RH |
| zero field and heat cover | LA, ZCG; GaloisTheoryOfZeros | trivial group ⇔ RH; conjugation a monodromy; orbits and the structure of the monodromy group open (B190, B193) |

## 7. Cross-family seams

| Seam | Statement | Anchor |
|---|---|---|
| Σ ∩ Π ∩ Γ: one test per prime | the prime trace is the Weil two-bump, the count on a prime ray and the plane defect | SOSZ [L*] |
| Σ ∩ Π ∩ Γ: one matrix | Weil's form on step packets = charges + potential + Dirichlet form of jets and contacts | AGZ [L*] |
| Σ ∩ Π ∩ Γ: one scale | saving, depth, rung, mollifier, level, comb growth, rate | [L*]; [D] |
| Σ ∩ Π ∩ Γ: the small primes | contacts of 2 and 3 (binding); the sextic tower (producer); unit multiplicity and the least deleted prime (door) | AGZ, FCT, EFT [L*]; [D] |
| Σ ∩ Π: the contacts | the prime side enters the sign matrix as the weights `Λ(k)/k` on the floor maps; their true values are needed from ratio three | AGZ [L*] |
| Σ ∩ Π: the width on the comb | critical-comb growth = width; Laguerre tails = Li coefficients | AGZ [L*] |
| Σ ∩ Π: verification | window sign ⇐ `exp(exp(Ca))`; confinement up to `2πe^a` | VHR, ZCG [L*] |
| Σ ∩ Π: returns | under `Θ≤b` heavy returns need `log t≥c·y^{1−b}` | SA [L*] |
| Σ ∩ Γ: index | B13 ⇔ packet index `0` or `∞`; index = crossings = right zeros | ACS, AGZ [L*] |
| Σ ∩ Γ: a failure as one object | critical state; odd bound state; sign-changing bound state; positive real branch time | AHD, RHTower, AGZ, GaloisTheoryOfZeros [L*] |
| Σ ∩ Γ: conjugation | reality of the zeros at positive time (Σ) is the triviality of a monodromy (Γ) | GaloisTheoryOfZeros [L*] |
| Σ ∩ Γ: regulators | the count of the limit | FFA, HAT [L*]/[F] |
| Σ ∩ Γ: number rings | index of quotients and powers | AGZ [L*] |
| Π ∩ Γ: worlds on the prime side | world I attains `x^β` on every window | FFA [F] |
| Π ∩ Γ: the defect of a twin | the FE defect of a fake has the size of ζ on the line | WZC [L*] |
| Π ∩ Γ: families | the correction is an `L`-function of a second family; the zero transfer `ρ↦6ρ−3` | FCT [L*] |
| Π ∩ Γ: horizon | exponents `1−Θ/2`, `1−Θ∞/2` [F]; the theta function at `3/16` in weight `½`, the cubic theta in the producer | BHR, RHTower, STCC [L*]/[F] |
| Π ∩ Γ: the count | a count rate above the pair says nothing; edits model every layer | WZC [L*] |
| Γ ∩ Γ: two involutions | reflection = local monodromy at central collisions; conjugation = a forward monodromy; both commute with `z↦−z` | GaloisTheoryOfZeros [L*] |
| Γ ∩ Γ: affine coincidences | halving pairs; the pairs `(ρ,6ρ−3)` | [KR]; [L*] |

## 8. Route → core map

| Route | Core | Worlds / atoms | Classes | Face |
|---|---|---|---|---|
| WL | Π (Σ, Γ) | both; thick runs | C9, C10, C11, C17, C24 | prime lag; thick deviation |
| RW, EWU, OWU, ACT | Σ | both | C1, C2, C8, C31, C34, C39, C41 | `Ψ`; feasible weights; crossings |
| FU, CFC, RP | Σ | both | C5 | history floors |
| SZ | Σ | both | C1, C2 | Abel residual |
| LI | Σ (Π) | both | C5, C8, C28, C37, C42 | Cayley–Li sign; Laguerre tails |
| PA (HJ) | Σ (Π) | both | C4, C8 | Hausdorff rows |
| TH | Σ (Γ) | both | C6, C8, C13 | adaptive heads |
| HCF | Σ (Π) | both | C4, C8 | two grids |
| LA | Σ | world II side; finite support | C4, C8, C17, C38, C43 | outer roots; Jensen quartets |
| GTA, XN, TG | Σ (Π) | both | C4 | charge, discs, gate |
| MC, SQF | Π (Γ) | both | C10, C11, C12, C16, C33 | the signal; the producer's end |
| TT | Π (Σ) | both | C1, C10 | endpoint energy |
| HF | Σ (Π, Γ) | both | C1, C3, C21–C23, C28, C31, C34, C39, C40, C41 | pole channel; binding; critical state |
| HAT-C | Σ (Γ) | both | C1, C7, C22 | fixed-height floor |
| SRT, AIP | Σ (Π) | both | C1, C3, C8, C9, C18, C40 | two-bumps; critical curve |
| SC | Σ, Π (Γ) | AAL branch; ZAL | C3, C17 | damped coupling |
| CHMD | Σ | both | C1, C40 | prime wave; odd bound state |
| RN | Σ | both | C1 | energy comparison |
| WD | Π (Σ, Γ) | world II side | C12 | long moments |
| PM | Γ (Σ) | both | C20, C21, C35 | rate; Krein; count |
| JAS | Σ, Π | level one excludes every world; shell signs give AAL | C10, C17, C18, C32, C33 | level one; the signal |
| CTF | Π | both | C10, C12 | rows; BSY |
| PBM, RB | Π | both | C10 | abscissa; extremal inequality |
| BAG | Γ | AAL | C13, C17, C18, C19, C26 | returns; transport |
| ACS | Γ (Σ, Π) | both | C1, C9, C14, C15, C21–C23, C28, C31, C34, C37, C39, C41, C42 | Hodge inequality; binding; critical comb |
| ECP | Γ (Π) | both | C15 | characters |
| PTR | Σ (Γ) | both | C4, C24, C30 | cosine producers |
| ZCG | Γ (Σ) | all | C4, C9, C12, C17–C19, C25, C35, C36, C38, C40, C43 | branch times; atoms; models; the door |
| S3 | Π | strip `[X]`; transfer = RH | C13, C9, C33 | the transfer |
| SEC, CDC/BSH, APF, EWJ, RFHM, WBF | Γ (Π) | — | C27 | landing |
| EGC, FEL, MSC | Σ (Π) | — | C5, C1 | landing; history; Sonin |
| IRK | Γ (Π) | — | C21 | trace and Chern charge |
| W1C | Σ (Γ) | — | C24, C19, C30 | index-one family |

## 9. What a closing argument must supply

| Needed | Present over ℤ | Missing |
|---|---|---|
| a crude count | one inequality per prime; two primes suffice [L*] | B130 |
| the resolution | logarithmic radius; bounded windows for layers [L*] | none |
| a finite object | the neutral part of every window; certified at ratio `≤103/50` and on narrow windows [L*] | the sign at every ratio (B152) |
| an induction step | the gluing law; brackets; response matrices [L*] | a step of growing rank, or a signed comparison keeping the true contacts (B192) |
| a first selective case | weakened and twisted contacts fail at ratio three and four [L*] | the sign there with the true contacts, from the contacts (B192) |
| a topological count | Morse = Maslov; polar shadow [L*] | no crossing (RH); the charge of the first crossing (B104) |
| an object to contradict | the critical half-line state: unique, outer, cyclic, stable [L*] | its charge; a Green or boundary-trace identity (B104) |
| a half-plane | `7/8` [X], stated without hypotheses in source [S]; the class reaches `2/3`, frame `≥3/5` at every period [L*]; [D] | A118; B174; B185; B187 |
| a step to the line | level one ⇔ RH; transfer ⇔ RH [L*]/[F] | a statement off the scale or a source outside the class |
| the two worlds | receivers; models for every structure set short of the door; rigidity at any decay [L*] | a statement at the door that sees a layer (B170, B145); B183; B191 |
| a uniformity source | moments; short-interval mean squares; logarithmic Chowla; tensor criterion [L*] | none by averaging |
| a Frobenius substitute | one prime [F]; the forward monodromy group with its turns [L*] | an exchange, and a restriction on the group (B193) |
| a surface | forced data, number rings, quotients, Artin Euler products, finite-scale matrix [L*] | one property that is an inequality (B149, B169); general reciprocity (A154) |
| a deformation | paths, mass, regulators; the heat cover, tame over forward times [L*]/[F] | control at the time of ζ; a family with a sign or a gap before the limit |
| a producer | one class, ended at `2/3` and at `≥3/5` for every period | a pairing outside the class (B187); a rate from the horizon with an input that fails in weight `½` (B188) |
| a sign-free conversion | Goss dominance; the order law; the zero field; the monodromy group [L*] | a norm on the zero field; a restriction on a group (B190, B193); B145 |
| reflection | sharp receivers; rigidity; the wall as the price of completion [L*] | a use of the reflection that sees a zero |
| breadth of returns | VK height; `y^{1/8}` [X] | B97, B137, B145 |
