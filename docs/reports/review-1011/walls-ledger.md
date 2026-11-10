# Walls ledger — status quo

**Corpus checkpoint:** commit `5bebbe1136` with its working tree (2026-11-10). Working log: `logs/review-1011-frontier-facts.md`. Companions: [route-obstacles.md](route-obstacles.md), [route-unification-ledger.md](route-unification-ledger.md), [obstacles-summary.md](obstacles-summary.md).

Three wall families carry the frontier. **Σ** is the critical sign of the window form, **Π** the precision and production of the prime count, **Γ** the selection of ζ, the reflection of its zeros and their position in height. All three meet in one minimal face, local in scale and tolerant of power-thin exceptions, and in one lattice: the comb pairing of the degree points.

- **The minimal face.** RH ⇔ `P(p)≤A(p)+K` at every prime ⇔ the same at the primes of arbitrarily late logarithmic windows `|log p−T|≤32 log(T+2)`, outside at most `Ce^{δT}` primes per window (`δ<1`) [L*]. Sign-free: RH ⇔ `|c_p|≤K` on such windows [L*]. In the class `𝒵` of tempered configurations with a lowest ordinate and logarithmic local counts no shorter window decides [S]; in ζ's class `𝒵₀` (deep zeros of density zero) the resolution is open (B151).
- **Σ is the sign of every window.** RH ⇔ `W≥0` on every window ⇔ `Ψ` locally bounded ⇔ one Weil test per prime ⇔ exactly one positive square of the comb pairing on the two rulings and every finite family of packets [L*]/[S]; a window at aperture `a` follows from verification to `windowHeight(a)` [L*]; at finite scale the comb form is coercive on short windows and has finite index on every window [S]; at the critical curve `R_c=R_polar=R_halfline≤W₀` with a three-way classification [L*].
- **Π is the same sign on the prime side.** Unconditional pointwise savings are Vinogradov–Korobov; everything past it is in law. Exact methods over ℤ have exact prices: Frobenius at one prime, cost `m·θ(S)`, Chebyshev auxiliaries, the tower's Riemann–Roch, the carry class, the fixed part of every canonical family [L*]/[S].
- **Γ is the same sign on the zero side, plus position.** A failure of RH lies in world I (¬AAL) or world II (AAL ∧ ¬ZAL) [L*]/[D]; RH ⇔ ZAL ∧ B13 ∧ Landing [L*]. Weil's kernel is contacts plus jets off the diagonal; its diagonal is the density of a comb and not one glued carrier object [L*]. The off-line zeros are the zeros of no bounded Dirichlet series [L*].

[Frontier](../rh-current-frontier-map.md): **38 live formulations, 12 candidates**. [Scoped obstructions](../rh-killed-routes.md) separate failed mechanisms from open replacements.

**Status.** **Solved** (the face is a theorem), **Partially solved**, **Sharpened** (open, exact form a theorem), **Open**, **No-go** (mechanism refuted), **Classified**, **Reduced** (theorem-level equivalent named), **Settled** (a method question answered). **Strength:** RH, ≥qRH, AAL, sub, indep., identity, method, producer. **Evidence:** `[L*]` Lean statement read for this ledger; `[L]` recorded as integrated Lean in the frontier map, the scoped-obstruction ledger or a programme table of `formal/`; `[S]` source present, graded unfinished or unintegrated by the frontier map or untracked in the working tree, statement read; `[K]` Lean with transitive axiom audit as recorded; `[D]` deduction; `[C]` classical; `[A]` assessment.

Notation as in [route-obstacles.md](route-obstacles.md).

## Σ — critical sign

| Wall | Status | Strength | Content |
|---|---|---|---|
| Σ1 Weil's sign | Sharpened | RH | RH ⇔ `W≥0` on every window ⇔ `Ψ` locally bounded on precontact intervals ⇔ the pole-free functional `≥0` on odd tests ⇔ the even blind minimum `≥0` at every aperture ⇔ the variation inequality at one shift ⇔ Weil positivity of every prime two-bump ⇔ the floor on logarithmic prime windows ⇔ `E_r(f)≥−(1−r²)‖f′‖²/2` near `r=1` on every packet ⇔ one positive square of the comb pairing on packets [L*]/[S]/[D] |
| Σ1b, Σ1k Subcritical regime; one critical multiple | Solved | sub | complete tilted-spline matrix PD with floor `κ/(2c⁷)` for `1≤c≤(log N)^α`, `α<1/8` [L*], and at `c≤2K₀(log N)^{1/8}` [K] |
| Σ1c–Σ1x Critical-curve calculus | Classified | sub / method | shell–pole payment, conductor resolution, receiving charges, Γ-liminf, top-collar Gårding, alias notch, Gamma reserves [L]/[K] |
| Σ1u, Σ129 Threshold law | Solved (identities) | RH (all thresholds `=⊤`) | `R_c=R_c^{PSD}=R_polar=R_halfline≤W₀`; hierarchy `0<R_c≤R_nonneg≤R_polar≤R_high=W₀`; each `=⊤` ⇔ `a*(ζ)=⊤` ⇔ RH [L*] |
| Σ2 Edge, zero modes, hard Lefschetz | Sharpened | RH | zero modes radical and two-site; Hodge index = Li positivity [L] |
| Σ3a Coprime stratum | Sharpened | RH | `det R_N=M(N)`; RH ⇔ `χ̃=O(N^{½+δ})` [L] |
| Σ4 Finite index / heat count | Sharpened | ≥qRH; RH for index 0 | under AAL: RH ⇔ ZAL ⇔ finitely many off-line zeros ⇔ finite negative index ⇔ bounded heat counts ⇔ eventual Hadamard positivity [L*]/[L] |
| Σ6 Rank and degree uniformity | Partially solved | RH | theta ranks `≤14`; all ranks reduce to the adaptive head (Σ133) [L] |
| Σ13–Σ15 Tensor amplification; deformation to a positive model; separable assemblies | No-go | — | `K_ζ^n` PD ⇔ RH; a crossing-free path ⇔ PD; separable assemblies miss a cross-difference [L] |
| Σ20 Scheduled prime sums | Open | RH | FU: one-sided subpower bound `A(M)/M≤C_εM^ε`; CFC, RP, LI receivers [L*]; no estimate on advancing histories |
| Σ27 Window stages | Partially solved | sub | floors `(1/20000)/2^k` on `a_k<0.3621`; margins `∫f²/5000` at `a=181/500`, `∫f²/8000` at the enlarged aperture `<½` [L]/[L*] |
| Σ28, Σ41 Negativity budget; aperture–depth duality | Sharpened / Classified | ≥qRH; sub | window positivity at `a` bounds `k·pairEnergy(δ,a)` by the cell count of the sea [L*]; models hide an off-line zero to aperture `(log T)/36` [L]; matching constants unverified (A79, A81) |
| Σ42, Σ53, Σ57 Markov, size-only payment, Perron | No-go | — | Markov part dies at `e^{−3/4}`; size payment ends before `21/40`; Beurling–Deny exactly on plastic windows [L]/[K] |
| Σ47 Odd unit window | Open (rung available) | sub | follows from verification to `windowHeight(½)` [L] |
| Σ49 Reality by continuation | Sharpened | RH | RH ⇔ every zero of every `H_t`, `t>0`, is simple [L*] |
| Σ56, Σ66, Σ113 Onset aperture; contact; restoring bound | Sharpened | RH | RH ⇔ `a*(ζ)=⊤` ⇔ `Ψ` and `L=artanh r` locally bounded; off RH `L` is unbounded above every base [L*] |
| Σ73–Σ80 Hausdorff rows, heat grids, theta endpoint, renewal, cosine, quartic charge, cubic gate | Sharpened | RH | exact receivers of PA, HCF, TT, RN, PTR, GTA, TG [L*]/[L] |
| Σ82 Finite-rung principle | Partially solved | sub | `RHVerifiedThrough 67`; `RHVerifiedThrough(windowHeight a)` ⇒ the sign on `[−a,a]` [L*]; no finite rung decides an atom [L] |
| Σ98, Σ133 Theta heads | No-go (fixed heads); Sharpened | RH (all ranks) | the adaptive partial sum is `ζ(½+ib)` up to `O(\|b\|^{−½})` [L]; the signed head near critical zeros is open |
| Σ116, Σ117 Weighted Gårding; typical-height sign | No-go (full horizon); Partially solved | sub | deep atoms defeat full-horizon Gårding; typical heights have the sign with Gaussian tails [L] |
| Σ130 Low-packet payment at every ratio | Reduced (to Σ1) | RH | payment at every `R` on growing windows is RH [L] |
| Σ135, Σ139 Pole channel; half-line ground states | Sharpened | method | complete matrix positive ⇔ primitive hyperplane ∧ pole channel; below `W₀` the pole channel decides; `R_c=W₀` ⇔ pole channel positive at every `R<W₀`; RH, or `R_polar<W₀`, or `R_polar=W₀` finite with every ground state polar-orthogonal [L*]; the third case is B104 |
| Σ140 Holomorphic multipliers | No-go | — | no countable square-bounded family dominates the depleted kernel [L] |
| Σ137, Σ138 Integer, sparse and prime degrees | Solved (identity) | RH; ≥qRH at `p^a` | RH ⇔ the traces at the prime degrees are bounded below [L*]; power-thin exceptions keep the criterion, density-zero exceptions need ZAL [L*] |
| Σ141 One Weil test per prime | Solved (identity) | RH | RH ⇔ `Re W(B±τ_{log p}B)≥0` at every prime ⇔ these values bounded below [L*] |
| Σ142, Σ143 The lower side; Rankin square | Classified; Solved (identity) | method | the lower side is blind to nonnegative almost periodic tops; a real zero masks shallower zeros [L] |
| Σ144 Two-sided bounds are sign-free | Solved (identity) | RH; ≥qRH | `\|c_p\|≤Kp^σ` ⇔ width `≤σ`; on log-square windows by complex deletion filters [L*] |
| Σ145 `√T` windows | Solved (identity) | RH | every tempered configuration without real zeros is decided on arbitrarily late `r√T` windows [L*] |
| Σ146 Resolution of the minimal face | Settled in `𝒵`; Open in `𝒵₀` | method | radius `32 log(T+2)` decides ζ [L*]; in `𝒵(γ_min,C)` no bounded length and not every unbounded radius decides [S]; the refuting configuration has `8(k+1)Γ_k` deep zeros in `[Γ_k,2Γ_k+1]` and ζ has `o(V)` [D]/[L*]; B151 |
| Σ147 Bohr-dense samples | Solved (receivers) | AAL; with ZAL RH | sets with arbitrarily long intervals are Bohr-dense; a floor on such a set puts an attained top on the line [L*]/[L] |
| Σ148 Logarithmic windows with exceptional sets | Solved (identity) | RH; ≥qRH at `p^σ` | RH ⇔ the floor outside `Ce^{δT}` primes of arbitrarily late logarithmic windows; width and Stepanov forms; a power saving ⇔ quasi-RH; under ¬RH every late window keeps a violator [L*] |
| Σ149 Short windows and deep-ordinate separation | Classified | method | every `L>0` has an impure tempered configuration bounded below on late windows of length `L`; with `δ`-separated deep ordinates length `80/δ+1` decides from both sides [L*] |
| Σ150 Arithmetic-clock Green energy | Solved (identity) | RH (sign) | `0≤W−E_r≤(1−r²)‖f′‖²/2` uniformly on a support window; the damped form has a finite limit exactly on the closed Weil form domain; coercively shifted damped inverses converge strongly to the restricted Weil covariance [L*]; the sign of `E_r` is Σ1 [D] |
| Σ151 Two-prime local windows | Solved (identity) | RH | RH ⇔ the lag correlation is bounded below on the difference lags of two primes in `\|ℓ−T\|≤r√T` for arbitrarily late `T` [L*] |
| Σ152 Windows below the logarithmic radius | No-go (class `𝒵`) | method | one configuration of simple zeros in `𝒵(γ_min,C)`, with unattained top `½+Θ`, `0<Θ≤½`, is bounded below beyond every bound on windows of every fixed length and on windows of a monotone radius `R→∞`, `R=o(log T)`, also at the prime logarithms; `R` is built with the configuration [S]. A floor on windows of any unbounded radius excludes world I [L*]/[D] |
| Σ153 Hodge index of the degree-point pairing | Solved (identity) | RH | on every finite family of packets the defect `2d₁d₂−D·D` has at most `#{ρ: Re ρ>½}` negative squares; RH ⇔ exactly one positive square on `H,V` and every finite family [S] |
| Σ154 The comb form at finite scale | Partially solved | sub (short windows); RH (every ratio) | one matrix on the integers; Zariski's lemma; on `(N,N+M]`, `18M≤N`: `D·D≤−(1/40)Σc_n²`, comb form `≥(1/50)Σc_n²`; for every `Q` nonnegative on vanishing block sums, fewer than `2QR(Q)` blocks, at every scale `N≥R(Q)`; a lower bound `−ηΣc_n²` at arbitrarily large scales, every ratio and `η`, gives RH; under ¬RH a negative direction of bounded norm exists at every large scale [S]; the full window is B152 |
| Σ155 The sign is carried by the contacts | Solved (identity) | RH (sign) | packets of width `≤181/250` of any sign with margin `∫f²/5000`; comb Bézout with weights `w` ⇔ RH ∧ `w=Λ`; a weight differing from `Λ` at one integer fails on some packet; unit masses force `Λ`; an excess of contact mass above `1+γ/2−½log 4π` breaks the flat tail [L*]/[S] |

## Π — precision and production

| Wall | Status | Strength | Content |
|---|---|---|---|
| Π1, Π4 Global law; window precision | Solved (equivalences) | RH | `ψ(x)−x≤C√x log²x` ⇔ RH; classical one-sided receivers [L] |
| Π2 Deciding input | Open | RH | no unconditional input at square-root precision [L] |
| Π3, Π67, Π70, Π71 Producer cost, ceilings and rates | Solved (exponent scale) | sub / ≥qRH / RH | `c₁/(√K(1+log K))≤bestRate K≤exp(−(log K)^α)`; rates `K^{−a}` for all `a<½` give RH; no rate past `½` [L*] |
| Π7, Π151 Census | Partially solved | sub | critical-line density `≥0.67250071`; covariance ceiling `4π(1−0.67250071)`; failure of `θN` forces `(1+HD(1)−2θ−1/A−ε)N` simple off-line zeros within `A/log T` [L*]; `7/10≤certOpt(B)` ⇔ `B≤4`; positivity alone cannot reach `¾` [L] |
| Π12 Subconvexity and heat floor | Partially solved | sub | `μ(½)≤33/200`; heat horizon `6600/9991` [L] |
| Π22, Π65 Near-line density; log-mean | Reduced | sub | depth `O(T)`; off-line second moment `o(V)`; zeros of depth `≥d₀` number `o(V)` [L*]; depth density `o(T)` open (B57) |
| Π40 Strip self-improvement | Open | sub | `Θ<1⇒Θ=½` fails for shifted products [L]; implies AAL and is implied by the transfer of S3 [D] |
| Π41, Π42, Π56 Mollifier length; long-moment receivers; last-scale floor | Solved (necessary bounds); Sharpened | RH (receivers) | near-unit moments need length `exp(c log²T)`; RH ⇔ cofinal polynomial boundedness of long Möbius-mollified moments [L] |
| Π46, Π55 Parity blindness; barrier blindness | No-go | — | Type I and Type II norms are parity-blind; one Euler factor plants a zero without moving the prime walk [L] |
| Π51 Vinogradov–Korobov barrier | Open | sub | every unconditional pointwise saving is VK [L] |
| Π53, Π54, Π80 Cluster wall; negative moments; short-sum barrier | Open | sub | isolated zeros at rate 2; exceptional heights past `log T` open [L] |
| Π66, Π125, Π126 Integrality; exactness on the torsion; Stepanov degrees | Solved (exact) | RH (degree bound) | exact Stepanov count over ℤ is Chebyshev's; RH ⇔ `log N(A_N)≤N+C√N log²N`, also for the squarefree auxiliary [L*] |
| Π84, Π99, Π100 Parity exponent; count rigidity | Solved | ≥qRH at power saving | Liouville exponent = zero abscissa; count error `o(log n)` forces the rational primes [L] |
| Π93 Möbius as a cubic Gauss coefficient | Solved (identity); descent open | past VK | nonzero residue at `4/3`; rational transfer open [L] |
| Π94, Π128–Π130, Π137 Returns of the prime orbit | Partially solved | sub; ≥qRH in a strip | no heavy return while `log t≤(log y)^{3/2−ε}` [L*]; a strip of depth `h` gives `log t≥c·y^{½−h}`; two-prime depth law [L] |
| Π102 Positive Euler products with a finite top layer | Solved (countermodels) | — | integer-norm products with linear counting, continued to `Re s>1/3`, with a finite top and prescribed remainder depths [L*] |
| Π103 Mean values of multiplicative functions | Solved (in law) | sub | Matomäki–Radziwiłł for μ at every length `h→∞`, `h≤√x`, fibre form [L] |
| Π105, Π127 Farey, nerve, orientation cover | Solved (identity) | RH (weight `½`) | centred count `M(N)=Ω±(√N)`; weight `½` ⇔ RH [L*] |
| Π112–Π114 Exceptional rank; infinite-rank Hasse–Weil; thick crude count | Sharpened | AAL; RH with attainment | RH ⇔ attained top ∧ thick bounded lag ⇔ attained top ∧ thick `O(√X)` prime deviation; a lag bounded on a thick set leaves RH or an unattained top [L*] |
| Π116, Π122 Long mean values are collision counts | Solved (identity) | identity | order `X²` past the height [L] |
| Π121 Precision cost of forced vanishing | No-go | — | Rouché copies capped at `J≤e²r log N+log(1/δ)` [L] |
| Π123, Π135 The Stepanov bound is a prime count; its saving | Solved | RH; sub (VK) | `c_B(log d)=A(d)−P(d)`; RH ⇔ `P(p)≤A(p)+K` [L*]; VK saving [L] |
| Π124, Π143 Tensor powers | Solved (identity) | RH (uniformity) | constituents are Tate twists; RH ⇔ sublinear tensor exponents with the trace of ζ retained [L*] |
| Π133, Π134 Reciprocity of returns; label statements | Solved; Classified | method | a uniform route from returns to ZAL over a class containing `ζ(s−h)` refutes the return conjecture [L*] |
| Π136, Π140 Collective rank depth and return counts | Solved (beyond the depth floor) | sub | the floor grows with the number of primes [L] |
| Π138, Π139 Stepanov syzygies; orbit symmetries | Solved (classification) | identity | rational self-maps preserving the prime orbit are Laurent Adams maps [L] |
| Π141, Π142 Gauge family; transfer to one fibre | Classified; No-go | method | big monodromy and Gaussian generic fibres; exact monodromy prices every fibre at the trivial bound [L] |
| Π144 Witt vectors and Frobenius lattices | Classified | method | no finitely generated lattice stable under three prime Frobenii [L] |
| Π145 The fixed part of the canonical arithmetic families | No-go (these families as producers) | method | moments `≥ν{0}\|A(0)\|²(Σa_n)^{2k}`; strict gain at a nontrivial torsion fibre; one-way product positivity; trivial fibre of vanishing mass in five family classes; cover-family tensor criterion ⇔ RH [L*] |
| Π146 Frobenius at one prime; the cost of vanishing | Solved (price) | — | `x↦xⁿ` is a Frobenius at `q` iff `n=q^k`; `Λ(n)` counts those primes with weight `log q`; order `m` at every prime of `S` costs `m·Σ_{p∈S}log p`, attained by `Πp^m`; `ℤ` has only the identity endomorphism [L*] |
| Π147 The arithmetic square | Solved (construction); Classified | — | `𝒢=W(ℤ)`; `Γ_m·Γ_n` = jets + contacts; a perfect square keeps no contact; finite fibres force contacts that are not Weil's; one ring of sequences contains the tower of lines, the pole plane and the jets with exact counts; for a Dedekind domain the necklace coordinate at `𝔡` is the ideal `𝔡` and an orbit exists iff `𝔡` is principal [L*] |
| Π148 Heavy returns in the two worlds; the transfer | Classified | ≥B56 (transfer) | world I: `log t≥c·y^{1−β″}`, `β″<Θ` [L*]; the transfer of S3 implies `Θ<1⇒Θ=½` [D] |
| Π149 Centred Vaughan currents | Solved (reduction); bound open | AAL | for every moment order `r≥1` the Gaussian prime moment minus its pole is the centred current up to `O_r((1+1/η)/t)` on admissible cutoffs; filtered cofactor reduction error `O(h^k/t)`; exact cofactor truncation with both continuum terms [L*]; at `σ=½`, `X=e^{at}`, moment order `r log t≍κt`: error `≤C(1+t²)(1+at)e^{−(3a/8)t}`, discarded cofactor tail `≤784e^{−t²}` for `UW≥Xt²`, so at most `3t^{J+3}` cofactors carry the current up to `Ce^{−(a/4)t}` [S]; the signed current at a growing isolated mode is the exclusion (B145) [D] |
| Π150 The gluing index counts the zeros in the mean | Solved (identity) | identity | gluing index `N!`; `\|log N!−N(2πN)\|≤C log N`; `G(T)−N(T)+S(T)→½log 2π−7/8`; `G(T)−N(T)` leaves every bounded neighbourhood of that constant [L*] |
| Π152 Kronecker over ℤ at infinite rank | Classified | — | integral trace-class modules with a chain condition carry only Tate twists; eventually integral traces of modes in the open strip force zero amplitudes; `Λ` and the Mertens function are not traces of any order [L] |
| Π153 Stepanov at one prime | Solved | sub (one prime) | fibres of the truncated logarithm over `𝔽_p` have at most `100p^{2/3}` points; pair collisions of the Teichmüller image in `ℤ/p²` are these fibres; `\|Σ_{n≤p}e(an^p/p²)\|≤5p^{11/12}`, `p∤a` [L*] |
| Π154 The carry class | Classified | — | the digit carry and the Witt carry are cocycles that are not coboundaries; carry defect + window-count defect + `½log N → −½log π`; a bound for either transfers to the other [L*] |
| Π155 Riemann–Roch on the tower of lines | Classified | — | a nonzero section vanishing on `Γ_1,…,Γ_K` exists once `Π_{n≤K}(⌊2B_n/n⌋+1)<(A+1)^{bτ(M)}`: second term the gluing index `K!`; its first nonvanishing graph has `n>K`, `n≤\|x_n\|`: the conclusion is the product formula [S] |

## Γ — selection, reflection, position

| Wall | Status | Strength | Content |
|---|---|---|---|
| Γ1 Self-return | Open | RH | strong recurrence on a disc ⇔ head-target density uniform in the head length; uniform density on every right-strip disc ⇒ RH [L*] |
| Γ15, Γ33, Γ35, Γ167 Rigidity of ζ | Solved (classification) | method | Hamburger; degree-one classification; Beurling systems with `L¹`/`L²` FE defect are the rational primes [L] |
| Γ23 Weil cone uniqueness | Solved | — | full positivity forces Λ; cone nonemptiness is RH [L] |
| Γ24, Γ62, Γ95 Mayer reflection; Hecke dispersion; Krein flux | Sharpened | RH | exact identities; the signs are RH [L] |
| Γ42 Legendre reality | Solved (identity) | RH | RH ⇔ `J(ρ)∈ℝ` [L] |
| Γ49 Exceptional values | Partially solved | indep. | nonrepelling values: dense `G_δ` of dimension zero; `0∉E` open [L] |
| Γ61 Inner factor | Solved (identity) | RH | `I≥0`; RH ⇔ `I=0` at one point [L] |
| Γ67, Γ183 Abscissa split and atoms | Solved (identity) | identity | RH ⇔ ZAL ∧ B13 ∧ Landing; AAL ⇔ B13 ∧ Landing ∧ DH; a failure of the abscissa law fails exactly one of B13, Landing, DH [L*] |
| Γ68, Γ69 AAL and its producers | Open; Partially solved | sub | thick lag bounds, log-dense integer lags, Bohr-dense floors give AAL [L*]/[L]; each retains its source bound |
| Γ73, Γ145 One-off countermodels; firewall | No-go (positive data) | — | integer-norm Euler products with linear counting carry finite top layers and approaching remainders [L*]/[L] |
| Γ86, Γ121, Γ122 Modular horizon; horocycle and ringdown rates | Solved (identity) | RH (rate) | RH ⇔ every compact pulse decays at `e^{−(¼−ε)τ}`; strip of width `2δ` ⇔ rate `e^{−(δ−ε)τ}` [L*] |
| Γ89, Γ148, Γ157 Physical positivity; modular conjugation; half-sided inclusions | No-go | — | blind, central, or without eigenvalues [L] |
| Γ96, Γ125, Γ154 Count law of curves; count door | Solved (curves); Sharpened (ℤ) | RH | quadratic growth of an `ℕ`-count ⇔ `Q≥0`; on a hyperelliptic curve the defect of an integral class is a natural number; RH ⇔ an `ℕ`-count with Tate limit the integer probes [L*] |
| Γ97, Γ131, Γ162 Integer probes | Sharpened | RH | the probes are not integer-valued [L] |
| Γ119, Γ191 Random models | Classified | method | Haar-a.e. Euler products are zero-free right of `½`; in-law statements are blind to the atoms [L]/[D] |
| Γ132 Narain remainder | Sharpened | RH (rate `¾`) | VK saving; exponents past `¾` impossible [L] |
| Γ134, Γ171 Cavity receivers | Solved (receiver) | RH (rate) | one cavity function of Hecke forms: RH ⇔ energy rate `y^{¾−ε}`; strip ⇔ rate `y^α`, `α>½` [L*] |
| Γ137, Γ161, Γ181 Positive annihilators | No-go (positivity as exclusion) | — | price finite zero sets, never exclude them [L] |
| Γ140, Γ155, Γ156 Two-scale law; linear hierarchy; heat family | No-go (scale-separated and family-uniform inputs) | — | landing is a tail law undecided below every height; heat finiteness does not pass to `t=0` [L*] |
| Γ141, Γ185 The FE admits finite layers and approaching remainders | No-go | method | an FE model with approaching quartets violates landing; so does an integer-norm Euler product [L] |
| Γ142, Γ143 AAL is transport; free AAL | Classified | sub | AAL ⇔ zero transport ⇔ tail transport; free for recurrent classes [L] |
| Γ150–Γ153, Γ158, Γ168 Half-products; point count; fibres | Solved (identity) | identity | archimedean kernel `=2π√(mn)G_{1/2}`; `p`-kernel = tree Green function at the Ramanujan point [L] |
| Γ160, Γ166 Finite-rank Euler + FE; Dirichlet selector | Solved (calibration) | — | finite Euler product with FE is pure; only `τ=0` has a Dirichlet series [L] |
| Γ164, Γ165, Γ178, Γ179 Sampling sets; metric recurrence; almost all primes; smooth degrees | Solved (receivers); No-go (without attainment) | AAL | off a relative-density-zero set of primes RH ⇔ ZAL ∧ the Stepanov bound [L*]; unattained tops pass at very smooth degrees [L] |
| Γ169, Γ170, Γ180, Γ187, Γ188 Hyperbolic carriers; locked dampings; mass obstruction; Gram coupling; prime unit | No-go / Solved (finite limits) | — | no one-place carrier; atoms lock to the discriminant; Gram coupling leaves an exact defect [L] |
| Γ172 Krein forms of the cavity | Classified | RH | RH ⇔ every tent reflection Krein form has negative index `0` [L*] |
| Γ173–Γ177 The prime current in world I | Solved (passage laws) | sub | a dominant top ordinate forces divergence; under ¬AAL the top has two distinct positive ordinates or the corrected current diverges at every supercritical speed; fixed positive critical modulus at the polynomial observation boundary [L*] |
| Γ182 The landing law | Sharpened; Settled (method question) | sub | equivalent forms for ζ (Hadamard threshold, Krein–Langer index, heat counts, …); a zero at depth `δ` is lost at every speed `a<π/(2δ)`; fails for the FE alone and the Euler product alone [L*]; open for ζ as an atom |
| Γ184 The Deuring–Heilbronn sector | Classified (models); Open for ζ | sub | classical repulsion for real zeros of primitive quadratic `L(s,χ)`, uniform constant; extreme DH ⇔ (AAL ⇔ B13); graded repulsion refuted on integer-norm products [L*] |
| Γ189 The adelic degree configuration | Solved | producer | full degrees as distinct points of a discrete adelic quotient with commuting prime operators [L] |
| Γ190 Infinite power sums | Solved | method | a maximal term is detected within `64M` powers [L] |
| Γ192 Two worlds | Solved (identity) | identity | `Θ<1⇔Θ∞<1`; ¬AAL ⇒ `Θ<1`; `¬(Θ<1)⇔Θ=Θ∞=1∧AAL`; world I has a Mertens power saving [L*] |
| Γ193 Boundary and polynomial damping filters | Classified | AAL (the gap) | in world I filters grow when `dκ<a(β−σ)/2`; VK bound with exponent `a(1−σ)/2`; the ranges are separated by `a(1−β)/2` [L] |
| Γ194 Gauge deformations are isozeric | Classified | method | a fibre with nonzero analytic residue at `1` is `ζ·exp(H)` left of `1` [L]; analytic unit smoothings `Φ(p^{−t})` from `1` to `−1`: multiplicities kept on `Re s>max(½,1−mt)`, no joint analytic regularization at `(0,1)`, zero-free non-polynomial scaling limit, entire scaling forces `Re Φ′(1)≤−2` [L*]; the `χ₄`-selected pair: zero of order four at `1−2t`, double pole at `1−4t`, scaling limit `ζ(2)(w+2)⁴/(w+4)²` [S] |
| Γ195 Index law and index-one limits | Solved (law); Sharpened | RH | a defect of degree `κ` has at most `κ` exceptional points, attained by `cosh` models; the bound passes to limits; RH ⇔ ξ is a limit of index-one functions; the cleared Eisenstein constant term has a right-half zero exactly for `Y>4πe^{−γ}`; the line law of a pencil ⇔ its fixed part lies in the closed strip [L*] |
| Γ196 One glued carrier object for the diagonal | No-go | — | every adelic-invariant kernel with a torus-orbit functional has a constant degree diagonal and drifts to `−∞`; discriminant jump `−2‖g‖²log p` for every scalar counterterm [L*] |
| Γ197 Weighted adelic Green kernel | Classified | — | invariant positive covariance; the mixed kernel converges absolutely over the rational torus on every pair, symmetric, with stabilizers `±1` and a leafwise Robin finite part; its spherical average at parameter `½` is the minimal Green kernel of the all-prime weighted adjacency [L*]; none identifies Weil's degree diagonal [L] |
| Γ198 The diagonal is the density of a comb | Solved (identity) | RH (sign) | the comb's own density is the counterterm; the ambient point counterterm on the multiples of `g` shifts the limit by `−log g·∫f²`; the comb of squares has the counterterm `log(n/4π)` [S]; a uniformly separated comb stable under the Frobenius monoid is one orbit `δℕ` [S]; the pairing of the degree points has the limit `2d₁d₂−Z(f)`, `Z(f)≥−D(f)`, RH ⇔ `D≡0` [L*] |
| Γ199 The archimedean fibre of the square | Classified | — | weight lines `χ_z`; transposition `z↦1−z`; pole plane at weights `0,1`; no Verschiebung carries the off-diagonal [L*]/[L] |
| Γ200 Section counts and finite type | Classified | RH (Bézout) | a section count with Riemann–Roch and Bézout exists iff the Hodge index holds [L]; no finite-type object carries the contacts [L*]; on the tower both axioms give the product formula (Π155) |
| Γ201 Halving descent and Shimura zeros | Sharpened | RH (rate) | for one Hecke eigenform RH ⇔ sharp rate ∧ no nonhalving Shimura zero [L*]; any halving pair forces `Θ≥2/3` [L] |
| Γ202 The scattering tower | Solved (identity) | identity | Weil's functional on `C²_c` packets is the limit of Robin-normalized Maass–Selberg diagonals, independent of the centre [L*] |
| Γ203 Separation by the height | Solved (receiver) | RH | ordinate injective on the zeros ⇔ `\|c_p\|≤K` at every prime ⇔ RH; fibre spread `≤2σ` ⇔ width `≤σ` [L*]; coefficient gaps do not occur at three explicit critical ordinates [L] |
| Γ204 Positive translation repair | Classified | — | a Laplace-positive function becomes pointwise nonnegative under a positive-root polynomial average of translations [L]: pointwise positivity locates nothing |
| Γ205 No periodicity in height | Solved (no-go) | method | no vertical progression consists of zeros, at any real part; on each half progression `Σ\|ζ(ρ+inT)/(ρ+inT)\|` diverges and no sequence of zeros is eventually within an `ℓ²` perturbation; the periodicity dichotomy for ζ is RH [L*] |
| Γ206 Graded recurrence | Solved (receiver) | ≥qRH (the return count) | for `½≤σ≤5/6`, `c>(30/13)(1−σ)`: `T^c` one-separated returns at arbitrarily large `T` on every small disc exclude a zero right of `σ` [L*] |
| Γ207 Finite-stratum laws on the Jensen and cosine families | Solved (receivers) | RH; RH given ZAL | at each degree finitely many shifted Jensen polynomials fail real-rootedness and the exclusion of finite nonempty strata is RH [L*]; on the cosine family the same exclusion gives RH ⇔ ZAL [L] |
| Γ208 Castelnuovo–Severi on the flow | Solved (identity) | RH | a locally finite summable module in a strip is determined by its trace on `x≥1`; the inequality on every divisor of Frobenius graphs ⇔ pure and effective ⇔ positive definite central trace; for the zero motive with weights `1/(ρ(1−ρ))` ⇔ RH [L*] |
| Γ209 Arithmetic factors | Solved (no-go) | method | a bounded holomorphic Dirichlet-series factor of ξ on a half-plane is pure; a Dirichlet polynomial with a constant term and its zeros on the line has `\|D(1−s̄)\|=N^{Re s−½}\|D(s)\|`; no Dirichlet polynomial with a constant term, with lowest frequency dividing the others, in one base or with two terms has all its zeros among those of ξ; a zero-free Dirichlet polynomial is bounded below on closed half-planes; generalized Dirichlet expansions on the two sides of the line of a function whose singularities on the line are cancelled by ζ have equal constant terms [L*] |
| Γ210 The zeros are the weights of the contacts under scaling | Solved (identity); No-go (pointwise) | identity | against a packet at the scale `e^a` the contact weights are `e^{∓a/2}`, the jets against the Gamma symbol, and `−m_ρĝ(γ_ρ)e^{(ρ−½)a}`; pointwise the shifts of the point count span every finite set of degrees [L*] |
| Γ211 The contacts at a height are the remainder | Solved (identity) | identity | the prime polynomial of a window at a height is the contact weights at that height; contacts + off-line correction − smoothed increments of `S` → 0 [S] |

## Scoped no-gos and surviving replacements

| Boundary | Exact scope and survivor |
|---|---|
| Windows below the logarithmic radius | at the level of `𝒵`: block tower with unattained top (Σ152). Survivors: the logarithmic radius (Σ148); the class `𝒵₀` with deep zeros of density zero (B151); floors on unbounded windows against world I |
| Families as producers | fixed-part laws; isozeric deformations; moving branch; delayed pole (Π145, Γ194). Survivor: a statement at the fibre itself |
| Exact arithmetic factors | bounded Dirichlet-series factors are pure; no polynomial factor with a constant term (Γ209). Outside: polynomials without constant term on several bases; approximation |
| One glued invariant carrier | refuted (Γ196). Survivors: the density of the comb (Γ198), weighted covariance and Robin diagonal (Γ197), the clock (Σ150), the scattering tower (Γ202) |
| Finite-type objects carrying the contacts | excluded (Π147). Survivor: the tower of lines and the ring of sequences with exact counts |
| Riemann–Roch with Bézout on the tower | the product formula (Π155). Survivor: Bézout for the comb pairing (B149) |
| Frobenius for a window; cheap vanishing | one prime per power map; cost `m·θ(S)` (Π146). Survivor: Stepanov at one prime (Π153) |
| The carry as an independent bound | nonzero class; complementary identity (Π154) |
| One counterterm across combs or scales; a diagonal attached to a point | the density of the comb (Γ198) |
| Other contact weights | the comb selects `Λ` (Σ155) |
| Incommensurable degree orbits on one separated comb | a separated comb stable under the Frobenius monoid is one orbit (Γ198) |
| Pointwise closure of the shifts of the point count | dense (Γ210). Survivor: packets at a scale |
| The gluing count as a count at a height | misses by `S` (Π150). Survivor: the contacts at a height (Γ211) |
| Integral or trace-class Frobenius modules | Tate twists only (Π152, Π144). Survivor: the flow (Γ208) |
| The line law of a family as purity of its fixed part | holds over impure fixed parts (Γ195). Survivor: an independent index-one family converging to ξ (B146) |
| Separation by absolute value | excluded for ζ (Γ203). Survivor: the ordinate as separating invariant, a receiver |
| The transfer of candidate S3 as a method question | implies strip self-improvement (Π148) |
| The clock energy as a producer | ordered approximation of `W` with exact form domain (Σ150) |
| Density-zero exceptions, very smooth degrees, finitely many Frobenii without attainment | unattained tops pass (Γ164, Γ178, Γ179). Survivor: power-thin exceptions per window (Σ148) |
| Scale-separated and family-uniform inputs | decide no atom (Γ140, Γ156) |
| Landing or repulsion from one structure | FE-only and Euler-only models (Γ185, Γ184). Survivor: joint FE–Euler inputs |
| VK or Euler-region bounds as exclusion of a finite layer | ranges separated by `a(1−β)/2` (Γ193). Survivor: an inequality not implied by the explicit formula |
| Exact Frobenius over ℤ; integrality at returns; Rouché copies | torsion only; Chebyshev; precision cap (Π121, Π125, Π126) |
| Positivity, Euler products, integrality, counting, annihilators as an atom | one-offs and annihilators (Γ73, Γ137, Π102) |
| Internal, vacuum-fixing and half-sided modular realizations | excluded (Γ148, Γ157) |
| Markov, Perron, size-only payment, floor tower, universal multipliers, fixed theta heads | refuted or bounded (Σ42, Σ53, Σ57, Σ27, Σ140, Σ98) |
| One Hecke eigenform without side condition | halving pairs and Shimura zeros (Γ201) |

## Bridges

| Bridge | Anchor |
|---|---|
| One inequality per prime: Weil test = Stepanov count = count door = sign-free trace, on logarithmic windows off power-thin exceptions | SOSZ [L*] |
| One matrix on the integers: Weil's form on packets = comb form = `2d₁d₂−D·D` → zero sum; Hodge index ⇔ RH; two-block divisors = the Stepanov bound | AGZ, HTFP [L*]/[S]/[D] |
| Window sign ⇔ verification height, up to constants | VHR, WVL [L*]/[L] |
| Critical curve: `R_c=R_polar=R_halfline≤W₀`; complete matrix = primitive hyperplane + pole channel | AHD [L*] |
| RH ⇔ ZAL ∧ B13 ∧ Landing; two worlds; quasi-RH is a tail law | ZCG, ELT [L*] |
| World I ⇒ Mertens power saving, late heavy returns, filters at every speed, failure of every floor on unbounded windows | ELT, TTPO, SOSZ [L*] |
| Unbounded windows ⇒ AAL; attained top + thick crude count ⇒ RH | SOSZ, IRP [L*] |
| Fixed part ⇔ no family producer; tensor exponents with the trace of ζ ⇔ RH | AWT [L*] |
| Rigidity: Hamburger, FE-defect isolation, count distance, isozeric deformations, pure factors | HTGeometry, EFT, SPAL, AWT, IRP [L*]/[L] |
| Off-diagonal Weil = contacts + jets = pole − `ℍ³` Green − tree Green | AGZ, SOSZ, HAT [L*]/[L] |
| Diagonal = density of the comb = limit of the scattering tower = limit of the clock energies | AGZ, HAT [L*] |
| Flat tail of the comb form = `2+γ−log 4π` = twice the first Li coefficient; its potential = the remainder of the prime number theorem | HTFP [S]/[D] |
| Gluing index `N!` ↔ smooth zero count; contacts at a height ↔ `S(T)` ↔ the prime polynomial of a window | AGZ, SquareRootThreshold [L*]/[S] |
| Flow: Castelnuovo–Severi = pure and effective = positive definite lag function | IRP [L*]/[D] |
| Index law; index-one limits; Eisenstein line law | IRP [L*] |
| Ordinate injectivity ⇔ bounded two-sided prime traces | SignFreePurityMechanisms [L*] |
| Cavity energy rate ⇔ zero-free region; reflection Krein index counts off-line zeros; one eigenform ⇔ rate ∧ Shimura | AHMH [L*] |
| Mertens level = producer rate = Farey = nerve = orientation cover | AAD, RIAC, HAT [L*]/[L] |
| Carry defect ↔ window-count defect | AGZ [L*] |
| Census: covariance ceiling ⇔ line density; deep zeros of density zero ⇒ pure factors | SquareRootThreshold, IRP [L*] |

## Strength of the open walls

- **RH:** Σ1, Σ2, Σ3a, Σ6 (all ranks), Σ20, Σ49, Σ56, Σ66, Σ73–Σ80, Σ113, Σ129 (thresholds `=⊤`), Σ130, Σ133, Σ137, Σ138, Σ141, Σ144, Σ145, Σ146 (the bound), Σ148, Σ150 (sign), Σ151, Σ153, Σ154 (every ratio), Σ155 (sign), Π2, Π42, Π123, Π124, Π126, Π127, Π143, Γ1, Γ24, Γ62, Γ95, Γ97, Γ121, Γ122, Γ131, Γ134, Γ154, Γ171, Γ172, Γ195, Γ198 (sign), Γ200 (Bézout), Γ201 (rate), Γ203, Γ207 (Jensen law), Γ208.
- **≥qRH:** Σ4, Σ28, ZAL, `N_d` bounded, any interior width value (Σ137, Σ138, Σ144, Σ148 at `p^σ`, `σ<½`), Π3 (polynomial rate), Γ121/Γ122/Γ132 (interior exponents), Π137 (strip rung), Γ206 (the return count).
- **AAL:** Π114 (thick crude count at every exponent), Γ164, Γ165, Σ147, Π149 and Γ193 (the growth-range bound), Π148 (the transfer, with strength ≥B56).
- **sub:** Σ27, Σ47, Σ82, Σ116, Σ117, Σ154 (bounded ratios), Π7, Π12, Π22, Π40, Π51, Π53, Π54, Π65, Π80, Π94, Π103, Π136, Π140, Π151, Π153, Γ68, Γ182 (landing as an atom), Γ184 (DH for ζ), B13.
- **method / producer / indep.:** Σ135 and Σ139 (B104), Σ146, Σ149 and Σ152 (B151, B144), Π141, Π142, Π144, Π145, Π146, Π147, Π152, Π154, Π155, Γ49, Γ189, Γ194, Γ196, Γ197, Γ199, Γ202, Γ204, Γ205, Γ209, Γ210, Γ211.
