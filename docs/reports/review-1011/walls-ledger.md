# Walls ledger — status quo

**Corpus checkpoint:** commit `e5518fe065` with its working tree (2026-11-10). Working log: `logs/review-1011-statusquo-research.md`. Companions: [route-obstacles.md](route-obstacles.md), [route-unification-ledger.md](route-unification-ledger.md), [obstacles-summary.md](obstacles-summary.md).

Three wall families carry the frontier. **Σ** is the critical sign of the window form, **Π** the precision and production of the prime count, **Γ** the selection of ζ, the reflection of its zeros and their position in height. All three meet in one minimal face, local in scale and tolerant of power-thin exceptions.

- **The minimal face.** RH ⇔ `P(p)≤A(p)+K` at every prime ⇔ the same at the primes of arbitrarily late logarithmic windows `|log p−T|≤32 log(T+2)`, outside at most `Ce^{δT}` primes per window (`δ<1`) [L*]. Sign-free: RH ⇔ `|c_p|≤K` on such windows [L*]. Width `≤α` ⇔ the floor `−Kp^α` [L*].
- **Σ is the sign of every window.** RH ⇔ `W≥0` on every window ⇔ `Ψ` locally bounded ⇔ one Weil test per prime [L*]; a window at aperture `a` follows from verification to `windowHeight(a)` [L*]; at the critical curve `R_c=R_polar=R_halfline≤W₀` with a three-way classification [L*].
- **Π is the same sign on the prime side.** Unconditional pointwise savings are Vinogradov–Korobov; everything past it is in law. Exact methods over ℤ have exact prices: Frobenius at one prime, cost `m·θ(S)`, Chebyshev auxiliaries, the fixed part of every family [L*].
- **Γ is the same sign on the zero side, plus position.** A failure of RH lies in world I (¬AAL: a finite isolated top, with a zero-free strip) or world II (AAL ∧ ¬ZAL: a tail) [L*]/[D]; RH ⇔ ZAL ∧ B13 ∧ Landing [L*]. Weil's kernel is an adelic Green pairing off the diagonal; its diagonal is a comb finite part and not one glued carrier object [L*].

[Frontier](../rh-current-frontier-map.md): **38 live formulations, 12 candidates**. [Scoped obstructions](../rh-killed-routes.md) separate failed mechanisms from open replacements.

**Status.** **Solved** (the face is a theorem), **Partially solved**, **Sharpened** (open, exact form a theorem), **Open**, **No-go** (mechanism refuted), **Classified**, **Reduced** (theorem-level equivalent named), **Settled** (a method question answered). **Strength:** RH, ≥qRH, AAL, sub, indep., identity, method, producer. **Evidence:** `[L*]` Lean statement read for this ledger; `[L]` recorded as integrated Lean in the frontier map, the scoped-obstruction ledger or a programme table of `formal/` returned by the corpus search tool; `[S]` source present in the working tree, not committed at the checkpoint, statement read; `[K]` Lean with transitive axiom audit as recorded; `[D]` deduction; `[C]` classical.

Notation as in [route-obstacles.md](route-obstacles.md).

## Σ — critical sign

| Wall | Status | Strength | Content |
|---|---|---|---|
| Σ1 Weil's sign | Sharpened | RH | RH ⇔ `W≥0` on every window ⇔ `Ψ` locally bounded on precontact intervals ⇔ the odd archimedean-minus-prime form `≥0` ⇔ the even blind minimum `≥0` at every aperture ⇔ the variation inequality at one shift ⇔ Cayley ladders NSD on primitives ⇔ global incidence allocation ⇔ Weil positivity of every prime two-bump ⇔ the floor on logarithmic prime windows ⇔ `E_r(f)≥−ε` near `r=1` on every packet [L*]/[D] |
| Σ1b, Σ1k Subcritical regime; one critical multiple | Solved | sub | complete tilted-spline matrix PD below exponent `1/8` [L] and at `c≤2K₀(log N)^{1/8}` [K] |
| Σ1c–Σ1x Critical-curve calculus | Classified | sub / method | shell–pole payment, conductor resolution, receiving charges, Γ-liminf, top-collar Gårding, alias notch, Gamma reserves [L]/[K] |
| Σ1u, Σ129 Threshold law | Solved (identities) | RH (all thresholds `=⊤`) | `R_c=R_c^{PSD}=R_polar=R_halfline≤W₀`; `R_polar=W₀` ⇔ half-line polar positivity at every `R<W₀` [L*] |
| Σ2 Edge, zero modes, hard Lefschetz | Sharpened | RH | zero modes radical and two-site; Hodge index = Li positivity [L] |
| Σ3a Coprime stratum | Sharpened | RH | `det R_N=M(N)`; RH ⇔ `χ̃=O(N^{½+δ})` [L] |
| Σ4 Finite index / heat count | Sharpened | ≥qRH; RH for index 0 | under AAL: RH ⇔ ZAL ⇔ finitely many off-line zeros ⇔ finite negative index ⇔ bounded heat counts ⇔ finite source energy ⇔ eventual Hadamard positivity ⇔ central-gap budget [L*] |
| Σ6 Rank and degree uniformity | Partially solved | RH | theta ranks `≤14`; all ranks reduce to the adaptive head (Σ133) [L] |
| Σ13–Σ15 Tensor amplification; deformation to a positive model; separable assemblies | No-go | — | `K_ζ^n` PD ⇔ RH; a crossing-free path ⇔ PD; separable assemblies miss a cross-difference [L] |
| Σ20 Scheduled prime sums | Open | RH | FU, CFC, RP, LI receivers [L*]; no estimate on advancing histories |
| Σ27 Window stages | Partially solved | sub | floors `(1/20000)/2^k` on `a_k<0.3621` [L] |
| Σ28, Σ41 Negativity budget; aperture–depth duality | Sharpened / Classified | ≥qRH; sub | ground-energy fall rate = width; positivity at aperture `a` forces near-line zeros to a height of scale `e^{a}`; models hide an off-line zero to aperture `(log T)/36` [L]; matching constants unverified (A79) |
| Σ42, Σ53, Σ57 Markov, size-only payment, Perron | No-go | — | Markov part dies at `e^{−3/4}`; size payment ends before `21/40`; Beurling–Deny exactly on plastic windows [L]/[K] |
| Σ47 Odd unit window | Open (rung available) | sub | follows from verification to `windowHeight(½)` [L] |
| Σ49 Reality by continuation | Sharpened | RH | RH ⇔ every zero of every `H_t`, `t>0`, is simple [L*] |
| Σ56, Σ66, Σ113 Onset aperture; contact; restoring bound | Sharpened | RH | RH ⇔ `a*(ζ)=⊤` ⇔ no finite contact ⇔ `Ψ` and `L=artanh r` locally bounded; off RH `L` is unbounded above every base [L*] |
| Σ73–Σ80 Hausdorff rows, heat grids, theta endpoint, renewal, cosine, quartic charge, cubic gate | Sharpened | RH | exact receivers of PA, HCF, TT, RN, PTR, GTA, TG [L*] |
| Σ82 Finite-rung principle | Partially solved | sub | `RHVerifiedThrough 67`; `RHVerifiedThrough(windowHeight a)` ⇒ the sign on `[−a,a]` [L*]; no finite rung decides an atom [L] |
| Σ98, Σ133 Theta heads | No-go (fixed heads); Sharpened | RH (all ranks) | the adaptive partial sum is `ζ(½+ib)` up to `O(\|b\|^{−½})` [L*]; the signed head near critical zeros is open |
| Σ116, Σ117 Weighted Gårding; typical-height sign | No-go (full horizon); Partially solved | sub | deep atoms defeat full-horizon Gårding; typical heights have the sign with Gaussian tails [L] |
| Σ130 Low-packet payment at every ratio | Reduced (to Σ1) | RH | payment at every `R` on growing windows is RH [L] |
| Σ135, Σ139 Pole channel; half-line ground states | Sharpened | method | RH, or `R_polar<W₀`, or `R_polar=W₀` finite with every ground state polar-orthogonal [L*]; the third case is B104 |
| Σ140 Holomorphic multipliers | No-go | — | no countable square-bounded family dominates the depleted kernel [L] |
| Σ137, Σ138 Integer, sparse and prime degrees | Solved (identity) | RH; ≥qRH at `p^a` | RH ⇔ Hasse–Weil at the integer degrees ⇔ the traces at the prime degrees are bounded below [L*]; power-thin exceptions keep the criterion, density-zero exceptions need ZAL [L*] |
| Σ141 One Weil test per prime | Solved (identity) | RH | RH ⇔ `Re W(B+τ_{log p}B)≥0` at every prime ⇔ these values bounded below [L*] |
| Σ142, Σ143 The lower side; Rankin square | Classified; Solved (identity) | method | the lower side is blind to nonnegative almost periodic tops; a real zero masks shallower zeros [L] |
| Σ144 Two-sided bounds are sign-free | Solved (identity) | RH; ≥qRH | `\|c_p\|≤Kp^σ` ⇔ width `≤σ`; on log-square windows by complex deletion filters without positive averaging [L*] |
| Σ145 `√T` windows | Solved (identity) | RH | every tempered configuration is decided on arbitrarily late `√T` windows [L*] |
| Σ146 Resolution of the minimal face | Sharpened | method | radius `32 log(T+2)` decides ζ [L*]; the radius below it is B143 |
| Σ147 Bohr-dense samples | Solved (receivers) | AAL; with ZAL RH | sets with arbitrarily long intervals are Bohr-dense; a floor or a ceiling on such a set puts an attained top on the line [L*] |
| Σ148 Logarithmic windows with exceptional sets | Solved (identity) | RH; ≥qRH at `p^σ` | RH ⇔ the floor outside `Ce^{δT}` primes of arbitrarily late logarithmic windows, `δ<1`, sets chosen per window; width and Stepanov forms; under ¬RH every late window keeps a violator outside every such set [L*] |
| Σ149 Short windows and deep-ordinate separation | Classified | method | every `δ>0` has an impure configuration with `δ`-separated ordinates bounded below on windows of length `2π/δ`; no fixed length decides every configuration; with `δ`-separated deep ordinates length `80/δ+1` decides from both sides, also in count form [L*] |
| Σ150 Arithmetic-clock Green energy | Solved (identity) | RH (sign) | `0≤W−E_r≤(1−r²)‖f′‖²/2` once the clock covers the capacity; capacity `∼4√N`; clock horizon sharp at `κ=4`; uniform on growing windows [L*]; the sign of `E_r` is Σ1 [D] |
| Σ151 Two-prime local windows | Solved (identity) | RH | for distinct primes `p,q` and `r>0`: RH ⇔ the lag correlation is bounded below on the difference lags of the monoid of `p,q` in `\|ℓ−T\|≤r√T` for arbitrarily late `T` [L*] |

## Π — precision and production

| Wall | Status | Strength | Content |
|---|---|---|---|
| Π1, Π4 Global law; window precision | Solved (equivalences) | RH | `ψ(x)−x≤C√x log²x` ⇔ RH; classical one-sided receivers [L] |
| Π2 Deciding input | Open | RH | no unconditional input at square-root precision [L] |
| Π3, Π67, Π70, Π71 Producer cost, ceilings and rates | Solved (exponent scale) | sub / ≥qRH / RH | rates `K^{−a}` for all `a<½` give RH [L*]; rate = Mertens level; no rate past `½` [L] |
| Π7, Π151 Census | Partially solved | sub | critical-line density `≥0.67250071`; covariance ceiling `4π(1−a)` ⇔ density `≥a`; `θN≤N₀` or `(1+HD(1)−2θ−1/A−ε)N` simple off-line zeros within `A/log T` [L*]; `7/10≤certOpt(B)` ⇔ `B≤4` [L*]; positivity alone cannot reach `¾` [L] |
| Π12 Subconvexity and heat floor | Partially solved | sub | `μ(½)≤33/200`; heat horizon `6600/9991` [L] |
| Π22, Π65 Near-line density; log-mean | Reduced | sub | eight equivalent forms; depth `O(T)`; `o(T)` open (B57) [L] |
| Π40 Strip self-improvement | Open | sub | `Θ<1⇒Θ=½` fails for shifted products [L]; implies AAL and is implied by the transfer of S3 [D] |
| Π41, Π42, Π56 Mollifier length; long-moment receivers; last-scale floor | Solved (necessary bounds); Sharpened | RH (receivers) | near-unit moments need length `exp(c log²T)`; RH ⇔ cofinal polynomial boundedness of long Möbius-mollified moments; strict slope saving ⇒ RH [L*] |
| Π46, Π55 Parity blindness; barrier blindness | No-go | — | Type I and Type II norms are parity-blind; one Euler factor plants a zero without moving the prime walk [L] |
| Π51 Vinogradov–Korobov barrier | Open | sub | every unconditional pointwise saving is VK [L] |
| Π53, Π54, Π80 Cluster wall; negative moments; short-sum barrier | Open | sub | isolated zeros at rate 2; exceptional heights past `log T` open [L] |
| Π66, Π125, Π126 Integrality; exactness on the torsion; Stepanov degrees | Solved (exact) | RH (degree bound) | exact Stepanov count over ℤ is Chebyshev's; RH ⇔ `log N(A_N)≤N+C√N log²N` [L*] |
| Π84, Π99, Π100 Parity exponent; count rigidity | Solved | ≥qRH at power saving | Liouville exponent = zero abscissa; count error `o(log n)` forces the rational primes [L] |
| Π93 Möbius as a cubic Gauss coefficient | Solved (identity); descent open | past VK | nonzero residue at `4/3`; rational transfer open [L] |
| Π94, Π128–Π130, Π137 Returns of the prime orbit | Partially solved | sub; ≥qRH in a strip | no heavy return while `log t≤(log y)^{3/2−ε}`; `√y≤K(y^{½−w(2t)}log t+log(2+t))`; a strip of depth `h` gives `log t≥c·y^{½−h}`; two-prime depth law [L*] |
| Π102 Positive Euler products with a finite top layer | Solved (countermodels) | — | integer-norm products with linear counting, continued to `Re s>1/3`, with zeros exactly `3/5±iγ` [L*] |
| Π103 Mean values of multiplicative functions | Solved (in law) | sub | Matomäki–Radziwiłł for μ at every length `h→∞`, `h≤√x`, fibre form [L*] |
| Π105, Π127 Farey, nerve, orientation cover | Solved (identity) | RH (weight `½`) | centred count `M(N)`; weight `½` ⇔ RH [L*] |
| Π112–Π114 Exceptional rank; infinite-rank Hasse–Weil; thick crude count | Sharpened | AAL; RH with attainment | a thick lag bound at every exponent ⇒ AAL; RH ⇔ attained top ∧ thick bounded lag ⇔ attained top ∧ thick `O(√X)` prime deviation; a mode accessible from infinity is eliminated on a full progression [L*] |
| Π116, Π122 Long mean values are collision counts | Solved (identity) | identity | order `X²` past the height [L] |
| Π121 Precision cost of forced vanishing | No-go | — | Rouché copies capped at `J≤e²r log N+log(1/δ)` [L] |
| Π123, Π135 The Stepanov bound is a prime count; its saving | Solved | RH; sub (VK) | `c_B(log d)=A(d)−P(d)`; RH ⇔ `P(p)≤A(p)+K` [L*]; VK saving [L] |
| Π124, Π143 Tensor powers | Solved (identity) | RH (uniformity) | constituents are Tate twists; RH ⇔ sublinear tensor exponents [L*] |
| Π133, Π134 Reciprocity of returns; label statements | Solved; Classified | method | a return at height `t` is a zero configuration near `t` imitating the pole; a uniform route from returns to ZAL refutes the return conjecture [L*] |
| Π136, Π140 Collective rank depth and return counts | Solved (beyond the depth floor) | sub | the floor grows with the number of primes [L] |
| Π138, Π139 Stepanov syzygies; orbit symmetries | Solved (classification) | identity | rational self-maps preserving the prime orbit are Laurent Adams maps [L*] |
| Π141, Π142 Gauge family; transfer to one fibre | Classified; No-go | method | big monodromy and Gaussian generic fibres; exact monodromy prices every fibre at the trivial bound [L] |
| Π144 Witt vectors and Frobenius lattices | Classified | method | no finitely generated lattice stable under three prime Frobenii [L*] |
| Π145 The fixed part of every arithmetic family | No-go (families as producers) | method | moments `≥ν{0}\|A(0)\|²(Σa_n)^{2k}` for every finite measure and amplifier; strict gain at a nontrivial torsion fibre; one-way product positivity for every `a<½`; trivial fibre of mass zero in five family classes; cover-family tensor criterion ⇔ RH [L*] |
| Π146 Frobenius at one prime; the cost of vanishing | Solved (price) | — | `x↦xⁿ` is a Frobenius at `q` iff `n=q^k`; `N(n)∈(1,2)` off prime powers; order `m` of the Fermat-quotient derivations at every prime of `S` costs `m·Σ_{p∈S}log p`; inseparability modulo `S` costs the primorial [L*] |
| Π147 The arithmetic square | Solved (construction); Classified | — | `𝒢=W(ℤ)` cofree among rings with Frobenius lifts; `frobeniusIntersection(ga,gb)=g·a/(1−(a/b)²)+g·log#(ℤ/J(a,b))`; a perfect square keeps no contact; finite fibres force contacts that are not Weil's; the carry term is `∼(2 log 2−1)N`; the `p`-derivation descends to the diagonal point exactly where the first and `p`-th ghost components agree, and evaluated jets do not measure integer order [L*] |
| Π148 Heavy returns in the two worlds; the transfer | Classified | ≥B56 (transfer) | world I: `log t≥c·y^{1−β″}`, `β″<Θ` [L*]; in every world with `½<Θ∞<1` the hypothesis of the transfer of S3 holds and its conclusion is RH, so the transfer implies `Θ<1⇒Θ=½`; its hypothesis follows from quasi-RH [D] |
| Π149 Centred Vaughan current | Solved (reduction); bound open | AAL | for `X≥t⁸` the first Gaussian prime moment minus its pole is the centred Vaughan current up to `O(1/t)`; uniform type-II block bounds [L*]; the filtered centred error is `O(h^k/t)` for cutoffs with `(UV)²t^{k+3}≤X^{1+σ−η}`; the cofactor tail beyond `W` is at most `784(k+2)!·X^{3+2k}/(UW)^{2k}` [L*]; the filtered current in the growth range is the exclusion (B145) [D] |
| Π150 The gluing index counts the zeros | Solved (identity) | identity | the first `N` graphs have gluing index `N!`; `\|log N!−N(2πN)\|≤C log N`; per graph the count misses only the increments of `S` [L*]; at every height the gluing count `G(T)`, the conditions of each graph spread evenly over its window, satisfies `G(T)−N(T)+S(T)→½log 2π−7/8`, and `G(T)−N(T)` leaves every bounded neighbourhood of that constant at arbitrarily large heights [S] |
| Π152 Kronecker over ℤ at infinite rank | Classified | — | integral trace-class modules with a chain condition carry only Tate twists; without it a module has trace `1` at every Frobenius and a mode at `5/4`; eventually integral traces of modes in the open strip force zero amplitudes [L*]; `Λ` and the Mertens function are not traces of any order [L] |

## Γ — selection, reflection, position

| Wall | Status | Strength | Content |
|---|---|---|---|
| Γ1 Self-return | Open | RH | uniform head-target density on every right-strip disc ⇒ RH; RH ⇒ strong recurrence [L*] |
| Γ15, Γ33, Γ35, Γ167 Rigidity of ζ | Solved (classification) | method | Hamburger; degree-one classification; Beurling systems with `L¹`/`L²` FE defect are the rational primes [L*]/[L] |
| Γ23 Weil cone uniqueness | Solved | — | full positivity forces Λ; cone nonemptiness is RH [L] |
| Γ24, Γ62, Γ95 Mayer reflection; Hecke dispersion; Krein flux | Sharpened | RH | exact identities; the signs are RH [L] |
| Γ42 Legendre reality | Solved (identity) | RH | RH ⇔ `J(ρ)∈ℝ` [L] |
| Γ49 Exceptional values | Partially solved | indep. | nonrepelling values: dense `G_δ` of dimension zero; `0∉E` open [L] |
| Γ61 Inner factor | Solved (identity) | RH | `I≥0`; RH ⇔ `I=0` at one point [L] |
| Γ67, Γ183 Abscissa split and atoms | Solved (identity) | identity | RH ⇔ ZAL ∧ B13 ∧ Landing; a failure of the abscissa law fails exactly one of B13, Landing, DH [L*] |
| Γ68, Γ69 AAL and its producers | Open; Partially solved | sub | thick lag bounds, Toeplitz positivity of a lag kernel, log-dense integer lags, Bohr-dense floors give AAL [L*]; each retains its source bound |
| Γ73, Γ145 One-off countermodels; firewall | No-go (positive data) | — | integer-norm Euler products with linear counting carry finite top layers and approaching remainders [L*] |
| Γ86, Γ121, Γ122 Modular horizon; horocycle and ringdown rates | Solved (identity) | RH (rate) | RH ⇔ every compact pulse decays at `e^{−(¼−ε)τ}`; rate ⇔ zero-free region [L*]/[L] |
| Γ89, Γ148, Γ157 Physical positivity; modular conjugation; half-sided inclusions | No-go | — | blind, central, or without eigenvalues [L] |
| Γ96, Γ125, Γ154 Count law of curves; count door | Solved (curves); Sharpened (ℤ) | RH | RH ⇔ every effective prime class carries an `ℕ`-count with Tate limit `δ_p(1,1)`; the same on power-saving gap sets [L*] |
| Γ97, Γ131, Γ162 Integer probes; Tate limit of a count | Sharpened | RH | a count within bounded distance of the probes gives RH; under RH a count within distance one exists [L*]; the probes are not integer-valued [L] |
| Γ119, Γ191 Random models | Classified | method | Haar-a.e. Euler products are zero-free right of `½`; in-law statements are blind to the atoms [L]/[D] |
| Γ132 Narain remainder | Sharpened | RH (rate `¾`) | VK saving; exponents past `¾` impossible [L] |
| Γ134, Γ171 Cavity receivers | Solved (receiver) | RH (rate) | one cavity function of Hecke forms: RH ⇔ energy rate `y^{¾−ε}`; strip ⇔ rate `y^α`, `α>½` [L*] |
| Γ137, Γ161, Γ181 Positive annihilators | No-go (positivity as exclusion) | — | price finite zero sets, never exclude them [L] |
| Γ140, Γ155, Γ156 Two-scale law; linear hierarchy; heat family | No-go (scale-separated and family-uniform inputs) | — | landing is a tail law undecided below every height; linear AAL along the heat flow is RH; heat finiteness does not pass to `t=0` [L*] |
| Γ141, Γ185 The FE admits finite layers and approaching remainders | No-go | method | an FE model of exponential type with approaching quartets violates landing; so does an integer-norm Euler product [L*] |
| Γ142, Γ143 AAL is transport; free AAL | Classified | sub | AAL ⇔ zero transport ⇔ tail transport; free for recurrent classes [L] |
| Γ150–Γ153, Γ158, Γ168 Half-products; point count; fibres | Solved (identity) | identity | archimedean kernel `=2π√(mn)G_{1/2}`; `p`-kernel = tree Green function at the Ramanujan point [L*] |
| Γ160, Γ166 Finite-rank Euler + FE; Dirichlet selector | Solved (calibration) | — | finite Euler product with FE is pure; only `τ=0` has a Dirichlet series [L] |
| Γ164, Γ165, Γ178, Γ179 Sampling sets; metric recurrence; almost all primes; smooth degrees | Solved (receivers); No-go (without attainment) | AAL | unattained tops pass off density-zero sets and at very smooth degrees [L] |
| Γ169, Γ170, Γ180, Γ187, Γ188 Hyperbolic carriers; locked dampings; mass obstruction; Gram coupling; prime unit | No-go / Solved (finite limits) | — | no one-place carrier; atoms lock to the discriminant; Gram coupling leaves an exact defect [L] |
| Γ172 Krein forms of the cavity | Classified | RH | RH ⇔ every tent reflection Krein form has negative index `0` [L*] |
| Γ173–Γ177 The prime current in world I | Solved (passage laws) | sub | corrected current = top mode × finite wave; a dominant ordinate of the top layer, in particular a single one, ⇒ divergence [L*]/[L] |
| Γ182 The landing law | Sharpened; Settled (method question) | sub | equivalent forms for ζ (Hadamard threshold, Krein–Langer index, heat counts, …); fails for the FE alone and the Euler product alone [L*]; open for ζ as an atom |
| Γ184 The Deuring–Heilbronn sector | Classified (models); Open for ζ | sub | classical repulsion for real zeros of quadratic `L(s,χ)`, uniform constant; `(1−Re ρ₁)log(\|Im ρ₁\|\|Im ρ₂\|)>1/58` for ζ; graded repulsion refuted on integer-norm products [L*] |
| Γ189 The adelic degree configuration | Solved | producer | full degrees as distinct points of a discrete adelic quotient with commuting prime operators, `A_p1=p+1` [L] |
| Γ190 Infinite power sums | Solved | method | a maximal term is detected within `64M` powers [L] |
| Γ192 Two worlds | Solved (identity) | identity | `Θ<1⇔Θ∞<1`; ¬AAL ⇒ `Θ<1`; `¬(Θ<1)⇔Θ=Θ∞=1∧AAL` [L*]; world I has a Mertens power saving [L*] |
| Γ193 Boundary and polynomial damping filters | Classified | AAL (the gap) | in world I filters grow when `dκ<a(β−σ)/2`, at every damping speed and at polynomial damping; VK bound `C h^d t^N exp(a(1−σ)t/2−a t·vk/4)`; decay under critical contraction; the ranges are separated by `a(1−β)/2` [L*] |
| Γ194 Gauge deformations are isozeric | Classified | method | a fibre with nonzero analytic residue at `1` is `ζ·exp(H)` left of `1`; quadratic rigidity; Liouville-type fibres continue to `exp(J)/ζ`; residue Hessian positive with kernel the zero phase speeds; damped Liouville phases: residue of order `t²`, a non-polynomial rescaled limit with a moving branch point of exponent `iπ`, no joint analytic regularization at `(0,1)` [L*] |
| Γ195 Index law and index-one limits | Solved (law); Sharpened | RH | a defect of degree `κ` has at most `κ` exceptional points; the bound passes to limits; RH ⇔ ξ is a limit of index-one functions; `Λ(2s)Y^s+Λ(2s−1)Y^{1−s}` pure off the real axis, exceptional zero exactly above `Y=4πe^{−γ}`; the line law holds over impure fixed parts [L*] |
| Γ196 One glued carrier object for the diagonal | No-go | — | every adelic-invariant kernel with a torus-orbit functional has a constant degree diagonal and drifts to `−∞`; the critical product erases contacts and diverges over the torus; bounded prime words vanish where Weil's off-diagonal is positive; discriminant jump `−2‖g‖²log p` [L*] |
| Γ197 Weighted adelic Green kernel | Classified | — | summably weighted: invariant, positive definite precision, positive covariance; unweighted: collapses; neither signs Weil's form [L*]/[L]; the mixed hyperbolic kernel is the limit of finite Dirichlet sections and is bounded off the diagonal by a strictly tempered barrier uniformly in the archimedean distance; it is invariant under adelic isometries; the barrier profile is summable over the rational torus [L*] |
| Γ198 The diagonal is a comb finite part | Solved (identity) | RH (sign) | jets on the comb `e^{ℤ/N}` minus mass × `log(N/2π)` tend to minus Weil's archimedean form; no function of the degree point is the counterterm on two combs; on the carrier Weil's form is a density at every frequency; the pairing of the degree points has the limit `2d₁d₂−Z(f)`, `Z(f)≥−D(f)` with `D(f)≥0` a sum over the off-line zeros, RH ⇔ `D≡0`; `D·D≤2d₁d₂` on packets of length `≤1/130` [L*] |
| Γ199 The archimedean fibre of the square | Classified | — | weight lines `χ_z`; transposition `z↦1−z`; traces `1+1/(n²−1)` and `m/(1−(m/n)²)` on the jets; pole plane at weights `0,1`; no Verschiebung carries the off-diagonal [L*] |
| Γ200 Section counts and finite type | Classified | RH (Bézout) | a section count with Riemann–Roch and Bézout exists iff the Hodge index holds; over ℤ ⇔ RH; no finite-type object carries the contacts; the tower of lines carries them with an exact count [L*] |
| Γ201 Halving descent and Shimura zeros | Sharpened | RH (rate) | for one Hecke eigenform RH ⇔ sharp rate ∧ no nonhalving Shimura zero; a halving pair blinds every Hecke form [L*]; any halving pair forces `Θ≥2/3` [L] |
| Γ202 The scattering tower | Solved (identity) | identity | Weil's functional on `C²_c` packets is the limit of Robin-normalized Maass–Selberg diagonals with one scalar counterterm [L*] |
| Γ203 Separation by the height | Solved (receiver) | RH | ordinate injective on the zeros ⇔ `\|c_p\|≤K` at every prime ⇔ RH; fibre spread `≤2σ` ⇔ width `≤σ`; coefficient gaps do not occur at three explicit critical ordinates [L*] |
| Γ204 Positive translation repair | Classified | — | a Laplace-positive function with positive tails becomes pointwise nonnegative under a positive-root polynomial average of translations, keeping a prescribed mode [L*]: pointwise positivity locates nothing |
| Γ205 No periodicity in height | Solved (no-go) | method | no vertical progression `ρ+ikT` consists of zeros of ξ, at any real part; `Σ_n\|ζ(ρ+inT)/(ρ+inT)\|` diverges in the strip, the squares are summable; no two-sided sequence of zeros lies within an `ℓ²` perturbation of a progression; the periodicity dichotomy for ζ is RH [L*]; the same for each half progression `n≥0` [S] |
| Γ206 Graded recurrence | Solved (receiver) | ≥qRH (the return count) | for `½≤σ≤5/6`, `c>(30/13)(1−σ)`: fewer than `T^c` one-separated returns to a small disc at a zero right of `σ`; `T^c` returns at arbitrarily large `T` on every small disc exclude the zero [L*] |
| Γ207 Finite-stratum laws on the Jensen and cosine families | Solved (receivers) | RH; RH given ZAL | at each degree finitely many shifted Jensen polynomials fail real-rootedness and the exclusion of finite nonempty strata is RH; on the cosine family the same exclusion gives RH ⇔ ZAL [L*] |

## Scoped no-gos and surviving replacements

| Boundary | Exact scope and survivor |
|---|---|
| Families as producers | fixed-part theorem; isozeric deformations (Π145, Γ194). Survivor: a statement at the fibre itself |
| One glued invariant carrier | refuted (Γ196). Survivors: comb finite parts (Γ198), weighted covariance (Γ197), the clock (Σ150), the scattering tower (Γ202) |
| Finite-type objects carrying the contacts | excluded (Π147, Γ200). Survivor: the tower of lines with an exact count; Bézout open |
| Frobenius for a window; cheap vanishing | one prime per power map; cost `m·θ(S)` (Π146). Survivor: the cofree square with exact contacts |
| A duality between contacts and jets | none (Γ199). Survivor: the compensation `Σ_{m\|n}Λ(n/m)=log n` against the comb counterterm |
| Integral or trace-class Frobenius modules | Tate twists only (Π152, Π144). Survivor: the flow, where growth reads weights of locally finite modules |
| The line law of a family as purity of its fixed part | holds over impure fixed parts (Γ195). Survivor: an independent index-one family converging to ξ (B146) |
| Separation by absolute value | excluded for ζ (Γ203). Survivor: the ordinate as separating invariant, a receiver |
| The transfer of candidate S3 as a method question | implies strip self-improvement (Π148). Survivor: the heavy-return laws as structure of the two worlds |
| The clock energy as a producer | ordered approximation of `W` (Σ150) |
| Fixed-length windows uniform over configurations | low off-line pair (Σ149). Survivors: logarithmic windows (Σ146, Σ148); separated deep ordinates |
| Density-zero exceptions, very smooth degrees, finitely many Frobenii without attainment | unattained tops pass (Γ164, Γ178, Γ179). Survivor: power-thin exceptions per window (Σ148) |
| Scale-separated and family-uniform inputs | decide no atom (Γ140, Γ156). Survivor: inputs that see the Dirichlet series at all scales |
| Landing or repulsion from one structure | FE-only and Euler-only models (Γ185, Γ184). Survivor: joint FE–Euler inputs |
| VK or Euler-region bounds as exclusion of a finite layer | ranges separated by `a(1−β)/2` (Γ193). Survivor: an inequality not implied by the explicit formula |
| Exact Frobenius over ℤ; integrality at returns; Rouché copies | torsion only; Chebyshev; precision cap (Π121, Π125, Π126) |
| Positivity, Euler products, integrality, counting, annihilators as an atom | one-offs and annihilators (Γ73, Γ137, Π102) |
| Internal, vacuum-fixing and half-sided modular realizations | excluded (Γ148, Γ157) |
| Hyperbolic one-place carriers; locked atomic dampings; scalar descent under the prime unit | excluded (Γ169, Γ170, Γ188) |
| Markov, Perron, size-only payment, floor tower, universal multipliers, fixed theta heads | refuted or bounded (Σ42, Σ53, Σ57, Σ27, Σ140, Σ98) |
| One Hecke eigenform without side condition | halving pairs and Shimura zeros (Γ201). Survivor: cavity functions; the Shimura condition |

## Bridges

| Bridge | Anchor |
|---|---|
| One inequality per prime: Weil test = Stepanov count = count door = sign-free trace, on logarithmic windows off power-thin exceptions | SOSZ [L*] |
| Window sign ⇔ verification height, up to constants | VHR, WVL [L*]/[L] |
| Critical curve: `R_c=R_polar=R_halfline≤W₀`; three-way classification | AHD, CACT [L*] |
| RH ⇔ ZAL ∧ B13 ∧ Landing; two worlds; quasi-RH is a tail law | ZCG, ELT [L*] |
| World I ⇒ Mertens power saving, late heavy returns, filters at every speed | ELT, TTPO [L*] |
| Unbounded windows ⇒ AAL; attained top + thick crude count ⇒ RH | SOSZ, IRP [L*] |
| Fixed part ⇔ no family producer; tensor exponents with the trace of ζ ⇔ RH | AWT [L*] |
| Rigidity: Hamburger, FE-defect isolation, count distance, isozeric deformations | HTGeometry, EFT, SPAL, AWT [L*]/[L] |
| Off-diagonal Weil = contacts + jets = pole − `ℍ³` Green − tree Green | AGZ, SOSZ, HAT [L*] |
| Diagonal = comb finite part = limit of the scattering tower = limit of the clock energies | AGZ, HAT [L*] |
| Section count with Riemann–Roch and Bézout ⇔ Hodge index ⇔ RH | ArithmeticCorrespondencePositivity, AGZ [L*] |
| Gluing index `N!` ↔ zero count at height `2πN` | AGZ [L*] |
| Index law; index-one limits; Eisenstein line law | IRP, RHTower [L*] |
| Ordinate injectivity ⇔ bounded two-sided prime traces | SignFreePurityMechanisms [L*] |
| Cavity energy rate ⇔ zero-free region; reflection Krein index counts off-line zeros; one eigenform ⇔ rate ∧ Shimura | AHMH [L*] |
| Heavy return at height `t` ⇔ zeros near `t` imitate the pole | TTPO [L*] |
| Mertens level = producer rate = Farey = nerve = orientation cover | AAD, RIAC, HAT [L*]/[L] |
| Census: covariance ceiling ⇔ line density; exchange rate | SquareRootThreshold, P [L*] |

## Strength of the open walls

- **RH:** Σ1, Σ2, Σ3a, Σ6 (all ranks), Σ20, Σ49, Σ56, Σ66, Σ73–Σ80, Σ113, Σ129 (thresholds `=⊤`), Σ130, Σ133, Σ137, Σ138, Σ141, Σ144, Σ145, Σ146 (the bound), Σ148, Σ150 (sign), Σ151, Π2, Π42, Π123, Π124, Π126, Π127, Π143, Γ1, Γ24, Γ62, Γ95, Γ97, Γ121, Γ122, Γ131, Γ134, Γ154, Γ171, Γ172, Γ195, Γ198 (sign), Γ200 (Bézout), Γ201 (rate), Γ203, Γ207 (Jensen law).
- **≥qRH:** Σ4, Σ28, ZAL, `N_d` bounded, any interior width value (Σ137, Σ138, Σ144, Σ148 at `p^σ`, `σ<½`), Π3 (polynomial rate), Γ121/Γ122/Γ132 (interior exponents), Π137 (strip rung), Γ206 (the return count).
- **AAL:** Π114 (thick crude count at every exponent), Γ164, Γ165, Σ147, Π149 and Γ193 (the growth-range bound), Π148 (the transfer, with strength ≥B56).
- **sub:** Σ27, Σ47, Σ82, Σ116, Σ117, Π7, Π12, Π22, Π40, Π51, Π53, Π54, Π65, Π80, Π94, Π103, Π136, Π140, Π151, Γ68, Γ182 (landing as an atom), Γ184 (DH for ζ), B13.
- **method / producer / indep.:** Σ135 and Σ139 (B104), Σ146 and Σ149 (B143, B144), Π141, Π142, Π144, Π145, Π146, Π147, Π152, Γ49, Γ189, Γ194, Γ196, Γ197, Γ199, Γ202, Γ204, Γ205.
