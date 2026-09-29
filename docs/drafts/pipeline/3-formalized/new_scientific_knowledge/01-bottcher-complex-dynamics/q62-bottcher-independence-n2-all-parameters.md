# Q6.2 n=2 -- all nonexceptional quadratic Bottcher independence

- **ID:** q62-bottcher-independence-n2-all-parameters
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / NOVEL+SIGNIFICANT bridge theorem
- **Source:** Nguyen arXiv:1310.2329, Question 6.2

## Statement

Let

`f_c(z)=z^2+c`.

For each `c`, let `psi_c(t)` be Nguyen's local conjugacy at infinity,

`psi_c(t^2)=f_c(psi_c(t))`, `psi_c(t)=t+O(t^-1)`,

and let `phi_c=psi_c^-1` be the Bottcher coordinate:

`phi_c(f_c(z))=phi_c(z)^2`, `phi_c(z)/z -> 1`.

If `c1 != c2` and `c1,c2 notin {0,-2}`, then `phi_c1(z)` and
`phi_c2(z)` are algebraically independent over `C(z)`. Hence they are
algebraically independent over `Qbar(c1,c2,z)`.

This proves the quadratic `n=2` nonexceptional case of Nguyen Question 6.2.

## Anti-Theatre Gate

No finite computation can promote this claim. Finite Laurent truncations are
nonidentifying: for every fixed truncation depth, triangular correction terms in
`phi_c1-z` can cancel the observed coefficients off the diagonal `c1=c2`.

The proof is therefore global. In connected cases, an algebraic relation would
force analytic continuation through a forbidden Julia-boundary point. In
disconnected cases, an algebraic relation is incompatible with exact dyadic
monodromy around Cantor cylinders.

## Proof

Assume a nonzero polynomial relation

`P(z,phi_c1(z),phi_c2(z))=0`

holds for the common germ near infinity. We split by the Mandelbrot placement of
the two parameters.

### 1. Connected/connected

Source card: `q62-bottcher-independence-natural-boundary.md`.

Assume `c1,c2 in M \ {0,-2}`. Then each `K_ci` is connected and the normalized
Bottcher coordinate is single-valued on `Omega_ci=C\K_ci`.

The crossing lemma gives, after possibly swapping indices,

`J_c1 cap Omega_c2 != empty`.

Indeed, if `J_c1 subset K_c2`, fullness of `K_c2` forces `K_c1 subset K_c2`.
Both filled Julia sets have logarithmic capacity `1`. A strict containment of
connected full compacta of the same capacity is impossible by the standard
energy-variation argument; equality of the filled Julia sets forces `c1=c2`
from uniqueness of the normalized exterior Riemann map and the Laurent
coefficient `c/(2z)`. This contradicts `c1 != c2`.

Choose a crossing point `z0 in J_c1 cap Omega_c2` outside the locally discrete
coefficient-pole and discriminant bad locus for the algebraic equation in
`phi_c1`. Since `phi_c2` is analytic near `z0`, the algebraic implicit-function
theorem gives an analytic continuation of `phi_c1` through `z0`.

But if `phi_c1` extends analytically through any point of `J_c1`, then
`J_c1` has a relatively open piece contained in the smooth real-analytic curve
`|Phi|=1`. Eremenko--van Strien's smooth-piece rigidity then forces the whole
Julia set to lie in a circle, which for `z^2+c` gives only the exceptional
parameters `c=0` or `c=-2`. Contradiction.

Thus no relation exists in the connected/connected case.

### 2. Disconnected/disconnected

Assume `c1,c2 notin M`. Each `K_ci=J_ci` is a Cantor compactum of capacity `1`.

The capacity-support lemma gives `K_c1 notsubset K_c2`. If containment held,
then the equilibrium measure of `K_c1` would also minimize logarithmic energy on
`K_c2`, because both capacities are `1`. By uniqueness of the equilibrium
measure, `mu_c1=mu_c2`; since the equilibrium measures have full support
`K_ci`, this gives `K_c1=K_c2`. The normalized exterior map then recovers
`c` from the coefficient `c/(2z)`, so `c1=c2`, contradiction.

Choose `z0 in K_c1\K_c2` and a disk `D subset Omega_c2` around `z0`. Since
`K_c1` is a hyperbolic Cantor repeller, depth-`n` symbolic cylinders shrink to
points; for arbitrarily large `n`, choose a depth-`n` cylinder

`C_w subset K_c1 cap D`.

The exact monodromy theorem
`bottcher-exact-pruefer-monodromy.md` gives a based loop `gamma` in
`D\K_c1` whose continuation sends

`phi_c1 -> exp(2*pi*i/2^n) phi_c1`.

The same loop lies in the simply connected disk `D subset Omega_c2`; equivalently
its winding-number integral against `mu_c2` is zero. Therefore it fixes
`phi_c2`.

The loop is reachable from the infinity germ inside
`C\(K_c1 union K_c2)`: the union of two compact zero-dimensional plane sets is
zero-dimensional and does not separate the plane, so its complement is connected
and hence path-connected.

For `2^n > deg_Y P`, analytic continuation around the iterates of `gamma` gives
more roots in the `Y`-variable than the degree of `P`. The
one-coordinate monodromy obstruction
`../../3-formalized/not_new_scientific_knowledge/unbounded-one-coordinate-monodromy-obstruction.md` then forces algebraic
independence, using the transcendence of the fixed coordinate `phi_c2`.

Thus no relation exists in the disconnected/disconnected case.

### 3. Mixed connected/disconnected

Assume `a in M \ {0,-2}` and `b notin M`.

First `K_b notsubset K_a`. If containment held, the same capacity argument would
give `mu_b=mu_a`. For a polynomial, the equilibrium measure of the filled Julia
set is the Brolin-Lyubich measure and has support `J_c`. Thus

`K_b = supp(mu_b) = supp(mu_a) = J_a`.

This is impossible because `K_b` is a Cantor set while `J_a` is connected.

Choose `z0 in K_b\K_a` and a disk `D subset Omega_a`. For arbitrarily large `n`,
choose a depth-`n` cylinder `C_w subset K_b cap D`. The exact monodromy theorem
gives a loop in `D\K_b` sending

`phi_b -> exp(2*pi*i/2^n) phi_b`.

The connected coordinate `phi_a` is single-valued on all of `Omega_a`, so the
same loop fixes `phi_a`. The zero-dimensional non-cutting gate gives a path from
the infinity germ to the loop basepoint in `Omega_a cap Omega_b`.

Taking `2^n` larger than the polynomial degree and applying
`../../3-formalized/not_new_scientific_knowledge/unbounded-one-coordinate-monodromy-obstruction.md` gives algebraic
independence.

This closes the mixed case.

## Exact Monodromy Input

For `c notin M`, the scalar monodromy image of `phi_c` on `Omega_c=C\K_c` is
exactly

`mu_{2^infty} = { exp(2*pi*i*r) : r in Z[1/2] }`,

and the period group of `d log phi_c` is exactly `2*pi*i Z[1/2]`.

The proof is potential-theoretic:

`d log phi_c = int dz/(z-zeta) dmu_c(zeta)`.

For a loop `gamma`,

`int_gamma d log phi_c = 2*pi*i int_K Ind(gamma,zeta) dmu_c(zeta)`.

On the quadratic shift locus, `K_c` is conjugate to the one-sided full two-shift
and `mu_c` is the fair Bernoulli measure. A loop around a depth-`n` clopen
cylinder therefore has period `2*pi*i/2^n`, while every loop has dyadic period
because its index function is locally constant on the Cantor set and hence
constant on sufficiently deep cylinders.

This is topological period monodromy around removed Julia cylinders. It is not
the retired local-branch-point argument around escaping precritical points.

## Source Boundary

- Nguyen defines the local conjugacy `psi_f` and asks for algebraic-independence
  criteria for the Bottcher coordinate `phi_f=psi_f^-1` in Question 6.2.
- Eremenko--van Strien supplies the smooth-piece Julia rigidity used in the
  connected/connected case.
- De Marco's shift-locus notes identify disconnected quadratic Julia dynamics
  with the one-sided full shift.
- Brolin-Lyubich theory identifies the polynomial equilibrium measure with
  harmonic/maximal-entropy measure; hence depth-`n` shift cylinders have mass
  `2^-n`.
- The planar path gate uses the classical Mazurkiewicz no-cut theorem:
  zero-dimensional subsets do not separate plane regions. This keeps the
  component-loop basepoint reachable from the infinity germ.
- Schmidt's Compositio paper studies monodromy in the disconnected case and
  independently supports high-order root-of-unity continuation. It does not
  state the two-parameter Nguyen-Q6.2 function-field independence theorem.
- Targeted searches found Nguyen's question and adjacent value/orbit literature,
  but no printed theorem settling this quadratic all-parameter case.

## Novelty and Significance

Grade: **NOVEL+SIGNIFICANT, bridge theorem.**

Novelty is the assembled cross-corpus theorem: capacity separation, algebraic
continuation, Eremenko--van Strien rigidity, and exact Cantor-cylinder monodromy
combine to settle a named open inverse-Bottcher independence problem in the
quadratic `n=2` nonexceptional case.

Significance is not that the ingredients are individually exotic. The significant
point is structural: for a hypertranscendence-adjacent family, finite algebraic
relations fail for two different global reasons, natural-boundary rigidity in the
connected case and infinite dyadic continuation monodromy in the disconnected
case. This is a concrete theorem about constraint-side hypertranscendence rather
than another finite-jet or numerical artefact.

## Gates

- [x] 0 -> 1 in-progress: case split and failed finite/computational routes
  isolated.
- [x] 1 -> 2 fully-proven: connected proof, exact disconnected monodromy theorem,
  path-placement gate, and algebraic obstruction assembled.
- [ ] 2 -> 3 formalized: Lean formalization not started.
- [ ] 3 -> 4 publication-ready: standalone preprint not written.

## Independent proof verification — 2026-06-24 (Turing): SOUND, no gap found

Hard-checked the flagship proof (corpus's best NOVEL+SIGNIFICANT bridge). All three cases close; verified
the subtle core independently:
- **Crossing lemma, "equal-capacity containment ⟹ equal set"** (used in all cases): sound via the strong
  minimum principle. For K1⊂K2 full continua of equal capacity 1, u = g_{K1} − g_{K2} ≥ 0 is harmonic on
  the exterior Ω_{K2}, and →0 at ∞ (equal capacity ⟹ matching log-pole constants). A non-negative harmonic
  function attaining its infimum 0 at the interior point ∞ (on the sphere) is ≡0, so g_{K1}=g_{K2} ⟹ K1=K2
  ⟹ c1=c2 (filled Julia set determines the quadratic parameter via the c/(2z) Laurent coefficient). ✓
- **Connected case:** φ_c1 continuing analytically through z0∈J_c1 makes {|φ_c1|=1}=J_c1 a real-analytic arc
  near z0 ⟹ Eremenko–van Strien smooth-piece rigidity ⟹ J in line/circle ⟹ c∈{0,−2}, contradiction. ✓
- **Disconnected/mixed:** exact dyadic monodromy φ→e^{2πi/2^n}φ around depth-n cylinders (period
  2πi·μ_c(cyl)=2πi/2^n, Brolin–Lyubich = fair Bernoulli) gives 2^n distinct roots e^{2πik/2^n}φ_c1 (distinct
  since |φ_c1|>1≠0) of P(z,Y,φ_c2); for 2^n>deg_Y P, too many roots ⟹ deg_Y P=0 ⟹ relation in φ_c2 alone,
  contradicting φ_c2 transcendental. Loop reachable from ∞ germ (Mazurkiewicz: zero-dim sets don't
  separate). ✓

No gap found in the assembly or the capacity core. Caveat: the cited sub-lemmas (Eremenko–van Strien exact
statement; the sibling exact-monodromy and one-coordinate-obstruction cards) are trusted by citation, not
re-derived here; full certification would chase those. The logical structure is sound and the theorem holds.

## Lean formalization progress — 2026-09-29

- Connected/connected: `Bottcher.noRelation_phiMero_of_mem_mandelbrot`
  (`Bottcher/Q62BothConnectedIndependence.lean`), unconditional. The natural-boundary tail is now the
  reusable lemma `false_of_relation_on_ball_component`.
- Mixed: `Bottcher.noRelation_phiMero_of_mem_mandelbrot_of_disconnected` and
  `Bottcher.noRelation_phiMero_of_disconnected_of_mem_mandelbrot`
  (`Bottcher/Q62MixedIndependence.lean`), unconditional, axioms `[propext, Classical.choice,
  Quot.sound]`. Route differs from the paper: the natural boundary of the connected coordinate does
  the work; the disconnected coordinate is carried by relation propagation along its local branches
  (`Bottcher/BottcherLocalBranch.lean`, `relBranchAt_of_preconnected`), so no cylinder loop and no
  Mazurkiewicz gate is needed. Orientation: `0 ∈ K_a ∖ K_b`.
- Disconnected/disconnected (in progress). Route: after propagating the relation to a disc around a
  point of `K_{c₁} ∖ K_{c₂}`, a root branch `w` of the relation is a single-valued branch of
  `φ_{c₁}` on a component `V` of `disc ∖ K_{c₁}`; a level piece `E` of `c₁` (small, with `E ∖ K`
  connected) lies in the disc and meets `V`, so `|w| = C e^{G}` on `E ∖ K`; the Green-modulus minimum
  principle (`no_green_modulus_continuation_dense`) and `int K = ∅` give the contradiction.
  Cantor input to be built for all `c ∉ M` (corpus had it only for `‖c‖ ≥ 4`):
  1. `D = {G < s}` (`G(0) < s < 2G(0)`) and `{0 < G < s}` connected (collar = tower-section image);
  2. `f⁻¹(D) = E ⊔ −E` with `f : E → D` biholomorphic (winding of `f∘γ` about `c` for a `C¹` path
     `z ⇝ −z` would be odd, but loops in `D` have winding `0` about `c`);
  3. Carathéodory density on the bounded `D`: each inverse branch maps `D` into the compact
     `{G ≤ s/2}`, so it contracts the density by `1 + ε` (Earle–Hamilton trick); depth-`n` pieces
     have derivative `O((1+ε)^{-n})` on compacta, and by a finite chain argument diameter `→ 0`;
  4. consequences: `int K = ∅`, `K` perfect, small pieces `E ∋ q` with `E ∖ K` connected.

## Lean formalization — complete (2026-09-29)

Main theorem, unconditional, axioms `[propext, Classical.choice, Quot.sound]`:

`Bottcher.noRelation_phiMero_of_ne` (`Bottcher/Q62DisconnectedIndependence.lean`): for any open
preconnected infinite `U` inside both escape regions, `c₁ ≠ c₂`, `c₁, c₂ ∉ {0, -2}`,
`NoRelation (RatFunc ℂ) (phiMero c₁) (phiMero c₂)` — no nonzero `P ∈ ℂ(z)[W][Y]` has
`P(φ_{c₁}, φ_{c₂}) = 0` in the meromorphic germ field (algebraic independence over `ℂ(z)`).

| Paper step | Lean |
|---|---|
| connected/connected | `noRelation_phiMero_of_mem_mandelbrot` (`Q62BothConnectedIndependence`), tail `false_of_relation_on_ball_component` |
| mixed (both orientations) | `noRelation_phiMero_of_mem_mandelbrot_of_disconnected`, `noRelation_phiMero_of_disconnected_of_mem_mandelbrot` (`Q62MixedIndependence`) |
| transcendence of `φ_c`, `c ∉ M`, any far domain | `phiMero_transcendental_of_disconnected` (`Q62MixedIndependence`) |
| relation propagation along local branches | `relBranchAt_of_preconnected`, `relBranchPairAt_of_preconnected` (`BottcherLocalBranch`) |
| branch modulus `‖g‖ = C e^{G}`, zeros | `IsBasinBranch.exists_norm_eq_mul_exp`, `IsBasinBranch.ne_zero_of_ne_zero` (`BottcherLocalBranch`) |
| `{0 < G_c < σ}` connected (`σ > G_c(0)`) | `isPreconnected_green_band` (`DisconnectedInverseBranch`) |
| inverse branches of `f_c` over `{G_c < 3G_c(0)/2}` | `exists_inverse_branch` (`DisconnectedInverseBranch`), via `false_of_path_neg_below` and `C¹` planar paths (`PlanarSmoothPaths`) |
| strict contraction of inverse branches | `exists_strict_caraDensity_contraction` (`CaratheodoryDensity`) |
| Cantor structure for all `c ∉ M` | `exists_small_piece`, `interior_filledJulia_eq_empty_of_not_mem_mandelbrot`, `filledJulia_no_isolated_of_not_mem_mandelbrot`, `isTotallyDisconnected_filledJulia_of_not_mem_mandelbrot` (`DisconnectedCantorPieces`) |
| disconnected/disconnected | `hno_of_disconnected_of_mem_filledJulia_not_mem`, `noRelation_phiMero_of_disconnected` (`Q62DisconnectedIndependence`) |

Route notes. The Lean proof differs from the paper in three places, all simplifications of the
argument rather than of the statement: (1) Step 1 needs no capacity theory — the symmetric
difference `K_{c₁} Δ K_{c₂} ≠ ∅` comes from `c_eq_of_filledJulia_eq'`, and the crossing point from
the common far-field component; (2) the mixed case runs the natural boundary of the connected
coordinate, carrying the disconnected one by branch propagation, so no Cantor cylinder loop is
needed there; (3) the disconnected case replaces the dyadic cylinder monodromy and the Mazurkiewicz
gate by the Green-modulus minimum principle on a small Cantor piece `E` with `E ∖ K` connected.
The Cantor structure of `K_c` for every `c ∉ M` (Fatou's theorem) is proved from scratch: inverse
branches over a Green sublevel set exist because loops below the critical value have winding `0`
about `c`, and they contract the Carathéodory density of that set by a uniform factor.

- [x] 2 -> 3 formalized.
