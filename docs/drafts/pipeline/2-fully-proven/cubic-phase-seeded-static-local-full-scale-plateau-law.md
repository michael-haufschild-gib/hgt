# Cubic-phase seeds give full-scale static-local complexity plateaux

- **ID:** `cubic-phase-seeded-static-local-full-scale-plateau-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / FULL-SCALE STATIC-LOCAL PLATEAU
- **Parents:** `stabilizer-seeded-static-local-double-exponential-plateau-law.md`,
  `fixed-shell-angular-dephasing-static-local-plateau-law.md`,
  `traceless-local-two-query-haar-separation-law.md`
- **Status:** `[PAPER-PROVED] [FRONTIER ADVANCE] [LEAN DEFERRED DURING REFACTOR]`
- **Statement:** An exactly and polynomially preparable cubic-phase seed has spectral collision
  `O(1/D)` with failure `O(1/D)` against every eigenbasis; one ordinary fixed-strength static-local
  Hamiltonian therefore produces a near-maximal continuous complexity plateau lasting
  `2^{Theta(D)}`, later recurrence, and permanent two-query separation from Haar randomness with
  probability `1-O(1/D)`.

## Public sentence

For every `n`, one cubic-phase state can be fixed in advance and prepared by a polynomial circuit.
After one ordinary nearest-neighbour Hamiltonian is sampled and then held fixed forever, the state becomes hard
to reproduce to depth `Theta(2^n/log n)` continuously for `2^{Theta(2^n)}` time, later returns near
its easy starting state, and remains distinguishable from Haar randomness by one fixed two-copy
local experiment throughout.  No noise, drive, Haar eigenbasis, random time, or varying interaction
strength is used.

This closes the probability--height tradeoff in the stabilizer parent theorem.  It does **not**
quantify the first plateau time or prove the Brown--Susskind linear ramp.

## Setup

Put `D=2^n`.  Let `omega=exp(2 pi i/8)`.  Write `P_3(n)` for the free `Z/8Z`-module of square-free
polynomials

\[
 h(x_1,\ldots,x_n)=\sum_{S\subseteq[n],\ |S|\le3}c_S\prod_{i\in S}x_i,
 \qquad c_S\in\mathbb Z/8\mathbb Z.                              \tag{1}
\]

Sample `h` uniformly and define

\[
 \chi_h={1\over\sqrt D}\sum_{x\in\{0,1\}^n}\omega^{h(x)}|x\rangle. \tag{2}
\]

Every `chi_h` has an exact ancilla-free preparation of size `O(n^3)`: start from `|+>^n` and apply
the one-, two-, or three-qubit controlled diagonal phase belonging to every nonzero monomial in `(1)`.
There are only eight phase values and arity at most three.  Fix exact two-qubit decompositions of
the finitely many three-qubit diagonal gates and adjoin their finitely many primitives to the gate
dictionary.  Thus one finite one- and two-qubit alphabet prepares every seed with

\[
 b_n=O(n^3).                                                       \tag{3}
\]

Use the unit-shell nearest-neighbour two-local Pauli ensemble and finite gate dictionary of the
stabilizer parent.  Let `C_epsilon` be ancilla-free state complexity from the product reference in
pure-state trace distance, let

\[
 0<\epsilon_-<\epsilon_+<1,\qquad
 a_+=1-\epsilon_+^2,\qquad \gamma=\epsilon_+-\epsilon_->0,        \tag{4}
\]

and write `M_n` for the padded branching number of the dictionary.

## Theorem A -- cubic evaluations are fifteen-wise independent

For any `k<=min(15,D)` and any distinct Boolean inputs `x_1,...,x_k`, the vector

\[
 (h(x_1),\ldots,h(x_k))
\]

is uniform on `(Z/8Z)^k`.  Consequently the phases

\[
 (\omega^{h(x_1)},\ldots,\omega^{h(x_k)})                         \tag{5}
\]

are independent uniform eighth roots of unity.

### Proof

Reduce the degree-at-most-three evaluation matrix modulo two.  Its row space is the binary
Reed--Muller code `RM(3,n)`.  The standard identity

\[
 RM(r,n)^\perp=RM(n-r-1,n)                                       \tag{6}
\]

is immediate from monomial orthogonality and the dimension count.  The minimum nonzero weight of
`RM(r,n)` is `2^(n-r)`: writing

\[
 p(x',x_n)=p_0(x')+x_np_1(x')
\]

proves this by induction, because if `p_1=0` the two slices coincide, while if `p_1!=0` the sum of
the two slice weights is at least the weight of `p_1`.  Therefore the dual of `RM(3,n)` has minimum
weight `16`.  No nonzero linear dependency can be supported on at most fifteen evaluation
columns.

Hence the chosen `k` columns contain a `k` by `k` minor with odd determinant.  The same determinant
is a unit modulo eight, so the evaluation map over `Z/8Z` is surjective onto `(Z/8Z)^k`.  A uniform
input to a surjective homomorphism of finite modules has uniform output.  This proves `(5)`.  For
`n<4`, degree at most three contains every square-free monomial and the full Boolean evaluation
matrix is invertible; the same conclusion holds.

## Lean status -- Theorem A is formal

`formal/GaloisForLFunctions/HTGeometry/CubicPhaseEvaluationUniformity.lean` (new, umbrella-wired,
axiom-clean) together with the corpus module `ReedMullerEvaluationRank`.

| Card item | Declaration | Module |
|---|---|---|
| `(6)`-based rank statement: no dual relation on fewer than `2^(m+1)` points | `vecMul_evalMatrix_eq_zero_imp` | `ReedMullerEvaluationRank` |
| surjectivity of degree-`<=m` evaluation over `ZMod 2` | `surjective_mulVec_evalMatrix` | `ReedMullerEvaluationRank` |
| an even residue modulo eight is halvable | `exists_two_mul_of_red_eq_zero` | `CubicPhaseEvaluationUniformity` |
| lifting surjectivity from `ZMod 2` to `ZMod 8` (three halvings) | `surjective_mulVec_of_surjective_map` | `CubicPhaseEvaluationUniformity` |
| the mod-two reduction of the evaluation matrix | `map_reedMullerEvalMatrix` | `CubicPhaseEvaluationUniformity` |
| surjective evaluation over `ZMod 8` at `k < 2^(m+1)` points | `surjective_mulVec_evalMatrix_zmod_eight` | `CubicPhaseEvaluationUniformity` |
| equal fibres of a surjective homomorphism | `card_fiber_eq_card_kernel`, `card_fiber_mul_card_eq_card` | `CubicPhaseEvaluationUniformity` |
| **Theorem A**: the evaluation vector is uniform on `(ZMod 8)^k` for `k < 2^(m+1)` | `card_fiber_evalMatrix_mul_card_eq` | `CubicPhaseEvaluationUniformity` |

At `m = 3` the hypothesis `k < 2^4` is exactly `k <= 15`, so Theorem A holds in the stated
fifteen-wise form.  The minimum-distance argument of the card is replaced by the corpus form of the
same fact -- a nonzero dual relation supported on fewer than `2^(m+1)` points is impossible -- and
the `Z/8Z` step is the nilpotence of `2` rather than an odd-determinant minor: both prove exactly
`(5)`.

## Lean status -- Theorem B, the pieces already owned

| Card item | Declaration | Module |
|---|---|---|
| `(11)` fourth Steinhaus moment `<= 2` | `integral_box_fidelity_uniformPhaseSeed_sq_le`, `integral_box_phase_fourth_le` | `PhaseSeedCollisionMoments`, `SteinhausFourthMoment` |
| `(14)` sixth Steinhaus moment `<= 6` | `integral_box_fidelity_uniformPhaseSeed_cube_le` | `PhaseSeedCollisionMoments` |
| `E C <= 2/D` | `integral_box_phaseCollision_le` | `PhaseSeedCollisionMoments` |
| `(12)` torus Poincare inequality | `variance_trigLift_le_sum_integral_normSq_pderiv` | `TorusTrigPoincare` |
| variance from an a.e. gradient bound | `variance_le_of_ae_fderiv_bound` | `TorusTranslateDifference` |
| `(9)` Chebyshev against the *upper* mean bound | `measureReal_gt_le_of_mean_le` | `UpperMeanChebyshev` (new) |
| the `(9)` scale arithmetic `96/D^3 / (kappa/D)^2 = 96/(kappa^2 D)` | `collision_tail_scale`, `collision_threshold_split` | `UpperMeanChebyshev` (new) |

### `(13)` is closed

`formal/GaloisForLFunctions/HTGeometry/CollisionPhaseGradient.lean` (new, umbrella-wired,
axiom-clean) proves the gradient identity in full, including the differentiation:

| Card item | Declaration |
|---|---|
| the phase orbit `y_j(theta) = sum_a U_{ja} e^{i theta_a}` and the quartic functional `f` | `phaseOrbit`, `collisionFunctional` |
| the cubic vector `v_j = \|y_j\|^2 y_j` and the closed-form derivative | `cubicVector`, `phaseDerivative` |
| the squared modulus is differentiable along a path, with derivative `2 Re(conj(y) y')` | `hasDerivAt_normSq` |
| the orbit depends on one phase coordinate through a single exponential | `hasDerivAt_phaseOrbit` |
| **the closed form is the derivative**: `d f / d theta_a = phaseDerivative` | `hasDerivAt_collisionFunctional` |
| each derivative is at most `4 \|(U^* v)_a\|` | `abs_phaseDerivative_le` |
| unitarity preserves the energy of the cubic vector | `sum_normSq_vecMul_conj` |
| the cubic vector has squared norm the sixth power sum | `sum_normSq_cubicVector` |
| **`(13)`**: `sum_a \|d f / d theta_a\|^2 <= 16 sum_j \|y_j\|^6` | `sum_sq_phaseDerivative_le_sixth` |

So the chain `(12) -> (13) -> (14)` has no analytic gap left: the Poincare inequality, the gradient
identity, and the sixth moment are all formal.

### The moment transfer is closed

`formal/GaloisForLFunctions/HTGeometry/EighthRootMomentTransfer.lean` (new, umbrella-wired,
axiom-clean):

| Card item | Declaration |
|---|---|
| a primitive eighth root and its additive character | `zeta8`, `isPrimitiveRoot_zeta8`, `charEight` |
| the character is trivial exactly at the zero residue | `charEight_eq_one_iff` |
| **the character sum**: `sum_x omega^{dx} = 8` if `d = 0`, else `0` | `sum_charEight_mul` |
| the monomial average factorizes over coordinates | `sum_prod_charEight` |
| a nontrivial monomial averages to zero -- the continuous-phase answer | `sum_prod_charEight_eq_zero` |
| equal fibres follow from the uniformity identity of Theorem A | `card_fiber_const_of_mul_eq` |
| **averaging over a uniform ensemble is averaging over the cube** | `sum_comp_of_uniform` |
| **the moment transfer**: a nontrivial monomial has vanishing ensemble average | `sum_comp_prod_charEight_eq_zero` |

Since `f` and `f^2` involve at most eight coordinate occurrences with net phase power in `[-4,4]`,
and `8` is not a divisor of any nonzero residue in that range, every monomial of `f` and `f^2` has
the same average over the cubic-phase ensemble as under continuous phases.  Theorem A supplies the
uniformity hypothesis, so the transfer is unconditional.

### What remains
3. Theorem C and the Corollary are assemblies over the two parent cards
   (`stabilizer-seeded-static-local-double-exponential-plateau-law`,
   `fixed-shell-angular-dephasing-static-local-plateau-law`), which are themselves still at stage 2.

## Theorem B -- basis-uniform collision concentration

Let `e_1,...,e_D` be **any** orthonormal basis of `C^D`, and put

\[
 C_e(\chi_h)=\sum_{j=1}^D|\langle e_j,\chi_h\rangle|^4.            \tag{7}
\]

Then

\[
 \boxed{
 \mathbb E_h C_e(\chi_h)\le {2\over D},\qquad
 \operatorname{Var}_h C_e(\chi_h)\le {96\over D^3}.}             \tag{8}
\]

In particular, for every `kappa>0`,

\[
 \boxed{
 \Pr_h\left\{C_e(\chi_h)>{2+\kappa\over D}\right\}
 \le {96\over\kappa^2D}.}                                       \tag{9}
\]

The basis may depend arbitrarily on a Hamiltonian sampled independently of `h`; integrating `(9)`
therefore gives the identical bound for the random Hamiltonian eigenbasis.

### Proof

Let `U` be the unitary whose rows are the conjugate basis vectors.  First replace the finite phase
vector in `(2)` by independent continuous Steinhaus phases `zeta_a`, and set

\[
 y=U\zeta,\qquad f(\zeta)=\sum_{j=1}^D|y_j|^4,
 \qquad C={f\over D^2}.                                           \tag{10}
\]

For every unit row `u`, direct phase pairing gives

\[
 \mathbb E\left|\sum_a u_a\zeta_a\right|^4
 =2-\sum_a|u_a|^4\le2.                                           \tag{11}
\]

Summing the rows proves `E C<=2/D`.

The product-torus Poincare inequality gives

\[
 \operatorname{Var}f
 \le\mathbb E\sum_{a=1}^D|\partial_{\theta_a}f|^2,
 \qquad \zeta_a=e^{i\theta_a}.                                  \tag{12}
\]

With `v_j=|y_j|^2y_j`, differentiation and unitarity imply

\[
 \sum_a|\partial_{\theta_a}f|^2
 \le16\|U^*v\|_2^2
 =16\sum_j|y_j|^6.                                                \tag{13}
\]

Another direct phase pairing gives, for every unit row,

\[
 \mathbb E\left|\sum_a u_a\zeta_a\right|^6
 =6-9\sum_a|u_a|^4+4\sum_a|u_a|^6\le6.                           \tag{14}
\]

Equations `(12)--(14)` yield `Var f<=96D`, hence `Var C<=96/D^3`.

Both `f` and `f^2` are polynomials containing at most eight coordinate occurrences, and the net
power of each phase lies between `-4` and `4`.  Theorem A supplies the required independence, while
uniform eighth roots have the same moments as continuous phase on this exponent range.  Thus the
finite cubic-phase ensemble has exactly the same first two moments of `f` as the Steinhaus
ensemble.  This transfers `(8)` to `(2)`.  Chebyshev at distance `kappa/D` from the upper mean bound
proves `(9)`.

## Theorem C -- high-probability full-scale plateau

Fix `kappa>0` and define

\[
 G_\kappa=
 \left\{(\theta,h):C_{H(\theta)}(\chi_h)\le{2+\kappa\over D}\right\},
 \qquad
 r=\left\lfloor{a_+^2D\over32(2+\kappa)}\right\rfloor.           \tag{15}
\]

Assume `r>=1` and

\[
 s+1\le {r\log2\over2\log M_n}.                                 \tag{16}
\]

Then

\[
 \boxed{
 \limsup_{t\to\infty}
 \Pr_{\theta,h}\{C_{\epsilon_+}(e^{-itH(\theta)}\chi_h)\le s\}
 \le {96\over\kappa^2D}+2^{-r/2}.}                              \tag{17}
\]

More sharply, for every `q>0` and plateau length `W>0`, there is a finite, generally non-effective
`T` such that every interval origin `A>=T` obeys

\[
 \Pr_{\theta,h}\left\{
   \forall t\in[A,A+W],\quad
   C_{\epsilon_-}(e^{-itH(\theta)}\chi_h)>s
 \right\}
 \ge1-{96\over\kappa^2D}-N_W2^{-r/2}-q,                          \tag{18}
\]

where

\[
 N_W=\left\lceil{W\sqrt{12n-9}\over\gamma}\right\rceil+1.     \tag{19}
\]

In particular, if `N_W<=2^(r/4)`, the right side of `(18)` is at least

\[
 1-{96\over\kappa^2D}-2^{-r/4}-q,                                \tag{20}
\]

and one may take

\[
 W={\gamma\over\sqrt{12n-9}}\left(2^{r/4}-2\right).             \tag{21}
\]

For fixed `epsilon_+` and `kappa`, this is depth

\[
 \boxed{\Omega(D/\log M_n)}                                     \tag{22}
\]

continuously for duration

\[
 \boxed{2^{\Omega(D)}}                                          \tag{23}
\]

with probability `1-O(1/D)`.  For a standard local dictionary,
`log M_n=O(log n)`, so `(22)` is `Omega(2^n/log n)` and `(23)` is doubly exponential in `n`.

### Proof

Theorem B gives

\[
 \Pr_{\theta,h}(G_\kappa^c)\le{96\over\kappa^2D}.                \tag{24}
\]

On `G_kappa`, the collision-to-capacity law of the stabilizer parent bounds the complete
depth-`s` shortcut union on the completed phase torus by

\[
 M_n^{s+1}r!\left({16(2+\kappa)\over a_+^2D}\right)^r
 \le M_n^{s+1}2^{-r}\le2^{-r/2}.                                 \tag{25}
\]

Fixed-shell angular dephasing transfers `(25)` to every sufficiently late common physical time.
Pay `(24)` once for the quenched Hamiltonian--seed pair.  This proves `(17)`.  The speed bound
`||H(theta)||_op<=sqrt(12n-9)`, a grid of mesh `gamma/sqrt(12n-9)`, the error-radius triangle
inequality, and one union bound prove `(18)`.  Equations `(20)--(23)` follow exactly as in the
parent theorem.

## Corollary -- one deterministic easy seed per system size

For every `n`, there exists one fixed polynomial `h_n in P_3(n)` such that, simultaneously for
every `kappa>0`,

\[
 \Pr_\theta\left\{
 C_{H(\theta)}(\chi_{h_n})>{2+\kappa\over D}
 \right\}
 \le {96\over\kappa^2D}.                                       \tag{26}
\]

For this one seed, all conclusions `(17)--(23)` hold with probability only over the single
Hamiltonian draw.  In particular, the initial state need not be freshly randomized between
experiments or correlated with the Hamiltonian.

### Proof

For each `theta`, put `mu_theta=E_h C_{H(theta)}(chi_h)<=2/D`.  Pointwise in `h`,

\[
 \left(C_{H(\theta)}(\chi_h)-{2\over D}\right)_+^2
 \le\left(C_{H(\theta)}(\chi_h)-\mu_\theta\right)^2.             \tag{27}
\]

Average `(27)` over `h`, use Theorem B, then integrate over `theta`.  Fubini gives

\[
 {1\over|P_3(n)|}\sum_h
 \mathbb E_\theta
 \left(C_{H(\theta)}(\chi_h)-{2\over D}\right)_+^2
 \le {96\over D^3}.                                             \tag{28}
\]

At least one summand is no larger than the average.  Fix such an `h_n`; it is independent of
`kappa` and has the common `O(n^3)` preparation bound.  Markov applied to its positive-part square
at threshold `(kappa/D)^2` proves `(26)` for every `kappa`.  The collision-good angular proof and
continuum grid then run conditionally on this fixed seed, proving the claim.

## Corollary -- low, full plateau, recurrence, and permanent non-Haar locality

Every seed has initial exact complexity at most `b_n=O(n^3)`, while `(22)` is exponentially larger.
For every fixed seed, cyclicity and maximal projective spectral rank hold for almost every
Hamiltonian in the path-local ensemble.  Indeed, product vectors span the Hilbert space, so local
basis rotations can be chosen with every product-basis amplitude of the seed nonzero; a one-local
Hamiltonian with distinct balanced-ternary product energies then witnesses that its Krylov
determinant is not the zero polynomial.  Finiteness of the seed ensemble permits one simultaneous
conull Hamiltonian set.

Kronecker--Weyl recurrence therefore returns the same evolved seed arbitrarily close to its
polynomial-circuit starting state after every time.  On the event `(18)`, one fixed trajectory has:

1. complexity `O(n^3)` at `t=0`;
2. complexity `Omega(2^n/log n)` at every instant of a block of length `2^{Omega(2^n)}`;
3. a later return to complexity `O(n^3)` at error `epsilon_-`.

Whenever the exact protocol's finite-size condition `9M_2<D+1` holds (hence for all sufficiently
large `n`), the bounded-weight Pauli protocol simultaneously distinguishes the same
`e^{-itH(theta)}` from Haar randomness at every real time.  Here `M_2` may be the known path-local
Pauli dictionary containing the Hamiltonian support.  Thus full-scale state complexity and
permanent observable locality coexist throughout the plateau and at recurrence.

## Conjecturing and falsification ledger

### C0 -- an exact projective four-design seed removes the stabilizer `D/L` loss

**Mathematically true but physically incomplete.**  A four-design gives collision variance
`Theta(D^-3)`, but an efficiently preparable exact four-design fiducial with the required literal
finite-gate model was not supplied uniformly in `n`.

### C1 -- an approximate four-design is enough

**Failed as the clean mechanism.**  Generic trace-norm design error enters the fourth-copy moment
additively and must be much smaller than `D^-2`; invoking deep design-mixing and compilation would
replace a short missing lemma by major external infrastructure.

### C2 -- eight-wise independent binary signs have basis-uniform `D^-3` collision variance

**Survives only for real eigenbases.**  A Walsh-tensor calculation gives such a bound for every
orthogonal basis, but restricting the Hamiltonian to the time-reversal-symmetric subfamily is
unnecessary.

### C3 -- finite independent eighth-root phases inherit Steinhaus Poincare concentration

**Proved.**  Only the first two collision moments are needed.  Fifteen-wise independent cubic
`Z/8Z` phases reproduce them exactly, while the continuous product-torus Poincare inequality gives
the uniform `96/D^3` variance.  Direct controlled phases give an exact `O(n^3)` finite-alphabet
preparation.  This proves Theorems A--C without restricting the Hamiltonian eigenbasis.

### C4 -- stronger seed concentration proves the Brown linear ramp

**Falsified.**  Every cubic-phase seed is shallow at `t=0`, and fixed finite seed moments do not
control the growing replica order needed for a depth-linear shortcut union.  The remaining ramp is
a genuinely dynamical quenched-incidence problem, not a seed-design problem.

**Positive survivor:** The full Brown-scale plateau height, lifetime, high probability, recurrence,
and permanent locality clauses now hold simultaneously.  The sole missing Brown--Susskind clause is
quantitative first onset/linear growth.

## Hostile audit

1. **No linear ramp.**  Equations `(17)--(23)` do not bound the first hard time.  They cannot be
   advertised as the full Brown--Susskind law.
2. **Late onset is non-effective.**  Angular Riemann--Lebesgue gives a finite common `T`, with no
   useful bound in `n`.
3. **Seed can be fixed but is nonconstructively selected.**  The finite averaging argument fixes one
   `O(n^3)`-preparable cubic seed per `n`; it does not give an efficient algorithm for finding the
   good seed.  No Haar-random initial state is hidden.
4. **Disorder is drawn once.**  Hamiltonian and seed are sampled once; no coupling, gate, time, or
   noise is refreshed during the plateau.
5. **Finite-gate model is literal.**  The dictionary must contain fixed exact decompositions of the
   finitely many controlled eighth-root phase gates.  Continuous adjustable gates are not counted.
6. **State, not unitary, complexity.**  The theorem concerns one efficiently preparable state
   trajectory.  It does not prove maximal unitary complexity.
7. **Formal gate remains closed.**  This card is paper-proved only.  Publication claims remain
   forbidden until its dependency chain is formalized and axiom-audited after the corpus refactor.

## External separation audit

- Nakata--Koashi--Murao construct diagonal-unitary `t`-designs from discrete controlled-phase
  circuits of logarithmic arity.  At fixed low `t`, this is close seed-preparation infrastructure;
  neither cubic controlled phases nor finite phase independence are claimed new here.
- Nakata--Turner--Murao analyze phase-random equal-amplitude states and their entanglement and
  simulability.  That work motivates the seed class but does not state the arbitrary-basis
  collision variance or the static-local complexity-history theorem below.
- Brakerski--Shmueli construct efficient approximate state designs from finite-wise-independent
  binary phases.  They do not prove the basis-uniform inverse-participation variance `(8)` or its
  static-local plateau consequence.
- Haferkamp proves linear complexity growth for random circuits with freshly sampled gates.  That
  result neither supplies a one-draw static Hamiltonian plateau nor the recurrence/locality
  coexistence law here.
- Oszmaniec--Kotowski--Horodecki--Hunter-Jones prove saturation and recurrence for random circuits
  and stochastic Hamiltonian evolution, not one fixed time-independent local Hamiltonian.
- Cui--Schuster--Mao--Huang--Brandao supply the broad permanent non-Haar obstruction for local
  Hamiltonian ensembles.  That clause is consumed here and carries no independent novelty claim.

Accordingly, candidate novelty begins at the arbitrary-eigenbasis collision concentration and its
quenched dynamical composition, not at phase-state preparation.  No located source states the
combined theorem: fixed polynomially preparable cubic-phase seed, arbitrary eigenbasis collision concentration
`O(D^-3)`, full `Theta(D/log n)` continuous plateau for
`2^{Theta(D)}` time under one fixed-strength nearest-neighbour static Hamiltonian, later recurrence,
and permanent same-protocol non-Haar separation.  Search absence is not a legal priority guarantee;
the collision lemma and combined law require specialist external review.

## Lean realization after corpus refactor

Formalize in this dependency order:

1. finite `ZMod 8` square-free polynomial evaluation and the weight-16 Reed--Muller dual bound;
2. fifteen-wise independence and moment transfer through degree eight;
3. finite-dimensional product-torus Poincare inequality or a direct finite phase-pairing variance
   proof with the same `O(D^-3)` bound;
4. basis-uniform collision tail `(8)--(9)`;
5. collision-good angular plateau, continuum mesh, cyclicity, recurrence, and locality capstone.

Do not formalize during the active corpus refactor.  Final audit must use `lake env lean <file>` for
foreground checks, one process, then one targeted `lake build <module>` only at the publication
gate, followed by axiom and lint audits.

## Log

- 2026-08-09 -- C0--C4 loop completed.  Replaced the stabilizer Markov tradeoff by an exact
  cubic-phase/Steinhaus Poincare argument; proved full-scale high-probability plateau on paper.
