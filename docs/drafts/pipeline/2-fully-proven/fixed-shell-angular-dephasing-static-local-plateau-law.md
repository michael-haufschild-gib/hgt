# Fixed-shell angular dephasing gives an all-late-time static-local complexity plateau

- **ID:** `fixed-shell-angular-dephasing-static-local-plateau-law`
- **Stage:** 2 -- fully proved on paper
- **Type:** theorem / fixed-interaction static-local complexity plateau
- **Parents:** `local-clifford-return-excised-phase-incidence-law.md`,
  `nearest-neighbor-chain-projective-spectral-maximality.md`
- **Status:** `[PAPER-PROVED] [FRONTIER ADVANCE] [NOVELTY UNVERIFIED] [LEAN DEFERRED]`
- **Date:** 2026-08-08

## Public sentence

At every sufficiently late common time, a fixed-strength random nearest-neighbour spin
Hamiltonian has produced a state of exponential circuit complexity with high probability, even
though locality remains efficiently distinguishable from Haar randomness forever.

This is an all-late-time ensemble plateau theorem. It is not a quantitative plateau-onset or
initial linear-growth theorem.

## Frontier crossed

The completed-phase theorem proves that almost every one fixed nearest-neighbour Hamiltonian
spends nearly all completed time at exponential state complexity. The common-time transfer then
proved only an unbounded subsequence of deterministic times. Neither result implies that a common
late laboratory time is typically hard: exceptional easy times could, in principle, align across
the ensemble.

A tempting shortcut is the polar decomposition of Gaussian disorder. Random radius turns a fixed
laboratory time into a random elapsed time and therefore dephases every nonresonant orbit. That is
not the required advance. It mixes interaction strengths, and disappears after time is normalized
by the Hamiltonian rate.

This card removes radial mixing. All Hamiltonians lie on one coefficient sphere, equivalently at
one normalized Hilbert--Schmidt interaction rate. The new mathematical input is a local-spectral
nonflatness theorem: no nontrivial integer spectral action is constant on any open patch of that
sphere. Angular disorder alone then dephases every projective spectral character.

## Setup

Fix `n>=2`, put `D=2^n`, and let `P_1,...,P_m` be the complete nonidentity Pauli basis consisting
of every one-site Pauli and every two-site Pauli orientation on each edge of the open path. Use
the normalized Pauli convention

\[
 D^{-1}\operatorname{Tr}(P_aP_b)=\delta_{ab}.                         \tag{1}
\]

For `theta` on the unit sphere `S^(m-1)`, define

\[
 H(\theta)=\sum_{a=1}^m\theta_aP_a.                                  \tag{2}
\]

Thus every member is traceless, time independent, nearest-neighbour and two local, and every
member has exactly the same coefficient/Hilbert--Schmidt interaction rate

\[
 D^{-1}\operatorname{Tr}H(\theta)^2=1.                               \tag{3}
\]

Uniform spherical measure is denoted by `sigma`. The same theorem holds on a support-weighted
ellipsoid after whitening, provided every Pauli orientation on a fixed support has the same
positive weight.

Let `Omega=|0>^(tensor n)`. Fix a finite gate dictionary with at most `M_n` padded choices,
including locations, per word position. Let `C_epsilon(psi)` be ancilla-free state complexity at
pure-state trace-distance error `epsilon`, and put

\[
 a=1-\epsilon^2.                                                       \tag{4}
\]

## Theorem A -- local spectral actions are nowhere flat on a fixed shell

On every simple-spectrum chart write the ordered eigenvalues as

\[
 E_1(\theta)<\cdots<E_D(\theta).
\]

For every nonzero integer vector `k in Z^(D-1)`, define its projective spectral action

\[
 \phi_k(\theta)
 =\sum_{j=2}^D k_j(E_j(\theta)-E_1(\theta)).                         \tag{5}
\]

Then

\[
 \boxed{\phi_k\text{ is not constant on any nonempty open simple-spectrum patch of }
 S^{m-1}.}                                                           \tag{6}
\]

Consequently its spherical gradient is nonzero almost everywhere on every analytic eigenchart,
and the pushforward of spherical volume by `phi_k` is absolutely continuous with respect to
Lebesgue measure after restriction by any continuous chart amplitude.

### Lemma A1 -- complete endpoint witnesses

For every path length `n>=2`, the local Hamiltonian space contains a simple-spectrum analytic
chart with both properties below:

1. no constant affine relation among all analytic eigenbranches exists except trace;
2. at one endpoint site, every pair of distinct eigenbranches has a nonzero transition matrix
   element for at least one one-site Hermitian probe.

For `n=2`, the allowed edge is the full Hermitian algebra on two qubits. For any fixed pair of
orthonormal eigenvectors, failure of all endpoint probes is the vanishing of

\[
 \operatorname{Tr}_{\bar u}|\psi_\beta\rangle\langle\psi_\alpha|.
\]

Its squared Hilbert--Schmidt norm is a nonzero real-analytic function of the eigenbasis. There are
only finitely many pairs, so a generic eigenbasis makes the endpoint transition graph complete.

For the induction, attach one qubit with distinct local energies. At zero edge coupling, endpoint
`X` supplies every vertical transition. If an old endpoint probe has nonzero matrix element
`A_(alpha beta)`, perturbing by `A tensor X` gives a nonzero first derivative of a new-site `Z`
transition across the two energy blocks and a nonzero first derivative of a new-site `X`
transition within each block. These are the standard nondegenerate eigenvector derivatives; their
denominators are nonzero after avoiding finitely many old gaps. Each desired transition failure is
therefore a proper analytic zero set. One sufficiently small edge perturbation outside their
finite union makes every new endpoint transition nonzero simultaneously. Completeness implies
connectedness and nonbipartiteness, so the existing endpoint-extension residue argument also gives
branchwise affine independence.

### Lemma A2 -- branchwise quadratic-rate rigidity

Let `Q(H)=D^(-1) Tr(H^2)`. On the charts in Lemma A1, no nonconstant zero-sum coefficient vector
`c` and no `kappa>=0` obey the analytic identity

\[
 \left(\sum_jc_jE_j(H)\right)^2=\kappa Q(H).                         \tag{7}
\]

For the two-qubit base, restrict the full Hermitian chart to diagonal traceless matrices. On an
open eigenvalue chamber, `(7)` would identify the rank-one quadratic form `(c dot E)^2` with a
nonzero multiple of the Euclidean form on the `(D-1)`-dimensional trace-zero space. This is
impossible for `D=4`. If `kappa=0`, affine independence makes `c` constant, and zero sum makes it
zero.

For the induction, use an old endpoint-complete, maximal-projective-rank Hamiltonian with
eigenpairs `(E_alpha,psi_alpha)`. Attach a qubit and write the uncoupled branches as

\[
 \lambda_{\alpha,0}(z,0)=E_\alpha+z/2,
 \qquad
 \lambda_{\alpha,1}(z,0)=E_\alpha-z/2.                              \tag{8}
\]

Perturb the edge by `x V_A`, where `V_A=A tensor X`. Put

\[
 L(z,x)=\sum_{\alpha,r}c_{\alpha,r}\lambda_{\alpha,r}(z,x),
 \qquad L_0(z)=L(z,0).                                               \tag{9}
\]

The perturbation is Hilbert--Schmidt orthogonal to the block-diagonal base, every first
eigenvalue derivative vanishes, and second-order perturbation theory gives

\[
 \partial_x^2L(z,0)
 =2\sum_{\alpha,\beta}
 { (c_{\alpha,0}-c_{\beta,1})
   |\langle\psi_\alpha,A\psi_\beta\rangle|^2
  \over z+E_\alpha-E_\beta}.                                       \tag{10}
\]

Twice differentiating `(7)` in `x` gives

\[
 L_0(z)\,\partial_x^2L(z,0)=\kappa Q(V_A),                          \tag{11}
\]

whose right side has no spectral pole. If `L_0` vanishes identically, `(11)` forces
`kappa=0`; affine independence then forces `c=0`. Otherwise `L_0` is a nonzero affine function of
`z` and has at most one zero.

Maximal projective rank makes all nonzero ordered old gaps distinct. Taking residues in `(11)`
therefore gives

\[
 c_{\alpha,0}=c_{\beta,1}                                           \tag{12}
\]

for every `alpha!=beta`, with at most one ordered pair omitted. Endpoint completeness supplies
the required probe `A` for every pair. The bipartite graph with all edges
`(alpha,0)--(beta,1)` for `alpha!=beta` is connected for old dimension at least three and remains
connected after deleting one edge. Thus all coefficients in `(12)` are equal. Their total sum is
zero, so all vanish. This proves Lemma A2.

### Proof of Theorem A

Suppose one action in `(5)` were constant, equal to `b`, on an open sphere patch. Homogeneity of
eigenvalues extends the identity to the open cone over that patch and gives

\[
 \left(\sum_jc_jE_j(H)\right)^2=b^2Q(H),                            \tag{13}
\]

where `c_1=-sum_(j>=2)k_j`, `c_j=k_j`, so `sum c_j=0` and `c!=0`.

Symmetrize the left side of `(13)` over every eigenvalue labeling:

\[
 \mathscr G_{c,b}(H)
 =\prod_{\pi\in S_D}
 \left[
   \left(\sum_jc_jE_{\pi(j)}(H)\right)^2-b^2Q(H)
 \right].                                                          \tag{14}
\]

This is a symmetric polynomial in the eigenvalues and therefore a polynomial in characteristic
coefficients and local Hamiltonian parameters. Vanishing on a parameter-space open set would make
it identically zero. On the connected witness chart of Lemma A2, a finite product of analytic
functions can vanish identically only if one factor does. Lemma A2 excludes every factor. This
contradiction proves `(6)`.

A nonconstant real-analytic function has critical set of measure zero. On the regular set, the
coarea formula shows that the inverse image of every Lebesgue-null subset of `R` has spherical
measure zero. Hence every continuously weighted pushforward by `phi_k` is absolutely continuous.

## Theorem B -- angular dephasing on the fixed shell

Let `m_T` denote Haar probability on the projective phase torus `T^(D-1)`. For almost every
`theta`, define the projective phase vector

\[
 \omega(\theta)
 =(E_2(\theta)-E_1(\theta),\ldots,E_D(\theta)-E_1(\theta)).          \tag{15}
\]

Then the joint angular-phase laws converge weakly:

\[
 \boxed{
 (\theta\mapsto(\theta,t\omega(\theta)\bmod2\pi))_*\sigma
 \ \Longrightarrow\ \sigma\otimes m_T
 \qquad(t\to\infty).}                                             \tag{16}
\]

### Proof

It suffices to test a continuous amplitude `g(theta)` times a torus character. The zero character
is unchanged. A nonzero character `k` gives

\[
 \int_{S^{m-1}}g(\theta)e^{it\phi_k(\theta)}d\sigma(\theta).        \tag{17}
\]

Use analytic eigencharts and a partition of unity away from the null discriminant. By Theorem A,
the weighted pushforward measure under `phi_k` is absolutely continuous. Its Fourier transform
therefore tends to zero by the Riemann--Lebesgue lemma. Equation `(17)` vanishes for every
nonzero character. Trigonometric-polynomial density proves `(16)`.

This is a fixed-shell theorem: no random radius, random time, stochastic Hamiltonian increment,
spectral-gap minimum or random-matrix eigenbasis is used.

## Theorem C -- every sufficiently late common time is typically exponentially hard

For `L>=1`, define

\[
 r_n=\left\lfloor{a^2\over32L}\left({3\over2}\right)^n\right\rfloor,
                                                                            \tag{18}
\]

and assume `r_n>=1`. If

\[
 s+1\le {r_n\log2\over2\log M_n},                                  \tag{19}
\]

then

\[
 \boxed{
 \limsup_{t\to\infty}
 \Pr_{\theta\sim\sigma}
 \{C_\epsilon(e^{-itH(\theta)}\Omega)\le s\}
 \le {1\over L}+2^{-r_n/2}.}                                      \tag{20}
\]

Equivalently, for every `delta>0` there is a finite, generally non-effective
`T_(n,L,epsilon,delta)` such that every common physical time `t>=T` obeys

\[
 \boxed{
 \Pr_\theta
 \{C_\epsilon(e^{-itH(\theta)}\Omega)>s\}
 \ge1-{1\over L}-2^{-r_n/2}-\delta.}                               \tag{21}
\]

For a standard finite two-qubit alphabet with arbitrary gate locations,
`log M_n=O(log n)`. Fixed `L` yields depth

\[
 \Omega\!\left({(3/2)^n\over L\log n}\right).                     \tag{22}
\]

Taking, for example, `L=n` makes the hard fraction tend to one while retaining exponential depth
`Omega((3/2)^n/(n log n))`.

The same conclusion holds on every interaction graph containing a spanning path, with every
one-site Pauli and every Pauli orientation on each allowed edge. If a spectral action were flat on
an open patch of the larger coefficient sphere, its symmetrized polynomial `(14)` would vanish
identically on the larger local space and hence on the path-local witness, contradicting Theorem A.
Product-Clifford invariance and the collision estimate `(23)` are unchanged. This includes rings
and standard finite rectangular lattices after choosing a spanning path.

### Proof

The spherical ensemble is invariant under every product of one-qubit Clifford conjugations:
these act by signed permutations of Pauli orientations. The exact product-stabilizer second-moment
argument therefore gives, exactly as for isotropic Gaussian coefficients,

\[
 \mathbb E_\theta C_{H(\theta)}(\Omega)
 =\mathbb E_\theta\sum_j|\langle e_j(\theta),\Omega\rangle|^4
 \le\left({2\over3}\right)^n.                                     \tag{23}
\]

Markov gives a good angular set of measure at least `1-1/L` on which

\[
 C_{H(\theta)}(\Omega)\le L(2/3)^n.                                \tag{24}
\]

Simple spectrum, maximal projective rank and full input support fail only on null sets.

For one good `theta`, let `Z_s` be the at most `M_n^(s+1)` circuit outputs. The completed-phase
heavy-sector incidence theorem gives

\[
 m_T\{\exists z\in Z_s:
       |\langle\Phi_\theta(\zeta),z\rangle|^2\ge a\}
 \le h_{r_n}(Z_s)r_n!
 \left({16L(2/3)^n\over a^2}\right)^{r_n}.                         \tag{25}
\]

Here `Phi_theta(zeta)=sum_j zeta_j P_j(theta)Omega`, written with spectral projectors so no
eigenvector gauge is chosen. Since `h_(r_n)(Z_s)<=|Z_s|`, `(18)` implies

\[
 r_n!\left({16L(2/3)^n\over a^2}\right)^{r_n}
 \le2^{-r_n},                                                       \tag{26}
\]

and `(19)` makes `(25)` at most `2^(-r_n/2)`.

The easy-circuit tube is a finite union of closed fidelity superlevel sets in the angular-phase
bundle. Apply `(16)` and the Portmanteau upper bound, exhausting the null discriminant by compact
simple-spectrum subsets. Integrating `(25)` on the good set and paying one on its complement gives
`(20)`. The definition of `limsup` gives `(21)`.

## Same-time non-Haar locality and individual recurrence

Every Hamiltonian in `(2)` is a nonzero traceless two-local Pauli Hamiltonian. The existing
two-query local-observer score therefore separates `e^(-itH(theta))` from Haar randomness at every
time, including every hard time in `(21)`. High circuit complexity and Haar randomness are not the
same property: the state orbit becomes exponentially hard while the generator's local conservation
witness remains permanently observable.

For almost every one fixed `theta`, maximal projective rank also gives Kronecker--Weyl recurrence
and the completed-phase plateau density. Thus the two ensemble statements are complementary:

1. **quenched:** almost every fixed Hamiltonian is hard for almost all completed time but recurs;
2. **common time:** at every sufficiently late deterministic time, a high fraction of fixed-rate
   Hamiltonians are hard.

Equation `(21)` does not assert that one common full-measure set of Hamiltonians is hard at every
late time. Recurrence forbids that strengthening.

## Conjecturing protocol

### C0 -- a periodic Feynman--Kitaev clock transfers circuit growth

**Verdict:** `[FALSIFIED AS A CIRCUIT-LOWER-BOUND TRANSFER]`.

The exact clock Hamiltonian transfers Floquet spectra and produces Bessel-weighted winding
amplitudes. A hard circuit appears only after conditioning on a clock branch. Postselection can
create high deterministic circuit complexity from a shallow parent, so branch hardness does not
lower-bound ordinary circuit complexity of the coherent clock evolution.

**Positive survivor:** spectral-ramp transfer is valid, but effective state complexity requires a
source-level incidence theorem.

### C1 -- completed time density plus Gaussian radius proves the desired plateau

**Verdict:** `[TRUE SCALE-MIXTURE STATEMENT; REJECTED AS O4 CORE]`.

For `J=R theta`, independent continuous `R` makes every nonzero projective character vanish by
Riemann--Lebesgue. But this varies the Hamiltonian interaction rate. Normalizing elapsed time by
that rate cancels `R`.

**Positive survivor:** seek dephasing under angular disorder on `R=constant`.

### C2 -- maximal projective rank alone makes angular characters decay

**Verdict:** `[INSUFFICIENT AS STATED]`.

Pointwise nonvanishing of an integer spectral action does not prevent it from being constant on a
coefficient sphere. A Clifford pencil of pairwise anticommuting matrices has exactly this defect:
its nonzero eigenvalues depend only on coefficient radius.

**Positive survivor:** prove the stronger local-spectral nonflatness law `(6)` for the full
nearest-neighbour family.

### C3 -- fixed-shell local-spectral nonflatness

**Verdict:** `[PAPER-PROVED]`.

Endpoint-complete local extension and the pole identity `(11)` rule out every quadratic-rate
spectral identity. Symmetrization converts local flatness anywhere into such an identity on the
witness chart. This proves Theorem A.

### C4 -- angular dephasing gives only a late subsequence

**Verdict:** `[FALSE; STRONGER SURVIVOR PROVED]`.

Character-by-character Fourier decay is weak convergence of the complete angular-phase law, not a
Cesaro statement. Portmanteau therefore controls every sufficiently late common time, proving
`(20)--(21)`.

### C5 -- the same Hamiltonian is hard for all sufficiently late times

**Verdict:** `[FALSIFIED BY RECURRENCE]`.

Every finite maximal-rank orbit returns arbitrarily close to its easy input. The order of
quantifiers in `(21)` is sharp: each late `t` has high hard probability over `theta`; no one
time-independent full-measure subset can avoid all recurrences.

### C6 -- angular weak convergence gives the Brown onset scale

**Verdict:** `[NOT PROVED]`.

Riemann--Lebesgue is non-effective uniformly over exponentially many spectral characters.
Quantitative onset still requires lower-tail control of the relevant local spectral actions, or an
equivalent oscillatory-integral estimate, strong enough for the complete circuit tube.

## Hostile audit

1. **Not full Brown--Susskind growth.** The theorem proves an all-late-time static-local ensemble
   plateau, not initial linear growth, a first-hard-time scale, or a plateau-onset scale.
2. **Non-effective threshold.** `T_(n,L,epsilon,delta)` is finite but no bound in `n` is proved.
   The order of the large-time and large-system limits is uncontrolled.
3. **Annealed at one time.** Equation `(21)` is uniform over sufficiently late time values but its
   probability is evaluated separately at each time. It is not a pathwise uniform-tail event.
4. **Fixed coefficient/Hilbert--Schmidt rate.** The shell fixes `(3)`, not operator norm or every
   individual coupling magnitude. This is nevertheless strictly stronger than Gaussian radial
   scale mixing.
5. **Disordered family.** Full support-isotropic nearest-neighbour angular disorder is used.
   Translation-invariant, anisotropic and deterministic chains are not covered.
6. **Finite dictionary and state complexity.** Adjustable continuous gates, discarded ancillas,
   unitary/channel complexity and device noise need separate entropy arguments.
7. **Exponential, not maximal.** The proved base is `3/2`, below the full state-space base `2`.
8. **Classical analytic ingredients.** Symmetric-polynomial globalization, coarea,
   Riemann--Lebesgue and Weyl's criterion are classical. Candidate new knowledge is the
   fixed-shell local-spectral nonflatness theorem and its composition with occupied-replica
   incidence to obtain `(20)--(22)`.
9. **Formal publication gate closed.** This proof is Stage 2. Per explicit instruction during
   corpus refactoring, no Lean source was created, modified or built. No final manuscript may cite
   this theorem until later Lean formalization and axiom audit.

## External comparison

- Kotowski--Oszmaniec--Horodecki prove an all-fixed-late-time near-maximal complexity jump for GUE
  and Haar-random-eigenbasis Hamiltonians. Those ensembles are nonlocal and use unitary invariance;
  they do not prove `(6)`, `(16)` or the nearest-neighbour conclusion `(20)`.
- Oszmaniec--Kotowski--Horodecki--Hunter-Jones prove saturation and recurrence for random circuits
  and stochastic local Hamiltonian evolution, not one time-independent local generator.
- Ippoliti proves a random-matrix spectral ramp for a specially clock-embedded static local
  Hamiltonian. A spectral form factor does not imply a circuit lower bound.
- Equidistribution of dilated curves and submanifolds on tori is a classical and active subject.
  Those theorems do not supply the local spectral-action nonflatness or the circuit-incidence
  conclusion.

The targeted searches found no theorem combining a fixed local-coupling shell, nowhere-flat
integer spectral actions for a bounded-degree many-body family, angular spectral-phase
equidistribution, and an exponential approximate circuit plateau at every sufficiently late common
time. This is separation evidence, not a priority claim.

## Future Lean map after refactor

No Lean work is authorized during the current refactor. Later dependency order:

1. endpoint-complete path-local witness strengthening;
2. branchwise quadratic-rate rigidity `(7)--(12)`;
3. symmetric globalization and nowhere-flat action theorem `(6)`;
4. analytic/coarea Fourier-decay interface and angular-phase weak convergence `(16)`;
5. fixed-shell local-Clifford collision transfer;
6. composition with completed-phase incidence and the capstone `(20)`.

## Lean progress -- Theorem A, algebraic layer

The refactor-time instruction that forbade Lean work on this card is superseded; formalisation is
now in progress.  Two new modules, both umbrella-wired and axiom-clean.

`formal/GaloisForLFunctions/HTGeometry/QuadraticRateSpectralRigidity.lean` proves the base case of
Lemma A2, in a form strictly stronger than the card's `D=4` argument.

| Card item | Declaration |
|---|---|
| the defect `(∑ c_jE_j)² − κ∑E_j²` of a candidate quadratic-rate identity `(7)` | `quadraticRateDefect` |
| the defect along a line is a quadratic polynomial in the line parameter whose leading coefficient is the defect of the direction | `quadraticRateDefect_affine` |
| three points of one line kill that leading coefficient | `quadraticRateDefect_eq_zero_of_symmetric_pair` |
| every direction is reached symmetrically inside a neighbourhood | `exists_symmetric_pair_of_mem_nhds` |
| **localisation**: `(7)` on a neighbourhood of one traceless point holds on the whole traceless hyperplane | `quadraticRateDefect_eq_zero_of_nhds` |
| the two-level traceless test directions and their three sums | `levelPairDirection`, `sum_levelPairDirection`, `sum_mul_levelPairDirection`, `sum_sq_levelPairDirection`, `quadraticRateDefect_levelPairDirection` |
| **Lemma A2, base case**: for `D ≥ 3`, no zero-sum `c` and no `κ` satisfy `(7)` | `quadraticRate_traceless_rigidity` |
| the same from a merely local identity | `quadraticRate_traceless_rigidity_of_nhds` |

The proof is the three-difference argument: with `u = c_i−c_j`, `v = c_i−c_l`, `w = c_j−c_l` one
has `u = v−w` and `u² = v² = w² = 2κ`, whence `vw = κ` and `κ² = 4κ²`, so `κ = 0`; every level
difference then vanishes and the zero sum forces `c = 0`.  Only three levels are needed, so the
card's two-qubit base case is a special case and the same lemma covers every `D ≥ 3` block.

`formal/GaloisForLFunctions/HTGeometry/QuadraticRateOrbitPolynomial.lean` builds the symmetrised
obstruction `(14)`, mirroring the corpus's linear `SpectralRelationOrbitPolynomial`.

| Card item | Declaration |
|---|---|
| the relation `(∑ c_iX_i)² − κ∑X_i²` as a polynomial in the spectrum | `quadraticRateRelationPolynomial` |
| **the symmetrised obstruction `(14)`**, the product over every labeling | `quadraticRateOrbitPolynomial`, `quadraticRateOrbitValue` |
| its factors are the defects of the relabelled coefficient packets | `quadraticRateOrbitValue_factor`, `quadraticRateOrbitValue_eq_zero_iff` |
| real evaluation | `eval₂_quadraticRateRelationPolynomial_real`, `eval₂_quadraticRateOrbitPolynomial_real` |
| **the obstruction is symmetric**, hence a polynomial in the characteristic coefficients | `quadraticRateOrbitPolynomial_isSymmetric`, `quadraticRateCoefficientPolynomial`, `esymmAlgHom_quadraticRateCoefficientPolynomial`, `eval₂_quadraticRateCoefficientPolynomial_real_esymm` |
| the relation is a nonzero polynomial unless the multiple and the packet both vanish | `quadraticRateRelationPolynomial_eq_zero_iff` |
| hence so are the orbit and coefficient obstructions | `quadraticRateOrbitPolynomial_ne_zero`, `quadraticRateCoefficientPolynomial_ne_zero` |

`formal/GaloisForLFunctions/HTGeometry/AffinePoleResidueRigidity.lean` proves the residue step
`(11)`--`(12)` in the exact shape the induction needs, over an arbitrary finite pole packet.

| Card item | Declaration |
|---|---|
| cleared numerator of `L(w)·∑ c_i/(z_i − w) − cst` for an affine multiplier `L` | `affinePolePacketNumerator` |
| such an identity on any infinite pole-free set clears to the zero numerator -- no meromorphic continuation is used | `affinePolePacketNumerator_eq_zero_of_identity` |
| **the residue law `(12)`**: at every node, `c_i · L(z_i) = 0` | `affinePoleResidue_eq_zero`, `affinePoleCoefficient_eq_zero` |
| **at most one surviving residue**: a nonzero affine multiplier has one root, so at most one ordered pair may be omitted | `affinePole_support_subsingleton`, `affinePole_eq_zero_of_ne` |
| a vanishing multiplier forces the constant to vanish, which is the `kappa=0` branch | `affinePole_const_eq_zero_of_multiplier_zero` |

`formal/GaloisForLFunctions/HTGeometry/BipartiteCrossPairRigidity.lean` proves the connectivity
step: the bipartite graph with all edges `(alpha,0)--(beta,1)`, `alpha != beta`, is the crown
graph, and for at least three labels it stays connected after deleting one edge.

| Card item | Declaration |
|---|---|
| with at least three labels every pair admits a third | `exists_third_label` |
| two labels with a common admissible partner have equal values | `crossPair_eq_of_common` |
| **crown rigidity**: cross equalities on every ordered pair of distinct labels except at most one force all values on both layers to coincide | `crossPair_constant` |

The proof exhibits the explicit two-step path `x → y → beta → x → y`, so no graph-connectivity API
is needed and the bound `3 <= D_old` is exactly the card's.

`formal/GaloisForLFunctions/HTGeometry/LocalExtensionQuadraticRateRigidity.lean` assembles the
residue step into the exact statement the induction needs.

| Card item | Declaration |
|---|---|
| the pole index of the extension: the zero gap plus every ordered off-diagonal old pair | `OrderedGapIndex`, `extensionPolePosition`, `extensionPoleResidue` |
| distinct nonzero ordered gaps make the pole positions injective | `extensionPolePosition_injective` |
| the double sum of `(10)` written over its poles | `extensionPole_sum_eq` |
| the cleared numerator of the packet vanishes | `extensionPacket_numerator_eq_zero` |
| **the residue at one ordered gap `(12)`**: either the affine multiplier vanishes there or the two layer coefficients agree through the probe weight | `extensionPacket_residue`, `extensionPacket_eq_of_probe` |
| **the extension collapse**: an affine multiple of the `(10)` packet equal to a constant forces every layer coefficient to coincide | `extensionPacket_crossPair_constant` |
| **the collapse for a probe *family***: the affine multiplier is probe-independent, so at most one ordered gap is exceptional and a family that sees every ordered pair collapses everything | `extensionKey_family_collapse` |

`formal/GaloisForLFunctions/HTGeometry/BlockExtensionSecondOrderResponse.lean` computes the
perturbation-theoretic input `(8)`--`(10)`.

| Card item | Declaration |
|---|---|
| the uncoupled energies `(8)`, `E_alpha ± z/2` | `layerSplitEnergy`, `layerSplitEnergy_sub_cross`, `layerSplitEnergy_sub_cross'` |
| `V_A = A ⊗ X` in the split eigenbasis: it acts only across layers, so its diagonal vanishes | `layerCrossPerturbation`, `layerCrossPerturbation_apply_same`, `_apply_cross`, `_diagonal` |
| **`L_0` is affine in the new local field** | `layerSplitAction_affine` |
| **the second-order response of one branch** is a simple-pole sum at the ordered old gaps | `layerCrossSecondOrder_response` |
| **`(10)`**: the weighted response is exactly the crown pole packet | `layerCrossSecondOrder_weighted_sum` |

`formal/GaloisForLFunctions/HTGeometry/QuadraticRateSecondVariation.lean` proves `(11)`: with a
vanishing first variation, a quadratic-rate identity along a line reduces to the pole-free product
identity `F(0)·F''(0) = kappa Q_V` (`quadraticRate_secondVariation`).

`formal/GaloisForLFunctions/HTGeometry/LocalExtensionQuadraticRateCollapse.lean` closes the
inductive half of Lemma A2 by composing all of the above with the corpus's exact eigenbranch laws
`affineEigenbranch_firstDerivative_eq_diagonal` and `affineEigenbranch_secondDerivative_eq_general`.

| Card item | Declaration |
|---|---|
| finite combinations of analytic germs are twice differentiable at the base point | `hasDerivAt_analyticCombination`, `hasDerivAt_analyticCombination_deriv` |
| **`(11)` for an actual extension**: the affine-times-pole-packet identity at every admissible local field | `localExtension_quadraticRate_key` |
| **Lemma A2, inductive step**: a quadratic-rate identity for a one-qubit extension makes every coefficient of the extended spectral action coincide | `localExtension_quadraticRate_collapse` |
| **Lemma A2, conclusion**: a zero-sum such packet vanishes | `localExtension_quadraticRate_eq_zero` |

The chain is: the first variation vanishes because `V_A` is off-diagonal in the split eigenbasis;
the second variation then gives `L_0(z)·d²_x L(z,0) = kappa Q(V_A)`; the response is the pole
packet at the ordered old gaps; residues vanish; a nonzero affine `L_0` has one root so at most one
ordered pair escapes; the crown graph survives one deletion.  Every step is unconditional.

`formal/GaloisForLFunctions/HTGeometry/AnalyticFiniteProductDomain.lean` supplies the two
globalisation steps of `(14)`.

| Card item | Declaration |
|---|---|
| a finite product of analytic functions is analytic | `analyticOnNhd_finsetProd` |
| **a finite product vanishing on a connected open set has a vanishing factor** -- the identity theorem iterated, so "a finite product of analytic functions can vanish identically only if one factor does" is formal | `exists_eqOn_zero_of_finsetProd_eqOn_zero` |
| **a real polynomial vanishing on a nonempty open parameter set is zero** -- the zero set of a nonzero real polynomial is Lebesgue-null while an open set is not | `realMvPolynomial_eq_zero_of_eqOn_zero_isOpen` |

Homogeneity of the defect, which converts flatness on a sphere patch into the cone identity
`(13)`, is `quadraticRateDefect_smul` in `QuadraticRateSpectralRigidity`.

`formal/GaloisForLFunctions/HTGeometry/EndpointProbeTransitionCriterion.lean` formalises the exact
criterion Lemma A1 is about: for a probe supported on the endpoint factor,
`⟨psi, (X ⊗ 1) phi⟩ = Tr(X · R)` with `R_{ji} = ∑_k phi(j,k) conj(psi(i,k))`.

| Card item | Declaration |
|---|---|
| the reduced transition operator `Tr_ū |psi_beta><psi_alpha|` | `reducedTransition` |
| **endpoint probes pair only through it** | `endpointPairing_probe_eq_trace` |
| explicit Hermitian endpoint probes on one pair of levels, and their traces | `unitProbe`, `symmetricProbe`, `skewProbe`, `trace_symmetricProbe_mul`, `trace_skewProbe_mul` |
| **a nonzero reduced operator is already seen by an explicit Hermitian probe** | `exists_hermitian_endpointProbe_ne_zero` |
| **the blindness criterion**: every Hermitian endpoint probe annihilates a pair exactly when the reduced operator vanishes | `reducedTransition_eq_zero_iff` |

So endpoint completeness is now a single, concrete nonvanishing condition on the eigenbasis, and
Hermitian probes are shown to be no weaker than arbitrary ones.

`formal/GaloisForLFunctions/HTGeometry/CompleteProbeCombination.lean` turns a covering probe
*family* into one probe: each matrix element of a combination is a nonzero linear form in the
combination coefficients, the product of those forms over all ordered pairs is a nonzero
polynomial, and a nonzero polynomial over the complex numbers has a nonvanishing point
(`probeCombinationForm`, `probeCombinationForm_ne_zero`, `exists_probeCombination_ne_zero`).
This is what lets a *single* edge coupling carry the completeness that the family supplies pair by
pair.  Composed with the blindness criterion it gives the *return* leg of the recursion:
`exists_covering_endpoint_probe` turns endpoint completeness of a system into one endpoint
operator that pairs every ordered pair of its eigenvectors nontrivially -- which is exactly the
`hM` hypothesis the next attachment consumes (`endpointPairing_sum_probe` supplies the linearity).

`formal/GaloisForLFunctions/HTGeometry/LayerExtensionEndpointCompleteness.lean` and
`.../LayerGermEndpointCompleteness.lean` prove the **induction step of Lemma A1**.

| Card item | Declaration |
|---|---|
| the reduced transition over the *old* factor, whose surviving factor is the attached qubit, and its identification with the general criterion | `layerReducedTransition`, `layerReducedTransition_eq_reducedTransition` |
| a curve with vanishing value and nonvanishing derivative is nonzero near, but not at, the base point | `eventually_ne_zero_of_hasDerivAt_zero`, `eventually_ne_zero_of_continuousAt_zero`, `continuousAt_finsetSum` |
| **at zero coupling the attached qubit already sees the two halves of one old level**, hence for all small coupling | `eventually_layerReducedTransition_ne_zero_sameLevel` |
| **first-order creation across two old levels**: the *flipped* entry has vanishing value and derivative `Pi' · conj(Dpsi(beta_0,!r_0))` | `eventually_layerReducedTransition_ne_zero` |
| the canonical adjugate-column germ of the split family, its value at zero coupling and its real derivative | `layerGerm`, `layerGapProduct`, `layerGapProduct_ne_zero`, `layerGerm_zero`, `hasDerivAt_layerGerm` |
| **the off-label first derivative is the coupling element over the gap**, hence nonzero exactly when the coupling sees the old pair | `layerGerm_deriv_ne_zero` |
| **the induction step**: if the edge coupling sees an old pair, the attached qubit sees the corresponding split pair for all small nonzero coupling | `eventually_layerGerm_endpoint_ne_zero` |
| the same-level version, at zeroth order and with no condition on the coupling | `eventually_layerGerm_endpoint_ne_zero_sameLevel` |
| **endpoint completeness of the split system**: one edge coupling seeing every ordered old pair makes the attached qubit see *every* ordered pair of split labels, for all small nonzero coupling | `eventually_forall_layerGerm_endpoint_ne_zero` |
| **endpoint completeness is an open condition** in any continuously varying eigenvector family | `eventually_forall_layerReducedTransition_ne_zero` |

The formalisation forced one clarification of the paper argument.  The reduced-transition entry at
the *unflipped* new index has vanishing first-order term, because the edge perturbation is purely
cross-layer; only the flipped entry moves at first order.  So the index flip is not a convenience
but the unique first-order channel, and the hypothesis `alpha_0 != beta_0` turns out to be
unnecessary: the same computation covers the same-level pairs too.

### What remains for Theorem A

The recursion of Lemma A1 is now a closed cycle of formal theorems:

```text
endpoint completeness at stage n
    --[ exists_covering_endpoint_probe ]-->        one covering endpoint operator M
    --[ eventually_forall_layerGerm_endpoint_ne_zero ]-->  endpoint completeness at stage n+1
    --[ eventually_forall_layerReducedTransition_ne_zero ]--> and it is open, hence survives
                                                              intersection with the dense
                                                              maximal-rank set of the parent card
```

with the base case `n = 2` (four levels) and the `D >= 3` quadratic-rate base already formal.

**The physical realisation is now formal too.**
`formal/GaloisForLFunctions/HTGeometry/LayerSplitPhysicalRealization.lean` (new, umbrella-wired,
axiom-clean) is exactly the tensor-product bookkeeping that was missing.

| Card item | Declaration |
|---|---|
| the local field of the attached qubit, `±z/2` | `layerFieldShift` |
| its exchange operator | `layerExchange`, `layerExchange_apply` |
| **`layerCrossPerturbation M` is the edge term `M ⊗ X`** | `layerCrossPerturbation_eq_coupling` |
| **`layerSplitEnergy E z` is `H_old ⊗ 1 + 1 ⊗ diag(field)`** | `diagonal_layerSplitEnergy_eq` |
| **the split system is the leaf Hamiltonian**: old Hamiltonian, new one-site field, one parent--leaf edge | `layerSplit_eq_physicalLeafHamiltonian` |
| it is Hermitian whenever the old spectrum, the field and the attachment are | `isHermitian_layerSplit` |
| its trace is twice the old trace | `trace_layerSplit` |
| **it is a local Hamiltonian of the leaf-extended architecture** | `isLocalHamiltonian_layerSplit` |
| it lies in the architecture's Hermitian local-Hamiltonian space | `layerSplit_mem_hermitianLocalHamiltonianSubmodule` |
| **and in its trace-zero part when the old spectrum is traceless** | `layerSplit_mem_traceless` |

So the abstract split system of Lemma A1 is a physical onsite-plus-edge Hamiltonian of the
architecture obtained by attaching one qubit at the parent site: no further analysis is needed --
every analytic and algebraic step of Lemma A1 and Lemma A2 is proved.

After that, Theorem A follows by the already-formal chain: `quadraticRateDefect_smul` for `(13)`,
`realMvPolynomial_eq_zero_of_eqOn_zero_isOpen` and `exists_eqOn_zero_of_finsetProd_eqOn_zero` for
`(14)`, and `localExtension_quadraticRate_eq_zero` for Lemma A2.

## Lean progress -- the Theorem A assembly layer (2026-08-19)

Three new modules turn the already-formal algebraic ingredients into the exact shape the
globalisation `(14)` needs.  They mirror the *linear* machine of the parent card
(`AnalyticEscapeGenericityTransfer`, `PolynomialHermitianMatrixProjectiveGenericity`), which is
what makes the quadratic case an assembly rather than a new theory.

`formal/GaloisForLFunctions/HTGeometry/QuadraticRateOrbitPolynomialField.lean` (new,
umbrella-wired, axiom-clean) repeats the labeling-orbit construction over an **arbitrary field of
characteristic zero**.  This is not cosmetic: the rational module cannot state `(13)`, because the
multiple there is `κ = b²` with `b` the constant value of the projective action on the sphere
patch, an arbitrary real number, while the characteristic-coefficient pullback used by the
genericity machine lives over `ℂ`.

| Card item | Declaration |
|---|---|
| the relation `(∑ c_iX_i)² − κ∑X_i²` over any field | `fieldQuadraticRateRelationPolynomial` |
| **the symmetrised obstruction `(14)`**, the product over every labeling | `fieldQuadraticRateOrbitPolynomial`, `fieldQuadraticRateOrbitValue` |
| its factors are the relabelled relations, so it vanishes exactly when some labeling holds | `fieldQuadraticRateOrbitValue_factor`, `fieldQuadraticRateOrbitValue_eq_zero_iff` |
| over the reals the factors are exactly the quadratic-rate defects | `fieldQuadraticRateOrbitValue_real_eq_zero_iff` |
| **the obstruction is symmetric**, hence a polynomial in the characteristic coefficients | `fieldQuadraticRateOrbitPolynomial_isSymmetric`, `fieldQuadraticRateCoefficientPolynomial`, `esymmAlgHom_fieldQuadraticRateCoefficientPolynomial`, `eval_fieldQuadraticRateCoefficientPolynomial_esymm` |
| **the relation is a nonzero polynomial** unless the multiple and the packet both vanish | `fieldQuadraticRateRelationPolynomial_eq_zero_iff` |
| hence so are the orbit and coefficient obstructions | `fieldQuadraticRateOrbitPolynomial_ne_zero`, `fieldQuadraticRateCoefficientPolynomial_ne_zero` |

Characteristic zero is used exactly once, to divide the cross term of the two-level test by two.

`formal/GaloisForLFunctions/HTGeometry/QuadraticRateMatrixObstruction.lean` (new, umbrella-wired,
axiom-clean) descends the obstruction to the Hamiltonian parameters.

| Card item | Declaration |
|---|---|
| elementary symmetric evaluation does not see the coefficient field | `eval₂_esymm_rat_eq_complex` |
| **the obstruction pulled through the characteristic coefficients of a polynomial matrix family** | `quadraticRateObstructionPullback` |
| **it evaluates to the orbit obstruction of the root packet** at every parameter with a full simple spectrum | `eval_quadraticRateObstructionPullback` |
| **one complex parameter where it survives beats every real open set**: the real and imaginary parts are real polynomials, and a nonzero real polynomial cannot vanish on a nonempty open set | `exists_mem_eval_quadraticRateObstructionPullback_ne_zero` |

`formal/GaloisForLFunctions/HTGeometry/QuadraticRateAnalyticEscape.lean` (new, umbrella-wired,
axiom-clean) supplies the complex parameter from one analytic chart.

| Card item | Declaration |
|---|---|
| the `σ`-relabelled relation of an analytic branch family | `permutedAnalyticQuadraticRate`, `fieldQuadraticRateOrbitValue_branch` |
| every labeling factor is analytic on the chart | `analyticOnNhd_permutedAnalyticQuadraticRate` |
| **chart escape**: if no single labeling holds identically on a connected chart, the orbit obstruction is somewhere nonzero there | `exists_fieldQuadraticRateOrbitValue_ne_zero_of_analytic` |
| **the complex witness** for the parameter-space argument | `exists_eval_quadraticRateObstructionPullback_ne_zero_of_analyticBranchEscape` |
| **nowhere flatness**: the obstruction is nonzero somewhere inside every nonempty open set of real parameters | `exists_mem_eval_quadraticRateObstructionPullback_ne_zero_of_analyticBranchEscape` |

The chain `(13) → (14) → (6)` is therefore complete *given one input*: for every labeling `σ`, a
chart point at which the `σ`-relabelled quadratic-rate relation fails.  That input is Lemma A2 in
contrapositive form, and `localExtension_quadraticRate_eq_zero` already proves it under its
hypothesis `hL` -- that the uncoupled action `L₀` is not identically zero in the new local field.

### What remains for Theorem A

1. **The `¬hL` branch.**  If `L₀ ≡ 0` then `(11)` forces `κ = 0` and the identity degenerates to a
   *linear* relation among the eigenbranches, which the parent card's affine independence (trace is
   the only relation) kills.  What is missing is the Lean bridge from the parent card's
   linear-relation escape to this branch.
2. **The induction bookkeeping.**  Assembling the closed cycle
   `exists_covering_endpoint_probe → eventually_forall_layerGerm_endpoint_ne_zero →
   eventually_forall_layerReducedTransition_ne_zero` into a witness at every qubit number,
   carrying simplicity and distinct ordered gaps along -- both are open conditions at small
   coupling, and both hold for all but finitely many split fields.

## Lean progress -- the degenerate branch of Lemma A2 is closed

`formal/GaloisForLFunctions/HTGeometry/LocalExtensionQuadraticRateFlatCollapse.lean` (new,
umbrella-wired, axiom-clean) removes the `hL` hypothesis from Lemma A2.  Item 1 of the previous
"what remains" is therefore done.

| Card item | Declaration |
|---|---|
| a crown-constant zero-sum packet on the split labels vanishes | `crossPairConstant_eq_zero_of_sum_zero` |
| **`(10)` isolated**: the second-order response of the extension is the crown pole packet | `localExtension_secondDeriv_sum` |
| **the degenerate identity**: a vanishing square of the spectral action makes the pole packet vanish at every admissible local field | `localExtension_packet_eq_zero_of_flatSquare` |
| **Lemma A2, degenerate branch**: `L₀ ≡ 0` still forces `c = 0` | `localExtension_quadraticRate_eq_zero_of_flat` |
| **Lemma A2, unconditional** | `localExtension_quadraticRate_eq_zero_unconditional` |

The mechanism is the one the card describes and is now fully formal.  If `L₀ ≡ 0` the key
identity `L₀(z)·∂²ₓL(z,0) = κ Q_V` degenerates to `κ Q_V = 0`, so a probe with nonzero rate forces
`κ = 0`; the quadratic-rate identity then reads `(∑ cᵢλᵢ)² = 0`, hence `∑ cᵢλᵢ = 0` on a whole
neighbourhood of the uncoupled point, hence its second derivative vanishes.  That second
derivative is the *same* simple-pole packet, now paired with the **constant** multiplier one.  A
constant nonzero multiplier has no root, so `affinePole_support_subsingleton` leaves *no*
exceptional ordered pair at all -- strictly better than the generic branch -- and the crown graph
collapses every layer coefficient; the zero sum finishes.

The only remaining hypothesis is `Q_V ≠ 0`, which is the statement that the probe `V_A = A ⊗ X`
carries a nonzero Hilbert--Schmidt rate.  It is not a restriction: a probe with zero rate is the
zero probe, which no endpoint-complete family uses.

Axiom audit: `propext`, `Classical.choice`, `Quot.sound` only, for every declaration above and
for the three assembly modules of the previous section.

### What remains for Theorem A

Only the induction bookkeeping: assembling
`exists_covering_endpoint_probe → eventually_forall_layerGerm_endpoint_ne_zero →
eventually_forall_layerReducedTransition_ne_zero` into a witness at every qubit number, carrying
simple spectrum and distinct ordered gaps along the extension.  Both are open conditions at small
coupling and hold for all but finitely many split fields, so the argument is a genericity
bookkeeping step over assets that are all already formal.

### The remaining gap, located exactly

`exists_localField_quadraticRate_not_eventually` (same module) is the contrapositive interface:
a nonzero zero-sum packet cannot satisfy the quadratic-rate identity throughout a one-qubit
extension slice, so some admissible local field escapes it.  That is precisely the `hlabel`
hypothesis of `exists_mem_eval_quadraticRateObstructionPullback_ne_zero_of_analyticBranchEscape`,
read inside the extension slice.  What it needs, and all that Theorem A now needs, is a witness
with **full endpoint completeness**:

`hM : ∀ α β, α ≠ β → M α β * M β α ≠ 0`.

This is where the quadratic case genuinely parts from the parent card.  The parent card's witness
is a `GoodObserverSpectralSystem`, whose `HermitianObserverFamilyGood` field asks only that the
transition support graph be **preconnected and non-bipartite** -- enough for the linear
affine-independence residue argument, because a spanning connected non-bipartite graph already
kills a linear relation.  The quadratic crown argument uses *every* ordered pair, so it needs the
support graph to be **complete**.  That is exactly Lemma A1 of this card, and it is the reason
Lemma A1 exists.

So the three items are:

1. **Base case.**  A two-qubit traceless local Hamiltonian with simple spectrum, distinct nonzero
   ordered gaps, and a *complete* endpoint transition graph.  The card's argument is genericity:
   the squared Hilbert--Schmidt norm of `Tr_ū |ψ_β⟩⟨ψ_α|` is a nonzero real-analytic function of
   the eigenbasis and there are finitely many pairs.  `reducedTransition_eq_zero_iff` already
   reduces completeness to that single nonvanishing condition, and
   `exists_probeCombination_ne_zero` already supplies "a nonzero polynomial over `ℂ` has a
   nonvanishing point".
2. **Induction.**  `exists_covering_endpoint_probe → eventually_forall_layerGerm_endpoint_ne_zero`
   is the closed cycle; simplicity and distinct ordered gaps are open conditions at small coupling
   and hold off a finite set of split fields.
3. **Slice plumbing.**  Identify `∑ᵢ λᵢ(g)² = Tr((H + gV)²)/D` for the full simple root packet, so
   that the chart identity really has the shape `κ (Q₀(z) + g² Q_V)`; `trace_pow_eq_sum_eigenvalues_pow`
   is the Hermitian case of that bridge.

Nothing else in the chain `(6) ← (13) ← (14)` is open.

## Lean progress -- the base case of Lemma A1 is closed

`formal/GaloisForLFunctions/HTGeometry/BellEndpointCompleteBasis.lean` (new, umbrella-wired,
axiom-clean) supplies the two-qubit endpoint-complete witness, and does it without any case
analysis over the twelve ordered pairs.

The observation that removes the case analysis is that reshaping a bipartite vector into a matrix
turns the endpoint criterion into a product:

`R(ψ, φ) = reshape φ · (reshape ψ)ᴴ`.

So a basis every member of which reshapes to a *nonzero multiple of a unitary* -- a maximally
entangled basis -- is endpoint complete outright, because a product of an invertible matrix with
an invertible matrix is nonzero.  The Bell basis is exactly such a basis: the reshape of the Bell
vector labelled `(a, b)` is `2^{-1/2}` times the unitary `i ↦ (-1)^{a i}` supported on
`k = i ⊕ b`.

| Card item | Declaration |
|---|---|
| the reshape of a bipartite vector | `bipartiteReshape` |
| **the reduced transition is a product of reshapes** | `reducedTransition_eq_reshape` |
| **maximally entangled vectors are endpoint visible** | `reducedTransition_ne_zero_of_unitary_reshape` |
| the sign `(-1)^{a i}` and the Bell reshapes | `boolSign`, `bellReshape`, `bellReshape_conjTranspose_mul` |
| the Bell vectors | `bellVector`, `bipartiteReshape_bellVector` |
| **endpoint completeness of the Bell basis**, for every ordered pair | `reducedTransition_bellVector_ne_zero` |
| **the Bell family is orthonormal** | `bellMatrix`, `bellMatrix_conjTranspose_mul`, `bellMatrix_mul_conjTranspose` |
| the two-qubit Hamiltonian with a prescribed spectrum in that eigenbasis | `bellHamiltonian`, `bellHamiltonian_isHermitian`, `bellHamiltonian_trace`, `bellHamiltonian_mul_bellMatrix` |
| **the base case of Lemma A1**: for every prescribed real spectrum there is a Hermitian two-qubit Hamiltonian with that spectrum in an orthonormal eigenbasis every ordered pair of which is endpoint visible | `exists_endpointComplete_twoQubit_witness` |

Choosing the spectrum to be a Sidon set shifted to trace zero -- for instance `{0,1,3,7} − 11/4`,
whose six positive differences `1,2,3,4,6,7` are distinct -- makes the witness simple with
distinct nonzero ordered gaps as well, so it satisfies every hypothesis of
`localExtension_quadraticRate_eq_zero_unconditional` at the base of the induction.  Note also that
for two qubits every `4 × 4` Hermitian matrix is an onsite-plus-edge Hamiltonian of the two-site
path, so the witness is automatically path-local.

Axiom audit: `propext`, `Classical.choice`, `Quot.sound`.

### What remains for Theorem A, after the base case

1. **The induction step's genericity bookkeeping.**  `eventually_forall_layerGerm_endpoint_ne_zero`
   already propagates endpoint completeness across one attached qubit for all small nonzero
   coupling.  What must be added is that simplicity and distinct nonzero ordered gaps also
   survive: both are open conditions at zero coupling and hold for all but finitely many split
   fields, so this is a finite-avoidance argument over assets that are already formal.
2. **Slice plumbing.**  Identify `∑ᵢ λᵢ(g)² = Tr((H + gV)²)` for the full simple root packet, so
   the chart identity has the shape `κ (Q₀(z) + g² Q_V)` that
   `localExtension_quadraticRate_eq_zero_unconditional` consumes;
   `trace_pow_eq_sum_eigenvalues_pow` is the Hermitian case of that bridge.

### Correction to item 2 of the previous list

Item 2 above -- "identify `∑ᵢ λᵢ² = Tr(H²)`" -- is not actually needed, and asking for it would be
a detour: mathlib has the power sum of the roots only at order one
(`Matrix.trace_eq_sum_roots_charpoly`), and the order-two case is a genuine mathlib gap requiring
either the second Newton identity for the characteristic polynomial or Schur triangulation,
neither of which is available.

The detour is avoidable because the card's rate is `Q(H) = D^{-1} Tr(H²)` in the first place, not
the spectral power sum.  Along the extension slice `H(z,g) = diag(layerSplitEnergy E z) + g·V`
with `V = layerCrossPerturbation M`,

`Tr(H(z,g)²) = Tr(diag(...)²) + 2g·Tr(diag(...)·V) + g²·Tr(V²) = Q₀(z) + g² Q_V`,

because `V` has zero diagonal -- which is already the corpus lemma
`layerCrossPerturbation_diagonal`.  So the shape `κ(Q₀(z) + g² Q_V)` that
`localExtension_quadraticRate_eq_zero_unconditional` consumes is a **direct matrix computation**,
with no eigenvalues involved.

What must change instead is the shape of the labeling-orbit obstruction.  It should carry the rate
as its own variable:

`(∑ᵢ cᵢ Xᵢ)² − Y`   in   `MvPolynomial (I ⊕ Unit) K`,

symmetrised over permutations of the `X`'s only.  The product is then symmetric in `X` for each
fixed `Y`, so it descends to a polynomial in the elementary symmetric functions of the spectrum
*and* `Y`; substituting the characteristic coefficients for the former and `κ·Tr(H²)/D` for the
latter gives a polynomial in the matrix entries exactly as before.  This is a bounded refactor of
`QuadraticRateOrbitPolynomialField` and `QuadraticRateMatrixObstruction`, and it removes the last
analytic dependency from the globalisation step.

### The refactor is already half done

`QuadraticRateOrbitPolynomialField` now works over an arbitrary **characteristic-zero integral
domain**, not just a field: the construction, the symmetry, the descent through
`MvPolynomial.esymmAlgEquiv` (which needs only `CommRing`) and the non-vanishing all go through,
because the only arithmetic used is "two is not a zero divisor" and "a square vanishes only at
zero".  That is what makes the rate-as-variable version free rather than a rewrite: instantiate
the same construction at

`K := MvPolynomial θ ℂ`,   `c := fun i => C (c₀ i)`,   `κ := C κ₀ · (M * M).trace`,

where `(M * M).trace` is literally `Tr(H²)` as a polynomial in the parameters.  Then
`fieldQuadraticRateCoefficientPolynomial` already lives over the parameter ring and
`MvPolynomial.aeval (matrixCharacteristicElementaryPolynomial M)` already substitutes the
characteristic coefficients, so the pullback is the same definition read one level up.

What that instantiation still needs is base-change naturality: for a ring hom `f : K →+* L`,
`map f` should commute with the relation, the labeling orbit, and the descent, so that evaluating
the parameters afterwards reproduces the orbit obstruction of the root packet.  The first two are
immediate from the formulas; the third is naturality of `esymmAlgEquiv`, which mathlib does not
state.

### Correction to item 1: the induction cannot preserve distinct gaps *uncoupled*

Item 1 above asked to propagate "simple spectrum and distinct nonzero ordered gaps" across the
attached qubit.  Simplicity does propagate for all but finitely many split fields, but distinct
ordered gaps **never** hold for the uncoupled split spectrum: the levels are `E_α ± z/2`, so the
old gap `E_β − E_α` occurs twice, once inside each layer.  Any plan that tries to carry `hgap`
through the uncoupled extension is therefore wrong.

The coupling is what breaks that degeneracy, and the correct induction step is an intersection
rather than a propagation:

* the leaf-extended architecture has a **dense, residual, full-measure** maximally projective set
  (`PhysicallyRealizedTensorTreeSystem.tracelessLocalHamiltonianMaximalSet_dense_residual_fullMeasure`),
  and maximal projective rank already gives simplicity and distinct nonzero ordered gaps
  (`MaximallyProjectiveEnergy.injective`, `maximallyProjectiveEnergy_orientedGap_injective`);
* endpoint completeness holds at some small nonzero coupling
  (`eventually_forall_layerGerm_endpoint_ne_zero`) and is an **open** condition
  (`eventually_forall_layerReducedTransition_ne_zero`);
* a nonempty open set meets a dense set, so the extended witness exists.

So the induction step is a two-line intersection once the two inputs are stated in the same
parameter space.  The remaining work in item 1 is exactly that matching, not a new genericity
argument.

## Lean progress -- the rate is now a variable (2026-08-19)

The previous entry located the last obstruction exactly:

> "What that instantiation still needs is base-change naturality: ... the third is naturality of
> `esymmAlgEquiv`, which mathlib does not state."

Both halves are now built, umbrella-wired and axiom-clean.

`formal/GaloisForLFunctions/HTGeometry/SymmetricDescentBaseChange.lean`

| Item | Declaration |
|---|---|
| the substitution `Xᵢ ↦ eᵢ₊₁` is natural in the coefficient ring | `map_esymmAlgHom` |
| it is injective, being half of an algebra equivalence | `injective_esymmAlgHom` |
| **naturality of the symmetric-polynomial descent** -- the named mathlib gap | `map_esymmAlgEquiv_symm` |
| the quadratic-rate relation and its labeling orbit are natural | `map_fieldQuadraticRateRelationPolynomial`, `map_fieldQuadraticRateOrbitPolynomial` |
| **the characteristic-coefficient obstruction is natural** | `map_fieldQuadraticRateCoefficientPolynomial` |

The proof of naturality never touches the construction of the inverse: the forward substitution is
visibly natural because the elementary symmetric polynomials have coefficients `1`, and the forward
map is injective, so two representatives with the same image coincide.

`formal/GaloisForLFunctions/HTGeometry/VariableRateMatrixObstruction.lean`

| Card item | Declaration |
|---|---|
| the obstruction built over `MvPolynomial θ ℂ`, with the rate one of its elements | `variableRateObstructionPullback` |
| **it evaluates to the orbit obstruction of the root packet at the rate evaluated there** | `eval_variableRateObstructionPullback` |
| a complex polynomial nonzero at one complex point is nonzero somewhere in every nonempty real open set | `exists_mem_eval₂_ne_zero_of_exists` |
| **one complex witness beats every real open set, at a moving rate** | `exists_mem_eval_variableRateObstructionPullback_ne_zero` |
| **the witness form**: a single simple root packet on which no relabeled quadratic-rate relation holds forces the same failure somewhere in every nonempty open set of real parameters | `exists_mem_forall_relabelled_quadraticRate_ne_zero` |

This is `(14)`, the symmetrisation `𝒢_{c,b}`, with `b² Q(H)` carried as the polynomial `κ` rather
than as a constant -- exactly the shape the proof of Theorem A needs, since `Q(H) = D^{-1} Tr(H²)`
moves with the Hamiltonian.  The user of the theorem supplies `κ := C(κ₀/D) · Tr(M²)`, which is a
direct matrix computation in the parameters with no eigenvalues involved.

Axiom audit for all listed declarations: `propext`, `Classical.choice`, `Quot.sound`.

### What remains for Theorem A

1. **The induction step's parameter matching** (unchanged): state the dense/residual maximally
   projective set and the open endpoint-completeness condition in one parameter space and
   intersect.
2. **The witness feed**: supply `exists_mem_forall_relabelled_quadraticRate_ne_zero` with the
   Lemma A2 chart -- the two-qubit Bell witness at the base, the layer extension at the step -- as
   its `z₀`, `energy₀`, `hfail` inputs.

## Lean progress -- the globalisation step of Theorem A is assembled (2026-08-19)

Two further modules complete the chain from Lemma A2 to the boxed statement `(6)`, at the moving
rate `κ Q(H)`.  Both are new, umbrella-wired and axiom-clean.

`formal/GaloisForLFunctions/HTGeometry/VariableRateAnalyticEscape.lean`

| Card item | Declaration |
|---|---|
| the `σ`-relabeled relation at a moving rate | `permutedAnalyticVariableRate` |
| the orbit value is the product of those factors | `fieldQuadraticRateOrbitValue_variableRate` |
| each factor is analytic when the rate is | `analyticOnNhd_permutedAnalyticVariableRate` |
| **evaluation of a multivariate polynomial is analytic in its parameters** | `analyticOnNhd_evalMvPolynomial` |
| **chart escape at a moving rate** | `exists_fieldQuadraticRateOrbitValue_ne_zero_of_analyticVariableRate` |
| the complex witness | `exists_eval_variableRateObstructionPullback_ne_zero_of_analyticBranchEscape` |
| **nowhere flatness at a moving rate** | `exists_mem_eval_variableRateObstructionPullback_ne_zero_of_analyticBranchEscape` |

`formal/GaloisForLFunctions/HTGeometry/LabelOrbitPacketEscape.lean`

| Card item | Declaration |
|---|---|
| **the `σ`-labeled factor of `c` is the unlabeled relation of `c ∘ σ⁻¹`**, so a rigidity statement over all nonzero zero-sum packets is already an escape for every labeling | `forall_perm_exists_permutedAnalyticVariableRate_ne_zero` |
| **the globalisation step**: inside every nonempty open set of real parameters there is a point at which no relabeling of the quadratic-rate relation holds, for any simple root packet over it | `exists_mem_forall_relabelled_quadraticRate_ne_zero_of_packetEscape` |

The second theorem is exactly the proof of Theorem A as written on this card -- symmetrise `(13)`
over labelings to get `(14)`, descend to the characteristic coefficients, and conclude by the
identity theorem on the witness chart -- with three differences from the earlier constant-rate
version, all of them removals: the rate is a polynomial in the parameters rather than a constant,
so `κ Q(H)` is admissible; the escape hypothesis is a statement about *packets*, which is literally
Lemma A2, rather than about labelings; and the conclusion is stated for every simple root packet
over the produced real point, so no eigenvalue-selection is needed downstream.

### What remains for Theorem A

1. **The chart.**  Produce `U ⊆ ℂ^m` connected open with analytic simple eigenbranches over the
   one-qubit extension slice, and feed `exists_localField_quadraticRate_not_eventually` to it as
   `hpacket`.  This is the `(z, g)`-to-`Fin m → ℂ` bridge -- coordinates, not mathematics.
2. **The induction step's parameter matching**: state the dense/residual maximally projective set
   and the open endpoint-completeness condition in one parameter space and intersect.

## Lean progress -- the slice rate has the shape `Q₀(z) + g² Q_V` (2026-08-19)

`formal/GaloisForLFunctions/HTGeometry/LayerSliceQuadraticTrace.lean` (new, umbrella-wired,
axiom-clean) settles the "slice plumbing" item, as the card predicted, by a direct matrix
computation with no eigenvalues in it.

| Card item | Declaration |
|---|---|
| the trace of a square as a double sum | `trace_sq_eq_sum` |
| the cross perturbation has zero trace against a diagonal, from either side | `trace_diagonal_mul_layerCrossPerturbation`, `trace_layerCrossPerturbation_mul_diagonal` |
| the diagonal part contributes its squared energies | `trace_diagonal_sq` |
| **`Tr H(z,g)² = Q₀(z) + g² Q_V`** -- no linear term in the coupling | `trace_sq_layerExtensionSlice` |
| **`Q_V = 2 ∑_{a,b} M_{ab} M_{ba}`** | `trace_sq_layerCrossPerturbation` |
| **`Q_V ≠ 0` for a nonzero Hermitian channel** -- the `hQv` hypothesis of Lemma A2 | `trace_sq_layerCrossPerturbation_ne_zero` |

The linear term vanishes for the reason the card gives: `layerCrossPerturbation M` has zero
diagonal, so both `Tr(D·V)` and `Tr(V·D)` vanish termwise.  The residual energy is
`2 ∑_{a,b} M_{ab} M_{ba} = 2 ∑_{a,b} |M_{ab}|²` for Hermitian `M`, hence strictly positive unless
the channel is zero, which is exactly the nondegeneracy Lemma A2 asks for.

Axiom audit: `propext`, `Classical.choice`, `Quot.sound`.
