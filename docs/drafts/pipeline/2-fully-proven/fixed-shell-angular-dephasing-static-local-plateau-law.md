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

### What remains for Theorem A

1. homogeneity of the eigenvalue branches, turning flatness of `phi_k` on a sphere patch into the
   cone identity `(13)`;
2. gluing: a polynomial vanishing on a nonempty open set of parameters vanishes identically
   (`HTGeometry.AlgebraicIndependenceFromDifferentials.mvPolynomial_eq_zero_of_eqOn_zero_isOpen`),
   and a finite product of analytic functions on a connected chart vanishes only if one factor
   does (`HTGeometry.DirectionalMeromorphicField.analyticOnNhd_domain'`);
3. Lemma A1's endpoint-complete witness -- the only remaining *input* to Lemma A2 -- on top of the
   corpus's `HTGeometry.CompleteObserverSpectralSeed`, `HTGeometry.ChartProbeFamilyReduction` and
   the already-formalized `exists_uniformQubitChainMaximalRank_dense_residual_fullMeasure` of the
   parent card, which supplies simple spectrum, `MaximallyProjectiveEnergy` and
   `maximallyProjectiveEnergy_orientedGap_injective` (distinctness of all nonzero ordered gaps --
   exactly the `hgap` hypothesis of `localExtension_quadraticRate_collapse`).
