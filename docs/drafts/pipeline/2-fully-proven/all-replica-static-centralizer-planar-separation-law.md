# All-replica static-centralizer / planar-separation law

- **ID:** `all-replica-static-centralizer-planar-separation-law`
- **Stage:** 2 -- fully proved on paper
- **Type:** theorem / failed-transfer classification / positive static replacement
- **Parents:**
  `all-replica-one-step-local-pauli-hall-saturation-law.md`,
  `../3-formalized/one-replica-local-pauli-planar-cavity-decay.md`, and
  `fixed-shell-angular-dephasing-static-local-plateau-law.md`
- **Status:** `[PAPER-PROVED] [FRONTIER ADVANCE] [APPLICATION NOVELTY UNVERIFIED] [LEAN DEFERRED]`
- **Date:** 2026-08-10

## Public sentence

A static Hamiltonian and a refreshed Gaussian evolution have different replica vacua: free planar
noise forgets every nonuniversal mode, whereas one fixed Hamiltonian permanently retains a large,
Hamiltonian-dependent centralizer.  Averaging rotates those hidden centralizers into a collision
plateau; it never turns the static problem into the zero-decay planar problem.

## Why this theorem is needed

The planar route had two separately proved inputs:

1. at one replica, a full local-Pauli matrix-semicircle pencil has absolutely continuous spectral
   law and a vacuum-compressed propagator which decays to zero; and
2. at every finite replica order, the complete graph-local replicated Pauli commutator family is
   rank nondecreasing after quotienting the exact global collective commutant.

It is tempting to compose these facts and treat all-replica planar decay as the reference estimate
for one ordinary static Gaussian Hamiltonian.  That transfer is false for an exact structural
reason.  The quotient removes the vectors fixed by **every** local Hamiltonian, but every individual
Hamiltonian has a much larger moving kernel.  This card proves both sides and identifies the
correct static replacement.

## Setup

Let `K=C^D`, let `r>=1`, and put

\[
 K_r=K^{\otimes r},\qquad \mathcal V_r=\operatorname{End}(K_r).            \tag{1}
\]

For a Hermitian matrix `H`, define its collective replica Hamiltonian and Liouvillian

\[
 H_{[r]}=\sum_{a=1}^r
 I^{\otimes(a-1)}\otimes H\otimes I^{\otimes(r-a)},
 \qquad L_{H,r}=\operatorname{ad}_{H_{[r]}}.                               \tag{2}
\]

The Hilbert--Schmidt inner product makes `L_(H,r)` self-adjoint.  Let

\[
 P_{H,r}=\mathbf1_{\{0\}}(L_{H,r})                                        \tag{3}
\]

be orthogonal projection onto the quenched centralizer

\[
 \mathcal C_{H,r}=\ker L_{H,r}=\{X:[H_{[r]},X]=0\}.                        \tag{4}
\]

Let `N_(D,r)` be the commutant of `U^(tensor r)` for every `U in U(D)`, let `Pi_(D,r)` be its
orthogonal projection, and put

\[
 Q_{D,r}=I-\Pi_{D,r}.                                                       \tag{5}
\]

The global replica permutations span `N_(D,r)`.  In the stable range `r<=D`,

\[
 d_{D,r}:=\dim\mathcal N_{D,r}=r!.                                         \tag{6}
\]

For every `H`,

\[
 \mathcal N_{D,r}\subseteq\mathcal C_{H,r}.                               \tag{7}
\]

Hence `P_(H,r)` commutes with `Pi_(D,r)` and restricts to a projection on `Q_(D,r)V_r`.

## Conjecturing protocol

### C0 -- all-replica Hall fullness transfers planar decay to static disorder

**Verdict:** `[FALSIFIED]`.

The all-replica Hall theorem does imply fullness for the free matrix-semicircle pencil on the
global-commutant quotient.  It does not make the classical pencil `L_(H,r)` invertible for a fixed
coefficient realization.  Every such pencil has the centralizer `(4)`, whose dimension is already
`D` at one replica.  These kernels move with `H`, so their intersection can equal `N_(D,r)` even
though every individual kernel is much larger.

### C1 -- quotienting the global permutation algebra removes the static fixed modes

**Verdict:** `[FALSIFIED]`.

At one replica this quotient removes only the scalar identity.  For simple `H`, its commutant has
dimension `D`, leaving `D-1` zero modes on the traceless quotient.  At higher replica order the
remaining dimension is the exact histogram-collision count below, minus the global permutation
dimension.

### C2 -- the static propagator decays after subtracting its quenched centralizer

**Verdict:** `[FALSIFIED IN QUENCHED NORM; PROVED AFTER SIGNED ENSEMBLE AVERAGING]`.

For fixed `H`, the centered propagator is unitary on `C_(H,r)^perp`, so neither its operator norm nor
its Hilbert--Schmidt norm decays.  For the ordinary fixed-shell local ensemble, however, every
nonzero spectral action is nowhere flat.  Signed angular averaging therefore kills all centered
matrix coefficients and leaves exactly the averaged quenched centralizer.

This is the positive survivor.

## Theorem A -- exact quenched centralizer decomposition and norm obstruction

For every finite Hermitian `H`, every `r>=1`, and every real `t`,

\[
 \boxed{
 e^{-itL_{H,r}}
 =P_{H,r}+e^{-itL_{H,r}}(I-P_{H,r}).}                                     \tag{8}
\]

If `C_(H,r)^perp` is nonzero, then

\[
 \boxed{
 \|e^{-itL_{H,r}}-P_{H,r}\|_{\rm op}=1,\qquad
 \|e^{-itL_{H,r}}-P_{H,r}\|_{\rm HS}^2
 =D^{2r}-\dim\mathcal C_{H,r}.}                                           \tag{9}
\]

Thus no quenched norm contraction exists, at any time, even after exact return/zero-mode removal.
Only signed averaging of the oscillatory complement can decay.

### Proof

`P_(H,r)` is the zero spectral projection of the self-adjoint matrix `L_(H,r)`, so it commutes with
the full functional calculus and `exp(-itL)P=P`.  This proves `(8)`.  On the orthogonal complement
of the zero eigenspace, `exp(-itL)` is unitary.  Its operator norm is therefore one and its squared
Hilbert--Schmidt norm is the dimension of that complement, proving `(9)`.  `square`

## Theorem B -- exact all-replica moving-kernel multiplicity

Assume that `H` has maximal projective spectral rank.  Write its distinct energies as
`E_1,...,E_D`.  For a histogram

\[
 k=(k_1,\ldots,k_D)\in\mathbb N^D,\qquad |k|=r,                            \tag{10}
\]

put

\[
 m_k={r!\over\prod_jk_j!},\qquad
 \kappa_{D,r}=\sum_{|k|=r}m_k^2.                                          \tag{11}
\]

Then

\[
 \boxed{\dim\mathcal C_{H,r}=\kappa_{D,r}.}                               \tag{12}
\]

Consequently the quenched zero-mode dimension on the global-commutant quotient is

\[
 \boxed{
 \dim(\mathcal C_{H,r}\cap Q_{D,r}\mathcal V_r)
 =\kappa_{D,r}-d_{D,r}.}                                                   \tag{13}
\]

In the stable range this is `kappa_(D,r)-r!`.  At one replica,

\[
 \kappa_{D,1}=D,\qquad
 \dim(\mathcal C_{H,1}\cap\mathcal N_{D,1}^\perp)=D-1.                   \tag{14}
\]

The normalized full-space kernel trace is exactly the uniform replica collision floor:

\[
 \boxed{
 {\kappa_{D,r}\over D^{2r}}
 =\Pr\{\operatorname{hist}(X_1,\ldots,X_r)
       =\operatorname{hist}(Y_1,\ldots,Y_r)\},}                           \tag{15}
\]

where the two samples are independent and uniform on `{1,...,D}`.

### Proof

The tensor eigenvector indexed by `alpha=(alpha_1,...,alpha_r)` has collective energy
`sum_a E_(alpha_a)`.  Maximal projective rank says equality of two such sums holds exactly when the
two tuples have the same histogram.  The eigenspace associated with histogram `k` therefore has
multiplicity `m_k`.  The commutant of a Hermitian matrix with eigenspace multiplicities `m_k` has
dimension `sum_k m_k^2`, proving `(12)`.

Inclusion `(7)` and nested orthogonal projections give `(13)`.  Counting two independent ordered
tuples by their common histogram gives `(15)`.  `square`

Two useful universal estimates follow immediately:

\[
 D^r\leq\kappa_{D,r}\leq r!D^r,                                          \tag{16}
\]

because, after the first tuple is fixed, at least itself and at most its `r!` permutations have the
same histogram.  If `r<=D`, the all-distinct histograms give the sharper lower bound

\[
 \kappa_{D,r}\geq (D)_r r!,\qquad (D)_r=D(D-1)\cdots(D-r+1).              \tag{17}
\]

For fixed `r` and growing `D`, `(15)` is therefore asymptotic to `r!/D^r`.

## Theorem C -- ordinary static-local annealed propagation converges to the moving-kernel average

Let `n>=2`, `D=2^n`, and let `H(theta)` range over the unit coefficient sphere of the complete
one-site plus nearest-neighbour two-site Pauli family on the open qubit path.  Let `sigma` be
spherical probability measure.  For every fixed finite `r`, define

\[
 \mathcal U_r(t)
 =\int e^{-itL_{H(\theta),r}}\,d\sigma(\theta),\qquad
 \overline P_r
 =\int P_{H(\theta),r}\,d\sigma(\theta).                                 \tag{18}
\]

Then, on the global-commutant quotient,

\[
 \boxed{
 \|Q_{D,r}\mathcal U_r(t)Q_{D,r}
   -Q_{D,r}\overline P_rQ_{D,r}\|_{\rm op}
 \longrightarrow0
 \quad(|t|\to\infty).}                                                   \tag{19}
\]

No Haar eigenbasis, refreshed noise, random time, minimum gap, or random-matrix premise occurs.
The result holds for every finite replica order.  The convergence is qualitative and not uniform
in `n` or `r`.

### Proof

Outside the discriminant, cover the coefficient sphere by analytic simple-spectrum eigencharts.
On such a chart, expand a matrix coefficient of the replicated propagator in tensor eigenoperators:

\[
 \langle X,e^{-itL_{H(\theta),r}}Y\rangle
 =\sum_{\alpha,\beta}
   g_{\alpha,\beta}(\theta)
   e^{-it[\sum_aE_{\alpha_a}(\theta)-\sum_aE_{\beta_a}(\theta)]}.         \tag{20}
\]

The terms with equal histograms are exactly the matrix coefficient of `P_(H(theta),r)`.  Every
other phase is a nonzero balanced integer spectral action.  The fixed-shell nowhere-flat theorem
says that no such action is constant on a nonempty open eigenchart.  Its continuously weighted
pushforward is absolutely continuous; Riemann--Lebesgue makes the corresponding integral tend to
zero.

A partition of unity and removal of an arbitrarily small discriminant neighborhood justify the
chart sum.  There are finitely many tuple pairs at fixed `D,r`, so every matrix coefficient of the
difference in `(19)` tends to zero.  Finite dimensionality upgrades entrywise convergence to
operator-norm convergence.  `square`

## Theorem D -- the static plateau survives every global-commutant quotient

For almost every `theta`, the local fixed-shell Hamiltonian has maximal projective rank.  Therefore

\[
 \operatorname{Tr}_{Q\mathcal V_r}
 (Q_{D,r}\overline P_rQ_{D,r})
 =\kappa_{D,r}-d_{D,r}.                                                     \tag{21}
\]

Since the averaged projection is positive and the quotient dimension is `D^(2r)-d_(D,r)`,

\[
 \boxed{
 \|Q_{D,r}\overline P_rQ_{D,r}\|_{\rm op}
 \geq {\kappa_{D,r}-d_{D,r}\over D^{2r}-d_{D,r}}.}                       \tag{22}
\]

In particular,

\[
 \boxed{
 \|Q_{D,1}\overline P_1Q_{D,1}\|_{\rm op}\geq{1\over D+1}.}            \tag{23}
\]

### Proof

For almost every shell point, `(12)` holds.  Nestedness `(7)` makes
`Q P_(H,r) Q` an orthogonal projection of rank `kappa_(D,r)-d_(D,r)`.  Trace commutes with the
finite-dimensional Bochner integral, proving `(21)`.  A positive operator on an `N`-dimensional
space has largest eigenvalue at least its trace divided by `N`, proving `(22)` and `(23)`. `square`

## Theorem E -- all-replica planar decay and its exact nontransfer

Return to a connected qubit graph and the complete one-site plus graph-edge replicated Pauli
commutator family on `Q_(D,r)V_r`.  Give every generator used by the Hall theorem strictly positive
variance and form the free matrix semicircle

\[
 S_r^{\rm free}=\sum_p\sqrt{v_p}\,A_p^{(r)}\otimes s_p,qquad
 U_{0,r}^{\rm free}(t)=E_\Omega(e^{-itS_r^{\rm free}}).                    \tag{24}
\]

Then, for every finite `n,r`,

\[
 \boxed{\|U_{0,r}^{\rm free}(t)\|_{\rm op}\longrightarrow0.}             \tag{25}
\]

Nevertheless, for the ordinary static fixed-shell ensemble on the same quotient,

\[
 \boxed{
 \liminf_{|t|\to\infty}
 \|Q\mathcal U_r(t)Q-U_{0,r}^{\rm free}(t)\|_{\rm op}
 \geq {\kappa_{D,r}-d_{D,r}\over D^{2r}-d_{D,r}}>0.}                    \tag{26}
\]

### Proof

The all-replica local-Pauli Hall theorem is exactly rank nondecrease of the Hermitian pencil on
the quotient.  Kargin's full-matrix-semicircle theorem therefore gives purely absolutely
continuous scalar spectral law.  Faithfulness transfers absolute continuity to every vector
spectral measure; Riemann--Lebesgue and finite dimensionality prove `(25)`, exactly as in the
formalized one-replica proof.

Equations `(19)`, `(22)`, and `(25)`, followed by the reverse triangle inequality, prove `(26)`.
Thus even perfect all-replica planar decay cannot approximate the long-time static ensemble in
operator norm.  `square`

## What the law changes

The previous open-core language treated all-replica planar fullness as though it might become a
static-Hamiltonian mixing theorem after enough conditioning.  Equations `(19)`--`(26)` show that
this is structurally wrong:

1. **Free/refreshed reference:** remove the common collective commutant, then decay to zero.
2. **One static Hamiltonian:** remove the same common commutant, but retain a moving centralizer of
   exact dimension `kappa_(D,r)-d_(D,r)`.
3. **Static ensemble:** signed oscillatory modes dephase, while the moving centralizers average to
   the nonzero operator `bar P_r`.
4. **Replica collision floor:** the normalized trace of that moving kernel is exactly the
   histogram/permutation collision probability.

This is the operator-level reason refreshed random circuits and free cavities can mix to a common
fixed algebra while one time-independent Hamiltonian retains quenched spectral memory.  It also
explains why minimum gaps and common-kernel Hall rank were repeatedly insufficient: both ignore the
realization-dependent zero eigenspaces.

## Correct Brown--Susskind survivor

The theorem does not prove the circuit-complexity ramp.  It replaces an invalid transfer target by
the exact static one.

For the bounded complete circuit reporter `F_s` and a collision-good seed, define the conditional
completed-phase baseline

\[
 B_s(H)=\int_{\mathbb T^{D-1}}F_s(U_\varphi\psi)\,d\varphi.                \tag{27}
\]

Existing completed-phase incidence theorems bound `B_s(H)` through Brown depth.  Fixed-shell
angular dephasing proves only the qualitative statement

\[
 \int F_s(e^{-itH(\theta)}\psi)\,d\sigma(\theta)
 -\int B_s(H(\theta))\,d\sigma(\theta)\longrightarrow0.                   \tag{28}
\]

The exact remaining core is therefore:

> **Centralizer-centered Bellman dephasing conjecture.**  After one independently fixed
> return/shortcut-carrier excision, prove a Brown-time quantitative version of `(28)` for the
> zero-temperature gate reporter itself, uniformly through the geometric circuit-depth schedule.
> The estimate must center at the quenched completed-phase baseline `(27)`, not at zero and not at
> the free planar cavity.

This formulation retains the Hamiltonian-dependent circuit selector, the moving spectral
centralizer, fibre-sheet multiplicity, and occupied endpoint image.  A linear or absolute-value
bound on the centered quenched propagator cannot prove it because `(9)` is time-independent.

## Hostile audit

1. **No Brown ramp.**  Equation `(19)` is a fixed-`n,r` late-time limit.  It gives no effective
   onset, no rate uniform at `r=O(n)`, and no zero-temperature Bellman estimate.
2. **Operator average is not shortcut probability.**  The circuit target maximizer depends on the
   realized Hamiltonian.  Passing the maximum through the signed average is forbidden.
3. **The collision floor is known in scalar form.**  Histogram counting, time dephasing, spectral
   commutants, and isospectral twirling are classical.  Candidate new content is their exact
   operator-level composition with the ordinary fixed-shell local ensemble and the resulting
   all-replica planar-nontransfer theorem `(26)`.  Priority remains unverified.
4. **No claim for every local ensemble.**  Theorem C uses the proved nowhere-flat spectral-action
   property of the complete inhomogeneous nearest-neighbour Pauli shell.  Integrable,
   translation-invariant, or symmetry-constrained subfamilies can retain additional actions.
5. **Finite volume.**  No thermodynamic-limit, continuous-spectrum, gravity, or black-hole claim is
   made.
6. **Planar theorem uses an external structure theorem.**  Equation `(25)` uses Kargin's full
   matrix-semicircle absolute-continuity theorem.  The one-replica instance and its analytic
   infrastructure are already formalized internally; the all-replica composition is paper-only.
7. **Lean status.**  No equation from this card is authorized for a final manuscript until its
   exact finite-dimensional core is formalized after the active corpus refactor.

## External priority boundary

- Leone--Oliviero--Hamma and Oliviero--Leone--Caravelli--Hamma develop isospectral twirling and show
  that long-time probes depend on spectral and eigenvector data
  ([arXiv:2011.06011](https://arxiv.org/abs/2011.06011),
  [arXiv:2012.07681](https://arxiv.org/abs/2012.07681)).
- Matsoukas-Roubeas--Beau--Santos--del Campo interpret disorder/time averaging of spectral form
  factors as mixed-unitary dephasing channels
  ([arXiv:2307.04791](https://arxiv.org/abs/2307.04791)).
- Kargin characterizes full matrix semicircles and their absolutely continuous laws
  ([arXiv:2604.23089](https://arxiv.org/abs/2604.23089),
  [arXiv:2607.26222](https://arxiv.org/abs/2607.26222)).

These works make the separate twirling, dephasing, and free-semicircle ingredients literature.  The
targeted search found no theorem identifying the exact moving-centralizer trace `(21)` as the
nonvanishing obstruction to all-replica planar transfer for an ordinary fixed-shell local
Hamiltonian ensemble.  This is separation evidence, not a priority proof.

## Lean plan after refactor

1. finite spectral projection decomposition `(8)` and norm identities `(9)`;
2. histogram eigenspace and centralizer count `(11)`--`(15)`;
3. nested global-commutant projection and trace bound `(21)`--`(23)`;
4. abstract weighted nowhere-flat action lemma implying operator-norm annealed convergence `(19)`;
5. compose the existing all-replica Hall theorem with the matrix-semicircle analytic-law
   infrastructure for `(25)`;
6. package the planar/static separation `(26)` and audit axioms.

No Lean file or process was touched while the corpus refactor was active.

## Lean progress

Five new modules under `formal/GaloisForLFunctions/HTGeometry/`, all wired into the
`GaloisForLFunctions.HTGeometry` umbrella and all axiom-clean
(`[propext, Classical.choice, Quot.sound]`).  Everything below is stated for an arbitrary finite
index type, an arbitrary Hermitian generator and an arbitrary probability space of parameters, so
none of it is tied to the card's concrete Pauli shell.

### Theorem A -- `QuenchedCentralizerPropagatorSplit`

| Card item | Declaration |
|---|---|
| the orthogonal projection onto `ker L`, in the generator's own eigenbasis | `spectralKernelProjector`, `spectralKernelProjector_idem` |
| the propagator fixes the kernel projector | `unitaryEvolution_mul_spectralKernelProjector` |
| **`(8)`** `e^{-itL} = P + e^{-itL}(I-P)` | `unitaryEvolution_eq_spectralKernelProjector_add` |
| the centered propagator, in closed diagonal form | `unitaryEvolution_sub_spectralKernelProjector_eq` |
| **`(9)`, operator norm** `‖e^{-itL}-P‖ = 1` at every `t` | `l2_opNorm_unitaryEvolution_sub_spectralKernelProjector` |
| **`(9)`, Hilbert--Schmidt** `‖e^{-itL}-P‖²_HS = #{nonzero eigenvalues}` | `hsNorm_sq_unitaryEvolution_sub_spectralKernelProjector` |
| the same, read as the codimension of the centralizer | `card_filter_eigenvalues_ne_zero`, `hsNorm_sq_unitaryEvolution_sub_spectralKernelProjector_eq_codim` |
| unitary conjugation is an isometry for the Hilbert--Schmidt norm | `hsNorm_conj_le`, `hsNorm_unitary_conj` |

### Theorem B -- `HistogramCentralizerDimension`

| Card item | Declaration |
|---|---|
| the commutant of a matrix, as a submodule | `commutantSubmodule`, `mem_commutantSubmodule` |
| the commutant of a diagonal matrix is the equal-energy support | `mem_commutantSubmodule_diagonal`, `commutantSubmodule_diagonal_eq_span` |
| **its dimension is the number of equal-energy level pairs** | `finrank_commutantSubmodule_diagonal` |
| **`(6)`** the collective energy is the histogram pairing | `collectiveReplicaEnergy`, `collectiveReplicaEnergy_eq_sum_multiplicity` |
| maximal projective spectral rank (corpus predicate, reused) | `MaximallyProjectiveEnergy` |
| **equal collective energy ⟺ equal histogram** | `collectiveReplicaEnergy_eq_iff_multiplicity_eq` |
| **`(11)`** `κ_{D,r} = ∑_{\|k\|=r} m_k²` | `replicaHistogramCollision`, `replicaHistogramCollision_eq_sum_sq` |
| **`(12)`** `dim C_{H,r} = κ_{D,r}` | `finrank_commutantSubmodule_collectiveReplicaEnergy` |
| **`(14)`** `κ_{D,1} = D` | `replicaHistogramCollision_one` |
| **`(15)`** the total pair count is `D^{2r}` | `card_orderedReplicaPair` |
| **`(16)`** `D^r ≤ κ_{D,r} ≤ r! D^r` | `replicaHistogramCollision_eq_sum_fiber`, `replicaHistogramCollision_bounds` |
| **`(17)`** `κ_{D,r} ≥ (D)_r r!` | `orderedReplicaMultiplicity_le_one_of_injective`, `multinomial_orderedReplicaMultiplicity_of_injective`, `descFactorial_mul_factorial_le_replicaHistogramCollision` |

`(15)` is the identity `κ_{D,r} = #{(α,β) : hist α = hist β}` together with `#pairs = D^{2r}`, which is
exactly the statement that `κ/D^{2r}` is the histogram collision probability of two independent
uniform tuples.

### Theorem D -- `AveragedCentralizerProjectionFloor`, `PlanarStaticSeparation`

| Card item | Declaration |
|---|---|
| **`(13)`** `dim(C ⊓ Nᗮ) = dim C - dim N` | `finrank_inf_orthogonal_eq_sub` |
| a Hermitian matrix has trace at most rank times operator norm | `abs_eigenvalue_le_l2_opNorm`, `trace_re_le_rank_mul_l2_opNorm` |
| the trace of a Hermitian idempotent is its rank | `trace_eq_rank_of_isHermitian_idem` |
| **`(21)`** compressing by the complement removes exactly the subprojector's trace | `trace_compression` |
| the average of Hermitian matrices is Hermitian; trace and products commute with the average | `isHermitian_integral`, `trace_integral`, `mul_integral`, `integral_mul` |
| **`(21)`--`(22)`** `‖Q P̄ Q‖ ≥ (κ-d)/(D^{2r}-d)` | `l2_opNorm_averaged_compression_ge` |
| **`(23)`** at one replica the ratio is `1/(D+1)` | `oneReplica_floor_ratio` |

### Theorem C -- `AnnealedSpectralDephasing`

| Card item | Declaration |
|---|---|
| Riemann--Lebesgue for a finite absolutely continuous measure on the line | `tendsto_integral_exp_measure_zero` |
| a phase with absolutely continuous pushforward dephases the parameter average | `tendsto_integral_exp_phase_zero` |
| the same against a bounded nonnegative weight | `tendsto_integral_exp_phase_nnreal_weight` |
| **the same against a bounded complex weight** | `tendsto_integral_exp_phase_weight` |
| **`(19)`, abstract form** entrywise oscillatory decay upgrades to operator-norm decay | `tendsto_annealed_matrix_l2_opNorm_zero` |

The absolute-continuity hypothesis is imposed once, on the pushforward of the *parameter* measure;
every bounded weight is then covered automatically, because `ν ≪ μ` implies
`φ_*ν ≪ φ_*μ`.  This is the card's "its continuously weighted pushforward is absolutely continuous;
Riemann--Lebesgue makes the corresponding integral tend to zero", proved once for all weights.

### Theorem E -- `PlanarStaticSeparation`

| Card item | Declaration |
|---|---|
| **`(26)`, abstract form** a family with a persistent floor is never approximated by a decaying reference | `eventually_le_norm_sub_of_tendsto` |

### What is not yet formalized

1. **The concrete instance of `(19)`.**  The abstract dephasing theorem consumes an entrywise
   expansion of the centered replica propagator into oscillatory averages whose phases push the
   spherical measure forward absolutely continuously.  That expansion is the card's `(20)`, and the
   absolute continuity is the fixed-shell nowhere-flat spectral-action theorem of the parent card
   `fixed-shell-angular-dephasing-static-local-plateau-law.md`, which is itself still at stage 2.
   Formalizing that parent card is the prerequisite.

2. **Equation `(25)`, all-replica planar decay.**  The corpus owns the complete one-replica
   pipeline (`FreeFockMatrixSemicircleFourierDecay`, `FiniteDysonHallAtomlessness`,
   `OneReplicaTracelessPauliSpectralDecay`), but it runs through
   `MatrixFamilyHasSubsingletonColumns`, which makes the matrix Dyson equation diagonal.  A
   *collective* replica generator is a sum over replicas, so in the replicated Pauli basis its
   adjoint matrix has up to `r` nonzero entries per column and the diagonal reduction fails.  The
   all-replica case therefore needs the genuinely non-diagonal matrix Dyson equation, i.e. Kargin's
   full matrix-semicircle theorem, exactly as the card's hostile audit records.  The all-replica
   Hall input it consumes is already available: `graphLocalCompleted_hall` and
   `graphLocal_finrank_le_shadow_add_factorial` from
   `../3-formalized/all-replica-one-step-local-pauli-hall-saturation-law.md`.

Everything else the card states -- Theorems A, B, D, equations `(6)`, `(8)`, `(9)`, `(11)`--`(17)`,
`(21)`--`(23)`, and the abstract mechanisms of `(19)` and `(26)` -- is proved unconditionally.

## Lean progress -- Theorem A, the quenched centralizer decomposition

`formal/GaloisForLFunctions/HTGeometry/QuenchedCentralizerDecomposition.lean` (new,
umbrella-wired, axiom-clean).

| Card item | Declaration |
|---|---|
| the Hilbert--Schmidt energy of a diagonal matrix | `hsSqRe_diagonal` |
| a real phase has modulus one | `norm_exp_neg_ofReal_mul_I` |
| the zero spectral projection and the generated flow | `zeroSpectralProj`, `liouvilleFlow` |
| the flow fixes the zero spectral projection | `liouvilleFlow_mul_zeroSpectralProj` |
| **`(8)`, the quenched decomposition** `e^{-itL} = P + e^{-itL}(I-P)` | `liouvilleFlow_decomposition` |
| the difference is supported on the nonzero spectrum | `liouvilleFlow_sub_zeroSpectralProj` |
| **`(9)`, Hilbert--Schmidt half**: `‖e^{-itL} - P‖²_HS` is the number of nonzero modes, at every time | `hsSqRe_liouvilleFlow_sub_zeroSpectralProj` |
| **`(9)`, operator half**: a nonzero mode gives a unit vector moved without shrinking | `exists_unit_vector_liouvilleFlow_sub` |

Proved in the spectral (diagonal) model of the Liouvillian, where `P` is the indicator of the zero
spectrum: the flow acts as `1` there and as a unit-modulus phase elsewhere, so the difference is
literally the indicator of the nonzero spectrum times a phase.  That makes `(9)`'s time-independence
immediate rather than an estimate -- the energy is exactly `D^{2r} - dim C_{H,r}` for every `t`, so
there is no quenched norm contraction at any time.

### What remains

Theorems B (all-replica moving-kernel multiplicity), C (annealed propagation converges to the
moving-kernel average), D (the plateau survives every global-commutant quotient) and E (planar decay
and its nontransfer).

## Lean status -- Theorems B and C are already in the corpus

Searching before building found that both are formalized, with the card's own equation numbering.

### Theorem B

`HTGeometry/HistogramCentralizerDimension.lean`:

| Card item | Declaration |
|---|---|
| the commutant of a diagonal matrix, and its dimension as the equal-energy pair count | `commutantSubmodule`, `mem_commutantSubmodule_diagonal`, `commutantSubmodule_diagonal_eq_span`, `finrank_commutantSubmodule_diagonal` |
| collective replica energy of an ordered tuple | `collectiveReplicaEnergy`, `collectiveReplicaEnergy_eq_sum_multiplicity` |
| **maximal projective rank ⟺ equal collective energy iff equal histogram** | `collectiveReplicaEnergy_eq_iff_multiplicity_eq` |
| **`(11)`**: `κ_{D,r} = Σ_k m_k²` | `replicaHistogramCollision`, `replicaHistogramCollision_eq_sum_sq` |
| **`(12)`**: `dim C_{H,r} = κ_{D,r}` | `finrank_commutantSubmodule_collectiveReplicaEnergy` |
| **`(14)`**: `κ_{D,1} = D` | `replicaHistogramCollision_one` |
| **`(15)`**: the total ordered-pair count `D^{2r}` | `card_orderedReplicaPair` |
| **`(16)`, `(17)`**: the two universal estimates | `replicaHistogramCollision_bounds`, `descFactorial_mul_factorial_le_replicaHistogramCollision` |

### Theorem C

`HTGeometry/AnnealedSpectralDephasing.lean`:

| Card item | Declaration |
|---|---|
| **`(19)`, abstract form** -- a finite matrix family whose entries are finite sums of bounded oscillatory averages against phases with absolutely continuous pushforward converges to zero in operator norm | `tendsto_annealed_matrix_l2_opNorm_zero` |

Its docstring states the intended application verbatim: "Applied to the difference between the
annealed propagator and the averaged invariant projector, this is the annealed convergence of the
replica propagator."  The card's proof supplies exactly the hypotheses it takes -- the tensor
eigenoperator expansion `(20)`, the identification of equal-histogram terms with `P_{H(θ),r}`, and
absolute continuity of the phase pushforward from the fixed-shell nowhere-flat theorem.

## Lean progress -- the norm floor of Theorem D and the separation of Theorem E

`formal/GaloisForLFunctions/HTGeometry/TraceDimensionEigenvalueFloor.lean` (new, umbrella-wired,
axiom-clean).

| Card item | Declaration |
|---|---|
| some member of a finite family is at least its average | `exists_le_of_sum_le_card_mul` |
| **`(22)`/`(23)`**: a Hermitian matrix has an eigenvalue at least its trace divided by the dimension, so a rank-`κ-d` projection inside dimension `D^{2r}-d` has norm floor `(κ-d)/(D^{2r}-d)` | `exists_eigenvalue_trace_floor` |
| **`(26)`**: the reverse triangle bound turning `(19)`, `(22)` and `(25)` into a positive separation | `norm_sub_ge_of_floor` |

`exists_eigenvalue_trace_floor` is the card's "a positive operator on an `N`-dimensional space has
largest eigenvalue at least its trace divided by `N`", and for a positive operator the largest
eigenvalue is the operator norm.  `norm_sub_ge_of_floor` is the final step of Theorem E: with
`y = QP̄Q` of norm at least `c`, `x = QU_r(t)Q` within `a → 0` of it by `(19)`, and `z = U^free(t)`
of norm at most `b → 0` by `(25)`, the separation is at least `c - a - b → c > 0`.

### `(13)` and `(21)`

| Card item | Declaration |
|---|---|
| **`(13)`**: with the global commutant nested inside the centralizer, the quotient part has dimension `κ_{D,r} - d_{D,r}` | `finrank_inf_orthogonal_eq_sub` (`TraceDimensionEigenvalueFloor`) |
| **`(21)`**: `Q P Q` is the orthogonal projection onto that part, being the difference of the two projections | `starProjection_inf_orthogonal_apply` (corpus, `HTGeometry/NestedProjectionConvergence.lean`) |

The dimension count rests on mathlib's `finrank_add_inf_finrank_orthogonal`, and the projection
identity -- "if `M ≤ K`, the projection onto the part of `K` orthogonal to `M` is the difference of
the two projections" -- was already in the corpus.  `(21)` is then the trace of an orthogonal
projection, which is its rank.

### `(25)` is formal at one replica, with the general machinery in place

| Card item | Existing declaration |
|---|---|
| **`(25)` at one replica** -- the vacuum-compressed propagator decays in operator norm | `oneReplicaWeightedVacuumCompressedPropagator_operatorNorm_tendsto_zero` (`HTGeometry/OneReplicaTracelessPauliSpectralDecay.lean`) |
| its absolutely continuous scalar and coordinate spectral laws | `oneReplicaWeightedScalarSpectralLaw_absolutelyContinuous`, `oneReplicaWeighted_coordinateSpectralLaw_absolutelyContinuous` (same module) |
| the free-Fock matrix-semicircle law and its Fourier decay | `freeFockCoordinateSpectralLaw_absolutelyContinuous` (`FreeFockMatrixSemicircleCoordinateLaw.lean`), `freeFockDiagonalVacuumPropagator_operatorNorm_tendsto_zero` (`FreeFockMatrixSemicircleFourierDecay.lean`) |
| a nonzero balanced integer relation stays nonconstant under permutation | `permutedSpectralCoefficient_not_constant` (`AnalyticSpectralRelationEscape.lean`) |

The card says `(25)` holds "exactly as in the formalized one-replica proof", and that proof is
`oneReplicaWeightedVacuumCompressedPropagator_operatorNorm_tendsto_zero`.  The Kargin input the card
cites -- absolute continuity of the full-matrix-semicircle scalar law -- is
`freeFockCoordinateSpectralLaw_absolutelyContinuous`, and the Riemann--Lebesgue decay it feeds is
`freeFockDiagonalVacuumPropagator_operatorNorm_tendsto_zero`.

### What remains

Two generalizations, both from one replica to all finite `r`:

1. `(25)` for `r > 1` -- the free-Fock decay machinery is complete, so this is the replicated
   instantiation rather than new analysis.
2. the chart/partition-of-unity reduction feeding `(20)` into
   `tendsto_annealed_matrix_l2_opNorm_zero`, whose absolute-continuity hypothesis comes from the
   nowhere-flat theorem; `permutedSpectralCoefficient_not_constant` is the nonconstancy half of that
   input.

Theorem A, all of Theorem B, `(13)`, `(21)`, the abstract form of Theorem C, and the quantitative
cores of D and E are formal.

## Lean status -- `(25)` at `r > 1` is not a replicated instantiation

The earlier note claimed that `(25)` for `r > 1` is "the replicated instantiation rather than new
analysis".  That is wrong, and the reason is structural.

The whole one-replica chain runs through
`MatrixFamilyHasSubsingletonColumns`: every column of every coefficient matrix has at most one
nonzero entry.  That hypothesis is what makes the matrix Dyson equation *diagonal*
(`matrixSemicircleCovariance_diagonal_of_subsingletonColumns`,
`matrixDysonFormalCoeff_diagonal_of_subsingletonColumns`), so the coordinate Stieltjes transforms
satisfy decoupled scalar equations and
`atomless_reciprocal_algebraic_stieltjes_absolutelyContinuous` applies.

At one replica the coefficient matrix is the adjoint action `ad_P` in the Pauli basis, and
`[P, Q] = 0` or `2PQ`, so each basis element has a single image: columns are subsingleton.  At `r`
replicas the generator is the Kronecker sum
`ad_{P_{[r]}}(Q_1 ⊗ ⋯ ⊗ Q_r) = ∑_a Q_1 ⊗ ⋯ ⊗ [P, Q_a] ⊗ ⋯ ⊗ Q_r`,
whose image is a sum over every slot that anticommutes with `P`.  Columns then carry up to `r`
nonzeros, the covariance map no longer preserves diagonal matrices, and the Dyson equation is a
genuine *matrix* equation.

There is also no reduction of the replicated family to `r` free copies: in
`∑_p \sqrt{v_p}\,(A_p)_{[r]} ⊗ s_p = ∑_a T_a` the slot operators `T_a` share the *same*
semicirculars `s_p`, and the matrix parts commuting does not make the `T_a` commute.

So `(25)` at `r > 1` genuinely needs the matrix Dyson equation -- existence, uniqueness and the
Stieltjes regularity giving absolute continuity of the matrix-valued semicircle law -- which is the
Kargin input the card already cites as external.  The card's remaining Lean content is therefore
exactly two named imports, not one import and one instantiation.
