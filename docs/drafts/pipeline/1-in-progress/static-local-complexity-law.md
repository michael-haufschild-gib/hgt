# Static-local quantum complexity law

- **ID:** static-local-complexity-law
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** Brown--Susskind complexity conjecture; master research goal
- **Statement:** Prove the complete growth--plateau--recurrence history for a concrete ensemble of fixed-locality, time-independent Hamiltonians, together with permanent efficient distinguishability from Haar randomness.

## Goal

Unconditionally prove Brown--Susskind's full law in ordinary autonomous
many-body dynamics. The final result must not substitute stochastic driving,
random circuits, growing locality, exact gate complexity, an assumed
complexity-class separation, or a nonphysical exponentially described
Hamiltonian.

### Scientific question and public headline

The paper is to answer a broader question than whether one chosen complexity
metric grows:

> Can an ordinary isolated quantum system computationally skip its own future?

The proposed answer is a **computational arrow-of-time law**.  For the generic
fixed-locality many-body phase, reaching the state at physical time `t` costs
order `t` elementary operations until exponential saturation; the system then
spends almost all time at maximal complexity and returns to a simple state only
on the doubly exponential recurrence scale.  Locality remains efficiently
observable throughout, so maximal complexity is not Haar randomness.

This one theorem would resolve three existing open problems rather than occupy
a gap between them:

1. Brown--Susskind's growth--plateau--recurrence history underlying the proposed
   growth of black-hole interiors.
2. The directional strengthening missing from the
   Brown--Freedman--Lin--Susskind critical-metric programme: exponentially
   late cut loci for ordinary fixed-local Hamiltonian rays.
3. Atia--Aharonov's open problem of proving that a typical local Hamiltonian
   cannot be fast-forwarded, and thereby identifying a physical origin of the
   computational time--energy uncertainty principle.

### Unifying conjectural jump: autonomous computational time

The research target is not the conjunction of those three problems.  It is the
following proposed law of which they would be consequences:

> **No-Shortcut Law for Autonomous Time.**  After fixing energy scale and
> observational resolution, generic irreducible local quantum matter reaches
> its future state by an essentially shortest local quantum computation until
> its finite state capacity is exhausted.  Thereafter it occupies maximal
> complexity for asymptotic density one and can become simple again only on
> its full spectral-recurrence scale.

For the Choi clock of `H_n`, the falsifiable mathematical form is

\[
 C_\varepsilon(\Phi_{H_n}(t))
   =\widetilde\Theta\!\left(
      \min\{\Lambda(H_n)|t|,\,2^n\}\right)
\]

from the resolution time to exponential saturation, followed by a
`exp(Theta(2^n))` first return to polynomial complexity.  Here `Lambda(H_n)`
is an explicit local interaction-rate normalization, not an adjustable fit
parameter, and the tildes may hide only the polynomial factors stated in the
theorem.  A permanent efficient locality witness must hold on the same event.

This would identify elapsed autonomous time with irreducible preparation work,
not merely correlate two curves.  In a holographic model for which complexity
has a geometric dual, it would say that the growing interior cannot be reached
by a shorter boundary preparation.  That transfer remains forbidden until the
law is proved for the corresponding SYK/CFT model.

Literal quantification over every Hamiltonian is false: `H = 0`, commuting
models, free systems, and finite-order evolutions can be fast-forwarded or
recur immediately.  Universality must therefore be a proved classification:
the no-shortcut phase is characterized by explicit spectral and computational
irreducibility predicates, while the exceptional phases are characterized by
the precise invariant that collapses.  Calling only the generic branch
"universal" without this complementary classification is not allowed.

The first headline theorem must concern robust state complexity (equivalently,
the thermofield-double/Choi trajectory after its fixed linear-size
preparation), not only black-box query complexity or uniform simulation.
Atia--Aharonov explicitly distinguish non-fast-forwarding of a unitary from the
stronger possibility that its distinguished evolved state has a shorter
preparation.  Closing only the former does not close this card.

The minimum target model is the standard all-to-all fixed-`q` Pauli
Hamiltonian ensemble on `n` qubits,

\[
  H_n=\sum_{1\leq |P|\leq q} J_P P,
\]

with fixed `q >= 2`, independent centred Gaussian coefficients under an
explicit normalization, a fixed product input state, and approximate state
circuit complexity relative to a fixed finite universal two-qubit gate set.
The intended extension includes fixed-`q` SYK and geometrically local spin
ensembles; neither extension may be asserted before proof.

## Master theorem target

Fix approximation error `0 < epsilon < epsilon_0`. Prove explicit constants
and a high-probability event in the Hamiltonian ensemble on which all four
parts hold:

1. **Growth.** After the resolution time and before exponential saturation
   time, approximate state circuit complexity has matching linear upper and
   lower bounds, up to explicitly stated polynomial factors in `n`.
2. **Plateau.** Complexity reaches order `2^n` and remains within a fixed
   fraction of maximal state complexity for all but a quantitatively negligible
   fraction of the subsequent time window.
3. **Recurrence.** The first post-saturation return to polynomial complexity
   has matching doubly exponential upper and lower scales.
4. **Complexity without randomness.** At every evolution time, the same
   fixed-locality unitary ensemble is distinguishable from Haar randomness by
   an explicit polynomial-time two-query experiment with inverse-polynomial
   advantage.

Quantifiers over time, probability, approximation error, circuit ancillas,
gate geometry, and norms remain part of the theorem and may not be relegated
to prose. `Chaotic`, `generic`, `black-hole-like`, and `typical` are forbidden
as hypotheses unless replaced by explicit mathematical predicates and then
proved for the target ensemble.

## Gates

- [x] 0 -> 1 in-progress: externally documented open problem; concrete first model; attack decomposition
- [ ] 1 -> 2 fully-proven: complete paper proof of all four parts, `[PROVED HERE]`, no open dependency
- [ ] 2 -> 3 formalized: every mathematical claim has a dependency-closed Lean theorem; no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`
- [ ] 3 -> 4 publication-ready: standalone paper passes hostile specialist and Nature editorial review

## Existing Lean building blocks found before new code

- `FiniteSpectralHaarRecurrenceLaw.lean` proves weak convergence of a
  rationally independent deterministic phase flow to normalized Haar measure
  on its full finite torus.
- `FiniteSpectralRecurrenceFrequencyLaw.lean` transfers that convergence to
  upper and lower long-time frequencies of high-fidelity recurrence targets.
- `ObserverReturnLocalVolumeLaw.lean` proves exact local target-volume bounds
  with exponent equal to half observer temporal dimension.
- `ObserverReturnGlobalLocalizationLaw.lean` localizes sufficiently small
  global return defects into chosen local charts.
- `UniversalProjectiveRecurrenceCapstoneLaw.lean` identifies balanced spectral
  relations and temporal rank.
- `RadialAngularRecurrenceCompletionLaw.lean` contains finite diagonal unitary
  evolution and its integer-time bridge.
- `FiniteAndersonAllTimeRecurrenceLocalitySeparationLaw.lean` supplies concrete
  finite local Hamiltonians with maximal projective recurrence rank, but does
  not supply circuit-complexity growth.
- `FiniteHorizonCStarPerturbationLaw.lean` supplies finite-time Hamiltonian
  distinguishability bounds, but not the unknown-Hamiltonian two-query Haar
  distinguisher.

No circuit/gate complexity definition or theorem was found in the formal
corpus. No Lean code for that layer is authorized until the paper definitions
and mathematical lemmas are dependency-closed.

## Proof obligations

### O1. Robust circuit model

Define approximate state complexity, allowed ancillas, gate placement, metric,
and a finite circuit-net counting theorem with the correct dependence on
`n`, depth, and `epsilon`.

### O2. Static spectral orbit

Prove maximal projective spectral rank and full input-state spectral support
for the concrete fixed-`q` ensemble, then transfer existing spectral Haar laws
to the state orbit.

**Paper-proof progress.** `../2-fully-proven/generic-two-local-spectral-monodromy.md`
proves that the generic two-local Pauli characteristic polynomial has full
`S_(2^n)` spectral monodromy.  It follows that every full-density `q >= 2`
Pauli ensemble has rationally independent projective energy gaps almost surely.
Using the Choi trajectory gives exactly uniform spectral weights, removing the
separate eigenvector-delocalization requirement for the operator-complexity
law.  Lean now certifies the full-symmetric permutation-to-relation-rigidity
step and generation of the full Boolean-hypercube symmetric group by edge
transpositions.  The analytic bridge from the two-local Pauli family to those
branch transpositions remains to be formalized, so O2 is not yet closed.

There is a second, dependency-closed paper proof for the fermionic model used
below.

`[PROVED HERE.]`  Fix `m>=2` and one parity
`eta in {+1,-1}`.  In the occupation basis, label the parity sector by

\[
 \mathcal X_\eta
 =\{s\in\{\pm1\}^m:\prod_{i=1}^m s_i=\eta\},
 \qquad |\mathcal X_\eta|=2^{m-1}.                    \tag{O2.1}
\]

The complexified two-plus-four-Majorana family contains every diagonal
Hamiltonian

\[
 E_{h,J}(s)=\sum_i h_i s_i+\sum_{i<j}J_{ij}s_is_j     \tag{O2.2}
\]

and, for every pair `i<j`, a quadratic Majorana word `Q_(ij)` which maps
`|s>` to a nonzero phase times `|s^(ij)>`, where `s^(ij)` flips precisely
coordinates `i,j`.

Fix one Hamming-two edge `{s,s^(ij)}`.  Its diagonal energy difference is a
nonzero linear functional of `(h,J)`.  No other unordered pair has a
proportional difference functional.  Different flip supports are already
distinguished by the field coefficients; on the same support, the
coefficients of `J_(ik)` and `J_(jk)` recover every exterior sign `s_k`.
Therefore the hyperplane

\[
 E_{h,J}(s)=E_{h,J}(s^{(ij)})                       \tag{O2.3}
\]

is not contained in any other degeneracy hyperplane.  Choose a point on it
avoiding their finite union.  The selected two basis states are then the
only degenerate pair.

The matrix `E_(h,J)+zQ_(ij)` is a direct sum of two-by-two blocks indexed by
the involution `r -> r^(ij)`.  Give `z` a sufficiently small nonzero complex
value and vary one diagonal parameter transverse to `(O2.3)`.  The selected
block has eigenvalues

\[
 {E_s+E_{s^{(ij)}}\over2}
 \ \pm\
 \sqrt{\left({E_s-E_{s^{(ij)}}\over2}\right)^2+c z^2},
 \qquad c\ne0,                                       \tag{O2.4}
\]

and hence a small loop about either simple branch point swaps exactly those
two eigenvalues.  All other block discriminants remain nonzero by the
choice of the diagonal point and smallness of `z`.

The graph on `\mathcal X_eta` generated by two-coordinate flips is connected.
Its edge transpositions therefore generate the full symmetric group
`S_(2^(m-1))`.  Thus the complexified two-plus-four-Majorana characteristic
polynomial has full symmetric spectral monodromy on each parity sector.

This also proves maximal projective spectral rank almost surely for every
full-density real coefficient law on that family.  If a nonzero integer
relation among the projective gaps held identically, its coefficient vector
would have coordinate sum zero.  Full symmetric monodromy would carry that
relation through the entire standard representation of the symmetric group,
forcing all eigenvalues equal, a contradiction.  Hence each fixed
nontrivial relation cuts out a proper real-analytic zero set.  The countable
union over integer coefficient vectors has measure zero.  In particular the
isotropic Gaussian two-plus-four-Majorana ensemble used in O3 has simple
spectrum and rationally independent projective gaps almost surely.

### O3. Local spectral complexity transversality

Prove that low-complexity state neighborhoods occupy exponentially small Haar
volume on the static spectral orbit. This is the missing replacement for
full-unitary designs, which static fixed-locality evolution cannot form.

**Paper-proof progress.**
`../2-fully-proven/universal-static-choi-complexity-plateau.md` proves an
eigenbasis-free theorem for the Choi/thermofield-double spectral torus.  Every
trace-distance ball has Haar mass at most

\[
  D e^{D/2}\left({\pi(1-\sqrt{1-4\delta^2})\over2}\right)^{(D-1)/2}.
\]

A union over all circuits of size at most `s` gives an explicit
`M^(s+1)` multiple of this bound.  Thus, at fixed small error, all but
`exp(-Omega(D))` of completed time has approximate circuit complexity
`Omega(D/log n)` for local gates, for every eigenbasis.  This closes O3 on
paper for the Choi orbit once combined with O2.  Lean now certifies translated-cap measure
invariance, controlled-target and finite-dictionary union bounds, the exact
Hilbert--Schmidt geometry of equal-weight Choi phase densities, and the
metric-displacement-to-coherence implication.  Circuit-word counting and the
metric-ball capstone are also compiled.  The completed-time Portmanteau
specialization is now compiled on the physically correct projective torus as
`completedTime_zeroAnchoredPaddedCircuitTargets`.  Maximal projective spectral
rank alone makes the zero-anchored relative frequencies independent; an exact
measure-preserving global-phase split identifies projective target volume with
the full-torus Choi bound.  Thus traceless local Hamiltonians are included.
The result proves a Choi-orbit plateau occupation law; it does
not imply O4's pointwise linear growth or O5's first hitting time.

`[SEMANTIC DEFECT.]`  This Choi theorem does not by itself prove the master
claim of near-maximal **state** complexity.  A Hamiltonian on `n` qubits
produces a Choi state on `2n` qubits.  The proved `Omega(2^n/poly(n))`
complexity is therefore only the square-root scale of unrestricted
`2n`-qubit state complexity `Theta(4^n)`.  Calling the two scales equivalent
would hide a full exponential factor.

There is a fixed-simple-input repair.

`[BRIDGE] [PAPER-PROVED, EXTERNAL DESIGN INPUT.]`  Put `D=2^n` and let
`\mathcal E_n` be any probability ensemble of nondegenerate self-adjoint
operators on `C^D`, with an ordered orthonormal eigenbasis
`(E_j(H))_(j=1)^D`.  For a unit vector `psi`, define its spectral collision
mass

\[
 \operatorname{Col}_H(\psi)
   =\sum_{j=1}^D|\langle E_j(H),\psi\rangle|^4.          \tag{O3.1}
\]

The uniform set `Stab_n` of all `n`-qubit stabilizer states is a complex
projective 2-design (indeed a 3-design; Kueng--Gross,
[arXiv:1510.02767](https://arxiv.org/abs/1510.02767)).  Consequently, for
every fixed `H`,

\[
 {1\over|\operatorname{Stab}_n|}
 \sum_{\psi\in\operatorname{Stab}_n}
 \operatorname{Col}_H(\psi)
 =
 \sum_{j=1}^D {2\over D(D+1)}
 ={2\over D+1}.                                       \tag{O3.2}
\]

Average `(O3.2)` over `H` and apply Markov's inequality before averaging
over the finite stabilizer set.  For every `K>0` there is therefore one
fixed stabilizer state `psi_n`, selected independently of `H`, such that

\[
 \Pr_{H\sim\mathcal E_n}\!\left\{
   \operatorname{Col}_H(\psi_n)>{K\over D}\right\}
 \leq {2D\over K(D+1)}<{2\over K}.                    \tag{O3.3}
\]

This is an existence theorem for a single initial state, not a
Hamiltonian-dependent choice.  Every stabilizer state has a polynomial-size
Clifford preparation, so the autonomous trajectory still begins at
polynomial state complexity.

Collision mass is already enough for uniform fixed-target
anti-concentration on the complete spectral phase torus.  Let
`p_j=|<E_j,psi_n>|^2`, suppose

\[
 \sum_jp_j=1,\qquad \sum_jp_j^2\leq {K\over D},         \tag{O3.4}
\]

and let `z_j` be independent uniform unit phases.  For any unit target
`phi`, any `0<epsilon<1`, and
`u=sqrt(1-epsilon^2)`, one has

\[
 \boxed{\quad
 \Pr_z\!\left\{
  \Delta\!\left(\sum_j\sqrt{p_j}z_jE_j,\phi\right)
       \leq\varepsilon\right\}
 \leq
 8\exp\!\left(-{u^4D\over64K}\right).
 \quad}                                                \tag{O3.5}
\]

Here `Delta` is pure-state trace distance.  To prove `(O3.5)`, set
`eta=u/2` and

\[
 A=\left\{j:p_j>{K\over\eta^2D}\right\}.
\]

The collision bound gives

\[
 \sum_{j\in A}p_j
 \leq{\eta^2D\over K}\sum_{j\in A}p_j^2
 \leq\eta^2.                                          \tag{O3.6}
\]

Thus the heavy coordinates contribute at most `eta` to the target overlap.
On the complement, with
`a_j=sqrt(p_j)\overline{<E_j,phi>}`,

\[
 \sum_{j\notin A}|a_j|^2
 \leq {K\over\eta^2D}.                                \tag{O3.7}
\]

For a Steinhaus sum `S=sum_j a_jz_j`, an eight-direction net and the
real Hoeffding bound give

\[
 \Pr\{|S|\geq v\}
 \leq8\exp\!\left(
   -{v^2\over4\sum_j|a_j|^2}\right).                  \tag{O3.8}
\]

Trace distance at most `epsilon` forces overlap at least `u`; after
`(O3.6)` the light sum must therefore have modulus at least
`u-eta=u/2`.  Substitution of `(O3.7)` into `(O3.8)` proves `(O3.5)`.

If a circuit dictionary has at most `M^(s+1)` words of length at most `s`,
the target-uniform estimate `(O3.5)` gives

\[
 \Pr_z\!\left\{
 C_\varepsilon\!\left(\sum_j\sqrt{p_j}z_jE_j\right)
 \leq s\right\}
 \leq
 8M^{s+1}\exp\!\left(-{u^4D\over64K}\right).           \tag{O3.9}
\]

Hence for `K=poly(n)` and `log M=O(log n)`, a single fixed
polynomial-preparable `n`-qubit input has completed-time complexity
`Omega(D/(K log n))` outside phase mass
`exp(-Omega(D/K))`, with Hamiltonian probability at least `1-2/K`.
This is the correct near-maximal `n`-qubit state scale, up to the allowed
polynomial loss.  It removes the Choi dimension mismatch without assuming
eigenvector universality.

The stabilizer selection can be made explicit, and the input can be product,
for a fixed-local fermionic ensemble relevant to black-hole models.  The
mechanism is a general symmetry-orbit frame law.

`[BRIDGE] [PAPER-PROVED.]`  Let a compact group `G` act unitarily on a
`D`-dimensional Hilbert space `S`.  Fix a unit vector `psi_0` and suppose

\[
 W=\operatorname{span}\{(g\psi_0)^{\otimes2}:g\in G\}
 \subset S^{\otimes2}                                \tag{O3.10}
\]

is an irreducible `G`-module of dimension `R`.  Let `\mathcal E` be any
conjugation-invariant probability ensemble of self-adjoint operators on `S`
with simple spectrum almost surely.  Then

\[
 \boxed{\qquad
 \mathbb E_{H\sim\mathcal E}\operatorname{Col}_H(\psi_0)
 \leq {D\over R}.
 \qquad}                                              \tag{O3.11}
\]

Indeed, Schur's lemma and trace normalization give the exact orbit second
moment

\[
 \int_G
 |(g\psi_0)^{\otimes2}\rangle
 \langle(g\psi_0)^{\otimes2}|\,dg
 ={P_W\over R}.                                      \tag{O3.12}
\]

For every fixed eigenvector `E_j`, its fourth overlap average is therefore
at most `1/R`; summing over `j` gives `D/R`.  Conjugation invariance moves
the group action from `H` to `psi_0`, so the same bound holds for the fixed
input after averaging over `H`.  Markov's inequality also gives

\[
 \Pr_H\!\left\{
 \operatorname{Col}_H(\psi_0)>L{D\over R}\right\}
 \leq {1\over L}\qquad(L>0).                         \tag{O3.13}
\]

This theorem needs neither random eigenvectors nor a design on the full
unit sphere.  It measures exactly how much of the symmetric tensor square
is swept out by the physical symmetry orbit of one simple state.

Apply it to `2m` Majorana modes.  On one fermion-parity sector the compact
spin group `Spin(2m)` acts in a half-spin representation `S^+` of dimension

\[
 D=2^{m-1}.
\]

The Fock vacuum `Omega` is a highest-weight pure spinor.  Its tensor-square
orbit spans the Cartan square `V_(2 omega_m)`, equivalently one of the two
middle-form summands, and hence

\[
 R=\dim V_{2\omega_m}={1\over2}{2m\choose m}.          \tag{O3.14}
\]

This standard half-spin decomposition is recorded, for example, in the
representation-theoretic treatment of the spinor variety by Manivel
([arXiv:0904.0565](https://arxiv.org/abs/0904.0565)).

Now take the explicit time-independent local ensemble

\[
 H(J_2,J_4)=
 i\sum_{a<b}J^{(2)}_{ab}\gamma_a\gamma_b+
 \sum_{|I|=4}J^{(4)}_I\gamma_I,
\]

restricted to `S^+`, where the two coefficient tensors are independent
nondegenerate isotropic Gaussians on
`\Lambda^2 R^(2m)` and `\Lambda^4 R^(2m)`.  Orthogonal rotation of the
Majoranas acts by spin conjugation and preserves both Gaussian laws, so the
ensemble satisfies the invariance premise.  Its spectrum is simple almost
surely: the discriminant is a polynomial in the coefficients and is not
identically zero, because at `J_q=0` a quadratic normal form with
rationally independent single-particle energies has distinct signed sums
inside a fixed parity sector.

The elementary central-binomial estimate

\[
 {2m\choose m}\geq {4^m\over2\sqrt m}
\]

gives `D^2/R<=sqrt(m)`.  Therefore the fixed product Fock vacuum obeys

\[
 \mathbb E_H\operatorname{Col}_H(\Omega)
 \leq{\sqrt m\over D},\qquad
 \Pr_H\!\left\{
 \operatorname{Col}_H(\Omega)>{L\sqrt m\over D}\right\}
 \leq {1\over L}.                                    \tag{O3.15}
\]

For completeness, the displayed binomial inequality follows by induction:
`binom(2m,m)sqrt(m)/4^m` equals `1/2` at `m=1`, and its consecutive ratio
is at least one after squaring and cancelling, with remainder `m+1>0`.

Combining `(O3.15)` with `(O3.5)--(O3.9)` at
`K=L sqrt(m)` proves, for this explicit fixed-`q` SYK-plus-quadratic
ensemble and the fixed product vacuum,

\[
 \Pr_z\{\Delta(\Phi_H(z),\phi)\leq\varepsilon\}
 \leq
 8\exp\!\left(-{(1-\varepsilon^2)^2D\over64L\sqrt m}\right)
                                                               \tag{O3.16}
\]

against every fixed target, on a Hamiltonian event of probability at least
`1-1/L`.  The circuit union yields completed-time state complexity

\[
 \Omega\!\left({D\over L\sqrt m\log M}\right)          \tag{O3.17}
\]

outside phase mass `exp(-Omega(D/(L sqrt(m))))`.  Taking, for example,
`L=log m` gives probability tending to one and a genuinely near-maximal
plateau for one explicit product input.  This is the first fixed-input
plateau route in the card that is both compatible with fixed locality and
free of the Choi dimension loss.

The original all-to-all Pauli ensemble still lacks an equally explicit
product-input orbit of second-moment rank `D^2/poly(n)`.  It may use the
fixed stabilizer selected in `(O3.3)`, while the fermionic theorem uses the
literal product vacuum.  Neither statement may be advertised as the other.

The plateau now also has an unconditional infinite-time strengthening.
`StaticChoiSyndeticComplexityLaw.lean` proves that whenever the explicit
finite-circuit entropy bound is below one, the complement of the low-circuit
target is nonempty and open; maximal projective rank makes the physical phase
flow dense, and compactness upgrades density to syndetic return.  Hence one
finite target-dependent gap `L` exists such that **every** interval of length
`L`, at every positive or negative epoch, contains a Choi endpoint farther
than `delta` from every word in the stated circuit dictionary.  This is
strictly stronger than completed-time density: high-complexity endpoints
cannot disappear for arbitrarily long intervals.  The theorem is
nonquantitative in `L`, so it does not yet place the first hard endpoint near
the direct-simulation saturation time.

The target semantics are now full-state rather than a spectral-subspace
surrogate.  `StaticChoiFullStateProjectionLaw.lean` defines the full
`D^2`-dimensional Choi density, proves that restriction to the
diagonal--diagonal spectral block is Hilbert--Schmidt contractive, and proves
that the evolved full density restricts exactly to `uniformPhaseDensity`.
Consequently `maximallyProjective_fullChoiCircuitTargets_syndetic` separates
the true full Choi state from every arbitrary full circuit-target density with
no radius or dimension loss.  Only the conversion from this full-state
Hilbert--Schmidt metric to the paper's preferred trace/operator normalization
remains.

### O4. Linear no-shortcuts theorem

Prove a robust lower bound matching direct Hamiltonian-simulation complexity
through exponential time. This is the central open core, not a corollary of
recurrence or phase equidistribution.

More precisely, Brown--Freedman--Lin--Susskind (Nature 622, 58--62, 2023)
conjecture an emergent long-distance universality class and an approximately
exponential critical penalty schedule.  They do **not** state a numbered
conjecture that a typical fixed-local Hamiltonian ray avoids its directional
cut locus until exponential time.  That stronger directional statement is the
new geometric target required here.  It must be made precise for an explicit
fixed-`q` Gaussian ensemble by a quantified high-probability cut-time bound,
then transferred to robust finite-gate state complexity with only the
permitted polynomial losses.  Proving only absence of conjugate points is
insufficient: that excludes local variations but not a globally shorter path.

#### Proved power-amplification bridge and its sharp resolution cost

There is one unconditional backward transfer from a hard late endpoint to an
earlier autonomous endpoint.  For arbitrary unitary elements `U,V` of any
unital C-star algebra,

\[
  \|U^N-V^N\|\leq N\|U-V\|,
  \qquad
  e^{-itH\,N}=e^{-iNtH}.
\]

Consequently, if the repeated circuit endpoint `V^N` misses `e^{-iNtH}` by
at least `epsilon`, then `V` misses `e^{-itH}` by at least `epsilon/N`.
`FiniteHorizonCStarPerturbationLaw.lean` proves all three statements without
dimension, spectrum, locality or commutativity assumptions.  In an exact word
metric this turns a size-`Ns` lower bound at time `Nt` into a size-`s` lower
bound at time `t`; this is the rigorous form of backward hardness
amplification.

The same argument does **not** close robust O4 at fixed resolution: operator
error accumulates linearly under repetition, so a late `epsilon` separation
only certifies early `epsilon/N` separation.  Any successful robust theorem
must prove that coherent shortcut errors cannot track the autonomous orbit,
not merely invoke subadditivity.  This locates the missing content of O4 more
sharply than the cut-locus formulation.

There is, however, a stronger fixed-resolution transfer using autonomous time
addition rather than powers.  If `U(T)` is farther than `epsilon_late` from
every word of length `P`, `U(tau)` has an `r`-gate approximation at error
`epsilon_inc`, and

\[
  \epsilon_{early}+\epsilon_{inc}\leq\epsilon_{late},
\]

then `U(T-tau)` is farther than `epsilon_early` from every word of length
`P-r`.  Concatenating hypothetical approximants would otherwise approximate
`U(T-tau)U(tau)=U(T)`.  The compiled theorem
`circuitWordSeparated_autonomous_backward_cone` proves this for every group
metric satisfying the product-distance inequality.  Thus every hard plateau
endpoint casts a robust linear no-shortcut cone backward through time after
inserting a direct-simulation upper bound for `r(tau)`.  Unlike power
amplification, error is paid once, not divided by elapsed time.

The multiplication premise is now discharged for the physical norm model.
`unitaryCircuitWordSeparated_autonomous_backward_cone` proves the statement in
the operator-norm unitary group of every unital C-star algebra, with no matrix,
dimension, or finite-spectrum premise.  The exact norm identity under left
and right unitary multiplication supplies the joint product Lipschitz bound.

The cone and the new syndetic endpoint law also compose without loss of the
gap.  `unitaryCircuitWordSeparated_syndetic_backward_cones` proves that if
`P`-hard endpoints occur in every interval of length `L`, then for every fixed
lag `tau` the `(P-r(tau))` backward section occurs in every interval of the
same length `L`.  Thus hard endpoints generate infinitely many robust ramps
forever; cone propagation neither divides resolution nor enlarges recurrence
gaps.  A remaining semantic bridge must identify the Choi density dictionary
with the corresponding projective-unitary word targets before this composed
statement can be claimed for physical circuits in the paper.

This does not yet prove Brown--Susskind growth from the initial simple state:
O3 supplies a completed-time density of hard terminal points but no bound
placing the first such point at the direct-simulation saturation time.  The
remaining O4 content is now precisely that first-terminal-time/cut-time bound,
not robustness or infinite recurrence of the backward ramps once hard
endpoints are known.  The new syndetic theorem supplies a finite first hard
time and bounded gaps, but its compactness-produced `L` is not quantitatively
controlled.  O4 therefore requires `L` at the direct-simulation saturation
scale, uniformly with high probability in the local-Hamiltonian ensemble.

#### Exact-complexity boundary: algebraic local dynamics jumps instantly

`[PAPER-PROVED] [BRIDGE]`  The new card
`../2-fully-proven/algebraic-two-local-instant-exact-complexity.md` combines
the corpus's full two-local spectral monodromy with Hilbert irreducibility,
finite Lindemann--Weierstrass, and Jia--Wolf's transcendence-degree circuit
bound.  It produces a rational two-local `n`-qubit Hamiltonian and the fixed
product input `|0>^tensor n` such that, at every nonzero algebraic time,

\[
 C_0(e^{-itH_n}|0^n\rangle)\ge {2^n-1\over16}.          \tag{O4.E1}
\]

For each smaller exact gate budget, semialgebraicity of bounded-gate state
sets and one-dimensional restricted-analytic o-minimality further imply that
the exceptional real times are locally finite.  Exact complexity therefore
jumps from zero to the exponential scale essentially instantly; it does not
display Brown growth.

This is not an O4 shortcut.  Algebraic vectors are dense, so transcendence
degree has no fixed-radius stability.  The positive residue is a sharper
identification of the missing mathematics: O4 is a **quantitative** distance
lower bound between one algebraic local-Hamiltonian orbit and the
semialgebraic `s`-gate state set.  Qualitative Lindemann--Weierstrass proves
only that this distance is nonzero at algebraic times.  A physical theorem
requires a dimension-independent radius through
`s=Theta(2^n/poly(n))`.  Exact complexity is forbidden as a substitute in the
paper because it would manufacture an instantaneous, discontinuous fake of
the desired arrow of time.

#### Failed circuitwise entropy route and surviving aggregate word escape

An initial candidate was unrestricted worst-target concentration

\[
 Q_\varepsilon(t)=\sup_\psi
   \Pr_H\{\Delta(\Phi_H(t),\psi)\leq\varepsilon\}.
\]

That candidate is false at the strength needed for O4.  A static `q`-local
ensemble has only `m=poly(n)` Gaussian parameters.  On a coefficient ball of
fixed positive probability, the Duhamel bound makes
`H -> exp(-itH)` `O(t)`-Lipschitz.  An `m`-dimensional parameter net therefore
covers the evolved ensemble by at most

\[
  (C t/\varepsilon)^m
\]

metric balls.  Pigeonhole forces some target ball to have probability at least
`(C t/epsilon)^(-m)`, so unrestricted projective min-entropy is at most
`O(m log(t/epsilon))`.  It cannot certify complexity linear in exponential
time.  This no-go also explains why fixed-order design and ambient-volume
arguments stall.

Restricting the target to computations that would constitute a shortcut does
not rescue the circuitwise union-bound strategy.  Define

\[
 Q_{\varepsilon,s}^{\rm short}(t)=
   \sup_{C:\,|C|\leq s}
   \Pr_H\{\Delta(\Phi_H(t),C\Phi_0)\leq\varepsilon\}.
\]

The identity circuit already gives a sharp obstruction.  Let
`H(J)=sum_(a=1)^m J_a P_a` with `||P_a|| <= 1`, and choose one nonidentity
Pauli word `P_1`.  For every large `t`, choose an integer `k` with
`2 pi k/t` in a fixed positive compact coefficient interval and put
`J^(0)=(2 pi k/t,0,...,0)`.  Then

\[
 e^{-itH(J^{(0)})}=e^{-2\pi i kP_1}=I.
\]

On a coefficient box of radius `c epsilon/(tm)` around `J^(0)`, Duhamel's
inequality keeps the evolution within `epsilon` of the identity.  The Gaussian
density is bounded below on that box, so for constants depending only on the
fixed normalization,

\[
 Q_{\varepsilon,s}^{\rm short}(t)
 \geq c_0^m\left({\varepsilon\over tm}\right)^m
 \qquad(s\geq0).                                      \tag{O4.1}
\]

This obstruction persists on a fixed-energy shell: `J^(0)` has order-one
norm.  Consequently

\[
 -\log Q_{\varepsilon,s}^{\rm short}(t)
 \leq m\log(tm/\varepsilon)+O(m),                     \tag{O4.2}
\]

and therefore cannot satisfy the previously proposed bound

\[
 -\log Q_{\varepsilon,s}^{\rm short}(t)
   \geq (s+1)\log M+\gamma_n(t)
 \quad\text{for }s\asymp t/\operatorname{poly}(n)
\]

once `s` is much larger than `m log t`.  Thus no proof may pay for circuits one
at a time.

There is a stronger obstruction to the tempting repair “remove one common
recurrence event and then use Haar anti-concentration for every fixed
short-circuit target.”  It is not specific to spectral recurrence.

`[NO-GO] [PAPER-PROVED]` Let `K subset R^m` carry a probability measure with
density at least `rho_0>0` on every ball `B(x_i,r_0)` considered below, and
let `F_t:K -> X` be `L_t`-Lipschitz into a metric space.  Let `T_s subset X`
be the set of permitted short-circuit targets.  Suppose a target-independent
exceptional set `E_t subset K` is claimed to leave the fixed-target bound

\[
 \mu\{x\notin E_t:d(F_t(x),y)\leq\varepsilon_+\}\leq h_t
 \qquad\text{for every }y\in T_s .                   \tag{O4.2a}
\]

Fix `0<=epsilon_-<epsilon_+`.  For any robust shortcut centre `x_i` and
target `y_i in T_s` satisfying

\[
 d(F_t(x_i),y_i)\leq\varepsilon_-,
\]

put

\[
 r=\min\{r_0,(\varepsilon_+-\varepsilon_-)/L_t\}.
\]

Lipschitz continuity gives

\[
 B(x_i,r)\subset
 \{x:d(F_t(x),y_i)\leq\varepsilon_+\}.
\]

Consequently

\[
 \mu(E_t\cap B(x_i,r))
 \geq \rho_0 v_m r^m-h_t,                            \tag{O4.2b}
\]

where `v_m` is the volume of the Euclidean unit ball.  For `N` pairwise
disjoint such shortcut balls, possibly with different targets,

\[
 \boxed{\quad
 \mu(E_t)\geq
 N\bigl(\rho_0v_mr^m-h_t\bigr).
 \quad}                                               \tag{O4.2c}
\]

The proof is only subtraction: `(O4.2a)` bounds
`mu(B(x_i,r) setminus E_t)` by `h_t`, while the density lower bound controls
the whole ball; disjointness permits summation.

For autonomous evolution the Duhamel estimate gives `L_t=O(t)`.  Each
attained short target therefore carries a local capture tube of mass
`Omega(t^{-m})`, whether or not the centre is a spectral recurrence.
For comparison, normalized Haar measure on pure states in complex dimension
`D` assigns the trace-distance cap of radius `epsilon` about any fixed pure
state the exact mass

\[
 h_{\rm Haar}(\varepsilon)=\varepsilon^{2(D-1)}.       \tag{O4.2d}
\]

This is exponentially smaller in Hilbert-space dimension than `t^{-m}` in
the intended pre-saturation range.
Thus a target-independent set that leaves Haar-scale anti-concentration must
absorb essentially every separated shortcut island.  Calling that union
“common recurrence mass” does not isolate an independently controllable
event: bounding it is exactly the aggregate no-shortcut theorem.  A
fixed-target Haar estimate followed by a circuit union is therefore
circular for a static `m`-parameter Hamiltonian ensemble.

The surviving object is the **whole shortcut locus**

\[
 \mathcal B_{\varepsilon,s}(t)
 =\{H:C_\varepsilon(\Phi_H(t))\leq s\}.
\]

The new hard target is an **aggregate autonomous word-escape theorem**.  After
fixing the energy shell, prove directly, without a union over circuit words,

\[
 \Pr_H\!\left\{
 C_\varepsilon(\Phi_H(t))
 \leq {a\Lambda(H)t\over\operatorname{poly}(n)}
 \right\}
 \leq
 \left({A tm\over\varepsilon}\right)^{-c m}           \tag{O4.3}
\]

uniformly from the resolution time through exponential saturation.  The
power-law-in-`t` failure with exponent proportional to parameter dimension is
strong enough for a time net through `t=exp(Theta(n))`, while `(O4.1)` shows
that its functional form is optimal up to constants.  This is a global
intersection theorem between the evolved local-Hamiltonian manifold and the
low-word metric variety; ordinary small-ball estimates and circuit counting
cannot prove it.

Conceptually, the missing invariant is noncommutative.  Exact spectral
relations are the abelianized shadow and control completed recurrence.
Relations between a local one-parameter subgroup and short local-gate words
control pre-saturation computation.  Finite-dimensional matrix identities
force saturation.  The proposed universal law says that generic irreducible
local matter has no robust low-word relations before that capacity boundary.
Its precise new mathematical content is `(O4.3)`, not the terminology.

#### Frontier reset: what would actually move O4

The fixed-order commutator, Wick, ribbon, and cavity results later in this
card are auxiliary.  They do **not** count as progress on Brown--Susskind
growth unless they imply (O4.3), uniformly in physical time after the
Hamiltonian-dependent circuit selector has been taken.  In particular,
coefficient cancellation, a planar Dyson equation, replica genus, spectral
return, operator spreading, and absence of invariant cavity modes are all
compatible with an unexpectedly short endpoint circuit.

The missing scientific knowledge is one global theorem:

> **Quenched robust word-metric injectivity.**  A typical fixed local
> Hamiltonian one-parameter subgroup has no approximate relation with the
> local-gate word ball of radius `a t/poly(n)` before exponential
> saturation, except on aggregate Hamiltonian mass bounded by (O4.3).

This target is a directional strengthening of the Brown--Freedman--Lin--
Susskind critical-metric programme, not the literal content of a numbered
conjecture in that paper.  Their discussion motivates an exponentially large
complexity geometry and a universal critical schedule, but it does not state
the robust discrete-circuit, quenched, uniform-in-time probability estimate
(O4.3).  The paper must not cite metric universality as if it already supplied
directional word-metric injectivity.

This is a nonuniform no-fast-forwarding theorem: the competing circuit may
depend on the realized Hamiltonian.  Oracle lower bounds, fixed-target
anti-concentration, finite-order moments, design comparison, support growth,
and ordinary NLTS do not establish it.  A genuine advance must construct an
endpoint-dependent global word-metric calibration or prove an aggregate
transversality theorem for the whole circuit tube.  Until one of those two
objects is obtained with a bound strong enough to imply (O4.3), the central
frontier has not moved.

This is the proposed physical reinterpretation: autonomous time can generate
**computational inaccessibility without statistical randomness**.  The orbit
remains a low-parameter, efficiently non-Haar family, while every center that
captures appreciable mass moves beyond the circuit budget available at that
time.  Kotowski--Oszmaniec--Horodecki obtain an immediate extremal jump for
GUE and Haar-conjugated diagonal generators using load-bearing unitary
invariance; no audited result proves this local ballistic law.

#### Quantized-witness reduction: the actual circuit-lower-bound frontier

`[BRIDGE] [PAPER-PROVED]`  The quenched theorem is not merely stronger than
known Hamiltonian-simulation lower bounds.  At exponential time it produces a
polynomial-bit local Hamiltonian with robust exponential **nonuniform endpoint
circuit complexity**.

Let

\[
 H(J)=\sum_{a=1}^m J_aP_a,\qquad \|P_a\|\leq1,
\]

let `K` be contained in the coefficient box `[-B,B]^m`, and suppose the state
metric is dominated by operator-norm perturbation of the implementing
unitary.  Fix `t>0`, `epsilon>0`, and an integer `s`.  If

\[
 \mu\{J\in K:C_\varepsilon(e^{-itH(J)}\Phi_0)\leq s\}<1,            \tag{O4.3j}
\]

then there is a rational coefficient vector `J_tilde` whose coordinates have
bit length

\[
 O\!\left(\log {Btm\over\varepsilon}\right)
                                                                    \tag{O4.3k}
\]

and for which

\[
 C_{\varepsilon/2}(e^{-itH(\widetilde J)}\Phi_0)>s.                 \tag{O4.3l}
\]

If the simulation rate `Lambda` is `L_Lambda`-Lipschitz in coefficient
`l^1` distance and `Lambda(H(J))>=lambda_0` on `K`, the same witness satisfies

\[
 \Lambda(H(\widetilde J))
 \geq\lambda_0-{L_\Lambda\varepsilon\over4t}.                       \tag{O4.3m}
\]

**Proof.**  Choose a hard `J` supplied by (O4.3j), take

\[
 Q=\left\lceil {2tm\over\varepsilon}\right\rceil,
\]

and round every coordinate of `J` to the nearest multiple of `1/Q`.
Then

\[
 \|H(J)-H(\widetilde J)\|
 \leq\sum_a|J_a-\widetilde J_a|
 \leq {m\over2Q},
\]

so Duhamel's inequality gives

\[
 \|e^{-itH(J)}-e^{-itH(\widetilde J)}\|
 \leq {tm\over2Q}\leq{\varepsilon\over4}.                           \tag{O4.3n}
\]

An `s`-gate circuit within `epsilon/2` of the rounded endpoint would
therefore lie within `3epsilon/4` of the original endpoint, contradicting
its `epsilon`-hardness.  The rounded numerator is at most `BQ+1`, proving
(O4.3k).  The same coefficient estimate and Lipschitz continuity prove
(O4.3m).

For `m=poly(n)`, constant `epsilon`, and
`t=exp(alpha n)`, (O4.3k) is `O(n)` bits per local coefficient, while the
O4 lower bound is `exp(Omega(n))/poly(n)` gates.  With a finite computable
gate alphabet the witnesses can even be selected as a uniformly computable
sequence: enumerate the finite coefficient grid and the finite word ball,
compute every distance to successively finer certified precision, and choose
the first point separated by the strict margin in (O4.3n).  This observation
does not make the search efficient; it shows that O4 would constitute a
robust exponential circuit lower bound for a finitely described autonomous
quantum evolution, rather than an oracle or input-uniform simulation bound.

`[LITERATURE BOUNDARY.]`  Zlokapa--Allen--Harrow,
*Optimal Lower Bounds for Hamiltonian Simulation*, arXiv:2607.19852, does not
cross this frontier.  Its gate theorem requires channel approximation on
every input state.  Its factor linear in late time is obtained by applying
successive unit intervals to fresh disjoint qubit blocks; after rewriting
the construction as time independent, both the number of qubits and the
Hamiltonian description grow linearly with `t`.  Its unit-time static lemma
is a spatial direct-sum lower bound.  None of these statements lower-bounds
the best circuit for one fixed Choi/state endpoint of one fixed finite
Hamiltonian at its `t`-th power.

`[FRONTIER RESET.]`  Equations (O4.12q)--(O4.12z16) below remain valid
fixed-order or planar identities, but they do not address (O4.3j).  Signed
Wick cancellation is destroyed by the Hamiltonian-dependent maximizer, and
the proposed planar Bellman dressing has not supplied a positive
selector-aware inequality.  It is therefore retired as evidence of progress
on O4.  The first missing scientific statement is exactly a robust
exponential nonuniform circuit lower bound of the form (O4.3l), proved for a
positive-density set of polynomial-bit fixed-local Hamiltonians and then
upgraded to the quenched annular law (O4.3i).  Any weaker simulator,
fixed-target, moment, design, spreading, or spatial direct-sum theorem leaves
the frontier unchanged.

#### Orientation--transgression transfer audit

`[PAPER-PROVED NO-GO]`  The abstract factorization law in
`riemann-source-orientation-transgression` has one exact quantum-complexity
consequence, but it is negative.  Let `Herm(H)` be the real vector space of
Hermitian operators on an `N`-qubit Hilbert space and consider the split
complex

\[
 \operatorname{Herm}_0(\mathcal H)
 \xrightarrow{\ \iota\ }
 \operatorname{Herm}(\mathcal H)
 \xrightarrow{\ \operatorname{Tr}\ }
 \mathbb R,                                                        \tag{O4.3o}
\]

where `Herm_0` is the traceless subspace.  With

\[
 \jmath(c)={c\over2^N}I,\qquad
 \mathsf H(X)=X-{\operatorname{Tr}X\over2^N}I,
\]

one has

\[
 \iota\mathsf H+\jmath\operatorname{Tr}=\operatorname{id},\qquad
 \operatorname{Tr}\iota=0,\qquad
 \operatorname{Tr}\jmath=\operatorname{id}.                       \tag{O4.3p}
\]

Therefore every real-linear functional `F` that kills all traceless
variations is a scalar multiple of trace.

The circuit-selector version is already forced at linear gate budget.
Assume the circuit class can prepare, independently on every qubit, the four
states

\[
 |0\rangle,\quad |1\rangle,\quad |+\rangle,\quad |+i\rangle
                                                                    \tag{O4.3q}
\]

using at most `c_0N` gates in total.  Let `T_N` be the resulting `4^N`
product-state projectors.  The four one-qubit projectors span
`Herm(C^2)`, since

\[
\begin{aligned}
 I&=P_0+P_1,& Z&=P_0-P_1,\\
 X&=2P_+-I,& Y&=2P_{+i}-I .
\end{aligned}
\]

Tensoring shows that `T_N` spans `Herm(H)`.  Every member has trace one, so
for any fixed `sigma_0 in T_N`,

\[
 \operatorname{span}\{\sigma-\sigma_0:\sigma\in T_N\}
 =\operatorname{Herm}_0(\mathcal H).                              \tag{O4.3r}
\]

Indeed, write a traceless `X` as `sum_sigma a_sigma sigma`.  Taking traces
gives `sum_sigma a_sigma=0`, and hence
`X=sum_sigma a_sigma(sigma-sigma_0)`.

It follows that if a linear observable `F` is insensitive to which
`c_0N`-gate target the adaptive circuit selector chooses,

\[
 F(\sigma)=F(\sigma_0)\qquad(\sigma\in T_N),
\]

then `F` kills (O4.3r), factors through trace by (O4.3p), and is constant on
**every** density matrix.  Thus no selector-independent linear statistic can
separate an evolved state from all short-circuit states beyond the first
tomographically complete gate budget.

This is the valid transfer of the orientation--transgression law: labels
must be retained through a nonlinear or relative construction before the
final scalar trace.  Replica powers do this algebraically, but the Riemann
source theorem supplies neither their positive Bellman bound nor the radial
shortcut estimate (O4.3i).  Its Green primitive cannot be imported as a
word-metric calibration without first constructing a circuit-boundary
complex and proving that its relative primitive escape is quantitatively
equivalent to robust gate distance.  Naming that missing complex would only
rename O4.

#### Hellinger--Hodge--Green transfer audit

The `riemann-hellinger-hodge-green-descent` paper reinforces the
labels-before-scalarization rule, but it does not supply a positive O4
estimate.  Its Hellinger density is the geometric mean of two prescribed
Bernoulli source occupations.  Its Hodge and Green transports are linear.
The circuit selector is instead a positive nonlinear infimum over a growing
word ball.  No map in that paper controls the associated support function,
shortcut-centre packing, or annular volume.

The updated paper does sharpen two exclusions.  First, its
uniform-capacity selector is powered by the split factor
`exp(c (Re rho-1/2))`.  Autonomous Hermitian evolution has only compact
characters `exp(-it E_j)`, so its split coordinate is identically zero.
Uniform boundedness of those characters is automatic for every spectrum and
cannot distinguish a long circuit from a shortcut.  The paper's compact
recurrence rank and torus-Haar law therefore transfer only to the completed
time plateau; they contain neither a first-hard-time estimate nor a word
metric lower bound.

Second, the paper's strict-reduction theorem gives a quantitative obstruction
to replacing the circuit union by one linear Hilbert reporter.  Let `W` be
any finite set of `N` distinct circuit labels and let

\[
             L:\ell^1(W)\longrightarrow \mathcal H
\]

be bounded, with `\mathcal H` Hilbert.  There is a signed packet `x` supported
on `W` such that

\[
 \|x\|_1=N,\qquad \|Lx\|^2\le N\|L\|^2.             \tag{O4.H1}
\]

Hence every lower modulus `c_W` satisfying
`c_W\|x\|_1\le\|Lx\|` obeys

\[
                    c_W\le {\|L\|\over\sqrt N}.      \tag{O4.H2}
\]

For arbitrary continuous two-qubit gates, finite target subsets have
unbounded `N`; for a finite alphabet, any exponentially growing family of
distinct word targets makes `(O4.H2)` exponentially small.  Thus a common
linear `\ell^1`-to-Hilbert reporter cannot retain the uniform stability needed
to survive the circuit union.  The finite signed-packet statement is already
proved in the corpus as `exists_lpOne_signed_packet_hilbert_bound`; the
infinite no-lower-modulus form is
`lpOne_to_innerProduct_not_boundedBelow`.  This does not exclude a nonlinear
selector-aware calibration, but it removes the updated paper's common-Hardy-
reporter architecture from the O4 frontier.

The positive survivor is a selector-aware use of Hellinger geometry that
retains the Hamiltonian label.  Let `theta` have probability law `eta`; in
the intended application `theta=H`.  On an observation space with reference
measure `mu`, let `p_theta` be the nonnegative endpoint density and let
`q_(theta,c)` be the nonnegative density associated with circuit target `c`.
Choose one strictly positive certificate `f_theta`, and put

\[
 \operatorname{Aff}(\theta,c)
   =\int\sqrt{p_\theta q_{\theta,c}}\,d\mu,qquad
 h(\theta)=\int f_\theta p_\theta\,d\mu.                \tag{O4.H3}
\]

Suppose a nonnegative integrable `r(theta)` controls **every** circuit in the
same Hamiltonian fibre,

\[
       \int {q_{\theta,c}\over f_\theta}\,d\mu
       \le r(\theta)\qquad(c\in C_\theta),               \tag{O4.H4}
\]

and let `c(theta)` be any Hamiltonian-dependent selector.  If on an event
`A` of Hamiltonians its selected target has affinity at least `alpha>0`,

\[
       \theta\in A\quad\Longrightarrow\quad
       \alpha\le\operatorname{Aff}(\theta,c(\theta)),    \tag{O4.H5}
\]

then the **resolved Hellinger selector-removal law** is

\[
 \boxed{\quad
       \eta(A)\le {\mathbb E_\eta h+\mathbb E_\eta r\over2\alpha}.
 \quad}                                                   \tag{O4.H6}
\]

Indeed, pointwise weighted arithmetic--geometric mean gives
`2 sqrt(p q)<=f p+q/f`.  Integrating first over the observation space gives
`2 Aff(theta,c)<=h(theta)+r(theta)` uniformly in `c`.  Apply this to the
selected `c(theta)` on `A`, integrate over `A`, and use nonnegativity to
enlarge the last integral to the whole Hamiltonian space.

`[PAPER-PROVED, LEAN PENDING]`  In a finite observation space the common
certificate has an exact minimax classification.  Let `p_i>0` be a
probability vector, let `(q_(c,i))_(c in C)` be finitely many probability
vectors, and assume every observation coordinate occurs in at least one
`q_c`.  Define the optimal common reciprocal-certificate cost

\[
 \mathcal B(p,Q)=\inf_{f_i>0}\left\{
   \sum_i p_i f_i+\max_{c\in C}\sum_i{q_{c,i}\over f_i}
                              \right\}.                \tag{O4.H7}
\]

If `Delta(C)` is the probability simplex on circuit labels and
`q_lambda=sum_c lambda_c q_c`, then

\[
 \boxed{\quad
 \mathcal B(p,Q)=
   2\max_{\lambda\in\Delta(C)}\sum_i\sqrt{p_iq_{\lambda,i}}.
 \quad}                                                \tag{O4.H8}
\]

To prove this, write the maximum in `(O4.H7)` as a maximum over
`lambda in Delta(C)`.  The resulting function

\[
 F(f,\lambda)=\sum_i p_i f_i+\sum_i{q_{\lambda,i}\over f_i}
\]

is convex and continuous in the positive vector `f` and affine in `lambda`.
The coordinate-covering assumption and `p_i>0` make its lower envelope
coercive at both ends of every coordinate, so the minimax theorem applies.
For fixed `lambda`, coordinatewise arithmetic--geometric mean gives

\[
 \inf_{f_i>0}F(f,\lambda)
   =2\sum_i\sqrt{p_iq_{\lambda,i}},
\]

including the limiting value zero in coordinates where `q_(lambda,i)=0`.
This proves `(O4.H8)`.

Consequently the resolved Hellinger route is nontrivial only if the endpoint
observation law is quantitatively separated from the **convex hull** of all
short-circuit observation laws, not merely from every fixed circuit law.
Indeed, if `p in conv{q_c}`, the right side of `(O4.H8)` is two: choose
`q_lambda=p`, while Hellinger affinity of probability vectors is at most
one.  The event bound `(O4.H6)` is then no better than the trivial probability
bound.  In particular, a single ordinary projective measurement cannot close
O4 once its low-complexity target family contains the measurement-basis
states: their point-mass outcome laws convexly generate every `p`.  A useful
certificate must therefore retain coherent or replica information for which
the shortcut convex hull has a proved quantitative deficit.  Establishing
that deficit at the required linear-in-time rate is again the substantive
O4 theorem, but `(O4.H8)` rules out hiding it inside a choice of scalar
Hellinger weight.

`[BRIDGE] [LEAN-PROVED]`  The exact continuum-parameter, continuum-observation
statement is `resolvedHellinger_selectorRemoval` in
`HTGeometry/ResolvedHellingerSelectorRemoval.lean`; its only axioms are the
standard Mathlib foundations `propext`, `Classical.choice`, and `Quot.sound`.
It does not union-bound circuit words, replace the adaptive selector by a
fixed target, commute a supremum with ensemble expectation, or force an
infinite `ell^1` family through a linear Hilbert map.  It turns O4 into the
construction of one positive nonlinear barrier `f(H,z)` whose reciprocal
cost is uniform over the entire low-circuit fibre.  The transported-parent/
dynamical-NLTS route below is one possible source.  No such exponential
barrier is supplied by the Riemann paper.  Choosing `f` from distance to the
circuit set would be circular; the certificate must come from independently
controlled local dynamics and achieve the full linear-in-time rate.

#### Selector-aware Gaussian-process audit: why spin-glass NLTS does not transfer

`[LITERATURE BOUNDARY]`  Al-Ghattas--Gamarnik, *Circuit complexity lower
bounds for quantum spin glasses*, arXiv:2607.14384v2 (2026), is the first
audited result here that controls a Gaussian process **after** taking the
supremum over an ancilla-uniform circuit class.  For a depth-`D` circuit
state `rho`, they subtract the product of its one-site marginals and write

\[
 \operatorname{Tr}(H\rho)
 =\operatorname{Tr}(H m(\rho))
  +\operatorname{Tr}(H(\rho-m(\rho))).                 \tag{O4.G1}
\]

Disjoint backward supports kill the residual coefficients.  Pruning the
remaining backward cones and applying a Gaussian entropy bound controls the
last term uniformly over all depth-`D` circuits, independently of the number
of ancillas.  This is a genuine selector-aware advance over a circuitwise
union bound.

It cannot certify autonomous complexity growth from a simple input.  If

\[
 \rho_t=e^{-itH}\rho_0e^{itH},
\]

then cyclicity of trace gives the exact conservation identity

\[
 \boxed{\quad \operatorname{Tr}(H\rho_t)
                 =\operatorname{Tr}(H\rho_0)\quad(t\in\mathbb R).\quad}
                                                               \tag{O4.G2}
\]

Because `rho_0` belongs to the simple-state class, the evolved endpoint can
never exceed the simple-state energy optimum used by `(O4.G1)`.  More
generally, for every observable `A=f(H)` obtained by functional calculus,

\[
 \operatorname{Tr}(A\rho_t)=\operatorname{Tr}(A\rho_0)
 \leq\sup_{\sigma\in\mathcal S}\operatorname{Tr}(A\sigma)
 \qquad(\rho_0\in\mathcal S).                              \tag{O4.G3}
\]

Thus no conserved spectral observable can separate an autonomous endpoint
from any comparison class containing its initial state.  Replacing energy by
a fixed-observable current does not create a persistent signed certificate:

\[
 j_{H,A}(t):=i\operatorname{Tr}(\rho_t[H,A])
 ={d\over dt}\operatorname{Tr}(A\rho_t),
 \qquad
 \left|\int_a^b j_{H,A}(t)\,dt\right|\leq2\|A\|.        \tag{O4.G4}
\]

Hence a time-independent positive gap in one signed commutator current can
last for at most `2||A||/gap`.  This is the conserved/coboundary obstruction
for disorder-linear dynamical witnesses.

The Hodge--Green viewpoint closes the entire **fixed linear observable**
version of this loophole in finite dimension.  In an energy basis of `H`,
let `Pi_H W` retain exactly the zero-gap entries of an arbitrary observable
`W`, and let

\[
 (G_H W)_{ab}=\begin{cases}
 0,&E_a=E_b,\\
 W_{ab}/(E_a-E_b),&E_a\ne E_b.
 \end{cases}
\]

Then, with `A=-i G_H W`,

\[
 \boxed{\qquad W=\Pi_H W+i[H,A].\qquad}                 \tag{O4.G5}
\]

The first term commutes with `H`; the second is an exact Liouvillian
coboundary.  Therefore every fixed linear signal along the autonomous orbit
has the normal form

\[
 \operatorname{Tr}(W\rho_t)
 =\operatorname{Tr}(\Pi_H W\rho_0)
   +{d\over dt}\operatorname{Tr}(A\rho_t).
                                                               \tag{O4.G6}
\]

For each fixed finite `H` and `W`, its integrated deviation from the
stationary value is bounded by `2||A||`.  This is not a system-size-uniform
O4 bound: `||A||` can diverge with inverse spectral gaps.  It is nonetheless
an exact route classification.  A persistent complexity certificate cannot
be one fixed linear observable.  It must be time-dependent, nonlinear in the
state (for example a support function or replica statistic), or carry a
separately proved uniform inverse-gap estimate strong enough for the intended
time scale.

`[BRIDGE] [LEAN-PROVED ALGEBRAIC CORE]`  The decomposition `(O4.G5)` is
`transitionGap_hodgeGreen_decomposition` in
`HTGeometry/FiniteLiouvillianHodgeGreenLaw.lean`; its only axioms are the
standard Mathlib foundations `propext`, `Classical.choice`, and `Quot.sound`.
Equation `(O4.G6)` is the ordinary finite-dimensional Schrödinger derivative
of `(O4.G5)` and is not used as a final-paper claim until its calculus layer
is separately formalized.

There is a second scale mismatch.  The Al-Ghattas--Gamarnik variance gain is
the disjointness of depth-`D` backward supports, whose cardinalities grow as
`2^D`; it becomes vacuous once `D` reaches order `log n`.  Their theorem
accordingly proves logarithmic depth, not gate count of order `2^n`.  No
iteration is available after light cones cover the system.

`[OPEN SURVIVOR]`  A Gaussian-supremum attack on `(O4.3)` would therefore
need a new observable family `W_(H,t)` satisfying all three properties
simultaneously:

1. `W_(H,t)` is sufficiently linear in the quenched disorder for a
   selector-aware Gaussian-process bound to survive;
2. the autonomous endpoint has a proved positive advantage over the entire
   `s`-gate class at `s=Theta(t/poly(n))`; and
3. the advantage is neither a conserved spectral expectation `(O4.G3)` nor
   a bounded signed coboundary `(O4.G4)`, and its circuit residual continues
   to contract after every ordinary light cone has saturated.

No such witness is supplied by spin-glass NLTS.  Producing it would be a
substantive route to `(O4.3)`; merely applying the published energy residual
to `rho_t(H)` gives exactly the initial product-state benchmark and proves
nothing about dynamical complexity.

There is also a decisive Hellinger obstruction to importing “Haar-like
bulk plus one exceptional recurrence component.”  Homogeneity of the full
local coefficient family strengthens it to a permanent separator without
spending even one dimension on time.  Let
`\mathcal P_D=CP^(D-1)` be pure-state space with normalized Fubini--Study
measure `sigma_D`, let `H(x)=sum_(j=1)^m x_j A_j`, and define the complete
autonomous reachability map

\[
 \widehat F:\mathbb R^m\times\mathbb R\longrightarrow\mathcal P_D,
 \qquad \widehat F(x,t)=[e^{-itH(x)}\Phi_0].
\]

Since `tH(x)=H(tx)`, this map factors through
`G(y)=[e^{-iH(y)}\Phi_0]` and

\[
 \mathfrak M:=\widehat F(\mathbb R^m\times\mathbb R)
              =G(\mathbb R^m).
\]

The matrix exponential is smooth, so `G` is Lipschitz on every compact
cube.  The set `\mathfrak M` is a countable union of compact sets and hence
Borel.  When

\[
 m<2D-2=\dim_{\mathbb R}\mathcal P_D,                 \tag{O4.3x}
\]

Lipschitz monotonicity of Hausdorff dimension on each cube gives
`\dim_H\mathfrak M\leq m`; comparison with the smooth
`(2D-2)`-dimensional Fubini--Study volume therefore gives

\[
 \sigma_D(\mathfrak M)=0,\qquad
 \nu(\mathfrak M)=1,\qquad \nu\perp\sigma_D           \tag{O4.3y}
\]

for every probability law `\nu=\widehat F_\#\lambda`, with arbitrary joint
coefficient--time law `\lambda`.  In particular the same single set
`\mathfrak M`, independent of time and of the coefficient distribution,
supports every fixed-time endpoint law and separates every one of them from
Haar.  Consequently

\[
 \operatorname{Aff}(\nu,\sigma_D)=0,\qquad
 H^2(\nu,\sigma_D)=1,\qquad
 \|\nu-\sigma_D\|_{\rm TV}=1,                         \tag{O4.3z}
\]

with the convention `H^2=1-Aff`.  The identical factorization and proof for
`(x,t)\mapsto[e^{-itH(x)}]\in PU(D)` gives a single Haar-null autonomous
unitary-reachability set whenever `m<D^2-1`.  For fixed `q`,
`m=sum_(k<=q)3^k binom(n,k)=poly(n)` while `D=2^n`, so both dimension
inequalities hold throughout the many-body regime.

Thus `[BRIDGE]` the entire all-time static-local family is permanently and
maximally singular from Haar, even if many coarse observables look
Haar-random.  This is a dependency-closed paper proof, but it is not the O4
complexity theorem: the perfect separator `1_\mathfrak M` is merely Borel
and need not be continuous, efficiently computable, or physically
measurable.  A device-feasible witness remains separate.  Hellinger or
total-variation closeness cannot leave a positive-mass Haar component to
which a circuit union is applied.  The other useful transfer from the
Riemann paper is methodological: retain every circuit label until a
nonlinear aggregate is formed.  In O4 that aggregate is precisely
`mathfrak S_(epsilon,a)` or its packing number `(O4.3t)`; the paper supplies
no bound on either.  Its table row labelled “Quantum recurrence” is a
two-state zero-temperature Gibbs purity/coherence limit; it contains no
return theorem for a unitary orbit and no circuit-complexity statement.

#### Hard-frontier audit: deterministic complexity production

The preceding formulation still permits misleading auxiliary progress unless
one isolates what the static problem lacks.  If

\[
 H(J)=\sum_{a=1}^{m}J_aP_a,\qquad
 F_t(J)=e^{-itH(J)}\Phi_0 ,
\]

then Duhamel's inequality gives

\[
 d(F_t(J),F_t(J'))\leq |t|\,L_H\|J-J'\|.
 \tag{O4.3a}
\]

Consequently the fixed-resolution metric entropy of the entire quenched
endpoint ensemble on a bounded coefficient set is at most

\[
 \log N_\varepsilon(F_t(K))
 \leq
 m\log\!\left(1+{C|t|\over\varepsilon}\right).
 \tag{O4.3b}
\]

Thus a static `m`-parameter law supplies only `O(m log t)` newly resolvable
coefficient bits by time `t`.  A lower bound of order `t` cannot be an
information-theoretic consequence of fresh disorder, ensemble dimension,
Haar volume, or parameter anti-concentration.  It must prove that a
short-description autonomous law **deterministically expands** those few
resolved bits into an endpoint having word complexity of order `t`.  This is
the quantum-circuit analogue of proving a pseudorandom generator hard against
nonuniform distinguishers; it is precisely the step absent from current
static-Hamiltonian methods.

The approximate-centralizer reformulation does not reduce this difficulty.
Every `epsilon`-approximant `V` to `e^{-itH}` satisfies

\[
 \|[H,V]\|\leq2\epsilon\|H\|,
 \tag{O4.3c}
\]

but the exact commutant of a simple-spectrum `H` already contains every
spectral function `f(H)`, including `e^{-itH}` itself.  Therefore a
"low-circuit approximate-centralizer rigidity" theorem strong enough to
exclude `V` must lower-bound the circuit complexity of nontrivial spectral
functions of `H`; that is O4 again, not a bridge to it.  The identity also
shows that small commutator alone contains no time information.

Likewise, word-height Diophantine extremality can at most explain the
completed plateau.  At fixed resolution it compares the word ball with a
low-dimensional analytic endpoint manifold and can force generic avoidance
near ambient capacity.  It cannot produce the pre-saturation slope: direct
Hamiltonian simulation places `F_t(K)` inside a word tube of radius
`O(t poly(n))`, while the constants measuring finite-time nondegeneracy of
that manifold necessarily collapse at exactly the rate whose lower bound O4
asks for.  Any claimed dynamic consequence that leaves those constants
uncontrolled is circular.

The 2025 spacetime-complexity construction of Du--Liu--Ma is an important
boundary case, not a solution.  It writes a depth-`T` random circuit into
`Theta(T)` spatial columns of a commuting two-dimensional Hamiltonian and
obtains a hard projected endpoint after constant physical time.  The fresh
random description and circuit volume are spatial.  It proves that static
local evolution can *read* extensive complexity already stored across the
Hamiltonian, but not that one fixed finite system produces new word
complexity linearly for exponentially long time.

Hence the actual frontier is narrower and harder than "static chaos":

> **Static seed-expansion theorem.**  Prove that exponentiation of a
> polynomial-description, fixed-locality Hamiltonian is an unconditional
> robust word-metric expander along its own one-parameter orbit, despite zero
> fresh disorder, a Hamiltonian-dependent circuit selector, and exact
> quasiperiodicity.

For a concrete Gaussian ensemble this theorem must be stated as (O4.3).
Spectral ramps, maximal rational rank, designs of fixed order, operator
spreading, NLTS, local distinguishability, commutant rigidity without a
quantitative word bound, and space-for-time encodings do not prove it.  Any
further route is rejected unless its headline estimate already contains the
Hamiltonian-dependent circuit infimum at fixed error.

#### Radial shortcut-codimension equivalence

`[BRIDGE] [PAPER-PROVED]` There is an exact representation of the remaining
theorem in which physical time is no longer a separate variable.  Assume the
Hamiltonian map is linear, write `H(x)=sum_a x_a P_a`, and let `Lambda` be the
homogeneous simulation cost.  Define the fixed radial shortcut locus

\[
 \mathfrak S_{\varepsilon,a}
 =
 \left\{x\in\mathbb R^m:
 C_\varepsilon(e^{-iH(x)}\Phi_0)
 \leq {a\Lambda(H(x))\over\operatorname{poly}(n)}
 \right\}.
 \tag{O4.3d}
\]

For every coefficient direction `J` and every `t>0`, linearity and
homogeneity give the exact identities

\[
 e^{-itH(J)}=e^{-iH(tJ)},\qquad
 t\Lambda(H(J))=\Lambda(H(tJ)).
 \tag{O4.3e}
\]

Hence, on a fixed energy shell with normalized angular measure `sigma`,
(O4.3) is exactly the spherical estimate

\[
 \sigma\{\theta:t\theta\in\mathfrak S_{\varepsilon,a}\}
 \leq C t^{-\kappa},
 \qquad \kappa=cm ,
 \tag{O4.3f}
\]

through the pre-saturation radial range.  The Brown--Susskind cut problem is
therefore a statement that the robust low-relative-word locus loses a fixed
fraction of the **volume-growth exponent** of local-Hamiltonian parameter
space at infinity.

For the unconditioned centered Gaussian ensemble the equivalence is a volume
theorem.  Let `gamma_m` be standard Gaussian measure and let `B` be any
measurable subset of `R^m`.  For `0<kappa<m`, the following two estimates are
equivalent up to constants depending only on `m,kappa`:

\[
 \gamma_m\{J:tJ\in B\}\leq Kt^{-\kappa}
 \quad(t\geq1),                                        \tag{O4.3g}
\]

and

\[
 \operatorname{vol}(B\cap B_R)
 \leq K'R^{m-\kappa}
 \quad(R\geq1).                                        \tag{O4.3h}
\]

Indeed, `(O4.3g)` at `t=R` and the lower bound

\[
 (2\pi R^2)^{-m/2}e^{-1/2}
\]

for the `N(0,R^2I_m)` density on `B_R` prove `(O4.3h)`.  Conversely, split
`B` into `B_t` and the dyadic annuli
`B_{2^{j+1}t}\setminus B_{2^jt}`.  On the `j`th annulus the scaled Gaussian
density is at most

\[
 (2\pi t^2)^{-m/2}e^{-2^{2j-1}},
\]

while `(O4.3h)` bounds its volume by
`K'(2^{j+1}t)^{m-\kappa}`.  The resulting series converges and gives
`(O4.3g)`.

Applied to `B=mathfrak S_(epsilon,a)`, this proves:

> **Radial shortcut-codimension theorem.**  Aggregate quenched linear
> complexity growth with failure `t^(-kappa)` is equivalent to polynomial
> volume growth of the complete Hamiltonian-dependent shortcut locus with
> upper radial volume-growth exponent at most `m-kappa`.

`[FALSIFIED]` This is not a Hausdorff-, Minkowski-, semialgebraic-, or
local-dimension statement.  At strict error tolerance, the preimage of one
circuit ball is open whenever nonempty, so `mathfrak S_(epsilon,a)` can have
ordinary local dimension `m` even when `(O4.3h)` holds with a large exponent
deficit.  The required invariant measures the sparse number and total volume
of open shortcut islands encountered as the coefficient radius grows.
Consequently an algebraic-codimension or transversality argument that only
proves each exact-relation locus has positive codimension cannot establish
O4.

This is stronger than saying each fixed circuit has a transverse preimage.
The union over all words whose permitted length grows radially is already
inside `mathfrak S_(epsilon,a)`.  Thus the exact remaining mathematical task
is to prove a deficit in the radial volume-growth exponent of that single
global set.  Word-by-word transversality, even if sharp, does not imply
`(O4.3h)`.

`[OPEN CORE]` Prove the annular form

\[
 \operatorname{vol}\!\left(
 \mathfrak S_{\varepsilon,a}\cap
 \{x:R\leq\|x\|\leq2R\}\right)
 \leq C R^{m-\kappa}
 \tag{O4.3i}
\]

uniformly before the circuit-capacity radius.  Because the left side is a
union of full-dimensional open islands and already contains the
Hamiltonian-dependent word selector, `(O4.3i)` is the first claim in this
section whose proof would cross the Brown--Susskind frontier.

The selector can nevertheless be eliminated **once**, without a circuit
union, by passing to shortcut-centre packing.  For a bounded set `A`, let
`N_r(A)` be its Euclidean `r`-packing number.  A maximal `r`-separated
subset has `r`-balls covering `A`, hence

\[
 \operatorname{vol}(A)\leq v_m r^m N_r(A).            \tag{O4.3s}
\]

Therefore the genuinely sufficient anti-concentration statement is the
single selector-aware bound

\[
 N_r\!\left(
 \mathfrak S_{\varepsilon,a}\cap
 \{x:R\leq\|x\|\leq2R\}\right)
 \leq C_r R^{m-\kappa}.                               \tag{O4.3t}
\]

Unlike a fixed-target cap estimate, `(O4.3t)` counts every separated
Hamiltonian-dependent shortcut island, with every circuit target already
selected, exactly once.

`[BRIDGE] [PAPER-PROVED]` This packing formulation is equivalent to the
annular volume law after an arbitrarily small robustness margin.  Choose
`epsilon_-<epsilon_+` and `a_-<a_+`.  Suppose the linear Hamiltonian map and
the homogeneous simulation cost obey

\[
 \|H(x)-H(x')\|\leq L_H\|x-x'\|,\qquad
 |\Lambda(H(x))-\Lambda(H(x'))|\leq L_\Lambda\|x-x'\|,
\]

and `Lambda(H(x))>=lambda_-||x||`.  If

\[
 r\leq{\varepsilon_+-\varepsilon_-\over L_H},\qquad
 R\geq
 {a_+L_\Lambda r\over(a_+-a_-)\lambda_-},             \tag{O4.3u}
\]

then every `x` in the strict shortcut locus
`mathfrak S_(epsilon_-,a_-)` with `||x||>=R` satisfies

\[
 B(x,r)\subset\mathfrak S_{\varepsilon_+,a_+}.         \tag{O4.3v}
\]

Indeed, Duhamel continuity lets the same circuit approximate every endpoint
in the ball within `epsilon_+`.  Moreover

\[
 a_-\Lambda(H(x))
 \leq a_+\bigl(\Lambda(H(x))-L_\Lambda r\bigr)
 \leq a_+\Lambda(H(x')),
\]

where the first inequality is exactly `(O4.3u)`.  Thus the same circuit also
obeys the relaxed relative-word budget.

Now take an `r`-separated family in the strict annular locus.  Its disjoint
`r/2`-balls lie in the relaxed locus and in the enlarged annulus
`R-r<=||x||<=2R+r`.  Consequently

\[
 N_r\!\left(
 \mathfrak S_{\varepsilon_-,a_-}\cap
 \{R\leq\|x\|\leq2R\}\right)
 \leq
 { \operatorname{vol}\!\left(
 \mathfrak S_{\varepsilon_+,a_+}\cap
 \{R-r\leq\|x\|\leq2R+r\}\right)
  \over v_m(r/2)^m}.                                  \tag{O4.3w}
\]

Equations `(O4.3s)` and `(O4.3w)` show that robust annular volume deficit and
robust shortcut-centre packing deficit are the same theorem up to constants
and margins.  They also locate the irreducible task: prove `(O4.3t)`
directly.  No targetwise Haar cap can imply it unless it has already removed
the union of shortcut tubes whose packing `(O4.3t)` is meant to bound.

#### Fast-forwarding codimension: forced half and inverse frontier

`[FALSIFIED]` Neither spectral chaos nor the dimension of the dynamical Lie
algebra can be the missing invariant by itself.  Commuting Hamiltonians,
quadratic fermions, efficiently block-diagonalizable spin systems, and several
Cartan-synthesizable models are all fast-forwardable for different algebraic
reasons.  Conversely, a term-generated dynamical Lie algebra forgets the
coefficients, although those coefficients can change the dynamics radically.
Thus the conjecture "large Lie algebra implies no shortcuts" is too coarse,
while "nonintegrable implies no shortcuts" has no quantitative content.

`[LOCAL-RESEARCH] [PAPER-PROVED]` A previously omitted obstruction fixes the
largest exponent that any version of `(O4.3)` can have.  First, the obstruction
does not require commutativity.  Let `F` be an `f`-dimensional linear subspace
of coefficient space, with orthogonal projection `pi_F`, and suppose one fixed
finite-format synthesis scheme prepares

\[
 e^{-iH(y)}\Phi_0\quad(y\in F)                                \tag{O4.3aa0}
\]

to error `epsilon_-` using at most `B` local gates, uniformly in `y`.  For a
fixed finite universal gate set this means a bounded word dictionary; for
adjustable local gates it may be one architecture with variable parameters.
The concrete certificate, rather than membership in the shortcut locus, is
part of the hypothesis.  Assume

\[
 \|H(x)-H(y)\|\leq L_H\|x-y\|,
 \qquad \Lambda(H(x))\geq\lambda_-\|x\|.                     \tag{O4.3aa1}
\]

Put `d=m-f`, choose

\[
 0<r\leq {\epsilon_+-\epsilon_-\over L_H},
\]

and let `J` be standard Gaussian in `R^m`.  Independence of its orthogonal
projections gives, for `t>=max{2r,1}`,

\[
 \begin{split}
 &\mathbb P\{1\leq\|\pi_FJ\|\leq2,
              \ \|(I-\pi_F)J\|\leq r/t\}\\
 &\qquad\geq
 p_f(2\pi)^{-d/2}e^{-1/2}v_d r^d t^{-d},             \tag{O4.3aa2}
 \end{split}
\]

where `p_f=P{1<=||pi_F J||<=2}>0` and `v_d` is unit-ball volume.  On this event
set `y=t pi_F J`.  Duhamel continuity proves

\[
 \|e^{-itH(J)}\Phi_0-e^{-iH(y)}\Phi_0\|
 \leq L_Ht\|(I-\pi_F)J\|\leq\epsilon_+-\epsilon_- .  \tag{O4.3aa3}
\]

Moreover `||tJ||>=t-r>=t/2`.  Hence, once

\[
 t\geq {2B\operatorname{poly}(n)\over a\lambda_-},             \tag{O4.3aa4}
\]

the same architecture is within the relative shortcut budget at `tJ`.
Therefore every `f`-dimensional uniformly synthesizable coefficient subspace
forces shortcut probability `Omega(t^{-(m-f)})`.  Deterministically, its
fixed-radius tube has annular volume `Omega(R^f)`.  This argument extends
verbatim to a tame proper synthesis stratum once its fixed-radius tube has
that volume growth.

The commuting case supplies an especially strong **recurrent** subevent.  Let

\[
 H(x)=\sum_{j=1}^m x_jP_j,
 \qquad \|P_j\|\leq1,
 \tag{O4.3aa}
\]

and suppose `P_1,...,P_f` are pairwise commuting Hermitian involutions.  Let
`J_1,...,J_m` be independent standard Gaussians.  For `0<eta<=1`, put
`delta=eta/m`.  If `t>=4pi`, then the event

\[
 \begin{split}
  &\operatorname{dist}(tJ_j,2\pi\mathbb Z)\leq\delta
       &&(1\leq j\leq f),\\
  &|tJ_j|\leq\delta
       &&(f<j\leq m)
 \end{split}                                                   \tag{O4.3ab}
\]

is contained in the `eta`-ball about the initial endpoint:

\[
 \|e^{-itH(J)}-I\|\leq\eta.                                  \tag{O4.3ac}
\]

Indeed, choose integers `k_j` in `(O4.3ab)` and set
`J_j^0=2pi k_j/t` for `j<=f`, `J_j^0=0` otherwise.  Commutativity and
`P_j^2=I` give

\[
 e^{-itH(J^0)}=\prod_{j=1}^f e^{-2\pi i k_jP_j}=I,
\]

while Duhamel's inequality gives

\[
 \|e^{-itH(J)}-I\|
 \leq t\|H(J)-H(J^0)\|
 \leq\sum_{j=1}^m t|J_j-J_j^0|\leq m\delta=\eta.
\]

This event has an explicit lower probability of the form

\[
 \mathbb P\bigl((\mathrm{O4.3ab})\bigr)
 \geq
 \left({\varphi(1)\delta\over2\pi}\right)^f
 \left(2\varphi(1)\delta\right)^{m-f}
 t^{-(m-f)},                                                  \tag{O4.3ad}
\]

where `varphi` is the standard Gaussian density.  For a transverse coordinate,
integrating over `[-delta/t,delta/t]` gives the second factor.  For a commuting
coordinate, take all disjoint intervals of radius `delta/t` centred at
`2pi k/t` inside `[-1/2,1/2]`.  There are at least `t/(4pi)` such intervals;
their total length is at least `delta/(2pi)`, and the Gaussian density is at
least `varphi(1)` on them.  Independence proves `(O4.3ad)`.

The identity word therefore witnesses a robust shortcut for every initial
state on `(O4.3ab)`.  Consequently, any upper law with failure
`O(t^{-kappa})`, uniform in the pre-capacity range with constants that do not
absorb an additional power of `t`, must satisfy

\[
 \boxed{\ \kappa\leq m-f.\ }                                  \tag{O4.3ae}
\]

The same result has a deterministic geometric form.  The exact recurrence
lattice `(2pi Z)^f times {0}^{m-f}` supplies `Theta(R^f)` separated centres in
an annulus of radius `R`.  Fixed small full-dimensional balls about them lie in
a relaxed shortcut locus by Duhamel continuity.  Hence its annular volume is
at least `c_{m,f,eta}R^f`.  This proves `(O4.3ae)` directly from `(O4.3i)` as
well.  The exponent `kappa approximately m` previously suggested by one
periodic ray is not sharp whenever an extensive commuting sector is present.

For the all-to-all fixed-`q` Pauli ensemble, all nonempty `Z` strings of weight
at most `q` form such a sector, so

\[
 f_Z(n,q)=\sum_{k=1}^q {n\choose k},\qquad
 m(n,q)=\sum_{k=1}^q3^k{n\choose k},                            \tag{O4.3af}
\]

and every admissible no-shortcut exponent obeys
`kappa<=m-f_Z`.  This is a theorem, not the desired upper bound.  It identifies
a mandatory obstruction that an upper bound must match; a larger
fast-forwardable stratum would strengthen it further.

`[SUPERSEDED 2026-08-05 — AUTONOMOUS SHORTCUT ORGANIZATION LAW.]`
The continuous-dimension-only representation below is retained as route
history.  It is not the active conjecture: mixed continuous/periodic carriers,
observer-stationary kernels, component entropy, and fixed-size saturation
falsify `m-f_*` as a universal scalar law.  The later finite-scale shortcut
free-energy replacement was itself killed as mathematically underdefined and
potentially circular.  The active exact conjecture is now the concrete
selector-aware Pauli law in `observer-rank-autonomous-no-shortcut-law.md`.

Fix an error margin and a sub-direct-simulation word budget.  A
`d`-dimensional **uniform synthesis stratum** is a proper, polynomial-distortion
coefficient chart whose unit neighbourhood has annular packing growth
`Theta(R^d)` and whose whole autonomous endpoint family is prepared by one
uniform finite-format synthesis scheme within the budget.  Let `f_*` be the maximum
such radial dimension, allowing a finite polynomial-complexity stratification
(commuting, Cartan, quadratic, block-diagonal, and their efficiently conjugate
forms), but not defining a stratum merely as a subset of the shortcut locus.

Then, for the fixed-`q` Gaussian Pauli family throughout the pre-capacity
double-scaling window, the robust aggregate shortcut locus has radial
volume-growth exponent exactly `f_*`:

\[
 \operatorname{vol}\!\left(
  \mathfrak S_{\varepsilon,a}\cap\{R\leq\|x\|\leq2R\}
 \right)
 =R^{f_*+o(m)},                                                \tag{O4.3ag}
\]

equivalently its optimal Gaussian escape exponent is

\[
 \boxed{\ \kappa_*=m-f_*.\ }                                  \tag{O4.3ah}
\]

The lower/forced half is `(O4.3aa0)`--`(O4.3af)` for every certified synthesis
stratum; `(O4.3aa)`--`(O4.3af)` additionally isolate exact recurrent mass in
the commuting case.  The new inverse half says that an excess
of Hamiltonian-dependent shortcut islands cannot remain arithmetically
scattered: it forces a higher-dimensional uniformly synthesizable stratum.
This is an inverse theorem for autonomous quantum complexity, not a relabeling
of the shortcut set.

`[OPEN CORE]` Prove the inverse organization implication with quantitative
robustness and circuit-capacity uniformity:

\[
 \limsup_R {\log N_r(\mathfrak S_{\varepsilon,a}\cap A_R)
                 \over\log R}>d
 \quad\Longrightarrow\quad
 \text{a uniform synthesis stratum of radial dimension greater than `d`},
 \tag{O4.3ai}
\]

where `A_R={x:R<=||x||<=2R}` and the limit is taken only in the stated
pre-capacity double scaling.  Establishing `(O4.3ai)` at `d=f_*` would close
`(O4.3i)`, hence O4.  It would also classify the exceptional branch instead of
excluding it by an adjective: autonomous time is compressible precisely along
organized fast-forwardable directions and irreducible in the transverse
codimension.

`[HOSTILE REVIEW]` Four attacks remain live and must be discharged before this
conjecture can enter the paper as a result.

1. Isolated arithmetic resonances might proliferate faster than every uniform
   synthesis stratum without organizing into one; that would falsify
   `(O4.3ai)`.
2. Bethe-integrable or parameter-dependently diagonalizable families might be
   fast-forwardable without fitting one polynomial-distortion chart; the
   definition must include them without becoming circular.
3. The number of circuit architectures grows with `R`; an inverse theorem must
   control component proliferation, not only the dimension of each pullback.
4. At fixed `n`, circuit capacity eventually makes every endpoint easy.
   Therefore `(O4.3ag)` is meaningful only with explicit uniform constants in
   the pre-saturation `n,R` double scaling, never as `R->infinity` at fixed
   `n`.

`[LITERATURE]` Atia--Aharonov prove fast-forwarding/precise-measurement
equivalence and exhibit commuting and quadratic examples, but ask for a
physical classification of fast-forwardability.  Gu--Somma--Sahinoglu extend
the positive classes to efficiently block-diagonalizable, permutation-
invariant, low-energy frustration-free, quadratic fermionic, and quadratic
bosonic systems.  Kokcu et al. give time-independent-depth Cartan synthesis.
The 2-local spin DLA classification shows polynomial and exponential algebra
dimensions but explicitly notes that coefficient-blind DLA data do not fix
dynamics.  None of these sources proves an inverse measure theorem for the
complete Hamiltonian-dependent shortcut locus or the codimension identity
`(O4.3ah)`.

`[CORPUS]` The paper-proved card
`algebraic-two-local-instant-exact-complexity` supplies the qualitative
transcendental half that this conjecture needs.  It constructs a rational
two-local Hamiltonian for which every nonzero algebraic time has exponential
exact state complexity, and uses restricted-analytic o-minimality to make the
low-exact-complexity times locally finite.  Its hostile audit identifies the
same missing bridge: exact transcendence gives no fixed positive separation
from the semialgebraic short-circuit set.

`[LITERATURE-BRIDGE]` Papas's Ax--Schanuel theorem for the matrix exponential
provides the correct qualitative inverse geometry.  An exact intersection
between an algebraic source and an algebraic target cannot have excess
dimension unless it lies in a weakly special subvariety.  Crucially, the
published `GL_D` theorem requires the component to pass through zero and the
target through the identity.  The author explains that these restrictions are
forced by the non-discrete, sometimes positive-dimensional fibre
`exp^{-1}(I)` and leaves the full classification of the remaining type-II
weakly special sets open.  Thus the obstruction to full matrix
Ax--Schanuel is literally recurrence, not merely analogous to it.

`[CONJECTURE — QUANTITATIVE AUTONOMOUS AX--SCHANUEL FORM.]` Let
`L_n` be the complexified fixed-`q` local-Hamiltonian coefficient space and,
for a fixed state-preparation gate-support architecture `A`, let `S_A` be the
Zariski closure of its state image and use the state-lifted algebraic target

\[
 Z_A=\{U\in GL_D:U\Phi_0\in S_A\}.
\]

(This lift is required because the master theorem concerns state, not unitary,
complexity.)  Call a real stratum `W subset L_n` **special-easy** when
it is contained in a matrix-exponential weakly special/type-II recurrence
stratum and `exp(W)Phi_0` is covered by one sub-budget gate architecture.  The
algebraic part is the finite-format union of these certified strata; let its
maximal radial tube-growth exponent be `f_*`.

Then the complement of this algebraic part obeys a uniform approximate
Ax--Schanuel tube bound strong enough to survive the union over every
architecture of length `s<=aR/poly(n)`.  In particular, for some `delta>0`,

\[
 \operatorname{vol}\!\left(
  (\mathfrak S_{\varepsilon,a}\setminus
    \mathcal N_r(\mathfrak A_{n,s}))\cap A_R
 \right)
 \leq C R^{f_*-\delta},                                      \tag{O4.3aj}
\]

while the tube theorem `(O4.3aa0)`--`(O4.3aa4)` gives
`vol(N_r(mathfrak A_(n,s)) cap A_R)=R^(f_*+o(m))`.  Equation
`(O4.3aj)` therefore implies `(O4.3ag)` and `(O4.3ah)`.

This formulation identifies the missing new mathematics without pretending
that qualitative Ax--Schanuel proves a robust circuit bound:

> **Quantitative matrix-exponential unlikely intersections with growing
> targets.**  Excess fixed-radius tube volume in the preimage of a growing
> semialgebraic circuit variety must concentrate near a recurrent weakly
> special synthesis stratum.

It has three genuinely new requirements absent from the published theorem:
approximation at fixed radius rather than exact intersection, components away
from zero rather than only the identity component, and uniformity after the
complete circuit-architecture union.  These are precisely the robustness,
recurrence, and selector obstacles already isolated independently in O4.
Consequently the universal interpretation is now falsifiable: **recurrence is
the algebraic part of autonomous quantum time; outside that part, elapsed time
is irreducible circuit work.**

`[LOCAL-RESEARCH — GITHUB LEAN INFRASTRUCTURE AUDIT]` Repository search found
no existing Lean formalization of Carbery--Wright anti-concentration,
Kac--Rice component counts, quantitative analytic tube bounds, unitary circuit
varieties, or quantum fast-forwarding.  The strongest reusable candidate is
`dududuguo/HighDimProb`: Apache-2.0, no `sorry`/`admit`/`axiom` tokens in its
Lean sources, with covering/packing numbers, finite chaining and Dudley,
Hanson--Wright, scalar concentration, and matrix Bernstein.  Its Lean 4.29.1
toolchain requires a controlled port to this project's Lean 4.32.2.  It can
formalize auxiliary metric-entropy bounds after the paper proof closes, but it
does not supply `(O4.3ai)`.  `leanprover-community/physlib` is toolchain-close
and has useful quantum-information infrastructure, but relevant entropy and
fidelity files still contain unfinished declarations.  `SciSolv/weingarten-lean`
can support low-order Haar moments only.  The quantum-information, Gaussian-
Hilbert, and classical-circuit repositories audited either contain unfinished
proofs, use obsolete Lean, lack a usable licence, or formalize the wrong
circuit model.  No dependency is added before Gate 4.

A targeted second GitHub search found no Pila--Wilkie, Ax--Schanuel,
o-minimal cell decomposition, or effective Lojasiewicz library in Lean.
The only `PilaWilkie` code hit explicitly takes the terminal counting theorem
as a hypothesis; the only `OEMinimality` hit packages cell decomposition as a
field of evidence.  Neither proves infrastructure.  Therefore GitHub can
remove later Gaussian/entropy boilerplate through `HighDimProb`, but no public
Lean project currently removes the new `(O4.3aj)` research obligation.

#### Dynamical NLTS equivalence

Fix a trivial gapped parent Hamiltonian `K_0` with unique product ground state
`Phi_0` and define

\[
 K_t=e^{-itH}K_0e^{itH}.
\]

`K_t` is unitarily equivalent to `K_0`, so every eigenvalue and the gap remain
unchanged, while its unique ground state is `Phi_H(t)`.  Bounded-observable
continuity gives the unconditional implication

\[
 \|\phi-\Phi_H(t)\|\leq\varepsilon
 \Longrightarrow
 \langle\phi,K_t\phi\rangle
 \leq E_0+2\|K_t\|\varepsilon.
\]

Consequently O4 follows from a **dynamical NLTS law**: every circuit shorter
than normalized physical time has an extensive energy separation from the
ground energy of `K_t`.  This turns endpoint complexity into an extremal-energy
problem, avoiding the fatal fact that the evolved state has only typical
conserved energy under `H` itself.

The new family has the Heisenberg/Gaussian-chaos expansion

\[
 K_t=\sum_{r\geq0}{(it)^r\over r!}\,\operatorname{ad}_H^r(K_0).
\]

The required new mathematics is uniform control of this hierarchy over the
short-circuit class.  Low-depth dependency-graph methods can access the first
support-growth regime; extending the barrier to exponential circuit size must
use chaos order and circuit entropy after lightcones have saturated.
`DynamicalParentComplexityBridge.lean` now formally proves exact transported
energy covariance, the `2||K_t||` expectation Lipschitz bound, and the strict
energy-barrier certificate.  It does not assume or prove the dynamical NLTS
barrier.

#### Connected Pauli-walk reduction and its exact surviving target

The July 2026 Gaussian-process lower bound of Al-Ghattas--Gamarnik does not
extend to O4 by increasing constants.  Its ancilla-uniform circuit entropy is
controlled by backward supports of size `2^depth`; after depth `Theta(log n)`
those supports fill the system and the variance reduction disappears.  It
therefore proves a genuine shallow-depth spin-glass obstruction, not an
exponential gate-count obstruction.

A direct Wick transfer from Brownian to static disorder also fails.  For a
fixed weight-`w` Pauli word `Q`, the exact number of weight-`q` Pauli words
that anticommute with it is

\[
 N_{\rm ac}(w,q)=
 \sum_{j=0}^{\min\{w,q\}}
 {w\choose j}{n-w\choose q-j}3^{q-j}
 {3^j-(-1)^j\over2}.                                 \tag{O4.4}
\]

Indeed `j` is the support-overlap size; on the overlap the odd-parity choices
among the three nonidentity Pauli letters number
`(3^j-(-1)^j)/2`.  In particular, for two independent weight-`q` words,

\[
 \Pr(PQ=-QP)
 ={2q^2\over3n}+O_q(n^{-2}).                          \tag{O4.5}
\]

Thus two random fixed-locality terms commute with probability `1-O(1/n)`.
The non-time-local Wick pairings of one quenched Hamiltonian are not small
perturbations of Brownian pairings, so ordinary Gaussian decoupling cannot
transfer the random-circuit theorem.

The transported parent removes precisely this disconnected obstruction.
Label Pauli words by the binary symplectic space and write `omega` for its
commutation form.  For Pauli labels `p_1,...,p_r,z`,

\[
 \operatorname{ad}_{P_{p_r}}\cdots
 \operatorname{ad}_{P_{p_1}}(P_z)\ne0
 \quad\Longleftrightarrow\quad
 \omega\!\left(p_j,z+\sum_{\ell<j}p_\ell\right)=1
 \quad(1\le j\le r).                                  \tag{O4.6}
\]

When nonzero, the result is a phase times `2^r P_{z+\sum_jp_j}`.  Hence every
coefficient of `ad_H^r(K_0)` is exactly a Gaussian-chaos sum over
parity-admissible walks on the exponential Pauli commutator graph.  Commuting
disconnected words vanish before any probabilistic estimate is taken.

There is an exact source-realization theorem behind this walk language.  For
`S` in the binary symplectic label space, let `cl_omega(S)` be the least set
containing `S` and satisfying

\[
 p,q\in\operatorname{cl}_\omega(S),\quad\omega(p,q)=1
 \quad\Longrightarrow\quad
 p+q\in\operatorname{cl}_\omega(S).
\]

Then

\[
 \operatorname{Lie}_{\mathbb R}\langle iP_p:p\in S\rangle
 =
 \operatorname{span}_{\mathbb R}
 \{iP_z:z\in\operatorname{cl}_\omega(S)\}.             \tag{O4.6a}
\]

The right side contains the generators and is Lie closed because a Pauli
commutator is zero when its labels are symplectically orthogonal and is a
nonzero multiple of `iP_(p+q)` otherwise.  Conversely every closure step is
realized by that nonzero commutator.  Linear independence of distinct Pauli
words proves equality.

For the complete one- and two-local source, this closure saturates rapidly:
every nonzero weight-`w` label belongs after at most `max(0,w-2)` extension
steps.  Inductively, for `w>=3`, choose a weight-`w-1` label `x` that agrees
with the target `z` on `w-2` old sites, has a different nonzero letter on
one old site, and omits the new site.  Then `y=x+z` has weight two, and the
two different nonzero letters on the shared old site give
`omega(x,y)=1`; hence `z=x+y` is the next closure step.  Thus the full Pauli
Lie algebra is already reached at commutator depth `O(n)`.

This is the valid transfer from the source-horizon Riemann-divisor work:
faithful source realization survives, but its Boolean source lattice is
replaced by a symplectic closure lattice.  Hypertranscendence and cofinal
observer collapse do not transfer.  A finite-dimensional static evolution
already satisfies a finite constant-coefficient matrix ODE, and a short
preparation circuit is neither a label-blind observer nor an inverse
spectral decoder.  The quantitative problem is therefore the weighted
injectivity radius inside (O4.6a), not differential independence.

Spectral recurrence is the abelianized shadow of this source closure.
Permanent locality tests retain the original generator labels.  The missing
growth theorem must show that robust low-word relations do not appear in the
full noncommutative group after its Lie closure has already saturated.
Closure depth itself cannot be the complexity invariant.  The required
invariant is the robust group word metric/injectivity radius, or an
equivalent circuit-tube energy.  This is a structural relation among O4,
O5, and O6, not a proof of O4.

There is a sharp counting limit on the source-horizon analogy.  Suppose one
uses only injectivity of a one-parameter orbit, an inverse-conditioning
bound, or the existence of `N_epsilon(T)` distinguishable time cells up to
time `T`.  A finite gate alphabet with `M` choices has `M^(s+1)` words of
length at most `s`.  Such source distinguishability can therefore force at
most

\[
 s\geq\log_M N_\varepsilon(T)=O(\log T),               \tag{O4.6b}
\]

not ballistic `Omega(T/poly(n))` complexity.  A proof of O4 must use the
metric geometry of noncommutative relations inside the closure, not only
faithful recovery of the time/source coordinate.  This rules out importing
the Riemann source's cofinal conditioning theorem as a disguised
no-fast-forwarding proof.

This exposes a narrower surviving theorem than an unspecified “dynamical
NLTS” assumption:

> **Quenched connected-walk escape target.**  Prove an aggregate tube bound
> for `exp(it ad_H)K_0` against the set of conjugates of `K_0` by circuits of
> fewer than `a t/poly(n)` gates, using the parity-admissible walk expansion,
> uniformly until `t=Theta(2^n/poly(n))`.

Unweighted graph expansion or Pauli-support growth is insufficient: a
linear-depth circuit can already populate exponentially many Pauli
coefficients.  The load-bearing estimate must control the joint amplitudes
of the connected Gaussian-chaos walk against the entire low-circuit tube.
Proving only vertex delocalization, Krylov dimension, or a spectral ramp does
not close O4.

#### Exact support-adaptive memory law

The first non-Brownian connected correction can be evaluated exactly.  This
is useful both as a positive theorem and as a falsifier for indiscriminate
Brownian comparison.

Let

\[
 H=\sum_{p\in S}\sqrt{v_p}\,g_pP_p,\qquad
 g_p\mathrel{\mathop\sim}^{\rm iid}N(0,1),
\]

where `S` is any finite set of Pauli labels and `v_p >= 0`.  For a Pauli label
`z`, put

\[
 \lambda_z=\sum_{\omega(p,z)=1}v_p,\qquad
 \beta_p=\sum_{\omega(r,p)=1}v_r,\qquad
 \gamma_{z,p}=\sum_{\substack{\omega(r,p)=1\\\omega(r,z)=1}}v_r .
\]

Then the return component of the second and fourth adjoint moments is

\[
 \mathbb E\,\operatorname{ad}_H^2(P_z)=4\lambda_zP_z,                 \tag{O4.7}
\]

\[
 \mathbb E\,\operatorname{ad}_H^4(P_z)
 =\left[
 48\lambda_z^2+
 16\sum_{\omega(p,z)=1}v_p(\beta_p-3\gamma_{z,p})
 \right]P_z .                                                       \tag{O4.8}
\]

In particular,

\[
 \left\|\mathbb E\,\operatorname{ad}_H^4(P_z)
             -48\lambda_z^2P_z\right\|
 \leq 32\lambda_z\max_{\omega(p,z)=1}\beta_p .                       \tag{O4.9}
\]

**Proof.**  Write `A_p=ad_(P_p)`.  If `p` anticommutes with the current
Pauli label then `A_p` changes that label by `p`, with coefficient of modulus
two; otherwise it kills the word.  Hence
`A_p^2(P_z)=4 P_z` when `omega(p,z)=1`, and it is zero otherwise, proving
(O4.7).

For the fourth moment Wick's rule gives the three words

\[
 A_p^2A_r^2,\qquad A_pA_rA_pA_r,\qquad A_pA_r^2A_p.
\]

Fix `omega(p,z)=1`, and write
`x=omega(r,z)`, `b=omega(r,p)`.  Their respective coefficients, divided by
sixteen, are

\[
 x,\qquad x(1-b),\qquad x\mathbin{\mathsf{xor}}b.
\]

For `b=0` their sum is `3x`; for `b=1` it is one.  Summing first over `r`
therefore gives

\[
 16\sum_{\omega(p,z)=1}v_p
 \left[3(\lambda_z-\gamma_{z,p})+\beta_p\right],
\]

which is (O4.8).  Since `0 <= gamma_(z,p) <= beta_p`,
`|beta_p-3 gamma_(z,p)| <= 2 beta_p`, proving (O4.9).  No asymptotic,
independence approximation, or spectral hypothesis enters the argument.

For the uniform weight-`q` ensemble, (O4.4) makes the bound explicit:

\[
 {\max_p\beta_p\over\sum_rv_r}
 ={2q^2\over3n}+O_q(n^{-2}).
\]

If `|z|/n -> alpha` with `0 < alpha <= 1`, then

\[
 {\lambda_z\over\sum_rv_r}
 ={1-(1-4\alpha/3)^q\over2}+O_q(n^{-1}),                             \tag{O4.10}
\]

so the relative fourth-moment defect in (O4.9) is `O_(q,alpha)(1/n)`.
For a one-site seed, by contrast,
`lambda_z/sum_r v_r=2q/(3n)` and `beta_p/lambda_z -> q`; the same defect
need not vanish.  Quenched static evolution therefore does not begin as a
Brownian process.  Its first possible comparison window opens only after
operator support becomes extensive.

The crude higher-moment comparison has a `k^2/n` collision parameter: in a
Wick word with `k` paired local labels, pairwise commutation reduces the word
to scalar-Gaussian pairing, while (O4.5) bounds the chance of any
anticommuting label pair.  That estimate is not the correct renormalized
barrier, however.  Paired commutator words obey a stronger exact parity law.

Number the paired labels by `a=1,...,k`, and let their two locations in the
application-ordered word be `l_a<r_a`.  Two blocks cross when their endpoints
interlace.  Immediately before a location `j`, let `O_j` be the blocks that
have occurred exactly once.  The current Pauli label is

\[
 z+\sum_{b\in O_j}p_b.
\]

Thus the paired word is nonzero exactly when, at every occurrence of block
`a`,

\[
 \omega\left(p_a,z+\sum_{b\in O_j}p_b\right)=1.                       \tag{O4.11}
\]

Comparing the equations at `l_a` and `r_a` gives the following equivalent
criterion:

\[
 \begin{split}
 \omega(p_a,z)
  +\sum_{b:\ l_b<l_a<r_b}\omega(p_a,p_b)&=1,\\
 \sum_{b:\ a\ {\rm crosses}\ b}\omega(p_a,p_b)&=0
 \qquad\text{for every }a.                                          \tag{O4.12}
 \end{split}
\]

The equivalence is exact.  A block `b` belongs to the symmetric difference
of the open sets at the two endpoints of `a` precisely when the two chords
cross; XOR of the two endpoint equations is therefore the second line of
(O4.12), while the first line is the equation at `l_a`.

Consequently, place an edge between crossing chords `a,b` exactly when
`P_(p_a)` and `P_(p_b)` anticommute.  The second line of (O4.12) says that
this anticommutation subgraph is Eulerian: every vertex has even degree.
Every nonempty crossing-memory component must therefore contain a cycle.  In
particular, one isolated crossing anticommutation kills the Wick word rather
than contributing an error.  Nested and containing chords can change the
first-line seed parity but create no compatibility defect; they belong in a
dressed self-energy, not in the crossing-memory remainder.

The surviving coefficient has an exact topological sign.  At every admissible
step,

\[
 \operatorname{ad}_{P_p}(P_y)=2P_pP_y.
\]

After all `2k` steps, reorder equal Pauli labels until each pair is adjacent.
Two paired labels require one interchange exactly when their chords cross,
and that interchange contributes `(-1)^(omega(p_a,p_b))`.  The equal pairs
then square to the identity.  Hence every word satisfying (O4.12) equals

\[
 4^k(-1)^{\,\sum_{a<b,\ a\ {\rm crosses}\ b}
                    \omega(p_a,p_b)}P_z .                            \tag{O4.12a}
\]

The crossing-memory remainder is therefore a signed Eulerian cycle gas, not
a positive collision gas.  Its first connected polymer is a triangle and
has negative sign.

For three independent uniform weight-`q` labels, the triangle probability
has the sharp fixed-`q` leading term

\[
 \mathbb P\bigl(
 \omega(p_1,p_2)=\omega(p_2,p_3)=\omega(p_3,p_1)=1
 \bigr)
 ={2q^3\over9n^2}+O_q(n^{-3}).                                      \tag{O4.12b}
\]

To see the leading term, fix `p_1`.  With probability
`1-O_q(n^(-1))` conditional on anticommutation, `p_2` meets it at one
site.  Choose that site in `q` ways and the different letter in two ways.
For `p_3` to anticommute with both at order `n^(-1)` rather than
`n^(-2)`, it must use the same site and the unique third Pauli letter.
The remaining supports are pairwise disjoint.  The exact leading count,
conditional on `p_1`, is

\[
 2q{n-q\choose q-1}{n-2q+1\choose q-1}3^{2q-2}
\]

out of `({n\choose q}3^q)^2`; every other support-incidence pattern has at
least three independent coincidences and contributes `O_q(n^(-3))`.

There is also an exact all-orders site factorization, so the cycle gas need
not be treated as an independent-edge surrogate.  Identify the one-site
Pauli alphabet with `A=F_2^2`, write its symplectic form as
`<.,.>`, and let zero denote the identity letter.  Fix a pairing `pi` of
`1,...,2k`; write `b(j)` for the block at location `j` and
`cross_pi(a,c)` for its chord-crossing indicator.  For
`eta in F_2^(2k)` and a one-site seed letter `zeta`, define the polynomial

\[
\begin{aligned}
 \mathscr F_{\pi,\zeta,\eta}(x_1,\ldots,x_k)
 =\sum_{a_1,\ldots,a_k\in\mathbb F_2^2}
 &\prod_{r=1}^k x_r^{\mathbf1_{a_r\ne0}}\\
 {}\times(-1)^{
 &\sum_{r<c}\operatorname{cross}_\pi(r,c)\langle a_r,a_c\rangle}\\
 {}\times(-1)^{
 &\sum_{j=1}^{2k}\eta_j
 \left\langle a_{b(j)},
 \zeta+\sum_{\ell<j}a_{b(\ell)}\right\rangle}.
                                                                    \tag{O4.12c}
\end{aligned}
\]

Let `N_q=3^q {n choose q}` and sample the `k` block labels independently
and uniformly from weight-`q` Pauli words.  Define the normalized signed
survival weight (with the common amplitude `4^k` removed) by

\[
 \mathcal W_\pi(z)=
 \mathbb E\!\left[
 (-1)^{\sum_{a<c}\operatorname{cross}_\pi(a,c)\omega(p_a,p_c)}
 \mathbf1_{\text{\rm(O4.11) holds}}
 \right].
\]

Then

\[
\boxed{
 \mathcal W_\pi(z)
 ={2^{-2k}\over N_q^k}
 \sum_{\eta\in\mathbb F_2^{2k}}(-1)^{\sum_j\eta_j}
 [x_1^q\cdots x_k^q]\,
 \prod_{i=1}^n
 \mathscr F_{\pi,z_i,\eta}(x_1,\ldots,x_k).
 }                                                                  \tag{O4.12d}
\]

**Proof.**  For occurrence `j`, let `c_j` be the bit on the left of
(O4.11).  The admissibility indicator has the Walsh expansion

\[
 \prod_{j=1}^{2k}\mathbf1_{c_j=1}
 =2^{-2k}\sum_{\eta\in\mathbb F_2^{2k}}
   (-1)^{\sum_j\eta_j+\sum_j\eta_jc_j}.
\]

Both `c_j` and the crossing-sign exponent in (O4.12a) are sums of their
one-site symplectic contributions.  Their characters therefore factor over
the `n` sites.  The monomial records whether block `r` is nonidentity at
that site; extracting `x_r^q` enforces weight exactly `q` for every block.
Division by `N_q^k` normalizes the label choices.  This proves (O4.12d).

For a seed of weight `w`, simultaneous one-site Clifford symmetry identifies
all nonzero `z_i`; the product in (O4.12d) consequently has only two local
types, `n-w` zero-seed factors and `w` nonzero-seed factors.  Formula
(O4.12d) is a finite coefficient-extraction problem for every `n,q,k` and
every chord pairing.  It includes repeated labels, all site-sharing
correlations, Eulerian cancellation, and the fixed-weight constraint
exactly.  No Brownian, independent-edge, or large-`n` approximation is
present.

The target ensemble with all weights `1,...,q` requires no new diagram
argument.  If every weight-`r` label has variance `v_r`, replace each
`[x_a^q]` in (O4.12d) by
`\sum_(r=1)^q v_r[x_a^r]` and replace `N_q` by
`\sum_(r=1)^q v_r3^r{n\choose r}`.  Wick block weights are then reproduced
exactly.

Repeated block labels do not need a separate large-order estimate.  For `m`
equal-variance Pauli coefficients write the standard Gaussian vector as

\[
 J=R\Theta,\qquad R=\|J\|_2,\qquad
 \Theta\ \text{uniform on }S^{m-1},
\]

with `R` and `Theta` independent.  Since an `r`-fold nested commutator is
homogeneous of degree `r`,

\[
 \mathbb E_J\,\operatorname{ad}_{H(J)}^r(K_0)
 =
 \mathbb E R^r\,
 \mathbb E_\Theta\operatorname{ad}_{H(\Theta)}^r(K_0).               \tag{O4.12e}
\]

For even order,

\[
 \mathbb E R^{2k}
 =2^k{\Gamma(k+m/2)\over\Gamma(m/2)}
 =m(m+2)\cdots(m+2k-2).                                             \tag{O4.12f}
\]

Thus the exact energy-shell/angular moment is obtained from the Wick sum by
dividing by (O4.12f).  This removes the high-order radial repetitions
without assuming distinct Pauli labels.  Unequal variances give the same
statement after whitening the coefficient ellipsoid.  The remaining
large-order problem is the signed angular site-transfer partition function,
which is the physically relevant fixed-energy-shell object.

Radial phase mixing is not an O4 shortcut.  The theorem normalizes elapsed
time by the interaction rate, which scales with `R`; that normalization
cancels the radial variable.  Any `t^(-m)` dephasing obtained by averaging
over `R` would prove a scale-mixture statement, not the fixed-energy
autonomous law.

The response-Liouvillian corpus gives an exact bridge from these commutator
diagrams to late spectral return.  In an energy eigenbasis of `H`, define for
a Hermitian Pauli observable `Q`

\[
 I_{ab}={1\over D}|Q_{ab}|^2,\qquad
 \mu_{H,Q}=\sum_{a,b}I_{ab}\,\delta_{E_a-E_b}.
\]

Then `mu_(H,Q)` is a finite nonnegative symmetric measure and, for every
`k>=0`,

\[
\begin{aligned}
 {1\over D}\operatorname{Tr}
 \bigl(Q^\dagger\operatorname{ad}_H^{2k}(Q)\bigr)
 &=\int x^{2k}\,d\mu_{H,Q}(x)\\
 &={1\over D}\|\operatorname{ad}_H^k(Q)\|_{\rm HS}^2,                \tag{O4.12g}\\
 {1\over D}\operatorname{Tr}
 \bigl(Q^\dagger e^{itH}Qe^{-itH}\bigr)
 &=\int e^{itx}\,d\mu_{H,Q}(x).                                    \tag{O4.12h}
\end{aligned}
\]

The first identity follows entrywise from
`(ad_H Q)_(a,b)=(E_a-E_b)Q_(a,b)`; self-adjointness of `ad_H` gives the
norm square.  The second is the same diagonal action exponentiated.
`FiniteResponseLiouvillian.lean` already certifies the abstract finite
transition-measure moment identity and odd-moment cancellation; the
basis-change specialization (O4.12g)--(O4.12h) is the physical dictionary.

Therefore the site partition formula (O4.12d) computes exact ensemble
moments of a positive spectral return measure, not merely formal Taylor
coefficients.  This genuinely joins connected operator growth to recurrence.
It does not yet join either one to circuit complexity: one transition
measure contains two-point response data, while a circuit-tube event depends
on a complete replicated endpoint tensor.  The next extension must construct
and control that replica Liouvillian hierarchy.

That hierarchy has an exact aggregate reduction.  Let
`rho_t=|Phi_H(t)><Phi_H(t)|`, let `C_s` be the full size-`s` circuit class,
and put `sigma_C=C rho_0 C^dagger`.  For pure states,

\[
 F_s(t)=\sup_{C\in\mathcal C_s}\operatorname{Tr}(\rho_t\sigma_C)
       =\sup_{C\in\mathcal C_s}|\langle\Phi_H(t),C\Phi_0\rangle|^2.
\]

If trace distance from `rho_t` to some `sigma_C` is at most `epsilon`, then
`F_s(t)>=1-epsilon^2`.  Hence, for every integer `r>=1`,

\[
 \mathbb P\{C_\varepsilon(\Phi_H(t))\leq s\}
 \leq
 (1-\varepsilon^2)^{-r}\,
 \mathbb E\,F_s(t)^r,                                               \tag{O4.12i}
\]

and the moment is exactly

\[
 F_s(t)^r
 =\sup_{C\in\mathcal C_s}
 \operatorname{Tr}\!\left(
   \rho_t^{\otimes r}\sigma_C^{\otimes r}\right).                   \tag{O4.12j}
\]

No circuitwise union has been introduced: the same circuit is repeated on
all replicas and the supremum remains inside the ensemble expectation.

The replicated density evolves under the collective static Liouvillian

\[
 \mathcal L_H^{(r)}
 =\sum_{\ell=1}^r
  1^{\otimes(\ell-1)}\otimes\operatorname{ad}_H
  \otimes1^{\otimes(r-\ell)},\qquad
 \rho_t^{\otimes r}=e^{-it\mathcal L_H^{(r)}}\rho_0^{\otimes r}.     \tag{O4.12k}
\]

In the replicated energy basis its eigenvalues are the sums of gaps

\[
 \sum_{\ell=1}^r(E_{a_\ell}-E_{b_\ell}).                            \tag{O4.12l}
\]

Thus (O4.12j) is a variational matrix coefficient of a finite
self-adjoint response Liouvillian, and every one of its polynomial moments
has a positive transition-measure realization.  The generic
`FiniteResponseLiouvillian` theorem already applies after taking the
multi-index energy
`E^(r)(a_1,\ldots,a_r)=\sum_\ell E_(a_\ell)`.

The site factorization also persists exactly.  Expanding
`(L_H^(r))^k` adds a replica-leg label to every commutator occurrence.
Its commutation and endpoint constraints are still sums of one-site
symplectic bits.  Walsh expansion and the same coefficient extraction as
(O4.12d) therefore factor every replicated matrix coefficient over the
physical sites; the circuit supplies only the replicated boundary tensor
`sigma_C^(tensor r)`.

The remaining O4 estimate is now precise:

\[
 \mathbb E\sup_{C\in\mathcal C_s}
 \operatorname{Tr}\!\left(
 e^{-it\mathcal L_H^{(r)}}\rho_0^{\otimes r}
 \,\sigma_C^{\otimes r}\right)
 \leq
 (1-\varepsilon^2)^r
 \left({A tm\over\varepsilon}\right)^{-cm},                         \tag{O4.12m}
\]

for a replica order and gate budget chosen in the theorem.  Proving
(O4.12m) by a signed angular site-transfer bound would imply (O4.3)
directly and would not pay `M^s` circuit words one at a time.

The circuit supremum itself has an exact recursive form.  Pad shorter words
with the identity and define the replicated circuit body

\[
 \mathfrak K_{s,r}
 =\operatorname{conv}\{
   (C\rho_0C^\dagger)^{\otimes r}:|C|=s\}.
\]

For a Hermitian replicated operator `X`, let

\[
 h_{s,r}(X)=\sup_{Y\in\mathfrak K_{s,r}}\operatorname{Tr}(XY).
\]

If `G_n` is the finite set of allowed one-step local gates including
placements and the identity, then

\[
\begin{aligned}
 h_{0,r}(X)&=\operatorname{Tr}(X\rho_0^{\otimes r}),\\
 h_{s+1,r}(X)
 &=\max_{G\in\mathcal G_n}
   h_{s,r}\!\left((G^\dagger)^{\otimes r}
                   XG^{\otimes r}\right),                           \tag{O4.12n}\\
 F_s(t)^r&=
 h_{s,r}\!\left(e^{-it\mathcal L_H^{(r)}}
                     \rho_0^{\otimes r}\right).                     \tag{O4.12o}
\end{aligned}
\]

Equation (O4.12n) follows by removing the last gate of the word; convexifying
does not change a support function.  It is a Bellman recursion, not a union
bound.  Thus the no-shortcut theorem compares two semigroups:
continuous evolution by the collective static Liouvillian and discrete
optimal control by one local gate per Bellman step.

In the site-factorized replica expansion, one Bellman step inserts one
two-site boundary tensor on all `r` replicas.  This suggests the precise
gate-sensitive estimate that return moments lacked.  Construct a replicated
transfer norm `||.||_(r,*)` and constants `gamma,kappa>0` for which the
signed angular bulk transfer through normalized time `t` gains
`exp(-gamma r Lambda t/poly(n))`, while every local Bellman insertion costs
at most `exp(kappa r)`.  Iteration of (O4.12n) would give

\[
 \mathbb E F_s(t)^r
 \leq
 \exp\!\left(
   \kappa r s-
   {\gamma r\Lambda(H)t\over\operatorname{poly}(n)}
 \right)
 +\text{exceptional angular mass}.                                 \tag{O4.12p}
\]

With the exceptional mass bounded in the optimal form (O4.3), (O4.12p)
would prove ballistic growth for `s<a Lambda(H)t/poly(n)`.  The open
mathematical problem is now a local transfer-norm inequality compatible with
the signed Eulerian site action and the Bellman gate action.

#### Pauli cut rank: an exact gate-sensitive bulk contraction

The required transfer norm can now be constructed for each paired angular
word.  The invariant is neither support size nor the rank of the whole
crossing graph.  It is the sum, over physical sites, of binary cut ranks of
the crossing graph seen by the Pauli letters active at that site.

First consider a bipartite graph with vertex classes `L,R`, `|L|=l`,
`|R|=r`, and binary adjacency matrix `A`.  Put
`rho=rank_(F_2)(A)`.  For nonzero one-qubit Pauli labels
`x_u,y_v in F_2^2\setminus{0}`, define the normalized signed transfer

\[
 (T_{A,\alpha,\beta}f)(x)
 =3^{-r}\sum_y
 (-1)^{
   \sum_{u,v}A_{uv}\omega(x_u,y_v)+\alpha(x)+\beta(y)}
 f(y),
\]

where `alpha,beta` are arbitrary binary-valued functions.  On the uniform
`L^2` spaces of the `3^r` and `3^l` nonzero-letter assignments,

\[
 \boxed{\quad
 \|T_{A,\alpha,\beta}\|_{2\to2}
 \le {2^{\,l+r-\rho}\over 3^{(l+r)/2}} .
 \quad}                                                            \tag{O4.12q}
\]

This estimate is unconditional and uniform in every seed or boundary
character.  To prove it, first allow zero Pauli labels.  The resulting
`4^l` by `4^r` character matrix has bilinear form
`A\otimes J`, where `J` is the nonsingular one-qubit symplectic matrix.
Its binary rank is `2rho`.  Character orthogonality gives unnormalized
operator norm exactly `2^(l+r-rho)`.  Restricting rows and columns to
nonzero labels cannot increase Euclidean operator norm, and conversion to
uniform `L^2` divides by `3^((l+r)/2)`.  The functions `alpha,beta` only
multiply rows and columns by signs.  This proves (O4.12q).

For a fixed support assignment of a paired word, apply (O4.12q) at every
physical site.  If `d_i` chord labels are active at site `i`, and `rho_i`
is the cut rank of their induced crossing matrix, put

\[
 Q=\sum_i d_i,\qquad R=\sum_i\rho_i .
\]

The site-factorized angular transfer therefore obeys

\[
 \|T_{\rm angular}\|_{2\to2}
 \le {2^{Q-R}\over3^{Q/2}}
 =2^{\,(\log_2(2/\sqrt3))Q-R}.                                    \tag{O4.12r}
\]

Here this is the transfer in the selected chord variables, uniformly after
conditioning on every unselected chord label.  Edges to conditioned labels
and the seed contribute only linear forms.  Consequently the same bound
controls the full scalar coefficient of every fixed Pauli boundary branch
after averaging the conditioned labels; it is not a claim that an arbitrary
spectator-dependent boundary function has this norm.

This is the first explicit norm with the required signed bulk contraction.
It also identifies its sharp threshold:

\[
 {R\over Q}>
 \theta_*:=\log_2(2/\sqrt3)=0.207518\ldots .                        \tag{O4.12s}
\]

The threshold is genuinely below the rank density produced by a random
paired word.  Here is an exact proof.  Draw a uniform pairing of `2k`
cyclically ordered commutator positions and split the positions into two
semicircles of size `k`.  Let `b` be the number of chords with one endpoint
in each semicircle.  Order those bridge chords by their first endpoint and
put the first `l=floor(b/2)` in `L` and the remaining `r=ceil(b/2)` in `R`.
Read the `L/R` word in the order of the second endpoints.  The bridge
crossing matrix, after ordering rows and columns by the second endpoints, is
a Ferrers matrix: its `(u,v)` entry is one exactly when the `L` endpoint
precedes the `R` endpoint.  Consequently its binary rank is exactly the
number of `L`-to-`R` transitions in that word.

Now give every bridge chord an independent uniform weight-`q` support.
At site `i`, delete the chords not containing `i` from the second-endpoint
word.  The rank `rho_i` of the resulting Ferrers matrix is again exactly the
number of `L`-to-`R` transitions in the surviving word.  With
`p=q/n`, conditional on `b`,

\[
 \mathbb E\rho_i
 ={lr\over b(b-1)}
   \left(bp-1+(1-p)^b\right).                                     \tag{O4.12t}
\]

Indeed a pair of positions becomes consecutive in the retained word with
total expected count
`E[(N_i-1)_+]=bp-1+(1-p)^b`, and an ordered pair of distinct positions has
types `L,R` with probability `lr/(b(b-1))`.  Since every bridge support has
exactly `q` sites,

\[
 Q=qb,\qquad
 \mathbb ER
 =n{lr\over b(b-1)}
   \left({bq\over n}-1+(1-q/n)^b\right).                            \tag{O4.12u}
\]

In particular, if `bq/n>=64`, then `lr/(b(b-1))>=1/4` and

\[
 \mathbb ER\ge {63\over256}Q.
\]

That bare crossing estimate must still survive the nonzero-commutator
conditions; omitting them would make the result inapplicable to (O4.12d).
Use the equivalent form (O4.12): one first-occurrence constraint and one
even crossing-parity constraint per chord.  Walsh-expand the parity
constraints with bits `xi_a` and the first-occurrence constraints with bits
`eta_a`.  Across the bridge cut `L|R`, all first endpoints in `L` precede
all first endpoints in `R`, and no bridge chord has closed yet.  Hence at
site `i` the complete quadratic cut matrix is

\[
 B_i^{\xi,\eta}(u,v)
 =A_i(u,v)(1+\xi_u+\xi_v)+\eta_v,
 \qquad u\in L_i,\ v\in R_i.                                      \tag{O4.12v}
\]

The first term is the direct sum of the two Ferrers matrices induced by
the `xi=0` and `xi=1` vertices.  The second term has rank at most one.
All conditioned nonbridge labels, all within-side interactions, and the
seed contribute only row or column signs in (O4.12q).

Let `R_xi` be the sum over sites of the ranks of those two induced Ferrers
matrices before the rank-one perturbation.  Filtering a retained word by
the two independent `xi` colors gives

\[
 \mathbb E R_\xi
 =n{lr\over b(b-1)}
 \left({bq\over n}-2+
       2(1-q/(2n))^b\right).
\]

Indeed the two color subsequences have respective retention probability
`p/2`, and their total expected number of adjacent pairs is
`bp-2+2(1-p/2)^b`.  If `bq/n>=256`, then

\[
 \mathbb ER_\xi\ge {127\over512}Q,
 \qquad
 \sum_i\operatorname{rank}B_i^{\xi,\eta}
 \ge R_\xi-n
 \quad\hbox{for every }\eta .
\]

Exposing `xi`, the uniform `L/R` permutation, and the independent supports
gives a bounded-difference martingale.  Changing one `xi` bit changes
`R_xi` by at most `4q`; replacing one support changes it by at most `4q`;
transposing two positions changes it by at most `8q`.  The usual
permutation-exposure proof of bounded differences therefore gives an
absolute `c_0>0` such that

\[
 \Pr\!\left\{
   \sum_i\operatorname{rank}B_i^{\xi,\eta}
   <{15\over64}Q
   \text{ for some }\eta
   \,\middle|\, b\right\}
 \le 4e^{-c_0b}.                                                    \tag{O4.12w}
\]

No independence between physical sites is used.  A second
bounded-difference exposure of the random matching gives
`Pr{b<k/3}<=2e^{-c_1k}` for an absolute `c_1>0`.  Therefore, for
`k>=768n/q`, averaging the two exact Walsh projectors and using
(O4.12q) gives

\[
 \|\mathcal W_{\pi,\rm angular}\|_{\rm branch}
 \le
 2^{-\eta qk/3},\qquad
 \eta={15\over64}-\log_2(2/\sqrt3)>0,                              \tag{O4.12x}
\]

outside total pairing/support/Walsh mass `O(e^{-ck})`.  This is a bound on
the full admissible signed coefficient (O4.12d), conditional on a fixed
Pauli boundary branch, not merely on its bare crossing phase.

The gate tariff is equally explicit.  In the normalized Pauli basis, the
transfer matrix of a `d`-qubit unitary conjugation is real orthogonal.
Every column therefore has `l^1` norm at most
`sqrt(4^d)=2^d`.  On `r` replicas a two-qubit gate has branch variation at
most `4^r`, and `s` gates have variation at most `4^(rs)`.

For one replica, each Pauli branch changes only row or column sign functions
in (O4.12q), because commutation with a fixed boundary Pauli is a symplectic
character.  Combining with (O4.12x), the
uniform-pairing-normalized, gate-expanded signed factor satisfies

\[
 \boxed{\quad
 \text{normalized paired signed factor at order }2k
 \ \le\
 4^s\!\left(2^{-\eta qk/3}+O(e^{-ck})\right)
 \quad}                                                            \tag{O4.12y}
\]

relative to its incoming Pauli-branch norm, whenever `k>=768n/q`.
Thus paired angular order beats an arbitrary `s`-gate boundary
exponentially once

\[
 k>\max\!\left\{{6\over\eta q},{2\log 4\over c}\right\}s .
\]

This bound is uniform for each fixed circuit word.  It does not commute the
Hamiltonian-dependent circuit supremum with ensemble expectation.  Closing
that nonlinear Bellman step, rather than applying a circuitwise union bound,
is part of (O4.12z0).

The `r`-replica Pauli branch tariff `4^(rs)` is exact, but (O4.12y) must not
yet be asserted for the full replicated Wick sum.  Pairings joining
occurrences on different replica legs form multi-backbone diagrams; their
sign matrix is not the one-circle crossing matrix used above.  The estimate
tensorizes over replica-factorized pairing sectors, but cross-replica sectors
require a separate multi-backbone cut-rank theorem.  That requirement is
closed below by the ribbon-genus, forest-contraction, and fixed-weight
elimination theorems (O4.12z1)--(O4.12z10); this paragraph records why those
steps were necessary.

Logically, a replica extension is not necessary if one can directly control
the positive Bellman support function.  Set `r=1` in (O4.12i) and
(O4.12n).  If a genuinely nonlinear single-replica estimate proves

\[
 \mathbb E F_s(t)
 \le e^{\kappa s-\gamma\Lambda(H)t/\operatorname{poly}(n)}
    +\left({A tm\over\varepsilon}\right)^{-cm},                    \tag{O4.12z0}
\]

then Markov's inequality gives

\[
 \Pr\{C_\varepsilon(\Phi_H(t))\le s\}
 \le {1\over1-\varepsilon^2}\,\mathbb EF_s(t).
\]

For `s<=gamma Lambda(H)t/(2 kappa poly(n))`, the first term is
exponentially small in normalized time and is absorbed by the second after
an explicit threshold.  Thus (O4.12z0) implies (O4.3) without any
multi-backbone estimate.  Replicas may sharpen constants later; they must
not block the theorem.

But the route from the signed cut-rank coefficient bound to (O4.12z0) at
first moment is **falsified**.  For a probability space `Omega`, a vector
space `V`, a compact body `K`, and an integrable random vector `X`, signed
transfer estimates control linear functionals of `E X`, whereas the desired
quantity is

\[
 \mathbb E h_K(X)
 =\mathbb E\sup_{y\in K}\langle X,y\rangle .
\]

There is no inequality bounding the latter by cancellation in `E X`.
Already for `V=R`, `K={-1,1}`, and a symmetric Rademacher `X`,
`E X=0` while `E h_K(X)=1`.  Convexifying `K` does not change the example.
In the Hamiltonian problem the maximizing circuit is likewise allowed to
depend on `H`; a fixed-boundary signed Wick estimate cannot commute that
selector through ensemble expectation.  Therefore (O4.12q)--(O4.12y) do
not imply (O4.12z0).

The strongest positive survivor is exact: any proof using the present
signed-transfer representation must control either

1. the positive nonlinear Bellman norm `E h_(s,1)(X_H)` directly, or
2. sufficiently high replicated moments before taking the circuit
   supremum.

The second alternative makes the multi-backbone Wick topology
load-bearing, not optional.  A rare event of probability `delta_t`
contributes `delta_t` to every positive moment, not `delta_t^r`.  However,
`(O4.2a)--(O4.2c)` show that this cannot be repaired by removing a small
target-independent “recurrence mass” and then union-bounding Haar caps:
every attained shortcut target has its own local capture tube.  A successful
moment argument must therefore bound the positive nonlinear selector norm,
or equivalently the complete shortcut-centre packing, in aggregate.

#### Replica ribbon genus: the exact multi-backbone cancellation invariant

The multi-backbone object has a canonical topological representation.
This is a proved bridge, not yet the required probabilistic estimate.
Take the `2k` commutator occurrences on `r` oriented replica backbones.
Let `sigma` be the permutation whose cycles are the cyclic orders on the
nonempty backbones, and let `alpha` be the fixed-point-free involution
pairing equal Gaussian occurrences.  Thicken each backbone to a vertex disc
and each pair to an untwisted ribbon.  Write

\[
 c=\#\langle\sigma,\alpha\rangle\text{-orbits},\qquad
 f=\#\operatorname{cycles}(\sigma\alpha).
\]

The resulting orientable ribbon surface has `r` vertices, `k` edges, `c`
connected components, `f` boundary components, and total genus

\[
 \boxed{\qquad
 2g=k-r+2c-f .
 \qquad}                                                          \tag{O4.12z1}
\]

This is Euler's identity twice: the surface retracts to the ribbon graph,
so `chi=r-k`, while an orientable surface with those components has
`chi=2c-2g-f`.

The same number is exactly the rank relevant to Pauli cancellation.  At one
physical site, first allow zero letters.  A label assignment is a
`F_2^2`-valued edge 1-chain.  Returning every replica backbone to its
endpoint Pauli label imposes zero boundary at every vertex, so the allowed
assignments are

\[
 Z_1(G;\mathbb F_2)\otimes\mathbb F_2^2 .
\]

Reordering paired Pauli occurrences records the mod-two intersection
pairing of the corresponding cycles in the thickened surface.  The
intersection form on `H_1` has radical generated by the boundary curves,
with one relation per connected component.  Since

\[
\begin{aligned}
 \dim H_1(G;\mathbb F_2)&=k-r+c,\\
 \dim\operatorname{rad}&=f-c,
\end{aligned}
\]

its rank is

\[
 (k-r+c)-(f-c)=k-r+2c-f=2g.                                      \tag{O4.12z2}
\]

Equivalently, choose a spanning forest, close each remaining ribbon edge
to a cycle, and record Pauli swaps in that cycle basis.  Every swap is one
transverse intersection; changing the forest performs a congruence and
does not change rank.  Thus the quadratic Gauss cancellation of the full
alphabet depends only on replica ribbon genus, not on a chosen linear order
or a diagram drawing.

There is also an exact Gauss-sum form.  Put
`h=dim H_1(G;F_2)=k-r+c`.  After endpoint conservation, a full-alphabet
Pauli assignment is a pair of binary cycles, hence an element of
`H_1(G;F_2)\otimes F_2^2`, up to the vertex-boundary gauge already removed
by the spanning forest.  Its sign quadratic form has polar matrix equal to
the surface intersection matrix tensored with the nonsingular one-qubit
symplectic matrix.  The polar rank is therefore `4g`.  Character
orthogonality for a quadratic Gauss sum gives, for every added linear
boundary character,

\[
 \left|
 4^{-h}\!\!
 \sum_{a\in H_1(G;\mathbb F_2)\otimes\mathbb F_2^2}
 (-1)^{q_\Sigma(a)+\ell(a)}
 \right|
 \in\{0,\,2^{-2g}\}.                                               \tag{O4.12z2a}
\]

The value is zero exactly when the linear character is incompatible with
the radical; otherwise its magnitude is `2^(-2g)`.  Thus every replica
handle costs exactly a factor `1/4` before the nonzero-letter restriction,
and every direction not cancelled by handle genus lies in the boundary
radical.

Random multi-backbone topology is already controllable.  Assume every
backbone contains at least two occurrences, so `sigma` has no fixed point,
and let `alpha` be a uniform fixed-point-free involution on `2k` symbols.
Loth and Rattan's conjugacy-class product theorem gives

\[
 \mathbb E f
 =\mathbb E\,\#\operatorname{cycles}(\sigma\alpha)
 \le H_{2k}+1.                                                     \tag{O4.12z2b}
\]

This is a literature input, not our novelty
([Loth--Rattan, arXiv:2310.06659](https://arxiv.org/abs/2310.06659)).
Their theorem applies because the law of `sigma alpha` depends only on the
fixed-point-free conjugacy types of `sigma` and `alpha`.

The required exponential tail follows elementarily.  Switching two matched
edges of `alpha` changes `sigma alpha` by a permutation supported on at most
four symbols and changes its number of cycles by at most two.  Generate the
uniform matching from a uniform random permutation paired in consecutive
positions and expose that permutation.  The bounded-difference inequality
for random permutations therefore gives, with a deliberately nonoptimal
constant,

\[
 \Pr\{f-\mathbb Ef\ge u\}
 \le \exp\!\left(-{u^2\over64k}\right).                            \tag{O4.12z2c}
\]

For `k>=256`, `H_(2k)+1<=k/16`; taking `u=k/16` shows
`f<=k/8` outside `e^(-k/16384)`.  If also `k>=8r`, Euler's law then gives

\[
 2g=k-r+2c-f\ge {3k\over4},
\]

and the exact full-alphabet Gauss factor (O4.12z2a) is at most
`2^(-3k/4)` on that event.  Thus the random replica topology itself is not
the open problem: it creates extensive genus with an exponential tail.
Backbones of occurrence count zero are omitted; singleton backbones form a
separate occupancy event and cost at most one incident ribbon each when
passing to the replica-incidence 2-core.

For one backbone, (O4.12z2) reduces to the familiar rank of the chord
interlacement matrix.  For several replicas it supplies the missing
coordinate-free replacement: tree-like replica connections have genus zero
and cannot cancel, while every handle contributes two independent binary
intersection directions.  The boundary radical `f-c` is the precise
topological carrier of the replica-collision memory that survives signed
bulk cancellation.

`[FALSIFIED — FIRST REPLICA GENUS TRANSPORT LAW.]`  The first formulation
asserted that, in the fixed-`q` angular
Pauli ensemble, after the exact nonzero-letter and first-commutator
projections, a replicated Wick ribbon graph with `k` pairs on `r`
nonempty backbones and `kq >= Cnr` retains site-summed effective
intersection rank

\[
 R_{\rm eff}\ge
 \left(\log_2(2/\sqrt3)+\delta_q\right)(qk-C_qnr)
                                                                    \tag{O4.12z3}
\]

outside mass `e^{-c_q(k-C_qr)}`, uniformly in every Walsh field and circuit
boundary tensor.  The complementary genus-zero/boundary-radical sector
admits a positive decomposition whose total spherical-time contribution is
the common recurrence mass, paid once rather than once per circuit word or
replica.

The recurrence identification is false.  Already for one backbone,
noncrossing pairings have genus zero but carry the order-one Catalan
self-energy governed by (O4.13); they describe ordinary bulk propagation,
not rare recurrence.  Boundary radical likewise records degeneracy of the
intersection form, not by itself a late-time spectral return.  The corrected
scale loss in (O4.12z3) is `O(nr)`, because an admissibility perturbation may
lose `O(r)` rank at each of `n` sites, rather than `O(qr)`.

The positive survivor is (O4.12z1)--(O4.12z2): replica genus is exactly the
signed cancellation rank, while the radical classifies the directions that
need a separate resummation.  Based on what killed the first statement, the
stronger active conjecture is:

The one-boundary planar resummation is already exact at operator level.
Write `A_p=ad_(P_p)` on the finite Hilbert--Schmidt operator space and define
the covariance map

\[
 \boldsymbol\eta(X)=\sum_p v_p A_pXA_p .
\]

Let `M_(2k)^(0)` be the sum of all noncrossing Wick words of length `2k`,
with `M_0^(0)=I` and odd moments zero.  Rooting at the partner of the first
occurrence gives the dependency-closed recursion

\[
 M_{2k}^{(0)}
 =\sum_{j=0}^{k-1}
   \boldsymbol\eta(M_{2j}^{(0)})
   M_{2(k-1-j)}^{(0)}.                                             \tag{O4.12z4}
\]

Indeed the rooted label `p` surrounds the `2j` occurrences inside its
chord, producing `A_p M_(2j)^(0) A_p`, and the remaining word follows on
the right.  Therefore the formal operator-valued Cauchy series

\[
 \mathbf G(z)
 =\sum_{k\ge0}M_{2k}^{(0)}z^{-2k-1}
\]

satisfies

\[
 z\mathbf G(z)
 =I+\boldsymbol\eta(\mathbf G(z))\mathbf G(z),\qquad
 \mathbf G(z)
 =\left(zI-\boldsymbol\eta(\mathbf G(z))\right)^{-1}               \tag{O4.12z5}
\]

whenever the formal inverse is interpreted coefficientwise (and
analytically wherever it exists).  Equation (O4.13) below is the diagonal
Pauli-coordinate shadow of (O4.12z4).  Thus the active conjecture does not
need to invent a planar reference; it must extend this exact Dyson object to
several boundary components and prove compatibility with the Bellman
support norm.

That first extension is combinatorial and can be closed exactly.  It is
useful to retain connected components and genus rather than immediately
summing them away.  Let
`\mathfrak C_(g,r)(C_1,\ldots,C_r)` be the formal sum of connected Wick
ribbon pairings of total genus `g` on `r` nonempty cyclic backbones
`C_1,\ldots,C_r`, with one half-edge `a` of `C_1` marked.  Coefficients may
take values in any tensor category in which disjoint union is a tensor
product and a paired edge is evaluated by the covariance contraction

\[
 \mathcal E_{a,b}
 =\sum_p v_p\,\mathcal A_p^{(a)}\mathcal A_p^{(b)} .
\]

For the admissible Pauli expansion, the object carried by a cut boundary
also records its exposed Pauli seed and Walsh projector bits.  With that
state retained, (O4.12d) supplies precisely such a local edge-contraction
weight; forgetting the state before gluing would be invalid.

Pair `a` with a half-edge `b`.  If `b` lies on a different backbone `C_j`,
contracting the ribbon joins the two cyclic words in the unique
orientation-preserving order, denoted `C_1#_(a,b)C_j`, and preserves genus.
If `b` lies on `C_1`, cut the cyclic word at `a,b` into the two cyclic words
`U_b,V_b`.  The root ribbon is either separating, in which case the other
backbones split into a subset `S` and its complement and the two genera add
to `g`, or nonseparating, in which case cutting it leaves one connected
surface of genus `g-1` with the two new backbones `U_b,V_b`.  Consequently
the connected Wick sums obey the exact rooted join--split identity

\[
\boxed{\begin{aligned}
 \mathfrak C_{g,r}(\mathbf C)
 ={}&
 \sum_{\substack{b\in C_j\\j>1}}
 \mathcal E_{a,b}\,
 \mathfrak C_{g,r-1}
 \bigl(C_1\#_{a,b}C_j,\mathbf C_{\widehat{1,j}}\bigr)\\
 &+\sum_{b\in C_1\setminus\{a\}}\mathcal E_{a,b}
 \Bigg[
 \sum_{\substack{S\subseteq\{2,\ldots,r\}\\g_1+g_2=g}}
 \mathfrak C_{g_1,1+|S|}(U_b,\mathbf C_S)
 \otimes
 \mathfrak C_{g_2,r-|S|}(V_b,\mathbf C_{S^c})\\
 &\hspace{50mm}
 +\mathbf1_{g\ge1}\,
 \mathfrak C_{g-1,r+1}(U_b,V_b,\mathbf C_{\widehat1})
 \Bigg].
\end{aligned}}                                                   \tag{O4.12z6}
\]

Empty arcs use the tensor unit, and unstable empty connected factors are
omitted.  The full, not necessarily connected, Wick sum is recovered by
the ordinary set-partition formula over backbone labels.

**Proof.**  The partner `b` of the marked half-edge is unique.  A ribbon
between distinct vertex discs may be contracted; this decreases both
vertices and edges by one and changes neither component count, faces, nor
genus.  A ribbon whose ends lie on the marked disc becomes, after capping
the boundary curves, a simple closed curve.  On an orientable surface it is
either separating or nonseparating.  In the separating case its two sides
determine `S` uniquely and restriction gives the displayed tensor product.
In the nonseparating case cutting along it raises Euler characteristic by
two and therefore lowers genus by one.  These operations are reversible by
gluing the root ribbon, so the cases are disjoint and exhaustive.  Edge
labels and the carried boundary state are contracted only when the ribbon
is glued, hence the same bijection is weight preserving.

At `g=0,r=1` only the separating line survives and gives (O4.12z4).
At `g=0,r>1`, (O4.12z6) is the required multi-backbone planar
Schwinger--Dyson hierarchy.  At positive genus it says something sharper
than the polymer language above: every handle is created by an explicit
nonseparating self-gluing operation.  Thus multi-boundary planar
resummation itself is no longer conjectural.  The still-open step is
analytic: prove that the solution of this hierarchy, with its exposed
boundary states, is bounded in a norm stable under the Bellman maximum.

There is no need to conjecture the algebraic part of that norm.  For an
`r`-replica Hermitian tensor define the absolute Bellman crossnorm

\[
 \|X\|^\sharp_{s,r}
 =\sup_{C\in\mathcal C_s}
   \left|\operatorname{Tr}\!\left(
      X(C\rho_0C^\dagger)^{\otimes r}\right)\right|.
\]

It has the two exact properties needed by the join--split hierarchy:

\[
\begin{aligned}
 \|X\otimes Z\|^\sharp_{s,r_1+r_2}
 &\le \|X\|^\sharp_{s,r_1}\|Z\|^\sharp_{s,r_2},\\
 \|X\|^\sharp_{s+1,r}
 &=\max_{G\in\mathcal G_n}
   \left\|(G^\dagger)^{\otimes r}XG^{\otimes r}
   \right\|^\sharp_{s,r}.                                         \tag{O4.12z7}
\end{aligned}
\]

The first line follows because evaluation of a tensor product on the same
replicated circuit target factors, and the supremum of a product is at most
the product of the two suprema.  The second is the absolute version of
(O4.12n).  Triangle inequality is immediate, so `\|\cdot\|^\sharp` is a
seminorm (a norm after quotienting the annihilator of the circuit body).
Therefore every separating term of (O4.12z6) is submultiplicative and every
Bellman insertion is represented exactly, without selecting a circuit
before ensemble averaging.  What remains is quantitative rather than
foundational: establish a strict normalized contraction for the joined
cavity and handle operators in this crossnorm.

Replica topology can also be reduced exactly to the already understood
one-backbone geometry.  Let a connected ribbon graph have `r` backbone
vertices and `k` paired ribbons, and choose a spanning tree `T` of its
backbone-incidence multigraph.  Contracting the `r-1` ribbons in `T` merges
the vertex discs into one disc.  The result is a one-vertex chord diagram
with

\[
 K=k-r+1
\]

chords, the same boundary curves, and the same genus.  Its chord
interlacement form is the surface intersection form in the fundamental
cycle basis determined by `T`.  This is not merely a rank comparison: it is
a congruent matrix presentation of the same form.

The reduction is compatible with the random matching before the
fixed-weight coefficient extraction.  Fix `T` as a set of `r-1` disjoint
pairs of occurrence positions.  Conditional on `T` being contained in a
uniform matching of `2k` positions, the residual pairs form a uniform
matching of the remaining `2K` positions.  After contracting `T`, they are
therefore an ordinary uniform one-backbone chord diagram.  If backbone `j`
has `d_j` occurrences, the number of possible occurrence-level spanning
trees is at most

\[
 (2k)^{r-2}\prod_{j=1}^r d_j,
\]

by the weighted Cayley identity
`\sum_T\prod_j d_j^{\deg_T(j)}
=(\sum_jd_j)^{r-2}\prod_jd_j`; choices reusing one occurrence only make
this an overcount.  A specified set of tree pairs occurs in a uniform
matching with probability
`\prod_{\ell=0}^{r-2}(2k-(2\ell+1))^{-1}`.  Hence its total marked mass in
the normalized pairing average is at most

\[
 {\displaystyle(2k)^{r-2}\prod_jd_j\over
  \displaystyle\prod_{\ell=0}^{r-2}(2k-(2\ell+1))}
 \le {1\over4k}\left({4k\over r}\right)^r
 \quad (r\le k/2),                                                 \tag{O4.12z8}
\]

where the last inequality uses
`\prod_jd_j\le(2k/r)^r` and bounds every denominator factor below by
`k`.  Thus marking a contraction tree has explicit
`O(r\log(k/r))` entropy when `k/r` is bounded below, rather than an
uncontrolled replica-diagram entropy.

There is an exact rank statement for the boundary constraints introduced
when the tree variables are removed.  At one site and for one binary
coordinate, write the polar matrix of a quadratic Walsh phase, with the
tree variable first, as

\[
 \begin{pmatrix}0&u^\mathsf T\\u&B\end{pmatrix}.
\]

An affine vertex-conservation equation has the form
`x_0=c+\ell^\mathsf Tx`.  Substitution changes the residual polar matrix
from `B` to

\[
 B+u\ell^\mathsf T+\ell u^\mathsf T,
\]

a perturbation of rank at most two.  Eliminating the two binary Pauli
coordinates of every tree ribbon therefore loses at most four binary polar
directions per contracted ribbon and site.  For `c` connected components,
forest contraction costs at most

\[
 4n(r-c)                                                        \tag{O4.12z9}
\]

in the site-summed binary polar rank.  This proves the previously asserted
`O(nr)` scale at the quadratic-form level and explains it: it is the exact
cost of solving replica-tree flow, not a genus defect.

The apparent fixed-weight obstruction can also be closed.  Let `\mu_q` be
uniform probability measure on weight-`q` Pauli words in
`A^n=(\mathbb F_2^2)^n`.  Solving one tree-flow equation replaces its
independent tree label by an affine function `Lx+c` of the residual cycle
labels and inserts the exact density `\mu_q(Lx+c)`.  Fourier inversion gives

\[
 \mu_q(Lx+c)
 =4^{-n}\sum_{\chi\in\widehat{A^n}}
   \widehat\mu_q(\chi)\chi(c)\chi(Lx),
 \qquad |\widehat\mu_q(\chi)|\le1.
\]

The total absolute coefficient of this expansion is at most one.  Products
of solved tree-label densities retain that bound.  Thus exact weight `q`
does not introduce an exponential coefficient-extraction loss at all; it
only averages the residual transfer over additional linear characters,
against which (O4.12w) is uniform.

The quadratic perturbation (O4.12z9) has a separate explicit cost.  A
binary quadratic phase whose polar perturbation has rank `R` is, after a
linear change of variables, a function of at most `R` essential coordinates
times one linear character.  Fourier expanding those coordinates has total
absolute coefficient at most `2^R`.  Combining this observation with
(O4.12z8)--(O4.12z9) and the one-backbone bound (O4.12x) proves the
following connected-sector transfer theorem.  Put `K=k-r+1`, assume
`r\le k/2` and `K\ge768n/q`, and retain arbitrary affine replica-boundary
data and all commutator Walsh projectors.  Then the normalized paired
angular contribution of the connected `r`-backbone sector, after an
arbitrary `s`-gate boundary, is at most

\[
\boxed{
 {1\over4k}\left({4k\over r}\right)^r
 2^{\,4n(r-1)}4^{rs}
 \left(2^{-\eta qK/3}+O(e^{-cK})\right),
 \qquad
 \eta={15\over64}-\log_2(2/\sqrt3)>0 .
}                                                                  \tag{O4.12z10}
\]

Indeed mark and condition on a spanning tree, contract it, solve its
sitewise flow variables, Fourier-expand their exact weight densities and
the rank-`4n(r-1)` perturbation, and then apply (O4.12x) to the resulting
uniform residual one-circle matching.  Summing the marked-tree overcount
gives (O4.12z8); the circuit boundary gives `4^(rs)`.  Every step is an
inequality in absolute value, so multiple possible spanning trees only
overcount and cannot invalidate the estimate.

Thus the fixed-weight forest-elimination conjecture is proved, with explicit
constants.  In particular the normalized paired factor beats the replica
and circuit boundary tariffs at that fixed order whenever

\[
 \min\!\left\{{\eta q\over3},{c\over\log 2}\right\}(k-r+1)
 >
 4n(r-1)+2rs
 +r\log_2(4k/r)+O(1),
                                                                    \tag{O4.12z11}
\]

where the absolute `O(1)` absorbs the constant in the exceptional matching
term.  Topology, cross-replica pairing, fixed Pauli weight, and the circuit
selector tariff are therefore no longer separate open problems at the
normalized-pairing level.  This does not yet bound the physical series:
restoring the pairing multiplicity (O4.12z) can amplify the exceptional
low-interlacement sector.  Its leading contribution is precisely the planar
cavity governed by (O4.12z6), and it must be resummed before applying
(O4.12z10).

The planar cavity has an exact norm-stable real-time realization.  This
closes item 3 below for one boundary, and for the collective replica
Liouvillian before resolving it into separate backbone boundaries.  Let
`\mathcal V_r` be the `r`-replica Hilbert--Schmidt operator space and put

\[
 A_p^{(r)}
 =\sum_{\ell=1}^r
  I^{\otimes(\ell-1)}\otimes\operatorname{ad}_{P_p}
  \otimes I^{\otimes(r-\ell)} .
\]

On the full Fock space
`\mathcal F(\mathbb C^m)\otimes\mathcal V_r`, with left creation operators
`\ell_p` and vacuum `\Omega`, define the bounded self-adjoint operator

\[
 S_r=\sum_p\sqrt{v_p}\,
  (\ell_p+\ell_p^\dagger)\otimes A_p^{(r)} .
\]

Vacuum compression `E_\Omega` is unital completely positive.  The relations
`\ell_p^\dagger\ell_q=\delta_{pq}I` show by the usual stack reduction,
without an asymptotic limit, that

\[
 E_\Omega(S_r^{2k})=M_{2k,r}^{(0)},\qquad
 E_\Omega(S_r^{2k+1})=0,
\]

where `M_(2k,r)^(0)` is the exact sum of globally noncrossing Wick pairings
for the collective replicated covariance

\[
 \boldsymbol\eta_r(X)=\sum_pv_pA_p^{(r)}XA_p^{(r)} .
\]

Consequently the planar real-time series converges in operator norm for
every real `t` and equals

\[
 U_{0,r}(t)
 =\sum_{k\ge0}{(-1)^kt^{2k}\over(2k)!}M_{2k,r}^{(0)}
 =E_\Omega(e^{-itS_r}),\qquad
 \boxed{\ \|U_{0,r}(t)\|_{\rm op}\le1\ }.                           \tag{O4.12z12}
\]

Self-adjointness uses self-adjointness of every Pauli commutator on
Hilbert--Schmidt space; contractivity follows because vacuum compression is
unital completely positive and `e^(-itS_r)` is unitary.  Also
`\|S_r\|\le2\|\boldsymbol\eta_r(I)\|^{1/2}`, so no formal-series radius is
being hidden.  Applying `U_(0,r)(t)` to a unit Hilbert--Schmidt endpoint and
testing against a pure replicated circuit target gives absolute overlap at
most one, uniformly in `s,r,t`.

This theorem prevents the Catalan multiplicity from blowing up after time
resummation.  It does not yet assert decay: a completely positive
contraction may have an invariant subspace.  Nor does the single collective
ordering by itself sum every annular/multi-boundary planar component in
(O4.12z6).  The remaining planar question is now spectral and explicit:
classify the fixed space of the cavity channel and prove decay on the
traceless Bellman-visible quotient, while solving the cross-boundary join
terms of (O4.12z6).

The fixed space can be classified exactly, and it is larger than the scalar
sector for replicas.  For every `r`,

\[
 \boxed{
 \{v:U_{0,r}(t)v=v\ {\rm for\ all}\ t\}
 =\bigcap_p\ker A_p^{(r)} .
 }                                                                  \tag{O4.12z13}
\]

One inclusion is immediate because `S_r(\Omega\otimes v)=0` on the common
kernel.  Conversely, differentiating `U_(0,r)(t)v=v` twice at zero gives

\[
 0=M_{2,r}^{(0)}v
   =\left(\sum_pv_p(A_p^{(r)})^2\right)v .
\]

Taking the Hilbert--Schmidt inner product with `v` yields
`\sum_pv_p\|A_p^{(r)}v\|^2=0`, hence every summand vanishes.

Suppose now that the Hamiltonian Pauli family generates the full unitary Lie
algebra on the physical Hilbert space under linear combinations and
commutators.  Under
`\mathcal V_r\cong\operatorname{HS}(\mathcal H^{\otimes r})`,
`A_p^(r)` is the infinitesimal diagonal-conjugation action.  Its common
kernel is therefore the commutant of `U^{\otimes r}` for all physical
unitaries `U`.  Schur--Weyl duality gives

\[
 \bigcap_p\ker A_p^{(r)}
 =\operatorname{span}\{W_\pi:\pi\in S_r\}
 \quad (\dim\mathcal H\ge r),                                      \tag{O4.12z14}
\]

where `W_\pi` permutes replica tensor factors.  In particular the
one-replica fixed space is exactly the scalar identity, but the replicated
fixed space contains the whole permutation algebra.

This corrects the target quotient.  “Traceless” is sufficient only at
`r=1`; high-moment decay must be proved modulo the replica-permutation
algebra.  These modes are not a recurrence remainder.  They are universal
purity moments:
`\operatorname{Tr}(W_\pi\sigma^{\otimes r})
=\prod_{c\in\operatorname{cycles}(\pi)}\operatorname{Tr}(\sigma^{|c|})`,
which equals one for every pure circuit target.  They can therefore be
subtracted as a target-independent baseline before the Bellman maximum.
The genuinely selector-sensitive planar problem lives on the orthogonal
complement of (O4.12z14).

`[LITERATURE BOUNDARY.]`  Operator-valued semicircular realization and the
Dyson equation are standard; see Helton--Rashidi Far--Speicher,
[arXiv:math/0703510](https://arxiv.org/abs/math/0703510).  General matrix
Dyson-equation regularity theorems give absolutely continuous densities only
under additional flatness/primitivity assumptions; see Alt--Erdos--Krueger,
[arXiv:1804.07752](https://arxiv.org/abs/1804.07752).  Such assumptions
cannot be quoted here without proof because (O4.12z14) makes the replicated
covariance nonfaithful on the full space.  Matrix-valued semicircular laws
can in fact have atoms for degenerate covariance
([Soltanifar, arXiv:1109.4973](https://arxiv.org/abs/1109.4973)).
Therefore atom-free decay on the permutation quotient is a genuine
model-specific frontier; (O4.12z13) alone does not establish it.

There is nevertheless an unconditional quantitative consequence.  Let
`Q_r` be Hilbert--Schmidt projection onto the orthogonal complement of the
permutation algebra and define the replica Casimir gap

\[
 \lambda_r
 =\lambda_{\min}^{+}\!\left(
   \sum_pv_p(A_p^{(r)})^2\right)>0,\qquad
 R_r=\|S_r\|.
\]

Positivity of `\lambda_r` follows from (O4.12z13)--(O4.12z14) and finite
dimension.  Hence

\[
 \sum_pv_p(A_p^{(r)})^2\ge\lambda_rQ_r .                           \tag{O4.12z15}
\]

For one replica this gap is explicit in the Pauli basis:

\[
 \lambda_1
 =4\min_{z\ne0}\sum_{\omega(p,z)=1}v_p .
\]

If all weight-one Pauli directions occur with variance at least `v_min`,
then `\lambda_1\ge8v_min`, because a nonidentity Pauli word anticommutes
with two one-site letters at any site in its support.

The gap gives a strict, fully controlled short-time cavity contraction.
Odd vacuum moments vanish, so

\[
 U_{0,r}(t)
 =I-\frac{t^2}{2}\sum_pv_p(A_p^{(r)})^2+\mathcal R_4(t),\qquad
 \|\mathcal R_4(t)\|
 \le{(R_r|t|)^4\cosh(R_r|t|)\over24}.
\]

Since `U_(0,r)(t)` is self-adjoint, fixes the permutation algebra, and is a
contraction, (O4.12z15) implies

\[
 \boxed{\quad
 \|Q_rU_{0,r}(t)Q_r\|
 \le1-{\lambda_rt^2\over4}
 \quad}                                                            \tag{O4.12z16}
\]

whenever

\[
 R_r|t|\le\tfrac12,\qquad
 t^2\le {6\lambda_r\over R_r^4\cosh(1/2)} .
\]

The first condition also keeps the spectrum of `U_(0,r)(t)` positive, so
the displayed upper spectral bound is an operator-norm bound.  This proves
genuine loss of every selector-sensitive planar mode at the first
interaction timescale.  It does not prove long-time decay because vacuum
compression is not a semigroup; iterating (O4.12z16) would silently replace
the static Hamiltonian by fresh noise.

`[BRIDGE] [PAPER-PROVED, EXTERNAL MATRIX-SEMICIRCLE INPUT.]`  At one replica,
the long-time planar problem can now be closed exactly for every bounded-
weight Pauli ensemble having a common positive variance `v_1` on its
weight-one words.  Let `V_0` be the traceless Hilbert--Schmidt operator space
and decompose it by exact nonempty Pauli support,

\[
                    V_0=\bigoplus_{\varnothing\ne T\subseteq[n]}V_T.
                                                               \tag{O4.12z17}
\]

Every one-site commutator `A_p=ad_(P_p)` preserves each `V_T`.  On a Pauli
word supported on `T`, exactly two one-site letters anticommute at every site
of `T`, and every nonzero squared commutator contributes four.  Hence

\[
 \sum_{\operatorname{wt}(p)=1}A_p^2\big|_{V_T}
 =8|T|I_{V_T}.                                          \tag{O4.12z18}
\]

For the weight-one covariance
`eta_1(X)=v_1 sum_(wt(p)=1) A_p X A_p`, put

\[
 C\big|_{V_T}=(8v_1|T|)^{-1/2}I_{V_T}.
\]

Equation `(O4.12z18)` gives the exact symmetric operator-scaling equation

\[
                         \eta_1(C)=C^{-1}.             \tag{O4.12z19}
\]

`[BRIDGE] [PAPER-PROVED.]`  The scaling mechanism extends to every replica
order on the complement of the sitewise singlet algebra.  For collective
one-site commutators `A_(i,a)^(r)`, put

\[
 \mathcal S_r=\bigcap_{i,a}\ker A_{i,a}^{(r)},\qquad
 W_r=\mathcal S_r^\perp,\qquad
 K_{1,r}=\sum_{i,a}(A_{i,a}^{(r)})^2.                 \tag{O4.12z19a}
\]

The local `su(2)` relations imply
`[K_(1,r),A_(i,a)^(r)]=0`.  On `W_r`, `K_(1,r)` is positive definite, so
`R_r=(K_(1,r)|_(W_r))^(-1/2)` exists and the self-adjoint scaled family
`B_(i,a)^(r)=R_r A_(i,a)^(r)` obeys

\[
             \sum_{i,a}(B_{i,a}^{(r)})^*B_{i,a}^{(r)}
 =\sum_{i,a}B_{i,a}^{(r)}(B_{i,a}^{(r)})^*=I_{W_r}.  \tag{O4.12z19b}
\]

Parseval--Bessel therefore gives, for every `U <= W_r`,

\[
 \dim\operatorname{span}\{A_{i,a}^{(r)}U:i,a\}
 \ge\dim U.                                           \tag{O4.12z19c}
\]

Thus growing-replica Hall expansion is already exact away from the sitewise
singlets.  The remaining algebraic frontier is confined to the action of
weight-two generators on `S_r` and its gluing with `(O4.12z19c)` for
arbitrary mixed subspaces.  The dependency-closed proof is in
`../3-formalized/all-replica-local-casimir-hall-expansion.md`.
The representation-independent implication “Hermitian family with central
Casimir and trivial common kernel implies Hall expansion for every subspace”
is now formalized over both `R` and `C` as
`centralHermitianMatrixFamily_subspace_finrank_of_commonKernel` in
`HTGeometry/CentralCasimirHallExpansion.lean`.  Centrality from antisymmetric
commutator structure constants is formalized as
`quadraticCasimir_commutes_of_antisymmetric_structure`.  Exact
collective-Pauli bracket and sitewise-singlet kernel instantiation remain
before `(O4.12z19c)` itself is Lean-complete.

The scaled covariance is therefore unital and trace-preserving.  Such a
completely positive map is rank non-decreasing: for a support projection
`P`, its image is bounded above by the identity and has trace `rank(P)`, so
its rank is at least `rank(P)`.  Invertible scaling preserves rank
non-decrease.  Adding the higher-weight positive covariance cannot reduce
the support of the image of any positive matrix.  Thus the complete
one-replica commutator pencil is full.

Kargin's 2026 algebraic matrix-semicircle theorem then applies: a full finite
matrix semicircle has purely absolutely continuous scalar spectral law, with
only finitely many algebraic density singularities and no singular-continuous
part.  Faithfulness of the matrix/free trace makes every vector spectral
measure absolutely continuous.  Riemann--Lebesgue and finite dimensionality
therefore give

\[
 \boxed{\qquad
       \|Q_1U_{0,1}(t)Q_1\|_{\rm op}\longrightarrow0
       \quad(|t|\to\infty).
 \qquad}                                                \tag{O4.12z20}
\]

This is the first all-long-time cavity contraction in the route; `(O4.12z16)`
was only local in time.  It is not yet circuit anti-concentration.

`[PROVED]` At two replicas the local-singlet synchronization part closes
exactly in the literal arbitrary-register physical matrix algebra. On one
physical site put

\[
 u={I\otimes I\over2},\qquad
 z={1\over2\sqrt3}\sum_{a=1}^3\sigma_a\otimes\sigma_a,
 \qquad f={u+\sqrt3z\over2}={F\over2}.               \tag{O4.12z21}
\]

Then `u,z` are an orthonormal basis of the local diagonal-`SU(2)` invariant
space and `f` is normalized replica swap.  For an interaction edge `{i,j}`
let

\[
 K_{ij}=\sum_{a,b=1}^3
 \operatorname{ad}_{\sigma_a^{(i)}\sigma_b^{(j)},\,\mathrm{coll}}^2.
\]

On the ordered invariant basis `uu,uz,zu,zz`, direct Pauli reduction gives

\[
 K_{ij}=
 \begin{pmatrix}
 0&0&0&0\\
 0&48&0&-16\sqrt3\\
 0&0&48&-16\sqrt3\\
 0&-16\sqrt3&-16\sqrt3&32
 \end{pmatrix},
 \quad
 \operatorname{Spec}K_{ij}=\{0,0,48,80\},             \tag{O4.12z22}
\]

and

\[
                  \ker K_{ij}=\operatorname{span}\{u_iu_j,f_if_j\}.
                                                               \tag{O4.12z23}
\]

For any connected interaction graph, exact tensor extension of the nine
physical edge commutator squares and an invertible local change of basis
`|0> -> u`, `|1> -> f` give

\[
 \boxed{\quad
 \ker\sum_{\{i,j\}}K_{ij}
 =\operatorname{span}\{u^{\otimes n},f^{\otimes n}\}.
 \quad}                                                        \tag{O4.12z24}
\]

The global identity/swap embedding has an explicit Möbius left inverse, so no
coefficient-surrogate assumption is present. Each edge generator is a Pauli
string of weight exactly two, and the literal physical edge Casimir
intertwines exactly with the displayed four-coordinate action. Every edge
kills all bit strings whose endpoint labels agree and is injective on the two
mismatch coordinates; connectedness leaves only the two constant strings.
Thus the entire `2^n`-dimensional one-site singlet algebra synchronizes to the
identity and global-swap modes. The dependency-closed proof is
`HTGeometry/TwoReplicaGlobalSingletEdgeCasimirBridge.lean`; capstone axiom
audits contain only `propext`, `Classical.choice` and `Quot.sound`.

This does **not** make the matrix pencil full.  The implication “positive
Casimir with correct common kernel implies rank non-decrease” is false: the
Hermitian matrices `E_13+E_31` and `E_23+E_32` have positive Casimir
`diag(1,1,2)` and zero common kernel, yet send the plane
`span{e_1,e_2}` into the line `span{e_3}`.  The exact remaining algebraic
gate is consequently the stronger Pauli Hall-expansion law

\[
 \dim\operatorname{span}\{A_p^{(2)}U:\operatorname{wt}(p)\le2\}
 \ge\dim U                                                   \tag{O4.12z25}
\]

for every subspace `U` of the global-permutation quotient.  This is precisely
the rank-nondecreasing condition; common-kernel or spectral-gap arguments do
not substitute for it. The dependency-closed synchronization proof is now
global and literal; the hostile counterexample remains decisive because
synchronization proves quadratic recovery, not the all-subspaces Hall law.

`[BRIDGE] [PAPER-PROVED.]`  The full Hall quantifier can now be closed on
the entire two-replica sitewise singlet quotient, not merely on coordinate
vectors.  Fix one Pauli orientation `(a,b)` and, for every graph edge `e`,
retain only `A_(e,ab)^(2)`.  In the local identity/swap basis its exact
single-commutator action is

\[
\begin{array}{rcl}
 A_{e,ab}(I\otimes I)&=&A_{e,ab}(F\otimes F)=0,\\
 A_{e,ab}(I\otimes F)&=&-D_a\otimes FD_b,\\
 A_{e,ab}(F\otimes I)&=&-FD_a\otimes D_b,
\end{array}
\qquad D_a=\sigma_a\otimes I-I\otimes\sigma_a.       \tag{O4.12z25a}
\]

The two mismatch outputs are nonzero and orthogonal.  Hence each fixed edge
map is injective on its endpoint-mismatch coordinate sector.  Distinct edges
land in mutually orthogonal sectors labelled by their two nonsinglet
endpoints.  If `P_e` retains the bit strings mismatched on edge `e`, graph
connectedness gives

\[
 \bigcap_e\ker P_e
 =\operatorname{span}\{I^{\otimes n},F^{\otimes n}\}. \tag{O4.12z25b}
\]

For any subspace `U` of the singlet quotient, the stacked mismatch projection
is therefore injective and the orthogonal edge images add, giving

\[
 \boxed{\quad
 \dim\operatorname{span}_{e}A_{e,ab}^{(2)}U
 =\sum_e\dim P_eU\ge\dim U.
 \quad}                                               \tag{O4.12z25c}
\]

Thus `(O4.12z25)` is now proved separately on both canonical layers:
`(O4.12z19c)` handles the orthogonal complement of sitewise singlets and
`(O4.12z25c)` handles the singlet quotient.  The unresolved two-replica
quantifier is only the gluing of arbitrary subspaces crossing those layers;
separate Hall inequalities do not automatically control overlap of their
outputs.  Full proof of `(O4.12z25c)` is in
`../3-formalized/two-replica-singlet-pauli-hall-expansion.md`.
The all-subspaces dimension mechanism is formalized as
`resolvedFiberAssembly_subspace_finrank` in
`HTGeometry/ResolvedFiberHallExpansion.lean`. Physical completion of the
quadratic synchronized-Casimir input is exact in
`HTGeometry/TwoReplicaGlobalSingletEdgeCasimirBridge.lean`.
Formal completion of `(O4.12z25c)` still requires the stronger concrete
fixed-orientation single-commutator mismatch projections and injective
assembly of distinct edge-defect sectors. Mixed-subspace Hall gluing then
requires the product-Clifford reducing decomposition and visible quotient
detector; no full two-replica Hall claim is made yet.

Primary inputs are V. Kargin,
[*An algebraic characterization of non-singular matrix semicircles*](https://arxiv.org/abs/2604.23089)
and [*Singularities of matrix semicircles*](https://arxiv.org/abs/2607.26222).
The support-Casimir, fullness, scalar absolute-continuity, and operator-norm decay chain is
dependency-closed on paper and unconditionally formalized in
`../3-formalized/one-replica-local-pauli-planar-cavity-decay.md`.

`[CONJECTURE — PLANAR-RENORMALIZED REPLICA GENUS LAW.]`  Exactly resum every
genus-zero component of the full admissible replica ribbon expansion into a
positive matrix-valued cavity propagator.  In the connected polymer
expansion relative to that propagator:

1. use the fixed-order contraction (O4.12z10) after, rather than before,
   exact planar dressing, so pairing multiplicity is paid only by the
   cavity propagator;
2. prove the dressed handle polymers are contractive in the Bellman
   crossnorm (O4.12z7);
3. extend the exact collective contraction (O4.12z12) to the joined
   multi-boundary hierarchy and prove decay on the orthogonal complement of
   the exact permutation fixed algebra (O4.12z14); and
4. control the remainder not captured at any finite genus directly in the
   positive selector norm.  It may not be replaced by a target-independent
   recurrence event followed by Haar-cap circuit counting, which is ruled out
   by `(O4.2a)--(O4.2c)`.

This replacement survives the killing example because it retains the whole
noncrossing Catalan sector in the reference propagator instead of calling it
exceptional.  It is stronger than a coefficient estimate: it asserts a
positive decomposition compatible with the Hamiltonian-dependent circuit
selector.  Its former first open implication, the multi-backbone
Schwinger--Dyson loop identity, is now (O4.12z6).  Two-replica local-singlet
synchronization is now `(O4.12z21)--(O4.12z24)`.  Its hostile audit exposes
the genuinely stronger first open implication: prove the Pauli Hall law
`(O4.12z25)` at every required growing replica order, hence fullness and a
quantitative operator scaling on the quotient by the global permutation
algebra.  After that algebraic gate, one still needs strict normalized
cavity/handle contraction in the exact Bellman crossnorm (O4.12z7) after
exact planar dressing.  The fixed-`q` multi-backbone estimate needed at that
point is already (O4.12z10).

This statement does not silently normalize away the number of Wick
pairings.  If the coefficient dictionary has size `m`, conversion from the
uniform pairing-and-label average to the degree-`2k` spherical moment carries
the exact scalar factor

\[
 a_{m,k}
 ={m^k(2k-1)!!\over m(m+2)\cdots(m+2k-2)}.                         \tag{O4.12z}
\]

It is obtained by summing the normalized label average over `m^k` block
labels and the normalized pairing average over `(2k-1)!!` pairings, then
dividing by the angular moment denominator (O4.12f).  The common commutator
amplitude and the chosen interaction-rate normalization must also remain in
the polynomial coefficient.  Thus (O4.12y) is a genuine exponential
contraction of the signed combinatorial factor, but not yet a bound on the
resummed unitary propagator.

Equations (O4.12q)--(O4.12z14) move the open core through the fixed-order
multi-backbone and selector geometry.  The exact remaining analytic task is
to solve the joined planar hierarchy on the complement of its permutation
fixed algebra, dress (O4.12z10) by that solution, and isolate the common
nonperturbative recurrence core once before the spherical/time transform.
Absolute Taylor summation is forbidden: it destroys the unitary
cancellations and introduces an artificial `e^(t\|\mathcal L\|)` loss.

That nested sector can be resummed exactly.  Let `N_k(z)` be the coefficient
of `P_z` obtained by summing the `2k`-th Wick expansion over noncrossing
pairings only, with `N_0(z)=1`.  Decomposing at the chord incident to the
first location gives

\[
 N_k(z)=4\sum_{\omega(p,z)=1}v_p
       \sum_{j=0}^{k-1}N_j(z+p)N_{k-1-j}(z).                          \tag{O4.13}
\]

Indeed the opening commutator moves `z` to `z+p`, the `j` enclosed pairs
return to `z+p`, the closing commutator contributes the second factor of two
and returns to `z`, and the remaining pairs evolve from `z`.  Hence the
formal generating functions

\[
 \mathcal N_z(u)=\sum_{k\geq0}N_k(z)u^k
\]

are the unique coefficientwise solution of the coupled cavity equations

\[
 \mathcal N_z(u)=
 {1\over
  1-4u\sum_{\omega(p,z)=1}v_p\mathcal N_{z+p}(u)}.                    \tag{O4.14}
\]

This is an exact all-orders self-energy law on the Pauli commutator graph.
For example, if `lambda_z <= Lambda` on the reachable component, induction in
(O4.13) yields

\[
 0\leq N_k(z)\leq C_k(4\Lambda)^k,                                  \tag{O4.15}
\]

where `C_k` is the `k`-th Catalan number.  Thus nested growth is not an open
diagrammatic remainder.  Pairings with crossing chords remain: commuting
crossings form the Gaussian background, whereas their nonempty
anticommutation subgraph is constrained by (O4.12) to be Eulerian.

The locality cost of those components has a uniform combinatorial bound.
Take the uniform weight-`q` ensemble and sample the `k` block labels
independently.  For any fixed set of `v` blocks, a connected
anticommutation graph forces their `q`-site supports to be connected by
overlaps.  For a fixed labelled spanning tree, expose it away from a root.
At every new vertex, its independent uniform `q`-subset intersects its
parent's fixed `q`-subset with probability at most

\[
 \mathbb P(S_a\cap S_b\ne\varnothing)
 \leq\mathbb E|S_a\cap S_b|={q^2\over n}.
\]

Cayley's formula and a union bound over the chosen vertices therefore give

\[
 \mathbb P(\text{some nonempty Eulerian crossing component})
 \leq
 \sum_{v=3}^{k}{k\choose v}v^{v-2}
       \left({q^2\over n}\right)^{v-1}.                              \tag{O4.16}
\]

The lower limit is three because a nonempty connected simple Eulerian graph
contains a cycle.  This estimate is uniform in the chord pairing, seed label
`z`, and Pauli letters; anticommutation is stronger than support overlap, so
forgetting letters only enlarges the event.

Writing `x=e q^2 k/n`, the right side is at most

\[
 {n\over q^2}\sum_{v=3}^{k}{x^v\over v^2}.
\]

For `x<=1/2` it is bounded by

\[
 {2e^3q^4k^3\over9n^2}.                                             \tag{O4.17}
\]

Consequently, if `R_(2k)^cross(z)` denotes the absolute Wick contribution
from labelings with a nonempty crossing-memory component, then

\[
 |R_{2k}^{\rm cross}(z)|
 \leq
 4^k(2k-1)!!\left(\sum_pv_p\right)^k
 \sum_{v=3}^{k}{k\choose v}v^{v-2}
       \left({q^2\over n}\right)^{v-1}.                              \tag{O4.18}
\]

Thus genuine crossing memory is negligible uniformly for
`k=o_q(n^(2/3))`, improving the unrenormalized pair-collision window
`k=o_q(sqrt(n))`.  The exponent `2/3` is not asserted sharp: it is the first
cycle threshold of the rigorous tree bound.  Reaching order `n` requires
resumming triangle and higher Eulerian polymers rather than bounding their
occurrence probability.

More generally, suppose every Eulerian crossing component on at most `L`
blocks has been summed into a dressed background.  The absolute unsummed
remainder is supported on a component of size at least `L+1`, and the same
tree argument gives

\[
 \mathbb P(\text{an unsummed component remains})
 \leq
 \sum_{v=L+1}^{k}{k\choose v}v^{v-2}
       \left({q^2\over n}\right)^{v-1}.                              \tag{O4.19}
\]

If `x=e q^2 k/n<=1/2`, this is at most

\[
 {2n\over q^2}\,{x^{L+1}\over(L+1)^2}.                              \tag{O4.20}
\]

For every fixed `L`, exact resummation through size `L` therefore controls
the remainder for

\[
 k=o_q\!\left(n^{L/(L+1)}\right).                                   \tag{O4.21}
\]

The sequence begins with the triangle threshold `n^(2/3)`, then
`n^(3/4)`, and tends to `n` as `L` grows.  This proves that no finite list of
connected corrections reaches the order-`n` transition.  The complete
signed polymer free energy, not another fixed cumulant, is the next
load-bearing object.

The same bound nevertheless reaches order `n` at the structural level.  Let
`k=floor(kappa n)` and assume

\[
 x_\kappa=e q^2\kappa<1.
\]

Choose `L_n=ceil(C log n)` with
`C>1/|log x_kappa|`.  Equation (O4.20) then gives

\[
 \mathbb P\!\left(
 \begin{array}{c}
 \text{some Eulerian crossing-memory component}\\
 \text{contains more than }L_n\text{ blocks}
 \end{array}\right)
 \longrightarrow0.                                                  \tag{O4.22}
\]

Indeed `n x_kappa^(L_n+1)/(L_n+1)^2 -> 0`.  Thus below the explicit
subcritical density `1/(e q^2)`, an order-`n` Wick word decomposes with high
probability into crossing-memory components of logarithmic size.  The
remaining difficulty is not a macroscopic connected diagram; it is the
collective signed free energy of extensively many small components and
their seed-parity dressing.

This Eulerian law moves the live problem beyond the elementary `k^2/n`
collision ceiling.  The next object is a forest-renormalized expansion in
which all nested self-energy insertions are summed exactly and the remaining
polymers are Eulerian crossing components.  For fixed-`q` labels, a connected
component on `v` sampled local words already costs support coincidences; the
Eulerian condition excludes the single-edge component that would have
produced the earliest divergence.  What remains unproved is a uniform
polymer bound after `k` reaches order `n`, followed by a joint-amplitude
version against the complete circuit tube.  Even a complete return-moment
resummation would not by itself prove O4.

A circuit-tube estimate at gate budget `s` must ultimately control entropy at
order comparable to `s`, which reaches `Theta(2^n/poly(n))` at saturation.
Fixed-order moment universality, including (O4.8), still cannot pay that
entropy; the exact gain is that the first nontrivial resummation target is
now a cycle gas rather than an arbitrary collision gas.

### O5. Quantitative first hitting

Upgrade completed-time occupation to a first-return lower bound from the
simple initial state and match it with a deterministic doubly exponential
upper bound. Unique ergodicity alone is insufficient.

### O6. Permanent locality witness

Formalize an explicit two-query experiment and prove a uniform advantage for
every time in the fixed-locality ensemble. The theorem must expose all
normalizations and query resources.

**Literature closure and formalization status.**  This obligation is no longer
an open research theorem.  Cui--Schuster--Mao--Huang--Brandao, *Random
unitaries from Hamiltonian dynamics*, arXiv:2510.08434 (2025), prove it for an
arbitrary distribution of fixed-`q` Hamiltonians and arbitrary evolution
times.  Their forward-only protocol prepares two copies of a random stabilizer
product state, applies the same sampled `U=exp(-itH)` once to each copy, and
measures the same uniformly sampled allowed Pauli on both copies.  For a local
Pauli dictionary of size `M_q`, its mean squared signal obeys

\[
 E_{\rm local}\geq {3^{-q}\over M_q},
 \qquad
 M_q\leq 4^q n\quad\hbox{(one-dimensional)},
 \qquad
 M_q\leq (4n)^q\quad\hbox{(all-to-all)}.
\]

The bound is uniform in time because `H` itself is the conserved local
observable.  Haar output gives exponentially small signal, yielding the
required inverse-polynomial two-query advantage for fixed `q`.  The final
paper must cite this theorem as an input; it is not part of our novelty.

`ConservedLocalCompressionWitness.lean` now certifies the
dimension-independent algebraic core: autonomous Heisenberg evolution fixes
`H` exactly; every local compression matrix with this nonzero fixed coordinate
has squared Frobenius mass at least one; its uniformly sampled mean transition
weight is at least `1/M_q^2`; and it strictly exceeds an isotropic
`1/(4^n-1)` benchmark whenever `M_q^2<4^n-1`.  Remaining Lean port obligations
are the random stabilizer-product twirl giving `3^{-q}`, the Pauli dictionary
cardinality bounds, and the explicit Haar/two-design comparison.  O6 is
therefore closed in external mathematics but not yet dependency-closed in
Lean.

### O7. Physics transfer

Prove the theorem directly for fixed-`q` SYK before making a black-hole-model
claim. A result only for abstract Pauli ensembles permits quantum-many-body
conclusions, not a claim about real black holes or spacetime interiors.

## State-design route audit

The tempting bridge

\[
  \text{high-order state design}\quad\Longrightarrow\quad
  \text{high state-circuit complexity}
\]

does not presently close O4.  Current autonomous-Hamiltonian results establish
late-time Haar moments only for each fixed design order `k`, or obtain a
finite-time error of order `1/T` while the Haar `k`-frame-potential scale is
of order `D^{-k}`.  The resulting requirement `T \gtrsim D^k` yields at most

\[
  k \lesssim \log_D T,
\]

so design order certifies at most logarithmic-in-time complexity rather than
Brown--Susskind linear growth.  Multiple quenches improve the temporal power
but replace one time-independent Hamiltonian by driven dynamics and therefore
do not satisfy the target.

The only surviving design formulation strong enough for O4 would be a new
fixed-time theorem for the *static local Hamiltonian ensemble*: design order
`k(t) \asymp t` up to `k \asymp D`, together with concentration from the
Hamiltonian ensemble to individual autonomous trajectories and robustness to
polynomial-bit coefficient perturbations.  None of these three statements is
available in the audited literature or corpus.  They remain possible proof
targets, not premises.

## Hard barrier

Robust superpolynomial circuit complexity for exponentially long evolution of
succinct local Hamiltonians is tied to
`PSPACE not subset of BQP/poly`. The proof programme must either establish the
needed separation, find and justify a theorem formulation outside the exact
equivalence while retaining physical meaning, or fail honestly. Continuous
random coefficients do not license hiding exponential information in the
Hamiltonian: robustness and coefficient precision must be audited.

## Literature collision and exact novelty

The slogan “ballistic escape plus entropic return” and the critical-metric
picture are not themselves novel.  Brown--Freedman--Lin--Susskind already
conjecture exponentially late cut loci for typical local directions.  Earlier
work of Balasubramanian--DeCross--Kar--Parrikar excludes *local* obstructions
under the Eigenstate Complexity Hypothesis but explicitly leaves global
shortcuts open.  Brown's Bishop--Gromov argument proves exponential complexity
for typical ambient unitaries, not for the one-parameter orbit of a succinct
static local Hamiltonian.

The admissible novelty claim is therefore exact and falsifiable: first
unconditional proof of the directional critical-metric conjecture for an
ordinary time-independent fixed-locality ensemble, followed by the first
single theorem deriving its growth, plateau, first low-complexity recurrence,
and all-time non-Haar witness.  If the directional cut-time theorem cannot be
proved, no geometric slogan is promoted as a discovery.

## No-go discipline

Failure of O4 kills the master theorem. It does not authorize publication of
O2, O3, O5, or O6 alone as the same universal law. Any positive survivor must
receive a new title and an independent significance audit.

## Log

- 2026-08-01 -- Created in 1-in-progress after literature-first collision
  audit. Existing recurrence and Haar infrastructure inventoried; circuit
  complexity absent; O4 identified as open core.
- 2026-08-01 -- Audited the autonomous state-design route. Fixed-order moment
  convergence and one-quench finite-time estimates imply only
  `k \lesssim log_D T`; they cannot yield linear complexity growth. The route
  survives only as a substantially stronger fixed-time random-static-local-H
  design theorem with concentration and precision robustness.
- 2026-08-01 -- Immediate collision audit identified the proposed global
  minimizing-geodesic mechanism as part of the
  Brown--Freedman--Lin--Susskind critical-metric programme, not a new slogan.
  Later primary-source re-audit corrected the stronger attribution: their
  paper does not state a numbered exponentially-late directional cut-locus
  conjecture.  O4 is the new fixed-`q` directional strengthening, including
  the global-shortcut gap that local conjugate-point arguments do not close.
- 2026-08-01 -- Closed O2 on paper by a full-symmetric spectral-monodromy
  theorem for generic two-local Pauli Hamiltonians. Isolated star-Ising edge
  degeneracies supply all Boolean-hypercube transpositions; the resulting
  `S_(2^n)` monodromy forbids every projective rational resonance almost surely.
  Choi evolution supplies uniform spectral weights. Lean remains pending.
- 2026-08-01 -- Promoted the scientific target from a four-result conjunction
  to the falsifiable No-Shortcut Law for Autonomous Time: normalized physical
  duration equals irreducible endpoint-preparation work until finite-state
  saturation, after which spectral entropy fixes the plateau and return scale.
  Recorded fast-forwardable systems as a required complementary class rather
  than hiding them behind "generic".
- 2026-08-01 -- Formalized exact equal-weight Choi phase-density geometry and
  the displacement-to-coherence implication in
  `StaticChoiPhaseDensity.lean`; the file compiles in isolation.  Together with
  `StaticChoiPhaseTargetEntropy.lean`, this closes the geometric core of O3 in
  Lean, leaving finite circuit counting and completed-time specialization.
- 2026-08-01 -- Retired the circuitwise temporal-min-entropy route.  A
  normalized one-Pauli recurrence point gives the identity circuit capture
  probability at least `t^(-O(m))`, contradicting the `exp(-Omega(s))` bound
  needed by a word-by-word union when `s` is linear in exponential time.
  Replaced it by the aggregate autonomous word-escape target `(O4.3)`, whose
  failure exponent is compatible with this sharp obstruction and sufficient
  for uniform-in-time growth.
- 2026-08-01 -- Lean-proved the dimension-free analytic core of that no-go in
  `FiniteHorizonCStarPerturbationLaw.lean`: an exact periodic Hamiltonian is
  the center of an operator-norm shortcut tube with radius proportional to
  `epsilon/|t|`.  Gaussian box volume remains paper-only and is not a
  manuscript claim.
- 2026-08-01 -- Strengthened the formal no-go from a conditional periodic
  center to an explicit fixed-energy non-scalar model.  The two-level sign
  Hamiltonian has norm `|omega|`, returns exactly to the identity at every
  `2 pi k / omega`, and its full self-adjoint perturbation tube obeys the
  dimension-free `|t| ||H-K||` bound.  Therefore neither removal of `H=0` nor
  conditioning on nonzero energy can support a word-by-word exponential
  capture bound.
- 2026-08-01 -- Proved the dimension-free hard-power amplification law in
  `FiniteHorizonCStarPerturbationLaw.lean`: `||U^N-V^N|| <= N||U-V||`, exact
  autonomous endpoint composition, and the converse `epsilon/N` separation
  theorem.  This transfers exact endpoint hardness backward but also exposes
  the unavoidable linear resolution loss, so plateau plus subadditivity alone
  cannot establish fixed-error robust growth.
- 2026-08-01 -- Located complete external closure of O6 in Cui et al.
  (arXiv:2510.08434): a forward-only two-query randomized stabilizer/Pauli test
  distinguishes every fixed-`q` Hamiltonian ensemble from Haar at every time.
  Formalized its conserved-coordinate and inverse-dictionary-squared signal
  core in `ConservedLocalCompressionWitness.lean` and wired the module into the
  HTGeometry umbrella.  Pauli-twirl and Haar benchmark ports remain.
- 2026-08-01 -- Closed O3's completed-time transfer first on the full torus,
  then found and repaired its failure for traceless Hamiltonians.  The new
  compiled projective capstone
  `completedTime_zeroAnchoredPaddedCircuitTargets` proves an exact
  measure-preserving global/projective phase split, derives rational
  independence of physical relative frequencies from maximal projective rank,
  and transfers the explicit Choi circuit-target bound to completed time.
- 2026-08-01 -- Replaced the failed robust power route by a one-step
  autonomous concatenation theorem.  `AutonomousWordComplexityConeLaw.lean`
  proves that a `P`-hard late endpoint and an `r`-gate increment force
  `(P-r)` hardness at the earlier endpoint with only additive fixed error.
  This gives a full backward linear cone below every hard plateau endpoint;
  the first plateau hitting/cut-time bound remains the exact unresolved O4
  core.
- 2026-08-01 -- Strengthened the cone to the operator-norm unitary group of
  every unital C-star algebra and proved syndetic cone propagation: recurring
  hard endpoints generate recurring backward ramps with the same gap bound.
  No Hilbert--Schmidt normalization or `1/N` error collapse remains in this
  transfer layer.
- 2026-08-01 -- Proved `StaticChoiSyndeticComplexityLaw.lean`.  For every
  maximally projective finite spectrum and every finite circuit dictionary
  whose explicit target-volume bound is below one, every interval of one
  finite length contains a hard Choi endpoint.  This upgrades an asymptotic
  plateau fraction to infinite, uniformly recurrent hard endpoints.  The gap
  is nonquantitative; controlling it at exponential saturation scale is the
  remaining first-cut problem.
- 2026-08-01 -- Closed the spectral-subspace target objection in
  `StaticChoiFullStateProjectionLaw.lean`.  Diagonal density restriction from
  the full Choi tensor-square space is contractive, and the true evolved full
  density restricts exactly to the phase density.  The syndetic theorem now
  holds against arbitrary full circuit-target densities without dimension or
  radius loss.
- 2026-08-01 -- Closed the operational-metric objection in
  `StaticChoiTraceDistanceLaw.lean`.  For normalized pure states the full
  density Hilbert--Schmidt distance is proved exactly equal to `sqrt 2` times
  trace distance; the physical diagonal-unitary Choi vector is normalized and
  has exactly the previously used full density.  Hard Choi endpoints are now
  syndetic against normalized pure circuit targets in operational trace
  distance.
- 2026-08-01 -- Replaced the plateau-only statement by an ordered universal
  mechanism.  `denseAddOrbit_disjoint_open_targets_alternate_syndetically`
  proves that every dense real flow on every compact group alternates between
  any two disjoint nonempty open regimes, with one finite bound on every leg.
  `StaticChoiComplexityAlternationLaw.lean` instantiates the regimes as
  recurrence to the identity channel and separation from every circuit of
  bounded depth.  After every starting time there is a strictly ordered
  low--high--low cycle, and this repeats forever.
- 2026-08-01 -- Closed local-Hamiltonian ensemble transfer for the already
  formal finite Anderson family in
  `FiniteAndersonChoiComplexityAlternationLaw.lean`.  For every fixed finite
  Hermitian hopping matrix, the existing corpus proves that qualifying onsite
  potentials are dense, residual, and full Lebesgue measure; every qualifying
  Hamiltonian obeys the operational low--high--low law.  This does not yet
  formalize the separate paper-only nearest-neighbour many-body qudit result.
- 2026-08-01 -- Axiom audit of the trace identity, syndetic trace-hard law,
  ordered alternation law, and finite-Anderson specialization reports only
  `propext`, `Classical.choice`, and `Quot.sound`.  O4 remains narrower and
  harder: a quantitative direct-simulation cut time/no-shortcut theorem.  The
  qualitative infinite alternation and local-H transfer no longer depend on
  O4.
- 2026-08-01 -- Proved the ambient-seed recurrence amplifier in
  `MetricEntropyRecurrenceAmplificationLaw.lean`: if an ambient carrier needs
  more radius-`epsilon` balls than a circuit endpoint dictionary contains, one
  hard seed on one compact autonomous slice generates ordered easy--hard--easy
  epochs forever.  Ambient covering entropy sets circuit depth; recurrence
  amplifies one seed in time.  The slice dimension does not cap a hardness
  certificate imported from its ambient family.
- 2026-08-01 -- Isolated and proved the spectrum/orientation separation law.
  `PeriodicMetricEntropySeparationLaw.lean` gives exact period-one bounds:
  after every start, easy, hard, and easy phases occur in strict order with
  every leg at most one period.  `StarProjectionPeriodicComplexityLaw.lean`
  proves that `1 + (exp(2*pi*i*theta)-1)P` is a continuous unitary subgroup for
  every star projection, proves the exact idempotent exponential formula, and
  identifies it with ordinary time-independent evolution `exp(-itH)` for the
  self-adjoint Hamiltonian `H=-2*pi*P`.  Thus eigenvalues set the recurrence
  clock while eigenspace orientation sets which endpoints the clock contains;
  locality is the extra structure that can couple the two.
- 2026-08-01 -- Removed the remaining entropy premise in a concrete quantum
  model.  `FinTwoProjectorClockComplexityLaw.lean` constructs an injective real
  line of rank-one projections in `M_2(C)`, proves its nontrivial phase carrier
  infinite, and proves: for every finite gate alphabet and every requested
  circuit depth `s`, some exactly one-periodic two-level static Hamiltonian has
  a positively separated depth-`>s` endpoint in every period, bracketed by
  identity-near epochs.  Resolution and Hamiltonian may depend on `s`; the
  theorem does not give fixed-resolution many-body maximal complexity and does
  not close O4.  Axiom audit reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
- 2026-08-01 -- Closed the fixed-resolution and many-body-size gaps for the
  nonlocal recurrence/complexity separation theorem.
  `DiagonalProjectorClockPackingLaw.lean` proves that the `2^D` Boolean
  diagonal projections in `M_D(C)` give half-period reflections at pairwise
  operator-norm distance exactly `2`.  Their external covering number at
  radius `1/2` is therefore at least `2^D`.  For every finite gate alphabet of
  size `g` and every depth `s` with
  `sum_(k=0)^s g^k < 2^D`, one diagonal star projection `P` yields the ordinary
  self-adjoint static Hamiltonian `H=-2*pi*P` whose evolution has exact period
  one and, after every start, a strict easy--hard--easy sequence with each leg
  at most one period; the hard endpoint is more than `1/2` in operator norm
  from every word of depth at most `s`.  Thus fixed-resolution exponential
  circuit hardness and immediate exact recurrence are rigorously compatible.
  The selected Boolean spectral projector is generally not fixed-`q` local.
  Hence this theorem proves that recurrence time alone cannot control
  complexity and isolates locality, rather than spectrum, as the remaining
  coupling mechanism.  It does not close O4's static fixed-local no-shortcut
  law.  Axiom audit of the packing, cardinal, fixed-radius recurrence, and
  circuit-hard capstones reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
- 2026-08-02 -- Strengthened O6 from the earlier inverse-dictionary-squared
  compression surrogate to the physical dimension-linear scale.
  `ConservedLocalTwoQuerySignalLaw.lean` proves the exact lower bound
  `3^(-q)/M`, hence `1/(12^q n)` for a one-dimensional fixed-`q` dictionary
  and `1/(12n)^q` all-to-all. `ProductStabilizerPauliTwirlLaw.lean` proves the
  six-state single-qubit twirl, its independent product factorization, exact
  cancellation of distinct Pauli strings, and equality of the operational
  two-copy protocol correlation with that weighted coefficient signal.
  `FiniteUnitaryHaarMeasureLaw.lean` constructs normalized Haar probability
  on every finite complex unitary group and proves the invariance, column
  normalization, permutation symmetry, and explicit coordinate mixers needed
  for the remaining Haar fourth-moment benchmark. All three modules compile
  individually with `lake env lean`; no forbidden declarations occur.
  O6 now lacks only completion of the exact Haar fourth-moment identity and
  dictionary-cardinality instantiation. O4 remains the master open core:
  a maximally hard endpoint by normalized time `O(2^n/poly(n))`, which the
  already compiled autonomous cone converts into the full initial linear
  growth ramp.
- 2026-08-02 -- Closed the exact Haar-moment and abstract all-time comparison
  layers of O6. `FiniteUnitaryHaarMeasureLaw.lean` now proves normalized Haar
  is a probability measure, exact first moments, exact same-row and
  distinct-row fourth moments
  `2/(D(D+1))` and `1/(D(D+1))`, and the exact mean-square law
  `1/(D+1)` for every balanced operator-norm-one diagonal probe. It also
  constructs such a probe explicitly in every even dimension, including all
  nontrivial qubit dimensions. `PermanentLocalityHaarSeparationLaw.lean`
  combines that benchmark with the physical product-stabilizer lower bound:
  whenever `M*3^q < D+1`, every Pauli-transfer time slice fixing the nonzero
  local Hamiltonian coordinate has protocol signal strictly above Haar. Both
  modules compile individually with `lake env lean`; the new separator is
  imported by the `HTGeometry` umbrella. Remaining O6 work is the concrete
  fixed-local Hamiltonian-to-Pauli-transfer instantiation and full same-score
  ensemble packaging, not the moment or dimension-linear inequality. The
  explicit balanced diagonal observable is also constructed as a unitary
  matrix and proved to have L2 operator norm exactly one, closing the previous
  Hilbert--Schmidt-normalization objection.
  `SelfAdjointPauliTransferConservationLaw.lean` then removes the abstract
  fixed-vector assumption: in every finite real basis of self-adjoint
  observables, the exact Heisenberg transfer matrix of every nonzero
  time-independent Hamiltonian fixes its nonzero coefficient vector at every
  real time. Combining this with the product-stabilizer theorem gives the
  strict all-time Haar gap directly for the basis-coordinate transfer matrix.
  The module compiles and is imported by `HTGeometry`. Remaining O6 work is a
  fully explicit arbitrary-qubit Pauli-basis realization tying the label
  combinatorics to matrix expectations; O4 remains unchanged and is still the
  master theorem gap.
- 2026-08-02 -- Completed the literal arbitrary-qubit Pauli realization in
  `FiniteQubitPauliBasisLaw.lean`. The module proves exact Pauli-string
  Hilbert--Schmidt orthogonality, constructs the real basis of all Hermitian
  matrices, defines the principal weight-`q` Pauli-transfer block, and proves
  that every nonzero Pauli-`q`-local finite-matrix Hamiltonian supplies a
  nonzero fixed vector of that block at every real time. Consequently its
  local two-query sub-signal strictly exceeds the inverse-Hilbert-dimension
  benchmark whenever `M_q 3^q < 2^n+1`. The module compiles in isolation and
  is wired into `HTGeometry`; the final identical-protocol Haar ensemble
  packaging remains. No new O4 endpoint machinery appeared in the concurrent
  corpus audit: the maximally hard endpoint by time `O(2^n/poly(n))` remains
  the unique growth bottleneck.
- 2026-08-02 -- Falsified the proposed “remove common recurrence mass, then
  union Haar caps over fixed short circuits” architecture.  A general
  Lipschitz capture-tube theorem shows that every attained short target, not
  only a recurrence, has parameter mass `Omega(t^(-m))`; any
  target-independent exceptional set leaving Haar-scale caps must absorb
  every separated shortcut island.  This makes the proposed exceptional set
  identical in difficulty to O4 rather than an independently bounded
  recurrence event.  Replaced it with the exact selector-aware invariant:
  fixed-radius packing of the complete radial shortcut locus.  Proved that,
  across arbitrarily small error and relative-budget margins, annular volume
  deficit `(O4.3i)` and shortcut-centre packing deficit `(O4.3t)` imply one
  another.  The remaining frontier is now cleanly the direct packing bound;
  fixed-target Haar anti-concentration cannot cross it.
- 2026-08-02 -- Audited
  `riemann-hellinger-hodge-green-descent` against O4.  Its only valid
  transfer is the instruction to preserve labels before scalarization; its
  Hodge and Green maps remain linear and do not control the nonlinear circuit
  selector.  Proved a stronger negative Hellinger result: an `m`-parameter
  static-Hamiltonian endpoint law on `CP^(D-1)` is supported on a
  Hausdorff-dimension-at-most-`m` image.  For `m<2D-2` it is mutually singular
  with Haar, with zero Hellinger affinity and maximal total-variation
  distance at every fixed time.  Hence no positive-mass “Haar bulk”
  decomposition exists for fixed-`q` static ensembles; only direct
  circuit-test discrepancy or shortcut-locus packing can close O4.  The
  Riemann paper's “Quantum recurrence” row is a two-state Gibbs limit, not a
  unitary-orbit recurrence or complexity theorem.
- 2026-08-04 -- Audited Al-Ghattas--Gamarnik's July 2026 selector-aware
  Gaussian-process lower bound for random quantum spin glasses.  Their
  marginal-subtracted residual and pruned backward-cone entropy genuinely
  take the supremum over all ancilla-assisted shallow circuits before the
  probability bound.  The transfer to autonomous growth is nevertheless
  exactly inert: energy and every spectral function of `H` are conserved, so
  the evolved endpoint never beats the simple-state benchmark containing its
  input; fixed-observable commutator currents are bounded signed coboundaries;
  and the residual variance gain ends when depth-`D` light cones saturate at
  `D=Theta(log n)`.  Recorded `(O4.G1)--(O4.G4)` and the surviving requirement
  for a disorder-linear, nonconserved, non-coboundary witness whose circuit
  residual continues contracting after light-cone saturation.
- 2026-08-04 -- Converted the Hellinger--Hodge--Green viewpoint into the
  finite Liouvillian normal form `(O4.G5)`: every fixed linear observable is
  its zero-gap conserved part plus one exact commutator coboundary.  Formalized
  the algebraic core as `transitionGap_hodgeGreen_decomposition`, built the
  module, and audited standard axioms only.  This closes fixed linear
  witnesses as an indefinite-growth strategy but does not give a uniform
  growth-scale bound because the Green primitive can diverge with inverse
  spectral gaps.
- 2026-08-04 -- Re-audited the updated Hellinger--Hodge--Green paper.  Its
  positive uniform-capacity separation uses a nonzero real Cartan rate;
  autonomous Hermitian phases have zero Cartan rate, so that mechanism is
  inert for quantum circuit growth.  Extracted a sharper formal no-go from
  its strict-reduction law: every Hilbert reporter of `N` resolved circuit
  labels loses lower modulus at least as `N^(-1/2)`, and no infinite
  `ell^1` label reporter has positive lower modulus.  Therefore common linear
  reporting cannot replace selector-aware annular shortcut packing.
- 2026-08-04 -- Extracted and formalized the positive Hellinger survivor.
  The resolved selector-removal law `(O4.H3)--(O4.H6)` retains Hamiltonian as
  fibre label and bounds any Hamiltonian-dependent circuit selector by one
  reciprocal positive certificate uniform over all circuits in that fibre.
  This removes the circuitwise union without commuting `sup` and expectation,
  but does not close O4: one must still construct a noncircular local-dynamical
  barrier with exponential linear-in-time rate.  Exact continuum theorem is
  `resolvedHellinger_selectorRemoval` in
  `../3-formalized/resolved-hellinger-selector-removal-law.md`.
- 2026-08-04 -- Proved the finite resolved-Hellinger minimax classification
  `(O4.H7)--(O4.H8)`: the optimal common reciprocal certificate equals twice
  the maximal Hellinger affinity between the endpoint observation law and the
  convex hull of all short-circuit observation laws.  Hence fixed-target
  separation is insufficient.  If the shortcut convex hull contains the
  endpoint law, every scalar certificate is trivial; in particular one
  projective measurement fails once its basis states are within the circuit
  budget.  Any viable Hellinger attack must retain coherent or replica data
  and prove a quantitative convex-hull deficit at the full growth rate.
- 2026-08-02 -- Corrected a fatal plateau semantic overclaim: the existing
  `Omega(2^n/poly(n))` Choi lower bound is on `2n` qubits and is only the
  square-root scale of unrestricted `2n`-qubit state complexity.  Proved two
  replacement bridges on paper.  First, the exact projective 2-design moment
  of stabilizer states selects one fixed polynomial-preparable `n`-qubit
  input, independent of `H`, whose spectral collision mass is at most
  `K/2^n` with Hamiltonian failure below `2/K`.  A new
  collision-to-Steinhaus theorem then bounds every fixed target phase cap by
  `8 exp(-(1-epsilon^2)^2 2^n/(64K))`, so the circuit union yields a genuine
  `n`-qubit near-maximal plateau.
- 2026-08-02 -- Strengthened that repair to an explicit product input for a
  fixed-local black-hole-relevant ensemble.  Proved the compact
  symmetry-orbit frame law: if the tensor-square orbit of `psi_0` spans an
  irreducible carrier of dimension `R`, every conjugation-invariant
  `D`-dimensional Hamiltonian ensemble has expected spectral collision at
  most `D/R` for that fixed input.  For the Fock vacuum in the half-spin
  representation of `Spin(2m)`, the carrier is the Cartan square of dimension
  `binom(2m,m)/2`, giving collision at most `sqrt(m)/2^(m-1)`.  Applied to the
  explicit isotropic SYK-`q` plus quadratic ensemble, whose simple spectrum is
  certified by a nonzero discriminant witness, this gives a fixed product
  vacuum plateau of complexity
  `Omega(2^(m-1)/(L sqrt(m) log M))` with Hamiltonian probability `1-1/L`.
  This avoids both eigenvector universality and the Choi dimension loss.
  O4's quantitative first-hard-time/direct-packing theorem remains open.
- 2026-08-02 -- Closed the fermionic O2 spectral premise on paper for the
  same isotropic two-plus-four-Majorana ensemble.  In a fixed parity sector,
  diagonal quadratic/quartic words give all degree-at-most-two Ising energies
  while quadratic cross-mode words generate every Hamming-two flip.  Any
  chosen parity-cube edge can be made the unique diagonal degeneracy; a
  two-parameter square-root loop swaps exactly that eigenvalue pair.  Since
  the Hamming-two parity graph is connected, these loops generate full
  `S_(2^(m-1))` spectral monodromy.  The standard-representation argument then
  excludes every nontrivial projective rational energy relation off a proper
  analytic set, so the full-density real Gaussian ensemble has simple
  spectrum and maximal projective rank almost surely.  The product-vacuum
  Spin/SYK phase-cap estimate therefore transfers to completed physical time,
  rather than remaining an abstract torus statement.
- 2026-08-04 -- Closed the two-replica local-singlet synchronization theorem
  on paper.  The full nine-direction two-site Pauli Casimir has exact
  invariant-sector spectrum `{0,0,48,80}` and kernel “swap neither or swap
  both.”  On every connected interaction graph, positivity and a local
  invertible change of basis reduce the common kernel to the two constant bit
  strings, hence exactly identity and global swap.  A hostile test then
  falsified the tempting upgrade from correct Casimir kernel to matrix-pencil
  fullness: two explicit Hermitian star matrices have positive Casimir and
  zero common kernel while shrinking a plane to a line.  The first remaining
  replica gate is now the strictly stronger Pauli Hall-expansion inequality
  `(O4.12z25)` for every subspace, not local-singlet synchronization.  Full
  proof and counterexample are in
  `../3-formalized/two-replica-local-singlet-synchronization-law.md`.
- 2026-08-04 -- Cross-audited `riemann-hellinger-hodge-green-descent` against
  the sharpened O4 frontier.  Its recurrence section supplies exactly the
  target-independent first split needed here: at every finite replica order,
  the finite-window survival moment is the exact resonant collision mass plus
  one nonresonant remainder, with norm at most
  `min(1,(T delta)^(-1))` and constant one independent of Hilbert dimension
  and replica order.  This is already formalized by
  `finiteSpectralSurvivalFidelityMean_eq_collisionMass_add_remainder` and
  `norm_fidelityReplicaFiniteWindowRemainder_le`.  On the complement, the
  already formalized `resolvedHellinger_selectorRemoval` can test the
  Hamiltonian-dependent best short circuit using one certificate uniform in
  the circuit target, so recurrence mass is paid once rather than once per
  circuit.  The paper does not supply the missing certificate: its
  Hodge--Green and observation-kernel laws control vector kernels and
  faithful transport, whereas `(O4.12z25)` is an all-subspaces obstruction
  (equivalently, nonvanishing through every exterior degree).  The exact
  surviving route is to combine the corpus theorem
  `tightOperatorFamily_subspace_finrank` with a replica Pauli scaling: a
  bi-tight scaled Pauli family implies Hall expansion immediately by
  Parseval--Bessel.  One-replica scaling `(O4.12z19)` is precisely this
  mechanism.  The all-replica central-Casimir scaling
  `(O4.12z19a)--(O4.12z19c)` now closes it on the orthogonal complement of
  the sitewise singlet algebra.  The genuine growing-replica frontier is the
  singlet-sector Hall law plus a mixed-subspace gluing theorem; a
  Hodge--Green inverse of a noncentral common-kernel Casimir alone cannot
  provide either.  Hostile quantifier audit also rejects the source paper's bare
  prose sentence “connected interaction graph of tensor dimension `D` has
  temporal rank `D-1`” as a universal Hamiltonian statement.  Its formal
  source `finiteGraphTemporalRank_of_connected` computes the separately
  defined *generic component-factorized rank*; actual spectral temporal rank
  reaches `D-1` only after an independent maximal-projective-rank theorem.
  None of the O4 argument may infer spectral rank from graph connectedness
  alone.
- 2026-08-04 -- Replaced the arbitrary mixed-subspace obstruction by a
  canonical one. For every finite linear family, deficiency
  `delta(U)=dim(U)-dim(span_j A_j U)` is supermodular, has a unique largest
  maximizer, and the full Hall condition is equivalent to the single scalar
  equation `delta(U_*)=0`. Every invertible input/output symmetry preserving
  the linear span of the family fixes `U_*`; the formal theorem covers
  continuous generator mixing, not only index permutations. Consequently a
  hypothetical local-Pauli Hall obstruction must be local-symmetry invariant
  and may be resolved into representation/Pauli-character sectors. The
  exact mixed-layer dimension identity is now also closed: forward Hall
  expansion from a singlet layer glues to a nonsinglet layer whenever a
  reverse channel expands the precise forward-image overlap; rank
  modularity proves that this overlap payment is sufficient. Finally, for
  any commuting involutions representing one physical Pauli on two replicas,
  the collective commutator squares to exactly `4I` on the relative-odd
  sector and is therefore invertible there. This all-subspaces rank law is
  instantiated for the literal one-qubit two-replica Pauli matrices. Global
  nonzero-grade selection and assembly, followed by the grade-zero edge
  image and reverse-overlap Hall expansion, are the remaining concrete
  gates; arbitrary singlet/nonsinglet mixing is no longer the correct
  formulation. Proofs and
  formal status are recorded in
  `../3-formalized/canonical-symmetry-reduced-hall-gluing-law.md`.
- 2026-08-04 -- Refreshed the five publication-ready manuscripts newer than
  `riemann-hellinger-hodge-green-descent`. `two-sided-singular-gelfand-defects` contributes the
  unconditional countable coercivity--defect dichotomy, already formalized in
  `PythagoreanObserverBlindness.lean`: in an infinite Hilbert source, countably many injective
  dense-range noncoercive observers admit a closed common blind space containing a countable
  independent family. This is useful for a later thermodynamic observability boundary but cannot
  close finite-dimensional Pauli Hall, because finite-dimensional injective dense maps are
  coercive. `riemann-relation-kernel-transgression` supplies the exact principle that a degree-two
  class made exact on a cover survives as a degree-one character on the relation kernel; its
  formalization suggests classifying the zero-sum syzygies of resolved Pauli images before
  augmentation, but supplies no such classification. `riemann-arithmetic-source-dagger-route`,
  `riemann-boundary-completeness-law`, and `real-corona-quaternionic-cyclic` provide respectively a
  canonical minimal invariant defect boundary, kernel-pair/graded recovery, and a two-sector
  Clifford grading. All are formally useful analogues, but current task-specific canonical-defect,
  overlap-compensation, and relative-Pauli inverse theorems are stronger for O4.12z25. No new paper
  proves Pauli Hall, selector-uniform Haar anti-concentration, or the circuit union.
- 2026-08-04 -- Proved the next symmetry-reduction layer. An invariant subspace of one involution
  splits internally into even and odd parts; under two commuting involutions it splits into four
  simultaneous parity sectors and their finranks add exactly. Paired two-replica Pauli conjugations
  are literal commuting involutions, so any subspace stable under two Pauli conjugations has the
  exact four-grade decomposition. The formal capstones are
  `invariantSubspace_eq_commutingInvolution_bigrading`,
  `invariantSubspace_finrank_eq_commutingInvolution_bigrading`, and
  `twoReplicaPairedPauliInvariantSubspace_eq_bigrading`. The remaining gate is no longer existence
  of a grading: prove concrete local-Pauli span covariance fixes the canonical global maximizer,
  then assemble the relative-odd inverses across the resulting global grades and close the
  grade-zero reverse-overlap channel.
- 2026-08-04 -- Closed concrete paired-Pauli covariance for the literal local Hall family. Exact
  conjugation sends the collective commutator on axis `a` to itself for the same axis and to its
  negative for either transverse axis. Hence the local operator-family span is preserved, and the
  unique greatest maximum-defect subspace is proved to be invariant under every paired-Pauli
  conjugation and to admit the four-sector Pauli bigrading. Formal capstones are
  `twoReplicaPairedPauli_collectiveCommutator_covariant`,
  `twoReplicaPairedPauli_conjugatedCollectiveCommutator_mem_span`,
  `twoReplicaLocalCollectiveCommutator_greatestMaximizer_fixed`, and
  `twoReplicaLocalCollectiveCommutator_greatestMaximizer_bigrading`; targeted compilation passes and
  axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`. This removes local span
  covariance as an assumed hypothesis. The exact surviving gate is arbitrary-site tensor lifting,
  followed by global nonzero-grade selection/assembly and the grade-zero reverse-overlap Hall law.
- 2026-08-04 -- Proved on paper an explicit collision-free selector for every nonzero global Pauli
  character. Grade a two-replica operator by its simultaneous characters under all paired local
  Pauli conjugations. For a nonzero grade, rotate the Pauli label at its first nonzero site through
  `X -> Y -> Z -> X`; the required weight-one generator is the phase-free difference between the
  old and new labels. It anticommutes with the source grade, so the collective commutator squares to
  exactly `4I` there. First-site rotation is a permutation of all nonzero grades, so selected images
  from distinct grades cannot overlap. Thus every invariant subspace supported on nonzero Pauli
  characters satisfies Hall expansion using weight-one generators alone. Exact statement and proof
  are in `../3-formalized/pauli-character-first-defect-selector-law.md`. Hostile audit prevents an
  overclaim: the zero Pauli-character grade strictly contains the sitewise `SU(2)` singlet algebra,
  and its anisotropic sector plus edge-image overlap remain the exact two-replica gate.
- 2026-08-04 -- Formalized arbitrary-register Pauli covariance and the first-defect selector core.
  `PauliCharacterFirstDefectSelector.lean` proves first-active rotation is a permutation of all
  nonzero global Pauli characters, constructs its exactly weight-one selected axis, and proves source
  anticommutation. `FinitePauliConjugationLaw.lean` proves exact product-sign conjugation for arbitrary
  finite Pauli strings. `TwoReplicaGlobalPauliHallSymmetryReduction.lean` then proves paired strings
  commute, every weight-at-most-`q` collective commutator is covariant by its exact character, and the
  canonical greatest maximum-defect subspace of the global family is invariant under every paired
  Pauli string. Targeted compilation and axiom audits pass with only `propext`, `Classical.choice`,
  and `Quot.sound`. The next formal gate is finite simultaneous character resolution and injective
  graded assembly; the scientific gate after it remains zero-character anisotropy/edge overlap.
- 2026-08-04 -- Closed finite simultaneous parity resolution. For any finite commuting list of
  involutions, every invariant subspace is exactly the sum of its simultaneous parity pieces and its
  finrank is the exact sum of the piece finranks. The global Pauli module instantiates this for every
  finite list of paired Pauli strings acting on the canonical weight-at-most-`q` maximum-defect
  subspace. Formal capstones are
  `invariantSubspace_eq_simultaneousParityPieces_sup`,
  `invariantSubspace_finrank_eq_simultaneousParityPieces_sum`,
  `finiteTwoReplicaQLocal_greatestMaximizer_eq_simultaneousParityPieces`, and
  `finiteTwoReplicaQLocal_greatestMaximizer_finrank_parityPieces`; targeted compilation and axiom
  audits pass with only `propext`, `Classical.choice`, and `Quot.sound`. The remaining formal gate is
  injective assembly of first-defect-selected outputs; the remaining scientific gate is the
  zero-character anisotropic/edge overlap.
- 2026-08-04 -- Refreshed the two publication-ready entries written after the previous corpus
  audit. `real-corona-isotropy-clifford-transgression-law` supplies an exact one-involution
  fixed/free atomic split and an even/odd smoothness--detectability allocation. This supports the
  representation choice “nonzero Pauli characters versus the fixed zero character,” but it proves
  no all-subspaces rank inequality and therefore contributes no Hall estimate. Its registry card
  is also internally stale: the opening universal Chern-character statement and gates remain
  marked conjectural/open while the terminal log records final closure, so no unresolved claim from
  that card is imported here. `stokes-cartan-lorentz-capacity-law` proves a genuine one-defect
  Schur-complement law, but its capacity is the scalar inertia wall
  `c^(-1)-lambda`, not Hall capacity `dim(sum_j A_j U)-dim U`; it supplies no selector or overlap
  bound. Neither new entry changes O4's open core.
- 2026-08-04 -- Closed the literal nonzero-character Hall channel in Lean. The simultaneous
  paired-Pauli character spaces are proved `iSupIndep`: distinct global Pauli words define distinct
  conjugation characters, and exact eigenspaces embed in the independent simultaneous generalized
  eigenspaces. `finiteTwoReplicaNonzeroPauliResolvedSubspace` is the direct sum of all nonzero
  character components contained in an arbitrary subspace. The capstone
  `finiteTwoReplicaNonzeroPauliResolvedSubspace_finrank_le_shadow` proves, without an invariance
  hypothesis, that this resolved subspace cannot shrink under the literal weight-one collective
  Pauli family. The proof assembles the first-defect inverse selector through collision-free target
  grades. Targeted elaboration passes; the capstone axiom audit uses only `propext`,
  `Classical.choice`, and `Quot.sound`. The nonzero channel is no longer open. Exact surviving
  two-replica gate: Hall expansion on the zero Pauli-character fixed algebra, including its local
  anisotropic diagonal-correlation component, plus reverse compensation for intersection of its
  edge images with already occupied nonzero target grades.
- 2026-08-04 -- Audited all six newly designated corpus surfaces before further proof work.
  `HTGeometry` contains direct reusable Hall machinery: central-Casimir scaling,
  resolved-fibre assembly, Pauli-character independence, exact local-singlet synchronization, and
  product-stabilizer operational locality witnesses. `HilbertMetric` supplies the bi-tight
  Parseval--Bessel law and exact adjoint-departure rigidity. `QuantumAlg` supplies the strict
  48-element one-qubit Clifford lift, doubled-commutant completeness, exact Casimir twirl, product
  Clifford tensor lift, and general Pauli symplectic Schur solver. These identify the local
  zero-character split into two Clifford-fixed directions and anisotropic nonsinglet directions.
  `QECLean` supplies exact binary-symplectic Pauli parity, commutation, centralizer, support, and
  logical-action bridges, but no matrix doubled-commutant or all-subspaces Hall theorem; concrete
  code endpoints using `native_decide` are excluded from standard-axiom capstones. `RHTower`
  supplies already-used recurrence, completed-time Choi plateau, syndetic hard-time, causal-horizon,
  and Clifford multiplicity mechanisms, but no zero-character Hall closure. `PNTPlus.lean` is an
  umbrella for PNT/sieve/Mellin modules and supplies no direct two-replica rank mechanism.
- 2026-08-04 -- Found and proved the correct mixed-layer mechanism. Full forward-image overlap need
  not be repaid. Let `F` record edge outputs modulo nonsinglet input. Its range pays visible singlet
  directions. For `s in ker F`, every edge image already lies in nonsinglet input, so applying the
  same generator again places `K_2 s=sum_p A_p^2 s` in total output. Edge synchronization makes
  `K_2` injective on the singlet layer after quotienting global identity and global swap. Visible
  range lies in nonsinglet layer and recovered kernel lies in singlet layer, hence their dimensions
  add and rank-nullity closes mixed Hall. Dependency-closed proof is in
  `../3-formalized/visible-kernel-recovery-hall-law.md`. Abstract capstone
  `visibleKernelRecovery_subspace_finrank` is formalized in
  `HTGeometry/VisibleKernelRecoveryHallExpansion.lean`. The same module formalizes quadratic return
  `linearFamilySquare`, proves hidden first images return inside one-step target shadow, and derives
  `quadraticHiddenKernelRecovery_subspace_finrank`. Targeted elaboration passes. Remaining
  Exact axiom audit of both recovery capstones contains only `propext`, `Classical.choice`, and
  `Quot.sound`. Remaining two-replica work is concrete construction of local-Casimir reducing split,
  graded quotient detector, and physical edge-Casimir restriction—not invention of another overlap
  inequality.
- 2026-08-04 -- Strengthened visible-kernel recovery to the exact physical interface.
  `visibleQuotientDetector_finrank` turns any injective assembly of detector range into actual output
  modulo occupied nonsinglet input into the required visible-rank inequality.
  `invariantSubspace_le_shadow_of_linearFamilySquare_injective` shows an invariant nonsinglet input
  is reproduced once its local quadratic Casimir is injective. The combined capstone
  `quadraticHiddenKernelRecovery_of_visibleQuotient` now leaves only task-specific representation
  bridges. Exact axiom audit of all five recovery capstones contains only `propext`,
  `Classical.choice`, and `Quot.sound`.
- 2026-08-04 -- Rejected an invalid design-order shortcut before it entered the paper. Doubled
  commutant completeness classifies fixed two-replica operators; it does not make every invariant
  subspace of the operator representation Lie-invariant. Using it that way would silently require
  fourth-moment control. The replacement is exact finite-group algebra.
  `TwoReplicaCliffordTwirlHallSymmetryReduction.lean` proves that every strict doubled Clifford gate
  normalizes the three collective Pauli commutators, hence fixes the canonical greatest Hall
  obstruction. Its uniform conjugation average is idempotent and has range exactly
  `span{identity, swap}`. Therefore every canonical obstruction splits into its identity/swap part
  and its exact zero-twirl part. The module transports all statements from QuantumAlg's `Fin 2`
  convention to the Boolean physical convention used by the edge-Casimir corpus. Ten capstone axiom
  audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-08-04 -- Isolated the correct no-differentiation Casimir mechanism for the product-local
  lift. For a collective Pauli commutator `B_(i,a)`, paired quarter-turn conjugation `C_(i,a)`, and
  paired-Pauli half-turn `J_(i,a)`, exact eigenvalue interpolation gives
  `B_(i,a)^2 = 6I - 4(C_(i,a)+C_(i,a)^(-1)) + 2J_(i,a)`. Thus the local quadratic Casimir lies in
  the finite Clifford group algebra and preserves every Clifford-invariant canonical obstruction.
  This identity replaces the rejected continuous-symmetry inference. Remaining concrete gates are
  its Lean proof, arbitrary-register product-Clifford covariance/twirl range, the graded quotient
  detector, and restriction of the already formalized connected-edge master Casimir to the global
  identity/swap quotient.
- 2026-08-05 -- Closed the concrete growing-replica central-Casimir bridge for every finite physical
  register and every finite replica register. `AllReplicaCollectivePauliCasimir.lean` proves exact
  Pauli structure constants, diagonal replica brackets, distinct-site commutation, literal
  vectorized operator action, Hermiticity, and centrality of the complete site/axis Casimir.
  `CentralCasimirCommonKernelCorrection.lean` then constructs the canonical orthogonal projector
  onto the simultaneous kernel and proves the unconditional mixed-subspace law
  `finrank U <= finrank V + finrank S_r`. This removes the earlier all-replica complement/gluing
  obligation for the weight-one family. Exact axiom audits use only `propext`, `Classical.choice`,
  and `Quot.sound`. The surviving frontier is sharply smaller but still substantive: one-step
  weight-two Hall inside `S_r`, with correction reduced from the full sitewise singlet sector to
  global replica-permutation modes. No cavity decay or Brown--Susskind time scale is claimed from
  the new algebra alone.
- 2026-08-05 -- Proved a universal positive-length replacement for any failed one-step Hall route.
  `LieGeneratedCentralHallExpansion.lean` constructs the Lie subalgebra of endomorphisms that both
  preserve a target `V` and send a source `U` into `V`. Consequently, if local generators preserve
  `V` and send `U` into `V`, every element of their Lie span also sends `U` into `V`. Composed with
  the exact common-kernel Casimir correction, any Lie-generated Hermitian central family satisfies
  `finrank U <= finrank V + finrank(common kernel)`. This is unconditional and requires neither
  one-step Hall nor a gap estimate. For the physical frontier it changes the exact remaining task:
  prove that weight-one/two replica commutators Lie-generate a full central family and bound that
  full family's common kernel by global replica permutations. This theorem alone does not prove the
  desired one-step cavity contraction; it supplies a rigorous block-orbit alternative whose depth
  cost must still be quantified.
- 2026-08-05 -- Closed both algebraic obligations left by the preceding block-orbit alternative.
  `AllReplicaTwoLocalPauliLieGeneration.lean` proves that the replicated commutator of every
  nonidentity full Pauli direction lies in the Lie span generated by physical weight-one/two Pauli
  directions, at every finite replica order. `FiniteReplicaCollectiveCommutantExact.lean` proves in
  the stable range `r <= 2^n` that the full collective commutant is exactly the `r!`-dimensional span
  of replica-position permutations. `FiniteReplicaCollectiveCommutantUniversalBound.lean` gives the
  unconditional all-`r` bound `(2^n)^r r!`. Consequently
  `finiteReplicaTwoLocalPauli_subspace_finrank_le_add_factorial` proves the exact block-orbit Hall
  defect `dim U <= dim V + r!` whenever the physical local directions send `U` into an invariant
  target `V`. This is the first dependency-closed all-replica local-to-full-algebra transfer with no
  unidentified singlet sector. It still does not prove one-step Hall for the non-invariant shadow
  `V=span{A_p U}`, so it does not imply quenched word-metric injectivity or the Brown--Susskind
  growth time scale.
- 2026-08-05 -- Closed the same-Hamiltonian recurrence/plateau/locality conjunction for the ordinary
  fixed-`q` Pauli ensemble. `PauliBoundedHamiltonianLocalityLaw.lean` proves that the polynomial
  spectral-genericity family is literally self-adjoint and Pauli-`q`-local in the operational basis,
  and that maximal projective spectrum forces a nonzero Hamiltonian on every nonempty register.
  `StaticQLocalComplexityHaarSeparationLaw.lean` then proves for every generic coefficient vector:
  after every start time, a near-identity Choi epoch is followed by an epoch separated in trace
  distance from every word in the stated finite circuit dictionary and then by another near-identity
  epoch, with uniformly bounded gaps; simultaneously, at every real time, the same Hamiltonian's
  product-stabilizer two-query signal is strictly above the exact Haar benchmark whenever
  `M_q 3^q < 2^n+1`. Standard-axiom audit passes. This closes O2, the Choi form of O3, and the
  concrete same-system O6 bridge. It does not supply the missing quantitative first-hard-time bound,
  monotone initial growth ramp, or matching first low-complexity recurrence scale.
- 2026-08-05 -- Quantified the all-replica local-algebra transfer at linear physical word depth.
  `FiniteReplicaTwoLocalPauliWordHall.lean` proves constructively that every replicated full-Pauli
  commutator of physical weight `w` lies in the `w`th associative power of the span of identity and
  physical weight-one/two replicated commutators. Since `w <= n`, every source subspace expands
  after at most `n` local factors modulo only the exact full collective commutant. The stable-range
  defect is exactly bounded by `r!`; the unconditional all-order defect is bounded by
  `(2^n)^r r!`. Targeted elaboration and capstone axiom audits pass with only `propext`,
  `Classical.choice`, and `Quot.sound`. This closes the previously unquantified local-word-depth
  gate without any invariant-target hypothesis. It does not yet prove O4: a rank inequality for
  `S^n U` supplies no selector-aware small-ball estimate for the nonlinear aggregate shortcut
  locus. The live frontier is now the conversion from growing-replica word expansion to quenched
  anti-concentration strong enough to survive the complete circuit union.
- 2026-08-05 -- Hostile review falsified any direct Hall/rank-to-complexity inference.
  `OneLocalPauliWordLinearUniversalityNoGo.lean` proves that every full Pauli basis matrix is a
  product of at most `n` physical one-local Pauli gates; therefore length-`n` local words already
  linearly span the entire `2^n`-dimensional operator algebra. Targeted elaboration and capstone
  axiom audit pass with only `propext`, `Classical.choice`, and `Quot.sound`. Hence maximal linear
  span, Lie generation, all-replica rank, and Hall expansion can coexist with uniformly linear
  circuit length. The new `n`-step Hall theorem remains valid representation-theoretic
  infrastructure but cannot be cited as O4 anti-concentration. The surviving frontier is
  irreducibly nonlinear: robust word-metric injectivity or selector-aware annular shortcut packing.
- 2026-08-05 -- Proved the fast-forwardable-stratum codimension obstruction on paper. Every
  `f`-dimensional coefficient stratum with a radial-independent synthesis bound `B` creates a
  fixed-radius annular shortcut tube of volume `Omega(R^f)` and Gaussian shortcut probability
  `Omega(t^{-(m-f)})`. A commuting involution sector supplies the same exponent through an exact
  recurrence lattice. For the fixed-`q` Pauli family this gives the unconditional ceiling
  `kappa <= m-sum_(k=1)^q binom(n,k)` on every proposed no-shortcut exponent. Full proof and hostile
  audit are in `../3-formalized/fast-forwardable-stratum-codimension-obstruction.md`. No Lean claim
  is made yet.
- 2026-08-05 -- Froze the autonomous shortcut-organization conjecture after killing chaos and raw
  dynamical-Lie-algebra dimension as candidate invariants. The proposed law is
  `kappa_*=m-f_*`, where `f_*` is the largest radial dimension of an independently certified uniform
  synthesis stratum. The forced inequality is proved; the exact open inverse says excess shortcut
  packing must organize into a higher-dimensional synthesis stratum. Papas's weak Ax--Schanuel
  theorem for `GL_D` reveals the same obstruction independently: its restrictions are needed because
  the matrix exponential has non-discrete, positive-dimensional identity fibres, and the remaining
  type-II recurrence strata obstruct a full theorem. This identifies the missing new mathematics as
  a quantitative approximate matrix-exponential unlikely-intersection theorem with growing
  state-circuit targets, translated components, and a selector-surviving architecture union.
- 2026-08-05 -- Audited GitHub Lean infrastructure instead of assuming all missing libraries must be
  built locally. `dududuguo/HighDimProb` is the only strong clean candidate: Apache-2.0, no forbidden
  proof placeholders found, and useful Gaussian concentration, covering/packing, Dudley,
  Hanson--Wright, and matrix Bernstein modules; it needs a Lean 4.29.1-to-4.32.2 port. `physlib` and
  `weingarten-lean` contain narrower reusable pieces but do not close O4. Searches found no genuine
  Lean Pila--Wilkie, Ax--Schanuel, o-minimal cell-decomposition, effective Lojasiewicz, quantum
  fast-forwarding, or unitary-circuit-variety library: apparent hits only package the desired theorem
  as input evidence. No dependency was added before a complete paper proof.
- 2026-08-05 -- Conjecture-protocol attack killed the frozen scalar law `kappa=m-f_*` as a universal
  representation. At fixed `n`, compactness and a finite epsilon-circuit net eventually make every
  radial endpoint easy, so an unspecified `R->infinity` exponent is ill-typed; different admissible
  `(n,R)` paths need a uniform finite-size statement. More decisively, a `d`-dimensional continuous
  synthesis carrier translated by a transverse rank-`r` period lattice creates annular shortcut
  volume `Omega(R^(d+r))` and Gaussian mass `Omega(t^(-(m-d-r)))`. The dependency-closed proof is in
  `../3-formalized/mixed-periodic-synthesis-carrier-obstruction.md`. Continuous dimension and
  discrete recurrence rank are independent additive contributions; architecture proliferation is a
  third contribution, not a nuisance constant.
- 2026-08-05 -- Found a stronger state-specific obstruction missed by the commuting-sector analysis.
  For any coefficient family, the real rank `v_Phi` of
  `x |-> (I-|Phi><Phi|)H(x)Phi` is the number of coefficient directions visible to the initial
  projective ray. Its kernel has dimension `m-v_Phi`; every Hamiltonian in that noncommuting kernel
  fixes the ray exactly and hence has zero state complexity. Therefore every state-complexity escape
  exponent obeys `kappa<=v_Phi`. For the full weight-at-most-`q` qubit Pauli space and every product
  input, the rank is exactly `2 sum_(k=1)^q binom(n,k)`, so this observer-stationary ceiling is
  `kappa<=2 sum_(k=1)^q binom(n,k)=(2/3^q)m+O(n^(q-1))`. Full proof is in
  `../2-fully-proven/observer-visible-local-time-dimension-obstruction.md`. This connects the corpus's
  prior observer-generated spectral-time laws to the static-complexity frontier without identifying
  the two notions: the earlier law measures visible energy-gap rank after fixing `H`; the new rank
  measures the projective action of an entire Hamiltonian coefficient family before evolution.
- 2026-08-05 -- Froze the stronger replacement conjecture in
  `autonomous-shortcut-free-energy-law.md`. A certified shortcut format has continuous carrier
  dimension `d`, polynomial component-growth/recurrence entropy exponent `h`, and free codimension
  `g=(m-d-h)_+`. The conjectural universal law is
  `kappa_*=inf_formats g+o(m)`: transverse tuning is the energy cost, while recurrence and component
  multiplicity are the entropy refund. It reproduces every proved shadow—observer-stationary
  carriers, continuous fast-forwarding, recurrence lattices, mixed carriers, and fully easy one-local
  dynamics—without defining the invariant from minimal circuit complexity. The exact open inverse is
  that the full Hamiltonian-dependent circuit union cannot beat all certified energy-entropy formats
  unless it organizes into a new format. For fixed `q>=2` Pauli dynamics from a product input, the
  sharper competing prediction is that the observer-stationary carrier minimizes free codimension,
  giving `kappa_*=2 sum_(k<=q) binom(n,k)+o(m)`. Current verdict:
  `SURVIVES PRELIMINARY ATTACK`; no upper law or Nature-level result is claimed.
- 2026-08-05 -- The next hostile pass killed that shortcut-free-energy card as
  an exact conjecture.  Its “certified format,” compiler class, overlap law,
  pre-capacity window, and scale errors were not mathematically fixed; making
  the class broad enough to contain an arbitrary circuit selector makes the
  inverse circular, while restricting it to known affine/periodic carriers
  makes it nonuniversal.  Raw circuit-language entropy also grows
  exponentially in word length and cannot be represented by one fixed
  polynomial component exponent without trivializing the formula.  The mixed
  carrier energy--entropy lower obstruction survives, but no inverse
  classification is claimed.  Relentless interrogation produced a sharper,
  exact flagship conjecture in `observer-rank-autonomous-no-shortcut-law.md`:
  for the full fixed-`q>=2` Gaussian Pauli ensemble and product input, the
  complete Hamiltonian-dependent shortcut probability has logarithmic
  exponent
  `v_(n,q)=2 sum_(k<=q) binom(n,k)`, the projective QFI rank, uniformly through
  an explicit polynomial-to-exponential pre-capacity window.  The stationary
  kernel proves the matching forced side up to `o(v)`; the selector-aware
  upper side is the exact open core.  This replacement removes all prose
  carrier categories and can be falsified by one larger aggregate shortcut
  family.
- 2026-08-05 -- The first direct attack on the observer-rank conjecture closed
  the entire fixed-block competitor class.  If a coefficient subspace `U`
  sends the observer action into a fixed real channel `K`, then exact
  rank-nullity gives
  `dim U <= m-v_Phi+dim K`, with the sharp preimage identity
  `dim T_Phi^(-1)(K)=m-v_Phi+dim(K intersect range T_Phi)`.  Hence Hamiltonians
  preserving a fixed complex `d`-dimensional easy block containing the input
  occupy coefficient dimension at most `m-v_Phi+2(d-1)`.  Bounded or
  `o(n^q)` block diagonalizations cannot beat the stationary-kernel exponent
  at leading order for the full fixed-`q` Pauli family.  The abstract theorem,
  QFI Gram/rank identity, and coefficient-kernel/eigenvector equivalence are
  axiom-clean Lean theorems in
  `HTGeometry/ObserverVisibleLocalTimeDimension.lean`.  This does not cover
  moving blocks, quadratic/Gaussian state manifolds, recurrence-component
  entropy, or the arbitrary circuit selector; those are the next hostile
  competitors.
- 2026-08-05 -- The next conjecture-protocol pass used the RHTower corpus's
  successful exceptional-carrier pattern: a cancelled direction cannot be
  discarded; it must be proved structurally harmless or charged to a
  transverse defect.  This closed all pairwise-commuting Pauli carriers.  On
  each exact support `S`, binary symplectic nondegeneracy bounds a commuting
  nonidentity fibre by `2^|S|-1`; summing gives
  `r <= sum_(k<=q)(2^k-1)binom(n,k)` and therefore
  `m-r >= v_(n,q)`.  The complete theorem, binomial identity, and
  observer-rank comparison are formalized and axiom-audited in
  `HTGeometry/CommutingPauliObserverRankDominance.lean`.  The remaining
  structured threat requires genuinely noncommuting cancellation in the
  observer-stationary kernel.
- 2026-08-05 -- Froze the wider conjectural interpretation in
  `observer-spectral-shortcut-action-law.md`.  Proposed shortcut action is
  the minimum of local observer information `v_(n,q) log t` and the exact
  completed spectral-orbit shortcut information of the circuit-easy target.
  Observer-rank growth, finite-capacity plateau, and recurrence are then three
  regimes of one information law rather than pasted results.  This is a wild
  conjecture, not a paper claim.  Its first open core is a selector-uniform
  exceptional-carrier dichotomy proving that mixed resonance must pay either
  observer codimension or global target information.
- 2026-08-05 -- Immediate hostile attack rejected Fubini--Study target mass as
  the spectral branch of that conjecture: a fixed-locality endpoint ensemble
  has only polynomially many coefficient parameters, and no unconditional
  ensemble-transfer theorem makes its circuit-target mass Fubini--Study.
  The repaired law uses exact Haar mass on each Hamiltonian's completed
  projective spectral phase closure, averaged over the same Gaussian
  ensemble.  Fubini--Study rate--distortion is retained only as a separately
  named delocalization/comparison theorem required for the strongest plateau
  interpretation.
- 2026-08-05 -- Falsified the observer-rank aggregate shortcut law on every
  exponential-time window. A full-dimensional coefficient box of width
  `epsilon^2/(16m)` around the diagonal fixed-`q` Hamiltonian
  `m^(-1/2) sum_(empty!=S, |S|<=q) Z_S` has Gaussian mass
  `exp(-O_q(n^q log n))`. The product input is its unique top eigenline with
  gap at least `2/sqrt(m)`; a self-contained eigenbasis argument proves every
  Hamiltonian in the box has a nearby eigenline, so the entire orbit remains
  `epsilon`-easy at every time. At `t=2^(cn)` this floor is exponentially
  larger than the conjectured `t^(-(1-eta)v)=exp(-Omega_q(n^(q+1)))`.
  Exact proof is in
  `../3-formalized/gapped-eigenstate-uniform-shortcut-floor.md`. This does
  not falsify the observer--spectral minimum: its annealed completed-orbit
  mass absorbs the box and therefore crosses branches by polynomial time.
  Typical Brown--Susskind target must now be quenched/quantile-resolved,
  charging Hamiltonian rarity separately from conditional orbit ease.
- 2026-08-05 -- Froze the exact quenched replacement after the gapped-eigenline
  falsification. `quenched-observer-spectral-action-law.md` conditions the
  fixed-time shortcut event on each Hamiltonian's own completed circuit-target
  information and conjectures
  `P(shortcut and I_J^comp>=B) <= exp(-(1-eta) min(v log t,B))`.
  The rare full-dimensional easy box now lies in the `I_J^comp=0` stratum and
  is charged explicitly instead of corrupting a typical-growth average. Small
  Hamiltonians cost `t^-m`, stationary-kernel tubes sharply cost `t^-v`, and
  commuting/anticommuting carriers cost at least `t^-v`; none kills the new
  statement. The first exact falsifier remains a codimension-`<v` nonlinear
  near-integrable carrier whose exact orbit is easy but whose arbitrarily
  small transverse perturbations have completed information at least `B`.
  No Lean work is authorized until this resolved exceptional-carrier open core
  has a dependency-closed paper proof.
- 2026-08-06 -- Closed a strictly stronger adaptive finite-window shortcut
  theorem in `../3-formalized/direct-net-adaptive-static-choi-shortcut-action-law.md`.
  Direct overlap with each arbitrary full-Choi target removes the orbit-anchor
  triangle loss: every capture radius below one is allowed, and maximal
  projective rank bounds each order-`r` target collision by `r! d^(-r)`.
  Finite circuit words pay their exact padded-word entropy.  An arbitrary,
  even uncountable, time-adaptive target class pays only any supplied finite
  metric-net cardinality; selector measurability is unnecessary.  Gaussian
  and uniform time-window laws are Lean-proved and axiom-audited.  This closes
  target resolution and continuous-family selector removal for the
  finite-window branch.  It does not close O4: intrinsic replica action
  resolution can collapse with size/order, and no fixed-time quenched
  coefficient-space anti-concentration follows.
- 2026-08-06 -- Replaced the finite-window branch's global minimum-action
  bottleneck by a formally proved local crowding invariant. At replica order
  `r` and resolution `delta`, let `kappa_r(delta)` be the maximum number of
  distinct replica multiplicity vectors whose energy sum lies within
  `delta` of one fixed vector. A symmetric weighted Schur estimate proves
  that all unresolved nonzero actions carry mass at most `kappa_r(delta)`
  times the exact permutation floor. Consequently every adaptive padded
  circuit dictionary obeys the Gaussian shortcut bound
  `|gate|^(s+1) * ((1+kappa_r(delta))*r!*d^(-r)
  + exp(-(T*delta)^2/2))`, with the uniform-window sinc analogue. The result
  is Lean-proved in `HTGeometry/ReplicaActionCrowdingShortcutLaw.lean` and
  `RHTower/DirectAdaptiveStaticChoiCrowdingLaw.lean`; it needs no smallest
  spectral gap, and an isolated arbitrarily small replica action costs only
  one floor unit. This is a real strengthening of the adaptive circuit law,
  not closure of O4. The exact surviving finite-window frontier is now a
  local-Hamiltonian bound on `kappa_r(delta)` at circuit-union replica order;
  the fixed-time quenched coefficient-space frontier remains separate.
- 2026-08-06 -- Classified replica-action crowding by a formally proved
  finite-window spectral dimension.  For every crowding fibre, translate
  multiplicities to balanced integer characters and let `s` be their rational
  span rank.  An injective coordinate minor gives the exact universal count
  `|Q_p(delta)| <= (2r+1)^s`; a basis of exactly `s` near characters obeys
  `|exp(i t <k,E>)-1| <= |t| delta`.  Hence adaptive padded-circuit shortcut
  probability is bounded by circuit entropy times the collision floor with
  crowding factor `(2r+1)^s`, plus the Gaussian or uniform window remainder.
  Lean modules:
  `HTGeometry/ReplicaCrowdingSpectralDimensionLaw.lean` and
  `RHTower/DirectAdaptiveStaticChoiSpectralDimensionLaw.lean`; card:
  `../3-formalized/replica-crowding-spectral-dimension-dichotomy.md`.
  Hostile verdict: genuine structural strengthening, but still not O4 or the
  Brown--Susskind law.  Missing theorem must convert low resolved spectral
  dimension into a quantitatively delayed/low-capacity complexity phase, or
  prove that local Hamiltonian ensembles avoid this branch at growing replica
  order.  Fixed-time quenched coefficient anti-concentration remains separate.
- 2026-08-06 -- Converted the spectral-dimension occupation law into an
  explicit future hard-time theorem.  If circuit entropy times the rank-form
  replica floor and uniform-window remainder is below `(1-epsilon^2)^r`, some
  `t in (0,2T]` misses every supplied depth-`s` Choi target.  Exact diagonal
  phase translation removes the centered-window and inverse-closed-gate
  loopholes while preserving norms and pure-state trace distance.  The
  ordinary bounded-weight Pauli capstone proves, for the same generic static
  `q`-local Hamiltonian, this future circuit-hard endpoint and strict
  product-stabilizer two-query separation from the Haar benchmark at every
  real time.  Lean modules:
  `RHTower/StaticChoiForwardSpectralDimensionLaw.lean` and
  `RHTower/StaticQLocalForwardComplexityHaarSeparationLaw.lean`.
  This quantitatively connects O3 and O6 but does not close Brown--Susskind
  timing: the live input is an ensemble-scale bound on
  `replicaNearActionRank(E,r,delta)` at growing `r`, or a sharper weighted
  crowding invariant that survives circuit entropy.
- 2026-08-06 -- Removed the remaining worst-spectrum minimax loss from the
  finite-window theorem.  `DirectAdaptiveStaticChoiWeightedCrowdingLaw.lean`
  retains each target's exact diagonal-weight near-action mass and sums it
  only after the adaptive circuit union.  The resulting resonance partition
  `Z_r(C;E,delta)` gives
  `(1-epsilon^2)^r P_shortcut <= |C|[r!d^-r+window]+Z_r`.
  It is formally bounded by the prior degree-floor term and hence by the
  spectral-rank term, so this is a genuine strengthening, not a renamed
  invariant.  `StaticChoiForwardWeightedCrowdingLaw.lean` proves exact phase-
  shift invariance of `Z_r` and a future hard endpoint in `(0,2T]` whenever
  the weighted budget closes.  The bounded-weight Pauli same-Hamiltonian
  capstone now pairs this stronger future-hardness certificate with permanent
  strict separation from Haar by the local two-query witness.  Remaining
  Brown--Susskind frontier: bound `Z_r` (or its ensemble quantiles) at growing
  replica order for ordinary local Hamiltonians, then extract the physical
  cut/plateau scale and matching low-complexity recurrence time.
- 2026-08-07 -- Retired the proposed raw observer-Jacobian pseudodeterminant
  lower tail by an exact replica-compensation theorem.  Uniform reporter
  duplication multiplies a rank-`v` Gram determinant by `k^v` without changing
  any matched event.  More decisively, physical iid pure-state replication
  multiplies the projective Gram by `r`, while tensor fidelity and its matched
  threshold both acquire the same `r`th power.  Thus the normalized determinant
  lower-tail probability and the complete matched target-union event are
  pointwise replica-invariant under every source law and every target type.
  Lean modules:
  `HTGeometry/ReplicaObserverJacobianCompensationLaw.lean` and
  `HTGeometry/PureStateReplicaProjectiveGramLaw.lean`; card:
  `../3-formalized/replica-observer-jacobian-compensation-law.md`.
  This is a no-go for the designated invariant, not O4 closure.  The surviving
  fixed-time frontier is a quenched bound on intrinsic, incidence-normalized
  coarea mass of the complete circuit tube after return removal; unlike a raw
  pointwise determinant, it must retain fibre-sheet multiplicity and occupied
  endpoint image.
- 2026-08-07 -- Closed the representation part of the incidence-normalized
  coarea frontier.  For the occupied return-removed replica span `S_r`, its
  Hilbert number `h_r`, and the quenched covariance `C_r` compressed to that
  span, the full approximate shortcut event satisfies the Lean-proved law
  `a^(2r) P(E_a)^2 <= h_r ||C_r||_HS^2`.  Source coefficient sheets remain
  inside the covariance integrals, while arbitrary target relabeling,
  duplicate circuit words, and exact-return zero residuals leave the bound
  invariant.  No targetwise probability union occurs.  Module:
  `HTGeometry/QuenchedReplicaIncidenceCovarianceLaw.lean`; card:
  `../3-formalized/quenched-replica-incidence-covariance-law.md`.  This is not
  O4 closure.  Exact remaining local-physics theorem is growing-replica decay
  of this one compressed covariance collision for the ordinary fixed-`q`
  Gaussian static ensemble, against occupied circuit-image Hilbert growth.
- 2026-08-07 -- Exposed that collision as an exact occupied-image pair action.
  If `k_r(x,y)` is the squared overlap of the two replica endpoints after
  projection to the occupied return-removed circuit image, then
  `||C_r||_HS^2 = integral integral k_r`.  Every measurable recurrence-pair
  relation `R` gives the exact one-time split into its `R` and `R^c` masses,
  and complete shortcut capture obeys
  `a^(2r) P(E_a)^2 <= h_r (integral_R k_r + integral_(R^c) k_r)`.
  This retains source fibre-sheet multiplicity and occupied endpoint image;
  duplicates and exact-return zero residuals remain invisible.  Global frame
  potential is retired as too lossy because it restores all source
  self-collisions.  Module:
  `HTGeometry/QuenchedReplicaPairIncidenceLaw.lean`; card:
  `../3-formalized/quenched-replica-pair-incidence-cut-law.md`.  Remaining
  physical core: choose the local-Hamiltonian recurrence relation and prove
  growing-replica decay of the compressed kernel on its complement.
- 2026-08-07 -- Strengthened exact-return zero removal to quantitative
  approximate-return removal.  Return-removed targets are grouped by residual
  squared-radius `rho_b`; each shell enters one complete occupied-image
  reporter with weight `rho_b^r`.  The resulting Lean-proved quenched law is
  `a^r P(E_a) <= integral sum_b rho_b^r q_(b,r)`.  It retains every source
  fibre sheet, ignores duplicate circuit labels inside each shell, and gives
  exact returns zero contribution.  Static-Choi Pythagoras identifies the
  exact radius as `1 - |<Phi_H(u),phi>|^2`.  Modules:
  `HTGeometry/ReplicaReturnShellCoareaIncidenceLaw.lean` and
  `RHTower/StaticChoiReturnShellCoareaIncidenceLaw.lean`; card:
  `../3-formalized/return-shell-replica-coarea-incidence-law.md`.  This does
  not close O4: genuinely transverse radius-one shells still require the
  ordinary-local-Hamiltonian compressed-kernel estimate.
- 2026-08-07 -- Removed the remaining return/nonreturn cross-pair
  contamination from the incidence-normalized coarea frontier.  For every
  independently fixed measurable source return set `R`, restrict the quenched
  measure to `R^c` before forming the occupied-image covariance.  Complete
  shortcut mass now obeys the Lean-proved scalar law
  `P(E_a) <= P(R) + a^(-r) sqrt(h_r A_(r,Z)(mu;R))`, where
  `A_(r,Z)(mu;R) = integral_(R^c x R^c) k_(r,Z)`.  Thus return mass is paid
  once with coefficient one; every pair left for anti-concentration has two
  off-return endpoints.  Source fibre sheets, complete occupied target image,
  duplicate invariance, and exact-return zero invariance are retained.
  Arbitrary optimization over `R` was explicitly rejected as circular because
  `R = E_a` trivializes the action; the return filtration must be fixed by a
  target-independent physical recurrence observable.  Module:
  `HTGeometry/QuenchedReplicaReturnExcisionLaw.lean`; card:
  `../3-formalized/return-excised-replica-coarea-incidence-law.md`.  Exact
  remaining local-physics core is now genuinely off return: choose a physical
  return level with small `P(R)` and prove growing-replica decay of
  `A_(r,Z)(mu;R)` for the ordinary fixed-`q` Gaussian static ensemble strongly
  enough to beat `h_r`.
- 2026-08-08 -- Replaced the projection-collision endpoint by a maximal-volume
  skeleton of actual occupied circuit endpoints.  Physical pair-fidelity
  domination of the compressed kernel was falsified: orthogonal vectors can
  have parallel projections.  The positive survivor selects `h_r` occupied
  replica targets by maximal determinant; Cramer's rule gives coefficient
  norm at most one for every other occupied target.  Lean now proves, after
  independently fixed return excision,
  `P(E_a) <= P(R) + h_r a^(-r) sum_(j<=h_r) M_r(z_j)` and the uniform form
  `P(E_a) <= P(R) + h_r^2 a^(-r) M_r`.  No circuit-description union or
  compressed pair cancellation remains; every `M_r(z_j)` is a genuine
  fixed-endpoint replica moment over the original restricted source measure,
  retaining every fibre sheet.  Module:
  `HTGeometry/MaximalVolumeReplicaTargetSkeletonLaw.lean`; card:
  `../3-formalized/maximal-volume-replica-target-skeleton-law.md`.  Classical
  max-volume/Cramer linear algebra is not claimed novel.  Exact remaining
  ordinary-local-Hamiltonian core is now targetwise and quantitative: prove a
  growing-replica ceiling on each selected physical endpoint moment strong
  enough to beat `h_r^2`, together with a small independent return tail.
- 2026-08-08 -- Removed a genuine overcount from the return-excised quenched
  coarea law.  After fixing target-independent return set `R`, let `U_R` be
  span of occupied-target projections of all surviving source replicas and
  `iota_R = dim U_R`.  Lean now proves `U_R` is unique least exact reporter,
  `iota_R <= h_r`, and, without changing off-return pair action `A_R`,
  `P(E_a) <= P(R) + a^(-r) sqrt(iota_R A_R)`.  Source space is not
  quotiented: fibre-sheet multiplicity and occupied endpoint image remain in
  original double-source integral.  Factor `iota_R` is universally sharp by
  uniform orthogonal-sheet example; any smaller universal coefficient fails.
  Duplicate labels and positive-order exact-zero residuals leave carrier and
  rank unchanged.  Module:
  `HTGeometry/ReturnExcisedMinimalIncidenceRankLaw.lean`; card:
  `../3-formalized/return-excised-minimal-incidence-rank-law.md`.  This does
  not close ordinary-local-Hamiltonian frontier: remaining hard theorem is
  growing-replica decay of unchanged `A_R`, now required only against exact
  surviving source--target incidence rank `iota_R`, not full target rank.
- 2026-08-08 -- Closed the dimension loss in complete endpoint incidence by
  replacing maximal-volume basis selection with one determinant-optimal
  probability design `lambda` on actual occupied replica endpoints.  A
  dependency-closed paper proof gives every endpoint design leverage at most occupied Hilbert number
  `h_r`, hence, after any independently fixed measurable return excision,
  `a^r P_(R^c)(E_a) <= h_r sum_z lambda_z M_r(z;R)` and
  `P(E_a) <= P(R) + h_r a^(-r) sum_z lambda_z M_r(z;R)`.  Under a uniform
  fixed-endpoint ceiling this costs `h_r`, improving the previous `h_r^2`.
  Weights live on physical occupied endpoints; all integrals remain on the
  original restricted source measure, so repeated fibre sheets retain full
  multiplicity.  An orthonormal endpoint family proves no universal
  probability-design coefficient below `h_r` is possible.  Classical
  D/G-optimal equivalence supplies the finite design mechanism; new frontier
  advance candidate is its exact composition with growing replicas, complete endpoint
  capture, and source-first return excision.  Lean formalization is open; card:
  `../2-fully-proven/return-excised-optimal-design-coarea-law.md`.  This closes on paper
  the complete-circuit-union geometry, not Brown--Susskind O4: remaining
  ordinary-local-Hamiltonian theorem is a quenched growing-replica ceiling on
  the resulting design-averaged fixed-endpoint moment strong enough to beat
  `h_r`, plus a small independent return tail.
- 2026-08-08 -- Proved that missing growing-replica ceiling on the completed
  spectral phase orbit for an ordinary bounded-degree static-local ensemble.
  For a fixed Hamiltonian/input with spectral collision
  `C_H = sum_j p_j^2`, remove once the common heavy spectral sector
  `{p_j > 4C_H/a}`.  Its norm is at most `sqrt(a)/2`; every surviving target
  capture therefore forces light overlap at least `sqrt(a)/2`.  Exact
  general-tensor Steinhaus orthogonality, projection into the least surviving
  light-source incidence carrier, and one projected-endpoint optimal design then give the
  return-excised, complete-incidence law
  `m_H(Q) <= m_H(R) + iota_(r,R)^L r! (16 C_H/a^2)^r`,
  where `Q\R` is the return-removed residual capture event and
  `iota_(r,R)^L <= h_r` is the exact minimal surviving source--target rank.
  Phase-source integration is never quotiented, so all fibre sheets remain;
  circuit duplicates and exact-zero residuals change neither `h_r` nor
  `iota_(r,R)^L`; `R` is
  paid once.  For the support-isotropic Gaussian Pauli ensemble on any graph
  containing a spanning path, product-local-Clifford invariance and the exact
  six-state one-qubit 2-design imply
  `E_H C_H(|0^n>) <= (2/3)^n`, hence
  `P{C_H > L(2/3)^n} <= 1/L`.  Generic path-local spectral maximality and a
  nonzero Krylov witness transfer the phase law to quenched physical-time
  density for almost every one fixed Hamiltonian.  Optimizing
  `r = floor((1-epsilon^2)^2 (3/2)^n/(32L))` yields a fixed-product-input
  completed-time plateau of approximate circuit depth
  `Omega((3/2)^n/(L log n))`, outside return density plus
  `exp(-Omega((3/2)^n/L))` time density.  This is the first theorem in this
  route giving an exponential state-complexity plateau for an ordinary
  nearest-neighbour static Gaussian spin Hamiltonian without eigenvector
  universality.  It does not close O4: projective equidistribution is
  non-effective, so first-hard-time, linear growth, plateau onset, and first
  recurrence scales remain open.  Paper proof and hostile audit:
  `../2-fully-proven/local-clifford-return-excised-phase-incidence-law.md`.
  Lean was deliberately not modified during the active corpus refactor.
- 2026-08-08 -- Converted the quenched completed-time plateau into the first
  common-fixed-time nonuniform endpoint lower bound on this route.  Restricting
  the Gaussian nearest-neighbour ensemble to a bounded coefficient box leaves
  probability at least `1/2` of Hamiltonians with completed easy-time density
  at most `eta_n=2^(-3r_n/4)`, where
  `r_n=Theta((3/2)^n)`.  Fatou and Tonelli then prove
  `liminf_(T->infinity) T^(-1) integral_0^T P_H{C_(2epsilon)(e^(-itH)Omega)>s_n}dt
  >= (1/2)(1-eta_n)` for
  `s_n=Omega((3/2)^n/log n)`.  Hence an unbounded sequence of deterministic
  times, common to the ensemble, has positive Gaussian mass of exponentially
  hard endpoints.  A uniform Duhamel margin on a bounded coefficient box
  moves one such common time to a rational time while retaining positive
  Hamiltonian mass.  Strict finite-word separation and coefficient continuity
  then yield bounded rational nearest-neighbour coefficients with the same
  exponential lower bound at error `epsilon`; exhaustive certified search
  selects one such pair for every `n`, so the witness family is uniformly
  computable.  This crosses existence of autonomous static-local exponential
  nonuniform state complexity, but not effective Brown--Susskind timing: no
  bound on first common time, coefficient/time bit length, or linear ramp is
  proved.  Paper proof and hostile audit:
  `../2-fully-proven/computable-static-local-exponential-state-complexity-law.md`.
  Lean remains deliberately untouched during corpus refactoring.
- 2026-08-08 -- Quantified the previously non-effective syndeticity constant
  for an algorithmically selectable static two-local Hamiltonian.  If an
  integer Hermitian `D`-level Hamiltonian has rationally independent
  projective frequencies and spectral norm at most `R`, then every relative
  phase cube of radius `rho` occupies at least
  `(rho/(2pi))^(D-1)/2` of every window of the explicit length
  `8(2N+1)^(D-1)(2(D-1)NR)^(D!-1)`, with
  `N=ceil((8pi(D-1)/(rho(rho/(2pi))^(D-1)))^2)`.  Proof:
  algebraic-integral field norm bounds every truncated spectral action;
  one product Fejer packet converts that bound into a shifted-window
  occupation law.  Minimum spectral gap is again falsified as the wrong
  invariant: spectrum `{0,1,2+eta}` has pairwise gap at least one but bounded
  action `2omega_1-omega_2=-eta`.  A birational positive-orthant map into a
  collision-good real box plus quantitative Hilbert irreducibility supplies
  a rational `S_(2^n)` full-two-local specialization there; scaling gives
  integer couplings.  The resulting fixed-product orbit has
  `Omega((3/2)^n/log n)` approximate state complexity for positive measure in
  every computably long window.  More strongly, applying the same arithmetic
  clock to the equal-weight Choi/thermofield-double orbit quantifies the open
  constant `L` in `universal-static-choi-complexity-plateau`: every long
  window has positive occupation at complexity
  `Omega(2^n/log n)`, and explicit recurrence--hardness--recurrence blocks
  repeat forever.  Qualitative Choi syndeticity and alternation were already
  formalized and are not claimed new; advance is the first explicit
  computable `L` for one selected integer static two-local Hamiltonian.  The
  deadline is catastrophically nonphysical (`D!` in the exponent), the
  Hamiltonian is all-to-all two-local with uncontrolled coefficient height,
  and no linear ramp or Brown--Susskind time scale follows.  Paper proof and
  hostile audit:
  `../2-fully-proven/arithmetic-static-local-hardness-recurrence-window-law.md`.
  Lean was read only and no build was run during corpus refactoring.
- 2026-08-08 -- Removed both random-time averaging and Gaussian radial scale
  mixing from the common-late-time plateau.  On the unit coefficient sphere
  of the full one-site plus nearest-neighbour two-site Pauli family, proved
  that no nonzero integer projective spectral action is constant on any open
  simple-spectrum patch.  New rigidity mechanism: strengthen the local path
  witness to a complete endpoint transition graph; if a zero-sum branch
  action obeyed `(sum_j c_j E_j)^2 = kappa D^(-1)Tr(H^2)`, a cross-block edge
  perturbation and two derivatives would give
  `L_0(z)L_xx(z,0)=kappa Q(V)`.  Unique old gaps isolate every residue;
  because `L_0` has at most one zero, the complete bipartite equality graph
  minus at most one edge forces all branch coefficients equal and hence zero.
  Symmetrization over eigenvalue labels globalizes this chart rigidity and
  excludes flat actions anywhere on the fixed shell.  Coarea plus
  Riemann--Lebesgue then proves angular-phase weak convergence
  `(theta,t omega(theta))_*sigma -> sigma tensor Haar` without varying
  interaction rate.  Composing with the completed-phase heavy-sector
  incidence theorem yields, for
  `r_n=floor((1-epsilon^2)^2(3/2)^n/(32L))`,
  `limsup_(t->infinity) P_theta{C_epsilon(e^(-itH(theta))Omega)<=s}
  <=1/L+2^(-r_n/2)` whenever
  `s+1<=r_n log(2)/(2log M_n)`.  Thus every sufficiently late common time,
  not merely a subsequence, has high probability of
  `Omega((3/2)^n/(L log n))` state complexity in an ordinary fixed-strength
  nearest-neighbour static ensemble.  The same times remain efficiently
  non-Haar by the permanent local two-query separator.  Quantifiers are
  sharp: recurrence forbids one fixed full-measure Hamiltonian set from being
  hard for all late times.  O4 remains open because angular Fourier decay is
  non-effective in `n`; no initial linear growth or Brown plateau-onset scale
  is proved.  Paper proof and hostile audit:
  `../2-fully-proven/fixed-shell-angular-dephasing-static-local-plateau-law.md`.
  Lean remained read only; no source or build was touched during refactoring.
- 2026-08-08 -- Upgraded the fixed-time fixed-shell result to a same-pair,
  continuous, doubly-exponential plateau and removed the product-input
  `(3/2)^n` loss.  Seed the ordinary `n`-qubit chain by one uniformly sampled
  stabilizer state, prepared once by a polynomial Clifford circuit.  The
  exact global stabilizer two-design identity gives, against every
  eigenbasis,
  `E_chi sum_j |<e_j,chi>|^4=2/(2^n+1)`.  Thus the collision is at most
  `2L/(2^n+1)` with pair probability at least `1-1/L`.  More generally this
  exposes the collision-to-lifetime law:
  on any time-independent pair set with spectral collision at most `c`,
  plateau depth is `Omega(1/(c log M_n))` while the logarithm of continuous
  plateau lifetime is `Omega(1/c)`.  Product, stabilizer and Choi plateaux are
  three specializations of this one mechanism.  For stabilizer seeds, with pair probability at
  least `1-1/L`, the completed-phase heavy-sector incidence theorem works at
  replica order
  `r=floor((1-epsilon_+^2)^2(2^n+1)/(64L))` and makes the complete depth-`s`
  shortcut probability at most `2^(-r/2)` for
  `s+1<=r log(2)/(2log M_n)`.  Crucially, the collision-bad pair set is fixed
  before time is sampled and is paid once, not once per time.  Fixed-shell
  angular dephasing transfers the restricted estimate to every sufficiently
  late common time.  A grid of
  `N<=2^(r/4)` times then survives the complete temporal union, and
  `||H(theta)||_op<=sqrt(12n-9)` plus trace-distance stability fills every
  grid gap.  For every sufficiently late block origin, with probability at
  least `1-1/L-2^(-r/4)-q`, one fixed Hamiltonian--stabilizer pair has
  complexity above `s` at every instant of a block of length
  `(epsilon_+-epsilon_-)(2^(r/4)-2)/sqrt(12n-9)`.  Fixed `L` gives depth
  `Omega(2^n/log n)` for duration `2^(Omega(2^n))`; slowly growing `L` makes
  success probability tend to one.  Generic cyclicity and maximal
  projective rank give a later low-complexity recurrence for the same pair,
  so the block is also a doubly-exponential post-plateau recurrence-gap lower
  bound.  The local two-query non-Haar separator remains valid at every time.
  This closes pathwise plateau duration at the Brown--Susskind scale for an
  ordinary time-independent nearest-neighbour ensemble.  It still does not
  quantify first onset or prove the initial linear ramp.  Paper proof and
  hostile audit:
  `../2-fully-proven/stabilizer-seeded-static-local-double-exponential-plateau-law.md`.
  Lean remained read only; no source or build was touched during refactoring.
- 2026-08-08 -- Replaced the unnamed fixed-shell Riemann--Lebesgue onset
  threshold by an exact spectral-transversality condition number.  At replica
  order `r`, every fixed-target fidelity moment has an ordered spectral-action
  expansion whose total absolute coefficient mass is at most one:
  `sum_(alpha,beta)|A_(alpha,beta)|=(sum_j|<z,Pi_j chi>|)^(2r)<=1`.
  The generic paired-replica equality is already Lean-proved in
  `HTGeometry/TracelessReplicaDyadicActionShellLaw.lean`; its spectral-projector
  contraction and filtered specialization remain paper proofs during refactoring.
  This removes the `D^(2r)`/character-count remainder at growing replicas;
  derivative constants may still depend on `D` and `r`.  For discriminant cutoff `zeta` and action-gradient threshold
  `g`, define `Q_r(zeta,g)` as spherical mass near the degeneracy locus or a
  critical point of any nonzero balanced action of height at most `r`.
  Fixed-shell nowhere-flatness gives
  `lim_(zeta->0) lim_(g->0) Q_r(zeta,g)=0`.  More sharply, Nash
  eigenvalue geometry, the semialgebraic Lojasiewicz inequality and tube
  volume give at every fixed `n,r`
  `Q_r(zeta,g)<=A_0 zeta^alpha_0+A_(r,zeta)g^alpha_(r,zeta)`.
  A common smooth light-sector filter removes spectral weights above the
  collision-adaptive scale, costs only half the capture amplitude, and retains
  the sharp completed moment `r!(8C/(1-epsilon_+^2))^r`; this avoids the false
  `C^(r/2)` scale of the raw full-overlap moment.  A cutoff
  integration-by-parts argument with vector field
  `grad(phi)/|grad(phi)|^2` proves finite-time defect at most
  `Q_r(zeta,g)+B|t|^(-1)(g^(-1)+g^(-2))`, where `B` is an exact finite
  derivative maximum on the discriminant-separated compact set.  A soft
  collision cutoff preserves the one-time bad-pair payment.  With
  `r=floor((1-epsilon_+^2)^2(2^n+1)/(256L))`, circuit entropy
  `N_s<=M_n^(s+1)<=2^(r/2)`, and
  `Q_r<=q((1-epsilon_+^2)/4)^r/(2N_s)`, every time beyond
  `T_tr=2BN_s(q((1-epsilon_+^2)/4)^r)^(-1)(g^(-1)+g^(-2))` has restricted
  shortcut probability at most `2^(-r/2)+q`.  Substitution of `q/N_W`
  makes the prior continuous-block onset quantitative in finite geometric
  data, without random radius, minimum action, random time or fresh noise.
  Collision controls capacity/lifetime; spectral-action transversality
  controls onset.  Composing the existing Lean-proved autonomous word cone
  with the stabilizer plateau gives every robust hard endpoint the envelope
  `C_(epsilon_-)(psi_(T-u)) > s-S_H(u,epsilon_+-epsilon_-)`.
  Nearly optimal nearest-neighbour simulation forces an exponential
  `2^(n(1-o(1)))` hardening shoulder below a depth
  `Omega(2^n/(L log n))` plateau, but not monotone growth from laboratory
  time zero.  This log entry's proposed next step is now retired: the capture
  denominator in `T_tr` itself forces `exp(Theta(r))` time, so no upper bound
  on its transversality constants can make it Brown-scale at `r=Theta(D)`.
  Replacement core is recorded in the next entry.  Paper proof and hostile audit:
  `../2-fully-proven/fixed-shell-transversality-onset-hardening-cone-law.md`.
  Lean corpus was inspected read only; no Lean source or process was touched.
- 2026-08-08 -- Retired individual-action and positive first-gradient
  dephasing as Brown-scale mechanisms, and replaced the vague survivor by an
  exact signed convolution lift.  For `D` spectral velocities in an observer
  space of dimension `d=12n-10`, the `binom(D+r-1,r)` replica multiplicity
  sums lie in a ball of radius `r sqrt(12n-9)`.  Euclidean packing therefore
  forces a nonzero balanced action gradient of size at most
  `2r sqrt(m)/(binom(D+r-1,r)^(1/d)-1)`, which is
  `exp(-Omega(D/n))` at `r=Theta(D)`.  A weighted central-bin theorem is
  stronger: for the collision-good seed target, the absolute coefficient mass
  of off-diagonal actions with gradient at most `D^(-1)` is at least
  `(9/16)^r exp(-O(n^2))`; relative to the required capture scale
  `((1-epsilon_+^2)/4)^r`, this grows exponentially.  Independently, the
  parent's onset formula obeys
  `T_tr>=(2/q)(4/(1-epsilon_+^2))^r` for fixed `0<q<=1`.  Hence neither better
  `Q_r`, better derivative constants, minimum gaps, Jacobians, nor a positive
  amplitude-weighted first-gradient cutoff can produce Brown time.
  The exact surviving representation is finite and unconditional.  With
  `mu_1=sum_j c_j delta_(e_j,v_j,E_j)`, conjugate reflection `star`, and
  `nu_1=mu_1*mu_1^star`, the full signed replica lift is
  `nu_r=nu_1^{*r}`.  Equal-multiplicity return is exactly the hidden lattice
  sector `k=0`, so source-first removal is the single final projection
  `P_(k ne 0)(nu_1^{*r})`; observer pushforward then preserves fibre-sheet
  multiplicity and performs signed addition before any norm.  Stepwise killed
  transfer operators are invalid because return projection does not commute
  with convolution.  Fourier evaluation is exact:
  `hat(nu_r)(xi,t)=|sum_j c_j exp(-i(tE_j+<xi,v_j>))|^(2r)`, with
  the diagonal multinomial mass subtracted after final return removal.  For the
  seed target the lift is positive, so cancellation comes from this character,
  not from total variation.  Exact open core: construct the duplication-invariant
  occupied-incidence quotient norm of this final-projected signed lift and
  prove or falsify scale-matched contraction through `r=Theta(D)`.  This is a
  conjecture, not a claimed Brown theorem; higher-order phase mechanisms not
  reducible to a positive first-order majorant remain logically possible.
  Paper proofs and hostile audits:
  `../2-fully-proven/observer-dimension-replica-action-crowding-law.md` and
  `scale-matched-signed-action-packet-law.md`.  Lean corpus remained read only;
  no Lean source, build, or process was touched.
- 2026-08-08 -- Removed the exterior signed packet from O4's genuine open
  core.  For every bounded static Hamiltonian, seed, finite occupied target
  image `Z`, Krylov order `K` and replica order `r`, let `P_K` project onto
  `span{psi_0,Hpsi_0,...,H^Kpsi_0}`.  Taylor's unitary integral remainder,
  tensor telescoping, and projection geometry give the complete-union law
  `q_r(t)<=q_(K,r)(t)+2r(BT)^(K+1)/(K+1)!`, where `q_r` is the original
  occupied-Veronese incidence action and `q_(K,r)` is formed only after
  projecting both orbit and actual occupied endpoint image by `P_K`.
  Crucially,
  `span{(P_Kz)^(tensor r)}=P_K^(tensor r)span{z^(tensor r)}` exactly, so the
  reduction is invariant under circuit-label duplication, retains every
  source fibre sheet, and pays any target-independent return set once.  Its
  projected Hilbert rank is at most both the original occupied-image rank and
  `binom(dim K_K+r-1,r)`, but hostile review proves rank alone cannot yield
  decay: one target parallel to the carrier makes rank-one action maximal.
  A second exact rigidity closes radial/Krylov mixing.  For every homogeneous
  linear local family `H(x)`, nonzero scaling satisfies
  `K_K(H(cx))=K_K(H(x))` and
  `q_(K,r,cx)(t)=q_(K,r,x)(ct)`; Gaussian disorder is therefore exactly a
  positive radial time mixture of fixed-shell carrier incidence actions, not
  a source of new carrier directions.  Failed conjecture loop: an undefined
  full packet norm was circular; targetwise moment stability reintroduced
  circuit entropy; causal projection before the Veronese lift succeeds;
  dimension-only and radial-Fourier closures fail.  O4 is now strictly the
  quenched growing-`K,r` upper bound on the projected carrier incidence action
  for the actual shallow-circuit image.  Paper proof and hostile audit:
  `../2-fully-proven/radial-krylov-projected-complete-incidence-law.md`.
  Lean corpus was inspected read only; no Lean file, build, or process was
  touched during refactoring.
- 2026-08-09 -- Removed the stabilizer seed's probability--height tradeoff
  without a Haar seed or design-mixing theorem.  Sample a square-free
  degree-at-most-three polynomial `h:{0,1}^n -> Z/8Z` and prepare the exact
  cubic-phase state `D^(-1/2) sum_x exp(2 pi i h(x)/8)|x>`.  Reed--Muller dual
  distance `16`, lifted through an odd minor to `Z/8Z`, makes any fifteen
  distinct phases independent uniform eighth roots, while every seed has an
  exact `O(n^3)` finite-alphabet circuit.  For every orthonormal basis `e`,
  product-torus Poincare and the exact Steinhaus fourth/sixth moments give
  `E_h sum_j|<e_j,chi_h>|^4 <= 2/D` and variance at most `96/D^3`.  Eight
  coordinate moments suffice, so fifteen-wise finite phases inherit the
  bounds exactly for an arbitrary complex Hamiltonian eigenbasis.  Hence
  collision is at most `(2+kappa)/D` with failure at most
  `96/(kappa^2 D)`.  Composing the existing collision-capacity law, fixed-shell
  angular dephasing, continuum speed mesh, generic cyclicity/recurrence, and
  permanent local two-query separator yields, with probability `1-O(1/D)`,
  one fixed Hamiltonian--seed pair of depth `Omega(D/log n)` continuously for
  `2^(Omega(D))` time, followed by low-complexity recurrence, while locality
  remains distinguishable from Haar at every time.  Fubini over the finite
  cubic family and the integrated positive-part second moment fix one
  `O(n^3)`-preparable seed per `n`, simultaneously for every collision threshold, with the same
  Hamiltonian-bad probability, so only the Hamiltonian need be sampled.  This closes full plateau
  height, lifetime, high probability, recurrence, and locality simultaneously.
  It does not bound first onset or prove the initial linear ramp; finite seed
  moments cannot replace the open growing-replica dynamical incidence law.
  Paper proof and hostile audit:
  `../2-fully-proven/cubic-phase-seeded-static-local-full-scale-plateau-law.md`.
  Nakata--Koashi--Murao already supply closely related diagonal-unitary
  design/controlled-phase seed infrastructure, so seed preparation is not a
  novelty claim.  Candidate new content starts at basis-uniform collision
  concentration and its static-local plateau/recurrence/locality composition.
  Lean remained read only during the active refactor.
- 2026-08-09 -- Corrected the finite-onset invariant from an exponentially
  amplified monomial/Bures moment to a bounded hypothesis test.  For squared
  target overlap `x`, fidelity thresholds `b<a`, replica order `r`, and
  `k=ceil(r(a+b)/2)`, the binomial-tail polynomial
  `B_(r,k)(x)=P{Bin(r,x)>=k}` is the expectation of one literal orthogonal
  projector on `r` replicas.  Hoeffding gives
  `(1-eta_r)1_(x>=a)<=B_(r,k)(x)<=1_(x>=b)+eta_r`, with
  `eta_r=exp(-r(a-b)^2/2)`.  Taking the maximum over the actual distinct
  depth-`s` endpoint image before source integration yields a complete,
  duplication-invariant incidence action sandwiched between the two physical
  shortcut probabilities.  Differentiating the binomial tail telescopes to
  the `Beta(k,r-k+1)` density, so this action is exactly a unit-mass
  beta-window average of complete approximate-tube coarea mass.  A source
  sheet of probability `p` and unit overlap contributes exactly `p`; the old
  monomial reporter contributes `a^(-r)p`.  Thus Bures minimax remains exact
  inside its ellipsoidal monomial class but is exponentially too strong as
  the mandatory finite-onset invariant when rare return/easy sheets are
  present.  The corrected open core is the weaker and radius-slack-sharp
  bound `I_(r;a,b)=o_n(1)` at scale-matched `r,t,s`, with target-independent
  easy/return excision.  Paper proof and hostile audit:
  `../3-formalized/beta-threshold-complete-incidence-law.md`.  No Brown
  growth claim follows yet; Lean remained read only during refactoring.
- 2026-08-09 -- Removed scale-matched order `r=Theta(D)` from the mandatory
  Brown-front formulation.  Fixed fidelity slack and the bounded binomial
  reporter needs only `r_n=ceil(4 log(n)/(a-b)^2)` to approximate the complete
  shortcut event at one fixed time within `n^(-2)`, regardless of target count
  or circuit depth.  A continuous ramp through time `Theta(D)` has
  `O(D poly(n))` speed-mesh points and needs only `r=O(log D)=O(n)` for the
  complete temporal union, still exponentially below `Theta(D)`.
  For an orthogonal spectral orbit with largest retained weight `p_*`, the
  complete target maximum followed by the binomial test has phase gradient
  squared at most `4r_n^2 p_*`; finite maxima preserve this constant without
  circuit entropy.  One common light filter turns collision `C<=c/D` into
  `p_*<=c/(rho^2D)`, hence conditional phase-Haar variance
  `O((log n)^2/D)` at one time and `O(n^2/D)` on the full Brown grid, while
  spending only fixed observational slack.  This
  falsifies growing-replica observer crowding and all-character
  pseudodeterminants as logically necessary invariants.  It does not close
  growth: a singular static-Hamiltonian phase graph may still concentrate on
  a Haar-rare circuit tube.  New minimal core is quantitative physical-graph
  mixing for this one bounded, low-influence, complete-incidence observable at
  Brown time/depth after target-independent return excision.  Paper proof and
  hostile audit:
  `../2-fully-proven/low-replica-complete-incidence-influence-law.md`.  Lean
  remained read only during corpus refactoring.
- 2026-08-09 -- Proved that arbitrary-target physical-graph mixing is still
  too weak a frontier because it omits preparation structure.  The time-`t`
  endpoint map of an `m`-parameter unit local shell is
  `|t|sqrt(m)`-Lipschitz, so its entire image has an `epsilon`-net of at most
  `(1+2|t|sqrt(m)/epsilon)^m` actual endpoints.  At `m=Theta(n)` and Brown
  time `t=Theta(D/poly(n))`, this cover has log-size only `O(n^2)` yet captures
  the whole Hamiltonian ensemble; allowed Brown-depth circuit words have
  entropy `Theta(D)`.  Therefore Jacobian, coarea, source dimension, target
  count, occupied rank, and target covering entropy cannot close O4 unless
  they encode local circuit preparation.  Exact positive survivor: the
  complete circuit fidelity and bounded binomial reporter obey a max-plus
  Bellman recursion under one local gate.  A metric-robust calibration
  `Phi(gv)<=Phi(v)+1`, `|Phi(v)-Phi(w)|<=L d(v,w)` gives
  `C_epsilon(v)>=Phi(v)-Phi(chi)-L epsilon`.  O4 is now the construction of a
  quenched recurrence-compatible nonlinear calibration with Brown-rate
  growth; arbitrary endpoint incidence is a proved dead route.  Paper proof
  and hostile audit:
  `../3-formalized/static-orbit-net-no-go-and-circuit-bellman-law.md`.  Lean
  remained read only during corpus refactoring.
- 2026-08-09 -- Separated full static-local plateau capacity from first onset
  by an exact weak-cut law.  If
  `H=H_A tensor I+I tensor H_B+V` starts from a product seed, Duhamel stability
  and factorwise state synthesis give
  `C_epsilon(exp(-itH)chi)<=S_A(eta_A)+S_B(eta_B)` throughout
  `|t| ||V||_op<=epsilon-eta_A-eta_B`.  On a balanced cut this cap is
  `2^(n/2) poly(n)=o(2^n/log n)`.  Independently, products of two finite
  cubic-phase seed families have collision expectation at most `4/2^n`
  against every possibly entangled eigenbasis.  Density of simple, cyclic,
  maximal-projective-rank points arbitrarily close to a decoupled
  nearest-neighbour shell point therefore supplies, for every prescribed
  delay `L`, one fixed ordinary path-local Hamiltonian and one product cubic
  seed which remain below full-scale complexity until `L`, but later exhibit
  an `Omega(2^n/log n)` plateau for `exp(Omega(2^n))` time, recurrence, and
  permanent local two-query separation from Haar randomness.  Thus collision
  and projective rank control capacity but cannot control onset.  For the
  ordinary path-local coefficient shell, the nine cross-edge coefficients
  obey an exact beta projection law; weak-edge mass is `Theta_n(x^9)`, forcing
  a quenched onset-delay floor `c_n L^(-9)`.  At Brown time this is
  `exp(-Theta(n))`, up to the beta law's polynomial-in-`n` prefactor.  The
  surviving endpoint target is geometric-skeleton Bellman escape on a
  conductance-good shell, paying the cut-bad sector once.  Paper proof and
  hostile audit:
  `../2-fully-proven/weak-cut-complexity-onset-capacity-separation-law.md`.
  No Lean source or process was touched during the active corpus refactor.
- 2026-08-09 -- Conductance conditioning is not the surviving onset invariant.
  The internally prior Lean-proved fast-forwardable-stratum law already owns the
  Duhamel/codimension shortcut mechanism; the weak-cut theorem is its physical
  balanced-cut specialization, not a new continuity theorem.  A stronger
  conjecture loop now fails three successively less naive onset criteria.  A
  fully coupled commuting diagonal path carrier has all edge interactions
  `Omega(n^(-1/2))` and admits a uniform polynomial compiler.  Complete cubic
  seeds have exact computational-basis collision `1/D`.  Arbitrarily small
  generic transverse perturbations add simple spectrum, cyclicity, and maximal
  projective rank while Duhamel continuity preserves any prescribed incubation
  time.  The completed-phase parents then force the same fixed system to attain
  an `Omega(D/log n)` plateau for `exp(Omega(D))` time, recur, and remain locally
  distinguishable from Haar at every time.  Thus conductance plus optimal
  collision plus maximal projective rank still does not control first onset.
  The positive theorem is a capacity-compatible completion of the prior
  codimension obstruction: every independently compiled `f`-dimensional patch
  whose finite seed family is basis-uniformly collision-good contributes a
  shell subset of mass `Omega_P(L^(-(m-f)))` that is easy through `L` but later
  has the full plateau, recurrence, and permanent non-Haar separator.  In the
  ordinary path-local Pauli shell, the diagonal carrier has
  `m=12n-9`, `f=2n-1`, and forced exponent `10n-8`; a patch with every edge
  strong contributes `A_n L^(-(10n-8))`, where
  `A_n>=exp(-O(n log n))`.  At Brown delay this is `exp(-Theta(n^2))`.
  This is a one-sided forced tail, not a full delay distribution or inverse
  classification.  No union over “all carriers” is defined.  Any next Brown
  theorem must name and pay concrete weak-cut and commuting-carrier exceptional
  sets before attempting geometric-skeleton Bellman escape; sufficiency on the
  complement remains open.  Paper proof and hostile audit:
  `../2-fully-proven/capacity-compatible-fast-forwardable-incubation-law.md`.
  Lean remained read only during corpus refactoring.
- 2026-08-09 -- Separated complexity onset from quantum-recurrence dimension.
  Intersecting the capacity-compatible diagonal-carrier incubation tube with
  the conull metric-Diophantine local-chain set costs no shell measure.  Thus,
  for every prescribed delay `L`, a fixed cubic-phase seed and a path-local
  shell subset of mass
  `A_n(1-O(1/D))L^(-(10n-8))`, with
  `A_n>=exp(-O(n log n))`, simultaneously remain polynomially easy through
  `L`, keep every edge interaction `Omega(n^(-1/2))`, have collision
  `O(1/D)`, maximal projective rank, a later `Omega(D/log n)` plateau of
  `exp(Omega(D))` duration, recurrence, and permanent local non-Haar
  separation.  The new conjunction adds the exact continuous fidelity-return
  exponent
  `lim_(delta->0) log T_fid(delta)/log(1/delta)=(D-2)/2` for every Hamiltonian
  retained in the set.  Cyclicity makes the fidelity deficit a nondegenerate
  quadratic form on the projective phase torus, so the phase-radius exponent
  `D-2` from metric extremality divides by two.  Therefore maximal recurrence
  dimension and all current uniform capacity/conductance thresholds do not
  upper-bound onset; a finer carrier-distance invariant is unavoidable.
  Hostile boundary: the recurrence limit is at fixed `n,H`, not a uniform
  fixed-error large-`n` law, and the theorem is a delayed positive-measure
  family rather than the missing typical Brown upper escape bound.  Failed
  representation loop: all-cut entanglement is externally known to saturate
  polynomially; additive history action upper-bounds one history rather than
  lower-bounding endpoint complexity; recurrence dimension is now explicitly
  falsified as an onset clock.  Surviving representation is finite-scale
  subgroup distortion: growth is undistortion, fast-forwarding/incubation is
  distortion, plateau is diameter saturation, and recurrence is distortion
  collapse.  Exact remaining core is quenched finite-scale undistortion on the
  geometric Brown skeleton after named shortcut tubes are paid.  Paper proof:
  `../2-fully-proven/onset-recurrence-dimension-independence-law.md`.  Lean
  remained read only during corpus refactoring.
- 2026-08-09 -- Upgraded arbitrary-delay examples to a genuine fixed-seed
  onset distribution.  The tempting equality “shortcut codimension equals
  the complete tail exponent” is false without an inverse classification:
  a carrier tube gives only a lower tail, and other shortcut sectors may
  dominate.  The positive survivor is exact and stronger than the prior
  delay-by-delay Fubini statement.  On a balanced path cut, the product-cubic
  collision mean `<=4/D` permits one fixed seed to be selected on a
  positive-measure simple-spectrum subset of the codimension-nine decoupled
  carrier.  Inner regularity, compactness, and collision continuity make that
  seed capacity-good on one fixed open tube.  Therefore the same seed, for
  every sufficiently large `L`, has
  `Pr{tau_full>L, later full plateau, maximal recurrence}>=A_n L^(-9)`.
  Layer cake now applies to one random variable and proves that every
  conditional onset moment of order `p>=9` diverges.  A second construction
  survives conductance conditioning: on a compact, uniformly gapped,
  strongly coupled diagonal `Z/ZZ` patch, the explicit seed `|+>^n` has
  collision `1/D`; Davis--Kahan preserves collision `<=81/(16D)` and
  cyclicity in a fixed transverse tube.  Its codimension is `10n-8`, so the
  same explicit seed has divergent conditional onset moments for every
  `p>=10n-8` while all edges remain `Omega(n^(-1/2))`, and every retained
  Hamiltonian later has the full plateau, exact recurrence exponent,
  recurrence, and permanent non-Haar locality.  These are forced divergence
  thresholds, not matching upper tails or finiteness below threshold.
  Brown-front consequence: unrestricted high onset moments are invalid
  concentration proxies; use quantiles or truncated moments after named
  shortcut excision.  Exact upper-escape/linear-ramp core remains open.
  Paper proof and hostile audit:
  `../2-fully-proven/codimension-forced-complexity-onset-moment-divergence-law.md`.
  Lean remained read only; no Lean file, build, or process was touched.
- 2026-08-09 -- Closed the external-calibration representation gap left by
  the circuit Bellman law.  For the one-gate Markov operator `P`, the
  normalized killed gate-walk Green function
  `G_(a,epsilon)=(1-a)(I-aP)^(-1)1_(B_epsilon(chi))` obeys the exact sandwich
  `(1-a)(a/M)^C <= G <= a^C`, where `C` is robust word complexity.  Hence
  complexity is exactly the zero-fugacity exponent
  `lim_(a->0)-log(G)/log(1/a)`.  Exponential-distance softening gives an
  explicit noncircular robust Bellman calibration with one-gate increment at
  most one and Lipschitz constant `beta/log(M/a)`.  For a random static
  endpoint `V`, one scalar estimate controls the complete circuit union:
  `Pr{R,C_epsilon(V)<=s} <= E[1_R G_tilde(V)]/((1-a)(a/M)^s)`.
  Hostile attack then exposes the exact limitation.  Positive `L^p`
  linearization of the complete maximum loses the factor `M^(-ell/p)`; to
  preserve it within `exp(-kappa r)` forces total replica order
  `rp >= ell log(M)/kappa`, which is `Omega(2^n)` at Brown depth.  Thus low
  replicas and positive linear transfer cannot coexist at the Brown front.
  The genuine surviving core is a zero-temperature quenched gate-transfer
  estimate, equivalently exponential suppression of shadowing between the
  static endpoint and a geometrically killed local random circuit after one
  return/shortcut-carrier excision.  Paper proof and hostile audit:
  `../2-fully-proven/gate-walk-green-bellman-tropicalization-law.md`.  Lean was
  intentionally deferred during corpus refactoring.
- 2026-08-10 -- Closed the one-step all-replica local-Pauli Hall gate on paper.
  First, one fixed Pauli orientation on each connected graph edge expands
  every subspace of the sitewise singlet quotient at every finite replica
  order.  The new mechanism avoids higher-replica permutation incidence:
  edge commutators create nonsinglet defects at both endpoints, distinct
  edges land in orthogonal defect sectors, and connected Pauli
  controllability identifies their joint singlet kernel with the exact
  global collective commutant.  Second, the complete weight-one and
  graph-edge weight-two Pauli family expands every subspace of the full
  replicated operator space modulo that commutant in one step.  The proof
  tests only the unique greatest maximum-defect subspace.  Continuous
  product-local rotation covariance makes its singlet split reducing and
  turns off-singlet Hall into internal reproduction; arbitrary-replica
  Pauli characters resolve visible edge outputs; the full nine-orientation
  positive edge Casimir injectively returns precisely the hidden detector
  kernel.  This improves the prior linear physical word-depth Hall theorem
  to depth one and replaces the mixed one-step defect `dim S_r` by the exact
  global permutation defect.  It proves rank saturation only: no replica-
  uniform capacity, pseudodeterminant, smallest-singular-value, cavity-decay,
  quenched lower-tail, circuit-union, or Brown-ramp estimate follows.  Exact
  surviving algebraic/analytic frontier is quantitative conditioning on the
  collective-commutant quotient, strong enough for approximate tubes and
  growing replica order.  Dependency-closed proofs and hostile audits:
  `../2-fully-proven/all-replica-fixed-edge-singlet-hall-expansion-law.md` and
  `../2-fully-proven/all-replica-one-step-local-pauli-hall-saturation-law.md`.
  Lean remained read only during corpus refactoring.
- 2026-08-10 -- Advanced and corrected the quantitative Hall frontier.  A new explicit symmetric
  `3 x 3` family proves that exact Hall plus a uniformly bounded and coercive quadratic Casimir does
  not bound operator capacity: its Casimir remains in `[(1/2)I,4I]` while capacity is
  `Theta(epsilon^2)`.  This retires the attempted direct transfer from the Baer--Haah-style vector
  frame gap to one-step commutator operator scaling.  The strongest positive survivor is an exact
  all-replica local-word leakage theorem.  Every full Pauli commutator has a depth-at-most-`n`
  synthesis from weight-one/two commutators with coefficient `ell^1` mass one; full-Pauli Casimir
  normalization is bi-tight and has least nontrivial eigenvalue `2D^2`.  Therefore every
  dimension-losing occupied incidence cut receives normalized, sheet-retaining local-word leakage
  at least `2D^2/(D^2-1)>2` per lost dimension, uniformly in replica order.  This is quantitative
  conditioning rather than rank.  Hostile boundary: a shallow circuit image may have full linear
  span, so the theorem does not prove Brown escape.  The remaining core is to transfer its
  sheetwise carré du champ through the bounded max-plus Bellman reporter before span
  scalarization.  Paper proof and counterexample:
  `../2-fully-proven/all-replica-incidence-normalized-local-word-leakage-law.md`.  Lean remained
  read only during corpus refactoring.
- 2026-08-10 -- Identified and proved the exact obstruction to transferring all-replica planar
  cavity decay to one ordinary static Hamiltonian.  The all-replica Hall theorem does compose with
  matrix-semicircle absolute continuity: on the global collective-commutant quotient, the free
  planar vacuum compression decays to zero at every finite replica order.  But each realized
  static Hamiltonian has a larger moving centralizer.  For a maximal-projective `D`-level
  Hamiltonian at replica order `r`, its dimension is exactly
  `kappa_(D,r)=sum_(|k|=r)(r!/prod_j k_j!)^2`; after the stable-range permutation quotient,
  `kappa_(D,r)-r!` zero modes remain.  For the ordinary nearest-neighbour fixed Pauli shell,
  nowhere-flat spectral actions imply operator-norm convergence of the annealed replicated
  propagator to the average of these quenched centralizer projections.  Its quotient trace is
  exactly `kappa_(D,r)-dim N_(D,r)` and its norm is at least that trace divided by
  `D^(2r)-dim N_(D,r)`; at one replica the lower bound is `1/(D+1)`.  Hence static and planar
  propagators remain separated at long times even after common-kernel removal.  Quenched centered
  norm cannot help: it is identically one on the oscillatory complement.  Correct Brown target is
  now a quantitative, centralizer-centered **Bellman** dephasing estimate relative to the quenched
  completed-phase circuit baseline, not decay to zero and not free-cavity transfer.  Paper proof
  and hostile audit:
  `../2-fully-proven/all-replica-static-centralizer-planar-separation-law.md`.  Lean remained read
  only during corpus refactoring.
- 2026-08-11 -- Closed the permanent-locality/Haar half with a dimension-only operational tail.
  For every nonzero traceless Hermitian source on a `D >= 2` dimensional register, exact Haar
  adjoint covariance gives
  `E(Re tr(HU*HU))^2=tr(H^2)^2/(D^2-1)` and therefore half-energy false-positive probability at
  most `4/(D^2-1)`.  Exact Pauli Hilbert--Schmidt orthogonality identifies the literal signed
  coefficient-matched product-eigenframe mean with
  `Re tr(HU*HU)/(D||h||_1^2)`.  Autonomous evolution retains its full value at every real time, so
  the same `4/(D^2-1)` bound applies at half the permanent operational value for every supported
  Pauli dictionary, with no dictionary-cardinality, spectral-gap, or nondegeneracy condition.
  This strengthens the existing same-Hamiltonian complexity--locality coexistence theorem; it does
  not prove initial growth.  It also confirms the preceding centralizer diagnosis: conserved-source
  memory is a permanent physical sector to condition on, not an error term that may be forced to
  decay to the full-Haar vacuum.  The Brown open core remains centralizer-conditioned Bellman
  escape/finite-scale undistortion after named return and shortcut-carrier excision.  Lean modules:
  `HTGeometry/FiniteUnitaryAdjointAutocorrelationLaw.lean` and
  `HTGeometry/EnergyMatchedEigenframeSourceMemory.lean`; final module build and axiom audit pass.
- 2026-08-11 -- Replaced the qualitative phrase “near the moving centralizer” by an exact,
  gap-free defect.  For every finite Hermitian `H` and unitary `U`,
  `||HU-UH||_HS^2 = 2(tr(H^2)-Re tr(HU*HU))`; hence full energy-matched source memory is
  equivalent to exact commutation.  Combining this identity with the exact Haar second moment
  proves that the Haar mass of the literal approximate-centralizer tube
  `{U: ||HU-UH||_HS^2 <= tr(H^2)}` is at most `4/(D^2-1)` for every nonzero traceless source.
  This removes minimum-gap and operator-versus-Hilbert--Schmidt normalization ambiguity from the
  tube itself.  It does not transfer Haar rarity to an adaptive circuit selected from a static
  local `H`; the remaining theorem is still quenched Bellman escape *inside* this low-defect
  sector, after return/carrier excision.  Lean module:
  `HTGeometry/FiniteUnitaryEnergyDefectLaw.lean`; development compile, final module build, and axiom
  audit pass.  Card: `../3-formalized/finite-unitary-energy-defect-law.md`.
- 2026-08-11 -- Closed a logical gap between robust Choi state shortcuts and the low energy-defect
  sector.  The naive operator-norm bridge loses system-size effective rank and cannot support fixed
  robust error.  In the source eigenbasis, the squared entries of the relative shortcut form a
  doubly stochastic coupling.  Its quadratic energy transport cost obeys the exact fourth-moment
  law
  `||[H,W]||_HS^4 <= 16 kappa_4(H) tr(H^2)^2 (1-F_Choi(T,W))` whenever the autonomous target `T`
  commutes with `H`.  Hence infidelity at most `1/(16 kappa_4(H))` forces every selected shortcut
  into the certified half-energy tube, with no minimum gap, nondegeneracy, or dictionary union.
  Established quantum hypercontractivity gives `kappa_4(H) <= 9^q` for degree-`q` Pauli
  Hamiltonians, making the required resolution dimension-independent; that Pauli corollary remains
  to be formalized before final use.  This bridge does not prove escape inside the tube, so the
  Brown growth core remains selector-aware quenched Bellman escape after return/carrier removal.
  Lean module `HTGeometry/ChoiShortcutEnergyDefectKurtosisLaw.lean`; final module build and axiom
  audit pass.  Card: `../3-formalized/choi-shortcut-energy-defect-kurtosis-law.md`.
- 2026-08-11 -- Closed the previously informal fixed-locality robustness premise by an elementary
  coefficient-to-matrix theorem.  Phase-free XOR autocorrelation satisfies an exact triple
  reindexing identity and a four-linear Cauchy--Schwarz law that tensorizes over qubits.  The
  one-qubit quartic has no term with exactly one nonidentity label, closing weight induction with a
  qubit-count-independent constant.  Regrouping `H^2` by XOR output retains Pauli orthogonality
  exactly and removes unit-modulus multiplication phases only afterward.  Consequently every real
  weight-`q` Pauli Hamiltonian obeys normalized spectral kurtosis at most `(9^q)^4`, and Choi
  infidelity at most `1/(16(9^q)^4)` forces any shortcut to a commuting target into the half-energy
  commutator tube.  This corrects the preceding log's sharper informal `9^q` constant: that value
  belongs to standard quantum hypercontractivity and is not what the new elementary Lean proof
  establishes.  The bound is dimension-independent but deliberately nonsharp, and no external
  novelty is claimed for its numerical strength.  Brown growth remains unproved: exact next core
  is quenched selector-aware Bellman escape inside this tube after return and fast-forwardable
  carrier removal.  Lean module:
  `HTGeometry/PauliXorIncidenceHypercontractivityLaw.lean`; direct compile, module build, lint, and
  axiom audit pass.  Card:
  `../3-formalized/pauli-xor-incidence-hypercontractivity-law.md`.
- 2026-08-11 -- Proved the gap-free Choi form of ordered spectral phase extraction.  Nearest-neighbour
  chord action is subadditive under phase multiplication and loses at most
  `4 sqrt(D) sqrt(E)` under radial recovery from total diagonal square error `E`.  For finite
  unitaries, trace alignment gives the exact identity
  `||W-cT||_HS^2=2D-2|tr(T^*W)|`; hence normalized Choi overlap directly yields a recovered exact
  centralizer phase profile without operator-norm conversion, a minimum spectral gap, or a
  minimum diagonal modulus.  Hostile falsification is part of the theorem: the alternating binary
  character attains the maximal action `2(D-1)`, so one shallow carrier gate can already saturate
  this invariant.  Spectral chord action is therefore a safe Choi-stable extraction auxiliary, not
  a circuit lower bound.  It closes the operator/Choi extraction gap in the phase-bandwidth branch
  but leaves the actual Brown core unchanged: quenched finite-scale undistortion/Bellman escape for
  the moving centralizer after return and carrier removal.  Lean module:
  `HTGeometry/FiniteSpectralPhaseActionLaw.lean`; direct compile, module-only build, and axiom audit
  pass.  Repository-wide lint is currently blocked by unrelated newly added unreachable RHTower
  and HTGeometry modules; the new module itself is umbrella-reachable and contains no forbidden
  declarations.
- 2026-08-11 -- Excised every subexponential gate-observer sector from the Brown obstruction.
  For a discounted first-entrance potential `h_A`, its positive equilibrium charge
  `q_A=(I-aP)h_A` has total mass `cap_a(A)` and is supported on the target.  On any finite
  `P`-invariant bounded eigenmode sector `E`, this gives the exact formula
  `<h_A,phi_j>=cap_a(A) E_(rho_A)[phi_j]/(1-a lambda_j)`.  Consequently the expectation of the
  entire projected reporter under an arbitrary endpoint law--even one singular to Haar and with
  order-one permanent distinguishing bias--differs from the stationary capacity baseline by at
  most `cap_a(A) B_(E,a)`, where `B_(E,a)` is the centered resolvent reproducing-kernel sup norm.
  Composing with prefix-free first entrance proves a complete-circuit-union bound whose only
  uncontrolled term is `int (I-Pi_E)h_A dnu`.  Thus every sector with
  `B_(E,a)=exp(o(D))` is harmless against `exp(-Theta(D))` target capacity.  A Neumann-resolvent
  argument proves `B_(E,a)<=L_E/(1-a)` from projection leverage; for every homogeneous
  `K`-dimensional sector this is `(K-1)/(1-a)`, and the standard `k`-copy unitary
  matrix-coefficient sector has real dimension `K<=2D^(4k)+1`.  Hence all `poly(log D)`-copy
  locality observers are covered unconditionally.  The same charge formula and Parseval prove the
  capacity--replica uncertainty law
  `||Pi_E h_A||_2^2/||h_A||_2^2 <= cap_a(A)K/(1-a)^2`.  Since orthogonal projection is the best
  `L^2` approximation, every function in `E` obeys the complementary lower bound.  For a
  projective trace-distance ball, `pi(A_epsilon)=epsilon^(2(D-1))`; capturing any fixed fraction of
  the global accessibility reporter therefore forces replica order `Omega(D/log D)`.  This is
  intrinsic and precedes the circuit union--not an artifact of its entropy estimate.  Operationally,
  every adaptive `k`-copy experiment has a `k`-copy polynomial conditional mean, so Jensen upgrades
  the same theorem to a Haar-average mean-square sample lower bound
  `k=Omega(D/log D)=Omega(2^n/n)` for estimating global preparation accessibility with nontrivial
  relative accuracy.  Normalizing the reporter as
  `A_(A,a)=(1-a)h_A/cap_a(A)` gives Haar mean one, return value `(1-a)/cap_a(A)`, and exact
  likelihood representation `d sigma_(A,a)/d pi=A_(A,a)`.  The return tube carries between
  `1-a` and one of the tilted probability mass; its KL divergence is at least
  `(1-a)log(1/pi(A))-log 2` and its chi-square divergence at least
  `(1-a)^2/cap_a(A)-1`, although every subexponential copy sector captures a vanishing fraction.
  This is the exact sense in which gate accessibility is globally non-Haar while remaining hidden
  from simple observers.  It obeys the complexity sandwich
  `-log h_A/log(M/a) <= C <= -log h_A/log(1/a)`.  Growth, plateau, and recurrence are therefore
  logarithmic accessibility loss and reamplification regimes of one canonical order parameter;
  their physical-time schedule remains open.  Crucially, the exact complete-union identity becomes
  `Pr{R,C<=s} <= (M/a)^s cap_a(A)/(1-a) E[1_R A_(A,a)(V)]`.  Writing
  `Q=-log cap_a(A)`, `X=log E[1_R A_(A,a)(V)]`, and
  `Q_eff=Q-X+log(1-a)`, the exact universal criterion is
  `circuit entropy < Q_eff`: circuit entropy plus accessibility excess must stay below capacity
  surprisal.  In the projective-state branch `Q=Theta(D)`, subexponential accessibility suffices
  below the capacity rate.  In a Choi/unitary branch `Q` may be `Theta(D^2)` and `X` may pay the
  ambient-to-static-support codimension; no state-to-Choi scaling transfer is made.  Exponential
  high-mode decay or convergence to Haar was an overstrong target.  This rigorously
  separates permanent efficient non-Haar locality from maximal complexity and retains the full
  capacity exponent; an `L^2` argument would lose its square root.  Pointwise, the same theorem
  makes `(I-Pi_E)h_A` an exact complexity--recurrence coordinate: it is at least
  `1-cap_a(A)((1-a)^(-1)+B_(E,a))` on every return, while complexity at least `s` forces it below
  `a^s-cap_a(A)/(1-a)+cap_a(A)B_(E,a)`.  Thus recurrence and the plateau realign only in the
  high-mode complement; persistent low locality modes stay capacity-small throughout.  It does not
  prove Brown growth.  Exact remaining core is now a **source-relative accessibility budget**
  after common return and fast-forwardable-carrier removal.  Frozen primary conjecture: for the
  Gaussian full nearest-neighbour Pauli shell and either fixed fugacity or the depth-optimal
  `a_D=s_D/(s_D+1)`, projective-state accessibility is `exp(o(D))` uniformly on the geometric
  Brown skeleton; for a Choi branch the scale-correct claim
  is instead `Q_eff-s log(M/a)>=kappa D`.  At recurrence the unexcised pointwise surprisal
  `-log h_A` returns to zero.  Dependency-closed proved reduction and hostile audit:
  `../2-fully-proven/capacitary-observer-sector-excision-law.md`.  Lean remained read only during
  corpus refactoring.
- 2026-08-13 -- Closed the completed-phase accessibility plateau and quantified carrier excision.
  If every circuit target tube has phase-torus mass at most `B`, summing the discounted inverse-gate
  paths and dropping first-hit restrictions gives
  `int h_A dmu <= sum_ell M^ell(a/M)^ell B=B/(1-a)`: gate-word branching cancels exactly.  Markov
  then bounds the whole accessibility tail, and `C_epsilon<=s` has phase mass at most
  `(M/a)^s B/(1-a)`.  The depth-optimal fugacity `a=s/(s+1)` recovers the direct circuit-union
  exponent with only the factor `e(s+1)`.  For the Lean-proved Choi phase target bound `B_D(delta)`,
  unique ergodicity transfers the same reporter bound to completed physical time.  Accessibility
  drops below every `theta>B_D(delta)/(1-a)` syndetically, while every recurrence restores it
  exactly to one.  This proves the accessibility plateau/recurrence law but not first-drop time or
  Brown growth.  Separately, source-relative accessibility surprisal obeys the exact mixture
  soft-min law `exp(-Q(sum w_i nu_i))=sum w_i exp(-Q(nu_i))`.  An easy carrier of mass `w` costs
  only `log(1/w)` and is harmless at depth `s` only when its rarity pays `s log(M/a)` plus the
  desired tail exponent.  Thus carrier excision is now a quantitative theorem, not an informal
  exception.  Internal duplicate search found no prior completed-phase all-word accessibility
  plateau theorem; the first-entrance/Green renewal law itself already existed in the parent card.
  Targeted external search found random/stochastic complexity saturation and Krylov-spread laws,
  not this static completed-phase composition.  Exact paper proof remains in
  `../2-fully-proven/capacitary-observer-sector-excision-law.md`; Lean remains deferred during the
  shared refactor.
- 2026-08-13 -- Reintegrated the parent renewal law into the accessibility plateau without losing
  Brown exponent.  For `g_(A,a)=(I-aP)^(-1)1_A`, strong Markov renewal gives the sharp comparison
  `(1-a)g_(A,a)<=h_A<=g_(A,a)`.  Against any endpoint sublaw `nu`, its expectation is exactly the
  Abel profile
  `Z_a(nu,A)=sum_(ell>=0) a^ell M^(-ell) sum_(|W|=ell) nu(WA)`, so
  `(1-a)Z_a<=int h_A dnu<=Z_a`.  Word multiplicity and repeated occupation sheets are retained;
  first entrance removes them only through the factor `1-a`.  Robust complexity obeys
  `(a/M)^C<=g_(A,a)<=a^C/(1-a)`, hence
  `Pr_nu{C<=s}<=(M/a)^s Z_a`, with the reverse scale bound
  `Z_a>=Pr_nu{C<=s}(a/M)^s`.  Therefore the exact Brown target can be stated as one positive linear
  Abel-incidence estimate
  `Z_a<=exp[-s log(M/a)-kappa D]` after return/carrier excision.  Complete targetwise coarea,
  growing replicas, and nonlinear Bellman control are sufficient proof methods but no longer
  logically mandatory invariants.  Duplicate audit found the Green/hitting comparison already
  proved in `first-entrance-gate-renewal-prefix-law.md`; it is an imported re-expression, not new
  mathematics.  Its new role is to expose the exact positive linear target after the completed-phase
  theorem.  No Brown-rate bound on `Z_a` for ordinary local Hamiltonians is yet proved.  Paper proof
  and hostile audit:
  `../2-fully-proven/capacitary-observer-sector-excision-law.md`.  Lean remained read only during
  shared refactoring.
- 2026-08-13 -- Proved an all-late same-Hamiltonian hardening shoulder with no continuum union
  loss.  Combine the new all-late fixed-shell Choi accessibility plateau with the existing
  deterministic simulation cone
  `C_(epsilon_+)(Phi_H(T))<=C_(epsilon_-)(Phi_H(T-u))+S_n(u,gamma)`.  For every sufficiently late
  endpoint time `T`, the same high-probability Hamiltonian set obeys the entire backward envelope
  `C_(epsilon_-)(Phi_H(T-u))>s-S_n(u,gamma)` simultaneously for all `u` in a prescribed interval.
  No time mesh or union factor appears because failure anywhere in the continuum would contradict
  hardness at the single endpoint.  At depth `s=Theta(D/log M_n)`, uniform local-Hamiltonian
  simulation makes the half-height shoulder length `2^(n(1-o(1)))`; its failure probability is
  `exp[-Omega(D)]`, and the conserved local-source witness remains nonzero throughout.  This is a
  Brown-scale backward lower envelope adjacent to every certified late plateau endpoint, not first
  onset, monotonicity, or a ramp anchored at `t=0`.  Exact paper proof and hostile boundary:
  `../2-fully-proven/capacitary-observer-sector-excision-law.md`.  Lean remained read only during
  shared refactoring.
- 2026-08-13 -- Removed the pre-return decline as an independent theorem obligation.  For Choi
  trace distance and every inverse-closed gate dictionary, an autonomous return with projective
  defect `delta_R` obeys the exact interlacing
  `C_(epsilon+delta_R)(U_t)<=C_epsilon(U_(R-t))` and
  `C_(epsilon+delta_R)(U_(R-t))<=C_epsilon(U_t)`.  At an exact projective return the complete robust
  complexity history is therefore palindromic about `R/2`.  Every proved forward growth lower
  envelope and simulation upper envelope is reflected into the last pre-return interval with only
  additive resolution loss.  This does not prove forward growth, plateau duration, or the first
  recurrence time; it is a bridge that sharpens the full Brown target to a one-sided first-cut law
  plus quantitative recurrence timing.  Paper proof and hostile boundary:
  `../2-fully-proven/autonomous-return-complexity-reflection-law.md`.  Lean remained read only during
  shared refactoring.
- 2026-08-13 -- Strengthened return reflection from the shortest word to the entire circuit
  incidence spectrum.  Word inversion is a length-preserving bijection, so an autonomous return of
  defect `delta_R` interlaces, at every exact depth `ell`, the normalized number of circuit words
  entering the `epsilon`-tube at `t` and `R-t`, with only the radius replacement
  `epsilon -> epsilon+delta_R`.  Every nonnegative length partition function, including the Abel
  endpoint-accessibility profile, obeys the same law; at an exact projective return each depth shell
  and every such free energy are exactly palindromic.  This does not reflect first-entrance path mass,
  because word reversal exchanges prefixes with suffixes.  The result reinforces that no separate
  recurrence-side incidence estimate is needed, while leaving finite-scale centralizer
  undistortion/first-cut growth untouched.  Proof:
  `../2-fully-proven/autonomous-return-complexity-reflection-law.md`.  Lean remained read only during
  shared refactoring.
- 2026-08-13 -- Extended recurrence reflection beyond closed systems.  For every CPTP semigroup and
  every full-channel diamond return defect `delta_R`, the remaining segment `Lambda_(R-t)` is an
  explicit `delta_R`-recovery channel for `Lambda_t` at every `0<=t<=R`; ancilla-assisted trace
  distinguishability can have lost at most that relative amount anywhere in the cycle.  If a
  length-`ell` unitary circuit approximates one intermediate channel within `epsilon`, its inverse
  word approximates the reflected channel within `epsilon+delta_R`.  Hence robust channel
  complexity, every exact circuit-length incidence shell, and every positive Abel partition
  function obey the same return reflection as the closed Choi law.  At an exact full-channel
  return, every intermediate channel has a CPTP inverse and is therefore unitary, so genuine
  Markovian dissipation and exact full-channel recurrence are incompatible.  Classical input is
  CPTP-inverse rigidity; candidate advance is its quantitative all-intermediate recovery and
  circuit-incidence composition.  This broadens the recurrence law but does not change the static
  first-cut obstruction.  Paper proof and hostile boundary:
  `../2-fully-proven/markovian-return-recovery-complexity-reflection-law.md`.  Lean remained read
  only during shared refactoring.
- 2026-08-13 -- Replaced raw local-gate word entropy by intrinsic heap entropy on bounded-degree
  hardware.  Quotient words only by exact swaps of disjoint-support gates.  For an alphabet of
  size `M` whose dependence graph has maximum degree `Delta`, pair projections of the resulting
  trace monoid give
  `h_ell <= binom(M+ell-1,ell) 2^(Delta ell)`.  The associated positive heap Green reporter has
  partition function at most `(1-2^Delta z)^(-M)` and detects every depth-`s` shortcut with the
  optimized penalty
  `2^(Delta s)(1+M/s)^s(1+s/M)^M`.  For a fixed nearest-neighbour gate alphabet,
  `M=O(n)`, `Delta=O(1)`, and `s=Theta(D)`, the logarithmic capacity is at most
  `Delta s log 2+o(D)`, not the raw bound `s log M=Theta(s log n)`.  Composing with the proved
  uniform Choi phase cap upgrades the completed-phase and all-late fixed-shell plateau lower bound
  from depth `Omega(D/log n)` to `Omega(D)`, while the permanent local/Haar separator remains
  unchanged.  This does not prove
  first growth.  It sharpens the remaining quenched target to dependency-normalized heap incidence
  after return/carrier excision and removes one spurious `log n` from its entropy budget.  Trace
  monoids and their use in circuit enumeration are classical; priority is assigned, provisionally,
  only to the heap Green/static-capacity composition.  Paper proof and hostile audit:
  `../2-fully-proven/local-circuit-heap-capacity-law.md`.  The exact trace-classification theorem,
  maximum-degree bound, and cumulative-depth bound are now unconditional in Lean:
  `../3-formalized/local-circuit-trace-capacity-law.md`.  The Green reporter remains paper-only.
- 2026-08-13 -- Replaced sequential first-hit/Kraft accounting by concurrent causal accessibility.
  Trace-prefix cylinders are not prefix-free: independent successful prefixes can share one
  completion.  Under the finite heap law `pi_z(T)=z^|T|/Z(z)`, left cancellation gives the exact
  cylinder identity `pi_z(up u)=z^|u|` and exact expected prefix count `E|Pref(T)|=Z(z)`.  Taking the
  probability of the union of all successful causal prefixes produces a bounded reporter `F`, with
  exact recurrence value one, `z^C<=F`, a sharp tail upper bound, and
  `-log F=inf_(Q(hit)=1) D(Q||pi_z)`.  A soft max-over-prefix version is `1/delta`-Lipschitz
  independent of Hilbert dimension, circuit depth, and prefix count, removing the previous
  dimension-linear approximate-tube remainder.  It does not prove the fixed-time mean decay.
  Paper proof: `../2-fully-proven/concurrent-causal-heap-accessibility-law.md`.  Lean remained read
  only during refactor.
- 2026-08-13 -- Identified the exact quenched growing-replica object and its carrier law.  Replicate
  preparation heaps while keeping one common static Hamiltonian:
  `Z_r(t)=E_H F(Phi_H(t))^r`.  This is exactly the product-incidence probability for `r` independent
  causal heaps against the same occupied endpoint, and
  `Pr_H{C<=s}<=z^(-rs)Z_r`.  Entropy duality gives the action formula
  `-log Z_r=inf_q[D(q||rho_H)+r E_q J]`.  Therefore replica closure is exactly the uniform tilted-law
  gap `(1/r)D(q||rho_H)+E_q J >= s log(1/z)+kappa` **within this replica certificate**.  The replica limit detects
  `ess inf J`: source rarity is paid once and amortized by `1/r`, so growing replicas amplify the
  easiest surviving rare carrier rather than washing it out.  The empty heap proves `F=1` exactly
  on the common recurrence target and isolates that nondecaying mass once.  This supersedes raw
  incidence-normalized coarea mass as the invariant: coarea/Jacobian methods are now proof devices
  only if they establish the action gap for every source tilt.  A rare easy carrier may be harmless
  to the desired event tail but still dominate `Z_r`; it must be cut, stratified, or handled by a
  direct non-moment proof.  Physical static-local gap remains open.  Paper proof and hostile audit:
  `../2-fully-proven/quenched-causal-replica-action-law.md`.  Lean remained read only during refactor.
- 2026-08-14 -- Formalized the universal two-memory mechanism exposed by the static-centralizer
  no-go.  For nested orthogonal projections `Pi<=P`, a unitary evolution `U` fixing `P`, and any
  preparation vector with the same `Pi` component as the seed, Lean proves the exact collision
  identity
  `<Ux,y>=<u,u>+<c,q>+<r,q>`, the completed baseline
  `<Px,y>=<u,u>+<c,q>`, the single dynamic correction `<(U-P)x,y>=<r,q>`, and conserved retained
  memory norm `||c||^2+||r||^2=||x-Pi x||^2`.  For every finite nonnegative target dictionary, one
  shortcut forces an explicit inverse-dictionary dynamic alignment; exact recurrence with the seed
  in the dictionary forces the corresponding realignment.  Composing with the exact trace-capacity
  theorem replaces inverse raw-word count by the intrinsic heap scale
  `1/(choose(M+ell-1,ell)2^(Delta ell))`; commuting-gate permutations are removed before the
  collision moment.  The formal Hilbert theorem needs no finite dimension.  This proves that
  persistent non-Haar memory is compatible with circuit hardness and isolates the Brown frontier to
  one signed quenched alignment, but it does not bound that alignment for ordinary local
  Hamiltonians.  Formal cards:
  `../3-formalized/static-circuit-two-memory-orthogonality-law.md` and
  `../3-formalized/local-circuit-two-memory-capacity-law.md`.
- 2026-08-14 -- Proved a new rational-frame constraint on static recurrence.  For a uniform
  `D`-phase orbit and any finite target dictionary of size `N`, at most
  `4N exp[-(1-4 delta^2)D/4]` of the projective `k`-torsion points lie within trace distance
  `delta<1/2` of the dictionary.  At prime order every nonzero power is an automorphism, so whenever
  `4(k-1)N exp[-(1-4 delta^2)D/4]<1`, a positive explicitly bounded fraction of torsion points
  generate cyclic polygons whose complete `k-1` nonidentity vertices avoid every target.  Maximal
  projective spectral rank shadows any such polygon at arbitrarily late physical times: the
  endpoint returns while every exact rational slice `jR/k` is hard.  With bounded-dependence local
  circuit heaps, `M=O(n)`, `Delta=O(1)`, and depth `s=cD`, one may take prime
  `k=exp(eta D+o(D))`; one recurrence cycle then contains exponentially many equally spaced
  `Theta(D)`-hard slices.  Generic path-local maximal rank and the permanent same-Hamiltonian
  two-query separator compose with this result, so the same ordinary static local Hamiltonian can
  exhibit those hard recurrence polygons while remaining distinguishable from Haar at every time.
  This advances recurrence anatomy, not Brown onset: it gives neither the first selected recurrence
  time nor initial monotone/linear growth.  Paper proof and hostile audit:
  `../2-fully-proven/prime-torsion-recurrence-polygon-complexity-law.md`.
- 2026-08-14 -- Closed the dependency-free Lean core of the prime-torsion polygon law and improved
  its cap mechanism.  `PrimeTorsionOrbitAvoidance` proves the exact survivor count
  `p^d-(p-1)|bad|`.  `FiniteGridCoherenceMoment` proves the exact `2n`-th phase-coherence moment for
  every modulus `M` with `2n<M`, translated target-cap invariance, and the factorial cap bound.
  `PrimeTorsionTargetCapPolygon` composes them: if
  `(p-1)N n! (sum_i w_i^2)^n < u^(2n)`, one prime-order phase has every nonidentity power outside
  all `N` target caps.  Decoupling replica order `n` from polygon order `p` is stronger than the
  original `M=2n+1` grid presentation and preserves exponentially long polygons.  The key
  literature boundary was already formalized separately: ordinary static-local hard epochs can
  coexist with a permanent two-query separation from Haar.  Remaining frontier is now the physical
  composition through arbitrary normalized rays, autonomous late-time shadowing, circuit
  asymptotics, and ultimately first Brown onset—not finite-grid power-orbit counting.
- 2026-08-14 -- Closed the arbitrary-ray composition in Lean.  `FiniteGridChoiRayCap` embeds every
  finite cyclic phase grid into normalized diagonal Choi vectors and proves that an
  `epsilon`-cap around any normalized vector in the full `d^2`-dimensional Choi space is contained
  in one translated coherence cap whenever nonempty.  `PrimeTorsionCircuitRayPolygon` then proves
  unconditionally that
  `((p-1)N)n!d^(-n) < sqrt(1-4epsilon^2)^(2n)`, with prime `p`, `2n<p`, and
  `0<=epsilon<1/2`, produces one order-`p` polygon whose every nonidentity vertex is farther than
  `epsilon` from every one of the `N` arbitrary normalized circuit rays.  This preserves fibre
  multiplicity and the complete circuit/power union; targets need not be diagonal or grid-valued.
  Remaining frontier is now autonomous same-Hamiltonian shadowing, explicit Brown-scale heap
  instantiation, and first onset.  Formal card:
  `../3-formalized/prime-torsion-circuit-ray-polygon-law.md`.
- 2026-08-14 -- Closed autonomous same-Hamiltonian polygon shadowing in Lean.  Strict hardness at
  all nonidentity prime-grid powers plus the prime return endpoint forms one nonempty open target
  in the projective phase torus.  Maximal projective rank makes one fixed autonomous phase flow hit
  that whole target syndetically.  Consequently, under the same replica budget, after every start
  time there is a base time `tau` such that every physical slice `a.val*tau`, `a!=0 mod p`, is
  `epsilon`-hard against the complete arbitrary normalized dictionary and `p*tau` is within any
  prescribed `rho>0` of the identity ray.  No quantitative Diophantine estimate or minimum gap is
  needed.  This retires autonomous late-time shadowing.  Remaining frontier: explicit ordinary
  local-Hamiltonian/permanent-Haar composition, Brown-scale heap instantiation, and first onset.
  Formal card: `../3-formalized/prime-torsion-autonomous-circuit-polygon-law.md`.
- 2026-08-14 -- Specialized the complete autonomous polygon to ordinary fixed bounded-weight Pauli
  Hamiltonians and composed the permanent same-Hamiltonian Haar separator.  For every generic
  coefficient vector, the exact replica budget gives syndetically recurring complete hard prime
  polygons and a near-identity endpoint, while a product-stabilizer two-query signal remains
  strictly above the exact operator-normalized Haar benchmark at every real time.  This closes the
  previously separate local-Hamiltonian ensemble-transfer and permanent-locality obligations for
  late recurrence polygons.  Remaining open core is Brown-scale heap instantiation and first-onset
  growth.  Formal card:
  `../3-formalized/pauli-local-prime-torsion-circuit-polygon-law.md`.
- 2026-08-14 -- Proved and formalized the adaptive observer--spectral reciprocity law.  After
  removing the completed centralizer sector, every finite weighted history of adaptively chosen
  circuit shortcuts satisfies
  `(eta sum_j w_j)^2 <= F_Pi(Y) sum_(i,j) w_i w_j
  <x-Px,U(t_j-t_i)(x-Px)>`.  Here `F_Pi(Y)` is exactly uniform target frame energy minus the
  universal-sector norm, equivalently the squared preparation-memory norm; uniform frame energy
  is the normalized sum of all target Gram entries.  Thus target adaptation disappears and the
  obstruction factorizes into average occupied-image overlap and one stationary source recurrence
  kernel.  The universal Cauchy step is sharp for every weighted history, so no stronger pure
  Hilbert inequality can remove its square.  This retires both minimum endpoint separation and
  minimum spectral gap as wrong frontier invariants.  Brown first onset now requires two explicit
  growing-replica estimates after return/carrier excision: inverse-capacity occupied heap-image
  frame energy and a quenched centralizer-centered recurrence-energy bound for an ordinary one-draw
  local Hamiltonian.  Exact source, pair-average identity, sharpness, and product law are checked in
  Lean with only standard foundational axioms.  Formal card:
  `../3-formalized/centralizer-centered-shortcut-history-recurrence-energy-law.md`.
