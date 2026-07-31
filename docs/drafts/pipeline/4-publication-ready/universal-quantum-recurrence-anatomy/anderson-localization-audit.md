# Anderson localization and recurrence: priority and scope audit

**Audit date:** 2026-07-30  
**Status:** rewrite gate; current manuscript is not submission-ready

## Superseding result — 2026-07-31

The finite-horizon boundary recorded below has been removed.  For every
finite Hermitian hopping matrix \(T\) and every prescribed positive
off-diagonal envelope \(b_{ij}>0\), there is an onsite packet \(p\) such
that the same fixed-hopping Hamiltonian
\[
  H=T+\operatorname{diag}(p)
\]
has maximal projective spectral rank and
\[
  \sup_{t\in\mathbb R}
  \left|\langle i|e^{-itH}|j\rangle\right|<b_{ij}
  \qquad(i\ne j).
\]
Taking \(b_{ij}=C e^{-\mu d(i,j)}\) gives an all-time exponential spatial
bound for every finite site metric and every \(C,\mu>0\).
Its completed relative-phase flow is Haar on the full projective torus.
The formal capstones are
`exists_finiteAnderson_fixedHopping_maximalProjective_allTimeBelow_any`,
`exists_finiteAnderson_fixedHopping_maximalProjective_exponentialLocality_any`
and `exists_finiteAnderson_fixedHopping_exponentialLocality_fullHaar`.

This is a same-witness, fixed-hopping, all-time theorem. It proves a
stronger local--global separation than finite-window indistinguishability:
uniform spatial confinement and maximal global phase exploration coexist
indefinitely.  Standard Anderson dynamical-localization results establish
uniform-in-time spatial decay, often probabilistically or in infinite
volume; they do not appear to classify the exact rational dimension of the
same completed spectral orbit.  Conversely, rationally independent local
free-fermion constructions do not prove uniform localization.

The remaining hostile boundary is narrower but decisive. The theorem is
finite-dimensional and existential near the atomic limit. Its selected
onsite disorder scale may grow with system size and with the inverse of the
smallest prescribed envelope value. It therefore gives no volume-uniform
decay length, no
positive-probability estimate for a named random-disorder law, and no
infinite-volume or interacting microscopic MBL transfer. “Finite Anderson
all-time spatial separation” is now manuscript authorized; “universal
Anderson-localization law” remains forbidden until external priority audit
and a volume-uniform ensemble theorem close those gaps.

## Infinite comparison and priority correction — 2026-07-31

The infinite same-field theorem is exact:
\[
 \|[\tau_t(X_x),X_y]\|
 \le \min\{2,4K|t|2^{-|x-y|}\},
 \qquad
 \tau_x(F)=2^{|F|}.
\]
Its individual ingredients are not new physics. Kim, Chandran and Abanin
proved the established \(t e^{-d/(2\xi)}\) logarithmic-light-cone scaling
from exponentially localized integrals of motion
([arXiv:1412.3073](https://arxiv.org/abs/1412.3073)).
Nandkishore, Gopalakrishnan and Huse derived the local l-bit spectral tree:
after resolving \(2n\) surrounding l-bits, a local line generically splits
into \(2^{2n}\) lines
([Phys. Rev. B 90, 064203](https://doi.org/10.1103/PhysRevB.90.064203)).
Chen, Zhou, Huse and Fradkin derived the exact l-bit OTO phase and its
logarithmic crossover
([Ann. Phys. 529, 1600332](https://doi.org/10.1002/andp.201600332)).

The exact rational rank \(2^{|F|}\) is a sharper algebraic classification,
but the present explicit prime-log field deliberately enforces it. The
conjunction with the logarithmic-light-cone bound is therefore a
`[BRIDGE]`, not a Nature-level discovery.

Anderson dynamical localization supplies the correct hostile comparator.
Hamza, Sims and Stolz prove a spatially decaying commutator estimate after
taking the supremum over all real times
([Commun. Math. Phys. 315, 215--239](https://doi.org/10.1007/s00220-012-1544-6)).
That order of quantifiers is stronger than the current \(t e^{-d}\) bound.

The explicit positive all-support field has a formally proved stronger
separation:
\[
 \sup_t\|[\tau_t(X_x),X_y]\|_{\mathrm{op}}=2
 \qquad(x\ne y).
\]
At the all-false configuration, the double energy difference is
\[
 4\sum_{S\ni x,y}J_S>0;
\]
choosing its inverse half-period makes the two commutator phases antipodal.
Combining the saturation equality with the fixed-time locality bound also
proves, for the same explicit witness time,
\[
 2\le 4Kt_{xy}2^{-|x-y|}.
\]
The exact scientific statement is:

> Influence decays exponentially with distance at every fixed time, yet
> eventually reaches its algebraic maximum between every pair of sites.

This proves failure of every nontrivial time-uniform Anderson-locality
bound for the constructed interacting field. Literature already predicts
the qualitative effect; possible novelty is limited to exact delayed
all-pairs saturation, maximal finite-window rational rank, and the
same-boundary law below.

The boundary law closes the earlier disjoint-packet objection.  For
\(F_r=\{1,\ldots,r\}\), \(D_r=2^r\) and
\(b_{r,S}=J_{\{0,r+1\}\cup S}\), adjoining site \(r+1\) doubles local-flip
rank from \(D_r\) to \(2D_r\), with the new half exactly the packet
\((b_{r,S})_{S\subseteq F_r}\).  The identical coefficients obey
\[
 2D_r\sum_S|b_{r,S}|\le K,\qquad
 2D_r\delta N_{r,\delta}\le K.
\]
If every new coefficient exceeds threshold \(\delta\), then
\[
 2\delta D_r^2\le K.
\]
This is `[LEAN-PROVED]` and is a coefficient-resolution theorem, not a
device-noise or finite-time distinguishability result.

## Proposed bridge

For every finite exact l-bit Hamiltonian
\[
  H_J=\sum_{S\subseteq I}J_S Z_S,
\]
the projective recurrence dimension is
\[
  \boxed{
  \tau(H_J)=
  \dim_{\mathbb Q}\operatorname{span}_{\mathbb Q}
  \{J_S:S\ne\varnothing\}.}
\]
Together with the projective relation law,
\[
  \boxed{
  \tau(H_J)+
  \operatorname{rank}_{\mathbb Q}L_{E_J}^{\mathrm{proj}}
  =2^{|I|}-1.}
\]

For rationally independent one-body coefficients and no higher interaction,
\[
  \tau=|I|,\qquad
  \operatorname{rank}_{\mathbb Q}L_{E_J}^{\mathrm{proj}}
  =2^{|I|}-1-|I|.
\]
An interacting l-bit Hamiltonian can retain exactly the same product
eigenbasis and every l-bit charge while attaining
\[
  \tau=2^{|I|}-1,\qquad
  L_{E_J}^{\mathrm{proj}}=\{0\}.
\]

The exact interpretation earned by the theorem is:

> Support geometry restricts allowed interaction coefficients. Their
> arithmetic determines projective recurrence rank.

## What is new and what is not

The qualitative statement that interactions suppress revivals in localized
matter is not new. Vasseur, Parameswaran and Moore already found that
interactions suppress localized revivals after the many-body dephasing
scale: [Quantum revivals and many-body localization](https://arxiv.org/abs/1407.4476).
Huse, Nandkishore and Oganesyan already described exponentially decaying
l-bit interactions producing dephasing without pseudospin flips:
[Phenomenology of fully many-body-localized systems](https://arxiv.org/abs/1408.4297).

Candidate novelty is narrower and exact:

1. complete rational classification of projective recurrence dimension by
   l-bit coefficients;
2. exact conservation of the complementary relation budget;
3. exact \(O(N)\)-to-\(2^N-1\) separation within one fixed product
   eigenbasis;
4. exact bounded-range ceiling
   \[
     \tau\le n\,2^{R+1};
   \]
5. one absolutely summable countable coefficient field with one explicit
   origin-dependent exponential support envelope and maximal rank on every
   finite embedded window;
6. exact top-coefficient--full-cube-relation-fracture--minimum-replica-depth
   identity and its calibrated finite-window response;
7. exact support-by-support elapsed-time wall crossing in a monomially
   scaled l-bit family;
8. exact equality between Hamiltonian temporal rank and the rank visible
   to the uniform l-bit product state's survival observable.

## Closest literature

| Source | Collision | Difference from candidate theorem |
|---|---|---|
| [Vasseur, Parameswaran and Moore (2015)](https://arxiv.org/abs/1407.4476) | Interactions add dephasing frequencies and suppress localized revivals | No exact full-spectrum rational-rank or relation-budget theorem |
| [Huse, Nandkishore and Oganesyan (2014)](https://arxiv.org/abs/1408.4297) | All-order quasi-local l-bit interactions, dephasing without transport | l-bit phenomenology, not recurrence arithmetic |
| [Serbyn, Papić and Abanin (2013)](https://arxiv.org/abs/1305.5554) | Complete localized integrals of motion and non-equilibrium implications | Assumes locality of perturbations on eigenstates; no recurrence rank |
| [Serbyn and Abanin (2017)](https://arxiv.org/abs/1701.07772) | Loschmidt-echo distinction between MBL and Anderson insulators | Echo under two Hamiltonians and finite-time power laws, not exact recurrence of one orbit |
| [Imbrie (2016)](https://arxiv.org/abs/1403.7837) | Rigorous quasi-local diagonalization of a random spin chain | Localization follows a level-attraction assumption; no rational independence theorem |
| [Mierzejewski, Kozarzewski and Prelovšek (2018)](https://arxiv.org/abs/1708.08931) | \(2^M-1\) quasi-local integrals of motion on \(M\) sites | Counts independent conserved operators, not rationally independent coefficients or phases |
| [Riddell, Pagliaroli and Alhambra (2023)](https://arxiv.org/abs/2206.07541) | Generic many-body recurrence can be doubly exponential; free recurrence is earlier | Ambient genericity and recurrence bounds, not localized coefficient classification |
| [Riddell and Bertini (2024)](https://arxiv.org/abs/2404.12100) | Rationally independent local free fermions and their non-Poisson higher moments | No interacting localized \(2^N-1\) rank growth |
| [Campos Venuti (2015)](https://arxiv.org/abs/1509.04352) | Recurrence-time scaling in generic and quasi-free systems | No fixed-localized-basis interaction law |
| [Huang and Harrow (2020)](https://arxiv.org/abs/1907.13392) | Algebraic exceptional-set arguments for generic local perturbations | Perturbations destabilize localization; no exact l-bit recurrence law |

## Strongest microscopic Anderson bridge found

For a finite \(N\)-site one-particle Anderson matrix
\[
  h(\omega)=T+\operatorname{diag}(\omega_1,\ldots,\omega_N)
\]
with an absolutely continuous joint disorder law, the strongest candidate
bridge is almost-sure rational independence of the \(N\) one-particle
eigenvalues. The proof route is an algebraic exceptional-set argument: for
each nonzero integer relation, symmetrize over eigenvalue permutations,
show the resulting spectral polynomial is nonzero by scaling the diagonal
disorder, and remove its measure-zero zero set.

This candidate is not yet formalized and therefore is not manuscript
authorized. If proved, its full spinless-fermion Fock lift would give
\[
  \tau=N,\qquad
  \operatorname{rank}_{\mathbb Q}L^{\mathrm{proj}}=2^N-1-N.
\]
In a fixed nontrivial \(m\)-particle sector, the expected exact values are
\[
  \tau=N-1,\qquad
  \operatorname{rank}_{\mathbb Q}L^{\mathrm{proj}}
  =\binom Nm-N.
\]
The loss of one direction is physically important: coherence across
particle-number sectors cannot be assumed under \(U(1)\) superselection.

This bridge would sharpen the noninteracting endpoint but would not supply
the interacting headline. Free Fock subset sums retain exact rectangle
relations even when every one-particle energy is nonresonant. The
Nature-relevant missing theorem is maximal projective rank for a standard
interacting disordered Hamiltonian in a proved localized regime. No such
result was found in the corpus or literature.

Related scope controls:

- Klein--Molchanov prove simplicity of Anderson eigenvalues, not complete
  rational independence:
  [Simplicity of eigenvalues in the Anderson model](https://arxiv.org/abs/math-ph/0503061).
- Imbrie's full diagonalization theorem uses a level-attraction assumption
  rather than deriving the needed nonresonance for the standard model.
- Rigorous random-field XXZ localization results do not currently provide
  the all-spectrum rational-relation theorem needed here.
- Spin-independent Anderson--Hubbard retains non-Abelian spin symmetry, so
  a full-MBL transfer is obstructed unless symmetry sectors and disorder
  structure are treated explicitly.

## Infinite and locality boundary

One fixed coefficient field on all finite supports of \(\mathbb N\) is now
proved to satisfy
\[
  \sum_S |J_S|<\infty,\qquad
  |J_S|\le
  2^{-(|S|+\max S+\operatorname{diam}S)}
\]
and to have rank \(2^{|\Lambda|}-1\) on every finite embedded window
\(\Lambda\). This proves that this explicit origin-dependent summable
envelope does not force a finite-window recurrence-rank ceiling.

The same field now defines a bounded continuous energy on the full infinite
Boolean configuration space, and the nested first-\(n\)-site energies
converge to it uniformly with error bounded by the omitted absolute
interaction mass. It also generates a reversible strongly continuous
one-parameter group of complex-linear uniform-norm isometries on continuous
configuration amplitudes. This still is not a theorem about global
recurrence of an infinite spectrum or Hilbert-space unitary dynamics; no
configuration measure or \(L^2\) multiplication operator is selected.

Fixed finite range behaves differently inside the commuting diagonal l-bit
class:
\[
  \tau\le n\,2^{R+1}.
\]
The ceiling is intrinsic to bounded support range and commutativity, not to
locality in general. A finite tensor-local extension theorem proves dense,
residual, full-measure maximal projective rank in the complete
onsite-plus-edge slice once a connected transition witness exists. It does
not yet identify that transition with a physical endpoint operator in a
standard random-field chain.

## Forbidden claims

- First discovery that interactions suppress localized revivals.
- First connection between Anderson/MBL physics and recurrence.
- Projective rank distinguishes localized, ergodic or chaotic phases.
- Maximal rank implies transport, thermalization, chaos or ETH.
- Arbitrary microscopic interacting models remain localized.
- Standard random-field XXZ or Anderson--Hubbard samples have maximal rank.
- Doubly exponential many-body recurrence is new.
- The \(2^N-1\) count of local integrals of motion is new.
- Exact rational rank is noise-robust or directly measurable at finite time.
- “Temporal dimension” is a dimension of spacetime.
- An infinite system has a finite global spectrum or a global exact return.

Poisson versus Wigner--Dyson statistics do not determine exact rational
rank. Continuous ensembles of either type may have maximal projective rank
almost surely.

## Nature gate

Hostile verdict: **reject the present Anderson/MBL framing as a Nature
claim**. The qualitative physics was substantially anticipated, while
exact rational rank is discontinuous and naturally infinite-time.

Required promotion path:

1. construct an \(L^2\) realization of the proved infinite evolution if a
   Hilbert-space claim is needed, or prove the law for a standard localized
   ensemble;
2. extend the proved ideal support-by-support elapsed-time wall crossing to
   a bounded-height, finite-margin and noise-stable classifier;
3. replace the ambient full-configuration Walsh cost by a support-local
   protocol with controlled quasi-local tail contamination;
4. transfer the generic finite local-extension theorem to an actual
   microscopic endpoint-local disordered chain while localization persists;
5. rerun hostile priority review after these theorems.

Until those gates close, the manuscript may use **exact l-bit
localization** as a theorem class and Anderson localization as motivation,
not as a proved microscopic scope claim.
