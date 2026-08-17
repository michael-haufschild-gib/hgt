# Centralizer-centered circuit-collision and design-barrier law

- **ID:** `centralizer-centered-circuit-collision-and-design-barrier-law`
- **Stage:** 2 -- fully proved on paper
- **Type:** theorem / static-versus-completed transfer / norm no-go
- **Parents:** `all-replica-static-centralizer-planar-separation-law.md`,
  `gate-walk-green-bellman-tropicalization-law.md`
- **Status:** `[PAPER-PROVED] [FRONTIER ADVANCE] [NOVELTY PROVISIONAL] [LEAN DEFERRED]`
- **Date:** 2026-08-10

## Public sentence

Randomizing the circuit target can erase every oscillatory memory of a static Hamiltonian exactly,
at every physical time.  But before circuit capacity is reached, there are provably too few shallow
targets for this erasure to hold in any global Hilbert--Schmidt norm.  The Brown frontier is therefore
a signed directional cancellation against the actual circuit moment, not convergence to a design and
not norm decay of the centered static propagator.

## 1. Abstract centralizer-centered transfer

Let `V` be a finite-dimensional complex Hilbert space, let `L=L^*` on `V`, and let

\[
 P=\mathbf 1_{\{0\}}(L)                                                   \tag{1}
\]

be the orthogonal projection onto `ker L`.  Let `N subset ker L` be a fixed subspace with orthogonal
projection `Pi`.  For `x,M in V`, put

\[
 \delta_t=(e^{-itL}-P)x.                                                   \tag{2}
\]

### Theorem A -- exact moving-centralizer decomposition

For every real `t`,

\[
 \boxed{
 \langle e^{-itL}x,M\rangle-\langle Px,M\rangle
 =\langle\delta_t,(I-P)M\rangle
 =\langle\delta_t,(I-\Pi)M\rangle .}                                      \tag{3}
\]

Consequently

\[
 \boxed{
 \left|\langle e^{-itL}x,M\rangle-\langle Px,M\rangle\right|
 \le \|(I-P)x\|\,\|(I-P)M\|
 \le \|x\|\,\|(I-\Pi)M\| .}                                             \tag{4}
\]

In particular, if `M in N`, the physical-time matrix coefficient equals its completed centralizer
baseline for every `t`; no time averaging and no ensemble averaging are required.

### Proof

Functional calculus gives `e^(-itL)P=P` and

\[
 e^{-itL}-P=e^{-itL}(I-P).                                                 \tag{5}
\]

Thus `delta_t` belongs to `(ker L)^perp`, proving the first equality in `(3)`.  Since
`N subset ker L`, `delta_t` is also orthogonal to `N`, proving the second equality.  Cauchy--Schwarz
gives the first inequality in `(4)`.  Distance to the larger space `ker L` is no greater than distance
to `N`, so `||(I-P)M|| <= ||(I-Pi)M||`; both projections are contractions, proving the rest.

## 2. Exact application to static evolution and a circuit dictionary

Let `K=C^D`, let `H=H^*`, and let `rho_0` be a pure-state density.  At replica order `r>=1`, set

\[
 x_r=\rho_0^{\otimes r},\qquad
 H_{[r]}=\sum_{a=1}^r I^{\otimes(a-1)}\otimes H\otimes I^{\otimes(r-a)},
 \qquad L_{H,r}=\operatorname{ad}_{H_{[r]}}.                              \tag{6}
\]

Let `P_(H,r)` project onto `ker L_(H,r)`.  Let `G` be a finite gate alphabet of cardinality `M>=2`
containing the identity.  Every circuit of length at most `s` may therefore be padded to a word in
`G^s`.  Write `N=M^s`, let `sigma_w` be the pure endpoint density of word `w`, and define the exact
length-`s` random-circuit moment

\[
 \mathcal M_{s,r}={1\over N}\sum_{w\in G^s}\sigma_w^{\otimes r}.           \tag{7}
\]

For `rho_t=e^(-itH)rho_0e^(itH)`, define

\[
 A_{s,r}(H,t)=\langle\rho_t^{\otimes r},\mathcal M_{s,r}\rangle_{HS},
 \qquad
 \bar A_{s,r}(H)=\langle P_{H,r}x_r,\mathcal M_{s,r}\rangle_{HS}.          \tag{8}
\]

The first quantity is the collision probability against one uniformly random padded circuit,
raised to replica order `r`; the second is its exact completed spectral baseline.

### Theorem B -- one scalar absorbs the complete circuit union

For every squared-fidelity threshold `0<a<=1`,

\[
 \boxed{
 \mathbf 1_{\{\max_{w\in G^s}\operatorname{Tr}(\rho_t\sigma_w)\ge a\}}
 \le N a^{-r} A_{s,r}(H,t).}                                               \tag{9}
\]

Moreover

\[
 \boxed{
 A_{s,r}(H,t)-\bar A_{s,r}(H)
 =\left\langle
   (e^{-itL_{H,r}}-P_{H,r})x_r,\mathcal M_{s,r}
  \right\rangle_{HS}.}                                                    \tag{10}
\]

Let `Pi_(D,r)` be orthogonal projection onto the commutant of collective conjugation by every
`U in U(D)`.  Since this universal permutation algebra is contained in every quenched centralizer,

\[
 \boxed{
 |A_{s,r}(H,t)-\bar A_{s,r}(H)|
 \le \|(I-\Pi_{D,r})\mathcal M_{s,r}\|_{HS}.}                             \tag{11}
\]

If the target moment lies in the universal permutation algebra--in particular, if the target
distribution is an exact projective `r`-design--then

\[
 \boxed{A_{s,r}(H,t)=\bar A_{s,r}(H)\quad\text{for every `H` and `t`.}}     \tag{12}
\]

### Proof

If one word has fidelity at least `a`, its one summand in `(7)` is at least `a^r/N`, which proves
`(9)`.  Equation `(10)` is Theorem A with `L=L_(H,r)`.  The collective permutation algebra commutes
with `H_[r]` for every `H`, so it is a subspace of `ker L_(H,r)`.  Pure `x_r` has Hilbert--Schmidt
norm one; `(11)` and `(12)` follow from `(4)`.

The key point is the order of operations.  The complete word family is averaged before the static
propagator is centered.  The moving centralizer is retained in `bar A`; it is neither discarded nor
replaced by the smaller universal permutation algebra.

## 3. Completed-phase capacity term

Assume `H` has `D` occupied eigenlines and the seed is spectrally flat,

\[
 \psi_0={1\over\sqrt D}\sum_{j=1}^D e_j.                                  \tag{13}
\]

For every unit target `z`, Steinhaus orthogonality gives

\[
 \int_{\mathbb T^{D-1}}
  |\langle z,U_\varphi\psi_0\rangle|^{2r}\,d\varphi
 \le {r!\over D^r}.                                                       \tag{14}
\]

Indeed, after projecting `z` to the occupied spectral space and writing its coordinates `c_j`, the
left side is

\[
 {1\over D^r}\sum_{|k|=r}
 \left({r!\over\prod_j k_j!}\right)^2\prod_j|c_j|^{2k_j}
 \le {r!\over D^r}\left(\sum_j|c_j|^2\right)^r
 \le {r!\over D^r}.                                                       \tag{15}
\]

Averaging `(14)` over the padded circuit words yields

\[
 \boxed{\bar A_{s,r}(H)\le r!D^{-r}}                                      \tag{16}
\]

whenever the completed centralizer is the full occupied phase completion; the same statement holds
with the actual completed spectral subtorus when its corresponding target moment bound is supplied.
For an ensemble `mu` of Hamiltonians satisfying `(16)`, equations `(9)`--`(10)` give the exact
criterion

\[
 \boxed{
 \mu\{\text{an `s`-gate target has fidelity at least `a` at time `t`}\}
 \le Na^{-r}\left({r!\over D^r}+\Delta_{s,r}(t)\right),}                   \tag{17}
\]

where the signed, centralizer-centered directional defect is

\[
 \Delta_{s,r}(t)=
 \int\left\langle
 (e^{-itL_{H,r}}-P_{H,r})x_r,\mathcal M_{s,r}
 \right\rangle_{HS}\,d\mu(H).                                            \tag{18}
\]

No absolute value is inserted in `(18)`.  It is exactly the signed cancellation the shortcut event
needs.  If desired, its positive part may replace it on the right of `(17)`.

## 4. Why target-design norm transfer cannot close the Brown regime

Theorem B suggests making `mathcal M_(s,r)` close to the universal permutation algebra.  The next
theorem proves that this norm strategy is incompatible with the very replica regime in which the
completed-phase capacity estimate is useful.

Let

\[
 h_{D,r}=\dim\operatorname{Sym}^r(\mathbb C^D)
 ={D+r-1\choose r},\qquad
 \Omega_{D,r}={\Pi_{\rm sym}\over h_{D,r}}.                               \tag{19}
\]

For any probability distribution `nu` supported on at most `N` pure states, put

\[
 \mathcal M_\nu=\int (|z\rangle\langle z|)^{\otimes r}\,d\nu(z).           \tag{20}
\]

The collective-unitary twirl of every summand in `(20)` is `Omega_(D,r)`.  Hence

\[
 (I-\Pi_{D,r})\mathcal M_\nu=\mathcal M_\nu-\Omega_{D,r}.                 \tag{21}
\]

### Theorem C -- support-rank square-root barrier

Every `mathcal M_nu` in `(20)` obeys

\[
 \boxed{
 \|(I-\Pi_{D,r})\mathcal M_\nu\|_{HS}^2
 =\operatorname{Tr}(\mathcal M_\nu^2)-{1\over h_{D,r}}
 \ge {1\over\min\{N,h_{D,r}\}}-{1\over h_{D,r}}.}                       \tag{22}
\]

In particular, if `N<h_(D,r)`,

\[
 \boxed{
 \|(I-\Pi_{D,r})\mathcal M_\nu\|_{HS}
 \ge\sqrt{{1\over N}-{1\over h_{D,r}}}.}                                 \tag{23}
\]

The constant is sharp whenever `N` orthogonal replica vectors exist and are given equal weight.

### Proof

The moment `M_nu` is positive, has trace one, is supported on `Sym^r(C^D)`, and has rank at most
`min{N,h_(D,r)}`.  Since `Omega_(D,r)` is normalized identity on that symmetric space,

\[
 \operatorname{Tr}(\mathcal M_\nu\Omega_{D,r})={1\over h_{D,r}},\qquad
 \operatorname{Tr}(\Omega_{D,r}^2)={1\over h_{D,r}}.                      \tag{24}
\]

Expanding the square proves the equality in `(22)`.  For every positive trace-one matrix of rank
`q`, Cauchy--Schwarz on its nonzero eigenvalues gives `Tr(M^2)>=1/q`, proving the inequality.
Uniform mass on `N` orthogonal vectors has purity `1/N`, proving sharpness.

### Corollary D -- exact incompatibility with the useful capacity regime

If the completed-phase moment in `(16)` is strong enough even to make the raw `N`-target bound
nontrivial,

\[
 Na^{-r}{r!\over D^r}<1,                                                   \tag{25}
\]

then necessarily

\[
 \boxed{
 N<a^r{D^r\over r!}\le {D^r\over r!}\le {D+r-1\choose r}=h_{D,r}.}       \tag{26}
\]

In fact `(26)` gives `N/h_(D,r)<a^r`, so `(23)` sharpens to

\[
 \boxed{
 \|(I-\Pi_{D,r})\mathcal M_\nu\|_{HS}
 >\sqrt{{1-a^r\over N}}.}                                                \tag{27}
\]

Thus the rank barrier applies throughout the entire capacity-producing replica regime.  For fixed
`0<a<1` and growing `N,r`, the universal norm defect is forced onto the square-root support scale
`N^(-1/2)`, whereas one padded shortcut in `(9)` must be detected at scale `a^r N^(-1)`.

The last inequality in `(26)` follows termwise from

\[
 {D+r-1\choose r}={D(D+1)\cdots(D+r-1)\over r!}\ge {D^r\over r!}.         \tag{28}
\]

This is a structural impossibility, not a missing mixing-time estimate.  No improvement to an
operator- or Hilbert--Schmidt-norm approximation of the circuit moment by a universal design can
reach the one-word witness scale before the completed-phase moment has already lost its capacity
advantage.

## 5. Conjecturing protocol

### C0 -- randomize the target to remove the moving centralizer

**Verdict:** `[PROVED EXACTLY]` by Theorems A--B.

An exact projective replica design lies in every quenched centralizer, so physical and completed
collision probabilities agree at every time.  This is stronger than static ensemble dephasing.

### C1 -- an approximate design in Hilbert--Schmidt norm closes the circuit union

**Verdict:** `[FALSIFIED SHARPLY]` by Theorem C and Corollary D.

The support-rank defect is `Omega(N^(-1/2))` precisely when completed phase can beat `N` targets.
The shortcut witness is only `a^r/N`.  Better random-circuit mixing constants cannot repair this
square-root mismatch.

### C2 -- center in quenched norm before pairing with the circuit moment

**Verdict:** `[FALSIFIED BY THE PARENT CENTRALIZER LAW]`.

For fixed `H`, the centered propagator is unitary on the oscillatory complement, so its operator
norm is one at every time.  Norm decay cannot be recovered by quotienting the universal permutation
algebra or the larger quenched centralizer.

### C3 -- retain the signed directional defect

**Verdict:** `[EXACT REPRESENTATION PROVED; QUANTITATIVE BOUND OPEN]`.

Equation `(18)` is the strongest survivor.  It keeps all four structures that the failed routes
discarded: the moving quenched centralizer, growing replicas, the actual local-circuit moment, and
signed static-ensemble cancellation.  It has no maximum and no circuitwise union, but it still pays
the exact padded-word factor `N` in `(17)`.

The next load-bearing theorem is therefore

\[
 \Delta_{s,r}(t)
 \le \delta_{n,t,s}\,{a^r\over N}-{r!\over D^r},                         \tag{29}
\]

or any directly equivalent upper bound making the right side of `(17)` small, at
`r=Theta(D)`, `s=Theta(D/log M)`, and the geometric Brown-skeleton times.  It must be proved by
directional signed cancellation.  Replacing `(18)` by an absolute norm, a positive moment channel,
or design distance is now formally ruled out.

## 6. Relation to the full static-local frontier

The theorem does not prove Brown--Susskind growth.  It makes one genuine reduction and closes one
false escape route:

1. the complete padded circuit dictionary is converted into one centralizer-centered scalar
   matrix coefficient `(18)`;
2. completed spectral capacity is separated exactly as `r!D^(-r)`;
3. realization-dependent zero modes are paid by `P_(H,r)`, not silently deleted;
4. every global norm/design approximation is proved too weak in the same regime;
5. only an anisotropic, signed estimate against the actual circuit moment remains.

This is compatible with the all-replica local-word leakage theorem: Hall/Casimir leakage may supply
directional cancellation after pairing with `mathcal M_(s,r)`, but its scalarized span or norm cannot.
It is also compatible with gate-walk tropicalization: positive finite-temperature linearization pays
word entropy, while `(18)` identifies the exact signed quantity that would have to repay it.

## 7. Hostile audit

1. **No ramp proved.**  Equation `(28)` is open.  No growth, onset, plateau time, or recurrence time
   follows from this card alone.
2. **Flat spectral seed in `(14)`.**  A general seed replaces `D^(-1)` by its collision/weight
   profile.  No flatness claim is made for generic product-state eigenvectors.
3. **Finite gate alphabet.**  Continuous gates require a measure-small-ball witness in place of the
   one-word mass `N^(-1)`.
4. **State version of the rank barrier.**  A Choi-unitary target orbit has a different representation-
   theoretic effective rank.  Theorem A and Theorem B are representation-independent, but Theorem C
   must be replaced by the corresponding Haar-orbit moment spectrum before quoting it verbatim for
   restricted Choi targets.
5. **Signed defect can be negative.**  This helps the upper bound.  Any proof may bound its positive
   part or its ensemble integral, but may not insert pointwise absolute values and still claim to
   have crossed the frontier.
6. **Novelty boundary.**  Orthogonal projection, Schur--Weyl fixed algebras, projective designs,
   rank--purity bounds, and Steinhaus moments are standard separately.  Targeted search found
   isospectral-twirling and design literature but no theorem composing the exact moving-centralizer
   identity `(10)`, padded-circuit capture `(9)`, and the finite incompatibility `(25)--(26)`.
   Priority remains provisional.
7. **Lean status.**  No theorem from this card is authorized for a final manuscript until the finite
   Hilbert-space core is formalized and axiom-audited after the active corpus refactor.

## 8. External boundary checked

- Haferkamp et al., *Linear growth of quantum circuit complexity*, arXiv:2106.05305, proves exact
  linear growth for refreshed random circuits, not robust static-Hamiltonian growth.
- Haferkamp, *On the moments of random quantum circuits and robust quantum complexity*,
  arXiv:2303.16944, obtains constant-error square-root growth and leaves constant-error linear growth
  conditional on a Fourier-support conjecture.
- Leone, Oliviero and Hamma, *Isospectral twirling and quantum chaos*, arXiv:2011.06011, develops
  isospectral twirls and chaos probes, not the circuit-union centralizer criterion or design barrier
  above.
- Roy and Scott, *Weighted complex projective 2-designs from bases*, arXiv:quant-ph/0703025, and
  the classical Welch-bound literature contain the projective moment identity and support-size
  obstruction.  No novelty is claimed for that rank bound by itself.
- Cui et al., *Random unitaries from Hamiltonian dynamics*, arXiv:2510.08434, proves permanent
  efficient distinguishability of constant-local static dynamics from Haar randomness; it does not
  prove robust circuit-complexity growth.

These sources confirm that `(28)`, not any theorem already claimed here, remains beyond current
published robust-complexity results.

## 9. Lean plan after refactor

1. finite-dimensional self-adjoint projection identity `(3)`--`(4)`;
2. padded finite-dictionary moment and capture law `(7)`--`(10)`;
3. collective-commutant inclusion and exact-design equality `(11)`--`(12)`;
4. projective moment rank--purity barrier `(19)`--`(23)`;
5. finite incompatibility `(25)`--`(27)`;
6. targeted `lake env lean` check and `#print axioms` audit, then one final module build.

## Lean progress -- Theorem C, the purity half of the square-root barrier

`formal/GaloisForLFunctions/HTGeometry/PurityRankBarrier.lean` (new, umbrella-wired, axiom-clean).

| Card item | Declaration |
|---|---|
| **the purity bound**: a probability vector on `q` entries has squared mass at least `1/q` | `inv_card_le_sum_sq` |
| the uniform distribution attains it, so the constant of `(23)` is sharp | `sum_sq_const_eq_inv_card` |
| **the deficit of `(22)`**: a purity above `1/q` sits at least `1/q - 1/h` above the reference `1/h` | `deficit_ge` |

`inv_card_le_sum_sq` is the card's "for every positive trace-one matrix of rank `q`, Cauchy--Schwarz
on its nonzero eigenvalues gives `Tr(M²) ≥ 1/q`", stated at the level of the eigenvalue vector where
the Cauchy--Schwarz actually happens.  `sum_sq_const_eq_inv_card` is the sharpness clause: uniform
mass on `N` orthogonal replica vectors has purity exactly `1/N`.

### The expansion and the rank bound are closed

`formal/GaloisForLFunctions/HTGeometry/SymmetricProjectionPurityBarrier.lean` (new, umbrella-wired,
axiom-clean) proves both halves of `(22)` in projection form, which is how the card's rank
hypothesis actually enters, and the arithmetic of Corollary D.

| Card item | Declaration |
|---|---|
| the squared Hilbert--Schmidt norm is `Tr(AᴴA)` | `hsNormSq_eq_trace` |
| Cauchy--Schwarz for the Hilbert--Schmidt pairing | `abs_re_trace_le` |
| **the purity bound**: a trace-one Hermitian moment carried by a rank-`q` projection has `Tr(M²) >= 1/q` | `inv_le_hsNormSq_of_support` |
| **the expansion `(24)`--`(22)`**: `‖M - Ω‖²_HS = Tr(M²) - 1/h`, with both `Tr(M Ω)` and `Tr(Ω²)` equal to `1/h` | `hsNormSq_sub_normalized_projection` |
| **`(22)`, `(23)`**: hence `‖M - Ω‖²_HS >= 1/q - 1/h` | `hsNormSq_sub_normalized_projection_ge` |
| **`(28)`**: `D^r <= r! binom(D+r-1, r)` | `pow_le_factorial_mul_choose` |
| **`(26)`**: a nontrivial raw target bound forces `N < h_{D,r}` | `lt_choose_of_capacity_bound` |

The rank hypothesis is carried by a support projection `Q` with `Q M = M` and `Tr Q = q` -- the
statement "positive, trace one, rank at most `q`" in the form the Cauchy--Schwarz argument uses, so
no spectral decomposition is needed.

### What remains

The construction of the concrete data: the symmetric projection `Π_sym` of `(19)` with
`Tr Π_sym = h_{D,r}`, the moment `M_ν` of `(20)` with its support projection, and the twirl identity
`(21)`.  Theorems A and B are untouched.
