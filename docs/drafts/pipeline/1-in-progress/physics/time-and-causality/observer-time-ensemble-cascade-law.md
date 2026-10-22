# Observer-time ensemble cascade law

- **ID:** `observer-time-ensemble-cascade-law`
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL LAW / SINGULAR PERTURBATION / QUANTUM RECURRENCE
- **Source:** valued spectral-constraint programme
- **Scientific status:** `[PAPER-PROVED]`
  `[CHARACTER LAW LEAN-PROVED]`
  `[RANK CONSERVATION LEAN-PROVED]`
  `[FINITE AND COUNTABLY INFINITE FULL WEAK-MEASURE LIFT LEAN-PROVED]`
  `[ACTUAL UNIFORM-TIME PHASE LAW LEAN-PROVED]`
  `[LOCALITY-TO-VALUATION BRIDGE LEAN-PROVED]`
  `[EXPONENTIAL TWO-REPLICA CONSTRAINT RANK LEAN-PROVED]`
  `[NOVELTY AUDIT OPEN]`

## Question

Why does an arbitrarily weak interaction appear to change a quantum
system's recurrence statistics discontinuously, and what does any finite
observer see before the infinite-time limit?

## Candidate universal law

> Every observer sees time through a valued lattice of spectral
> constraints. A constraint lost at perturbative order \(r\) becomes one
> temporal direction at the same order and becomes operationally visible
> on the universal horizon \(T\asymp g^{-r}\).

This is not a claim that spacetime has extra coordinates. “Temporal
dimension” means rank of the compact phase ensemble accessible to a stated
observer.

## Exact theorem

Let \(d<\infty\), let
\[
 \omega(g)=(\omega_1(g),\ldots,\omega_d(g))\in\mathbb R^d
\]
be real analytic near \(g=0\), and let
\(\Gamma=\mathbb Z^d\) be the observer's character lattice. For
\(k\in\Gamma\), define
\[
 \delta_k(g)=k\cdot\omega(g),\qquad
 v(k)=\operatorname{ord}_{g=0}\delta_k(g)
      \in\mathbb N_0\cup\{\infty\}.
\]
Put
\[
 F^r=\{k:v(k)\ge r\}
     =\ker\!\left(k\mapsto
       (k\cdot\omega^{(0)}(0),\ldots,
        k\cdot\omega^{(r-1)}(0)/(r-1)!)\right).
\]
Let
\[
 d_r=\operatorname{rank}_{\mathbb Q}
 \operatorname{im}\!\left(
   \Gamma\otimes\mathbb Q\longrightarrow\mathbb R^r
 \right).
\]
For \(g>0\), sample \(u\) uniformly from \([-1,1]\) and observe the torus
phase
\[
 X_{g,r,\tau}(u)
  =\exp\!\left(i\tau g^{-r}u\,\omega(g)\right)
  \in\mathbb T^d.
\]
Write \(\mu_{g,r,\tau}\) for its probability law.

Then, for every \(r\in\mathbb N_0\), every \(\tau>0\), and every
\(k\in\Gamma\),
\[
 \boxed{
 \lim_{g\downarrow0}\widehat\mu_{g,r,\tau}(k)=
 \begin{cases}
 0,&v(k)<r,\\[2mm]
 \operatorname{sinc}(\tau\,a_r(k)),&v(k)=r,\\[2mm]
 1,&v(k)>r,
 \end{cases}}
 \tag{1}
\]
where
\[
 a_r(k)=k\cdot\omega^{(r)}(0)/r!.
\]
These coefficients determine one unique probability measure
\(\mu_{r,\tau}\) on \(\mathbb T^d\), and
\[
 \boxed{\mu_{g,r,\tau}\Longrightarrow\mu_{r,\tau}.}
 \tag{2}
\]
Moreover,
\[
 \boxed{d_r+\operatorname{rank}_{\mathbb Q}
   (F^r\otimes\mathbb Q)=d,}
 \tag{3}
\]
and hence, for \(r\le s\),
\[
 \boxed{d_s-d_r=
   \operatorname{rank}(F^r)-\operatorname{rank}(F^s).}
 \tag{4}
\]

For a finite spectrum, take \(\Gamma\) to be the projective character
lattice
\[
 \{k\in\mathbb Z^I:\sum_i k_i=0\}.
\]
For any finite-dimensional observer, restrict this lattice to the
characters accessible to that observer. Equations `(1)`--`(4)` are
unchanged.

For every countable spectrum, replace \(\mathbb Z^d\) by the
finite-support character group \(\mathbb Z^{(I)}\) and the finite torus by
\(\mathbb T^I\). Finite-support Fourier characters are uniformly dense in
all continuous functions on the full compact product torus. Hence
convergence of every finite-support coefficient determines and forces weak
convergence of the complete probability law, not merely convergence of
cylinder reporters.

## Proof

Exact integration gives
\[
 \widehat\mu_{g,r,\tau}(k)
 =\frac12\int_{-1}^{1}
   e^{i\tau g^{-r}u\delta_k(g)}\,du
 =\operatorname{sinc}\!\left(
   \tau\delta_k(g)/g^r\right).
 \tag{5}
\]
If \(v(k)=q<\infty\), analyticity gives
\[
 \delta_k(g)=a_q(k)g^q+o(g^q),\qquad a_q(k)\ne0.
\]
The sinc argument therefore tends to infinity in modulus for \(q<r\),
to \(\tau a_r(k)\) for \(q=r\), and to zero for \(q>r\). If
\(v(k)=\infty\), analyticity makes \(\delta_k\) identically zero near the
origin. This proves `(1)`.

Probability measures on the finite torus form a compact space in the weak
topology. Every subnet therefore has a cluster measure. Integration
against a torus character is continuous, so every cluster measure has the
Fourier coefficients in `(1)`. Finite Fourier polynomials are uniformly
dense in all continuous complex functions on \(\mathbb T^d\).
Consequently two probability measures with those coefficients agree on
every continuous reporter and are equal. There is thus one cluster point,
which proves `(2)`.

Equation `(3)` is rank-nullity for the jet map. Equation `(4)` follows by
subtraction because the kernels form a decreasing filtration.
\(\square\)

## What this says that prior results do not

An infinite-time genericity statement says that any nonzero perturbation
can destroy resonances. It does not say what a finite observer sees as the
perturbation vanishes. Equation `(1)` resolves that singularity completely:

1. below a relation's birth horizon it remains operationally exact;
2. at birth it has a universal sinc transition;
3. above birth it is averaged away;
4. all characters transition coherently into one probability ensemble;
5. every lost independent relation creates exactly one observable phase
   direction.

Thus the integrable/nonintegrable discontinuity is the infinite-time shadow
of a discrete observer-time ensemble cascade.

## Relation to existing physics

Closest checked parents:

1. Kronecker--Weyl theory identifies the infinite-time Haar measure on the
   subtorus fixed by exact relations.
2. Mark et al. (2024), <https://arxiv.org/abs/2403.11970>, connect
   all-order no-resonance to the random-phase temporal ensemble and study
   finite-time sinc suppression.
3. Riddell and Pagliaroli (2024),
   <https://arxiv.org/abs/2307.05417>, show that higher no-resonance
   conditions can have violations and near violations even in random
   matrices and chaotic models.
4. Campos Venuti (2015), <https://arxiv.org/abs/1509.04352>, observes the
   pointwise recurrence-time fracture between integrable and arbitrarily
   weakly nonintegrable systems.
5. Yin et al. (2025), <https://arxiv.org/abs/2401.01307>, experimentally
   and theoretically study finite-data broadening of monitored recurrence
   resonances.
6. Surace and Motrunich (2023),
   <https://arxiv.org/abs/2302.12804>, construct order-\(\ell\)
   quasi-conserved quantities and obtain rigorous persistence through
   \(O(g^{-\ell})\), with a non-rigorous \(O(g^{-2\ell})\)
   thermalization estimate.

None of these checked statements gives the full valuation of every
observer-visible relation, the exact conservation law `(3)`--`(4)`, and
the complete weak ensemble wall crossing `(1)`--`(2)` for every analytic
spectral path. This is a provisional novelty boundary, not a completed
priority claim.

## Open-system extension already proved per mode

For a complex contractive mode \(\lambda(g)\), replace symmetric phase
sampling by the normalized forward semigroup average. The universal kernel
is
\[
 \Phi(z)=\frac{e^z-1}{z},\qquad \Phi(0)=1.
\]
If \(\lambda(g)/g^b\to c\ne0\) and
\(\operatorname{Re}\lambda(g)\le0\), its averages on
\(T=\tau g^{-r}\) tend to \(1\), \(\Phi(\tau c)\), or \(0\) according
as \(r<b\), \(r=b\), or \(r>b\). This is unconditionally Lean-proved.
It is not yet a probability-measure theorem for arbitrary open-system
generators.

## Formal proof ledger

Lean-proved:

- exact analytic birth valuation and factorization;
- saturated finite-support integer relation filtration;
- non-Archimedean valuation law and unequal-depth noncancellation;
- arbitrary-label finite-character wall crossing;
- exact symmetric time-average identity;
- observer-restricted rank-nullity and conservation `(3)`--`(4)`;
- exact integral/rational relation-kernel bridge;
- forward contractive-semigroup kernel and all three regimes;
- local connected-spanning interaction-sector direct sum.
- weak convergence of the full finite-torus probability measure from all
  character limits;
- finite-support Fourier density, measure uniqueness and the full weak
  probability-law lift on every countable product torus;
- exact pushforward construction of the actual uniformly sampled
  finite- and countably infinite phase ensembles, with every coefficient
  equal to the corresponding sinc detuning.
- analytic Big-O onset forces intrinsic Taylor birth order;
- every active local-Hamiltonian observer ray has birth order at least its
  connected interaction-packet Steiner cost;
- endpoint rectangle characters embed independently into the rational
  projective constraint kernel;
- delaying every endpoint rectangle through order \(r-1\) forces constraint
  rank at least
  \[
    (|A|-1)(|B|-1)|C|,
  \]
  hence at least \((q-1)^2q^{n-2}\) for two sites of an \(n\)-site
  \(q\)-level product spectrum;
- releasing that rectangle span later forces temporal dimension to grow by
  at least the same amount.

New forced physical consequence:

- one explicit qutrit-conditioned qubit Hamiltonian is Hermitian, exactly
  affine in one coupling, and carries two actual projective eigenvalue
  characters with exact profiles \(2g+o(g)\) and \(3g^2+o(g^2)\);
- their minimum replica realization orders are exactly two and four;
- these facts are Lean-proved independently of numerical computation.

The finite and countably infinite Fourier-density, compactness and
uniform-time pushforward theorems have passed clean foreground compilation.
The new locality/rank theorem and analytic locality-to-jet bridge passed
clean foreground scratch compilation. Final dependency-closed module audit
remains open because the shared build cache was concurrently rewritten.

## Hostile review

### “This is Taylor expansion plus sinc.”

Each coefficient calculation is elementary. Novelty can only be the exact
global composition: one valued relation lattice simultaneously determines
all finite-time limiting ensembles and obeys exact temporal-dimension
conservation. If specialist literature already contains that composition
with equal scope, reject novelty.

### “This is not a law of time.”

Correct if “time” means spacetime. Paper must say observer-time phase
dimension and must provide an operational protocol. No extra spacetime
dimension claim is allowed.

### “This does not predict thermalization.”

Correct. Equation `(1)` predicts finite-time phase-ensemble resolution,
not many-body thermalization. Thermalization requires eigenvectors,
matrix elements, locality, state preparation, and a thermodynamic limit.

### “Where is the experiment?”

Fatal for a general-science physics submission. Paper needs a finite
Hamiltonian family with at least two nonzero birth layers and a low-order
reporter whose crossover exponents can be measured. A theorem without that
witness is mathematics, not Nature-level physics.

### “Generic paths break everything at first order.”

Often true. Higher layers require symmetry, selection rules, locality, or
engineered weak integrability breaking. Paper must prove a nontrivial
physical family where multiple layers are forced, not merely permitted.

### “The full torus dimension is exponentially large and unobservable.”

The observer restriction is exact, but significance requires a
low-complexity reporter. Complete reconstruction is not a device proposal.

### “Open, continuous, and thermodynamic systems are absent.”

Contractive modes and arbitrary spectral probability measures have separate
proved laws, but the joined valued weak-ensemble theorem is presently
finite-torus. No broader claim is authorized.

## Falsifiers

Reject this as master law if any one holds:

1. a primary source proves `(1)`--`(4)` with equal or greater scope;
2. Fourier coefficients in `(1)` fail to define a unique probability law;
3. a finite analytic spectrum violates `(1)`;
4. observer restriction does not commute with relation filtration;
5. no physical local family forces two distinct measurable birth layers;
6. the only corollaries are restatements of Kronecker--Weyl or
   perturbative quasi-conservation.

## Next exact obligation

The lower half is closed: locality acts on this same valuation filtration
and forces an exponential independent family of delayed second-replica
relations. Three gaps remain fatal under hostile review:

1. prove scalable activation for an actual edge-local Hermitian family,
   rather than calling a relation a hidden clock when it might remain exact
   forever;
2. join the per-character trichotomy to Fourier compactness in one theorem
   giving the unique weak limit of the complete phase probability law at
   every inverse-power scale;
3. close the reporter bridge from the two-layer Hamiltonian to a finite-copy
   interferometric statistic.

Until all three are done, this is not a Nature paper and not an earned
universal-law title.
