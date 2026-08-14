# Hypertranscendental elastic law without particle proliferation

- **ID:** `one-species-hypertranscendental-elastic-saturation`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** CANDIDATE THEOREM / FOUNDATIONAL QFT SEPARATION / SOURCE NO-GO
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED] [SIGNIFICANCE GATE OPEN]`
- **Scope:** general hypertranscendence in relativistic QFT; no RH or distinguished
  special-function input
- **Parents:** `geometric-cdd-hypertranscendental-local-qft.md`,
  `geometric-cdd-higher-spin-completion-fracture.md`, and
  `feshbach-reciprocal-jost-interface.md`
- **Statement:** A local asymptotically complete interacting QFT can have one and only one
  asymptotic particle species while its exact elastic scattering law is hypertranscendental.
  The geometric q-ladder is therefore an infinite interaction/constraint-scale measure, not an
  infinite particle-mass spectrum.  Exact unit-modulus elastic scattering also forbids any
  proposed auxiliary sector from being produced from the two-particle channel.

## Goal

Determine what is physically infinite in the geometric CDD theory.  Three objects must not be
conflated:

```text
an infinite particle spectrum,
an infinite set of local deformation couplings,
an infinite divisor in one elastic scattering phase.
```

The theorem below proves that the last two can occur while the first is absent.  This is a
literal separation between the number of asymptotic degrees of freedom and the differential
complexity of their interaction law.

## The geometric model

Fix `0<q<1` and `C>1`.  In the canonical crossing coordinate

```text
t(theta)=-i sinh(theta)/C
```

put

```text
P_q(t)=product_(k>=0) ((1-q^k t)/(1+q^k t))^2,
S_(q,C)(theta)=-P_q(t(theta)).                              (1)
```

The parent card proves that `(1)` is a regular factorizing scattering function and that `P_q`
is hypertranscendental over `C(t)`.  Lechner's inverse-scattering theorem therefore constructs a
local interacting Haag--Kastler net with `(1)` as its scattering function.

The point of this card is not to repeat that existence proof, but to extract its exact particle
content and its consequence for microscopic source proposals.

## Lemma -- elastic norm saturation excludes every orthogonal output channel `[PROVED]`

Let `H_el` be an elastic input/output Hilbert space and let

```text
H_out = H_el direct_sum H_perp.
```

Write `i : H_el -> H_out` for the canonical isometry and `P : H_out -> H_el` for the elastic
projection.  Let `U : H_out -> H_out` be unitary and define its elastic compression

```text
A = P U i.                                                  (2)
```

If `A` is an isometry, then

```text
(1-P) U i = 0.                                              (3)
```

Indeed, for every `psi in H_el`, orthogonality and unitarity give

```text
||psi||^2
  = ||U i psi||^2
  = ||P U i psi||^2 + ||(1-P) U i psi||^2
  = ||A psi||^2 + ||(1-P) U i psi||^2.
```

The isometry hypothesis makes the first term on the final line equal to `||psi||^2`; hence the
last term vanishes.  This is the channel form of elastic-unitarity saturation.  It is elementary
Hilbert-space geometry and is not claimed as new mathematics.

For a scalar rapidity-diagonal elastic amplitude, `A` is multiplication by `S(theta)`.  Therefore

```text
|S(theta)|=1 almost everywhere
  => no transition from that elastic channel to H_perp.    (4)
```

Statement `(4)` is stronger than the assertion that a particular perturbative production
diagram vanishes: all orthogonal final channels vanish simultaneously and nonperturbatively.

It does **not** prove that every field absent from the asymptotic spectrum is absent from every
off-shell presentation.  Confined, gauge, topological, defect, virtual, or superselected sectors
can fail to appear in `H_perp`.  The theorem excludes an auxiliary sector precisely when that
sector is advertised as a producible asymptotic channel.

## Theorem -- asymptotic rank one, scattering Kolchin slope one `[PROVED]`

The QFT reconstructed from `(1)` has the following simultaneous properties.

### 1. Exactly one asymptotic species

The construction starts from the one-particle space of a single neutral scalar of mass `m>0`.
Its incoming and outgoing asymptotic spaces are the bosonic Fock space over that one-particle
space.  Lechner proves that the Moeller maps from this Fock space onto the interacting Hilbert
space are unitary.  Hence the theory is asymptotically complete and has one asymptotic particle
species, not merely a selected one-species subsector.

### 2. No particle production

The scattering operator preserves every particle-number sector and acts on an `n`-particle
rapidity wavefunction by a product of two-particle factors.  On the real rapidity axis every
factor in `(1)` has modulus one.  Thus the two-particle elastic compression is unitary and the
saturation lemma gives zero amplitude into every orthogonal output channel.

### 3. No bound-state tower hidden in the q-ladder

The poles of `(1)` nearest the physical strip lie at imaginary rapidities `-pi/2` and `3pi/2`.
There are no poles in `0<Im(theta)<pi`.  Therefore the geometric divisor does not add a tower of
physical-strip bound-state poles to the one-species theory.  Its zeros in the physical strip and
its adjacent-strip poles are scattering-phase data, not additional stable asymptotic particles.

### 4. Maximal one-reporter differential jet growth

The exact q-difference constraint

```text
P_q(t)=((1-t)/(1+t))^2 P_q(qt)                             (5)
```

together with the infinite divisor puts `P_q` on the hypertranscendental branch of the published
rational-or-HT theorem.  For one reporter this means

```text
trdeg_(C(t)) C(t)(P_q,P_q',...,P_q^(r)) = r+1              (6)
```

for every `r>=0`.  In the notation of the sectoral Kolchin card,

```text
asymptotic species rank = 1,
scattering Kolchin slope = 1.                               (7)
```

Equations `(1)`--`(7)` prove that maximal differential complexity of an exact interaction law
does not require particle proliferation.

## What the q-ladder physically is `[PROVED]`

Write

```text
C q^(-k)=cosh(eta_k),
r_k=exp(-eta_k) in (0,1).
```

The local higher-spin germ of the scattering phase has coefficients `alpha_(2m+1)` satisfying

```text
b_m = (-1)^m (2m+1) alpha_(2m+1)/8
    = sum_(k>=0) r_k^(2m+1)
    = integral y^m d nu(y),

nu = sum_(k>=0) r_k delta_(r_k^2).                         (8)
```

The parent moment theorem proves strict Hankel positivity and Hausdorff determinacy.  Hence the
full local odd-spin coupling germ uniquely reconstructs `nu`, and `nu` uniquely reconstructs the
global CDD divisor.

The measure `nu` in `(8)` is an **interaction-coupling measure**.  It is not a
Kallen--Lehmann measure and its support is not the particle spectrum.  This distinction is
load-bearing:

```text
Kallen--Lehmann atom  -> asymptotic/spectral mass data,
Hausdorff atom in nu  -> one elastic phase scale.           (9)
```

The separately constructed reciprocal Kallen--Lehmann field pushes a bound-state counting
measure through a mass map and obtains a genuine infinite mass tower.  That generalized free
field is a different QFT, is Gaussian, and is not the asymptotic spectrum of the interacting
model `(1)`.

## Consequence for the reciprocal Feshbach source `[PROVED NO-GO]`

The reciprocal Jost interface uses a local auxiliary channel to produce the Schur law
`k=g/p`.  If that auxiliary channel is promoted to a producible physical asymptotic particle,
then at sufficiently high center-of-mass energy it contributes an orthogonal output channel.
But the target elastic amplitude `(1)` has unit modulus at every real rapidity.  The saturation
lemma forces the production amplitude into that channel to vanish identically.

Therefore an ordinary propagating auxiliary-particle tower cannot be the claimed source of the
target phase **through physical conversion into the tower**.  A viable reciprocal source must
instead do at least one of the following:

1. remove the auxiliary channel by a gauge or constraint quotient;
2. confine it or keep it outside the asymptotic Hilbert space;
3. realize it as a defect/interface response and prove a separate bulk-fusion theorem;
4. generate the phase through one-species local current--current deformations;
5. exhibit an exact selection or cancellation theorem that forbids all auxiliary production
   while retaining its virtual effect on the elastic phase.

This narrows the positive completion problem but does not select among these mechanisms.

## The surviving source problem

Two parent constructions show that non-asymptotic dressing is physically possible without
solving the present problem.

1. The ordinary `T bar T` flow multiplies a factorizing S-matrix by an entire CDD phase and has
   a flat-JT topological-gravity description.  This demonstrates that a non-propagating
   gravitational sector can alter scattering without adding asymptotic particle species.
2. Generalized `T bar T` operators `X_s` generate the odd higher-spin CDD tangent directions.
   The geometric model supplies the exact infinite coupling vector `(8)` and its unique global
   meromorphic completion.

Neither result gives a positive action integrating the entire vector `(8)`.  The JT construction
proves the `s=1` direction, not the geometric infinite product.  Recent form-factor work also
shows that generalized irrelevant deformations can require changes to the usual higher-particle
form-factor locality equations.  Thus the phrase "topological spectral dressing" is presently a
research conjecture, not a derived action.

> `[CONJECTURE -- CONSTRAINT-MEASURE DRESSING]` There is a positive one-species operator-flow or
> gauge/topological completion whose only additional datum is the finite Hausdorff measure `nu`
> in `(8)`, whose infinitesimal local currents are its moments, and whose exact global scattering
> phase is `(1)`.  The affine q-boundary law `(5)` must follow from the constraint sector rather
> than be inserted as an S-matrix input.

The conjecture has a sharp discriminator.  A construction with extra produced states is false by
elastic saturation.  A construction that merely prescribes `(1)` is inverse scattering, not a
source theorem.  A construction that yields only the Taylor germ has not proved the global HT
completion.

## Anti-theatre and novelty gate

Established parent knowledge:

- factorizing scattering is purely elastic and preserves particle number;
- scalar CDD factors can be finite or infinite;
- Lechner's one-species net is local and asymptotically complete;
- generalized `T bar T` deformations give higher-spin CDD directions;
- ordinary `T bar T` admits a flat-JT description;
- elastic channel saturation is immediate from unitarity;
- Hausdorff moment determinacy is classical.

Accordingly, the channel lemma and the words "one species" are not new scientific knowledge.
The candidate new theorem is the exact conjunction:

```text
one asymptotic species + asymptotic completeness
+ no production + no bound-state tower
+ scattering Kolchin slope one
+ deterministic positive coupling measure.                (10)
```

Focused searches for `hypertranscendental S-matrix`, `differentially transcendental scattering`,
and `differential algebraic particle species` did not find `(10)`.  They did find the parent CDD,
integrability, generalized-deformation, and inverse-scattering theories.  This is negative search
evidence, not a novelty proof.

The result is physically significant because it changes the ontology of HT QFT.  The infinity
need not be an infinity of particles or states.  It can be an infinity of mutually consistent
constraint scales in the exact law relating the same asymptotic particles.  This realizes the
founding principle "fixed by a constraint, not propagated by a flow" at the S-matrix level.

It is not yet Fields/Nobel-level.  That gate requires the constraint-measure dressing conjecture,
or a universality theorem proving that a physical source class forces `(5)` and `(8)`.

## Formal boundary

The live HTGeometry corpus was checked before opening this card.  It already contains the bounded
optical theorem for a unitary scattering defect, finite geometric shell constraints, endpoint
selection, logarithmic-derivative HT transfer, and strict Hankel positivity from an
infinite-support measure.  The new theorem uses the analytic asymptotic-completeness theorem and
the published q-difference HT dichotomy.  Formalizing another finite norm decomposition would be
wrapper theatre and would not close either external interface.

No Lean edit, build, scratch compilation, lint, axiom check, or numerical computation was run.

## Primary literature

- G. Lechner, *Construction of Quantum Field Theories with Factorizing S-Matrices*,
  <https://arxiv.org/abs/math-ph/0601022>.
- F. A. Smirnov and A. B. Zamolodchikov, *On space of integrable quantum field theories*,
  <https://arxiv.org/abs/1608.05499>.
- G. Hernandez-Chifflet, S. Negro, and A. Sfondrini, *Flow equations for generalised T bar T
  deformations*, <https://arxiv.org/abs/1911.12233>.
- S. Dubovsky, V. Gorbenko, and G. Hernandez-Chifflet, *T bar T Partition Function from
  Topological Gravity*, <https://arxiv.org/abs/1805.07386>.
- F. Sailis, O. A. Castro-Alvaredo, and S. Negro, *Complete Minimal Form Factors for Irrelevant
  Deformations of Integrable Quantum Field Theory*, <https://arxiv.org/abs/2506.20517>.
- B. Adamczewski, T. Dreyfus, and C. Hardouin, *Hypertranscendence and linear difference
  equations*, <https://arxiv.org/abs/1910.01874>.

## Gates

- [x] one-species asymptotic Hilbert space identified at source level
- [x] asymptotic completeness and exact factorized scattering identified at source level
- [x] elastic channel-saturation theorem proved
- [x] absence of physical-strip bound-state poles proved for the geometric product
- [x] q-ladder separated from Kallen--Lehmann particle masses
- [x] higher-spin coupling measure linked to the deterministic moment reconstruction
- [x] no ordinary producible auxiliary-tower source corollary proved
- [ ] specialist audit of the particle-spectrum interpretation
- [ ] formula-level novelty audit beyond the focused searches
- [ ] positive action/operator-flow or gauge/topological source of the full measure `nu`
