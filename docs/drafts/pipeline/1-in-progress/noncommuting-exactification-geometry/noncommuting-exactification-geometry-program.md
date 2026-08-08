# Noncommuting exactification geometry

- **ID:** `noncommuting-exactification-geometry-program`
- **Stage:** 1-in-progress
- **Type:** NEW GENERAL MATHEMATICAL THEORY / RESEARCH PROGRAM
- **Short name:** NEG
- **Domain:** heterogeneous constraints, hypertranscendental functions, arithmetic--spectral--geometric
  comparison, exactness, completion, duality, positivity
- **Status:** kinematic layer retained but rejected as the full theory; six paper theorems now
  established, including source--observer Gauss--Hodge coupling and C1/J/L repair no-gos;
  source-native zeta comparison and route-complete realization remain open
- **Dedicated paper lane:**
  `../../2-fully-proven/noncommuting-exactification-geometry/`

## 0. The answer in one sentence

The thousands of theorems and no-gos are shadows of a **source-exact boundary seen through curved
observer changes**: arithmetic supplies exactness and provenance, Fourier/spectral realization
supplies comparison, geometry supplies adjoint and positive energy, and failure of comparison to
commute with the two differentials supplies the energy-supporting curvature.

The original “curved field of mutually exactifying observers” remains the kinematic container but
is not enough.  The revised dynamical theory is developed in
`source-observer-relativity-and-all-route-field-law.md`, where all three faces occur in one proved
Gauss--Hodge identity and every named RH route is assigned a proof role.

The ontology changes from

> one object with several incomplete descriptions

to

> one contextual relation-field whose descriptions are its local fibers.

If no global section exists, asking where the single combined object is located is a type error. The
geometry, holonomy, and exactness defects of the observer field are the object.

## 1. Newtonian mechanics versus the proposed geometry

| Fixed-background obstruction mechanics | Noncommuting exactification geometry |
|---|---|
| choose one ambient category | context category is part of geometry |
| object exists before its representations | source is a relation-field assembled through representations |
| each no-go is an external obstacle | no-go is local curvature, incidence, gap, or horizon data |
| changes of representation are bookkeeping | observer transport and holonomy are primary |
| exactness is a yes/no property | exactness is a provenance flag \(B\subseteq Z\) |
| completion preserves intended meaning | closure can change homology and erase literal source range |
| noncommutativity is treated as incompatibility | exchange curvature and precision are independent tensors |
| positivity is imposed on the raw carrier | indefinite Green data comes before quotient; positivity may live only after reduction |
| finite truncations approximate the whole | finite consistency can escape to infinite capacity or a nonclosed range |
| finite differential invariants can search for HT | DA and HT germs are mutually dense in finite-jet topology |

The general-relativistic move is exact: obstruction is no longer a force acting inside a fixed
mathematical background. Obstruction is curvature of the space of backgrounds in which one attempts
to make the source exact.

## 2. Primitive data

NEG does not begin with a Hilbert space or a zero set. It begins with a source and its admissible
observers.

### 2.1 Source spacetime: the Cartan pro-jet

For a source \(f\) over a differential field \((K,\delta)\), the local spacetime is the tower

\[
J^0(f)\leftarrow J^1(f)\leftarrow J^2(f)\leftarrow\cdots,
\qquad
J^\infty(f)=\varprojlim_r J^r(f).                              \tag{2.1}
\]

Its time direction is the Cartan line

\[
[\delta]=\{u\delta:u\in K^\times\},                           \tag{2.2}
\]

not one chosen derivative coordinate. The paper theorem
`finite-jet-indistinguishability-and-clock-covariance.md` proves:

1. hypertranscendence is invariant under (2.2);
2. every exact finite jet fiber contains both a DA germ and an HT germ;
3. DA and HT are both dense in finite-jet topology;
4. source-dependent analytic clock changes are too large and can trivialize HT.

Therefore hypertranscendence is a tail condition of source spacetime. No finite jet chart can see it.

### 2.2 Observer contexts

Let \(I\) index exactification operations such as:

- arithmetic source extraction;
- functional or difference-equation realization;
- analytic continuation;
- Fourier or Mellin realization;
- geometric/cohomological realization;
- topological completion;
- real structure and dagger;
- positive Hilbert reduction.

An **observer word** is a finite ordered word

\[
w=i_k\cdots i_2i_1.                                           \tag{2.3}
\]

It records not only which observers were used but in which order. The **context category**
\(\mathcal C_f\) has finite jet depth, source aperture, observer words, and compatible refinements
as objects and morphisms. Swapping adjacent observers gives comparison 2-cells when such comparisons
exist.

The use of words is essential. Replacing a word by its unordered set assumes the theorem that the
exactifiers commute, which is precisely what usually fails.

### 2.3 Heterogeneous realization fibration

Different observers need not land in the same category. Arithmetic may produce divisors or modules;
spectral analysis may produce operators; geometry may produce complexes; topology may produce
completed quotients. NEG therefore uses a fibration or category of correspondences

\[
\pi_f:\mathcal R_f\longrightarrow\mathcal C_f,                \tag{2.4}
\]

whose fiber over a context \(c\) contains the exact representation data available in that context.
Transport along a context morphism is a correspondence, derived functor, or comparison map of the
correct type. It is not assumed to be an isomorphism.

A **unified presentation** is a global compatible section of (2.4). Failure of a section is not
failure to discover an already existing point. It is geometric nontriviality of the fibration.

### 2.4 Provenance flags

Whenever a context produces a two-step complex

\[
C^{-1}\xrightarrow{d_-}C^0\xrightarrow{d_+}C^1,
\]

retain

\[
B_c=\operatorname{im}d_-,
\qquad
Z_c=\ker d_+,
\qquad
B_c\subseteq Z_c.                                              \tag{2.5}
\]

The spectrum or cohomology is only the quotient \(H_c=Z_c/B_c\). The flag remembers which cycles
came from the source. The proven provenance topology uses lower topology on \(B\) and Scott topology
on \(Z\); its specialization order is

\[
(B,Z)\preceq(B',Z')
\quad\Longleftrightarrow\quad
B'\subseteq B\subseteq Z\subseteq Z'.                         \tag{2.6}
\]

Its basic survival proposition is

\[
v\in Z\setminus B.                                             \tag{2.7}
\]

Cycle-only topologies cannot distinguish different source ranges. Dagger reverses the flag,

\[
(B\subseteq Z)^\dagger=(Z^\circ\subseteq B^\circ),             \tag{2.8}
\]

so a one-sided topology is insufficient; the bipolar provenance topology is the join with its
dagger pullback.

These statements are proved in the dedicated polarized-exchange papers and imported here as a
layer, not claimed as new NEG theorems.

## 3. Two independent local tensors

When a finite family of context fibers admits a source-defined Hilbert mediator \(H\), each exact
observer is represented by a closed admissible sector \(U_i\subseteq H\) with orthogonal projector
\(P_i\).

### 3.1 Exactness metric: constraint Laplacian

Define

\[
\Delta_{\mathcal C}=\sum_i(I-P_i).                             \tag{3.1}
\]

Then

\[
\ker\Delta_{\mathcal C}=\bigcap_iU_i.                          \tag{3.2}
\]

The bottom of the transverse spectrum gives the precision gap

\[
\mu_{\mathcal C}
=\inf_{x\perp\cap U_i,\ \|x\|=1}\langle\Delta_{\mathcal C}x,x\rangle.
                                                                    \tag{3.3}
\]

- \(\mu>0\): hard, stable incompatibility;
- \(\mu=0\) with no transverse kernel: arbitrarily sharp finite appearances but nonclosed range;
- nonzero kernel: a genuine joint sector.

For two observers, \(\mu=1-c_F(U,V)\), where \(c_F\) is the Friedrichs cosine. If the first
observer is exact, its irreducible error in the second is at least \(1-c_F^2\) in squared norm.

### 3.2 Exchange curvature

Define

\[
\Omega_{ij}=P_iP_j-P_jP_i.                                    \tag{3.4}
\]

This measures order dependence, not simultaneous precision. The dedicated paper proves:

- commuting exactifiers can have or lack a joint sector;
- noncommuting exactifiers can have or lack a joint sector;
- equal commutator norm can coexist with different uncertainty gaps.

Thus \(\Omega\) and \(\Delta\) are independent. The previous temptation

\[
\text{interaction}\Longrightarrow\text{noncommutativity}
\Longrightarrow\text{uncertainty}
\]

is false. NEG replaces it with a computed pair

\[
(\Delta_{\mathcal C},\Omega_{\mathcal C}).                    \tag{3.5}
\]

This is the first non-theatrical consequence of the proposed geometry.

## 4. Higher curvature and context holonomy

Pairwise commutators are not enough when three or more exactifiers exist. Adjacent exchanges can be
invertible while different exchange sequences around a braid hexagon disagree. If
\(\beta_{ij}:E_iE_j\Rightarrow E_jE_i\) are comparison 2-cells, the first higher curvature is the
Yang--Baxter defect

\[
\mathfrak Y_{123}
=(\beta_{23}\beta_{13}\beta_{12})^{-1}
  (\beta_{12}\beta_{13}\beta_{23}),                           \tag{4.1}
\]

with the composition order interpreted in the appropriate 2-category. Formula (4.1) is a target
definition, not a claim that every corpus route already supplies invertible \(\beta\)'s.

More generally, choose a base context and transport around loops in \(\mathcal C_f\). Their actions
form the **observer holonomy**. A global parallel section must be fixed by every holonomy operator.
Consequently:

\[
\{\text{unified exact presentations}\}
\cong
\operatorname{Fix}(\operatorname{Hol}_f),                     \tag{4.2}
\]

under the unitary local-system hypotheses. This is now proved, including affine source defects,
in `affine-observer-holonomy-and-global-section-law.md`. For affine transports the fixed-vector
equation becomes ((I-H_e)x=c_e) for every based loop.

The complete representation object is therefore not one fiber. It is

\[
\mathfrak X_f
=\left(J^\infty(f),[\delta],\pi_f,\nabla_f,
  \{B_c\subseteq Z_c\},\Delta_f,\Omega_f,\dagger\right),       \tag{4.3}
\]

including all observer words and their higher comparison data.

## 5. New topology: contextual bipolar provenance topology

The total representation field needs a topology that sees three kinds of approximation at once.

1. **Jet approximation:** finite cylinders in \(J^\infty(f)\).
2. **Source survival:** opens \(v\in Z_c\setminus B_c\) in a context flag.
3. **Dual survival:** the dagger images of the source-survival opens.

Define the **contextual bipolar provenance topology** \(\tau_{\mathrm{CBP}}\) on the total space of
\(\mathcal R_f\) to be the smallest topology containing:

- inverse images of finite-jet cylinders;
- transported provenance opens in every context;
- transported dagger-provenance opens;
- overlap domains on which observer comparison maps are defined.

This topology is new terminology and a new proposed construction. Its novelty does not yet make it
useful. Stage-2 promotion requires proofs of:

1. independence from equivalent presentations of the context category;
2. continuity of admissible observer transport;
3. exact characterization of its specialization preorder;
4. one source-native invariant that becomes continuous in \(\tau_{\mathrm{CBP}}\) but is invisible
   in every individual chart topology.

Until those are proved, \(\tau_{\mathrm{CBP}}\) remains a serious definition under test, not the
solution.

## 6. Horizons, caustics, and the black-hole analogy

NEG has exact mathematical horizons before any physical interpretation.

### 6.1 Precision horizon

Along a family of contexts \(c(t)\), a **precision horizon** occurs when

\[
\mu_{c(t)}>0\quad(t<t_0),
\qquad
\mu_{c(t)}\downarrow0\quad(t\uparrow t_0).                    \tag{6.1}
\]

At the horizon, stable joint reconstruction becomes arbitrarily ill-conditioned. Beyond it, the
literal range may be dense and nonclosed. Every finite experiment can remain accurate while the
global quotient becomes non-Hausdorff.

### 6.2 Capacity horizon

For nested affine finite-stage constraint sets \(C_r\), a **capacity horizon** occurs when

\[
C_r\neq\varnothing\text{ for all }r,
\qquad
\operatorname{dist}(0,C_r)\longrightarrow\infty.              \tag{6.2}
\]

The dedicated paper proves that bounded capacity is exactly the missing compactness condition for
a nonempty global intersection in Hilbert space.

### 6.3 Signature horizon

A path from a nondegenerate indefinite source Green form supporting a nonzero isotropic boundary to
a positive-definite form on the same unreduced carrier must cross a degenerate form. The viable
alternative is reduction first, positivity second. This follows from inertia invariance and the
proved positive self-dual flag rigidity; a separate closed paper theorem is still to be written.

### 6.4 Holographic reading

The black-hole/holographic hunch has one rigorous analogue and several unproved extrapolations.

- **Rigorous analogue:** bulk scalarization or quotient can erase orientation and source range, while
  a marked boundary/provenance flag retains them.
- **Rigorous analogue:** a spectral-gap closure is an information horizon: finite observers cannot
  distinguish an exact object from escaping approximate objects.
- **Unproved:** these exactification horizons are literal wormhole interiors, black-hole time phases,
  or physical holographic screens.

The physical words are permitted only as discovery metaphors until a physical source functor and an
observable prediction are constructed.

## 7. Hypertranscendence in NEG

Hypertranscendence is not curvature, uncertainty, sign failure, monodromy, or descent height. The
corpus already falsifies every such universal identification.

Its precise NEG role is:

\[
\text{HT}=\text{absence of every finite algebraic hypersurface containing the Cartan jet orbit}.
                                                                    \tag{7.1}
\]

The finite-jet theorem strengthens (7.1): every finite observer fiber contains both DA and HT
sources. Therefore any coupling between HT and the other NEG tensors must be a tail coupling.

Define an observer field to be **HT-sensitive** only if there is no finite jet depth \(r\) through
which its discriminating invariant factors. Define it to be **source-coupled** only if changing the
source while holding the coarse realization fixed changes that invariant. These two conditions block
the common theatre of attaching an infinite tower or noncommutative word growth that does not see the
source.

The major axes are independent until a source equation couples them:

| Axis | Tensor/invariant | What it can decide |
|---|---|---|
| Cartan tail | differential ideal over all jet orders | DA versus HT |
| incidence | flag \(B\subseteq Z\) | source range versus cycles |
| precision | \(\Delta\), \(\mu\) | joint exactness and closure |
| route order | \(\Omega\), higher holonomy | observer-order dependence |
| duality | dagger and bipolar topology | orientation/provenance reversal |
| signature | inertia after exact reduction | positive versus indefinite realization |
| higher descent | source-specific Postnikov/fracture tower | coherence depth |

No arrow between rows is automatic.

## 8. Proven kinematic field equation and missing source geometry

The affine observer-holonomy theorem gives the first closed field equation. For a rooted observer
graph, spanning-tree transport converts every remaining comparison loop into

\[
(I-H_e)x=c_e.
\]

Define

\[
\Delta_{\mathrm{hol}}=\sum_e(I-H_e)^*(I-H_e),
\qquad
J_{\mathrm{src}}=\sum_e(I-H_e)^*c_e.
\]

Every unified presentation satisfies

\[
\boxed{\Delta_{\mathrm{hol}}x=J_{\mathrm{src}},
\qquad
\sum_e\|(I-H_e)x-c_e\|^2=0.}                                 \tag{8.1}
\]

The zero-residual equation is indispensable: the normal equation alone can describe only a
least-squares compromise. Both operators are derived from observer comparison data. Frame changes
conjugate the equation, and changing spanning tree preserves exactness and gap type. For countably
many contexts, exact finite consistency globalizes exactly when root-solution capacity remains
bounded.

This is a kinematic field equation, not yet the general-relativistic achievement. Its observer graph,
linear holonomies, and affine source currents must be constructed from the actual arithmetic,
spectral, and geometric source rather than inserted.

The remaining dynamical core is a **provenance--curvature coupling law**. In its weakest typed form,
seek a
source current \(\mathcal J_f\) and a transgression map \(\mathsf T\) such that

\[
[\Omega_f]=\mathsf T(\mathcal J_f)                             \tag{8.2}
\]

in a source-defined obstruction group, with a Bianchi/coherence identity forcing conservation of
\(\mathcal J_f\). Equation (8.1) must satisfy all of the following or be rejected:

1. \(\mathcal J_f\) is computed from literal source/provenance data, not from the desired curvature;
2. the obstruction group and transgression exist before RH is assumed;
3. at least one known corpus no-go is recovered as a contraction of (8.1);
4. at least one new nontrivial theorem follows that is not available in a single parent category;
5. HT sensitivity is proved as non-factorization through every finite jet order;
6. flat examples and source-decoupled HT examples map to zero curvature, as they must;
7. changing observer presentation conjugates the equation rather than changing its content.

No present card proves (8.2), and no present card constructs the source-native observer graph needed
to apply (8.1) across all three principal faces. Writing an Einstein-shaped formula without these
obligations would be theatre.

## 9. Conjecture--proof/failure loops

### Loop A — interaction forces complementarity

**Conjecture.** Coupled sectors must have noncommuting complete reporters and a positive uncertainty
bound.

**Failure.** The retired causal-identity complementarity card contains exact coupled dynamics with
commuting reporters. Coupling does not imply kinematic complementarity.

**Survivor.** Compute \(\Delta\) and \(\Omega\) separately from source-defined exactifiers.

### Loop B — commutator is the combined constraint

**Conjecture.** \(\|[P,Q]\|\) measures exactification uncertainty.

**Failure.** Equal commutator norms can have different precision gaps; commuting projections may or
may not have joint exact vectors.

**Survivor.** Pairwise geometry is carried by incidence sectors plus the full angle operator. For
many observers, use the constraint-Laplacian spectrum plus higher holonomy.

### Loop C — one fixed gerbe class is the universal obstruction

**Conjecture.** Every HT realization obstruction is a fixed degree-two gerbe.

**Failure.** The corpus proves pair-face sewing can be degree one and that obstruction degree depends
on source data.

**Survivor.** Retain the source-specific Postnikov/fracture tower as the higher-coherence layer of
NEG. Do not collapse it to one degree.

### Loop D — HT is nonzero curvature

**Conjecture.** Hypertranscendence forces observer curvature, sign failure, or nontrivial holonomy.

**Failure.** HT families can have exact descent; digamma HT can have positive Hankel data; complicated
monodromy can remain finite differential rank; arbitrary composition can cancel HT.

**Survivor.** HT is Cartan-tail freedom. Curvature requires an additional source-sensitive coupling.

### Loop E — the missing object is a global section

**Conjecture.** Construct the homotopy limit of all routes and call it the hidden object.

**Failure at stated universality.** A nontrivial contextual fibration may have no global section.
Declaring a homotopy limit does not make it nonempty, Hausdorff, positive, or source-canonical.

**Survivor.** The fibration and its holonomy exist even when the global section does not. Existence,
closure, and positivity become separate theorems rather than axioms.

### Loop F — finite exactification data can classify HT

**Conjecture.** A sufficiently rich but fixed finite jet geometry might distinguish DA from HT.

**Failure, proved.** Every finite jet fiber contains both classes; both are dense.

**Survivor.** Any HT-sensitive invariant must live in pro-tail transport, not a finite chart.

## 10. Cross-corpus obstruction atlas

This atlas is the first audit, not the exhaustive census required for completion.

| Corpus result/no-go | NEG coordinate | What one chart forgets | New obligation |
|---|---|---|---|
| Deninger secondary Poisson radical strictly exceeds literal source range | incidence/provenance | \(Z\) retained, \(B\) lost | construct both flags in one comparison fiber |
| Möbius right inverse classifies literal Poisson range | source section | analytic image without source Green form | transport range through dagger/Stokes chart |
| positive ambient Hodge--Stokes forces boundary zero | signature/reduction | positivity imposed before quotient | compute reduced form and transverse gap |
| Hedenmalm divisor form has dense proper nonclosed radical | capacity horizon | algebraic radical versus completed closure | compute constraint normal operator |
| two-prime Kummer: finite modes invertible, limiting range dense nonclosed | precision horizon | finite inverses hide \(\mu\downarrow0\) | extract finite-stage gap asymptotics |
| positive finite cutoffs with nonsummable mass have no finite positive extension | affine capacity | pointwise positivity hides total source cost | identify nested convex sets and capacity function |
| same completed ring supports opposite Herglotz orientations | bipolar provenance | completion forgets sign/orientation | retain dagger flag and residue orientation |
| source-face cohomology changes under specialization | derived incidence | kernel alone forgets cokernel/Tor | use full complex and base-change curvature |
| finite spectral rank selector is transverse-blind | finite observer blindness | height projection loses divisor direction | prove non-factorization through every finite rank |
| differential field misses finite symmetric divisor gauges | source gauge blindness | field forgets marked divisor | add source marking to fiber |
| word-growth/monodromy does not force differential innovation | curvature/HT independence | raw holonomy ignores observable quotient | define source-sensitive cocycle quotient |
| finite ternary presentation misses parameter derivative | missing connection | fixed fiber forgets horizontal transport | construct source-selected connection |
| arbitrary HT composition can equal identity | inadmissible clock gauge | solution used as coordinate | restrict to Cartan/base covariance |
| Gamma/digamma HT can have positive Hankel matrices | tail/signature independence | HT says nothing about positivity | require explicit source coupling |
| two-state projective route failed under wrong Yang--Baxter convention | observer conversion error | permutation/connection term dropped | type all exchanges and higher coherence |
| fixed-degree polarized selection gerbe failed | higher-curvature degree | one obstruction class hides tower | retain full source-specific Postnikov data |
| stabilizer-enriched realization lacks canonical source section | no-global-section/contextuality | fiber completeness confused with horizontal conservativity | prove holonomy-fixed section criterion |

The atlas already shows no single scalar invariant can be the substrate. At minimum, six independent
coordinates are required. The proposed unity is their common transformation law, not their collapse.

## 11. Concrete theorem pipeline

### Fully proved on paper

1. `finite-jet-indistinguishability-and-clock-covariance.md`
   - Cartan clock covariance;
   - exact finite-jet DA/HT indistinguishability;
   - mutual density and no continuous classifier;
   - source-dependent analytic trivialization no-go.
2. `constraint-laplacian-uncertainty-and-capacity-horizon.md`
   - exactification trichotomy;
   - Friedrichs precision law;
   - curvature/uncertainty independence;
   - affine capacity-horizon criterion.
3. `affine-observer-holonomy-and-global-section-law.md`
   - global presentations as affine holonomy fixed points;
   - source current and holonomy Laplacian;
   - frame and spanning-tree covariance;
   - exact countable globalization by bounded capacity.
4. Imported dedicated polarized-exchange papers
   - provenance flag topology;
   - bipolar dagger reduction;
   - positive self-dual cochain rigidity.
5. `two-prime-kummer-precision-horizon-and-compact-repair-no-go.md`
   - exact finite precision gap and inverse capacity;
   - quantitative approximate-Green blow-up;
   - full interval essential spectrum;
   - every compact Route-L repair ruled out.
6. `source-observer-hodge-curvature-and-subunit-annihilation-law.md`
   - exact arithmetic--comparison--Hodge energy identity;
   - unitary observer-frame covariance;
   - exact comparison weakened to strict subunit curvature;
   - quantitative approximate co-closure law.
7. `observer-horizon-stability-under-bounded-and-compact-repair.md`
   - multivalued graph horizon invariant under every bounded perturbation;
   - sequential nonclosability invariant under bounded positive form correction;
   - compact precision-horizon stability;
   - new Route-C1 and Route-J repair no-gos.

### Next dependency-closed paper targets

1. **Curved comparison-square theorem.** A noncommuting observer square totalizes to a curved complex
   with \(d^2=\Omega\); gauge changes conjugate curvature and transport provenance flags.
2. **Reduction-or-signature-wall theorem.** A nonzero isotropic source boundary cannot be carried from
   a nondegenerate indefinite Green form to a positive-definite raw form without reduction or metric
   degeneracy.
3. **Contextual topology theorem.** Compute specialization and continuity for
   \(\tau_{\mathrm{CBP}}\).
4. **Source-native field-law calculation.** Construct comparison maps for Deninger/Route R or
   Hedenmalm and prove either exact curvature or a strict subunit bound on a literal source
   antecedent.
5. **Declaration-level route audit.** Map the full corpus census to source, comparison, Hodge,
   horizon, and cofinal-tail components without ad hoc mediators.

Direct leverage now spans three independent routes: compact repair cannot close the two-prime
Kummer precision horizon; bounded positive correction cannot close the C1 Hedenmalm form; and
bounded post-fusion correction cannot close the Route-J codiagonal.  The field law additionally
weakens Route R's exact-comparison target to strict source-curvature contraction.

## 12. External literature boundary

Broad current searches found close ingredients, not this assembled theory.

- Abramsky--Brandenburger, arXiv:1102.0264: contextuality as failure of global sections.
- Williams--Doosti--Shahandeh, arXiv:2605.00975: preparation contextuality as failure of stochastic
  extension.
- Mesland--Rennie, arXiv:2112.03822: Friedrichs angles and alternating projections in Hilbert
  \(C^*\)-modules.
- Goetz, arXiv:2606.10146: curved DG modules; confirms that \(d^2\neq0\) curvature language is
  established and cannot carry novelty alone.
- Classical local systems, holonomy, idempotent monads/localizations, two-projection theory,
  derived categories, and Postnikov towers are all prior art.

Current novelty claim is restricted to the source-framed assembly:

1. infinite Cartan-tail source;
2. ordered heterogeneous exactification contexts;
3. independent precision and exchange tensors;
4. provenance and dagger topology;
5. source-specific higher coherence;
6. a theorem pipeline that decides whether a unified section exists instead of assuming one.

A complete priority audit remains open. Search must continue with broad terms: localization and
distributive-law defects, context fibrations, noncommuting projections, jet groupoids, differential
algebraic density, curved descent, and source-sensitive contextuality.

## 13. Kill conditions

Retire NEG as insignificant if any of the following survives hostile audit.

1. The whole construction is equivalent to an existing stack/local-system framework with no new
   invariant, theorem, or source coupling.
2. Contextual bipolar provenance topology depends on arbitrary presentation choices.
3. Every corpus mapping requires an ad hoc Hilbert mediator and none is source-canonical.
4. Constraint Laplacian and exchange curvature never produce a theorem beyond already known route
   facts.
5. HT sensitivity cannot be coupled to observer transport except by inserting HT into definitions.
6. A single parent category already supplies all claimed comparison laws.
7. The proposed field equation (8.1) is circular or has no nontrivial source current.
8. No live route yields a new gap, capacity, holonomy, or provenance theorem.

## 14. Promotion gates

- [x] Dedicated Stage-1 and Stage-2 subfolders created.
- [x] Finite-jet observer no-go proved.
- [x] Exactification uncertainty/closure trichotomy proved.
- [x] Exchange curvature separated from precision.
- [x] Prior fixed-gerbe, composition, holonomy-growth, positivity, and complementarity failures
  incorporated.
- [x] Observer holonomy/global-section law proved on paper, including affine source current.
- [ ] Contextual bipolar provenance topology proved presentation-invariant and useful.
- [ ] Source-provenance curvature law constructed without circularity.
- [x] Live two-prime Kummer obstruction receives exact gap/capacity law and compact-repair no-go.
- [x] Exact source--observer Gauss--Hodge field law and subunit annihilation proved on paper.
- [x] Bounded/compact horizon stability proved with new C1 and J consequences.
- [x] Every named route in the current route quotient assigned a typed field-law role.
- [ ] Full declaration-level corpus realization proved conservative and presentation-independent.
- [ ] Source-native zeta comparison with curvature gain below one constructed.
- [ ] Broad priority audit completed.
- [ ] Hostile review finds no remaining substantive conjecture, proof attack, salvage, or pivot.

The goal is not met while the remaining open boxes remain.

## 15. Lean return notes

Do not write or build Lean in this research phase. Later formalization should proceed theorem by
theorem after paper closure. Read-only corpus searches should identify existing files for:

- differential derivations and differential algebra;
- orthogonal projections and positive operators;
- exactness flags and annihilators;
- graph/local-system holonomy;
- weak compactness and nested intersections.

No Lean file path is guessed here.

## 16. Log

- 2026-08-08 — program opened after user correction that arithmetic, Fourier/spectral, and geometric
  precision behave like conjugate aspects of one combined constraint. Rejected route-local repair and
  universal physical complementarity. Defined source pro-jet, context fibration, constraint Laplacian,
  exchange curvature, provenance flags, higher holonomy, and contextual bipolar provenance topology.
  Banked finite-jet indistinguishability and exactification uncertainty/capacity theorems. Recorded
  source-provenance field equation and first live quantitative route calculation as open gates.
- 2026-08-08 — hostile all-route audit rejected the global-section/holonomy equation as the missing
  dynamics.  Added source--observer relativity: proved the Gauss--Hodge curvature identity, exposed
  strict subunit comparison as a weaker Route-R target, proved bounded/compact horizon conservation,
  derived C1/J repair no-gos, and mapped the full named-route quotient.  RH source construction
  remains open.
