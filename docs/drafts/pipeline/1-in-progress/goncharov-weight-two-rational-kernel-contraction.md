# Rational contraction of the weight-two cycle kernel

- **ID:** goncharov-weight-two-rational-kernel-contraction
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Parent:** `goncharov-weight-two-rank-contraction`
- **Statement:** `[CONJECTURE]` For every perfect field `k`, the rational Zariski sheaf
  `Z⁰_k(2)_ℚ` is rationally contractible, where
  `Z⁰_k(2) = ker(Cor(Δ²_k × -, G_m^∧2) → Cor(Δ¹_k × -, G_m^∧2))`.

## Goal

Construct a presheaf morphism

`s : Z⁰_k(2)_ℚ → C̃₁ Z⁰_k(2)_ℚ`

with endpoint identities `i₀*s=0` and `i₁*s=id`.  Suslin's rational-contractibility
theorem would then make `Z⁰_k(2)_ℚ(Δ̂_K^•)` contractible for every finitely generated
extension `K/k`.  Garkusha's Theorem 4.1 and weight-two comparison identify the resulting
degree-three vanishing with

`H₃(K₂ᴹ(Δ̂_K^•))_ℚ = K₄⁽²⁾(K)_ℚ = 0`.

Taking `k=ℚ` or `k=F_p`, then using filtered colimits, covers arbitrary fields.  This is a
strict chain-level construction; it may not assume Beilinson--Soulé vanishing, motivic
connectivity, or the desired semilocal acyclicity.

## Gates

- [x] 0 → 1 in-progress: exact kernel sheaf and endpoint identities fixed; consequence audited
- [ ] 1 → 2 fully-proven: contraction formula defined on every correspondence and all identities proved
- [ ] 2 → 3 formalized: only after the full paper contraction closes
- [ ] 3 → 4 publication-ready: standalone proof, Lean certificate, and novelty audit

## Approach

Each ambient sheaf `Cor(Δʳ_k × -, G_m^∧2)_ℚ` is already rationally contractible.  Start
with Suslin's ambient contraction.  For `z∈Z⁰_k(2)_ℚ`, its boundary defect along the
homotopy parameter has zero endpoints.  Construct a second finite correction whose boundary is
that defect, naturally under pullback and finite correspondence, without altering the endpoints.

The tempting target homotopy `u ↦ 1+t(u-1)` works pointwise on `G_m`, but not uniformly on
`Cor(Δʳ×X,G_m^∧2)`.  An element of `C̃₁` must be defined over an open
`U⊂X×A¹` containing both endpoint fibers, independent of the simplex coordinate.  The bad locus
lies over `Δʳ×X×A¹`; because `Δʳ` is not proper, its projection to `X×A¹` need not be
closed and cannot simply be removed.  Compactifying the simplex isolates an infinity divisor.
Required correction must show that the kernel condition cancels this infinity defect or turns it
into an explicit principal boundary.

On the configuration shadow in characteristic different from `2,3`, a squarefree binary form
`F_S` supplies a `PGL₂`-covariant moving divisor `div Hess(F_S)` disjoint from its roots.  For a
deletion `T⊂S`, normalized divisor differences are principal through explicit common-degree
ratios of Hessians; square deletion coherences telescope strictly.  This defines the correction
through triple stabilizers.  The unresolved terminal datum is the pair stabilizer torus: it has no
nonzero finite invariant zero-chain on the complement, so the last correction must be semilinear
or bar-homological rather than another covariant point.

## Hostile tests

- The correction must preserve the kernel before evaluating on semilocal simplices; acyclicity of
  the target complex cannot be used to define it.
- Degree-one Bloch classes must survive.  Any formula contracting the full weight-two complex is
  false.
- Pair-stabilizer ambiguity must be killed in ordinary `PGL₂` coinvariants, not only after
  quotienting by automorphisms of a transcendental parameter field.
- Pointwise target contraction is insufficient: produce one endpoint neighborhood uniform over
  every simplex coordinate, with all projective-infinity components accounted for.
- Characteristics `2` and `3` require covariants whose resultant with every squarefree form is
  nonzero; the ordinary Hessian is insufficient.
- Pullback, transfer, alteration, and degeneration compatibility must be literal, not inferred
  from rational equivalence after the desired vanishing.

## Current obstruction

The remaining pair-level defect is the same object in four exact models:

1. second equivariance defect of a generic configuration cone;
2. `H₂(PGL₂; St₂∞)` or five-term-relation syzygies modulo six-point boundaries;
3. the difference of Kimura's two weight-two Bloch--Kriz fillers in `N⁰(2)`;
4. the degree-zero ruled-surface class below Bolbachan's proved Totaro comparison.

No audited source constructs the required second correction.

## Log

- 2026-08-27 — created in Stage 1 after corpus search and audit of Garkusha's rational
  contractibility criterion.  Ambient contraction, Hessian moving divisor, and principal deletion
  homotopies are available on paper; pair-level coherence and characteristics `2,3` remain open.
- 2026-08-27 — falsified the naive coordinatewise contraction.  Its zero-avoidance open depends
  on the nonproper simplex coordinate, whereas `C̃₁` requires an open pulled back from the base.
  The missing correction is now localized to the projective-infinity divisor of the simplex.
- 2026-08-27 — recovered Suslin's exact ambient construction from Proposition 2.2 of *On the
  Grayson Spectral Sequence*.  The contraction of `Z_tr(G_m^∧2)` is induced by the target map
  `h_t(u)=1+t(u-1)` on its endpoint neighborhood.  The maps satisfy the strict semigroup law
  `h_s h_t=h_{st}`.  Applying this before `C_2` preserves the cycle differential formally; the
  sole failure to land in `C̃₁ C_2` is that the good open may depend on the affine-simplex point.
  Thus there is no interior coherence error beyond the already isolated infinity support.
- 2026-08-27 — `[FALSIFIED]` Kill the infinity error by passing to nilpotent higher Chow groups
  with modulus.  Miyazaki's Theorem 4.10 makes the nilpotent group `p`-primary in characteristic
  `p`, but in characteristic zero it is a `k`-vector space, not rationally zero.  Moreover the
  theorem is homological after quotienting by higher-cycle boundaries; using it to manufacture a
  chain-level contraction of `Z⁰(2)` would assume the missing filler.  Positive survivor: modulus
  identifies the error as unipotent/infinity data, but does not remove its rational characteristic-
  zero part.
- 2026-08-27 — `[POSITIVE SURVIVOR]` Let
  `R_n=O(Δ̂_k^n)` and `J_n=ker(R_n→k^{n+1})`, evaluation at the vertices.  In barycentric
  coordinates,

  `J_n=(t_i t_j | 0≤i<j≤n)`.

  Indeed the quotient has pairwise orthogonal generators `t_i`, with `t_i²=t_i` and
  `Σ_i t_i=1`, hence is exactly `k^{n+1}`.  The corpus's Stanley--Reisner and normalized-simplex
  contraction theorems therefore apply to the additive monomial shadow of the semilocal problem;
  its Dennis--Stein files supply the exact nonlinear addition and scaling correction terms that a
  relative-`K₂` lift must respect.  The corpus also proves nonzero disconnected/hollow Koszul
  classes, so a blanket contraction of every relative jet layer is false and would erase the
  degree-two Bloch group.
- 2026-08-27 — `[ACTIVE CONJECTURE]` For every `d≥2`, define the semilocal toric power map

  `q_{d,n}^*(t_i)=t_i^d/(Σ_j t_j^d)`.

  Its denominator is a unit at every vertex; it fixes every vertex, restricts literally to
  `q_{d,n-1}` on every face, and sends `J_n` into `J_n^d`.  The formula

  `H_{d,n,λ}^*(t_i)=λt_i+(1-λ)t_i^d/(Σ_j t_j^d)`

  is defined on an open containing every vertex cylinder and joins `q_{d,n}` to the identity,
  again face-compatibly.  This removes the earlier pair/infinity incompatibility at the level of
  the semilocal Milnor complex.  Exact remaining theorem: prove that the induced endomorphism on
  `H₃(K₂ᴹ(Δ̂_k^•))_ℚ` has no fixed vectors.  The homotopy then identifies it with the identity and
  forces vanishing.  Any proof must retain the known nonzero `H₂` Bloch/`K₃^{ind}` sector; a claim
  that `q_d` contracts the entire positive-degree complex is false.
- 2026-08-27 — `[NO-GO BOUNDARY]` `J_n`-adic completion alone cannot finish.  The power map pushes
  relative symbols arbitrarily deep, but localization units supported away from the selected
  vertices can survive every `J_n`-adic layer.  This is the same global infinity phantom in a new
  form.  Required next invariant is a finite residue/configuration profile on which `q_d` has no
  degree-three fixed vector, while its degree-two fixed part is exactly the Bloch group.
- 2026-08-27 — `[POSITIVE SURVIVOR]` If finite Milnor transfer for `q_{d,n}` satisfies the
  ramified face formula

  `∂ q_{d,n,*}=d q_{d,n-1,*} ∂`,

  then `B_{d,n}=d^{-n}q_{d,n,*}` is a chain map.  Projection formula gives
  `B_d q_d^*=id` termwise.  Consequently, if the open-cylinder homotopy could identify
  `q_d^*` with the identity on homology, it would force `q_{d,n,*}=d^n` there.  A separate
  assertion that transfer has weight-two eigenvalue `d²` in degree `n=3` would prove vanishing,
  but this eigenvalue is not supplied by Adams--Riemann--Roch: equating `d^n` and `d²` is already
  equivalent to the desired vanishing.  Naive codimension counting also fails because it would
  erase the nonzero degree-two `K₃^{ind}` sector.
- 2026-08-27 — `[NO-GO BOUNDARY]` The displayed `H_{d,n,λ}` is a morphism only after
  semilocalizing `Δ^n×A¹` along the vertex cylinders.  It is generally not a ring map
  `R_n→R_n[λ]`: a target denominator that is nonzero at every vertex can acquire zeros away from
  the cylinders after substitution.  Endpoint equality therefore has finite tame-residue terms
  on the deleted parameter divisors plus the projective-infinity residue.  Corpus projective-line
  reciprocity computes this defect only modulo constants.  Removing it in simplicial degree three
  is precisely the missing second coherence, not ordinary `A¹`-invariance.
- 2026-08-27 — `[FALSIFIED]` Generate every five-term second syzygy using only Dennis--Stein
  triangles.  The corpus proves the triangle defect is the inverse symbol `{v,-1}` and hence
  rationally trivial, but its addition formulas also contain unrestricted symbols `{w,U}`.
  Corpus Sullivan/Koszul modules exhibit independent hollow-simplex syzygies and attach arbitrary
  degree-two syzygies at the second stage.  Thus triangle transport controls orientation and
  `2`-torsion, not generation of the full relation-syzygy module.
- 2026-08-27 — `[POSITIVE SURVIVOR]` Goncharov's complete-quadrilateral involution in the
  appendix of *Geometry of Configurations, Polylogarithms and Motivic Cohomology* has the explicit
  normalized formula

  `s(∞,0,1,a,b)=(∞,0,a(b-1)/(a-1),a,b)`.

  The subgroup generated by six-point boundaries and `x-s(x)` is Suslin's exact universal model
  for the additional relations among five-term relations.  Interpreting this quotient as ordinary
  degree-zero cycles on the rational surface `M̄₀,₅` is false: six-point boundaries preserve the
  inversion local system and do not generate arbitrary rational equivalence.  Suslin's comparison
  identifies the remaining homology with `K₄⁽²⁾`, so such an identification would assume the
  theorem sought.
- 2026-08-27 — `[FALSIFIED]` Combine Suslin's involution with a duality sign contradiction.
  Goncharov's `s` is induced by projective duality of a rank-three six-point configuration.  KRS
  proves categorical duality acts by `-1` on the rank-three critical source and by `+1` on
  `H₂(PGL₂;St₂∞)`; every Rognes differential preserves this eigensplitting.  Hence Suslin's
  duality relations remove the opposite eigenspace, while the weight-two obstruction is the
  permanent `+1` rank-two class.  The apartment-swap duality differs from categorical duality by
  the rank sign; confusing them creates the spurious contradiction.
- 2026-08-27 — `[FALSIFIED]` Fourier--Mukai dimension descent on the Jacobian.  The primitive
  curve class lies in the higher-Chow Beauville component `CH²(J,4)_(3)`, because multiplication
  pullback acts by `m= m^(2·2-3)` on the `h¹(J)` projector.  Fourier transform sends it to
  `CH^(g+1)(Ĵ,4)_(3)`.  Codimension `g+1` is not impossible on a `g`-fold in higher simplicial
  degree `4`; the transformed group can contain three-dimensional higher cycles.  Fourier
  symmetry therefore relocates the same negative motivic extension and gives no vanishing.
- 2026-08-27 — `[POSITIVE SURVIVOR / BRIDGE GAP]` The characteristic-zero modulus no-go has a
  weight-specific refinement.  Goodwillie--Cathelineau identifies
  `K₄⁽²⁾(A[t]/(t^r),(t))_ℚ` with `HC₃⁽¹⁾(A[t]/(t^r),(t))`.  Morrow's Lemma 2.4 proves that for a
  regular local `ℚ`-algebra `A` the pro-system of these lower-Hodge pieces is zero: for every
  modulus `r`, a sufficiently deep transition from modulus `s` to `r` is the zero map.  This is
  exactly compatible with `q_d(J)⊂J^d`, unlike fixed-modulus vanishing (which is false in
  general).  It does **not** yet close the contraction: Miyazaki's `NCH` is the homotopy defect of
  the modulus cycle complex, while Goodwillie computes relative Quillen `K`; no audited comparison
  carries the deleted-divisor error into that pro-`K₄⁽²⁾` tower.  Even after such a comparison,
  pro-zero controls the formal vertex neighborhoods and leaves the global completion phantom.
  Required bridge: a face-compatible localization theorem showing that every infinity-residue
  error of `H_d` is induced from a sufficiently deep relative `K₄⁽²⁾` class, with no residual
  tame-kernel class.
- 2026-08-27 — `[POSITIVE SURVIVOR]` Compactify the affine simplex to `Pⁿ` and let `V_n` be its
  `n+1` coordinate vertices.  The Gersten localization map for the semilocal ring at `V_n`
  embeds `K₂ᴹ(O_{Pⁿ,V_n})/K₂ᴹ(F)` into the finite-support sum

  `⊕_{D∩V_n=∅} K₁ᴹ(F(D))`,

  where `D` runs over prime divisors avoiding every vertex.  This is the exact global residue
  carrier missed by the `J_n`-adic completion; the kernel is constant by unramified `K₂` of
  projective space.  The projective toric power map `[t_i]↦[t_i^d]` acts on this carrier by
  pullback.  It has **no nonzero chain-level fixed residue profile**: pullback on each residue
  field is injective, hence the support of a fixed profile would be a finite totally invariant union
  of divisors.  Away from the coordinate hyperplanes the power map is generically étale, so for
  the reduced union `S` one has `q_d^*S=S`; divisor degree then gives
  `d·deg(S)=deg(S)`, forcing `S=0`.  Coordinate hyperplanes are the only ramified survivors, but
  each contains vertices and is excluded from the carrier.  Remaining gap is homological
  strictness: a fixed class need only have `q_d^*e-e=∂b`, not a fixed representative.  Required
  theorem is that the projective-degree/support filtration on the residue **complex** is strict
  under `q_d`; then minimal support upgrades fixed homology to a fixed leading residue profile.
- 2026-08-27 — `[FALSIFIED / POSITIVE SURVIVOR]` Anderson's resolution of the universal norm
  distribution does not directly supply the missing strictness.  Its hypotheses use a fixed
  scalar coefficient module and relations

  `p(Fr_x⁻¹)[z'] - N_{z(x)}[z(x)z']`,

  whereas a toric pullback residue carries `F(D)×_ℚ` to the varying groups
  `F(E)×_ℚ` by field restriction.  Finite-cover restriction is rationally split by norm, so a
  Mackey-coefficient Anderson complex can still be decomposed into truncated Koszul cubes when
  the coprime base-change squares are distributive.  This kills positive **level** homology but
  leaves its degree-zero primitive coefficient module; the simplicial degree-four homology of
  that module is exactly the possible fixed-class phantom.  Treating Anderson acyclicity as
  vanishing of the distribution itself would therefore discard the unresolved group.
- 2026-08-27 — `[POSITIVE SURVIVOR / BRIDGE GAP]` Allowed residue divisors have no bounded-degree
  inverse tower under toric power maps.  More precisely, let `D` be an irreducible divisor in
  `Pⁿ` avoiding all coordinate vertices, with `n≥2`.  If an irreducible component `E_m` of
  `q_m⁻¹D` had projective degree bounded along unbounded `m`, the deck stabilizer of `E_m` in
  `μ_m^n` would have order `≫m^(n-1)`, since all components form one orbit and
  `(#components)·deg(E_m)=m·deg(D)`.  A bounded-degree Laurent equation for `E_m` has bounded
  exponent differences.  A stabilizer of order `≫m^(n-1)` forces their lattice to have rank at
  most one; over an algebraically closed field, irreducibility then forces a binomial equation.
  The projective closure of a homogeneous binomial can avoid at most the two coordinate vertices
  represented by its two pure monomials, so it meets a coordinate vertex when `n≥2`, contradiction.
  Thus the minimum component degree tends to infinity.  This eliminates bounded torsion-coset
  residue survivors.  It still does not prove homological strictness: a high-degree divisor in
  `P^(n+1)` may restrict to many lower-degree face components.  Required next theorem is an
  associated-graded face acyclicity statement, or a formal--residue fracture argument excluding
  the resulting infinite-tail class.
- 2026-08-27 — `[POSITIVE SURVIVOR / EXACT CURVE CORE]` Déglise's computation of generic motives
  (arXiv:2408.06233v3, Proposition 4.3.2 and Lemma 4.3.7) makes the minimal-transcendence
  obstruction precise.  For `K=k(C)` with smooth projective model and Jacobian sheaf `A`, the
  generic motive has a non-split `1⊕A` quotient, and `A∨≃A(-1)[-2]`.  After lower-dimensional
  `H^(0,2)` terms vanish, the primitive part of `H^(0,2)(K)` is therefore the negative
  abelian-coefficient group

  `Hom_DM(A,Q(2)) ≃ H^(-2,1)(k,A)`.

  Déglise--Kahn--Yamazaki compute the diagonal nonnegative Somekawa groups and prove negative
  contractions of `A` vanish, but neither statement kills `H^(-2,1)(k,A)`.  Claiming that a curve
  has insufficient dimension, or that `A` is a 1-motive, silently assumes the missing negative
  amplitude bound.  A valid new theorem may equivalently prove projective/flat dimension at most
  one for the relevant rational tensor of the abelian sheaf with `G_m`; this bound is not present
  in the audited literature.
- 2026-08-27 — `[POSITIVE SURVIVOR]` In characteristic `p`, `q_p` on simplex coordinates is the
  relative Frobenius.  Absolute Frobenius is coefficient Frobenius followed by `q_p`, and its
  pullback on `K₄⁽²⁾` is multiplication by `p²`.  Since `q_p` is homotopic to the identity in the
  semilocal model, every obstruction obeys

  `Frob_F^*(x)=p²x`.

  This kills classes whose coefficient-Frobenius orbit is finite, recovering the finite-constant
  cases, but not classes over positive-transcendence perfect fields: coefficient Frobenius is an
  outer automorphism and may have a `p²` eigenspace.  Treating perfectness as Frobenius-triviality
  is false.
- 2026-08-27 — `[FALSIFIED / SHARP REFORMULATION]` The generic-curve triangle does not make the
  Jacobian obstruction a formal Ext-vanishing.  Although the abelian sheaf `A` lies in the
  effective homotopy heart and its stabilized zeroth homotopy module has vanishing negative
  contractions, the full stable suspension `Σ∞A` need not lie in the stable homotopy heart.
  Therefore

  `H^(-2,1)(k,A)=Hom_DM(1,Σ∞A(1)[-2])`

  is a higher derived stabilization/tensor class, not a diagonal Somekawa group.  Replacing
  `Σ∞A` by its zeroth homotopy module silently assumes the desired connectivity.  Equivalent
  concrete target: prove that the rational derived tensor of a proper abelian homotopy sheaf with
  `G_m` has no degree-three tail.  This is the curve/Jacobian form of the same second-coherence
  problem, and Déglise's Proposition 5.3.6 explicitly leaves this negative coefficient group as
  the source of `H^(0,2)` for curve function fields.
- 2026-08-27 — `[ACTIVE CONJECTURE / CORPUS-LED SYNTHESIS]` Use a Rees filtration that records both
  vertex depth and polynomial monomial support.  On the associated additive shadow, every
  monomial block has an exact dichotomy.  If a monomial omits a barycentric coordinate, corpus
  theorem `faceComplex_exact` gives an explicit face-cone primitive at that unused coordinate.
  If it omits none, it is divisible by `t₀⋯t_n`, hence lies in the vertex ideal
  `J_n=(t_i t_j)` and `q_d` sends its exponent vector arbitrarily deep.  The latter block is the
  lower-Hodge formal sector controlled pro-zero by Goodwillie--Morrow.  Thus no additive
  monomial block can carry the global completion phantom.

  Required nonlinear comparison: filter relative `K₂` by Dennis--Stein/Milnor degree and prove
  that its associated graded has at most one maximal-degree entry; the unrestricted correction
  terms in `dennisStein_add_left/right` must land in strictly deeper Rees degree.  Then lift the
  corpus face primitives through successive graded layers and prove the Roos `lim¹` class is zero.
  Corpus `CompletionDefectExactnessFlag` only identifies this `lim¹` obstruction; it deliberately
  supplies no vanishing premise.  This comparison is the current named open core.
- 2026-08-27 — `[FALSIFIED / POSITIVE SURVIVOR]` Cyclic coordinate rotation gives no odd-degree
  sign contradiction.  For the cyclic operator `τ_n` the cyclic face identities give an
  uncancelled terminal-face term in `∂τ_n`; the degreewise rotations are not a chain map.  Full
  alternation does give a chain projector: if

  `Alt_n=Σ_{σ∈S_(n+1)} sgn(σ)σ*`, then `∂Alt_n=(n+1)Alt_(n-1)∂`,

  so `Alt_n/(n+1)!` is compatible with the differential over `ℚ`.  On its image, an `(n+1)`-cycle
  acts by `(-1)^n`; the orientation correction needed to make the action compatible with the
  boundary contributes the same `(-1)^n`, hence acts as `+1`.  The proposed contradiction cancels
  exactly.  Survivor: the open `H₃` class may be confined to the alternating residue-incidence
  sector; any support-filtration argument only needs to exclude that oriented sector.
- 2026-08-27 — `[POSITIVE SURVIVOR / FORMAL LOCAL MODEL]` Let `A_n` be the semilocal simplex ring,
  `m_i` its coordinate-vertex maximal ideals, and `J_n=∩_i m_i`.  Pairwise comaximality gives

  `A_n/J_n^r ≅ ∏_(i=0)^n A_n/m_i^r`,  `J_n^r=∩_i m_i^r`.

  Since every `A_(n,m_i)` is regular with residue field `F`, its tangent cone is a polynomial
  algebra in the `n` coordinates pointing from vertex `i` to the other vertices.  Consequently

  `gr_(J_n)(A_n) ≅ ∏_(i=0)^n F[x_j | j≠i]`

  as a graded `F^(n+1)`-algebra, with face maps deleting the excluded vertex component and setting
  the corresponding tangent variable to zero on every surviving component.  Thus Morrow's smooth
  positively graded Hodge argument applies to the actual multivariable formal vertex sector:
  lower Hodge cyclic pieces of the `J_n`-adic quotients are pro-zero.  Constants give the augmented
  simplex complex and have no positive homology.  This proves the formal half of the proposed
  formal--residue fracture.  It does not prove separatedness of simplicial `K₂ᴹ` homology: a class
  can be represented in every `J`-depth without a compatible algebraic primitive, producing the
  Roos `lim¹` already isolated by `CompletionDefectExactnessFlag`.
- 2026-08-27 — `[FALSIFIED]` Spread a primitive curve/Jacobian class and detect it by reduction
  to finite fields.  Specialization maps on higher Chow groups exist, but injectivity on the
  realization-invisible component

  `Hom_DM(A,Q(2)) = H^(-2,1)(k,A)`

  is not known.  Such injectivity is a conservativity/Tate-type assertion; Griffiths-style
  homologically trivial classes show why it cannot be inferred from smooth spread or from
  injectivity after ordinary field extension.  Finite-field Frobenius kills a specialized class,
  but no unconditional theorem recovers the generic class from all these specializations.
- 2026-08-27 — `[FALSIFIED / SHARP KOSZUL CORE]` Kimura's 2026 Bloch--Kriz construction cannot
  be made unconditional by choosing or averaging fillers linearly.  In weight four, two ordered
  copies `D²_(ij),D²_(ji)` fill the same weight-two boundary.  Their difference is an arbitrary
  cocycle in

  `H⁰(N(2)) = CH²(F,4)_Q = K₄⁽²⁾(F)_Q`.

  Replacing both by one chosen filler changes the next coherence by products of that cocycle with
  weight-one classes; it need not remain a boundary.  KRS Theorem 10.9 makes the obstruction
  stricter: pure transcendence preserves `K₄⁽²⁾`, and multiplication by a fresh irreducible
  `p(t)` is residue-injective because its localization boundary is the original class.  Thus fresh
  symbols detect rather than annihilate the filler defect.  This is the same Koszul second
  coherence as the semilocal `H₃` class, now located exactly in the ordering ambiguity of the
  Bloch--Kriz fillers.
- 2026-08-27 — `[POSITIVE SURVIVOR / EXACT BOLBACHAN REDUCTION]` Bolbachan's comparison map is
  already defined and surjective in the target degree:

  `W : N(K,2)^0 -> Lambda(K,2)^0`.

  His 2024 comparison theorem proves injectivity only after truncation to degrees at least one.
  His later degreewise Beilinson--Soule theorem proves `Lambda(K,2)^0=0`.  Therefore every
  degree-zero Bloch chain belongs to `ker W`, while Goncharov's conjecture is exactly the missing
  assertion

  `ker(W : N(K,2)^0 -> Lambda(K,2)^0) = im(d : N(K,2)^(-1) -> N(K,2)^0)`

  on closed chains.  The vanishing generator
  `[P1 x P1, t wedge (1-t) wedge u wedge (1-u)]` is not itself an admissible Bloch cycle because
  each Steinberg pair has a common pole.  Thus Bolbachan's involution proof cannot be copied to
  the cycle complex without a coherent lift of wedge multiplicativity.
- 2026-08-27 — `[FALSIFIED / POSITIVE SURVIVOR]` Extending the decomposable subcomplex
  `im(Sym^2 N(K,1) -> N(K,2))` does not by itself contain the degree-zero comparison kernel.
  The universal multiplicativity homotopy on a surface has vertical faces of the form

  `[F(x,t), t, f(x), g(x)]_(D x P1)`.

  Since `F` depends on both `x` and `t`, these are not external products of two weight-one
  chains.  Survivor: they are one-dimensional families of Bolbachan's already-controlled curve
  multiplicativity homotopy.  A successful proof must totalize these curve families and their
  second coherence, not merely prove acyclicity of the decomposable ideal.
- 2026-08-27 — `[FALSIFIED / ORIENTED DISTRIBUTION SURVIVOR]` The `H0` term left by the
  dilation/universal-distribution Koszul resolution is not killed by simplex alternation.
  A generic deleted divisor has a free `S_(n+1)` orbit, so its rational permutation module
  contains the sign representation.  Hence alternating global residue profiles survive in
  `H0`.  Corpus theorem `deningerCalderonWittGlobalOrientedKoszulSourceComplex_H0_eq_zero`
  identifies the abstract algebraic pattern that would suffice: an injective defect-axis map
  (equivalently an explicit section/trace pairing).  Symmetry supplies no such injection; the
  missing HGT task is to construct it geometrically for residue profiles.
- 2026-08-27 — `[POSITIVE SURVIVOR / REES LOCAL ALGEBRA]` The corpus Dennis--Stein identities do
  satisfy the required finite-layer triangularity more strongly than the raw addition formulas
  suggest.  In the three-index relation with `v=1+abc`, every unipotent correction coefficient is
  a monomial containing an extra product factor, and the apparent residual torus term has the
  exact normal form

  `torusTriangleDefect(v) = {v,-1}^{-1} = {1+abc,-1}^{-1}`.

  Hence this term is relative to the same deeper ideal generated by `abc`; it is not a depth-zero
  exception.  Together with `dennisStein_add_left/right`, this proves the expected triangular
  shape of every elementary binary and ternary presentation move at a fixed nilpotent quotient.
  It strengthens the formal half of the Rees strategy.  It does **not** solve algebraization:
  iterating unit inverses still produces an infinite compatible tower, and no finite-layer
  identity supplies an algebraic primitive for its Roos `lim^1` class.
- 2026-08-27 — `[FALSIFIED / CURVE-FAMILY CORE]` A canonical filler for the special ruled surfaces
  occurring in Bolbachan's multiplicativity homotopy would prove the missing injectivity of `W`,
  but existing strong reciprocity maps only give residue homotopies in the polylogarithmic target.
  They do not lift those homotopies to admissible Bloch chains.  Postulating such a lift, even only
  for the mixed surfaces `[F(x,t),t,f(x),g(x)]`, is the original second-coherence problem in a
  smaller presentation, not an independent theorem.
- 2026-08-27 — `[FALSIFIED / EXACT JACOBIAN OBSTRUCTION]` Projectivity of a curve's birational
  motive does not kill the primitive Jacobian term.  The abelian sheaf `A=J(C)` is a direct
  summand of the projective object represented by the birational `h_0` of `C`, but the relevant
  group is a higher derived tensor/stabilization term, not ordinary `Tor` in that birational
  heart.  Kahn--Sujatha's later derived-unramified results prove birationality of positive
  `Tor(G_m,F)` and exhibit higher-`Tor` pathologies; they give no vanishing.  Kumallagov's 2026
  coproduct theorem controls `R^1_nr`, while its degree-two obstruction is Griffiths-type.  It does
  not provide the missing third-amplitude bound.  Correspondence detection by torsion order also
  applies only when generic `CH_0` has finite torsion order; ruled surfaces over positive-genus
  curves retain exactly the Jacobian summand and fail that hypothesis.
- 2026-08-27 — `[FALSIFIED / UNIFORMITY BARRIER]` Reduction to algebraic closures of finite fields
  cannot currently prove the characteristic-zero case.  A transfer argument would require a
  bound, uniform in the characteristic, on the degree and number of components of a Bloch chain
  filling every bounded-complexity cycle.  Bounded moving lemmas control representatives, not
  nullhomology fillers.  Without the stronger filler bound, vanishing in each finite
  characteristic is not first-order: filler complexity may diverge with `p`, and an ultraproduct
  can retain a nonstandard hyperfinite primitive.  The required uniform bound is at least as hard
  as algebraizing the completion tower and is absent from the audited corpus and literature.
- 2026-08-27 — `[FALSIFIED / DEGREE-SPLITTING WARNING]` The corpus one-variable Milnor filtration
  proves strictness in the opposite direction needed by a naive degree-growth argument:
  `polyResidue_degreeFiltration_eq_zero` kills all lower stages, while
  `exists_mem_degreeFiltrationOnlyAt_milnorResidue_eq` realizes an arbitrary residue at one
  irreducible polynomial with every other same-degree residue zero.  Thus leading divisor
  profiles are independent before simplicial faces are imposed.  No collection of
  face-compatible coordinatewise power maps can force vanishing from projective degree alone.
  Any successful strictness theorem must use the full alternating face equations to pair leading
  residues across adjacent simplicial degrees.
- 2026-08-27 — `[POSITIVE SURVIVOR / EXPLICIT RANK-TWO RESOLUTION]` KRS's projective resolution
  turns the group-homology endpoint into a concrete chain problem.  For `V=F^2`, formal
  correlators are oriented affine triangles; after translation an ordered triangle is an ordered
  basis, and its vertex permutations give the finite `S_3` stabilizer with orientation character.
  Thus `FC(V)` is a rationally projective induced `GL_2(F)`-module.  The entire obstruction lies
  in degree-two homology of the coinvariants of

  `B_k(Dec_V;FC(V)) = Q[Dec_V]^(tensor k) tensor FC(V)`,

  where `Dec_V=V^*\{0}` has left-zero multiplication and the terminal bar face applies the explicit
  decomposition operator `D_h`.  In degree one its boundary is the five-term relation and its
  homology is the Bloch group.  The target is exactly the next syzygy: every relation among those
  five-term boundaries must be generated by the degree-three bar boundary, after removing the
  known central `B_2(F)_Q tensor F^x_Q` summand from `GL_2` to pass to `PGL_2`.
- 2026-08-27 — `[FALSIFIED / ORIENTATION BARRIER]` An affine triangle has three canonical side
  covectors.  Prepending their average to the left-zero bar complex looks like an equivariant
  extra degeneracy, but the construction is identically zero over `Q`: the three covectors form
  the permutation representation of `S_3`, while the triangle carries the sign representation;
  an odd side stabilizer forces any supported equivariant signed average to equal its negative.
  Choosing a generic covector gives a free six-element `S_3` orbit and a nonzero insertion, but
  its equivariance defect is precisely the five-term/Bloch relation.  It therefore preserves the
  known degree-one class and does not yet supply its missing degree-two coherence.  Homological
  vanishing theorems for Steinberg coefficients remain outside this boundary case and add no
  rank-two cancellation.
- 2026-08-27 — `[FALSIFIED / ADELIC FUNCTORIALITY GAP]` Adelic descent cannot by itself glue the
  formal vertex contraction to the open residue contraction.  It reconstructs `K`-theory from
  flags on each fixed semilocal scheme, but coordinate faces are non-flat closed embeddings and
  do not give a flagwise pullback decomposition.  Moreover, units whose zero and pole divisors
  avoid every vertex occur in the generic adelic factor and are not separated by flags of the
  semilocal spectrum.  A compactified/log adelic refinement reintroduces their boundary divisors,
  but its face-compatible totalization is the same formal--residue fracture theorem being sought.
- 2026-08-27 — `[FALSIFIED / UNIVERSAL P1 AVERAGING BARRIER]` Replacing a forbidden finite
  equivariant covector choice by the universal family over `P1(V^*)` does not produce a
  degree-preserving contraction.  Proper pushforward from the family raises geometric dimension;
  preserving motivic weight requires capping with the equivariant hyperplane class
  `c1(O(1))`.  That cap factors through the stabilizer of a line, hence through the same
  Borel/torus induction already separated by the configuration spectral sequence.  Its
  finite-support shadow is exactly the corpus no-go
  `no_equivariant_orbitPushforward_section`; its cycle-theoretic shadow is the Bloch five-term
  defect.  Thus universal averaging either shifts weight or returns to the known first-coherence
  quotient; it cannot reach the primitive `PGL_2` second syzygy.
- 2026-08-27 — `[FALSIFIED / SECONDARY-COBRACKET PARITY BARRIER]` KRS's secondary cobracket
  `delta_sigma : G_3(F) -> H_2(GL_2(F);St_2^infty(F))` cannot source the desired primitive class.
  Their canonical splitting is

  `H_2(GL_2;St_2^infty) = G_2(F) tensor F^x_Q  direct-sum  H_2(PGL_2;St_2^infty)`.

  Projection of `delta_sigma` to the first summand is the known `-delta_(2,1)`.  The remaining
  component is forced to vanish by duality: `G_3` is odd, whereas the primitive `PGL_2` target is
  even (KRS Lemma 9.6), and the rank-spectral differential preserves the involution.  Later
  incoming rank differentials vanish in the relevant range, so the target survives as a
  permanent primitive quotient rather than being killed by a higher-weight source.
- 2026-08-27 — `[FALSIFIED / RECIPROCITY-SHEAF AMPLITUDE GAP]` Reciprocity sheaves do not make
  the Jacobian reformulation connective.  Ivorra--Rülling's reciprocity-functor `K`-groups and
  Sugiyama's SC tensor product identify the underived geometric-symbol quotient.  Saito purity,
  Binda--Rülling--Saito Gysin/proper pushforward, and the Rülling--Saito conductor filtration
  control sections, cohomology, and ramification, but supply no projective-dimension or higher
  derived-tensor bound.  Consequently they see the Somekawa/degree-zero face and not the required
  degree-three tail of `A tensor^L G_m`.  Applying their theorems to
  `H^(-2,1)(k,A)` would first require exactly the stabilization-connectivity statement under
  investigation.
- 2026-08-27 — `[ACTIVE CONJECTURE / RANK-RELATIVE BAR CONTRACTION]` Filter the KRS rank-two
  coinvariant bar complex by the span of its covectors.  The rank-one part is induced from a
  line stabilizer and therefore accounts only for the Borel/torus sector.  On the relative
  rank-two quotient, the first independent pair `(h_i,h_j)` provides the canonical equivariant
  pivot `h_i+h_j`; unlike a unary triangle-side choice, it is nonzero and has no odd-stabilizer
  obstruction.  Conjecture: lexicographic insertion of this pivot, with the terminal
  decomposition face placed in a lower filtration, gives an algebraic Morse contraction in
  degrees at least two.  If the contraction descends through the terminal face, every `H_2`
  class is represented in the rank-one subcomplex; projecting from `GL_2` to the primitive
  `PGL_2` summand then forces it to vanish.  Hard check: prove the terminal `D_h` face is strictly
  lower for a filtration compatible with all other deletions, rather than assuming this from
  covector-span monotonicity.
- 2026-08-27 — `[FALSIFIED / FREE-SPANNING-MODEL SURVIVOR]` The rank-relative pivot does not
  contract after coinvariants.  The semisimplicial set of ordered nonzero covector tuples whose
  span is `V^*` is contractible non-equivariantly (prepend any fixed covector) and its `PGL_2`
  action is free: a group element fixing a spanning tuple fixes a covector basis.  Its quotient
  is therefore a model for `BPGL_2`, not a contractible orbit complex.  Normalizing at the first
  independent pair is a local section of this universal bundle; when a face deletes a member of
  that pair, the change of normalization is a nontrivial transition matrix.  The resulting
  transition-matrix 2-cocycle is precisely what the proposed Morse homotopy omitted.  The
  terminal `D_h` face adds the Steinberg-coefficient twist, but is not the primary failure.
  Positive survivor: rank-one tuples isolate the Borel/central `B_2 tensor F^x` summand, while
  the primitive target is the twisted `BPGL_2` cocycle carried by changes between first-basis
  charts.
- 2026-08-27 — `[FALSIFIED / NOETHERIAN-REES GAP]` A Nakayama argument cannot be applied to the
  power-map orbit of simplicial `K_2^M`.  The vertex-depth filtration lives on chain groups of
  varying localized polynomial rings, not on a finite module over one Noetherian Rees algebra.
  Corpus polynomial-place strictness supplies arbitrarily many independent residue generators,
  and closure under the power maps produces unbounded divisor degree.  Finite generation of the
  resulting homology module would already be a new compactness theorem of essentially the same
  strength as algebraizing the desired primitive; it cannot be inferred from finite support of
  one representative.
- 2026-08-27 — `[POSITIVE SURVIVOR / FORMAL ML CRITERION]` The formal tower has a sharper possible
  closure than bare pro-vanishing.  Maps
  `K_2^M(R/J^(r+1)) -> K_2^M(R/J^r)` are degreewise surjective because units lift across the
  nilpotent kernel.  If the corpus additive face contraction is promoted to vanishing of `H_3`
  for every successive kernel complex, the long exact sequence makes the transition maps on
  `H_4` surjective.  The tower is then Mittag--Leffler, its relevant Roos `lim^1` vanishes, and
  the completed vertex-sector contraction is genuine.  This still leaves one exact global gap:
  injectivity from algebraic simplicial homology into the completed sector after adjoining all
  deleted-divisor residues.  Vertex completion alone is not faithful, as divisors avoiding the
  vertices are invisible there.
- 2026-08-27 — `[POSITIVE SURVIVOR / TORIC CHARACTER DESCENT]` After a finite cyclotomic extension,
  the deck group of `q_(d,n)` is `mu_d^(n+1)/mu_d`.  Its rational character decomposition is
  compatible with faces: restriction to face `i` kills a character unless its `i`th exponent is
  zero.  Semilocal face maps on `K_2^M` are surjective (lift each unit and choose a nonzero value
  at the added vertex), so inserting a zero exponent and applying the Reynolds projector gives
  the usual simplex contraction on every nontrivial character-support block.  Hence only the
  deck-invariant block can contribute to simplicial homology.  Rational ramified descent holds
  for that block: descend at the generic field by restriction/corestriction, then use Gersten;
  vanishing of the pulled-back residue implies vanishing downstairs because ramification indices
  are invertible over `Q`.  Therefore `q_d^*` is surjective as well as split injective on the
  obstruction homology.
- 2026-08-27 — `[OPEN CORE / TORIC SOLENOID]` Surjectivity does not finish the proof.  Iterated
  normalized transfer `d^(-n) q_(d,n),*` lowers codimension-one divisor mass by a factor `d`, but
  introduces denominators of order `d^n`; a rational class can therefore survive as an infinitely
  divisible inverse-limit tail.  Independent polynomial-place residues show chain orbits are not
  locally finite representations of the coordinate torus, so finite-character averaging cannot
  be upgraded to a Zariski-torus average.  Required new theorem: exclude this rational toric
  solenoid in degree-three homology while retaining the nonzero degree-one Bloch sector.
