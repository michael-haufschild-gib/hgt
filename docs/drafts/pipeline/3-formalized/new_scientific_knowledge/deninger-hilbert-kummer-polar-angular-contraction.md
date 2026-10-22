# Hilbert--Kummer polar splitting and angular contraction

- **ID:** `deninger-hilbert-kummer-polar-angular-contraction`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Label:** `DAC_DENINGER_HILBERT_KUMMER_POLAR_ANGULAR_CONTRACTION`
- **Parent:** `deninger-hilbert-kummer-radial-flow-poisson`
- **Lean modules:**
  `GaloisForLFunctions.RHTower.Deninger.DeningerCharacterPolar` (`(1)`, `(2)`, `(4)`),
  `GaloisForLFunctions.RHTower.Deninger.DeningerSphereContraction` (the two deformations of `(8)`, `(9)`),
  `GaloisForLFunctions.RHTower.Deninger.DeningerSphereSlideHomotopy` (`(9)` as a homotopy),
  `GaloisForLFunctions.RHTower.Deninger.DeningerSphereLineHomotopy` (`(8)` as a homotopy),
  `GaloisForLFunctions.RHTower.Deninger.DeningerSphereContractible` (`(6)`),
  `GaloisForLFunctions.RHTower.Deninger.DeningerShift` (the model),
  `GaloisForLFunctions.RHTower.Deninger.DeningerHaarAverage` (`(7)`)
- **Statement:** the Hilbert--Kummer bounded generic character locus
  splits into unitary phase and Hilbert logarithmic modulus; the
  nonzero modulus has contractible infinite-dimensional angular factor,
  so only its radial coordinate contributes ordinary derived
  cohomology.

## Polar decomposition of a character

Let
\[
 V=\overline{\mathbb Q}^{\times}/\mu_\infty
   \otimes_{\mathbb Z}\mathbb Q
\]
and let \(P:\overline{\mathbb Q}^{\times}\to\mathbb C^\times\) be a
generic Deninger character.  Pointwise polar decomposition gives
\[
 P(\alpha)
 =\eta_P(\alpha)\exp L_P([\alpha]),                              \tag{1}
\]
where
\[
 \eta_P(\alpha)=P(\alpha)/|P(\alpha)|\in S^1,\qquad
 L_P([\alpha])=\log|P(\alpha)|\in\mathbb R.                      \tag{2}
\]
Both factors are multiplicative.  The second is a
\(\mathbb Q\)-linear functional on \(V\), and the first retains the
torsion character.

Let \(H=H_{\rm Kum}=L^2(Y,\lambda)\).  On the Hilbert--Kummer bounded
locus, `DAC_DENINGER_HILBERT_KUMMER_RADIAL_SUSPENSION` identifies
\(L_P\) with a unique \(\ell_P\in H'\).  Riesz representation
identifies \(H'\) isometrically with \(H\).  Thus, before Galois and
positive-rational descent, the refined generic locus has the exact
polar form
\[
 \check X_{\rm HK}
 \cong
 \check X_{\rm unit}\times H,                                   \tag{3}
\]
where \(\check X_{\rm unit}\) is the source unitary-character locus
carrying Deninger's Tate--Kummer class.

Under Frobenius,
\[
 (\eta,h)\longmapsto(\eta^q,qh).                                \tag{4}
\]
Galois acts on the first factor by character transport and on the
second by the Allcock--Vaaler unitary representation.

## Angular contraction theorem

`[PROVED HERE] [DAC_DENINGER_HILBERT_KUMMER_POLAR_ANGULAR_CONTRACTION]`

The real Hilbert space \(H=L^2(Y,\lambda)\) is infinite-dimensional
and separable.  Its punctured space has the polar homeomorphism
\[
 H\setminus\{0\}
 \xrightarrow{\sim}
 S(H)\times\mathbb R_{>0},\qquad
 h\longmapsto(h/\|h\|,\|h\|).                                   \tag{5}
\]
The unit sphere \(S(H)\) is contractible.  Consequently
\[
 R\Gamma(S(H),\mathbb R)\simeq\mathbb R[0],                     \tag{6}
\]
and the modulus-angular factor creates no positive-degree ordinary
cohomology.

If a compact group \(G\) acts unitarily on \(H\), then for complete
real or complex coefficient modules on which Haar integration is
defined, invariants are exact.  Applying invariants to `(6)` gives
\[
 R\Gamma(S(H),\mathbb R)^G\simeq\mathbb R[0].                   \tag{7}
\]
Thus coarse Galois invariants do not reintroduce an angular derived
class in the degreewise-invariant coefficient model.

### Proof

The maps in `(5)` and their inverse \((\omega,r)\mapsto r\omega\) are
continuous.

For contractibility, choose a Hilbert isometry
\(H\cong\ell^2(\mathbb N,\mathbb R)\), let \(S\) be the unilateral
shift, and let \(e_0\) be the first basis vector.  No nonzero vector is
an eigenvector of \(S\).  Hence
\[
 K_1(x,t)
 =
 \frac{(1-t)x+tSx}{\|(1-t)x+tSx\|},
 \qquad 0\le t\le1,                                               \tag{8}
\]
is well-defined and deforms the identity of the unit sphere to \(S\).
Since \(e_0\perp\operatorname{im}S\),
\[
 K_2(x,t)
 =
 \sqrt{1-t^2}\,Sx+t e_0                                         \tag{9}
\]
stays on the unit sphere and deforms \(S\) to the constant \(e_0\).
Concatenating `(8)` and `(9)` contracts \(S(H)\), proving `(6)`.

For `(7)`, let \(C^\bullet\) be a complete continuous cochain model.
The inclusion of constants
\(\mathbb R\to C^\bullet(S(H),\mathbb R)\) is a
\(G\)-equivariant quasi-isomorphism by `(6)`.  Compact-group
invariants are exact: an invariant element in a quotient is lifted
arbitrarily and its orbit is averaged with normalized Haar measure.
Taking invariants therefore preserves the quasi-isomorphism.

## Arithmetic interpretation

Combining `(3)` and `(5)`, the nonunitary refined locus is
\[
 \check X_{\rm unit}\times S(H)\times\mathbb R_{>0}.             \tag{10}
\]
The factors have distinct roles:

1. \(\check X_{\rm unit}\) carries the nontrivial pro-torus
   Tate--Kummer/Milnor coefficient.  It is not contracted.
2. \(S(H)\) is the modulus direction and is cohomologically trivial by
   `(6)`--`(7)`.
3. \(\mathbb R_{>0}\) is the canonical Kummer radius.  After
   suspension it carries the dilation flow and Meyer's
   Poisson--zeta complex.
4. The omitted locus \(h=0\) is the unitary boundary.  It supplies the
   radial evaluation \(f(0)\); it must be joined to the real
   Fourier-dual boundary rather than declared acyclic.

This is the source explanation for why the Poisson middle coefficient
has one radial variable despite the infinite-rank Kummer character
space.

## Remaining topological gate

Equations `(6)`--`(7)` are ordinary derived statements.  To obtain the
actual comparison one must still prove their strict nuclear analogue:

- completed tensoring with the Tate--Milnor phase coefficient;
- the mixed \(L^1/L^2\) and residue graph topologies;
- compact support in the radial variable only;
- commutation with the infinite flow sum;
- identification of the \(h=0\) boundary maps with
  \(f(0)\) and \(\mathcal Ff(0)\).

Contractibility alone does not prove those strict locally convex
claims.

## Hostile audit

- No averaging over an infinite-dimensional orthogonal group is used.
- No nonexistent Haar probability on \(S(H)\) is assumed.
- The unitary phase factor is retained; only modulus direction is
  contracted.
- The contraction need not be Galois-equivariant.  Exact compact
  invariants are applied to the equivariant quasi-isomorphism from
  constants instead.
- No zeta zero, RH, CCM object, or numerical computation occurs.

## References

- Daniel Allcock and Jeffrey D. Vaaler,
  *A Banach space determined by the Weil height*:
  https://arxiv.org/abs/0808.1038
- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  generic character space and Tate regulator:
  https://arxiv.org/abs/1807.06400

## Log

- 2026-07-27 — Split the bounded character locus into phase and modulus
  and proved the infinite-dimensional modulus sphere contributes no
  angular ordinary cohomology.

## Lean status

### The polar decomposition landed

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerCharacterPolar.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerCharacter_polar` — **`(1)`--`(2)`**: `P(α) = η_P(α)·exp(L_P(α))`, with
  `η_P = P/|P|` and `L_P = log|P|`.  Unconditional: a character of a *group* into `ℂ` never
  vanishes, so no nonvanishing hypothesis is needed.
- `deningerCharacter_eq_modulusReplace` — the same decomposition read through the modulus
  replacement of the parent card, which is what makes the two factors independently deformable.
- `deningerCharacter_polar_norm` — the factors really are a phase and a positive scale:
  `‖η_P(α)‖ = 1` and `exp(L_P(α)) > 0`.
- `deningerUnitPart_zpow` together with `deningerLogModulus_zpow` (parent card) — **`(4)`**: under
  the power map the phase is raised to the exponent and the modulus is multiplied by it,
  `(η, h) ↦ (η^q, q·h)`.

### The two sphere deformations landed

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerSphereContraction.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

Both statements are proved for an arbitrary real inner product space and an arbitrary linear
isometry with the stated properties, so no model of `H` has to be fixed yet.

- `deningerSphereLine_ne_zero` — **`(8)` is defined**: if the isometry `S` has no eigenvector, the
  segment `(1-t)x + tSx` from a unit vector to its image never meets the origin, so it can be
  normalized.  At `t = 0` the point is `x ≠ 0`; for `t > 0` vanishing would make `x` an eigenvector
  of `S` with eigenvalue `-(1-t)/t`.
- `deningerSphereSlide_norm` — **`(9)` stays on the sphere**: if `e` is a unit vector orthogonal to
  the range of `S`, then `‖√(1-t²)·Sx + t·e‖ = 1` for every unit `x` and `t ∈ [0,1]`, by the
  Pythagorean expansion and `‖Sx‖ = ‖x‖`.

### The quarter-circle homotopy landed

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerSphereSlideHomotopy.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerSphereIsometryMap` — a linear isometry restricts to a continuous self-map of the unit
  sphere.
- `deningerSphereConstMap` — the constant map at a unit vector.
- `deningerSlideHomotopy` — **`(9)` as a bundled `ContinuousMap.Homotopy`** from the isometry to
  that constant map, given that the vector is orthogonal to the range of the isometry.  The
  sphere-membership of every intermediate point is the previous module's
  `deningerSphereSlide_norm`; the endpoints are `t = 0`, where the square root is one, and
  `t = 1`, where it is zero.

So the second half of the contraction is complete as a homotopy.

### The angular contraction `(6)` landed

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerSphereLineHomotopy.lean` and
`formal/GaloisForLFunctions/RHTower/Deninger/DeningerSphereContractible.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerSegment`, `deningerSegment_ne_zero`, `deningerSphereLineHomotopy` — **`(8)` as a
  homotopy** from the identity of the unit sphere to the isometry, along segments normalized to
  unit length.  Well-definedness is the eigenvector-free hypothesis; continuity is continuity of
  the segment together with `Continuous.inv₀` applied to its norm, which is nonvanishing exactly by
  that hypothesis.
- `deningerSphere_nullhomotopic`, `deningerSphere_contractible` — **`(6)`**: concatenating the two
  homotopies (`ContinuousMap.Homotopy.trans`) makes the identity of the sphere nullhomotopic, hence
  `ContractibleSpace (Metric.sphere 0 1)` by `contractible_iff_id_nullhomotopic`.

The statement is proved for any real inner product space carrying an eigenvector-free linear
isometry whose range misses a unit vector.  Such an isometry exists precisely in infinite
dimensions, so this is the infinite-dimensional sphere contractibility that mathlib lacks, in the
form the card's `(6)` needs.

### The model landed — the unit sphere of `ℓ²(ℕ, ℝ)` is contractible

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerShift.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerShiftFun`, `deningerShiftFun_memℓp`, `deningerShift` — **the unilateral shift** as a
  linear isometry of `lp (fun _ : ℕ => ℝ) 2`.  Square-summability and norm preservation are the
  same series reindexed along `Nat.succ`, using `Function.Injective.summable_iff` and
  `Function.Injective.tsum_eq` with the support contained in the range of `succ`.
- `deningerShift_no_eigenvector` — **the shift has no eigenvector**.  Coordinatewise, `Sx = c·x`
  reads `0 = c·x₀` and `xₙ = c·xₙ₊₁`.  If `c = 0` the second equation alone kills every
  coordinate; if `c ≠ 0` the first kills `x₀` and the second propagates by induction.
- `deningerE0`, `deningerE0_norm`, `deningerShift_perp` — the first basis vector is a unit vector
  orthogonal to the range of the shift, since every shifted sequence vanishes at zero.
- `deningerL2SeqSphere_contractible` — **the unit sphere of `ℓ²(ℕ, ℝ)` is contractible**,
  instantiating the abstract contraction.

This is the model the card's `(6)` names, and it makes the contractibility statement concrete
rather than conditional on the existence of such an isometry.  mathlib has neither the shift nor
the contractibility.

### Haar averaging `(7)` landed

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerHaarAverage.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerHaarAverage μ ρ m = ∫ g, ρ g m ∂μ` — the orbit average against a left-invariant
  probability measure on a compact group acting by linear isometries.
- `deningerOrbit_integrable` — the orbit map is integrable: it is continuous, and on a compact
  space every function has compact support.
- `deningerHaarAverage_invariant` — **the average is invariant**: the isometry passes through the
  integral (`ContinuousLinearMap.integral_comp_comm`), turning `ρ g₀ ∘ ρ g` into `ρ (g₀ * g)`, and
  left invariance of the measure absorbs the translation.
- `deningerHaarAverage_of_invariant` — it fixes vectors that are already invariant, since the
  integrand is constant and the measure has total mass one.
- `deningerInvariants_surjective` — **`(7)`**: for an equivariant continuous linear map, an
  invariant vector downstairs is the image of an invariant vector upstairs, namely the average of
  any lift.  This is the exactness of compact-group invariants the card uses to pass `(6)` to
  invariants.

## Status: fully formalized

Every numbered statement of this card is an unconditional Lean theorem.  Axiom audits throughout:
`propext, Classical.choice, Quot.sound` only.

| Statement | Lean |
|---|---|
| `(1)`, `(2)` polar decomposition | `deningerCharacter_polar`, `deningerCharacter_polar_norm` |
| `(4)` Frobenius on the two factors | `deningerUnitPart_zpow`, `deningerLogModulus_zpow` |
| `(5)` polar homeomorphism | mathlib's `homeomorphUnitSphereProd` |
| `(6)` angular contraction | `deningerSphere_contractible`, `deningerL2SeqSphere_contractible` |
| `(8)`, `(9)` the two deformations | `deningerSphereLineHomotopy`, `deningerSlideHomotopy` |
| `(7)` invariants | `deningerInvariants_surjective` |

Built here because mathlib lacks them: contractibility of the unit sphere of an
infinite-dimensional Hilbert space, and the unilateral shift on `ℓ²(ℕ, ℝ)` with its
eigenvector-freeness.

### Gates

- [x] 0 → 1 in-progress
- [x] 1 → 2 fully-proven
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready
