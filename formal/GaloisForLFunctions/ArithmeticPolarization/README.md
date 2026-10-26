# Arithmetic Polarization (APol)

**One question.** Over `𝔽_q` the sign of the explicit formula is a consequence of a
*polarization*: an ample class on `C × C` (the theta divisor on the Jacobian), whose sections make
the Rosati trace `τ(ξ ξ′)` an intersection number of effective classes and hence nonnegative. Over
`ℤ` the corpus has every other layer of Weil's argument — the identities, the theorem of the
square, the budget — and has proved that every positivity it can build from invariance is
isotropic at off-line zeros. What structure on the correspondence surface of `Spec ℤ` could play
the polarization, by which *mechanism* can a positivity be a theorem about that structure rather
than a consequence of a symmetry, and what does each mechanism give for `ζ`?

APol is the theory of **positive structures on reflection pairs** and of the operations that
create, localize, collide and complete them. Its basic object is a *polarized correspondence
surface*: a correspondence surface (ACP) together with a positive trace and the mechanism that
makes it positive. Its basic invariant is the **local type** of a positive structure at a
reflection pair `{ρ, ρ* = 1 − ρ̄}`: isotropic, definite (elliptic), or collided. Its basic
principle is

> *Positivity excludes a pair only through an indefinite fibre.* A symmetry that is hyperbolic at
> the pair makes every invariant positive fibre isotropic; a symmetry that is elliptic at the pair
> makes the fibre definite, positive on one sector and negative on the other. A polarization is a
> positive structure whose sign does not come from either.

Namespace `GaloisForLFunctions.ArithmeticPolarization`; umbrella `ArithmeticPolarization.lean`.
Everything is unconditional; RH and its partial forms appear only inside equivalences.

---

## 1. Place in the research

The frontier's B-tier obstacles (B1.3, B1.6, B1.9, B1.10, B3.5, B3.25–B3.28) are one missing
object in several currencies: a **polarization of the correspondence surface of `Spec ℤ`**, a
positive structure on the Hecke–archimedean correspondences whose positivity (i) is a theorem about
the structure — from counting or from a non-hyperbolic localizing symmetry — and not a consequence
of invariance, (ii) sees the sign of prime-power atoms, and (iii) has an exterior part that collides
conjugate zeros without an ordinate-dependent conductor. Over `𝔽_q` Riemann–Roch and an ample class
on `C × C` supply it, with `Λ²H¹` inside the cohomology of the surface. Over number fields no
existing theory does: arithmetic intersection theory lives on arithmetic surfaces fibred over
`Spec ℤ`, not on its square; the scaling site has Riemann–Roch on the base while its Hodge index on
the square is RH; one-variable positive objects are exhausted at classical strength.

APol is the extension of three programmes by that object.

| Programme | What APol takes | What APol adds |
|---|---|---|
| [ArithmeticCorrespondencePositivity](../ArithmeticCorrespondencePositivity/README.md) | correspondence surfaces, normalized graphs, the budget, determinant and Rosati degrees, the local form `2 Re(u v̄)` and its boosts, the layer map L1–L6, the contraction and collision calculus, escape states | the elliptic and collided local types, their localizers and their price; the polarization layer L5 as an object |
| [ArithmeticCorrelationGeometry](../ArithmeticCorrelationGeometry/README.md) | the gauge torus, gauge-invariant and gauge-charged statistics, the loss laws, the gauge mass of escape states | the identification of the first gauge charge with an archimedean twist; charged weights `Λ(n) cos(γ log n)` as the arithmetic side of elliptic localization |
| [ArithmeticPositiveDuality](../ArithmeticPositiveDuality/README.md) | positive Poisson pairs, Hamburger rigidity, the `κ = 1` collapse, the exhaustion map of forcing mechanisms, archimedean–successor coupling | rigidity probes for coupled classes; capacity of positive structures that are not deformations |

Further interfaces:

| Programme | Interface |
|---|---|
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | scaling surface, curve data, the golden datum, effectivity with RR + ample, the universal floor law (every ample cone with RR forces the defect floor), the maximal blind ideal, the Fejér barrier of harmonic coupling |
| [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md) | scaling data, Rosati positivity = orbit Hodge index, damping automorphisms, the theta `h⁰` of `Spec ℤ` and its Riemann–Roch |
| [StripBochnerWeilForcing](../StripBochnerWeilForcing/README.md), [MultiplicativePositivityGeometry](../MultiplicativePositivityGeometry/README.md) | completed positive systems, collar capacity, boundary forcing, positive-definite functions |
| [ArithmeticKunnethTheory](../ArithmeticKunnethTheory/README.md) | product receivers, depth homogeneity, Künneth positivity as point-count positivity |
| [ArithmeticDefectRigidity](../ArithmeticDefectRigidity/README.md) | cofactor modules, translated-zero escape eigenstates |
| [SquareRootThreshold](../SquareRootThreshold/README.md), [BiScaleUncertainty](../BiScaleUncertainty/README.md) | window certificates for every prime weight, the Liouville twist on the odd window, modulated tests and the twist identity of the prime side |
| [arithmetic-positivity-theory](../arithmetic-positivity-theory/README.md) | single-height phase-selective detection with modulated tests |
| `Zeta23`, RHTower | zero configurations `ZeroConfig` and Weil's form `Z.W`, the explicit formula, digamma bounds |

---

## 2. Why

**The exhaustion map has one shape.** Every positivity the corpus has proved unconditionally for a
carrier that sees off-line pairs is a consequence of invariance, and every such positivity is
isotropic there:

- Hecke operators, the archimedean flow and every gauge twist act on the fibre of an off-line pair
  by boosts `diag(β, β′)`, `β β̄′ = 1`, `|β| ≠ 1` (ACP P4); invariant positive subspaces of a boost
  are isotropic;
- isometries of the local form separate the two points of a pair only as boosts (ACP P13);
- the successor is unipotent on polar fibres (ACP P5);
- positivity with full fibres exists only on non-localizing carriers, and there it holds for every
  prime weight (ACP P6);
- on nonnegative tests `ζ` is the worst member of its sign orbit (ACP P7);
- one-variable positivity is Landau–Fejér positivity: real anchors of twice the weight, the barrier
  `a₁ < 2a₀`, the classical local count at `2 + iγ` (ACP P25).

**What a polarization does over `𝔽_q`.** The Rosati trace of an endomorphism `ξ` of the Jacobian is,
up to a positive constant, the intersection number `ξ*Θ · Θ^{g−1}`: the pullback of the theta
divisor is the divisor of a section, an effective class, and an effective class meets powers of an
ample class nonnegatively. The positivity is a count — of zeros of a section on a curve — and it is
not a consequence of any symmetry of the Frobenius: the Frobenius acts on the off-line part of a
fake datum just as hyperbolically as Hecke operators act over `ℤ`, and Weil still wins because the
trace is positive on the *whole* ring for an independent reason. Hyperbolic localization then turns
that positivity into the vanishing of the off-line pair.

**Three conceivable sources over `ℤ`.**

1. *Counting* (Q3): a section count on the correspondence surface with a Riemann–Roch whose
   quadratic term is Weil's form.
2. *Elliptic localization* (Q1): a localizing operation whose local symmetry at an off-line pair is
   not hyperbolic, so that positivity there is not forced to be isotropic.
3. *Charge* (Q2): a positivity that reads the sign of prime-power atoms, so that it can distinguish
   `ζ` from its gauge twins.

APol's organizing discovery is that the second and third sources are one object, and that the
fourth phenomenon of the frontier — collisions of conjugate zeros cost conductor over `ℤ` — is the
price of that object:

> **Elliptic localization is archimedean twisting.** Among the affine maps of the `s`-plane that
> commute with the Rosati reflection `s ↦ 1 − s̄`, the only non-identity map stabilizing an off-line
> pair at ordinate `γ` is the point reflection `σ_γ(s) = 1 + 2iγ − s`, which swaps its two points.
> It is the functional equation conjugated by the archimedean flow by `γ`. On tests it is
> `g ↦ e^{−2iγu} g(−u)`; its sectors are the even and odd tests of the twisted source `ζ(s + iγ)`;
> in them the complex quartets of `ζ` at ordinate `γ` become real pairs; the even sector is
> positive at a real pair (the pair is invisible to positivity), the odd sector is negative there
> (positivity excludes it); the prime side carries the charged weights `Λ(n) cos(γ log n)`; the
> archimedean side carries `Γ_ℝ(s ± iγ)` and the poles move to `±iγ, 1 ± iγ`. The positive
> completion of the charged weights by a nonnegative cosine polynomial is the height-coupled lift,
> and the Fejér barrier is its limit.

So the frontier's questions Q1 (a non-hyperbolic localizer), Q2 (gauge charge), B3.27 (an
arithmetic exterior count) and §4.4.8 (the archimedean place) meet in one carrier: the **odd sector
of the archimedean twist at height `γ`**. Its positivity at the localizing aperture `≍ log γ` is RH
at height `γ`; at bounded aperture it is source-blind. APol makes this precise, builds the
calculus of twists, collisions and completions around it, and asks what a positivity on it that is
neither invariant nor non-localizing would have to be.

---

## 3. Objects and language

| Over `𝔽_q` | APol object | Over `ℤ` | Owner |
|---|---|---|---|
| `(End J ⊗ ℚ, ′, Tr)` | polarized ring: algebra with involution and a trace `τ` with `τ(ξ ξ′) ≥ 0` | Hecke algebra of `ℝ_{>0}` with `ξ′(g) = ξ(−g)` and the Rosati trace `τ_x` | APol, AOG |
| ample class, theta divisor | polarization class | `H + V` on the scaling surface | ACS |
| `h⁰(D)` | section count on classes of a correspondence surface | base theta `h⁰(d) = log Σ e^{−πn²e^{−2d}}`; lattice counts on the square | AOG, APol |
| eigenvalue pair `{α, q/ᾱ}` | reflection pair `π = {ρ, ρ*}` with fibre `(ĝ(ρ), ĝ(ρ*))` and local form `2 Re(u v̄)` | zeros `ρ ↦ 1 − ρ̄` | ACP |
| Frobenius action on a pair | local type: hyperbolic (boost), elliptic (swap or rotation), unipotent, collided | Hecke, archimedean flow; `σ_γ`; successor; real pairs | ACP, APol |
| — | reflection-commuting affine group `s ↦ ½ + λ(s − ½) + iκ` | dilations of tests, archimedean flow | APol |
| — | point reflection `σ_γ(s) = 1 + 2iγ − s`; elliptic localizer | `g ↦ e^{−2iγu} g(−u)` | APol |
| — | twisted configuration `Z − iγ`; twisted sector (even/odd tests of the twist) | `ζ(s + iγ)` | APol |
| `Λ²H¹`, eigenvalues `α_i α_j` | exterior divisor `{ρ_j + ρ_k − ½}`; collided point `2 Re ρ − ½` of a conjugate pair | height-coupled lift `ζ(s)² ζ(s + iγ) ζ(s − iγ)` | ACP, APol |
| — | charged weight `Λ(n) cos(γ log n)`; positive completion by a cosine polynomial | Fejér barrier `a₁ < 2a₀` | ACS, APol |
| — | conductor of a localizer: the archimedean shift `Γ_ℝ(s ± iγ)` | `≍ log γ` | APol |
| fake curves | battery: golden datum, complex fake, twins, `CompletedPositiveSystem 2 1`, height-coupled lifts | — | ACS, ACP |

**Words.**

- *Polarization*: a positive trace on a correspondence ring compatible with its involution.
  *Mechanism* of a polarization: invariant (its positivity follows from invariance under a
  symmetry), counting, elliptic, charged.
- *Fibre* of a carrier at a pair `π`: the image of `g ↦ (ĝ(ρ), ĝ(ρ*))`. *Localized fibre*: the image
  on carrier elements that vanish at every other pair.
- *Isotropic* fibre: `Re(u v̄) = 0` on it. *Definite* fibre: contained in a line `u = ± v`, positive on
  `u = v`, negative on `u = −v`.
- *Elliptic localizer* at ordinate `γ`: the point reflection `σ_γ`. Its *even* (*odd*) sector: tests
  with `σ_γ g = g` (`= −g`). *Blind half*, *forcing half*: the sector on which off-line pairs at
  ordinate `γ` are positive, negative.
- *Twist* at `γ`: `g ↦ e^{iγu} g`, the archimedean flow on tests; *twisted configuration* `Z − iγ`.
- *Collision*: a complex quartet sent to a real pair (by a twist), or a conjugate pair sent to one
  real point of the exterior divisor. *Ordinate-local* versus *global* collision.
- *Charged weight*: a prime weight that changes sign at prime powers. *Positive completion*: a
  nonnegative combination of twists whose weights are nonnegative; its *anchor weight* and *pole
  weight*.
- *Conductor* of a localizer: the growth of its archimedean term with the ordinate.
- *Diagonal collapse*: a count on the square of `Spec ℤ` whose arithmetic depends only on
  `s₁ + s₂`.

The numerical parameters are the **ordinate** `γ` (where a localizer acts), the **depth** `a` of a
pair, the **aperture** `A` (support of tests), the **height** `T`, the **pole order** `κ` and the
**degree** `d`. Every theorem states which are fixed and which grow.

---

## 4. Mechanisms

1. **Polarization law.** In a finite-dimensional `*`-algebra with a faithful positive trace, left
   multiplication by an element with `ξ ξ′ = c > 0` is `√c` times an isometry of the trace inner
   product; every eigenvalue has modulus `√c`. This is the whole of Weil's step from Rosati
   positivity to purity.
2. **Local sign principle.** On the local form `2 Re(u v̄)` a positive real subspace invariant under a
   boost is isotropic; a subspace invariant under the swap `(u, v) ↦ (v, u)` splits into the lines
   `u = ± v`, positive and negative definite. Positivity therefore excludes a pair only where its
   fibre contains a negative direction.
3. **Affine classification.** Affine maps of `ℂ` commuting with `s ↦ 1 − s̄` are
   `s ↦ ½ + λ(s − ½) + iκ`, `λ ∈ ℝ^×`, `κ ∈ ℝ`. The stabilizer of an off-line pair is `{id, σ_γ}`; the
   stabilizer of a critical point is a one-parameter family of dilations about it. The arithmetic
   operations (Hecke translations as multipliers, the archimedean flow `s ↦ s + iκ`, the functional
   equation `s ↦ 1 − s`) generate the vertical translations and the point reflections.
4. **Conjugation of the functional equation.** `σ_γ = τ_γ ∘ σ_0 ∘ τ_{−γ}`, `τ_κ(s) = s + iκ`; on tests
   `σ_γ g = e^{−2iγu} g(−u)`, and `σ_γ`-symmetric tests are the twists `e^{−iγu} r` of even (or odd)
   `r`.
5. **Twist identity.** `Z.W(e^{−iγu} r, e^{−iγu} r) = (Z − iγ).W(r, r)`: Weil's form of `ζ` on a
   twisted test is Weil's form of the twisted configuration; its prime side carries
   `Λ(n) cos(γ log n)`, its poles sit at `±iγ`, `1 ± iγ`, its archimedean density is shifted by `γ`.
6. **Collision.** A quartet `{½ ± a ± iγ}` of `Z` is the real pair `{½ ± a}` of `Z − iγ`. On real
   tests the local form at a real pair is `2 r̂(½ + a) r̂(½ − a)`: `+2 r̂(½+a)²` on even tests,
   `−2 r̂(½+a)²` on odd tests.
7. **Dihedral dilemma.** A boost `B` and the swap `S` at the same pair satisfy `S B S = λ B^{−1}`,
   `|λ| = 1`; a subspace invariant under both is isotropic. Hecke separation and elliptic symmetry
   cannot be used at the same pair; the `σ_γ`-compatible Hecke operators are the twisted symmetric
   operators `T_p + p^{2iγ} T_p^{−1}`, which act on the pairs at ordinate `γ` by scalars.
8. **Positive completion.** `Λ(n) P(γ log n) ≥ 0` for every nonnegative cosine polynomial `P`; the
   completion `Π_k F(s ± ikγ)^{a_k/2}` has real anchors of weight `a₁ m` against pole weight
   `2a₀ m`, and Fejér's inequality `a₁ < 2a₀` bounds every completion.
9. **Exterior divisor.** The exterior divisor of a configuration is `{ρ_j + ρ_k − ½}`; a conjugate
   pair collides at the real point `2 Re ρ − ½`; for `ζ` the conjugate-pair sums `½ + i(γ_j − γ_k)`
   accumulate at `½`, so no meromorphic function carries the global collision.
10. **Diagonal collapse.** The theta count of a rank-one sublattice `ℤ(n, m)` of `ℤ²` with the
    product metric has two-variable Mellin transform `Γ_ℝ(s₁) Γ_ℝ(s₂) n^{−s₁} m^{−s₂} ζ(s₁ + s₂)`;
    rank-two counts factor through products `L(s₁, χ) L(s₂, χ′)`. Lattice counts on the square see
    either one variable or a product, and on the reflection plane `s₂ = 1 − s̄₁` a product is a
    modulus square: counting on the square of `Spec ℤ` produces determinant positivity, never Rosati
    positivity.

---

## 5. Pillar theorems

| Pillar | Statement |
|---|---|
| **Π1 The polarization law** | Faithful positive traces turn similitudes into isometries; every eigenvalue of a similitude of ratio `c` has modulus `√c`. Calibration: for a curve datum the Rosati trace of `ℝ[F]` is a polarization iff the datum is unitary; the golden datum and the complex fake have none. |
| **Π2 The local sign principle** | Boost-invariant positive fibres are isotropic; swap-invariant fibres are definite; positivity excludes a pair only through a negative direction of its fibre. |
| **Π3 The elliptic localization law** | Classification of reflection-commuting affine maps; the stabilizer of an off-line pair is `{id, σ_γ}`; `σ_γ` is the functional equation conjugated by the archimedean flow; the `σ_γ` sectors are the even and odd sectors of the twist. |
| **Π4 The twist and collision identities** | `Z.W` on twisted tests is the Weil form of `Z − iγ`; ordinate-`γ` quartets become real pairs; the even sector is positive and the odd sector negative at a real off-line pair. |
| **Π5 The price of elliptic localization** | The prime side of the twisted form has the charged weights `Λ(n) cos(γ log n)`; its poles are at `±iγ, 1 ± iγ`; its archimedean term is the digamma density shifted by `γ`, of size `½ log γ + O(1)`. |
| **Π6 The dihedral dilemma** | Hecke boosts and the elliptic swap at the same pair generate a group whose invariant positive subspaces are isotropic; the `σ_γ`-compatible Hecke algebra is the twisted symmetric algebra and acts by scalars at ordinate `γ`. |
| **Π7 The Fejér barrier for coupled contraction** | For every nonnegative cosine polynomial with nonnegative coefficients, the harmonic completion never removes the whole lifted divisor of a deepest quartet. |
| **Π8 The collision law** | Exterior divisors and conjugate collision; non-meromorphy of the global collision of `ζ`; ordinate-local collisions are twists. |
| **Π9 The diagonal collapse** | Lattice counts on the square of `Spec ℤ` are diagonal or Künneth; on the reflection plane they are modulus squares. |
| **Π10 The first gauge charge is a twist** | On windows reading only the atom `2`, the Liouville flip and the archimedean twist at `π / log 2` have the same prime side; the twin differs from the twisted form of `ζ` only by the archimedean and polar terms. |

Further pillars belong to the questions of §6 (rigidity probes, oscillatory capacity, loss laws).

---

## 6. The questions

The eleven questions of the frontier report (§4.4), with the form an answer must take.

1. **What is the polarization?** Which class plays the ample divisor, so that the Rosati trace is
   positive for a reason other than RH? The ample class exists (`H + V`); what is missing is the
   effectivity that makes it ample. Answer form: the polarization law (Π1) with its calibration, and
   for each mechanism the exact statement it produces over `ℤ`.
2. **What counts sections?** A genuine dimension `h⁰` on normalized graphs with Riemann–Roch.
   Answer form: the counting law — which counts the square of `Spec ℤ` carries (Π9), what their
   Riemann–Roch is, and why their positivity is determinantal.
3. **Which localizer is not hyperbolic?** Answer form: the elliptic localization law (Π3–Π6): the
   localizers, their sectors, their forcing half and its price.
4. **Where is the gauge charge?** Answer form: the charged weights of the twist (Π5) and the
   identification of the first gauge charge (Π10); the separating aperture of each twin.
5. **What is the exterior square of the spectrum?** Answer form: the collision law (Π8); the height-
   coupled lifts as ordinate-local collisions; the obstruction to a global meromorphic one.
6. **Is a coupled class rigid?** `HeightCoupledSystem 2 1 1 γ = ℝ^× · ζ_γ`? Answer form: the
   implication from rigidity at `γ` to the absence of off-line zeros at `γ`, and probes at zero-free
   ordinates.
7. **What pays `ζ`'s own zeros?** Answer form: an oscillatory capacity graded by depth.
8. **How does the archimedean place enter?** Answer form: as the conductor of the elliptic
   localizer (Π5): every localization in height pays the shifted Gamma factor.
9. **What are escape states of `ζ`?** Answer form: the explicit-formula split of the cofactor profile
   and the arithmetic content of positive gauge mass.
10. **How does an average become a point?** Answer form: selection lemmas at the zero spacing; the
    aperture at which the forcing half of a twisted sector localizes.
11. **What is the base?** Answer form: loss laws for the remaining amplification classes (harmonic
    twists, Følner coupling).

---

## 7. Traps

| Trap | Truth |
|---|---|
| An elliptic symmetry gives a positivity that can exclude a zero | Its fibre is definite: on the even sector an off-line pair is positive and invisible; only the odd sector forces |
| The functional equation is an elliptic localizer | It swaps pairs only on the real axis; at ordinate `γ` the localizer is the FE conjugated by the archimedean flow |
| Elliptic localization is free | Its prime side is charged (`Λ(n) cos(γ log n)`) and its archimedean side carries the conductor `log γ` |
| Hecke separation can be combined with elliptic symmetry | A boost and the swap at the same pair generate a hyperbolic group: isotropy again |
| A positive completion of a charged weight keeps the charge | It is a height coupling; its anchors are Fejér-limited |
| Squaring the explicit formula collides all conjugate pairs | The conjugate-pair sums accumulate; no meromorphic carrier exists |
| A two-variable lattice count is a surface count | Lattice counts on the square of `Spec ℤ` collapse to the diagonal or factor; their positivity is a modulus square |
| Existence of a positive trace is the issue | The Hecke algebra has many positive traces; the question is whether Weil's trace is one |
| A polarization is an extra choice | Weil's trace is determined by the explicit formula; what can be chosen is only the mechanism of a proof |

---

## 8. Tools

**From sibling programmes:** polar and scaling surfaces, curve data and fakes, normalized graphs,
determinant and Rosati degrees, the local form and its boosts, the Hecke symbol and its resonance
law, the transform `mellinAt`, completed positive and height-coupled systems with the real-anchor
law, zero configurations and Weil's form, modulated tests, window certificates.

**Built here:**

- the polarization calculus of `*`-algebras with positive traces;
- the local sign principle and the classification of invariant fibres;
- the reflection-commuting affine group, its stabilizers and the point reflections;
- twisted tests, twisted configurations and the twist identity of Weil's form;
- the sector calculus of real pairs (even positive, odd negative);
- the charged prime side, the shifted poles and the conductor of a twist;
- the twisted symmetric Hecke algebra and the dihedral dilemma;
- positive completions of charged weights and the Fejér barrier for coupled contraction;
- exterior divisors, conjugate collision and the non-meromorphy of global collision;
- theta counts of sublattices of the square and their Mellin transforms.

---

## 9. Open research topics

1. **A positivity on the odd twisted sector that is neither invariant nor non-localizing.** The
   forcing half of elliptic localization at height `γ`; at bounded aperture it is source-blind, at
   aperture `≍ log γ` it is RH at height `γ`. What intermediate statement is true?
2. **A conductor-free collision.** A two-variable structure colliding conjugate zeros at every
   ordinate at once; its one-variable restrictions are twists, which pay `log γ`.
3. **A count with a quadratic Riemann–Roch.** A section count on normalized graphs whose rank grows
   with the class; lattice counts on the square are excluded.
4. **The separating aperture of each twin.** The least aperture at which certified positivity of
   `ζ` fails for a gauge twin, starting with the flip of `Λ(2)`.
5. **Rigidity of coupled classes** at zero-free ordinates.
6. **Oscillatory capacity uniform in the depth.**

---

## 10. Success criteria and contribution standard

APol succeeds when it produces a positivity theorem of a type the corpus does not contain — a
polarization, an elliptic localizer with a forcing half, a charged positivity, a collision law, a
rigidity law — or a sharp no-go naming the missing input, with its positive survivor.

| Criterion | Test |
|---|---|
| Selectivity | distinguishes `ζ` from the battery: `CompletedPositiveSystem 2 1` pairs and quartets and their height-coupled lifts, pole-order-3 and strip-pole quartets, over-regular Beurling systems, the Siegel family, twisted boundary systems, the golden datum and the complex fake, `Γ_ℝ^d` solutions, signed self-dual combinations, dominated and flipped twins |
| Gauge charge | separates the gauge point `0` from its twins; fails on the Liouville twin |
| Localization | isolates a reflection pair and states the length of its localizing operation |
| Local type | its positivity is not a consequence of invariance under a symmetry hyperbolic at off-line pairs |
| Reflection pairing | pairs `ρ` with `1 − ρ̄`, sees complex quartets |
| Two variables | collides conjugate zeros at every ordinate at a cost independent of the ordinate |
| Counting origin | positivity is a dimension or a cardinality, with Riemann–Roch proved without the sign |
| Calibration | Weil for curves; exterior-count purity; Fejér barrier; the `κ = 1` collapse; the height-coupled budget as the classical local count |

A contribution must:

1. be an unconditional Lean theorem about an object of §3;
2. name its mechanism (invariant, counting, elliptic, charged) and the layer of Weil's argument it
   concerns;
3. state the local type of its operations at off-line pairs, and on which sector it forces;
4. state its gauge charge and its conductor;
5. say what it gives on the golden datum, the complex fake, curves and the battery;
6. keep identities apart from signs;
7. record the positive survivor of every no-go.

Principles: positivity forces only through indefinite fibres; elliptic means definite, not
positive; localization in height is a twist and costs a conductor; a completion is a coupling;
counting on the square is determinantal; identities first, sign last; a reformulation is not a
reduction.
