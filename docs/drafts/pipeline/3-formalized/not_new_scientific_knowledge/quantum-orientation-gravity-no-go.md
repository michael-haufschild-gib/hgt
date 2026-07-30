# Probabilities do not choose time orientation, and orientation alone cannot be gravity

- **ID:** `quantum-orientation-gravity-no-go`
- **Stage:** 3-formalized
- **Type:** EXACT ALGEBRAIC THEOREM / OPERATOR-ALGEBRA LITERATURE BRIDGE / NO-GO
- **Status:** `[PAPER-PROVED ALGEBRAIC CORE] [UNCONDITIONAL LEAN]`
  `[LITERATURE CLASSIFICATION] [NOT NEW MATHEMATICS]`
- **Lean target:** `formal/GaloisForLFunctions/HTGeometry/QuantumOrientationFracture.lean`

## Question

Could the missing sign of quantum multiplication itself vary from event to event and be
gravitational curvature?

The answer is no for a fixed factor. The failure is useful: it identifies what the next theory
must add.

## Algebraic orientation fracture

Let \(m:A\times A\to A\) be any product on an additive group and define its reverse
\[
m^{\mathrm{op}}(x,y)=m(y,x).
\]
Write its symmetric and antisymmetric parts without normalization as
\[
S_m(x,y)=m(x,y)+m(y,x),\qquad
L_m(x,y)=m(x,y)-m(y,x).
\]
Then, identically,
\[
\boxed{
S_{m^{\mathrm{op}}}=S_m,\qquad
L_{m^{\mathrm{op}}}=-L_m,\qquad
m^{\mathrm{op}}(x,x)=m(x,x).
}
\]
If \(m\) is associative, then \(m^{\mathrm{op}}\) is associative.

Proof is direct:
\[
\begin{aligned}
S_{m^{\mathrm{op}}}(x,y)
  &=m(y,x)+m(x,y)=S_m(x,y),\\
L_{m^{\mathrm{op}}}(x,y)
  &=m(y,x)-m(x,y)=-L_m(x,y).
\end{aligned}
\]
For associativity,
\[
m^{\mathrm{op}}\!\left(m^{\mathrm{op}}(x,y),z\right)
=m\!\left(z,m(y,x)\right)
=m\!\left(m(z,y),x\right)
=m^{\mathrm{op}}\!\left(x,m^{\mathrm{op}}(y,z)\right).
\]

For a \(C^*\)-algebra this says that the algebra and its opposite have the same squares, positive
cone, norm, state space, spectral probability laws, and Jordan product, while their commutators
and dynamical correspondences have opposite sign. Probability kinematics therefore does not
select the order of composition.

## Fixed-factor orientation is discrete

Alfsen and Shultz prove that global orientations of the normal state space of a von Neumann
algebra, Jordan-compatible von Neumann products, and central symmetries are in bijection relative
to a supplied reference product. For a factor the only central symmetries are \(+1\) and \(-1\).
Hence a factor has only two orientations: its product and the opposite product.

Now let \(X\) be a connected topological space and let
\[
o:X\longrightarrow\{+,-\}
\]
be a continuous factor-orientation field. Since the codomain is discrete, the continuous image of
connected \(X\) is connected and therefore a singleton. Thus
\[
\boxed{o\text{ is constant on }X.}
\]

Consequently a smooth factor-orientation field has no local continuous degrees of freedom. It can
carry a global reversal, discrete holonomy, or domain-wall data, but it cannot by itself encode a
generic Riemann tensor or the continuously varying metric of general relativity.

## No-go verdict

`[ROUTE KILLED]`

> Gravity is not curvature of the bare \(A\) versus \(A^{\mathrm{op}}\) sign.

The phrase “time orientation is missing from probabilities” is established operator-algebra
theory. Promoting its two-valued sign directly to a gravitational field fails by connectedness.

## Strongest positive survivor

The obstruction exposes a more precise common structure.

1. Counterfactual probability data determine a Jordan possibility algebra but not the
   antisymmetric product that makes actual sequences dynamical.
2. An actual event must therefore supply more than a state or orientation sign: it must supply a
   **relative compositional lift** between its source and its generated successor.
3. Continuous gravity can only live in the soldering and comparison of changing possibility
   algebras, targets, supports, and dynamical correspondences. After quotient by local
   automorphisms, a bare two-valued orientation has no infinitesimal curvature left.
4. The absolute sign may be gauge; relative transport and its failure to glue may still be
   physical. That requires a source-generated transport law, not a field of signs on a supplied
   spacetime.

This points from
`../../1-in-progress/source-generated-left-unit-law.md` to the stronger
`../../1-in-progress/dynamical-composition-universal-law.md`.

## Relation to corpus

- The Riemann orientation-boundary fracture proves that complete scalar differential data can
  forget oriented charge while a source-marked boundary retains it.
- The Schwarzschild time-orientation split proves that the antisymmetric dressed-log sector can be
  differentially algebraic while the common symmetric memory is Hypertranscendental. Orientation
  sign and global complexity are independent.
- The hypersurface-deformation algebra places the spatial metric in the antisymmetric bracket of
  local time deformations, but that bracket already acts on a supplied phase space.
- Event partial-isometry composition fails exactly at a noncommuting support interface, but the
  support projections and \(C^*\)-algebra are already supplied.

Together these say that orientation must be retained, but orientation alone is not the missing
physics. The source generation of composition is.

## Novelty boundary

All mathematical ingredients are prior:

- E. M. Alfsen and F. W. Shultz,
  [*Orientation in operator algebras*](https://pmc.ncbi.nlm.nih.gov/articles/PMC22571/);
- M. Frembs,
  [*Bipartite entanglement and the arrow of time*](https://arxiv.org/abs/2207.00024);
- M. Frembs and E. G. Cavalcanti,
  [*Variations on the Choi--Jamiołkowski isomorphism*](https://arxiv.org/abs/2211.16533).

The no-go receives no novelty credit. Its role is to prevent the research programme from calling
a discrete orientation torsor “gravity.”

## Formal boundary

Lean proves unconditionally:

- reverse multiplication preserves squares;
- reverse multiplication preserves the symmetric/Jordan part;
- reverse multiplication negates the antisymmetric/Lie part;
- reverse multiplication preserves associativity; and
- every continuous map from a preconnected space to `Bool` is constant.

Lean does not encode the Alfsen--Shultz classification or identify a physical factor, spacetime, or
gravitational field.

## Formal certificate

Verified 2026-07-30 with the repository toolchain:

- `lake env lean GaloisForLFunctions/HTGeometry/QuantumOrientationFracture.lean`: pass;
- `lake build GaloisForLFunctions.HTGeometry.QuantumOrientationFracture`: pass
  (`903/903` jobs);
- `#print axioms`: `reverseProduct_square` and `isAssociativeProduct_reverse` use no axioms;
  the additive equalities use only `propext`; the connectedness theorem uses only `propext`,
  `Classical.choice`, and `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration occurs in the module.

The repository-wide `scripts/formal_tools.py lint` audit remains red because the pre-existing dirty
tree contains unrelated unreachable modules in `RHTower` and `HTGeometry`. It did not report this
module as unreachable or report a forbidden declaration in it. This baseline repository failure is
not silently promoted to a clean global lint certificate.

## Gates

- [x] algebraic proof dependency-closed
- [x] fixed-factor classification sourced to primary literature
- [x] strongest positive survivor extracted
- [x] unconditional Lean formalization and direct file check
- [x] terminal axiom and leaf-build audit
- [ ] repository-wide lint clean (blocked by unrelated pre-existing unreachable modules)
- [ ] successor source-generated composition law remains open
