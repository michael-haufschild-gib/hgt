# Cyclic law action, Euler--Lagrange, and higher Noether law

- **ID:** `nhg-cyclic-action-noether`
- **Stage:** 2 — fully proven on paper
- **Status:** `[PAPER-PROVED] [LEAN FORMALIZED — DOCUMENTED IN PLACE] [LEAF CHECK CLEAN]`
  `[UNIVERSAL FIELD THEOREM] [FORMAL VARIATIONAL SECTOR] [NO COERCIVITY CLAIM]`
  `[NO ROUTE INPUT] [NOT RH]`

## 1. Setup

Let `k` be a characteristic-zero field. Let `(L,{ell_n})` be a complete separated filtered
uncurved `L_infinity` algebra, with brackets compatible with the filtration. Let

\[
 \langle-,-\rangle:L\otimes L\longrightarrow k[-3]
\tag{CA.1}
\]

be a continuous nondegenerate graded-symmetric cyclic pairing of degree `-3`, so degree-one fields
and degree-two equations pair to degree-zero scalars. Cyclic means that

\[
 \langle x_0,\ell_n(x_1,\ldots,x_n)\rangle
\tag{CA.2}
\]

is graded cyclic in all `n+1` inputs. Let `alpha in F^1L^1`, so every series below converges in the
filtration. Define

\[
 \operatorname{MC}(\alpha)=
 \sum_{n\geq1}{1\over n!}\ell_n(\alpha^{\otimes n})
\tag{CA.3}
\]

and the formal homotopy Chern--Simons functional

\[
 \mathcal S(\alpha)=
 \sum_{n\geq1}{1\over(n+1)!}
 \langle\alpha,\ell_n(\alpha^{\otimes n})\rangle.
\tag{CA.4}
\]

All signs below use the standard shifted `L_infinity` convention; `alpha` has the Maurer--Cartan
degree, so the cyclic permutations in the variation have the required common sign.

## 2. Variational theorem

### Theorem 2.1 — Euler--Lagrange equals Maurer--Cartan

For every degree-one compatible variation `eta`,

\[
 \boxed{
 \delta\mathcal S_\alpha(\eta)
 =\langle\eta,\operatorname{MC}(\alpha)\rangle.}
\tag{CA.5}
\]

Since the pairing is nondegenerate,

\[
 \boxed{
 \alpha\text{ is critical for }\mathcal S
 \quad\Longleftrightarrow\quad
 \operatorname{MC}(\alpha)=0.}
\tag{CA.6}
\]

#### Proof

Vary the `n`th summand of `(CA.4)`. There are `n+1` contributions: one from the displayed first
argument and `n` from the inputs of `ell_n`. Cyclicity moves `eta` in each contribution to the first
slot, with the same shifted sign. Thus the factor `n+1` cancels `(n+1)!` and yields

\[
 {1\over n!}\langle\eta,\ell_n(\alpha^{\otimes n})\rangle.
\]

Summing gives `(CA.5)`. Nondegeneracy gives `(CA.6)`. QED.

## 3. Twisted differential and Hessian

Define the twisted unary operation

\[
 \ell_1^\alpha(x)=
 \sum_{n\geq0}{1\over n!}
 \ell_{n+1}(\alpha^{\otimes n},x).
\tag{CA.7}
\]

### Theorem 3.1 — sourced Hessian

At a Maurer--Cartan point `alpha`,

\[
 \boxed{
 \operatorname{Hess}_\alpha\mathcal S(\eta,\xi)
 =\langle\eta,\ell_1^\alpha\xi\rangle,}
\tag{CA.8}
\]

and

\[
 (\ell_1^\alpha)^2=0.
\tag{CA.9}
\]

Thus the linearized field equation, deformation complex, and quadratic action are the same sourced
object.

#### Proof

Differentiate `(CA.5)` in direction `xi`; differentiating `(CA.3)` gives `(CA.7)`, proving
`(CA.8)`. Twisting an `L_infinity` algebra by a Maurer--Cartan element preserves the
`L_infinity` identities, whose unary identity is `(CA.9)`. QED.

## 4. Higher Noether identity

For arbitrary `alpha`, the `L_infinity` identities imply the off-shell Bianchi identity

\[
 \boxed{
 \ell_1^\alpha\bigl(\operatorname{MC}(\alpha)\bigr)=0.}
\tag{CA.10}
\]

An infinitesimal gauge parameter `epsilon` acts by

\[
 \delta_\epsilon\alpha=\ell_1^\alpha\epsilon.
\tag{CA.11}
\]

### Theorem 4.1 — infinitesimal gauge invariance

\[
 \boxed{\delta_\epsilon\mathcal S(\alpha)=0.}
\tag{CA.12}
\]

#### Proof

The Bianchi identity `(CA.10)` is the zero-input component of the twisted square-zero
codifferential. By `(CA.5)` and cyclicity of the twisted unary bracket,

\[
 \delta_\epsilon\mathcal S
 =\langle\ell_1^\alpha\epsilon,\operatorname{MC}(\alpha)\rangle
 =\pm\langle\epsilon,
 \ell_1^\alpha\operatorname{MC}(\alpha)\rangle=0.
\]

QED.

## 5. Source and observer covariance

Let `F:L->L'` be a filtration-preserving cyclic `L_infinity` isomorphism. Its Maurer--Cartan map
`F_*` sends solutions to solutions and transports the variational one-form `(CA.5)`. Therefore the
critical formal moduli problem and its sourced Hessian complex are invariant under cyclic formal
gauge.

The numerical action itself is fixed only after normalization; an additive locally constant term is
invisible to `(CA.5)`.

## Lean formalization status

- Module:
  `formal/GaloisForLFunctions/HTGeometry/NomologicalHomotopyGeometry/CyclicActionNoether.lean`
- Umbrella: `GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry`
- Card remains in Stage 2 by explicit instruction; no pipeline move was performed.

The module formalizes uncurved positive-arity multilinear operations, fixed nondegenerate cyclic
pairing, exact algebraic first variation of every homogeneous action term, every finite arity
quotient of the completed action and Maurer--Cartan series, critical-locus equivalence, sourced
Hessian, twisted square-zero differential, off-shell Bianchi identity, higher Noether/gauge
invariance, and covariance of critical loci and Hessians under strict cyclic formal-coordinate
isomorphisms. Infinite formal series are represented by the compatible family of their finite
arity quotients, matching the separated filtered interpretation and making no analytic convergence
or coercivity claim.

Foreground verification:

```text
lake env lean GaloisForLFunctions/HTGeometry/NomologicalHomotopyGeometry/CyclicActionNoether.lean
```

Command exited `0` with zero output. Final umbrella build, axiom print, and repository lint remain
part of the all-card final audit.

## 6. Hostile boundary

1. If the pairing is degenerate, criticality need not imply Maurer--Cartan.
2. Without cyclicity, the `n+1` variation terms do not combine into `(CA.5)`.
3. The formal series gives no positivity, lower bound, convergence in an analytic norm, coercivity,
   or properness.
4. Infinitesimal gauge invariance does not exclude global gauge anomalies.
5. Curved `L_infinity` algebras with `ell_0!=0` require the corresponding curved action formula.
6. The action does not select `alpha`; it makes the independently sourced Maurer--Cartan law
   variational.
7. Equality of Euler--Lagrange loci does not identify two cyclic actions or their global histories.

## 7. Field consequence

Nomological Homotopy Geometry now has one non-arbitrary formal dynamics:

\[
 \boxed{
 \text{cyclic law field}
 \Longrightarrow
 \text{homotopy Chern--Simons action}
 \Longrightarrow
 \text{Maurer--Cartan equation + higher Noether identity}.}
\tag{CA.13}
\]

The remaining physical/mathematical problem is analytic: determine when a real form, polarization,
boundary condition, and completion make this formal action coercive or proper on observer fibres.
