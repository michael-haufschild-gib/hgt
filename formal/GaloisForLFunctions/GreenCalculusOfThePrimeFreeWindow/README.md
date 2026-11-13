# Green Calculus of the Prime-Free Window (GCW)

Namespace `GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow`; umbrella
`GreenCalculusOfThePrimeFreeWindow.lean`.

**First draft.** Statements marked *corpus* are Lean theorems of the programmes named (MAFT =
MixingArithmeticOfTheFloorTrees, AGZ = AbsoluteGeometryOfSpecZ). Statements marked *target* are
what this programme sets out to prove; they are not theorems yet.

## 1. Motivation

At finite scale the Riemann hypothesis is one statement per window: the neutral part `N_W` of
Weil's form on the step packets of `W = (R, R + J]`, `R ≤ J`, has exactly one negative square
(AGZ, *corpus*). The overlap law (MAFT, *corpus*) turns this into a recursion. Write
`W = (R, 2D + b]`, `D = R + a`, as a left end `(R, D]`, the **dyadic middle** `(D, 2D]` and a right
end `(2D, 2D + b]`. Then `W` holds one bound state iff its two parts `(R, 2D]`, `(D, 2D + b]` do
and the coupling of the two ends *after the middle is eliminated* is a contraction between their
conditional energies. Ratio `ρ` goes to `ρ²/2` in one step, and RH is this contraction at every
step.

Everything in the step is mediated by one object: the inverse of the neutral part of the dyadic
middle. Two facts make it the right object to study by itself.

* **It is prime-free and universal.** Between two blocks of `(D, 2D]` no floor map `b ↦ ⌊b/k⌋`,
  `k ≥ 2`, acts. The middle is the archimedean matrix at block size `D` (a logarithmic potential
  and the jets), the same for every window that contains it and for every `Q`.
* **The primes enter a step only as boundary maps.** For ratio at most three the only contact is
  that of the prime `2`; it sends the left end into the top sliver of the middle and the bottom
  sliver of the middle into the right end. The ends are joined by the prime `2` only through the
  inverse of the middle between its two slivers.

No declaration of the corpus bounds that inverse, the conditional energies or the conditional
coupling. The certified floors of the short windows do not give the first step: they would need a
coupling of norm `≤ 1/5000` against a direct coupling of norm `≈ 0.03`. What is missing at the
open core of the finite-scale picture is therefore not a field but a calculus: potential theory
on one universal family of matrices, with the arithmetic as boundary data.

## 2. Objects

| Object | Notation | Meaning |
|---|---|---|
| Prime-free kernel | `N⁰(x, y) = δ_{xy} ϱ(x) − J(x, y)` | density `ϱ(x) = ΔF(x) − γ − log 2π`, jets `J(x, y) = ½(Δ²F(x + y + 1) + Δ²F(|x − y|))`, `F(n) = n log n` |
| Dyadic middle | `M_D` | `N⁰` on the blocks `D, …, 2D − 1`; equals `neutralWindow Q D D` for every `Q` |
| Potential, Dirichlet form | `V_D`, `𝓔_D` | `V_D(x) = Σ_y M_D(x, y)`; `𝓔_D(f) = ½ Σ J(x, y)(f_x − f_y)²`; `M_D = V_D + 𝓔_D` |
| Green matrix | `G_D = M_D⁻¹` | exists at every block size (MAFT, *corpus*) |
| Binding energy, ground vector | `μ_D`, `φ_D` | `M_D φ_D = −μ_D φ_D`, `φ_D > 0`, `‖φ_D‖ = 1` |
| Positive part | `G₊ = G_D + φ_D φ_Dᵀ/μ_D` | the Green matrix of the middle on the orthogonal complement of its bound state |
| Ends, couplings | `N₁`, `N₂`, `K`, `P₁`, `P₂` | neutral parts of the two ends, their direct coupling, their couplings to the middle |
| Jet and contact maps | `P_i = −𝒥_i − 𝒞_i` | `𝒥_i` the jets between an end and the middle, `𝒞_i` the contact of `2` |
| Slivers | `T = (2R, 2D]`, `B = (D, D + ⌈b/2⌉]` | the image of the left end under `x ↦ 2x, 2x + 1`; the image of the right end under `x ↦ ⌊x/2⌋` |
| Sliver blocks | `G_D[T, T]`, `G_D[T, B]`, `G_D[B, B]` | the blocks of the Green matrix the contact maps read |
| Conditional energies, coupling | `S₁`, `S₃`, `X` | `S_i = N_i − P_iᵀ G_D P_i`, `X = K − P₁ᵀ G_D P₂` (`overlapLeftEnergy`, `overlapRightEnergy`, `overlapCoupling`, MAFT) |
| Dirichlet-to-Neumann form | `Λ_D(P) = Pᵀ G_D P` | the response of the middle to boundary data `P` |
| Level | `C ≥ 0` | every object above with `N + C` in place of `N`: `G_D(C) = (M_D + C)⁻¹`, `S(C)`, `X(C)` |
| Excess of a step | `e_C(W)` | the negative part of the least eigenvalue of the Schur complement of `M_D + C` in `N_W + C` |
| Contact weight | `w` | the pencil `N_W(w) = N⁰_W − w · (contact of 2)`; `w = 1` is `ζ`, `w = −1` its sign twin, `w = 0` the prime-free window |
| Tower | `ι_m` | the isometric refinement of packets from block size `D` to `mD` (AGZ `refineStep`) |

## 3. Language

- A **bound state** is a negative square of a neutral part; the **margin** of a window is minus
  its second eigenvalue, so that one bound state is margin `≤ 0`.
- The **bound-state channel** of the middle is `−φ_D φ_Dᵀ/μ_D`; the **positive channel** is `G₊`.
  Through the first the ends repel, `+(P_iᵀφ_D)(P_jᵀφ_D)ᵀ/μ_D`; through the second they attract.
- The **Dirichlet-to-Neumann form** of the middle is the Schur complement seen from outside. Windows
  compose by composing these forms: the form of a longer window is the form of the middle
  corrected by the ends.
- A **step** is one application of the overlap law. Its **Green form** is
  `P G₊ Pᵀ ⪯ N_e + (Pᵀφ_D)(Pᵀφ_D)ᵀ/μ_D` on the two ends.
- The **sign twin** is the window with the contact of `2` reversed (Liouville twist). The middle
  does not change; the **mixed terms** `𝒥ᵀ G_D 𝒞 + 𝒞ᵀ G_D 𝒥` change sign; the **pure terms**
  `𝒥ᵀ G_D 𝒥`, `𝒞ᵀ G_D 𝒞` do not.
- A statement is **uniform** if it holds at every block size `D` with constants independent of
  `D`, and **monotone along the tower** if it passes from `D` to `mD`.

## 4. Mechanisms

*Each item is a target unless marked corpus.*

1. **The middle is archimedean.** `neutralWindow Q D D` does not depend on `Q`; it is
   `V_D + 𝓔_D` with a closed-form potential that is negative in the bulk and grows like
   `½ log(1/distance)` at the two ends.
2. **Two channels.** `G_D = −φ_Dφ_Dᵀ/μ_D + G₊` with `G₊ ⪰ 0`, `G₊ φ_D = 0`. The Schur complement of
   the middle is `N_e + (Pᵀφ_D)(Pᵀφ_D)ᵀ/μ_D − Pᵀ G₊ P`, and RH is `Pᵀ G₊ P ⪯ N_e +
   (Pᵀφ_D)(Pᵀφ_D)ᵀ/μ_D` on every window `(R, 2(R + a) + b]`, `R ≥ 34`.
3. **Binding of the middle.** `μ_D` lies between two absolute constants: the flat packet gives
   `μ_D ≥ −N⁰(1, 1) > 1`, the potential gives the upper bound. `μ_D` increases along the tower.
4. **Additive loss.** Below the binding energy of the middle the Schur complement increases at
   rate at least one in the level. A step whose parts have margin `≤ C` gives a whole of margin
   `≤ C + e_C`, and `e_C ≤ ‖X(C)‖`. Margins bounded on all windows are RH (MAFT, *corpus*), so a
   recursion that loses a summable amount below `inf_D μ_D` proves RH.
5. **The primes are boundary maps.** For ratio at most three `N_W = N⁰_W − (log 2 / 2)(A₂ + A₂ᵀ)`,
   `A₂` the graph of `b ↦ ⌊b/2⌋`; on the stars `{c, 2c, 2c + 1}` this is `−c₂‖s‖² + c₂‖t‖²`,
   `c₂ = log 2/√2`. The Schur complement is a quadratic pencil in the contact weight,
   `S(w) = S(0) − w Ξ − w² Π`, with `Π = 𝒞ᵀ G_D 𝒞` the sliver blocks of the Green matrix and `Ξ`
   the mixed terms.
6. **Selectivity lives in the mixed terms.** `S(1) − S(−1) = −2Ξ`: a proof of a step that does not
   use the sign of `Ξ` proves the same step for the sign twin, which is false at ratio three
   (AGZ, *corpus*).
7. **Uniformity through the tower.** Inversion is antitone among symmetric matrices with the same
   number of negative squares. Hence the Green form increases under refinement,
   `G_D ⪯ ι_mᵀ G_{mD} ι_m`: an upper bound at infinite block size is an upper bound at every
   block size.
8. **Cooperativity.** `M_D` has negative entries off the diagonal. Its Green matrix is not
   entrywise of one sign, but `G_D φ_D = −φ_D/μ_D` and `G_D V_D = 𝟙`: against the ground vector
   every row is negative, against the potential every row sums to one.

## 5. Questions

| # | Question | Status |
|---|---|---|
| 1 | Two-sided bounds for the sliver blocks of `G_D`, uniform in `D` | open |
| 2 | A lower bound for `μ_D` uniform in `D` | target: `μ_D ≥ −N⁰(1, 1)`, with an upper bound and monotonicity along the tower |
| 3 | The first step: `Pᵀ G₊ P ⪯ N_e + (Pᵀφ_D)(Pᵀφ_D)ᵀ/μ_D` for `a ≤ 3R/100`, `b ≤ 3(R + a)/50` | open; the Green form itself is a target |
| 4 | The excess of step `k` as a function of the ratio | open; the loss law that makes the excess the object is a target |
| 5 | The Green kernel of the prime-free form on `[0, log 2]` in closed form | open |

## 6. Tools

**From the corpus.** Haynsworth additivity for real symmetric blocks
(`hermNegIndex_fromBlocks_transpose`); the overlap law
(`hermNegIndex_neutralWindow_overlap_eq_one_iff`); invertibility and index one of the dyadic
middle (`isUnit_neutralWindow_dyadic`, `hermNegIndex_neutralWindow_dyadic`); negativity of the
entries off the diagonal (`neutralBlock_neg_of_lt`) and the positive ground vector
(`exists_pos_eigenvector`); the certified floor on charge-free packets
(`sum_neutralBlock_ge_of_short`); invariance of the neutral part under refinement
(`sum_neutralBlock_refine`); margins bounded below are RH
(`riemannHypothesis_iff_neutralWindow_margin_bddBelow`).

**To build.**
- The prime-free matrix with its potential in closed form.
- The Green matrix with its two channels; the Green form of the overlap law.
- The level calculus: shifted Schur complements, the excess, the additive loss law.
- Inversion at equal index; monotonicity of the Green form along the tower.
- The contact pencil: sliver blocks, mixed terms, the sign twin.
- Uniform norms of the boundary maps (jets between adjacent windows; the contact of `2`).
- Bounds for the sliver blocks.

## 7. Traps

| Trap | Truth |
|---|---|
| The certified floors give the first step | They give `S_i ⪰ 1/5000` and would need `‖X‖ ≤ 1/5000`; the direct coupling alone is `≈ 0.03` |
| The middle sees the primes | No floor map acts inside a dyadic window; the middle is the same for every `Q` and every window |
| A bound for `G₊` in operator norm suffices | The only uniform norm bound known is `5000`; the step needs the sliver blocks |
| The Green matrix of a cooperative matrix has one sign | With one bound state it is `−φφᵀ/μ` plus a positive part; the diagonal is positive at large block size |
| The sizes of the contacts decide a step | The pure terms are the same for `ζ` and its sign twin; the mixed terms decide |
| A model of the middle of bounded rank suffices | Rank-`r` models of the gluing fail (AGZ, *corpus*) |
| A proof of the sign at each step is the goal | Without the excess per step there is no loss law, and the recursion is an identity |
| The loss may be multiplicative | A loss that squares per step reproduces the trivial exponent `½`; only an additive loss below `inf_D μ_D` iterates |

## 8. Context

| Neighbour | Interface |
|---|---|
| MixingArithmeticOfTheFloorTrees | the overlap law, Doob chains, margins and exponent laws; GCW studies the mediator of its step |
| AbsoluteGeometryOfSpecZ | block matrix, neutral part, tower, certified windows, rank law, weakened and twisted contacts |
| HTGeometry, HeckeKreinToeplitz | Hermitian inertia, Haynsworth additivity, index comparison lemmas |
| SelectivePositivityAndThresholdLaws, ArithmeticIncidencePositivity | the certificate at aperture `181/500` and the selective refutation of the sign twin |

In the finite-scale picture of the corpus the route is: certificate at one aperture → transfer to
every block size → overlap recursion → margin and exponent receivers. GCW is the analysis of the
one inequality the recursion asks for at each step.

## 9. Success criteria

The programme is developed when
- the Green matrix of the dyadic middle is a Lean object with its two channels, and the overlap
  law is stated in Green form;
- `μ_D` is bounded on both sides uniformly in `D`;
- the additive loss law is a theorem and RH is reduced to a bound for the excess per step;
- the contact pencil separates `ζ` from its sign twin by a theorem;
- the sliver blocks of `G_D` are bounded on both sides uniformly in `D`, or it is proved which
  further input such a bound needs;
- the first step is proved with a stated excess, or the obstruction to it is a theorem.

## 10. What a contribution must be

- **C1** Uniform in the block size, or monotone along the tower.
- **C2** It reproves the certified range without the certificate, or bounds its own loss there.
- **C3** It fails for the sign twin and for contact weights in `[−5/2, 19/40]`, or it concerns the
  middle alone.
- **C4** It uses the full rank of the middle.
- **C5** It produces an excess per step, not only a sign.
- **C6** No statement about a finite list of windows; no optimization of a constant that changes no
  conclusion.
