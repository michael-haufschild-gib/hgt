# The Tensor-Power Programme Ω (TPP)

Namespace `GaloisForLFunctions.TensorPowerProgramme`; umbrella `TensorPowerProgramme.lean`; 3 modules.
Specification: §2.22 of [the review-1511 obstacles summary](../../../docs/reports/review-1511/obstacles-summary.md).

*Deligne's tensor-power argument, carried to `Spec ℤ`: what it needs, where it breaks, and which
object would make it run.*

## 1. Motivation

Deligne's proof of the Riemann hypothesis over finite fields is the only argument of its shape that
has proved an RH. For a sheaf `F` on a curve `U` over `𝔽_q` with real traces, a polarization of
weight `w` and large monodromy it has four steps:

1. **Pointwise data.** At every closed point `x` the Frobenius has eigenvalues `α_{x,i}`.
2. **Free positivity.** The traces of `F^{⊗2k}` are `t_x^{2k} ≥ 0`, so the Euler product of
   `F^{⊗2k}` has nonnegative coefficients and converges up to its first real singularity.
3. **A pole law uniform in `k`.** The `L`-function of `F^{⊗2k}` is rational, its poles come only
   from `H²_c`, the coinvariants of the geometric monodromy; with large monodromy these are spanned
   by products of the polarization, of weight exactly `kw + 2`. The first pole sits at a place fixed
   in advance, whatever the eigenvalues are.
4. **The limit.** One Euler factor is dominated by the whole product, so `|α_x|^{2k} ≤ q_x^{kw+1}`
   for every `k`, and `k → ∞` gives `|α_x| ≤ q_x^{w/2}`.

The corpus already owns the receiver, the bookkeeping and several pieces. RH is equivalent to a
bound of the prime-trace moments `Σ_{p≤N} log p (2 Re S(log p))^{2k} = O(N^{1+A})` with `A`
independent of `k` (`SurfaceOfSpecZ.riemannHypothesis_iff_moments_primeTraces`): positivity is
free and the uniformity is RH. Frames, towers, levers and walls are a proved calculus
(FamilyContinuationTheory, ExponentDynamicsOfTheCriticalStrip). Products of the spectrum alone are
depth-homogeneous and gain nothing (ArithmeticKunnethTheory, layer 1). A family sees its members of
positive mass through the moments of its full traces (InfiniteRankPurityTheory).

What the corpus does not have is step 3 over `ℤ`: a base whose tensor powers have a pole law
fixed in advance, and in which the zeros of `ζ` are local parameters. TPP is the programme of that
step. It asks what the pole law is made of, proves where it is missing, prices every substitute
the corpus has (the frames of the cubic probe, the Möbius sign, the completions), and writes the
missing object as a list of axioms. Under the working prior of the report — no shortcut, every
question at its least favourable answer — each stage still ends in a theorem: a calibration, a
price law, a ruler no-go, a pencil or the axiom list of the object RH needs, a completion or a cost
theorem, a transport or an intrinsic floor.

## 2. The argument in the frame calculus

A **frame** `(c, k)` transports a zero of real part `β` to a zero of a correction at `kβ − c`.
With a top bound `b` for the correction (its Euler product converges and does not vanish on
`Re > b`) it gives the one-step bound `β ≤ (c + b)/k`; a coupled tower of frames gives the centre
`c/(k − 1)`, and every bound is `max(σ₀, centre)` with `σ₀` the estimate floor
(`FamilyContinuationTheory.abscissa_le_max_fixedPoint_of_tower`).

The `k`-th tensor power of a datum moves an eigenvalue of depth `δ` to depth `kδ`, i.e. a zero
at `β` to `kβ − (k − 1)/2`. It is the frame `((k − 1)/2, k)`: with the top bound `1` it gives
`½ + 1/(2k)`, its tower centre is `½`. Three lines of frames organize the programme:

| Line | Price `c` at period `k` | One step (`b = 1`) | Tower centre | Source |
|---|---|---|---|---|
| Deligne | `(k − 1)/2` | `½ + 1/(2k)` | `½` | tensor powers with a pole law |
| Sign | `k/2` | `½ + 1/k` | `k/(2(k − 1)) → ½` | short Möbius-signed Gauss monomials, priced by Stickelberger |
| Completion | `2k/3 − 1` | `2/3` | `2/3 − 1/(3(k − 1)) → 2/3` | Gauss pairings completed factor by factor |

The sign line lies exactly half a unit above the Deligne line: the Möbius sign costs `½` at some
place (`ExponentDynamicsOfTheCriticalStrip.Stickelberger.half_lt_stickelbergerPrice_div`), and the
cost disappears in the limit. The completion line meets the sign line at `k = 6`, the frame
`(3, 6)` of the cubic probe and the wall `3/5` of every tower of Gauss pairings
(`three_fifths_le_towerValue_pairings`). Beyond `k = 6` completion, not the sign, is the
obstruction of the producer.

## 3. Objects

| Object | Meaning |
|---|---|
| Euler datum over a base | points `x` with norms `N(x) > 1`; at each point local parameters `α_{x,i}`, closed under conjugation, so the level traces `t_x(n) = Σ_i α_{x,i}^n` are real |
| Depth, width | `δ(α) = log‖α‖ / log N(x) − w/2` for weight `w`; the width `W` is the supremum of the depths |
| Tensor-power moments | `D_{2k}(s) = Σ_x Σ_n log N(x) · t_x(n)^{2k} · N(x)^{−ns}`, nonnegative coefficients; the moment exponent `a_k` is its abscissa |
| Pole law | `a_k ≤ 2k·(w/2) + A` for all `k` with `A` independent of `k`: the content of step 3 |
| Edge | the part of the `2k`-th tensor power that fixes `a_k`: tuples of parameters whose product survives the averaging over the base |
| Polarization pair | `α` and `N(x)^w/α` (functional equation); their tensor has the known size `N(x)^w` |
| Conjugation pair | `α` and `ᾱ`; their tensor has the unknown size `‖α‖²`. Purity is the coincidence of the two pairings |
| Flow datum | Frobenius at `x` is `N(x)^D` for one operator `D`: the motive of the zeros `⊕ ℤ(−ρ)` over `Spec ℤ`. Its geometric monodromy is trivial |
| Flow datum (Lean) | `flowTrace z b n = Σ_i b_i n^{z_i}`, moments `flowMomentTerm z b k σ n = Λ(n) |t(n)|^{2k} n^{−σ}` |
| Abelian base | every local system a sum of characters (Dirichlet and Hecke twists, Jacobi-sum characters, the archimedean family); in Lean `IsAbelianBase N λ ev`: norms, von Mangoldt weights, characters with conjugation = inversion, linear independence, and the prime number theorem of each character |
| Twisted datum (Lean) | `twistTrace` `t(x) = Σ_i b_i χ_i(x) N(x)^{z_i}`, moments `twistMomentTerm` |
| Tuples (Lean) | `tupleMode` `Σ z_{a_j}`, `tupleWeight` `Π b_{a_j}`, `tupleChar` `Π χ_{a_j}`; pairs `pairMode` `Z_{a,a'}`, `pairWeight` `B_{a,a'}`, `pairChar` `χ_a χ_{a'}⁻¹`; edge residues `edgeResidue`, `twistEdgeResidue` |
| Adams power (Lean) | `adamsTrace α m n x = Σ_i (α_{x,i}^{mn} + α_{x,i}^{−mn})`: moves modulus `N^δ` to `N^{mδ}`; its Rankin–Selberg square `adamsSquareCoeff`; frequencies `levelFreq` `(n+1) log N(x)`; `AdamsPoleLaw`: every square continues to `Re s > 1` |
| Pencil through `ζ` (N1) | an Euler datum over a base with a pole law, non-abelian monodromy, and the zeros of `ζ` among the local parameters of one point |
| Sign-line completion (N2) | a joint completion of a Möbius-signed monomial of period `k ≥ 7` priced `c = k/2` |
| Exact transport (N3) | zeros of `ζ` forced into a period-`k` family with no estimate floor and constants uniform in `k` |

## 4. Language

- **Ruler**: a criterion that reads the width exactly and produces no bound. **Lever**: a map `T` on
  exponents with `θ ≤ b ⇒ θ ≤ T b`. **Wall**: the fixed point a family of levers cannot pass.
- **Price** of a frame: `c`; the **half unit** is the gap `½` between the sign line and the
  Deligne line.
- **Top bound**: the abscissa right of which a correction has a convergent Euler product and no
  zeros. Tempered members have top bound `1` for free; a dilation has the Deligne frame with top
  `(k + 1)/2` and is a ruler.
- **Arithmetic fibre**: a member of a family with Dirichlet series, Euler product and functional
  equation. **Geometry**: a monodromy acting on the zeros of the members.

## 5. Mechanisms

1. **Free positivity, Rankin domination.** For real traces `t^{2k} ≥ 0`; a nonnegative Euler
   product that converges dominates each of its factors. A pole law turns this into
   `‖α_x‖ ≤ N(x)^{w/2 + A/(2k)}` for every `k` (ArithmeticKunnethTheory `tensor_moment_bound_iff`,
   InfiniteRankPurityTheory `norm_le_of_amortized_levelSums`).
2. **The ruler law.** For every datum `2kW ≤ a_k ≤ 2kW + a₀`, `a₀` the abscissa of the base, so
   `a_k/(2k) → W`. The tensor-power trick is a ruler plus a pole law; the pole law is its whole
   content.
3. **What a pole law is made of.** Over `𝔽_q`: rationality (the trace formula), poles only from
   coinvariants (`H⁰_c = 0` on an affine base), coinvariants of a large monodromy spanned by
   polarization tensors, and the known weight of the polarization. Monodromy alone does not suffice:
   an impure Frobenius has a lift with full `SL₂` image (`goldenFrobenius_has_split_lift`).
4. **Two pairings at the edge.** Under abelian monodromy the conjugation pair `α ⊗ ᾱ` survives the
   averaging, and the edge of every even tensor power carries `‖α‖^{2k}`: the pole law is the
   conclusion. Under symplectic monodromy only polarization pairs survive and the edge has the
   weight fixed by the functional equation. Over `Spec ℤ` the two pairings are `ρ ↦ ρ̄` and
   `ρ ↦ 1 − ρ`; RH is their coincidence (GaloisTheoryOfZeros).
5. **Frames are tensor powers with a price.** A frame `(c, k)` is a `k`-th tensor power whose
   correction is completed at the cost `c`; `c − (k − 1)/2` is what the completion pays above
   the polarization.
6. **Diagnosis over `Spec ℤ`.** The motive of the zeros is a flow datum: all Frobenii are
   simultaneously diagonal, the geometric monodromy is trivial, every tuple of zeros contributes
   to the edge and nothing cancels. The zeros have to vary in a family with monodromy.
7. **Coinvariants are everything, nothing cancels.** For a flow datum the `k`-th tensor moment is
   `Σ_{a,a'} B_{a,a'} (−ζ'/ζ)(σ − Z_{a,a'})` over pairs of `k`-tuples of modes; each tuple carries
   its own shifted pole. At the edge `σ = 1 + 2kW` the surviving pairs are the conjugation pairs
   of top tuples, and the residue is `Σ_w ‖Σ_{Σ z_a = w} Π b_a‖²`, a sum of squares that the
   top mode of largest imaginary part makes positive. On an abelian base the characters only
   split the squares further (`Σ ‖Σ_{(Σ z_a, χ_a) = κ} Π b_a‖²`); positivity is the linear
   independence of characters, and the analytic input is the prime number theorem of each
   character (a pole only for the trivial one, no zero on `Re s = 1`).
8. **Polarization fixes the edge.** For a polarized datum (`α ↔ α⁻¹`) the Rankin–Selberg square of
   the `m`-th Adams power has nonnegative coefficients; if it continues analytically to `Re s > 1`,
   Landau's theorem makes it converge there, and one point of the base gives `|α|^m ≤ N(x)` for
   every `m`: purity. In rank two `p_m² = p_{2m} + 2`: the square is the next Adams power plus the
   two polarization pairs `α^m ⊗ α^{−m}`, of weight `det = 1` whatever `α` is, so the pole law
   reduces to the continuation of the Adams series themselves — the constituents. For
   `GL₂`-automorphic data they are differences of symmetric-power log-derivatives (the classical
   route from functoriality to Ramanujan); for flow data they are the shifted modes.

## 6. Questions

| # | Question | Least favourable answer, and what it teaches |
|---|---|---|
| Q1 (Ω1) | **Calibration.** Write the argument for a model base over `𝔽_q` in the frame calculus. Which inputs does the pole law need; does monodromy enter already over `𝔽_q`? | The pole law needs monodromy and the trace formula: then N1 is unavoidable over `ℤ`. |
| Q2 (Ω2) | **Price ledger.** Sign line and Deligne line differ by the half unit and have the same limit; completion centres increase to `2/3`. | None: arithmetic. The obstruction of the producer is completion, not the sign. |
| Q3 (Ω3) | **Diagnosis over `Spec ℤ`.** The exponents of the prime-trace moments satisfy `2kw ≤ a_k ≤ 1 + 2kw`. | A ruler no-go: `Spec ℤ` with the motive of the zeros is the wrong base. |
| Q4 (Ω4) | **Pencil.** Decide the heat pencil (arithmetic at `τ ≠ 0` or no-go), twist families (monodromy), the Fermat/Kummer family (transport of the zeros into its fibres). | Each splits into geometry without arithmetic or arithmetic without geometry; then the axiom list of N1 is the output, and it is the target of the `𝔽₁` programme. |
| Q5 (Ω5) | **Frame track.** A sign-line completion at period `k ≥ 7`: the Stickelberger price of the `A₂` series coefficients; Jacobi-sum Hecke characters as corrections at `ks − k/2`. | Higher covers cost more than the sign saves: the frame track needs a source outside metaplectic theta functions. |
| Q6 (Ω6) | **Exact transport.** Continuation of the cubic probe to the centre of `(3, 6)` by identities alone. | The dual series has the abscissa of the estimate floor: the floor is intrinsic. |
| Q7 (Ω7) | **Uniformity.** Constants of completion and transport uniform in `k`; the top bound `1` for tempered members. | Conductors of order-`k` families push `σ₀(k)` to `1`. |
| Q8 (Ω8) | **Assembly.** `Θ ≤ max(σ₀(k), (c_k + 1)/k)` for every period; levers covering `(½, 20999/24000]` give RH. | — |
| Q9 | **Refutation.** Does every family of Euler–FE data through `ζ` with moving zeros have finite monodromy on them; does every transport from `ζ` have an intrinsic estimate floor? | Either theorem ends the Deligne shape for `ζ`. |

## 7. Tools

**From the corpus.** Frame and tower calculus with walls and mixed towers
(`pairingStep`, `towerValue`, `wall`); Stickelberger valuations and prices of Gauss sums
(`norm_gaussSum_extremalChar_pow`, `stickelbergerPrice_eq_half_mul`); the prime-trace receiver and
the width law at the primes (`riemannHypothesis_iff_moments_primeTraces`,
`zetaZeroWidth_le_iff_bddBelow_primeDegrees`); amortization over families
(`member_norm_le_of_family_moments`); `SL₂` invariants and the golden countermodel
(ArithmeticKunnethTheory); the heat monodromy and its comparison with the arithmetic group
(GaloisTheoryOfZeros); the cubic probe, its correction and rung (`correctionAbscissa_eq`).

**To build.**
- Euler data over a base with tensor powers, moment exponents and the ruler law (flow data and
  abelian bases done: `IsAbelianBase`, `twistMomentTerm`, the edge residue as a sum of squares).
- The pole law as an axiom with its Rankin step, and a dissection of its inputs over `𝔽_q`.
- An edge calculus: which tuples survive averaging under abelian, symplectic and flow monodromy, and
  at which weight.
- The price ledger of the three lines and the assembly of frames into bounds for `Θ`.
- The axioms of a pencil through `ζ`, with the verdict on each candidate family.

## 8. Traps

| Trap | Truth |
|---|---|
| Positivity of even tensor powers forces purity | Golden data have positive even-tensor Euler coefficients and are impure (ArithmeticKunnethTheory) |
| Large monodromy forces purity | An impure Frobenius has a split lift with full `SL₂` image; the pole law is the input |
| The pole law needs the moments to converge | It needs only analytic continuation: positivity (Landau) converts continuation into convergence |
| Tensor powers of `ζ` amplify the depth | Products of the spectrum are homogeneous: gain equals depth times length |
| A family proves the purity of its members | Only members of positive mass, through moments of the full traces; without a measure, the closed strip |
| The heat pencil is a pencil | Only its fibre at `τ = 0` has a Dirichlet series; arithmetic group and heat monodromy agree on finite windows only |
| Twist families are a base | They are abelian: every even tensor moment has base loss exactly one and its edge is a positive sum of squares over conjugation pairs (`summable_dirichletMomentTerm_iff`) |
| Characters can cancel the edge | Distinct characters are linearly independent; the edge residue is a sum of squares that never vanishes |
| The Möbius sign is the obstruction | The sign line has wall `½`; completion caps the producer at `3/5` |
| A dilation transports zeros at the Deligne price | It has the Deligne frame with top `(k + 1)/2`: a ruler |
| Composing frames lowers the centre | Composite centres are convex combinations of the centres |
| Exact transport is a lever | The cubic correction moves bounds between `ζ` and the rung without loss: a ruler until the rung family has a seed |

## 9. Pillar theorems

| Theorem | Status |
|---|---|
| Flow data have base loss exactly one: `D_k(σ) < ∞ ⇔ σ > 1 + 2kW`; coinvariant expansion into shifted `−ζ'/ζ`; positive edge residue; pole law ⇔ `W ≤ w₀` | `summable_flowMomentTerm_iff`, `ofReal_tsum_flowMomentTerm`, `edgeResidue_pos`, `exists_poleLaw_iff` — proved |
| Abelian bases are rulers: same exact law on every abelian base; Dirichlet twists of any modulus form one | `summable_twistMomentTerm_iff`, `exists_twistPoleLaw_iff`, `isAbelianBase_dirichlet`, `summable_dirichletMomentTerm_iff` — proved |
| Over `Spec ℤ` for `ζ` itself: the prime-trace moments read `w` with an offset in `[0, 1]`; uniformity in `k` is RH | corpus: `riemannHypothesis_iff_moments_primeTraces`, `zetaZeroWidth_le_iff_linear_tensor_loss` |
| Polarized bases: continuation of the Adams squares to `Re s > 1` ⇒ purity; rank two: continuation of the Adams series suffices | `norm_eq_one_of_adamsPoleLaw`, `norm_eq_one_of_adams_continue` — proved |
| Price ledger of the Deligne, sign and completion lines | target |
| Pencil axioms and the verdict on the heat, twist and Kummer candidates | target |
| Sign-line price of Jacobi-sum characters and of the `A₂` coefficients | target |

## 10. Context

| Neighbour | Interface |
|---|---|
| ArithmeticKunnethTheory | closes layer 1 (products of the spectrum); TPP is layer 3, families over a base; uses its `SL₂` invariants and golden countermodels |
| InfiniteRankPurityTheory, InfiniteRankWeilTheory | amortization, fixed parts, self-improvement at infinite rank: the Rankin step at a point |
| SurfaceOfSpecZ | the tensor-power trick over `ℤ` and the width law at the primes |
| FamilyContinuationTheory, ExponentDynamicsOfTheCriticalStrip | frames, towers, walls, Stickelberger prices, the sign line, the cubic probe and its rung |
| GaloisTheoryOfZeros | the two involutions `ρ ↦ ρ̄`, `ρ ↦ 1 − ρ`; heat monodromy and the arithmetic group |
| ZeroConfigurationGeometry | the heat pencil has a Dirichlet series only at `τ = 0`; Ramanujan as reality of an Euler column |
| ArithmeticCastelnuovoSeveri | Kummer calibration curves |
| AbsoluteGeometryOfSpecZ (`𝔽₁`) | receives the axiom list of N1 as its specification |

## 11. Success criteria

The programme is complete when every question of §6 has a Lean answer — the theorem asked for or a
no-go with its strongest positive survivor — and the tools of §7 exist: Euler data over a base with
the ruler law and the Rankin step; the edge calculus; the price ledger and assembly; the pencil
axioms with a verdict on each candidate.

A contribution to TPP

- is unconditional Lean, with no premise that carries the mathematics;
- moves one question of §6, or builds a tool that a later answer uses;
- works with tensor powers, frames, pole laws, edges or pencils — not with products of the spectrum
  alone, which ArithmeticKunnethTheory has closed;
- states no "RH ⇒ X"; reductions "X ⇒ RH" only when `X` is a named object of the programme (a pole
  law, a pencil, a completion, a transport);
- is not a finite computation;
- records, when it is a no-go, the positive statement the obstruction exposes.
