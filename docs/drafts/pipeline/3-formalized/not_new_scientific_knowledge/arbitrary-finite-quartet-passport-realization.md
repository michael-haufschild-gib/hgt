# Arbitrary Finite Quartet-Passport Realization

- **ID:** `arbitrary-finite-quartet-passport-realization`
- **Stage:** 2-fully-proven / needs independent audit
- **Type:** THEOREM (paper) / POSITIVE ARBITRARY-LOCATION REALIZATION
- **Date:** 2026-07-11
- **Scientific status:** `[NOVELTY UNVERIFIED]`.  The theorem strengthens the simultaneous common-line
  construction to arbitrary finite off-critical zero packets with independently prescribed jet depths.
  The proof is complete but uses classical Chinese-remainder interpolation and entire-function tools;
  novelty requires an independent proof audit and a broad literature comparison.
- **Statement:** Every finite symmetry-closed packet of nonreal off-critical strip points, equipped with
  arbitrary finite completed-flux passport depths, is realized by a real-even, exact-order-one,
  aperiodic entire function with a zero-free real axis; every prescribed quartet consists of simple
  zeros whose FE/Schwarz partner germs agree to the assigned depth and disagree as full germs.

## Positive theorem

Fix pairwise symmetry-disjoint points

`rho_j=sigma_j+i gamma_j`, `j=1,...,r`,

where `r>=1`, `0<sigma_j<1/2`, and `gamma_j>0`.  Let `N_j>=0` be arbitrary.  There exists an entire
function `X` such that:

1. `X(1-s)=X(s)` and `X(conj s)=conj(X(s))`;
2. `X` has exact order one and no nonzero period;
3. `X(t)!=0` for all real `t`;
4. every point in

   `{rho_j, 1-rho_j, conj(rho_j), 1-conj(rho_j)}`

   is a simple zero of `X`;
5. the residue-filled negative logarithmic-flux germs at `1-rho_j` and `conj(rho_j)` have identical
   Taylor coefficients through order `N_j`, but are unequal as analytic germs.

The quartet positions and finite depths are prescribed before constructing `X`.  In particular, the
quartets need not lie on one pair of vertical lines and the depths need not be equal.

## Centered coordinates

Put

`z=-i(s-1/2)`, `alpha_j=-i(rho_j-1/2)=gamma_j+i(1/2-sigma_j)`.

Both real and imaginary parts of every `alpha_j` are positive.  The four-point orbit in the `s`-plane
becomes

`W_j={alpha_j,-alpha_j,conj(alpha_j),-conj(alpha_j)}`.

The compared FE and Schwarz partners correspond to

`c_j=-alpha_j`, `d_j=-conj(alpha_j)`.

Their difference is nonzero and purely imaginary.

## Order-one envelope

Choose `a_0>0` different from every `|Re w|`, `w` in the finite packet `W=union_j W_j`, and define

`A(z)=cosh(z-a_0) cosh(z+a_0)`.

Then `A` is real and even, has exact order one, has period `pi i`, and is nonzero at every point of
`W`.  It is also nonzero on the imaginary axis: for real `y`,

`A(iy)=|cosh(a_0+iy)|^2>0`.

## Symmetry-compatible Hermite interpolation

For `w in W_j`, set `K_w=N_j` and choose signs `epsilon_w in {+1,-1}` satisfying

`epsilon_(conj w)=epsilon_w`, `epsilon_(-w)=-epsilon_w`.

At each `w`, prescribe the polynomial jet

`B_0(w+x) = epsilon_w x / A(w+x) mod x^(K_w+2)`.                 (1)

The reciprocal of `A(w+x)` is analytic because `A(w)!=0`, so the right side defines a finite Taylor
class.  The ideals `(z-w)^(K_w+2)` are pairwise comaximal.  The polynomial Chinese remainder theorem
therefore supplies a polynomial satisfying all congruences (1).

The tuple of prescribed classes is invariant under `z -> -z` and under coefficient conjugation:
evenness of `A` and the sign rule give the first compatibility, while reality of `A` gives the second.
Average any CRT solution over these two involutions.  The resulting polynomial `B_0` is real and even
and still satisfies every congruence.  It may be chosen with degree strictly below

`D=sum_(w in W)(K_w+2)=4 sum_j(N_j+2)`.                         (2)

## Positive imaginary-axis repair

Define the real-even quartet polynomials

`Q_j(z)=(z^2-alpha_j^2)(z^2-conj(alpha_j)^2)`

and the flat repair polynomial

`R(z)=prod_j Q_j(z)^(N_j+2)`.

At every `w in W_j`, `R` vanishes to order at least `N_j+2`, so replacing `B_0` by

`B_L=B_0+L R`                                                    (3)

preserves all prescribed jets.  On the imaginary axis,

`Q_j(iy)=|y^2+alpha_j^2|^2>0`,

hence `R(iy)>0`.  Moreover `deg B_0<deg R=D`, so

`B_0(iy)/R(iy) -> 0` as `|y| -> infinity`.

The real continuous quotient is bounded.  Choose a real `L` larger than its absolute supremum.  Then

`B_L(iy)>0` for every real `y`.                                  (4)

This repair is the decisive simultaneous step: it enforces a global zero-free axis without changing
any of the finitely prescribed local passports.

## The realized entire function

Set

`F(z)=A(z)B_L(z)`, `X(s)=F(-i(s-1/2))`.

Both factors of `F` are real and even, so `X` has the functional-equation and Schwarz symmetries.
Equation (1), preserved by (3), gives

`F(w+x)=epsilon_w x+O(x^(N_j+2))` for `w in W_j`.                (5)

Thus every prescribed point is a simple zero.  Writing (5) as

`F(w+x)=epsilon_w x(1+O(x^(N_j+1)))`

gives

`-x F'(w+x)/F(w+x)=-1+O(x^(N_j+1))`.                            (6)

Therefore all residue-filled completed-flux germs in the quartet share the constant Taylor passport
through order `N_j`; in particular the FE/Schwarz partner germs at `c_j,d_j` agree to that depth.

Equation (4) and positivity of `A(iy)` give `F(iy)!=0`, hence `X(t)!=0` for every real `t`.
Multiplication of the exact-order-one function `A` by the nonzero polynomial `B_L` preserves exact order
one, as does the affine change from `F` to `X`.

## Full-germ separation

Suppose the residue-filled flux germs at two distinct partner centers `c_j,d_j` were equal.  Away from
the local origin, cancel `-x` to obtain equality of the logarithmic derivatives of the two translates.
The identity theorem then gives a nonzero constant `C` such that

`F(z+h)=C F(z)`, `h=d_j-c_j!=0`,                                (7)

for every `z`.

The polynomial `B_L` has finitely many zeros, while `A` has the two infinite zero progressions

`+/-a_0 + pi i(k+1/2)`, `k in Z`.

Iterating (7), all but finitely many translates of an `A`-zero must again be `A`-zeros.  Consecutive
large iterates force `Re h=0` and `Im h in pi Z`.  Hence `h` is a period of `A`.  Cancelling `A` in (7)
gives

`B_L(z+h)=C B_L(z)`.

Comparison of leading coefficients gives `C=1`; a nonconstant polynomial has no nonzero period.
Contradiction.  Thus the full partner germs are unequal, even though their assigned finite passports
agree.

## Aperiodicity

The same zero-progression argument with `C=1` proves aperiodicity directly.  If `F(z+h)=F(z)`, iteration
forces `h in pi i Z`, hence `A(z+h)=A(z)`, and then `B_L(z+h)=B_L(z)`.  Since `B_L` has the prescribed
zeros it is nonconstant, so `h=0`.  The affine normalization transfers aperiodicity to `X`.

## Attack and boundary cases

- **Depth zero:** the modulus is `(z-w)^2`; (5) makes the zero simple and preserves the residue value.
- **Arbitrary locations:** only symmetry-orbit disjointness is required.  The envelope parameter `a_0`
  avoids the finite set of real parts.
- **Zero-free axis:** the repair works globally because every `Q_j(iy)` is strictly positive and its
  degree exceeds the canonical CRT representative.
- **No hidden periodicity:** the finite polynomial zero set cannot absorb infinitely many iterates of
  an envelope zero; this is what forces any quasi-period into the known period lattice of `A`.
- **Finite boundary:** the proof uses a finite CRT and finite-degree positive repair.  It does not realize
  an infinite prescribed packet in one function.

## RH-route consequence

This theorem positively classifies the reach of finite local passport data:

> Every finite off-line zero configuration with every finite assignment of completed-flux contact depths
> occurs inside the elementary global `xi` envelope of FE symmetry, Schwarz reality, exact order one,
> aperiodicity, and a zero-free real axis.

Hence the surviving RH constraint is genuinely global and arithmetic.  It must fail to factor through
any finite set of tested zeros with any finite set of local completed-flux coefficients.  This strengthens
the open source law in `CompletedFluxGradedReality.lean`: the law must couple the Euler source to an
unbounded zero packet or to the complete germ, rather than merely deepen finitely many local tests.

## Relation to formal work

`formal/GaloisForLFunctions/RHTower/SimultaneousFiniteJetFlatness.lean` already formalizes the exact local
analytic-unit mechanism and the full finite-product flatness order.  In particular:

- `simultaneousFlatProduct_shift_factorization` is the local factor extraction used by the positive
  repair polynomial;
- `simultaneousFlatMultiplier_localFluxCorrection_order` proves independent exact depths at every
  simple disjoint quartet;
- `hermiteFlatPerturbedGerm_pair_same_prefix` proves common finite prefixes for independently chosen
  local units.
- `simultaneousFlatProduct_mul_I_pos_real` proves that every nondegenerate finite quartet packet is
  strictly positive real on the imaginary axis, formalizing the algebraic core of the global positive
  repair.

`formal/GaloisForLFunctions/RHTower/FiniteHermiteCRT.lean` now formalizes the finite polynomial CRT,
the sign/Schwarz averaging, and a representative whose degree is strictly below the product modulus.
The capstone
`exists_real_even_polynomial_iterateDerivative_eval_eq_degree_lt_modulus` supplies exactly the
real-even, Schwarz-real, degree-controlled interpolant used in the proof.

`formal/GaloisForLFunctions/RHTower/FiniteFluxPassport.lean` strengthens the local conclusion:
every polynomial residue-filled flux passport with constant term `-1` is realized by an entire
simple-zero exponential germ.  The successor theorem
`finite-completed-flux-passport-surjectivity.md` uses this to realize every finite graded-real
passport and an arbitrary transverse first separating coefficient.

`formal/GaloisForLFunctions/RHTower/ImaginaryAxisPositiveRepair.lean` now closes the global repair
step: the strict degree gap makes the quotient tend to zero at both ends, compactifies its range,
and yields one scalar for which the repaired polynomial is strictly positive real on the complete
imaginary axis.  Its packet capstone simultaneously certifies divisibility by every prescribed
quartet power, so all local multiplicities are retained.

`formal/GaloisForLFunctions/RHTower/CoshQuartetEnvelope.lean` now formalizes the envelope as an entire,
real-even, Schwarz-real, `pi i`-periodic function, proves its exact two-lattice zero classification,
and proves strict positive reality on the whole imaginary axis.
`formal/GaloisForLFunctions/RHTower/CoshPolynomialPeriodClassification.lean` proves that the period
group of its product with every nonconstant polynomial is exactly `{0}`.
`formal/GaloisForLFunctions/RHTower/CoshPolynomialExactOrderOne.lean` proves explicit global upper
and real-ray lower exponential bounds, certifying exact entire order one for every nonzero polynomial
multiplier.  The remaining formal task is the single capstone assembling these global results with
the equivariant CRT and positive repair.

## Parent-theory and novelty gate

- Polynomial CRT and involution averaging are classical.
- Adding a sufficiently large positive high-degree term is a classical real-polynomial technique.
- The candidate scientific content is their joint use to realize arbitrary finite off-critical quartet
  packets with independently assigned completed-flux passports while simultaneously retaining FE,
  Schwarz, zero-free-axis, exact-order-one, and aperiodicity guards.
- The statement remains `[NOVELTY UNVERIFIED]`; absence from the local corpus is not a literature gate.


## Lean formalization — 2026-08-17

Five new modules complete the capstone the card asked for.  Everything is axiom-clean and wired
into the `GaloisForLFunctions.RHTower` umbrella.

| New module | Content |
|---|---|
| `RHTower/CoshPolynomialQuasiPeriod.lean` | the **quasi-period** classification: `A(z+h)P(z+h) = C·A(z)P(z)` with `C ≠ 0` forces `h = 0`.  The tree only had the additive case `C = 1`.  A quasi-period still maps zeros to zeros, so the existing zero-orbit machinery forces `h ∈ πiℤ`; cancelling the envelope leaves `P(z+h) = C P(z)`, and comparing **leading coefficients** of `P ∘ (X+h) = C·P` gives `C = 1` |
| `RHTower/EnvelopeJetAgreement.lean` | the jet-agreement calculus: `iteratedDeriv_mul_congr` (Leibniz), `iteratedDeriv_envelopeProduct_eq_linear` (matching the jets of `ε(z-w)/A` makes `A·B` match those of the linear germ `ε(z-w)`), `simpleZero_of_envelopeProduct_jets` |
| `RHTower/QuartetSymmetryJets.lean` | jets under the two quartet symmetries, analytic (`iteratedDeriv_comp_neg`, `iteratedDeriv_of_even`) and polynomial (`iterate_derivative_comp_neg_eval`, `iterate_derivative_map_conj_eval`) |
| `RHTower/QuartetPassportRealizer.lean` | all global guards of `F = A·B`, plus the affine transfer `X(s) = F(-i(s-1/2))` giving `X(1-s) = X(s)`, Schwarz reality, and the zero-free **real** axis |
| `RHTower/QuartetPassportCapstone.lean` | the assembly |

| Card step | Lean name |
|---|---|
| the four points `α, -α, conj α, -conj α` and the two slot involutions | `quartetPoint`, `neg4`, `conj4`, `sign4`, `quartetPoint_neg4`, `quartetPoint_conj4` |
| symmetry-compatible Hermite interpolation, equation (1) | `quartetTarget`, `quartetBasePoly`, `quartetBasePoly_jets` |
| the CRT compatibility conditions | `quartetTarget_jet_neg`, `quartetTarget_jet_conj` |
| degree bound `deg B_0 < D = 4 Σ_j (N_j+2)`, equation (2) | `natDegree_finiteHermiteModulus`, `sum_quartet_index` |
| the repair `B_L = B_0 + L R` preserves every prescribed jet, equation (3) | `X_sub_C_dvd_quartetFlatPolynomial`, `X_sub_C_pow_dvd_simultaneousFlatPolynomial`, `iterate_derivative_eval_eq_zero_of_pow_dvd` |
| positivity `B_L(iy) > 0`, equation (4) | `exists_quartet_passport_polynomial` (via `exists_scalar_add_mul_pos_real_on_imaginaryAxis`) |
| **the realized entire function**, equations (5)–(6) | `exists_quartet_passport_realizer` |
| item 1, FE and Schwarz symmetry | `quartetRealizerStrip_one_sub`, `quartetRealizerStrip_conj` |
| item 2, exact order one and aperiodicity | `quartetRealizer_exact_order_one_bounds`, `quartetRealizer_periodic_iff` |
| item 3, zero-free real axis | `quartetRealizerStrip_ne_zero_on_realAxis` |
| item 4, simple zeros | `simpleZero_of_envelopeProduct_jets`, and the `n ≤ N_j+1` jet clause of the capstone |
| item 5, full-germ separation | `quartetRealizer_quasiPeriodic_eq_zero` |

Three points worth recording.

* **The equivariance conditions are made structural.**  Rather than computing the jets of
  `ε_w x / A(w+x)` at all four points of a quartet and checking the sign/conjugation rules, the four
  targets are *generated* from the base one by `P`, `P ∘ (-X)`, `P̄`, `P̄ ∘ (-X)`.  The CRT's two
  hypotheses then reduce to polynomial identities.
* **Only the head jet is analytic.**  The prescribed germ is verified at `α_j` alone; evenness and
  Schwarz reality of `F` propagate it to the other three points of the quartet, which is exactly the
  card's sign rule `ε_{-w} = -ε_w`, `ε_{conj w} = ε_w`.
* **A defect found in the existing repair interface.**  The packaged
  `exists_scalar_add_simultaneousFlatPolynomial_pos_real_on_imaginaryAxis`
  (`RHTower/ImaginaryAxisPositiveRepair.lean`) is vacuous: its hypothesis
  `∀ i y, (y : ℂ)^2 + (α i)^2 ≠ 0` binds `y` at type `ℂ` — the ascription is a no-op — and no `α i`
  satisfies it, since `y = ± i·α i` is a root.  The intended reading quantifies `y` over `ℝ`.  The
  capstone therefore calls the primitive `exists_scalar_add_mul_pos_real_on_imaginaryAxis` and
  supplies packet positivity from `simultaneousFlatPolynomial_mul_I_pos_real`, whose `y : ℝ` is a
  genuine parameter.  The packaged lemma should be restated.

**Not formalized (and not obligations of this card).**  The two remaining card gates are audits, not
formalization: the independent proof audit of the CRT averaging and quasi-period argument, and the
literature/parent-theory audit required before any scientific-novelty promotion.  The card is
`[NOVELTY UNVERIFIED]` and stays so.

Verification: `lake build GaloisForLFunctions.RHTower.QuartetPassportCapstone` — PASS;
`#print axioms` on all named results across the five modules reports only
`[propext, Classical.choice, Quot.sound]`.

## Gates

- [x] 0 -> 1: arbitrary-location formulation, symmetry-compatible interpolation, and global repair were
  made explicit and attacked.
- [x] 1 -> 2: CRT realization, positivity repair, flux-prefix equality, full-germ separation, exact order,
  and aperiodicity have complete proofs above.
- [ ] independent audit of the invariant CRT averaging and quasi-period argument.
- [x] 2 -> 3: the degree-bounded equivariant CRT, packet positivity, global scalar repair, and
  cosh-envelope realizability, product period classification, and exact entire order one are
  formalized; the arbitrary finite-packet capstone is assembled
  (`RHTower/QuartetPassportCapstone.lean`, `exists_quartet_passport_realizer`).
- [ ] complete literature and parent-theory audit before any scientific-novelty promotion.
