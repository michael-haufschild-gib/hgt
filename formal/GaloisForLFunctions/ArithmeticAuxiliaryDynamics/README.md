# Arithmetic Auxiliary Dynamics (AAD)

Namespace `GaloisForLFunctions.ArithmeticAuxiliaryDynamics`; umbrella `ArithmeticAuxiliaryDynamics.lean`.

## 1. Motivation

Every sign route to RH uses a positive form, a passive medium or an operator. This programme asks what is
left when all of them are removed. Over `𝔽_q` something is left: Stepanov's proof. An auxiliary polynomial is
constructed, forced to vanish beyond its size, and that count gives purity, with no Hodge index in sight.
Almost-periodicity of the zeros in `Im s` does the rest, and a curve has it automatically.

AAD studies how the rational integers force zeros of `ζ` by two operations that carry no sign:

- **Construction.** An integer object forced to vanish beyond its size.
- **Transport.** A vertical return moving a zero to new heights.

The split matches RH: construction aims at the count (ZAL side), transport at one-offs (AAL side). A proof in
this field would be Weil's theorem in Stepanov's order, over `ℤ`.

## 2. Objects

| Object | Meaning |
|---|---|
| Stencil `c : ℕ →₀ ℤ` | integer ratio `∏⌊n/k⌋!^{c(k)}`, equivalently a Dirichlet polynomial `D_c(s) = Σ c(k)k^{-s}` |
| Multiplicity `g_c(r) = Σ c(k)⌊r/k⌋` | exact order of vanishing of the auxiliary at primes of `(n/(r+1), n/r]` |
| Increment `h_c = c * 1` | discrete derivative of the multiplicity |
| Balance, slope, peak | `D_c(1) = 0`; `D_c′(1)`, the size of the auxiliary; `-D_c(0)`, the peak multiplicity |
| Nair lattice and horizon | `∫₀¹P` for `P ∈ ℤ[X]` of degree `≤ n` fills `lcm(1..n+1)⁻¹ℤ` |
| Hecke dilations | `T_j : c ↦ c(·/j)`, the commuting action on stencils |
| Gauge torus, Adams operators | completely multiplicative phases and the maps `x ↦ kx` |
| Return sets | shifts `τ` with `ζ(· + iτ)` uniformly close to `ζ` on a set |
| Hurwitz limit set | limits of vertical translates of `ζ` |
| Extremal top layer | the zeros of largest real part, when attained |

## 3. Language

Size against multiplicity. Siegel half (small auxiliaries exist) and Liouville half (nonzero values are large).
Integrality exponent. Slope. Peak. Return exponent. Transport. Extremal position in place of sign.

## 4. Mechanisms

1. Forced vanishing contradicting size: the ledger `Σ m_p log p ≤ log A`.
2. Zero transport by minimum modulus: a return of `ζ` on a disc around a zero produces a new zero.
3. Extremal-factor modulus at a top zero.
4. Exact functional-equation rigidity as a uniqueness theorem.
5. Gamma speed as dominance.

## 5. Questions the programme must answer

1. What replaces Frobenius? Over `𝔽_q`, `(x^q)′ = 0` makes multiplicity cheap. What makes multiplicity at
   primes cheap over `ℤ`?
2. What is the exact rate `A(K) − 1` of the least stencil slope in the alphabet size? Is it a capacity?
3. Where does the factor 2 of sieve parity go in a signed construction?
4. Why do primes recur at a zero, if they do?
5. Is a single off-line zero a contradiction with integer-valued integers `N(x) = ⌊x⌋`?

## 6. Tools to develop

- Size bounds for signed stencils, past sup-norm.
- Siegel's lemma with parity constraints.
- Zero and multiplicity estimates over `ℤ` on the gauge torus.
- Quantitative universality at prescribed base points.
- Effective Kronecker at arithmetic scale.

## 7. Traps

| Trap | Fact |
|---|---|
| A stencil is independent of prime information | see Section 9; the corpus stencils come from a Möbius test by duality |
| Integrality gives a rate | the Nair lattice is exact, and exactness carries no rate |
| Non-alternating stencils can be sharpened | they stop above `31/30` |
| Vanishing at primes selects parity | divisibility sees primes and the odd class alike at `√x` precision |
| Sup-norm control of auxiliaries reaches the main term | capped at `e^{-0.87n}` |
| Returns at typical heights give returns at a zero | a return of positive density at a fixed off-line zero is impossible |

## 8. Pillars inherited from the corpus

| Theorem | Lean |
|---|---|
| Nair lattice exact; `ψ(n+1)` is the best integrality bound | `nairLattice_eq`, `isGreatest_log_inv_nairIntegral` |
| Slope infimum is 1, unattained | `isGLB_producerSlopeSet`, `one_notMem_producerSlopeSet` |
| Finite-prime and non-alternating ceilings | `finite_prime_alphabet_slope_gt_one`, `non_alternating_stencil_slope_gt` |
| The ledgers over `𝔽_q[X]` and `ℤ` | `sum_le_natDegree_of_vanishing`, `sum_mul_log_le_log_of_dvd` |
| Weil in Stepanov's order for split hyperelliptic curves | `stepanov_order_hyperelliptic` |
| Structure of failure of AAL | `not_asymptoticAbscissaLaw_iff_bilateral_spectralGap` |
| Typical-height pair returns; transport | `exists_headPhaseReturnSet_zetaReturn_typicalHeight`, `exists_zero_of_mem_poleShiftedReturnSet` |

## 9. Research topics

Construction: the calculus of stencils, the two-sided rate of `A(K)`, the role of the peak, the parity factor.
Transport: return exponents at a zero, limit sets, the fake battery. Bridge: where one operation can feed the
other.

## 10. Place in the research

AAD sits on the sign-free side of the corpus map: Production, Transport, Rigidity and Dominance. It uses
ArithmeticKreinLangerTheory (stencils, ledgers), ArithmeticOfSquareRootPrecision (Nair lattice, precision),
ArithmeticProduction (necessary lengths, parity filters), ArithmeticGaugeTheory (Adams operators, gauges),
ArithmeticDiscreteness (repulsion, near-coincidences) and RHTower (recurrence, AAL).

It is the complement of ArithmeticInnerFunctionTheory, which keeps positivity: a Blaschke mass is a positive
quantity and a passive medium is a positive form.

## 11. Success criteria

A contribution belongs to this field only if it

- uses no quadratic form with a sign, no self-adjoint operator and no Hadamard positivity;
- is stated so that it can be tested over `𝔽_q`, where Hasse–Weil must come out in the same language;
- separates rational primes from continuous Beurling systems and from discrete near-fakes;
- passes the Liouville twin and the filters on Type I and II data;
- is not bound by the last-scale floor of polynomial detectors.

The programme succeeds when it has an exact answer to each question of Section 5, including answers of the
form "this is equivalent to a stated zero-free region" or "this class cannot do it".
