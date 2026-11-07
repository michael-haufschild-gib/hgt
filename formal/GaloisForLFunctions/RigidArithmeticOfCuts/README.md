# Rigid Arithmetic of Cuts (RAC)

Namespace `GaloisForLFunctions.RigidArithmeticOfCuts`; umbrella `RigidArithmeticOfCuts.lean`.
Every theorem is unconditional. RH and zero-free strips appear only inside implications and equivalences.

## 1. Motivation

Suppose positivity, Weil positivity and spectral methods are all excluded. Inner-function theory loses its core,
since a Blaschke mass is a positive quantity and a passive medium is a positive form. Stepanov over `ℤ`, as a linear
stencil theory, has closed: the rate of a producer is the Mertens level. What is left has to be nonlinear in the primes.

This field asks how an exact statement about one object, `N(x) = ⌊x⌋`, forces its zeros by operations that have no sign
and are not linear floor identities. Three facts set the scene.

- All multiplicity of a stencil lives in fractional parts: `g(r) = −Σ c(k) {r/k}`.
- Every integer is a cut. Over `𝔽_q[T]` norms are quantized and a stencil is cut only at a degree boundary.
- The object is single. Within FE defect `1/6400` there is nothing else, so there is no deformation theory near it.

So the theorems of the field concern one function and the exact system of linear and nonlinear relations it satisfies.

## 2. Objects

| Object | Meaning |
|---|---|
| Sawtooth | `r mod k`, `{x/k}`; the jump of `⌊x/k⌋` |
| Cut system | the infinite linear system `Σ_r u(r) (r mod k) = log k` |
| Fake prime measure | a nonnegative solution of the cut system up to level `K` |
| Tail | `T(r) = Σ_{j ≥ r} u(j)`, the scaling image of `ψ(n/r)/n` |
| Cut functional | `C_k T = lim_J (Σ_{r ≤ kJ} T(r) − k Σ_{j ≤ J} T(kj))` |
| Kernel | tails with `C_k T = 0` for all `k` |
| Ledger | `Σ_d a(d) g(⌊x/d⌋)` for a weight `a` |
| `k`-ledger | the same reading of the `k`-fold convolution `a^{∗k}` |
| Finite oscillation | `ψ(x) − x = x^β T(log x) + O(x^{β−η})`, `T` a trigonometric polynomial |
| Dilation operators | Hecke action on `ψ`, tails and stencils |
| Return set | Bohr set of a finite prime family; returns of `ζ` at a disc |
| Gauge torus | unitary completely multiplicative `ω`; Adams operators |
| Integer Beurling system | a multiset of integers `≥ 2` used as primes, `a(n)` its integer count |
| Maximal-angle zero | the zero of `Q(α²)=XiC α` with maximal positive argument; `w=−(s−½)²` |

## 3. Language

- **Cut.** A point where a floor jumps. **Multiplicity against size.** The count of a cut against the size of the integer it builds.
- **Blind.** A functional is blind at `ρ` when its generating function has no pole at `ρ`.
- **Exact.** A functional is exact when its value is determined by `⌊x⌋` alone.
- **Fake.** A measure consistent with the cut system at some level.
- **Kernel vector.** A tail invisible to every balanced stencil. Zeros are the power-law kernel vectors.
- **Annihilator.** A dilation combination sending a finite oscillation to lower order.
- **Transport.** Copying a zero to new heights by a vertical return, by minimum modulus.
- **Isolation.** A positive lower bound for the distance from `ζ` to every other system.
- **Extremal position.** A statement at the zero of maximal angle, used in place of a sign.

## 4. Mechanisms

1. **Exact identities.** Chebyshev's `Σ_k ψ(x/k) = log⌊x⌋!`, Selberg's `Λ log + Λ∗Λ = μ∗log²`, Liouville's `Σ_k L(x/k) = ⌊√x⌋`.
2. **Triangular rows.** Differences of rows of the cut system are triangular with an infinite tail.
3. **No uniform measure on `ℕ`.** A finite measure with `W(kℕ) = S/k` for all `k` is zero.
4. **Extremal-factor modulus.** For an upper-half-plane rotation, Hadamard factors at the maximal-angle zero compare in the same direction [paper argument]. The exact factor difference is `4 Im(q) Im(u)` (`rotated_factor_norm_sq_sub`).
5. **Rigidity as uniqueness.** Exact FE forces the rational primes; a small defect does too.
6. **Transport by minimum modulus.** Rouché on a circle around a zero.
7. **Gamma speed as dominance.** Finite Euler speed is beaten by Gamma speed above a horizon.
8. **Nonlinear ledgers.** `A^k ζ` has a pole of order `k − m` at a zero of multiplicity `m`.

## 5. Traps

| Trap | Fact |
|---|---|
| A stencil identity sees a zero | Every exact ledger is holomorphic at every zero |
| A functional that sees a zero is a new input | It has no exact value |
| Selberg's identity excludes a zero | It is exact, so its sum is blind; only its pieces see zeros |
| Balanced rotated coefficients force equal moduli at a zero | Only when the coefficients are nonzero there; `a=b=F` supplies a vacuous identity for every entire `F` |
| Integer norms exclude fakes | Integer Beurling systems near `⌊x⌋` exist |
| The twin is a fake for zero location | `ζ(s)/ζ(2s)` has the same zeros right of `½` |

## 6. Questions

1. What replaces Frobenius? Over `𝔽_q[T]` quantized norms give rate `0`. Over `ℤ` what removes the sawtooth?
2. What nonlinear functional of `Λ` sees a zero mode and survives the Liouville twin?
3. Why do primes recur at a zero, if they do?
4. Is a single off-line zero a contradiction with `N(x) = ⌊x⌋`?
5. What is the fake prime measure closest to the true one, for each `K`?
6. Is there an arithmetic rotated identity with balanced coefficients nonzero at the zeros of `ξ`?

## 7. Tools to build

- Ledgers that are not blind, nonlinear in `Λ`.
- A parity input in the term `Σ c(k) λ(k) L(⌊x/k⌋)`.
- Effective Kronecker at arithmetic scale.
- Pointwise bounds below the VK length.
- A metric geometry of Beurling systems above the gap.

## 8. Test cases

Weil for curves through Stepanov and the Carlitz stencil. Kloosterman data. Continuous Beurling systems, which must fail
construction. Golden, which obeys transport and fails construction.

## 9. Open research topics

- The cut system over `ℤ`: the kernel beyond power laws.
- Finite-level radius of the fake set.
- Coefficient classes for rotated relations.
- Smallest FE defect carrying a one-off.
- Integer-norm one-offs.

## 10. Pillar theorems

The following programme targets are not all formalized. The coefficient boundary below is Lean verified.

| Theorem | Statement |
|---|---|
| Uniqueness of the fake | A fake prime measure at every level is the pronic measure |
| Zeros are the kernel | `r^{-s}` lies in the kernel on `Re s > 0` iff `ζ(s) = 0` |
| Extremal modulus [paper] | Under `¬RH` the maximal positive angle is attained and `|Q(qw)| > |Q(q̄w)|` there for `|q|=1`, `Im q>0` |
| Coefficient boundary [Lean] | `balanced_relation_zero_or_modulus_eq`; unit-coefficient cancellation iff equal moduli; `balanced_modulus_gap_le` bounds every residual |
| Vacuous normalized identity [Lean] | `exists_normalized_entire_vacuous_rotated_relation`: origin normalization still permits an off-axis zero and unequal rotated moduli |
| Ledger hierarchy | `ζ A^k` has a pole of order `k − m` at a zero of multiplicity `m`; only `k = 1` is blind |
| Twin separation | Selberg's ledger separates the Liouville twin at scale `x` |
| Hamming stability | Zeros right of `σ` are invariant under exchange of primes of exponent `< σ` |

## 11. Place in the research

| Neighbour | Relation |
|---|---|
| ArithmeticAuxiliaryDynamics | stencils, rate, fake measures; RAC continues where its linear theory closes |
| ZeroConfigurationGeometry | the finite oscillation and dilation annihilation |
| ArithmeticPositiveDuality | Beurling isolation |
| ArithmeticOfSquareRootPrecision | parity twins and filters |
| ArithmeticInnerFunctionTheory | its complement: it keeps positivity |

## 12. Success criteria and contributions

A contribution belongs to this field only if it

- uses no quadratic form with a sign and no self-adjoint operator;
- can be read over `𝔽_q`, where Hasse–Weil must come out in the same language;
- distinguishes rational primes from continuous and discrete Beurling systems;
- breaks parity: it passes the Liouville twin and the filters on Type I and II data;
- is not blind to zero modes, which excludes every functional linear in `ψ` read through floors.

The goal of the field is a contradiction between one off-line zero and `N(x) = ⌊x⌋`, or a precise proof that a stated class of arithmetic information cannot give one.
