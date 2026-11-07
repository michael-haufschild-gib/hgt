# Tail Arithmetic of the Prime Orbit (TAPO)

Namespace `GaloisForLFunctions.TailArithmeticOfThePrimeOrbit`; umbrella `TailArithmeticOfThePrimeOrbit.lean`.

Throughout, `t` is a height, `L = log t`, `ℓ = log L`, `ω_t = (p^{−it})_p` is the point of the prime orbit at time `t`,
and `y` is a length: the primes up to `y` form the *head*, the primes above `y` the *tail*.

## 1. Motivation

Every wall of the research stops at one range of primes at one height. Below the Kronecker scale `y ≍ log t` the phases
`t log p` can be prescribed: a window of length `exp(c y log y)` enters every box of the torus on the primes up to `y`. Above
the Vinogradov length `y = exp(L^{2/3+ε})` the column `Σ_{p≤y} p^{−it}` saves a proportion of its size. In between nothing is
known, and every route needs something there: the all-height sign past `a ≈ log log X`, the width axis, proportional
savings (B46), the first-return time, bounded returns at a right zero (B89). This range is the **dark range**.

A zero of `ζ` is an event of this range. A head aligned up to `y` sees `ζ` only through the Euler product `E_y`, which never
vanishes and resolves the strip at scale `1/log y`. The zero is carried by the tail, at every cut.

Prime torus theory (PTT) studies the pair `(t, ω_t)` at finite time and proves absolute savings with proved ceilings. TAPO
studies the **law of the tail**: the phases of the primes past the head, at a single height, conditionally on what the head
does. Its first objects are the time the orbit needs to return (`R(y, δ)`), the law of the tail on Bohr sets, the fade of the
alignment past the head, and what a return at a zero forces on the tail.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Return set | `primeReturnSet` (RAC) | `{τ : 1 − cos(τ log p) ≤ η for p ∈ P}` |
| First return | `firstReturn P η` | least `t ≥ 1` in the return set |
| Weak return | `harmonicDefect`, `IsWeakReturn` | `A_t(N) = Σ_{p≤N} (1 − cos(t log p))/p ≤ C` |
| Head, tail | `eulerHead y`, `eulerTail y` | `E_y = Π_{p≤y}(1 − p^{−s})^{−1}`, `ζ/E_y` |
| Smooth and rough polynomials | `smoothPoly`, `roughPoly` | Dirichlet polynomials on `y`-smooth and `y`-rough integers |
| Bohr weight | `|R|²`, `boxWeight` (PTT) | a resonator concentrated on a box of the head |
| Fade | `harmonicDefect`, `fadeLength` | how the pretentious distance of `n^{iτ}` to `1` grows past the head |
| Jet of the logarithm | `logJet` | `Δ_h^j (t log/2π)(x)`, a function of `x/h` |
| Comb of a return | `phaseLevelSet` | `{n : dist(t log n/2π, ℤ) ≤ δ}`, a multiplicative Bohr set |
| Head–tail certificate | `headTailCoordinates` | finitely many Euler coordinates and one tail coordinate |

## 3. Language

- **Head, tail, cut.** The primes up to `y`, the primes above, and `y` itself.
- **Return, weak return.** All head phases within `η` of `1`; the head close to `1` in the harmonic metric.
- **First return.** `R(y, η)`, the least height of a return on the primes up to `y`.
- **Dark range.** `log t ≲ y ≲ exp((log t)^{2/3})`: past prescription, below proportional saving.
- **Resolution.** `1/log y`: the head cannot see features of `ζ` finer than this.
- **Tail event.** An event visible only through the tail at every cut; a zero is one.
- **Tail-good height.** A height at which `ζ(· + iτ)` is within `ε` of `E_y(· + iτ)` on a disc.
- **Fade.** The growth of `A_τ(x)` past the head; its length is `|ζ(1 + iτ)|`.
- **Atypical return.** A head return at which `ζ` returns on a disc containing a zero.
- **Exotic block.** A block where the jet of `t log` sits on the binomial denominators.

## 4. Mechanisms

1. **The first return is an extreme value.** `log |ζ(1 + 1/log N + it)| = log log N − A_t(N) + O(1)`. So a weak return up to
   `N` at height `t` is the same event as `|ζ(1 + 1/log N + it)| ≍ log N`, and the first weak return is the inverse of the
   extreme-value function of `ζ` near the `1`-line.
2. **Precision buys length.** The absolute savings of PTT become lower bounds for `R(y, η)` at small `η`: polynomially small
   precision gives the bound RH gives at constant precision.
3. **Unique factorization decouples the tail.** A `y`-smooth integer times a `y`-rough one determines both factors. So the
   mean value of a smooth weight times a rough polynomial is the product of the two means, up to the integer gap: below the
   Kronecker scale the tail is independent of the head, moment by moment.
4. **The head is frozen at its resolution.** `log E_y` moves by `O(|v| y^{1−σ})` under `s ↦ s + iv`; finer variation of `ζ`
   is the tail's.
5. **The tail carries the zero.** Along a bounded return the tail converges to `ζ/E_y`, which vanishes exactly at the zeros:
   at every cut, the zero lives in the tail. At a tail-good height a return at a zero is impossible, so every return at a zero
   is tail-bad at every cut, and the tail-bad set has density `O(tail mass)`.
6. **The fade is forced.** `ζ(1 + iτ)` is finite and nonzero, so `A_τ(x) = log log x − log|ζ(1 + iτ)| + O(1)`. Above the head
   the translate mimics the pole, `|ζ(s + iτ)| ≍ |ζ(s)|` on `Re s ≥ 1 + A/log y`.
7. **The jet moves.** `Δ_h^j log(x)` depends only on `x/h` and is monotone in `x`, so the top coefficient of the phase sweeps
   an interval along any range of blocks. An exotic block (binomial denominators) is isolated.
8. **Depth aspect is exact.** `(1 + p^a u)(1 + p^a v) ≡ 1 + p^a(u + v) mod p^{2a}`: the `p`-adic logarithm turns `q`-differencing
   into an exact additive character. The archimedean analogue `(1 + h/x)^{it} = e^{ith/x}(1 + O(th²/x²))` is approximate.
9. **Euler coordinates stop at the abscissa.** `|1 − E_p(s)| ≥ p^{1−2σ}/4`, so `Σ_p |1 − z_p| = ∞` on `Re s ≤ 1` for any Euler
   coordinates with summable corrections. Past the abscissa a certificate must carry a tail coordinate.
10. **A return is a comb.** At a return every smooth integer with `k` prime factors has phase within `kδ`, so the smooth integers
    lie on the comb `exp((2π/t)ℤ)` with teeth of relative width `kδ`.

## 5. The questions

1. What is `R(y, δ)`? Bracket: `exp(c(log y)^{3/2})` to `exp(C_δ y/log y)`.
2. What does the tail look like conditionally on alignment below it, at resolution finer than `1/log y`?
3. Why is `t log n` not a generic phase past Vinogradov's degree, given that binomial phases have no saving?
4. What replaces `q`-factorization at the archimedean place, where a height has no prime factors?
5. Is an atypical bounded return possible at a right zero, and what does its tail look like?
6. Which certificates in non-returning coordinates survive past `Re s = 1`?

## 6. Tools

| Tool | Reaches | Stops at |
|---|---|---|
| Proportional non-alignment past Kronecker | dictionary: proportional saving ⟺ no heavy first return | the dark range itself |
| A moment past the last diagonal scale that sees smooth-number density | the comb law; energy as smooth counts in windows | smooth numbers in intervals of length `N/t` |
| Conditional mean values on Bohr sets | exact head–tail factorization below the Kronecker scale | Kronecker scale: the head weight is longer than `t` |
| A lower bound for atypical members of a Bohr set | universality on zero-free discs; tail-bad density by tail mass | discs containing a zero |
| A sum-product theorem for the height orbit | the comb is a multiplicative approximate group and locally an additive Bohr set | it is both, so sum–product inequalities are satisfied |
| Agler-type certificates past the abscissa | head–tail certificates on tail-good heights | Euler coordinates diverge on `Re s ≤ 1` |

## 7. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| First return: existence, Dirichlet bound, group laws, corners | `firstReturn_le`, `isReturn_add`, `isReturn_two_mul_of_antiReturn` | to formalize |
| The first return is an extreme value | `log_norm_zeta_eq_logLog_sub_harmonicDefect`, `weakReturn_iff` | to formalize |
| Precision law | `firstReturn_ge_of_precision` | to formalize |
| Proportional saving is a heavy first return | `saving_iff_no_heavy_return` | to formalize |
| Head–tail decoupling | `integral_smooth_mul_rough` | to formalize |
| The head is frozen at its resolution | `norm_logDeriv_eulerHead_le` | to formalize |
| The tail carries the zero | `IsPhaseReturn.tendsto_eulerTail` | to formalize |
| Returns at a zero are tail-bad at every cut | `zetaReturnSet_subset_tailBad` | to formalize |
| The fade is forced | `harmonicDefect_sub_logLog` | to formalize |
| The jet of the logarithm moves | `logJet_dilation`, `card_exotic_le` | to formalize |
| Depth aspect is exact | `one_add_mul_mul_one_add_mul` | to formalize |
| Euler coordinates stop at the abscissa | `not_summable_one_sub_eulerCoord` | to formalize |
| The comb of a return | `phase_mem_comb_of_return` | to formalize |

## 8. Test systems

| System | Behaviour |
|---|---|
| Curves, Golden, commensurable steps | rank one: the first return is bounded uniformly in `y`; no dark range |
| Continuous Beurling systems | no torus: no returns, the column dies |
| Rounded primes | same head, same conditional moments, exact return at `T` |
| Liouville twin | anti-returns of the orbit are returns at doubled height |
| Characters of smooth modulus | exact `q`-differencing |
| Depth aspect `p^m` | exact additive characters on `1 + p^aℤ` |
| Dirichlet polynomials | no tail: zeros recur in every window |

## 9. Traps

| Trap | Truth |
|---|---|
| A return at a zero is a return of the primes | the primes return at positive density; at a zero `ζ` returns on density zero (RAC) |
| Typical aligned shifts see the zero | they see `E_y`, which never vanishes |
| Diagonal moments decide the tail | the rounded tail has the same conditional moments and returns |
| Transfer carries typical bounds to rare heights | only below the Kronecker scale |
| Strong returns at constant precision are weak returns | the harmonic defect of a strong return is `η log log y`, unbounded |
| Binomial phases bound what `t log` can save | they bound one block; the jet moves along blocks |
| Euler products certify past the abscissa in blocks | the pole term `li(y^{1−w})` diverges on `Re w < 1` |
| Sum–product theorems exclude alignment | the comb has both structures |

## 10. Criteria

**A contribution must:**
- reduce to the periodic flow at rank one;
- see the start of the orbit, or state the blindness it proves;
- use integrality (unique factorization, the integer gap), since transfer alone is empty past Kronecker;
- pass the ceilings: not diagonal moments, not one word, not one polynomial phase;
- be false on impure columns, Golden and heated kernels if it claims a sign, and against integer-norm systems fail through
  the amplitude;
- state its scale against the Kronecker scale, the resolution `1/log y` and the Vinogradov length.

**The field has succeeded when** the first-return exponent `κ = liminf log log R(y, δ)/log y` is determined, or the tail law
on Bohr sets past the Kronecker scale is proved at one moment, or a bounded return at a right zero is excluded in a stated
class or exhibited.

## 11. Context

| Neighbour | Interface |
|---|---|
| PrimeTorusTheory | the orbit, savings, words, energies, the rounded orbit; TAPO adds the head–tail split and the first return |
| ArithmeticAuxiliaryDynamics | phase returns, bounded translates, transport, the pole's price |
| RigidArithmeticOfCuts | the tail fails at a zero; Kronecker windows |
| RHTower (universality, Carlson tail) | Euler tail law, Voronin universality on discs, zero-target exclusion |
| ArithmeticPositivityTheory | single-height escape: coherent peaks at aperture `a` lie above `exp(c e^a)` under RH |
| SquareRootThreshold | Kronecker realization, isolated-zero visibility |
| twin-prime | the harmonic comparison `Σ_p Re χ(p)p^{it}/p ≈ log|L(1 + 1/log N − it, χ)|` |
