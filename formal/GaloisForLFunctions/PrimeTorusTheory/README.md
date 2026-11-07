# Prime Torus Theory (PTT)

Namespace `GaloisForLFunctions.PrimeTorusTheory`; umbrella `PrimeTorusTheory.lean`.

## 1. Motivation

Over `𝔽_q` the phases of the Euler product are one coordinate: `q^{−s}` is periodic, there is one
column, and Schur parameters, Castelnuovo and the Carlitz stencil close. Over `ℤ` the coordinates
`p^{−s}` are independent. The height `t` moves one point `ω_t = (p^{−it})_p` along a dense
one-parameter subgroup of the infinite torus `𝕋^∞`, and the Gamma base sees only `t`.

Every one-dimensional theory (inner functions, canonical chains, lattice Schur theory, critical
Hardy theory, the curve chain) has one causal order and one reflector per step, so it cannot state
the walls that concern many independent primes at finite height. Torus theories (gauge torus,
Wiener monoid, Bohr points, multiplicative Bochner theory) have no time coordinate, and by Bohr's
isometry a fixed function sees the whole torus: there the infimum over the orbit is the infimum over
the torus, and only size survives.

PTT takes as its object the pair `(t, ω_t)` **at finite time**: how far the orbit has travelled by
time `T`, what it has not yet reached, and what it costs to get there.

## 2. Objects

| Object | Meaning |
|---|---|
| Phase system | steps `ℓ : ι → ℝ`, weights `a : ι → ℝ≥0`; for `ℤ`, `ℓ_p = log p` |
| Orbit | `ω_t(i) = e^{−itℓ_i}`, a one-parameter subgroup of `𝕋^ι` |
| Space | `X = [1,∞) × 𝕋^∞` with the graph `{(t, ω_t)}` |
| Column sum | `P_a(t) = Σ a_i cos(tℓ_i)`, size `S_a = Σ a_i` |
| Defect | `D_a(t) = S_a − P_a(t) ≥ 0`, a squared Hilbert distance from the start of the orbit |
| Bohr sets | `B_a(r) = {t : D_a(t) ≤ r²}`, the return sets |
| Large-value set | `E_a(θ) = {t : P_a(t) ≥ θ S_a}` |
| Alignment time | first time after the start that the orbit enters a half-space |
| Near-diagonal energy | `E_k(y,T)`: pairs of `k`-fold products of primes `≤ y` with `|log(a/b)| ≲ 1/T` |
| Hull | limits of translates of `ζ`, fibred over torus points |
| Corners | `+1` (the start of the orbit, the pole), `−1` (the Liouville twin) |

## 3. Language

Alignment, entry, return, corner, race (base against columns), fibre, time to reach, Kronecker scale
(`y ≈ log T`: the orbit reaches every half-space), mixing time, below-mixing regime, diagonal range
(`k ≤ log T / log y`), start of the orbit, height coupling.

## 4. Mechanisms

1. **Group closure.** `ω_{t+u} = ω_t ω_u`, so `√D_a` is subadditive: the defect is a translation
   invariant Hilbert metric, and Bohr sets are approximate groups. Multiples, differences and doubling
   of large-value heights are controlled.
2. **Halász–Montgomery on the orbit.** Large values at `N` heights force the correlation on the
   differences of those heights to be large on average. Rare heights descend to lower heights.
3. **Resonators are finite-time Bohr isometries.** A Fejér product on the primes of a finite set is
   the square of a Dirichlet polynomial with unimodular coefficients on an integer set, so integrality
   gives a mean value with no Baker input. Every half-space of the torus on primes `≤ c log T` is
   entered in every window of length `T`.
4. **Unique factorization pays for non-alignment.** Past the diagonal range two products of primes
   fall in one box of width `1/T` by pigeonhole, they are distinct integers by unique factorization,
   so their log ratio is at least `y^{−k}`. A return would make that ratio small.
5. **The start of the orbit.** Positive counts contain `t = 0`. The mixing term of the near-diagonal
   energy is the contribution of the start, and every return adds a further term of the same shape.
6. **Doubling and corners.** `ω ↦ ω²` sends both corners to `+1`, which is the `3 + 4cos + cos 2`
   inequality as a statement about the orbit: a visit near `−1` is a visit near `+1` at double height.

## 5. Questions

1. How long does the orbit need to enter a half-space at length `y = (log T)^{2K}`, `K > ½`? Is there
   any saving against size?
2. What is the near-diagonal energy past `k = log T / log y`?
3. Why does the Gamma coupling sit at exactly the critical growth `κ = ½` of the Bernstein theorem?
4. Which functions on `X` restrict to the Ξ-current and have a sum-of-squares form with `t`-dependent
   coefficients?
5. Over which torus points does the hull extend into the strip, and which of those carry zeros?
6. Does a large-value set of heights have additive structure, and does its structure force returns
   that the pole must pay for?

## 6. Tools to develop

- Non-alignment below the mixing time.
- Bounds on `E_k(y,T)` for `k ≫ log T / log y`.
- Discrepancy of the orbit against Haar measure at time `T`, for `y > log T`.
- Transfer from typical to rare heights.
- Sum-of-squares certificates on `X` with kernel-valued prime conductances.

## 7. Test cases

Curves (rank one, periodic flow); Golden (rank one, wrong weights); commensurable steps (unbounded
room in one column); continuous Beurling systems (no torus: `ζ_B → 1` vertically); integer-norm
systems (same torus, different amplitude).

## 8. Criteria for a contribution

A contribution to PTT must:

- reduce to Schur, Castelnuovo and periodic flow at rank one, or state why it does not apply there;
- not be invariant under torus translation, unless it is an explicit statement of that blindness;
- carry a time coordinate: a statement with no `T` belongs to a torus theory;
- see incommensurability: commensurable steps must behave differently;
- be false on impure columns, Golden and heated kernels if it claims any sign; against integer-norm
  systems it must fail through the amplitude, since the torus is the same.

## 9. Limits

- For a Dirichlet series the supremum on the orbit equals the supremum on the torus, so every gain
  must come from finite time or from the Gamma coupling.
- A non-alignment theorem speaks about large heights only. A one-off at fixed height is invisible to
  it.
- Non-alignment gives the sign past size, which is a zero-free strip up to crystal shielding. A
  theorem of the field that is macroscopic on the critical line is of quasi-RH strength.
