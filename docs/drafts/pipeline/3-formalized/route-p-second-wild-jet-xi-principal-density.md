# Route-P second wild jet matches Xi principal density

- **ID:** IRH-P-SECOND-WILD-JET-XI-DENSITY
- **Stage:** 3-formalized
- **Type:** CONSTRUCTIVE BRIDGE
- **Source:** intrinsic prime-labelled exponential factors of full Route P; second wild/Mellin
  derivative; irregular-RH `det₂` carrier
- **Statement:** A source-pure signed second wild jet with cofinal multiplier
  `(log p)^2 / (2πp)` has the same exact logarithmically enhanced approximation-number scale as
  ordered reciprocal Xi.

## Goal

Construct, before reading Xi zeros, a Route-P irregular source operator carrying the principal
`log n/(πn)` singular density that trace-class and first-logarithmic Route-P carriers lack.

## Gates

- [x] 0 → 1 in-progress: exact source operator fixed; corpus and primary-literature audits complete
- [x] 1 → 2 fully-proven: dependency-closed asymptotic proof and hostile audit
- [x] 2 → 3 formalized: Lean theorem, direct check, umbrella wiring, new-axiom audit
- [ ] 3 → 4 publication-ready: standalone note and external novelty review pending

## Audit

- `[CORPUS]` Literal depth-zero Route-P multiplier is `2/p`, hence only weak `S₁`; full positive
  depth contributes a trace-class tail.
- `[CORPUS]` Physical first prime-log endpoint `log p/p` exists, but ordered primes satisfy
  `p_n ~ n log n`, so this still has only `1/n` density and remains weak `S₁`.
- `[CORPUS]` `nth_prime_asymp` and `tendsto_log_nthPrime_div` imply
  `(log p_n)^2/p_n ~ log n/n`.
- `[CORPUS]` Ordered reciprocal Xi has exact approximation-number model
  `log(n+1)/(π(n+1))`.
- `[CORPUS]` Searches for `prime log squared divided by prime diagonal operator`, `RouteP second
  wild derivative`, and `Xi principal wild face` found no operator or comparison theorem.
- `[LITERATURE]` Irregular Riemann--Hilbert theory retains exponential components and their Stokes
  filtrations; enhanced Fourier--Sato/Laplace transport geometrically controls exponential factors.
- `[LITERATURE]` Hilbert--Schmidt kernels are natural `det₂` inputs in RH/Fredholm constructions.
  No source found relating a prime-labelled second exponential jet to Xi singular density.
- `[NOVELTY STATUS]` `[BRIDGE]`: new arithmetic/irregular-RH synthesis; no external-priority claim.

## Exact theorem `[PAPER PROOF COMPLETE]`

Define the nonnegative second-jet profile

```text
j₂(x) = (log(x) · x^(-1/2))² / (2π).
```

Cap only the finite low-prime sector by replacing `x` with `max(exp 2,x)`. On the two signed
prime sectors use multipliers `+j₂(p)` and `-j₂(p)`, and call the resulting diagonal operator
`J₂`. Then

```text
a_n(J₂) / (log(n+1)/(π(n+1))) → 1,
a_n(J₂) / a_n(Xi) → 1.
```

Consequently `J₂∈S₂`, `J₂∉S_{1,∞}`, and its logarithmically enhanced weak-trace residue is
`1/π`, exactly Xi's residue.

## Dependency-closed proof

1. For `x > 0`, `j₂(x) = (log x)²/(2πx)`. The function
   `log x · x^(-1/2)` is nonnegative and decreasing on `[exp 2,∞)`, so its square and the
   capped prime sequence are nonnegative and decreasing.
2. The diagonal approximation-number theorem therefore identifies the unsigned singular sequence
   exactly with capped `j₂(p_n)`. Passing to the signed two-sector operator duplicates every
   value, hence `a_n(J₂) = j₂(p_⌊n/2⌋)` exactly.
3. Since primes tend to infinity, the cap is eventually inactive. The prime number theorem gives
   `p_m/(m log m) → 1`, while `log p_m/log m → 1`. Substitution into
   `(log p_m)²/(2πp_m)` gives `log m/(2πm)`.
4. With `m=⌊n/2⌋`, one has `m/(n+1) → 1/2` and `log m/log(n+1) → 1`; signed
   multiplicity therefore changes `1/(2π)` to `1/π`. Thus
   `a_n(J₂)/(log(n+1)/(π(n+1))) → 1`.
5. Xi's ordered signed prime model has the same positive denominator asymptotic, so quotient
   calculus gives `a_n(J₂)/a_n(Xi) → 1`.
6. This quotient is globally bounded. Termwise domination by a fixed multiple of Xi and Xi's
   `S₂` membership imply `J₂∈S₂`. The normalized profile converges to `1/π`, so it is
   bounded and `J₂` belongs to the logarithmically enhanced weak-trace class. Multiplying that
   profile by `log(n+1) → ∞` proves `(n+1)a_n(J₂) → ∞`, excluding weak `S₁`.

## Hostile-audit result

- Cap affects finitely many primes only; no asymptotic constant is fitted there.
- Operator uses prime labels and a fixed second wild/Mellin derivative only; no Xi ordinate enters
  its definition.
- Factor `1/π` is forced by `1/(2π)` per prime and exact signed multiplicity two.
- Derivative order `k` produces the scale `(log p)^k/p ~ (log n)^(k-1)/n`; order one reaches only
  weak `S₁`, while order two is the first order reaching Xi's logarithmically enhanced density.
- Result identifies principal singular density and endpoint ideal only. It supplies no trace-class
  difference, determinant identity, zero-spectrum realization, or RH implication.

## Lean formalization

- Module: `GaloisForLFunctions.RHTower.RoutePSecondWildJetXiPrincipalDensity`.
- Capstone: `routeP_secondWildJet_xiPrincipalDensity`.
- Direct module check: passed with `lake env lean`.
- Umbrella import: wired into `GaloisForLFunctions.RHTower`.
- New-declaration axiom audit: every theorem depends only on `propext`, `Classical.choice`, and
  `Quot.sound`; no project axiom introduced.
- Deliberately skipped `lake build`: previous exact-target checks replayed 13,283 dependencies;
  direct source check is the targeted verification required here.

## Hostile audit targets

- Low-prime cap must be finite and disappear cofinally; no fitted Xi constants beyond universal
  Riemann--von Mangoldt normalization `1/(2π)`.
- Multiplier must come solely from prime labels and wild differentiation, not Xi ordinates.
- Approximation numbers must be exact, including signed multiplicity two.
- Matching principal density does not imply trace-class difference, determinant equality,
  self-adjoint realization of Xi zeros, or RH; those remain open.
- Need explain why derivative order one is insufficient and order two is minimal.

## References

- Andrea D'Agnolo, Marco Hien, Giovanni Morando, Claude Sabbah, *Topological computation of some
  Stokes phenomena on the affine line*, Ann. Inst. Fourier 70 (2020), 739--808.
- Andrea D'Agnolo and Masaki Kashiwara, *Riemann--Hilbert correspondence for holonomic
  D-modules*, Publ. Math. IHÉS 123 (2016), 69--197.
- Marco Bertola and Marco Cafasso, *Riemann--Hilbert approach to multi-time processes*, Appendix
  B on regularized Fredholm determinants.

## Log

- 2026-08-24 — corpus and primary-literature audit; minimal second-wild-jet conjecture fixed;
  moved to `1-in-progress`.
- 2026-08-24 — dependency-closed PNT proof and hostile audit complete; moved to
  `2-fully-proven`.
- 2026-08-24 — Lean formalization, direct module check, umbrella wiring, and new-declaration
  axiom audit complete; moved to `3-formalized`.
