# 20 — The DISC Dictionary: Window-Localized Sections and Their Discriminant Signs

**Register: SEARCH** (experiments pre-registered and archived:
`computations/DISC-RESULTS.md`; support-brick citations delegate-sourced — spot-check
before any promotion). Task #132, continuing doc 19 §5.

## 1. Objects

Carrier Ξ₁ = `xiDescent` (real entire, order 1/2; zeros: negative reals = on-line,
non-real conjugate pairs = off-line; square class ε = the bridge invariant, doc 19).
For real entire f(x) = Σ γ(m) x^m/m!, Jensen sections J^{d,n}(X) = Σ_j C(d,j) γ(n+j) Xʲ.
For squarefree real polynomials, sign(disc) = (−1)^{#non-real pairs} [KNOWN].

**Exact shift identity** (derivation trivial, recorded for reuse): if f = P·g with
P(x) = x² − 2ax + |τ|², then

> γ_f(m) = |τ|² γ_g(m) − 2a·m·γ_g(m−1) + m(m−1)·γ_g(m−2).

So multiplying the carrier by one zero pair acts on Jensen data as a three-term
operator mixing shifts n, n−1, n−2 with polynomial weights — the section family is
closed under adding/removing zero pairs.

## 2. What the experiments established (all pre-registered; DISC-RESULTS.md)

Model: g = cos(√x) ∈ LP, witness = g × one simple non-real pair, control = g × real
pair at identical scale.

1. **No spurious pairs, ever** (runs 1–3): section pair-count never exceeded the true
   local count; controls were hyperbolic throughout. The (SPUR) mechanism is clean in
   the model.
2. **The global shift index n does NOT localize** (run 2, prediction P4 FAILED —
   load-bearing): pairs at zero-index ≥ 2 are invisible for all d ≤ 40, n ≤ 24.
   Scale analysis (C(d,j)/dʲ ≈ e^{−j²/2d}/j!): global visibility costs d ≳ c·x_pair.
   For ζ that would be section degree ~ T² per window — prohibitive, and consistent
   with Pólya–Wiman forgetting (large n absorbs pairs rather than revealing them).
3. **Recentering IS localization** (run 3): expanding the carrier at x₀ near the pair
   (pair at h = ±8i) makes the pair visible at EVERY degree d ≥ 4 with shift n ≤ 1,
   count exactly 1, while the matched real-pair control reads 0 everywhere. A
   degree-4 recentered section already reads the local square class exactly.

> **(DISC dictionary, calibrated)** A line-centered window of ζ at height T
> corresponds NOT to a shift-n global Jensen section but to the **recentered
> sections**: expand Ξ₁ at u₀ = −T² (a slit point — Ξ₁ is real-analytic there, so
> the section coefficients are REAL), take low degree d and shift n ≤ 1. The
> coefficients Ξ₁^{(m)}(−T²) are exactly the jet of the Hardy Z-data at the window
> center. **The candidate finite reader of N(W) mod 2 is the discriminant sign of a
> low-degree polynomial in the Z-jet at T.**

FE and reality make the jet real (the carrier exists — doc 19 layering); Euler enters
through the VALUES of the jet (Z^{(j)}(T) are Riemann–Siegel/explicit-formula
computable arithmetic data). The R9 jet census (doc 16 §7) measured exactly these
objects — the lane's threads converge.

## 3. Position against the known corpus [delegate-sourced, to spot-check at promotion]

- f ∈ LP ⟺ all Jensen sections hyperbolic: Craven–Csordas 1989 (after Jensen/Pólya).
- Pólya–Wiman (derivatives of LP* eventually in LP): Craven–Csordas–Smith 1987; Kim
  1990; Ki–Kim 2000. Derivatives only — **no published theorem gives the
  2k-exactness of Jensen sections for LP* functions** (our (SPUR) statement is open
  ground). Nearest bound: Kim–Lee 2022 — non-real zeros of J^{d,n} are O(d^{c/2}) in
  a strip.
- Discriminant signs appear in the literature ONLY at d = 3: disc(J^{3,n}) ≥ 0 is the
  "higher-order Turán inequality," proved for ξ by Dimitrov–Lucas 2011 (global
  center, i.e. our u₀ = 0 case). **The general-d and — decisively — the
  window-RECENTERED disc-sign program does not appear.** Novelty gate: the
  recentered dictionary came from run 2's failure, not from any search. Passes.

## 4. The theorems the dictionary now demands

- **(SPUR-R) [OPEN, the section stability theorem]:** for real entire g of genus 0
  with only real zeros and P a real quadratic with non-real roots at distance r from
  x₀, the recentered sections J^{d,n}_{(Pg)(x₀+·)} have exactly one non-real pair for
  d ≥ d₀(r/spacing), n ≤ 1 — and (control direction) zero pairs when P has real
  roots. Proof route: Hurwitz on J^d(z/d) → f(x₀+z) plus a real-rootedness stability
  argument for the far roots; Kim–Lee's strip bound as the containment brick.
- **(DISC-ζ) [CONJECTURE, the bridge instance]:** for every T and suitable
  (d ≤ d₀, n ≤ 1), sign disc of the recentered Z-jet section at T equals
  (−1)^{N(W_T)} — in particular positive for all T ⟺ (WR_1) on the covered windows.
- Foil prediction [falsifiable]: at the certified D–H off-line zero (box 84,
  t ≈ 85.7), the recentered D–H jet section of low degree has disc < 0. This is a
  finite computation on the pod; it would be the first *measured* nonvanishing
  square class.

## 5. Next

(SPUR-R) is a self-contained classical-analysis theorem with a clear route — card
it. The D–H foil computation is the decisive falsifier for (DISC-ζ)'s shape. And the
residue/germ coordinate (#133) should now be read against the jet reader: both are
finite window data; the germ gives the arithmetic side, the jet the analytic side.
