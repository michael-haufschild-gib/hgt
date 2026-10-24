# Transport in aperture as a renormalization flow: the shell-flux law of the ground energy

- **ID:** `aperture-rg-flow-shell-flux-2026-10-24`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) → THEOREM (Lean)
- **Source:** `docs/reports/review-2410/fable.md` §2.3 opening D (AOT, ACCE, ACT); ACT README open
  problem 7, ACCE README open problem 6, AOT README open problem 7.
- **Statement:** the restricted Weil ground energy `μ(A)` is an exact renormalization flow: its
  jump between two apertures is the shell flux of the smaller ground state paired with the larger
  one, the flux never vanishes, the flow is strictly decreasing and crosses zero at most once, and
  its arithmetic part is the cross-collar correlation of the primes with `log n` in the shell
  `(2a, 2b]`.

## Goal
Opening D asks for (i) the beta function of `A ↦ μ(A)` as a boundary-shell flux, (ii) a
sign-definite jump, (iii) the Class III nature of the beta function (Beurling-type perturbations
cross zero), (iv) the relative form of any flux law compatible with the doubly exponential ceiling,
and (v) the first rung (a graded flux law gives a zero-free strip). The corpus had the gauge-level
identity for a fixed test and the telescoping of jumps, but no identity for `μ` itself
(ACT OP7: "the aperture face has none").

## Results (paper level)
Let `F` be any aperture-compatible remainder family (`CCMRemainderFamily`: ζ, prime-deleted,
prime-inserted, countably perturbed, prime-free), `form_a` its sesquilinear form on the form domain
`D_a`, `μ(a)` its ground energy, `u_a` a normalized ground form state, and for `a ≤ b`
`Φ_{a,b}(v) = form_b(ext u_a, v) − μ(a)⟨J ext u_a, J v⟩` on `D_b`.

1. **Euler–Lagrange for every family.** `form_a(u_a, w) = μ(a)⟨Ju_a, Jw⟩` for all `w ∈ D_a`
   (nonnegative Hermitian shifted form vanishing on its diagonal at `u_a`).
2. **Polarized aperture compatibility.** `form_b(ext x, ext y) = form_a(x, y)`.
3. **Shell support.** `Φ_{a,b}(ext w) = 0` for all `w ∈ D_a`: the flux functional lives on the shell.
4. **Flux law (the beta function).** `(μ(b) − μ(a)) ⟨J u_b, J ext u_a⟩ = conj Φ_{a,b}(u_b)`.
5. **Sign-definite jump.** `μ(a) − μ(b) = Re h_b(ext u_a − c u_b)` for every `c ∈ ℂ`, where
   `h_b = form_b − μ(b)⟨J·,J·⟩ ≥ 0`; equality `μ(a) = μ(b)` iff `ext u_a` is a ground state at `b`.
6. **No non-radiating eigenvector (literal ζ).** For `a < b`, no nonzero `v ∈ D_a` has `ext v` as a
   form eigenvector at `b`. Proof: the full literal form is translation invariant (the two polar
   characters `e^{∓h/2}` cancel in the polar product); small translates of `v` would all be
   eigenvectors at an intermediate aperture with the same eigenvalue, but the eigenspace is
   `ker(1 − K)` with `K` the compact Birman–Schwinger pencil, finite-dimensional, while distinct
   equally spaced `L²` translates are independent.
7. **Strict flow.** Hence `μ` is strictly antitone; every shell flux `Φ_{a,b}` (`a < b`) is nonzero;
   RH iff `μ(A) > 0` at every aperture; off RH the contact aperture is the unique zero of `μ`.
8. **Prime-shell beta function.** For the literal family write `Q_b = Q_b^{[a]} − σ_{a,b}`, where
   `Q^{[a]}` freezes the primes at `n ≤ e^{2a}` and `σ_{a,b}(f) = Σ_{e^{2a} < n ≤ e^{2b}}
   Λ(n) n^{−1/2} · 2 Re⟨T_{log n} f, f⟩` (Fable's "primes with `log p` in the shell"). The frozen
   family is aperture compatible, agrees with `μ` at `a`, and
   `σ_{a,b}(u_b) ≥ μ^{[a]}(b) − μ(b) ≥ σ_{a,b}(u^{[a]}_b)`: the flow step is a geometric step
   (frozen primes) plus an arithmetic step sandwiched between the shell prime correlations of the
   two ground states. Each shell term reads only the two collars `[−b, b − 2a]`, `[2a − b, b]`.
9. **Class III and the relative law.** Every one-prime perturbation of ζ crosses zero
   (`exists_inserted_zero_crossing_of_ne_zero`), so no flux bound shared with a perturbed family
   is true; a law `μ(b) ≥ e^{−C(b−a)} μ(a)` is refuted by the ceiling; the ceiling-compatible
   relative law is equivalent to RH; the graded law gives `zetaZeroWidth ≤ σ`, i.e. `Θ ≤ ½ + σ`.

## What remains open
The Class III estimate itself: a bound on the shell flux of the actual ground state, relative to
`μ`, from an input that does not presuppose the floor. By 9 it is RH (relative law) or quasi-RH
(graded law); nothing here proves it.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [ ] 1 → 2  fully-proven: complete paper proof, no open dependency
- [ ] 2 → 3  formalized: Lean theorems, file checks green, axiom audit PASS
- [ ] 3 → 4  publication-ready

## Lean plan
`formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/`:
`TheApertureFlowIsAShellFlux.lean` (items 1–5), `TheApertureFlowNeverStalls.lean` (items 6–7),
`ThePrimeShellBetaFunction.lean` (items 8–9).

## Log
- 2026-10-24 — created; results 1–9 proved on paper.
