# 58 — Attacking (K-bdd): the Esseen Interface, the Degree-2 Wall, and the Ergodic×Transfer Split

**Register: SEARCH** (task board #5; the open kernel of doc 56 §5, now the sole
open input of Route B to (CR-density)). Everything below is labelled; §2's
no-go is proof-sketch grade, §4's split is the proposed mechanism.

Target: **(K-bdd)** — for P = F_N·M_y (BV taper, y = N^θ), fixed r ∈ (0, 1/2]:
meas{t ∈ [T, T+U] : |P(1/2+it)| ≤ r} ≤ C_θ·r²·U, matched N ≍ √(T/2π), U ≍ T.
Measured (doc 56 §9): true with C ≈ 0.5, density flat ≈ 0.1, N-stable.

## 1. The Esseen interface [KNOWN-shape; the precise reduction]

Let ψ_r be a smooth bump ≥ 1_{D(0,r)}, supported in D(0, 2r). Then
meas{|P| ≤ r} ≤ ∫ ψ_r(P(1/2+it)) dt, and by 2D Fourier inversion the right side
is r²·∫_{ℝ²} ψ̂(rλ)·φ_P(λ) dλ with φ_P(λ) := (1/U)∫ e^{i Re(λ̄ P(1/2+it))} dt.
Since ∫|ψ̂(rλ)|r²dλ = O(1) over |λ| ≤ Λ/r and ψ̂ decays fast:

> (K-bdd) ⟸ **(CHAR-decay):** |φ_P(λ)| ≤ C·e^{−c|λ|²} + err(N) for |λ| ≤ Λ(r),
> with Λ(r) = O(1/r) FIXED as N → ∞, err(N) → 0.

Fixed r means fixed λ-range: no shrinking scales, no large deviations —
Berry–Esseen grade, not chaos grade. (The Lean smoothing bricks already exist:
`Bottcher/Brolin/WeylLemma.lean`'s ContDiffBump/convolution layer.)

## 2. The degree-2 wall [no-go, proof-sketch — recorded so nobody re-walks]

Expanding e^{iRe(λ̄P)} in powers and t-averaging term by term: degree-D
monomials are frequencies log A with A ≤ (Ny)^D = N^{(1+θ)D}; distinct integer
products separate only by |log(A/B)| ≥ 1/max(A,B), so the MV off-diagonal
error is ≫ N^{(1+θ)D}/U = N^{(1+θ)D−2}. The expansion is controlled only for
D < 2/(1+θ) < 2 — **for every θ > 0 and every window U ≤ T, the matched
regime blocks all moment expansions strictly below degree 2.** The N² = T
threshold is the same seam every object in this lane hits (doc 50 §7, doc 55
§6.3): squares of the polynomial exactly fill the window. No naive Fourier
route crosses it; (CHAR-decay) needs structure, not expansion.

## 3. Attack-as-false, updated

An atom of P near 0 with mass ≫ r² requires positive-density near-clusters of
F_N zeros at the line — refuted-shaped by three independent measurements
(doc 55 §2 saturation; doc 56 §9 flat Q/r²; the census's 1/900 survivor
sparsity). Further, the GAF σ-profile (doc 55 §6.2) predicts the density near
0 quantitatively and matches. (K-bdd) is TRUE-shaped from every side; the task
is mechanism.

## 4. The proposed mechanism: ergodic × transfer split [CONJECTURE, the program]

Split the Kronecker orbit average against the Bohr-lift Haar average:

**(K-bdd-∞) [ergodic half — attackable now].** In the Steinhaus random model
(X_p independent uniform phases, G_∞ = Σ c_m m^{−1/2}·Π X_p^{a_p(m)}), the law
of P_∞ = 1 + G_∞ has bounded 2D density near 0.
*Proposed proof (two-phase co-area + scale induction):* condition on all
phases except two active primes p, q ∈ (y, N]. P_∞ is a bilinear trig
polynomial in (X_p, X_q) with coefficients A_p, A_q, A_{pq}, A_∅ from the
conditioned field. Where the fiber map (θ_p, θ_q) ↦ P_∞ is a submersion
(gradient bounded below), the co-area formula gives fiber-density ≤
C/|gradient|²; the degenerate event {|A_p|, |A_q| both small for ALL available
(p,q)} is a simultaneous smallness of ~π(N)-many conditioned coefficients —
itself an anti-concentration event for the one-scale-down field (the A_p are
mollified sums over the remaining primes). Induct on dyadic prime scales
y_0 = O(1) ⊂ … ⊂ y_k = N; the base case is a FIXED torus dimension where
effective equidistribution is classical — and Baker's theorem on linear forms
in logarithms of the primes gives the effective irrationality the base needs.
(The Baker floor, which every hgt search lane hit as a wall, enters here FOR
the proof — the {σ_p}-side arithmetic doing constructive work.)

**(TRANSFER) [the genuinely open half — now precisely typed].** The window
average of the FIXED smooth functional ψ_r(P(1/2+it)) equals the ergodic
average up to o(1). On the torus-Fourier side: monomial frequencies
Π p^{n_p} of total height Σ|n_p| log p ≤ log U transfer EXACTLY at
pair-correlation/MV level; what remains is:

> **(SPEC-decay):** the torus-Fourier mass of ψ_r(P_∞) above height U is o(1) —
> a spectral-smoothness statement about a fixed functional of the RANDOM
> model, computable there, with no window in it.

This is the correct residue of the old (M2) question: the a.p.-category no-go
(11 Thm B) killed coarse transfer of ASYMPTOTIC data; a fixed localized smooth
functional with quantitative spectral decay is the case that no-go does not
touch. If (SPEC-decay) holds with any rate, (TRANSFER) closes at MV level and
(K-bdd) = (K-bdd-∞) × (TRANSFER) follows.

**Fallback mechanisms recorded:** (i) Harper-style dyadic-prime-block
conditioning transplanted to the mollified sum (the machinery that proved
better-than-√ cancellation at exactly these window/length scales — here it
would be run on a SUBcritical object, i.e. downhill); (ii) van der Corput
differencing of φ_P itself (|φ|² = E_τ φ_{P_τ} with the differenced field's
correlation decay as input) — both live, both heavier than §4.

## 5. Numerical pre-registrations for the split (queued, NOT run)

- (P4) Two-phase submersion margin: sample the conditioned coefficients A_p at
  random t; register: P(max_p |A_p| < ε·rms) ≤ C·ε⁴ (two-prime degeneracy is
  codim-4). Tests the induction's engine.
- (P5) Spectral decay: estimate the autocorrelation
  (1/U)∫ ψ_r(P(t))·ψ_r(P(t+τ)) dt against the random-model prediction as a
  proxy for (SPEC-decay); register: relative deviation ≤ 10% for τ ∈ [1, 100].

## 6. What this opens

1. (K-bdd-∞) is a self-contained theorem target with a complete proposed
   proof skeleton — write it out as its own card; its ingredients (co-area,
   conditioning, Baker base case) are all classical technology assembled in a
   new place. If it lands, Route B's open core shrinks to (SPEC-decay).
2. (SPEC-decay) is a random-model computation — no matched window, no zeros.
   It may follow from hypercontractivity of the Steinhaus semigroup on the
   polynomial chaos (the functional is smooth and localized) — check the
   Boolean/Steinhaus analysis literature for exactly this decay [method
   research, sanctioned].
3. The Baker entry point (§4) is the first place in the MWM lane where the
   {σ_p}-side transcendence toolbox does constructive work inside the RH
   bridge — the weld metaphor made literal. If the pattern holds, effective
   linear-forms bounds are the generic base-case engine for finite-window
   equidistribution throughout the lane.
