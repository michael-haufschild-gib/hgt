# CYCLE 11: the all-k sector-stability conjecture is FALSE (2026-08-06)

Card: `squarefree-gibbs-parity-vortex.md` (cycle-11 section).
Lean: `formal/GaloisForLFunctions/RHTower/GibbsTruncationSection.lean`, wired, built,
no sorry, axioms clean.

## THE FALSIFICATION (stop pursuing all-k stability / TSP)
Counterexample family: S = k primes in [N,2N], x = N^{−(J+1/2)}, J = 6, k and N large.
- Z1 (Lean, `gibbsDiagC_sub_truncated_le`): light/heavy dichotomy at level J ⟹
  ‖P_S(z,x) − Σ_{j≤J}C(k,j)z^j‖ ≤ (ε + e^{−R})(1+‖z‖)^k.
- Z2: with that choice ε = 2^J N^{−1/2} → 0, R = N^{1/2} → ∞; substituting z = w/k and
  k → ∞ gives C(k,j)/k^j → 1/j!, i.e. the J-th Taylor section s_J(w) of exp. Tail harmless
  on |z| ≍ J/k where (1+‖z‖)^k = O(e^J).
- Z3 (Lean): q = 6!·s₆ = w⁶+6w⁵+30w⁴+120w³+360w²+720w+720 has
  (a) NO imaginary-axis zero: Im q(iy) = 6y((y²−10)²+20), and q(0) = 720;
  (b) third Hurwitz determinant det[6,120,720; 1,30,360; 0,6,120] = −1440 < 0.
  With classical Routh–Hurwitz NECESSITY (Hurwitz 1895 — cited, NOT assumed in Lean),
  s₆ has a zero with Re w > 0. Independent check: even part of q(iy) in u = y² is
  u³−30u²+360u−720 with derivative 3(u²−20u+120) > 0 ⟹ strictly increasing ⟹ ONE positive
  root, but stability of a degree-6 real polynomial needs three. Szegő's theorem is the
  asymptotic reason (zeros of s_n(nz) accumulate on |ze^{1−z}|=1, which meets Re z > 0).
- Z4: hence the gas has a zero with Re z > 0. Sector stability FAILS.

## Consequences for the programme
- Parity cancellation is NOT monotonically graded by the zeros: some zeros give
  ‖1+ζ‖/‖1−ζ‖ > 1 (anti-cancellation).
- Cycles 3–9 results are sharp in scope: k ≤ 4 all couplings; all k at weak coupling
  (x·σ(m) < 1). The cycle-8 TWO-SCALE POSITIVITY (TSP), being sufficient for stability,
  must fail in general — the engine cannot be completed. CLOSE that line.
- What survives as load-bearing: the CONDENSATION LAW (cycle 10,
  `gibbs_parity_cross_ratio`) — an identity at every coupling, independent of zero
  locations.

## Lean trap
`mul_le_mul_of_nonneg_left h (by positivity)`: the multiplier is a metavariable at
elaboration, and positivity can unify it with the WRONG hypothesis in context (here
hx : 0 ≤ x). Bind it with an explicit `have hzc : 0 ≤ ...` and use a `calc`.
