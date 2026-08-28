# Index/parity near-miss programme — after PF test + attack-A first assault (2026-08-28)

Card: `1-in-progress/index-parity-near-miss-rigidity.md` (complete detail). Hub:
`source-contraction-two-volterra-domination` cycles 7–8+. Scripts:
`computations/2026-08-28-two-volterra-domination-loop/pf_test.py`, `pf_check.py`.

## Headline state
κ_T = N_off(T) (two negative squares per off-line quadruple; model-quartic verified).
**C8: κ ∈ {0,∞}** — near-miss rigidity, weaker than RH, absent from refereed literature; the
κ=2 analytic counterfeit `Ξ·(τ²−ρ²)(τ²−ρ̄²)/((τ²−γ₁²)(τ²−γ₂²))` forces any proof to use the
Euler orbit. C9 (FF/Perron–Frobenius weld) RETIRED by the executed two-atom test: witness =
anti-Perron point at critical cone weight (exact; three finite-section regimes measured; m-fold
soft space = discretized zero lattice), but cone bounds give only the trivial region, zeta's
operative cone is Λ≥0+341 (classical), and the **Bohr-denseness no-go** kills all fixed-weight
spectral-membership frames (inf|ζ|=0 on every strip line ⟹ 0 ∈ σ unconditionally). Surviving
receiver: RH ⟺ weight-indexed WH Fredholm index constant on (0,1/2); finite jumps ⟺ C8.

## Lean landed for this programme (unconditional; axioms standard)
- `HTGeometry/HerglotzPoleIndexAnchor.lean`: `re_one_div_sub`, `re_one_div_sub_neg_iff` (RHP
  pole ⟹ negative rank-one Carathéodory diagonal left of its abscissa), `re_lhpPoleSum_nonneg`,
  `isPSDKernel_lhpPoleSum` (stable poles ⟹ zero negative squares) — the generic κ = N_off
  anchors, assembled on `isPSDKernel_halfPlaneCaratheodory`.
- `RHTower/ThetaTailKreinTiltSectionAnchor.lean`: sesquilinear section identity
  `2c(w+conj v)·B = tiltGram-difference`; `tiltGram_param_uniform` (section inertia is
  tilt-parameter-free).
- `HTGeometry/CosineSublevelPeriodMeasure.lean`: `cos_sublevel_period_eq` +
  `volume_cos_sublevel_period` — {cos ≤ −1/2} is exactly the middle third (2π/3 per period):
  the κ=1 Bohr-negativity measure core.

## Attack A — state after first assault
Anomaly law (paper-exact, unconditional inputs only): finite κ ⟹
`(ψ(e^u)−e^u)e^{−βu} = A(u) + E(u)`, A the exact κ-frequency Bohr polynomial,
density{|E|>δ} → 0 (explicit formula + Σ1/|ρ|² + windowed Chebyshev). **C10 (minimal target):
the normalized prime fluctuation does not converge in density to a nonzero finite Bohr
polynomial** — C10 ⟸ any unconditional one-sided carrier bound at density > 2/3 (κ=1;
> 1−1/(8κ) general via the L²/L∞ lemma: density ≥ 1/(8κ) at depth ‖A‖₂/(4√(2κ))); C10 ⟹ C8.
Carrier failure map (audited): ψ-direct = RH-strength; quadratic = blind; Λ≥0-monotonicity =
main-term-dominated (kills only β=1 — the classical mechanism); S(T) insensitive; Littlewood
line-means non-discriminating (keep receiver: ∫₀^T log|ζ(σ₀+it)| = O(1) ⟺ finitely many zeros
right of σ₀); Odlyzko budgets spent by on-line zeros.
**Landing:** the missing piece = unconditional positive-density one-sided prime bound at
sub-main scale vs a FIXED frequency — exactly the T2-subhalf / E-supply / D2-window frontier,
with a new consumer relation (their PARTIAL goals suffice for C8) and the extra resource of
Diophantine window tuning to the known frequency. Next: mine proved T2/E layers for any
statement meeting the spec.

## Do-not-revisit (extended)
Shift-orbit amplification; abstract Toeplitz/Smirnov 0-or-∞; Pontryagin symmetry-compression;
det-sign mod 2; C9 PF-invertibility weld; fixed-weight spectral membership (Bohr no-go);
ψ-direct one-sided bounds; quadratic carriers; monotonicity beyond β=1; S(T); line-means;
positive-test budgets.

## Queued
Periodized κ=1 density statement; general-κ negativity lemma; E(u)-density-vanishing as formal
brick; the κ=2 counterfeit formal object; Littlewood discriminator receiver; section-index
nesting export.
