# Cycle 14: distant zeros inert; dictionary closed; refined conjecture downgraded

Card: `squarefree-gibbs-parity-vortex.md` (cycle-14).
Lean: `formal/GaloisForLFunctions/RHTower/GibbsZeroLocalization.lean`, wired, built,
no sorry, axioms clean.

## U1 (Lean)
‖1−ζ‖ ≤ 2 + ‖1+ζ‖ ⟹ a zero at distance d from −1 contributes cross-ratio ≤ 1 + 2/d:
DISTANT ZEROS ARE INERT. Division-free:
  ‖Z_S(x)‖·∏_ζ‖1+ζ‖ ≤ ‖J_S(x)‖·∏_ζ(2+‖1+ζ‖)     (`gibbs_partition_le_current_mul_localization`)

## The closed dictionary (all unconditional, every coupling, NO stability needed)
  gap δ around −1     ⟹ ‖J_S‖ ≥ e^{−xm}δ^{|S|}                (T1, cycle 13)
  ‖J_S‖ small         ⟹ a zero within δ of −1                  (T2, cycle 13)
  zeros far from −1   ⟹ no cancellation (≤ 1+2/d each)         (U1, cycle 14)
  zeros confined to ρ ⟹ cancellation ≤ (ρ/(2−ρ))^{|S|}         (cycle 10)

## PREDICTION: the refined conjecture (cycle 12) is LIKELY FALSE — do not chase it
Natural gas profile: A_j ≈ Z·λ^j/j! (λ = loglog(1/x)) persists in large-deviation form up
to j ≈ K where P_K x ≈ 1 (P_K = primorial); beyond K it drops super-exponentially (minimum
energy takes over). That is Poisson with a SHARP cutoff = Z e^{−λ}s_K(λz) — the Szegő
shape. s_K has RHP zeros for K ≥ 6, and K ≥ 6 already at x ≤ 1/30030. So the natural gas is
probably unstable too.
OBSTRUCTION TO PROVING IT (named, not a gap in the gas theory): needs Sathe–Selberg
counting uniform in j up to j = K ≈ log(1/x)/loglog(1/x), far outside the usual j ≍ loglog
range.
**Programme conclusion: stability is not the right structure. The two-sided condensation
law is, and it requires no stability.**

## Repo hygiene (IMPORTANT)
Several concurrent sessions write to this tree (HTGeometry umbrella churn, a 2-fully-proven
card, RHTower/DivisorReesDehomogenization.lean). `pgrep -f "lean --"` matches THEIR shell
command text and gives false "stale process" hits. Use
`ps -Ao comm | grep -E "/lean$|/lake$"` instead. Never kill processes you did not start.
