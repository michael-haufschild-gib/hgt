# Full Hecke growth countermodel without global automorphy

Frozen goal RP for actual normalized level-one Hecke-Maass cusp forms remains unproved and unfalsified. Own card/facts remain `docs/drafts/pipeline/1-in-progress/ramanujan-petersson-maass-2026-09-26{,-facts}.md`. Previous rigidity/import work: `mem:ramanujan/maass-dilation-rigidity-and-hecke-imports-2026-09-26`.

## Kernel-checked positive survivor
New module `formal/GaloisForLFunctions/RHTower/EisensteinTailSpectrum.lean`, namespace ROOT `RHTower.EisensteinTailSpectrum`, wired into RHTower umbrella.

`tail u x y` is the actual positive-frequency Fourier-Bessel series with coefficient `n^u * sum_(d|n) d^(-2u)` and factor `exp(2*pi*i*n*x)*sqrt(y)*K_u(2*pi*n*y)`. For real u:
- `tail_re_pos`: strictly positive real part at x=0, every y>0; summability and real Bessel positivity prevent a totalized nonsummable-series artifact.
- `tail_periodic`, `tail_mean_zero`, `tail_rapid_decay`: one-periodic, zero mean on each positive-height period, fixed-x decay under every complex power weight.
- `tail_norm_le_exp`, `tail_zero_at_im_infty`: uniform-in-x exponential bound and actual UpperHalfPlane.IsZeroAtImInfty. Not merely fixed-line decay.
- `tail_laplace_equation`: actual iterated real-coordinate derivatives satisfy -y^2*(F_xx+F_yy)=(1/4-u^2)*F.
- `hecke_tail`: complete existing normalized RHTower.heckeOp, including residue branch, has eigenvalue `eigenvalue p u = p^u+p^(-u)` for every prime.
- `eigenvalue_gt_two` for u>0; `hecke_iterate_tail` gives exact mu^k growth; `hecke_iterate_div_pow_tendsto_atTop` proves norm(T_p^k F(0,1))/r^k tends to infinity for every positive r<mu.
- `exists_mean_zero_rapid_decay_supercritical_hecke_family` is CLOSED with no theorem parameters, at u=1/4: nonzero periodic mean-zero uniformly cusp-decaying function, local Laplace eigenvalue 3/16, all prime Hecke eigenvalues >2, and growth normalized by 2^k diverges.

This refutes a sufficient-condition shortcut OMITTING GLOBAL AUTOMORPHY. It is NOT a Maass counterexample, NOT an eigenvalue-exponent improvement, and NOT a bound for actual automorphic sources. No actual Maass-form identification is supplied. Do not expand this countermodel lane as a substitute for the missing quantitative global argument.

Separate `symmetric_tail_inversion_defect` identifies two-sign tail defect with minus constant-part defect for Re(u)>1/2, using actual full Eisenstein inversion. This is a different source and parameter sector from the one-sign u=1/4 witness; do NOT claim its defect formula applies to that witness.

## Verification and optimization
- Scratch `lake env lean /tmp/rp_tail_countermodel_20260926d.lean` passed.
- Uniform cusp proof initially hit default 200000 heartbeats. Explicit uniform-bound lemma plus typed eventual inequality fixed elaboration without raising any limit.
- Targeted `LEAN_NUM_THREADS=1 lake build GaloisForLFunctions.RHTower.EisensteinTailSpectrum` passed, rebuilding stale required dependencies serially; 12484 dependency jobs. After one EOF-whitespace correction, exact-final-source targeted build passed again using cache. Logs `/tmp/rp_tail_spectrum{,_final}_build_20260926d.log`. Leaf reported 5.5s then45s; NOT controlled benchmarks.
- `/tmp/rp_tail_axioms_20260926d.lean` passed against installed oleans. All14 public theorems only use propext/Classical.choice/Quot.sound. Main existential signature and general growth/defect signatures printed and inspected.
- No proof holes, new mathematical axioms, numeric evaluation commands, resource overrides, full/umbrella builds, or commits. Global index regenerated; final lint diagnostics live in `/tmp/rp_tail_final_lint_20260926d.log` and card. No global clean-lint claim.

## Source checks that changed next action
SarnakXueCounting.card_le counts determinant-one congruence matrices, not determinant-prime-power Hecke correspondences. KloostermanZeta establishes absolute convergence only for sigma>3/4. Petersson-Kloosterman gives Poincare pairings, not the required individual finite-place bound. Inspected global collision envelopes retain response-energy costs.

Four deep/method searches `/tmp/rp_{power_amplification,modulus_cancellation,tail_countermodel,inversion_boundary}_20260926d.json`; first reported complete retrieval, remaining3 partial. Compiler coverage predominantly source-only. Retained source proofs inspected; no exhaustive absence claim.

Next discriminating target remains actual full-Hecke-power or cancellation control using global modular constraints. Local PDE, zero Fourier mean, uniform cusp decay, and exact arithmetic eigen-equations by themselves have now been ruled out as sufficient.