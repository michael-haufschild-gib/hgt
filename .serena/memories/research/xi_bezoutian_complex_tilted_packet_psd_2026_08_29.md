# BZ-2: complex-tilted packet PSD of the Bezoutian RH criterion — LEAN-PROVED (2026-08-29)

Card: `docs/drafts/pipeline/1-in-progress/xi-bezoutian-complex-tilted-packet-positivity.md`.
Modules (umbrella-wired, `lake build` 10906 jobs, all audited theorems on
propext/Classical.choice/Quot.sound):
- `formal/GaloisForLFunctions/RHTower/XiRayComplexTiltedTransforms.lean` (moments + tilt
  perturbation + off-ray L-bounds, 1027 lines)
- `formal/GaloisForLFunctions/RHTower/XiBezoutianComplexTiltedPacketPosSemidef.lean`
  (Hermitian Gershgorin + capstones, ~670 lines)

## The theorems

Budget `xiRayTiltBudget b = 1/(32(log b + 3))`. For every W : ℕ → ℂ with
Re W_0 ≥ R₀ = xiRayPacketBase, Re W_{m+1} ≥ R₀²·Re W_m, |Im W_m| ≤ budget(Re W_m), every n:
`posSemidef_criticalLogDerivKernel_tiltedPacket` and
`posSemidef_thetaTailFirstMomentBezoutian_tiltedPacket` (+ `_nodes` endpoint shape).
First unconditional MULTI-NODE COMPLEX stratum of
`riemannHypothesis_iff_posSemidef_thetaTailFirstMomentBezoutian`. Supporting new layer:
- `xiRayLaplaceAbsMoment_le` (N_abs ≤ (X+3)Z), `xiRayLaplaceSecondMoment_le`
  (M₂ ≤ (X+3)²Z), `thetaEnvelopeUpper_le_xiRayLaplace` (C_u ≤ Z on the packet ray).
- Tilt perturbation: ‖Z(b+it)−Z(b)‖ ≤ |t|N_abs, ‖N(b+it)−N(b)‖ ≤ |t|M₂ via
  ‖e^{iθ}−1‖ ≤ |θ| (2−2cos ≤ θ², `Real.one_sub_sq_div_two_le_cos`).
- Off-ray: `re_logDeriv_xiCent_tilted_ge` ((log b)/16 ≤ Re L(b+it)),
  `norm_logDeriv_xiCent_tilted_le` (‖L‖ ≤ 4 log b) — 31/32–33/32 sandwich +
  `Complex.div_re`; constants close at (92X−96)/1090 ≥ X/16 for X ≥ 5.
- `xiRayPacketBase_ge'` (9216 ≤ R₀, public-input rederivation).
- Refactors: module 2 now exposes `xiRayLog_div_self_contraction` and
  `natDist_geom_row_sum_le`; module 1 exposes moment/mass_reflected_le and the even splits.

## Proof shape (reusable)

Perturbation of BZ-1 around the real ray: budget ⟹ |ΔZ| ≤ Z/32, |ΔN| ≤ (X+3)Z/32 ⟹
diagonal K₀(W,W) = Re L(W)/Re W (real! via Complex.add_conj) ≥ log β/(16β);
off-diag ‖K₀‖ ≤ 8 log β_k/β_k (‖W_j+conj W_k‖ ≥ Re-sum); contraction gives
‖K₀‖ ≤ 128(2/R₀)^d√(D_jD_k); Hermitian Gershgorin: Im E = 0 by conj-pairing
(criticalLogDerivKernel_conj_symm — corpus, hypothesis-free), Re E via Re z ≥ −‖z‖ and the
b_j = ‖c_j‖√D_j scaling; threshold 256q ≤ 1−q at q = 2/R₀ ≤ 1/513 (needs R₀ ≥ 1026 ⟸ 9216).
Bezoutian transfer: congruence vector y_j = conj(ξ(W_j))·c_j.

## Lean traps (new)

- Fin/ℕ elaboration: lambdas `fun k => ... (k:ℕ) ...` infer k : ℕ — annotate `fun k : Fin n`
  in Finset.sum_le_sum's f/g and in scaled vectors `fun j : Fin n => ... * cv j`.
- `Finset.add_sum_erase` over Fin sums of `g ↑k` needs the function given explicitly
  (`fun k : Fin n => g (k:ℕ)`), else unification fails.
- Un-beta'd pointwise goals also appear under `MeasureTheory.integral_mono` — `dsimp only`
  after `intro x` fixes rw/norm_mul failures.
- `div_eq_div_iff` takes ≠0 args now; for a/b = c*d shapes use `div_eq_iff` + ring.
- exp-square: `rw [pow_two, ← Real.exp_add, two_mul]` — deterministic, avoids the
  norm_num/ring_nf no-goals dance of `← Real.exp_nat_mul`.
- Fixed-rate corpus integrability (`integrable_pow_mul_exp_mul_thetaCuspFullSource` is rate
  e^x only) — build tilted majorants from `integrable_exp_abs_mul_thetaCuspFullSource` with
  x² ≤ 4e^{|x|}.
- Concurrent agents' builds DELETE shared oleans mid-flight — when `lake env lean` reports a
  missing olean for an unchanged module, run `lake build +target` (restores) and continue.

## Open next

Widen the budget (binding term |t|M₂; second-order oscillation should give ~1/√log or
const); mixed real/tilted packets; deep-complex regime (|Im| ~ zero heights — needs |Z(W)|
lower bounds through Γ-decay; separate programme). Siblings:
`research/xi_bezoutian_real_packet_psd_2026_08_29`,
`research/theta_kernel_cp1_separated_packets_2026_08_29`.
