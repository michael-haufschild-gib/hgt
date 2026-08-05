# Littlewood L3 built: KuzminLandau.lean (2026-08-05)

Card: `littlewood-zero-free-region.md` (L1 ✓ L2 ✓ L3 ✓).

`RHTower/Sieve/KuzminLandau.lean` — wired, build 3272 jobs, axioms only
propext/Classical.choice/Quot.sound, zero warnings. Key theorem `kuzminLandau_band`:
monotone increments in [δ, 1−δ] ⟹ ‖∑ e(φ m)‖ ≤ 3/(2δ) + 1 uniformly in length.
Device: klCoeff β = −1/2 − i·cot(πβ)/2 (constant real part ⟹ variation telescopes via
`Finset.sum_range_sub'`); `klCoeff_mul` by factoring e(β) − 1 = 2S(−S+Ci) +
`linear_combination` vs I²=−1, S²+C²=1; norms via corpus `ChordalSeparation`
(`norm_exp_I_sub_one`, Jordan `four_mul_le_norm_exp_two_pi_I_sub_one` — reused, not
redeclared).

Lean traps (add to the drift playbook): (1) positivity ignores sign HYPOTHESES — use
nlinarith for 0 < π·β; (2) mathlib `Finset.sum_range_by_parts` is the PARTIAL-SUM Abel form
(f·g with ∑g partials), not f·Δg — composing with `Finset.sum_range_sub` telescopes costs a
factor 2 (bound 3/(2δ)+1 instead of 1/δ+1; constants certified irrelevant); (3) push_cast
rewrites ((Real.sin x:ℝ):ℂ) into Complex.sin ↑x — when matching set-abbreviations distribute
with simp only [Complex.ofReal_sub/mul/pow/one/ofNat] instead; (4) `Complex.norm_ofReal`
doesn't exist — use `Complex.norm_real` + `Real.norm_eq_abs`; (5) zsh: use $? not
PIPESTATUS[0].

Index regen deferred to L4 batch. Next: L4 = windowed Weyl step (W) `|S|² ≤ 9N²/H +
(6N/H)Σ_{h<H}S_h*` + the k-fold iteration — pure CS/counting, statements in
`littlewood-l2-weyl-chain.md`.
