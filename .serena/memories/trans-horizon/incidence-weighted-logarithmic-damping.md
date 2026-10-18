# Divisor-incidence perturbation and logarithmic damping (2026-10-18)

Thirteenth connected contribution completed; indefinite THIM research goal remains active. Previous state: `mem:trans-horizon/explicit-damping-radius`.

## Verified result

New leaf `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/DivisorIncidencePerturbationAndLogarithmicDamping.lean`, 340 lines, 19 public theorems + 1 definition + 1 private helper. SHA256 `d1f497e8a2da771becdca4b43c18fe731dea85ab38e8fd8afd3a5327cedf90a5`. Imports previous quantitative leaf (unchanged hash `26f4f099e118a6e00df88f11dca456ba51ef49e780d092fe4d9949b45b2de6d5`) and Mathlib.NumberTheory.Harmonic.Bounds. Wired into THIM umbrella; MainTheorems reachability verified.

For arbitrary coefficient weights c,b, summed response error through K is at most Σ_{d≤N}|c(d)−b(d)| floor(K/d). If both response paths are bounded by B through M+1, prefix-defect error is at most 4B times that weighted coefficient sum with K=M+1. No squarefree support needed for perturbation bound. Uses existing exact floor reciprocity from BezoutValuationIncidence/FermiCellJumpReciprocityAndPronicTailBridge.lean; no duplicate incidence identity.

Removing the unchanged unit damping coefficient before the harmonic estimate gives Σ_{d≤N}log(d)/d≤(log N)^2, N≥1. Consequently six-band damping error ≤8ε(M+1)(log N)^2 for ε≥0,M+1<6(N+1).

`incidenceDampingRadius N = 1/(96*(N+1)*(log N)^2)`. For N≥2 this is positive and strictly larger than previous radius by exact algebraic factor N/log N>1. Throughout 0≤ε≤radius, every M≥1 with R_N(M+1)<6(N+1) has D≤−1/2. Infinite endpoint height and all positive powers share the same interval.

General finite-certificate transport: any squarefree-supported c, any real C, certificates D_N(k−1;c)≤C for all2≤k<6(N+1) transfer to every M≥1 with certified radical endpoint. Rough state uses Bertrand prime; independent of damping and sign of C.

On new interval, finite response error ≤1/16. For prime p>5,N=6p−1,k=30p, every positive power has response≥31/16 AND D≤−1/2. Base k remains first unit-envelope failure. Radius depends on N/p; no cofinal fixed-positive-exponent claim. Full all-ε≥0 six-band defect control remains OPEN; no optimality of constant96 or radius order asserted. Classification: new formulation from known classical constituents; no external priority claim.

## Public names

abs_sieveSeq_sub_le_sieveSeq_abs_sub; sum_abs_sieveSeq_sub_le_divisor_incidence; abs_edge_defect_sub_le_endpoint_errors; abs_prefix_defect_sub_le_sum_response_errors; abs_prefix_defect_sub_le_divisor_incidence; sum_log_div_le_log_sq; sum_damping_error_mul_div_le; sum_abs_sieveSeq_damping_sub_le_log_sq; abs_prefix_defect_damping_sub_le_log_sq; incidenceDampingRadius; incidenceDampingRadius_pos; sixHorizonDampingRadius_lt_incidenceDampingRadius; incidence_damping_radius_budget; prefix_defect_le_neg_half_of_incidence_radius; prefix_defect_le_of_finite_radical_certificate; radical_defect_le_neg_half_of_incidence_radius; power_defect_le_neg_half_of_incidence_radius; response_error_le_sixteenth_of_incidence_radius; incidence_damping_counterfamily_power_separation; incidence_damping_counterfamily_first_failure.

## Verification

Full scratch and actual source `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/TransHorizonIncidenceMechanics/DivisorIncidencePerturbationAndLogarithmicDamping.olean GaloisForLFunctions/TransHorizonIncidenceMechanics/DivisorIncidencePerturbationAndLogarithmicDamping.lean` exited0 without warnings. Actual-source handle34645 terminal0; axioms handle4403 terminal0. DO NOT poll again. All20 public declarations and private sum_shift_le_sum_succ have exactly {propext,Classical.choice,Quot.sound}; two generated helpers use only {propext,Quot.sound}. 23 closures audited, all standard-only. Index exited0, all20 public API entries/source positions verified. API generator DECL_RE excludes private declarations; search INDEX_DECL_RE includes them. Initial audit expecting21 APIrows failed; corrected against actual generator policy, axiom checks unchanged. No need to rerun Lean.

`logs/thim-incidence-audit.json` records hashes, source/artifact freshness, all closures, API checks, baseline docstrings, wiring, cleanup and lint. Logs `logs/thim-incidence-{lean,axioms,index,lint}.txt`. Global `lint --check-generated` exited1 with2 external errors: unreachable BezoutValuationIncidence.CoprimeMobiusCancellationAndOddDilationMeans; research leaf at package root TransHorizonIncidenceMechanics.lean. No new-leaf/prohibited declaration findings. No full/umbrella build or numerical experiment; no added axioms, heartbeat changes, commits, pushes or README edits. All owned jobs terminal; nine owned temporary files removed and verified absent. Structural audit handles36243failed then22816passed, both terminal. Index5142 and lint54202 terminal.

Card `docs/drafts/pipeline/3-formalized/thim-incidence-weighted-damping.md`, ledger `logs/thim-radical-sawtooth-knowledge.md`, failed-route positive survivor `docs/drafts/pipeline/5-failed/thim-universal-unit-envelope-beyond-five.md` updated. Last two contain new radius, 31/16 and general incidence/transport laws.

## Next conjecture — UNPROVED

For N≥2,K=6(N+1), W_N(c)=Σ_{d≤N}|c(d)−μ(d)|floor(K/d), conjecture every squarefree-supported c with W≤1/20 satisfies D_N(M;c)≤−1/2 on all certified nonempty radical fibers. Mechanism: aggregate incidence bound controls pointwise error≤W up toK; |s_c|≤2+W; defect error≤4(2+W)W≤41/100<1/2. Strict μmargin and new general certificate transfer finish if every hypothesis checks. Stronger candidate exact quadratic condition4(2+W)W≤1/2. Unit coefficient charged weightK, respecting gauge obstruction. Audit paper proof/endpoints/Lean before asserting. Separate all-ε conjecture stays open.

Preliminary field-filtered search `squarefree coefficient perturbation weighted divisor incidence neighborhood negative prefix defect`: partial=false,74142files,pending0,generation1455029; all20 candidates and20 source-argument statements inspected. Rough-sign/gauge/radical/power/recovery hits, no matching quantitative neighborhood certificate returned. Broaden before implementing. Prior broad incidence search partial=false74139files generation1454954; Mathlib harmonic search partial=false74141files generation1454970, all ranked hits inspected. Mixed compiler/source coverage, not full validation.

## Next-turn discipline and useful Lean details

User attachment must be reread every turn: `/Users/michael/.codex/attachments/74d97d4e-25ce-464f-8843-4a83e3b3476e/pasted-text-1.txt`. Full THIM README reread each new turn; current turn read317lines, never edited. No hgtl7, no RH, no numerical experimentation. One owned foreground Lean process, no full builds; actual-source leaf audit and separate /tmp axiom scratch; keep goal active and make one significant contribution each turn. Read docs if available, list/read task-relevant Serena memories, state mission, inspect prior research. No subagents authorized this turn. update_plan unavailable; card tracks steps.

`_root_.harmonic_eq_sum_Icc` avoids RHTower namespace collision. Harmonic real cast conversion uses Rat.cast_sum/Rat.cast_inv/Rat.cast_natCast. Nat.cast_div_le bounds natural floor by real quotient. Prefer `add_le_add ih (le_refl _)` over shadowed add_le_add_right. For cast polynomial normalization explicit calc + `push_cast; ring` works. Private axiom enumeration via environment name + mkIdent, never guessed numeric private prefixes. Source new docstrings20, API public entries20, private1 separately audited.
