# EDQ finite logarithmic cotangent transport — 2026-09-06

Goal remains active: no unconditional RH proof or falsification. User requires efficient foreground single-process Lean, no full or umbrella builds, only new-declaration axiom audits. Latest turn completed a positive finite source law, not R/B2/C or weighted-head sign.

New leaves, wired and final built:
- formal/GaloisForLFunctions/RHTower/ArithmeticCotangentPhaseTransport.lean (303 lines), namespace RHTower.PhaseCotangent.
- formal/GaloisForLFunctions/RHTower/ArithmeticLogarithmicCotangent.lean (260 lines), namespace RHTower.LogarithmicCotangent.
39 declarations total (31 theorems, 8 defs); all audited ONLY for these new declarations: propext, Classical.choice, Quot.sound. Scratch lake env lean checks passed; serialized lake build --old <leaf> final audits built only each new leaf (dependency log messages were cached replays). Formal lint now PASSES, prior unrelated wiring holes fixed by other work. No new sorry/axiom/native_decide or computational certificate. No owned Lean processes left. Scratch sources removed, validation logs remain /tmp/edq_cotangent_transport_build.log, /tmp/edq_logarithmic_cotangent_build.log, /tmp/edq_cotangent_new_axioms.log, /tmp/edq_cotangent_lint.log.

Proof chain: literal Euler deletion -> retained remainder/joint signature -> source orientation through exceptional head -> exclusion of every off-line zero -> RH. New exact law links literal remainder to finite cotangent phase transport, but weighted drift/head comparison is still missing.

Generic law:
phi0=0, E_j=exp(2pi i phi_j), delta_j=phi(j+1)-phi j, q_j=cot(pi delta_j).
Lean cutoff M includes M+1 samples, terminal phase M+1, interior sum range M.
weightedPhaseDefect D_M(w)=sum(j<=M) w_j sin(theta_j) + w_M sin(theta_(M+1))/2 - w_M q_M(1-cos(theta_(M+1)))/2.
weightedPhaseDefect_eq universally:
D_M = sum(j<M)[Delta w_j sin(theta_(j+1))/2 - Delta(wq)_j(1-cos(theta_(j+1)))/2] + resonantPhasePrefix.
The resonant prefix retains w_j sin(theta_j) when sin(pi delta_j)=0. Exact inverse chord c=-1/2-i cot/2 comes from local Sieve/KuzminLandau. Nonresonant coefficient formula now proved for every winding band; resonance E_(j+1)=E_j retains original sample.
For weights1, decreasing increments in(0,1) give D<=0; strict decrease with M>0 gives D<0. At arbitrary increments phaseDefect_eq_with_resonance, and nonresonant next step phaseDefect_step give exact transport.

Literal law:
logarithmicPhase n t j = t/(2pi)*(log(n+j)-log n), equal log ratio n>0.
Increments = t/(2pi) log(1+1/(n+j)); positive strictly decreasing, strictly less than t/[2pi(n+j)] for every t>0.
logarithmicPhase_defect_neg: n>0, 0<t<2pi n, M>0 -> corrected unweighted defect<0.
logarithmicPhase_closed_prefix_neg: if terminal t log((n+M+1)/n)=2pi K (integer), correction vanishes -> literal sine sum<0.
logarithmicPhase_cotangent_step_pos/chord_nonzero beyond local threshold t<2pi(n+j).
logarithmicPhase_defect_le_head: t>0, t<2pi(n+J), M>=J -> D_M<=D_J. Retains actual head value, no sign assigned.
powerWeight n sigma j=(n+j)^(-sigma).
rotated_power_eq retains exact anchor rotation exp(-i t log n) and complex power at s=sigma-it.
rawPrefix_im_eq identifies n=1 weighted sine sum with literal Dirichlet rawPrefix(s,N). sourcePhaseDefect_eq retains actual powerSumRemainder(s,M+1)+zeta(s)+(M+1)^(1-s)/(1-s)+kernel(s,M+1)/2 plus endpoint phase correction. Exact weighted/drift/resonance decomposition valid for ALL real sigma,t, with no zero premise. Minus-height convention explicit. No sign proved for actual weighted drift, initial head, C/B2, proposed linear remainder threshold R, or RH.

Docs:
- Active comparison: docs/drafts/pipeline/1-in-progress/edq-logarithmic-cotangent-orientation.md; LCO1-LCO5 completed, checkbox only RH/independent head comparison remains.
- Certificate: docs/drafts/pipeline/3-formalized/edq-logarithmic-cotangent-transport.md.
- Frontier EDQ narrative and table updated current-state only.
- STATUS new route-independent constraint: must retain phase-normalization/reweighting endpoints, drifts, resonant samples.
- Generic ancestry classical finite summation by parts; no novelty claim.

Next useful direction must control complete weighted expression, not prove more unweighted orientation or recreate generic exact sum identities. Prior quartic normalizedWeightedRemainder negativity n²>=t³ remains; exceptional head at unit still open. Do not infer C/R/B2 from finite unweighted sine sum. Holomorphic unit-phase global/finite charts already terminal; local germ iff simple critical zero. No need re-audit those modules.

Toolchain pitfalls: set_option autoImplicit false prevents accidental free sum-index hypotheses; ALWAYS parenthesize entire sum bodies with subtraction. Real.cos_lt_one_iff does not exist; Real.cos_eq_one_iff_of_lt_of_lt exists. Real.cos_two_mul' yields cos²-sin²; use sin_sq_add_cos_sq or sin_eq_zero_iff_cos_eq at resonance. Complex.exp_re/im with simp is safer than exp_mul_I for real parts; broad simp may coerce real trig to Complex trig. one_div_lt_one_div exists. Check exact new names in /tmp only, no repeated existing audits.

Repo concurrently modified/committed by other work. No commit/push performed here. Preserve unrelated changes.