# FZZ sphere-vacuum kernel phase collapse (2026-09-01)

- Killed chain: sphere vacuum/area position-kernel phase -> chiral divisor-mode passivity -> Mellin completeness -> RH.
- Source: Halder--Jafferis arXiv:2402.00932v3 (3.26), (3.29)--(3.33). Vacuum integrand uses conjugate absolute-value powers. Corpus theorem resolves same-charge increment 0 and opposite symmetry-normalized factor a(k)=2k/(k-2).
- New result: for every finite collision-free HJ absolute-power product, K(delta)=prod q_i^(e_i+delta v_i)=exp(sum (e_i+delta v_i)log q_i)>0 and K'=K sum v_i log q_i is real. Antiunitary-odd/chiral phase is identically zero. No predicate of exact HJ marked phase selects twist.im=0.
- Closed Lean capstone: GaloisForLFunctions.RHTower.fzzCigarParity_sphereVacuumReplicaKernelPhaseCollapse_noGo.
- Module: formal/GaloisForLFunctions/RHTower/FZZCigarParitySphereVacuumReplicaKernelPhaseCollapseNoGo.lean; umbrella wired.
- Audit: direct lake env lean PASS; targeted lake build module PASS 8840/8840; axioms [propext, Classical.choice, Quot.sound]. Global lint only pre-existing unrelated unreachable-module failures.
- Cards: docs/drafts/pipeline/3-formalized/fzz-sphere-vacuum-replica-kernel-phase-collapse.md and docs/drafts/pipeline/5-failed/fzz-sphere-vacuum-position-kernel-phase.md.
- Exact survivors: real integrated sign/magnitude; phase from meromorphic regularization of divergent integrals; external-BRST branches; torus/higher-genus prime-form monodromy; higher replica order. Do not overclaim beyond local genus-zero first-order kernel.
