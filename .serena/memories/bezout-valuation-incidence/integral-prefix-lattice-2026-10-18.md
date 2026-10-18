Contribution 006 is complete, counted once; root-agent total 6 / 250, goal active.
Source: formal/GaloisForLFunctions/BezoutValuationIncidence/IntegralPrefixLatticeAndPrimePowerObstructions.lean (628 lines, 60 explicit declarations: 26 public theorems, 12 public definitions, 19 private theorems, 3 private definitions).
Card: docs/drafts/pipeline/3-formalized/bvi-integral-prefix-lattice-and-prime-rank-defect-2026-10-18.md.
Ledger: logs/bvi-root-2026-10-18-knowledge.md.

Exact integer primitive R_Z(q,M)=sum_{uv=q} u*mu(v)*floor(M/u), with complex and real cast bridges to the actual existing Ramanujan primitive.
R_Z matrix: rows 1..n, moduli 2..n+1. Integer incidence E(e,d)=1_{e|d}; scaled floor B(m,d)=d*floor(m/d)-m. Actual factorization R_Z*E=B.
F(m,d)=floor(m/d), indices 1..n, has determinant 1; E also determinant 1.
A terminal-column shear S and signed cyclic rotation W give B*S=F*diag(1..n)*W.
Explicit U=F^-1 and V=E*S*W^-1 are unimodular and U*R_Z*V=diag(1..n), including dimension zero. This is diagonal equivalence, not a claim that 1..n is a Smith divisibility chain.

Public core:
sieveIntegralRamanujanPrimitive_complex / _real;
sievePrefixIntegralRamanujanMatrix_incidence / _reduction;
sievePrefixIntegralLeftTransform / RightTransform and _unit theorems;
sievePrefixIntegral_solvable_iff, _injective, _existsUnique_iff;
sievePrefixIntegralReconstruction_iff;
sievePrefixIntegralObstructedData_no_solution / _real_solution;
sievePrefixIntegral_cokernel / _cokernel_cyclic / _cokernel_card;
sievePrefixIntegralMatrixOver_reduction;
sievePrefixIntegralKernelEquiv;
sievePrefixIntegral_modular_kernel_card;
sievePrefixIntegral_prime_power_kernel_card / _step;
sievePrefixIntegral_mod_prime_rank.

For every integer y, solvability iff k divides (U*y)_k; canonical x=V*((U*y)_k/k) is then unique.
At dimension n+2, F*e_last is integer data with no integer solution but a real solution.
Cokernel is product_{k=1}^n ZMod k, cardinal n!.
Over every commutative ring the actual operator's kernel is equivalent to product of scalar k-torsion kernels.
For m>0, modular kernel cardinal is product gcd(m,k).
For intrinsic prime p and all a>=0, cardinal mod p^a is p^(sum_{r=1}^a floor(n/p^r)); each a->a+1 ratio is p^floor(n/p^(a+1)).
Rank mod p is n-floor(n/p).
Scope is integer Ramanujan amplitudes, equivalently integer normalized coefficients c(d)/d on the nonconstant tail, not arbitrary integer raw weights. No asymptotic cancellation/conditioning result.

Reused generic cokernel transport:
HTGeometry.ConstraintRelativity.nonempty_coker_equiv_pi_of_smith from SimpleHorizonTransmutation.lean.
Reused scalar kernel cardinality: IsAddCyclic.card_nsmulAddMonoidHom_ker.
Do not count these dependencies or a future canonical lcm Smith-chain display separately.
Local corpus audits were exhaustive over returned hits but retrieval coverage was partial; no external novelty claim.

Verification: final named original-source lake --old env lean -j 1 with explicit root/output passed warning-free. All 38 public declarations axiom-audited; all 26 theorem closures exactly propext, Classical.choice, Quot.sound. Raw audit logs/bvi-root-2026-10-18-integral-prefix-axioms.txt.
All 60 source declarations matched the index exactly. Owned module wired once; artifact installed atomically/hash verified. Source SHA256 325e220a02d88fe3b6cf09574694bc7e0584be403f749c7789016cd809fe3b95; artifact eb5fd38addb820656b5525cfd45b1a6cbc524fcaa419c0e9fe7ee2f1e3c1ad2c.
Global lint exited 1 on foreign missing imports StationaryResolventMarkovPositivityAndNodalDefectProducer and PrimeTailCalibrationAndMobiusDefect. No finding names this module. At that inventory time 12/13 field modules wired. All 56 owned temporary roots removed and owned jobs terminal; no full/umbrella build, no numerical experiments.

Useful Lean pitfalls: qualify open _root_.RHTower inside GaloisForLFunctions; use controlled Int.cast_sub/mul/natCast rewrites to preserve Nat floor divisions rather than broad push_cast; parenthesize additive bodies of typed Fin products; Matrix.mulVec_diagonal is pointwise, so apply after ext i.
Next uncounted candidate: docs/drafts/pipeline/0-backlog/bvi-translated-prefix-observability-and-maximal-zero-runs-2026-10-18.md. Its sharp translated-window horizon and proposed family require their own paper/novelty/Lean audit.