# Concurrent causal accessibility and quenched replica action (2026-08-13)

New Stage-2 paper proofs:
- docs/drafts/pipeline/2-fully-proven/concurrent-causal-heap-accessibility-law.md
- docs/drafts/pipeline/2-fully-proven/quenched-causal-replica-action-law.md

Core correction:
- Trace-prefix first hits are not prefix-free after quotienting support-disjoint gate commutations: for independent a,b, ↑a ∩ ↑b = ↑ab.
- For trace monoid M and Z(z)=sum_T z^|T|, finite law pi_z(T)=z^|T|/Z has exact cylinder pi_z(↑u)=z^|u| by cancellation, and E|Pref(T)|=Z.
- Define F_A,z(x)=pi_z{T: some causal prefix u reaches x from robust seed A}. Then 0≤F≤1, z^C≤F≤pi_z{|T|≥C}, recurrence C=0 gives F=1, and -log F is exact KL information projection onto causal-hit heaps.
- Completed phase cap exponent matches heap capacity; improvement is exact bounded causal union, not stronger exponent.
- Soft reporter S=E_T max_{u≤T}(1-d(x,ev(u)A)/delta)_+ is 1/delta-Lipschitz independent of Hilbert dimension, depth, and prefix count; C≤s => S≥z^s. Duhamel gives source Lipschitz |t|/delta. This removes dimension-linear approximate-tube regularity remainder but not mean decay.

Quenched replica law:
- Replicate heaps, not Hamiltonian. For one shared static H, J(H)=-log F(Phi_H(t)), Z_r=E_H F(H)^r.
- Z_r is exact product-incidence probability for r independent heaps against same H and endpoint.
- P_H{C≤s}≤z^(-rs) Z_r.
- Exact duality: -log Z_r = inf_{q<<rho_H} [D(q||rho_H)+r E_q J].
- Thus Z_r≤z^(rs)e^(-kappa r) iff (1/r)D(q||rho)+E_q J≥s log(1/z)+kappa for every source tilt q. Exact for growing-replica certificate; sufficient, not necessary, for direct Brown event lower tail.
- Rare carrier B with J≤j contributes Z_r≥rho(B)e^(-rj), so source rarity is amortized as log(1/rho(B))/r.
- a_r=-(1/r)logZ_r=-log||F||_r decreases with r to ess inf J. Replica orders with a_r>s log(1/z) form an initial interval; larger r can destroy certificate.
- Empty heap p0=1/Z proves F=1 iff endpoint is in recurrence seed A and Z_r→rho{x(H)∈A}; common recurrence mass isolated once.
- Hostile limitation: rare easy carrier can be harmless to desired event tail but dominate Z_r because certificate pays z^(rs); must cut, stratify, or use direct non-moment proof.

Active exact growing-replica core after one common recurrence/fast-forwardable carrier cut:
For every retained source tilt q,
(1/r)D(q||rho_t^circ)+E_q J_A,z(Phi_H(t)) ≥ s(t)log(1/z)+kappa.
Physical static-local action gap remains open.

Updated research logs:
- docs/drafts/pipeline/1-in-progress/static-local-complexity-law.md
- docs/drafts/pipeline/1-in-progress/synthesis-divergence-brown-law.md
- docs/drafts/pipeline/1-in-progress/observer-critical-carrier-confinement-law.md

No Lean writes/builds due shared corpus refactor. No subagents. git diff --check passed.
External boundary: Abbes–Mairesse arXiv:1407.5879 classical trace probabilities; Rizzo arXiv:1403.1828 rare-sample replicas; no abstract probability novelty claimed; quantum application priority unverified.