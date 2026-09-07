# EDQ prime-energy transport

- **ID:** EDQ-PET
- **Stage:** 3-formalized; paper proof and Lean verified
- **Sources:** ArithmeticFiniteZeroDisplacement, PrimeClockFiniteScaling, FinitePrimeBoundaryTransfer, PrimeEnergyZeroTransfer.

## Full chain

Euler deletion → exact complex zero balance → signed arithmetic separation → exclusion of off-line zeros → RH. The displacement law gives vanishing logarithmic motion relative to an actual zero. The prime-energy RH receiver instead uses displacement from the critical line. This component proves an independent source comparison identifying exactly how that energy changes under the actual finite-zero motion.

## Dependency-closed paper proof

The actual finite prime-clock energy is E_N(e)=sum_(p<=N) 4*sinh(e*log p)^2/p. Fix e!=0 and N>=2; write c=abs(e)*log 2>0, b=abs(h)*log N>=0, and

a(c,b)=cosh b-1+(1+1/c)*sinh b.

For each prime p<=N, set x=e*log p and y=h*log p. Then abs(x)>=c and abs(y)<=b. The inequalities cosh x<=abs(sinh x)+1 and abs(sinh x)>=abs(x) imply cosh x<=(1+1/c)*abs(sinh x). The exact addition formula and monotonicity of cosh and sinh give

abs(sinh(x+y)-sinh x)<=a(c,b)*abs(sinh x).

Factoring the difference of squares gives a relative term bound a*(2+a)*sinh(x)^2. Sum with the actual positive weights 4/p, retaining every prime, to obtain

abs(E_N(e+h)-E_N(e))<=a(c,b)*(2+a(c,b))*E_N(e).

The prime 2 makes E_N(e)>0. Therefore, whenever integer cutoffs N_j tend to infinity and h_j*log N_j tends to zero, E_(N_j)(e+h_j)/E_(N_j)(e) tends to 1. This comparison has no zeta-zero premise.

For the critical center e=0, the corpus's quadratic upper bound, together with susceptibility/(log N)^2 -> 1/2, proves E_(N_j)(h_j)->0 under the same logarithmic-motion condition. For any fixed e!=0, the corpus's lower bound gives E_N(e)->infinity, and the relative comparison transports that divergence to e+h_j.

Apply the exact finite-zero displacement law: for every actual nontrivial zero rho and every cofinal sequence of finite-head zeros tending to rho, h_j=Re(z_j-rho) satisfies h_j*log N_j->0. Hence the motion energy E_(N_j)(h_j) vanishes. Energy measured from the critical line has a different classification: it tends to zero if Re(rho)=1/2; otherwise it is asymptotic to E_(N_j)(Re(rho)-1/2) and diverges. The normalization in the RH receiver is retained as well: its lower bound is 4*(Re(z_j)-1/2)^2*susceptibility(N_j)/(log N_j)^2, which tends to 2*(Re(rho)-1/2)^2. Thus eventually the normalized energy is at least (Re(rho)-1/2)^2; at the critical center the zero floor holds by nonnegativity. Actual cofinal sequences exist for every rho. Thus finite approximation cannot silently replace critical-line energy by motion energy. An independent source bound at the critical center remains necessary; this result does not establish RH.

## Gates

- [x] Source and receiver comparison; dependency-closed paper proof.
- [x] Lean relative source bound, cofinal limits, actual finite-zero specialization and normalized floor.
- [x] Leaf audit, new-only axioms, wiring; repository lint executed with unrelated concurrent failures.
- [x] Index, ledgers, cleanup.
- [ ] Independent critical-center energy bound or signed separation; RH.

## Formal certificate

- Leaf: `formal/GaloisForLFunctions/RHTower/ArithmeticPrimeEnergyTransport.lean` (283 lines, 11 theorems, 1 definition); namespace `RHTower.DeletionMixedRefinement`.
- Independent full-source comparison: `abs_primeClockCutoffEnergy_sub_le_transport`; explicit amplitude error: `primeEnergyTransportError`.
- Relative cofinal transport: `tendsto_primeClockEnergy_ratio_of_log_motion`.
- Critical-center decay: `tendsto_primeClockEnergy_zero_of_cofinal_log_motion`; noncritical-center divergence: `tendsto_primeClockEnergy_atTop_of_log_motion`.
- RH-normalized floor: `eventually_center_sq_le_normalized_primeEnergy`.
- Actual finite-zero specialization: `finite_zero_primeEnergy_transport`; unconditional actual cofinal witnesses: `exists_cofinal_finite_zero_primeEnergy_transport`.
- Scratch: `LEAN_NUM_THREADS=1 lake env lean /tmp/edq_energy.lean`, exit 0, no diagnostics.
- Final audit from `formal`: `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticPrimeEnergyTransport`, exit 0. Only this leaf built (4.0 seconds); dependencies cached. Umbrella import appended; no full or umbrella build.
- New-only axioms: `lake env lean /tmp/edq_energy_axioms.lean`, exit 0. All 12 declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`; no added axioms, admissions, or computational certificates.
- Repository lint: exit 1; unrelated concurrent modules remain unreachable from their umbrella: `ThetaCuspTwoAtomOddProfiles`, `TwoAtomOddAlgebra`, `TwoAtomOddHighReserve`. The new EDQ leaf is wired. These concurrent modules were not modified by this task. Existing file-size warnings also present.
- Index: exit 0; API/GAPS/OVERVIEW and search database refreshed once. refreshed formal/.lean_search-9925dbc05e32a559.db (5 changed, 0 removed).
- Cleanup: all owned scratch-check, leaf-build, axiom, lint, and index sessions reached terminal states. Both owned scratch Lean sources removed; logs retained. No owned Lean/lake process remains.
- Logs: `/tmp/edq_energy.check.log`, `.build.log`, `.axioms.log`, `.lint.log`, `.index.log`.

RH remains unproved and unfalsified. No off-line zero is asserted to exist, and no unproved energy bound is used. The noncritical statements give the exact conditional branch; the source comparison and actual-zero transport theorem are unconditional.
