# Genuine prime resonance: modulus decrease, actual error dominance, conservative flow

## Goal/status
Goal remains ACTIVE and unmet: RH must be formally proved before complete. RH remains unproved/unfalsified. This turn made verified mathematical progress, no blocker. Four new leaf modules audited individually with `lake --old env lean <leaf> -o <fresh olean>`, all green/no warnings. Eight endpoint axioms audits: only propext, Classical.choice, Quot.sound. No added axioms, sorry, numerical experiments, heartbeat hacks, umbrella/full builds, commit/push, subagents. All four imports wired RHTower.lean lines19751–19754 at completion. Own scratch `work/noether_prime_resonance_audit.lean` deleted. Source files untracked, preserve other concurrent work.

Repo `/Users/michael/Documents/code/hgt/formal`. Chat cwd different. Session init/skills/manual already done. Use corpus search tool `../scripts/formal_tools.py research QUERY --mode lexical --no-refresh --budget-seconds 45 --per-module 0` plus actual Lean; no cards. Short meaningful commentary <=60sec. No build process remains except possibly final index refresh handle from turn (see final output); index isn't a Lean build.

Index/lint: refreshed index, lint then saw concurrent new source changes. Repeated index+lint once; still races: latest lint flags OTHER unfinished/unwired modules MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, MoebiusMollifiedZetaField, XiGaussianOrientationPhase, XiGaussianThirdOrientationSaving, ZetaZeroDensityPowerSaving, and concurrent staleness in LEAN_API/LEAN_OVERVIEW. A final index refresh is being completed after that lint. Do not claim global lint green. No own module unreachable; all own final oleans freshly checked. Don't wire others' unfinished modules.

Prior state `mem:research/noether_cofinal_prime_log_cell_full_atom_coercivity_2026_09_27`, `mem:research/noether_far_gap_full_complex_coercivity_positive_phase_flow_2026_09_27`.

## Main discovery
Previous cofinal prime-log cell sources allowed interior atoms but did not guarantee the selected cells contained proper powers. New construction centers two exact physical translates at an ACTUAL PRIME logarithm. At the resonant lag, ground cross-correlation equals the full physical mass. Continuous cross is O(radius * mass), so narrowing forces the prime term to dominate. For arbitrarily large primes, critical weight Lambda(n)/sqrt n is small enough for both full quadratics to stay positive.

Result: actual nonzero profiles at arbitrarily large primes with `0 < Q(phi+psi) < Q(phi-psi)`, and phi+psi=abs(phi-psi) pointwise. Prime cross difference strictly positive (not removed by support avoidance). Earlier atom-free examples had the reverse strict ordering. Actual CCM source reconstruction gives ErrPrime<ErrContinuous<0, both full energies positive, and a positive full phase potential with exact conserved mechanical energy/Newton law. Any continuous local scalar potential preserves the strict modulus decrease, complementing the existing modulus-increase-after-all-local-potentials theorem.

Interpretation: no universal direction of modulus monotonicity, even repaired by adding a local scalar potential. This does not produce negative Q or refute RH. B<0 alone is not a new invariant obstruction (phase origin can flip coefficient sign); the actual nonzero prime error and its dominance are the new arithmetic content. Kinetic choice in inverse-Noether construction remains chosen, not canonical arithmetic dynamics.

## 1. ThetaCompactRealGroundProfiles.lean
Namespace RHTower.ThetaSourceWard. Imports ThetaFinitePrimeAtomPolarization.
- `thetaCompactRealGroundProfile (f:ℝ→ℝ) (hf:ContDiff ℝ (⊤:ℕ∞) f) (hc:HasCompactSupport f) : Schwartz real` built from f*inv k via compact-support.toSchwartzMap.
- apply: f/k. reconstruct: k*profile=f.
- support exactly support f; compactness retained.
- `thetaGroundNormSq_compactRealGroundProfile`: M(complexify profile)=integral f².
- `thetaGroundShiftCross_matched_physical_translate f g hf hg hfc hgc d hmatch`: if g(x+d)=f x for all x, cross(profilef,profileg,d)=M(profilef).
- `thetaGroundNormSq_matched_physical_translate`: same translation assumption gives equal masses.
Important type lesson: bare `ContDiff ℝ ⊤` denotes the stronger omega order in current Lean/mathlib; use `(⊤ : ℕ∞)` for smooth functions. k has order infinity, bumps too. Had to fix this before any successful audit. The support proof needs explicit `⟨And.left,fun hx=>⟨hx,hk⟩⟩`; simp didn't consume even a typed hk due elaboration/coercion behavior.

## 2. ThetaIsolatedPrimeAtomBounds.lean
Namespace RHTower, opens ThetaSourceWard and GaloisForLFunctions.RHTower.
- `abs_thetaGammaPolarGroundCrossPairing_balls_le` line23: compact real phi/psi in balls c1,c2 radiusr>=0, threshold<=c2-c1-2r gives
  abs(Ccross)<=exp((c2-c1+2r)/2)*r*(Mphi+Mpsi).
  Uses actual CCM source bridge, established L1 support/mass bound and regular kernel bound. Retains full Gamma/pole sign and proves integrability via prior bound. No prime assumptions.
- `exists_logNat_isolating_radius {n} (hn:2<=n)` line61: exists e>0 with threshold<=logn-e and for every m>=2, abs(logm-logn)<e =>m=n. e=min(logn-log(n-1),min(log(n+1)-logn,logn-threshold)). Uses plasticRoot<2, log monotonicity.
- `tendsto_vonMangoldt_div_sqrt_zero` line95: Lambda(n)/sqrt n→0 along naturals. Squeezed by log n/sqrt n using `ArithmeticFunction.vonMangoldt_le_log` and root `HTGeometry.tendsto_logPow_div_rpow` exponent1/2,k1.

## 3. ThetaPrimeResonantModulusDecrease.lean
Single endpoint `exists_arbitrarily_large_prime_resonant_modulus_decrease (N:ℕ)` line24:
exists actual prime n>=N, compact real Schwartz phi,psi,r>0,
- STRICT threshold<logn-2r;
- exact supports ball0r and ball(logn)r;
- nonnegative phi,psi, strictly positive at centers;
- phi+psi=abs(phi-psi) pointwise;
- P(phi+psi)-P(phi-psi)>0;
- 0<Q(phi+psi)<Q(phi-psi).
All existence endpoints internally proved, no missing mathematics assumed.

Proof recipe:
1. Existing local coercivity gives delta,C>0 uniform in center.
2. Choose actual prime n beyond N and eventual cutoff so w=Lambda(n)/sqrt n<C/4. w>0 by actual primality. Nat.exists_infinite_primes produces n.
3. d=logn; isolate radius e above; E=exp((d+1)/2).
4. r=min(delta/2,min(e/4,min(1/2,w/(8E)))). All positive, r<delta,2r<=e/2,2r<=1.
5. F=ContDiffBump0 with inner r/2 outerr; physical g(x)=F(x-d); phi=groundprofile(F),psi=groundprofile(g).
6. Their masses both M>0; shiftCross at d=M exactly. Every active prime-power log among their cross translations lies in singleton{n}, by isolation.
7. Exact finite atom polarization: Pdiff=2wM. Full Qdiff=4Ccross-4wM.
8. Continuous bound +radius gives abs(Ccross)<=(w/4)M. Therefore Qplus<Qminus. Both local diagonal energies>=CM; parallelogram +w<C/4 gives Qplus>0.
9. Disjoint nonnegative profiles imply modulus equality.

Lean details: compactness of g via `F.hasCompactSupport.comp_homeomorph (Homeomorph.addRight(-d))`; `convert ... using1; funext x; rfl` works whereas simp_only failed to unfold comp. When rewriting atom cross at d, first change RHS to `2*w*thetaGroundShiftCross phi psi d` then rw[hcross]; simp didn't unfold let d automatically.

## 4. CCMPrimeResonantNoetherWitness.lean
Imports new resonance + existing CCMPositiveNoetherPhaseWitness.
Private `primeEnergy_ordered_difference`: ordered profiles have equal prime diagonal (pointwise norm-squares of plus/minus equal), so Eprime(plus)-Eprime(minus)=-2(Pplus-Pminus).

`exists_ccmPrime_resonant_localization_dominance` line56:
exists actual a,u,v,compact smooth theta with
- v(x)=norm(u(x)) cast complex;
- theta only0 orpi on supportu;
- cosLocalized(u)=v; sinLocalized(u)=0;
- ErrPrime(u,theta)<ErrContinuous(u,theta)<0;
- 0<Q(v)<Q(u).
Constructed from new prime resonance (N0), compact separator angle on disjoint closed supports. The proof establishes exact
ErrPrime=-2 Pdiff,
ErrContinuous=-4 Ccross.
Ccross>0 from existing `thetaGammaPolarGroundCrossPairing_pos_of_balls` using strict threshold gap. Hence genuine nonzero prime interaction drives the sign reversal. This is stronger than the earlier prime-error-zero localization witnesses.

`exists_ccmSmooth_modulus_decrease_all_local_potentials` line165:
exists fixed actual u,v with v=absu and for EVERY V:C(ℝ,ℝ),
Q(v)+integral V normv² < Q(u)+integral V normu².
Local scalar potential energies exactly agree pointwise. Opposite-order theorem already exists in CCMThetaModulusObstruction.lean:132 `exists_ccmSmooth_modulus_increase_all_local_potentials`; don't duplicate it.

`exists_ccmPrime_resonant_positive_noether_flow` line183:
exists actual a,u,compacttheta,B<0, ErrPrime<ErrContinuous<0,
- E(q)=Q(u)+arithmeticPhasePotential B q (B*(1-cosq));
- E(q)>0 allq;
- (flow'(B,q,t))²/2+E(flow(B,q,t))=Q(u)+2absB+1;
- trajectory''(t)=-E'(trajectory(t)).
B=(ErrPrime-ErrContinuous)/2. E(pi)=Q(v)>0 is minimum because B<0 and cos>=-1. Uses existing global selected positive-speed flow and action, no assertion for arbitrary initial velocity/energy.

## Verification
Four finished source leaves compiled individually, fresh oleans. Umbrella four imports only, no umbrella compilation. Scratch eight axioms audits all only standard3. Own scratch removed. Source scan clean of sorry/axiom/admit/heartbeat/#eval/native_decide. Shared generated metadata may change during long lint; final refresh performed after repeated race; report global lint limitation rather than claiming clean repo. No commit/push.

## Continuing the actual RH goal
No proof/disproof yet. New result pinpoints actual competition and rules out a universal modulus argument even after local scalar corrections. Need a genuinely nonlocal/global control mechanism; pairwise positivity of narrow sources does not glue automatically.
Potential next experiments (unproved):
- Many-component resonant packets with exact prime/Euler deletion coupling; search corpus first (lots of EulerDeletion and prime-power flow infrastructure already exists). Target actual collective sign, not merely rewrapping narrow-source positivity.
- Sharp atom recovery: matched narrow translates give Qdiff/(4M)=Ccross/M-w and abs(Ccross/M)<=2 exp((d+2r)/2)r, so as radius shrinks, normalized relative-phase interference recovers -Lambda(n)/sqrt n. Can formalize for every integer n>=2, zero-weight composites included; this is an arithmetic reconstruction result, not by itself RH.
- Do not assume prime gaps near every square are below sqrt scale; previous cofinal cell theorem does not supply that. Genuine prime-centered construction now avoids needing this false/unproved shortcut.
