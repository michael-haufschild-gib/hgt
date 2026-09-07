# CCM-FU Bernoulli prime energy — 2026-09-07

RH, actual SD1 and adaptive PE4/PE4G remain OPEN. Goal ACTIVE. Previous turn's generic cube obstruction was progress; this turn adds actual-source finite identities and a new pole-based paper obstruction. Full chain unchanged: completed Guinand–Weil → marked rectangular current → affine Suzuki checkpoints → signed curvature → coherent prime–polar–Gamma/unit-Riesz boundary → Xi-screw Green → RH.

## PE5 frozen and current status
New `docs/drafts/pipeline/1-in-progress/ccm-fu-bernoulli-prime-energy.md` freezes PE5: independent Bernoulli processing at every t∈[0,1] keeps average literal retained energy E_t(M)≤original Q(M) for all M. Separate from adaptive PE4; t1 endpoint is SD1. Half probability t1/2 is enough for obstruction.
At1/2 actual mean retained cofactor-one head H(M)=Σ_{d≤M} μ(d)K_d(M)/2^ω(d). Exact finite variance now PROVED H²≤E_half. Average source weights change before convolution. PE5 NUMERICALLY REJECTED with dependency-closed analytic paper no-go; assembled Lean analytic no-go remains PENDING. Do not claim formal refutation or retire card yet: strongest actual survivor H not O(M) still to formalize. PE4 and SD1 not refuted.

## New verified Lean (20 public theorems)
`formal/GaloisForLFunctions/RHTower/UniformPrimeSubsetEnergy.lean` (232lines):12 public theorems. Uniform subset mean, subsetLabelFibre(I,a,c,P,R)=Σi if a(i)\P=R then c(i) else0, energy=ΣR⊆U fibre². Exact containment probability c/2^card(T), finite sum interchange, variance identity, mean-square inequality, pair collision iff symmdiff⊆P, average kernel Σij cicj/2^card(ai∆aj), mean head Σi ci/2^card(ai), mean-head²≤averageenergy, empty diagonal under injective labels, full signed square, literal insert-coordinate signed merger, all-subset source conservation. Namespace RHTower. Imports Mathlib.Data.Finset.Interval, SymmDiff, Tactic. Generic hypotheses are only source bookkeeping, not RH assumptions.
`formal/GaloisForLFunctions/RHTower/MobiusDivisorBernoulliPrimeEnergy.lean`:8 public theorems. Imports generic and existing MobiusDivisorAbelQuadraticDiagonal plus Nat.Squarefree. Uses actual primes rangeM.filter Prime and squarefree indices Icc1(M−1).filter Squarefree. Nonsquarefree and terminal channels proved zero, prime labels injective via Nat.prod_primeFactors_of_squarefree. Public:
- mobiusDivisorSelectionEnergy_empty (original Σd≤M C_d²)
- mobiusDivisorSelectionEnergy_full (original signed sum²)
- mobiusDivisorHalfSelectionHead_eq_mean
- mobiusDivisorHalfSelectionHead_sq_le_energy
- mobiusDivisorHalfSelectionEnergy_eq_kernel
- mobiusDivisorSelectionFibre_insert (literal signed + merger)
- mobiusDivisorSelectionFibre_sum
- mobiusDivisorHalfSelectionHead_eq_divisor_abel
Also defines halfSelectionMoebiusWeight d = (μ(d):Real)/2^d.primeFactors.card. Last theorem exact H=Σk∈Icc1(M−1) (√(k+1)−√k) Σd≤k halfWeight(d)D(k/d).
Both exact leaves passed `lake env lean file -o exactolean` after scratch. All20 public theorems axiom-audited ONCE this turn: only propext, Classical.choice, Quot.sound. No experimental results as premises. Both wired once in RHTower umbrella; no umbrella/dependency build or lake build. DO NOT reaudit old axioms/rebuild absent edits. Index refreshed. All own sessions terminal; zero own Lean processes confirmed; ten own /tmp scratches/logs removed.
Global formal lint ran once and FAILED on TEN unrelated concurrently added unwired HTGeometry.PolynomialODEOddCompact* modules: Cubic, Model, Remainder0..6, SourceJets. Initial commentary mistakenly counted only finalthree lines; full result confirmed ten and certificate records ten. Neither CCM-FU new module flagged. No foreign module changed. Check current state before repeating lint, others may finish wiring.

## Numerics: new frozen question, <1sec each
`docs/drafts/pipeline/2-fully-proven/computations/ccm-fu-bernoulli-prime-energy-2026-09-07/` contains screen.py/screen.json, audit.py/direct-audit.json, README.
Screen reuses old saved full-subset energies through32 (half-average/Q at32≈.4007733). Then PREDECLARED dyadic mean-head screen M2^5..2^18 using actual exact quotient-block channel formula. First DYADIC mean-square violation M1024: H≈−41.3155330400005004, Q≈1249.1097676908448, H²/Q≈1.3665518551944024, finalS²/Q≈.11030981569296. At262144 H²/Q≈30.40823. Do not call1024 first integer failure.
Independent80-digit audit directly evaluated every defining half-order sum at1024 (new trial factorizations, divisor counts, direct D), confirming H²−Q≈457.8635026885281742. Screen .61sec, audit .47sec. No expensive greedy rerun/exponential enumeration. Guidance only, no formal numerical counterexample. Do not rerun without new question.

## Dependency-closed analytic paper proof, not yet Lean
Let a(n)=μ(n)/2^ω(n), b(n)=log n−τ(n)+2γ. D(q)=Σn≤q b(n). g=a*b, G0(x)=Σn≤x g(n). Finite identity H(M)=Σk<M (√(k+1)−√k)G0(k) is now Lean.
W(x)=∫1^x G0(floor u)/(2√u)du. W(M)=H(M); between integers W lies between endpoint values. Hypothetical H=O(M) gives W=O(x). For Res>1, twice Abel integration gives L(g,s)=2s(s+1/2)∫1∞W(x)x^(−s−3/2)dx. This would be holomorphic Res>1/2.
B(s)=L(b,s)=−ζ'(s)−ζ(s)^2+2γζ(s)=s∫1∞D(floor x)x^(−s−1)dx. Existing `abs_primeFreeDivisorDefect_le` is actually |D(n)|≤24√n, stronger than paper's first rough logbound; makes B holomorphic Res>1/2. B1>0 source-derived: w_n=1/n−1/(n+1), A_n=Σk≤n D(k)≥0 (already Lean), D1>0. B1=ΣA_n(w_n−w_(n+1))≥D1/3>0. Boundary A_Nw_N→0 from O(N^1.5), series absolute.
Euler identity (1−X/2)^2=(1−X)(1+X²/[4(1−X)]). Therefore L(a,s)^2=R(s)/ζ(s), R=∏p(1+p^(−2s)/(4(1−p^(−s)))). R holomorphic near1 via absolute ∑p^(−2σ), σ>.5; R1>0. Then holomorphic continuation of L(g,s)^2=B(s)^2R(s)/ζ(s) near1 would have a SIMPLE zero at1. A holomorphic square has even zero order (or derivative0 after value0); RHS derivativeB1²R1>0 by zeta residue1. Contradiction. No fractional Tauberian theorem needed.
Hence H notO(M), cofinally beyond every linear budget. H²≤Ehalf and Q≤722M² exclude every fixed multiple originalQ for averageEhalf. This does NOT refute adaptivePE4 or finalSD1.

## Next actual Lean chain
1. Construct absolute harmonic B boundary from |D|≤24√n and prove B1≥D1/3>0 via known all-prefix positivity.
2. Construct a and exact squared Euler factorization; prime-square positive correction R holomorphic and R1>0.
3. Mellin landing of W under temporary linear-bound contradiction assumption, concluding holomorphic L(g).
4. Simple-zero-of-square contradiction and unconditional no-linear-bound actual-source theorem; energy corollary. Preserve strongest positive actual growth statement before retiring PE5.
Reusable CORPUS source inspected: `SquarefreeConvolutionHalfCofinalScheduleNoGo.lean:51` not_exists_bound_squarefreeHalfDirichletPartialSum_boundaryExteriorPoint uses bounded partial sums + `DirichletUniformAbel.differentiableOn_dirichletSum` (module/name, not qualifiednamespace) + source Euler square + residue unit + analytic uniqueness. Its coefficient is a DIFFERENT squarefree convolution half (square ζ/ζ2), do not substitute source identities. `SquarefreeConvolutionHalfSelbergDelange.lean` explicitly leaves fractional Wiener–Ikehara as a Prop, not a proved theorem; avoid using it. `PrimeMobiusPhaseFidelity` normalized probabilities are not this source; `Sieve/LcmQuadraticDiagonalization` is distinct kernel.

## Docs
New3-formalized `ccm-fu-bernoulli-prime-energy-identities.md` certifies ONLY finite20theorems, not numeric/all-scale no-go. PE5 paper/protocol card inprogress. Updated PE4, SD1, frontiercurrentstate, MUST217 route-independent variance/selection distinction. Newlinks allresolve; single imports and oleans verified.

## Lean lessons
Finset.Icc_eq_filter_powerset + card_Icc_finset hT immediately count supersets; pow_sub₀2 hne(card_le_card hT), field_simp gives probability. Do not simp with sum_comm (loops); use rw[sum_comm] then sum_div. Rewrite polynomial point identity BEFORE unfolding uniformSubsetMean to preserve match. Rewriting iff inside if may fail dependent Decidable motive; simp only[←iff] works. subset_iff binds element implicitly, so h(hmembership), not h x hmembership. Eta-expand (fun P=>energy ...P) before simp_rw its pointwise theorem. Use explicit args for uniformSubsetMean_labelHead_sq_le_energy; adding named c after four anonymous positional args caused failed elaboration and a slow scratch run. `Finset.sum_comm'` plus intro d k; simp only[mem_Icc];omega proves triangular nested sum swap directly (used source Abel landing). All new names checked in this toolchain via scratch. Serena write_memory uses memory_name.
