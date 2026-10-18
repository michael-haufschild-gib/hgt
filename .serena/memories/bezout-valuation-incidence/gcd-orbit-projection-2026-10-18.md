# Gcd orbit projection and complete period classification — contribution008

Status: paper + Lean verified, counted once in 8/250. No open premise in public results.
Source: `formal/GaloisForLFunctions/BezoutValuationIncidence/GcdOrbitProjectionAndExactTranslationPeriods.lean`.
Card: `docs/drafts/pipeline/3-formalized/bvi-translation-stabilizers-and-gcd-orbit-projection-2026-10-18.md`.

For N,h∈ℕ and c:ℕ→ℝ, Γ_h c(e)=e*Σ[1≤d≤N;gcd(d,h)=e]c(d)/d on [1,N], zero outside.
The test-function transport identity gives Y(Γ_h c,q)=if q|h then Y(c,q) else0 for all q.
H preserved; Γ_hΓ_k=Γ_gcd(h,k); Γ_h idempotent; Γ_0 truncates and Γ_1 retains H at1.
The actual sequence satisfies S_Γ(k)=(1/N!)*Σ[j<N!]S_c(k+jh).
Complete periods: Periodic(S_c,h) iff ∀d∈[1,N],c(d)≠0→d|h.
Least positive period = finite lcm of active raw divisors, with empty support giving1.
Fixed-point criterion Γ_h c=Γ_0 c iff original signal is h-periodic.
Exact Pythagoras Q(c−Γ_h b)=Q(c−Γ_h c)+Q(Γ_h c−Γ_h b).
Best approximation is unique on projected weight functions; equality iff Γ_h c=Γ_h b.
All N,h,k and arbitrary real weights, including N=0 and h=0; c1 unrestricted.

Proof dependencies:
- Existing finite multiples-coordinate tail injectivity (001), subtraction bridge (004).
- Existing AffineSieve.coordinate/residueSignal/dft_residueSignal/sum_zmod_val.
- Existing RHTower.Sieve.dft_eq_zero_of_periodic_nontrivial_phase.
- Resonant frequencies have addOrderOf r|h iff h*r=0. DFT injectivity identifies literal orbit mean.
- Period converse tests r=N!/q, orderq, kills nonresonant Yq, then uses finite inversion.
- Totient positivity plus finite inversion proves Q-zero iff all within-level coefficients vanish.
Do not count generic finite Fourier facts, the prior inverse, existing cycleAverage_fracAtom, or direct projection corollaries as new research.

Verification: original named source exit0/no diagnostics;31 named declarations and17public indices matched.
All17 public axiom closures exactly propext, Classical.choice, Quot.sound.
Raw audit `logs/bvi-root-2026-10-18-gcd-projection-axioms.txt`.
Artifact installed atomically and hash/freshness checked; all26 temporary paths cleaned.
No owned jobs remain. Lint's two foreign omissions and381 large-file warnings recorded on card.
Local novelty audit is limited by reported semantic/partial coverage; no external/global novelty claim.
See `mem:bezout-valuation-incidence/research-progress-2026-10-18` and durable ledger for full progress.
