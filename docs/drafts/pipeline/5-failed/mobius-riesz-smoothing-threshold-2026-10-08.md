# Exact smoothing threshold for finite Möbius–Riesz packets

Status: fixed-order universal finite-prime packet positivity retired; sharp positive survivor fully proved on paper and formalized in Lean.

## Final result and scope

For every nonempty finite set P of primes, the normalized literal Möbius Riesz packet has an everywhere-nonnegative r-fold logarithmic primitive if and only if P.card - 1 ≤ r. Below that threshold a negative value occurs on the positive ray. Consequently no single finite smoothing order gives nonnegativity for all finite prime packets.

This retires only the route premise of universal finite-packet positivity after one fixed logarithmic smoothing order. It does not retire signed cancellation estimates, prove or falsify RH, or assert external novelty.

The strongest positive survivor is the exact threshold, together with the explicit tail at threshold: exp(-t) times the product of exp(a)-1 over shifts a. One order below threshold the tail is its negative. The literal arithmetic bridge preserves the square-root cutoff and identifies the full finite-prime packet with its Möbius-weighted sum.

## Final verification

- Final leaves MobiusRieszCausalCalculus.lean, MobiusRieszSmoothingThreshold.lean, and MobiusRieszPrimePacketThreshold.lean each compiled directly with lake --old env lean, exit 0, with no warnings. All three imports were added to RHTower.lean.
- A scratch #print axioms audit of all 44 public theorems compiled successfully. Every theorem uses only propext, Classical.choice, and Quot.sound.
- git diff --check for RHTower.lean passed. The corpus index was refreshed.
- Global formal lint exited 1 for nine unrelated missing umbrella imports: RHTower.ChronologicalBoseDilateCompleteness, RHTower.LeeYangDatumFirstZero, RHTower.LeeYangFirstZeroLaw, HTGeometry.ApertureConeCalculus, HTGeometry.ApertureConeWinding, HTGeometry.ApertureLogTranslation, HTGeometry.ApertureOpenHistoryIdeal, HTGeometry.BoundaryCoronaCStarAlgebra, and HTGeometry.PaperCoordinateCompression. No new module from this card was reported.
- Source-access rule for continuation: research reading is restricted to Lean corpus results from scripts/formal_tools.py research, with Lean-only output projection. Do not read web, Markdown, direct source files, or memories.

RH remains unresolved. The next route must address signed cancellation or a quantitatively controlled smoothing order that grows with prime count; the present theorem supplies no uniform estimate for either.

Goal context: unconditional RH proof or falsification remains the full objective. This investigation tests whether literal prime pairing can furnish the signed source bound. The corpus already proves one-prime positivity, a two-prime sign wall, and both signs of the full Möbius tail on every scale. A new positive survivor must preserve the literal source and quantify the smoothing cost.

Research restrictions: all research reads through `scripts/formal_tools.py research`, Lean content only. No web, Markdown reads, direct source reads, numerical experiments, heartbeat increases, umbrella builds, or concurrent foreground Lean processes. Writing this working card and compiling own leaf proofs are allowed.

Corpus audit: `CCMFUSuzukiMobiusRieszPrimeCellSign` gives `atom_eq_positivePart`, `literal_firstPrime_cancellation`, `literal_primeCell_sign_wall`, and `literal_tail_both_signs_on_every_scale`. Searches for Möbius/Riesz smoothing positivity and finite-difference integral representations did not produce this threshold theorem. Coverage includes source-only declarations and semantic-coverage warnings; no external novelty claim.

Definitions: h(t)=max(1-exp(-t),0), D_a f(t)=f(t)-f(t-a), I f(t)=integral_0^t f(u)du. For a nonempty list of positive shifts A, let K_A=D_{a1}...D_{ak}h and J_{A,r}=I^r K_A. For literal prime atoms the shifts are a_p=log(p)/2, with t=log(M/n)/2, after division by sqrt(M).

Theorem target: J_{A,r} is everywhere nonnegative if and only if k-1 ≤ r. At the first nonnegative order, J_{A,k-1}(t)=exp(-t)*product_a(exp(a)-1) for t ≥ sum A. If k≥2, then J_{A,k-2}(t)=-exp(-t)*product_a(exp(a)-1)<0 for t>sum A. Thus no fixed smoothing order repairs positivity for arbitrarily many primes.

Paper proof:
1. Continuous causal functions (zero for t≤0) remain continuous and causal after I or D_a for a≥0. I and D_a commute on this class. Moreover D_a(I f)(t)=integral_{t-a}^t f(u)du.
2. For k=1, D_a h≥0 because h is monotone. For k≥2, commute I through D_a and use the preceding identity: J_{a::A,k-1}(t)=integral_{t-a}^t J_{A,k-2}(u)du. Induction gives nonnegativity and the box-integral representation.
3. Beyond sum A, the one-prime kernel equals exp(-t)*(exp(a)-1). The same box-integral recursion multiplies the tail coefficient by exp(a)-1. This proves the exact tail formula and its strictly positive coefficient.
4. The derivative of J_{A,k-1} is J_{A,k-2}. On the open tail it is also the derivative of the explicit exponential tail, hence strictly negative. This proves failure one order below the threshold.
5. If any lower order were nonnegative everywhere, integrating it repeatedly would make J_{A,k-2} nonnegative on t≥0, contradicting step 4. Every higher order is nonnegative by causal integration. This closes both directions of the threshold.
6. Connect the finite-difference packet to actual square-root Möbius atoms, retaining cutoff and normalization. At minimum, the existing two-prime `primeCell` must be linked explicitly; extend to arbitrary finite prime sets through the literal subset expansion if no existing theorem supplies it.

Implementation plan: verify FTC/interval identities in scratch; formalize causal integration and difference calculus; formalize threshold and exact tails; attach literal prime-cell/subset bridge; compile each leaf, print axioms in scratch, wire modules, refresh index, run formal lint, clean scratches. Do not treat the smoothing result as an RH producer: its required order grows with the number of primes.

Verified: `MobiusRieszCausalCalculus.lean` compiled to its olean with `lake --old env lean -o ...`, exit 0. The threshold scratch compiled at default heartbeats, including the exact positive tail, strictly negative tail one order lower, full iff for every integration order, and existence of negative values at all insufficient orders. Two unnecessary tactic-sequencing warnings were removed before final-leaf compilation.

New corpus ingredient: `RHTower.sum_powerset_eq_tsum_moebius` in `ThetaCutoffCommutatorCofinalLimit` identifies a finite prime subset expansion with the literal Möbius sum restricted to those prime factors. Use this to connect the general packet to arbitrary finite prime sets; the two-prime bridge must agree with `MobiusRieszCancellation.primeCell` as a separate consistency check.
