# First-omission time-shear obstruction — paper asymptotic, finite law in Lean

Own CCM-FU research note. The frontier map is read-only. This is a source-specific necessary law for all-age payment, not an RH proof. Corpus novelty search found no matching theorem; external priority remains unverified.

## Theorem

Fix real constants `0<a<b<min(2a,1)` and `δ>0`. Let `M_j→∞` be integer cutoffs and `P_j` any processed-prime cores at those cutoffs. Assume, for every large `j`,

1. every prime `p<a M_j` is in `P_j`, and
2. at least `δ M_j/log M_j` primes in `[aM_j,bM_j]` are **not** in `P_j`.

Put `m_j=⌊bM_j⌋`. Then, for some fixed `c>0` and every large `j`, the literal energy of the **same** core at the earlier cutoff satisfies

`mobiusDivisorSelectionEnergy m_j P_j ≥ c M_j³/(log M_j)²`.

In particular no such core family has one quadratic old-cutoff budget. The processed core may be arbitrary above the hard lower edge; this is not a prime-prefix theorem.

## Proof

Choose `ε>0` so small that `a<b−ε` and, by the prime number theorem, the number of primes in `((b−ε)M,bM]` is eventually less than `(δ/2) M/log M`. At least `(δ/2)M/log M` omitted primes therefore lie in `[aM,(b−ε)M]`. At the old cutoff `m=⌊bM⌋`, all these primes are active and have quotient

`m/p ∈ [b/(b−ε)+o(1), b/a+o(1)] ⊂ (1,2)`.

The literal Abel source `C=criticalContinuousAbel` is continuous and **strictly positive** throughout `(1,2]`: `C(y)=(√y−1)(2γ−1)`. Thus `C(m/p)≥c₀>0` on the selected compact quotient interval. Each selected prime contributes at least `c₀√(aM)` to the omitted-prime head, giving a positive total `≫M^(3/2)/log M`.

No omitted active prime can contribute negatively: property 1 gives `p≥aM`, while `p≤m`, so `1≤m/p≤b/a+o(1)<2` and `C(m/p)≥0`. The completed-head term `C(m)=o(M^(3/2)/log M)` by the corpus's strong `ψ` PNT. For large `M`, property 1 also covers every prime with `p²≤m`, so the arbitrary terminal-core identity applies exactly:

`H(m,P_j)=C(m)+Σ_{p≤m,,p∉P_j} √p C(m/p) ≥ c₁ M^(3/2)/log M`.

The terminal energy identity contains `H²` as a nonnegative summand; squaring proves the theorem. Rounding at `m=⌊bM⌋` changes at most an `o(1)` quotient margin and one endpoint prime.

## Whole-route meaning

A direct same-cutoff corollary is more relevant to the exact CCM-FU receiver. Fix `1/2<a<b<1` and `δ>0`. If a core at cutoff `M` contains every prime below `aM` but omits at least `δM/log M` primes in `[aM,bM]`, then its **energy at `M` itself** is `≫M³/log²M`. Indeed every omitted active prime is in the first quotient cell `M/p<1/a<2`, and each omitted prime in the specified band has `√M−√p≥(1−√b)√M`; apply the Lean-closed finite identity, the strong-PNT source bound, and the terminal energy square. No short-band prime count or old-cutoff transfer is needed for this corollary. It rules out a fixed quadratic-budget path that clears a proportional lower-prime segment while leaving a positive-density interior upper band; it does not rule out interleaved cores with lower counter-reserves. This asymptotic corollary is paper-only.

A macroscopic omitted-prime reservoir cannot have the stated positive **hard lower edge** in scaled prime size while still paying its earlier cutoffs. Even perfect current-cutoff head cancellation cannot cure that first-activation positive interval. To evade this theorem while retaining a positive-density upper band, a schedule must also leave lower primes unprocessed (or use a different signed notion of payment); merely selecting upper macroscopic bands is insufficient. A stronger weak-limit statement that every nonzero viable omission profile has support accumulating at `p/M=0` is plausible, but it is **not** claimed by this finite-band theorem without a separate density audit.

The theorem does **not** exclude reserves with vanishing prime density, scale-free omissions, or signed old-cutoff/covariance payment. It does not prove RH. Its positive survivor is a sharp geometric design constraint on an exhaustive history: no positive-density reserve isolated above a fixed proportional processed prefix. The exact first-cell terminal-head source identity is Lean-closed in `MobiusDivisorFirstOmissionSourceLaw.lean`. The arbitrary-core same-cutoff finite band inequality is Lean-closed in `MobiusDivisorTerminalBandRigidity.lean`: `κ√M·#(unpaid p≤3M/4)/8≤|C(M)|+√E(M,P)` under terminal first-cell coverage. The PNT window count and asymptotic energy lower bound remain paper-only; the full theorem has not been Lean-checked.
