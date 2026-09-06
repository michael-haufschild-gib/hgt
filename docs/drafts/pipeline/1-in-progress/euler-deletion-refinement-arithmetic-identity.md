# Arithmetic identity for Euler-deletion refinement

- **Stage:** 1-in-progress
- **Type:** CONJECTURE SEARCH; no RH proof
- **Target:** Derive replication–Euler-dilation second-level equality from a literal nontrivial zeta zero, with all cross terms retained.

## Exact obligation

For the closed word `w_q=(1,...,1,-q)`, let `H` denote its strict Hermitian second level. The Lean theorem `eulerDeletionChronologicalWord_sigma_eq_half_of_secondRefinement` consumes

`H(repeat (q+1) w_q) = H(scale ((q+1)^(1-Re rho)) w_q)`.

The equality is not currently supplied by the zero hypothesis. The proposed full chain is zero → arithmetic refinement identity → equality of the two nonzero second-level scales → `Re rho=1/2` → RH. The arithmetic implication is the unresolved step.

For a finite weighted prefix with endpoint `A_N`, literal `p`-fold concatenation instead gives

`H(repeat p prefix_N) = p H(prefix_N) + p(p-1)/2 |A_N|²`.

At a hypothetical zero right of half, existing Lean results give `A_N→0`, a convergent second level `H_N→L`, and `Re L=-E/2<0`. The replication–dilation difference therefore tends to `(p-p^(2-2 Re rho))L`. Endpoint decay removes only the endpoint term.

## Research discipline

Corpus search supplies mechanisms for conjectures; actual statements and proof bodies determine their scope. Each attempted identity must be written before testing, with its source variables and retained boundary terms. Rejected identities do not retire the target. Numerical experiments, if useful, run only on the specified Runpod and cannot enter Lean proofs. No new conditional receiver counts as proof of the arithmetic implication.

## Current status

The arithmetic identity forcing annihilation remains open. Exact finite decomposition identities are formalized; the growing-modulus analytic decomposition has a paper derivation only. No RH proof, impossibility result, or novelty claim follows.

## Conjecture loop: mixed ordinary-sum primitive

Write `u_n=n^(-s)`, `S_N=sum_(n<=N) u_n`, `c_p=p^(1-s)`,
`D_p=(1-c_p) zeta(s)`, and `X_p(N)=S_N-c_p S_floor(N/p)`.
The zero condition is exactly `D_p=0` in the source domain.

Consider the tail-centered mixed primitive

`T_p(s)=sum_(k>=0) (X_p(k)-D_p) (k+1)^(-conj(s))`.

Unlike the self second level, its leading periodic tail has zero mean.
The exact finite insertion formula suggests retaining the correction

`J_(p,q)(s)=c_p sum_(k>=0) (X_q(k)-D_q) [sum_(r=1..p) (pk+r)^(-conj(s)) - p(pk+p)^(-conj(s))]`.

The bracket is the actual within-cell variation of the ordinary weight. Grouping finite sums by their `p`-cells gives the candidate limiting identity

`T_(pq)=T_p+p^(2-2 Re s) T_q+J_(p,q)`.

**Conjecture being tested:** at literal zeta zeros, the correction `J_(p,q)` vanishes, or its complete arithmetic commutation combination has a stronger relation than the displayed insertion identity. A vanishing assertion is not assumed. Even if supported, a further proof connecting this mixed primitive to the target self second level would be necessary.

**Why compute:** neither the complex values nor the signs of this particular mixed within-cell correction at actual zeros have been determined here by reasoning. A Runpod experiment compares cutoffs, direct correction sums, and independently assembled insertion differences, with nearby nonzero controls. It tests this precise candidate, not RH numerically.

Two earlier mechanisms were examined before this test. Simultaneous additive and multiplicative preservation of `n^(1-2 Re s)` forces neutral exponent, but no source proof supplies additive preservation. A finite orbit primitive exists only after its component charge vanishes; substituting the refinement charge makes that criterion circular. These are rejected derivations, not counterexamples to RH or retirement of the arithmetic target.

The first Runpod scan found large nonzero corrections at the first eight critical-line zeros, stable over three cutoffs. This is numerical rejection of the blanket `J=0` candidate, not a certified counterexample in Lean and not a rejection of a strict-right-only identity.

**Next conjecture:** for each dilation `p`, an amended scalar `kappa_p(s)` absorbs the correction for every source modulus: `J_(p,q)=kappa_p T_q`. This is stronger than merely fitting one pair. It is motivated by the corpus mechanism `cycleDeletionShapeBlind_iff_constant_ratio`; its applicability here is conjectural. Test all four other source moduli for each `p`, retain the best-fit residual, and verify representative sums independently at higher precision.

## Outcomes and positive survivor

The scalar repair failed numerically across the tested source moduli. Three specified two-coordinate replacements also failed: add respectively the uniform deletion mass `q-1`, the residue-cell variance coordinate `q²-1`, or the Euler amplitude coordinate `c_q-1`. None supplies the requested identity. These numerical tests reject these blanket candidates on the tested critical-line zeros; they cannot refute a claim restricted to hypothetical strict-right zeros.

The unexpected common cutoff error suggested the complete-cell asymptotic correction `(p²-1)/(12 N^(2 Re s))`. Removing it improved the numerical insertion check at both zeros and nonzeros. This is a convergence correction, not zero-specific mathematical information. Its full asymptotic proof and Lean formalization have not been claimed.

The exact finite identity survives without any numerical input or zero hypothesis:

`T_(pq)(pN)=T_p(pN)+|c_p|² T_q(N)+J_(p,q)(N)`.

For three dilations it forces the exact correction law

`J_(p,q)(qN)+J_(pq,r)(N)=|c_p|² J_(q,r)(N)+J_(p,qr)(qN)`.

### Paper proof of the finite survivor

The division identity `floor(floor(k/p)/q)=floor(k/(pq))` and multiplicativity of `c_p` give

`(X_(pq)(k)-D_(pq))=(X_p(k)-D_p)+c_p(X_q(floor(k/p))-D_q)`.

Multiply by `(k+1)^(-conj(s))` and sum through `pN`. Partition the inserted sum by `k=pj+r`, `0<=r<p`. On each complete cell, subtract and add `p[p(j+1)]^(-conj(s))`. The subtracted contribution is precisely the displayed `J`; the endpoint contribution is `|c_p|² T_q(N)`. No limit or rearrangement of an infinite series enters. Applying this finite law to `(pq)r` and `p(qr)` at the same outer cutoff and cancelling common terms proves the weighted cocycle.

The centering can be any complex number `Z`, with `D_p=(1-c_p)Z`. Thus this law holds before a zero is selected, including when `Z=0`. Its associativity does not erase its nonzero correction or replace `|c_p|²` by `p`.

**Lean survivor:** `formal/GaloisForLFunctions/RHTower/EulerDeletionMixedRefinementCarry.lean`, namespace `RHTower.DeletionMixedRefinement`, theorems `mixedPrefix_mul` and `cellCorrection_cocycle`. Scratch and published-source `lake env lean` checks passed. The serialized final leaf build passed; no umbrella was built. All eight public theorem axiom audits returned only `propext`, `Classical.choice`, and `Quot.sound`. The leaf is wired into `RHTower.lean`, index refreshed, and global formal lint passed with existing large-file warnings. No owned Lean process remains, and the Runpod process check found no process using the experiment directory.

**Scope retained:** no route is retired; no numerical failure is labelled a Lean counterexample. The original arithmetic annihilation remains open. The next mathematical obligation must use more than the finite insertion/cocycle identities, or prove a genuinely strict-right zero-specific constraint on the full correction. No such constraint has been produced here.

## Search and experimental evidence

The companion `euler-deletion-refinement-arithmetic-identity-searches.json` preserves 49 mechanism searches with their query interpretations, totals, module caps, and exploration hits. This is broad brainstorming coverage, not an exhaustive corpus audit or proof of novelty. Selected proof bodies were inspected with `rg` and direct reads, including two-product rigidity, orbit-charge exactness, geometric primitives, star-defect composition, scalar insertion ratios, and finite sign-pairing mechanisms. Search hits belonging to excluded RH machinery were not adopted as proof steps.

[Runpod report, scripts and results](../2-fully-proven/computations/euler-deletion-mixed-refinement-carry/REPORT.md) retain the tested formulas, parameters, controls, cutoff diagnostics, and independent high-precision check.

## Growing-modulus conjectures

The next test retains the literal centered primitive and varies its deletion modulus. The corpus mechanisms inspected for this question include invariant carry current, finite scaling stabilizers, and discrete second-difference rigidity. Their proofs require, respectively, an invariant measure with an integrable lift, a rational function fixed by the scalings, or integer-valued traces. None of those source requirements has been established here. They are not imported as RH premises.

For `0<sigma=Re(s)<1`, define `alpha=2-2 sigma`. A direct rescaling of the literal sum suggests

`T_p(s)/p^alpha -> K(s) = zeta(2 sigma-1)/(1-conj(s))`.

This is a conjecture, including at `sigma=1/2`, not a proved limit. The candidate continuum remainder is `E_s(x)=x^(1-s)/(1-s)-S_floor(x)(s)+zeta(s)`. Its jumps must remain in an integration-by-parts argument; discarding them changes the proposed constant. The leading constant is expected at nonzeros as well, so it cannot itself be the missing zero-specific law.

**Conjecture G1:** after removing this leading term, the growing contribution is `|zeta(s)|^2 p^(1-s)`. Determine whether the coefficient or exponent is wrong before using it. **Conjecture G2:** at literal zeros the remaining modulus-dependent term is bounded. **Conjecture G3:** if G2 survives, the large-source-modulus correction `J_(p,q)` has an exact zero-specific limiting law that supplies more than the original endpoint equation. G3 is the desired implication to investigate, not a consequence asserted from G1 or G2.

The Runpod test will compare zeros, horizontal shifts, and a nonzero critical-line control. It retains multiple ordinary cutoffs and records every subtraction. Numerical agreement will not establish any of these conjectures or enter a Lean proof.

### Growing-modulus outcome

G1 led to the complete decomposition in [the growing-modulus derivation](euler-deletion-growing-modulus-decomposition.md). The predicted `|zeta(s)|² p^(1-s)` term survives the independent checks and follows in that paper argument. G2, when asserted at critical-line zeros, failed: a universal real term `-(1/2)log p` remains. For strict-right zeros the remainder is bounded but its real limit is `-zeta(2 Re(s))/2`, not zero. G3 therefore produced a zero detector rather than a new location constraint: boundedness of `J_(p,q)` as `q` grows is equivalent to the original zero condition in that strip, and its limiting constant is retained.

The new finite Lean statements are `centeredBlockSum_eq_endpoint_sub_pairing`, `mixedPrefix_eq_ordinary_endpoint_pairing`, and `ordinaryMixedPrefix_quadratic_identity`, in the existing `EulerDeletionMixedRefinementCarry` module. The exact infinite decomposition is formalized in `EulerDeletionInfiniteDecomposition` (`infiniteMixed_eq_decomposition`), including ordinary-cutoff convergence, absolute convergence of its actual remainder series, and the critical logarithm. Its growing-modulus asymptotics and the separate real-part identity remain paper results; the decomposition is a [BRIDGE] and does not replace the missing arithmetic vanishing conjecture. [Runpod report](../2-fully-proven/computations/euler-deletion-growing-modulus/REPORT.md) preserves numerical evidence separately. The missing RH implication remains open; neither an annihilating identity nor a proof of its impossibility was obtained.

Verification: scratch and published-source `lake env lean` passed; the serialized final leaf build passed; the three new theorems and the two existing mixed-refinement capstones use only `propext`, `Classical.choice`, and `Quot.sound`. The existing umbrella import remains in place; index refresh and global formal lint passed, with existing large-file warnings. No owned Lean process or Runpod experiment process remained after checks. The companion `euler-deletion-growing-modulus-searches.json` retains 19 of the mechanism searches from this loop, including their caps; it is not an exhaustive corpus audit.
