# CCM-FU: signed mass balance obstructs the corrected coarea action

- Type: derived obstruction and sharp positive decomposition.
- Status: obstruction and sharp positive decomposition kernel checked;
  14 new public theorems, targeted final builds passed. RH remains unproved.
- Chain: actual source → uniform quadratic retained-energy control through
  exhaustive prime processing → O(M) Abel bound → CCM-FU → RH.
- Frontier map read only. The raw-energy bound and RH remain open.

## Exact source constraint [PROVED HERE]

Use the actual signed source C_d. Put U=Σ|C_d|, S=ΣC_d, and let T be
total active late-prime mass. At a processed state P, let t be consumed
late mass, r=T-t remaining late mass, a original absolute head mass,
and E_late the exact remaining late singleton square reserve.

Remove only the unprocessed active late singleton cells. The retained
cells, including the head, have total absolute mass U-r and signed mass
S+r. The latter identity uses that every removed late coefficient is
negative. The corrected action is exactly

    H_corrected = a Σ_retained F_R²/A_R + E_late.

Weighted Cauchy therefore gives

    a(S+r)² ≤ (U-r)(H_corrected-E_late).

In particular, since E_late≥0, r≥0, H_corrected≥0, and a≥t,

    t(S+r)² ≤ U H_corrected.

This lower bound permits arbitrary cancellation within every mixed
fibre. No unproved estimate on an individual mixed fibre is needed.

## Every-order obstruction [PROVED HERE]

Along every complete one-index insertion chain, consumed late mass
crosses T/2 in jumps at most D=(3/5)sqrt(M). Once D≤T/2, some prefix
has T/4≤t≤3T/4, hence also T/4≤r≤3T/4. The existing unconditional
source limit S(4N)/T(4N)→0 gives |S|≤T/8 eventually. At that prefix,
S+r≥T/8 and t≥T/4, so

    T³ ≤ 256 U H_corrected.

The corpus gives U(M)≤(3/5)M sqrt(M) and, eventually,
T(4N)≥N sqrt(N)/(80 log(2N)). Consequently the forced prefix action
divided by M² grows at least like a fixed positive multiple of
N/(log(2N))³, which tends to infinity. Thus the corrected coarea
action also cannot have a uniform quadratic ceiling along any complete
prime order. The correction repairs the old artificial late-diagonal
cost, but leaves this independently forced signed-mass cost.

## Positive survivor: the exact unavoidable component [PROVED HERE]

For any finite cell collection W, let V=Σ_W A_R and Y=Σ_W F_R.
Zero A_R forces zero F_R. With the zero-denominator convention,

    Σ_W F_R²/A_R
      = Y²/V + Σ_W (F_R-(Y/V)A_R)²/A_R.

The second term is nonnegative and vanishes exactly when every cell
has F_R=(Y/V)A_R. This separates the forced signed-mass component
from the remaining variation of signed densities. It is sharp, handles
zero-mass cells, and identifies the equality configuration.

For the retained cells above, V=U-r and Y=S+r. Multiplying the exact
decomposition by a and restoring E_late gives the complete corrected
action, including its unavoidable rank-one component. A future useful
comparison must retain the raw cell squares at a finer scale; merely
improving mixed-cell cancellation cannot violate this conservation law.

## Corpus audit and no-go closure

Broad repository searches explicitly used OR (`--any`), including
martingale, discrepancy, rearrangement, cancellation, coupling, coarea,
weighted variance, mass conservation, and fibre sums. They exposed the
actual source conservation theorem, physical-fibre variance laws, and
the quantitative late-prime source asymptotics. The obstruction above
combines their literal arithmetic quantities; it does not substitute a
toy source or hypothesize the desired cancellation.

- Killing mechanism: retained signed mass S+r forces a positive component
  of corrected conditional energy at every state.
- Strongest positive survivor: exact weighted variance decomposition,
  sharp equality classification, and actual corrected-action identity.
- Lean status: exact decomposition, equality classification, actual mass
  balance, finite barrier, and unconditional every-order obstruction
  formalized. No experiment was needed for this predictable consequence
  of the exact source laws.

## Formal certificates

- [MobiusDivisorFibreCoareaVariance](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorFibreCoareaVariance.lean):
  three theorems. `mobiusDivisorFibre_coarea_cauchy` handles arbitrary
  finite actual cell collections, including zero masses;
  `mobiusDivisorFibre_coarea_variance` gives the exact decomposition;
  `mobiusDivisorFibre_coarea_variance_zero_iff` classifies equality.
- [MobiusDivisorCorrectedCoareaMassBalance](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorCorrectedCoareaMassBalance.lean):
  seven theorems. Complete absolute and retained signed/absolute sums are
  conserved exactly. `mobiusDivisorCorrectedCoareaAction_eq_variance`
  identifies the forced component and remainder;
  `mobiusDivisorCorrectedCoareaAction_mass_balance` proves
  `t(S+r)²≤U H_corrected` without a mixed-cell hypothesis.
- [MobiusDivisorCorrectedCoareaOrderBarrier](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorCorrectedCoareaOrderBarrier.lean):
  four theorems. `exists_prefix_mass_quarter_band` supplies the prefix;
  `exists_mobiusDivisorCorrectedCoarea_prefix_mass_barrier` proves
  `T³≤256 U H_corrected` under explicit finite source bounds;
  `eventually_mobiusDivisorLatePrimeMass_cube_gt` discharges the growth
  requirement from actual source asymptotics. The capstone
  `eventually_every_mobiusDivisorCorrectedCoarea_order_exceeds_quadratic`
  quantifies unconditionally over every complete one-index insertion
  chain, including arbitrary interleaving and repeated indices.

## Verification

All new scratch proofs and installed leaves passed `lake env lean`.
Only their required oleans were emitted. One external scratch audit
checked the 14 new public theorems exactly once: only `propext`,
`Classical.choice`, and `Quot.sound`. No old theorem was re-audited.
No numerical result or new experiment enters this work.

Final exact-module `lake build` audits passed sequentially in an isolated
temporary package with byte-identical sources and the repository toolchain.
The final leaves compiled in 4.0 seconds, 4.8 seconds, and 6.8 seconds.
Cache-only dependency packages exposed existing oleans; only the three
new leaves compiled. Initial missing-manifest messages concerned those
temporary packages. Final Lean leaves produced no warnings or tactic
diagnostics. No full, umbrella, or dependency-source build ran.

All three leaves are imported by RHTower. Indexes were regenerated.
`scripts/formal_tools.py lint --check-generated` currently fails solely
because three unrelated modules lack umbrella reachability:
`FokasLenellsContourJost`, `FokasLenellsContourScattering`, and
`FokasLenellsContourSymmetry`. No passing global lint gate is claimed.
Own source-copy, unique-import, proof-debt, whitespace, and card-link
checks passed. Owned scratch files and the temporary audit package were
removed; no owned Lean process remains. The frontier map was read only.
