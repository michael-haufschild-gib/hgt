# Theta Schur quartic asymptotic zero transfer

- **ID:** GTA-PQ4-LSC
- **Stage:** 2-fully-proven
- **Type:** THEOREM (Lean; stage-3 lint promotion pending unrelated umbrella repair)
- **Source:** `rh-current-frontier-map.md` · route GTA (`COF + ORIENT`)
- **Statement:** If arbitrarily late actual signed theta stages admit a Schur packet with arbitrarily small positive quartic charge, then RH; conversely, every off-real Xi zero forces an eventual positive charge floor for every packet.

## Goal
Replace exact charge zero at every finite theta stage by an asymptotic scalar condition.  The
condition is source-pure after Schur transport: it concerns actual finite corrected theta matrices,
not Xi zeros.  Compact-open determinant completion is already unconditional in the corpus.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: exact Lean module and build pass; axiom audit pass; global lint blocked by unrelated concurrent unwired modules
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
For a finite matrix `M` with Schur packet `S`, a zero `z != 0` of `det(1-zM)` forces one
diagonal entry of `S.T` to equal `z^-1`.  Nonnegativity of every packet summand therefore gives the
quantitative lower bound

`sourcePairPositiveQuarticCharge (z^-1).re (z^-1).im <= charge(S)`.

**[PROVED HERE]** Normalized finite theta determinants converge locally uniformly to normalized
`XiC`, so an XiC zero persists in one fixed small closed ball.  At an off-real zero `z`, reciprocal
local charge is strictly positive and continuous on a sufficiently small ball avoiding zero.  Thus
every Schur packet of every sufficiently late stage has charge bounded below by one fixed positive
constant.  Cofinal smallness supplies, beyond any cutoff and below that same constant, a stage and
packet. Contradiction. Hence every XiC zero is real and RH follows.

This proves the stronger persistent-floor law independently of the RH endpoint:

`XiC z = 0 ∧ z.im != 0 → ∃ c > 0, ∀ᶠ k, ∀ S, c < charge(k,S)`.

## Conjecturing loop
- `[GTA-PQ4-LSC.1]` Exact zero at every stage. Already Lean-proved but source burden too rigid.
- `[GTA-PQ4-LSC.2]` Decay of one arbitrarily selected Schur packet. Plausible, but introduces a
  noncanonical choice and requires packet-invariance infrastructure.
- `[GTA-PQ4-LSC.3]` Uniform decay over all Schur packets. True but still unnecessarily strong.
- `[GTA-PQ4-LSC.4]` Cofinal smallness: for every `ε > 0` and cutoff `N`, one `k ≥ N` and one Schur
  packet have charge `< ε`. Proved; strongest source-side weakening exposed by eventual Hurwitz
  persistence. Exact all-stage vanishing implies it in Lean.

## Novelty audit
- Internal corpus search on 2026-08-27 found qualitative positive charge from a nonreal divisor and
  finite-prime energy zero transfer, but no reciprocal-zero quantitative quartic lower bound or
  asymptotic theta-stage quartic criterion.
- External exact-phrase and concept searches through 2026-08-27 found no reciprocal-Schur quartic
  floor or cofinal-smallness RH criterion. Bornemann's Fredholm work concerns numerical convergence;
  Sierra's spectral model is a tuned Rindler/Dirac realization; Connes--Consani's scaling Hamiltonian
  is a distinct trace/geometry program; arXiv:2606.29555 studies a Weyl-positive Volterra quotient
  and explicitly leaves its RH bridge open. Novelty remains **UNVERIFIED**, not a priority claim.

## Lean certificate
- Generic quantitative theorem:
  `sourcePairPositiveQuarticCharge_inv_le_finiteMatrixSchurPositiveQuarticCharge`.
- Persistent floor:
  `eventually_thetaSourceStageSchurPositiveQuarticCharge_gt_of_XiC_zero_im_ne_zero`.
- RH endpoint:
  `riemannHypothesis_of_thetaSourceSchurPositiveQuarticChargeCofinallySmall`.
- Weakening witness:
  `thetaSourceSchurPositiveQuarticChargeCofinallySmall_of_flag`.
- Module: `GaloisForLFunctions.RHTower.HedenmalmThetaSchurQuarticAsymptoticZeroTransfer`.
- `lake env lean` and exact `lake build` pass. Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- 2026-08-27 global `formal_tools.py lint` failure is outside this card: five concurrently added
  owned modules were not yet imported by `RHTower.lean`; no forbidden declaration was reported here.

## Log
- 2026-08-27 — created directly in 1-in-progress after corpus-led conjecture freeze.
- 2026-08-27 — `.1 → .2 → .3 → .4` heavy loop completed; paper proof and Lean module closed.
- 2026-08-27 — moved to 2-fully-proven pending clean global lint rerun.
