# Theta Schur quartic spectral decay equivalence

- **ID:** GTA-PQ4-SC2
- **Stage:** 2-fully-proven
- **Type:** THEOREM (Lean; stage-3 lint promotion pending unrelated umbrella repair)
- **Source:** `rh-current-frontier-map.md` · route GTA (`COF + ORIENT`)
- **Statement:** RH is equivalent to uniform convergence to zero of positive quartic charge across every Schur packet of the actual corrected finite theta stages.

## Goal
Replace one-way cofinal-smallness endpoint by an exact asymptotic classification.  Forward direction
must control growing, nonnormal finite matrices without labeling eigenvalues; reverse direction uses
the already proved persistent charge floor caused by any off-real Xi zero.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, exact build green, axiom audit and lint pass
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
**[PROVED HERE]** Corpus-led route uses honest theta determinant convergence and Schur
Hilbert--Schmidt energy.
Uniformly bound all stage energies from Hilbert--Schmidt convergence.  For fixed `δ,η>0`, place
bounded Schur nodes satisfying `normSq ≥ δ` and `Im² ≥ η` in one compact spectral window.  Inversion
maps that window compactly away from real normalized-Xi zeros under RH.  Compact-open convergence
makes finite determinants eventually zero-free there, contradicting the reciprocal determinant
zero contributed by any such Schur node.  The finite spectral split theorem then forces charge
uniformly to zero.  Conversely, uniform decay implies cofinal smallness, which already implies RH.

## Conjecturing loop
- `[GTA-PQ4-SC2.1]` Use individual compact-operator eigenvalue branches. Rejected: unnecessary
  labeling and nonnormal multiplicity infrastructure.
- `[GTA-PQ4-SC2.2]` Use compact zero-free windows for reciprocals of all bad eigenvalues at once.
  Scratch Lean proof closed uniform transverse localization.
- `[GTA-PQ4-SC2.3]` Combine localization with dimension-free quartic spectral split. Scratch Lean
  proof closed uniform charge decay under RH; uniform decay implies cofinal smallness and the prior
  persistent-floor theorem gives the reverse implication.

## Novelty audit
- Internal corpus search on 2026-08-27 found local-uniform zero-count transfer, one fixed central
  zero-free disk, Schur diagonal Hilbert--Schmidt bounds, and the one-way cofinal-smallness endpoint,
  but no compact reciprocal-window localization or uniform all-packet charge-decay equivalence.
- External searches through 2026-08-27 found no matching Schur/quartic criterion. Bornemann's
  arXiv:0804.2543 treats numerical Fredholm determinants; Connes--Consani arXiv:2006.13771 treats
  Weil positivity and cutoff compression; arXiv:2605.20224 reports truncated-Weil numerics and says
  convergence to Riemann zeros remains open; Freedman arXiv:2606.29555 explicitly leaves its Weyl
  positivity-to-RH bridge open. None states this actual-theta uniform quartic equivalence. Novelty
  remains **UNVERIFIED**, not a priority claim.

## Lean certificate
- Module:
  `GaloisForLFunctions.RHTower.HedenmalmThetaSchurQuarticSpectralDecayEquivalence`.
- Uniform localization:
  `eventually_thetaSourceStageSchurDiagonal_im_sq_lt_of_rh`.
- Uniform decay:
  `eventually_thetaSourceStageSchurPositiveQuarticCharge_lt_of_rh`.
- Equivalence:
  `riemannHypothesis_iff_thetaSourceSchurPositiveQuarticChargeUniformDecay`.
- `lake env lean` and exact `lake build` pass. Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- Global lint reaches only an unrelated unwired concurrent module:
  `GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenBlockConvolution`.

## Log
- 2026-08-27 — frozen after corpus search and successful compact-window Lean scratch proof.
- 2026-08-27 — `.1 → .2 → .3` loop closed; exact RH equivalence paper proof and Lean module completed.
- 2026-08-27 — moved to 2-fully-proven pending clean global lint rerun.
