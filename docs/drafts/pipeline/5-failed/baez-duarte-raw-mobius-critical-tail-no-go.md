# Raw Möbius Baez--Duarte critical-tail obstruction

- **ID:** NBBD-RMCT
- **Stage:** 5-failed
- **Type:** PROVED NO-GO WITH FORMALIZED POSITIVE SURVIVOR
- **Source:** `rh-current-frontier-map.md` NB/BD branch (read-only ledger)
- **Statement:** Canonical raw Möbius full-error decay forces an impossible little-o square-root harmonic charge; determine and formalize the sharp surviving tail obstruction.

## Goal
Decide the literal complementary-tail premise for the canonical raw Möbius modular approximants. If false, prove more than its negation: identify the sharp critical-scale lower obstruction and the coefficient correction forced by critical-line zeta zeros.

## Gates
- [x] 0 → 1  in-progress: source-pure statement, exact corpus reduction, falsifiable boundary mechanism
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, exact module build green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper and external novelty review

## Corpus-led conjecture loop
- **NBBD-RMCT.1:** `bdMobiusFullErrorEnergy → 0` forces `N · deningerHarmonicPartial N ^ 2 → 0` and hence `sqrt N · |deningerHarmonicPartial N| → 0`. First implication already exists in Lean; square-root normalization remains to package.
- **NBBD-RMCT.2:** Little-o square-root harmonic charge forces little-o half-power decay of the canonical discrete Möbius--Laplace source.
- **NBBD-RMCT.3:** Little-o half-power source decay makes `r · Mellin(source)(rho+r) → 0` at every critical-line point. Combined with the corpus Mellin--zeta identity, differentiability of the pole-filled zeta factor, and existence of a critical-line zero after the RH consequence, this is contradictory.
- **NBBD-RMCT.4:** Therefore raw full-error decay and canonical complementary-tail decay are impossible. Seek strongest survivor: a frequent/limsup positive critical-scale floor rather than a restated nonconvergence theorem.

## Approach
Reuse `BaezDuarteMobiusPrefixApproximation`, `MobiusLaplaceBoundaryMultiplicity`, and `XiHeatCassiniWoldCriticalGraphNoGo`. Build only missing little-o Abel transport. At every failed strengthening, retain exact boundary law exposed by failure.

## No-go closure
- **Exact killing theorem/mechanism:** `[PROVED HERE]` Critical energy decay forces `M(N)=o(sqrt N)`, hence vanishing critical Möbius--Laplace profile and vanishing normalized radial Mellin residue; a critical zeta zero forces the same residue to retain the nonzero Gamma boundary value.
- **Strongest positive survivor:** `[PROVED HERE] [LEAN]` Fixed positive cofinal floors for `N · deningerHarmonicPartial N ^ 2`, raw full error, and canonical complementary-tail error.
- **New insight:** Raw canonical coefficients may be too rigid at critical scale; logarithmic prefix decay does not address unavoidable critical zero residues in the complementary tail.
- **Status:** Dependency-closed paper proof and Lean formalization complete. Route retired. Exact literature novelty of the no-go is not claimed; classical work already documents failure of natural Beurling sequences. The canonical discrete complementary-tail floor and machine-checked proof appear absent from audited sources, but external expert novelty review remains required.

## Log
- 2026-08-27 — created directly in stage 1 after corpus search isolated exact boundary contradiction route; frontier map left untouched.

## Dependency-closed paper proof

Write
\[
  H_N=\sum_{n=1}^{N}\frac{\mu(n)}n,
  \qquad M(N)=\sum_{n\le N}\mu(n).
\]
The corpus full-error identity already implies that raw Báez--Duarte full-error decay forces
\(N H_N^2\to0\). The missing argument is the following chain.

1. Exact inverse Abel summation gives
   \[
     M(N)=N H_N-\sum_{n<N}H_n.
   \]
2. From \(N H_N^2\to0\), both \(\sqrt N\,H_N\to0\) and
   \(\sqrt{N+1}\,H_N\to0\). Weighted Cesàro applied to the inverse Abel identity then yields
   \(M(N)/\sqrt N\to0\).
3. Exact Abel summation for the Möbius power series, split at a finite index, gives
   \[
     e^{-y/2}F(e^{-y})\longrightarrow0,
   \]
   where \(F\) is the corpus Möbius generating function. This is the canonical critical
   Möbius--Laplace profile.
4. A sharp Abel final-value lemma says that a continuous logarithmic profile \(f(y)\to0\)
   satisfies
   \[
     r\int_0^\infty e^{-(\tau+r)y}f(y)\,dy\longrightarrow0
     \quad(r\downarrow0)
   \]
   whenever \(\Re\tau=0\). Splitting the Mellin integral at one and using the logarithmic
   head chart proves vanishing of the normalized radial Mellin residue at every critical-line
   point.
5. Profile decay implies the corpus half-decay criterion and therefore RH. An unconditional
   nontrivial zeta zero \(\rho\) is consequently placed on \(\Re\rho=1/2\).
6. At this \(\rho\), the denominator-free corpus Mellin--zeta identity gives the same radial
   limit as
   \[
     \Gamma(\rho)(\rho-1),
   \]
   which is nonzero because \(\Re\rho>0\) and \(\rho\ne1\). This contradicts step 4.

Thus \(N H_N^2\not\to0\), raw full error does not tend to zero, and—by the corpus exact
full-error/complementary-tail equivalence—the canonical complementary tail does not tend to
zero. Nonnegativity upgrades each negated limit to one fixed positive floor attained cofinally
often.

## Lean realization

- Module: `GaloisForLFunctions.RHTower.BaezDuarteMobiusCriticalTailObstruction`
- Umbrella: imported by `GaloisForLFunctions.RHTower`
- Core transport:
  - `sieveMertensM_eq_nat_mul_deningerHarmonicPartial_sub_sum`
  - `tendsto_sieveMertensM_div_sqrt_zero_of_critical_energy`
  - `tendsto_mobiusLaplaceCriticalProfile_zero_of_critical_energy`
- Boundary contradiction:
  - `not_tendsto_mobiusLaplaceCriticalProfile_zero_of_critical_zeta_zero`
  - `not_tendsto_nat_mul_deningerHarmonicPartial_sq_zero`
- Route endpoints:
  - `not_tendsto_bdMobiusFullErrorEnergy_zero`
  - `not_tendsto_bdMobiusComplementaryTailErrorEnergy_zero`
- Positive survivors:
  - `frequent_harmonic_energy_floor`
  - `frequent_bdMobiusFullErrorEnergy_floor`
  - `frequent_bdMobiusComplementaryTailErrorEnergy_floor`

## Verification audit

- Direct check: `lake env lean GaloisForLFunctions/RHTower/BaezDuarteMobiusCriticalTailObstruction.lean` — PASS.
- Exact final build: `lake build GaloisForLFunctions.RHTower.BaezDuarteMobiusCriticalTailObstruction` — PASS (`10003/10003`).
- Axiom audit for all three no-go endpoints and all three floor survivors — PASS; dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.
- `git diff --check` on module, umbrella, and card — PASS.
- Global formal lint reached unrelated pre-existing/uncommitted unreachable-module errors in `RHTower.Sieve` and `HTGeometry`; it did not report this module as unreachable and reported no forbidden declaration in it.

## Literature and novelty audit

- Báez-Duarte, *Arithmetical Aspects of Beurling's Real Variable Reformulation of the Riemann Hypothesis* (2000), already shows that natural pointwise/\(L^1\) approximants can fail in \(L^2\).
- Auil, *The Nyman--Beurling criterion for the Riemann hypothesis* (2004), proves nonconvergence of an iterative natural Beurling sequence in \(L^2\).
- Báez-Duarte's strengthened criterion and later discrete formulations establish the surrounding natural-span framework.
- Gallardo-Gutiérrez--Seco (2025) explicitly distinguish the natural Möbius sum from a corrected approximant containing a terminal harmonic counterterm.

Accordingly, broad novelty for failure of the raw natural approximant is **not claimed**. The
audited sources did not expose this exact denominator-free critical-zero residue proof or the
fixed cofinal lower floor for the corpus canonical discrete complementary tail after its
log-prefix split. Those are candidate corpus/formal novelties only; publication novelty remains
subject to external expert review.

## Final route disposition

Raw canonical NB/BD complementary-tail decay is a proved dead end. Any surviving NB/BD route
must change coefficients or subtract the critical residue contribution; merely improving the
existing logarithmic prefix estimate cannot overcome the cofinal critical-scale floor.
