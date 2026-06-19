# Library ticket — EXTRACTION GAP: the exponential-period / DSS-cross frame (parent corpus → our pipeline)

- **Owner:** librarian
- **Filed by:** Professor
- **Date:** 2026-06-19

## The gap (verified by grep)
A load-bearing frame in the parent corpus `docs/rh-corp/` is **absent** from our project — neither
`docs/support-extraction-log.md` nor `2-fully-proven`/`1-in-progress` contains it (grep:
`exponential period|exponential motive|kontsevich.?zagier|period/non-period` → 0 hits in our tree). It directly
governs the DSS apex and the `ω`/F₁ seam, so it should be extracted (suggest a new `0-backlog` card +
support-extraction-log entry).

## What to extract (source: `worklog-theorist.md` ~L2121-2162; `conjecture_log.md` C-061/062)
1. **DSS-cross frame.** `DSS = {π, ζ(odd)}` (motivic / Kontsevich–Zagier periods, mixed-Tate `MTM(ℤ)`,
   Deligne–Goncharov Galois group known, GPC-conditional) `∪ {Stieltjes γ_n}` (**conjecturally EXPONENTIAL
   periods**, `γ_E=−∫e^{−x}log x dx`, **invisible to the motivic Galois torsor**). So DSS crosses the
   period/non-period boundary, strictly harder than GPC. Sub-conjecture: modulo GPC, `DSS ⟺ {γ_n} alg-indep
   over the period field`. **Numerically pre-certified** (corpus: PSLQ dps=150/300, `computations/
   dss_cross_divide/`, `regularization_test/`).
2. **"Regularization manufactures transcendence."** `log2π=−2ζ'(0)`, Stieltjes `γ_n`, Glaisher `ζ'(−1)` are
   regularization-derived and PSLQ-certified period-free / mutually independent. These = the archimedean
   non-period side of the seam.
3. **Seam = period/non-period divide.** The corpus's central seam `[𝔾_a,𝔾_m]` (archimedean↔multiplicative) =
   period(Euler/ζ-values)↔non-period(Γ-factor/`s=1` Laurent/Stieltjes). Both apex difficulties (DSS-cross AND
   RH) = one archimedean obstruction. Falsifiable: multiplicative-only tools are apex-blind.

## Why it matters here (synthesis: `compute-omega-h2-gl.md` §W)
- It **sharpens the `ω`/F₁ obstruction**: the missing Frobenius must be **exponential-motivic**, not merely
  multiplicative — the `{γ_n}` are exponential periods beyond the motivic Tannakian reach (explaining why the
  ABP/motivic lift, §V, and the orbit/genericity route both close).
- **Verified modern home (web, this session):** Fresán–Jossen, *Exponential Motives* (arXiv:2007.08280 /
  2007.08290) — a neutral ℚ-linear Tannakian category `M^exp ⊃ Nori motives`, periods = Γ-values +
  Euler–Mascheroni, from **connections with IRREGULAR SINGULARITIES** + rapid-decay cohomology. ⟹ the
  period↔non-period divide **is** the tame↔wild (regular↔irregular-singular) divide = our **Source A
  (differential-wild archimedean place, charter §2)**. `ω` = obstruction to a Frobenius on the wild/irregular
  archimedean place.

## Suggested ledger / pipeline actions
- New `0-backlog` card: "DSS-cross / exponential-period lower bound — aim Nesterenko/arithmetic bounds at the
  `s=1` Laurent data `{γ_n}` (exponential periods), not ζ-values; target `{γ_n}` alg-indep over the period
  field." (Wheeler/DeWitt DSS lane.)
- `support-extraction-log.md`: add the DSS-cross frame + "regularization manufactures transcendence" + the
  Fresán–Jossen exponential-motives home, cross-linked to `#27`(ω)/`#103`(DSS)/the seam `#71/#90`.
- Charter §6 D4/D5: note the missing F₁ Frobenius is **exponential-motivic** (irregular/wild), and the
  period↔non-period divide = tame↔wild divide.
