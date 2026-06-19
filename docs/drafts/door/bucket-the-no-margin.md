# Bucket X6 — The no-margin phenomenon

**Bucket grade:** organizational (SEARCH channel). Sorted from `docs/support-extraction-log.md`.
**Scope (one line).** Positivity in this problem holds with **no uniform floor** (`λ_min→0`); the
no-margin is not a nuisance but the **content** — it is faithfulness / criticality / the exceptional
point, and it appears identically across many coordinates.
**Work package this seeds.** Find the **one missing uniform bound** (the "Kronecker→Liouville height
upgrade") that, if it existed, would unblock all coordinates at once — and decide whether the
no-margin is an obstacle (to be overcome) or the prize (faithfulness, to be embraced).

> **The no-margin filter (`testing.md`).** A claim that produces a *fixed positive margin* has smuggled
> in extra strength and is suspect. This bucket collects every face of the no-margin so the filter can
> be applied consistently and the phenomenon understood, not just flagged.

---

## The no-margin in four coordinates = one missing bound (#89 §8, #70 SEED-Q)
- #89 §8 the **weld:** the no-margin `ĥ(ρ) ≈ δ/A → 0` linearly off-line is the **same vanishing margin
  in four coordinates:** height excess (B7) = Toeplitz first-violated-minor order→∞ / magnitude→0
  (#77 Thm 7) = Weil-certificate `dim_min`→∞ (berry resolution law) = discrepancy resolution→∞
  (#69 §16). **Closing the gap = finding a height that SEPARATES (a uniform floor `ĥ(ρ)≥c(δ)>0`) =
  uniform-in-order TP = the uniform multiplicity/equidistribution estimate.** *One missing uniform bound
  unblocks all four.*
- #70 SEED-Q the **two-rate failure signature:** `margin ~ δ`, `detection-cost ~ log(1/δ)`. Every
  `B_wall` coordinate (height / total-positivity / discrepancy / explicit-formula) shows it. *The
  field's honest meta-finding: it FACTORS the wall (free vs the one wall), it does not break it.*

## The exact no-margin theorems (#77)
- §4 **Thm 6 (PROVED HERE):** a Stieltjes moment sequence need NOT be Pólya-frequency (witness
  `a_n=1+4^n`: PSD Hankel but Toeplitz minor `a_1²−a_0a_2=−9<0`). **Free moment positivity (FE-forced)
  is strictly weaker than Toeplitz total positivity (= RH).** *The precise reason RH isn't a free
  byproduct of FE-positivity.* Candidate native lemma **N6: "moment positivity ⇏ frequency positivity."**
- §4 **Thm 7 (PROVED HERE / NUM):** an off-line zero at distance `δ` breaks Toeplitz TP, but the **first
  violated minor's order grows as `δ→0`** with **vanishing magnitude** — no fixed-order TP test
  certifies RH. (the two-rate signature, exact)
- §3 what the FE forces FOR FREE (genuine byproducts): TP₁ (`c_n>0`); moment/Stieltjes Hankel positivity;
  TP₂/Turán (Csordas–Norfolk–Varga, with scale-free margin monotonically ↓ — the no-margin *trend*);
  asymptotic each-order TP_d (GORZ). **RH is only the UNIFORM completion.** `Λ=0` (= the TP-onset time) =
  the no-margin (Rodgers–Tao `Λ≥0` forces RH ⟺ Λ=0). Ledger: `secularHankel_posSemidef`.

## The no-margin = faithfulness (#92 §3 — the reframe that makes it the prize)
- A **faithful** representation has spectrum DENSE on the circle (no gap); a uniform positive margin
  would be a GAP = a place the angles never reach = a hidden relation = the FAILURE of faithfulness.
  **"No margin ⟺ no spectral gap ⟺ faithful ⟺ the secret numbers are independent."** *The knife's-edge
  is the PRIZE wearing the mask of an obstacle — it IS DSS/A2.* This reframes the program's central
  nuisance as the positive content. (→ [[bucket-A1-A2-unification-the-carrier]])

## The no-margin = an exceptional point (#96 §1 — the mechanism for WHY)
- The no-margin is NOT merely `λ_min→0` — it is an **EXCEPTIONAL POINT** (a non-Hermitian degeneracy
  where eigenvalues AND eigenvectors COALESCE, overlap→1, a Jordan block). **RH = PT-UNBROKEN (real
  spectrum), pinned exactly at the exceptional threshold** ("that verge is why there is no positive
  floor"). The weld: **no-margin = exceptional point = eigenvector coalescence = Nyman–Beurling
  completeness defect `d_N→0`** — three independently-derived faces = one non-Hermitian degeneracy.
  Certified toy `H(a,b)=[[ia,b],[b,−ia]]` (overlap `a/b→1` at `a=b`). (→ [[G5-unitarity-gatekeeper]],
  [[bucket-time-and-non-holonomic-time]])

## The no-margin = the light-cone / clock marginally null (#94 §5, #95)
- #94: the DeWitt metric is Lorentzian; **RH = the emergent clock is marginally NULL** (timelike block
  ≈ spacelike block, near-cancellation = the no-margin's geometric reason); off-line zero = tachyonic
  mode. #95 §3–4: no-margin = the dBN slow-roll **flatness** (`λ_min→0` = flat potential `V_arch`); RH =
  near-flatness is the flow's **attractor** (dynamical, not fine-tuned). (→ [[bucket-time-and-non-holonomic-time]])

## The no-margin = the Law of the Iterated Logarithm (#97 §1)
- `|M(x)|<√x` fails (te Riele: `limsup>1.06`) because the primes are *perfectly random* — the LIL
  overshoots √x by `√(loglog x)`. **The no-margin is the LIL signature, NOT a positivity defect** — it
  is Kronecker–Weyl resonance of ℚ-independent frequencies. *Caveat: soft (correlation-randomness)
  methods are amplitude-blind, structurally cannot reach RH (the amplitude IS the zeros).*

## The arithmetic of Λ — the no-margin constant itself (#85 SEED-W)
- `Λ` (dBN constant) = the **Face-A-criticality time** of the moment flow (positivity marginal, Face B
  flow-invariant). **New open sub-question: is `Λ` itself transcendental / a period?** Its arithmetic
  nature is unstudied; the field places it among the `{P_k(t)}`-periods. *Ties the no-margin constant to
  the transcendence axis (TIME/A2).* (→ [[bucket-new-sibling-conjectures]])

---

## The no-margin in one screen
| Coordinate | The no-margin face | Source |
|---|---|---|
| Arakelov height | `ĥ(ρ) ≈ δ/A → 0`, Kronecker (vanishes on whole locus) | #89 |
| Toeplitz TP | first violated minor order→∞, magnitude→0 (Thm 7) | #77 |
| Weil certificate | `dim_min → ∞` as `δ→0` (resolution law) | berry/#89 |
| discrepancy | resolution → ∞ | #69 §16 |
| representation theory | no spectral gap = **faithfulness** | #92 |
| non-Hermitian operator | **exceptional point**, eigenvector coalescence | #96 |
| Nyman–Beurling | completeness defect `d_N → 0` | #96 |
| geometry/cosmology | clock marginally **null** / slow-roll flat attractor | #94,#95 |
| analytic NT | the **LIL** overshoot `√(loglog x)` | #97 |
| dBN | `Λ = 0` (TP-onset time); is `Λ` a period? | #77,#85 |

**The two opposite readings to resolve:** the no-margin is either (a) the **obstacle** — there is no
finite certificate, every test's cost diverges as `δ→0` (so finite/positivity methods provably can't
close RH); or (b) the **prize** — it *is* faithfulness/criticality/independence (A2), the positive
content the program should target directly. #92's reframe argues (b).

## Open core / the work package
Find the **one missing uniform bound** (the Kronecker→Liouville height upgrade = uniform-in-order TP =
the uniform multiplicity/equidistribution estimate) — or prove no such bound can exist (confirming the
no-margin is irreducibly faithfulness, not an obstacle). Side-question: **is `Λ` a period?**

## Cross-references
- [[G5-unitarity-gatekeeper]] — the no-margin is G5's signature (`κ₋→0`, `|γ_k|→1`, exceptional point).
- [[bucket-A1-A2-unification-the-carrier]] — no-margin = faithfulness = A2.
- [[bucket-realization-and-fake-family]] — same integrality lesson: positivity is necessary, not sufficient.
- [[bucket-time-and-non-holonomic-time]] — no-margin = clock marginally null / exceptional point (T-breaking).
