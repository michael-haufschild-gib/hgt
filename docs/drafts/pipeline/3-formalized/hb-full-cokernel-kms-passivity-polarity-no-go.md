# HB full-cokernel KMS passivity polarity no-go

- **ID:** HB-FULL-COKERNEL-KMS-POLARITY-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` HB full-cokernel survivor; corpus searches for passive response, full-cokernel causal cut, and optical power
- **Statement:** Every canonical HB full-cokernel orbit is exactly the dissipative quadrature of an explicit off-diagonal two-level finite KMS response; standard passivity therefore supplies the already-proved nonpositive orientation, while its opposite nonnegative sign holds exactly on the critical wall.

## Goal

Kill generic KMS/passivity/ordinary optical positivity as producer of HB's remaining opposite-sign premise. Proof chain:

`finite KMS positivity -> anti-Herglotz response -> exact HB full-cokernel negative orbit -> [missing opposite sign] -> orbit extinction -> source-clock extinction -> RH`.

The theorem must show first three arrows unconditionally and classify the fourth: ordinary passivity has wrong polarity, so only a phase-sensitive causal/source anomaly capable of proving the opposite orientation survives. This significantly reduces HB burden by excluding all arguments that use only positive Lehmann weights or generic passive realization.

## Gates

- [x] 0 → 1  in-progress: exact corpus-derived target, source-pure construction, hostile alternatives stated
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `d4HBFullCokernelFiniteKMSPassivityPolarityRouteKilled`, targeted `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

For grade `n` and Xi fibre `q`, set

`P(n,q) = susceptibility(n,q) * opticalPower(n,q) >= 0`.

Use a two-level Hamiltonian with energies `0,1`, inverse temperature zero, and Hermitian observable supported only on off-diagonal transitions, with amplitude `sqrt(2P)`. Each canonical KMS/Wightman transition intensity is exactly `P`. At spectral point `i`, the two nonzero-frequency resolvents sum to `-iP`; multiplying by fixed dissipative quadrature `-i` gives `-P`, exactly canonical full-cokernel orbit. Hence response imaginary part equals orbit real part, is always nonpositive, is strictly negative off wall, and has opposite nonnegative sign iff `Re(q)=1/2`. Global opposite sign remains exactly RH. No zero-frequency atom occurs.

## Paper proof

**[PROVED HERE]** Existing HB square law gives `P ≥ 0` and full orbit `K=-P`. For energies `E₀=0`, `E₁=1` at `β=0`, partition function is `2`; Wightman weight of either off-diagonal transition is `1/2`. Hermitian amplitude `A₀₁=A₁₀=sqrt(2P)`, `A₀₀=A₁₁=0` therefore gives off-diagonal intensity `(1/2)|A|²=P` and no diagonal intensity. At `z=i`,

`R(i)=P/(i+1)+P/(i-1)=-iP`.

Thus `(-i)R(i)=-P=K` and `Im R(i)=Re K`. Canonical KMS positivity proves `Im R(z)≤0` for all `Im z>0`. Existing exact HB orbit theorem gives `Re K<0` off wall and `0≤Re K ↔ Re(q)=1/2`; therefore opposite KMS orientation and extinction occur exactly on wall. Universal wall incidence is RH. Every step is dependency-closed.

## Competing conjectures and hostile audit

- **C1 — generic passivity produces HB's opposite sign:** failed. Corpus finite KMS response is anti-Herglotz; canonical full-cokernel orbit is a negative optical square. Signs agree in the nonpositive chamber, not the missing nonnegative chamber.
- **C2 — exact one-state KMS counterrealization:** sharpened and superseded because it used a zero-frequency atom.
- **C2b — exact off-diagonal two-level KMS counterrealization:** proved. Unlike corpus closure/density palette, response is exact, finite, Hermitian, nonzero-frequency, and equals physical full-cokernel orbit after one fixed quadrature.
- **C3 — positive Hermitian/QNM projection rescues C1:** failed before formalization. Corpus proves positive Hermitian source-FE cancellation off wall; external Kerr QNM projection uses a conserved bilinear form and requires direct/tail sectors, not a positive Hilbert inner product.
- **Hostile singularity check:** `P=0` is allowed; `sqrt(0)=0`, so no division or wall singularity occurs.
- **Hostile zero-mode check:** rejected one-state construction; final carrier has only off-diagonal gaps `±1`.
- **Hostile convention check:** theorem records fixed `-i` quadrature and separately identifies response imaginary part with orbit real part; no sign is hidden in a variable convention.

## Novelty audit

- Internal search found finite passive/KMS sign laws, universal closure of the dissipative ray, HB negative-square transmutation, and full-cokernel realization, but no exact finite-KMS realization of the HB orbit and no passivity-polarity route certificate.
- Green--Hollands--Sberna--Toomani--Zimmerman (arXiv:2210.15935) derive Kerr QNM excitation through a conserved bilinear projection and emphasize missing direct and tail pieces; they do not identify the Xi/HB orbit or this KMS counterrealization.
- Spiers--Pound--Moxon (arXiv:2305.19332) derive the nonlinear second-order Teukolsky source; no Xi/HB passivity polarity theorem appears.
- Belyi--Hassi--de Snoo--Tsekanovskii (arXiv:math/0510464) give general Herglotz conservative realizations; they do not contain the exact HB/FZZ-P/PW-B/RBH orbit identity or its RH-wall classification.

## No-go closure

- **Exact killing theorem/mechanism:** `d4HBFullCokernelFiniteKMSPassivityPolarityRouteKilled`: explicit two-level canonical KMS response is passive on upper half-plane, its `-i` quadrature equals HB full-cokernel orbit, and opposite sign remains exactly critical-wall/RH condition.
- **Strongest positive survivor:** phase-sensitive analytic/causal response regularity, beyond positive spectral weights, must produce the opposite sign or extinction.
- **New insight:** ordinary passive response does not merely fail to prove HB extinction; it exactly realizes the off-wall negative HB orbit.
- **Status:** internal and primary-literature audit complete; paper proof dependency-closed; formalized in `ThetaCuspHawkingHBFullCokernelKMSPassivityPolarityNoGo.lean`; targeted module build PASS; axiom audit only `propext`, `Classical.choice`, `Quot.sound`; lint has only three unrelated pre-existing HTGeometry umbrella errors.

## Log

- 2026-08-31 — created directly in 1-in-progress after corpus and literature audit; C1/C3 killed, C2 active.
- 2026-08-31 — one-state zero-mode version rejected; C2b two-level nonzero-frequency construction paper-proved and Lean-formalized; route killed.
