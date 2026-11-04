# Fable 0311 §5 (Q4) — breakthrough questions that open the path to RH

- **ID:** F0311-Q4
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (loop card)
- **Source:** `docs/reports/review-0311/fable.md` §5.1–5.6
- **Statement:** answer §5.1–5.6 with complete, unconditional, Lean-formalized solutions.

## Status

| Q | Question | Corpus reduction | State |
|---|---|---|---|
| 5.1 | mixed-pairing bound `W(τ_εu,v)² ≤ Q(u)Q(v)` on `W_ℓ`, every stage | RH (`riemannHypothesis_iff_translation_contraction`) | open |
| 5.2 | finite cusp energy ⇒ `D_s(ψ) = 0` for Lewis periods | RH (`criticalLineResonance_iff_dyadicCuspEnergy_and_zero_coIsometryDefect`; resonance ⇔ `ζ(2s) = 0`) | open |
| 5.3 | inner-cap cancellation at every polynomial stage | RH across degrees | open |
| 5.4 | half-power law at the trivial gauge point from the pole | RH | **answered (negative), Lean**: no property of the pole decides it, in Möbius and prime-source form (flip points: Möbius exponent `max(θ, Θ)`); spectrum of the pole-subtracted exponent is `[Θ, 1]`, minimized at `0`; `3-formalized/the-pole-does-not-decide-the-half-power-law.md` |
| 5.5 | all-`K`, all-vector conductor Gram | RH (HWV equivalence) | open; CSAR/ReceivingCharges owned by a non-Claude agent |
| 5.6 | rank-uniform theta source law | RH; first instance rank nine | open; `ThetaCuspSections/FifthEven*` actively written by another agent — do not edit |

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Ledger

| # | Q | Conjecture | Outcome | Lesson |
|---|---|---|---|---|
| 1 | 5.2 | A PM functional of the Eisenstein period forces `Re s = ¼` at resonances | fails: `D_s(ψ_s) = −∫ w_σ|ψ_s|²` with weight vanishing exactly at `σ = ¼` for every strip `s`, resonant or not | every PM reading is defined for all `s`; resonance enters only through `ζ(2s) = 0` (cusp energy), never coupled to `σ` |
| 2 | 5.2 | Virial identity `(4σ−1)E_ren(s) = K·D_s`, `K > 0`, forces the line via the reflected pair | fails: renormalized self-energy of a resonance is `−|c_s|²/(4σ−1)` (sign of `¼−σ`), pair sum `(|c_{s'}|² − |c_s|²)/(4σ−1)` with `c_s = 2ζ(2s−1)/(2s−1)`, `c_{s'} = 2ζ(−2s̄)/(−2s̄)` unrelated by FE | renormalized cusp energies only read the side; no sign without a relation between `|ζ(2s−1)|` and `|ζ(1+2s)|` at zeros of `ζ(2s)` |
| 3 | 5.4 | The half-power law at `0` follows from a property of the pole | **refuted, Lean**: sparse flips `x_θ` share the pole up to `N^b` (`b > θ`) and have pole-subtracted exponent `θ` under RH | survivor = exact law: exponent of `x_θ` is `max(Θ_ψ(0), θ)` off `θ = Θ_ψ(0)`; the pole carries no information below precision `N^b` |
| 4 | 5.1 | Margin of window positivity decays at a fixed exponential rate, so a Grönwall law `λ' ≥ −Cλ` closes the induction | fails as a mechanism: rate ≈ `2γ₁` on `[0.75, 1.1]` (numerics, ledger Q3 6b) but the floor must decay doubly exponentially (KR-PAF); a Grönwall law with `C(ℓ) ≍ e^ℓ` is RH-equivalent and off RH fails at the first zero crossing | certificates must be exact at every stage; any differential margin law is the RH statement in disguise |
| 5 | 5.4 | A gauge point can beat the trivial point (pole-subtracted exponent below `Θ`), so a construction of such a point proves RH | **refuted, Lean**: coherence `Re ψ_y ≤ ψ_0` makes every law at `y` a one-sided bound at `0`; with the one-sided strip law `E(y) ≥ Θ`, Schmidt gives `E(y) ≥ 1/2`; range of `E` is exactly `[Θ, 1]` | survivor = `range_poleSubtractedExponent`; RH iff the minimum of the spectrum is `1/2`; gauge freedom only repairs positive excursions of `ψ − N`, never negative ones |
| 6 | 5.2 | Krein self-adjointness of `T_p` forces real Hecke eigenvalues `p^{2s−½}+p^{½−2s}` at resonances, hence `Re s = ¼` | fails: off-line resonant vectors are Krein-neutral (`mayerKreinForm` of an off-line basis vector with itself vanishes), and a neutral eigenvector of a Krein-self-adjoint operator may have a nonreal eigenvalue | arithmetic (Hecke for every prime) is present in PM but acts on the neutral cone; a sign needs a nonneutral vector at an off-line resonance |
| 8 | 5.4 | The Möbius half-power law (the corpus's `GaugeHalfPowerLaw moebiusSource`) is decided by the pole even though the pole-subtracted prime law is not | **refuted, Lean**: `gaugeExponent_moebius_flipPoint` — Möbius exponent of `x_θ` is `max(θ, Θ)` unconditionally (Landau-type: `ζD = L(b)` with `b = μχ * 1 ≥ 0`, identity theorem off `s = 1`, divergence of `Σ_{flip} p^{−θ}`) | survivor = explicit points with every Möbius exponent in `[Θ, 1)`, all carrying the pole of `0` |
| 9 | 5.6 | The TH current hides a structural positivity | the current at aperture `a` is `2|ξ(s)|² Re(ξ'/ξ)(s) = ∂_σ|ξ(σ+ib)|²` at `σ = 1/2 + a` (TH card: exact at `a = 1/2`); its moment hierarchy is the `σ`-derivative of the Gram matrices of `b^k ξ(σ+ib)`, which are PD for every `σ` | 5.6 is Loewner monotonicity in `σ ∈ (1/2, 1)` of these Gram matrices, i.e. `|ξ|` increasing in `σ` (Lagarias/monotonicity criterion); the TH lane is owned by another agent |
| 7 | 5.3 | A source identity on the Burnol window cancels the inner-cap flux | reduces exactly to zero-freeness of `A_N` on `[½, σ_m] ×` window (`rightHalfPort_criticalLineFlux_zeroFree_tfae`): Cauchy's theorem cancels everything except residues at zeros in the cap | the only source identity is the residue theorem; cancellation is the absence of zeros, RH locally |

## Log
- 2026-11-04 — created
