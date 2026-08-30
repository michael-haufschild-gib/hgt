# HB modewise QNM clock-renormalization no-go

- **ID:** HB-HC-QNM
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `rh-current-frontier-map.md` · HB open source-dynamical FE–Schwarz extinction core
- **Statement:** The literal mixed-Casimir-corrected reduced Einstein–Teukolsky source has a unique modewise QNM frequency counterterm; it makes the returned Jost determinant vanish on every Xi fibre, while the counterterm is zero exactly on the critical wall and globally zero exactly under RH.

## Goal

Kill the HB proof chain

```text
literal mixed-Casimir-corrected spin-two source
  -> higher-order QNM solvability / clock renormalization
  -> returned-Jost extinction
  -> FE–Schwarz Ward extinction
  -> RH
```

by proving that higher-order QNM solvability is nonselective: its unique modewise frequency shift
absorbs the exact source on every Xi fibre.  Identify exact surviving RH burden as the additional
global standard-clock assertion that every modewise shift is zero.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `<name>`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Conjecture chain

### HC-QNM-1 — unique modewise solvability counterterm

Let `S(q)` be the exact reduced doubled-grade chiral Teukolsky source with nonzero actual
mixed-Casimir-corrected scalar seed, and let `D_n` be the normalized derivative of the simple BM
Jost zero.  Since `D_n != 0`,

```text
delta_n(q) = -S(q) / D_n
```

is the unique scalar satisfying `S(q) + delta_n(q) D_n = 0`.

**Proof chain closed:** literal source → QNM perturbative solvability.

### HC-QNM-2 — renormalized return is universally trivial

Insert `S + delta_n(q) D_n` as additive returned-Jost source.  At the old QNM, the multiplicative
horizon phase multiplies the vanishing old Jost factor and the additive source is zero.  Hence the
Evans return determinant vanishes for every Xi copy without RH.

**Route killed:** modewise QNM solvability / frequency renormalization cannot select critical-line
copies.

### HC-QNM-3 — exact positive survivor

For nonzero seed, `delta_n(q)=0` iff `S(q)=0` iff `Re(q)=1/2`.  Therefore

```text
(forall q, delta_n(q)=0) <-> RH.
```

Off wall the raw source and unique counterterm are both nonzero although the renormalized return
is exactly zero.  The surviving producer must prohibit mode-dependent frequency renormalization
and derive the standard-clock condition independently; QNM solvability cannot provide it.

## Approach

Use corpus theorems:

- `d4BM_mixedCasimirCorrectedActualUnfoldedSource_two_five_eq_canonical` and
  `d4BM_actualTwoFiveUnfoldedScalarSource_ne_zero` for a literal nonzero scalar seed;
- `d4ThetaReducedSecondOrderChiralTeukolskyGradeSource_sameGrade_ne_zero_iff` and its global RH
  theorem for exact source zero locus;
- `teukolskyNormalizedJostOmegaDerivative_ne_zero` for simple-pole transversality;
- `teukolskyReturnDeterminant_qnmPlus` for returned-channel incidence.

Paper audit uses Lestingi–Sberna–Green, *Schrodinger perturbation theory for black hole
quasinormal modes*, arXiv:2607.19492, especially the all-order inhomogeneous Teukolsky hierarchy
and frequency-shift solvability formula.  Literature search through 2026-08-30 found no RH/QNM
modewise-renormalization classification.

## Paper proof

`[PROVED HERE]` Put

```text
A = mixedCasimir(2,5) * actualUnfoldedSource(2,5),
S(q) = reducedSecondOrderChiralGradeSource(A,0,0,q,2s(q)),
D_n = normalizedJostOmegaDerivative(n).
```

The corpus proves `mixedCasimir(2,5)=2800` and the actual unfolded source is nonzero, so `A != 0`.
It then proves `S(q) != 0` iff `Re(q) != 1/2`, and proves universal `S(q)=0` iff RH.  The simple
BM Jost-zero theorem gives `D_n != 0` for every overtone.

Define `delta_n(q)=-S(q)/D_n`.  Field cancellation gives

```text
S(q) + delta_n(q) D_n = 0.
```

If another scalar `eta` cancels, then `(eta-delta_n(q))D_n=0`; nonvanishing of `D_n` gives
`eta=delta_n(q)`.  Thus the counterterm is unique.  Division by `D_n != 0` also gives
`delta_n(q)=0` iff `S(q)=0`, proving the pointwise wall criterion and the global RH equivalence.

Finally define the locally frequency-renormalized cross source by adding
`delta_n(q)D_n` to the exact spectral cross source.  At the old QNM its value is zero.  The returned
Jost channel is a multiplicative horizon phase times the old Jost factor plus this cross source.
The old Jost factor vanishes at the QNM, so the returned channel and therefore its Evans determinant
vanish for every `q`, without RH.  Off wall, both `S(q)` and `delta_n(q)` are nonzero, so this is
sourceful cancellation rather than darkness.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** Nonzero Jost derivative makes a unique modewise frequency
  shift available on every fibre; it cancels the exact source identically.
- **Strongest positive survivor:** Zero modewise shift is equivalent pointwise to the critical wall
  and globally to RH.
- **New insight:** HB cannot obtain RH from perturbative solvability or a renormalized returned-Jost
  extinction law.  It needs a separate divisor-independent standard-clock theorem that forbids the
  canonical nonzero off-wall frequency shifts.
- **Status:** Corpus and current-literature audits complete; dependency-closed paper proof above;
  ready for Lean.

## Log

- 2026-08-30 — created directly in 1-in-progress after corpus-first conjecture and literature audit.
- 2026-08-30 — HC-QNM-1/2/3 proved on paper; conjecture survived and moved to Lean gate.
