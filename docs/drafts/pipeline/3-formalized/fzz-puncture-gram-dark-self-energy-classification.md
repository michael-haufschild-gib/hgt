# FZZ puncture Gram-dark self-energy classification

- **ID:** FZZ-P-GDSC
- **Stage:** 3-formalized
- **Type:** FESHBACH CLASSIFICATION / NO-GO SURVIVOR
- **Parent:** FZZ-P-TCPC
- **Frontier-map policy:** read only; no edit made

## Exact result

Let `K : X → Y` be a bounded coupling between complete complex Hilbert spaces and
let `G=K†K` be its positive Gram/Feshbach return self-energy.

1. `Gx=0 ↔ Kx=0`.
2. For every bounded interior operator `A`,
   `((A-G)x=0 ∧ Kx=0) ↔ (Ax=0 ∧ Kx=0)`.
3. In two-channel affine FZZ data, if the on-shell source row is the same nonzero
   coupling row `(p,q)`, an internal-dark point mode exists exactly when the
   slope row is Plücker-transverse: `q d₀-p d₁≠0`.
4. With fixed nonzero coupling and transverse slope, that point mode exists for
   every real target energy.

## Paper proof

Adjointness gives

`⟪K†Kx,x⟫ = ⟪Kx,Kx⟫`.

If `K†Kx=0`, the right side vanishes, hence `Kx=0` by definiteness of the Hilbert
inner product.  The converse is immediate.  On `Kx=0`, therefore `K†Kx=0`, so
the effective equation `(A-K†K)x=0` is literally `Ax=0`.

For the FZZ specialization, substitute `(c₀,c₁)=(p,q)` into the exact
two-channel Plücker classification.  The on-shell minor `qp-pq` vanishes
identically; the slope minor is the sole remaining condition.  Since the
criterion contains no `E`, transversality gives occurrence at every energy.

## No-go closure and positive survivor

Positive Gram return cannot dynamically create a mode in its own dark sector:
there it vanishes exactly, leaving the bare interior equation.  When the same
coupling supplies the continuum source, nodality is automatic rather than
zeta-selective.

Strongest positive survivor: a viable FZZ-P producer must prove an independently
derived, energy-dependent common-kernel law

`ker A(E) ∩ ker K(E) ≠ {0}`

at precisely the required zeta energies while retaining a transverse continuum
jet.  Alternatively it must derive a non-Gram, nonpositive, or genuinely
energy-nonlocal return term whose dark sector is not `ker K(E)`.

## Hostile review

- No claim that actual GFZZ backreaction has bounded, positive Gram form.
- No spectral mode inferred solely from positivity.
- Dark-sector assumption is explicit in both sides of effective-kernel theorem.
- Result separates source nodality from interior spectral occurrence.
- All-energy theorem demonstrates energy blindness, rather than fitting rows to
  zeta ordinates.

## Novelty audit (2026-08-27)

Corpus search found positive Gram Feshbach self-energy and affine/Plücker FZZ
classifications separately, but no theorem joining them into this dark-sector
no-creation law and FZZ energy-blindness result.  Primary literature treats
Friedrichs-Lee self-energies, multi-continuum states, and threshold determinants,
but search found no FZZ-puncture theorem with this exact Gram-dark/common-kernel
burden.  General identity `ker(K†K)=ker K` is standard; novelty claim concerns
its precise route-level consequence, not the Hilbert-space lemma alone. Priority
remains provisional pending expert review.

Primary comparison sources:

- arXiv:2109.02939, *The self-energy of Friedrichs-Lee models and its application
  to bound states and resonances*
- arXiv:1608.06833, *On Friedrichs Model with Two Continuum States*
- arXiv:math/0604277, *The threshold effects for a family of Friedrichs models
  under rank one perturbations*

## Lean realization

Module:
`GaloisForLFunctions.RHTower.FZZCigarPunctureGramDarkSelfEnergyClassification`

Theorems:

- `fzzPunctureGramSelfEnergy_apply_eq_zero_iff`
- `fzzPunctureGramDarkEffectiveKernel_iff`
- `fzzPunctureCouplingSourcedTwoChannelPointMode_iff`
- `fzzPunctureCouplingSourcedTwoChannelPointMode_allEnergy`

Verification:

- direct `lake env lean` passed
- targeted module `lake build` passed
- exported theorem axiom audit passed: only standard Mathlib axioms
- imported by `GaloisForLFunctions.RHTower`
