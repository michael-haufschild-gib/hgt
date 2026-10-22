# Extremality is not yet a hypertranscendence phase transition

- **ID:** `extremality-hypertranscendence-phase-transition`
- **Stage:** 1-in-progress
- **Type:** FALSIFIED UNIVERSAL PHYSICS CLAIM / OPEN NO-GO CLOSURE
- **Killed candidate headline:** “Crossing extremality changes the mathematical species of
  black-hole time.”
- **Status:** universal comparison killed; positive mathematical and model-level survivor proved
  on paper; unconditional Lean formalization required before moving this card to `5-failed`.

## Candidate claim

The attempted universal law was:

```text
nonextremal horizon response is differential-algebraic
extremal horizon response is hypertranscendental
```

The motivation was the exact extremal Reissner--Nordström all-time intensity

\[
 |\beta_{\omega\omega'}|^2
 =\frac{e^{-2\pi\omega/\kappa}\omega'}{\pi^2\kappa^2\omega_p}
 \left|K_{1+2i\omega/\kappa}
 \left(\frac{2}{\kappa}\sqrt{\omega\omega_p}\right)\right|^2,
 \qquad \omega_p=\omega+\omega'.                          \tag{1}
\]

A constant-argument scan reduces the non-elementary intensity factor to
\(K_\nu(s)K_{\nu-2}(s)\), which is hypertranscendental on paper.

## Exact killing mechanism

The comparison mixes two inequivalent approximations.

1. In the universal late-time limit, nonextremal collapse has exponential peeling and Planck
   intensity, while extremal collapse has reciprocal peeling and a fixed-order \(K_1\) intensity.
   Both are differential-algebraic in their natural frequency scans.
2. In the exact all-time thin-shell model, extremal RN has variable-order \(K_\nu\), but
   nonextremal RN already has variable-parameter regularized confluent-hypergeometric kernels.
   Their differential species has not been shown to be DA and may also be hypertranscendental.
3. The variable Bessel order in `(1)` comes from retaining the logarithmic term beyond the leading
   reciprocal extremal peeling law. A universal claim cannot compare this exact subleading
   structure against only the leading nonextremal Planck limit.
4. The moving-mirror model omits greybody factors, \(3+1\) propagation, vacuum-polarization
   corrections, backreaction, and extremal-collapse stability.

Therefore no DA-to-HT phase transition across extremality is established.

## Strongest positive survivor

For every \(s>0\),

\[
  \nu\mapsto K_\nu(s)K_{\nu-2}(s)
\]

is hypertranscendental over \(\mathbb C(\nu)\). Consequently the exact extremal RN moving-mirror
intensity has an explicit physical one-parameter scan that is hypertranscendental after removal of
its nonzero elementary prefactor.

Paper proof:
`../2-fully-proven/new_scientific_knowledge/bessel-order-intensity-hypertranscendence.md`.

## New insight

Horizon degeneracy does cause a real and already known discontinuity—exponential versus reciprocal
peeling, thermal versus nonthermal response, and exponential versus power-law late-time decay—but
differential species must be assigned at the same asymptotic resolution on both sides.
Hypertranscendence currently detects exact collapse-response structure, not extremality alone.

This blocks future attempts to manufacture a phase transition by comparing a full kernel on one
side with an asymptotic kernel on the other.

## Closure obligations

- [x] Exact physical mismatch identified from primary formulas.
- [x] Nontrivial positive survivor proved on paper.
- [ ] Positive survivor formalized unconditionally in Lean.
- [ ] Full nonextremal RN confluent-hypergeometric intensity classified in the same variable and
  calibration scheme.
- [ ] Greybody and \(3+1\) propagation tested for differential-species preservation.
- [ ] Move to `5-failed` only after Lean closure of the survivor.

## Primary sources

- S. Liberati, T. Rothman, and S. Sonego, *Nonthermal nature of incipient extremal black holes*,
  <https://arxiv.org/abs/gr-qc/0002019>.
- T. Rothman, *Nonthermal nature of extremal Kerr black holes*,
  <https://arxiv.org/abs/gr-qc/0006036>.
- M. R. R. Good, *Extreme Hawking Radiation*,
  <https://arxiv.org/abs/2003.07016>.
- M. R. R. Good and Y. C. Ong, *Particle spectrum of the Reissner--Nordström black hole*,
  <https://arxiv.org/abs/2004.03916>.

## Log

- 2026-07-28 — proposed extremality DA-to-HT phase transition.
- 2026-07-28 — hostile same-resolution comparison killed universal claim.
- 2026-07-28 — exact modified-Bessel intensity hypertranscendence retained as positive survivor.
