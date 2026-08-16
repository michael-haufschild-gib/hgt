# Suzuki Cauchy reporter-secant sharp transition

- **Status:** Formalized; targeted source check, leaf build, and axiom audit pass
- **Routes:** CCM-UR, CCM-FU, CCM-HG, Route O, Suzuki reflected-wall assembly
- **Labels:** `[NEW]` `[SOURCE-SPECIFIC]` `[UNCONDITIONAL]` `[SHARP-CLASSIFICATION]`
- **Lean module:** `GaloisForLFunctions.RHTower.SuzukiCauchyReporterSecantSharpTransition`

## Corpus-first frontier audit

Novelty was checked before proof. `scripts/formal_tools.py research` searches covered exact Cauchy
reporter profiles, full secant sign classifications, multi-turning-seam Mangoldt transport, and
prime--polar completed-source energies. Existing corpus supplied only:

- positive definiteness and finite Ward capacity of the Cauchy packet;
- factor-two negativity `G(p,2p+r) <= 0`;
- one-turning-seam Mangoldt log-Haar transport and bicausal seam conservation;
- completed prime--polar carriers and RH-equivalent scalar receivers.

No declaration gave the sign transition inside `p < q < 2p`. Targeted external search checked
Suzuki's 2023 screw-function paper, his screw-line paper, the 2026 Weil-form synthesis, and the 2026
M-function/screw-function paper. Those sources study screw kernels and RH criteria, not the
two-depth Cauchy reporter cross-Gram or the transition below.

## New theorem

For

```text
K(x) = exp(-|x|/2),
G(p,q) = K(p-q) - K(p-2q) - K(2p-q) + K(2p-2q),
```

write `q=p+r` with `0 <= r <= p`. Exact middle-band factorization is

```text
exp(-r/2) G(p,p+r)
  = exp(-r) + (1-exp(-p/2)) exp(-3r/2) - exp(-p/2).
```

Right side is strictly decreasing in `r`. For every `p>0`, it is positive at `r=p/2` and negative
at `r=p`. Consequently there is one unique transition residual `r_*(p)` with

```text
p/2 < r_*(p) < p,
G(p,p+r_*(p)) = 0.
```

Equivalently, unique transition depth satisfies

```text
3p/2 < q_*(p) < 2p.
```

Within complete middle band, sign is exact:

```text
r < r_*(p)  -> G(p,p+r) > 0,
r = r_*(p)  -> G(p,p+r) = 0,
r > r_*(p)  -> G(p,p+r) < 0.
```

All interval and nonzero conditions are packaged in source types, so exported Lean theorems have
no analytic premise, RH hypothesis, added axiom, or numerical assumption.

## Scientific consequence

Factor-two wall was sufficient but not sharp. Every nonzero lag has an additional strictly negative
middle-band sector before depth `2p`; transition varies with shallow lag and tends numerically from
ratio near `2` at small lag toward `3/2` at large lag. Thus completed-source estimates should not
discard whole strip `p<q<2p` as potentially positive.

This is genuine prime--prime localization, not completed-energy closure. Prime--polar and
prime--Gamma mixed blocks can carry either sign and remain open. Next source step must combine this
sharp transition atlas with signed completed-current transport; a prime-only uniform norm claim is
neither proved nor asserted.

## Lean certificate

Principal declarations:

- `SuzukiReporterSecantMiddleBand.transition_factorization`
- `strictAnti_suzukiReporterSecantTransitionPolynomial`
- `existsUnique_suzukiReporterSecantTransitionResidual`
- `suzukiReporterSecantTransitionDepth_mem`
- `suzukiReporterSecantCauchyGram_transitionDepth_eq_zero`
- `SuzukiReporterSecantStrictMiddleBand.gram_sign_trichotomy`
- `SuzukiReporterSecantSharpNegativePair.gram_neg`
- `SuzukiReporterSecantSharpPositivePair.gram_pos`

Verification after umbrella wiring:

- `lake env lean GaloisForLFunctions/RHTower/SuzukiCauchyReporterSecantSharpTransition.lean`
  passes;
- `lake build GaloisForLFunctions.RHTower.SuzukiCauchyReporterSecantSharpTransition` passes;
- `#print axioms` on factorization, strict antitonicity, unique transition, transition zero,
  sign trichotomy, and sharp positive/negative theorems reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
