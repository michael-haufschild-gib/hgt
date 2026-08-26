# Hawking–Teukolsky semigroup terminal value (2026-08-26)

## Result
Created `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingTeukolskySemigroupTerminalValue.lean` and imported it from `formal/GaloisForLFunctions/RHTower.lean`.

For an integrable spectral amplitude `a` and measurable contraction-semigroup generator `lambda` with `Re lambda <= 0`, the continuous Cesaro-completed return
[
\int a(x)\,\Phi(T\lambda(x))\,d\mu(x),\qquad \Phi(z)=(e^z-1)/z
]
converges exactly to the integral over `{lambda=0}`. The proof supplies a sharp kernel norm bound `||Phi(T lambda)|| <= 1`, dominated convergence, a no-zero-generator decay corollary, and persistent-counterterm rigidity. It allows infinite discrete spectra, damping accumulation at zero, purely oscillatory modes, and absolutely/singular-continuous threshold spectrum. Only an exact co-resonant atom survives.

Created declarations use only `[propext, Classical.choice, Quot.sound]`. Direct compile and targeted build passed before a terminology-only rename from Stationary to Persistent. A later repeat direct check was stopped after 90s with no output because unrelated concurrent Lean builds saturated the machine. Formal lint reports existing unreachable-owned-module errors; new module is reachable. Scratch files cleaned.

## Physical interpretation
Generator zero is in the target-QNM-normalized frame: it means exact co-resonance with the target QNM pole, NOT physical omega=0. Therefore corpus theorem `d4GravitationalHypergeometricBoundaryJost_stationary_xi_ne_zero` does not close the remaining atom.

The surviving RH-bearing coefficient is exactly the full target-pole cokernel atom
[
P_{\omega_*} S^{(3)}_{++-},
]
i.e. the complete retarded Einstein–Teukolsky third-order Schur section. Slow tails, branch cuts, and nonresonant QNMs cannot persistently cancel normalized AIME.

## Falsified conjectures
1. Affine sideband instability: false for BM QNMs. Physical `++-` frequency is `2 omegaPlus + omegaMinus`; damping adds. The `x-y+z` lattice is only an inverse-character rule. Corrected comments in `ThetaCuspHawkingBMVariationalFoldedSidebandDichotomy.lean`.
2. Physical stationary-zero-mode shortcut: false because normalized zero generator is target-QNM co-resonance, not omega=0.

## Corpus facts used
- Exact AIME numerator `-12/(Q+2)`, nonzero at every Xi for nonzero seed.
- Only same-pole third-order `++-` counterterm can cancel.
- Complete source is AIME/orthogonal stationary cascade + second harmonic cascade + direct third jet.
- Direct third jet cancels from retarded-minus-advanced causal cut.
- BM physical `++-` source frequency has additive damping.
- Finite local/Jordan and finite-energy continuum returns decay.
- QNM-only expansions are not complete; threshold/branch-cut channel is now handled by terminal-value law except exact co-resonant atom.

## Literature audit
- Spiers–Pound–Moxon, arXiv:2305.19332: explicit nonlinear source only at second order.
- AIME, arXiv:2112.11168: mass/spin absorption mediates third-order excitation.
- Green et al./Kerr QNM bilinear, arXiv:2210.15935: QNM basis not known complete; branch-cut contributions remain.

## Next exact open core
Evaluate/prove noncancellation of the full co-resonant atom:
[
\ell\left[B(p,R_{+-}B(p,m)) + B(m,R_{++}B(p,p)/2) + C(p,p,m)/2\right]
]
on BM modes, including causal horizon/boundary normalization. No tail or generic KMS/passivity argument can replace this computation.
