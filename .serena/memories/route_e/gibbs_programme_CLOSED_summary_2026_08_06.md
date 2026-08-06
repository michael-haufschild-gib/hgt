# The squarefree Gibbs gas programme: CLOSED at cycle 21 (2026-08-06)

Card MOVED to `docs/drafts/pipeline/3-formalized/squarefree-gibbs-parity-vortex.md`.
21 Lean modules in namespace `RHTower.GibbsGas`, all wired into
`GaloisForLFunctions.RHTower`, all audited to [propext, Classical.choice, Quot.sound],
no sorry, zero warnings. Umbrella builds clean (~17k jobs).

## What the theory contains
- Object/vortex: gibbsDiag, T0 cutoff recursion, 2-prime Lee–Yang, parity-jet law (totient
  = vortex intensity), k=3 vortex, current–discriminant identity.
- Locking: Disc/J^{k−1} → (−1)^{k(k−1)/2}k^k — repulsion is NOT independent of the current.
- Stability: k ≤ 4 all couplings; all k for x·σ(m) < 1; FALSIFIED in general (Szegő, s₆
  has Δ₃ = −1440 < 0 and no imaginary-axis zero); energy-spread scoping; two-scale engine
  levels 0–2.
- Condensation: EXACT log identity log‖Z‖−log‖J‖ = Σ_ζ(log‖1−ζ‖−log‖1+ζ‖); two-sided
  gap↔cancellation; localization (distant zeros inert); Coulomb-potential bound.
- Arithmetic: anchor (gas = Möbius on divisors of the primorial); infinite-volume bridge
  |Φ(x) − gas| ≤ e^{−(y+1)x}/(1−e^{−x}); zero potential = ratio of Möbius sums.
- Mechanism: adjoining a prime DIFFERENCES J and AVERAGES Z ⟹ non-expansiveness +
  contraction by (Z(x)−Z(px))/(Z(x)+Z(px)) ≈ (p−1)/(p+1) ⟹ ∏ ≍ (log y)^{−2} = the
  Erdős–Kac baseline; EXACT decomposition J_{S∪p}Z_S(x) = J_S(x)(Z_S(x)−Z_S(px)) − Δ with
  Δ = J_S(px)Z_S(x) − J_S(x)Z_S(px) the scale-invariance defect.

## FINAL STATEMENT
Baseline cancellation = two-scale averaging contraction, worth exactly (log 1/x)^{−2}.
RH needs x^{1/2}. ALL RH-strength cancellation is carried by the defect Δ. Bounding Δ is
equivalent to (G2)/RH and the gas gives NO new leverage on it — stated honestly, not
claimed as progress.

## Open (not claimed) / dead (do not re-attempt)
OPEN: refined conjecture (natural-gas stability) — predicted FALSE; obstruction =
Sathe–Selberg uniform to j ≈ log(1/x)/loglog(1/x). Bounding Δ.
DEAD: X1 criterion (empty for k ≥ 5); TSP engine (sufficient for a false statement);
general-S sector stability.

## If resuming
Do NOT re-derive any of the above. The natural next objects, if any, are OUTSIDE the gas:
new input on the defect Δ, i.e. coherent-mode control (see `mr-bilinear-scope-boundary`).
