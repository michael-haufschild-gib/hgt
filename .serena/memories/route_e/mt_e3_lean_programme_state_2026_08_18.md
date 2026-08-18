# MT all-interval E₃ — Lean programme state (2026-08-18)

Programme card: `docs/drafts/pipeline/1-in-progress/matomaki-teravainen-e3-lean-programme.md`.
Serves the two E3 cards in `2-fully-proven` (`route-e-forbidden-support-e3-stability`,
`route-e-cofactor-amplified-e3-token-supply`), whose only remaining input it is.

## Source
arXiv:2207.05038 = Matomäki–Teräväinen, *Almost primes in almost all short intervals II*.  **The PDF
text was retrieved** (WebFetch saves the file locally; `pdftotext -layout` on it works).  Do not
re-guess the construction: §7 counts `p₁p₂n` with `p₁ ∼ (log x)^{1.1}`, `p₂ ∼ √(x/P₁)/2`, and `n`
weighted by **Harman's minorant `ρ⁻`** — not three primes.

## Three structural facts (all read off the paper)
1. **§6.1 removes Kuznetsov.**  Heath-Brown's identity replaces Harman's sieve, Bourgain's
   zero-density replaces Watt/Deshouillers–Iwaniec, at exponent `1.615` instead of `1.55`.
2. **Remark 5.2: the exponent is free.**  `c = 1 + 1/(1 − θ(1−2σ) − ε)` for any
   `1/5 + 2ε ≤ σ ≤ 1/2`; `c ∈ [2,3]` always.  The Route E cards do not care which `c` — the
   exponent reaches them only as a polylog factor in the displacement.  So **some** `σ > 1/5`
   suffices; the sharp `49/206` is not needed.
3. **`(FS7)` is the paper's own step 4**, proved there by the improved MVT + a 2-D sieve for
   `n(n+k)` — exactly the corpus's shifted-pair Selberg sieve.

## What is Lean now (all axiom-clean, all wired into `GaloisForLFunctions.RHTower`)
§7 assembly: `Sieve/ImprovedMeanValue` (Lemma 3.3, general), `Sieve/DyadicPrimeMeanSquare` +
`Sieve/DyadicPrimeMeanSquareAffine` (`(FS7)`, and in affine shape), `Sieve/MixedMomentAssembly`
(steps 3+5), `Sieve/PerronKernelBound` (both branches, `min(h, 2(x+h)/|t|)`),
`Sieve/PerronWindowKernel` (the two prefix integrals merged into one kernel integral).
Prime-pair sieve: `Sieve/PrimePair{Count,ShiftSum,Average,Neighbour}`.
Jutila: `Sieve/DivisorBound` (`d(n) ≤ C_ε n^ε`, explicit constant — mathlib gap),
`Sieve/PowerFibreDivisorBound` (fibre = ordered `ℓ`-factorisations ⟹ `d(m)^ℓ`; the adapted-moment
level-set bound), `Sieve/JutilaLargeValues` (both endpoints, `k` free),
`Sieve/CriticalTruncationZeta` (Euler–Maclaurin bridge to `ζ`),
`Sieve/AbelIncreasingWeight` (Abel with a nondecreasing weight),
`Sieve/GramEntryZetaBound` (`|∑_{n<M}n^{-it}| ≤ 2(‖ζ(1/2+it)‖+M^{1/2}/|t|+1/2+4|t|)(M−1)^{1/2}`),
`Sieve/DirichletRowZeta` (the same as a Gram-entry bound for `dirRow`),
`Sieve/GallagherSumGeneral` (discrete→integral for any `C¹` function),
`Sieve/MeanSquareLevelSplit` (level splits: squared, weighted, and `L¹`).

## THE single remaining analytic input on the Jutila route
**A fourth moment for `ζ` OFF the critical line** (equivalently a `ζ′` fourth moment).  The corpus
owns `∫_{Icc N 2N}‖ζ(1/2+it)‖⁴dt ≤ C·N(1+log N)⁴` only ON the line
(`RHTower.exists_integral_Icc_norm_riemannZeta_line_pow_four_le_polylog`, via `linePt`).  Every
route to the discrete average `∑_r‖ζ(1/2+iτ_r)‖⁴` over separated `τ_r` needs the off-line moment:
Gallagher/Sobolev needs `ζ′`; the subharmonic mean-value property needs a disc integral; the
derivative-free `Sieve/SeparatedSampling.sum_le_integral_of_separated` needs a local comparison.
Candidate routes: Hadamard three-lines between `σ = 1/2` and `σ = 1+ε` (where the moment is `≪ T`);
or redo the corpus's AFE derivation (`SmoothAFEZetaSquare*`) at a general `σ`.

## Do not rebuild — the corpus already owns these
- Dirichlet rows, Gram entries, Schur/Halász–Montgomery: `Sieve/DirichletRow` (`dirRow`,
  `inner_dirRow`, `dirichlet_bessel`, `dirichlet_bilinear`), `Sieve/DirichletFarField`,
  `Sieve/DirichletLipschitz`, `Sieve/DirichletTrivial`, `Sieve/HalaszMontgomeryDyadic`.
  **I started a duplicate `DirichletSchur` and had to delete it — check this family first.**
- Montgomery large-values count: `Sieve/DirichletLargeValuesL1.card_largeValues_div_le`.
- Heath-Brown's identity: `Sieve/HeathBrownIdentity` (monomial and compressed forms), plus a
  163-module `Sieve/Maynard*` layer on top of it.
- Sharp truncated Perron: `Sieve/PerronShortInterval`.
- Gallagher pointwise/window: `Sieve/GallagherSobolev`, `Sieve/WindowDisjointness`.

## Exponent arithmetic that rules routes out (checked)
With `G ≍ L/N`, `V = N^{-σ}`, `N = T^α`, `α ∈ [2/3,1)`:
Montgomery gives `T^{(1+4σ)/3}` (needs `σ ≥ 1/2`); the pure `ℓ`-th moment needs `ℓ = 1`; Huxley's
`R ≪ GNV^{-2}+G³N²TV^{-6}` needs `α(6σ−1) ≤ 2σ−1`, unsatisfiable for `σ > 1/6` and needing `α ≥ 3`
for `σ < 1/6`.  Only the fourth-moment interpolation reaches `σ > 1/5`.  Jutila's own range is
`N ≥ T^{9/11-10ε}`, which is why §6.1 needs Bourgain for `N ≥ T^{2/3}`.
