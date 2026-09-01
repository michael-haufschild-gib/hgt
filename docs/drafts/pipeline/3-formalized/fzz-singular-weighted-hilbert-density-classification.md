# FZZ singular weighted-Hilbert density classification

- **ID:** FZZ-SWH
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` FZZ-P singular/non-Fock survivor
- **Statement:** The forced log-reflection is unitary for a positive measurable density exactly when `rho=g^-2 h`, where `g(x)=exp(-x/2)F(exp x)` and `h` is arbitrary positive measurable even; one such density gives a genuine weighted `L²` carrier and the literal Fermi source finite energy.

## Goal

Kill carrier existence, positivity, unitarity, and finite weighted energy as selectors in
`FZZ singular carrier -> phase/sign -> Ward extinction -> RH`. Survivor: independent source-specific
phase/sign law.

## Gates

- [x] 0 -> 1: corpus-derived forced gain; exact source-pure statement
- [x] 1 -> 2: dependency-closed proof below; `[PROVED HERE]`
- [x] 2 -> 3: `fzzCigarParity_singularWeightedHilbertDensity_noGo`; targeted build and axiom audit pass
- [ ] 3 -> 4: publication-ready

## Proof `[PROVED HERE]`

Let `F(t)=1/(exp t+1)` and let the corpus-forced local gain be
`a(x)=exp(-x)F(exp x)/F(exp(-x))`. Set `g(x)=exp(-x/2)F(exp x)`. Then `g>0`,
`a(x)=g(x)/g(-x)`, and `a(x)a(-x)=1`.

For `Tf(x)=a(x)f(-x)`, invariance of `integral rho(x)f(x)^2 dx` is equivalent pointwise to
`rho(-x)=a(x)^2 rho(x)`. This holds iff `h(x)=g(x)^2 rho(x)` is even, hence every positive
measurable unitary density is uniquely `rho=g^-2 h` for arbitrary positive measurable even `h`.

Take `h(x)=exp(-2|x|)`. Then the literal source energy density is
`rho(x)F(exp x)^2=exp(x-2|x|) <= exp(-|x|)`, so it is integrable. Thus singular positive
unitary finite-energy carriers exist off wall in an infinite family and cannot determine source
phase/sign. Lean also instantiates the corresponding `L²(volume.withDensity rho)` Hilbert carrier
and its density unitary.

## Novelty audit

Corpus search found forced reciprocal-Fermi gain and regular/tempered no-gos, but no weighted
Hilbert density classification or source-admitting density. Pakman, *FZZ Scattering*
([arXiv:hep-th/0606067](https://arxiv.org/abs/hep-th/0606067)), states classical scattering does
not uniquely determine the quantum reflection coefficient; it does not give this classification.
Boundary FZZ duality and cigar density-of-states papers likewise do not classify positive densities
for this forced reciprocal-Fermi operator. No matching result was found through 2026-08.

## No-go closure

- **Exact killing theorem/mechanism:** arbitrary positive even `h` parametrizes all positive unitary densities; an explicit `h` admits the source with finite energy.
- **Strongest positive survivor:** exact gauge-coboundary classification `rho=g^-2 h` and explicit source-admitting carrier.
- **New insight:** singular/non-Fock completion is feasible but maximally nonselective at carrier level.
- **Status:** Lean-proved in `ThetaCuspHawkingFZZParitySingularWeightedHilbertDensityNoGo.lean`.
