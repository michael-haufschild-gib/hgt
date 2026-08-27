# FZZ regular polynomial-pencil no-go (2026-08-27)

Formalized `GaloisForLFunctions.RHTower.FZZCigarPunctureRegularPolynomialPencilNoGo` and wired it into the RHTower umbrella. For arbitrary finite polynomial matrix pencil `P` over `ℂ` and arbitrary fixed coupling `K`, every real dark-mode energy is a root of `P.det`. If `P.det ≠ 0`, dark energies form a finite set. An injective positive-real XiC Hardy packet of size `natDegree(P.det)+1` contradicts Xi-completeness. Therefore Xi-completeness forces the polynomial identity `P.det = 0`.

Targeted `lake build GaloisForLFunctions.RHTower.FZZCigarPunctureRegularPolynomialPencilNoGo` passed. Principal theorem axiom audit: only `propext`, `Classical.choice`, `Quot.sound`. Card moved to `docs/drafts/pipeline/3-formalized/fzz-puncture-regular-polynomial-pencil-no-go.md`. Frontier map remained read-only.

Next sharp boundary: singular polynomial pencils. Strong corpus-driven candidate is coupling-sensitive row-replacement/maximal-minor vanishing under Xi-completeness, then polynomial-kernel/persistent-branch classification.