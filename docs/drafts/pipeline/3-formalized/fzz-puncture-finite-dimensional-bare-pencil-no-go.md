# FZZ puncture finite-dimensional bare-pencil no-go

- **ID:** FZZ-FDP
- **Stage:** 3-formalized
- **Type:** ALL-FINITE-DIMENSION CLASSIFICATION / NO-GO WITH HARDY PACKET SURVIVOR
- **Parent:** FZZ-P
- **Lean module:** `GaloisForLFunctions.RHTower.FZZCigarPunctureFiniteDimensionalBarePencilNoGo`
- **Frontier-map policy:** read only

## Result

Corpus Hardy theorem is upgraded to a canonical strictly increasing sequence
`Eₙ>0` satisfying `XiC(Eₙ)=0`.  Consequently, for every finite `n`, there is an
injective packet `E : Fin n → ℝ` of positive real `XiC` zeros.

Fix arbitrary dimensions `N,Q`, arbitrary complex endomorphism
`A : End(ℂ^N)`, and arbitrary coupling map `K : ℂ^N → ℂ^Q`.  A bare dark mode
at real energy `E` is a nonzero `A`-eigenvector of eigenvalue `E` lying in
`ker K`.  Lean proves unconditionally:

`¬ FZZPunctureFiniteBarePencilXiComplete A K`.

No selfadjointness, normality, diagonalizability, nonzero-coupling, or
coupling-rank assumption is used.

## Paper proof

Choose `E₀>0` by Hardy's zero-above-height theorem and recursively choose
`Eₙ₊₁>Eₙ`.  The same theorem supplies `Xi(Eₙ)=0`; the corpus real-axis identity
transfers this to `XiC(Eₙ)=0`.  Strict increase gives injectivity on every finite
initial packet.

If a fixed `N`-dimensional pencil were complete, apply it to
`E₀,...,E_N`.  Choose one dark eigenvector at each energy.  Eigenvectors of one
endomorphism at pairwise distinct eigenvalues are linearly independent, giving
`N+1` independent vectors in `ℂ^N`.  Finite-dimensional rank gives `N+1≤N`, a
contradiction.  The kernel equations are never needed after existence, so
arbitrary finite coupling geometry cannot evade the obstruction.

Dependency-closed and unconditional.

## Lean theorems

- `hardyXiPositiveZeroSequence_zero_pos`
- `hardyXiPositiveZeroSequence_lt_succ`
- `hardyXiPositiveZeroSequence_strictMono`
- `hardyXiPositiveZeroSequence_pos`
- `Xi_hardyXiPositiveZeroSequence_eq_zero`
- `XiC_hardyXiPositiveZeroSequence_eq_zero`
- `exists_injective_positive_real_XiC_zero_packet`
- `not_fzzPunctureFiniteBarePencilXiComplete`

## No-go and positive survivor

**No-go.** Every fixed finite-dimensional bare affine pencil `A-EI` fails FZZ
Xi-completeness, regardless of finite coupling rank.  This closes all finite
interior dimensions, not only the earlier two-channel dark line.

**Positive survivor.** Hardy's theorem now exposes injective positive real
`XiC` zero packets of every prescribed finite size.  This reusable spectral
width invariant forces any exact fixed-pencil realization to have unbounded
dimension.

Surviving FZZ producer space must use an infinite-dimensional interior,
genuine energy dependence beyond `A-EI`, or energy-dependent coupling/domain
data.  A finite matrix enlargement cannot work.

## Novelty audit (through 2026-08-27)

Mandatory corpus searches found the two-channel result and a general Hardy
model-space dimension theorem, but no all-finite-dimensional FZZ bare-pencil
classification or explicit positive `XiC` packet API.  Primary-source search
covered the proof of FZZ duality
([arXiv:0805.3931](https://arxiv.org/abs/0805.3931)), FZZ duality with boundary
([arXiv:1012.4731](https://arxiv.org/abs/1012.4731)), and higher-rank FZZ
dualities ([arXiv:2010.14681](https://arxiv.org/abs/2010.14681)).  None states
this puncture dark-pencil spectral-width obstruction.

Novelty priority remains provisional pending expert/database review; theorems
are unconditional and formally checked.

## Verification

- Direct `lake env lean` check: passed.
- Targeted module build: passed.
- Axiom audit: all eight exported theorems use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Umbrella import: wired; full umbrella build intentionally not run.
