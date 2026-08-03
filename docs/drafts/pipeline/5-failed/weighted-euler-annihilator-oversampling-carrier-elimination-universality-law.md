# Weighted-Euler annihilator oversampling carrier-elimination universality law

- **ID:** weighted-euler-annihilator-oversampling-carrier-elimination-universality
- **Stage:** failed/retired after hostile nonvacuity audit
- **Type:** VACUOUS THEOREM ON THE INTENDED NONEMPTY CARRIER
- **Source:** theorem-generated closure of weighted-Euler graph dual reduction, unconditional
  prime-log Lambert oversampling, quantitative Möbius ray recovery, and carrier separation
- **Statement:** The formal implication is valid, but its hypotheses have no instance on a
  nonempty positive-strip carrier. The current oversampling mechanism therefore cannot prove
  carrier elimination.

## Goal

Close the full weighted-Euler dual pipeline. Existing endpoints separately turn graph
annihilation into prime-log Lambert samples, samples into large-ray Lambert decay, multiplicative
Lambert decay into a Fourier--Borel bound, and a super-carrier Fourier--Borel bound into global
vanishing. No corpus theorem composes all four mechanisms.

## Gates

- [x] 0 → 1 in-progress: full source read, corpus research search, well-posed theorem, source-pure
  attack
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check and RHTower umbrella import
- [x] 3 → 4 novelty audit: post-proof literature search found no collision

## Corpus inputs

- `norm_lambert_primeLog_le_of_graph_annihilation`
- `norm_le_ray_of_primeLog_sampled_lambert`
- `norm_compactFourierBorel_le_of_sampled_lambert_decay`
- `compactFourierBorel_eq_zero_of_ray_decay`
- `map_coordinate_pow_eq_zero_of_fourierBorel_zero`

## Proof

**[PROVED HERE]** Let the carrier coordinate `s` satisfy
`α ≤ Re(s(k)) ≤ β`, with `α > 0`, and let the prime-log coefficient bound have
rate `σ > 0`. Put `κ = min(σ, α/2)` and assume `β < κ`.

For every prime `p`, the graph relation

`λ_p + L(u_p) = 0`

and coefficient-dual estimate

`‖λ_p‖ ≤ C log(p) p^{-σ}`

give

`‖Λ_L(log p)‖ ≤ C p^{-σ} = C exp(-σ log p)`

by weighted-Euler dual reduction. Unconditional compact-carrier oversampling therefore supplies
constants `D` and `R₁` such that

`‖Λ_L(y)‖ ≤ D exp(-κ y)` for `y ≥ R₁`.

Replace `D` by `max(D,0)` and choose

`R ≥ max(R₁, 0, log(2)/κ)`.

For `x ≥ R` and every positive integer `n`, one has `nx ≥ R₁`, hence

`‖Λ_L(nx)‖ ≤ D exp(-κnx) = D ρ_x^n`,

where `ρ_x = exp(-κx) ≤ 1/2`. The lower carrier wall also gives

`‖exp(-nxs)‖ < 1`

and the geometric Fourier--Borel majorant required by quantitative Möbius inversion. Möbius ray
recovery yields

`‖FB_L(x)‖ ≤ 4D exp(-κx)`

on the whole tail `x ≥ R`.

For `0 ≤ x < R`, the ordinary compact-carrier growth estimate gives

`‖FB_L(x)‖ ≤ ‖L‖ exp(‖s‖x)
             ≤ ‖L‖ exp((‖s‖+κ)R) exp(-κx)`.

Thus one global constant bounds `FB_L` by `exp(-κx)` for every `x ≥ 0`.
Since `β < κ`, carrier separation forces `FB_L` to vanish identically. Fourier--Borel
coefficient detection then gives `L(s^m)=0` for every `m`. ∎

## Strict gain over corpus endpoints

The result discharges the uniform multiplicative-ray hypothesis of the earlier Lambert
carrier-separation law from actual prime-indexed graph-annihilator data. The nontrivial new
connector is that a one-variable oversampled tail becomes a geometric family after evaluation
at every integer multiple of a sufficiently large base point; the finite initial ray is then
absorbed by the carrier growth bound.

## Lean formalization

- Main theorem:
  `compactFourierBorel_eq_zero_of_primeLog_graph_annihilation`
- Module:
  `GaloisForLFunctions.RHTower.WeightedEulerAnnihilatorOversamplingCarrierEliminationUniversalityLaw`
- Verification:
  `lake env lean GaloisForLFunctions/RHTower/WeightedEulerAnnihilatorOversamplingCarrierEliminationUniversalityLaw.lean`
  passed without warnings.
- Umbrella:
  imported by `GaloisForLFunctions/RHTower.lean`.

## Novelty audit

Post-proof searches found the classical Lambert-series/Möbius inversion identity, ordinary
Paley--Wiener carrier theorems, and sampling theorems for band-limited functions. They did not
find a theorem combining prime-log graph-annihilator estimates, oversampling, multiplicative-ray
Möbius recovery, and compact-functional carrier elimination. Relevant comparison points:

- NIST DLMF, “Lambert Series as Generating Functions”:
  `https://dlmf.nist.gov/27.7`
- Paley--Wiener theorem overview:
  `https://en.wikipedia.org/wiki/Paley%E2%80%93Wiener_theorem`
- “Uniform and non-uniform sampling of bandlimited functions at minimal density with a few
  additional samples”:
  `https://link.springer.com/article/10.1007/s43670-022-00041-7`

Novelty remains a negative-search conclusion, not a claim of bibliographic completeness.

## Log

- 2026-07-23 — generated from residual terminal pair linking weighted-Euler dual reduction,
  unconditional Lambert oversampling, and Lambert carrier separation.
- 2026-07-23 — corpus research found no existing theorem closing graph annihilation through
  oversampling and Möbius recovery to global carrier elimination.
- 2026-07-23 — dependency-closed paper proof completed before Lean implementation or literature
  search.
- 2026-07-23 — exact-file Lean verification passed; module wired into RHTower umbrella.
- 2026-07-23 — post-proof literature audit found no exact or equivalent law.
- 2026-08-03 — hostile nonvacuity audit found the decisive contradiction. On a nonempty carrier,
  `hstrip` gives `α ≤ β`; the claimed separation hypothesis gives
  `β < min(σ,α/2) ≤ α/2 < α`. Thus the theorem applies only when the carrier is empty.
  Formalized as `not_beta_lt_min_sigma_half_alpha_of_nonempty_positiveStrip`. The route is
  retired; any replacement must improve continuous-ray decay beyond the upper carrier wall,
  rather than reuse the present `α/2` oversampling rate.
