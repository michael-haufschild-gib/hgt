# Burnol stage-2 folder: first Lean layer (2026-08-09)

Target: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/burnol/` (9 cards).

## Promoted to stage 3 (verified, clean axioms, umbrella-wired)

- `burnol-divided-shift-evaluation-separation-law` (+ `-formalized.md` companion) —
  `RHTower/BurnolDividedShiftEvaluationSeparation`, five theorems, was already formalized.
- `burnol-holonomy-cauchy-sector-separation` (+ companion) —
  `RHTower/BurnolHolonomyCauchySectorSeparation`, three theorems, was already formalized.

## New Lean modules built this session (all in `RHTower/`, all umbrella-wired)

| Module | Covers |
|---|---|
| `BurnolPrimeLogSummability` | `∑ 1/(p log²p) < ∞` (telescoping), Euler divergence on the subtype, `log^k = o(x^δ)`, `u^k e^{-2y√u} ≤ C/u²` |
| `BurnolAllPrimeCompletionWall` | card 8 essentially complete: `C_p F_p = ξ`, shuttle/potential/boundary identities, the sharp `ℓ²` wall `Re ρ ≤ 1/2` both directions, physical-endpoint correction |
| `BurnolGammaSteinCollarKernel` | cards 3/4/5: Stein profile calculus, `κ_n`, three-chamber sign law + width `½log6`, translate law, deformed kernel `κ_ε`, Bockstein kernel + sign chambers |
| `BurnolGammaSteinMoments` | master Gamma-moment identity via `z = C e^{-2u}`; `∫γφ=1`, `∫κ_ε φ = ε(1+ε)²/2`, `∫κ_*φ=0`, `2∫κ̇φ=1`, `∫κ_n = -(2^{-n/2}/16)Γ_ℝ(1/2) < 0` |
| `BurnolFirstWallResiduePolarization` | card 3 Theorem 3: `(24)`, `(25)`, `(18)`, landing on `burnolCartierDividedShiftHeadFlux` |
| `BurnolDyadicCoboundaryContraction` | card 3 Theorem 1: `T₂f₀ = -{t}/t` pointwise (HasSum) and in `L²(0,∞)` |
| `BurnolDyadicCommutatorStaircase` | card 4 Theorem 4: staircase `(19)`, `‖[P_a,T₂]f‖² = 2a‖c‖²`, and the `J_ρ` difference `(21)` |
| `BurnolPrimeCartierWallTrace` | card 6: sideband residues, zero-wall derivative, both unit-gain traces, horizon gap, `(CH23)` |
| `BurnolReciprocalStokesSewing` | card 7: `m_p`, `S_p` reflection + `‖S_p‖ ≤ 6`, sewn conormal always `ℓ²`, unsewing wall, `Q ∉ ℓ²` |
| `BurnolPoissonSubordinateWall` | card 9: `(PS6)`–`(PS10)`, `(PS14)`–`(PS16)`, the smooth wall `(PS4)` |

Each card in stage 2 now carries a `## Lean formalization` table mapping equations to declarations
and naming exactly what is still open.

## What is still open per card (the real frontier)

- card 3: tail/endpoint mass `(10)`–`(17)` of `g_ρ`, deep-profile limit `(29)`, `(30)`–`(31)`, Cor 5.
- card 4: asymptotic Bockstein extraction `(13)`, `(15)`, `(16)`, transgression `(22)`.
- card 5: operator realization `(3)`/`(4)`, `γ̂ = Γ_ℝ` `(7)`, normal convergence `(11)`,
  `(18e)`–`(18g)`, crossing formula `(19)`, landings `(22)`, `(24)`.
- card 6: cofinite radius law `(CH10)`, maximal-germ nonclosed range `(CH13)`–`(CH17)`.
- card 7: window norms `(HJ2)`, direct-sum membership `(HJ3)`, packaged `(HJ5)`.
- card 9: Poisson subordination identity `(PS2)`/`(PS11)`, `(PS12)`–`(PS13)`.

Cards 3, 4, 5 all need the same missing object: the actual zero-divided source `g_ρ` on the ray,
its constant head, its `O(t^{-2})` tail, and the aperture-crossing correlation `W_G`.  Build that
once and four card items close at the same time.

## Two traps hit

1. **`lake env lean` can pass against a stale olean set.**  `BurnolPoissonSubordinateWall` was clean
   per-file and then produced six errors under `lake build GaloisForLFunctions.RHTower`.  Treat the
   umbrella build as the only real gate (see `mem:rhtower_umbrella_collisions_2026_08_07b`).
2. **Two committed modules are rotten and block the RHTower umbrella**, independent of this work:
   `HTGeometry/HalfLineCoshPrimitive.lean` (lines ~387–404) and
   `RHTower/DeningerCriticalFloquetVonMangoldtWall.lean` (many, incl. unknown constant
   `intervalIntegral.integral_eq_zero`).  Both are clean in `git status`; per-file checks pass
   against their stale oleans.

## Technique notes worth reusing

- Every collar moment reduces to one master identity: substitute `z = C e^{-2u}` (Jacobian `2z`,
  `integral_image_eq_integral_abs_deriv_smul` with `s = univ`), then the integrand is
  `e^{-z} z^{s-1}·cubic` and the answer is a Gamma combination.  No integration by parts is needed
  for `(27)`/`(28)`.
- `field_simp` on the *whole* collar expression is very slow; factor the polynomial out as an
  opaque variable (`burnolCollarProfile_mul_mode (P u : ℝ)`) and the file compiles in seconds.
- The cofinite-comparison pattern for prime divergence: `Set.Finite.preimage Subtype.val_injective`
  for the small-prime set, `Summable.subtype`, then `Set.Finite.summable_compl_iff`.
