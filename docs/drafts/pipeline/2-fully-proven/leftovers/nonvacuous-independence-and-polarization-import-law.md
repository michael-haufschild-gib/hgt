# Non-vacuous independence and the polarization import law

- **ID:** ULF-INV-6
- **Stage:** 2-fully-proven
- **Type:** METATHEOREM (paper) / UPGRADE OF ULF-INV-5 THEOREMS B AND D
- **Source:** the vacuity caveat of ULF-INV-5 §3, attacked directly
- **Statement:** The independence of the polarization clause survives the vacuity caveat:
  noncompact finite-area hyperbolic surfaces with small first eigenvalue satisfy the Selberg-world
  analogues of N1–N6 **non-vacuously — including the cusp clause N5 and geometric truncation
  N2 —** while their Selberg-zeta RH fails with explicit off-critical real zeros. Hence even the
  full no-go specification with genuine infinite-dimensional cusped structure does not force the
  conclusion; only polarization does. Calibration upgrade: in every world where the
  RH-analogue is proved, the polarization is *imported* from the function-field world where it is
  native geometry (Castelnuovo/Deligne); the rationals sit at the top of the import chain with no
  upstream world, which derives the exact fork the two major programs occupy.
- **Status:** [PAPER-PROVED AT CITATION LEVEL] [VACUITY CAVEAT CLOSED] [IMPORT STRUCTURE
  OBSERVED, NOT CLAIMED AS THEOREM] [NOT RH] [LEAN CORE CERTIFIED]

## 1. Theorem B′ — the non-vacuous independence witness

Let \(S=\Gamma\backslash\mathbb H\) be a noncompact finite-area hyperbolic surface obtained by
pinching a separating geodesic of a finite-area surface with cusps (Buser-type construction;
classically, pinching drives \(\lambda_1\to0\), and the construction coexists with cusps —
Buser, *Geometry and Spectra*; Colin de Verdière). Choose the pinching so that
\(0<\lambda_1<\tfrac14\). Then:

1. **N5 non-vacuous:** \(S\) has cusps; the spectral decomposition has continuous (Eisenstein)
   spectrum; the heat/wave traces diverge naively and are rendered finite by the Maass–Selberg /
   truncation mechanism — which is *restriction to a compact core*, a geometrically positive
   operation (multiplication by an indicator), exactly the shape N2 demands and the moment
   category cannot express.
2. **N1, N3, N4, N6 non-vacuous:** the pairing is the Selberg trace formula (geometric, not a
   regularized moment limit of the length spectrum); upper bounds on eigenvalue counts come
   from `count ≤ trace` (Weyl law with the truncated trace); the length spectrum begins at the
   systole of \(S\); the identity/volume term plays the pole role and every spectral estimate
   spends it.
3. **The RH-analogue fails, exactly:** the Selberg zeta \(Z_S\) has zeros at
   \(s=\tfrac12\pm\sqrt{\tfrac14-\lambda}\) for each eigenvalue \(\lambda\); since
   \(\lambda_1<\tfrac14\), there are real zeros in \((0,1)\setminus\{\tfrac12\}\) — off the
   critical line.

Hence the specification N1–N6, satisfied with genuine infinite-dimensional content, a genuine
cusp, and a genuine geometric truncation, is consistent with failure of the conclusion. The
missing clause is precisely the spectral-gap/polarization statement \(\lambda_1\ge\tfrac14\),
which for congruence \(\Gamma\) is **Selberg's eigenvalue conjecture** — open since 1965. The
specification's N7, instantiated in the nearest continuous world, is a named 60-year-old open
problem; ULF-INV-5's vacuity caveat is closed and its Theorem D sharpens: the joint model
{N5, N2, N7} exists *conjecturally* (congruence quotients), with exactly N7 unproved there.

## 2. Theorem D′ — the polarization import structure

Where does N7 ever get proved? Reading the proofs:

| world | RH-analogue proved? | where the polarization comes from |
|---|---|---|
| curves over \(\mathbb F_q\) | yes (Weil) | **native**: Castelnuovo positivity — geometry of \(C\times C\) |
| varieties over \(\mathbb F_q\) | yes (Deligne) | native + amplification: purity via tensor-power monodromy |
| Ramanujan graphs (LPS) | yes, for the constructed families | **imported**: Ramanujan–Petersson via Eichler–Shimura from Deligne — function-field positivity transported to graphs |
| congruence \(\Gamma\backslash\mathbb H\), archimedean place | partial (\(\lambda_1\ge\) Kim–Sarnak bound) | **imported through functoriality**: poles of symmetric-power \(L\)-functions — bounded-degree purchase |
| \(\zeta\) over \(\mathbb Q\) | open | — no upstream world exists |

Observation (recorded as structure, not theorem): polarization has never been proved *in-world*
outside function-field geometry; every other instance is an import along a correspondence whose
source is the function-field world. The rationals are terminal in this import order. Therefore
any adequate theory must do one of exactly two things:

- **Fork (a) — make polarization native over \(\mathbb Q\):** construct the cusped polarized
  geometric-truncation object directly (the Deninger/Connes shape). The corpus's constraints on
  this fork are the axioms: the object's corner is noncompact (N5), its truncation is geometric
  (N2), its normalizers pay the systole floor (N4), its bounds spend the pole (N6), and none of
  it lives in the moment category (N1, N2).
- **Fork (b) — build a new upstream world:** a geometry in which \(\operatorname{Spec}\mathbb Z\)
  becomes a curve-like object with a genuine product \(\ \times\ \) and an intersection theory,
  from which positivity can be imported (the \(\mathbb F_1\)/global-field-analogy shape). The
  corpus constraint here is ULF-INV-1/N1: the import correspondence cannot factor through
  Mertens-normal moment data — it must transport more than asymptotics.

The two forks are precisely the two major live programs in the literature; what the inverse
theory adds is that the fork is *forced* (Theorem B′: nothing weaker suffices) and that each
fork inherits a specific, machine-checked constraint list.

## 3. Hostile scope

- Small-eigenvalue cusped surfaces: classical (Buser; Randol; Colin de Verdière); Selberg zeta
  zero dictionary: standard (Hejhal). Nothing new claimed in the witness itself — its role
  against the axiom list is the contribution.
- The import table is a reading of proofs, cited; the "terminal in the import order"
  observation is exactly that — an observation about existing proofs, not a nonexistence
  theorem about future correspondences. Fork (b) is not excluded by it; it is *specified* by it.
- This card does not advance either fork; it proves the fork is exhaustive relative to the
  specification and equips both sides with the corpus's constraint lists. The program's next
  falsifiable targets remain ULF-INV-4 (general-d barrier) and the fork-(a)/(b) constraint
  instantiations.

## 4. Lean status

The self-contained quantitative content of Theorem B′ clause 3 is certified in
`GaloisForLFunctions.HTGeometry.SelbergSpectralParameter`, wired into
`GaloisForLFunctions.HTGeometry.UniversalLawField`: for `0 < λ < 1/4` the two spectral parameters
`1/2 ± √(1/4 − λ)` are real, lie in `(0,1)`, are distinct, are neither equal to `1/2`, and sum to
`1` (`selbergSmallEigenvalue_offCritical`); they coincide with `1/2` exactly at the Selberg bound
(`selbergSpectralParameter_eq_half_iff`).

The remaining clauses of B′ are citation-level: the existence of pinched finite-area cusped
hyperbolic surfaces with `λ₁ < 1/4` (Buser; Colin de Verdière) and the Selberg-zeta zero
dictionary (Hejhal).  Formalizing them requires a hyperbolic-surface spectral layer — Laplace
spectrum on `Γ\ℍ`, Eisenstein series, Maass–Selberg truncation, the Selberg trace formula and the
Selberg zeta function — which is present neither in mathlib nor in this corpus.  Theorem D′ is
explicitly recorded as an observation about existing proofs, not a theorem, so it carries no Lean
obligation.

## Log

- 2026-08-09 — created: vacuity caveat of ULF-INV-5 closed with the cusped thin-neck witness;
  Selberg's conjecture identified as N7's instance in the continuous world; polarization import
  structure tabulated; the two-fork conclusion derived with per-fork constraint lists.
- 2026-08-11 — the off-critical spectral-parameter core certified in Lean; the remaining clauses
  recorded as citation-level, with the missing hyperbolic-spectral layer named explicitly.

## Lean programme for Theorem B′ (2026-10-09)

A corpus audit was made on 2026-10-09. The Lean status above is out of date: mathlib now has the invariant
measure on `ℍ` (`Analysis/Complex/UpperHalfPlane/Measure`) and the Petersson product, and the corpus has
Maass cusp forms, Poincaré and Eisenstein series for `Γ(N)`, Fourier expansions, and the non-existence
theorems `selberg_status` (3/16, levels ≤ 25).  Every one of these is a *non-existence* or explicit
statement.  Theorem B′ needs *existence* of a small eigenvalue and the Selberg-zeta zero dictionary, which
no corpus module provides.

The witness is Selberg's cyclic cover.  Γ(2)/{±1} is free on `A = [[1,2],[0,1]]` and `B = [[1,0],[2,1]]`
(Sanov).  Let `ψ : Γ(2) → ℤ` be the exponent sum of `A`, and put `Γ_N = ker(ψ mod N)`: it has finite index
in `SL(2,ℤ)` and is torsion-free modulo `±1`, so `Γ_N\ℍ` is a noncompact finite-area surface.  Test
function: `f = e^{iπx/N} g(y)` in the two cusps where `ψ` is nontrivial on the stabiliser, and `≈ 1`
elsewhere.  With `g` cut off at height `≈ N`, the Rayleigh quotient is `O(1/N)`; the function is orthogonal
to the constants after lifting.

```text
S1  Sanov + winding homomorphism ψ (GammaTwoSanov)                         [delegated to hgt-61]
S2  cusp Hardy inequality ∫|f|²y⁻² ≤ 4∫|f'|² + 2|f(Y)|²/Y: the constant term costs ≥ 1/4
S3  L²(Γ\ℍ) on a fundamental domain built from SL(2,ℤ)-cosets; the Dirichlet form
S4  variational existence below 1/4: minimising sequences are tight, by S2 on the cusp constant terms
    and by the Fourier gap (2π/w)² on the nonconstant cusp modes; Rellich on the compact core
S5  regularity: a weak eigenfunction is a smooth Maass eigenfunction (hyperbolic mean value /
    point-pair invariants)
S6  the test function on Γ_N: λ_1(Γ_N) ∈ (0, 1/4) for N large            ⇒ B′ clauses 1–2 witness
S7  Selberg zeta Z_Γ (Euler product over primitive hyperbolic classes, Re s > 1)
S8  spectral decomposition of L²(Γ\ℍ) (Eisenstein continuation for cofinite Γ) and the Selberg trace
    formula with scattering terms; Z_Γ meromorphic, ord_{s_j} Z_Γ = mult(λ_j) for s_j ∈ (1/2, 1)
                                                                          ⇒ B′ clause 3
```

Open point to settle in S8: the card claims zeros at *both* `1/2 ± √(1/4 − λ)`.  For a residual
eigenvalue the order of `Z_Γ` at `1 − s_j` involves the scattering determinant.  The theorem will be
stated exactly as the trace formula gives it.  Any correction this forces is recorded here and sent back
through the paper audit.  The zero at `s_j ∈ (1/2, 1)` alone already refutes the RH-analogue.

### Refined route for clause 1–2 (existence), 2026-10-09

The existence step uses no form domain and no Rellich lemma.  The proof works throughout with
fields twisted by a unitary representation `ρ` of `SL(2, ℤ)` on `ℂ^ι` (`RHTower/RepPointPair*`,
ported from the congruence deck stack).  For the witness, `ρ` is the regular representation of
`SL(2,ℤ)/Γ'`, where `Γ'` is the normal core of `Γ_N = ker(Γ(2) → ℤ/N)` and the map is the winding
homomorphism `gammaTwoWinding`.

1. `L_φ` (φ ≥ 0 continuous, compactly supported, unit mass) is a bounded symmetric operator
   (`RepPointPairOperator`, `RepPointPairSymmetry`), with C² images (`RepPointPairRegularity`,
   Laplacian port).
2. **Cusp splitting** `L_φ = K + B`.  `K` has a continuous kernel supported in a compact region; it is
   compact by Stone–Weierstrass, being a norm limit of finite-rank operators.  `B = ψ L_φ ψ` lives high
   in the cusp, where only `±Tⁿ` act.  Fourier modes in `x` (eigenspaces of `ρ(T)`) diagonalise `B`:
   - on the constant term, `B` is a multiplicative convolution, and the Schur test with weight `y^{1/2}`
     gives norm `≤ h_φ(1/2)`;
   - on the other modes, two integrations by parts give norm `≤ C/(ξ₀Y)²`.
   Hence `‖B‖ ≤ h_φ(1/2) + ε`.
3. **Fredholm step.**  Let `M = sup ⟨L_φ f, f⟩` over unit `f ⊥ constants`.  If `M > ‖B‖`, then `M` is an
   eigenvalue: `M − L_φ` is not bounded below, since `‖Sx‖² ≤ ‖S‖⟨Sx, x⟩` for `S ≥ 0`.  Moreover
   `L_φ − M = (B − M)(1 + K')` with `K'` compact, so mathlib's Fredholm alternative applies.  The
   eigenspace is finite-dimensional.
4. The `M`-eigenspace is `L_{Dφ}`-invariant, so it contains a C² Laplace eigenfunction `U`.  Selberg's
   theorem gives `M = h_φ(s)`.  Then:
   - `|h_φ(½+ir)| ≤ h_φ(½) < M` excludes `λ ≥ ¼`;
   - `h_φ(s) > 1 ≥ ‖L_φ‖` for `s > 1` excludes `λ < 0`;
   - ergodicity of `L_φ`, together with `U ⊥ 1`, excludes `λ = 0`.
   So `λ ∈ (0, ¼)`.
5. **Test function** on `Γ_N`: `F = (λ/|λ|)^{1/N} κ(log|λ|)`, with `λ` the modular lambda function
   (corpus `Bottcher/ModularLambda*`) and `κ` a ramp cutoff at scale `L = N`.
   - `F` is `Γ_N`-invariant, and the phase average gives `F ⊥ 1`.
   - Its Dirichlet energy is `O(1)`.  The mass is `≍ N`.
   - `⟨(1 − L_φ)F, F⟩ ≤ C_φ D(F)` then forces `M > h_φ(½) + ε` for `N` large.

### Lean log, existence step (2026-10-09)
- `HTGeometry/CompactPerturbationTopEigenvalue`: the abstract Fredholm step for symmetric
  `L = K + B` with `K` compact, `‖B‖ ≤ b` and `re⟪Lf, f⟫ > b‖f‖²`. Its supremum `M > b` is an
  eigenvalue (`exists_eigenvector_of_compact_add`), and the eigenspace is finite-dimensional
  (`finiteDimensional_eigenspace_of_compact_add`).
- `RHTower/RepPointPairCuspBound`: the cusp bound `‖ψ_Y L_φ ψ_Y‖ ≤ h_{|φ|}(½)` once
  `Y² > 4R + 2` (`norm_cuspOp_le`). The proof is the weighted Schur test with weight `y^{1/2}`,
  so the route needs no Fourier-mode split. Supporting results:
  - `im_smul_le_of_mem_fd`: height maximality of the modular cell;
  - `c_eq_zero_of_pairU_le_high`: only `±Tⁿ` act high in the cusp;
  - `integral_kernel_sqrt`: the weight identity.
- `RHTower/SelbergTransformRealMonotone` (hgt-8a), facts about `h_φ`:
  - `h(s) = h(1−s)`;
  - realness and positivity on ℝ;
  - strict monotonicity on `[½, ∞)`;
  - `|h(½+ir)| ≤ h(½)`;
  - `h(1)` is the mass, and the mass is `< h(σ)` for `σ > 1`.
- In progress: `RHTower/RepPointPairCoreCompact`, compactness of the core part `χ_H L_φ χ_H`
  through the corpus Hilbert–Schmidt kernel theorem.
- Existence chain DONE in Lean (all installed, wired, 0 warnings):
  - `RHTower/RepPointPairCoreCompact`: `isCompactOperator_coreOp`. The core `χ_H L_φ χ_H` is compact,
    via the corpus Hilbert–Schmidt kernel theorem (`RHTower.isCompactOperator_kernelOperator`)
    applied coordinatewise, with the Riesz vectors continuous in `L²` by dominated convergence.
  - `RHTower/RepPointPairCuspSplitting`: `ppL2_sub_cuspOp` (`L − ψLψ = χLχ − ψ(χLχ)ψ`, with
    `H = 2(4R+2)Y`) and `isCompactOperator_ppL2_sub_cuspOp`.
  - `HTGeometry/CompactPerturbationInvariantSubspace`: `exists_eigenvector_of_compact_add_orthogonal`,
    the top eigenvalue on `Vᗮ` for an invariant `V`.
  - `RHTower/RepPointPairTopEigen`: `invConst` (span of the constants with invariant values),
    `ppL2_constRep` (`L c = m c`), `exists_top_eigenvector`, `finiteDimensional_eigenspace_ppL2`.
  - `RHTower/RepPointPairSmallEigen`:
    - `exists_lap_eigenvector`, a joint `L_φ, L_{Dφ}` eigenvector in `Vᗮ`;
    - `selbergTransform_eq_of_lapEigen`, `h_φ(s) = m`;
    - `laplaceEigenvalue_mem_Ico`, giving `0 ≤ λ < ¼`.
  - `RHTower/RepPointPairDirichletForm`: `integral_dirichlet`,
    `∫_𝒟∫_ℍ φ(u)‖U(z)−U(w)‖² = 2m∫_𝒟‖U‖² − 2∫_𝒟 re⟪U, L_φU⟫`, using the dual tiling
    `lintegral_fd_kernel_mul_invariant`.
  - `RHTower/RepPointPairErgodic`: `eq_const_of_ppApply_eq_mass`. For `φ(0) > 0`, `L_φU = mU`
    forces `U` to be an invariant constant, which excludes `λ = 0`.
  - Peer bricks (hgt-8a):
    - `RHTower/RepCosetRepresentation`: `cosetRep`, `cosetLift`, equivariance and the converse,
      `hypLap_cosetLift`;
    - `RHTower/ModularLambdaWindingLog`: `windingSubgroup N` (finite index), `lambdaLog`,
      `lambdaLog_smul` (cocycle = `gammaTwoWinding`), `exp_lambdaLog_div_smul`,
      `exists_norm_modularLambda_le`.
- REMAINING for clauses 1–2: the test field. Take `f = e^{i Im ℓ/N} κ_L(Re ℓ)` with `ℓ = lambdaLog`,
  `F = cosetLift f` for `Γ_N = windingSubgroup N`.
  - Needed: `F ⊥ invConst`. This holds pointwise, since `A = T²` normalizes `Γ_N` and
    `f(A⁻¹w) = e^{−2πi/N} f(w)`, so `Σ_q F_q(z) = 0`.
  - Needed: `D(F) < 2(m − h(½))‖F‖²`.
  - Plan for `D(F)`:
    - (P1) Selberg at `s = 1` gives the hyperbolic mean value `g(z) m_ψ = ∫ψ(u(z,w))g(w)` for
      holomorphic `g`;
    - (P2) Cauchy–Schwarz then gives `y²|ℓ'(z)|² ≤ C L_ψ(y²|ℓ'|²)(z)`;
    - (P3) the segment estimate `|ℓ(z)−ℓ(w)|² ≤ C ∫ 1[u(z,η) ≤ R'] y²|ℓ'(η)|² dμ(η)` for
      `u(z,w) ≤ R`;
    - (P4) distortion of `Re ℓ` on near pairs at the cusps;
    - (P5) dual tiling plus the area bound `area(ℓ(D₂) ∩ {|Re| ≤ T}) ≤ 4πT` (hgt-8a,
      `ModularLambdaTestEnergy`, in progress), giving `D(F) ≲ L/N + N/L` against `‖F‖² ≳ N`.
- Clause 3 (Selberg zeta zeros) is not started. It needs `Z_Γ` and the trace formula for
  noncongruence cofinite `Γ`.
