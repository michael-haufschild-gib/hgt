# Mass-shifted adaptive arithmetic source far-right positivity

- **ID:** mass-shifted-adaptive-source-far-right-positivity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3, successor to Conjecture 55
- **Statement:** Every fixed nonzero adaptive amplitude makes the literal completed mixed arithmetic source strictly positive at all sufficiently large square-root masses.

## Goal

Sign the source-first producer itself,

\[
 \mathsf{Arch}_{w,A}+\int_1^\infty K_{w,A}(x)\,dx
 -\sum_m\Lambda(m)K_{w,A}(m),
\]

without replacing it by a fixed reporter, orientation map, or reflected aggregate. Determine exactly
which noncompactness can still support a negative source event.

## Gates

- [x] 0 → 1 in-progress: source-pure statement and exact asymptotic attack
- [x] 1 → 2 fully-proven: complete paper proof below, `[PROVED HERE]`
- [x] 2 → 3 formalized: unconditional Lean theorem, target build, axiom audit
- [ ] 3 → 4 publication-ready

## Paper proof `[PROVED HERE]`

Let `A ≠ 0`, let `d` be its least nonzero degree, and write `a_d` for its least nonzero
coefficient. The adaptive shear polynomial is

\[
 Q_A=(XA)\,\bigl(X(XA'+A)\bigr).
\]

The first factor has least degree `d+1` and least coefficient `a_d`. The shifted Euler factor
`XA'+A` has coefficient `(k+1)a_k` in degree `k`; hence its least degree is `d` and its least
coefficient is `(d+1)a_d`. Therefore

\[
 \operatorname{ord}_0 Q_A=2d+2,
 \qquad [X^{2d+2}]Q_A=(d+1)a_d^2>0.                 \tag{1}
\]

For every fixed `k`, the unconditional shifted-Xi source asymptotic already proved in the corpus is

\[
 \frac{2w^{2k+1}}{\log w}\,\Re m_k(w^2)\longrightarrow
 c_k:=\binom{2k}{k}4^{-k}>0.                       \tag{2}
\]

Expand the finite polynomial moment functional `L_w(Q_A)=Σ_k q_k Re m_k(w²)` and multiply by
`2w^(4d+5)/log w`. Terms below `2d+2` vanish by (1). The term at `2d+2` tends to
`(d+1)a_d² c_(2d+2)`. Every higher term is its normalized limit from (2) times an additional
inverse even power of `w`, hence tends to zero. Thus

\[
 \frac{2w^{4d+5}}{\log w}L_w(Q_A)
 \longrightarrow (d+1)a_d^2c_{2d+2}>0.            \tag{3}
\]

For `w>1`, the scale in (3) is positive, so `L_w(Q_A)>0` eventually. Existing exact identities
give completed adaptive packet `= 2L_w(Q_A)` and, for `w>1/2`, completed adaptive packet `=` the
literal Archimedean-plus-Lebesgue-minus-von-Mangoldt formation of the common endogenous kernel.
Consequently that arithmetic source is strictly positive eventually. No RH assumption, numerical
computation, interchange of infinite polynomial sums, or uniformity in degree is used.

## Hostile conjecture loop

- **Conjecture:** fixed finite Hankel positivity already signs adaptive shear. **Fails:** adaptive
  shear is bilinear, not a square; positive definiteness alone does not sign its cross term.
- **Conjecture:** one confluent three-point determinant signs the source. **Fails:** it controls a
  different fourth-order Turán combination and does not identify reciprocal-moment shear.
- **Conjecture:** fixed amplitude can remain a far-right negative source. **Fails by (1)–(3):**
  arcsine recession sees a strictly positive least coefficient.
- **Positive survivor:** every fixed nonzero admission has a finite positivity horizon.

## New principle

Literal source landing is complete; obstruction is nonuniform admission under recession. Any
RH-false crossing compatible with a later negative source must use amplitudes whose degree or
least-coefficient conditioning outruns their positivity horizons. This places the residual
finite-to-global obstruction exactly in effectivity/nonproperness, not in missing orientation.

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/XiShiftedAdaptiveArithmeticSourceFarRightPositivity.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Capstones:
  - `tendsto_scaled_xiShiftedMomentFunctional`
  - `xiShiftedBoundaryAdaptiveShearPolynomial_trailing`
  - `tendsto_scaled_xiShiftedAdaptiveArithmeticSource`
  - `xiShiftedAdaptiveMixedCompletedArithmeticSource_eventually_pos`
  - `exists_xiShiftedAdaptiveMixedCompletedArithmeticSource_pos_horizon`
- Direct check: PASS, warning-free.
- Target build: PASS.
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
- Formal lint: new module is forbidden-declaration clean and umbrella-wired. Repository lint remains
  red on unrelated concurrently unwired Hedenmalm/XiMass/HTGeometry modules.

## Exact successor

Prove a degree/conditioning-uniform positivity horizon for amplitudes emitted by actual null flags,
or prove those admissions cannot escape every fixed-degree compact set along the outgoing ray.
