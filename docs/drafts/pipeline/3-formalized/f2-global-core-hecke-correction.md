# F2 — corrected source Hecke transport of actual physical cores

- **Stage:** 3-formalized
- **Result:** For every prime `p` and every `0<Re s<1/2`, `Im s>0`, an explicit correction using two physical evaluations makes the actual PM core a source Hecke eigenfunction with eigenvalue `1+p^(1−2s)`. At upper resonances only one scattering channel remains.
- **Scope:** Parameterized physical source operators; no assumed arithmetic coefficients, positive metric, or common operator on mixed-parameter synthesis.

The [audited global identity](f2-global-actual-core-identity.md) is

`core_s=E_s−ζ(w)A_w−b_sP_w`,

where `w=2s`, `A_w(a)=1+a^(−w)`, `P_w(a)=a⁻¹+a^(1−w)`, and `b_s=2ζ(w−1)/(w−1)`. It holds for the literal Cauchy integral at every `a>0`.

## Recovering the boundary coefficients from the core

The scattering-state normalization at `1` gives

`core_s(1)=b_s(w−3)−2ζ(w)`.

The existing exact core Hecke error at `1`, together with actual inversion, gives

`2core_s(2)=b_s(w−2−4q)−2ζ(w)(1+q)`, `q=2^(−w)`.

Set `D_w=1−(w+1)q`. If `D_w=0`, then `2^w=w+1`; taking real parts and using the norm of the complex power gives `1+σ≤2^σ`. Strict convexity of the exponential gives `2^σ<1+σ` for `0<σ<1`, a contradiction. Thus

`β_s(f)=[2f(2)−(1+q)f(1)]/D_w`,

`α_s(f)=[(w−3)β_s(f)−f(1)]/2`

are well-defined explicit linear evaluation functionals. On the actual core they equal `b_s` and `ζ(w)`.

## Corrected physical Hecke law

Write `λ_s=1+2q`. Define

`T̂_s f=T₂,s f+α_s(f)(T₂,s A_w−λ_s A_w)+β_s(f)(T₂,s P_w−λ_s P_w)`.

Apply the global actual-core identity and the existing completed-period eigenlaw. Linearity and the recovered coefficients give

`T̂_s core_s=λ_s core_s`

pointwise on `(0,∞)`. At resonances `α_s(core_s)=0`, and the remaining coefficient is already `core_s(1)/(w−3)`.

## All-prime extension

For each prime `p`, put `λ_(p,s)=1+p^(1−2s)` and replace `T₂,s` in the correction by the actual finite-cone source operator `T_(p,s)`. The same `α_s,β_s` recover the coefficients independently of `p`. All source branches have positive arguments; applying the global core identity termwise and using the public all-prime completed-period eigenlaw gives

`T̂_(p,s) core_s = λ_(p,s) core_s`.

At every upper resonance this reads

`T_(p,s) core_s + core_s(1)/(w−3) · (T_(p,s)P_w−λ_(p,s)P_w) = λ_(p,s)core_s`.

No boundary coefficient is supplied externally. The coefficient is recovered from the actual core, and `w−3≠0` on the stated strip.

## Limits

These identities do not establish boundedness on bare Haar space, where evaluation is unbounded, or intertwining of the full Mayer families under spectral reflection. They do not identify the PM Krein form with a positive metric. A common action on infinite mixed-parameter synthesis and independent arithmetic positivity remain open.

## Lean

`RenormalizedIntersectionTheory/MayerScattering/GlobalCoreHeckeCorrection`:

- `coreBoundaryDeterminant_ne_zero`
- `mayerCoreScatteringCoordinate_core`
- `mayerCoreZetaCoordinate_core`
- `mayerCorrectedHeckeT2_core`
- `mayerCorrectedHeckeOperator_core`
- `mayerPeriodCore_prime_hecke_rank_one`

Individual final `lake --old env lean` audit passed without warnings. All six declarations have only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. Umbrella import wired.
