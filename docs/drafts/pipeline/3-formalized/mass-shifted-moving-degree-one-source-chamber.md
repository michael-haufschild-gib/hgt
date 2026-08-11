# Mass-shifted moving degree-one arithmetic-source chamber

- **ID:** mass-shifted-moving-degree-one-source-chamber
- **Stage:** 3-formalized
- **Type:** FALSIFIED + THEOREM (Lean)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3, successor to Conjecture 60
- **Statement:** Fixed degree does not give a uniform source-positivity horizon; scaled monic degree-one amplitudes have an exact quadratic far-right sign chamber.

## Goal

Test whether fixed-admission positivity can be upgraded uniformly over bounded polynomial degree.
Extract exact admission constraint that survives when this fails.

## Gates

- [x] 0 → 1 in-progress: explicit source-pure moving family
- [x] 1 → 2 fully-proven: complete paper proof below, `[PROVED HERE]`
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready

## Paper proof `[PROVED HERE]`

For fixed `R ∈ ℝ`, define the moving monic amplitude

\[
 A_{R,w}(X)=X-R/w^2.
\]

One shifted Euler step gives `E₁A=2X-R/w²`, hence the adaptive polynomial is

\[
 Q_{R,w}=(XA_{R,w})(XE_1A_{R,w})
 =2X^4-3(R/w^2)X^3+(R/w^2)^2X^2.                 \tag{1}
\]

The literal completed arithmetic source equals twice its shifted-Xi moment functional. Therefore

\[
 \mathcal S(w,A_{R,w})
 =4m_4(w^2)-6(R/w^2)m_3(w^2)+2(R/w^2)^2m_2(w^2). \tag{2}
\]

Apply the unconditional normalized moment limits
`2w^(2k+1)m_k(w²)/log w → c_k`, where `c₂=3/8`, `c₃=5/16`, and `c₄=35/128`.
Finite linearity in (2) yields

\[
 \frac{w^9}{\log w}\mathcal S(w,A_{R,w})
 \longrightarrow R^2c_2-3Rc_3+2c_4
 =\frac{24R^2-60R+35}{64}.                         \tag{3}
\]

At `R=5/4`, the limit is `-5/128`. Since `w^9/log w>0` eventually,
`S(w,A_(5/4,w))<0` eventually. Every amplitude in this family is monic of degree one, while the
fixed-amplitude theorem proves eventual positivity for each amplitude after freezing `w`.
Therefore no positivity horizon can be uniform over monic degree-one amplitudes. No numerical
computation, RH assumption, or infinite-dimensional limit is used.

## No-go closure

- **Exact killing theorem/mechanism:** coefficient conditioning `R/w²` tracks the anisotropic mass
  dilation and keeps all degrees `2,3,4` at the same asymptotic order. Resulting limit quadratic is
  negative at `R=5/4`.
- **Strongest positive survivor:** exact sign chamber `(24R²-60R+35)/64`; actual admission must
  control scaled root `R=w²r`, not merely degree or monicity.
- **New insight:** nonproperness already occurs inside degree-one monic stratum. Degree escape is
  not necessary; coefficient conditioning alone defeats fixed-amplitude recession.
- **Status:** dependency-closed and formalized in
  `XiShiftedAdaptiveArithmeticSourceMovingDegreeOneChamber`.

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/XiShiftedAdaptiveArithmeticSourceMovingDegreeOneChamber.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Capstones:
  - `tendsto_scaled_xiShiftedAdaptiveDegreeOneArithmeticSource`
  - `xiShiftedAdaptiveMovingDegreeOneArithmeticSource_eventually_neg`
- Direct check: PASS, warning-free.
- Target build: PASS.
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.

## Exact successor

For canonical degree-one null admission `r=m₁/m₀`, prove its scaled root `w²r` stays in positive
chamber globally (far-right limit is `1/2`). For higher null flags, identify corresponding scaled
arcsine orthogonal polynomial and sign adaptive limit on that admitted locus.
