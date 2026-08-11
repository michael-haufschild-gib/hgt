# Mass-shifted arcsine null-admission adaptive-source margin

- **ID:** mass-shifted-arcsine-null-adaptive-source-margin
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3, successor to canonical degree-one admitted-source recession
- **Statement:** Every fixed-degree monic arcsine null admission has a strictly positive exact adaptive-source recession margin, but those margins decay exponentially with degree.

## Goal

Classify higher-degree canonical admission at the arcsine recession face. Determine whether the
source law loses sign or only uniform coercivity when degree escapes.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack proof complete
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready

## Paper proof `[PROVED HERE]`

Let `c_k = centralBinom(2k,k)/4^k` and let `L_c` be its moment functional. Under the normalized
arcsine coordinate

\[
 x=\frac{1+\cos\phi}{2},\qquad d\mu_c=\frac{d\phi}{\pi},
\]

the monic degree-`n` orthogonal polynomial is

\[
 p_n(x)=\alpha_n T_n(2x-1),\qquad \alpha_n=2^{1-2n},\qquad n\ge1.
\]

The adaptive shear polynomial is

\[
 Q(p)=(Xp)\,X(Xp'+p)=x^2p^2+x^3pp'.
\]

Writing `t=cos φ`, the normalized margin `S_n=L_c(Q(p_n))` becomes

\[
 \frac{S_n}{\alpha_n^2}
 =\frac14\,\mathbb E[(1+t)^2T_n(t)^2]
  +\frac n4\,\mathbb E[(1+t)^3T_n(t)U_{n-1}(t)].
\]

For the square term, `2T_n^2=T_{2n}+1` and

\[
 (1+t)^2=\frac32T_0+2T_1+\frac12T_2.
\]

Chebyshev orthogonality therefore gives `7/32` when `n=1` and `3/16` when `n≥2`.

For the derivative term, `2T_nU_{n-1}=U_{2n-1}` and

\[
 (1+t)^3=\frac52T_0+\frac{15}{4}T_1+\frac32T_2+\frac14T_3,
\]

while

\[
 U_{2n-1}=2(T_1+T_3+\cdots+T_{2n-1}).
\]

Only `T₁` contributes for `n=1`; `T₁,T₃` contribute for every `n≥2`. Hence derivative term is
`15/32` for `n=1` and `n/2` for `n≥2`. Adding terms yields

\[
 S_1=\alpha_1^2\frac{11}{16}=\frac{11}{64},
 \qquad
 S_n=\alpha_n^2\frac{8n+3}{16}
      =2^{2-4n}\frac{8n+3}{16}>0\quad(n\ge2).
\]

Because `α_n²=2^{2-4n}`, these positive margins tend to zero with degree. Thus fixed-degree
canonical admission does not lose source sign. It loses a degree-uniform lower bound.

## Significance

This separates two phenomena previously conflated as “nonproper admission.” Coefficient motion at
fixed degree can enter negative source chambers, but canonical Hankel admission selects the positive
arcsine chamber. Degree escape still defeats compactness because monic normalization makes the exact
positive margin exponentially small. Remaining route burden is quantitative tracking of actual Xi
null admissions against this collapsing margin, not construction of another orientation map.

## Lean certificate

`formal/GaloisForLFunctions/RHTower/XiShiftedAdaptiveArithmeticSourceArcsineAdmissionMargin.lean`

Capstones:

- arcsine/`measureT` affine transport of the moment functional;
- monicity and degree of shifted Chebyshev admission;
- exact `n=1` and `n≥2` adaptive margins;
- strict positivity and non-uniform decay.

Exact declarations in namespace `RHTower.XiShiftedArcsineAdmission`:

- `bridge`
- `amplitude_monic`
- `momentFunctional_adaptiveShear_amplitude_one`
- `momentFunctional_adaptiveShear_amplitude_of_two_le`
- `momentFunctional_adaptiveShear_amplitude_pos`
- `tendsto_margin_zero`
- `no_uniform_positive_margin`

Direct `lake env lean` check: PASS, warning-free. Target-module build: PASS. Umbrella import:
`formal/GaloisForLFunctions/RHTower.lean`. Axiom audit: only `propext`, `Classical.choice`, and
`Quot.sound`.

## Log

- 2026-08-11 — paper proof completed; moved directly to in-progress formalization.
- 2026-08-11 — exact affine transport, monicity, margins, positivity, exponential collapse, and
  no-uniform-margin survivor formalized unconditionally.
