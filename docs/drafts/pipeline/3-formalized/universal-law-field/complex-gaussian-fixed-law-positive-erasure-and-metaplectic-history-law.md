# Complex Gaussian fixed law, positive erasure, and metaplectic history law

- **ID:** ULF-ACTION-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** Candidate L finite action-principle test
- **Statement:** One rotating quadratic action has fixed critical law and fixed positive Hessian while its oriented thimble and Gaussian determinant require a double cover.
- **Status:** [PAPER-PROVED] [BRIDGE] [CLASSICAL PICARD--LEFSCHETZ/METAPLECTIC MECHANISM] [NOT FIELD CORE] [LEAN CERTIFIED]

## 1. Setup

For \(\theta\in\mathbb R\), define

\[
\mathcal S_\theta(z)=\frac12e^{i\theta}z^2,
\qquad z\in\mathbb C.
\tag{1}
\]

Let the oriented steepest-descent line \(L_\theta\) be parametrized by

\[
\iota_\theta:\mathbb R\longrightarrow\mathbb C,
\qquad
\iota_\theta(y)=e^{-i\theta/2}y,
\tag{2}
\]

with the orientation transported from increasing \(y\).

## 2. Theorem

For every \(\theta\):

1. \(\operatorname{Crit}(\mathcal S_\theta)=\{0\}\);
2. the complex Hessian is \(H_\theta=e^{i\theta}\), while its positive Gram shadow is
   \(H_\theta^*H_\theta=1\);
3. \(\mathcal S_\theta(\iota_\theta(y))=y^2/2\), so \(L_\theta\) is a convergent
   steepest-descent cycle;
4. the oriented Gaussian amplitude is

   \[
   Z(\theta)=\int_{L_\theta}e^{-\mathcal S_\theta(z)}\,dz
   =\sqrt{2\pi}\,e^{-i\theta/2};
   \tag{3}
   \]

5. the action, critical locus, positive Hessian, and unoriented line are \(2\pi\)-periodic, but

   \[
   Z(\theta+2\pi)=-Z(\theta),
   \qquad
   \iota_{\theta+2\pi}=-\iota_\theta;
   \tag{4}
   \]

6. the oriented determinant/thimble history closes only after \(4\pi\).

### Proof

Differentiating (1) gives \(d\mathcal S_\theta=e^{i\theta}z\,dz\), so the unique critical point is
zero and the Hessian is \(e^{i\theta}\). Its Hermitian square is one. Substituting (2) into (1)
gives

\[
\mathcal S_\theta(e^{-i\theta/2}y)
=\frac12e^{i\theta}e^{-i\theta}y^2
=\frac12y^2.
\]

Moreover \(dz=e^{-i\theta/2}dy\), hence

\[
Z(\theta)=e^{-i\theta/2}\int_{\mathbb R}e^{-y^2/2}\,dy
=\sqrt{2\pi}\,e^{-i\theta/2}.
\]

Replacing \(\theta\) by \(\theta+2\pi\) fixes \(e^{i\theta}\) but multiplies
\(e^{-i\theta/2}\) by \(-1\). Therefore the underlying line is fixed while its chosen orientation
and amplitude reverse. Repeating the loop twice restores both. QED.

## 3. Exact consequence

Neither the critical locus nor the positive Hessian shadow determines the oriented proof cycle or
Gaussian amplitude. The missing datum is not curvature: it is the square-root/determinant lift of a
loop in the space of nondegenerate quadratic laws.

Thus a complex action can genuinely produce several requested shadows from one formula. However,
this finite success is standard Picard--Lefschetz and metaplectic behavior. It validates an action
chart but does not establish a new universal field.

## 4. Hostile boundary

- The theorem does not produce hypertranscendence, arithmetic selection, completion, or a proof
  language.
- Replacing “proof” by “thimble” adds no mathematics unless a source canonically supplies the action.
- Derived critical loci and their shifted symplectic structures are established mathematics; the
  positive/phase split above is a classical Gaussian instance.
- Candidate L remains a possible local realization and is rejected as current universal ontology.

## 5. External parents

- Joyce, `A classical model for derived critical loci`, arXiv:1304.4508.
- Brav--Bussi--Joyce, `A Darboux theorem for derived schemes with shifted symplectic structure`,
  arXiv:1305.6302.
- Anel--Calaque, `Shifted symplectic reduction of derived critical loci`, arXiv:2106.06625.

## Log

- 2026-08-09 — finite action-principle gate closed; classified as bridge, not field core.

## Lean certification status (2026-08-09) — COMPLETE

Module: `GaloisForLFunctions.HTGeometry.ConstitutiveMetaplecticActionHistory`
(wired into `HTGeometry.UniversalLawField`).

`rotatingAction θ z = ½ e^{iθ} z²` is (1) and `descentLine θ y = e^{-iθ/2} y` is (2).

1. `rotatingAction_hasDerivAt` and `deriv_rotatingAction` give `dS_θ = e^{iθ} z`, and
   `crit_rotatingAction` proves `{z | deriv (S_θ) z = 0} = {0}` for every `θ`, using only
   `Complex.exp_ne_zero`.
2. `secondDeriv_rotatingAction` proves the second derivative is the constant `rotatingHessian θ
   = e^{iθ}`; `rotatingHessian_gram` proves `conj(H_θ) H_θ = 1` and `rotatingHessian_norm` gives
   `‖H_θ‖ = 1`.
3. `rotatingAction_descentLine` proves `S_θ(ι_θ(y)) = y²/2` exactly, as an identity in `ℂ` with the
   right-hand side a real number.
4. `descentLine_hasDerivAt` certifies `dz = e^{-iθ/2} dy`, so `thimbleAmplitude` really is the
   pullback line integral of `e^{-S}dz` along the oriented parametrization, not a definition chosen
   to make the answer come out.  `gaussian_integral_half` evaluates `∫ e^{-y²/2} = √(2π)` from
   mathlib's `integral_gaussian`, and `thimbleAmplitude_eq` is equation (3):
   `Z(θ) = √(2π) e^{-iθ/2}`.  `thimbleAmplitude_ne_zero` is used below.
5. `rotatingAction_periodic`, `crit_periodic`, `rotatingHessian_periodic` and
   `descentLine_range_add_two_pi` give the `2π`-periodicity of the action, the critical locus, the
   Hessian and the **unoriented** line; `descentLine_add_two_pi` and `thimbleAmplitude_add_two_pi`
   are equation (4): `ι_{θ+2π} = −ι_θ` and `Z(θ+2π) = −Z(θ)`.
6. `thimbleAmplitude_add_four_pi` closes the history at `4π` and
   `thimbleAmplitude_add_two_pi_ne` proves it does **not** close at `2π`, using the nonvanishing of
   the amplitude.

`positive_shadow_does_not_determine_orientation` bundles all eight statements: the positive Gram
shadow of the Hessian is literally the same before and after the loop while the oriented amplitude
has changed sign.

`#print axioms` on `crit_rotatingAction`, `secondDeriv_rotatingAction`, `rotatingHessian_gram`,
`rotatingAction_descentLine`, `descentLine_hasDerivAt`, `thimbleAmplitude_eq`,
`descentLine_range_add_two_pi`, `thimbleAmplitude_add_two_pi`, `thimbleAmplitude_add_four_pi`, and
`positive_shadow_does_not_determine_orientation` reports only `propext`, `Classical.choice`, and
`Quot.sound`.
