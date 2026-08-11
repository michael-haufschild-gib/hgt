# Hard-edge Padé residue is hyperbolic restricted-Weil source capacity

- **ID:** `mass-shifted-hard-edge-hyperbolic-source-capacity`
- **Stage:** 2-fully-proven / needs independent specialist audit
- **Route:** U, positive-axis hard Padé atoms
- **Type:** THEOREM + FRONTIER REDUCTION (paper)
- **Scientific status:** `[PAPER-PROVED] [CORPUS-NOVEL] [EXTERNAL NOVELTY UNVERIFIED] [LEAN NOT STARTED]`
- **Depends on:** `mass-shifted-hard-edge-hyperbolic-weil-boundary`,
  `mass-shifted-hard-edge-root-jet-radical-rigidity`, and
  `mass-shifted-hard-edge-gauss-node-jet-residue-law`
- **Statement:** At a simple negative hard root `r=-kappa^2`, the limiting positive-axis Padé
  residue is exactly the minimum restricted-Weil energy needed to synthesize unit hyperbolic
  source `cosh(kappa t)`. Positive terminal mass is equivalent to a finite nonzero zero-edge
  reduced resolvent response; zero terminal mass is equivalent to a source-visible ground pole.

## 1. Setup

Let

\[
 f(z)=F(z^2)\in PW_\sigma
\]

be the nonzero hard-edge state supplied by the literal completed-Xi compactification.  Let
`I_sigma=(-sigma,sigma)` and use the Fourier convention

\[
 \widehat\eta(z)=\int_{I_\sigma}\eta(t)e^{izt}\,dt.
\]

The closed even restricted-Weil form from the hard-edge theorem is

\[
 \mathfrak q_\sigma(\eta,\psi)
 :=\mathfrak b_\sigma(\widehat\eta,\widehat\psi),             \tag{HSC.1}
\]

where `mathfrak b_sigma` is the literal finite-prime Gamma form, including polar evaluation.
It is nonnegative on the closed critical even domain.  Write `A_sigma^+` for its associated
self-adjoint even operator.  If `xi` is the inverse Fourier transform of `f`, then

\[
 \xi\in\ker A_\sigma^+,
 \qquad
 \mathfrak q_\sigma(\xi,\psi)=0                            \tag{HSC.2}
\]

for every form-domain vector `psi`.

Fix a simple negative root

\[
 r=-\kappa^2<0,
 \qquad F(r)=0,
 \qquad F'(r)\ne0,                                        \tag{HSC.3}
\]

and define its continuously cancelled descendant

\[
 h_r(z)={f(z)\over z^2+\kappa^2},
 \qquad
 \eta_r=\mathcal F^{-1}h_r.                               \tag{HSC.4}
\]

The root-jet law gives its terminal energy

\[
 \gamma_r
 =\mathfrak q_\sigma(\eta_r,\eta_r)\ge0.                 \tag{HSC.5}
\]

The Padé-residue theorem gives the limiting atom

\[
 \rho_r={\gamma_r\over F'(r)^2}.                           \tag{HSC.6}
\]

The new point is that `(HSC.6)` has an exact literal source meaning.

## 2. Weak hyperbolic source equation `[PAPER-PROVED]`

Put

\[
 L_\kappa=-\partial_t^2+\kappa^2,
 \qquad v_\kappa(t)=\cosh(\kappa t).                       \tag{HSC.7}
\]

Then

\[
 \boxed{\quad
 \mathfrak q_\sigma(\eta_r,\psi)
 ={\gamma_r\over F'(r)}
   \langle v_\kappa,\psi\rangle_{L^2(I_\sigma)}
 \quad}                                                     \tag{HSC.8}
\]

for every even vector `psi` in the closed critical form domain.  Equivalently, in the weak
operator sense,

\[
 A_\sigma^+\eta_r={\gamma_r\over F'(r)}v_\kappa.           \tag{HSC.9}
\]

### Proof

Because `h_r in PW_sigma`, division by `z^2+kappa^2` preserves Fourier support.  Moreover

\[
 z^2h_r(z)=f(z)-\kappa^2h_r(z)\in L^2(\mathbb R).
\]

Thus `eta_r in H^2(R)` after zero extension.  Compact support then forces both endpoint traces
of `eta_r` and its first derivative to vanish, so no boundary distribution appears and

\[
 L_\kappa\eta_r=\xi.                                      \tag{HSC.10}
\]

For an even `psi in C_c^infty(I_sigma)`, convolution of the restricted-Weil distribution
commutes with the constant-coefficient operator `L_kappa`.  Hence `(HSC.2)` and `(HSC.10)` give

\[
 \mathfrak q_\sigma(\eta_r,L_\kappa\psi)
 =\mathfrak q_\sigma(L_\kappa\eta_r,\psi)
 =\mathfrak q_\sigma(\xi,\psi)=0.                         \tag{HSC.11}
\]

Define the even distribution `w_r` on `I_sigma` by

\[
 w_r(\psi)=\mathfrak q_\sigma(\eta_r,\psi).
\]

Equation `(HSC.11)` says `L_kappa w_r=0`.  Every even distributional solution of this ODE on an
interval is a scalar multiple of `cosh(kappa t)`.  Therefore

\[
 \mathfrak q_\sigma(\eta_r,\psi)
 =c_r\langle v_\kappa,\psi\rangle                         \tag{HSC.12}
\]

on the smooth core.  Closed-form density and `v_kappa in L^2(I_sigma)` extend `(HSC.12)` to the
whole form domain.

The cancelled value at the imaginary root is

\[
 \langle v_\kappa,\eta_r\rangle
 =h_r(i\kappa)
 ={f'(i\kappa)\over2i\kappa}
 =F'(-\kappa^2)=F'(r).                                    \tag{HSC.13}
\]

Putting `psi=eta_r` in `(HSC.12)` and using `(HSC.5)` proves
`c_r=gamma_r/F'(r)`, hence `(HSC.8)`.

## 3. Exact capacity law `[PAPER-PROVED]`

Normalize

\[
 \zeta_r={\eta_r\over F'(r)}.
\]

Then `(HSC.6)`, `(HSC.8)`, and `(HSC.13)` become

\[
 \langle v_\kappa,\zeta_r\rangle=1,
 \qquad
 \mathfrak q_\sigma(\zeta_r,\psi)
 =\rho_r\langle v_\kappa,\psi\rangle.                    \tag{HSC.14}
\]

Define the hyperbolic source capacity

\[
 \operatorname{Cap}_\sigma(\kappa)
 :=\inf\left\{
 \mathfrak q_\sigma(\psi,\psi):
 \psi\in\mathcal D(\mathfrak q_\sigma)^+,
 \ \langle v_\kappa,\psi\rangle=1
 \right\}.                                                \tag{HSC.15}
\]

Then

\[
 \boxed{\qquad
 \operatorname{Cap}_\sigma(\kappa)
 =\rho_r
 ={\gamma_r\over F'(r)^2}.
 \qquad}                                                   \tag{HSC.16}
\]

Indeed, `zeta_r` is admissible.  For any other admissible `psi`, put `d=psi-zeta_r`.  Then
`<v_kappa,d>=0`, so `(HSC.14)` and nonnegativity of the closed even form give

\[
 \mathfrak q_\sigma(\psi,\psi)
 =\rho_r+\mathfrak q_\sigma(d,d)\ge\rho_r.                \tag{HSC.17}
\]

Thus the hard Padé residue is not merely analogous to a source norm.  It is the exact minimum
literal prime--Gamma energy of a unit hyperbolic source synthesis problem.

## 4. Reduced-resolvent dichotomy `[PAPER-PROVED]`

The localized operator has discrete spectrum and finite-dimensional kernel.  Let

\[
 K_\sigma=\ker A_\sigma^+,
 \qquad
 S_\sigma=(A_\sigma^+|_{K_\sigma^\perp})^{-1}.             \tag{HSC.18}
\]

If `gamma_r>0`, then `(HSC.14)` applied to every `k in K_sigma` gives

\[
 \langle v_\kappa,k\rangle=0.
\]

Consequently `v_kappa in K_sigma^perp`, and projection of `(HSC.14)` to that complement yields

\[
 \boxed{\qquad
 \rho_r^{-1}
 =\langle v_\kappa,S_\sigma v_\kappa\rangle.
 \qquad}                                                   \tag{HSC.19}
\]

Equivalently, for `lambda<0`, define the literal even source response

\[
 M_\kappa(\lambda)
 =\langle v_\kappa,(A_\sigma^+-\lambda)^{-1}v_\kappa\rangle.
                                                                    \tag{HSC.20}
\]

Then

\[
 \gamma_r>0
 \quad\Longrightarrow\quad
 \lim_{\lambda\uparrow0}M_\kappa(\lambda)=\rho_r^{-1}<\infty.
                                                                    \tag{HSC.21}
\]

If `gamma_r=0`, then `zeta_r in K_sigma` while
`<v_kappa,zeta_r>=1`.  Hence the ground projection of `v_kappa` is nonzero and

\[
 \gamma_r=0
 \quad\Longrightarrow\quad
 \lim_{\lambda\uparrow0}M_\kappa(\lambda)=+\infty.        \tag{HSC.22}
\]

Thus the two Route-U branches are the two possible zero-edge impedances of one literal source:

\[
 \begin{array}{c|c|c}
 \text{terminal mass} & \text{hyperbolic response at }0 & \text{Pad\'e atom}\\ \hline
 \gamma_r>0 & \text{finite, with value }1/\rho_r & \rho_r>0\\
 \gamma_r=0 & \text{ground pole} & \rho_r=0.
 \end{array}                                               \tag{HSC.23}
\]

## 5. Route-U consequence

Along the selected finite faces, the Gauss-node residue theorem gives

\[
 \rho_{j,i}\longrightarrow\rho_r
 =\operatorname{Cap}_\sigma(\sqrt{-r})                    \tag{HSC.24}
\]

at every simple negative limiting root.  Therefore the positive-axis Padé-measure target is
at a simple limiting root a hyperbolic-capacity collapse target.  A literal source theorem
excluding the finite nonzero alternative `(HSC.21)` forces `gamma_r=0` and hands that root to the
already explicit parity-doubled radical branch.  A simultaneous ground-simplicity theorem would
then exclude the root completely.  Proving vague vanishing of the whole finite pole measure still
requires a prelimit uniform version; `(HSC.24)` alone makes no claim about clusters converging to
multiple roots.

This is strictly sharper than asking for generic Padé convergence.  It names the exact
prime--Gamma observable whose finite value is the nonvanishing Padé atom.

## 6. Conjecture -> proof/failure -> pivot

1. **Conjecture:** analyticity of the completed-Xi resolvent excludes the positive Padé pole.
   **FAILED.** Moving-order Padé approximation need not be locally bounded.
2. **Conjecture:** exact center evolution of Gauss nodes supplies the missing anchor.
   **FAILED AS A CLOSURE.** Center flow depends only on the shifted-moment ODE and positive finite
   quadrature; it controls pole velocity, not the literal source value.
3. **Conjecture:** the surviving residue is the capacity of the hyperbolic source created by
   cancelled root division. **PROVED** in `(HSC.8)--(HSC.16)`.
4. **Conjecture:** nonnegative even form alone forces this capacity to vanish. **FALSIFIED.** A
   positive semidefinite operator can have a source orthogonal to its kernel and strictly positive
   capacity.  The finite/nonzero branch `(HSC.21)` is genuine.
5. **Pivot:** attack the literal prime--Gamma zero-edge response `(HSC.20)`.  Prove that its finite
   part cannot stay nonzero on a selected negative-root branch, or prove that any resulting ground
   pole contradicts source-derived ground multiplicity.  Generic moment, Padé, or abstract
   semidefinite arguments cannot decide this response.

## 7. Higher universal principle

Four objects previously treated separately are one source-capacity invariant:

\[
 \text{hard terminal mass}
 \longleftrightarrow
 \text{positive-axis Pad\'e residue}
 \longleftrightarrow
 \text{unit hyperbolic source capacity}
 \longleftrightarrow
 \text{inverse zero-edge reduced susceptibility}.          \tag{HSC.26}
\]

The derivative/level obstruction is therefore a source-visibility obstruction.  A negative hard
root with positive terminal mass is exactly a hyperbolic source invisible to the whole ground
space but visible through the reduced resolvent.  Zero terminal mass reverses the visibility: the
source sees a new ground vector and the Padé atom collapses.

This identifies the missing mathematical primitive more narrowly than “global Xi information”:
it is zero-edge source visibility for the continuum of hyperbolic vectors `cosh(kappa t)` in the
literal finite-prime Gamma operator.

## 8. Literature, corpus, and Lean audit

- `[LOCAL-RESEARCH]` The hard-edge root-jet card proves terminal energy `gamma_r`; the Padé card
  proves `rho_r=gamma_r/F'(r)^2`.  Neither identifies this scalar with a literal source capacity
  or reduced resolvent.
- `[LOCAL-RESEARCH]` Suzuki cards use ground projections and reduced resolvents for the fixed
  completion sources.  They do not identify Route U's moving hyperbolic root source with the hard
  Padé atom.
- `[LITERATURE]` Riesz representers, reduced resolvents, de Branges reproducing kernels, and Clark
  norming constants are classical parents.  Connes--van Suijlekom and Suzuki supply the localized
  convolution-operator setting.  No located source states `(HSC.8)`, `(HSC.16)`, or `(HSC.19)` for
  the completed-Xi hard-edge Padé residue.

External priority remains unverified pending specialist review.  The abstract capacity argument
is not claimed new; candidate-new content is its literal prime--Gamma identification and the exact
Route-U/Suzuki bridge.

No Lean declaration is claimed.  Formalizing an abstract positive form with a supplied radical
vector would repeat theorem laundering.  Exact formalization requires the literal hard-edge
Paley--Wiener limit, completed finite-prime Gamma form, associated localized operator, and cancelled
root-division domain.  Lean work remains gated on a source theorem that closes `(HSC.21)` or its
ground-pole alternative.

## Log

- 2026-08-11 — derived the weak hyperbolic source equation, exact source-capacity identity, and
  finite-response/ground-pole dichotomy for Route U's limiting positive-axis Padé atom.
