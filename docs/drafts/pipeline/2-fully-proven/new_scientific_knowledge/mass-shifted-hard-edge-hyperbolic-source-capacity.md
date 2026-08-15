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

For an even `psi in C_c^infty(I_sigma)`, write its Fourier transform as
`widehat psi(z)=K(z^2)`.  The Fourier transform of `L_kappa psi` is
`(z^2+kappa^2)K(z^2)`.  Therefore the **literal squared-variable form**, including its atom at
`u=-1/4`, gives directly

\[
 \begin{aligned}
 \mathfrak q_\sigma(\eta_r,L_\kappa\psi)
 &=\int_{\mathbb R}
   {F(u)\over u+\kappa^2}(u+\kappa^2)K(u)\,d\eta_\sigma(u)\\
 &=\mathfrak b_\sigma(F,K)=0.
 \end{aligned}                                             \tag{HSC.11}
\]

There is no hidden commutation assumption here.  At the polar atom, the same cancellation is
the ordinary scalar identity
`[F(-1/4)/(-1/4+kappa^2)](-1/4+kappa^2)=F(-1/4)`, with continuous
cancellation if `r=-1/4`.  Equation `(HSC.10)` is the time-domain version of the same multiplier
identity.

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

## 5. Square-root zero-edge capacity spike `[PAPER-PROVED]`

The singular dichotomy has a quantitative regularization that distinguishes the two branches
before `lambda` reaches zero.  Let `P_sigma` be the orthogonal projection onto `K_sigma`, put
`Q_sigma=1-P_sigma`, and for `tau>0` define

\[
 M_\tau(\kappa)
 :=\langle v_\kappa,(A_\sigma^++\tau)^{-1}v_\kappa\rangle,
 \qquad C_\tau(\kappa):=M_\tau(\kappa)^{-1}.              \tag{HSC.24}
\]

Equivalently, `C_tau(kappa)` is the minimum of
`mathfrak q_sigma(psi,psi)+tau||psi||_2^2` under the unit-source constraint.  Spectral
decomposition at zero gives the exact identity

\[
 M_\tau(\kappa)
 ={\|P_\sigma v_\kappa\|_2^2\over\tau}
 +\left\langle Q_\sigma v_\kappa,
   (A_\sigma^+|_{K_\sigma^\perp}+\tau)^{-1}
   Q_\sigma v_\kappa\right\rangle.                       \tag{HSC.25}
\]

Fix a simple negative root `r=-kappa_0^2`.

### Positive terminal mass

If `gamma_r>0`, then `P_sigma v_(kappa_0)=0`.  Put

\[
 c_r:=\|P_\sigma v'_{\kappa_0}\|_2^2.                    \tag{HSC.26}
\]

This coefficient is strictly positive.  Indeed, the hard-edge ground vector `xi` lies in
`K_sigma` and

\[
 \langle v_\kappa,\xi\rangle=F(-\kappa^2),
 \qquad
 \langle v'_{\kappa_0},\xi\rangle
 =-2\kappa_0F'(r)\ne0,                                   \tag{HSC.27}
\]

so

\[
 c_r\ge {4\kappa_0^2F'(r)^2\over\|\xi\|_2^2}>0.
\]

For every fixed real `s`, analyticity of `kappa mapsto v_kappa` in `L^2(I_sigma)`, `(HSC.19)`,
and `(HSC.25)` give the square-root profile

\[
 \boxed{\qquad
 \lim_{\tau\downarrow0}
 C_\tau(\kappa_0+s\sqrt\tau)
 ={1\over c_rs^2+\rho_r^{-1}}
 ={\rho_r\over1+\rho_rc_rs^2}.
 \qquad}                                                  \tag{HSC.28}
\]

The convergence is locally uniform in `s`.  To prove it, expand

\[
 P_\sigma v_{\kappa_0+s\sqrt\tau}
 =s\sqrt\tau\,P_\sigma v'_{\kappa_0}+O(\tau)
\]

locally uniformly in `s`.  The first term of `(HSC.25)` tends to `c_rs^2`; the second tends to
`<v_(kappa_0),S_sigma v_(kappa_0)>=rho_r^(-1)` because zero is isolated on
`K_sigma^perp`.

### Zero terminal mass

If `gamma_r=0`, then `zeta_r in K_sigma` and
`<v_(kappa_0),zeta_r>=1`, so `P_sigma v_(kappa_0) ne 0`.  Equation `(HSC.25)` instead yields

\[
 \boxed{\qquad
 {C_\tau(\kappa_0)\over\tau}
 \longrightarrow {1\over\|P_\sigma v_{\kappa_0}\|_2^2}.
 \qquad}                                                  \tag{HSC.29}
\]

Thus a nonzero positive-axis Padé atom is exactly an `O(1)` regularized capacity spike of width
`sqrt(tau)` and Lorentzian local profile.  The parity-radical branch has no such spike: its
regularized capacity is only `O(tau)` even at the root.  Any source-side proof of Padé-atom
vanishing must therefore rule out `(HSC.28)` uniformly; an unscaled integral or pointwise estimate
away from the root cannot see the obstruction.

## 6. Route-U consequence

Along the selected finite faces, the Gauss-node residue theorem gives

\[
 \rho_{j,i}\longrightarrow\rho_r
 =\operatorname{Cap}_\sigma(\sqrt{-r})                    \tag{HSC.30}
\]

at every simple negative limiting root.  Therefore the positive-axis Padé-measure target is
at a simple limiting root a hyperbolic-capacity collapse target.  A literal source theorem
excluding the finite nonzero alternative `(HSC.21)` forces `gamma_r=0` and hands that root to the
already explicit parity-doubled radical branch.  A simultaneous ground-simplicity theorem would
then exclude the root completely.  Proving vague vanishing of the whole finite pole measure still
requires a prelimit uniform version; `(HSC.30)` alone makes no claim about clusters converging to
multiple roots.

This is strictly sharper than asking for generic Padé convergence.  It names the exact
prime--Gamma observable whose finite value is the nonvanishing Padé atom.

## 7. Conjecture -> proof/failure -> pivot

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
6. **Conjecture:** ordinary zero-edge regularization blurs the two branches into the same limit.
   **FALSIFIED.** Positive terminal mass produces the square-root Lorentzian spike `(HSC.28)`;
   zero terminal mass produces the linear collapse `(HSC.29)`.  This is the exact boundary-layer
   observable a prelimit prime--Gamma estimate must exclude.

## 8. Higher universal principle

Four objects previously treated separately are one source-capacity invariant:

\[
 \text{hard terminal mass}
 \longleftrightarrow
 \text{positive-axis Pad\'e residue}
 \longleftrightarrow
 \text{unit hyperbolic source capacity}
 \longleftrightarrow
 \text{inverse zero-edge reduced susceptibility}
 \longleftrightarrow
 \text{square-root capacity spike}.                        \tag{HSC.31}
\]

The derivative/level obstruction is therefore a source-visibility obstruction.  A negative hard
root with positive terminal mass is exactly a hyperbolic source invisible to the whole ground
space but visible through the reduced resolvent.  Zero terminal mass reverses the visibility: the
source sees a new ground vector and the Padé atom collapses.

This identifies the missing mathematical primitive more narrowly than “global Xi information”:
it is zero-edge source visibility for the continuum of hyperbolic vectors `cosh(kappa t)` in the
literal finite-prime Gamma operator.

## 9. Literature, corpus, and Lean audit

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
- 2026-08-11 — derived the exact regularized zero-edge decomposition and proved the positive-mass
  Lorentzian `sqrt(tau)` spike versus zero-mass `O(tau)` collapse.

## Lean status (updated)

Section 3 — the exact capacity law — is formal and axiom-clean, in the generality the card uses: a
nonnegative symmetric form, a source functional, and a vector representing the form on that
functional.

    HTGeometry/NonnegFormRadical.lean                 (axiom-clean, wired, built)
      bilinForm_sq_le, form_pairing_eq_zero_of_diag   Cauchy-Schwarz and the radical of a
      formRadical                                     nonnegative symmetric bilinear form
      form_capacity                                   **(HSC.14)-(HSC.17)** a unit-source vector
                                                      representing the form has energy `rho`, and
                                                      no unit-source vector has smaller energy:
                                                      `Cap = rho`
      source_eq_zero_on_radical                       **(HSC.19) first half** a nonzero capacity
                                                      forces the source to annihilate the whole
                                                      radical, so it lies in the orthogonal
                                                      complement of the kernel
      mem_formRadical_of_capacity_eq_zero             **(HSC.22) first half** vanishing capacity
                                                      puts the normalized source vector in the
                                                      radical while keeping unit source, so the
                                                      ground projection of the source is nonzero
      eq_zero_of_form_diag_eq_zero,
        card_le_rank_ker_of_zero_energy               radical vectors are kernel vectors of any
                                                      operator representing the form

Still to formalize: section 2, the weak hyperbolic source equation (HSC.8)-(HSC.9), which needs the
distributional classification of even solutions of `-w'' + kappa² w = 0` on an interval; and
sections 4-5, the reduced-resolvent dichotomy (HSC.21)-(HSC.23) and the square-root capacity spike
(HSC.25)-(HSC.29), which need the spectral decomposition of the localized operator at zero.
