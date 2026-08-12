# Hyperbolic zero-edge capacity has an exact contact-order defect law

- **ID:** `mass-shifted-hyperbolic-capacity-contact-defect-law`
- **Stage:** 2-fully-proven / needs independent specialist audit
- **Route:** U, positive-axis hard Padé atoms
- **Type:** THEOREM + FRONTIER REDUCTION (paper)
- **Scientific status:** `[PAPER-PROVED] [CORPUS-NOVEL] [EXTERNAL NOVELTY UNVERIFIED] [LEAN GATED] [NOT RH]`
- **Depends on:** `mass-shifted-hard-edge-hyperbolic-source-capacity`
- **Statement:** Zero-edge capacity integrated over the hyperbolic source parameter detects every
  ground-invisible source contact.  A contact of order `m` contributes an explicit positive term
  of order `tau^(1/(2m))`; simple contacts converge after `sqrt(tau)` renormalization to a positive
  atomic defect measure whose mass is the Padé residue divided by hard-root transversality.

## 1. Goal and exact gain

The local Lorentzian profile `(HSC.28)` is pointwise on the moving scale
`kappa-kappa_0=O(sqrt(tau))`.  An ordinary pointwise estimate away from `kappa_0`, or an unscaled
integral, loses the spike.  This card globalizes the boundary layer and proves its exact integrated
mass.  More strongly, it classifies higher-order ground contacts and identifies one scalar source
target that excludes all of them:

\[
 \int \varphi(\kappa)C_\tau(\kappa)\,d\kappa=o(\sqrt\tau).
                                                               \tag{HCD.1}
\]

On any region where `varphi>0`, `(HCD.1)` is possible only when the hyperbolic source never becomes
orthogonal to the zero eigenspace.  This is a literal zero-edge response target, not a generic
Padé-convergence surrogate.

## 2. Isolated-zero setup

Let `H` be a real Hilbert space, let `A` be a nonnegative self-adjoint operator, and suppose zero is
an isolated spectral point.  Write

\[
 K=\ker A,\qquad P=P_K,\qquad Q=1-P,
 \qquad B=A|_{K^\perp},\qquad S=B^{-1}.                  \tag{HCD.2}
\]

Thus `B >= delta` on `K^perp` for some `delta>0`.  Let `J` be an open real interval and let
`kappa mapsto v_kappa in H` be real analytic, with `v_kappa ne 0`.  Assume `P v_kappa` is not
identically zero.  For `tau>0`, define

\[
 M_\tau(\kappa)=\langle v_\kappa,(A+\tau)^{-1}v_\kappa\rangle,
 \qquad C_\tau(\kappa)=M_\tau(\kappa)^{-1}.              \tag{HCD.3}
\]

The zero set

\[
 Z=\{\kappa\in J:P v_\kappa=0\}                         \tag{HCD.4}
\]

is discrete.  At `kappa_j in Z`, let `m_j` be the first positive integer for which
`P v^(m_j)_(kappa_j) ne 0`, and put

\[
 a_j={P v^{(m_j)}_{\kappa_j}\over m_j!},\qquad
 c_j=\|a_j\|^2,
 \qquad
 r_j=\langle v_{\kappa_j},S v_{\kappa_j}\rangle.        \tag{HCD.5}
\]

Here `S` is extended by zero on `K`.  Since `P v_(kappa_j)=0`, the vector `v_(kappa_j)` lies in
`K^perp`; hence `c_j>0` and `r_j>0`.

## 3. Contact-order defect theorem `[PROVED HERE]`

Let `phi in C_c(J)`.  Choose pairwise disjoint cutoff functions `chi_j` that equal one near the
finitely many points `kappa_j in Z intersect supp(phi)`.  Then

\[
 \boxed{\quad
 \lim_{\tau\downarrow0}\tau^{-1/(2m_j)}
 \int_J\chi_j(\kappa)\phi(\kappa)C_\tau(\kappa)\,d\kappa
 =K_{m_j}\phi(\kappa_j)c_j^{-1/(2m_j)}
       r_j^{\,1/(2m_j)-1},
 \quad}                                                   \tag{HCD.6}
\]

where

\[
 K_m={\pi\over m}\csc\!\left({\pi\over2m}\right).      \tag{HCD.7}
\]

On the complement of these neighborhoods,

\[
 \int \left(1-\sum_j\chi_j\right)\phi C_\tau\,d\kappa
 =O(\tau).                                                \tag{HCD.8}
\]

In particular, if every zero in `J` is simple, the positive Radon measures

\[
 \mu_\tau(d\kappa)=\tau^{-1/2}C_\tau(\kappa)\,d\kappa
\]

converge vaguely on `J` to

\[
 \boxed{\qquad
 \mu_\tau\ \Longrightarrow\
 \pi\sum_{\kappa_j\in Z}{1\over\sqrt{c_jr_j}}\,
       \delta_{\kappa_j}.
 \qquad}                                                  \tag{HCD.9}
\]

If a zero has order `m_j>1`, its mass under the simple-contact normalization instead satisfies

\[
 \tau^{-1/2}\int\chi_j C_\tau\,d\kappa
 \asymp \tau^{1/(2m_j)-1/2}\longrightarrow+\infty.       \tag{HCD.10}
\]

Thus failure of local boundedness of `mu_tau` records higher ground-contact order rather than an
analytic error.

### Proof

Spectral decomposition gives the exact identity

\[
 M_\tau(\kappa)
 ={\|P v_\kappa\|^2\over\tau}+R_\tau(\kappa),
 \qquad
 R_\tau(\kappa)
 =\langle Qv_\kappa,(B+\tau)^{-1}Qv_\kappa\rangle,       \tag{HCD.11}
\]

and therefore

\[
 C_\tau(\kappa)
 ={\tau\over \|P v_\kappa\|^2+\tau R_\tau(\kappa)}.    \tag{HCD.12}
\]

The gap `B>=delta` gives

\[
 \|(B+\tau)^{-1}-B^{-1}\|
 \le {\tau\over\delta(\delta+\tau)}.                   \tag{HCD.13}
\]

Hence `R_tau -> R_0` uniformly on compact `kappa`-sets.  At `kappa_j`,
`R_0(kappa_j)=r_j>0`.

Analyticity and the definition of `m_j` give, in `H`,

\[
 P v_{\kappa_j+h}=h^{m_j}a_j+O(|h|^{m_j+1}),
\]

so

\[
 \|P v_{\kappa_j+h}\|^2
 =c_jh^{2m_j}+O(|h|^{2m_j+1}).                           \tag{HCD.14}
\]

After shrinking a fixed neighborhood, there are constants `alpha_j,beta_j>0`, independent of
small `tau`, such that

\[
 \|P v_{\kappa_j+h}\|^2\ge\alpha_j|h|^{2m_j},
 \qquad R_\tau(\kappa_j+h)\ge\beta_j.                   \tag{HCD.15}
\]

Set `h=tau^(1/(2m_j))s` in the localized integral.  Equations `(HCD.12)` and `(HCD.14)` give
pointwise

\[
 {\tau\over
   \|P v_{\kappa_j+\tau^{1/(2m_j)}s}\|^2
      +\tau R_\tau(\kappa_j+\tau^{1/(2m_j)}s)}
 \longrightarrow {1\over c_js^{2m_j}+r_j}.              \tag{HCD.16}
\]

Equation `(HCD.15)` bounds the left side by
`1/(alpha_j|s|^(2m_j)+beta_j)`, an integrable function on the real line.  Dominated convergence
therefore proves `(HCD.6)`, because

\[
 \int_{-\infty}^{\infty}{ds\over c_js^{2m_j}+r_j}
 ={\pi\over m_j}\csc\!\left({\pi\over2m_j}\right)
   c_j^{-1/(2m_j)}r_j^{\,1/(2m_j)-1}.                   \tag{HCD.17}
\]

The last equality follows from scaling and Euler's integral
`integral_0^infty (1+t^(2m))^(-1) dt = pi/(2m)csc(pi/(2m))`.

Away from the finitely many zeros meeting `supp(phi)`, compactness gives
`||P v_kappa||^2>=epsilon>0`.  Equation `(HCD.12)` then gives `C_tau<=tau/epsilon`, proving
`(HCD.8)`.  Taking `m_j=1` yields `K_1=pi` and `(HCD.9)`.  Dividing `(HCD.6)` by `sqrt(tau)` proves
`(HCD.10)`.  This completes the proof.

## 4. Literal Route-U specialization `[PAPER-PROVED]`

Use the hard-edge operator and source from the parent card:

\[
 A=A_\sigma^+,
 \qquad v_\kappa(t)=\cosh(\kappa t),
 \qquad P=P_\sigma.                                      \tag{HCD.18}
\]

The source projection is not identically zero because the hard-edge ground vector `xi` satisfies

\[
 \langle v_\kappa,\xi\rangle=F(-\kappa^2),              \tag{HCD.19}
\]

and `F` is not identically zero.  Consequently the ground-invisible source set is discrete and
locally finite.

Let `r=-kappa_j^2` be a simple negative hard root.  If its terminal mass is positive, the parent
capacity theorem gives

\[
 P_\sigma v_{\kappa_j}=0,
 \qquad
 c_j=\|P_\sigma v'_{\kappa_j}\|^2>0,
 \qquad
 r_j=\rho_r^{-1}.                                        \tag{HCD.20}
\]

The strict derivative pairing `(HSC.27)` makes this a first-order source contact.  Its defect mass
is therefore

\[
 \boxed{\qquad
 \pi{1\over\sqrt{c_jr_j}}
 =\pi\sqrt{\rho_r\over c_j}.
 \qquad}                                                  \tag{HCD.21}
\]

If terminal mass is zero, `(HSC.29)` gives `P_sigma v_(kappa_j) ne 0`; there is no defect atom.
Thus, on every compact `kappa`-interval containing only simple negative hard roots,

\[
 \boxed{\qquad
 \tau^{-1/2}C_\tau(\kappa)\,d\kappa
 \Longrightarrow
 \pi\sum_{\substack{r=-\kappa_j^2\\ \gamma_r>0}}
       \sqrt{\rho_r\over c_j}\,\delta_{\kappa_j}.
 \qquad}                                                  \tag{HCD.22}
\]

This turns the whole surviving positive-axis Padé branch into one positive source-side defect
measure.  It loses neither a moving root nor a spike whose pointwise location is unknown.

## 5. Sharp extinction criterion

Let `U compactly contained in J`, and choose nonnegative `phi in C_c(J)` with `phi>0` on `U`.
If

\[
 \int_J\phi(\kappa)C_\tau(\kappa)\,d\kappa=o(\sqrt\tau), \tag{HCD.23}
\]

then

\[
 \boxed{\qquad P v_\kappa\ne0\quad\text{for every }\kappa\in U.\qquad} \tag{HCD.24}
\]

Indeed, a simple zero contradicts `(HCD.6)` with a positive finite `sqrt(tau)` coefficient; a zero
of order `m>1` contradicts it even more strongly because `tau^(1/(2m))/sqrt(tau) -> infinity`.
Conversely, if `P v_kappa ne 0` on `supp(phi)`, then `(HCD.8)` gives an `O(tau)` bound and hence
`(HCD.23)`.

For Route U, `(HCD.23)` is therefore the exact global source estimate needed to exclude every
positive-terminal-mass simple negative hard root in `U`.  It is strictly stronger than unscaled
vanishing, which holds even in the presence of a simple Lorentzian spike.

## 6. Conjecture -> proof/failure -> pivot

1. **Conjecture:** integrate `C_tau` without rescaling to expose a surviving Padé atom.
   **FAILED.** Every finite-order contact contribution tends to zero.
2. **Conjecture:** the square-root rescaling globalizes the local Lorentzian law.
   **PROVED for simple contacts** in `(HCD.9)` and specialized literally in `(HCD.22)`.
3. **Conjecture:** the same rescaled measures remain locally bounded at all contacts.
   **FALSIFIED.** An order-`m>1` contact has the different natural width `tau^(1/(2m))` and forces
   `(HCD.10)`.
4. **Pivot:** do not seek pointwise control at unknown moving roots.  Prove the integrated literal
   prime--Gamma response estimate `(HCD.23)`.  Positivity prevents cancellation, and the threshold
   is sharp for every contact order.

## 7. Higher universal principle

The obstruction is a positive defect measure created when a continuum of source vectors crosses
the invisible subspace of the zero eigenspace.  Regularization turns contact order into geometric
width:

\[
 \text{order }m
 \longleftrightarrow
 \text{width }\tau^{1/(2m)}
 \longleftrightarrow
 \text{integrated capacity }K_m c^{-1/(2m)}r^{1/(2m)-1}\tau^{1/(2m)}.
                                                               \tag{HCD.25}
\]

The repeated failure of pointwise, unscaled, and fixed-degree reporters is one phenomenon: they
discard concentration on a moving zero set.  Source capacity must be treated as a concentrating
positive measure.  At simple Route-U roots, its atom weight factors exactly into Padé mass
`rho_r` and transverse ground visibility `c_r`.

## 8. Corpus, literature, and Lean audit

- **Corpus collision audit.** Searches for rescaled capacity measures, Lorentzian defect measures,
  and contact-order capacity laws found the local profile `(HSC.28)` but no integrated limit,
  higher-contact classification, or criterion `(HCD.23)`.
- **Nearby literature.** Lasserre, *A modified Christoffel function and its asymptotic properties*
  (arXiv:2301.11072), studies density asymptotics of a different modified Christoffel function.
  Pauwels--Bach--Vert, *Relating Leverage Scores and Density using Regularized Christoffel
  Functions* (arXiv:1805.07943), studies kernel leverage and population density.  Neither located
  source states a zero-eigenspace contact-order atomic limit of the form `(HCD.6)--(HCD.10)`.
- **Novelty status.** Abstract boundary-layer methods are classical and no external priority is
  claimed.  Candidate-new content is the exact contact-order law, sharp `o(sqrt(tau))` threshold,
  and literal factorization `(HCD.21)` for Route-U hard Padé mass.
- **Lean status.** No Lean wrapper is created.  Under the project's unconditional-proof rule, an
  abstract theorem parameterized by `A`, `v`, and spectral assumptions would be theorem
  laundering.  Literal formalization requires the already-gated hard-edge operator, its isolated
  zero decomposition, analytic hyperbolic source family, and the parent capacity identification.
  This card changes the literal source target; it does not pretend to close that missing source
  theorem.

## 9. Log

- 2026-08-12 — local Lorentzian conjecture globalized; higher-contact scaling discovered and
  proved; exact Route-U defect mass and sharp integrated extinction criterion recorded.
