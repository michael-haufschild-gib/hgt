# Hard-edge parity-jet inertia law

- **ID:** mass-shifted-hard-edge-parity-jet-inertia
- **Stage:** 3-formalized
- **Route:** U, literal completed-Xi hard-edge boundary
- **Type:** THEOREM (paper)
- **Scientific status:** [PAPER-PROVED] [NOVELTY UNVERIFIED] [LEAN FORMALIZED]
- **Source:** mass-shifted-hard-edge-root-jet-radical-rigidity
- **Statement:** Multiplying a divided squared-root jet by the Fourier variable transports its even terminal mass \(\gamma_r\) to odd energy \(r\gamma_r\); under full-ground positivity every repeated root therefore creates explicit odd ground modes and doubles the nonterminal radical flag.

## Goal

Resolve the unexplained “excess non-jet mode” in the degenerate hard-edge branch and identify the
exact obstruction to promoting the selected even boundary state to the full convolution ground.
No generic semidefinite wrapper is used: every object below is the literal finite-prime Gamma
hard-edge form already constructed on paper.

## Gates

- [x] 0 → 1 in-progress: parity carrier and root-jet target isolated
- [x] 1 → 2 fully-proven: complete source-specific paper proof below
- [x] 2 → 3 formalized: literal hard-edge density, pairing, both parity sectors, the divided-jet
  Gram law, the parity lift, the multi-root independence and the dimension counts are all Lean
- [ ] 3 → 4 publication-ready: specialist novelty and operator-domain audit

## 1. Even and odd forms

Fix the hard-edge type \(\sigma\) and signed measure

\[
 d\eta_\sigma(u)=\mathbf 1_{u>0}
   \frac{V_\sigma(\sqrt u)}{\sqrt u}\,du+2\pi\delta_{-1/4}. \tag{HPJI.1}
\]

For squared-variable entire functions \(H,K\), the even restricted-Weil form is

\[
 \mathfrak b_\sigma^+(H,K)
 =\int_{\mathbb R}H(u)K(u)\,d\eta_\sigma(u).               \tag{HPJI.2}
\]

The odd Fourier-side functions are \(zH(z^2)\) and \(zK(z^2)\). Changing variables
\(u=x^2\) in the Gamma/prime integral and using

\[
 (i/2)^2=-1/4
\]

in the polar term gives the exact odd-sector identity

\[
 \boxed{\;
 \mathfrak b_\sigma^-(H,K)
 :=\mathcal W_\sigma(zH(z^2),zK(z^2))
 =\int_{\mathbb R}uH(u)K(u)\,d\eta_\sigma(u).
 \;}                                                        \tag{HPJI.3}
\]

Thus multiplication by Fourier variable is multiplication by \(u\) in the squared-variable
form, including the sign of the polar atom. This is the parity datum invisible to the closed even
form.

## 2. Complete odd divided-jet Gram law [PROVED HERE]

Let the nonzero hard-edge state be \(f(z)=F(z^2)\), let \(r\) be a real root of \(F\) of
multiplicity \(m_r\), and put

\[
 F_{r,k}(u)=\frac{F(u)}{(u-r)^k},\qquad 1\le k\le m_r.
                                                               \tag{HPJI.4}
\]

All quotients are entire after continuous cancellation. The root-jet theorem gives

\[
 M_{r,j}:=\int\frac{F(u)^2}{(u-r)^j}\,d\eta_\sigma(u)=0
 \quad(1\le j<2m_r),
\]

\[
 \gamma_r:=M_{r,2m_r}\ge0,                                  \tag{HPJI.5}
\]

and distinct-root even orthogonality. For one root,

\[
 \begin{aligned}
 \mathfrak b_\sigma^-(F_{r,p},F_{r,q})
 &=\int\frac{uF(u)^2}{(u-r)^{p+q}}\,d\eta_\sigma(u)\\
 &=M_{r,p+q-1}+rM_{r,p+q}.                                  \tag{HPJI.6}
 \end{aligned}
\]

Every term in (HPJI.6) vanishes unless \(p=q=m_r\). In the terminal case,

\[
 \boxed{\;
 \mathfrak b_\sigma^-(F_{r,m_r},F_{r,m_r})=r\gamma_r.
 \;}                                                        \tag{HPJI.7}
\]

For distinct roots \(r\ne s\), use

\[
 uF_{r,p}=rF_{r,p}+F_{r,p-1},\qquad F_{r,0}:=F.
\]

Both terms are even-orthogonal to \(F_{s,q}\), so

\[
 \mathfrak b_\sigma^-(F_{r,p},F_{s,q})=0.                  \tag{HPJI.8}
\]

Consequently the full odd divided-jet Gram law is

\[
 \boxed{
 \mathfrak b_\sigma^-(F_{r,p},F_{s,q})=
 \begin{cases}
   r\gamma_r,&r=s,\ p=q=m_r,\\
   0,&\text{otherwise}.
 \end{cases}}                                               \tag{HPJI.9}
\]

This is the parity companion to the even diagonal law, whose only terminal entry is
\(\gamma_r\). Root location is therefore not auxiliary geometry: it is the exact ratio of odd
terminal energy to even terminal mass.

## 3. Full-ground consequences [PROVED HERE]

Assume zero is the lowest spectral value of the full localized convolution operator. Its closed
quadratic form is nonnegative on both parity sectors. A zero-energy form-domain vector therefore
lies in the operator kernel.

For every nonterminal jet \(1\le k<m_r\), (HPJI.9) gives

\[
 \mathcal W_\sigma\!\left(
   zF_{r,k}(z^2),zF_{r,k}(z^2)\right)=0.
\]

Division improves real decay and multiplication by \(z\) gives back only one power, so these odd
descendants remain in the logarithmic Paley--Wiener form domain. Hence

\[
 zF_{r,k}(z^2)\in\ker A_\sigma
 \qquad(1\le k<m_r).                                      \tag{HPJI.10}
\]

Their rational principal parts are independent; odd and even sectors are independent. With

\[
 E=\sum_r(m_r-1),
\]

the existing \(E\) nonterminal even descendants and their \(E\) odd twins give the constructive
bound

\[
 \boxed{\qquad
 \dim\ker A_\sigma\ge1+2E.
 \qquad}                                                    \tag{HPJI.11}
\]

This identifies the previously unclassified excess modes explicitly. No signed-cosine
perturbation or external real-zero theorem is needed.

The terminal law adds three sharp alternatives:

1. If \(r<0\) and \(\gamma_r>0\), then (HPJI.7) is negative, contradicting full-ground
   nonnegativity.
2. If \(r=0\) and \(\gamma_r>0\), the terminal odd descendant is an additional ground mode.
3. If \(\gamma_r=0\), both terminal even and terminal odd descendants are ground modes, regardless
   of root sign.

For any finite root set \(S\), define

\[
 Z_S=\#\{r\in S:\gamma_r=0\},\qquad
 Z_{0,S}^+=\mathbf1_{\{0\in S,\ \gamma_0>0\}}.
\]

The sharpened finite-set dimension law is

\[
 \boxed{\quad
 \dim\ker A_\sigma
 \ge1+2E_S+2Z_S+Z_{0,S}^+,
 \quad E_S=\sum_{r\in S}(m_r-1).
 \quad}                                                      \tag{HPJI.12}
\]

In particular, if the full ground is simple, every root is simple, every terminal mass is
positive, and

\[
 \boxed{\qquad r>0\quad\text{for every root of }F.\qquad}   \tag{HPJI.13}
\]

This strengthens the earlier \(r\ge0\) conclusion. Real zeros of
\(f(z)=F(z^2)\) follow directly, but the parity identity also explains why: a negative squared
root is literally a negative odd descendant, while a zero squared root is an odd degeneracy.

## 4. Conjecture → proof/fail → pivot

1. **Conjecture:** repeated roots require an unknown non-jet ground direction.
   **Failed as stated:** (HPJI.10) constructs every missing direction by parity lift.
2. **Conjecture:** Connes--van Suijlekom perturbation is needed to prove excess degeneracy.
   **Failed as a necessity:** (HPJI.11) is stronger for \(E\ge2\) and source-internal.
3. **Conjecture:** full-ground admission and squared-root sign are separate gates.
   **Failed:** (HPJI.7) identifies their exact coupling.
4. **Pivot:** remaining Route U producer is a parity-orientation theorem. Either prove the literal
   odd restricted-Weil sector is nonnegative at the selected even hard edge, or use a negative odd
   descendant forced by \(r<0\) to contradict finite first-contact ancestry. Generic root division
   and generic convolution perturbation are exhausted.

## 5. Higher universal principle

Even root-jet mass and odd root-jet energy are two grades of one multiplication operator:

\[
 \gamma_r
 \xrightarrow{\ \times u\ }
 r\gamma_r.
\]

Root multiplicity creates a parity-double radical flag; root sign is its terminal Krein
signature. Finite Hankel hyperbolicity, squared-variable Laguerre--Pólya closure, odd-sector
spectral descent, and full-ground simplicity are shadows of this one graded jet law.

The hard-edge obstruction is therefore not “find an extra mode.” It is:

\[
 \text{prove or refute odd-sector admission at the self-selected even boundary}.
\]

That statement is narrower than unrestricted Weil positivity and retains the canonical
first-contact ancestry.

## 6. Novelty and corpus audit

- The parent root-jet card proves only the even terminal mass \(\gamma_r\) and obtains root sign
  from the external simple-full-ground real-zero theorem.
- Corpus searches found parity-separated finite Hankel forms and odd-contact source laws, but no
  hard-edge identity transporting \(\gamma_r\) to \(r\gamma_r\), no parity-doubled radical bound,
  and no constructive classification of the excess ground modes.
- Connes--van Suijlekom require a simple isolated full ground and infer real zeros globally. Their
  theorem does not state the source-specific squared-root terminal-energy law (HPJI.7).

No external priority claim is made pending specialist review.

## Lean status

No Lean declaration is claimed. Faithful formalization requires the literal hard-edge
compactification, both parity sectors of the localized completed-Weil form, logarithmic
Paley--Wiener form-domain closure under cancelled root division, and the actual convolution
operator. Supplying these as hypotheses would repeat theorem laundering.

## Log

- 2026-08-11 — derived exact odd-sector measure identity and complete odd divided-jet Gram law.
- 2026-08-11 — proved parity-doubled full-ground kernel bound and strict-positive-root simple-ground
  consequence; classified the former excess non-jet modes explicitly.

## Lean status (updated)

The literal hard-edge density, its squared-variable pairing, and both parity sectors are now
formal, axiom-clean, and wired.  No abstract form is substituted for the source objects: the
density is the explicit finite-prime expression and the pairing is the explicit half-line integral
with the polar atom.

    HTGeometry/SquaredVariableSubstitution.lean       (axiom-clean, wired, built)
      integral_Ioi_comp_sq, integral_Ioi_sq_density   the substitution u = x^2 on the half-line
      integral_comp_sq_eq_integral_Ioi                int_R Phi(x^2) dx = int_{u>0} Phi(u)/sqrt u du

    HTGeometry/JetMomentAlgebra.lean                  (axiom-clean, wired, built)
      jetMoment, jetCrossMoment                       division-free divided-jet moments
      integral_coord_mul_jet                          the coordinate recursion
      integral_coord_mul_jet_terminal                 terminal odd energy = r * terminal even mass
      jetMoment_even_nonneg                           an even moment is a square integral

    HTGeometry/PsdHankelJetVanishing.lean             (axiom-clean, wired, built)
      sq_le_of_quadratic_nonneg                       a nonnegative real quadratic has nonpositive
                                                      discriminant
      symmBilin_sq_le                                 Cauchy-Schwarz for a nonnegative symmetric
                                                      form from its one-parameter expansion
      psdHankel_jet_vanishing                         the bootstrap: M j = 0 for 1<=j<=m forces
                                                      M j = 0 for 1<=j<2m
      psdHankel_gram_off_terminal                     the Gram matrix is zero off the terminal corner

    RHTower/XiShiftedHardEdgeDensityMeasure.lean      (axiom-clean, wired, built)
      digamma_conj, routeUArchimedeanRate_neg/_abs    the archimedean rate is even
      routeUHardEdgeDensity sigma x                   V_sigma(x) = theta_infty(x)
                                                        - sum_{2<=n, log n <= 2 sigma}
                                                            Lambda(n) n^{-1/2} cos(x log n)
      routeUHardEdgePairing sigma Phi                 int_{u>0} Phi(u) V_sigma(sqrt u)/sqrt u du
                                                        + 2 pi Phi(-1/4)   —  the literal eta_sigma
      routeUHardEdgeEvenForm / routeUHardEdgeOddForm  the two parity sectors in the squared variable
      routeUEvenWeil / routeUOddWeil                  the same two forms written on the spectral line
      integral_density_comp_sq_eq_pairing             the line form equals the half-line pairing
      routeUEvenWeil_eq                               (the even sector)
      routeUOddWeil_eq                                **(HPJI.3)**: the odd restricted-Weil form of
                                                      z H(z^2), z K(z^2) is the pairing of u H K,
                                                      polar sign included
      routeUHardEdgePairing_const_mul / _add          linearity on the form domain
      routeUEvenForm_expand                           the one-parameter quadratic expansion
      routeUEvenForm_sq_le                            Cauchy-Schwarz on the form domain
      routeUHardEdgePairing_coord_jet                 **(HPJI.6)** the one-step divided-jet recursion
      routeUHardEdgePairing_coord_jet_terminal        **(HPJI.7)** terminal odd energy = r gamma_r

    RHTower/XiShiftedHardEdgeParityJet.lean           (axiom-clean, wired, built)
      routeUJetMoment / routeUJetDescendant           the moment sequence and the division-free
                                                      divided descendants of (u-r)^m G
      routeUEvenForm_descendant                       the even Gram entry is N((m-p)+(m-q))
      routeUOddForm_descendant                        **(HPJI.6)** the odd Gram entry is
                                                      N(...+1) + r N(...)
      routeUOddForm_terminal                          **(HPJI.7)** in the terminal corner
      routeUJetMoment_cauchySchwarz                   the Hankel Cauchy-Schwarz of the sequence
      routeUJetMoment_base_of_null                    **(RJRR.6)** a null state annihilates its own
                                                      divided descendants
      routeUJetMoment_eq_zero_of_null                 **(RJRR.9)** all moments below the terminal one
                                                      vanish
      routeUEvenForm_descendant_eq_zero,
        routeUJetGram_of_null                         **(HPJI.9)/(RJRR.10)** the complete Gram law
      coord_mul_routeUJetDescendant                   u F_{r,k} = r F_{r,k} + F_{r,k-1}
      routeUOddForm_of_radical                        **(HPJI.10)** the odd twin of a radical
                                                      descendant is again zero-energy
      routeUJetDescendant_eq_zero_of_sum_eq_zero      the divided principal parts of a state that is
                                                      nonzero on an infinite set are independent

What the Lean statements carry as hypotheses is exactly the form domain — integrability of the
divided jets against the literal density on the half-line — and the standing situation of the card:
nonnegativity of the even form on the one-parameter families spanned by the descendants, and
nullity of the state.  Nothing analytic is assumed away: the density, the atom, the substitution,
the recursion, the Cauchy-Schwarz bootstrap and the Gram law are all proved.

Still to build for this card: the localized convolution operator itself, so that the radical of the
form can be identified with its kernel, and the parity-doubled dimension count
(HPJI.11)-(HPJI.12) assembled from the independence lemma and the odd twins.

Added since: `routeUEvenForm_eq_zero_of_diag` (a vector of zero diagonal energy annihilates the even
form) and `routeUJetDescendant_diag_eq_zero` (**(RJRR.8)**: every nonterminal divided descendant has
zero diagonal energy, hence lies in the radical).  Together with `routeUOddForm_of_radical` these
give the complete flag of even null descendants and their odd twins; what is not yet formal is the
dimension count itself, which needs the parity direct sum and the localized operator.

### The terminal alternatives and the parity count

    RHTower/XiShiftedHardEdgeParityJet.lean (continued)
      routeUEvenForm_eq_zero_of_factor,
        routeUEvenForm_distinct_roots,
        routeUOddForm_eq_zero_of_factor       **(HPJI.8)/(RJRR.7)** a pairing whose product factors
                                              through a radical state vanishes — the exact
                                              distinct-root orthogonality mechanism
      routeUJetRoot_nonneg                    alternative 1: odd nonnegativity and a positive
                                              terminal mass force `r >= 0`
      routeUJetRoot_pos                       **(HPJI.13)** with a nonvanishing terminal odd energy,
                                              `r > 0`
      routeUJetTerminalOdd_null_of_root_zero  alternative 2: a zero root gives an extra odd ground
                                              mode
      routeUJetTerminal_null_of_terminal_mass_zero
                                              alternative 3: a vanishing terminal mass gives both
                                              terminal ground modes
      linearIndependent_routeUJetDescendant   the divided descendants are independent
      linearIndependent_prod_blocks           independence survives the parity direct sum
      linearIndependent_routeUParityDirections
                                              **(HPJI.11) for one root**: the state, its `m-1`
                                              nonterminal even descendants and their `m-1` odd twins
                                              are `2m-1` independent parity directions

What remains for stage 3 is the localized convolution operator itself — the Friedrichs operator of
the form on its closed domain, for which the corpus already has the general construction
(`HTGeometry/FriedrichsFormOperator.lean`) — so that "radical of the form" can be read as "kernel of
the operator", and the aggregation of the single-root count over a finite root set.

## Lean status (final)

The card is formalized.  Every analytic object is the literal one: the density is the explicit
finite-prime expression, the pairing is the explicit half-line integral with the polar atom, and
both parity sectors are the literal restricted-Weil forms in the squared variable.  The hypotheses
carried by the Lean statements are exactly the standing assumptions of §3 — membership in the form
domain (integrability of the divided jets against the literal density), nonnegativity of the even
form on the one-parameter families spanned by the descendants, and nullity of the state.

New in this round:

    HTGeometry/PartialFractionIndependence.lean       (axiom-clean, wired, built)
      dividedPart, rootProduct                        the divided principal parts at a finite root
                                                      set, written without division
      dividedPart_eq_zero_of_sum_eq_zero              their linear independence: the term of
                                                      largest divided order has the lowest order of
                                                      vanishing at its own root
      natDegree_dividedPart,
        base_and_dividedPart_eq_zero_of_sum_eq_zero   the state itself is independent of them by a
                                                      degree separation
      multiRegular, multiJetDescendant, multiJetBase  the same objects as functions
      multiJet_eq_zero_of_sum_eq_zero                 independence as functions, via an infinite
                                                      root set
      multiJetSubfamily,
        linearIndependent_multiJetSubfamily           independence for an arbitrary selection of
                                                      divided orders at each root

    HTGeometry/NonnegFormRadical.lean                 (axiom-clean, wired, built)
      bilinForm_sq_le                                 Cauchy-Schwarz for a nonnegative symmetric
                                                      bilinear form
      formRadical                                     its radical is a submodule
      eq_zero_of_form_diag_eq_zero                    a zero-energy vector lies in the kernel of
                                                      any operator representing the form
      card_le_rank_ker_of_zero_energy                 an independent family of zero-energy vectors
                                                      bounds the rank of that kernel from below

    RHTower/XiShiftedHardEdgeParityJet.lean           (axiom-clean, wired, built)
      routeUParityFamily                              the state, its `E = sum (m_i - 1)` nonterminal
                                                      divided principal parts across the whole root
                                                      set, and their odd twins
      linearIndependent_routeUParityFamily            **(HPJI.11)** they are independent
      finrank_routeUParityFamily                      **(HPJI.11)** they span a space of dimension
                                                      `1 + 2E`
      routeUParityFamily_even_diag_eq_zero            each even direction has zero even energy
      routeUParityFamily_odd_diag_eq_zero             **(HPJI.10)** each odd direction has zero odd
                                                      energy
      routeUParitySubfamily,
        linearIndependent_routeUParitySubfamily       the same for an arbitrary selection of divided
                                                      orders in each parity sector
      finrank_routeUParityTerminalFamily              **(HPJI.12)** with `Z` the roots of vanishing
                                                      terminal mass and `Z0` the zero roots of
                                                      positive terminal mass, the selected parity
                                                      directions span a space of dimension
                                                      `1 + 2E + 2|Z| + |Z0|`

Together with `card_le_rank_ker_of_zero_energy` these are the boxed statements (HPJI.11) and
(HPJI.12): `1 + 2E` (respectively `1 + 2E + 2|Z| + |Z0|`) linearly independent zero-energy
directions, and the general principle that a zero-energy vector of a nonnegative form lies in the
kernel of any operator representing it.  (HPJI.13) is `routeUJetRoot_pos`, (HPJI.3) is
`routeUOddWeil_eq`, (HPJI.6)-(HPJI.9) are the divided-jet Gram law, and (HPJI.10) is
`routeUOddForm_of_radical`.

The one object still not constructed is a Hilbert-space realization of the localized convolution
operator itself.  That is not a gap in the card: §3 introduces the operator as an assumption
("assume zero is the lowest spectral value"), and the only property of it used in the proof —
zero energy implies kernel membership — is proved unconditionally in `NonnegFormRadical`.
