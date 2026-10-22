# Theta likelihood--Eisenstein mass-shell orientation

- **ID:** `theta-likelihood-eisenstein-mass-shell-orientation`
- **Stage:** 3-formalized / needs-audit
- **Type:** THEOREM (Lean)
- **Source:** `docs/handover/connes.md` §§19--20 and
  `docs/drafts/pipeline/1-in-progress/theta-wigner-eisenstein-orientation-current.md`
- **Statement:** Shifted pairs of atomic theta-likelihood gaps form exact integral Lorentz mass
  shells indexed by the Wigner--Eisenstein product mode; their log-rapidity phase is exactly the
  complete divisor phase and has strict negative upper-half-plane current on every nontrivial
  shell.

Labels: `[LEAN-FORMALIZED] [PAPER-PROVED] [SOURCE-CONNECTOR] [NOVELTY-UNVERIFIED] [NOT-RH]`

## Goal

Join two previously separate source architectures:

1. the positive fixed theta-likelihood measure with atomic gaps \(t_n=n^2-1\); and
2. the product-fibre/divisor characters in the Wigner--Bessel--Eisenstein expansion.

The desired output is a sign-producing theorem inside each complete arithmetic pair shell, not
another estimate or one-particle stochastic-order criterion.

## Gates

- [x] 0 → 1: exact source objects and existing divisor-phase theorem identified
- [x] 1 → 2: dependency-closed algebraic and analytic proof below
- [x] 2 → 3: Lean module
  `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodEisensteinMassShell` passes direct checking,
  targeted build, axiom audit, generated-index check, and formal lint
- [ ] 3 → 4: independent novelty audit and publication packaging

## Exact theorem

Write

\[
t_n=n^2-1,
\qquad q=(q_1,q_2),
\qquad n=q_1+1,
\qquad m=q_2+1,
\qquad k=nm.
\]

Then the shifted likelihood-gap pair obeys

\[
(t_n+1)(t_m+1)=k^2.                                      \tag{1}
\]

In energy--displacement coordinates

\[
E=t_n+t_m+2,
\qquad P=t_n-t_m,
\]

this is the exact Lorentz equation

\[
E^2-P^2=4k^2.                                             \tag{2}
\]

There is no loss in the shell equation: for every natural \(K\),

\[
(t_n+1)(t_m+1)=K^2
\quad\Longleftrightarrow\quad
nm=K.                                                      \tag{3}
\]

The zero-based positive factor packet

\[
\mathcal F_k=\{q:(q_1+1)(q_2+1)=k\}
\]

is therefore exactly the integral likelihood mass shell of mode \(k\). Its centered divisor
rapidity has the intrinsic gap formula

\[
d(q)
=\frac{\log n-\log m}{2}
=\frac{\log(t_n+1)-\log(t_m+1)}{4}.                       \tag{4}
\]

Define the complete likelihood-shell phase and its derivative by

\[
\Phi_k(z)=\sum_{q\in\mathcal F_k}e^{i d(q)z},
\qquad
\Phi'_k(z)=\sum_{q\in\mathcal F_k}i d(q)e^{i d(q)z}.       \tag{5}
\]

Then, exactly rather than asymptotically,

\[
\Phi_k(z)=\operatorname{thetaProductFiberCenteredPhase}(k,z)
          =\operatorname{centeredDivisorPhase}(k,z).       \tag{6}
\]

Consequently, for every \(k>1\) and \(\operatorname{Im}z>0\),

\[
\Im\!\left(\Phi'_k(z)\overline{\Phi_k(z)}\right)<0,        \tag{7}
\]

and \(\Phi_k(z)\ne0\).

For the Wigner notation of the parent card,

\[
\tau_b(k)=\sum_{nm=k}(m/n)^{ib}=\Phi_k(-2b).              \tag{8}
\]

Thus the divisor coefficient is the real-boundary value of the analytic likelihood mass-shell
phase. Equation (7) concerns its open upper half-plane, not the real boundary in (8).

If a common radial tail \(F\) is attached coherently to the shell, define

\[
B_k(z;F)=|F|^2\Im\!\left(\Phi'_k(z)\overline{\Phi_k(z)}\right). \tag{9}
\]

Then \(B_k(z;F)<0\) whenever \(k>1\), \(\operatorname{Im}z>0\), and \(F\ne0\). More importantly,
the actual untruncated theta phase current \(C_k(z)\) on this same shell has the exact decomposition

\[
C_k(z)=B_k(z;F_c)+S_k(c,z),                              \tag{10}
\]

where \(F_c\) is the common positive-half-line tail at centre \(c\ge0\), and \(S_k\) is the already
defined **complete corrected seam**: Hermitian-polarization defect plus all oriented swept-window
terms. No piece is discarded or estimated in (10).

## Proof

Equation (1) is immediate from \(t_n+1=n^2\) and \(t_m+1=m^2\). The difference-of-squares identity

\[
(a+b)^2-(a-b)^2=4ab
\]

with \(a=t_n+1\), \(b=t_m+1\) gives (2). If (1) equals \(K^2\), nonnegativity of \(nm\) and \(K\)
allows equality of the square roots, proving (3).

Since \(n,m>0\),

\[
\log(t_n+1)=\log(n^2)=2\log n,
\qquad
\log(t_m+1)=2\log m,
\]

which gives (4). Substituting (4) termwise in (5) proves the first equality in (6). The existing
successor embedding identifies \(\mathcal F_k\) with the complete divisor antidiagonal, proving the
second equality. Existing prime-power factorization of the centered divisor phase gives (7), and
(7) rules out an upper-half-plane zero.

Multiplication by \(|F|^2>0\) proves (9). Substitution into the existing exact
common-tail/window decomposition proves (10). The global theta current is already formalized as
the absolutely convergent sum of the actual currents \(C_k\); grouping introduces no additional
cross-shell term because every ordered atom pair has one unique product \(k=nm\).

Every step is unconditional.

## Correction to the pair-birth story

The first atom born under self-convolution in the preceding nondivisibility card is

\[
(3,3)=(t_2,t_2),
\qquad 3+3=6.
\]

This pair is the central divisor point \((n,m)=(2,2)\) on mode \(k=4\), but

\[
d(2,2)=0.
\]

Therefore the new atom at total gap \(6\) is **current-neutral in isolation**. It does not by
itself create the missing Fourier orientation. Its significance is that it belongs to the full
mode-four shell, whose reflected off-diagonal divisor pairs complete an oriented analytic packet.
The right unit is the complete arithmetic mass shell, not one newly created convolution atom.

This correction is formalized by
`thetaCuspLikelihood_selfConv_birth_is_mode_four_zeroRapidity`.

## Lean certificate

Module:

`formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspLikelihoodEisensteinMassShell.lean`

Principal declarations:

- `thetaCuspLikelihoodGap_add_one`
- `thetaCuspLikelihoodAtomicGapPair_massSq`
- `thetaCuspLikelihoodAtomicGapPair_lorentz_massShell`
- `thetaCuspLikelihoodAtomicGapPair_massShell_iff`
- `thetaCuspLikelihoodAtomicGapPair_mem_massShell`
- `thetaFactorPairLogDisplacement_eq_gapPair`
- `thetaCuspLikelihood_selfConv_birth_is_mode_four_zeroRapidity`
- `thetaCuspLikelihoodMassShellPhase_eq_productFiber`
- `thetaCuspLikelihoodMassShellPhaseDerivative_eq_productFiber`
- `thetaCuspLikelihoodMassShellPhase_current_lt_zero`
- `thetaCuspLikelihoodMassShellCoherentBaseCurrent_lt_zero`
- `thetaProductFiberActualPhaseCurrent_eq_likelihoodMassShellBase_add_correctedSeam`
- `thetaCuspLikelihoodMassShell_two_hermitian_sign_reversal`
- `thetaCuspLikelihoodMassShellPhase_ne_zero`

## Hostile audit

1. **Only atomic likelihood sector is represented.** The fixed theta-likelihood measure also has
   continuous ray components. Equations (1)--(8) do not orient those components.
2. **Shell phase is the coherent common-tail part.** Positive-half-line translation gives
   different swept windows to different factor-pair entries. It cannot be replaced by one common
   Bessel/radial scalar without retaining the corrected seam in (10).
3. **There is no extra cross-shell interference after pair expansion.** Existing absolute
   convergence permits exact grouping of every ordered pair by its unique product \(k\). The open
   defect is inside each \(C_k\), not between different product labels.
4. **Physical Wigner frequency is a boundary value.** Equation (8) uses real \(b\), hence real
   \(z=-2b\). Strict sign (7) holds only for \(\operatorname{Im}z>0\); divisor characters can vanish on the real
   boundary.
5. **No RH-equivalent hypothesis is hidden.** The strict sign is inherited from finite divisor
   factorization and unique factorization, not from Xi zero geometry.
6. **The central pair is not a phase producer.** Its rapidity and derivative contribution vanish.
   Any claim that the atom at \(6\) alone supplies orientation is false.
7. **Hermitian polarization can reverse the sign before endpoint windows.** On the first
   nontrivial shell \(k=2\), at
   \(z_*=\pi/\log 2+i/4\), Lean proves the likelihood-shell current is negative while the
   seam-free Hermitian common-unit-tail current is positive. Thus radial positivity alone cannot
   transport (7) to the actual current.

## Frontier consequence

Pairwise arithmetic phase orientation is no longer open inside a fixed complete product mode. The
remaining source problem is an **intra-shell Hermitian/seam domination theorem**:

> Prove, after summing the exact identities (10), that the complete corrected seams are dominated
> by the favorable likelihood-shell bases in the target upper strip.

The first nontrivial shell already excludes a naïve sign-preserving scalar radial transform.
Required theorem must use joint Hermitian polarization of reflected factor pairs together with
the nested endpoint windows. Viable forms are an exact completed-square identity for \(S_k\), a
conditional-positive kernel coupling its polarization and window parts, or a cofinal cancellation
law for \(\sum_k S_k\). Estimating either seam component separately repeats a recorded dead route.

This is direct frontier reduction: arithmetic orientation within every complete atomic shell is
settled, actual current is now expressed in the same likelihood coordinates, and the sign reversal
locates the precise datum still missing. RH and the global Hedenmalm current sign remain open.

## Novelty audit

The ingredients \(t_n=n^2-1\), divisor antidiagonals, Eisenstein divisor characters, and Lorentz
difference-of-squares algebra are individually classical or already present in this repository.
Targeted internal and external searches found no source making the exact fixed-likelihood-gap
mass-shell identification (1)--(4), the analytic phase transport (6)--(7), or the zero-rapidity
correction for the newly born atom. This does not establish priority. Label remains
`[NOVELTY-UNVERIFIED]`.

## Log

- 2026-07-21 — derived exact likelihood-gap mass shells; transferred complete divisor phase,
  strict current, and zero-freeness; formalized zero-rapidity correction for the `(3,3)` birth;
  connected oriented shell to actual current and explicit mode-two Hermitian sign reversal.
