# Theta-source conormal socle and Jordan-chain conservation

- **ID:** `ULF-ODTM-4`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM / FOUR-ORGAN FUSION LAW
- **Scientific status:** `[PROVED HERE] [DEPENDENCY-CLOSED] [LEAN-FORMALIZED] [NOT RH]`
- **Statement:** Kernel-growth converts geometric multiplicity one into one complete nilpotent
  chain.  Applied to every nonzero theta-source root block, its top nilpotent power is a nonzero
  rank-one conormal current whose range is exactly the ordinary eigenspace and whose exponent is
  the actual Xi multiplicity.

## Goal

Construct a source-native bounded realization of the multiplicity current from existing theta
source data, rather than postulating an operator model for the Xi quotient.  Required mechanism
must conserve the full divisor multiplicity and expose an exact reconstruction identity.

## Gates

- [x] 0 → 1: mechanism, collision audit, route fusion, and falsifier explicit
- [x] 1 → 2: dependency-closed proofs below
- [x] 2 → 3: Lean formalization and targeted audit
- [ ] 3 → 4: global conservative sewing and RH selection

## 1. Kernel-growth law

Let `K` be a field, `V` a finite-dimensional `K`-space, and `N:V→V` linear.  For every
nonnegative integer `k`,

\[
  \dim\ker N^k\le k\,\dim\ker N.                         \tag{TSC.1}
\]

### Proof

For composable finite-dimensional linear maps `f,g`, rank-nullity applied to the restriction of
`f` to `ker(gf)` gives

\[
  \dim\ker(gf)\le \dim\ker f+\dim\ker g.                \tag{TSC.2}
\]

The case `k=0` of (TSC.1) is `ker 1=0`.  If (TSC.1) holds at `k`, apply (TSC.2) to
`N^(k+1)=N^k N` and then the induction hypothesis:

\[
 \dim\ker N^{k+1}
 \le \dim\ker N+\dim\ker N^k
 \le (k+1)\dim\ker N.
\]
∎

The input (TSC.2) is already the linear-algebra engine of the corpus's homological transfer
organ.  Iterating it is the first fusion step: a transfer defect inequality becomes a spectral
chain-length law.

## 2. Coordinate-free single-chain theorem

Write `d=dim V`.  If `dim ker N=1`, then

\[
  N^{d-1}\ne0.                                            \tag{TSC.3}
\]

If in addition `N` is nilpotent, then

\[
  N^d=0,
  \qquad
  \operatorname{im}N^{d-1}=\ker N.                       \tag{TSC.4}
\]

Consequently `N` is one complete Jordan chain without choosing coordinates.  For `d=1`, its top
socle operator is `N^0=1`.  For `d≥2`,

\[
  C_N:=N^{d-1}\ne0,
  \quad \operatorname{im}C_N=\ker N,
  \quad \operatorname{rank}C_N=1,
  \quad C_N^2=0.                                          \tag{TSC.5}
\]

### Proof

Because `dim ker N=1`, `d>0`.  If `N^(d-1)=0`, then its kernel is all of `V`; (TSC.1) gives
`d≤d-1`, impossible.  This proves (TSC.3) without nilpotence.

For nilpotent `N`, Cayley-Hamilton and
`charpoly(N)=X^d` give `N^d=0`.  Therefore
`im N^(d-1)⊆ker N`.  The image is nonzero by (TSC.3), while the target kernel is one-dimensional;
hence equality, proving (TSC.4) and the rank statement.  If `d≥2`, then
`2(d-1)≥d`, so `C_N^2=N^(2(d-1))=0`. ∎

## 3. Actual theta-source conormal current

Let `B` be the fixed compact theta-source inverse.  For a nonzero spectral point `mu`, let

\[
  G_\mu=\operatorname{MaxGenEig}(B,\mu),\qquad
  N_\mu=B|_{G_\mu}-\mu I,
\]

and put `d_mu=dim G_mu`.  Existing corpus theorems give:

1. `G_mu` is finite dimensional;
2. `N_mu` is nilpotent;
3. every two `mu`-eigenvectors of `B` are proportional;
4. because `mu` is a nonzero compact spectral point, a nonzero `mu`-eigenvector exists.

### Theorem 3.1 — source conormal reconstruction

The ordinary eigenspace inside `G_mu` is exactly `ker N_mu` and has dimension one.  Hence

\[
  C_\mu:=N_\mu^{d_\mu-1}\ne0,
  \qquad
  \operatorname{im}C_\mu=\ker N_\mu.                    \tag{TSC.6}
\]

For `d_mu≥2`, `C_mu` is nonzero, rank one, and square-zero.  For `d_mu=1`, `C_mu=1`.

### Proof

The kernel equation `N_mu x=0` is exactly `Bx=mu x`.  Choose a nonzero eigenvector `v`.  Source
ODE uniqueness, already formalized as proportionality of every two nonzero-eigenvalue
eigenvectors, says every kernel vector is a scalar multiple of `v`.  Conversely `v` lies in the
kernel.  Thus `ker N_mu=K v` and has dimension one.  Apply the coordinate-free single-chain
theorem. ∎

Equation (TSC.6) is the promised exact conservation identity: the full generalized root block is
compressed by one canonical top-power operation to the uniquely reconstructible source
eigenline, without killing it.

## 4. Xi multiplicity and local phase prediction

For an actual Xi divisor support point `rho`, take

\[
 \mu_\rho=-(\alpha_\rho)^{-1}.
\]

The exact theta determinant multiplicity theorem gives

\[
 d_{\mu_\rho}=m_\rho,
\]

where `m_rho` is the analytic multiplicity of the Xi zero.  Therefore

\[
 C_\rho=N_{\mu_\rho}^{m_\rho-1}\ne0,
 \qquad \operatorname{im}C_\rho=\ker N_{\mu_\rho}.       \tag{TSC.7}
\]

This predicts and proves a sharp two-phase law in the source organ:

- simple Xi zero (`m_rho=1`): local conormal current is the identity on its root line;
- multiple Xi zero (`m_rho≥2`): local conormal current is a nonzero rank-one square-zero map.

This exactly matches the algebraic conormal phase exposed by `ULF-ODTM-2`: simple fibres carry an
invertible derivative class, while multiple fibres carry a nonzero nilpotent socle current.

## 5. Positivity consequence

Every `G_mu` is a finite-dimensional Hilbert space, so `C_mu` is bounded.  Apply the faithful
parity-suspension law `ULF-ODTM-3` to obtain an odd square-zero charge `Q_mu` and Hodge observer

\[
 H_\mu=Q_\mu^*Q_\mu+Q_\mu Q_\mu^*.
\]

Since `C_mu≠0`, faithfulness gives `Q_mu≠0` and `H_mu≠0`; `H_mu` is positive and self-adjoint.
Thus the actual source realizes multiplicity as a conservative positive graded system without
requiring a nilpotent current itself to be normal.

## 6. Fusion law and exact remaining gate

One mechanism now crosses four structurally different organs:

1. **homological transfer:** composite-kernel defect inequality (TSC.2);
2. **theta source:** compact root blocks and geometric uniqueness;
3. **Xi analytic divisor:** determinant order fixes chain length exactly;
4. **conormal/BRST/Hodge:** top socle current is faithfully suspended into positive energy.

No organ is merely renamed.  The transfer law predicts a new theorem in the theta organ,
the determinant identifies its exponent, and the Hodge organ receives a nonzero positive object.

Remaining RH gate is global, not local: construct a conservative direct-sum/direct-integral sewing
of the `C_rho` compatible with functional-equation reflection and prime-sector superselection,
then prove properness/selection.  Any proposed global sewing that kills a local range in (TSC.7)
is falsified as non-conservative.

## 7. Collision audit

- `BBBocksteinRank.finrank_ker_comp_le` contains (TSC.2), but does not iterate it, derive the
  single-chain theorem, or touch theta/Xi source blocks.
- `HedenmalmEssentialInverseFlowTrace` proves nilpotence of each root-block remainder, but not
  geometric kernel dimension one, nonvanishing of the top power, or its exact range.
- `HedenmalmThetaDivisorPolarizedInterpolation` proves eigenvector proportionality, but not the
  generalized-chain consequence.
- `HedenmalmPrimeTranslationJordanCapstone` proves algebraic multiplicity equality, but not a
  source conormal current.
- `ULF-ODTM-2` constructs the analytic Xi conormal current, but not its source-native bounded
  realization.

No novelty criterion is asserted or required.  Result is an exact integration and new
interpretation of already proved organs.

## Log

- 2026-08-31 — dependency-closed proof written; generic kernel-growth, top-power nonvanishing,
  nilpotent range reconstruction, and square-zero phase pass scratch Lean elaboration.
- 2026-08-31 — formalized as
  `GaloisForLFunctions.HTGeometry.ConstitutiveNilpotentSocleLaw` and
  `GaloisForLFunctions.RHTower.HedenmalmThetaSourceConormalSocle`; direct elaboration and batched
  named leaf build pass (`10961/10961`), umbrellas wired without building them, scoped forbidden
  scan and diff check pass, and audited capstones depend only on `propext`, `Classical.choice`, and
  `Quot.sound`.
