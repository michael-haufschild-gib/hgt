# Paired-Pauli zero-twirl invariance law

- **Stage:** 2 — fully proven on paper
- **Status:** `[PAPER-PROVED] [BRIDGE] [NOVELTY NOT CLAIMED]`
- **Parent:** `global-product-clifford-twirl-range-law.md`
- **Lean target:** `HTGeometry/TwoReplicaGlobalCliffordTwirlRange.lean`

## Exact statement

For every finite qubit register `V`, let `T_V` be independent doubled
Clifford averaging and let `C_Q` be conjugation by an arbitrary paired Pauli
word `Q tensor Q`. Then

\[
 \boxed{T_V C_Q=T_V,\qquad C_Q(\ker T_V)\subseteq\ker T_V.}
 \tag{1}
\]

The statement includes the empty register.

## Dependency-closed proof

For a finite group representation `u`, right-translation of the averaging
index gives

\[
 {1\over |G|}\sum_g u_g(u_hXu_h^*)u_g^*
 ={1\over |G|}\sum_g u_{gh}Xu_{gh}^*
 ={1\over |G|}\sum_g u_gXu_g^*.                  \tag{2}
\]

It remains to realize paired Pauli conjugation inside the strict product
Clifford representation without identifying projective gates informally.
For local label `p`, use identity code when `p=I`; for `p` a Pauli axis use
the square of the already formalized positive Clifford quarter-turn code.
Its one-qubit matrix is exactly

\[
 U_p=\eta_p P_p,qquad
 \eta_I=1,\quad \eta_X=\eta_Y=\eta_Z=i.           \tag{3}
\]

For a word `Q`, tensor multiplication gives

\[
 U_Q=\eta_Q P_Q,qquad |\eta_Q|^2=1.              \tag{4}
\]

Therefore doubled conjugation by `U_Q tensor U_Q` is exactly paired-Pauli
conjugation: its scalar phase and conjugate cancel. Apply `(2)` to this
strict product-Clifford code to obtain `T_V C_Q=T_V`. If `T_V X=0`, then
`T_V(C_QX)=0`, proving kernel invariance.

## Frontier consequence

The canonical nonsinglet layer

\[
 U_W=U_*\cap\ker T_V
\]

is now paired-Pauli invariant because both factors are invariant. Hence the
exact character projectors preserve `U_W`, and the aggregate visible
detector can recover every hidden character component modulo `U_W`.

## Hostile audit

- Kernel invariance is proved from an explicit strict-group code, not from
  the false assertion that projective Pauli matrices literally belong to
  `SU(2)` without phases.
- `(1)` does not imply first-order commutator invariance of the kernel.
- This theorem does not prove Hall expansion, central-Casimir reproduction,
  edge recovery, anti-concentration, complexity growth, or recurrence time.
- No novelty is claimed for finite-group averaging invariance.
