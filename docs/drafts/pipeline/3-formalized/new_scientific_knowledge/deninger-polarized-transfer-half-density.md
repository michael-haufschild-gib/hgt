# Deninger polarized-transfer half-density law

- **ID:** `deninger-polarized-transfer-half-density`
- **Stage:** 3-formalized
- **Type:** ABSTRACT SOURCE THEOREM / SPECIALIZATION GATE
- **Parent:** `deninger-mw-gamma-brst-complex`
- **Lean modules:**
  `GaloisForLFunctions.RHTower.DeningerArithmeticPolarizedTransfer` (the ungraded form of `(4)`),
  `GaloisForLFunctions.RHTower.DeningerPolarizedHalfDensity` (the modulus-graded data, `(4)`,
  `(5)`, `(6)`, and the half-density factorization)

## Statement

Let \(H_r\) be coefficient spaces indexed by a positive modulus \(r\).  Suppose that a degree
\(n\) finite-syntomic power correspondence supplies pullback and pushforward maps
\[
 V_n:H_r\longrightarrow H_{nr},
 \qquad
 F_n:H_{nr}\longrightarrow H_r.
\]
Let \(B_r\) be Poincare pairings and \(J_r\) odd Hodge operators.  Define
\[
 g_r(x,y)=B_r(x,J_ry).
\]
Assume:

1. projection-formula adjunction
   \[
   B_{nr}(V_nx,z)=B_r(x,F_nz);                                    \tag{1}
   \]
2. Hodge naturality
   \[
   J_{nr}V_n=V_nJ_r;                                               \tag{2}
   \]
3. polarized degree law
   \[
   F_nV_n=n\,\mathrm{id}_{H_r}.                                   \tag{3}
   \]

Then
\[
 g_{nr}(V_nx,V_ny)=n\,g_r(x,y).                                  \tag{4}
\]
Consequently the half-density normalized transfer
\[
 U_n=n^{-1/2}V_n
\]
is an isometry:
\[
 g_{nr}(U_nx,U_ny)=g_r(x,y).                                     \tag{5}
\]
If \(V_mV_n=V_{mn}\), the positive square-root normalization is multiplicative and
\[
 U_mU_n=U_{mn}.                                                    \tag{6}
\]

For Milnor--Witt power transfers, `(3)` is replaced before polarized realization by
\[
 F_nV_n=n_\epsilon .
\]
Thus the exact source-realization obligation is
\[
 \operatorname{Real}^{\mathrm{pol}}_\Gamma(n_\epsilon)
   =n\,\mathrm{id}.                                                \tag{7}
\]
Equation `(7)` is a rank-collapse law inside the Gamma-polarized metric; it is not the false
claim that the bare real quadratic form \(n_\epsilon\) is positive.

## Proof

Using `(1)`, `(2)`, and `(3)`,
\[
\begin{aligned}
g_{nr}(V_nx,V_ny)
 &=B_{nr}(V_nx,J_{nr}V_ny)\\
 &=B_{nr}(V_nx,V_nJ_ry)\\
 &=B_r(x,F_nV_nJ_ry)\\
 &=B_r(x,nJ_ry)\\
 &=n\,g_r(x,y).
\end{aligned}
\]
This proves `(4)`.  Sesquilinearity and the positive real scalar \(n^{-1/2}\) give
\[
g_{nr}(U_nx,U_ny)=n^{-1}g_{nr}(V_nx,V_ny)=g_r(x,y),
\]
which is `(5)`.  Finally
\[
U_mU_n
  =m^{-1/2}n^{-1/2}V_mV_n
  =(mn)^{-1/2}V_{mn}
  =U_{mn},
\]
proving `(6)`.

## Deninger consequence

At discrete time \(t=\log n\), the unnormalized transfer decomposes as
\[
 V_n=e^{t/2}U_n.
\]
Therefore its infinitesimal generator, wherever the discrete semigroup extends to a strongly
continuous flow, has the forced form
\[
 \Theta=\frac12+A
\]
with \(A\) skew-symmetric for the Gamma-polarized metric.  This obtains Deninger's weight-one
half shift from finite-syntomic degree and Poincare adjunction, before any Xi-divisor comparison.

The theorem does not supply:

1. the Gamma-polarized realization or positivity;
2. equation `(7)`;
3. extension from the rational-time power semigroup to a closed continuous generator;
4. spectral comparison with Xi.

Those are separate construction theorems.

## Formalized statement

`GaloisForLFunctions/RHTower/DeningerArithmeticPolarizedTransfer.lean` proves the ungraded form
of `(4)`: `deningerPolarizedTransfer_pairing_scale` derives `B(Vx, J(Vy)) = q·B(x, Jy)` from
adjunction, Hodge naturality, the degree law, and right-linearity of the pairing, over an
arbitrary commutative semiring.

`GaloisForLFunctions/RHTower/DeningerPolarizedHalfDensity.lean` carries the graded statement:

- `DeningerPolarizedTransfer ι H` : coefficient spaces `H r` indexed by a modulus, with
  `pull n r : H r →ₗ H (modulus n r)`, `push n r : H (modulus n r) →ₗ H r`, Poincaré pairings
  `pairing r`, odd Hodge operators `hodge r`, and exactly the card's three axioms `adjunction`,
  `hodgeNatural`, `degree` — hypotheses `(1)`, `(2)`, `(3)`;
- `metric r x y = pairing r x (hodge r y)` : the cup--Hodge metric `g_r`;
- `metric_pull` : `g_{nr}(V_n x, V_n y) = n g_r(x,y)`, which is `(4)`;
- `normalized n r = (√n)⁻¹ • pull n r` : the half-density transfer `U_n`;
- `metric_normalized` : `g_{nr}(U_n x, U_n y) = g_r(x,y)` for `n ≥ 1`, which is `(5)`;
- `normalized_comp` : `(6)`.  The composite `U_m U_n` lands in `H (modulus m (modulus n r))` and
  `U_{mn}` in `H (modulus (m·n) r)`, so the statement transports along the modulus identity
  `hmod` by `deningerModulusCast`; given that the pullbacks compose, the normalizations do.  The
  proof is `√(mn) = √m √n`, so no positivity hypothesis on `m`, `n` is needed;
- `pull_eq_expHalfLog_smul_normalized` : `V_n = e^{(log n)/2} U_n`, and
  `metric_pull_eq_exp_log` : `g_{nr}(V_n x, V_n y) = e^{log n} g_r(x,y)`.  These are the
  half-density decomposition `V_n = e^{t/2}U_n` at discrete time `t = log n` from which the
  weight-one half shift is read off.

The transport lemma `deningerModulusCast_smul` is the one piece of infrastructure the graded
statement needs and mathlib does not have in this form.

Everything the theorem asserts — `(4)`, `(5)`, `(6)`, and the `t = log n` decomposition — is
formalized.  Items `(7)`, the Gamma-polarized realization, the continuous-generator extension,
and Xi comparison are the four things the card explicitly says the theorem does not supply.

### Verification

- Direct commands: `lake env lean` on both modules — pass with no errors and no warnings.
- Cached module build: `lake build GaloisForLFunctions.RHTower.DeningerPolarizedHalfDensity`
  completes (`✔ [2005/2005]`).
- Scratch `#print axioms`: `deningerPolarizedTransfer_pairing_scale` depends on no axioms at all;
  the graded theorems use `propext`, `Classical.choice`, `Quot.sound` and nothing else.
- Imported by the `GaloisForLFunctions.RHTower` umbrella.

## Gates

- [x] 0 → 1 in-progress: half-density law isolated
- [x] 1 → 2 fully-proven: `(4)`, `(5)`, `(6)` proved
- [x] 2 → 3 formalized: the graded transfer data, `(4)`, `(5)`, `(6)`, and `V_n = e^{t/2}U_n`
- [ ] 3 → 4 publication-ready: blocked on the four items the theorem does not supply, in
      particular `(7)`

## Hostile audit

- Bare \(n_\epsilon\) is indefinite.  Replacing `(7)` by “\(n_\epsilon>0\)” is false.
- \(F_nV_n=n_\epsilon\) has the correct order only when \(V_n\) is pullback and \(F_n\) is
  pushforward.  Swapping them would require the generally false scalar law for \(V_nF_n\).
- Projection onto an analytic cutoff may break `(1)` and `(3)`.  Half-density normalization must
  be imposed before compression.
- Equation `(2)` must be proved from the moving Gamma/rectangular polarization.  Proving it by
  comparing with Xi zeros would assume the purity conclusion.

## Novelty audit

The projection formula and degree formula are standard.  New content is the exact extraction
showing that Deninger's half shift follows from their Gamma-polarized combination and that the
only quadratic obstruction is the explicit rank-collapse law `(7)`.

## Log

- 2026-08-01 — Formalized `(5)`, `(6)`, and the half-density factorization.  The pre-existing
  module only had the ungraded `(4)` on a single space; the card's `H_r`/`H_{nr}` grading, the
  isometry, the multiplicativity, and the `t = log n` decomposition were all missing.  Added
  `DeningerPolarizedHalfDensity` with the `DeningerPolarizedTransfer` structure carrying exactly
  `(1)`--`(3)` as axioms, plus the modulus-transport lemma needed to state `(6)` across the
  dependent index.  Card moved to `3-formalized`.  `(7)` and the three other listed obligations
  remain open, as the card states.
