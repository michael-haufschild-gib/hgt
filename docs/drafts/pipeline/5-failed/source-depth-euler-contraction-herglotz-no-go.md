# Source-depth Euler contraction is never a global Herglotz carrier

- **ID:** `source-depth-euler-contraction-herglotz-no-go`
- **Stage:** 5-failed
- **Type:** EXACT ROUTE KILL / CONNECTION-FORM CORRECTION
- **Scientific status:** `[PAPER-PROVED] [REDISCOVERED] [NOT RH]`
- **Killed open core:** `SOURCE_DEPTH_CONNECTION_HERGLOTZ_PURITY` when “connection” means the
  balanced scalar
  \[
  {\cal G}_{\rm bal}(u)
  =-(u-\tfrac12)\Xi'(u)/\Xi(u).
  \]
- **Positive survivor:** the uncontracted logarithmic connection one-form, already represented
  unconditionally by `RHTower.XiHerglotzCriterion`.

## 1. Exact abstract no-go

Let \(\Phi\) be a nonzero even real entire function. Suppose \(a>0\) is a zero of \(\Phi\) of
multiplicity \(m\). Put
\[
 H_E(z):=-z\frac{\Phi'(z)}{\Phi(z)}.
 \tag{1}
\]
Then \(H_E\) is neither a meromorphic Herglotz function nor a meromorphic anti-Herglotz function
on the upper half-plane.

### Proof

Evenness gives a zero of the same multiplicity at \(-a\). The logarithmic derivative has residue
\(m\) at each zero, hence
\[
 \operatorname*{Res}_{z=a}H_E=-ma,
 \qquad
 \operatorname*{Res}_{z=-a}H_E=+ma.
 \tag{2}
\]
Every real pole of a meromorphic Herglotz function is simple with strictly negative residue.
Equation `(2)` therefore excludes the Herglotz property at \(-a\). Every real pole of a
meromorphic anti-Herglotz function has strictly positive residue, so `(2)` excludes the
anti-Herglotz property at \(a\). `QED`

The obstruction is structural, not a normalization issue. Multiplication by the centered
coordinate reverses residue orientation across the reflection-fixed point.

## 2. Application to the balanced Xi depth generator

Use the centered coordinate
\[
 u=\frac12+iz,
 \qquad
 \Phi(z)=\Xi(\tfrac12+iz)=\Xi_C(z).
 \tag{3}
\]
Since
\[
 \frac{\Phi'(z)}{\Phi(z)}
 =
 i\frac{\Xi'(u)}{\Xi(u)},
 \]
the balanced depth generator becomes
\[
 {\cal G}_{\rm bal}(\tfrac12+iz)
 =
 -z\frac{\Phi'(z)}{\Phi(z)}.
 \tag{4}
\]
Hardy's theorem supplies nonzero real zeros of \(\Phi\), so the abstract no-go applies
unconditionally. In particular, `(4)` would fail the Herglotz test even if RH were assumed.

Therefore the proposed implication
\[
 \text{positive realization of }{\cal G}_{\rm bal}
 \Longrightarrow
 {\cal G}_{\rm bal}\text{ Herglotz}
 \Longrightarrow RH
\]
cannot be the source-depth mechanism. Its middle statement is incompatible with the actual
critical-line divisor.

## 3. Exact representation error

Let
\[
 \omega_\Xi
 :=
 -d\log\Phi
 =
 -\frac{\Phi'(z)}{\Phi(z)}\,dz
 \tag{5}
\]
and let \(E=z\partial_z\) be the Euler field of the centered normal coordinate. Then
\[
 \iota_E\omega_\Xi
 =
 -z\frac{\Phi'(z)}{\Phi(z)}
 =
 {\cal G}_{\rm bal}(\tfrac12+iz).
 \tag{6}
\]
The depth-successor calculation produces the Euler contraction of the logarithmic connection,
not the Herglotz coefficient itself. Herglotz positivity is not preserved by contraction with an
Euler field that changes orientation at the reflection fixed point.

The deformation-to-normal-cone family already contains the uncontracted form. For
\[
 {\mathscr X}_0(\varepsilon,u)
 =
 \frac{\Xi(\varepsilon u)}{\Xi(u)},
 \]
one has
\[
 d_u\log{\mathscr X}_0(0,u)
 =
 -\frac{\Xi'(u)}{\Xi(u)}\,du.
 \tag{7}
\]
Under `(3)`, equation `(7)` is exactly `(5)`.

## 4. Strongest positive survivor

The source-depth theorem should be formulated for the logarithmic connection one-form `(5)`, not
its Euler contraction `(6)`.

Every real zero of \(\Phi\) contributes the same residue \(-m\) to the coefficient
\(-\Phi'/\Phi\). Consequently the residue-orientation obstruction disappears. For the actual
centered Xi function, the corpus already proves the exact target theorem:
\[
 RH
 \quad\Longleftrightarrow\quad
 -\operatorname{logDeriv}\Xi_C
 \text{ is Herglotz on }\mathbb C_+.
 \tag{8}
\]
The forward sign is
`RHTower.im_logDeriv_XiC_nonpos_of_rh`; the converse is
`RHTower.riemannHypothesis_of_im_logDeriv_nonpos`, both in
`formal/GaloisForLFunctions/RHTower/XiHerglotzCriterion.lean`.

Equation `(7)` adds a source-generation statement absent from the bare criterion: the correct
connection is the logarithmic differential of the exceptional DNC fibre. It does not add the
missing positivity theorem.

## 5. Stronger replacement conjecture and hostile status

`[CONJECTURE] [SOURCE_DEPTH_LOG_CONNECTION_FORM_REALIZATION]`

The prime-winning/depth deformation totalization admits a source-defined matrix-valued
Dirichlet-to-Neumann realization whose scalar logarithmic connection is the one-form `(7)`;
Gamma reflection is its real structure; and conservative Xi Cartier base change preserves the
matrix Herglotz cone and every multiplicity residue.

**Why the killing theorem no longer applies.** All divisor residues of the scalar coefficient are
\(-m\), independent of the sign of the centered zero coordinate.

**Hostile verdict:** `SURVIVES THE EULER-RESIDUE ATTACK`, but remains an `[OPEN CORE]`. Without a
divisor-free source construction of the matrix Herglotz cone, the conjecture is exactly the
existing Xi Herglotz criterion plus a renamed producer. No RH progress may be claimed from
`(7)` alone.

The first proof-bearing obligation is not another residue calculation. It is an explicit
finite-rectangle source Green identity whose boundary Weyl form differentiates to `(7)` and whose
matrix positivity is stable under horizontal prime-face and vertical exponent-depth enlargement.

## 6. Literature and novelty boundary

- Meromorphic Nevanlinna--Herglotz functions have real simple poles with strictly negative
  residues by the Herglotz representation theorem. A recent operator-theoretic statement appears
  in Gesztesy et al., *The Jacobi Operator on \((-1,1)\) and Its Various \(m\)-Functions*,
  Complex Analysis and Operator Theory 18 (2024), Section 8.
- Deformation-to-normal-cone geometry canonically carries an Euler vector field; see
  Sadegh--Higson, *Euler-like vector fields, deformation spaces and manifolds with filtered
  structure*, Documenta Math. 23 (2018), arXiv:1611.05312.
- The residue computation and Cartan contraction `(6)` are routine parent mathematics.
- The Xi Herglotz criterion is already unconditional Lean corpus knowledge.

No novelty is claimed. Mathematical delta is the exact falsification of the balanced-scalar
Herglotz route and identification of the correct DNC object as a logarithmic connection one-form.

## 7. Gates

- [x] exact residue no-go proved on paper
- [x] actual Xi coordinate identity proved on paper
- [x] positive connection-form survivor extracted
- [x] parent-theory and corpus collision recorded
- [x] existing Lean survivor identified
- [ ] divisor-free matrix Weyl realization of the DNC connection
- [ ] conservative Xi conormal base change
- [ ] RH

