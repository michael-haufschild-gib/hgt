# Ordinary-integer BV Green--Stokes boundary and the physical radial coefficient

- **Stage:** 3-formalized

**Status:** paper-proved exact comparison; source Stokes relation constructed; physical annihilation not proved.

**Route:** L

## 1. Pre-specialization ordinary-integer chain

Let
\[
 \mathcal H=\ell^2(\mathbf N_{\ge 1}),\qquad
 S_ne_k=e_{nk},\qquad
 Qe_k=k^{-1}e_k,\qquad
 P_n=S_nS_n^* .
\]
All four objects are fixed before a Xi divisor point is selected. Directly on the standard
basis,
\[
 S_n^*QS_n=n^{-1}Q,\qquad QP_n=P_nQ.
 \tag{1}
\]
Consequently
\[
 \mathcal B_n
 :=[S_n^*,QS_n]
 =n^{-1}Q-P_nQ
 =b(S_n^*\otimes QS_n),
 \tag{2}
\]
where \(b(a_0\otimes a_1)=a_0a_1-a_1a_0\) is the degree-one Hochschild
boundary. Equation (2) is the required ordinary-integer Green--Stokes chain: its two terms are
the normalized coarse Green density and the density retained on the ordinary divisibility
sublattice \(n\mathbf N\).

For any completed Xi Green primitive \(G\), projective tensoring preserves (2):
\[
 G\widehat\otimes\mathcal B_n
 =(\mathrm{id}\widehat\otimes b)
   (G\widehat\otimes S_n^*\otimes QS_n).
 \tag{3}
\]
No zero, critical-line statement, compactness condition, or positivity criterion enters
(1)--(3). Since \(S_n\) and \(Q\) are bounded, this finite chain remains strict under every
completed projective tensor product used here.

## 2. Physical conormal evaluation

Put
\[
 \chi_n(s)=\exp\!\bigl((2\operatorname{Re}s-1)\log n\bigr).
 \tag{4}
\]
The gauge-diagonal Wold marginal of the centered conormal has exponent
\(\beta_s=2\operatorname{Re}s\). Normalizing its nonzero \(Q\)-value gives
\[
 \frac{\omega_s(P_nQ)}{\omega_s(Q)}
   =n^{-2\operatorname{Re}s}
   =n^{-1}\chi_n(s)^{-1}.
 \tag{5}
\]
Hence the physical value of the Green--Stokes boundary is
\[
 g_n(s)
 :=\frac{\omega_s(\mathcal B_n)}{\omega_s(Q)}
 =n^{-1}\bigl(1-\chi_n(s)^{-1}\bigr).
 \tag{6}
\]
Critical reflection \(s^\#=1-\overline s\) sends
\(\chi_n(s)\) to \(\chi_n(s)^{-1}\), so
\[
 g_n(s^\#)=n^{-1}(1-\chi_n(s)).
 \tag{7}
\]
Subtracting (7) from (6) gives the exact reflected Stokes-defect law
\[
 \boxed{\quad
 n\bigl(g_n(s)-g_n(s^\#)\bigr)
 =\chi_n(s)-\chi_n(s)^{-1}
 =K_n(s).
 \quad}
 \tag{8}
\]

At an actual Xi divisor \(\rho\), the prior Burnol/Deninger comparison identifies
\[
 K_n(\rho)=E_n^{\mathrm B}(\rho),
 \tag{9}
\]
where \(E_n^{\mathrm B}\) is the reflected squared-norm defect of the
multiplicity-exact nested co-Poisson conormal jets. Therefore
\[
 \boxed{\quad
 E_n^{\mathrm B}(\rho)
 =n\bigl(g_n(\rho)-g_n(\rho^\#)\bigr).
 \quad}
 \tag{10}
\]
At \(n=6\), the same scalar is already known to multiply the fixed nonzero
Gamma/Calderón--Witt incidence witness.

## 3. What Green--Stokes does and does not annihilate

Every cyclic trace \(\tau\) annihilates (2):
\[
 \tau(\mathcal B_n)=0.
 \tag{11}
\]
The physical conormal functional is not such a trace away from the critical line. Indeed,
(6), positivity of \(\chi_n(s)\), and \(n\ge2\) give
\[
 g_n(s)=0
 \quad\Longleftrightarrow\quad
 \chi_n(s)=1
 \quad\Longleftrightarrow\quad
 \operatorname{Re}s=\frac12 .
 \tag{12}
\]
Thus the tempting inference
\[
 \mathcal B_n\in bC_1
 \quad\Longrightarrow\quad
 \omega_\rho(\mathcal B_n)=0
\]
is invalid unless one first proves that the physical Xi conormal marginal is the strict
specialization of the source cyclic functional on this same chain. By (12), that descent
statement is already critical-line strength on every retained divisor fibre.

This is the precise chain-map obstruction. Source chain (2), its strict completed tensor (3),
and its physical value (10) are unconditional. Missing assertion is not existence of a
Green--Stokes boundary; it is descent of the physical completed/cofinal Xi Green landing through
the Hochschild quotient containing (2).

## 4. Hostile audit

1. **Not residue-Cuntz rediscovery.** Residue-class Cuntz/QMF partition is energy-neutral and
   its joint-eigenvector law is false for the actual Hurwitz residue packet. Equation (2) instead
   uses the ordinary divisibility sublattice and reciprocal Green density \(Q\).
2. **Not adelic product formula.** Product formula gives reciprocal finite and infinite gains.
   Equation (8) computes their reflected additive boundary defect.
3. **No RH-equivalent premise hidden in the proof.** Equations (1)--(10) are identities. Only
   vanishing statement is classification (12), explicitly not assumed.
4. **No generic commutator shortcut.** \(\mathcal B_n\) is a Hochschild boundary, but
   \(\omega_s\) is a modular/KMS functional. Its failure of cyclicity is exactly (6).
5. **No generalized-prime closure.** Formal symbols can imitate \(S_n\), but simultaneous
   ordinary-integer divisibility representation, reciprocal density \(Qe_k=k^{-1}e_k\), and
   finite-index normalization in (1) use actual lattice \(\mathbf N\). This gives an
   ordinary-integer carrier, not yet required Xi descent.

## 5. New frontier statement

**[OPEN CORE — XI_BV_GREEN_STOKES_STRICT_DESCENT]**

Construct one pre-specialization chain map from completed/cofinal Xi Green source tensored with
Wold/BV Hochschild complex to resolved Calderón--Witt incidence complex such that:

1. its degree-zero component is already-proved physical Burnol/Deninger landing;
2. it sends explicit primitive in (3) to a target boundary;
3. it retains divisor multiplicity and prime-labelled provenance through completion; and
4. it is obtained from arithmetic source before divisor specialization.

Then (3) makes source class zero, chain-map descent makes its physical image zero, (10)
annihilates \(E_n^{\mathrm B}(\rho)\), and coefficient-faithful incidence gives
\(\operatorname{Re}\rho=1/2\).

No such strict descent is proved here. Defining it only after evaluating \(\rho\), assuming
physical marginal is cyclic, or declaring its target image a boundary would import conclusion
through (12).

## 6. Formal status

`DeningerOrdinaryIntegerBVGreenStokesRadialComparison.lean` formalizes (1)--(2) on the
positive-integer sequence endomorphism algebra, including the literal degree-one Hochschild
primitive, and formalizes (6), (8), (10), and (12) through the existing Burnol/Deninger radial
comparison. All proofs are unconditional. The completed tensor statement (3) remains paper-level
because its strict Xi-to-incidence chain map is exactly the open core above.

- 2026-08-06 — Formalization re-verified on this toolchain: the named Lean module exists, is wired into `GaloisForLFunctions.RHTower`, builds, uses no `native_decide`, and every audited declaration depends only on `propext, Classical.choice, Quot.sound`.  Every gate this card states is closed; what the card lists as still open is its declared successor core, not this theorem.  Card moves to `3-formalized`.
