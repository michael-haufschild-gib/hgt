# Reciprocal Paugam polarization of the Meyer regulator quotient

- **ID:** `deninger-meyer-reciprocal-paugam-polarization`
- **Stage:** 3-formalized
- **Type:** EXACT PARITY NO-GO WITH MINIMAL POSITIVE DOUBLED SURVIVOR
- **Label:** `DAC_DENINGER_MEYER_RECIPROCAL_PAUGAM_POLARIZATION`
- **Parent:** Route L in `rh-current-frontier-map.md`
- **Claim:** the one-dimensional local Meyer secondary-regulator quotient cannot be Paugam's odd
  \(K_{\mathbb R}\) coefficient.  Pairing reciprocal quotient lines is the minimal repair; it
  carries a canonical odd conjugation and an explicit positive zero-radical Paugam cup--Hodge
  diagonal. Subsequent grading audit proves this polarization is transverse regulator/degree-two
  data: it vanishes identically when pulled back to endpoint-global middle cycles.

## 1. The false local identification

The secondary-regulator theorem gives the canonical local quotient
\[
 Q_x=\mathbb C^2/\Gamma_x,\qquad
 \Gamma_x=\{(u,v):u=x^{-1}v\},
\]
and the defect coordinate
\[
 \bar\delta_x:Q_x\xrightarrow{\sim}\mathbb C.                  \tag{1}
\]

Paugam's nonreal spectral coefficient is odd: its anti-linear sign-conjugation \(\Sigma\) must
satisfy
\[
 \Sigma^2=-1.                                                  \tag{2}
\]
It is tempting to put `(2)` directly on \(Q_x\).  This is impossible.

The repository already proved the general theorem that no complex line admits a conjugate-linear
endomorphism squaring to \(-1\).  Transporting any hypothetical odd structure on \(Q_x\) through
`(1)` would contradict that theorem.  Therefore
\[
 \boxed{\operatorname{KRealStructure}_{\rm odd}(Q_x)=\varnothing.} \tag{3}
\]

The general odd-line theorem is prior infrastructure, not new knowledge.  New content is the
identification `(1)` from the actual Meyer regulator and the resulting obstruction `(3)` to the
specific Route L/Paugam comparison.

## 2. Reciprocal doubling

Poisson reflection exchanges radii \(x\) and \(x^{-1}\).  Define anti-linear maps
\[
 c_{x,y}
 =\bar\delta_y^{-1}\circ\operatorname{conj}\circ\bar\delta_x:
 Q_x\longrightarrow Q_y.                                      \tag{4}
\]
They obey
\[
 c_{y,x}c_{x,y}=1.
\]
Thus \(Q_x\) and \(Q_{x^{-1}}\) form a concrete Paugam upper/lower exchange.  Its sign-conjugation
is
\[
 \Sigma_x(q_+,q_-)
  =\bigl(c_{x^{-1},x}(q_-),-c_{x,x^{-1}}(q_+)\bigr),            \tag{5}
\]
and
\[
 \Sigma_x^2=-1.                                                \tag{6}
\]

Since one complex dimension is impossible and the reciprocal double has two, `(5)` is the minimal
odd repair.  It is not an arbitrary duplicate: the second factor is the Fourier-reflected collar
already forced by the secondary regulator.

## 3. Concrete cup and positive Hodge diagonal

In canonical defect coordinates define the oriented upper-to-lower cup
\[
 B_x(q_+,q_-)
  =-\bar\delta_x(q_+)\bar\delta_{x^{-1}}(q_-).                  \tag{7}
\]
Paugam's alternating split cup is
\[
 \omega_x((u_+,u_-),(v_+,v_-))
  =B_x(u_+,v_-)-B_x(v_+,u_-).                                  \tag{8}
\]
Substituting `(5)` into `(8)` gives the exact diagonal
\[
 \boxed{\;
 \omega_x(q,\Sigma_xq)
  =|\bar\delta_x(q_+)|^2+
    |\bar\delta_{x^{-1}}(q_-)|^2.
 \;}                                                          \tag{9}
\]
Consequently
\[
 \operatorname{Re}\omega_x(q,\Sigma_xq)\ge0,
\qquad
 \omega_x(q,\Sigma_xq)=0\iff q=0.                              \tag{10}
\]

This is a positive local bilinear relation on the actual reciprocal regulator quotient. It does
not import a post hoc Hilbert metric: norm coordinates in `(9)` are canonical defect coordinates
`(1)`, and sign in `(7)` is cup orientation for which Paugam's prescribed sign-conjugation is
positive. It is not yet a second Riemann bilinear relation on middle cohomology.

## 4. Consequences for Route L

The separated local architecture is now forced:

```text
single Poisson quotient line
    -- cannot be odd K_R -->
reciprocal physical/Fourier quotient double
    -- canonical conjugate exchange -->
Paugam odd sign-conjugation
    -- oriented cross-cup -->
positive zero-radical cup--Hodge diagonal.
```

Any claimed arithmetic comparison that identifies one prime quotient line alone with Paugam's
odd coefficient is false.  A valid comparison must retain reciprocal or upper/lower labels through
cup formation.

## 4a. Later grading correction

Endpoint-global cycle classification supplies decisive grading test. A genuine separated middle
cycle \(h\) satisfies
\[
 h_+(x)=x^{-1}h_-(x^{-1})\qquad(x>0).
\]
Therefore its class in every local Calderón quotient is zero:
\[
 [h_+(x),h_-(x^{-1})]_{Q_x}=0.
\]
The same holds at \(x^{-1}\), so reciprocal quotient double and diagonal `(9)` both pull back to
zero on every middle cycle.

Thus local reciprocal polarization remains correct but cannot itself be middle \(H^1\) Hodge
form. It belongs to transverse regulator/degree-two geometry. Missing middle Paugam form must be
constructed on one-collar endpoint-global cycles modulo Meyer boundaries, not on local defect
quotients.

## 5. Hostile audit

- **Not rediscovery of quaternionic parity.**  Impossibility of an odd complex line and existence
  on \(\mathbb C^2\) were already formalized.  This card applies that theorem to the newly
  constructed source quotient and identifies the forced reciprocal double.
- **Not arbitrary doubling.**  \(x^{-1}\) is the Fourier collar in Meyer--Poisson reflection.
- **Not generic positive linear algebra detached from source.**  Both quotient coordinates are
  the canonical source defects \(\bar\delta_x\) and \(\bar\delta_{x^{-1}}\).
- **Not the middle Hodge theorem.** Later grading theorem proves stronger negative statement:
  reciprocal local defect energy pulls back identically to zero on every endpoint-global middle
  cycle. Treating it as nondegenerate middle polarization is false.
- **Not a source flow theorem.**  Cup and parity are closed locally; weight-one flow compatibility
  with the actual arithmetic generator remains separate.

## 6. Novelty audit

Paugam's primary paper constructs the symplectic pairing and upper/lower sign-conjugation on the
Connes--Meyer spectral realization.  Meyer supplies the spectral quotient; Deninger supplies the
rational-Witt dynamical program.  No located source states the local obstruction `(3)` for the
Meyer secondary prime regulator, the reciprocal quotient exchange `(4)`--`(6)`, or its exact
positive diagonal `(9)`.

Repository search found the general odd-line theorem and generic Paugam split-pairing theorem, but
not their instantiation on the concrete Poisson regulator quotient.  External priority remains
provisional pending specialist review.

## 7. Lean status

Formalized unconditionally in:

- `GaloisForLFunctions/RHTower/DeningerMeyerReciprocalPaugamPolarization.lean`;
- `GaloisForLFunctions/RHTower/DeningerMeyerPaugamGradingObstruction.lean`.

Capstones:

1. `not_nonempty_deningerMeyerPoissonCollarQuotient_oddKReal`;
2. `deningerMeyerPoissonReciprocalPaugamExchange`;
3. `deningerMeyerPoissonReciprocal_signConjugation_sq`;
4. `deningerMeyerPoissonReciprocalCrossPairing`;
5. `deningerMeyerPoissonReciprocal_cupSigma_self`;
6. `deningerMeyerPoissonReciprocal_cupSigma_eq_zero_iff`;
7. `deningerMeyerEndpointCycleReciprocalQuotient_eq_zero`;
8. `deningerMeyerEndpointCycleReciprocal_cupSigma_self_zero`.

No `sorry`, `axiom`, `opaque`, `unsafe`, computation, zero set, or RH-equivalent hypothesis is
used.

## References

- Frédéric Paugam, *Spectral symmetries of zeta functions*,
  https://arxiv.org/abs/0803.0199.
- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann zeta function*,
  https://arxiv.org/abs/math/0412277.
- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  https://arxiv.org/abs/1807.06400.

## Log

- 2026-08-02 — Local quotient tested against odd \(K_{\mathbb R}\); single-line identification
  rejected by the existing dimension-parity theorem.
- 2026-08-02 — Reciprocal quotient exchange, odd sign-conjugation, oriented cup, and exact positive
  zero-radical diagonal constructed and Lean-formalized.
- 2026-08-02 — Endpoint-global grading audit proved local quotient and positive diagonal vanish on
  every genuine middle cycle; interpretation corrected from middle Hodge to transverse regulator.
