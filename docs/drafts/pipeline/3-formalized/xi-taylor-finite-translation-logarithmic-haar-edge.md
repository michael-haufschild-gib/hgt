# Xi Taylor finite translation and logarithmic Haar edge

- **ID:** xi-taylor-finite-translation-logarithmic-haar-edge
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/xi-taylor-theta-tail-core-density-current.md
- **Statement:** The exact two-component finite cosine--sine translation defect, including both packet--edge mixed currents, and the cofinal dyadic Haar row have absolute oriented current `o(n)|P_{2d+3}(z_n)|^2` on every source-selected anisotropic Taylor mesh, at one explicit logarithmic Haar depth.

## Goal

Remove the only finite-section obstruction created by translating the theta-tail source through
`log 2`.  The result must preserve the cosine--sine cancellation, control value and derivative
together, and use no Xi divisor data, real-rootedness, anti-Herglotz sign, limiting measure, or
continued-Cauchy sign.

This theorem closes the finite translation/top-edge gate.  It does not prove the full raw
theta-tail core-current estimate, which remains equivalent to RH.

## Gates

- [x] 0 → 1 in-progress: source-pure finite defect isolated and explicit
- [x] 1 → 2 fully-proven: complete proof below, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean capstone
  `eventually_logarithmicHaarTopRow_and_twoPhaseFullDefectCurrents_lt_scaled_normSq`, narrow build green,
  axiom audit green
- [ ] 3 → 4 publication-ready: standalone exposition not prepared

## Theorem

Let

```text
C_d(x,z)=sum_(j=0)^d (-1)^j (xz)^(2j)/(2j)!,
S_d(x,z)=sum_(j=0)^d (-1)^j x^(2j+1)z^(2j+1)/(2j+1)!,
H_d^+(x,z)=C_d(x,z)+iS_d(x,z),
H_d^-(x,z)=C_d(x,z)-iS_d(x,z).
```

For real `x,a`, define the two finite translation edges by the exact identities

```text
H_d^±(x+a,z)=H_d^±(x,z)H_d^±(a,z)-E_d^±(x,a;z).       (1)
```

Let `rho=4T''` be the canonical theta-tail density and put

```text
V_d^±(z,a)=integral_(0,infinity) rho(x)E_d^±(x,a;z) dx,
W_d^±(z,a)=integral_(0,infinity) rho(x)
               H_d^±(x,z)H_d^±(a,z) dx,
J_d^±(z,a)=-Im(partial_z W_d^± conjugate(V_d^±))
            -Im(partial_z V_d^± conjugate(W_d^±))
            +Im(partial_z V_d^± conjugate(V_d^±)).        (2)
```

Thus `J_d^±` is the complete current difference between the translated finite section and its
product packet, not merely the edge self-current.

Let `D` be any source-selected odd super-accurate Taylor schedule, let `sigma` be any complex
target, let `z_n` be its anisotropic centered mesh, and write

```text
d_n=D(stage_sigma(n))+1,
m=ord_sigma(xi),
k_n=(2m+1) clog_2(n+1),
a_n=2k_n log 2.
```

Then, for every `epsilon>0`, eventually

```text
|J_(d_n)^+(z_n,a_n)|
  < epsilon(n+1)|P_(2D(stage_sigma(n))+3)(z_n)|^2,       (3+)
|J_(d_n)^-(z_n,a_n)|
  < epsilon(n+1)|P_(2D(stage_sigma(n))+3)(z_n)|^2.       (3-)
```

At the same depth `k_n`, the integrated cofinal dyadic Haar row satisfies the identical bound.

## Proof

**[PROVED HERE]** Expanding the finite products gives the exact two-component translation laws

```text
C_d(x+a)=C_d(x)C_d(a)-S_d(x)S_d(a)-E_d^C,
S_d(x+a)=S_d(x)C_d(a)+C_d(x)S_d(a)-E_d^S.               (4)
```

Adding and subtracting `i` times the second identity diagonalizes `(4)` and gives `(1)` with
`E_d^±=E_d^C±iE_d^S`.  Parity is exact:

```text
E_d^C(x,a;-z)= E_d^C(x,a;z),
E_d^S(x,a;-z)=-E_d^S(x,a;z).
```

Consequently

```text
E_d^-(x,a;z)=E_d^+(x,a;-z),
partial_z E_d^-(x,a;z)=-partial_z E_d^+(x,a;-z).        (5)
```

This is the required two-component value relation.  In particular the second phase has no
independent truncation defect.

For a natural radius `R>=1`, define the joint positive-phase envelope

```text
N_d(z,a)=integral |rho(x)| |E_d^+(x,a;z)| dx
          +integral |rho(x)| |partial_z E_d^+(x,a;z)| dx. (6)
```

The exact finite Taylor remainder, integrated against the canonical density, gives for `|z|<=R`
and `a=2A clog_2(n+1) log 2`

```text
N_d(z,a)
 <= 32 C_R (2d+2) 4^(-d) [2(n+1)]^(6AR),               (7)
```

where `C_R` is the finite canonical density exponential-moment constant.  The estimate retains
the combined value--derivative edge; it does not split the three-term completed source.  Since
every admissible schedule has `d_n>=n`, the geometric factor in `(7)` beats every fixed power:

```text
N_(d_n)(z_n,a_n)(n+1)^M -> 0                            (8)
```

for every fixed `M`, because the anisotropic centered points are eventually contained in one
fixed ball.

Define the packet envelope

```text
M_d(z,a)=integral |rho(x)| |H_d^+(x,z)H_d^+(a,z)| dx
          +integral |rho(x)|
             |partial_z(H_d^+(x,z)H_d^+(a,z))| dx.
```

The common-cutoff phase section is bounded degree-independently by the full exponential series.
The arbitrary exponential moments of the exact canonical density therefore give

```text
M_d(z,a) <= 4 C'_R (R+1) exp((R+1)a).                   (9)
```

At `a=a_n`, the right side of `(9)` is a fixed power of `n+1`.  Keeping both mixed terms from the
exact current subtraction law and applying the triangle inequality only after that identity gives

```text
|J_d^+(z,a)| <= M_d(z,a)N_d(z,a)+N_d(z,a)^2.            (10)
```

Since `(8)` holds for every fixed power, `(9)`--`(10)` imply
`|J_(d_n)^+(z_n,a_n)|(n+1)^(2m)->0`.

Equations `(5)` and the corresponding reflection of the full finite packet also give the exact
reflected full-defect identity

```text
J_d^-(z,a)=-J_d^+(-z,a).                                (11)
```

Reflection preserves the packet and edge norm bounds.  Applying the positive-channel estimate
separately to `z_n` and `-z_n`, without reflecting the one-sided anisotropic mesh or its Taylor
denominator, yields

```text
|J_(d_n)^±(z_n,a_n)|(n+1)^(2m) -> 0.                    (12)
```

The source-selected Taylor lower bound at the local analytic order `m` converts `(12)` directly
to `(3+)` and `(3-)`.  This lower bound is local analytic multiplicity, not zero-location or
real-rootedness information.

Finally the exact cofinal Haar-row estimate has the form

```text
|R_k(d,z)| <= C''_R 2^(-k).                             (13)
```

For `k=k_n=(2m+1)clog_2(n+1)`, `(13)` times `(n+1)^(2m)` tends to zero.  The same local-order Taylor
lower bound therefore gives the relative `o(n)|P|^2` estimate for the top row.  Combining the
three eventual estimates proves the theorem.  No sign assumption enters the proof.  ∎

## Lean certificate

The exact finite system and its reflection are in
`formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailFiniteTranslation.lean`:

- `finitePositivePhasePolynomial_add_eq_mul_sub_topEdge`
- `finiteNegativePhasePolynomial_add_eq_mul_sub_topEdge`
- `finiteNegativePhaseTranslationTopEdge_eq_positive_comp_neg_X`
- `finiteNegativePhaseTranslationTopEdge_derivative_eval_eq_neg_positive_derivative_eval_neg`

The geometric edge estimates and Haar-row decay are in
`formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailLogarithmicHaarEdge.lean`:

- `tendsto_thetaCuspTailPhaseTranslationEdgeIntegratedNorm_mul_pow_zero`
- `tendsto_scheduled_dyadicHaarRemainderKernel_mul_localOrder_zero`

The exact mixed-current identity, packet envelope, local-order conversion, reflected full defect,
and capstone are in
`formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailFiniteTranslationDefectCurrent.lean`:

- `thetaCuspTailPhaseTranslationIntegratedCurrent_sub_exact`
- `abs_thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent_le`
- `eventually_abs_scheduled_thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent_lt_scaled_normSq`
- `eventually_abs_scheduled_thetaCuspTailNegativePhaseTranslationFullDefectIntegratedCurrent_lt_scaled_normSq`
- `eventually_logarithmicHaarTopRow_and_twoPhaseFullDefectCurrents_lt_scaled_normSq`

The normalization step is isolated in
`formal/GaloisForLFunctions/RHTower/XiCTaylorAnisotropicRelativeRemainder.lean` as
`eventually_remainder_lt_scaled_xiCTaylor_normSq_of_tendsto_localOrder`.

## Novelty and significance gate

The scalar Taylor remainder estimate is classical.  The result here is the source-specific
combination of the exact finite cosine--sine translation system, phase reflection at both value
and derivative level, canonical-density integration, source-selected logarithmic Haar depth, and
anisotropic Taylor normalization.  This exact combination was absent from the project corpus and
closes the last finite-section edge identified by the RH-equivalent core-current reduction.

The theorem is significant within the HGT/RH programme because it removes the finite truncation
edge without importing any RH-equivalent sign or measure statement.  It is not presented as a
proof of RH: the untruncated raw theta-tail/seam mixed current remains the decisive open term.
