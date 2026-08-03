# Route E Möbius friable \(u=2\) seam charge

- **ID:** `ROUTE-E-MOBIUS-FRIABLE-U2-SEAM-CHARGE-003`
- **Stage:** 3-formalized
- **Type:** CORRECTED PUBLISHED-THEOREM EXTRACTION / PROJECT-NEW SEAM NORMALIZATION
- **Parent:** `../../1-in-progress/route-e-squarefree-exponential-gibbs-parity.md`
- **Source:** `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no
- **Lean status:** delay equation with uniqueness, Taylor coefficient `a_0(mu)=1`, the seam jumps,
  and the exact largest-prime sector split `(20)` are formalized unconditionally in
  `MobiusFriableIntegerSeamProfile.lean`, `MobiusFriableDelayEquation.lean`,
  `MobiusFriableTaylorCoefficient.lean` and `MobiusFriableLargestPrimeDecomposition.lean`;
  the two cited analytic inputs (the friable expansion and the global Mertens estimate) remain
  external

## Result

Write
\[
 M_{\mathrm{fri}}(X,Y)
 =\sum_{\substack{n\le X\\P^+(n)\le Y}}\mu(n),
 \qquad
 u={\log X\over\log Y}.
\tag{1}
\]
The leading function in de la Bretèche--Tenenbaum's theorem for \(f=\mu\) is not their delay
solution \(\varphi_{-1}\).  It is
\[
 \psi_{-1}=\varphi_{-1}'',
\tag{2}
\]
because their negative-zeta-exponent convention has \(m=1\) and defines
\(\psi_z=\varphi_z^{(m+1)}\) when \(\Re z\le0\).

For \(1<u<2\),
\[
 \varphi_{-1}(u)=1+\log u,\qquad
 \psi_{-1}(u)=-{1\over u^2}.
\tag{3}
\]
The leading Taylor coefficient in their expansion is \(a_0(\mu)=1\).  Therefore, uniformly
through every left approach \(u\to2^-\) allowed by their theorem,
\[
 \boxed{\quad
 M_{\mathrm{fri}}\!\left(X,X^{1/u}\right)
 =-{X\over(\log X)^2}
  +O\!\left({X\over(\log X)^3}\right).
 \quad}
\tag{4}
\]
The main term is negative and exactly aperture-independent throughout \(1<u<2\).

The one-sided profile at the first integer seam has
\[
 \psi_{-1}(2-)=-{1\over4},\qquad
 \psi_{-1}(2+)={1\over4},
\tag{5}
\]
so the raw profile jump is \(1/2\).  Under the normalization forced by
\(\log Y=\log X/u\),
\[
 u^2\psi_{-1}(u):\quad -1\longrightarrow+1,
\tag{6}
\]
and the normalized seam-charge jump is exactly \(2\).

This is a profile statement.  At the integer seam itself, the published expansion contains an
additional boundary term \(U_J\) built from \(W_j\).  Equation `(6)` must not be misread as a
discontinuity of the arithmetic sum.

## Proof

### 1. Specialize the published notation

For \(f=\mu\),
\[
 {\cal F}(s)=\sum_{n\ge1}{\mu(n)\over n^s}=\zeta(s)^{-1}.
\tag{7}
\]
Thus the zeta exponent in de la Bretèche--Tenenbaum is \(z=-1\), with analytic factor
\({\cal B}(s)=1\).  Their notation gives
\[
 m_z=-1,\qquad m=1,\qquad \vartheta_z=0.
\tag{8}
\]
Their delay equation becomes
\[
 v\varphi_{-1}'(v)-\varphi_{-1}(v-1)=0\quad(v>1),
 \qquad
 \varphi_{-1}(v)=1\quad(0<v\le1).
\tag{9}
\]
Definition (1.28) of the paper, not the delay equation alone, identifies the asymptotic profile:
\[
 \psi_{-1}=\varphi_{-1}^{(m+1)}
 =\varphi_{-1}''.
\tag{10}
\]

The Taylor coefficients \(a_j(f)\) are defined by
\[
 {s^z{\cal F}(1+s)\over1+s}
 ={s^{-1}\over(1+s)\zeta(1+s)}
 =\sum_{j\ge0}a_j(\mu)s^j.
\tag{11}
\]
Since \(s\zeta(1+s)\to1\), `(11)` gives
\[
 a_0(\mu)=1.
\tag{12}
\]

### 2. Solve the first two delay branches

If \(1<v<2\), then \(v-1\in(0,1)\), so `(9)` gives
\[
 \varphi_{-1}'(v)={1\over v}.
\tag{13}
\]
Right continuity at \(v=1\) gives
\[
 \varphi_{-1}(v)=1+\log v,\qquad
 \varphi_{-1}''(v)=-{1\over v^2}.
\tag{14}
\]

If \(2<v<3\), then \(v-1\in(1,2)\).  Equations `(9)` and `(14)` give
\[
 \varphi_{-1}'(v)={1+\log(v-1)\over v}.
\tag{15}
\]
Hence
\[
 \lim_{v\to2^+}\varphi_{-1}''(v)
 =\left.{v/(v-1)-1-\log(v-1)\over v^2}\right|_{v=2}
 ={1\over4}.
\tag{16}
\]
The left limit from `(14)` is \(-1/4\), proving `(5)`.

### 3. Apply the friable expansion

Theorem 1.2 and Corollary 1.3(i) of de la Bretèche--Tenenbaum give, away from the relevant
integer-delay boundary,
\[
 M_{\mathrm{fri}}(X,Y)
 ={X\over(\log Y)^2}
 \left\{a_0(\mu)\psi_{-1}(u)
 O\!\left({1\over\log Y}\right)\right\}
\tag{17}
\]
for bounded \(u\).  Their admissible-set condition remains uniform on a left approach to \(2\):
when \(u<2\), the previous integer delay is \(1\), so \(u-1\) stays bounded away from zero.
Using `(12)` and `(14)` in `(17)` gives
\[
 M_{\mathrm{fri}}(X,Y)
 =-{X\over u^2(\log Y)^2}
 +O\!\left({X\over(\log Y)^3}\right).
\tag{18}
\]
Since \(\log Y=\log X/u\), the leading term in `(18)` is exactly
\[
 -{X\over(\log X)^2}.
\tag{19}
\]
For \(u\) in a fixed neighborhood below \(2\), its error has the form in `(4)`.

### 4. Identify the opposite sector

For \(1<u<2\), every \(n\le X<Y^2\) has at most one prime factor exceeding \(Y\).
Largest-prime factorization is therefore exact:
\[
 M(X)=M_{\mathrm{fri}}(X,Y)
      -\sum_{Y<p\le X}M(X/p).
\tag{20}
\]
The classical zero-free region gives \(M(X)=o_A(X/\log^A X)\) for every fixed \(A\).
Combining this with `(4)` shows that the one-large-prime sector has the opposite main charge:
\[
 -\sum_{Y<p\le X}M(X/p)
 ={X\over(\log X)^2}
  +O\!\left({X\over(\log X)^3}\right).
\tag{21}
\]
Thus the seam is a cancellation of a universal negative zero-large-prime charge against a
universal positive one-large-prime charge.

## Consequence for Route E

The critical Route E aperture has \(u=2-o(1)\), on the left of the first integer seam.
Consequently its deterministic zero-large-prime charge is already fixed by `(4)`:
\[
 -X/\log^2X.
\tag{22}
\]
The remaining source is not an unknown leading profile and not an unspecified ``friable bias.''
It is the source-fixed, label-sensitive cancellation of `(22)` against `(21)` after physical
cutoff localization, with strict-half control of the residual Gibbs energy.

This sharpens `CO-MOVING-RECTANGLE-SEAM-FLUX`:

> **`QUANTIZED-U2-SEAM-FLUX`.**  Construct a source-fixed prime-labeled cutoff flux whose
> zero-large-prime component has normalized charge \(-1\), whose one-large-prime component has
> normalized charge \(+1\), and whose combined remainder has strict-half Gibbs energy.

The leading charges cannot be estimated separately in absolute value.  Any valid construction
must reproduce them before cancellation.

## Hostile audit

1. **The old profile was wrong.**  Positivity of \(\varphi_{-1}\) says nothing about the sign of
   \(\psi_{-1}=\varphi_{-1}''\).  Replacing \(\psi\) by \(\varphi\) reverses the answer.
2. **No arithmetic discontinuity is claimed.**  The jump belongs to the one-sided profile.
   De la Bretèche--Tenenbaum add \(U_J\) near integer delays.
3. **No RH input is used.**  The friable expansion is unconditional in its stated range; the
   global Mertens estimate used in `(21)` follows from the classical zero-free region.
4. **No strict-half bound is obtained.**  Both sector charges have order \(X/\log^2X\), far
   above \(X^{1/2+\varepsilon}\).  Their localized residual remains `OPEN-SOURCE-001`.
5. **The Lean file does not impersonate the analytic theorem.**  It proves only `(14)`,
   aperture-independence `(19)`, and the jumps `(5)`--`(6)`.

## Novelty audit

The analytic expansion and delay system are published in de la Bretèche--Tenenbaum,
[*Friable averages of complex arithmetic functions*](https://arxiv.org/abs/2305.06486),
Theorem 1.2 and Corollary 1.3.  The branch integrations are elementary.

No claim is made that `(3)`--`(5)` are independently publishable discoveries.  The
project-relevant new content is the corrected specialization to Möbius, exact cancellation of
the aperture dependence in `(4)`, quantized normalization `(6)`, and identification of the two
Route E seam charges.  External priority for that extraction is unverified.

## Log

- 2026-08-01 — primary-source audit found that the previous Route E card substituted
  \(\varphi_{-1}\) for the published leading profile \(\psi_{-1}=\varphi_{-1}''\), reversing its
  sign.  Corrected the expansion, proved exact aperture-independence and the quantized \(u=2\)
  jump, and isolated `QUANTIZED-U2-SEAM-FLUX`.

## Lean completion programme (opened 2026-08-03)

Corpus audit before starting: `MobiusFriableIntegerSeamProfile.lean` held the branch formulas
`(3)`, the aperture-independence `(19)` and the jumps `(5)`–`(6)`; `FriableAuxiliary.lean` holds
iterated-derivative machinery for friable Dirichlet exponentials.  Neither the delay equation
itself, the Taylor coefficient `(11)`–`(12)`, nor the largest-prime identity `(20)` was formalized.
`Sieve/SmoothSum.lean` already owns the friable index set `smoothUpTo`, so the friable Möbius sums
are definable on existing corpus objects.

### `(9)`, `(13)`, `(15)` landed — `MobiusFriableDelayEquation.lean`

- `hasDerivAt_mobiusFriableDelayBelowTwo` : on the first branch `φ'(v) = φ(v−1)/v = 1/v`, which is
  the delay equation because `v−1` lies in the initial range;
- **`eq_mobiusFriableDelayBelowTwo_of_delayEquation`** : *uniqueness*.  Any function continuous on
  `[1,2]`, satisfying `φ'(v) = 1/v` from the right on `[1,2)`, with `φ(1) = 1`, equals `1 + log v`
  throughout `[1,2]`.  This replaces the card's appeal to "right continuity at `v=1`" by a
  mean-value argument (`constant_of_has_deriv_right_zero` applied to the difference);
- `mobiusFriableDelayDerivativeAboveTwo_eq` : the delay equation *propagates* — the second-branch
  derivative recorded in the corpus is exactly `φ(v−1)/v` with `φ` the first branch, which is `(15)`.

### `(7)`, `(11)`, `(12)` landed — `MobiusFriableTaylorCoefficient.lean`

- **`LSeries_moebius_eq_inv_riemannZeta`** : `∑ μ(n) n^{−s} = ζ(s)^{−1}` for `Re s > 1`, which is `(7)`;
- `tendsto_mul_riemannZeta_add_one` : `s ζ(1+s) → 1` as `s → 0`, `s ≠ 0` — the simple pole of `ζ`
  transported to the origin (mathlib's `riemannZeta_residue_one` composed with the shift);
- `mobiusFriableTaylor_eq` : on `Re s > 0` the expanded function of `(11)` equals
  `((1+s)·(s ζ(1+s)))^{−1}`;
- **`tendsto_mobiusFriableTaylor`** : that function tends to `1` at the origin — this is `a₀(μ)=1`,
  equation `(12)`, now a theorem rather than a computation.

### `(20)` landed — `MobiusFriableLargestPrimeDecomposition.lean`

The exact largest-prime decomposition, with no analytic input whatever:

- `mertensM`, `mertensFriable`, `largePrimes`, `mertensLargePrimeSector` — the two sectors;
- **`eq_of_two_large_primes`** : for `n ≤ X < Y²`, two prime factors above `Y` are impossible,
  since their product already divides `n`;
- `mertensM_eq_add_sector` : the two sectors partition `M(X)`, for every cut;
- **`mertensM_eq_mertensFriable_sub`** :
  `M(X) = M_fri(X,Y) − ∑_{Y < p ≤ X} M(X/p)` whenever `X < Y²`.
  The proof is a bijection `(p,m) ↦ pm` between the pairs `{Y < p ≤ X prime} × [1, X/p]` and the
  non-friable integers of `[1,X]`, together with `μ(pm) = −μ(m)` (which needs `p ∤ m`, again from
  `X < Y²`);
- `mertensLargePrimeSector_eq` : the one-large-prime sector is exactly `−∑_p M(X/p)`;
- `div_lt_of_mem_largePrimes`, `mertensFriable_div_eq` : below the seam `X/p < Y`, so the inner sums
  carry no friability restriction — this is the step the card states implicitly when it writes
  `M(X/p)` rather than `M_fri(X/p, Y)`;
- **`mertensM_eq_mertensFriable_sub_friable`** : the same identity with both sides friable.

Built, wired into `GaloisForLFunctions/RHTower.lean`, axiom-clean (fourteen theorems, every one
`[propext, Classical.choice, Quot.sound]`).

### What remains

Two inputs stay external, and both are genuine research-scale analytic theorems rather than
bookkeeping:

1. `(17)`/`(18)` — de la Bretèche–Tenenbaum's friable expansion.  Its proof is a Selberg–Delange
   development combined with a saddle-point analysis of the friable Dirichlet integral; nothing in
   mathlib or the corpus is close to it.
2. `(21)` — the global Mertens estimate `M(X) = o_A(X/\log^A X)`, which is the prime number theorem
   with the classical zero-free region.  Mathlib has the analytic continuation and the
   nonvanishing of `ζ` on `Re s = 1`, but not the Mertens/PNT asymptotic.

Everything the card proves *itself* — the corrected profile `(2)`–`(3)`, the branch solutions and
their uniqueness `(9)`, `(13)`–`(15)`, the seam limits `(5)`, the normalisation `(6)`, the Taylor
coefficient `(11)`–`(12)`, the aperture-independence `(19)`, and the exact sector split `(20)` — is
now an unconditional Lean theorem.

### Stage 2 → 3 audit (2026-08-03)

Every statement this card *proves* is now an unconditional Lean theorem:

| card equation | Lean declaration |
|-|-|
| `(1)` definitions | `mertensM`, `mertensFriable`, `mertensLargePrimeSector` |
| `(2)`, `(10)` profile is `φ''` | `mobiusFriableDelayFirstDerivative_hasDerivAt` |
| `(3)`, `(14)` first branch | `mobiusFriableDelayBelowTwo_formula_hasDerivAt`, `hasDerivAt_mobiusFriableDelayBelowTwo` |
| `(5)`, `(16)` seam limits | `mobiusFriableDelayDerivativeAboveTwo_hasDerivAt_two`, `mobiusFriableLeadingProfile_jumpAtTwo` |
| `(6)` quantized jump | `mobiusFriableScaledProfile_jumpAtTwo` |
| `(7)` `𝓕 = ζ⁻¹` | `LSeries_moebius_eq_inv_riemannZeta` |
| `(9)`, `(13)` delay equation + uniqueness | `eq_mobiusFriableDelayBelowTwo_of_delayEquation` |
| `(11)`, `(12)` `a₀(μ) = 1` | `tendsto_mobiusFriableTaylor`, `mobiusFriableTaylor_eq` |
| `(15)` second branch | `mobiusFriableDelayDerivativeAboveTwo_eq` |
| `(19)` aperture independence | `mobiusFriableLeadingProfile_apertureIndependent`, `_scaled` |
| `(20)` exact sector split | `mertensM_eq_mertensFriable_sub`, `_sub_friable`, `mertensLargePrimeSector_eq` |

The two inputs that remain external are *cited published theorems*, consistent with this card's own
type (`CORRECTED PUBLISHED-THEOREM EXTRACTION`) and with hostile-audit item 5, which scopes the Lean
obligation to the elementary content:

- de la Bretèche–Tenenbaum's friable expansion, used for `(4)`/`(17)`/`(18)`/`(22)`;
- the global Mertens estimate `M(X) = o_A(X/\log^A X)`, used for `(21)`.

Checked against this toolchain: mathlib supplies `riemannZeta`'s continuation, its residue at one,
its non-vanishing on `Re s > 1`, and both Chebyshev bounds (`Mathlib/NumberTheory/Chebyshev.lean`),
but no prime number theorem and no friable expansion.  Neither is reachable by adapting an existing
corpus asset; both are separate research-scale formalisations, and neither is needed for any
statement this card proves.

Stage advanced to `3-formalized`.
