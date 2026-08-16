# Additive heat aperture has an infinite shifted-zeta echo ladder

- **ID:** `additive-heat-aperture-shifted-zeta-echo-ladder`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper); coefficient laws formalized in Lean
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** The small-aperture expansion of the additive heat energy contains one complex
  channel for every backward zeta value `zeta(s-k)`; at a nontrivial zeta zero exactly the zeroth
  rung disappears and every later rung is provably nonzero.  After functional normalization, the
  strict tail is the forward sequence `zeta(1-conj(s)+k)`; the Euler logarithms of that sequence
  recover every prime-power value `Lambda(N)/log N` by exact coefficient peeling.

## Source observable

For `s=sigma+it` with `1/2<sigma<1`, let

```text
Psi_s(n)=n^(-s)/sqrt(zeta(2sigma)),
H_x(m,n)=exp(-pi x(m-n)^2),
E_s(x)=<Psi_s,H_x Psi_s>.
```

The value `E_s(x)` is finite and strictly positive for every `x>0`. The first heat-aperture theorem
identifies its leading singular value, zeroth complex echo, and finite part. This card gives the
complete complex echo family.

## Echo-ladder theorem `[PROVED HERE]`

There are real-channel coefficients `D_m(s)` such that the full polyhomogeneous expansion has the
form

```text
zeta(2sigma)E_s(x)
 ~ L(s)x^(sigma-1)
   +sum_(k>=0) [
       C_k(s)conj(zeta(s-k))x^((s+k-1)/2)
       +conj(C_k(s)conj(zeta(s-k))x^((s+k-1)/2))]
   +sum_(m>=0) D_m(s)x^m.                              (1)
```

Here `D_0(s)=|zeta(s)|^2`, and the exact archimedean echo coefficient is

```text
C_k(s)
 = Gamma(1-s) sin(pi(s+k)/2)
   (4pi)^((s+k-1)/2) Gamma((s+k)/2)
   /(k! sqrt(pi)).                                     (2)
```

For `t!=0`, the echo exponents have imaginary parts `+t/2` and `-t/2`, while the regular ladder
has real integer exponents, so every coefficient in (1) is intrinsically identifiable. For real
`s` in the strip, the echo exponents are nonintegral and remain distinct from the regular ladder.

More precisely, truncating the complex echo sum after `k=N` leaves a singular--regular remainder
of order `O_s(x^((sigma+N)/2))`; the smooth regular square has its ordinary integer-power heat
expansion.

## Proof

The boundary polylogarithm has the convergent local expansion

```text
f_s(theta)
 =Gamma(1-s)(-i theta)^(s-1)
  +sum_(k>=0) zeta(s-k)(i theta)^k/k!                 (3)
```

for `|theta|<2pi`. Put

```text
A_+(s)=Gamma(1-s)exp(-i pi(s-1)/2),
A_-(s)=Gamma(1-s)exp(+i pi(s-1)/2).
```

On the positive side, the coefficient of the singular term times the conjugate of the `k`-th
regular term is

```text
A_+(s)(-i)^k conj(zeta(s-k))/k!.
```

On the negative side it is

```text
A_-(s)i^k conj(zeta(s-k))/k!.
```

The heat kernel is even, so the averaged phase factor is

```text
[A_+(s)(-i)^k+A_-(s)i^k]/2
 =Gamma(1-s)sin(pi(s+k)/2).                            (4)
```

The Gaussian moment

```text
integral W_x(theta)|theta|^(s+k-1)dtheta/(2pi)
 =(4pi x)^((s+k-1)/2)Gamma((s+k)/2)/sqrt(pi)
```

then gives (2) and the `k`-th complex channel in (1). Taylor expansion of the smooth regular
square gives the real integer-power coefficients `D_m(s)`. Termwise truncation of (3), followed by
the same Gaussian moment bound, gives the stated remainder and hence the full expansion.

## Archimedean two-step law `[PROVED HERE]`

The coefficients satisfy

```text
C_(k+2)(s)
 =-[2pi(s+k)/((k+1)(k+2))] C_k(s).                    (5)
```

This follows immediately from

```text
sin(pi(s+k+2)/2)=-sin(pi(s+k)/2),
Gamma((s+k+2)/2)=((s+k)/2)Gamma((s+k)/2),
(k+2)!=(k+2)(k+1)k!.
```

Thus the even and odd echo values are each generated from one initial coefficient by exact
rational multipliers in `s`.

Writing `(a)_m` for the rising Pochhammer symbol, iteration of (5) gives the closed parity laws

```text
C_(2m)(s)
 =C_0(s)(-1)^m(4pi)^m(s/2)_m/(2m)!,

C_(2m+1)(s)
 =C_1(s)(-1)^m(4pi)^m((s+1)/2)_m/(2m+1)!.            (5a)
```

Hence the complete archimedean ladder is determined by the two values `C_0,C_1`.

## Single-missing-rung law `[PROVED HERE]`

Every `C_k(s)` is nonzero in the open critical strip. Indeed, Gamma has no zeros, its displayed
arguments have positive real part where needed, and `sin(pi(s+k)/2)=0` would force `s+k` to be an
even integer, which is incompatible with `1/2<Re(s)<1`.

For every `k>=1`,

```text
zeta(s-k)!=0.                                          (6)
```

To prove (6), put `w=s-k`. The functional equation expresses `zeta(w)` as nonzero archimedean
factors times `zeta(1-w)`. Since `Re(1-w)>1`, the Euler product gives `zeta(1-w)!=0`; the open-strip
condition excludes negative even `w`, because such a value would force `Re(s)` to be an integer.

Consequently,

```text
zeta(s)=0
 iff
the k=0 complex echo is absent and every k>=1 echo is present. (7)
```

The first surviving value is the previously recorded tangent `i zeta(s-1)`. Formula (7) upgrades
that tangent to an infinite, recursively weighted nonvanishing ladder.

## Forward-value and prime-power tail `[PROVED HERE]`

Let `e_k(s)=C_k(s)conj(zeta(s-k))` be the complex echo coefficient.  For every `k>=1`, the
functional equation gives

```text
e_k(s)
 =C_k(s)chi(conj(s)-k)zeta(1-conj(s)+k),
chi(w)=Gamma_R(1-w)/Gamma_R(w).                        (7a)
```

The last zeta value lies in `Re>1`.  Taking its canonical Euler logarithm and then peeling its
Dirichlet coefficients at large `k` recovers

```text
Lambda(N)/log N = 1/r  if N=p^r,
Lambda(N)/log N = 0    otherwise.                      (7b)
```

For real strip parameters these Euler-log echo values have strictly positive-definite Hankel
matrices of every order.  The complete theorem and proof are in
`additive-heat-echo-prime-power-tomography-law.md`.  Lean formalizes `(7a)` as
`heatApertureEchoValue_eq_forward`.

## Law developed from the relation

The heat aperture separates the zeta divisor from all backward shifts of that divisor. A
nontrivial zero is therefore an **isolated echo defect** in parameter depth: it removes exactly one
coefficient from a source-defined infinite family and leaves the entire tail nonzero.

For RH, the law gives a canonical measurement vocabulary:

```text
RH
 iff
every isolated zeroth-rung defect in the critical strip occurs at sigma=1/2. (8)
```

Equation (8) is a faithful measurement reformulation, not a proof of localization. Its new content
is the rigidity of the tail: no backward-shift cancellation can imitate the zeroth-rung defect.

## Novelty audit

The parent ingredients are classical: Jonquière's expansion, the zeta functional equation,
Poisson summation, and Gaussian moments. Searches across polylogarithm heat asymptotics, periodic
zeta Gaussian summability, zeta heat kernels, shifted zeta values, and additive heat regularization
found these ingredients separately. No located source states the full channel expansion (1), the
coefficient recurrence (5), or the single-missing-rung law (7) for this positive quadratic
observable.

Connes's zeta-zero heat trace and general zeta/heat-kernel literature concern spectral traces or
Mellin transforms, rather than this additive Toeplitz heat energy of the normalizable vector
`n^(-s)`. The candidate-new label remains provisional pending independent expert comparison.

## Lean certificate

The module

```text
formal/GaloisForLFunctions/RHTower/HeatApertureEchoLadder.lean
```

formalizes the actual coefficients (2) and proves

```text
heatApertureEchoCoeff_add_two
heatApertureEchoCoeff_ne_zero
riemannZeta_sub_nat_ne_zero_of_criticalStrip
heatApertureBackwardZetaValue_eq_zetaChi_mul_forward
heatApertureEchoValue_eq_forward
```

The targeted build passes. Each final theorem depends only on Lean's standard `propext`,
`Classical.choice`, and `Quot.sound` axioms. The positive additional value for a complete Lean
formalization of (1) is the local polylogarithm expansion with a Gaussian asymptotic-integration
theorem.

## Gates

- [x] exact infinite value family isolated
- [x] complete paper proof of the echo expansion
- [x] coefficient recurrence and nonvanishing proved
- [x] shifted-zeta tail nonvanishing proved
- [x] core coefficient and zeta-value laws formalized in Lean
- [x] targeted build and axiom audit pass
- [x] focused literature collision search
- [x] formalize Jonquière expansion and Gaussian asymptotic integration (see the 2026-08-16 notes)
- [ ] independent specialist novelty audit

## References checked

- A. Jonquière, *Note sur la série `sum x^n/n^s`*, Bulletin de la Société Mathématique de France
  17 (1889), 142--152.
- NIST DLMF §25.12, especially the local polylogarithm expansion 25.12.12.
- J. Lagarias and W.-C. Winnie Li, *The Lerch Zeta Function III: Polylogarithms and Special
  Values*, Research in the Mathematical Sciences 3 (2016).
- A. Connes, *Heat Expansion and Zeta*, arXiv:2402.13082, for comparison with a different
  zeta-zero heat observable.

## Log

- 2026-07-11 -- Expanded the single echo to the complete shifted-zeta ladder, proved the two-step
  archimedean recurrence and single-missing-rung law, completed a focused novelty search, and
  formalized the coefficient and shifted-zeta nonvanishing theorems.

## 2026-08-16 — Jonquière's expansion is formalized unconditionally

The polylogarithm boundary expansion this ladder is built on is now Lean-closed; see the
2026-08-16 section of `additive-heat-aperture-zeta-zero-echo.md` for the full account.  The two new
modules are

- `formal/GaloisForLFunctions/RHTower/HurwitzZetaSmallShift.lean` — the small-shift expansion
  `ζ(w, ±a) = [a^{-w}] + ζ(w) + O(a)` for every `Re w > 0`, continued off the convergent regime
  through the *entire* difference `ζ(·, a) - ζ`;
- `formal/GaloisForLFunctions/RHTower/JonquiereExpansion.lean` — `expZeta_eq_jonquiere`,
  `expZeta_neg_eq_jonquiere` and their linear remainder bounds.

Every declaration reports `propext, Classical.choice, Quot.sound`.  What remains for this card is
the Gaussian asymptotic integration.

## 2026-08-16 — Jonquière's expansion `(3)` is formalized to every order

The gate "formalize Jonquière expansion and Gaussian asymptotic integration" is closed on the
Jonquière side, and the Gaussian side was closed by `norm_heatMoment_sub_term_le` (equation `(6)`
of `additive-heat-aperture-zeta-zero-echo`, valid at every complex exponent with `Re λ > -1`).
All declarations report `propext, Classical.choice, Quot.sound`.

### The all-order small-shift expansion

`formal/GaloisForLFunctions/RHTower/HurwitzShiftTaylor.lean` builds the Taylor expansion of the
shifted power to every order **without** the binomial series, by an induction that trades one
order of the expansion for one unit of the exponent:

```text
shiftTaylorCoeff w j          = (∏_{i<j} (-w-i)) / j!
shiftTaylorCoeff_succ_mul     : shiftTaylorCoeff w (j+1) · (j+1) = -w · shiftTaylorCoeff (w+1) j
shiftRemainder w K x y        = (x+y)^{-w} - ∑_{j ≤ K} shiftTaylorCoeff w j · y^j · x^{-w-j}
hasDerivAt_shiftPoly          : ∂_y shiftRemainder w (K+1) x y = -w · shiftRemainder (w+1) K x y
norm_shiftRemainder_le (0 < Re w, x ≥ 1, |b| ≤ ½) :
    ‖shiftRemainder w K x b‖ ≤ shiftTaylorConst w K · x^{-Re w-K-1} · |b|^{K+1}
```

The bound is proved by induction on `K` with `w` varying: the mean-value inequality
`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` on `[0,b]` reduces order `K+1` at `w` to
order `K` at `w+1`, and the base case is the existing first-order bound.  Summing over
`x = n+1` gives

```text
shiftZetaTaylor b w K = ∑_{j<K} shiftTaylorCoeff w (j+1) · b^{j+1} · ζ(w+j+1)
norm_shiftDiffSeries_sub_taylor_le (0 < Re w, |b| ≤ ½) :
    ‖shiftDiffSeries b w - shiftZetaTaylor b w K‖ ≤ C · ζ(Re w+K+1) · |b|^{K+1}
```

### The phase identity and the channel coefficient

`formal/GaloisForLFunctions/RHTower/JonquierePhase.lean`:

```text
jonquiere_phase_identity :
    (e^{iπ(1-s)/2} + (-1)^k e^{-iπ(1-s)/2}) · cos(π(s-k)/2) = i^k sin(π s)
```

proved by writing everything through `E = e^{iπs/2}` and `e^{iπ/2} = i`, so the whole statement
becomes a polynomial identity in `E, E⁻¹, i^k, (-1)^k` closed by `linear_combination` against
`(-1)^k(-1)^k = 1`.

`formal/GaloisForLFunctions/RHTower/JonquiereChannel.lean` combines it with the functional
equation at `s-k`, Euler reflection and the descending Gamma recursion

```text
gamma_eq_prod_mul_gamma_sub : Γ(s) = (∏_{i<k}(s-1-i)) · Γ(s-k)
gamma_reflect_prod          : Γ(1-s)Γ(s-k)(∏_{i<k}(s-1-i)) sin(πs) = π
jonquiere_channel_coeff (0 < σ < 1) :
    (2π)^{-(1-s)-k} Γ(1-s) (e^{iπ(1-s)/2} + (-1)^k e^{-iπ(1-s)/2})
      · shiftTaylorCoeff (1-s) k · ζ(1-s+k)  =  ζ(s-k) i^k / k!
```

which is exactly the statement that the `k`-th Taylor term of the shift-difference series carries
the `k`-th regular Jonquière coefficient.

### The expansion itself

`formal/GaloisForLFunctions/RHTower/JonquiereAllOrder.lean`:

```text
jonquiereRegPoly s K θ = ∑_{k ≤ K} ζ(s-k) (iθ)^k / k!
expZeta_eq_jonquiere_order (0 < σ < 1, 0 < θ ≤ π) :
    Li_s(e^{iθ}) = A₊(s) θ^{s-1} + jonquiereRegPoly s K θ + jonquiereRemainderOrder s K θ
norm_expZeta_sub_jonquiereRegPoly_le :
    ‖Li_s(e^{iθ}) - (A₊(s) θ^{s-1} + jonquiereRegPoly s K θ)‖ ≤ jonquiereOrderConst s K · θ^{K+1}
expZeta_neg_eq_jonquiere_order, norm_jonquiereRemainderOrderNeg_le :
    the same at the reflected phase, with A₋(s) and jonquiereRegPoly s K (-θ)
```

This is the card's `(3)`, with the stated `O(θ^{K+1})` truncation error, on both sides of the
phase origin.

## 2026-08-16 — the closed parity laws `(5a)` and the single-missing-rung law `(7)`

`formal/GaloisForLFunctions/RHTower/HeatApertureEchoParity.lean` (unconditional, axiom-clean):

```text
factorial_mul_heatApertureEchoCoeff_two_mul,  heatApertureEchoCoeff_two_mul :
    (2m)!  · C_{2m}(s)   = C_0(s) (-1)^m (4π)^m ∏_{j<m} (s/2 + j)
factorial_mul_heatApertureEchoCoeff_two_mul_add_one, heatApertureEchoCoeff_two_mul_add_one :
    (2m+1)! · C_{2m+1}(s) = C_1(s) (-1)^m (4π)^m ∏_{j<m} ((s+1)/2 + j)
heatApertureEchoValue_zero      : e_0(s) = C_0(s) · conj(ζ(s))         (Schwarz reflection)
heatApertureEchoValue_ne_zero   : every rung with k ≥ 1 is nonzero in the strip
riemannZeta_eq_zero_iff_echoLadder (1/2 < σ < 1) :
    ζ(s) = 0  ↔  the k = 0 rung vanishes and every k ≥ 1 rung is present
```

The parity laws are proved division-free by induction on the two-step recurrence, then divided.
The Pochhammer symbols are written as explicit `Finset.range` products.

**Remaining for this card.**  The assembly of the full channel expansion `(1)`: the averaged
singular--regular phase `(-i)^k (A₊ + (-1)^k A₋)/2 = Γ(1-s) sin(π(s+k)/2)` (the card's `(4)`),
the regular integer ladder `D_m`, and the `O(x^{(σ+N)/2})` truncation remainder, all against the
Gaussian moments already available.

## 2026-08-16 — the channel expansion `(1)` is formalized; the card is complete

All declarations report `propext, Classical.choice, Quot.sound`.

### The averaged singular--regular phase `(4)`

`formal/GaloisForLFunctions/RHTower/JonquierePhase.lean`:

```text
jonquiere_lead_avg_identity :
    (-i)^k (e^{iπ(1-s)/2} + (-1)^k e^{-iπ(1-s)/2}) / 2 = sin(π(s+k)/2)
```

so `(-i)^k (A₊(s) + (-1)^k A₋(s))/2 = Γ(1-s) sin(π(s+k)/2)` — the card's `(4)` — is
`RHTower.jonquiereLead_avg_pow`.

### The all-order principal part and its square

```text
RHTower/HeatLadderPrincipal.lean
  germPrincipalOrder s K θ = A_±(s)|θ|^{s-1} + jonquiereRegPoly s K θ
  norm_phaseGerm_sub_principalOrder_le : ‖f_s(θ) - germPrincipalOrder s K θ‖ ≤ C_K |θ|^{K+1}

RHTower/HeatLadderExpand.lean
  ofReal_pow_eq_sign_mul_abs_cpow : θ^k = (sign) · |θ|^k
  leadSq_expand, leadRegCross_expand, regLeadCross_expand, regSq_expand
  germPrincipalOrder_mul_conj : the four groups of two-sided power tests at the exponents
      2σ-2,  s-1+k,  conj s-1+k,  and the integers k+l
```

### The finite moment sum and the coefficient identification

```text
RHTower/HeatLadderMoments.lean
  heatLadderMoments s K x  -- averaged coefficients times heatMoment x λ, exactly
  integrableOn_principalOrderSq_mul_heatMultiplier
  heatLadderMoments_eq (1/2 < σ < 1, 0 < x) :
      (1/2π)∫ W_x |germPrincipalOrder s K|² = heatLadderMoments s K x

RHTower/HeatLadderCoefficients.lean
  heatLadderCross_eq (0 < x) :
      (averaged k-th cross coefficient) · heatMomentTerm x (s-1+k)
        = heatApertureEchoValue s k · x^{(s+k-1)/2}
```

The last identity **is** the card's `(2)`: the `k`-th complex channel of the expansion carries
exactly `C_k(s) · conj(ζ(s-k)) · x^{(s+k-1)/2)}`, with `C_k(s)` the archimedean coefficient already
formalized in `HeatApertureEchoLadder.lean`.  Its proof is the phase identity `(4)`, the
conjugation `conj(ζ(s-k) i^k/k!) = conj(ζ(s-k))(-i)^k/k!`, and the splitting
`(4πx)^{(s+k-1)/2} = (4π)^{(s+k-1)/2} x^{(s+k-1)/2}`.

### The expansion and its truncation rate

```text
RHTower/HeatLadderAsymptotic.lean
  regPolyConst, germPrincipalOrderConst, heatLadderErrorConst
  norm_germSqOrder_sub_le (0 < σ < 1) :
      ‖|f_s|² - |germPrincipalOrder|²‖ ≤ C (|θ|^{K+σ} + |θ|^{K+1})
  norm_heatEnergy_sub_ladderMoments_le (1/2 < σ < 1, 0 < x) :
      ‖E_s(x)ζ(2σ) - heatLadderMoments s K x‖
        ≤ C (realHeatMoment x (K+σ) + realHeatMoment x (K+1))
  tendsto_heatEnergy_sub_ladderMoments : the difference tends to 0 as x ↓ 0
  tendsto_rpow_neg_mul_exp, heatMomentErr, tendsto_heatMomentErr_div,
  norm_heatMomentTerm_ofReal, isBigO_realHeatMoment :
      every real window moment satisfies  realHeatMoment x λ = O(x^{λ/2})
  isBigO_heatEnergy_sub_ladderMoments (1/2 < σ < 1) :
      E_s(x)ζ(2σ) - heatLadderMoments s K x  =  O(x^{(σ+K)/2})
```

The last theorem is the card's `(1)` together with its stated truncation order.  Combining it with
`heatLadderCross_eq` and the Gaussian moment asymptotic `norm_heatMoment_sub_term_le` (equation
`(6)` of the companion card) replaces every `heatMoment x λ` by `(4πx)^{λ/2}Γ((λ+1)/2)/√π` up to an
exponentially small error, which is precisely the displayed form of `(1)`: the singular power
`L(s)x^{σ-1}`, the complex echoes `C_k(s)conj(ζ(s-k))x^{(s+k-1)/2}` with their conjugates, and the
regular integer ladder `∑ D_m(s) x^m` (the odd integer moments drop out because the two-sided test
averages to `((1+(-1)^{k+l})/2)`).

## Gates

- [x] exact infinite value family isolated
- [x] complete paper proof of the echo expansion
- [x] coefficient recurrence and nonvanishing proved
- [x] shifted-zeta tail nonvanishing proved
- [x] core coefficient and zeta-value laws formalized in Lean
- [x] targeted build and axiom audit pass
- [x] focused literature collision search
- [x] formalize Jonquière expansion and Gaussian asymptotic integration
- [ ] independent specialist novelty audit
