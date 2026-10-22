# CCM unit-Riesz Möbius wavelet reduction

- **ID:** `ccm-unit-riesz-mobius-wavelet-reduction`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM (paper), exact source reduction
- **Scientific status:** `[PROVED] [KNOWN-DERIVED CORPUS INFRASTRUCTURE]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`
- **Parent:** `ccm-critical-mellin-aperture-resolvent-law.md`
- **Open consumer:**
  `../../1-in-progress/ccm-unit-riesz-causal-complement-wavelet.md`

## Statement

Unit-rate CCM aperture averaging has an arithmetic resonance in addition to its resolvent
resonance.  It converts the critical prime source exactly into the order-one Riesz weight.  The
full Möbius--log future dressing then collapses to a positive prime-power renewal, while the
remaining prime--polar discrepancy is exactly one zero-mean moving wavelet coefficient of the
critical causal complement `h_0(t)=exp(-t)-sum_(n<=exp(t))mu(n)/n`.

This identifies a source-specific half-unit coefficient problem strictly smaller than the full
weighted-Mertens `L2` tower.  It does not prove the coefficient bound.

Finite unit-Riesz normalization and complete Möbius-renewal collapse are formalized in
`formal/GaloisForLFunctions/RHTower/CCM/CCMCriticalMellinRieszMobiusRenewal.lean`.

## 1. Unit aperture is a double resonance

The already-proved unit aperture primitive is

```text
U(x)=integral_0^x [2 exp(-t)-exp(-t/2)]dt
    =2(exp(-x/2)-exp(-x)).                                (1)
```

For `0<n<=N`, put `x=log(N/n)` and normalize by the critical half-density.  Then

```text
U(log(N/n))/sqrt(n)
 =2/sqrt(N) * (1-sqrt(n/N)).                              (2)
```

The first monomial in `(2)` is independent of `n`.  For general aperture rate `a`, the two
monomials have powers `n^(a/2-1/2)` and `n^(a-1/2)`; only `a=1` removes `n` from the first one.
Thus unit rate is simultaneously the unique arithmetic resonance and the analytic Volterra
collapse rate from the parent card.

## 2. Sharp progression quadrature defect

For `t>=1`, define

```text
g(t)=sum_(1<=r<=t)(1-sqrt(r/t)),
eta(t)=t/3-g(t).                                         (3)
```

The layer-cake identity

```text
1-sqrt(u)=integral_u^1 dv/(2sqrt(v))                     (4)
```

gives, without asymptotics,

```text
g(t)=integral_0^1 floor(tv) dv/(2sqrt(v)),
eta(t)=integral_0^1 {tv} dv/(2sqrt(v)).                  (5)
```

Consequently

```text
0<=eta(t)<=1,
0<=eta(t)<=t/3.                                          (6)
```

For the averaged CCM prime weight, the mass on multiples of `q` is therefore

```text
K_N(q)=2/sqrt(N) g(N/q)
      =2sqrt(N)/(3q)-2/sqrt(N) eta(N/q),                 (7)
```

so every individual modulus already has a sharp `O(N^(-1/2))` quadrature defect.  Any off-line
growth must come from the cofinal signed Möbius assembly, not one progression.

## 3. Exact Möbius compensation

Let

```text
P_N=sum_(n<=N)Lambda(n)(1-sqrt(n/N)),
Q_N=-sum_(q<=N)mu(q)log(q)/q.                            (8)
```

The divisor law `sum_(q|n)mu(q)log(q)=-Lambda(n)` gives

```text
P_N=-sum_(q<=N)mu(q)log(q) g(N/q).                       (9)
```

Combining `(3)`, `(8)`, and `(9)` yields

```text
P_N-N/3
 =N/3*(Q_N-1)+sum_(q<=N)mu(q)log(q)eta(N/q).             (10)
```

Thus bounding the two terms in `(10)` separately is invalid: their main parts cancel exactly.

Define the positive cutoff

```text
W(t)=3g(t)/t=1-3eta(t)/t,       0<=W(t)<=1,              (11)

a_q=-mu(q)log(q)/q,
S_N=sum_(q<=N)a_q W(N/q).                                (12)
```

Then the entire future-dressed cube has the exact positive renewal collapse

```text
S_N=3P_N/N.                                              (13)
```

Equivalently, writing

```text
J_N=2/sqrt(N)*(P_N-N/3),                                 (14)
```

one has

```text
J_N=2sqrt(N)/3*(S_N-1).                                  (15)
```

This falsifies the proposed probability-contraction provider.  Complete future dressing does not
leave a smaller signed Euler packet: it is exactly the positive von-Mangoldt prime-power renewal.
The only cancellation left is renewal mass versus the polar continuum `N/3`.

## 4. Critical Möbius wavelet

Let `T=log N` and use the corpus critical boundary vector

```text
m_0(u)=sum_(q<=exp(u))mu(q)/q.                            (16)
```

On `0<=u<=T`, define

```text
Phi_T(u)=u W(exp(T-u)),
K_T(u)=Phi_T'(u)          almost everywhere.             (17)
```

Both endpoints of `Phi_T` vanish: `Phi_T(0)=0` and `W(1)=0`.  Stieltjes partial summation in
`(12)` therefore gives

```text
S_N=integral_0^T m_0(u)K_T(u)du,
integral_0^T K_T(u)du=0.                                 (18)
```

So the normalized CCM Riesz mass is one canonical zero-mean wavelet measurement of the
unconditional critical Möbius vector, not a norm of its weighted tail.

## 5. Causal-complement localization

The corpus proves the exact critical causal graph identity

```text
m_0(u)+h_0(u)=exp(-u).                                   (19)
```

Put

```text
A_T=integral_0^T exp(-u)K_T(u)du.                        (20)
```

Integration by parts and `(17)` give

```text
A_T=integral_0^T u exp(-u)W(exp(T-u))du.                 (21)
```

Since `0<=W<=1` and `1-W(t)=3eta(t)/t<=3/t`,

```text
0<=1-A_T
 <=integral_T^infinity u exp(-u)du
   +3exp(-T)integral_0^T u du
 =(3T^2/2+T+1)exp(-T).                                  (22)
```

Equations `(18)--(22)` produce the exact frontier identity

```text
S_N-1=(A_T-1)-integral_0^T h_0(u)K_T(u)du.               (23)
```

The pole channel is therefore saturated at `1` with a full exponential margin.  Every possible
half-unit obstruction is carried by one signed causal-complement wavelet coefficient.

## 6. Consequence for the RH frontier

For every `epsilon>0`, the desired one-sided CCM bound

```text
J_N<=C_epsilon N^epsilon                                 (24)
```

is equivalent, up to the explicit negligible error `(22)`, to

```text
integral_0^T h_0(u)K_T(u)du
  >=-C_epsilon exp(-(1/2-epsilon)T).                     (25)
```

This is not a proof of `(25)`.  It is a strict data reduction relative to the known sufficient
condition `exp(alpha t)m_0 in L2` for every `alpha<1/2`: only one one-sided, zero-mean coefficient
per physical aperture is required.

## Hostile audit

1. **Generic `L2` is insufficient.**  A general `L2` vector can align with the negative lobe of
   `K_T`; no exponential coefficient decay follows.
2. **Probability contraction is exhausted.**  Equation `(13)` shows exact contraction merely
   reconstructs the positive prime-power renewal.
3. **Separate `Q_N` and `eta` bounds are forbidden.**  Equation `(10)` contains an exact main-term
   cancellation; absolute values lose `sqrt(N)`.
4. **Fixed Euler grades are insufficient.**  The divisor collapse in `(9)` needs every squarefree
   grade before scalar estimation.
5. **The conjectural step remains RH-bearing.**  After the one-sided Landau connector, `(25)` is
   equivalent to RH.  It must not be advertised as an unconditional estimate.

## Literature boundary

Classical and recent Möbius Riesz criteria study weights such as
`sum mu(n)(1-n/x)^tau` or exponential Riesz kernels.  They do not state `(17)--(25)` for the
unit-aperture CCM profile and its causal complement.  Connes--Consani's archimedean trace work
constructs the positivity framework, while the 2025 zeta-spectral-triple paper explicitly leaves
rigorous spectral/determinant convergence as the RH-closing step.  No located source proves `(25)`.

Novelty claim withdrawn.  Equations `(1)--(25)` are elementary Laplace, Möbius inversion, and
Stieltjes calculus; their value here is exact corpus closure and frontier localization.

## Gates

- [x] unit-aperture arithmetic resonance
- [x] exact positive fractional-part quadrature defect
- [x] exact Möbius compensation and positive-renewal collapse
- [x] zero-mean critical Möbius wavelet
- [x] deterministic pole-channel saturation with explicit error
- [x] causal-complement localization of the half-unit burden
- [x] finite normalization and renewal core formalized
- [ ] prove causal-complement coefficient bound `(25)`
- [ ] compose with one-sided Landau connector
- [ ] RH

## Lean status — the layer-cake quadrature defect, 2026-08-15

`formal/GaloisForLFunctions/RHTower/CCM/CCMUnitRieszQuadratureDefect.lean` (wired, axiom-clean, 19
declarations) proves section 2 exactly.

- `layerWeight`, **`integral_layerWeight`** — equation `(4)`:
  `1 - sqrt a = int_a^1 dv/(2 sqrt v)`, by the fundamental theorem of calculus with primitive
  `sqrt`; and `integral_layerWeight_unit`: the whole layer has mass `1`.
- `rieszProgressionSum`, `rieszQuadratureDefect` — the card's `g(t)` and `eta(t) = t/3 - g(t)`.
- **`sum_indicator_eq_floor`** — the counting identity
  `sum_{r < floor t} 1_{(r+1)/t <= v} = floor (t v)` for `0 <= v <= 1`, which is what makes the
  layer cake a single integral.
- **`integral_floor_layerWeight`** — equation `(5)`, first half:
  `g(t) = int_0^1 floor (t v) dv/(2 sqrt v)`.
- **`integral_polar_layerWeight`** — the polar continuum in the same coordinates:
  `int_0^1 t v dv/(2 sqrt v) = t/3`.
- **`rieszQuadratureDefect_eq`** — equation `(5)`, second half:
  `eta(t) = int_0^1 (t v - floor (t v)) dv/(2 sqrt v)`.
- **`rieszQuadratureDefect_nonneg`**, **`rieszQuadratureDefect_le_one`**,
  **`rieszQuadratureDefect_le_third`** — equation `(6)`: `0 <= eta(t) <= min (1, t/3)`, directly
  from `0 <= {t v} <= min (1, t v)`.
- **`unitRieszLogProfile_eq_progression`** — the corpus's cell-assembled profile is exactly
  `W(t) = 3 g(t)/t` at `t = exp v`.
- **`one_sub_unitRieszLogProfile_le`** — equation `(11)`'s sharp form:
  `1 - W(t) = 3 eta(t)/t <= 3/t`, i.e. `1 - W(exp v) <= 3 exp(-v)`.  This is the estimate the
  pole-channel bound `(22)` consumes.

Still to formalize for this card: `(7)`, `(10)`, `(15)`, the Stieltjes partial summation `(18)`,
the pole-channel saturation `(20)`-`(23)`, and the equivalence `(25)`.

## Lean status — complete, 2026-08-16

`[FORMALIZED]` — the remaining items of the previous section are now proved in the new module

`formal/GaloisForLFunctions/RHTower/CCM/CCMUnitRieszWaveletFrontier.lean`
(8 theorems, all unconditional, axioms exactly `[propext, Classical.choice, Quot.sound]`, wired into
`formal/GaloisForLFunctions/RHTower.lean`).

- `progressionMass`, **`progressionMass_eq`** — equation `(7)`:
  `K_N(q) = 2√N/(3q) − 2 η(N/q)/√N`, so every individual modulus already carries a sharp
  `O(N^{-1/2})` quadrature defect.
- **`mobius_compensation`** — equation `(10)`:
  `(−∑_q μ(q)log q · g(N/q)) − N/3 = (N/3)(Q_N − 1) + ∑_q μ(q)log q · η(N/q)`, the exact
  cancellation of the two main parts (so they may not be bounded separately).
- **`riesz_normalization_eq`** — equation `(15)`: `J_N = (2√N/3)(S_N − 1)`.
- **`integral_kernel_zero_mean`** — equation `(18)`, zero-mean half: a kernel that is the derivative
  of a primitive vanishing at both endpoints integrates to `0`.
- **`integral_u_exp_neg`** — the exact window moment `∫_0^T u e^{-u} du = 1 − (T+1)e^{-T}`.
- **`one_sub_poleChannel_le`** — equations `(20)`–`(22)`: with the sharp cutoff bound
  `1 − W(t) ≤ 3/t` (already proved as `one_sub_unitRieszLogProfile_le`) the pole channel is
  saturated at `1` with the explicit margin `1 − A_T ≤ (3T²/2 + T + 1)e^{-T}`.
- **`frontier_identity`** — equation `(23)`:
  `S_N − 1 = (A_T − 1) − ∫_0^T h_0 K_T`, using the causal graph identity `m_0 = e^{-u} − h_0`.
- **`frontier_equivalence`** — equation `(25)`: the one-sided bound `J_N ≤ M` is *equivalent* to the
  one-sided lower bound `(A_T − 1) − 3M/(2√N) ≤ ∫_0^T h_0 K_T` on the single causal-complement
  wavelet coefficient.

Together with `CCMUnitRieszQuadratureDefect` (section 2) and
`CCMCriticalMellinRieszMobiusRenewal` (equations `(1)`, `(2)`, `(9)`, `(13)`), every equation of
this card that is not an explicitly cited parent is now Lean-certified.

Deliberately outside the Lean statement (cited parents):

- the Möbius divisor law `∑_{q|n} μ(q)log q = −Λ(n)` used to pass from `(8)` to `(9)`;
- the Stieltjes partial summation that produces the wavelet representation `(18)` itself;
- the corpus critical causal graph identity `(19)`.
