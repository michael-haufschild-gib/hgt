# Bounded homogeneous seam coupling has a rigid half-log trace

- **ID:** `suzuki-bounded-seam-half-log-rigidity`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (paper) / ASYMPTOTIC-INTEGRATION BRIDGE
- **Scientific status:** `[PROVED HERE] [PARENT THEORY] [NOT AN RH PROOF]`
- **Parent theory:** asymptotic integration for Banach-space linear ordinary differential
  equations with an integrable coefficient
- **Route:** Connes/CCM restricted-Weil form through Suzuki's completed screw operator
- **Statement:** A homogeneous boundary Volterra system with an arbitrary bounded pointwise
  Banach-space coupling has only two terminal behaviors: it vanishes identically, or it has a
  nonzero vector-valued half-logarithmic trace. Thus finite prime-seam adjacency and bounded
  polar--Gamma multiplication cannot create an inverse-log-flat non-`H1` branch. Any such branch
  must use the genuinely nonlocal logarithmic remainder.

## 1. Exact theorem

Let `X` be a real or complex Banach space. Fix `L_0>0`. Let

```text
T:[L_0,infinity)->B(X)
```

be strongly continuous and uniformly bounded:

```text
sup_(L>=L_0)||T(L)|| <= C.                                  (1)
```

Let `F:[L_0,infinity)->X` be continuous and suppose

```text
(2L I+T(L))F(L)=integral_(L_0)^L F(t)dt                     (2)
```

for every sufficiently large `L`.

`[PROVED]` There is a terminal point `L_1` and a vector `beta in X` such that

```text
lim_(L->infinity) sqrt(L)F(L)=beta.                         (3)
```

Moreover, exactly one of the following occurs:

```text
beta=0 and F(L)=0 for every L>=L_1;

beta!=0 and
  F(L)=beta/sqrt(L)+o(L^(-1/2)).                            (4)
```

In particular, no nonzero solution of `(2)` is flat at every inverse-logarithmic order.

## 2. Proof

Move `L_1` far enough that `(2)` holds and `2L_1>C`. Put

```text
Y(L)=integral_(L_0)^L F(t)dt,
A(L)=(2L I+T(L))^(-1).                                     (5)
```

The inverse in `(5)` exists by the Neumann series because `||T(L)/(2L)||<1`. Equation `(2)` and
the fundamental theorem of Bochner integration give

```text
Y'(L)=F(L)=A(L)Y(L).                                       (6)
```

The resolvent identity gives

```text
A(L)-(1/(2L))I=-(1/(2L))A(L)T(L).                          (7)
```

Since

```text
||A(L)|| <= 1/(2L-C),                                      (8)
```

we obtain the integrable bound

```text
||A(L)-(1/(2L))I||
 <= C/[2L(2L-C)]
 =O(L^(-2)).                                               (9)
```

Conjugate out the indicial power:

```text
U(L)=L^(-1/2)Y(L).                                         (10)
```

Differentiating `(10)` and using `(6)` yields the exact equation

```text
U'(L)=B(L)U(L),
B(L)=A(L)-(1/(2L))I.                                      (11)
```

By `(9)`,

```text
integral_(L_1)^infinity ||B(L)||dL < infinity.             (12)
```

Gronwall's inequality first makes `U` bounded. Equation `(11)` and `(12)` then make `U'`
integrable, so

```text
U_infinity=lim_(L->infinity)U(L)                           (13)
```

exists in `X`.

The limit cannot annihilate a nonzero state. Indeed, applying Gronwall backwards on `[L_1,M]`
gives

```text
||U(M)||
 >= ||U(L_1)||
    exp(-integral_(L_1)^M ||B(t)||dt).                     (14)
```

If `U(L_1)!=0`, then `(12)`--`(14)` imply `U_infinity!=0`. If `U(L_1)=0`, uniqueness for
`(11)` gives `U=0`, hence `Y=F=0`, on the terminal half-line.

Finally, `(6)` gives

```text
sqrt(L)F(L)=L A(L)U(L).                                    (15)
```

Equations `(7)`--`(9)` imply

```text
L A(L) -> (1/2)I                                           (16)
```

in operator norm. Therefore

```text
beta=(1/2)U_infinity.                                      (17)
```

Equations `(13)`--`(17)` prove `(3)`--`(4)`. `QED`

## 3. Sharpness and hostile tests

### Critical exponent

For `T=0`, equation `(2)` differentiates to

```text
2L F'(L)+F(L)=0,
```

so every nonzero solution is exactly `F(L)=c L^(-1/2)`. The exponent and the nonzero-trace
alternative are sharp.

### Vector coupling

No commutativity, self-adjointness, positivity, finite dimension, or diagonalizability of `T(L)`
is used. The theorem therefore includes finite oriented prime-seam adjacency on any Banach
carrier, including nonnormal and aperture-dependent bounded matrices.

### Why bounded pointwise forcing is harmless

Any homogeneous lower-order term `S(L)F(L)` with uniformly bounded `S(L)` can be absorbed into
`T(L)`. Such a term changes the trace vector but cannot create an intermediate flat scale.

### Exact kill boundary

The theorem does **not** cover a nonlocal term

```text
(R F)(L)
 =integral_0^infinity [F(L)-F(L+s)]/(exp(s)-1)ds
  +integral_0^L [F(L)-F(L-s)]/(exp(s)-1)ds.                (18)
```

There is no bounded pointwise operator `S(L)` satisfying `(R F)(L)=S(L)F(L)` uniformly over
functions `F`: one may have `F(L)=0` while neighboring values are nonzero. Replacing `(18)` by a
pointwise multiplier would be false and would constitute theorem theatre.

## 4. Exact Route-O consequence

At fixed aperture, Suzuki's visible prime translations produce a finite weighted adjacency:

```text
||T_prime,a||
 <= 2 sum_(n<=exp(2a)) Lambda(n)/sqrt(n) < infinity.        (19)
```

The smooth polar--Gamma multiplication block is bounded as well. Therefore these source pieces,
even acting jointly on a vector-valued seam carrier, cannot support a nonzero inverse-log-flat
homogeneous boundary cycle.

The source-specific scale-gap gate is reduced to one exact question:

```text
Does the nonlocal remainder `(18)`, after the completed Suzuki seam lift,
become an integrable perturbation of equation `(11)`?       (20)
```

If `(20)` is proved, the same asymptotic-integration argument gives a two-ended half-log trace for
every completed zero mode. Trace zero then forces terminal vanishing on every seam component;
unique continuation would place the mode in the regular `H1_0` branch.

Here “integrable perturbation” must be proved on the actual completed solution class. The
high-frequency part of `(18)` is logarithmic and is not uniformly lower order on arbitrary
functions. A proof restricted to a pre-assumed log-conormal class would leave a nonconormal
boundary-frequency escape and would not close the Suzuki source theorem.

This does not close either remaining source channel:

```text
CORONA: rule out a nonzero two-ended half-log trace state;
REGULAR: prove raw Evans Gram positivity for every aperture. (21)
```

It closes only the bounded-coupling part of the no-intermediate-scale problem.

## 5. Novelty and formalization decision

The proof is standard Banach-space asymptotic integration after the exact conjugation
`Y -> L^(-1/2)Y`. Its Route-O value is the sharp attribution of possible intermediate behavior:
finite prime adjacency and bounded polar--Gamma multiplication are innocent; the nonlocal
logarithmic remainder is the only surviving scale-gap mechanism.

This is parent theory, not claimed new scientific knowledge. The formal tree still lacks the
literal logarithmic Dirichlet remainder and completed Suzuki seam carrier, so `(20)` is untouched by
what follows. What is formalized below is not the generic statement "`U'=B U` with `B in L1` has a
limit": it is the exact system `(2)` with its bounded operator coupling, from which the conjugated
equation `(11)`, the integrable bound `(9)`, the trace `(3)`, and the terminal dichotomy `(4)` are
derived, together with an explicit scalar solution showing the nonzero-trace alternative is
realized.  Formalization becomes source-bearing for `(20)` only after the exact remainder lift
supplies the hypotheses of `(11)`--`(12)`.

Comparison sources include the classical Levinson asymptotic-integration line and its modern
Banach-space extensions; see P. N. Nesterov, *Asymptotic integration of certain differential
equations in Banach space*, Model. Anal. Inform. Sist. 24 (2017), 596--614, and G. Cotti,
D. Guzzetti, and D. Masoero, *Asymptotic solutions for linear ODEs with not-necessarily
meromorphic coefficients*, J. Differential Equations (2025). The elementary `L1` perturbation
proved above is strictly simpler than those parent results.

## 6. Lean formalization

Module: `formal/GaloisForLFunctions/HTGeometry/BoundedSeamHalfLogRigidity.lean`.

The hypotheses `(1)`--`(2)` are packaged as the structure `HTGeometry.BoundedSeamData`: a Banach
carrier `X`, a base `L₀ > 0`, an onset beyond which `(2)` holds, a uniform operator bound `C`, a
continuous profile `F`, and the equation `(2L) • F L + T L (F L) = ∫_{L₀}^L F`.  Neither
commutativity, self-adjointness, positivity, finite dimension, diagonalizability *nor even strong
continuity* of `T` is used: only the uniform bound enters the proof.

| Card statement | Lean declaration |
|---|---|
| `Y' = F` and the conjugation `(10)` | `primitive`, `halfLog`, `hasDerivAt_primitive` |
| the exact conjugated equation `(11)` | `hasDerivAt_halfLog` |
| the integrable bound `(9)` | `norm_halfLog_deriv_le`, `perturbationRate_le_majorant`, `integral_perturbationMajorant_le` |
| boundedness of `U` (Gronwall step) | `norm_halfLog_le_two_mul` |
| existence of the limit `(13)` | `integrableOn_halfLogDeriv`, `halfLogLimit`, `tendsto_halfLog` |
| the backward bound `(14)` | `norm_halfLog_sub_le`, `norm_halfLog_threshold_le`, `norm_halfLogLimit_ge` |
| terminal vanishing when the trace is zero | `halfLog_eq_zero_of_threshold`, `primitive_eq_zero_of_threshold`, `profile_eq_zero_of_threshold` |
| `(15)`--`(17)`, the trace `(3)` | `sqrt_smul_profile_eq`, `norm_traceRemainder_le`, `tendsto_traceRemainder`, `tendsto_sqrt_smul_profile` |
| the dichotomy `(4)` | `halfLog_trace_dichotomy` |
| sharpness of the nonzero-trace alternative | `sharpProfile`, `sharpSeam`, `tendsto_sharpSeam_trace` |

The Gronwall step of §2 is replaced by a maximum-point bootstrap on `[L₁,L]`: the terminal threshold
`threshold = max (L₀+1) (max onset (2C+1))` makes the tail mass of the majorant `C/(2t²)` at most
`1/4`, which bounds `‖U‖` by `2‖U(L₁)‖` and simultaneously gives the two-sided conclusion.  The
sharpness witness is the zero-coupling profile `t^{-1/2} + 4 max(0, 2-t)` on `[1,∞)` with onset `2`;
its half-logarithmic trace is `1`, so the theorem is not vacuous on the nonzero branch.

`#print axioms` reports `[propext, Classical.choice, Quot.sound]` for every declaration above.

## Gates

- [x] exact bounded-coupling Volterra system stated
- [x] half-log conjugation derived
- [x] integrable operator perturbation proved
- [x] nonzero limiting trace proved by backward Gronwall
- [x] sharp scalar model checked
- [x] finite prime adjacency included without commutativity assumptions
- [x] nonlocal-remainder limitation stated
- [x] nonconormal high-frequency escape retained as a kill condition
- [x] 2 -> 3: formalized; see `## 6. Lean formalization`
- [ ] prove the exact Suzuki remainder lift `(20)`
- [ ] deduce trace-zero terminal vanishing for the completed source
- [ ] prove corona no-return
- [ ] prove raw Evans positivity
- [ ] RH
