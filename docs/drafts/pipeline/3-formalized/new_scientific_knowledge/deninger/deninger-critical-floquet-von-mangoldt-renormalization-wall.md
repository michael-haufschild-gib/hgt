# Critical Floquet renormalization and the von Mangoldt wall

- **ID:** `deninger-critical-floquet-von-mangoldt-renormalization-wall`
- **Stage:** 3-formalized
- **Type:** SOURCE TRACE IDENTIFICATION / SHARP POSITIVITY NO-GO / FRONTIER REORIENTATION
- **Labels:**
  - `DAC_DENINGER_FLOQUET_ADIABATIC_RELATIVE_MONODROMY`;
  - `DAC_DENINGER_PRIME_CIRCLE_AUTOCORRELATION_UNFOLDING`;
  - `DAC_DENINGER_CRITICAL_FLOQUET_VON_MANGOLDT_CURRENT`;
  - `DAC_DENINGER_DIAGONAL_FLOQUET_RENORMALIZATION_SIGN_WALL`.
- **Parent:** Route L in `rh-current-frontier-map.md`
- **Inputs:**
  - `DAC_DENINGER_HALF_DENSITY_FLOQUET_EXACT_SEQUENCE`;
  - `DAC_DENINGER_ALL_PRIME_FLOQUET_COCHAIN_HODGE_ENERGY`;
  - `DAC_DENINGER_MERTENS_ADIABATIC_CORNER`.
- **Lean status:** formalized; see *Lean status* below.

## 1. Result

The summable all-prime Floquet energy

\[
 \sum_p p^{-2}\|\operatorname{Per}_{p,1/2}h\|_{p,1/2}^2
\]

is positive and weight one, but its prime weights are too small to retain the logarithmic Euler
current.  The first unsuppressed prime-circle sum does retain that current.  After the unique
diagonal subtraction forced by large prime circles, its off-diagonal part is exactly the
von Mangoldt prime-power autocorrelation.

This does not produce the missing positive Hodge form.  The same renormalized form is necessarily
indefinite.  In fact one compactly supported two-bump source gives the positive sign and the
matching Floquet Euler coboundary gives the negative sign.  The obstruction holds for every
nonnegative diagonal prime weighting which sees the prime (2), not only for the von Mangoldt
weight.

Consequently the corrected Tate--Floquet interface cannot be closed by changing the scalar weights
or by subtracting the prime-circle vacuum.  The prime circles supply an exact source coordinate for
the arithmetic current.  Positivity must come from a non-diagonal Gamma/Poisson Green--Stokes
coupling formed before scalar diagonal renormalization.

## 2. Relative monodromy is the adiabatic kernel

Put (L_p=\log p), and for \(\alpha\in\mathbb R\) define

\[
 \operatorname{Per}_{p,\alpha}h(t)
 =\sum_{j\in\mathbb Z}p^{\alpha j}h(t+jL_p),
 \qquad
 F(t+L_p)=p^{-\alpha}F(t).
\tag{1}
\]

The monodromy of the exponent \(\alpha=1/2+u\), relative to the half-density exponent, is

\[
 {p^{-(1/2+u)}\over p^{-1/2}}
 =p^{-u}
 =\exp\!\left(-{u\over\varepsilon_p}\right),
 \qquad \varepsilon_p=(\log p)^{-1}.
\tag{2}
\]

Reflection \(\alpha\mapsto1-\alpha\) is exactly \(u\mapsto-u\).  Moreover

\[
 \left.{d^k\over du^k}p^{-u}\right|_{u=0}
 =(-\log p)^k.
\tag{3}
\]

Thus the half-density Floquet family, the finite adiabatic front face, and the complete prime-log
jet are three restrictions of the same relative monodromy.  Equations `(2)`--`(3)` are an exact
bridge, not the new positivity theorem.

## 3. Prime-circle norm unfolding

For (u\in\mathscr S_{\exp}(\mathbb R)), define ordinary periodization and autocorrelation by

\[
 P_pu(t)=\sum_{j\in\mathbb Z}u(t+jL_p),
 \qquad
 C_u(a)=\int_{\mathbb R}u(t)\overline{u(t+a)}\,dt,
\tag{4}
\]

and put

\[
 I_p(u)=\int_0^{L_p}|P_pu(t)|^2\,dt.
\tag{5}
\]

If (u(t)=e^{t/2}h(t)), the half-density trivialization gives

\[
 I_p(u)=\|\operatorname{Per}_{p,1/2}h\|_{p,1/2}^2.
\tag{6}
\]

`[PROVED HERE] [DAC_DENINGER_PRIME_CIRCLE_AUTOCORRELATION_UNFOLDING]`

For every prime (p),

\[
 \boxed{
 I_p(u)=\sum_{m\in\mathbb Z}C_u(mL_p).
 }
\tag{7}
\]

The series is absolutely convergent.  If (u) is compactly supported in an interval of length
strictly less than (L_p), then

\[
 I_p(u)=C_u(0)=\|u\|_2^2.
\tag{8}
\]

### Proof

Absolute convergence follows from faster-than-every-exponential decay of (u) and its translates.
Expanding `(5)`, set (x=t+jL_p) and (m=k-j).  The (j)-translated fundamental intervals tile
the real line, so

\[
\begin{aligned}
 I_p(u)
 &=\sum_{j,k\in\mathbb Z}
   \int_0^{L_p}u(t+jL_p)\overline{u(t+kL_p)}\,dt\\
 &=\sum_{m\in\mathbb Z}
   \int_{\mathbb R}u(x)\overline{u(x+mL_p)}\,dx,
\end{aligned}
\]

which is `(7)`.  Under the support hypothesis, distinct (L_p)-translates do not overlap, so all
terms with (m\ne0) vanish.  This proves `(8)`.

## 4. Exact von Mangoldt current

The large-prime value `(8)` forces the diagonal counterterm (\|u\|_2^2\).  Define the critical
off-diagonal Floquet form

\[
 \mathcal Q_{\mathrm{Fl}}^{\mathrm{crit}}(u)
 =\sum_p(\log p)\bigl(I_p(u)-\|u\|_2^2\bigr).
\tag{9}
\]

For compactly supported (u), only finitely many primes contribute.  More generally, if

\[
 |C_u(a)|\le B_Ae^{-A|a|}
\quad\text{for some }A>1,
\tag{10}
\]

then `(9)` converges absolutely, since

\[
 \sum_p(\log p)\sum_{m\ge1}|C_u(m\log p)|
 \le B_A\sum_p{(\log p)p^{-A}\over1-p^{-A}}<\infty.
\tag{11}
\]

`[PROVED HERE] [DAC_DENINGER_CRITICAL_FLOQUET_VON_MANGOLDT_CURRENT]`

Under `(10)`,

\[
 \boxed{
 \mathcal Q_{\mathrm{Fl}}^{\mathrm{crit}}(u)
 =\sum_{n\ge2}\Lambda(n)
   \bigl(C_u(\log n)+C_u(-\log n)\bigr).
 }
\tag{12}
\]

In particular `(9)` is real-valued and is exactly the centered prime-power autocorrelation current.

### Proof

Subtract the (m=0) term in `(7)` and split the remaining sum into positive and negative (m):

\[
 \mathcal Q_{\mathrm{Fl}}^{\mathrm{crit}}(u)
 =\sum_p\sum_{m\ge1}(\log p)
   \bigl(C_u(m\log p)+C_u(-m\log p)\bigr).
\]

Absolute convergence from `(11)` permits reindexing by (n=p^m).  Since

\[
 \Lambda(n)=
 \begin{cases}
 \log p,&n=p^m,\ m\ge1,\\
 0,&\text{otherwise},
 \end{cases}
\]

this is `(12)`.  Finally (C_u(-a)=\overline{C_u(a)}), proving reality.

Equation `(12)` is the precise positive survivor of critical prime-circle renormalization.  It
recovers the prime-power current before the archimedean Gamma/polar completion.  It does not assert
positivity of that current.

## 5. Universal sign wall

Let (a_p\ge0) be arbitrary prime weights with (a_2>0), and define whenever meaningful

\[
 \mathcal Q_a(u)=\sum_p a_p\bigl(I_p(u)-\|u\|_2^2\bigr).
\tag{13}
\]

`[PROVED HERE] [DAC_DENINGER_DIAGONAL_FLOQUET_RENORMALIZATION_SIGN_WALL]`

There exist nonzero (u_+,u_-\in C_c^\infty(\mathbb R)) such that

\[
 \mathcal Q_a(u_+)=a_2\|u_+\|_2^2>0,
 \qquad
 \mathcal Q_a(u_-)=-a_2\|u_-\|_2^2<0.
\tag{14}
\]

For the half-density cochains (h_\pm(t)=e^{-t/2}u_\pm(t)), the negative witness is a literal
matching Floquet Euler coboundary:

\[
 h_-=D_{2,1/2}g,
 \qquad
 D_{2,1/2}=1-2^{1/2}\tau_{\log2},
\tag{15}
\]

for one (g\in C_c^\infty(\mathbb R)\subset H_-).

### Proof

Choose (0\ne v\in C_c^\infty(\mathbb R)) whose support has diameter

\[
 \delta<\min(\log2,\log3-\log2).
\tag{16}
\]

Write (L=\log2), let ((\tau_Lv)(t)=v(t+L)), and set

\[
 u_+=v+\tau_Lv,
 \qquad
 u_-=v-\tau_Lv.
\tag{17}
\]

The two supports are disjoint, hence

\[
 \|u_+\|_2^2=\|u_-\|_2^2=2\|v\|_2^2.
\tag{18}
\]

Periodization on the (2)-circle satisfies (P_2\tau_Lv=P_2v).  Therefore

\[
 P_2u_+=2P_2v,
 \qquad
 P_2u_-=0.
\]

Since the support of (v) has diameter less than (L), `(8)` gives

\[
 I_2(u_+)=4\|v\|_2^2=2\|u_+\|_2^2,
 \qquad
 I_2(u_-)=0.
\tag{19}
\]

Both (u_+) and (u_-) are supported in an interval of length at most (L+\delta<\log3\).
Consequently `(8)` gives

\[
 I_p(u_\pm)=\|u_\pm\|_2^2
 \qquad(p\ge3).
\tag{20}
\]

Only the prime (2) survives in `(13)`.  Equations `(19)`--`(20)` prove `(14)`.

Finally put (g(t)=e^{-t/2}v(t)).  Since

\[
 e^{-t/2}(\tau_Lv)(t)=2^{1/2}(\tau_Lg)(t),
\]

equation `(17)` gives `(15)`.

## 6. Conjecture loop disposition

1. **Conjecture:** the half-density Floquet family is unrelated to the older adiabatic corner.
   **Failed by `(2)`--`(3)`.** Its relative monodromy is exactly the adiabatic kernel and its normal
   derivatives are the prime-log jet.
2. **Conjecture:** replacing the summable (p^{-2}) weights by the logarithmic Euler weight may
   produce the missing arithmetic Hodge form. **Half survives.** Unfolding produces the exact
   von Mangoldt current `(12)`.
3. **Conjecture:** diagonal vacuum subtraction preserves positivity. **Failed sharply by `(14)`.**
   The failure already occurs on one two-bump compact source and for every nonnegative prime
   weighting seeing (p=2).
4. **Conjecture:** matching Floquet depletion could remove only an inessential negative direction.
   **Failed by `(15)`.** The negative direction is the exact matching Euler coboundary which killed
   the admitted sector in the earlier leakage dichotomy.
5. **Survivor:** prime-circle geometry is an exact pre-Gamma realization of the von Mangoldt
   current.  Any positive Route-L form must couple that current to Gamma/polar and Poisson data
   non-diagonally before scalarization.  Reweighting, diagonal subtraction, or another compact
   circle norm cannot do it.

## 7. Route-L consequence

The corrected Tate--Floquet Poisson descent remains a valid target interface, but it is not the
source producer.  Three surrounding pieces are now exact:

\[
\begin{array}{c}
\text{summable Floquet trace}\quad\longrightarrow\quad
\text{positive weight-one cochain energy, but wrong boundary},\\[2mm]
\text{critical Floquet trace}\quad\longrightarrow\quad
\text{exact von Mangoldt current, but indefinite after forced subtraction},\\[2mm]
\text{actual Gamma/Calderón Green transport}\quad\longrightarrow\quad
\text{correct boundary coefficient, but nonselective without source annihilation}.
\end{array}
\tag{21}
\]

The first unproved operation is therefore a strict all-prime arithmetic gauge-defect sewing, or an
equivalent non-diagonal source differential, whose Green--Stokes identity couples the second and
third lines of `(21)` before Hermitian squaring.  It must annihilate literal Poisson boundaries in
the nuclear source topology and then induce the corrected Floquet interface.  Constructing only a
singular target, local divisor current, compact trace, or renormalized scalar form does not reach
this operation.

## 8. Hostile audit

- **Unconditional.** Proofs use periodization, support separation, exponential decay, and the
  definition of (\Lambda).  No zero, divisor, RH premise, positivity criterion, or numerical input
  occurs.
- **Not a disguised explicit-formula proof.** Only the prime-power autocorrelation current is
  identified.  Gamma/polar completion and its sign are not asserted.
- **Not positivity theatre.** The exact positive and negative compact witnesses are exhibited.
- **No topology substitution.** Witnesses lie in (C_c^\infty\subset H_-), before every Hilbert
  completion.
- **No finite-prime overclaim.** One prime suffices only for the universal sign obstruction.  The
  arithmetic survivor `(12)` uses all prime powers.
- **No Lean activity.** Lean corpus was inspected read-only.  No Lean file, build, or process was
  used for this theorem.

## 9. Novelty boundary

Periodization/autocorrelation unfolding and reindexing prime powers by (\Lambda) are classical
separately.  The potentially new content is their exact combination with the forced half-density
Floquet source, plus the universal two-bump sign classification `(14)` and its identification
`(15)` with matching Floquet Euler depletion.  Repository-wide search found no prior theorem making
this combination.  Primary-source searches through Deninger/Meyer, co-Poisson/Sonin work, current
semi-local scaling-Hamiltonian work, and the 2025--2026 spectral-triple and theta spectral papers
found periodic-orbit trace formulas and RH-equivalent positive forms, but not this exact diagonal
renormalization wall.

Novelty is claimed only for the combined Route-L classification and exact frontier consequence,
not for the component harmonic-analysis identities.

## References

- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann zeta function*,
  arXiv:math/0412277.
- Christopher Deninger, *Dynamical systems for arithmetic schemes*, arXiv:1807.06400.
- Alain Connes and Caterina Consani, *The scaling Hamiltonian*, arXiv:1910.14368.
- Alain Connes, Caterina Consani, and Henri Moscovici, *Zeta Spectral Triples*,
  arXiv:2511.22755.
- Haakan Hedenmalm, *Spectral interpretation of Riemann zeta zeros*, arXiv:2606.17494.

## Lean status

`formal/GaloisForLFunctions/RHTower/DeningerCriticalFloquetVonMangoldtWall.lean`,
`DeningerCriticalFloquetCrossCurrent.lean` and
`DeningerFloquetDiagonalSignWall.lean`.  Axiom audit for every declaration:
`propext, Classical.choice, Quot.sound`.

### Done

- **§2, `(2)`--`(4)`: relative monodromy is the adiabatic kernel.**
  `deningerFloquetRelativeMonodromy`, **`deningerFloquetRelativeMonodromy_eq_adiabatic`**,
  `deningerFloquetRelativeMonodromy_eq_exp_neg_log`, `deningerFloquetRelativeMonodromy_neg`, and
  `iteratedDeriv_deningerFloquetRelativeMonodromyComplex_zero`.
- **§3, `(5)`--`(8)`: prime-circle norm unfolding.**  `deningerPrimeCirclePeriodization`,
  `deningerMeyerStrongLogAutocorrelation`, and
  **`deningerPrimeCircleEnergy_eq_tsum_autocorrelation`**: the literal circle norm is the
  absolutely convergent autocorrelation lattice of the all-weight Meyer source.
- **§4, `(9)`--`(12)`: the exact von Mangoldt current.**
  `tsum_prime_iterate_eq_deningerPrimePower_vonMangoldt` (the purely arithmetic reindexing),
  `deningerPrimeCircleEnergy_sub_autocorrelation_zero`, and
  **`deningerCriticalFloquetForm_eq_vonMangoldtAutocorrelationCurrent`**, whose analytic premise is
  discharged in `DeningerCriticalFloquetCrossCurrent.lean` by
  `exists_deningerAutocorrelationExpBound`, giving the premise-free
  **`deningerCriticalFloquetForm_eq_vonMangoldtAutocorrelationCurrent_unconditional`**.
- **§5, `(13)`--`(15)`: the universal sign wall.**  `DeningerFloquetDiagonalSignWall.lean`.  With a
  source supported in an interval of diameter less than `log 3 - log 2`, the two-bump witnesses
  `deningerFloquetTwoBumpPlus/Minus` at spacing `log 2` have support of diameter less than `log 3`
  (`deningerFloquetTwoBump_support`), so every prime circle of circumference at least `log 3`
  contributes exactly zero to the renormalized diagonal form
  (**`deningerFloquetDiagonalDefect_of_three_le`**), while the circle of `2` contributes
  `+‖u₊‖²` and `-‖u₋‖²` respectively (**`deningerFloquetDiagonalDefect_two`**).  The mass is
  strictly positive for a nonzero source
  (`deningerMeyerStrongLogAutocorrelation_zero_re_pos`).  Hence for every nonnegative prime
  weighting `a` with `a₂ > 0` the renormalized form satisfies `Q_a(u₊) = a₂‖u₊‖² > 0` and
  `Q_a(u₋) = -a₂‖u₋‖² < 0`, which is `(14)`.  Equation `(15)` — that the negative witness is a
  literal half-density Floquet Euler coboundary — is
  **`deningerFloquetTwoBumpMinus_eq_floquetDefect`**.
- The two card inputs are corpus-owned: `DAC_DENINGER_HALF_DENSITY_FLOQUET_EXACT_SEQUENCE` is
  `DeningerFloquetExactSequence.lean` and `DAC_DENINGER_ALL_PRIME_FLOQUET_COCHAIN_HODGE_ENERGY` is
  `DeningerHalfDensityFloquetEnergy.lean`.

## Gates

- [x] exact relative-monodromy/adiabatic identification
- [x] exact prime-circle autocorrelation unfolding
- [x] exact von Mangoldt reindexing and convergence
- [x] universal positive/negative compact witnesses
- [x] hostile novelty and circularity audit
- [x] Lean formalization: §2--§5 proved unconditionally (see *Lean status*)

## Log

- 2026-08-12 — Completed the Lean formalization: the pre-existing monodromy, autocorrelation and
  von Mangoldt layers were audited against the card, and the missing `(13)`--`(15)` sign wall was
  built.  Card moved to stage 3.
