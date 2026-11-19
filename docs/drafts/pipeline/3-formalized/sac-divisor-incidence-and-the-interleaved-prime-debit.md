# Divisor incidence, the interleaved prime debit, and the macroscopic cost barrier

- **ID:** sac-divisor-incidence-and-the-interleaved-prime-debit
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-1911/obstacles-summary.md` §2.5; `SignedArithmeticCorrespondences/TheFullWeilFormOnInterleavingDivisors.lean`; `HodgeTheoryOfAFixedPart/TheRiemannHypothesisIsExactEventualCombPositivity.lean`; `GreenCalculusOfThePrimeFreeWindow/TheFirstOverlapStepOfWeilsFormFailsForTheSignTwin.lean`
- **Statement:** Splitting `combFormW w S c = diagRealBudget S c - mixedPrimeDebitW w S c` shows that divisor incidence fails to pay its prime debit on unshifted prefixes `[1, N]` (`combForm [1, N] v_p → -∞`), while on late combs `S = Ioc N (N + 3KN)` (`K ≥ 1`) every linear combination `c = ∑_{t ∈ T} α_t v_{d_t, r_t}` of centered congruence indicators satisfies `combFormW w S c ≥ κ ∑_{n ∈ S} c(n)^2 - (C_{K, w, κ} / N)(∑_{t ∈ T} |α_t|)^2`, yielding uniform positivity and `B^2 ≤ A C` on the moving `√N` two-prime pilot and on the full unrestricted span `{v_p : p ≤ ⌊C_0 √N⌋}`; at the macroscopic cost threshold `(∑_{d=2}^{(1+3K)N} |α_d|)^2 ≤ C_K N ∑_{n ∈ S} c(n)^2`, centered divisibility indicators span every `c : S → ℝ`, `SelectiveArithmetic.liouvilleWeight` becomes strictly negative (`< -(1/2000) ∑_{n ∈ S} c(n)^2`), and paying `mixedPrimeDebit S c ≤ diagRealBudget S c` for `Λ` across all `K ≥ 1` is unconditionally equivalent to `RiemannHypothesis`.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean modules `ThePrimeDebitOfInterleavingSelfIntersections`, `DivisorIncidenceOnLateCombs`, `ControlledDivisibilityPositivityAndTheMacroscopicBarrier`, `lake --old env lean` green, axioms `propext`, `Classical.choice`, `Quot.sound`

## Lean
Namespace `GaloisForLFunctions.SignedArithmeticCorrespondences`:
- `SignedArithmeticCorrespondences/ThePrimeDebitOfInterleavingSelfIntersections.lean`:
  `diagRealBudget`, `mixedPrimeDebitW`, `mixedPrimeDebit`, `centeredResidue`, `centeredMultiple`,
  `combFormW_eq_diagRealBudget_sub_mixedPrimeDebitW`, `combForm_eq_diagRealBudget_sub_mixedPrimeDebit`,
  `mixedPrimeDebitW_le_diagRealBudget_iff`, `mixedPrimeDebit_le_diagRealBudget_iff`,
  `interleaved_self_budget_and_debit`, `abs_sum_centeredResidue_Ioc_le_one`,
  `abs_sum_centeredMultiple_Ioc_le_one`, `abs_sum_centeredResidue_harmonic_Ioc_le`,
  `abs_sum_jetKernel_centeredResidue_erase_le`, `unshifted_prefix_two_debit_gt_budget`,
  `tendsto_combForm_Icc_centeredMultiple_atBot`, `lateComb_mixedPrimeDebit_pos`.
- `SignedArithmeticCorrespondences/DivisorIncidenceOnLateCombs.lean`:
  `poleTerm`, `diagTerm`, `jetTerm`, `contactTerm`, `formBilinW`, `combSlice`,
  `formBilinW_eq_four_parts`, `formBilinW_self`, `formBilinW_vonMangoldt`, `formBilinW_comm`,
  `combFormW_two_linear_comb`, `combFormW_two_span_nonneg_of_cauchy_schwarz`,
  `contactTerm_lateComb_eq`, `contactTerm_coprime_eq_slice_sum`,
  `combFormW_liouville_sub_combForm_coprime`, `combForm_lt_combFormW_liouville_coprime`,
  `abs_sum_centeredMultiple_shift_le`, `abs_sum_centeredMultiple_shift_left_le`,
  `abs_sum_centeredMultiple_mul_Ioc_le`, `abs_formBilinW_distinct_primes_le`,
  `sum_centeredMultiple_sq_Ioc_ge`, `sum_centeredMultiple_sq_Ioc_le`.
- `SignedArithmeticCorrespondences/ControlledDivisibilityPositivityAndTheMacroscopicBarrier.lean`:
  `combFormW_congr`, `combFormW_of_subset`, `abs_contactTerm_lateComb_self_le`,
  `eventually_combFormW_controlled_residue_ge`, `eventually_mixedPrimeDebitW_le_diagRealBudget_of_cost`,
  `eventually_pilot_pos_and_cauchy_schwarz`, `eventually_pilot_vonMangoldt_pos_and_cauchy_schwarz`,
  `eventually_pilot_liouville_pos_and_cauchy_schwarz`, `card_primesLE_le`,
  `eventually_combFormW_primeSpan_sqrt_ge`, `sum_moebius_div_Icc_ne_zero`,
  `exists_centeredMultiple_comb_representation`, `eventually_exists_liouville_centeredMultiple_neg`,
  `riemannHypothesis_iff_centeredMultiple_debit_le_budget`,
  `riemannHypothesis_iff_macroscopic_cost_centeredMultiple_debit_le_budget`.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Paper proof
1. **Budget–debit decomposition and failure on unshifted prefixes.** For finite $S\subseteq\mathbb N_{>0}$, contact weight $w:\mathbb N\to\mathbb R$, and $c:S\to\mathbb R$, set $B_{\mathrm{dr}}(S,c)=\sum_{n\in S}c_n^2\log(n/(2\pi))-\sum_{n\in S}\sum_{m\in S\setminus\{n\}}c_m c_n\,\mathrm{jetKernel}(m,n)$ and $D_w(S,c)=\sum_{n\in S}\sum_{m\in S\setminus\{n\}}c_m c_n\,\mathrm{contactW}(w,m,n)-2(\sum_{n\in S}c_n/n)(\sum_{n\in S}c_n)$, so $\mathrm{combFormW}(w,S,c)=B_{\mathrm{dr}}(S,c)-D_w(S,c)$. When $S=[1,N]$ and $u=\mathrm{upperDivisor}(N,a)$, `interleaved_finite_part` identifies $B_{\mathrm{dr}}([1,N],u)=\sum_{n=1}^N u_n^2\log(n/(2\pi))-\tfrac12\int_0^1 J_{a,a}(x)\,dx$ and $D_\Lambda([1,N],u)=\sum_{k=0}^N c_k^{a,a}(\psi(k)-k)-2F_{u,a}$. On $[1,2]$, $u_2(n)=2\mathbf 1_{2\mid n}-1$ already satisfies $B_{\mathrm{dr}}([1,2],u_2)<D_\Lambda([1,2],u_2)$. For every prime $p$, contacts of ratio coprime to $p$ preserve $v_p(n)=\mathbf 1_{p\mid n}-1/p$, so monotonicity of $\psi$ across $p$-periods and $\sum_{j\le M}\psi(M/j)=\log(M!)$ give $D_\Lambda([1,N],v_p)\ge 2(1-1/p)\log(\lfloor N/p\rfloor!)-O_p(N)$ while $B_{\mathrm{dr}}([1,N],v_p)\le (1-1/p)\lfloor N/p\rfloor\log(N/(2\pi))+O_p(N)$, forcing $\mathrm{combForm}([1,N],v_p)\to -\infty$ at rate $-\frac1p(1-\frac1p)N\log N$. Even on $S=(N,N+3KN]$, $D_\Lambda(S,v_p)>0$ for $3K<p\le KN$, so the isolated prime-and-boundary term is strictly negative before spending $B_{\mathrm{dr}}$.
2. **Three divisibility counts on late combs.** Fix $K\ge 1$, $S=(N,N+3KN]$, and $S_r=(N,\lfloor(1+3K)N/r\rfloor]$.
   - *Coprime contact bijection:* For $d_1,d_2$ coprime to $\{2,\dots,3K\}$, $m\mapsto rm$ preserves divisibility on $S_r$, giving $\sum_{m\ne n\in S}v_{d_1}(m)v_{d_2}(n)\,\mathrm{contactW}(w,m,n)=2\sum_{r=2}^{3K}w(r)\sum_{m\in S_r}v_{d_1}(m)v_{d_2}(m)$. Replacing $\Lambda$ by $\lambda\Lambda$ leaves pole, real-jet, and diagonal terms unchanged and flips only nonsquare ratios $2\le r\le 3K$, giving $\mathrm{combFormW}(\lambda\Lambda,S,v_d)-\mathrm{combForm}(S,v_d)=4\sum_{2\le r\le 3K,\,\neg\mathrm{IsSquare}(r)}\Lambda(r)\sum_{m\in S_r}v_d(m)^2>0$ for $3K<d\le KN$.
   - *CRT shifted-incidence cancellation:* For coprime $d_1,d_2\ge 1$ and $h\in\mathbb N$, Chinese Remainder incidence cancels $(b-a)/(d_1 d_2)$ in $\sum_{m\in(a,b]}v_{d_1}(m)v_{d_2}(m+h)$, leaving $|\sum_{m\in(a,b]}v_{d_1}(m)v_{d_2}(m+h)|\le 2$; direct and reversed Abel summation give $|\mathrm{formBilinW}(w,S,v_p,v_q)|\le C_{K,w}(1+\log N)$ for all distinct primes $p\ne q$.
   - *Complete-period variance:* Partitioning $(a,b]$ into $\lfloor(b-a)/d\rfloor$ periods gives $\sum_{n\in(a,b]}v_d(n)^2\ge \lfloor(b-a)/d\rfloor(1-1/d)$ and $|\sum_{n\in(a,b]}v_{d,r}(n)|\le 1$.
3. **Controlled-cost positivity producer, two-prime pilot, and $\sqrt N$ prime spans.** Orthogonal block reduction, step-packet matrix boundedness, $|\sum_{n\in(a,b]}v_{d,r}(n)|\le 1$, and the bounded-ratio Schur bound $|\mathrm{contactTerm}(w-\Lambda,S,c,c)|\le 2(\sum_{r=2}^{3K}|w(r)-\Lambda(r)|)\sum_{n\in S}c_n^2$ give $\mathrm{combFormW}(w,S,c)\ge\kappa\sum_{n\in S}c_n^2-(C_{K,w,\kappa}/N)(\sum_{t\in T}|\alpha_t|)^2$ eventually for all $c=\sum_{t\in T}\alpha_t v_{d_t,r_t}$. Combining with $|\langle v_p,v_q\rangle_S|\le 2$ and $\pi(X)\le\sqrt X+(2\log 4)X/\log X$ yields both the moving-prime pilot ($A_w,C_w\ge(K/c_2)\sqrt N>0$ and $B_w^2\le A_w C_w$ for $p\ne q\le\lfloor c_2\sqrt N\rfloor$) and unconditional eventual positivity on the unrestricted span $\{v_p:p\le\lfloor C_0\sqrt N\rfloor\}$ for any $w$ (including $\Lambda$ and $\lambda\Lambda$).
4. **Macroscopic cost barrier, Liouville refutation, and RH equivalence.** Upper-triangular Möbius inversion on $S=(N,QN]$ expresses every point mass modulo $\mathbf 1_S$, while $\sum_{t=1}^Q\mu(t)v_{tN}(n)=-N^{-1}(\sum_{t=1}^Q\mu(t)/t)\mathbf 1_S(n)$ on $S$. By Bertrand's postulate a prime $p\in(Q/2,Q]$ has unique multiple $p$ in $[1,Q]$, so $p$-adic valuation forces $\sum_{t=1}^Q\mu(t)/t\ne 0$. Hence every $c:S\to\mathbb R$ has a representation $c=\sum_{d=2}^{QN}\alpha_d v_d$ on $S$ with $(\sum_{d=2}^{QN}|\alpha_d|)^2\le C_Q N\sum_{n\in S}c_n^2$. At $Q=1+3K$, embedding the first-step sign-twin failure window into $S$ gives macroscopic-cost combinations with $\mathrm{combFormW}(\lambda\Lambda,S,c)<-(1/2000)\sum_{n\in S}c_n^2<0$, whereas eventual payment $D_\Lambda(S,c)\le B_{\mathrm{dr}}(S,c)$ across macroscopic-cost centered-divisibility combinations for all $K\ge 1$ is unconditionally equivalent to `RiemannHypothesis`.

## No-go closure (unshifted-prefix and contact-sign-blind sub-routes)
- **Exact killing theorem/mechanism:** (a) On unshifted prefixes `[1, N]`, contacts up to ratio `N/m` accumulate `2(1 - 1/p) log(⌊N/p⌋!)` against only `(1 - 1/p)⌊N/p⌋ log(N/(2π))` diagonal budget (`unshifted_prefix_two_debit_gt_budget`, `tendsto_combForm_Icc_centeredMultiple_atBot`). (b) On late combs `S = Ioc N (N + 3KN)` at macroscopic cost `(∑ |α_d|)^2 ≤ C_K N ‖c‖_2^2`, `{v_d : 2 ≤ d ≤ (1+3K)N}` spans all of `ℝ^S` (`exists_centeredMultiple_comb_representation`) and `SelectiveArithmetic.liouvilleWeight` becomes strictly negative (`eventually_exists_liouville_centeredMultiple_neg`), killing any contact-sign-blind divisibility positivity route past the `N^{-1}(∑ |α_t|)^2` threshold.
- **Strongest positive survivor:** The sharp universal sub-macroscopic positivity inequality `combFormW w S c ≥ κ ∑_{n ∈ S} c(n)^2 - (C_{K, w, κ} / N)(∑_{t ∈ T} |α_t|)^2` (`eventually_combFormW_controlled_residue_ge`), unconditional positivity on the moving `√N` two-prime pilot (`eventually_pilot_pos_and_cauchy_schwarz`) and the entire unrestricted `√N`-prime span (`eventually_combFormW_primeSpan_sqrt_ge`), and the exact macroscopic-cost centered-divisibility equivalence to `RiemannHypothesis` (`riemannHypothesis_iff_macroscopic_cost_centeredMultiple_debit_le_budget`).
- **New insight:** Centered divisibility indicators are not a thin special family on `(N, (1+3K)N]` — by Bertrand's postulate and upper-triangular Möbius inversion they form a complete spanning dictionary at `ℓ^1` cost `(∑ |α_d|)^2 asymp_K N ‖c‖_2^2`, locating the exact boundary between universal incidence positivity (`o(N ‖c‖_2^2)`) and genuine `Λ`-vs-`λΛ` sign sensitivity (`Θ_K(N ‖c‖_2^2)`).
- **Status:** Complete paper proof and unconditional Lean formalization across `ThePrimeDebitOfInterleavingSelfIntersections.lean`, `DivisorIncidenceOnLateCombs.lean`, and `ControlledDivisibilityPositivityAndTheMacroscopicBarrier.lean`.

## Log
- 2026-11-19 — created; proved; formalized.
