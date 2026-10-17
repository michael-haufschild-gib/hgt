### 1. Why EWU Is Strictly Stronger Than OWU (What Is Already Closed `[L]`)

In OWU, we are fighting on two fronts at once (the negative pole square in the blind minimum *and* the inability of odd tests to kill the real cut). **EWU has already eliminated both:**

1. **Uniqueness, Cut Removal, and Pole Completion Are 100% Formalized:**
   - By [`weilPositiveFull_of_weilPositiveEvenAt`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorFullPositivity.lean#L657-L660) and [`source_unique_of_weilPositiveEvenAt`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorPoleWeightUniqueness.lean#L209-L211), even positivity at *any* finite pole weight $\beta \in \mathbb{R}$ unconditionally forces $\lambda = \Lambda$ on $n \ge 2$ and `RiemannHypothesis`.
   - Even better, [`EvenSectorPolarCompletion.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorPolarCompletion.lean) proves [`weilPositiveFull_of_weilPositiveEvenPolar`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorPolarCompletion.lean#L127-L129) and [`evenPolar_sourceCone_eq_full_sourceCone`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorPolarCompletion.lean#L139-L140): **even pole-free positivity (`WeilPositiveEvenPolar`) automatically completes the pole and the full complex test cone** (using detuned Toeplitz packets + local Harnack propagation to kill both super-poles and negative double poles).
2. **Mixture Purification to a Single Smooth Source Is 100% Formalized:**
   - By [`exists_single_smooth_exact_moments`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorExactMomentRealization.lean#L41-L45) and [`singleSmooth_energy_fibre_eq`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorExactMomentRealization.lean#L77-L78), any nonnegative finite mixture of $C^2$ Weil tests is realized *with exact arithmetic trace and exact archimedean energy* by a **single** smooth compact even pole-free source.
3. **No Negative Pole Term in the Blind Objective:**
   - In [`EvenSectorBlindVariationalAttainment.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorBlindVariationalAttainment.lean), [`BlindUnitSource`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorBlindVariationalAttainment.lean#L32-L35) imposes the **linear** polar constraint `IsPolarConstrained a u` ($\hat{u}(\pm i/2) = 0$).
   - Consequently, on `BlindUnitSource a`, both the prime sum and the pole term vanish identically ([`sourceQuadratic_blind_eq_gamma`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorBlindVariationalAttainment.lean#L145-L148)):
     $$\mathcal{Q}_a(u) = \int_{\mathbb{R}} 2\,\gamma_{\text{Hardy}}(2\pi\xi)\,|u(\xi)|^2\,d\xi.$$
   - And [`exists_blind_minimizer`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorBlindVariationalAttainment.lean#L172-L174) proves unconditionally that at every aperture $a > 0$, a normalized minimizer $u_* \in \text{BlindUnitSource}(a)$ is attained.

---

### 2. The Single Remaining Open Step in EWU

By [`exists_weilPositiveEvenPolar_iff`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorPoleFreeBlindFarkas.lean#L217-L218) and [`weilPositiveFull_of_weilPositiveEvenPolar`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorPolarCompletion.lean#L127-L129), **closing RH via EWU reduces to a single unconditional target** ([ewu-blind-minimum-sign-2026-10-16.md](file:///Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/ewu-blind-minimum-sign-2026-10-16.md#L18-L22)):

> **EWU Open Core:** For every aperture $a > 0$, show that the attained blind minimizer $u_* \in \text{BlindUnitSource}(a)$ satisfies
> $$\int_{\mathbb{R}} 2\,\gamma_{\text{Hardy}}(2\pi\xi)\,|u_*(\xi)|^2\,d\xi \ge 0.$$

#### How Close Are We Quantitatively?
Write $\gamma(r) = \operatorname{Re}\psi(\tfrac{1}{4} + \tfrac{ir}{2}) - \log\pi$. The only negative region of $\gamma(r)$ is a small low-frequency well near $r = 0$, with minimum $\gamma(0) \approx -5.37$:
- **Without any constraints:** the minimum of the integral on unit vectors is $\gamma(0) \approx -5.37$.
- **With blindness at $n = 2$ alone:** [`node_two_certificate_le_weilArchRe`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/BlindArchimedeanNodeTwoCertificate.lean#L105-L110) raises the floor from $-5.37$ to $\gamma(0) + 2 \approx -3.37$.
- **With cosine-blindness at powers of $2$ ($n = 2^j$):** [`blindSymbolSlack_two_powers`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/BlindSymbolSlackPrimePowerPeriodization.lean#L507-L510) folds $\gamma(r)$ over the circle $[-\pi/\log 2, \pi/\log 2]$ and raises the floor to $m_2 = \frac{2\log 2}{\pi}\theta(\pi/\log 2) \approx -1.50$ (formally proved $\ge \gamma(0) + \frac{121}{32} \approx -1.59$).
- **Why cosine-blindness alone cannot cross $0$:** [`not_blindSymbolSlack_of_nonpos`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/BlindArchimedeanNodeTwoCertificate.lean#L254-L258) proves unconditionally that if you drop the polar constraint $\hat{u}(\pm i/2) = 0$, the archimedean integral *can* be negative on the blind cone. Conversely, [`riemannHypothesis_iff_forall_pos_zeroPoleBlindSymbolSlack`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/BlindArchimedeanNodeTwoCertificate.lean#L294-L296) shows that **the polar zero $\hat{u}(\pm i/2) = 0$ plus multi-prime blindness must eliminate the remaining $\approx 1.50$ of negative slack**.

---

### 3. Where Is the Genuine Chance to Close EWU?

In [ewu-blind-minimum-sign-2026-10-16.md](file:///Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/ewu-blind-minimum-sign-2026-10-16.md#L16-L75), ten naive mechanisms (dropping the polar constraint, pointwise squaring $P \mapsto P^2$, integer dilation $h \mapsto kh$, unnormalized fibre descent, single-prime periodization) were audited and shown not to work because they either violate $\hat{u}(i/2) = 0$ or ignore the analytic structure of $\hat{u}$.

However, there are **three concrete analytic ingredients** in `BlindUnitSource a` that have *not* yet been combined, and they represent our best shot at closing EWU:

#### Avenue A: Coupling Prime-Circle Periodization with the Paley–Wiener Factor $(z^2 + \tfrac{1}{4})$
Look at why [`BlindSymbolSlackPrimePowerPeriodization.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/BlindSymbolSlackPrimePowerPeriodization.lean) stops at $-1.50$: it treats the spectral density $G(r) = |\hat{f}(r)|^2$ as an **arbitrary nonnegative $L^1$ density** whose cosine moments vanish at $j\log 2$. That allows $G(r)$ to approximate a flat indicator on $[-\pi/\log 2, \pi/\log 2]$ without penalty.
- But for $u \in \text{BlindUnitSource}(a)$, $f = J_a u$ is compactly supported on $[-a, a]$, even, and satisfies $\hat{f}(\pm i/2) = 0$.
- By Paley–Wiener, $\hat{f}(r) = (r^2 + \tfrac{1}{4})\,\hat{g}(r)$, where $g$ is *also* compactly supported on $[-a, a]$ and even (`(∂² - 1/4)g = f`)!
- Writing $G(r) = (r^2 + \tfrac{1}{4})^2 |\hat{g}(r)|^2$ means the spectral measure is **forced to carry the quartic weight $(r^2 + \tfrac{1}{4})^2$** while its time-domain autocorrelation $((∂^2 - \tfrac{1}{4})g \star \widetilde{(∂^2 - \tfrac{1}{4})g})(\log n) = 0$ vanishes at all $n \ge 2$.
- Upweighting high frequencies by $(r^2 + \tfrac{1}{4})^2$ directly penalizes concentration near $r = 0$ (where $\gamma(r) < 0$ and $(r^2 + \tfrac{1}{4})^2$ attains its minimum $\tfrac{1}{16}$). We have not yet combined the $(r^2 + \tfrac{1}{4})^2$ differential factorization $f = (\partial^2 - \tfrac{1}{4})g$ with the multi-prime cosine-blindness periodization.

#### Avenue B: Importing OWU's de Branges Ground-Space Machinery into EWU
There is a striking asymmetry between what we formalized in OWU vs. EWU:
- In **OWU**, we built the full Farkas-corrected ground operator $Q_a - A_a - m(a)I \ge 0$, paired zero division, canonical de Branges generator $F_G(w)$, simple real-axis zeros, and exact Riesz spectral interpolation ([`OddSectorGroundPolynomialStructure.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/OddSectorGroundPolynomialStructure.lean), [`OddSectorExactSpectralInterpolation.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/OddSectorExactSpectralInterpolation.lean))—only to get blocked by OWU's rank-one negative pole square and cut-removal failure.
- In **EWU**, we stopped at variational attainment ([`EvenSectorBlindVariationalAttainment.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorBlindVariationalAttainment.lean)) and **never built the even polar ground operator or de Branges generator**!
- Because `IsPolarConstrained a u` ($\hat{u}(\pm i/2) = 0$) is a **linear** condition, the even polar Hilbert space $\mathcal{H}_{\text{even,polar}}(a) = \{f \in L^2_{\text{even}}[-a,a] : \langle \cosh(\cdot/2), f\rangle = 0\}$ is a closed linear subspace on which the pole term is identically zero.
- Every transform $F_u(w)$ in $\mathcal{H}_{\text{even,polar}}(a)$ automatically has fixed zeros at $w = \pm i/2$, so $F_u(w) = (w^2 + \tfrac{1}{4}) E_u(w)$ where $E_u$ belongs to a de Branges space of smaller exponential type. Building the Euler–Lagrange / ground-state characterization for `exists_blind_minimizer` on $\mathcal{H}_{\text{even,polar}}(a)$ brings the full power of de Branges zero-interlacing to bear on an operator that has **no negative pole rank-one term**.

#### Avenue C: Multi-Prime Joint Periodization (`log 2` and `log 3` Incommensurability)
[`BlindSymbolSlackPrimePowerPeriodization.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/BlindSymbolSlackPrimePowerPeriodization.lean) only uses the powers of a **single** prime ($2^j$), which only equidistributes the phase $r \log 2 \pmod{2\pi}$ and leaves modes supported at multiples of $2\pi/\log 2 \approx 9.06$ unconstrained.
- A source $u \in \text{BlindUnitSource}(a)$ is blind at **all** integers $n \ge 2$—not just $2^j$, but $3^k$, $2^j 3^k$, $5^\ell$, etc.
- While $\langle T_{\log m} f, T_{\log n} f\rangle$ involves $\log(m/n)$ (which is not directly constrained when $m \nmid n$), the autocorrelation $P_f(h) = \int_{\mathbb{R}} G(r)\cos(rh)\,dr$ vanishes simultaneously on the multiplicative semigroup $\{j\log 2 + k\log 3 : j + k \ge 1\}$.
- Combining the two-prime Fourier constraints $\widehat{G}(j\log 2 + k\log 3) = 0$ with the Paley–Wiener factor $G(r) = (r^2 + \tfrac{1}{4})^2|\hat{g}(r)|^2$ (Avenue A) directly attacks the $-1.50$ single-prime slack.

### Summary
- **OWU** is blocked on *both* existence and uniqueness, and its blind objective has an uncancelled negative pole square.
- **EWU** has **100% of uniqueness, cut removal, pole completion, mixture purification, and blind attainment already proved in Lean 4**.
- If we want to focus our effort where a single analytical breakthrough closes the entire formal RH proof, **EWU (`ewu-blind-minimum-sign-2026-10-16.md`, specifically combining the $(r^2 + \tfrac{1}{4})^2$ polar Paley–Wiener factorization with multi-prime blindness and the even-polar de Branges ground space) is the highest-leverage target.**