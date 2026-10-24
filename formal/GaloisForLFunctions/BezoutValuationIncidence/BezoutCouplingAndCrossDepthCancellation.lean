import GaloisForLFunctions.BezoutValuationIncidence.AllDepthHilbertDilationCubeAndHyperCubeGramFactorization
import GaloisForLFunctions.BezoutValuationIncidence.NaturalCutoffMultiDepthCofactorAndConditionalTailBridge
import GaloisForLFunctions.BezoutValuationIncidence.DilationClockComplementPrimeSurvival
import GaloisForLFunctions.BezoutValuationIncidence.RamanujanDilationProfileResidueGapBudget

/-!
# Bézout Coupling and Cross-Depth Cancellation: Global Signed-Complement Laws, Signed Packets, and Cutoff-Uniform Hypercube Dirichlet Forms

This module resolves Open Problem §7.5 ("Bézout coupling and cross-depth cancellation") of the
Bézout–Valuation Incidence programme (`BezoutValuationIncidence/README.md`) by establishing:

1. **Global Control of the Signed Complement (`ramanujanClockSignedComplement`) Across All Scale Pairs
   `(p, q)` Beyond Nearby Prime Pairs (§1):**
   - For all `1 < r, p, q` with `p < q ∨ q + 1 < p`, the physical signed complement of all
     non-clock-successor lags is universally bounded above in magnitude by the diagonal Gram
     plus the cutoff and seed-gap budgets (`abs_ramanujanClockSignedComplement_le`):
     $$|\mathrm{ramanujanClockSignedComplement}(r, p, q)|
       \le \mathcal G(r, r) + \sqrt{pq}\,\frac{B_r^2}{H + 1}
         + \mathrm{ramanujanClockSuccessorRelativeGapBudget}(r, p, q).$$
   - Combining `abs_dilationProfile_sub_clockSignedComplement_le_relativeGap` with the exact
     rational residue-gap bound (`ramanujanDilationProfile_defect_le_gap_budget`) yields a global
     two-sided distance bound between `ramanujanClockSignedComplement (r + 2) p q` and the positive
     diagonal `G(r + 2, r + 2)` valid for **every** integer pair `1 < p, q` with `p < q ∨ q + 1 < p`
     (`abs_diag_sub_ramanujanClockSignedComplement_le_gap_budget`), and in explicit relative-gap
     form on every dyadic band `2 ≤ p < q ≤ 2p` (`abs_diag_sub_ramanujanClockSignedComplement_dyadic_le`):
     $$\bigl|\mathcal G(R, R) - \mathrm{ramanujanClockSignedComplement}(R, p, q)\bigr|
       \le \frac{\mathrm{ramanujanDilationResidueBudget}(R)\,\mathrm{residueGapPronicBudget}(p, q)}{2p}
         + \frac{2 v \varphi(s)^2 (q - p)}{p}
         + \frac{B_R^2 + v s \varphi(s)^2}{p}.$$

2. **Positive Semidefiniteness and Exact Residue-Gap Decomposition for Arbitrary Signed Dilation
   Packets and Signed Prime Packets (§2):**
   - For any finite set $D \subset \mathbb{N}$ of positive scales (`∀ d ∈ D, 0 < d`), any $r > 1$,
     and any signed weights $c : \mathbb{N} \to \mathbb{R}$, the dilation-profile quadratic form is
     an exact `SoninL2` norm-square and is therefore nonnegative (`sum_mul_pmRamanujanDilationProfile_nonneg`):
     $$0 \le \sum_{d_1 \in D}\sum_{d_2 \in D} c(d_1)\,c(d_2)\,\Phi_r\Bigl(\frac{d_1}{d_2}\Bigr).$$
   - For any signed scaled packet $w : \mathbb{N} \to \mathbb{R}$ on $D$, the scaled dilation form
     decomposes into the product of the zero-th and first moments times $\mathcal G(r, r)$ minus half
     the pairwise scaled residue-gap form (`scaled_dilationProfile_packet_eq_diag_sub_gap`), giving
     the global residue-gap bound (`abs_scaled_dilationProfile_packet_sub_diag_le_budget`) and exact
     cancellation of the diagonal main term whenever $\sum_{d \in D} w(d) = 0$ or
     $\sum_{d \in D} d\,w(d) = 0$ (`abs_scaled_dilationProfile_packet_le_of_sum_eq_zero`).
   - For any signed energy-centered prime packet `primePacketBilinear S S a a` on
     $S : \mathrm{Finset}\ \mathrm{Nat.Primes}$, the quadratic form is nonnegative
     (`primePacketBilinear_self_nonneg`), decomposes identically into
     (`primePacketBilinear_eq_diag_sub_residueGap_add_log`):
     $$\mathrm{primePacketBilinear}(S, S, a, a)
       = \Bigl(\sum_{p \in S} a(p)\Bigr)\Bigl(\sum_{p \in S} a(p)\,\mathcal G^{\mathrm{ec}}(p, p)\Bigr)
         - \frac{1}{2}\sum_{p, q \in S} a(p)\,a(q)\,\mathrm{residueGapPronicEnergy}(p, q)
         + \Bigl(\sum_{p \in S} a(p)\,\log p\Bigr)^2
         - \Bigl(\sum_{p \in S} a(p)\Bigr)\Bigl(\sum_{p \in S} a(p)\,(\log p)^2\Bigr),$$
     and when $\sum_{p \in S} a(p) = 0$, the diagonal cancels identically leaving
     (`primePacketBilinear_eq_of_primePacketMass_eq_zero`,
     `abs_primePacketBilinear_sub_logMoment_sq_le_gapBudget_of_mass_zero`):
     $$\Bigl|\mathrm{primePacketBilinear}(S, S, a, a)
         - \Bigl(\sum_{p \in S} a(p)\,\log p\Bigr)^2\Bigr|
       \le \frac{1}{2}\sum_{p, q \in S} |a(p)|\,|a(q)|\,\mathrm{residueGapPronicBudget}(p, q).$$

3. **Cutoff-Uniform Bounds and Exact Cross-Depth Cancellation for the Hypercube Dirichlet Form of
   the Dilation Profile (§3):**
   - The hypercube Dirichlet form
     $\mathcal D_{r, \varepsilon}(P) = \sum_{d_1, d_2 \mid P} \mu(d_1)\mu(d_2)(d_1 d_2)^{-1/2-\varepsilon}\Phi_r(d_1/d_2)$
     is nonnegative for all $\varepsilon \in \mathbb{R}$, $P : \mathbb{N}$, and $r > 1$
     (`hypercubeDilationDirichletForm_nonneg`).
   - Multiplying by $(\mathrm{pmEulerCubeFactor}(\varepsilon, P))^2 Y_\varepsilon(r)^2$ and applying the
     exact cross-depth identity $\mathrm{pmEulerCubeFactor}(\varepsilon, P)\sum_{d \mid P}\mu(d)d^{-1-\varepsilon} = 1$
     cancels one factor of $\mathrm{pmEulerCubeFactor}(\varepsilon, P)$ against the zero-th moment,
     yielding the exact cross-depth decomposition (`hypercubeGram_eq_cancelled_diag_sub_residueGap`):
     $$\sum_{m_1, m_2 \mid P} Y_\varepsilon(m_1 r)\,Y_\varepsilon(m_2 r)\,\mathcal G(m_1 r, m_2 r)
       = Y_\varepsilon(r)^2\Bigl(\prod_{p \mid P}\frac{p^{1+\varepsilon} - p}{p^{1+\varepsilon} - 1}\Bigr)\mathcal G(r, r)
         - \frac{1}{2}\,\bigl(\mathrm{pmEulerCubeFactor}(\varepsilon, P)\bigr)^2 Y_\varepsilon(r)^2
           \sum_{d_1, d_2 \mid P} \frac{\mu(d_1)\mu(d_2)}{(d_1 d_2)^{1+\varepsilon}}
             \Bigl((d_1 + d_2)\mathcal G(r, r) - 2\sqrt{d_1 d_2}\Phi_r\Bigl(\frac{d_1}{d_2}\Bigr)\Bigr),$$
     where the cancelled diagonal coefficient $\prod_{p \mid P}\frac{p^{1+\varepsilon} - p}{p^{1+\varepsilon} - 1}$
     lies in $(0, 1]$ **uniformly in the squarefree cutoff $P$** for every $\varepsilon > 0$
     (`eulerCancelledFirstMoment_pos_and_le_one`)!
   - The diagonal of $\mathcal D_{r, \varepsilon}(P)$ is bounded uniformly in $P$ for every
     $\varepsilon > 0$ by $(\sum_{n=1}^\infty n^{-1-2\varepsilon})\mathcal G(r, r)$
     (`all_depth_dilationProfile_cube_diag_sum_le_tsum`), and the full Dirichlet form
     $\mathcal D_{r, \varepsilon}(P)$ is bounded uniformly in $P$ for every $\varepsilon > 1/2$ by
     $(\sum_{n=1}^\infty n^{-1/2-\varepsilon})^2 \mathcal G(r, r)$
     (`hypercubeDilationDirichletForm_le_tsum_sq_of_half_lt`).
   - On any finite prefix $0 \le N \le H$, every divisor $d \mid P$ with $d > H$ has $\lfloor N/d \rfloor = 0$
     and $\operatorname{Re} S_r(\lfloor N/d \rfloor) = 0$, so the Dirichlet dilation polynomial
     $\sum_{d \mid P} \mu(d) d^{-\varepsilon} \operatorname{Re} S_r(\lfloor N/d \rfloor)$ truncates
     identically to $d \le H$ (`dirichletDilationPrimitive_eq_filter_le`), and both its finite-prefix
     pronic head energy and its forced conditional tail-mean energy are bounded by $B_r^2 H^2$
     **independently of the squarefree cutoff $P$** for all $\varepsilon \ge 0$
     (`dirichletDilationHeadEnergy_and_tailMean_le_uniform_in_cutoff`).
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.NymanMellin GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Global Control of the Signed Complement Across All Scale Pairs `(p, q)` -/

/-- **Universal Upper Bound on the Signed Complement (`abs_ramanujanClockSignedComplement_le`):**
For every modulus `r > 1` and scale pair `p, q > 1` with `p < q ∨ q + 1 < p`, the magnitude of
`ramanujanClockSignedComplement r p q` is bounded by the diagonal Gram `G(r, r)` plus the physical
cutoff error and the clock-successor relative-gap budget. -/
theorem abs_ramanujanClockSignedComplement_le {r p q : ℕ}
    (hr : 1 < r) (hp : 1 < p) (hq : 1 < q) (hpq : p < q ∨ q + 1 < p) :
    |ramanujanClockSignedComplement r p q| ≤
      pmRamanujanPrimitiveGram r r +
        Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
          (pmRamanujanPrimitiveBound r ^ 2 /
            ((ramanujanClockSuccessorHorizon r p q : ℝ) + 1)) +
        ramanujanClockSuccessorRelativeGapBudget r p q := by
  have hdiff := abs_dilationProfile_sub_clockSignedComplement_le_relativeGap hr hp hq hpq
  have hprof : |pmRamanujanDilationProfile r hr ((p : ℝ) / q)| ≤ pmRamanujanPrimitiveGram r r :=
    abs_pmRamanujanDilationProfile_le hr (by positivity)
  have htri : |ramanujanClockSignedComplement r p q| ≤
      |pmRamanujanDilationProfile r hr ((p : ℝ) / q)| +
        |pmRamanujanDilationProfile r hr ((p : ℝ) / q) - ramanujanClockSignedComplement r p q| := by
    have := abs_add_le (pmRamanujanDilationProfile r hr ((p : ℝ) / q))
      (ramanujanClockSignedComplement r p q - pmRamanujanDilationProfile r hr ((p : ℝ) / q))
    rw [add_sub_cancel, abs_sub_comm] at this
    exact this
  linarith

/-- **Global Two-Sided Residue-Gap Distance from the Signed Complement to the Diagonal
(`abs_diag_sub_ramanujanClockSignedComplement_le_gap_budget`):**
For every `r : ℕ` (`R = r + 2`) and every scale pair `1 < p, q` with `p < q ∨ q + 1 < p`, the
distance between the positive diagonal `G(R, R)` and the physical signed complement
`ramanujanClockSignedComplement R p q` is bounded explicitly by the rational residue-gap budget
plus the clock-successor cutoff and relative-gap budgets. -/
theorem abs_diag_sub_ramanujanClockSignedComplement_le_gap_budget (r : ℕ) {p q : ℕ}
    (hp : 1 < p) (hq : 1 < q) (hpq : p < q ∨ q + 1 < p) :
    let R := r + 2
    |pmRamanujanPrimitiveGram R R - ramanujanClockSignedComplement R p q| ≤
      (ramanujanDilationResidueBudget R * residueGapPronicBudget p q -
          (Real.sqrt p - Real.sqrt q) ^ 2 * pmRamanujanPrimitiveGram R R) /
        (2 * Real.sqrt p * Real.sqrt q) +
      Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
        (pmRamanujanPrimitiveBound R ^ 2 /
          ((ramanujanClockSuccessorHorizon R p q : ℝ) + 1)) +
      ramanujanClockSuccessorRelativeGapBudget R p q := by
  intro R
  have hR : 1 < R := by dsimp [R]; omega
  have hp0 : 0 < p := by omega
  have hq0 : 0 < q := by omega
  have h2pq : 0 < 2 * Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) := by positivity
  obtain ⟨hdef0, hdef⟩ := ramanujanDilationProfile_gap_budget r ⟨p, hp0⟩ ⟨q, hq0⟩
  obtain ⟨hdef_nn, hdef_le⟩ := ramanujanDilationProfile_defect_le_gap_budget r ⟨p, hp0⟩ ⟨q, hq0⟩
  change 0 ≤ pmRamanujanPrimitiveGram R R - pmRamanujanDilationProfile R hR ((p : ℝ) / q) at hdef_nn
  change 2 * Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
      (pmRamanujanPrimitiveGram R R - pmRamanujanDilationProfile R hR ((p : ℝ) / q)) ≤
    ramanujanDilationResidueBudget R * residueGapPronicBudget p q -
      (Real.sqrt (p : ℝ) - Real.sqrt (q : ℝ)) ^ 2 * pmRamanujanPrimitiveGram R R at hdef_le
  have hprof :
      |pmRamanujanPrimitiveGram R R - pmRamanujanDilationProfile R hR ((p : ℝ) / q)| ≤
        (ramanujanDilationResidueBudget R * residueGapPronicBudget p q -
            (Real.sqrt p - Real.sqrt q) ^ 2 * pmRamanujanPrimitiveGram R R) /
          (2 * Real.sqrt p * Real.sqrt q) := by
    rw [abs_of_nonneg hdef_nn, le_div_iff₀ h2pq]
    linarith
  have hcomp := abs_dilationProfile_sub_clockSignedComplement_le_relativeGap hR hp hq hpq
  have htri :
      |pmRamanujanPrimitiveGram R R - ramanujanClockSignedComplement R p q| ≤
        |pmRamanujanPrimitiveGram R R - pmRamanujanDilationProfile R hR ((p : ℝ) / q)| +
          |pmRamanujanDilationProfile R hR ((p : ℝ) / q) -
            ramanujanClockSignedComplement R p q| := by
    simpa [sub_add_sub_cancel] using
      abs_add_le (pmRamanujanPrimitiveGram R R - pmRamanujanDilationProfile R hR ((p : ℝ) / q))
        (pmRamanujanDilationProfile R hR ((p : ℝ) / q) - ramanujanClockSignedComplement R p q)
  linarith

/-- **Explicit Dyadic-Band Distance Bound for the Signed Complement
(`abs_diag_sub_ramanujanClockSignedComplement_dyadic_le`):**
For every `r : ℕ` (`R = r + 2`) and every scale pair `2 ≤ p < q ≤ 2p` (whether prime or composite),
the distance between `ramanujanClockSignedComplement R p q` and `G(R, R)` is bounded by the
residue-gap budget plus the relative-gap and inverse-scale clock errors. -/
theorem abs_diag_sub_ramanujanClockSignedComplement_dyadic_le (r : ℕ) {p q : ℕ}
    (hp : 1 < p) (hpq : p < q) (hqp : (q : ℝ) ≤ 2 * p) :
    let R := r + 2
    |pmRamanujanPrimitiveGram R R - ramanujanClockSignedComplement R p q| ≤
      ramanujanDilationResidueBudget R * residueGapPronicBudget p q / (2 * p) +
        2 * (lagVisibilityClock R : ℝ) * ((primeRadical R).totient : ℝ) ^ 2 *
          ((q : ℝ) - p) / p +
        (pmRamanujanPrimitiveBound R ^ 2 + (lagVisibilityClock R : ℝ) *
          (primeRadical R : ℝ) * ((primeRadical R).totient : ℝ) ^ 2) / p := by
  intro R
  have hq : 1 < q := lt_trans hp hpq
  have h1 := abs_diag_sub_ramanujanClockSignedComplement_le_gap_budget r hp hq (Or.inl hpq)
  have h2 := clock_successor_total_error_le_relative_gap (by dsimp [R]; omega : R ≠ 0) hp hpq hqp
  have hR : 1 < R := by dsimp [R]; omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hpqR : (p : ℝ) ≤ q := by exact_mod_cast hpq.le
  have h2p : 2 * (p : ℝ) ≤ 2 * Real.sqrt p * Real.sqrt q := by
    have hsp : Real.sqrt (p : ℝ) ≤ Real.sqrt (q : ℝ) := Real.sqrt_le_sqrt hpqR
    calc 2 * (p : ℝ) = 2 * (Real.sqrt p * Real.sqrt p) := by rw [Real.mul_self_sqrt hp0.le]
      _ ≤ 2 * (Real.sqrt p * Real.sqrt q) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsp (Real.sqrt_nonneg _)) zero_le_two
      _ = 2 * Real.sqrt p * Real.sqrt q := by ring
  have hG0 : 0 ≤ (Real.sqrt p - Real.sqrt q) ^ 2 * pmRamanujanPrimitiveGram R R :=
    mul_nonneg (sq_nonneg _) (pmRamanujanPrimitiveGram_pos hR).le
  have hB0 : 0 ≤ ramanujanDilationResidueBudget R * residueGapPronicBudget p q := by
    have := (ramanujanDilationProfile_gap_budget r ⟨p, by omega⟩ ⟨q, by omega⟩)
    exact this.1.trans this.2
  have hquot :
      (ramanujanDilationResidueBudget R * residueGapPronicBudget p q -
          (Real.sqrt p - Real.sqrt q) ^ 2 * pmRamanujanPrimitiveGram R R) /
        (2 * Real.sqrt p * Real.sqrt q) ≤
      ramanujanDilationResidueBudget R * residueGapPronicBudget p q / (2 * p) := by
    calc (ramanujanDilationResidueBudget R * residueGapPronicBudget p q -
            (Real.sqrt p - Real.sqrt q) ^ 2 * pmRamanujanPrimitiveGram R R) /
          (2 * Real.sqrt p * Real.sqrt q)
        ≤ (ramanujanDilationResidueBudget R * residueGapPronicBudget p q) /
            (2 * Real.sqrt p * Real.sqrt q) :=
          div_le_div_of_nonneg_right (sub_le_self _ hG0) (by positivity)
      _ ≤ ramanujanDilationResidueBudget R * residueGapPronicBudget p q / (2 * p) :=
          div_le_div_of_nonneg_left hB0 (by positivity) h2p
  dsimp only [R] at h1 h2 hquot ⊢
  linarith

/-! ## §2. Positive Semidefiniteness and Residue-Gap Decomposition for Signed Dilation and Prime Packets -/

/-- **Positive Semidefiniteness of the Dilation Profile for Arbitrary Signed Weights
(`sum_mul_pmRamanujanDilationProfile_nonneg`):**
For any modulus `r > 1`, any finite set of positive scales `D : Finset ℕ` (`∀ d ∈ D, 0 < d`), and
any real weights `c : ℕ → ℝ`, the dilation-profile quadratic form equals the `SoninL2` norm-square
of `∑ d ∈ D, (c d : ℂ) • rayDilate d⁻¹ (pmRamanujanStepVector r hr)` and is therefore nonnegative. -/
theorem sum_mul_pmRamanujanDilationProfile_nonneg {r : ℕ} (hr : 1 < r)
    {D : Finset ℕ} (hD : ∀ d ∈ D, 0 < d) (c : ℕ → ℝ) :
    0 ≤ ∑ d₁ ∈ D, ∑ d₂ ∈ D,
      c d₁ * c d₂ * pmRamanujanDilationProfile r hr ((d₁ : ℝ) / d₂) ∧
    ∑ d₁ ∈ D, ∑ d₂ ∈ D,
      c d₁ * c d₂ * pmRamanujanDilationProfile r hr ((d₁ : ℝ) / d₂) =
      ‖∑ d ∈ D, (c d : ℂ) • rayDilate (d : ℝ)⁻¹ (pmRamanujanStepVector r hr)‖ ^ 2 := by
  let v : ℕ → SoninL2 := fun d => rayDilate (d : ℝ)⁻¹ (pmRamanujanStepVector r hr)
  let V : SoninL2 := ∑ d ∈ D, (c d : ℂ) • v d
  have hinner : (inner ℂ V V).re =
      ∑ d₁ ∈ D, ∑ d₂ ∈ D, c d₁ * c d₂ * pmRamanujanDilationProfile r hr ((d₁ : ℝ) / d₂) := by
    dsimp only [V]
    rw [sum_inner, Complex.re_sum]
    refine sum_congr rfl fun d₁ hd₁ => ?_
    rw [inner_sum, Complex.re_sum]
    refine sum_congr rfl fun d₂ hd₂ => ?_
    rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hd₁0 : (0 : ℝ) < d₁ := by exact_mod_cast hD d₁ hd₁
    have hd₂0 : (0 : ℝ) < d₂ := by exact_mod_cast hD d₂ hd₂
    rw [re_inner_rayDilate_inv hr hd₁0 hd₂0]
    ring
  have hnorm : (inner ℂ V V).re = ‖V‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, sq, sq]
    simp
  rw [← hinner, hnorm]
  exact ⟨sq_nonneg _, rfl⟩

/-- **Exact Residue-Gap Decomposition for Signed Scaled Dilation Packets
(`scaled_dilationProfile_packet_eq_diag_sub_gap`):**
For any modulus `r > 1`, finite set `D : Finset ℕ`, and signed weights `w : ℕ → ℝ`, the scaled
dilation-profile quadratic form splits into the product of the zero-th and first moments times
`G(r, r)` minus half the pairwise scaled residue-gap form. -/
theorem scaled_dilationProfile_packet_eq_diag_sub_gap {r : ℕ} (hr : 1 < r)
    (D : Finset ℕ) (w : ℕ → ℝ) :
    (∑ d₁ ∈ D, ∑ d₂ ∈ D,
        w d₁ * w d₂ * Real.sqrt d₁ * Real.sqrt d₂ *
          pmRamanujanDilationProfile r hr ((d₁ : ℝ) / d₂)) =
      (∑ d ∈ D, w d) * (∑ d ∈ D, (d : ℝ) * w d) * pmRamanujanPrimitiveGram r r -
        (1 / 2) * ∑ d₁ ∈ D, ∑ d₂ ∈ D,
          w d₁ * w d₂ *
            (((d₁ : ℝ) + d₂) * pmRamanujanPrimitiveGram r r -
              2 * Real.sqrt d₁ * Real.sqrt d₂ *
                pmRamanujanDilationProfile r hr ((d₁ : ℝ) / d₂)) := by
  have h1 :
      (∑ d ∈ D, w d) * (∑ d ∈ D, (d : ℝ) * w d) * pmRamanujanPrimitiveGram r r =
        (1 / 2) * ∑ d₁ ∈ D, ∑ d₂ ∈ D,
          w d₁ * w d₂ * ((d₁ : ℝ) + d₂) * pmRamanujanPrimitiveGram r r := by
    have hA :
        ∑ d₁ ∈ D, ∑ d₂ ∈ D, w d₁ * w d₂ * (d₁ : ℝ) * pmRamanujanPrimitiveGram r r =
          (∑ d ∈ D, w d) * (∑ d ∈ D, (d : ℝ) * w d) * pmRamanujanPrimitiveGram r r := by
      rw [mul_comm (∑ d ∈ D, w d), sum_mul, sum_mul]
      refine sum_congr rfl fun d₁ _ => ?_
      rw [mul_sum, sum_mul]
      refine sum_congr rfl fun d₂ _ => by ring
    have hB :
        ∑ d₁ ∈ D, ∑ d₂ ∈ D, w d₁ * w d₂ * (d₂ : ℝ) * pmRamanujanPrimitiveGram r r =
          (∑ d ∈ D, w d) * (∑ d ∈ D, (d : ℝ) * w d) * pmRamanujanPrimitiveGram r r := by
      rw [sum_comm]
      refine (sum_congr rfl fun d₂ _ => sum_congr rfl fun d₁ _ => ?_).trans hA
      ring
    have hAB :
        ∑ d₁ ∈ D, ∑ d₂ ∈ D, w d₁ * w d₂ * ((d₁ : ℝ) + d₂) * pmRamanujanPrimitiveGram r r =
          (∑ d₁ ∈ D, ∑ d₂ ∈ D, w d₁ * w d₂ * (d₁ : ℝ) * pmRamanujanPrimitiveGram r r) +
            ∑ d₁ ∈ D, ∑ d₂ ∈ D, w d₁ * w d₂ * (d₂ : ℝ) * pmRamanujanPrimitiveGram r r := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun d₁ _ => ?_
      rw [← sum_add_distrib]
      refine sum_congr rfl fun d₂ _ => by ring
    rw [hAB, hA, hB]
    ring
  rw [h1, ← mul_sub, ← sum_sub_distrib]
  have hinner :
      ∑ x ∈ D,
          (∑ d₂ ∈ D, w x * w d₂ * ((x : ℝ) + d₂) * pmRamanujanPrimitiveGram r r -
            ∑ d₂ ∈ D, w x * w d₂ *
              (((x : ℝ) + d₂) * pmRamanujanPrimitiveGram r r -
                2 * Real.sqrt x * Real.sqrt d₂ *
                  pmRamanujanDilationProfile r hr ((x : ℝ) / d₂))) =
        ∑ d₁ ∈ D, ∑ d₂ ∈ D,
          2 * (w d₁ * w d₂ * Real.sqrt d₁ * Real.sqrt d₂ *
            pmRamanujanDilationProfile r hr ((d₁ : ℝ) / d₂)) := by
    refine sum_congr rfl fun d₁ _ => ?_
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun d₂ _ => by ring
  rw [hinner, mul_sum]
  refine sum_congr rfl fun d₁ _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun d₂ _ => by ring

/-- **Global Residue-Gap Bound for Arbitrary Signed Scaled Dilation Packets
(`abs_scaled_dilationProfile_packet_sub_diag_le_budget`):**
For any `r : ℕ` (`R = r + 2`), any finite set of positive scales `D : Finset ℕ` (`∀ d ∈ D, 0 < d`),
and any signed weights `w : ℕ → ℝ`, the deviation of the scaled dilation-profile form from the
moment product `(∑ w(d))(∑ d w(d)) G(R, R)` is bounded by half the pairwise residue-gap budget. -/
theorem abs_scaled_dilationProfile_packet_sub_diag_le_budget (r : ℕ)
    {D : Finset ℕ} (hD : ∀ d ∈ D, 0 < d) (w : ℕ → ℝ) :
    let R := r + 2
    |(∑ d₁ ∈ D, ∑ d₂ ∈ D,
        w d₁ * w d₂ * Real.sqrt d₁ * Real.sqrt d₂ *
          pmRamanujanDilationProfile R (by omega) ((d₁ : ℝ) / d₂)) -
      (∑ d ∈ D, w d) * (∑ d ∈ D, (d : ℝ) * w d) * pmRamanujanPrimitiveGram R R| ≤
      (1 / 2) * ramanujanDilationResidueBudget R *
        ∑ d₁ ∈ D, ∑ d₂ ∈ D, |w d₁| * |w d₂| * residueGapPronicBudget d₁ d₂ := by
  intro R
  have hR : 1 < R := by dsimp [R]; omega
  rw [scaled_dilationProfile_packet_eq_diag_sub_gap hR D w, sub_sub_cancel_left, abs_neg,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rw [mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d₁ hd₁ => ?_)
  rw [mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d₂ hd₂ => ?_)
  obtain ⟨h0, hbud⟩ := ramanujanDilationProfile_gap_budget r ⟨d₁, hD d₁ hd₁⟩ ⟨d₂, hD d₂ hd₂⟩
  change 0 ≤ ((d₁ : ℝ) + d₂) * pmRamanujanPrimitiveGram R R -
      2 * Real.sqrt d₁ * Real.sqrt d₂ * pmRamanujanDilationProfile R hR ((d₁ : ℝ) / d₂) at h0
  change ((d₁ : ℝ) + d₂) * pmRamanujanPrimitiveGram R R -
      2 * Real.sqrt d₁ * Real.sqrt d₂ * pmRamanujanDilationProfile R hR ((d₁ : ℝ) / d₂) ≤
    ramanujanDilationResidueBudget R * residueGapPronicBudget d₁ d₂ at hbud
  rw [abs_mul, abs_mul, abs_of_nonneg h0]
  calc |w d₁| * |w d₂| *
        (((d₁ : ℝ) + d₂) * pmRamanujanPrimitiveGram R R -
          2 * Real.sqrt d₁ * Real.sqrt d₂ * pmRamanujanDilationProfile R hR ((d₁ : ℝ) / d₂))
      ≤ |w d₁| * |w d₂| * (ramanujanDilationResidueBudget R * residueGapPronicBudget d₁ d₂) :=
        mul_le_mul_of_nonneg_left hbud (by positivity)
    _ = ramanujanDilationResidueBudget R * (|w d₁| * |w d₂| * residueGapPronicBudget d₁ d₂) := by
        ring

/-- **Exact Diagonal Cancellation for Mean-Zero Signed Scaled Dilation Packets
(`abs_scaled_dilationProfile_packet_le_of_sum_eq_zero`):**
Whenever `∑ d ∈ D, w d = 0` or `∑ d ∈ D, d * w d = 0`, the diagonal term `G(R, R)` cancels
identically from the scaled dilation-profile packet, leaving pure residue-gap control. -/
theorem abs_scaled_dilationProfile_packet_le_of_sum_eq_zero (r : ℕ)
    {D : Finset ℕ} (hD : ∀ d ∈ D, 0 < d) (w : ℕ → ℝ)
    (hw : (∑ d ∈ D, w d) = 0 ∨ (∑ d ∈ D, (d : ℝ) * w d) = 0) :
    let R := r + 2
    |∑ d₁ ∈ D, ∑ d₂ ∈ D,
        w d₁ * w d₂ * Real.sqrt d₁ * Real.sqrt d₂ *
          pmRamanujanDilationProfile R (by omega) ((d₁ : ℝ) / d₂)| ≤
      (1 / 2) * ramanujanDilationResidueBudget R *
        ∑ d₁ ∈ D, ∑ d₂ ∈ D, |w d₁| * |w d₂| * residueGapPronicBudget d₁ d₂ := by
  intro R
  have h := abs_scaled_dilationProfile_packet_sub_diag_le_budget r hD w
  have hz : (∑ d ∈ D, w d) * (∑ d ∈ D, (d : ℝ) * w d) * pmRamanujanPrimitiveGram R R = 0 := by
    rcases hw with h0 | h1
    · simp [h0]
    · simp [h1]
  simpa [R, hz] using h

/-- **Positive Semidefiniteness of Energy-Centered Prime Packets (`primePacketBilinear_self_nonneg`):**
For every finite set of primes `S : Finset Nat.Primes` and every signed weight `a : Nat.Primes → ℝ`,
`0 ≤ primePacketBilinear S S a a`. -/
theorem primePacketBilinear_self_nonneg (S : Finset Nat.Primes) (a : Nat.Primes → ℝ) :
    0 ≤ primePacketBilinear S S a a := by
  rw [← (hasSum_primePacketBilinear S S a a).tsum_eq]
  exact tsum_nonneg fun n => div_nonneg (mul_self_nonneg _) (by positivity)

/-- **Exact Residue-Gap and Logarithmic-Variance Decomposition of Signed Prime Packets
(`primePacketBilinear_eq_diag_sub_residueGap_add_log`):**
For any finite set of primes `S` and signed weights `a : Nat.Primes → ℝ`, `primePacketBilinear S S a a`
decomposes into the diagonal product `(∑ a_p)(∑ a_p G^{ec}(p, p))`, minus half the pairwise
residue-gap energy form, plus the logarithmic variance `(1/2) ∑_{p, q} a_p a_q (log p - log q)^2`. -/
theorem primePacketBilinear_eq_diag_sub_residueGap_add_log
    (S : Finset Nat.Primes) (a : Nat.Primes → ℝ) :
    primePacketBilinear S S a a =
      primePacketMass S a * (∑ p ∈ S, a p * pmRamanujanEnergyCenteredGram (p : ℕ) (p : ℕ)) -
        (1 / 2) * (∑ p ∈ S, ∑ q ∈ S, a p * a q * residueGapPronicEnergy (p : ℕ) (q : ℕ)) +
        (1 / 2) * (∑ p ∈ S, ∑ q ∈ S, a p * a q * (Real.log (p : ℕ) - Real.log (q : ℕ)) ^ 2) := by
  have hpair :
      ∀ p ∈ S, ∀ q ∈ S,
        a p * a q * pmRamanujanEnergyCenteredGram (p : ℕ) (q : ℕ) =
          (1 / 2) * (a p * a q * pmRamanujanEnergyCenteredGram (p : ℕ) (p : ℕ) +
              a p * a q * pmRamanujanEnergyCenteredGram (q : ℕ) (q : ℕ)) -
            (1 / 2) * (a p * a q * residueGapPronicEnergy (p : ℕ) (q : ℕ)) +
            (1 / 2) * (a p * a q * (Real.log (p : ℕ) - Real.log (q : ℕ)) ^ 2) := by
    intro p _ q _
    have h := primePair_centered_distance_eq_residueGap ⟨(p : ℕ), p.property⟩ ⟨(q : ℕ), q.property⟩
    change pmRamanujanEnergyCenteredGram (p : ℕ) (p : ℕ) +
        pmRamanujanEnergyCenteredGram (q : ℕ) (q : ℕ) -
        2 * pmRamanujanEnergyCenteredGram (p : ℕ) (q : ℕ) =
      residueGapPronicEnergy (p : ℕ) (q : ℕ) - (Real.log (p : ℕ) - Real.log (q : ℕ)) ^ 2 at h
    linarith [congrArg (fun x => (1 / 2 : ℝ) * (a p * a q) * x) h]
  have hA :
      ∑ p ∈ S, ∑ q ∈ S, a p * a q * pmRamanujanEnergyCenteredGram (p : ℕ) (p : ℕ) =
        primePacketMass S a * (∑ p ∈ S, a p * pmRamanujanEnergyCenteredGram (p : ℕ) (p : ℕ)) := by
    unfold primePacketMass
    rw [mul_comm (∑ p ∈ S, a p), sum_mul]
    refine sum_congr rfl fun p _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun q _ => by ring
  have hB :
      ∑ p ∈ S, ∑ q ∈ S, a p * a q * pmRamanujanEnergyCenteredGram (q : ℕ) (q : ℕ) =
        primePacketMass S a * (∑ p ∈ S, a p * pmRamanujanEnergyCenteredGram (p : ℕ) (p : ℕ)) := by
    rw [sum_comm]
    refine (sum_congr rfl fun q _ => sum_congr rfl fun p _ => ?_).trans hA
    ring
  change (∑ p ∈ S, ∑ q ∈ S, a p * a q * pmRamanujanEnergyCenteredGram (p : ℕ) (q : ℕ)) = _
  rw [sum_congr rfl fun p hp => sum_congr rfl fun q hq => hpair p hp q hq]
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum]
  rw [hA, hB]
  ring

/-- **Exact Diagonal Cancellation and Conditional Negative Definiteness of the Residue-Gap Form for
Mean-Zero Signed Prime Packets (`primePacketBilinear_eq_of_primePacketMass_eq_zero`):**
Whenever `primePacketMass S a = 0` (`∑_{p ∈ S} a_p = 0`), the diagonal terms `G^{ec}(p, p)` cancel
identically from `primePacketBilinear S S a a`, leaving
`-(1 / 2) * ∑_{p, q} a_p a_q E_gap(p, q) - primePacketLogMoment S a ^ 2`, which forces
`primePacketLogMoment S a ^ 2 ≤ -(1 / 2) * ∑_{p, q} a_p a_q E_gap(p, q)` and bounds
`primePacketBilinear S S a a + primePacketLogMoment S a ^ 2` by half the pairwise residue-gap budget. -/
theorem primePacketBilinear_eq_of_primePacketMass_eq_zero
    (S : Finset Nat.Primes) (a : Nat.Primes → ℝ) (hmass : primePacketMass S a = 0) :
    primePacketBilinear S S a a =
      -(1 / 2) * (∑ p ∈ S, ∑ q ∈ S, a p * a q * residueGapPronicEnergy (p : ℕ) (q : ℕ)) -
        primePacketLogMoment S a ^ 2 ∧
    primePacketLogMoment S a ^ 2 ≤
      -(1 / 2) * (∑ p ∈ S, ∑ q ∈ S, a p * a q * residueGapPronicEnergy (p : ℕ) (q : ℕ)) ∧
    |primePacketBilinear S S a a + primePacketLogMoment S a ^ 2| ≤
      (1 / 2) * ∑ p ∈ S, ∑ q ∈ S, |a p| * |a q| * residueGapPronicBudget (p : ℕ) (q : ℕ) := by
  have hlog :
      (1 / 2 : ℝ) * (∑ p ∈ S, ∑ q ∈ S, a p * a q * (Real.log (p : ℕ) - Real.log (q : ℕ)) ^ 2) =
        -primePacketLogMoment S a ^ 2 := by
    have h1 :
        ∑ p ∈ S, ∑ q ∈ S, a p * a q * (Real.log (p : ℕ)) ^ 2 =
          primePacketMass S a * (∑ p ∈ S, a p * (Real.log (p : ℕ)) ^ 2) := by
      unfold primePacketMass
      rw [mul_comm (∑ p ∈ S, a p), sum_mul]
      refine sum_congr rfl fun p _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun q _ => by ring
    have h2 :
        ∑ p ∈ S, ∑ q ∈ S, a p * a q * (Real.log (q : ℕ)) ^ 2 =
          primePacketMass S a * (∑ p ∈ S, a p * (Real.log (p : ℕ)) ^ 2) := by
      rw [sum_comm]
      refine (sum_congr rfl fun q _ => sum_congr rfl fun p _ => ?_).trans h1
      ring
    have hLP : primePacketLogMoment S a = ∑ p ∈ S, a p * Real.log (p : ℕ) := rfl
    have h3 :
        ∑ p ∈ S, ∑ q ∈ S, a p * a q * (2 * Real.log (p : ℕ) * Real.log (q : ℕ)) =
          2 * primePacketLogMoment S a ^ 2 := by
      rw [hLP, sq, sum_mul, mul_sum]
      refine sum_congr rfl fun p _ => ?_
      rw [mul_sum, mul_sum]
      refine sum_congr rfl fun q _ => by ring
    have hexp :
        ∑ p ∈ S, ∑ q ∈ S, a p * a q * (Real.log (p : ℕ) - Real.log (q : ℕ)) ^ 2 =
          (∑ p ∈ S, ∑ q ∈ S, a p * a q * (Real.log (p : ℕ)) ^ 2) +
            (∑ p ∈ S, ∑ q ∈ S, a p * a q * (Real.log (q : ℕ)) ^ 2) -
            ∑ p ∈ S, ∑ q ∈ S, a p * a q * (2 * Real.log (p : ℕ) * Real.log (q : ℕ)) := by
      rw [← sum_add_distrib, ← sum_sub_distrib]
      refine sum_congr rfl fun p _ => ?_
      rw [← sum_add_distrib, ← sum_sub_distrib]
      refine sum_congr rfl fun q _ => by ring
    rw [hexp, h1, h2, h3, hmass]
    ring
  have heq :
      primePacketBilinear S S a a =
        -(1 / 2) * (∑ p ∈ S, ∑ q ∈ S, a p * a q * residueGapPronicEnergy (p : ℕ) (q : ℕ)) -
          primePacketLogMoment S a ^ 2 := by
    rw [primePacketBilinear_eq_diag_sub_residueGap_add_log, hmass, zero_mul, zero_sub, hlog]
    ring
  have hnn := primePacketBilinear_self_nonneg S a
  refine ⟨heq, by linarith, ?_⟩
  rw [heq, sub_add_cancel, neg_mul, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p _ => ?_)
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun q _ => ?_)
  have hE0 : 0 ≤ residueGapPronicEnergy (p : ℕ) (q : ℕ) :=
    tsum_nonneg fun n => by unfold residueGapPronicTerm; positivity
  have hbud := residueGapPronicEnergy_le_budget ⟨(p : ℕ), p.property.pos⟩ ⟨(q : ℕ), q.property.pos⟩
  change residueGapPronicEnergy (p : ℕ) (q : ℕ) ≤ residueGapPronicBudget (p : ℕ) (q : ℕ) at hbud
  rw [abs_mul, abs_mul, abs_of_nonneg hE0]
  exact mul_le_mul_of_nonneg_left hbud (by positivity)

/-! ## §3. Cutoff-Uniform Bounds and Cross-Depth Cancellation for the Hypercube Dirichlet Form -/

/-- **The Hypercube Dirichlet Form of the Continuous Dilation Profile (`hypercubeDilationDirichletForm`):**
The quadratic form `∑_{d₁, d₂ ∣ P} μ(d₁) μ(d₂) (d₁ d₂)^{-1/2-ε} Φ_r(d₁ / d₂)` appearing on the
right-hand side of the all-depth hypercube factorization `all_depth_coherent_primitiveGram_cube_eq`. -/
def hypercubeDilationDirichletForm (ε : ℝ) (P r : ℕ) (hr : 1 < r) : ℝ :=
  ∑ d₁ ∈ P.divisors, ∑ d₂ ∈ P.divisors,
    (moebiusReal d₁ * (d₁ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
      (moebiusReal d₂ * (d₂ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
      pmRamanujanDilationProfile r hr ((d₁ : ℝ) / d₂)

/-- **Nonnegativity of the Hypercube Dilation Dirichlet Form (`hypercubeDilationDirichletForm_nonneg`):**
For every `ε : ℝ`, `P : ℕ`, and `r > 1`, `0 ≤ hypercubeDilationDirichletForm ε P r hr`. -/
theorem hypercubeDilationDirichletForm_nonneg (ε : ℝ) (P : ℕ) {r : ℕ} (hr : 1 < r) :
    0 ≤ hypercubeDilationDirichletForm ε P r hr :=
  (sum_mul_pmRamanujanDilationProfile_nonneg hr (fun _ hd => Nat.pos_of_mem_divisors hd)
    (fun d => moebiusReal d * (d : ℝ) ^ (-(1 / 2 : ℝ) - ε))).1

private theorem abs_moebiusReal_le_one (d : ℕ) : |moebiusReal d| ≤ 1 :=
  Sieve.abs_moebius_le_one d

private theorem sum_divisors_prime_mul_real (F : ℕ → ℝ) {p Q : ℕ} (hp : p.Prime) (hpQ : ¬ p ∣ Q) :
    (∑ d ∈ (p * Q).divisors, F d) = ∑ d ∈ Q.divisors, (F d + F (p * d)) := by
  classical
  rw [(hp.coprime_iff_not_dvd.mpr hpQ).divisors_mul]
  simp only [Finset.sum_map, Function.Embedding.coeFn_mk]
  trans ∑ x ∈ p.divisors ×ˢ Q.divisors, F (x.1 * x.2)
  · exact Finset.sum_attach (p.divisors ×ˢ Q.divisors) (fun x : ℕ × ℕ => F (x.1 * x.2))
  rw [Finset.sum_product, hp.divisors, Finset.sum_pair hp.ne_one.symm]
  simp only [one_mul, Finset.sum_add_distrib]

/-- **Cutoff-Uniform Bound on the Cancelled Euler First Moment
(`eulerCancelledFirstMoment_pos_and_le_one`):**
For any `ε > 0` and any squarefree `P`, the product
`pmEulerCubeFactor ε P * ∑_{d ∣ P} μ(d) d^{-ε}` equals the local Euler product
`∏_{p ∣ P} (p^{1+ε} - p) / (p^{1+ε} - 1)`, which lies strictly in `(0, 1]` **uniformly in the
squarefree cutoff `P`**! -/
theorem eulerCancelledFirstMoment_pos_and_le_one {ε : ℝ} (hε : 0 < ε)
    {P : ℕ} (hP : Squarefree P) :
    pmEulerCubeFactor ε P * (∑ d ∈ P.divisors, moebiusReal d * (d : ℝ) ^ (-ε)) =
      ∏ p ∈ P.primeFactors,
        ((p : ℝ) ^ (1 + ε) - p) / ((p : ℝ) ^ (1 + ε) - 1) ∧
    0 < pmEulerCubeFactor ε P * (∑ d ∈ P.divisors, moebiusReal d * (d : ℝ) ^ (-ε)) ∧
    pmEulerCubeFactor ε P * (∑ d ∈ P.divisors, moebiusReal d * (d : ℝ) ^ (-ε)) ≤ 1 := by
  have heq :
      pmEulerCubeFactor ε P * (∑ d ∈ P.divisors, moebiusReal d * (d : ℝ) ^ (-ε)) =
        ∏ p ∈ P.primeFactors,
          ((p : ℝ) ^ (1 + ε) - p) / ((p : ℝ) ^ (1 + ε) - 1) := by
    induction P using induction_on_primes with
    | zero => exact (_root_.not_squarefree_zero hP).elim
    | one => simp [pmEulerCubeFactor_one, moebiusReal]
    | prime_mul p Q hp ih =>
      have hQ : Squarefree Q := hP.of_mul_right
      have hQ0 : Q ≠ 0 := hQ.ne_zero
      have hpQ : ¬ p ∣ Q := hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hP)
      have hpQ_mem : p ∉ Q.primeFactors := fun h => hpQ (Nat.dvd_of_mem_primeFactors h)
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hden : (p : ℝ) ^ (1 + ε) - 1 ≠ 0 :=
        ne_of_gt (zero_lt_one.trans (pmPowerDampedRamanujan_prime_denominator_one_lt hε hp))
      rw [pmEulerCubeFactor_prime_mul ε hp hQ0 hpQ,
        Nat.primeFactors_mul hp.ne_zero hQ0, hp.primeFactors, Finset.singleton_union,
        Finset.prod_insert hpQ_mem, ← ih hQ]
      have hdiv :
          (∑ d ∈ (p * Q).divisors, moebiusReal d * (d : ℝ) ^ (-ε)) =
            (1 - (p : ℝ) ^ (-ε)) * (∑ d ∈ Q.divisors, moebiusReal d * (d : ℝ) ^ (-ε)) := by
        rw [sum_divisors_prime_mul_real (fun d => moebiusReal d * (d : ℝ) ^ (-ε)) hp hpQ,
          sub_mul, one_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun d hd => ?_
        have hpd : ¬ p ∣ d := fun h => hpQ (h.trans (Nat.dvd_of_mem_divisors hd))
        have hmu : moebiusReal (p * d) = -moebiusReal d := by
          simpa [moebiusReal, hpd] using Sieve.moebius_prime_mul (e := d) hp
        rw [hmu, Nat.cast_mul, Real.mul_rpow hp0.le (Nat.cast_nonneg d)]
        ring
      have hloc :
          ((p : ℝ) ^ (1 + ε) / ((p : ℝ) ^ (1 + ε) - 1)) * (1 - (p : ℝ) ^ (-ε)) =
            ((p : ℝ) ^ (1 + ε) - p) / ((p : ℝ) ^ (1 + ε) - 1) := by
        have hrpow : (p : ℝ) ^ (1 + ε) * (p : ℝ) ^ (-ε) = p := by
          rw [← Real.rpow_add hp0, add_neg_cancel_right, Real.rpow_one]
        field_simp
        linear_combination -hrpow
      rw [hdiv]
      linear_combination
        (pmEulerCubeFactor ε Q * ∑ d ∈ Q.divisors, moebiusReal d * (d : ℝ) ^ (-ε)) * hloc
  rw [heq]
  refine ⟨rfl, ?_, ?_⟩
  · refine prod_pos fun p hp => ?_
    have hpP : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpP.one_lt
    have hgt : (p : ℝ) < (p : ℝ) ^ (1 + ε) := by
      calc (p : ℝ) = (p : ℝ) ^ (1 : ℝ) := (Real.rpow_one (p : ℝ)).symm
        _ < (p : ℝ) ^ (1 + ε) := Real.rpow_lt_rpow_of_exponent_lt hp1 (by linarith)
    exact div_pos (by linarith) (by linarith)
  · refine prod_le_one (fun p hp => ?_) (fun p hp => ?_)
    · have hpP : p.Prime := (Nat.mem_primeFactors.mp hp).1
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hpP.one_lt
      have hgt : (p : ℝ) < (p : ℝ) ^ (1 + ε) := by
        calc (p : ℝ) = (p : ℝ) ^ (1 : ℝ) := (Real.rpow_one (p : ℝ)).symm
          _ < (p : ℝ) ^ (1 + ε) := Real.rpow_lt_rpow_of_exponent_lt hp1 (by linarith)
      exact div_nonneg (by linarith) (by linarith)
    · have hpP : p.Prime := (Nat.mem_primeFactors.mp hp).1
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hpP.one_lt
      have hgt : (p : ℝ) < (p : ℝ) ^ (1 + ε) := by
        calc (p : ℝ) = (p : ℝ) ^ (1 : ℝ) := (Real.rpow_one (p : ℝ)).symm
          _ < (p : ℝ) ^ (1 + ε) := Real.rpow_lt_rpow_of_exponent_lt hp1 (by linarith)
      exact (div_le_one (by linarith)).mpr (by linarith)

/-- **Exact Cross-Depth `ζ(1+ε) ζ(1+ε)⁻¹ = 1` Cancellation and Residue-Gap Decomposition of the
Hypercube Gram Form (`hypercubeGram_eq_cancelled_diag_sub_residueGap`):**
Across the $2^{\omega(P)} \times 2^{\omega(P)}$ hypercube of depths $m_1, m_2 \mid P$, the finite
cancellation $\mathrm{pmEulerCubeFactor}(\varepsilon, P)\sum_{d \mid P}\mu(d)d^{-1-\varepsilon} = 1$
cancels one factor of $\mathrm{pmEulerCubeFactor}(\varepsilon, P)$ from the diagonal main term,
reducing its prefactor to the cutoff-uniform product
$\prod_{p \mid P}\frac{p^{1+\varepsilon} - p}{p^{1+\varepsilon} - 1} \in (0, 1]$ and leaving the
pairwise scaled residue-gap form. -/
theorem hypercubeGram_eq_cancelled_diag_sub_residueGap {ε : ℝ} (hε : 0 < ε)
    {P r : ℕ} (hP : Squarefree P) (hr : 1 < r) (hPr : Nat.Coprime P r) :
    (∑ m₁ ∈ P.divisors, ∑ m₂ ∈ P.divisors,
        pmRealRamanujanWeight ε (m₁ * r) * pmRealRamanujanWeight ε (m₂ * r) *
          pmRamanujanPrimitiveGram (m₁ * r) (m₂ * r)) =
      pmRealRamanujanWeight ε r ^ 2 *
          (pmEulerCubeFactor ε P * ∑ d ∈ P.divisors, moebiusReal d * (d : ℝ) ^ (-ε)) *
          pmRamanujanPrimitiveGram r r -
        (1 / 2) * pmEulerCubeFactor ε P ^ 2 * pmRealRamanujanWeight ε r ^ 2 *
          ∑ d₁ ∈ P.divisors, ∑ d₂ ∈ P.divisors,
            (moebiusReal d₁ * (d₁ : ℝ) ^ (-1 - ε)) *
              (moebiusReal d₂ * (d₂ : ℝ) ^ (-1 - ε)) *
              (((d₁ : ℝ) + d₂) * pmRamanujanPrimitiveGram r r -
                2 * Real.sqrt d₁ * Real.sqrt d₂ *
                  pmRamanujanDilationProfile r hr ((d₁ : ℝ) / d₂)) := by
  rw [all_depth_coherent_primitiveGram_cube_eq hε hP hr hPr]
  let w : ℕ → ℝ := fun d => moebiusReal d * (d : ℝ) ^ (-1 - ε)
  have hw_term :
      ∀ d₁ ∈ P.divisors, ∀ d₂ ∈ P.divisors,
        (moebiusReal d₁ * (d₁ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
            (moebiusReal d₂ * (d₂ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
            pmRamanujanDilationProfile r hr ((d₁ : ℝ) / d₂) =
          w d₁ * w d₂ * Real.sqrt d₁ * Real.sqrt d₂ *
            pmRamanujanDilationProfile r hr ((d₁ : ℝ) / d₂) := by
    intro d₁ hd₁ d₂ hd₂
    have hd₁0 : (0 : ℝ) < d₁ := by exact_mod_cast (Nat.pos_of_mem_divisors hd₁)
    have hd₂0 : (0 : ℝ) < d₂ := by exact_mod_cast (Nat.pos_of_mem_divisors hd₂)
    have h1 : (d₁ : ℝ) ^ (-1 - ε) * Real.sqrt d₁ = (d₁ : ℝ) ^ (-(1 / 2 : ℝ) - ε) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hd₁0]
      congr 1; ring
    have h2 : (d₂ : ℝ) ^ (-1 - ε) * Real.sqrt d₂ = (d₂ : ℝ) ^ (-(1 / 2 : ℝ) - ε) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hd₂0]
      congr 1; ring
    dsimp [w]
    linear_combination
      moebiusReal d₁ * moebiusReal d₂ * pmRamanujanDilationProfile r hr ((d₁ : ℝ) / d₂) *
        ((d₂ : ℝ) ^ (-(1 / 2 : ℝ) - ε) * h1.symm +
          (d₁ : ℝ) ^ (-1 - ε) * Real.sqrt d₁ * h2.symm)
  have hsum_eq :
      (∑ d₁ ∈ P.divisors, ∑ d₂ ∈ P.divisors,
          (moebiusReal d₁ * (d₁ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
            (moebiusReal d₂ * (d₂ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
            pmRamanujanDilationProfile r hr ((d₁ : ℝ) / d₂)) =
        ∑ d₁ ∈ P.divisors, ∑ d₂ ∈ P.divisors,
          w d₁ * w d₂ * Real.sqrt d₁ * Real.sqrt d₂ *
            pmRamanujanDilationProfile r hr ((d₁ : ℝ) / d₂) :=
    sum_congr rfl fun d₁ hd₁ => sum_congr rfl fun d₂ hd₂ => hw_term d₁ hd₁ d₂ hd₂
  have hw1 :
      ∑ d ∈ P.divisors, (d : ℝ) * w d = ∑ d ∈ P.divisors, moebiusReal d * (d : ℝ) ^ (-ε) := by
    refine sum_congr rfl fun d hd => ?_
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (Nat.pos_of_mem_divisors hd)
    have hrpow : (d : ℝ) * (d : ℝ) ^ (-1 - ε) = (d : ℝ) ^ (-ε) := by
      calc (d : ℝ) * (d : ℝ) ^ (-1 - ε)
          = (d : ℝ) ^ (1 : ℝ) * (d : ℝ) ^ (-1 - ε) := by rw [Real.rpow_one]
        _ = (d : ℝ) ^ ((1 : ℝ) + (-1 - ε)) := (Real.rpow_add hd0 1 (-1 - ε)).symm
        _ = (d : ℝ) ^ (-ε) := by congr 1; ring
    dsimp [w]
    linear_combination moebiusReal d * hrpow
  have hcancel : pmEulerCubeFactor ε P * (∑ d ∈ P.divisors, w d) = 1 :=
    pmEulerCubeFactor_mul_dirichlet_moebius_sum_eq_one hε hP
  rw [hsum_eq, scaled_dilationProfile_packet_eq_diag_sub_gap hr P.divisors w, hw1]
  dsimp [w] at hcancel ⊢
  linear_combination
    pmEulerCubeFactor ε P * pmRealRamanujanWeight ε r ^ 2 *
      (∑ d ∈ P.divisors, moebiusReal d * (d : ℝ) ^ (-ε)) *
      pmRamanujanPrimitiveGram r r * hcancel

/-- **Cutoff-Uniform Bound on the Hypercube Dilation-Profile Diagonal (`all_depth_dilationProfile_cube_diag_sum_le_tsum`):**
For every `ε > 0`, every squarefree cutoff `P`, and every modulus `r > 1`, the diagonal of
`hypercubeDilationDirichletForm ε P r hr` is bounded **uniformly in `P`** by
`(∑' n : ℕ, (n : ℝ) ^ (-1 - 2 * ε)) * G(r, r)`. -/
theorem all_depth_dilationProfile_cube_diag_sum_le_tsum {ε : ℝ} (hε : 0 < ε)
    {P r : ℕ} (hP : Squarefree P) (hr : 1 < r) :
    (∑ d ∈ P.divisors,
        (moebiusReal d * (d : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
          (moebiusReal d * (d : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
          pmRamanujanDilationProfile r hr ((d : ℝ) / d)) ≤
      (∑' n : ℕ, (n : ℝ) ^ (-1 - 2 * ε)) * pmRamanujanPrimitiveGram r r := by
  rw [all_depth_dilationProfile_cube_diag_sum_eq ε hP hr]
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-1 - 2 * ε)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  exact mul_le_mul_of_nonneg_right
    (hsum.sum_le_tsum P.divisors fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)
    (pmRamanujanPrimitiveGram_pos hr).le

/-- **Cutoff-Uniform Bound on the Full Hypercube Dilation Dirichlet Form Above Half Damping
(`hypercubeDilationDirichletForm_le_tsum_sq_of_half_lt`):**
For every `ε > 1 / 2`, every cutoff `P : ℕ`, and every modulus `r > 1`, the full Dirichlet form
`hypercubeDilationDirichletForm ε P r hr` is bounded **uniformly in `P`** by
`(∑' n : ℕ, (n : ℝ) ^ (-(1 / 2) - ε)) ^ 2 * G(r, r)`. -/
theorem hypercubeDilationDirichletForm_le_tsum_sq_of_half_lt {ε : ℝ} (hε : 1 / 2 < ε)
    (P : ℕ) {r : ℕ} (hr : 1 < r) :
    hypercubeDilationDirichletForm ε P r hr ≤
      (∑' n : ℕ, (n : ℝ) ^ (-(1 / 2 : ℝ) - ε)) ^ 2 * pmRamanujanPrimitiveGram r r := by
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 / 2 : ℝ) - ε)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hdiv_le :
      (∑ d ∈ P.divisors, (d : ℝ) ^ (-(1 / 2 : ℝ) - ε)) ≤
        ∑' n : ℕ, (n : ℝ) ^ (-(1 / 2 : ℝ) - ε) :=
    hsum.sum_le_tsum P.divisors fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hG0 : 0 ≤ pmRamanujanPrimitiveGram r r := (pmRamanujanPrimitiveGram_pos hr).le
  have hterm :
      ∀ d₁ ∈ P.divisors, ∀ d₂ ∈ P.divisors,
        (moebiusReal d₁ * (d₁ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
            (moebiusReal d₂ * (d₂ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
            pmRamanujanDilationProfile r hr ((d₁ : ℝ) / d₂) ≤
          (d₁ : ℝ) ^ (-(1 / 2 : ℝ) - ε) * (d₂ : ℝ) ^ (-(1 / 2 : ℝ) - ε) *
            pmRamanujanPrimitiveGram r r := by
    intro d₁ hd₁ d₂ hd₂
    have hd₁0 : (0 : ℝ) < d₁ := by exact_mod_cast (Nat.pos_of_mem_divisors hd₁)
    have hd₂0 : (0 : ℝ) < d₂ := by exact_mod_cast (Nat.pos_of_mem_divisors hd₂)
    have h1 : |moebiusReal d₁ * (d₁ : ℝ) ^ (-(1 / 2 : ℝ) - ε)| ≤ (d₁ : ℝ) ^ (-(1 / 2 : ℝ) - ε) := by
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hd₁0 _)]
      exact mul_le_of_le_one_left (by positivity) (abs_moebiusReal_le_one d₁)
    have h2 : |moebiusReal d₂ * (d₂ : ℝ) ^ (-(1 / 2 : ℝ) - ε)| ≤ (d₂ : ℝ) ^ (-(1 / 2 : ℝ) - ε) := by
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hd₂0 _)]
      exact mul_le_of_le_one_left (by positivity) (abs_moebiusReal_le_one d₂)
    have h3 : |pmRamanujanDilationProfile r hr ((d₁ : ℝ) / d₂)| ≤ pmRamanujanPrimitiveGram r r :=
      abs_pmRamanujanDilationProfile_le hr (div_pos hd₁0 hd₂0)
    calc (moebiusReal d₁ * (d₁ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
            (moebiusReal d₂ * (d₂ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
            pmRamanujanDilationProfile r hr ((d₁ : ℝ) / d₂)
        ≤ |(moebiusReal d₁ * (d₁ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
            (moebiusReal d₂ * (d₂ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
            pmRamanujanDilationProfile r hr ((d₁ : ℝ) / d₂)| := le_abs_self _
      _ = |moebiusReal d₁ * (d₁ : ℝ) ^ (-(1 / 2 : ℝ) - ε)| *
            |moebiusReal d₂ * (d₂ : ℝ) ^ (-(1 / 2 : ℝ) - ε)| *
            |pmRamanujanDilationProfile r hr ((d₁ : ℝ) / d₂)| := by rw [abs_mul, abs_mul]
      _ ≤ (d₁ : ℝ) ^ (-(1 / 2 : ℝ) - ε) * (d₂ : ℝ) ^ (-(1 / 2 : ℝ) - ε) *
            pmRamanujanPrimitiveGram r r :=
          mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (by positivity)) h3 (abs_nonneg _)
            (by positivity)
  unfold hypercubeDilationDirichletForm
  calc (∑ d₁ ∈ P.divisors, ∑ d₂ ∈ P.divisors,
          (moebiusReal d₁ * (d₁ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
            (moebiusReal d₂ * (d₂ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
            pmRamanujanDilationProfile r hr ((d₁ : ℝ) / d₂))
      ≤ ∑ d₁ ∈ P.divisors, ∑ d₂ ∈ P.divisors,
          (d₁ : ℝ) ^ (-(1 / 2 : ℝ) - ε) * (d₂ : ℝ) ^ (-(1 / 2 : ℝ) - ε) *
            pmRamanujanPrimitiveGram r r :=
        sum_le_sum fun d₁ hd₁ => sum_le_sum fun d₂ hd₂ => hterm d₁ hd₁ d₂ hd₂
    _ = (∑ d ∈ P.divisors, (d : ℝ) ^ (-(1 / 2 : ℝ) - ε)) ^ 2 * pmRamanujanPrimitiveGram r r := by
        rw [sq, sum_mul, sum_mul]
        refine sum_congr rfl fun d₁ _ => ?_
        rw [mul_sum, sum_mul]
    _ ≤ (∑' n : ℕ, (n : ℝ) ^ (-(1 / 2 : ℝ) - ε)) ^ 2 * pmRamanujanPrimitiveGram r r :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (sum_nonneg fun _ _ => by positivity) hdiv_le 2) hG0

/-- **The Physical-Space Dirichlet Dilation Primitive (`dirichletDilationPrimitive`):**
The discrete dilation polynomial `∑_{d ∣ P} μ(d) d^{-ε} Re S_r(⌊N / d⌋)` produced by the all-depth
Euler–Dirichlet factorization `all_depth_coherent_pmRamanujanPrimitive_eq`. -/
def dirichletDilationPrimitive (ε : ℝ) (P r N : ℕ) : ℝ :=
  ∑ d ∈ P.divisors, moebiusReal d * (d : ℝ) ^ (-ε) * (pmRamanujanPrimitive r (N / d)).re

/-- **Exact Support Truncation of the Dirichlet Dilation Primitive (`dirichletDilationPrimitive_eq_filter_le`):**
For every horizon `H` and every `N ≤ H`, every divisor `d ∣ P` with `d > H` has `⌊N / d⌋ = 0` and
`pmRamanujanPrimitive r 0 = 0`, so `dirichletDilationPrimitive ε P r N` truncates identically to
divisors `d ≤ H`. -/
theorem dirichletDilationPrimitive_eq_filter_le (ε : ℝ) (P r : ℕ) {H N : ℕ} (hNH : N ≤ H) :
    dirichletDilationPrimitive ε P r N =
      ∑ d ∈ P.divisors.filter (· ≤ H),
        moebiusReal d * (d : ℝ) ^ (-ε) * (pmRamanujanPrimitive r (N / d)).re := by
  unfold dirichletDilationPrimitive
  symm
  refine sum_subset (filter_subset _ _) fun d hd hnot => ?_
  have hdH : H < d := not_le.mp fun hle => hnot (mem_filter.mpr ⟨hd, hle⟩)
  have hdiv : N / d = 0 := Nat.div_eq_of_lt (lt_of_le_of_lt hNH hdH)
  simp [hdiv, pmRamanujanPrimitive]

/-- **Cutoff-Uniform Pointwise Bound on the Dirichlet Dilation Primitive at Every `ε ≥ 0`
(`abs_dirichletDilationPrimitive_le_uniform_in_cutoff`):**
For every `ε ≥ 0`, every cutoff `P : ℕ` (arbitrarily large), every `r > 1`, and every `N ≤ H`,
`|dirichletDilationPrimitive ε P r N| ≤ pmRamanujanPrimitiveBound r * H` **independently of `P`**. -/
theorem abs_dirichletDilationPrimitive_le_uniform_in_cutoff {ε : ℝ} (hε : 0 ≤ ε)
    (P : ℕ) {r : ℕ} (hr : 1 < r) {H N : ℕ} (hNH : N ≤ H) :
    |dirichletDilationPrimitive ε P r N| ≤ pmRamanujanPrimitiveBound r * H := by
  rw [dirichletDilationPrimitive_eq_filter_le ε P r hNH]
  have hsub : P.divisors.filter (· ≤ H) ⊆ Icc 1 H := fun d hd => by
    have hm := mem_filter.mp hd
    exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hm.1, hm.2⟩
  have hcard : ((P.divisors.filter (· ≤ H)).card : ℝ) ≤ H := by
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc, show H + 1 - 1 = H by omega] at this
    exact_mod_cast this
  have hB0 : 0 ≤ pmRamanujanPrimitiveBound r := sum_nonneg fun _ _ => norm_nonneg _
  calc |∑ d ∈ P.divisors.filter (· ≤ H),
          moebiusReal d * (d : ℝ) ^ (-ε) * (pmRamanujanPrimitive r (N / d)).re|
      ≤ ∑ d ∈ P.divisors.filter (· ≤ H),
          |moebiusReal d * (d : ℝ) ^ (-ε) * (pmRamanujanPrimitive r (N / d)).re| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ P.divisors.filter (· ≤ H), pmRamanujanPrimitiveBound r := by
        refine sum_le_sum fun d hd => ?_
        have hd1 : (1 : ℝ) ≤ d := by
          exact_mod_cast Nat.pos_of_mem_divisors (mem_filter.mp hd).1
        have hd0 : (0 : ℝ) < d := by linarith
        have hrpow : (d : ℝ) ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hd1 (by linarith)
        have hprim : |(pmRamanujanPrimitive r (N / d)).re| ≤ pmRamanujanPrimitiveBound r :=
          (Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr _)
        rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hd0 _)]
        calc |moebiusReal d| * (d : ℝ) ^ (-ε) * |(pmRamanujanPrimitive r (N / d)).re|
            ≤ 1 * 1 * pmRamanujanPrimitiveBound r :=
              mul_le_mul (mul_le_mul (abs_moebiusReal_le_one d) hrpow (by positivity) zero_le_one)
                hprim (abs_nonneg _) (by positivity)
          _ = pmRamanujanPrimitiveBound r := by ring
    _ = ((P.divisors.filter (· ≤ H)).card : ℝ) * pmRamanujanPrimitiveBound r := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (H : ℝ) * pmRamanujanPrimitiveBound r := mul_le_mul_of_nonneg_right hcard hB0
    _ = pmRamanujanPrimitiveBound r * H := mul_comm _ _

/-- **Cutoff-Uniform Head Energy and Forced Tail-Mean Bound for the Dirichlet Dilation Primitive
at Every `ε ≥ 0` (`dirichletDilationHeadEnergy_and_tailMean_le_uniform_in_cutoff`):**
For every `ε ≥ 0`, every cutoff `P : ℕ` (arbitrarily large), every `r > 1`, and every horizon `H : ℕ`,
the finite-prefix pronic head energy of `dirichletDilationPrimitive ε P r` on `0 ≤ n ≤ H` is bounded
by `(pmRamanujanPrimitiveBound r * H) ^ 2` and its forced conditional tail-mean energy is bounded by
`pmRamanujanPrimitiveBound r ^ 2 * (H : ℝ) ^ 3`, **independently of the cutoff `P`**. -/
theorem dirichletDilationHeadEnergy_and_tailMean_le_uniform_in_cutoff {ε : ℝ} (hε : 0 ≤ ε)
    (P : ℕ) {r : ℕ} (hr : 1 < r) (H : ℕ) :
    (∑ n ∈ range (H + 1),
        (dirichletDilationPrimitive ε P r n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤
      (pmRamanujanPrimitiveBound r * H) ^ 2 ∧
    ((H : ℝ) + 1) *
        (∑ n ∈ range (H + 1),
          dirichletDilationPrimitive ε P r n / ((n : ℝ) * ((n : ℝ) + 1))) ^ 2 ≤
      pmRamanujanPrimitiveBound r ^ 2 * (H : ℝ) ^ 3 := by
  set M := pmRamanujanPrimitiveBound r * H
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg (sum_nonneg fun _ _ => norm_nonneg _) (Nat.cast_nonneg H)
  have hmass_le : (∑ n ∈ range (H + 1), 1 / ((n : ℝ) * ((n : ℝ) + 1))) ≤ 1 :=
    sum_le_hasSum (range (H + 1)) (fun n _ => by positivity) hasSum_pm_reciprocal_weight
  have hhead :
      (∑ n ∈ range (H + 1),
          (dirichletDilationPrimitive ε P r n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤ M ^ 2 := by
    calc (∑ n ∈ range (H + 1),
            (dirichletDilationPrimitive ε P r n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)))
        ≤ ∑ n ∈ range (H + 1), M ^ 2 * (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
          refine sum_le_sum fun n hn => ?_
          have hnH : n ≤ H := Nat.lt_succ_iff.mp (mem_range.mp hn)
          have hb := abs_dirichletDilationPrimitive_le_uniform_in_cutoff hε P hr hnH
          have hsq : (dirichletDilationPrimitive ε P r n) ^ 2 ≤ M ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) hb 2
          simpa only [mul_one_div] using div_le_div_of_nonneg_right hsq (by positivity)
      _ = M ^ 2 * ∑ n ∈ range (H + 1), 1 / ((n : ℝ) * ((n : ℝ) + 1)) := (mul_sum _ _ _).symm
      _ ≤ M ^ 2 * 1 := mul_le_mul_of_nonneg_left hmass_le (sq_nonneg M)
      _ = M ^ 2 := mul_one _
  refine ⟨hhead, ?_⟩
  have hmean_abs :
      |∑ n ∈ range (H + 1),
          dirichletDilationPrimitive ε P r n / ((n : ℝ) * ((n : ℝ) + 1))| ≤
        M * (1 - 1 / ((H : ℝ) + 1)) := by
    have hrange :
        (∑ n ∈ range (H + 1),
            dirichletDilationPrimitive ε P r n / ((n : ℝ) * ((n : ℝ) + 1))) =
          ∑ n ∈ Ico 1 (H + 1),
            dirichletDilationPrimitive ε P r n / ((n : ℝ) * ((n : ℝ) + 1)) := by
      rw [← sum_range_add_sum_Ico _ (Nat.succ_pos H), sum_range_one]
      simp
    rw [hrange]
    have hIco_mass :
        (∑ n ∈ Ico 1 (H + 1), 1 / ((n : ℝ) * ((n : ℝ) + 1))) = 1 - 1 / ((H : ℝ) + 1) := by
      have := sum_Ico_reciprocal_pronic zero_lt_one (Nat.succ_pos H)
      simpa using this
    calc |∑ n ∈ Ico 1 (H + 1),
            dirichletDilationPrimitive ε P r n / ((n : ℝ) * ((n : ℝ) + 1))|
        ≤ ∑ n ∈ Ico 1 (H + 1),
            |dirichletDilationPrimitive ε P r n / ((n : ℝ) * ((n : ℝ) + 1))| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Ico 1 (H + 1), M * (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
          refine sum_le_sum fun n hn => ?_
          have hnH : n ≤ H := Nat.lt_succ_iff.mp (mem_Ico.mp hn).2
          have hb := abs_dirichletDilationPrimitive_le_uniform_in_cutoff hε P hr hnH
          rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1)),
            mul_one_div]
          exact div_le_div_of_nonneg_right hb (by positivity)
      _ = M * ∑ n ∈ Ico 1 (H + 1), 1 / ((n : ℝ) * ((n : ℝ) + 1)) := (mul_sum _ _ _).symm
      _ = M * (1 - 1 / ((H : ℝ) + 1)) := by rw [hIco_mass]
  have h1_le : 1 - 1 / ((H : ℝ) + 1) ≤ 1 := by
    have : (0 : ℝ) ≤ 1 / ((H : ℝ) + 1) := by positivity
    linarith
  have hsq_mean :
      (∑ n ∈ range (H + 1),
          dirichletDilationPrimitive ε P r n / ((n : ℝ) * ((n : ℝ) + 1))) ^ 2 ≤
        M ^ 2 * (1 - 1 / ((H : ℝ) + 1)) ^ 2 := by
    rw [← sq_abs, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hmean_abs 2
  have hH_mul : ((H : ℝ) + 1) * (1 - 1 / ((H : ℝ) + 1)) ^ 2 ≤ H := by
    have hH_id : ((H : ℝ) + 1) * (1 - 1 / ((H : ℝ) + 1)) = H := by
      have : (H : ℝ) + 1 ≠ 0 := by positivity
      field_simp; ring
    calc ((H : ℝ) + 1) * (1 - 1 / ((H : ℝ) + 1)) ^ 2
        = (((H : ℝ) + 1) * (1 - 1 / ((H : ℝ) + 1))) * (1 - 1 / ((H : ℝ) + 1)) := by ring
      _ = (H : ℝ) * (1 - 1 / ((H : ℝ) + 1)) := by rw [hH_id]
      _ ≤ (H : ℝ) * 1 := mul_le_mul_of_nonneg_left h1_le (Nat.cast_nonneg H)
      _ = H := mul_one _
  calc ((H : ℝ) + 1) *
        (∑ n ∈ range (H + 1),
          dirichletDilationPrimitive ε P r n / ((n : ℝ) * ((n : ℝ) + 1))) ^ 2
      ≤ ((H : ℝ) + 1) * (M ^ 2 * (1 - 1 / ((H : ℝ) + 1)) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq_mean (by positivity)
    _ = M ^ 2 * (((H : ℝ) + 1) * (1 - 1 / ((H : ℝ) + 1)) ^ 2) := by ring
    _ ≤ M ^ 2 * H := mul_le_mul_of_nonneg_left hH_mul (sq_nonneg M)
    _ = pmRamanujanPrimitiveBound r ^ 2 * (H : ℝ) ^ 3 := by dsimp [M]; ring

end

end GaloisForLFunctions.BezoutValuationIncidence
