import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.ThePrimeWaveAtTheWallIsTheBoundedOrderOfTheWallLaw
import GaloisForLFunctions.RHTower.XiPrimeLogHigherValuationCriticalBoundary

/-!
# Proper prime powers in the prime wave

The heads at prime powers of exponent at least two converge normally on the entire open
left half-plane. Completing each head integral to the full transform costs a holomorphic
tail across the imaginary axis. The remaining Euler series has a square contribution at
twice the frequency, which gives residue `-ℒF(0)/2` at zero.

In time coordinates, absolute values suffice to bound the contribution from all proper
powers by every growing exponential on the positive ray.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- The prime power indexed by its prime base and its exponent minus two. -/
abbrev properPrimePowerIndex (j : Nat.Primes × ℕ) := (j.1 : ℕ) ^ (j.2 + 2)

private def eulerAtom (n : ℕ) (p : ℂ) : ℂ :=
  (vonMangoldtAtom n : ℂ) * cexp (p * Real.log n)

private theorem atom_nonneg (n : ℕ) : 0 ≤ vonMangoldtAtom n := by
  unfold vonMangoldtAtom
  split_ifs
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  · exact le_rfl

private theorem norm_eulerAtom (n : ℕ) (p : ℂ) :
    ‖eulerAtom n p‖ = vonMangoldtAtom n * Real.exp (p.re * Real.log n) := by
  rw [eulerAtom, norm_mul, Complex.norm_real, Real.norm_of_nonneg (atom_nonneg _),
    norm_cexp_mul_ofReal]

private theorem summable_properAtoms {p : ℂ} (hp : p.re < 0) :
    Summable fun j => eulerAtom (properPrimePowerIndex j) p := by
  have hs : 1 / 2 < ((1 : ℂ) / 2 - p).re := by simp; linarith
  exact (summable_xiPrimeLogHigherValuation_term_of_half_lt_re hs).congr
    fun j => (vonMangoldtAtom_mul_cexp_eq_term p _).symm

private theorem summable_properWeights {σ : ℝ} (hσ : σ < 0) :
    Summable fun j => vonMangoldtAtom (properPrimePowerIndex j) * Real.exp (σ * Real.log (properPrimePowerIndex j)) := by
  simpa only [norm_eulerAtom, ofReal_re] using
    (summable_properAtoms (p := (σ : ℂ)) (by simpa using hσ)).norm

/-- The subseries of the actual prime head at all proper prime powers. -/
def properPowerHead (F : ℝ → ℝ) (p : ℂ) : ℂ :=
  ∑' j : Nat.Primes × ℕ, eulerAtom (properPrimePowerIndex j) p * levyHead F p (Real.log (properPrimePowerIndex j))

/-- The proper-power heads converge normally for every negative real part. -/
theorem differentiableOn_properPowerHead {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    DifferentiableOn ℂ (properPowerHead F) {p : ℂ | p.re < 0} := by
  intro p hp
  obtain ⟨σ, hlow, hσ⟩ := exists_between (max_lt (show p.re < 0 from hp) (by norm_num : (-4 : ℝ) < 0))
  have hσ4 := (le_max_right p.re (-4)).trans_lt hlow
  have hpσ := (le_max_left p.re (-4)).trans_lt hlow
  have hU : IsOpen {z : ℂ | z.re < σ} := isOpen_lt continuous_re continuous_const
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableOn.differentiableAt _ (hU.mem_nhds hpσ)
  refine Complex.differentiableOn_tsum_of_summable_norm
    ((summable_properWeights hσ).mul_right (∫ u, |F u| * Real.exp (σ * u))) ?_ hU ?_
  · intro j
    unfold eulerAtom
    exact (((by fun_prop : Differentiable ℂ fun z : ℂ => (vonMangoldtAtom (properPrimePowerIndex j) : ℂ) *
      cexp (z * Real.log (properPrimePowerIndex j))).mul (differentiable_levyHead hF _)).differentiableOn)
  · intro j z hz
    simpa only [eulerAtom, mul_assoc] using norm_primeHead_term_le hF hσ4 (le_of_lt hz) (properPrimePowerIndex j)

/-- Split any summable family supported on prime powers into ordinary primes
and the powers with exponent at least two. -/
theorem tsum_eq_ordinary_primes_add_proper_powers {f : ℕ → ℂ} (hf : Summable f)
    (hsupp : Function.support f ⊆ {n : ℕ | IsPrimePow n}) :
    (∑' n, f n) = (∑' q : Nat.Primes, f (q : ℕ)) + ∑' j, f (properPrimePowerIndex j) := by
  have hall := hf.comp_injective eulerPrimePowerNat_injective
  have hq : Summable fun q : Nat.Primes => f (q : ℕ) := hf.comp_injective Subtype.coe_injective
  have htail : Summable fun j : Nat.Primes × ℕ => f (properPrimePowerIndex j) :=
    hall.comp_injective (i := fun j : Nat.Primes × ℕ => (j.1, j.2 + 1))
      (by
        rintro ⟨q, k⟩ ⟨r, l⟩ h
        have hq : q = r := congrArg Prod.fst h
        have hk : k + 1 = l + 1 := congrArg Prod.snd h
        exact Prod.ext hq (Nat.succ.inj hk))
  have hinner (q : Nat.Primes) :
      (∑' k : ℕ, f ((q : ℕ) ^ (k + 1))) = f q + ∑' k : ℕ, f ((q : ℕ) ^ (k + 2)) := by
    have hqk : Summable fun k : ℕ => f ((q : ℕ) ^ (k + 1)) :=
      hall.comp_injective (i := fun k : ℕ => (q, k)) (fun _ _ h => congrArg Prod.snd h)
    simpa only [zero_add, pow_one, add_assoc] using hqk.tsum_eq_zero_add
  rw [tsum_eq_tsum_primes_of_support_subset_prime_powers hf hsupp]
  simp_rw [hinner]
  rw [hq.tsum_add htail.prod, htail.tsum_prod]

/-- On its original half-plane the full head is the sum of the ordinary-prime and
proper-power heads. -/
theorem primeHead_eq_prime_add_properPowerHead {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {p : ℂ} (hp : p.re < -(1 / 2)) :
    primeHead F p = (∑' q : Nat.Primes, (vonMangoldtAtom (q : ℕ) : ℂ) *
      (cexp (p * Real.log (q : ℕ)) * levyHead F p (Real.log (q : ℕ)))) + properPowerHead F p := by
  let f (n : ℕ) := eulerAtom n p * levyHead F p (Real.log n)
  obtain ⟨σ, hσp, hσ⟩ := exists_between
    (max_lt hp (by norm_num : (-4 : ℝ) < -(1 / 2)))
  have hf : Summable f := by
    apply Summable.of_norm_bounded (summable_primeHead_bound (F := F) hσ)
    intro n
    simpa only [f, eulerAtom, mul_assoc] using
      norm_primeHead_term_le hF ((le_max_right _ _).trans_lt hσp)
        ((le_max_left _ _).trans hσp.le) n
  have hsupp : Function.support f ⊆ {n : ℕ | IsPrimePow n} := by
    intro n hn
    apply vonMangoldtLSeriesTerm_support_primePower (1 / 2 - p)
    intro h
    apply hn
    simp only [f, eulerAtom, vonMangoldtAtom_mul_cexp_eq_term, h, zero_mul]
  have hfull := tsum_eq_ordinary_primes_add_proper_powers hf hsupp
  simpa only [primeHead, properPowerHead, f, eulerAtom, mul_assoc] using hfull

private def properTailTerm (F : ℝ → ℝ) (j : Nat.Primes × ℕ) (p : ℂ) : ℂ :=
  eulerAtom (properPrimePowerIndex j) p * levyTail F p (Real.log (properPrimePowerIndex j))

private theorem norm_properTailTerm_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {σ : ℝ} (hσ : -4 < σ) (j : Nat.Primes × ℕ) {p : ℂ} (hp : σ ≤ p.re) :
    ‖properTailTerm F j p‖ ≤ (vonMangoldtAtom (properPrimePowerIndex j) *
      Real.exp (-4 * Real.log (properPrimePowerIndex j))) *
        (((∫ u, F u ^ 2 * Real.exp (-(8 * u))) + 1 / (2 * σ + 8)) / 2) := by
  simpa only [properTailTerm, eulerAtom, levyTail, mul_assoc, neg_mul,
    mul_comm (cexp (p * _)) (ofReal (F _))] using norm_stateTail_term_le_of hF hσ hp (properPrimePowerIndex j)

private theorem differentiableAt_properTail {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {p : ℂ} (hp : -4 < p.re) :
    DifferentiableAt ℂ (fun z => ∑' j, properTailTerm F j z) p := by
  obtain ⟨σ, hσ, hσp⟩ := exists_between hp
  have hU : IsOpen {z : ℂ | σ < z.re} := isOpen_lt continuous_const continuous_re
  apply DifferentiableOn.differentiableAt _ (hU.mem_nhds hσp)
  refine Complex.differentiableOn_tsum_of_summable_norm
    ((summable_properWeights (by norm_num : (-4 : ℝ) < 0)).mul_right
      (((∫ u, F u ^ 2 * Real.exp (-(8 * u))) + 1 / (2 * σ + 8)) / 2)) ?_ hU ?_
  · intro j
    apply DifferentiableOn.mul
    · unfold eulerAtom
      fun_prop
    · exact (differentiableOn_levyTail hF _).mono fun z hz => hσ.trans hz
  · exact fun j z hz => norm_properTailTerm_le hF hσ j (le_of_lt hz)

/-- Completing the head integrals leaves the scalar higher-valuation Euler series. -/
def properPowerHeadContinuation (F : ℝ → ℝ) (p : ℂ) : ℂ :=
  xiPrimeLogHigherValuationCriticalContinuation (1 / 2 - p) *
    negativeHalfLineLaplace (cx F) p - ∑' j, properTailTerm F j p

theorem properPowerHeadContinuation_eq {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {p : ℂ} (hp4 : -4 < p.re) (hp : p.re < 0) :
    properPowerHeadContinuation F p = properPowerHead F p := by
  have hs : 1 / 2 < ((1 : ℂ) / 2 - p).re := by simp; linarith
  have he : (∑' j, eulerAtom (properPrimePowerIndex j) p) = xiPrimeLogHigherValuation (1 / 2 - p) :=
    tsum_congr fun j => vonMangoldtAtom_mul_cexp_eq_term p _
  have ht : Summable fun j => properTailTerm F j p :=
    Summable.of_norm_bounded ((summable_properWeights (by norm_num : (-4 : ℝ) < 0)).mul_right _)
      (fun j => norm_properTailTerm_le hF hp4 j le_rfl)
  rw [properPowerHeadContinuation, xiPrimeLogHigherValuationCriticalContinuation_eq hs,
    ← he, ← tsum_mul_right, ← ((summable_properAtoms hp).mul_right _).tsum_sub ht]
  apply tsum_congr
  intro j
  rw [laplace_eq_levyTail_add hF hp4 (Real.log (properPrimePowerIndex j))]
  unfold properTailTerm levyHead
  ring

private theorem diff_laplace {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {p : ℂ} (hp : -4 < p.re) : DifferentiableAt ℂ (negativeHalfLineLaplace (cx F)) p :=
  differentiableAt_laplace_of_sq hF hF.exponential (by linarith)

/-- The continuation crosses the imaginary axis at every nonzero frequency. -/
theorem differentiableAt_properPowerHeadContinuation_of_re_zero {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {p : ℂ} (hre : p.re = 0) (hp : p ≠ 0) :
    DifferentiableAt ℂ (properPowerHeadContinuation F) p := by
  have hs : ((1 : ℂ) / 2 - p).re = 1 / 2 := by simp [hre]
  have hne : 2 * ((1 : ℂ) / 2 - p) ≠ 1 := fun h => hp (by linear_combination -h / 2)
  have hζ : riemannZeta (2 * ((1 : ℂ) / 2 - p)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp [hre])
  exact (((differentiableAt_xiPrimeLogHigherValuationCriticalContinuation (by rw [hs]; norm_num)
    hne hζ).comp p (by fun_prop)).mul (diff_laplace hF (by linarith))).sub
      (differentiableAt_properTail hF (by linarith))

/-- Multiplication by the frequency removes the square pole, with value `-ℒF(0)/2`. -/
theorem properPowerHeadContinuation_residue {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧ G 0 = -negativeHalfLineLaplace (cx F) 0 / 2 ∧
      ∀ᶠ p in 𝓝[≠] (0 : ℂ), G p = p * properPowerHeadContinuation F p := by
  let d : ℂ → ℂ := fun p => 1 - 2 * p
  let s : ℂ → ℂ := fun p => 1 / 2 - p
  have ed (p : ℂ) : 2 * s p = d p := by dsimp [d, s]; ring
  have hd : AnalyticAt ℂ d 0 := by dsimp [d]; fun_prop
  have hs : AnalyticAt ℂ s 0 := by dsimp [s]; fun_prop
  have hd0 : d 0 = 1 := by simp [d]
  have hs0 : s 0 = 1 / 2 := by simp [s]
  have hG1 : zetaResidueUnit 1 ≠ 0 := by rw [zetaResidueUnit_one]; norm_num
  have hlog : AnalyticAt ℂ (logDeriv zetaResidueUnit) (d 0) := by
    rw [hd0]
    exact zetaResidueUnit_analyticAt.deriv.div zetaResidueUnit_analyticAt hG1
  have hhigh : AnalyticAt ℂ xiPrimeLogHigherValuation (d 0) := by
    apply differentiableOn_xiPrimeLogHigherValuation_halfPlane.analyticOnNhd
      (isOpen_lt continuous_const continuous_re)
    rw [hd0]
    norm_num
  have hthree : AnalyticAt ℂ xiPrimeLogHigherValuationThreePlus (s 0) := by
    have hD : DifferentiableOn ℂ xiPrimeLogHigherValuationThreePlus {z : ℂ | 1 / 3 < z.re} :=
      fun z hz => (differentiableAt_xiPrimeLogHigherValuationThreePlus hz).differentiableWithinAt
    exact hD.analyticOnNhd (isOpen_lt continuous_const continuous_re) _ (by rw [hs0]; norm_num)
  let R := fun p => -logDeriv zetaResidueUnit (d p) - xiPrimeLogHigherValuation (d p) +
    xiPrimeLogHigherValuationThreePlus (s p)
  have hR : AnalyticAt ℂ R 0 := (((hlog.comp hd).neg.sub (hhigh.comp hd)).add (hthree.comp hs))
  have hL : AnalyticAt ℂ (negativeHalfLineLaplace (cx F)) 0 :=
    ((differentiableOn_laplace_of_sq hF.meas hF.support hF.exponential).analyticOnNhd
      (isOpen_lt continuous_const continuous_re)) 0 (by norm_num)
  have hT : AnalyticAt ℂ (fun z => ∑' j, properTailTerm F j z) 0 := by
    have hD : DifferentiableOn ℂ (fun z => ∑' j, properTailTerm F j z) {p : ℂ | -4 < p.re} :=
      fun z hz => (differentiableAt_properTail hF hz).differentiableWithinAt
    exact hD.analyticOnNhd (isOpen_lt continuous_const continuous_re) _ (by norm_num)
  refine ⟨fun p => (-(1 / 2) + p * R p) * negativeHalfLineLaplace (cx F) p -
    p * ∑' j, properTailTerm F j p, ((analyticAt_const.add (analyticAt_id.mul hR)).mul hL).sub
      (analyticAt_id.mul hT), by simp; ring, ?_⟩
  have hunit : ∀ᶠ p in 𝓝 (0 : ℂ), zetaResidueUnit (d p) ≠ 0 := by
    have h := hd.continuousAt.tendsto
    rw [hd0] at h
    exact h.eventually zetaResidueUnit_ne_zero_eventually
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hunit] with p hp hu
  have hp0 : p ≠ 0 := hp
  have hne : d p ≠ 1 := fun h => hp0 (by dsimp [d] at h; linear_combination -h / 2)
  change _ = p * (xiPrimeLogHigherValuationCriticalContinuation (s p) *
    negativeHalfLineLaplace (cx F) p - _)
  rw [xiPrimeLogHigherValuationCriticalContinuation, ed, infinitePrimeFlux, logDeriv_zeta_eq hne hu]
  dsimp only [R, d]
  field_simp [show 1 - 2 * p - 1 ≠ 0 by intro h; exact hp0 (by linear_combination -h / 2)]
  ring

/-- Exponential confinement of a profile bounds the absolute sum of its
proper-power translates at every real time, with the same exponent. -/
theorem properPowerWave_absolute_envelope {Φ : ℝ → ℝ} {a C : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (a*u)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ,
      (Summable fun j => vonMangoldtAtom (properPrimePowerIndex j)*|Φ (x-Real.log (properPrimePowerIndex j))|) ∧
      (∑' j, vonMangoldtAtom (properPrimePowerIndex j)*|Φ (x-Real.log (properPrimePowerIndex j))|) ≤
        B*Real.exp (a*x) := by
  let w := fun j => vonMangoldtAtom (properPrimePowerIndex j)*Real.exp (-a*Real.log (properPrimePowerIndex j))
  have hw : Summable w := summable_properWeights (neg_lt_zero.mpr ha)
  refine ⟨(∑' j, w j)*C,mul_nonneg
    (tsum_nonneg fun j => mul_nonneg (atom_nonneg _) (Real.exp_pos _).le) hC,fun x => ?_⟩
  have hbound (j : Nat.Primes × ℕ) :
      vonMangoldtAtom (properPrimePowerIndex j)*|Φ (x-Real.log (properPrimePowerIndex j))| ≤ w j*(C*Real.exp (a*x)) := by
    let l := Real.log (properPrimePowerIndex j)
    apply (mul_le_mul_of_nonneg_left (hb (x-l)) (atom_nonneg _)).trans_eq
    change vonMangoldtAtom _*(C*Real.exp (a*(x-l)))=(vonMangoldtAtom _*Real.exp (-a*l))*(C*Real.exp (a*x))
    rw [show a*(x-l)= -a*l+a*x by ring,Real.exp_add]
    ring
  have hs := Summable.of_nonneg_of_le (fun j => mul_nonneg (atom_nonneg _) (abs_nonneg _)) hbound (hw.mul_right _)
  exact ⟨hs,(hs.tsum_le_tsum hbound (hw.mul_right _)).trans_eq (by rw [tsum_mul_right,mul_assoc])⟩

/-- For the continuous representative of a critical state, the proper-power wave is
absolutely subexponential on the entire positive ray. -/
theorem criticalState_properPowerWave_subexponential {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ Φ : ℝ → ℝ, Continuous Φ ∧ F =ᵐ[volume] Φ ∧ ∀ ε : ℝ, 0 < ε →
      ∃ B : ℝ, ∀ x : ℝ, 0 ≤ x →
        (Summable fun j : Nat.Primes × ℕ => vonMangoldtAtom (properPrimePowerIndex j) *
          |Φ (x - Real.log (properPrimePowerIndex j))|) ∧
        (∑' j : Nat.Primes × ℕ, vonMangoldtAtom (properPrimePowerIndex j) *
          |Φ (x - Real.log (properPrimePowerIndex j))|) ≤ B * Real.exp (ε * x) := by
  obtain ⟨_, _, Φ, hcont, heq, hsupp, ⟨C, hC, hΦ⟩, _⟩ :=
    criticalState_exists_continuous_representative hW ht hF
  refine ⟨Φ, hcont, heq, fun ε hε => ?_⟩
  let a := min ε 2
  have ha : 0 < a := lt_min hε (by norm_num)
  have hφ (u : ℝ) : |Φ u| ≤ C*Real.exp (a*u) := by
    rcases le_or_gt 0 u with hu | hu
    · rw [hsupp _ hu,abs_zero]; positivity
    · exact (hΦ u).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_right (min_le_right ε 2) hu.le)) hC)
  obtain ⟨B,hB,h⟩ := properPowerWave_absolute_envelope ha hC hφ
  refine ⟨B,fun x hx => ⟨(h x).1,(h x).2.trans ?_⟩⟩
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (min_le_left ε 2) hx)) hB

/-- Every positive damping exponent makes the signed proper-power wave of the
state square-integrable. Translation of its continuous representative preserves
the pointwise series simultaneously for all integer shifts almost everywhere. -/
theorem criticalState_memLp_damped_properPowerWave {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {s : ℝ} (hs : 0 < s) :
    MemLp (fun t : ℝ => expRay (s:ℂ) t * ∑' j : Nat.Primes × ℕ,
      (primeAtom (properPrimePowerIndex j):ℂ)*(F (t - Real.log (properPrimePowerIndex j)):ℂ))
      2 halfLineLaplaceMeasure := by
  obtain ⟨Φ,hΦ,heq,hbound⟩ := criticalState_properPowerWave_subexponential hW ht hF
  let d := s/2
  have hd : 0 < d := half_pos hs
  obtain ⟨B,hB⟩ := hbound d hd
  let f := fun (j : Nat.Primes × ℕ) (t : ℝ) =>
    (primeAtom (properPrimePowerIndex j):ℂ)*(Φ (t-Real.log (properPrimePowerIndex j)):ℂ)
  have hn (j t) : ‖f j t‖ = vonMangoldtAtom (properPrimePowerIndex j) *
      |Φ (t-Real.log (properPrimePowerIndex j))| := by
    change ‖(vonMangoldtAtom _:ℂ)*(Φ _:ℂ)‖ = _
    rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg (atom_nonneg _),Real.norm_eq_abs]
  have hm : Measurable fun t => ∑' j, f j t := Measurable.tsum fun j => by
    dsimp [f]; fun_prop
  have hbase := (memLp_two_expRay_restrict (w := (d:ℂ)) (by simpa using hd) 0).const_mul (B:ℂ)
  have hp : MemLp (fun t : ℝ => expRay (s:ℂ) t * ∑' j, f j t) 2 halfLineLaplaceMeasure := by
    apply hbase.mono ((continuous_expRay _).measurable.mul hm).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht
    have hsum : Summable fun j => ‖f j t‖ := by simpa only [hn] using (hB t (le_of_lt ht)).1
    have hmaj : ‖∑' j, f j t‖ ≤ B*Real.exp (d*t) := (norm_tsum_le_tsum_norm hsum).trans
      (by simpa only [hn] using (hB t (le_of_lt ht)).2)
    change ‖expRay (s:ℂ) t * ∑' j, f j t‖ ≤ ‖(B:ℂ)*expRay (d:ℂ) t‖
    rw [norm_mul,norm_mul,norm_expRay,norm_expRay,Complex.ofReal_re,Complex.ofReal_re,Complex.norm_real,
      Real.norm_eq_abs]
    have hmul : Real.exp (-(s*t))*Real.exp (d*t) = Real.exp (-(d*t)) := by
      rw [← Real.exp_add]; congr 1; dsimp [d]; ring
    calc _ ≤ Real.exp (-(s*t)) * (B*Real.exp (d*t)) :=
          mul_le_mul_of_nonneg_left hmaj (Real.exp_pos _).le
      _ = B*Real.exp (-(d*t)) := by rw [← hmul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_abs_self B) (Real.exp_pos _).le
  have hshift : ∀ᵐ t ∂volume, ∀ n : ℕ, F (t-Real.log n) = Φ (t-Real.log n) :=
    ae_all_iff.mpr fun n => (measurePreserving_sub_right volume (Real.log n)).quasiMeasurePreserving.ae heq
  refine MemLp.ae_eq ?_ hp
  filter_upwards [ae_restrict_of_ae (s := Ioi (0:ℝ)) hshift] with t ht
  simp only [f,ht]

#print axioms criticalState_memLp_damped_properPowerWave

/-- If the critical state occurs, its proper-power head has a genuine simple pole at zero.
The continuation and the residue are obtained from the actual Euler coefficients. -/
theorem riemannHypothesis_or_criticalState_properPowerHead_pole :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧
        G 0 ≠ 0 ∧ G 0 = -negativeHalfLineLaplace (cx F) 0 / 2 ∧
        ∀ᶠ p in 𝓝[≠] (0 : ℂ), G p = p * properPowerHeadContinuation F p := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  obtain ⟨G, hG, hzero, heq⟩ := properPowerHeadContinuation_residue
    (criticalHalfLineEnergyDomain_of_groundState hF)
  refine Or.inr ⟨W₀, F, hW, ht, hF, G, hG, ?_, hzero, heq⟩
  rw [hzero]
  exact div_ne_zero (neg_ne_zero.mpr (criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero
    hW ht hF (by simp))) two_ne_zero

#print axioms primeHead_eq_prime_add_properPowerHead
#print axioms differentiableOn_properPowerHead
#print axioms properPowerHeadContinuation_eq
#print axioms differentiableAt_properPowerHeadContinuation_of_re_zero
#print axioms criticalState_properPowerWave_subexponential
#print axioms riemannHypothesis_or_criticalState_properPowerHead_pole

end GaloisForLFunctions.ExclusionOfTheCriticalState
