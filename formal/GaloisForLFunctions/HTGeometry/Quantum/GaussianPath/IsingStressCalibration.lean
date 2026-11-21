import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IsingStressEnvelope

/-!
# Stress calibration by diagonal energy excess

Energy and stress read the same basis probabilities. Each excited
configuration contributes a stress excess divided by its energy gap.
The largest such ratio gives a sharp linear uncertainty bound, even
when the ground eigenspace is degenerate.
-/

open Matrix Set
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace FiniteStrain

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- A law of computational basis outcomes. -/
def IsBasisLaw (p : ι → ℝ) : Prop := (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- Expectation of a diagonal observable under a basis law. -/
def diagonalMean (p a : ι → ℝ) : ℝ := ∑ i, p i * a i

omit [Nonempty ι] in
theorem diagonalMean_sub_const {p : ι → ℝ} (hp : IsBasisLaw p) (a : ι → ℝ) (x : ℝ) :
    diagonalMean p (fun i => a i - x) = diagonalMean p a - x := by
  simp only [diagonalMean, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp.2, one_mul]

omit [Nonempty ι] in
theorem diagonalMean_neg (p a : ι → ℝ) :
    diagonalMean p (fun i => -a i) = -diagonalMean p a := by
  simp only [diagonalMean, mul_neg, Finset.sum_neg_distrib]

theorem groundEnergy_le_diagonalMean (a : ι → ℝ) {p : ι → ℝ} (hp : IsBasisLaw p) :
    groundEnergy a ≤ diagonalMean p a := by
  apply sub_nonneg.mp
  rw [← diagonalMean_sub_const hp]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hp.1 i) (sub_nonneg.mpr (groundEnergy_le a i))

/-- A basis law has ground energy exactly when it is supported on
the ground configurations. -/
theorem diagonalMean_eq_groundEnergy_iff (a : ι → ℝ) {p : ι → ℝ} (hp : IsBasisLaw p) :
    diagonalMean p a = groundEnergy a ↔ ∀ i, p i ≠ 0 → i ∈ groundConfigurations a := by
  have hnonneg (i : ι) : 0 ≤ p i * (a i - groundEnergy a) :=
    mul_nonneg (hp.1 i) (sub_nonneg.mpr (groundEnergy_le a i))
  constructor
  · intro h i hi
    have hz : diagonalMean p (fun j => a j - groundEnergy a) = 0 := by
      rw [diagonalMean_sub_const hp, h, sub_self]
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp
      hz i (Finset.mem_univ _)
    exact mem_groundConfigurations.mpr (sub_eq_zero.mp ((mul_eq_zero.mp hterm).resolve_left hi))
  · intro h
    apply sub_eq_zero.mp
    rw [← diagonalMean_sub_const hp]
    apply Finset.sum_eq_zero
    intro i _
    change p i * (a i - groundEnergy a) = 0
    by_cases hi : p i = 0
    · rw [hi, zero_mul]
    · rw [mem_groundConfigurations.mp (h i hi), sub_self, mul_zero]

/-- The basis law concentrated on configuration `i`. -/
def pointBasisLaw (i : ι) : ι → ℝ := by
  classical
  exact fun j => if j = i then 1 else 0

omit [Nonempty ι] in
theorem isBasisLaw_point (i : ι) : IsBasisLaw (pointBasisLaw i) := by
  classical
  constructor
  · intro j
    unfold pointBasisLaw
    split <;> norm_num
  · simp [pointBasisLaw]

omit [Nonempty ι] in
theorem diagonalMean_point (a : ι → ℝ) (i : ι) : diagonalMean (pointBasisLaw i) a = a i := by
  classical
  simp [diagonalMean, pointBasisLaw, ite_mul]

/-- Mixture with weight `t` on the second law. -/
def mixBasisLaw (p q : ι → ℝ) (t : ℝ) (i : ι) : ℝ :=
  (1 - t) * p i + t * q i

omit [Nonempty ι] in
theorem isBasisLaw_mix {p q : ι → ℝ} (hp : IsBasisLaw p) (hq : IsBasisLaw q)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) : IsBasisLaw (mixBasisLaw p q t) := by
  constructor
  · intro i
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht₁) (hp.1 i)) (mul_nonneg ht₀ (hq.1 i))
  · simp only [mixBasisLaw, Finset.sum_add_distrib, ← Finset.mul_sum, hp.2, hq.2, mul_one]
    ring

omit [Nonempty ι] in
theorem diagonalMean_mix (p q a : ι → ℝ) (t : ℝ) :
    diagonalMean (mixBasisLaw p q t) a = (1 - t) * diagonalMean p a + t * diagonalMean q a := by
  simp only [diagonalMean, mixBasisLaw, add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Greatest upward stress excess per unit energy gap. Ground
configurations contribute zero to the supremum. -/
def upperStressEnergySlope (a b : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun i => (b i - groundStressMax a b) / (a i - groundEnergy a))

/-- Greatest downward stress excess per unit energy gap. -/
def lowerStressEnergySlope (a b : ι → ℝ) : ℝ :=
  upperStressEnergySlope a (fun i => -b i)

theorem upperStressEnergySlope_nonneg (a b : ι → ℝ) : 0 ≤ upperStressEnergySlope a b := by
  obtain ⟨i, hi⟩ := groundConfigurations_nonempty a
  calc
    0 = (b i - groundStressMax a b) / (a i - groundEnergy a) := by
      rw [mem_groundConfigurations.mp hi, sub_self, div_zero]
    _ ≤ upperStressEnergySlope a b :=
      Finset.le_sup' (fun j => (b j - groundStressMax a b) / (a j - groundEnergy a)) (Finset.mem_univ i)

theorem lowerStressEnergySlope_nonneg (a b : ι → ℝ) : 0 ≤ lowerStressEnergySlope a b :=
  upperStressEnergySlope_nonneg a _

private theorem stress_excess_le_scaled_gap (a b : ι → ℝ) (i : ι) :
    b i - groundStressMax a b ≤ upperStressEnergySlope a b * (a i - groundEnergy a) := by
  by_cases hi : a i = groundEnergy a
  · rw [hi, sub_self, mul_zero]
    exact sub_nonpos.mpr (le_groundStressMax (mem_groundConfigurations.mpr hi))
  · have hgap : 0 < a i - groundEnergy a :=
      sub_pos.mpr (lt_of_le_of_ne (groundEnergy_le a i) (Ne.symm hi))
    apply (div_le_iff₀ hgap).mp
    exact Finset.le_sup' (fun j => (b j - groundStressMax a b) / (a j - groundEnergy a))
      (Finset.mem_univ i)

/-- The commuting stress readout has linear error in energy excess. -/
theorem diagonalMean_stress_upper (a b : ι → ℝ) {p : ι → ℝ} (hp : IsBasisLaw p) :
    diagonalMean p b - groundStressMax a b ≤
      upperStressEnergySlope a b * (diagonalMean p a - groundEnergy a) := by
  rw [← diagonalMean_sub_const hp, ← diagonalMean_sub_const hp]
  unfold diagonalMean
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (stress_excess_le_scaled_gap a b i) (hp.1 i)

theorem diagonalMean_stress_lower (a b : ι → ℝ) {p : ι → ℝ} (hp : IsBasisLaw p) :
    groundStressMin a b - diagonalMean p b ≤
      lowerStressEnergySlope a b * (diagonalMean p a - groundEnergy a) := by
  have h := diagonalMean_stress_upper a (fun i => -b i) hp
  rw [diagonalMean_neg, groundStressMax_neg, neg_sub_neg] at h
  exact h

/-- Testing the basis configurations proves optimality of the upper
constant among nonnegative coefficients valid for all prepared laws. -/
theorem upperStressEnergySlope_le_iff (a b : ι → ℝ) {L : ℝ} (hL : 0 ≤ L) :
    upperStressEnergySlope a b ≤ L ↔ ∀ p, IsBasisLaw p →
      diagonalMean p b - groundStressMax a b ≤ L * (diagonalMean p a - groundEnergy a) := by
  constructor
  · intro h p hp
    exact (diagonalMean_stress_upper a b hp).trans
      (mul_le_mul_of_nonneg_right h (sub_nonneg.mpr (groundEnergy_le_diagonalMean a hp)))
  · intro H
    unfold upperStressEnergySlope
    apply Finset.sup'_le
    intro i _
    by_cases hi : a i = groundEnergy a
    · simpa only [hi, sub_self, div_zero] using hL
    · have hgap : 0 < a i - groundEnergy a :=
        sub_pos.mpr (lt_of_le_of_ne (groundEnergy_le a i) (Ne.symm hi))
      apply (div_le_iff₀ hgap).mpr
      simpa only [diagonalMean_point] using H (pointBasisLaw i) (isBasisLaw_point i)

theorem lowerStressEnergySlope_le_iff (a b : ι → ℝ) {L : ℝ} (hL : 0 ≤ L) :
    lowerStressEnergySlope a b ≤ L ↔ ∀ p, IsBasisLaw p →
      groundStressMin a b - diagonalMean p b ≤ L * (diagonalMean p a - groundEnergy a) := by
  simpa only [lowerStressEnergySlope, diagonalMean_neg, groundStressMax_neg, neg_sub_neg] using
    upperStressEnergySlope_le_iff a (fun i => -b i) hL

/-- The upper calibration slope determines exactly when an excited
configuration can undercut the negative-strain ground branch. -/
theorem strainedEnergy_negative_eq_groundBranch_iff (a b : ι → ℝ) (k : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    strainedEnergy a b k (-t) = groundEnergy a - t * groundStressMax a b + k * t ^ 2 ↔
      t * upperStressEnergySlope a b ≤ 1 := by
  constructor
  · intro he
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun i => (b i - groundStressMax a b) / (a i - groundEnergy a))
    change upperStressEnergySlope a b = _ at hi
    by_cases h : a i = groundEnergy a
    · rw [hi, h, sub_self, div_zero, mul_zero]
      exact zero_le_one
    · have hgap : 0 < a i - groundEnergy a :=
        sub_pos.mpr (lt_of_le_of_ne (groundEnergy_le a i) (Ne.symm h))
      have hc := groundEnergy_le (fun j => a j + (-t) * b j + k * (-t) ^ 2) i
      change strainedEnergy a b k (-t) ≤ a i + (-t) * b i + k * (-t) ^ 2 at hc
      rw [he, neg_sq] at hc
      have hm : t * (b i - groundStressMax a b) ≤ a i - groundEnergy a := by
        nlinarith only [hc]
      rw [hi, ← mul_div_assoc]
      exact (div_le_iff₀ hgap).mpr (by simpa only [one_mul] using hm)
  · intro h
    obtain ⟨i, hi, hmax⟩ := exists_groundStressMax a b
    have he := mem_groundConfigurations.mp hi
    have hs (j : ι) : t * (b j - groundStressMax a b) ≤ a j - groundEnergy a := by
      calc
        _ ≤ t * (upperStressEnergySlope a b * (a j - groundEnergy a)) :=
          mul_le_mul_of_nonneg_left (stress_excess_le_scaled_gap a b j) ht
        _ = (t * upperStressEnergySlope a b) * (a j - groundEnergy a) := by ring
        _ ≤ _ := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right h (sub_nonneg.mpr (groundEnergy_le a j))
    have hm (j : ι) : a i + (-t) * b i + k * (-t) ^ 2 ≤ a j + (-t) * b j + k * (-t) ^ 2 := by
      apply add_le_add _ le_rfl
      rw [he, ← hmax]
      nlinarith only [hs j]
    rw [strainedEnergy, groundEnergy_eq_of_minimizer _ i hm, he, ← hmax, neg_sq]
    ring

theorem strainedEnergy_positive_eq_groundBranch_iff (a b : ι → ℝ) (k : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    strainedEnergy a b k t = groundEnergy a + t * groundStressMin a b + k * t ^ 2 ↔
      t * lowerStressEnergySlope a b ≤ 1 := by
  have he : strainedEnergy a (fun i => -b i) k (-t) = strainedEnergy a b k t := by
    simp only [strainedEnergy, neg_mul_neg, neg_sq]
  have h := strainedEnergy_negative_eq_groundBranch_iff a (fun i => -b i) k ht
  rw [he, groundStressMax_neg, mul_neg, sub_neg_eq_add] at h
  exact h

/-- Stress expectations at exactly ground energy fill the closed interval
between the one-sided slopes. Two ground configurations suffice. -/
theorem groundStressRange_eq_Icc (a b : ι → ℝ) :
    {s | ∃ p, IsBasisLaw p ∧ diagonalMean p a = groundEnergy a ∧ diagonalMean p b = s} =
      Icc (groundStressMin a b) (groundStressMax a b) := by
  ext s
  constructor
  · rintro ⟨p, hp, he, rfl⟩
    have h₁ := diagonalMean_stress_lower a b hp
    have h₂ := diagonalMean_stress_upper a b hp
    rw [he, sub_self, mul_zero] at h₁ h₂
    exact ⟨sub_nonpos.mp h₁, sub_nonpos.mp h₂⟩
  · intro hs
    obtain ⟨i, hi, hmin⟩ := exists_groundStressMin a b
    obtain ⟨j, hj, hmax⟩ := exists_groundStressMax a b
    have hi₀ := mem_groundConfigurations.mp hi
    have hj₀ := mem_groundConfigurations.mp hj
    by_cases h : groundStressMin a b = groundStressMax a b
    · have he : groundStressMin a b = s := le_antisymm hs.1 (hs.2.trans_eq h.symm)
      refine ⟨pointBasisLaw i, isBasisLaw_point i, ?_, ?_⟩
      · rwa [diagonalMean_point]
      · rw [diagonalMean_point, ← hmin, he]
    · have hgap : 0 < groundStressMax a b - groundStressMin a b :=
        sub_pos.mpr (lt_of_le_of_ne (hs.1.trans hs.2) h)
      let t := (s - groundStressMin a b) / (groundStressMax a b - groundStressMin a b)
      have ht₀ : 0 ≤ t := div_nonneg (sub_nonneg.mpr hs.1) hgap.le
      have ht₁ : t ≤ 1 := (div_le_iff₀ hgap).mpr (by
        rw [one_mul]
        exact sub_le_sub_right hs.2 (groundStressMin a b))
      have hcancel : t * (groundStressMax a b - groundStressMin a b) = s - groundStressMin a b :=
        div_mul_cancel₀ _ hgap.ne'
      refine ⟨mixBasisLaw (pointBasisLaw i) (pointBasisLaw j) t,
        isBasisLaw_mix (isBasisLaw_point i) (isBasisLaw_point j) ht₀ ht₁, ?_, ?_⟩
      · rw [diagonalMean_mix, diagonalMean_point, diagonalMean_point, hi₀, hj₀]
        ring
      · rw [diagonalMean_mix, diagonalMean_point, diagonalMean_point, ← hmin, ← hmax]
        calc
          _ = groundStressMin a b + t * (groundStressMax a b - groundStressMin a b) := by ring
          _ = _ := by rw [hcancel]; ring

/-- For all sufficiently small nonnegative energy budgets the upper
calibration bound is attained by a mixture of at most two configurations. -/
theorem upperStressEnergyBudget_attained_locally (a b : ι → ℝ) :
    ∃ r : ℝ, 0 < r ∧ ∀ η : ℝ, 0 ≤ η → η ≤ r → ∃ p, IsBasisLaw p ∧
      diagonalMean p a - groundEnergy a ≤ η ∧
      diagonalMean p b = groundStressMax a b + upperStressEnergySlope a b * η := by
  obtain ⟨j, hj, hjb⟩ := exists_groundStressMax a b
  have hja := mem_groundConfigurations.mp hj
  by_cases hz : upperStressEnergySlope a b = 0
  · refine ⟨1, zero_lt_one, fun η hη _ => ⟨pointBasisLaw j, isBasisLaw_point j, ?_, ?_⟩⟩
    · simpa only [diagonalMean_point, hja, sub_self] using hη
    · rw [diagonalMean_point, hz, zero_mul, add_zero, hjb]
  · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun i => (b i - groundStressMax a b) / (a i - groundEnergy a))
    change upperStressEnergySlope a b = _ at hi
    have hne : a i ≠ groundEnergy a := by
      intro he
      exact hz (by simpa only [he, sub_self, div_zero] using hi)
    let r := a i - groundEnergy a
    have hr : 0 < r := sub_pos.mpr (lt_of_le_of_ne (groundEnergy_le a i) hne.symm)
    have hslope : upperStressEnergySlope a b * r = b i - groundStressMax a b := by
      rw [hi]
      exact div_mul_cancel₀ _ hr.ne'
    refine ⟨r, hr, fun η hη hηr => ?_⟩
    let t := η / r
    have ht₀ : 0 ≤ t := div_nonneg hη hr.le
    have ht₁ : t ≤ 1 := (div_le_iff₀ hr).mpr (by simpa only [one_mul] using hηr)
    have htr : t * r = η := div_mul_cancel₀ _ hr.ne'
    refine ⟨mixBasisLaw (pointBasisLaw j) (pointBasisLaw i) t,
      isBasisLaw_mix (isBasisLaw_point j) (isBasisLaw_point i) ht₀ ht₁, ?_, ?_⟩
    · rw [diagonalMean_mix, diagonalMean_point, diagonalMean_point, hja]
      calc
        _ = t * r := by dsimp [r]; ring
        _ ≤ _ := htr.le
    · rw [diagonalMean_mix, diagonalMean_point, diagonalMean_point, ← hjb]
      calc
        _ = groundStressMax a b + t * (b i - groundStressMax a b) := by ring
        _ = groundStressMax a b + t * (upperStressEnergySlope a b * r) := by rw [hslope]
        _ = groundStressMax a b + upperStressEnergySlope a b * η := by rw [mul_left_comm, htr]

/-- Computational-basis probabilities of a pure state. -/
def pureBasisLaw (ψ : EuclideanSpace ℂ ι) (i : ι) : ℝ := ‖ψ.ofLp i‖ ^ 2

omit [Nonempty ι] in
theorem isBasisLaw_pure (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) : IsBasisLaw (pureBasisLaw ψ) := by
  refine ⟨fun i => sq_nonneg _, ?_⟩
  change (∑ i, ‖ψ.ofLp i‖ ^ 2) = 1
  rw [← EuclideanSpace.norm_sq_eq, hψ, one_pow]

omit [Nonempty ι] in
/-- Square roots of the outcome probabilities realize every basis law
by a normalized pure state. -/
theorem exists_pureBasisLaw {p : ι → ℝ} (hp : IsBasisLaw p) :
    ∃ ψ : EuclideanSpace ℂ ι, ‖ψ‖ = 1 ∧ pureBasisLaw ψ = p := by
  let ψ : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun i => (Real.sqrt (p i) : ℂ))
  have hprob : pureBasisLaw ψ = p := by
    funext i
    change ‖(Real.sqrt (p i) : ℂ)‖ ^ 2 = p i
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hp.1 i)]
  refine ⟨ψ, ?_, hprob⟩
  have hsq : ‖ψ‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ i, pureBasisLaw ψ i) = 1
    rw [hprob]
    exact hp.2
  rw [← Real.sqrt_sq (norm_nonneg ψ), hsq, Real.sqrt_one]

/-- The pure-state expectation of a real diagonal observable. -/
def pureDiagonalMean (ψ : EuclideanSpace ℂ ι) (a : ι → ℝ) : ℝ :=
  diagonalMean (pureBasisLaw ψ) a

omit [Nonempty ι] in
theorem pureDiagonalMean_matrix (ψ : EuclideanSpace ℂ ι) (a : ι → ℝ) [DecidableEq ι] :
    dotProduct (fun i => star (ψ.ofLp i)) (Matrix.diagonal (fun i => (a i : ℂ)) *ᵥ ψ.ofLp) =
      (pureDiagonalMean ψ a : ℂ) := by
  rw [dotProduct, pureDiagonalMean, diagonalMean, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_diagonal, Complex.ofReal_mul]
  calc
    _ = (star (ψ.ofLp i) * ψ.ofLp i) * (a i : ℂ) := by ring
    _ = _ := by simp only [Complex.star_def, Complex.conj_mul', pureBasisLaw, Complex.ofReal_pow]

/-- All ground-space stress values between the two slopes are realized
by normalized pure states, including coherent superpositions. -/
theorem pureGroundStressRange_eq_Icc (a b : ι → ℝ) :
    {s | ∃ ψ : EuclideanSpace ℂ ι, ‖ψ‖ = 1 ∧ pureDiagonalMean ψ a = groundEnergy a ∧
      pureDiagonalMean ψ b = s} = Icc (groundStressMin a b) (groundStressMax a b) := by
  rw [← groundStressRange_eq_Icc a b]
  ext s
  constructor
  · rintro ⟨ψ, hψ, ha, hb⟩
    exact ⟨pureBasisLaw ψ, isBasisLaw_pure ψ hψ, ha, hb⟩
  · rintro ⟨p, hp, ha, hb⟩
    obtain ⟨ψ, hψ, hprob⟩ := exists_pureBasisLaw hp
    exact ⟨ψ, hψ, by rwa [pureDiagonalMean, hprob], by rwa [pureDiagonalMean, hprob]⟩

end FiniteStrain

/-- Diagonal mean gives the quadratic-form readout of the encoded path Hamiltonian. -/
theorem isingStrain_energy_readout {n : ℕ}
    (h dh : Fin (n + 2) → ℝ) (J : Fin (n + 1) → ℝ) (t : ℝ)
    (ψ : EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2)))) :
    dotProduct (fun x => star (ψ.ofLp x)) (pathHamiltonian (strainPath h dh J t) *ᵥ ψ.ofLp) =
      (FiniteStrain.pureDiagonalMean ψ (pathDiagEnergy (strainPath h dh J t)) : ℂ) := by
  have hd := pathHamiltonian_eq_diagonal (u := strainPath h dh J t) (by
    rintro (⟨i, a⟩ | ⟨e, a, b⟩) hl
    · change (if a = 2 then h i + t * dh i else 0) = 0
      exact if_neg hl
    · change (if (a, b) = (2, 2) then J e else 0) = 0
      exact if_neg hl)
  rw [hd]
  exact FiniteStrain.pureDiagonalMean_matrix ψ _

/-- The stress readouts of normalized Ising ground states fill the
interval from the right derivative to the left derivative. -/
theorem isingStrain_groundStressRange_eq_derivativeInterval {n : ℕ}
    (h dh : Fin (n + 2) → ℝ) (J : Fin (n + 1) → ℝ) :
    {s | ∃ ψ : EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2))), ‖ψ‖ = 1 ∧
      FiniteStrain.pureDiagonalMean ψ (pathDiagEnergy (strainPath h dh J 0)) =
        isingStrainGroundEnergy h dh J 0 ∧ FiniteStrain.pureDiagonalMean ψ (onsiteResponse dh) = s} =
    Icc (derivWithin (isingStrainGroundEnergy h dh J) (Ici 0) 0)
      (derivWithin (isingStrainGroundEnergy h dh J) (Iic 0) 0) := by
  obtain ⟨hr, hl⟩ := isingStrainGroundEnergy_oneSided_derivatives h dh J
  rw [hr.derivWithin (uniqueDiffWithinAt_Ici _), hl.derivWithin (uniqueDiffWithinAt_Iic _)]
  exact FiniteStrain.pureGroundStressRange_eq_Icc _ _

/-- On the diagonal path carrier, one can certify the prepared-state
stress using only the energy excess and the basis stress ratios. -/
theorem isingStrain_pureStress_calibration {n : ℕ}
    (h dh : Fin (n + 2) → ℝ) (J : Fin (n + 1) → ℝ)
    (ψ : EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2)))) (hψ : ‖ψ‖ = 1) :
    let a := pathDiagEnergy (strainPath h dh J 0)
    let b := onsiteResponse dh
    let η := FiniteStrain.pureDiagonalMean ψ a - isingStrainGroundEnergy h dh J 0
    FiniteStrain.groundStressMin a b - FiniteStrain.lowerStressEnergySlope a b * η ≤
      FiniteStrain.pureDiagonalMean ψ b ∧
    FiniteStrain.pureDiagonalMean ψ b ≤
      FiniteStrain.groundStressMax a b + FiniteStrain.upperStressEnergySlope a b * η := by
  let a := pathDiagEnergy (strainPath h dh J 0)
  let b := onsiteResponse dh
  have hp := FiniteStrain.isBasisLaw_pure ψ hψ
  exact ⟨sub_le_comm.mp (FiniteStrain.diagonalMean_stress_lower a b hp),
    sub_le_iff_le_add'.mp (FiniteStrain.diagonalMean_stress_upper a b hp)⟩

#print axioms FiniteStrain.diagonalMean_eq_groundEnergy_iff
#print axioms FiniteStrain.diagonalMean_stress_upper
#print axioms FiniteStrain.diagonalMean_stress_lower
#print axioms FiniteStrain.upperStressEnergySlope_le_iff
#print axioms FiniteStrain.lowerStressEnergySlope_le_iff
#print axioms FiniteStrain.strainedEnergy_negative_eq_groundBranch_iff
#print axioms FiniteStrain.strainedEnergy_positive_eq_groundBranch_iff
#print axioms FiniteStrain.groundStressRange_eq_Icc
#print axioms FiniteStrain.upperStressEnergyBudget_attained_locally
#print axioms FiniteStrain.pureGroundStressRange_eq_Icc
#print axioms FiniteStrain.pureDiagonalMean_matrix
#print axioms isingStrain_energy_readout
#print axioms isingStrain_groundStressRange_eq_derivativeInterval
#print axioms isingStrain_pureStress_calibration

end

end GaloisForLFunctions.HTGeometry
