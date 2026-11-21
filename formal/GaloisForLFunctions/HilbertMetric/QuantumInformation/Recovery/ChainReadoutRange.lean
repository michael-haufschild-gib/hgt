import GaloisForLFunctions.HilbertMetric.QuantumInformation.Recovery.ChainSiteReadout

/-!
# Exact single-site distinguishability at fixed population

The coherence in the single-site formula of Kanno and Soda
(arXiv:2611.26368, Eq. 7.19) uses two adjacent run amplitudes.
A third run on either side of the site can carry population without
contributing coherence. This gives the entire attainable interval.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric.QuantumInformation.ReadyBranch

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : ℕ}

/-- Squared readout distance splits into the squared population and the adjacent-run weight product. -/
theorem siteReadoutDistance_sq (A : RunAmplitudes n) (s : Fin n) :
    siteReadoutDistance A s ^ 2 = siteExcitedPopulation A s ^ 2 +
      ‖A.1 s.succ‖ ^ 2 * ‖A.1 s.castSucc‖ ^ 2 := by
  rw [siteReadoutDistance, Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)),
    norm_mul, norm_star, mul_pow]

private def groundWeight (A : RunAmplitudes n) (s : Fin n) (j : Fin (n + 1)) : ℝ :=
  if s.val < j.val then 0 else ‖A.1 j‖ ^ 2

private theorem groundWeight_nonneg (A : RunAmplitudes n) (s : Fin n) (j : Fin (n + 1)) :
    0 ≤ groundWeight A s j := by unfold groundWeight; split <;> positivity

private theorem population_add_ground (A : RunAmplitudes n) (s : Fin n) :
    siteExcitedPopulation A s + (∑ j, groundWeight A s j) = 1 := by
  unfold siteExcitedPopulation
  rw [← Finset.sum_add_distrib]
  calc
    _ = cnormSq A.1 := by
      unfold cnormSq
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : s.val < j.val <;> simp [groundWeight, h]
    _ = 1 := A.2

/-- At the initial site only the zero-length run contributes to the ground population. -/
theorem initialSite_before_sq_eq_ground (A : RunAmplitudes n) (s : Fin n) (hs : s.val = 0) :
    ‖A.1 s.castSucc‖ ^ 2 = 1 - siteExcitedPopulation A s := by
  have hg : (∑ j, groundWeight A s j) = ‖A.1 s.castSucc‖ ^ 2 := by
    rw [Finset.sum_eq_single s.castSucc]
    · simp [groundWeight]
    · intro j _ hj
      have hj' : s.val < j.val := by
        by_contra! h
        apply hj
        apply Fin.ext
        change j.val = s.val
        omega
      simp [groundWeight, hj']
    · exact fun h => (h (Finset.mem_univ _)).elim
  linarith only [hg, population_add_ground A s]

private theorem population_split_bounds (A : RunAmplitudes n) (s : Fin n) :
    0 ≤ siteExcitedPopulation A s ∧ siteExcitedPopulation A s ≤ 1 ∧
      ‖A.1 s.succ‖ ^ 2 ≤ siteExcitedPopulation A s ∧
      ‖A.1 s.castSucc‖ ^ 2 ≤ 1 - siteExcitedPopulation A s := by
  let w (j : Fin (n + 1)) := ‖A.1 j‖ ^ 2
  let g := ∑ j, groundWeight A s j
  have hp : 0 ≤ siteExcitedPopulation A s :=
    Finset.sum_nonneg fun j _ => by split <;> positivity
  have hg : 0 ≤ g := Finset.sum_nonneg fun j _ => groundWeight_nonneg A s j
  have hsum : siteExcitedPopulation A s + g = 1 := population_add_ground A s
  have hafter : w s.succ ≤ siteExcitedPopulation A s := by
    change w s.succ ≤ ∑ j, if s.val < j.val then w j else 0
    simpa only [Fin.val_succ, Nat.lt_succ_self, if_true] using
      (Finset.single_le_sum (f := fun j : Fin (n + 1) => if s.val < j.val then w j else 0)
        (fun j _ => by split <;> positivity) (Finset.mem_univ s.succ))
  have hbefore : w s.castSucc ≤ g := by
    have h := Finset.single_le_sum (fun j _ => groundWeight_nonneg A s j)
      (Finset.mem_univ s.castSucc)
    have he : groundWeight A s s.castSucc = w s.castSucc := by simp [groundWeight, w]
    rwa [he] at h
  exact ⟨hp, by linarith only [hsum, hg], hafter, by linarith only [hsum, hbefore]⟩

/-- Population measurement gives the lower bound. The two-level purity
bound gives the upper bound, even when the chain contains more sites. -/
theorem siteReadoutDistance_bounds (A : RunAmplitudes n) (s : Fin n) :
    siteExcitedPopulation A s ≤ siteReadoutDistance A s ∧
      siteReadoutDistance A s ≤ Real.sqrt (siteExcitedPopulation A s) := by
  obtain ⟨hp, _, ha, hb⟩ := population_split_bounds A s
  have hd : 0 ≤ siteReadoutDistance A s := Real.sqrt_nonneg _
  constructor
  · apply (sq_le_sq₀ hp hd).mp
    rw [siteReadoutDistance_sq]
    exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  · apply (sq_le_sq₀ hd (Real.sqrt_nonneg _)).mp
    rw [siteReadoutDistance_sq, Real.sq_sqrt hp]
    have hprod := mul_le_mul ha hb (sq_nonneg _) hp
    nlinarith only [hprod]

/-- At a noninitial site the all-zero run is the entire recoverable slice. -/
theorem noninitialSite_ready_mass (A : RunAmplitudes n) (s : Fin n) (hs : s.val ≠ 0) :
    maskedRunMass ({s} : Finset (Fin n)) A = ‖A.1 (0 : Fin (n + 1))‖ ^ 2 := by
  let i : Fin n := ⟨0, (Nat.zero_le s.val).trans_lt s.isLt⟩
  have hmiss : i ∉ ({s} : Finset (Fin n)) :=
    fun h => hs (congrArg Fin.val (Finset.mem_singleton.mp h)).symm
  have hzero : accessiblePrefixLength ({s} : Finset (Fin n)) = 0 :=
    Nat.le_zero.mp (accessiblePrefixLength_le_of_missing hmiss)
  unfold maskedRunMass
  rw [hzero, Finset.sum_eq_single (0 : Fin (n + 1))]
  · simp
  · intro j _ hj
    exact if_neg fun h => hj (Fin.ext (Nat.le_zero.mp h))
  · exact fun h => (h (Finset.mem_univ _)).elim

private theorem noninitialSite_before_sq_le (A : RunAmplitudes n) (s : Fin n) (hs : s.val ≠ 0) :
    ‖A.1 s.castSucc‖ ^ 2 ≤ 1 - siteExcitedPopulation A s - maskedRunMass ({s} : Finset (Fin n)) A := by
  have hne : s.castSucc ≠ (0 : Fin (n + 1)) := fun h => hs (congrArg Fin.val h)
  have hmem : s.castSucc ∈ (Finset.univ.erase (0 : Fin (n + 1))) :=
    Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩
  have hbefore := Finset.single_le_sum (fun j _ => groundWeight_nonneg A s j) hmem
  have hsum := Finset.sum_erase_add Finset.univ (groundWeight A s)
    (Finset.mem_univ (0 : Fin (n + 1)))
  have hpop := population_add_ground A s
  have he : groundWeight A s s.castSucc = ‖A.1 s.castSucc‖ ^ 2 := by simp [groundWeight]
  have hzero : groundWeight A s 0 = maskedRunMass ({s} : Finset (Fin n)) A := by
    rw [noninitialSite_ready_mass A s hs]
    simp [groundWeight]
  rw [he] at hbefore
  rw [hzero] at hsum
  linarith only [hbefore, hsum, hpop]

/-- At a noninitial site the excited and ready-slice populations are disjoint. -/
theorem noninitialSite_population_add_ready_mass_le (A : RunAmplitudes n) (s : Fin n) (hs : s.val ≠ 0) :
    siteExcitedPopulation A s + maskedRunMass ({s} : Finset (Fin n)) A ≤ 1 := by
  linarith only [noninitialSite_before_sq_le A s hs, sq_nonneg ‖A.1 s.castSucc‖]

/-- The ground population spent on ready-slice recovery is unavailable
to the adjacent pair that supplies local readout coherence. -/
theorem noninitialSite_readout_le_recovery_bound (A : RunAmplitudes n) (s : Fin n) (hs : s.val ≠ 0) :
    siteReadoutDistance A s ≤ Real.sqrt
      (siteExcitedPopulation A s * (1 - maskedRunMass ({s} : Finset (Fin n)) A)) := by
  obtain ⟨hp, _, ha, _⟩ := population_split_bounds A s
  have hb := noninitialSite_before_sq_le A s hs
  rw [siteReadoutDistance, norm_mul, norm_star, mul_pow]
  apply Real.sqrt_le_sqrt
  have hprod := mul_le_mul ha hb (sq_nonneg _) hp
  nlinarith only [hprod]

/-- A weight concentrated at one run length. -/
def runAtomWeight (i : Fin (n + 1)) (a : ℝ) (j : Fin (n + 1)) : ℝ :=
  if j = i then a else 0

theorem sum_filter_runAtomWeight (i : Fin (n + 1)) (a : ℝ)
    (P : Fin (n + 1) → Prop) [DecidablePred P] :
    (∑ j, if P j then runAtomWeight i a j else 0) = if P i then a else 0 := by
  rw [Finset.sum_eq_single i]
  · simp [runAtomWeight]
  · intro j _ hj
    simp [runAtomWeight, hj]
  · exact fun h => (h (Finset.mem_univ _)).elim

theorem sum_runAtomWeight (i : Fin (n + 1)) (a : ℝ) : ∑ j, runAtomWeight i a j = a := by
  simpa only [if_true] using sum_filter_runAtomWeight i a (fun _ => True)

/-- Every probability distribution on run lengths is realised by normalized amplitudes. -/
theorem exists_runAmplitudes_of_weights (w : Fin (n + 1) → ℝ) (hw : ∀ j, 0 ≤ w j)
    (ht : ∑ j, w j = 1) : ∃ A : RunAmplitudes n, ∀ j, ‖A.1 j‖ ^ 2 = w j := by
  let ψ (j : Fin (n + 1)) : ℂ := (Real.sqrt (w j) : ℝ)
  have hψ (j : Fin (n + 1)) : ‖ψ j‖ ^ 2 = w j := by
    rw [show ψ j = (Real.sqrt (w j) : ℂ) from rfl, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hw j)]
  have hn : cnormSq ψ = 1 := by simpa only [cnormSq, hψ] using ht
  exact ⟨⟨ψ, hn⟩, hψ⟩

/-- Allocate population between the two adjacent runs and a third distinct run. -/
theorem exists_three_run_amplitudes (s : Fin n) (u : Fin (n + 1))
    (hu₀ : u ≠ s.castSucc) (hu₁ : u ≠ s.succ) (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (ht : a + b + c = 1) :
    ∃ A : RunAmplitudes n,
      siteExcitedPopulation A s = a + (if s.val < u.val then c else 0) ∧
      ‖A.1 s.succ‖ ^ 2 = a ∧ ‖A.1 s.castSucc‖ ^ 2 = b ∧ ‖A.1 u‖ ^ 2 = c := by
  let w (j : Fin (n + 1)) := runAtomWeight s.succ a j + runAtomWeight s.castSucc b j + runAtomWeight u c j
  have hw (j : Fin (n + 1)) : 0 ≤ w j := by
    unfold w runAtomWeight
    split_ifs <;> positivity
  have hnorm : ∑ j, w j = 1 := by
    simp only [w, Finset.sum_add_distrib, sum_runAtomWeight, ht]
  obtain ⟨A, hψ⟩ := exists_runAmplitudes_of_weights w hw hnorm
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · unfold siteExcitedPopulation
    simp only [hψ, w]
    calc
      _ = ∑ j, ((if s.val < j.val then runAtomWeight s.succ a j else 0) +
          (if s.val < j.val then runAtomWeight s.castSucc b j else 0) +
          (if s.val < j.val then runAtomWeight u c j else 0)) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : s.val < j.val <;> simp [h]
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_filter_runAtomWeight,
          sum_filter_runAtomWeight, sum_filter_runAtomWeight]
        simp
  · simp [hψ, w, runAtomWeight, s.castSucc_lt_succ.ne', hu₁.symm]
  · simp [hψ, w, runAtomWeight, s.castSucc_lt_succ.ne, hu₀.symm]
  · simp [hψ, w, runAtomWeight, hu₀, hu₁]

/-- Three runs attain the upper readout bound for every admissible
excited population and ready-slice mass at a noninitial site. -/
theorem exists_noninitialSite_attain_recovery_bound (s : Fin n) (hs : s.val ≠ 0)
    (p R : ℝ) (hp : 0 ≤ p) (hR : 0 ≤ R) (h : p + R ≤ 1) :
    ∃ A : RunAmplitudes n,
      siteExcitedPopulation A s = p ∧ maskedRunMass ({s} : Finset (Fin n)) A = R ∧
        siteReadoutDistance A s = Real.sqrt (p * (1 - R)) := by
  have h₀ : (0 : Fin (n + 1)) ≠ s.castSucc := fun he => hs (congrArg Fin.val he).symm
  have h₁ : (0 : Fin (n + 1)) ≠ s.succ := fun he => Nat.zero_ne_add_one _ (congrArg Fin.val he)
  obtain ⟨A, hpop, ha, hb, hc⟩ := exists_three_run_amplitudes s 0 h₀ h₁
    p (1 - p - R) R hp (by linarith only [h]) hR (by ring)
  have hpop' : siteExcitedPopulation A s = p := by simpa using hpop
  refine ⟨A, hpop', (noninitialSite_ready_mass A s hs).trans hc, ?_⟩
  rw [siteReadoutDistance, hpop', norm_mul, norm_star, mul_pow, ha, hb]
  congr 1
  ring

/-- At any fixed population p, every distance in [p, sqrt p] is realised
on a chain with at least two sites. Three run configurations suffice. -/
theorem exists_siteReadoutDistance_iff (hn : 2 ≤ n) (s : Fin n) (p d : ℝ) :
    (∃ A : RunAmplitudes n, siteExcitedPopulation A s = p ∧ siteReadoutDistance A s = d) ↔
      0 ≤ p ∧ p ≤ 1 ∧ p ≤ d ∧ d ≤ Real.sqrt p := by
  constructor
  · rintro ⟨A, rfl, rfl⟩
    obtain ⟨hp, hp₁, _, _⟩ := population_split_bounds A s
    exact ⟨hp, hp₁, siteReadoutDistance_bounds A s⟩
  · rintro ⟨hp, hp₁, hpd, hd⟩
    have hd₀ : 0 ≤ d := hp.trans hpd
    let q := d ^ 2 - p ^ 2
    have hq₀ : 0 ≤ q := sub_nonneg.mpr ((sq_le_sq₀ hp hd₀).mpr hpd)
    have hq : q ≤ p * (1 - p) := by
      have h := (sq_le_sq₀ hd₀ (Real.sqrt_nonneg _)).mpr hd
      rw [Real.sq_sqrt hp] at h
      dsimp [q]
      nlinarith only [h]
    let P := p * (1 - p)
    have hP₀ : 0 ≤ P := mul_nonneg hp (sub_nonneg.mpr hp₁)
    obtain ⟨t, ht₀, ht₁, ht⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ P * t = q := by
      have hqP : q ≤ P := hq
      by_cases h : P = 0
      · exact ⟨0, le_rfl, zero_le_one, by
          simpa only [mul_zero] using (le_antisymm (h ▸ hqP) hq₀).symm⟩
      · have hP : 0 < P := lt_of_le_of_ne hP₀ (Ne.symm h)
        refine ⟨q / P, div_nonneg hq₀ hP₀, (div_le_one hP).mpr hqP, ?_⟩
        rw [mul_comm, div_mul_cancel₀ _ h]
    have finish (A : RunAmplitudes n) (hpop : siteExcitedPopulation A s = p)
        (hprod : ‖A.1 s.succ‖ ^ 2 * ‖A.1 s.castSucc‖ ^ 2 = q) :
        ∃ A : RunAmplitudes n, siteExcitedPopulation A s = p ∧ siteReadoutDistance A s = d := by
      refine ⟨A, hpop, ?_⟩
      apply (mul_self_inj (Real.sqrt_nonneg _) hd₀).mp
      change siteReadoutDistance A s * siteReadoutDistance A s = d * d
      rw [← pow_two, ← pow_two, siteReadoutDistance_sq, hpop, hprod]
      dsimp [q]
      ring
    by_cases hs : s.val = 0
    · let u : Fin (n + 1) := ⟨2, by omega⟩
      have hu₀ : u ≠ s.castSucc := fun h =>
        Nat.succ_ne_zero 1 ((congrArg Fin.val h).trans hs)
      have hu₁ : u ≠ s.succ := by
        intro h
        have hv : 2 = s.val + 1 := congrArg Fin.val h
        omega
      obtain ⟨A, hpop, h₁, h₀, _⟩ := exists_three_run_amplitudes s u hu₀ hu₁
        (p * t) (1 - p) (p * (1 - t)) (mul_nonneg hp ht₀) (sub_nonneg.mpr hp₁)
        (mul_nonneg hp (sub_nonneg.mpr ht₁)) (by ring)
      have hu : s.val < u.val := by change s.val < 2; omega
      refine finish A ?_ ?_
      · rw [hpop, if_pos hu]
        ring
      · rw [h₁, h₀, ← ht]
        dsimp [P]
        ring
    · let u : Fin (n + 1) := 0
      have hu₀ : u ≠ s.castSucc := fun h => hs (congrArg Fin.val h).symm
      have hu₁ : u ≠ s.succ := fun h => Nat.zero_ne_add_one _ (congrArg Fin.val h)
      obtain ⟨A, hpop, h₁, h₀, _⟩ := exists_three_run_amplitudes s u hu₀ hu₁
        p ((1 - p) * t) ((1 - p) * (1 - t)) hp (mul_nonneg (sub_nonneg.mpr hp₁) ht₀)
        (mul_nonneg (sub_nonneg.mpr hp₁) (sub_nonneg.mpr ht₁)) (by ring)
      have hu : ¬s.val < u.val := Nat.not_lt_zero _
      refine finish A ?_ ?_
      · rw [hpop, if_neg hu, add_zero]
      · rw [h₁, h₀, ← ht]
        dsimp [P]
        ring

/-- With only one site the two run configurations exhaust the signal,
forcing maximal distinguishability for the specified population. -/
theorem siteReadoutDistance_one (A : RunAmplitudes 1) (s : Fin 1) :
    siteReadoutDistance A s = Real.sqrt (siteExcitedPopulation A s) := by
  have hs : s = 0 := Fin.eq_zero s
  subst s
  have hsum : ‖A.1 (0 : Fin 2)‖ ^ 2 + ‖A.1 1‖ ^ 2 = 1 := by
    calc
      _ = ∑ j : Fin 2, ‖A.1 j‖ ^ 2 := (Fin.sum_univ_two (fun j : Fin 2 => ‖A.1 j‖ ^ 2)).symm
      _ = _ := A.2
  have hp : siteExcitedPopulation A 0 = ‖A.1 (1 : Fin 2)‖ ^ 2 := by
    simp [siteExcitedPopulation, Fin.sum_univ_two]
  have hafter : (0 : Fin 1).succ = 1 := rfl
  have hbefore : (0 : Fin 1).castSucc = 0 := rfl
  apply (mul_self_inj (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mp
  change siteReadoutDistance A 0 * siteReadoutDistance A 0 =
    Real.sqrt (siteExcitedPopulation A 0) * Real.sqrt (siteExcitedPopulation A 0)
  rw [← pow_two, ← pow_two, siteReadoutDistance_sq, hp, Real.sq_sqrt (sq_nonneg _),
    hafter, hbefore, show ‖A.1 (0 : Fin 2)‖ ^ 2 = 1 - ‖A.1 (1 : Fin 2)‖ ^ 2 by linarith only [hsum]]
  ring

#print axioms siteReadoutDistance_bounds
#print axioms noninitialSite_readout_le_recovery_bound
#print axioms exists_noninitialSite_attain_recovery_bound
#print axioms exists_siteReadoutDistance_iff
#print axioms siteReadoutDistance_one

end

end GaloisForLFunctions.HilbertMetric.QuantumInformation.ReadyBranch
