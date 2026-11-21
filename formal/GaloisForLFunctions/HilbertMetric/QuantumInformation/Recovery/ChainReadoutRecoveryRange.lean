import GaloisForLFunctions.HilbertMetric.QuantumInformation.Recovery.ChainReadoutRange

/-!
# Joint population, readout and recovery range

The adjacent-run coherence and the ready slice in the chain of Kanno
and Soda (arXiv:2611.26368, Eqs. 7.19 and 7.26) use different run
weights. Four runs fill the noninitial-site range. A two-site chain
leaves no spare run, and at the initial site the two populations already
fix both adjacent weights.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric.QuantumInformation.ReadyBranch

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : ℕ}

private theorem site_pop_nonneg (A : RunAmplitudes n) (s : Fin n) :
    0 ≤ siteExcitedPopulation A s :=
  Finset.sum_nonneg fun j _ => by split <;> positivity

private theorem ready_mass_le_one (A : RunAmplitudes n) (S : Finset (Fin n)) :
    maskedRunMass S A ≤ 1 := by
  calc
    _ ≤ cnormSq A.1 := Finset.sum_le_sum fun j _ => by
      split
      · exact le_rfl
      · exact sq_nonneg _
    _ = _ := A.2

private theorem sum_excited_weights_add (s : Fin n) (a b : Fin (n + 1) → ℝ) :
    (∑ j, if s.val < j.val then a j + b j else 0) =
      (∑ j, if s.val < j.val then a j else 0) + ∑ j, if s.val < j.val then b j else 0 := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : s.val < j.val <;> simp [h]

private theorem exists_four_run_amplitudes (s : Fin n) (hs : s.val ≠ 0) (u : Fin (n + 1))
    (hu₀ : u ≠ 0) (hu₁ : u ≠ s.castSucc) (hu₂ : u ≠ s.succ) (a b c R : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hR : 0 ≤ R) (ht : a + b + c + R = 1) :
    ∃ A : RunAmplitudes n,
      siteExcitedPopulation A s = a + (if s.val < u.val then c else 0) ∧
      maskedRunMass ({s} : Finset (Fin n)) A = R ∧
      ‖A.1 s.succ‖ ^ 2 = a ∧ ‖A.1 s.castSucc‖ ^ 2 = b := by
  let w (j : Fin (n + 1)) :=
    runAtomWeight s.succ a j + runAtomWeight s.castSucc b j + runAtomWeight u c j +
      runAtomWeight 0 R j
  have atom_nonneg (i j : Fin (n + 1)) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ runAtomWeight i x j := by
    by_cases h : j = i <;> simp [runAtomWeight, h, hx]
  have hw (j : Fin (n + 1)) : 0 ≤ w j :=
    add_nonneg (add_nonneg (add_nonneg (atom_nonneg _ _ ha) (atom_nonneg _ _ hb))
      (atom_nonneg _ _ hc)) (atom_nonneg _ _ hR)
  have hsum : ∑ j, w j = 1 := by
    simp only [w, Finset.sum_add_distrib, sum_runAtomWeight, ht]
  obtain ⟨A, hA⟩ := exists_runAmplitudes_of_weights w hw hsum
  have hafter : s.succ ≠ (0 : Fin (n + 1)) :=
    fun h => Nat.succ_ne_zero _ (congrArg Fin.val h)
  have hbefore : s.castSucc ≠ (0 : Fin (n + 1)) := fun h => hs (congrArg Fin.val h)
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · simp only [siteExcitedPopulation, hA, w, sum_excited_weights_add, sum_filter_runAtomWeight]
    simp
  · rw [noninitialSite_ready_mass A s hs, hA]
    simp [w, runAtomWeight, Ne.symm hafter, Ne.symm hbefore, Ne.symm hu₀]
  · simp [hA, w, runAtomWeight, s.castSucc_lt_succ.ne', Ne.symm hu₂, hafter]
  · simp [hA, w, runAtomWeight, s.castSucc_lt_succ.ne, Ne.symm hu₁, hbefore]

private theorem exists_product_slice {q x y : ℝ} (hq : 0 ≤ q) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hle : q ≤ x * y) : ∃ z : ℝ, 0 ≤ z ∧ z ≤ x ∧ z * y = q := by
  by_cases h : y = 0
  · have hq₀ : q = 0 := le_antisymm (by simpa only [h, mul_zero] using hle) hq
    exact ⟨0, le_rfl, hx, by rw [zero_mul, hq₀]⟩
  · have hy' : 0 < y := lt_of_le_of_ne hy (Ne.symm h)
    exact ⟨q / y, div_nonneg hq hy, (div_le_iff₀ hy').mpr hle, div_mul_cancel₀ _ h⟩

/-- With three or more sites, the full joint range at a noninitial
site is the interval from population readout to the recovery-dependent upper bound. -/
theorem exists_noninitialSite_joint_readout_iff (hn : 3 ≤ n) (s : Fin n) (hs : s.val ≠ 0)
    (p R d : ℝ) :
    (∃ A : RunAmplitudes n, siteExcitedPopulation A s = p ∧
      maskedRunMass ({s} : Finset (Fin n)) A = R ∧ siteReadoutDistance A s = d) ↔
      0 ≤ p ∧ 0 ≤ R ∧ p + R ≤ 1 ∧ p ≤ d ∧ d ≤ Real.sqrt (p * (1 - R)) := by
  constructor
  · rintro ⟨A, rfl, rfl, rfl⟩
    refine ⟨site_pop_nonneg A s, ?_, noninitialSite_population_add_ready_mass_le A s hs,
      (siteReadoutDistance_bounds A s).1, noninitialSite_readout_le_recovery_bound A s hs⟩
    rw [noninitialSite_ready_mass A s hs]
    positivity
  · rintro ⟨hp, hR, hsum, hpd, hd⟩
    let q := d ^ 2 - p ^ 2
    let g := 1 - p - R
    have hg : 0 ≤ g := by dsimp [g]; linarith only [hsum]
    have hd₀ : 0 ≤ d := hp.trans hpd
    have hq : 0 ≤ q := sub_nonneg.mpr ((sq_le_sq₀ hp hd₀).mpr hpd)
    have hpg : q ≤ p * g := by
      have hR₁ : 0 ≤ 1 - R := by linarith only [hp, hsum]
      have h := (sq_le_sq₀ hd₀ (Real.sqrt_nonneg _)).mpr hd
      rw [Real.sq_sqrt (mul_nonneg hp hR₁)] at h
      dsimp [q, g]
      nlinarith only [h]
    have finish (A : RunAmplitudes n) (hpop : siteExcitedPopulation A s = p)
        (hready : maskedRunMass ({s} : Finset (Fin n)) A = R)
        (hcoh : ‖A.1 s.succ‖ ^ 2 * ‖A.1 s.castSucc‖ ^ 2 = q) :
        ∃ A : RunAmplitudes n, siteExcitedPopulation A s = p ∧
          maskedRunMass ({s} : Finset (Fin n)) A = R ∧ siteReadoutDistance A s = d := by
      refine ⟨A, hpop, hready, (mul_self_inj (Real.sqrt_nonneg _) hd₀).mp ?_⟩
      change siteReadoutDistance A s * siteReadoutDistance A s = d * d
      rw [← pow_two, ← pow_two, siteReadoutDistance_sq, hpop, hcoh]
      dsimp [q]
      ring
    by_cases hsite : s.val = 1
    · let u : Fin (n + 1) := ⟨3, Nat.lt_succ_of_le hn⟩
      have hu₀ : u ≠ 0 := fun he => Nat.succ_ne_zero 2 (congrArg Fin.val he)
      have hu₁ : u ≠ s.castSucc := by
        intro he
        have h : 3 = s.val := congrArg Fin.val he
        omega
      have hu₂ : u ≠ s.succ := by
        intro he
        have h : 3 = s.val + 1 := congrArg Fin.val he
        omega
      have hu : s.val < u.val := by change s.val < 3; omega
      obtain ⟨a, ha, hap, hcoh⟩ := exists_product_slice hq hp hg hpg
      obtain ⟨A, hpop, hready, hafter, hbefore⟩ := exists_four_run_amplitudes s hs u hu₀ hu₁ hu₂
        a g (p - a) R ha hg (sub_nonneg.mpr hap) hR (by dsimp [g]; ring)
      refine finish A ?_ hready ?_
      · rw [hpop, if_pos hu]
        ring
      · rw [hafter, hbefore, hcoh]
    · let u : Fin (n + 1) := ⟨1, by omega⟩
      have hu₀ : u ≠ 0 := fun he => Nat.one_ne_zero (congrArg Fin.val he)
      have hu₁ : u ≠ s.castSucc := fun he => hsite (congrArg Fin.val he).symm
      have hu₂ : u ≠ s.succ := by
        intro he
        have h : 1 = s.val + 1 := congrArg Fin.val he
        omega
      have hu : ¬s.val < u.val := by change ¬s.val < 1; omega
      obtain ⟨b, hb, hbg, hcoh⟩ := exists_product_slice hq hg hp
        (by simpa only [mul_comm] using hpg)
      obtain ⟨A, hpop, hready, hafter, hbefore⟩ := exists_four_run_amplitudes s hs u hu₀ hu₁ hu₂
        p b (g - b) R hp hb (sub_nonneg.mpr hbg) hR (by dsimp [g]; ring)
      refine finish A ?_ hready ?_
      · rw [hpop, if_neg hu, add_zero]
      · rw [hafter, hbefore, mul_comm p b, hcoh]

/-- On a two-site chain the noninitial-site populations exhaust all
three runs, so the distance is forced to attain the upper bound. -/
theorem noninitial_two_site_readout_eq (A : RunAmplitudes 2) (s : Fin 2) (hs : s.val ≠ 0) :
    siteReadoutDistance A s = Real.sqrt
      (siteExcitedPopulation A s * (1 - maskedRunMass ({s} : Finset (Fin 2)) A)) := by
  have hs₁ : s = (1 : Fin 2) := Fin.ext (by have h := s.isLt; omega)
  subst s
  let w (j : Fin 3) := ‖A.1 j‖ ^ 2
  have hnorm : w 0 + w 1 + w 2 = 1 :=
    (Fin.sum_univ_three w).symm.trans A.2
  have hp : siteExcitedPopulation A (1 : Fin 2) = w 2 := by
    change (∑ j : Fin 3, if (1 : Fin 2).val < j.val then w j else 0) = w 2
    rw [Fin.sum_univ_three]
    simp
  have hR : maskedRunMass ({(1 : Fin 2)} : Finset (Fin 2)) A = w 0 :=
    noninitialSite_ready_mass A _ hs
  rw [siteReadoutDistance, norm_mul, norm_star, mul_pow, hp, hR]
  change √(w 2 ^ 2 + w 2 * w 1) = √(w 2 * (1 - w 0))
  rw [show w 1 = 1 - w 0 - w 2 by linarith only [hnorm]]
  congr 1
  ring

/-- The two-site noninitial range is the upper boundary of the longer-chain range. -/
theorem exists_noninitial_two_site_joint_readout_iff (s : Fin 2) (hs : s.val ≠ 0) (p R d : ℝ) :
    (∃ A : RunAmplitudes 2, siteExcitedPopulation A s = p ∧
      maskedRunMass ({s} : Finset (Fin 2)) A = R ∧ siteReadoutDistance A s = d) ↔
      0 ≤ p ∧ 0 ≤ R ∧ p + R ≤ 1 ∧ d = Real.sqrt (p * (1 - R)) := by
  constructor
  · rintro ⟨A, rfl, rfl, rfl⟩
    refine ⟨site_pop_nonneg A s, ?_, noninitialSite_population_add_ready_mass_le A s hs,
      noninitial_two_site_readout_eq A s hs⟩
    rw [noninitialSite_ready_mass A s hs]
    positivity
  · rintro ⟨hp, hR, hsum, rfl⟩
    exact exists_noninitialSite_attain_recovery_bound s hs p R hp hR hsum

private theorem initialSite_prefix_length (s : Fin n) (hs : s.val = 0) :
    accessiblePrefixLength ({s} : Finset (Fin n)) = 1 := by
  have hzero : (runSignature ({s} : Finset (Fin n)) s.succ).1 = fun _ => false := by
    funext i
    change decide (i.val.val < s.val + 1) = false
    apply decide_eq_false
    intro hi
    apply i.2
    exact Finset.mem_singleton.mpr (Fin.ext (by omega))
  have hl := (runSignature_lost_ready_iff ({s} : Finset (Fin n)) s.succ).mp hzero
  have hl' : 1 ≤ accessiblePrefixLength ({s} : Finset (Fin n)) := by simpa [hs] using hl
  apply le_antisymm _ hl'
  by_cases h : n ≤ 1
  · exact (accessiblePrefixLength_le _).trans h
  · let i : Fin n := ⟨1, by omega⟩
    have hi : i ∉ ({s} : Finset (Fin n)) := fun he =>
      Nat.one_ne_zero ((congrArg Fin.val (Finset.mem_singleton.mp he)).trans hs)
    exact accessiblePrefixLength_le_of_missing hi

/-- At the initial site the ready slice contains exactly the first two run lengths. -/
theorem initialSite_ready_mass_eq (A : RunAmplitudes n) (s : Fin n) (hs : s.val = 0) :
    maskedRunMass ({s} : Finset (Fin n)) A =
      ‖A.1 s.castSucc‖ ^ 2 + ‖A.1 s.succ‖ ^ 2 := by
  have hsucc : s.succ.val = 1 := by change s.val + 1 = 1; omega
  unfold maskedRunMass
  rw [initialSite_prefix_length s hs]
  calc
    _ = ∑ j, (runAtomWeight s.castSucc (‖A.1 s.castSucc‖ ^ 2) j +
        runAtomWeight s.succ (‖A.1 s.succ‖ ^ 2) j) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h₀ : j = s.castSucc
      · subst j
        simp [runAtomWeight, hs, s.castSucc_lt_succ.ne]
      · by_cases h₁ : j = s.succ
        · subst j
          simp [runAtomWeight, h₀, hs]
        · have hv : ¬j.val ≤ 1 := by
            intro h
            have hv₀ : j.val ≠ 0 := fun he => h₀ (Fin.ext (he.trans hs.symm))
            have hv₁ : j.val ≠ 1 := fun he => h₁ (Fin.ext (he.trans hsucc.symm))
            omega
          simp [runAtomWeight, h₀, h₁, hv]
    _ = _ := by rw [Finset.sum_add_distrib, sum_runAtomWeight, sum_runAtomWeight]

/-- At the initial site the two populations determine the distance at all chain lengths. -/
theorem initialSite_readout_eq (A : RunAmplitudes n) (s : Fin n) (hs : s.val = 0) :
    siteReadoutDistance A s = Real.sqrt (siteExcitedPopulation A s ^ 2 +
      (1 - siteExcitedPopulation A s) *
        (maskedRunMass ({s} : Finset (Fin n)) A + siteExcitedPopulation A s - 1)) := by
  have hg := initialSite_before_sq_eq_ground A s hs
  have hr := initialSite_ready_mass_eq A s hs
  have ha : ‖A.1 s.succ‖ ^ 2 =
      maskedRunMass ({s} : Finset (Fin n)) A + siteExcitedPopulation A s - 1 := by
    linarith only [hg, hr]
  rw [siteReadoutDistance, norm_mul, norm_star, mul_pow, ha, hg]
  congr 1
  ring

/-- With a second site available in the chain, every initial-site
population pair satisfying 1 - p ≤ R ≤ 1 occurs. Its distance is fixed. -/
theorem exists_initialSite_joint_readout_iff (hn : 2 ≤ n) (s : Fin n) (hs : s.val = 0)
    (p R d : ℝ) :
    (∃ A : RunAmplitudes n, siteExcitedPopulation A s = p ∧
      maskedRunMass ({s} : Finset (Fin n)) A = R ∧ siteReadoutDistance A s = d) ↔
      0 ≤ p ∧ p ≤ 1 ∧ 1 - p ≤ R ∧ R ≤ 1 ∧ d = Real.sqrt (p ^ 2 + (1 - p) * (R + p - 1)) := by
  constructor
  · rintro ⟨A, rfl, rfl, rfl⟩
    have hg := initialSite_before_sq_eq_ground A s hs
    have hr := initialSite_ready_mass_eq A s hs
    exact ⟨site_pop_nonneg A s, by linarith only [hg, sq_nonneg ‖A.1 s.castSucc‖],
      by linarith only [hg, hr, sq_nonneg ‖A.1 s.succ‖],
      ready_mass_le_one A _, initialSite_readout_eq A s hs⟩
  · rintro ⟨hp, hp₁, hRg, hR₁, rfl⟩
    let u : Fin (n + 1) := ⟨2, Nat.lt_succ_of_le hn⟩
    have hu₀ : u ≠ s.castSucc := fun he =>
      Nat.succ_ne_zero 1 ((congrArg Fin.val he).trans hs)
    have hu₁ : u ≠ s.succ := by
      intro he
      have h : 2 = s.val + 1 := congrArg Fin.val he
      omega
    have hu : s.val < u.val := by change s.val < 2; omega
    obtain ⟨A, hpop, ha, hb, _⟩ := exists_three_run_amplitudes s u hu₀ hu₁
      (R + p - 1) (1 - p) (1 - R) (by linarith only [hRg]) (sub_nonneg.mpr hp₁)
      (sub_nonneg.mpr hR₁) (by ring)
    have hp' : siteExcitedPopulation A s = p := by rw [hpop, if_pos hu]; ring
    have hR' : maskedRunMass ({s} : Finset (Fin n)) A = R := by
      rw [initialSite_ready_mass_eq A s hs, ha, hb]
      ring
    exact ⟨A, hp', hR', by rw [initialSite_readout_eq A s hs, hp', hR']⟩

/-- Retaining the sole site gives complete recovery. At every population
the readout distance is the square root of that population. -/
theorem exists_single_site_joint_readout_iff (s : Fin 1) (p R d : ℝ) :
    (∃ A : RunAmplitudes 1, siteExcitedPopulation A s = p ∧
      maskedRunMass ({s} : Finset (Fin 1)) A = R ∧ siteReadoutDistance A s = d) ↔
      0 ≤ p ∧ p ≤ 1 ∧ R = 1 ∧ d = Real.sqrt p := by
  have hs : s.val = 0 := congrArg Fin.val (Fin.eq_zero s)
  have hbefore : s.castSucc = (0 : Fin 2) := Fin.ext hs
  have hafter : s.succ = (1 : Fin 2) := Fin.ext (by change s.val + 1 = 1; omega)
  have hready (A : RunAmplitudes 1) : maskedRunMass ({s} : Finset (Fin 1)) A = 1 := by
    rw [initialSite_ready_mass_eq A s hs, hbefore, hafter]
    exact (Fin.sum_univ_two (fun j : Fin 2 => ‖A.1 j‖ ^ 2)).symm.trans A.2
  constructor
  · rintro ⟨A, rfl, rfl, rfl⟩
    have hg := initialSite_before_sq_eq_ground A s hs
    exact ⟨site_pop_nonneg A s, by linarith only [hg, sq_nonneg ‖A.1 s.castSucc‖],
      hready A, siteReadoutDistance_one A s⟩
  · rintro ⟨hp, hp₁, rfl, rfl⟩
    let w (j : Fin 2) := if j = 0 then 1 - p else p
    have hw (j : Fin 2) : 0 ≤ w j := by unfold w; split <;> linarith only [hp, hp₁]
    have hsum : ∑ j : Fin 2, w j = 1 := by rw [Fin.sum_univ_two]; simp [w]
    obtain ⟨A, hA⟩ := exists_runAmplitudes_of_weights (n := 1) w hw hsum
    have hg := initialSite_before_sq_eq_ground A s hs
    have hp' : siteExcitedPopulation A s = p := by
      rw [hA, hbefore, show w 0 = 1 - p by simp [w]] at hg
      linarith only [hg]
    exact ⟨A, hp', hready A, by rw [siteReadoutDistance_one, hp']⟩

#print axioms exists_noninitialSite_joint_readout_iff
#print axioms exists_noninitial_two_site_joint_readout_iff
#print axioms exists_initialSite_joint_readout_iff
#print axioms exists_single_site_joint_readout_iff

end

end GaloisForLFunctions.HilbertMetric.QuantumInformation.ReadyBranch
