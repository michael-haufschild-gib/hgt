import GaloisForLFunctions.RHTower.CCMPrimeMomentPotentialEscape

/-!
# Upper contact for the actual nonlinear prime discrepancy

A mass lying above the physical square-root curve must eventually meet it:
otherwise the actual Abel potential is nondecreasing, contrary to its proved
negative escape. Until the first contact, prime admissions increase the
nonlinear discrepancy. At contact the continuous potential equals that
stored discrepancy, with no positive-square remainder.

Consequently every upward discrepancy crossing forces a later potential
crossing. The two actual sources have exactly the same eventual strict
finite upper levels. No RH or eventual-sign premise is assumed for this
comparison; neither source's eventual negativity is proved here.
-/

noncomputable section
open Filter Topology
open GaloisForLFunctions.RHTower
namespace RHTower

private theorem mass_succ (n : ℕ) :
    primeMassHalf ((n+1 : ℕ) : ℝ) = primeMassHalf n + criticalMellinAtomWeight (n+1) := by
  simp only [primeMassHalf, Nat.floor_natCast, criticalMellinAtomWeight_eq_div_sqrt]
  rw [Finset.sum_Icc_succ_top (by omega : 0 ≤ n+1)]

private theorem atom_nonneg (n : ℕ) : 0 ≤ criticalMellinAtomWeight n := by
  rw [criticalMellinAtomWeight_eq_div_sqrt]
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

private theorem discrepancy_step (n : ℕ) :
    ccmPrimeMomentDiscrepancy (n+1)-ccmPrimeMomentDiscrepancy n =
      criticalMellinAtomWeight (n+1) *
        (1+primeMassHalf n/2-Real.sqrt (n+1 : ℕ)) +
          criticalMellinAtomWeight (n+1)^2/4 := by
  have hp : Chebyshev.psi ((n+1 : ℕ) : ℝ) =
      Chebyshev.psi n + ArithmeticFunction.vonMangoldt (n+1) := by
    simp only [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
    rw [Finset.sum_Icc_succ_top (by omega : 0 ≤ n+1)]
  have hw : Real.sqrt (n+1 : ℕ)*criticalMellinAtomWeight (n+1) =
      ArithmeticFunction.vonMangoldt (n+1) := by
    rw [criticalMellinAtomWeight_eq_div_sqrt, mul_div_cancel₀ _
      (Real.sqrt_ne_zero'.mpr (by positivity))]
  unfold ccmPrimeMomentDiscrepancy
  rw [mass_succ, hp]
  linear_combination hw

private theorem exists_upper_contact (n : ℕ) :
    ∃ j : ℕ, 1+primeMassHalf (n+j : ℕ)/2 < Real.sqrt (n+j+1 : ℕ) := by
  by_contra! h
  have hm : Monotone (fun j : ℕ => ccmPrimeMomentPotential (n+j)) := by
    apply monotone_nat_of_le_succ
    intro j
    have hg : 0 ≤ Real.sqrt (n+j+1 : ℕ)-Real.sqrt (n+j : ℕ) := by
      exact sub_nonneg.mpr (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ (n+j)))
    have hi := ccmPrimeMomentPotential_succ_sub (n+j)
    have hb : 0 ≤ primeMassHalf (n+j : ℕ)+2-Real.sqrt (n+j+1 : ℕ)-Real.sqrt (n+j : ℕ) := by
      linarith [h j]
    have hp := mul_nonneg hg hb
    simp only [Nat.add_assoc] at hi hp ⊢
    linarith
  obtain ⟨k,hk,hu⟩ := ccmPrimeMomentPotential_negative_escape
    (-ccmPrimeMomentPotential n) n
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk
  have hh := hm (Nat.zero_le j)
  simp only [Nat.add_zero] at hh
  linarith

/-- Upper contact realizes at least the stored discrepancy in the later continuous
potential. Actual negative escape forces the contact to occur. -/
theorem ccmPrimeMomentDiscrepancy_le_later_potential_of_mass_ge
    (n : ℕ) (hn : 1 ≤ n) (hm : Real.sqrt n ≤ 1+primeMassHalf n/2) :
    ∃ T : ℝ, Real.log n ≤ T ∧ ccmPrimeMomentDiscrepancy n ≤ ccmPrimeMomentLogPotential T := by
  classical
  have hex := exists_upper_contact n
  let j := Nat.find hex
  have hright : 1+primeMassHalf (n+j : ℕ)/2 < Real.sqrt (n+j+1 : ℕ) := Nat.find_spec hex
  have hbefore (i : ℕ) (hi : i < j) :
      Real.sqrt (n+i+1 : ℕ) ≤ 1+primeMassHalf (n+i : ℕ)/2 := by
    exact le_of_not_gt (Nat.find_min hex hi)
  have hbudget (i : ℕ) (hi : i ≤ j) :
      ccmPrimeMomentDiscrepancy n ≤ ccmPrimeMomentDiscrepancy (n+i) := by
    induction i with
    | zero => simp
    | succ i ih =>
      have hb := hbefore i (by omega)
      have hs := discrepancy_step (n+i)
      have hp := mul_nonneg (atom_nonneg (n+i+1)) (sub_nonneg.mpr hb)
      have hsq := sq_nonneg (criticalMellinAtomWeight (n+i+1))
      have hh := ih (by omega)
      simp only [Nat.add_assoc] at *
      linarith
  have hleft : Real.sqrt (n+j : ℕ) ≤ 1+primeMassHalf (n+j : ℕ)/2 := by
    cases hj : j with
    | zero => simpa using hm
    | succ i =>
      have hb := hbefore i (by omega)
      have hs := mass_succ (n+i)
      have hw := atom_nonneg (n+i+1)
      simp only [Nat.add_assoc] at *
      linarith
  let k := n+j
  let m : ℝ := 1+primeMassHalf k/2
  have hm0 : 0 ≤ m := by dsimp [m]; linarith [routeP_primeMass_nonneg (k : ℝ)]
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hlo : (k : ℝ) ≤ m^2 := by
    have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) k)
    change Real.sqrt k ≤ m at hleft
    nlinarith [Real.sqrt_nonneg (k : ℝ)]
  have hhi : m^2 < (k : ℝ)+1 := by
    have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (k+1))
    change m < Real.sqrt (k+1 : ℕ) at hright
    push_cast at hs hright
    nlinarith [Real.sqrt_nonneg ((k : ℝ)+1)]
  have hx : 1 ≤ m^2 := (by exact_mod_cast hk : (1 : ℝ) ≤ k).trans hlo
  have hf : ⌊m^2⌋₊ = k := (Nat.floor_eq_iff (by positivity)).mpr ⟨hlo,hhi⟩
  have hmass : primeMassHalf (m^2) = primeMassHalf k := by simp [primeMassHalf, hf]
  have hpsi : Chebyshev.psi (m^2) = Chebyshev.psi k := by simp [Chebyshev.psi_eq_sum_Icc, hf]
  refine ⟨Real.log (m^2), ?_, ?_⟩
  · apply Real.log_le_log (by exact_mod_cast (by omega : 0 < n))
    have hnk : (n : ℝ) ≤ k := by exact_mod_cast (show n ≤ k by dsimp [k]; omega)
    exact hnk.trans hlo
  · have hu := ccmPrimeMomentLogPotential_eq_source (Real.log_nonneg hx)
    rw [Real.exp_log (by linarith), hmass, hpsi, Real.sqrt_sq hm0] at hu
    have hd : ccmPrimeMomentDiscrepancy k = m^2-Chebyshev.psi k-1 := by
      unfold ccmPrimeMomentDiscrepancy
      dsimp [m]
      ring
    have he : ccmPrimeMomentLogPotential (Real.log (m^2)) = ccmPrimeMomentDiscrepancy k := by
      rw [hu, hd]
      dsimp [m]
      ring
    rw [he]
    exact hbudget j le_rfl


private theorem mass_gt_of_discrepancy_increase (n : ℕ)
    (h : ccmPrimeMomentDiscrepancy n < ccmPrimeMomentDiscrepancy (n+1)) :
    Real.sqrt (n+1 : ℕ) < 1+primeMassHalf (n+1 : ℕ)/2 := by
  by_contra! hb
  have hs := discrepancy_step n
  have hm := mass_succ n
  have hw := atom_nonneg (n+1)
  have hpre : 1+primeMassHalf n/2-Real.sqrt (n+1 : ℕ) ≤
      -criticalMellinAtomWeight (n+1)/2 := by linarith
  have hp := mul_le_mul_of_nonneg_left hpre hw
  nlinarith [sq_nonneg (criticalMellinAtomWeight (n+1))]

/-- A return above a level after starting below it cannot be caused by the positive
square alone: the actual continuous potential also reaches that level later. -/
theorem ccmPrimeMoment_return_forces_potential_return
    (A : ℝ) (N n : ℕ) (hN : 1 ≤ N) (hn : N ≤ n)
    (hstart : ccmPrimeMomentDiscrepancy N < A)
    (hend : A ≤ ccmPrimeMomentDiscrepancy n) :
    ∃ T : ℝ, Real.log N ≤ T ∧ A ≤ ccmPrimeMomentLogPotential T := by
  classical
  have hex : ∃ j : ℕ, A ≤ ccmPrimeMomentDiscrepancy (N+j) := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hn
    exact ⟨j,hend⟩
  let j := Nat.find hex
  have hlast : A ≤ ccmPrimeMomentDiscrepancy (N+j) := Nat.find_spec hex
  have hj : 0 < j := by
    by_contra! hj
    have hz : j = 0 := by omega
    simp only [hz,Nat.add_zero] at hlast
    linarith
  let i := j-1
  have hi : i < j := by dsimp [i]; omega
  have hidx : N+i+1 = N+j := by dsimp [i]; omega
  have hprev : ccmPrimeMomentDiscrepancy (N+i) < A :=
    lt_of_not_ge (Nat.find_min hex hi)
  have hinc : ccmPrimeMomentDiscrepancy (N+i) < ccmPrimeMomentDiscrepancy (N+i+1) := by
    rw [hidx]
    exact hprev.trans_le hlast
  have hm := mass_gt_of_discrepancy_increase (N+i) hinc
  obtain ⟨T,hT,hU⟩ := ccmPrimeMomentDiscrepancy_le_later_potential_of_mass_ge
    (N+i+1) (by omega) hm.le
  refine ⟨T, ?_, ?_⟩
  · apply le_trans ?_ hT
    apply Real.log_le_log (by exact_mod_cast (by omega : 0 < N))
    exact_mod_cast (show N ≤ N+i+1 by omega)
  · rw [hidx] at hU
    exact hlast.trans hU

/-- On each actual prime cell the potential is the discrepancy minus a square. -/
theorem ccmPrimeMomentLogPotential_le_discrepancy {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeMomentLogPotential T ≤ ccmPrimeMomentDiscrepancy ⌊Real.exp T⌋₊ := by
  have hm : primeMassHalf (Real.exp T) = primeMassHalf (⌊Real.exp T⌋₊ : ℕ) := by
    simp [primeMassHalf]
  have hp : Chebyshev.psi (Real.exp T) = Chebyshev.psi (⌊Real.exp T⌋₊ : ℕ) := by
    simp [Chebyshev.psi_eq_sum_Icc]
  rw [ccmPrimeMomentLogPotential_eq_source hT,hm,hp]
  unfold ccmPrimeMomentDiscrepancy
  have hsq := Real.sq_sqrt (Real.exp_pos T).le
  nlinarith only [hsq, sq_nonneg
    (1+primeMassHalf (⌊Real.exp T⌋₊ : ℕ)/2-Real.sqrt (Real.exp T))]

/-- The actual nonlinear discrepancy and linear Abel potential have exactly the
same eventual strict upper levels, unconditionally. -/
theorem ccmPrimeMoment_eventual_upper_level_iff (A : ℝ) :
    (∃ N : ℕ, ∀ n : ℕ, N ≤ n → ccmPrimeMomentDiscrepancy n < A) ↔
      ∃ H : ℝ, ∀ T : ℝ, H ≤ T → ccmPrimeMomentLogPotential T < A := by
  constructor
  · rintro ⟨N,hN⟩
    refine ⟨max 0 (Real.log ((N : ℝ)+1)), fun T hT => ?_⟩
    have hT0 : 0 ≤ T := (le_max_left _ _).trans hT
    have hx := Real.exp_le_exp.mpr ((le_max_right _ _).trans hT)
    rw [Real.exp_log (by positivity)] at hx
    have hn : N ≤ ⌊Real.exp T⌋₊ := Nat.le_floor (by linarith)
    exact (ccmPrimeMomentLogPotential_le_discrepancy hT0).trans_lt (hN _ hn)
  · rintro ⟨H,hH⟩
    obtain ⟨N,hN⟩ := exists_nat_ge (max (1 : ℝ) (Real.exp H))
    have hN1 : 1 ≤ N := by exact_mod_cast (le_max_left (1 : ℝ) (Real.exp H)).trans hN
    obtain ⟨k,hk,hD⟩ := ccmPrimeMomentDiscrepancy_negative_escape (-A) N
    have hD' : ccmPrimeMomentDiscrepancy k < A := by simpa only [neg_neg] using hD
    have hlog : H ≤ Real.log k := by
      have he : Real.exp H ≤ (k : ℝ) :=
        ((le_max_right _ _).trans hN).trans (by exact_mod_cast hk)
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos H) he
    refine ⟨k, fun n hn => ?_⟩
    by_contra! hbad
    obtain ⟨T,hT,hU⟩ := ccmPrimeMoment_return_forces_potential_return A k n
      (hN1.trans hk) hn hD' hbad
    exact (not_lt_of_ge hU) (hH T (hlog.trans hT))

end RHTower
