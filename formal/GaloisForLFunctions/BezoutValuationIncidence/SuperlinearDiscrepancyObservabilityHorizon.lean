import GaloisForLFunctions.BezoutValuationIncidence.SuperlinearObservabilityHorizonAtArbitraryPhase
import GaloisForLFunctions.BezoutValuationIncidence.SharpInitialPrefixObservabilityAndExactGramDeterminants
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The prefix-discrepancy observability horizon is superlinear

Vanishing prefix discrepancy on `≍ N² log N` consecutive prefixes forces zero variance at every
phase (`sieveVariance_eq_zero_of_discrepancy_window_quadratic`). No linear number of prefixes does:
for every `m` and all large `N` a row of positive variance has vanishing discrepancy at the `mN + 1`
consecutive prefixes `A, …, A + mN` (`exists_discrepancy_zero_window`,
`not_exists_linear_discrepancy_observability_horizon`). In particular the universal horizon
`2N − 3`, valid at common returns and for `N ≤ 4`, fails at arbitrary phase for large `N`.

Mechanism: three alternating grids (`SuperlinearObservabilityHorizonAtArbitraryPhase`) with bases
`D, D − K, D − 2K`, `K = M 2^m`, share one phase, because all their moduli `D − Mτ`, `τ < 3·2^m`,
are pairwise coprime (`exists_joint_phase`). Each grid has zero response on the common window.
Two linear observables remain — the harmonic mode `H` and the discrepancy at the phase — and a
nonzero combination of the three grids kills both. On the window the discrepancy then starts at
zero and has zero increments `s − H`. The tops `D − iK` of the grids carry the combination
coefficients, so the variance is positive.
-/

open Finset GaloisForLFunctions.BiScaleUncertainty

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- Two linear functionals on `ℝ³` have a common nonzero zero. -/
private theorem exists_ne_zero_two_constraints (u v : Fin 3 → ℝ) :
    ∃ a : Fin 3 → ℝ, a ≠ 0 ∧ ∑ i, a i * u i = 0 ∧ ∑ i, a i * v i = 0 := by
  let f : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := Matrix.mulVecLin (Matrix.of ![u, v])
  have hker : LinearMap.ker f ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simp)
  obtain ⟨a, ha, hne⟩ := (Submodule.ne_bot_iff _).mp hker
  rw [LinearMap.mem_ker] at ha
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  simp [f, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1
  refine ⟨a, hne, ?_, ?_⟩ <;> simp only [Fin.sum_univ_three] <;> linarith

/-- The joint slope `τ = i 2^m + σ_S` of grid `i` and subset `S`. -/
private theorem jointSlope_inj {m i i' : ℕ} {S S' : Finset ℕ} (hS : S ⊆ range m)
    (hS' : S' ⊆ range m) (h : i * 2 ^ m + binarySlope S = i' * 2 ^ m + binarySlope S') :
    i = i' ∧ S = S' := by
  have hp : 0 < 2 ^ m := Nat.pos_of_ne_zero (by positivity)
  have hd : ∀ j (T : Finset ℕ), T ⊆ range m → (j * 2 ^ m + binarySlope T) / 2 ^ m = j := by
    intro j T hT
    rw [add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt (binarySlope_lt hT), zero_add]
  have hii : i = i' := by rw [← hd i S hS, h, hd i' S' hS']
  subst hii
  exact ⟨rfl, geomSum_injective le_rfl (by simpa [binarySlope] using h)⟩

private theorem gridModulus_shift (m D M i : ℕ) (S : Finset ℕ) :
    gridModulus (D - i * (M * 2 ^ m)) M S = D - M * (i * 2 ^ m + binarySlope S) := by
  rw [gridModulus, Nat.sub_sub, show M * (i * 2 ^ m + binarySlope S) =
    i * (M * 2 ^ m) + M * binarySlope S by ring]

/-- **One phase for three grids.** The bases `D − iM2^m`, `i < 3`, carry pairwise coprime moduli, so
one phase aligns all of them. -/
theorem exists_joint_phase {m D M : ℕ} (hM : ∀ q, 0 < q → q < 2 ^ (m + 2) → q ∣ M)
    (hD : Nat.Coprime D M) (hlarge : (m + 3) * (M * 2 ^ m) < D) :
    ∃ A : ℕ, ∀ i ∈ range 3, ∀ S ∈ (range m).powerset,
      gridModulus (D - i * (M * 2 ^ m)) M S ∣ A + gridOffset M S := by
  set t := (range 3) ×ˢ (range m).powerset with ht
  have hτ : ∀ p ∈ t, p.1 * 2 ^ m + binarySlope p.2 < 3 * 2 ^ m := by
    intro p hp
    obtain ⟨h1, h2⟩ := mem_product.mp hp
    have := binarySlope_lt (mem_powerset.mp h2)
    have : p.1 * 2 ^ m ≤ 2 * 2 ^ m := Nat.mul_le_mul_right _ (by simp at h1; omega)
    omega
  have hle : ∀ p ∈ t, M * (p.1 * 2 ^ m + binarySlope p.2) ≤ 3 * (M * 2 ^ m) := fun p hp => by
    have := Nat.mul_le_mul_left M (hτ p hp).le
    linarith
  have h3 : 3 * (M * 2 ^ m) ≤ (m + 3) * (M * 2 ^ m) := Nat.mul_le_mul_right _ (by omega)
  have hoff : ∀ p ∈ t, gridOffset M p.2 <
      gridModulus (D - p.1 * (M * 2 ^ m)) M p.2 := fun p hp => by
    rw [gridModulus_shift]
    have h1 := gridOffset_le (M := M) (mem_powerset.mp (mem_product.mp hp).2)
    have h2 := hle p hp
    have : m * (M * 2 ^ m) + 3 * (M * 2 ^ m) < D := by nlinarith
    omega
  have hs : ∀ p ∈ t, gridModulus (D - p.1 * (M * 2 ^ m)) M p.2 ≠ 0 := fun p hp =>
    ((Nat.zero_le _).trans_lt (hoff p hp)).ne'
  have pp : Set.Pairwise (t : Set (ℕ × Finset ℕ))
      (Function.onFun Nat.Coprime fun p => gridModulus (D - p.1 * (M * 2 ^ m)) M p.2) := by
    intro p hp p' hp' hne
    simp only [Function.onFun, gridModulus_shift]
    have hτp := hτ p hp
    have hτp' := hτ p' hp'
    have hneτ : p.1 * 2 ^ m + binarySlope p.2 ≠ p'.1 * 2 ^ m + binarySlope p'.2 := by
      intro heq
      obtain ⟨e1, e2⟩ := jointSlope_inj (mem_powerset.mp (mem_product.mp hp).2)
        (mem_powerset.mp (mem_product.mp hp').2) heq
      exact hne (Prod.ext e1 e2)
    have hM' : ∀ q, 0 < q → q < 2 ^ (m + 2) → q ∣ M := hM
    have h4 : 3 * 2 ^ m < 2 ^ (m + 2) := by rw [pow_add]; omega
    rcases Nat.lt_or_gt_of_ne hneτ with hlt | hlt
    · exact coprime_sub_mul_of_lt hM' hD hlt (by omega) (by linarith [hle p' hp'])
    · exact (coprime_sub_mul_of_lt hM' hD hlt (by omega) (by linarith [hle p hp])).symm
  obtain ⟨A, hA⟩ := Nat.chineseRemainderOfFinset
    (fun p => gridModulus (D - p.1 * (M * 2 ^ m)) M p.2 - gridOffset M p.2)
    (fun p => gridModulus (D - p.1 * (M * 2 ^ m)) M p.2) t hs pp
  refine ⟨A, fun i hi S hS => ?_⟩
  have hp : (i, S) ∈ t := mem_product.mpr ⟨hi, hS⟩
  have hlt := hoff (i, S) hp
  have hmod := (hA (i, S) hp).add_right (gridOffset M S)
  simp only at hmod hlt
  rw [Nat.sub_add_cancel hlt.le] at hmod
  exact (Nat.modEq_zero_iff_dvd).mp (hmod.trans ((Nat.modEq_zero_iff_dvd).mpr dvd_rfl))

/-- The grid with base `D − jM2^m` vanishes at the top `D − iM2^m` of every other grid. -/
private theorem gridRow_shift_top {m D M i j : ℕ} (hM : 0 < M) (hi : i < 3) (hj : j < 3)
    (hlarge : 3 * (M * 2 ^ m) ≤ D) :
    gridRow m (D - j * (M * 2 ^ m)) M (D - i * (M * 2 ^ m)) =
      if i = j then gridRow m (D - j * (M * 2 ^ m)) M (D - j * (M * 2 ^ m)) else 0 := by
  split_ifs with hij
  · rw [hij]
  · unfold gridRow
    refine sum_eq_zero fun S hS => if_neg fun heq => hij ?_
    rw [gridModulus_shift] at heq
    have hσ := binarySlope_lt (mem_powerset.mp hS)
    have hτ : M * (j * 2 ^ m + binarySlope S) ≤ D := by
      have : j * 2 ^ m + binarySlope S < 3 * 2 ^ m := by
        have : j * 2 ^ m ≤ 2 * 2 ^ m := Nat.mul_le_mul_right _ (by omega)
        omega
      have := Nat.mul_le_mul_left M this.le
      linarith
    have hi' : i * (M * 2 ^ m) = M * (i * 2 ^ m + binarySlope ∅) := by
      simp [binarySlope]; ring
    have hiD : i * (M * 2 ^ m) ≤ D := by
      have : i * (M * 2 ^ m) ≤ 3 * (M * 2 ^ m) := Nat.mul_le_mul_right _ (by omega)
      omega
    have hmul : M * (i * 2 ^ m + binarySlope ∅) = M * (j * 2 ^ m + binarySlope S) := by
      rw [← hi']; omega
    exact (jointSlope_inj (empty_subset _) (mem_powerset.mp hS)
      (Nat.eq_of_mul_eq_mul_left hM hmul)).1

private theorem sieveSeq_lincomb (N k : ℕ) (a : Fin 3 → ℝ) (r : Fin 3 → ℕ → ℝ) :
    sieveSeq N (fun d => ∑ i, a i * r i d) k = ∑ i, a i * sieveSeq N (r i) k := by
  unfold sieveSeq
  rw [sum_comm]
  exact sum_congr rfl fun i _ => (mul_sum _ _ _).symm

private theorem finiteHarmonicSum_lincomb (N : ℕ) (a : Fin 3 → ℝ) (r : Fin 3 → ℕ → ℝ) :
    finiteHarmonicSum N (fun d => ∑ i, a i * r i d) = ∑ i, a i * finiteHarmonicSum N (r i) := by
  unfold finiteHarmonicSum
  simp only [sum_div, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun d _ => by ring

private theorem finiteFloorSum_lincomb (N : ℕ) (x : ℝ) (a : Fin 3 → ℝ) (r : Fin 3 → ℕ → ℝ) :
    finiteFloorSum N (fun d => ∑ i, a i * r i d) x = ∑ i, a i * finiteFloorSum N (r i) x := by
  unfold finiteFloorSum
  simp only [sum_mul, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun d _ => by ring

private theorem sievePrefixDiscrepancy_lincomb (N M : ℕ) (a : Fin 3 → ℝ) (r : Fin 3 → ℕ → ℝ) :
    sievePrefixDiscrepancy N M (fun d => ∑ i, a i * r i d) =
      ∑ i, a i * sievePrefixDiscrepancy N M (r i) := by
  unfold sievePrefixDiscrepancy
  rw [finiteFloorSum_lincomb, finiteHarmonicSum_lincomb, mul_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun i _ => by ring

/-- **Superlinear discrepancy horizon.** For every `m` and every
`N ≥ (m + 4)(2^{m+3})!(1 + 3·2^{m+1})` some row of positive variance has vanishing prefix
discrepancy at the `mN + 1` consecutive prefixes `A, …, A + mN`. -/
theorem exists_discrepancy_zero_window (m N : ℕ)
    (hN : (m + 4) * ((2 ^ (m + 3)).factorial * (1 + 3 * 2 ^ (m + 1))) ≤ N) :
    ∃ (A : ℕ) (c : ℕ → ℝ), sieveVariance N c ≠ 0 ∧
      ∀ M' ∈ Icc A (A + m * N), sievePrefixDiscrepancy N M' c = 0 := by
  set M := (2 ^ (m + 3)).factorial with hMdef
  set K := M * 2 ^ (m + 1) with hK
  have hM0 : 0 < M := Nat.factorial_pos _
  have hN1 : 1 ≤ N := by
    have : 1 ≤ (m + 4) * (M * (1 + 3 * 2 ^ (m + 1))) := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (Nat.mul_ne_zero hM0.ne' (by positivity)))
    omega
  set D := 1 + (N - 1) / M * M with hDdef
  have hDN : D ≤ N := by have := Nat.div_mul_le_self (N - 1) M; omega
  have hND : N < D + M := by have := Nat.lt_div_mul_add (a := N - 1) hM0; omega
  have hcop : Nat.Coprime D M := by
    rw [hDdef, mul_comm, Nat.coprime_add_mul_left_left]
    exact Nat.coprime_one_left M
  have hNK : (m + 4) * (M + 3 * K) ≤ N := by
    have : M * (1 + 3 * 2 ^ (m + 1)) = M + 3 * K := by rw [hK]; ring
    rw [← this]; exact hN
  have hlarge : (m + 1 + 3) * K < D := by nlinarith
  have hdvd : ∀ q, 0 < q → q < 2 ^ (m + 1 + 2) → q ∣ M := fun q hq hq' =>
    Nat.dvd_factorial hq (by rw [show m + 1 + 2 = m + 3 by ring] at hq'; exact hq'.le)
  obtain ⟨A, hA⟩ := exists_joint_phase hdvd hcop hlarge
  -- the three grids
  have hdata : ∀ j < 3, GridData (m + 1) (D - j * K) M := fun j hj =>
    { dvd := fun q hq hq' => hdvd q hq (hq'.trans (Nat.pow_lt_pow_right (by norm_num) (by omega)))
      pos := hM0
      coprime := by
        have hjD : j * K ≤ D := by
          have : j * K ≤ 3 * K := Nat.mul_le_mul_right _ hj.le
          nlinarith
        have hjK : j * K = M * (j * 2 ^ (m + 1)) := by rw [hK]; ring
        have hrepr : D = D - j * K + M * (j * 2 ^ (m + 1)) := by rw [← hjK]; omega
        have := hcop
        rw [hrepr] at this
        exact (Nat.coprime_add_mul_left_left _ _ _).mp this
      large := by
        rw [← hK]
        have : j * K ≤ 2 * K := Nat.mul_le_mul_right _ (by omega)
        have : (m + 1 + 1) * K + j * K < D := by nlinarith
        omega }
  let r : Fin 3 → ℕ → ℝ := fun i => gridRow (m + 1) (D - (i : ℕ) * K) M
  set W := (m + 1) * (D - 3 * K) with hW
  have hzero : ∀ i : Fin 3, ∀ k ∈ Ico A (A + W), sieveSeq N (r i) k = 0 := by
    intro i k hk
    have hi := i.isLt
    refine gridRow_response_eq_zero (hdata i hi) ((Nat.sub_le _ _).trans hDN)
      (hA i (mem_range.mpr hi)) ?_
    obtain ⟨hk1, hk2⟩ := mem_Ico.mp hk
    refine mem_Ico.mpr ⟨hk1, lt_of_lt_of_le hk2 (Nat.add_le_add_left
      (Nat.mul_le_mul_left _ ?_) A)⟩
    rw [← hK]
    have : (i : ℕ) * K ≤ 2 * K := Nat.mul_le_mul_right _ (by omega)
    omega
  obtain ⟨a, ha, hH, hL⟩ := exists_ne_zero_two_constraints
    (fun i => finiteHarmonicSum N (r i)) (fun i => sievePrefixDiscrepancy N A (r i))
  set c : ℕ → ℝ := fun d => ∑ i, a i * r i d with hc
  have hHc : finiteHarmonicSum N c = 0 := by rw [hc, finiteHarmonicSum_lincomb]; exact hH
  have hLc : sievePrefixDiscrepancy N A c = 0 := by
    rw [hc, sievePrefixDiscrepancy_lincomb]; exact hL
  have hwin : m * N < W := by
    rw [hW]
    have h3K : 3 * K ≤ D := by nlinarith
    obtain ⟨E, hE⟩ : ∃ E, D = E + 3 * K := ⟨D - 3 * K, (Nat.sub_add_cancel h3K).symm⟩
    rw [hE, Nat.add_sub_cancel]
    have h1 : N + 1 ≤ E + M + 3 * K := by omega
    have h2 := Nat.mul_le_mul_left (m + 1) h1
    nlinarith
  refine ⟨A, c, ?_, ?_⟩
  · -- positive variance: the grid tops carry the coefficients
    obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
    have hci : c (D - (i : ℕ) * K) = a i := by
      rw [hc]
      simp only [r]
      rw [Fin.sum_univ_three]
      have htop : ∀ j : Fin 3, gridRow (m + 1) (D - (j : ℕ) * K) M (D - (i : ℕ) * K) =
          if (i : ℕ) = j then 1 else 0 := by
        intro j
        rw [gridRow_shift_top hM0 i.isLt j.isLt (by nlinarith)]
        split_ifs
        · exact gridRow_top (hdata j j.isLt)
        · rfl
      rw [htop 0, htop 1, htop 2]
      fin_cases i <;> simp
    intro hvar
    have hD2 : 2 ≤ D - (i : ℕ) * K := by
      have h1 : (i : ℕ) * K ≤ 2 * K := Nat.mul_le_mul_right _ (by omega)
      have h2 : (m + 1 + 1) * K + 2 * K < D := by nlinarith
      have hK1 : 1 ≤ K := by rw [hK]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
      exact Nat.le_sub_of_add_le (by nlinarith)
    have := (sieveVariance_eq_zero_iff_tail_zero N c).mp hvar (D - (i : ℕ) * K)
      (mem_Icc.mpr ⟨hD2, (Nat.sub_le _ _).trans hDN⟩)
    rw [hci] at this
    exact hi this
  · -- the discrepancy vanishes along the window
    have hW' : ∀ t, t ≤ m * N → t < W := fun t ht => lt_of_le_of_lt ht hwin
    have key : ∀ j, j ≤ m * N → sievePrefixDiscrepancy N (A + j) c = 0 := by
      intro j
      induction j with
      | zero => intro _; simpa using hLc
      | succ j ih =>
        intro hj
        have hprev := ih (by omega)
        have hstep := sievePrefixDiscrepancy_succ_sub N (A + j) c
        have hj1 := hW' (j + 1) hj
        have hmem : A + j + 1 ∈ Ico A (A + W) :=
          mem_Ico.mpr ⟨by omega, by rw [add_assoc]; exact Nat.add_lt_add_left hj1 A⟩
        have hs : sieveSeq N c (A + j + 1) = 0 := by
          rw [hc, sieveSeq_lincomb]
          exact sum_eq_zero fun i _ => by rw [hzero i (A + j + 1) hmem, mul_zero]
        rw [← sieveSeq_eq_sievedDivisorSum N c (by omega), hs, hHc, hprev] at hstep
        rw [← add_assoc]
        linarith
    intro M' hM'
    obtain ⟨h1, h2⟩ := mem_Icc.mp hM'
    obtain ⟨j, rfl⟩ : ∃ j, M' = A + j := ⟨M' - A, by omega⟩
    exact key j (by omega)

/-- **No linear discrepancy observability law at arbitrary phase.** -/
theorem not_exists_linear_discrepancy_observability_horizon :
    ¬ ∃ C : ℕ, ∀ (N A : ℕ) (c : ℕ → ℝ),
      (∀ M ∈ Icc A (A + C * N), sievePrefixDiscrepancy N M c = 0) → sieveVariance N c = 0 := by
  rintro ⟨C, hC⟩
  obtain ⟨A, c, hvar, hz⟩ := exists_discrepancy_zero_window C _ le_rfl
  exact hvar (hC _ A c hz)

end

end GaloisForLFunctions.BezoutValuationIncidence
