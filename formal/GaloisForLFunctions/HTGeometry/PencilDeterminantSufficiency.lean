/-
# The several-variable sufficiency half, in determinant form

Feeding the several-variable sufficiency construction through the order-shift identity and Schatten
continuity of the regularized determinant gives the several-variable form of the sufficiency half of
`(DC)`: at every parameter the *plain* determinants of the finite-rank pencils converge to the
exponential of the prescribed jet times the order-`p` regularized determinant of the given pencil.

Main results:
* `exists_uniform_schattenNorm_bound` — a Schatten-convergent family is uniformly bounded.
* `exists_finiteRankPencil_tendsto_plainDet` — **the several-variable sufficiency half of `(DC)`**.
-/
import GaloisForLFunctions.HTGeometry.PencilSufficiencyLaw
import GaloisForLFunctions.HTGeometry.DeterminantCompletionLaw

open Filter Topology ContinuousLinearMap Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- **A Schatten-convergent family is uniformly bounded**, together with its limit. -/
theorem exists_uniform_schattenNorm_bound {p : ℝ} (hp : 0 < p) {X : ℕ → H →L[ℂ] H}
    {T : H →L[ℂ] H} (hT : MemSchattenClass p T)
    (hD : ∀ n, MemSchattenClass p (X n - T))
    (htend : Tendsto (fun n => schattenNorm p (X n - T)) atTop (nhds 0)) :
    ∃ C : ℝ, 1 ≤ C ∧ (∀ n, schattenNorm p (X n) ≤ C) ∧ schattenNorm p T ≤ C := by
  classical
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, ∀ n, schattenNorm p (X n - T) ≤ C₀ := by
    obtain ⟨C₀, hC₀⟩ := htend.bddAbove_range
    exact ⟨C₀, fun n => hC₀ ⟨n, rfl⟩⟩
  have hC₀0 : (0 : ℝ) ≤ C₀ := le_trans (schattenNorm_nonneg _ _) (hC₀ 0)
  obtain ⟨K, hK⟩ : ∃ K : ℝ,
      K = 2 ^ (p + 1) * (C₀ ^ p + schattenNorm p T ^ p) := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max 1 (max (K ^ (1 / p)) (schattenNorm p T)) := ⟨_, rfl⟩
  have hC1 : (1 : ℝ) ≤ C := by rw [hCdef]; exact le_max_left _ _
  have hCT : schattenNorm p T ≤ C := by
    rw [hCdef]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have htwo : (0 : ℝ) ≤ 2 ^ (p + 1) := Real.rpow_nonneg (by norm_num) _
  refine ⟨C, hC1, fun n => ?_, hCT⟩
  have hsplit : schattenNorm p (X n) ^ p
      ≤ 2 ^ (p + 1) * (schattenNorm p (X n - T) ^ p + schattenNorm p T ^ p) := by
    have h := schattenNorm_add_rpow_le hp (hD n) hT
    rwa [show X n - T + T = X n by abel] at h
  have hmono : schattenNorm p (X n - T) ^ p ≤ C₀ ^ p :=
    Real.rpow_le_rpow (schattenNorm_nonneg _ _) (hC₀ n) hp.le
  have hXK : schattenNorm p (X n) ^ p ≤ K := by
    rw [hK]
    nlinarith [hsplit, hmono, htwo]
  have hnn : (0 : ℝ) ≤ schattenNorm p (X n) := schattenNorm_nonneg _ _
  calc schattenNorm p (X n) = (schattenNorm p (X n) ^ p) ^ (1 / p) := by
        rw [← Real.rpow_mul hnn, mul_one_div, div_self hp.ne', Real.rpow_one]
    _ ≤ K ^ (1 / p) := Real.rpow_le_rpow (Real.rpow_nonneg hnn _) hXK (by positivity)
    _ ≤ C := by rw [hCdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)

/-- **The several-variable sufficiency half of `(DC)`.**  At every parameter the plain determinants
of the finite-rank pencils converge to the exponential of the prescribed jet times the order-`p`
regularized determinant of the given pencil. -/
theorem exists_finiteRankPencil_tendsto_plainDet (hH : ¬ FiniteDimensional ℂ H) {p d : ℕ}
    (hp : 0 < p) {A : Fin d → (H →L[ℂ] H)} (hA : ∀ j, MemSchattenClass (p : ℝ) (A j))
    (P : ℕ → (Fin d → ℂ) → ℂ)
    (hP : ∀ k, 1 ≤ k → k ≤ p - 1 → P k ∈ Submodule.span ℂ (clmPowSet (Fin d → ℂ) k)) :
    ∃ F : ℕ → Fin d → (H →L[ℂ] H),
      (∀ n j, ∃ N : ℕ, HasRankLE (F n j) N) ∧
      (∀ v : Fin d → ℂ, Tendsto (fun n => schattenNorm (p : ℝ)
        (pencilOperator (F n) v - pencilOperator A v)) atTop (nhds 0)) ∧
      (∀ v : Fin d → ℂ, ∃ C : ℝ, 1 ≤ C ∧ ∀ z : ℂ, ‖z‖ * (2 * C) < 1 →
        Tendsto (fun n => opSchattenDet 1 (pencilOperator (F n) v) z) atTop
          (nhds (opSchattenDet p (pencilOperator A v) z
            * Complex.exp (∑ m ∈ Finset.Ico 1 p, P m v * z ^ m)))) := by
  classical
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  obtain ⟨F, hFrank, hFtend, hFtrace⟩ := exists_finiteRankPencil_tendsto_lowTrace hH hp hA P hP
  refine ⟨F, hFrank, hFtend, ?_⟩
  intro v
  have hXmem : ∀ n, MemSchattenClass (p : ℝ) (pencilOperator (F n) v) := by
    intro n
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ j, HasRankLE (F n j) N := by
      choose Nf hNf using hFrank n
      exact ⟨Finset.univ.sup Nf, fun j => (hNf j).mono (Finset.le_sup (Finset.mem_univ j))⟩
    exact memSchattenClass_pencilOperator_of_hasRankLE hpR hN v
  have hTmem : MemSchattenClass (p : ℝ) (pencilOperator A v) :=
    memSchattenClass_pencilOperator hpR hA v
  have hDmem : ∀ n, MemSchattenClass (p : ℝ)
      (pencilOperator (F n) v - pencilOperator A v) :=
    fun n => memSchattenClass_sub hpR (hXmem n) hTmem
  obtain ⟨C, hC1, hCA, hCT⟩ :=
    exists_uniform_schattenNorm_bound hpR hTmem hDmem (hFtend v)
  refine ⟨C, hC1, ?_⟩
  intro z hz
  have hB1 : (1 : ℝ) ≤ 2 * C := by linarith
  have hdetp := tendsto_opSchattenDet_of_tendsto_schattenNorm hp hXmem hTmem hDmem hC1 hCA
    (hFtend v) hz
  have hshift : ∀ n : ℕ, opSchattenDet 1 (pencilOperator (F n) v) z
      = opSchattenDet p (pencilOperator (F n) v) z
        * Complex.exp (∑ m ∈ Finset.Ico 1 p, P m v * z ^ m) := by
    intro n
    have hbound : ∀ k : ℕ,
        ‖(fun m => opTrace ((pencilOperator (F n) v) ^ m)) (k + p)‖
          ≤ ((1 + (p : ℝ)) * C ^ (p : ℝ)) * (2 * C) ^ k :=
      fun k => norm_opTrace_pow_add_le hp (hXmem n) hC1 (hCA n) k
    have hord := tracePowerDet_order_shift
      (τ := fun m => opTrace ((pencilOperator (F n) v) ^ m)) hp hB1 hbound hz (q := 1) hp
    have hhead : (∑ m ∈ Finset.Ico 1 p,
        tracePowerTerm (fun m => opTrace ((pencilOperator (F n) v) ^ m)) z m)
        = -∑ m ∈ Finset.Ico 1 p, P m v * z ^ m := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [Finset.mem_Ico] at hm
      have hmne : ((m : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      show z ^ m / (m : ℂ) * opTrace ((pencilOperator (F n) v) ^ m) = -(P m v * z ^ m)
      rw [hFtrace n v m hm.1 (by omega)]
      field_simp
    rw [opSchattenDet_eq_tracePowerDet, opSchattenDet_eq_tracePowerDet, hord, hhead, neg_neg]
  exact (hdetp.mul_const (Complex.exp (∑ m ∈ Finset.Ico 1 p, P m v * z ^ m))).congr
    fun n => (hshift n).symm

end

end GaloisForLFunctions.HTGeometry
