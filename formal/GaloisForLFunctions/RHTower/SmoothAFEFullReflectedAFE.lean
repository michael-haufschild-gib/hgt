import GaloisForLFunctions.RHTower.SmoothAFEFullReflectedLocalTarget
import GaloisForLFunctions.RHTower.SmoothAFEReflectedComplementCharacterStability
import GaloisForLFunctions.RHTower.SmoothAFEReflectedPoleBound

open Complex MeasureTheory Filter Finset
open scoped Topology
noncomputable section
namespace RHTower
open SteinhausModel

/-- The coefficient-faithful full reflected AFE, including reciprocal complementary
characters and the literal pole correction. -/
def steinhausFullReflectedAFE (d tau : ℝ) (N : ℕ) (ω : Omega) : ℂ :=
  steinhausFullReflectedPrimalCarrier d tau N ω +
    steinhausFullReflectedComplement d tau N ω -
    zetaChi (rightDisplacedLinePt d tau) *
      smoothAFEZetaShiftedPoleResidue (displacedLinePt d (-tau)) N

/-- At the physical phase the complete carrier is exactly zeta. -/
theorem steinhausFullReflectedAFE_zero {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (tau : ℝ) {N : ℕ} (hN : 0 < N) :
    steinhausFullReflectedAFE d tau N (fun _ => 0) =
      riemannZeta (rightDisplacedLinePt d tau) := by
  rw [steinhausFullReflectedAFE, steinhausFullReflectedPrimalCarrier_eq_tsum]
  have hX (n : ℕ) : X n (fun _ => 0) = 1 := by simp [X]
  simp only [steinhausFullReflectedComplement, hX, map_one, mul_one]
  exact (riemannZeta_rightDisplaced_eq_reflectedPrimal_add_complement
    (by exact_mod_cast hN) hd hdhalf tau).symm

/-- The bounded non-primal part of the complete reflected AFE. -/
def steinhausHilbertReflectedCorrection {J : ℕ} (d b : Fin J → ℝ)
    (tau : ℝ) (N : ℕ) (ω : Omega) : EuclideanSpace ℂ (Fin J) :=
  WithLp.toLp 2 (fun j => steinhausFullReflectedComplement (d j) (tau + b j) N ω -
    zetaChi (rightDisplacedLinePt (d j) (tau + b j)) *
      smoothAFEZetaShiftedPoleResidue (displacedLinePt (d j) (-(tau + b j))) N)

/-- Complete reflected AFE at every finite common-height node. -/
def steinhausHilbertFullReflectedAFE {J : ℕ} (d b : Fin J → ℝ)
    (tau : ℝ) (N : ℕ) (ω : Omega) : EuclideanSpace ℂ (Fin J) :=
  steinhausHilbertFullReflectedCarrier d b tau N ω +
    steinhausHilbertReflectedCorrection d b tau N ω

/-- Vector assembly retains the exact scalar AFE at each node. -/
theorem steinhausHilbertFullReflectedAFE_apply {J : ℕ} (d b : Fin J → ℝ)
    (tau : ℝ) (N : ℕ) (ω : Omega) (j : Fin J) :
    steinhausHilbertFullReflectedAFE d b tau N ω j =
      steinhausFullReflectedAFE (d j) (tau + b j) N ω := by
  let P := steinhausFullReflectedPrimalCarrier (d j) (tau + b j) N ω
  let C := steinhausFullReflectedComplement (d j) (tau + b j) N ω
  let Z := zetaChi (rightDisplacedLinePt (d j) (tau + b j)) *
    smoothAFEZetaShiftedPoleResidue (displacedLinePt (d j) (-(tau + b j))) N
  change P + (C - Z) = (P + C) - Z
  ring

private theorem norm_le_card_mul_of_coord_le {J : ℕ} (hJ : 0 < J)
    (v : EuclideanSpace ℂ (Fin J)) {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ j, ‖v j‖ ≤ C) : ‖v‖ ≤ J * C := by
  have hJR : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hsq : ‖v‖ ^ 2 ≤ (J : ℝ) * C ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _j : Fin J, C ^ 2 :=
        sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hv j) 2)
      _ = _ := by simp
  have hJ2 : (J : ℝ) ≤ (J : ℝ) ^ 2 := by nlinarith
  apply (sq_le_sq₀ (norm_nonneg v) (mul_nonneg (Nat.cast_nonneg J) hC)).mp
  calc
    ‖v‖ ^ 2 ≤ (J : ℝ) * C ^ 2 := hsq
    _ ≤ (J : ℝ) ^ 2 * C ^ 2 := mul_le_mul_of_nonneg_right hJ2 (sq_nonneg C)
    _ = ((J : ℝ) * C) ^ 2 := by ring

/-- The complete non-primal correction is uniformly bounded on conductor windows. -/
theorem exists_norm_steinhausHilbertReflectedCorrection_le
    {J : ℕ} (hJ : 0 < J) (d b : Fin J → ℝ)
    (hd : ∀ j, 0 < d j) (hdhalf : ∀ j, d j < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ tau : ℝ,
      (∀ j, (N : ℝ) ≤ tau + b j ∧ tau + b j ≤ 2 * N) →
      ∀ ω : Omega, ‖steinhausHilbertReflectedCorrection d b tau N ω‖ ≤ C := by
  choose C hC hcomp using fun j => exists_norm_steinhausFullReflectedComplement_le (hd j) (hdhalf j)
  choose P hP hpole using fun j => exists_norm_reflectedShiftedPole_le_conductor
    (hd j) (hdhalf j)
  let M : ℝ := ∑ j, (C j + P j)
  have hM : 0 ≤ M := sum_nonneg (fun j _ => add_nonneg (hC j) (hP j))
  refine ⟨J * M, by positivity, fun N hN tau ht ω => ?_⟩
  apply norm_le_card_mul_of_coord_le hJ _ hM
  intro j
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  change ‖steinhausFullReflectedComplement (d j) (tau + b j) N ω -
    zetaChi (rightDisplacedLinePt (d j) (tau + b j)) *
      smoothAFEZetaShiftedPoleResidue (displacedLinePt (d j) (-(tau + b j))) N‖ ≤ M
  exact ((norm_sub_le _ _).trans (add_le_add
    (hcomp j N hNR _ (ht j).1 (ht j).2 ω)
    (hpole j N hNR _ (ht j).1))).trans
      (single_le_sum (f := fun k : Fin J => C k + P k)
        (fun k _ => add_nonneg (hC k) (hP k)) (mem_univ j))

/-- A fixed character prefix controls the complete vector correction uniformly over
conductor windows, including its unchanged pole term. -/
theorem exists_steinhausHilbertReflectedCorrection_character_tolerance
    {J : ℕ} (hJ : 0 < J) (d b : Fin J → ℝ)
    (hd : ∀ j, 0 < d j) (hdhalf : ∀ j, d j < 1 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, 1 ≤ N → ∀ tau : ℝ,
      (∀ j, (N : ℝ) ≤ tau + b j ∧ tau + b j ≤ 2 * N) →
      ∀ ω η : Omega, η ∈ steinhausCharacterCell B ω δ →
        ‖steinhausHilbertReflectedCorrection d b tau N η -
          steinhausHilbertReflectedCorrection d b tau N ω‖ < ε := by
  classical
  letI : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
  have hε' : 0 < ε / (J + 1 : ℝ) := div_pos hε (by positivity)
  choose B _hB δ hδ htol using fun j =>
    exists_fullReflectedComplement_character_tolerance (hd j) (hdhalf j) hε'
  obtain ⟨j₀, _, hmin⟩ := exists_min_image univ δ univ_nonempty
  refine ⟨univ.sup B, δ j₀, hδ j₀, fun N hN tau ht ω η hcell => ?_⟩
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hcoord (j : Fin J) :
      ‖(steinhausHilbertReflectedCorrection d b tau N η -
        steinhausHilbertReflectedCorrection d b tau N ω) j‖ ≤ ε / (J + 1 : ℝ) := by
    have h := htol j N hNR _ (ht j).1 (ht j).2 ω η
      (fun n hn => (hcell n (mem_Icc.mpr ⟨(mem_Icc.mp hn).1,
        (mem_Icc.mp hn).2.trans (le_sup (mem_univ j))⟩)).trans_le (hmin j (mem_univ j)))
    change ‖(steinhausFullReflectedComplement (d j) (tau + b j) N η - _) -
      (steinhausFullReflectedComplement (d j) (tau + b j) N ω - _)‖ ≤ _
    simpa only [sub_sub_sub_cancel_right] using h.le
  refine (norm_le_card_mul_of_coord_le hJ _ hε'.le hcoord).trans_lt ?_
  rw [← mul_div_assoc, div_lt_iff₀ (by positivity : (0 : ℝ) < J + 1)]
  nlinarith

end RHTower
