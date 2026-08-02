import GaloisForLFunctions.HTGeometry.IntegerTorusHomomorphism
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Injective torus homomorphisms are bi-Lipschitz

An integer matrix defines a homomorphism of phase tori and, on the universal cover, a linear map.
The homomorphism is Lipschitz with the entrywise size of the matrix.  If it is injective then the
linear lift is injective too, so it is antilipschitz on the cover; near the identity the torus norm
agrees with the norm of the lift, and away from the identity compactness gives a uniform positive
lower bound.  Hence an injective torus homomorphism distorts distances by a bounded factor in both
directions.
-/

open Filter Metric Set Topology
open scoped NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d k : Type*} [Fintype d] [Fintype k] [DecidableEq k]

theorem norm_circle_le_half (x : UnitAddCircle) : ‖x‖ ≤ 1 / 2 := by
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [UnitAddCircle.norm_eq]
  exact abs_sub_round u

omit [DecidableEq k] in
theorem norm_torus_le_half (z : UnitAddTorus k) : ‖z‖ ≤ 1 / 2 :=
  (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i => norm_circle_le_half (z i)

/-- Below half a period the circle norm is the absolute value of the representative. -/
theorem norm_coe_eq_abs {v : ℝ} (hv : |v| ≤ 1 / 2) :
    ‖((v : ℝ) : UnitAddCircle)‖ = |v| := by
  rw [UnitAddCircle.norm_eq]
  have hle : |v - (round v : ℝ)| ≤ |v| := by
    simpa using round_le v 0
  by_cases hr : round v = 0
  · rw [hr]
    simp
  · have hone : (1 : ℝ) ≤ |(round v : ℝ)| := by
      have : 1 ≤ |round v| := Int.one_le_abs (by exact_mod_cast hr)
      exact_mod_cast this
    have hge : 1 / 2 ≤ |v - (round v : ℝ)| := by
      have htri : |(round v : ℝ)| ≤ |v| + |v - (round v : ℝ)| := by
        have := abs_sub_abs_le_abs_sub (round v : ℝ) v
        have h2 : |(round v : ℝ) - v| = |v - (round v : ℝ)| := abs_sub_comm _ _
        linarith [abs_nonneg v, this, h2]
      linarith
    linarith

/-- The linear lift of an integer matrix. -/
def integerLinearMap (M : d → k → ℤ) : (k → ℝ) →ₗ[ℝ] (d → ℝ) where
  toFun w := fun i => ∑ j, (M i j : ℝ) * w j
  map_add' w₁ w₂ := by
    funext i
    show ∑ j, (M i j : ℝ) * (w₁ j + w₂ j) = (∑ j, (M i j : ℝ) * w₁ j) + ∑ j, (M i j : ℝ) * w₂ j
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  map_smul' c w := by
    funext i
    show ∑ j, (M i j : ℝ) * (c * w j) = c * ∑ j, (M i j : ℝ) * w j
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

omit [Fintype d] [DecidableEq k] in
@[simp] theorem integerLinearMap_apply (M : d → k → ℤ) (w : k → ℝ) (i : d) :
    integerLinearMap M w i = ∑ j, (M i j : ℝ) * w j := rfl

omit [Fintype d] [DecidableEq k] in
/-- The torus homomorphism is the reduction of the linear lift. -/
theorem torusIntegerHom_coe (M : d → k → ℤ) (w : k → ℝ) :
    torusIntegerHom M (fun j => ((w j : ℝ) : UnitAddCircle))
      = fun i => (((integerLinearMap M w i : ℝ)) : UnitAddCircle) := by
  funext i
  show ∑ j, M i j • ((w j : ℝ) : UnitAddCircle) = _
  rw [← coe_sum_mul]
  rfl

omit [DecidableEq k] in
/-- Every torus point lifts to a real vector of the same size. -/
theorem exists_lift_norm_eq (z : UnitAddTorus k) :
    ∃ w : k → ℝ, (fun j => ((w j : ℝ) : UnitAddCircle)) = z ∧ ‖w‖ = ‖z‖ ∧
      ∀ j, |w j| ≤ 1 / 2 := by
  classical
  have hchoice : ∀ j : k, ∃ v : ℝ, ((v : ℝ) : UnitAddCircle) = z j ∧ |v| = ‖z j‖ ∧ |v| ≤ 1 / 2 := by
    intro j
    obtain ⟨u, hu⟩ := QuotientAddGroup.mk_surjective (z j)
    refine ⟨u - round u, ?_, ?_, ?_⟩
    · rw [show ((u - (round u : ℝ) : ℝ) : UnitAddCircle)
          = ((u : ℝ) : UnitAddCircle) - (((round u : ℤ) : ℝ) : UnitAddCircle) from
        map_sub (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) _ _]
      rw [show ((((round u : ℤ) : ℝ)) : UnitAddCircle) = 0 from
        (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨round u, by simp⟩, sub_zero, hu]
    · rw [← hu, UnitAddCircle.norm_eq]
    · exact abs_sub_round u
  choose w hw₁ hw₂ hw₃ using hchoice
  refine ⟨w, funext hw₁, ?_, hw₃⟩
  refine le_antisymm ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr fun j => ?_
    rw [Real.norm_eq_abs, hw₂ j]
    exact norm_le_pi_norm z j
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr fun j => ?_
    rw [← hw₂ j, ← Real.norm_eq_abs]
    exact norm_le_pi_norm w j

/-- The entrywise size of an integer matrix. -/
def matrixAbsSum (M : d → k → ℤ) : ℝ := ∑ i, ∑ j, |(M i j : ℝ)|

omit [DecidableEq k] in
theorem matrixAbsSum_nonneg (M : d → k → ℤ) : 0 ≤ matrixAbsSum M := by
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _

omit [DecidableEq k] in
/-- **Torus homomorphisms are Lipschitz.** -/
theorem lipschitzWith_torusIntegerHom (M : d → k → ℤ) :
    LipschitzWith (Real.toNNReal (matrixAbsSum M)) (torusIntegerHom M) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ (matrixAbsSum_nonneg M)]
  have hsub : torusIntegerHom M x - torusIntegerHom M y = torusIntegerHom M (x - y) := by
    have h := torusIntegerHom_add M (x - y) y
    rw [sub_add_cancel] at h
    rw [h]
    abel
  rw [dist_eq_norm, dist_eq_norm, hsub]
  refine (pi_norm_le_iff_of_nonneg
    (mul_nonneg (matrixAbsSum_nonneg M) (norm_nonneg _))).mpr fun i => ?_
  show ‖∑ j, M i j • (x - y) j‖ ≤ _
  refine le_trans (norm_sum_le _ _) ?_
  have hrow : ∀ j : k, ‖M i j • (x - y) j‖ ≤ |(M i j : ℝ)| * ‖x - y‖ := by
    intro j
    refine le_trans (norm_zsmul_le (M i j) ((x - y) j)) ?_
    have hcast : ‖(M i j : ℤ)‖ = |(M i j : ℝ)| := by
      rw [Int.norm_eq_abs]
    rw [hcast]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (x - y) j) (abs_nonneg _)
  refine le_trans (Finset.sum_le_sum fun j _ => hrow j) ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine Finset.single_le_sum (f := fun i => ∑ j, |(M i j : ℝ)|) ?_ (Finset.mem_univ i)
  intro i' _
  exact Finset.sum_nonneg fun j _ => abs_nonneg _

omit [Fintype d] [DecidableEq k] in
/-- An injective torus homomorphism has injective linear lift. -/
theorem injective_integerLinearMap_of_injective {M : d → k → ℤ}
    (hinj : Function.Injective (torusIntegerHom M)) :
    Function.Injective (integerLinearMap M) := by
  rw [← LinearMap.ker_eq_bot] at *
  refine LinearMap.ker_eq_bot'.mpr fun v hv => ?_
  by_contra hne
  -- some coordinate of `v` is nonzero, so a small multiple of `v` is a nonzero torus point
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hne
  set t : ℝ := 1 / (4 * ‖v‖) with ht
  have htpos : 0 < t := by positivity
  have hsmall : ∀ j, |t * v j| ≤ 1 / 2 := by
    intro j
    rw [abs_mul, abs_of_pos htpos, ht]
    have hbound : |v j| ≤ ‖v‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_le_pi_norm v j
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    nlinarith [hbound, hvpos]
  set z : UnitAddTorus k := fun j => ((t * v j : ℝ) : UnitAddCircle) with hz
  have hzero : torusIntegerHom M z = 0 := by
    have hcoe := torusIntegerHom_coe M (fun j => t * v j)
    rw [hz, hcoe]
    funext i
    have hlin : integerLinearMap M (fun j => t * v j) i = t * (integerLinearMap M v i) := by
      simp only [integerLinearMap_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hlin]
    have hvi : integerLinearMap M v i = 0 := by
      rw [hv]
      rfl
    rw [hvi, mul_zero]
    rfl
  have hzne : z ≠ 0 := by
    intro hcon
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
    have hzj : ((t * v j : ℝ) : UnitAddCircle) = 0 := congrFun hcon j
    have hnormzero : ‖((t * v j : ℝ) : UnitAddCircle)‖ = 0 := by rw [hzj, norm_zero]
    rw [norm_coe_eq_abs (hsmall j)] at hnormzero
    have : t * v j = 0 := by
      exact abs_eq_zero.mp hnormzero
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (ne_of_gt htpos)
    · exact hj (by simpa using h)
  have hzeq : torusIntegerHom M z = torusIntegerHom M 0 := by
    rw [hzero, torusIntegerHom_zero]
  exact hzne (hinj hzeq)

/-- The torus norm of a small real vector is the norm of the vector. -/
theorem norm_coe_torus_eq (v : d → ℝ) (hv : ∀ i, |v i| ≤ 1 / 2) :
    ‖(fun i => ((v i : ℝ) : UnitAddCircle))‖ = ‖v‖ := by
  refine le_antisymm ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr fun i => ?_
    rw [norm_coe_eq_abs (hv i), ← Real.norm_eq_abs]
    exact norm_le_pi_norm v i
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
    rw [Real.norm_eq_abs, ← norm_coe_eq_abs (hv i)]
    exact norm_le_pi_norm (fun i => ((v i : ℝ) : UnitAddCircle)) i

omit [DecidableEq k] in
/-- **Injective torus homomorphisms are antilipschitz.** -/
theorem exists_antilipschitzWith_torusIntegerHom (M : d → k → ℤ)
    (hinj : Function.Injective (torusIntegerHom M)) :
    ∃ K : ℝ≥0, 0 < (K : ℝ) ∧ AntilipschitzWith K (torusIntegerHom M) := by
  classical
  obtain ⟨σ, hσpos, hσ⟩ := (integerLinearMap M).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.mpr (injective_integerLinearMap_of_injective hinj))
  set A : ℝ := matrixAbsSum M with hA
  have hAnn : 0 ≤ A := matrixAbsSum_nonneg M
  set δ : ℝ := 1 / (2 * (A + 1)) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    positivity
  -- the near regime: the torus norm of the image is the norm of the linear image
  have hnear : ∀ z : UnitAddTorus k, ‖z‖ ≤ δ → ‖z‖ ≤ (σ : ℝ) * ‖torusIntegerHom M z‖ := by
    intro z hz
    obtain ⟨w, hwz, hwnorm, hwhalf⟩ := exists_lift_norm_eq z
    have hrow : ∀ i : d, |integerLinearMap M w i| ≤ A * ‖w‖ := by
      intro i
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hterm : ∀ j : k, |(M i j : ℝ) * w j| ≤ |(M i j : ℝ)| * ‖w‖ := by
        intro j
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [← Real.norm_eq_abs]
        exact norm_le_pi_norm w j
      refine le_trans (Finset.sum_le_sum fun j _ => hterm j) ?_
      rw [← Finset.sum_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg w)
      refine Finset.single_le_sum (f := fun i => ∑ j, |(M i j : ℝ)|) ?_ (Finset.mem_univ i)
      intro i' _
      exact Finset.sum_nonneg fun j _ => abs_nonneg _
    have hsmall : ∀ i : d, |integerLinearMap M w i| ≤ 1 / 2 := by
      intro i
      refine le_trans (hrow i) ?_
      rw [hwnorm]
      have hzδ : ‖z‖ ≤ δ := hz
      calc A * ‖z‖ ≤ A * δ := mul_le_mul_of_nonneg_left hzδ hAnn
        _ ≤ 1 / 2 := by
            rw [hδ, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith [hAnn]
    have himg : torusIntegerHom M z = fun i => ((integerLinearMap M w i : ℝ) : UnitAddCircle) := by
      rw [← hwz]
      exact torusIntegerHom_coe M w
    have hnormimg : ‖torusIntegerHom M z‖ = ‖integerLinearMap M w‖ := by
      rw [himg]
      exact norm_coe_torus_eq (integerLinearMap M w) hsmall
    have hlin : ‖w‖ ≤ (σ : ℝ) * ‖integerLinearMap M w‖ := by
      have := hσ.le_mul_dist w 0
      simpa using this
    rw [← hwnorm, hnormimg]
    exact hlin
  -- the far regime: compactness gives a uniform positive lower bound
  have hfar : ∃ c : ℝ, 0 < c ∧ ∀ z : UnitAddTorus k, δ ≤ ‖z‖ → c ≤ ‖torusIntegerHom M z‖ := by
    by_cases hS : (({z : UnitAddTorus k | δ ≤ ‖z‖}) : Set (UnitAddTorus k)).Nonempty
    · have hclosed : IsClosed {z : UnitAddTorus k | δ ≤ ‖z‖} :=
        isClosed_le continuous_const continuous_norm
      have hcompact : IsCompact {z : UnitAddTorus k | δ ≤ ‖z‖} := hclosed.isCompact
      obtain ⟨z₀, hz₀mem, hz₀min⟩ := hcompact.exists_isMinOn hS
        ((continuous_norm.comp (continuous_torusIntegerHom M)).continuousOn)
      have hz₀ne : z₀ ≠ 0 := by
        intro hcon
        rw [hcon] at hz₀mem
        simp only [Set.mem_setOf_eq, norm_zero] at hz₀mem
        exact absurd hz₀mem (not_le.mpr hδpos)
      have hpos : 0 < ‖torusIntegerHom M z₀‖ := by
        rw [norm_pos_iff]
        intro hcon
        refine hz₀ne (hinj ?_)
        rw [hcon, torusIntegerHom_zero]
      exact ⟨‖torusIntegerHom M z₀‖, hpos, fun z hz => hz₀min hz⟩
    · exact ⟨1, one_pos, fun z hz => absurd ⟨z, hz⟩ hS⟩
  obtain ⟨c, hcpos, hc⟩ := hfar
  have hσR : (0 : ℝ) < (σ : ℝ) := NNReal.coe_pos.mpr hσpos
  have hmaxnn : (0 : ℝ) ≤ max (σ : ℝ) (1 / (2 * c)) := le_trans hσR.le (le_max_left _ _)
  refine ⟨Real.toNNReal (max (σ : ℝ) (1 / (2 * c))), ?_, ?_⟩
  · rw [Real.coe_toNNReal _ hmaxnn]
    exact lt_of_lt_of_le hσR (le_max_left _ _)
  · refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
    rw [Real.coe_toNNReal _ hmaxnn]
    have hsub : torusIntegerHom M x - torusIntegerHom M y = torusIntegerHom M (x - y) := by
      have h := torusIntegerHom_add M (x - y) y
      rw [sub_add_cancel] at h
      rw [h]
      abel
    rw [dist_eq_norm, dist_eq_norm, hsub]
    set z := x - y
    by_cases hz : ‖z‖ ≤ δ
    · refine le_trans (hnear z hz) ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    · have hzδ : δ ≤ ‖z‖ := le_of_lt (not_le.mp hz)
      have hcz := hc z hzδ
      have hhalf := norm_torus_le_half z
      have hstep : ‖z‖ ≤ (1 / (2 * c)) * ‖torusIntegerHom M z‖ := by
        have h2c : 0 < 2 * c := by linarith
        rw [one_div, inv_mul_eq_div, le_div_iff₀ h2c]
        nlinarith [hhalf, hcz, hcpos, norm_nonneg z]
      exact le_trans hstep (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

end

end GaloisForLFunctions.HTGeometry
