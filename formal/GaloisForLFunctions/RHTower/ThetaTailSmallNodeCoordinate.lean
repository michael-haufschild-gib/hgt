import GaloisForLFunctions.RHTower.ThetaTailNormalizedSchurHessian
import GaloisForLFunctions.RHTower.ThetaTailConfluentCoordinatePort

/-! Uniform finite-node coordinate positivity at the actual center Schur kernel. -/

noncomputable section
open Filter Topology Set
namespace RHTower.ThetaJoint
open ThetaConfluent ThetaCoordinate GaloisForLFunctions.HTGeometry

private theorem diagonal_hasDerivAt {F A B : ℝ → ℝ → ℝ}
    (hA : Continuous fun p : ℝ × ℝ => A p.1 p.2)
    (hB : Continuous fun p : ℝ × ℝ => B p.1 p.2)
    (dA : ∀ x y, HasDerivAt (fun x => F x y) (A x y) x)
    (dB : ∀ x y, HasDerivAt (F x) (B x y) y) (t : ℝ) :
    HasDerivAt (fun t => F t t) (A t t+B t t) t := by
  have h : HasFDerivAt (Function.uncurry F)
      ((toCLM (A t t)).coprod (toCLM (B t t))) (t,t) :=
    (hasStrictFDerivAt_uncurry_coprod
      (u := (t,t)) (f := F) (f₁ := fun x y => toCLM (A x y)) (f₂ := fun x y => toCLM (B x y))
      (Eventually.of_forall fun p => (dA p.1 p.2).hasFDerivAt)
      (Eventually.of_forall fun p => (dB p.1 p.2).hasFDerivAt)
      (continuous_toCLM.continuousAt.comp hA.continuousAt)
      (continuous_toCLM.continuousAt.comp hB.continuousAt)).hasFDerivAt
  simpa only [Function.comp_def, Function.uncurry_apply_pair, ContinuousLinearMap.coprod_apply,
    toCLM_apply, one_mul] using
    h.comp_hasDerivAt (f := fun t : ℝ => (t,t)) t
      ((hasDerivAt_id t).prodMk (hasDerivAt_id t))

private theorem triangular_decrease {F G A B : ℝ → ℝ → ℝ}
    (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2)
    (hG : Continuous fun p : ℝ × ℝ => G p.1 p.2)
    (hA : Continuous fun p : ℝ × ℝ => A p.1 p.2)
    (hB : Continuous fun p : ℝ × ℝ => B p.1 p.2)
    (dF : ∀ x y, HasDerivAt (F x) (G x y) y)
    (dA : ∀ x y, HasDerivAt (fun x => G x y) (A x y) x)
    (dB : ∀ x y, HasDerivAt (G x) (B x y) y)
    (h0 : G 0 0 = 0)
    (hn : ∀ᶠ p : ℝ × ℝ in 𝓝 (0,0), B p.1 p.2 < 0 ∧ A p.1 p.2+B p.1 p.2 < 0) :
    ∃ e > 0, ∀ x y : ℝ, 0 < x → x < y → y < e → F x y < F x x := by
  obtain ⟨e,he,hs⟩ := Metric.eventually_nhds_iff.mp hn
  have hsign (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxe : x < e) (hye : y < e) :
      B x y < 0 ∧ A x y+B x y < 0 := by
    apply hs (y := (x,y))
    simpa only [Prod.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg hx, abs_of_nonneg hy,
      max_lt_iff] using And.intro hxe hye
  have hdiag : StrictAntiOn (fun t => G t t) (Icc 0 e) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 e)
    · exact (hG.comp (continuous_id.prodMk continuous_id)).continuousOn
    · intro t ht
      have ht' : 0 < t ∧ t < e := by simpa only [interior_Icc, mem_Ioo] using ht
      rw [(diagonal_hasDerivAt hA hB dA dB t).deriv]
      exact (hsign t t ht'.1.le ht'.1.le ht'.2 ht'.2).2
  have hnegative (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) (hye : y < e) : G x y < 0 := by
    have hxe := lt_of_le_of_lt hxy hye
    have hxx : G x x < 0 := by
      simpa only [h0] using hdiag ⟨le_rfl,he.le⟩ ⟨hx.le,hxe.le⟩ hx
    have hv : StrictAntiOn (G x) (Icc x e) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc x e)
      · exact (hG.comp (continuous_const.prodMk continuous_id)).continuousOn
      · intro t ht
        have ht' : x < t ∧ t < e := by simpa only [interior_Icc, mem_Ioo] using ht
        rw [(dB x t).deriv]
        exact (hsign x t hx.le (lt_trans hx ht'.1).le hxe ht'.2).1
    exact lt_of_le_of_lt (hv.antitoneOn ⟨le_rfl,hxe.le⟩ ⟨hxy,hye.le⟩ hxy) hxx
  refine ⟨e,he,?_⟩
  intro x y hx hxy hye
  have hv : StrictAntiOn (F x) (Icc x e) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc x e)
    · exact (hF.comp (continuous_const.prodMk continuous_id)).continuousOn
    · intro t ht
      have ht' : x < t ∧ t < e := by simpa only [interior_Icc, mem_Ioo] using ht
      rw [(dF x t).deriv]
      exact hnegative x t hx ht'.1.le ht'.2
  exact hv ⟨le_rfl,(hxy.trans hye).le⟩ ⟨hxy.le,hye.le⟩ hxy

theorem exists_normalizedSchur_triangular_decrease :
    ∃ e > 0, ∀ x y : ℝ, 0 < x → x < y → y < e →
      normalizedSchur x y < normalizedSchur x x :=
  triangular_decrease normalizedSchur_continuous normalizedSchurRight_continuous
    normalizedSchurRightLeft_continuous normalizedSchurRightTwice_continuous
    normalizedSchur_hasDerivAt_right normalizedSchurRight_hasDerivAt_left
    normalizedSchurRight_hasDerivAt_right normalizedSchurRight_origin
    eventually_normalizedSchurHessian_neg

local notation "H" => thetaTailFirstMomentKernel
local notation "J" => thetaTailFirstMomentKernel 0 0
local notation "k" => thetaCuspFullSource
local notation "D" => ThetaSturm.determinant

theorem centerSchur_diagonal (z : ℝ) : centerSchur z z = D 0 z/J := by
  unfold centerSchur ThetaSturm.determinant
  field_simp [centerMass_pos.ne']

theorem normalizedSchur_diag_pos {z : ℝ} (hz : 0 < z) : 0 < normalizedSchur z z := by
  unfold normalizedSchur
  rw [dividedSchur_eq hz.ne' hz.ne', centerSchur_diagonal]
  exact div_pos
    (div_pos (div_pos (ThetaTailTwoPoint.kernel_two_point_det_pos hz.ne) centerMass_pos)
      (mul_pos hz hz))
    (mul_pos (thetaCuspFullSource_pos_all z) (thetaCuspFullSource_pos_all z))

/-- Exact conversion of the smooth Schur comparison into the literal coordinate residual. -/
theorem coordinateResidual_eq_normalizedSchur {z y : ℝ} (hz : 0 < z) (hy : 0 < y) :
    coordinateResidual z y = y*k y*(1-normalizedSchur z y/normalizedSchur z z) := by
  have hD : D 0 z ≠ 0 := (ThetaTailTwoPoint.kernel_two_point_det_pos hz.ne).ne'
  unfold normalizedSchur
  rw [dividedSchur_eq hz.ne' hy.ne', dividedSchur_eq hz.ne' hz.ne', centerSchur_diagonal]
  unfold coordinateResidual centerSchur
  field_simp [hz.ne', hy.ne', (thetaCuspFullSource_pos_all z).ne',
    (thetaCuspFullSource_pos_all y).ne', centerMass_pos.ne', hD]

/-- One neighborhood works for every pair of ordered positive nodes. -/
theorem exists_coordinateResidual_pos_triangle :
    ∃ e > 0, ∀ z y : ℝ, 0 < z → z < y → y < e → 0 < coordinateResidual z y := by
  obtain ⟨e,he,h⟩ := exists_normalizedSchur_triangular_decrease
  refine ⟨e,he,?_⟩
  intro z y hz hzy hye
  have hy := hz.trans hzy
  rw [coordinateResidual_eq_normalizedSchur hz hy]
  apply mul_pos (mul_pos hy (thetaCuspFullSource_pos_all y))
  apply sub_pos.mpr
  exact (div_lt_one (normalizedSchur_diag_pos hz)).mpr (h z y hz hzy hye)

end RHTower.ThetaJoint
