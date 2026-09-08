import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointWaveCoercivity

/-! Bounded forced wave solutions for every right-half-plane Laplace frequency. -/
open scoped ComplexConjugate
namespace RHTower.D4BMJointWave
noncomputable section
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The form equation retains its complete spatial part and the independent Laplace frequency. -/
def WaveFormSolution (J : V →L[ℂ] H) (w : ℂ) (F : H) (u : V) : Prop :=
  ∀ v : V, inner ℂ v u + (w^2-1)*inner ℂ (J v) (J u) = inner ℂ (J v) F

private theorem solution_iff (J : V →L[ℂ] H) (w : ℂ) (F : H) (u : V) :
    WaveFormSolution J w F u ↔ waveFormOperator J w u = J.adjoint F := by
  constructor
  · intro hu
    apply ext_inner_left ℂ
    intro v
    rw [waveFormOperator_inner,J.adjoint_inner_right]
    exact hu v
  · intro hu v
    rw [← waveFormOperator_inner,hu,J.adjoint_inner_right]

private theorem adjoint_contractive (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖) (F : H) :
    ‖J.adjoint F‖ ≤ ‖F‖ := by
  have hn : ‖J‖ ≤ 1 := J.opNorm_le_bound (by norm_num) (fun v => by simpa using hJ v)
  calc
    ‖J.adjoint F‖ ≤ ‖J.adjoint‖ * ‖F‖ := J.adjoint.le_opNorm F
    _ = ‖J‖ * ‖F‖ := by rw [LinearIsometryEquiv.norm_map]
    _ ≤ ‖F‖ := by nlinarith [norm_nonneg F]

/-- Existence with a quantitative bound uses the actual forcing vector, never an inverse premise. -/
theorem exists_bounded_waveFormSolution (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (w : ℂ) (hw : 0 < w.re) (F : H) :
    ∃ u : V, WaveFormSolution J w F u ∧
      ‖u‖ ≤ (waveCoercivity w)⁻¹ * ‖w‖ * ‖F‖ := by
  obtain ⟨S,hS,_,hb⟩ := rotatedWaveOperator_inverse J hJ w hw
  let u := S (conj w • J.adjoint F)
  have hw0 : conj w ≠ 0 := by simpa using (show w ≠ 0 from fun h => by simp [h] at hw)
  have he : waveFormOperator J w u = J.adjoint F := by
    apply smul_right_injective V hw0
    exact hS (conj w • J.adjoint F)
  refine ⟨u,(solution_iff J w F u).mpr he,?_⟩
  calc
    ‖u‖ ≤ (waveCoercivity w)⁻¹ * ‖conj w • J.adjoint F‖ := hb _
    _ = (waveCoercivity w)⁻¹ * ‖w‖ * ‖J.adjoint F‖ := by rw [norm_smul,Complex.norm_conj,mul_assoc]
    _ ≤ (waveCoercivity w)⁻¹ * ‖w‖ * ‖F‖ := mul_le_mul_of_nonneg_left
      (adjoint_contractive J hJ F) (mul_nonneg (inv_nonneg.mpr (waveCoercivity_pos w hw).le) (norm_nonneg w))

/-- The right-half-plane forced solution is unique in the completed energy domain. -/
theorem waveFormSolution_unique (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (w : ℂ) (hw : 0 < w.re) (F : H) {u v : V}
    (hu : WaveFormSolution J w F u) (hv : WaveFormSolution J w F v) : u = v := by
  obtain ⟨S,_,hS,_⟩ := rotatedWaveOperator_inverse J hJ w hw
  have he : rotatedWaveOperator J w u = rotatedWaveOperator J w v := by
    change conj w • waveFormOperator J w u = conj w • waveFormOperator J w v
    rw [(solution_iff J w F u).mp hu,(solution_iff J w F v).mp hv]
  have hh := congrArg S he
  simpa only [hS] using hh

/-- The scalar L² resolvent has the sharper decay needed for causal frequency control. -/
theorem waveFormSolution_mass_bound (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (w : ℂ) (hw : 0 < w.re) (F : H) {u : V} (hu : WaveFormSolution J w F u) :
    ‖J u‖ ≤ ‖F‖ / (w.re * ‖w‖) := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hmass : ‖J u‖^2 ≤ ‖u‖^2 := pow_le_pow_left₀ (norm_nonneg _) (hJ u) 2
  have he := rotatedWaveOperator_energy J w u
  have hr : rotatedWaveOperator J w u = conj w • J.adjoint F := by
    change conj w • waveFormOperator J w u = _
    rw [(solution_iff J w F u).mp hu]
  rw [hr,inner_smul_left,J.adjoint_inner_left,starRingEnd_self_apply] at he
  have hupper : (w * inner ℂ F (J u)).re ≤ ‖w‖ * ‖F‖ * ‖J u‖ := by
    calc
      _ ≤ ‖w * inner ℂ F (J u)‖ := Complex.re_le_norm _
      _ = ‖w‖ * ‖inner ℂ F (J u)‖ := norm_mul _ _
      _ ≤ ‖w‖ * (‖F‖ * ‖J u‖) := mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) hwn.le
      _ = _ := by ring
  rw [he,Complex.normSq_eq_norm_sq] at hupper
  have hb : w.re * ‖w‖^2 * ‖J u‖^2 ≤ ‖w‖ * ‖F‖ * ‖J u‖ := by
    nlinarith [mul_nonneg hw.le (sub_nonneg.mpr hmass)]
  rcases eq_or_lt_of_le (norm_nonneg (J u)) with hz | hp
  · rw [← hz]
    positivity
  · rw [le_div_iff₀ (mul_pos hw hwn)]
    have hh : (‖J u‖ * (w.re * ‖w‖)) * (‖w‖ * ‖J u‖) ≤ ‖F‖ * (‖w‖ * ‖J u‖) := by
      nlinarith [hb]
    exact le_of_mul_le_mul_right hh (mul_pos hwn hp)

end
end RHTower.D4BMJointWave
