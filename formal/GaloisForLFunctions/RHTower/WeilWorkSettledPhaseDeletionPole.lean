import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseDeletionRatio
import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseForwardRegularPart

/-!
# The odd forward series has a nonzero radial pole

Combining the full source regular part with its odd-to-full ratio gives
a nonzero simple-pole term and a bounded remainder along the real axis.
This does not assert analytic continuation of the odd series.
-/

open Complex Filter Topology Set
noncomputable section
namespace RHTower.WeilWorkSettledPhase

/-- The leading coefficient of the original source is nonzero. -/
theorem sourceCompletion_one_ne_zero {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    sourceCompletion hW 1 ≠ 0 := by
  unfold sourceCompletion
  exact mul_ne_zero (IntegerMassRigidity.bigG_ne_zero lam (by norm_num)) (Complex.exp_ne_zero _)

/-- The odd forward series has a nonzero radial simple-pole term and a
bounded remainder, without asserting meromorphic continuation. -/
theorem exists_odd_source_radial_pole {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ r K : ℝ, 0<r ∧ 0≤K ∧ (r : ℂ)*sourceCompletion hW 1 ≠ 0 ∧
      ∀ᶠ σ : ℝ in 𝓝[>] 1,
        ‖LSeries (oddPart (sourceCoeff lam)) (σ : ℂ) -
          (r : ℂ)*sourceCompletion hW 1/((σ : ℂ)-1)‖ ≤ K := by
  obtain ⟨r,K,eta,hr,hK,heta,ht,herr⟩ := exists_odd_source_ratio_limit hW
  obtain ⟨R,hRd,hReq,_⟩ := exists_forward_regularPart hW
  have hRc : ContinuousAt R (1 : ℂ) :=
    (hRd.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (1/2 : ℝ)<(1 : ℂ).re))).continuousAt
  have hreal : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝 1) :=
    (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
  obtain ⟨M,hM⟩ := (hRc.tendsto.comp hreal).norm.isBoundedUnder_le
  obtain ⟨Q,hQ⟩ := ht.norm.isBoundedUnder_le
  refine ⟨r,|Q| * |M|+K*‖sourceCompletion hW 1‖,hr,by positivity,
    mul_ne_zero (by exact_mod_cast hr.ne') (sourceCompletion_one_ne_zero hW),?_⟩
  have hu : ∀ᶠ σ : ℝ in 𝓝[>] 1, σ<1+eta :=
    (eventually_lt_nhds (by linarith : (1 : ℝ)<1+eta)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hu,hM,hQ] with σ hσ hu hM hQ
  change 1<σ at hσ
  let F : ℂ := LSeries (sourceCoeff lam) (σ : ℂ)
  let O : ℂ := LSeries (oddPart (sourceCoeff lam)) (σ : ℂ)
  let q : ℂ := O/F
  let B : ℂ := sourceCompletion hW 1
  have hFne : F≠0 := by
    dsimp [F]
    rw [(sourceCoeff_LSeries hW hσ).2,IntegerMassRigidity.zetaOf]
    exact Complex.exp_ne_zero _
  have hFR : F=R (σ : ℂ)+B/((σ : ℂ)-1) := by
    rw [hReq (σ : ℂ) hσ]
    dsimp [F,B]
    ring
  have hO : O=q*F := by dsimp [q]; rw [div_mul_cancel₀ _ hFne]
  have hq : ‖q‖≤|Q| := hQ.trans (le_abs_self Q)
  have hR : ‖R (σ : ℂ)‖≤|M| := hM.trans (le_abs_self M)
  have he : ‖q-(r : ℂ)‖≤K*(σ-1) := herr σ hσ hu
  have hn : ‖(σ : ℂ)-1‖ = σ-1 := by
    rw [show (σ : ℂ)-1=((σ-1 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr hσ)]
  change ‖O-(r : ℂ)*B/((σ : ℂ)-1)‖≤_
  have hid : O-(r : ℂ)*B/((σ : ℂ)-1) =
      q*R (σ : ℂ)+(q-(r : ℂ))*B/((σ : ℂ)-1) := by
    rw [hO,hFR]
    ring
  rw [hid]
  calc
    _ ≤ ‖q*R (σ : ℂ)‖+‖(q-(r : ℂ))*B/((σ : ℂ)-1)‖ := norm_add_le _ _
    _ = ‖q‖*‖R (σ : ℂ)‖+‖q-(r : ℂ)‖*‖B‖/(σ-1) := by simp only [norm_mul,norm_div,hn]
    _ ≤ |Q| * |M|+(K*(σ-1))*‖B‖/(σ-1) := by gcongr
    _ = _ := by
      dsimp [B]
      field_simp [(sub_pos.mpr hσ).ne']

end RHTower.WeilWorkSettledPhase
