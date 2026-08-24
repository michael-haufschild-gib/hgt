import GaloisForLFunctions.HTGeometry.EisensteinSeriesDiskChazy
import GaloisForLFunctions.Bottcher.ArcContinuation

/-!
# Natural boundary of the disk Eisenstein series `E₂`

The quasimodular transformation law makes `E₂` diverge at every rational cusp.  Their images under
`q = exp(2πiτ)` are dense on the unit circle, so the disk `q`-expansion cannot continue across any
boundary point.
-/

open UpperHalfPlane hiding I
open Real Complex Filter Topology Set Metric
open ModularForm EisensteinSeries MatrixGroups SlashInvariantForm
open scoped MatrixGroups Manifold

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local notation "E₂" => EisensteinSeries.E2

/-- Exact quasimodular transformation formula for `E₂`. -/
theorem e2_transform (γ : SL(2, ℤ)) (τ : ℍ) :
    E₂ (γ • τ) =
      UpperHalfPlane.denom γ τ ^ 2 * E₂ τ -
        (6 : ℂ) * I * (γ 1 0 : ℂ) / Real.pi * UpperHalfPlane.denom γ τ := by
  have h := congrFun (EisensteinSeries.E2_slash_action γ) τ
  rw [ModularForm.SL_slash_apply] at h
  change E₂ (γ • τ) * (UpperHalfPlane.denom γ τ) ^ (-(2 : ℤ)) =
    E₂ τ - (1 / (2 * riemannZeta 2)) *
      (2 * Real.pi * I * (γ 1 0 : ℂ) / UpperHalfPlane.denom γ τ) at h
  rw [zpow_neg] at h
  have hden : UpperHalfPlane.denom γ τ ≠ 0 := UpperHalfPlane.denom_ne_zero γ τ
  rw [riemannZeta_two] at h
  field_simp [hden] at h ⊢
  linear_combination h

/-- Standard vertical sequence tending to the cusp at infinity. -/
def cuspVertical (n : ℕ) : ℍ :=
  ⟨((n + 1 : ℕ) : ℂ) * I, by simp; positivity⟩

@[simp] theorem cuspVertical_coe (n : ℕ) :
    (cuspVertical n : ℂ) = ((n + 1 : ℕ) : ℂ) * I := rfl

@[simp] theorem cuspVertical_im (n : ℕ) :
    (cuspVertical n).im = (n + 1 : ℕ) := by simp [cuspVertical]

theorem cuspVertical_tendsto_atImInfty :
    Tendsto cuspVertical atTop atImInfty := by
  rw [atImInfty, Filter.tendsto_comap_iff]
  have h : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    apply Filter.tendsto_atTop_mono' atTop
      (f₁ := fun n : ℕ => (n : ℝ)) (f₂ := fun n : ℕ => ((n + 1 : ℕ) : ℝ))
    · exact Filter.Eventually.of_forall fun n => by norm_num
    · exact tendsto_natCast_atTop_atTop
  rw [show UpperHalfPlane.im ∘ cuspVertical =
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) by
    funext n
    simp]
  exact h

theorem e2_cuspVertical_tendsto_one :
    Tendsto (fun n => E₂ (cuspVertical n)) atTop (nhds 1) :=
  Bottcher.eisensteinSeries_E2_tendsto_one_atImInfty.comp
    cuspVertical_tendsto_atImInfty

theorem cuspVertical_inv_tendsto_zero :
    Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℂ))⁻¹) atTop (nhds 0) := by
  have hy : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    apply Filter.tendsto_atTop_mono' atTop
      (f₁ := fun n : ℕ => (n : ℝ)) (f₂ := fun n : ℕ => ((n + 1 : ℕ) : ℝ))
    · exact Filter.Eventually.of_forall fun n => by norm_num
    · exact tendsto_natCast_atTop_atTop
  have h := hy.inv_tendsto_atTop.ofReal
  simpa only [Pi.inv_apply, ofReal_inv, ofReal_natCast, ofReal_zero] using h

theorem denom_cuspVertical_scaled_tendsto (γ : SL(2, ℤ)) :
    Tendsto (fun n : ℕ => UpperHalfPlane.denom γ (cuspVertical n) /
      ((n + 1 : ℕ) : ℂ)) atTop (nhds ((γ 1 0 : ℂ) * I)) := by
  have hc : Tendsto (fun _ : ℕ => (γ 1 0 : ℂ) * I) atTop
      (nhds ((γ 1 0 : ℂ) * I)) := tendsto_const_nhds
  have hd := cuspVertical_inv_tendsto_zero.const_mul (γ 1 1 : ℂ)
  have ht := hc.add hd
  convert ht using 1
  · funext n
    unfold UpperHalfPlane.denom
    simp only [cuspVertical_coe]
    have h10 :
        (((γ : GL (Fin 2) ℝ) 1 0 : ℝ) : ℂ) = (γ 1 0 : ℂ) := rfl
    have h11 :
        (((γ : GL (Fin 2) ℝ) 1 1 : ℝ) : ℂ) = (γ 1 1 : ℂ) := rfl
    rw [h10, h11]
    have hy : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    field_simp [hy]
  · ring

/-- Quadratically normalized rational-cusp values tend to the nonzero leading coefficient. -/
theorem e2_transformed_scaled_tendsto (γ : SL(2, ℤ)) :
    Tendsto (fun n : ℕ => E₂ (γ • cuspVertical n) /
      (((n + 1 : ℕ) : ℂ) ^ 2)) atTop
      (nhds (-((γ 1 0 : ℂ) ^ 2))) := by
  have hs := denom_cuspVertical_scaled_tendsto γ
  have hmain := (hs.pow 2).mul e2_cuspVertical_tendsto_one
  have hsmall := hs.mul cuspVertical_inv_tendsto_zero
  have hanom := hsmall.const_mul
    ((6 : ℂ) * I * (γ 1 0 : ℂ) / Real.pi)
  have ht := hmain.sub hanom
  convert ht using 1
  · funext n
    rw [e2_transform]
    have hy : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    field_simp [hy]
  · rw [mul_pow, Complex.I_sq]
    ring

/-- `E₂(γ(i(n+1)))` diverges whenever `γ` represents a finite rational cusp. -/
theorem e2_transformed_norm_tendsto_atTop (γ : SL(2, ℤ))
    (hc : γ 1 0 ≠ 0) :
    Tendsto (fun n : ℕ => ‖E₂ (γ • cuspVertical n)‖) atTop atTop := by
  let L : ℝ := ‖-((γ 1 0 : ℂ) ^ 2)‖
  have hcC : (γ 1 0 : ℂ) ≠ 0 := by exact_mod_cast hc
  have hL : 0 < L := norm_pos_iff.mpr (neg_ne_zero.mpr (pow_ne_zero 2 hcC))
  have hscaled := (e2_transformed_scaled_tendsto γ).norm
  have hev : ∀ᶠ n : ℕ in atTop,
      L / 2 < ‖E₂ (γ • cuspVertical n) / (((n + 1 : ℕ) : ℂ) ^ 2)‖ := by
    apply hscaled.eventually_const_lt
    dsimp only [L]
    linarith
  have hy : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    apply Filter.tendsto_atTop_mono' atTop
      (f₁ := fun n : ℕ => (n : ℝ)) (f₂ := fun n : ℕ => ((n + 1 : ℕ) : ℝ))
    · exact Filter.Eventually.of_forall fun n => by norm_num
    · exact tendsto_natCast_atTop_atTop
  have hy2 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2) atTop atTop := by
    apply Filter.tendsto_atTop_mono' atTop
      (f₁ := fun n : ℕ => ((n + 1 : ℕ) : ℝ))
      (f₂ := fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2)
    · exact Filter.Eventually.of_forall fun n => by
        have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by norm_num
        nlinarith
    · exact hy
  apply Filter.tendsto_atTop_mono' atTop
    (f₁ := fun n : ℕ => (L / 2) * ((n + 1 : ℕ) : ℝ) ^ 2)
  · filter_upwards [hev] with n hn
    have hyC : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have heq : ‖E₂ (γ • cuspVertical n)‖ =
        ‖E₂ (γ • cuspVertical n) / (((n + 1 : ℕ) : ℂ) ^ 2)‖ *
          ((n + 1 : ℕ) : ℝ) ^ 2 := by
      rw [norm_div, norm_pow, Complex.norm_natCast]
      field_simp [hyC]
    rw [heq]
    exact mul_le_mul_of_nonneg_right hn.le (sq_nonneg _)
  · exact hy2.const_mul_atTop (by linarith)

theorem num_cuspVertical_scaled_tendsto (γ : SL(2, ℤ)) :
    Tendsto (fun n : ℕ => UpperHalfPlane.num γ (cuspVertical n) /
      ((n + 1 : ℕ) : ℂ)) atTop (nhds ((γ 0 0 : ℂ) * I)) := by
  have hc : Tendsto (fun _ : ℕ => (γ 0 0 : ℂ) * I) atTop
      (nhds ((γ 0 0 : ℂ) * I)) := tendsto_const_nhds
  have hd := cuspVertical_inv_tendsto_zero.const_mul (γ 0 1 : ℂ)
  have ht := hc.add hd
  convert ht using 1
  · funext n
    unfold UpperHalfPlane.num
    simp only [cuspVertical_coe]
    have h00 :
        (((γ : GL (Fin 2) ℝ) 0 0 : ℝ) : ℂ) = (γ 0 0 : ℂ) := rfl
    have h01 :
        (((γ : GL (Fin 2) ℝ) 0 1 : ℝ) : ℂ) = (γ 0 1 : ℂ) := rfl
    rw [h00, h01]
    have hy : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    field_simp [hy]
  · ring

theorem coe_smul_SL2Z (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ • τ : ℍ) : ℂ) = UpperHalfPlane.num γ τ / UpperHalfPlane.denom γ τ := by
  change (((γ : GL (Fin 2) ℝ) • τ : ℍ) : ℂ) =
    UpperHalfPlane.num (γ : GL (Fin 2) ℝ) τ /
      UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ
  rw [UpperHalfPlane.coe_smul]
  simp [UpperHalfPlane.σ]

theorem smul_cuspVertical_tendsto_cusp (γ : SL(2, ℤ)) (hc : γ 1 0 ≠ 0) :
    Tendsto (fun n : ℕ => ((γ • cuspVertical n : ℍ) : ℂ)) atTop
      (nhds ((γ 0 0 : ℂ) / (γ 1 0 : ℂ))) := by
  have hcC : (γ 1 0 : ℂ) ≠ 0 := by exact_mod_cast hc
  have hquot := (num_cuspVertical_scaled_tendsto γ).div
    (denom_cuspVertical_scaled_tendsto γ) (mul_ne_zero hcC Complex.I_ne_zero)
  convert hquot using 1
  · funext n
    rw [coe_smul_SL2Z]
    simp only [Pi.div_apply]
    have hy : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    field_simp [hy, UpperHalfPlane.denom_ne_zero γ (cuspVertical n)]
  · field_simp [hcC, Complex.I_ne_zero]

/-- Unit-circle point associated to the rational cusp represented by `γ`. -/
def cuspRoot (γ : SL(2, ℤ)) : ℂ :=
  Complex.exp (2 * Real.pi * I * ((γ 0 0 : ℂ) / (γ 1 0 : ℂ)))

theorem qParam_smul_cuspVertical_tendsto_cuspRoot (γ : SL(2, ℤ))
    (hc : γ 1 0 ≠ 0) :
    Tendsto (fun n : ℕ => Function.Periodic.qParam 1
      ((γ • cuspVertical n : ℍ) : ℂ)) atTop (nhds (cuspRoot γ)) := by
  have h := (smul_cuspVertical_tendsto_cusp γ hc).const_mul
    (2 * (Real.pi : ℂ) * I) |>.cexp
  simpa [Function.Periodic.qParam, cuspRoot] using h

/-- Every finite rational cusp is a singular point of the disk `E₂`. -/
theorem not_continuesAcross_e2Disk_cuspRoot (γ : SL(2, ℤ))
    (hc : γ 1 0 ≠ 0) : ¬ Bottcher.ContinuesAcross e2Disk (cuspRoot γ) := by
  rintro ⟨U, hUo, hζU, G, hGd, hGeq⟩
  let qseq : ℕ → ℂ := fun n => Function.Periodic.qParam 1
    ((γ • cuspVertical n : ℍ) : ℂ)
  have hq : Tendsto qseq atTop (nhds (cuspRoot γ)) :=
    qParam_smul_cuspVertical_tendsto_cuspRoot γ hc
  have hqU : ∀ᶠ n : ℕ in atTop, qseq n ∈ U :=
    hq.eventually (hUo.mem_nhds hζU)
  have hqball : ∀ n : ℕ, qseq n ∈ ball (0 : ℂ) 1 := by
    intro n
    rw [mem_ball_zero_iff]
    exact Function.Periodic.norm_qParam_lt_one one_pos
      (γ • cuspVertical n : ℍ).im_pos
  have hvalues : (fun n => G (qseq n)) =ᶠ[atTop]
      (fun n => E₂ (γ • cuspVertical n)) := by
    filter_upwards [hqU] with n hn
    rw [hGeq ⟨hn, hqball n⟩, e2Disk_qParam]
  have hGcont : ContinuousAt G (cuspRoot γ) :=
    (hGd.differentiableAt (hUo.mem_nhds hζU)).continuousAt
  have hfinite : Tendsto (fun n => E₂ (γ • cuspVertical n)) atTop
      (nhds (G (cuspRoot γ))) :=
    (hGcont.tendsto.comp hq).congr' hvalues
  have hupper : ∀ᶠ n : ℕ in atTop,
      ‖E₂ (γ • cuspVertical n)‖ < ‖G (cuspRoot γ)‖ + 1 :=
    hfinite.norm.eventually (eventually_lt_nhds (lt_add_one _))
  have hlower : ∀ᶠ n : ℕ in atTop,
      ‖G (cuspRoot γ)‖ + 1 ≤ ‖E₂ (γ • cuspVertical n)‖ :=
    (Filter.tendsto_atTop.1 (e2_transformed_norm_tendsto_atTop γ hc)) _
  obtain ⟨n, hn, h'n⟩ := (hupper.and hlower).exists
  exact (not_lt_of_ge h'n) hn

/-- An explicit determinant-one matrix with first column `(a,c)`. -/
def coprimeCuspMatrix (a c : ℤ) (hcop : a.gcd c = 1) : SL(2, ℤ) :=
  ⟨!![a, -(a.gcdB c); c, a.gcdA c], by
    rw [Matrix.det_fin_two_of]
    have hbez := Int.gcd_eq_gcd_ab a c
    rw [hcop] at hbez
    calc
      a * a.gcdA c - -a.gcdB c * c = a * a.gcdA c + c * a.gcdB c := by ring
      _ = 1 := hbez.symm⟩

@[simp] theorem coprimeCuspMatrix_apply_zero_zero (a c : ℤ) (hcop) :
    coprimeCuspMatrix a c hcop 0 0 = a := rfl

@[simp] theorem coprimeCuspMatrix_apply_one_zero (a c : ℤ) (hcop) :
    coprimeCuspMatrix a c hcop 1 0 = c := rfl

theorem rat_num_gcd_den (q : ℚ) : q.num.gcd (q.den : ℤ) = 1 := by
  rw [Int.gcd_eq_natAbs]
  simpa using q.reduced.gcd_eq_one

/-- Canonical determinant-one matrix representing a rational cusp. -/
def ratCuspMatrix (q : ℚ) : SL(2, ℤ) :=
  coprimeCuspMatrix q.num q.den (rat_num_gcd_den q)

@[simp] theorem ratCuspMatrix_apply_zero_zero (q : ℚ) :
    ratCuspMatrix q 0 0 = q.num := rfl

@[simp] theorem ratCuspMatrix_apply_one_zero (q : ℚ) :
    ratCuspMatrix q 1 0 = q.den := rfl

theorem ratCuspMatrix_lowerLeft_ne_zero (q : ℚ) :
    ratCuspMatrix q 1 0 ≠ 0 := by
  simp only [ratCuspMatrix_apply_one_zero]
  exact_mod_cast q.den_nz

theorem cuspRoot_ratCuspMatrix (q : ℚ) :
    cuspRoot (ratCuspMatrix q) =
      Complex.exp (2 * Real.pi * I * (q : ℂ)) := by
  simp only [cuspRoot, ratCuspMatrix_apply_zero_zero, ratCuspMatrix_apply_one_zero]
  rw [Rat.cast_def]
  norm_cast

def unitExpReal (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * I * (x : ℂ))

def unitExpRat (q : ℚ) : ℂ :=
  Complex.exp (2 * Real.pi * I * (q : ℂ))

theorem unitExpReal_eq_of_norm_one {w : ℂ} (hw : ‖w‖ = 1) :
    unitExpReal (w.arg / (2 * Real.pi)) = w := by
  unfold unitExpReal
  rw [show 2 * (Real.pi : ℂ) * I * ((w.arg / (2 * Real.pi) : ℝ) : ℂ) =
      (w.arg : ℂ) * I by
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast
    field_simp [hpi]]
  simpa [hw] using norm_mul_exp_arg_mul_I w

theorem dense_unitExpRat :
    sphere (0 : ℂ) 1 ⊆ closure (range unitExpRat) := by
  intro w hw
  rw [mem_sphere_zero_iff_norm] at hw
  rw [Metric.mem_closure_iff]
  intro ε hε
  let x : ℝ := w.arg / (2 * Real.pi)
  have hx : unitExpReal x = w := unitExpReal_eq_of_norm_one hw
  have hcont : ContinuousAt unitExpReal x := by
    unfold unitExpReal
    fun_prop
  obtain ⟨δ, hδ, hmap⟩ := Metric.continuousAt_iff.mp hcont ε hε
  obtain ⟨q, hq⟩ := Rat.denseRange_cast.exists_dist_lt x hδ
  refine ⟨unitExpRat q, ⟨q, rfl⟩, ?_⟩
  rw [← hx]
  have hcast : unitExpRat q = unitExpReal (q : ℝ) := by
    simp [unitExpRat, unitExpReal]
  rw [hcast, dist_comm]
  apply hmap
  simpa [dist_comm] using hq

theorem dense_ratCuspRoots :
    sphere (0 : ℂ) 1 ⊆
      closure {z : ℂ | ∃ q : ℚ, z = cuspRoot (ratCuspMatrix q)} := by
  intro w hw
  have h := dense_unitExpRat hw
  apply closure_mono _ h
  rintro z ⟨q, rfl⟩
  exact ⟨q, (cuspRoot_ratCuspMatrix q).symm⟩

/-- The unit circle is a pointwise natural boundary of the disk `E₂`. -/
theorem e2Disk_naturalBoundary {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ¬ Bottcher.ContinuesAcross e2Disk ζ := by
  rintro ⟨U, hUo, hζU, G, hGd, hGeq⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUo ζ hζU
  have hζcl : ζ ∈ closure
      {z : ℂ | ∃ q : ℚ, z = cuspRoot (ratCuspMatrix q)} := by
    apply dense_ratCuspRoots
    simpa [mem_sphere_zero_iff_norm]
  rw [Metric.mem_closure_iff] at hζcl
  obtain ⟨z0, hz0set, hz0dist⟩ := hζcl ε hε
  obtain ⟨q, hq⟩ := hz0set
  subst z0
  apply not_continuesAcross_e2Disk_cuspRoot
    (ratCuspMatrix q) (ratCuspMatrix_lowerLeft_ne_zero q)
  exact ⟨U, hUo, hball (by simpa [mem_ball, dist_comm] using hz0dist), G, hGd, hGeq⟩

end

end GaloisForLFunctions.HTGeometry
