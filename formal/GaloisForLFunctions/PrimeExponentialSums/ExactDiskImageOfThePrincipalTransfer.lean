import GaloisForLFunctions.PrimeExponentialSums.PrincipalRamanujanTransferOnTheDisk

/-!
# Exact disks for the principal Ramanujan factor

The fractional part of the transfer is an involution. It maps every
closed disk of radius r<p centered at zero onto an explicit disk. Its
center passes through zero at r²=p, where every boundary phase has
the same output modulus. Beyond that circle the positive real input
is extremal.
-/

noncomputable section
namespace GaloisForLFunctions.PrimeExponentialSums.PrincipalRamanujan

def center (p r : ℝ) := p*(p-r^2)/(p^2-r^2)
def radius (p r : ℝ) := p*r*(p-1)/(p^2-r^2)

private theorem denominator_pos {p r : ℝ} (hp : 1<p) (hr : 0≤r) (hrp : r<p) :
    0<p^2-r^2 := by
  have h := mul_pos (sub_pos.mpr hrp) (show 0<p+r by linarith only [hp,hr])
  nlinarith only [h]

/-- Pullback of the defining quadratic of the output disk. -/
theorem disk_identity {p r : ℝ} (hp : 1<p) (hr : 0≤r) (hrp : r<p) (w : ℂ) :
    (p^2-r^2)*(‖w-(center p r : ℂ)‖^2-(radius p r)^2) =
      p^2*‖(1 : ℂ)-w‖^2-r^2*‖(p : ℂ)-w‖^2 := by
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.one_re,Complex.one_im]
  unfold center radius
  field_simp [(denominator_pos hp hr hrp).ne']
  ring

private theorem pole_gap {p : ℝ} {z : ℂ} (hz : (p : ℂ)-z≠0) :
    (p : ℂ)-fraction p z = (p : ℂ)*(p-1)/(p-z) := by
  unfold fraction
  field_simp
  ring

/-- Self-inversion away from the pole. -/
theorem fraction_involution {p : ℝ} (hp : 1<p) {z : ℂ} (hz : (p : ℂ)-z≠0) :
    fraction p (fraction p z)=z := by
  have hp₀ : (p : ℂ)≠0 := by exact_mod_cast (zero_lt_one.trans hp).ne'
  have hp₁ : (p : ℂ)-1≠0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne')
  rw [fraction,pole_gap hz,fraction]
  field_simp
  ring

private theorem disk_test {p r : ℝ} (hp : 1<p) (hr : 0≤r) (hrp : r<p) (w : ℂ) :
    ‖w-(center p r : ℂ)‖ ≤ radius p r ↔
      p*‖(1 : ℂ)-w‖ ≤ r*‖(p : ℂ)-w‖ := by
  have hd := denominator_pos hp hr hrp
  have hR : 0≤radius p r := div_nonneg
    (mul_nonneg (mul_nonneg (zero_lt_one.trans hp).le hr) (sub_nonneg.mpr hp.le)) hd.le
  rw [← sq_le_sq₀ (norm_nonneg _) hR,
    ← sq_le_sq₀ (mul_nonneg (zero_lt_one.trans hp).le (norm_nonneg _)) (mul_nonneg hr (norm_nonneg _)),
    mul_pow,mul_pow]
  have h := disk_identity hp hr hrp w
  constructor
  · intro he
    have hh := mul_nonpos_of_nonneg_of_nonpos hd.le (sub_nonpos.mpr he)
    rwa [h,sub_nonpos] at hh
  · intro he
    apply sub_nonpos.mp
    by_contra! hpos
    have hh := mul_pos hd hpos
    rw [h] at hh
    exact (not_lt_of_ge (sub_nonpos.mpr he)) hh

private theorem pole_outside {p r : ℝ} (hp : 1<p) (hr : 0≤r) (hrp : r<p) {w : ℂ}
    (hw : ‖w-(center p r : ℂ)‖≤radius p r) : (p : ℂ)-w≠0 := by
  intro he
  have h := (disk_test hp hr hrp w).1 hw
  rw [he,norm_zero,mul_zero] at h
  have hw' : w=(p:ℂ) := (sub_eq_zero.mp he).symm
  have hn : (1 : ℂ)-w ≠ 0 := by rw [hw']; exact sub_ne_zero.mpr (by exact_mod_cast hp.ne)
  exact (not_lt_of_ge h) (mul_pos (zero_lt_one.trans hp) (norm_pos_iff.mpr hn))

private theorem inside_iff {p r : ℝ} (hp : 1<p) (hr : 0≤r) (hrp : r<p) {w : ℂ}
    (hw : (p : ℂ)-w≠0) :
    ‖w-(center p r : ℂ)‖≤radius p r ↔ ‖fraction p w‖≤r := by
  rw [disk_test hp hr hrp,fraction,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (zero_lt_one.trans hp),div_le_iff₀ (norm_pos_iff.mpr hw)]

/-- The exact image, with no exclusion of the input or output boundaries. -/
theorem image_disk {p r : ℝ} (hp : 1<p) (hr : 0≤r) (hrp : r<p) :
    fraction p '' {z : ℂ | ‖z‖≤r} = {w : ℂ | ‖w-(center p r : ℂ)‖≤radius p r} := by
  ext w
  constructor
  · rintro ⟨z,hz,rfl⟩
    have hP : (p:ℂ)-z ≠ 0 := by
      intro he
      have hn := sub_eq_zero.mp he
      have hz' : ‖z‖≤r := hz
      rw [← hn,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (zero_lt_one.trans hp)] at hz'
      exact (not_lt_of_ge hz') hrp
    have hp₀ : (p : ℂ)≠0 := by exact_mod_cast (zero_lt_one.trans hp).ne'
    have hp₁ : (p : ℂ)-1≠0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne')
    have hQ : (p:ℂ)-fraction p z ≠ 0 := by rw [pole_gap hP]; exact div_ne_zero (mul_ne_zero hp₀ hp₁) hP
    exact (inside_iff hp hr hrp hQ).2 (by rwa [fraction_involution hp hP])
  · intro hw
    have hP := pole_outside hp hr hrp hw
    exact ⟨fraction p w,(inside_iff hp hr hrp hP).1 hw,fraction_involution hp hP⟩

/-- At the critical radius sqrt p, the fractional factor is an automorphism
of the disk centered at zero. -/
theorem critical_disk {p r : ℝ} (hp : 1<p) (hr : 0≤r) (he : r^2=p) :
    fraction p '' {z : ℂ | ‖z‖≤r} = {z : ℂ | ‖z‖≤r} := by
  have hrp : r<p := by
    by_contra! h
    have h₁ : 0 < p*(p-1) := mul_pos (zero_lt_one.trans hp) (sub_pos.mpr hp)
    have h₂ := sq_le_sq₀ (zero_lt_one.trans hp).le hr |>.2 h
    nlinarith only [he,h₁,h₂]
  have hc : center p r=0 := by simp [center,he]
  have hR : radius p r=r := by
    unfold radius
    apply (div_eq_iff (denominator_pos hp hr hrp).ne').2
    rw [he]
    ring
  rw [image_disk hp hr hrp,hc,hR]
  simp

/-- Above the critical radius the output center is negative, and the
positive real input gives the maximum modulus p(r−1)/(p−r). -/
theorem upper_radius_extremum {p r : ℝ} (hp : 1<p) (hr : 0≤r) (hrp : r<p)
    (hc : p≤r^2) :
    (∀ z : ℂ, ‖z‖≤r → ‖fraction p z‖ ≤ p*(r-1)/(p-r)) ∧
      ‖fraction p (r : ℂ)‖=p*(r-1)/(p-r) := by
  have hd := denominator_pos hp hr hrp
  have hcenter : center p r≤0 := div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (zero_lt_one.trans hp).le (sub_nonpos.mpr hc)) hd.le
  have hsum : radius p r-center p r=p*(r-1)/(p-r) := by
    unfold radius center
    field_simp [hd.ne',(sub_pos.mpr hrp).ne']
    ring
  have hr₁ : 1≤r := by
    by_contra! h
    have h₀ := mul_nonneg hr (sub_nonneg.mpr h.le)
    nlinarith only [hp,hc,h,h₀]
  constructor
  · intro z hz
    have hmem : fraction p z ∈ fraction p '' {u : ℂ | ‖u‖≤r} := ⟨z,hz,rfl⟩
    rw [image_disk hp hr hrp] at hmem
    have hball : ‖fraction p z-(center p r : ℂ)‖≤radius p r := hmem
    have h := norm_add_le (fraction p z-(center p r : ℂ)) (center p r : ℂ)
    rw [sub_add_cancel,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos hcenter] at h
    linarith only [h,hball,hsum]
  · have he : fraction p (r : ℂ) = ((p*(1-r)/(p-r) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (zero_lt_one.trans hp).le (sub_nonpos.mpr hr₁))
      (sub_nonneg.mpr hrp.le))]
    ring

end GaloisForLFunctions.PrimeExponentialSums.PrincipalRamanujan
