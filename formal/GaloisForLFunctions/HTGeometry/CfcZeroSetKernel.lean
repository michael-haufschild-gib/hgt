import GaloisForLFunctions.HTGeometry.CfcKernelPreservation

/-!
# Continuous spectral zero sets determine vector kernels

Dini convergence of g(x)^2/(1+n f(x)^2) transfers inclusion of continuous
spectral zero sets to inclusion of actual Hilbert-space kernels. No quotient
bound or spectral gap is needed. Equal zero sets give equal kernels, and a
singleton spectral fibre recovers the original operator eigenspace exactly.
-/

open Filter Topology
open scoped InnerProductSpace
namespace GaloisForLFunctions.HTGeometry
noncomputable section

private def zeroSetRegularizer (f g : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  g x ^ 2 / (1+(n:ℝ)*f x ^ 2)

private theorem zeroSetRegularizer_den_pos (f : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    0 < 1+(n:ℝ)*f x ^ 2 := by positivity

private theorem zeroSetRegularizer_continuousOn {K : Set ℝ} {f g : ℝ → ℝ}
    (hf : ContinuousOn f K) (hg : ContinuousOn g K) (n : ℕ) :
    ContinuousOn (zeroSetRegularizer f g n) K :=
  (hg.pow 2).div (continuousOn_const.add (continuousOn_const.mul (hf.pow 2)))
    (fun x _ => ne_of_gt (zeroSetRegularizer_den_pos f n x))

private theorem zeroSetRegularizer_antitone (f g : ℝ → ℝ) (x : ℝ) :
    Antitone (fun n => zeroSetRegularizer f g n x) := by
  intro m n hmn
  apply div_le_div_of_nonneg_left (sq_nonneg (g x)) (zeroSetRegularizer_den_pos f m x)
  have hc : (m:ℝ) ≤ n := by exact_mod_cast hmn
  simpa only [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_right hc (sq_nonneg (f x))) 1

private theorem zeroSetRegularizer_tendsto {f g : ℝ → ℝ} {x : ℝ}
    (hz : f x=0 → g x=0) :
    Tendsto (fun n => zeroSetRegularizer f g n x) atTop (𝓝 0) := by
  by_cases hf : f x=0
  · simp [zeroSetRegularizer,hz hf]
  · have hs : 0 < f x ^ 2 := sq_pos_of_ne_zero hf
    have hn : Tendsto (fun n : ℕ => (n:ℝ)*f x ^ 2) atTop atTop :=
      Tendsto.atTop_mul_const hs tendsto_natCast_atTop_atTop
    have hd : Tendsto (fun n : ℕ => 1+(n:ℝ)*f x ^ 2) atTop atTop :=
      tendsto_atTop_add_const_left atTop (1:ℝ) hn
    exact Tendsto.div_atTop tendsto_const_nhds hd

private theorem zeroSetRegularizer_uniform {K : Set ℝ} {f g : ℝ → ℝ}
    (hK : IsCompact K) (hf : ContinuousOn f K) (hg : ContinuousOn g K)
    (hz : ∀ x ∈ K, f x=0 → g x=0) :
    TendstoUniformlyOn (zeroSetRegularizer f g) (fun _ => 0) atTop K :=
  Antitone.tendstoUniformlyOn_of_forall_tendsto hK
    (zeroSetRegularizer_continuousOn hf hg) (fun x _ => zeroSetRegularizer_antitone f g x)
    continuousOn_const (fun x hx => zeroSetRegularizer_tendsto (hz x hx))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Inclusion of continuous spectral zero sets gives actual Hilbert-space kernel
inclusion, without a spectral gap or a bounded quotient between the symbols. -/
theorem cfc_apply_eq_zero_of_zero_set_subset
    (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) (f g : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ B)) (hg : ContinuousOn g (spectrum ℝ B))
    (hz : ∀ x ∈ spectrum ℝ B, f x=0 → g x=0)
    (v : H) (hv : cfc f B v=0) : cfc g B v=0 := by
  nontriviality H
  have hnorm : Tendsto (fun n => ‖cfc (zeroSetRegularizer f g n) B‖) atTop (𝓝 0) := by
    apply tendsto_norm_cfc_zero _ B hB
    · exact Filter.Eventually.of_forall (zeroSetRegularizer_continuousOn hf hg)
    · intro ε hε
      have hu := (Metric.tendstoUniformlyOn_iff.mp
        (zeroSetRegularizer_uniform (spectrum.isCompact B) hf hg hz)) ε hε
      filter_upwards [hu] with n hn x hx
      simpa only [dist_zero_left] using (hn x hx).le
  have heq (n : ℕ) : ((cfc g B)^2) v = cfc (zeroSetRegularizer f g n) B v := by
    let k : ℝ → ℝ := fun x => (n:ℝ)*g x ^ 2*f x / (1+(n:ℝ)*f x ^ 2)
    have hk : ContinuousOn k (spectrum ℝ B) :=
      ((continuousOn_const.mul (hg.pow 2)).mul hf).div
        (continuousOn_const.add (continuousOn_const.mul (hf.pow 2)))
        (fun x _ => ne_of_gt (zeroSetRegularizer_den_pos f n x))
    have hid : cfc (fun x => g x ^ 2-zeroSetRegularizer f g n x) B = cfc k B*cfc f B := by
      rw [← cfc_mul k f B hk hf]
      apply cfc_congr
      intro x _
      dsimp [k,zeroSetRegularizer]
      field_simp [ne_of_gt (zeroSetRegularizer_den_pos f n x)]
      ring
    rw [cfc_sub (fun x => g x ^ 2) (zeroSetRegularizer f g n) B
      (hg.pow 2) (zeroSetRegularizer_continuousOn hf hg n),cfc_pow g 2 B hg hB] at hid
    have ha := congrArg (fun T : H →L[ℂ] H => T v) hid
    simp only [sub_apply,mul_apply_eq_comp,hv,map_zero] at ha
    exact sub_eq_zero.mp ha
  have hlim : Tendsto (fun _ : ℕ => ‖((cfc g B)^2) v‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) (by simpa using hnorm.mul_const ‖v‖)
    rw [heq n]
    exact (cfc (zeroSetRegularizer f g n) B).le_opNorm v
  have hs : ((cfc g B)^2) v=0 := norm_eq_zero.mp (tendsto_const_nhds_iff.mp hlim)
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (show IsSelfAdjoint (cfc g B) from IsSelfAdjoint.cfc)
  have hp : inner ℂ (cfc g B (cfc g B v)) v = inner ℂ (cfc g B v) (cfc g B v) :=
    hsym (cfc g B v) v
  have hs' : cfc g B (cfc g B v)=0 := by simpa only [pow_two,mul_apply_eq_comp] using hs
  rw [← hp,hs',inner_zero_left]

/-- Equal continuous spectral zero sets give exactly equal vector kernels. -/
theorem cfc_apply_eq_zero_iff_of_zero_set_eq
    (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) (f g : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ B)) (hg : ContinuousOn g (spectrum ℝ B))
    (hz : ∀ x ∈ spectrum ℝ B, f x=0 ↔ g x=0) (v : H) :
    cfc f B v=0 ↔ cfc g B v=0 :=
  ⟨cfc_apply_eq_zero_of_zero_set_subset B hB f g hf hg (fun x hx => (hz x hx).mp) v,
    cfc_apply_eq_zero_of_zero_set_subset B hB g f hg hf (fun x hx => (hz x hx).mpr) v⟩

private theorem cfc_shift_apply (B : H →L[ℂ] H) (hB : IsSelfAdjoint B)
    (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ B)) (c : ℝ) (v : H) :
    cfc (fun x => f x-c) B v = cfc f B v-(c:ℂ) • v := by
  rw [cfc_sub f (fun _ => c) B hf continuousOn_const,cfc_const c B hB]
  simp [Algebra.algebraMap_eq_smul_one]

/-- A singleton spectral fibre recovers precisely the original eigenspace.
Neither existence of that eigenvalue nor nonvanishing of a vector is assumed. -/
theorem cfc_eigenvector_iff_of_singleton_fibre
    (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ B)) (c b : ℝ)
    (hfibre : ∀ x ∈ spectrum ℝ B, f x=c ↔ x=b) (v : H) :
    cfc f B v=(c:ℂ) • v ↔ B v=(b:ℂ) • v := by
  have h := cfc_apply_eq_zero_iff_of_zero_set_eq B hB
    (fun x => f x-c) (fun x => x-b)
    (hf.sub continuousOn_const) (continuousOn_id.sub continuousOn_const)
    (fun x hx => by simpa only [sub_eq_zero] using hfibre x hx) v
  rw [cfc_shift_apply B hB f hf c v,
    cfc_shift_apply B hB (fun x => x) continuousOn_id b v,cfc_id' ℝ B hB] at h
  simpa only [sub_eq_zero] using h

end
end GaloisForLFunctions.HTGeometry
