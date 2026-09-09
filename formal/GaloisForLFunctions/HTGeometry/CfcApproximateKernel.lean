import GaloisForLFunctions.HTGeometry.CfcKernelPreservation

/-!
# Continuous spectral zero sets determine bounded approximate kernels

A signed remainder g/(1+n f²) tends uniformly to zero on the compact spectrum
when every zero of f is a zero of g. Its complement is a continuous multiple
of f, giving approximate factorization in operator norm. This transfers
vanishing residuals for uniformly bounded vector families. Equal zero sets
and singleton fibres give exact two-way limit criteria, with no spectral gap
or differentiability assumption. No spectral occurrence is asserted.
-/

open Filter Topology
namespace GaloisForLFunctions.HTGeometry
noncomputable section

private def approximateKernelRemainder (f g : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  g x / (1+(n:ℝ)*f x ^ 2)

private theorem approximateKernel_den_pos (f : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    0 < 1+(n:ℝ)*f x ^ 2 := by positivity

private theorem approximateKernelRemainder_continuousOn {K : Set ℝ} {f g : ℝ → ℝ}
    (hf : ContinuousOn f K) (hg : ContinuousOn g K) (n : ℕ) :
    ContinuousOn (approximateKernelRemainder f g n) K :=
  hg.div (continuousOn_const.add (continuousOn_const.mul (hf.pow 2)))
    (fun x _ => ne_of_gt (approximateKernel_den_pos f n x))

private theorem approximateKernelRemainder_norm (f g : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    ‖approximateKernelRemainder f g n x‖ = |g x|/(1+(n:ℝ)*f x ^ 2) := by
  rw [approximateKernelRemainder,Real.norm_eq_abs,abs_div,
    abs_of_pos (approximateKernel_den_pos f n x)]

private theorem approximateKernelRemainder_uniform {K : Set ℝ} {f g : ℝ → ℝ}
    (hK : IsCompact K) (hf : ContinuousOn f K) (hg : ContinuousOn g K)
    (hz : ∀ x ∈ K, f x=0 → g x=0) :
    TendstoUniformlyOn (fun n x => ‖approximateKernelRemainder f g n x‖)
      (fun _ => 0) atTop K := by
  refine Antitone.tendstoUniformlyOn_of_forall_tendsto hK
    (fun n => (approximateKernelRemainder_continuousOn hf hg n).norm) ?_ continuousOn_const ?_
  · intro x _ m n hmn
    dsimp only
    rw [approximateKernelRemainder_norm,approximateKernelRemainder_norm]
    apply div_le_div_of_nonneg_left (abs_nonneg _) (approximateKernel_den_pos f m x)
    have hc : (m:ℝ) ≤ n := by exact_mod_cast hmn
    nlinarith [sq_nonneg (f x)]
  · intro x hx
    simp_rw [approximateKernelRemainder_norm]
    by_cases hfx : f x=0
    · simp [hz x hx hfx]
    · have hs : 0 < f x ^ 2 := sq_pos_of_ne_zero hfx
      have hn : Tendsto (fun n : ℕ => (n:ℝ)*f x ^ 2) atTop atTop :=
        Tendsto.atTop_mul_const hs tendsto_natCast_atTop_atTop
      exact Tendsto.div_atTop tendsto_const_nhds
        (tendsto_atTop_add_const_left atTop (1:ℝ) hn)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every continuous spectral zero-set inclusion admits arbitrarily accurate
operator-norm factorization through the first symbol, with continuous factors. -/
theorem cfc_exists_approximate_factor_of_zero_set_subset
    (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) (f g : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ B)) (hg : ContinuousOn g (spectrum ℝ B))
    (hz : ∀ x ∈ spectrum ℝ B, f x=0 → g x=0) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℝ → ℝ, ContinuousOn k (spectrum ℝ B) ∧
      ‖cfc g B-cfc k B*cfc f B‖ < ε := by
  classical
  by_cases htr : Subsingleton H
  · letI := htr
    refine ⟨fun _ => 0,continuousOn_const,?_⟩
    simpa only [Subsingleton.elim (cfc g B-cfc (fun _ : ℝ => (0:ℝ)) B*cfc f B) 0,norm_zero] using hε
  haveI : Nontrivial H := not_subsingleton_iff_nontrivial.mp htr
  have hn : Tendsto (fun n => ‖cfc (approximateKernelRemainder f g n) B‖) atTop (𝓝 0) := by
    apply tendsto_norm_cfc_zero _ B hB
    · exact Filter.Eventually.of_forall (approximateKernelRemainder_continuousOn hf hg)
    · intro δ hδ
      have hu := (Metric.tendstoUniformlyOn_iff.mp
        (approximateKernelRemainder_uniform (spectrum.isCompact B) hf hg hz)) δ hδ
      filter_upwards [hu] with n hn x hx
      simpa only [dist_zero_left,norm_norm] using (hn x hx).le
  obtain ⟨n,hn⟩ := (hn.eventually (gt_mem_nhds hε)).exists
  let k : ℝ → ℝ := fun x => (n:ℝ)*g x*f x/(1+(n:ℝ)*f x ^ 2)
  have hk : ContinuousOn k (spectrum ℝ B) :=
    ((continuousOn_const.mul hg).mul hf).div
      (continuousOn_const.add (continuousOn_const.mul (hf.pow 2)))
      (fun x _ => ne_of_gt (approximateKernel_den_pos f n x))
  refine ⟨k,hk,?_⟩
  have he : cfc g B-cfc k B*cfc f B = cfc (approximateKernelRemainder f g n) B := by
    rw [← cfc_mul k f B hk hf,← cfc_sub g (fun x => k x*f x) B hg (hk.mul hf)]
    apply cfc_congr
    intro x _
    dsimp [k,approximateKernelRemainder]
    field_simp [ne_of_gt (approximateKernel_den_pos f n x)]
    ring
  rwa [he]

/-- Vanishing residuals transfer along spectral zero-set inclusion for every
uniformly bounded vector family. Neither a quotient bound nor a spectral gap is needed. -/
theorem cfc_apply_tendsto_zero_of_zero_set_subset
    {ι : Type*} {l : Filter ι}
    (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) (f g : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ B)) (hg : ContinuousOn g (spectrum ℝ B))
    (hz : ∀ x ∈ spectrum ℝ B, f x=0 → g x=0)
    (v : ι → H) {M : ℝ} (hM : 0 ≤ M) (hv : ∀ i, ‖v i‖ ≤ M)
    (ht : Tendsto (fun i => ‖cfc f B (v i)‖) l (𝓝 0)) :
    Tendsto (fun i => ‖cfc g B (v i)‖) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨k,hk,he⟩ := cfc_exists_approximate_factor_of_zero_set_subset
    B hB f g hf hg hz (div_pos (half_pos hε) (by positivity : 0 < M+1))
  have hb : ‖cfc g B-cfc k B*cfc f B‖*M < ε/2 := by
    have h1 := (lt_div_iff₀ (by positivity : 0 < M+1)).mp he
    nlinarith [norm_nonneg (cfc g B-cfc k B*cfc f B)]
  have hh : Tendsto (fun i => ‖cfc k B‖*‖cfc f B (v i)‖) l (𝓝 0) := by
    simpa using ht.const_mul ‖cfc k B‖
  filter_upwards [hh.eventually (gt_mem_nhds (half_pos hε))] with i hi
  have hid : cfc g B (v i) =
      (cfc g B-cfc k B*cfc f B) (v i)+cfc k B (cfc f B (v i)) := by
    simp [sub_apply,mul_apply_eq_comp]
  have hb' : ‖cfc g B (v i)‖ ≤
      ‖cfc g B-cfc k B*cfc f B‖*M+‖cfc k B‖*‖cfc f B (v i)‖ := by
    calc
      _ ≤ ‖(cfc g B-cfc k B*cfc f B) (v i)‖+‖cfc k B (cfc f B (v i))‖ := by
        rw [hid]
        exact norm_add_le _ _
      _ ≤ ‖cfc g B-cfc k B*cfc f B‖*‖v i‖+‖cfc k B‖*‖cfc f B (v i)‖ :=
        add_le_add ((cfc g B-cfc k B*cfc f B).le_opNorm _) ((cfc k B).le_opNorm _)
      _ ≤ _ := by gcongr; exact hv i
  rw [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  linarith

/-- Equal continuous spectral zero sets have exactly the same bounded approximate kernels. -/
theorem cfc_apply_tendsto_zero_iff_of_zero_set_eq
    {ι : Type*} {l : Filter ι}
    (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) (f g : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ B)) (hg : ContinuousOn g (spectrum ℝ B))
    (hz : ∀ x ∈ spectrum ℝ B, f x=0 ↔ g x=0)
    (v : ι → H) {M : ℝ} (hM : 0 ≤ M) (hv : ∀ i, ‖v i‖ ≤ M) :
    Tendsto (fun i => ‖cfc f B (v i)‖) l (𝓝 0) ↔
      Tendsto (fun i => ‖cfc g B (v i)‖) l (𝓝 0) :=
  ⟨cfc_apply_tendsto_zero_of_zero_set_subset B hB f g hf hg (fun x hx => (hz x hx).mp) v hM hv,
    cfc_apply_tendsto_zero_of_zero_set_subset B hB g f hg hf (fun x hx => (hz x hx).mpr) v hM hv⟩

private theorem cfc_approx_shift_apply (B : H →L[ℂ] H) (hB : IsSelfAdjoint B)
    (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ B)) (c : ℝ) (v : H) :
    cfc (fun x => f x-c) B v = cfc f B v-(c:ℂ) • v := by
  rw [cfc_sub f (fun _ => c) B hf continuousOn_const,cfc_const c B hB]
  simp [Algebra.algebraMap_eq_smul_one]

/-- A singleton continuous spectral fibre recovers the original approximate
eigen-equation for every bounded family, in both directions. -/
theorem cfc_residual_tendsto_zero_iff_of_singleton_fibre
    {ι : Type*} {l : Filter ι}
    (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ B)) (c b : ℝ)
    (hfibre : ∀ x ∈ spectrum ℝ B, f x=c ↔ x=b)
    (v : ι → H) {M : ℝ} (hM : 0 ≤ M) (hv : ∀ i, ‖v i‖ ≤ M) :
    Tendsto (fun i => ‖cfc f B (v i)-(c:ℂ) • v i‖) l (𝓝 0) ↔
      Tendsto (fun i => ‖B (v i)-(b:ℂ) • v i‖) l (𝓝 0) := by
  have h := cfc_apply_tendsto_zero_iff_of_zero_set_eq (l := l) B hB
    (fun x => f x-c) (fun x => x-b)
    (hf.sub continuousOn_const) (continuousOn_id.sub continuousOn_const)
    (fun x hx => by simpa only [sub_eq_zero] using hfibre x hx) v hM hv
  simpa only [cfc_approx_shift_apply B hB f hf c,
    cfc_approx_shift_apply B hB (fun x => x) continuousOn_id b,cfc_id' ℝ B hB] using h

end
end GaloisForLFunctions.HTGeometry
