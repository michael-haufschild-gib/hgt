import GaloisForLFunctions.HTGeometry.ComplexMetricEinsteinSpatialSource

set_option autoImplicit false
namespace GaloisForLFunctions.HTGeometry.ComplexMetricField
open ScalarTwoJet ComplexCoordinateMetricTwoJet ComplexCoordinateConnection Filter Topology
open scoped ContDiff
noncomputable section
variable {d : ℕ}

private theorem amplitude_inverse_smooth (g h : Field d) (x : Fin d → ℝ)
    (hdet : (g x).det ≠ 0) (i j : Fin d) :
    ContDiffAt ℂ 2 (fun e => (affineField g h e x)⁻¹ i j) 0 := by
  have hd : ContDiffAt ℂ 2 (fun e => (affineField g h e x).det) 0 := by
    simp only [Matrix.det_apply',affineField,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
    fun_prop
  have ha : ContDiffAt ℂ 2 (fun e => (affineField g h e x).adjugate i j) 0 := by
    have he : (fun e => (affineField g h e x).adjugate i j) =
        fun e => ((affineField g h e x).updateRow j (Pi.single i 1)).det := by
      funext e; exact Matrix.adjugate_apply _ i j
    rw [he]
    simp only [Matrix.det_apply']
    apply ContDiffAt.sum
    intro s _
    apply contDiffAt_const.mul
    apply contDiffAt_prod
    intro a _
    by_cases hj : s a = j
    · simp only [Matrix.updateRow_apply,hj,if_pos]
      exact contDiffAt_const
    · simp only [Matrix.updateRow_apply,hj]
      change ContDiffAt ℂ 2 (fun e => g x (s a) a+e*h x (s a) a) 0
      fun_prop
  have hn : (affineField g h 0 x).det ≠ 0 := by simpa [affineField] using hdet
  have he : (fun e => (affineField g h e x)⁻¹ i j) =
      fun e => ((affineField g h e x).det)⁻¹*(affineField g h e x).adjugate i j := by
    funext e
    rw [Matrix.inv_def,Ring.inverse_eq_inv',Matrix.smul_apply,smul_eq_mul]
  rw [he]
  exact (hd.inv hn).mul ha

private theorem amplitude_connection_smooth (g h : Field d) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ 2 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 2 (fun y => h y i j) x)
    (hdet : (g x).det ≠ 0) (k a b : Fin d) :
    ContDiffAt ℂ 2 (fun e => connection (affineField g h e) x k a b) 0 := by
  have hj (e : ℂ) : twoJet (affineField g h e) x =
      ofSpace (amplitudeJet (jetSpace g x) (jetSpace h x) e) :=
    congrArg ofSpace (jetSpace_add_smul g h x e hg hh)
  have he : (fun e => connection (affineField g h e) x k a b) =
      fun e => (1/2 : ℂ)*∑ m, (affineField g h e x)⁻¹ a m*
        ((amplitudeJet (jetSpace g x) (jetSpace h x) e).2.1 k m b+
          (amplitudeJet (jetSpace g x) (jetSpace h x) e).2.1 b m k-
          (amplitudeJet (jetSpace g x) (jetSpace h x) e).2.1 m k b) := by
    funext e
    unfold connection
    rw [hj]
    rfl
  rw [he]
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro m _
  apply (amplitude_inverse_smooth g h x hdet a m).mul
  unfold amplitudeJet
  fun_prop

/-- At a double zero, the second coefficient retains only the weight's background value. -/
private theorem weighted_second {w f : ℂ → ℂ}
    (hw : ContDiffAt ℂ 2 w 0) (hf : ContDiffAt ℂ 2 f 0)
    (h0 : f 0 = 0) (h1 : deriv f 0 = 0) :
    iteratedDeriv 2 (fun e => w e*f e) 0 = w 0*iteratedDeriv 2 f 0 := by
  rw [iteratedDeriv_fun_mul hw hf]
  simp [Finset.sum_range_succ,iteratedDeriv_zero,iteratedDeriv_one,h0,h1]

/-- The original contracted divergence, expanded without discarding either tensor-index action. -/
def amplitudeDivergence (g h : Field d) (Λ : ℂ) (x : Fin d → ℝ) (j : Fin d) (e : ℂ) : ℂ :=
  ∑ k, ∑ b, ((affineField g h e x)⁻¹ b k*spatialSource g h Λ x k b j e-
    (∑ a, ((affineField g h e x)⁻¹ b k*connection (affineField g h e) x k a b)*affineSource g h Λ x a j e)-
    (∑ a, ((affineField g h e x)⁻¹ b k*connection (affineField g h e) x k a j)*affineSource g h Λ x b a e))

theorem amplitudeDivergence_eq (g h : Field d) (Λ : ℂ) (x : Fin d → ℝ) (j : Fin d) (e : ℂ) :
    amplitudeDivergence g h Λ x j e =
      tensorDivergence (affineField g h e) (literalEinstein (affineField g h e) Λ) x j := by
  unfold amplitudeDivergence tensorDivergence covariantTwo
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro b _
  simp only [Matrix.sub_apply,Matrix.mul_apply,Matrix.transpose_apply,mul_sub,Finset.mul_sum]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro a _
    unfold affineSource
    ring
  · apply Finset.sum_congr rfl
    intro a _
    unfold affineSource
    ring

/-- The full tensor of original Einstein Hessian entries on actual field jets. -/
def hessianTensor (g h : Field d) : Field d := fun x i j => hessianField g h x i j

/-- Full coefficient contraction: all moving metric weights multiply lower-order zero fields. -/
private theorem amplitudeDivergence_second (g h : Field d) (Λ : ℂ) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 3 (fun y => h y i j) x)
    (hdet : (g x).det ≠ 0)
    (hE0 : ∀ i j, affineSource g h Λ x i j 0 = 0)
    (hE1 : ∀ i j, deriv (affineSource g h Λ x i j) 0 = 0)
    (hS0 : ∀ k i j, spatialSource g h Λ x k i j 0 = 0)
    (hS1 : ∀ k i j, deriv (spatialSource g h Λ x k i j) 0 = 0) (j : Fin d) :
    iteratedDeriv 2 (amplitudeDivergence g h Λ x j) 0 =
      tensorDivergence g (hessianTensor g h) x j := by
  have hg2 (a b : Fin d) := (hg a b).of_le (show (2 : ℕ∞ω) ≤ 3 by norm_num)
  have hh2 (a b : Fin d) := (hh a b).of_le (show (2 : ℕ∞ω) ≤ 3 by norm_num)
  let H := fun b k e => (affineField g h e x)⁻¹ b k
  let C := fun k a b e => connection (affineField g h e) x k a b
  let E := fun a b => affineSource g h Λ x a b
  let S := fun k b => spatialSource g h Λ x k b j
  let A := fun k b e => H b k e*S k b e
  let B := fun k b a e => (H b k e*C k a b e)*E a j e
  let D := fun k b a e => (H b k e*C k a j e)*E b a e
  let T := fun k b e => A k b e-(∑ a, B k b a e)-(∑ a, D k b a e)
  have hH (b k : Fin d) : ContDiffAt ℂ 2 (H b k) 0 := amplitude_inverse_smooth g h x hdet b k
  have hC (k a b : Fin d) : ContDiffAt ℂ 2 (C k a b) 0 := amplitude_connection_smooth g h x hg2 hh2 hdet k a b
  have hE (a b : Fin d) : ContDiffAt ℂ 2 (E a b) 0 := affineSource_contDiffAt g h Λ x hg2 hh2 hdet a b
  have hS (k b : Fin d) : ContDiffAt ℂ 2 (S k b) 0 := spatialSource_contDiffAt g h Λ x hg hh hdet k b j
  have hA (k b : Fin d) : ContDiffAt ℂ 2 (A k b) 0 := (hH b k).mul (hS k b)
  have hB (k b a : Fin d) : ContDiffAt ℂ 2 (B k b a) 0 := ((hH b k).mul (hC k a b)).mul (hE a j)
  have hD (k b a : Fin d) : ContDiffAt ℂ 2 (D k b a) 0 := ((hH b k).mul (hC k a j)).mul (hE b a)
  have hT (k b : Fin d) : ContDiffAt ℂ 2 (T k b) 0 :=
    ((hA k b).sub (ContDiffAt.sum (fun a _ => hB k b a))).sub (ContDiffAt.sum (fun a _ => hD k b a))
  have hTA (k b : Fin d) : iteratedDeriv 2 (A k b) 0 =
      H b k 0*coordDeriv k (fun y => hessianField g h y b j) x := by
    rw [weighted_second (hH b k) (hS k b) (hS0 k b j) (hS1 k b j)]
    congr 1
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using spatialSource_second g h Λ x hg hh hdet k b j
  have hTB (k b a : Fin d) : iteratedDeriv 2 (B k b a) 0 =
      (H b k 0*C k a b 0)*hessianField g h x a j := by
    rw [weighted_second ((hH b k).mul (hC k a b)) (hE a j) (hE0 a j) (hE1 a j)]
    congr 1
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using affineSource_second g h Λ x hg2 hh2 hdet a j
  have hTD (k b a : Fin d) : iteratedDeriv 2 (D k b a) 0 =
      (H b k 0*C k a j 0)*hessianField g h x b a := by
    rw [weighted_second ((hH b k).mul (hC k a j)) (hE b a) (hE0 b a) (hE1 b a)]
    congr 1
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using affineSource_second g h Λ x hg2 hh2 hdet b a
  have hTT (k b : Fin d) : iteratedDeriv 2 (T k b) 0 =
      H b k 0*coordDeriv k (fun y => hessianField g h y b j) x-
        (∑ a, (H b k 0*C k a b 0)*hessianField g h x a j)-
        (∑ a, (H b k 0*C k a j 0)*hessianField g h x b a) := by
    rw [iteratedDeriv_fun_sub ((hA k b).sub (ContDiffAt.sum (fun a _ => hB k b a)))
      (ContDiffAt.sum (fun a _ => hD k b a)),
      iteratedDeriv_fun_sub (hA k b) (ContDiffAt.sum (fun a _ => hB k b a)),
      iteratedDeriv_fun_sum (fun a _ => hB k b a),iteratedDeriv_fun_sum (fun a _ => hD k b a),hTA]
    simp_rw [hTB,hTD]
  change iteratedDeriv 2 (fun e => ∑ k, ∑ b, T k b e) 0 = _
  rw [iteratedDeriv_fun_sum (fun k _ => ContDiffAt.sum (fun b _ => hT k b))]
  have hzero : affineField g h 0 = g := by funext y; simp [affineField]
  unfold tensorDivergence
  apply Finset.sum_congr rfl
  intro k _
  rw [iteratedDeriv_fun_sum (fun b _ => hT k b)]
  apply Finset.sum_congr rfl
  intro b _
  rw [hTT]
  simp only [H,C,hzero]
  unfold covariantTwo
  simp only [Matrix.sub_apply,Matrix.mul_apply,Matrix.transpose_apply,mul_sub,Finset.mul_sum]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro a _
    change _ = (g x)⁻¹ b k*(connection g x k a b*hessianField g h x a j)
    ring
  · apply Finset.sum_congr rfl
    intro a _
    change _ = (g x)⁻¹ b k*(hessianField g h x b a*connection g x k a j)
    ring

/-- The Hessian of the original cosmological Einstein field is background-conserved when
its original zeroth and first equations hold on a genuine spatial neighborhood. -/
theorem hessian_conservation (g h : Field d) (Λ : ℂ) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 3 (fun y => h y i j) x)
    (hdet : (g x).det ≠ 0)
    (hs : ∀ y i j, g y i j = g y j i)
    (hhs : ∀ y i j, h y i j = h y j i)
    (h0 : ∀ᶠ y in 𝓝 x, ∀ i j, literalEinstein g Λ y i j = 0)
    (h1 : ∀ᶠ y in 𝓝 x, ∀ i j, linearField g h y i j+Λ*h y i j = 0) (j : Fin d) :
    tensorDivergence g (hessianTensor g h) x j = 0 := by
  have hg2 (a b : Fin d) := (hg a b).of_le (show (2 : ℕ∞ω) ≤ 3 by norm_num)
  have hh2 (a b : Fin d) := (hh a b).of_le (show (2 : ℕ∞ω) ≤ 3 by norm_num)
  have hzero : affineField g h 0 = g := by funext y; simp [affineField]
  have hE0 (a b : Fin d) : affineSource g h Λ x a b 0 = 0 := by
    unfold affineSource; rw [hzero]; exact h0.self_of_nhds a b
  have hE1 (a b : Fin d) : deriv (affineSource g h Λ x a b) 0 = 0 := by
    rw [affineSource_first g h Λ x hg2 hh2 hdet]; exact h1.self_of_nhds a b
  have hS0 (k a b : Fin d) : spatialSource g h Λ x k a b 0 = 0 := by
    have he : (fun y => affineSource g h Λ y a b 0) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [h0] with y hy
      unfold affineSource; rw [hzero]; exact hy a b
    unfold spatialSource coordDeriv
    rw [he.fderiv_eq]; simp
  have hS1 (k a b : Fin d) : deriv (spatialSource g h Λ x k a b) 0 = 0 := by
    rw [spatialSource_first g h Λ x hg hh hdet]
    have he : (fun y => linearField g h y a b+Λ*h y a b) =ᶠ[𝓝 x] (fun _ => 0) :=
      h1.mono (fun _ hy => hy a b)
    unfold coordDeriv
    rw [he.fderiv_eq]; simp
  have hd : Continuous (fun e => (affineField g h e x).det) := by
    simp only [Matrix.det_apply',affineField,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]; fun_prop
  have hn : (affineField g h 0 x).det ≠ 0 := by rw [hzero]; exact hdet
  have hc : amplitudeDivergence g h Λ x j =ᶠ[𝓝 0] (fun _ => 0) := by
    filter_upwards [hd.continuousAt.eventually_ne hn] with e he
    rw [amplitudeDivergence_eq]
    apply literalEinstein_divergence (affineField g h e) Λ x
      (fun a b => (hg a b).add (contDiffAt_const.mul (hh a b))) he
    intro y a b
    change g y a b+e*h y a b = g y b a+e*h y b a
    rw [hs,hhs]
  have hz : iteratedDeriv 2 (amplitudeDivergence g h Λ x j) 0 = 0 := by
    simp only [iteratedDeriv_succ,iteratedDeriv_zero]
    rw [hc.deriv.deriv_eq]
    simp
  rw [amplitudeDivergence_second g h Λ x hg hh hdet hE0 hE1 hS0 hS1] at hz
  exact hz

/-- Covariant divergence commutes with a fixed scalar on actual differentiable tensor fields. -/
theorem tensorDivergence_const_smul (g S : Field d) (x : Fin d → ℝ)
    (hS : ∀ i j, DifferentiableAt ℝ (fun y => S y i j) x) (c : ℂ) (j : Fin d) :
    tensorDivergence g (fun y => c • S y) x j = c*tensorDivergence g S x j := by
  have hZ (k : Fin d) : covariantTwo (connection g) (fun _ => 0) x k = 0 := by
    ext a b
    simp [covariantTwo,matrixPartial,coordDeriv]
  have hC (k : Fin d) : covariantTwo (connection g) (fun y => c • S y) x k =
      c • covariantTwo (connection g) S x k := by
    have hv := covariantTwo_add_smul (connection g) (fun _ => 0) S (fun _ => c) x
      (fun _ _ => differentiableAt_const 0) hS (differentiableAt_const c) k
    have hc : coordDeriv k (fun _ : Fin d → ℝ => c) x = 0 := by simp [coordDeriv]
    rw [hZ,hc] at hv
    simpa using hv
  unfold tensorDivergence
  simp_rw [hC]
  simp only [Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro b _
  ring

end
end GaloisForLFunctions.HTGeometry.ComplexMetricField
