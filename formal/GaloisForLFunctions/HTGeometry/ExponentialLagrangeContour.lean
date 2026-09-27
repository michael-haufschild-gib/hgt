import GaloisForLFunctions.HTGeometry.LagrangeRectangleContour

/-!
# Lagrange interpolation at exponential nodes through a rectangle contour

For `κ ≠ 0` and nodes `vᵢ`, interpolate in the variable `w = e^{iκz}` at `ωᵢ = e^{iκvᵢ}`. When the
data are values of a function `G` holomorphic near a rectangle `R`, the barycentric part carried
by the nodes inside `R` is a contour integral over `∂R` in the `z`-plane
(`sum_expNodalWeight_inside_eq_rectangleIntegral`):

`Σ_{vᵢ ∈ R} wᵢ (e^{iκx} - ωᵢ)⁻¹ G(vᵢ) = (2πi)⁻¹ ∮_{∂R} G(t) iκ e^{iκt} / ((e^{iκx} - e^{iκt}) Ω(e^{iκt})) dt`.

The residue of `iκ e^{iκt}/(e^{iκt} - ωᵢ)` at `vᵢ` is `1`, computed through `dslope` without any
removable-singularity argument (`rectangleIntegral'_expNode_eq`). As in the polynomial case, only
`|Ω(e^{iκt})|` on `∂R` enters the size of the interpolant, never the separation of the nodes.

The coefficients of the interpolating polynomial are bounded by its supremum on the unit circle,
i.e. on the real line `x ↦ e^{iκx}` (`norm_coeff_le_of_forall_real`).
-/

open Complex Set Filter Topology Polynomial Lagrange
open scoped Interval

noncomputable section

namespace HTGeometry

/-! ### One exponential node -/

/-- For `κ ≠ 0`, `H` holomorphic on an open `U ⊇ R`, and `v` interior to `R` the only solution in
`R` of `e^{iκt} = e^{iκv}`,
`(2πi)⁻¹ ∮_{∂R} H(t) iκ e^{iκt} / (e^{iκt} - e^{iκv}) dt = H(v)`. -/
theorem rectangleIntegral'_expNode_eq {H : ℂ → ℂ} {z w v : ℂ} {U : Set ℂ} {κ : ℝ} (hκ : κ ≠ 0)
    (hU : IsOpen U) (hRU : Rectangle z w ⊆ U) (hH : DifferentiableOn ℂ H U)
    (hzw : z.re ≤ w.re) (hzw' : z.im ≤ w.im) (hv : Rectangle z w ∈ 𝓝 v)
    (huniq : ∀ t ∈ Rectangle z w, Complex.exp (I * t * κ) = Complex.exp (I * v * κ) → t = v) :
    RectangleIntegral' (fun t => H t * (I * κ * Complex.exp (I * t * κ)) /
      (Complex.exp (I * t * κ) - Complex.exp (I * v * κ))) z w = H v := by
  set E : ℂ → ℂ := fun t => Complex.exp (I * t * κ) - Complex.exp (I * v * κ) with hE
  have hEd : Differentiable ℂ E := by simp only [hE]; fun_prop
  have hEv : E v = 0 := by simp [hE]
  set D : ℂ → ℂ := dslope E v with hD
  have hvU : U ∈ 𝓝 v := Filter.mem_of_superset hv hRU
  have hDd : DifferentiableOn ℂ D U := (differentiableOn_dslope hvU).mpr hEd.differentiableOn
  have hDv : D v = I * κ * Complex.exp (I * v * κ) := by
    simp only [hD, dslope_same]
    have h : HasDerivAt E (Complex.exp (I * v * κ) * (I * κ)) v := by
      have h1 : HasDerivAt (fun t : ℂ => I * t * κ) (I * κ) v := by
        simpa using ((hasDerivAt_id v).const_mul I).mul_const (κ : ℂ)
      have h2 := (h1.cexp).sub_const (Complex.exp (I * v * κ))
      simpa [hE] using h2
    rw [h.deriv]; ring
  have hκC : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ
  have hDv0 : D v ≠ 0 := by
    rw [hDv]; exact mul_ne_zero (mul_ne_zero I_ne_zero hκC) (Complex.exp_ne_zero _)
  have hDt : ∀ t, t ≠ v → D t * (t - v) = E t := by
    intro t ht
    simp only [hD, dslope_of_ne _ ht, slope_def_field, hEv, sub_zero]
    field_simp [sub_ne_zero.mpr ht]
  have hDne : ∀ t ∈ Rectangle z w, D t ≠ 0 := by
    intro t ht
    by_cases htv : t = v
    · rw [htv]; exact hDv0
    · intro h0
      have := hDt t htv
      rw [h0, zero_mul] at this
      exact htv (huniq t ht (sub_eq_zero.mp (by simp only [hE] at this; exact this.symm)))
  set U' : Set ℂ := U ∩ D ⁻¹' {0}ᶜ with hU'
  have hU'o : IsOpen U' := hDd.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
  have hRU' : Rectangle z w ⊆ U' := fun t ht => ⟨hRU ht, hDne t ht⟩
  set h : ℂ → ℂ := fun t => H t * (I * κ * Complex.exp (I * t * κ)) / D t with hh
  have hhd : DifferentiableOn ℂ h U' := by
    refine ((hH.mono inter_subset_left).mul (by fun_prop)).div (hDd.mono inter_subset_left)
      fun t ht => ht.2
  have heq : Set.EqOn (fun t => H t * (I * κ * Complex.exp (I * t * κ)) /
      (Complex.exp (I * t * κ) - Complex.exp (I * v * κ))) (fun t => h t / (t - v))
      (RectangleBorder z w) := by
    intro t ht
    have htv : t ≠ v := fun e => not_mem_rectangleBorder_of_rectangle_mem_nhds hv (e ▸ ht)
    have hE' := hDt t htv
    simp only [hh]
    rw [div_div, hE']
  rw [RectangleIntegral'_congr heq, rectangleIntegral'_div_sub_eq hRU' hhd hzw hzw' hv]
  simp only [hh, hDv]
  field_simp

/-- If `e^{iκt} ≠ c` on `R`, then `∮_{∂R} H(t) iκ e^{iκt} / (e^{iκt} - c) dt = 0`. -/
theorem rectangleIntegral_expNode_eq_zero {H : ℂ → ℂ} {z w c : ℂ} {U : Set ℂ} {κ : ℝ}
    (hRU : Rectangle z w ⊆ U) (hH : DifferentiableOn ℂ H U)
    (hout : ∀ t ∈ Rectangle z w, Complex.exp (I * t * κ) ≠ c) :
    RectangleIntegral (fun t => H t * (I * κ * Complex.exp (I * t * κ)) /
      (Complex.exp (I * t * κ) - c)) z w = 0 := by
  set U' : Set ℂ := U ∩ (fun t => Complex.exp (I * t * κ)) ⁻¹' {c}ᶜ with hU'
  have hd : DifferentiableOn ℂ (fun t => H t * (I * κ * Complex.exp (I * t * κ)) /
      (Complex.exp (I * t * κ) - c)) U' := by
    refine ((hH.mono inter_subset_left).mul (by fun_prop)).div (by fun_prop) fun t ht => ?_
    exact sub_ne_zero.mpr ht.2
  exact HolomorphicOn.vanishesOnRectangle hd fun t ht => ⟨hRU ht, hout t ht⟩

/-! ### The contour form of the exponential barycentric sum -/

open scoped Classical in
/-- **Contour form of the exponential barycentric sum.**  Let `ωᵢ = e^{iκvᵢ}` be distinct, each
node `vᵢ` either interior to the rectangle `R` or outside it, and suppose `e^{iκt} = ωᵢ` has no
solution in `R` other than `vᵢ`.  For `G` holomorphic on an open `U ⊇ R` and a point `x` with
`e^{iκx} ∉ e^{iκR}`,
`Σ_{vᵢ ∈ R} wᵢ (e^{iκx} - ωᵢ)⁻¹ G(vᵢ) = (2πi)⁻¹ ∮_{∂R} G(t) iκ e^{iκt} / ((e^{iκx} - e^{iκt}) Ω(e^{iκt})) dt`,
with `wᵢ` the nodal weights and `Ω` the nodal polynomial of the `ωᵢ`. -/
theorem sum_expNodalWeight_inside_eq_rectangleIntegral {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {v : ι → ℂ} {κ : ℝ} (hκ : κ ≠ 0)
    (hinj : Set.InjOn (fun i => Complex.exp (I * v i * κ)) s) (hs : s.Nonempty) {G : ℂ → ℂ}
    {z w x : ℂ} {U : Set ℂ} (hU : IsOpen U) (hRU : Rectangle z w ⊆ U) (hG : DifferentiableOn ℂ G U)
    (hzw : z.re ≤ w.re) (hzw' : z.im ≤ w.im)
    (hnode : ∀ i ∈ s, Rectangle z w ∈ 𝓝 (v i) ∨ v i ∉ Rectangle z w)
    (huniq : ∀ i ∈ s, ∀ t ∈ Rectangle z w,
      Complex.exp (I * t * κ) = Complex.exp (I * v i * κ) → t = v i)
    (hx : ∀ t ∈ Rectangle z w, Complex.exp (I * t * κ) ≠ x) :
    ∑ i ∈ s.filter (fun i => v i ∈ Rectangle z w),
        nodalWeight s (fun i => Complex.exp (I * v i * κ)) i *
          (x - Complex.exp (I * v i * κ))⁻¹ * G (v i)
      = RectangleIntegral' (fun t => G t * (I * κ * Complex.exp (I * t * κ)) /
          ((x - Complex.exp (I * t * κ)) *
            eval (Complex.exp (I * t * κ)) (nodal s (fun i => Complex.exp (I * v i * κ))))) z w := by
  classical
  set ω : ι → ℂ := fun i => Complex.exp (I * v i * κ) with hω
  set R := Rectangle z w
  set U' := U ∩ (fun t => Complex.exp (I * t * κ)) ⁻¹' {x}ᶜ with hU'
  have hU'o : IsOpen U' :=
    hU.inter ((by fun_prop : Continuous fun t : ℂ => Complex.exp (I * t * κ)).isOpen_preimage _
        isOpen_compl_singleton)
  have hRU' : R ⊆ U' := fun t ht => ⟨hRU ht, hx t ht⟩
  set H : ℂ → ℂ := fun t => G t / (x - Complex.exp (I * t * κ)) with hH
  have hHd : DifferentiableOn ℂ H U' := by
    refine (hG.mono inter_subset_left).div (by fun_prop) fun t ht => ?_
    exact sub_ne_zero.mpr fun e => ht.2 e.symm
  -- border points are not solutions
  have hborder : ∀ t ∈ RectangleBorder z w, ∀ i ∈ s, Complex.exp (I * t * κ) ≠ ω i := by
    intro t ht i hi e
    have htR : t ∈ R := rectangleBorder_subset_rectangle z w ht
    have htv := huniq i hi t htR e
    rcases hnode i hi with h1 | h1
    · exact not_mem_rectangleBorder_of_rectangle_mem_nhds h1 (htv ▸ ht)
    · exact h1 (htv ▸ htR)
  have heq : Set.EqOn (fun t => G t * (I * κ * Complex.exp (I * t * κ)) /
      ((x - Complex.exp (I * t * κ)) * eval (Complex.exp (I * t * κ)) (nodal s ω)))
      (fun t => ∑ i ∈ s, nodalWeight s ω i *
        (H t * (I * κ * Complex.exp (I * t * κ)) / (Complex.exp (I * t * κ) - ω i)))
      (RectangleBorder z w) := by
    intro t ht
    have hpf := sum_nodalWeight_mul_inv_sub_eq_inv_nodal hinj hs (hborder t ht)
    simp only [hH]
    have e1 : ∀ i ∈ s, nodalWeight s ω i * (G t / (x - Complex.exp (I * t * κ)) *
        (I * κ * Complex.exp (I * t * κ)) / (Complex.exp (I * t * κ) - ω i)) =
        (nodalWeight s ω i * (Complex.exp (I * t * κ) - ω i)⁻¹) *
          (G t * (I * κ * Complex.exp (I * t * κ)) / (x - Complex.exp (I * t * κ))) := by
      intro i _; ring
    rw [Finset.sum_congr rfl e1, ← Finset.sum_mul, hpf]
    field_simp
  have hint : ∀ i ∈ s, RectangleBorderIntegrable (fun t => nodalWeight s ω i *
      (H t * (I * κ * Complex.exp (I * t * κ)) / (Complex.exp (I * t * κ) - ω i))) z w := by
    intro i hi
    refine ContinuousOn.rectangleBorder_integrable ?_
    refine continuousOn_const.mul ?_
    refine (((hHd.continuousOn).mono ?_).mul (by fun_prop)).div (by fun_prop) fun t ht =>
      sub_ne_zero.mpr (hborder t ht i hi)
    exact (rectangleBorder_subset_rectangle z w).trans hRU'
  rw [RectangleIntegral'_congr heq, RectangleIntegral',
    rectangleIntegral_finsetSum_of_borderIntegrable _ _ _ _ hint, Finset.smul_sum]
  have hterm : ∀ i ∈ s, (1 / (2 * (Real.pi : ℂ) * I)) •
      RectangleIntegral (fun t => nodalWeight s ω i *
        (H t * (I * κ * Complex.exp (I * t * κ)) / (Complex.exp (I * t * κ) - ω i))) z w =
      if v i ∈ R then nodalWeight s ω i * (x - ω i)⁻¹ * G (v i) else 0 := by
    intro i hi
    rw [rectangleIntegral_const_mul, smul_eq_mul]
    split_ifs with hin
    · rcases hnode i hi with hint' | hout
      · have := rectangleIntegral'_expNode_eq hκ hU'o hRU' hHd hzw hzw' hint' (huniq i hi)
        rw [RectangleIntegral', smul_eq_mul] at this
        rw [mul_left_comm, this]
        simp only [hH]
        ring
      · exact absurd hin hout
    · have hno : ∀ t ∈ R, Complex.exp (I * t * κ) ≠ ω i := by
        intro t ht e
        exact hin (huniq i hi t ht e ▸ ht)
      rw [rectangleIntegral_expNode_eq_zero hRU' hHd hno, mul_zero, mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const_zero, add_zero]

/-- The size of the contour form: if the integrand is bounded by `M` on `∂R`, the barycentric
sum over the nodes inside `R` is at most `(|Δ re| + |Δ im|) M / π`. -/
theorem norm_rectangleIntegral'_le {f : ℂ → ℂ} {z w : ℂ} {M : ℝ}
    (hM : ∀ t ∈ RectangleBorder z w, ‖f t‖ ≤ M) :
    ‖RectangleIntegral' f z w‖ ≤ (|w.re - z.re| + |w.im - z.im|) * M / Real.pi := by
  rw [RectangleIntegral', norm_smul]
  have h := norm_rectangleIntegral_le hM
  have hc : ‖(1 / (2 * (Real.pi : ℂ) * I))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hc]
  calc 1 / (2 * Real.pi) * ‖RectangleIntegral f z w‖
      ≤ 1 / (2 * Real.pi) * (2 * (|w.re - z.re| + |w.im - z.im|) * M) := by
        gcongr
    _ = (|w.re - z.re| + |w.im - z.im|) * M / Real.pi := by
        field_simp

/-! ### Coefficients on the unit circle -/

theorem integral_cexp_int_mul_I (n : ℤ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp ((n : ℂ) * θ * I) =
      if n = 0 then (2 * Real.pi : ℂ) else 0 := by
  split_ifs with hn
  · subst hn; simp
  · have hc : (n : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hn) I_ne_zero
    have h := integral_exp_mul_complex (a := 0) (b := 2 * Real.pi) hc
    have e : ∀ θ : ℝ, Complex.exp ((n : ℂ) * θ * I) = Complex.exp ((n : ℂ) * I * θ) := by
      intro θ; ring_nf
    simp_rw [e]
    rw [h]
    have h1 : Complex.exp ((n : ℂ) * I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      have := Complex.exp_int_mul_two_pi_mul_I n
      rw [← this]; push_cast; ring_nf
    rw [h1]; simp

/-- **Coefficients of a polynomial are bounded by its supremum on the unit circle**, here
parametrized as `x ↦ e^{iκx}` on the real line. -/
theorem norm_coeff_le_of_forall_real (Q : ℂ[X]) {κ : ℝ} (hκ : 0 < κ) {M : ℝ}
    (hM : ∀ x : ℝ, ‖Q.eval (Complex.exp (I * x * κ))‖ ≤ M) (k : ℕ) : ‖Q.coeff k‖ ≤ M := by
  have hM' : ∀ θ : ℝ, ‖Q.eval (Complex.exp (θ * I))‖ ≤ M := by
    intro θ
    have := hM (θ / κ)
    have e : I * ((θ / κ : ℝ) : ℂ) * κ = θ * I := by
      have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
      push_cast; field_simp
    rwa [e] at this
  set N := Q.natDegree + 1
  have hexpand : ∀ θ : ℝ, Q.eval (Complex.exp (θ * I)) * Complex.exp (-((k : ℂ) * θ * I)) =
      ∑ j ∈ Finset.range N, Q.coeff j * Complex.exp ((((j : ℤ) - k : ℤ) : ℂ) * θ * I) := by
    intro θ
    rw [eval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 2
    push_cast; ring
  have hint : ∫ θ in (0 : ℝ)..(2 * Real.pi),
      Q.eval (Complex.exp (θ * I)) * Complex.exp (-((k : ℂ) * θ * I)) =
      (2 * Real.pi : ℂ) * Q.coeff k := by
    simp_rw [hexpand]
    rw [intervalIntegral.integral_finsetSum (fun j _ => by
      apply Continuous.intervalIntegrable; fun_prop)]
    simp_rw [intervalIntegral.integral_const_mul, integral_cexp_int_mul_I]
    by_cases hk : k < N
    · rw [Finset.sum_eq_single k]
      · simp; ring
      · intro j _ hj
        have : ((j : ℤ) - k : ℤ) ≠ 0 := by omega
        simp [this]
      · intro h; exact absurd (Finset.mem_range.mpr hk) h
    · have hc : Q.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hc, mul_zero]
      refine Finset.sum_eq_zero fun j hj => ?_
      have : ((j : ℤ) - k : ℤ) ≠ 0 := by have := Finset.mem_range.mp hj; omega
      simp [this]
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hcoef : Q.coeff k = (1 / (2 * Real.pi : ℂ)) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
      Q.eval (Complex.exp (θ * I)) * Complex.exp (-((k : ℂ) * θ * I)) := by
    rw [hint]; field_simp
  rw [hcoef, norm_mul]
  have hb : ‖∫ θ in (0 : ℝ)..(2 * Real.pi),
      Q.eval (Complex.exp (θ * I)) * Complex.exp (-((k : ℂ) * θ * I))‖ ≤ M * |2 * Real.pi - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => ?_
    rw [norm_mul]
    have h1 : ‖Complex.exp (-((k : ℂ) * θ * I))‖ = 1 := by
      rw [Complex.norm_exp]; simp
    rw [h1, mul_one]; exact hM' θ
  have hn : ‖(1 / (2 * Real.pi : ℂ))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [hn]
  rw [sub_zero, abs_of_pos hpi] at hb
  calc 1 / (2 * Real.pi) * ‖∫ θ in (0 : ℝ)..(2 * Real.pi),
        Q.eval (Complex.exp (θ * I)) * Complex.exp (-((k : ℂ) * θ * I))‖
      ≤ 1 / (2 * Real.pi) * (M * (2 * Real.pi)) := by gcongr
    _ = M := by field_simp

end HTGeometry
