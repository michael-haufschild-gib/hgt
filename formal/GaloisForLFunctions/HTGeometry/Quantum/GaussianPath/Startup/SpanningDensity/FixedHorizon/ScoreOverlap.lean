import GaloisForLFunctions.HTGeometry.PhaseOrbitGradient

/-! # Overlap obstruction from decorrelated Choi tests -/
open scoped InnerProductSpace
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An observable with mean `a` on the first unit vector bounds the
overlap by its fluctuation there and its root second moment on the other
vector. Positive means from independent marked bonds add linearly. -/
theorem overlap_le_residual (x y u v : E) (hs : inner ℂ u y=inner ℂ x v)
    (hx : ‖x‖=1) (hy : ‖y‖=1) {a : ℝ} (ha : 0 < a) :
    ‖inner ℂ x y‖ ≤ (‖u-(a:ℂ) • x‖+‖v‖)/a := by
  have he : (a:ℂ)*inner ℂ x y = inner ℂ x v-inner ℂ (u-(a:ℂ) • x) y := by
    rw [inner_sub_left,inner_smul_left,Complex.conj_ofReal,hs,sub_sub_cancel]
  apply (le_div_iff₀ ha).mpr
  have h1 := norm_inner_le_norm (𝕜:=ℂ) x v
  have h2 := norm_inner_le_norm (𝕜:=ℂ) (u-(a:ℂ) • x) y
  rw [hx,one_mul] at h1
  rw [hy,mul_one] at h2
  calc ‖inner ℂ x y‖*a = ‖(a:ℂ)*inner ℂ x y‖ := by
         rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha,mul_comm]
       _ = _ := congrArg norm he
       _ ≤ _ := (norm_sub_le ..).trans ((add_le_add h1 h2).trans_eq (add_comm ..))

/-- Replacing each centered evolution test by a nearby orthogonal vector
costs its individual error divided by the common signal strength. Only
the local tests need approximating, even when their number grows. -/
theorem overlap_of_localized_tests {m : ℕ} (hm : 0 < m) (x y : E)
    (u v z : Fin m → E) (hs : ∀ i, inner ℂ (u i) y=inner ℂ x (v i))
    (hx : ‖x‖=1) (hy : ‖y‖=1) (a : Fin m → ℝ) {r δ : ℝ} (hr : 0 < r)
    (ha : ∀ i, r ≤ a i) (hlocal : ∀ i, ‖u i-(a i:ℂ) • x-z i‖ ≤ δ)
    (hz : ∀ i, ‖z i‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1)
    (hz' : ∀ i j, i≠j → inner ℂ (z i) (z j)=0)
    (hv' : ∀ i j, i≠j → inner ℂ (v i) (v j)=0) :
    (m:ℝ)*r*‖inner ℂ x y‖ ≤ 2*Real.sqrt m+m*δ := by
  classical
  let A := ∑ i, a i
  have hA : (m:ℝ)*r ≤ A := by simpa [A] using Finset.sum_le_sum (s:=Finset.univ) (fun i _ => ha i)
  have hpos := (mul_pos (Nat.cast_pos.mpr hm) hr).trans_le hA
  have hsum : inner ℂ (∑ i, u i) y=inner ℂ x (∑ i, v i) := by
    rw [sum_inner,inner_sum]
    exact Finset.sum_congr rfl fun i _ => hs i
  have bound (w : Fin m → E) (hw : ∀ i, ‖w i‖ ≤ 1)
      (ho : ∀ i j, i≠j → inner ℂ (w i) (w j)=0) : ‖∑ i, w i‖ ≤ Real.sqrt m := by
    apply Real.le_sqrt_of_sq_le
    rw [norm_sq_sum_of_orthogonal ho]
    simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
      (sq_le_sq₀ (norm_nonneg (w i)) zero_le_one).mpr (hw i))
  let e (i : Fin m) := u i-(a i:ℂ) • x-z i
  have he : ‖∑ i, e i‖ ≤ (m:ℝ)*δ := (norm_sum_le _ _).trans (by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
      Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hlocal i))
  have hsplit : (∑ i, u i)-(A:ℂ) • x=(∑ i, e i)+∑ i, z i := by
    simp only [e,A,Complex.ofReal_sum,Finset.sum_smul,Finset.sum_sub_distrib,sub_add_cancel]
  have hres := (le_div_iff₀ hpos).mp (overlap_le_residual x y _ _ hsum hx hy hpos)
  rw [hsplit] at hres
  calc (m:ℝ)*r*‖inner ℂ x y‖ ≤ A*‖inner ℂ x y‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg _)
       _ ≤ _ := by linarith only [hres,norm_add_le (∑ i, e i) (∑ i, z i),he,bound z hz hz',bound v hv hv']

/-- Orthogonal centered tests on the evolution and orthogonal uncentered
tests on the circuit turn a common positive signal into an overlap bound. -/
theorem overlap_of_orthogonal_tests {m : ℕ} (hm : 0 < m) (x y : E) (u v : Fin m → E)
    (hs : ∀ i, inner ℂ (u i) y=inner ℂ x (v i)) (hx : ‖x‖=1) (hy : ‖y‖=1)
    (a : Fin m → ℝ) {r : ℝ} (hr : 0 < r) (ha : ∀ i, r ≤ a i)
    (hx₁ : ∀ i, ‖u i-(a i:ℂ) • x‖ ≤ 1) (hy₁ : ∀ i, ‖v i‖ ≤ 1)
    (hx₂ : ∀ i j, i≠j → inner ℂ (u i-(a i:ℂ) • x) (u j-(a j:ℂ) • x)=0)
    (hy₂ : ∀ i j, i≠j → inner ℂ (v i) (v j)=0) :
    (m:ℝ)*r*‖inner ℂ x y‖ ≤ 2*Real.sqrt m := by
  simpa only [mul_zero,add_zero] using
    overlap_of_localized_tests hm x y u v (fun i => u i-(a i:ℂ) • x)
      hs hx hy a hr ha (δ:=0) (fun i => by rw [sub_self,norm_zero]) hx₁ hy₁ hx₂ hy₂

#print axioms overlap_of_localized_tests
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
