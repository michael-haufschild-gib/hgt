import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix

/-! # Isometric regrouping of a square-summable coordinate product

Grouping a scalar `ℓ²(I × J)` history into `ℓ²(J)` blocks preserves the
complete norm. Neither index set needs to be finite.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

private theorem lp_two_summable_sq {I : Type*} {E : I → Type*}
    [∀ i, NormedAddCommGroup (E i)] (f : lp E 2) : Summable (fun i => ‖f i‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.memℓp f).summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)

private theorem lp_two_norm_sq {I : Type*} {E : I → Type*}
    [∀ i, NormedAddCommGroup (E i)] (f : lp E 2) : ‖f‖ ^ 2 = ∑' i, ‖f i‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) f

variable {I J : Type*}

private def curryRow (f : lp (fun _ : I × J => ℂ) 2) (i : I) : lp (fun _ : J => ℂ) 2 :=
  ⟨fun j => f (i, j), HilbertSchmidt.memℓp_of_sq ((HilbertSchmidt.summable_coe_sq f).prod_factor i)⟩

private theorem curry_mem (f : lp (fun _ : I × J => ℂ) 2) : Memℓp (curryRow f) 2 := by
  apply memℓp_gen
  have h := (HilbertSchmidt.summable_coe_sq f).prod
  have he (i : I) : ‖curryRow f i‖ ^ (2 : ℝ) = ∑' j, ‖f (i, j)‖ ^ 2 := by
    rw [Real.rpow_two, HilbertSchmidt.lp_norm_sq_eq]
    rfl
  simpa only [ENNReal.toReal_ofNat, he] using h

private theorem uncurry_mem (f : lp (fun _ : I => lp (fun _ : J => ℂ) 2) 2) :
    Memℓp (fun p : I × J => f p.1 p.2) 2 := by
  apply HilbertSchmidt.memℓp_of_sq
  apply (summable_prod_of_nonneg (fun p : I × J => sq_nonneg ‖f p.1 p.2‖)).mpr
  refine ⟨fun i => HilbertSchmidt.summable_coe_sq (f i), ?_⟩
  simpa only [← HilbertSchmidt.lp_norm_sq_eq] using lp_two_summable_sq f

/-- Infinite coordinate blocks are an exact Hilbert-space regrouping, with no energy loss. -/
def lpTwoCurry : lp (fun _ : I × J => ℂ) 2 ≃ₗᵢ[ℂ]
    lp (fun _ : I => lp (fun _ : J => ℂ) 2) 2 where
  toFun f := ⟨curryRow f, curry_mem f⟩
  invFun f := ⟨fun p => f p.1 p.2, uncurry_mem f⟩
  left_inv f := by ext p; rfl
  right_inv f := by ext i j; rfl
  map_add' f g := by ext i j; rfl
  map_smul' c f := by ext i j; rfl
  norm_map' f := by
    have hs := (HilbertSchmidt.summable_coe_sq f).tsum_prod
    have he : ‖(⟨curryRow f, curry_mem f⟩ : lp (fun _ : I => lp (fun _ : J => ℂ) 2) 2)‖ ^ 2 = ‖f‖ ^ 2 := by
      rw [lp_two_norm_sq, HilbertSchmidt.lp_norm_sq_eq]
      simpa only [HilbertSchmidt.lp_norm_sq_eq, curryRow] using hs.symm
    change ‖(⟨curryRow f, curry_mem f⟩ : lp (fun _ : I => lp (fun _ : J => ℂ) 2) 2)‖ = ‖f‖
    nlinarith [norm_nonneg f,
      norm_nonneg (⟨curryRow f, curry_mem f⟩ : lp (fun _ : I => lp (fun _ : J => ℂ) 2) 2)]

@[simp] theorem lpTwoCurry_apply (f : lp (fun _ : I × J => ℂ) 2) (i : I) (j : J) :
    lpTwoCurry f i j = f (i, j) := rfl

@[simp] theorem lpTwoCurry_symm_apply (f : lp (fun _ : I => lp (fun _ : J => ℂ) 2) 2) (p : I × J) :
    lpTwoCurry.symm f p = f p.1 p.2 := rfl

end
end GaloisForLFunctions.HTGeometry
