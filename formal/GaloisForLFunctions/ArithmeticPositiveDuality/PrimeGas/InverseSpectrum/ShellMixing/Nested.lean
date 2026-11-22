import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing.Finite

/-!
# Recovery of shell coordinates from nested experiments

A new shell cannot change the already normalized columns or rows.
Consequently every off-diagonal amplitude vanishes, even for a nonpositive
propagator. Cofinal positive measurements suffice to fix every phase.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open scoped Matrix MatrixOrder ComplexOrder

abbrev Kernel := ℕ → ℕ → ℂ

def corner (K : Kernel) (M : ℕ) : Block M := fun i j => K i.val j.val

def scale (n : ℕ) : ℂ := (Real.sqrt ((n+1:ℕ):ℝ):ℂ)

def phaseKernel (u : ℕ → ℂ) : Kernel := fun i j => if i = j then (scale i)⁻¹*u i else 0

def Test (K : Kernel) (M : ℕ) := (orderSplit (corner K M))ᴴ*orderSplit (corner K M) = 1

private theorem scale_ne (n : ℕ) : scale n ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by exact_mod_cast Nat.succ_pos n)).ne'

private def weighted (K : Kernel) : Kernel := fun i j => scale i*K i j

private theorem root_prefix (K : Kernel) (M : ℕ) : root M*corner K M = corner (weighted K) M := by
  ext i j
  exact Matrix.diagonal_mul _ _ _ _

private theorem test_iff (K : Kernel) (M : ℕ) : Test K M ↔
    (corner (weighted K) M)ᴴ*corner (weighted K) M = 1 := by rw [Test,order_gram,root_prefix]

private def Columns (A : Kernel) := ∀ M (j : Fin M), ∑ i : Fin M, star (A i.val j.val)*A i.val j.val = 1

/-- Subtracting adjacent column norms isolates the newly admitted entry. -/
private theorem below_zero {A : Kernel} (h : Columns A) {n j : ℕ} (hj : j < n) : A n j = 0 := by
  let k : Fin n := ⟨j,hj⟩
  have H := h (n+1) k.castSucc
  rw [Fin.sum_univ_castSucc] at H
  change (∑ i : Fin n, star (A i.val k.val)*A i.val k.val)+star (A n j)*A n j = 1 at H
  rw [h n k] at H
  have hz : star (A n j)*A n j = 0 := by linear_combination H
  exact (mul_eq_zero.mp hz).elim star_eq_zero.mp id

private theorem columns_and_rows {A : Kernel}
    (h : ∀ M, (corner A M)ᴴ*corner A M = 1) : Columns A ∧ Columns (fun i j => A j i) := by
  constructor
  · intro M j
    have H := congrArg (fun B : Block M => B j j) (h M)
    exact H.trans (Matrix.one_apply_eq j)
  · intro M j
    have H := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin M))).mp (h M)
    have H' := (congrArg (fun B : Block M => B j j) H).trans (Matrix.one_apply_eq j)
    change ∑ i : Fin M, A j.val i.val*star (A j.val i.val) = 1 at H'
    simpa only [mul_comm] using H'

private theorem phase_norm {z : ℂ} : star z*z = 1 ↔ ‖z‖ = 1 := by
  rw [Complex.star_def,← Complex.normSq_eq_conj_mul_self,← Complex.sq_norm,
    ← Complex.ofReal_one,Complex.ofReal_inj]
  constructor
  · intro h
    nlinarith only [norm_nonneg z,h]
  · intro h
    rw [h,one_pow]

private theorem weighted_phase (u : ℕ → ℂ) (M : ℕ) :
    corner (weighted (phaseKernel u)) M = Matrix.diagonal (fun i : Fin M => u i.val) := by
  ext i j
  change scale i.val*(if i.val = j.val then (scale i.val)⁻¹*u i.val else 0) = _
  rw [Matrix.diagonal_apply]
  by_cases h : i = j
  · subst j
    rw [if_pos rfl,if_pos rfl,← mul_assoc,mul_inv_cancel₀ (scale_ne _),one_mul]
  · rw [if_neg (fun he => h (Fin.ext he)),if_neg h,mul_zero]

private theorem diagonal_test {M : ℕ} (u : Fin M → ℂ) :
    (Matrix.diagonal u)ᴴ*Matrix.diagonal u = 1 ↔ ∀ i, ‖u i‖ = 1 := by
  rw [Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
  constructor
  · intro h i
    apply phase_norm.mp
    exact ((Matrix.diagonal_apply_eq _ i).symm.trans (congrArg (fun B : Block M => B i i) h)).trans
      (Matrix.one_apply_eq i)
  · intro h
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    exact phase_norm.mpr (h i)

/-- All successive experiments allow independent shell phases and no mixing. -/
theorem nested_isometries_iff (K : Kernel) :
    (∀ M, Test K M) ↔ ∃ u : ℕ → ℂ, (∀ n, ‖u n‖ = 1) ∧ K = phaseKernel u := by
  constructor
  · intro ht
    let A := weighted K
    have H (M : ℕ) : (corner A M)ᴴ*corner A M = 1 := (test_iff K M).mp (ht M)
    obtain ⟨hc,hr⟩ := columns_and_rows H
    have off {i j : ℕ} (hne : i ≠ j) : A i j = 0 := by
      rcases lt_or_gt_of_ne hne with h|h
      · exact below_zero hr h
      · exact below_zero hc h
    let u (n : ℕ) := A n n
    have hK : K = phaseKernel u := by
      funext i j
      rw [phaseKernel]
      by_cases h : i = j
      · subst j
        rw [if_pos rfl]
        change K i i = (scale i)⁻¹*(scale i*K i i)
        rw [← mul_assoc,inv_mul_cancel₀ (scale_ne _),one_mul]
      · rw [if_neg h]
        exact (mul_eq_zero.mp (off h)).resolve_left (scale_ne i)
    refine ⟨u,fun n => ?_,hK⟩
    have HH := (test_iff K (n+1)).mp (ht (n+1))
    rw [hK,weighted_phase,diagonal_test] at HH
    exact HH (Fin.last n)
  · rintro ⟨u,hu,rfl⟩ M
    rw [test_iff,weighted_phase,diagonal_test]
    exact fun i => hu i.val

theorem prefix_critical (M : ℕ) : corner (phaseKernel 1) M = critical M := by
  ext i j
  change (if i.val = j.val then (scale i.val)⁻¹*1 else 0) = _
  rw [critical,Matrix.diagonal_apply,Complex.ofReal_inv,mul_one]
  by_cases h : i = j
  · subst j
    rw [if_pos rfl,if_pos rfl]; rfl
  · rw [if_neg (fun he => h (Fin.ext he)),if_neg h]

/-- Positive conserving measurements along any unbounded set of cutoffs determine every entry. -/
theorem cofinal_positive_iff (K : Kernel) :
    (∀ m, ∃ M ≥ m, (corner K M).PosSemidef ∧ Test K M) ↔ K = phaseKernel 1 := by
  constructor
  · intro h
    funext i j
    obtain ⟨M,hM,hp,ht⟩ := h (max i j+1)
    let a : Fin M := ⟨i,by omega⟩
    let b : Fin M := ⟨j,by omega⟩
    have he := ((positive_order_isometry_iff (corner K M)).mp ⟨hp,ht⟩).trans (prefix_critical M).symm
    exact congrArg (fun B : Block M => B a b) he
  · rintro rfl m
    refine ⟨m,le_rfl,(positive_order_isometry_iff _).mpr (prefix_critical m)⟩

#print axioms nested_isometries_iff
#print axioms cofinal_positive_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
