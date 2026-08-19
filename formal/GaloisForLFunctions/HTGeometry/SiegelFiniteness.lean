import GaloisForLFunctions.HTGeometry.SiegelIsometryVanishing

/-!
# Siegel's finiteness property

Two Siegel-reduced forms in one integral orbit have comparable Jacobi diagonals, so the weighted
isometry between them vanishes wherever the weights separate and is bounded where they do not.  The
conjugating matrix is the isometry between two bounded triangular factors, hence bounded; being
integral, it ranges over a finite set.

Together with the covering property this is the Siegel property of the reduction domain, which is
what makes the arithmetic group act with finitely many identifications on it.

* `exists_gamma_bound` : **the conjugating matrix is bounded.**
* `finite_intMatrix_bounded` : bounded integral matrices are finite in number.
* `siegel_finiteness` : **only finitely many integral matrices identify two Siegel-reduced forms.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- **The conjugating matrix between two Siegel-reduced forms in one orbit is bounded.** -/
theorem exists_gamma_bound (n : ℕ) (t u : ℝ) (ht : 1 ≤ t) :
    ∃ B : ℝ, ∀ (J J' : JacobiData n), J.IsSiegel t u → J'.IsSiegel t u →
      ∀ γ : Matrix (Fin n) (Fin n) ℝ, IsIntUnimodular γ → J'.form = γᵀ * J.form * γ →
      ∀ k i : Fin n, |γ k i| ≤ B := by
  classical
  obtain ⟨c, hc, hquasi⟩ := exists_quasiDiagonal n t u ht
  obtain ⟨Cst, hCst, hcmp⟩ := exists_d_comparable_of_siegel n t u ht
  obtain ⟨Cu₀, hCu₀⟩ := exists_unipotent_inv_bound n u
  set Cu : ℝ := max Cu₀ 0 with hCudef
  have hCu0 : (0 : ℝ) ≤ Cu := le_max_right _ _
  have hCu : ∀ U ∈ unipotentBall n u, ∀ i j, |U⁻¹ i j| ≤ Cu :=
    fun U hU i j => le_trans (hCu₀ U hU i j) (le_max_left _ _)
  have htn : (0 : ℝ) < t ^ n := pow_pos (lt_of_lt_of_le zero_lt_one ht) n
  set Kn : ℝ := (n : ℝ) * u ^ 2 * t ^ n with hKndef
  have hKn0 : (0 : ℝ) ≤ Kn := by positivity
  set R : ℝ := Cst * Kn / c with hRdef
  have hR0 : (0 : ℝ) ≤ R := by positivity
  set T : ℝ := t ^ n * (R * t ^ n) with hTdef
  have hT0 : (0 : ℝ) ≤ T := by positivity
  set Bm : ℝ := Real.sqrt (Cst * T) with hBmdef
  refine ⟨(n : ℝ) * ((n : ℝ) * (Cu * Bm) * u), ?_⟩
  intro J J' hS hS' γ hγ hform k i
  obtain ⟨δ, hδu, hγδ, hδγ⟩ := hγ.exists_inv
  obtain ⟨h, hhu, hh⟩ := id hδu
  have hrev : J.form = δᵀ * J'.form * δ := by
    have h1 : δᵀ * J'.form * δ = (γ * δ)ᵀ * J.form * (γ * δ) := by
      rw [hform, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    rw [h1, hγδ, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  have hUunit : IsUnit (J.U).det := by rw [J.det_eq_one]; exact isUnit_one
  have hU'unit : IsUnit (J'.U).det := by rw [J'.det_eq_one]; exact isUnit_one
  set M : Matrix (Fin n) (Fin n) ℝ := J.U * γ * (J'.U)⁻¹ with hMdef
  set P : Matrix (Fin n) (Fin n) ℝ := J'.U * δ * (J.U)⁻¹ with hPdef
  have hiso : Mᵀ * Matrix.diagonal J.d * M = Matrix.diagonal J'.d := weightedIsometry_congr hform
  have hMP : M * P = 1 := by
    rw [hMdef, hPdef]
    calc J.U * γ * (J'.U)⁻¹ * (J'.U * δ * (J.U)⁻¹)
        = J.U * γ * ((J'.U)⁻¹ * J'.U) * δ * (J.U)⁻¹ := by simp only [Matrix.mul_assoc]
      _ = J.U * γ * δ * (J.U)⁻¹ := by
          rw [Matrix.nonsing_inv_mul _ hU'unit, Matrix.mul_one]
      _ = 1 := by
          rw [Matrix.mul_assoc J.U γ δ, hγδ, Matrix.mul_one, Matrix.mul_nonsing_inv _ hUunit]
  have hPeq : isometryInv J J' M = P := isometryInv_eq hiso hMP
  -- the integrality threshold for the inverse
  have hδcond : ∀ a b : Fin n, δ a b ≠ 0 → J.d a ≤ R * J.d b := by
    intro a b hne
    have hentry : c * J'.d a ≤ Kn * J.d b :=
      d_le_of_entry_ne_zero_of_siegel ht hc hS hrev (hquasi J' hS') hh hne
    have hda : J.d a ≤ Cst * J'.d a := hcmp J J' hS hS' γ hγ hform a
    have hstep : c * J.d a ≤ Cst * (c * J'.d a) := by
      have := mul_le_mul_of_nonneg_left hda hc.le
      nlinarith [this]
    have : c * J.d a ≤ Cst * (Kn * J.d b) :=
      le_trans hstep (mul_le_mul_of_nonneg_left hentry hCst.le)
    rw [hRdef]
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    nlinarith [this]
  -- the isometry is bounded
  have hMbound : ∀ p q : Fin n, |M p q| ≤ Bm := by
    intro p q
    have hdq : (0 : ℝ) < J.d p := J.pos p
    by_cases hbig : t ^ n * (R * (t ^ n * J.d p)) < J.d q
    · have hzero : P q p = 0 := triangular_conjugate_entry_zero ht hR0 hS hδcond hbig
      have hval : J.d p * M p q / J'.d q = 0 := by
        have := congrFun (congrFun hPeq q) p
        rw [hzero] at this
        exact this
      have hMz : M p q = 0 := by
        rcases div_eq_zero_iff.1 hval with h1 | h1
        · rcases mul_eq_zero.1 h1 with h2 | h2
          · exact absurd h2 (ne_of_gt hdq)
          · exact h2
        · exact absurd h1 (ne_of_gt (J'.pos q))
      rw [hMz, abs_zero, hBmdef]
      positivity
    · have hle : J.d q ≤ T * J.d p := by
        have := not_lt.1 hbig
        rw [hTdef]
        nlinarith [this]
      have h1 : J.d p * (M p q) ^ 2 ≤ J'.d q := weightedIsometry_entry_le hiso p q
      have h2 : J'.d q ≤ Cst * J.d q := hcmp J' J hS' hS δ hδu hrev q
      have h3 : J.d p * (M p q) ^ 2 ≤ Cst * (T * J.d p) := by
        refine le_trans h1 (le_trans h2 ?_)
        exact mul_le_mul_of_nonneg_left hle hCst.le
      have h4 : (M p q) ^ 2 ≤ Cst * T := by
        have hmul : J.d p * (M p q) ^ 2 ≤ J.d p * (Cst * T) := by
          rw [show J.d p * (Cst * T) = Cst * (T * J.d p) from by ring]
          exact h3
        exact le_of_mul_le_mul_left hmul hdq
      have h5 : Real.sqrt ((M p q) ^ 2) ≤ Real.sqrt (Cst * T) := Real.sqrt_le_sqrt h4
      rwa [Real.sqrt_sq_eq_abs] at h5
  -- transport the bound to γ
  have hUball : J.U ∈ unipotentBall n u := ⟨J.upper, J.unit, hS.2⟩
  have hUinv : ∀ p q : Fin n, |(J.U)⁻¹ p q| ≤ Cu := hCu J.U hUball
  have hgamma : γ = (J.U)⁻¹ * M * J'.U := by
    rw [hMdef]
    calc γ = ((J.U)⁻¹ * J.U) * γ * ((J'.U)⁻¹ * J'.U) := by
          rw [Matrix.nonsing_inv_mul _ hUunit, Matrix.nonsing_inv_mul _ hU'unit,
            Matrix.one_mul, Matrix.mul_one]
      _ = (J.U)⁻¹ * (J.U * γ * (J'.U)⁻¹) * J'.U := by simp only [Matrix.mul_assoc]
  rw [hgamma]
  exact entry_abs_mul_le (fun p q => entry_abs_mul_le hUinv hMbound p q) hS'.2 k i

/-- Integer matrices with bounded entries form a finite set. -/
theorem finite_intMatrix_bounded (n : ℕ) (N : ℤ) :
    {g : Matrix (Fin n) (Fin n) ℤ | ∀ k i, |g k i| ≤ N}.Finite := by
  classical
  have hbox : {g : Matrix (Fin n) (Fin n) ℤ | ∀ k i, |g k i| ≤ N}
      = Set.pi Set.univ (fun _ : Fin n =>
          Set.pi Set.univ (fun _ : Fin n => Set.Icc (-N) N)) := by
    ext g
    constructor
    · intro hg k _ i _
      exact abs_le.1 (hg k i)
    · intro hg k i
      exact abs_le.2 (hg k (Set.mem_univ k) i (Set.mem_univ i))
  rw [hbox]
  exact Set.Finite.pi fun _ => Set.Finite.pi fun _ => Set.finite_Icc _ _

/-- **Siegel's finiteness property.**  Only finitely many integral unimodular matrices carry one
Siegel-reduced form to another.  The conjugating matrix is bounded, and bounded integral matrices
are finite in number. -/
theorem siegel_finiteness (n : ℕ) (t u : ℝ) (ht : 1 ≤ t) :
    {γ : Matrix (Fin n) (Fin n) ℝ | IsIntUnimodular γ ∧
      ∃ J J' : JacobiData n, J.IsSiegel t u ∧ J'.IsSiegel t u
        ∧ J'.form = γᵀ * J.form * γ}.Finite := by
  classical
  obtain ⟨B, hB⟩ := exists_gamma_bound n t u ht
  refine Set.Finite.subset
    ((finite_intMatrix_bounded n ⌈B⌉).image (fun g => g.map (fun z : ℤ => (z : ℝ)))) ?_
  rintro γ ⟨hγ, J, J', hS, hS', hform⟩
  obtain ⟨g, hgu, hg⟩ := id hγ
  refine ⟨g, ?_, ?_⟩
  · intro k i
    have h1 : |γ k i| ≤ B := hB J J' hS hS' γ hγ hform k i
    have h2 : ((|g k i| : ℤ) : ℝ) ≤ B := by
      rw [Int.cast_abs, ← hg k i]
      exact h1
    have h3 : ((|g k i| : ℤ) : ℝ) ≤ ((⌈B⌉ : ℤ) : ℝ) := le_trans h2 (Int.le_ceil B)
    exact_mod_cast h3
  · ext k i
    exact (hg k i).symm

end GaloisForLFunctions.HTGeometry
