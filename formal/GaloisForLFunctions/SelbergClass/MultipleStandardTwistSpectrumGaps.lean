import GaloisForLFunctions.SelbergClass.MultipleStandardTwistSpectrum

/-!
# Local finiteness and right gaps for multiple-standard-twist spectral values

This is a prerequisite for contour deformations around the discrete spectrum.
It derives local finiteness from Kaczorowski--Perelli's normalized spectral
value formula itself: no finiteness certificate or discreteness assumption is
part of `MultipleStandardTwistData`.

The results concern only the explicit spectral-value map and the spectrum
selected by nonzero coefficients.  They make no assertion about meromorphic
continuation, residues, or actual poles of a multiple standard twist.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.SelbergClass

namespace MultipleStandardTwistData

/-- The positive-index tuples below a bounded spectral level form a finite set.
The proof bounds each coordinate explicitly using the positive scale product
and the positive twist exponent. -/
theorem spectralSublevel_finite {N : ℕ} (D : MultipleStandardTwistData N) (a : ℝ) :
    {n : Fin N → ℕ+ | D.spectralValue n < a}.Finite := by
  by_cases ha : 0 < a
  · let M : ℝ := a * D.spectralScaleProduct
    have hM : 0 < M := mul_pos ha D.spectralScaleProduct_pos
    let B : Fin N → ℕ := fun i => Nat.ceil (M ^ (D.kappa i)⁻¹)
    let T : Set (Fin N → ℕ) := {m | ∀ i, m i ≤ B i}
    have hTfinite : T.Finite := by
      simpa only [T, Set.mem_setOf_eq, Set.mem_Iic] using
        (Set.Finite.pi' fun i => Set.finite_Iic (B i))
    let coeIndex : (Fin N → ℕ+) → (Fin N → ℕ) := fun n i => (n i : ℕ)
    have hcoeIndex : Function.Injective coeIndex := by
      intro n m h
      funext i
      apply PNat.eq
      exact congrFun h i
    have hsubset : {n : Fin N → ℕ+ | D.spectralValue n < a} ⊆ coeIndex ⁻¹' T := by
      intro n hn
      change ∀ i, (n i : ℕ) ≤ B i
      intro i
      have hweighted : D.weightedIndexValue n < M := by
        calc
          D.weightedIndexValue n = D.spectralValue n * D.spectralScaleProduct :=
            (D.spectralValue_mul_spectralScaleProduct n).symm
          _ < a * D.spectralScaleProduct :=
            mul_lt_mul_of_pos_right hn D.spectralScaleProduct_pos
          _ = M := rfl
      have hfactor : ((n i : ℕ) : ℝ) ^ D.kappa i ≤ M :=
        (D.weightedIndexCoordinate_le n i).trans hweighted.le
      have hrootpow : (M ^ (D.kappa i)⁻¹) ^ D.kappa i = M := by
        rw [← Real.rpow_mul hM.le, inv_mul_cancel₀ (ne_of_gt (D.kappa_pos i)),
          Real.rpow_one]
      have hreal : ((n i : ℕ) : ℝ) ≤ M ^ (D.kappa i)⁻¹ := by
        apply (Real.rpow_le_rpow_iff (by positivity)
          (Real.rpow_nonneg hM.le _) (D.kappa_pos i)).mp
        simpa only [hrootpow] using hfactor
      have hcast : ((n i : ℕ) : ℝ) ≤ (B i : ℝ) := by
        dsimp only [B]
        exact hreal.trans (Nat.le_ceil _)
      exact_mod_cast hcast
    exact (Set.Finite.preimage hcoeIndex.injOn hTfinite).subset hsubset
  · have hempty : {n : Fin N → ℕ+ | D.spectralValue n < a} = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      rintro ⟨n, hn⟩
      exact not_lt_of_ge (le_of_not_gt ha) (lt_trans (D.spectralValue_pos n) hn)
    rw [hempty]
    exact Set.finite_empty

/-- Every real level has a positive right-hand gap in the set of spectral
values.  In particular, this holds above each value occurring in the spectrum. -/
theorem exists_spectralValue_right_gap {N : ℕ} (D : MultipleStandardTwistData N)
    (α : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ n : Fin N → ℕ+, α < D.spectralValue n →
      α + ε ≤ D.spectralValue n := by
  classical
  let S : Finset (Fin N → ℕ+) :=
    ((D.spectralSublevel_finite (α + 1)).toFinset).filter
      (fun n => α < D.spectralValue n)
  let T : Finset ℝ := insert 1 (S.image fun n => D.spectralValue n - α)
  have hTne : T.Nonempty := ⟨1, Finset.mem_insert_self 1 _⟩
  refine ⟨T.min' hTne, ?_, ?_⟩
  · have hmem : T.min' hTne ∈ T := Finset.min'_mem T hTne
    rcases Finset.mem_insert.mp hmem with hone | hdiff
    · simp [hone]
    · rcases Finset.mem_image.mp hdiff with ⟨n, hnS, hEq⟩
      have hn : α < D.spectralValue n := (Finset.mem_filter.mp hnS).2
      rw [← hEq]
      linarith
  · intro n hn
    by_cases hsmall : D.spectralValue n < α + 1
    · have hnsublevel : n ∈ (D.spectralSublevel_finite (α + 1)).toFinset :=
        (Set.Finite.mem_toFinset _).mpr hsmall
      have hnS : n ∈ S := Finset.mem_filter.mpr ⟨hnsublevel, hn⟩
      have hdiff : D.spectralValue n - α ∈ T := by
        apply Finset.mem_insert_of_mem
        exact Finset.mem_image.mpr ⟨n, hnS, rfl⟩
      have hmin : T.min' hTne ≤ D.spectralValue n - α :=
        Finset.min'_le T _ hdiff
      linarith
    · have hlarge : α + 1 ≤ D.spectralValue n := le_of_not_gt hsmall
      have hone : (1 : ℝ) ∈ T := Finset.mem_insert_self 1 _
      have hmin : T.min' hTne ≤ 1 := Finset.min'_le T _ hone
      linarith

/-- The actual spectrum has the same positive right-hand gap, because every
spectral point is represented by a positive-index tuple. -/
theorem exists_spectrum_right_gap {N : ℕ} (D : MultipleStandardTwistData N)
    (α : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ β : ℝ, β ∈ D.spectrum → α < β → α + ε ≤ β := by
  rcases D.exists_spectralValue_right_gap α with ⟨ε, hε, hgap⟩
  refine ⟨ε, hε, ?_⟩
  intro β hβ hlt
  rcases (D.mem_spectrum_iff β).mp hβ with ⟨n, hn, _⟩
  have hlt' : α < D.spectralValue n := by simpa only [hn] using hlt
  rw [← hn]
  exact hgap n hlt'

end MultipleStandardTwistData

end GaloisForLFunctions.SelbergClass
