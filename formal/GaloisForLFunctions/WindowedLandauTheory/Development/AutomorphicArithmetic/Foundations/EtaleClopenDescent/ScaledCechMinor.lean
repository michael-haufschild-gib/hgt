import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechMinorCocycle

/-! A determinant of integral rows is integral after dividing out
the units used to scale those rows. -/

noncomputable section

namespace GlobalTheory.WH

variable {k S E ι : Type} [Field k] [CommRing S] [Algebra k S]
  [AddCommGroup E] [Module k E] [LinearOrder ι] {p : ℕ}

/-- Multiplying the columns of the row array multiplies the ordered
minor by the product of the column factors. -/
theorem orderedMinor_mul_columns (r : ι → Fin p → S) (c : Fin p → S) (s : Finset ι) :
    orderedMinor (fun i j => r i j * c j) s = orderedMinor r s * ∏ j, c j := by
  by_cases hs : s.card = p
  · let e := s.orderEmbOfFin hs
    let P : Matrix (Fin p) (Fin p) S := Matrix.of fun a b => r (e a) b
    have he : (Matrix.of fun a b => r (e a) b * c b) = P * Matrix.diagonal c := by
      ext a b
      simp only [Matrix.of_apply, Matrix.mul_diagonal, P]
    simp only [orderedMinor, dif_pos hs]
    change (Matrix.of fun a b => r (e a) b * c b).det = P.det * ∏ j, c j
    rw [he, Matrix.det_mul, Matrix.det_diagonal]
  · simp only [orderedMinor, dif_neg hs, zero_mul]

/-- The ordered determinant has the product of its row scalings
as a factor, with the remaining coefficient in the chart ring. -/
theorem orderedMinor_normalized_mem (R : Subalgebra k S)
    (r : ι → Fin p → S) (u : ι → Sˣ) (s : Finset ι)
    (hr : ∀ i ∈ s, ∀ j, ((u i)⁻¹ : Sˣ) * r i j ∈ R) :
    (((∏ i ∈ s, u i)⁻¹ : Sˣ) : S) * orderedMinor r s ∈ R := by
  by_cases hs : s.card = p
  · let e := s.orderEmbOfFin hs
    let P : Matrix (Fin p) (Fin p) R :=
      Matrix.of fun i j => ⟨((u (e i))⁻¹ : Sˣ) * r (e i) j, hr _ (Finset.orderEmbOfFin_mem _ _ _) _⟩
    let D : Matrix (Fin p) (Fin p) S := Matrix.diagonal fun i => (u (e i) : S)
    have hd : (Matrix.of fun i j => r (e i) j) = D * P.map R.val := by
      ext i j
      simp only [D, Matrix.diagonal_mul, Matrix.of_apply, Matrix.map_apply, P, Subalgebra.coe_val]
      rw [← mul_assoc, Units.mul_inv, one_mul]
    have hprod : (∏ i : Fin p, (u (e i) : S)) = ((∏ i ∈ s, u i : Sˣ) : S) := by
      rw [Units.coe_prod, ← Finset.map_orderEmbOfFin_univ s hs, Finset.prod_map]
      rfl
    have hdet : D.det = ((∏ i ∈ s, u i : Sˣ) : S) := Matrix.det_diagonal.trans hprod
    change (((∏ i ∈ s, u i)⁻¹ : Sˣ) : S) * orderedMinor r s ∈ R
    rw [orderedMinor, dif_pos hs]
    change (((∏ i ∈ s, u i)⁻¹ : Sˣ) : S) * (Matrix.of fun i j => r (e i) j).det ∈ R
    rw [hd, Matrix.det_mul, hdet, ← mul_assoc, Units.inv_mul, one_mul]
    have he : (P.map R.val).det = R.val P.det := (R.val.map_det P).symm
    rw [he]
    exact (P.det : R).property
  · simp only [orderedMinor, dif_neg hs, mul_zero, zero_mem]

/-- If the chart lattice is stable under its ring, the ordered
determinant sends it to the row-scaled chart lattice. -/
theorem act_orderedMinor_mem_scaled (R : Subalgebra k S) (M : Submodule k E)
    (act : S →ₐ[k] Module.End k E)
    (hstab : ∀ a ∈ R, ∀ v ∈ M, act a v ∈ M)
    (r : ι → Fin p → S) (u : ι → Sˣ) (s : Finset ι)
    (hr : ∀ i ∈ s, ∀ j, ((u i)⁻¹ : Sˣ) * r i j ∈ R) {m : E} (hm : m ∈ M) :
    act (orderedMinor r s) m ∈ M.map (act ((∏ i ∈ s, u i : Sˣ) : S)) := by
  let v : Sˣ := ∏ i ∈ s, u i
  let z : S := (v⁻¹ : Sˣ) * orderedMinor r s
  have hz : z ∈ R := orderedMinor_normalized_mem R r u s hr
  refine ⟨act z m, hstab z hz m hm, ?_⟩
  change act (v : S) (act z m) = act (orderedMinor r s) m
  rw [← Module.End.mul_apply, ← map_mul, show (v : S) * z = orderedMinor r s by
    dsimp only [z]
    rw [← mul_assoc, Units.mul_inv, one_mul]]

end GlobalTheory.WH
