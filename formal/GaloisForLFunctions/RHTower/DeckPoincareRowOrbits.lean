import GaloisForLFunctions.RHTower.DeckPoincareSeries

/-!
# Translation orbits of coprime rows

The translation `T` acts on coprime rows by `(c, d) ↦ (c, d + c)` (`rowShift`).  Rows with `c = 0` are
`±(0, 1)`; rows with `c ≠ 0` are the free orbits of this action, and each orbit meets the reduced rows
`0 ≤ d < |c|` exactly once: `(r, k) ↦ r T^k` is a bijection from reduced rows × `ℤ` onto the rows with
`c ≠ 0` (`reducedRowShiftEquiv`).

For a compatible pair `(h, v)` the Poincaré terms transform by `P_{rT^k}(z) = ρ(T^k)⁻¹ P_r(T^k z)`
(`poincTerm_rowShift`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set EisensteinSeries
open scoped MatrixGroups

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet SelbergMaassCongruenceTrace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

/-- The translate `r T^k` of a coprime row. -/
def rowShift (k : ℤ) (p : gammaSet 1 1 0) : gammaSet 1 1 0 :=
  gammaSetSelfEquiv (ModularGroup.T ^ k) p

theorem rowShift_zero_coord (k : ℤ) (p : gammaSet 1 1 0) : (rowShift k p).1 0 = p.1 0 := by
  rw [rowShift, gammaSetSelfEquiv_apply_val, ModularGroup.coe_T_zpow]
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem rowShift_one_coord (k : ℤ) (p : gammaSet 1 1 0) :
    (rowShift k p).1 1 = p.1 1 + k * p.1 0 := by
  rw [rowShift, gammaSetSelfEquiv_apply_val, ModularGroup.coe_T_zpow]
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  ring

theorem rowShift_val (k : ℤ) (p : gammaSet 1 1 0) :
    (rowShift k p).1 = ![p.1 0, p.1 1 + k * p.1 0] := by
  funext i
  fin_cases i
  · exact rowShift_zero_coord k p
  · exact rowShift_one_coord k p

/-- Reduced rows: `c ≠ 0` and `0 ≤ d < |c|`. -/
def ReducedRow : Type := {r : gammaSet 1 1 0 // r.1 0 ≠ 0 ∧ 0 ≤ r.1 1 ∧ r.1 1 < |r.1 0|}

theorem rowShift_injective {r r' : gammaSet 1 1 0} {k k' : ℤ} (hr : r.1 0 ≠ 0)
    (h0 : 0 ≤ r.1 1) (h1 : r.1 1 < |r.1 0|) (h0' : 0 ≤ r'.1 1) (h1' : r'.1 1 < |r'.1 0|)
    (h : rowShift k r = rowShift k' r') : r = r' ∧ k = k' := by
  have hc : r.1 0 = r'.1 0 := by
    have := congrArg (fun p : gammaSet 1 1 0 => p.1 0) h
    simpa [rowShift_zero_coord] using this
  have hd : r.1 1 + k * r.1 0 = r'.1 1 + k' * r'.1 0 := by
    have := congrArg (fun p : gammaSet 1 1 0 => p.1 1) h
    simpa [rowShift_one_coord] using this
  rw [← hc] at hd h1'
  -- `r.1 1 - r'.1 1 = (k' - k) c` with `|r.1 1 - r'.1 1| < |c|`
  have hdiff : r.1 1 - r'.1 1 = (k' - k) * r.1 0 := by linarith
  have hkk : k' - k = 0 := by
    by_contra hne
    have habs : |r.1 0| ≤ |r.1 1 - r'.1 1| := by
      rw [hdiff, abs_mul]
      have : (1 : ℤ) ≤ |k' - k| := Int.one_le_abs hne
      nlinarith [abs_nonneg (r.1 0)]
    have : |r.1 1 - r'.1 1| < |r.1 0| := by
      rw [abs_lt]
      constructor <;> linarith
    linarith
  have hk : k = k' := by linarith
  refine ⟨Subtype.ext ?_, hk⟩
  funext i
  fin_cases i
  · exact hc
  · show r.1 1 = r'.1 1
    rw [hk] at hdiff
    linarith [hdiff, show (k' - k') * r.1 0 = 0 by ring]

/-- Every row with `c ≠ 0` is a translate of a reduced row. -/
theorem exists_rowShift_eq {p : gammaSet 1 1 0} (hp : p.1 0 ≠ 0) :
    ∃ (r : gammaSet 1 1 0) (k : ℤ), r.1 0 ≠ 0 ∧ 0 ≤ r.1 1 ∧ r.1 1 < |r.1 0| ∧ rowShift k r = p := by
  set c := p.1 0
  set d := p.1 1
  set d₀ := d % |c|
  have hc0 : (0 : ℤ) < |c| := abs_pos.2 hp
  have hd₀ : 0 ≤ d₀ := Int.emod_nonneg d hc0.ne'
  have hd₁ : d₀ < |c| := Int.emod_lt_of_pos d hc0
  obtain ⟨k, hk⟩ : c ∣ d - d₀ := by
    have h1 : |c| ∣ d - d₀ := by
      rw [show d - d₀ = |c| * (d / |c|) by rw [Int.emod_def]; ring]
      exact dvd_mul_right _ _
    exact (abs_dvd c _).1 h1
  have hcop : IsCoprime c d₀ := by
    have hp' := (gammaSet_one_mem_iff 1 p.1).1 p.2
    have hcd : IsCoprime c d := Int.isCoprime_iff_gcd_eq_one.2 hp'
    have : d₀ = d + (-k) * c := by linear_combination -hk
    rw [this]
    exact hcd.add_mul_left_right (-k)
  let r : gammaSet 1 1 0 := ⟨![c, d₀], by
    rw [gammaSet_one_mem_iff]
    simpa using Int.isCoprime_iff_gcd_eq_one.1 hcop⟩
  refine ⟨r, k, by simpa [r] using hp, by simpa [r] using hd₀, by simpa [r] using hd₁, ?_⟩
  apply Subtype.ext
  rw [rowShift_val]
  funext i
  fin_cases i
  · rfl
  · simp only [r, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    show d₀ + k * c = d
    linear_combination hk

/-- Rows with `c ≠ 0`. -/
def NonzeroRow : Type := {p : gammaSet 1 1 0 // p.1 0 ≠ 0}

/-- **Orbit decomposition**: reduced rows × `ℤ` ≃ rows with `c ≠ 0`, `(r, k) ↦ r T^k`. -/
def reducedRowShiftEquiv : ReducedRow × ℤ ≃ NonzeroRow :=
  Equiv.ofBijective (fun rk => ⟨rowShift rk.2 rk.1.1, by rw [rowShift_zero_coord]; exact rk.1.2.1⟩)
    ⟨fun ⟨r, k⟩ ⟨r', k'⟩ h => by
      have h' : rowShift k r.1 = rowShift k' r'.1 := congrArg Subtype.val h
      obtain ⟨hr, hk⟩ := rowShift_injective r.2.1 r.2.2.1 r.2.2.2 r'.2.2.1 r'.2.2.2 h'
      exact Prod.ext (Subtype.ext hr) hk,
    fun p => by
      obtain ⟨r, k, h1, h2, h3, h4⟩ := exists_rowShift_eq p.2
      exact ⟨(⟨r, h1, h2, h3⟩, k), Subtype.ext h4⟩⟩

theorem reducedRowShiftEquiv_apply (r : ReducedRow) (k : ℤ) :
    (reducedRowShiftEquiv (r, k)).1 = rowShift k r.1 := rfl

/-! ## The Poincaré terms along an orbit -/

theorem poincTerm_rowShift {h : ℍ → ℂ} {v : DeckSpace N} (hc : CuspCompatible h v) (k : ℤ)
    (p : gammaSet 1 1 0) (z : ℍ) :
    poincTerm h v (rowShift k p) z =
      (deckRho N (ModularGroup.T ^ k)).symm (poincTerm h v p (ModularGroup.T ^ k • z)) := by
  rw [poincTerm_smul hc, LinearIsometryEquiv.symm_apply_apply]
  rfl

end

end GaloisForLFunctions.RHTower.DeckPointPair
