import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicInductionInStages

/-! Iterating the Fourier step writes a mirabolic class function as the sum
of the contributions from its successive zero-frequency column means. -/

noncomputable section
open GaloisForLFunctions
open scoped Classical

namespace GlobalTheory.GLq

variable {g : ℕ} [Fact g.Prime]

/-- Take the nonzero column coefficient until the indicated rank, then the zero coefficient. -/
def mirabolicDerivative (ψ : AddChar (ZMod g) ℂ) :
    (m : ℕ) → (i : Fin (m + 1)) → (Gn g (m + 1) → ℂ) → Gn g i.val → ℂ
  | 0, i => Fin.lastCases (motive := fun i => (Gn g 1 → ℂ) → Gn g i.val → ℂ)
      (fun F A => mirabolicFourier ψ F A 0) (fun j => Fin.elim0 j) i
  | m + 1, i => Fin.lastCases
      (motive := fun i => (Gn g (m + 2) → ℂ) → Gn g i.val → ℂ)
      (fun F A => mirabolicFourier ψ F A 0)
      (fun j F => mirabolicDerivative ψ m j (mirabolicTail ψ F)) i

/-- Inflate from the indicated leading rank and induce through successive
mirabolic subgroups with the last-column character. -/
def mirabolicInductionAt (ψ : AddChar (ZMod g) ℂ) :
    (m : ℕ) → (i : Fin (m + 1)) → (Gn g i.val → ℂ) → mirabolicSubgroup g m → ℂ
  | 0, i => Fin.lastCases (motive := fun i => (Gn g i.val → ℂ) → mirabolicSubgroup g 0 → ℂ)
      (fun F u => F (mirabolicLevi u)) (fun j => Fin.elim0 j) i
  | m + 1, i => Fin.lastCases
      (motive := fun i => (Gn g i.val → ℂ) → mirabolicSubgroup g (m + 1) → ℂ)
      (fun F u => F (mirabolicLevi u))
      (fun j F => mirabolicInduce ψ (mirabolicInductionAt ψ m j F)) i

private theorem mirabolicFourier_zero_rank (ψ : AddChar (ZMod g) ℂ) (F : Gn g 1 → ℂ)
    (u : mirabolicSubgroup g 0) : mirabolicFourier ψ F (mirabolicLevi u) 0 = F u.val := by
  obtain ⟨A, v, h⟩ := exists_mirabolicBlock u.property
  rw [show u = mirabolicUnit A v from Subtype.ext h, mirabolicLevi_unit]
  change mirabolicFourier ψ F A 0 = F (mirabolicBlock A v)
  have hv : v = 0 := Subsingleton.elim _ _
  subst v
  unfold mirabolicFourier columnFourier
  rw [Fintype.sum_subsingleton _ 0]
  simp

/-- The full expansion of a mirabolic class function by its successive derivatives. -/
theorem mirabolic_eq_sum_induced_derivatives (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1)
    (m : ℕ) (F : Gn g (m + 1) → ℂ) (hF : IsMirabolicClass F) (u : mirabolicSubgroup g m) :
    F u.val = ∑ i : Fin (m + 1), mirabolicInductionAt ψ m i (mirabolicDerivative ψ m i F) u := by
  induction m with
  | zero =>
    rw [Fin.sum_univ_one]
    rw [show (0 : Fin 1) = Fin.last 0 from rfl, mirabolicInductionAt, mirabolicDerivative,
      Fin.lastCases_last, Fin.lastCases_last]
    exact (mirabolicFourier_zero_rank ψ F u).symm
  | succ m ih =>
    rw [Fin.sum_univ_castSucc, mirabolic_eq_mean_add_induced ψ hψ hF u]
    have hmean : mirabolicInductionAt ψ (m + 1) (Fin.last (m + 1))
        (mirabolicDerivative ψ (m + 1) (Fin.last (m + 1)) F) u =
          mirabolicFourier ψ F (mirabolicLevi u) 0 := by
      rw [mirabolicInductionAt, mirabolicDerivative, Fin.lastCases_last, Fin.lastCases_last]
      rfl
    have hrest (i : Fin (m + 1)) :
        mirabolicInductionAt ψ (m + 1) i.castSucc (mirabolicDerivative ψ (m + 1) i.castSucc F) u =
          mirabolicInduce ψ (mirabolicInductionAt ψ m i
            (mirabolicDerivative ψ m i (mirabolicTail ψ F))) u := by
      rw [mirabolicInductionAt, mirabolicDerivative, Fin.lastCases_castSucc, Fin.lastCases_castSucc]
    rw [hmean, add_comm _ (mirabolicFourier ψ F (mirabolicLevi u) 0),
      Finset.sum_congr rfl fun i _ => hrest i]
    congr 1
    have ht : (fun x : mirabolicSubgroup g m => mirabolicTail ψ F x.val) =
        fun x => ∑ i : Fin (m + 1), mirabolicInductionAt ψ m i
          (mirabolicDerivative ψ m i (mirabolicTail ψ F)) x :=
      funext (ih (mirabolicTail ψ F) (mirabolicTail_isMirabolicClass ψ hF))
    change mirabolicInduce ψ (fun x => mirabolicTail ψ F x.val) u = _
    rw [ht, mirabolicInduce_sum]
    simp only [Finset.sum_apply]

end GlobalTheory.GLq
