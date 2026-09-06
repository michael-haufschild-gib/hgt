import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.DividedDifference
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Mixed divided differences of translation kernels

Applying the corpus divided-difference mean-value theorem successively in the two variables
identifies a mixed stencil with one literal derivative evaluated inside the difference of the
node hulls. The identity includes order zero and imposes no spacing-ratio bound.
-/

open Set Finset
namespace GaloisForLFunctions.HTGeometry
open HilbertIrreducibility
noncomputable section

/-- Closed-hull form of the corpus divided-difference theorem, including order zero. -/
theorem exists_dividedDiff_eq_closed {m : ℕ} (D : ℕ → ℝ → ℝ)
    (hD : ∀ j, j < m → ∀ x : ℝ, HasDerivAt (D j) (D (j+1) x) x)
    (t : Fin (m+1) → ℝ) (ht : StrictMono t) :
    ∃ u ∈ Icc (t 0) (t (Fin.last m)), dividedDiff (D 0) t = D m u / (m.factorial : ℝ) := by
  cases m with
  | zero =>
      refine ⟨t 0, by simp, ?_⟩
      simp [dividedDiff]
  | succ m =>
      obtain ⟨u, hu, heq⟩ := exists_dividedDiff_eq (Nat.succ_pos m) D
        (U:=univ) (fun j hj x _ => hD j hj x) t ht (subset_univ _)
      exact ⟨u, Ioo_subset_Icc_self hu, heq⟩

/-- Two independent divided-difference stencils applied to a translation kernel. -/
def mixedTranslationDividedDiff {p q : ℕ} (f : ℝ → ℝ)
    (x : Fin (p+1) → ℝ) (y : Fin (q+1) → ℝ) : ℝ :=
  dividedDiff (fun u => dividedDiff (fun v => f (u-v)) y) x

private theorem derivative_shift_chain {n j : ℕ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ n f) (hj : j < n) (v u : ℝ) :
    HasDerivAt (fun x => iteratedDeriv j f (x-v)) (iteratedDeriv (j+1) f (u-v)) u := by
  have hd := (hf.differentiable_iteratedDeriv j (by exact_mod_cast hj) (u-v)).hasDerivAt
  rw [← iteratedDeriv_succ] at hd
  convert hd.comp u ((hasDerivAt_id u).sub_const v) using 1 <;> first | rfl | simp

/-- Mixed mean-value identity with no bound on spacing ratios or denominator conditioning. -/
theorem exists_mixedTranslationDividedDiff_eq {p q : ℕ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ (p+q : ℕ) f)
    (x : Fin (p+1) → ℝ) (hx : StrictMono x)
    (y : Fin (q+1) → ℝ) (hy : StrictMono y) :
    ∃ u ∈ Icc (x 0) (x (Fin.last p)), ∃ v ∈ Icc (y 0) (y (Fin.last q)),
      mixedTranslationDividedDiff f x y =
        (-1 : ℝ)^q * iteratedDeriv (p+q) f (u-v) /
          ((p.factorial : ℝ) * (q.factorial : ℝ)) := by
  let D : ℕ → ℝ → ℝ := fun j u =>
    dividedDiff (fun v => iteratedDeriv j f (u-v)) y
  have hD : ∀ j, j < p → ∀ u : ℝ, HasDerivAt (D j) (D (j+1) u) u := by
    intro j hj u
    dsimp only [D, dividedDiff]
    simpa only [sum_fn] using HasDerivAt.sum (u:=Finset.univ) (fun i _ =>
      (derivative_shift_chain (n:=p+q) (j:=j) hf (Nat.lt_of_lt_of_le hj (Nat.le_add_right p q)) (y i) u).div_const (∏ j ∈ Finset.univ.erase i, (y i-y j)))
  obtain ⟨u, hu, hleft⟩ := exists_dividedDiff_eq_closed D hD x hx
  let E : ℕ → ℝ → ℝ := fun j v => (-1 : ℝ)^j * iteratedDeriv (p+j) f (u-v)
  have hE : ∀ j, j < q → ∀ v : ℝ, HasDerivAt (E j) (E (j+1) v) v := by
    intro j hj v
    have hd := (hf.differentiable_iteratedDeriv (p+j) (by exact_mod_cast (show p+j < p+q by omega)) (u-v)).hasDerivAt
    rw [← iteratedDeriv_succ] at hd
    have hc := (hd.comp v ((hasDerivAt_id v).const_sub u)).const_mul ((-1 : ℝ)^j)
    dsimp only [E]
    convert hc using 1 <;> first | rfl | simp [Nat.add_assoc, pow_succ]
  obtain ⟨v, hv, hright⟩ := exists_dividedDiff_eq_closed E hE y hy
  refine ⟨u, hu, v, hv, ?_⟩
  change mixedTranslationDividedDiff f x y = D p u / (p.factorial : ℝ) at hleft
  have heq : D p u = (-1 : ℝ)^q * iteratedDeriv (p+q) f (u-v) / (q.factorial : ℝ) := by
    simpa [D, E] using hright
  rw [hleft, heq]
  ring

end
end GaloisForLFunctions.HTGeometry
