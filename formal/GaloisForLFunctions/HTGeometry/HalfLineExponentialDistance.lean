import GaloisForLFunctions.HTGeometry.HalfLineExponentialGram
import GaloisForLFunctions.HTGeometry.CauchyDeterminantStep

/-!
# The exact distance from one half-line exponential to the span of the earlier ones

The Gram determinant of the half-line exponential system is a Cauchy determinant, and the
consecutive Cauchy relation turns the Gram-determinant recursion into a closed formula: the squared
distance from `e_{λ_N}` to `span {e_{λ_0}, …, e_{λ_{N-1}}}` is

`(∏_{i<N} (λ_i - λ_N))² / ((∏_{i<N} (λ_i + λ_N))² · 2 λ_N)`,

which is the Blaschke product of the earlier rates against the last one, divided by the squared
norm's reciprocal.
-/

open Finset Matrix MeasureTheory
open scoped InnerProductSpace
open InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The exponential family of an `ℕ`-indexed rate sequence. -/
def expSystem (lam : ℕ → ℝ) (hpos : ∀ k, 0 < lam k) (k : ℕ) :
    Lp ℂ 2 halfLineLaplaceMeasure :=
  expFeature (lam k) (hpos k)

/-- **The exact Blaschke distance law.**  The squared Gram--Schmidt length of the exponential
system at step `N` is the Blaschke ratio of the earlier rates against `λ_N`. -/
theorem inner_gramSchmidt_expSystem {lam : ℕ → ℝ} (hpos : ∀ k, 0 < lam k)
    (hinj : Function.Injective lam) (N : ℕ) :
    inner ℂ (gramSchmidt ℂ (expSystem lam hpos) N) (gramSchmidt ℂ (expSystem lam hpos) N) *
        ((∏ i : Fin N, (((lam i : ℝ) : ℂ) + ((lam N : ℝ) : ℂ))) ^ (2 : ℕ) *
          (((lam N : ℝ) : ℂ) + ((lam N : ℝ) : ℂ)))
      = (∏ i : Fin N, (((lam i : ℝ) : ℂ) - ((lam N : ℝ) : ℂ))) ^ (2 : ℕ) := by
  classical
  set mu : Fin (N + 1) → ℝ := fun i => lam (i : ℕ) with hmu
  have hmupos : ∀ i, 0 < mu i := fun i => hpos _
  have hmuinj : Function.Injective mu := by
    intro i j hij
    exact Fin.val_injective (hinj hij)
  have hmusmall : ∀ i : Fin N, 0 < mu i.castSucc := fun i => hmupos _
  have hindep : LinearIndependent ℂ (fun i : Fin (N + 1) => expSystem lam hpos (i : ℕ)) :=
    linearIndependent_expFeature mu hmupos hmuinj
  have hgramrec := det_gram_fin_succ (expSystem lam hpos) N hindep
  -- both Gram matrices are Cauchy matrices
  set x : Fin (N + 1) → ℂ := fun i => ((mu i : ℝ) : ℂ) with hx
  have hxne : ∀ i j, x i + x j ≠ 0 := fun i j => add_ne_zero_of_pos (hmupos i) (hmupos j)
  have hgbig : Matrix.gram ℂ (fun i : Fin (N + 1) => expSystem lam hpos (i : ℕ)) =
      cauchyMatrix x x := gram_expFeature mu hmupos
  have hgsmall : Matrix.gram ℂ (fun i : Fin N => expSystem lam hpos (i : ℕ)) =
      cauchyMatrix (fun i : Fin N => x i.castSucc) (fun j : Fin N => x j.castSucc) :=
    gram_expFeature (fun i : Fin N => mu i.castSucc) hmusmall
  have hstep := det_cauchyMatrix_castSucc x hxne
  have hsmallne : (cauchyMatrix (fun i : Fin N => x i.castSucc)
      (fun j : Fin N => x j.castSucc)).det ≠ 0 := by
    rw [← hgsmall]
    exact det_gram_expFeature_ne_zero (fun i : Fin N => mu i.castSucc) hmusmall
      (fun i j hij => Fin.castSucc_injective N (hmuinj hij))
  rw [hgbig, hgsmall] at hgramrec
  have hkey := hstep
  rw [hgramrec] at hkey
  have hcancel :
      inner ℂ (gramSchmidt ℂ (expSystem lam hpos) N) (gramSchmidt ℂ (expSystem lam hpos) N) *
          ((∏ i : Fin N, (x i.castSucc + x (Fin.last N))) ^ (2 : ℕ) *
            (x (Fin.last N) + x (Fin.last N))) =
        (∏ i : Fin N, (x i.castSucc - x (Fin.last N))) ^ (2 : ℕ) := by
    refine mul_left_cancel₀ hsmallne ?_
    calc (cauchyMatrix (fun i : Fin N => x i.castSucc)
            (fun j : Fin N => x j.castSucc)).det *
          (inner ℂ (gramSchmidt ℂ (expSystem lam hpos) N)
              (gramSchmidt ℂ (expSystem lam hpos) N) *
            ((∏ i : Fin N, (x i.castSucc + x (Fin.last N))) ^ (2 : ℕ) *
              (x (Fin.last N) + x (Fin.last N))))
        = (cauchyMatrix (fun i : Fin N => x i.castSucc)
              (fun j : Fin N => x j.castSucc)).det *
            inner ℂ (gramSchmidt ℂ (expSystem lam hpos) N)
              (gramSchmidt ℂ (expSystem lam hpos) N) *
            ((∏ i : Fin N, (x i.castSucc + x (Fin.last N))) ^ (2 : ℕ) *
              (x (Fin.last N) + x (Fin.last N))) := by ring
      _ = (cauchyMatrix (fun i : Fin N => x i.castSucc)
              (fun j : Fin N => x j.castSucc)).det *
            (∏ i : Fin N, (x i.castSucc - x (Fin.last N))) ^ (2 : ℕ) := hkey
  have hcast : ∀ i : Fin N, x i.castSucc = ((lam (i : ℕ) : ℝ) : ℂ) := by
    intro i
    rw [hx, hmu]
    simp
  have hlast : x (Fin.last N) = ((lam N : ℝ) : ℂ) := by
    rw [hx, hmu]
    simp
  simp only [hcast, hlast] at hcancel
  exact hcancel

end

end GaloisForLFunctions.HTGeometry
