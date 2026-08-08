/-
Differential algebraicity relative to a family, compared with the absolute notion.

`RelativeDifferentialAlgebraicity` grades differential algebraicity by a base *family* of functions
`g : ι → ℂ → ℂ`, with monotonicity in the base; the absolute notion of `Hypertranscendence` grades
it by the point coordinate alone.  The relative layer compares itself only with the *empty* base,
which is strictly smaller than the absolute one: the absolute notion already carries the point as a
jet variable.

The correct comparison is with the one-element base consisting of the coordinate function.  It is a
reindexing of the relation polynomial in both directions, so the two notions agree there, and
monotonicity then gives the layer's headline claim, which was stated in prose but never proved:

* `differentiallyAlgebraicOver_coordinateBase_iff`,
  `hypertranscendentalOver_coordinateBase_iff` — the absolute notions are the coordinate-base ones;
* `differentiallyAlgebraicOver_of_differentiallyAlgebraic` — absolute differential algebraicity
  transfers to any base containing the coordinate;
* `hypertranscendental_of_hypertranscendentalOver` — hypertranscendence over such a base implies
  ordinary hypertranscendence, so the relative statement is the stronger one.
-/
import GaloisForLFunctions.HTGeometry.RelativeDifferentialAlgebraicWitnesses

open MvPolynomial

namespace GaloisForLFunctions

namespace RelativeDifferentialAlgebraicity

variable {ι : Type*}

/-- The one-element base consisting of the coordinate function. -/
def coordinateBase : Unit → ℂ → ℂ := fun _ => id

@[simp] theorem coordinateBase_apply (u : Unit) (z : ℂ) : coordinateBase u z = z := rfl

/-- The reindexing of the absolute jet coordinates by the coordinate base. -/
private def coordEmb (n : ℕ) : Fin (n + 2) → Unit ⊕ Fin (n + 1) :=
  Fin.cases (Sum.inl ()) fun j => Sum.inr j

/-- The reindexing of the coordinate-base variables by the absolute jet coordinates. -/
private def coordProj (n : ℕ) : Unit ⊕ Fin (n + 1) → Fin (n + 2) :=
  Sum.elim (fun _ => 0) Fin.succ

private theorem coordProj_coordEmb (n : ℕ) (v : Fin (n + 2)) :
    coordProj n (coordEmb n v) = v := by
  refine Fin.cases ?_ ?_ v
  · simp [coordEmb, coordProj]
  · intro j
    simp [coordEmb, coordProj]

private theorem coordEmb_coordProj (n : ℕ) (v : Unit ⊕ Fin (n + 1)) :
    coordEmb n (coordProj n v) = v := by
  cases v with
  | inl u => cases u; simp [coordEmb, coordProj]
  | inr j => simp [coordEmb, coordProj]

private theorem coordEmb_injective (n : ℕ) : Function.Injective (coordEmb n) :=
  Function.LeftInverse.injective (coordProj_coordEmb n)

private theorem coordProj_injective (n : ℕ) : Function.Injective (coordProj n) :=
  Function.LeftInverse.injective (coordEmb_coordProj n)

private theorem coordEmb_comp (n : ℕ) (z : ℂ) (f : ℂ → ℂ) :
    (Sum.elim (fun u => coordinateBase u z) fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) ∘
        coordEmb n
      = Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z := by
  funext v
  refine Fin.cases ?_ ?_ v
  · simp [coordEmb]
  · intro j
    simp [coordEmb]

private theorem coordProj_comp (n : ℕ) (z : ℂ) (f : ℂ → ℂ) :
    (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) ∘ coordProj n
      = Sum.elim (fun u => coordinateBase u z) fun j : Fin (n + 1) =>
          iteratedDeriv (j : ℕ) f z := by
  funext v
  cases v with
  | inl u => simp [coordProj]
  | inr j => simp [coordProj]

/-- **Differential algebraicity is differential algebraicity over the coordinate base**, order by
order.  The absolute notion already carries the point coordinate as a jet variable; naming it as a
one-element base is a reindexing of the polynomial. -/
theorem differentiallyAlgebraicOverOfOrder_coordinateBase_iff {f : ℂ → ℂ} {n : ℕ} :
    DifferentiallyAlgebraicOverOfOrder coordinateBase f n ↔
      ∃ P : MvPolynomial (Fin (n + 2)) ℂ, P ≠ 0 ∧
        ∀ z : ℂ, MvPolynomial.eval
          (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) P = 0 := by
  constructor
  · rintro ⟨Q, hQ, hzero⟩
    refine ⟨MvPolynomial.rename (coordProj n) Q, ?_, ?_⟩
    · intro hcon
      apply hQ
      apply MvPolynomial.rename_injective _ (coordProj_injective n)
      simpa using hcon
    · intro z
      rw [MvPolynomial.eval_rename, coordProj_comp n z f]
      exact hzero z
  · rintro ⟨P, hP, hzero⟩
    refine ⟨MvPolynomial.rename (coordEmb n) P, ?_, ?_⟩
    · intro hcon
      apply hP
      apply MvPolynomial.rename_injective _ (coordEmb_injective n)
      simpa using hcon
    · intro z
      rw [MvPolynomial.eval_rename, coordEmb_comp n z f]
      exact hzero z

/-- **The absolute and coordinate-base notions agree.** -/
theorem differentiallyAlgebraicOver_coordinateBase_iff {f : ℂ → ℂ} :
    DifferentiallyAlgebraicOver coordinateBase f ↔ GaloisForLFunctions.DifferentiallyAlgebraic f := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, differentiallyAlgebraicOverOfOrder_coordinateBase_iff.1 hn⟩
  · rintro ⟨n, P, hP, hzero⟩
    exact ⟨n, differentiallyAlgebraicOverOfOrder_coordinateBase_iff.2 ⟨P, hP, hzero⟩⟩

/-- **Hypertranscendence over the coordinate base is ordinary hypertranscendence.** -/
theorem hypertranscendentalOver_coordinateBase_iff {f : ℂ → ℂ} :
    HypertranscendentalOver coordinateBase f ↔ GaloisForLFunctions.Hypertranscendental f :=
  not_congr differentiallyAlgebraicOver_coordinateBase_iff

/-- **A differentially algebraic function is differentially algebraic over any base containing the
coordinate.** -/
theorem differentiallyAlgebraicOver_of_differentiallyAlgebraic {g : ι → ℂ → ℂ} {i₀ : ι}
    (h₀ : g i₀ = id) {f : ℂ → ℂ} (hf : GaloisForLFunctions.DifferentiallyAlgebraic f) :
    DifferentiallyAlgebraicOver g f := by
  refine DifferentiallyAlgebraicOver.mono (e := fun _ : Unit => i₀)
    (fun _ _ _ => rfl) (fun _ => h₀) ?_
  exact differentiallyAlgebraicOver_coordinateBase_iff.2 hf

/-- **Relative hypertranscendence over a base containing the coordinate implies ordinary
hypertranscendence.**  This is the sense in which the relative notion is the stronger statement. -/
theorem hypertranscendental_of_hypertranscendentalOver {g : ι → ℂ → ℂ} {i₀ : ι}
    (h₀ : g i₀ = id) {f : ℂ → ℂ} (hf : HypertranscendentalOver g f) :
    GaloisForLFunctions.Hypertranscendental f :=
  fun hda => hf (differentiallyAlgebraicOver_of_differentiallyAlgebraic h₀ hda)

/-- The relative interface is inhabited over the coordinate base: Gamma is hypertranscendental
there. -/
theorem hypertranscendentalOver_coordinateBase_gamma :
    HypertranscendentalOver coordinateBase Complex.Gamma :=
  hypertranscendentalOver_coordinateBase_iff.2 hypertranscendental_gamma

end RelativeDifferentialAlgebraicity

end GaloisForLFunctions
