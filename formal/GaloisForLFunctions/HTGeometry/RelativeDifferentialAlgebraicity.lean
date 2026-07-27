import GaloisForLFunctions.HTGeometry.DifferentialOrder

/-!
# Differential algebraicity relative to a base family

`DifferentialOrder` defines `DifferentiallyAlgebraic f` by a polynomial relation among `z` and the
jets of `f` with **constant** coefficients — differential algebraicity over `ℂ[z]`.  The
frequency-criterion programme needs the *relative* notion: differential algebraicity over a larger
differential base, for instance a field containing `Γ`.  Until that notion exists, statements about
"differential algebraicity over the Gamma field" cannot be written down, and a criterion phrased with
an opaque `Prop` for the hypothesis is not a statement about anything.

This file supplies the relative notion.  A base is a family `g : ι → ℂ → ℂ`, and `f` is
differentially algebraic over it when some nonzero polynomial in the base values and the jets of `f`
vanishes identically:

`∃ P ≠ 0, ∀ z, P((g i z)ᵢ, (f⁽ʲ⁾ z)ⱼ) = 0`.

The two laws proved here are the ones the programme uses:

* enlarging the base can only make differential algebraicity easier (`mono`), so
* hypertranscendence over a **larger** base is a **stronger** statement (`HypertranscendentalOver.mono`).

The second is why "hypertranscendental over the Gamma field" is worth stating at all: it is strictly
stronger than the classical Hölder conclusion, which is hypertranscendence over `ℂ[z]`.
-/

open MvPolynomial

namespace GaloisForLFunctions

variable {ι κ : Type*}

/-- `f` satisfies a nonzero algebraic differential relation of order at most `n` whose coefficients
are polynomial in the base family `g`. -/
def DifferentiallyAlgebraicOverOfOrder (g : ι → ℂ → ℂ) (f : ℂ → ℂ) (n : ℕ) : Prop :=
  ∃ P : MvPolynomial (ι ⊕ Fin (n + 1)) ℂ, P ≠ 0 ∧
    ∀ z : ℂ, MvPolynomial.eval
      (Sum.elim (fun i => g i z) fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) P = 0

/-- Differential algebraicity over a base family: some finite order works. -/
def DifferentiallyAlgebraicOver (g : ι → ℂ → ℂ) (f : ℂ → ℂ) : Prop :=
  ∃ n, DifferentiallyAlgebraicOverOfOrder g f n

/-- Hypertranscendence relative to a base family. -/
def HypertranscendentalOver (g : ι → ℂ → ℂ) (f : ℂ → ℂ) : Prop :=
  ¬ DifferentiallyAlgebraicOver g f

/-- **Enlarging the base preserves differential algebraicity.**  If every member of the base `g` is a
member of the base `h`, indexed injectively, a relation over `g` renames to a relation over `h`. -/
theorem DifferentiallyAlgebraicOverOfOrder.mono
    {g : ι → ℂ → ℂ} {h : κ → ℂ → ℂ} {e : ι → κ}
    (he : Function.Injective e) (hbase : ∀ i, h (e i) = g i)
    {f : ℂ → ℂ} {n : ℕ} (hda : DifferentiallyAlgebraicOverOfOrder g f n) :
    DifferentiallyAlgebraicOverOfOrder h f n := by
  obtain ⟨P, hP, hzero⟩ := hda
  refine ⟨MvPolynomial.rename (Sum.map e id) P, ?_, ?_⟩
  · intro hcon
    apply hP
    have hinj : Function.Injective (Sum.map e (id : Fin (n + 1) → Fin (n + 1))) :=
      Function.Injective.sumMap he Function.injective_id
    have := MvPolynomial.rename_injective (R := ℂ) _ hinj
    apply this
    simpa using hcon
  · intro z
    rw [MvPolynomial.eval_rename]
    have hcomp :
        (Sum.elim (fun k => h k z) fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) ∘
            Sum.map e (id : Fin (n + 1) → Fin (n + 1))
          = Sum.elim (fun i => g i z) fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z := by
      funext v
      cases v with
      | inl i => simp [hbase i]
      | inr j => simp
    rw [hcomp]
    exact hzero z

theorem DifferentiallyAlgebraicOver.mono
    {g : ι → ℂ → ℂ} {h : κ → ℂ → ℂ} {e : ι → κ}
    (he : Function.Injective e) (hbase : ∀ i, h (e i) = g i)
    {f : ℂ → ℂ} (hda : DifferentiallyAlgebraicOver g f) :
    DifferentiallyAlgebraicOver h f := by
  obtain ⟨n, hn⟩ := hda
  exact ⟨n, hn.mono he hbase⟩

/-- **Hypertranscendence over a larger base is stronger.**  This is the reason the relative notion is
needed: hypertranscendence over a base containing `Γ` implies hypertranscendence over every smaller
base, in particular over `ℂ[z]`, but not conversely. -/
theorem HypertranscendentalOver.mono
    {g : ι → ℂ → ℂ} {h : κ → ℂ → ℂ} {e : ι → κ}
    (he : Function.Injective e) (hbase : ∀ i, h (e i) = g i)
    {f : ℂ → ℂ} (hht : HypertranscendentalOver h f) :
    HypertranscendentalOver g f :=
  fun hda => hht (hda.mono he hbase)

end GaloisForLFunctions
