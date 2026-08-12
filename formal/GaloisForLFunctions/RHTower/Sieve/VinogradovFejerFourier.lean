import GaloisForLFunctions.RHTower.Sieve.VinogradovFejerMajorant

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

def vinogradovFejerCenteredCoordinate
    {N b k : ℕ}
    (l : Fin (vinogradovWideDifferenceBoxSize
      (vinogradovFejerRadius N b k))) : ℝ :=
  l.val - vinogradovFejerRadius N b k

theorem vinogradovFejerCenteredCoordinate_signature
    {N b k : ℕ} (hN : N ≠ 0) (j : Fin k)
    (ab : Fin (vinogradovFejerLength N b j) ×
      Fin (vinogradovFejerLength N b j)) :
    vinogradovFejerCenteredCoordinate
        (vinogradovFejerCoordinateSignature hN j ab) =
      (ab.1.val : ℝ) - ab.2.val := by
  have hcoord := vinogradovFejerCoordinateBound_le_radius (b := b) hN j
  have hb : ab.2.val ≤ 2 * vinogradovFejerCoordinateBound N b j := by
    have hbLt := ab.2.isLt
    unfold vinogradovFejerLength at hbLt
    omega
  have hbR : ab.2.val ≤ vinogradovFejerRadius N b k := hb.trans hcoord
  have hsub : ab.2.val ≤ ab.1.val + vinogradovFejerRadius N b k :=
    hbR.trans (Nat.le_add_left _ _)
  unfold vinogradovFejerCenteredCoordinate vinogradovFejerCoordinateSignature
  rw [Nat.cast_sub hsub]
  push_cast
  ring

theorem sum_comp_eq_sum_card_fiber_mul_complex
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (w : β → ℂ) :
    (∑ a : α, w (f a)) =
      ∑ b : β, (Fintype.card {a : α // f a = b} : ℂ) * w b := by
  rw [← Fintype.sum_fiberwise f (fun a => w (f a))]
  apply Finset.sum_congr rfl
  intro b _
  have hterm : ∀ i : {a : α // f a = b}, w (f i.1) = w b :=
    fun i => congrArg w i.2
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ]
  simp only [nsmul_eq_mul]

/-- One coordinate of the smooth Vinogradov majorant is exactly a Fejér
kernel.  The equality simultaneously records positivity, compact support,
and the phase-cancellation scale. -/
theorem sum_vinogradovFejerCoordinateWeight_mul_phase
    {N b k : ℕ} (hN : N ≠ 0) (j : Fin k) (x : ℝ) :
    (∑ l : Fin (vinogradovWideDifferenceBoxSize
        (vinogradovFejerRadius N b k)),
      (vinogradovFejerCoordinateWeight hN j l : ℂ) *
        finitePhaseChar (vinogradovFejerCenteredCoordinate l * x)) =
      (finiteFejerKernel (vinogradovFejerLength N b j) x : ℂ) := by
  let H := vinogradovFejerLength N b j
  let Q := Fin (vinogradovWideDifferenceBoxSize
    (vinogradovFejerRadius N b k))
  let A := Fin H × Fin H
  let sig : A → Q := vinogradovFejerCoordinateSignature hN j
  let phase : Q → ℂ := fun l =>
    finitePhaseChar (vinogradovFejerCenteredCoordinate l * x)
  calc
    (∑ l : Q, (vinogradovFejerCoordinateWeight hN j l : ℂ) * phase l) =
        ((2 / (H : ℝ) : ℝ) : ℂ) *
          ∑ l : Q, (Fintype.card {ab : A // sig ab = l} : ℂ) * phase l := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      unfold vinogradovFejerCoordinateWeight
      simp only [Complex.ofReal_mul]
      dsimp [H, A, sig, phase]
      ring
    _ = ((2 / (H : ℝ) : ℝ) : ℂ) * ∑ ab : A, phase (sig ab) := by
      rw [sum_comp_eq_sum_card_fiber_mul_complex sig phase]
    _ = ∑ ab : A, ((2 / (H : ℝ) : ℝ) : ℂ) *
        finitePhaseChar ((((ab.1.val : ℝ) - ab.2.val) * x)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ab _
      congr 1
      dsimp [phase, sig, A, H, Q]
      rw [vinogradovFejerCenteredCoordinate_signature]
    _ = (finiteFejerKernel H x : ℂ) := by
      simpa [H, A] using (finiteFejerKernel_expansion H x).symm

/-- Tensorized Fejér identity over the full exact power-difference box.
This is the algebraic heart of the second Hölder step in MV24.7. -/
theorem sum_vinogradovFejerWeight_mul_phase
    {N b k : ℕ} (hN : N ≠ 0) (x : Fin k → ℝ) :
    (∑ l : Fin k → Fin (vinogradovWideDifferenceBoxSize
        (vinogradovFejerRadius N b k)),
      (vinogradovFejerWeight hN l : ℂ) *
        finitePhaseChar
          (∑ j : Fin k, vinogradovFejerCenteredCoordinate (l j) * x j)) =
      ∏ j : Fin k,
        (finiteFejerKernel (vinogradovFejerLength N b j) (x j) : ℂ) := by
  let Q := Fin (vinogradovWideDifferenceBoxSize
    (vinogradovFejerRadius N b k))
  let term : (j : Fin k) → Q → ℂ := fun j l =>
    (vinogradovFejerCoordinateWeight hN j l : ℂ) *
      finitePhaseChar (vinogradovFejerCenteredCoordinate l * x j)
  calc
    (∑ l : Fin k → Q, (vinogradovFejerWeight hN l : ℂ) *
        finitePhaseChar
          (∑ j : Fin k, vinogradovFejerCenteredCoordinate (l j) * x j)) =
      ∑ l : Fin k → Q, ∏ j : Fin k, term j (l j) := by
        apply Finset.sum_congr rfl
        intro l _
        unfold vinogradovFejerWeight term
        rw [Complex.ofReal_prod, Finset.prod_mul_distrib, prod_finitePhaseChar]
    _ = ∏ j : Fin k, ∑ l : Q, term j l := by
      exact (Fintype.prod_sum term).symm
    _ = ∏ j : Fin k,
        (finiteFejerKernel (vinogradovFejerLength N b j) (x j) : ℂ) := by
      apply Finset.prod_congr rfl
      intro j _
      exact sum_vinogradovFejerCoordinateWeight_mul_phase hN j (x j)

end

end RHTower.Sieve
