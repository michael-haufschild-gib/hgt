/-
# Explicit finite grid cover for Bourgain phase space

An explicit product grid covers a large sup-norm cube by translated cubes.
The grid has exactly `(m + 1)^(4 : ℕ)` centers, so local moment estimates sum with
that precise combinatorial loss.
-/
import GaloisForLFunctions.RHTower.BourgainFiniteCubeCover

open MeasureTheory

namespace RHTower

noncomputable section

def bourgainGridCenter1D
    (n : ℕ) (r : ℝ) (k : Fin n) : ℝ :=
  (2 * (k : ℝ) + 1 - (n : ℝ)) * r

theorem exists_bourgainGridCenter1D
    (m : ℕ) {r x : ℝ}
    (hx : |x| ≤ ((m + 1 : ℕ) : ℝ) * r) :
    ∃ k : Fin (m + 1),
      |x - bourgainGridCenter1D (m + 1) r k| ≤ r := by
  induction m generalizing x with
  | zero =>
      refine ⟨0, ?_⟩
      simpa [bourgainGridCenter1D] using hx
  | succ m ih =>
      have hxb := (abs_le.mp hx)
      have htotal :
          (((m + 1 + 1 : ℕ) : ℝ) * r) =
            ((m + 1 : ℕ) : ℝ) * r + r := by
        push_cast
        ring
      rw [htotal] at hxb
      by_cases hleft :
          x ≤ -((m + 1 : ℕ) : ℝ) * r + r
      · refine ⟨0, ?_⟩
        have hc0 :
            bourgainGridCenter1D (m + 1 + 1) r
                (0 : Fin (m + 1 + 1)) =
              -((m + 1 : ℕ) : ℝ) * r := by
          unfold bourgainGridCenter1D
          simp only [Fin.val_zero, Nat.cast_zero, mul_zero, zero_add]
          push_cast
          ring
        rw [hc0, abs_le]
        constructor <;> linarith
      · have hxshift :
          |(x - r)| ≤ ((m + 1 : ℕ) : ℝ) * r := by
          rw [abs_le]
          constructor
          · have hleft' := (lt_of_not_ge hleft).le
            linarith
          · linarith
        obtain ⟨k, hk⟩ := ih hxshift
        refine ⟨Fin.succ k, ?_⟩
        have hcenter :
            bourgainGridCenter1D (m + 2) r (Fin.succ k) =
              bourgainGridCenter1D (m + 1) r k + r := by
          unfold bourgainGridCenter1D
          norm_num [Fin.val_succ]
          ring
        rw [hcenter]
        have harg :
            x - (bourgainGridCenter1D (m + 1) r k + r) =
              (x - r) - bourgainGridCenter1D (m + 1) r k := by
          ring
        rw [harg]
        exact hk

def bourgainGridCenter
    (n : ℕ) (r : ℝ) (k : Fin 4 → Fin n) :
    BourgainPhaseSpace :=
  fun i => bourgainGridCenter1D n r (k i)

theorem bourgain_normCube_subset_gridCover
    (m : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    {x : BourgainPhaseSpace |
        ‖x‖ ≤ ((m + 1 : ℕ) : ℝ) * r} ⊆
      ⋃ k : Fin 4 → Fin (m + 1),
        bourgainTranslatedNormCube
          (bourgainGridCenter (m + 1) r k) r := by
  intro x hx
  have hxcoord (i : Fin 4) :
      |x i| ≤ ((m + 1 : ℕ) : ℝ) * r := by
    rw [← Real.norm_eq_abs]
    exact (norm_apply_le_norm_bourgainPhaseSpace x i).trans hx
  choose k hk using fun i =>
    exists_bourgainGridCenter1D m (hxcoord i)
  apply Set.mem_iUnion.2
  refine ⟨k, ?_⟩
  rw [mem_bourgainTranslatedNormCube_iff]
  rw [pi_norm_le_iff_of_nonneg hr]
  intro i
  rw [Real.norm_eq_abs]
  exact hk i

theorem card_bourgainGridIndex
    (n : ℕ) :
    Fintype.card (Fin 4 → Fin n) = n ^ (4 : ℕ) := by
  simp

theorem setLIntegral_normCube_le_grid_sum
    (m : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (f : BourgainPhaseSpace → ENNReal) {B : ENNReal}
    (hlocal :
      ∀ k : Fin 4 → Fin (m + 1),
        (∫⁻ x in
          bourgainTranslatedNormCube
            (bourgainGridCenter (m + 1) r k) r,
          f x) ≤ B) :
    (∫⁻ x in
      {x : BourgainPhaseSpace |
        ‖x‖ ≤ ((m + 1 : ℕ) : ℝ) * r},
      f x) ≤
        (((m + 1 : ℕ) ^ (4 : ℕ) : ℕ) : ENNReal) * B := by
  simpa [card_bourgainGridIndex] using
    setLIntegral_le_card_mul_of_finite_cover
      {x : BourgainPhaseSpace |
        ‖x‖ ≤ ((m + 1 : ℕ) : ℝ) * r}
      (fun k : Fin 4 → Fin (m + 1) =>
        bourgainTranslatedNormCube
          (bourgainGridCenter (m + 1) r k) r)
      f (bourgain_normCube_subset_gridCover m hr) hlocal

end

end RHTower
