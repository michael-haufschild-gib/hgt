import GaloisForLFunctions.HTGeometry.AIRResponseCore

/-!
# Exact finite shadow recovery for the attraction–indifference–repulsion response

The threshold-shadow mechanism of Araújo, arXiv:2609.05560, Theorems 7–8 admits an explicit
finite-probe realization on a separated grid. Three probes at each visible attraction
threshold cancel the smooth background and isolate that atom's weight. All nodes, threshold
separations, and probe positions are constructed, rather than supplied as hypotheses.
-/
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- AIR response with attraction radius one half, repulsion radius one, and arbitrary gain. -/
def finiteShadowAIR (eta u : ℝ) : ℝ :=
  airResponse (1 / 2) 1 eta u

/-- Grid spacing keeps every other response threshold away from the selected probes. -/
def finiteShadowSpacing (n : ℕ) : ℝ := 1 / (8 * (n + 1 : ℝ))

def finiteShadowNode {n : ℕ} (i : Fin (n + 1)) : ℝ := (i : ℕ) * finiteShadowSpacing n

/-- The three probes sit at the shadow and one quarter and one half grid step to its right. -/
def finiteShadowProbe {n : ℕ} (i : Fin (n + 1)) (k : Fin 3) : ℝ :=
  finiteShadowNode i - 1 / 2 + (k : ℕ) * finiteShadowSpacing n / 4

theorem finiteShadowSpacing_pos (n : ℕ) : 0 < finiteShadowSpacing n := by
  unfold finiteShadowSpacing
  positivity

theorem finiteShadowSpacing_scale (n : ℕ) : 8 * (n + 1 : ℝ) * finiteShadowSpacing n = 1 := by
  unfold finiteShadowSpacing
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp

theorem finiteShadowSpacing_le (n : ℕ) : finiteShadowSpacing n ≤ 1 / 8 := by
  have hs := finiteShadowSpacing_pos n
  have he := finiteShadowSpacing_scale n
  have hn : (0 : ℝ) ≤ n := by positivity
  nlinarith

theorem finiteShadowNode_bounds {n : ℕ} (i : Fin (n + 1)) :
    0 ≤ finiteShadowNode i ∧ finiteShadowNode i < 1 / 8 := by
  have hs := finiteShadowSpacing_pos n
  have he := finiteShadowSpacing_scale n
  have hi : ((i : ℕ) : ℝ) < n + 1 := by exact_mod_cast i.isLt
  have hi0 : (0 : ℝ) ≤ (i : ℕ) := by positivity
  unfold finiteShadowNode
  constructor
  · positivity
  · nlinarith

/-- Every selected source-probe displacement lies below the repulsion threshold. -/
theorem finiteShadowProbe_displacement_bounds {n : ℕ} (i j : Fin (n + 1)) (k : Fin 3) :
    0 < finiteShadowNode j - finiteShadowProbe i k ∧
      finiteShadowNode j - finiteShadowProbe i k < 1 := by
  have hi := finiteShadowNode_bounds i
  have hj := finiteShadowNode_bounds j
  have hs := finiteShadowSpacing_pos n
  have hsle := finiteShadowSpacing_le n
  have hk : ((k : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (show (k : ℕ) ≤ 2 by omega)
  have hk0 : (0 : ℝ) ≤ (k : ℕ) := by positivity
  unfold finiteShadowProbe
  constructor <;> nlinarith

/-- Each atom has an isolated affine-versus-zero response at its three probes. -/
theorem finiteShadowAIR_grid_response {n : ℕ} (eta : ℝ)
    (i j : Fin (n + 1)) (k : Fin 3) :
    finiteShadowAIR eta (finiteShadowNode j - finiteShadowProbe i k) =
      if j < i then finiteShadowNode j - finiteShadowProbe i k
      else if j = i ∧ k ≠ 0 then finiteShadowNode j - finiteShadowProbe i k else 0 := by
  have hb := finiteShadowProbe_displacement_bounds i j k
  have hs := finiteShadowSpacing_pos n
  have hk : ((k : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (show (k : ℕ) ≤ 2 by omega)
  have hk0 : (0 : ℝ) ≤ (k : ℕ) := by positivity
  unfold finiteShadowAIR airResponse
  rw [abs_of_pos hb.1]
  by_cases hji : j < i
  · have hjiR : ((j : ℕ) : ℝ) + 1 ≤ (i : ℕ) := by
      exact_mod_cast (show (j : ℕ) + 1 ≤ (i : ℕ) from hji)
    have hlt : finiteShadowNode j - finiteShadowProbe i k < 1 / 2 := by
      simp only [finiteShadowProbe, finiteShadowNode]
      nlinarith
    rw [if_pos hlt]
    simp [hji]
  · by_cases heq : j = i
    · subst j
      by_cases hkz : k = 0
      · subst k
        norm_num [finiteShadowProbe]
      · have hkpos : (0 : ℝ) < (k : ℕ) := by
          exact_mod_cast (show 0 < (k : ℕ) by omega)
        have hlt : finiteShadowNode i - finiteShadowProbe i k < 1 / 2 := by
          unfold finiteShadowProbe
          nlinarith
        rw [if_pos hlt]
        simp [hkz]
    · have hjiR : ((i : ℕ) : ℝ) + 1 ≤ (j : ℕ) := by
        exact_mod_cast (show (i : ℕ) + 1 ≤ (j : ℕ) by omega)
      have hnlt : ¬ finiteShadowNode j - finiteShadowProbe i k < 1 / 2 := by
        simp only [finiteShadowProbe, finiteShadowNode]
        nlinarith
      rw [if_neg hnlt, if_pos hb.2]
      simp [hji, heq]

/-- A three-probe stencil isolates the selected atom, independently of the repulsive gain. -/
theorem finiteShadowAIR_atom_stencil {n : ℕ} (eta : ℝ) (i j : Fin (n + 1)) :
    finiteShadowAIR eta (finiteShadowNode j - finiteShadowProbe i 2) -
      2 * finiteShadowAIR eta (finiteShadowNode j - finiteShadowProbe i 1) +
        finiteShadowAIR eta (finiteShadowNode j - finiteShadowProbe i 0) =
          if j = i then -(1 / 2 : ℝ) else 0 := by
  simp only [finiteShadowAIR_grid_response]
  by_cases hji : j < i
  · have hne : j ≠ i := ne_of_lt hji
    simp [hji, hne, finiteShadowProbe]
    ring
  · by_cases heq : j = i
    · subst j
      simp [finiteShadowProbe]
      ring
    · simp [hji, heq]

/-- Every weight of an arbitrary finite signed grid packet is recovered from three force probes. -/
theorem finiteShadowAIR_force_stencil {n : ℕ} (eta : ℝ) (w : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    finiteResponseForce (finiteShadowAIR eta) w finiteShadowNode (finiteShadowProbe i 2) -
      2 * finiteResponseForce (finiteShadowAIR eta) w finiteShadowNode (finiteShadowProbe i 1) +
        finiteResponseForce (finiteShadowAIR eta) w finiteShadowNode (finiteShadowProbe i 0) =
          -(1 / 2 : ℝ) * w i := by
  unfold finiteResponseForce
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  calc
    _ = ∑ j, w j * (if j = i then -(1 / 2 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← finiteShadowAIR_atom_stencil eta i j]
      ring
    _ = _ := by simp; ring

/-- The constructed finite probe panel determines the entire source weight vector. -/
theorem finiteShadowAIR_probe_identifiability {n : ℕ} (eta : ℝ)
    (w v : Fin (n + 1) → ℝ) :
    (∀ (i : Fin (n + 1)) (k : Fin 3),
      finiteResponseForce (finiteShadowAIR eta) w finiteShadowNode (finiteShadowProbe i k) =
        finiteResponseForce (finiteShadowAIR eta) v finiteShadowNode (finiteShadowProbe i k)) ↔
          w = v := by
  constructor
  · intro h
    funext i
    have hw := finiteShadowAIR_force_stencil eta w i
    have hv := finiteShadowAIR_force_stencil eta v i
    rw [h i 2, h i 1, h i 0] at hw
    linarith
  · rintro rfl i k
    rfl

/-- The force values on the constructed finite recovery panel. -/
def finiteShadowForcePanel {n : ℕ} (eta : ℝ) (w : Fin (n + 1) → ℝ) :
    Fin (n + 1) × Fin 3 → ℝ :=
  fun p => finiteResponseForce (finiteShadowAIR eta) w finiteShadowNode
    (finiteShadowProbe p.1 p.2)

/-- Uniform force error bounds every individual recovered mass error. -/
theorem finiteShadow_mass_error_bound {n : ℕ} (eta : ℝ)
    (w v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    |w i - v i| ≤ 8 * ‖finiteShadowForcePanel eta w - finiteShadowForcePanel eta v‖ := by
  let D := finiteShadowForcePanel eta w - finiteShadowForcePanel eta v
  have h (k : Fin 3) : |D (i, k)| ≤ ‖D‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm D (i, k)
  have he : D (i, 2) - 2 * D (i, 1) + D (i, 0) = -(1 / 2 : ℝ) * (w i - v i) := by
    dsimp [D, finiteShadowForcePanel]
    linear_combination finiteShadowAIR_force_stencil eta w i -
      finiteShadowAIR_force_stencil eta v i
  have h0 := abs_le.mp (h 0)
  have h1 := abs_le.mp (h 1)
  have h2 := abs_le.mp (h 2)
  change |w i - v i| ≤ 8 * ‖D‖
  rw [abs_le]
  constructor <;> linarith

/-- The inverse bound controls half the complete mass-vector ℓ¹ error. -/
theorem finiteShadow_half_l1_error_bound {n : ℕ} (eta : ℝ)
    (w v : Fin (n + 1) → ℝ) :
    (∑ i, |w i - v i|) / 2 ≤
      4 * (n + 1 : ℝ) * ‖finiteShadowForcePanel eta w - finiteShadowForcePanel eta v‖ := by
  have h := Finset.sum_le_sum (fun (i : Fin (n + 1)) (_ : i ∈ Finset.univ) =>
    finiteShadow_mass_error_bound eta w v i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one] at h
  linarith

/-- Deleting any atom of the uniform source incurs a strictly positive force-error floor. -/
theorem finiteShadow_uniform_deletion_floor {n : ℕ} (eta : ℝ)
    (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    1 / (8 * (n + 1 : ℝ)) ≤
      ‖finiteShadowForcePanel eta (fun _ : Fin (n + 1) => 1 / (n + 1 : ℝ)) -
        finiteShadowForcePanel eta (Function.update v i 0)‖ := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have h := finiteShadow_mass_error_bound eta
    (fun _ : Fin (n + 1) => 1 / (n + 1 : ℝ)) (Function.update v i 0) i
  simp only [Function.update_self, sub_zero, abs_of_pos (one_div_pos.mpr hn)] at h
  have he : 1 / (8 * (n + 1 : ℝ)) = (1 / (n + 1 : ℝ)) / 8 := by
    field_simp
  rw [he]
  linarith

/-- The constructed recovery grid has distinct physical source positions at every size. -/
theorem finiteShadowNode_injective (n : ℕ) :
    Function.Injective (finiteShadowNode : Fin (n + 1) → ℝ) := by
  intro i j h
  unfold finiteShadowNode at h
  apply Fin.ext
  exact_mod_cast mul_right_cancel₀ (finiteShadowSpacing_pos n).ne' h

/-- Every recovery probe stays strictly inside the paper's recipient interval. -/
theorem finiteShadowProbe_in_opinion_interval {n : ℕ} (i : Fin (n + 1)) (k : Fin 3) :
    -1 < finiteShadowProbe i k ∧ finiteShadowProbe i k < 1 := by
  have hi := finiteShadowNode_bounds i
  have hs := finiteShadowSpacing_pos n
  have hsle := finiteShadowSpacing_le n
  have hk : ((k : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (show (k : ℕ) ≤ 2 by omega)
  have hk0 : (0 : ℝ) ≤ (k : ℕ) := by positivity
  unfold finiteShadowProbe
  constructor <;> nlinarith


end
end GaloisForLFunctions.HTGeometry
