import GaloisForLFunctions.HTGeometry.PathShellFixedSeed
import GaloisForLFunctions.HTGeometry.PowerTailMomentDivergence

/-!
# The onset moments of the path-local shell diverge

The delay sector of the path-local Pauli shell carries a ninth-power floor: the shell probability
that the split synthesis cap survives through time `L` is at least a constant times `L^{-9}`.  In
shell-measure form that is a genuine tail bound for any onset time whose lateness is implied by
survival of the cap.

Chebyshev then turns the tail into a lower bound `A L^{p-9}` for every `p`-th moment, and the
family is unbounded as soon as `p > 9`, so every such moment of the onset time is infinite.  At the
boundary exponent nine the layer-cake formula does the same job, because the tail contributes an
integrand comparable to `1/t`.
-/

open MeasureTheory Metric Set Filter

namespace GaloisForLFunctions.HTGeometry

open _root_.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section OnsetMoments

variable {n : ℕ}

/-- The shell mass of an event is its probability times the total shell mass. -/
theorem toSphere_ge_of_pathShellProb_ge {A : Set (sphere (0 : PathShell n) 1)} {x : ℝ}
    (h : x ≤ pathShellProb A) :
    ENNReal.ofReal
        (x * (volume.toSphere (univ : Set (sphere (0 : PathShell n) 1))).toReal)
      ≤ volume.toSphere A := by
  have hpos := toSphere_pathShell_univ_pos (n := n)
  have hle : x * (volume.toSphere (univ : Set (sphere (0 : PathShell n) 1))).toReal
      ≤ (volume.toSphere A).toReal := by
    rw [pathShellProb, le_div_iff₀ hpos] at h
    exact h
  calc ENNReal.ofReal (x * (volume.toSphere (univ : Set (sphere (0 : PathShell n) 1))).toReal)
      ≤ ENNReal.ofReal ((volume.toSphere A).toReal) := ENNReal.ofReal_le_ofReal hle
    _ = volume.toSphere A := ENNReal.ofReal_toReal (toSphere_pathShell_ne_top A)

/-- **`(17)` in shell-measure form.**  The delay sector has shell mass at least a positive constant
times `L^{-9}` at every finite delay. -/
theorem exists_delay_floor_toSphere {Γ : Type*}
    (act : Γ → EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2))) →
      EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2))))
    (chi ψ : EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2)))) (hψ : ‖ψ‖ = 1)
    {eta eps : ℝ} {S : ℕ} (hmargin : eta < eps) (e : Fin (n + 1))
    (hcert : ∀ u : PathShell n, ∀ s : ℝ, ∃ w : List Γ, w.length ≤ S ∧
      dist (orbitState (pathHamiltonianCut u e) ψ s) (wordAct act w chi) ≤ eta) :
    ∃ A : ℝ, 0 < A ∧ ∀ L : ℝ, (eps - eta) / 3 ≤ L →
      ENNReal.ofReal (A * L ^ (-9 : ℝ))
        ≤ volume.toSphere (delayEvent act chi ψ eps S L) := by
  obtain ⟨c, hc, hfloor⟩ := exists_delay_floor act chi ψ hψ hmargin e hcert
  have hpos := toSphere_pathShell_univ_pos (n := n)
  refine ⟨c * (volume.toSphere (univ : Set (sphere (0 : PathShell n) 1))).toReal, by positivity, ?_⟩
  intro L hL
  have hLpos : 0 < L := lt_of_lt_of_le (by linarith) hL
  have hrw : c * (volume.toSphere (univ : Set (sphere (0 : PathShell n) 1))).toReal * L ^ (-9 : ℝ)
      = (c / L ^ 9) * (volume.toSphere (univ : Set (sphere (0 : PathShell n) 1))).toReal := by
    rw [Real.rpow_neg (le_of_lt hLpos), show ((9 : ℝ)) = ((9 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    field_simp
  rw [hrw]
  exact toSphere_ge_of_pathShellProb_ge (hfloor L hL)

/-- **`(18)` above the boundary.**  If lateness of the onset time follows from survival of the split
cap, every moment of order above nine is infinite. -/
theorem lintegral_onset_pow_eq_top {Γ : Type*}
    (act : Γ → EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2))) →
      EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2))))
    (chi ψ : EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2)))) (hψ : ‖ψ‖ = 1)
    {eta eps : ℝ} {S : ℕ} (hmargin : eta < eps) (e : Fin (n + 1))
    (hcert : ∀ u : PathShell n, ∀ s : ℝ, ∃ w : List Γ, w.length ≤ S ∧
      dist (orbitState (pathHamiltonianCut u e) ψ s) (wordAct act w chi) ≤ eta)
    (τ : sphere (0 : PathShell n) 1 → ℝ) {p : ℝ} (hp : 9 < p)
    (hτm : AEMeasurable (fun u => ENNReal.ofReal (τ u ^ p)) (volume.toSphere))
    (hτ : ∀ L : ℝ, 0 < L → delayEvent act chi ψ eps S L ⊆ {u | L < τ u}) :
    ∫⁻ u, ENNReal.ofReal (τ u ^ p) ∂(volume.toSphere) = ⊤ := by
  obtain ⟨A, hA, hfloor⟩ := exists_delay_floor_toSphere act chi ψ hψ hmargin e hcert
  set L₀ : ℝ := max ((eps - eta) / 3) 1 with hL₀
  have hL₀pos : 0 < L₀ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine lintegral_eq_top_of_unbounded_real (g := fun L => A * (max L L₀) ^ (p - 9)) ?_ ?_
  · intro L
    have hmax : L₀ ≤ max L L₀ := le_max_right _ _
    have hmaxpos : 0 < max L L₀ := lt_of_lt_of_le hL₀pos hmax
    have hcut : (eps - eta) / 3 ≤ max L L₀ := le_trans (le_max_left _ _) hmax
    have htail : ENNReal.ofReal (A * (max L L₀) ^ (-9 : ℝ))
        ≤ volume.toSphere {u | max L L₀ < τ u} :=
      le_trans (hfloor _ hcut) (measure_mono (hτ _ hmaxpos))
    exact moment_floor hτm (lt_trans (by norm_num) hp) hmaxpos htail
  · refine Filter.Tendsto.const_mul_atTop hA ?_
    refine Filter.Tendsto.comp (tendsto_rpow_atTop (by linarith)) ?_
    exact tendsto_atTop_mono (fun L => le_max_left L L₀) tendsto_id

/-- **`(18)` at the boundary exponent nine.**  The ninth moment itself is infinite. -/
theorem lintegral_onset_rpow_nine_eq_top {Γ : Type*}
    (act : Γ → EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2))) →
      EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2))))
    (chi ψ : EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2)))) (hψ : ‖ψ‖ = 1)
    {eta eps : ℝ} {S : ℕ} (hmargin : eta < eps) (e : Fin (n + 1))
    (hcert : ∀ u : PathShell n, ∀ s : ℝ, ∃ w : List Γ, w.length ≤ S ∧
      dist (orbitState (pathHamiltonianCut u e) ψ s) (wordAct act w chi) ≤ eta)
    (τ : sphere (0 : PathShell n) 1 → ℝ)
    (hτ0 : 0 ≤ᵐ[volume.toSphere] τ) (hτm : AEMeasurable τ (volume.toSphere))
    (hτ : ∀ L : ℝ, 0 < L → delayEvent act chi ψ eps S L ⊆ {u | L < τ u}) :
    ∫⁻ u, ENNReal.ofReal (τ u ^ (9 : ℝ)) ∂(volume.toSphere) = ⊤ := by
  obtain ⟨A, hA, hfloor⟩ := exists_delay_floor_toSphere act chi ψ hψ hmargin e hcert
  set L₀ : ℝ := max ((eps - eta) / 3) 1 with hL₀
  have hL₀pos : 0 < L₀ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine lintegral_rpow_eq_top_of_boundary_tail hA hL₀pos hτ0 hτm ?_
  intro t ht
  have htpos : 0 < t := lt_trans hL₀pos ht
  have hcut : (eps - eta) / 3 ≤ t := le_trans (le_max_left _ _) (le_of_lt ht)
  exact le_trans (hfloor t hcut) (measure_mono (hτ t htpos))

end OnsetMoments

end

end GaloisForLFunctions.HTGeometry
