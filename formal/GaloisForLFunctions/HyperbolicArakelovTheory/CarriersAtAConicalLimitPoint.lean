import GaloisForLFunctions.HyperbolicArakelovTheory.CarriersAlongAnEndOfBoundedSelfEnergy

/-!
# Carriers at a conical limit point

The end `∞` of the degree geodesic is a **conical limit point** of `Γ ⊂ SL₂(ℂ)` when the degree ray
returns infinitely often to a bounded neighbourhood of an orbit: for some `R` and infinitely many
degrees `M` there is `γ_M ∈ Γ` with `d(z_M, γ_M z_1) ≤ R`.

**Theorem** (`not_carrierSum_eq_torsion_of_conical`). If `Σ_{γ≠1} e^{−d(z_1, γz_1)/2} = S < ∞` and `∞`
is a conical limit point, no twisted carrier of `Γ` with weights `‖w‖ ≤ 1` carries the torsion kernel.

**Mechanism.** At a return, `d(γ_M z_1, gγ_M z_1) ≤ d(z_M, gz_M) + 2R` and conjugation by `γ_M`
permutes `Γ∖{1}`, so the self-energy of `z_M` is at most `e^R S` (`selfEnergy_le_of_near_orbit`);
`not_carrierSum_eq_torsion_of_selfEnergy` concludes.
-/

open Filter

noncomputable section

namespace GaloisForLFunctions.HyperbolicArakelovTheory

open SurfaceOfSpecZ ArithmeticEffectivityTheory

/-- **A degree point near an orbit point has self-energy `≤ e^R·(Poincaré sum)`.** If
`d(z_t, γz_1) ≤ R` with `γ ∈ Γ`, then `d(γz_1, gγz_1) ≤ d(z_t, gz_t) + 2R`, and conjugation by `γ`
permutes `Γ∖{1}`. -/
theorem selfEnergy_le_of_near_orbit {Γ : Subgroup SL2C}
    (hP : Summable fun i : Nontriv Γ => poincareWeight i.1) {t R : ℝ} (ht : 0 < t) {γ : SL2C}
    (hγ : γ ∈ Γ) (hR : h3Dist (degPoint t ht) (h3Act γ basePoint) ≤ R) :
    selfEnergy Γ t ≤ Real.exp R * ∑' i : Nontriv Γ, poincareWeight i.1 := by
  set x := degPoint t ht with hx
  set e := conjEquiv Γ hγ with he
  have hle : ∀ g : Nontriv Γ, rayWeight g.1 t ≤ Real.exp R * poincareWeight (e g).1 := by
    intro g
    rw [rayWeight_eq _ ht, ← hx, poincareWeight, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    -- `d(z_1, γ⁻¹gγ z_1) = d(γz_1, gγz_1)`
    have hconj : h3Dist basePoint (h3Act (e g).1 basePoint) =
        h3Dist (h3Act γ basePoint) (h3Act g.1 (h3Act γ basePoint)) := by
      rw [← h3Dist_h3Act γ basePoint]
      congr 1
      simp only [he, conjEquiv, Equiv.coe_fn_mk]
      rw [← h3Act_mul, ← h3Act_mul]
      congr 1
      group
    have h1 := h3Dist_triangle (h3Act γ basePoint) x (h3Act g.1 (h3Act γ basePoint))
    have h2 := h3Dist_triangle x (h3Act g.1 x) (h3Act g.1 (h3Act γ basePoint))
    rw [h3Dist_h3Act] at h2
    have h1' : h3Dist (h3Act γ basePoint) x = h3Dist x (h3Act γ basePoint) := h3Dist_comm _ _
    have h3 : h3Dist x (h3Act γ basePoint) ≤ R := hR
    linarith
  have hsum : Summable fun g : Nontriv Γ => Real.exp R * poincareWeight (e g).1 :=
    (e.summable_iff.mpr hP).mul_left _
  calc selfEnergy Γ t ≤ ∑' g : Nontriv Γ, Real.exp R * poincareWeight (e g).1 :=
        Summable.tsum_le_tsum hle (summable_rayWeight hP ht) hsum
    _ = Real.exp R * ∑' i : Nontriv Γ, poincareWeight i.1 := by
        rw [tsum_mul_left]
        congr 1
        exact e.tsum_eq fun i : Nontriv Γ => poincareWeight i.1

/-- **No carrier with a conical degree end carries the torsion** (B118′.2 at conical limit
points). Let `Γ ⊂ SL₂(ℂ)` have convergent Poincaré series at `½`, and let the degree ray return
infinitely often within `R` of `Γz_1`. For every weight `‖w‖ ≤ 1` on `Γ∖{1}` and every `κ ≠ 0`,
`Σ_{γ≠1} w(γ)·2πG_{1/2}(d(z_m, γz_n)) = κ·Λ(n/m)(n/m)^{−1/2}` fails. -/
theorem not_carrierSum_eq_torsion_of_conical {Γ : Subgroup SL2C}
    (hP : Summable fun i : Nontriv Γ => poincareWeight i.1) {R : ℝ}
    (hcon : ∀ N : ℕ, ∃ M : ℕ, ∃ hM : 0 < M, N ≤ M ∧
      ∃ γ ∈ Γ, h3Dist (natPoint M hM) (h3Act γ basePoint) ≤ R)
    {w : Nontriv Γ → ℂ} (hw : ∀ i, ‖w i‖ ≤ 1) {κ : ℂ} (hκ : κ ≠ 0) :
    ¬ ∀ m n : ℕ, 0 < m → 0 < n → m ≠ n →
      carrierSum (fun i : Nontriv Γ => i.1) w m n = κ * (weilPrimeKernel m n : ℂ) := by
  refine not_carrierSum_eq_torsion_of_selfEnergy hP (C := Real.exp R * ∑' i : Nontriv Γ,
    poincareWeight i.1) (frequently_atTop.mpr fun N => ?_) hw hκ
  obtain ⟨M, hM, hNM, γ, hγ, hR⟩ := hcon N
  exact ⟨M, hNM, selfEnergy_le_of_near_orbit hP (by exact_mod_cast hM) hγ hR⟩

end GaloisForLFunctions.HyperbolicArakelovTheory
