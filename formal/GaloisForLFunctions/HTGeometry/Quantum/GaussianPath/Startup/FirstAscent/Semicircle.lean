import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralEnclosingArc

/-! # Exact empty-circuit error before the spectral phases wrap -/
open Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent
noncomputable section

/-- The enclosing circular arc agrees with the ordinary range when that
range is at most π. Its midpoint is a minimax center, and the two
extreme phases force its radius. -/
theorem arc_eq_span {I : Type*} [Fintype I] [Nonempty I] (θ : I→ℝ) (a b : I)
    (ha : ∀ j, θ a ≤ θ j) (hb : ∀ j, θ j ≤ θ b) (hs : θ b-θ a ≤ π) :
    spectralEnclosingArcLength θ=θ b-θ a := by
  have hab := ha b
  let c := (θ a+θ b)/2
  let R := (θ b-θ a)/2
  have hr (j) : circDist (θ j) c ≤ R := by
    apply (circDist_le (θ j) c 0).trans
    simp only [Int.cast_zero,mul_zero,add_zero]
    exact abs_le.mpr ⟨by dsimp [c,R]; linarith only [ha j],
      by dsimp [c,R]; linarith only [hb j]⟩
  have hu := spectralEnclosingArcLength_le_twice_radius θ c R hr
  have hdist : circDist (θ b) (θ a)=θ b-θ a := by
    rw [circDist_eq_abs_of_le_pi (by simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hs),
      abs_of_nonneg (sub_nonneg.mpr hab)]
  obtain ⟨d,hd⟩ := exists_spectralEnclosingArc_center θ
  have hl := circDist_triangle (θ b) d (θ a)
  rw [hdist,circDist_comm d] at hl
  dsimp only [R] at hu
  linarith only [hu,hl,hd a,hd b]

/-- Before the phases cover a semicircle the unwrapped energy diameter
is exactly the length of their shortest enclosing circular arc. -/
theorem initial_arc {n : ℕ} (H : selfAdjoint (Matrix (Fin n→Bool) (Fin n→Bool) ℂ)) {t : ℝ}
    (ht : 0≤t) (hs : t*circuitHamiltonianSpectralWidth H ≤ π) :
    orbitSpectralEnclosingArcLength H t=t*circuitHamiltonianSpectralWidth H := by
  let E := H.2.isHermitian.eigenvalues
  obtain ⟨a,_,ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty E
  obtain ⟨b,_,hb⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty E
  have he : circuitHamiltonianSpectralWidth H=E a-E b := by
    change Finset.univ.sup' Finset.univ_nonempty E-Finset.univ.inf' Finset.univ_nonempty E=_
    rw [ha,hb]
  have hθ : -(t*E b) - -(t*E a)=t*circuitHamiltonianSpectralWidth H := by rw [he]; ring
  have h := arc_eq_span (fun j => -(t*E j)) a b (fun j => by
    apply neg_le_neg
    apply mul_le_mul_of_nonneg_left _ ht
    exact (Finset.le_sup' E (Finset.mem_univ j)).trans_eq ha) (fun j => by
    apply neg_le_neg
    apply mul_le_mul_of_nonneg_left _ ht
    exact hb.symm.le.trans (Finset.inf'_le E (Finset.mem_univ j))) (hθ.le.trans hs)
  exact h.trans hθ

/-- The zero-gate chord throughout the initial spectral semicircle. -/
theorem empty_distance {n : ℕ} (H : selfAdjoint (Matrix (Fin n→Bool) (Fin n→Bool) ℂ)) {t : ℝ}
    (ht : 0≤t) (hs : t*circuitHamiltonianSpectralWidth H ≤ π) :
    orbitCircuitDistance H 0 t=2*sin (t*circuitHamiltonianSpectralWidth H/4) := by
  rw [orbitCircuitDistance_zeroGate_eq_enclosingArc,initial_arc H ht hs]

#print axioms empty_distance
end
end GaloisForLFunctions.HTGeometry.FirstAscent
