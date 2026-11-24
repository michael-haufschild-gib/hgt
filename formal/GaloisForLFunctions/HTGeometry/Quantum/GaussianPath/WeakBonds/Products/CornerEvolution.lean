import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.Products.FrozenPhases
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.Products.EnergyRectangle

/-! # The evolution near two erased interactions -/

open Finset Matrix Filter Set Metric Topology Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds.Products
noncomputable section

private theorem product_error {A : Type*} [NormedRing A] (a b c x y z : A) {M h : ℝ}
    (hx : ‖x‖≤M) (hy : ‖y‖≤M) (hb : ‖b‖≤M) (hc : ‖c‖≤M)
    (ha' : ‖a-x‖≤h) (hb' : ‖b-y‖≤h) (hc' : ‖c-z‖≤h) :
    ‖a*b*c-x*y*z‖≤3*M^2*h := by
  have hM := (norm_nonneg x).trans hx
  have hh := (norm_nonneg (a-x)).trans ha'
  have h₁ := (norm_mul_le ((a-x)*b) c).trans (mul_le_mul ((norm_mul_le _ _).trans
    (mul_le_mul ha' hb (norm_nonneg _) hh)) hc (norm_nonneg _) (mul_nonneg hh hM))
  have h₂ := (norm_mul_le (x*(b-y)) c).trans (mul_le_mul ((norm_mul_le _ _).trans
    (mul_le_mul hx hb' (norm_nonneg _) hM)) hc (norm_nonneg _) (mul_nonneg hM hh))
  have h₃ := (norm_mul_le (x*y) (c-z)).trans (mul_le_mul ((norm_mul_le _ _).trans
    (mul_le_mul hx hy (norm_nonneg _) hM)) hc' (norm_nonneg _) (mul_nonneg hM hM))
  rw [show a*b*c-x*y*z=(a-x)*b*c+x*(b-y)*c+x*y*(c-z) by noncomm_ring]
  linarith only [norm_add_le ((a-x)*b*c+x*(b-y)*c) (x*y*(c-z)),
    norm_add_le ((a-x)*b*c) (x*(b-y)*c),h₁,h₂,h₃]

/-- At a simple Hermitian pencil, the three proper corners of a
coefficient rectangle approximate the fourth evolution. Freezing all
four eigenspaces costs an arbitrarily small constant independent of
time. The remaining phase error costs the product of the two shifts. -/
theorem corner_evolution {p D : ℕ} {P : Fin p→Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ i, (P i).IsHermitian) {a : Fin p→ℝ}
    (ha : Function.Injective (isHermitian_spectralEnsembleMatrix hP a).eigenvalues)
    {δ : ℝ} (hδ : 0<δ) :
    ∃ r>0, ∃ C≥(0:ℝ), ∀ x u v : Fin p→ℝ, x∈ball a r → x+u∈ball a r →
      x+v∈ball a r → x+v+u∈ball a r → ∀ t : ℝ,
      let U := fun (y : Fin p→ℝ) (s : ℝ) => unitaryEvolution (spectralEnsembleMatrix P y) s
      ‖U (x+v+u) t-U (x+u) t*U x (-t)*U (x+v) t‖≤δ+C*|t|*‖u‖*‖v‖ := by
  let H := spectralEnsembleMatrix P
  let E := sortedEnsembleSpectrum hP
  let A (x : Fin p→ℝ) (t : ℝ) := frozenEvolution (H a) (E a) (E x) t
  let U (x : Fin p→ℝ) (t : ℝ) := unitaryEvolution (H x) t
  let m := projectorMass (H a) (E a)
  let M := m+1
  have hm : 0≤m := sum_nonneg fun _ _ => norm_nonneg _
  have hM : 0<M := add_pos_of_nonneg_of_pos hm zero_lt_one
  let h := min 1 (δ/(1+3*M^2))
  have hd : 0<1+3*M^2 := by positivity
  have hh : 0<h := lt_min zero_lt_one (div_pos hδ hd)
  have hsmall := (le_div_iff₀ hd).mp (min_le_right 1 (δ/(1+3*M^2)))
  have hs : Function.Injective (E a) := injective_sortedTuple ha
  have hE : Continuous E := continuous_sortedEnsembleSpectrum hP
  have hH : Continuous H := continuous_spectralEnsembleMatrix P
  have hb (y : Fin p→ℝ) : ∃ e, IsOrthoEigenBasis (H y) e (E y) :=
    ⟨_,(isOrthoEigenBasis_hermitian _ (isHermitian_spectralEnsembleMatrix hP y)).reindex
      (Tuple.sort (isHermitian_spectralEnsembleMatrix hP y).eigenvalues)⟩
  have hopen : ∀ᶠ y in 𝓝 a, Function.Injective (E y) := by
    have hpair (i j : Fin D) : ∀ᶠ y in 𝓝 a, i≠j → E y i≠E y j := by
      by_cases h : i=j
      · exact Eventually.of_forall fun _ h' => (h' h).elim
      exact (((continuous_apply i).comp hE).continuousAt.eventually_ne
        ((continuous_apply j).comp hE).continuousAt (hs.ne h)).mono fun _ he _ => he
    filter_upwards [Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hpair i))] with y hy
    exact fun i j h => by_contra fun h' => hy i j h' h
  have happrox : ∀ᶠ y in 𝓝 a, ∀ t, ‖U y t-A y t‖≤h := by
    filter_upwards [hopen,uniform_freezing hH hE hs hh] with y hi hf
    obtain ⟨e,he⟩ := hb y
    intro t
    change ‖unitaryEvolution (H y) t-A y t‖≤h
    rw [evolution_lines he hi]
    exact (hf t).le
  obtain ⟨r,hr,hr'⟩ := Metric.mem_nhds_iff.mp happrox
  obtain ⟨s,hs',C,hC,hrect⟩ := sorted_rectangle hP ha
  refine ⟨min r s,lt_min hr hs',C*m,mul_nonneg hC hm,?_⟩
  intro x u v h₀ hu hv huv t
  intro _
  have inside {y : Fin p→ℝ} (hy : y∈ball a (min r s)) :
      (∀ t, ‖U y t-A y t‖≤h) ∧ y∈ball a s :=
    ⟨hr' (ball_subset_ball (min_le_left ..) hy),ball_subset_ball (min_le_right ..) hy⟩
  have hnorm {y : Fin p→ℝ} (hy : y∈ball a (min r s)) (t : ℝ) : ‖U y t‖≤M := by
    have h := norm_sub_le_norm_sub_add_norm_sub (U y t) (A y t) 0
    rw [sub_zero,sub_zero] at h
    have h₁ := frozen_norm (H a) (E a) (E y) t
    linarith only [h,(inside hy).1 t,h₁,min_le_left 1 (δ/(1+3*M^2))]
  have haf (y t) : ‖A y t‖≤M := (frozen_norm ..).trans (le_add_of_nonneg_right zero_le_one)
  have hp := product_error (U (x+u) t) (U x (-t)) (U (x+v) t) (A (x+u) t) (A x (-t)) (A (x+v) t)
    (haf ..) (haf ..) (hnorm h₀ _) (hnorm hv _) ((inside hu).1 _) ((inside h₀).1 _) ((inside hv).1 _)
  obtain ⟨e,he⟩ := hb a
  have ha' : A (x+u) t*A x (-t)*A (x+v) t =
      frozenEvolution (H a) (E a) (E (x+u)+ -(E x)+E (x+v)) t := by
    dsimp only [A]
    rw [frozen_neg,frozen_add he hs,frozen_add he hs]
  have hrct := hrect x u v (inside h₀).2 (inside hu).2 (inside hv).2 (inside huv).2
  have hdif (i : Fin D) : |E (x+v+u) i-(E (x+u)+ -(E x)+E (x+v)) i|≤C*‖u‖*‖v‖ := by
    have h := (norm_le_pi_norm (E (x+v+u)-E (x+v)-E (x+u)+E x) i).trans hrct
    simp only [Pi.add_apply,Pi.neg_apply]
    convert h using 1
    rw [Real.norm_eq_abs]
    congr 1
    simp only [Pi.add_apply,Pi.sub_apply]
    ring
  have hphase := frozen_change (H a) (E a) _ _ t hdif
  let V := U (x+u) t*U x (-t)*U (x+v) t
  let B := A (x+u) t*A x (-t)*A (x+v) t
  have h₁ := norm_sub_le_norm_sub_add_norm_sub (U (x+v+u) t) (A (x+v+u) t) V
  have h₂ := norm_sub_le_norm_sub_add_norm_sub (A (x+v+u) t) B V
  have h₃ : ‖B-V‖≤3*M^2*h := by rw [norm_sub_rev]; exact hp
  change ‖U (x+v+u) t-V‖≤δ+C*m*|t|*‖u‖*‖v‖
  change ‖A (x+v+u) t-frozenEvolution (H a) (E a) _ t‖≤|t|*(C*‖u‖*‖v‖)*m at hphase
  rw [←ha'] at hphase
  linarith only [h₁,h₂,h₃,hphase,(inside huv).1 t,hsmall]

#print axioms corner_evolution
end
end GaloisForLFunctions.HTGeometry.WeakBonds.Products
