import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.Arc
import GaloisForLFunctions.HTGeometry.SimultaneousDirichlet

/-! # Earlier visits from repeated winding residues -/

open Set Finset
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding
noncomputable section
variable {I : Type*} [Fintype I] [Nonempty I]

/-- Integer lifts lying in a common real interval can be based at its lowest coordinate. -/
private theorem shift_anchor {w : I → ℝ} {t r : ℝ} (b : I) (p : I → ℤ) {l : ℝ}
    (h : ∀ i, t*(w i-w b)-(p i:ℝ) ∈ Set.Icc l (l+r)) :
    ∃ a y, Anchored w t r a y := by
  classical
  let u := fun i => t*(w i-w b)-(p i:ℝ)
  obtain ⟨a,_,ha⟩ := exists_min_image univ u univ_nonempty
  refine ⟨a,fun i => p i-p a,fun i => ?_⟩
  rw [Int.cast_sub,show t*(w i-w a)-((p i:ℝ)-(p a:ℝ))=u i-u a by dsimp only [u]; ring]
  exact ⟨sub_nonneg.mpr (ha i (mem_univ _)),by linarith only [(h i).2,(h a).1]⟩

/-- Distinct nonzero winding residues modulo a proposed time denominator. -/
def residues (z : I → ℤ) (d : ℕ) : Finset ℤ :=
  (Finset.univ.image fun i => z i % (d:ℤ)).erase 0

omit [Nonempty I] in
private theorem approximate_residues (z : I → ℤ) {d Q : ℕ} (hd : 0 < d) (hQ : 0 < Q) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ Q^(residues z d).card ∧
      ∃ p : I → ℤ, ∀ i, |(j:ℝ)/d*(z i:ℝ)-(p i:ℝ)| ≤ 1/Q := by
  classical
  let S := residues z d
  let e := S.equivFin
  let β := fun k => ((e.symm k).val:ℝ)/(d:ℝ)
  obtain ⟨j,hj,hJ,hfit⟩ := exists_simultaneous_dirichlet β hQ
  refine ⟨j,hj,hJ,?_⟩
  have hd' : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have close (i : I) : ∃ p : ℤ, |(j:ℝ)/d*(z i:ℝ)-(p:ℝ)| ≤ 1/Q := by
    let a := z i % (d:ℤ)
    have happrox : ∃ k : ℤ, |(j:ℝ)*((a:ℝ)/d)-(k:ℝ)| ≤ 1/Q := by
      by_cases hzero : a=0
      · refine ⟨0,?_⟩
        simp only [hzero,Int.cast_zero,zero_div,mul_zero,sub_zero,abs_zero]
        positivity
      have ha : a ∈ S := mem_erase.mpr ⟨hzero,mem_image.mpr ⟨i,mem_univ _,rfl⟩⟩
      obtain ⟨k,hk⟩ := hfit (e ⟨a,ha⟩)
      exact ⟨k,by simpa only [β,Equiv.symm_apply_apply] using hk.le⟩
    obtain ⟨k,hk⟩ := happrox
    let q := z i/(d:ℤ)
    have hz : (z i:ℝ) = (a:ℝ)+(d:ℝ)*(q:ℝ) := by
      exact_mod_cast (Int.emod_add_mul_ediv (z i) (d:ℤ)).symm
    refine ⟨k+(j:ℤ)*q,?_⟩
    push_cast
    rw [hz,show (j:ℝ)/d*((a:ℝ)+d*(q:ℝ))-((k:ℝ)+j*(q:ℝ)) =
      (j:ℝ)*((a:ℝ)/d)-(k:ℝ) by field_simp; ring]
    exact hk
  choose p hp using close
  exact ⟨p,hp⟩

/-- At most m distinct nonzero residues give an earlier visit at one of
the first Q^m multiples of t/d. The error is the original width scaled
by j/d plus the two-sided Dirichlet rounding error. -/
theorem compressed_visit {w : I → ℝ} {t r : ℝ} {b : I} {z : I → ℤ}
    (h : Anchored w t r b z) {d Q : ℕ} (hd : 0 < d) (hQ : 0 < Q) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ Q^(residues z d).card ∧
      ∃ a p, Anchored w ((j:ℝ)/d*t) (2/Q+(j:ℝ)/d*r) a p := by
  obtain ⟨j,hj,hJ,p,hp⟩ := approximate_residues z hd hQ
  refine ⟨j,hj,hJ,shift_anchor b p (l:=-(1/(Q:ℝ))) fun i => ?_⟩
  let c := (j:ℝ)/d
  have hc : 0 ≤ c := div_nonneg (Nat.cast_nonneg j) (Nat.cast_nonneg d)
  have h₀ := mul_nonneg hc (h i).1
  have h₁ := mul_le_mul_of_nonneg_left (h i).2 hc
  have he := abs_le.mp (hp i)
  change -(1/(Q:ℝ)) ≤ c*(z i:ℝ)-(p i:ℝ) ∧ c*(z i:ℝ)-(p i:ℝ) ≤ 1/Q at he
  change c*t*(w i-w b)-(p i:ℝ) ∈ Set.Icc _ _
  rw [show c*t*(w i-w b)-(p i:ℝ) =
    c*(t*(w i-w b)-(z i:ℝ))+(c*(z i:ℝ)-(p i:ℝ)) by ring]
  change -(1/(Q:ℝ)) ≤ _ ∧ _ ≤ -(1/(Q:ℝ))+(2/(Q:ℝ)+c*r)
  rw [show (2:ℝ)/Q=1/Q+1/Q by ring]
  exact ⟨by linarith only [h₀,he.1],by linarith only [h₁,he.2]⟩

#print axioms compressed_visit
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding
