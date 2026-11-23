import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.SpectatorCost.CommonBasisWindow
import Mathlib.Data.Fintype.Pigeonhole

/-! # Number of bases needed to cover a unit interval with short circuits -/
open Matrix Real MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
noncomputable section
private abbrev Basis (N : ℕ) := unitaryGroup (Fin N → Bool) ℂ

/-- A cover by m bases must use the same basis at two points of any
(m+1)-point grid. The spacing budget then bounds the size of the cover. -/
private theorem cover_window {m : ℕ} {A c N S : ℝ} (hA : 0 < A) (hN : 0 < N)
    (hS : 1 ≤ S) (a : ℝ) (p : Fin m → ℝ → Prop)
    (hcover : ∀ t ∈ Icc a (a+1), ∃ i, p i t)
    (hgap : ∀ i v w, p i v → p i w → A ≤ (w-v)*N → c ≤ S*N*(w-v)^2) :
    min (1/A) (c/A^2)*N ≤ S*(m:ℝ)^2 := by
  let k := min (1/A) (c/A^2)
  have hm : 1 ≤ (m:ℝ) := by
    obtain ⟨i,_⟩ := hcover a ⟨le_rfl,by linarith⟩
    exact_mod_cast (by have := i.isLt; omega : 1 ≤ m)
  by_cases hroom : A*(m:ℝ) ≤ N
  · let d := A/N
    have hd : 0 < d := div_pos hA hN
    have hdN : d*N=A := div_mul_cancel₀ _ hN.ne'
    let t (i : Fin (m+1)) := a+i.val*d
    have htime (i : Fin (m+1)) : t i ∈ Icc a (a+1) := by
      have him : (i.val:ℝ) ≤ m := Nat.cast_le.mpr (by have := i.isLt; omega)
      have hmd : (m:ℝ)*d ≤ 1 := by
        dsimp only [d]
        rw [←mul_div_assoc,div_le_iff₀ hN,one_mul,mul_comm]
        exact hroom
      exact ⟨le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hd.le),
        add_le_add le_rfl ((mul_le_mul_of_nonneg_right him hd.le).trans hmd)⟩
    choose f hf using fun i => hcover (t i) (htime i)
    obtain ⟨i,j,hij,he⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
    have charge {i j : Fin (m+1)} (hij : i<j) (he : f i=f j) : c ≤ S*N*((m:ℝ)*d)^2 := by
      have hstep : (i.val:ℝ)+1 ≤ j.val := by exact_mod_cast (show i.val+1≤j.val from hij)
      have hsub : d ≤ t j-t i := by
        dsimp only [t]
        linarith only [mul_le_mul_of_nonneg_right hstep hd.le]
      have hjm : (j.val:ℝ) ≤ m := Nat.cast_le.mpr (by have := j.isLt; omega)
      have hbound : t j-t i ≤ (m:ℝ)*d := by
        dsimp only [t]
        linarith only [mul_le_mul_of_nonneg_right hjm hd.le,mul_nonneg (Nat.cast_nonneg i.val) hd.le]
      have hh := hgap (f j) _ _ (he ▸ hf i) (hf j)
        (hdN.ge.trans (mul_le_mul_of_nonneg_right hsub hN.le))
      exact hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hd.le.trans hsub) hbound 2)
        (mul_nonneg (zero_le_one.trans hS) hN.le))
    have hcost := (lt_or_gt_of_ne hij).elim (fun h => charge h he) (fun h => charge h he.symm)
    have hkn := mul_le_mul_of_nonneg_right (min_le_right (1/A) (c/A^2)) hN.le
    apply hkn.trans
    rw [div_mul_eq_mul_div,div_le_iff₀ (sq_pos_of_pos hA)]
    have heq : S*N*((m:ℝ)*d)^2=(S*(m:ℝ)^2*A^2)/N := by
      dsimp only [d]
      field_simp [hN.ne']
    exact (le_div_iff₀ hN).mp (hcost.trans_eq heq)
  · have hscale : (1/A)*N ≤ (m:ℝ) := by
      rw [one_div_mul_eq_div,div_le_iff₀ hA,mul_comm]
      exact le_of_not_ge hroom
    exact ((mul_le_mul_of_nonneg_right (min_le_left ..) hN.le).trans hscale).trans
      (by nlinarith only [mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg m),
        mul_le_mul_of_nonneg_right hS (sq_nonneg (m:ℝ))])

/-- On any unit interval, m bases giving s-gate fits at every date
must satisfy (1+2s)m² ≥ cN. Both bases and interval may depend on the draw. -/
theorem gaussian_basis_cover_size :
    ∃ c > 0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ (a : ℝ) (m s : ℕ)
      (V : Fin m → Basis (n+2)),
      (∀ t ∈ Icc a (a+1), ∃ i : Fin m, HasProjectiveCircuitApproximation (n+2) (1/10) s
        ((V i).val*unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t*star (V i).val)) →
      c*(n+2:ℕ) ≤ (1+2*(s:ℝ))*(m:ℝ)^2 := by
  obtain ⟨A,b,hA,hb,h⟩ := SpectatorCost.gaussian_common_basis_window
  refine ⟨min (1/A) (b/A^2),lt_min (by positivity) (by positivity),?_⟩
  filter_upwards [h] with ω hw
  filter_upwards [hw] with n hn
  intro a m s V hcover
  apply cover_window hA (by positivity) (by linarith only [Nat.cast_nonneg (α:=ℝ) s]) a _ hcover
  intro i v w hv hw hlate
  have hh := hn v w hlate (V i) s s _ _ (by norm_num : (1/10:ℝ)+1/10 ≤ 11/50) hv hw
  simpa only [Nat.cast_add,two_mul] using hh

#print axioms gaussian_basis_cover_size
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
