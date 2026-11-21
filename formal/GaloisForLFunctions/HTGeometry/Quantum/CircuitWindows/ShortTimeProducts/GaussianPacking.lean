import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ShortTimeProducts.PathPacking
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ShortTimeProducts.ScalarDensity

/-! # Small-error occupation gain at one linear circuit budget -/
open Matrix Filter Topology MeasureTheory Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ShortTimeProducts
noncomputable section
open SharpOccupation

private theorem positive_width {k : ℕ} (H : selfAdjoint (Register (k+3)))
    (hi : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues) :
    0 < circuitHamiltonianSpectralWidth H := by
  let E := H.2.isHermitian.eigenvalues
  let x : Fin (k+3) → Bool := fun _ => false
  obtain ⟨y,hy⟩ := exists_ne x
  by_contra! h
  change Finset.univ.sup' Finset.univ_nonempty E - Finset.univ.inf' Finset.univ_nonempty E ≤ 0 at h
  have he (i j) : E i ≤ E j := (Finset.le_sup' E (Finset.mem_univ i)).trans
    ((sub_nonpos.mp h).trans (Finset.inf'_le E (Finset.mem_univ j)))
  exact hy (hi.injective (le_antisymm (he y x) (he x y)))

/-- On each Gaussian prefix one linear gate budget occupies at least a
constant times m^(1−2(D−1)) at error B/m². Its extra factor m compared
with scalar occupation comes from distinct near-identity lags. -/
theorem gaussian_product_step_occupation :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let D := 2^N
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let J := Fintype.card (PathLabel (k+1))
      ∃ B > 0, ∀ m : ℕ, 0<m → ∀ a : ℝ, ∀ᶠ T : ℝ in atTop,
        (m:ℝ)*D/4*(1/(4*π*(m:ℝ)^2))^(D-1) ≤ visitFraction H J (B/(m:ℝ)^2) a T := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω k
  intro N D u H J
  let W := circuitHamiltonianSpectralWidth H
  have hw := positive_width H (hω k)
  let B := 1/4+((∑ l, |u l|)*π/W)^2
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B,hB,?_⟩
  intro m hm a
  let r := 1/(4*(m:ℝ)^2)
  let g := π/(W*m)
  have hm' : (0:ℝ)<m := Nat.cast_pos.mpr hm
  have h1 : (1:ℝ)≤m := by exact_mod_cast hm
  have hr : 0<r := by dsimp [r]; positivity
  have hs : r<sqrt 2 := by
    have hpow : (1:ℝ)≤(m:ℝ)^2 := one_le_pow₀ h1
    have hsmall : r≤1/4 := by dsimp only [r]; gcongr
    have hroot := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
    nlinarith only [hroot,Real.sqrt_nonneg 2,hsmall]
  have hW : 0 < W := hw
  have hg : 0 < g := by dsimp only [g]; positivity
  let p := (D:ℝ)*(r/π)^(D-1)
  have hd : (0:ℝ)<D := by dsimp [D]; positivity
  have hp : 0 < p := by dsimp only [p]; positivity
  have hle : p ≤ (D:ℝ)*(physicalArc r)^(D-1) := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (physical_arc_bounds hr hs).1 _) hd.le
  have hb := (scalar_fraction H (hω k) hr hs a).eventually_const_lt ((half_lt_self hp).trans_le hle)
  obtain ⟨S,hS⟩ := eventually_atTop.mp hb
  filter_upwards [eventually_ge_atTop (max S a+2*g+1)] with T hT
  have hS' : S ≤ T-g := by linarith only [hT,le_max_left S a,hg]
  have hlen : 0<T-g-a := by linarith only [hT,le_max_right S a,hg]
  have hlen' : 0<T-a := by linarith only [hlen,hg]
  have hhalf : (T-a)/2 ≤ T-g-a := by linarith only [hT,le_max_right S a]
  have hvol := (lt_div_iff₀ hlen).mp (hS (T-g) hS')
  have hpack := inverse_square_packing u m hm a (T-g) hw
  change (m:ℝ)*volume.real (visitSet H 0 r ∩ Icc a (T-g)) ≤ volume.real (visitSet H J (B/(m:ℝ)^2) ∩ Icc a (T-g+g)) at hpack
  rw [sub_add_cancel] at hpack
  have he : 1/(4*π*(m:ℝ)^2)=r/π := by dsimp only [r]; ring
  rw [he]
  change (m:ℝ)*D/4*(r/π)^(D-1) ≤ _/(T-a)
  rw [le_div_iff₀ hlen']
  calc
    _ = (m:ℝ)*(p/2*((T-a)/2)) := by dsimp only [p]; ring
    _ ≤ (m:ℝ)*(p/2*(T-g-a)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hhalf (half_pos hp).le) hm'.le
    _ ≤ _ := (mul_le_mul_of_nonneg_left hvol.le hm'.le).trans hpack

#print axioms gaussian_product_step_occupation
end
end GaloisForLFunctions.HTGeometry.ShortTimeProducts
