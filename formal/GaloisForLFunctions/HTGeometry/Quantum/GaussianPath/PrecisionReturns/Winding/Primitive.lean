import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.Arc
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.GaussianLaw

/-! # Primitive windings at the distinguished first scalar return -/

open Filter MeasureTheory Set Real
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding
open EmptyVisitFlux SharpOccupation
noncomputable section

/-- Any common divisor of a first-return winding places its previous
multiple strictly before the observation origin. -/
theorem predecessor_before_origin {N : ℕ} (H : selfAdjoint (Register N)) {a ε : ℝ}
    (ha : 0 < a) (hε : ε ∈ Ioo (0:ℝ) (sqrt 2)) :
    let w := fun i => -H.2.isHermitian.eigenvalues i/(2*π)
    let v := firstVisit H a 0 ε
    ∀ b z, Anchored w v (physicalArc ε) b z → ∀ d : ℕ, 2 ≤ d →
      (∀ i, (d:ℤ) ∣ z i) → (((d-1 : ℕ):ℝ)/d)*v < a := by
  intro w v b z hz d hd hdiv
  have hd₀ : 0 < d := by omega
  let f := (((d-1 : ℕ):ℝ)/(d:ℝ))
  have hf : f < 1 := (div_lt_one (Nat.cast_pos.mpr hd₀)).mpr (by exact_mod_cast (show d-1<d by omega))
  have rpos := (physicalArc_spec hε.1 hε.2).1.1
  obtain ⟨y,hy⟩ := divide_turns (j:=d-1) hz hd₀ hdiv
  have hvisit := (anchored_iff rpos.le).mpr ⟨b,y,fun i =>
    ⟨(hy i).1,(hy i).2.trans (mul_le_of_le_one_left rpos.le hf.le)⟩⟩
  have h := firstVisit_isLeast H a 0 hε.1
  have hv : 0 < v := ha.trans_le h.1.1
  apply lt_of_not_ge
  intro hdate
  exact (mul_lt_of_lt_one_left hv hf).not_ge
    (h.2 ⟨hdate,(physical_visit H hε.1 hε.2 (f*v)).mp hvisit⟩)

/-- Once the first date is at least twice the origin, every integer
winding certifying its fit is primitive. -/
theorem first_winding_primitive {N : ℕ} (H : selfAdjoint (Register N)) {a ε : ℝ}
    (ha : 0 < a) (hε : ε ∈ Ioo (0:ℝ) (sqrt 2)) (hv : 2*a ≤ firstVisit H a 0 ε) :
    let w := fun i => -H.2.isHermitian.eigenvalues i/(2*π)
    let v := firstVisit H a 0 ε
    (∃ b z, Anchored w v (physicalArc ε) b z) ∧
      ∀ b z, Anchored w v (physicalArc ε) b z → ∀ d : ℕ, 2 ≤ d → ¬∀ i, (d:ℤ) ∣ z i := by
  intro w v
  have h := firstVisit_isLeast H a 0 hε.1
  refine ⟨(anchored_iff (physicalArc_spec hε.1 hε.2).1.1.le).mp
    ((physical_visit H hε.1 hε.2 v).mpr h.1.2),?_⟩
  intro b z hz d hd hdiv
  have hd₀ : 0 < d := by omega
  have hhalf : (1:ℝ)/2 ≤ (((d-1 : ℕ):ℝ)/d) := by
    apply (div_le_div_iff₀ (by norm_num) (Nat.cast_pos.mpr hd₀)).mpr
    rw [one_mul,Nat.cast_sub (by omega : 1 ≤ d),Nat.cast_one]
    linarith only [show (2:ℝ) ≤ d by exact_mod_cast hd]
  have hlow := mul_le_mul_of_nonneg_right hhalf (ha.le.trans h.1.1)
  have hh := predecessor_before_origin H ha hε b z hz d hd hdiv
  change 2*a ≤ v at hv
  change _*v < a at hh
  change 1/2*v ≤ _*v at hlow
  linarith only [hh,hlow,hv]

/-- On each typical frozen prefix of at least three spins, the first
empty winding after any positive origin is primitive at all sufficiently
small tolerances. The origin may depend on the entire draw. -/
theorem gaussian_first_winding_primitive :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let w := fun i => -H.2.isHermitian.eigenvalues i/(2*π)
      ∀ a : ℝ, 0 < a → ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ),
        let v := firstVisit H a 0 ε
        (∃ b z, Anchored w v (physicalArc ε) b z) ∧
          ∀ b z, Anchored w v (physicalArc ε) b z → ∀ d : ℕ, 2 ≤ d → ¬∀ i, (d:ℤ) ∣ z i := by
  filter_upwards [gaussian_first_return_precision_exponent] with ω hω k
  intro N H w a ha
  let D : ℝ := (2^N-2 : ℕ)
  have hD : 0 < D := by
    have hcard : 3 ≤ (2:ℕ)^N := (by decide : 3 ≤ 2^3).trans (Nat.pow_le_pow_right (by decide) (by dsimp only [N]; omega))
    dsimp only [D]
    exact_mod_cast (show 0 < 2^N-2 by omega)
  obtain ⟨hmin,hv,_⟩ := hω k a ha 0 (by omega)
  have hb := (tendsto_const_div_log_one_div (log (2*a))).eventually_lt_const (half_pos hD)
  filter_upwards [hb,hv.eventually_const_lt (half_lt_self hD),
    Ioo_mem_nhdsGT (zero_lt_one' ℝ),Ioo_mem_nhdsGT (sqrt_pos.mpr zero_lt_two)] with ε h₁ h₂ he hε
  have hl := log_pos ((one_lt_div he.1).mpr he.2)
  have hh := (div_lt_div_iff_of_pos_right hl).mp (h₁.trans h₂)
  exact first_winding_primitive H ha hε ((log_lt_log_iff (mul_pos zero_lt_two ha)
    (ha.trans_le (hmin ε he.1).1.1)).mp hh).le

#print axioms predecessor_before_origin
#print axioms gaussian_first_winding_primitive
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding
