import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CurvatureDepth
import Mathlib.Analysis.Calculus.DerivativeTest
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.ChebyshevWindows

/-!
# Sharp universal enclosure depth

Homogenized Chebyshev forms have unit monotone capacity and exact enclosure
depth d*(d-1), for every d >= 2. An outward endpoint derivative provides a
signed unit probe at each smaller depth. Their finite enclosure curvature
is positive precisely throughout the complete degree-bound interval.

This sharpness statement concerns unrestricted finite windows; it makes no
claim that the extremizer is a linear combination of perfect endpoint pairings.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Filter
open scoped Topology

theorem chebyshev_escape (r : ℕ) (k : Fin ((r+2)*(r+1))) :
    ∃ x : ℝ, 1 < x ∧ x^(r+2+k.val) < (Polynomial.Chebyshev.T ℝ (r+2 : ℕ)).eval x := by
  let f : ℝ → ℝ := fun x => (Polynomial.Chebyshev.T ℝ (r+2 : ℕ)).eval x-x^(r+2+k.val)
  have ht := (Polynomial.Chebyshev.T ℝ (r+2 : ℕ)).hasDerivAt (1 : ℝ)
  rw [Polynomial.Chebyshev.derivative_T_eval_one] at ht
  have hx := (hasDerivAt_id (1 : ℝ)).pow (r+2+k.val)
  simp only [id_eq,one_pow,mul_one] at hx
  have hd : HasDerivAt f (((r+2 : ℕ) : ℝ)^(2 : ℕ)-((r+2+k.val : ℕ) : ℝ)) 1 := by
    exact ht.sub hx
  have hk : (k.val : ℝ) < (((r+2)*(r+1) : ℕ) : ℝ) := by exact_mod_cast k.isLt
  have hp : 0 < deriv f 1 := by
    rw [hd.deriv]
    push_cast at hk ⊢
    nlinarith only [hk]
  have hf : f 1 = 0 := by
    dsimp only [f]
    rw [Polynomial.Chebyshev.T_eval_one,one_pow,sub_self]
  have he := eventually_nhdsWithin_sign_eq_of_deriv_pos hp hf
  have hright : ∀ᶠ x in 𝓝[>] (1 : ℝ), 1 < x ∧ 0 < f x := by
    filter_upwards [nhdsWithin_le_nhds he,self_mem_nhdsWithin] with x hs (hx : 1 < x)
    refine ⟨hx,?_⟩
    apply sign_eq_one_iff.mp
    rw [hs]
    exact sign_pos (sub_pos.mpr hx)
  obtain ⟨x,hx,hf⟩ := hright.exists
  exact ⟨x,hx,sub_pos.mp hf⟩

theorem binary_chebyshev_capacity_escape (r : ℕ) (k : Fin ((r+2)*(r+1))) :
    1 < sealedCapacity (binaryWindows (r+2)) (chebyshevCoefficients (r+2)) k.val := by
  obtain ⟨x,hx,he⟩ := chebyshev_escape r k
  have hx0 : 0 < x := lt_trans (by positivity) hx
  have hxne : x ≠ 0 := ne_of_gt hx0
  let g : Fin 2 → ℝ := ![(x+1)/(2*x),(1-x)/(2*x)]
  have hg0 : 0 ≤ g 0 := by dsimp [g]; positivity
  have hg1 : g 1 ≤ 0 := by
    change (1-x)/(2*x) ≤ 0
    exact div_nonpos_of_nonpos_of_nonneg (by linarith only [hx]) (by positivity)
  have hv : variation g = 1 := by
    rw [variation,Fin.sum_univ_two,abs_of_nonneg hg0,abs_of_nonpos hg1]
    dsimp [g]
    field_simp
    ring
  have hn : normalizeProbe g = g := (normalizeProbe_fixed_iff g).mpr hv.le
  have hs : displacement g = 1/x := by
    rw [displacement,Fin.sum_univ_two]
    dsimp [g]
    field_simp
    ring
  have hr : g = (![(1/x)*((x+1)/2),(1/x)*(1-(x+1)/2)] : Fin 2 → ℝ) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (x+1)/(2*x) = (1/x)*((x+1)/2)
      field_simp
    · have hj : j = 0 := Fin.eq_zero j
      subst j
      change (1-x)/(2*x) = (1/x)*(1-(x+1)/2)
      field_simp
      ring
  have hf : familyValue (binaryWindows (r+2)) (chebyshevCoefficients (r+2)) g =
      (1/x)^(r+2)*(Polynomial.Chebyshev.T ℝ (r+2 : ℕ)).eval x := by
    rw [hr,binary_chebyshev_radial,show 2*((x+1)/2)-1=x by ring]
  have hmul : 1 < (1/x)^(r+2+k.val)*(Polynomial.Chebyshev.T ℝ (r+2 : ℕ)).eval x := by
    have hh : 1 < (Polynomial.Chebyshev.T ℝ (r+2 : ℕ)).eval x/x^(r+2+k.val) :=
      (lt_div_iff₀ (pow_pos hx0 (r+2+k.val))).mpr (by simpa only [one_mul] using he)
    rw [one_div,inv_pow]
    simpa only [div_eq_mul_inv,mul_comm] using hh
  have hp : 1 < displacement g^k.val*familyValue (binaryWindows (r+2))
      (chebyshevCoefficients (r+2)) g := by
    rw [hs,hf,← mul_assoc,← pow_add,Nat.add_comm k.val (r+2)]
    exact hmul
  have hb := sealedCapacity_probe_bound (binaryWindows (r+2)) (chebyshevCoefficients (r+2)) k.val g
  rw [hn] at hb
  exact hp.trans_le ((le_abs_self _).trans hb)

theorem binary_chebyshev_exact_depth (r : ℕ) :
    enclosureDepth (binaryWindows (r+2)) (chebyshevCoefficients (r+2)) = (r+2)*(r+1) := by
  apply Nat.le_antisymm (enclosureDepth_degree_bound _ _)
  by_contra h
  have hn : enclosureDepth (binaryWindows (r+2)) (chebyshevCoefficients (r+2)) < (r+2)*(r+1) := by omega
  have hc := binary_chebyshev_capacity_escape r ⟨_,hn⟩
  have hs := enclosureDepth_spec (binaryWindows (r+2)) (chebyshevCoefficients (r+2))
  rw [binary_chebyshev_monotoneCapacity] at hs
  change 1 < sealedCapacity (binaryWindows (r+2)) (chebyshevCoefficients (r+2))
    (enclosureDepth (binaryWindows (r+2)) (chebyshevCoefficients (r+2))) at hc
  linarith only [hc,hs]

theorem binary_chebyshev_sealing_iff (r k : ℕ) :
    sealedCapacity (binaryWindows (r+2)) (chebyshevCoefficients (r+2)) k = 1 ↔
      (r+2)*(r+1) ≤ k := by
  have h := enclosureDepth_le_iff (binaryWindows (r+2)) (chebyshevCoefficients (r+2)) k
  rw [binary_chebyshev_exact_depth,binary_chebyshev_monotoneCapacity] at h
  exact h.symm

theorem binary_chebyshev_curvature_support (r k : ℕ) :
    0 < enclosureCurvature (binaryWindows (r+2)) (chebyshevCoefficients (r+2)) k ↔
      k < (r+2)*(r+1) := by
  rw [enclosureCurvature_support,binary_chebyshev_exact_depth]

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
