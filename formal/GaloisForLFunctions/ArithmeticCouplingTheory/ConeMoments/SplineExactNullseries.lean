import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineCompatiblePrefixes

/-!
# Absolutely convergent nullseries with exact spline coefficients

Compatible finite prefixes give zero moments on the exhaustive positive cone.
Summable coefficient norms justify regrouping the atoms into finite blocks.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

variable {a b d D : ℝ}

abbrev PrescribedSplineSchedule.AtomIndex (s : PrescribedSplineSchedule a b d D) :=
  (k : ℕ) × Fin (s.size k)

def PrescribedSplineSchedule.atom (s : PrescribedSplineSchedule a b d D)
    (γ : (k : ℕ) → Fin (s.size k) → ℝ) (i : s.AtomIndex) : ℂ := s.point γ i.1 i.2

lemma PrescribedSplineSchedule.nested (s : PrescribedSplineSchedule a b d D) :
    ∀ k l, k ≤ l → s.frequency k ⊆ s.frequency l := by
  intro k l hkl
  exact coneSquare_mono a b (quantitativeCutoff_mono (le_trans zero_le_one s.cutoff_one)
    (Nat.add_le_add_left hkl s.start))

lemma PrescribedSplineSchedule.covers (s : PrescribedSplineSchedule a b d D)
    (t : PositiveCone a b) : ∃ k, t.val ∈ s.frequency k := by
  obtain ⟨k,hk⟩ := quantitativeCutoff_covers s.cutoff_one t
  exact ⟨k,coneSquare_mono a b (quantitativeCutoff_mono
    (le_trans zero_le_one s.cutoff_one) (by omega : k ≤ s.start+k)) hk⟩

lemma summable_prescribed_spline_norm (s : PrescribedSplineSchedule a b d D)
    (hd : 0 < d) (hdD : d < D) {γ : (k : ℕ) → Fin (s.size k) → ℝ}
    (hγ : ∀ k j, s.height k ≤ γ k j) :
    Summable (fun i : s.AtomIndex => ‖splineMomentCoefficient (s.atom γ i)‖) := by
  rw [summable_sigma_of_nonneg
    (f := fun i : s.AtomIndex => ‖splineMomentCoefficient (s.atom γ i)‖)
    (fun i => norm_nonneg (splineMomentCoefficient (s.atom γ i)))]
  refine ⟨fun _ => Summable.of_finite,?_⟩
  apply Summable.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => norm_nonneg _)
    (fun k => ?_) (summable_geometric_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1))
  rw [tsum_fintype]
  exact s.block_norm_mass_le (γ := γ) (k := k) hd hdD (hγ k)

lemma tsum_prescribed_spline_norm_le_two (s : PrescribedSplineSchedule a b d D)
    (hd : 0 < d) (hdD : d < D) {γ : (k : ℕ) → Fin (s.size k) → ℝ}
    (hγ : ∀ k j, s.height k ≤ γ k j) :
    ∑' i : s.AtomIndex, ‖splineMomentCoefficient (s.atom γ i)‖ ≤ 2 := by
  have hs := summable_prescribed_spline_norm s hd hdD hγ
  have hσ := hs.hasSum.sigma (fun k => hasSum_fintype
    (fun j : Fin (s.size k) => ‖splineMomentCoefficient (s.point γ k j)‖))
  have hg := hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1)
  have h := hσ.summable.tsum_le_tsum (fun k => s.block_norm_mass_le (γ := γ) (k := k) hd hdD (hγ k)) hg.summable
  rw [hσ.tsum_eq,hg.tsum_eq] at h
  norm_num at h
  exact h

lemma summable_prescribed_spline_moment (s : PrescribedSplineSchedule a b d D)
    (hd : 0 < d) (hdD : d < D) {γ : (k : ℕ) → Fin (s.size k) → ℝ}
    (hγ : ∀ k j, s.height k ≤ γ k j) (u : ℝ) :
    Summable (fun i : s.AtomIndex => splineMomentCoefficient (s.atom γ i)*
      Complex.exp ((u : ℂ)*s.atom γ i)) := by
  have hs := summable_prescribed_spline_norm s hd hdD hγ
  refine Summable.of_norm_bounded (hs.mul_right (Real.exp (|u| * D))) fun i => ?_
  rw [norm_mul,Complex.norm_exp]
  have he : ((u : ℂ)*s.atom γ i).re=u*s.level i.1 := by
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
      PrescribedSplineSchedule.atom,s.point_re]
  rw [he]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  exact (mul_le_mul_of_nonneg_right (le_abs_self u)
    (hd.le.trans (approachLevel_lower hdD (s.start+i.1)))).trans
    (mul_le_mul_of_nonneg_left (approachLevel_lt hdD (s.start+i.1)).le (abs_nonneg u))

lemma hasSum_prescribed_spline_block_moment (s : PrescribedSplineSchedule a b d D)
    (γ : (k : ℕ) → Fin (s.size k) → ℝ)
    (hz : ∀ k u, u ∈ s.frequency k → s.prefixMoment γ (k+1) u=0)
    {N : ℕ} {u : ℝ} (hu : u ∈ s.frequency N) :
    HasSum (fun k => s.blockMoment γ k u) 0 := by
  have hp : ∀ k, N ≤ k → s.prefixMoment γ (k+1) u=0 :=
    fun k hk => hz k u (s.nested N k hk hu)
  have hzero : ∀ k ∉ range (N+1), s.blockMoment γ k u=0 := by
    intro k hk
    rw [mem_range,not_lt] at hk
    obtain ⟨j,rfl⟩ : ∃ j, k=j+1 := ⟨k-1,by omega⟩
    have h := hp (j+1) (by omega)
    rw [PrescribedSplineSchedule.prefixMoment,sum_range_succ] at h
    change s.prefixMoment γ (j+1) u+s.blockMoment γ (j+1) u=0 at h
    rwa [hp j (by omega),zero_add] at h
  have h : HasSum (fun k => s.blockMoment γ k u)
      (∑ k ∈ range (N+1), s.blockMoment γ k u) := hasSum_sum_of_ne_finset_zero hzero
  change HasSum (fun k => s.blockMoment γ k u) (s.prefixMoment γ (N+1) u) at h
  rwa [hp N le_rfl] at h

/-- Every positive cone moment vanishes as an absolutely convergent atomic sum. -/
theorem hasSum_prescribed_spline_atomic_moment (s : PrescribedSplineSchedule a b d D)
    (hd : 0 < d) (hdD : d < D) {γ : (k : ℕ) → Fin (s.size k) → ℝ}
    (hγ : ∀ k j, s.height k ≤ γ k j)
    (hz : ∀ k u, u ∈ s.frequency k → s.prefixMoment γ (k+1) u=0)
    (t : PositiveCone a b) :
    HasSum (fun i : s.AtomIndex => splineMomentCoefficient (s.atom γ i)*
      Complex.exp ((t.val : ℂ)*s.atom γ i)) 0 := by
  obtain ⟨N,hN⟩ := s.covers t
  have hs := summable_prescribed_spline_moment s hd hdD hγ t.val
  have hσ := hs.hasSum.sigma (fun k => hasSum_fintype
    (fun j : Fin (s.size k) => splineMomentCoefficient (s.point γ k j)*
      Complex.exp ((t.val : ℂ)*s.point γ k j)))
  change HasSum (fun k => s.blockMoment γ k t.val)
    (∑' i : s.AtomIndex, splineMomentCoefficient (s.atom γ i)*
      Complex.exp ((t.val : ℂ)*s.atom γ i)) at hσ
  rw [← hσ.unique (hasSum_prescribed_spline_block_moment s γ hz hN)]
  exact hs.hasSum

#print axioms hasSum_prescribed_spline_atomic_moment
#print axioms tsum_prescribed_spline_norm_le_two
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
