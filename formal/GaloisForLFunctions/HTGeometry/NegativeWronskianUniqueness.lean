import Mathlib

/-! Uniqueness on the original negative ray from actual bounded jets and a decaying fundamental mode. -/
open Set Filter Topology
namespace GaloisForLFunctions.HTGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

def negativeWronskian (f g h k : ℝ → ℂ) (x : ℝ) : ℂ := f x*k x-g x*h x

/-- The original homogeneous equation makes the actual Wronskian constant throughout the negative ray. -/
theorem negativeWronskian_constant {Q f g h k : ℝ → ℂ}
    (hf : ∀ x < 0, HasDerivAt f (g x) x) (hg : ∀ x < 0, HasDerivAt g (Q x*f x) x)
    (hh : ∀ x < 0, HasDerivAt h (k x) x) (hk : ∀ x < 0, HasDerivAt k (Q x*h x) x)
    {x y : ℝ} (hx : x < 0) (hy : y < 0) : negativeWronskian f g h k x=negativeWronskian f g h k y := by
  have hd (t : ℝ) (ht : t < 0) : HasDerivAt (negativeWronskian f g h k) 0 t := by
    apply (((hf t ht).mul (hk t ht)).sub ((hg t ht).mul (hh t ht))).congr_deriv
    ring
  exact isOpen_Iio.is_const_of_deriv_eq_zero (convex_Iio (0:ℝ)).isPreconnected
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt) (fun t ht => (hd t ht).deriv) hx hy

/-- Bounded actual value and first jet imply a zero horizon Wronskian against a decaying mode. -/
theorem negativeWronskian_eq_zero_of_bounded {Q f g h k : ℝ → ℂ}
    (hf : ∀ x < 0, HasDerivAt f (g x) x) (hg : ∀ x < 0, HasDerivAt g (Q x*f x) x)
    (hh : ∀ x < 0, HasDerivAt h (k x) x) (hk : ∀ x < 0, HasDerivAt k (Q x*h x) x)
    {C D : ℝ}
    (hb : ∀ x < 0, ‖f x‖ ≤ C) (hgb : ∀ x < -1, ‖g x‖ ≤ D)
    (hh0 : Tendsto h atBot (𝓝 0)) (hk0 : Tendsto k atBot (𝓝 0))
    {x : ℝ} (hx : x < 0) : negativeWronskian f g h k x=0 := by
  have ht : Tendsto (negativeWronskian f g h k) atBot (𝓝 0) := by
    apply squeeze_zero_norm' ?_ (show Tendsto (fun t => C*‖k t‖+D*‖h t‖) atBot (𝓝 0) from by
      simpa only [norm_zero,mul_zero,zero_add] using (hk0.norm.const_mul C).add (hh0.norm.const_mul D))
    filter_upwards [eventually_lt_atBot (-1:ℝ)] with t ht
    calc
      ‖negativeWronskian f g h k t‖ ≤ ‖f t*k t‖+‖g t*h t‖ := norm_sub_le _ _
      _ ≤ C*‖k t‖+D*‖h t‖ := by
        rw [norm_mul,norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_right (hb t (by linarith)) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (hgb t ht) (norm_nonneg _))
  have hc : Tendsto (negativeWronskian f g h k) atBot (𝓝 (negativeWronskian f g h k x)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_lt_atBot (0:ℝ)] with t ht
    exact (negativeWronskian_constant hf hg hh hk ht hx).symm
  exact tendsto_nhds_unique hc ht

/-- A nondegenerate physical basis and nonzero boundary connection exclude every bounded homogeneous defect. -/
theorem negative_homogeneous_eq_zero {Q f g h k n m : ℝ → ℂ} {W B : ℂ}
    (hf : ∀ x < 0, HasDerivAt f (g x) x) (hg : ∀ x < 0, HasDerivAt g (Q x*f x) x)
    (hh : ∀ x < 0, HasDerivAt h (k x) x) (hk : ∀ x < 0, HasDerivAt k (Q x*h x) x)
    (hn : ∀ x < 0, HasDerivAt n (m x) x) (hm : ∀ x < 0, HasDerivAt m (Q x*n x) x)
    (hW : W ≠ 0) (hbasis : ∀ x < 0, negativeWronskian h k n m x=W)
    (hB : B ≠ 0) (hhB : Tendsto h (𝓝[<] (0:ℝ)) (𝓝 B))
    (hf0 : Tendsto f (𝓝[<] (0:ℝ)) (𝓝 0))
    (hh0 : Tendsto h atBot (𝓝 0)) (hk0 : Tendsto k atBot (𝓝 0))
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ x < 0, ‖f x‖ ≤ C)
    (hgb : ∃ D : ℝ, 0 ≤ D ∧ ∀ x < -1, ‖g x‖ ≤ D) : ∀ x < 0, f x=0 := by
  obtain ⟨C,_,hb⟩ := hb
  obtain ⟨D,_,hgb⟩ := hgb
  have hz (x : ℝ) (hx : x < 0) := negativeWronskian_eq_zero_of_bounded hf hg hh hk hb hgb hh0 hk0 hx
  let A := negativeWronskian f g n m (-1)
  have hc (x : ℝ) (hx : x < 0) : negativeWronskian f g n m x=A :=
    negativeWronskian_constant hf hg hn hm hx (by norm_num)
  have hid (x : ℝ) (hx : x < 0) : f x*W=h x*A := by
    have h₁ := hbasis x hx
    have h₂ := hz x hx
    have h₃ := hc x hx
    dsimp only [negativeWronskian] at h₁ h₂ h₃
    linear_combination -f x*h₁-n x*h₂+h x*h₃
  have hlim : Tendsto (fun x => f x*W) (𝓝[<] (0:ℝ)) (𝓝 (B*A)) := by
    apply (hhB.mul_const A).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hid x hx).symm
  have hzero : B*A=0 := by
    have h := tendsto_nhds_unique hlim (hf0.mul_const W)
    simpa only [zero_mul] using h
  have hA : A=0 := (mul_eq_zero.mp hzero).resolve_left hB
  intro x hx
  have h := hid x hx
  rw [hA,mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_right hW

end
end GaloisForLFunctions.HTGeometry
