import GaloisForLFunctions.HTGeometry.EvenlyCoveredLimit

/-!
# Excluding finite Laurent limits at logarithmic conic corners

The Laurent relation fixes a limiting character. The exponential covering then
fixes a logarithmic difference. Its direction is incompatible with the conic.
The proof uses exact identities and topological limits, with no growth estimate.
-/

namespace GaloisForLFunctions.HTGeometry.ToricConicCorner

open Filter Topology Complex EvenlyCoveredLimit

noncomputable section

def laurent (x y : ℂ) : ℂ := x + x⁻¹ + y + y⁻¹

theorem corner_identity {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (y / x) * (1 + x ^ 2 + x * y - laurent x y * x) = -1 := by
  dsimp [laurent]
  field_simp
  ring

theorem ratio_limit {A : Type*} {l : Filter A} {x y : A → ℂ} {d : ℂ}
    (hx : Tendsto x l (𝓝 0)) (hy : Tendsto y l (𝓝 0))
    (hx₀ : ∀ t, x t ≠ 0) (hy₀ : ∀ t, y t ≠ 0)
    (hd : Tendsto (fun t ↦ laurent (x t) (y t)) l (𝓝 d)) :
    Tendsto (fun t ↦ y t / x t) l (𝓝 (-1)) := by
  let W : A → ℂ := fun t ↦ 1 + x t ^ 2 + x t * y t - laurent (x t) (y t) * x t
  have hW : Tendsto W l (𝓝 1) := by
    simpa [W] using ((tendsto_const_nhds.add (hx.pow 2)).add (hx.mul hy)).sub (hd.mul hx)
  have hlim : Tendsto (fun t ↦ (-1 : ℂ) / W t) l (𝓝 (-1)) := by
    simpa only [neg_div, one_div, inv_one] using (hW.inv₀ one_ne_zero).neg
  apply hlim.congr'
  filter_upwards [hW.eventually_ne one_ne_zero] with t ht
  exact (eq_div_iff ht).mpr (corner_identity (hx₀ t) (hy₀ t)) |>.symm

theorem no_conic_corner {a b : ℝ → ℂ} (ha : Continuous a) (hb : Continuous b)
    {C d : ℂ} (hconic : ∀ t, a t ^ 2 + b t ^ 2 = C)
    (hx : Tendsto (fun t ↦ exp (a t)) atTop (𝓝 0))
    (hy : Tendsto (fun t ↦ exp (b t)) atTop (𝓝 0))
    (hd : Tendsto (fun t ↦ laurent (exp (a t)) (exp (b t))) atTop (𝓝 d)) : False := by
  have hratio := ratio_limit hx hy (fun t ↦ exp_ne_zero (a t)) (fun t ↦ exp_ne_zero (b t)) hd
  have hdiff : Tendsto (fun t ↦ exp (b t - a t)) atTop (𝓝 (-1)) := by
    simpa only [exp_sub] using hratio
  obtain ⟨k, _, hk⟩ := exp_lift_limit (hb.sub ha) (neg_ne_zero.mpr one_ne_zero) hdiff
  have hi := inv_limit_of_exp_zero hx
  have he : ∀ᶠ t in atTop, a t ≠ 0 := by
    filter_upwards [hx.eventually_ne zero_ne_one] with t ht
    intro hz
    exact ht (by simp [hz])
  have hquot : Tendsto (fun t ↦ b t / a t) atTop (𝓝 1) := by
    have hh : Tendsto (fun t ↦ (b t - a t) * (a t)⁻¹ + 1) atTop (𝓝 1) := by
      simpa using (hk.mul hi).add_const 1
    apply hh.congr'
    filter_upwards [he] with t ht
    field_simp
    ring
  have hleft : Tendsto (fun t ↦ 1 + (b t / a t) ^ 2) atTop (𝓝 (2 : ℂ)) := by
    convert (hquot.pow 2).const_add 1 using 1
    norm_num
  have hright : Tendsto (fun t ↦ C * (a t)⁻¹ ^ 2) atTop (𝓝 (0 : ℂ)) := by
    simpa using (hi.pow 2).const_mul C
  have hsame : (fun t ↦ 1 + (b t / a t) ^ 2) =ᶠ[atTop] (fun t ↦ C * (a t)⁻¹ ^ 2) := by
    filter_upwards [he] with t ht
    rw [← hconic t]
    field_simp
  have hbad : (2 : ℂ) = 0 := tendsto_nhds_unique hleft (hright.congr' hsame.symm)
  exact two_ne_zero hbad

end

end GaloisForLFunctions.HTGeometry.ToricConicCorner
