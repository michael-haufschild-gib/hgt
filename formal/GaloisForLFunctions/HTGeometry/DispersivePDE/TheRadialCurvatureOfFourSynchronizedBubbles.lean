import GaloisForLFunctions.HTGeometry.DispersivePDE.TheEnergyGapOfFourUnequalCriticalBubbles

/-!
# Radial and transverse curvature of a synchronized quartet

The centered second variation has a radial part with curvature 8m.
Its remaining quadratic form is the complete-graph energy of the four
relative displacements. Symmetric finite differences retain just one
additional term, the homogeneous quartic energy of the displacement.
-/

noncomputable section
open Filter Topology
namespace HTGeometry.CriticalQuartet

private def spread (u : Fin 4 → ℝ) : ℝ :=
  (u 0-u 1)^2+(u 0-u 2)^2+(u 0-u 3)^2+(u 1-u 2)^2+(u 1-u 3)^2+(u 2-u 3)^2

/-- Directional curvature in relative displacements: the physical
displacement of the i-th amplitude is xᵢuᵢ. -/
def curvature (m b : ℝ) (x u : Fin 4 → ℝ) : ℝ :=
  8*m*total (fun i => (x i*u i)^2)+4*b*product x*spread u

private theorem spread_zero (u : Fin 4 → ℝ) : spread u=0 ↔ ∀ i, u i=u 0 := by
  constructor
  · intro h
    unfold spread at h
    have z (a : ℝ) (ha : a^2≤0) : a=0 := sq_eq_zero_iff.mp (le_antisymm ha (sq_nonneg a))
    have zero (i : Fin 4) (h₀ : (u 0-u i)^2≤0) : u i=u 0 := (sub_eq_zero.mp (z _ h₀)).symm
    intro i
    have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by fin_cases i <;> simp
    rcases cases with rfl|rfl|rfl|rfl
    · rfl
    all_goals
      apply zero
      linarith only [h,sq_nonneg (u 0-u 1),sq_nonneg (u 0-u 2),sq_nonneg (u 0-u 3),
        sq_nonneg (u 1-u 2),sq_nonneg (u 1-u 3),sq_nonneg (u 2-u 3)]
  · intro h
    simp [spread,h 1,h 2,h 3]

private theorem quartic_profile {μ x : Fin 4 → ℝ} {m b : ℝ} (h : Synchronized μ m b x) (u : Fin 4 → ℝ) :
    energy μ 0 b (fun i => x i*u i)=m*total (fun i => x i^2*u i^4)+b*product x*mixingGap u := by
  have site (i : Fin 4) : μ i*(x i*u i)^4=m*x i^2*u i^4+b*product x*u i^4 := by
    rw [mul_pow,←mul_assoc,h.2 i,add_mul]
  have fac : product (fun i => x i*u i)=product x*product u := by unfold product; ring
  rw [energy,fac,mixingGap_identity]
  unfold total
  linarith only [site 0,site 1,site 2,site 3]

private theorem mix_step (t : ℝ) (u : Fin 4 → ℝ) :
    mixingGap (fun i => 1+t*u i)+mixingGap (fun i => 1-t*u i)=4*t^2*spread u+2*t^4*mixingGap u := by
  unfold mixingGap spread
  ring

/-- Exact symmetric Taylor formula at every displacement size. The
quartic correction has precisely the zero-mass Kerr energy. -/
theorem centered_energy_at_scale {μ x : Fin 4 → ℝ} {m b : ℝ} (h : Synchronized μ m b x)
    (u : Fin 4 → ℝ) (t : ℝ) :
    energy μ m b (fun i => x i*(1+t*u i))+energy μ m b (fun i => x i*(1-t*u i))-2*energy μ m b x =
      t^2*curvature m b x u+2*t^4*energy μ 0 b (fun i => x i*u i) := by
  have plus := energy_gap h (fun i => 1+t*u i)
  have minus := energy_gap h (fun i => 1-t*u i)
  have base := energy_at_solution h
  have mix : b*product x*(mixingGap (fun i => 1+t*u i)+mixingGap (fun i => 1-t*u i)) =
      b*product x*(4*t^2*spread u+2*t^4*mixingGap u) := congrArg _ (mix_step t u)
  rw [quartic_profile h,curvature]
  unfold total at plus minus base ⊢
  linarith only [plus,minus,base,mix]

/-- The symmetric second difference converges to the stated curvature
in every physical direction relative to the positive state. -/
theorem second_difference_limit {μ x : Fin 4 → ℝ} {m b : ℝ} (h : Synchronized μ m b x) (u : Fin 4 → ℝ) :
    Tendsto (fun t : ℝ => (energy μ m b (fun i => x i*(1+t*u i))+
      energy μ m b (fun i => x i*(1-t*u i))-2*energy μ m b x)/t^2)
      (𝓝[≠] 0) (𝓝 (curvature m b x u)) := by
  let H := curvature m b x u
  let Q := energy μ 0 b (fun i => x i*u i)
  have cont : Continuous (fun t : ℝ => H+2*t^2*Q) := by fun_prop
  have lim : Tendsto (fun t : ℝ => H+2*t^2*Q) (𝓝[≠] 0) (𝓝 H) := by
    simpa only [zero_pow (by decide : 2≠0),mul_zero,zero_mul,add_zero] using
      ((cont.tendsto 0).mono_left nhdsWithin_le_nhds)
  apply lim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hn : t≠0 := ht
  rw [centered_energy_at_scale h]
  change H+2*t^2*Q=(t^2*H+2*t^4*Q)/t^2
  field_simp [hn] <;> ring

/-- The curvature floor is exactly 8m and its equality directions are
exactly the radial displacements. -/
theorem sharp_radial_curvature {μ x : Fin 4 → ℝ} {m b : ℝ} (hb : 0<b) (h : Synchronized μ m b x) :
    (∀ c : ℝ, (∀ u : Fin 4 → ℝ, c*total (fun i => (x i*u i)^2)≤curvature m b x u) ↔ c≤8*m) ∧
    ∀ u : Fin 4 → ℝ, curvature m b x u=8*m*total (fun i => (x i*u i)^2) ↔ ∀ i,u i=u 0 := by
  have price : 0<4*b*product x := mul_pos (mul_pos (by norm_num) hb) (product_pos h.1)
  constructor
  · intro c
    constructor
    · intro all
      have test := all (fun _ => 1)
      simp only [curvature,mul_one,spread,sub_self,zero_pow (by decide : 2≠0),add_zero,mul_zero] at test
      exact le_of_mul_le_mul_right test ((sq_pos_of_pos (h.1 0)).trans_le (le_total (fun i => sq_nonneg (x i)) 0))
    · intro hc u
      have nonneg : 0≤total (fun i => (x i*u i)^2) := by unfold total; positivity
      have extra : 0≤4*b*product x*spread u := mul_nonneg price.le (by unfold spread; positivity)
      unfold curvature
      linarith only [extra,mul_le_mul_of_nonneg_right hc nonneg]
  · intro u
    unfold curvature
    constructor
    · intro eq
      exact (spread_zero u).mp ((mul_eq_zero.mp (show 4*b*product x*spread u=0 by
        linarith only [eq])).resolve_left price.ne')
    · intro hu
      rw [(spread_zero u).mpr hu,mul_zero,add_zero]

#print axioms centered_energy_at_scale
#print axioms second_difference_limit
#print axioms sharp_radial_curvature
end HTGeometry.CriticalQuartet
