import GaloisForLFunctions.RHTower.XiLogDerivEventualPositivity
import GaloisForLFunctions.RHTower.XiLogDerivReCriticalLine

/-!
# Zero multiplicity from parabolic Hadamard readings

The quadratic ray map in Guyomard–Pahl–Rasel–Gaaloul
(arXiv:2611.13032, §II) suggests examining horizontal displacements
on the scale of the squared ordinate displacement. At every complex
point the resulting finite real reading is affine in the curvature
parameter. Its slope is the multiplicity of ξ. On the critical line
the intercept vanishes by reflection.
-/

noncomputable section
open Complex Filter Topology Metric
open RHTower RHTower.BacklundConverse
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- A vertical approach with horizontal offset a u². -/
def parabolicPlace (ρ : ℂ) (a u : ℝ) : ℂ := ρ+⟨a*u^2,u⟩

/-- The order of ξ at the marked place, including order zero. -/
abbrev hadamardOrder (ρ : ℂ) := (analyticOrderAt xi ρ).toNat

private theorem place_limit {ι : Type*} {l : Filter ι} {u a : ι → ℝ} {A : ℝ}
    (hu : Tendsto u l (𝓝 0)) (ha : Tendsto a l (𝓝 A)) (ρ : ℂ) :
    Tendsto (fun i => parabolicPlace ρ (a i) (u i)) l (𝓝 ρ) := by
  have hc : Continuous (fun p : ℝ×ℝ => parabolicPlace ρ p.1 p.2) := by
    have he (p : ℝ×ℝ) : parabolicPlace ρ p.1 p.2 =
        ρ+(((p.1*p.2^2:ℝ):ℂ)+(p.2:ℂ)*I) :=
      congrArg (ρ+·) (Complex.re_add_im (⟨p.1*p.2^2,p.2⟩:ℂ)).symm
    simp_rw [he]
    fun_prop
  simpa only [Function.comp_def,parabolicPlace,zero_pow (by decide : 2≠0),mul_zero,
    show (⟨0,0⟩:ℂ)=0 from rfl,add_zero] using (hc.tendsto (A,0)).comp (ha.prodMk_nhds hu)

private theorem pole_reading (m : ℕ) (a u : ℝ) (hu : u≠0) :
    ((m:ℂ)/(⟨a*u^2,u⟩:ℂ)).re = (m:ℝ)*a/(1+(a*u)^2) := by
  simp only [Complex.div_re,Complex.natCast_re,Complex.natCast_im,zero_mul,zero_div,
    add_zero,Complex.normSq_apply]
  have hd : 0<1+(a*u)^2 := by positivity
  have he : a*u^2*(a*u^2)+u*u = u^2*(1+(a*u)^2) := by ring
  rw [he]
  field_simp [hu,hd.ne']

/-- For arbitrarily varying offsets a→A and heights u→0, u≠0, the
limiting Hadamard reading is B+mA. The same B works for all filters,
heights and curvatures at the given point. -/
theorem parabolic_hadamard_affine_law (ρ : ℂ) :
    ∃ B : ℝ, ∀ {ι : Type*} {l : Filter ι} {u a : ι → ℝ} {A : ℝ},
      Tendsto u l (𝓝 0) → (∀ᶠ i in l, u i≠0) → Tendsto a l (𝓝 A) →
      Tendsto (fun i => (logDeriv xi (parabolicPlace ρ (a i) (u i))).re)
        l (𝓝 (B+(hadamardOrder ρ:ℝ)*A)) := by
  obtain ⟨r,hr,g,hga,hgz,hf⟩ := xi_peel_ball ρ
  have hg := hga ρ (mem_ball_self hr)
  have hc : ContinuousAt (logDeriv g) ρ := hg.deriv.continuousAt.div hg.continuousAt
    (hgz ρ (mem_ball_self hr))
  refine ⟨(logDeriv g ρ).re,?_⟩
  intro ι l u a A hu hn ha
  have hp := place_limit hu ha ρ
  have hreg := Complex.continuous_re.continuousAt.tendsto.comp (hc.tendsto.comp hp)
  have hden := (tendsto_const_nhds (x:=(1:ℝ))).add ((ha.mul hu).pow 2)
  simp only [mul_zero,zero_pow (by decide : 2≠0),add_zero] at hden
  have hpol := (ha.const_mul (hadamardOrder ρ:ℝ)).div hden one_ne_zero
  rw [div_one] at hpol
  apply (hreg.add hpol).congr'
  filter_upwards [hn,hp.eventually (ball_mem_nhds _ hr)] with i hi hball
  have hz : parabolicPlace ρ (a i) (u i) ≠ ρ := by
    intro he
    have he' := congrArg Complex.im he
    change ρ.im+u i=ρ.im at he'
    exact hi (by linarith only [he'])
  rw [logDeriv_xi_eq_pole_add hga hgz hf hball hz,Complex.add_re]
  rw [show parabolicPlace ρ (a i) (u i) - ρ = (⟨a i*u i^2,u i⟩:ℂ) by
    unfold parabolicPlace; abel,pole_reading _ _ _ hi]
  exact add_comm _ _

/-- The real reading differs from its principal part by a bounded amount
throughout a small disk, including the marked point under totalized division. -/
theorem local_hadamard_principal_part_bound (ρ : ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∃ K : ℝ, 0≤K ∧ ∀ z ∈ ball ρ r,
      |(logDeriv xi z).re-((hadamardOrder ρ:ℂ)/(z-ρ)).re| ≤ K := by
  obtain ⟨R,hR,g,ha,hg,hfact⟩ := xi_peel_ball ρ
  have hρ := ha ρ (mem_ball_self hR)
  have hc : ContinuousAt (fun z => (logDeriv g z).re) ρ :=
    Complex.continuous_re.continuousAt.comp (hρ.deriv.continuousAt.div hρ.continuousAt
      (hg ρ (mem_ball_self hR)))
  obtain ⟨r,hr,hd⟩ := Metric.continuousAt_iff.mp hc 1 one_pos
  let K := max |(logDeriv xi ρ).re| (|(logDeriv g ρ).re|+1)
  refine ⟨min R r,lt_min hR hr,K,(abs_nonneg _).trans (le_max_left ..),?_⟩
  intro z hz
  by_cases he : z=ρ
  · subst z
    simpa only [sub_self,div_zero,Complex.zero_re,sub_zero] using
      (le_max_left |(logDeriv xi ρ).re| (|(logDeriv g ρ).re|+1))
  have hball := (ball_subset_ball (min_le_left R r)) hz
  rw [logDeriv_xi_eq_pole_add ha hg hfact hball he,Complex.add_re,add_sub_cancel_left]
  have hh := hd ((mem_ball.mp hz).trans_le (min_le_right R r))
  rw [Real.dist_eq] at hh
  have htri := abs_add_le ((logDeriv g z).re-(logDeriv g ρ).re) (logDeriv g ρ).re
  rw [sub_add_cancel] at htri
  exact (show |(logDeriv g z).re|≤|(logDeriv g ρ).re|+1 by linarith only [hh,htri]).trans
    (le_max_right ..)

/-- Two simultaneous real readings recover the integer multiplicity at
any marked point, using the same vertical displacements on both paths. -/
theorem paired_hadamard_readings_count_multiplicity (ρ : ℂ)
    {ι : Type*} {l : Filter ι} {u : ι → ℝ} (hu : Tendsto u l (𝓝 0))
    (hn : ∀ᶠ i in l, u i≠0) :
    Tendsto (fun i => (logDeriv xi (parabolicPlace ρ 1 (u i))).re -
      (logDeriv xi (parabolicPlace ρ 0 (u i))).re) l (𝓝 (hadamardOrder ρ:ℝ)) := by
  obtain ⟨B,h⟩ := parabolic_hadamard_affine_law ρ
  simpa only [mul_one,mul_zero,add_zero,add_sub_cancel_left] using
    (h hu hn (tendsto_const_nhds (x:=(1:ℝ)))).sub (h hu hn (tendsto_const_nhds (x:=(0:ℝ))))

/-- On the critical line a single reading recovers the zero order.
Every sequence of nonzero vertical offsets tending to zero works. -/
theorem critical_line_parabolic_reading (ρ : ℂ) (hr : ρ.re=1/2)
    {ι : Type*} {l : Filter ι} {u : ι → ℝ} (hu : Tendsto u l (𝓝 0))
    (hn : ∀ᶠ i in l, u i≠0) :
    Tendsto (fun i => (logDeriv xi (parabolicPlace ρ 1 (u i))).re) l (𝓝 (hadamardOrder ρ:ℝ)) := by
  apply (paired_hadamard_readings_count_multiplicity ρ hu hn).congr
  intro i
  rw [re_logDeriv_xi_eq_zero_of_re_eq_half (s:=parabolicPlace ρ 0 (u i))
    (by change ρ.re+0*u i^2=1/2; simpa only [zero_mul,add_zero] using hr),sub_zero]

/-- Order zero is equivalent to regularity of the logarithmic derivative at a nonzero value of ξ. -/
theorem hadamardOrder_zero_iff (ρ : ℂ) : hadamardOrder ρ=0 ↔ xi ρ≠0 := by
  obtain ⟨r,hr,g,_,hn,h⟩ := xi_peel_ball ρ
  have he := h ρ (mem_ball_self hr)
  change xi ρ = (ρ-ρ)^hadamardOrder ρ*g ρ at he
  rw [sub_self] at he
  constructor
  · intro hz
    rw [he,hz,pow_zero,one_mul]
    exact hn ρ (mem_ball_self hr)
  · intro hne
    by_contra hpos
    exact hne (by rw [he,zero_pow hpos,zero_mul])

/-- The right half-plane is zero-free exactly when every marked point
has cofinally many paired readings whose difference is below one half.
At an actual zero this difference tends to a positive integer. -/
theorem rh_iff_subhalf_parabolic_difference :
    RiemannHypothesis ↔ ∀ ρ : ℂ, 1/2<ρ.re → ∃ᶠ u : ℝ in 𝓝[≠] 0,
      (logDeriv xi (parabolicPlace ρ 1 u)).re-(logDeriv xi (parabolicPlace ρ 0 u)).re<1/2 := by
  rw [rh_iff_xi_ne_zero_right]
  have lim (ρ : ℂ) := paired_hadamard_readings_count_multiplicity ρ
    (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto id (𝓝[≠] (0:ℝ)) (𝓝 0))
    (self_mem_nhdsWithin : ∀ᶠ u : ℝ in 𝓝[≠] 0, u≠0)
  constructor
  · intro h ρ hr
    have hh := lim ρ
    rw [(hadamardOrder_zero_iff ρ).mpr (h ρ hr),Nat.cast_zero] at hh
    exact (hh.eventually_lt_const (by norm_num : (0:ℝ)<1/2)).frequently
  · intro h ρ hr
    apply (hadamardOrder_zero_iff ρ).mp
    by_contra hn
    have hm : (1:ℝ)≤hadamardOrder ρ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hh := (lim ρ).eventually_const_lt (by linarith only [hm] : (1/2:ℝ)<hadamardOrder ρ)
    obtain ⟨_,h₁,h₂⟩ := ((h ρ hr).and_eventually hh).exists
    exact h₁.not_ge h₂.le

#print axioms local_hadamard_principal_part_bound
#print axioms parabolic_hadamard_affine_law
#print axioms paired_hadamard_readings_count_multiplicity
#print axioms critical_line_parabolic_reading
#print axioms rh_iff_subhalf_parabolic_difference
end GaloisForLFunctions.ExceptionalLayerTheory
