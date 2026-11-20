import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.SpectraOfCascadedRectangularWindows

/-!
# The zero set of a dyadic product of rectangular windows

The rectangular time window in Yang–Zhang–Ying (arXiv:2611.14200, S29)
has a sinc response. Cascading one window at each dyadic width gives an
entire response with precisely the nonzero integer multiples of π as
zeros. Absolute local convergence prevents any extra blind frequencies.
Removing the first factor halves the frequency. Hence the zero at an
odd multiple of 2ʲπ has multiplicity exactly j+1.
-/

noncomputable section
open Complex Filter Metric Set Topology
open RHTower
namespace GaloisForLFunctions.BlackHoleRingdown

/-- Half-width of the nth rectangular time window. -/
def pulseWindowWidth (n : ℕ) : ℝ := (1/2:ℝ)^n

theorem pulseWindowWidth_pos (n : ℕ) : 0<pulseWindowWidth n := by
  unfold pulseWindowWidth; positivity

theorem pulseWindowWidth_le_one (n : ℕ) : pulseWindowWidth n≤1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

private theorem width_bounds (n : ℕ) : 0≤pulseWindowWidth n ∧ pulseWindowWidth n≤1 :=
  ⟨(pulseWindowWidth_pos n).le,pulseWindowWidth_le_one n⟩

/-- Entire amplitude obtained by multiplying the rectangular-window factors. -/
abbrev dyadicPulseFactor (n : ℕ) := rectangularWindow (pulseWindowWidth n)
abbrev dyadicPulseSpectrum := windowSpectrum pulseWindowWidth

theorem dyadicPulseSpectrum_hasProd (z : ℂ) :
    HasProd (fun n => dyadicPulseFactor n z) (dyadicPulseSpectrum z) :=
  windowSpectrum_hasProd width_bounds summable_geometric_two z

theorem differentiable_dyadicPulseSpectrum : Differentiable ℂ dyadicPulseSpectrum :=
  differentiable_windowSpectrum width_bounds summable_geometric_two

theorem dyadicPulseSpectrum_even : Function.Even dyadicPulseSpectrum :=
  windowSpectrum_even pulseWindowWidth

@[simp] theorem dyadicPulseSpectrum_zero : dyadicPulseSpectrum 0=1 := by
  simp [dyadicPulseSpectrum,windowSpectrum,rectangularWindow,entireSinc_zero]

/-- The first sinc factor already accounts for the full zero set. Each
subsequent factor can increase multiplicities only on this same lattice. -/
theorem dyadicPulseSpectrum_zero_iff (z : ℂ) :
    dyadicPulseSpectrum z=0 ↔ ∃ k : ℤ, k≠0 ∧ z=(k:ℂ)*(Real.pi:ℂ) := by
  rw [windowSpectrum_zero_iff_factor width_bounds summable_geometric_two]
  constructor
  · rintro ⟨n,hn⟩
    have hw : (pulseWindowWidth n:ℂ)*z≠0 := by
      intro he
      exact one_ne_zero (by simpa only [dyadicPulseFactor,rectangularWindow,he,entireSinc_zero] using hn : (1:ℂ)=0)
    rw [rectangularWindow,entireSinc_of_ne_zero hw] at hn
    obtain ⟨k,hk⟩ := Complex.sin_eq_zero_iff.mp ((div_eq_zero_iff.mp hn).resolve_right hw)
    have hk0 : k≠0 := by rintro rfl; simp only [Int.cast_zero,zero_mul] at hk; exact hw hk
    refine ⟨2^n*k,mul_ne_zero (pow_ne_zero n (by norm_num)) hk0,?_⟩
    have hcancel : (2:ℂ)^n*(pulseWindowWidth n:ℂ)=1 := by
      simp only [pulseWindowWidth,Complex.ofReal_pow, Complex.ofReal_div,Complex.ofReal_one,
        Complex.ofReal_ofNat,←mul_pow]; norm_num
    calc z = (2:ℂ)^n*((pulseWindowWidth n:ℂ)*z) := by rw [←mul_assoc,hcancel,one_mul]
         _ = _ := by rw [hk]; push_cast; ring
  · rintro ⟨k,hk,rfl⟩
    refine ⟨0,?_⟩
    have hz : (k:ℂ)*(Real.pi:ℂ)≠0 := mul_ne_zero (by exact_mod_cast hk)
      (by exact_mod_cast Real.pi_ne_zero)
    simp only [dyadicPulseFactor,rectangularWindow,pulseWindowWidth,pow_zero,Complex.ofReal_one,one_mul,
      entireSinc_of_ne_zero hz,(Complex.sin_eq_zero_iff.mpr ⟨k,rfl⟩),zero_div]

/-- Every nonreal scattering frequency is visible to this one spectrum. -/
theorem dyadicPulseSpectrum_ne_zero_off_axis {z : ℂ} (hz : z.im≠0) : dyadicPulseSpectrum z≠0 := by
  intro h
  obtain ⟨k,_,rfl⟩ := (dyadicPulseSpectrum_zero_iff z).mp h
  exact hz (by simp [Complex.mul_im])

/-- Removing the first box leaves the same spectrum at half frequency. -/
theorem dyadicPulseSpectrum_halving (z : ℂ) :
    dyadicPulseSpectrum z = entireSinc z * dyadicPulseSpectrum ((1/2:ℂ)*z) := by
  have hh := (dyadicPulseSpectrum_hasProd ((1/2:ℂ)*z)).tendsto_prod_nat
  have h := (dyadicPulseSpectrum_hasProd z).tendsto_prod_nat.comp (tendsto_add_atTop_nat 1)
  apply tendsto_nhds_unique h ((hh.const_mul (entireSinc z)).congr ?_)
  intro n
  change _ = ∏ k ∈ Finset.range (n+1), dyadicPulseFactor k z
  rw [Finset.prod_range_succ',mul_comm (entireSinc z)]
  simp only [dyadicPulseFactor,rectangularWindow,pulseWindowWidth,pow_succ,
    Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,
    pow_zero,one_mul,mul_assoc]

private theorem sinc_simple {k : ℤ} (hk : k≠0) :
    analyticOrderAt entireSinc ((k:ℂ)*(Real.pi:ℂ))=1 := by
  let p := (k:ℂ)*(Real.pi:ℂ)
  have hp : p≠0 := mul_ne_zero (by exact_mod_cast hk) (by exact_mod_cast Real.pi_ne_zero)
  have hs : Complex.sin p=0 := Complex.sin_eq_zero_iff.mpr ⟨k,rfl⟩
  have hc : deriv Complex.sin p≠0 := by
    rw [Complex.deriv_sin]
    intro hz
    have ht := Complex.sin_sq_add_cos_sq p
    simp [hz,hs] at ht
  have ho := (Complex.differentiable_sin.analyticAt p).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hs hc
  have hm : entireSinc*(id:ℂ → ℂ)=Complex.sin := by
    funext z
    by_cases hz : z=0
    · simp [hz]
    · change entireSinc z*z=Complex.sin z
      rw [entireSinc_of_ne_zero hz,div_mul_cancel₀ _ hz]
  have hi : analyticOrderAt (id:ℂ → ℂ) p=0 := analyticAt_id.analyticOrderAt_eq_zero.mpr hp
  have he := analyticOrderAt_mul (differentiable_entireSinc.analyticAt p)
    (show AnalyticAt ℂ (id:ℂ → ℂ) p from analyticAt_id)
  rw [hm,hi,add_zero,ho] at he
  exact he.symm

private theorem order_step {k : ℤ} (hk : k≠0) :
    analyticOrderAt dyadicPulseSpectrum ((k:ℂ)*(Real.pi:ℂ)) =
      1+analyticOrderAt dyadicPulseSpectrum ((1/2:ℂ)*((k:ℂ)*(Real.pi:ℂ))) := by
  let p := (k:ℂ)*(Real.pi:ℂ)
  let half := fun z : ℂ => (1/2:ℂ)*z
  have ha : AnalyticAt ℂ half p := analyticAt_const.mul analyticAt_id
  have hd : deriv half p≠0 := by simp [half]
  have hh := analyticOrderAt_comp_of_deriv_ne_zero (f:=dyadicPulseSpectrum) ha hd
  have hf : dyadicPulseSpectrum=entireSinc*(dyadicPulseSpectrum ∘ half) :=
    funext dyadicPulseSpectrum_halving
  calc analyticOrderAt dyadicPulseSpectrum p = analyticOrderAt (entireSinc*(dyadicPulseSpectrum ∘ half)) p :=
         congrArg (fun f : ℂ → ℂ => analyticOrderAt f p) hf
       _ = _ := by
         rw [analyticOrderAt_mul (differentiable_entireSinc.analyticAt p)
           ((differentiable_dyadicPulseSpectrum.analyticAt _).comp ha),hh,sinc_simple hk]

/-- Every odd multiple of 2ʲπ has order exactly j+1, on either side of
the origin. Thus the blind frequencies have unbounded multiplicity. -/
theorem dyadicPulseSpectrum_lattice_order (j : ℕ) (k : ℤ) :
    analyticOrderAt dyadicPulseSpectrum (((2^j*(2*k+1):ℤ):ℂ)*(Real.pi:ℂ)) =
      ((j+1:ℕ):ℕ∞) := by
  have hk : 2*k+1≠0 := by omega
  have hpi : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  induction j with
  | zero =>
    rw [pow_zero,one_mul,order_step hk]
    have hn : dyadicPulseSpectrum ((1/2:ℂ)*(((2*k+1:ℤ):ℂ)*(Real.pi:ℂ)))≠0 := by
      intro hz
      obtain ⟨a,_,he⟩ := (dyadicPulseSpectrum_zero_iff _).mp hz
      have h₁ : (((2*k+1:ℤ):ℂ))=2*(a:ℂ) := by
        apply mul_right_cancel₀ hpi
        linear_combination (2:ℂ)*he
      have h₂ : 2*k+1=2*a := by exact_mod_cast h₁
      omega
    rw [(differentiable_dyadicPulseSpectrum.analyticAt _).analyticOrderAt_eq_zero.mpr hn]
    norm_num
  | succ j ih =>
    have hl : (2:ℤ)^(j+1)*(2*k+1)≠0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hk
    rw [order_step hl]
    have he : (1/2:ℂ)*(((2^(j+1)*(2*k+1):ℤ):ℂ)*(Real.pi:ℂ)) =
        ((2^j*(2*k+1):ℤ):ℂ)*(Real.pi:ℂ) := by push_cast; rw [pow_succ]; ring
    rw [he,ih]
    exact_mod_cast (Nat.add_comm 1 (j+1))

#print axioms differentiable_dyadicPulseSpectrum
#print axioms dyadicPulseSpectrum_zero_iff
#print axioms dyadicPulseSpectrum_lattice_order
end GaloisForLFunctions.BlackHoleRingdown
