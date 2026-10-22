import GaloisForLFunctions.RHTower.Deninger.DeningerPoissonZeroDivisor
import GaloisForLFunctions.RHTower.Deninger.DeningerPoissonInjective

/-!
# The cokernel of the Poisson operator, and the zero divisor of zeta

Every member of the radial space is bounded by `x^{-s}` on the multiplicative half line for every
integer `s`, because its `s`-th weight is a Schwartz function; so its Mellin transform converges
everywhere and is entire.  The Mellin transform is therefore additive on the radial space, and the
elements whose transform vanishes at a prescribed point form a subspace.

The Poisson operator is injective, so

`0 → ℋ_∩ → ℋ_− → M_ζ → 0`

is exact with `M_ζ` its cokernel, and the image lies in the subspace of the radial space cut out by
the non-real zeros of `ζ` in the right half plane.

* `deningerRadialValue` : the multiplicative-coordinate function of a radial family.
* `mellinConvergent_deningerRadialValue` : **its Mellin transform converges everywhere.**
* `DeningerMZeta`, `deningerPoisson_exact` : the cokernel and exactness.
* `deningerZetaZeroSubspace`, `deningerPoisson_range_le_zetaZero` : **the image lies in the
  zero-divisor subspace of `ζ`.**
-/

open scoped Real SchwartzMap FourierTransform Topology
open Complex MeasureTheory Set Filter Asymptotics GaloisForLFunctions
open GaloisForLFunctions.RHTower

noncomputable section

namespace RHTower

/-! ## The multiplicative-coordinate function of a radial family -/

/-- The function on the multiplicative half line attached to a member of the radial space: the
zeroth weight read in the multiplicative coordinate. -/
def deningerRadialValue (g : deningerRadialCompat) (x : ℝ) : ℂ :=
  ((g : ∀ _ : ℤ, 𝓢(ℝ, ℂ)) 0) (Real.log x)

theorem deningerRadialValue_add (g h : deningerRadialCompat) (x : ℝ) :
    deningerRadialValue (g + h) x = deningerRadialValue g x + deningerRadialValue h x := rfl

theorem deningerRadialValue_smul (c : ℂ) (g : deningerRadialCompat) (x : ℝ) :
    deningerRadialValue (c • g) x = c * deningerRadialValue g x := rfl

theorem continuous_deningerRadialValue (g : deningerRadialCompat) :
    ContinuousOn (deningerRadialValue g) (Ioi 0) := by
  have hlogc : ContinuousOn Real.log (Ioi (0 : ℝ)) := by
    refine Real.continuousOn_log.mono fun x hx => ?_
    have hx' : (0 : ℝ) < x := hx
    exact hx'.ne'
  exact ((g : ∀ _ : ℤ, 𝓢(ℝ, ℂ)) 0).continuous.comp_continuousOn hlogc

/-! ## Two-ended decay of a radial family -/

theorem norm_deningerRadialValue_le (g : deningerRadialCompat) (s : ℤ) {x : ℝ} (hx : 0 < x) :
    ‖deningerRadialValue g x‖
      ≤ SchwartzMap.seminorm ℂ 0 0 ((g : ∀ _ : ℤ, 𝓢(ℝ, ℂ)) s) * x ^ (-(s : ℝ)) := by
  have hcompat := g.2 s (Real.log x)
  have hexp : Complex.exp ((s : ℂ) * (Real.log x : ℝ))
      = ((x ^ (s : ℝ) : ℝ) : ℂ) := by
    rw [Real.rpow_def_of_pos hx, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hexp] at hcompat
  have hval : deningerRadialValue g x
      = ((x ^ (-(s : ℝ)) : ℝ) : ℂ) * ((g : ∀ _ : ℤ, 𝓢(ℝ, ℂ)) s) (Real.log x) := by
    have hsum : (-(s : ℝ)) + (s : ℝ) = 0 := by ring
    show ((g : ∀ _ : ℤ, 𝓢(ℝ, ℂ)) 0) (Real.log x) = _
    rw [hcompat, ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add hx, hsum,
      Real.rpow_zero, Complex.ofReal_one, one_mul]
  rw [hval, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hx.le _)]
  have hb : ‖((g : ∀ _ : ℤ, 𝓢(ℝ, ℂ)) s) (Real.log x)‖
      ≤ SchwartzMap.seminorm ℂ 0 0 ((g : ∀ _ : ℤ, 𝓢(ℝ, ℂ)) s) :=
    SchwartzMap.norm_le_seminorm ℂ _ _
  calc x ^ (-(s : ℝ)) * ‖((g : ∀ _ : ℤ, 𝓢(ℝ, ℂ)) s) (Real.log x)‖
      ≤ x ^ (-(s : ℝ)) * SchwartzMap.seminorm ℂ 0 0 ((g : ∀ _ : ℤ, 𝓢(ℝ, ℂ)) s) :=
        mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hx.le _)
    _ = SchwartzMap.seminorm ℂ 0 0 ((g : ∀ _ : ℤ, 𝓢(ℝ, ℂ)) s) * x ^ (-(s : ℝ)) := by ring

theorem isBigO_deningerRadialValue_atTop (g : deningerRadialCompat) (a : ℝ) :
    (deningerRadialValue g) =O[atTop] fun x : ℝ => x ^ (-a) := by
  set s : ℤ := ⌈a⌉ with hs
  have hsa : a ≤ (s : ℝ) := Int.le_ceil a
  refine Asymptotics.isBigO_iff.mpr
    ⟨SchwartzMap.seminorm ℂ 0 0 ((g : ∀ _ : ℤ, 𝓢(ℝ, ℂ)) s), ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hbound := norm_deningerRadialValue_le g s hx0
  have hle : x ^ (-(s : ℝ)) ≤ x ^ (-a) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hnorm : ‖x ^ (-a)‖ = x ^ (-a) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
  rw [hnorm]
  refine hbound.trans ?_
  exact mul_le_mul_of_nonneg_left hle (apply_nonneg _ _)

theorem isBigO_deningerRadialValue_zero (g : deningerRadialCompat) (b : ℝ) :
    (deningerRadialValue g) =O[𝓝[>] (0 : ℝ)] fun x : ℝ => x ^ (-b) := by
  set s : ℤ := ⌊b⌋ with hs
  have hsb : (s : ℝ) ≤ b := Int.floor_le b
  refine Asymptotics.isBigO_iff.mpr
    ⟨SchwartzMap.seminorm ℂ 0 0 ((g : ∀ _ : ℤ, 𝓢(ℝ, ℂ)) s), ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with x hx hx1
  have hx0 : (0 : ℝ) < x := hx
  have hxle : x ≤ 1 := le_of_lt hx1
  have hbound := norm_deningerRadialValue_le g s hx0
  have hnorm : ‖x ^ (-b)‖ = x ^ (-b) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
  rw [hnorm]
  refine hbound.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (apply_nonneg _ _)
  exact Real.rpow_le_rpow_of_exponent_ge hx0 hxle (by linarith)

/-! ## Convergence of the Mellin transform on the radial space -/

theorem mellinConvergent_deningerRadialValue (g : deningerRadialCompat) (s : ℂ) :
    MellinConvergent (deningerRadialValue g) s := by
  refine mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1)
    ((continuous_deningerRadialValue g).locallyIntegrableOn measurableSet_Ioi)
    (isBigO_deningerRadialValue_atTop g (s.re + 1)) (by linarith)
    (isBigO_deningerRadialValue_zero g (s.re - 1)) (by linarith)

theorem mellin_deningerRadialValue_add (g h : deningerRadialCompat) (s : ℂ) :
    mellin (deningerRadialValue (g + h)) s
      = mellin (deningerRadialValue g) s + mellin (deningerRadialValue h) s := by
  have hg := mellinConvergent_deningerRadialValue g s
  have hh := mellinConvergent_deningerRadialValue h s
  rw [mellin, mellin, mellin, ← integral_add hg hh]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [deningerRadialValue_add, smul_add]

theorem mellin_deningerRadialValue_smul (c : ℂ) (g : deningerRadialCompat) (s : ℂ) :
    mellin (deningerRadialValue (c • g)) s = c * mellin (deningerRadialValue g) s := by
  rw [mellin, mellin]
  have hfun : ∀ x : ℝ, (x : ℂ) ^ (s - 1) • deningerRadialValue (c • g) x
      = c • ((x : ℂ) ^ (s - 1) • deningerRadialValue g x) := by
    intro x
    rw [deningerRadialValue_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring
  rw [funext hfun, integral_smul, smul_eq_mul]

/-! ## The cokernel -/

/-- **The cokernel `M_ζ` of the Poisson operator.** -/
abbrev DeningerMZeta : Type :=
  (deningerRadialCompat ⧸ LinearMap.range deningerPoissonLM)

/-- The projection onto the cokernel. -/
def deningerMZetaMk : deningerRadialCompat →ₗ[ℂ] DeningerMZeta :=
  (LinearMap.range deningerPoissonLM).mkQ

theorem deningerMZetaMk_surjective : Function.Surjective deningerMZetaMk :=
  Submodule.mkQ_surjective _

/-- **The Poisson sequence is exact at the radial space.** -/
theorem deningerPoisson_exact : Function.Exact deningerPoissonLM deningerMZetaMk := by
  rw [LinearMap.exact_iff]
  exact Submodule.ker_mkQ _

/-! ## The zero-divisor subspace -/

/-- The members of the radial space whose multiplicative Mellin transform vanishes at every
non-real zero of `ζ` in the right half plane. -/
def deningerZetaZeroSubspace : Submodule ℂ deningerRadialCompat where
  carrier := {g | ∀ ρ : ℂ, 0 < ρ.re → ρ.im ≠ 0 → riemannZeta ρ = 0 →
    mellin (deningerRadialValue g) ρ = 0}
  add_mem' {g h} hg hh := by
    intro ρ hre him hζ
    rw [mellin_deningerRadialValue_add, hg ρ hre him hζ, hh ρ hre him hζ, add_zero]
  zero_mem' := by
    intro ρ _ _ _
    have hfun : deningerRadialValue (0 : deningerRadialCompat) = fun _ : ℝ => (0 : ℂ) := by
      funext x
      rfl
    rw [hfun, mellin]
    simp
  smul_mem' c g hg := by
    intro ρ hre him hζ
    rw [mellin_deningerRadialValue_smul, hg ρ hre him hζ, mul_zero]

theorem deningerRadialValue_poisson (f : DeningerMeyerCap) {x : ℝ} (hx : 0 < x) :
    deningerRadialValue (deningerPoissonLM f) x = deningerPoissonValue (f : 𝓢(ℝ, ℂ)) x := by
  show deningerPoissonWeight 0 (f : 𝓢(ℝ, ℂ)) (Real.log x) = _
  rw [deningerPoissonWeight, deningerExpWeight]
  have hzero : ((Real.exp (((0 : ℤ) : ℝ) * Real.log x) : ℝ) : ℂ) = 1 := by
    norm_num
  rw [hzero, one_mul, deningerPoissonLog_eq, Real.exp_log hx]

theorem mellin_deningerRadialValue_poisson (f : DeningerMeyerCap) (s : ℂ) :
    mellin (deningerRadialValue (deningerPoissonLM f)) s
      = mellin (deningerPoissonValue (f : 𝓢(ℝ, ℂ))) s := by
  rw [mellin, mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx' : (0 : ℝ) < x := hx
  rw [deningerRadialValue_poisson f hx']

/-- **The image of the Poisson operator lies in the zero-divisor subspace of `ζ`.** -/
theorem deningerPoisson_range_le_zetaZero :
    LinearMap.range deningerPoissonLM ≤ deningerZetaZeroSubspace := by
  rintro g ⟨f, rfl⟩
  intro ρ hre him hζ
  rw [mellin_deningerRadialValue_poisson f ρ]
  exact mellin_deningerPoissonValue_eq_zero_of_zeta_eq_zero f.2 hre him hζ

end RHTower

end
