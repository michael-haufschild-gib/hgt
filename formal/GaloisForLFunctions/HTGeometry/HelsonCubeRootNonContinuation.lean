import GaloisForLFunctions.HTGeometry.HelsonZetaEulerProduct
import Mathlib.Analysis.Meromorphic.Order

/-!
# A Helson zeta function with no meromorphic continuation

The phase that takes the same primitive cube root of unity `ω` at every prime carries a Helson zeta
function that is **not** meromorphic at `s = 1`.  The obstruction is a half-integral order: since
`1`, `ω` and `ω̄` are the three cube roots of unity,

```text
(1 - ω x)(1 - ω̄ x)(1 - x) = 1 - x ^ 3 ,
```

so on the half plane of absolute convergence the Euler products multiply to

```text
Z_ω(s) · Z_ω(s)‾ · ζ(s) = ζ(3 s)   for real `s`,
```

because the conjugate phase is the complex conjugate of `Z_ω` along the real axis.  As `σ ↓ 1` the
right side tends to `ζ(3) ≠ 0` and `(σ - 1) ζ(σ) → 1`, so `‖Z_ω(σ)‖ ²` vanishes to order exactly
one.  A function meromorphic at `1` has `‖F(σ)‖ ²` vanishing to an even order, and no even integer
equals one.

Consequently every finite modification of that phase is noncontinuable, and the noncontinuable
phases are dense in the phase torus.  Together with the density of the continuable stratum this
makes the continuation seam boundary-everywhere with no probabilistic input.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### A primitive cube root of unity -/

/-- The primitive cube root of unity in the upper half plane. -/
def cubeRootUnit : ℂ := -1 / 2 + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I

@[simp] theorem cubeRootUnit_re : cubeRootUnit.re = -1 / 2 := by
  simp [cubeRootUnit]

@[simp] theorem cubeRootUnit_im : cubeRootUnit.im = Real.sqrt 3 / 2 := by
  simp [cubeRootUnit]

theorem normSq_cubeRootUnit : Complex.normSq cubeRootUnit = 1 := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [Complex.normSq_apply, cubeRootUnit_re, cubeRootUnit_im]
  nlinarith [h3]

@[simp] theorem norm_cubeRootUnit : ‖cubeRootUnit‖ = 1 := by
  have h := normSq_cubeRootUnit
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg cubeRootUnit, h]

theorem cubeRootUnit_add_conj : cubeRootUnit + (starRingEnd ℂ) cubeRootUnit = -1 := by
  rw [Complex.add_conj, cubeRootUnit_re]
  norm_num

theorem cubeRootUnit_mul_conj : cubeRootUnit * (starRingEnd ℂ) cubeRootUnit = 1 := by
  rw [Complex.mul_conj, normSq_cubeRootUnit]
  norm_num

/-- **The cube-root factorization.**  The three linear factors attached to the cube roots of unity
multiply to `1 - x ^ 3`. -/
theorem cubeRoot_factorization (x : ℂ) :
    (1 - cubeRootUnit * x) * (1 - (starRingEnd ℂ) cubeRootUnit * x) * (1 - x) = 1 - x ^ 3 := by
  have h1 := cubeRootUnit_add_conj
  have h2 := cubeRootUnit_mul_conj
  linear_combination (-x + x ^ 2) * h1 + (x ^ 2 - x ^ 3) * h2

/-! ### The Euler factors on the real axis -/

/-- On the real axis a prime power is a positive real. -/
theorem prime_cpow_ofReal (p : Nat.Primes) (σ : ℝ) :
    ((p : ℂ)) ^ (-((σ : ℝ) : ℂ)) = (((p : ℕ) : ℝ) ^ (-σ) : ℝ) := by
  have hp0 : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := Nat.cast_nonneg _
  have hcast : (-((σ : ℝ) : ℂ)) = (((-σ : ℝ)) : ℂ) := by push_cast; ring
  have hpc : ((p : ℂ)) = (((((p : ℕ) : ℝ))) : ℂ) := by push_cast; ring
  rw [hpc, hcast, ← Complex.ofReal_cpow hp0]

/-- The cube of a real prime power is the prime power at three times the abscissa. -/
theorem prime_rpow_cube (p : Nat.Primes) (σ : ℝ) :
    (((p : ℕ) : ℝ) ^ (-σ)) ^ (3 : ℕ) = ((p : ℕ) : ℝ) ^ (-(3 * σ)) := by
  have hp0 : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [← Real.rpow_natCast (((p : ℕ) : ℝ) ^ (-σ)) 3, ← Real.rpow_mul hp0]
  norm_num
  ring_nf

/-! ### The modulus identity -/

/-- **The cube-root Helson zeta has modulus square `ζ(3σ)/ζ(σ)` on the real axis.**  Multiplying the
Euler products of the phase, its conjugate and the trivial phase gives the Euler product at three
times the abscissa. -/
theorem norm_sq_mul_riemannZeta {F : ℂ → ℂ}
    (hF : ∀ s : ℂ, 1 < s.re →
      HasProd (fun p : Nat.Primes => (1 - cubeRootUnit * (p : ℂ) ^ (-s))⁻¹) (F s))
    {σ : ℝ} (hσ : 1 < σ) :
    ‖F ((σ : ℝ) : ℂ)‖ ^ 2 * ‖riemannZeta ((σ : ℝ) : ℂ)‖
      = ‖riemannZeta (((3 * σ : ℝ)) : ℂ)‖ := by
  have hs : (1 : ℝ) < (((σ : ℝ) : ℂ)).re := by simpa using hσ
  have hs3 : (1 : ℝ) < ((((3 * σ : ℝ)) : ℂ)).re := by
    have : (1 : ℝ) < 3 * σ := by linarith
    simpa using this
  set s : ℂ := ((σ : ℝ) : ℂ) with hsdef
  have h1 := hF s hs
  -- the conjugate phase
  have hconj : HasProd
      (fun p : Nat.Primes => (1 - (starRingEnd ℂ) cubeRootUnit * (p : ℂ) ^ (-s))⁻¹)
      ((starRingEnd ℂ) (F s)) := by
    have hmap := h1.map (starRingEnd ℂ) Complex.continuous_conj
    refine hmap.congr_fun ?_
    intro p
    have hreal : ((p : ℂ)) ^ (-s) = ((((p : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) := by
      rw [hsdef]; exact prime_cpow_ofReal p σ
    rw [Function.comp_apply, hreal]
    rw [map_inv₀, map_sub, map_one, map_mul, Complex.conj_ofReal]
  have hzeta := riemannZeta_eulerProduct_hasProd hs
  have hzeta3 := riemannZeta_eulerProduct_hasProd hs3
  have hprod := (h1.mul hconj).mul hzeta
  have hshape : (fun p : Nat.Primes =>
      (1 - cubeRootUnit * (p : ℂ) ^ (-s))⁻¹
        * (1 - (starRingEnd ℂ) cubeRootUnit * (p : ℂ) ^ (-s))⁻¹
        * (1 - (p : ℂ) ^ (-s))⁻¹)
      = fun p : Nat.Primes => (1 - (p : ℂ) ^ (-(((3 * σ : ℝ)) : ℂ)))⁻¹ := by
    funext p
    have hunit : ∀ z : ℂ, ‖z‖ ≤ 1 → (1 : ℂ) - z * (p : ℂ) ^ (-s) ≠ 0 := by
      intro z hz
      exact one_sub_phase_prime_cpow_ne_zero (χ := fun _ => z) (fun _ => hz) hs
    have hω : (1 : ℂ) - cubeRootUnit * (p : ℂ) ^ (-s) ≠ 0 :=
      hunit _ (le_of_eq norm_cubeRootUnit)
    have hωc : (1 : ℂ) - (starRingEnd ℂ) cubeRootUnit * (p : ℂ) ^ (-s) ≠ 0 := by
      refine hunit _ ?_
      rw [RCLike.norm_conj]
      exact le_of_eq norm_cubeRootUnit
    have hone : (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := one_sub_prime_cpow_ne_zero hs
    have hcube : ((p : ℂ)) ^ (-(((3 * σ : ℝ)) : ℂ)) = (((p : ℂ)) ^ (-s)) ^ (3 : ℕ) := by
      rw [hsdef, prime_cpow_ofReal p σ, prime_cpow_ofReal p (3 * σ)]
      rw [← Complex.ofReal_pow, prime_rpow_cube p σ]
    rw [hcube, ← cubeRoot_factorization ((p : ℂ) ^ (-s))]
    field_simp
  rw [hshape] at hprod
  have heq : F s * (starRingEnd ℂ) (F s) * riemannZeta s
      = riemannZeta (((3 * σ : ℝ)) : ℂ) := hprod.unique hzeta3
  have hnorm := congrArg (fun z : ℂ => ‖z‖) heq
  simp only [norm_mul, RCLike.norm_conj] at hnorm
  rw [← hnorm]
  ring

/-! ### The phase and its noncontinuability -/

/-- The phase taking the same primitive cube root of unity at every prime. -/
def cubeRootPhase : PhaseTorus := fun _ => ⟨cubeRootUnit, norm_cubeRootUnit⟩

@[simp] theorem cubeRootPhase_coe (p : Nat.Primes) : ((cubeRootPhase p : ℂ)) = cubeRootUnit := rfl

/-- The real abscissae above one approach `1` inside the punctured plane. -/
theorem tendsto_ofReal_nhdsWithin_ne :
    Filter.Tendsto (fun σ : ℝ => ((σ : ℝ) : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have hcont : Filter.Tendsto (fun σ : ℝ => ((σ : ℝ) : ℂ)) (𝓝 (1 : ℝ)) (𝓝 (((1 : ℝ) : ℂ))) :=
      Complex.continuous_ofReal.tendsto 1
    simpa using hcont.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have h1 : σ = 1 := by exact_mod_cast h
    rw [h1] at hσ
    exact lt_irrefl 1 (Set.mem_Ioi.mp hσ)

/-- **The constant cube-root phase is not continuable.**  Its Helson zeta would have to vanish to
half-integral order at `s = 1`. -/
theorem notMem_continuableStratum_cubeRootPhase :
    cubeRootPhase ∉ continuableStratum := by
  rintro ⟨F, hFmero, hFprod⟩
  have hFprod' : ∀ s : ℂ, 1 < s.re →
      HasProd (fun p : Nat.Primes => (1 - cubeRootUnit * (p : ℂ) ^ (-s))⁻¹) (F s) := by
    intro s hs
    simpa using hFprod s hs
  -- the modulus identity, on the whole ray
  have hid : ∀ σ : ℝ, 1 < σ →
      ‖F ((σ : ℝ) : ℂ)‖ ^ 2 * ‖riemannZeta ((σ : ℝ) : ℂ)‖
        = ‖riemannZeta (((3 * σ : ℝ)) : ℂ)‖ := fun σ hσ => norm_sq_mul_riemannZeta hFprod' hσ
  -- the right side does not vanish
  have hzeta3ne : riemannZeta ((3 : ℂ)) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_lt_re ?_
    norm_num
  have hFne : ∀ σ : ℝ, 1 < σ → F ((σ : ℝ) : ℂ) ≠ 0 := by
    intro σ hσ hzero
    have h3 : riemannZeta (((3 * σ : ℝ)) : ℂ) ≠ 0 := by
      refine riemannZeta_ne_zero_of_one_lt_re ?_
      have : (1 : ℝ) < 3 * σ := by linarith
      simpa using this
    have := hid σ hσ
    rw [hzero] at this
    simp only [norm_zero] at this
    exact h3 (norm_eq_zero.mp (by linarith [this, norm_nonneg (riemannZeta ((3 * σ : ℝ) : ℂ))]))
  have hmero : MeromorphicAt F 1 := hFmero 1 (Set.mem_univ _)
  -- the order is a finite integer
  have hnotTop : meromorphicOrderAt F 1 ≠ ⊤ := by
    intro htop
    have hev := meromorphicOrderAt_eq_top_iff.mp htop
    have hpull := tendsto_ofReal_nhdsWithin_ne.eventually hev
    obtain ⟨σ, hσzero, hσgt⟩ := ((hpull.and self_mem_nhdsWithin).exists)
    exact hFne σ (Set.mem_Ioi.mp hσgt) hσzero
  obtain ⟨n, hn⟩ : ∃ n : ℤ, meromorphicOrderAt F 1 = (n : WithTop ℤ) := by
    cases hord : meromorphicOrderAt F 1 with
    | top => exact absurd hord hnotTop
    | coe m => exact ⟨m, rfl⟩
  obtain ⟨g, hganalytic, hg1, hgev⟩ := (meromorphicOrderAt_eq_int_iff hmero).mp hn
  -- transport the factorization to the real ray
  have hgev' : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      F ((σ : ℝ) : ℂ) = (((σ : ℝ) : ℂ) - 1) ^ n • g ((σ : ℝ) : ℂ) :=
    tendsto_ofReal_nhdsWithin_ne.eventually hgev
  have hkey : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      (σ - 1) ^ (2 * n - 1) * (‖g ((σ : ℝ) : ℂ)‖ ^ 2 * ((σ - 1) * ‖riemannZeta ((σ : ℝ) : ℂ)‖))
        = ‖riemannZeta (((3 * σ : ℝ)) : ℂ)‖ := by
    filter_upwards [hgev', self_mem_nhdsWithin] with σ hσfac hσgt
    have hσ : 1 < σ := Set.mem_Ioi.mp hσgt
    have hpos : (0 : ℝ) < σ - 1 := by linarith
    have hne : (σ - 1 : ℝ) ≠ 0 := ne_of_gt hpos
    have hnormF : ‖F ((σ : ℝ) : ℂ)‖ = (σ - 1) ^ n * ‖g ((σ : ℝ) : ℂ)‖ := by
      rw [hσfac, smul_eq_mul, norm_mul, norm_zpow]
      congr 2
      have hnr : ‖((σ : ℝ) : ℂ) - 1‖ = |σ - 1| := by
        rw [show ((σ : ℝ) : ℂ) - 1 = (((σ - 1 : ℝ)) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs]
      rw [hnr, abs_of_pos hpos]
    have hbase := hid σ hσ
    rw [hnormF] at hbase
    have hsplit : (σ - 1 : ℝ) ^ (2 * n) = (σ - 1) ^ (2 * n - 1) * (σ - 1) := by
      have hz := zpow_add₀ hne (2 * n - 1) 1
      rw [show 2 * n - 1 + 1 = 2 * n by ring, zpow_one] at hz
      exact hz
    calc (σ - 1) ^ (2 * n - 1)
            * (‖g ((σ : ℝ) : ℂ)‖ ^ 2 * ((σ - 1) * ‖riemannZeta ((σ : ℝ) : ℂ)‖))
        = ((σ - 1) ^ (2 * n - 1) * (σ - 1)) * ‖g ((σ : ℝ) : ℂ)‖ ^ 2
            * ‖riemannZeta ((σ : ℝ) : ℂ)‖ := by ring
      _ = (σ - 1) ^ (2 * n) * ‖g ((σ : ℝ) : ℂ)‖ ^ 2 * ‖riemannZeta ((σ : ℝ) : ℂ)‖ := by
            rw [hsplit]
      _ = ((σ - 1) ^ n * ‖g ((σ : ℝ) : ℂ)‖) ^ 2 * ‖riemannZeta ((σ : ℝ) : ℂ)‖ := by
            rw [mul_pow, ← zpow_natCast ((σ - 1 : ℝ) ^ n) 2, ← zpow_mul]
            ring_nf
      _ = ‖riemannZeta (((3 * σ : ℝ)) : ℂ)‖ := hbase
  -- the two sides have positive limits, up to a power of `σ - 1`
  have hPlim : Filter.Tendsto
      (fun σ : ℝ => ‖g ((σ : ℝ) : ℂ)‖ ^ 2 * ((σ - 1) * ‖riemannZeta ((σ : ℝ) : ℂ)‖))
      (𝓝[>] (1 : ℝ)) (𝓝 (‖g 1‖ ^ 2 * 1)) := by
    refine Filter.Tendsto.mul ?_ ?_
    · have hcont : ContinuousAt g 1 := hganalytic.continuousAt
      have hcomp : Filter.Tendsto (fun σ : ℝ => g ((σ : ℝ) : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (g 1)) := by
        refine hcont.tendsto.comp ?_
        exact tendsto_ofReal_nhdsWithin_ne.mono_right nhdsWithin_le_nhds
      exact (hcomp.norm).pow 2
    · have hres := riemannZeta_residue_one.comp tendsto_ofReal_nhdsWithin_ne
      have hnorm := hres.norm
      simp only [norm_one] at hnorm
      refine hnorm.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with σ hσgt
      have hσ : 1 < σ := Set.mem_Ioi.mp hσgt
      have hpos : (0 : ℝ) < σ - 1 := by linarith
      simp only [Function.comp_apply, norm_mul]
      congr 1
      rw [show ((σ : ℝ) : ℂ) - 1 = (((σ - 1 : ℝ)) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hpos]
  have hQlim : Filter.Tendsto (fun σ : ℝ => ‖riemannZeta (((3 * σ : ℝ)) : ℂ)‖)
      (𝓝[>] (1 : ℝ)) (𝓝 ‖riemannZeta ((3 : ℂ))‖) := by
    have hcont : ContinuousAt riemannZeta (3 : ℂ) :=
      (differentiableAt_riemannZeta (by norm_num)).continuousAt
    have hcomp : Filter.Tendsto (fun σ : ℝ => (((3 * σ : ℝ)) : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (3 : ℂ)) := by
      have h1 : Filter.Tendsto (fun σ : ℝ => (3 * σ : ℝ)) (𝓝[>] (1 : ℝ)) (𝓝 (3 : ℝ)) := by
        have hc : Continuous (fun σ : ℝ => (3 * σ : ℝ)) := by fun_prop
        have := (hc.tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
        simpa using this
      have h2 : Filter.Tendsto (fun r : ℝ => ((r : ℝ) : ℂ)) (𝓝 (3 : ℝ)) (𝓝 (((3 : ℝ) : ℂ))) :=
        Complex.continuous_ofReal.tendsto 3
      have hcomp2 := h2.comp h1
      simpa [Function.comp_def] using hcomp2
    exact (hcont.tendsto.comp hcomp).norm
  have hg1ne : ‖g 1‖ ^ 2 * 1 ≠ 0 := by
    rw [mul_one]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hg1)
  have hz3ne : ‖riemannZeta ((3 : ℂ))‖ ≠ 0 := norm_ne_zero_iff.mpr hzeta3ne
  -- an odd power of `σ - 1` cannot have a nonzero limit
  rcases lt_or_gt_of_ne (show 2 * n - 1 ≠ 0 by omega) with hneg | hpos
  · -- negative exponent: multiply it away
    set m : ℕ := (1 - 2 * n).toNat with hm
    have hmpos : 1 ≤ m := by omega
    have hmcast : ((m : ℤ)) = 1 - 2 * n := by omega
    have hkey2 : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
        ‖g ((σ : ℝ) : ℂ)‖ ^ 2 * ((σ - 1) * ‖riemannZeta ((σ : ℝ) : ℂ)‖)
          = ‖riemannZeta (((3 * σ : ℝ)) : ℂ)‖ * (σ - 1) ^ m := by
      filter_upwards [hkey, self_mem_nhdsWithin] with σ hσkey hσgt
      have hσ : 1 < σ := Set.mem_Ioi.mp hσgt
      have hne : (σ - 1 : ℝ) ≠ 0 := by
        have : (0 : ℝ) < σ - 1 := by linarith
        exact ne_of_gt this
      have hmul : (σ - 1 : ℝ) ^ (2 * n - 1) * (σ - 1) ^ m = 1 := by
        rw [← zpow_natCast (σ - 1 : ℝ) m, ← zpow_add₀ hne, hmcast]
        simp
      calc ‖g ((σ : ℝ) : ℂ)‖ ^ 2 * ((σ - 1) * ‖riemannZeta ((σ : ℝ) : ℂ)‖)
          = ((σ - 1 : ℝ) ^ (2 * n - 1) * (σ - 1) ^ m)
              * (‖g ((σ : ℝ) : ℂ)‖ ^ 2 * ((σ - 1) * ‖riemannZeta ((σ : ℝ) : ℂ)‖)) := by
                rw [hmul, one_mul]
        _ = ((σ - 1 : ℝ) ^ (2 * n - 1)
              * (‖g ((σ : ℝ) : ℂ)‖ ^ 2 * ((σ - 1) * ‖riemannZeta ((σ : ℝ) : ℂ)‖)))
              * (σ - 1) ^ m := by ring
        _ = ‖riemannZeta (((3 * σ : ℝ)) : ℂ)‖ * (σ - 1) ^ m := by rw [hσkey]
    have hrhs : Filter.Tendsto
        (fun σ : ℝ => ‖riemannZeta (((3 * σ : ℝ)) : ℂ)‖ * (σ - 1) ^ m)
        (𝓝[>] (1 : ℝ)) (𝓝 (‖riemannZeta ((3 : ℂ))‖ * 0)) := by
      refine hQlim.mul ?_
      have hbase : Filter.Tendsto (fun σ : ℝ => σ - 1) (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
        have hc : Continuous (fun σ : ℝ => σ - 1) := by fun_prop
        have := (hc.tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
        simpa using this
      have := hbase.pow m
      simpa [zero_pow (by omega : m ≠ 0)] using this
    have := tendsto_nhds_unique (hPlim.congr' hkey2) hrhs
    rw [mul_zero] at this
    exact hg1ne this
  · -- positive exponent: the left side tends to zero
    set m : ℕ := (2 * n - 1).toNat with hm
    have hmpos : 1 ≤ m := by omega
    have hmcast : ((m : ℤ)) = 2 * n - 1 := by omega
    have hkey2 : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
        (σ - 1) ^ m * (‖g ((σ : ℝ) : ℂ)‖ ^ 2 * ((σ - 1) * ‖riemannZeta ((σ : ℝ) : ℂ)‖))
          = ‖riemannZeta (((3 * σ : ℝ)) : ℂ)‖ := by
      filter_upwards [hkey] with σ hσkey
      rw [← hσkey, ← zpow_natCast (σ - 1 : ℝ) m, hmcast]
    have hlhs : Filter.Tendsto
        (fun σ : ℝ => (σ - 1) ^ m * (‖g ((σ : ℝ) : ℂ)‖ ^ 2
          * ((σ - 1) * ‖riemannZeta ((σ : ℝ) : ℂ)‖)))
        (𝓝[>] (1 : ℝ)) (𝓝 (0 * (‖g 1‖ ^ 2 * 1))) := by
      refine Filter.Tendsto.mul ?_ hPlim
      have hbase : Filter.Tendsto (fun σ : ℝ => σ - 1) (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
        have hc : Continuous (fun σ : ℝ => σ - 1) := by fun_prop
        have := (hc.tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
        simpa using this
      have := hbase.pow m
      simpa [zero_pow (by omega : m ≠ 0)] using this
    have := tendsto_nhds_unique (hlhs.congr' hkey2) hQlim
    rw [zero_mul] at this
    exact hz3ne this.symm

/-! ### Transfer along finite modifications -/

/-- The ratio of two Euler factors at the same prime. -/
def eulerRatio (a c b : ℂ) : ℂ → ℂ :=
  fun s => (1 - c * a ^ (-s)) / (1 - b * a ^ (-s))

theorem meromorphicAt_eulerRatio {a c b : ℂ} (ha : a ≠ 0) (s : ℂ) :
    MeromorphicAt (eulerRatio a c b) s := by
  have hnum : AnalyticAt ℂ (fun z : ℂ => 1 - c * a ^ (-z)) s :=
    analyticAt_const.sub (analyticAt_const.mul (analyticAt_const_cpow_neg ha s))
  have hden : AnalyticAt ℂ (fun z : ℂ => 1 - b * a ^ (-z)) s :=
    analyticAt_const.sub (analyticAt_const.mul (analyticAt_const_cpow_neg ha s))
  exact hnum.meromorphicAt.div hden.meromorphicAt

/-- **Continuability transfers along finite modifications of the phase.** -/
theorem mem_continuableStratum_of_finite_ne {χ ψ : PhaseTorus}
    (hψ : ψ ∈ continuableStratum) (hfin : {p : Nat.Primes | (χ p : ℂ) ≠ (ψ p : ℂ)}.Finite) :
    χ ∈ continuableStratum := by
  classical
  obtain ⟨F, hFmero, hFprod⟩ := hψ
  set c : Nat.Primes → ℂ → ℂ := fun p => eulerRatio ((p : ℂ)) (ψ p) (χ p) with hcdef
  refine ⟨fun s => F s * ∏ p ∈ hfin.toFinset, c p s, ?_, ?_⟩
  · intro s hs
    refine (hFmero s hs).mul ?_
    refine meromorphicAt_finsetProd _ c s ?_
    intro p _
    refine meromorphicAt_eulerRatio ?_ s
    exact_mod_cast Nat.cast_ne_zero.mpr p.2.ne_zero
  · intro s hs
    have hunitψ : ∀ p : Nat.Primes, ‖(ψ p : ℂ)‖ ≤ 1 := fun p => le_of_eq (ψ p).2
    have hunitχ : ∀ p : Nat.Primes, ‖(χ p : ℂ)‖ ≤ 1 := fun p => le_of_eq (χ p).2
    have hcorr : HasProd (fun p : Nat.Primes => c p s) (∏ p ∈ hfin.toFinset, c p s) := by
      refine hasProd_prod_of_ne_finset_one ?_
      intro p hp
      have hpe : (χ p : ℂ) = (ψ p : ℂ) := by
        by_contra hne
        exact hp (hfin.mem_toFinset.mpr hne)
      have hdenψp : (1 : ℂ) - (ψ p : ℂ) * ((p : ℂ)) ^ (-s) ≠ 0 :=
        one_sub_phase_prime_cpow_ne_zero (χ := fun q : Nat.Primes => (ψ q : ℂ))
          hunitψ (p := p) hs
      rw [hcdef]
      simp only [eulerRatio, hpe]
      exact div_self hdenψp
    have hmul := (hFprod s hs).mul hcorr
    refine hmul.congr_fun ?_
    intro p
    have hdenψ : (1 : ℂ) - (ψ p : ℂ) * ((p : ℂ)) ^ (-s) ≠ 0 :=
      one_sub_phase_prime_cpow_ne_zero (χ := fun q : Nat.Primes => (ψ q : ℂ)) hunitψ (p := p) hs
    rw [hcdef]
    simp only [eulerRatio]
    rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hdenψ, one_mul]

/-- **Every finite modification of the cube-root phase is noncontinuable.** -/
theorem notMem_continuableStratum_of_finiteModification {χ : PhaseTorus}
    (hχ : χ ∈ GaloisForLFunctions.finiteModification
      (fun _ : Nat.Primes => {z : ℂ // ‖z‖ = 1}) cubeRootPhase) :
    χ ∉ continuableStratum := by
  intro hmem
  refine notMem_continuableStratum_cubeRootPhase ?_
  refine mem_continuableStratum_of_finite_ne hmem ?_
  have hbase : {p : Nat.Primes | χ p ≠ cubeRootPhase p}.Finite := hχ
  refine hbase.subset ?_
  intro p hp hcon
  exact hp (by rw [hcon])

/-- **The noncontinuable phases are dense in the phase torus.** -/
theorem dense_compl_continuableStratum : Dense (continuableStratumᶜ) := by
  refine Dense.mono ?_ (GaloisForLFunctions.dense_finiteModification cubeRootPhase)
  intro χ hχ
  exact notMem_continuableStratum_of_finiteModification hχ

/-! ### The boundary-everywhere continuation seam -/

/-- **The continuation seam is boundary-everywhere.**  The phases whose Helson zeta continues
meromorphically to the whole plane and those whose Helson zeta does not are both dense, so the
frontier of the continuable stratum is the entire phase torus. -/
theorem frontier_continuableStratum_eq_univ :
    frontier continuableStratum = (Set.univ : Set PhaseTorus) :=
  GaloisForLFunctions.frontier_eq_univ_of_dense_and_dense_compl
    dense_continuableStratum dense_compl_continuableStratum

/-- **The continuation indicator is continuous at no phase.** -/
theorem nowhereContinuous_continuationIndicator :
    ∀ χ : PhaseTorus, ¬ ContinuousAt (GaloisForLFunctions.seamIndicator continuableStratum) χ :=
  GaloisForLFunctions.nowhereContinuous_seamIndicator dense_continuableStratum
    dense_compl_continuableStratum

/-- **No continuous readout decides meromorphic continuation.**  The Boolean continuation indicator
does not factor through any continuous map to a topological readout space followed by a continuous
map to the discrete two-point space. -/
theorem no_continuous_factorization_continuationIndicator {Y : Type*} [TopologicalSpace Y]
    (q : PhaseTorus → Y) (c : Y → Bool) (hq : Continuous q) (hc : Continuous c) :
    GaloisForLFunctions.seamIndicator continuableStratum ≠ c ∘ q := by
  letI : Nonempty PhaseTorus := ⟨trivialPhase⟩
  exact GaloisForLFunctions.no_continuous_factorization_seamIndicator dense_continuableStratum
    dense_compl_continuableStratum q c hq hc

end

end GaloisForLFunctions.HTGeometry
