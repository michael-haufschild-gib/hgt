import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicPrimeIsotropyRelativeXiChainMap
import GaloisForLFunctions.RHTower.Deninger.DeningerCapVanishing

/-!
# Bilateral prime-orbit Stokes regulator on the rational-adelic relative complex

The relative ordinary-prime cocycle was previously known to be nonzero by a fixed-vector
argument.  This file constructs an independent scalar detector on the actual adelic source.

For an archimedean Schwartz function `f` and ordinary prime `p`, the bilateral orbit functional is

`sum_{n >= 0} f(p^n) + sum_{n >= 0} (f(p^(-n-1)) - f(0))`.

The expanding tail is summable by Schwartz decay on the integer lattice.  The contracting tail is
summable by the mean-value estimate and a geometric majorant.  Reindexing both tails proves the
exact Stokes law

`R_p(alpha_p f - f) = f(0)`.

After finite-zero partial evaluation, `z - R_p(y)` annihilates the actual relative differential
`D0 x = (alpha_p x - x, epsilon_0 x)`.  It therefore descends to genuine first relative
cohomology and takes value one on the retained ordinary-prime class.

This is source Stokes flatness.  It does not identify the scalar Cartier/Xi comparison: the strict
Xi map still sends the class to a resolved boundary, so a non-flat graded Cartier comparison
remains the Route-R frontier.
-/

open Filter Topology
open scoped SchwartzMap
open GaloisForLFunctions
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

private abbrev Arch := CCMRationalArchimedeanSchwartz
private abbrev Core := CCMRationalAdelicBruhatSimpleTensor

private def primeOrbitPositiveTerm
    (p : Nat.Primes) (f : Arch) (n : ℕ) : ℂ :=
  f ((p.1 : ℝ) ^ n)

private def primeOrbitNegativeTerm
    (p : Nat.Primes) (f : Arch) (n : ℕ) : ℂ :=
  f (((p.1 : ℝ)⁻¹) ^ (n + 1)) - f 0

private theorem primeOrbitPositiveTerm_summable
    (p : Nat.Primes) (f : Arch) :
    Summable (primeOrbitPositiveTerm p f) := by
  have hZ := ccmRationalArchimedeanSchwartz_lattice_summable
    f (by norm_num : (1 : ℝ) ≠ 0)
  have hinj : Function.Injective (fun n : ℕ => (p.1 ^ n : ℤ)) := by
    intro m n h
    apply Nat.pow_right_injective p.2.two_le
    exact Int.ofNat.inj h
  have hcomp := hZ.comp_injective hinj
  have hnorm : Summable (fun n : ℕ => ‖primeOrbitPositiveTerm p f n‖) := by
    simpa [Function.comp_def, primeOrbitPositiveTerm] using hcomp
  exact summable_norm_iff.mp hnorm

private theorem archimedean_schwartz_lipschitz
    (f : Arch) (x : ℝ) :
    ‖f x - f 0‖ ≤
      SchwartzMap.seminorm ℂ 0 0 (derivSCLM f) * |x| := by
  have hdiff : ∀ y ∈ (Set.univ : Set ℝ),
      DifferentiableAt ℝ (f : ℝ → ℂ) y := by
    intro y _
    exact f.differentiable y
  have hbound : ∀ y ∈ (Set.univ : Set ℝ),
      ‖deriv (f : ℝ → ℂ) y‖ ≤
        SchwartzMap.seminorm ℂ 0 0 (derivSCLM f) := by
    intro y _
    have hval : deriv (f : ℝ → ℂ) y = derivSCLM f y := by
      symm
      rw [derivSCLM_apply]
    rw [hval]
    exact SchwartzMap.norm_le_seminorm ℂ (derivSCLM f) y
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.univ) (x := 0) (y := x) hdiff hbound convex_univ
      (Set.mem_univ 0) (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using h

private theorem primeOrbitNegativeTerm_summable
    (p : Nat.Primes) (f : Arch) :
    Summable (primeOrbitNegativeTerm p f) := by
  let r : ℝ := (p.1 : ℝ)⁻¹
  let M : ℝ := SchwartzMap.seminorm ℂ 0 0 (derivSCLM f)
  have hp1 : (1 : ℝ) < (p.1 : ℝ) := by
    exact_mod_cast p.2.one_lt
  have hr0 : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr1 : r < 1 := by
    dsimp [r]
    exact (inv_lt_one₀ (by linarith : 0 < (p.1 : ℝ))).2 hp1
  have hgeom : Summable (fun n : ℕ => M * r ^ (n + 1)) := by
    have h := (summable_geometric_of_lt_one hr0 hr1).mul_left M
    exact h.comp_injective Nat.succ_injective
  apply Summable.of_norm_bounded hgeom
  intro n
  calc
    ‖primeOrbitNegativeTerm p f n‖ ≤ M * |r ^ (n + 1)| := by
      exact archimedean_schwartz_lipschitz f (r ^ (n + 1))
    _ = M * r ^ (n + 1) := by
      rw [abs_of_nonneg (pow_nonneg hr0 _)]

private def primeOrbitPositiveSum
    (p : Nat.Primes) (f : Arch) : ℂ :=
  ∑' n : ℕ, primeOrbitPositiveTerm p f n

private def primeOrbitNegativeSum
    (p : Nat.Primes) (f : Arch) : ℂ :=
  ∑' n : ℕ, primeOrbitNegativeTerm p f n

/-- Bilateral prime-orbit Stokes functional on the archimedean Schwartz factor. -/
def ccmRationalArchimedeanPrimeOrbitStokes
    (p : Nat.Primes) (f : Arch) : ℂ :=
  primeOrbitPositiveSum p f + primeOrbitNegativeSum p f

/-- The bilateral orbit functional written out as its two explicit tails. -/
theorem ccmRationalArchimedeanPrimeOrbitStokes_eq
    (p : Nat.Primes) (f : Arch) :
    ccmRationalArchimedeanPrimeOrbitStokes p f =
      (∑' n : ℕ, f ((p.1 : ℝ) ^ n)) +
        ∑' n : ℕ, (f (((p.1 : ℝ)⁻¹) ^ (n + 1)) - f 0) := rfl

private theorem primeOrbitPositiveSum_add
    (p : Nat.Primes) (f g : Arch) :
    primeOrbitPositiveSum p (f + g) =
      primeOrbitPositiveSum p f + primeOrbitPositiveSum p g := by
  rw [primeOrbitPositiveSum, primeOrbitPositiveSum,
    primeOrbitPositiveSum]
  simpa [primeOrbitPositiveTerm] using
    (primeOrbitPositiveTerm_summable p f).tsum_add
      (primeOrbitPositiveTerm_summable p g)

private theorem primeOrbitNegativeSum_add
    (p : Nat.Primes) (f g : Arch) :
    primeOrbitNegativeSum p (f + g) =
      primeOrbitNegativeSum p f + primeOrbitNegativeSum p g := by
  rw [primeOrbitNegativeSum, primeOrbitNegativeSum,
    primeOrbitNegativeSum]
  have hterm : primeOrbitNegativeTerm p (f + g) =
      fun n => primeOrbitNegativeTerm p f n +
        primeOrbitNegativeTerm p g n := by
    funext n
    simp only [primeOrbitNegativeTerm, add_apply]
    abel
  rw [hterm, (primeOrbitNegativeTerm_summable p f).tsum_add
    (primeOrbitNegativeTerm_summable p g)]

/-- Linear form underlying the bilateral archimedean prime-orbit Stokes functional. -/
def ccmRationalArchimedeanPrimeOrbitStokesLM
    (p : Nat.Primes) : Arch →ₗ[ℂ] ℂ where
  toFun := ccmRationalArchimedeanPrimeOrbitStokes p
  map_add' f g := by
    rw [ccmRationalArchimedeanPrimeOrbitStokes,
      ccmRationalArchimedeanPrimeOrbitStokes,
      ccmRationalArchimedeanPrimeOrbitStokes,
      primeOrbitPositiveSum_add, primeOrbitNegativeSum_add]
    ring
  map_smul' c f := by
    rw [ccmRationalArchimedeanPrimeOrbitStokes,
      ccmRationalArchimedeanPrimeOrbitStokes,
      primeOrbitPositiveSum, primeOrbitPositiveSum,
      primeOrbitNegativeSum, primeOrbitNegativeSum]
    have hp := Summable.tsum_const_smul c
      (primeOrbitPositiveTerm_summable p f)
    have hn := Summable.tsum_const_smul c
      (primeOrbitNegativeTerm_summable p f)
    have hpos : primeOrbitPositiveTerm p (c • f) =
        fun n => c • primeOrbitPositiveTerm p f n := by
      funext n
      simp [primeOrbitPositiveTerm]
    have hneg : primeOrbitNegativeTerm p (c • f) =
        fun n => c • primeOrbitNegativeTerm p f n := by
      funext n
      simp only [primeOrbitNegativeTerm, smul_apply, smul_eq_mul]
      ring
    rw [hpos, hneg, hp, hn]
    simp [smul_eq_mul, mul_add]

@[simp]
private theorem archimedean_prime_scaling_apply
    (p : Nat.Primes) (f : Arch) (x : ℝ) :
    ccmRationalArchimedeanScaling
        (ccmRationalAdelicPrimeScaling p) f x =
      f ((p.1 : ℝ)⁻¹ * x) := by
  simp [ccmRationalArchimedeanScaling_apply,
    ccmRationalAdelicPrimeScaling]

private theorem primeOrbitPositiveSum_scaling
    (p : Nat.Primes) (f : Arch) :
    primeOrbitPositiveSum p
        (ccmRationalArchimedeanScaling
          (ccmRationalAdelicPrimeScaling p) f) =
      f (p.1 : ℝ)⁻¹ + primeOrbitPositiveSum p f := by
  have hs := (primeOrbitPositiveTerm_summable p
    (ccmRationalArchimedeanScaling
      (ccmRationalAdelicPrimeScaling p) f)).sum_add_tsum_nat_add 1
  rw [Finset.sum_range_one] at hs
  rw [primeOrbitPositiveSum, primeOrbitPositiveSum]
  calc
    (∑' n : ℕ, primeOrbitPositiveTerm p
        (ccmRationalArchimedeanScaling
          (ccmRationalAdelicPrimeScaling p) f) n) =
        primeOrbitPositiveTerm p
          (ccmRationalArchimedeanScaling
            (ccmRationalAdelicPrimeScaling p) f) 0 +
          ∑' n : ℕ, primeOrbitPositiveTerm p
            (ccmRationalArchimedeanScaling
              (ccmRationalAdelicPrimeScaling p) f) (n + 1) :=
      hs.symm
    _ = f (p.1 : ℝ)⁻¹ +
        ∑' n : ℕ, primeOrbitPositiveTerm p f n := by
      congr 1
      · rw [primeOrbitPositiveTerm, archimedean_prime_scaling_apply]
        simp
      · apply tsum_congr
        intro n
        simp only [primeOrbitPositiveTerm,
          archimedean_prime_scaling_apply]
        congr 1
        rw [pow_succ]
        have hp0 : (p.1 : ℝ) ≠ 0 := by
          exact_mod_cast p.2.ne_zero
        calc
          (p.1 : ℝ)⁻¹ * ((p.1 : ℝ) ^ n * (p.1 : ℝ)) =
              (p.1 : ℝ)⁻¹ * (p.1 : ℝ) * (p.1 : ℝ) ^ n := by
            ring
          _ = (p.1 : ℝ) ^ n := by
            rw [inv_mul_cancel₀ hp0, one_mul]
    _ = _ := rfl

private theorem primeOrbitNegativeSum_scaling
    (p : Nat.Primes) (f : Arch) :
    primeOrbitNegativeSum p
        (ccmRationalArchimedeanScaling
          (ccmRationalAdelicPrimeScaling p) f) =
      primeOrbitNegativeSum p f - (f (p.1 : ℝ)⁻¹ - f 0) := by
  have hs := (primeOrbitNegativeTerm_summable p f).sum_add_tsum_nat_add 1
  rw [Finset.sum_range_one] at hs
  rw [primeOrbitNegativeSum, primeOrbitNegativeSum]
  have hshift : (fun n : ℕ => primeOrbitNegativeTerm p
      (ccmRationalArchimedeanScaling
        (ccmRationalAdelicPrimeScaling p) f) n) =
      fun n : ℕ => primeOrbitNegativeTerm p f (n + 1) := by
    funext n
    simp only [primeOrbitNegativeTerm, archimedean_prime_scaling_apply]
    congr 2
    · rw [pow_succ']
      ring
    · simp
  rw [hshift]
  calc
    (∑' n : ℕ, primeOrbitNegativeTerm p f (n + 1)) =
        (∑' n : ℕ, primeOrbitNegativeTerm p f n) -
          primeOrbitNegativeTerm p f 0 := by
      linear_combination hs
    _ = (∑' n : ℕ, primeOrbitNegativeTerm p f n) -
        (f (p.1 : ℝ)⁻¹ - f 0) := by
      simp [primeOrbitNegativeTerm]

/-- Exact archimedean Stokes law for inverse ordinary-prime scaling. -/
theorem ccmRationalArchimedeanPrimeOrbitStokes_scaling_sub
    (p : Nat.Primes) (f : Arch) :
    ccmRationalArchimedeanPrimeOrbitStokesLM p
        (ccmRationalArchimedeanScaling
          (ccmRationalAdelicPrimeScaling p) f - f) =
      f 0 := by
  rw [map_sub, ccmRationalArchimedeanPrimeOrbitStokesLM]
  change ccmRationalArchimedeanPrimeOrbitStokes p
      (ccmRationalArchimedeanScaling
        (ccmRationalAdelicPrimeScaling p) f) -
      ccmRationalArchimedeanPrimeOrbitStokes p f = f 0
  rw [ccmRationalArchimedeanPrimeOrbitStokes,
    ccmRationalArchimedeanPrimeOrbitStokes,
    primeOrbitPositiveSum_scaling, primeOrbitNegativeSum_scaling]
  ring

/-- Bilateral prime-orbit Stokes functional on the actual adelic tensor core. -/
def ccmRationalAdelicPrimeOrbitStokesLM
    (p : Nat.Primes) : Core →ₗ[ℂ] ℂ :=
  (ccmRationalArchimedeanPrimeOrbitStokesLM p).comp
    ccmRationalAdelicFiniteZeroPartialEval

/-- The adelic orbit Stokes coboundary is exactly full zero-adele evaluation. -/
theorem ccmRationalAdelicPrimeOrbitStokes_scaling_sub
    (p : Nat.Primes) (x : Core) :
    ccmRationalAdelicPrimeOrbitStokesLM p
        (ccmRationalAdelicPrimeScaling p • x - x) =
      ccmRationalAdelicBruhatZeroEval x := by
  change ccmRationalArchimedeanPrimeOrbitStokesLM p
      (ccmRationalAdelicFiniteZeroPartialEval
        (ccmRationalAdelicPrimeScaling p • x - x)) = _
  rw [map_sub, ccmRationalAdelicFiniteZeroPartialEval_scaling,
    ccmRationalArchimedeanPrimeOrbitStokes_scaling_sub,
    ccmRationalAdelicFiniteZeroPartialEval_zero]

/-- Independent Stokes reader on the relative degree-one source. -/
def ccmRationalAdelicPrimeRelativeStokesRegulatorLM
    (p : Nat.Primes) :
    CCMRationalAdelicPrimeRelativeOne →ₗ[ℂ] ℂ where
  toFun yz := yz.2 - ccmRationalAdelicPrimeOrbitStokesLM p yz.1
  map_add' x y := by
    simp
    ring
  map_smul' c x := by
    simp [smul_eq_mul]
    ring

/-- Source Stokes flatness: the regulator annihilates every relative boundary. -/
theorem ccmRationalAdelicPrimeRelativeStokesRegulator_comp_D0
    (p : Nat.Primes) :
    (ccmRationalAdelicPrimeRelativeStokesRegulatorLM p).comp
      (ccmRationalAdelicPrimeRelativeD0 p) = 0 := by
  apply LinearMap.ext
  intro x
  change ccmRationalAdelicBruhatZeroEval x -
      ccmRationalAdelicPrimeOrbitStokesLM p
        (ccmRationalAdelicPrimeScaling p • x - x) = 0
  rw [ccmRationalAdelicPrimeOrbitStokes_scaling_sub]
  exact sub_self _

/-- The retained ordinary-prime cocycle has Stokes period one. -/
theorem ccmRationalAdelicPrimeRelativeStokesRegulator_cocycle
    (p : Nat.Primes) :
    ccmRationalAdelicPrimeRelativeStokesRegulatorLM p
      (ccmRationalAdelicPrimeRelativeCocycle p) = 1 := by
  change (1 : ℂ) - ccmRationalAdelicPrimeOrbitStokesLM p 0 = 1
  rw [map_zero, sub_zero]

/-- Restriction of the Stokes reader to genuine relative one-cocycles. -/
def ccmRationalAdelicPrimeRelativeStokesCyclesLM
    (p : Nat.Primes) :
    (ccmRationalAdelicPrimeRelativeComplex p).cycles1 →ₗ[ℂ] ℂ :=
  (ccmRationalAdelicPrimeRelativeStokesRegulatorLM p).comp
    (ccmRationalAdelicPrimeRelativeComplex p).cycles1.subtype

/-- Relative boundaries lie in the kernel of the source Stokes reader. -/
theorem ccmRationalAdelicPrimeRelativeStokes_boundaries_le_ker
    (p : Nat.Primes) :
    (ccmRationalAdelicPrimeRelativeComplex p).boundaries1.comap
        (ccmRationalAdelicPrimeRelativeComplex p).cycles1.subtype ≤
      LinearMap.ker
        (ccmRationalAdelicPrimeRelativeStokesCyclesLM p) := by
  intro y hy
  change (y : CCMRationalAdelicPrimeRelativeOne) ∈
      LinearMap.range (ccmRationalAdelicPrimeRelativeD0 p) at hy
  rcases hy with ⟨x, hx⟩
  change ccmRationalAdelicPrimeRelativeStokesRegulatorLM p
      (y : CCMRationalAdelicPrimeRelativeOne) = 0
  rw [← hx]
  exact LinearMap.congr_fun
    (ccmRationalAdelicPrimeRelativeStokesRegulator_comp_D0 p) x

/-- Stokes period on genuine first relative cohomology. -/
def ccmRationalAdelicPrimeRelativeH1StokesRegulator
    (p : Nat.Primes) :
    (ccmRationalAdelicPrimeRelativeComplex p).H1 →ₗ[ℂ] ℂ :=
  ((ccmRationalAdelicPrimeRelativeComplex p).boundaries1.comap
      (ccmRationalAdelicPrimeRelativeComplex p).cycles1.subtype).liftQ
    (ccmRationalAdelicPrimeRelativeStokesCyclesLM p)
    (ccmRationalAdelicPrimeRelativeStokes_boundaries_le_ker p)

/-- The induced Stokes period detects the retained ordinary-prime homology class. -/
theorem ccmRationalAdelicPrimeRelativeH1StokesRegulator_class
    (p : Nat.Primes) :
    ccmRationalAdelicPrimeRelativeH1StokesRegulator p
      (ccmRationalAdelicPrimeRelativeClass p) = 1 := by
  exact (LinearMap.congr_fun
    (Submodule.liftQ_mkQ
      ((ccmRationalAdelicPrimeRelativeComplex p).boundaries1.comap
        (ccmRationalAdelicPrimeRelativeComplex p).cycles1.subtype)
      (ccmRationalAdelicPrimeRelativeStokesCyclesLM p)
      (ccmRationalAdelicPrimeRelativeStokes_boundaries_le_ker p))
    (ccmRationalAdelicPrimeRelativeCocycle p)).trans
      (ccmRationalAdelicPrimeRelativeStokesRegulator_cocycle p)

end

end RHTower
