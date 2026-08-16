import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesWallAtomicFredholmLimit

/-!
# P-G105Y: physical-child Fredholm transport and locally uniform wall limit

P-G105X constructs normalized atomic wall coefficients but leaves their identification with the
literal cofinal Stokes child open.  Here each ordered prime tuple is evaluated with the actual
P-G105K child kernel.  Exact diagonal congruence gives

```text
det K_d[p_i,p_j]
  = (product_i w_d(p_i)) det C[log p_i,log p_j].
```

Writing `S_d = sum_p w_d(p)` and normalizing by the source PMF therefore gives, at every Fredholm
order `n`,

```text
physicalChildCoefficient(d,n) = S_d^n * wallCoefficient(d,n).
```

No prime tuple, repeated label, determinant order, or cross-prime incidence is removed.  The
identity supplies an aperture-sensitive Hadamard majorant for the complete physical child series.
Since `S_d -> 4` from the positive side and P-G105X's normalized determinant converges uniformly
on closed discs, the literal ordered-prime child Fredholm series converges uniformly on every
closed disc to the exponential-wall determinant at the forced rescaling `z ↦ 4z`.

This closes coefficient transport and order-uniform wall convergence for the child Fredholm
expansion.  Identification of the resulting exponential-wall divisor with Xi remains separate;
no Xi coefficient or zero data is fitted here.
-/

open Complex Filter Topology Set MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal

namespace RHTower

noncomputable section

/-- Positive physical apertures. Positivity is source data, never a theorem premise. -/
structure RoutePPrimitiveGammaJuliaStokesPositiveAperture where
  value : ℝ
  positive : 0 < value

instance : Coe RoutePPrimitiveGammaJuliaStokesPositiveAperture ℝ :=
  ⟨RoutePPrimitiveGammaJuliaStokesPositiveAperture.value⟩

@[simp] theorem coe_routePPrimitiveGammaJuliaStokesPositiveAperture
    (d : RoutePPrimitiveGammaJuliaStokesPositiveAperture) :
    (d : ℝ) = d.value := rfl

def routePPrimitiveGammaJuliaStokesPhysicalChildFredholmMatrix
    (d : ℝ) (n : ℕ) (a : Fin n → Nat.Primes) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => routePPrimitiveGammaJuliaStokesCofinalChildKernel d (a i, a j)

def routePPrimitiveGammaJuliaStokesPhysicalChildWeightDiagonal
    (d : ℝ) (n : ℕ) (a : Fin n → Nat.Primes) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun i =>
    (Real.sqrt (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d (a i)) : ℂ)

theorem routePPrimitiveGammaJuliaStokesPhysicalChildFredholmMatrix_factorization
    (d : RoutePPrimitiveGammaJuliaStokesPositiveAperture)
    (n : ℕ) (a : Fin n → Nat.Primes) :
    routePPrimitiveGammaJuliaStokesPhysicalChildFredholmMatrix (d : ℝ) n a =
      routePPrimitiveGammaJuliaStokesPhysicalChildWeightDiagonal (d : ℝ) n a *
        routePPrimitiveGammaJuliaStokesWallPrimeFredholmMatrix n a *
      routePPrimitiveGammaJuliaStokesPhysicalChildWeightDiagonal (d : ℝ) n a := by
  ext i j
  simp only [routePPrimitiveGammaJuliaStokesPhysicalChildFredholmMatrix,
    routePPrimitiveGammaJuliaStokesPhysicalChildWeightDiagonal,
    Matrix.diagonal_mul, Matrix.mul_diagonal,
    routePPrimitiveGammaJuliaStokesWallPrimeFredholmMatrix,
    routePPrimitiveGammaJuliaStokesCofinalChildKernel_eq_wallCubicKernel d.positive]
  push_cast
  ring

theorem det_routePPrimitiveGammaJuliaStokesPhysicalChildFredholmMatrix
    (d : RoutePPrimitiveGammaJuliaStokesPositiveAperture)
    (n : ℕ) (a : Fin n → Nat.Primes) :
    (routePPrimitiveGammaJuliaStokesPhysicalChildFredholmMatrix (d : ℝ) n a).det =
      (∏ i : Fin n,
        (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight (d : ℝ) (a i) : ℂ)) *
      routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand n a := by
  rw [routePPrimitiveGammaJuliaStokesPhysicalChildFredholmMatrix_factorization d,
    Matrix.det_mul, Matrix.det_mul]
  unfold routePPrimitiveGammaJuliaStokesPhysicalChildWeightDiagonal
  rw [Matrix.det_diagonal]
  unfold routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand
  let s : Fin n → ℂ := fun i =>
    (Real.sqrt (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight (d : ℝ) (a i)) : ℂ)
  have hs (i : Fin n) : s i * s i =
      (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight (d : ℝ) (a i) : ℂ) := by
    dsimp [s]
    rw [← Complex.ofReal_mul,
      Real.mul_self_sqrt
        (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_nonneg d.positive (a i))]
  calc
    (∏ i : Fin n, s i) *
          (routePPrimitiveGammaJuliaStokesWallPrimeFredholmMatrix n a).det *
        ∏ i : Fin n, s i =
        ((∏ i : Fin n, s i) * ∏ i : Fin n, s i) *
          (routePPrimitiveGammaJuliaStokesWallPrimeFredholmMatrix n a).det := by ring
    _ = (∏ i : Fin n, s i * s i) *
          (routePPrimitiveGammaJuliaStokesWallPrimeFredholmMatrix n a).det := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ i : Fin n,
          (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight (d : ℝ) (a i) : ℂ)) *
          (routePPrimitiveGammaJuliaStokesWallPrimeFredholmMatrix n a).det := by
      rw [show (∏ i : Fin n, s i * s i) =
          ∏ i : Fin n,
            (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight (d : ℝ) (a i) : ℂ) by
        exact Finset.prod_congr rfl fun i _hi => hs i]

theorem prod_transportWeight_eq_current_pow_mul_normalized
    (d : RoutePPrimitiveGammaJuliaStokesPositiveAperture)
    (n : ℕ) (a : Fin n → Nat.Primes) :
    (∏ i : Fin n,
      (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight (d : ℝ) (a i) : ℂ)) =
      (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent (d : ℝ) : ℂ) ^ n *
        ∏ i : Fin n,
          (routePPrimitiveGammaJuliaStokesWallNormalizedWeight (d : ℝ) (a i) : ℂ) := by
  have hS : gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent (d : ℝ) ≠ 0 :=
    (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos d.positive).ne'
  calc
    (∏ i : Fin n,
        (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight (d : ℝ) (a i) : ℂ)) =
        ∏ i : Fin n,
          ((gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent (d : ℝ) : ℂ) *
            (routePPrimitiveGammaJuliaStokesWallNormalizedWeight (d : ℝ) (a i) : ℂ)) := by
      apply Finset.prod_congr rfl
      intro i _hi
      rw [routePPrimitiveGammaJuliaStokesWallNormalizedWeight]
      push_cast
      field_simp [hS]
    _ = (∏ _i : Fin n,
          (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent (d : ℝ) : ℂ)) *
        ∏ i : Fin n,
          (routePPrimitiveGammaJuliaStokesWallNormalizedWeight (d : ℝ) (a i) : ℂ) := by
      rw [Finset.prod_mul_distrib]
    _ = _ := by simp

def routePPrimitiveGammaJuliaStokesPhysicalChildFredholmCoefficient
    (d : ℝ) (n : ℕ) : ℂ :=
  (∑' a : Fin n → Nat.Primes,
    (routePPrimitiveGammaJuliaStokesPhysicalChildFredholmMatrix d n a).det) /
      (n.factorial : ℂ)

theorem routePPrimitiveGammaJuliaStokesPhysicalChildFredholmCoefficient_eq
    (d : RoutePPrimitiveGammaJuliaStokesPositiveAperture) (n : ℕ) :
    routePPrimitiveGammaJuliaStokesPhysicalChildFredholmCoefficient (d : ℝ) n =
      (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent (d : ℝ) : ℂ) ^ n *
        routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw (d : ℝ)) n := by
  rw [routePPrimitiveGammaJuliaStokesPhysicalChildFredholmCoefficient]
  rw [show (∑' a : Fin n → Nat.Primes,
      (routePPrimitiveGammaJuliaStokesPhysicalChildFredholmMatrix d n a).det) =
      ∑' a : Fin n → Nat.Primes,
        (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent (d : ℝ) : ℂ) ^ n *
          ((∏ i : Fin n,
            (routePPrimitiveGammaJuliaStokesWallNormalizedWeight (d : ℝ) (a i) : ℂ)) *
            routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand n a) by
    apply tsum_congr
    intro a
    rw [det_routePPrimitiveGammaJuliaStokesPhysicalChildFredholmMatrix d,
      prod_transportWeight_eq_current_pow_mul_normalized d]
    ring]
  rw [tsum_mul_left]
  have hwall :=
    routePPrimitiveGammaJuliaStokesWallFredholmCoefficient_eq_orderedPrimeTuple_tsum d.positive n
  push_cast at hwall
  rw [hwall]
  ring

theorem tendsto_routePPrimitiveGammaJuliaStokesPhysicalChildFredholmCoefficient_nhdsGT_zero
    (n : ℕ) :
    Tendsto
      (fun d : ℝ =>
        routePPrimitiveGammaJuliaStokesPhysicalChildFredholmCoefficient d n)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((4 : ℂ) ^ n *
        routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
          (expMeasure 1) n)) := by
  have hcurrent : Tendsto
      (fun d : ℝ =>
        (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (4 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsGT_zero
  have hmain := (hcurrent.pow n).mul
    (tendsto_routePPrimitiveGammaJuliaStokesWallFredholmCoefficient_nhdsGT_zero n)
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with d hd
  exact (routePPrimitiveGammaJuliaStokesPhysicalChildFredholmCoefficient_eq
    ⟨d, hd⟩ n).symm

theorem norm_routePPrimitiveGammaJuliaStokesPhysicalChildFredholmCoefficient_le
    (d : RoutePPrimitiveGammaJuliaStokesPositiveAperture) (n : ℕ) :
    ‖routePPrimitiveGammaJuliaStokesPhysicalChildFredholmCoefficient (d : ℝ) n‖ ≤
      gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent (d : ℝ) ^ n *
        ((Real.sqrt n) ^ n / (n.factorial : ℝ)) := by
  rw [routePPrimitiveGammaJuliaStokesPhysicalChildFredholmCoefficient_eq d,
    norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg
      (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos d.positive).le]
  exact mul_le_mul_of_nonneg_left
    (norm_routePPrimitiveGammaJuliaStokesWallFredholmCoefficient_le
      (routePPrimitiveGammaJuliaStokesWallHalfLineLaw (d : ℝ))
      (wallHalfLineLaw_Iio_zero (d : ℝ)) n)
    (pow_nonneg
      (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos d.positive).le n)

def routePPrimitiveGammaJuliaStokesPhysicalChildFredholmEntireDet
    (d : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ n *
    routePPrimitiveGammaJuliaStokesPhysicalChildFredholmCoefficient d n

theorem summable_routePPrimitiveGammaJuliaStokesPhysicalChildFredholmEntireDet
    (d : RoutePPrimitiveGammaJuliaStokesPositiveAperture) (z : ℂ) :
    Summable (fun n : ℕ => z ^ n *
      routePPrimitiveGammaJuliaStokesPhysicalChildFredholmCoefficient (d : ℝ) n) := by
  refine (summable_routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
    (routePPrimitiveGammaJuliaStokesWallHalfLineLaw (d : ℝ))
    (wallHalfLineLaw_Iio_zero (d : ℝ))
    ((gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent (d : ℝ) : ℂ) * z)).congr ?_
  intro n
  rw [routePPrimitiveGammaJuliaStokesPhysicalChildFredholmCoefficient_eq d]
  ring

theorem routePPrimitiveGammaJuliaStokesPhysicalChildFredholmEntireDet_eq_scaledWall
    (d : RoutePPrimitiveGammaJuliaStokesPositiveAperture) (z : ℂ) :
    routePPrimitiveGammaJuliaStokesPhysicalChildFredholmEntireDet (d : ℝ) z =
      routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw (d : ℝ))
        ((gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent (d : ℝ) : ℂ) * z) := by
  unfold routePPrimitiveGammaJuliaStokesPhysicalChildFredholmEntireDet
    routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
  apply tsum_congr
  intro n
  rw [routePPrimitiveGammaJuliaStokesPhysicalChildFredholmCoefficient_eq d]
  ring

theorem tendsto_routePPrimitiveGammaJuliaStokesPhysicalChildFredholmEntireDet_nhdsGT_zero
    (z : ℂ) :
    Tendsto
      (fun d : ℝ =>
        routePPrimitiveGammaJuliaStokesPhysicalChildFredholmEntireDet d z)
      (𝓝[>] (0 : ℝ))
      (𝓝 (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
        (expMeasure 1) ((4 : ℂ) * z))) := by
  unfold routePPrimitiveGammaJuliaStokesPhysicalChildFredholmEntireDet
    routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
  apply tendsto_tsum_of_dominated_convergence
    (ContinuousKernelFredholm.summable_hadamard_majorant
      (5 * ‖z‖) (mul_nonneg (by norm_num) (norm_nonneg z)))
  · intro n
    have hconst : Tendsto (fun _d : ℝ => z ^ n)
        (𝓝[>] (0 : ℝ)) (𝓝 (z ^ n)) := tendsto_const_nhds
    have h := hconst.mul
      (tendsto_routePPrimitiveGammaJuliaStokesPhysicalChildFredholmCoefficient_nhdsGT_zero n)
    convert h using 1
    ring_nf
  · have hcurrent :=
      tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsGT_zero
    have hlt : ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ),
        gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d < 5 :=
      hcurrent.eventually (Iio_mem_nhds (by norm_num : (4 : ℝ) < 5))
    filter_upwards [self_mem_nhdsWithin, hlt] with d hd hS
    intro n
    rw [norm_mul, norm_pow]
    have hcoef :=
      norm_routePPrimitiveGammaJuliaStokesPhysicalChildFredholmCoefficient_le ⟨d, hd⟩ n
    have hpow :
        gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d ^ n ≤ (5 : ℝ) ^ n :=
      pow_le_pow_left₀
        (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd).le hS.le n
    calc
      ‖z‖ ^ n *
          ‖routePPrimitiveGammaJuliaStokesPhysicalChildFredholmCoefficient d n‖ ≤
          ‖z‖ ^ n *
            (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d ^ n *
              ((Real.sqrt n) ^ n / (n.factorial : ℝ))) :=
        mul_le_mul_of_nonneg_left hcoef (pow_nonneg (norm_nonneg z) n)
      _ ≤ ‖z‖ ^ n *
            ((5 : ℝ) ^ n * ((Real.sqrt n) ^ n / (n.factorial : ℝ))) := by
        gcongr
      _ = (Real.sqrt n * (5 * ‖z‖)) ^ n / (n.factorial : ℝ) := by ring

theorem tendstoUniformlyOn_routePPrimitiveGammaJuliaStokesPhysicalChildFredholmEntireDet_nhdsGT_zero
    (rho : ℝ≥0) :
    TendstoUniformlyOn
      (fun d z =>
        routePPrimitiveGammaJuliaStokesPhysicalChildFredholmEntireDet d z)
      (fun z => routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
        (expMeasure 1) ((4 : ℂ) * z))
      (𝓝[>] (0 : ℝ)) (Metric.closedBall 0 (rho : ℝ)) := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure one_pos
  let rhoR : ℝ := rho
  let R : ℝ := 5 * rhoR
  have hR : 0 ≤ R := mul_nonneg (by norm_num) rho.property
  let u : ℕ → ℝ := routePPrimitiveGammaJuliaStokesWallFredholmMajorant R
  have hu : Summable u :=
    summable_routePPrimitiveGammaJuliaStokesWallFredholmMajorant hR
  let F0 : ℂ → ℂ := fun z =>
    routePPrimitiveGammaJuliaStokesWallFredholmEntireDet (expMeasure 1) z
  have htarget : TendstoUniformlyOn
      (fun N : ℕ => fun z : ℂ =>
        ∑ n ∈ Finset.range N,
          z ^ n * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
            (expMeasure 1) n)
      F0 atTop (Metric.closedBall 0 R) := by
    change TendstoUniformlyOn
      (fun N : ℕ => fun z : ℂ =>
        ∑ n ∈ Finset.range N,
          z ^ n * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
            (expMeasure 1) n)
      (fun z : ℂ => ∑' n : ℕ,
        z ^ n * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
          (expMeasure 1) n)
      atTop (Metric.closedBall 0 R)
    exact
      (tendstoUniformlyOn_tsum_nat hu
        (s := Metric.closedBall (0 : ℂ) R)
        (f := fun (n : ℕ) (z : ℂ) =>
          z ^ n * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
            (expMeasure 1) n)
        (fun n z hz => norm_routePPrimitiveGammaJuliaStokesWallFredholmTerm_le_majorant
          (expMeasure 1) GaloisForLFunctions.HTGeometry.expMeasure_one_Iio_zero
          hR hz n))
  have htargetContinuous : ContinuousOn F0 (Metric.closedBall 0 R) := by
    apply htarget.continuousOn
    exact (Filter.Eventually.of_forall fun N => by fun_prop).frequently
  have htargetUniform : UniformContinuousOn F0 (Metric.closedBall 0 R) :=
    (isCompact_closedBall (0 : ℂ) R).uniformContinuousOn_of_continuous
      htargetContinuous
  have hfamily :=
    tendstoUniformlyOn_routePPrimitiveGammaJuliaStokesWallFredholmEntireDet_nhdsGT_zero hR
  rw [Metric.tendstoUniformlyOn_iff] at hfamily ⊢
  intro eps heps
  have heps2 : 0 < eps / 2 := by positivity
  obtain ⟨delta, hdelta, hUC⟩ :=
    Metric.uniformContinuousOn_iff.mp htargetUniform (eps / 2) heps2
  have hfamilyEvent := hfamily (eps / 2) heps2
  have hcurrent :=
    tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsGT_zero
  have hlt : ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ),
      gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d < 5 :=
    hcurrent.eventually (Iio_mem_nhds (by norm_num : (4 : ℝ) < 5))
  have hmoveTendsto : Tendsto
      (fun d : ℝ =>
        |gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d - 4| * rho)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hsub := hcurrent.sub
      (tendsto_const_nhds : Tendsto (fun _d : ℝ => (4 : ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝 4))
    have habs := hsub.abs
    simpa [rhoR] using habs.mul_const rhoR
  have hmove : ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ),
      |gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d - 4| * rhoR < delta :=
    hmoveTendsto.eventually (Iio_mem_nhds hdelta)
  filter_upwards [hfamilyEvent, self_mem_nhdsWithin, hlt, hmove] with
      d hFd hd hS hdist
  intro z hz
  have hznorm : ‖z‖ ≤ rho := by
    simpa [rhoR, Metric.mem_closedBall, dist_zero_right] using hz
  let S : ℝ := gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d
  have hSpos : 0 < S :=
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd
  have hsourceMem : (S : ℂ) * z ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hSpos]
    dsimp [R]
    exact (mul_le_mul_of_nonneg_left hznorm hSpos.le).trans
      (mul_le_mul_of_nonneg_right hS.le rho.property)
  have htargetMem : (4 : ℂ) * z ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul]
    norm_num [R]
    nlinarith
  have hinputDist : dist ((S : ℂ) * z) ((4 : ℂ) * z) < delta := by
    rw [dist_eq_norm, ← sub_mul, norm_mul]
    rw [show (S : ℂ) - 4 = ((S - 4 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hznorm (abs_nonneg (S - 4))).trans_lt hdist
  have hfirst : dist
      (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) ((S : ℂ) * z))
      (F0 ((S : ℂ) * z)) < eps / 2 := by
    simpa [F0, dist_comm] using hFd ((S : ℂ) * z) hsourceMem
  have hsecond := hUC ((S : ℂ) * z) hsourceMem ((4 : ℂ) * z) htargetMem hinputDist
  rw [routePPrimitiveGammaJuliaStokesPhysicalChildFredholmEntireDet_eq_scaledWall ⟨d, hd⟩]
  rw [dist_comm]
  change dist
      (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) ((S : ℂ) * z))
      (F0 ((4 : ℂ) * z)) < eps
  calc
    dist
        (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) ((S : ℂ) * z))
        (F0 ((4 : ℂ) * z)) ≤
      dist
          (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
            (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) ((S : ℂ) * z))
          (F0 ((S : ℂ) * z)) +
        dist (F0 ((S : ℂ) * z)) (F0 ((4 : ℂ) * z)) := dist_triangle _ _ _
    _ < eps / 2 + eps / 2 := add_lt_add hfirst hsecond
    _ = eps := by ring

end
end RHTower
