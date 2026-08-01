import GaloisForLFunctions.HTGeometry.PrimeDirichletApertureSpectrum
import GaloisForLFunctions.HTGeometry.EulerFactorRankOne

/-!
# The cutoff Euler product carries the whole aperture

The finite Euler product

`Z_{N,σ}(t) = ∏_{p ≤ N} (1 − p^{-σ-it})⁻¹`

is a uniform limit on the vertical line of the expanded products of the factors' geometric partial
sums.  Each expanded product is a trigonometric polynomial indexed by exponent vectors, with
frequency `−∑ e_p log p` and *positive* coefficient `∏ p^{-σ e_p}`; positivity means no exponent
vector can cancel another.  The single vector `e = δ_p` therefore keeps the coefficient at `−log p`
bounded below by `p^{-σ}`, and every frequency lies in the aperture module.

Hence the Bohr frequency module of the cutoff Euler product is exactly the aperture-`N` character
module, of rational rank `π(N)`: the finite aperture really does transport `π(N)` independent phase
dimensions.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

noncomputable section

open scoped BigOperators

variable {N : ℕ} {σ : ℝ}

/-- A uniform bound on the factors bounds the difference of two products. -/
theorem norm_prod_sub_prod_le {ι : Type*} (a b : ι → ℂ) {C δ : ℝ} (hC : 1 ≤ C) (hδ : 0 ≤ δ) :
    ∀ s : Finset ι, (∀ i ∈ s, ‖a i‖ ≤ C) → (∀ i ∈ s, ‖b i‖ ≤ C) →
      (∀ i ∈ s, ‖a i - b i‖ ≤ δ) →
      ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ s.card * C ^ s.card * δ := by
  classical
  intro s
  induction s using Finset.induction with
  | empty => intro _ _ _; simp
  | insert x s hx ih =>
    intro ha hb hd
    have hCpos : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
    have ha' : ∀ i ∈ s, ‖a i‖ ≤ C := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hb' : ∀ i ∈ s, ‖b i‖ ≤ C := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hd' : ∀ i ∈ s, ‖a i - b i‖ ≤ δ := fun i hi => hd i (Finset.mem_insert_of_mem hi)
    have hrec := ih ha' hb' hd'
    have hprodb : ‖∏ i ∈ s, b i‖ ≤ C ^ s.card := by
      rw [norm_prod]
      calc ∏ i ∈ s, ‖b i‖ ≤ ∏ _i ∈ s, C :=
            Finset.prod_le_prod (fun i _ => norm_nonneg _) hb'
        _ = C ^ s.card := by rw [Finset.prod_const]
    have hsplit : (∏ i ∈ insert x s, a i) - ∏ i ∈ insert x s, b i
        = a x * ((∏ i ∈ s, a i) - ∏ i ∈ s, b i) + (a x - b x) * ∏ i ∈ s, b i := by
      rw [Finset.prod_insert hx, Finset.prod_insert hx]
      ring
    have hax : ‖a x‖ ≤ C := ha x (Finset.mem_insert_self x s)
    have hdx : ‖a x - b x‖ ≤ δ := hd x (Finset.mem_insert_self x s)
    have hstep : ‖(∏ i ∈ insert x s, a i) - ∏ i ∈ insert x s, b i‖
        ≤ C * (s.card * C ^ s.card * δ) + δ * C ^ s.card := by
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, norm_mul]
      have h1 : ‖a x‖ * ‖(∏ i ∈ s, a i) - ∏ i ∈ s, b i‖ ≤ C * (s.card * C ^ s.card * δ) :=
        mul_le_mul hax hrec (norm_nonneg _) hCpos.le
      have h2 : ‖a x - b x‖ * ‖∏ i ∈ s, b i‖ ≤ δ * C ^ s.card :=
        mul_le_mul hdx hprodb (norm_nonneg _) hδ
      linarith
    refine le_trans hstep ?_
    have hCk : (0 : ℝ) < C ^ s.card := pow_pos hCpos _
    have hcard : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
    rw [Finset.card_insert_of_notMem hx, pow_succ]
    push_cast
    nlinarith [mul_nonneg (mul_nonneg hCk.le hδ) (sub_nonneg.mpr hC), mul_nonneg hcard hδ,
      hCk.le, hδ]

/-- Every prime is a base greater than one. -/
theorem one_lt_prime_cast (p : Nat.Primes) : (1 : ℝ) < ((p : ℕ) : ℝ) := by
  have := p.2.two_le
  have : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast this
  linarith

/-- The cutoff Euler product on the vertical line. -/
noncomputable def eulerProductLine (N : ℕ) (σ t : ℝ) : ℂ :=
  ∏ p ∈ primesLE N, eulerFactorLine ((p : ℕ) : ℝ) σ t

/-- The exponent-vector coefficient of the expanded partial product. -/
noncomputable def smoothCoeff (N : ℕ) (σ : ℝ)
    (x : ↥(primesLE N) → ℕ) : ℝ :=
  ∏ i : ↥(primesLE N), (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ * x i)

/-- The exponent-vector frequency of the expanded partial product. -/
noncomputable def smoothFreq (N : ℕ) (x : ↥(primesLE N) → ℕ) : ℝ :=
  ∑ i : ↥(primesLE N), baseFrequency ((((i : Nat.Primes) : ℕ) : ℝ)) (x i)

theorem smoothCoeff_pos (N : ℕ) (σ : ℝ) (x : ↥(primesLE N) → ℕ) :
    0 < smoothCoeff N σ x := by
  refine Finset.prod_pos fun i _ => ?_
  exact Real.rpow_pos_of_pos (lt_trans zero_lt_one (one_lt_prime_cast _)) _

/-- Each exponent-vector frequency lies in the aperture module. -/
theorem smoothFreq_mem_aperture (N : ℕ) (x : ↥(primesLE N) → ℕ) :
    smoothFreq N x ∈ primeApertureCharacterModule N := by
  rw [smoothFreq]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hbase : Real.log ((i : Nat.Primes) : ℕ) ∈ primeApertureCharacterModule N := by
    unfold primeApertureCharacterModule primeLogSpan
    exact Submodule.subset_span ⟨i, rfl⟩
  have hsmul := Submodule.smul_mem (primeApertureCharacterModule N) (-(x i : ℚ)) hbase
  have heq : (-(x i : ℚ)) • Real.log ((i : Nat.Primes) : ℕ)
      = baseFrequency ((((i : Nat.Primes) : ℕ) : ℝ)) (x i) := by
    rw [baseFrequency, Rat.smul_def]
    push_cast
    ring
  rwa [heq] at hsmul

/-- The expanded partial product: a trigonometric polynomial indexed by exponent vectors. -/
theorem eulerProductApprox_eq (N : ℕ) (σ : ℝ) (M : ℕ) (t : ℝ) :
    (∏ p ∈ primesLE N, ∑ e ∈ Finset.range M,
        ((((p : ℕ) : ℝ) ^ (-σ * e) : ℝ) : ℂ) * expChar (baseFrequency (((p : ℕ) : ℝ)) e) t)
      = ∑ x ∈ Fintype.piFinset (fun _ : ↥(primesLE N) => Finset.range M),
          ((smoothCoeff N σ x : ℝ) : ℂ) * expChar (smoothFreq N x) t := by
  classical
  rw [← Finset.prod_coe_sort (primesLE N) (fun p => ∑ e ∈ Finset.range M,
    ((((p : ℕ) : ℝ) ^ (-σ * e) : ℝ) : ℂ) * expChar (baseFrequency (((p : ℕ) : ℝ)) e) t)]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.prod_mul_distrib, prod_expChar, smoothCoeff, smoothFreq, Complex.ofReal_prod]

/-- The uniform factor bound on the aperture. -/
noncomputable def apertureBound (σ : ℝ) : ℝ := 2 * (1 - (2 : ℝ) ^ (-σ))⁻¹

/-- The uniform per-factor truncation error at depth `M`. -/
noncomputable def apertureError (σ : ℝ) (M : ℕ) : ℝ :=
  ((2 : ℝ) ^ (-σ)) ^ M * (1 - (2 : ℝ) ^ (-σ))⁻¹

theorem two_rpow_lt_one (hσ : 0 < σ) : (2 : ℝ) ^ (-σ) < 1 :=
  base_rpow_neg_lt_one one_lt_two hσ

theorem one_sub_two_rpow_pos (hσ : 0 < σ) : (0 : ℝ) < 1 - (2 : ℝ) ^ (-σ) := by
  have := two_rpow_lt_one hσ
  linarith

theorem one_le_apertureBound (hσ : 0 < σ) : 1 ≤ apertureBound σ := by
  have hpos := one_sub_two_rpow_pos hσ
  have hle : 1 - (2 : ℝ) ^ (-σ) ≤ 1 := by
    have := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-σ)
    linarith
  have hinv : (1 : ℝ) ≤ (1 - (2 : ℝ) ^ (-σ))⁻¹ := by
    rw [le_inv_comm₀ zero_lt_one hpos]
    simpa using hle
  rw [apertureBound]
  linarith

theorem prime_rpow_le (hσ : 0 < σ) (p : Nat.Primes) :
    ((p : ℕ) : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) := by
  have h2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
  exact Real.rpow_le_rpow_of_nonpos (by norm_num) h2 (neg_nonpos.mpr hσ.le)

theorem one_sub_prime_rpow_inv_le (hσ : 0 < σ) (p : Nat.Primes) :
    (1 - ((p : ℕ) : ℝ) ^ (-σ))⁻¹ ≤ (1 - (2 : ℝ) ^ (-σ))⁻¹ := by
  have hp := prime_rpow_le hσ p
  have hpos := one_sub_two_rpow_pos hσ
  have hle : 1 - (2 : ℝ) ^ (-σ) ≤ 1 - ((p : ℕ) : ℝ) ^ (-σ) := by linarith
  rw [inv_eq_one_div, inv_eq_one_div]
  exact one_div_le_one_div_of_le hpos hle

theorem norm_eulerFactorLine_prime_le (hσ : 0 < σ) (p : Nat.Primes) (t : ℝ) :
    ‖eulerFactorLine ((p : ℕ) : ℝ) σ t‖ ≤ apertureBound σ := by
  have h1 := norm_eulerFactorLine_le (one_lt_prime_cast p) hσ t
  have h2 := one_sub_prime_rpow_inv_le hσ p
  have h3 : (0 : ℝ) ≤ (1 - (2 : ℝ) ^ (-σ))⁻¹ := le_of_lt (inv_pos.mpr (one_sub_two_rpow_pos hσ))
  rw [apertureBound]
  linarith

theorem norm_eulerFactorLine_prime_sub_le (hσ : 0 < σ) (p : Nat.Primes) (M : ℕ) (t : ℝ) :
    ‖eulerFactorLine ((p : ℕ) : ℝ) σ t
        - ∑ e ∈ Finset.range M, ((((p : ℕ) : ℝ) ^ (-σ * e) : ℝ) : ℂ)
            * expChar (baseFrequency (((p : ℕ) : ℝ)) e) t‖
      ≤ apertureError σ M := by
  refine le_trans (norm_eulerFactorLine_sub_dirichletSum_le (one_lt_prime_cast p) hσ t M) ?_
  have hp := prime_rpow_le hσ p
  have hnn : (0 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (-σ) :=
    le_of_lt (Real.rpow_pos_of_pos (lt_trans zero_lt_one (one_lt_prime_cast p)) _)
  have hpow : (((p : ℕ) : ℝ) ^ (-σ)) ^ M ≤ ((2 : ℝ) ^ (-σ)) ^ M := pow_le_pow_left₀ hnn hp _
  have hinv := one_sub_prime_rpow_inv_le hσ p
  have hpow0 : (0 : ℝ) ≤ (((p : ℕ) : ℝ) ^ (-σ)) ^ M := pow_nonneg hnn _
  have hinv0 : (0 : ℝ) ≤ (1 - ((p : ℕ) : ℝ) ^ (-σ))⁻¹ := by
    have hlt : ((p : ℕ) : ℝ) ^ (-σ) < 1 := base_rpow_neg_lt_one (one_lt_prime_cast p) hσ
    have : (0 : ℝ) < 1 - ((p : ℕ) : ℝ) ^ (-σ) := by linarith
    exact le_of_lt (inv_pos.mpr this)
  rw [apertureError]
  exact mul_le_mul hpow hinv hinv0 (pow_nonneg (le_of_lt (Real.rpow_pos_of_pos
    (by norm_num : (0 : ℝ) < 2) _)) _)

theorem norm_partialSum_prime_le (hσ : 0 < σ) (p : Nat.Primes) (M : ℕ) (t : ℝ) :
    ‖∑ e ∈ Finset.range M, ((((p : ℕ) : ℝ) ^ (-σ * e) : ℝ) : ℂ)
        * expChar (baseFrequency (((p : ℕ) : ℝ)) e) t‖ ≤ apertureBound σ := by
  have hsplit : (∑ e ∈ Finset.range M, ((((p : ℕ) : ℝ) ^ (-σ * e) : ℝ) : ℂ)
      * expChar (baseFrequency (((p : ℕ) : ℝ)) e) t)
      = eulerFactorLine ((p : ℕ) : ℝ) σ t
        - (eulerFactorLine ((p : ℕ) : ℝ) σ t
          - ∑ e ∈ Finset.range M, ((((p : ℕ) : ℝ) ^ (-σ * e) : ℝ) : ℂ)
            * expChar (baseFrequency (((p : ℕ) : ℝ)) e) t) := by ring
  rw [hsplit]
  refine le_trans (norm_sub_le _ _) ?_
  have h1 := norm_eulerFactorLine_le (one_lt_prime_cast p) hσ t
  have h2 := norm_eulerFactorLine_prime_sub_le hσ p M t
  have h3 := one_sub_prime_rpow_inv_le hσ p
  have hrpow : ((2 : ℝ) ^ (-σ)) ^ M ≤ 1 :=
    pow_le_one₀ (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)) (le_of_lt (two_rpow_lt_one hσ))
  have hinv0 : (0 : ℝ) ≤ (1 - (2 : ℝ) ^ (-σ))⁻¹ := le_of_lt (inv_pos.mpr (one_sub_two_rpow_pos hσ))
  have herr : apertureError σ M ≤ (1 - (2 : ℝ) ^ (-σ))⁻¹ := by
    rw [apertureError]
    nlinarith
  rw [apertureBound]
  linarith

/-- **The uniform approximation of the cutoff Euler product** by its expanded partial products. -/
theorem norm_eulerProductLine_sub_approx_le (hσ : 0 < σ) (N M : ℕ) (t : ℝ) :
    ‖eulerProductLine N σ t
        - ∑ x ∈ Fintype.piFinset (fun _ : ↥(primesLE N) => Finset.range M),
            ((smoothCoeff N σ x : ℝ) : ℂ) * expChar (smoothFreq N x) t‖
      ≤ (primesLE N).card * (apertureBound σ) ^ (primesLE N).card * apertureError σ M := by
  rw [← eulerProductApprox_eq, eulerProductLine]
  refine norm_prod_sub_prod_le _ _ (one_le_apertureBound hσ) ?_ (primesLE N)
    (fun p _ => norm_eulerFactorLine_prime_le hσ p t)
    (fun p _ => norm_partialSum_prime_le hσ p M t)
    (fun p _ => norm_eulerFactorLine_prime_sub_le hσ p M t)
  rw [apertureError]
  have hinv : (0 : ℝ) ≤ (1 - (2 : ℝ) ^ (-σ))⁻¹ :=
    le_of_lt (inv_pos.mpr (one_sub_two_rpow_pos hσ))
  have hpow : (0 : ℝ) ≤ ((2 : ℝ) ^ (-σ)) ^ M :=
    pow_nonneg (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)) _
  exact mul_nonneg hpow hinv

theorem tendsto_apertureError (hσ : 0 < σ) (N : ℕ) :
    Tendsto (fun M : ℕ =>
      (primesLE N).card * (apertureBound σ) ^ (primesLE N).card * apertureError σ M)
      atTop (nhds 0) := by
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one
    (le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-σ))) (two_rpow_lt_one hσ)
  have := ((hlim.mul_const ((1 - (2 : ℝ) ^ (-σ))⁻¹)).const_mul
    ((primesLE N).card * (apertureBound σ) ^ (primesLE N).card))
  simpa [apertureError, mul_assoc] using this

theorem continuous_eulerProductLine (hσ : 0 < σ) (N : ℕ) :
    Continuous (eulerProductLine N σ) := by
  unfold eulerProductLine
  exact continuous_finsetProd _ (fun p _ => continuous_eulerFactorLine (one_lt_prime_cast p) hσ)

theorem continuous_smoothTrig (N : ℕ) (σ : ℝ) (M : ℕ) :
    Continuous (fun t : ℝ => ∑ x ∈ Fintype.piFinset (fun _ : ↥(primesLE N) => Finset.range M),
      ((smoothCoeff N σ x : ℝ) : ℂ) * expChar (smoothFreq N x) t) :=
  continuous_finsetSum _ (fun _x _ => continuous_const.mul (continuous_expChar _))

theorem isBohrAlmostPeriodic_smoothTrig (N : ℕ) (σ : ℝ) (M : ℕ) :
    HTGeometry.IsBohrAlmostPeriodic
      (fun t : ℝ => ∑ x ∈ Fintype.piFinset (fun _ : ↥(primesLE N) => Finset.range M),
        ((smoothCoeff N σ x : ℝ) : ℂ) * expChar (smoothFreq N x) t) :=
  isBohrAlmostPeriodic_sum _ (fun _x _ => continuous_const.mul (continuous_expChar _))
    (fun _x _ => isBohrAlmostPeriodic_const_mul _ (isBohrAlmostPeriodic_expChar _))

theorem isBohrAlmostPeriodic_eulerProductLine (hσ : 0 < σ) (N : ℕ) :
    HTGeometry.IsBohrAlmostPeriodic (eulerProductLine N σ) := by
  refine HTGeometry.isBohrAlmostPeriodic_of_uniform_approx fun ε hε => ?_
  obtain ⟨M, hM⟩ := ((tendsto_apertureError hσ N).eventually (gt_mem_nhds hε)).exists
  exact ⟨_, isBohrAlmostPeriodic_smoothTrig N σ M,
    fun t => le_trans (norm_eulerProductLine_sub_approx_le hσ N M t) hM.le⟩

/-- The Bohr coefficients of the expanded partial product are its exponent-vector coefficients. -/
theorem bohrCoefficient_smoothTrig (N : ℕ) (σ : ℝ) (M : ℕ) (lam : ℝ) :
    bohrCoefficient (fun t : ℝ =>
        ∑ x ∈ Fintype.piFinset (fun _ : ↥(primesLE N) => Finset.range M),
          ((smoothCoeff N σ x : ℝ) : ℂ) * expChar (smoothFreq N x) t) lam
      = (((∑ x ∈ Fintype.piFinset (fun _ : ↥(primesLE N) => Finset.range M),
          if smoothFreq N x = lam then smoothCoeff N σ x else 0) : ℝ) : ℂ) := by
  classical
  have hfun : (fun t : ℝ =>
      ∑ x ∈ Fintype.piFinset (fun _ : ↥(primesLE N) => Finset.range M),
        ((smoothCoeff N σ x : ℝ) : ℂ) * expChar (smoothFreq N x) t)
      = fun t : ℝ => ∑ x ∈ Fintype.piFinset (fun _ : ↥(primesLE N) => Finset.range M),
        ((smoothCoeff N σ x : ℝ) : ℂ) * bohrExp (smoothFreq N x) t := by
    funext t
    exact Finset.sum_congr rfl fun x _ => by rw [expChar_eq_bohrExp]
  rw [hfun, bohrCoefficient_trigPoly, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : smoothFreq N x = lam
  · simp [h]
  · simp [h]

/-- The exponent vector supported at a single prime. -/
noncomputable def singleExponent {N : ℕ} {p : Nat.Primes} (hp : p ∈ primesLE N) :
    ↥(primesLE N) → ℕ := fun i => if i = ⟨p, hp⟩ then 1 else 0

theorem smoothFreq_singleExponent {N : ℕ} {p : Nat.Primes} (hp : p ∈ primesLE N) :
    smoothFreq N (singleExponent hp) = primeLineFrequency p := by
  classical
  rw [smoothFreq]
  rw [Finset.sum_eq_single (⟨p, hp⟩ : ↥(primesLE N))]
  · rw [singleExponent, if_pos rfl, baseFrequency, primeLineFrequency]
    push_cast
    ring
  · intro i _ hi
    rw [singleExponent, if_neg hi, baseFrequency]
    push_cast
    ring
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem smoothCoeff_singleExponent {N : ℕ} (σ : ℝ) {p : Nat.Primes} (hp : p ∈ primesLE N) :
    smoothCoeff N σ (singleExponent hp) = ((p : ℕ) : ℝ) ^ (-σ) := by
  classical
  rw [smoothCoeff]
  rw [Finset.prod_eq_single (⟨p, hp⟩ : ↥(primesLE N))]
  · rw [singleExponent, if_pos rfl]
    norm_num
  · intro i _ hi
    rw [singleExponent, if_neg hi]
    norm_num
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem singleExponent_mem_piFinset {N M : ℕ} {p : Nat.Primes} (hp : p ∈ primesLE N)
    (hM : 1 < M) :
    singleExponent hp ∈ Fintype.piFinset (fun _ : ↥(primesLE N) => Finset.range M) := by
  classical
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_range, singleExponent]
  by_cases h : i = (⟨p, hp⟩ : ↥(primesLE N))
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

/-- **No cancellation.**  The expanded partial product keeps the coefficient at `−log p` above the
Dirichlet coefficient `p^{-σ}`: all exponent-vector coefficients are positive. -/
theorem prime_rpow_le_smoothTrig_coeff {N M : ℕ} (σ : ℝ) {p : Nat.Primes}
    (hp : p ∈ primesLE N) (hM : 1 < M) :
    ((p : ℕ) : ℝ) ^ (-σ)
      ≤ ∑ x ∈ Fintype.piFinset (fun _ : ↥(primesLE N) => Finset.range M),
          if smoothFreq N x = primeLineFrequency p then smoothCoeff N σ x else 0 := by
  classical
  have hterm := Finset.single_le_sum
    (f := fun x : ↥(primesLE N) → ℕ =>
      if smoothFreq N x = primeLineFrequency p then smoothCoeff N σ x else 0)
    (fun x _ => by
      by_cases h : smoothFreq N x = primeLineFrequency p
      · rw [if_pos h]; exact le_of_lt (smoothCoeff_pos N σ x)
      · rw [if_neg h])
    (singleExponent_mem_piFinset hp hM)
  rwa [if_pos (smoothFreq_singleExponent hp), smoothCoeff_singleExponent σ hp] at hterm

/-- **Every aperture prime is a frequency of the cutoff Euler product.** -/
theorem prime_rpow_le_norm_bohrCoefficient_eulerProductLine (hσ : 0 < σ) {N : ℕ} {p : Nat.Primes}
    (hp : p ∈ primesLE N) :
    ((p : ℕ) : ℝ) ^ (-σ)
      ≤ ‖bohrCoefficient (eulerProductLine N σ) (primeLineFrequency p)‖ := by
  classical
  have hlim : Tendsto (fun M : ℕ => ((p : ℕ) : ℝ) ^ (-σ)
      - (primesLE N).card * (apertureBound σ) ^ (primesLE N).card * apertureError σ M) atTop
      (nhds (((p : ℕ) : ℝ) ^ (-σ))) := by
    have h := (tendsto_const_nhds (x := ((p : ℕ) : ℝ) ^ (-σ)) (f := atTop (α := ℕ))).sub
      (tendsto_apertureError hσ N)
    rw [sub_zero] at h
    exact h
  refine le_of_tendsto hlim (eventually_atTop.mpr ⟨2, fun M hM => ?_⟩)
  have hlip := norm_bohrCoefficient_sub_le
    (continuous_smoothTrig N σ M) (isBohrAlmostPeriodic_smoothTrig N σ M)
    (continuous_eulerProductLine hσ N) (isBohrAlmostPeriodic_eulerProductLine hσ N)
    (fun t => by
      have h := norm_eulerProductLine_sub_approx_le hσ N M t
      rw [show (∑ x ∈ Fintype.piFinset (fun _ : ↥(primesLE N) => Finset.range M),
          ((smoothCoeff N σ x : ℝ) : ℂ) * expChar (smoothFreq N x) t) - eulerProductLine N σ t
          = -(eulerProductLine N σ t
            - ∑ x ∈ Fintype.piFinset (fun _ : ↥(primesLE N) => Finset.range M),
              ((smoothCoeff N σ x : ℝ) : ℂ) * expChar (smoothFreq N x) t) from by ring, norm_neg]
      exact h)
    (primeLineFrequency p)
  have hcoeff := bohrCoefficient_smoothTrig N σ M (primeLineFrequency p)
  have hge := prime_rpow_le_smoothTrig_coeff (N := N) (M := M) σ hp (by omega)
  have hnorm : ((p : ℕ) : ℝ) ^ (-σ)
      ≤ ‖bohrCoefficient (fun t : ℝ =>
        ∑ x ∈ Fintype.piFinset (fun _ : ↥(primesLE N) => Finset.range M),
          ((smoothCoeff N σ x : ℝ) : ℂ) * expChar (smoothFreq N x) t) (primeLineFrequency p)‖ := by
    rw [hcoeff, Complex.norm_real, Real.norm_eq_abs]
    have hpos : (0 : ℝ) < ((p : ℕ) : ℝ) ^ (-σ) :=
      Real.rpow_pos_of_pos (lt_trans zero_lt_one (one_lt_prime_cast p)) _
    rw [abs_of_nonneg (le_trans hpos.le hge)]
    exact hge
  have hsub := norm_sub_norm_le
    (bohrCoefficient (fun t : ℝ =>
      ∑ x ∈ Fintype.piFinset (fun _ : ↥(primesLE N) => Finset.range M),
        ((smoothCoeff N σ x : ℝ) : ℂ) * expChar (smoothFreq N x) t) (primeLineFrequency p))
    (bohrCoefficient (eulerProductLine N σ) (primeLineFrequency p))
  linarith

theorem primeLineFrequency_mem_bohrSpectrum_eulerProductLine (hσ : 0 < σ) {N : ℕ}
    {p : Nat.Primes} (hp : p ∈ primesLE N) :
    primeLineFrequency p ∈ bohrSpectrum (eulerProductLine N σ) := by
  show bohrCoefficient (eulerProductLine N σ) (primeLineFrequency p) ≠ 0
  intro hzero
  have h := prime_rpow_le_norm_bohrCoefficient_eulerProductLine hσ hp
  rw [hzero, norm_zero] at h
  exact absurd h (not_le_of_gt (Real.rpow_pos_of_pos
    (lt_trans zero_lt_one (one_lt_prime_cast p)) _))

/-- **The frequency module of the cutoff Euler product is the aperture module.** -/
theorem bohrFrequencyModule_eulerProductLine (hσ : 0 < σ) (N : ℕ) :
    bohrFrequencyModule (eulerProductLine N σ) = primeApertureCharacterModule N := by
  classical
  refine le_antisymm ?_ ?_
  · have hbound := bohrFrequencyModule_le_of_uniform_approx_index
      (continuous_eulerProductLine hσ N) (isBohrAlmostPeriodic_eulerProductLine hσ N)
      ((primeApertureCharacterModule N : Submodule ℚ ℝ) : Set ℝ) (smoothFreq N)
      (fun x => smoothFreq_mem_aperture N x) ?_
    · rwa [Submodule.span_eq] at hbound
    · intro ε hε
      obtain ⟨M, hM⟩ := ((tendsto_apertureError hσ N).eventually (gt_mem_nhds hε)).exists
      exact ⟨Fintype.piFinset (fun _ : ↥(primesLE N) => Finset.range M),
        fun x => ((smoothCoeff N σ x : ℝ) : ℂ),
        fun t => le_trans (norm_eulerProductLine_sub_approx_le hσ N M t) hM.le⟩
  · unfold primeApertureCharacterModule primeLogSpan
    refine Submodule.span_le.mpr ?_
    rintro x ⟨p, rfl⟩
    have hp : (p : Nat.Primes) ∈ primesLE N := p.2
    have hmem := primeLineFrequency_mem_bohrSpectrum_eulerProductLine hσ hp
    have hneg := Submodule.neg_mem (bohrFrequencyModule (eulerProductLine N σ))
      (Submodule.subset_span hmem)
    rw [SetLike.mem_coe]
    rw [primeLineFrequency, neg_neg] at hneg
    exact hneg

/-- The rational Bohr frequency rank of the cutoff Euler product is exactly `π(N)`. -/
theorem finrank_bohrFrequencyModule_eulerProductLine (hσ : 0 < σ) (N : ℕ) :
    Module.finrank ℚ (bohrFrequencyModule (eulerProductLine N σ)) = Nat.primeCounting N := by
  rw [bohrFrequencyModule_eulerProductLine hσ, primeApertureCharacterModule_finrank]

/-- **The carrier bound on the cutoff Euler product itself.**  Any finite rational character space
receiving an injection of its frequency module has dimension at least `π(N)`. -/
theorem eulerProduct_carrier_covering_dim_ge {A : Type*} [AddCommGroup A] [Module ℚ A]
    [Module.Finite ℚ A] (hσ : 0 < σ) (N : ℕ)
    (j : bohrFrequencyModule (eulerProductLine N σ) →ₗ[ℚ] A) (hj : Function.Injective j) :
    Nat.primeCounting N ≤ Module.finrank ℚ A := by
  have h := bohrFrequencyModule_eulerProductLine hσ N
  refine primeAperture_carrier_covering_dim_ge N
    (j.comp (LinearEquiv.ofEq _ _ h.symm).toLinearMap) ?_
  exact hj.comp (LinearEquiv.ofEq _ _ h.symm).injective

end

end GaloisForLFunctions
