import GaloisForLFunctions.HTGeometry.OriginAtomFormationProperness
import GaloisForLFunctions.HTGeometry.PrimeFormationMeasureObserver
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Algebra.Polynomial.Roots

/-!
# Complete rate reconstruction for hypoexponential formation

The law `ν_λ = Exp(λ_1) ∗ ⋯ ∗ Exp(λ_m)` has Laplace transform `L_λ(z) = Π_j λ_j/(λ_j + z)`
`(CTL.25)`, from `∫_0^∞ e^{-zx} λ e^{-λx} dx = λ/(λ + z)` and Fubini.  Along a rate path
`λ + s v`, `d/ds L / L = Σ_j z v_j / (λ_j(λ_j + z))` `(CTL.26)`, which vanishes at `z = 0`.

If this logarithmic derivative vanishes at every positive integer and the rates are distinct, every
velocity vanishes (Theorem 6.1): `Q(z) = Σ_j (v_j/λ_j) z Π_{k ≠ j}(λ_k + z)` is a polynomial with
infinitely many roots, so `Q = 0`, and `Q(-λ_j) = -v_j Π_{k ≠ j}(λ_k - λ_j)`.

For a finite set of primes the subset rates `λ_S = log Π_{p ∈ S} p` are distinct by unique
factorization `(CTL.27)`, so the complete integer response reconstructs every subset-rate velocity
and in particular every prime-log velocity.  A hypoexponential law has no atom at the origin, so the
convolution multiplier of a subset-phase formation is compact with dense nonclosed range on `c_0`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped NNReal ENNReal ZeroAtInfty

noncomputable section

namespace GaloisForLFunctions.HTGeometry.LaplaceTomography

open GaloisForLFunctions.HTGeometry.PrimeShiftSource Permutohedral

/-! ### The Laplace transform of a hypoexponential law `(CTL.25)` -/

theorem integral_exp_expMeasure {ρ : ℝ} (hρ : 0 < ρ) {z : ℝ} (hz : 0 ≤ z) :
    ∫ x, Real.exp (-(z * x)) ∂(expMeasure ρ) = ρ / (ρ + z) := by
  rw [expMeasure, gammaMeasure, integral_withDensity_eq_integral_toReal_smul (f := gammaPDF 1 ρ)
    (measurable_gammaPDFReal 1 ρ).ennreal_ofReal (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  have h : ∀ x : ℝ, (gammaPDF 1 ρ x).toReal • Real.exp (-(z * x)) =
      (Ici (0 : ℝ)).indicator (fun x => ρ * Real.exp (-(ρ + z) * x)) x := fun x => by
    have he := exponentialPDF_eq ρ x
    rw [exponentialPDF] at he
    change ENNReal.ofReal (gammaPDFReal 1 ρ x) = _ at he
    rw [show gammaPDF 1 ρ x = ENNReal.ofReal (gammaPDFReal 1 ρ x) from rfl, he]
    by_cases hx : 0 ≤ x
    · rw [if_pos hx, indicator_of_mem (mem_Ici.2 hx), ENNReal.toReal_ofReal
        (mul_nonneg hρ.le (Real.exp_pos _).le), smul_eq_mul, mul_assoc, ← Real.exp_add]
      ring_nf
    · rw [if_neg hx, indicator_of_notMem (by simpa using hx), ENNReal.ofReal_zero,
        ENNReal.toReal_zero, zero_smul]
  simp_rw [h]
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, integral_const_mul,
    integral_exp_mul_Ioi (by linarith) 0]
  field_simp
  simp

theorem ae_nonneg_of_hasHalfLineCDF {ν : Measure ℝ} {F : ℝ → ℝ} (h : HasHalfLineCDF ν F) :
    ∀ᵐ x ∂ν, 0 ≤ x := by
  have hnull : ν (Iio 0) = 0 := by
    have : Iio (0 : ℝ) = ⋃ n : ℕ, Iic (-(1 / ((n : ℝ) + 1))) := by
      ext x
      simp only [mem_Iio, mem_iUnion, mem_Iic]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (neg_pos.2 hx)
        exact ⟨n, by linarith⟩
      · rintro ⟨n, hn⟩
        have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    rw [this]
    exact measure_iUnion_null fun n => h.Iic_neg _ (by
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith)
  rw [ae_iff]
  simp only [not_le]
  exact hnull

theorem integrable_exp_of_ae_nonneg {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : ∀ᵐ x ∂ν, 0 ≤ x)
    {z : ℝ} (hz : 0 ≤ z) : Integrable (fun x => Real.exp (-(z * x))) ν :=
  Integrable.of_bound (by fun_prop) 1 (hν.mono fun x hx => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
    exact mul_nonneg hz hx)

/-- **`(CTL.25)`**: `∫ e^{-zx} dν_λ = Π_j λ_j/(λ_j + z)` for `z ≥ 0`. -/
theorem integral_exp_hypoMeasureList :
    ∀ {ρs : List ℝ}, (∀ ρ ∈ ρs, 0 < ρ) → ∀ {z : ℝ}, 0 ≤ z →
      ∫ x, Real.exp (-(z * x)) ∂(hypoMeasureList ρs) = (ρs.map fun ρ => ρ / (ρ + z)).prod
  | [], _, z, _ => by simp [hypoMeasureList]
  | ρ :: ρs, h, z, hz => by
    have hρ : 0 < ρ := h ρ List.mem_cons_self
    have hs : ∀ x ∈ ρs, 0 < x := fun x hx => h x (List.mem_cons_of_mem ρ hx)
    haveI := isProbabilityMeasure_expMeasure hρ
    haveI := isProbabilityMeasure_hypoMeasureList hs
    haveI := isProbabilityMeasure_hypoMeasureList h
    have hint : Integrable (fun x => Real.exp (-(z * x))) (expMeasure ρ ∗ hypoMeasureList ρs) :=
      integrable_exp_of_ae_nonneg
        (ae_nonneg_of_hasHalfLineCDF (hasHalfLineCDF_hypoMeasureList h)) hz
    rw [hypoMeasureList, integral_conv hint, List.map_cons, List.prod_cons,
      ← integral_exp_hypoMeasureList hs hz, ← integral_exp_expMeasure hρ hz, ← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    dsimp only
    rw [← Real.exp_add]
    ring_nf

/-- `L_λ(z) = Π_j λ_j/(λ_j + z)` for rates indexed by a finite type. -/
def laplaceRates {ι : Type*} [Fintype ι] (lam : ι → ℝ) (z : ℝ) : ℝ := ∏ j, lam j / (lam j + z)

theorem integral_exp_hypoMeasure_ofFn {m : ℕ} {lam : Fin m → ℝ} (hlam : ∀ j, 0 < lam j) {z : ℝ}
    (hz : 0 ≤ z) :
    ∫ x, Real.exp (-(z * x)) ∂(hypoMeasureList (List.ofFn lam)) = laplaceRates lam z := by
  rw [integral_exp_hypoMeasureList (fun ρ hρ => by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hρ
    exact hlam j) hz, laplaceRates, List.map_ofFn, List.prod_ofFn]
  rfl

/-! ### The rate-velocity log-derivative `(CTL.26)` -/

/-- **`(CTL.26)`**: along `λ + s v`, `d/ds L_{λ+sv}(z) = L_λ(z) Σ_j z v_j/(λ_j(λ_j + z))`. -/
theorem hasDerivAt_laplaceRates {ι : Type*} [Fintype ι] {lam : ι → ℝ} (hlam : ∀ j, 0 < lam j)
    (v : ι → ℝ)
    {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt (fun s => laplaceRates (fun j => lam j + s * v j) z)
      (laplaceRates lam z * ∑ j, z * v j / (lam j * (lam j + z))) 0 := by
  classical
  have hne : ∀ j, lam j + z ≠ 0 := fun j => by linarith [hlam j]
  have hfac : ∀ j, HasDerivAt (fun s => (lam j + s * v j) / (lam j + s * v j + z))
      (z * v j / (lam j + z) ^ 2) 0 := fun j => by
    have h1 : HasDerivAt (fun s => lam j + s * v j) (v j) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v j)).const_add (lam j)
    have h2 : HasDerivAt (fun s => lam j + s * v j + z) (v j) 0 := h1.add_const z
    refine (h1.div h2 (by simpa using hne j)).congr_deriv ?_
    show (v j * (lam j + 0 * v j + z) - (lam j + 0 * v j) * v j) / (lam j + 0 * v j + z) ^ 2 = _
    simp only [zero_mul, add_zero]
    field_simp
    ring
  have hprod := HasDerivAt.finsetProd (u := Finset.univ) fun j _ => hfac j
  have hfun : (∏ j ∈ Finset.univ, fun s => (lam j + s * v j) / (lam j + s * v j + z)) =
      fun s => laplaceRates (fun j => lam j + s * v j) z := by
    funext s
    simp [laplaceRates, Finset.prod_apply]
  rw [hfun] at hprod
  refine hprod.congr_deriv ?_
  show ∑ i ∈ Finset.univ, (∏ j ∈ Finset.univ.erase i,
      (lam j + 0 * v j) / (lam j + 0 * v j + z)) • (z * v i / (lam i + z) ^ 2) = _
  simp only [zero_mul, add_zero, smul_eq_mul]
  rw [laplaceRates, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_prod_erase Finset.univ (fun j => lam j / (lam j + z)) (Finset.mem_univ i)]
  have hl : lam i ≠ 0 := (hlam i).ne'
  field_simp

/-- The normalized rate response `(d/ds L)/L` at `z`. -/
def rateResponse {ι : Type*} [Fintype ι] (lam v : ι → ℝ) (z : ℝ) : ℝ :=
  ∑ j, z * v j / (lam j * (lam j + z))

theorem rateResponse_zero {ι : Type*} [Fintype ι] (lam v : ι → ℝ) : rateResponse lam v 0 = 0 := by
  simp [rateResponse]

/-! ### Theorem 6.1: complete rate reconstruction -/

/-- **Theorem 6.1**: for distinct positive rates, a velocity whose normalized response vanishes at
every positive integer is zero. -/
theorem eq_zero_of_rateResponse {ι : Type*} [Fintype ι] {lam : ι → ℝ} (hlam : ∀ j, 0 < lam j)
    (hinj : Function.Injective lam) {v : ι → ℝ}
    (h : ∀ n : ℕ, 1 ≤ n → rateResponse lam v n = 0) : v = 0 := by
  classical
  open Polynomial in
  set Q : ℝ[X] := ∑ j, C (v j / lam j) * X * ∏ k ∈ Finset.univ.erase j, (C (lam k) + X)
  have hQn : ∀ n : ℕ, 1 ≤ n → Q.eval (n : ℝ) = 0 := fun n hn => by
    have hpos : ∀ k, lam k + n ≠ 0 := fun k => by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith [hlam k]
    have hval : Q.eval (n : ℝ) = (∏ k, (lam k + n)) * rateResponse lam v n := by
      simp only [Q, eval_finsetSum, eval_mul, eval_C, eval_X, eval_prod, eval_add, rateResponse,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.mul_prod_erase Finset.univ (fun k => lam k + (n : ℝ)) (Finset.mem_univ j)]
      have hl : lam j ≠ 0 := (hlam j).ne'
      field_simp [hpos j]
    rw [hval, h n hn, mul_zero]
  have hQ : Q = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot Q (Set.infinite_of_injective_forall_mem
      (f := fun n : ℕ => ((n + 1 : ℕ) : ℝ)) (fun a b hab => by simpa using hab) fun n => ?_)
    exact hQn (n + 1) (Nat.le_add_left 1 n)
  funext i
  have hi : Q.eval (-lam i) = -v i * ∏ k ∈ Finset.univ.erase i, (lam k - lam i) := by
    simp only [Q, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_prod, Polynomial.eval_add]
    rw [Finset.sum_eq_single i (fun j _ hj => by
      rw [Finset.prod_eq_zero (i := i) (Finset.mem_erase.2 ⟨Ne.symm hj, Finset.mem_univ _⟩)
        (by ring), mul_zero]) (by simp)]
    have hl : lam i ≠ 0 := (hlam i).ne'
    rw [show ∏ k ∈ Finset.univ.erase i, (lam k + -lam i) =
      ∏ k ∈ Finset.univ.erase i, (lam k - lam i) from Finset.prod_congr rfl fun k _ => by ring]
    field_simp
  rw [hQ, Polynomial.eval_zero] at hi
  have hprod : ∏ k ∈ Finset.univ.erase i, (lam k - lam i) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k hk => sub_ne_zero.2 fun he =>
      (Finset.mem_erase.1 hk).1 (hinj he)
  have := hi.symm
  rw [neg_mul, neg_eq_zero, mul_eq_zero] at this
  exact this.resolve_right hprod


/-- Along a rate path the Laplace transform of the law itself has derivative
`L_λ(z) Σ_j z v_j/(λ_j(λ_j + z))` `(CTL.26)`. -/
theorem hasDerivAt_integral_rate_path {m : ℕ} {lam : Fin m → ℝ} (hlam : ∀ j, 0 < lam j)
    (v : Fin m → ℝ) {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt (fun s => ∫ x, Real.exp (-(z * x)) ∂(hypoMeasureList
      (List.ofFn fun j => lam j + s * v j))) (laplaceRates lam z * rateResponse lam v z) 0 := by
  refine (hasDerivAt_laplaceRates hlam v hz).congr_of_eventuallyEq ?_
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ j, 0 < lam j + s * v j := by
    refine Filter.eventually_all.2 fun j => ?_
    have : Tendsto (fun s : ℝ => lam j + s * v j) (𝓝 0) (𝓝 (lam j)) := by
      have h : Continuous fun s : ℝ => lam j + s * v j := by fun_prop
      simpa using h.tendsto 0
    exact this.eventually (lt_mem_nhds (hlam j))
  filter_upwards [hev] with s hs
  exact integral_exp_hypoMeasure_ofFn hs hz

/-! ### Prime subset rates `(CTL.27)` -/

/-- **`(CTL.27)`**: distinct subsets of a finite prime set have distinct rates
`λ_S = log Π_{p ∈ S} p` (unique factorization). -/
theorem subsetRate_injective (I : PrimeSet) :
    Function.Injective fun S : Finset (Fin I.1.card) => ∑ i ∈ S, I.grades i := by
  intro S T hST
  have hprod : ∀ U : Finset (Fin I.1.card), ∑ i ∈ U, I.grades i =
      Real.log ((∏ p ∈ U.image I.prime, p : ℕ) : ℝ) := fun U => by
    rw [Finset.prod_image (f := fun p : ℕ => p) (g := I.prime)
      fun a _ b _ h => (I.1.orderEmbOfFin rfl).injective h]
    push_cast
    rw [Real.log_prod (fun i _ => by exact_mod_cast (I.prime_prime i).ne_zero)]
    rfl
  simp only at hST
  rw [hprod, hprod] at hST
  have hpos : ∀ U : Finset (Fin I.1.card), (0 : ℝ) < ((∏ p ∈ U.image I.prime, p : ℕ) : ℝ) :=
    fun U => by
      exact_mod_cast Finset.prod_pos fun p hp => by
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
        exact (I.prime_prime i).pos
  have h1 := Real.log_injOn_pos (hpos S) (hpos T) hST
  have h2 : (∏ p ∈ S.image I.prime, p) = ∏ p ∈ T.image I.prime, p := by exact_mod_cast h1
  have hpr : ∀ U : Finset (Fin I.1.card), ∀ p ∈ U.image I.prime, p.Prime := fun U p hp => by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    exact I.prime_prime i
  have h3 : S.image I.prime = T.image I.prime := by
    rw [← Nat.primeFactors_prod (hpr S), ← Nat.primeFactors_prod (hpr T), h2]
  exact Finset.image_injective (fun a b h => (I.1.orderEmbOfFin rfl).injective h) h3

/-- The nonempty subsets of a prime set, as an index type. -/
abbrev SubsetIdx (I : PrimeSet) : Type := {S : Finset (Fin I.1.card) // S ∈ subsets I.1.card}

theorem subsetRate_pos (I : PrimeSet) (S : SubsetIdx I) : 0 < ∑ i ∈ S.1, I.grades i := by
  obtain ⟨i, hi⟩ := (Finset.mem_filter.1 S.2).2
  exact Finset.sum_pos (fun j _ => I.grades_pos j) ⟨i, hi⟩

/-- `∫ e^{-zx} dμ_I = Π_{∅ ≠ S} λ_S/(λ_S + z)`. -/
theorem integral_exp_subsetLaw {r : ℕ} {lam : Fin r → ℝ} (hlam : ∀ i, 0 < lam i) {z : ℝ}
    (hz : 0 ≤ z) :
    ∫ x, Real.exp (-(z * x)) ∂(subsetLaw lam) =
      ∏ S ∈ subsets r, (∑ i ∈ S, lam i) / ((∑ i ∈ S, lam i) + z) := by
  rw [subsetLaw, integral_exp_hypoMeasureList (subsetRates_pos hlam) hz, subsetRates, List.map_map]
  exact Finset.prod_map_toList _ _

/-- **Complete prime-log velocity reconstruction.**  Along `λ_S(s) = Σ_{i ∈ S}(log p_i + s w_i)`,
if the normalized derivative of the subset-phase Laplace transform vanishes at every positive
integer, then every subset velocity `Σ_{i ∈ S} w_i` vanishes, and so does every prime-log velocity `w_i`. -/
theorem prime_velocity_reconstruction (I : PrimeSet) (w : Fin I.1.card → ℝ)
    (h : ∀ n : ℕ, 1 ≤ n → rateResponse (fun S : SubsetIdx I => ∑ i ∈ S.1, I.grades i)
      (fun S => ∑ i ∈ S.1, w i) n = 0) :
    (∀ S : SubsetIdx I, ∑ i ∈ S.1, w i = 0) ∧ w = 0 := by
  have hv := eq_zero_of_rateResponse (subsetRate_pos I)
    (fun S T hST => Subtype.ext (subsetRate_injective I hST)) h
  refine ⟨fun S => congrFun hv S, funext fun i => ?_⟩
  have hi : ({i} : Finset (Fin I.1.card)) ∈ subsets I.1.card :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.singleton_nonempty i⟩
  have := congrFun hv ⟨{i}, hi⟩
  simpa using this

/-- The normalized derivative of `μ_I`'s Laplace transform along a prime-log velocity is the rate
response of the subset velocities. -/
theorem hasDerivAt_integral_subsetLaw (I : PrimeSet) (w : Fin I.1.card → ℝ) {z : ℝ}
    (hz : 0 ≤ z) :
    HasDerivAt (fun s => ∫ x, Real.exp (-(z * x)) ∂(subsetLaw fun i => I.grades i + s * w i))
      (laplaceRates (fun S : SubsetIdx I => ∑ i ∈ S.1, I.grades i) z *
        rateResponse (fun S : SubsetIdx I => ∑ i ∈ S.1, I.grades i) (fun S => ∑ i ∈ S.1, w i) z)
      0 := by
  refine (hasDerivAt_laplaceRates (subsetRate_pos I) (fun S => ∑ i ∈ S.1, w i) hz)
    |>.congr_of_eventuallyEq ?_
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ i, 0 < I.grades i + s * w i := by
    refine Filter.eventually_all.2 fun i => ?_
    have : Tendsto (fun s : ℝ => I.grades i + s * w i) (𝓝 0) (𝓝 (I.grades i)) := by
      have h : Continuous fun s : ℝ => I.grades i + s * w i := by fun_prop
      simpa using h.tendsto 0
    exact this.eventually (lt_mem_nhds (I.grades_pos i))
  filter_upwards [hev] with s hs
  rw [integral_exp_subsetLaw hs hz, laplaceRates, ← Finset.prod_coe_sort]
  refine Finset.prod_congr rfl fun S _ => ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]

/-! ### No origin atom: compact cofinal response -/

theorem hypoMeasureList_zero_atom {ρ : ℝ} {ρs : List ℝ} (h : ∀ x ∈ ρ :: ρs, 0 < x) :
    hypoMeasureList (ρ :: ρs) {0} = 0 :=
  measure_mono_null (Set.singleton_subset_iff.2 (Set.mem_Iic.2 le_rfl)) (by
    rw [(hasHalfLineCDF_hypoMeasureList h).Iic_eq 0 le_rfl]
    show ENNReal.ofReal (expKernelConv ρ (hypoCDFList ρs) 0) = 0
    rw [expKernelConv_zero, ENNReal.ofReal_zero])

/-- A law on `ℝ` carried by `[0, ∞)`, as a law on `[0, ∞)`. -/
def halfLineLaw (ν : Measure ℝ) : Measure ℝ≥0 := ν.comap NNReal.toReal

theorem measurableEmbedding_toReal : MeasurableEmbedding NNReal.toReal :=
  NNReal.isClosedEmbedding_coe.measurableEmbedding

theorem map_halfLineLaw {ν : Measure ℝ} (hν : ∀ᵐ x ∂ν, 0 ≤ x) :
    (halfLineLaw ν).map NNReal.toReal = ν := by
  rw [halfLineLaw, measurableEmbedding_toReal.map_comap, Measure.restrict_eq_self_of_ae_mem]
  filter_upwards [hν] with x hx
  exact ⟨⟨x, hx⟩, rfl⟩

theorem isProbabilityMeasure_halfLineLaw {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, 0 ≤ x) : IsProbabilityMeasure (halfLineLaw ν) := by
  constructor
  have h : (halfLineLaw ν).map NNReal.toReal univ = ν univ := by rw [map_halfLineLaw hν]
  rwa [Measure.map_apply measurableEmbedding_toReal.measurable MeasurableSet.univ,
    preimage_univ, measure_univ (μ := ν)] at h

theorem halfLineLaw_zero (ν : Measure ℝ) : halfLineLaw ν {0} = ν {0} := by
  rw [halfLineLaw, measurableEmbedding_toReal.comap_apply, Set.image_singleton, NNReal.coe_zero]

/-- A subset-phase formation law `μ_I` has no origin atom, so its convolution multiplier on `c_0`
is injective and compact with dense, nonclosed range. -/
theorem primeLaw_compact_response (I : PrimeSet) :
    haveI := isProbabilityMeasure_halfLineLaw (ν := primeLaw I)
      (ae_nonneg_of_hasHalfLineCDF (hasHalfLineCDF_subsetLaw I.grades_pos))
    halfLineLaw (primeLaw I) {0} = 0 ∧
      Function.Injective (diagMul (halfLineLaw (primeLaw I))) ∧
      IsCompactOperator (diagMul (halfLineLaw (primeLaw I))) ∧
      Dense (range (diagMul (halfLineLaw (primeLaw I)))) ∧
      ¬ IsClosed (range (diagMul (halfLineLaw (primeLaw I)))) := by
  haveI := isProbabilityMeasure_halfLineLaw (ν := primeLaw I)
    (ae_nonneg_of_hasHalfLineCDF (hasHalfLineCDF_subsetLaw I.grades_pos))
  have h0 : halfLineLaw (primeLaw I) {0} = 0 := by
    rw [halfLineLaw_zero]
    obtain ⟨ρ, ρs, h⟩ := List.exists_cons_of_ne_nil (subsetRates_ne_nil I)
    rw [primeLaw, subsetLaw, h]
    exact hypoMeasureList_zero_atom (h ▸ subsetRates_pos I.grades_pos)
  obtain ⟨hi, hc, -, hd, hn, -⟩ := originAtom_zero _ h0
  exact ⟨h0, hi, hc, hd, hn⟩

end GaloisForLFunctions.HTGeometry.LaplaceTomography
