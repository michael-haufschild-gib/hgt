import Mathlib

/-!
# Atom lower bounds under measure convolution

Elementary lower bounds on the atoms of a convolution `μ ∗ ν` and of `n`-fold self-convolutions
`μ^{∗n}`: an atom of a convolution is at least the product of atoms of the factors summing to it.
These are the reusable measure-theory primitives behind compound-distribution atom arithmetic — for
instance the two-particle atom birth of `theta-likelihood-square-gap-nondivisibility` and the
compound-Poisson atom-support closure step of its non-divisibility argument.
-/

open MeasureTheory
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry
variable {M : Type*} [AddCommMonoid M] [MeasurableSpace M] [MeasurableAdd₂ M] [MeasurableSingletonClass M]

/-- **Atoms add under convolution.**  For measures `μ, ν` on an additive monoid, the convolution
`μ ∗ ν` puts at least mass `μ{a}·ν{b}` on `a + b`. -/
theorem measure_singleton_le_conv (μ ν : Measure M) [SFinite ν] (a b : M) :
    μ {a} * ν {b} ≤ (μ ∗ ν) {a + b} := by
  rw [Measure.conv, Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
  calc μ {a} * ν {b} = (μ.prod ν) ({a} ×ˢ {b}) := (Measure.prod_prod _ _).symm
    _ ≤ (μ.prod ν) ((fun x => x.1 + x.2) ⁻¹' {a + b}) := by
        apply measure_mono; rintro ⟨x, y⟩ hxy
        simp only [Set.mem_prod, Set.mem_singleton_iff] at hxy
        simp only [Set.mem_preimage, Set.mem_singleton_iff, hxy.1, hxy.2]

omit [MeasurableAdd₂ M] [MeasurableSingletonClass M] in
/-- `n`-fold self-convolution of a measure (`μ^{∗n}`, with `μ^{∗0} = δ₀`). -/
noncomputable def convPow (μ : Measure M) : ℕ → Measure M
  | 0 => Measure.dirac 0
  | (n + 1) => μ ∗ convPow μ n

omit [MeasurableAdd₂ M] [MeasurableSingletonClass M] in
instance sFinite_convPow (μ : Measure M) [SFinite μ] (n : ℕ) : SFinite (convPow μ n) := by
  induction n with
  | zero => rw [convPow]; infer_instance
  | succ n ih => rw [convPow]; haveI := ih; infer_instance

set_option maxHeartbeats 800000 in
/-- **Atoms add under `n`-fold convolution.**  If each `a i` is an atom of `μ`, then `∑ a i` is an
atom of `μ^{∗n}` with mass at least `∏ μ{a i}`. -/
theorem prod_measure_singleton_le_convPow (μ : Measure M) [SFinite μ] :
    ∀ (n : ℕ) (a : Fin n → M), (∏ i, μ {a i}) ≤ (convPow μ n) {∑ i, a i} := by
  intro n
  induction n with
  | zero =>
    intro a
    simp only [Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_empty, convPow]
    rw [Measure.dirac_apply' 0 (measurableSet_singleton 0)]
    simp
  | succ n ih =>
    intro a
    haveI := sFinite_convPow μ n
    rw [convPow, Fin.prod_univ_succ, Fin.sum_univ_succ]
    exact le_trans (mul_le_mul' (le_refl (μ {a 0})) (ih (fun i => a (Fin.succ i))))
      (measure_singleton_le_conv μ (convPow μ n) (a 0) (∑ i, a (Fin.succ i)))

omit [MeasurableSingletonClass M] in
/-- **Convolution powers add**: `μ^{∗(m+n)} = μ^{∗m} ∗ μ^{∗n}` (associativity + `δ₀` identity). -/
theorem convPow_add (μ : Measure M) [SFinite μ] (m n : ℕ) :
    convPow μ (m + n) = convPow μ m ∗ convPow μ n := by
  induction m with
  | zero =>
    haveI := sFinite_convPow μ n
    rw [Nat.zero_add, convPow, Measure.dirac_zero_conv]
  | succ m ih =>
    haveI := sFinite_convPow μ m
    haveI := sFinite_convPow μ n
    rw [Nat.succ_add, convPow, ih, convPow, Measure.conv_assoc]

/-- **Atoms of convolution powers form an additive sub-semigroup.**  If `x` is an atom of `μ^{∗m}`
and `y` an atom of `μ^{∗n}`, then `x + y` is an atom of `μ^{∗(m+n)}`.  This is the compound-Poisson
atom-support closure core (concatenating the atom tuples). -/
theorem convPow_singleton_add_ne_zero (μ : Measure M) [SFinite μ] {m n : ℕ} {x y : M}
    (hx : convPow μ m {x} ≠ 0) (hy : convPow μ n {y} ≠ 0) :
    convPow μ (m + n) {x + y} ≠ 0 := by
  haveI := sFinite_convPow μ n
  have h := measure_singleton_le_conv (convPow μ m) (convPow μ n) x y
  rw [← convPow_add] at h
  exact fun hz => (mul_ne_zero hx hy) (nonpos_iff_eq_zero.mp (h.trans_eq hz))

/-- A nonnegative-weighted mixture of convolution powers `∑_m c_m · μ^{∗m}`.  With
`c_m = e^{-λ} λ^m / m!` this is the compound Poisson law with jump distribution `μ` and intensity `λ`. -/
noncomputable def convPowMixture (c : ℕ → ℝ≥0∞) (μ : Measure M) : Measure M :=
  Measure.sum (fun m => c m • convPow μ m)

omit [MeasurableAdd₂ M] in
theorem convPowMixture_singleton (c : ℕ → ℝ≥0∞) (μ : Measure M) (x : M) :
    convPowMixture c μ {x} = ∑' m, c m * (convPow μ m) {x} := by
  rw [convPowMixture, Measure.sum_apply _ (measurableSet_singleton x)]
  simp only [Measure.smul_apply, smul_eq_mul]

/-- **Compound-Poisson atom-support closure.**  Every positive-weighted convolution-power mixture has
additively closed atom support: if `x` and `y` are atoms, so is `x + y`. -/
theorem convPowMixture_singleton_add_ne_zero {c : ℕ → ℝ≥0∞} (hc : ∀ m, c m ≠ 0)
    (μ : Measure M) [SFinite μ] {x y : M}
    (hx : convPowMixture c μ {x} ≠ 0) (hy : convPowMixture c μ {y} ≠ 0) :
    convPowMixture c μ {x + y} ≠ 0 := by
  rw [convPowMixture_singleton] at hx hy
  have hex : ∀ (z : M), (∑' m, c m * (convPow μ m) {z}) ≠ 0 → ∃ m, (convPow μ m) {z} ≠ 0 := by
    intro z hz
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hz (ENNReal.tsum_eq_zero.mpr (fun m => by rw [h m, mul_zero]))
  obtain ⟨m, hm⟩ := hex x hx
  obtain ⟨n, hn⟩ := hex y hy
  have hatom : (convPow μ (m + n)) {x + y} ≠ 0 := convPow_singleton_add_ne_zero μ hm hn
  rw [convPowMixture_singleton]
  intro hz
  exact (mul_ne_zero (hc (m + n)) hatom) (nonpos_iff_eq_zero.mp ((ENNReal.le_tsum (m + n)).trans_eq hz))

omit [MeasurableSingletonClass M] in
theorem isProbabilityMeasure_convPow (μ : Measure M) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (convPow μ n) := by
  induction n with
  | zero => rw [convPow]; infer_instance
  | succ n ih => rw [convPow]; haveI := ih; infer_instance

omit [MeasurableSingletonClass M] in
/-- A probability measure is **infinitely divisible** when it is an `n`-fold convolution power of some
probability measure, for every `n`. -/
def InfinitelyDivisible (μ : Measure M) : Prop :=
  ∀ n : ℕ, 0 < n → ∃ ν : Measure M, IsProbabilityMeasure ν ∧ μ = convPow ν n

/-- A measure is a **compound Poisson mixture** when it is a positive-weighted mixture of convolution
powers `∑_m c_m · Q^{∗m}` of some `SFinite` jump law `Q`. -/
def IsCompoundPoissonMixture (μ : Measure M) : Prop :=
  ∃ (c : ℕ → ℝ≥0∞) (Q : Measure M), (∀ m, c m ≠ 0) ∧ SFinite Q ∧ μ = convPowMixture c Q

/-- Compound Poisson mixtures have additively closed atom support. -/
theorem IsCompoundPoissonMixture.singleton_add_ne_zero {μ : Measure M}
    (h : IsCompoundPoissonMixture μ) {x y : M} (hx : μ {x} ≠ 0) (hy : μ {y} ≠ 0) :
    μ {x + y} ≠ 0 := by
  obtain ⟨c, Q, hc, hQ, rfl⟩ := h
  haveI := hQ
  exact convPowMixture_singleton_add_ne_zero hc Q hx hy

omit [MeasurableSingletonClass M] in
/-- **Convolution distributes over `Measure.sum` on the left**: `(∑_i f i) ∗ ν = ∑_i (f i ∗ ν)`. -/
theorem sum_conv {ι : Type*} (f : ι → Measure M) (ν : Measure M) [SFinite ν] :
    (Measure.sum f) ∗ ν = Measure.sum (fun i => f i ∗ ν) := by
  rw [Measure.conv, Measure.prod_sum_left, Measure.map_sum (by fun_prop)]
  rfl

omit [MeasurableSingletonClass M] in
/-- **Convolution distributes over `Measure.sum` on the right**: `μ ∗ (∑_i f i) = ∑_i (μ ∗ f i)`. -/
theorem conv_sum {ι : Type*} [Countable ι] (μ : Measure M) (f : ι → Measure M) [∀ i, SFinite (f i)] :
    μ ∗ (Measure.sum f) = Measure.sum (fun i => μ ∗ f i) := by
  rw [Measure.conv, Measure.prod_sum_right, Measure.map_sum (by fun_prop)]
  rfl

omit [MeasurableSingletonClass M] in
/-- **Convolution of two convolution-power mixtures**: `(∑_m c₁_m Q^{∗m}) ∗ (∑_k c₂_k Q^{∗k})
= ∑_m ∑_k (c₁_m·c₂_k) Q^{∗(m+k)}`.  The structural step behind the compound-Poisson convolution
semigroup (the coefficient double sum is the Cauchy product of `c₁, c₂`). -/
theorem convPowMixture_conv (c₁ c₂ : ℕ → ℝ≥0∞) (Q : Measure M) [SFinite Q] :
    convPowMixture c₁ Q ∗ convPowMixture c₂ Q =
      Measure.sum (fun m => Measure.sum (fun k => (c₁ m * c₂ k) • convPow Q (m + k))) := by
  rw [convPowMixture, convPowMixture, sum_conv]
  congr 1
  funext m
  rw [conv_sum]
  congr 1
  funext k
  rw [Measure.conv_smul_left, Measure.conv_smul_right, smul_smul, convPow_add]

open Finset in
/-- **Poisson/exponential coefficient Cauchy product** (EGF product identity):
`∑_{(m,k)∈antidiag j} (a^m/m!)(b^k/k!) = (a+b)^j/j!`.  For the compound-Poisson intensities this is the
semigroup coefficient identity `compoundPoisson(a) ∗ compoundPoisson(b) = compoundPoisson(a+b)`. -/
theorem poisson_cauchy (a b : ℝ) (j : ℕ) :
    ∑ p ∈ Finset.antidiagonal j, (a ^ p.1 / p.1.factorial) * (b ^ p.2 / p.2.factorial)
      = (a + b) ^ j / j.factorial := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, add_pow, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_range, Nat.lt_succ_iff] at hm
  have h1 : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  have h2 : ((j - m).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (j - m).factorial_ne_zero
  have h3 : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  have hchoose : (j.choose m : ℝ) * m.factorial * (j - m).factorial = j.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hm
  rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero h1 h2) h3, ← hchoose]
  ring

variable {α : Type*} [MeasurableSpace α]

/-- **`Measure.sum` over a sigma type** equals the iterated sum (`Measure.sum_apply` + `tsum_sigma'`). -/
theorem measure_sum_sigma {ι : Type*} {T : ι → Type*} (f : (Σ i, T i) → Measure α) :
    Measure.sum f = Measure.sum (fun i => Measure.sum (fun t : T i => f ⟨i, t⟩)) := by
  ext s hs
  rw [Measure.sum_apply _ hs, Measure.sum_apply _ hs, ENNReal.tsum_sigma' (fun p => (f p) s)]
  exact tsum_congr (fun i => (Measure.sum_apply _ hs).symm)

/-- Equivalence grouping `ℕ × ℕ` by the antidiagonal of the coordinate sum. -/
def sigmaAntidiagEquiv : (Σ j : ℕ, {p : ℕ × ℕ // p ∈ Finset.antidiagonal j}) ≃ ℕ × ℕ where
  toFun x := x.2.1
  invFun p := ⟨p.1 + p.2, ⟨p, Finset.mem_antidiagonal.mpr rfl⟩⟩
  left_inv := fun ⟨j, p, hp⟩ => by simp only [Finset.mem_antidiagonal] at hp; subst hp; rfl
  right_inv := fun _ => rfl

/-- **Antidiagonal Cauchy reindex for `Measure.sum`**: a double-indexed measure sum over `ℕ × ℕ`
regroups as a sum over `j` of the finite antidiagonal sums. -/
theorem measure_sum_antidiagonal (g : ℕ × ℕ → Measure α) :
    Measure.sum g = Measure.sum (fun j : ℕ => ∑ p ∈ Finset.antidiagonal j, g p) := by
  rw [← Measure.sum_comp_equiv sigmaAntidiagEquiv g, measure_sum_sigma]
  exact congrArg Measure.sum (funext (fun j => Measure.sum_coe_finset (Finset.antidiagonal j) g))

omit [MeasurableSingletonClass M] in
/-- **Convolution of two convolution-power mixtures is a mixture with the Cauchy-product coefficients**:
`(∑_m c₁_m Q^{∗m}) ∗ (∑_k c₂_k Q^{∗k}) = ∑_j (∑_{p∈antidiag j} c₁_{p.1}·c₂_{p.2}) Q^{∗j}`.  The complete
compound-Poisson convolution-semigroup structural formula. -/
theorem convPowMixture_conv_antidiagonal (c₁ c₂ : ℕ → ℝ≥0∞) (Q : Measure M) [SFinite Q] :
    convPowMixture c₁ Q ∗ convPowMixture c₂ Q =
      convPowMixture (fun j => ∑ p ∈ Finset.antidiagonal j, c₁ p.1 * c₂ p.2) Q := by
  rw [convPowMixture_conv, Measure.sum_sum, measure_sum_antidiagonal, convPowMixture]
  refine congrArg Measure.sum (funext (fun j => ?_))
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Finset.mem_antidiagonal] at hp
  rw [hp]

omit [MeasurableSingletonClass M] in
/-- Compound Poisson law with intensity `lam` and jump distribution `Q`. -/
noncomputable def compoundPoisson (lam : ℝ) (Q : Measure M) : Measure M :=
  convPowMixture (fun m => ENNReal.ofReal (Real.exp (-lam) * lam ^ m / m.factorial)) Q

theorem compoundPoisson_coeff_cauchy (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (j : ℕ) :
    (∑ p ∈ Finset.antidiagonal j,
        ENNReal.ofReal (Real.exp (-a) * a ^ p.1 / p.1.factorial) *
          ENNReal.ofReal (Real.exp (-b) * b ^ p.2 / p.2.factorial))
      = ENNReal.ofReal (Real.exp (-(a + b)) * (a + b) ^ j / j.factorial) := by
  have hreal : ∑ p ∈ Finset.antidiagonal j,
      (Real.exp (-a) * a ^ p.1 / p.1.factorial) * (Real.exp (-b) * b ^ p.2 / p.2.factorial)
      = Real.exp (-(a + b)) * (a + b) ^ j / j.factorial := by
    have hfac : ∀ p : ℕ × ℕ,
        (Real.exp (-a) * a ^ p.1 / p.1.factorial) * (Real.exp (-b) * b ^ p.2 / p.2.factorial)
        = Real.exp (-(a + b)) * ((a ^ p.1 / p.1.factorial) * (b ^ p.2 / p.2.factorial)) := by
      intro p
      rw [show -(a + b) = -a + -b by ring, Real.exp_add]; ring
    rw [Finset.sum_congr rfl (fun p _ => hfac p), ← Finset.mul_sum, poisson_cauchy]
    ring
  rw [← hreal, ENNReal.ofReal_sum_of_nonneg]
  · exact Finset.sum_congr rfl (fun p _ => (ENNReal.ofReal_mul (by positivity)).symm)
  · intro p _
    positivity

omit [MeasurableSingletonClass M] in
/-- **Compound Poisson convolution semigroup**: `compoundPoisson(a) ∗ compoundPoisson(b) =
compoundPoisson(a+b)` for `a, b ≥ 0` — via the mixture Cauchy product and the Poisson coefficient
identity `poisson_cauchy`. -/
theorem compoundPoisson_conv (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (Q : Measure M) [SFinite Q] :
    compoundPoisson a Q ∗ compoundPoisson b Q = compoundPoisson (a + b) Q := by
  rw [compoundPoisson, compoundPoisson, convPowMixture_conv_antidiagonal, compoundPoisson]
  congr 1
  funext j
  exact compoundPoisson_coeff_cauchy a b ha hb j

omit [MeasurableAdd₂ M] [MeasurableSingletonClass M] in
/-- `compoundPoisson 0 Q = δ₀` (only the `m = 0` term survives). -/
theorem compoundPoisson_zero (Q : Measure M) [SFinite Q] :
    compoundPoisson 0 Q = Measure.dirac 0 := by
  rw [compoundPoisson, convPowMixture]; ext s hs
  rw [Measure.sum_apply _ hs, tsum_eq_single 0]
  · rw [convPow]; norm_num
  · intro m hm; rw [Measure.smul_apply]; simp [zero_pow hm]

omit [MeasurableSingletonClass M] in
/-- **`n`-fold compound-Poisson semigroup**: `(compoundPoisson lam Q)^{∗n} = compoundPoisson (n·lam) Q`. -/
theorem convPow_compoundPoisson (lam : ℝ) (hlam : 0 ≤ lam) (Q : Measure M) [SFinite Q] (n : ℕ) :
    convPow (compoundPoisson lam Q) n = compoundPoisson (n * lam) Q := by
  induction n with
  | zero => rw [convPow, Nat.cast_zero, zero_mul, compoundPoisson_zero]
  | succ n ih =>
    rw [convPow, ih, compoundPoisson_conv lam (n * lam) hlam (mul_nonneg (Nat.cast_nonneg n) hlam)]
    congr 1; push_cast; ring

omit [MeasurableSingletonClass M] in
/-- The compound Poisson law is a probability measure (its Poisson weights sum to `1`). -/
theorem isProbabilityMeasure_compoundPoisson (lam : ℝ) (hlam : 0 ≤ lam) (Q : Measure M) [IsProbabilityMeasure Q] :
    IsProbabilityMeasure (compoundPoisson lam Q) := by
  have hcoeff : ∀ m : ℕ, (0:ℝ) ≤ Real.exp (-lam) * lam ^ m / m.factorial :=
    fun m => div_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg hlam m)) (Nat.cast_nonneg _)
  have hsummable : Summable (fun m : ℕ => Real.exp (-lam) * lam ^ m / m.factorial) := by
    simp_rw [mul_div_assoc]; exact (Real.summable_pow_div_factorial lam).mul_left _
  have hexp : ∑' m : ℕ, lam ^ m / m.factorial = Real.exp lam := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hsum : ∑' m : ℕ, Real.exp (-lam) * lam ^ m / m.factorial = 1 := by
    simp_rw [mul_div_assoc]; rw [tsum_mul_left, hexp, ← Real.exp_add]; simp
  have huniv : ∀ m : ℕ, (convPow Q m) Set.univ = 1 := fun m => (isProbabilityMeasure_convPow Q m).measure_univ
  constructor
  rw [compoundPoisson, convPowMixture, Measure.sum_apply _ MeasurableSet.univ]
  simp_rw [Measure.smul_apply, smul_eq_mul, huniv, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg hcoeff hsummable, hsum, ENNReal.ofReal_one]

omit [MeasurableSingletonClass M] in
/-- **Compound Poisson laws are infinitely divisible** (the easy half of the ID/compound-Poisson
equivalence): `compoundPoisson(lam) = compoundPoisson(lam/n)^{∗n}` with `compoundPoisson(lam/n)` a
probability measure. -/
theorem infinitelyDivisible_compoundPoisson (lam : ℝ) (hlam : 0 ≤ lam) (Q : Measure M)
    [IsProbabilityMeasure Q] : InfinitelyDivisible (compoundPoisson lam Q) := by
  intro n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  refine ⟨compoundPoisson (lam / n) Q,
    isProbabilityMeasure_compoundPoisson _ (div_nonneg hlam (Nat.cast_nonneg n)) Q, ?_⟩
  rw [convPow_compoundPoisson (lam / n) (div_nonneg hlam (Nat.cast_nonneg n)) Q n]
  congr 1
  field_simp

omit [MeasurableSingletonClass M] in
/-- **`n`-fold convolution distributes over `∗`** (commutative monoid): `(μ ∗ ν)^{∗n} = μ^{∗n} ∗ ν^{∗n}`. -/
theorem convPow_conv (μ ν : Measure M) [SFinite μ] [SFinite ν] (n : ℕ) :
    convPow (μ ∗ ν) n = convPow μ n ∗ convPow ν n := by
  induction n with
  | zero => rw [convPow, convPow, convPow, Measure.dirac_zero_conv]
  | succ n ih =>
    haveI := sFinite_convPow μ n
    haveI := sFinite_convPow ν n
    rw [convPow, ih, convPow, convPow]
    calc (μ ∗ ν) ∗ (convPow μ n ∗ convPow ν n)
        = μ ∗ (ν ∗ (convPow μ n ∗ convPow ν n)) := Measure.conv_assoc _ _ _
      _ = μ ∗ ((ν ∗ convPow μ n) ∗ convPow ν n) := by
        rw [← Measure.conv_assoc ν (convPow μ n) (convPow ν n)]
      _ = μ ∗ ((convPow μ n ∗ ν) ∗ convPow ν n) := by rw [Measure.conv_comm ν (convPow μ n)]
      _ = μ ∗ (convPow μ n ∗ (ν ∗ convPow ν n)) := by
        rw [Measure.conv_assoc (convPow μ n) ν (convPow ν n)]
      _ = (μ ∗ convPow μ n) ∗ (ν ∗ convPow ν n) := by
        rw [← Measure.conv_assoc μ (convPow μ n) (ν ∗ convPow ν n)]

omit [MeasurableSingletonClass M] in
/-- **Infinite divisibility is closed under convolution.** -/
theorem InfinitelyDivisible.conv {μ ν : Measure M} (hμ : InfinitelyDivisible μ)
    (hν : InfinitelyDivisible ν) : InfinitelyDivisible (μ ∗ ν) := by
  intro n hn
  obtain ⟨μn, hμn, hμeq⟩ := hμ n hn
  obtain ⟨νn, hνn, hνeq⟩ := hν n hn
  haveI := hμn
  haveI := hνn
  exact ⟨μn ∗ νn, inferInstance, by rw [hμeq, hνeq, convPow_conv]⟩

omit [MeasurableSingletonClass M] in
/-- `δ₀^{∗n} = δ₀`. -/
theorem convPow_dirac_zero (n : ℕ) : convPow (Measure.dirac (0 : M)) n = Measure.dirac 0 := by
  induction n with
  | zero => rw [convPow]
  | succ k ih => rw [convPow, ih, Measure.dirac_zero_conv]

omit [MeasurableSingletonClass M] in
/-- The point mass `δ₀` is infinitely divisible. -/
theorem infinitelyDivisible_dirac_zero : InfinitelyDivisible (Measure.dirac (0 : M)) :=
  fun n _ => ⟨Measure.dirac 0, inferInstance, (convPow_dirac_zero n).symm⟩

omit [MeasurableSingletonClass M] in
/-- **Generating functions are multiplicative under convolution.**  For any measurable
`f : M → ℝ≥0∞` that is multiplicative on the monoid (`f (x + y) = f x * f y`) — e.g. a Laplace
kernel `x ↦ exp (-s x)`, an MGF kernel, or a character — the integral against a convolution
factors: `∫⁻ f d(μ ∗ ν) = (∫⁻ f dμ) * (∫⁻ f dν)`. -/
theorem lintegral_conv_of_multiplicative {f : M → ℝ≥0∞} (hf : Measurable f)
    (hmul : ∀ x y, f (x + y) = f x * f y) (μ ν : Measure M) [SFinite ν] :
    ∫⁻ z, f z ∂(μ ∗ ν) = (∫⁻ x, f x ∂μ) * (∫⁻ y, f y ∂ν) := by
  rw [Measure.lintegral_conv hf]
  simp_rw [hmul, lintegral_const_mul _ hf]
  rw [lintegral_mul_const _ hf]

omit [MeasurableSingletonClass M] in
/-- **Generating function of an `n`-fold convolution power is the `n`-th power.**  For a
measurable multiplicative `f` with `f 0 = 1`, `∫⁻ f d(μ^{∗n}) = (∫⁻ f dμ) ^ n`.  This is the
Laplace/MGF identity underlying infinite-divisibility arguments: the transform of a law's `n`-th
convolution root is the `n`-th root of its transform. -/
theorem lintegral_convPow_of_multiplicative {f : M → ℝ≥0∞} (hf : Measurable f)
    (hmul : ∀ x y, f (x + y) = f x * f y) (h0 : f 0 = 1) (μ : Measure M) [SFinite μ] (n : ℕ) :
    ∫⁻ z, f z ∂(convPow μ n) = (∫⁻ x, f x ∂μ) ^ n := by
  induction n with
  | zero => rw [convPow, pow_zero, lintegral_dirac' _ hf, h0]
  | succ k ih => rw [convPow, lintegral_conv_of_multiplicative hf hmul, ih, pow_succ']

/-! ### Singleton (atomic) analysis of convolutions on `ℝ`

The mass a convolution places on a single point is the fibre integral of the second factor.  For a
self-convolution this makes the singleton mass a sum over pairs of atoms, so a point unreachable as a
sum of two atoms carries no mass — the exact structure behind the atomic non-divisibility
obstruction. -/

/-- **Singleton mass of a convolution as a fibre integral:** `(μ ∗ ν){z} = ∫⁻ x, ν{z - x} ∂μ`. -/
theorem conv_singleton_eq_lintegral (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] (z : ℝ) :
    (μ ∗ ν) {z} = ∫⁻ x, ν {z - x} ∂μ := by
  rw [Measure.conv, Measure.map_apply (by fun_prop) (measurableSet_singleton z),
    Measure.prod_apply (by measurability)]
  congr 1; ext x; congr 1; ext y
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-- The atoms of a finite measure on `ℝ` form a countable set. -/
theorem countable_atoms (ν : Measure ℝ) [IsFiniteMeasure ν] :
    {x : ℝ | ν {x} ≠ 0}.Countable := by
  have h := Measure.countable_meas_level_set_pos (μ := ν) (g := (id : ℝ → ℝ)) measurable_id
  have hset : {x : ℝ | ν {x} ≠ 0} = {t | 0 < ν {a | id a = t}} := by
    ext t; simp [pos_iff_ne_zero]
  rw [hset]; exact h

/-- **No-pair vanishing.**  If no atom of `ν` pairs with another to sum to `z`
(`ν{x} ≠ 0 → ν{z - x} = 0`), then the self-convolution charges no mass at `z`:
`(ν ∗ ν){z} = 0`.  Only atom pairs contribute to a singleton, so the absence of pairs forces the
mass to vanish. -/
theorem conv_self_singleton_eq_zero_of_no_pair (ν : Measure ℝ) [IsFiniteMeasure ν] (z : ℝ)
    (hpair : ∀ x, ν {x} ≠ 0 → ν {z - x} = 0) : (ν ∗ ν) {z} = 0 := by
  rw [conv_singleton_eq_lintegral]
  set S : Set ℝ := (fun a => z - a) '' {x | ν {x} ≠ 0} with hS
  have hScount : S.Countable := (countable_atoms ν).image _
  have hSmeas : MeasurableSet S := hScount.measurableSet
  have hSnull : ν S = 0 := by
    have : ν (⋃ s ∈ S, ({s} : Set ℝ)) = 0 := by
      rw [measure_biUnion_null_iff hScount]
      rintro s ⟨a, ha, rfl⟩
      exact hpair a ha
    rwa [Set.biUnion_of_singleton] at this
  have hbound : ∀ x, ν {z - x} ≤ S.indicator (fun _ => (⊤ : ℝ≥0∞)) x := by
    intro x
    by_cases hx : x ∈ S
    · simp [Set.indicator_of_mem hx]
    · have hzx : ν {z - x} = 0 := by
        by_contra hne
        exact hx ⟨z - x, hne, by ring⟩
      simp [hzx]
  refine nonpos_iff_eq_zero.mp ?_
  calc ∫⁻ x, ν {z - x} ∂ν
      ≤ ∫⁻ x, S.indicator (fun _ => (⊤ : ℝ≥0∞)) x ∂ν := lintegral_mono hbound
    _ = ⊤ * ν S := by rw [lintegral_indicator_const hSmeas]
    _ = 0 := by rw [hSnull, mul_zero]

end GaloisForLFunctions.HTGeometry
