import GaloisForLFunctions.HTGeometry.ObserverFibreCurrentBudget

/-!
# Prefix localization on a product of finite sets

On `X = ∏_{n ≥ 0} X_n` with finite discrete factors and `0 < θ < 1` put
`d_θ(x, x') = θ^{m(x, x')}`, `m` the first index where `x` and `x'` differ.  This ultrametric
induces the product topology.  Points in one fibre of the prefix observer `π_N` (the restriction to
the first `N` coordinates) are at distance at most `θ^N`, so an `L`-Lipschitz effect oscillates by
at most `Lθ^N` inside each fibre, and the observer-fibre budget gives

`∫ e d(μ₁ - μ₀) ≤ TV(μ₀^{<N}, μ₁^{<N}) + 2Lθ^N`.

Applied to the Neyman–Pearson effect of an exact formation this gives
`α(K_d) ≥ (TV(p₀^{⊗d}, p₁^{⊗d}) - TV(μ₀^{<N}, μ₁^{<N}))_+ / (2θ^N)`.  For product laws the prefix
affinity tensorizes to `A_{s,N} = ∏_{n<N} a_n`, and Cauchy–Schwarz gives `TV ≤ √(1 - A²)` for finite
laws, whence `α(K_d) ≥ (1 - A^d - √(1 - A_{s,N}²))_+ / (2θ^N)`.
-/

open MeasureTheory Set Filter Topology PiNat
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## The prefix ultrametric -/

section Ultrametric

variable {E : ℕ → Type*}

open Classical in
/-- `d_θ(x, x') = θ^{m(x, x')}` for `x ≠ x'` and `0` on the diagonal. -/
def prefixDist (θ : ℝ) (x y : ∀ n, E n) : ℝ := if x ≠ y then θ ^ firstDiff x y else 0

theorem prefixDist_eq_of_ne {θ : ℝ} {x y : ∀ n, E n} (h : x ≠ y) :
    prefixDist θ x y = θ ^ firstDiff x y := by
  simp [prefixDist, h]

theorem prefixDist_self (θ : ℝ) (x : ∀ n, E n) : prefixDist θ x x = 0 := by simp [prefixDist]

theorem prefixDist_comm (θ : ℝ) (x y : ∀ n, E n) : prefixDist θ x y = prefixDist θ y x := by
  classical
  simp [prefixDist, @eq_comm _ x y, firstDiff_comm]

theorem prefixDist_nonneg {θ : ℝ} (hθ : 0 ≤ θ) (x y : ∀ n, E n) : 0 ≤ prefixDist θ x y := by
  rcases eq_or_ne x y with rfl | h
  · simp [prefixDist]
  · rw [prefixDist_eq_of_ne h]
    positivity

theorem prefixDist_triangle_nonarch {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (x y z : ∀ n, E n) :
    prefixDist θ x z ≤ max (prefixDist θ x y) (prefixDist θ y z) := by
  rcases eq_or_ne x z with rfl | hxz
  · simp [prefixDist_self, prefixDist_nonneg hθ0]
  rcases eq_or_ne x y with rfl | hxy
  · simp
  rcases eq_or_ne y z with rfl | hyz
  · simp
  rw [prefixDist_eq_of_ne hxz, prefixDist_eq_of_ne hxy, prefixDist_eq_of_ne hyz]
  rcases min_le_iff.mp (min_firstDiff_le x y z hxz) with h | h
  · exact le_max_of_le_left (pow_le_pow_of_le_one hθ0 hθ1 h)
  · exact le_max_of_le_right (pow_le_pow_of_le_one hθ0 hθ1 h)

theorem prefixDist_triangle {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (x y z : ∀ n, E n) :
    prefixDist θ x z ≤ prefixDist θ x y + prefixDist θ y z :=
  (prefixDist_triangle_nonarch hθ0 hθ1 x y z).trans
    (max_le_add_of_nonneg (prefixDist_nonneg hθ0 _ _) (prefixDist_nonneg hθ0 _ _))

theorem eq_of_prefixDist_eq_zero {θ : ℝ} (hθ : 0 < θ) (x y : ∀ n, E n)
    (h : prefixDist θ x y = 0) : x = y := by
  rcases eq_or_ne x y with rfl | hxy
  · rfl
  rw [prefixDist_eq_of_ne hxy] at h
  exact absurd h (pow_pos hθ _).ne'

theorem mem_cylinder_iff_prefixDist_le {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {x y : ∀ n, E n}
    {n : ℕ} : y ∈ cylinder x n ↔ prefixDist θ y x ≤ θ ^ n := by
  rcases eq_or_ne y x with rfl | hne
  · simp [prefixDist_self, pow_nonneg hθ0.le]
  rw [prefixDist_eq_of_ne hne, mem_cylinder_iff_le_firstDiff hne]
  exact (pow_le_pow_iff_right_of_lt_one₀ hθ0 hθ1).symm

theorem isOpen_iff_prefixDist [∀ n, TopologicalSpace (E n)] [∀ n, DiscreteTopology (E n)]
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (s : Set (∀ n, E n)) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, prefixDist θ x y < ε → y ∈ s := by
  constructor
  · intro hs x hx
    obtain ⟨v, ⟨y, n, rfl⟩, h'x, h's⟩ :=
      (isTopologicalBasis_cylinders E).exists_subset_of_mem_open hx hs
    rw [← mem_cylinder_iff_eq.1 h'x] at h's
    refine ⟨θ ^ n, pow_pos hθ0 n, fun y hy => h's ?_⟩
    rw [mem_cylinder_iff_prefixDist_le hθ0 hθ1, prefixDist_comm]
    exact hy.le
  · intro h
    refine (isTopologicalBasis_cylinders E).isOpen_iff.2 fun x hx => ?_
    obtain ⟨ε, εpos, hε⟩ := h x hx
    obtain ⟨n, hn⟩ : ∃ n : ℕ, θ ^ n < ε := exists_pow_lt_of_lt_one εpos hθ1
    refine ⟨cylinder x n, ⟨x, n, rfl⟩, self_mem_cylinder x n, fun y hy => hε y ?_⟩
    rw [prefixDist_comm]
    exact ((mem_cylinder_iff_prefixDist_le hθ0 hθ1).mp hy).trans_lt hn

end Ultrametric

/-- The product of the `E n` equipped with the prefix ultrametric `d_θ`. -/
def PrefixSpace (_θ : ℝ) (E : ℕ → Type*) : Type _ := ∀ n, E n

namespace PrefixSpace

variable {θ : ℝ} {E : ℕ → Type*}

instance [∀ n, MeasurableSpace (E n)] : MeasurableSpace (PrefixSpace θ E) :=
  inferInstanceAs (MeasurableSpace (∀ n, E n))

instance [∀ n, Nonempty (E n)] : Nonempty (PrefixSpace θ E) :=
  inferInstanceAs (Nonempty (∀ n, E n))

/-- `d_θ` is a metric inducing the product topology. -/
instance instMetricSpace [∀ n, TopologicalSpace (E n)] [∀ n, DiscreteTopology (E n)]
    [Fact (0 < θ)] [Fact (θ < 1)] : MetricSpace (PrefixSpace θ E) :=
  @MetricSpace.ofDistTopology (∀ n, E n) Pi.topologicalSpace (prefixDist θ) (prefixDist_self θ)
    (prefixDist_comm θ) (prefixDist_triangle (Fact.out : 0 < θ).le (Fact.out : θ < 1).le)
    (isOpen_iff_prefixDist Fact.out Fact.out) (eq_of_prefixDist_eq_zero Fact.out)

variable [∀ n, TopologicalSpace (E n)] [∀ n, DiscreteTopology (E n)] [Fact (0 < θ)]
  [Fact (θ < 1)]

theorem dist_eq (x y : PrefixSpace θ E) : dist x y = prefixDist θ x y := rfl

theorem topology_eq :
    (inferInstance : TopologicalSpace (PrefixSpace θ E))
      = (Pi.topologicalSpace : TopologicalSpace (∀ n, E n)) := rfl

instance [∀ n, MeasurableSpace (E n)] [∀ n, BorelSpace (E n)] [∀ n, Fintype (E n)] :
    BorelSpace (PrefixSpace θ E) :=
  ⟨BorelSpace.measurable_eq (α := ∀ n, E n)⟩

end PrefixSpace

/-! ## Prefix localization -/

section Localization

variable {θ : ℝ} {E : ℕ → Type*}

/-- The prefix observer `π_N`, the restriction to the first `N` coordinates. -/
def prefixObserver (N : ℕ) (x : PrefixSpace θ E) : ∀ i : Finset.range N, E i :=
  (Finset.range N).restrict x

theorem measurable_prefixObserver [∀ n, MeasurableSpace (E n)] (N : ℕ) :
    Measurable (prefixObserver (θ := θ) (E := E) N) :=
  Finset.measurable_restrict _

theorem surjective_prefixObserver [∀ n, Nonempty (E n)] (N : ℕ) :
    Function.Surjective (prefixObserver (θ := θ) (E := E) N) := by
  classical
  intro y
  refine ⟨fun n => if h : n ∈ Finset.range N then y ⟨n, h⟩ else Classical.arbitrary (E n), ?_⟩
  funext i
  simp [prefixObserver, i.2]

variable [Fact (0 < θ)] [Fact (θ < 1)] [∀ n, TopologicalSpace (E n)] [∀ n, DiscreteTopology (E n)]

theorem prefixDist_le_of_prefixObserver_eq {N : ℕ} {x x' : PrefixSpace θ E}
    (h : prefixObserver N x = prefixObserver N x') : dist x x' ≤ θ ^ N := by
  rw [PrefixSpace.dist_eq]
  have hmem : x ∈ cylinder (E := E) x' N := mem_cylinder_iff.2 fun i hi => by
    simpa [prefixObserver] using congrFun h ⟨i, Finset.mem_range.mpr hi⟩
  exact (mem_cylinder_iff_prefixDist_le Fact.out Fact.out).mp hmem

variable [∀ n, Fintype (E n)] [∀ n, Nonempty (E n)] [∀ n, MeasurableSpace (E n)]
  [∀ n, BorelSpace (E n)]

/-- **Theorem 5.3 (RP.17).**  `∫ e d(μ₁ - μ₀) ≤ TV(μ₀^{<N}, μ₁^{<N}) + 2Lθ^N` for every
`L`-Lipschitz
effect. -/
theorem hahnEffectCurrent_le_prefix (P Q : Measure (PrefixSpace θ E)) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {e : PrefixSpace θ E → ℝ} (heb : ∀ x, e x ∈ Icc (0 : ℝ) 1)
    {L : ℝ≥0} (hL : LipschitzWith L e) (N : ℕ) :
    hahnEffectCurrent P Q e
      ≤ measurableHahnTV (P.map (prefixObserver N)) (Q.map (prefixObserver N))
        + 2 * L * θ ^ N := by
  have h := hahnEffectCurrent_le_observer_add P Q (measurable_prefixObserver N)
    (surjective_prefixObserver N) hL.continuous.measurable heb
  have hosc : fibreOscillation (prefixObserver N) e ≤ L * θ ^ N := by
    haveI : Nonempty {p : PrefixSpace θ E × PrefixSpace θ E //
        prefixObserver N p.1 = prefixObserver N p.2} :=
      ⟨⟨(Classical.arbitrary _, Classical.arbitrary _), rfl⟩⟩
    refine ciSup_le fun p => ?_
    have hd := prefixDist_le_of_prefixObserver_eq p.2
    have h2 := hL.dist_le_mul p.1.1 p.1.2
    rw [Real.dist_eq] at h2
    exact h2.trans (mul_le_mul_of_nonneg_left hd L.2)
  linarith

variable {Y : Type*} [Fintype Y] [MetricSpace Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]

/-- **Theorem 5.3 (RP.18)–(RP.19).**  An exact formation has
`α(K_d) ≥ (TV(p₀^{⊗d}, p₁^{⊗d}) - TV(μ₀^{<N}, μ₁^{<N})) / (2θ^N)`. -/
theorem prefix_resolutionAmplification_ge (P Q : Measure (PrefixSpace θ E))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hsep : ∀ y y' : Y, y ≠ y' → 1 ≤ dist y y') (p₀ p₁ : Measure Y) [IsProbabilityMeasure p₀]
    [IsProbabilityMeasure p₁] {d : ℕ} (K : ProbabilityTheory.Kernel (PrefixSpace θ E) (Fin d → Y))
    [ProbabilityTheory.IsMarkovKernel K] (h₀ : IsExactFormation P K p₀)
    (h₁ : IsExactFormation Q K p₁) {B : Set (Fin d → Y)} (hNP : IsNeymanPearson p₀ p₁ B)
    (N : ℕ) :
    ENNReal.ofReal
        ((measurableHahnTV (Measure.pi fun _ : Fin d => p₀) (Measure.pi fun _ : Fin d => p₁)
          - measurableHahnTV (P.map (prefixObserver N)) (Q.map (prefixObserver N)))
          / (2 * θ ^ N))
      ≤ resolutionAmplification K := by
  obtain ⟨hcur, hlip, -⟩ := formation_resolutionPrice_law P Q hsep p₀ p₁ K h₀ h₁ hNP
  rcases eq_or_ne (resolutionAmplification K) ⊤ with htop | hfin
  · rw [htop]
    exact le_top
  have hαfin : lipNorm (formationEffect K B) < ⊤ := hlip.trans_lt (lt_top_iff_ne_top.mpr hfin)
  have hL := lipschitzWith_of_lipNorm_lt_top hαfin
  have h := hahnEffectCurrent_le_prefix P Q (formationEffect_mem K B) hL N
  rw [hcur] at h
  have hθN : 0 < θ ^ N := pow_pos Fact.out N
  have hle : (lipNorm (formationEffect K B)).toReal ≤ (resolutionAmplification K).toReal :=
    ENNReal.toReal_mono hfin hlip
  rw [← ENNReal.ofReal_toReal hfin]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_iff₀ (by positivity)]
  have : ((lipNorm (formationEffect K B)).toNNReal : ℝ) = (lipNorm (formationEffect K B)).toReal :=
    rfl
  rw [this] at h
  nlinarith

end Localization

/-! ## Product laws -/

section Product

/-- The Hellinger affinity of finite product laws is the product of the factor affinities. -/
theorem hellingerAffinity_pi_dep {ι : Type*} [Fintype ι] [DecidableEq ι] {F : ι → Type*}
    [∀ i, Fintype (F i)] [∀ i, MeasurableSpace (F i)] [∀ i, MeasurableSingletonClass (F i)]
    (P Q : ∀ i, Measure (F i)) [∀ i, IsProbabilityMeasure (P i)]
    [∀ i, IsProbabilityMeasure (Q i)] :
    hellingerAffinity (Measure.pi P) (Measure.pi Q) = ∏ i, hellingerAffinity (P i) (Q i) := by
  simp only [hellingerAffinity, tsum_fintype]
  have hpi : ∀ (R : ∀ i, Measure (F i)) [∀ i, IsProbabilityMeasure (R i)] (y : ∀ i, F i),
      (Measure.pi R {y}).toReal = ∏ i, (R i {y i}).toReal := by
    intro R _ y
    rw [← Set.univ_pi_singleton, Measure.pi_pi, ENNReal.toReal_prod]
  simp_rw [hpi, ← Finset.prod_mul_distrib]
  rw [Finset.prod_univ_sum (fun i => (Finset.univ : Finset (F i)))
    (fun i z => Real.sqrt ((P i {z}).toReal * (Q i {z}).toReal)), Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact Real.sqrt_prod _ fun i _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- `TV(u, v) ≤ √(1 - A(u, v)²)` for laws on a finite set. -/
theorem measurableHahnTV_le_sqrt {Z : Type*} [Fintype Z] [MeasurableSpace Z]
    [MeasurableSingletonClass Z] (u v : Measure Z) [IsProbabilityMeasure u]
    [IsProbabilityMeasure v] :
    measurableHahnTV u v ≤ Real.sqrt (1 - hellingerAffinity u v ^ 2) := by
  have htot : ∀ (ρ : Measure Z) [IsProbabilityMeasure ρ], ∑ z, ρ.real {z} = 1 := by
    intro ρ _
    rw [← measureReal_eq_sum_singleton ρ Finset.univ, Finset.coe_univ, probReal_univ]
  set A := hellingerAffinity u v with hAdef
  have hA : A = ∑ z, Real.sqrt (u.real {z}) * Real.sqrt (v.real {z}) := by
    rw [hAdef, hellingerAffinity, tsum_fintype]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← Real.sqrt_mul measureReal_nonneg]
    rfl
  have hTV : 2 * measurableHahnTV u v = ∑ z, |u.real {z} - v.real {z}| := by
    rw [measurableHahnTV_eq_one_sub_sum_min]
    have : ∀ z, |u.real {z} - v.real {z}| = u.real {z} + v.real {z}
        - 2 * min (u.real {z}) (v.real {z}) := by
      intro z
      rcases le_total (u.real {z}) (v.real {z}) with h | h
      · rw [min_eq_left h, abs_of_nonpos (by linarith)]
        ring
      · rw [min_eq_right h, abs_of_nonneg (by linarith)]
        ring
    simp_rw [this]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, htot u, htot v, ← Finset.mul_sum]
    ring
  have hsq : ∀ z, |u.real {z} - v.real {z}|
      = |Real.sqrt (u.real {z}) - Real.sqrt (v.real {z})|
        * (Real.sqrt (u.real {z}) + Real.sqrt (v.real {z})) := by
    intro z
    have h1 : u.real {z} - v.real {z} = (Real.sqrt (u.real {z}) - Real.sqrt (v.real {z}))
        * (Real.sqrt (u.real {z}) + Real.sqrt (v.real {z})) := by
      rw [show ∀ a b : ℝ, (a - b) * (a + b) = a ^ 2 - b ^ 2 from fun a b => by ring,
        Real.sq_sqrt measureReal_nonneg, Real.sq_sqrt measureReal_nonneg]
    rw [h1, abs_mul, abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun z => |Real.sqrt (u.real {z}) - Real.sqrt (v.real {z})|)
    (fun z => Real.sqrt (u.real {z}) + Real.sqrt (v.real {z}))
  have hS1 : ∑ z, |Real.sqrt (u.real {z}) - Real.sqrt (v.real {z})| ^ 2 = 2 - 2 * A := by
    simp_rw [sq_abs, sub_sq, Real.sq_sqrt measureReal_nonneg]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, htot u, htot v, hA, Finset.mul_sum]
    ring_nf
  have hS2 : ∑ z, (Real.sqrt (u.real {z}) + Real.sqrt (v.real {z})) ^ 2 = 2 + 2 * A := by
    simp_rw [add_sq, Real.sq_sqrt measureReal_nonneg]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, htot u, htot v, hA, Finset.mul_sum]
    ring_nf
  simp_rw [← hsq] at hCS
  rw [hS1, hS2, ← hTV] at hCS
  have hTV0 : 0 ≤ measurableHahnTV u v := by
    rw [measurableHahnTV]
    exact mul_nonneg (by norm_num) (integral_nonneg fun _ => abs_nonneg _)
  rw [Real.le_sqrt hTV0 (by nlinarith)]
  nlinarith

/-- The product law `⊗_n q_n` on the prefix space. -/
def prefixProductLaw (θ : ℝ) {E : ℕ → Type*} [∀ n, MeasurableSpace (E n)]
    (q : ∀ n, Measure (E n)) [∀ n, IsProbabilityMeasure (q n)] : Measure (PrefixSpace θ E) :=
  Measure.infinitePi q

instance {θ : ℝ} {E : ℕ → Type*} [∀ n, MeasurableSpace (E n)] (q : ∀ n, Measure (E n))
    [∀ n, IsProbabilityMeasure (q n)] : IsProbabilityMeasure (prefixProductLaw θ q) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi q))

/-- **Corollary 5.4 (RP.20).**  For product laws
`α(K_d) ≥ (1 - A^d - √(1 - A_{s,N}²))_+ / (2θ^N)` with `A_{s,N} = ∏_{n<N} a_n`. -/
theorem product_prefix_resolutionAmplification_ge {θ : ℝ} [Fact (0 < θ)] [Fact (θ < 1)]
    {E : ℕ → Type*} [∀ n, Fintype (E n)] [∀ n, Nonempty (E n)] [∀ n, TopologicalSpace (E n)]
    [∀ n, DiscreteTopology (E n)] [∀ n, MeasurableSpace (E n)] [∀ n, BorelSpace (E n)]
    [∀ n, MeasurableSingletonClass (E n)]
    (q₀ q₁ : ∀ n, Measure (E n)) [∀ n, IsProbabilityMeasure (q₀ n)]
    [∀ n, IsProbabilityMeasure (q₁ n)] {Y : Type*} [Fintype Y] [MetricSpace Y]
    [MeasurableSpace Y] [MeasurableSingletonClass Y] (hsep : ∀ y y' : Y, y ≠ y' → 1 ≤ dist y y')
    (p₀ p₁ : Measure Y) [IsProbabilityMeasure p₀] [IsProbabilityMeasure p₁] {d : ℕ}
    (K : ProbabilityTheory.Kernel (PrefixSpace θ E) (Fin d → Y))
    [ProbabilityTheory.IsMarkovKernel K]
    (h₀ : IsExactFormation (prefixProductLaw θ q₀) K p₀)
    (h₁ : IsExactFormation (prefixProductLaw θ q₁) K p₁)
    {B : Set (Fin d → Y)} (hNP : IsNeymanPearson p₀ p₁ B) (N : ℕ) :
    ENNReal.ofReal ((1 - hellingerAffinity p₀ p₁ ^ d
        - Real.sqrt (1 - (∏ n ∈ Finset.range N, hellingerAffinity (q₀ n) (q₁ n)) ^ 2))
          / (2 * θ ^ N))
      ≤ resolutionAmplification K := by
  classical
  have h := prefix_resolutionAmplification_ge (prefixProductLaw θ q₀) (prefixProductLaw θ q₁)
    hsep p₀ p₁ K h₀ h₁ hNP N
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) h
  have hθN : 0 < θ ^ N := pow_pos Fact.out N
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have hmap : ∀ (q : ∀ n, Measure (E n)) [∀ n, IsProbabilityMeasure (q n)],
      (prefixProductLaw θ q).map (prefixObserver N)
        = Measure.pi fun i : Finset.range N => q i := by
    intro q _
    exact Measure.infinitePi_map_restrict q
  simp only [hmap q₀, hmap q₁]
  have hTVd := one_sub_hellingerAffinity_pow_le p₀ p₁ d
  have hTVN := measurableHahnTV_le_sqrt (Measure.pi fun i : Finset.range N => q₀ i)
    (Measure.pi fun i : Finset.range N => q₁ i)
  rw [hellingerAffinity_pi_dep, Finset.prod_coe_sort (Finset.range N)
    (fun n => hellingerAffinity (q₀ n) (q₁ n))] at hTVN
  linarith

end Product

end GaloisForLFunctions.HTGeometry
