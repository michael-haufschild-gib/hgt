import GaloisForLFunctions.HTGeometry.MeromorphicLaurentCoefficient

/-!
# Translation, congruence and local finiteness of Laurent coefficients

Three further properties of the Laurent transform of a meromorphic germ.

* it is equivariant for translations of the argument;
* it only sees the punctured germ, so functions agreeing off the point have the same coefficients;
* a negative Laurent coefficient can be nonzero only at a pole, and the poles of a function
  meromorphic on the plane meet every closed ball in a finite set.

The last item is the analytic input of every orbital residue argument: a family of pairwise
distinct points inside one compact set can carry only finitely many nonzero principal-part
coefficients.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

/-! ### Translation equivariance -/

theorem laurentShift_comp_add (f : ℂ → ℂ) (a h : ℂ) (k : ℕ) :
    laurentShift (fun z => f (z + h)) a k = laurentShift f (a + h) k := by
  funext t
  simp only [laurentShift]
  ring_nf

/-- **The Laurent coefficients are translation equivariant.** -/
theorem laurentCoeff_comp_add (f : ℂ → ℂ) (a h : ℂ) (ℓ : ℤ) :
    laurentCoeff (fun z => f (z + h)) a ℓ = laurentCoeff f (a + h) ℓ := by
  simp only [laurentCoeff, laurentShift_comp_add]

/-! ### Dependence on the punctured germ only -/

theorem laurentShift_eventuallyEq_of_nhdsNE {f g : ℂ → ℂ} {a : ℂ} {k : ℕ} (hk : k ≠ 0)
    (h : f =ᶠ[𝓝[≠] a] g) :
    laurentShift f a k =ᶠ[𝓝 (0 : ℂ)] laurentShift g a k := by
  have hne : laurentShift f a k =ᶠ[𝓝[≠] (0 : ℂ)] laurentShift g a k := by
    have h' := (tendsto_const_add_nhdsNE a).eventually h
    filter_upwards [h'] with t ht
    simp [laurentShift, ht]
  rw [Filter.EventuallyEq, ← nhdsNE_sup_pure (0 : ℂ), eventually_sup]
  refine ⟨hne, ?_⟩
  simp [laurentShift_zero_of_ne_zero f a hk, laurentShift_zero_of_ne_zero g a hk]

/-- **The Laurent coefficients depend only on the punctured germ.** -/
theorem laurentCoeff_congr {f g : ℂ → ℂ} {a : ℂ} (hf : MeromorphicAt f a)
    (h : f =ᶠ[𝓝[≠] a] g) (ℓ : ℤ) :
    laurentCoeff f a ℓ = laurentCoeff g a ℓ := by
  obtain ⟨k, hk1, hk⟩ := exists_analyticAt_laurentShift_ge hf (ℓ.natAbs + 1)
  have hkne : k ≠ 0 := by omega
  have heq := laurentShift_eventuallyEq_of_nhdsNE (f := f) (g := g) (a := a) hkne h
  have hkg : AnalyticAt ℂ (laurentShift g a k) 0 := hk.congr heq
  have hℓ : 0 ≤ ℓ + (k : ℤ) := by omega
  rw [laurentCoeff_eq_taylorCoeffZero hk hℓ, laurentCoeff_eq_taylorCoeffZero hkg hℓ,
    taylorCoeffZero, taylorCoeffZero, Filter.EventuallyEq.iteratedDeriv_eq _ heq]

/-! ### Negative coefficients live at poles -/

/-- An analytic germ has no negative Laurent coefficient. -/
theorem laurentCoeff_eq_zero_of_analyticAt {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a)
    {ℓ : ℤ} (hℓ : ℓ < 0) : laurentCoeff f a ℓ = 0 := by
  set k : ℕ := ℓ.natAbs with hkdef
  have hk0 : k ≠ 0 := by
    simp only [hkdef, ne_eq, Int.natAbs_eq_zero]
    omega
  have hg : AnalyticAt ℂ (fun t : ℂ => f (a + t)) 0 := by
    have hadd : AnalyticAt ℂ (fun t : ℂ => a + t) 0 := by fun_prop
    have hf' : AnalyticAt ℂ f ((fun t : ℂ => a + t) 0) := by simpa using hf
    exact AnalyticAt.comp hf' hadd
  have hshift : laurentShift f a k = fun t : ℂ => t ^ k * (fun t : ℂ => f (a + t)) t := rfl
  have hanalytic : AnalyticAt ℂ (laurentShift f a k) 0 := by
    rw [hshift]
    exact (by fun_prop : AnalyticAt ℂ (fun t : ℂ => t ^ k) 0).mul hg
  have hsum : ℓ + (k : ℤ) = 0 := by
    simp only [hkdef]
    omega
  rw [laurentCoeff_eq_taylorCoeffZero hanalytic (by omega), hsum, hshift,
    taylorCoeffZero_pow_mul hg k (0 : ℤ).toNat]
  simp only [Int.toNat_zero]
  rw [if_neg (by omega)]

/-- A germ of nonnegative order has no negative Laurent coefficient. -/
theorem laurentCoeff_eq_zero_of_meromorphicOrderAt_nonneg {f : ℂ → ℂ} {a : ℂ}
    (hf : MeromorphicAt f a) (hord : 0 ≤ meromorphicOrderAt f a) {ℓ : ℤ} (hℓ : ℓ < 0) :
    laurentCoeff f a ℓ = 0 := by
  obtain ⟨g, hg, hfg⟩ := hf.meromorphicOrderAt_nonneg_iff.mp hord
  rw [laurentCoeff_congr hf hfg ℓ]
  exact laurentCoeff_eq_zero_of_analyticAt hg hℓ

/-- **A nonzero negative Laurent coefficient forces a pole.** -/
theorem meromorphicOrderAt_neg_of_laurentCoeff_ne_zero {f : ℂ → ℂ} {a : ℂ}
    (hf : MeromorphicAt f a) {ℓ : ℤ} (hℓ : ℓ < 0) (hne : laurentCoeff f a ℓ ≠ 0) :
    meromorphicOrderAt f a < 0 := by
  by_contra hcon
  exact hne (laurentCoeff_eq_zero_of_meromorphicOrderAt_nonneg hf (not_lt.mp hcon) hℓ)

/-- A pole is a point of nonzero divisor. -/
theorem divisor_ne_zero_of_laurentCoeff_ne_zero {f : ℂ → ℂ} {U : Set ℂ} (hf : MeromorphicOn f U)
    {a : ℂ} (ha : a ∈ U) {ℓ : ℤ} (hℓ : ℓ < 0) (hne : laurentCoeff f a ℓ ≠ 0) :
    MeromorphicOn.divisor f U a ≠ 0 := by
  have hlt : meromorphicOrderAt f a < 0 :=
    meromorphicOrderAt_neg_of_laurentCoeff_ne_zero (hf a ha) hℓ hne
  rw [MeromorphicOn.divisor_apply hf ha]
  intro hzero
  have htop : meromorphicOrderAt f a ≠ ⊤ := by
    intro htop
    rw [htop] at hlt
    exact absurd hlt (by simp)
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp htop
  rw [← hn] at hzero hlt
  simp only [WithTop.untop₀_coe] at hzero
  rw [hzero] at hlt
  exact absurd hlt (by simp)

/-! ### Local finiteness of the principal-part support -/

/-- **Only finitely many points of a ball carry a nonzero principal-part coefficient.** -/
theorem finite_setOf_laurentCoeff_ne_zero_ball {f : ℂ → ℂ} (hf : MeromorphicOn f Set.univ)
    {ℓ : ℤ} (hℓ : ℓ < 0) (c : ℂ) (R : ℝ) :
    {a : ℂ | a ∈ Metric.ball c R ∧ laurentCoeff f a ℓ ≠ 0}.Finite := by
  have hball : MeromorphicOn f (Metric.closedBall c R) := fun z _ => hf z (Set.mem_univ z)
  refine (MeromorphicOn.divisor_ball_support_finite hball).subset ?_
  rintro a ⟨hmem, hne⟩
  exact divisor_ne_zero_of_laurentCoeff_ne_zero
    (fun z hz => hf z (Set.mem_univ z)) hmem hℓ hne

/-- **A set of points inside a bounded region carrying nonzero principal-part coefficients is
finite.** -/
theorem finite_setOf_laurentCoeff_ne_zero_of_bounded {f : ℂ → ℂ} (hf : MeromorphicOn f Set.univ)
    {ℓ : ℤ} (hℓ : ℓ < 0) {S : Set ℂ} (hS : Bornology.IsBounded S) :
    {a : ℂ | a ∈ S ∧ laurentCoeff f a ℓ ≠ 0}.Finite := by
  obtain ⟨R, hR⟩ := hS.subset_ball (0 : ℂ)
  refine (finite_setOf_laurentCoeff_ne_zero_ball hf hℓ 0 R).subset ?_
  rintro a ⟨hmem, hne⟩
  exact ⟨hR hmem, hne⟩


/-! ### Meromorphy and linearity in the translated variable -/

theorem meromorphicAt_comp_add {f : ℂ → ℂ} {a h : ℂ} :
    MeromorphicAt (fun z => f (z + h)) a ↔ MeromorphicAt f (a + h) := by
  rw [meromorphicAt_iff_exists_analyticAt_laurentShift,
    meromorphicAt_iff_exists_analyticAt_laurentShift]
  simp only [laurentShift_comp_add]

/-- Additivity of the Laurent coefficients. -/
theorem laurentCoeff_add {f g : ℂ → ℂ} {a : ℂ} (hf : MeromorphicAt f a) (hg : MeromorphicAt g a)
    (ℓ : ℤ) :
    laurentCoeff (fun z => f z + g z) a ℓ = laurentCoeff f a ℓ + laurentCoeff g a ℓ := by
  have h := laurentCoeff_sum (Finset.univ : Finset (Fin 2)) ![f, g] ![1, 1] a ℓ
    (by intro i _; fin_cases i <;> simpa using ‹_›)
  simpa [Fin.sum_univ_two] using h

/-- Subtractivity of the Laurent coefficients. -/
theorem laurentCoeff_sub {f g : ℂ → ℂ} {a : ℂ} (hf : MeromorphicAt f a) (hg : MeromorphicAt g a)
    (ℓ : ℤ) :
    laurentCoeff (fun z => f z - g z) a ℓ = laurentCoeff f a ℓ - laurentCoeff g a ℓ := by
  have h := laurentCoeff_sum (Finset.univ : Finset (Fin 2)) ![f, g] ![1, -1] a ℓ
    (by intro i _; fin_cases i <;> simpa using ‹_›)
  simpa [Fin.sum_univ_two, sub_eq_add_neg] using h

/-- Adding a constant does not change a negative Laurent coefficient. -/
theorem laurentCoeff_add_const {f : ℂ → ℂ} {a : ℂ} (hf : MeromorphicAt f a) (Cst : ℂ)
    {ℓ : ℤ} (hℓ : ℓ < 0) :
    laurentCoeff (fun z => f z + Cst) a ℓ = laurentCoeff f a ℓ := by
  rw [laurentCoeff_add hf (analyticAt_const.meromorphicAt) ℓ,
    laurentCoeff_eq_zero_of_analyticAt (analyticAt_const (v := Cst)) hℓ, add_zero]

/-- **The difference quotient of a translation.**  The principal-part coefficients of
`z ↦ f (z + h) - f z` are the differences of the coefficients of `f` at the two translates. -/
theorem laurentCoeff_shiftDiff {f : ℂ → ℂ} (hf : MeromorphicOn f Set.univ) (h a : ℂ) (ℓ : ℤ) :
    laurentCoeff (fun z => f (z + h) - f z) a ℓ
      = laurentCoeff f (a + h) ℓ - laurentCoeff f a ℓ := by
  have hshift : MeromorphicAt (fun z => f (z + h)) a :=
    meromorphicAt_comp_add.mpr (hf (a + h) (Set.mem_univ _))
  rw [laurentCoeff_sub hshift (hf a (Set.mem_univ a)) ℓ, laurentCoeff_comp_add]

/-- A period of the coefficient function is a period for every integer multiple. -/
theorem laurentCoeff_add_zsmul_of_period {f : ℂ → ℂ} {ℓ : ℤ} {h : ℂ}
    (hp : ∀ z : ℂ, laurentCoeff f (z + h) ℓ = laurentCoeff f z ℓ) (z : ℂ) (n : ℤ) :
    laurentCoeff f (z + (n : ℂ) * h) ℓ = laurentCoeff f z ℓ := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
      have hstep : z + (((k : ℤ) + 1 : ℤ) : ℂ) * h = (z + ((k : ℤ) : ℂ) * h) + h := by
        push_cast; ring
      rw [hstep, hp, ih]
  | pred k ih =>
      have hstep : (z + ((-(k : ℤ) - 1 : ℤ) : ℂ) * h) + h = z + ((-(k : ℤ) : ℤ) : ℂ) * h := by
        push_cast; ring
      have hh := hp (z + ((-(k : ℤ) - 1 : ℤ) : ℂ) * h)
      rw [hstep, ih] at hh
      exact hh.symm


/-! ### Translation of the meromorphic order -/

theorem tendsto_add_const_nhdsNE (a h : ℂ) :
    Filter.Tendsto (fun z : ℂ => z + h) (𝓝[≠] a) (𝓝[≠] (a + h)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have hc : Filter.Tendsto (fun z : ℂ => z + h) (𝓝 a) (𝓝 (a + h)) :=
      (continuous_id.add continuous_const).continuousAt
    exact hc.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
    intro hcon
    exact hz (by linear_combination hcon)

/-- **The meromorphic order is translation equivariant.** -/
theorem meromorphicOrderAt_comp_add (f : ℂ → ℂ) (a h : ℂ) :
    meromorphicOrderAt (fun z => f (z + h)) a = meromorphicOrderAt f (a + h) := by
  by_cases hf : MeromorphicAt f (a + h)
  swap
  · rw [meromorphicOrderAt_of_not_meromorphicAt hf,
      meromorphicOrderAt_of_not_meromorphicAt (fun hc => hf (meromorphicAt_comp_add.mp hc))]
  have hfa : MeromorphicAt (fun z => f (z + h)) a := meromorphicAt_comp_add.mpr hf
  rcases eq_or_ne (meromorphicOrderAt f (a + h)) ⊤ with htop | hne
  · rw [htop, meromorphicOrderAt_eq_top_iff]
    rw [meromorphicOrderAt_eq_top_iff] at htop
    filter_upwards [(tendsto_add_const_nhdsNE a h).eventually htop] with z hz
    simpa using hz
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
    have hord : meromorphicOrderAt f (a + h) = (n : ℤ) := hn.symm
    rw [hord, meromorphicOrderAt_eq_int_iff hfa]
    obtain ⟨g, hg, hga, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hord
    refine ⟨fun z => g (z + h), ?_, ?_, ?_⟩
    · exact AnalyticAt.comp (g := g) (f := fun z : ℂ => z + h) (x := a) (by simpa using hg)
        (by fun_prop)
    · simpa using hga
    · filter_upwards [(tendsto_add_const_nhdsNE a h).eventually hfg] with z hz
      rw [show z + h - (a + h) = z - a from by ring] at hz
      exact hz

end GaloisForLFunctions.HTGeometry
