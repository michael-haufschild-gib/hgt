import Mathlib

/-!
# Laurent coefficients of a meromorphic function at a point

For a function `f` meromorphic at `a`, some power `t ^ k` clears the pole, so `t ↦ t ^ k * f (a + t)`
is analytic at the origin and its Taylor coefficients are the Laurent coefficients of `f`, shifted
by `k`.  Increasing `k` shifts the Taylor index by the same amount, so the resulting family of
numbers is independent of `k`; `laurentCoeff` therefore takes the eventual value along `k → ∞`,
which needs no choice of clearing exponent.

* `taylorCoeffZero`, `laurentShift`, `laurentCoeff` — the definitions.
* `taylorCoeffZero_pow_mul` — multiplying by `t ^ j` shifts Taylor indices by `j`; the one-shot
  Leibniz computation behind the `k`-independence.
* `laurentCoeff_eq_taylorCoeffZero` — evaluation of `laurentCoeff` through any admissible `k`.
* `laurentCoeff_sum` — `ℂ`-linearity on finite families of functions meromorphic at `a`.
* `eventuallyEq_zero_nhdsNE_iff_forall_laurentCoeff_eq_zero` — the Laurent coefficients vanish
  exactly when the function vanishes on a punctured neighbourhood: the Laurent transform is
  injective on germs of meromorphic functions.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology
open scoped BigOperators

/-- The `m`-th Taylor coefficient at the origin. -/
noncomputable def taylorCoeffZero (g : ℂ → ℂ) (m : ℕ) : ℂ :=
  iteratedDeriv m g 0 / (m.factorial : ℂ)

/-- The `k`-fold clearing shift `t ↦ t ^ k * f (a + t)` of `f` at `a`. -/
noncomputable def laurentShift (f : ℂ → ℂ) (a : ℂ) (k : ℕ) : ℂ → ℂ :=
  fun t => t ^ k * f (a + t)

/-- The `ℓ`-th Laurent coefficient of `f` at `a`, read off as the eventual value of the shifted
Taylor coefficients of the clearing shifts. -/
noncomputable def laurentCoeff (f : ℂ → ℂ) (a : ℂ) (ℓ : ℤ) : ℂ :=
  limUnder atTop fun k : ℕ => taylorCoeffZero (laurentShift f a k) (ℓ + k).toNat

theorem laurentShift_add (f : ℂ → ℂ) (a : ℂ) (k j : ℕ) :
    laurentShift f a (k + j) = fun t => t ^ j * laurentShift f a k t := by
  funext t
  simp only [laurentShift, pow_add]
  ring

@[simp]
theorem laurentShift_zero_of_ne_zero (f : ℂ → ℂ) (a : ℂ) {k : ℕ} (hk : k ≠ 0) :
    laurentShift f a k 0 = 0 := by
  simp [laurentShift, zero_pow hk]

/-! ### The Taylor shift identity -/

/-- **Multiplying by `t ^ j` shifts Taylor indices by `j`.**  One application of the Leibniz rule:
all derivatives of `t ^ j` at the origin vanish except the `j`-th. -/
theorem taylorCoeffZero_pow_mul {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (j m : ℕ) :
    taylorCoeffZero (fun t => t ^ j * g t) m
      = if j ≤ m then taylorCoeffZero g (m - j) else 0 := by
  have hpow : AnalyticAt ℂ (fun t : ℂ => t ^ j) 0 := by fun_prop
  have hd : iteratedDeriv m (fun t : ℂ => t ^ j * g t) 0
      = ∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℂ) * iteratedDeriv i (fun t : ℂ => t ^ j) 0
            * iteratedDeriv (m - i) g 0 := by
    have hL := iteratedDeriv_mul (n := m) (x := (0 : ℂ))
      (f := fun t : ℂ => t ^ j) (g := g) hpow.contDiffAt hg.contDiffAt
    simpa [Pi.mul_def] using hL
  have hterm : ∀ i : ℕ, iteratedDeriv i (fun t : ℂ => t ^ j) 0
      = ((if i = j then j.factorial else 0 : ℕ) : ℂ) := fun i => iteratedDeriv_fun_pow_zero
  have hfac : ∀ p : ℕ, ((p.factorial : ℂ)) ≠ 0 := fun p =>
    Nat.cast_ne_zero.mpr p.factorial_ne_zero
  by_cases h : j ≤ m
  · rw [if_pos h, taylorCoeffZero, taylorCoeffZero, hd,
      Finset.sum_eq_single j (fun i _ hi => by simp [hterm i, hi])
        (fun hj => absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le h)) hj)]
    rw [hterm j, if_pos rfl]
    have hc : ((m.choose j : ℂ)) * ((j.factorial : ℂ)) * (((m - j).factorial : ℂ))
        = ((m.factorial : ℂ)) := by
      exact_mod_cast congrArg (Nat.cast (R := ℂ)) (Nat.choose_mul_factorial_mul_factorial h)
    rw [div_eq_div_iff (hfac m) (hfac (m - j))]
    linear_combination (iteratedDeriv (m - j) g 0) * hc
  · rw [if_neg h, taylorCoeffZero, hd]
    rw [Finset.sum_eq_zero]
    · simp
    · intro i hi
      have hij : i ≠ j := by
        have := Finset.mem_range.mp hi
        omega
      simp [hterm i, hij]

/-! ### Clearing exponents -/

/-- Analyticity of a clearing shift is inherited by every larger clearing exponent. -/
theorem analyticAt_laurentShift_add {f : ℂ → ℂ} {a : ℂ} {k : ℕ}
    (hk : AnalyticAt ℂ (laurentShift f a k) 0) (j : ℕ) :
    AnalyticAt ℂ (laurentShift f a (k + j)) 0 := by
  rw [laurentShift_add]
  exact (by fun_prop : AnalyticAt ℂ (fun t : ℂ => t ^ j) 0).mul hk

theorem analyticAt_laurentShift_of_le {f : ℂ → ℂ} {a : ℂ} {k k' : ℕ}
    (hk : AnalyticAt ℂ (laurentShift f a k) 0) (hkk' : k ≤ k') :
    AnalyticAt ℂ (laurentShift f a k') 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkk'
  exact analyticAt_laurentShift_add hk j

/-- Meromorphy at `a` is exactly the existence of a clearing exponent. -/
theorem meromorphicAt_iff_exists_analyticAt_laurentShift (f : ℂ → ℂ) (a : ℂ) :
    MeromorphicAt f a ↔ ∃ k : ℕ, AnalyticAt ℂ (laurentShift f a k) 0 := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hadd : AnalyticAt ℂ (fun t : ℂ => a + t) 0 := by fun_prop
    have hn' : AnalyticAt ℂ (fun z : ℂ => (z - a) ^ n • f z) ((fun t : ℂ => a + t) 0) := by
      simpa using hn
    refine (AnalyticAt.comp (g := fun z : ℂ => (z - a) ^ n • f z)
      (f := fun t : ℂ => a + t) (x := (0 : ℂ)) hn' hadd).congr ?_
    filter_upwards with t
    simp [laurentShift, Function.comp]
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hsub : AnalyticAt ℂ (fun z : ℂ => z - a) a := by fun_prop
    have hk' : AnalyticAt ℂ (laurentShift f a k) ((fun z : ℂ => z - a) a) := by
      simpa using hk
    refine (AnalyticAt.comp (g := laurentShift f a k)
      (f := fun z : ℂ => z - a) (x := a) hk' hsub).congr ?_
    filter_upwards with z
    simp [laurentShift, Function.comp]

/-- Every function meromorphic at `a` has clearing exponents beyond any given bound. -/
theorem exists_analyticAt_laurentShift_ge {f : ℂ → ℂ} {a : ℂ} (hf : MeromorphicAt f a) (N : ℕ) :
    ∃ k : ℕ, N ≤ k ∧ AnalyticAt ℂ (laurentShift f a k) 0 := by
  obtain ⟨k, hk⟩ := (meromorphicAt_iff_exists_analyticAt_laurentShift f a).mp hf
  exact ⟨max N k, le_max_left _ _, analyticAt_laurentShift_of_le hk (le_max_right _ _)⟩

/-- A finite family of functions meromorphic at `a` has a common clearing exponent beyond any given
bound. -/
theorem exists_common_analyticAt_laurentShift {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (a : ℂ)
    (hF : ∀ i ∈ s, MeromorphicAt (F i) a) (N : ℕ) :
    ∃ k : ℕ, N ≤ k ∧ ∀ i ∈ s, AnalyticAt ℂ (laurentShift (F i) a k) 0 := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨N, le_rfl, by simp⟩
  | insert i s hi IH =>
      obtain ⟨k, hkN, hk⟩ := IH (fun j hj => hF j (Finset.mem_insert_of_mem hj))
      obtain ⟨k', hk'k, hk'⟩ :=
        exists_analyticAt_laurentShift_ge (hF i (Finset.mem_insert_self i s)) k
      refine ⟨k', hkN.trans hk'k, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hk'
      · exact analyticAt_laurentShift_of_le (hk j hj) hk'k

/-! ### Evaluation and linearity -/

/-- **Evaluation of a Laurent coefficient through any admissible clearing exponent.** -/
theorem laurentCoeff_eq_taylorCoeffZero {f : ℂ → ℂ} {a : ℂ} {k : ℕ} {ℓ : ℤ}
    (hk : AnalyticAt ℂ (laurentShift f a k) 0) (hℓ : 0 ≤ ℓ + k) :
    laurentCoeff f a ℓ = taylorCoeffZero (laurentShift f a k) (ℓ + k).toNat := by
  have hstab : ∀ j : ℕ,
      taylorCoeffZero (laurentShift f a (k + j)) (ℓ + (k + j : ℕ)).toNat
        = taylorCoeffZero (laurentShift f a k) (ℓ + k).toNat := by
    intro j
    rw [laurentShift_add, taylorCoeffZero_pow_mul hk]
    have hidx : (ℓ + ((k + j : ℕ) : ℤ)).toNat = (ℓ + k).toNat + j := by
      push_cast
      omega
    rw [hidx, if_pos (Nat.le_add_left j _)]
    congr 1
    omega
  have htend : Tendsto (fun k' : ℕ => taylorCoeffZero (laurentShift f a k') (ℓ + k').toNat)
      atTop (𝓝 (taylorCoeffZero (laurentShift f a k) (ℓ + k).toNat)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop k] with k' hk'
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk'
    exact (hstab j).symm
  exact htend.limUnder_eq

/-- The Taylor coefficients at the origin are `ℂ`-linear on finite families of functions analytic at
the origin. -/
theorem taylorCoeffZero_sum {ι : Type*} (s : Finset ι) (G : ι → ℂ → ℂ) (c : ι → ℂ) (m : ℕ)
    (hG : ∀ i ∈ s, AnalyticAt ℂ (G i) 0) :
    taylorCoeffZero (fun t => ∑ i ∈ s, c i * G i t) m = ∑ i ∈ s, c i * taylorCoeffZero (G i) m := by
  have hd : iteratedDeriv m (fun t : ℂ => ∑ i ∈ s, c i * G i t) 0
      = ∑ i ∈ s, c i * iteratedDeriv m (G i) 0 := by
    have hmul : ∀ i ∈ s, ContDiffAt ℂ (m : ℕ) (fun t : ℂ => c i * G i t) 0 :=
      fun i hi => (analyticAt_const.mul (hG i hi)).contDiffAt
    rw [iteratedDeriv_fun_sum hmul]
    exact Finset.sum_congr rfl fun i hi => iteratedDeriv_const_mul _ (hG i hi).contDiffAt
  simp only [taylorCoeffZero, hd, Finset.sum_div, mul_div_assoc]

/-- **`ℂ`-linearity of the Laurent coefficients.** -/
theorem laurentCoeff_sum {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (c : ι → ℂ) (a : ℂ) (ℓ : ℤ)
    (hF : ∀ i ∈ s, MeromorphicAt (F i) a) :
    laurentCoeff (fun z => ∑ i ∈ s, c i * F i z) a ℓ = ∑ i ∈ s, c i * laurentCoeff (F i) a ℓ := by
  obtain ⟨k, hkN, hk⟩ := exists_common_analyticAt_laurentShift s F a hF ℓ.natAbs
  have hℓ : 0 ≤ ℓ + (k : ℤ) := by
    have : (ℓ.natAbs : ℤ) ≤ (k : ℤ) := by exact_mod_cast hkN
    omega
  have hshift : laurentShift (fun z => ∑ i ∈ s, c i * F i z) a k
      = fun t => ∑ i ∈ s, c i * laurentShift (F i) a k t := by
    funext t
    simp only [laurentShift, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hanalytic : AnalyticAt ℂ (laurentShift (fun z => ∑ i ∈ s, c i * F i z) a k) 0 := by
    rw [hshift]
    have := Finset.analyticAt_sum (f := fun i => fun t : ℂ => c i * laurentShift (F i) a k t)
      (c := (0 : ℂ)) s (fun i hi => analyticAt_const.mul (hk i hi))
    refine this.congr ?_
    filter_upwards with t
    simp
  rw [laurentCoeff_eq_taylorCoeffZero hanalytic hℓ, hshift,
    taylorCoeffZero_sum s _ c _ (fun i hi => hk i hi)]
  exact Finset.sum_congr rfl fun i hi => by
    rw [laurentCoeff_eq_taylorCoeffZero (hk i hi) hℓ]

/-! ### Injectivity of the Laurent transform -/

theorem tendsto_const_add_nhdsNE (a : ℂ) :
    Tendsto (fun t : ℂ => a + t) (𝓝[≠] (0 : ℂ)) (𝓝[≠] a) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hc : Tendsto (fun t : ℂ => a + t) (𝓝 (0 : ℂ)) (𝓝 (a + 0)) :=
      (continuous_const.add continuous_id).continuousAt
    simpa using hc.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht ⊢
    intro h
    exact ht (by linear_combination h)

theorem tendsto_sub_const_nhdsNE (a : ℂ) :
    Tendsto (fun z : ℂ => z - a) (𝓝[≠] a) (𝓝[≠] (0 : ℂ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hc : Tendsto (fun z : ℂ => z - a) (𝓝 a) (𝓝 (a - a)) :=
      (continuous_id.sub continuous_const).continuousAt
    simpa using hc.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, sub_eq_zero]
    exact hz

/-- Vanishing near `a` is the same as vanishing of a clearing shift near the origin. -/
theorem eventuallyEq_zero_nhdsNE_iff_laurentShift (f : ℂ → ℂ) (a : ℂ) {k : ℕ} (hk : k ≠ 0) :
    f =ᶠ[𝓝[≠] a] 0 ↔ laurentShift f a k =ᶠ[𝓝[≠] (0 : ℂ)] 0 := by
  constructor
  · intro h
    have h' := (tendsto_const_add_nhdsNE a).eventually h
    filter_upwards [h'] with t ht
    simp [laurentShift, ht]
  · intro h
    have h' := (tendsto_sub_const_nhdsNE a).eventually h
    filter_upwards [h', self_mem_nhdsWithin] with z hz hzne
    have hsub : z - a ≠ 0 := sub_ne_zero_of_ne hzne
    have hz' : (z - a) ^ k * f (a + (z - a)) = 0 := hz
    rw [show a + (z - a) = z by ring] at hz'
    rcases mul_eq_zero.mp hz' with h1 | h2
    · exact absurd (pow_eq_zero_iff hk |>.mp h1) hsub
    · simpa using h2

/-- **Injectivity of the Laurent transform.**  A function meromorphic at `a` has vanishing Laurent
coefficients exactly when it vanishes on a punctured neighbourhood of `a`. -/
theorem eventuallyEq_zero_nhdsNE_iff_forall_laurentCoeff_eq_zero {f : ℂ → ℂ} {a : ℂ}
    (hf : MeromorphicAt f a) :
    f =ᶠ[𝓝[≠] a] 0 ↔ ∀ ℓ : ℤ, laurentCoeff f a ℓ = 0 := by
  constructor
  · intro h ℓ
    obtain ⟨k, hk1, hk⟩ : ∃ k : ℕ, k ≠ 0 ∧ 0 ≤ ℓ + (k : ℤ) := by
      refine ⟨ℓ.natAbs + 1, Nat.succ_ne_zero _, ?_⟩
      have h1 : -ℓ ≤ |ℓ| := neg_le_abs ℓ
      push_cast
      linarith
    have hshift : laurentShift f a k =ᶠ[𝓝 (0 : ℂ)] 0 := by
      have hne : laurentShift f a k =ᶠ[𝓝[≠] (0 : ℂ)] 0 :=
        (eventuallyEq_zero_nhdsNE_iff_laurentShift f a hk1).mp h
      rw [Filter.EventuallyEq, ← nhdsNE_sup_pure (0 : ℂ), eventually_sup]
      exact ⟨hne, by simp [laurentShift_zero_of_ne_zero f a hk1]⟩
    have hanalytic : AnalyticAt ℂ (laurentShift f a k) 0 :=
      analyticAt_const.congr hshift.symm
    rw [laurentCoeff_eq_taylorCoeffZero hanalytic hk, taylorCoeffZero,
      Filter.EventuallyEq.iteratedDeriv_eq _ hshift]
    simp
  · intro h
    obtain ⟨k, hk1, hk⟩ := exists_analyticAt_laurentShift_ge hf 1
    have hk1' : k ≠ 0 := by omega
    have hderiv : ∀ m : ℕ, iteratedDeriv m (laurentShift f a k) 0 = 0 := by
      intro m
      have hℓ : ((m : ℤ) - k) + (k : ℤ) = (m : ℤ) := by ring
      have := h ((m : ℤ) - k)
      rw [laurentCoeff_eq_taylorCoeffZero hk (by omega), hℓ] at this
      simp only [Int.toNat_natCast, taylorCoeffZero, div_eq_zero_iff] at this
      rcases this with h1 | h2
      · exact h1
      · exact absurd h2 (Nat.cast_ne_zero.mpr m.factorial_ne_zero)
    have htop : analyticOrderAt (laurentShift f a k) 0 = ⊤ := by
      by_contra hcon
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hcon
      have hle : ((n + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (laurentShift f a k) 0 :=
        (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hk).mpr fun i _ => hderiv i
      rw [← hn] at hle
      exact absurd hle (by exact_mod_cast Nat.not_succ_le_self n)
    have hshift : laurentShift f a k =ᶠ[𝓝 (0 : ℂ)] 0 := analyticOrderAt_eq_top.mp htop
    refine (eventuallyEq_zero_nhdsNE_iff_laurentShift f a hk1').mpr ?_
    exact hshift.filter_mono nhdsWithin_le_nhds

end GaloisForLFunctions.HTGeometry
