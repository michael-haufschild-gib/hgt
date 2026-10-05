import GaloisForLFunctions.HTGeometry.CompactMonoidMeasureAlgebra
import GaloisForLFunctions.HTGeometry.BanachTriangularExponential

/-!
# Weak-* continuity of formations in the measure algebra

Let `K` be a compact metrizable commutative monoid and `M(K) = C(K, ℂ)*` its measure algebra.

* **Diagonal extraction.**  In a sequentially compact set, every array `x_{n,j}` has a single
  subsequence along which every column converges (Cantor's diagonal argument).
* **Positive balls.**  A positive element has norm `Φ(1)`; positivity passes to weak-* limits and to
  products; the positive elements of norm `≤ C` are weak-* sequentially compact (Banach–Alaoglu,
  `C(K)` separable).
* **Uniform weak-* convergence.**  If `F_n(z) → F(z)` against every test function uniformly for
  `z ∈ D`, with `‖F_n(z)‖, ‖F(z)‖ ≤ B`, then the convergence is uniform over `D × S` for every compact
  set `S` of test functions (finite nets).  Writing
  `(Φ Ψ)(f) = Φ(x ↦ Ψ(y ↦ f(xy)))`, whose inner test functions form the compact set of translates
  of `f`, this makes products of such families converge uniformly on `D`; finite products and the
  convolution exponential `exp(z X_n) → exp(z X)` follow.
-/

open Filter Topology NormedSpace MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry.FormationDust

/-! ### Cantor diagonal extraction -/

section Diagonal

variable {X : Type*} [TopologicalSpace X] {s : Set X}

/-- The nested extractions `ψ_{k+1} = ψ_k ∘ θ_k`, `θ_k` making column `k` converge. -/
def diagSeq (hs : IsSeqCompact s) (x : ℕ → ℕ → X) (hx : ∀ n j, x n j ∈ s) : ℕ → ℕ → ℕ
  | 0 => id
  | k + 1 => diagSeq hs x hx k ∘ Classical.choose
      (Classical.choose_spec (hs (x := fun n => x (diagSeq hs x hx k n) k) fun _ => hx _ _)).2

theorem diagSeq_succ (hs : IsSeqCompact s) (x : ℕ → ℕ → X) (hx : ∀ n j, x n j ∈ s) (k : ℕ) :
    ∃ θ : ℕ → ℕ, StrictMono θ ∧ diagSeq hs x hx (k + 1) = diagSeq hs x hx k ∘ θ ∧
      ∃ a ∈ s, Tendsto (fun n => x (diagSeq hs x hx (k + 1) n) k) atTop (𝓝 a) := by
  set h := hs (x := fun n => x (diagSeq hs x hx k n) k) fun n => hx _ _
  have ha := Classical.choose_spec h
  have hθ := Classical.choose_spec ha.2
  exact ⟨_, hθ.1, rfl, _, ha.1, hθ.2⟩

theorem diagSeq_strictMono (hs : IsSeqCompact s) (x : ℕ → ℕ → X) (hx : ∀ n j, x n j ∈ s) :
    ∀ k, StrictMono (diagSeq hs x hx k)
  | 0 => strictMono_id
  | k + 1 => by
    obtain ⟨θ, hθ, he, -⟩ := diagSeq_succ hs x hx k
    rw [he]
    exact (diagSeq_strictMono hs x hx k).comp hθ

theorem diagSeq_factor (hs : IsSeqCompact s) (x : ℕ → ℕ → X) (hx : ∀ n j, x n j ∈ s) {k m : ℕ}
    (hkm : k ≤ m) : ∃ τ : ℕ → ℕ, StrictMono τ ∧ diagSeq hs x hx m = diagSeq hs x hx k ∘ τ := by
  induction m, hkm using Nat.le_induction with
  | base => exact ⟨id, strictMono_id, rfl⟩
  | succ m _ ih =>
    obtain ⟨τ, hτ, he⟩ := ih
    obtain ⟨θ, hθ, he', -⟩ := diagSeq_succ hs x hx m
    exact ⟨τ ∘ θ, hτ.comp hθ, by rw [he', he]; rfl⟩

/-- **Cantor's diagonal argument**: one subsequence makes every column converge in `s`. -/
theorem exists_diagonal_subseq (hs : IsSeqCompact s) (x : ℕ → ℕ → X) (hx : ∀ n j, x n j ∈ s) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j, ∃ a ∈ s, Tendsto (fun n => x (φ n) j) atTop (𝓝 a) := by
  refine ⟨fun n => diagSeq hs x hx n n, ?_, fun j => ?_⟩
  · refine strictMono_nat_of_lt_succ fun n => ?_
    obtain ⟨θ, hθ, he, -⟩ := diagSeq_succ hs x hx n
    show diagSeq hs x hx n n < diagSeq hs x hx (n + 1) (n + 1)
    rw [he]
    exact diagSeq_strictMono hs x hx n ((hθ.id_le (n + 1)).trans_lt' (Nat.lt_succ_self n))
  · obtain ⟨-, -, -, a, ha, hlim⟩ := diagSeq_succ hs x hx j
    refine ⟨a, ha, ?_⟩
    rw [tendsto_atTop'] at hlim ⊢
    intro U hU
    obtain ⟨M, hM⟩ := hlim U hU
    refine ⟨max M (j + 1), fun n hn => ?_⟩
    obtain ⟨τ, hτ, he⟩ := diagSeq_factor hs x hx (le_of_max_le_right hn)
    show x (diagSeq hs x hx n n) j ∈ U
    rw [he]
    exact hM _ ((le_of_max_le_left hn).trans (hτ.id_le n))

end Diagonal

/-! ### Uniform weak-* convergence of families -/

section Uniform

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

open MeasureAlgebra

/-- `F_n(z) → G(z)` against every test function, uniformly for `z ∈ D`. -/
def WeakUnifOn (F : ℕ → ℂ → MeasureAlgebra K) (G : ℂ → MeasureAlgebra K) (D : Set ℂ) : Prop :=
  ∀ f : C(K, ℂ), TendstoUniformlyOn (fun n z => F n z f) (fun z => G z f) atTop D

/-- Uniform weak-* convergence of bounded families is uniform over compact sets of test
functions. -/
theorem WeakUnifOn.uniform_compact {F : ℕ → ℂ → MeasureAlgebra K} {G : ℂ → MeasureAlgebra K}
    {D : Set ℂ} (h : WeakUnifOn F G D) {B : ℝ} (hF : ∀ n, ∀ z ∈ D, ‖F n z‖ ≤ B)
    (hG : ∀ z ∈ D, ‖G z‖ ≤ B) {S : Set C(K, ℂ)} (hS : IsCompact S) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ z ∈ D, ∀ g ∈ S, ‖F n z g - G z g‖ < ε := by
  intro ε hε
  set B' := max B 0 + 1
  have hB' : 0 < B' := by positivity
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.1 hS.totallyBounded (ε / (4 * B'))
    (by positivity)
  have hev : ∀ᶠ n in atTop, ∀ y ∈ t, ∀ z ∈ D, dist (G z y) (F n z y) < ε / 2 :=
    (eventually_all_finite ht).2 fun y _ => Metric.tendstoUniformlyOn_iff.1 (h y) (ε / 2)
      (by positivity)
  filter_upwards [hev] with n hn z hz g hg
  obtain ⟨y, hy, hgy⟩ := mem_iUnion₂.1 (hcover hg)
  rw [Metric.mem_ball, dist_eq_norm] at hgy
  have h1 : ‖F n z (g - y)‖ ≤ B' * (ε / (4 * B')) :=
    (le_opNorm _ _).trans (mul_le_mul ((hF n z hz).trans (by
      linarith [le_max_left B 0])) hgy.le (norm_nonneg _) hB'.le)
  have h2 : ‖G z (y - g)‖ ≤ B' * (ε / (4 * B')) :=
    (le_opNorm _ _).trans (mul_le_mul ((hG z hz).trans (by linarith [le_max_left B 0]))
      (by rw [norm_sub_rev]; exact hgy.le) (norm_nonneg _) hB'.le)
  have h3 := hn y hy z hz
  rw [dist_eq_norm, norm_sub_rev] at h3
  have he : B' * (ε / (4 * B')) = ε / 4 := by field_simp
  rw [he] at h1 h2
  calc ‖F n z g - G z g‖ = ‖F n z (g - y) + (F n z y - G z y) + G z (y - g)‖ := by
        rw [map_sub, map_sub]; ring_nf
    _ ≤ ‖F n z (g - y)‖ + ‖F n z y - G z y‖ + ‖G z (y - g)‖ := norm_add₃_le
    _ < ε := by linarith

end Uniform

/-! ### Positive elements -/

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K] [SecondCountableTopology K]
  [CommMonoid K] [ContinuousMul K] [MeasurableSpace K] [BorelSpace K]

open MeasureAlgebra

omit [SecondCountableTopology K] in
/-- A positive element of `M(K)` has norm equal to its mass `Φ(1)`. -/
theorem IsPositive.norm_eq {Φ : MeasureAlgebra K} (hΦ : IsPositive Φ) :
    ‖Φ‖ = (Φ 1).re := by
  haveI : Nonempty K := ⟨1⟩
  obtain ⟨μ, rfl⟩ := hΦ.exists_ofMeasure_eq
  rw [norm_ofMeasure, ofMeasure_apply]
  simp only [ContinuousMap.one_apply, integral_const, Complex.real_smul, mul_one,
    Complex.ofReal_re]
  rw [mass_eq_real]

omit [CompactSpace K] [T2Space K] [SecondCountableTopology K] [CommMonoid K] [ContinuousMul K]
  [MeasurableSpace K] [BorelSpace K] in
theorem isPositive_of_tendsto {Φ : ℕ → MeasureAlgebra K} {Ψ : MeasureAlgebra K}
    (hΦ : ∀ n, IsPositive (Φ n)) (h : ∀ f, Tendsto (fun n => Φ n f) atTop (𝓝 (Ψ f))) :
    IsPositive Ψ := fun f hf => by
  have hre := (Complex.continuous_re.tendsto _).comp (h (realToComplex f))
  have him := (Complex.continuous_im.tendsto _).comp (h (realToComplex f))
  refine ⟨tendsto_nhds_unique him (tendsto_const_nhds.congr fun n => ?_),
    ge_of_tendsto' hre fun n => ((hΦ n) f hf).2⟩
  exact ((hΦ n) f hf).1.symm

theorem IsPositive.mul {Φ Ψ : MeasureAlgebra K} (hΦ : IsPositive Φ) (hΨ : IsPositive Ψ) :
    IsPositive (Φ * Ψ) := by
  obtain ⟨μ, rfl⟩ := hΦ.exists_ofMeasure_eq
  obtain ⟨ν, rfl⟩ := hΨ.exists_ofMeasure_eq
  rw [← ofMeasure_measureConv]
  exact isPositive_ofMeasure _

omit [SecondCountableTopology K] [ContinuousMul K] in
theorem isPositive_one : IsPositive (1 : MeasureAlgebra K) := by
  rw [← ofMeasure_diracMeasure_one]
  exact isPositive_ofMeasure _

theorem IsPositive.smul {Φ : MeasureAlgebra K} (hΦ : IsPositive Φ) {c : ℝ} (hc : 0 ≤ c) :
    IsPositive ((c : ℂ) • Φ) := fun f hf => by
  refine ⟨?_, ?_⟩
  · rw [MeasureAlgebra.smul_apply, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      (hΦ f hf).1]
    ring
  rw [MeasureAlgebra.smul_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  exact mul_nonneg hc (hΦ f hf).2

omit [SecondCountableTopology K] in
/-- The mass functional `Φ ↦ Re Φ(1)` is additive on positive elements. -/
theorem IsPositive.norm_add {Φ Ψ : MeasureAlgebra K} (hΦ : IsPositive Φ) (hΨ : IsPositive Ψ) :
    ‖Φ + Ψ‖ = ‖Φ‖ + ‖Ψ‖ := by
  rw [IsPositive.norm_eq (hΦ.add hΨ), IsPositive.norm_eq hΦ, IsPositive.norm_eq hΨ,
    MeasureAlgebra.add_apply, Complex.add_re]

/-! ### Weak-* sequential compactness of the positive ball -/

omit [CommMonoid K] [ContinuousMul K] [MeasurableSpace K] [BorelSpace K] in
/-- The weak-* sequential compactness of the positive ball `{Φ ≥ 0, ‖Φ‖ ≤ C}`. -/
theorem isSeqCompact_positiveBall (C : ℝ) :
    IsSeqCompact {Λ : WeakDual ℂ C(K, ℂ) |
      IsPositive (ofDual (WeakDual.toStrongDual Λ) : MeasureAlgebra K) ∧
        ‖WeakDual.toStrongDual Λ‖ ≤ C} := by
  intro u hu
  have hball := WeakDual.isSeqCompact_closedBall ℂ C(K, ℂ) 0 C
  obtain ⟨a, ha, φ, hφ, hlim⟩ := hball (x := u) fun n => by
    simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right]
    exact (hu n).2
  refine ⟨a, ⟨?_, by simpa using ha⟩, φ, hφ, hlim⟩
  refine isPositive_of_tendsto (Φ := fun n => ofDual (WeakDual.toStrongDual (u (φ n))))
    (fun n => (hu (φ n)).1) fun f => ?_
  exact ((WeakDual.eval_continuous f).tendsto a).comp hlim

omit [MeasurableSpace K] [BorelSpace K] in
/-- **Diagonal extraction in the positive ball**: an array of positive elements of norm `≤ C`
has one subsequence along which every column converges weak-*. -/
theorem exists_diagonal_positive (C : ℝ) (x : ℕ → ℕ → MeasureAlgebra K)
    (hx : ∀ n j, IsPositive (x n j) ∧ ‖x n j‖ ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y : ℕ → MeasureAlgebra K, ∀ j, IsPositive (y j) ∧
      ‖y j‖ ≤ C ∧ ∀ f, Tendsto (fun n => x (φ n) j f) atTop (𝓝 (y j f)) := by
  obtain ⟨φ, hφ, hcol⟩ := exists_diagonal_subseq (isSeqCompact_positiveBall (K := K) C)
    (fun n j => (WeakDual.toStrongDual.symm (toDual (x n j)) : WeakDual ℂ C(K, ℂ)))
    fun n j => hx n j
  choose y hy hlim using hcol
  refine ⟨φ, hφ, fun j => ofDual (WeakDual.toStrongDual (y j)), fun j => ⟨(hy j).1, (hy j).2,
    fun f => ?_⟩⟩
  exact ((WeakDual.eval_continuous f).tendsto (y j)).comp (hlim j)

/-! ### Products and exponentials of uniformly convergent families -/

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem rightTransform_sub (Ψ₁ Ψ₂ : MeasureAlgebra K) (f : C(K, ℂ)) :
    rightTransform (Ψ₁ - Ψ₂) f = rightTransform Ψ₁ f - rightTransform Ψ₂ f := by
  ext x; rfl

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- **Products**: uniform weak-* convergence of bounded families passes to products, provided the
limit of the second factor is norm-continuous on the compact set `D`. -/
theorem WeakUnifOn.mul {F F' : ℕ → ℂ → MeasureAlgebra K} {G G' : ℂ → MeasureAlgebra K}
    {D : Set ℂ} (hD : IsCompact D) (h : WeakUnifOn F G D) (h' : WeakUnifOn F' G' D) {B B' : ℝ}
    (hF : ∀ n, ∀ z ∈ D, ‖F n z‖ ≤ B) (hG : ∀ z ∈ D, ‖G z‖ ≤ B)
    (hF' : ∀ n, ∀ z ∈ D, ‖F' n z‖ ≤ B') (hG' : ∀ z ∈ D, ‖G' z‖ ≤ B')
    (hc : ContinuousOn G' D) :
    WeakUnifOn (fun n z => F n z * F' n z) (fun z => G z * G' z) D := by
  intro f
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set T : Set C(K, ℂ) := range (shift f)
  have hT : IsCompact T := isCompact_range (shift f).continuous
  set S : Set C(K, ℂ) := (fun z => rightTransform (G' z) f) '' D
  have hS : IsCompact S := by
    refine hD.image_of_continuousOn ?_
    have hlin : Continuous fun Ψ : MeasureAlgebra K => rightTransform Ψ f := by
      refine (LipschitzWith.of_dist_le_mul (K := ‖f‖₊) fun Ψ₁ Ψ₂ => ?_).continuous
      rw [dist_eq_norm, dist_eq_norm, ← rightTransform_sub, coe_nnnorm, mul_comm]
      exact ((rightTransform (Ψ₁ - Ψ₂)).le_opNorm f).trans
        (mul_le_mul_of_nonneg_right (norm_rightTransform_le _) (norm_nonneg _))
    exact hlin.comp_continuousOn hc
  set Bp := max B 0 + 1
  have hBp : 0 < Bp := by positivity
  filter_upwards [WeakUnifOn.uniform_compact h' hF' hG' hT (ε / (2 * Bp)) (by positivity),
    WeakUnifOn.uniform_compact h hF hG hS (ε / 2) (by positivity)] with n h1 h2 z hz
  have hr : ‖rightTransform (F' n z) f - rightTransform (G' z) f‖ ≤ ε / (2 * Bp) := by
    rw [← rightTransform_sub]
    refine (ContinuousMap.norm_le _ (by positivity)).2 fun x => ?_
    rw [rightTransform_apply, MeasureAlgebra.sub_apply]
    exact (h1 z hz (shift f x) ⟨x, rfl⟩).le
  have h3 := h2 z hz (rightTransform (G' z) f) ⟨z, hz, rfl⟩
  rw [dist_eq_norm, norm_sub_rev, mul_apply, mul_apply,
    show F n z (rightTransform (F' n z) f) - G z (rightTransform (G' z) f) =
      F n z (rightTransform (F' n z) f - rightTransform (G' z) f) +
        (F n z (rightTransform (G' z) f) - G z (rightTransform (G' z) f)) by
      rw [map_sub]; ring]
  have h4 : ‖F n z (rightTransform (F' n z) f - rightTransform (G' z) f)‖ ≤ Bp * (ε / (2 * Bp)) :=
    (le_opNorm _ _).trans (mul_le_mul ((hF n z hz).trans (by linarith [le_max_left B 0])) hr
      (norm_nonneg _) hBp.le)
  have he : Bp * (ε / (2 * Bp)) = ε / 2 := by field_simp
  rw [he] at h4
  calc _ ≤ _ := norm_add_le _ _
    _ < ε := by linarith

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- The affine families `1 + z α_n` converge uniformly on bounded `D` when `α_n → α` weak-*. -/
theorem weakUnifOn_one_add {α : ℕ → MeasureAlgebra K} {α' : MeasureAlgebra K} {D : Set ℂ}
    {R : ℝ} (hD : D ⊆ Metric.closedBall 0 R) (h : ∀ f, Tendsto (fun n => α n f) atTop (𝓝 (α' f))) :
    WeakUnifOn (fun n z => 1 + z • α n) (fun z => 1 + z • α') D := by
  intro f
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set R' := max R 0 + 1
  have hR0 : R' ≠ 0 := by positivity
  filter_upwards [Metric.tendsto_nhds.1 (h f) (ε / R') (by positivity)] with n hn z hz
  have hz' : ‖z‖ ≤ R' := (mem_closedBall_zero_iff.1 (hD hz)).trans (by
    linarith [le_max_left R 0])
  rw [dist_eq_norm, MeasureAlgebra.add_apply, MeasureAlgebra.add_apply, MeasureAlgebra.smul_apply,
    MeasureAlgebra.smul_apply, add_sub_add_left_eq_sub, ← mul_sub, norm_mul, ← dist_eq_norm,
    dist_comm]
  calc ‖z‖ * dist (α n f) (α' f) ≤ R' * dist (α n f) (α' f) :=
        mul_le_mul_of_nonneg_right hz' dist_nonneg
    _ < R' * (ε / R') := mul_lt_mul_of_pos_left hn (by positivity)
    _ = ε := by field_simp

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem norm_one_add_smul_le (α : MeasureAlgebra K) {z : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) :
    ‖(1 : MeasureAlgebra K) + z • α‖ ≤ Real.exp (R * ‖α‖) := by
  calc ‖(1 : MeasureAlgebra K) + z • α‖ ≤ ‖(1 : MeasureAlgebra K)‖ + ‖z • α‖ := norm_add_le _ _
    _ = 1 + ‖z‖ * ‖α‖ := by rw [norm_one, norm_smul]
    _ ≤ 1 + R * ‖α‖ := by gcongr
    _ ≤ Real.exp (R * ‖α‖) := by linarith [Real.add_one_le_exp (R * ‖α‖)]

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem norm_prod_one_add_le (s : Finset ℕ) (α : ℕ → MeasureAlgebra K) {z : ℂ} {R : ℝ}
    (hz : ‖z‖ ≤ R) : ‖∏ j ∈ s, (1 + z • α j)‖ ≤ Real.exp (R * ∑ j ∈ s, ‖α j‖) := by
  refine (Finset.norm_prod_le _ _).trans ?_
  rw [Finset.mul_sum, Real.exp_sum]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun j _ => norm_one_add_smul_le (α j) hz

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- **Finite formations**: if every factor converges weak-* with uniform norm bounds, the finite
products `Π_{j < J} (1 + z α_{n,j})` converge uniformly on compact `D`. -/
theorem weakUnifOn_prod_range (α : ℕ → ℕ → MeasureAlgebra K) (α' : ℕ → MeasureAlgebra K)
    {D : Set ℂ} (hD : IsCompact D) {R : ℝ} (hDR : D ⊆ Metric.closedBall 0 R) {c : ℕ → ℝ}
    (hα : ∀ n j, ‖α n j‖ ≤ c j) (hα' : ∀ j, ‖α' j‖ ≤ c j)
    (h : ∀ j f, Tendsto (fun n => α n j f) atTop (𝓝 (α' j f))) (J : ℕ) :
    WeakUnifOn (fun n z => ∏ j ∈ Finset.range J, (1 + z • α n j))
      (fun z => ∏ j ∈ Finset.range J, (1 + z • α' j)) D := by
  have hz : ∀ z ∈ D, ‖z‖ ≤ max R 0 := fun z hz =>
    (mem_closedBall_zero_iff.1 (hDR hz)).trans (le_max_left _ _)
  induction J with
  | zero =>
    intro f
    simp only [Finset.range_zero, Finset.prod_empty]
    exact Metric.tendstoUniformlyOn_iff.2 fun ε hε => Eventually.of_forall fun n z _ => by
      simpa using hε
  | succ J ih =>
    simp only [Finset.prod_range_succ]
    refine WeakUnifOn.mul hD ih (weakUnifOn_one_add hDR (h J))
      (B := Real.exp (max R 0 * ∑ j ∈ Finset.range J, c j)) (B' := Real.exp (max R 0 * c J))
      (fun n z hzD => (norm_prod_one_add_le _ _ (hz z hzD)).trans (Real.exp_le_exp.2
        (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hα n j) (le_max_right _ _))))
      (fun z hzD => (norm_prod_one_add_le _ _ (hz z hzD)).trans (Real.exp_le_exp.2
        (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hα' j) (le_max_right _ _))))
      (fun n z hzD => (norm_one_add_smul_le _ (hz z hzD)).trans (Real.exp_le_exp.2
        (mul_le_mul_of_nonneg_left (hα n J) (le_max_right _ _))))
      (fun z hzD => (norm_one_add_smul_le _ (hz z hzD)).trans (Real.exp_le_exp.2
        (mul_le_mul_of_nonneg_left (hα' J) (le_max_right _ _))))
      (by fun_prop)

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- `‖Π_{j<M}(1 + z X/M) - exp(z X)‖ ≤ e^{2RB} R² B² / M` for `|z| ≤ R`, `‖X‖ ≤ B`. -/
theorem norm_pow_approx_exp_le (X : MeasureAlgebra K) {z : ℂ} {R B : ℝ} (hR : 0 ≤ R)
    (hz : ‖z‖ ≤ R) (hX : ‖X‖ ≤ B) {M : ℕ} (hM : 0 < M) :
    ‖∏ _j ∈ Finset.range M, (1 + z • ((M : ℂ)⁻¹ • X)) - exp (z • X)‖ ≤
      Real.exp (2 * (R * B)) * (R ^ 2 * B ^ 2 / M) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hx : ‖z • ((M : ℂ)⁻¹ • X)‖ ≤ R * B / M := by
    rw [norm_smul, norm_smul, norm_inv, Complex.norm_natCast, ← mul_assoc, mul_comm ‖z‖,
      inv_mul_eq_div, div_mul_eq_mul_div, mul_comm R B]
    exact div_le_div_of_nonneg_right (by nlinarith [norm_nonneg z, norm_nonneg X]) hM'.le
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hsum : ∑ _j ∈ Finset.range M, z • ((M : ℂ)⁻¹ • X) = z • X := by
    rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]
    congr 1
    field_simp
  have h := norm_prod_one_add_sub_exp_le (Finset.range M) fun _ => z • ((M : ℂ)⁻¹ • X)
  rw [hsum] at h
  refine h.trans (mul_le_mul (Real.exp_le_exp.2 ?_) ?_ (Finset.sum_nonneg fun _ _ => by
    positivity) (Real.exp_pos _).le)
  · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have := mul_le_mul_of_nonneg_left hx hM'.le
    rw [mul_div_cancel₀ _ hM'.ne'] at this
    linarith
  · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h2 : ‖z • ((M : ℂ)⁻¹ • X)‖ ^ 2 ≤ (R * B / M) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
    calc (M : ℝ) * ‖z • ((M : ℂ)⁻¹ • X)‖ ^ 2 ≤ M * (R * B / M) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 hM'.le
      _ = R ^ 2 * B ^ 2 / M := by field_simp

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- **Convolution exponentials**: if `X_n → X` weak-* with `‖X_n‖, ‖X‖ ≤ B`, then
`exp(z X_n) → exp(z X)` weak-* uniformly on compact `D`. -/
theorem weakUnifOn_exp (X : ℕ → MeasureAlgebra K) (X' : MeasureAlgebra K) {B : ℝ}
    (hX : ∀ n, ‖X n‖ ≤ B) (hX' : ‖X'‖ ≤ B) (h : ∀ f, Tendsto (fun n => X n f) atTop (𝓝 (X' f)))
    {D : Set ℂ} (hD : IsCompact D) {R : ℝ} (hDR : D ⊆ Metric.closedBall 0 R) :
    WeakUnifOn (fun n z => exp (z • X n)) (fun z => exp (z • X')) D := by
  intro f
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set R' := max R 0
  have hz : ∀ z ∈ D, ‖z‖ ≤ R' := fun z hz =>
    (mem_closedBall_zero_iff.1 (hDR hz)).trans (le_max_left _ _)
  set A := Real.exp (2 * (R' * B)) * (R' ^ 2 * B ^ 2) * (‖f‖ + 1)
  obtain ⟨M, hM⟩ := exists_nat_gt (4 * A / ε)
  have hM0 : 0 < M := by
    have : 0 ≤ 4 * A / ε := by positivity
    exact_mod_cast this.trans_lt hM
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM0
  have happrox : ‖f‖ * (Real.exp (2 * (R' * B)) * (R' ^ 2 * B ^ 2 / M)) < ε / 4 := by
    rw [div_lt_iff₀ hε] at hM
    rw [mul_div_assoc', mul_div_assoc', div_lt_iff₀ hM']
    nlinarith [norm_nonneg f, Real.exp_pos (2 * (R' * B)), sq_nonneg R', sq_nonneg B]
  have hprod := weakUnifOn_prod_range (fun n _ => (M : ℂ)⁻¹ • X n) (fun _ => (M : ℂ)⁻¹ • X')
    hD hDR (c := fun _ => B / M) (fun n _ => by
      rw [norm_smul, norm_inv, Complex.norm_natCast, inv_mul_eq_div]
      exact div_le_div_of_nonneg_right (hX n) hM'.le) (fun _ => by
      rw [norm_smul, norm_inv, Complex.norm_natCast, inv_mul_eq_div]
      exact div_le_div_of_nonneg_right hX' hM'.le) (fun _ g => by
      simp only [MeasureAlgebra.smul_apply]
      exact (h g).const_mul _) M f
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hprod (ε / 2) (by positivity)] with n hn z hzD
  have h1 := norm_pow_approx_exp_le (X n) (le_max_right R 0) (hz z hzD)
    ((hX n).trans le_rfl) hM0
  have h2 := norm_pow_approx_exp_le X' (le_max_right R 0) (hz z hzD) hX' hM0
  have h3 := hn z hzD
  rw [dist_eq_norm] at h3 ⊢
  set P := ∏ _j ∈ Finset.range M, (1 + z • ((M : ℂ)⁻¹ • X n))
  set P' := ∏ _j ∈ Finset.range M, (1 + z • ((M : ℂ)⁻¹ • X'))
  have e1 : ‖exp (z • X') f - P' f‖ ≤ ‖f‖ * (Real.exp (2 * (R' * B)) * (R' ^ 2 * B ^ 2 / M)) := by
    rw [← MeasureAlgebra.sub_apply, mul_comm]
    refine (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    rw [norm_sub_rev]
    exact h2
  have e2 : ‖P f - exp (z • X n) f‖ ≤ ‖f‖ * (Real.exp (2 * (R' * B)) * (R' ^ 2 * B ^ 2 / M)) := by
    rw [← MeasureAlgebra.sub_apply, mul_comm]
    exact (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
  calc ‖exp (z • X') f - exp (z • X n) f‖
      = ‖(exp (z • X') f - P' f) + (P' f - P f) + (P f - exp (z • X n) f)‖ := by ring_nf
    _ ≤ ‖exp (z • X') f - P' f‖ + ‖P' f - P f‖ + ‖P f - exp (z • X n) f‖ := norm_add₃_le
    _ < ε := by linarith

end GaloisForLFunctions.HTGeometry.FormationDust
