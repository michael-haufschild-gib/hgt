import GaloisForLFunctions.RHTower.XiHorizontalSliceConeCriterion
import GaloisForLFunctions.HTGeometry.ToeplitzTotalPositivityOrderTwo

/-!
# Log-concavity of the horizontal slice coefficients outside the `√3`-cone

The slice product `g_t(x) = ξ(½ + x + it)·ξ(½ − x + it)` is even, so its Taylor series at `0` is a
power series in `y = x²` with coefficients `a_k(t) = c_{2k}(t)`.  The per-zero cone criterion
(`XiHorizontalSliceConeCriterion`) gives `a_k(t) ≥ 0` when every zero copy satisfies
`|Re ρ − ½| ≤ |Im ρ − t|`.  Here the conclusion is strengthened to total positivity of order two:
`a_k(t)` is a Turán sequence (`TuranSeq`), in particular log-concave,

  `a_{k−1}(t)·a_{k+1}(t) ≤ a_k(t)²`,

whenever every zero copy satisfies `3 (Re ρ − ½)² ≤ (Im ρ − t)²`.

The mechanism is the same factorization: a critical zero contributes the factor
`e^{2t/γ}((γ − t)² + x²)/γ²`, whose `y`-coefficients `(A, B)` form a Turán sequence, and a reflection
pair with spectral point `a + ci` contributes a positive multiple of
`x⁴ + 2((a − t)² − c²)x² + ((a − t)² + c²)²`, whose `y`-coefficients `(Q, P, 1)` form a Turán
sequence exactly when `Q ≤ P²`, i.e. `(a − t)² ≥ 3c²`.  Turán sequences are closed under the Cauchy
product (`TuranSeq.conv`, the Binet–Cauchy formula) and under pointwise limits, and for even entire
functions the `y`-coefficients of a product are the Cauchy product of the `y`-coefficients.

With the unconditional critical-line band below squared ordinate `2365/16`, the `√3`-cone condition
holds at every height `|t| ≤ 56/5`, so the slice coefficients are log-concave there
(`xiSliceCoeff_turanSeq_of_abs_le`).
-/

open Complex Filter Topology
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## Even Taylor coefficients and their Turán property -/

/-- The `k`-th Taylor coefficient at `0` in the variable `y = x²`, as a real number. -/
def evenTaylorRe (f : ℂ → ℂ) (k : ℕ) : ℝ :=
  ((((2 * k).factorial : ℂ))⁻¹ * iteratedDeriv (2 * k) f 0).re

/-- An entire function with nonnegative Taylor coefficients at `0`, vanishing odd coefficients, and
a Turán sequence of even coefficients. -/
def TuranTaylorAtZero (f : ℂ → ℂ) : Prop :=
  NonnegTaylorAtZero f ∧ (∀ k : ℕ, iteratedDeriv (2 * k + 1) f 0 = 0) ∧
    TuranSeq (evenTaylorRe f)

/-- Splitting a finite sum over `0, …, 2k` into its even part when the odd terms vanish. -/
theorem sum_range_two_mul_add_one_eq_even {R : Type*} [AddCommMonoid R] (F : ℕ → R)
    (hF : ∀ j, F (2 * j + 1) = 0) (k : ℕ) :
    ∑ i ∈ Finset.range (2 * k + 1), F i = ∑ j ∈ Finset.range (k + 1), F (2 * j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, hF k, add_zero, Finset.sum_range_succ (n := k + 1),
      show 2 * (k + 1) = 2 * k + 1 + 1 by ring]

/-- A nonnegative Taylor coefficient is real. -/
theorem im_iteratedDeriv_eq_zero {f : ℂ → ℂ} (hf : NonnegTaylorAtZero f) (n : ℕ) :
    (iteratedDeriv n f 0).im = 0 :=
  (Complex.nonneg_iff.mp (hf.2 n)).2.symm

/-- The normalized Leibniz rule at even order for two even entire functions. -/
theorem factorial_inv_mul_iteratedDeriv_mul_even {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hfo : ∀ k : ℕ, iteratedDeriv (2 * k + 1) f 0 = 0) (k : ℕ) :
    (((2 * k).factorial : ℂ))⁻¹ * iteratedDeriv (2 * k) (f * g) 0 =
      ∑ j ∈ Finset.range (k + 1),
        ((((2 * j).factorial : ℂ))⁻¹ * iteratedDeriv (2 * j) f 0) *
          ((((2 * (k - j)).factorial : ℂ))⁻¹ * iteratedDeriv (2 * (k - j)) g 0) := by
  rw [iteratedDeriv_mul hf.contDiff.contDiffAt hg.contDiff.contDiffAt, Finset.mul_sum]
  have hterm : ∀ i ∈ Finset.range (2 * k + 1),
      (((2 * k).factorial : ℂ))⁻¹ *
          (((2 * k).choose i : ℂ) * iteratedDeriv i f 0 * iteratedDeriv (2 * k - i) g 0) =
        (((i.factorial : ℂ))⁻¹ * iteratedDeriv i f 0) *
          ((((2 * k - i).factorial : ℂ))⁻¹ * iteratedDeriv (2 * k - i) g 0) := by
    intro i hi
    have hik : i ≤ 2 * k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hfac : ((2 * k).choose i : ℂ) * (i.factorial : ℂ) * ((2 * k - i).factorial : ℂ) =
        ((2 * k).factorial : ℂ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hik
    have h1 : ((2 * k).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have h2 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have h3 : ((2 * k - i).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    field_simp
    linear_combination (iteratedDeriv i f 0 * iteratedDeriv (2 * k - i) g 0) * hfac
  rw [Finset.sum_congr rfl hterm]
  refine sum_range_two_mul_add_one_eq_even _ (fun j => by rw [hfo j]; simp) k |>.trans ?_
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [show 2 * k - 2 * j = 2 * (k - j) by omega]

/-- Odd coefficients of a product of even entire functions vanish. -/
theorem iteratedDeriv_mul_odd_eq_zero {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hfo : ∀ k : ℕ, iteratedDeriv (2 * k + 1) f 0 = 0)
    (hgo : ∀ k : ℕ, iteratedDeriv (2 * k + 1) g 0 = 0) (k : ℕ) :
    iteratedDeriv (2 * k + 1) (f * g) 0 = 0 := by
  rw [iteratedDeriv_mul hf.contDiff.contDiffAt hg.contDiff.contDiffAt]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hik : i ≤ 2 * k + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rcases Nat.even_or_odd' i with ⟨j, rfl | rfl⟩
  · rw [show 2 * k + 1 - 2 * j = 2 * (k - j) + 1 by omega, hgo, mul_zero]
  · rw [hfo, mul_zero, zero_mul]

/-- The real part of a product of real complex numbers. -/
theorem re_mul_of_im_eq_zero {z w : ℂ} (hz : z.im = 0) (hw : w.im = 0) :
    (z * w).re = z.re * w.re := by
  simp [Complex.mul_re, hz, hw]

theorem im_factorial_inv_mul {f : ℂ → ℂ} (hf : NonnegTaylorAtZero f) (n : ℕ) :
    ((((n.factorial : ℂ))⁻¹ * iteratedDeriv n f 0)).im = 0 := by
  rw [Complex.mul_im, im_iteratedDeriv_eq_zero hf n]
  simp [← Complex.ofReal_natCast, ← Complex.ofReal_inv]

/-- The even coefficients of a product are the Cauchy product of the even coefficients. -/
theorem evenTaylorRe_mul {f g : ℂ → ℂ} (hf : NonnegTaylorAtZero f) (hg : NonnegTaylorAtZero g)
    (hfo : ∀ k : ℕ, iteratedDeriv (2 * k + 1) f 0 = 0) :
    evenTaylorRe (f * g) = cauchyConv (evenTaylorRe f) (evenTaylorRe g) := by
  funext k
  unfold evenTaylorRe cauchyConv
  rw [factorial_inv_mul_iteratedDeriv_mul_even hf.1 hg.1 hfo k, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact re_mul_of_im_eq_zero (im_factorial_inv_mul hf _) (im_factorial_inv_mul hg _)

theorem TuranTaylorAtZero.mul {f g : ℂ → ℂ} (hf : TuranTaylorAtZero f)
    (hg : TuranTaylorAtZero g) : TuranTaylorAtZero (f * g) := by
  refine ⟨hf.1.mul hg.1, iteratedDeriv_mul_odd_eq_zero hf.1.1 hg.1.1 hf.2.1 hg.2.1, ?_⟩
  rw [evenTaylorRe_mul hf.1 hg.1 hf.2.1]
  exact hf.2.2.conv hg.2.2

/-- **The Turán property passes to locally uniform limits.** -/
theorem TuranTaylorAtZero.of_tendstoLocallyUniformlyOn {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} (hF : ∀ i, TuranTaylorAtZero (F i)) (hf : Differentiable ℂ f)
    (h : TendstoLocallyUniformlyOn F f l Set.univ) : TuranTaylorAtZero f := by
  have hd : ∀ n, Tendsto (fun i => iteratedDeriv n (F i) 0) l (𝓝 (iteratedDeriv n f 0)) :=
    fun n => (tendstoLocallyUniformlyOn_iteratedDeriv (fun i => (hF i).1.1) h n).tendsto_at
      (Set.mem_univ (0 : ℂ))
  refine ⟨NonnegTaylorAtZero.of_tendstoLocallyUniformlyOn (fun i => (hF i).1) hf h,
    fun k => ?_, ?_⟩
  · have h0 : Tendsto (fun i => iteratedDeriv (2 * k + 1) (F i) 0) l (𝓝 0) := by
      simp only [fun i => (hF i).2.1 k]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique (hd (2 * k + 1)) h0
  · refine TuranSeq.of_tendsto (l := l) (fun i => (hF i).2.2) fun n => ?_
    unfold evenTaylorRe
    exact (Complex.continuous_re.tendsto _).comp ((hd (2 * n)).const_mul _)

/-! ## The factors -/

/-- Iterated derivatives at `0` of an even quartic polynomial. -/
theorem iteratedDeriv_evenQuartic_zero (c0 c2 c4 : ℂ) (n : ℕ) :
    iteratedDeriv n (fun x : ℂ => c0 + c2 * x ^ 2 + c4 * x ^ 4) 0 =
      (if n = 0 then c0 else 0) + c2 * (if n = 2 then 2 else 0) +
        c4 * (if n = 4 then 24 else 0) := by
  have hc0 : ContDiffAt ℂ n (fun _ : ℂ => c0) 0 := contDiffAt_const
  have hc2 : ContDiffAt ℂ n (fun x : ℂ => c2 * x ^ 2) 0 := by fun_prop
  have hc4 : ContDiffAt ℂ n (fun x : ℂ => c4 * x ^ 4) 0 := by fun_prop
  rw [iteratedDeriv_fun_add (hc0.add hc2) hc4, iteratedDeriv_fun_add hc0 hc2, iteratedDeriv_const,
    iteratedDeriv_const_mul_field c2 (fun x : ℂ => x ^ 2),
    iteratedDeriv_const_mul_field c4 (fun x : ℂ => x ^ 4), iteratedDeriv_fun_pow_zero,
    iteratedDeriv_fun_pow_zero]
  simp [Nat.factorial]

/-- An even quartic with nonnegative coefficients `c₀, c₂, c₄` and `c₀c₄ ≤ c₂²` has the Turán
property. -/
theorem turanTaylorAtZero_evenQuartic {c0 c2 c4 : ℝ} (h0 : 0 ≤ c0) (h2 : 0 ≤ c2) (h4 : 0 ≤ c4)
    (h : c0 * c4 ≤ c2 * c2) :
    TuranTaylorAtZero (fun x : ℂ => (c0 : ℂ) + (c2 : ℂ) * x ^ 2 + (c4 : ℂ) * x ^ 4) := by
  refine ⟨⟨by fun_prop, fun n => ?_⟩, fun k => ?_, ?_⟩
  · rw [iteratedDeriv_evenQuartic_zero]
    have hc0 : (0 : ℂ) ≤ (c0 : ℂ) := Complex.zero_le_real.mpr h0
    have hc2 : (0 : ℂ) ≤ (c2 : ℂ) := Complex.zero_le_real.mpr h2
    have hc4 : (0 : ℂ) ≤ (c4 : ℂ) := Complex.zero_le_real.mpr h4
    refine add_nonneg (add_nonneg ?_ (mul_nonneg hc2 ?_)) (mul_nonneg hc4 ?_) <;>
      split_ifs <;> first | exact hc0 | exact le_rfl | norm_num
  · rw [iteratedDeriv_evenQuartic_zero]
    have h2' : 2 * k + 1 ≠ 2 := by omega
    have h3 : 2 * k + 1 ≠ 4 := by omega
    simp [h2', h3]
  · have e : evenTaylorRe (fun x : ℂ => (c0 : ℂ) + (c2 : ℂ) * x ^ 2 + (c4 : ℂ) * x ^ 4) =
        fun n => if n = 0 then c0 else if n = 1 then c2 else if n = 2 then c4 else 0 := by
      funext n
      unfold evenTaylorRe
      rw [iteratedDeriv_evenQuartic_zero]
      rcases n with _ | _ | _ | n
      · simp
      · simp [Nat.factorial]
        ring
      · simp [Nat.factorial]
        ring
      · have ha : 2 * (n + 3) ≠ 0 := by omega
        have hb : 2 * (n + 3) ≠ 2 := by omega
        have hc : 2 * (n + 3) ≠ 4 := by omega
        simp [ha, hb, hc]
    rw [e]
    exact TuranSeq.of_three h0 h2 h4 h

/-- A nonnegative constant has the Turán property. -/
theorem turanTaylorAtZero_const {c : ℝ} (hc : 0 ≤ c) : TuranTaylorAtZero (fun _ : ℂ => (c : ℂ)) := by
  have h := turanTaylorAtZero_evenQuartic hc le_rfl le_rfl (by simp)
  have e : (fun x : ℂ => (c : ℂ) + ((0 : ℝ) : ℂ) * x ^ 2 + ((0 : ℝ) : ℂ) * x ^ 4) =
      fun _ : ℂ => (c : ℂ) := by
    funext x
    simp
  rwa [e] at h

/-- The paired factor of a critical zero has the Turán property. -/
theorem turanTaylorAtZero_slice_pair {γ t : ℝ} (hγ : γ ≠ 0) :
    TuranTaylorAtZero (fun x => weierstrassE1 (((t : ℂ) - I * x) / γ) *
      weierstrassE1 (((t : ℂ) + I * x) / γ)) := by
  have e : (fun x => weierstrassE1 (((t : ℂ) - I * x) / γ) *
      weierstrassE1 (((t : ℂ) + I * x) / γ)) =
      fun x : ℂ => (((Real.exp (2 * t / γ) * (γ - t) ^ 2 / γ ^ 2 : ℝ) : ℂ)) +
        (((Real.exp (2 * t / γ) / γ ^ 2 : ℝ) : ℂ)) * x ^ 2 + ((0 : ℝ) : ℂ) * x ^ 4 := by
    funext x
    rw [weierstrassE1_slice_pair hγ x]
    simp only [Complex.ofReal_zero, zero_mul, add_zero]
    ring
  rw [e]
  exact turanTaylorAtZero_evenQuartic (by positivity) (by positivity) le_rfl
    (by rw [mul_zero]; exact mul_self_nonneg _)

/-- The four-factor reflection pair outside the `√3`-cone has the Turán property. -/
theorem turanTaylorAtZero_reflectionPair {C P Q : ℝ} (hC : 0 ≤ C) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hQP : Q ≤ P * P) :
    TuranTaylorAtZero (fun x => (C : ℂ) * (x ^ 4 + (P : ℂ) * x ^ 2 + (Q : ℂ))) := by
  have e : (fun x : ℂ => (C : ℂ) * (x ^ 4 + (P : ℂ) * x ^ 2 + (Q : ℂ))) =
      fun x : ℂ => ((C * Q : ℝ) : ℂ) + ((C * P : ℝ) : ℂ) * x ^ 2 + (C : ℂ) * x ^ 4 := by
    funext x
    push_cast
    ring
  rw [e]
  refine turanTaylorAtZero_evenQuartic (by positivity) (by positivity) hC ?_
  have : C * Q * C ≤ C * P * (C * P) := by
    have hCC : 0 ≤ C * C := mul_nonneg hC hC
    nlinarith [mul_le_mul_of_nonneg_left hQP hCC]
  linarith

/-- Turán property of a finite product grouped into orbits of an involution. -/
theorem turanTaylorAtZero_prod_of_involution {α : Type*} [DecidableEq α] (σ : α → α)
    (hσ : ∀ a, σ (σ a) = a) (f : α → ℂ → ℂ)
    (hfix : ∀ a, σ a = a → TuranTaylorAtZero (f a))
    (hpair : ∀ a, σ a ≠ a → TuranTaylorAtZero (f a * f (σ a))) :
    ∀ S : Finset α, (∀ a ∈ S, σ a ∈ S) → TuranTaylorAtZero (fun x => ∏ a ∈ S, f a x) := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hS
    rcases S.eq_empty_or_nonempty with hE | ⟨a, ha⟩
    · subst hE
      simpa using turanTaylorAtZero_const (zero_le_one : (0 : ℝ) ≤ 1)
    by_cases hfa : σ a = a
    · set T := S.erase a with hT
      have hTS : T ⊂ S := Finset.erase_ssubset ha
      have hTc : ∀ b ∈ T, σ b ∈ T := by
        intro b hb
        rw [hT, Finset.mem_erase] at hb ⊢
        refine ⟨fun h => hb.1 ?_, hS b hb.2⟩
        rw [← hσ b, h, hfa]
      have e : (fun x => ∏ b ∈ S, f b x) = f a * fun x => ∏ b ∈ T, f b x := by
        funext x
        rw [Pi.mul_apply, hT, Finset.mul_prod_erase S (fun b => f b x) ha]
      rw [e]
      exact (hfix a hfa).mul (ih T hTS hTc)
    · have hσa : σ a ∈ S.erase a := Finset.mem_erase.mpr ⟨hfa, hS a ha⟩
      set T := (S.erase a).erase (σ a) with hT
      have hTS : T ⊂ S :=
        (Finset.erase_ssubset hσa).trans_le (Finset.erase_subset a S)
      have hTc : ∀ b ∈ T, σ b ∈ T := by
        intro b hb
        rw [hT, Finset.mem_erase, Finset.mem_erase] at hb ⊢
        exact ⟨fun h => hb.2.1 (by rw [← hσ b, h, hσ]), fun h => hb.1 (by rw [← hσ b, h]),
          hS b hb.2.2⟩
      have e : (fun x => ∏ b ∈ S, f b x) = (f a * f (σ a)) * fun x => ∏ b ∈ T, f b x := by
        funext x
        rw [Pi.mul_apply, Pi.mul_apply, hT,
          ← Finset.mul_prod_erase S (fun b => f b x) ha,
          ← Finset.mul_prod_erase (S.erase a) (fun b => f b x) hσa]
        ring
      rw [e]
      exact (hpair a hfa).mul (ih T hTS hTc)

/-! ## The slice product -/

/-- **Log-concave slice coefficients outside the `√3`-cone.**  If every zero copy satisfies
`3 (Re ρ − ½)² ≤ (Im ρ − t)²`, the slice product at height `t` has the Turán property: its
coefficients in `y = x²` are nonnegative and form a Turán sequence. -/
theorem turanTaylorAtZero_xiSliceProduct_of_cone {t : ℝ}
    (hcone : ∀ q : XiZeroCopy, 3 * ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ ((q.1 : ℂ).im - t) ^ 2) :
    TuranTaylorAtZero (xiSliceProduct t) := by
  classical
  set φm : ℂ → ℂ := fun x => (t : ℂ) - I * x with hφm
  set φp : ℂ → ℂ := fun x => (t : ℂ) + I * x with hφp
  have hcm : Continuous φm := by rw [hφm]; fun_prop
  have hcp : Continuous φp := by rw [hφp]; fun_prop
  have hP : TendstoLocallyUniformlyOn
      (fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) xiCanonicalProduct atTop
      Set.univ := xiCanonicalProduct_hasProdLocallyUniformlyOn
  have hPcont : Continuous xiCanonicalProduct :=
    continuous_iff_continuousAt.mpr fun z =>
      (xiCanonicalProduct_analytic z (Set.mem_univ z)).continuousAt
  have hPdiff : Differentiable ℂ xiCanonicalProduct := fun z =>
    (xiCanonicalProduct_analytic z (Set.mem_univ z)).differentiableAt
  have hm := TendstoLocallyUniformlyOn.comp hP φm (Set.mapsTo_univ φm Set.univ) hcm.continuousOn
  have hp := TendstoLocallyUniformlyOn.comp hP φp (Set.mapsTo_univ φp Set.univ) hcp.continuousOn
  have hmul := hm.mul₀ hp (hPcont.comp hcm).continuousOn (hPcont.comp hcp).continuousOn
  let c : Finset XiZeroCopy → Finset XiZeroCopy := fun S => S ∪ S.image lagPartner
  have hc : Tendsto c atTop atTop :=
    tendsto_atTop_mono (fun S => Finset.subset_union_left) tendsto_id
  have hclosed : ∀ S, ∀ a ∈ c S, lagPartner a ∈ c S := by
    intro S a ha
    simp only [c, Finset.mem_union, Finset.mem_image] at ha ⊢
    rcases ha with ha | ⟨b, hb, rfl⟩
    · exact Or.inr ⟨a, ha, rfl⟩
    · left
      rw [lagPartner_lagPartner]
      exact hb
  have hmul' := tendstoLocallyUniformlyOn_comp_index hmul hc
  set f : XiZeroCopy → ℂ → ℂ := fun q x =>
    weierstrassE1 (φm x / xiSpectralPoint q) * weierstrassE1 (φp x / xiSpectralPoint q) with hf
  have hfix : ∀ q, lagPartner q = q → TuranTaylorAtZero (f q) := by
    intro q hq
    have hre : (q.1 : ℂ).re = 1 / 2 :=
      (lagPartner_fst_eq_iff q).mp (congrArg (fun r => (r.1 : ℂ)) hq)
    have hz : xiSpectralPoint q = (((q.1 : ℂ).im : ℝ) : ℂ) := by
      rw [xiSpectralPoint_eq_re_im, hre]
      simp
    have hγ : (q.1 : ℂ).im ≠ 0 := by
      intro h0
      apply xiSpectralPoint_ne_zero q
      rw [hz, h0, Complex.ofReal_zero]
    simp only [hf, hz, hφm, hφp]
    exact turanTaylorAtZero_slice_pair hγ
  have hpair : ∀ q, lagPartner q ≠ q → TuranTaylorAtZero (f q * f (lagPartner q)) := by
    intro q _
    set a : ℝ := (q.1 : ℂ).im with ha
    set cc : ℝ := 1 / 2 - (q.1 : ℂ).re with hcc
    have hz : xiSpectralPoint q = (a : ℂ) + cc * I := xiSpectralPoint_eq_re_im q
    have hz0 : (a : ℂ) + cc * I ≠ 0 := by rw [← hz]; exact xiSpectralPoint_ne_zero q
    have hzσ : xiSpectralPoint (lagPartner q) = starRingEnd ℂ ((a : ℂ) + cc * I) := by
      rw [xiSpectralPoint_lagPartner, hz]
    have e : f q * f (lagPartner q) = fun x =>
        ((Real.exp (4 * t * a / (a ^ 2 + cc ^ 2)) / (a ^ 2 + cc ^ 2) ^ 2 : ℝ) : ℂ) *
          (x ^ 4 + ((2 * ((a - t) ^ 2 - cc ^ 2) : ℝ) : ℂ) * x ^ 2 +
            ((((a - t) ^ 2 + cc ^ 2) ^ 2 : ℝ) : ℂ)) := by
      funext x
      simp only [Pi.mul_apply, hf, hz, hzσ, hφm, hφp]
      exact weierstrassE1_slice_reflectionPair hz0 x
    rw [e]
    have hsq : 3 * cc ^ 2 ≤ (a - t) ^ 2 := by
      have h := hcone q
      have hc2 : cc ^ 2 = ((q.1 : ℂ).re - 1 / 2) ^ 2 := by rw [hcc]; ring
      rw [hc2, ha]
      exact h
    refine turanTaylorAtZero_reflectionPair (by positivity) (by nlinarith [sq_nonneg cc])
      (by positivity) ?_
    nlinarith [sq_nonneg cc, sq_nonneg (a - t)]
  have hfin : ∀ S : Finset XiZeroCopy, TuranTaylorAtZero
      (((fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) (c S) ∘ φm) *
        ((fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) (c S) ∘ φp)) := by
    intro S
    have e : (((fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) (c S) ∘ φm) *
        ((fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) (c S) ∘ φp)) =
        fun x => ∏ q ∈ c S, f q x := by
      funext x
      simp only [Pi.mul_apply, Function.comp_apply, hf]
      rw [Finset.prod_mul_distrib]
    rw [e]
    exact turanTaylorAtZero_prod_of_involution lagPartner lagPartner_lagPartner f hfix hpair
      (c S) (hclosed S)
  have hlim : TuranTaylorAtZero ((xiCanonicalProduct ∘ φm) * (xiCanonicalProduct ∘ φp)) :=
    TuranTaylorAtZero.of_tendstoLocallyUniformlyOn hfin
      ((hPdiff.comp (by rw [hφm]; fun_prop)).mul (hPdiff.comp (by rw [hφp]; fun_prop))) hmul'
  have e : xiSliceProduct t = (fun _ => XiC 0 * XiC 0) *
      ((xiCanonicalProduct ∘ φm) * (xiCanonicalProduct ∘ φp)) := by
    funext x
    rw [xiSliceProduct_eq_XiC]
    have hX : ∀ a, XiC a = XiC 0 * xiCanonicalProduct a := fun a => by
      simpa only [Pi.mul_apply] using congrFun XiC_eq_constant_mul_canonicalProduct a
    simp only [Pi.mul_apply, Function.comp_apply, hφm, hφp]
    rw [hX ((t : ℂ) - I * x), hX ((t : ℂ) + I * x)]
    ring
  have hX0 : XiC 0 * XiC 0 = (((XiC 0 * XiC 0).re : ℝ) : ℂ) := by
    have h := zero_le_XiC_zero_mul_self
    apply Complex.ext <;> simp [(Complex.nonneg_iff.mp h).2.symm]
  have hX0nn : 0 ≤ (XiC 0 * XiC 0).re := (Complex.nonneg_iff.mp zero_le_XiC_zero_mul_self).1
  rw [e, hX0]
  exact (turanTaylorAtZero_const hX0nn).mul hlim

/-- The slice coefficients `c_{2k}(t)` are real and their `y`-sequence is `evenTaylorRe`. -/
theorem evenTaylorRe_xiSliceProduct (t : ℝ) (k : ℕ) :
    evenTaylorRe (xiSliceProduct t) k = (xiSliceCoeff t (2 * k)).re := by
  rfl

/-- **Turán inequalities for the slice coefficients outside the `√3`-cone.**  Under the cone
condition `3 (Re ρ − ½)² ≤ (Im ρ − t)²`, the real slice coefficients `a_k = c_{2k}(t)` form a
Turán sequence: nonnegative, with `a_i · a_{j+1} ≤ a_{i+1} · a_j` for `i < j`. -/
theorem xiSliceCoeff_turanSeq_of_cone {t : ℝ}
    (hcone : ∀ q : XiZeroCopy, 3 * ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ ((q.1 : ℂ).im - t) ^ 2) :
    TuranSeq (fun k => (xiSliceCoeff t (2 * k)).re) :=
  (turanTaylorAtZero_xiSliceProduct_of_cone hcone).2.2

/-- **Log-concavity of the slice coefficients outside the `√3`-cone.** -/
theorem xiSliceCoeff_logConcave_of_cone {t : ℝ}
    (hcone : ∀ q : XiZeroCopy, 3 * ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ ((q.1 : ℂ).im - t) ^ 2)
    (k : ℕ) :
    (xiSliceCoeff t (2 * k)).re * (xiSliceCoeff t (2 * (k + 2))).re ≤
      (xiSliceCoeff t (2 * (k + 1))).re ^ 2 := by
  have h := (xiSliceCoeff_turanSeq_of_cone hcone).2 k (k + 1) (Nat.lt_succ_self k)
  rw [sq]
  simpa only [show k + 1 + 1 = k + 2 by ring] using h

/-- On `|t| ≤ 56/5` every zero copy lies outside the `√3`-cone at height `t`, unconditionally. -/
theorem sqrt3Cone_of_abs_le {t : ℝ} (ht : |t| ≤ 56 / 5) (q : XiZeroCopy) :
    3 * ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ ((q.1 : ℂ).im - t) ^ 2 := by
  by_cases hh : (q.1 : ℂ).im ^ 2 < 2365 / 16
  · rw [xiZeroCopy_re_eq_half_of_im_sq_lt_2365_over_16 q hh, sub_self]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    exact sq_nonneg _
  · push Not at hh
    have hstrip := xiZeroCopy_re_mem_open_unit q
    have h1 : ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 := by
      nlinarith [hstrip.1, hstrip.2]
    have h2 : (243 / 20 : ℝ) ≤ |(q.1 : ℂ).im| := by
      by_contra h
      push Not at h
      have habs := abs_nonneg ((q.1 : ℂ).im)
      have hsq : (q.1 : ℂ).im ^ 2 = |(q.1 : ℂ).im| ^ 2 := (sq_abs _).symm
      nlinarith
    have h3 := abs_sub_abs_le_abs_sub ((q.1 : ℂ).im) t
    have h4 : (19 / 20 : ℝ) ≤ |(q.1 : ℂ).im - t| := by linarith
    have h5 : ((19 / 20 : ℝ)) ^ 2 ≤ ((q.1 : ℂ).im - t) ^ 2 := by
      rw [← sq_abs ((q.1 : ℂ).im - t)]
      exact pow_le_pow_left₀ (by norm_num) h4 2
    nlinarith

/-- **Unconditional log-concavity of the slice coefficients on `|t| ≤ 56/5`.**  At every height
`|t| ≤ 56/5`, the coefficients `c_{2k}(t)` of `ξ(½ + x + it)ξ(½ − x + it)` in `y = x²` form a Turán
sequence; in particular `c_{2k}(t)·c_{2k+4}(t) ≤ c_{2k+2}(t)²`.  At `t = 0` this is the statement for
the even Taylor coefficients of `ξ(½ + x)²`. -/
theorem xiSliceCoeff_turanSeq_of_abs_le {t : ℝ} (ht : |t| ≤ 56 / 5) :
    TuranSeq (fun k => (xiSliceCoeff t (2 * k)).re) :=
  xiSliceCoeff_turanSeq_of_cone (sqrt3Cone_of_abs_le ht)

end

end RHTower
