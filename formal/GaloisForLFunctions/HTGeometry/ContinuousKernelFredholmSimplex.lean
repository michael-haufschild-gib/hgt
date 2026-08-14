import GaloisForLFunctions.HTGeometry.ContinuousKernelFredholmDeterminant
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Ordered-simplex presentation of continuous-kernel Fredholm coefficients

For a symmetric Fredholm determinant integrand, the factor `1/n!` in the cube presentation is
equivalently absorbed by integrating over one ordered simplex.  This presentation exposes the
moving-aperture derivative as a literal fundamental-theorem-of-calculus boundary term.  The module
does not identify cube and simplex presentations yet; it provides both constructions and the exact
boundary-minor recursion needed for that identification and Suzuki's equation (4.19).
-/

open scoped BigOperators
open Set MeasureTheory Filter Topology

noncomputable section

namespace ContinuousKernelFredholm

/-- Iterated integral over `0 ≤ t₀ ≤ ... ≤ tₙ₋₁ ≤ a`. -/
noncomputable def orderedSimplexIntegral :
    ∀ n : ℕ, ℝ → ((Fin n → ℝ) → ℂ) → ℂ
  | 0, _a, f => f (fun i => Fin.elim0 i)
  | n + 1, a, f => ∫ t in (0 : ℝ)..a,
      orderedSimplexIntegral n t (fun v => f (Fin.snoc v t))

/-- FTC for an ordered-simplex integral, with its face integral as derivative. -/
theorem hasDerivAt_orderedSimplexIntegral_succ
    (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℂ) (a : ℝ)
    (hcont : Continuous (fun t : ℝ =>
      orderedSimplexIntegral n t (fun v => f (Fin.snoc v t)))) :
    HasDerivAt (fun u => orderedSimplexIntegral (n + 1) u f)
      (orderedSimplexIntegral n a (fun v => f (Fin.snoc v a))) a := by
  rw [show (fun u => orderedSimplexIntegral (n + 1) u f) =
      fun u => ∫ t in (0 : ℝ)..u,
        orderedSimplexIntegral n t (fun v => f (Fin.snoc v t)) by
    funext u
    rw [orderedSimplexIntegral]]
  exact intervalIntegral.integral_hasDerivAt_right
    (hcont.intervalIntegrable 0 a) (hcont.stronglyMeasurableAtFilter volume (nhds a))
      hcont.continuousAt

/-- Rescaling a moving ordered-simplex face to the fixed interval `[0,1]`. -/
theorem orderedSimplexIntegral_succ_scale
    (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℂ) (a : ℝ) :
    orderedSimplexIntegral (n + 1) a f =
      a • ∫ s in (0 : ℝ)..1,
        orderedSimplexIntegral n (a * s) (fun v => f (Fin.snoc v (a * s))) := by
  rw [orderedSimplexIntegral]
  simpa using (intervalIntegral.smul_integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1)
    (fun t : ℝ => orderedSimplexIntegral n t (fun v => f (Fin.snoc v t))) a).symm

/-- Joint continuity of an ordered-simplex integral in arbitrary locally compact parameters and
its moving aperture.  Scaling to `[0,1]` turns the induction into a compact parametric integral. -/
theorem continuous_orderedSimplexIntegral_param
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] [LocallyCompactSpace X]
    (n : ℕ) (f : X → (Fin n → ℝ) → ℂ) (hf : Continuous f.uncurry) :
    Continuous (fun p : X × ℝ => orderedSimplexIntegral n p.2 (f p.1)) := by
  induction n generalizing X with
  | zero =>
      change Continuous (fun p : X × ℝ => f p.1 (fun i => Fin.elim0 i))
      change Continuous (Function.uncurry f ∘
        fun p : X × ℝ => (p.1, fun i : Fin 0 => Fin.elim0 i))
      exact hf.comp (by fun_prop)
  | succ n ih =>
      let g : (X × ℝ) → (Fin n → ℝ) → ℂ :=
        fun q v => f q.1 (Fin.snoc v q.2)
      have hg : Continuous g.uncurry := by
        change Continuous (fun q : (X × ℝ) × (Fin n → ℝ) =>
          f q.1.1 (@Fin.snoc n (fun _ => ℝ) q.2 q.1.2))
        change Continuous (Function.uncurry f ∘
          fun q : (X × ℝ) × (Fin n → ℝ) =>
            (q.1.1, @Fin.snoc n (fun _ => ℝ) q.2 q.1.2))
        exact hf.comp (by fun_prop)
      have hinner := ih g hg
      let h : (X × ℝ) → ℝ → ℂ := fun p s =>
        orderedSimplexIntegral n (p.2 * s) (g (p.1, p.2 * s))
      have hh : Continuous h.uncurry := by
        change Continuous (fun q : (X × ℝ) × ℝ =>
          orderedSimplexIntegral n (q.1.2 * q.2)
            (g (q.1.1, q.1.2 * q.2)))
        change Continuous ((fun p : (X × ℝ) × ℝ =>
          orderedSimplexIntegral n p.2 (g p.1)) ∘
            fun q : (X × ℝ) × ℝ =>
              ((q.1.1, q.1.2 * q.2), q.1.2 * q.2))
        exact hinner.comp (by fun_prop)
      have hset : Continuous (fun p : X × ℝ => ∫ s in Icc (0 : ℝ) 1, h p s) :=
        continuous_parametric_integral_of_continuous hh isCompact_Icc
      have hint : Continuous (fun p : X × ℝ => ∫ s in (0 : ℝ)..1, h p s) := by
        convert hset using 1
        funext p
        rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
          ← integral_Icc_eq_integral_Ioc]
      have hscaled : Continuous (fun p : X × ℝ => p.2 • ∫ s in (0 : ℝ)..1, h p s) :=
        continuous_snd.smul hint
      convert hscaled using 1
      funext p
      rw [orderedSimplexIntegral_succ_scale]

/-- A pointwise bound `C` gives the exact ordered-simplex volume factor `a^n/n!`. -/
theorem norm_orderedSimplexIntegral_le
    (n : ℕ) {a C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    (f : (Fin n → ℝ) → ℂ)
    (hf : ∀ x, (∀ i, x i ∈ Icc (0 : ℝ) a) → ‖f x‖ ≤ C) :
    ‖orderedSimplexIntegral n a f‖ ≤ a ^ n / (n.factorial : ℝ) * C := by
  induction n generalizing a C with
  | zero =>
      simpa [orderedSimplexIntegral] using
        hf (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  | succ n ih =>
      rw [orderedSimplexIntegral]
      calc
        ‖∫ t in (0 : ℝ)..a,
            orderedSimplexIntegral n t (fun v => f (Fin.snoc v t))‖
            ≤ ∫ t in (0 : ℝ)..a, t ^ n / (n.factorial : ℝ) * C := by
              apply intervalIntegral.norm_integral_le_of_norm_le ha
              · filter_upwards with t ht
                have ht0 : 0 ≤ t := ht.1.le
                apply ih ht0 hC (fun v => f (Fin.snoc v t))
                intro v hv
                apply hf (Fin.snoc v t)
                intro i
                refine Fin.lastCases ?_ (fun j => ?_) i
                · simpa using (show t ∈ Icc (0 : ℝ) a from ⟨ht.1.le, ht.2⟩)
                · simpa using (show v j ∈ Icc (0 : ℝ) a from
                    ⟨(hv j).1, (hv j).2.trans ht.2⟩)
              · exact (show Continuous (fun t : ℝ => t ^ n / (n.factorial : ℝ) * C) from
                  ((continuous_pow n).div_const _).mul continuous_const).intervalIntegrable 0 a
        _ = a ^ (n + 1) / ((n + 1).factorial : ℝ) * C := by
          rw [intervalIntegral.integral_mul_const]
          change ((∫ t in (0 : ℝ)..a, t ^ n * (n.factorial : ℝ)⁻¹) * C) = _
          rw [intervalIntegral.integral_mul_const]
          rw [integral_pow]
          rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          field_simp
          ring

/-- Ordered-simplex form of the `n`-th Fredholm coefficient. -/
noncomputable def orderedFredholmCoefficient
    (K : ℝ → ℝ → ℂ) (a : ℝ) (n : ℕ) : ℂ :=
  orderedSimplexIntegral n a (fredholmIntegrand K n)

/-- Ordered-simplex Fredholm series. -/
noncomputable def orderedDeterminant
    (K : ℝ → ℝ → ℂ) (a : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ n * orderedFredholmCoefficient K a n

/-- Hadamard bound for one ordered Fredholm coefficient. -/
theorem orderedFredholmCoefficient_norm_le
    (K : ℝ → ℝ → ℂ) {a M : ℝ} (ha : 0 ≤ a) (hM : 0 ≤ M)
    (hK : ∀ x ∈ Icc (0 : ℝ) a, ∀ y ∈ Icc (0 : ℝ) a, ‖K x y‖ ≤ M)
    (n : ℕ) :
    ‖orderedFredholmCoefficient K a n‖ ≤
      (Real.sqrt n * (a * M)) ^ n / (n.factorial : ℝ) := by
  rw [orderedFredholmCoefficient]
  refine (norm_orderedSimplexIntegral_le n ha
    (pow_nonneg (mul_nonneg (Real.sqrt_nonneg n) hM) n) _ ?_).trans_eq ?_
  · intro x hx
    exact complex_hadamard_entry_bound _ (fun i j => hK _ (hx i) _ (hx j))
  · rw [mul_pow]
    ring

/-- Absolute convergence of the ordered-simplex Fredholm series for every parameter. -/
theorem orderedDeterminant_summable
    (K : ℝ → ℝ → ℂ) {a M : ℝ} (ha : 0 ≤ a) (hM : 0 ≤ M)
    (hK : ∀ x ∈ Icc (0 : ℝ) a, ∀ y ∈ Icc (0 : ℝ) a, ‖K x y‖ ≤ M)
    (z : ℂ) :
    Summable (fun n : ℕ => z ^ n * orderedFredholmCoefficient K a n) := by
  apply Summable.of_norm_bounded
    (summable_hadamard_majorant (‖z‖ * (a * M))
      (mul_nonneg (norm_nonneg z) (mul_nonneg ha hM)))
  intro n
  rw [norm_mul, norm_pow]
  calc
    ‖z‖ ^ n * ‖orderedFredholmCoefficient K a n‖
        ≤ ‖z‖ ^ n * ((Real.sqrt n * (a * M)) ^ n / (n.factorial : ℝ)) := by
          gcongr
          exact orderedFredholmCoefficient_norm_le K ha hM hK n
    _ = (Real.sqrt n * (‖z‖ * (a * M))) ^ n / (n.factorial : ℝ) := by ring

/-- Shifted Hadamard majorant needed for the first-minor and aperture-derivative series. -/
theorem summable_succ_hadamard_majorant (c : ℝ) (hc : 0 ≤ c) :
    Summable (fun n : ℕ =>
      (Real.sqrt (n + 1) * c) ^ (n + 1) / (n.factorial : ℝ)) := by
  have hgeom : Summable (fun n : ℕ =>
      2 * c * ((n : ℝ) ^ 1 * ((1 : ℝ) / 2) ^ n)) :=
    (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (by norm_num : ‖(1 : ℝ) / 2‖ < 1)).mul_left (2 * c)
  apply hgeom.of_norm_bounded_eventually_nat
  obtain ⟨N, hN⟩ := exists_nat_ge ((4 * Real.exp 1 * c) ^ 2)
  rw [Filter.eventually_atTop]
  refine ⟨max N 1, fun n hnmax => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left N 1) hnmax
  have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right N 1) hnmax)
  have hncast : (N : ℝ) ≤ n := by exact_mod_cast hnN
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hsqrtn : 0 < Real.sqrt n := Real.sqrt_pos.2 hnreal
  have hsqrtSucc : 0 ≤ Real.sqrt (n + 1) := Real.sqrt_nonneg _
  have hsqrtBound : Real.sqrt (n + 1) ≤ 2 * Real.sqrt n := by
    rw [Real.sqrt_le_left (mul_nonneg (by norm_num) hsqrtn.le)]
    rw [mul_pow, Real.sq_sqrt hnreal.le]
    nlinarith
  have hfour : 0 ≤ 4 * Real.exp 1 * c := by positivity
  have hsqrtLower : 4 * Real.exp 1 * c ≤ Real.sqrt n := by
    rw [← Real.sqrt_sq hfour]
    exact Real.sqrt_le_sqrt (hN.trans hncast)
  have hratio : 2 * Real.exp 1 * c / Real.sqrt n ≤ 1 / 2 := by
    rw [div_le_iff₀ hsqrtn]
    nlinarith
  have hbase : 0 < (n : ℝ) / Real.exp 1 := div_pos hnreal (Real.exp_pos 1)
  have hsqrtFactor : 1 ≤ Real.sqrt (2 * Real.pi * n) := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    have hpi := Real.pi_gt_three
    calc
      (1 : ℝ) ≤ 2 * 3 * 1 := by norm_num
      _ ≤ 2 * Real.pi * n := by gcongr
  have hfacLower : ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
    calc
      ((n : ℝ) / Real.exp 1) ^ n ≤
          Real.sqrt (2 * Real.pi * n) * ((n : ℝ) / Real.exp 1) ^ n := by
            exact le_mul_of_one_le_left (pow_nonneg hbase.le n) hsqrtFactor
      _ ≤ (n.factorial : ℝ) := Stirling.le_factorial_stirling n
  have hnum : 0 ≤ (Real.sqrt (n + 1) * c) ^ (n + 1) := by positivity
  rw [Real.norm_of_nonneg (div_nonneg hnum (Nat.cast_nonneg n.factorial))]
  calc
    (Real.sqrt (n + 1) * c) ^ (n + 1) / (n.factorial : ℝ)
        ≤ (Real.sqrt (n + 1) * c) ^ (n + 1) /
            (((n : ℝ) / Real.exp 1) ^ n) :=
      div_le_div_of_nonneg_left hnum (pow_pos hbase n) hfacLower
    _ ≤ (2 * Real.sqrt n * c) ^ (n + 1) /
            (((n : ℝ) / Real.exp 1) ^ n) := by
      gcongr
    _ = 2 * Real.sqrt n * c *
          (2 * Real.exp 1 * c / Real.sqrt n) ^ n := by
      have hbaseEq : 2 * Real.sqrt n * c =
          ((n : ℝ) / Real.exp 1) * (2 * Real.exp 1 * c / Real.sqrt n) := by
        field_simp [hsqrtn.ne', (Real.exp_pos 1).ne']
        rw [Real.sq_sqrt hnreal.le]
        ring
      rw [pow_succ', hbaseEq, mul_pow]
      field_simp [hbase.ne']
    _ ≤ 2 * Real.sqrt n * c * ((1 : ℝ) / 2) ^ n := by
      gcongr
    _ ≤ 2 * c * ((n : ℝ) ^ 1 * ((1 : ℝ) / 2) ^ n) := by
      have hsqrtn_le : Real.sqrt n ≤ n := by
        rw [Real.sqrt_le_left hnreal.le]
        nlinarith
      rw [pow_one]
      calc
        2 * Real.sqrt n * c * ((1 : ℝ) / 2) ^ n ≤
            2 * n * c * ((1 : ℝ) / 2) ^ n := by gcongr
        _ = 2 * c * (n * ((1 : ℝ) / 2) ^ n) := by ring

/-- First Fredholm-minor integrand with distinguished row point `x` and column point `y`. -/
noncomputable def fredholmMinorIntegrand
    (K : ℝ → ℝ → ℂ) (n : ℕ) (x y : ℝ) (t : Fin n → ℝ) : ℂ :=
  Matrix.det (fun i j : Fin (n + 1) =>
    K (@Fin.snoc n (fun _ => ℝ) t x i) (@Fin.snoc n (fun _ => ℝ) t y j))

/-- Ordered-simplex coefficient of the first Fredholm minor. -/
noncomputable def orderedFredholmMinorCoefficient
    (K : ℝ → ℝ → ℂ) (a : ℝ) (n : ℕ) (x y : ℝ) : ℂ :=
  orderedSimplexIntegral n a (fredholmMinorIntegrand K n x y)

/-- Hadamard bound for one ordered first-minor coefficient.  The distinguished row and column
contribute the shift from `n` to `n + 1`. -/
theorem orderedFredholmMinorCoefficient_norm_le
    (K : ℝ → ℝ → ℂ) {a M x y : ℝ} (ha : 0 ≤ a) (hM : 0 ≤ M)
    (hx : x ∈ Icc (0 : ℝ) a) (hy : y ∈ Icc (0 : ℝ) a)
    (hK : ∀ u ∈ Icc (0 : ℝ) a, ∀ v ∈ Icc (0 : ℝ) a, ‖K u v‖ ≤ M)
    (n : ℕ) :
    ‖orderedFredholmMinorCoefficient K a n x y‖ ≤
      a ^ n / (n.factorial : ℝ) * (Real.sqrt (n + 1) * M) ^ (n + 1) := by
  rw [orderedFredholmMinorCoefficient]
  apply norm_orderedSimplexIntegral_le n ha
    (pow_nonneg (mul_nonneg (Real.sqrt_nonneg (n + 1)) hM) (n + 1))
  intro t ht
  rw [fredholmMinorIntegrand]
  simpa [Nat.cast_add, Nat.cast_one] using
    (complex_hadamard_entry_bound
      (fun i j : Fin (n + 1) =>
        K (@Fin.snoc n (fun _ => ℝ) t x i) (@Fin.snoc n (fun _ => ℝ) t y j))
      (M := M) (by
        intro i j
        apply hK
        · refine Fin.lastCases ?_ (fun k => ?_) i
          · simpa using hx
          · simpa using ht k
        · refine Fin.lastCases ?_ (fun k => ?_) j
          · simpa using hy
          · simpa using ht k))

/-- Ordered-simplex first Fredholm minor series. -/
noncomputable def orderedFredholmMinor
    (K : ℝ → ℝ → ℂ) (a : ℝ) (z : ℂ) (x y : ℝ) : ℂ :=
  ∑' n : ℕ, z ^ n * orderedFredholmMinorCoefficient K a n x y

/-- Absolute convergence of the ordered first-minor series for every complex parameter. -/
theorem orderedFredholmMinor_summable
    (K : ℝ → ℝ → ℂ) {a M x y : ℝ} (ha : 0 ≤ a) (hM : 0 ≤ M)
    (hx : x ∈ Icc (0 : ℝ) a) (hy : y ∈ Icc (0 : ℝ) a)
    (hK : ∀ u ∈ Icc (0 : ℝ) a, ∀ v ∈ Icc (0 : ℝ) a, ‖K u v‖ ≤ M)
    (z : ℂ) :
    Summable (fun n : ℕ => z ^ n * orderedFredholmMinorCoefficient K a n x y) := by
  let B : ℝ := ‖z‖ * (a * M)
  let c : ℝ := max M B
  have hB : 0 ≤ B := mul_nonneg (norm_nonneg z) (mul_nonneg ha hM)
  have hc : 0 ≤ c := le_max_of_le_left hM
  have hMc : M ≤ c := le_max_left _ _
  have hBc : B ≤ c := le_max_right _ _
  apply Summable.of_norm_bounded (summable_succ_hadamard_majorant c hc)
  intro n
  rw [norm_mul, norm_pow]
  have hsqrt : 0 ≤ Real.sqrt (n + 1) := Real.sqrt_nonneg _
  calc
    ‖z‖ ^ n * ‖orderedFredholmMinorCoefficient K a n x y‖
        ≤ ‖z‖ ^ n *
            (a ^ n / (n.factorial : ℝ) *
              (Real.sqrt (n + 1) * M) ^ (n + 1)) := by
          gcongr
          exact orderedFredholmMinorCoefficient_norm_le K ha hM hx hy hK n
    _ = (Real.sqrt (n + 1) * M) *
          (Real.sqrt (n + 1) * B) ^ n / (n.factorial : ℝ) := by
          rw [pow_succ']
          dsimp [B]
          ring
    _ ≤ (Real.sqrt (n + 1) * c) *
          (Real.sqrt (n + 1) * c) ^ n / (n.factorial : ℝ) := by
          gcongr
    _ = (Real.sqrt (n + 1) * c) ^ (n + 1) / (n.factorial : ℝ) := by
          rw [pow_succ']

/-- A continuous kernel gives a jointly continuous first-minor integrand. -/
theorem continuous_fredholmMinorIntegrand
    (K : ℝ → ℝ → ℂ) (hK : Continuous K.uncurry) (n : ℕ) :
    Continuous (fun p : (ℝ × ℝ) × (Fin n → ℝ) =>
      fredholmMinorIntegrand K n p.1.1 p.1.2 p.2) := by
  rw [show (fun p : (ℝ × ℝ) × (Fin n → ℝ) =>
      fredholmMinorIntegrand K n p.1.1 p.1.2 p.2) =
    fun p => Matrix.det (fun i j : Fin (n + 1) =>
      K (@Fin.snoc n (fun _ => ℝ) p.2 p.1.1 i)
        (@Fin.snoc n (fun _ => ℝ) p.2 p.1.2 j)) by rfl]
  apply Continuous.matrix_det
  fun_prop

/-- Joint continuity of a first-minor coefficient in both distinguished points and aperture. -/
theorem continuous_orderedFredholmMinorCoefficient
    (K : ℝ → ℝ → ℂ) (hK : Continuous K.uncurry) (n : ℕ) :
    Continuous (fun p : (ℝ × ℝ) × ℝ =>
      orderedFredholmMinorCoefficient K p.2 n p.1.1 p.1.2) := by
  exact continuous_orderedSimplexIntegral_param n
    (fun p : ℝ × ℝ => fredholmMinorIntegrand K n p.1 p.2)
      (continuous_fredholmMinorIntegrand K hK n)

/-- In particular, the moving-aperture diagonal first-minor coefficient is continuous. -/
theorem continuous_orderedFredholmMinorCoefficient_diagonal
    (K : ℝ → ℝ → ℂ) (hK : Continuous K.uncurry) (n : ℕ) :
    Continuous (fun a : ℝ => orderedFredholmMinorCoefficient K a n a a) := by
  change Continuous ((fun p : (ℝ × ℝ) × ℝ =>
    orderedFredholmMinorCoefficient K p.2 n p.1.1 p.1.2) ∘
      fun a : ℝ => ((a, a), a))
  exact (continuous_orderedFredholmMinorCoefficient K hK n).comp (by fun_prop)

theorem fredholmIntegrand_snoc
    (K : ℝ → ℝ → ℂ) (n : ℕ) (t : Fin n → ℝ) (a : ℝ) :
    fredholmIntegrand K (n + 1) (Fin.snoc t a) =
      fredholmMinorIntegrand K n a a t := by
  rfl

/-- Each successor determinant coefficient is the aperture integral of its diagonal minor. -/
theorem orderedFredholmCoefficient_succ
    (K : ℝ → ℝ → ℂ) (n : ℕ) (a : ℝ) :
    orderedFredholmCoefficient K a (n + 1) =
      ∫ t in (0 : ℝ)..a, orderedFredholmMinorCoefficient K t n t t := by
  rw [orderedFredholmCoefficient, orderedSimplexIntegral]
  apply intervalIntegral.integral_congr
  intro t ht
  change orderedSimplexIntegral n t
      (fun v => fredholmIntegrand K (n + 1) (Fin.snoc v t)) =
    orderedSimplexIntegral n t (fredholmMinorIntegrand K n t t)
  congr 1

/-- Derivative of one ordered Fredholm coefficient is its diagonal first-minor coefficient. -/
theorem hasDerivAt_orderedFredholmCoefficient_succ
    (K : ℝ → ℝ → ℂ) (n : ℕ) (a : ℝ)
    (hcont : Continuous (fun t : ℝ => orderedFredholmMinorCoefficient K t n t t)) :
    HasDerivAt (fun u => orderedFredholmCoefficient K u (n + 1))
      (orderedFredholmMinorCoefficient K a n a a) a := by
  rw [show (fun u => orderedFredholmCoefficient K u (n + 1)) =
      fun u => ∫ t in (0 : ℝ)..u, orderedFredholmMinorCoefficient K t n t t by
    funext u
    exact orderedFredholmCoefficient_succ K n u]
  exact intervalIntegral.integral_hasDerivAt_right
    (hcont.intervalIntegrable 0 a) (hcont.stronglyMeasurableAtFilter volume (nhds a))
      hcont.continuousAt

/-- Moving-aperture derivative of the complete ordered Fredholm determinant.  The proof is
termwise differentiation on a positive aperture interval, with one shifted Hadamard majorant
uniformly controlling every first-minor derivative. -/
theorem hasDerivAt_orderedDeterminant
    (K : ℝ → ℝ → ℂ) (hKcont : Continuous K.uncurry)
    {a A M : ℝ} (ha : 0 < a) (haA : a < A) (hM : 0 ≤ M)
    (hK : ∀ x ∈ Icc (0 : ℝ) A, ∀ y ∈ Icc (0 : ℝ) A, ‖K x y‖ ≤ M)
    (z : ℂ) :
    HasDerivAt (fun u : ℝ => orderedDeterminant K u z)
      (z * orderedFredholmMinor K a z a a) a := by
  have hA : 0 ≤ A := le_trans ha.le haA.le
  let c : ℝ := max (‖z‖ * M) (‖z‖ * (A * M))
  have hfirst : 0 ≤ ‖z‖ * M := mul_nonneg (norm_nonneg z) hM
  have hsecond : 0 ≤ ‖z‖ * (A * M) :=
    mul_nonneg (norm_nonneg z) (mul_nonneg hA hM)
  have hc : 0 ≤ c := le_max_of_le_left hfirst
  have hfirstc : ‖z‖ * M ≤ c := le_max_left _ _
  have hsecondc : ‖z‖ * (A * M) ≤ c := le_max_right _ _
  have hmajorant : Summable (fun n : ℕ =>
      (Real.sqrt (n + 1) * c) ^ (n + 1) / (n.factorial : ℝ)) :=
    summable_succ_hadamard_majorant c hc
  have hterm : ∀ n : ℕ, ∀ s ∈ Ioo (0 : ℝ) A,
      HasDerivAt
        (fun u : ℝ => z ^ (n + 1) * orderedFredholmCoefficient K u (n + 1))
        (z ^ (n + 1) * orderedFredholmMinorCoefficient K s n s s) s := by
    intro n s hs
    exact (hasDerivAt_orderedFredholmCoefficient_succ K n s
      (continuous_orderedFredholmMinorCoefficient_diagonal K hKcont n)).const_mul
        (z ^ (n + 1))
  have hderivBound : ∀ n : ℕ, ∀ s ∈ Ioo (0 : ℝ) A,
      ‖z ^ (n + 1) * orderedFredholmMinorCoefficient K s n s s‖ ≤
        (Real.sqrt (n + 1) * c) ^ (n + 1) / (n.factorial : ℝ) := by
    intro n s hs
    have hs0 : 0 ≤ s := hs.1.le
    have hsA : s ≤ A := hs.2.le
    have hss : s ∈ Icc (0 : ℝ) s := ⟨hs0, le_rfl⟩
    have hminor := orderedFredholmMinorCoefficient_norm_le K hs0 hM hss hss
      (fun x hx y hy => hK x ⟨hx.1, hx.2.trans hsA⟩ y ⟨hy.1, hy.2.trans hsA⟩) n
    have hsPow : s ^ n ≤ A ^ n := pow_le_pow_left₀ hs0 hsA n
    have hsqrt : 0 ≤ Real.sqrt (n + 1) := Real.sqrt_nonneg _
    rw [norm_mul, norm_pow]
    calc
      ‖z‖ ^ (n + 1) * ‖orderedFredholmMinorCoefficient K s n s s‖
          ≤ ‖z‖ ^ (n + 1) *
              (s ^ n / (n.factorial : ℝ) *
                (Real.sqrt (n + 1) * M) ^ (n + 1)) := by
            gcongr
      _ ≤ ‖z‖ ^ (n + 1) *
              (A ^ n / (n.factorial : ℝ) *
                (Real.sqrt (n + 1) * M) ^ (n + 1)) := by
            gcongr
      _ = (Real.sqrt (n + 1) * (‖z‖ * M)) *
            (Real.sqrt (n + 1) * (‖z‖ * (A * M))) ^ n /
              (n.factorial : ℝ) := by
            rw [pow_succ']
            ring
      _ ≤ (Real.sqrt (n + 1) * c) *
            (Real.sqrt (n + 1) * c) ^ n / (n.factorial : ℝ) := by
            gcongr
      _ = (Real.sqrt (n + 1) * c) ^ (n + 1) / (n.factorial : ℝ) := by
            rw [pow_succ']
  have haMem : a ∈ Ioo (0 : ℝ) A := ⟨ha, haA⟩
  have hKa : ∀ x ∈ Icc (0 : ℝ) a, ∀ y ∈ Icc (0 : ℝ) a, ‖K x y‖ ≤ M := by
    intro x hx y hy
    exact hK x ⟨hx.1, hx.2.trans haA.le⟩ y ⟨hy.1, hy.2.trans haA.le⟩
  have hfullSummable := orderedDeterminant_summable K ha.le hM hKa z
  have htailSummable : Summable (fun n : ℕ =>
      z ^ (n + 1) * orderedFredholmCoefficient K a (n + 1)) := by
    exact (summable_nat_add_iff 1).2 hfullSummable
  have htailDeriv := hasDerivAt_tsum_of_isPreconnected hmajorant isOpen_Ioo
    isPreconnected_Ioo hterm hderivBound haMem htailSummable haMem
  have hminorTsum :
      (∑' n : ℕ, z ^ (n + 1) * orderedFredholmMinorCoefficient K a n a a) =
        z * orderedFredholmMinor K a z a a := by
    rw [orderedFredholmMinor, ← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [pow_succ']
    ring
  rw [hminorTsum] at htailDeriv
  have heq : (fun u : ℝ => orderedDeterminant K u z) =ᶠ[nhds a]
      (fun u : ℝ => 1 + ∑' n : ℕ,
        z ^ (n + 1) * orderedFredholmCoefficient K u (n + 1)) := by
    filter_upwards [isOpen_Ioo.mem_nhds haMem] with s hs
    have hs0 : 0 ≤ s := hs.1.le
    have hKs : ∀ x ∈ Icc (0 : ℝ) s, ∀ y ∈ Icc (0 : ℝ) s, ‖K x y‖ ≤ M := by
      intro x hx y hy
      exact hK x ⟨hx.1, hx.2.trans hs.2.le⟩ y ⟨hy.1, hy.2.trans hs.2.le⟩
    have hsSummable := orderedDeterminant_summable K hs0 hM hKs z
    rw [orderedDeterminant, hsSummable.tsum_eq_zero_add]
    simp [orderedFredholmCoefficient, orderedSimplexIntegral, fredholmIntegrand]
  exact (htailDeriv.const_add 1).congr_of_eventuallyEq heq

end ContinuousKernelFredholm
