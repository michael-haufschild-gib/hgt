import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHorizonCountertermIsBlindToResidueClasses

/-!
# The horizon sees only the mean of a class function

Twist a uniform step profile `Σ_i c_i u^{(M_i)}` by a function `f` of `n mod q` on the units. The
rank-one residue law (`exists_abs_atomicWeilForm_unitClassProfile_sub_le`) turns the horizon
divergence of the twisted profile into a single number.

* **The class-function law** (`exists_abs_atomicWeilForm_classFunctionProfile_sub_le`):
  `P_N(x) = κ_f (Σ_i c_i log M_i)² + O((1 + log N)(Σ_i |c_i|)²)` with
  `κ_f = (Σ_{a ∈ (ℤ/q)ˣ} f(a))²/(q φ(q)) = (φ(q)/q) ⟨f⟩²`, `⟨f⟩` the mean of `f` over the units.
  The polar functional of the twisted profile is `(Σ_a f(a)/q) Σ_i c_i log M_i + O(Σ_i |c_i|)`,
  because every unit class carries `log M/q + O(q)` of the harmonic sum.
* **Characters of every modulus are invisible** (`exists_abs_atomicWeilForm_charRe_le`,
  `exists_abs_atomicWeilForm_charIm_le`): for a Dirichlet character `χ ≠ 1` mod `q`, the profiles
  `Re χ(n) Σ_i c_i u^{(M_i)}_n` and `Im χ(n) Σ_i c_i u^{(M_i)}_n` have
  `|P_N(x)| ≤ K (1 + log N) (Σ_i |c_i|)²`: no `(log N)²` divergence.

For `f = 1` the law gives `κ = φ(q)/q`, the density of the units: the sieved pole has divergence
`(φ(q)/q) ℓ₀²`, the inverse-density weight `δ^{−1} ℓ_u²` of the tensor law with `ℓ_u ≈ δ ℓ₀`. Any
`f` of mean zero on the units — every character `χ ≠ 1`, real or complex, of every modulus — is
annihilated. This extends the matching coefficient `0` of real characters mod a prime from the
gauge picture to all moduli, and it needs only orthogonality on top of the residue law: the
horizon reads the mean of a class function and nothing else.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics

variable {q : ℕ} [NeZero q]

/-- The **class-function profile** `x = Σ_{a ∈ (ℤ/q)ˣ} Σ_i f(a) c_i w_a^{(M_i)}`: the step profile
`Σ_i c_i u^{(M_i)}` twisted by `f(n mod q)` on the units. -/
def classFunctionProfile (q : ℕ) [NeZero q] (f : ZMod q → ℝ) {k : ℕ} (c : Fin k → ℝ)
    (M : Fin k → ℕ) : ℕ → ℝ :=
  unitClassProfile q (fun α => f α.1 * c α.2) M

/-- A function vanishing off the units twists the step profile pointwise:
`classFunctionProfile q g c M n = g(n) Σ_i c_i u^{(M_i)}_n`. -/
theorem classFunctionProfile_eq {g : ZMod q → ℝ} (hg : ∀ a, ¬ IsUnit a → g a = 0) {k : ℕ}
    (c : Fin k → ℝ) (M : Fin k → ℕ) (n : ℕ) :
    classFunctionProfile q g c M n = g n * stepProfile c M n := by
  rw [classFunctionProfile, unitClassProfile, Fintype.sum_prod_type]
  by_cases hn : IsUnit (n : ZMod q)
  · rw [sum_eq_single hn.unit]
    · simp only [residuePole, IsUnit.unit_spec, if_true, stepProfile, mul_sum]
      exact sum_congr rfl fun i _ => by ring
    · intro u _ hu
      refine sum_eq_zero fun i _ => ?_
      have hne : (n : ZMod q) ≠ u := fun h => hu (Units.ext (by rw [IsUnit.unit_spec, h]))
      simp [residuePole, hne]
    · simp
  · rw [hg _ hn, zero_mul]
    refine sum_eq_zero fun u _ => sum_eq_zero fun i _ => ?_
    have hne : (n : ZMod q) ≠ u := fun h => hn (h ▸ u.isUnit)
    simp [residuePole, hne]

/-- **The polar functional of a class-function profile**:
`|ℓ(x) − (Σ_a f(a)/q) Σ_i c_i log M_i| ≤ (2q + 1) (Σ_a |f(a)|) (Σ_i |c_i|)`. -/
theorem abs_polarFunctional_classFunctionProfile_sub_le (f : ZMod q → ℝ) {k N : ℕ}
    (c : Fin k → ℝ) (M : Fin k → ℕ) (hM : ∀ i, M i ≤ N) :
    |polarFunctional N (classFunctionProfile q f c M) -
        (∑ a : (ZMod q)ˣ, f a) / q * ∑ i, c i * Real.log (M i)| ≤
      (2 * q + 1) * (∑ a : (ZMod q)ˣ, |f a|) * ∑ i, |c i| := by
  rw [classFunctionProfile, polarFunctional_unitClassProfile _ M hM]
  -- the main term is the sum of the class means `log M_i/q`
  have hmain : (∑ a : (ZMod q)ˣ, f a) / q * ∑ i, c i * Real.log (M i) =
      ∑ α : (ZMod q)ˣ × Fin k, f α.1 * c α.2 * (Real.log (M α.2) / q) := by
    rw [Fintype.sum_prod_type, div_mul_eq_mul_div, sum_mul_sum, sum_div]
    exact sum_congr rfl fun a _ => by rw [sum_div]; exact sum_congr rfl fun i _ => by ring
  rw [hmain, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ α : (ZMod q)ˣ × Fin k,
        |f α.1 * c α.2 * classHarmonic q α.1 (M α.2) - f α.1 * c α.2 * (Real.log (M α.2) / q)|
      ≤ ∑ α : (ZMod q)ˣ × Fin k, |f α.1| * |c α.2| * (2 * q + 1) := by
        refine sum_le_sum fun α _ => ?_
        rw [← mul_sub, abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_classHarmonic_sub_log_le _ _) (by positivity)
    _ = (2 * q + 1) * (∑ a : (ZMod q)ˣ, |f a|) * ∑ i, |c i| := by
        rw [Fintype.sum_prod_type, mul_assoc, sum_mul_sum, mul_sum]
        exact sum_congr rfl fun a _ => by rw [mul_sum]; exact sum_congr rfl fun i _ => by ring

/-- **The class-function law**: there is `K` such that for every uniform step profile with
`1 ≤ M_i ≤ N`, `|P_N(x) − κ_f (Σ_i c_i log M_i)²| ≤ K (1 + log N) (Σ_i |c_i|)²` for the twisted
profile `x`, with `κ_f = (Σ_{a ∈ (ℤ/q)ˣ} f(a))²/(q φ(q))`. -/
theorem exists_abs_atomicWeilForm_classFunctionProfile_sub_le (f : ZMod q → ℝ) :
    ∃ K : ℝ, ∀ {k N : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ), (∀ i, M i ≤ N) → (∀ i, 1 ≤ M i) →
      |atomicWeilForm N (classFunctionProfile q f c M) -
          (∑ a : (ZMod q)ˣ, f a) ^ 2 / (q * q.totient) * (∑ i, c i * Real.log (M i)) ^ 2| ≤
        K * (1 + Real.log N) * (∑ i, |c i|) ^ 2 := by
  obtain ⟨K, hK⟩ := exists_abs_atomicWeilForm_unitClassProfile_sub_le (q := q)
  set F := ∑ a : (ZMod q)ˣ, |f a| with hFdef
  refine ⟨(|K| + q * (2 * q + 1) ^ 2) * F ^ 2, fun {k N} c M hM hM1 => ?_⟩
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hφ : (1 : ℝ) ≤ q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hF : 0 ≤ F := sum_nonneg fun _ _ => abs_nonneg _
  set C := ∑ i, |c i| with hCdef
  have hC : 0 ≤ C := sum_nonneg fun _ _ => abs_nonneg _
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  set X := 1 + Real.log N with hXdef
  set ℓ := polarFunctional N (classFunctionProfile q f c M)
  set Λ₀ := ∑ i, c i * Real.log (M i)
  set m := (∑ a : (ZMod q)ˣ, f a) / q with hmdef
  -- the residue law and its mass
  have h1 := hK (fun α => f α.1 * c α.2) M hM hM1
  have hmass : ∑ α : (ZMod q)ˣ × Fin k, ∑ β : (ZMod q)ˣ × Fin k,
      |f α.1 * c α.2| * |f β.1 * c β.2| * harmonicSum (min (M α.2) (M β.2)) ≤ F ^ 2 * C ^ 2 * X := by
    have hH : ∀ α β : (ZMod q)ˣ × Fin k, harmonicSum (min (M α.2) (M β.2)) ≤ X := fun α β =>
      (harmonicSum_mono ((min_le_left _ _).trans (hM α.2))).trans (harmonicSum_le N)
    have hsum : ∑ α : (ZMod q)ˣ × Fin k, |f α.1 * c α.2| = F * C := by
      rw [Fintype.sum_prod_type, hFdef, hCdef, sum_mul_sum]
      exact sum_congr rfl fun a _ => sum_congr rfl fun i _ => abs_mul _ _
    calc _ ≤ ∑ α : (ZMod q)ˣ × Fin k, ∑ β : (ZMod q)ˣ × Fin k,
          |f α.1 * c α.2| * |f β.1 * c β.2| * X :=
          sum_le_sum fun α _ => sum_le_sum fun β _ =>
            mul_le_mul_of_nonneg_left (hH α β) (by positivity)
      _ = (∑ α : (ZMod q)ˣ × Fin k, |f α.1 * c α.2|) ^ 2 * X := by
          rw [sq, sum_mul_sum, sum_mul]
          exact sum_congr rfl fun α _ => by rw [sum_mul]
      _ = F ^ 2 * C ^ 2 * X := by rw [hsum]; ring
  have hA : |atomicWeilForm N (classFunctionProfile q f c M) - (q : ℝ) / q.totient * ℓ ^ 2| ≤
      |K| * (F ^ 2 * C ^ 2 * X) := by
    refine h1.trans ?_
    have hS : 0 ≤ ∑ α : (ZMod q)ˣ × Fin k, ∑ β : (ZMod q)ˣ × Fin k,
        |f α.1 * c α.2| * |f β.1 * c β.2| * harmonicSum (min (M α.2) (M β.2)) :=
      sum_nonneg fun α _ => sum_nonneg fun β _ =>
        mul_nonneg (by positivity) (harmonicSum_nonneg _)
    exact (mul_le_mul_of_nonneg_right (le_abs_self K) hS).trans
      (mul_le_mul_of_nonneg_left hmass (abs_nonneg K))
  -- the polar square against its main term
  have hR : |ℓ - m * Λ₀| ≤ (2 * q + 1) * F * C :=
    abs_polarFunctional_classFunctionProfile_sub_le f c M hM
  have hΛ : |Λ₀| ≤ C * Real.log N := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [hCdef, sum_mul]
    refine sum_le_sum fun i _ => ?_
    have hMi : (1 : ℝ) ≤ M i := by exact_mod_cast hM1 i
    rw [abs_mul, abs_of_nonneg (Real.log_nonneg hMi)]
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (by linarith) (by exact_mod_cast hM i)) (abs_nonneg _)
  have hm : |m| ≤ F := by
    rw [hmdef, abs_div, abs_of_pos hq, div_le_iff₀ hq]
    exact (abs_sum_le_sum_abs _ _).trans (le_mul_of_one_le_right hF hq1)
  have hsq : |ℓ ^ 2 - (m * Λ₀) ^ 2| ≤
      (2 * q + 1) * F * C * (2 * F * (C * Real.log N) + (2 * q + 1) * F * C) := by
    have hplus : |ℓ + m * Λ₀| ≤ 2 * F * (C * Real.log N) + (2 * q + 1) * F * C := by
      have hmΛ : |m * Λ₀| ≤ F * (C * Real.log N) := by
        rw [abs_mul]; exact mul_le_mul hm hΛ (abs_nonneg _) hF
      calc |ℓ + m * Λ₀| = |(ℓ - m * Λ₀) + 2 * (m * Λ₀)| := by ring_nf
        _ ≤ |ℓ - m * Λ₀| + 2 * |m * Λ₀| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_two]
        _ ≤ _ := by linarith
    rw [sq_sub_sq, abs_mul, mul_comm]
    exact mul_le_mul hR hplus (abs_nonneg _) (by positivity)
  have hT : (∑ a : (ZMod q)ˣ, f a) ^ 2 / (q * q.totient) * Λ₀ ^ 2 =
      (q : ℝ) / q.totient * (m * Λ₀) ^ 2 := by
    rw [hmdef]; field_simp
  have hB : (q : ℝ) / q.totient * |ℓ ^ 2 - (m * Λ₀) ^ 2| ≤ q * (2 * q + 1) ^ 2 * F ^ 2 * C ^ 2 * X := by
    have hqφ : (q : ℝ) / q.totient ≤ q := div_le_self hq.le hφ
    have hpoly : (2 * q + 1) * F * C * (2 * F * (C * Real.log N) + (2 * q + 1) * F * C) ≤
        (2 * q + 1) ^ 2 * F ^ 2 * C ^ 2 * X := by
      have hFC : 0 ≤ (2 * q + 1) * F ^ 2 * C ^ 2 := by positivity
      have : 2 * Real.log N + (2 * q + 1) ≤ (2 * q + 1) * X := by rw [hXdef]; nlinarith
      calc (2 * q + 1) * F * C * (2 * F * (C * Real.log N) + (2 * q + 1) * F * C)
          = (2 * q + 1) * F ^ 2 * C ^ 2 * (2 * Real.log N + (2 * q + 1)) := by ring
        _ ≤ (2 * q + 1) * F ^ 2 * C ^ 2 * ((2 * q + 1) * X) :=
            mul_le_mul_of_nonneg_left this hFC
        _ = _ := by ring
    calc (q : ℝ) / q.totient * |ℓ ^ 2 - (m * Λ₀) ^ 2|
        ≤ q * ((2 * q + 1) ^ 2 * F ^ 2 * C ^ 2 * X) :=
          mul_le_mul hqφ (hsq.trans hpoly) (abs_nonneg _) hq.le
      _ = _ := by ring
  rw [hT]
  calc |atomicWeilForm N (classFunctionProfile q f c M) - (q : ℝ) / q.totient * (m * Λ₀) ^ 2|
      = |(atomicWeilForm N (classFunctionProfile q f c M) - (q : ℝ) / q.totient * ℓ ^ 2) +
          (q : ℝ) / q.totient * (ℓ ^ 2 - (m * Λ₀) ^ 2)| := by ring_nf
    _ ≤ |K| * (F ^ 2 * C ^ 2 * X) + (q : ℝ) / q.totient * |ℓ ^ 2 - (m * Λ₀) ^ 2| := by
        refine (abs_add_le _ _).trans (add_le_add hA ?_)
        rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ |K| * (F ^ 2 * C ^ 2 * X) + q * (2 * q + 1) ^ 2 * F ^ 2 * C ^ 2 * X := by linarith
    _ = (|K| + q * (2 * q + 1) ^ 2) * F ^ 2 * X * C ^ 2 := by ring

/-- `Σ_{u ∈ (ℤ/q)ˣ} χ(u) = 0` for a non-trivial character. -/
theorem sum_units_char_eq_zero (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∑ u : (ZMod q)ˣ, χ u = 0 := by
  calc ∑ u : (ZMod q)ˣ, χ u
      = ∑ a ∈ univ.map ⟨((↑) : (ZMod q)ˣ → ZMod q), Units.val_injective⟩, χ a :=
        (sum_map univ ⟨((↑) : (ZMod q)ˣ → ZMod q), Units.val_injective⟩ fun a => χ a).symm
    _ = ∑ a, χ a := sum_subset (subset_univ _) fun a _ ha =>
        MulChar.map_nonunit χ fun hu => ha (mem_map.mpr ⟨hu.unit, mem_univ _, hu.unit_spec⟩)
    _ = 0 := MulChar.sum_eq_zero_of_ne_one hχ

/-- **The real part of a character is invisible**: for `χ ≠ 1` mod `q` the profile
`Re χ(n) Σ_i c_i u^{(M_i)}_n` has `|P_N(x)| ≤ K (1 + log N) (Σ_i |c_i|)²`. -/
theorem exists_abs_atomicWeilForm_charRe_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ K : ℝ, ∀ {k N : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ), (∀ i, M i ≤ N) → (∀ i, 1 ≤ M i) →
      |atomicWeilForm N (fun n : ℕ => (χ (n : ZMod q)).re * stepProfile c M n)| ≤
        K * (1 + Real.log N) * (∑ i, |c i|) ^ 2 := by
  obtain ⟨K, hK⟩ := exists_abs_atomicWeilForm_classFunctionProfile_sub_le (q := q)
    (fun a => (χ a).re)
  refine ⟨K, fun c M hM hM1 => ?_⟩
  have hzero : ∑ a : (ZMod q)ˣ, (χ a).re = 0 := by
    rw [← Complex.re_sum, sum_units_char_eq_zero χ hχ, Complex.zero_re]
  have hprof : (fun n : ℕ => (χ (n : ZMod q)).re * stepProfile c M n) =
      classFunctionProfile q (fun a => (χ a).re) c M :=
    funext fun n => (classFunctionProfile_eq (g := fun a => (χ a).re) (fun a ha => by
      show (χ a).re = 0
      rw [MulChar.map_nonunit χ ha, Complex.zero_re]) c M n).symm
  have h := hK c M hM hM1
  rwa [hzero, zero_pow two_ne_zero, zero_div, zero_mul, sub_zero, ← hprof] at h

/-- **The imaginary part of a character is invisible**: for `χ ≠ 1` mod `q` the profile
`Im χ(n) Σ_i c_i u^{(M_i)}_n` has `|P_N(x)| ≤ K (1 + log N) (Σ_i |c_i|)²`. -/
theorem exists_abs_atomicWeilForm_charIm_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ K : ℝ, ∀ {k N : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ), (∀ i, M i ≤ N) → (∀ i, 1 ≤ M i) →
      |atomicWeilForm N (fun n : ℕ => (χ (n : ZMod q)).im * stepProfile c M n)| ≤
        K * (1 + Real.log N) * (∑ i, |c i|) ^ 2 := by
  obtain ⟨K, hK⟩ := exists_abs_atomicWeilForm_classFunctionProfile_sub_le (q := q)
    (fun a => (χ a).im)
  refine ⟨K, fun c M hM hM1 => ?_⟩
  have hzero : ∑ a : (ZMod q)ˣ, (χ a).im = 0 := by
    rw [← Complex.im_sum, sum_units_char_eq_zero χ hχ, Complex.zero_im]
  have hprof : (fun n : ℕ => (χ (n : ZMod q)).im * stepProfile c M n) =
      classFunctionProfile q (fun a => (χ a).im) c M :=
    funext fun n => (classFunctionProfile_eq (g := fun a => (χ a).im) (fun a ha => by
      show (χ a).im = 0
      rw [MulChar.map_nonunit χ ha, Complex.zero_im]) c M n).symm
  have h := hK c M hM hM1
  rwa [hzero, zero_pow two_ne_zero, zero_div, zero_mul, sub_zero, ← hprof] at h

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
