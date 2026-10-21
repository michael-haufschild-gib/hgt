import GaloisForLFunctions.RHTower.Sieve.GuthMaynardLagSum

set_option autoImplicit false

/-!
# Sums over affine transformations: the quantity `J(f)` of Guth–Maynard §9

For `f : ℝ → ℝ` and scales `M₁, M₂, M₃` the affine sum is

`A(u) = Σ_{|m₁| ∼ M₁, m₂ ∼ M₂, |m₃| ≤ M₃} f((m₁ u + m₃)/m₂)`,

where `n ∼ M` means `M < n ≤ 2M` (`m₁` of either sign, `m₂` positive). Guth–Maynard
(arXiv 2405.20552, §9) put `J(f) = sup_{0 < M₁, M₂, M₃ < M} ∫ A(u)² du`; the implied constant in
their `|m₃| ≪ M₃` is taken to be one here (other constants are absorbed by changing `M`).

* `affineSum`, `affineEnergy` (`∫ A²`), `affineSup` (`J(f)` at scale `M`);
* `affineSum_eq_posAffineSum_add`: the two signs of `m₁` give `A(u) = A₊(u) + A₊(−u)`, where
  `A₊` sums over positive `m₁ ∼ M₁`;
* `affineEnergy_le_trivial`: the Cauchy–Schwarz bound `∫ A² ≤ 10368 μ⁶ ∫ f²`,
  `μ = max(M₁, M₂, M₃, 1/2)` (the paper's remark "`J(f) ≪ M⁶ ∫ f²`"); it makes `J(f)` finite.
-/

open MeasureTheory Finset

namespace RHTower.GuthMaynard

noncomputable section

/-! ### Index sets -/

/-- Positive integers `n ∼ M`, i.e. `M < n ≤ 2M`. -/
def dyadicNat (M : ℝ) : Finset ℕ :=
  (Finset.range (⌊2 * M⌋₊ + 1)).filter fun n => M < n ∧ (n : ℝ) ≤ 2 * M

theorem mem_dyadicNat {M : ℝ} {n : ℕ} : n ∈ dyadicNat M ↔ M < n ∧ (n : ℝ) ≤ 2 * M := by
  simp only [dyadicNat, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  exact fun h => Nat.lt_succ_of_le (Nat.le_floor h.2)

theorem one_le_of_mem_dyadicNat {M : ℝ} {n : ℕ} (hn : n ∈ dyadicNat M) : 1 ≤ n := by
  rw [mem_dyadicNat] at hn
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp only [Nat.cast_zero] at hn
    linarith [hn.1, hn.2]
  · exact h

/-- A nonempty dyadic range has `M ≥ 1/2`. -/
theorem half_le_of_mem_dyadicNat {M : ℝ} {n : ℕ} (hn : n ∈ dyadicNat M) : 1 / 2 ≤ M := by
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast one_le_of_mem_dyadicNat hn
  linarith [(mem_dyadicNat.mp hn).2]

theorem dyadicNat_eq_empty {M : ℝ} (hM : M < 1 / 2) : dyadicNat M = ∅ :=
  Finset.eq_empty_of_forall_notMem fun _ hn => absurd (half_le_of_mem_dyadicNat hn) (not_le.mpr hM)

/-- `#{n : M < n ≤ 2M} ≤ M + 1`. -/
theorem card_dyadicNat_le {M : ℝ} (hM : 0 ≤ M) : ((dyadicNat M).card : ℝ) ≤ M + 1 := by
  have hsub : dyadicNat M ⊆ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊ := fun n hn => by
    rw [mem_dyadicNat] at hn
    exact Finset.mem_Ioc.mpr ⟨(Nat.floor_lt hM).mpr hn.1, Nat.le_floor hn.2⟩
  have hle : ⌊M⌋₊ ≤ ⌊2 * M⌋₊ := Nat.floor_le_floor (by linarith)
  calc ((dyadicNat M).card : ℝ) ≤ ((Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = (⌊2 * M⌋₊ : ℝ) - ⌊M⌋₊ := by rw [Nat.card_Ioc, Nat.cast_sub hle]
    _ ≤ 2 * M - (M - 1) := by
        have h1 := Nat.floor_le (by linarith : (0 : ℝ) ≤ 2 * M)
        have h2 := Nat.lt_floor_add_one M
        linarith
    _ = M + 1 := by ring

theorem card_dyadicNat_le_three_mul {M : ℝ} (hM : 1 / 2 ≤ M) :
    ((dyadicNat M).card : ℝ) ≤ 3 * M := by
  linarith [card_dyadicNat_le (by linarith : (0 : ℝ) ≤ M)]

/-- `Σ_{n ∼ M} 1/n ≤ 3`. -/
theorem sum_dyadicNat_inv_le {M : ℝ} (hM : 1 / 2 ≤ M) :
    ∑ n ∈ dyadicNat M, (n : ℝ)⁻¹ ≤ 3 := by
  calc ∑ n ∈ dyadicNat M, (n : ℝ)⁻¹ ≤ ∑ _n ∈ dyadicNat M, M⁻¹ :=
        Finset.sum_le_sum fun n hn => inv_anti₀ (by linarith) (mem_dyadicNat.mp hn).1.le
    _ = (dyadicNat M).card * M⁻¹ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (M + 1) * M⁻¹ := by
        gcongr
        exact card_dyadicNat_le (by linarith)
    _ ≤ 3 := by
        rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)]
        linarith

/-- `Σ_{n ∼ M} n ≤ 6 M²`. -/
theorem sum_dyadicNat_le {M : ℝ} (hM : 1 / 2 ≤ M) : ∑ n ∈ dyadicNat M, (n : ℝ) ≤ 6 * M ^ 2 := by
  calc ∑ n ∈ dyadicNat M, (n : ℝ) ≤ ∑ _n ∈ dyadicNat M, 2 * M :=
        Finset.sum_le_sum fun n hn => (mem_dyadicNat.mp hn).2
    _ = (dyadicNat M).card * (2 * M) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (3 * M) * (2 * M) := by
        gcongr
        exact card_dyadicNat_le_three_mul hM
    _ = 6 * M ^ 2 := by ring

/-- Integers `|m| ≤ M`. -/
def centredInt (M : ℝ) : Finset ℤ :=
  Finset.Icc (-⌊M⌋) ⌊M⌋

theorem mem_centredInt {M : ℝ} {m : ℤ} : m ∈ centredInt M ↔ |(m : ℝ)| ≤ M := by
  simp only [centredInt, Finset.mem_Icc, abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : -m ≤ ⌊M⌋ := by omega
    have h4 := Int.le_floor.mp h3
    push_cast at h4
    exact ⟨by linarith, Int.le_floor.mp h2⟩
  · rintro ⟨h1, h2⟩
    have h3 : -m ≤ ⌊M⌋ := Int.le_floor.mpr (by push_cast; linarith)
    exact ⟨by omega, Int.le_floor.mpr h2⟩

/-- `#{m : |m| ≤ M} ≤ 2M + 1`. -/
theorem card_centredInt_le {M : ℝ} (hM : 0 ≤ M) : ((centredInt M).card : ℝ) ≤ 2 * M + 1 := by
  have h0 : 0 ≤ ⌊M⌋ := Int.floor_nonneg.mpr hM
  have hc : ((centredInt M).card : ℤ) = 2 * ⌊M⌋ + 1 := by
    rw [centredInt, Int.card_Icc, Int.toNat_of_nonneg (by omega)]
    ring
  have hc' : ((centredInt M).card : ℝ) = 2 * (⌊M⌋ : ℝ) + 1 := by exact_mod_cast hc
  rw [hc']
  linarith [Int.floor_le M]

/-- Nonzero integers `|m| ∼ M`, i.e. `M < |m| ≤ 2M`. -/
def dyadicInt (M : ℝ) : Finset ℤ :=
  (dyadicNat M).image (fun n : ℕ => (n : ℤ)) ∪ (dyadicNat M).image (fun n : ℕ => -(n : ℤ))

theorem mem_dyadicInt {M : ℝ} {m : ℤ} : m ∈ dyadicInt M ↔ M < |(m : ℝ)| ∧ |(m : ℝ)| ≤ 2 * M := by
  simp only [dyadicInt, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩)
    · simpa [Nat.abs_cast] using mem_dyadicNat.mp hn
    · simpa [Nat.abs_cast] using mem_dyadicNat.mp hn
  · intro h
    have hn : m.natAbs ∈ dyadicNat M := by
      rw [mem_dyadicNat, Nat.cast_natAbs]
      simpa [Int.cast_abs] using h
    rcases Int.natAbs_eq m with hm | hm
    · exact Or.inl ⟨m.natAbs, hn, hm.symm⟩
    · exact Or.inr ⟨m.natAbs, hn, hm.symm⟩

/-- A sum over `|m| ∼ M` is the sum over `n ∼ M` of the two signs. -/
theorem sum_dyadicInt {M : ℝ} (F : ℤ → ℝ) :
    ∑ m ∈ dyadicInt M, F m = ∑ n ∈ dyadicNat M, (F n + F (-n)) := by
  have hdisj : Disjoint ((dyadicNat M).image (fun n : ℕ => (n : ℤ)))
      ((dyadicNat M).image (fun n : ℕ => -(n : ℤ))) := by
    rw [Finset.disjoint_left]
    rintro _ ha hb
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨n', hn', hnn'⟩ := Finset.mem_image.mp hb
    have h1 := one_le_of_mem_dyadicNat hn
    have h2 := one_le_of_mem_dyadicNat hn'
    omega
  rw [dyadicInt, Finset.sum_union hdisj, Finset.sum_image (fun a _ b _ h => by exact_mod_cast h),
    Finset.sum_image (fun a _ b _ h => by simpa using h), ← Finset.sum_add_distrib]

/-! ### The affine sum and `J(f)` -/

/-- `A(u) = Σ_{|m₁| ∼ M₁, m₂ ∼ M₂, |m₃| ≤ M₃} f((m₁ u + m₃)/m₂)`. -/
def affineSum (f : ℝ → ℝ) (M₁ M₂ M₃ u : ℝ) : ℝ :=
  ∑ m₁ ∈ dyadicInt M₁, ∑ m₂ ∈ dyadicNat M₂, ∑ m₃ ∈ centredInt M₃, f ((m₁ * u + m₃) / m₂)

/-- `A₊(u)`: the affine sum over positive `m₁ ∼ M₁`. -/
def posAffineSum (f : ℝ → ℝ) (M₁ M₂ M₃ u : ℝ) : ℝ :=
  ∑ n ∈ dyadicNat M₁, ∑ m₂ ∈ dyadicNat M₂, ∑ m₃ ∈ centredInt M₃, f ((n * u + m₃) / m₂)

/-- `∫ A(u)² du`. -/
def affineEnergy (f : ℝ → ℝ) (M₁ M₂ M₃ : ℝ) : ℝ :=
  ∫ u, affineSum f M₁ M₂ M₃ u ^ 2

/-- The admissible scales `0 < M₁, M₂, M₃ < M`. -/
def affineWindow (M : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {t | 0 < t.1 ∧ t.1 < M ∧ 0 < t.2.1 ∧ t.2.1 < M ∧ 0 < t.2.2 ∧ t.2.2 < M}

/-- Guth–Maynard's `J(f)` at scale `M`: the supremum of `∫ A²` over the admissible scales. -/
def affineSup (f : ℝ → ℝ) (M : ℝ) : ℝ :=
  sSup ((fun t : ℝ × ℝ × ℝ => affineEnergy f t.1 t.2.1 t.2.2) '' affineWindow M)

/-- The largest scale of a triple, floored at `1/2`. -/
def affineScale (M₁ M₂ M₃ : ℝ) : ℝ :=
  max (max M₁ M₂) (max M₃ (1 / 2))

theorem half_le_affineScale (M₁ M₂ M₃ : ℝ) : 1 / 2 ≤ affineScale M₁ M₂ M₃ :=
  le_max_of_le_right (le_max_right _ _)

theorem le_affineScale (M₁ M₂ M₃ : ℝ) :
    M₁ ≤ affineScale M₁ M₂ M₃ ∧ M₂ ≤ affineScale M₁ M₂ M₃ ∧ M₃ ≤ affineScale M₁ M₂ M₃ :=
  ⟨le_max_of_le_left (le_max_left _ _), le_max_of_le_left (le_max_right _ _),
    le_max_of_le_right (le_max_left _ _)⟩

/-- The two signs of `m₁`: `A(u) = A₊(u) + A₊(−u)`. -/
theorem affineSum_eq_posAffineSum_add (f : ℝ → ℝ) (M₁ M₂ M₃ u : ℝ) :
    affineSum f M₁ M₂ M₃ u = posAffineSum f M₁ M₂ M₃ u + posAffineSum f M₁ M₂ M₃ (-u) := by
  rw [affineSum, sum_dyadicInt, Finset.sum_add_distrib, posAffineSum, posAffineSum]
  congr 1
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m₂ _ =>
    Finset.sum_congr rfl fun m₃ _ => ?_
  push_cast
  ring_nf

theorem posAffineSum_nonneg {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (M₁ M₂ M₃ u : ℝ) :
    0 ≤ posAffineSum f M₁ M₂ M₃ u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hf0 _

theorem posAffineSum_le_affineSum {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (M₁ M₂ M₃ u : ℝ) :
    posAffineSum f M₁ M₂ M₃ u ≤ affineSum f M₁ M₂ M₃ u := by
  rw [affineSum_eq_posAffineSum_add]
  linarith [posAffineSum_nonneg hf0 M₁ M₂ M₃ (-u)]

/-! ### Regularity of the affine terms -/

/-- Precomposition with a nondegenerate affine map keeps compact support. -/
theorem hasCompactSupport_comp_affine {f : ℝ → ℝ} (hf : HasCompactSupport f) {a : ℝ} (b : ℝ)
    (ha : a ≠ 0) : HasCompactSupport fun u => f (a * u + b) :=
  hf.comp_homeomorph (affineHomeomorph a b ha)

/-- `u ↦ f((n u + h)/m)` written as an affine precomposition. -/
theorem affine_term_eq (f : ℝ → ℝ) (n m h : ℝ) (hm : m ≠ 0) :
    (fun u => f ((n * u + h) / m)) = fun u => f (n / m * u + h / m) := by
  funext u
  congr 1
  field_simp

theorem continuous_affine_term {f : ℝ → ℝ} (hf : Continuous f) (n m h : ℝ) :
    Continuous fun u => f ((n * u + h) / m) := by
  fun_prop

theorem hasCompactSupport_affine_term {f : ℝ → ℝ} (hfc : HasCompactSupport f) {n m : ℝ}
    (hn : n ≠ 0) (hm : m ≠ 0) (h : ℝ) : HasCompactSupport fun u => f ((n * u + h) / m) := by
  rw [affine_term_eq f n m h hm]
  exact hasCompactSupport_comp_affine hfc _ (div_ne_zero hn hm)

theorem memLp_affine_term {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) {n m : ℝ}
    (hn : n ≠ 0) (hm : m ≠ 0) (h : ℝ) (p : ENNReal) :
    MemLp (fun u => f ((n * u + h) / m)) p :=
  (continuous_affine_term hf n m h).memLp_of_hasCompactSupport
    (hasCompactSupport_affine_term hfc hn hm h)

/-- Change of variables `y = a u + b` on the line. -/
theorem integral_comp_affine (g : ℝ → ℝ) (a b : ℝ) :
    ∫ u, g (a * u + b) = |a⁻¹| * ∫ y, g y := by
  have h := Measure.integral_comp_mul_left (fun y => g (y + b)) a
  rw [h, integral_add_right_eq_self, smul_eq_mul]

/-- `∫ f((n u + h)/m)² du = (m/n) ∫ f²` for `n, m > 0`. -/
theorem integral_affine_term_sq (f : ℝ → ℝ) {n m : ℝ} (hn : 0 < n) (hm : 0 < m) (h : ℝ) :
    ∫ u, f ((n * u + h) / m) ^ 2 = m / n * ∫ y, f y ^ 2 := by
  have hrw : (fun u => f ((n * u + h) / m) ^ 2) = fun u => (fun y => f y ^ 2) (n / m * u + h / m) := by
    funext u
    congr 2
    field_simp
  rw [hrw, integral_comp_affine (fun y => f y ^ 2), inv_div,
    abs_of_pos (div_pos hm hn)]

/-- The positive affine sum is continuous. -/
theorem continuous_posAffineSum {f : ℝ → ℝ} (hf : Continuous f) (M₁ M₂ M₃ : ℝ) :
    Continuous (posAffineSum f M₁ M₂ M₃) := by
  unfold posAffineSum
  exact continuous_finsetSum _ fun n _ => continuous_finsetSum _ fun m₂ _ =>
    continuous_finsetSum _ fun m₃ _ => continuous_affine_term hf _ _ _

/-- The positive affine sum lies in every `Lᵖ`. -/
theorem memLp_posAffineSum {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (M₁ M₂ M₃ : ℝ) (p : ENNReal) : MemLp (posAffineSum f M₁ M₂ M₃) p := by
  have h : posAffineSum f M₁ M₂ M₃ = fun u => ∑ n ∈ dyadicNat M₁, ∑ m₂ ∈ dyadicNat M₂,
      ∑ m₃ ∈ centredInt M₃, f ((n * u + m₃) / m₂) := rfl
  rw [h]
  refine memLp_finsetSum _ fun n hn => memLp_finsetSum _ fun m₂ hm₂ =>
    memLp_finsetSum _ fun m₃ _ => memLp_affine_term hf hfc ?_ ?_ _ p
  · exact Nat.cast_ne_zero.mpr (by have := one_le_of_mem_dyadicNat hn; omega)
  · exact Nat.cast_ne_zero.mpr (by have := one_le_of_mem_dyadicNat hm₂; omega)

theorem memLp_affineSum {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (M₁ M₂ M₃ : ℝ) (p : ENNReal) : MemLp (affineSum f M₁ M₂ M₃) p := by
  have h : affineSum f M₁ M₂ M₃ =
      fun u => posAffineSum f M₁ M₂ M₃ u + posAffineSum f M₁ M₂ M₃ (-u) :=
    funext (affineSum_eq_posAffineSum_add f M₁ M₂ M₃)
  rw [h]
  refine (memLp_posAffineSum hf hfc M₁ M₂ M₃ p).add ?_
  exact (memLp_posAffineSum hf hfc M₁ M₂ M₃ p).comp_measurePreserving (Measure.measurePreserving_neg _)

/-! ### The trivial bound -/

/-- Cauchy–Schwarz over the `#terms` summands: `∫ A₊² ≤ 162 M₁ M₂³ (2M₃+1)² ∫ f²`. -/
theorem integral_posAffineSum_sq_le {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {M₁ M₂ M₃ : ℝ} (hM₁ : 1 / 2 ≤ M₁) (hM₂ : 1 / 2 ≤ M₂) (hM₃ : 0 ≤ M₃) :
    ∫ u, posAffineSum f M₁ M₂ M₃ u ^ 2 ≤
      162 * M₁ * M₂ ^ 3 * (2 * M₃ + 1) ^ 2 * ∫ y, f y ^ 2 := by
  set ι := dyadicNat M₁ ×ˢ (dyadicNat M₂ ×ˢ centredInt M₃) with hι
  let g : ℕ × ℕ × ℤ → ℝ → ℝ := fun p u => f ((p.1 * u + p.2.2) / p.2.1)
  have hsum : ∀ u, posAffineSum f M₁ M₂ M₃ u = ∑ p ∈ ι, g p u := fun u => by
    rw [posAffineSum, hι, Finset.sum_product]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_product]
  have hpos : ∀ p ∈ ι, (0 : ℝ) < p.1 ∧ (0 : ℝ) < p.2.1 := fun p hp => by
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
    obtain ⟨h2, -⟩ := Finset.mem_product.mp h2
    exact ⟨by exact_mod_cast one_le_of_mem_dyadicNat h1, by exact_mod_cast one_le_of_mem_dyadicNat h2⟩
  have hgsq : ∀ p ∈ ι, ∫ u, g p u ^ 2 = (p.2.1 : ℝ) / p.1 * ∫ y, f y ^ 2 := fun p hp =>
    integral_affine_term_sq f (hpos p hp).1 (hpos p hp).2 _
  have hint : ∀ p ∈ ι, Integrable fun u => g p u ^ 2 := fun p hp =>
    (memLp_affine_term hf hfc (hpos p hp).1.ne' (hpos p hp).2.ne' _ 2).integrable_sq
  have hcardι : (ι.card : ℝ) ≤ 3 * M₁ * (3 * M₂) * (2 * M₃ + 1) := by
    rw [hι, Finset.card_product, Finset.card_product]
    push_cast
    have h1 := card_dyadicNat_le_three_mul hM₁
    have h2 := card_dyadicNat_le_three_mul hM₂
    have h3 := card_centredInt_le hM₃
    have h1' : (0 : ℝ) ≤ (dyadicNat M₁).card := Nat.cast_nonneg _
    have h2' : (0 : ℝ) ≤ (dyadicNat M₂).card := Nat.cast_nonneg _
    have h3' : (0 : ℝ) ≤ (centredInt M₃).card := Nat.cast_nonneg _
    calc ((dyadicNat M₁).card : ℝ) * ((dyadicNat M₂).card * (centredInt M₃).card)
        ≤ 3 * M₁ * (3 * M₂ * (2 * M₃ + 1)) := by gcongr
      _ = 3 * M₁ * (3 * M₂) * (2 * M₃ + 1) := by ring
  have hweight : ∑ p ∈ ι, (p.2.1 : ℝ) / p.1 ≤ 3 * (6 * M₂ ^ 2) * (2 * M₃ + 1) := by
    have hfac : ∑ p ∈ ι, (p.2.1 : ℝ) / p.1 = (∑ n ∈ dyadicNat M₁, (n : ℝ)⁻¹) *
        ((∑ m ∈ dyadicNat M₂, (m : ℝ)) * (centredInt M₃).card) := by
      rw [hι, Finset.sum_product, Finset.sum_mul]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.sum_product, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      dsimp only
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    rw [hfac]
    have hS := sum_dyadicNat_le hM₂
    have hC := card_centredInt_le hM₃
    have hI := sum_dyadicNat_inv_le hM₁
    have hS0 : 0 ≤ ∑ m ∈ dyadicNat M₂, (m : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have hI0 : 0 ≤ ∑ n ∈ dyadicNat M₁, (n : ℝ)⁻¹ := Finset.sum_nonneg fun _ _ => by positivity
    calc (∑ n ∈ dyadicNat M₁, (n : ℝ)⁻¹) * ((∑ m ∈ dyadicNat M₂, (m : ℝ)) * (centredInt M₃).card)
        ≤ 3 * ((6 * M₂ ^ 2) * (2 * M₃ + 1)) := by gcongr
      _ = 3 * (6 * M₂ ^ 2) * (2 * M₃ + 1) := by ring
  have hF0 : 0 ≤ ∫ y, f y ^ 2 := integral_nonneg fun _ => sq_nonneg _
  calc ∫ u, posAffineSum f M₁ M₂ M₃ u ^ 2 ≤ ∫ u, (ι.card : ℝ) * ∑ p ∈ ι, g p u ^ 2 := by
        refine integral_mono ((memLp_posAffineSum hf hfc M₁ M₂ M₃ 2).integrable_sq)
          ((integrable_finsetSum _ hint).const_mul _) fun u => ?_
        rw [hsum u]
        exact sq_sum_le_card_mul_sum_sq
    _ = (ι.card : ℝ) * ∑ p ∈ ι, (p.2.1 : ℝ) / p.1 * ∫ y, f y ^ 2 := by
        rw [integral_const_mul, integral_finsetSum _ hint]
        congr 1
        exact Finset.sum_congr rfl hgsq
    _ = (ι.card : ℝ) * (∑ p ∈ ι, (p.2.1 : ℝ) / p.1) * ∫ y, f y ^ 2 := by
        rw [← Finset.sum_mul, mul_assoc]
    _ ≤ (3 * M₁ * (3 * M₂) * (2 * M₃ + 1)) * (3 * (6 * M₂ ^ 2) * (2 * M₃ + 1)) * ∫ y, f y ^ 2 := by
        have hw0 : 0 ≤ ∑ p ∈ ι, (p.2.1 : ℝ) / p.1 := Finset.sum_nonneg fun p hp =>
          div_nonneg (hpos p hp).2.le (hpos p hp).1.le
        gcongr
    _ = 162 * M₁ * M₂ ^ 3 * (2 * M₃ + 1) ^ 2 * ∫ y, f y ^ 2 := by ring

/-- The energy of the full sum is at most four times that of the positive part. -/
theorem affineEnergy_le_four_mul {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (M₁ M₂ M₃ : ℝ) :
    affineEnergy f M₁ M₂ M₃ ≤ 4 * ∫ u, posAffineSum f M₁ M₂ M₃ u ^ 2 := by
  have hA := (memLp_posAffineSum hf hfc M₁ M₂ M₃ 2).integrable_sq
  have hneg : ∫ u, posAffineSum f M₁ M₂ M₃ (-u) ^ 2 = ∫ u, posAffineSum f M₁ M₂ M₃ u ^ 2 :=
    integral_neg_eq_self (fun u => posAffineSum f M₁ M₂ M₃ u ^ 2) _
  have hA' : Integrable fun u => posAffineSum f M₁ M₂ M₃ (-u) ^ 2 := hA.comp_neg
  unfold affineEnergy
  calc ∫ u, affineSum f M₁ M₂ M₃ u ^ 2
      ≤ ∫ u, (2 * posAffineSum f M₁ M₂ M₃ u ^ 2 + 2 * posAffineSum f M₁ M₂ M₃ (-u) ^ 2) := by
        refine integral_mono (memLp_affineSum hf hfc M₁ M₂ M₃ 2).integrable_sq
          ((hA.const_mul 2).add (hA'.const_mul 2)) fun u => ?_
        rw [affineSum_eq_posAffineSum_add]
        nlinarith [sq_nonneg (posAffineSum f M₁ M₂ M₃ u - posAffineSum f M₁ M₂ M₃ (-u))]
    _ = 4 * ∫ u, posAffineSum f M₁ M₂ M₃ u ^ 2 := by
        rw [integral_add (hA.const_mul 2) (hA'.const_mul 2), integral_const_mul, integral_const_mul,
          hneg]
        ring

/-- Unless every range is nonempty, the affine sum vanishes. -/
theorem posAffineSum_eq_zero_of_scales {f : ℝ → ℝ} {M₁ M₂ M₃ : ℝ}
    (h : M₁ < 1 / 2 ∨ M₂ < 1 / 2 ∨ M₃ < 0) (u : ℝ) : posAffineSum f M₁ M₂ M₃ u = 0 := by
  unfold posAffineSum
  rcases h with h | h | h
  · rw [dyadicNat_eq_empty h, Finset.sum_empty]
  · refine Finset.sum_eq_zero fun n _ => ?_
    rw [dyadicNat_eq_empty h, Finset.sum_empty]
  · refine Finset.sum_eq_zero fun n _ => Finset.sum_eq_zero fun m _ => ?_
    have hempty : centredInt M₃ = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun m hm => ?_
      have := mem_centredInt.mp hm
      linarith [abs_nonneg (m : ℝ)]
    rw [hempty, Finset.sum_empty]

theorem affineEnergy_eq_zero_of_scales {f : ℝ → ℝ} {M₁ M₂ M₃ : ℝ}
    (h : M₁ < 1 / 2 ∨ M₂ < 1 / 2 ∨ M₃ < 0) : affineEnergy f M₁ M₂ M₃ = 0 := by
  unfold affineEnergy
  simp [affineSum_eq_posAffineSum_add, posAffineSum_eq_zero_of_scales h]

/-- **The trivial bound** `∫ A² ≤ 10368 μ⁶ ∫ f²`, `μ = max(M₁, M₂, M₃, 1/2)`. -/
theorem affineEnergy_le_trivial {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (M₁ M₂ M₃ : ℝ) :
    affineEnergy f M₁ M₂ M₃ ≤ 10368 * affineScale M₁ M₂ M₃ ^ 6 * ∫ y, f y ^ 2 := by
  have hF0 : 0 ≤ ∫ y, f y ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hμ := half_le_affineScale M₁ M₂ M₃
  obtain ⟨h1, h2, h3⟩ := le_affineScale M₁ M₂ M₃
  by_cases hs : M₁ < 1 / 2 ∨ M₂ < 1 / 2 ∨ M₃ < 0
  · rw [affineEnergy_eq_zero_of_scales hs]
    positivity
  · simp only [not_or, not_lt] at hs
    obtain ⟨hM₁, hM₂, hM₃⟩ := hs
    set μ := affineScale M₁ M₂ M₃
    have h3' : 2 * M₃ + 1 ≤ 4 * μ := by linarith
    calc affineEnergy f M₁ M₂ M₃ ≤ 4 * (162 * M₁ * M₂ ^ 3 * (2 * M₃ + 1) ^ 2 * ∫ y, f y ^ 2) :=
          (affineEnergy_le_four_mul hf hfc M₁ M₂ M₃).trans
            (by gcongr; exact integral_posAffineSum_sq_le hf hfc hM₁ hM₂ hM₃)
      _ ≤ 4 * (162 * μ * μ ^ 3 * (4 * μ) ^ 2 * ∫ y, f y ^ 2) := by
          have : 0 ≤ 2 * M₃ + 1 := by linarith
          gcongr
      _ = 10368 * μ ^ 6 * ∫ y, f y ^ 2 := by ring

theorem affineEnergy_nonneg (f : ℝ → ℝ) (M₁ M₂ M₃ : ℝ) : 0 ≤ affineEnergy f M₁ M₂ M₃ :=
  integral_nonneg fun _ => sq_nonneg _

/-! ### `J(f)` as a supremum -/

theorem affineScale_le_of_mem_affineWindow {M : ℝ} {t : ℝ × ℝ × ℝ} (ht : t ∈ affineWindow M) :
    affineScale t.1 t.2.1 t.2.2 ≤ max M (1 / 2) := by
  obtain ⟨-, h1, -, h2, -, h3⟩ := ht
  unfold affineScale
  refine max_le (max_le ?_ ?_) (max_le ?_ (le_max_right _ _)) <;>
    exact le_max_of_le_left (by linarith)

theorem bddAbove_affineEnergy {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (M : ℝ) :
    BddAbove ((fun t : ℝ × ℝ × ℝ => affineEnergy f t.1 t.2.1 t.2.2) '' affineWindow M) := by
  refine ⟨10368 * max M (1 / 2) ^ 6 * ∫ y, f y ^ 2, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have hF0 : 0 ≤ ∫ y, f y ^ 2 := integral_nonneg fun _ => sq_nonneg _
  refine (affineEnergy_le_trivial hf hfc _ _ _).trans ?_
  have h0 : 0 ≤ affineScale t.1 t.2.1 t.2.2 := by linarith [half_le_affineScale t.1 t.2.1 t.2.2]
  have := affineScale_le_of_mem_affineWindow ht
  gcongr

/-- Each admissible energy is at most `J(f)`. -/
theorem affineEnergy_le_affineSup {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {M M₁ M₂ M₃ : ℝ} (h : (M₁, M₂, M₃) ∈ affineWindow M) :
    affineEnergy f M₁ M₂ M₃ ≤ affineSup f M :=
  le_csSup (bddAbove_affineEnergy hf hfc M) ⟨(M₁, M₂, M₃), h, rfl⟩

/-- A bound for every admissible energy bounds `J(f)`. -/
theorem affineSup_le {f : ℝ → ℝ} {M X : ℝ} (hM : 0 < M)
    (h : ∀ t ∈ affineWindow M, affineEnergy f t.1 t.2.1 t.2.2 ≤ X) : affineSup f M ≤ X := by
  refine csSup_le ⟨_, (M / 2, M / 2, M / 2), ?_, rfl⟩ ?_
  · exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact h t ht

end

end RHTower.GuthMaynard
