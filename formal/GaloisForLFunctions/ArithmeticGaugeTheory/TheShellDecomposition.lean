import GaloisForLFunctions.ArithmeticGaugeTheory.TheDivisorCollapse

/-!
# The shell decomposition of the prime pair form

On atomic families the prime part of Weil's form pairs an atom at `log m`, a prime power `k` and an
atom at `log n` through a kernel of the lag `log n − log m − log k`. For any kernel `G` write
`P(a, x) = Σ_{k ≤ K} Σ_{m, n ≤ N} a(k) x(m) x̄(n) G(log n − log m − log k)` (`primePairForm`). This file
splits `P` by the additive relation between `n` and the product `km`.

* **Convolved form** (`primePairForm_eq_convolved`). Grouping by `ℓ = km`,
  `P(a, x) = Σ_ℓ Σ_n (a ⋆ x)(ℓ) x̄(n) G(log n − log ℓ)`, where `a ⋆ x` is the truncated Dirichlet
  convolution (`truncConv`). The prime form is a bilinear form of the convolved source against `x`,
  with a kernel of `log(n/ℓ)` alone. The pairs `n = ℓ + j`, `j ≠ 0`, are the successor shells.
* **Ratio part and shells** (`primePairForm_eq_ratioPart_add_shellPart`). The pairs `n = km` (ratio
  lags, kernel value `G(0)`) form the ratio part; all other pairs form the shell part.
* **Gauge action** (`gaugeTransform`). A gauge point `y` acts on weights and vectors at once:
  `a ↦ a χ_y`, `x ↦ x χ_y`. The convolution is covariant, `(aχ ⋆ xχ)(ℓ) = χ(ℓ) (a ⋆ x)(ℓ)`
  (`truncConv_gaugeTransform`); the ratio part is gauge invariant (`ratioPart_gaugeTransform`); the
  shell part has gauge mean zero (`integral_shellPart_gaugeTransform`).
* **The gauge average is the ratio part** (`integral_primePairForm_gaugeTransform`). Averaging the
  gauge-transformed form over Haar measure deletes every shell. Whatever the shells contribute to the
  form at a given gauge point is gauge charge; at a Haar-typical point it averages away.
* **The pole vector collapses** (`truncConv_poleVector`, `truncConv_poleVector_trivial`). On the
  constant vector the convolved source is the divisor fibre `F_y(ℓ)`, and at the trivial point it
  is `log ℓ`. The shells of the pole direction read the archimedean absolute value of the product.

So the additive structure enters the prime form only through successor correlations of the convolved
source, and the one point at which these correlations are determined by structure is the trivial
point, through `Λ * 1 = log`.
-/

open MeasureTheory Finset ArithmeticFunction
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

variable (K N : ℕ) (a x : ℕ → ℂ) (G : ℝ → ℂ)

/-- The prime pair form `Σ_{k ≤ K} Σ_{m, n ≤ N} a(k) x(m) x̄(n) G(log n − log m − log k)`. -/
def primePairForm : ℂ :=
  ∑ k ∈ Icc 1 K, ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
    a k * x m * conj (x n) * G (Real.log n - Real.log m - Real.log k)

/-- The ratio part: the pairs with `n = km`, where the lag vanishes. -/
def ratioPart : ℂ :=
  ∑ k ∈ Icc 1 K, ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
    if n = k * m then a k * x m * conj (x n) * G 0 else 0

/-- The shell part: the pairs with `n ≠ km`. -/
def shellPart : ℂ :=
  ∑ k ∈ Icc 1 K, ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
    if n = k * m then 0 else a k * x m * conj (x n) * G (Real.log n - Real.log m - Real.log k)

/-- The truncated Dirichlet convolution `(a ⋆ x)(ℓ) = Σ_{km = ℓ, k ≤ K, m ≤ N} a(k) x(m)`. -/
def truncConv (ℓ : ℕ) : ℂ :=
  ∑ p ∈ (Icc 1 K ×ˢ Icc 1 N).filter (fun p => p.1 * p.2 = ℓ), a p.1 * x p.2

/-- The gauge transform of a coefficient system by a gauge point. -/
def gaugeTransform (y : GaugeTorus) (v : ℕ → ℂ) : ℕ → ℂ := fun n => v n * twist y n

theorem log_mul_of_mem_Icc {k m : ℕ} (hk : k ∈ Icc 1 K) (hm : m ∈ Icc 1 N) :
    Real.log ((k * m : ℕ) : ℝ) = Real.log k + Real.log m := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hk).1)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hm).1)
  rw [Nat.cast_mul, Real.log_mul hk0 hm0]

/-! ### Ratio lags and shells -/

/-- **Ratio part plus shells.** -/
theorem primePairForm_eq_ratioPart_add_shellPart :
    primePairForm K N a x G = ratioPart K N a x G + shellPart K N a x G := by
  simp only [primePairForm, ratioPart, shellPart, ← sum_add_distrib]
  refine sum_congr rfl fun k hk => sum_congr rfl fun m hm => sum_congr rfl fun n _ => ?_
  split_ifs with h
  · subst h
    rw [log_mul_of_mem_Icc K N hk hm]
    ring_nf
  · rw [zero_add]

/-- **The convolved form.** Grouping the pairs `(k, m)` by their product `ℓ = km`, the prime form is
the bilinear form of the convolved source `a ⋆ x` against `x` with kernel `G(log n − log ℓ)`. -/
theorem primePairForm_eq_convolved :
    primePairForm K N a x G = ∑ ℓ ∈ Icc 1 (K * N), ∑ n ∈ Icc 1 N,
      truncConv K N a x ℓ * conj (x n) * G (Real.log n - Real.log ℓ) := by
  have hmaps : ∀ p ∈ Icc 1 K ×ˢ Icc 1 N, p.1 * p.2 ∈ Icc 1 (K * N) := by
    intro p hp
    obtain ⟨hk, hm⟩ := mem_product.mp hp
    rw [mem_Icc] at hk hm ⊢
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
      Nat.mul_le_mul hk.2 hm.2⟩
  -- Write the form as one sum over pairs `p = (k, m)`, with lag `log n − log(km)`.
  have hpairs : primePairForm K N a x G = ∑ p ∈ Icc 1 K ×ˢ Icc 1 N, ∑ n ∈ Icc 1 N,
      a p.1 * x p.2 * conj (x n) * G (Real.log n - Real.log ((p.1 * p.2 : ℕ) : ℝ)) := by
    rw [primePairForm, sum_product]
    refine sum_congr rfl fun k hk => sum_congr rfl fun m hm => sum_congr rfl fun n _ => ?_
    rw [log_mul_of_mem_Icc K N hk hm]
    ring_nf
  rw [hpairs, ← sum_fiberwise_of_maps_to hmaps]
  refine sum_congr rfl fun ℓ _ => ?_
  rw [sum_comm, truncConv]
  refine sum_congr rfl fun n _ => ?_
  rw [sum_mul, sum_mul]
  refine sum_congr rfl fun p hp => ?_
  rw [(mem_filter.mp hp).2]

/-! ### The gauge action -/

/-- **Gauge covariance of the convolution.** -/
theorem truncConv_gaugeTransform (y : GaugeTorus) (ℓ : ℕ) :
    truncConv K N (gaugeTransform y a) (gaugeTransform y x) ℓ = twist y ℓ * truncConv K N a x ℓ := by
  rw [truncConv, truncConv, mul_sum]
  refine sum_congr rfl fun p hp => ?_
  obtain ⟨hpq, hprod⟩ := mem_filter.mp hp
  obtain ⟨hk, hm⟩ := mem_product.mp hpq
  have hk0 : p.1 ≠ 0 := Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hk).1
  have hm0 : p.2 ≠ 0 := Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hm).1
  rw [gaugeTransform, gaugeTransform, ← hprod, twist_mul y hk0 hm0]
  ring

/-- **The ratio part is gauge invariant.** -/
theorem ratioPart_gaugeTransform (y : GaugeTorus) :
    ratioPart K N (gaugeTransform y a) (gaugeTransform y x) G = ratioPart K N a x G := by
  refine sum_congr rfl fun k hk => sum_congr rfl fun m hm => sum_congr rfl fun n _ => ?_
  split_ifs with h
  · subst h
    have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hk).1
    have hm0 : m ≠ 0 := Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hm).1
    have hunit := twist_mul_conj_self y (k * m)
    rw [twist_mul y hk0 hm0] at hunit
    simp only [gaugeTransform, map_mul]
    rw [twist_mul y hk0 hm0]
    linear_combination (a k * x m * conj (x (k * m)) * G 0) * hunit
  · rfl

/-- One shell term of the gauge-transformed form, as a multiple of a twist pair. -/
theorem shellTerm_gaugeTransform (y : GaugeTorus) {k m : ℕ} (hk : k ≠ 0) (hm : m ≠ 0) (n : ℕ)
    (c : ℂ) :
    gaugeTransform y a k * gaugeTransform y x m * conj (gaugeTransform y x n) * c =
      a k * x m * conj (x n) * c * (twist y (k * m) * conj (twist y n)) := by
  simp only [gaugeTransform, map_mul]
  rw [twist_mul y hk hm]
  ring

/-- The coefficient of the twist pair `χ(km) χ̄(n)` in the shell part. -/
def shellCoeff (k m n : ℕ) : ℂ :=
  if n = k * m then 0 else a k * x m * conj (x n) * G (Real.log n - Real.log m - Real.log k)

/-- The gauge-transformed shell part is a combination of twist pairs `χ(km) χ̄(n)`, `n ≠ km`. -/
theorem shellPart_gaugeTransform_eq (y : GaugeTorus) :
    shellPart K N (gaugeTransform y a) (gaugeTransform y x) G =
      ∑ k ∈ Icc 1 K, ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        shellCoeff a x G k m n * (twist y (k * m) * conj (twist y n)) := by
  refine sum_congr rfl fun k hk => sum_congr rfl fun m hm => sum_congr rfl fun n _ => ?_
  rw [shellCoeff]
  split_ifs
  · rw [zero_mul]
  · exact shellTerm_gaugeTransform a x y (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hk).1)
      (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hm).1) n _

theorem integrable_shellTerm (k m n : ℕ) :
    Integrable (fun y : GaugeTorus =>
      shellCoeff a x G k m n * (twist y (k * m) * conj (twist y n))) gaugeHaar :=
  (integrable_twist_mul_conj (k * m) n).const_mul _

theorem integrable_shellPart_gaugeTransform :
    Integrable (fun y => shellPart K N (gaugeTransform y a) (gaugeTransform y x) G) gaugeHaar := by
  simp_rw [shellPart_gaugeTransform_eq]
  exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun m _ =>
    integrable_finsetSum _ fun n _ => integrable_shellTerm a x G k m n

/-- **The shells are gauge charge.** The shell part of the gauge-transformed form has Haar mean
zero. -/
theorem integral_shellPart_gaugeTransform :
    ∫ y, shellPart K N (gaugeTransform y a) (gaugeTransform y x) G ∂gaugeHaar = 0 := by
  simp_rw [shellPart_gaugeTransform_eq]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun m _ =>
    integrable_finsetSum _ fun n _ => integrable_shellTerm a x G k m n]
  refine sum_eq_zero fun k hk => ?_
  rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ =>
    integrable_shellTerm a x G k m n]
  refine sum_eq_zero fun m hm => ?_
  rw [integral_finsetSum _ fun n _ => integrable_shellTerm a x G k m n]
  refine sum_eq_zero fun n hn => ?_
  have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hk).1
  have hm0 : m ≠ 0 := Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hm).1
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hn).1
  rw [integral_const_mul, integral_twist_mul_conj (Nat.mul_ne_zero hk0 hm0) hn0]
  by_cases h : n = k * m
  · rw [shellCoeff, if_pos h, zero_mul]
  · rw [if_neg (fun h' => h h'.symm), mul_zero]

/-- **The gauge average of the prime form is its ratio part.** -/
theorem integral_primePairForm_gaugeTransform :
    ∫ y, primePairForm K N (gaugeTransform y a) (gaugeTransform y x) G ∂gaugeHaar =
      ratioPart K N a x G := by
  have hsplit : (fun y => primePairForm K N (gaugeTransform y a) (gaugeTransform y x) G) =
      fun y => ratioPart K N a x G + shellPart K N (gaugeTransform y a) (gaugeTransform y x) G := by
    funext y
    rw [primePairForm_eq_ratioPart_add_shellPart, ratioPart_gaugeTransform]
  rw [hsplit, integral_add (integrable_const _) (integrable_shellPart_gaugeTransform K N a x G),
    integral_shellPart_gaugeTransform, add_zero, integral_const, probReal_univ, one_smul]

/-! ### The pole vector -/

/-- **The pole vector collapses to the divisor fibre.** For `1 ≤ ℓ ≤ min(K, N)` the convolution of
the twisted prime source with the constant vector is the divisor fibre. -/
theorem truncConv_poleVector (y : GaugeTorus) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hK : ℓ ≤ K) (hN : ℓ ≤ N) :
    truncConv K N (gaugeTransform y fun k => (Λ k : ℂ)) (fun _ => 1) ℓ = divisorFibre y ℓ := by
  have hset : (Icc 1 K ×ˢ Icc 1 N).filter (fun p => p.1 * p.2 = ℓ) = ℓ.divisorsAntidiagonal := by
    ext p
    simp only [mem_filter, mem_product, mem_Icc, Nat.mem_divisorsAntidiagonal]
    constructor
    · rintro ⟨-, hp⟩
      exact ⟨hp, by omega⟩
    · rintro ⟨hp, hℓ0⟩
      have h1 : p.1 ≠ 0 := left_ne_zero_of_mul (hp ▸ hℓ0)
      have h2 : p.2 ≠ 0 := right_ne_zero_of_mul (hp ▸ hℓ0)
      have hle1 : p.1 ≤ ℓ := hp ▸ Nat.le_mul_of_pos_right p.1 (Nat.pos_of_ne_zero h2)
      have hle2 : p.2 ≤ ℓ := hp ▸ Nat.le_mul_of_pos_left p.2 (Nat.pos_of_ne_zero h1)
      exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, hp⟩
  rw [truncConv, hset, Nat.sum_divisorsAntidiagonal (fun i j => gaugeTransform y
    (fun k => (Λ k : ℂ)) i * (fun _ => (1 : ℂ)) j), divisorFibre_apply]
  simp [gaugeTransform]

/-- At the trivial point the pole-vector convolution is `log ℓ`: the shells of the pole direction
read the archimedean absolute value of the product. -/
theorem truncConv_poleVector_trivial {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hK : ℓ ≤ K) (hN : ℓ ≤ N) :
    truncConv K N (gaugeTransform 0 fun k => (Λ k : ℂ)) (fun _ => 1) ℓ = Real.log ℓ := by
  rw [truncConv_poleVector K N 0 hℓ hK hN, divisorFibre_trivial]

end GaloisForLFunctions.ArithmeticGaugeTheory
