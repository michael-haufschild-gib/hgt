import GaloisForLFunctions.ArithmeticGaugeTheory.AffineInvariantKernelsAreTrivial
import GaloisForLFunctions.ArithmeticGaugeTheory.TheCoherencePrinciple

/-!
# Affine positivity is the pole and Haar

A real kernel on the positive integers that is invariant under the dilations and the successor has
three values: `A` above the diagonal, `B` below, `D` on it (`AffineInvariantKernelsAreTrivial`). This
file describes the positive ones.

* **The form** (`kernelForm_affine`). With `c = (A + B)/2`,
  `Σ_{m,n ∈ s} v_m K(m, n) v_n = c (Σ v_n)² + (D − c) Σ v_n²`.
* **The positive cone** (`affine_nonneg_iff`). The form is nonnegative on every finite set iff
  `0 ≤ c ≤ D`. The positive affine-invariant forms are exactly `c ℓ(v)² + d ‖v‖²` with `c, d ≥ 0`,
  where `ℓ(v) = Σ v_n` is the pole functional.
* **The gauge reading** (`kernelForm_affine_eq_gauge`). `ℓ(v)²` is the square of the twisted sum at the
  trivial point and `‖v‖²` is its Haar mean square. The positive affine-invariant forms are the
  mixtures `c δ_0 + d Haar` of the two ends of the gauge torus: the trivial point and the typical
  measure. Nothing in between is affine invariant.
* **The Krein–Langer index is at most one, carried by the pole**
  (`affine_nonneg_on_poleHyperplane_iff`). On the hyperplane `ℓ(v) = 0` the form is `(D − c) ‖v‖²`, so it
  is nonnegative there iff `c ≤ D`. An affine-invariant form with `c < 0 ≤ D` has exactly one negative
  direction, the pole; positivity fails only through the boundary.

So an affine positivity principle has a boundary, and the boundary is the pole: the rank-one polar
term `ℓ(x)²` is the only non-diagonal positive affine form. Arithmetic positivity, Weil's form, must
come from the part of the kernel that breaks the successor invariance, the shells.
-/

open Finset MeasureTheory
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

/-- The quadratic form of a real kernel on a finite set. -/
def kernelForm (K : ℕ → ℕ → ℝ) (s : Finset ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ m ∈ s, ∑ n ∈ s, v m * K m n * v n

variable {K : ℕ → ℕ → ℝ}

/-- The three values of an affine-invariant real kernel. -/
theorem affine_kernel_eq (hdil : ∀ a m n, 1 ≤ a → 1 ≤ m → 1 ≤ n → K (a * m) (a * n) = K m n)
    (hsucc : ∀ m n, 1 ≤ m → 1 ≤ n → K (m + 1) (n + 1) = K m n) {m n : ℕ} (hm : 1 ≤ m)
    (hn : 1 ≤ n) :
    K m n = (if m < n then K 1 2 else 0) + (if n < m then K 2 1 else 0) +
      (if m = n then K 1 1 else 0) := by
  -- Apply the complex three-constant theorems to the complexified kernel.
  have hdilC : ∀ a m n, 1 ≤ a → 1 ≤ m → 1 ≤ n →
      ((K (a * m) (a * n) : ℝ) : ℂ) = ((K m n : ℝ) : ℂ) :=
    fun a m n ha hm hn => by rw [hdil a m n ha hm hn]
  have hsuccC : ∀ m n, 1 ≤ m → 1 ≤ n → ((K (m + 1) (n + 1) : ℝ) : ℂ) = ((K m n : ℝ) : ℂ) :=
    fun m n hm hn => by rw [hsucc m n hm hn]
  rcases lt_trichotomy m n with h | rfl | h
  · have := affineInvariant_kernel_lt (K := fun i j => ((K i j : ℝ) : ℂ)) hdilC hsuccC hm h
    rw [if_pos h, if_neg (by omega), if_neg (by omega)]
    simpa using this
  · have := affineInvariant_kernel_diag (K := fun i j => ((K i j : ℝ) : ℂ)) hsuccC hm
    simp only [lt_irrefl, if_false, if_true, zero_add]
    exact_mod_cast this
  · have := affineInvariant_kernel_gt (K := fun i j => ((K i j : ℝ) : ℂ)) hdilC hsuccC hn h
    rw [if_neg (by omega), if_pos h, if_neg (by omega)]
    simpa using this

/-- `(Σ v)² = 2 Σ_{m < n} v_m v_n + Σ v²`, and the two triangles agree. -/
theorem sq_sum_eq_triangles (s : Finset ℕ) (v : ℕ → ℝ) :
    (∑ n ∈ s, v n) ^ 2 =
      2 * ∑ m ∈ s, ∑ n ∈ s, v m * v n * (if m < n then 1 else 0) + ∑ n ∈ s, v n ^ 2 := by
  have htri : ∑ m ∈ s, ∑ n ∈ s, v m * v n * (if n < m then (1 : ℝ) else 0) =
      ∑ m ∈ s, ∑ n ∈ s, v m * v n * (if m < n then 1 else 0) := by
    rw [sum_comm]
    exact sum_congr rfl fun m _ => sum_congr rfl fun n _ => by ring
  have hdiag : ∑ m ∈ s, ∑ n ∈ s, v m * v n * (if m = n then (1 : ℝ) else 0) = ∑ n ∈ s, v n ^ 2 := by
    refine sum_congr rfl fun m hm => ?_
    simp_rw [mul_ite, mul_one, mul_zero]
    rw [sum_ite_eq s m, if_pos hm, sq]
  have hsplit : (∑ n ∈ s, v n) ^ 2 = ∑ m ∈ s, ∑ n ∈ s, (v m * v n * (if m < n then 1 else 0) +
      v m * v n * (if n < m then 1 else 0) + v m * v n * (if m = n then 1 else 0)) := by
    rw [sq, sum_mul_sum]
    refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
    rcases lt_trichotomy m n with h | rfl | h
    · rw [if_pos h, if_neg (by omega), if_neg (by omega)]; ring
    · simp
    · rw [if_neg (by omega), if_pos h, if_neg (by omega)]; ring
  rw [hsplit]
  simp only [sum_add_distrib]
  rw [htri, hdiag]
  ring

/-- **The affine form.** `Q(v) = c (Σ v)² + (D − c) Σ v²` with `c = (K(1,2) + K(2,1))/2`. -/
theorem kernelForm_affine (hdil : ∀ a m n, 1 ≤ a → 1 ≤ m → 1 ≤ n → K (a * m) (a * n) = K m n)
    (hsucc : ∀ m n, 1 ≤ m → 1 ≤ n → K (m + 1) (n + 1) = K m n) {s : Finset ℕ}
    (hs : ∀ n ∈ s, 1 ≤ n) (v : ℕ → ℝ) :
    kernelForm K s v = (K 1 2 + K 2 1) / 2 * (∑ n ∈ s, v n) ^ 2 +
      (K 1 1 - (K 1 2 + K 2 1) / 2) * ∑ n ∈ s, v n ^ 2 := by
  have hterm : ∀ m ∈ s, ∀ n ∈ s, v m * K m n * v n =
      K 1 2 * (v m * v n * (if m < n then 1 else 0)) +
        K 2 1 * (v m * v n * (if n < m then 1 else 0)) +
          K 1 1 * (v m * v n * (if m = n then 1 else 0)) := by
    intro m hm n hn
    rw [affine_kernel_eq hdil hsucc (hs m hm) (hs n hn)]
    split_ifs <;> ring
  have htri : ∑ m ∈ s, ∑ n ∈ s, v m * v n * (if n < m then (1 : ℝ) else 0) =
      ∑ m ∈ s, ∑ n ∈ s, v m * v n * (if m < n then 1 else 0) := by
    rw [sum_comm]
    exact sum_congr rfl fun m _ => sum_congr rfl fun n _ => by ring
  have hdiag : ∑ m ∈ s, ∑ n ∈ s, v m * v n * (if m = n then (1 : ℝ) else 0) = ∑ n ∈ s, v n ^ 2 := by
    refine sum_congr rfl fun m hm => ?_
    simp_rw [mul_ite, mul_one, mul_zero]
    rw [sum_ite_eq s m, if_pos hm, sq]
  rw [kernelForm, sum_congr rfl fun m hm => sum_congr rfl fun n hn => hterm m hm n hn]
  simp only [sum_add_distrib, ← mul_sum]
  rw [htri, hdiag, sq_sum_eq_triangles]
  ring

/-- **The positive cone of affine-invariant forms**: nonnegative on every finite set of positive
integers iff `0 ≤ c ≤ D`. -/
theorem affine_nonneg_iff (hdil : ∀ a m n, 1 ≤ a → 1 ≤ m → 1 ≤ n → K (a * m) (a * n) = K m n)
    (hsucc : ∀ m n, 1 ≤ m → 1 ≤ n → K (m + 1) (n + 1) = K m n) :
    (∀ s : Finset ℕ, (∀ n ∈ s, 1 ≤ n) → ∀ v, 0 ≤ kernelForm K s v) ↔
      0 ≤ (K 1 2 + K 2 1) / 2 ∧ (K 1 2 + K 2 1) / 2 ≤ K 1 1 := by
  set c := (K 1 2 + K 2 1) / 2
  constructor
  · intro h
    -- The pole-free test vector `e₁ − e₂`.
    have h12 := h {1, 2} (by simp) fun n => if n = 1 then 1 else if n = 2 then -1 else 0
    rw [kernelForm_affine hdil hsucc (by simp)] at h12
    simp only [sum_insert (show (1 : ℕ) ∉ {2} by simp), sum_singleton] at h12
    norm_num at h12
    -- The pole vector `1` on `[1, M]`.
    have hpole : ∀ M : ℕ, 0 ≤ c * (M : ℝ) ^ 2 + (K 1 1 - c) * M := by
      intro M
      have hM := h (Icc 1 M) (fun n hn => (mem_Icc.mp hn).1) fun _ => 1
      rw [kernelForm_affine hdil hsucc (fun n hn => (mem_Icc.mp hn).1)] at hM
      simpa using hM
    refine ⟨?_, by linarith⟩
    by_contra hc
    push Not at hc
    obtain ⟨M, hM⟩ := exists_nat_gt ((K 1 1 - c) / (-c))
    have hMpos : (0 : ℝ) < M := lt_of_le_of_lt (div_nonneg (by linarith) (by linarith)) hM
    have hlt : K 1 1 - c < -c * M := by rwa [div_lt_iff₀ (by linarith)] at hM
    have := hpole M
    nlinarith
  · rintro ⟨hc0, hcD⟩ s hs v
    rw [kernelForm_affine hdil hsucc hs]
    have : 0 ≤ ∑ n ∈ s, v n ^ 2 := sum_nonneg fun n _ => sq_nonneg _
    positivity

/-- **The Krein–Langer index is at most one, carried by the pole.** On the hyperplane `Σ v = 0` an
affine-invariant form is nonnegative iff `c ≤ D`. -/
theorem affine_nonneg_on_poleHyperplane_iff
    (hdil : ∀ a m n, 1 ≤ a → 1 ≤ m → 1 ≤ n → K (a * m) (a * n) = K m n)
    (hsucc : ∀ m n, 1 ≤ m → 1 ≤ n → K (m + 1) (n + 1) = K m n) :
    (∀ s : Finset ℕ, (∀ n ∈ s, 1 ≤ n) → ∀ v, ∑ n ∈ s, v n = 0 → 0 ≤ kernelForm K s v) ↔
      (K 1 2 + K 2 1) / 2 ≤ K 1 1 := by
  constructor
  · intro h
    have h12 := h {1, 2} (by simp) (fun n => if n = 1 then 1 else if n = 2 then -1 else 0)
      (by simp [sum_insert (show (1 : ℕ) ∉ {2} by simp)])
    rw [kernelForm_affine hdil hsucc (by simp)] at h12
    simp only [sum_insert (show (1 : ℕ) ∉ {2} by simp), sum_singleton] at h12
    norm_num at h12
    linarith
  · intro hcD s hs v hv
    rw [kernelForm_affine hdil hsucc hs, hv]
    have : 0 ≤ ∑ n ∈ s, v n ^ 2 := sum_nonneg fun n _ => sq_nonneg _
    nlinarith

/-- **The gauge reading.** An affine-invariant form is `c` times the square of the twisted sum at the
trivial point plus `D − c` times its Haar mean square. -/
theorem kernelForm_affine_eq_gauge
    (hdil : ∀ a m n, 1 ≤ a → 1 ≤ m → 1 ≤ n → K (a * m) (a * n) = K m n)
    (hsucc : ∀ m n, 1 ≤ m → 1 ≤ n → K (m + 1) (n + 1) = K m n) {s : Finset ℕ}
    (hs : ∀ n ∈ s, 1 ≤ n) (v : ℕ → ℝ) :
    ((kernelForm K s v : ℝ) : ℂ) =
      ((K 1 2 + K 2 1) / 2 : ℝ) * (twistSum s (fun n => (v n : ℂ)) 0 *
          conj (twistSum s (fun n => (v n : ℂ)) 0)) +
        ((K 1 1 - (K 1 2 + K 2 1) / 2 : ℝ) : ℂ) *
          ∫ x, twistSum s (fun n => (v n : ℂ)) x * conj (twistSum s (fun n => (v n : ℂ)) x)
            ∂gaugeHaar := by
  rw [integral_twistSum_mul_conj (fun n hn => by have := hs n hn; omega), twistSum_trivial,
    kernelForm_affine hdil hsucc hs]
  push_cast
  simp only [Complex.conj_ofReal, ← map_sum]
  rw [Complex.conj_ofReal]
  push_cast
  ring

end GaloisForLFunctions.ArithmeticGaugeTheory
