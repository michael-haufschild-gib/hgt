import GaloisForLFunctions.HTGeometry.EllipticGammaConeCocycle
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentTranslation

/-!
# A lattice theta from two opposite half-line products

The single-index product `∏_{k ≥ 0}(1 - e(kb + z))` vanishes on the half lattice `ℤ - ℕb`.  Its
reflection `z ↦ ∏_{k ≥ 0}(1 - e(kb + b - z))` vanishes on the complementary half `ℤ + (ℕ+1)b`, so
the product of the two vanishes exactly on the full lattice `ℤ + ℤb`, to first order at every point.

The resulting entire function is `1`-periodic and multiplies by the nowhere-zero character
`-e(-z)` under a `b`-step.  It is the theta function of the lattice, built from the cone products
alone.

* `latticeTheta`, `differentiable_latticeTheta`, `latticeTheta_periodic`;
* `latticeTheta_shift` — `Θ(z + b) = -e(-z)·Θ(z)`;
* `latticeTheta_eq_zero_iff` — the zero set is exactly `ℤ + ℤb`;
* `meromorphicOrderAt_latticeTheta` — order `1` on the lattice, `0` off it.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

noncomputable section

/-! ### Periodicity of the half-line product -/

theorem singleFactor_periodic (b : ℂ) (k : ℕ) (z : ℂ) :
    singleFactor b k (z + 1) = singleFactor b k z := by
  rw [singleFactor, singleFactor]
  congr 1
  rw [show (k : ℂ) * b + (z + 1) = ((k : ℂ) * b + z) + 1 from by ring, expChar_add_one]

/-- The half-line product is `1`-periodic. -/
theorem singleProduct_periodic (b z : ℂ) : singleProduct b (z + 1) = singleProduct b z := by
  rw [singleProduct, singleProduct]
  exact tprod_congr fun k => singleFactor_periodic b k z

theorem singleProduct_periodic_sub (b z : ℂ) : singleProduct b (z - 1) = singleProduct b z := by
  have h := singleProduct_periodic b (z - 1)
  rw [sub_add_cancel] at h
  exact h.symm

/-! ### The lattice theta -/

/-- The theta function of the lattice `ℤ + ℤb`, as the product of the two opposite half-line
products. -/
def latticeTheta (b : ℂ) (z : ℂ) : ℂ := singleProduct b z * singleProduct b (b - z)

theorem differentiable_latticeTheta {b : ℂ} (hb : 0 < b.im) :
    Differentiable ℂ (latticeTheta b) := fun z => by
  refine DifferentiableAt.mul (differentiable_singleProduct hb z) ?_
  exact (differentiable_singleProduct hb (b - z)).comp z (differentiableAt_id.const_sub b)

theorem latticeTheta_periodic (b z : ℂ) : latticeTheta b (z + 1) = latticeTheta b z := by
  rw [latticeTheta, latticeTheta, singleProduct_periodic]
  congr 1
  rw [show b - (z + 1) = (b - z) - 1 from by ring, singleProduct_periodic_sub]

/-- **The `b`-step multiplier of the lattice theta** is the nowhere-zero character `-e(-z)`. -/
theorem latticeTheta_shift {b : ℂ} (hb : 0 < b.im) (z : ℂ) :
    latticeTheta b (z + b) = -expChar (-z) * latticeTheta b z := by
  have h1 : singleProduct b z = (1 - expChar z) * singleProduct b (z + b) :=
    singleProduct_shift hb z
  have h2 : singleProduct b (-z) = (1 - expChar (-z)) * singleProduct b (-z + b) :=
    singleProduct_shift hb (-z)
  rw [latticeTheta, latticeTheta, show b - (z + b) = -z from by ring, h2,
    show -z + b = b - z from by ring, h1, one_sub_expChar_neg z]
  ring

/-! ### The zero set -/

theorem singleFactor_eq_zero_iff (b : ℂ) (k : ℕ) (z : ℂ) :
    singleFactor b k z = 0 ↔ ∃ m : ℤ, z = (m : ℂ) - (k : ℂ) * b := by
  rw [singleFactor, sub_eq_zero]
  constructor
  · intro h
    obtain ⟨m, hm⟩ := (expChar_eq_one_iff _).mp h.symm
    exact ⟨m, by linear_combination hm⟩
  · rintro ⟨m, rfl⟩
    exact ((expChar_eq_one_iff _).mpr ⟨m, by ring⟩).symm

theorem singleProduct_eq_zero_iff' {b : ℂ} (hb : 0 < b.im) (z : ℂ) :
    singleProduct b z = 0 ↔ ∃ (k : ℕ) (m : ℤ), z = (m : ℂ) - (k : ℂ) * b := by
  rw [singleProduct_eq_zero_iff hb]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, (singleFactor_eq_zero_iff b k z).mp hk⟩
  · rintro ⟨k, m, hm⟩
    exact ⟨k, (singleFactor_eq_zero_iff b k z).mpr ⟨m, hm⟩⟩

/-- **The zero set of the lattice theta is exactly the lattice.** -/
theorem latticeTheta_eq_zero_iff {b : ℂ} (hb : 0 < b.im) (z : ℂ) :
    latticeTheta b z = 0 ↔ ∃ m n : ℤ, z = (m : ℂ) + (n : ℂ) * b := by
  rw [latticeTheta, mul_eq_zero, singleProduct_eq_zero_iff' hb, singleProduct_eq_zero_iff' hb]
  constructor
  · rintro (⟨k, m, hm⟩ | ⟨k, m, hm⟩)
    · exact ⟨m, -(k : ℤ), by push_cast; linear_combination hm⟩
    · exact ⟨-m, (k : ℤ) + 1, by push_cast; linear_combination -hm⟩
  · rintro ⟨m, n, rfl⟩
    rcases le_or_lt n 0 with hn | hn
    · refine Or.inl ⟨(-n).toNat, m, ?_⟩
      have : (((-n).toNat : ℤ) : ℂ) = ((-n : ℤ) : ℂ) := by
        norm_cast
        omega
      push_cast at this ⊢
      rw [this]
      ring
    · refine Or.inr ⟨(n - 1).toNat, -m, ?_⟩
      have : (((n - 1).toNat : ℤ) : ℂ) = ((n - 1 : ℤ) : ℂ) := by
        norm_cast
        omega
      push_cast at this ⊢
      rw [this]
      ring

/-! ### Simple zeros -/

theorem hasDerivAt_one_sub_expChar (z : ℂ) :
    HasDerivAt (fun w : ℂ => 1 - expChar w) (-(expChar z * (2 * (Real.pi : ℂ) * Complex.I))) z := by
  have h1 : HasDerivAt (fun w : ℂ => 2 * (Real.pi : ℂ) * Complex.I * w)
      (2 * (Real.pi : ℂ) * Complex.I) z := by
    simpa using (hasDerivAt_id z).const_mul (2 * (Real.pi : ℂ) * Complex.I)
  exact h1.cexp.const_sub 1

theorem differentiable_one_sub_expChar : Differentiable ℂ (fun w : ℂ => 1 - expChar w) :=
  fun z => (hasDerivAt_one_sub_expChar z).differentiableAt

/-- The character takes the value one to first order. -/
theorem analyticOrderAt_one_sub_expChar_eq_one {z : ℂ} (h : expChar z = 1) :
    analyticOrderAt (fun w : ℂ => 1 - expChar w) z = 1 := by
  have hderiv : deriv (fun w : ℂ => 1 - expChar w) z = -(2 * (Real.pi : ℂ) * Complex.I) := by
    rw [(hasDerivAt_one_sub_expChar z).deriv, h, one_mul]
  have hne : deriv (fun w : ℂ => 1 - expChar w) z ≠ 0 := by
    rw [hderiv]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [hpi, Complex.I_ne_zero]
  have hiff := analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
    (differentiable_one_sub_expChar.analyticAt z) (n := 1)
  rw [Nat.cast_one] at hiff
  rw [hiff]
  refine ⟨fun k hk => ?_, ?_⟩
  · interval_cases k
    simpa using h
  · simpa [iteratedDeriv_one] using hne

/-! ### The order of the lattice theta -/

theorem singleProduct_shifted_ne_zero {b : ℂ} (hb : 0 < b.im) : singleProduct b b ≠ 0 := by
  rw [singleProduct_eq_zero_iff' hb]
  rintro ⟨k, m, hm⟩
  have him : ((m : ℂ) - (k : ℂ) * b).im = -((k : ℝ) * b.im) := by
    simp [Complex.sub_im, Complex.mul_im]
  have hb' : b.im = -((k : ℝ) * b.im) := by rw [← him, ← hm]
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

private theorem meromorphicOrderAt_eq_zero_of_ne_zero {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (h : f z ≠ 0) : meromorphicOrderAt f z = 0 := by
  rw [hf.meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (Or.inr h)]
  rfl

/-- **The lattice theta has a simple zero at the origin.** -/
theorem meromorphicOrderAt_latticeTheta_zero {b : ℂ} (hb : 0 < b.im) :
    meromorphicOrderAt (latticeTheta b) 0 = 1 := by
  set G : ℂ → ℂ := fun z => singleProduct b (z + b) * singleProduct b (b - z) with hG
  have hGdiff : Differentiable ℂ G := fun z => by
    refine DifferentiableAt.mul ?_ ?_
    · exact (differentiable_singleProduct hb (z + b)).comp z (differentiableAt_id.add_const b)
    · exact (differentiable_singleProduct hb (b - z)).comp z (differentiableAt_id.const_sub b)
  have hfac : latticeTheta b = (fun z : ℂ => 1 - expChar z) * G := by
    funext z
    simp only [Pi.mul_apply, hG]
    rw [latticeTheta, singleProduct_shift hb z]
    ring
  have hG0 : G 0 ≠ 0 := by
    rw [hG]
    simp only [zero_add, sub_zero]
    exact mul_ne_zero (singleProduct_shifted_ne_zero hb) (singleProduct_shifted_ne_zero hb)
  rw [hfac, meromorphicOrderAt_mul (differentiable_one_sub_expChar.analyticAt 0).meromorphicAt
      (hGdiff.analyticAt 0).meromorphicAt,
    meromorphicOrderAt_eq_zero_of_ne_zero (hGdiff.analyticAt 0) hG0, add_zero,
    (differentiable_one_sub_expChar.analyticAt 0).meromorphicOrderAt_eq,
    analyticOrderAt_one_sub_expChar_eq_one expChar_zero]
  rfl

/-! ### Lattice invariance of the order -/

private theorem eq_of_add_intCast_mul {α : Type*} {f : ℂ → α} {p : ℂ}
    (h : ∀ r : ℂ, f (r + p) = f r) (r : ℂ) (n : ℤ) : f (r + (n : ℂ) * p) = f r := by
  induction n using Int.induction_on with
  | zero => norm_num
  | succ k ih =>
      have hs : r + (((k : ℤ) + 1 : ℤ) : ℂ) * p = (r + ((k : ℤ) : ℂ) * p) + p := by
        push_cast; ring
      rw [hs, h, ih]
  | pred k ih =>
      have hs : (r + ((-(k : ℤ) - 1 : ℤ) : ℂ) * p) + p = r + ((-(k : ℤ) : ℤ) : ℂ) * p := by
        push_cast; ring
      have hh := h (r + ((-(k : ℤ) - 1 : ℤ) : ℂ) * p)
      rw [hs] at hh
      rw [← hh, ih]

theorem meromorphicOrderAt_latticeTheta_add_one (b r : ℂ) :
    meromorphicOrderAt (latticeTheta b) (r + 1) = meromorphicOrderAt (latticeTheta b) r := by
  have hfun : (fun z => latticeTheta b (z + 1)) = latticeTheta b := funext (latticeTheta_periodic b)
  rw [← meromorphicOrderAt_comp_add (latticeTheta b) r 1, hfun]

theorem meromorphicOrderAt_latticeTheta_add_period {b : ℂ} (hb : 0 < b.im) (r : ℂ) :
    meromorphicOrderAt (latticeTheta b) (r + b) = meromorphicOrderAt (latticeTheta b) r := by
  have hfun : (fun z => latticeTheta b (z + b))
      = (fun z : ℂ => -expChar (-z)) * latticeTheta b := by
    funext z
    simp only [Pi.mul_apply]
    exact latticeTheta_shift hb z
  have hu : Differentiable ℂ fun z : ℂ => -expChar (-z) := by
    unfold expChar
    fun_prop
  have hune : (fun z : ℂ => -expChar (-z)) r ≠ 0 := by
    simp only [neg_ne_zero, expChar]
    exact Complex.exp_ne_zero _
  rw [← meromorphicOrderAt_comp_add (latticeTheta b) r b, hfun,
    meromorphicOrderAt_mul (hu.analyticAt r).meromorphicAt
      ((differentiable_latticeTheta hb).analyticAt r).meromorphicAt,
    meromorphicOrderAt_eq_zero_of_ne_zero (hu.analyticAt r) hune, zero_add]

/-- **The lattice theta has a simple zero at every lattice point.** -/
theorem meromorphicOrderAt_latticeTheta_lattice {b : ℂ} (hb : 0 < b.im) (m n : ℤ) :
    meromorphicOrderAt (latticeTheta b) ((m : ℂ) + (n : ℂ) * b) = 1 := by
  have hb' := eq_of_add_intCast_mul (f := fun r => meromorphicOrderAt (latticeTheta b) r)
    (p := b) (meromorphicOrderAt_latticeTheta_add_period hb) (m : ℂ) n
  have h1' := eq_of_add_intCast_mul (f := fun r => meromorphicOrderAt (latticeTheta b) r)
    (p := 1) (meromorphicOrderAt_latticeTheta_add_one b) 0 m
  simp only [zero_add, mul_one] at h1'
  rw [hb', h1', meromorphicOrderAt_latticeTheta_zero hb]

/-- **Off the lattice the theta is a unit.** -/
theorem meromorphicOrderAt_latticeTheta_of_notMem {b : ℂ} (hb : 0 < b.im) {z : ℂ}
    (hz : ¬ ∃ m n : ℤ, z = (m : ℂ) + (n : ℂ) * b) :
    meromorphicOrderAt (latticeTheta b) z = 0 :=
  meromorphicOrderAt_eq_zero_of_ne_zero ((differentiable_latticeTheta hb).analyticAt z)
    (fun h => hz ((latticeTheta_eq_zero_iff hb z).mp h))

end

end GaloisForLFunctions.HTGeometry
