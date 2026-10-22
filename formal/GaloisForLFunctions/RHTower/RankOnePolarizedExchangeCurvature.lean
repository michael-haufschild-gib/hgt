import GaloisForLFunctions.RHTower.Deninger.DeningerOneSidedFramedMateCurvatureTransgression

/-!
# Rank-one polarized exchange curvature

The affine top-conormal transport `A n = !![n, n - 1; 0, 1]` of the multiplicative monoid of
positive integers is flat.  Placing a multiplicative gain on the conormal term only produces the
one-sided polarized transport

`T χ n = !![χ n * n, χ n * (n - 1); 0, 1]`,

whose composition defect is the single upper-right entry `χ m * (m - 1) * (1 - χ n)`.  Because the
calibration at `m = 2` is the unit `1`, the defect vanishes identically exactly at the trivial
character; for the power character `n ↦ n ^ θ` this happens exactly at zero modular weight, and for
a centred spectral gain of weight `w` exactly on the purity line `Re s = w / 2`.

The same scalar is the paracyclic monodromy defect of the swap `J χ n = !![0, 1; χ n, 0]`, and for a
complex character it is the affine transgression of the Hermitian torsion anomaly.
-/

namespace RHTower

noncomputable section

open Matrix

/-! ## Flat affine transport over an arbitrary field -/

variable (k : Type*) [Field k]

/-- The flat affine top-conormal transport of a positive integer. -/
def conormalTransport (n : ℕ+) : Matrix (Fin 2) (Fin 2) k :=
  !![((n : ℕ) : k), ((n : ℕ) : k) - 1; 0, 1]

variable {k}

/-- **The unpolarized top-conormal transport is flat.** -/
theorem conormalTransport_mul (m n : ℕ+) :
    conormalTransport k m * conormalTransport k n = conormalTransport k (m * n) := by
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [conormalTransport, Matrix.mul_apply, Fin.sum_univ_succ, PNat.mul_coe]
  all_goals ring

/-! ## One-sided polarized transport and its curvature -/

/-- One-sided polarized exchange transport: the gain acts on the conormal term only. -/
def exchangeTransport (χ : ℕ+ →* kˣ) (n : ℕ+) : Matrix (Fin 2) (Fin 2) k :=
  !![(χ n : k) * ((n : ℕ) : k), (χ n : k) * (((n : ℕ) : k) - 1); 0, 1]

/-- The polarized transport is the conormal gain followed by the flat affine transport. -/
theorem exchangeTransport_eq_diagonal_mul (χ : ℕ+ →* kˣ) (n : ℕ+) :
    exchangeTransport χ n =
      Matrix.diagonal (fun i : Fin 2 => if i = 0 then (χ n : k) else 1) *
        conormalTransport k n := by
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [exchangeTransport, conormalTransport, Matrix.mul_apply, Fin.sum_univ_succ]

variable (k) in
/-- The upper-right elementary matrix, the single direction of the exchange defect. -/
def exchangeE12 : Matrix (Fin 2) (Fin 2) k := !![0, 1; 0, 0]

theorem exchangeE12_sq : exchangeE12 k * exchangeE12 k = 0 := by
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [exchangeE12, Matrix.mul_apply, Fin.sum_univ_succ]

theorem smul_exchangeE12_eq_zero_iff (c : k) : c • exchangeE12 k = 0 ↔ c = 0 := by
  constructor
  · intro h
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) k => M 0 1) h
    simpa [exchangeE12] using this
  · rintro rfl
    simp

/-- Composition curvature of the polarized exchange transport. -/
def exchangeCurvature (χ : ℕ+ →* kˣ) (m n : ℕ+) : Matrix (Fin 2) (Fin 2) k :=
  exchangeTransport χ m * exchangeTransport χ n - exchangeTransport χ (m * n)

/-- **Exact one-sided exchange curvature.**  The defect is a single upper-right entry. -/
theorem exchangeCurvature_eq (χ : ℕ+ →* kˣ) (m n : ℕ+) :
    exchangeCurvature χ m n =
      ((χ m : k) * (((m : ℕ) : k) - 1) * (1 - (χ n : k))) • exchangeE12 k := by
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [exchangeCurvature, exchangeTransport, exchangeE12, PNat.mul_coe]
  all_goals ring

/-- **The curvature obeys the nonabelian Bianchi identity.** -/
theorem exchangeCurvature_bianchi (χ : ℕ+ →* kˣ) (l m n : ℕ+) :
    exchangeCurvature χ l m * exchangeTransport χ n +
        exchangeCurvature χ (l * m) n =
      exchangeTransport χ l * exchangeCurvature χ m n +
        exchangeCurvature χ l (m * n) := by
  simp only [exchangeCurvature, mul_assoc]
  noncomm_ring

/-- The first nontrivial calibration is the unit `1`, so the curvature at `(2, n)` measures the
character alone. -/
theorem exchangeCurvature_two (χ : ℕ+ →* kˣ) (n : ℕ+) :
    exchangeCurvature χ 2 n = ((χ 2 : k) * (1 - (χ n : k))) • exchangeE12 k := by
  rw [exchangeCurvature_eq]
  norm_num

theorem exchangeCurvature_two_eq_zero_iff (χ : ℕ+ →* kˣ) (n : ℕ+) :
    exchangeCurvature χ 2 n = 0 ↔ χ n = 1 := by
  rw [exchangeCurvature_two, smul_exchangeE12_eq_zero_iff, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (Units.ne_zero (χ 2))
    · refine Units.ext ?_
      simp only [Units.val_one]
      linear_combination -h
  · intro h
    right
    rw [h]
    simp

/-- **The polarized transport is a monoid representation exactly at the trivial character.** -/
theorem exchangeTransport_mul_iff (χ : ℕ+ →* kˣ) :
    (∀ m n : ℕ+, exchangeTransport χ m * exchangeTransport χ n =
        exchangeTransport χ (m * n)) ↔ χ = 1 := by
  constructor
  · intro h
    ext n
    have hz : exchangeCurvature χ 2 n = 0 := by
      rw [exchangeCurvature, h 2 n, sub_self]
    have := (exchangeCurvature_two_eq_zero_iff χ n).1 hz
    rw [this]
    rfl
  · rintro rfl
    intro m n
    have hz : exchangeCurvature (1 : ℕ+ →* kˣ) m n = 0 := by
      rw [exchangeCurvature_eq]
      simp
    rw [exchangeCurvature, sub_eq_zero] at hz
    exact hz

/-- At the trivial character the polarized transport is the flat affine transport. -/
theorem exchangeTransport_one (n : ℕ+) :
    exchangeTransport (1 : ℕ+ →* kˣ) n = conormalTransport k n := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [exchangeTransport, conormalTransport]

/-! ## Paracyclic monodromy calibration -/

/-- The polarized swap of a character. -/
def exchangeSwap (χ : ℕ+ →* kˣ) (n : ℕ+) : Matrix (Fin 2) (Fin 2) k :=
  !![0, 1; (χ n : k), 0]

/-- The swap squares to the character scalar. -/
theorem exchangeSwap_sq (χ : ℕ+ →* kˣ) (n : ℕ+) :
    exchangeSwap χ n * exchangeSwap χ n = (χ n : k) • (1 : Matrix (Fin 2) (Fin 2) k) := by
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [exchangeSwap, Matrix.mul_apply, Fin.sum_univ_succ]

theorem exchangeE12_mul_smul_one_sub_one (c : k) :
    exchangeE12 k * (c • (1 : Matrix (Fin 2) (Fin 2) k) - 1) = (c - 1) • exchangeE12 k := by
  rw [mul_sub, Matrix.mul_smul, mul_one, sub_smul, one_smul]

/-- **The exchange curvature is the calibrated paracyclic monodromy defect.** -/
theorem exchangeCurvature_eq_paracyclic (χ : ℕ+ →* kˣ) (m n : ℕ+) :
    exchangeCurvature χ m n =
      -((χ m : k) * (((m : ℕ) : k) - 1)) •
        (exchangeE12 k * (exchangeSwap χ n * exchangeSwap χ n - 1)) := by
  rw [exchangeCurvature_eq, exchangeSwap_sq, exchangeE12_mul_smul_one_sub_one, smul_smul]
  congr 1
  ring

/-- At the calibrating degree two, the exchange defect and the paracyclic monodromy defect have the
same zero locus. -/
theorem exchangeCurvature_two_eq_zero_iff_swap (χ : ℕ+ →* kˣ) (n : ℕ+) :
    exchangeCurvature χ 2 n = 0 ↔
      exchangeSwap χ n * exchangeSwap χ n = (1 : Matrix (Fin 2) (Fin 2) k) := by
  rw [exchangeCurvature_two_eq_zero_iff, exchangeSwap_sq]
  constructor
  · intro h; rw [h]; simp
  · intro h
    have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) k => M 0 0) h
    simp at hentry
    exact Units.ext (by simpa using hentry)

end

end RHTower
