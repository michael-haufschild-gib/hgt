import Mathlib

/-!
# Midpoint–radius enclosures and Taylor enclosures of `sin` and `cos`

An enclosure `⟨c, r⟩` of a real number `X` is the statement `|X - c| ≤ r`.  Enclosures are closed
under sums, differences, products, scalar multiples and inverses (when `r < |c|`), with the
standard midpoint–radius formulas, so any rational expression in enclosed quantities is enclosed
by the same expression tree evaluated on the enclosures.  Degree-20 Taylor polynomials enclose
`cos θ` and `sin θ` for `|θ| ≤ 10`, with error at most `2|θ|^{20}/20!`, from the exponential
remainder bound applied to `e^{iθ}`.
-/

open Real

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- A midpoint–radius enclosure `|X - c| ≤ r`. -/
structure Encl where
  c : ℝ
  r : ℝ

namespace Encl

def Holds (X : ℝ) (e : Encl) : Prop := |X - e.c| ≤ e.r

def add (a b : Encl) : Encl := ⟨a.c + b.c, a.r + b.r⟩
def sub (a b : Encl) : Encl := ⟨a.c - b.c, a.r + b.r⟩
def mul (a b : Encl) : Encl := ⟨a.c * b.c, |a.c| * b.r + |b.c| * a.r + a.r * b.r⟩
def smul (k : ℝ) (a : Encl) : Encl := ⟨k * a.c, |k| * a.r⟩
def inv (a : Encl) : Encl := ⟨a.c⁻¹, a.r / (|a.c| * (|a.c| - a.r))⟩
def exact (x : ℝ) : Encl := ⟨x, 0⟩
def ofBounds (lo hi : ℝ) : Encl := ⟨(lo + hi) / 2, (hi - lo) / 2⟩

theorem holds_exact (x : ℝ) : Holds x (exact x) := by simp [Holds, exact]

theorem holds_ofBounds {X lo hi : ℝ} (h1 : lo ≤ X) (h2 : X ≤ hi) : Holds X (ofBounds lo hi) := by
  unfold Holds ofBounds
  rw [abs_le]
  constructor <;> linarith

theorem holds_add {X Y : ℝ} {a b : Encl} (hX : Holds X a) (hY : Holds Y b) :
    Holds (X + Y) (add a b) := by
  unfold Holds add at *
  calc |X + Y - (a.c + b.c)| = |(X - a.c) + (Y - b.c)| := by ring_nf
    _ ≤ |X - a.c| + |Y - b.c| := abs_add_le _ _
    _ ≤ a.r + b.r := add_le_add hX hY

theorem holds_sub {X Y : ℝ} {a b : Encl} (hX : Holds X a) (hY : Holds Y b) :
    Holds (X - Y) (sub a b) := by
  unfold Holds sub at *
  calc |X - Y - (a.c - b.c)| = |(X - a.c) - (Y - b.c)| := by ring_nf
    _ ≤ |X - a.c| + |Y - b.c| := abs_sub _ _
    _ ≤ a.r + b.r := add_le_add hX hY

theorem holds_mul {X Y : ℝ} {a b : Encl} (hX : Holds X a) (hY : Holds Y b) :
    Holds (X * Y) (mul a b) := by
  unfold Holds mul at *
  have hra : 0 ≤ a.r := (abs_nonneg _).trans hX
  have hrb : 0 ≤ b.r := (abs_nonneg _).trans hY
  have hid : X * Y - a.c * b.c = a.c * (Y - b.c) + b.c * (X - a.c) + (X - a.c) * (Y - b.c) := by
    ring
  rw [hid]
  calc |a.c * (Y - b.c) + b.c * (X - a.c) + (X - a.c) * (Y - b.c)|
      ≤ |a.c * (Y - b.c)| + |b.c * (X - a.c)| + |(X - a.c) * (Y - b.c)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = |a.c| * |Y - b.c| + |b.c| * |X - a.c| + |X - a.c| * |Y - b.c| := by
        rw [abs_mul, abs_mul, abs_mul]
    _ ≤ |a.c| * b.r + |b.c| * a.r + a.r * b.r := by
        gcongr

theorem holds_smul (k : ℝ) {X : ℝ} {a : Encl} (hX : Holds X a) : Holds (k * X) (smul k a) := by
  unfold Holds smul at *
  rw [show k * X - k * a.c = k * (X - a.c) by ring, abs_mul]
  exact mul_le_mul_of_nonneg_left hX (abs_nonneg k)

theorem holds_inv {X : ℝ} {a : Encl} (hX : Holds X a) (hsmall : a.r < |a.c|) :
    Holds X⁻¹ (inv a) := by
  unfold Holds inv at *
  have hc : 0 < |a.c| := lt_of_le_of_lt ((abs_nonneg _).trans hX) hsmall
  have hc0 : a.c ≠ 0 := abs_pos.mp hc
  have hXabs : |a.c| - a.r ≤ |X| := by
    have := abs_sub_abs_le_abs_sub a.c X
    rw [abs_sub_comm] at this
    linarith
  have hXpos : 0 < |X| := lt_of_lt_of_le (by linarith) hXabs
  have hX0 : X ≠ 0 := abs_pos.mp hXpos
  rw [show X⁻¹ - a.c⁻¹ = (a.c - X) / (X * a.c) by field_simp, abs_div, abs_mul,
    abs_sub_comm]
  rw [div_le_div_iff₀ (mul_pos hXpos hc) (mul_pos hc (by linarith))]
  have h1 : |X - a.c| * (|a.c| * (|a.c| - a.r)) ≤ a.r * (|a.c| * (|a.c| - a.r)) :=
    mul_le_mul_of_nonneg_right hX (mul_nonneg hc.le (by linarith))
  have h2 : a.r * (|a.c| * (|a.c| - a.r)) ≤ a.r * (|X| * |a.c|) := by
    apply mul_le_mul_of_nonneg_left _ ((abs_nonneg _).trans hX)
    rw [mul_comm |X|]
    exact mul_le_mul_of_nonneg_left hXabs hc.le
  linarith

theorem le_of_holds {X : ℝ} {a : Encl} (hX : Holds X a) : X ≤ a.c + a.r := by
  unfold Holds at hX
  linarith [le_abs_self (X - a.c)]

theorem ge_of_holds {X : ℝ} {a : Encl} (hX : Holds X a) : a.c - a.r ≤ X := by
  unfold Holds at hX
  linarith [neg_abs_le (X - a.c)]

end Encl

/-! ## Taylor enclosures of `sin` and `cos` -/

/-- `Σ_{j<J} (-1)^j θ^{2j}/(2j)!`. -/
def cosTaylor (J : ℕ) (θ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range J, (-1) ^ j * θ ^ (2 * j) / ((2 * j).factorial : ℝ)

/-- `Σ_{j<J} (-1)^j θ^{2j+1}/(2j+1)!`. -/
def sinTaylor (J : ℕ) (θ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range J, (-1) ^ j * θ ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)

theorem sum_exp_I_taylor (J : ℕ) (θ : ℝ) :
    ∑ m ∈ Finset.range (2 * J), ((θ : ℂ) * Complex.I) ^ m / (m.factorial : ℂ) =
      (cosTaylor J θ : ℂ) + (sinTaylor J θ : ℂ) * Complex.I := by
  induction J with
  | zero => simp [cosTaylor, sinTaylor]
  | succ J ih =>
    rw [show 2 * (J + 1) = 2 * J + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih]
    unfold cosTaylor sinTaylor
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hI2 : ∀ n : ℕ, Complex.I ^ (2 * n) = (-1) ^ n := by
      intro n
      rw [pow_mul, Complex.I_sq]
    have e1 : ((θ : ℂ) * Complex.I) ^ (2 * J) = (((-1) ^ J * θ ^ (2 * J) : ℝ) : ℂ) := by
      rw [mul_pow, hI2]
      push_cast
      ring
    have e2 : ((θ : ℂ) * Complex.I) ^ (2 * J + 1) =
        (((-1) ^ J * θ ^ (2 * J + 1) : ℝ) : ℂ) * Complex.I := by
      rw [pow_succ, mul_pow, hI2]
      push_cast
      ring
    rw [e1, e2]
    push_cast
    ring

/-- Degree-20 Taylor enclosures of `cos θ` and `sin θ` for `|θ| ≤ 10`. -/
theorem cos_sin_taylor_bound {θ : ℝ} (hθ : |θ| ≤ 10) :
    |Real.cos θ - cosTaylor 10 θ| ≤ |θ| ^ 20 / (Nat.factorial 20 : ℝ) * 2 ∧
      |Real.sin θ - sinTaylor 10 θ| ≤ |θ| ^ 20 / (Nat.factorial 20 : ℝ) * 2 := by
  have hx : ‖(θ : ℂ) * Complex.I‖ / ((20 : ℕ).succ : ℝ) ≤ 1 / 2 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [div_le_iff₀ (by norm_num)]
    push_cast
    linarith
  have hb := Complex.exp_bound' hx
  rw [show (20 : ℕ) = 2 * 10 by norm_num, sum_exp_I_taylor] at hb
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at hb
  have hexp : Complex.exp ((θ : ℂ) * Complex.I) =
      (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [hexp] at hb
  have hdiff : (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I -
      ((cosTaylor 10 θ : ℂ) + (sinTaylor 10 θ : ℂ) * Complex.I) =
      ((Real.cos θ - cosTaylor 10 θ : ℝ) : ℂ) +
        ((Real.sin θ - sinTaylor 10 θ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hdiff] at hb
  have hre := (Complex.abs_re_le_norm (((Real.cos θ - cosTaylor 10 θ : ℝ) : ℂ) +
    ((Real.sin θ - sinTaylor 10 θ : ℝ) : ℂ) * Complex.I)).trans hb
  have him := (Complex.abs_im_le_norm (((Real.cos θ - cosTaylor 10 θ : ℝ) : ℂ) +
    ((Real.sin θ - sinTaylor 10 θ : ℝ) : ℂ) * Complex.I)).trans hb
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
    Complex.mul_im, zero_add] at hre him
  exact ⟨hre, him⟩

theorem encl_cos (θ : ℝ) (hθ : |θ| ≤ 10) :
    Encl.Holds (Real.cos θ) ⟨cosTaylor 10 θ, |θ| ^ 20 / (Nat.factorial 20 : ℝ) * 2⟩ :=
  (cos_sin_taylor_bound hθ).1

theorem encl_sin (θ : ℝ) (hθ : |θ| ≤ 10) :
    Encl.Holds (Real.sin θ) ⟨sinTaylor 10 θ, |θ| ^ 20 / (Nat.factorial 20 : ℝ) * 2⟩ :=
  (cos_sin_taylor_bound hθ).2

end GaloisForLFunctions.HTGeometry
