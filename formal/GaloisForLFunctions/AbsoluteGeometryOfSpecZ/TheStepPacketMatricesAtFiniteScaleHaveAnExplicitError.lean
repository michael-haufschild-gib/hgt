import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheRiemannHypothesisIsTheSignOfWeilsFormOnStepPackets
import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.WherePrecisionIsLost
import GaloisForLFunctions.BezoutValuationIncidence.TheCofinalMobiusSlopeIsThePeriodVariance

/-!
# The step-packet matrices at finite scale have an explicit error

Weil's form on the comb of a divisor constant on the `J` blocks of `B` points above `RB` is, per
point of a block, Weil's form `𝔚_Q` of the step packet up to an explicit error:

  `|combW(block σ)/B − 𝔚_Q(stepPacket σ)| ≤ 6(J + 1)·E(R + J, Q, B)·Σ σ_j²`,
  `E(X, Q, B) = (2X + 16(1 + log 2XB) + 2ψ(Q))/B`,  `ψ(Q) = Σ_{k ≤ Q} Λ(k)`

(`abs_combForm_blockFunction_div_sub_le`). Every piece of the finite form is elementary: harmonic
numbers (`|H_n − H_m − log(n/m)| ≤ 1/m`), log-factorials (Stirling, error `≤ 1 + ½ log n`) and
the contact counts `⌊bN/k⌋ − aN` (error `≤ 1`).

* **Ratios four and seven** (`abs_combForm_blockFunction_div_sub_le_ratioFour`, `…_ratioSeven`):
  the windows `(R, 4R]` and `(R, 7R]` of `𝔚_4` and `𝔚_7`, with `ψ(4) = log 12`,
  `ψ(7) = log 420`.
* **Certified transfer** (`le_combForm_of_packetForm_ge`, `packetForm_ge_of_combForm_ge`): a
  margin `μ₀` of the step-packet matrix gives the sign of the comb at every block size with
  `6(J+1)E ≤ μ₀/2`, and a sign of the comb at one finite block size bounds the matrix from
  below by minus the error. Both are finite statements with explicit constants.
-/

open Finset Filter
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HodgeTheoryOfAFixedPart (blockIndex)

local notation "combW" => HodgeTheoryOfAFixedPart.combForm

/-! ### Harmonic numbers and factorials -/

theorem harm_sub_log_sub_gamma_mem {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ harm n - Real.log n - Real.eulerMascheroniConstant ∧
      harm n - Real.log n - Real.eulerMascheroniConstant ≤ 1 / n := by
  rw [harm_eq_harmonic]
  exact BezoutValuationIncidence.harmonic_sub_log_sub_gamma_mem hn

theorem harm_le_one_add_log (n : ℕ) : harm n ≤ 1 + Real.log n := by
  rw [harm_eq_harmonic]
  exact_mod_cast harmonic_le_one_add_log n

theorem harm_nonneg (n : ℕ) : 0 ≤ harm n :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- `|H_n − H_m − log(n/m)| ≤ 1/m` for `1 ≤ m ≤ n`. -/
theorem abs_harm_sub_harm_sub_log_le {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    |harm n - harm m - (Real.log n - Real.log m)| ≤ 1 / m := by
  obtain ⟨h1, h2⟩ := harm_sub_log_sub_gamma_mem hm
  obtain ⟨h3, h4⟩ := harm_sub_log_sub_gamma_mem (hm.trans hmn)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnm : (1 : ℝ) / n ≤ 1 / m := one_div_le_one_div_of_le hmR (by exact_mod_cast hmn)
  rw [abs_le]
  constructor <;> linarith

/-- `S(xN)/N = x log N + x(log x + γ − 1) + ε` with `0 ≤ ε ≤ 1/N`. -/
theorem harmSum_mul_div_sub_mem (x : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ harmSum (x * N) / N - x * Real.log N -
        x * (Real.log x + Real.eulerMascheroniConstant - 1) ∧
      harmSum (x * N) / N - x * Real.log N -
        x * (Real.log x + Real.eulerMascheroniConstant - 1) ≤ 1 / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp only [zero_mul, harmSum, Nat.cast_zero, sub_self, zero_div]
    exact ⟨le_rfl, by positivity⟩
  · have hxN : 1 ≤ x * N := Nat.one_le_iff_ne_zero.mpr (by positivity)
    obtain ⟨h1, h2⟩ := harm_sub_log_sub_gamma_mem hxN
    have hx' : (0 : ℝ) < x := by exact_mod_cast hx
    have hlog : Real.log ((x * N : ℕ) : ℝ) = Real.log x + Real.log N := by
      push_cast
      exact Real.log_mul hx'.ne' hN'.ne'
    have hval : harmSum (x * N) / N - x * Real.log N -
        x * (Real.log x + Real.eulerMascheroniConstant - 1) =
        x * (harm (x * N) - Real.log ((x * N : ℕ) : ℝ) - Real.eulerMascheroniConstant) := by
      rw [harmSum, hlog]
      push_cast
      field_simp
      ring
    have hone : (x : ℝ) * (1 / ((x * N : ℕ) : ℝ)) = 1 / N := by
      push_cast
      field_simp
    rw [hval]
    exact ⟨mul_nonneg hx'.le h1, (mul_le_mul_of_nonneg_left h2 hx'.le).trans_eq hone⟩

/-! ### The jets at finite scale -/

/-- **The pairing of two flat packets at finite scale**:
`|(X(aN, bN) − Σ_{n ≤ aN} log(n/2π))/N − W(a, b)| ≤ 4(1 + log((b + a)N))/N`. -/
theorem abs_jetCross_sub_counterterm_div_sub_le {a b N : ℕ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hN : 1 ≤ N) :
    |(jetCross (a * N) (b * N) - ∑ n ∈ Icc 1 (a * N), Real.log ((n : ℝ) / (2 * Real.pi))) / N -
        flatPairing a b| ≤ 4 * (1 + Real.log (((b + a) * N : ℕ) : ℝ)) / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hle : a * N ≤ b * N := Nat.mul_le_mul_right N hab
  have haN : 1 ≤ a * N := Nat.one_le_iff_ne_zero.mpr (by positivity)
  set L := Real.log (((b + a) * N : ℕ) : ℝ)
  -- the three harmonic numbers are at most `1 + L`
  have hmono : ∀ M : ℕ, 1 ≤ M → M ≤ (b + a) * N → harm M ≤ 1 + L := fun M hM hMle => by
    have h0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have h1 : (M : ℝ) ≤ (((b + a) * N : ℕ) : ℝ) := by exact_mod_cast hMle
    have := Real.log_le_log h0 h1
    linarith [harm_le_one_add_log M]
  have h₁ := hmono ((b + a) * N) (by nlinarith) le_rfl
  have h₂ := hmono (b * N) (by nlinarith) (Nat.mul_le_mul_right N (Nat.le_add_right b a))
  have h₃ := hmono (a * N) haN (Nat.mul_le_mul_right N (by omega))
  have h₁0 := harm_nonneg ((b + a) * N)
  have h₂0 := harm_nonneg (b * N)
  have h₃0 := harm_nonneg (a * N)
  obtain ⟨e₁0, e₁1⟩ := harmSum_mul_div_sub_mem (b + a) hN
  obtain ⟨e₂0, e₂1⟩ := harmSum_mul_div_sub_mem (b - a) hN
  obtain ⟨e₃0, e₃1⟩ := ArithmeticOfSquareRootPrecision.log_factorial_sub_bounds haN
  have hLa : Real.log ((a * N : ℕ) : ℝ) ≤ L :=
    Real.log_le_log (by exact_mod_cast haN) (by exact_mod_cast Nat.mul_le_mul_right N (by omega))
  have hlogaN : Real.log ((a * N : ℕ) : ℝ) = Real.log a + Real.log N := by
    push_cast
    exact Real.log_mul ha'.ne' hN'.ne'
  -- the exact decomposition of the error
  set e₁ := harmSum ((b + a) * N) / N - ((b + a : ℕ) : ℝ) * Real.log N -
    ((b + a : ℕ) : ℝ) * (Real.log ((b + a : ℕ) : ℝ) + Real.eulerMascheroniConstant - 1)
  set e₂ := harmSum ((b - a) * N) / N - ((b - a : ℕ) : ℝ) * Real.log N -
    ((b - a : ℕ) : ℝ) * (Real.log ((b - a : ℕ) : ℝ) + Real.eulerMascheroniConstant - 1)
  set e₃ := Real.log ((a * N).factorial : ℕ) -
    (((a * N : ℕ) : ℝ) * Real.log ((a * N : ℕ) : ℝ) - ((a * N : ℕ) : ℝ))
  have hval : (jetCross (a * N) (b * N) -
        ∑ n ∈ Icc 1 (a * N), Real.log ((n : ℝ) / (2 * Real.pi))) / N - flatPairing a b =
      (e₁ - e₂) / 2 + ((harm ((b + a) * N) - harm (b * N)) / 2 - 3 / 4 * harm (a * N) - e₃) / N := by
    rw [jetCross_eq hle, sum_log_div_two_pi, ← Nat.sub_mul,
      show b * N + 1 + a * N = (b + a) * N + 1 by ring, harmSum_succ, harmSum_succ]
    simp only [e₁, e₂, e₃, flatPairing, hlogaN]
    rw [Nat.cast_sub hab, Nat.cast_add]
    push_cast
    field_simp
    ring
  rw [hval]
  have hNinv : (0 : ℝ) < 1 / N := by positivity
  have hdiff : |harm ((b + a) * N) - harm (b * N)| ≤ 1 + L := by
    rw [abs_le]; constructor <;> linarith
  have hb1 : |(e₁ - e₂) / 2| ≤ 1 / N := by
    rw [abs_le]; constructor <;> linarith
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast (by nlinarith : 1 ≤ (b + a) * N))
  have hb2 : |((harm ((b + a) * N) - harm (b * N)) / 2 - 3 / 4 * harm (a * N) - e₃) / N| ≤
      3 * (1 + L) / N := by
    rw [abs_div, abs_of_pos hN']
    refine div_le_div_of_nonneg_right ?_ hN'.le
    rw [abs_le] at hdiff ⊢
    constructor <;> linarith [hdiff.1, hdiff.2]
  calc |(e₁ - e₂) / 2 + ((harm ((b + a) * N) - harm (b * N)) / 2 - 3 / 4 * harm (a * N) - e₃) / N|
      ≤ |(e₁ - e₂) / 2| + |((harm ((b + a) * N) - harm (b * N)) / 2 - 3 / 4 * harm (a * N) -
          e₃) / N| := abs_add_le _ _
    _ ≤ 1 / N + 3 * (1 + L) / N := add_le_add hb1 hb2
    _ ≤ 4 * (1 + L) / N := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by linarith) hN'.le

/-- **The energy of a window at finite scale**: within `16(1 + log 2bN)/N` of
`W(b, b) − 2W(a, b) + W(a, a)`. -/
theorem abs_windowEnergy_sub_counterterm_div_sub_le {a b N : ℕ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hN : 1 ≤ N) :
    |(windowEnergy (a * N) (b * N) -
          ∑ n ∈ Ioc (a * N) (b * N), Real.log ((n : ℝ) / (2 * Real.pi))) / N -
        (flatPairing b b - 2 * flatPairing a b + flatPairing a a)| ≤
      16 * (1 + Real.log ((2 * b * N : ℕ) : ℝ)) / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hle : a * N ≤ b * N := Nat.mul_le_mul_right N hab
  have hI : Icc 1 (b * N) = Icc 1 (a * N) ∪ Ioc (a * N) (b * N) := by
    ext k
    simp only [mem_Icc, mem_union, mem_Ioc]
    omega
  have hd : Disjoint (Icc 1 (a * N)) (Ioc (a * N) (b * N)) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [mem_Icc, mem_Ioc] at hk hk'
    omega
  have hct : ∑ n ∈ Icc 1 (b * N), Real.log ((n : ℝ) / (2 * Real.pi)) =
      ∑ n ∈ Icc 1 (a * N), Real.log ((n : ℝ) / (2 * Real.pi)) +
        ∑ n ∈ Ioc (a * N) (b * N), Real.log ((n : ℝ) / (2 * Real.pi)) := by
    rw [hI, Finset.sum_union hd]
  set A := fun x y : ℕ => (jetCross (x * N) (y * N) -
    ∑ n ∈ Icc 1 (x * N), Real.log ((n : ℝ) / (2 * Real.pi))) / N
  have hval : (windowEnergy (a * N) (b * N) -
        ∑ n ∈ Ioc (a * N) (b * N), Real.log ((n : ℝ) / (2 * Real.pi))) / N -
      (flatPairing b b - 2 * flatPairing a b + flatPairing a a) =
      (A b b - flatPairing b b) - 2 * (A a b - flatPairing a b) + (A a a - flatPairing a a) := by
    simp only [A]
    rw [windowEnergy_eq hle, hct]
    field_simp
    ring
  rw [hval]
  have hbb := abs_jetCross_sub_counterterm_div_sub_le (ha.trans hab) le_rfl hN
  have hab' := abs_jetCross_sub_counterterm_div_sub_le ha hab hN
  have haa := abs_jetCross_sub_counterterm_div_sub_le ha le_rfl hN
  have hlog : ∀ y : ℕ, y ≤ 2 * b → 1 ≤ y →
      Real.log ((y * N : ℕ) : ℝ) ≤ Real.log ((2 * b * N : ℕ) : ℝ) := fun y hy hy1 =>
    Real.log_le_log (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity))
      (by exact_mod_cast Nat.mul_le_mul_right N hy)
  have l1 := hlog (b + b) (by omega) (by omega)
  have l2 := hlog (b + a) (by omega) (by omega)
  have l3 := hlog (a + a) (by omega) (by omega)
  have hf : ∀ {u v : ℝ}, u ≤ v → 4 * (1 + u) / N ≤ 4 * (1 + v) / N := fun h =>
    div_le_div_of_nonneg_right (by linarith) hN'.le
  calc |(A b b - flatPairing b b) - 2 * (A a b - flatPairing a b) + (A a a - flatPairing a a)|
      ≤ |A b b - flatPairing b b| + 2 * |A a b - flatPairing a b| + |A a a - flatPairing a a| := by
        have h := abs_add_le ((A b b - flatPairing b b) - 2 * (A a b - flatPairing a b))
          (A a a - flatPairing a a)
        have h' := abs_sub ((A b b - flatPairing b b)) (2 * (A a b - flatPairing a b))
        rw [abs_mul, abs_two] at h'
        linarith
    _ ≤ 4 * (1 + Real.log ((2 * b * N : ℕ) : ℝ)) / N +
          2 * (4 * (1 + Real.log ((2 * b * N : ℕ) : ℝ)) / N) +
          4 * (1 + Real.log ((2 * b * N : ℕ) : ℝ)) / N := by
        gcongr
        · exact hbb.trans (hf l1)
        · exact hab'.trans (hf l2)
        · exact haa.trans (hf l3)
    _ = 16 * (1 + Real.log ((2 * b * N : ℕ) : ℝ)) / N := by ring

/-! ### One window at finite scale -/

/-- The contacts of ratio `k ≥ 2` in `(aN, bN]`: the `m ∈ (aN, ⌊bN/k⌋]`. -/
theorem filter_contact_window {a b N k : ℕ} (hk : 2 ≤ k) :
    (Ioc (a * N) (b * N)).filter (fun m => k * m ∈ Ioc (a * N) (b * N)) =
      Ioc (a * N) (b * N / k) := by
  ext m
  simp only [mem_filter, mem_Ioc]
  have hk0 : 0 < k := by omega
  constructor
  · rintro ⟨⟨h1, -⟩, -, h4⟩
    exact ⟨h1, (Nat.le_div_iff_mul_le hk0).mpr (by rw [mul_comm]; exact h4)⟩
  · rintro ⟨h1, h2⟩
    have h3 : k * m ≤ b * N := by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hk0).mp h2
    refine ⟨⟨h1, le_trans (Nat.le_div_iff_mul_le hk0 |>.mp h2 |>.trans' ?_) le_rfl⟩, ?_, h3⟩
    · exact Nat.le_mul_of_pos_right m hk0
    · exact h1.trans_le (Nat.le_mul_of_pos_left m hk0)

/-- The contact count of ratio `k` is `(b/k − a)⁺ N` up to one. -/
theorem abs_contactCount_div_sub_le {a b N k : ℕ} (hk : 2 ≤ k) (hN : 1 ≤ N) :
    |(((Ioc (a * N) (b * N)).filter fun m => k * m ∈ Ioc (a * N) (b * N)).card : ℝ) / N -
        max ((b : ℝ) / k - a) 0| ≤ 1 / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hk' : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  rw [filter_contact_window hk, Nat.card_Ioc]
  set f := b * N / k
  have hf1 : (f : ℝ) ≤ (b : ℝ) * N / k := by
    rw [le_div_iff₀ hk']
    exact_mod_cast Nat.div_mul_le_self (b * N) k
  have hf2 : (b : ℝ) * N / k < f + 1 := by
    rw [div_lt_iff₀ hk']
    have := Nat.lt_div_mul_add (a := b * N) (b := k) (by omega)
    have h' : ((b * N : ℕ) : ℝ) < ((b * N / k * k + k : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h'
    nlinarith
  have hmax : max ((b : ℝ) / k - a) 0 * N = max ((b : ℝ) * N / k - a * N) 0 := by
    rw [max_mul_of_nonneg _ _ hN'.le, zero_mul]
    congr 1
    field_simp
  have hcast : ((f - a * N : ℕ) : ℝ) = max ((f : ℝ) - a * N) 0 := by
    rcases le_total (a * N) f with h | h
    · have h' : ((a * N : ℕ) : ℝ) ≤ f := by exact_mod_cast h
      push_cast at h'
      rw [Nat.cast_sub h, max_eq_left (by linarith)]
      push_cast
      ring
    · have h' : (f : ℝ) ≤ ((a * N : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at h'
      rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, max_eq_right (by linarith)]
  have hkey : |max ((f : ℝ) - a * N) 0 - max ((b : ℝ) * N / k - a * N) 0| ≤ 1 := by
    have := abs_max_sub_max_le_abs ((f : ℝ) - a * N) ((b : ℝ) * N / k - a * N) 0
    refine this.trans ?_
    rw [abs_le]
    constructor <;> linarith
  rw [hcast, show max ((b : ℝ) / k - a) 0 = max ((b : ℝ) * N / k - a * N) 0 / N by
    rw [← hmax]; field_simp, ← sub_div, abs_div, abs_of_pos hN']
  exact div_le_div_of_nonneg_right hkey hN'.le

/-- The error scale of a window of length at most `X` with contacts up to `Q` at block size
`N`. -/
def windowError (X Q N : ℕ) : ℝ :=
  (2 * X + 16 * (1 + Real.log ((2 * X * N : ℕ) : ℝ)) + 2 * ∑ k ∈ Icc 2 Q, (Λ k : ℝ)) / N

theorem windowError_nonneg (X Q N : ℕ) : 0 ≤ windowError X Q N := by
  unfold windowError
  refine div_nonneg ?_ (Nat.cast_nonneg _)
  have h1 : 0 ≤ Real.log ((2 * X * N : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have h2 : 0 ≤ ∑ k ∈ Icc 2 Q, (Λ k : ℝ) :=
    Finset.sum_nonneg fun k _ => ArithmeticFunction.vonMangoldt_nonneg
  positivity

theorem windowError_mono {X Y Q N : ℕ} (hXY : X ≤ Y) (hX : 1 ≤ X) :
    windowError X Q N ≤ windowError Y Q N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [windowError]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold windowError
  refine div_le_div_of_nonneg_right ?_ hN'.le
  have hlog : Real.log ((2 * X * N : ℕ) : ℝ) ≤ Real.log ((2 * Y * N : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity))
      (by exact_mod_cast Nat.mul_le_mul_right N (Nat.mul_le_mul_left 2 hXY))
  have hXY' : (X : ℝ) ≤ Y := by exact_mod_cast hXY
  linarith

/-- **One window at finite scale.** For `1 ≤ a ≤ b ≤ Qa`,
`|combW((aN, bN])/N − 𝔚_Q(flatPacket a b)| ≤ E(b, Q, N)`. -/
theorem abs_combForm_window_div_sub_le {a b Q N : ℕ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hQ : b ≤ Q * a) (hN : 1 ≤ N) :
    |combW (Ioc (a * N) (b * N)) (fun _ => 1) / N - packetForm Q (flatPacket a b)| ≤
      windowError b Q N := by
  rcases hab.eq_or_lt with rfl | hlt
  · have h0 : combW (Ioc (a * N) (a * N)) (fun _ => (1 : ℝ)) / N = 0 := by
      rw [Finset.Ioc_self]
      simp [HodgeTheoryOfAFixedPart.combForm, HodgeTheoryOfAFixedPart.combPairing,
        HodgeTheoryOfAFixedPart.degOne, HodgeTheoryOfAFixedPart.degTwo]
    rw [h0, flatPacket_self, packetForm_zero, sub_zero, abs_zero]
    exact windowError_nonneg _ _ _
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have hle : a * N ≤ b * N := Nat.mul_le_mul_right N hab
  have haN : 1 ≤ a * N := Nat.one_le_iff_ne_zero.mpr (by positivity)
  -- the contacts, the energy and the counterterm as atoms
  have hS : ∑ k ∈ Icc 2 Q, (Λ k : ℝ) *
        ((((Ioc (a * N) (b * N)).filter fun m => k * m ∈ Ioc (a * N) (b * N)).card : ℝ) / N -
          max ((b : ℝ) / k - a) 0) =
      (∑ k ∈ Icc 2 Q, (Λ k : ℝ) *
        (((Ioc (a * N) (b * N)).filter fun m => k * m ∈ Ioc (a * N) (b * N)).card : ℝ)) / N -
        ∑ k ∈ Icc 2 Q, (Λ k : ℝ) * max ((b : ℝ) / k - a) 0 := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hval : combW (Ioc (a * N) (b * N)) (fun _ => 1) / N - packetForm Q (flatPacket a b) =
      2 * ((b : ℝ) - a) * (harm (b * N) - harm (a * N) - (Real.log b - Real.log a)) -
        ((windowEnergy (a * N) (b * N) -
            ∑ n ∈ Ioc (a * N) (b * N), Real.log ((n : ℝ) / (2 * Real.pi))) / N -
          (flatPairing b b - 2 * flatPairing a b + flatPairing a a)) -
        2 * ∑ k ∈ Icc 2 Q, (Λ k : ℝ) *
          ((((Ioc (a * N) (b * N)).filter fun m => k * m ∈ Ioc (a * N) (b * N)).card : ℝ) / N -
            max ((b : ℝ) / k - a) 0) := by
    rw [hS, combForm_window_eq hle ((Nat.mul_le_mul_right N hQ).trans_eq (Nat.mul_assoc Q a N)),
      packetForm_flatPacket_eq ha hlt Q]
    set SC := ∑ k ∈ Icc 2 Q, (Λ k : ℝ) *
      (((Ioc (a * N) (b * N)).filter fun m => k * m ∈ Ioc (a * N) (b * N)).card : ℝ)
    set E0 := windowEnergy (a * N) (b * N)
    set L0 := ∑ n ∈ Ioc (a * N) (b * N), Real.log ((n : ℝ) / (2 * Real.pi))
    set M0 := ∑ k ∈ Icc 2 Q, (Λ k : ℝ) * max ((b : ℝ) / k - a) 0
    push_cast
    field_simp
    ring
  rw [hval]
  have hharm := abs_harm_sub_harm_sub_log_le haN hle
  have hlogd : Real.log ((b * N : ℕ) : ℝ) - Real.log ((a * N : ℕ) : ℝ) =
      Real.log b - Real.log a := by
    push_cast
    rw [Real.log_mul hb0 hN'.ne', Real.log_mul ha'.ne' hN'.ne']
    ring
  rw [hlogd] at hharm
  have hT1 : |2 * ((b : ℝ) - a) * (harm (b * N) - harm (a * N) - (Real.log b - Real.log a))| ≤
      2 * b / N := by
    have hba : (0 : ℝ) ≤ (b : ℝ) - a := sub_nonneg.mpr (by exact_mod_cast hab)
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ((b : ℝ) - a))]
    have h1 : (1 : ℝ) / ((a * N : ℕ) : ℝ) ≤ 1 / N := by
      apply one_div_le_one_div_of_le hN'
      exact_mod_cast Nat.le_mul_of_pos_left N ha
    calc 2 * ((b : ℝ) - a) * |harm (b * N) - harm (a * N) - (Real.log b - Real.log a)|
        ≤ 2 * b * (1 / N) := by
          apply mul_le_mul (by linarith) (hharm.trans h1) (abs_nonneg _) (by positivity)
      _ = 2 * b / N := by ring
  have hT2 := abs_windowEnergy_sub_counterterm_div_sub_le ha hab hN
  have hT3 : |2 * ∑ k ∈ Icc 2 Q, (Λ k : ℝ) *
        ((((Ioc (a * N) (b * N)).filter fun m => k * m ∈ Ioc (a * N) (b * N)).card : ℝ) / N -
          max ((b : ℝ) / k - a) 0)| ≤ 2 * (∑ k ∈ Icc 2 Q, (Λ k : ℝ)) / N := by
    rw [abs_mul, abs_two, mul_div_assoc, Finset.sum_div]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun k hk => ?_)) (by norm_num)
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, div_eq_mul_one_div (Λ k : ℝ)]
    exact mul_le_mul_of_nonneg_left (abs_contactCount_div_sub_le hk2 hN)
      ArithmeticFunction.vonMangoldt_nonneg
  set X1 := 2 * ((b : ℝ) - a) * (harm (b * N) - harm (a * N) - (Real.log b - Real.log a))
  set X2 := (windowEnergy (a * N) (b * N) -
      ∑ n ∈ Ioc (a * N) (b * N), Real.log ((n : ℝ) / (2 * Real.pi))) / N -
    (flatPairing b b - 2 * flatPairing a b + flatPairing a a)
  set X3 := 2 * ∑ k ∈ Icc 2 Q, (Λ k : ℝ) *
    ((((Ioc (a * N) (b * N)).filter fun m => k * m ∈ Ioc (a * N) (b * N)).card : ℝ) / N -
      max ((b : ℝ) / k - a) 0)
  have htri : |X1 - X2 - X3| ≤ |X1| + |X2| + |X3| := by
    have h1 := abs_sub (X1 - X2) X3
    have h2 := abs_sub X1 X2
    linarith
  refine htri.trans ((add_le_add (add_le_add hT1 hT2) hT3).trans_eq ?_)
  unfold windowError
  ring

/-! ### Step packets at finite scale -/

/-- The entries of the nested windows at finite scale are within `3E` of the limit entries. -/
theorem abs_nestedEntry_sub_stepEntry_le {ι : Type*} {s : Finset ι} {x : ι → ℕ} {x₀ X Q N : ℕ}
    (hx₀ : 1 ≤ x₀) (hx : ∀ j ∈ s, x₀ ≤ x j ∧ x j ≤ X) (hQ : X ≤ Q * x₀) (hN : 1 ≤ N)
    {j l : ι} (hj : j ∈ s) (hl : l ∈ s) :
    |nestedEntry x₀ x N j l - stepEntry Q x₀ x j l| ≤ 3 * windowError X Q N := by
  have hX : 1 ≤ X := hx₀.trans ((hx j hj).1.trans (hx j hj).2)
  have hmin : x₀ ≤ min (x j) (x l) := le_min (hx j hj).1 (hx l hl).1
  have hmax : max (x j) (x l) ≤ X := max_le (hx j hj).2 (hx l hl).2
  have e1 := (abs_combForm_window_div_sub_le hx₀ (hx j hj).1 ((hx j hj).2.trans hQ) hN).trans
    (windowError_mono (hx j hj).2 (hx₀.trans (hx j hj).1))
  have e2 := (abs_combForm_window_div_sub_le hx₀ (hx l hl).1 ((hx l hl).2.trans hQ) hN).trans
    (windowError_mono (hx l hl).2 (hx₀.trans (hx l hl).1))
  have e3 := (abs_combForm_window_div_sub_le (Q := Q) (hx₀.trans hmin) min_le_max
    (hmax.trans (hQ.trans (Nat.mul_le_mul_left Q hmin))) hN).trans
    (windowError_mono hmax ((hx₀.trans hmin).trans min_le_max))
  have hval : nestedEntry x₀ x N j l - stepEntry Q x₀ x j l =
      (combW (Ioc (x₀ * N) (x j * N)) (fun _ => 1) / N - packetForm Q (flatPacket x₀ (x j))) +
      (combW (Ioc (x₀ * N) (x l * N)) (fun _ => 1) / N - packetForm Q (flatPacket x₀ (x l))) -
      (combW (Ioc (min (x j) (x l) * N) (max (x j) (x l) * N)) (fun _ => 1) / N -
        packetForm Q (flatPacket (min (x j) (x l) : ℕ) (max (x j) (x l) : ℕ))) := by
    rw [nestedEntry, stepEntry]
    ring
  rw [hval]
  have h := abs_sub (combW (Ioc (x₀ * N) (x j * N)) (fun _ => 1) / N -
    packetForm Q (flatPacket x₀ (x j)) + (combW (Ioc (x₀ * N) (x l * N)) (fun _ => 1) / N -
      packetForm Q (flatPacket x₀ (x l))))
    (combW (Ioc (min (x j) (x l) * N) (max (x j) (x l) * N)) (fun _ => 1) / N -
      packetForm Q (flatPacket (min (x j) (x l) : ℕ) (max (x j) (x l) : ℕ)))
  have h' := abs_add_le (combW (Ioc (x₀ * N) (x j * N)) (fun _ => 1) / N -
    packetForm Q (flatPacket x₀ (x j))) (combW (Ioc (x₀ * N) (x l * N)) (fun _ => 1) / N -
      packetForm Q (flatPacket x₀ (x l)))
  linarith

/-- **The block approximation with an explicit error.** For a divisor constant on the `J` blocks
of `B` points above `RB` and `R + J ≤ QR`:
`|combW(block σ)/B − 𝔚_Q(stepPacket σ)| ≤ 6(J + 1) E(R + J, Q, B) Σ σ_j²`. -/
theorem abs_combForm_blockFunction_div_sub_le {R J Q B : ℕ} (hR : 1 ≤ R) (hQ : R + J ≤ Q * R)
    (hB : 1 ≤ B) (σ : ℕ → ℝ) :
    |combW (Ioc (R * B) (R * B + B * J)) (fun n => σ (blockIndex (R * B) B n)) / B -
        packetForm Q (stepPacket R J σ)| ≤
      6 * (J + 1) * windowError (R + J) Q B * ∑ j ∈ range J, σ j ^ 2 := by
  have hwin : (R + J) * B = R * B + B * J := by ring
  have hc : combW (Ioc (R * B) (R * B + B * J)) (fun n => σ (blockIndex (R * B) B n)) =
      combW (Ioc (R * B) ((R + J) * B)) (fun n => ∑ j ∈ range (J + 1),
        nestedCoeff J σ j * windowDivisor (R * B) ((R + j) * B) n) := by
    rw [hwin]
    exact combForm_congr fun n hn => blockFunction_eq_nested (by omega) σ hn
  have hp : packetForm Q (stepPacket R J σ) =
      packetForm Q (fun u => ∑ j ∈ range (J + 1),
        nestedCoeff J σ j * flatPacket (R : ℝ) ((R + j : ℕ) : ℝ) u) := by
    rw [stepPacket_eq_nested hR J σ]
  rw [hc, hp, combForm_nested_eq (x := fun j => R + j) (nested_bounds R J) (nestedCoeff J σ) B,
    packetForm_nested_eq (x := fun j => R + j) hR (nested_bounds R J) (nestedCoeff J σ),
    ← mul_sub, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, ← mul_sub]
  have hδ := abs_half_sum_sum_le (s := range (J + 1)) (nestedCoeff J σ)
    (fun j l => nestedEntry R (fun j => R + j) B j l - stepEntry Q R (fun j => R + j) j l)
    (δ := 3 * windowError (R + J) Q B) fun j hj l hl =>
      abs_nestedEntry_sub_stepEntry_le hR (nested_bounds R J) hQ hB hj hl
  refine hδ.trans ?_
  rw [Finset.card_range]
  have hsq := sum_nestedCoeff_sq_le J σ
  have hE := windowError_nonneg (R + J) Q B
  push_cast
  nlinarith [mul_nonneg hE (by positivity : (0 : ℝ) ≤ (J : ℝ) + 1)]

/-! ### Certified transfer -/

/-- **From the matrix to the comb.** If `𝔚_Q ≥ μ₀ Σσ²` on the step packets of `J` blocks, then at
every block size `B` with `6(J + 1)E ≤ μ₀/2` the comb form on block divisors is at least
`(μ₀/2) B Σσ²`. -/
theorem le_combForm_of_packetForm_ge {R J Q B : ℕ} (hR : 1 ≤ R) (hQ : R + J ≤ Q * R)
    (hB : 1 ≤ B) {μ₀ : ℝ} (hμ₀ : ∀ σ : ℕ → ℝ,
      μ₀ * ∑ j ∈ range J, σ j ^ 2 ≤ packetForm Q (stepPacket R J σ))
    (hsmall : 6 * (J + 1) * windowError (R + J) Q B ≤ μ₀ / 2) (σ : ℕ → ℝ) :
    μ₀ / 2 * B * ∑ j ∈ range J, σ j ^ 2 ≤
      combW (Ioc (R * B) (R * B + B * J)) (fun n => σ (blockIndex (R * B) B n)) := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have h := abs_combForm_blockFunction_div_sub_le hR hQ hB σ
  have hS : 0 ≤ ∑ j ∈ range J, σ j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hlow := (abs_le.mp h).1
  have h1 : μ₀ / 2 * ∑ j ∈ range J, σ j ^ 2 ≤
      combW (Ioc (R * B) (R * B + B * J)) (fun n => σ (blockIndex (R * B) B n)) / B := by
    have := hμ₀ σ
    nlinarith
  rw [le_div_iff₀ hB'] at h1
  linarith

/-- **From the comb to the matrix.** A lower bound of the comb form at one block size bounds
`𝔚_Q` on the step packet from below, up to the explicit error. -/
theorem packetForm_ge_of_combForm_ge {R J Q B : ℕ} (hR : 1 ≤ R) (hQ : R + J ≤ Q * R)
    (hB : 1 ≤ B) {c : ℝ} (σ : ℕ → ℝ)
    (hc : c * B * ∑ j ∈ range J, σ j ^ 2 ≤
      combW (Ioc (R * B) (R * B + B * J)) (fun n => σ (blockIndex (R * B) B n))) :
    (c - 6 * (J + 1) * windowError (R + J) Q B) * ∑ j ∈ range J, σ j ^ 2 ≤
      packetForm Q (stepPacket R J σ) := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have h := (abs_le.mp (abs_combForm_blockFunction_div_sub_le hR hQ hB σ)).2
  have h1 : c * ∑ j ∈ range J, σ j ^ 2 ≤
      combW (Ioc (R * B) (R * B + B * J)) (fun n => σ (blockIndex (R * B) B n)) / B := by
    rw [le_div_iff₀ hB']
    linarith
  nlinarith

/-! ### Ratios four and seven -/

theorem sum_vonMangoldt_Icc_two_four : ∑ k ∈ Icc 2 4, (Λ k : ℝ) = Real.log 12 := by
  rw [show Icc 2 4 = {2, 3, 4} by rfl, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three,
    show (4 : ℕ) = 2 ^ 2 by norm_num,
    ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
    ← Real.log_mul (by norm_num) (by norm_num), ← Real.log_mul (by norm_num) (by norm_num)]
  norm_num

theorem sum_vonMangoldt_Icc_two_seven : ∑ k ∈ Icc 2 7, (Λ k : ℝ) = Real.log 420 := by
  have h6 : Λ 6 = 0 := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr (by
    rw [show (6 : ℕ) = 2 * 3 by norm_num]
    exact fun h => by
      obtain ⟨p, k, hp, hk, he⟩ := (isPrimePow_nat_iff _).mp h
      have h2 : 2 ∣ p ^ k := he ▸ dvd_mul_right 2 3
      have h3 : 3 ∣ p ^ k := he ▸ dvd_mul_left 3 2
      have hp2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
        (Nat.prime_two.dvd_of_dvd_pow h2)
      have hp3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega)
  rw [show Icc 2 7 = {2, 3, 4, 5, 6, 7} by rfl]
  simp only [Finset.sum_insert (show (2 : ℕ) ∉ ({3, 4, 5, 6, 7} : Finset ℕ) by decide),
    Finset.sum_insert (show (3 : ℕ) ∉ ({4, 5, 6, 7} : Finset ℕ) by decide),
    Finset.sum_insert (show (4 : ℕ) ∉ ({5, 6, 7} : Finset ℕ) by decide),
    Finset.sum_insert (show (5 : ℕ) ∉ ({6, 7} : Finset ℕ) by decide),
    Finset.sum_insert (show (6 : ℕ) ∉ ({7} : Finset ℕ) by decide), Finset.sum_singleton]
  rw [h6, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three,
    show (4 : ℕ) = 2 ^ 2 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 7)]
  rw [show (420 : ℝ) = 2 * 3 * 2 * 5 * 7 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]
  push_cast
  ring

/-- **Ratio four** (`𝔚_4` on the window `(R, 4R]`, `3R` blocks). -/
theorem abs_combForm_blockFunction_div_sub_le_ratioFour {R B : ℕ} (hR : 1 ≤ R) (hB : 1 ≤ B)
    (σ : ℕ → ℝ) :
    |combW (Ioc (R * B) (R * B + B * (3 * R))) (fun n => σ (blockIndex (R * B) B n)) / B -
        packetForm 4 (stepPacket R (3 * R) σ)| ≤
      6 * (3 * R + 1) * ((8 * R + 16 * (1 + Real.log ((8 * R * B : ℕ) : ℝ)) + 2 * Real.log 12) / B) *
        ∑ j ∈ range (3 * R), σ j ^ 2 := by
  have h := abs_combForm_blockFunction_div_sub_le (J := 3 * R) (Q := 4) hR (by omega) hB σ
  rw [windowError, sum_vonMangoldt_Icc_two_four, show 2 * (R + 3 * R) * B = 8 * R * B by ring]
    at h
  push_cast at h ⊢
  convert h using 3
  ring

/-- **Ratio seven** (`𝔚_7` on the window `(R, 7R]`, `6R` blocks). -/
theorem abs_combForm_blockFunction_div_sub_le_ratioSeven {R B : ℕ} (hR : 1 ≤ R) (hB : 1 ≤ B)
    (σ : ℕ → ℝ) :
    |combW (Ioc (R * B) (R * B + B * (6 * R))) (fun n => σ (blockIndex (R * B) B n)) / B -
        packetForm 7 (stepPacket R (6 * R) σ)| ≤
      6 * (6 * R + 1) *
        ((14 * R + 16 * (1 + Real.log ((14 * R * B : ℕ) : ℝ)) + 2 * Real.log 420) / B) *
        ∑ j ∈ range (6 * R), σ j ^ 2 := by
  have h := abs_combForm_blockFunction_div_sub_le (J := 6 * R) (Q := 7) hR (by omega) hB σ
  rw [windowError, sum_vonMangoldt_Icc_two_seven, show 2 * (R + 6 * R) * B = 14 * R * B by ring]
    at h
  push_cast at h ⊢
  convert h using 3
  ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
