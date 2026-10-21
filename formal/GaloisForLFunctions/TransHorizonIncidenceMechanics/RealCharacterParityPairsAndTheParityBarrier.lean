import GaloisForLFunctions.TransHorizonIncidenceMechanics.CharacterFourParityPairAtEveryDamping
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Parity pairs of every real character, and the parity barrier

Let `χ` be a nontrivial integer-valued multiplicative character modulo `q` (a real Dirichlet
character) and `s(d) = χ(d)`. Over a period `Σ_{a mod q} χ(a) = 0`, so the partial sums of `s` are
bounded by `q`, and the receiver of `c_χ(d) = χ(d) d^{-ε}` is bounded at every damping `ε > 0`. The
twist of its Ramanujan coefficients `W_χ(e) = (c_χ(e)/e) L_χ` by `χ(e)` (the parity of the inert
prime factors of `e`) gives `χ(e)² e^{-1-ε} L_χ`, realised up to the sign of `L_χ` by the
nonnegative weight `c_+(d) = (|L_χ|/O_χ) 1_{(d,q)=1} d^{-ε}`, whose drift on the residues
`1 + qj ∈ (n, 2n]` diverges for `ε ≤ 1/2`. The value `L_χ = L(1+ε, χ)` is nonzero by the
nonvanishing of Dirichlet `L`-series on `Re s > 1`. So **every real non-principal character gives a
parity pair at every `0 < ε ≤ 1/2`.**

**The parity barrier.** For `0 < ε ≤ 1/2` and every `K > 0`, boundedness of the receiver is not a
function of the Ramanujan amplitudes on the class `|c(d)| ≤ K d^{-ε}`: a rescaled character pair lies
in the class with equal amplitudes and opposite receivers. A receiver estimate below half damping must
read the signs of the coefficients.
-/

open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

variable {q : ℕ} [NeZero q]

/-! ### Real characters on `ℕ` -/

/-- A real character modulo `q`, read on `ℕ`. -/
def charSign (χ : MulChar (ZMod q) ℤ) (d : ℕ) : ℝ := ((χ (d : ZMod q) : ℤ) : ℝ)

omit [NeZero q] in
theorem charSign_mul (χ : MulChar (ZMod q) ℤ) (a b : ℕ) :
    charSign χ (a * b) = charSign χ a * charSign χ b := by
  simp [charSign, Nat.cast_mul, map_mul]

omit [NeZero q] in
theorem charSign_one (χ : MulChar (ZMod q) ℤ) : charSign χ 1 = 1 := by
  simp [charSign]

theorem charSign_sq_eq (χ : MulChar (ZMod q) ℤ) (d : ℕ) :
    charSign χ d ^ 2 = if IsUnit (d : ZMod q) then 1 else 0 := by
  unfold charSign
  split_ifs with hu
  · have hχ : IsUnit (χ (d : ZMod q)) := hu.map χ.toMonoidHom
    rcases Int.isUnit_iff.mp hχ with h | h <;> rw [h] <;> norm_num
  · rw [χ.map_nonunit hu]; norm_num

theorem abs_charSign_le (χ : MulChar (ZMod q) ℤ) (d : ℕ) : |charSign χ d| ≤ 1 := by
  have h := charSign_sq_eq χ d
  rw [← sq_abs] at h
  have h0 := abs_nonneg (charSign χ d)
  split_ifs at h <;> nlinarith

omit [NeZero q] in
theorem charSign_mul_period_add (χ : MulChar (ZMod q) ℤ) (k i : ℕ) :
    charSign χ (q * k + i) = charSign χ i := by
  simp [charSign, Nat.cast_add, Nat.cast_mul]

/-- **Bounded partial sums.** A nontrivial real character has `|Σ_{d < x} χ(d)| ≤ q`. -/
theorem abs_sum_range_charSign_le {χ : MulChar (ZMod q) ℤ} (hχ : χ ≠ 1) (x : ℕ) :
    |∑ d ∈ range x, charSign χ d| ≤ q := by
  have hperiod : ∑ d ∈ range q, charSign χ d = 0 := by
    have hsum := MulChar.sum_eq_zero_of_ne_one hχ
    have hbij : ∑ a : ZMod q, ((χ a : ℤ) : ℝ) = ∑ d ∈ range q, charSign χ d := by
      refine Finset.sum_nbij' (fun a => a.val) (fun d => (d : ZMod q)) ?_ ?_ ?_ ?_ ?_
      · intro a _; exact mem_range.mpr (ZMod.val_lt a)
      · intro d _; exact mem_univ _
      · intro a _; exact ZMod.natCast_zmod_val a
      · intro d hd; exact ZMod.val_natCast_of_lt (mem_range.mp hd)
      · intro a _; simp [charSign]
    rw [← hbij]
    exact_mod_cast hsum
  have hblocks : ∀ k, ∑ d ∈ range (q * k), charSign χ d = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show q * (k + 1) = q * k + q by ring, Finset.sum_range_add, ih, zero_add, ← hperiod]
      exact sum_congr rfl fun i _ => charSign_mul_period_add χ k i
  have hx : x = q * (x / q) + x % q := (Nat.div_add_mod x q).symm
  rw [hx, Finset.sum_range_add, hblocks, zero_add]
  simp_rw [charSign_mul_period_add]
  calc |∑ i ∈ range (x % q), charSign χ i| ≤ ∑ i ∈ range (x % q), |charSign χ i| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ range (x % q), (1 : ℝ) := sum_le_sum fun i _ => abs_charSign_le χ i
    _ = (x % q : ℕ) := by simp
    _ ≤ q := by exact_mod_cast (Nat.mod_lt x (NeZero.pos q)).le

/-! ### The pair -/

/-- The unit indicator `1_{(d,q)=1} = χ(d)²`. -/
def charUnit (χ : MulChar (ZMod q) ℤ) (d : ℕ) : ℝ := charSign χ d ^ 2

omit [NeZero q] in
theorem charUnit_mul (χ : MulChar (ZMod q) ℤ) (a b : ℕ) :
    charUnit χ (a * b) = charUnit χ a * charUnit χ b := by
  simp [charUnit, charSign_mul, mul_pow]

omit [NeZero q] in
theorem charUnit_nonneg (χ : MulChar (ZMod q) ℤ) (d : ℕ) : 0 ≤ charUnit χ d := sq_nonneg _

/-- `L_χ = Σ_d χ(d) d^{-1-ε}`. -/
def charDampedMass (χ : MulChar (ZMod q) ℤ) (ε : ℝ) : ℝ :=
  ∑' d : ℕ, dampedSignWeight (charSign χ) ε d / d

/-- `O_χ = Σ_{(d,q)=1} d^{-1-ε}`. -/
def charUnitMass (χ : MulChar (ZMod q) ℤ) (ε : ℝ) : ℝ :=
  ∑' d : ℕ, dampedSignWeight (charUnit χ) ε d / d

/-- The positive twin `c_+(d) = (|L_χ|/O_χ) 1_{(d,q)=1} d^{-ε}`. -/
def charTwinWeight (χ : MulChar (ZMod q) ℤ) (ε : ℝ) (d : ℕ) : ℝ :=
  |charDampedMass χ ε| / charUnitMass χ ε * dampedSignWeight (charUnit χ) ε d

theorem summable_charUnit_weight (χ : MulChar (ZMod q) ℤ) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun d : ℕ => dampedSignWeight (charUnit χ) ε d / d) := by
  refine (Real.summable_nat_rpow.mpr (by linarith : -(1 + ε) < -1)).of_norm_bounded fun d => ?_
  rw [dampedSignWeight_div hε, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _), abs_of_nonneg (charUnit_nonneg χ d)]
  have : charUnit χ d ≤ 1 := by
    have h := abs_charSign_le χ d
    have := sq_abs (charSign χ d)
    unfold charUnit; nlinarith [abs_nonneg (charSign χ d)]
  nlinarith [Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) d) (-(1 + ε))]

theorem charUnitMass_pos (χ : MulChar (ZMod q) ℤ) {ε : ℝ} (hε : 0 < ε) : 0 < charUnitMass χ ε := by
  have h := (summable_charUnit_weight χ hε).le_tsum 1 (fun d _ => by
    rw [dampedSignWeight_div hε]
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _) (charUnit_nonneg χ d))
  have h1 : dampedSignWeight (charUnit χ) ε 1 / (1 : ℕ) = 1 := by
    simp [dampedSignWeight, charUnit, charSign_one]
  unfold charUnitMass
  linarith

omit [NeZero q] in
/-- `L(1+ε, χ) ≠ 0`, from the nonvanishing of Dirichlet `L`-series on `Re s > 1`. -/
theorem charDampedMass_ne_zero {χ : MulChar (ZMod q) ℤ} {ε : ℝ} (hε : 0 < ε) :
    charDampedMass χ ε ≠ 0 := by
  set χC : DirichletCharacter ℂ q := χ.ringHomComp (Int.castRingHom ℂ)
  have hne := DirichletCharacter.LSeries_ne_zero_of_one_lt_re χC (s := ((1 + ε : ℝ) : ℂ))
    (by simp; linarith)
  intro h0
  apply hne
  have hterm : ∀ n : ℕ, LSeries.term (fun n => χC n) ((1 + ε : ℝ) : ℂ) n =
      ((dampedSignWeight (charSign χ) ε n / n : ℝ) : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term, dampedSignWeight, Real.zero_rpow (show -ε ≠ 0 by linarith)]
    · rw [LSeries.term_of_ne_zero hn.ne', dampedSignWeight_div hε]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      rw [show ((n : ℕ) : ℂ) = ((n : ℝ) : ℂ) by norm_cast,
        ← Complex.ofReal_cpow hn0.le]
      simp only [χC, MulChar.ringHomComp_apply, eq_intCast, charSign]
      rw [Real.rpow_neg hn0.le]
      push_cast
      field_simp
  rw [LSeries, tsum_congr hterm, ← Complex.ofReal_tsum]
  unfold charDampedMass at h0
  rw [h0, Complex.ofReal_zero]

omit [NeZero q] in
/-- The character weight's Ramanujan coefficients: `W_χ(e) = (c_χ(e)/e) L_χ`. -/
theorem weightRamanujanCoeff_char (χ : MulChar (ZMod q) ℤ) {ε : ℝ} (e : ℕ) :
    weightRamanujanCoeff (dampedSignWeight (charSign χ) ε) e =
      dampedSignWeight (charSign χ) ε e / e * charDampedMass χ ε := by
  unfold weightRamanujanCoeff charDampedMass
  simp_rw [dampedSignWeight_mul_div (charSign_mul χ) e]
  exact tsum_mul_left

/-- **The twist on moduli:** `W_{c_+}(e) = sign(L_χ) χ(e) W_χ(e)`, so the amplitudes agree. -/
theorem abs_weightRamanujanCoeff_charTwin (χ : MulChar (ZMod q) ℤ) {ε : ℝ} (hε : 0 < ε) (e : ℕ) :
    |weightRamanujanCoeff (charTwinWeight χ ε) e| =
      |weightRamanujanCoeff (dampedSignWeight (charSign χ) ε) e| := by
  have hO := (charUnitMass_pos χ hε).ne'
  have hL : weightRamanujanCoeff (charTwinWeight χ ε) e =
      |charDampedMass χ ε| * (dampedSignWeight (charUnit χ) ε e / e) := by
    unfold weightRamanujanCoeff charTwinWeight
    have hterm : ∀ k : ℕ, |charDampedMass χ ε| / charUnitMass χ ε *
        dampedSignWeight (charUnit χ) ε (e * k) / ((e * k : ℕ) : ℝ) =
        |charDampedMass χ ε| / charUnitMass χ ε * ((dampedSignWeight (charUnit χ) ε e / e) *
          (dampedSignWeight (charUnit χ) ε k / k)) := by
      intro k
      rw [mul_div_assoc, dampedSignWeight_mul_div (charUnit_mul χ) e k]
    simp_rw [hterm]
    rw [tsum_mul_left, tsum_mul_left, ← charUnitMass]
    field_simp
  rw [hL, weightRamanujanCoeff_char, abs_mul, abs_mul, abs_abs,
    mul_comm |dampedSignWeight (charSign χ) ε e / ↑e|]
  congr 1
  have hs : |charSign χ e| ^ 2 = |charSign χ e| := by
    have := charSign_sq_eq χ e
    rw [← sq_abs] at this
    have h0 := abs_nonneg (charSign χ e)
    split_ifs at this
    · have h1 : |charSign χ e| = 1 := by nlinarith
      rw [h1]; norm_num
    · have h1 : |charSign χ e| = 0 := by nlinarith
      rw [h1]; norm_num
  unfold dampedSignWeight charUnit
  rw [abs_div, abs_div, abs_mul, abs_mul, abs_pow, hs]

theorem charTwinWeight_nonneg (χ : MulChar (ZMod q) ℤ) {ε : ℝ} (hε : 0 < ε) (d : ℕ) :
    0 ≤ charTwinWeight χ ε d := by
  unfold charTwinWeight dampedSignWeight
  have := charUnitMass_pos χ hε
  have := charUnit_nonneg χ d
  positivity

theorem hasSum_charTwinWeight_div (χ : MulChar (ZMod q) ℤ) {ε : ℝ} (hε : 0 < ε) :
    HasSum (fun d : ℕ => charTwinWeight χ ε d / d) |charDampedMass χ ε| := by
  have hO := (charUnitMass_pos χ hε).ne'
  have h := (summable_charUnit_weight χ hε).hasSum.mul_left (|charDampedMass χ ε| / charUnitMass χ ε)
  rw [← charUnitMass, div_mul_cancel₀ _ hO] at h
  refine h.congr_fun fun d => ?_
  simp only [charTwinWeight, mul_div_assoc]

/-- The residues `1 + qj ∈ (n, 2n]` carry the drift of the positive twin. -/
theorem charTwin_drift_ge (χ : MulChar (ZMod q) ℤ) {ε : ℝ} (hε : 0 < ε) (hL : charDampedMass χ ε ≠ 0)
    {n : ℕ} (hn : 8 * q ≤ n) :
    |charDampedMass χ ε| / charUnitMass χ ε / (8 * q) * n * (2 * (n : ℝ)) ^ (-ε) ≤
      (n : ℝ) * ∑ d ∈ Ioc n (2 * n), charTwinWeight χ ε d / d := by
  set κ := |charDampedMass χ ε| / charUnitMass χ ε
  have hκ : 0 < κ := div_pos (abs_pos.mpr hL) (charUnitMass_pos χ hε)
  have hq0 : 0 < q := NeZero.pos q
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h2n : (0 : ℝ) < 2 * n := by linarith
  set J := Ico (n / q + 1) (2 * (n / q))
  have hmaps : ∀ j ∈ J, 1 + q * j ∈ Ioc n (2 * n) := by
    intro j hj
    rw [mem_Ico] at hj
    rw [mem_Ioc]
    have h1 := Nat.lt_mul_div_succ n hq0
    have h2 := Nat.mul_div_le n q
    constructor
    · nlinarith
    · have : q * j ≤ q * (2 * (n / q) - 1) := Nat.mul_le_mul_left q (by omega)
      have h3 : q * (2 * (n / q) - 1) + 1 ≤ 2 * n := by
        have : q * (2 * (n / q) - 1) = 2 * (q * (n / q)) - q := by
          rw [Nat.mul_sub, Nat.mul_one]; ring_nf
        omega
      omega
  have hinj : Set.InjOn (fun j => 1 + q * j) J := fun a _ b _ h => by
    simp only at h
    exact Nat.eq_of_mul_eq_mul_left hq0 (by omega)
  have hunit : ∀ j, charUnit χ (1 + q * j) = 1 := fun j => by
    rw [charUnit, show 1 + q * j = q * j + 1 by ring, charSign_mul_period_add, charSign_one]
    norm_num
  have hterm : ∀ j ∈ J, κ * (2 * (n : ℝ)) ^ (-1 - ε) ≤
      charTwinWeight χ ε (1 + q * j) / ((1 + q * j : ℕ) : ℝ) := by
    intro j hj
    have hd := hmaps j hj
    rw [mem_Ioc] at hd
    have hd0 : (0 : ℝ) < ((1 + q * j : ℕ) : ℝ) := by positivity
    have hdle : ((1 + q * j : ℕ) : ℝ) ≤ 2 * n := by exact_mod_cast hd.2
    rw [charTwinWeight, dampedSignWeight, hunit, one_mul, mul_div_assoc,
      show ((1 + q * j : ℕ) : ℝ) ^ (-ε) / ((1 + q * j : ℕ) : ℝ) =
        ((1 + q * j : ℕ) : ℝ) ^ (-1 - ε) by
        rw [show -1 - ε = -ε - 1 by ring, Real.rpow_sub_one hd0.ne']]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hd0 hdle (by linarith)) hκ.le
  have himg : ∑ d ∈ J.image (fun j => 1 + q * j), charTwinWeight χ ε d / (d : ℝ) =
      ∑ j ∈ J, charTwinWeight χ ε (1 + q * j) / ((1 + q * j : ℕ) : ℝ) := sum_image hinj
  have hsub : ∑ j ∈ J, charTwinWeight χ ε (1 + q * j) / ((1 + q * j : ℕ) : ℝ) ≤
      ∑ d ∈ Ioc n (2 * n), charTwinWeight χ ε d / d := by
    rw [← himg]
    refine sum_le_sum_of_subset_of_nonneg ?_ fun d _ _ =>
      div_nonneg (charTwinWeight_nonneg χ hε d) (Nat.cast_nonneg d)
    intro d hd
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hd
    exact hmaps j hj
  have hcard : (n : ℝ) / (2 * q) ≤ J.card := by
    rw [Nat.card_Ico]
    have hdiv : (n : ℝ) / q - 1 < ((n / q : ℕ) : ℝ) := by
      have h := Nat.lt_div_mul_add (a := n) hq0
      have h' : (n : ℝ) < ((n / q : ℕ) : ℝ) * q + q := by exact_mod_cast h
      rw [div_sub_one hqR.ne', div_lt_iff₀ hqR]; linarith
    have hge : 8 ≤ n / q := (Nat.le_div_iff_mul_le hq0).mpr (by linarith)
    have hc : 2 * (n / q) - (n / q + 1) = n / q - 1 := by omega
    rw [hc, Nat.cast_sub (by omega), Nat.cast_one]
    have h8 : (8 : ℝ) ≤ ((n / q : ℕ) : ℝ) := by exact_mod_cast hge
    have : (n : ℝ) / (2 * q) = (n : ℝ) / q / 2 := by field_simp
    rw [this]
    linarith
  have hlow := sum_le_sum hterm
  rw [sum_const, nsmul_eq_mul] at hlow
  have hpow : (2 * (n : ℝ)) ^ (-1 - ε) = (2 * (n : ℝ)) ^ (-ε) / (2 * n) := by
    rw [show -1 - ε = -ε - 1 by ring, Real.rpow_sub_one h2n.ne']
  have hP : 0 ≤ (2 * (n : ℝ)) ^ (-ε) := Real.rpow_nonneg h2n.le _
  have key : (n : ℝ) / (2 * q) * (κ * ((2 * (n : ℝ)) ^ (-ε) / (2 * n))) ≤
      ∑ d ∈ Ioc n (2 * n), charTwinWeight χ ε d / d := by
    rw [← hpow]
    exact (mul_le_mul_of_nonneg_right hcard (by positivity)).trans (hlow.trans hsub)
  have e1 : κ / (8 * q) * (n : ℝ) * (2 * (n : ℝ)) ^ (-ε) =
      (n : ℝ) * ((1 / 2) * ((n : ℝ) / (2 * q) * (κ * ((2 * (n : ℝ)) ^ (-ε) / (2 * n))))) := by
    have := hn0.ne'; have := hqR.ne'
    field_simp
    ring
  rw [e1]
  refine mul_le_mul_of_nonneg_left ?_ hn0.le
  have hk0 : 0 ≤ (n : ℝ) / (2 * q) * (κ * ((2 * (n : ℝ)) ^ (-ε) / (2 * n))) := by positivity
  linarith

/-- **Every real non-principal character gives a parity pair at every `0 < ε ≤ 1/2`.** -/
theorem char_parityPair {χ : MulChar (ZMod q) ℤ} (hχ : χ ≠ 1) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    (∀ e : ℕ, |weightRamanujanCoeff (charTwinWeight χ ε) e| =
        |weightRamanujanCoeff (dampedSignWeight (charSign χ) ε) e|) ∧
    (∀ d : ℕ, 0 ≤ charTwinWeight χ ε d) ∧
    (∃ E : ℝ, ∀ T : ℕ,
        weightPronicEnergy (dampedSignWeight (charSign χ) ε) (charDampedMass χ ε) T ≤ E) ∧
    Tendsto (fun T => weightPronicEnergy (charTwinWeight χ ε) |charDampedMass χ ε| T)
      atTop atTop := by
  have hL := charDampedMass_ne_zero (χ := χ) hε
  refine ⟨abs_weightRamanujanCoeff_charTwin χ hε, charTwinWeight_nonneg χ hε,
    exists_weightPronicEnergy_dampedSign_le (Nat.cast_nonneg q) hε (abs_sum_range_charSign_le hχ), ?_⟩
  exact tendsto_weightPronicEnergy_of_drift (charTwinWeight_nonneg χ hε) (hasSum_charTwinWeight_div χ hε)
    (by have := div_pos (abs_pos.mpr hL) (charUnitMass_pos χ hε)
        have : (0 : ℝ) < 8 * q := by have := NeZero.pos q; positivity
        positivity)
    hε2 (8 * q) fun n hn => charTwin_drift_ge χ hε hL hn

/-! ### The parity barrier -/

/-- The damped class `|c(d)| ≤ K d^{-ε}`. -/
def DampedClass (K ε : ℝ) (c : ℕ → ℝ) : Prop := ∀ d : ℕ, |c d| ≤ K * (d : ℝ) ^ (-ε)

/-- The receiver of `c`, centred at its mean `Σ c(d)/d`, is bounded. -/
def ReceiverBounded (c : ℕ → ℝ) : Prop :=
  ∃ E : ℝ, ∀ T : ℕ, weightPronicEnergy c (∑' d : ℕ, c d / d) T ≤ E

omit [NeZero q] in
theorem weightCenteredPrefix_smul (t : ℝ) (c : ℕ → ℝ) (m : ℝ) (n : ℕ) :
    weightCenteredPrefix (fun d => t * c d) (t * m) n = t * weightCenteredPrefix c m n := by
  simp only [weightCenteredPrefix, ← mul_sum]; ring

omit [NeZero q] in
theorem weightPronicEnergy_smul (t : ℝ) (c : ℕ → ℝ) (m : ℝ) (T : ℕ) :
    weightPronicEnergy (fun d => t * c d) (t * m) T = t ^ 2 * weightPronicEnergy c m T := by
  simp only [weightPronicEnergy, weightCenteredPrefix_smul, mul_pow, mul_div_assoc, ← mul_sum]

omit [NeZero q] in
theorem weightRamanujanCoeff_smul (t : ℝ) (c : ℕ → ℝ) (e : ℕ) :
    weightRamanujanCoeff (fun d => t * c d) e = t * weightRamanujanCoeff c e := by
  simp only [weightRamanujanCoeff, mul_div_assoc, tsum_mul_left]

omit [NeZero q] in
theorem receiverBounded_smul_iff {t : ℝ} (ht : t ≠ 0) (c : ℕ → ℝ) :
    ReceiverBounded (fun d => t * c d) ↔ ReceiverBounded c := by
  have hm : ∑' d : ℕ, t * c d / d = t * ∑' d : ℕ, c d / d := by
    simp only [mul_div_assoc, tsum_mul_left]
  have ht2 : 0 < t ^ 2 := lt_of_le_of_ne (sq_nonneg t) (Ne.symm (pow_ne_zero 2 ht))
  unfold ReceiverBounded
  simp only [hm, weightPronicEnergy_smul]
  constructor
  · rintro ⟨E, hE⟩
    exact ⟨E / t ^ 2, fun T => by rw [le_div_iff₀ ht2, mul_comm]; exact hE T⟩
  · rintro ⟨E, hE⟩
    exact ⟨t ^ 2 * E, fun T => mul_le_mul_of_nonneg_left (hE T) ht2.le⟩

omit [NeZero q] in
/-- **The parity barrier.** For `0 < ε ≤ 1/2` and every `K > 0`, boundedness of the receiver is not
a function of the Ramanujan amplitudes on the class `|c(d)| ≤ K d^{-ε}`: the character pair modulo
four, rescaled into the class, has equal amplitudes and opposite receivers. -/
theorem parity_barrier {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ¬ ∃ Φ : (ℕ → ℝ) → Prop, ∀ c : ℕ → ℝ, DampedClass K ε c →
      (ReceiverBounded c ↔ Φ (fun e => |weightRamanujanCoeff c e|)) := by
  rintro ⟨Φ, hΦ⟩
  obtain ⟨-, hA, -, ⟨E, hE⟩, hdiv⟩ := chiFour_parityPair hε hε2
  set κ := chiFourDampedMass ε / oddDampedMass ε with hκdef
  have hκ : 0 < κ := div_pos (chiFourDampedMass_pos hε) (oddDampedMass_pos hε)
  set t := K / (1 + κ) with htdef
  have ht : 0 < t := div_pos hK (by linarith)
  have htK : t ≤ K := div_le_self hK.le (by linarith)
  have htκ : t * κ ≤ K := by
    rw [htdef, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
  have hrpow : ∀ d : ℕ, 0 ≤ (d : ℝ) ^ (-ε) := fun d => Real.rpow_nonneg (Nat.cast_nonneg d) _
  have hclassχ : DampedClass K ε (fun d => t * dampedSignWeight chiFour ε d) := fun d => by
    have h1 : |chiFour d| ≤ 1 := by rw [chiFour_eq]; split_ifs <;> norm_num
    dsimp only
    rw [dampedSignWeight, abs_mul, abs_mul, abs_of_pos ht, abs_of_nonneg (hrpow d)]
    calc t * (|chiFour d| * (d : ℝ) ^ (-ε)) ≤ K * (1 * (d : ℝ) ^ (-ε)) :=
          mul_le_mul htK (mul_le_mul_of_nonneg_right h1 (hrpow d)) (by positivity) hK.le
      _ = _ := by ring
  have hclassP : DampedClass K ε (fun d => t * oddDampedTwinWeight ε d) := fun d => by
    have h1 : oddIndicator d ≤ 1 := by unfold oddIndicator; split_ifs <;> norm_num
    have h0 : 0 ≤ oddIndicator d := by unfold oddIndicator; split_ifs <;> norm_num
    dsimp only
    rw [abs_mul, abs_of_pos ht, abs_of_nonneg (oddDampedTwinWeight_nonneg hε d),
      oddDampedTwinWeight, dampedSignWeight, ← hκdef]
    calc t * (κ * (oddIndicator d * (d : ℝ) ^ (-ε))) =
          t * κ * (oddIndicator d * (d : ℝ) ^ (-ε)) := by ring
      _ ≤ K * (1 * (d : ℝ) ^ (-ε)) :=
          mul_le_mul htκ (mul_le_mul_of_nonneg_right h1 (hrpow d)) (by positivity) hK.le
      _ = _ := by ring
  have hamp : (fun e => |weightRamanujanCoeff (fun d => t * oddDampedTwinWeight ε d) e|) =
      fun e => |weightRamanujanCoeff (fun d => t * dampedSignWeight chiFour ε d) e| := by
    funext e
    rw [weightRamanujanCoeff_smul, weightRamanujanCoeff_smul, abs_mul, abs_mul, hA e]
  have hboundχ : ReceiverBounded (fun d => t * dampedSignWeight chiFour ε d) :=
    (receiverBounded_smul_iff ht.ne' _).mpr ⟨E, hE⟩
  have hunbounded : ¬ ReceiverBounded (fun d => t * oddDampedTwinWeight ε d) := by
    rw [receiverBounded_smul_iff ht.ne']
    rintro ⟨E', hE'⟩
    rw [(hasSum_oddDampedTwinWeight_div hε).tsum_eq] at hE'
    obtain ⟨T, hT⟩ := (hdiv.eventually_gt_atTop E').exists
    exact absurd (hE' T) (not_le.mpr hT)
  have hP := hΦ _ hclassP
  rw [hamp, ← hΦ _ hclassχ] at hP
  exact hunbounded (hP.mpr hboundχ)

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
