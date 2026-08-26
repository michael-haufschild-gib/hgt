import GaloisForLFunctions.RHTower.Sieve.SelbergEulerCorrectionCoefficient

open ArithmeticFunction Finset
open scoped BigOperators ArithmeticFunction.Moebius

/-!
# Mass of the pushed Barban--Vehov Euler correction

The squarefree-support correction is pushed along `(r,u,v) ↦ (r*u,r*v)`.  Absolute
summability survives this many-to-one regrouping, and its signed mass remains exactly one.
-/

namespace RHTower.Sieve

noncomputable section

/-- Absolutely convergent pushforward along arbitrary set-theoretic fibres. -/
def summableFiberPushforward {α β : Type*} (f : α → β) (w : α → ℝ) (y : β) : ℝ :=
  ∑' x : {x : α // f x = y}, w x.1

theorem summable_summableFiberPushforward {α β : Type*} (f : α → β) (w : α → ℝ)
    (hw : Summable w) : Summable (summableFiberPushforward f w) := by
  let e := Equiv.sigmaFiberEquiv f
  have hsigma : Summable (fun z : (y : β) × {x : α // f x = y} => w (e z)) :=
    e.summable_iff.mpr hw
  have hsigmaNorm : Summable (fun z : (y : β) × {x : α // f x = y} =>
      ‖w (e z)‖) := hsigma.norm
  have hmajor : Summable (fun y : β => ∑' x : {x : α // f x = y}, ‖w x.1‖) := by
    have hsplit := (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mp hsigmaNorm
    simpa only [e, Equiv.sigmaFiberEquiv_apply] using hsplit.2
  rw [← summable_norm_iff]
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun y => ?_) hmajor
  exact norm_tsum_le_tsum_norm ((hw.subtype (fun x => f x = y)).norm)

theorem tsum_summableFiberPushforward {α β : Type*} (f : α → β) (w : α → ℝ)
    (hw : Summable w) :
    (∑' y : β, summableFiberPushforward f w y) = ∑' x : α, w x := by
  let e := Equiv.sigmaFiberEquiv f
  have hsigma : Summable (fun z : (y : β) × {x : α // f x = y} => w (e z)) :=
    e.summable_iff.mpr hw
  calc
    (∑' y : β, summableFiberPushforward f w y) =
        ∑' y : β, ∑' x : {x : α // f x = y}, w x.1 := rfl
    _ = ∑' z : (y : β) × {x : α // f x = y}, w (e z) := by
      rw [hsigma.tsum_sigma]
      rfl
    _ = ∑' x : α, w x := e.tsum_eq w

def selbergCorrectionIndex (x : ℕ × (ℕ × ℕ)) : ℕ × ℕ :=
  (x.1 * x.2.1, x.1 * x.2.2)

def selbergCorrectionTerm (x : ℕ × (ℕ × ℕ)) : ℝ :=
  selbergCorrectionWeight x.1 x.2.1 x.2.2

theorem localizedReciprocalMoebiusAmplitude_zero {r : ℕ} (_hr : 0 < r) :
    localizedReciprocalMoebiusAmplitude r 0 = 0 := by
  classical
  simp [localizedReciprocalMoebiusAmplitude]

theorem selbergCorrectionTerm_eq_zero_of_index_fst_zero
    {x : ℕ × (ℕ × ℕ)} (h : (selbergCorrectionIndex x).1 = 0) :
    selbergCorrectionTerm x = 0 := by
  change x.1 * x.2.1 = 0 at h
  rcases Nat.mul_eq_zero.mp h with hr | hu
  · simp [selbergCorrectionTerm, hr, selbergCorrectionWeight_zero]
  · rcases eq_or_ne x.1 0 with hr | hr
    · simp [selbergCorrectionTerm, hr, selbergCorrectionWeight_zero]
    · rw [selbergCorrectionTerm, selbergCorrectionWeight, hu,
        localizedReciprocalMoebiusAmplitude_zero (Nat.pos_of_ne_zero hr)]
      ring

theorem selbergCorrectionTerm_eq_zero_of_index_snd_zero
    {x : ℕ × (ℕ × ℕ)} (h : (selbergCorrectionIndex x).2 = 0) :
    selbergCorrectionTerm x = 0 := by
  change x.1 * x.2.2 = 0 at h
  rcases Nat.mul_eq_zero.mp h with hr | hv
  · simp [selbergCorrectionTerm, hr, selbergCorrectionWeight_zero]
  · rcases eq_or_ne x.1 0 with hr | hr
    · simp [selbergCorrectionTerm, hr, selbergCorrectionWeight_zero]
    · rw [selbergCorrectionTerm, selbergCorrectionWeight, hv,
        localizedReciprocalMoebiusAmplitude_zero (Nat.pos_of_ne_zero hr)]
      ring

private def selbergCorrectionFiberEquiv {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    {x : ℕ × (ℕ × ℕ) // selbergCorrectionIndex x = (m, n)} ≃
      {r // r ∈ (Nat.gcd m n).divisors} where
  toFun x := by
    have hmEq : x.1.1 * x.1.2.1 = m := congrArg Prod.fst x.2
    have hnEq : x.1.1 * x.1.2.2 = n := congrArg Prod.snd x.2
    refine ⟨x.1.1, Nat.mem_divisors.mpr ⟨Nat.dvd_gcd ⟨x.1.2.1, hmEq.symm⟩
      ⟨x.1.2.2, hnEq.symm⟩, (Nat.gcd_pos_of_pos_left n hm).ne'⟩⟩
  invFun r := by
    have hrm : r.1 ∣ m := dvd_trans (Nat.dvd_of_mem_divisors r.2)
      (Nat.gcd_dvd_left m n)
    have hrn : r.1 ∣ n := dvd_trans (Nat.dvd_of_mem_divisors r.2)
      (Nat.gcd_dvd_right m n)
    refine ⟨(r.1, (m / r.1, n / r.1)), ?_⟩
    apply Prod.ext
    · exact Nat.mul_div_cancel' hrm
    · exact Nat.mul_div_cancel' hrn
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · have hmEq : x.1.1 * x.1.2.1 = m := congrArg Prod.fst x.2
        have hrpos : 0 < x.1.1 := by
          by_contra hr
          have : x.1.1 = 0 := by omega
          rw [this, zero_mul] at hmEq
          omega
        change m / x.1.1 = x.1.2.1
        apply Nat.div_eq_of_eq_mul_left hrpos
        calc
          m = x.1.1 * x.1.2.1 := hmEq.symm
          _ = x.1.2.1 * x.1.1 := Nat.mul_comm _ _
      · have hnEq : x.1.1 * x.1.2.2 = n := congrArg Prod.snd x.2
        have hrpos : 0 < x.1.1 := by
          by_contra hr
          have : x.1.1 = 0 := by omega
          rw [this, zero_mul] at hnEq
          omega
        change n / x.1.1 = x.1.2.2
        apply Nat.div_eq_of_eq_mul_left hrpos
        calc
          n = x.1.1 * x.1.2.2 := hnEq.symm
          _ = x.1.2.2 * x.1.1 := Nat.mul_comm _ _
  right_inv r := by
    apply Subtype.ext
    rfl

/-- The finite divisor definition of the correction coefficient is exactly the fibrewise
pushforward of the three-variable weight. -/
theorem selbergEulerCorrectionCoeff_eq_tsum_fiber (m n : ℕ) :
    selbergEulerCorrectionCoeff m n =
      ∑' x : {x : ℕ × (ℕ × ℕ) // selbergCorrectionIndex x = (m, n)},
        selbergCorrectionTerm x.1 := by
  by_cases hm : m = 0
  · subst m
    rw [selbergEulerCorrectionCoeff]
    simp only [true_or, if_true]
    rw [show (fun x : {x : ℕ × (ℕ × ℕ) // selbergCorrectionIndex x = (0, n)} =>
        selbergCorrectionTerm x.1) = fun _ => 0 by
      funext x
      exact selbergCorrectionTerm_eq_zero_of_index_fst_zero
        (by simpa using congrArg Prod.fst x.2)]
    exact tsum_zero.symm
  by_cases hn : n = 0
  · subst n
    rw [selbergEulerCorrectionCoeff]
    simp only [or_true, if_true]
    rw [show (fun x : {x : ℕ × (ℕ × ℕ) // selbergCorrectionIndex x = (m, 0)} =>
        selbergCorrectionTerm x.1) = fun _ => 0 by
      funext x
      exact selbergCorrectionTerm_eq_zero_of_index_snd_zero
        (by simpa using congrArg Prod.snd x.2)]
    exact tsum_zero.symm
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let e := selbergCorrectionFiberEquiv hmpos hnpos
    rw [selbergEulerCorrectionCoeff, if_neg (not_or_intro hm hn)]
    change (∑ r : {r // r ∈ (Nat.gcd m n).divisors},
        selbergCorrectionTerm (r.1, (m / r.1, n / r.1))) = _
    have he := e.symm.tsum_eq (fun x => selbergCorrectionTerm x.1)
    rw [tsum_fintype] at he
    calc
      (∑ r : {r // r ∈ (Nat.gcd m n).divisors},
          selbergCorrectionTerm (r.1, (m / r.1, n / r.1))) =
          ∑ r : {r // r ∈ (Nat.gcd m n).divisors},
            selbergCorrectionTerm (e.symm r).1 := by
        apply Fintype.sum_congr
        intro r
        rfl
      _ = ∑' x : {x : ℕ × (ℕ × ℕ) // selbergCorrectionIndex x = (m, n)},
          selbergCorrectionTerm x.1 := he

private theorem summable_selbergCorrectionTerm :
    Summable selbergCorrectionTerm := by
  change Summable (fun x : ℕ × (ℕ × ℕ) =>
    selbergCorrectionWeight x.1 x.2.1 x.2.2)
  exact summable_selbergCorrectionWeight

/-- Absolute summability survives the many-to-one coefficient pushforward. -/
theorem summable_selbergEulerCorrectionCoeff :
    Summable (fun mn : ℕ × ℕ => selbergEulerCorrectionCoeff mn.1 mn.2) := by
  have hpush := summable_summableFiberPushforward selbergCorrectionIndex
    selbergCorrectionTerm summable_selbergCorrectionTerm
  apply hpush.congr
  intro mn
  exact (selbergEulerCorrectionCoeff_eq_tsum_fiber mn.1 mn.2).symm

/-- Total signed mass of the pushed bivariate correction remains exactly one. -/
theorem tsum_selbergEulerCorrectionCoeff :
    (∑' mn : ℕ × ℕ, selbergEulerCorrectionCoeff mn.1 mn.2) = 1 := by
  calc
    (∑' mn : ℕ × ℕ, selbergEulerCorrectionCoeff mn.1 mn.2) =
        ∑' mn : ℕ × ℕ, summableFiberPushforward selbergCorrectionIndex
          selbergCorrectionTerm mn := by
      apply tsum_congr
      intro mn
      exact selbergEulerCorrectionCoeff_eq_tsum_fiber mn.1 mn.2
    _ = ∑' x : ℕ × (ℕ × ℕ), selbergCorrectionTerm x :=
      tsum_summableFiberPushforward selbergCorrectionIndex selbergCorrectionTerm
        summable_selbergCorrectionTerm
    _ = 1 := by
      change (∑' x : ℕ × (ℕ × ℕ),
        selbergCorrectionWeight x.1 x.2.1 x.2.2) = 1
      exact tsum_selbergCorrectionWeight

end

end RHTower.Sieve
