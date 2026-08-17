import GaloisForLFunctions.HTGeometry.ExponentialSumAsymptotics

/-!
# Sign changes of a coefficient sequence, and peeling the lowest exponent

Two pieces of bookkeeping for the Laguerre induction on exponential sums.

* `signChanges` counts the sign alternations of a coefficient sequence, read in increasing order of
  exponent.  It satisfies the recursion that peels off the first coefficient.
* Once the exponents are shifted so that the lowest one is `0`, differentiating **removes** that
  term — its coefficient gets multiplied by the exponent `0` — and multiplies each surviving
  coefficient by a strictly positive number, hence leaves the sign pattern of the tail untouched.

Together: the derivative of a normalised exponential sum is an exponential sum with one fewer term
whose sign-change count is exactly that of the tail of the original coefficient sequence.
-/

namespace GaloisForLFunctions.HTGeometry

/-! ## Sign changes -/

/-- Sign alternations of a list of reals: adjacent pairs of strictly opposite sign. -/
noncomputable def signChangesList : List ℝ → ℕ
  | [] => 0
  | [_] => 0
  | x :: y :: l => (if x * y < 0 then 1 else 0) + signChangesList (y :: l)

/-- Sign alternations of a coefficient sequence indexed by `Fin m`. -/
noncomputable def signChanges {m : ℕ} (c : Fin m → ℝ) : ℕ := signChangesList (List.ofFn c)

@[simp] theorem signChanges_zero (c : Fin 0 → ℝ) : signChanges c = 0 := by
  simp [signChanges, signChangesList]

@[simp] theorem signChanges_one (c : Fin 1 → ℝ) : signChanges c = 0 := by
  simp [signChanges, signChangesList]

/-- Peeling the first coefficient. -/
theorem signChanges_succ {m : ℕ} (c : Fin (m + 2) → ℝ) :
    signChanges c =
      (if c 0 * c 1 < 0 then 1 else 0) + signChanges (fun i : Fin (m + 1) => c i.succ) := by
  rw [signChanges, signChanges]
  simp only [List.ofFn_succ]
  rw [signChangesList]
  rfl

/-- Two reals of the same strict sign are simultaneously negative. -/
theorem neg_iff_neg_of_mul_pos {p q : ℝ} (h : 0 < p * q) : p < 0 ↔ q < 0 := by
  constructor
  · intro hp; nlinarith
  · intro hq; nlinarith

/-- Rescaling every coefficient by a factor of its own sign leaves the sign changes unchanged. -/
theorem signChangesList_congr_sign {l l' : List ℝ}
    (h : List.Forall₂ (fun x y => 0 < x * y) l l') :
    signChangesList l = signChangesList l' := by
  induction h with
  | nil => rfl
  | @cons x x' u u' hx hu ih =>
    cases hu with
    | nil => rfl
    | @cons y y' v v' hy hv =>
      have hprod : 0 < (x * y) * (x' * y') := by nlinarith [mul_pos hx hy]
      have hterm : (if x * y < 0 then 1 else 0) = (if x' * y' < 0 then 1 else 0) :=
        if_congr (neg_iff_neg_of_mul_pos hprod) rfl rfl
      rw [signChangesList, signChangesList, hterm]
      exact congrArg _ ih

theorem forall₂_ofFn_mul :
    ∀ (m : ℕ) (c d : Fin m → ℝ), (∀ i, c i ≠ 0) → (∀ i, 0 < d i) →
      List.Forall₂ (fun x y => 0 < x * y) (List.ofFn fun i => c i * d i) (List.ofFn c) := by
  intro m
  induction m with
  | zero => intro c d _ _; simp
  | succ n ih =>
    intro c d hc hd
    simp only [List.ofFn_succ]
    refine List.Forall₂.cons ?_
      (ih (fun i => c i.succ) (fun i => d i.succ) (fun i => hc _) (fun i => hd _))
    have hrw : c 0 * d 0 * c 0 = d 0 * (c 0 * c 0) := by ring
    rw [hrw]
    exact mul_pos (hd 0) (mul_self_pos.mpr (hc 0))

/-- **Positive rescaling preserves the sign pattern.** -/
theorem signChanges_mul_pos {m : ℕ} (c d : Fin m → ℝ) (hc : ∀ i, c i ≠ 0) (hd : ∀ i, 0 < d i) :
    signChanges (fun i => c i * d i) = signChanges c :=
  signChangesList_congr_sign (forall₂_ofFn_mul m c d hc hd)

/-! ## Peeling the lowest exponent -/

theorem expSum_succ {m : ℕ} (c a : Fin (m + 1) → ℝ) (t : ℝ) :
    expSum c a t =
      c 0 * Real.exp (a 0 * t) + expSum (fun i => c i.succ) (fun i => a i.succ) t := by
  rw [expSum, expSum, Fin.sum_univ_succ]

/-- With the lowest exponent normalised to `0`, differentiating deletes the lowest term. -/
theorem deriv_expSum_of_head_zero {m : ℕ} (c a : Fin (m + 1) → ℝ) (h : a 0 = 0) :
    deriv (expSum c a) =
      expSum (fun i : Fin m => c i.succ * a i.succ) (fun i : Fin m => a i.succ) := by
  rw [deriv_expSum]
  funext t
  rw [expSum_succ]
  simp [h]

/-- **The sign-change count of the derivative.**  After normalising the lowest exponent to `0`, the
derivative is an exponential sum with one fewer term, and its sign changes are exactly those of the
tail of the original coefficient sequence. -/
theorem signChanges_deriv_coeff {m : ℕ} (c a : Fin (m + 1) → ℝ)
    (hc : ∀ i, c i ≠ 0) (ha : ∀ i : Fin m, 0 < a i.succ) :
    signChanges (fun i : Fin m => c i.succ * a i.succ)
      = signChanges (fun i : Fin m => c i.succ) :=
  signChanges_mul_pos _ _ (fun i => hc _) ha

end GaloisForLFunctions.HTGeometry
