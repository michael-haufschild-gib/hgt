import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TheShortMoebiusMonomialsPayExactlyHalf

/-!
# The Gauss pairings are priced above the sign

A Möbius-signed Gauss pairing `P` over the characters of `𝔽_p` (FCT `MoebiusGaussPairing`) prices a
completed factor of order `m` at `(½ − 1/m)k` and a row twist at `k/2 − 1`, `k` the period
(`pairingC`). Its tuple `L` (completed factors and rows) is a Möbius-signed Gauss monomial.

* **Factor by factor** (`logb_norm_gaussSum_pow_le`): every conjugate `x^t` of a character of order
  `m ≥ 2` has `log_p ‖g(x^t)‖ ≤ −1/m` (`exists_norm_gaussSum_pow_orderOf`), so its defect is at most
  `½ − 1/m`; a row of order `m' ∣ k` has defect at most `½ − 1/k`.
* **The pairing dominates the sign** (`stickelbergerPrice_le_pairingC`): the defect of a monomial is
  the sum of the defects of its factors, so `k·defect(L^t) ≤ c` at every conjugate, and `c` is at
  least the Stickelberger price of `L`.
* **An arithmetic barrier** (`half_mul_period_le_pairingC`): `c ≥ k/2` for every Möbius-signed
  Gauss pairing over `𝔽_p`, so its centre exceeds `½`. The barrier `⅗` of FCT is this bound at the
  period `6`, where the pair of the frame `(3, 6)` is priced exactly at `k/2 = 3`
  (`stickelbergerPrice_eq_half_mul`).
-/

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.Stickelberger

open GaloisForLFunctions.FamilyContinuationTheory (IsMoebiusSignedTuple MoebiusGaussPairing)

variable {p : ℕ} [hp : Fact p.Prime]

attribute [local instance] neZero_p neZero_p_sub_one

/-- The defect of a monomial is the sum of the defects of its factors. -/
theorem stickelbergerDefect_eq_sum {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p)
    (L : List (MulChar (ZMod p) (PadicAlgCl p))) :
    stickelbergerDefect p hζ L =
      (L.map fun x => 1 / 2 + Real.logb p ‖gaussSum x (AddChar.zmodChar p hζ.pow_eq_one)‖).sum := by
  rw [stickelbergerDefect, (logb_norm_prod hζ L).2]
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    push_cast
    linarith

/-- A character of order `m ≥ 2` has `log_p ‖g(x)‖ ≤ −1/m`. -/
theorem logb_norm_gaussSum_le {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p)
    (x : MulChar (ZMod p) (PadicAlgCl p)) (hx : 2 ≤ orderOf x) :
    Real.logb p ‖gaussSum x (AddChar.zmodChar p hζ.pow_eq_one)‖ ≤ -(1 / (orderOf x : ℝ)) := by
  obtain ⟨v, hv1, -, -, hv⟩ := exists_norm_gaussSum_pow_orderOf p hζ x hx
  have h := congrArg (Real.logb p) hv
  rw [Real.logb_pow, Real.logb_pow, Real.logb_inv,
    Real.logb_self_eq_one (by exact_mod_cast hp.out.one_lt)] at h
  have hm : (0 : ℝ) < orderOf x := by have : 0 < orderOf x := by omega
                                     exact_mod_cast this
  have hv1' : (1 : ℝ) ≤ v := by exact_mod_cast hv1
  rw [le_neg, ← neg_div' ] at *
  rw [div_le_iff₀ hm]
  nlinarith

/-- Every conjugate of a character of order `m ≥ 2` has `log_p ‖g(x^t)‖ ≤ −1/m`. -/
theorem logb_norm_gaussSum_pow_le {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p)
    (x : MulChar (ZMod p) (PadicAlgCl p)) (hx : 2 ≤ orderOf x) (t : (ZMod (p - 1))ˣ) :
    Real.logb p ‖gaussSum (x ^ (t : ZMod (p - 1)).val) (AddChar.zmodChar p hζ.pow_eq_one)‖ ≤
      -(1 / (orderOf x : ℝ)) := by
  have hcop : (orderOf x).Coprime (t : ZMod (p - 1)).val :=
    (Nat.Coprime.coprime_dvd_right (orderOf_dvd_sub_one p x) (ZMod.val_coe_unit_coprime t)).symm
  have hord := Nat.Coprime.orderOf_pow hcop
  have h := logb_norm_gaussSum_le hζ (x ^ (t : ZMod (p - 1)).val) (by rw [hord]; exact hx)
  rwa [hord] at h

/-- **The pairing dominates the sign at every conjugate.** -/
theorem period_mul_stickelbergerDefect_conjList_le_pairingC {ζ : PadicAlgCl p}
    (hζ : IsPrimitiveRoot ζ p) (P : MoebiusGaussPairing (MulChar (ZMod p) (PadicAlgCl p)))
    (t : (ZMod (p - 1))ˣ) :
    (P.period : ℝ) * stickelbergerDefect p hζ (conjList p t (P.compChars ++ P.rowChars)) ≤
      P.pairingC := by
  have hk : (0 : ℝ) < P.period := by exact_mod_cast P.period_pos
  have hdiv : ∀ x ∈ P.compChars ++ P.rowChars, orderOf x ∣ P.period := fun x hx =>
    (FamilyContinuationTheory.orderOf_dvd_tupleOrderLcm hx).trans P.lcm_dvd_period
  have h2 : ∀ x ∈ P.compChars ++ P.rowChars, 2 ≤ orderOf x := P.moebius.two_le_order
  rw [stickelbergerDefect_eq_sum, conjList, List.map_map, List.map_append, List.sum_append,
    mul_add, FamilyContinuationTheory.MoebiusGaussPairing.pairingC]
  refine add_le_add ?_ ?_
  · rw [← List.sum_map_mul_left]
    refine List.sum_le_sum fun x hx => ?_
    have hx2 := h2 x (List.mem_append_left _ hx)
    have hl := logb_norm_gaussSum_pow_le hζ x hx2 t
    simp only [Function.comp]
    nlinarith
  · have hrow : ∀ x ∈ P.rowChars, (P.period : ℝ) * (1 / 2 + Real.logb p
        ‖gaussSum (x ^ (t : ZMod (p - 1)).val) (AddChar.zmodChar p hζ.pow_eq_one)‖) ≤
        (P.period : ℝ) / 2 - 1 := by
      intro x hx
      have hx2 := h2 x (List.mem_append_right _ hx)
      have hl := logb_norm_gaussSum_pow_le hζ x hx2 t
      have hm : (orderOf x : ℝ) ≤ P.period := by
        exact_mod_cast Nat.le_of_dvd P.period_pos (hdiv x (List.mem_append_right _ hx))
      have hm0 : (0 : ℝ) < orderOf x := by
        have : 0 < orderOf x := by omega
        exact_mod_cast this
      have h1 : (P.period : ℝ) * (1 / (orderOf x : ℝ)) ≥ 1 := by
        rw [mul_one_div, ge_iff_le, le_div_iff₀ hm0, one_mul]
        exact hm
      nlinarith
    rw [← List.sum_map_mul_left]
    calc ((P.rowChars.map fun x => (P.period : ℝ) * ((fun x => 1 / 2 + Real.logb p
          ‖gaussSum x (AddChar.zmodChar p hζ.pow_eq_one)‖) ∘ fun χ => χ ^ (t : ZMod (p - 1)).val) x)).sum
        ≤ (P.rowChars.map fun _ => (P.period : ℝ) / 2 - 1).sum :=
          List.sum_le_sum fun x hx => by simpa [Function.comp] using hrow x hx
      _ = (P.rowChars.length : ℝ) * ((P.period : ℝ) / 2 - 1) := by
          rw [List.map_const', List.sum_replicate, nsmul_eq_mul]

/-- **The Gauss pairings are priced above the sign:** `c` is at least the Stickelberger price of
the tuple of the pairing. -/
theorem stickelbergerPrice_le_pairingC {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p)
    (P : MoebiusGaussPairing (MulChar (ZMod p) (PadicAlgCl p))) :
    stickelbergerPrice hζ P.period (P.compChars ++ P.rowChars) ≤ P.pairingC := by
  have hk : (0 : ℝ) < P.period := by exact_mod_cast P.period_pos
  rw [stickelbergerPrice, ← le_div_iff₀' hk]
  refine Finset.sup'_le _ _ fun t _ => ?_
  rw [le_div_iff₀' hk]
  exact period_mul_stickelbergerDefect_conjList_le_pairingC hζ P t

/-- **An arithmetic barrier for the Gauss pairings:** `c ≥ k/2`. -/
theorem half_mul_period_le_pairingC {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p)
    (P : MoebiusGaussPairing (MulChar (ZMod p) (PadicAlgCl p))) :
    (P.period : ℝ) / 2 ≤ P.pairingC :=
  (half_mul_le_stickelbergerPrice hζ (by positivity) P.moebius).trans
    (stickelbergerPrice_le_pairingC hζ P)

#print axioms stickelbergerPrice_le_pairingC
#print axioms half_mul_period_le_pairingC

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.Stickelberger
