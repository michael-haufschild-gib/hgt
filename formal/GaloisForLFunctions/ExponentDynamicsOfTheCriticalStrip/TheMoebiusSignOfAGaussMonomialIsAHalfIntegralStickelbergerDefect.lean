import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TheTensorPowersOfAGaussSumReachZetaAtTheRateOfItsOrder

/-!
# The Möbius sign of a Gauss monomial is a half-integral Stickelberger defect

A list `L` of characters of `𝔽_p` with `(∏ L)² = 1` gives the Gauss monomial `G = ∏_{χ ∈ L} g(χ)`
of archimedean weight `r/2`, `r = |L|`, and `p`-adic content `C = −log_p ‖G‖` in an algebraic
closure `K` of `ℚ_p`. Its **Stickelberger defect** `r/2 − C` (`stickelbergerDefect`) is the part of
the weight that does not reach `ζ` through powers of `p`.

* **The defect** (`stickelbergerDefect_eq`): with `χ = ω^{n_χ}` and Stickelberger's valuation,
  `C = Σ_χ (p − 1 − n_χ)/(p − 1)`, so the defect is `S/(p − 1) − r/2` with `S = Σ_χ n_χ`, and
  `∏ L = ω^S`.
* **Parity** (`isMoebiusSignedTuple_iff_defect`): for nontrivial characters with `(∏ L)² = 1`, the
  Möbius parity law of the Gauss pairings, `(∏ L = 1, r odd)` or `(∏ L quadratic, r even)`, holds iff
  the defect is half-integral. Write `2S = (p − 1) q`; then `∏ L = 1` iff `q` is even and the defect
  is `(q − r)/2`.
* **No pure Möbius monomial** (`half_le_abs_stickelbergerDefect`): a Möbius-signed Gauss monomial has
  defect at least `½` in absolute value; it is pure (`G = unit · p^{r/2}`) at no place above `p`.
  Applied to the conjugate lists `(χ^t)` this holds at every place.
-/

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.Stickelberger

open GaloisForLFunctions.FamilyContinuationTheory (IsMoebiusSignedTuple)

variable (p : ℕ) [hp : Fact p.Prime]

attribute [local instance] neZero_p

/-- The Teichmüller exponent: `χ = ω^{teichExp χ}` with `1 ≤ teichExp χ ≤ p − 1`. -/
noncomputable def teichExp (χ : MulChar (ZMod p) (PadicAlgCl p)) : ℕ :=
  (exists_eq_teichCharK_pow p χ).choose

theorem teichExp_spec (χ : MulChar (ZMod p) (PadicAlgCl p)) :
    1 ≤ teichExp p χ ∧ teichExp p χ ≤ p - 1 ∧ χ = teichCharK p ^ teichExp p χ :=
  (exists_eq_teichCharK_pow p χ).choose_spec

variable {p}

theorem norm_gaussSum_pow_sub_one {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p)
    (χ : MulChar (ZMod p) (PadicAlgCl p)) :
    ‖gaussSum χ (AddChar.zmodChar p hζ.pow_eq_one)‖ ^ (p - 1) =
      ((p : ℝ)⁻¹) ^ (p - 1 - teichExp p χ) := by
  obtain ⟨h1, h2, h3⟩ := teichExp_spec p χ
  have hX := norm_gaussSum_teichCharK_pow_pow p hζ (by omega : teichExp p χ ≠ 0) h2
  rwa [← h3] at hX

theorem norm_gaussSum_ne_zero {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p)
    (χ : MulChar (ZMod p) (PadicAlgCl p)) : ‖gaussSum χ (AddChar.zmodChar p hζ.pow_eq_one)‖ ≠ 0 := by
  intro h
  have hX := norm_gaussSum_pow_sub_one hζ χ
  rw [h, zero_pow (by have := hp.out.two_le; omega)] at hX
  exact pow_ne_zero _ (inv_ne_zero (Nat.cast_ne_zero.2 hp.out.ne_zero)) hX.symm

/-- **Stickelberger's valuation as a logarithm:** `log_p ‖g(ω^n)‖ = −(p − 1 − n)/(p − 1)`. -/
theorem logb_norm_gaussSum {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p)
    (χ : MulChar (ZMod p) (PadicAlgCl p)) :
    Real.logb p ‖gaussSum χ (AddChar.zmodChar p hζ.pow_eq_one)‖ =
      -(((p - 1 - teichExp p χ : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ)) := by
  have h := congrArg (Real.logb p) (norm_gaussSum_pow_sub_one hζ χ)
  rw [Real.logb_pow, Real.logb_pow, Real.logb_inv,
    Real.logb_self_eq_one (by exact_mod_cast hp.out.one_lt)] at h
  have hN : ((p - 1 : ℕ) : ℝ) ≠ 0 := by
    have := hp.out.two_le
    exact Nat.cast_ne_zero.2 (by omega)
  rw [neg_div', eq_div_iff hN, mul_comm]
  linarith

theorem logb_norm_prod {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p)
    (L : List (MulChar (ZMod p) (PadicAlgCl p))) :
    ‖(L.map fun χ => gaussSum χ (AddChar.zmodChar p hζ.pow_eq_one)).prod‖ ≠ 0 ∧
      Real.logb p ‖(L.map fun χ => gaussSum χ (AddChar.zmodChar p hζ.pow_eq_one)).prod‖ =
        (L.map fun χ => Real.logb p ‖gaussSum χ (AddChar.zmodChar p hζ.pow_eq_one)‖).sum := by
  induction L with
  | nil => simp
  | cons χ L ih =>
    rw [List.map_cons, List.prod_cons, norm_mul, List.map_cons, List.sum_cons]
    exact ⟨mul_ne_zero (norm_gaussSum_ne_zero hζ χ) ih.1,
      by rw [Real.logb_mul (norm_gaussSum_ne_zero hζ χ) ih.1, ih.2]⟩

theorem prod_eq_teichCharK_pow (L : List (MulChar (ZMod p) (PadicAlgCl p))) :
    L.prod = teichCharK p ^ (L.map (teichExp p)).sum := by
  induction L with
  | nil => simp
  | cons χ L ih =>
    rw [List.prod_cons, ih, List.map_cons, List.sum_cons, pow_add, ← (teichExp_spec p χ).2.2]

theorem sum_logb_eq (L : List (MulChar (ZMod p) (PadicAlgCl p))) :
    (L.map fun χ => -(((p - 1 - teichExp p χ : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ))).sum =
      ((L.map (teichExp p)).sum : ℝ) / ((p - 1 : ℕ) : ℝ) - L.length := by
  have hN : ((p - 1 : ℕ) : ℝ) ≠ 0 := by
    have := hp.out.two_le
    exact Nat.cast_ne_zero.2 (by omega)
  induction L with
  | nil => simp
  | cons χ L ih =>
    rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, List.length_cons,
      Nat.cast_sub (teichExp_spec p χ).2.1]
    push_cast
    field_simp
    ring

variable (p) in
/-- The **Stickelberger defect** of a Gauss monomial: its weight `r/2` minus its `p`-adic content
`−log_p ‖∏ g(χ)‖`. -/
noncomputable def stickelbergerDefect {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p)
    (L : List (MulChar (ZMod p) (PadicAlgCl p))) : ℝ :=
  (L.length : ℝ) / 2 +
    Real.logb p ‖(L.map fun χ => gaussSum χ (AddChar.zmodChar p hζ.pow_eq_one)).prod‖

/-- **The defect is `S/(p − 1) − r/2`**, `S = Σ n_χ`. -/
theorem stickelbergerDefect_eq {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p)
    (L : List (MulChar (ZMod p) (PadicAlgCl p))) :
    stickelbergerDefect p hζ L =
      ((L.map (teichExp p)).sum : ℝ) / ((p - 1 : ℕ) : ℝ) - (L.length : ℝ) / 2 := by
  rw [stickelbergerDefect, (logb_norm_prod hζ L).2,
    List.map_congr_left fun χ _ => logb_norm_gaussSum hζ χ, sum_logb_eq]
  ring

/-- **The Möbius parity law is the half-integrality of the Stickelberger defect.** -/
theorem isMoebiusSignedTuple_iff_defect {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p)
    {L : List (MulChar (ZMod p) (PadicAlgCl p))} (hne : L ≠ []) (hL : ∀ χ ∈ L, χ ≠ 1)
    (hsq : L.prod ^ 2 = 1) :
    IsMoebiusSignedTuple L ↔ ∃ j : ℤ, stickelbergerDefect p hζ L = j + 1 / 2 := by
  have hp2 := hp.out.two_le
  set S := (L.map (teichExp p)).sum with hS
  set r := L.length with hr
  have hN0 : 0 < p - 1 := by omega
  have hprod := prod_eq_teichCharK_pow L
  -- `2S = (p − 1) q`
  obtain ⟨q, hq⟩ : p - 1 ∣ 2 * S := by
    rw [← orderOf_teichCharK p]
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [mul_comm, pow_mul, ← hprod, hsq]
  have hone : L.prod = 1 ↔ Even q := by
    rw [hprod, ← orderOf_dvd_iff_pow_eq_one, orderOf_teichCharK]
    constructor
    · rintro ⟨s, hs⟩
      refine ⟨s, ?_⟩
      have : (p - 1) * q = (p - 1) * (s + s) := by rw [← hq, hs]; ring
      exact Nat.eq_of_mul_eq_mul_left hN0 this
    · rintro ⟨s, hs⟩
      refine ⟨s, ?_⟩
      have : 2 * S = 2 * ((p - 1) * s) := by rw [hq, hs]; ring
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  have hdef : stickelbergerDefect p hζ L = ((q : ℝ) - r) / 2 := by
    rw [stickelbergerDefect_eq, ← hS, ← hr]
    have hN : ((p - 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN0.ne'
    have hq' : (2 : ℝ) * S = ((p - 1 : ℕ) : ℝ) * q := by exact_mod_cast hq
    field_simp
    linarith
  have hmoeb : IsMoebiusSignedTuple L ↔
      (L.prod = 1 ∧ Odd r) ∨ (L.prod ≠ 1 ∧ Even r) :=
    ⟨fun h => h.parity, fun h => ⟨hne, fun χ hχ => by
      have h1 : orderOf χ ≠ 1 := fun h' => hL χ hχ (orderOf_eq_one_iff.1 h')
      have h0 : 0 < orderOf χ := by
        rw [(teichExp_spec p χ).2.2]
        exact Nat.pos_of_dvd_of_pos (orderOf_dvd_sub_one p _) hN0
      omega, hsq, h⟩⟩
  rw [hmoeb, hone, hdef]
  constructor
  · rintro (⟨⟨s, hs⟩, ⟨t, ht⟩⟩ | ⟨hs, ⟨t, ht⟩⟩)
    · refine ⟨(s : ℤ) - t - 1, ?_⟩
      rw [hs, ht]
      push_cast
      ring
    · obtain ⟨s, hs⟩ := Nat.not_even_iff_odd.1 hs
      refine ⟨(s : ℤ) - t, ?_⟩
      rw [hs, ht]
      push_cast
      ring
  · rintro ⟨j, hj⟩
    have hz : (q : ℤ) - r = 2 * j + 1 := by
      have : ((q : ℤ) : ℝ) - ((r : ℤ) : ℝ) = 2 * j + 1 := by push_cast; linarith
      exact_mod_cast this
    rcases Nat.even_or_odd q with hqe | hqo
    · left
      refine ⟨hqe, ?_⟩
      obtain ⟨s, hs⟩ := hqe
      refine ⟨(s : ℤ).toNat - j.toNat - 1 + 0, ?_⟩
      omega
    · right
      refine ⟨Nat.not_even_iff_odd.2 hqo, ?_⟩
      obtain ⟨s, hs⟩ := hqo
      refine ⟨s - j.toNat, ?_⟩
      omega

/-- **No pure Möbius-signed Gauss monomial.** The defect of a Möbius-signed monomial is at least
`½` in absolute value. -/
theorem half_le_abs_stickelbergerDefect {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p)
    {L : List (MulChar (ZMod p) (PadicAlgCl p))} (hL : ∀ χ ∈ L, χ ≠ 1)
    (hM : IsMoebiusSignedTuple L) : 1 / 2 ≤ |stickelbergerDefect p hζ L| := by
  obtain ⟨j, hj⟩ := (isMoebiusSignedTuple_iff_defect hζ hM.nonempty hL hM.prod_sq_eq_one).1 hM
  rw [hj]
  rcases le_or_gt 0 j with h | h
  · have : (0 : ℝ) ≤ j := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have : (j : ℝ) ≤ -1 := by exact_mod_cast (Int.lt_iff_add_one_le.1 h)
    rw [abs_of_neg (by linarith)]
    linarith

#print axioms isMoebiusSignedTuple_iff_defect
#print axioms half_le_abs_stickelbergerDefect

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.Stickelberger
