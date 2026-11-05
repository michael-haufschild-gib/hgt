import GaloisForLFunctions.RHTower.Matveev.EffectiveBaker

/-!
# The prime flow is Diophantine at torsion points

The discreteness that the Euler product carries, in its basic form. The Kronecker flow
`t ↦ (p^{−it}, p'^{−it})` of two distinct primes is dense in the torus, but it approaches any
torsion point `(e^{2πia/N}, e^{2πia'/N})` at most polynomially fast:

* **Chord bound** (`exists_chord_lower`). For real `φ` there is `m ∈ ℤ` with
  `(2/π)|φ − 2πm| ≤ |e^{iφ} − 1|` (Jordan's inequality on the nearest representative).
* **Polynomial approach** (`primeFlow_diophantine_at_torsion`). There are `c, C > 0` with
  `max(|p^{−it} − e^{2πia/N}|, |p'^{−it} − e^{2πia'/N}|) ≥ c (2 + |t|)^{−C}` for `|t| ≥ 1`. If both
  coordinates are `ε`-close, `N t log p/(2π)` and `N t log p'/(2π)` are within `O(Nε)` of integers
  `−k, −k'`, so `|k' log p − k log p'| ≲ Nε`; the pair `(k, k')` is not zero for `|t| ≥ 1`, and the
  effective Baker bound (`RHTower.Matveev.effectiveBakerBound_holds`) bounds the form below by a
  power of `|k| + |k'| ≲ N|t|`.

Torsion points are exactly where integral pure Euler carriers have their consistent tangencies
(`pow_twelve_eq_one_of_satake`, `exists_pow_eq_one_of_pure`), and where algebraic carriers have
only singular ones (`algebraic_tangency_is_singular`); this is the Diophantine input their
polynomial collide-or-repel laws rest on.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

/-- **Chord bound.** -/
theorem exists_chord_lower (φ : ℝ) :
    ∃ m : ℤ, 2 / Real.pi * |φ - 2 * Real.pi * m| ≤ ‖Complex.exp (φ * I) - 1‖ := by
  set m : ℤ := round (φ / (2 * Real.pi)) with hm
  refine ⟨m, ?_⟩
  set ψ : ℝ := φ - 2 * Real.pi * m with hψ
  have hpi : 0 < Real.pi := Real.pi_pos
  have hψπ : |ψ| ≤ Real.pi := by
    have h := abs_sub_round (φ / (2 * Real.pi))
    rw [← hm] at h
    have : ψ = 2 * Real.pi * (φ / (2 * Real.pi) - m) := by rw [hψ]; field_simp
    rw [this, abs_mul, abs_of_pos (by positivity)]
    nlinarith
  have hexp : Complex.exp (φ * I) = Complex.exp (I * ψ) := by
    have : (φ : ℂ) * I = I * ψ + ((m : ℤ) : ℂ) * (2 * Real.pi * I) := by
      rw [hψ]; push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hexp, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_two]
  -- `|sin(ψ/2)| ≥ (2/π)|ψ/2|`
  have hj := Real.mul_le_sin (x := |ψ| / 2) (by positivity) (by linarith)
  have hψ2 := abs_le.mp hψπ
  have hs : Real.sin (|ψ| / 2) = |Real.sin (ψ / 2)| := by
    rcases le_total 0 ψ with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
        (by linarith [hψ2.2]))]
    · have e : Real.sin (-ψ / 2) = -Real.sin (ψ / 2) := by
        rw [show -ψ / 2 = -(ψ / 2) by ring, Real.sin_neg]
      have h1 : 0 ≤ Real.sin (-ψ / 2) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hψ2.1])
      rw [e] at h1
      rw [abs_of_nonpos h, e, abs_of_nonpos (by linarith)]
  rw [hs] at hj
  calc 2 / Real.pi * |ψ| = 2 * (2 / Real.pi * (|ψ| / 2)) := by ring
    _ ≤ 2 * |Real.sin (ψ / 2)| := by linarith

/-- A coordinate of the flow near a root of unity. -/
theorem exists_flow_chord {P : ℝ} (hP : 0 < P) (t θ : ℝ) :
    ∃ m : ℤ, 2 / Real.pi * |-(t * Real.log P) - θ - 2 * Real.pi * m| ≤
      ‖((P : ℝ) : ℂ) ^ (-((t : ℂ) * I)) - Complex.exp (θ * I)‖ := by
  obtain ⟨m, hm⟩ := exists_chord_lower (-(t * Real.log P) - θ)
  refine ⟨m, hm.trans_eq ?_⟩
  have hcp : ((P : ℝ) : ℂ) ^ (-((t : ℂ) * I)) = Complex.exp (θ * I) *
      Complex.exp (((-(t * Real.log P) - θ : ℝ) : ℂ) * I) := by
    rw [cpow_def_of_ne_zero (by exact_mod_cast hP.ne'), ← Complex.ofReal_log hP.le,
      ← Complex.exp_add]
    congr 1; push_cast; ring
  rw [hcp, show Complex.exp (θ * I) * Complex.exp (((-(t * Real.log P) - θ : ℝ) : ℂ) * I) -
      Complex.exp (θ * I) = Complex.exp (θ * I) *
        (Complex.exp (((-(t * Real.log P) - θ : ℝ) : ℂ) * I) - 1) by ring, norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul]

/-- The integer pair attached to two chord representatives: `k = a + Nm`, with
`N t L/(2π) = −k − Nψ/(2π)` for `ψ = −tL − 2πa/N − 2πm`. -/
theorem chord_integer_eq {L t : ℝ} {N : ℕ} (hN : 0 < N) (a m : ℤ) :
    ((a + N * m : ℤ) : ℝ) =
      -(N * (t * L + (-(t * L) - 2 * Real.pi * a / N - 2 * Real.pi * m)) / (2 * Real.pi)) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast; field_simp; ring

/-- **The linear form of two chords.** -/
theorem chord_form_le {L L' t ψ ψ' δ : ℝ} {N : ℕ} (hL : 0 < L) (hL' : 0 < L') {k k' : ℤ}
    (hk : (k : ℝ) = -(N * (t * L + ψ) / (2 * Real.pi)))
    (hk' : (k' : ℝ) = -(N * (t * L' + ψ') / (2 * Real.pi))) (hψ : |ψ| ≤ δ) (hψ' : |ψ'| ≤ δ) :
    |(k' : ℝ) * L - k * L'| ≤ N * (L + L') * δ / (2 * Real.pi) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hform : (k' : ℝ) * L - k * L' = N * (L' * ψ - L * ψ') / (2 * Real.pi) := by
    rw [hk, hk']; field_simp; ring
  rw [hform, abs_div, abs_mul, Nat.abs_cast, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg N)
  calc |L' * ψ - L * ψ'| ≤ L' * |ψ| + L * |ψ'| := by
        refine (abs_sub _ _).trans ?_; rw [abs_mul, abs_mul, abs_of_pos hL, abs_of_pos hL']
    _ ≤ L' * δ + L * δ := by gcongr
    _ = (L + L') * δ := by ring

/-- **The integer of a chord is bounded by the time.** -/
theorem chord_integer_le {L t ψ δ : ℝ} {N : ℕ} (hL : 0 < L) {k : ℤ}
    (hk : (k : ℝ) = -(N * (t * L + ψ) / (2 * Real.pi))) (hψ : |ψ| ≤ δ) :
    |(k : ℝ)| ≤ N * (|t| * L + δ) / (2 * Real.pi) := by
  rw [hk, abs_neg, abs_div, abs_mul, Nat.abs_cast,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg N))
    (by positivity)
  calc |t * L + ψ| ≤ |t| * L + |ψ| := by refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_of_pos hL]
    _ ≤ |t| * L + δ := by linarith

/-- **The integer of a chord is nonzero at time `|t| L > δ`.** -/
theorem chord_integer_ne_zero {L t ψ δ : ℝ} {N : ℕ} (hN : 0 < N) (hL : 0 < L) {k : ℤ}
    (hk : (k : ℝ) = -(N * (t * L + ψ) / (2 * Real.pi))) (hψ : |ψ| ≤ δ) (ht : δ < |t| * L) :
    k ≠ 0 := by
  intro h0
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : t * L + ψ = 0 := by
    have h2 : (k : ℝ) = 0 := by exact_mod_cast h0
    rw [hk, neg_eq_zero, div_eq_zero_iff] at h2
    rcases h2 with h | h
    · exact (mul_eq_zero.mp h).resolve_left hNr.ne'
    · exact absurd h (by positivity)
  have : |t| * L = |ψ| := by
    rw [show ψ = -(t * L) by linarith, abs_neg, abs_mul, abs_of_pos hL]
  linarith

theorem chord_scale_eq (N L ε : ℝ) :
    N * L * (Real.pi / 2 * ε) / (2 * Real.pi) = N * L * ε / 4 := by
  have : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp; ring

theorem four_div_mul_cancel {x ε : ℝ} (hx : x ≠ 0) : 4 / x * (x * ε / 4) = ε := by
  field_simp

/-- **The prime flow is Diophantine at torsion points.** -/
theorem primeFlow_diophantine_at_torsion {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime) (hne : p ≠ p')
    {N : ℕ} (hN : 0 < N) (a a' : ℤ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| →
      c * (2 + |t|) ^ (-C) ≤
        max ‖((p : ℝ) : ℂ) ^ (-((t : ℂ) * I)) - Complex.exp ((2 * Real.pi * a / N : ℝ) * I)‖
          ‖((p' : ℝ) : ℂ) ^ (-((t : ℂ) * I)) - Complex.exp ((2 * Real.pi * a' / N : ℝ) * I)‖ := by
  have hinj : Function.Injective ![p, p'] := by
    intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have hpr : ∀ i, (![p, p'] i).Prime := by intro i; fin_cases i <;> simpa
  obtain ⟨c₀, C₀, hc₀, hC₀, hB⟩ := RHTower.Matveev.effectiveBakerBound_holds ![p, p'] hinj hpr
  have hL : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hL' : 0 < Real.log p' := Real.log_pos (by exact_mod_cast hp'.one_lt)
  have hLge : Real.log 2 ≤ Real.log p :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨S, hS⟩ : ∃ S, S = Real.log p + Real.log p' := ⟨_, rfl⟩
  have hS0 : 0 < S := by rw [hS]; linarith
  obtain ⟨A, hA⟩ : ∃ A, A = 1 + N + N * S / (2 * Real.pi) := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hA]; positivity
  have hε₀0 : 0 < Real.log 2 / Real.pi := div_pos (Real.log_pos (by norm_num)) hpi
  refine ⟨min (Real.log 2 / Real.pi) (4 * c₀ * A ^ (-C₀) / (N * S)), C₀,
    lt_min hε₀0 (by have := Real.rpow_pos_of_pos hA0 (-C₀); positivity), hC₀, fun t ht => ?_⟩
  have ht0 : 0 < 2 + |t| := by positivity
  have htC : (2 + |t|) ^ (-C₀) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg t]) (by linarith)
  have htCpos : 0 < (2 + |t|) ^ (-C₀) := Real.rpow_pos_of_pos ht0 _
  obtain ⟨m, hm⟩ := exists_flow_chord (by exact_mod_cast hp.pos : (0 : ℝ) < p) t
    (2 * Real.pi * a / N)
  obtain ⟨m', hm'⟩ := exists_flow_chord (by exact_mod_cast hp'.pos : (0 : ℝ) < p') t
    (2 * Real.pi * a' / N)
  generalize hε : max ‖((p : ℝ) : ℂ) ^ (-((t : ℂ) * I)) - Complex.exp ((2 * Real.pi * a / N : ℝ) * I)‖
    ‖((p' : ℝ) : ℂ) ^ (-((t : ℂ) * I)) - Complex.exp ((2 * Real.pi * a' / N : ℝ) * I)‖ = ε
  have hle1 := hε ▸ le_max_left
    ‖((p : ℝ) : ℂ) ^ (-((t : ℂ) * I)) - Complex.exp ((2 * Real.pi * a / N : ℝ) * I)‖
    ‖((p' : ℝ) : ℂ) ^ (-((t : ℂ) * I)) - Complex.exp ((2 * Real.pi * a' / N : ℝ) * I)‖
  have hle2 := hε ▸ le_max_right
    ‖((p : ℝ) : ℂ) ^ (-((t : ℂ) * I)) - Complex.exp ((2 * Real.pi * a / N : ℝ) * I)‖
    ‖((p' : ℝ) : ℂ) ^ (-((t : ℂ) * I)) - Complex.exp ((2 * Real.pi * a' / N : ℝ) * I)‖
  by_cases hbig : Real.log 2 / Real.pi ≤ ε
  · calc min (Real.log 2 / Real.pi) (4 * c₀ * A ^ (-C₀) / (N * S)) * (2 + |t|) ^ (-C₀)
        ≤ min (Real.log 2 / Real.pi) (4 * c₀ * A ^ (-C₀) / (N * S)) * 1 :=
          mul_le_mul_of_nonneg_left htC (le_min hε₀0.le (by
            have := Real.rpow_pos_of_pos hA0 (-C₀); positivity))
      _ ≤ Real.log 2 / Real.pi := by rw [mul_one]; exact min_le_left _ _
      _ ≤ ε := hbig
  push Not at hbig
  -- both chords are at most `δ = πε/2 < log 2 / 2`
  have hδ : ∀ ψ : ℝ, 2 / Real.pi * |ψ| ≤ ε → |ψ| ≤ Real.pi / 2 * ε := fun ψ h => by
    have h2 : |ψ| = Real.pi / 2 * (2 / Real.pi * |ψ|) := by field_simp
    rw [h2]; exact mul_le_mul_of_nonneg_left h (by positivity)
  have hψ := hδ _ (hm.trans hle1)
  have hψ' := hδ _ (hm'.trans hle2)
  have hδlt : Real.pi / 2 * ε < Real.log 2 := by
    rw [lt_div_iff₀ hpi] at hbig; nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hk := chord_integer_eq (L := Real.log p) (t := t) hN a m
  have hk' := chord_integer_eq (L := Real.log p') (t := t) hN a' m'
  have hform := chord_form_le hL hL' hk hk' hψ hψ'
  have hk0 : a + N * m ≠ 0 :=
    chord_integer_ne_zero hN hL hk hψ (by nlinarith [abs_nonneg t])
  have hnz : (![a' + N * m', -(a + N * m)] : Fin 2 → ℤ) ≠ 0 := by
    intro h0
    exact hk0 (neg_eq_zero.mp (by simpa using congrFun h0 1))
  have hbaker := hB _ hnz
  have hformB : RHTower.Matveev.primeLogForm ![p, p'] ![a' + N * m', -(a + N * m)] =
      (((a' + N * m' : ℤ) : ℝ)) * Real.log p - ((a + N * m : ℤ) : ℝ) * Real.log p' := by
    unfold RHTower.Matveev.primeLogForm
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_neg]
    ring
  rw [hformB] at hbaker
  -- the height of the pair
  have hkb := chord_integer_le hL hk hψ
  have hkb' := chord_integer_le hL' hk' hψ'
  have hheight : 2 + (RHTower.Matveev.coeffHeight ![a' + N * m', -(a + N * m)] : ℝ) ≤
      A * (2 + |t|) := by
    have hcH : (RHTower.Matveev.coeffHeight ![a' + N * m', -(a + N * m)] : ℝ) =
        |((a' + N * m' : ℤ) : ℝ)| + |((a + N * m : ℤ) : ℝ)| := by
      unfold RHTower.Matveev.coeffHeight
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Int.natAbs_neg]
      push_cast
      rw [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
      norm_cast
    rw [hcH]
    have hsum : |((a' + N * m' : ℤ) : ℝ)| + |((a + N * m : ℤ) : ℝ)| ≤
        N + N * S / (2 * Real.pi) * |t| := by
      have hsplit : N * (|t| * Real.log p' + Real.pi / 2 * ε) / (2 * Real.pi) +
          N * (|t| * Real.log p + Real.pi / 2 * ε) / (2 * Real.pi) =
          N * S / (2 * Real.pi) * |t| + N * ε / 2 := by
        rw [hS]; field_simp; ring
      have hε1 : N * ε / 2 ≤ N := by
        have : ε ≤ 1 := by
          have : Real.log 2 / Real.pi ≤ 1 := by
            rw [div_le_one hpi]; linarith [Real.log_two_lt_d9, Real.pi_gt_three]
          linarith
        nlinarith
      linarith
    have hNS : 0 ≤ N * S / (2 * Real.pi) := by positivity
    rw [hA]
    nlinarith [abs_nonneg t]
  have hH0 : 0 < 2 + (RHTower.Matveev.coeffHeight ![a' + N * m', -(a + N * m)] : ℝ) := by
    positivity
  have hpow := Real.rpow_le_rpow_of_nonpos hH0 hheight (by linarith : -C₀ ≤ 0)
  rw [Real.mul_rpow hA0.le ht0.le] at hpow
  have hNS : 0 < N * S := by positivity
  have hform' : |(((a' + N * m' : ℤ) : ℝ)) * Real.log p - ((a + N * m : ℤ) : ℝ) * Real.log p'| ≤
      N * S * ε / 4 := by
    refine hform.trans (le_of_eq ?_)
    rw [hS]; exact chord_scale_eq _ _ _
  calc min (Real.log 2 / Real.pi) (4 * c₀ * A ^ (-C₀) / (N * S)) * (2 + |t|) ^ (-C₀)
      ≤ 4 * c₀ * A ^ (-C₀) / (N * S) * (2 + |t|) ^ (-C₀) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) htCpos.le
    _ = 4 / (N * S) * (c₀ * (A ^ (-C₀) * (2 + |t|) ^ (-C₀))) := by ring
    _ ≤ 4 / (N * S) * |(((a' + N * m' : ℤ) : ℝ)) * Real.log p - ((a + N * m : ℤ) : ℝ) *
          Real.log p'| :=
        mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hpow hc₀.le).trans hbaker)
          (by positivity)
    _ ≤ 4 / (N * S) * (N * S * ε / 4) := mul_le_mul_of_nonneg_left hform' (by positivity)
    _ = ε := four_div_mul_cancel hNS.ne'

end GaloisForLFunctions.ArithmeticDiscreteness
