import GaloisForLFunctions.RHTower.HalfWeightCoefficientL

/-!
# Fourier coefficients of the weight-½ Eisenstein series with a character of prime conductor

For a prime `q`, a nontrivial `ψ₀` mod `q` (hence primitive), and `ψ = ψ₀` lifted to level `4M`:

* `conj_char_eq_gauss`: `τ(ψ₀) ψ̄₀(x) = Σ_b ψ₀(b) e(xb/q)` (`gaussSum_mulShift_of_isPrimitive`).
* `gPsi_changeLevel`: `g_ψ(k; c) = τ(ψ₀)⁻¹ Σ_b ψ₀(b) c_c(k + b c/q)` for `4M ∣ c`.
* `klH_changeLevel`: `klH_ψ(n,c) = (ic)^{1/2}/√2 · τ(ψ₀)⁻¹ T(n,c)`, `T(n,c) = Σ_b ψ₀(b) (μ*N(n + bc/q))(c)`
  (Ramanujan sums over squares, `sum_ramSum_sq`).
* **`Tsum_eq`**: for `q ∤ c'`, `T(n, q^α c') = (μ*N(n))(c') ψ̄₀(c') A_α(n)` with
  `A_α(n) = Σ_b ψ₀(b) N_{q^α}(n + b q^{α-1})`: multiplicativity of `μ*N`, periodicity of `N_f`, and
  `(μ*N)(q^α) = N_{q^α} - N_{q^{α-1}}` where the second term is independent of `b` and cancels
  against `Σ_b ψ₀(b) = 0`.
* `sum_sqCount_shift`, `norm_Aq_le`: `Σ_b N_{q^α}(n + b q^{α-1}) = q N_{q^{α-1}}(n)`, so
  `|A_α(n)| ≤ q N_{q^{α-1}}(n)`.
* `Ftw_eq`: `[4M'q² ∣ c] T(n,c) = (Q * ψ̄₀ g_L)(c)` with `Q(q^α) = A_α(n)` (`α ≥ 2`).
* **`Dser_tw_eq_LSeries`**: `D_n(w) = i^{1/2}/(√2 τ(ψ₀)) · L(Q * ψ̄₀ g_L, 2w - 1/2)` at level `4M'q²`.
-/

open Complex Matrix Filter Topology ArithmeticFunction
open scoped MatrixGroups Real ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RHTower.HalfWeight

open GaloisForLFunctions.RHTower.CoprimeClassExact GaloisForLFunctions.RHTower.CoprimeClassRamanujan

noncomputable section

section Gauss

variable {q : ℕ} [hq : Fact q.Prime] (ψ₀ : DirichletCharacter ℂ q)

theorem isPrimitive_of_ne_one (h : ψ₀ ≠ 1) : ψ₀.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  have hd := ψ₀.conductor_dvd_level
  rcases (Nat.dvd_prime hq.out).1 hd with h1 | h1
  · exact absurd ((DirichletCharacter.eq_one_iff_conductor_eq_one (χ := ψ₀)).2 h1) h
  · exact h1

/-- The Gauss sum `τ(ψ₀) = Σ_b ψ₀(b) e(b/q)`. -/
def tauG : ℂ := gaussSum ψ₀ ZMod.stdAddChar

theorem tauG_ne_zero (h : ψ₀ ≠ 1) : tauG ψ₀ ≠ 0 := by
  refine gaussSum_ne_zero_of_nontrivial ?_ h (ZMod.isPrimitive_stdAddChar q)
  rw [ZMod.card]; exact_mod_cast hq.out.ne_zero

theorem stdAddChar_mul_val (x b : ZMod q) :
    ZMod.stdAddChar (x * b) = cexp (2 * π * I * ((x.val : ℕ) : ℂ) * ((b.val : ℕ) : ℂ) / q) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.out.ne_zero
  have hk := Nat.mod_add_div (x.val * b.val) q
  rw [← ZMod.val_mul] at hk
  obtain ⟨K, hK⟩ : ∃ K, K = x.val * b.val / q := ⟨_, rfl⟩
  rw [← hK] at hk
  have hkC : (((x * b).val : ℕ) : ℂ) + q * (K : ℂ) =
      ((x.val : ℕ) : ℂ) * ((b.val : ℕ) : ℂ) := by exact_mod_cast hk
  rw [show 2 * (π : ℂ) * I * ((x.val : ℕ) : ℂ) * ((b.val : ℕ) : ℂ) / q =
      2 * π * I * (((x * b).val : ℕ) : ℂ) / q + (((K : ℕ) : ℤ) : ℂ) * (2 * π * I) by
    rw [mul_assoc (2 * (π : ℂ) * I), ← hkC]; push_cast; field_simp,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **Gauss expansion of a primitive character**: `τ(ψ₀) ψ̄₀(x) = Σ_b ψ₀(b) e(x b/q)`. -/
theorem conj_char_eq_gauss (h : ψ₀ ≠ 1) (x : ZMod q) :
    starRingEnd ℂ (ψ₀ x) = (tauG ψ₀)⁻¹ * ∑ b : ZMod q, ψ₀ b *
      cexp (2 * π * I * ((x.val : ℕ) : ℂ) * ((b.val : ℕ) : ℂ) / q) := by
  have hg := gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar (isPrimitive_of_ne_one ψ₀ h) x
  rw [show starRingEnd ℂ (ψ₀ x) = star (ψ₀ x) from rfl, MulChar.star_apply', eq_inv_mul_iff_mul_eq₀ (tauG_ne_zero ψ₀ h), mul_comm, tauG, ← hg]
  unfold gaussSum
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [AddChar.mulShift_apply, stdAddChar_mul_val]

theorem cexp_val_natCast (r : ℕ) (b : ZMod q) :
    cexp (2 * π * I * ((((r : ZMod q)).val : ℕ) : ℂ) * ((b.val : ℕ) : ℂ) / q) =
      cexp (2 * π * I * (r : ℂ) * ((b.val : ℕ) : ℂ) / q) := by
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.out.ne_zero
  have hk := Nat.mod_add_div r q
  rw [← ZMod.val_natCast] at hk
  obtain ⟨K, hK⟩ : ∃ K, K = r / q := ⟨_, rfl⟩
  rw [← hK] at hk
  have hkC : ((((r : ZMod q)).val : ℕ) : ℂ) + q * (K : ℂ) = (r : ℂ) := by exact_mod_cast hk
  rw [show 2 * (π : ℂ) * I * (r : ℂ) * ((b.val : ℕ) : ℂ) / q =
      2 * π * I * ((((r : ZMod q)).val : ℕ) : ℂ) * ((b.val : ℕ) : ℂ) / q +
        (((K * b.val : ℕ) : ℤ) : ℂ) * (2 * π * I) by
    rw [← hkC]; push_cast; field_simp,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

variable {M : ℕ} (hqM : q ∣ 4 * M)

theorem changeLevel_natCast {c r : ℕ} (h4 : 4 * M ∣ c) (hcr : c.Coprime r) :
    ψ₀.changeLevel hqM ((r : ℤ) : ZMod (4 * M)) = ψ₀ (r : ZMod q) := by
  have hu : IsUnit ((r : ℕ) : ZMod (4 * M)) :=
    (ZMod.isUnit_iff_coprime r (4 * M)).2 (Nat.Coprime.coprime_dvd_right h4 hcr.symm)
  obtain ⟨u, hu⟩ := hu
  have h := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ₀ hqM u
  rw [hu] at h
  push_cast
  rw [h, ZMod.cast_natCast hqM]

/-- **The twisted Ramanujan sum through Gauss sums**: for `ψ = ψ₀` lifted to `4M` and `4M ∣ c`,
`g_ψ(k; c) = τ(ψ₀)⁻¹ Σ_b ψ₀(b) c_c(k + b c/q)`. -/
theorem gPsi_changeLevel (h1 : ψ₀ ≠ 1) {c : ℕ} (hc : 0 < c) (h4 : 4 * M ∣ c) (k : ℤ) :
    gPsi M (ψ₀.changeLevel hqM) k c = (tauG ψ₀)⁻¹ *
      ∑ b : ZMod q, ψ₀ b * ramSum (k + ((b.val : ℕ) : ℤ) * ((c / q : ℕ) : ℤ)) c := by
  obtain ⟨e, rfl⟩ : q ∣ c := dvd_trans hqM h4
  rw [Nat.mul_div_cancel_left e hq.out.pos]
  have hcC : ((q * e : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.out.ne_zero
  have heC : (e : ℂ) ≠ 0 := by
    intro h0; apply hcC; push_cast; rw [h0, mul_zero]
  unfold gPsi ramSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hiff : IsCoprime ((q * e : ℕ) : ℤ) (r : ℤ) ↔ (q * e).Coprime r := Nat.isCoprime_iff_coprime
  by_cases hcr : (q * e).Coprime r
  · rw [if_pos (hiff.2 hcr)]
    simp only [if_pos hcr]
    rw [changeLevel_natCast ψ₀ hqM h4 hcr, conj_char_eq_gauss ψ₀ h1, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [cexp_val_natCast]
    unfold ph
    rw [show cexp (2 * π * I * ((k + ((b.val : ℕ) : ℤ) * ((e : ℕ) : ℤ) : ℤ) : ℂ) * (r : ℂ) /
        ((q * e : ℕ) : ℂ)) = cexp (2 * π * I * (r : ℂ) * ((b.val : ℕ) : ℂ) / q) *
          cexp (2 * π * I * k * (r : ℂ) / ((q * e : ℕ) : ℂ)) by
      rw [← Complex.exp_add]; congr 1; push_cast; field_simp; ring]
    ring
  · rw [if_neg (fun h => hcr (hiff.1 h))]
    simp only [if_neg hcr, mul_zero, Finset.sum_const_zero]

/-- **The twisted weight-½ Kloosterman sum**: for `4M ∣ c`,
`klH_ψ(n,c) = (ic)^{1/2}/√2 · τ(ψ₀)⁻¹ Σ_b ψ₀(b) (μ * N(n + b c/q))(c)`. -/
theorem klH_changeLevel (h1 : ψ₀ ≠ 1) {c : ℕ} [NeZero c] (h4 : 4 * M ∣ c) (n : ℤ) :
    klH M (ψ₀.changeLevel hqM) n c = (I * c) ^ (1 / 2 : ℂ) / Real.sqrt 2 * (tauG ψ₀)⁻¹ *
      ∑ b : ZMod q, ψ₀ b * muN (n + ((b.val : ℕ) : ℤ) * ((c / q : ℕ) : ℤ)) c := by
  have hc : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have h4' : (4 : ℤ) ∣ c := by
    have : (4 : ℕ) ∣ c := dvd_trans (dvd_mul_right 4 M) h4
    exact_mod_cast this
  have hcC : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  rw [klH_pos_eq M _ h4' n]
  simp_rw [gPsi_changeLevel ψ₀ hqM h1 hc h4]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hb : ∀ b : ZMod q, ∑ m ∈ Finset.range c, ψ₀ b *
      ramSum (n - (m : ℤ) ^ 2 + ((b.val : ℕ) : ℤ) * ((c / q : ℕ) : ℤ)) c =
      ψ₀ b * (c * muN (n + ((b.val : ℕ) : ℤ) * ((c / q : ℕ) : ℤ)) c) := by
    intro b
    rw [← Finset.mul_sum]
    congr 1
    have := sum_ramSum_sq hc (n + ((b.val : ℕ) : ℤ) * ((c / q : ℕ) : ℤ))
    rw [muN, ← this]
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1; ring
  simp_rw [hb]
  rw [show ∑ b : ZMod q, ψ₀ b * (c * muN (n + ((b.val : ℕ) : ℤ) * ((c / q : ℕ) : ℤ)) c) =
      (c : ℂ) * ∑ b : ZMod q, ψ₀ b * muN (n + ((b.val : ℕ) : ℤ) * ((c / q : ℕ) : ℤ)) c by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring]
  field_simp

end Gauss

/-! ### Periodicity of the square-root counts -/

theorem sqCount_add_mul (n t : ℤ) (f : ℕ) : sqCount (n + f * t) f = sqCount n f := by
  unfold sqCount
  refine Finset.sum_congr rfl fun m _ => ?_
  have : (f : ℤ) ∣ n + f * t - (m : ℤ) ^ 2 ↔ (f : ℤ) ∣ n - (m : ℤ) ^ 2 := by
    rw [show n + f * t - (m : ℤ) ^ 2 = n - (m : ℤ) ^ 2 + f * t by ring]
    exact dvd_add_left (dvd_mul_right _ _)
  simp only [this]

theorem sqCount_add_dvd {d F : ℕ} (hd : d ∣ F) (n t : ℤ) : sqCount (n + F * t) d = sqCount n d := by
  obtain ⟨k, rfl⟩ := hd
  rw [show n + ((d * k : ℕ) : ℤ) * t = n + (d : ℤ) * (k * t) by push_cast; ring, sqCount_add_mul]

theorem muN_add_mul (n t : ℤ) (c : ℕ) : muN (n + c * t) c = muN n c := by
  unfold muN
  refine Finset.sum_congr rfl fun e he => ?_
  rw [sqCount_add_dvd (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors he))]

theorem muN_mul_of_coprime (n : ℤ) {a b : ℕ} (hab : a.Coprime b) : muN n (a * b) = muN n a * muN n b := by
  rw [← fN_apply, ← fN_apply, ← fN_apply]
  exact (isMultiplicative_fN n).map_mul_of_coprime hab

theorem muN_prime_pow (n : ℤ) {p : ℕ} (hp : p.Prime) {i : ℕ} (hi : 1 ≤ i) :
    muN n (p ^ i) = sqCount n (p ^ i) - sqCount n (p ^ (i - 1)) := by
  rw [← fN_apply, fN, moebius_mul_prime_pow _ hp hi, Nfun_apply, Nfun_apply]

/-! ### The `q`-part of the twisted coefficients -/

section Qpart

variable {q : ℕ} [hq : Fact q.Prime] (ψ₀ : DirichletCharacter ℂ q)

/-- `A_α(n) = Σ_{b mod q} ψ₀(b) N_{q^α}(n + b q^{α-1})`. -/
def Aq (n : ℤ) (α : ℕ) : ℂ :=
  ∑ b : ZMod q, ψ₀ b * sqCount (n + ((b.val : ℕ) : ℤ) * ((q ^ (α - 1) : ℕ) : ℤ)) (q ^ α)

/-- The sum `T(n,c) = Σ_b ψ₀(b) (μ * N(n + b c/q))(c)`. -/
def Tsum (n : ℤ) (c : ℕ) : ℂ :=
  ∑ b : ZMod q, ψ₀ b * muN (n + ((b.val : ℕ) : ℤ) * ((c / q : ℕ) : ℤ)) c

omit hq in
theorem sqCount_congr (n : ℤ) {A B : ℤ} {α : ℕ} (hα : 1 ≤ α) (h : (q : ℤ) ∣ A - B) :
    sqCount (n + A * ((q ^ (α - 1) : ℕ) : ℤ)) (q ^ α) = sqCount (n + B * ((q ^ (α - 1) : ℕ) : ℤ)) (q ^ α) := by
  obtain ⟨t, ht⟩ := h
  have hqα : ((q ^ α : ℕ) : ℤ) = q * ((q ^ (α - 1) : ℕ) : ℤ) := by
    push_cast; rw [← pow_succ']; congr 1; omega
  rw [show n + A * ((q ^ (α - 1) : ℕ) : ℤ) = n + B * ((q ^ (α - 1) : ℕ) : ℤ) + ((q ^ α : ℕ) : ℤ) * t by
    rw [hqα, show A = B + q * t by linarith]; ring, sqCount_add_mul]

/-- **The `q`-part**: for `q ∤ c'`, `α ≥ 1`, `T(n, q^α c') = (μ * N(n))(c') ψ̄₀(c') A_α(n)`. -/
theorem Tsum_eq (h1 : ψ₀ ≠ 1) (n : ℤ) {α c' : ℕ} (hα : 1 ≤ α) (hc' : ¬ q ∣ c') :
    Tsum ψ₀ n (q ^ α * c') = muN n c' * starRingEnd ℂ (ψ₀ c') * Aq ψ₀ n α := by
  have hq1 := hq.out
  have hcop : (q ^ α).Coprime c' := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hq1).2 hc')
  have hdiv : q ^ α * c' / q = q ^ (α - 1) * c' := by
    rw [show q ^ α = q * q ^ (α - 1) by rw [← pow_succ']; congr 1; omega, mul_assoc,
      Nat.mul_div_cancel_left _ hq1.pos]
  unfold Tsum
  rw [hdiv]
  have hb : ∀ b : ZMod q, ψ₀ b * muN (n + ((b.val : ℕ) : ℤ) * ((q ^ (α - 1) * c' : ℕ) : ℤ)) (q ^ α * c') =
      muN n c' * (ψ₀ b * sqCount (n + ((b.val : ℕ) : ℤ) * ((q ^ (α - 1) * c' : ℕ) : ℤ)) (q ^ α)) -
      muN n c' * sqCount n (q ^ (α - 1)) * ψ₀ b := by
    intro b
    rw [muN_mul_of_coprime _ hcop, muN_prime_pow _ hq1 hα]
    have e1 : muN (n + ((b.val : ℕ) : ℤ) * ((q ^ (α - 1) * c' : ℕ) : ℤ)) c' = muN n c' := by
      rw [show n + ((b.val : ℕ) : ℤ) * ((q ^ (α - 1) * c' : ℕ) : ℤ) =
          n + (c' : ℤ) * (((b.val : ℕ) : ℤ) * ((q ^ (α - 1) : ℕ) : ℤ)) by push_cast; ring, muN_add_mul]
    have e2 : sqCount (n + ((b.val : ℕ) : ℤ) * ((q ^ (α - 1) * c' : ℕ) : ℤ)) (q ^ (α - 1)) =
        sqCount n (q ^ (α - 1)) := by
      rw [show n + ((b.val : ℕ) : ℤ) * ((q ^ (α - 1) * c' : ℕ) : ℤ) =
          n + ((q ^ (α - 1) : ℕ) : ℤ) * (((b.val : ℕ) : ℤ) * c') by push_cast; ring, sqCount_add_mul]
    rw [e1, e2]; ring
  simp_rw [hb]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, MulChar.sum_eq_zero_of_ne_one h1,
    mul_zero, sub_zero, mul_assoc]
  congr 1
  -- reindex `b ↦ b c'`
  have hu : IsUnit ((c' : ℕ) : ZMod q) := by
    rw [ZMod.isUnit_iff_coprime]
    exact (Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd hq1).2 hc')
  obtain ⟨u, hu⟩ := hu
  unfold Aq
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Units.mulRight u) _ _ fun b => ?_
  simp only [Units.mulRight_apply]
  rw [hu, map_mul]
  have hconj : starRingEnd ℂ (ψ₀ (c' : ZMod q)) * ψ₀ (c' : ZMod q) = 1 := by
    rw [← hu, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      DirichletCharacter.unit_norm_eq_one]; simp
  have e3 : ((b.val : ℕ) : ℤ) * ((q ^ (α - 1) * c' : ℕ) : ℤ) =
      (((b.val : ℕ) : ℤ) * c') * ((q ^ (α - 1) : ℕ) : ℤ) := by push_cast; ring
  have hcg : sqCount (n + (((b.val : ℕ) : ℤ) * c') * ((q ^ (α - 1) : ℕ) : ℤ)) (q ^ α) =
      sqCount (n + (((b * (c' : ZMod q)).val : ℕ) : ℤ) * ((q ^ (α - 1) : ℕ) : ℤ)) (q ^ α) := by
    refine sqCount_congr n hα ?_
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast
    simp
  rw [e3, hcg]
  linear_combination (-(ψ₀ b * sqCount (n + (((b * (c' : ZMod q)).val : ℕ) : ℤ) *
    ((q ^ (α - 1) : ℕ) : ℤ)) (q ^ α))) * hconj

/-- The count identity `Σ_{b mod q} N_{q^α}(n + b q^{α-1}) = q N_{q^{α-1}}(n)`. -/
theorem sum_sqCount_shift (n : ℤ) {α : ℕ} (hα : 1 ≤ α) :
    ∑ b : ZMod q, sqCount (n + ((b.val : ℕ) : ℤ) * ((q ^ (α - 1) : ℕ) : ℤ)) (q ^ α) =
      (q : ℂ) * sqCount n (q ^ (α - 1)) := by
  have hq1 := hq.out
  have hqα : q ^ α = q ^ (α - 1) * q := by rw [← pow_succ]; congr 1; omega
  unfold sqCount
  rw [Finset.sum_comm]
  have hm : ∀ m ∈ Finset.range (q ^ α), ∑ b : ZMod q,
      (if ((q ^ α : ℕ) : ℤ) ∣ n + ((b.val : ℕ) : ℤ) * ((q ^ (α - 1) : ℕ) : ℤ) - (m : ℤ) ^ 2 then (1 : ℂ) else 0) =
      if ((q ^ (α - 1) : ℕ) : ℤ) ∣ n - (m : ℤ) ^ 2 then 1 else 0 := by
    intro m _
    split_ifs with hd
    · obtain ⟨t, ht⟩ := hd
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hfilt : Finset.univ.filter (fun b : ZMod q => ((q ^ α : ℕ) : ℤ) ∣
          n + ((b.val : ℕ) : ℤ) * ((q ^ (α - 1) : ℕ) : ℤ) - (m : ℤ) ^ 2) = {((-t : ℤ) : ZMod q)} := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        rw [show n + ((b.val : ℕ) : ℤ) * ((q ^ (α - 1) : ℕ) : ℤ) - (m : ℤ) ^ 2 =
            ((q ^ (α - 1) : ℕ) : ℤ) * (t + ((b.val : ℕ) : ℤ)) by linear_combination ht,
          hqα, Nat.cast_mul, mul_dvd_mul_iff_left (by exact_mod_cast (pow_pos hq1.pos _).ne')]
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val, add_eq_zero_iff_neg_eq, eq_comm]
      rw [hfilt, Finset.card_singleton]; simp
    · refine Finset.sum_eq_zero fun b _ => ?_
      rw [if_neg]
      intro h
      apply hd
      have h2 : ((q ^ (α - 1) : ℕ) : ℤ) ∣ n + ((b.val : ℕ) : ℤ) * ((q ^ (α - 1) : ℕ) : ℤ) - (m : ℤ) ^ 2 :=
        dvd_trans (by rw [hqα, Nat.cast_mul]; exact dvd_mul_right _ _) h
      rw [show n - (m : ℤ) ^ 2 = n + ((b.val : ℕ) : ℤ) * ((q ^ (α - 1) : ℕ) : ℤ) - (m : ℤ) ^ 2 -
        ((q ^ (α - 1) : ℕ) : ℤ) * ((b.val : ℕ) : ℤ) by ring]
      exact dvd_sub h2 (dvd_mul_right _ _)
  rw [Finset.sum_congr rfl hm, sum_dvd_sub_sq ⟨q, hqα⟩ n, hqα,
    Nat.mul_div_cancel_left _ (pow_pos hq1.pos _)]
  rfl

theorem sqCount_nonneg_re (n : ℤ) (f : ℕ) : ∃ r : ℕ, sqCount n f = (r : ℂ) := by
  unfold sqCount
  refine ⟨∑ m ∈ Finset.range f, if (f : ℤ) ∣ n - (m : ℤ) ^ 2 then 1 else 0, ?_⟩
  push_cast; rfl

/-- `|A_α(n)| ≤ q N_{q^{α-1}}(n)`. -/
theorem norm_Aq_le (n : ℤ) {α : ℕ} (hα : 1 ≤ α) :
    ‖Aq ψ₀ n α‖ ≤ q * ‖sqCount n (q ^ (α - 1))‖ := by
  unfold Aq
  calc ‖∑ b : ZMod q, ψ₀ b * sqCount (n + ((b.val : ℕ) : ℤ) * ((q ^ (α - 1) : ℕ) : ℤ)) (q ^ α)‖
      ≤ ∑ b : ZMod q, ‖sqCount (n + ((b.val : ℕ) : ℤ) * ((q ^ (α - 1) : ℕ) : ℤ)) (q ^ α)‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)
    _ = ‖∑ b : ZMod q, sqCount (n + ((b.val : ℕ) : ℤ) * ((q ^ (α - 1) : ℕ) : ℤ)) (q ^ α)‖ := by
        have : ∀ b : ZMod q, ‖sqCount (n + ((b.val : ℕ) : ℤ) * ((q ^ (α - 1) : ℕ) : ℤ)) (q ^ α)‖ =
            (sqCount (n + ((b.val : ℕ) : ℤ) * ((q ^ (α - 1) : ℕ) : ℤ)) (q ^ α)).re := by
          intro b
          obtain ⟨r, hr⟩ := sqCount_nonneg_re (n + ((b.val : ℕ) : ℤ) * ((q ^ (α - 1) : ℕ) : ℤ)) (q ^ α)
          rw [hr]; simp
        simp_rw [this]
        obtain ⟨R, hR⟩ : ∃ R : ℕ, ∑ b : ZMod q,
            sqCount (n + ((b.val : ℕ) : ℤ) * ((q ^ (α - 1) : ℕ) : ℤ)) (q ^ α) = (R : ℂ) := by
          rw [sum_sqCount_shift n hα]
          obtain ⟨r, hr⟩ := sqCount_nonneg_re n (q ^ (α - 1))
          exact ⟨q * r, by rw [hr]; push_cast; ring⟩
        rw [← Complex.re_sum, hR]; simp
    _ = q * ‖sqCount n (q ^ (α - 1))‖ := by
        rw [sum_sqCount_shift n hα, norm_mul, Complex.norm_natCast]

/-- The `q`-part `Q(q^α) = A_α(n)` (`α ≥ 2`), supported on powers of `q`. -/
def Qf (n : ℤ) : ArithmeticFunction ℂ :=
  ⟨fun c => if 2 ≤ padicValNat q c ∧ c = q ^ padicValNat q c then Aq ψ₀ n (padicValNat q c) else 0,
    by simp⟩

/-- `ψ̄₀` as an arithmetic function. -/
def conjA : ArithmeticFunction ℂ := ⟨fun c => if c = 0 then 0 else starRingEnd ℂ (ψ₀ c), by simp⟩

theorem conjA_apply {c : ℕ} (hc : c ≠ 0) : conjA ψ₀ c = starRingEnd ℂ (ψ₀ c) := by
  simp [conjA, hc]

/-- The `q`-free part `ψ̄₀ · g_L` at level `4M'`. -/
def Btw (n : ℤ) (M' : ℕ) : ArithmeticFunction ℂ := (conjA ψ₀).pmul (gL (n := n) (M := M'))

theorem Qf_pow (n : ℤ) (α : ℕ) : Qf ψ₀ n (q ^ α) = if 2 ≤ α then Aq ψ₀ n α else 0 := by
  simp only [Qf, ArithmeticFunction.coe_mk, padicValNat.prime_pow, and_true]

theorem not_dvd_of_Btw_ne_zero {n : ℤ} {M' b : ℕ} (h : Btw ψ₀ n M' b ≠ 0) : ¬ q ∣ b := by
  intro hb
  apply h
  rw [Btw, ArithmeticFunction.pmul_apply]
  by_cases hb0 : b = 0
  · simp [hb0]
  rw [conjA_apply ψ₀ hb0]
  have : ((b : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff b q).2 hb
  rw [this, MulChar.map_nonunit _ not_isUnit_zero]
  simp

theorem Tsum_zero (n : ℤ) : Tsum ψ₀ n 0 = 0 := by
  simp [Tsum, muN]

/-- **The coefficient function as a Dirichlet convolution**: for `q ∤ 4M'`,
`[4M'q² ∣ c] T(n,c) = (Q * ψ̄₀ g_L)(c)`. -/
theorem Ftw_eq (h1 : ψ₀ ≠ 1) (n : ℤ) {M' : ℕ} (hcop : q.Coprime (4 * M')) (c : ℕ) :
    (if 4 * (M' * q ^ 2) ∣ c then Tsum ψ₀ n c else 0) = (Qf ψ₀ n * Btw ψ₀ n M') c := by
  have hq1 := hq.out
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp [Tsum_zero]
  set v := padicValNat q c with hv
  set c' := c / q ^ v with hc'
  have hcc : c = q ^ v * c' := (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
  have hc'0 : c' ≠ 0 := by rintro h; rw [h, mul_zero] at hcc; omega
  have hqc' : ¬ q ∣ c' := by
    intro hd
    apply pow_succ_padicValNat_not_dvd (p := q) hc.ne'
    rw [← hv, hcc, pow_succ]
    exact mul_dvd_mul_left _ hd
  rw [ArithmeticFunction.mul_apply, Finset.sum_eq_single_of_mem (q ^ v, c')
    (by rw [Nat.mem_divisorsAntidiagonal]; exact ⟨hcc.symm, hc.ne'⟩)]
  · -- the main term
    rw [Qf_pow, Btw, ArithmeticFunction.pmul_apply, conjA_apply ψ₀ hc'0, gL_apply]
    dsimp only
    have hiff : 4 * (M' * q ^ 2) ∣ c ↔ 2 ≤ v ∧ 4 * M' ∣ c' := by
      rw [hcc]
      have hc4 : (q ^ 2).Coprime (4 * M') := Nat.Coprime.pow_left _ hcop
      constructor
      · intro h
        have h1' : q ^ 2 ∣ q ^ v * c' := dvd_trans ⟨4 * M', by ring⟩ h
        have h2' : 4 * M' ∣ q ^ v * c' := dvd_trans ⟨q ^ 2, by ring⟩ h
        refine ⟨?_, (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_left v hcop).symm h2')⟩
        by_contra hlt
        push Not at hlt
        have : q ^ 2 ∣ q ^ v * c' := h1'
        have hv2 : padicValNat q (q ^ v * c') = v := by
          rw [padicValNat.mul (pow_ne_zero _ hq1.ne_zero) hc'0, padicValNat.prime_pow,
            padicValNat.eq_zero_of_not_dvd hqc', add_zero]
        have := (padicValNat_dvd_iff_le (p := q) (mul_ne_zero (pow_ne_zero _ hq1.ne_zero) hc'0)).1 this
        omega
      · rintro ⟨hv2, h4⟩
        rw [show 4 * (M' * q ^ 2) = q ^ 2 * (4 * M') by ring]
        exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hc4 (dvd_mul_of_dvd_left (pow_dvd_pow q hv2) _)
          (dvd_mul_of_dvd_right h4 _)
    by_cases hv2 : 2 ≤ v
    · by_cases h4 : 4 * M' ∣ c'
      · rw [if_pos (hiff.2 ⟨hv2, h4⟩), if_pos hv2, if_pos h4, hcc,
          Tsum_eq ψ₀ h1 n (by omega) hqc', fN_apply]
        ring
      · rw [if_neg (fun h => h4 (hiff.1 h).2), if_neg h4]; simp
    · rw [if_neg (fun h => hv2 (hiff.1 h).1), if_neg hv2]; simp
  · -- the other terms vanish
    rintro ⟨a, b⟩ hab hne
    rw [Nat.mem_divisorsAntidiagonal] at hab
    obtain ⟨hab1, hab2⟩ := hab
    by_contra hQB
    have hQ : Qf ψ₀ n a ≠ 0 := left_ne_zero_of_mul hQB
    have hB : Btw ψ₀ n M' b ≠ 0 := right_ne_zero_of_mul hQB
    have hqb := not_dvd_of_Btw_ne_zero ψ₀ hB
    have ha : a = q ^ padicValNat q a := by
      by_contra h
      apply hQ
      simp only [Qf, ArithmeticFunction.coe_mk]
      rw [if_neg (fun h' => h h'.2)]
    have ha0 : a ≠ 0 := fun h => by rw [h, zero_mul] at hab1; omega
    have hb0 : b ≠ 0 := fun h => by rw [h, mul_zero] at hab1; omega
    have hva : padicValNat q c = padicValNat q a := by
      rw [← hab1, padicValNat.mul ha0 hb0, padicValNat.eq_zero_of_not_dvd hqb, add_zero]
    apply hne
    have ha' : a = q ^ v := by rw [hv, hva]; exact ha
    have hb' : b = c' := by
      rw [hc', ← hab1, ha', Nat.mul_div_cancel_left _ (pow_pos hq1.pos _)]
    rw [ha', hb']

/-- **The twisted coefficient series as an `L`-series**: for `ψ = ψ₀` lifted to level
`4M'q²` (`q ∤ 4M'`), `D_n(w) = i^{1/2}/(√2 τ(ψ₀)) · L(Q * ψ̄₀ g_L, 2w - 1/2)`. -/
theorem Dser_tw_eq_LSeries (h1 : ψ₀ ≠ 1) (n : ℤ) {M' : ℕ} [NeZero M'] (hcop : q.Coprime (4 * M'))
    (hqM : q ∣ 4 * (M' * q ^ 2)) (w : ℂ) :
    Dser (M' * q ^ 2) (ψ₀.changeLevel hqM) n w = I ^ (1 / 2 : ℂ) / Real.sqrt 2 * (tauG ψ₀)⁻¹ *
      LSeries (fun c => (Qf ψ₀ n * Btw ψ₀ n M') c) (2 * w - 1 / 2) := by
  unfold Dser LSeries
  have hinj : Function.Injective (fun k : ℕ => k + 1) := fun a b h => by simpa using h
  have hsupp : Function.support (LSeries.term (fun c => (Qf ψ₀ n * Btw ψ₀ n M') c) (2 * w - 1 / 2)) ⊆
      Set.range (fun k : ℕ => k + 1) := by
    intro c hc
    rw [Function.mem_support, LSeries.term_def] at hc
    split_ifs at hc with hc0
    · exact absurd rfl hc
    · exact ⟨c - 1, by simp only; omega⟩
  rw [← hinj.tsum_eq hsupp, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero k), ← Ftw_eq ψ₀ h1 n hcop]
  split_ifs with h4
  · haveI : NeZero (k + 1) := ⟨Nat.succ_ne_zero k⟩
    simp only [Nat.succ_eq_add_one]
    rw [klH_changeLevel ψ₀ hqM h1 h4 n]
    have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hsplit : (I * ((k + 1 : ℕ) : ℂ)) ^ (1 / 2 : ℂ) =
        I ^ (1 / 2 : ℂ) * ((k + 1 : ℕ) : ℂ) ^ (1 / 2 : ℂ) := by
      have := cpow_mul_ofReal_pos (x := I) Complex.I_ne_zero hpos (1 / 2 : ℂ)
      simpa using this
    have hk0 : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hpow : ((k + 1 : ℕ) : ℂ) ^ (-2 * w) = ((k + 1 : ℕ) : ℂ) ^ (-1 / 2 : ℂ) *
        (((k + 1 : ℕ) : ℂ) ^ (2 * w - 1 / 2))⁻¹ := by
      rw [← Complex.cpow_neg, ← Complex.cpow_add _ _ hk0]; congr 1; ring
    have hh : ((k + 1 : ℕ) : ℂ) ^ (-1 / 2 : ℂ) * ((k + 1 : ℕ) : ℂ) ^ (1 / 2 : ℂ) = 1 := by
      rw [← Complex.cpow_add _ _ hk0]; norm_num
    have hP : ((k + 1 : ℕ) : ℂ) ^ (2 * w - 1 / 2) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; push Not; intro h; exact absurd h hk0
    rw [hsplit, Tsum, hpow]
    set A := ((k + 1 : ℕ) : ℂ) ^ (1 / 2 : ℂ)
    set B := ((k + 1 : ℕ) : ℂ) ^ (-1 / 2 : ℂ)
    set P := ((k + 1 : ℕ) : ℂ) ^ (2 * w - 1 / 2)
    set J := I ^ (1 / 2 : ℂ)
    set Sb := ∑ b : ZMod q, ψ₀ b * muN (n + ((b.val : ℕ) : ℤ) * (((k + 1) / q : ℕ) : ℤ)) (k + 1)
    field_simp
    linear_combination (J * Sb * (tauG ψ₀)⁻¹) * hh
  · simp

end Qpart


end

end GaloisForLFunctions.RHTower.HalfWeight
