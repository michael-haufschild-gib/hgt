import GaloisForLFunctions.RHTower.KloostermanComposite

/-!
# The second-moment kernel of hyper-Kloosterman sums over two moduli

Let `Kl₃(m; n) = Σ_{x₁x₂x₃ = m} e((x₁+x₂+x₃)/n)`, summed over all triples in `ZMod n`.

* **Fourier transform.** For a unit `β`, `Σ_m Kl₃(m; n) e(βm/n) = n S(1, -β⁻¹; n)`
  (`fourier_hyperKloosterman_three`). Summing the third coordinate gives `n·[1 + βx₁x₂ = 0]`,
  and the surviving pairs are `(u, -β⁻¹u⁻¹)` with `u` a unit. For `n > 1` the complete sum
  `Σ_m Kl₃(m; n)` vanishes (`sum_hyperKloosterman_three`), and `conj Kl₃(a) = Kl₃(-a)`
  (`star_hyperKloosterman_three`).
* **Product kernel.** For coprime `q, r` and a unit `h mod qr`,
  `Σ_{m mod qr} Kl₃(m; q) Kl₃(-m; r) e(hm/qr) = qr · S(1, h⁻¹(q³ - r³); qr)`
  (`second_moment_kernel`). The character splits by the Chinese remainder theorem and each
  factor is a Fourier transform. Twisted multiplicativity then recombines
  `S(1, -h⁻¹r; q) S(1, h⁻¹q; r)` into one sum modulo `qr`: the argument `h⁻¹(q³ - r³)` is
  `-h⁻¹r³` mod `q` and `h⁻¹q³` mod `r`. When `q ∣ h` the kernel vanishes
  (`second_moment_kernel_of_fst`).

By Poisson summation in `m`, these are the Fourier coefficients of the off-diagonal part of
`Σ_m G(m/L) |Σ_q w_q Kl₃(m; q)|²`. That off-diagonal is therefore the Kloosterman form
`L Σ_{h} Σ_{q ≠ q'} Ĝ(hL/qq') S(1, h⁻¹(q³ - q'³); qq')`, with no lower-order terms.
-/

open Finset

namespace GaloisForLFunctions.RHTower.HyperKloostermanSecondMoment

open GaloisForLFunctions.RHTower.HyperKloosterman RHTower.Sieve

noncomputable section

/-- A triple as three coordinates. -/
def tripleEquiv (R : Type*) : (Fin 3 → R) ≃ R × R × R where
  toFun x := (x 0, x 1, x 2)
  invFun t := ![t.1, t.2.1, t.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv t := rfl

theorem sum_fin_three {M : Type*} [AddCommMonoid M] {R : Type*} [Fintype R]
    (f : (Fin 3 → R) → M) :
    ∑ x, f x = ∑ a : R, ∑ b : R, ∑ c : R, f ![a, b, c] := by
  rw [← (tripleEquiv R).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

variable {n : ℕ} [NeZero n]

/-- Sum over the units as a sum over residues with a unit indicator. -/
theorem sum_units_eq {M : Type*} [AddCommMonoid M] (f : ZMod n → M) :
    ∑ u : (ZMod n)ˣ, f u = ∑ a : ZMod n, if IsUnit a then f a else 0 := by
  classical
  have h : ∀ a : ZMod n, (if IsUnit a then f a else 0) =
      ∑ u : (ZMod n)ˣ, if (u : ZMod n) = a then f a else 0 := by
    intro a
    by_cases ha : IsUnit a
    · obtain ⟨w, rfl⟩ := ha
      rw [if_pos (Units.isUnit w)]
      have : ∀ u : (ZMod n)ˣ, ((u : ZMod n) = w) ↔ u = w := fun u => Units.ext_iff.symm
      simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · rw [if_neg ha]
      refine (Finset.sum_eq_zero fun u _ => ?_).symm
      rw [if_neg]
      intro hu; exact ha (hu ▸ Units.isUnit u)
  simp_rw [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_ite_eq]
  simp

/-- The Fourier transform of `Kl₃` as a triple sum. -/
theorem fourier_eq_triple (β : ZMod n) :
    ∑ m : ZMod n, hyperKloosterman ZMod.stdAddChar 3 m * ZMod.stdAddChar (β * m) =
      ∑ a : ZMod n, ∑ b : ZMod n, ZMod.stdAddChar (a + b) *
        ∑ c : ZMod n, ZMod.stdAddChar (c * (1 + β * (a * b))) := by
  unfold hyperKloosterman
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, sum_fin_three]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [Fin.sum_univ_three, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- The complete additive-character sum `Σ_c e(cX) = n·[X = 0]`. -/
theorem sum_stdAddChar_mul (X : ZMod n) :
    ∑ c : ZMod n, ZMod.stdAddChar (c * X) = if X = 0 then (n : ℂ) else 0 := by
  rw [AddChar.sum_mulShift X (ZMod.isPrimitive_stdAddChar n), ZMod.card]
  split_ifs <;> simp

/-- For a unit `β`, the solutions of `1 + β a b = 0` are the pairs `(u, -β⁻¹u⁻¹)`. -/
theorem pair_sum_eq {β : ZMod n} (hβ : IsUnit β) :
    ∑ a : ZMod n, ∑ b : ZMod n, (if 1 + β * (a * b) = 0 then ZMod.stdAddChar (a + b) else 0) =
      ∑ a : ZMod n, if IsUnit a then ZMod.stdAddChar (a + (-β⁻¹) * a⁻¹) else 0 := by
  classical
  obtain ⟨v, rfl⟩ := hβ
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : IsUnit a
  · obtain ⟨w, rfl⟩ := ha
    rw [if_pos (Units.isUnit w)]
    have hiff : ∀ b : ZMod n, (1 + (v : ZMod n) * ((w : ZMod n) * b) = 0) ↔
        b = -(v : ZMod n)⁻¹ * (w : ZMod n)⁻¹ := by
      intro b
      rw [ZMod.inv_coe_unit, ZMod.inv_coe_unit]
      constructor
      · intro h
        have hv : (v : ZMod n) * ((v⁻¹ : (ZMod n)ˣ) : ZMod n) = 1 := Units.mul_inv v
        have hw : (w : ZMod n) * ((w⁻¹ : (ZMod n)ˣ) : ZMod n) = 1 := Units.mul_inv w
        linear_combination (((v⁻¹ : (ZMod n)ˣ) : ZMod n) * ((w⁻¹ : (ZMod n)ˣ) : ZMod n)) * h -
          (b * (w : ZMod n) * ((w⁻¹ : (ZMod n)ˣ) : ZMod n)) * hv - b * hw
      · intro h
        rw [h]
        have hv : (v : ZMod n) * ((v⁻¹ : (ZMod n)ˣ) : ZMod n) = 1 := Units.mul_inv v
        have hw : (w : ZMod n) * ((w⁻¹ : (ZMod n)ˣ) : ZMod n) = 1 := Units.mul_inv w
        linear_combination (-((w : ZMod n) * ((w⁻¹ : (ZMod n)ˣ) : ZMod n))) * hv - hw
    simp only [hiff, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · rw [if_neg ha]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg]
    intro h
    apply ha
    exact IsUnit.of_mul_eq_one (-((v : ZMod n) * b)) (by linear_combination -h)

/-- **The Fourier transform of `Kl₃` is a Kloosterman sum:** for a unit `β`,
`Σ_m Kl₃(m; n) e(βm/n) = n S(1, -β⁻¹; n)`. -/
theorem fourier_hyperKloosterman_three {β : ZMod n} (hβ : IsUnit β) :
    ∑ m : ZMod n, hyperKloosterman ZMod.stdAddChar 3 m * ZMod.stdAddChar (β * m) =
      n * kloostermanSum n 1 (-β⁻¹) := by
  rw [fourier_eq_triple]
  simp_rw [sum_stdAddChar_mul, mul_ite, mul_zero]
  have hswap : ∀ a b : ZMod n, (if 1 + β * (a * b) = 0 then
      ZMod.stdAddChar (a + b) * (n : ℂ) else 0) =
      (n : ℂ) * (if 1 + β * (a * b) = 0 then ZMod.stdAddChar (a + b) else 0) := by
    intro a b; split_ifs <;> ring
  simp_rw [hswap, ← Finset.mul_sum]
  rw [pair_sum_eq hβ, ← sum_units_eq]
  congr 1
  unfold kloostermanSum kloostermanPhase
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [one_mul, ZMod.inv_coe_unit]

/-- Reflection: `Σ_m Kl₃(-m) e(βm) = n S(1, β⁻¹; n)` for a unit `β`. -/
theorem fourier_hyperKloosterman_three_neg {β : ZMod n} (hβ : IsUnit β) :
    ∑ m : ZMod n, hyperKloosterman ZMod.stdAddChar 3 (-m) * ZMod.stdAddChar (β * m) =
      n * kloostermanSum n 1 β⁻¹ := by
  have h := fourier_hyperKloosterman_three (n := n) hβ.neg
  have hn : (-β)⁻¹ = -β⁻¹ := ZMod.inv_eq_of_mul_eq_one _ _ _ (by
    rw [neg_mul_neg]; exact ZMod.mul_inv_of_unit β hβ)
  rw [hn, neg_neg] at h
  rw [← h]
  refine Fintype.sum_equiv (Equiv.neg (ZMod n)) _ _ fun m => ?_
  simp only [Equiv.neg_apply, neg_mul, mul_neg, neg_neg]

omit [NeZero n] in
/-- A unit of `ZMod n` satisfies `u⁻¹ · u = 1` for the `ZMod` inverse. -/
theorem isUnit_inv_mul {a : ZMod n} (ha : IsUnit a) : a⁻¹ * a = 1 := by
  rw [mul_comm]; exact ZMod.mul_inv_of_unit a ha

section CRT

variable {q r : ℕ} [NeZero q] [NeZero r]

theorem sum_crt (hqr : q.Coprime r) (F : ZMod q → ZMod r → ℂ) :
    ∑ m : ZMod (q * r), F (ZMod.chineseRemainder hqr m).1 (ZMod.chineseRemainder hqr m).2 =
      ∑ a : ZMod q, ∑ b : ZMod r, F a b := by
  rw [← Fintype.sum_prod_type']
  exact (ZMod.chineseRemainder hqr).toEquiv.sum_comp (fun p => F p.1 p.2)

/-- **The complete second-moment kernel of `Kl₃` over two coprime moduli.** For a unit
`h mod qr`, the product-period Fourier coefficient of `m ↦ Kl₃(m; q) Kl₃(-m; r)` is a single
Kloosterman sum: `Σ_{m mod qr} Kl₃(m; q) Kl₃(-m; r) e(hm/qr) = qr · S(1, h⁻¹(q³ - r³); qr)`. -/
theorem second_moment_kernel (hqr : q.Coprime r) {h : ZMod (q * r)} (hh : IsUnit h) :
    ∑ m : ZMod (q * r),
        hyperKloosterman ZMod.stdAddChar 3 (ZMod.chineseRemainder hqr m).1 *
          hyperKloosterman ZMod.stdAddChar 3 (-(ZMod.chineseRemainder hqr m).2) *
          ZMod.stdAddChar (h * m) =
      ((q * r : ℕ) : ℂ) * kloostermanSum (q * r) 1
        (h⁻¹ * (((q : ℕ) : ZMod (q * r)) ^ 3 - ((r : ℕ) : ZMod (q * r)) ^ 3)) := by
  set C := ZMod.chineseRemainder hqr
  set h₁ : ZMod q := (C h).1
  set h₂ : ZMod r := (C h).2
  have hh₁ : IsUnit h₁ := hh.map ((RingHom.fst _ _).comp C.toRingHom)
  have hh₂ : IsUnit h₂ := hh.map ((RingHom.snd _ _).comp C.toRingHom)
  have hr : (r : ZMod q) * (r : ZMod q)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one r hqr.symm
  have hq : (q : ZMod r) * (q : ZMod r)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one q hqr
  have hrU : IsUnit ((r : ZMod q)⁻¹) := IsUnit.of_mul_eq_one (r : ZMod q) (by rw [mul_comm, hr])
  have hqU : IsUnit ((q : ZMod r)⁻¹) := IsUnit.of_mul_eq_one (q : ZMod r) (by rw [mul_comm, hq])
  -- split the character and the sum
  have hsplit : ∀ m : ZMod (q * r), ZMod.stdAddChar (h * m) =
      ZMod.stdAddChar (N := q) (h₁ * (r : ZMod q)⁻¹ * (C m).1) *
        ZMod.stdAddChar (N := r) (h₂ * (q : ZMod r)⁻¹ * (C m).2) := by
    intro m
    rw [stdAddChar_crt hqr]
    simp only [C, h₁, h₂, map_mul, Prod.fst_mul, Prod.snd_mul]
    congr 1 <;> ring_nf
  simp_rw [hsplit]
  rw [sum_crt hqr (fun a b => hyperKloosterman ZMod.stdAddChar 3 a *
      hyperKloosterman ZMod.stdAddChar 3 (-b) *
      (ZMod.stdAddChar (N := q) (h₁ * (r : ZMod q)⁻¹ * a) *
        ZMod.stdAddChar (N := r) (h₂ * (q : ZMod r)⁻¹ * b)))]
  have hfac : ∀ a b, hyperKloosterman ZMod.stdAddChar 3 a *
      hyperKloosterman ZMod.stdAddChar 3 (-b) *
      (ZMod.stdAddChar (N := q) (h₁ * (r : ZMod q)⁻¹ * a) *
        ZMod.stdAddChar (N := r) (h₂ * (q : ZMod r)⁻¹ * b)) =
      (hyperKloosterman ZMod.stdAddChar 3 a * ZMod.stdAddChar (N := q) (h₁ * (r : ZMod q)⁻¹ * a)) *
      (hyperKloosterman ZMod.stdAddChar 3 (-b) *
        ZMod.stdAddChar (N := r) (h₂ * (q : ZMod r)⁻¹ * b)) := by
    intro a b; ring
  simp_rw [hfac, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [fourier_hyperKloosterman_three (hh₁.mul hrU),
    fourier_hyperKloosterman_three_neg (hh₂.mul hqU)]
  -- the right side by twisted multiplicativity
  rw [KloostermanComposite.kloostermanSum_mul hqr]
  have h1 : (C 1).1 = 1 := by simp [C]
  have h2 : (C 1).2 = 1 := by simp [C]
  rw [h1, h2, one_mul, one_mul]
  have hinv : (C h⁻¹).1 = h₁⁻¹ ∧ (C h⁻¹).2 = h₂⁻¹ := by
    have hmul : C h⁻¹ * C h = 1 := by rw [← map_mul, isUnit_inv_mul hh, map_one]
    constructor
    · symm; apply ZMod.inv_eq_of_mul_eq_one
      have := congrArg Prod.fst hmul
      simp only [Prod.fst_mul, Prod.fst_one] at this
      rw [mul_comm]; exact this
    · symm; apply ZMod.inv_eq_of_mul_eq_one
      have := congrArg Prod.snd hmul
      simp only [Prod.snd_mul, Prod.snd_one] at this
      rw [mul_comm]; exact this
  have hB1 : (C (h⁻¹ * (((q : ℕ) : ZMod (q * r)) ^ 3 - ((r : ℕ) : ZMod (q * r)) ^ 3))).1 =
      h₁⁻¹ * (0 - (r : ZMod q) ^ 3) := by
    rw [map_mul, Prod.fst_mul, hinv.1]
    simp [C]
  have hB2 : (C (h⁻¹ * (((q : ℕ) : ZMod (q * r)) ^ 3 - ((r : ℕ) : ZMod (q * r)) ^ 3))).2 =
      h₂⁻¹ * ((q : ZMod r) ^ 3 - 0) := by
    rw [map_mul, Prod.snd_mul, hinv.2]
    simp [C]
  rw [hB1, hB2]
  have eU : (((ZMod.unitOfCoprime r hqr.symm)⁻¹ : (ZMod q)ˣ) : ZMod q) = (r : ZMod q)⁻¹ := by
    rw [← ZMod.inv_coe_unit, ZMod.coe_unitOfCoprime]
  have eV : (((ZMod.unitOfCoprime q hqr)⁻¹ : (ZMod r)ˣ) : ZMod r) = (q : ZMod r)⁻¹ := by
    rw [← ZMod.inv_coe_unit, ZMod.coe_unitOfCoprime]
  rw [← eU, kloostermanSum_unit_left, ← eV, kloostermanSum_unit_left, eU, eV]
  have e1 := ZMod.mul_inv_of_unit h₁ hh₁
  have e2 := ZMod.mul_inv_of_unit h₂ hh₂
  have k1 : -(h₁ * (r : ZMod q)⁻¹)⁻¹ =
      (r : ZMod q)⁻¹ * (h₁⁻¹ * (0 - (r : ZMod q) ^ 3) * (r : ZMod q)⁻¹) := by
    rw [ZMod.inv_eq_of_mul_eq_one _ (h₁ * (r : ZMod q)⁻¹) (h₁⁻¹ * r) (by
      calc h₁ * (r : ZMod q)⁻¹ * (h₁⁻¹ * r) = (h₁ * h₁⁻¹) * ((r : ZMod q) * (r : ZMod q)⁻¹) := by
            ring
        _ = 1 := by rw [e1, hr, one_mul])]
    linear_combination (h₁⁻¹ * (r : ZMod q) * ((r : ZMod q) * (r : ZMod q)⁻¹ + 1)) * hr
  have k2 : (h₂ * (q : ZMod r)⁻¹)⁻¹ =
      (q : ZMod r)⁻¹ * (h₂⁻¹ * ((q : ZMod r) ^ 3 - 0) * (q : ZMod r)⁻¹) := by
    rw [ZMod.inv_eq_of_mul_eq_one _ (h₂ * (q : ZMod r)⁻¹) (h₂⁻¹ * q) (by
      calc h₂ * (q : ZMod r)⁻¹ * (h₂⁻¹ * q) = (h₂ * h₂⁻¹) * ((q : ZMod r) * (q : ZMod r)⁻¹) := by
            ring
        _ = 1 := by rw [e2, hq, one_mul])]
    linear_combination (-(h₂⁻¹ * (q : ZMod r) * ((q : ZMod r) * (q : ZMod r)⁻¹ + 1))) * hq
  rw [k1, k2]
  push_cast
  ring

end CRT

/-- The complete sum of `Kl₃` vanishes for `n > 1`. -/
theorem sum_hyperKloosterman_three (hn : 1 < n) :
    ∑ m : ZMod n, hyperKloosterman ZMod.stdAddChar 3 m = 0 := by
  have h := fourier_eq_triple (n := n) 0
  simp only [zero_mul, AddChar.map_zero_eq_one, mul_one] at h
  rw [h]
  have h10 : (1 : ZMod n) ≠ 0 := by
    haveI : Fact (1 < n) := ⟨hn⟩
    exact one_ne_zero
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  rw [sum_stdAddChar_mul, if_neg (by simpa using h10), mul_zero]

omit [NeZero n] in
/-- Conjugation reflects the argument of `Kl₃`: `conj Kl₃(a) = Kl₃(-a)`. -/
theorem star_hyperKloosterman_three [NeZero n] (a : ZMod n) :
    star (hyperKloosterman ZMod.stdAddChar 3 a) = hyperKloosterman ZMod.stdAddChar 3 (-a) := by
  unfold hyperKloosterman
  rw [star_sum]
  refine Fintype.sum_equiv (Equiv.neg (Fin 3 → ZMod n)) _ _ fun x => ?_
  simp only [Equiv.neg_apply, Pi.neg_apply, Finset.sum_neg_distrib, Fin.prod_univ_three,
    Fin.sum_univ_three]
  by_cases hx : x 0 * x 1 * x 2 = a
  · rw [if_pos hx, if_pos (by rw [← hx]; ring), show ∀ z : ℂ, star z = starRingEnd ℂ z from
      fun _ => rfl, ← AddChar.map_neg_eq_conj]
  · rw [if_neg hx, if_neg (by intro h; apply hx; linear_combination -h), star_zero]

section CRTzero

variable {q r : ℕ} [NeZero q] [NeZero r]

/-- The kernel vanishes when `q ∣ h` (and `q > 1`). -/
theorem second_moment_kernel_of_fst (hqr : q.Coprime r) (hq1 : 1 < q) {h : ZMod (q * r)}
    (h0 : (ZMod.chineseRemainder hqr h).1 = 0) :
    ∑ m : ZMod (q * r),
        hyperKloosterman ZMod.stdAddChar 3 (ZMod.chineseRemainder hqr m).1 *
          hyperKloosterman ZMod.stdAddChar 3 (-(ZMod.chineseRemainder hqr m).2) *
          ZMod.stdAddChar (h * m) = 0 := by
  set C := ZMod.chineseRemainder hqr
  have hsplit : ∀ m : ZMod (q * r), ZMod.stdAddChar (h * m) =
      ZMod.stdAddChar (N := q) ((C h).1 * (r : ZMod q)⁻¹ * (C m).1) *
        ZMod.stdAddChar (N := r) ((C h).2 * (q : ZMod r)⁻¹ * (C m).2) := by
    intro m
    rw [stdAddChar_crt hqr]
    simp only [C, map_mul, Prod.fst_mul, Prod.snd_mul]
    congr 1 <;> ring_nf
  simp_rw [hsplit, h0, zero_mul, AddChar.map_zero_eq_one, one_mul]
  rw [sum_crt hqr (fun a b => hyperKloosterman ZMod.stdAddChar 3 a *
      hyperKloosterman ZMod.stdAddChar 3 (-b) *
        ZMod.stdAddChar (N := r) ((C h).2 * (q : ZMod r)⁻¹ * b))]
  have : ∀ a : ZMod q, ∑ b : ZMod r, hyperKloosterman ZMod.stdAddChar 3 a *
      hyperKloosterman ZMod.stdAddChar 3 (-b) *
        ZMod.stdAddChar (N := r) ((C h).2 * (q : ZMod r)⁻¹ * b) =
      hyperKloosterman ZMod.stdAddChar 3 a * ∑ b : ZMod r, hyperKloosterman ZMod.stdAddChar 3 (-b) *
        ZMod.stdAddChar (N := r) ((C h).2 * (q : ZMod r)⁻¹ * b) := by
    intro a; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
  simp_rw [this, ← Finset.sum_mul, sum_hyperKloosterman_three hq1, zero_mul]

end CRTzero

end

end GaloisForLFunctions.RHTower.HyperKloostermanSecondMoment
