import GaloisForLFunctions.RHTower.EisensteinHeckeOperator
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinLineInvariance
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.ResonantHeckePoissonMixtureAndDispersion

/-!
# Every Hecke operator is diagonal on the Eisenstein line model

The classical Hecke operator of index `n` on functions of `(x, y)` sums over the upper triangular
representatives of determinant `n`:

`T_n F(x, y) = n^{-1/2} Σ_{ad = n} Σ_{b < d} F((ax + b)/d, ay/d)`.

For a prime `p` it is `heckeOp p` (`heckeN_prime`).

* **Hecke recursion** (`heckeOp_heckeN`). On functions `1`-periodic in `x`,
  `T_p T_n = T_{pn} + 1_{p ∣ n} T_{n/p}`. The branch `F(px, py)` of `T_p` gives the
  representatives `(pa, d)` of `T_{pn}`. The residue branch sums `F((ax + ab + pc)/(pd), ·)` over
  `b < p`, `c < d`: for `p ∤ a` the numerators `ab + pc` run once through the residues modulo `pd`,
  giving the representatives `(a, pd)`; for `a = pa₁` they collapse to `p` copies of the `(a₁, d)`
  term of `T_{n/p}`.
* **Eigen-equation** (`heckeN_cuspLeg`). `T_n E_u = W_u(n) E_u` for every `n ≥ 1`, by induction on
  `n` from the prime case `heckeOp_cuspLeg` and the Hecke relation `whittakerCoeff_hecke`.
-/

set_option autoImplicit false

open Complex Finset
open RHTower

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates

noncomputable section

/-! ### The classical Hecke operator -/

/-- The orbit sum `Σ_{c < d} F((ax + c)/d, ay/d)` of one upper triangular representative. -/
def heckeOrbit (F : ℝ → ℝ → ℂ) (a d : ℕ) (x y : ℝ) : ℂ :=
  ∑ c ∈ range d, F (((a : ℝ) * x + (c : ℝ)) / (d : ℝ)) ((a : ℝ) * y / (d : ℝ))

/-- The classical Hecke operator `T_n F(x,y) = n^{-1/2} Σ_{ad=n} Σ_{b<d} F((ax+b)/d, ay/d)`. -/
def heckeN (n : ℕ) (F : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  (((Real.sqrt n)⁻¹ : ℝ) : ℂ) * ∑ ad ∈ n.divisorsAntidiagonal, heckeOrbit F ad.1 ad.2 x y

theorem heckeN_one (F : ℝ → ℝ → ℂ) (x y : ℝ) : heckeN 1 F x y = F x y := by
  simp [heckeN, heckeOrbit]

/-- At a prime the classical operator is `heckeOp`. -/
theorem heckeN_prime {p : ℕ} (hp : p.Prime) (F : ℝ → ℝ → ℂ) (x y : ℝ) :
    heckeN p F x y = heckeOp p F x y := by
  unfold heckeN heckeOp
  rw [Nat.sum_divisorsAntidiagonal (fun a d => heckeOrbit F a d x y), hp.divisors,
    Finset.sum_pair hp.one_lt.ne, Nat.div_one, Nat.div_self hp.pos]
  simp only [heckeOrbit, Nat.cast_one, one_mul, range_one, sum_singleton, Nat.cast_zero, add_zero,
    div_one]
  ring

theorem heckeN_const_mul (n : ℕ) (c : ℂ) (F : ℝ → ℝ → ℂ) (x y : ℝ) :
    heckeN n (fun x y => c * F x y) x y = c * heckeN n F x y := by
  simp only [heckeN, heckeOrbit, ← mul_sum]
  ring

theorem heckeN_sub (n : ℕ) (F G : ℝ → ℝ → ℂ) (x y : ℝ) :
    heckeN n (fun x y => F x y - G x y) x y = heckeN n F x y - heckeN n G x y := by
  simp only [heckeN, heckeOrbit, sum_sub_distrib]
  ring

theorem pos_of_mem_divisorsAntidiagonal {n : ℕ} {ad : ℕ × ℕ}
    (had : ad ∈ n.divisorsAntidiagonal) : 0 < ad.1 ∧ 0 < ad.2 := by
  obtain ⟨hprod, hn⟩ := Nat.mem_divisorsAntidiagonal.mp had
  refine ⟨Nat.pos_of_ne_zero fun h => hn ?_, Nat.pos_of_ne_zero fun h => hn ?_⟩
  · rw [← hprod, h, zero_mul]
  · rw [← hprod, h, mul_zero]

/-- `T_n` only sees positive heights. -/
theorem heckeN_congr {n : ℕ} {F G : ℝ → ℝ → ℂ} (h : ∀ x y, 0 < y → F x y = G x y) (x : ℝ)
    {y : ℝ} (hy : 0 < y) : heckeN n F x y = heckeN n G x y := by
  unfold heckeN heckeOrbit
  congr 1
  refine sum_congr rfl fun ad had => sum_congr rfl fun c _ => h _ _ ?_
  obtain ⟨ha, hd⟩ := pos_of_mem_divisorsAntidiagonal had
  have ha' : (0 : ℝ) < ad.1 := by exact_mod_cast ha
  have hd' : (0 : ℝ) < ad.2 := by exact_mod_cast hd
  positivity

theorem heckeOp_congr_pos {p : ℕ} (hp : 0 < p) {F G : ℝ → ℝ → ℂ}
    (h : ∀ x y, 0 < y → F x y = G x y) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    heckeOp p F x y = heckeOp p G x y := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  unfold heckeOp
  rw [h _ _ (mul_pos hpR hy)]
  congr 2
  exact sum_congr rfl fun b _ => h _ _ (div_pos hy hpR)

/-! ### Periodic sums -/

theorem periodic_add_nat {F : ℝ → ℝ → ℂ} (hF : ∀ x y, F (x + 1) y = F x y) (k : ℕ) (x y : ℝ) :
    F (x + k) y = F x y := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, ← add_assoc, hF, ih]

theorem periodic_mod {D : ℕ} (G : ℕ → ℂ) (hG : ∀ e, G (e + D) = G e) (e : ℕ) :
    G (e % D) = G e := by
  have h : ∀ q r, G (r + D * q) = G r := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih => intro r; rw [Nat.mul_succ, ← add_assoc, hG, ih]
  conv_rhs => rw [← Nat.mod_add_div e D]
  rw [h]

/-- A sum over one period is invariant under translation. -/
theorem sum_range_add_of_periodic {d : ℕ} (G : ℕ → ℂ) (hG : ∀ e, G (e + d) = G e) (k : ℕ) :
    ∑ c ∈ range d, G (k + c) = ∑ c ∈ range d, G c := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := sum_range_succ' (fun c => G (k + c)) d
    have h2 := sum_range_succ (fun c => G (k + c)) d
    have hd : G (k + d) = G (k + 0) := by rw [add_zero, hG]
    have hshift : ∑ c ∈ range d, G (k + 1 + c) = ∑ c ∈ range d, G (k + (c + 1)) :=
      sum_congr rfl fun c _ => by rw [add_assoc, add_comm 1 c]
    rw [hshift, ← ih]
    linear_combination h2 - h1 + hd

/-- **Residues modulo `pd`.** For `p ∤ a` the numerators `ab + pc`, `b < p`, `c < d`, form a complete
residue system modulo `pd`. -/
theorem sum_crt {p a d : ℕ} (hp : p.Prime) (ha : ¬ p ∣ a) (hd : 0 < d) (G : ℕ → ℂ)
    (hG : ∀ e, G (e + p * d) = G e) :
    ∑ b ∈ range p, ∑ c ∈ range d, G (a * b + p * c) = ∑ e ∈ range (p * d), G e := by
  set φ : ℕ × ℕ → ℕ := fun bc => (a * bc.1 + p * bc.2) % (p * d) with hφ
  have hsum : ∑ b ∈ range p, ∑ c ∈ range d, G (a * b + p * c) =
      ∑ bc ∈ range p ×ˢ range d, G (φ bc) := by
    rw [sum_product]
    exact sum_congr rfl fun b _ => sum_congr rfl fun c _ => (periodic_mod G hG _).symm
  have hinj : ∀ x ∈ range p ×ˢ range d, ∀ y ∈ range p ×ˢ range d, φ x = φ y → x = y := by
    rintro ⟨b, c⟩ hx ⟨b', c'⟩ hy hxy
    simp only [mem_product, mem_range] at hx hy
    have h : a * b + p * c ≡ a * b' + p * c' [MOD p * d] := hxy
    have h1 : a * b ≡ a * b' [MOD p] := by
      have h' := h.of_mul_right d
      unfold Nat.ModEq at h' ⊢
      simpa [Nat.add_mul_mod_self_left] using h'
    have hcop : Nat.gcd p a = 1 := (Nat.Prime.coprime_iff_not_dvd hp).mpr ha
    have hb : b = b' := by
      have h2 := Nat.ModEq.cancel_left_of_coprime hcop h1
      unfold Nat.ModEq at h2
      rwa [Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hy.1] at h2
    subst hb
    have h3 : c ≡ c' [MOD d] :=
      Nat.ModEq.mul_left_cancel' hp.ne_zero (Nat.ModEq.add_left_cancel' (a * b) h)
    unfold Nat.ModEq at h3
    rw [Nat.mod_eq_of_lt hx.2, Nat.mod_eq_of_lt hy.2] at h3
    rw [h3]
  have himage : (range p ×ˢ range d).image φ = range (p * d) := by
    apply eq_of_subset_of_card_le
    · intro e he
      obtain ⟨bc, -, rfl⟩ := mem_image.mp he
      exact mem_range.mpr (Nat.mod_lt _ (Nat.mul_pos hp.pos hd))
    · rw [card_image_of_injOn hinj, card_product, card_range, card_range, card_range]
  rw [hsum, ← himage, sum_image hinj]

/-! ### The two branches of `T_p` on one orbit -/

theorem heckeOrbit_scale (F : ℝ → ℝ → ℂ) (p a d : ℕ) (x y : ℝ) :
    heckeOrbit F a d (p * x) (p * y) = heckeOrbit F (p * a) d x y := by
  unfold heckeOrbit
  refine sum_congr rfl fun c _ => ?_
  push_cast
  ring_nf

/-- The residue branch on an orbit with `p ∤ a` is the orbit of `(a, pd)`. -/
theorem heckeOrbit_residue_coprime {p a d : ℕ} (hp : p.Prime) (ha : ¬ p ∣ a) (hd : 0 < d)
    {F : ℝ → ℝ → ℂ} (hF : ∀ x y, F (x + 1) y = F x y) (x y : ℝ) :
    ∑ b ∈ range p, heckeOrbit F a d ((x + b) / p) (y / p) = heckeOrbit F a (p * d) x y := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  set G : ℕ → ℂ := fun e =>
    F (((a : ℝ) * x + (e : ℝ)) / ((p * d : ℕ) : ℝ)) ((a : ℝ) * y / ((p * d : ℕ) : ℝ)) with hG
  have hGper : ∀ e, G (e + p * d) = G e := by
    intro e
    simp only [hG]
    have hx : ((a : ℝ) * x + ((e + p * d : ℕ) : ℝ)) / ((p * d : ℕ) : ℝ) =
        ((a : ℝ) * x + (e : ℝ)) / ((p * d : ℕ) : ℝ) + 1 := by
      push_cast
      field_simp
      ring
    rw [hx]
    exact hF _ _
  have hterm : ∀ b c : ℕ,
      F (((a : ℝ) * ((x + (b : ℝ)) / (p : ℝ)) + (c : ℝ)) / (d : ℝ))
          ((a : ℝ) * (y / (p : ℝ)) / (d : ℝ)) = G (a * b + p * c) := by
    intro b c
    simp only [hG]
    congr 1
    · push_cast
      field_simp
      ring
    · push_cast
      field_simp
  unfold heckeOrbit
  rw [show (∑ c ∈ range (p * d), F (((a : ℝ) * x + (c : ℝ)) / ((p * d : ℕ) : ℝ))
      ((a : ℝ) * y / ((p * d : ℕ) : ℝ))) = ∑ e ∈ range (p * d), G e from rfl,
    ← sum_crt hp ha hd G hGper]
  exact sum_congr rfl fun b _ => sum_congr rfl fun c _ => hterm b c

/-- The residue branch on an orbit with `a = pa₁` is `p` copies of the orbit of `(a₁, d)`. -/
theorem heckeOrbit_residue_dvd {p a₁ d : ℕ} (hp : 0 < p) (hd : 0 < d) {F : ℝ → ℝ → ℂ}
    (hF : ∀ x y, F (x + 1) y = F x y) (x y : ℝ) :
    ∑ b ∈ range p, heckeOrbit F (p * a₁) d ((x + b) / p) (y / p) =
      (p : ℂ) * heckeOrbit F a₁ d x y := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  set G : ℕ → ℂ := fun e => F (((a₁ : ℝ) * x + (e : ℝ)) / (d : ℝ)) ((a₁ : ℝ) * y / (d : ℝ))
    with hG
  have hGper : ∀ e, G (e + d) = G e := by
    intro e
    simp only [hG]
    have hx : ((a₁ : ℝ) * x + ((e + d : ℕ) : ℝ)) / (d : ℝ) =
        ((a₁ : ℝ) * x + (e : ℝ)) / (d : ℝ) + 1 := by
      rw [div_add_one hdR]
      push_cast
      ring
    rw [hx]
    exact hF _ _
  have hterm : ∀ b c : ℕ,
      F ((((p * a₁ : ℕ) : ℝ) * ((x + (b : ℝ)) / (p : ℝ)) + (c : ℝ)) / (d : ℝ))
          (((p * a₁ : ℕ) : ℝ) * (y / (p : ℝ)) / (d : ℝ)) = G (a₁ * b + c) := by
    intro b c
    simp only [hG]
    congr 1
    · push_cast
      field_simp
      ring
    · push_cast
      field_simp
  unfold heckeOrbit
  calc ∑ b ∈ range p, ∑ c ∈ range d,
        F ((((p * a₁ : ℕ) : ℝ) * ((x + (b : ℝ)) / (p : ℝ)) + (c : ℝ)) / (d : ℝ))
          (((p * a₁ : ℕ) : ℝ) * (y / (p : ℝ)) / (d : ℝ))
      = ∑ b ∈ range p, ∑ c ∈ range d, G (a₁ * b + c) :=
        sum_congr rfl fun b _ => sum_congr rfl fun c _ => hterm b c
    _ = ∑ _b ∈ range p, ∑ c ∈ range d, G c :=
        sum_congr rfl fun b _ => sum_range_add_of_periodic G hGper _
    _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]

/-! ### Representatives of determinant `pn` -/

/-- Representatives of `pn` split by divisibility of the first entry by `p`. -/
theorem sum_divisorsAntidiagonal_mul_prime {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : n ≠ 0)
    (H : ℕ → ℕ → ℂ) :
    ∑ AD ∈ (p * n).divisorsAntidiagonal, H AD.1 AD.2 =
      ∑ ad ∈ n.divisorsAntidiagonal, H (p * ad.1) ad.2 +
        ∑ ad ∈ n.divisorsAntidiagonal with ¬ p ∣ ad.1, H ad.1 (p * ad.2) := by
  have hpn : p * n ≠ 0 := mul_ne_zero hp.ne_zero hn
  rw [← sum_filter_add_sum_filter_not _ (fun AD : ℕ × ℕ => p ∣ AD.1)]
  congr 1
  · refine sum_nbij' (fun AD => (AD.1 / p, AD.2)) (fun ad => (p * ad.1, ad.2)) ?_ ?_ ?_ ?_ ?_
    · intro AD hAD
      simp only [mem_filter, Nat.mem_divisorsAntidiagonal] at hAD
      obtain ⟨⟨hprod, -⟩, ⟨k, hk⟩⟩ := hAD
      simp only [Nat.mem_divisorsAntidiagonal]
      refine ⟨?_, hn⟩
      rw [hk, Nat.mul_div_cancel_left _ hp.pos]
      rw [hk, mul_assoc] at hprod
      exact Nat.eq_of_mul_eq_mul_left hp.pos hprod
    · intro ad had
      simp only [mem_filter, Nat.mem_divisorsAntidiagonal] at had ⊢
      exact ⟨⟨by rw [mul_assoc, had.1], hpn⟩, dvd_mul_right p _⟩
    · intro AD hAD
      simp only [mem_filter] at hAD
      obtain ⟨-, k, hk⟩ := hAD
      ext
      · simp [hk, Nat.mul_div_cancel_left _ hp.pos]
      · rfl
    · intro ad _
      simp [Nat.mul_div_cancel_left _ hp.pos]
    · intro AD hAD
      simp only [mem_filter] at hAD
      obtain ⟨-, k, hk⟩ := hAD
      simp [hk, Nat.mul_div_cancel_left _ hp.pos]
  · refine sum_nbij' (fun AD => (AD.1, AD.2 / p)) (fun ad => (ad.1, p * ad.2)) ?_ ?_ ?_ ?_ ?_
    · intro AD hAD
      simp only [mem_filter, Nat.mem_divisorsAntidiagonal] at hAD ⊢
      obtain ⟨⟨hprod, -⟩, hnd⟩ := hAD
      have hdvd : p ∣ AD.2 := by
        have h : p ∣ AD.1 * AD.2 := hprod ▸ dvd_mul_right p n
        rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h2
        · exact absurd h1 hnd
        · exact h2
      obtain ⟨k, hk⟩ := hdvd
      refine ⟨⟨?_, hn⟩, hnd⟩
      rw [hk, Nat.mul_div_cancel_left _ hp.pos]
      rw [hk, mul_left_comm] at hprod
      exact Nat.eq_of_mul_eq_mul_left hp.pos hprod
    · intro ad had
      simp only [mem_filter, Nat.mem_divisorsAntidiagonal] at had ⊢
      exact ⟨⟨by rw [mul_left_comm, had.1.1], hpn⟩, had.2⟩
    · intro AD hAD
      simp only [mem_filter, Nat.mem_divisorsAntidiagonal] at hAD
      obtain ⟨⟨hprod, -⟩, hnd⟩ := hAD
      have hdvd : p ∣ AD.2 := by
        have h : p ∣ AD.1 * AD.2 := hprod ▸ dvd_mul_right p n
        rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h2
        · exact absurd h1 hnd
        · exact h2
      obtain ⟨k, hk⟩ := hdvd
      ext
      · rfl
      · simp [hk, Nat.mul_div_cancel_left _ hp.pos]
    · intro ad _
      simp [Nat.mul_div_cancel_left _ hp.pos]
    · intro AD hAD
      simp only [mem_filter, Nat.mem_divisorsAntidiagonal] at hAD
      obtain ⟨⟨hprod, -⟩, hnd⟩ := hAD
      have hdvd : p ∣ AD.2 := by
        have h : p ∣ AD.1 * AD.2 := hprod ▸ dvd_mul_right p n
        rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h2
        · exact absurd h1 hnd
        · exact h2
      obtain ⟨k, hk⟩ := hdvd
      simp [hk, Nat.mul_div_cancel_left _ hp.pos]

/-- Representatives of `n = pm` with first entry divisible by `p` are those of `m`. -/
theorem sum_filter_dvd_divisorsAntidiagonal {p m : ℕ} (hp : 0 < p) (hm : m ≠ 0)
    (H : ℕ → ℕ → ℂ) :
    ∑ ad ∈ (p * m).divisorsAntidiagonal with p ∣ ad.1, H (ad.1 / p) ad.2 =
      ∑ ad ∈ m.divisorsAntidiagonal, H ad.1 ad.2 := by
  have hpm : p * m ≠ 0 := mul_ne_zero hp.ne' hm
  refine sum_nbij' (fun AD => (AD.1 / p, AD.2)) (fun ad => (p * ad.1, ad.2)) ?_ ?_ ?_ ?_ ?_
  · intro AD hAD
    simp only [mem_filter, Nat.mem_divisorsAntidiagonal] at hAD ⊢
    obtain ⟨⟨hprod, -⟩, ⟨k, hk⟩⟩ := hAD
    refine ⟨?_, hm⟩
    rw [hk, Nat.mul_div_cancel_left _ hp]
    rw [hk, mul_assoc] at hprod
    exact Nat.eq_of_mul_eq_mul_left hp hprod
  · intro ad had
    simp only [mem_filter, Nat.mem_divisorsAntidiagonal] at had ⊢
    exact ⟨⟨by rw [mul_assoc, had.1], hpm⟩, dvd_mul_right p _⟩
  · intro AD hAD
    simp only [mem_filter] at hAD
    obtain ⟨-, k, hk⟩ := hAD
    ext
    · simp [hk, Nat.mul_div_cancel_left _ hp]
    · rfl
  · intro ad _
    simp [Nat.mul_div_cancel_left _ hp]
  · intro AD _
    rfl

theorem sum_filter_dvd_eq_zero {p n : ℕ} (hpn : ¬ p ∣ n) (H : ℕ → ℕ → ℂ) :
    ∑ ad ∈ n.divisorsAntidiagonal with p ∣ ad.1, H (ad.1 / p) ad.2 = 0 := by
  refine sum_eq_zero fun ad had => ?_
  simp only [mem_filter, Nat.mem_divisorsAntidiagonal] at had
  obtain ⟨⟨hprod, -⟩, hdvd⟩ := had
  exact absurd (hprod ▸ dvd_mul_of_dvd_left hdvd _) hpn

/-! ### The Hecke recursion -/

theorem sqrt_inv_mul_sqrt_inv (p n : ℕ) :
    (Real.sqrt p)⁻¹ * (Real.sqrt n)⁻¹ = (Real.sqrt ((p * n : ℕ) : ℝ))⁻¹ := by
  rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg p), mul_inv]

theorem sqrt_inv_mul_sqrt_inv_mul_self {p : ℕ} (hp : 0 < p) (m : ℕ) :
    (Real.sqrt p)⁻¹ * (Real.sqrt ((p * m : ℕ) : ℝ))⁻¹ * p = (Real.sqrt m)⁻¹ := by
  have hs : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt (Nat.cast_nonneg p)
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg p), mul_inv,
    show (Real.sqrt p)⁻¹ * ((Real.sqrt p)⁻¹ * (Real.sqrt m)⁻¹) * p =
      ((Real.sqrt p * Real.sqrt p)⁻¹ * p) * (Real.sqrt m)⁻¹ by ring, hs, inv_mul_cancel₀ hp0,
    one_mul]

/-- **Hecke recursion.** On functions `1`-periodic in `x`,
`T_p T_n = T_{pn} + 1_{p ∣ n} T_{n/p}`. -/
theorem heckeOp_heckeN {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : n ≠ 0) {F : ℝ → ℝ → ℂ}
    (hF : ∀ x y, F (x + 1) y = F x y) (x y : ℝ) :
    heckeOp p (heckeN n F) x y =
      heckeN (p * n) F x y + (if p ∣ n then heckeN (n / p) F x y else 0) := by
  set O : ℕ → ℕ → ℂ := fun a d => heckeOrbit F a d x y with hO
  set S₁ : ℂ := ∑ ad ∈ n.divisorsAntidiagonal, O (p * ad.1) ad.2 with hS₁
  set S₂ : ℂ := ∑ ad ∈ n.divisorsAntidiagonal with ¬ p ∣ ad.1, O ad.1 (p * ad.2) with hS₂
  set S₃ : ℂ := ∑ ad ∈ n.divisorsAntidiagonal with p ∣ ad.1, O (ad.1 / p) ad.2 with hS₃
  have h1 : heckeN n F (p * x) (p * y) = (((Real.sqrt n)⁻¹ : ℝ) : ℂ) * S₁ := by
    unfold heckeN
    congr 1
    exact sum_congr rfl fun ad _ => heckeOrbit_scale F p ad.1 ad.2 x y
  have h2 : ∑ b ∈ range p, heckeN n F ((x + b) / p) (y / p) =
      (((Real.sqrt n)⁻¹ : ℝ) : ℂ) * ((p : ℂ) * S₃ + S₂) := by
    unfold heckeN
    rw [← mul_sum, sum_comm]
    congr 1
    rw [hS₃, mul_sum, ← sum_filter_add_sum_filter_not _ (fun ad : ℕ × ℕ => p ∣ ad.1)]
    congr 1
    · refine sum_congr rfl fun ad had => ?_
      obtain ⟨had, a₁, ha₁⟩ := mem_filter.mp had
      have hd := (pos_of_mem_divisorsAntidiagonal had).2
      rw [hO, ha₁, Nat.mul_div_cancel_left _ hp.pos]
      exact heckeOrbit_residue_dvd hp.pos hd hF x y
    · refine sum_congr rfl fun ad had => ?_
      obtain ⟨had, hnd⟩ := mem_filter.mp had
      exact heckeOrbit_residue_coprime hp hnd (pos_of_mem_divisorsAntidiagonal had).2 hF x y
  have h3 : heckeN (p * n) F x y = (((Real.sqrt ((p * n : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) * (S₁ + S₂) := by
    unfold heckeN
    congr 1
    exact sum_divisorsAntidiagonal_mul_prime hp hn O
  have hγ : (((Real.sqrt p)⁻¹ : ℝ) : ℂ) * (((Real.sqrt n)⁻¹ : ℝ) : ℂ) =
      (((Real.sqrt ((p * n : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, sqrt_inv_mul_sqrt_inv]
  unfold heckeOp
  rw [h1, h2, h3]
  split_ifs with hpn
  · obtain ⟨m, rfl⟩ := hpn
    have hm : m ≠ 0 := fun h => hn (by rw [h, mul_zero])
    have h4 : heckeN (p * m / p) F x y = (((Real.sqrt m)⁻¹ : ℝ) : ℂ) * S₃ := by
      rw [Nat.mul_div_cancel_left _ hp.pos, hS₃, sum_filter_dvd_divisorsAntidiagonal hp.pos hm O]
      rfl
    have hδ : (((Real.sqrt p)⁻¹ : ℝ) : ℂ) * (((Real.sqrt ((p * m : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) * (p : ℂ) =
        (((Real.sqrt m)⁻¹ : ℝ) : ℂ) := by
      have h := congrArg (fun r : ℝ => (r : ℂ)) (sqrt_inv_mul_sqrt_inv_mul_self hp.pos m)
      push_cast at h ⊢
      exact h
    rw [h4]
    linear_combination (S₁ + S₂) * hγ + S₃ * hδ
  · have h0 : S₃ = 0 := sum_filter_dvd_eq_zero hpn O
    rw [h0]
    linear_combination (S₁ + S₂) * hγ

/-! ### The eigen-equation -/

/-- **Every Hecke operator is diagonal on the Eisenstein line model.**
`T_n E_u = W_u(n) E_u` for every `n ≥ 1` and every parameter `u`. -/
theorem heckeN_cuspLeg (u : ℂ) {n : ℕ} (hn : n ≠ 0) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    heckeN n (fun x y => d4BMCompletedEisensteinCuspLeg .scalar u x y) x y =
      whittakerCoeff u n * d4BMCompletedEisensteinCuspLeg .scalar u x y := by
  induction n using Nat.strong_induction_on generalizing x y with
  | _ n ih =>
    by_cases h1 : n = 1
    · subst h1
      rw [heckeN_one, ArithmeticCorrespondencePositivity.whittakerCoeff_one, one_mul]
    have hp : n.minFac.Prime := Nat.minFac_prime h1
    set p := n.minFac with hpdef
    have hpn : p ∣ n := Nat.minFac_dvd n
    set m := n / p with hmdef
    have hnm : n = p * m := (Nat.mul_div_cancel' hpn).symm
    have hm : m ≠ 0 := fun h => hn (by rw [hnm, h, mul_zero])
    have hmlt : m < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) hp.one_lt
    have hper : ∀ x y, d4BMCompletedEisensteinCuspLeg .scalar u (x + 1) y =
        d4BMCompletedEisensteinCuspLeg .scalar u x y := fun x y => cuspLeg_add_one u x y
    have hrec := heckeOp_heckeN hp hm hper x y
    have hcongr : heckeOp p (heckeN m fun x y => d4BMCompletedEisensteinCuspLeg .scalar u x y) x y =
        heckeOp p (fun x y => whittakerCoeff u m * d4BMCompletedEisensteinCuspLeg .scalar u x y)
          x y :=
      heckeOp_congr_pos hp.pos (fun x y hy => ih m hmlt hm x hy) x hy
    rw [hcongr, RHTower.heckeOp_const_mul, heckeOp_cuspLeg hp u x hy] at hrec
    have hW := whittakerCoeff_hecke u hp hm
    rw [hnm]
    split_ifs at hrec hW with hpm
    · have hlt : m / p < n := lt_of_le_of_lt (Nat.div_le_self m p) hmlt
      have hne : m / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hpm)
        hp.pos).ne'
      rw [ih (m / p) hlt hne x hy] at hrec
      linear_combination -hrec - d4BMCompletedEisensteinCuspLeg .scalar u x y * hW
    · linear_combination -hrec - d4BMCompletedEisensteinCuspLeg .scalar u x y * hW

end

end GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates
