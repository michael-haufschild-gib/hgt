import GaloisForLFunctions.ConstituentTheoryOfTheZeros.TheWienerAlgebraOfAStrip
import GaloisForLFunctions.HTGeometry.PrimeTorusKroneckerDensity
import Mathlib.Analysis.CStarAlgebra.GelfandDuality

/-!
# Wiener's lemma on a strip

An element of the Wiener algebra `𝒲[σ₁, σ₂]` of a closed strip that is bounded below on the strip
is invertible in the algebra (`StripWiener.isUnit_of_le_norm_eval`): if `Σ c(q) q^s` converges
absolutely on the strip and is bounded below there, its inverse is again an absolutely convergent
expansion over the positive rationals (`exists_inverse_expansion`).

The proof is Gelfand's. A character `φ` gives the homomorphism `χ(q) = φ(δ_q)` of the positive
rationals into `ℂ^×` with `|χ(q)| ≤ max(q^σ₁, q^σ₂)`.

* **One real part for all scales** (`PosRat.exists_eq_mul_log`, `exists_exponent`): an additive
  function on the positive rationals that lies between `σ₁ log q` and `σ₂ log q` for `q ≥ 1` is
  `σ log q` with one `σ ∈ [σ₁, σ₂]`; so `|χ(q)| = q^σ`. The elements `q^b 2^{−a}` with logarithm in
  `[0, log 2)` carry `b` times the deviation.
* **Kronecker for the phases** (`PosRat.exists_height_approx`): a unimodular homomorphism of the
  positive rationals is approximated on every finite set by `q ↦ q^{it}`, from the density of the
  prime phases.
* So `φ(f)` is a limit of values `f(σ + it)` of `f` on the strip, and a character cannot vanish on
  an element that is bounded below.

No lower bound on a half-plane is needed: the function may have zeros on both sides of the strip.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.ConstituentTheoryOfTheZeros

namespace PosRat

/-! ### Additive functions on the positive rationals -/

/-- The logarithm of a scale. -/
def log (q : PosRat) : ℝ := Real.log q.toReal

theorem log_mul (q r : PosRat) : (q * r).log = q.log + r.log := by
  unfold log
  rw [toReal_mul, Real.log_mul q.toReal_pos.ne' r.toReal_pos.ne']

/-- The scale two. -/
def two : PosRat := ⟨2, by norm_num⟩

theorem toReal_two : two.toReal = 2 := by
  unfold toReal two
  norm_num

theorem log_two_pos : 0 < two.log := by
  unfold log
  rw [toReal_two]
  exact Real.log_pos (by norm_num)

theorem toReal_inv (q : PosRat) : (q⁻¹).toReal = (q.toReal)⁻¹ := Rat.cast_inv _

section Additive

variable {f : PosRat → ℝ} (hf : ∀ q r, f (q * r) = f q + f r)
include hf

theorem additive_one : f 1 = 0 := by
  have h := hf 1 1
  rw [mul_one] at h
  linarith

theorem additive_inv (q : PosRat) : f q⁻¹ = -f q := by
  have h := hf q q⁻¹
  rw [mul_inv_cancel, additive_one hf] at h
  linarith

theorem additive_pow (q : PosRat) (n : ℕ) : f (q ^ n) = n * f q := by
  induction n with
  | zero => rw [pow_zero, additive_one hf, Nat.cast_zero, zero_mul]
  | succ n ih =>
    rw [pow_succ, hf, ih]
    push_cast
    ring

theorem additive_zpow (q : PosRat) (n : ℤ) : f (q ^ n) = n * f q := by
  cases n with
  | ofNat k => rw [Int.ofNat_eq_natCast, zpow_natCast, additive_pow hf, Int.cast_natCast]
  | negSucc k =>
    rw [zpow_negSucc, additive_inv hf, additive_pow hf, Int.cast_negSucc]
    ring

/-- **An additive function between two multiples of the logarithm is one multiple.** If
`σ₁ log q ≤ f(q) ≤ σ₂ log q` for every `q ≥ 1`, then `f = σ log` with `σ₁ ≤ σ ≤ σ₂`. -/
theorem exists_eq_mul_log {σ₁ σ₂ : ℝ}
    (hb : ∀ q : PosRat, 0 ≤ q.log → σ₁ * q.log ≤ f q ∧ f q ≤ σ₂ * q.log) :
    ∃ σ : ℝ, σ₁ ≤ σ ∧ σ ≤ σ₂ ∧ ∀ q : PosRat, f q = σ * q.log := by
  have hL2 := log_two_pos
  obtain ⟨h1, h2⟩ := hb two hL2.le
  have hσ1 : σ₁ ≤ f two / two.log := by
    rw [le_div_iff₀ hL2]
    exact h1
  have hσ2 : f two / two.log ≤ σ₂ := by
    rw [div_le_iff₀ hL2]
    exact h2
  refine ⟨f two / two.log, hσ1, hσ2, fun q => ?_⟩
  set σ := f two / two.log with hσ
  have hf2 : f two = σ * two.log := by rw [hσ, div_mul_cancel₀ _ hL2.ne']
  have h12 : σ₁ ≤ σ₂ := hσ1.trans hσ2
  by_contra hne
  have hpos : 0 < |f q - σ * q.log| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨b, hb'⟩ := exists_nat_gt ((σ₂ - σ₁) * two.log / |f q - σ * q.log|)
  rw [div_lt_iff₀ hpos] at hb'
  -- the element `q^b 2^{−a}` with logarithm in `[0, log 2)`
  set a : ℤ := ⌊(b : ℝ) * q.log / two.log⌋ with ha
  have hLr : (q ^ (b : ℤ) * two ^ (-a)).log = b * q.log - a * two.log := by
    rw [log_mul, additive_zpow log_mul, additive_zpow log_mul]
    push_cast
    ring
  have hfr : f (q ^ (b : ℤ) * two ^ (-a)) = b * f q - a * f two := by
    rw [hf, additive_zpow hf, additive_zpow hf]
    push_cast
    ring
  have hfloor1 : (a : ℝ) ≤ (b : ℝ) * q.log / two.log := Int.floor_le _
  have hfloor2 : (b : ℝ) * q.log / two.log < a + 1 := Int.lt_floor_add_one _
  have hr0 : 0 ≤ (q ^ (b : ℤ) * two ^ (-a)).log := by
    rw [hLr]
    have := (le_div_iff₀ hL2).mp hfloor1
    linarith
  have hr1 : (q ^ (b : ℤ) * two ^ (-a)).log ≤ two.log := by
    rw [hLr]
    have := (div_lt_iff₀ hL2).mp hfloor2
    linarith
  obtain ⟨hlo, hhi⟩ := hb _ hr0
  set L := (q ^ (b : ℤ) * two ^ (-a)).log with hL
  -- `f(r) = b·Δ + σ log r`
  have hkey : f (q ^ (b : ℤ) * two ^ (-a)) = b * (f q - σ * q.log) + σ * L := by
    rw [hfr, hLr, hf2]
    ring
  have hub : (b : ℝ) * (f q - σ * q.log) ≤ (σ₂ - σ₁) * two.log := by
    have e1 : (b : ℝ) * (f q - σ * q.log) ≤ (σ₂ - σ) * L := by linarith
    have e2 : (σ₂ - σ) * L ≤ (σ₂ - σ₁) * L :=
      mul_le_mul_of_nonneg_right (by linarith) hr0
    have e3 : (σ₂ - σ₁) * L ≤ (σ₂ - σ₁) * two.log :=
      mul_le_mul_of_nonneg_left hr1 (sub_nonneg.mpr h12)
    linarith
  have hlb : -((σ₂ - σ₁) * two.log) ≤ (b : ℝ) * (f q - σ * q.log) := by
    have e1 : (σ₁ - σ) * L ≤ (b : ℝ) * (f q - σ * q.log) := by linarith
    have e2 : -((σ₂ - σ₁) * L) ≤ (σ₁ - σ) * L := by
      have := mul_le_mul_of_nonneg_right (show σ - σ₁ ≤ σ₂ - σ₁ by linarith) hr0
      linarith
    have e3 : (σ₂ - σ₁) * L ≤ (σ₂ - σ₁) * two.log :=
      mul_le_mul_of_nonneg_left hr1 (sub_nonneg.mpr h12)
    linarith
  have habs : (b : ℝ) * |f q - σ * q.log| ≤ (σ₂ - σ₁) * two.log := by
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    have h : |(b : ℝ) * (f q - σ * q.log)| ≤ (σ₂ - σ₁) * two.log := abs_le.mpr ⟨hlb, hub⟩
    rwa [abs_mul, abs_of_nonneg hb0] at h
  linarith

end Additive

/-! ### Unimodular homomorphisms and Kronecker's theorem -/

section Unimodular

variable {u v : PosRat → ℂ}

theorem unimodular_one (hu1 : ∀ q, ‖u q‖ = 1) (hum : ∀ q r, u (q * r) = u q * u r) : u 1 = 1 := by
  have h := hum 1 1
  rw [mul_one] at h
  have hne : u 1 ≠ 0 := fun h0 => by
    have := hu1 1
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  exact (mul_right_cancel₀ hne (by rw [one_mul]; exact h)).symm

theorem unimodular_inv (hu1 : ∀ q, ‖u q‖ = 1) (hum : ∀ q r, u (q * r) = u q * u r) (q : PosRat) :
    u q⁻¹ = (u q)⁻¹ := by
  have h := hum q q⁻¹
  rw [mul_inv_cancel, unimodular_one hu1 hum] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- The distance of two unimodular homomorphisms is subadditive. -/
theorem norm_sub_mul_le (hu1 : ∀ q, ‖u q‖ = 1) (hv1 : ∀ q, ‖v q‖ = 1)
    (hum : ∀ q r, u (q * r) = u q * u r) (hvm : ∀ q r, v (q * r) = v q * v r) (q r : PosRat) :
    ‖u (q * r) - v (q * r)‖ ≤ ‖u q - v q‖ + ‖u r - v r‖ := by
  have h : u (q * r) - v (q * r) = u q * (u r - v r) + (u q - v q) * v r := by
    rw [hum, hvm]
    ring
  rw [h]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, hu1, hv1, one_mul, mul_one, add_comm]

/-- The distance of two unimodular homomorphisms is invariant under inversion. -/
theorem norm_sub_inv (hu1 : ∀ q, ‖u q‖ = 1) (hv1 : ∀ q, ‖v q‖ = 1)
    (hum : ∀ q r, u (q * r) = u q * u r) (hvm : ∀ q r, v (q * r) = v q * v r) (q : PosRat) :
    ‖u q⁻¹ - v q⁻¹‖ = ‖u q - v q‖ := by
  have hu0 : u q ≠ 0 := fun h0 => by
    have := hu1 q
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have hv0 : v q ≠ 0 := fun h0 => by
    have := hv1 q
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have h : u q⁻¹ - v q⁻¹ = (v q - u q) * ((u q)⁻¹ * (v q)⁻¹) := by
    rw [unimodular_inv hu1 hum, unimodular_inv hv1 hvm]
    field_simp
  rw [h, norm_mul, norm_mul, norm_inv, norm_inv, hu1, hv1, inv_one, mul_one, mul_one,
    norm_sub_rev]

end Unimodular

/-- A positive natural number as a scale (the scale one for `0`). -/
def ofNat (n : ℕ) : PosRat := if h : 0 < n then ⟨(n : ℚ), by exact_mod_cast h⟩ else 1

theorem ofNat_val {n : ℕ} (h : 0 < n) : ((ofNat n : PosRat) : ℚ) = n := by
  unfold ofNat
  rw [dif_pos h]

theorem ofNat_mul {m n : ℕ} (hm : 0 < m) (hn : 0 < n) : ofNat (m * n) = ofNat m * ofNat n := by
  refine Subtype.ext ?_
  show ((ofNat (m * n) : PosRat) : ℚ) = ((ofNat m : PosRat) : ℚ) * ((ofNat n : PosRat) : ℚ)
  rw [ofNat_val (Nat.mul_pos hm hn), ofNat_val hm, ofNat_val hn, Nat.cast_mul]

theorem toReal_ofNat {n : ℕ} (h : 0 < n) : (ofNat n).toReal = n := by
  unfold toReal
  rw [ofNat_val h, Rat.cast_natCast]

/-- Every positive rational is a quotient of two positive naturals. -/
theorem eq_ofNat_div (q : PosRat) :
    q = ofNat (q : ℚ).num.toNat * (ofNat (q : ℚ).den)⁻¹ := by
  have hnum : 0 < (q : ℚ).num := Rat.num_pos.mpr q.2
  have hnat : 0 < (q : ℚ).num.toNat := by omega
  have hden : 0 < (q : ℚ).den := (q : ℚ).den_pos
  refine Subtype.ext ?_
  show (q : ℚ) = ((ofNat (q : ℚ).num.toNat : PosRat) : ℚ) * ((ofNat (q : ℚ).den : PosRat) : ℚ)⁻¹
  rw [ofNat_val hnat, ofNat_val hden, ← div_eq_mul_inv]
  have hcast : (((q : ℚ).num.toNat : ℕ) : ℚ) = ((q : ℚ).num : ℚ) := by
    have h := Int.toNat_of_nonneg hnum.le
    exact_mod_cast h
  rw [hcast, Rat.num_div_den]

/-- The homomorphism `q ↦ q^{it}` is unimodular. -/
theorem norm_cpow_mul_I (q : PosRat) (t : ℝ) : ‖q.cpow ((t : ℂ) * Complex.I)‖ = 1 := by
  rw [norm_cpow]
  simp

/-- Two unimodular homomorphisms within `δ` at the primes `≤ N` are within `nδ` at `n ≤ N`. -/
theorem norm_sub_ofNat_le {u v : PosRat → ℂ} (hu1 : ∀ q, ‖u q‖ = 1) (hv1 : ∀ q, ‖v q‖ = 1)
    (hum : ∀ q r, u (q * r) = u q * u r) (hvm : ∀ q r, v (q * r) = v q * v r) {N : ℕ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hp : ∀ p : ℕ, p.Prime → p ≤ N → ‖u (ofNat p) - v (ofNat p)‖ ≤ δ) (n : ℕ) :
    0 < n → n ≤ N → ‖u (ofNat n) - v (ofNat n)‖ ≤ n * δ := by
  induction n using induction_on_primes with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | one =>
    intro _ _
    have h1 : (ofNat 1 : PosRat) = 1 := Subtype.ext (by rw [ofNat_val one_pos]; rfl)
    rw [h1, unimodular_one hu1 hum, unimodular_one hv1 hvm, sub_self, norm_zero]
    positivity
  | prime_mul p a hpp ih =>
    intro hpos hle
    have ha : 0 < a := Nat.pos_of_mul_pos_left hpos |> fun _ => by
      rcases Nat.eq_zero_or_pos a with h | h
      · rw [h, mul_zero] at hpos
        exact absurd hpos (lt_irrefl 0)
      · exact h
    have hpN : p ≤ N := (Nat.le_mul_of_pos_right p ha).trans hle
    have haN : a ≤ N := (Nat.le_mul_of_pos_left a hpp.pos).trans hle
    rw [ofNat_mul hpp.pos ha]
    refine (norm_sub_mul_le hu1 hv1 hum hvm _ _).trans ?_
    have h1 := hp p hpp hpN
    have h2 := ih ha haN
    have h3 : (1 : ℝ) + a ≤ p * a := by
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
      have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
      nlinarith
    push_cast
    nlinarith

/-- **Kronecker's theorem on a finite set of scales.** A unimodular homomorphism of the positive
rationals is approximated on every finite set by `q ↦ q^{it}` for some real `t`. -/
theorem exists_height_approx {ω : PosRat → ℂ} (hω1 : ∀ q, ‖ω q‖ = 1)
    (hωm : ∀ q r, ω (q * r) = ω q * ω r) (T : Finset PosRat) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, ∀ q ∈ T, ‖q.cpow ((t : ℂ) * Complex.I) - ω q‖ ≤ ε := by
  -- all numerators and denominators of `T` are at most `N`
  set N : ℕ := T.sup (fun q => max (q : ℚ).num.toNat (q : ℚ).den) + 1 with hN
  have hNpos : (0 : ℝ) < N := by
    rw [hN]
    push_cast
    positivity
  set δ : ℝ := ε / (2 * N) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨t, ht⟩ := GaloisForLFunctions.primeTorus_cpow_dense N
    (fun p => Complex.arg (ω (ofNat ((p : Nat.Primes) : ℕ)))) hδpos
  refine ⟨t, fun q hq => ?_⟩
  have hum : ∀ q r : PosRat, (q * r).cpow ((t : ℂ) * Complex.I) =
      q.cpow ((t : ℂ) * Complex.I) * r.cpow ((t : ℂ) * Complex.I) := fun q r => cpow_mul q r _
  have hu1 : ∀ q : PosRat, ‖q.cpow ((t : ℂ) * Complex.I)‖ = 1 := fun q => norm_cpow_mul_I q t
  -- the primes `≤ N`
  have hp : ∀ p : ℕ, p.Prime → p ≤ N →
      ‖(ofNat p).cpow ((t : ℂ) * Complex.I) - ω (ofNat p)‖ ≤ δ := by
    intro p hpp hpN
    have h := ht ⟨⟨p, hpp⟩, (GaloisForLFunctions.mem_primesLE N ⟨p, hpp⟩).mpr hpN⟩
    have harg : Complex.exp ((Complex.arg (ω (ofNat p)) : ℝ) * Complex.I) = ω (ofNat p) := by
      have h' := Complex.norm_mul_exp_arg_mul_I (ω (ofNat p))
      rwa [hω1, Complex.ofReal_one, one_mul] at h'
    have hbase : (ofNat p).cpow ((t : ℂ) * Complex.I) = ((p : ℕ) : ℂ) ^ ((t : ℂ) * Complex.I) := by
      unfold cpow
      rw [toReal_ofNat hpp.pos, Complex.ofReal_natCast]
    rw [hbase]
    simp only at h
    rw [harg] at h
    exact h.le
  have hnat : ∀ n : ℕ, 0 < n → n ≤ N →
      ‖(ofNat n).cpow ((t : ℂ) * Complex.I) - ω (ofNat n)‖ ≤ N * δ := by
    intro n hn hnN
    refine (norm_sub_ofNat_le hu1 hω1 hum hωm hδpos.le hp n hn hnN).trans ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnN) hδpos.le
  have hsup : max (q : ℚ).num.toNat (q : ℚ).den ≤
      T.sup (fun q => max (q : ℚ).num.toNat (q : ℚ).den) :=
    Finset.le_sup (f := fun q : PosRat => max (q : ℚ).num.toNat (q : ℚ).den) hq
  have hnumN : (q : ℚ).num.toNat ≤ N := by
    have := le_max_left (q : ℚ).num.toNat (q : ℚ).den
    omega
  have hdenN : (q : ℚ).den ≤ N := by
    have := le_max_right (q : ℚ).num.toNat (q : ℚ).den
    omega
  have hnumpos : 0 < (q : ℚ).num.toNat := by
    have : 0 < (q : ℚ).num := Rat.num_pos.mpr q.2
    omega
  have hdenpos : 0 < (q : ℚ).den := (q : ℚ).den_pos
  rw [eq_ofNat_div q]
  refine (norm_sub_mul_le hu1 hω1 hum hωm _ _).trans ?_
  rw [norm_sub_inv hu1 hω1 hum hωm]
  have h1 := hnat _ hnumpos hnumN
  have h2 := hnat _ hdenpos hdenN
  have hNδ : (N : ℝ) * δ = ε / 2 := by
    rw [hδ]
    field_simp
  linarith

theorem cpow_add (q : PosRat) (s₁ s₂ : ℂ) : q.cpow (s₁ + s₂) = q.cpow s₁ * q.cpow s₂ := by
  unfold cpow
  exact Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr q.toReal_pos.ne')

theorem cpow_ofReal (q : PosRat) (σ : ℝ) : q.cpow (σ : ℂ) = ((q.toReal ^ σ : ℝ) : ℂ) := by
  unfold cpow
  rw [Complex.ofReal_cpow q.toReal_pos.le]

end PosRat

/-! ### Twists are uniform limits of vertical translates -/

/-- The twist of an expansion by a unimodular function converges absolutely where the expansion
does. -/
theorem WSummable.twist {σ₁ σ₂ : ℝ} {c : PosRat → ℂ} (hc : WSummable σ₁ σ₂ c) {ω : PosRat → ℂ}
    (hω1 : ∀ q, ‖ω q‖ = 1) : WSummable σ₁ σ₂ fun q => c q * ω q := by
  refine hc.congr fun q => ?_
  rw [norm_mul, hω1, mul_one]

/-- **A twist is a uniform limit of vertical translates.** For a unimodular homomorphism `ω` of the
positive rationals, the twisted expansion `Σ c(q) ω(q) q^s` is approximated uniformly on the closed
strip by a translate `s ↦ Σ c(q) q^{s + it}`: Kronecker on a finite set carrying all but a small
part of the weighted coefficients. -/
theorem exists_height_expansion_approx {σ₁ σ₂ : ℝ} {c : PosRat → ℂ} (hc : WSummable σ₁ σ₂ c)
    {ω : PosRat → ℂ} (hω1 : ∀ q, ‖ω q‖ = 1) (hωm : ∀ q r, ω (q * r) = ω q * ω r) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ t : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ‖expansion c (s + (t : ℂ) * Complex.I) - expansion (fun q => c q * ω q) s‖ ≤ ε := by
  -- the weighted coefficients and a finite set carrying all but `ε/4` of their sum
  set a : PosRat → ℝ := fun q => ‖c q‖ * stripWeight σ₁ σ₂ q with ha
  have hasum : Summable a := hc
  have ha0 : ∀ q, 0 ≤ a q := fun q =>
    mul_nonneg (norm_nonneg _) (stripWeight_pos σ₁ σ₂ q).le
  set S : ℝ := ∑' q, a q with hS
  have hS0 : 0 ≤ S := tsum_nonneg ha0
  have htend : Tendsto (fun T : Finset PosRat => ∑ q ∈ T, a q) atTop (𝓝 S) := hasum.hasSum
  obtain ⟨T, hT⟩ : ∃ T : Finset PosRat, S - ε / 4 < ∑ q ∈ T, a q :=
    (htend.eventually (lt_mem_nhds (show S - ε / 4 < S by linarith))).exists
  have hTle : ∑ q ∈ T, a q ≤ S := Summable.sum_le_tsum T (fun q _ => ha0 q) hasum
  -- a height at which `q^{it}` follows the phases on `T`
  set ε' : ℝ := ε / (2 * (S + 1)) with hε'
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨t, ht⟩ := PosRat.exists_height_approx hω1 hωm T hε'pos
  refine ⟨t, fun s h₁ h₂ => ?_⟩
  have hre : (s + (t : ℂ) * Complex.I).re = s.re := by simp
  have he1 : HasSum (fun q => c q * q.cpow (s + (t : ℂ) * Complex.I))
      (expansion c (s + (t : ℂ) * Complex.I)) :=
    (hc.summable_term (by rw [hre]; exact h₁) (by rw [hre]; exact h₂)).hasSum
  have he2 : HasSum (fun q => c q * ω q * q.cpow s) (expansion (fun q => c q * ω q) s) :=
    ((hc.twist hω1).summable_term h₁ h₂).hasSum
  have hterm : ∀ q, ‖c q * q.cpow (s + (t : ℂ) * Complex.I) - c q * ω q * q.cpow s‖ ≤
      ε' * (if q ∈ T then a q else 0) + 2 * (a q - if q ∈ T then a q else 0) := by
    intro q
    have hnorm : ‖c q * q.cpow (s + (t : ℂ) * Complex.I) - c q * ω q * q.cpow s‖ =
        ‖c q‖ * q.toReal ^ s.re * ‖q.cpow ((t : ℂ) * Complex.I) - ω q‖ := by
      rw [PosRat.cpow_add, show c q * (q.cpow s * q.cpow ((t : ℂ) * Complex.I)) -
        c q * ω q * q.cpow s = c q * q.cpow s * (q.cpow ((t : ℂ) * Complex.I) - ω q) by ring,
        norm_mul, norm_mul, PosRat.norm_cpow]
    have hw : ‖c q‖ * q.toReal ^ s.re ≤ a q :=
      mul_le_mul_of_nonneg_left (rpow_le_stripWeight h₁ h₂ q) (norm_nonneg _)
    rw [hnorm]
    by_cases hq : q ∈ T
    · rw [if_pos hq, sub_self, mul_zero, add_zero, mul_comm ε']
      exact mul_le_mul hw (ht q hq) (norm_nonneg _) (ha0 q)
    · rw [if_neg hq, mul_zero, zero_add, sub_zero, mul_comm 2]
      have h2' : ‖q.cpow ((t : ℂ) * Complex.I) - ω q‖ ≤ 2 := by
        refine (norm_sub_le _ _).trans ?_
        rw [PosRat.norm_cpow_mul_I, hω1]
        norm_num
      exact mul_le_mul hw h2' (norm_nonneg _) (ha0 q)
  have hind : HasSum (fun q => if q ∈ T then a q else 0) (∑ q ∈ T, a q) := by
    have h : HasSum (fun q => if q ∈ T then a q else 0)
        (∑ q ∈ T, if q ∈ T then a q else 0) :=
      hasSum_sum_of_ne_finset_zero fun q hq => if_neg hq
    rwa [Finset.sum_congr rfl fun q hq => if_pos hq] at h
  have hmaj : HasSum (fun q => ε' * (if q ∈ T then a q else 0) +
      2 * (a q - if q ∈ T then a q else 0))
      (ε' * ∑ q ∈ T, a q + 2 * (S - ∑ q ∈ T, a q)) :=
    (hind.mul_left ε').add ((hasum.hasSum.sub hind).mul_left 2)
  have hbound := (he1.sub he2).norm_le_of_bounded hmaj hterm
  have hεS : ε' * S < ε / 2 := by
    rw [hε', div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have hεT : ε' * ∑ q ∈ T, a q ≤ ε' * S := mul_le_mul_of_nonneg_left hTle hε'pos.le
  linarith

/-! ### Characters of the Wiener algebra of a strip -/

namespace StripWiener

variable {σ₁ σ₂ : ℝ} [hσ : Fact (σ₁ ≤ σ₂)]

/-- The value of a character on the point mass at `q`. -/
def charVal (φ : WeakDual.characterSpace ℂ (StripWiener σ₁ σ₂)) (q : PosRat) : ℂ :=
  φ (pointMass q)

variable (φ : WeakDual.characterSpace ℂ (StripWiener σ₁ σ₂))

theorem charVal_one : charVal φ 1 = 1 := by
  unfold charVal
  rw [pointMass_one, map_one]

theorem charVal_mul (q r : PosRat) : charVal φ (q * r) = charVal φ q * charVal φ r := by
  unfold charVal
  rw [← pointMass_mul, map_mul]

theorem charVal_ne_zero (q : PosRat) : charVal φ q ≠ 0 := fun h => by
  have h1 := charVal_mul φ q q⁻¹
  rw [mul_inv_cancel, charVal_one, h, zero_mul] at h1
  exact one_ne_zero h1

/-- The spectral bound: `|χ(q)| ≤ ‖δ_q‖`. -/
theorem norm_charVal_le (q : PosRat) : ‖charVal φ q‖ ≤ stripWeight σ₁ σ₂ q := by
  rw [← norm_pointMass (σ₁ := σ₁) (σ₂ := σ₂) q]
  exact spectrum.norm_le_norm_of_mem (AlgHom.apply_mem_spectrum φ _)

/-- **A character has one real part**: `|χ(q)| = q^σ` for all scales, with `σ₁ ≤ σ ≤ σ₂`. -/
theorem exists_exponent :
    ∃ σ : ℝ, σ₁ ≤ σ ∧ σ ≤ σ₂ ∧ ∀ q : PosRat, ‖charVal φ q‖ = q.toReal ^ σ := by
  have hpos : ∀ q : PosRat, 0 < ‖charVal φ q‖ := fun q => norm_pos_iff.mpr (charVal_ne_zero φ q)
  have hadd : ∀ q r : PosRat, Real.log ‖charVal φ (q * r)‖ =
      Real.log ‖charVal φ q‖ + Real.log ‖charVal φ r‖ := fun q r => by
    rw [charVal_mul, norm_mul, Real.log_mul (hpos q).ne' (hpos r).ne']
  have hupper : ∀ q : PosRat, 0 ≤ q.log → Real.log ‖charVal φ q‖ ≤ σ₂ * q.log := by
    intro q hq
    have hq1 : 1 ≤ q.toReal := by
      by_contra hlt
      have := Real.log_neg q.toReal_pos (not_le.mp hlt)
      exact absurd hq (not_le.mpr this)
    have hw : stripWeight σ₁ σ₂ q ≤ q.toReal ^ σ₂ :=
      max_le (Real.rpow_le_rpow_of_exponent_le hq1 hσ.out) le_rfl
    have h := Real.log_le_log (hpos q) ((norm_charVal_le φ q).trans hw)
    rwa [Real.log_rpow q.toReal_pos] at h
  have hlower : ∀ q : PosRat, 0 ≤ q.log → σ₁ * q.log ≤ Real.log ‖charVal φ q‖ := by
    intro q hq
    have hq1 : 1 ≤ q.toReal := by
      by_contra hlt
      have := Real.log_neg q.toReal_pos (not_le.mp hlt)
      exact absurd hq (not_le.mpr this)
    have hinv0 : 0 < (q.toReal)⁻¹ := inv_pos.mpr q.toReal_pos
    have hinv1 : (q.toReal)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq1
    have hw : stripWeight σ₁ σ₂ q⁻¹ ≤ (q.toReal)⁻¹ ^ σ₁ := by
      unfold stripWeight
      rw [PosRat.toReal_inv]
      exact max_le le_rfl (Real.rpow_le_rpow_of_exponent_ge hinv0 hinv1 hσ.out)
    have h := Real.log_le_log (hpos q⁻¹) ((norm_charVal_le φ q⁻¹).trans hw)
    have hinv : Real.log ‖charVal φ q⁻¹‖ = -Real.log ‖charVal φ q‖ :=
      PosRat.additive_inv (f := fun q => Real.log ‖charVal φ q‖) hadd q
    rw [hinv, Real.log_rpow hinv0, Real.log_inv] at h
    have hq' : q.log = Real.log q.toReal := rfl
    rw [hq']
    linarith
  obtain ⟨σ, h1, h2, h⟩ := PosRat.exists_eq_mul_log (f := fun q => Real.log ‖charVal φ q‖) hadd
    fun q hq => ⟨hlower q hq, hupper q hq⟩
  refine ⟨σ, h1, h2, fun q => ?_⟩
  rw [← Real.exp_log (hpos q), h q, Real.rpow_def_of_pos q.toReal_pos]
  congr 1
  exact mul_comm _ _

/-- A character applied to `f` is the sum of the coefficients against its values. -/
theorem hasSum_charVal (f : StripWiener σ₁ σ₂) :
    HasSum (fun q => f.coeff q * charVal φ q) (φ f) := by
  have h := (hasSum_pointMass f).map φ (map_continuous φ)
  refine h.congr_fun fun q => ?_
  simp only [Function.comp_apply, map_smul, smul_eq_mul]
  rfl

/-- **The form of a character**: `χ(q) = q^σ ω(q)` with `σ₁ ≤ σ ≤ σ₂` and `ω` a unimodular
homomorphism of the positive rationals. -/
theorem exists_exponent_phase :
    ∃ (σ : ℝ) (ω : PosRat → ℂ), σ₁ ≤ σ ∧ σ ≤ σ₂ ∧ (∀ q, ‖ω q‖ = 1) ∧
      (∀ q r, ω (q * r) = ω q * ω r) ∧
      ∀ q, charVal φ q = ((q.toReal ^ σ : ℝ) : ℂ) * ω q := by
  obtain ⟨σ, h1, h2, hmod⟩ := exists_exponent φ
  have hrne : ∀ q : PosRat, ((q.toReal ^ σ : ℝ) : ℂ) ≠ 0 := fun q =>
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos q.toReal_pos _).ne'
  refine ⟨σ, fun q => charVal φ q / ((q.toReal ^ σ : ℝ) : ℂ), h1, h2, fun q => ?_, fun q r => ?_,
    fun q => ?_⟩
  · beta_reduce
    rw [norm_div, hmod, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg q.toReal_pos.le _),
      div_self (Real.rpow_pos_of_pos q.toReal_pos _).ne']
  · beta_reduce
    rw [charVal_mul, PosRat.toReal_mul, Real.mul_rpow q.toReal_pos.le r.toReal_pos.le,
      Complex.ofReal_mul]
    field_simp [hrne q, hrne r]
  · beta_reduce
    rw [mul_div_cancel₀ _ (hrne q)]

/-- **A character is the value of a twist at a real point of the strip.** -/
theorem exists_apply_eq_expansion_twist :
    ∃ (σ : ℝ) (ω : PosRat → ℂ), σ₁ ≤ σ ∧ σ ≤ σ₂ ∧ (∀ q, ‖ω q‖ = 1) ∧
      (∀ q r, ω (q * r) = ω q * ω r) ∧
      ∀ f : StripWiener σ₁ σ₂, φ f = expansion (fun q => f.coeff q * ω q) (σ : ℂ) := by
  obtain ⟨σ, ω, h1, h2, hω1, hωm, hχ⟩ := exists_exponent_phase φ
  refine ⟨σ, ω, h1, h2, hω1, hωm, fun f => ?_⟩
  rw [← (hasSum_charVal φ f).tsum_eq]
  unfold expansion
  refine tsum_congr fun q => ?_
  rw [hχ, PosRat.cpow_ofReal]
  ring

/-- **Wiener's lemma on a strip.** An element of `𝒲[σ₁, σ₂]` that is bounded below on the strip is
invertible: a character is the value of a twist, a twist is a uniform limit of translates, and the
translates are bounded below. -/
theorem isUnit_of_le_norm_eval (f : StripWiener σ₁ σ₂) {δ : ℝ} (hδ : 0 < δ)
    (hf : ∀ s, δ ≤ ‖f.eval s‖) : IsUnit f := by
  by_contra hunit
  obtain ⟨φ, hφ⟩ := WeakDual.CharacterSpace.exists_apply_eq_zero hunit
  obtain ⟨σ, ω, h1, h2, hω1, hωm, hval⟩ := exists_apply_eq_expansion_twist φ
  obtain ⟨t, ht⟩ := exists_height_expansion_approx f.wsummable_coeff hω1 hωm (half_pos hδ)
  have hre : ((σ : ℂ)).re = σ := Complex.ofReal_re σ
  have hmem : σ₁ ≤ ((σ : ℂ) + (t : ℂ) * Complex.I).re ∧
      ((σ : ℂ) + (t : ℂ) * Complex.I).re ≤ σ₂ := by
    have : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
    rw [this]
    exact ⟨h1, h2⟩
  have h := ht (σ : ℂ) (by rw [hre]; exact h1) (by rw [hre]; exact h2)
  rw [← hval f, hφ, sub_zero, ← f.eval_eq ⟨_, hmem⟩] at h
  linarith [hf ⟨_, hmem⟩]

end StripWiener

/-! ### Inverse expansions -/

/-- **The inverse of an expansion that is bounded below on a strip is an expansion.** If
`Σ c(q) q^s` converges absolutely on the closed strip `σ₁ ≤ Re s ≤ σ₂` and is bounded below
there, there is `d` with `Σ ‖d(q)‖ max(q^σ₁, q^σ₂) < ∞` and `(Σ c(q) q^s)(Σ d(q) q^s) = 1` on the
strip. -/
theorem exists_inverse_expansion {σ₁ σ₂ : ℝ} (h12 : σ₁ ≤ σ₂) {c : PosRat → ℂ}
    (hc : WSummable σ₁ σ₂ c) {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → δ ≤ ‖expansion c s‖) :
    ∃ d : PosRat → ℂ, WSummable σ₁ σ₂ d ∧
      ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → expansion c s * expansion d s = 1 := by
  haveI : Fact (σ₁ ≤ σ₂) := ⟨h12⟩
  have hunit : IsUnit (StripWiener.ofCoeff c hc) :=
    StripWiener.isUnit_of_le_norm_eval _ hδ fun s => h s.1 s.2.1 s.2.2
  obtain ⟨g, hg⟩ := hunit.exists_right_inv
  refine ⟨g.coeff, g.wsummable_coeff, fun s h₁ h₂ => ?_⟩
  have hs := congrArg (fun F : StripWiener σ₁ σ₂ => F.eval ⟨s, h₁, h₂⟩) hg
  simp only [StripWiener.eval_mul, StripWiener.eval_one, StripWiener.eval_ofCoeff] at hs
  rw [← g.eval_eq ⟨s, h₁, h₂⟩]
  exact hs

end GaloisForLFunctions.ConstituentTheoryOfTheZeros
