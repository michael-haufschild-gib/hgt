import GaloisForLFunctions.RHTower.CharacterProductZeroPlanting
import GaloisForLFunctions.HTGeometry.DirichletExpMultiplicativeTwist

/-!
# A periodic Dirichlet exponential carries a single character

**Theorem** (`periodic_exp_single_character`).  Let `ℓ : ℕ → ℂ` with `ℓ(0) = ℓ(1) = 0` and
`Σ |ℓ(n)| n^{−σ} < ∞` for every `σ > 1`.  Suppose the Dirichlet exponential `a = exp⋆ ℓ` is
`N`-periodic, `a(n) = Ψ(n mod N)`.  Then exactly one Dirichlet character `χ₁` mod `N` carries `Ψ`:
for every other `χ` and every `N`-smooth `m`, the section
`c_χ(m) = φ(N)^{−1} Σ_b χ(b⁻¹) Ψ(m b)` vanishes.  Equivalently, `Ψ(m r) = c_{χ₁}(m) χ₁(r)` for
`m` `N`-smooth and `r` coprime to `N`, and `Σ a(n) n^{−s} = A(s) L(s, χ₁)`.

This is the Saias–Weingartner rigidity in Bohr-lift form, with the zero-freeness taken on the lift
rather than on the line.

**Proof.**  Suppose two characters `χ₂ ≠ χ₃` have nonzero sections.  A nonzero Dirichlet series is
nonzero at all large real arguments, so for some real `s₀ > 1` both `C(χ) = Σ_m c_χ(m) m^{−s₀}`
(over `N`-smooth `m`) are nonzero.  `exists_charProduct_zero` gives `σ > 1`, a finite set `S` of
primes coprime to `N`, and `|z_p| ≤ p^{−σ}` with `Σ_χ C(χ) Π_{p∈S}(1 − χ(p) z_p)^{−1} = 0`.  Let
`f` be the completely multiplicative function with `f(p) = p^{−s₀}` for `p | N`, `f(p) = z_p` for
`p ∈ S`, and `f(p) = 0` otherwise.  By the character decomposition and the Euler product,
`Σ_n a(n) f(n) = Σ_χ C(χ) Π_{p∈S}(1 − χ(p) z_p)^{−1} = 0`.  This contradicts
`Σ_n a(n) f(n) = exp(Σ_n ℓ(n) f(n)) ≠ 0` (`tsum_dirichletExp_twist_ne_zero`).
-/

open Complex Filter Topology

namespace RHTower

namespace CharacterZeroPlanting

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Completely multiplicative functions from prime values -/

/-- The completely multiplicative function with prescribed values at the primes. -/
def primeValueTwist (v : ℕ → ℂ) : ℕ →*₀ ℂ where
  toFun n := if n = 0 then 0 else n.factorization.prod fun p k => v p ^ k
  map_zero' := if_pos rfl
  map_one' := by simp
  map_mul' m n := by
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    simp only [if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn]
    rw [Nat.factorization_mul hm hn,
      Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]

theorem primeValueTwist_prime (v : ℕ → ℂ) {p : ℕ} (hp : p.Prime) : primeValueTwist v p = v p := by
  show (if p = 0 then 0 else p.factorization.prod fun q k => v q ^ k) = v p
  rw [if_neg hp.ne_zero, hp.factorization]
  simp

/-- `|f(n)| ≤ n^{−σ}` when `|f(p)| ≤ p^{−σ}` at every prime. -/
theorem norm_primeValueTwist_le {v : ℕ → ℂ} {σ : ℝ} (hv : ∀ p, p.Prime → ‖v p‖ ≤ (p : ℝ) ^ (-σ))
    {n : ℕ} (hn : n ≠ 0) : ‖primeValueTwist v n‖ ≤ (n : ℝ) ^ (-σ) := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one => simp
  | prime p hp => rw [primeValueTwist_prime v hp]; exact hv p hp
  | mul a b ha hb =>
    have ha0 : a ≠ 0 := left_ne_zero_of_mul hn
    have hb0 : b ≠ 0 := right_ne_zero_of_mul hn
    rw [map_mul, norm_mul, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    exact mul_le_mul (ha ha0) (hb hb0) (norm_nonneg _) (by positivity)

/-- On `P`-factored numbers, prime values `p^{−s}` give `n^{−s}`. -/
theorem primeValueTwist_eq_cpow {v : ℕ → ℂ} {P : Finset ℕ} {s : ℂ}
    (hv : ∀ p, p.Prime → p ∈ P → v p = (p : ℂ) ^ (-s)) {n : ℕ} (hn : n ∈ Nat.factoredNumbers P) :
    primeValueTwist v n = (n : ℂ) ^ (-s) := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl (Nat.ne_zero_of_mem_factoredNumbers hn)
  | one => simp
  | prime p hp =>
    rw [primeValueTwist_prime v hp]
    refine hv p hp ((Nat.mem_factoredNumbers.mp hn).2 p ?_)
    rw [Nat.primeFactorsList_prime hp]; exact List.mem_singleton_self p
  | mul a b ha hb =>
    rw [map_mul, ha (Nat.mem_factoredNumbers_of_dvd hn (dvd_mul_right a b)),
      hb (Nat.mem_factoredNumbers_of_dvd hn (dvd_mul_left b a)), Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow]

/-! ### Nonvanishing of Dirichlet series at large real arguments -/

theorem eventually_LSeries_ne_zero {f : ℕ → ℂ} (hf0 : f 0 = 0)
    (habs : LSeries.abscissaOfAbsConv f < ⊤) (hne : ∃ n, f n ≠ 0) :
    ∀ᶠ x : ℝ in atTop, LSeries f x ≠ 0 := by
  classical
  have hex : ∃ n, f (n + 1) ≠ 0 := by
    obtain ⟨n, hn⟩ := hne
    rcases n with _ | n
    · exact absurd hf0 hn
    · exact ⟨n, hn⟩
  set n₀ := Nat.find hex with hn₀
  have hlow : ∀ m ≤ n₀, f m = 0 := by
    intro m hm
    rcases m with _ | k
    · exact hf0
    · by_contra h
      have := Nat.find_min hex (show k < n₀ by omega)
      exact this h
  have ht := LSeries.tendsto_cpow_mul_atTop hlow habs
  have hlim : f (n₀ + 1) ≠ 0 := Nat.find_spec hex
  filter_upwards [ht.eventually_ne hlim] with x hx
  intro h0
  rw [h0, mul_zero] at hx
  exact hx rfl

/-! ### Sections as Dirichlet series -/

/-- The `N`-smooth section of `c_χ`. -/
def charSmoothCoeff [NeZero N] (Ψ : ZMod N → ℂ) (χ : DirichletCharacter ℂ N) (m : ℕ) : ℂ :=
  open Classical in
  if m ∈ Nat.factoredNumbers N.primeFactors then charSection Ψ χ m else 0

theorem norm_charSection_le [NeZero N] (Ψ : ZMod N → ℂ) (χ : DirichletCharacter ℂ N) (m : ℕ) :
    ‖charSection Ψ χ m‖ ≤ ∑ a, ‖Ψ a‖ := by
  have htot : (0 : ℝ) < N.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  unfold charSection
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hb : ∀ b : (ZMod N)ˣ, ‖χ ((b : ZMod N)⁻¹) * Ψ ((m : ZMod N) * b)‖ ≤ ∑ a, ‖Ψ a‖ := by
    intro b
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)).trans ?_
    exact Finset.single_le_sum (f := fun a => ‖Ψ a‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ _)
  calc ((N.totient : ℝ))⁻¹ * ‖∑ b : (ZMod N)ˣ, χ ((b : ZMod N)⁻¹) * Ψ ((m : ZMod N) * b)‖
      ≤ ((N.totient : ℝ))⁻¹ * ∑ _b : (ZMod N)ˣ, ∑ a, ‖Ψ a‖ :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => hb b))
          (by positivity)
    _ = ∑ a, ‖Ψ a‖ := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ZMod.card_units_eq_totient]
        field_simp

theorem lseriesSummable_of_bounded {f : ℕ → ℂ} {B : ℝ} (hf : ∀ n, ‖f n‖ ≤ B) {s : ℝ} (hs : 1 < s) :
    LSeriesSummable f s :=
  LSeriesSummable_of_le_const_mul_rpow (x := 1) (by simpa using hs)
    ⟨B, fun n _ => by simpa using hf n⟩

theorem abscissa_charSmoothCoeff_lt_top [NeZero N] (Ψ : ZMod N → ℂ) (χ : DirichletCharacter ℂ N) :
    LSeries.abscissaOfAbsConv (charSmoothCoeff Ψ χ) < ⊤ := by
  have hb : ∀ n, ‖charSmoothCoeff Ψ χ n‖ ≤ ∑ a, ‖Ψ a‖ := by
    intro n
    unfold charSmoothCoeff
    split_ifs
    · exact norm_charSection_le Ψ χ n
    · rw [norm_zero]; exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have := lseriesSummable_of_bounded hb (s := 2) (by norm_num)
  exact (this.abscissaOfAbsConv_le).trans_lt (by exact_mod_cast EReal.coe_lt_top 2)

/-! ### Twisted characters and their Euler products -/

/-- The completely multiplicative function `n ↦ χ(n) f(n)`. -/
def charTwist [NeZero N] (χ : DirichletCharacter ℂ N) (f : ℕ →*₀ ℂ) : ℕ →* ℂ where
  toFun n := χ n * f n
  map_one' := by simp
  map_mul' m n := by
    simp only [Nat.cast_mul, map_mul]
    ring

/-- **The Euler product of a twisted character.**  If `χ(p) v(p) = 0` at every prime outside
the finite set `S`, then `Σ_n χ(n) f(n) = Π_{p ∈ S} (1 − χ(p) v(p))^{−1}`. -/
theorem LSeries_charTwist_eq_prod [NeZero N] (χ : DirichletCharacter ℂ N) (v : ℕ → ℂ)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hv : ∀ p, p.Prime → p ∉ S → χ p * v p = 0)
    (hsum : Summable fun n : ℕ => χ n * primeValueTwist v n) :
    LSeries (fun n : ℕ => χ n * primeValueTwist v n) 0 = ∏ p ∈ S, (1 - χ p * v p)⁻¹ := by
  classical
  have hE := EulerProduct.prod_filter_prime_geometric_eq_tsum_factoredNumbers
    (f := charTwist χ (primeValueTwist v)) hsum S
  have hfilter : S.filter Nat.Prime = S := Finset.filter_true_of_mem hS
  have hgp : ∀ p, p.Prime → charTwist χ (primeValueTwist v) p = χ p * v p := fun p hp => by
    show χ p * primeValueTwist v p = _
    rw [primeValueTwist_prime v hp]
  rw [hfilter, Finset.prod_congr rfl fun p hp => by rw [hgp p (hS p hp)]] at hE
  rw [hE]
  have hsupp : Function.support (fun n => charTwist χ (primeValueTwist v) n) ⊆ Nat.factoredNumbers S := by
    intro n hn
    have hn' : χ n * primeValueTwist v n ≠ 0 := hn
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hn' (by simp)
    refine Nat.mem_factoredNumbers.mpr ⟨hn0, fun p hp => ?_⟩
    have hpp : p.Prime := Nat.prime_of_mem_primeFactorsList hp
    have hdvd : p ∣ n := Nat.dvd_of_mem_primeFactorsList hp
    obtain ⟨k, rfl⟩ := hdvd
    by_contra hpS
    apply hn'
    have hmul : χ (p * k : ℕ) * primeValueTwist v (p * k) =
        (χ p * primeValueTwist v p) * (χ k * primeValueTwist v k) := by
      simp only [Nat.cast_mul, map_mul]; ring
    rw [hmul, primeValueTwist_prime v hpp, hv p hpp hpS, zero_mul]
  rw [tsum_subtype_eq_of_support_subset hsupp]
  unfold LSeries
  refine tsum_congr fun n => ?_
  rw [LSeries.term_def]
  split_ifs with h
  · subst h; simp [charTwist]
  · rw [Complex.cpow_zero, div_one]; rfl

/-! ### The theorem -/

theorem summable_of_norm_le_rpow {g : ℕ → ℂ} {σ : ℝ} (hσ : 1 < σ)
    (hg : ∀ n, n ≠ 0 → ‖g n‖ ≤ (n : ℝ) ^ (-σ)) : LSeriesSummable g 0 :=
  LSeriesSummable_of_le_const_mul_rpow (x := 1 - σ) (by simp; linarith)
    ⟨1, fun n hn => by rw [one_mul, show 1 - σ - 1 = -σ by ring]; exact hg n hn⟩

/-- **A periodic Dirichlet exponential carries a single character.** -/
theorem periodic_exp_single_character [NeZero N] {ℓ : ℕ → ℂ} (hℓ0 : ℓ 0 = 0) (hℓ1 : ℓ 1 = 0)
    (hℓ : ∀ σ : ℝ, 1 < σ → LSeriesSummable ℓ σ) {Ψ : ZMod N → ℂ}
    (hΨ : ∀ n : ℕ, n ≠ 0 → dirichletExp ℓ n = Ψ n) :
    ∃ χ₁ : DirichletCharacter ℂ N, ∀ χ, χ ≠ χ₁ → ∀ m, charSmoothCoeff Ψ χ m = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨χ₂, -, m₂, hm₂⟩ := hcon 1
  obtain ⟨χ₃, h32, m₃, hm₃⟩ := hcon χ₂
  have hsc0 : ∀ χ, charSmoothCoeff Ψ χ 0 = 0 := fun χ => by
    unfold charSmoothCoeff
    rw [if_neg fun h => Nat.ne_zero_of_mem_factoredNumbers h rfl]
  have hev2 := eventually_LSeries_ne_zero (hsc0 χ₂) (abscissa_charSmoothCoeff_lt_top Ψ χ₂) ⟨m₂, hm₂⟩
  have hev3 := eventually_LSeries_ne_zero (hsc0 χ₃) (abscissa_charSmoothCoeff_lt_top Ψ χ₃) ⟨m₃, hm₃⟩
  obtain ⟨s₀, ⟨hs2, hs3⟩, hs₀⟩ := ((hev2.and hev3).and (eventually_gt_atTop (2 : ℝ))).exists
  set C : DirichletCharacter ℂ N → ℂ := fun χ => LSeries (charSmoothCoeff Ψ χ) s₀ with hC
  obtain ⟨σ, hσ, S, hS, z, hz, hzero⟩ :=
    exists_charProduct_zero (C := C) (Ne.symm h32) hs2 hs3
  -- the twist
  set v : ℕ → ℂ := fun p => if p ∈ N.primeFactors then (p : ℂ) ^ (-(s₀ : ℂ))
    else if p ∈ S then z p else 0 with hvdef
  set f : ℕ →*₀ ℂ := primeValueTwist v with hf
  set σ' : ℝ := min σ s₀ with hσ'def
  have hσ' : 1 < σ' := lt_min hσ (by linarith)
  have hSN : ∀ p ∈ S, p ∉ N.primeFactors := by
    intro p hp hpN
    have hcop := (ZMod.isUnit_iff_coprime p N).mp (hS p hp).2
    exact (Nat.Prime.coprime_iff_not_dvd (hS p hp).1).mp hcop (Nat.dvd_of_mem_primeFactors hpN)
  have hv_norm : ∀ p, p.Prime → ‖v p‖ ≤ (p : ℝ) ^ (-σ') := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    simp only [hvdef]
    split_ifs with h1 h2
    · rw [Complex.norm_natCast_cpow_of_pos hp.pos]
      simp only [neg_re, ofReal_re]
      exact Real.rpow_le_rpow_of_exponent_le hp1 (by simp [hσ'def])
    · exact (hz p h2).trans (Real.rpow_le_rpow_of_exponent_le hp1 (by simp [hσ'def]))
    · simp; positivity
  have hf_norm : ∀ n, n ≠ 0 → ‖f n‖ ≤ (n : ℝ) ^ (-σ') := fun n hn =>
    norm_primeValueTwist_le hv_norm hn
  -- the twisted sum does not vanish
  have hsumℓ : LSeriesSummable (fun n => ℓ n * f n) 0 := by
    refine Summable.of_norm_bounded (summable_norm_iff.mpr (hℓ σ' hσ')) fun n => ?_
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    split_ifs with hn
    · rfl
    · rw [norm_mul, Complex.zero_re, Real.rpow_zero, div_one, ofReal_re, div_eq_mul_inv,
        ← Real.rpow_neg (Nat.cast_nonneg n)]
      exact mul_le_mul_of_nonneg_left (hf_norm n hn) (norm_nonneg _)
  have hnz := tsum_dirichletExp_twist_ne_zero hℓ0 hℓ1 f hsumℓ
  -- the character decomposition
  have hB : ∀ χ : DirichletCharacter ℂ N, ∀ n, n ≠ 0 →
      ‖smoothSection Ψ χ f n‖ ≤ (∑ a, ‖Ψ a‖) * (n : ℝ) ^ (-σ') := by
    intro χ n hn
    unfold smoothSection
    split_ifs
    · rw [norm_mul]
      exact mul_le_mul (norm_charSection_le Ψ χ n) (hf_norm n hn) (norm_nonneg _)
        (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    · rw [norm_zero]; positivity
  have hβS : ∀ χ : DirichletCharacter ℂ N, LSeriesSummable (smoothSection Ψ χ f) 0 := fun χ =>
    LSeriesSummable_of_le_const_mul_rpow (x := 1 - σ') (by simp; linarith)
      ⟨∑ a, ‖Ψ a‖, fun n hn => by rw [show 1 - σ' - 1 = -σ' by ring]; exact hB χ n hn⟩
  have hγnorm : ∀ χ : DirichletCharacter ℂ N, ∀ n : ℕ, n ≠ 0 → ‖χ n * f n‖ ≤ (n : ℝ) ^ (-σ') := by
    intro χ n hn
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)).trans
      (hf_norm n hn)
  have hγS : ∀ χ : DirichletCharacter ℂ N, LSeriesSummable (fun n : ℕ => χ n * f n) 0 := fun χ =>
    summable_of_norm_le_rpow hσ' (hγnorm χ)
  have hdecomp : LSeries (fun n => dirichletExp ℓ n * f n) 0 =
      ∑ χ : DirichletCharacter ℂ N,
        LSeries (smoothSection Ψ χ f) 0 * LSeries (fun n : ℕ => χ n * f n) 0 := by
    have h1 : LSeries (fun n => dirichletExp ℓ n * f n) 0 = LSeries (∑ χ : DirichletCharacter ℂ N,
        LSeries.convolution (smoothSection Ψ χ f) (fun r => χ r * f r)) 0 := by
      refine LSeries_congr (fun {n} hn => ?_) 0
      rw [Finset.sum_apply, hΨ n hn]
      exact periodic_twist_eq_sum_convolution Ψ f hn
    rw [h1, LSeries_sum fun χ _ => (hβS χ).convolution (hγS χ)]
    exact Finset.sum_congr rfl fun χ _ => LSeries_convolution' (hβS χ) (hγS χ)
  -- the sections are the Dirichlet series `C(χ)`
  have hβ : ∀ χ : DirichletCharacter ℂ N, LSeries (smoothSection Ψ χ f) 0 = C χ := by
    intro χ
    simp only [hC, LSeries]
    refine tsum_congr fun n => ?_
    rw [LSeries.term_def, LSeries.term_def]
    split_ifs with hn
    · rfl
    · rw [Complex.cpow_zero, div_one]
      unfold smoothSection charSmoothCoeff
      split_ifs with hm
      · rw [hf, primeValueTwist_eq_cpow (P := N.primeFactors) (s := (s₀ : ℂ)) (fun p hp hpN => by
          simp only [hvdef, if_pos hpN]) hm, Complex.cpow_neg, div_eq_mul_inv]
      · rw [zero_div]
  -- the twisted characters are the Euler products
  have hγ : ∀ χ : DirichletCharacter ℂ N,
      LSeries (fun n : ℕ => χ n * f n) 0 = ∏ p ∈ S, (1 - χ p * z p)⁻¹ := by
    intro χ
    have hvS : ∀ p ∈ S, v p = z p := fun p hp => by
      simp only [hvdef, if_neg (hSN p hp), if_pos hp]
    have hplain : Summable fun n : ℕ => χ n * primeValueTwist v n := by
      refine (summable_congr fun n => ?_).mp (hγS χ)
      rw [LSeries.term_def]
      split_ifs with hn
      · subst hn; simp
      · rw [Complex.cpow_zero, div_one]
    rw [hf, LSeries_charTwist_eq_prod χ v S (fun p hp => (hS p hp).1) ?_ hplain]
    · exact Finset.prod_congr rfl fun p hp => by rw [hvS p hp]
    · intro p hp hpS
      simp only [hvdef, if_neg hpS]
      split_ifs with hpN
      · have : ¬ IsUnit (p : ZMod N) := fun hu =>
          (Nat.Prime.coprime_iff_not_dvd hp).mp ((ZMod.isUnit_iff_coprime p N).mp hu)
            (Nat.dvd_of_mem_primeFactors hpN)
        rw [MulChar.map_nonunit χ this, zero_mul]
      · rw [mul_zero]
  apply hnz
  rw [hdecomp]
  simp_rw [hβ, hγ]
  exact hzero

end

end CharacterZeroPlanting

end RHTower
