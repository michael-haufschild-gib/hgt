import GaloisForLFunctions.RHTower.SqrtTwoWindowDefect

/-!
# Primes of `ℤ[√2]` above a rational prime

* Every prime `π` of `ℤ[√2]` divides exactly one rational prime `p`, and `|N π| ∈ {p, p²}`.
* At most two normalized primes divide `p`, since the norms of the normalized factors of `p`
  multiply to `p²` and each is `≥ p`. For `p ≡ 3, 5 (mod 8)` there is exactly one, of norm `p²`.
* If two distinct normalized primes `π₁, π₂` divide `p`, both have norm `p` and `π₂ ~ π̄₁`.
* **Per-prime contribution.** With `Φ(π) = max(½, r^{−t(π)})`, the normalized primes above `p`
  contribute at most:
  - `2 p^{−σ}` in general;
  - `p^{−2σ}` if `p ≡ 3, 5 (mod 8)`;
  - `(2 − η) p^{−σ}` if `{log p / log r} ∈ (0, ¾]`, where `η = 1 − max(½, r^{−1/8}) > 0`.
    Here the pairing forces `t(π₁) + t(π₂) ≥ ¼`.
-/

noncomputable section

namespace RHTower.SqrtTwo

open UniqueFactorizationMonoid

theorem prime_star {π : ℤ√2} (hπ : Prime π) : Prime (star π) :=
  (MulEquiv.prime_iff (starRingAut : RingAut (ℤ√2))).mpr hπ

theorem natAbs_norm_mul (x y : ℤ√2) :
    (x * y).norm.natAbs = x.norm.natAbs * y.norm.natAbs := by
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]

theorem natAbs_norm_natCast (p : ℕ) : ((p : ℤ√2)).norm.natAbs = p ^ 2 := by
  rw [Zsqrtd.norm_natCast, Int.natAbs_mul, Int.natAbs_natCast, sq]

theorem dvd_natCast_natAbs_norm (x : ℤ√2) : x ∣ ((x.norm.natAbs : ℕ) : ℤ√2) := by
  have h : x ∣ (x.norm : ℤ√2) := ⟨star x, Zsqrtd.norm_eq_mul_conj x⟩
  rcases Int.natAbs_eq x.norm with he | he
  · have : ((x.norm.natAbs : ℕ) : ℤ√2) = (x.norm : ℤ√2) := by
      rw [← Int.cast_natCast, ← he]
    rw [this]; exact h
  · have : ((x.norm.natAbs : ℕ) : ℤ√2) = -(x.norm : ℤ√2) := by
      have e : ((x.norm.natAbs : ℕ) : ℤ) = -x.norm := by omega
      rw [← Int.cast_natCast, e, Int.cast_neg]
    rw [this]; exact dvd_neg.mpr h

theorem natAbs_norm_dvd_of_dvd {x y : ℤ√2} (h : x ∣ y) : x.norm.natAbs ∣ y.norm.natAbs := by
  obtain ⟨z, rfl⟩ := h
  rw [natAbs_norm_mul]; exact dvd_mul_right _ _

/-- A prime of `ℤ[√2]` lies over a rational prime `p` with `|N π| ∈ {p, p²}`. -/
theorem exists_rat_prime_below {π : ℤ√2} (hπ : Prime π) :
    ∃ p : ℕ, p.Prime ∧ π ∣ (p : ℤ√2) ∧ (π.norm.natAbs = p ∨ π.norm.natAbs = p ^ 2) := by
  have hm0 : π.norm.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (norm_ne_zero hπ.ne_zero)
  have hdvd := dvd_natCast_natAbs_norm π
  have hprod : ((π.norm.natAbs : ℕ) : ℤ√2) =
      ((π.norm.natAbs.primeFactorsList.map (fun n : ℕ => (n : ℤ√2))).prod) := by
    rw [← Nat.cast_list_prod, Nat.prod_primeFactorsList hm0]
  rw [hprod, hπ.dvd_prod_iff] at hdvd
  obtain ⟨_, hmem, hπp⟩ := hdvd
  obtain ⟨p, hpm, rfl⟩ := List.mem_map.mp hmem
  have hp : p.Prime := Nat.prime_of_mem_primeFactorsList hpm
  refine ⟨p, hp, hπp, ?_⟩
  have hd := natAbs_norm_dvd_of_dvd hπp
  rw [natAbs_norm_natCast] at hd
  obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow hp).mp hd
  interval_cases i
  · exact absurd (Zsqrtd.norm_eq_one_iff.mp (by simpa using hi')) hπ.not_unit
  · left; simpa using hi'
  · right; exact hi'

/-- The rational prime below `π` is unique. -/
theorem eq_of_dvd_rat_primes {π : ℤ√2} (hπ : Prime π) {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime)
    (h : π ∣ (p : ℤ√2)) (h' : π ∣ (p' : ℤ√2)) : p = p' := by
  by_contra hne
  have hcop : IsCoprime (p : ℤ) (p' : ℤ) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (by
      rw [Int.gcd_natCast_natCast]; exact (Nat.coprime_primes hp hp').mpr hne)
  have hcop' : IsCoprime (p : ℤ√2) (p' : ℤ√2) := by
    have := hcop.map (Int.castRingHom (ℤ√2))
    simpa using this
  exact hπ.not_unit (hcop'.isUnit_of_dvd' h h')

/-- A normalized prime dividing `x ≠ 0` is one of its normalized factors. -/
theorem mem_normalizedFactors_of_dvd {π x : ℤ√2} (hπ : Prime π) (hn : normalize π = π)
    (hx : x ≠ 0) (h : π ∣ x) : π ∈ normalizedFactors x := by
  obtain ⟨q, hq, hassoc⟩ := exists_mem_normalizedFactors_of_dvd hx hπ.irreducible h
  have hqn : normalize q = q := normalize_normalized_factor q hq
  have : π = q := by rw [← hn, ← hqn]; exact normalize_eq_normalize hassoc.dvd hassoc.symm.dvd
  rw [this]; exact hq

theorem natAbs_norm_prod (s : Multiset (ℤ√2)) :
    s.prod.norm.natAbs = (s.map fun x => x.norm.natAbs).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => rw [Multiset.prod_cons, natAbs_norm_mul, ih, Multiset.map_cons,
      Multiset.prod_cons]

/-- The normalized factors of a rational prime have norms multiplying to `p²`, each `≥ p`. -/
theorem prod_natAbs_norm_normalizedFactors {p : ℕ} (hp : p.Prime) :
    ((normalizedFactors (p : ℤ√2)).map fun x => x.norm.natAbs).prod = p ^ 2 := by
  have hp0 : (p : ℤ√2) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hassoc := prod_normalizedFactors hp0
  obtain ⟨V, hV⟩ := hassoc
  have := congrArg (fun z : ℤ√2 => z.norm.natAbs) hV
  simp only [natAbs_norm_mul] at this
  rw [Zsqrtd.norm_eq_one_iff.mpr V.isUnit, mul_one, natAbs_norm_prod, natAbs_norm_natCast] at this
  exact this

theorem le_natAbs_norm_of_mem {p : ℕ} (hp : p.Prime) {π : ℤ√2}
    (hπ : π ∈ normalizedFactors (p : ℤ√2)) : p ≤ π.norm.natAbs := by
  have hπp := prime_of_normalized_factor π hπ
  have hdvd := dvd_of_mem_normalizedFactors hπ
  obtain ⟨p', hp', hπp', hN⟩ := exists_rat_prime_below hπp
  have := eq_of_dvd_rat_primes hπp hp hp' hdvd hπp'
  subst this
  rcases hN with h | h
  · exact h.ge
  · rw [h]; exact Nat.le_self_pow (by norm_num) p

theorem card_normalizedFactors_le_two {p : ℕ} (hp : p.Prime) :
    (normalizedFactors (p : ℤ√2)).card ≤ 2 := by
  have hprod := prod_natAbs_norm_normalizedFactors hp
  have hle : p ^ (normalizedFactors (p : ℤ√2)).card ≤ p ^ 2 := by
    rw [← hprod, ← Multiset.card_map (fun x : ℤ√2 => x.norm.natAbs)]
    apply Multiset.pow_card_le_prod
    intro n hn
    obtain ⟨π, hπ, rfl⟩ := Multiset.mem_map.mp hn
    exact le_natAbs_norm_of_mem hp hπ
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hle


/-- `Φ(π) = max(½, r^{−t(π)})`. -/
def phiW (π : ℤ√2) : ℝ := max (1 / 2) (rr ^ (-windowDefect π))

theorem phiW_le_one (π : ℤ√2) : phiW π ≤ 1 :=
  max_le (by norm_num)
    (Real.rpow_le_one_of_one_le_of_nonpos one_lt_rr.le (by linarith [windowDefect_nonneg π]))

theorem phiW_nonneg (π : ℤ√2) : 0 ≤ phiW π := le_trans (by norm_num) (le_max_left _ _)

/-- The saving `η = 1 − max(½, r^{−1/8}) > 0`. -/
def etaW : ℝ := 1 - max (1 / 2) (rr ^ (-(1 / 8 : ℝ)))

theorem etaW_pos : 0 < etaW := by
  have : rr ^ (-(1 / 8 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_rr (by norm_num)
  unfold etaW
  have : max (1 / 2) (rr ^ (-(1 / 8 : ℝ))) < 1 := max_lt (by norm_num) this
  linarith

theorem etaW_le_half : etaW ≤ 1 / 2 := by
  unfold etaW; linarith [le_max_left (1 / 2 : ℝ) (rr ^ (-(1 / 8 : ℝ)))]

theorem phiW_le_of_defect {π : ℤ√2} (h : 1 / 8 ≤ windowDefect π) : phiW π ≤ 1 - etaW := by
  unfold phiW etaW
  rw [sub_sub_cancel]
  apply max_le_max le_rfl
  exact Real.rpow_le_rpow_of_exponent_le one_lt_rr.le (by linarith)

/-- Two distinct normalized factors of `p` both have norm `p`. -/
theorem natAbs_norm_eq_of_ne {p : ℕ} (hp : p.Prime) {π₁ π₂ : ℤ√2}
    (h₁ : π₁ ∈ normalizedFactors (p : ℤ√2)) (h₂ : π₂ ∈ normalizedFactors (p : ℤ√2))
    (hne : π₁ ≠ π₂) : π₁.norm.natAbs = p := by
  have hprod := prod_natAbs_norm_normalizedFactors hp
  rw [← Multiset.cons_erase h₁, Multiset.map_cons, Multiset.prod_cons] at hprod
  have h₂' : π₂ ∈ (normalizedFactors (p : ℤ√2)).erase π₁ := (Multiset.mem_erase_of_ne hne.symm).mpr h₂
  have hdvd : π₂.norm.natAbs ∣ (((normalizedFactors (p : ℤ√2)).erase π₁).map
      fun x => x.norm.natAbs).prod :=
    Multiset.dvd_prod (Multiset.mem_map_of_mem _ h₂')
  have hp2 : 0 < p ^ 2 := by have := hp.pos; positivity
  have hpos : 0 < (((normalizedFactors (p : ℤ√2)).erase π₁).map fun x => x.norm.natAbs).prod := by
    rcases Nat.eq_zero_or_pos (((normalizedFactors (p : ℤ√2)).erase π₁).map
      fun x => x.norm.natAbs).prod with h | h
    · rw [h, mul_zero] at hprod; omega
    · exact h
  have hle2 := Nat.le_of_dvd hpos hdvd
  have hπ₁ := le_natAbs_norm_of_mem hp h₁
  have hπ₂ := le_natAbs_norm_of_mem hp h₂
  have : π₁.norm.natAbs * π₂.norm.natAbs ≤ p ^ 2 := by
    rw [← hprod]; exact Nat.mul_le_mul_left _ hle2
  nlinarith

/-- Two distinct normalized factors of `p` are conjugate up to association. -/
theorem associated_star_of_ne {p : ℕ} (hp : p.Prime) {π₁ π₂ : ℤ√2}
    (h₁ : π₁ ∈ normalizedFactors (p : ℤ√2)) (h₂ : π₂ ∈ normalizedFactors (p : ℤ√2))
    (hne : π₁ ≠ π₂) : Associated (star π₁) π₂ := by
  have hp0 : (p : ℤ√2) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hπ₁ := prime_of_normalized_factor π₁ h₁
  have hN := natAbs_norm_eq_of_ne hp h₁ h₂ hne
  have hs := prime_star hπ₁
  have hsN : (star π₁).norm.natAbs = p := by rw [Zsqrtd.norm_conj]; exact hN
  have hsdvd : star π₁ ∣ (p : ℤ√2) := by
    have := dvd_natCast_natAbs_norm (star π₁); rwa [hsN] at this
  set q := normalize (star π₁) with hq
  have hqprime : Prime q := (associated_normalize (star π₁)).prime hs
  have hqn : normalize q = q := by rw [hq, normalize_idem (star π₁)]
  have hqdvd : q ∣ (p : ℤ√2) := (associated_normalize (star π₁)).symm.dvd.trans hsdvd
  have hqmem := mem_normalizedFactors_of_dvd hqprime hqn hp0 hqdvd
  have hπ₁n : normalize π₁ = π₁ := normalize_normalized_factor π₁ h₁
  by_cases hq1 : q = π₁
  · exfalso
    -- then `p ~ π₁²`
    have hsa : Associated (star π₁) π₁ := by
      have := associated_normalize (star π₁); rw [← hq, hq1] at this; exact this
    have hpassoc : Associated (p : ℤ√2) (π₁ ^ 2) := by
      have h1 : Associated (π₁ * star π₁) (p : ℤ√2) := by
        have e := Zsqrtd.norm_eq_mul_conj π₁
        rcases Int.natAbs_eq π₁.norm with he | he
        · refine Associated.of_eq ?_
          rw [← e, he, hN, Int.cast_natCast]
        · refine ⟨-1, ?_⟩
          rw [Units.val_neg, Units.val_one, ← e, he, hN]; push_cast; ring
      exact h1.symm.trans ((Associated.refl π₁).mul_mul hsa |>.trans (Associated.of_eq (sq π₁).symm))
    have hnf := (associated_iff_normalizedFactors_eq_normalizedFactors hp0
      (pow_ne_zero 2 hπ₁.ne_zero)).mp hpassoc
    rw [normalizedFactors_pow, normalizedFactors_irreducible hπ₁.irreducible, hπ₁n] at hnf
    rw [hnf] at h₂
    simp at h₂
    exact hne h₂.symm
  by_cases hq2 : q = π₂
  · rw [← hq2]; exact associated_normalize _
  · exfalso
    have hsub : ({π₁, π₂, q} : Finset (ℤ√2)) ⊆ (normalizedFactors (p : ℤ√2)).toFinset := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> exact Multiset.mem_toFinset.mpr (by assumption)
    have hcard : ({π₁, π₂, q} : Finset (ℤ√2)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hq2)]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hne, Ne.symm hq1⟩
    have h3 := (Finset.card_le_card hsub).trans (Multiset.toFinset_card_le _)
    have h2 := card_normalizedFactors_le_two hp
    omega

/-- **Per-prime contribution, general case.** -/
theorem sum_le_two_mul {p : ℕ} (hp : p.Prime) (T : Finset (ℤ√2))
    (hT : ∀ π ∈ T, π ∈ normalizedFactors (p : ℤ√2)) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∑ π ∈ T, ((π.norm.natAbs : ℕ) : ℝ) ^ (-σ) * phiW π ≤ 2 * (p : ℝ) ^ (-σ) := by
  have hcard : T.card ≤ 2 := by
    have hsub : T ⊆ (normalizedFactors (p : ℤ√2)).toFinset := fun π hπ =>
      Multiset.mem_toFinset.mpr (hT π hπ)
    exact (Finset.card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans
      (card_normalizedFactors_le_two hp))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  calc ∑ π ∈ T, ((π.norm.natAbs : ℕ) : ℝ) ^ (-σ) * phiW π
      ≤ ∑ _π ∈ T, (p : ℝ) ^ (-σ) := by
        refine Finset.sum_le_sum fun π hπ => ?_
        have hle : (p : ℝ) ≤ ((π.norm.natAbs : ℕ) : ℝ) := by
          exact_mod_cast le_natAbs_norm_of_mem hp (hT π hπ)
        calc ((π.norm.natAbs : ℕ) : ℝ) ^ (-σ) * phiW π
            ≤ ((π.norm.natAbs : ℕ) : ℝ) ^ (-σ) * 1 :=
              mul_le_mul_of_nonneg_left (phiW_le_one π) (Real.rpow_nonneg (by positivity) _)
          _ ≤ (p : ℝ) ^ (-σ) := by
              rw [mul_one]; exact Real.rpow_le_rpow_of_nonpos hp0 hle (by linarith)
    _ = T.card * (p : ℝ) ^ (-σ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * (p : ℝ) ^ (-σ) := by
        gcongr; exact_mod_cast hcard

/-- **Per-prime contribution, inert case.** -/
theorem sum_le_inert {p : ℕ} [hp : Fact p.Prime] (h8 : p % 8 = 3 ∨ p % 8 = 5) (T : Finset (ℤ√2))
    (hT : ∀ π ∈ T, π ∈ normalizedFactors (p : ℤ√2)) (σ : ℝ) :
    ∑ π ∈ T, ((π.norm.natAbs : ℕ) : ℝ) ^ (-σ) * phiW π ≤ (p : ℝ) ^ (-(2 * σ)) := by
  have hnf := normalizedFactors_irreducible (irreducible_natCast_of_mod_eight h8)
  have hsub : T ⊆ {normalize (p : ℤ√2)} := by
    intro π hπ; have := hT π hπ; rw [hnf] at this; simpa using this
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  calc ∑ π ∈ T, ((π.norm.natAbs : ℕ) : ℝ) ^ (-σ) * phiW π
      ≤ ∑ π ∈ ({normalize (p : ℤ√2)} : Finset (ℤ√2)),
          ((π.norm.natAbs : ℕ) : ℝ) ^ (-σ) * phiW π :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun π _ _ =>
          mul_nonneg (Real.rpow_nonneg (by positivity) _) (phiW_nonneg π)
    _ = (((normalize (p : ℤ√2)).norm.natAbs : ℕ) : ℝ) ^ (-σ) * phiW (normalize (p : ℤ√2)) := by
        rw [Finset.sum_singleton]
    _ ≤ (((normalize (p : ℤ√2)).norm.natAbs : ℕ) : ℝ) ^ (-σ) * 1 :=
        mul_le_mul_of_nonneg_left (phiW_le_one _) (Real.rpow_nonneg (by positivity) _)
    _ = (p : ℝ) ^ (-(2 * σ)) := by
        have hN : (normalize (p : ℤ√2)).norm.natAbs = p ^ 2 := by
          obtain ⟨V, hV⟩ := (associated_normalize (p : ℤ√2))
          rw [← hV, natAbs_norm_mul, Zsqrtd.norm_eq_one_iff.mpr V.isUnit, mul_one,
            natAbs_norm_natCast]
        rw [mul_one, hN]; push_cast
        rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; ring_nf

/-- **Per-prime contribution, split case with a phase gap.** -/
theorem sum_le_split {p : ℕ} (hp : p.Prime) (T : Finset (ℤ√2))
    (hT : ∀ π ∈ T, π ∈ normalizedFactors (p : ℤ√2)) {σ : ℝ} (hσ : 0 ≤ σ)
    (hfr0 : 0 < Int.fract (Real.log p / Real.log rr))
    (hfr : Int.fract (Real.log p / Real.log rr) ≤ 3 / 4) :
    ∑ π ∈ T, ((π.norm.natAbs : ℕ) : ℝ) ^ (-σ) * phiW π ≤ (2 - etaW) * (p : ℝ) ^ (-σ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hterm : ∀ π ∈ T, ((π.norm.natAbs : ℕ) : ℝ) ^ (-σ) * phiW π ≤ (p : ℝ) ^ (-σ) * phiW π := by
    intro π hπ
    have hle : (p : ℝ) ≤ ((π.norm.natAbs : ℕ) : ℝ) := by
      exact_mod_cast le_natAbs_norm_of_mem hp (hT π hπ)
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hp0 hle (by linarith))
      (phiW_nonneg π)
  have hpσ : 0 ≤ (p : ℝ) ^ (-σ) := Real.rpow_nonneg hp0.le _
  have hcard : T.card ≤ 2 := by
    have hsub : T ⊆ (normalizedFactors (p : ℤ√2)).toFinset := fun π hπ =>
      Multiset.mem_toFinset.mpr (hT π hπ)
    exact (Finset.card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans
      (card_normalizedFactors_le_two hp))
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, mul_comm (2 - etaW)]
  apply mul_le_mul_of_nonneg_left _ hpσ
  rcases Nat.lt_or_ge T.card 2 with h1 | h2
  · -- at most one prime above `p`
    calc ∑ π ∈ T, phiW π ≤ ∑ _π ∈ T, (1 : ℝ) := Finset.sum_le_sum fun π _ => phiW_le_one π
      _ = T.card := by simp
      _ ≤ 1 := by exact_mod_cast (by omega : T.card ≤ 1)
      _ ≤ 2 - etaW := by linarith [etaW_le_half]
  · obtain ⟨π₁, π₂, hne, rfl⟩ := Finset.card_eq_two.mp (show T.card = 2 by omega)
    rw [Finset.sum_pair hne]
    have h₁ := hT π₁ (by simp)
    have h₂ := hT π₂ (by simp)
    have hπ₁ := prime_of_normalized_factor π₁ h₁
    have hN := natAbs_norm_eq_of_ne hp h₁ h₂ hne
    have hassoc := associated_star_of_ne hp h₁ h₂ hne
    have ht₂ : windowDefect π₂ = windowDefect (star π₁) :=
      windowDefect_eq_of_associated (star_ne_zero' hπ₁.ne_zero) hassoc
    have hpair := one_sub_fract_le_windowDefect_add hπ₁.ne_zero (by rw [hN]; exact hfr0)
    rw [hN] at hpair
    have hsum : 1 / 4 ≤ windowDefect π₁ + windowDefect π₂ := by rw [ht₂]; linarith
    rcases le_or_gt (1 / 8) (windowDefect π₁) with ht | ht
    · have := phiW_le_of_defect ht; linarith [phiW_le_one π₂]
    · have := phiW_le_of_defect (show 1 / 8 ≤ windowDefect π₂ by linarith)
      linarith [phiW_le_one π₁]

end RHTower.SqrtTwo
