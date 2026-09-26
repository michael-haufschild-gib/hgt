import GaloisForLFunctions.RHTower.HalfWeightEisensteinCoefficients

/-!
# Square roots modulo `f`: the local data of the weight-½ Eisenstein coefficients

`N_f(n) = #{x ∈ ℤ/f : x² = n}` (`rootCard`, equal to the range count `sqCount` of
`HalfWeightEisensteinCoefficients` by `sqCount_eq_rootCard`).

* `rootCard_mul`: `N_{ab}(n) = N_a(n) N_b(n)` for coprime `a, b` (Chinese remainder theorem).
* `card_sq_eq_of_isSquare`: in a finite cyclic group of even order a square has exactly two square
  roots (kernel of `g ↦ g²` has order `gcd(|G|, 2) = 2`).
* `isSquare_units_iff`: a unit mod `p^a` (`p` odd) is a square iff its reduction mod `p` is; the
  squares and the preimage of the squares mod `p` are subgroups of index `2`, one inside the other
  (cyclicity of `(ℤ/p^a)ˣ`, `ZMod.isCyclic_units_of_prime_pow`). No Hensel lifting is used.
* `rootCard_prime_pow`: `N_{p^a}(n) = 1 + (n/p)` for odd `p ∤ n`, `a ≥ 1`.
* `pm_classes`, `rootCard_le`: two square roots of `n ≠ 0` mod `p^a` agree up to sign mod
  `p^{a - v_p(4n)}`, hence `N_{p^a}(n) ≤ 8|n|` uniformly in `a`; the local Euler factors at primes
  dividing `2Mn` therefore converge for `Re s > 0`.
-/

open Complex

namespace GaloisForLFunctions.RHTower.HalfWeight

/-! ### Square roots modulo `f` -/

/-- The number of square roots of `n` in `ZMod f`. -/
def rootCard (n : ℤ) (f : ℕ) [NeZero f] : ℕ :=
  (Finset.univ.filter fun x : ZMod f => x ^ 2 = (n : ZMod f)).card

theorem dvd_sub_sq_iff_zmod (n : ℤ) (f m : ℕ) :
    (f : ℤ) ∣ n - (m : ℤ) ^ 2 ↔ ((m : ZMod f)) ^ 2 = (n : ZMod f) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [sub_eq_zero, eq_comm]

theorem sqCount_eq_rootCard (n : ℤ) (f : ℕ) [NeZero f] : sqCount n f = (rootCard n f : ℂ) := by
  unfold sqCount rootCard
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_nbij (fun m : ℕ => (m : ZMod f)) ?_ ?_ ?_ ?_
  · intro m _; exact Finset.mem_univ _
  · intro a ha b hb h
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have := congrArg ZMod.val h
    rwa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at this
  · intro x _
    refine ⟨x.val, ?_, ZMod.natCast_zmod_val x⟩
    simp only [Finset.coe_range, Set.mem_Iio]
    exact ZMod.val_lt x
  · intro m _
    simp only [dvd_sub_sq_iff_zmod]

/-- **Multiplicativity** of the square-root count (Chinese remainder theorem). -/
theorem rootCard_mul {a b : ℕ} [NeZero a] [NeZero b] (hab : a.Coprime b) (n : ℤ) :
    haveI : NeZero (a * b) := ⟨mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
    rootCard n (a * b) = rootCard n a * rootCard n b := by
  haveI : NeZero (a * b) := ⟨mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  unfold rootCard
  rw [← Finset.card_product]
  set e := ZMod.chineseRemainder hab
  refine Finset.card_bij (fun x _ => e x) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [Finset.mem_product]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h := congrArg e hx
    rw [map_pow, map_intCast] at h
    exact ⟨by simpa using congrArg Prod.fst h, by simpa using congrArg Prod.snd h⟩
  · intro x _ y _ h; exact e.injective h
  · intro p hp
    rw [Finset.mem_product] at hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    refine ⟨e.symm p, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply e.injective
    rw [map_pow, map_intCast, RingEquiv.apply_symm_apply]
    exact Prod.ext (by simpa using hp.1) (by simpa using hp.2)

/-! ### Square roots of units in a cyclic group -/

/-- In a finite cyclic group of even order, a square has exactly two square roots. -/
theorem card_sq_eq_of_isSquare {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [IsCyclic G]
    (hev : 2 ∣ Fintype.card G) {u : G} (hu : IsSquare u) :
    (Finset.univ.filter fun g : G => g ^ 2 = u).card = 2 := by
  obtain ⟨h, rfl⟩ := hu
  have hker := IsCyclic.card_powMonoidHom_ker G 2
  rw [Nat.card_eq_fintype_card (α := G), Nat.gcd_eq_right hev] at hker
  rw [← Nat.card_eq_finsetCard]
  refine (Nat.card_congr ?_).trans hker
  refine
    { toFun := fun g => ⟨g.1 * h⁻¹, by
        simp only [MonoidHom.mem_ker, powMonoidHom_apply]
        have := (Finset.mem_filter.1 g.2).2
        rw [mul_pow, this, inv_pow]; group⟩
      invFun := fun t => ⟨t.1 * h, by
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
        have := t.2
        simp only [MonoidHom.mem_ker, powMonoidHom_apply] at this
        rw [mul_pow, this, one_mul, pow_two]⟩
      left_inv := fun g => by ext; simp
      right_inv := fun t => by ext; simp }

theorem card_sq_eq_of_not_isSquare {G : Type*} [Monoid G] [Fintype G] [DecidableEq G] {u : G}
    (hu : ¬ IsSquare u) : (Finset.univ.filter fun g : G => g ^ 2 = u).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro g _ hg
  exact hu ⟨g, by rw [← hg, pow_two]⟩

/-! ### Squares modulo odd prime powers -/

section PrimePow

variable {p : ℕ} [hp : Fact p.Prime]

theorem two_dvd_card_units_prime_pow (hp2 : p ≠ 2) {a : ℕ} (ha : 0 < a) :
    2 ∣ Nat.card (ZMod (p ^ a))ˣ := by
  haveI : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow hp.out ha]
  exact dvd_mul_of_dvd_right (hp.out.even_sub_one hp2).two_dvd _

theorem two_dvd_card_units_prime (hp2 : p ≠ 2) : 2 ∣ Nat.card (ZMod p)ˣ := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units]
  exact (hp.out.even_sub_one hp2).two_dvd

/-- A unit modulo `p^a` (`p` odd) is a square iff its reduction modulo `p` is a square. -/
theorem isSquare_units_iff (hp2 : p ≠ 2) {a : ℕ} (ha : 0 < a) (u : (ZMod (p ^ a))ˣ) :
    IsSquare u ↔ IsSquare (ZMod.unitsMap (dvd_pow_self p ha.ne') u) := by
  haveI : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  haveI : IsCyclic (ZMod (p ^ a))ˣ := ZMod.isCyclic_units_of_prime_pow p hp.out hp2 a
  set π := ZMod.unitsMap (dvd_pow_self p ha.ne') with hπ
  have hsurj : Function.Surjective π := ZMod.unitsMap_surjective _
  set H := (powMonoidHom 2 : (ZMod (p ^ a))ˣ →* (ZMod (p ^ a))ˣ).range
  set K := Subgroup.comap π (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range
  have hHK : H ≤ K := by
    rintro _ ⟨g, rfl⟩
    exact ⟨π g, by simp [map_pow]⟩
  have hH : H.index = 2 := by
    rw [IsCyclic.index_powMonoidHom_range, Nat.gcd_eq_right (two_dvd_card_units_prime_pow hp2 ha)]
  have hK : K.index = 2 := by
    rw [Subgroup.index_comap_of_surjective _ hsurj, IsCyclic.index_powMonoidHom_range,
      Nat.gcd_eq_right (two_dvd_card_units_prime hp2)]
  have hcard : Nat.card K ≤ Nat.card H := by
    have h1 := Subgroup.card_mul_index H
    have h2 := Subgroup.card_mul_index K
    rw [hH] at h1; rw [hK] at h2
    omega
  have hEq : H = K := Subgroup.eq_of_le_of_card_ge hHK hcard
  have hsq : ∀ {G : Type} [CommGroup G] (v : G),
      IsSquare v ↔ v ∈ (powMonoidHom 2 : G →* G).range := by
    intro G _ v
    constructor
    · rintro ⟨r, rfl⟩; exact ⟨r, by simp [pow_two]⟩
    · rintro ⟨r, rfl⟩; exact ⟨r, by simp [pow_two]⟩
  rw [hsq, hsq]
  change u ∈ H ↔ π u ∈ (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range
  rw [hEq]
  rfl

end PrimePow

section PrimePowCount

variable {p : ℕ} [hp : Fact p.Prime]

theorem isUnit_intCast_prime_pow {a : ℕ} {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) :
    IsUnit (n : ZMod (p ^ a)) := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime]
  push_cast
  exact ((Nat.prime_iff_prime_int.mp hp.out).coprime_iff_not_dvd.2 hn).pow_left

/-- The square roots of a unit `n` in `ZMod (p^a)` correspond to the square roots of the unit. -/
theorem rootCard_eq_units {a : ℕ} [NeZero (p ^ a)] {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) :
    rootCard n (p ^ a) = (Finset.univ.filter fun g : (ZMod (p ^ a))ˣ =>
      g ^ 2 = (isUnit_intCast_prime_pow (a := a) hn).unit).card := by
  unfold rootCard
  symm
  refine Finset.card_bij (fun g _ => (g : ZMod (p ^ a))) ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    have := congrArg Units.val hg
    simpa using this
  · intro g _ h _ hgh; exact Units.ext hgh
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have hxu : IsUnit x := by
      have h1 : IsUnit (x * x) := by
        rw [← pow_two, hx]; exact isUnit_intCast_prime_pow hn
      exact isUnit_of_mul_isUnit_left h1
    refine ⟨hxu.unit, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    ext
    simp [hx]

/-- **Square roots modulo an odd prime power**: for `p ∤ n`, `N_{p^a}(n) = 1 + (n/p)` (`a ≥ 1`). -/
theorem rootCard_prime_pow (hp2 : p ≠ 2) {a : ℕ} (ha : 0 < a) {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) :
    haveI : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    (rootCard n (p ^ a) : ℤ) = legendreSym p n + 1 := by
  haveI : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  haveI : IsCyclic (ZMod (p ^ a))ˣ := ZMod.isCyclic_units_of_prime_pow p hp.out hp2 a
  rw [rootCard_eq_units hn]
  set U := (isUnit_intCast_prime_pow (a := a) hn).unit
  have hnp : (n : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hn
  have hπU : ((ZMod.unitsMap (dvd_pow_self p ha.ne') U : (ZMod p)ˣ) : ZMod p) = (n : ZMod p) := by
    rw [ZMod.unitsMap_def]
    simp [U]
  have hsqF : IsSquare (ZMod.unitsMap (dvd_pow_self p ha.ne') U) ↔ IsSquare (n : ZMod p) := by
    rw [← hπU]
    constructor
    · rintro ⟨r, hr⟩; exact ⟨r, by rw [hr]; simp⟩
    · rintro ⟨r, hr⟩
      have hr0 : r ≠ 0 := by
        rintro rfl; rw [hπU] at hr; simp at hr; exact hnp hr
      refine ⟨Units.mk0 r hr0, Units.ext ?_⟩
      simp [hr]
  have hev : 2 ∣ Fintype.card (ZMod (p ^ a))ˣ := by
    rw [← Nat.card_eq_fintype_card]; exact two_dvd_card_units_prime_pow hp2 ha
  by_cases hsq : IsSquare (n : ZMod p)
  · rw [card_sq_eq_of_isSquare hev ((isSquare_units_iff hp2 ha U).2 (hsqF.2 hsq)),
      (legendreSym.eq_one_iff p hnp).2 hsq]
    norm_num
  · rw [card_sq_eq_of_not_isSquare (fun h => hsq (hsqF.1 ((isSquare_units_iff hp2 ha U).1 h))),
      (legendreSym.eq_neg_one_iff p).2 hsq]
    norm_num

end PrimePowCount

/-! ### A bound for the number of square roots, uniform in the exponent -/

section RootBound

variable {p : ℕ} [hp : Fact p.Prime]

/-- Two square roots of `n ≠ 0` modulo `p^a` agree up to sign modulo `p^{a-e}`, `e = v_p(4n)`. -/
theorem pm_classes {a : ℕ} {n X Y : ℤ} (hn : n ≠ 0) (hX : (p : ℤ) ^ a ∣ X ^ 2 - n)
    (hY : (p : ℤ) ^ a ∣ Y ^ 2 - n) :
    (p : ℤ) ^ (a - padicValNat p (4 * n.natAbs)) ∣ X - Y ∨
      (p : ℤ) ^ (a - padicValNat p (4 * n.natAbs)) ∣ X + Y := by
  set e := padicValNat p (4 * n.natAbs) with he
  by_cases hae : a ≤ e
  · left; rw [Nat.sub_eq_zero_of_le hae, pow_zero]; exact one_dvd _
  push Not at hae
  have h4n : 4 * n.natAbs ≠ 0 := by positivity
  have hdiv : (p : ℤ) ^ a ∣ (X - Y) * (X + Y) := by
    have := dvd_sub hX hY
    rw [show X ^ 2 - n - (Y ^ 2 - n) = (X - Y) * (X + Y) by ring] at this
    exact this
  have hpe : (p : ℤ) ^ (e + 1) ∣ (p : ℤ) ^ a := pow_dvd_pow _ hae
  -- `p^{e+1} ∤ 2X`
  have key : ¬ (p : ℤ) ^ (e + 1) ∣ 2 * X := by
    intro h2X
    have h1 : (p : ℤ) ^ (e + 1) ∣ 4 * X ^ 2 := by
      have := dvd_mul_of_dvd_left h2X (2 * X)
      rw [show 2 * X * (2 * X) = 4 * X ^ 2 by ring] at this; exact this
    have h2 : (p : ℤ) ^ (e + 1) ∣ 4 * (X ^ 2 - n) := dvd_mul_of_dvd_right (hpe.trans hX) 4
    have h3 : (p : ℤ) ^ (e + 1) ∣ 4 * n := by
      have := dvd_sub h1 h2
      rw [show 4 * X ^ 2 - 4 * (X ^ 2 - n) = 4 * n by ring] at this; exact this
    have h4 : p ^ (e + 1) ∣ 4 * n.natAbs := by
      have := Int.natAbs_dvd_natAbs.2 h3
      simpa [Int.natAbs_mul, Int.natAbs_pow] using this
    exact pow_succ_padicValNat_not_dvd h4n h4
  -- one of `X ∓ Y` is not divisible by `p^{e+1}`
  have hone : ∀ D S : ℤ, D * S = (X - Y) * (X + Y) → ¬ (p : ℤ) ^ (e + 1) ∣ D →
      (p : ℤ) ^ (a - e) ∣ S := by
    intro D S hDS hD
    have hD0 : D ≠ 0 := by rintro rfl; exact hD (dvd_zero _)
    obtain ⟨k, D', hpD', hDk⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hD0) p
      hp.out.ne_one
    have hk : k ≤ e := by
      by_contra hk; push Not at hk
      apply hD
      rw [← Int.natAbs_dvd_natAbs]
      simp only [Int.natAbs_pow, Int.natAbs_natCast]
      rw [hDk]
      exact dvd_mul_of_dvd_left (pow_dvd_pow _ hk) _
    have hpa : p ^ a ∣ p ^ k * D' * S.natAbs := by
      have := Int.natAbs_dvd_natAbs.2 (hdiv.trans (by rw [← hDS]))
      simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at this
      rwa [hDk] at this
    have hsplit : p ^ a = p ^ k * p ^ (a - k) := by rw [← pow_add]; congr 1; omega
    rw [hsplit, mul_assoc] at hpa
    have hpa' := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.out.pos k) hpa
    have hcop : (p ^ (a - k)).Coprime D' :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpD')
    have hS : p ^ (a - k) ∣ S.natAbs := hcop.dvd_of_dvd_mul_left hpa'
    have hS' : p ^ (a - e) ∣ S.natAbs := (pow_dvd_pow _ (by omega)).trans hS
    rw [← Int.natAbs_dvd_natAbs]
    simpa [Int.natAbs_pow] using hS'
  by_cases hXY : (p : ℤ) ^ (e + 1) ∣ X - Y
  · -- then `X + Y` is not divisible, so `p^{a-e} ∣ X - Y`
    have hXY' : ¬ (p : ℤ) ^ (e + 1) ∣ X + Y := by
      intro h; apply key
      have := dvd_add hXY h
      rw [show X - Y + (X + Y) = 2 * X by ring] at this; exact this
    left
    exact hone (X + Y) (X - Y) (by ring) hXY'
  · right
    exact hone (X - Y) (X + Y) rfl hXY

end RootBound

theorem rootCard_eq_card_range (n : ℤ) (f : ℕ) [NeZero f] :
    rootCard n f = ((Finset.range f).filter fun m : ℕ => (f : ℤ) ∣ n - (m : ℤ) ^ 2).card := by
  unfold rootCard
  symm
  refine Finset.card_nbij (fun m : ℕ => (m : ZMod f)) ?_ ?_ ?_
  · intro m hm
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hm
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    exact (dvd_sub_sq_iff_zmod n f m).1 hm.2
  · intro a ha b hb h
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ha hb
    have := congrArg ZMod.val h
    rwa [ZMod.val_natCast_of_lt ha.1, ZMod.val_natCast_of_lt hb.1] at this
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx
    refine ⟨x.val, ?_, ZMod.natCast_zmod_val x⟩
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
    refine ⟨ZMod.val_lt x, ?_⟩
    rw [dvd_sub_sq_iff_zmod, ZMod.natCast_zmod_val]; exact hx

theorem card_class_le (q Q : ℕ) (c : ℤ) :
    ((Finset.range (Q * q)).filter fun m : ℕ => (q : ℤ) ∣ c - m).card ≤ Q := by
  calc _ ≤ (Finset.range Q).card := by
        refine Finset.card_le_card_of_injOn (fun m => m / q) ?_ ?_
        · intro m hm
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hm
          simp only [Finset.coe_range, Set.mem_Iio]
          exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hm.1)
        · intro m hm m' hm' h
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hm hm'
          have hmod : m % q = m' % q := by
            have h1 : (q : ℤ) ∣ (m' : ℤ) - m := by
              have := dvd_sub hm.2 hm'.2
              rw [show c - m - (c - m') = (m' : ℤ) - m by ring] at this; exact this
            have h2 : (m : ℤ) ≡ m' [ZMOD q] := Int.modEq_iff_dvd.2 h1
            have h3 : (m : ℤ) % q = (m' : ℤ) % q := h2
            exact_mod_cast h3
          simp only at h
          rw [← Nat.div_add_mod m q, ← Nat.div_add_mod m' q, h, hmod]
    _ = Q := Finset.card_range Q

section RootBound2

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Uniform bound**: `N_{p^a}(n) ≤ 8|n|` for `n ≠ 0`, every `a`. -/
theorem rootCard_le {n : ℤ} (hn : n ≠ 0) (a : ℕ) [NeZero (p ^ a)] :
    rootCard n (p ^ a) ≤ 8 * n.natAbs := by
  set e := padicValNat p (4 * n.natAbs) with he
  have h4n : 0 < 4 * n.natAbs := by positivity
  have hpe : p ^ e ≤ 4 * n.natAbs := Nat.le_of_dvd h4n pow_padicValNat_dvd
  rw [rootCard_eq_card_range]
  by_cases hae : a ≤ e
  · calc _ ≤ (Finset.range (p ^ a)).card := Finset.card_filter_le _ _
      _ = p ^ a := Finset.card_range _
      _ ≤ p ^ e := Nat.pow_le_pow_right hp.out.pos hae
      _ ≤ 8 * n.natAbs := by omega
  push Not at hae
  set F := (Finset.range (p ^ a)).filter fun m : ℕ => ((p ^ a : ℕ) : ℤ) ∣ n - (m : ℤ) ^ 2
  rcases F.eq_empty_or_nonempty with hF | ⟨m₀, hm₀⟩
  · rw [hF]; simp
  set q := p ^ (a - e)
  have hpa : p ^ a = p ^ e * q := by rw [← pow_add]; congr 1; omega
  set A := (Finset.range (p ^ e * q)).filter fun m : ℕ => (q : ℤ) ∣ (m₀ : ℤ) - m
  set B := (Finset.range (p ^ e * q)).filter fun m : ℕ => (q : ℤ) ∣ (-(m₀ : ℤ)) - m
  have hsub : F ⊆ A ∪ B := by
    intro m hm
    simp only [F, Finset.mem_filter, Finset.mem_range] at hm hm₀
    have hX : (p : ℤ) ^ a ∣ (m₀ : ℤ) ^ 2 - n := by
      have := hm₀.2; push_cast at this; rw [← neg_sub]; exact (dvd_neg).2 this
    have hY : (p : ℤ) ^ a ∣ (m : ℤ) ^ 2 - n := by
      have := hm.2; push_cast at this; rw [← neg_sub]; exact (dvd_neg).2 this
    have hmr : m < p ^ e * q := hpa ▸ hm.1
    rcases pm_classes hn hX hY with h | h
    · refine Finset.mem_union_left _ ?_
      simp only [A, Finset.mem_filter, Finset.mem_range]
      exact ⟨hmr, by push_cast [q]; exact h⟩
    · refine Finset.mem_union_right _ ?_
      simp only [B, Finset.mem_filter, Finset.mem_range]
      refine ⟨hmr, ?_⟩
      have : (q : ℤ) ∣ -((m₀ : ℤ) + m) := (dvd_neg).2 (by push_cast [q]; exact h)
      rw [show -(m₀ : ℤ) - m = -((m₀ : ℤ) + m) by ring]; exact this
  calc F.card ≤ (A ∪ B).card := Finset.card_le_card hsub
    _ ≤ A.card + B.card := Finset.card_union_le _ _
    _ ≤ p ^ e + p ^ e := add_le_add (card_class_le q _ _) (card_class_le q _ _)
    _ ≤ 8 * n.natAbs := by omega

end RootBound2

end GaloisForLFunctions.RHTower.HalfWeight
