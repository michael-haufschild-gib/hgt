import GaloisForLFunctions.RHTower.HyperKloostermanRootNumber
import GaloisForLFunctions.RHTower.Sieve.KloostermanSum

open GaloisForLFunctions.RHTower.HyperKloosterman

/-!
# Kloosterman sums to composite moduli

Twisted multiplicativity `S(m, n; qr) = S(r̄m₁, r̄n₁; q) S(q̄m₂, q̄n₂; r)` for coprime `q, r`
(`kloostermanSum_mul`), the stationary-phase identity
`S(m, n; p^k) = Σ_{x unit, p^j(mx - nx⁻¹) = 0} e((mx + nx⁻¹)/p^k)` for `k ≤ 2j` (`kloostermanSum_stationary`,
by averaging over the units `1 + p^j w`), and the resulting bound `|S(m, n; p^k)| ≤ 2 p^j` for odd `p`, a unit
`n`, `k ≤ 2j` and `j < k` (`norm_kloostermanSum_prime_pow_le`): the solutions of `p^j(mx² - n) = 0` lie in the
two cosets `±y + ker(p^j ·)`.
-/

namespace GaloisForLFunctions.RHTower.KloostermanComposite

open RHTower.Sieve

/-- **Twisted multiplicativity.** For coprime `q, r`,
`S(m, n; qr) = S(r̄ m₁, r̄ n₁; q) · S(q̄ m₂, q̄ n₂; r)` with `(m₁, m₂)`, `(n₁, n₂)` the CRT components. -/
theorem kloostermanSum_mul {q r : ℕ} [NeZero q] [NeZero r] (h : q.Coprime r) (m n : ZMod (q * r)) :
    kloostermanSum (q * r) m n =
      kloostermanSum q ((ZMod.chineseRemainder h m).1 * ((r : ZMod q))⁻¹)
          ((ZMod.chineseRemainder h n).1 * ((r : ZMod q))⁻¹) *
        kloostermanSum r ((ZMod.chineseRemainder h m).2 * ((q : ZMod r))⁻¹)
          ((ZMod.chineseRemainder h n).2 * ((q : ZMod r))⁻¹) := by
  set e := ZMod.chineseRemainder h
  unfold kloostermanSum
  rw [Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]
  let E : (ZMod (q * r))ˣ ≃ (ZMod q)ˣ × (ZMod r)ˣ :=
    (Units.mapEquiv e.toMulEquiv).toEquiv.trans MulEquiv.prodUnits.toEquiv
  refine Fintype.sum_equiv E _ _ (fun x => ?_)
  simp only [kloostermanPhase]
  rw [stdAddChar_crt h]
  have hx1 : ((E x).1 : ZMod q) = (e (x : ZMod (q * r))).1 := rfl
  have hx2 : ((E x).2 : ZMod r) = (e (x : ZMod (q * r))).2 := rfl
  have hi1 : (((E x).1⁻¹ : (ZMod q)ˣ) : ZMod q) = (e ((x⁻¹ : (ZMod (q * r))ˣ) : ZMod (q * r))).1 := rfl
  have hi2 : (((E x).2⁻¹ : (ZMod r)ˣ) : ZMod r) = (e ((x⁻¹ : (ZMod (q * r))ˣ) : ZMod (q * r))).2 := rfl
  rw [hx1, hx2, hi1, hi2]
  simp only [map_add, map_mul, Prod.fst_add, Prod.snd_add, Prod.fst_mul, Prod.snd_mul]
  congr 2 <;> ring

/-- **Stationary phase for prime powers.** If `k ≤ 2j`, then
`S(m, n; p^k) = Σ_{x unit, p^j (m x - n x⁻¹) = 0} e((m x + n x⁻¹)/p^k)`. -/
theorem kloostermanSum_stationary (p k j : ℕ) [NeZero (p ^ k)] (hkj : k ≤ 2 * j) (m n : ZMod (p ^ k)) :
    kloostermanSum (p ^ k) m n =
      ∑ x : (ZMod (p ^ k))ˣ, if ((p : ZMod (p ^ k)) ^ j * (m * (x : ZMod (p ^ k)) - n * ((x⁻¹ : (ZMod (p ^ k))ˣ) :
        ZMod (p ^ k)))) = 0 then kloostermanPhase (p ^ k) m n x else 0 := by
  classical
  have hpk : (p : ZMod (p ^ k)) ^ k = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hsq : ∀ w : ZMod (p ^ k), ((p : ZMod (p ^ k)) ^ j * w) ^ 2 = 0 := by
    intro w
    have : ((p : ZMod (p ^ k)) ^ j) ^ 2 = (p : ZMod (p ^ k)) ^ k * (p : ZMod (p ^ k)) ^ (2 * j - k) := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    rw [mul_pow, this, hpk, zero_mul, zero_mul]
  -- the unit `1 + p^j w`
  let uw (w : ZMod (p ^ k)) : (ZMod (p ^ k))ˣ := ⟨1 + (p : ZMod (p ^ k)) ^ j * w, 1 - (p : ZMod (p ^ k)) ^ j * w, by
    linear_combination -(hsq w), by linear_combination -(hsq w)⟩
  have hinv : ∀ (w : ZMod (p ^ k)) (x : (ZMod (p ^ k))ˣ), (((x * uw w)⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) = ((x⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) * (1 - (p : ZMod (p ^ k)) ^ j * w) := by
    intro w x; rw [mul_inv_rev, Units.val_mul, mul_comm]; rfl
  -- average over the shifts
  have havg : ∀ w : ZMod (p ^ k), kloostermanSum (p ^ k) m n =
      ∑ x : (ZMod (p ^ k))ˣ, kloostermanPhase (p ^ k) m n (x * uw w) := by
    intro w
    unfold kloostermanSum
    exact (Fintype.sum_equiv (Equiv.mulRight (uw w)) _ _ (fun x => rfl)).symm
  have hphase : ∀ (w : ZMod (p ^ k)) (x : (ZMod (p ^ k))ˣ), kloostermanPhase (p ^ k) m n (x * uw w) =
      kloostermanPhase (p ^ k) m n x *
        ZMod.stdAddChar (w * ((p : ZMod (p ^ k)) ^ j * (m * (x : ZMod (p ^ k)) - n * ((x⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))))) := by
    intro w x
    unfold kloostermanPhase
    rw [← AddChar.map_add_eq_mul, hinv]
    congr 1
    simp only [uw, Units.val_mul]
    ring
  have hN : (Fintype.card (ZMod (p ^ k)) : ℂ) ≠ 0 := by
    rw [ZMod.card]; exact_mod_cast (NeZero.ne (p ^ k))
  have hsum : (Fintype.card (ZMod (p ^ k)) : ℂ) * kloostermanSum (p ^ k) m n =
      ∑ x : (ZMod (p ^ k))ˣ, kloostermanPhase (p ^ k) m n x *
        ∑ w : ZMod (p ^ k), ZMod.stdAddChar (w * ((p : ZMod (p ^ k)) ^ j * (m * (x : ZMod (p ^ k)) - n * ((x⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))))) := by
    rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    rw [havg w]
    exact Finset.sum_congr rfl (fun x _ => hphase w x)
  simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar (p ^ k))] at hsum
  rw [← mul_right_inj' hN, hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp [mul_comm]

/-- The kernel of multiplication by `p^j` on `ZMod (p^k)` has at most `p^j` elements. -/
theorem card_ker_pow_le (p k j : ℕ) [NeZero (p ^ k)] (hp : 0 < p) (hjk : j ≤ k) :
    (Finset.univ.filter (fun d : ZMod (p ^ k) => (p : ZMod (p ^ k)) ^ j * d = 0)).card ≤ p ^ j := by
  classical
  let φ : Fin (p ^ j) → ZMod (p ^ k) := fun e => ((p ^ (k - j) * e.val : ℕ) : ZMod (p ^ k))
  calc (Finset.univ.filter (fun d : ZMod (p ^ k) => (p : ZMod (p ^ k)) ^ j * d = 0)).card
      ≤ (Finset.univ.image φ).card := by
        apply Finset.card_le_card
        intro d hd
        have h0 := (Finset.mem_filter.mp hd).2
        have hdv : p ^ k ∣ p ^ j * d.val := by
          apply (ZMod.natCast_eq_zero_iff _ _).mp
          push_cast; rw [ZMod.natCast_zmod_val]; exact h0
        have hsplit : p ^ k = p ^ j * p ^ (k - j) := by rw [← pow_add]; congr 1; omega
        have hdv' : p ^ j * p ^ (k - j) ∣ p ^ j * d.val := by rw [← hsplit]; exact hdv
        obtain ⟨e, he⟩ := (Nat.mul_dvd_mul_iff_left (pow_pos hp j)).mp hdv'
        have hlt : e < p ^ j := by
          have hv : d.val < p ^ j * p ^ (k - j) := lt_of_lt_of_eq (ZMod.val_lt d) hsplit
          rw [he, mul_comm (p ^ j)] at hv
          exact Nat.lt_of_mul_lt_mul_left hv
        refine Finset.mem_image.mpr ⟨⟨e, hlt⟩, Finset.mem_univ _, ?_⟩
        simp only [φ]
        rw [← he, ZMod.natCast_zmod_val]
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = p ^ j := by simp

theorem isUnit_of_cast_ne_zero {p k : ℕ} [hp : Fact p.Prime] (hk : 1 ≤ k) {a : ZMod (p ^ k)}
    (ha : ZMod.castHom (dvd_pow_self p (by omega : k ≠ 0)) (ZMod p) a ≠ 0) : IsUnit a := by
  have hval : a = (a.val : ZMod (p ^ k)) := (ZMod.natCast_zmod_val a).symm
  rw [hval, ZMod.isUnit_iff_coprime]
  apply Nat.Coprime.pow_right
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
  intro hd
  apply ha
  rw [hval, map_natCast, ZMod.natCast_eq_zero_iff]
  exact hd

/-- **Kloosterman sums to odd prime powers.** For `k ≤ 2j`, `j < k`, and `n` a unit,
`|S(m, n; p^k)| ≤ 2 p^j`. -/
theorem norm_kloostermanSum_prime_pow_le (p k j : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hkj : k ≤ 2 * j) (hjk : j < k) (m : ZMod (p ^ k)) {n : ZMod (p ^ k)} (hn : IsUnit n) :
    ‖kloostermanSum (p ^ k) m n‖ ≤ 2 * (p : ℝ) ^ j := by
  classical
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hk1 : 1 ≤ k := by omega
  set π := ZMod.castHom (dvd_pow_self p (by omega : k ≠ 0)) (ZMod p)
  set T := Finset.univ.filter (fun x : (ZMod (p ^ k))ˣ =>
    (p : ZMod (p ^ k)) ^ j * (m * (x : ZMod (p ^ k)) - n * ((x⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))) = 0)
  have hS : ‖kloostermanSum (p ^ k) m n‖ ≤ T.card := by
    rw [kloostermanSum_stationary p k j hkj, ← Finset.sum_filter]
    refine (norm_sum_le _ _).trans ?_
    simp [norm_kloostermanPhase, T]
  refine hS.trans ?_
  -- `p^j ≠ 0`
  have hpj : (p : ZMod (p ^ k)) ^ j ≠ 0 := by
    intro h
    have : p ^ k ∣ p ^ j := by rw [← ZMod.natCast_eq_zero_iff]; push_cast; exact h
    have := Nat.le_of_dvd (pow_pos hp.out.pos j) this
    have := Nat.pow_lt_pow_right hp.out.one_lt hjk
    omega
  rcases T.eq_empty_or_nonempty with he | ⟨y, hy⟩
  · rw [he]; simp
  -- the equation `p^j (m x² - n) = 0`
  have heq : ∀ x ∈ T, (p : ZMod (p ^ k)) ^ j * (m * (x : ZMod (p ^ k)) ^ 2 - n) = 0 := by
    intro x hx
    have h := (Finset.mem_filter.mp hx).2
    have := congrArg (· * (x : ZMod (p ^ k))) h
    simp only [zero_mul] at this
    rw [← this]
    have : ((x⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) * x = 1 := by simp
    linear_combination ((p : ZMod (p ^ k)) ^ j * n) * this
  -- `m` is a unit
  have hm : IsUnit m := by
    by_contra hm
    have h := heq y hy
    have hu : IsUnit (m * (y : ZMod (p ^ k)) ^ 2 - n) := by
      apply isUnit_of_cast_ne_zero hk1
      intro h0
      have hmz : π m = 0 := by
        by_contra hmz
        exact hm (isUnit_of_cast_ne_zero hk1 hmz)
      rw [map_sub, map_mul, hmz, zero_mul, zero_sub, neg_eq_zero] at h0
      exact (hn.map π).ne_zero h0
    exact hpj (hu.mul_left_eq_zero.mp h)
  -- kernel set
  set K := Finset.univ.filter (fun d : ZMod (p ^ k) => (p : ZMod (p ^ k)) ^ j * d = 0)
  have hK : K.card ≤ p ^ j := card_ker_pow_le p k j hp.out.pos hjk.le
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : (p : ℕ) ∣ 2 := by rw [← ZMod.natCast_eq_zero_iff]; exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
  have hsub : T.image (fun x : (ZMod (p ^ k))ˣ => (x : ZMod (p ^ k))) ⊆
      K.image (fun d => (y : ZMod (p ^ k)) + d) ∪ K.image (fun d => -(y : ZMod (p ^ k)) + d) := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    have hdiff : (p : ZMod (p ^ k)) ^ j * (m * (((x : ZMod (p ^ k)) - y) * ((x : ZMod (p ^ k)) + y))) = 0 := by
      linear_combination heq x hx - heq y hy
    have hdiff' : (p : ZMod (p ^ k)) ^ j * (((x : ZMod (p ^ k)) - y) * ((x : ZMod (p ^ k)) + y)) = 0 := by
      rw [show (p : ZMod (p ^ k)) ^ j * (m * (((x : ZMod (p ^ k)) - y) * ((x : ZMod (p ^ k)) + y))) =
        m * ((p : ZMod (p ^ k)) ^ j * (((x : ZMod (p ^ k)) - y) * ((x : ZMod (p ^ k)) + y))) by ring] at hdiff
      exact hm.mul_right_eq_zero.mp hdiff
    by_cases hplus : π ((x : ZMod (p ^ k)) + y) = 0
    · -- then `x - y` is a unit
      have hminus : π ((x : ZMod (p ^ k)) - y) ≠ 0 := by
        intro h0
        have hx0 : π (x : ZMod (p ^ k)) ≠ 0 := ((x.isUnit).map π).ne_zero
        apply hx0
        have : π (2 * (x : ZMod (p ^ k))) = 0 := by
          rw [show 2 * (x : ZMod (p ^ k)) = ((x : ZMod (p ^ k)) + y) + ((x : ZMod (p ^ k)) - y) by ring,
            map_add, hplus, h0, add_zero]
        rw [map_mul, map_ofNat] at this
        exact (mul_eq_zero.mp this).resolve_left h2
      have hu := isUnit_of_cast_ne_zero hk1 hminus
      have h' : (p : ZMod (p ^ k)) ^ j * ((x : ZMod (p ^ k)) + y) = 0 := by
        rw [show (p : ZMod (p ^ k)) ^ j * (((x : ZMod (p ^ k)) - y) * ((x : ZMod (p ^ k)) + y)) =
          ((x : ZMod (p ^ k)) - y) * ((p : ZMod (p ^ k)) ^ j * ((x : ZMod (p ^ k)) + y)) by ring] at hdiff'
        exact hu.mul_right_eq_zero.mp hdiff'
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(x : ZMod (p ^ k)) + y,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩, by ring⟩)
    · have hu := isUnit_of_cast_ne_zero hk1 hplus
      have h' : (p : ZMod (p ^ k)) ^ j * ((x : ZMod (p ^ k)) - y) = 0 := by
        rw [show (p : ZMod (p ^ k)) ^ j * (((x : ZMod (p ^ k)) - y) * ((x : ZMod (p ^ k)) + y)) =
          ((x : ZMod (p ^ k)) + y) * ((p : ZMod (p ^ k)) ^ j * ((x : ZMod (p ^ k)) - y)) by ring] at hdiff'
        exact hu.mul_right_eq_zero.mp hdiff'
      refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(x : ZMod (p ^ k)) - y,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩, by ring⟩)
  have hcard : T.card ≤ 2 * p ^ j := by
    rw [← Finset.card_image_of_injective T Units.val_injective]
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ (K.image (fun d => (y : ZMod (p ^ k)) + d)).card + (K.image (fun d => -(y : ZMod (p ^ k)) + d)).card :=
          Finset.card_union_le _ _
      _ ≤ K.card + K.card := add_le_add Finset.card_image_le Finset.card_image_le
      _ ≤ 2 * p ^ j := by omega
  exact_mod_cast hcard

end GaloisForLFunctions.RHTower.KloostermanComposite
