import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheOrbitRingWithABaseIsATowerOfLines

/-!
# Riemann–Roch on the tower has the gluing index as its second term

The tower of lines carries an exact count of sections. This file counts the sections that vanish
on the first `K` graphs, and restricts a section to the first graph on which it does not vanish.

* **Bézout in necklace coordinates** (`natCast_dvd_ghostComponent_of_vanish`): an element of the
  arithmetic square that vanishes on the graphs of the proper divisors of `n` has `n ∣ x_n`. The
  zeros forced on `Γ_n` are the whole row of its contacts with the graphs below it,
  `Σ_{d ∣ n, d < n} Λ(n/d) = log n`.
* **The triangular pigeonhole** (`exists_fiber_of_triangular`): for values `v_n(x)`, `n ≤ K`,
  bounded by `B_n` and glued in this way, a set `T` contains a subset on which all `v_n` are
  constant, of at least `#T / Π_{n ≤ K} (⌊2B_n/n⌋ + 1)` elements. The value vectors lie in the
  lattice of gluing conditions, of index `K!`, and the factor `n` in the denominator is the
  gluing condition of `Γ_n`.
* **Riemann–Roch** (`exists_orbitLatticeMap_vanishing`): on the level `M`, with `b` digits in
  `[−A, A]` on each of the `τ(M)` lines, a nonzero section vanishing on `Γ_1, …, Γ_K` exists as
  soon as `Π_{n ≤ K} (⌊2B_n/n⌋ + 1) < (A + 1)^{bτ(M)}`, `B_n = σ(M)·b·A·q^{bn}` the size of a
  section on `Γ_n`. In logarithms: the count of the class minus the degrees of the class on the
  graphs plus `log K!`.
* **Bézout** (`exists_first_graph`, `exists_orbitLatticeMap_first_graph`): a nonzero section
  vanishes on `Γ_d` for `d < n` and not on `Γ_n` for some `n`, and there `n ≤ |x_n|`. For the
  section of Riemann–Roch `n > K` and `n ≤ |x_n| ≤ σ(M)·b·A·q^{bn}`: the contact `log n` against
  a height of the size `n·b·log q`. On the tower the two axioms hold and their conclusion is the
  product formula.
-/

open Finset Polynomial

noncomputable section

namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

open AbsoluteGeometryOfSpecZ

/-! ### Bézout in necklace coordinates -/

/-- An element that vanishes on the graphs of the proper divisors of `n` has no closed points of
the degrees properly dividing `n`. -/
theorem coord_eq_zero_of_vanish (z : ghostRing) (n : ℕ)
    (h : ∀ d : ℕ+, (d : ℕ) ∣ n → (d : ℕ) < n → ghostComponent d z = 0) :
    ∀ d : ℕ, d ∣ n → d < n → 0 < d → coord z d = 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hdn hlt hd
    obtain ⟨D, rfl⟩ : ∃ D : ℕ+, (D : ℕ) = d := ⟨⟨d, hd⟩, rfl⟩
    have h0 := h D hdn hlt
    rw [ghostComponent_eq_sum_coord, sum_divisors_eq_add_self _ D.ne_zero,
      Finset.sum_eq_zero fun e he => by
        obtain ⟨he1, he2⟩ := Nat.mem_properDivisors.mp he
        rw [ih e he2 (he1.trans hdn) (he2.trans hlt) (Nat.pos_of_dvd_of_pos he1 hd), mul_zero],
      zero_add] at h0
    exact (mul_eq_zero.mp h0).resolve_left (by exact_mod_cast D.ne_zero)

/-- **Bézout in necklace coordinates.** An element of the arithmetic square that vanishes on
the graphs of the proper divisors of `n` has `n ∣ x_n`. -/
theorem natCast_dvd_ghostComponent_of_vanish (z : ghostRing) (n : ℕ+)
    (h : ∀ d : ℕ+, (d : ℕ) ∣ n → (d : ℕ) < n → ghostComponent d z = 0) :
    ((n : ℕ) : ℤ) ∣ ghostComponent n z := by
  rw [ghostComponent_eq_sum_coord, sum_divisors_eq_add_self _ n.ne_zero,
    Finset.sum_eq_zero fun e he => by
      obtain ⟨he1, he2⟩ := Nat.mem_properDivisors.mp he
      rw [coord_eq_zero_of_vanish z n h e he1 he2 (Nat.pos_of_dvd_of_pos he1 n.pos), mul_zero],
    zero_add]
  exact dvd_mul_right _ _

/-- **The first graph of a nonzero element.** A nonzero element of the arithmetic square
vanishes on `Γ_d` for `d < n` and not on `Γ_n` for some `n`, and there `n ∣ x_n`. -/
theorem exists_first_graph {x : ghostRing} (hx : x ≠ 0) :
    ∃ n : ℕ+, ghostComponent n x ≠ 0 ∧ (∀ d : ℕ+, d < n → ghostComponent d x = 0) ∧
      ((n : ℕ) : ℤ) ∣ ghostComponent n x := by
  classical
  have hex : ∃ k : ℕ, ∃ h : 0 < k, ghostComponent ⟨k, h⟩ x ≠ 0 := by
    by_contra hnone
    refine hx (ghostRing_ext fun n => ?_)
    rw [map_zero]
    by_contra hne
    exact hnone ⟨n, n.pos, hne⟩
  obtain ⟨hk, hne⟩ := Nat.find_spec hex
  have hmin : ∀ d : ℕ+, (d : ℕ) < Nat.find hex → ghostComponent d x = 0 := by
    intro d hd
    by_contra hd'
    exact Nat.find_min hex hd ⟨d.pos, hd'⟩
  refine ⟨⟨Nat.find hex, hk⟩, hne, fun d hd => hmin d hd, ?_⟩
  exact natCast_dvd_ghostComponent_of_vanish x ⟨Nat.find hex, hk⟩ fun d _ hd => hmin d hd

/-- The size of a nonzero element on its first graph is at least the degree of the graph. -/
theorem natCast_le_abs_ghostComponent {x : ghostRing} {n : ℕ+}
    (hne : ghostComponent n x ≠ 0) (hdvd : ((n : ℕ) : ℤ) ∣ ghostComponent n x) :
    ((n : ℕ) : ℤ) ≤ |ghostComponent n x| :=
  Int.le_of_dvd (abs_pos.mpr hne) ((dvd_abs _ _).mpr hdvd)

/-! ### The triangular pigeonhole -/

/-- Two integers in `[−B, B]` that are congruent modulo `n` and have the same quotient after the
shift by `B` are equal. -/
theorem eq_of_dvd_of_div_eq {n B : ℕ} {a a' : ℤ} (ha : |a| ≤ B) (ha' : |a'| ≤ B)
    (hdvd : (n : ℤ) ∣ a - a') (hq : (a + B).toNat / n = (a' + B).toNat / n) : a = a' := by
  have h0 : 0 ≤ a + B := by linarith [(abs_le.mp ha).1]
  have h0' : 0 ≤ a' + B := by linarith [(abs_le.mp ha').1]
  have e : ((a + B).toNat : ℤ) = a + B := Int.toNat_of_nonneg h0
  have e' : ((a' + B).toNat : ℤ) = a' + B := Int.toNat_of_nonneg h0'
  have hmod : (a' + B).toNat ≡ (a + B).toNat [MOD n] := by
    rw [Nat.modEq_iff_dvd, e, e']
    have : a + B - (a' + B) = a - a' := by ring
    rwa [this]
  have heq : (a + B).toNat = (a' + B).toNat := by
    rw [← Nat.div_add_mod (a + B).toNat n, ← Nat.div_add_mod (a' + B).toNat n, hq, hmod.symm]
  have : a + B = a' + B := by rw [← e, ← e', heq]
  linarith

/-- **The triangular pigeonhole.** Let the values `v_n`, `1 ≤ n ≤ K`, on a finite set `T` be
bounded by `B_n` and glued: if `v_d(x) = v_d(y)` for the proper divisors `d` of `n`, then
`n ∣ v_n(x) − v_n(y)`. Then `T` has a subset `U` on which every `v_n` is constant, with
`#T ≤ #U · Π_{n ≤ K} (⌊2B_n/n⌋ + 1)`. -/
theorem exists_fiber_of_triangular {α : Type*} [DecidableEq α] (v : ℕ → α → ℤ) (B : ℕ → ℕ) :
    ∀ (K : ℕ) (T : Finset α),
      (∀ n ∈ Icc 1 K, ∀ x ∈ T, |v n x| ≤ B n) →
      (∀ n ∈ Icc 1 K, ∀ x ∈ T, ∀ y ∈ T, (∀ d ∈ n.properDivisors, v d x = v d y) →
        (n : ℤ) ∣ v n x - v n y) →
      ∃ U ⊆ T, (∀ x ∈ U, ∀ y ∈ U, ∀ n ∈ Icc 1 K, v n x = v n y) ∧
        T.card ≤ U.card * ∏ n ∈ Icc 1 K, (2 * B n / n + 1) := by
  intro K
  induction K with
  | zero =>
    intro T _ _
    exact ⟨T, Finset.Subset.refl T, fun x _ y _ n hn => by simp at hn, by simp⟩
  | succ K ih =>
    intro T hB hdvd
    have hsub : Icc 1 K ⊆ Icc 1 (K + 1) := Finset.Icc_subset_Icc_right (Nat.le_succ K)
    obtain ⟨U₀, hU₀T, hconst, hcard⟩ := ih T (fun n hn => hB n (hsub hn))
      (fun n hn => hdvd n (hsub hn))
    have hK1 : K + 1 ∈ Icc 1 (K + 1) := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
    -- the quotient of the shifted value on the last graph
    set g : α → ℕ := fun x => (v (K + 1) x + B (K + 1)).toNat / (K + 1) with hg
    have hmaps : ∀ x ∈ U₀, g x ∈ range (2 * B (K + 1) / (K + 1) + 1) := by
      intro x hx
      have hb := hB (K + 1) hK1 x (hU₀T hx)
      have h2 : (v (K + 1) x + B (K + 1)).toNat ≤ 2 * B (K + 1) := by
        have : v (K + 1) x + B (K + 1) ≤ ((2 * B (K + 1) : ℕ) : ℤ) := by
          push_cast
          linarith [(abs_le.mp hb).2]
        exact Int.toNat_le.mpr this
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right h2))
    obtain ⟨y₀, -, hmax⟩ := Finset.exists_max_image (range (2 * B (K + 1) / (K + 1) + 1))
      (fun a => (U₀.filter fun x => g x = a).card) ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
    have hfib : U₀.card ≤ (U₀.filter fun x => g x = y₀).card *
        (range (2 * B (K + 1) / (K + 1) + 1)).card :=
      Finset.card_le_mul_card_image_of_maps_to hmaps _ hmax
    rw [Finset.card_range] at hfib
    refine ⟨U₀.filter fun x => g x = y₀, (Finset.filter_subset _ _).trans hU₀T, ?_, ?_⟩
    · intro x hx y hy n hn
      obtain ⟨hx0, hxg⟩ := Finset.mem_filter.mp hx
      obtain ⟨hy0, hyg⟩ := Finset.mem_filter.mp hy
      rcases Nat.lt_or_ge n (K + 1) with hlt | hge
      · exact hconst x hx0 y hy0 n (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, by omega⟩)
      · have hnK : n = K + 1 := le_antisymm (Finset.mem_Icc.mp hn).2 hge
        subst hnK
        have hd := hdvd (K + 1) hK1 x (hU₀T hx0) y (hU₀T hy0) fun d hd => by
          obtain ⟨hd1, hd2⟩ := Nat.mem_properDivisors.mp hd
          exact hconst x hx0 y hy0 d (Finset.mem_Icc.mpr
            ⟨Nat.pos_of_dvd_of_pos hd1 (by omega), by omega⟩)
        have hd' : ((K + 1 : ℕ) : ℤ) ∣ v (K + 1) x - v (K + 1) y := hd
        exact eq_of_dvd_of_div_eq (hB (K + 1) hK1 x (hU₀T hx0)) (hB (K + 1) hK1 y (hU₀T hy0)) hd'
          (hxg.trans hyg.symm)
    · rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ K + 1)]
      calc T.card ≤ U₀.card * ∏ n ∈ Icc 1 K, (2 * B n / n + 1) := hcard
        _ ≤ ((U₀.filter fun x => g x = y₀).card * (2 * B (K + 1) / (K + 1) + 1)) *
              ∏ n ∈ Icc 1 K, (2 * B n / n + 1) := Nat.mul_le_mul_right _ hfib
        _ = _ := by ring

/-! ### Riemann–Roch on the tower -/

theorem digitPoly_sub {b : ℕ} (c c' : Fin b → ℤ) :
    digitPoly (c - c') = digitPoly c - digitPoly c' := by
  simp only [digitPoly, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

/-- The sections of a level are additive in their digits. -/
theorem orbitLatticeMap_sub (q : ℤ) (M b : ℕ) (c c' : ↥M.divisors → Fin b → ℤ) :
    orbitLatticeMap q M b (c - c') = orbitLatticeMap q M b c - orbitLatticeMap q M b c' := by
  rw [orbitLatticeMap, orbitLatticeMap, orbitLatticeMap, ← orbitSection_sub]
  congr 1
  funext d
  split_ifs with h
  · exact digitPoly_sub _ _
  · rw [sub_zero]

open Classical in
/-- **Riemann–Roch on the tower.** On the level `M` of the tower with the base `q ≥ 2`, with
`b` digits on each line: if `Π_{n ≤ K} (⌊2B_n/n⌋ + 1) < (A + 1)^{bτ(M)}`, where
`B_n = σ(M)·b·A·q^{bn}`, there is a nonzero section with digits in `[−A, A]` that vanishes on
`Γ_1, …, Γ_K`. -/
theorem exists_orbitLatticeMap_vanishing {q : ℕ} (hq : 2 ≤ q) {M : ℕ} (hM : 0 < M)
    (A b K : ℕ)
    (hcount : ∏ n ∈ Icc 1 K, (2 * ((∑ d ∈ M.divisors, d) * (b * A * (q ^ b) ^ n)) / n + 1) <
      ((A + 1) ^ b) ^ M.divisors.card) :
    ∃ c : ↥M.divisors → Fin b → ℤ, c ≠ 0 ∧ (∀ d j, |c d j| ≤ A) ∧
      orbitLatticeMap (q : ℤ) M b c ≠ 0 ∧
      ∀ n : ℕ+, (n : ℕ) ≤ K → ghostComponent n (orbitLatticeMap (q : ℤ) M b c) = 0 := by
  -- the sections with digits in `[0, A]`
  set T : Finset (↥M.divisors → Fin b → ℤ) :=
    Fintype.piFinset fun _ : ↥M.divisors => Fintype.piFinset fun _ : Fin b =>
      Finset.Icc (0 : ℤ) A with hT
  have hTcard : T.card = ((A + 1) ^ b) ^ M.divisors.card := by
    have hcard : (Finset.Icc (0 : ℤ) A).card = A + 1 := by
      rw [Int.card_Icc]
      omega
    rw [hT, Fintype.card_piFinset]
    simp [Fintype.card_piFinset, hcard]
  have hmemT : ∀ c ∈ T, ∀ d j, 0 ≤ c d j ∧ c d j ≤ A := fun c hc d j =>
    Finset.mem_Icc.mp (Fintype.mem_piFinset.mp (Fintype.mem_piFinset.mp hc d) j)
  -- the values on the graphs
  set v : ℕ → (↥M.divisors → Fin b → ℤ) → ℤ := fun n c =>
    if h : 0 < n then ghostComponent ⟨n, h⟩ (orbitLatticeMap (q : ℤ) M b c) else 0 with hv
  set B : ℕ → ℕ := fun n => (∑ d ∈ M.divisors, d) * (b * A * (q ^ b) ^ n) with hBdef
  have hvB : ∀ n ∈ Icc 1 K, ∀ c ∈ T, |v n c| ≤ B n := by
    intro n hn c hc
    have hn0 : 0 < n := by
      have := (Finset.mem_Icc.mp hn).1
      omega
    have habs : ∀ d j, |c d j| ≤ A := fun d j =>
      abs_le.mpr ⟨by linarith [(hmemT c hc d j).1], (hmemT c hc d j).2⟩
    have h := abs_ghostComponent_orbitLatticeMap_le (by omega : 1 ≤ q) hM habs ⟨n, hn0⟩
    rw [hv]
    simp only [dif_pos hn0]
    rw [hBdef]
    push_cast
    exact h
  have hvdvd : ∀ n ∈ Icc 1 K, ∀ c ∈ T, ∀ c' ∈ T,
      (∀ d ∈ n.properDivisors, v d c = v d c') → (n : ℤ) ∣ v n c - v n c' := by
    intro n hn c _ c' _ hlow
    have hn0 : 0 < n := by
      have := (Finset.mem_Icc.mp hn).1
      omega
    have hz := natCast_dvd_ghostComponent_of_vanish
      (orbitLatticeMap (q : ℤ) M b c - orbitLatticeMap (q : ℤ) M b c') ⟨n, hn0⟩ fun d hd hlt => by
        have h := hlow d (Nat.mem_properDivisors.mpr ⟨hd, hlt⟩)
        rw [hv] at h
        simp only [dif_pos d.pos] at h
        rw [map_sub, sub_eq_zero]
        exact h
    rw [map_sub] at hz
    rw [hv]
    simp only [dif_pos hn0]
    exact hz
  obtain ⟨U, hUT, hconst, hcard⟩ := exists_fiber_of_triangular v B K T hvB hvdvd
  -- two sections with the same values
  have hU : 1 < U.card := by
    by_contra hle
    have h1 : U.card ≤ 1 := not_lt.mp hle
    have h2 : T.card ≤ 1 * ∏ n ∈ Icc 1 K, (2 * B n / n + 1) :=
      hcard.trans (Nat.mul_le_mul_right _ h1)
    rw [one_mul, hTcard] at h2
    exact absurd hcount (not_lt.mpr h2)
  obtain ⟨c₁, hc₁, c₂, hc₂, hne⟩ := Finset.one_lt_card.mp hU
  have hsub : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr hne
  refine ⟨c₁ - c₂, hsub, fun d j => ?_, ?_, fun n hn => ?_⟩
  · have h1 := hmemT c₁ (hUT hc₁) d j
    have h2 := hmemT c₂ (hUT hc₂) d j
    rw [Pi.sub_apply, Pi.sub_apply]
    exact abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
  · intro h0
    have hinj := orbitLatticeMap_injective hq hM b
    have : orbitLatticeMap (q : ℤ) M b (c₁ - c₂) = orbitLatticeMap (q : ℤ) M b 0 := by
      rw [h0]
      have hz := orbitLatticeMap_sub (q : ℤ) M b (0 : ↥M.divisors → Fin b → ℤ) 0
      rw [sub_self, sub_self] at hz
      exact hz.symm
    exact hsub (hinj this)
  · have h := hconst c₁ hc₁ c₂ hc₂ n (Finset.mem_Icc.mpr ⟨n.pos, hn⟩)
    rw [hv] at h
    simp only [dif_pos n.pos] at h
    rw [orbitLatticeMap_sub, map_sub, sub_eq_zero]
    exact h

/-- **Bézout for the section of Riemann–Roch.** The section of
`exists_orbitLatticeMap_vanishing` has a first graph `Γ_n`, `n > K`, on which it does not
vanish, and there `n ≤ |x_n| ≤ σ(M)·b·A·q^{bn}`. -/
theorem exists_orbitLatticeMap_first_graph {q : ℕ} (hq : 2 ≤ q) {M : ℕ} (hM : 0 < M)
    (A b K : ℕ)
    (hcount : ∏ n ∈ Icc 1 K, (2 * ((∑ d ∈ M.divisors, d) * (b * A * (q ^ b) ^ n)) / n + 1) <
      ((A + 1) ^ b) ^ M.divisors.card) :
    ∃ (c : ↥M.divisors → Fin b → ℤ) (n : ℕ+), (∀ d j, |c d j| ≤ A) ∧ K < (n : ℕ) ∧
      (∀ d : ℕ+, d < n → ghostComponent d (orbitLatticeMap (q : ℤ) M b c) = 0) ∧
      ((n : ℕ) : ℤ) ≤ |ghostComponent n (orbitLatticeMap (q : ℤ) M b c)| ∧
      |ghostComponent n (orbitLatticeMap (q : ℤ) M b c)| ≤
        (∑ d ∈ M.divisors, (d : ℤ)) * (b * A * ((q : ℤ) ^ b) ^ (n : ℕ)) := by
  obtain ⟨c, -, hc, hne, hvan⟩ := exists_orbitLatticeMap_vanishing hq hM A b K hcount
  obtain ⟨n, hn, hlow, hdvd⟩ := exists_first_graph hne
  refine ⟨c, n, hc, ?_, hlow, natCast_le_abs_ghostComponent hn hdvd,
    abs_ghostComponent_orbitLatticeMap_le (by omega : 1 ≤ q) hM hc n⟩
  by_contra hle
  exact hn (hvan n (not_lt.mp hle))

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
