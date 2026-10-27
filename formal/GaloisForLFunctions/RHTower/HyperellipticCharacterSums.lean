import GaloisForLFunctions.RHTower.HyperellipticDescent

/-!
# Weil's bound for quadratic character sums of split polynomials

For a finite field `F` of odd characteristic, `q = |F|`, and a nonempty finset `S ⊆ F`,

  `|Σ_{x ∈ F} χ(Π_{c ∈ S} (x − c))| ≤ (|S| − 1) √q`  (`abs_sum_quadraticChar_prod_le`).

For odd `|S|` this is the Hasse–Weil bound of `y² = Π (x − c)` over `F` itself. For even `|S|` the
substitution `x = c₀ + 1/u` at a root `c₀ ∈ S` turns the polynomial into `u^{−|S|}` (a square)
times a constant times `Π_{c ≠ c₀} (u − 1/(c − c₀))`, of odd degree `|S| − 1`; the point `u = 0`
costs `1 ≤ √q`.

With repeated roots (`abs_sum_quadraticChar_multiset_le`): if some root of `Π_{c ∈ s}(x − c)` has
odd multiplicity, the sum is at most `3|s|√q`; the square part is invisible to `χ` off the roots.
-/

open Polynomial Finset

namespace GaloisForLFunctions.RHTower.Hyperelliptic

attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F]

/-- `Π_{c ∈ S} (X − c)`. -/
noncomputable def rootPoly (S : Finset F) : F[X] := ∏ c ∈ S, (X - C c)

omit [Fintype F] in
theorem rootPoly_eval (S : Finset F) (x : F) : (rootPoly S).eval x = ∏ c ∈ S, (x - c) := by
  simp [rootPoly, eval_prod]

omit [Fintype F] in
theorem natDegree_rootPoly (S : Finset F) : (rootPoly S).natDegree = S.card := by
  rw [rootPoly, natDegree_prod_of_monic _ _ fun c _ => monic_X_sub_C c]
  simp

omit [Fintype F] in
theorem squarefree_rootPoly (S : Finset F) : Squarefree (rootPoly S) :=
  (separable_prod_X_sub_C_iff' (f := id).mpr fun _ _ _ _ h => h).squarefree

/-- The odd case: the Hasse–Weil bound over `F` itself. -/
theorem abs_sum_quadraticChar_prod_le_of_odd (hF : ringChar F ≠ 2) {S : Finset F}
    (hS : Odd S.card) :
    ‖∑ x : F, ((quadraticChar F (∏ c ∈ S, (x - c)) : ℤ) : ℂ)‖ ≤
      (S.card - 1 : ℕ) * Real.sqrt (Fintype.card F) := by
  have hodd : Odd (rootPoly S).natDegree := by rwa [natDegree_rootPoly]
  obtain ⟨hcard, hnorm, hsum⟩ := riemannHypothesis_oddHyperelliptic hF (squarefree_rootPoly S) hodd
  have hext : extHyp (E := F) (rootPoly S) =
      ∑ x : F, ((quadraticChar F (∏ c ∈ S, (x - c)) : ℤ) : ℂ) := by
    unfold extHyp
    refine sum_congr rfl fun x _ => ?_
    rw [coe_aeval_eq_eval, rootPoly_eval]
  have h : ∑ x : F, ((quadraticChar F (∏ c ∈ S, (x - c)) : ℤ) : ℂ) = -(lRoots (rootPoly S)).sum := by
    rw [← hext, hsum F, Module.finrank_self]
    simp
  rw [h, norm_neg]
  calc ‖(lRoots (rootPoly S)).sum‖ ≤ ((lRoots (rootPoly S)).map (fun ω => ‖ω‖)).sum :=
        norm_multiset_sum_le _
    _ = ((lRoots (rootPoly S)).map (fun _ => Real.sqrt (Fintype.card F))).sum := by
        congr 1
        exact Multiset.map_congr rfl fun ω hω => hnorm ω hω
    _ = (S.card - 1 : ℕ) * Real.sqrt (Fintype.card F) := by
        rw [Multiset.map_const', Multiset.sum_replicate, hcard, natDegree_rootPoly, nsmul_eq_mul]

omit [Fintype F] in
/-- **The inversion at a root**: for `x ≠ c₀`, `c ≠ c₀`,
`x − c = (x − c₀)(c₀ − c)(1/(x − c₀) − 1/(c − c₀))`. -/
theorem sub_eq_of_inv {c₀ c x : F} (hc : c ≠ c₀) (hx : x ≠ c₀) :
    x - c = (x - c₀) * (c₀ - c) * ((x - c₀)⁻¹ - (c - c₀)⁻¹) := by
  have hx' : x - c₀ ≠ 0 := sub_ne_zero.mpr hx
  have hc' : c - c₀ ≠ 0 := sub_ne_zero.mpr hc
  field_simp
  ring

theorem quadraticChar_pow_even {x : F} (hx : x ≠ 0) {n : ℕ} (hn : Even n) :
    quadraticChar F (x ^ n) = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [← two_mul, pow_mul, map_pow, quadraticChar_sq_one' hx, one_pow]

/-- The even case reduces to the odd case at a root `c₀`: with `T = {1/(c − c₀) : c ≠ c₀}`,
`Σ_x χ(Π_S (x − c)) = χ(Π_{c≠c₀}(c₀ − c)) · (Σ_u χ(Π_T (u − e)) − χ(Π_T (−e)))`. -/
theorem sum_quadraticChar_prod_eq_of_even {S : Finset F} {c₀ : F} (hc₀ : c₀ ∈ S)
    (heven : Even S.card) :
    ∑ x : F, ((quadraticChar F (∏ c ∈ S, (x - c)) : ℤ) : ℂ) =
      ((quadraticChar F (∏ c ∈ S.erase c₀, (c₀ - c)) : ℤ) : ℂ) *
        (∑ u : F, ((quadraticChar F (∏ c ∈ S.erase c₀, (u - (c - c₀)⁻¹)) : ℤ) : ℂ) -
          ((quadraticChar F (∏ c ∈ S.erase c₀, (0 - (c - c₀)⁻¹)) : ℤ) : ℂ)) := by
  set K := ∏ c ∈ S.erase c₀, (c₀ - c)
  set h : F → F := fun u => ∏ c ∈ S.erase c₀, (u - (c - c₀)⁻¹)
  have hpoint : ∀ x, x ≠ c₀ → ((quadraticChar F (∏ c ∈ S, (x - c)) : ℤ) : ℂ) =
      ((quadraticChar F K : ℤ) : ℂ) * ((quadraticChar F (h (x - c₀)⁻¹) : ℤ) : ℂ) := by
    intro x hx
    have hx' : x - c₀ ≠ 0 := sub_ne_zero.mpr hx
    rw [← Finset.mul_prod_erase S _ hc₀,
      Finset.prod_congr rfl fun c hc => sub_eq_of_inv (Finset.ne_of_mem_erase hc) hx,
      Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const]
    have hpow : (x - c₀) * (((x - c₀) ^ (S.erase c₀).card * K) * h (x - c₀)⁻¹) =
        (x - c₀) ^ S.card * K * h (x - c₀)⁻¹ := by
      rw [← Finset.card_erase_add_one hc₀]; ring
    rw [hpow, map_mul, map_mul, quadraticChar_pow_even hx' heven, one_mul]
    push_cast
    rfl
  have hzero : ((quadraticChar F (∏ c ∈ S, (c₀ - c)) : ℤ) : ℂ) = 0 := by
    rw [Finset.prod_eq_zero hc₀ (sub_self c₀), quadraticChar_zero]; simp
  rw [← Finset.sum_erase_add _ _ (mem_univ c₀), hzero, add_zero,
    Finset.sum_congr rfl fun x hx => hpoint x (Finset.ne_of_mem_erase hx), ← Finset.mul_sum]
  congr 1
  rw [← Finset.sum_erase_add _ _ (mem_univ (0 : F)), add_sub_cancel_right]
  refine Finset.sum_nbij' (fun x => (x - c₀)⁻¹) (fun u => c₀ + u⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_erase.mpr ⟨inv_ne_zero (sub_ne_zero.mpr (Finset.ne_of_mem_erase hx)),
      mem_univ _⟩
  · intro u hu
    refine Finset.mem_erase.mpr ⟨fun h0 => ?_, mem_univ _⟩
    have : u⁻¹ = 0 := by linear_combination h0
    exact Finset.ne_of_mem_erase hu (inv_eq_zero.mp this)
  · intro x _
    simp
  · intro u _
    simp
  · intro x _
    rfl

/-- **Weil's bound for split polynomials**: `|Σ_x χ(Π_{c ∈ S} (x − c))| ≤ (|S| − 1) √q` for every
nonempty `S ⊆ F`. -/
theorem abs_sum_quadraticChar_prod_le (hF : ringChar F ≠ 2) {S : Finset F} (hS : S.Nonempty) :
    ‖∑ x : F, ((quadraticChar F (∏ c ∈ S, (x - c)) : ℤ) : ℂ)‖ ≤
      (S.card - 1 : ℕ) * Real.sqrt (Fintype.card F) := by
  rcases Nat.even_or_odd S.card with heven | hodd
  · obtain ⟨c₀, hc₀⟩ := hS
    rw [sum_quadraticChar_prod_eq_of_even hc₀ heven]
    set T := (S.erase c₀).image fun c => (c - c₀)⁻¹
    have hinj : Set.InjOn (fun c => (c - c₀)⁻¹) (S.erase c₀ : Set F) := by
      intro a ha b hb hab
      simpa using hab
    have hT : T.card = S.card - 1 := by
      rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem hc₀]
    have hprod : ∀ u : F, ∏ c ∈ S.erase c₀, (u - (c - c₀)⁻¹) = ∏ e ∈ T, (u - e) := by
      intro u
      rw [Finset.prod_image hinj]
    have hS1 : 1 ≤ S.card := Finset.card_pos.mpr ⟨c₀, hc₀⟩
    have hS2 : 2 ≤ S.card := by
      rcases heven with ⟨k, hk⟩; omega
    have hTodd : Odd T.card := by
      rw [hT]; rcases heven with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
    have hbound := abs_sum_quadraticChar_prod_le_of_odd hF hTodd
    simp_rw [hprod]
    have hχ : ∀ y : F, ‖((quadraticChar F y : ℤ) : ℂ)‖ ≤ 1 := by
      intro y
      rcases quadraticChar_trichotomy F y with h | h | h <;> simp [h]
    have hsq : 1 ≤ Real.sqrt (Fintype.card F) := by
      rw [Real.one_le_sqrt]; exact_mod_cast Fintype.card_pos
    calc ‖((quadraticChar F (∏ c ∈ S.erase c₀, (c₀ - c)) : ℤ) : ℂ) *
          (∑ u : F, ((quadraticChar F (∏ e ∈ T, (u - e)) : ℤ) : ℂ) -
            ((quadraticChar F (∏ e ∈ T, (0 - e)) : ℤ) : ℂ))‖
        ≤ 1 * ((T.card - 1 : ℕ) * Real.sqrt (Fintype.card F) + 1) := by
          rw [norm_mul]
          refine mul_le_mul (hχ _) ((norm_sub_le _ _).trans (add_le_add hbound (hχ _)))
            (norm_nonneg _) zero_le_one
      _ ≤ (S.card - 1 : ℕ) * Real.sqrt (Fintype.card F) := by
          rw [one_mul, hT]
          have : ((S.card - 1 - 1 : ℕ) : ℝ) + 1 = (S.card - 1 : ℕ) := by
            rw [show S.card - 1 = (S.card - 1 - 1) + 1 by omega]; push_cast; ring
          nlinarith [Real.sqrt_nonneg (Fintype.card F)]
  · exact abs_sum_quadraticChar_prod_le_of_odd hF hodd

/-! ### Polynomials with repeated roots -/

/-- The roots of odd multiplicity of a multiset. -/
noncomputable def oddPart (s : Multiset F) : Finset F := s.toFinset.filter fun c => Odd (s.count c)

omit [Fintype F] in
/-- `Π_{c ∈ s} (x − c) = Π_{c odd} (x − c) · B(x)²` with `B(x) = Π_c (x − c)^{⌊count/2⌋}`. -/
theorem prod_map_sub_eq (s : Multiset F) (x : F) :
    (s.map (x - ·)).prod = (∏ c ∈ oddPart s, (x - c)) *
      (∏ c ∈ s.toFinset, (x - c) ^ (s.count c / 2)) ^ 2 := by
  rw [Finset.prod_multiset_map_count, oddPart, Finset.prod_filter, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun c _ => ?_
  rcases Nat.even_or_odd (s.count c) with h | h
  · rw [if_neg (Nat.not_odd_iff_even.mpr h), one_mul, ← pow_mul,
      Nat.div_mul_cancel (even_iff_two_dvd.mp h)]
  · rw [if_pos h, ← pow_mul, ← pow_succ']
    congr 1
    obtain ⟨k, hk⟩ := h
    omega

/-- **Weil's bound with multiplicities**: if some root of `Π_{c ∈ s} (x − c)` has odd
multiplicity, `|Σ_x χ(Π_{c ∈ s}(x − c))| ≤ 3 |s| √q`. Away from the roots the square factor is
invisible to `χ`; the roots cost at most `2|s|`. -/
theorem abs_sum_quadraticChar_multiset_le (hF : ringChar F ≠ 2) {s : Multiset F}
    (hs : ∃ c, Odd (s.count c)) :
    ‖∑ x : F, ((quadraticChar F (s.map (x - ·)).prod : ℤ) : ℂ)‖ ≤
      3 * Multiset.card s * Real.sqrt (Fintype.card F) := by
  set S := oddPart s
  obtain ⟨c, hc⟩ := hs
  have hcS : c ∈ S := by
    refine Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr ?_, hc⟩
    exact Multiset.count_pos.mp (Nat.pos_of_ne_zero fun h => by rw [h] at hc; simp at hc)
  have hSs : S.card ≤ Multiset.card s :=
    (Finset.card_filter_le _ _).trans (Multiset.toFinset_card_le s)
  have hχ : ∀ y : F, ‖((quadraticChar F y : ℤ) : ℂ)‖ ≤ 1 := by
    intro y
    rcases quadraticChar_trichotomy F y with h | h | h <;> simp [h]
  -- away from the roots, `χ(P) = χ(Π_S)`
  have hoff : ∀ x ∉ s.toFinset, ((quadraticChar F (s.map (x - ·)).prod : ℤ) : ℂ) =
      ((quadraticChar F (∏ c ∈ S, (x - c)) : ℤ) : ℂ) := by
    intro x hx
    have hB : ∏ c ∈ s.toFinset, (x - c) ^ (s.count c / 2) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun c hc => pow_ne_zero _ (sub_ne_zero.mpr ?_)
      rintro rfl; exact hx hc
    rw [prod_map_sub_eq, map_mul, quadraticChar_sq_one' hB, mul_one]
  have hsplit : ∀ g : F → ℂ, ∑ x : F, g x =
      ∑ x ∈ s.toFinset, g x + ∑ x ∈ univ.filter (· ∉ s.toFinset), g x := by
    intro g
    rw [← Finset.sum_filter_add_sum_filter_not univ (· ∈ s.toFinset)]
    congr 1
    exact Finset.sum_congr (by ext; simp) fun _ _ => rfl
  have hdiff : ‖∑ x : F, ((quadraticChar F (s.map (x - ·)).prod : ℤ) : ℂ) -
      ∑ x : F, ((quadraticChar F (∏ c ∈ S, (x - c)) : ℤ) : ℂ)‖ ≤ 2 * Multiset.card s := by
    rw [hsplit, hsplit (fun x => ((quadraticChar F (∏ c ∈ S, (x - c)) : ℤ) : ℂ)),
      Finset.sum_congr rfl fun x hx => hoff x (Finset.mem_filter.mp hx).2, add_sub_add_right_eq_sub,
      ← Finset.sum_sub_distrib]
    calc ‖∑ x ∈ s.toFinset, (((quadraticChar F (s.map (x - ·)).prod : ℤ) : ℂ) -
          ((quadraticChar F (∏ c ∈ S, (x - c)) : ℤ) : ℂ))‖
        ≤ ∑ x ∈ s.toFinset, (2 : ℝ) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
          refine (norm_sub_le _ _).trans ?_
          linarith [hχ ((s.map (x - ·)).prod), hχ (∏ c ∈ S, (x - c))]
      _ ≤ 2 * Multiset.card s := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast Multiset.toFinset_card_le s)
            zero_le_two
  have hmain := abs_sum_quadraticChar_prod_le hF ⟨c, hcS⟩
  have hsq : 1 ≤ Real.sqrt (Fintype.card F) := by
    rw [Real.one_le_sqrt]; exact_mod_cast Fintype.card_pos
  have hS' : ((S.card - 1 : ℕ) : ℝ) ≤ Multiset.card s := by
    have : S.card - 1 ≤ Multiset.card s := by omega
    exact_mod_cast this
  calc ‖∑ x : F, ((quadraticChar F (s.map (x - ·)).prod : ℤ) : ℂ)‖
      ≤ ‖∑ x : F, ((quadraticChar F (s.map (x - ·)).prod : ℤ) : ℂ) -
          ∑ x : F, ((quadraticChar F (∏ c ∈ S, (x - c)) : ℤ) : ℂ)‖ +
        ‖∑ x : F, ((quadraticChar F (∏ c ∈ S, (x - c)) : ℤ) : ℂ)‖ := norm_le_norm_sub_add _ _
    _ ≤ 2 * Multiset.card s + (S.card - 1 : ℕ) * Real.sqrt (Fintype.card F) :=
        add_le_add hdiff hmain
    _ ≤ 3 * Multiset.card s * Real.sqrt (Fintype.card F) := by
        have h0 : (0 : ℝ) ≤ Multiset.card s := Nat.cast_nonneg _
        nlinarith [mul_le_mul_of_nonneg_right hS' (Real.sqrt_nonneg (Fintype.card F))]

end GaloisForLFunctions.RHTower.Hyperelliptic
