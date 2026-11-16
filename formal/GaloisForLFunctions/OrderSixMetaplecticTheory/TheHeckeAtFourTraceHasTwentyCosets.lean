import GaloisForLFunctions.OrderSixMetaplecticTheory.TheHeckeAtFourTraceIsAutomorphicOnTheCubicCover

/-!
# The Hecke-at-four trace has twenty cosets

Reduction modulo the inert prime `2` sends `O = ℤ[ω]` onto `𝔽₄ = 𝔽₂[ω]` (`red`, `two_dvd_iff`). A left coset
`γΓ_A` of `Γ_A = Γ(3) ∩ {2 ∣ b, 2 ∣ c}` is determined by the two columns of `γ` as points of `P¹(𝔽₄)`
(`columnPair`): `Γ_A` is the stabilizer of the pair `(∞, 0)` (`columnPair_mul_of_mem`, `mem_of_columnPair_eq`),
and the two columns of a matrix of determinant `1` are distinct points. The twenty representatives

`T_{3t}`, `W T_{3t}` (`W = [[−2, 3], [3, −5]]`), `L_u T_{3t}` (`L_u = [[1, 0], [3u, 1]]`),   `t ∈ {0, 1, ω, ω²}`, `u ∈ {1, ω, ω²}`,

realize the twenty ordered pairs of distinct points (`cosetPoint_injective`, `exists_cosetPoint`), and all have
`κ = 1`. Hence (`heckeFourTrace_eq_sum`)

`Tr F_Θ(w) = Σ_t F_Θ(T_{3t} w) + Σ_t F_Θ(W T_{3t} w) + Σ_{u, t} F_Θ(L_u T_{3t} w)`.
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicJacobi MetaplecticMobiusDescent.CubicEisenstein

/-! ### Reduction modulo two -/

/-- `𝔽₄ = 𝔽₂[ω]` in the basis `1, ω`. -/
abbrev F4 := ZMod 2 × ZMod 2

/-- Multiplication of `𝔽₄` (`ω² = 1 + ω`). -/
def f4mul (p q : F4) : F4 := (p.1 * q.1 + p.2 * q.2, p.1 * q.2 + p.2 * q.1 + p.2 * q.2)

/-- Reduction `O → O/2O = 𝔽₄` in the coordinates `x = a + bω`. -/
def red (x : O) : F4 := ((((Coordinates.coords x).1 : ℤ) : ZMod 2), (((Coordinates.coords x).2 : ℤ) : ZMod 2))

theorem red_eval (a b : ℤ) : red (Coordinates.eval a b) = ((a : ZMod 2), (b : ZMod 2)) := by
  simp [red, Coordinates.coords_eval]

theorem eval_add (a b c d : ℤ) :
    Coordinates.eval a b + Coordinates.eval c d = Coordinates.eval (a + c) (b + d) := by
  simp only [Coordinates.eval]
  push_cast
  ring

theorem red_add (x y : O) : red (x + y) = red x + red y := by
  obtain ⟨a, b, rfl⟩ := Coordinates.exists_coordinates x
  obtain ⟨c, d, rfl⟩ := Coordinates.exists_coordinates y
  change red (Coordinates.eval a b + Coordinates.eval c d) = red (Coordinates.eval a b) + red (Coordinates.eval c d)
  rw [eval_add, red_eval, red_eval, red_eval]
  ext <;> simp

theorem red_neg (x : O) : red (-x) = red x := by
  obtain ⟨a, b, rfl⟩ := Coordinates.exists_coordinates x
  change red (-Coordinates.eval a b) = red (Coordinates.eval a b)
  rw [show -Coordinates.eval a b = Coordinates.eval (-a) (-b) by simp only [Coordinates.eval]; push_cast; ring,
    red_eval, red_eval]
  ext <;> push_cast <;> exact CharTwo.neg_eq _

theorem red_sub (x y : O) : red (x - y) = red x + red y := by
  rw [sub_eq_add_neg, red_add, red_neg]

theorem red_mul (x y : O) : red (x * y) = f4mul (red x) (red y) := by
  obtain ⟨a, b, rfl⟩ := Coordinates.exists_coordinates x
  obtain ⟨c, d, rfl⟩ := Coordinates.exists_coordinates y
  change red (Coordinates.eval a b * Coordinates.eval c d) =
    f4mul (red (Coordinates.eval a b)) (red (Coordinates.eval c d))
  rw [Coordinates.eval_mul, red_eval, red_eval, red_eval]
  simp only [f4mul]
  ext <;> push_cast <;> simp only [CharTwo.sub_eq_add]

theorem red_intCast (n : ℤ) : red (n : O) = ((n : ZMod 2), 0) := by
  have h : (n : O) = Coordinates.eval n 0 := by simp [Coordinates.eval]
  rw [h, red_eval]
  simp

theorem red_one : red 1 = (1, 0) := by
  simpa using red_intCast 1

theorem red_two : red 2 = 0 := by
  have h := red_intCast 2
  simp only [Int.cast_ofNat] at h
  rw [h]
  decide

theorem red_three : red 3 = (1, 0) := by
  have h := red_intCast 3
  simp only [Int.cast_ofNat] at h
  rw [h]
  decide

theorem red_omega : red omega = (0, 1) := by
  have h : omega = Coordinates.eval 0 1 := by simp [Coordinates.eval]
  rw [h, red_eval]
  simp

theorem red_omega_sq : red (omega ^ 2) = (1, 1) := by
  have h : omega ^ 2 = Coordinates.eval (-1) (-1) := by
    simp only [Coordinates.eval]
    push_cast
    linear_combination omega_sq_add
  rw [h, red_eval]
  ext <;> decide

/-- `2 ∣ x` exactly when `x` reduces to `0` in `𝔽₄`. -/
theorem two_dvd_iff (x : O) : (2 : O) ∣ x ↔ red x = 0 := by
  obtain ⟨a, b, rfl⟩ := Coordinates.exists_coordinates x
  change (2 : O) ∣ Coordinates.eval a b ↔ red (Coordinates.eval a b) = 0
  rw [red_eval, Prod.mk_eq_zero, ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨c, d, rfl⟩ := Coordinates.exists_coordinates y
    have h2 : (2 : O) * ((c : O) + (d : O) * omega) = Coordinates.eval (2 * c) (2 * d) := by
      simp only [Coordinates.eval]
      push_cast
      ring
    rw [h2] at hy
    have hc := congrArg Coordinates.coords hy
    rw [Coordinates.coords_eval, Coordinates.coords_eval, Prod.mk.injEq] at hc
    exact ⟨⟨c, by exact_mod_cast hc.1⟩, ⟨d, by exact_mod_cast hc.2⟩⟩
  · rintro ⟨⟨c, rfl⟩, ⟨d, rfl⟩⟩
    exact ⟨Coordinates.eval c d, by simp only [Coordinates.eval]; push_cast; ring⟩

/-! ### Points of `P¹(𝔽₄)` -/

/-- The point `[p : q] ∈ P¹(𝔽₄)`: `∞` if `q = 0`, else `p/q = p q²`. -/
def ptF (p q : F4) : Option F4 := if q = 0 then none else some (f4mul p (f4mul q q))

/-- Scaling a column by a unit does not move its point. -/
theorem ptF_scale : ∀ s p q : F4, s ≠ 0 → ptF (f4mul p s) (f4mul q s) = ptF p q := by
  unfold ptF f4mul
  decide

/-- Two nonzero columns give the same point exactly when their cross product vanishes. -/
theorem ptF_eq_iff : ∀ p q p' q' : F4, (p, q) ≠ (0, 0) → (p', q') ≠ (0, 0) →
    (ptF p q = ptF p' q' ↔ f4mul p q' + f4mul q p' = 0) := by
  unfold ptF f4mul
  decide

/-- The columns of a determinant-one matrix are nonzero. -/
theorem col_ne_zero : ∀ p q r s : F4, f4mul p s + f4mul q r = (1, 0) → (p, r) ≠ (0, 0) ∧ (q, s) ≠ (0, 0) := by
  unfold f4mul
  decide

/-- The columns of a determinant-one matrix are distinct points. -/
theorem ptF_ne_of_det : ∀ p q r s : F4, f4mul p s + f4mul q r = (1, 0) → ptF p r ≠ ptF q s := by
  unfold ptF f4mul
  decide

/-- The pair of points `(γ∞, γ0)` given by the columns of `γ` modulo `2`. -/
def columnPair (γ : levelThree) : Option F4 × Option F4 :=
  (ptF (red ((γ : SL(2, O)) 0 0)) (red ((γ : SL(2, O)) 1 0)),
    ptF (red ((γ : SL(2, O)) 0 1)) (red ((γ : SL(2, O)) 1 1)))

theorem red_det (γ : levelThree) :
    f4mul (red ((γ : SL(2, O)) 0 0)) (red ((γ : SL(2, O)) 1 1)) +
      f4mul (red ((γ : SL(2, O)) 0 1)) (red ((γ : SL(2, O)) 1 0)) = (1, 0) := by
  have hdet : (γ : SL(2, O)) 0 0 * (γ : SL(2, O)) 1 1 - (γ : SL(2, O)) 0 1 * (γ : SL(2, O)) 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact (γ : SL(2, O)).det_coe
  have h := congrArg red hdet
  rwa [red_sub, red_mul, red_mul, red_one] at h

theorem columnPair_ne (γ : levelThree) : (columnPair γ).1 ≠ (columnPair γ).2 :=
  ptF_ne_of_det _ _ _ _ (red_det γ)

theorem f4mul_zero_right (p : F4) : f4mul p 0 = 0 := by
  simp [f4mul]

/-- Right multiplication by `Γ_A` fixes the column pair. -/
theorem columnPair_mul_of_mem (γ δ : levelThree) (hδ : δ ∈ fourCorrelationGroup) :
    columnPair (γ * δ) = columnPair γ := by
  have hb : red ((δ : SL(2, O)) 0 1) = 0 := (two_dvd_iff _).mp hδ.1
  have hc : red ((δ : SL(2, O)) 1 0) = 0 := (two_dvd_iff _).mp hδ.2
  have hd := red_det δ
  rw [hb, hc, f4mul_zero_right, add_zero] at hd
  have hs₁ : red ((δ : SL(2, O)) 0 0) ≠ 0 := by
    intro h
    rw [h] at hd
    revert hd
    simp [f4mul]
  have hs₂ : red ((δ : SL(2, O)) 1 1) ≠ 0 := by
    intro h
    rw [h, f4mul_zero_right] at hd
    exact absurd hd (by decide)
  simp only [columnPair, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    red_add, red_mul, hb, hc, f4mul_zero_right, add_zero, zero_add]
  rw [ptF_scale _ _ _ hs₁, ptF_scale _ _ _ hs₂]

/-- Equal column pairs give the same coset. -/
theorem mem_of_columnPair_eq (γ γ' : levelThree) (h : columnPair γ = columnPair γ') :
    γ⁻¹ * γ' ∈ fourCorrelationGroup := by
  have hγ := red_det γ
  have hγ' := red_det γ'
  obtain ⟨h1, h2⟩ := Prod.mk.injEq _ _ _ _ ▸ h
  have c1 := col_ne_zero _ _ _ _ hγ
  have c1' := col_ne_zero _ _ _ _ hγ'
  have e1 := (ptF_eq_iff _ _ _ _ c1.1 c1'.1).mp h1
  have e2 := (ptF_eq_iff _ _ _ _ c1.2 c1'.2).mp h2
  refine ⟨(two_dvd_iff _).mpr ?_, (two_dvd_iff _).mpr ?_⟩
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.SL2_inv_expl, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, red_add, red_neg, red_mul]
    first | exact e2 | (rw [add_comm]; exact e2)
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.SL2_inv_expl, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, red_add, red_neg, red_mul]
    first | exact e1 | (rw [add_comm]; exact e1)

/-! ### Twenty representatives -/

theorem red_zero : red 0 = 0 := by
  have h := red_intCast 0
  simp only [Int.cast_zero] at h
  rw [h]
  rfl

theorem red_five : red 5 = (1, 0) := by
  have h := red_intCast 5
  simp only [Int.cast_ofNat] at h
  rw [h]
  decide

/-- `t ∈ {0, 1, ω, ω²}`, the residues modulo `2`. -/
def tO : Fin 4 → O := ![0, 1, omega, omega ^ 2]

/-- `u ∈ {1, ω, ω²}`, the units modulo `2`. -/
def uO : Fin 3 → O := ![1, omega, omega ^ 2]

/-- The residues `0, 1, ω, ω²` in `𝔽₄`. -/
def tF : Fin 4 → F4 := ![(0, 0), (1, 0), (0, 1), (1, 1)]

/-- The units `1, ω, ω²` in `𝔽₄`. -/
def uF : Fin 3 → F4 := ![(1, 0), (0, 1), (1, 1)]

theorem red_tO (x : Fin 4) : red (tO x) = tF x := by
  fin_cases x
  · exact red_zero
  · exact red_one
  · exact red_omega
  · exact red_omega_sq

theorem red_uO (k : Fin 3) : red (uO k) = uF k := by
  fin_cases k
  · exact red_one
  · exact red_omega
  · exact red_omega_sq

/-- `T_{3t} = [[1, 3t], [0, 1]]`. -/
def transThree (t : O) : levelThree :=
  ⟨⟨!![1, 3 * t; 0, 1], by simp [Matrix.det_fin_two_of]⟩,
    levelThree_of_entries _ (by
      intro i j
      fin_cases i <;> fin_cases j <;> simp)⟩

/-- `L_c = [[1, 0], [3c, 1]]`. -/
def lowerThree (c : O) : levelThree :=
  ⟨⟨!![1, 0; 3 * c, 1], by simp [Matrix.det_fin_two_of]⟩,
    levelThree_of_entries _ (by
      intro i j
      fin_cases i <;> fin_cases j <;> simp)⟩

/-- `W = [[−2, 3], [3, −5]]`. -/
def wMat : levelThree :=
  ⟨⟨!![-2, 3; 3, -5], by rw [Matrix.det_fin_two_of]; norm_num⟩,
    levelThree_of_entries _ (by
      intro i j
      fin_cases i <;> fin_cases j
      · exact ⟨-1, by simp; ring⟩
      · exact ⟨1, by simp⟩
      · exact ⟨1, by simp⟩
      · exact ⟨-2, by simp; ring⟩)⟩

/-- The twenty cosets: `(∞, t)`, `(t + 1, ∞)` and `(t + u², t)`. -/
abbrev CosetIndex := Fin 4 ⊕ Fin 4 ⊕ (Fin 3 × Fin 4)

/-- The representatives `T_{3t}`, `W T_{3t}`, `L_u T_{3t}`. -/
def cosetRep : CosetIndex → levelThree
  | .inl x => transThree (tO x)
  | .inr (.inl x) => wMat * transThree (tO x)
  | .inr (.inr (k, x)) => lowerThree (uO k) * transThree (tO x)

/-- The column pair of `δ_i⁻¹`. -/
def cosetPoint : CosetIndex → Option F4 × Option F4
  | .inl x => (none, some (tF x))
  | .inr (.inl x) => (some (tF x + (1, 0)), none)
  | .inr (.inr (k, x)) => (some (f4mul (f4mul (uF k) (tF x) + (1, 0)) (f4mul (uF k) (uF k))), some (tF x))

theorem cosetPoint_injective : Function.Injective cosetPoint := by
  unfold Function.Injective cosetPoint tF uF f4mul
  decide

theorem exists_cosetPoint : ∀ p : Option F4 × Option F4, p.1 ≠ p.2 → ∃ i, cosetPoint i = p := by
  unfold cosetPoint tF uF f4mul
  decide

theorem columnPair_inv (δ : levelThree) : columnPair δ⁻¹ =
    (ptF (red ((δ : SL(2, O)) 1 1)) (red ((δ : SL(2, O)) 1 0)),
      ptF (red ((δ : SL(2, O)) 0 1)) (red ((δ : SL(2, O)) 0 0))) := by
  simp [columnPair, Matrix.SpecialLinearGroup.SL2_inv_expl, red_neg]

theorem columnPair_rep_inv (i : CosetIndex) : columnPair (cosetRep i)⁻¹ = cosetPoint i := by
  rw [columnPair_inv]
  rcases i with x | x | ⟨k, x⟩
  · simp only [cosetRep, transThree, cosetPoint, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      red_mul, red_one, red_zero, red_three, red_tO]
    fin_cases x <;> decide
  · simp only [cosetRep, transThree, wMat, cosetPoint, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      red_add, red_mul, red_neg, red_one, red_zero, red_two, red_three, red_five, red_tO]
    fin_cases x <;> decide
  · simp only [cosetRep, transThree, lowerThree, cosetPoint, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      red_add, red_mul, red_one, red_zero, red_three, red_tO, red_uO]
    fin_cases k <;> fin_cases x <;> decide

/-- The coset `δ_i⁻¹ Γ_A`. -/
def cosetOf (i : CosetIndex) : levelThree ⧸ fourCorrelationGroup := ((cosetRep i)⁻¹ : levelThree)

theorem cosetOf_bijective : Function.Bijective cosetOf := by
  constructor
  · intro i j h
    apply cosetPoint_injective
    rw [← columnPair_rep_inv i, ← columnPair_rep_inv j]
    have h' := QuotientGroup.eq.mp h
    have := columnPair_mul_of_mem (cosetRep i)⁻¹ _ h'
    rw [mul_inv_cancel_left] at this
    exact this.symm
  · intro q
    obtain ⟨i, hi⟩ := exists_cosetPoint (columnPair q.out) (columnPair_ne _)
    refine ⟨i, ?_⟩
    rw [← QuotientGroup.out_eq' q, cosetOf, QuotientGroup.eq]
    exact mem_of_columnPair_eq _ _ (by rw [columnPair_rep_inv, hi])

/-! ### The representatives have trivial multiplier -/

theorem lambda_sq_dvd_neg_three : lambda ^ 2 ∣ (-3 : O) := by
  refine ⟨omega ^ 2, ?_⟩
  rw [CubicRamified.lambda_sq_eq]
  linear_combination (3 : O) * omega_primitive.pow_eq_one

theorem complexCharacter_transThree (t : O) : complexCharacter (transThree t) = 1 := by
  change ringComplex (value (transThree t)) = 1
  rw [value_zero_lower_left _ (by simp [transThree]), map_one]

theorem complexCharacter_lowerThree (c : O) : complexCharacter (lowerThree c) = 1 := by
  change ringComplex (symbol (3 * c) 1) = 1
  rw [symbol_one, map_one]

theorem complexCharacter_wMat : complexCharacter wMat = 1 := by
  change ringComplex (symbol 3 (-2)) = 1
  have h := CubicEisenstein.RationalSource.integer_symbol_eq_one 3 (-2) (by
    push_cast
    rw [show (-2 : O) - 1 = -3 by ring]
    exact lambda_sq_dvd_neg_three) (by decide)
  push_cast at h
  rw [h, map_one]

theorem complexCharacter_cosetRep (i : CosetIndex) : complexCharacter (cosetRep i) = 1 := by
  rcases i with x | x | ⟨k, x⟩
  · exact complexCharacter_transThree _
  · rw [cosetRep, map_mul, complexCharacter_wMat, complexCharacter_transThree, mul_one]
  · rw [cosetRep, map_mul, complexCharacter_lowerThree, complexCharacter_transThree, mul_one]

/-- **The Hecke-at-four trace over the twenty representatives.** -/
theorem heckeFourTrace_eq_sum (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (w : HyperbolicSpace) :
    heckeFourTrace Θ w = ∑ i : CosetIndex, heckeFourCorrelation Θ (complexMatrix (cosetRep i) • w) := by
  have hF : ∀ δ ∈ fourCorrelationGroup, ∀ x, heckeFourCorrelation Θ (complexMatrix δ • x) =
      kubotaSquare δ * heckeFourCorrelation Θ x := fun δ hδ x => by
    rw [kubotaSquare_apply]
    exact heckeFourCorrelation_automorphy Θ hΘ δ hδ x
  unfold heckeFourTrace cosetTrace
  rw [← cosetOf_bijective.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cosetTerm_congr hF w (γ := (cosetOf i).out) (γ' := (cosetRep i)⁻¹) (QuotientGroup.out_eq' _)]
  unfold cosetTerm
  rw [inv_inv, kubotaSquare_apply, map_inv, complexCharacter_cosetRep i, inv_one, one_pow, one_mul]

end GaloisForLFunctions.OrderSixMetaplecticTheory
