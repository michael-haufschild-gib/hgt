import GaloisForLFunctions.HTGeometry.LegendreHalvingCriterion

/-!
# Coordinates of all halves on a Legendre curve

Let `f : E → L` be a field embedding in characteristic zero and `y² = x(x-1)(x-λ)` a smooth
Legendre curve over `E`.  Its two-torsion is `{0, (0,0), (1,0), (λ,0)}`, so it is rational over
`E` and has four elements.  Consequently a point of the curve over `E` which has a half over `E`
has exactly four halves over `L`: they form one coset of the two-torsion, and every one of them is
the image of a half over `E`.  In particular the coordinates of every half lie in `f(E)`.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.LegendreDoubling
open WeierstrassCurve.Affine

/-! ## Two-torsion -/

section TwoTorsion
variable {L : Type*} [Field L] [CharZero L] [DecidableEq L]

omit [CharZero L] [DecidableEq L] in
theorem curve_nonsingular_root {lam x : L} (hl0 : lam ≠ 0) (hl1 : lam ≠ 1)
    (hx : x = 0 ∨ x = 1 ∨ x = lam) : (curve lam).Nonsingular x 0 := by
  apply (nonsingular_iff' x 0).mpr
  refine ⟨(equation_iff x 0).mpr ?_, Or.inl ?_⟩
  · simp only [curve]
    rcases hx with h | h | h <;> rw [h] <;> ring
  · simp only [curve]
    rcases hx with h | h | h <;> rw [h]
    · simpa using hl0
    · intro h; apply hl1; linear_combination h
    · intro h
      have : lam * (lam - 1) = 0 := by linear_combination -h
      rcases mul_eq_zero.mp this with h0 | h1
      · exact hl0 h0
      · exact hl1 (sub_eq_zero.mp h1)

/-- The finite two-torsion points are exactly `(0,0)`, `(1,0)` and `(λ,0)`. -/
theorem add_self_eq_zero_iff {lam : L} (T : (curve lam).Point) :
    T + T = 0 ↔ T = 0 ∨ ∃ (x : L) (h : (curve lam).Nonsingular x 0),
      (x = 0 ∨ x = 1 ∨ x = lam) ∧ T = Point.some x 0 h := by
  constructor
  · intro hT
    rcases T with _ | ⟨x, y, h⟩
    · exact Or.inl rfl
    right
    have hy : y = (curve lam).negY x y := by
      by_contra hne
      rw [Point.add_self_of_Y_ne hne] at hT
      exact Point.some_ne_zero _ hT
    have hy0 : y = 0 := by
      simp only [curve, negY, zero_mul, sub_zero] at hy
      have : (2 : L) * y = 0 := by linear_combination hy
      exact (mul_eq_zero.mp this).resolve_left two_ne_zero
    subst hy0
    have he := (equation_iff x 0).mp ((nonsingular_iff' x 0).mp h).1
    simp only [curve, zero_mul, add_zero] at he
    have hprod : x * ((x - 1) * (x - lam)) = 0 := by linear_combination -he
    refine ⟨x, h, ?_, rfl⟩
    rcases mul_eq_zero.mp hprod with h0 | h1
    · exact Or.inl h0
    rcases mul_eq_zero.mp h1 with h1 | h2
    · exact Or.inr (Or.inl (sub_eq_zero.mp h1))
    · exact Or.inr (Or.inr (sub_eq_zero.mp h2))
  · rintro (rfl | ⟨x, h, -, rfl⟩)
    · rfl
    · exact Point.add_self_of_Y_eq (by simp [curve, negY])

/-- The two-torsion subgroup has exactly four elements. -/
theorem ncard_twoTorsion {lam : L} (hl0 : lam ≠ 0) (hl1 : lam ≠ 1) :
    {T : (curve lam).Point | T + T = 0}.ncard = 4 := by
  classical
  have h₀ := curve_nonsingular_root hl0 hl1 (Or.inl rfl)
  have h₁ := curve_nonsingular_root hl0 hl1 (Or.inr (Or.inl rfl))
  have hl := curve_nonsingular_root hl0 hl1 (Or.inr (Or.inr rfl))
  have hset : {T : (curve lam).Point | T + T = 0} =
      ↑({0, Point.some 0 0 h₀, Point.some 1 0 h₁, Point.some lam 0 hl} :
        Finset (curve lam).Point) := by
    ext T
    simp only [Set.mem_setOf_eq, add_self_eq_zero_iff, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | ⟨x, h, hx, rfl⟩)
      · exact Or.inl rfl
      · rcases hx with rfl | rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
    · rintro (rfl | rfl | rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr ⟨0, h₀, Or.inl rfl, rfl⟩
      · exact Or.inr ⟨1, h₁, Or.inr (Or.inl rfl), rfl⟩
      · exact Or.inr ⟨lam, hl, Or.inr (Or.inr rfl), rfl⟩
  rw [hset, Set.ncard_coe_finset]
  have hne : ∀ {a b : L} {ha : (curve lam).Nonsingular a 0} {hb : (curve lam).Nonsingular b 0},
      a ≠ b → Point.some a 0 ha ≠ Point.some b 0 hb := fun hab h =>
    hab (Point.some.inj h).1
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
  · exact hne (Ne.symm hl1)
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hne (by norm_num), hne (Ne.symm hl0)⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨(Point.some_ne_zero _).symm, (Point.some_ne_zero _).symm, (Point.some_ne_zero _).symm⟩

/-- A point with one half has exactly four halves. -/
theorem ncard_halves {lam : L} (hl0 : lam ≠ 0) (hl1 : lam ≠ 1) {Q R₀ : (curve lam).Point}
    (hR₀ : R₀ + R₀ = Q) : {R : (curve lam).Point | R + R = Q}.ncard = 4 := by
  have hset : {R : (curve lam).Point | R + R = Q} = (R₀ + ·) '' {T | T + T = 0} := by
    ext R
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro hR
      refine ⟨R - R₀, ?_, by abel⟩
      calc R - R₀ + (R - R₀) = (R + R) - (R₀ + R₀) := by abel
        _ = 0 := by rw [hR, hR₀, sub_self]
    · rintro ⟨T, hT, rfl⟩
      calc R₀ + T + (R₀ + T) = (R₀ + R₀) + (T + T) := by abel
        _ = Q := by rw [hT, hR₀, add_zero]
  rw [hset, Set.ncard_image_of_injective _ (add_right_injective R₀), ncard_twoTorsion hl0 hl1]

end TwoTorsion

/-! ## Coordinatewise images under a field embedding -/

section Map
variable {E L : Type*} [Field E] [Field L] [CharZero E] [CharZero L]

theorem curve_map (f : E →+* L) (lam : E) : (curve lam).map f = curve (f lam) := by
  ext <;> simp [curve, WeierstrassCurve.map]

theorem nonsingular_map_iff (f : E →+* L) {lam : E} {mu : L} (hmu : f lam = mu) (x y : E) :
    (curve mu).Nonsingular (f x) (f y) ↔ (curve lam).Nonsingular x y := by
  subst hmu
  rw [← curve_map]
  exact (curve lam).map_nonsingular f.injective x y

/-- The coordinatewise image of a point of the Legendre curve under a field embedding. -/
def pointMap (f : E →+* L) {lam : E} {mu : L} (hmu : f lam = mu) :
    (curve lam).Point → (curve mu).Point
  | .zero => 0
  | .some x y h => .some (f x) (f y) ((nonsingular_map_iff f hmu x y).mpr h)

variable (f : E →+* L) {lam : E} {mu : L} (hmu : f lam = mu)

@[simp] theorem pointMap_zero : pointMap f hmu 0 = 0 := rfl

@[simp] theorem pointMap_some {x y : E} (h : (curve lam).Nonsingular x y) :
    pointMap f hmu (.some x y h) = .some (f x) (f y) ((nonsingular_map_iff f hmu x y).mpr h) :=
  rfl

theorem pointMap_injective : Function.Injective (pointMap f hmu) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · exact absurd h.symm (Point.some_ne_zero _)
  · exact absurd h (Point.some_ne_zero _)
  · simp only [pointMap_some, Point.some.injEq] at h
    simp only [Point.some.injEq]
    exact ⟨f.injective h.1, f.injective h.2⟩

/-- Points with coordinates in the image are images. -/
theorem exists_pointMap_eq {x y : L} (h : (curve mu).Nonsingular x y) (hx : x ∈ f.range)
    (hy : y ∈ f.range) : ∃ P : (curve lam).Point, pointMap f hmu P = .some x y h := by
  obtain ⟨x', rfl⟩ := hx
  obtain ⟨y', rfl⟩ := hy
  exact ⟨.some x' y' ((nonsingular_map_iff f hmu x' y').mp h), rfl⟩

/-- The coordinates of an image point lie in the image. -/
theorem coordinates_mem_range_of_pointMap {P : (curve lam).Point} {x y : L}
    {h : (curve mu).Nonsingular x y} (hP : pointMap f hmu P = .some x y h) :
    x ∈ f.range ∧ y ∈ f.range := by
  rcases P with _ | ⟨x', y', h'⟩
  · exact absurd hP.symm (Point.some_ne_zero _)
  · simp only [pointMap_some, Point.some.injEq] at hP
    exact ⟨⟨x', hP.1⟩, ⟨y', hP.2⟩⟩

variable [DecidableEq E] [DecidableEq L]

theorem pointMap_add (P Q : (curve lam).Point) :
    pointMap f hmu (P + Q) = pointMap f hmu P + pointMap f hmu Q := by
  subst hmu
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  · rfl
  · rfl
  · have hneg : ∀ x y : E, (curve (f lam)).negY (f x) (f y) = f ((curve lam).negY x y) := by
      intro x y; rw [← curve_map]; exact map_negY f x y
    by_cases hxy : x₁ = x₂ ∧ y₁ = (curve lam).negY x₂ y₂
    · rw [Point.add_of_Y_eq hxy.1 hxy.2, pointMap_zero, pointMap_some, pointMap_some,
        Point.add_of_Y_eq (congrArg f hxy.1) (by rw [hxy.2, hneg])]
    · have hxy' : ¬(f x₁ = f x₂ ∧ f y₁ = (curve (f lam)).negY (f x₂) (f y₂)) := fun h =>
        hxy ⟨f.injective h.1, f.injective (by rw [h.2, hneg])⟩
      rw [Point.add_some hxy, pointMap_some, pointMap_some, pointMap_some, Point.add_some hxy',
        Point.some.injEq]
      have hslope : (curve (f lam)).slope (f x₁) (f x₂) (f y₁) (f y₂) =
          f ((curve lam).slope x₁ x₂ y₁ y₂) := by
        rw [← curve_map]; exact map_slope f x₁ x₂ y₁ y₂
      rw [hslope, ← curve_map, map_addX, map_addY]
      exact ⟨rfl, rfl⟩

omit [DecidableEq E] in
theorem twoTorsion_mem_range {T : (curve mu).Point}
    (hT : T + T = 0) : ∃ T' : (curve lam).Point, pointMap f hmu T' = T := by
  rcases (add_self_eq_zero_iff T).mp hT with rfl | ⟨x, h, hx, rfl⟩
  · exact ⟨0, rfl⟩
  · refine exists_pointMap_eq f hmu h ?_ ⟨0, map_zero f⟩
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, map_zero f⟩
    · exact ⟨1, map_one f⟩
    · exact ⟨lam, hmu⟩

/-- **Every half comes from the base.**  If `P` has a half over `E`, then every half of its image
over `L` is the image of a half over `E`. -/
theorem half_eq_pointMap {P R₀ : (curve lam).Point}
    (hR₀ : R₀ + R₀ = P) {R : (curve mu).Point} (hR : R + R = pointMap f hmu P) :
    ∃ R' : (curve lam).Point, R' + R' = P ∧ pointMap f hmu R' = R := by
  set S := pointMap f hmu R₀
  have hT : (R - S) + (R - S) = 0 := by
    calc (R - S) + (R - S) = (R + R) - (S + S) := by abel
      _ = 0 := by rw [hR, ← pointMap_add, hR₀, sub_self]
  obtain ⟨T', hT'⟩ := twoTorsion_mem_range f hmu hT
  have himage : pointMap f hmu (R₀ + T') = R := by
    rw [pointMap_add, hT']; abel
  refine ⟨R₀ + T', ?_, himage⟩
  apply pointMap_injective f hmu
  rw [pointMap_add, himage, hR]

/-- The coordinates of every half lie in the image of the base field. -/
theorem half_coordinates_mem_range {P R₀ : (curve lam).Point}
    (hR₀ : R₀ + R₀ = P) {x y : L} {h : (curve mu).Nonsingular x y}
    (hR : Point.some x y h + Point.some x y h = pointMap f hmu P) :
    x ∈ f.range ∧ y ∈ f.range := by
  obtain ⟨R', -, hR'⟩ := half_eq_pointMap f hmu hR₀ hR
  exact coordinates_mem_range_of_pointMap f hmu hR'

end Map

end GaloisForLFunctions.HTGeometry.LegendreDoubling
