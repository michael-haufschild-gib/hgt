import GaloisForLFunctions.CountingHolography.TheCountLawAtEveryGenus
import GaloisForLFunctions.ArithmeticScatteringHolography.TheCountLawOfATrueCurve
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The Jacobian count of a bielliptic genus-two curve

**Manin's count at genus two, through the Jacobian.** Let `h = X³ + aX² + bX + c` be separable with
`c ≠ 0`, over a finite field of odd characteristic. The curve

  `C : y² = h(x²)`

has genus two and the involutions `(x, y) ↦ (−x, ±y)`. Its two quotients are elliptic curves:

  `E₁ : y² = h(u)`  (`u = x²`),   `E₂ : y² = u h(u) ≅ y² = m(v)`,  `m = X³ + bX² + acX + c²`,

the second through `v = c/u`, which carries the roots of `h` to the roots of `m`. The Jacobian of `C`
is isogenous to `E₁ × E₂`, and its height is the sum of the heights of the factors. So the count of
`C` is the sum of Manin's two counts (`ArithmeticScatteringHolography.manin_countLaw`): the height of
`y P₀ − x P₁` on each twisted factor over `𝔽_q(T)`.

* **The mirror cubic is separable** (`mirror_coprime`): a common root `v` of `m` and `m'` gives the
  common root `c/v` of `h` and `h'`, through `v³ h(c/v) = c m(v)` and `v² h'(c/v) = 3m(v) − v m'(v)`.
* **The point count of `C` is the sum of the counts of its quotients** (`card_points_bielliptic`):
  `#C_aff = q + S₁ + S₂ − 1`, `S₁ = Σ χ(h(u))`, `S₂ = Σ χ(m(v))`. The squares `x²` cover each `u`
  exactly `1 + χ(u)` times (`sum_sq_eq`), and `u ↦ c/u` carries `χ(u h(u))` to `χ(m(v))`
  (`charSum_mirror`).
* **The count law of `C`, produced by heights** (`bielliptic_countLaw`): `K = K₁ + K₂` obeys the
  parallelogram law with the channel numbers of genus two, `K(0,1) = 2`, `K(1,0) = 2q`,
  `K(1,1) = N_C + (q + 1)`, `N_C = #C_aff + 2` (the two points at infinity). This is the genus-two
  count law of `TheCountLawAtEveryGenus` on a true curve, from the addition laws of `E₁` and `E₂`.
* **Hasse–Weil at genus two from heights** (`bielliptic_weil`): `(q + 1 − N_C)² ≤ 16 q`, and over every
  finite extension (`bielliptic_weil_tower`).

No character-sum bound and no auxiliary polynomial enters: the sign comes from Manin's two counts, and
the character sums only identify `K(1,1)` with the number of points.
-/

open Polynomial Finset

noncomputable section

namespace GaloisForLFunctions.CountingHolography

open ArithmeticScatteringHolography

attribute [local instance] Classical.propDecidable

/-! ### The mirror cubic -/

section Mirror

variable {F : Type*} [Field F]

theorem eval_cubicPoly (a b c t : F) : (cubicPoly a b c).eval t = t ^ 3 + a * t ^ 2 + b * t + c := by
  simp [cubicPoly]

theorem aeval_cubicPoly {K : Type*} [CommRing K] [Algebra F K] (a b c : F) (x : K) :
    aeval x (cubicPoly a b c) =
      x ^ 3 + algebraMap F K a * x ^ 2 + algebraMap F K b * x + algebraMap F K c := by
  simp only [cubicPoly, map_add, map_mul, aeval_X_pow, aeval_X, aeval_C]

theorem aeval_derivative_cubicPoly {K : Type*} [CommRing K] [Algebra F K] (a b c : F) (x : K) :
    aeval x (derivative (cubicPoly a b c)) = 3 * x ^ 2 + 2 * algebraMap F K a * x + algebraMap F K b := by
  simp only [derivative_cubicPoly, map_add, map_mul, aeval_X_pow, aeval_X, aeval_C, map_ofNat]

/-- **The mirror cubic is separable.** If `h = X³ + aX² + bX + c` is separable and `c ≠ 0`, so is
`m = X³ + bX² + acX + c²`, whose roots are the `c/u` for the roots `u` of `h`. -/
theorem mirror_coprime {a b c : F} (hc : c ≠ 0)
    (hcop : IsCoprime (cubicPoly a b c) (derivative (cubicPoly a b c))) :
    IsCoprime (cubicPoly b (a * c) (c ^ 2)) (derivative (cubicPoly b (a * c) (c ^ 2))) := by
  rw [isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := F) (AlgebraicClosure F)] at hcop
  rw [isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := F) (AlgebraicClosure F)]
  intro v
  by_contra hv
  rw [not_or, not_not, not_not, aeval_cubicPoly, aeval_derivative_cubicPoly] at hv
  obtain ⟨hm, hm'⟩ := hv
  set α := algebraMap F (AlgebraicClosure F) a
  set β := algebraMap F (AlgebraicClosure F) b
  set γ := algebraMap F (AlgebraicClosure F) c
  have hγ : γ ≠ 0 := (_root_.map_ne_zero _).mpr hc
  simp only [map_mul, map_pow] at hm hm'
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hγ (pow_eq_zero_iff two_ne_zero |>.mp (by linear_combination hm))
  -- `u = γ/v` is a common root of `h` and `h'`
  have key := hcop (γ / v)
  rw [aeval_cubicPoly, aeval_derivative_cubicPoly] at key
  rcases key with h | h
  · apply h
    have e : (γ / v) ^ 3 + α * (γ / v) ^ 2 + β * (γ / v) + γ =
        γ * (v ^ 3 + β * v ^ 2 + α * γ * v + γ ^ 2) / v ^ 3 := by
      field_simp
      ring
    rw [e, hm, mul_zero, zero_div]
  · apply h
    have e : 3 * (γ / v) ^ 2 + 2 * α * (γ / v) + β =
        (3 * (v ^ 3 + β * v ^ 2 + α * γ * v + γ ^ 2) - v * (3 * v ^ 2 + 2 * β * v + α * γ)) / v ^ 2 := by
      field_simp
      ring
    rw [e, hm, hm', mul_zero, mul_zero, sub_zero, zero_div]

end Mirror

/-! ### Counting the points of `C` -/

section Count

variable {F : Type*} [Field F] [Fintype F]

local notation "χ" => quadraticChar F

/-- The squares cover `u` exactly `1 + χ(u)` times: `Σ_x f(x²) = Σ_u (1 + χ(u)) f(u)`. -/
theorem sum_sq_eq (hF : ringChar F ≠ 2) (f : F → ℤ) :
    ∑ x : F, f (x ^ 2) = ∑ u : F, (χ u + 1) * f u := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := (univ : Finset F)) (t := univ) (g := fun x => x ^ 2)
    (fun _ _ => mem_univ _) (fun x => f (x ^ 2))]
  refine Finset.sum_congr rfl fun u _ => ?_
  have h1 : ∑ x ∈ univ.filter (fun x : F => x ^ 2 = u), f (x ^ 2) =
      ((univ.filter (fun x : F => x ^ 2 = u)).card : ℤ) * f u := by
    rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2]), Finset.sum_const,
      nsmul_eq_mul]
  rw [h1]
  congr 1
  have := quadraticChar_card_sqrts hF u
  rw [Set.toFinset_setOf] at this
  exact_mod_cast this

/-- **The substitution `u = c/v`.** With `c ≠ 0`, `Σ_u χ(u h(u)) = Σ_v χ(m(v)) − 1`. -/
theorem charSum_mirror {a b c : F} (hc : c ≠ 0) :
    ∑ u : F, χ (u * (cubicPoly a b c).eval u) =
      ∑ v : F, χ ((cubicPoly b (a * c) (c ^ 2)).eval v) - 1 := by
  simp only [eval_cubicPoly]
  have hm0 : χ (0 ^ 3 + b * 0 ^ 2 + a * c * 0 + c ^ 2) = 1 := by
    rw [show (0 : F) ^ 3 + b * 0 ^ 2 + a * c * 0 + c ^ 2 = c ^ 2 by ring, quadraticChar_sq_one' hc]
  have hsplit (f : F → ℤ) : ∑ u : F, f u = f 0 + ∑ u ∈ univ.erase 0, f u :=
    (Finset.add_sum_erase _ _ (mem_univ 0)).symm
  rw [hsplit (fun u => χ (u * (u ^ 3 + a * u ^ 2 + b * u + c))),
    hsplit (fun v => χ (v ^ 3 + b * v ^ 2 + a * c * v + c ^ 2)), hm0]
  simp only [zero_mul, quadraticChar_zero, zero_add, add_sub_cancel_left]
  -- `u ↦ c/u` is a bijection of the nonzero elements
  refine Finset.sum_nbij' (fun u => c / u) (fun v => c / v) ?_ ?_ ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_erase, mem_univ, and_true] at hu ⊢
    exact div_ne_zero hc hu
  · intro v hv
    simp only [Finset.mem_erase, mem_univ, and_true] at hv ⊢
    exact div_ne_zero hc hv
  · intro u hu
    simp only [Finset.mem_erase, mem_univ, and_true] at hu
    field_simp
  · intro v hv
    simp only [Finset.mem_erase, mem_univ, and_true] at hv
    field_simp
  · intro u hu
    simp only [Finset.mem_erase, mem_univ, and_true] at hu
    -- `u h(u) = m(c/u) (u²/c)²`
    have key : u * (u ^ 3 + a * u ^ 2 + b * u + c) =
        ((c / u) ^ 3 + b * (c / u) ^ 2 + a * c * (c / u) + c ^ 2) * (u ^ 2 / c) ^ 2 := by
      field_simp
      ring
    rw [key, map_mul, quadraticChar_sq_one' (div_ne_zero (pow_ne_zero 2 hu) hc), mul_one]

/-- **The point count of `C : y² = h(x²)` is the sum of the counts of its quotients.** -/
theorem card_points_bielliptic (hF : ringChar F ≠ 2) {a b c : F} (hc : c ≠ 0) :
    ((univ.filter fun p : F × F => p.2 ^ 2 = (cubicPoly a b c).eval (p.1 ^ 2)).card : ℤ) =
      Fintype.card F + ∑ u : F, χ ((cubicPoly a b c).eval u) +
        ∑ v : F, χ ((cubicPoly b (a * c) (c ^ 2)).eval v) - 1 := by
  have hcount := GaloisForLFunctions.RHTower.Hyperelliptic.card_points_eq hF
    ((cubicPoly a b c).comp (X ^ 2))
  simp only [eval_comp, eval_pow, eval_X] at hcount
  rw [hcount, sum_sq_eq hF (fun u => χ ((cubicPoly a b c).eval u))]
  have hmul : ∀ u : F, (χ u + 1) * χ ((cubicPoly a b c).eval u) =
      χ (u * (cubicPoly a b c).eval u) + χ ((cubicPoly a b c).eval u) := by
    intro u
    rw [map_mul (quadraticChar F) u]
    ring
  simp only [hmul, Finset.sum_add_distrib, charSum_mirror hc]
  ring

/-! ### The count law, from the two heights -/

/-- **The count law of a bielliptic genus-two curve, produced by the heights of its Jacobian.** For a
separable cubic `h = X³ + aX² + bX + c` with `c ≠ 0` over a finite field of odd characteristic, the sum
`K = K₁ + K₂` of Manin's height counts on the two elliptic quotients of `C : y² = h(x²)` obeys the
parallelogram law, with the genus-two channel numbers `K(0,1) = 2`, `K(1,0) = 2q`,
`K(1,1) = N_C + (q + 1)`, where `N_C` counts the affine points and the two points at infinity. -/
theorem bielliptic_countLaw (hF : ringChar F ≠ 2) {a b c : F} (hc : c ≠ 0)
    (hcop : IsCoprime (cubicPoly a b c) (derivative (cubicPoly a b c))) :
    ∃ K : ℤ → ℤ → ℕ, CountLaw K ∧ K 0 1 = 2 ∧ K 1 0 = 2 * Fintype.card F ∧
      (K 1 1 : ℤ) = ((univ.filter fun p : F × F =>
          p.2 ^ 2 = (cubicPoly a b c).eval (p.1 ^ 2)).card + 2 : ℕ) + (Fintype.card F + 1) := by
  obtain ⟨K₁, hK₁, h01₁, h10₁, h11₁⟩ := manin_countLaw hF hcop
  obtain ⟨K₂, hK₂, h01₂, h10₂, h11₂⟩ := manin_countLaw hF (mirror_coprime hc hcop)
  refine ⟨fun x y => K₁ x y + K₂ x y, fun x y u v => ?_, by simp only [h01₁, h01₂],
    by simp only [h10₁, h10₂]; ring, ?_⟩
  · have e₁ := hK₁ x y u v
    have e₂ := hK₂ x y u v
    push_cast
    linear_combination e₁ + e₂
  · -- `K(1,1) = N₁ + N₂ = N_C + (q + 1)`
    have s₁ := sum_compl_eq (a := a) (b := b) (c := c) hF
    have s₂ := sum_compl_eq (a := b) (b := a * c) (c := c ^ 2) hF
    have hC := card_points_bielliptic hF (a := a) (b := b) hc
    simp only [h11₁, h11₂]
    push_cast at s₁ s₂ ⊢
    linear_combination s₁ + s₂ - hC

/-- **Hasse–Weil at genus two from heights**: `(q + 1 − N_C)² ≤ 16 q` for `C : y² = h(x²)`. -/
theorem bielliptic_weil (hF : ringChar F ≠ 2) {a b c : F} (hc : c ≠ 0)
    (hcop : IsCoprime (cubicPoly a b c) (derivative (cubicPoly a b c))) :
    ((Fintype.card F : ℤ) + 1 - ((univ.filter fun p : F × F =>
        p.2 ^ 2 = (cubicPoly a b c).eval (p.1 ^ 2)).card + 2 : ℕ)) ^ 2 ≤ 16 * Fintype.card F := by
  obtain ⟨K, hK, h01, h10, h11⟩ := bielliptic_countLaw hF hc hcop
  set N : ℕ := (univ.filter fun p : F × F => p.2 ^ 2 = (cubicPoly a b c).eval (p.1 ^ 2)).card + 2
  have h := (exists_genusCountLaw_iff (g := 2) (Q := (Fintype.card F : ℤ))
    (a := (Fintype.card F : ℤ) + 1 - N) (by norm_num)).mp
    ⟨K, hK, by exact_mod_cast h01, by rw [h10]; push_cast; ring, by rw [h11]; ring⟩
  linarith

end Count

/-! ### Every level of the tower -/

/-- **Hasse–Weil at every level, from heights.** Over every finite extension `E` of `F`, the curve
`y² = h(x²)` has `(|E| + 1 − N_E)² ≤ 16 |E|`. -/
theorem bielliptic_weil_tower {F : Type*} [Field F] (hF : ringChar F ≠ 2) {a b c : F} (hc : c ≠ 0)
    (hcop : IsCoprime (cubicPoly a b c) (derivative (cubicPoly a b c)))
    (E : Type*) [Field E] [Fintype E] [Algebra F E] :
    ((Fintype.card E : ℤ) + 1 - ((univ.filter fun p : E × E =>
        p.2 ^ 2 = (cubicPoly (algebraMap F E a) (algebraMap F E b) (algebraMap F E c)).eval
          (p.1 ^ 2)).card + 2 : ℕ)) ^ 2 ≤ 16 * Fintype.card E := by
  have hmap : (cubicPoly a b c).map (algebraMap F E) =
      cubicPoly (algebraMap F E a) (algebraMap F E b) (algebraMap F E c) := by
    simp [cubicPoly, Polynomial.map_add, Polynomial.map_mul]
  refine bielliptic_weil (by rwa [← Algebra.ringChar_eq F E]) ((_root_.map_ne_zero _).mpr hc) ?_
  rw [← hmap, Polynomial.derivative_map]
  exact hcop.map (Polynomial.mapRingHom (algebraMap F E))

end GaloisForLFunctions.CountingHolography

end
