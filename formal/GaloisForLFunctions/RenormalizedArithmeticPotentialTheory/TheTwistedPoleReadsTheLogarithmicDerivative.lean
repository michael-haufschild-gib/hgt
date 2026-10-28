import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheResidueFinitePartIsDiagonalizedByCharacters

/-!
# The twisted pole reads the logarithmic derivative

The residue finite part is diagonalized by the characters mod `q`
(`sum_residueFinitePart_mul_char`). Read on a single profile: the pole twisted by `Re χ`,
`x_n = Re χ(n) n^{−1/2} 𝟙_{n ≤ M}`, has horizon form `2 Re(−L′/L(1, χ)) |x|² + o(mass)`.

* **Unit poles** (`unitPole`, `sum_unitPole_sq`, `atomicWeilForm_unitPole_eq`): for `f` on the units,
  `x = Σ_u f(u) w_u^{(M)}` has mass `Σ_u f(u)² S_u(M)` and expands over the residue Grams.
* **Eigenprofiles** (`exists_abs_atomicWeilForm_unitPole_sub_le`): if `|f| ≤ 1`, `Σ_u f(u) = 0` and
  `Σ_v (c_{u⁻¹v} + c_{v⁻¹u}) f(v) = 2β f(u)`, then `|P_N(x) − 2β |x|²| ≤ η H_M + C`. The mean zero
  removes the divergence, the eigenvalue relation turns the finite part into a scalar.
* **The twisted pole** (`charPole_eq`, `exists_abs_atomicWeilForm_charPole_sub_le`): `Re χ` is such
  an eigenprofile for every `χ ≠ 1`, with `β = Re β_χ = Re(−L′/L(1, χ))`
  (`charPole_finitePart_eq_logDeriv`), and the twisted pole is `Re χ(n) u^{(M)}_n` pointwise.

For `ζ` the pole carries the divergence `ℓ²` and the finite part `−2γ`. A twisted pole carries no
divergence, and its finite part is `2 Re(−L′/L(1, χ))` per unit of mass, for every modulus and
every non-trivial character, real or complex.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics

variable {q : ℕ} [NeZero q]

/-- The **unit pole** `x = Σ_{u ∈ (ℤ/q)ˣ} f(u) w_u^{(M)}`. -/
def unitPole (f : (ZMod q)ˣ → ℝ) (M n : ℕ) : ℝ :=
  ∑ u : (ZMod q)ˣ, f u * residuePole q u M n

/-- On an integer of the class `u₀` the unit pole is `f(u₀) w_{u₀}^{(M)}`; elsewhere it vanishes. -/
theorem unitPole_eq (f : (ZMod q)ˣ → ℝ) (M n : ℕ) :
    unitPole f M n = if h : IsUnit (n : ZMod q) then f h.unit * truncPole M n else 0 := by
  rw [unitPole]
  split_ifs with hn
  · rw [sum_eq_single hn.unit]
    · simp [residuePole, IsUnit.unit_spec]
    · intro u _ hu
      have hne : (n : ZMod q) ≠ u := fun h => hu (Units.ext (by rw [IsUnit.unit_spec, h]))
      simp [residuePole, hne]
    · simp
  · refine sum_eq_zero fun u _ => ?_
    have hne : (n : ZMod q) ≠ u := fun h => hn (h ▸ u.isUnit)
    simp [residuePole, hne]

/-- **The mass of a unit pole**: `|x|² = Σ_u f(u)² S_u(M)`. -/
theorem sum_unitPole_sq (f : (ZMod q)ˣ → ℝ) {M N : ℕ} (hMN : M ≤ N) :
    ∑ n ∈ Icc 1 N, unitPole f M n ^ 2 = ∑ u : (ZMod q)ˣ, f u ^ 2 * classHarmonic q u M := by
  have hpt : ∀ n ∈ Icc 1 N, unitPole f M n ^ 2 =
      ∑ u : (ZMod q)ˣ, f u ^ 2 *
        (if n ≤ M then (if (n : ZMod q) = u then 1 / (n : ℝ) else 0) else 0) := by
    intro n _
    rw [unitPole_eq]
    by_cases hu : IsUnit (n : ZMod q)
    · rw [dif_pos hu, sum_eq_single hu.unit]
      · simp only [IsUnit.unit_spec, if_true, truncPole]
        by_cases hnM : n ≤ M
        · rw [if_pos hnM, if_pos hnM, mul_pow, poleVector_sq]
        · rw [if_neg hnM, if_neg hnM]
          ring
      · intro u _ hne
        have h : (n : ZMod q) ≠ u := fun h => hne (Units.ext (by rw [IsUnit.unit_spec, h]))
        simp [h]
      · simp
    · rw [dif_neg hu, zero_pow two_ne_zero]
      symm
      refine sum_eq_zero fun u _ => ?_
      have h : (n : ZMod q) ≠ u := fun h => hu (h ▸ u.isUnit)
      simp [h]
  rw [sum_congr rfl hpt, sum_comm]
  refine sum_congr rfl fun u _ => ?_
  rw [← mul_sum, classHarmonic, ← sum_truncate hMN]

/-- The unit pole expands over pairs of residue Grams. -/
theorem atomicWeilForm_unitPole_eq (f : (ZMod q)ˣ → ℝ) (M N : ℕ) :
    atomicWeilForm N (unitPole f M) = ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ, f u * f v *
      primeBilinear N (residuePole q u M) (residuePole q v M) := by
  have hL : ∀ y, primeBilinear N (unitPole f M) y =
      ∑ u : (ZMod q)ˣ, f u * primeBilinear N (residuePole q u M) y := fun y =>
    primeBilinear_fintype_sum_left N f (fun u => residuePole q u M) y
  rw [atomicWeilForm_eq_primeBilinear, hL]
  refine sum_congr rfl fun u _ => ?_
  rw [primeBilinear_comm, hL, mul_sum]
  refine sum_congr rfl fun v _ => ?_
  rw [primeBilinear_comm]
  ring

/-- **Eigenprofiles have a scalar finite part**: if `|f| ≤ 1`, `Σ_u f(u) = 0` and
`Σ_v (c_{u⁻¹v} + c_{v⁻¹u}) f(v) = 2β f(u)`, then for every `η > 0` there is `C` with
`|P_N(x) − 2β |x|²| ≤ η H_M + C` for the unit pole `x` and `1 ≤ M ≤ N`. -/
theorem exists_abs_atomicWeilForm_unitPole_sub_le (f : (ZMod q)ˣ → ℝ) (hf1 : ∀ u, |f u| ≤ 1)
    (hf0 : ∑ u : (ZMod q)ˣ, f u = 0) {β : ℝ}
    (heig : ∀ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ, (classMertensConstant q ↑(u⁻¹ * v) +
      classMertensConstant q ↑(v⁻¹ * u)) * f v = 2 * β * f u) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, ∀ M N : ℕ, 1 ≤ M → M ≤ N →
      |atomicWeilForm N (unitPole f M) - 2 * β * ∑ n ∈ Icc 1 N, unitPole f M n ^ 2| ≤
        η * harmonicSum M + C := by
  have hφ0 : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hcard : (Fintype.card (ZMod q)ˣ : ℝ) = q.totient := by
    rw [ZMod.card_units_eq_totient]
  -- a uniform Gram constant over all pairs of units
  have hex : ∀ u v : (ZMod q)ˣ, ∃ C : ℝ, ∀ M M' N : ℕ, 1 ≤ M → M ≤ M' → M' ≤ N →
      |primeBilinear N (residuePole q u M) (residuePole q v M') -
          (q : ℝ) / q.totient * classHarmonic q u M * classHarmonic q v M' -
          classMertensConstant q ((u : ZMod q)⁻¹ * v) * classHarmonic q u M -
          classMertensConstant q ((v : ZMod q)⁻¹ * u) * classHarmonic q v M| ≤
        η / (q.totient : ℝ) ^ 2 * harmonicSum M + C := fun u v =>
    exists_abs_residueGram_finitePart_le u.isUnit v.isUnit (by positivity)
  choose Cg hCg using hex
  -- the constants
  let E : ℝ := 2 * q + 1
  let B : ℝ := ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ, |Cg u v|
  let B₂ : ℝ := ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ, (|classMertensConstant q ↑(u⁻¹ * v)| +
    |classMertensConstant q ↑(v⁻¹ * u)|) * E
  refine ⟨B + (q : ℝ) * q.totient * E ^ 2 + B₂ + 2 * |β| * q.totient * E,
    fun M N hM hMN => ?_⟩
  have hE0 : 0 ≤ E := by positivity
  -- the class sums around their mean `log M/q`
  have he : ∀ u : (ZMod q)ˣ, |classHarmonic q u M - Real.log M / q| ≤ E := fun u =>
    abs_classHarmonic_sub_log_le (u : ZMod q) M
  -- the Gram remainders
  have hR : ∀ u v : (ZMod q)ˣ, |primeBilinear N (residuePole q u M) (residuePole q v M) -
      (q : ℝ) / q.totient * classHarmonic q u M * classHarmonic q v M -
      classMertensConstant q ↑(u⁻¹ * v) * classHarmonic q u M -
      classMertensConstant q ↑(v⁻¹ * u) * classHarmonic q v M| ≤
        η / (q.totient : ℝ) ^ 2 * harmonicSum M + |Cg u v| := by
    intro u v
    have h := hCg u v M M N hM le_rfl hMN
    rw [ZMod.inv_coe_unit, ← Units.val_mul, ZMod.inv_coe_unit, ← Units.val_mul] at h
    exact h.trans (by linarith [le_abs_self (Cg u v)])
  -- the polar functional is bounded, since `Σ f = 0`
  have hℓ : |∑ u : (ZMod q)ˣ, f u * classHarmonic q u M| ≤ q.totient * E := by
    have : ∑ u : (ZMod q)ˣ, f u * classHarmonic q u M =
        ∑ u : (ZMod q)ˣ, f u * (classHarmonic q u M - Real.log M / q) := by
      have h0 : ∑ u : (ZMod q)ˣ, f u * (Real.log M / q) = 0 := by rw [← sum_mul, hf0, zero_mul]
      rw [← sub_zero (∑ u : (ZMod q)ˣ, f u * classHarmonic q u M), ← h0, ← sum_sub_distrib]
      exact sum_congr rfl fun u _ => by ring
    rw [this]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ u : (ZMod q)ˣ, |f u * (classHarmonic q u M - Real.log M / q)|
        ≤ ∑ _u : (ZMod q)ˣ, E := sum_le_sum fun u _ => by
          rw [abs_mul]
          calc |f u| * |classHarmonic q u M - Real.log M / q| ≤ 1 * E :=
                mul_le_mul (hf1 u) (he u) (abs_nonneg _) zero_le_one
            _ = E := one_mul E
      _ = q.totient * E := by rw [sum_const, card_univ, nsmul_eq_mul, hcard]
  -- the identity: `P − 2β|x|² = Σ f f R + (q/φ) ℓ² + Σ f f (c₁ e_u + c₂ e_v) − 2β Σ f² e`
  have hid : atomicWeilForm N (unitPole f M) - 2 * β * ∑ n ∈ Icc 1 N, unitPole f M n ^ 2 =
      ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ, f u * f v *
        (primeBilinear N (residuePole q u M) (residuePole q v M) -
          (q : ℝ) / q.totient * classHarmonic q u M * classHarmonic q v M -
          classMertensConstant q ↑(u⁻¹ * v) * classHarmonic q u M -
          classMertensConstant q ↑(v⁻¹ * u) * classHarmonic q v M) +
      (q : ℝ) / q.totient * (∑ u : (ZMod q)ˣ, f u * classHarmonic q u M) ^ 2 +
      ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ, f u * f v *
        (classMertensConstant q ↑(u⁻¹ * v) * (classHarmonic q u M - Real.log M / q) +
          classMertensConstant q ↑(v⁻¹ * u) * (classHarmonic q v M - Real.log M / q)) -
      2 * β * ∑ u : (ZMod q)ˣ, f u ^ 2 * (classHarmonic q u M - Real.log M / q) := by
    rw [atomicWeilForm_unitPole_eq, sum_unitPole_sq f hMN]
    -- the eigenvalue relation: `Σ_{u,v} f_u f_v (c_{u⁻¹v} + c_{v⁻¹u}) = 2β Σ f²`
    have hdiag : ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ, f u * f v *
        (classMertensConstant q ↑(u⁻¹ * v) + classMertensConstant q ↑(v⁻¹ * u)) =
        2 * β * ∑ u : (ZMod q)ˣ, f u ^ 2 := by
      rw [mul_sum]
      refine sum_congr rfl fun u _ => ?_
      calc ∑ v : (ZMod q)ˣ, f u * f v *
            (classMertensConstant q ↑(u⁻¹ * v) + classMertensConstant q ↑(v⁻¹ * u))
          = f u * ∑ v : (ZMod q)ˣ, (classMertensConstant q ↑(u⁻¹ * v) +
              classMertensConstant q ↑(v⁻¹ * u)) * f v := by
            rw [mul_sum]; exact sum_congr rfl fun v _ => by ring
        _ = 2 * β * f u ^ 2 := by rw [heig u]; ring
    have hsq : (q : ℝ) / q.totient * (∑ u : (ZMod q)ˣ, f u * classHarmonic q u M) ^ 2 =
        ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ,
          f u * f v * ((q : ℝ) / q.totient * classHarmonic q u M * classHarmonic q v M) := by
      rw [sq, sum_mul_sum, mul_sum]
      exact sum_congr rfl fun u _ => by
        rw [mul_sum]; exact sum_congr rfl fun v _ => by ring
    have hsplitL : ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ, f u * f v *
        (classMertensConstant q ↑(u⁻¹ * v) * (classHarmonic q u M - Real.log M / q) +
          classMertensConstant q ↑(v⁻¹ * u) * (classHarmonic q v M - Real.log M / q)) =
        ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ, f u * f v *
          (classMertensConstant q ↑(u⁻¹ * v) * classHarmonic q u M +
            classMertensConstant q ↑(v⁻¹ * u) * classHarmonic q v M) -
        Real.log M / q * ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ, f u * f v *
          (classMertensConstant q ↑(u⁻¹ * v) + classMertensConstant q ↑(v⁻¹ * u)) := by
      rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun u _ => by
        rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun v _ => by ring
    have hmassL : ∑ u : (ZMod q)ˣ, f u ^ 2 * (classHarmonic q u M - Real.log M / q) =
        ∑ u : (ZMod q)ˣ, f u ^ 2 * classHarmonic q u M -
          Real.log M / q * ∑ u : (ZMod q)ˣ, f u ^ 2 := by
      rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun u _ => by ring
    rw [hsq, hsplitL, hdiag, hmassL]
    have hG : ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ, f u * f v *
        primeBilinear N (residuePole q u M) (residuePole q v M) =
        ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ, f u * f v *
          (primeBilinear N (residuePole q u M) (residuePole q v M) -
            (q : ℝ) / q.totient * classHarmonic q u M * classHarmonic q v M -
            classMertensConstant q ↑(u⁻¹ * v) * classHarmonic q u M -
            classMertensConstant q ↑(v⁻¹ * u) * classHarmonic q v M) +
        ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ,
          f u * f v * ((q : ℝ) / q.totient * classHarmonic q u M * classHarmonic q v M) +
        ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ, f u * f v *
          (classMertensConstant q ↑(u⁻¹ * v) * classHarmonic q u M +
            classMertensConstant q ↑(v⁻¹ * u) * classHarmonic q v M) := by
      rw [← sum_add_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun u _ => by
        rw [← sum_add_distrib, ← sum_add_distrib]; exact sum_congr rfl fun v _ => by ring
    rw [hG]
    ring
  rw [hid]
  -- bound each piece
  have h1 : |∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ, f u * f v *
      (primeBilinear N (residuePole q u M) (residuePole q v M) -
        (q : ℝ) / q.totient * classHarmonic q u M * classHarmonic q v M -
        classMertensConstant q ↑(u⁻¹ * v) * classHarmonic q u M -
        classMertensConstant q ↑(v⁻¹ * u) * classHarmonic q v M)| ≤ η * harmonicSum M + B := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ,
          (η / (q.totient : ℝ) ^ 2 * harmonicSum M + |Cg u v|) :=
          sum_le_sum fun u _ => (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun v _ => by
            rw [abs_mul, abs_mul]
            calc |f u| * |f v| * _ ≤ 1 * 1 * (η / (q.totient : ℝ) ^ 2 * harmonicSum M +
                  |Cg u v|) :=
                  mul_le_mul (mul_le_mul (hf1 u) (hf1 v) (abs_nonneg _) zero_le_one) (hR u v)
                    (abs_nonneg _) (by norm_num)
              _ = _ := by ring)
      _ = η * harmonicSum M + B := by
          simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, hcard, B]
          field_simp
  have h2 : |(q : ℝ) / q.totient * (∑ u : (ZMod q)ˣ, f u * classHarmonic q u M) ^ 2| ≤
      (q : ℝ) * q.totient * E ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg (sq_nonneg _)]
    have hsq : (∑ u : (ZMod q)ˣ, f u * classHarmonic q u M) ^ 2 ≤ (q.totient * E) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hℓ 2
    calc (q : ℝ) / q.totient * (∑ u : (ZMod q)ˣ, f u * classHarmonic q u M) ^ 2
        ≤ (q : ℝ) / q.totient * (q.totient * E) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (q : ℝ) * q.totient * E ^ 2 := by field_simp
  have h3 : |∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ, f u * f v *
      (classMertensConstant q ↑(u⁻¹ * v) * (classHarmonic q u M - Real.log M / q) +
        classMertensConstant q ↑(v⁻¹ * u) * (classHarmonic q v M - Real.log M / q))| ≤ B₂ := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun u _ =>
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun v _ => ?_))
    rw [abs_mul, abs_mul]
    have hc : |classMertensConstant q ↑(u⁻¹ * v) * (classHarmonic q u M - Real.log M / q) +
        classMertensConstant q ↑(v⁻¹ * u) * (classHarmonic q v M - Real.log M / q)| ≤
        (|classMertensConstant q ↑(u⁻¹ * v)| + |classMertensConstant q ↑(v⁻¹ * u)|) * E := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, add_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (he u) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (he v) (abs_nonneg _))
    calc |f u| * |f v| * _ ≤ 1 * 1 * ((|classMertensConstant q ↑(u⁻¹ * v)| +
          |classMertensConstant q ↑(v⁻¹ * u)|) * E) :=
          mul_le_mul (mul_le_mul (hf1 u) (hf1 v) (abs_nonneg _) zero_le_one) hc (abs_nonneg _)
            (by norm_num)
      _ = _ := by ring
  have h4 : |2 * β * ∑ u : (ZMod q)ˣ, f u ^ 2 * (classHarmonic q u M - Real.log M / q)| ≤
      2 * |β| * q.totient * E := by
    rw [abs_mul, abs_mul, abs_two]
    have : |∑ u : (ZMod q)ˣ, f u ^ 2 * (classHarmonic q u M - Real.log M / q)| ≤
        q.totient * E := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ u : (ZMod q)ˣ, |f u ^ 2 * (classHarmonic q u M - Real.log M / q)|
          ≤ ∑ _u : (ZMod q)ˣ, E := sum_le_sum fun u _ => by
            rw [abs_mul, abs_pow]
            have hf2 : |f u| ^ 2 ≤ 1 := by nlinarith [hf1 u, abs_nonneg (f u)]
            calc |f u| ^ 2 * |classHarmonic q u M - Real.log M / q| ≤ 1 * E :=
                  mul_le_mul hf2 (he u) (abs_nonneg _) zero_le_one
              _ = E := one_mul E
        _ = q.totient * E := by rw [sum_const, card_univ, nsmul_eq_mul, hcard]
    calc 2 * |β| * |∑ u : (ZMod q)ˣ, f u ^ 2 * (classHarmonic q u M - Real.log M / q)|
        ≤ 2 * |β| * (q.totient * E) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * |β| * q.totient * E := by ring
  rw [abs_le] at h1 h2 h3 h4 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]

/-! ### The twisted pole -/

/-- The **twisted pole** `x = Σ_u Re χ(u) w_u^{(M)}`. -/
def charPole (χ : DirichletCharacter ℂ q) (M : ℕ) : ℕ → ℝ :=
  unitPole (fun u : (ZMod q)ˣ => (χ (u : ZMod q)).re) M

/-- The twisted pole is `Re χ(n) u^{(M)}_n`. -/
theorem charPole_eq (χ : DirichletCharacter ℂ q) (M n : ℕ) :
    charPole χ M n = (χ (n : ZMod q)).re * truncPole M n := by
  rw [charPole, unitPole_eq]
  split_ifs with hn
  · rw [IsUnit.unit_spec]
  · rw [MulChar.map_nonunit χ hn, Complex.zero_re, zero_mul]

/-- **The finite part of the twisted pole**: for `χ ≠ 1` and every `η > 0` there is `C` with
`|P_N(x) − 2 Re β_χ |x|²| ≤ η H_M + C` for `1 ≤ M ≤ N`. -/
theorem exists_abs_atomicWeilForm_charPole_sub_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, ∀ M N : ℕ, 1 ≤ M → M ≤ N →
      |atomicWeilForm N (charPole χ M) -
          2 * (residueSpectralValue χ).re * ∑ n ∈ Icc 1 N, charPole χ M n ^ 2| ≤
        η * harmonicSum M + C := by
  refine exists_abs_atomicWeilForm_unitPole_sub_le (fun u : (ZMod q)ˣ => (χ (u : ZMod q)).re)
    (fun u => (Complex.abs_re_le_norm _).trans (DirichletCharacter.norm_le_one χ _)) ?_
    (fun u => ?_) hη
  · rw [← Complex.re_sum, sum_units_char_eq_zero χ hχ, Complex.zero_re]
  · have h := congrArg Complex.re (sum_residueFinitePart_mul_char χ u)
    rw [Complex.re_sum] at h
    simpa only [Complex.re_ofReal_mul] using h

/-- For `χ ≠ 1` the spectral value is `−L′/L(1, χ)`. -/
theorem charPole_finitePart_eq_logDeriv (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    residueSpectralValue χ =
      -deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1 := by
  rw [residueSpectralValue, if_neg hχ, charMertensLimit_eq_neg_logDeriv χ hχ]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
