import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TheCubicCurveCountWithoutWeil
import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TheLFunctionOfACharacterOnASplitPolynomial

/-!
# The cubic norm character sum has the Weil bound

Let `χ ≠ 1` be a cubic character of `F`, `|F| = 3N_F + 1`, and `E/F` an extension with `|E| = s²`.

* **Constancy on cubic classes** (`char_eq_of_pow_eq`): `χ(a) = χ(b)` when `a^{N_F} = b^{N_F}`, since
  then `a/b` is a cube.
* **The norm** (`algebraMap_norm_pow_eq`): `N_{E/F}(y)^{N_F} = y^{N_E}`, `N_E = (|E| − 1)/3`.
* **The bound** (`norm_sum_char_norm_le`): with `a` such that `ζ = χ(a) ≠ 1` and `ε₀ = a^{N_F}`, the sum
  `Σ_{x ∈ E} χ(N f(x))` is `T_1 + ζ T_{ε₀} + ζ² T_{ε₀²}` over the three classes of `f(x)^{N_E}`
  (`sum_char_norm_eq`); `1 + ζ + ζ² = 0` and Stepanov's equidistribution give
  `|Σ_{x ∈ E} χ(N f(x))| ≤ 2(5D + 4)s + 3D` without Weil's theorem.
-/

open Polynomial Finset

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

section

variable {F : Type*} [Field F] [Fintype F] {χ : MulChar F ℂ}

/-- A cubic character is constant on the classes of `a^{(q−1)/3}`. -/
theorem char_eq_of_pow_eq (hχ3 : χ ^ 3 = 1) {N : ℕ} (hq : Fintype.card F = 3 * N + 1)
    {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ^ N = b ^ N) : χ a = χ b := by
  have hw : (a / b) ^ ((Fintype.card F - 1) / 3) = 1 := by
    rw [show (Fintype.card F - 1) / 3 = N by rw [hq]; omega, div_pow, hab,
      div_self (pow_ne_zero _ hb)]
  have hc := AbsoluteGeometryOfSpecZ.CubeRootsOfTwo.card_cube_roots_of_dvd (F := F)
    (by rw [hq]; omega) (div_ne_zero ha hb)
  rw [if_pos hw] at hc
  obtain ⟨⟨c, hc3⟩⟩ : Nonempty {x : F // x ^ 3 = a / b} :=
    (Nat.card_pos_iff.mp (by rw [hc]; norm_num)).1
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hc3
    exact div_ne_zero ha hb hc3.symm
  have h1 : χ (a / b) = 1 := by
    rw [← hc3, map_pow, ← MulChar.pow_apply' χ (by norm_num), hχ3,
      MulChar.one_apply (isUnit_iff_ne_zero.mpr hc0)]
  calc χ a = χ (a / b * b) := by rw [div_mul_cancel₀ _ hb]
    _ = χ b := by rw [map_mul, h1, one_mul]

end

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- `N_{E/F}(y)^{N_F} = y^{N_E}` for `|F| = 3N_F + 1`, `|E| = 3N_E + 1`. -/
theorem algebraMap_norm_pow_eq {NF N : ℕ} (hqF : Fintype.card F = 3 * NF + 1)
    (hqE : Fintype.card E = 3 * N + 1) (y : E) :
    algebraMap F E (Algebra.norm F y ^ NF) = y ^ N := by
  have hdvd : Fintype.card F - 1 ∣ Fintype.card E - 1 := by
    rw [Module.card_eq_pow_finrank (K := F) (V := E)]
    simpa using Nat.sub_dvd_pow_sub_pow (Fintype.card F) 1 (Module.finrank F E)
  obtain ⟨k, hk⟩ := hdvd
  rw [map_pow, FiniteField.algebraMap_norm_eq_pow, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, ← pow_mul, hk, Nat.mul_div_cancel_left _ (by rw [hqF]; omega)]
  congr 1
  have h3 : 3 * N = 3 * (k * NF) := by
    have e1 : Fintype.card E - 1 = 3 * N := by rw [hqE]; omega
    have e2 : Fintype.card F - 1 = 3 * NF := by rw [hqF]; omega
    rw [← e1, hk, e2]; ring
  omega

/-- **The cubic norm sum over the three classes.** -/
theorem sum_char_norm_eq [DecidableEq E] {χ : MulChar F ℂ} (hχ3 : χ ^ 3 = 1) {NF N : ℕ}
    (hqF : Fintype.card F = 3 * NF + 1) (hqE : Fintype.card E = 3 * N + 1) (f : F[X]) {a : F}
    (ha0 : a ≠ 0) (hε1 : a ^ NF ≠ 1) :
    ∑ x : E, χ (Algebra.norm F (aeval x f)) =
      ((univ.filter (fun x : E => (f.map (algebraMap F E)).eval x ≠ 0 ∧
          (f.map (algebraMap F E)).eval x ^ N = 1)).card : ℂ) +
      χ a * (univ.filter (fun x : E => (f.map (algebraMap F E)).eval x ≠ 0 ∧
          (f.map (algebraMap F E)).eval x ^ N = algebraMap F E (a ^ NF))).card +
      χ a ^ 2 * (univ.filter (fun x : E => (f.map (algebraMap F E)).eval x ≠ 0 ∧
          (f.map (algebraMap F E)).eval x ^ N = algebraMap F E (a ^ NF) ^ 2)).card := by
  set h := f.map (algebraMap F E)
  set ε₀ := a ^ NF
  have hε3 : ε₀ ^ 3 = 1 := by
    rw [← pow_mul, show NF * 3 = Fintype.card F - 1 by rw [hqF]; omega]
    exact FiniteField.pow_card_sub_one_eq_one a ha0
  set ω := algebraMap F E ε₀
  have hω3 : ω ^ 3 = 1 := by rw [← map_pow, hε3, map_one]
  have hω1 : ω ≠ 1 := fun h1 => hε1 ((algebraMap F E).injective (h1.trans (map_one _).symm))
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h2; apply hω1
    calc ω = ω ^ 2 * ω := by rw [h2, one_mul]
      _ = ω ^ 3 := by ring
      _ = 1 := hω3
  have hω0 : ω ≠ 0 := by rintro rfl; norm_num at hω3
  have hωω2 : ω ≠ ω ^ 2 := by
    intro h2
    have : ω * (ω - 1) = 0 := by linear_combination -h2
    rcases mul_eq_zero.mp this with h' | h'
    · exact hω0 h'
    · exact hω1 (sub_eq_zero.mp h')
  have heval : ∀ x : E, aeval x f = h.eval x := fun x => by rw [eval_map, aeval_def]
  have hpt : ∀ x : E, χ (Algebra.norm F (aeval x f)) =
      (if h.eval x ≠ 0 ∧ h.eval x ^ N = 1 then 1 else 0) +
        χ a * (if h.eval x ≠ 0 ∧ h.eval x ^ N = ω then 1 else 0) +
        χ a ^ 2 * (if h.eval x ≠ 0 ∧ h.eval x ^ N = ω ^ 2 then 1 else 0) := by
    intro x
    rw [heval]
    set y := h.eval x
    by_cases hy : y = 0
    · rw [hy, map_zero, MulChar.map_zero]
      simp
    · have hNy : Algebra.norm F y ≠ 0 := Algebra.norm_ne_zero_iff.mpr hy
      have hcube : (y ^ N) ^ 3 = 1 := by
        rw [← pow_mul, show N * 3 = Fintype.card E - 1 by rw [hqE]; omega]
        exact FiniteField.pow_card_sub_one_eq_one y hy
      have hlink := algebraMap_norm_pow_eq hqF hqE y
      rcases eq_of_pow_three_eq_one hω3 hω1 hcube with h1 | h1 | h1
      · have hF1 : Algebra.norm F y ^ NF = 1 :=
          (algebraMap F E).injective (by rw [hlink, h1, map_one])
        rw [char_eq_of_pow_eq hχ3 hqF hNy one_ne_zero (by rw [hF1, one_pow]), map_one,
          if_pos ⟨hy, h1⟩, if_neg (fun h' => hω1 (h'.2.symm.trans h1)),
          if_neg (fun h' => hω2 (h'.2.symm.trans h1))]
        ring
      · have hF1 : Algebra.norm F y ^ NF = a ^ NF := (algebraMap F E).injective (by rw [hlink, h1])
        rw [char_eq_of_pow_eq hχ3 hqF hNy ha0 hF1,
          if_neg (fun h' => hω1 (h1.symm.trans h'.2)), if_pos ⟨hy, h1⟩,
          if_neg (fun h' => hωω2 (h1.symm.trans h'.2))]
        ring
      · have hF1 : Algebra.norm F y ^ NF = (a ^ 2) ^ NF := by
          apply (algebraMap F E).injective
          rw [hlink, h1, ← pow_mul, mul_comm, pow_mul, map_pow]
        rw [char_eq_of_pow_eq hχ3 hqF hNy (pow_ne_zero 2 ha0) hF1, map_pow,
          if_neg (fun h' => hω2 (h1.symm.trans h'.2)),
          if_neg (fun h' => hωω2 (h'.2.symm.trans h1)), if_pos ⟨hy, h1⟩]
        ring
  rw [Finset.sum_congr rfl fun x _ => hpt x, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [Finset.sum_boole]
  rfl

/-- **The Weil bound for the cubic norm character over `𝔽_{s²}`, by counting.** -/
theorem norm_sum_char_norm_le [DecidableEq E] {χ : MulChar F ℂ} (hχ : χ ≠ 1) (hχ3 : χ ^ 3 = 1)
    {NF : ℕ} (hqF : Fintype.card F = 3 * NF + 1) {p n : ℕ} [Fact p.Prime] [CharP E p]
    (hcard : Fintype.card E = p ^ n) {f : F[X]} (hsq : Squarefree f) (hdeg : 1 ≤ f.natDegree)
    {N s : ℕ} (hQ : p ^ n = 3 * N + 1) (hs : p ^ n = s ^ 2) (hsD : 3 * f.natDegree + 10 ≤ s) :
    ‖∑ x : E, χ (Algebra.norm F (aeval x f))‖ ≤
      2 * (5 * f.natDegree + 4) * s + 3 * f.natDegree := by
  set D := f.natDegree
  set h := f.map (algebraMap F E)
  have hsqE : Squarefree h := ((PerfectField.separable_iff_squarefree.mpr hsq).map).squarefree
  have hdegE : h.natDegree = D := natDegree_map _
  obtain ⟨a, ha0, ha⟩ : ∃ a : F, a ≠ 0 ∧ χ a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hχ
    ext u
    rw [MulChar.one_apply_coe]
    exact hcon u u.ne_zero
  have hε1 : a ^ NF ≠ 1 := by
    intro h1
    apply ha
    rw [char_eq_of_pow_eq hχ3 hqF ha0 one_ne_zero (by rw [h1, one_pow]), map_one]
  have hε3 : (a ^ NF) ^ 3 = 1 := by
    rw [← pow_mul, show NF * 3 = Fintype.card F - 1 by rw [hqF]; omega]
    exact FiniteField.pow_card_sub_one_eq_one a ha0
  have hqE : Fintype.card E = 3 * N + 1 := hcard.trans hQ
  rw [sum_char_norm_eq hχ3 hqF hqE f ha0 hε1]
  set ζ := χ a
  have hζ3 : ζ ^ 3 = 1 := by
    rw [← MulChar.pow_apply' χ (by norm_num), hχ3, MulChar.one_apply (isUnit_iff_ne_zero.mpr ha0)]
  have hζsum : 1 + ζ + ζ ^ 2 = 0 := by
    have : (ζ - 1) * (1 + ζ + ζ ^ 2) = 0 := by linear_combination hζ3
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr ha)
  have hζn : ‖ζ‖ = 1 := norm_char_eq_one χ ha0
  have hbound := fun (ε : E) (hε : ε ^ 3 = 1) =>
    abs_three_mul_card_sub_le_of_cube_eq_one hcard hsqE (by rw [hdegE]; exact hdeg) hQ hs
      (by rw [hdegE]; exact hsD) hε
  simp only [hdegE] at hbound
  set ω := algebraMap F E (a ^ NF)
  have hω3 : ω ^ 3 = 1 := by rw [← map_pow, hε3, map_one]
  set T : E → ℕ := fun ε => (univ.filter (fun x : E => h.eval x ≠ 0 ∧ h.eval x ^ N = ε)).card
  set B : ℝ := 2 * (5 * D + 4) * s + 3 * D
  have hb : ∀ ε : E, ε ^ 3 = 1 → ‖(3 * (T ε : ℂ) - s ^ 2)‖ ≤ B := by
    intro ε hε
    have h1 := hbound ε hε
    have : ((3 * (T ε : ℂ) - s ^ 2)) = (((3 * (T ε : ℤ) - s ^ 2 : ℤ) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    have h2 : |((3 * (T ε : ℤ) - s ^ 2 : ℤ) : ℝ)| = ((|3 * (T ε : ℤ) - s ^ 2| : ℤ) : ℝ) := by
      push_cast; rfl
    rw [h2]
    exact_mod_cast h1
  have key : (3 : ℂ) * ((T 1 : ℂ) + ζ * T ω + ζ ^ 2 * T (ω ^ 2)) =
      (3 * (T 1 : ℂ) - s ^ 2) + ζ * (3 * (T ω : ℂ) - s ^ 2) + ζ ^ 2 * (3 * (T (ω ^ 2) : ℂ) - s ^ 2) +
        s ^ 2 * (1 + ζ + ζ ^ 2) := by ring
  rw [hζsum, mul_zero, add_zero] at key
  have hn3 : ‖(3 : ℂ) * ((T 1 : ℂ) + ζ * T ω + ζ ^ 2 * T (ω ^ 2))‖ ≤ 3 * B := by
    rw [key]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    rw [norm_mul, norm_mul, norm_pow, hζn, one_pow, one_mul, one_mul]
    have := hb 1 (one_pow 3)
    have := hb ω hω3
    have := hb (ω ^ 2) (by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow])
    linarith
  rw [norm_mul, show ‖(3 : ℂ)‖ = 3 by norm_num] at hn3
  change ‖(T 1 : ℂ) + ζ * T ω + ζ ^ 2 * T (ω ^ 2)‖ ≤ B
  linarith

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip
